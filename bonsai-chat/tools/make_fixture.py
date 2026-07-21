#!/usr/bin/env python3
"""bonsai-chat エンジン検証用のミニチュア QLlama フィクスチャ生成。

- deepgrove/Bonsai と同じテンソル命名・格納形式 (bf16 safetensors) の小型モデルを乱数生成
- エンジンと同じ数値経路 (bf16→f16 丸め、三値化 clamp(-1,1).round-half-even、
  KV キャッシュ f16 丸め、f32 計算) の numpy リファレンス forward を実行
- fixture/config.json, fixture/model.safetensors, fixture/expected.json を出力

使い方: python3 make_fixture.py
"""
import json
import os
import struct

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "fixture")

CFG = {
    "architectures": ["QLlamaForCausalLM"],
    "hidden_size": 64,
    "num_hidden_layers": 2,
    "num_attention_heads": 4,
    "num_key_value_heads": 2,
    "head_dim": 16,
    "intermediate_size": 128,
    "vocab_size": 128,
    "rms_norm_eps": 1e-5,
    "rope_theta": 100000.0,
    "max_position_embeddings": 64,
    "bos_token_id": 1,
    "eos_token_id": 2,
    "tie_word_embeddings": False,
    "torch_dtype": "bfloat16",
}

PROMPT_IDS = [1, 5, 9, 42, 7]
N_GREEDY = 8


def f32_to_bf16_bits(x: np.ndarray) -> np.ndarray:
    """float32 → bf16 (round-to-nearest-even) のビット列 (uint16)。"""
    bits = x.astype(np.float32).view(np.uint32)
    bias = np.uint32(0x7FFF) + ((bits >> np.uint32(16)) & np.uint32(1))
    return ((bits + bias) >> np.uint32(16)).astype(np.uint16)


def bf16_bits_to_f32(bits: np.ndarray) -> np.ndarray:
    return (bits.astype(np.uint32) << np.uint32(16)).view(np.float32)


def f16_round(x: np.ndarray) -> np.ndarray:
    """f32 → f16 → f32 丸め (エンジンの fp テンソル格納を模倣)。"""
    return x.astype(np.float16).astype(np.float32)


def round_half_even(x: np.ndarray) -> np.ndarray:
    return np.round(x)  # numpy は half-to-even


def ternarize(w_latent_f32: np.ndarray) -> np.ndarray:
    return round_half_even(np.clip(w_latent_f32, -1.0, 1.0))


def rand_latent(rng, shape):
    """三値化の境界 (±0.5) 近傍を避けた潜在重み。"""
    w = rng.uniform(-1.2, 1.2, size=shape).astype(np.float32)
    # ±0.5 の 1e-2 以内は避ける (丸めモード差の混入防止)
    near = np.abs(np.abs(w) - 0.5) < 1e-2
    w[near] += np.sign(w[near]) * 0.05
    return w


def build_weights(rng):
    H, L = CFG["hidden_size"], CFG["num_hidden_layers"]
    I, V = CFG["intermediate_size"], CFG["vocab_size"]
    NH, NKV, HD = CFG["num_attention_heads"], CFG["num_key_value_heads"], CFG["head_dim"]
    t = {}
    t["model.embed_tokens.weight"] = rng.normal(0, 0.5, (V, H)).astype(np.float32)
    t["lm_head.weight"] = rng.normal(0, 0.5, (V, H)).astype(np.float32)
    t["model.norm.weight"] = rng.uniform(0.5, 1.5, (H,)).astype(np.float32)
    for i in range(L):
        p = f"model.layers.{i}."
        t[p + "input_layernorm.weight"] = rng.uniform(0.5, 1.5, (H,)).astype(np.float32)
        t[p + "post_attention_layernorm.weight"] = rng.uniform(0.5, 1.5, (H,)).astype(np.float32)
        for name, (n_out, n_in) in {
            "self_attn.q_proj": (NH * HD, H),
            "self_attn.k_proj": (NKV * HD, H),
            "self_attn.v_proj": (NKV * HD, H),
            "self_attn.o_proj": (H, NH * HD),
            "mlp.gate_proj": (I, H),
            "mlp.up_proj": (I, H),
            "mlp.down_proj": (H, I),
        }.items():
            t[p + name + ".weight"] = rand_latent(rng, (n_out, n_in))
            t[p + name + ".scales"] = rng.uniform(0.05, 0.3, (n_out,)).astype(np.float32)
    return t


def save_safetensors(path, tensors):
    header = {}
    blobs = []
    off = 0
    for name in sorted(tensors.keys()):
        bits = f32_to_bf16_bits(tensors[name])
        b = bits.tobytes()
        header[name] = {
            "dtype": "BF16",
            "shape": list(tensors[name].shape),
            "data_offsets": [off, off + len(b)],
        }
        blobs.append(b)
        off += len(b)
    hj = json.dumps(header).encode()
    with open(path, "wb") as f:
        f.write(struct.pack("<Q", len(hj)))
        f.write(hj)
        for b in blobs:
            f.write(b)


class Ref:
    """エンジン数値経路を模倣した numpy リファレンス。"""

    def __init__(self, tensors):
        # 保存時の bf16 丸めを通した値から開始 (エンジンが読むのはこの値)
        self.t = {k: bf16_bits_to_f32(f32_to_bf16_bits(v)) for k, v in tensors.items()}
        self.kc = None  # [L, T, NKV, HD] f16 丸め済み
        self.vc = None

    def fp(self, name):
        return f16_round(self.t[name])

    def qlinear(self, prefix, x):
        w = ternarize(self.t[prefix + ".weight"])
        s = f16_round(self.t[prefix + ".scales"])
        return (x @ w.T) * s

    def rmsnorm(self, x, gname):
        g = self.fp(gname)
        return x / np.sqrt(np.mean(x * x) + CFG["rms_norm_eps"]) * g

    def rope(self, vec, nheads, pos):
        HD = CFG["head_dim"]
        half = HD // 2
        inv = 1.0 / (CFG["rope_theta"] ** (np.arange(half, dtype=np.float64) * 2.0 / HD))
        ang = (pos * inv).astype(np.float32)
        cos, sin = np.cos(ang), np.sin(ang)
        v = vec.reshape(nheads, HD).copy()
        a, b = v[:, :half].copy(), v[:, half:].copy()
        v[:, :half] = a * cos - b * sin
        v[:, half:] = b * cos + a * sin
        return v.reshape(-1)

    def forward_token(self, tok, pos):
        H = CFG["hidden_size"]
        NH, NKV, HD = CFG["num_attention_heads"], CFG["num_key_value_heads"], CFG["head_dim"]
        L = CFG["num_hidden_layers"]
        if self.kc is None:
            T = CFG["max_position_embeddings"]
            self.kc = np.zeros((L, T, NKV, HD), np.float32)
            self.vc = np.zeros((L, T, NKV, HD), np.float32)
        x = self.fp("model.embed_tokens.weight")[tok].copy()
        for li in range(L):
            p = f"model.layers.{li}."
            xn = self.rmsnorm(x, p + "input_layernorm.weight")
            q = self.qlinear(p + "self_attn.q_proj", xn)
            k = self.qlinear(p + "self_attn.k_proj", xn)
            v = self.qlinear(p + "self_attn.v_proj", xn)
            q = self.rope(q, NH, pos)
            k = self.rope(k, NKV, pos)
            self.kc[li, pos] = f16_round(k.reshape(NKV, HD))
            self.vc[li, pos] = f16_round(v.reshape(NKV, HD))
            qh = q.reshape(NH, HD)
            out = np.zeros((NH, HD), np.float32)
            grp = NH // NKV
            for h in range(NH):
                kv = h // grp
                ks = self.kc[li, : pos + 1, kv]  # [T, HD]
                vs = self.vc[li, : pos + 1, kv]
                sc = ks @ qh[h] / np.sqrt(HD)
                sc = sc - sc.max()
                pr = np.exp(sc)
                pr /= pr.sum()
                out[h] = pr @ vs
            attn = self.qlinear(p + "self_attn.o_proj", out.reshape(-1))
            x = x + attn
            hn = self.rmsnorm(x, p + "post_attention_layernorm.weight")
            g = self.qlinear(p + "mlp.gate_proj", hn)
            u = self.qlinear(p + "mlp.up_proj", hn)
            act = g / (1.0 + np.exp(-g)) * u
            x = x + self.qlinear(p + "mlp.down_proj", act)
        xf = self.rmsnorm(x, "model.norm.weight")
        return xf @ self.fp("lm_head.weight").T


def main():
    os.makedirs(OUT, exist_ok=True)
    rng = np.random.default_rng(20260721)
    tensors = build_weights(rng)
    save_safetensors(os.path.join(OUT, "model.safetensors"), tensors)
    with open(os.path.join(OUT, "config.json"), "w") as f:
        json.dump(CFG, f, indent=1)

    ref = Ref(tensors)
    logits = None
    for pos, tok in enumerate(PROMPT_IDS):
        logits = ref.forward_token(tok, pos)
    prompt_logits = logits.copy()
    ids = list(PROMPT_IDS)
    greedy = []
    for _ in range(N_GREEDY):
        nxt = int(np.argmax(logits))
        greedy.append(nxt)
        ids.append(nxt)
        logits = ref.forward_token(nxt, len(ids) - 1)
    with open(os.path.join(OUT, "expected.json"), "w") as f:
        json.dump(
            {
                "prompt_ids": PROMPT_IDS,
                "logits_after_prompt": [float(x) for x in prompt_logits],
                "greedy_ids": greedy,
            },
            f,
        )
    print("fixture written to", OUT)
    print("greedy_ids:", greedy)


if __name__ == "__main__":
    main()
