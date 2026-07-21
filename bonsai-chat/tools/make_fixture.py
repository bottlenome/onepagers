#!/usr/bin/env python3
"""bonsai-chat エンジン検証用のミニチュアフィクスチャ生成。

2種類のフィクスチャを生成する:
  fixture/     : deepgrove/Bonsai と同形式 (QLlama, bf16潜在重み→三値)
  fixture-mlx/ : prism-ml/Bonsai* と同形式 (Qwen3, MLX affine 2bit量子化,
                 QK-norm / YaRN RoPE / tied embeddings)

いずれもエンジンと同じ数値経路 (f16丸め・f32計算・KVキャッシュf16) の
numpy リファレンス forward で期待 logits と greedy 系列を出力する。

使い方: python3 make_fixture.py
"""
import json
import math
import os
import struct

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))

PROMPT_IDS = [1, 5, 9, 42, 7]
N_GREEDY = 8


# ---------- 共通ヘルパ ----------

def f32_to_bf16_bits(x: np.ndarray) -> np.ndarray:
    bits = x.astype(np.float32).view(np.uint32)
    bias = np.uint32(0x7FFF) + ((bits >> np.uint32(16)) & np.uint32(1))
    return ((bits + bias) >> np.uint32(16)).astype(np.uint16)


def bf16_bits_to_f32(bits: np.ndarray) -> np.ndarray:
    return (bits.astype(np.uint32) << np.uint32(16)).view(np.float32)


def f16_round(x: np.ndarray) -> np.ndarray:
    return x.astype(np.float16).astype(np.float32)


def save_safetensors(path, tensors):
    """tensors: {name: (dtype_str, np_array)} dtype_str: 'BF16'|'F16'|'U32'"""
    header = {}
    blobs = []
    off = 0
    for name in sorted(tensors.keys()):
        dtype, arr = tensors[name]
        if dtype == "BF16":
            b = f32_to_bf16_bits(arr).tobytes()
        elif dtype == "F16":
            b = arr.astype(np.float16).tobytes()
        elif dtype == "U32":
            b = arr.astype(np.uint32).tobytes()
        else:
            raise ValueError(dtype)
        header[name] = {"dtype": dtype, "shape": list(arr.shape), "data_offsets": [off, off + len(b)]}
        blobs.append(b)
        off += len(b)
    hj = json.dumps(header).encode()
    with open(path, "wb") as f:
        f.write(struct.pack("<Q", len(hj)))
        f.write(hj)
        for b in blobs:
            f.write(b)


def softmax_rows(x):
    x = x - x.max()
    e = np.exp(x)
    return e / e.sum()


def write_expected(outdir, ref, cfg):
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
    with open(os.path.join(outdir, "expected.json"), "w") as f:
        json.dump({
            "prompt_ids": PROMPT_IDS,
            "logits_after_prompt": [float(x) for x in prompt_logits],
            "greedy_ids": greedy,
        }, f)
    print(f"{outdir}: greedy_ids = {greedy}")


# ---------- フィクスチャ1: QLlama (deepgrove形式) ----------

QL_CFG = {
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


def rand_latent(rng, shape):
    w = rng.uniform(-1.2, 1.2, size=shape).astype(np.float32)
    near = np.abs(np.abs(w) - 0.5) < 1e-2
    w[near] += np.sign(w[near]) * 0.05
    return w


def build_qllama(rng):
    c = QL_CFG
    H, L, I, V = c["hidden_size"], c["num_hidden_layers"], c["intermediate_size"], c["vocab_size"]
    NH, NKV, HD = c["num_attention_heads"], c["num_key_value_heads"], c["head_dim"]
    t = {}
    t["model.embed_tokens.weight"] = rng.normal(0, 0.5, (V, H)).astype(np.float32)
    t["lm_head.weight"] = rng.normal(0, 0.5, (V, H)).astype(np.float32)
    t["model.norm.weight"] = rng.uniform(0.5, 1.5, (H,)).astype(np.float32)
    for i in range(L):
        p = f"model.layers.{i}."
        t[p + "input_layernorm.weight"] = rng.uniform(0.5, 1.5, (H,)).astype(np.float32)
        t[p + "post_attention_layernorm.weight"] = rng.uniform(0.5, 1.5, (H,)).astype(np.float32)
        for name, (n_out, n_in) in {
            "self_attn.q_proj": (NH * HD, H), "self_attn.k_proj": (NKV * HD, H),
            "self_attn.v_proj": (NKV * HD, H), "self_attn.o_proj": (H, NH * HD),
            "mlp.gate_proj": (I, H), "mlp.up_proj": (I, H), "mlp.down_proj": (H, I),
        }.items():
            t[p + name + ".weight"] = rand_latent(rng, (n_out, n_in))
            t[p + name + ".scales"] = rng.uniform(0.05, 0.3, (n_out,)).astype(np.float32)
    return t


class QLlamaRef:
    def __init__(self, tensors):
        self.t = {k: bf16_bits_to_f32(f32_to_bf16_bits(v)) for k, v in tensors.items()}
        self.c = QL_CFG
        self.kc = self.vc = None

    def fp(self, name):
        return f16_round(self.t[name])

    def qlinear(self, prefix, x):
        w = np.round(np.clip(self.t[prefix + ".weight"], -1, 1))
        s = f16_round(self.t[prefix + ".scales"])
        return (x @ w.T) * s

    def rmsnorm(self, x, gname):
        return x / np.sqrt(np.mean(x * x) + self.c["rms_norm_eps"]) * self.fp(gname)

    def rope(self, vec, nheads, pos):
        HD = self.c["head_dim"]
        half = HD // 2
        inv = 1.0 / (self.c["rope_theta"] ** (np.arange(half, dtype=np.float64) * 2.0 / HD))
        ang = (pos * inv).astype(np.float32)
        cos, sin = np.cos(ang), np.sin(ang)
        v = vec.reshape(nheads, HD).copy()
        a, b = v[:, :half].copy(), v[:, half:].copy()
        v[:, :half] = a * cos - b * sin
        v[:, half:] = b * cos + a * sin
        return v.reshape(-1)

    def forward_token(self, tok, pos):
        c = self.c
        NH, NKV, HD, L = c["num_attention_heads"], c["num_key_value_heads"], c["head_dim"], c["num_hidden_layers"]
        if self.kc is None:
            T = c["max_position_embeddings"]
            self.kc = np.zeros((L, T, NKV, HD), np.float32)
            self.vc = np.zeros((L, T, NKV, HD), np.float32)
        x = self.fp("model.embed_tokens.weight")[tok].copy()
        for li in range(L):
            p = f"model.layers.{li}."
            xn = self.rmsnorm(x, p + "input_layernorm.weight")
            q = self.rope(self.qlinear(p + "self_attn.q_proj", xn), NH, pos)
            k = self.rope(self.qlinear(p + "self_attn.k_proj", xn), NKV, pos)
            v = self.qlinear(p + "self_attn.v_proj", xn)
            self.kc[li, pos] = f16_round(k.reshape(NKV, HD))
            self.vc[li, pos] = f16_round(v.reshape(NKV, HD))
            out = np.zeros((NH, HD), np.float32)
            qh = q.reshape(NH, HD)
            for h in range(NH):
                kv = h // (NH // NKV)
                sc = self.kc[li, : pos + 1, kv] @ qh[h] / math.sqrt(HD)
                pr = softmax_rows(sc)
                out[h] = pr @ self.vc[li, : pos + 1, kv]
            x = x + self.qlinear(p + "self_attn.o_proj", out.reshape(-1))
            hn = self.rmsnorm(x, p + "post_attention_layernorm.weight")
            g = self.qlinear(p + "mlp.gate_proj", hn)
            u = self.qlinear(p + "mlp.up_proj", hn)
            x = x + self.qlinear(p + "mlp.down_proj", g / (1.0 + np.exp(-g)) * u)
        xf = self.rmsnorm(x, "model.norm.weight")
        return xf @ self.fp("lm_head.weight").T


# ---------- フィクスチャ2: Qwen3 MLX (prism-ml形式) ----------

MLX_CFG = {
    "architectures": ["Qwen3ForCausalLM"],
    "model_type": "qwen3",
    "hidden_size": 64,
    "num_hidden_layers": 2,
    "num_attention_heads": 4,
    "num_key_value_heads": 2,
    "head_dim": 16,
    "intermediate_size": 128,
    "vocab_size": 96,
    "rms_norm_eps": 1e-6,
    "rope_theta": 1000000.0,
    "max_position_embeddings": 64,
    "eos_token_id": 2,
    "tie_word_embeddings": True,
    "quantization": {"group_size": 16, "bits": 2},
    "rope_scaling": {"rope_type": "yarn", "factor": 4.0, "original_max_position_embeddings": 16},
}


def pack_bits(q: np.ndarray, bits: int) -> np.ndarray:
    """q: int配列 [N, K] → u32 [N, K*bits/32] (LSB-first, MLX互換)"""
    N, K = q.shape
    epw = 32 // bits
    words = K // epw
    out = np.zeros((N, words), np.uint64)
    for i in range(epw):
        out |= (q[:, i::epw].astype(np.uint64) & ((1 << bits) - 1)) << np.uint64(bits * i)
    return out.astype(np.uint32)


def make_qtensor(rng, n_out, n_in, bits, gs):
    q = rng.integers(0, 1 << bits, size=(n_out, n_in), dtype=np.int64)
    ng = n_in // gs
    scales = rng.uniform(0.02, 0.2, (n_out, ng)).astype(np.float32)
    # 実モデル同様、各グループの重みがほぼゼロ中心になるバイアス
    center = ((1 << bits) - 1) / 2.0
    biases = (-center * scales + rng.normal(0, 0.01, (n_out, ng))).astype(np.float32)
    return q, scales, biases


def build_mlx(rng):
    c = MLX_CFG
    H, L, I, V = c["hidden_size"], c["num_hidden_layers"], c["intermediate_size"], c["vocab_size"]
    NH, NKV, HD = c["num_attention_heads"], c["num_key_value_heads"], c["head_dim"]
    bits, gs = c["quantization"]["bits"], c["quantization"]["group_size"]
    st = {}   # 保存用 {name: (dtype, arr)}
    raw = {}  # リファレンス用 {name: q/scales/biases/norm}

    def add_q(name, n_out, n_in):
        q, s, b = make_qtensor(rng, n_out, n_in, bits, gs)
        st[name + ".weight"] = ("U32", pack_bits(q, bits))
        st[name + ".scales"] = ("F16", s)
        st[name + ".biases"] = ("F16", b)
        raw[name] = (q, f16_round(s.astype(np.float16).astype(np.float32)), f16_round(b))

    def add_norm(name, n):
        g = rng.uniform(0.5, 1.5, (n,)).astype(np.float32)
        st[name] = ("F16", g)
        raw[name] = f16_round(g)

    add_q("model.embed_tokens", V, H)
    add_norm("model.norm.weight", H)
    for i in range(L):
        p = f"model.layers.{i}."
        add_norm(p + "input_layernorm.weight", H)
        add_norm(p + "post_attention_layernorm.weight", H)
        add_norm(p + "self_attn.q_norm.weight", HD)
        add_norm(p + "self_attn.k_norm.weight", HD)
        add_q(p + "self_attn.q_proj", NH * HD, H)
        add_q(p + "self_attn.k_proj", NKV * HD, H)
        add_q(p + "self_attn.v_proj", NKV * HD, H)
        add_q(p + "self_attn.o_proj", H, NH * HD)
        add_q(p + "mlp.gate_proj", I, H)
        add_q(p + "mlp.up_proj", I, H)
        add_q(p + "mlp.down_proj", H, I)
    return st, raw


def yarn_inv_freq(cfg):
    """HF transformers / mlx-lm と同じ YaRN inv_freq + attention factor"""
    HD = cfg["head_dim"]
    half = HD // 2
    base = cfg["rope_theta"]
    inv = 1.0 / (base ** (np.arange(half, dtype=np.float64) * 2.0 / HD))
    rs = cfg.get("rope_scaling")
    af = 1.0
    if rs and rs.get("rope_type") == "yarn":
        factor = rs["factor"]
        orig = rs.get("original_max_position_embeddings", cfg["max_position_embeddings"])
        beta_fast, beta_slow = rs.get("beta_fast", 32), rs.get("beta_slow", 1)

        def find_dim(nrot):
            return (HD * math.log(orig / (nrot * 2 * math.pi))) / (2 * math.log(base))

        low = max(math.floor(find_dim(beta_fast)), 0)
        high = min(math.ceil(find_dim(beta_slow)), half - 1)
        ramp = np.clip((np.arange(half) - low) / max(high - low, 1e-3), 0, 1)
        inv = inv * (1 - ramp) + (inv / factor) * ramp
        af = rs.get("attention_factor") or (0.1 * math.log(factor) + 1.0)
    return inv.astype(np.float32), np.float32(af)


class MlxRef:
    def __init__(self, raw):
        self.r = raw
        self.c = MLX_CFG
        self.inv, self.af = yarn_inv_freq(self.c)
        self.kc = self.vc = None
        gs = self.c["quantization"]["group_size"]
        self.deq = {}
        for name, v in raw.items():
            if isinstance(v, tuple):
                q, s, b = v
                n_out, n_in = q.shape
                ng = n_in // gs
                w = np.zeros((n_out, n_in), np.float32)
                for g in range(ng):
                    sl = slice(g * gs, (g + 1) * gs)
                    w[:, sl] = s[:, g:g + 1] * q[:, sl].astype(np.float32) + b[:, g:g + 1]
                self.deq[name] = w

    def lin(self, name, x):
        return self.deq[name] @ x

    def rmsnorm(self, x, g, eps):
        return x / np.sqrt(np.mean(x * x) + eps) * g

    def rope(self, vec, nheads, pos):
        HD = self.c["head_dim"]
        half = HD // 2
        ang = (pos * self.inv).astype(np.float32)
        cos, sin = np.cos(ang), np.sin(ang)
        v = vec.reshape(nheads, HD).copy()
        a, b = v[:, :half].copy(), v[:, half:].copy()
        v[:, :half] = (a * cos - b * sin) * self.af
        v[:, half:] = (b * cos + a * sin) * self.af
        return v.reshape(-1)

    def forward_token(self, tok, pos):
        c = self.c
        eps = c["rms_norm_eps"]
        NH, NKV, HD, L = c["num_attention_heads"], c["num_key_value_heads"], c["head_dim"], c["num_hidden_layers"]
        if self.kc is None:
            T = c["max_position_embeddings"]
            self.kc = np.zeros((L, T, NKV, HD), np.float32)
            self.vc = np.zeros((L, T, NKV, HD), np.float32)
        x = self.deq["model.embed_tokens"][tok].copy()
        for li in range(L):
            p = f"model.layers.{li}."
            xn = self.rmsnorm(x, self.r[p + "input_layernorm.weight"], eps)
            q = self.lin(p + "self_attn.q_proj", xn).reshape(NH, HD)
            k = self.lin(p + "self_attn.k_proj", xn).reshape(NKV, HD)
            v = self.lin(p + "self_attn.v_proj", xn)
            # QK-norm (head単位 RMSNorm)
            qg, kg = self.r[p + "self_attn.q_norm.weight"], self.r[p + "self_attn.k_norm.weight"]
            for h in range(NH):
                q[h] = self.rmsnorm(q[h], qg, eps)
            for h in range(NKV):
                k[h] = self.rmsnorm(k[h], kg, eps)
            q = self.rope(q.reshape(-1), NH, pos)
            k = self.rope(k.reshape(-1), NKV, pos)
            self.kc[li, pos] = f16_round(k.reshape(NKV, HD))
            self.vc[li, pos] = f16_round(v.reshape(NKV, HD))
            out = np.zeros((NH, HD), np.float32)
            qh = q.reshape(NH, HD)
            for h in range(NH):
                kv = h // (NH // NKV)
                sc = self.kc[li, : pos + 1, kv] @ qh[h] / math.sqrt(HD)
                pr = softmax_rows(sc)
                out[h] = pr @ self.vc[li, : pos + 1, kv]
            x = x + self.lin(p + "self_attn.o_proj", out.reshape(-1))
            hn = self.rmsnorm(x, self.r[p + "post_attention_layernorm.weight"], eps)
            g = self.lin(p + "mlp.gate_proj", hn)
            u = self.lin(p + "mlp.up_proj", hn)
            x = x + self.lin(p + "mlp.down_proj", g / (1.0 + np.exp(-g)) * u)
        xf = self.rmsnorm(x, self.r["model.norm.weight"], eps)
        return self.deq["model.embed_tokens"] @ xf  # tied lm_head


def main():
    rng = np.random.default_rng(20260721)
    out1 = os.path.join(HERE, "fixture")
    os.makedirs(out1, exist_ok=True)
    t = build_qllama(rng)
    save_safetensors(os.path.join(out1, "model.safetensors"), {k: ("BF16", v) for k, v in t.items()})
    with open(os.path.join(out1, "config.json"), "w") as f:
        json.dump(QL_CFG, f, indent=1)
    write_expected(out1, QLlamaRef(t), QL_CFG)

    rng2 = np.random.default_rng(20260722)
    out2 = os.path.join(HERE, "fixture-mlx")
    os.makedirs(out2, exist_ok=True)
    st, raw = build_mlx(rng2)
    save_safetensors(os.path.join(out2, "model.safetensors"), st)
    with open(os.path.join(out2, "config.json"), "w") as f:
        json.dump(MLX_CFG, f, indent=1)
    write_expected(out2, MlxRef(raw), MLX_CFG)


if __name__ == "__main__":
    main()
