#!/usr/bin/env python3
"""JS トークナイザ検証用ベクトル生成。

HF tokenizers で tokenizer.json を読み、encode/decode の期待値を JSON に書き出す。

使い方:
  python3 make_token_vectors.py tokenizer.json                      # → token_vectors.json (SP-BPE用)
  python3 make_token_vectors.py qwen_tok.json qwen_token_vectors.json  # → Qwen ByteLevel BPE用
"""
import json
import sys

from tokenizers import Tokenizer

CASES = [
    "Hello, world!",
    "The capital of France is",
    "こんにちは、世界！日本語のテスト。",
    "  leading spaces and\nnewlines\t tabs",
    "emoji 🎋 and symbols ©®™ …",
    "1234567890 3.14159",
    "Bonsai is a ternary-weight LLM.",
    "混ざった English と 日本語 mixed",
    "",
    "▁literal metasymbol",
    "I'm sure it's O'Brien's",
    "<|im_start|>user\nこんにちは<|im_end|>\n<|im_start|>assistant\n",
]


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "tokenizer.json"
    out = sys.argv[2] if len(sys.argv) > 2 else "token_vectors.json"
    tok = Tokenizer.from_file(path)
    vecs = []
    for s in CASES:
        ids = tok.encode(s).ids
        vecs.append({"text": s, "ids": ids, "decoded": tok.decode(ids)})
    with open(out, "w") as f:
        json.dump(vecs, f, ensure_ascii=False, indent=1)
    print(f"wrote {len(vecs)} cases to {out}")


if __name__ == "__main__":
    main()
