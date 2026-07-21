#!/usr/bin/env python3
"""JS トークナイザ検証用ベクトル生成。

deepgrove/Bonsai の tokenizer.json (Llama SP-BPE) を HF tokenizers で読み、
encode/decode の期待値を token_vectors.json に書き出す。

使い方: python3 make_token_vectors.py [path/to/tokenizer.json]
(省略時はカレントの tokenizer.json)
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
]


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "tokenizer.json"
    tok = Tokenizer.from_file(path)
    out = []
    for s in CASES:
        ids = tok.encode(s).ids
        out.append({"text": s, "ids": ids, "decoded": tok.decode(ids)})
    with open("token_vectors.json", "w") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)
    print(f"wrote {len(out)} cases to token_vectors.json")


if __name__ == "__main__":
    main()
