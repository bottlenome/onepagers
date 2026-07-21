# Bonsai Chat

三値(1.58bit)LLM [deepgrove/Bonsai 0.5B](https://huggingface.co/deepgrove/Bonsai) を、自作 WebGPU カーネルで低ビットのままブラウザ実行するチャット/補完ツール。

## 概要

- 種別: tool
- 状態: wip
- ファイル: `index.html`（依存ライブラリなし・1ファイル完結）
- 検証ツール: `tools/`（フィクスチャ生成・数値検証・スモークテスト）

## なぜ WebLLM ではないか

- Bonsai は線形層が三値 {-1, 0, +1} ＋ 出力チャネル毎スケールの 1.58bit LLM（`clamp(-1,1).round()`、活性は bf16 のまま）
- WebLLM/MLC には三値量子化スキームが存在せず、bf16 展開でコンパイルすると低ビットの利点（メモリ・帯域）が消える
- PrismML が llama.cpp をフォークして三値カーネルを整備したのに倣い、WGSL カーネルを自作して三値のまま実行する方針を採用

## アーキテクチャ

- モデル: QLlama 0.5B（Llama系: hidden 1536 / 16層 / GQA 16:8 / head_dim 96 / vocab 32000 / RoPE θ=100k / ctx 2048。lm_head と埋め込みはフル精度）
- 重み取得: Hugging Face から safetensors をストリーミング取得 → ブラウザ内で bf16 → 三値2bitパック（16重み/u32）
- キャッシュ: パック済み重みを OPFS に保存。初回 約1.2GB DL → 2回目以降 約300MB のローカル読込のみ
- カーネル (WGSL): 三値GEMV（2bit展開＋行スケール）/ RMSNorm / RoPE / GQA attention / SiLU·mul / f16 GEMV (lm_head)
- 数値設計: 計算は全て f32。fp16 格納部（埋め込み・lm_head・norm・scales・KVキャッシュ）は u32 パック＋`unpack2x16float` でデコードし、shader-f16 拡張に依存しない
- GPU メモリ: 約400MB（三値重み 104MB + f16部 197MB + KVキャッシュ 100MB）
- トークナイザ: Llama SP-BPE（tokenizer.json から自前実装、byte fallback 対応）
- サンプリング: temperature / top-p / greedy（CPU側）
- 注意: Bonsai は事前学習のみのベースモデル。簡易Q&Aモードはプロンプト整形のみで、応答品質は控えめ

## 動作要件

- WebGPU 対応ブラウザ（Chrome / Edge デスクトップ最新版推奨）
- `file://` ではなく HTTP 配信が必要（例: `python3 -m http.server`）

## 検証

`tools/` に検証一式（要 python3 + numpy、node + playwright）:

```bash
cd bonsai-chat/tools
python3 make_fixture.py            # ミニチュアQLlama + numpyリファレンス生成
python3 make_token_vectors.py tokenizer.json   # トークナイザ期待値生成（要 pip install tokenizers）
node test_engine.mjs               # headless Chromium (WebGPU SwiftShader) で数値照合
node smoke_real.mjs                # 実モデル1.2GBでのスモークテスト（低速）
```

検証結果（2026-07-21）:

- logits がリファレンス実装と max 3.5e-3 で一致（スケール ±10.7）、greedy 8トークン完全一致
- トークナイザは HF tokenizers と 10ケース（日本語・絵文字・byte fallback・空文字等）完全一致

## タスク

- [x] Bonsai の量子化仕様調査（qlinear.py / safetensors 解析）
- [x] 三値2bitパック形式の設計・ブラウザ内変換
- [x] WGSL カーネル一式（三値GEMV / RMSNorm / RoPE / GQA attention / SiLU / f16 GEMV）
- [x] safetensors ストリーミングローダ + OPFS キャッシュ
- [x] SP-BPE トークナイザ自前実装
- [x] チャット/補完 UI（ストリーミング表示・停止・続き生成・設定永続化）
- [x] numpy リファレンスとの数値検証ハーネス
- [ ] 実GPU環境でのパフォーマンス計測（tok/s）
- [ ] プリフィルのバッチ化（現状は1トークンずつ逐次）
- [ ] 埋め込み/lm_head の int8 量子化オプション（DL/メモリ削減）
- [ ] mlc-llm フォーク（本家WebLLMへの三値スキーム追加）の設計検討
