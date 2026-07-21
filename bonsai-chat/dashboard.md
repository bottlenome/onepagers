# Bonsai Chat

三値(1.58bit)/1bit の低ビットLLM「Bonsai」ファミリーを、自作 WebGPU カーネルで低ビットのままブラウザ実行するチャット/補完ツール。

## 概要

- 種別: tool
- 状態: wip
- ファイル: `index.html`（依存ライブラリなし・1ファイル完結）
- 検証ツール: `tools/`（フィクスチャ生成・数値検証・スモークテスト）

## 対応モデル（バリエーション）

| モデル | 形式 | DL サイズ | 特徴 |
|---|---|---|---|
| [Bonsai 0.5B](https://huggingface.co/deepgrove/Bonsai) (deepgrove) | 三値 潜在bf16→ブラウザ内2bitパック | 1.2GB→キャッシュ0.3GB | 元祖三値LLM。英語ベースモデル（チャット非対応） |
| [Ternary Bonsai 1.7B](https://huggingface.co/prism-ml/Ternary-Bonsai-1.7B-mlx-2bit) ★推奨 | MLX affine 2bit | 0.48GB | Qwen3 1.7B・チャット対応 |
| [Bonsai 1.7B 1bit](https://huggingface.co/prism-ml/Bonsai-1.7B-mlx-1bit) | MLX affine 1bit | 0.27GB | 最軽量 |
| [Bonsai 4B 1bit](https://huggingface.co/prism-ml/Bonsai-4B-mlx-1bit) | MLX affine 1bit | 0.63GB | |
| [Ternary Bonsai 4B](https://huggingface.co/prism-ml/Ternary-Bonsai-4B-mlx-2bit) | MLX affine 2bit | 1.13GB | 高品質 |
| [Bonsai 8B 1bit](https://huggingface.co/prism-ml/Bonsai-8B-mlx-1bit) | MLX affine 1bit | 1.28GB | |
| [Ternary Bonsai 8B](https://huggingface.co/prism-ml/Ternary-Bonsai-8B-mlx-2bit) | MLX affine 2bit | 2.3GB | 最高品質・要ハイエンドGPU |

PrismML 系は Qwen3 アーキテクチャ（QK-norm / YaRN RoPE / GQA / tied embeddings）のチャット調整済みモデル。
スマホ（iPhone 等の WebGPU 対応ブラウザ）を意識し、DL 2GB 前後までのラインナップとコンテキスト長セレクタ（512/1024/2048）を用意。

## なぜ WebLLM ではないか

- Bonsai ファミリーは線形層が三値 {-1,0,+1}（1.58bit）または 1bit の低ビットLLM
- WebLLM/MLC には三値/1bit 量子化スキームが存在せず、bf16 展開でコンパイルすると低ビットの利点（メモリ・帯域）が消える
- PrismML が llama.cpp をフォークして低ビットカーネルを整備したのに倣い、WGSL カーネルを自作して低ビットのまま実行する方針を採用

## アーキテクチャ

- **qllama ファミリー** (deepgrove 0.5B): safetensors ストリーミング取得 → ブラウザ内で bf16 潜在重みを `clamp(-1,1).round()` → 三値2bitパック（16重み/u32）＋出力チャネル毎スケール
- **mlx ファミリー** (PrismML 1.7B/4B/8B): MLX affine 量子化形式（group_size=128、1bit/2bit、LSB-first パック済み・実データで照合済み）をそのまま GPU に転送し、`w = scale·q + bias` をカーネル内デコードしながら積和
- カーネル (WGSL): 三値GEMV / MLX量子化GEMV / RMSNorm / head単位RMSNorm(QK-norm) / RoPE(YaRN対応・inv_freqバッファ) / GQA attention / SiLU·mul / f16 GEMV / 量子化埋め込みルックアップ
- 数値設計: 計算は全て f32。fp16 格納部は u32 パック＋`unpack2x16float`（shader-f16 拡張不要）。KVキャッシュ f16
- YaRN: HF transformers / mlx-lm と同一式（inv_freq 補間 + attention factor 0.1·ln(factor)+1）
- トークナイザ: Llama SP-BPE と Qwen ByteLevel BPE（pre-tokenizer 正規表現・byte-fallback / byte-level・special token 分割）の2種を自前実装
- チャット: Qwen3 `<|im_start|>` テンプレート・履歴管理（ctx超過時は古いターンから間引き）・&lt;think&gt;思考モード切替
- キャッシュ: パック済み重みをモデル別に OPFS 保存。2回目以降ダウンロード不要
- サンプリング: temperature / top-p / greedy（CPU側）

## 動作要件

- WebGPU 対応ブラウザ（Chrome / Edge デスクトップ最新版推奨、iOS 18+ Safari 等）
- `file://` ではなく HTTP 配信が必要（例: `python3 -m http.server`）
- 8B 系はハイエンドGPU＋メモリ推奨

## 検証

`tools/` に検証一式（要 python3 + numpy、node + playwright。tokenizers は期待値生成時のみ）:

```bash
cd bonsai-chat/tools
python3 make_fixture.py            # ミニチュア QLlama & Qwen3-MLX + numpyリファレンス生成
python3 make_token_vectors.py tokenizer.json                        # SP-BPE 期待値
python3 make_token_vectors.py qwen_tokenizer.json qwen_token_vectors.json  # ByteLevel BPE 期待値
node test_engine.mjs               # headless Chromium (WebGPU SwiftShader) で数値照合
node smoke_real.mjs                # 実モデル 0.5B スモーク
node smoke_real.mjs --model tb17   # 実モデル Ternary 1.7B スモーク
```

検証結果（2026-07-21、headless Chromium + WebGPU SwiftShader）:

- **qllama fixture**: logits max 3.5e-3 一致（スケール±10.7）、greedy 8トークン完全一致
- **mlx fixture**（QK-norm・YaRN・tied embed・affine 2bit）: logits max 3.0e-4 一致、greedy 8トークン完全一致
- **MLX パック順序**: 実モデルの量子化テンソルを unpacked 版と照合し LSB-first・`w=scale·q+bias` を誤差0で確認
- **トークナイザ**: HF tokenizers と SP-BPE / ByteLevel BPE 各12ケース（日本語・絵文字・special tokens・空文字等）完全一致
- **実モデル 0.5B**: "The capital of France is" → "Paris. Paris"。GPU 402MB、読込+パック53s
- **実モデル Ternary 1.7B**: チャットテンプレートで "What is the capital of France? Answer in one word." → **"Paris"** + `<|im_end|>` を正しく生成。GPU 720MB、読込+変換18s（パック済み形式のため変換が軽い）

## タスク

- [x] Bonsai 0.5B の量子化仕様調査・三値2bitパック・WGSLカーネル一式
- [x] safetensors ストリーミングローダ + OPFS キャッシュ
- [x] SP-BPE トークナイザ自前実装
- [x] チャット/補完 UI（ストリーミング表示・停止・続き生成・設定永続化）
- [x] numpy リファレンスとの数値検証ハーネス
- [x] PrismML Bonsai バリエーション対応（1.7B/4B/8B × 三値/1bit、モデルセレクタ）
- [x] MLX affine 量子化 GEMV / QK-norm / YaRN RoPE / tied embeddings
- [x] Qwen ByteLevel BPE トークナイザ + `<|im_start|>` チャットテンプレート + 思考モード
- [x] コンテキスト長セレクタ（512/1024/2048、モバイルメモリ対策）
- [ ] 実GPU環境でのパフォーマンス計測（tok/s）
- [ ] プリフィルのバッチ化（現状は1トークンずつ逐次）
- [ ] iPhone (iOS Safari) 実機での動作確認
- [ ] mlc-llm フォーク（本家WebLLMへの三値スキーム追加）の設計検討
