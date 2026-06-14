# Open Chatbot

オープンウェイトLLMをブラウザ内（WebGPU）で動かすチャットボット。

## 概要

- 種別: tool
- 状態: wip
- ファイル: `index.html`
- 技術: [WebLLM (MLC)](https://github.com/mlc-ai/web-llm) を CDN (`https://esm.run/@mlc-ai/web-llm`) から読込
- 特徴: APIキー不要・完全ローカル実行。推論はすべてユーザー端末上で行われ、サーバーへは何も送信しない。

## 機能

- モデル選択UI（Qwen2.5 / Llama 3.2 / Gemma 2 / Phi-3.5 など小型〜中型を切替）
- ブラウザ内推論（WebGPU）。初回はモデルをDL、2回目以降はブラウザキャッシュから起動
- ダウンロード/初期化のプログレスバー表示
- ストリーミング応答（トークンを逐次描画・生成中は停止可能）
- 会話履歴とモデル選択を localStorage に保存（リロードで復元）
- WebGPU 非対応ブラウザの判定と案内表示

## 動作要件

- WebGPU 対応ブラウザ（Chrome / Edge など、できればデスクトップ最新版）
- モデルサイズに応じた GPU メモリ
- `type="module"` + CDN import のため `file://` ではなく HTTP 配信が必要
  （ローカル確認例: `python3 -m http.server`）

## タスク

- [x] 基本UI作成（モデル選択 / 入力欄 / メッセージ表示）
- [x] WebLLM 連携・モデル読込＋進捗表示
- [x] ストリーミング応答・停止
- [x] 履歴 / モデル選択の永続化
- [x] WebGPU 非対応判定
- [ ] モデル候補のメンテナンス（WebLLM 更新に追従）
- [ ] システムプロンプト/温度のUI調整
