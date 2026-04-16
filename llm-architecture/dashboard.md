# LLMアーキテクチャ比較 2026

2026年4月時点の主要LLMの内部アーキテクチャを視覚的に比較できるワンページャー。

## 概要

- 種別: doc
- 状態: wip
- ファイル: `index.html`

## 開発プラン (細分化)

タイムアウト対策のため、各ステップを小さく分けて進める。

### Step 1: 基本骨格 ✅
- [x] HTML 土台 (ダークテーマ、ヘッダー、フッター)
- [x] ベンダー別フィルタータブ (Anthropic/Google/OpenAI/中国/Open)
- [x] モデル概要カード (18モデル分)
- [x] 公開/非公開バッジ
- [x] タグ表示

### Step 2: モデル詳細モーダル (1モデル目・DeepSeek-V3) ⏳
- [ ] カードクリックでモーダル表示
- [ ] DeepSeek-V3 のアーキテクチャ図 (ブロック図)
- [ ] 層構造: Input → Embed → [Transformer × 61] → RMSNorm → Output
- [ ] モーダル閉じる操作 (×ボタン, ESC, 背景クリック)

### Step 3: Attention 機構の詳細ズーム
- [ ] Transformer ブロック内の Attention 部分をクリック
- [ ] MHA / GQA / MQA / MLA を比較する SVG 図
- [ ] 各機構の KV キャッシュサイズ比較
- [ ] 数式表示 (Q·Kᵀ/√d)

### Step 4: MoE (Mixture of Experts) 詳細
- [ ] Router → Expert 選択の動的可視化
- [ ] DeepSeekMoE vs Mixtral-style の違い
- [ ] Shared expert / routed expert
- [ ] Aux-loss-free load balancing

### Step 5: 他モデルのアーキテクチャ図を順次追加
- [ ] Llama 4 Maverick (iRoPE, NoPE層)
- [ ] Qwen3 (dual-mode)
- [ ] Gemma 3 (Sliding Window)
- [ ] Mixtral 8x22B

### Step 6: 長文脈 (1M/10M) の学習手法セクション
- [ ] 位置エンコーディング: RoPE / ALiBi / NoPE / iRoPE
- [ ] コンテキスト拡張: PI (Position Interpolation) / NTK-aware / YaRN / LongRoPE
- [ ] Llama 4 Scout の 10M 学習手順
- [ ] Gemini 2.5 の 1M/2M の推定手法
- [ ] needle-in-haystack 評価

### Step 7: 学習手法セクション
- [ ] Pre-training → SFT → RLHF/DPO → RLVR
- [ ] GRPO (DeepSeek-R1)
- [ ] Constitutional AI (Claude)
- [ ] Test-time compute (o3)

### Step 8: アーキテクチャ比較表
- [ ] Attention / FFN / Norm / Position / Context の行列比較
- [ ] ソート・フィルタ

### Step 9: タイムライン
- [ ] 2024-2026 のリリース年表
- [ ] 技術的ブレイクスルーのマーカー

### Step 10: 仕上げ
- [ ] レスポンシブ調整
- [ ] アクセシビリティ
- [ ] ダッシュボード更新
- [ ] コミット & プッシュ

## 含まれるモデル (18)

### Anthropic (3)
- Claude Opus 4.6, Sonnet 4.6, Haiku 4.5

### Google (3)
- Gemini 2.5 Pro, Gemini 2.5 Flash, Gemma 3

### OpenAI (3)
- GPT-5, GPT-4o, o3

### 中国勢 (5)
- DeepSeek-V3, DeepSeek-R1, Qwen3, Kimi K2, GLM-4.5

### オープンモデル (4)
- Llama 4 Maverick, Llama 4 Scout, Mistral Large 2, Mixtral 8x22B

## 設計方針

- **1ファイル完結**: 外部依存なし、純粋HTML/CSS/JS
- **公開/非公開の明示**: 非公開モデル (Claude, GPT, Gemini) は推定と明記
- **ズーム階層**: 概要 → モデル → コンポーネント → 数式 の4段階
- **情報の優先順位**: 最初は俯瞰、詳細は要求時に表示
