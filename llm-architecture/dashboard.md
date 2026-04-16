# LLMアーキテクチャ比較 2026

2026年4月時点の主要LLMの内部アーキテクチャを視覚的に比較できるワンページャー。

## 概要

- 種別: doc
- 状態: done (v1)
- ファイル: `index.html`

## 機能

- **18モデルの概要カード**: Anthropic/Google/OpenAI/中国勢/オープンモデル
  をベンダー別にフィルタ可能。公開/非公開バッジで情報の信頼度を明示
- **アーキテクチャ詳細モーダル**: カードクリックで公開9モデルのブロック図・
  スペック・特徴・論文リンクを表示 (DeepSeek-V3/R1, Llama 4 M/S, Qwen3,
  Mixtral, Gemma 3, Kimi K2, GLM-4.5, Mistral Large 2)
- **Attention 機構の比較**: MHA/GQA/MQA/MLA の Q/K/V ヘッド共有パターンを
  色付きで可視化。KVキャッシュ式、採用モデル、pros/cons を併記
- **MoE 詳細**: Token → Router → top-K エキスパートのフロー図。
  7モデルの MoE 構成比較表。負荷均衡4手法 (aux-loss 〜 aux-loss-free)
- **1M/10M 超長コンテキスト**: RoPE の基本・外挿不能性、拡張手法5種
  (PI/NTK/YaRN/LongRoPE/DCA)、アーキテクチャ工夫6種 (iRoPE/NoPE/SWA/
  Hybrid/Ring/Sink)、Llama 4 Scout の4段階 curriculum、6モデルの戦略
- **学習パイプライン & アライメント**: Pre-train → SFT → Align → Test-time
  の5段階。RLHF/DPO/KTO/ORPO/GRPO/CAI/RLVR の比較カード。8モデルの学習
  スタック。Test-time compute (o1/o3/R1/Claude/Gemini thinking) 解説

## 開発ステップ (完了)

- [x] Step 1: 基本HTML構造 + 18モデル概要カード
- [x] Step 2a: 詳細モーダル枠組み
- [x] Step 2b+2c: DeepSeek-V3 ブロック図
- [x] Step 3: Attention 比較 (MHA/GQA/MQA/MLA)
- [x] Step 4: MoE 詳細 (Router, 変種比較, 負荷均衡)
- [x] Step 5: 1M/10M 超長コンテキスト (RoPE, 拡張, アーキ, pipeline)
- [x] Step 6: 学習手法 (RLHF/DPO/GRPO/CAI/RLVR, test-time)
- [x] Step 8: 公開9モデルのアーキ詳細データ追加
- [x] Step 9: ルートダッシュボード/index.html 更新

## 今後の拡張アイデア

- [ ] モデル比較マトリクス (全モデル×全コンポーネントの表)
- [ ] 2024-2026 タイムラインビジュアル
- [ ] モデル選びフロー (用途から推奨モデルを出す診断)
- [ ] tokenizer 比較 (BPE, SentencePiece, tiktoken の違い)
- [ ] ベンチマーク結果の重ね合わせ (MMLU, HumanEval, AIME 等)

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
