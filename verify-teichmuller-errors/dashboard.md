# IUT理論の間違い検証プロジェクト

## 概要

| 項目 | 内容 |
|------|------|
| 種別 | doc / simulation |
| 状態 | wip |
| メインファイル | index.html |
| 関連 | teichmuller/ (解説プロジェクト) |

宇宙際タイヒミューラー理論（IUT）の既存の批判を検証し、独自の分析を加えるプロジェクト。
**数学的証明**と**計算シミュレーション**の二系統で問題点を明らかにする。

---

## 二系統のアプローチ

### 系統1: 数学的手段による検証

既存の批判（Scholze-Stix 2018, Scholze 2021, Joshi 2024）を数学的に再構成し、
論理構造を明確化する。

| # | 検証項目 | ファイル | 状態 |
|---|---------|---------|------|
| 1 | Scholze-Stix批判の再構成と検証 | notes/01_scholze_stix_verification.md | done |
| 2 | 三つの不定性の定量的分析 | notes/02_indeterminacy_analysis.md | done |
| 3 | 対数殻の制約力の限界証明 | notes/03_log_shell_limits.md | done |
| 4 | 遠アーベル復元のギャップ分析 | notes/04_anabelian_gap.md | todo |
| 5 | Joshiの再構成の評価 | notes/05_joshi_evaluation.md | todo |

### 系統2: シミュレーションによる検証

p進算術とΘ-リンクの動作を計算機で再現し、不定性が不等式を飲み込む様子を
可視化・定量化する。

| # | シミュレーション | ファイル | 状態 |
|---|----------------|---------|------|
| A | Θ-リンクの数値シミュレーション | index.html (Sim-A) | done |
| B | 不定性の爆発シミュレーション | index.html (Sim-B) | done |
| C | 対数殻サイズ vs 不定性の比較 | index.html (Sim-C) | done |
| D | ABC予想の反例探索（IUT不等式の検証）| index.html (Sim-D) | done |

---

## 検証の結論（要約）

### 発見された問題点

1. **Ind1不定性の制御不全**: 対数殻による制約は、Ind1（内部自己同型）の全効果を
   吸収するには不十分。Scholzeの指摘は数学的に妥当。

2. **マルチラジアル表現の循環論法疑惑**: テータ値がマルチラジアルに表現可能であることの
   証明が、系3.12の結論を暗黙に仮定している可能性。

3. **シミュレーションによる確認**: Ind1の自由度を数値的に走査すると、
   不等式が自明化するパラメータ領域が広範に存在することを確認。

4. **群論的手法の限界**: Joshiの指摘通り、純粋に群論的な復元では
   幾何的情報の損失が避けられない。

---

## アーキテクチャ

```
verify-teichmuller-errors/
├── index.html          # インタラクティブシミュレーション（1ファイル完結）
├── dashboard.md        # このファイル
├── notes/
│   ├── 01_scholze_stix_verification.md   # 系統1: Scholze-Stix検証
│   ├── 02_indeterminacy_analysis.md      # 系統1: 不定性の定量分析
│   ├── 03_log_shell_limits.md            # 系統1: 対数殻の限界
│   ├── 04_anabelian_gap.md               # 系統1: 遠アーベル復元ギャップ
│   └── 05_joshi_evaluation.md            # 系統1: Joshi評価
└── docs/
    └── tasks/
```
