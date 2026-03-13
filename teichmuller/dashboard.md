# 宇宙際タイヒミューラー理論 解説プロジェクト

望月新一の宇宙際タイヒミューラー理論 (IUT) とABC予想を、数学科でない人向けに多角的に解説するワンページャー。

## 状態: WIP

## 構成

```
teichmuller/
├── index.html          # 解説ページ (未作成)
├── dashboard.md        # このファイル
├── pdf/                # 原論文PDF (6本)
└── notes/
    ├── 00_overview.md–09_glossary.md   # 論文に沿った縦読み解説 (10本)
    └── views/                          # ビュー別の横読み解説
        ├── summary_view.md             # 概要ビュー
        ├── applications_view.md        # 何ができるかビュー
        ├── why_view.md                 # なんで？ビュー
        ├── rigorous_view.md            # 数学的厳密さビュー（索引）
        │   └── rigorous/ (8本)         #   定義・定理・証明・争点の詳細
        ├── analogy_view.md             # 例えビュー
        ├── history_view.md             # 歴史ビュー
        └── open_questions_view.md      # 未解決問題ビュー
```

## コンテンツ一覧

### 原論文PDF

| ファイル | 状態 | 説明 |
|---------|------|------|
| IUT I–IV + Panoramic + Essential | done | 望月の論文をRIMSからダウンロード済み |

### 縦読み: 論文に沿った解説 (notes/)

| ファイル | 状態 | 説明 |
|---------|------|------|
| 00_overview | done | 全体概要、読み順ガイド、推奨ルート |
| 01_abc_conjecture | done | ABC予想とは何か（具体例付き）|
| 02_prerequisites | done | 前提知識マップ（レベル1〜3の段階別）|
| 03_classical_teichmuller | done | 古典的タイヒミューラー理論とのアナロジー |
| 04_hodge_theater | done | IUT I: ホッジシアター・二つの対称性 |
| 05_theta_link | done | IUT II: シータリンク・マルチラジアリティ |
| 06_log_theta_lattice | done | IUT III: 対数テータ格子・LGPモノイド |
| 07_diophantine_result | done | IUT IV: ディオファンタス不等式・Species |
| 08_controversy | done | 論争の経緯（Scholze-Stix、Joshi）|
| 09_glossary | done | 基礎数学〜IUT固有用語の用語集 |

### 横読み: ビュー別の多角的解説 (notes/views/)

| ビュー | 状態 | 問い |
|--------|------|------|
| summary_view | done | 「で、結局何なの？」を30秒/3分/30分で |
| applications_view | done | 「何ができるの？」帰結と応用の一覧 |
| why_view | done | 「なんで？」各段階の動機を10問で |
| rigorous_view | done | 「厳密にはどう？」定義・定理・証明の骨格 (8サブファイル) |
| analogy_view | done | 「例えると？」日常の言葉での概念理解 |
| history_view | done | 「どこから来た？」時系列と知的系譜 |
| open_questions_view | done | 「何がわかっていない？」未解決問題の整理 |
| numerical_example_view | done | 「数値で見せて！」p進数での分離操作を具体的な数字で |

### 未作成

| コンテンツ | 状態 | 説明 |
|-----------|------|------|
| index.html | todo | 解説ワンページャー（上記ノートをベースに構成予定）|

## 原論文情報

- **著者**: 望月新一 (京都大学数理解析研究所)
- **公開**: 2012年 (プレプリント), 2021年 (PRIMS掲載)
- **出典**: https://www.kurims.kyoto-u.ac.jp/~motizuki/papers-english.html
- **合計**: 約1,000ページ超

## メモ

- index.html の構成は解説ノートの内容確定後に決定予定
- 解説方針: 同じ概念を複数のビューで多角的に照らす。数学的厳密さも例え話も両方提供
- 論争についても公平に記載（証明の受容状況は2025年時点でも未決着）
