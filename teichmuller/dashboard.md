# 宇宙際タイヒミューラー理論 解説プロジェクト

望月新一の宇宙際タイヒミューラー理論 (IUT) とABC予想を、数学科でない人向けに解説するワンページャー。

## 状態: WIP

## 構成

```
teichmuller/
├── index.html          # 解説ページ (未作成)
├── dashboard.md        # このファイル
├── pdf/                # 原論文PDF
│   ├── IUT_I_Construction_of_Hodge_Theaters.pdf
│   ├── IUT_II_Hodge-Arakelov-theoretic_Evaluation.pdf
│   ├── IUT_III_Canonical_Splittings.pdf
│   ├── IUT_IV_Log-volume_Computations.pdf
│   ├── Panoramic_Overview_of_IUT.pdf
│   └── Essential_Logical_Structure_of_IUT.pdf
└── notes/              # 解説ノート (概要→詳細の階層構造)
    ├── 00_overview.md              # 全体概要・読み進め順ガイド
    ├── 01_abc_conjecture.md        # ABC予想とは何か
    ├── 02_prerequisites.md         # 前提知識マップ (レベル別)
    ├── 03_classical_teichmuller.md # 古典的タイヒミューラー理論とのアナロジー
    ├── 04_hodge_theater.md         # IUT I: ホッジシアターの構成
    ├── 05_theta_link.md            # IUT II: シータリンクと評価
    ├── 06_log_theta_lattice.md     # IUT III: 対数テータ格子
    ├── 07_diophantine_result.md    # IUT IV: 不等式の導出
    ├── 08_controversy.md           # 論争の経緯
    └── 09_glossary.md              # 用語集
```

## 機能・コンテンツ一覧

| コンテンツ | 状態 | 説明 |
|-----------|------|------|
| 原論文PDF (6本) | done | 望月の論文をRIMSからダウンロード済み |
| 全体概要ノート | done | IUT理論の超概要、読み順ガイド |
| ABC予想の解説 | done | 具体例付きの平易な解説 |
| 前提知識マップ | done | レベル1〜3の段階的知識整理 |
| 古典アナロジー | done | タイヒミューラー理論・ガウス積分との対比 |
| IUT I 解説 | done | ホッジシアター・シータリンクの構成 |
| IUT II 解説 | done | マルチラジアリティ・共役同期 |
| IUT III 解説 | done | 対数テータ格子・LGPモノイド |
| IUT IV 解説 | done | ディオファンタス不等式・Species理論 |
| 論争の経緯 | done | Scholze-Stix批判、Joshiの介入 |
| 用語集 | done | 基礎数学〜IUT固有用語まで |
| index.html | todo | 解説ワンページャー（内容は上記ノートをベースに構成予定）|

## 原論文情報

- **著者**: 望月新一 (京都大学数理解析研究所)
- **公開**: 2012年 (プレプリント), 2021年 (PRIMS掲載)
- **出典**: https://www.kurims.kyoto-u.ac.jp/~motizuki/papers-english.html
- **合計**: 約1,000ページ超

## メモ

- index.html の構成は解説ノートの内容確定後に決定予定
- 解説の方針: 数式の厳密性より「なぜ必要か」「何を達成したか」の構造的理解を重視
- 論争についても公平に記載（証明の受容状況は2025年時点でも未決着）
