# OnePagers Dashboard

1ページで完結するツール & ゲームを管理するリポジトリ。

公開サイト: https://bottlenome.github.io/onepagers/

## ディレクトリ構成

```
onepagers/
├── index.html              # 公開用ダッシュボード (HTML)
├── dashboard.md            # 全体のプロジェクト管理 (このファイル)
├── docs/
│   └── tasks/              # リポジトリ全体のタスク
├── <project>/
│   ├── index.html          # 1ページ完結のツール/ゲーム
│   ├── dashboard.md        # プロジェクト個別の管理用
│   └── docs/
│       └── tasks/*.md      # プロジェクト個別のタスク
└── .gitignore
```

## プロジェクト一覧

| プロジェクト | 種別 | 状態 | 説明 |
|-------------|------|------|------|
| [counter](counter/index.html) | tool | done | シンプルなカウンター |
| [虹色リバーシ](rainbow-reversi/index.html) | game | done | 虹色グラデーションの駒で最大4人対戦できるリバーシ |
| [Loveless Chronicle](browser-rpg/index.html) | game | wip | 転職・スキル・自動戦闘が楽しめるRPGブラウザゲーム |
| [櫻井政博のゲームデザイン方法論](sakurai-methodology/index.html) | doc | done | YouTube「桜井政博のゲーム作るには」全256話の設計原則まとめ |
| [宇宙際タイヒミューラー理論](teichmuller/index.html) | doc | done | 望月新一のIUT理論とABC予想を非数学者向けに解説。10タブ構成（概要/なぜ/構造/例え/数値例/応用/歴史/論争/用語集/資料） |
| [IUT理論の間違い検証](verify-teichmuller-errors/index.html) | doc | wip | IUT III 系3.12の論理的ギャップを数学的証明とシミュレーションで検証 |
| [IUT の Lean 形式検証マップ](iut-lean-verification/index.html) | doc | done | 原論文PDFを一次資料に IUT 全体の土台（柱A〜E）を Lean 4 で積み上げ、結論の要=系3.12 をめぐる論争を機械判定（総合証明率: ページ重み ~28% / 主張平均 ~36%）。系3.12 はスコープ全体ではなくABC予想に届く決定的不等式＝係争点。定理3.11 の出力仕様を原文から形式化し系3.12 の証明本体を公理ゼロで機械化。「仕様充足→系3.12→Szpiro→ABC型帰結」の全経路接続済み。構成の4基盤——基本群（M9）・遠アーベル復元アルゴリズム（M10、選択公理不使用）・cyclotomic rigidity（M11）・Frobenioid 次数層（M12）——も骨格形式化済み。残る未形式化は構成の実体（sorry なし） |
| [DDD実践入門](learn-ddd/index.html) | doc | done | ドメイン駆動設計の核心をインタラクティブに学べる実践入門 |
| [LLMアーキテクチャ比較 2026](llm-architecture/index.html) | doc | wip | 2026年4月時点の主要LLM 18モデルを視覚比較。Attention/MoE/1M長文脈/RLHFを図解 |

## 新規プロジェクト追加手順

1. `<project名>/index.html` を作成（1ファイルで完結させる）
2. `<project名>/dashboard.md` を作成（プロジェクト概要・タスク管理）
3. `<project名>/docs/tasks/` を作成（詳細タスク用）
4. ルートの `index.html` のグリッドにカードを追加
5. このファイルのプロジェクト一覧テーブルに行を追加
