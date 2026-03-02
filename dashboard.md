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

## 新規プロジェクト追加手順

1. `<project名>/index.html` を作成（1ファイルで完結させる）
2. `<project名>/dashboard.md` を作成（プロジェクト概要・タスク管理）
3. `<project名>/docs/tasks/` を作成（詳細タスク用）
4. ルートの `index.html` のグリッドにカードを追加
5. このファイルのプロジェクト一覧テーブルに行を追加
