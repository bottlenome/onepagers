# OnePagers Dashboard

1ページで完結するツール & ゲームを管理するリポジトリ。

## ディレクトリ構成

```
onepagers/
├── index.html              # 公開用ダッシュボード (HTML)
├── dashboard.md            # プロジェクト管理用 (このファイル)
├── docs/
│   └── tasks/              # タスク管理用ドキュメント
│       └── *.md
├── <project>/
│   └── index.html          # 1ページ完結のツール/ゲーム
└── .gitignore
```

## プロジェクト一覧

| プロジェクト | 種別 | 状態 | 説明 |
|-------------|------|------|------|
| [counter](counter/index.html) | tool | done | シンプルなカウンター |

## 新規プロジェクト追加手順

1. `<project名>/index.html` を作成（1ファイルで完結させる）
2. `index.html` のグリッドにカードを追加
3. このファイルのプロジェクト一覧テーブルに行を追加
4. 必要に応じて `docs/tasks/<project名>.md` にタスクを記録
