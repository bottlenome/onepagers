# 新規ゲームプロジェクト作成

新しいゲームプロジェクトを立ち上げるスキル。

## 手順

1. **ディレクトリ作成**: `<project名>/` と `<project名>/docs/tasks/` を作成
2. **ゲーム本体作成**: `<project名>/index.html` を1ファイルで完結するゲームとして作成
   - 共通スタイル: `background: #0f172a; color: #e2e8f0; font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;`
   - 戻るリンク: `<a class="back" href="../index.html">&larr; OnePagers</a>`
   - タイトルの `<title>` は `プロジェクト名 - OnePagers` 形式
   - `user-select: none;` をbodyに追加（ゲーム操作のため）
   - 色覚バリアフリー: 色の区別が必要な場合はOkabe-Itoパレットを使用し、模様でも識別可能にする
3. **プロジェクトdashboard作成**: `<project名>/dashboard.md` を以下のテンプレートで作成

```markdown
# プロジェクト名

一行説明。

## 概要

- 種別: game
- 状態: done
- ファイル: `index.html`

## ルール

- ルール1
- ルール2

## 機能

- [x] 実装済み機能1
- [x] 実装済み機能2
- [ ] 未実装機能
```

4. **ルート `index.html` 更新**: `<!-- 新しいプロジェクトはここに追加 -->` の直前にカードを追加

```html
    <a class="card" href="<project名>/index.html">
      <span class="tag">game</span>
      <h2>表示名</h2>
      <p>一行説明。</p>
    </a>
```

5. **ルート `dashboard.md` 更新**: プロジェクト一覧テーブルに行を追加

```
| [表示名](<project名>/index.html) | game | done | 一行説明 |
```

6. **動作確認**: ゲームが正しく動作し、ダッシュボード間の説明文が一致していることを確認
