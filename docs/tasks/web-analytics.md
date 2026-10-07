# Cloudflare Web Analytics

## 目的

一覧と各作品の閲覧数・流入元を比較し、利用される作品の改善に使う。無料の Web Analytics を GitHub Pages に手動設置する。DNS やホスティングは変更しない。

## 設定状態

- サイト所有者が Cloudflare の JS snippet から取得した公開サイトトークンを設定済み。
- 公式の現行スニペットどおり beacon は `type="module"` で読み込む。各ページの `defer` 付きローダーが DOM 構築後に対象を判定してから追加する。beacon 自体はページが既に読み込み済みの場合にも対応する。
- 空または不正な形式のトークンでは停止する。API 認証情報は不要。

## 設定

1. Cloudflare dashboard → Web Analytics → Add a site。
2. ホスト名 `bottlenome.github.io` を登録する。
3. Manage site の JS snippet にある公開サイトトークンを `analytics.js` の `SITE_TOKEN` に設定する。API トークンや認証情報は使用しない。
4. 検証後に GitHub Pages へ公開し、本番で beacon の正常応答と Web Analytics 側の受信を確認する。

公式: https://developers.cloudflare.com/web-analytics/get-started/

## 計測範囲

- 一覧 + 11作品 + IUT 詳細レポート（13 HTML）。ディレクトリ URL と `index.html` の両方を許可。
- `open-chatbot` と `bonsai-chat` はスクリプトを追加せず、ローダーの許可リストからも除外。
- IUT `report.html` は直接開いた閲覧だけを集計する。マップ内 iframe は二重計測しない。
- `privacy.html`、ローカルコピー、プレビュー、許可リスト外のページは対象外。
- SPA 計測を無効にし、ページ内のタブ・ゲーム操作・入力をカスタムイベントとして送らない。
- `browser-rpg/build.sh` と `verify-teichmuller-errors/src/template.html` にも設置を維持。IUT のレポートを生成する HTML ビルダーは既存リポジトリにない。

## プライバシー

- 各対象ページから `privacy.html` にリンク。
- ゲーム状態・フォーム内容・チャットを読む処理は追加しない。
- Cloudflare の 2026.10.0 beacon は page location / referrer の credentials、query、fragment を送信前に削除することを公式配布ソースで確認（2026-10-07 JST）。
- 公式 FAQ も query strings を記録しないと説明している。現行 beacon はバージョン固定不可なので、将来の変更には注意する。
- Cloudflare は通信上 IP を受け取り、最寄りデータセンターで破棄する旨を説明している。「外部送信なし」とは表示しない。
- 出典: https://developers.cloudflare.com/web-analytics/faq/ と https://developers.cloudflare.com/speed/observatory/rum-beacon/

## 検証

```sh
node tools/check-analytics.mjs
node tools/check-analytics.mjs --release
bash browser-rpg/build.sh
bash verify-teichmuller-errors/build.sh
# 再ビルド後に generated HTML に追加差分がないことを確認する
```

対象ページ・除外ページ・ホスト制限・iframe・二重読み込み・未設定時の停止を検証する。テストのダミートークンは VM 内でのみ使い、ファイルを書き換えずネットワーク通信もしない。

本番公開前に実トークン入りの `--release` 検証、表示・主要操作の確認、beacon の送信内容の確認を行う。公開後は対象コミットの Pages deployment と解析画面で受信を確認する。閲覧数は広告ブロッカー等で欠落することがあり、売上や登録数の代わりにはならない。
