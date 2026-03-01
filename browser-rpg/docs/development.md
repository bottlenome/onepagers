# Loveless Chronicle 開発ガイド

## ビルド

### 前提条件

- Bash (Linux / macOS / WSL)
- Node.js (テスト実行用)

### ビルド手順

```bash
cd browser-rpg
bash build.sh
```

`src/` 以下のファイルを結合して `index.html` (単一ファイル) を生成する。

### ビルドの仕組み

`build.sh` は以下の順序でファイルを連結する:

1. HTMLヘッダ + `<style>` タグ開始
2. `src/css/style.css`
3. `</style>` + `<body>` + `<script>` タグ開始 (`'use strict'`)
4. データ層: `src/data/` (constants → jobs → skills → equips → items → monsters → areas → shops → recipes → arena)
5. エンジン層: `src/engine/` (state → stats → combat → economy → crafting → navigation → save)
6. UI層: `src/ui/` (components → screens → events → render)
7. プラグイン: `src/plugins/social.js`
8. エントリポイント: `src/main.js`
9. `</script></body></html>`

**注意**: ファイル結合順序に依存関係がある。新しいファイルを追加する場合は `build.sh` の該当位置に `cat` 行を追加すること。

---

## テスト

### テスト実行

```bash
cd browser-rpg
bash build.sh && node test.js
```

ビルド後の `index.html` から `<script>` タグ内のJSを抽出し、Node.js上で実行する。

### テストの仕組み

`test.js` は以下の手順で動作する:

1. `index.html` を読み込み、`<script>` タグ内のJSコードを抽出
2. 最小限のDOM/localStorageモックを `global` に設定
3. ゲームコード + テストコードを `eval()` で一括実行

`'use strict'` + `const` の組み合わせにより、`eval()` 内の `const` 宣言は外部スコープに漏れない。そのためテストコードはゲームコードと同じ `eval()` 内で実行する必要がある。

### テスト項目

| 項目 | 確認内容 |
|------|----------|
| データ定義数 | Jobs: 9, Skills: 33, Equips: 29, Items: 13, Monsters: 57, Bosses: 5 |
| プレイヤー生成 | `newPlayer()` + 初期装備 + `calcStats()` |
| モンスター生成 | `spawnMonster()` でエリア・階層に応じたモンスター出現 |
| 経験値計算 | `calcExpGain()` / `expForNextLevel()` |
| 成長率取得 | `getGrowthRates()` で職業+装備の合算確率 |
| レベルアップ | `processLevelUp()` で確定成長+確率成長 |
| マップ移動 | `getFieldExits()` でエリア間の接続確認 |

### テスト追加方法

`test.js` の IIFE 内 (`(function(){ ... })()`) にテストコードを追加する:

```javascript
const testCode = js + `
;(function(){
  // 既存テスト...

  // 新しいテストを追加
  var result = someFunction();
  console.log('Test result:', result);
  if (result !== expected) {
    throw new Error('Test failed: expected ' + expected + ', got ' + result);
  }
})();
`;
```

---

## ソースコード規則

### ファイル構成

```
src/
├── css/style.css          # スタイル (CSS変数でテーマ管理)
├── data/                  # ゲームデータ (定数・マスターデータ)
├── engine/                # ゲームロジック (状態管理・計算)
├── ui/                    # UI (レンダリング・イベント)
├── plugins/               # プラグイン (拡張機能)
└── main.js                # エントリポイント
```

### コーディング規約

- **モジュールシステム不使用**: ES Modules (`import`/`export`) は使わない。ビルドは単純な `cat` 結合のため、すべてグローバルスコープで定義する
- **変数宣言**: `const` を基本とし、再代入が必要な場合のみ `let` を使用。`var` はテストコード内でのみ使用可
- **命名規則**:
  - 定数/マスターデータ: `UPPER_SNAKE_CASE` (例: `JOBS`, `INIT_STATS`, `MAX_LEVEL`)
  - 関数: `camelCase` (例: `calcStats`, `processLevelUp`)
  - ゲーム状態: グローバル変数 `G` に集約
- **HTMLレンダリング**: テンプレートリテラル (バッククォート) で HTML 文字列を生成し `innerHTML` に代入
- **イベント処理**: イベント委譲パターン。`data-a` (アクション名), `data-p` / `data-p2` (パラメータ) 属性を使用
- **非同期処理**: 戦闘アニメーションなどは `async`/`await` + `setTimeout` ベースの `delay()` 関数

### 新しいデータの追加

1. **装備追加**: `src/data/equips.js` の `EQUIP_LIST` 配列に追加。`createEquip()` で生成される
2. **モンスター追加**: `src/data/monsters.js` の `MONSTER_POOL` 配列に追加。`area` と `minLv`/`maxLv` で出現条件を設定
3. **スキル追加**: `src/data/skills.js` の `SKILLS` オブジェクトに追加。職業スキルの場合は `jobs.js` の該当職業の `skills` にもエントリを追加
4. **エリア追加**: `src/data/areas.js` の `AREA_INFO` にエリア情報を追加し、`getFieldExits()` に接続ルールを追加
5. **ショップ追加**: `src/data/shops.js` に商品リストを追加し、`areas.js` の `TOWN_FACILITIES` に施設を追加

### プラグインAPI

外部機能の拡張は `PluginAPI.register()` を使用する:

```javascript
PluginAPI.register({
  name: 'プラグイン名',
  facilities: {
    townId: [{ id: 'screen_id', icon: '🏠', label: '施設名' }]
  },
  screens: {
    screen_id: () => '<h2>画面タイトル</h2><p>内容</p>'
  },
  init: () => { /* 初期化処理 */ }
});
```

---

## トラブルシューティング

| 問題 | 原因 | 対処 |
|------|------|------|
| ビルドエラー `No such file` | ソースファイルのパスが変更された | `build.sh` のパスを修正 |
| テストで `ReferenceError` | `eval()` 内の `const` スコープ問題 | テストコードを IIFE 内に記述する |
| ゲームが真っ白 | JS構文エラー | ブラウザのDevToolsコンソールでエラーを確認 |
| セーブデータ破損 | `save.js` のバージョン不一致 | `localStorage.removeItem('onepagers-browser-rpg')` で初期化 |
