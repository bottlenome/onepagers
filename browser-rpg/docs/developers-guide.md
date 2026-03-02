# Developers Guide - タスク別リファレンス

開発タスクごとに「何を読むべきか」「何を編集するか」をまとめたガイド。

---

## ファイル一覧 (読む順序の目安)

| ファイル | 役割 | よく変更するタスク |
|----------|------|-------------------|
| `src/data/constants.js` | 定数 (CARRY_RATIO, MAX_LEVEL等) | バランス調整 |
| `src/data/jobs.js` | 職業定義 (成長値, 成長率, スキル) | 職業バランス調整 |
| `src/data/skills.js` | スキル定義 (ダメージ倍率, コスト) | スキル追加・調整 |
| `src/data/equips.js` | 装備定義 (ステ, 耐久, 成長率ボーナス) | 装備追加 |
| `src/data/items.js` | アイテム定義 (消耗品, 素材) | アイテム追加 |
| `src/data/monsters.js` | モンスター・ボス定義 | 敵追加・ボス調整 |
| `src/data/areas.js` | エリア・町・接続定義 | マップ・施設変更 |
| `src/data/shops.js` | ショップ品揃え | 商品追加 |
| `src/data/recipes.js` | 鍛冶・合成レシピ | レシピ追加 |
| `src/engine/state.js` | ゲーム状態・newPlayer() | 初期状態変更 |
| `src/engine/stats.js` | ステータス計算・転職処理・レベルアップ | バランス調整 |
| `src/engine/combat.js` | 戦闘・ダメージ計算・宝箱 | 戦闘バランス調整 |
| `src/engine/crafting.js` | 鍛冶・合成・強化ロジック | クラフト変更 |
| `src/engine/economy.js` | ショップ・銀行・倉庫 | 経済バランス |
| `src/ui/screens.js` | 全画面レンダリング | UI変更 |
| `src/ui/events.js` | イベントハンドラ・ゲーム開始 | 新アクション追加 |
| `src/ui/render.js` | メインレンダラ | 新画面追加 |

---

## タスク別ガイド

### 1. ボスの強さ調整
**読むファイル:**
- `src/data/monsters.js` — `BOSSES` オブジェクトでHP/ATK/DEF等の固定値を確認
- `src/data/constants.js` — `CARRY_RATIO_BASIC` (転職引き継ぎ率)
- `src/data/jobs.js` — 各職業のbase成長値とrate成長率
- `src/engine/stats.js` — `processLevelUp()`, `changeJob()` で成長計算を確認

**編集ファイル:**
- `src/data/monsters.js` — `BOSSES` のステータス値を変更

**シミュレーション方法:**
- Lv1→30の成長量 = `Σ(base[stat] + rate[stat]の期待値)` × 29レベル分
- 転職引き継ぎ = 成長量 × CARRY_RATIO_BASIC
- Nループ後 = INIT_STATS + 引き継ぎ累積 + 現周回の成長

### 2. 転職バランス調整
**読むファイル:**
- `src/data/constants.js` — `CARRY_RATIO_BASIC`
- `src/engine/stats.js` — `changeJob()` 関数

**編集ファイル:**
- `src/data/constants.js` — 引き継ぎ率変更
- `src/ui/screens.js` — `screenJobChange()` の説明文

### 3. 新装備追加
**読むファイル:**
- `src/data/equips.js` — 既存装備のフォーマット確認
- `src/data/skills.js` — `SUBTYPE_SKILL` マッピング

**編集ファイル:**
- `src/data/equips.js` — 配列に新装備を追加
- `src/data/items.js` — 素材が必要なら追加
- `src/data/recipes.js` — 鍛冶/合成レシピ追加
- `src/data/shops.js` — ショップ販売する場合
- `src/data/monsters.js` — ドロップで入手する場合

### 4. モンスタードロップ追加
**読むファイル:**
- `src/data/monsters.js` — `MONSTER_POOL` のdropsフォーマット
- `src/data/items.js` — ドロップ対象のアイテムID確認

**編集ファイル:**
- `src/data/monsters.js` — `MONSTER_POOL` の該当エントリの `drops` 配列
- `src/data/items.js` — 新素材が必要なら追加

### 5. 隠しキャラ・チートコード追加
**読むファイル:**
- `src/ui/events.js` — `handleAction` の `startgame` ケースで初期化処理を確認
- `src/engine/state.js` — `newPlayer()` のプレイヤー構造

**編集ファイル:**
- `src/ui/events.js` — `startgame` ケースに名前判定ロジックを追加

### 6. ダンジョン宝箱の変更
**読むファイル:**
- `src/engine/combat.js` — `openTreasureChest()` 関数

**編集ファイル:**
- `src/engine/combat.js` — 宝箱の内容変更

### 7. 新ダンジョン要素追加
**読むファイル:**
- `src/data/areas.js` — `AREA_INFO`, `getFieldExits()` でエリア構造
- `src/data/monsters.js` — 該当エリアのモンスタープール

**編集ファイル:**
- `src/data/monsters.js` — 新モンスター追加
- `src/data/areas.js` — エリア接続変更

### 8. 町施設の追加
**読むファイル:**
- `src/data/areas.js` — `TOWN_FACILITIES` で既存施設の構造を確認
- `src/ui/screens.js` — 既存の施設画面関数（例: `screenGuild()`）
- `src/ui/render.js` — `renderScreen()` のswitch文
- `src/ui/events.js` — `handleFacility()` のswitch文

**編集ファイル:**
- `src/data/areas.js` — `TOWN_FACILITIES` の該当町に施設追加
- `src/ui/screens.js` — 新画面関数を追加
- `src/ui/render.js` — `renderScreen()` にcaseを追加
- `src/ui/events.js` — `handleFacility()` にcaseを追加

### 9. 下級職パッシブの変更
**読むファイル:**
- `src/data/jobs.js` — 各職業の `passive` フィールド（`id`, `name`, `value`, `desc`）
- `src/engine/combat.js` — パッシブ適用箇所（`doEnemyAction`: 戦士, `runBattle`: 魔法使い, `handleVictory`: 僧侶・盗賊）

**編集ファイル:**
- `src/data/jobs.js` — `passive` の値やIDを変更
- `src/engine/combat.js` — パッシブIDで分岐するコードを変更

**パッシブ適用箇所マップ:**
| パッシブID | 適用箇所 | 関数 |
|-----------|---------|------|
| `dmg_reduce` | 敵攻撃の最終ダメージ計算 | `doEnemyAction()` |
| `mp_regen` | ターン開始時のMP回復 | `runBattle()` |
| `post_heal` | 勝利後のHP回復 | `handleVictory()` |
| `drop_bonus` | ドロップ判定の確率加算 | `handleVictory()` |

### 10. デモバトルの変更
**読むファイル:**
- `src/engine/state.js` — `createDemoPlayer()` でデモキャラのステータス確認
- `src/engine/combat.js` — `G.demo` フラグによる分岐（`runBattle`, `handleVictory`, `handleDefeat`）
- `src/ui/events.js` — `newgame`・`battleend`・`demo_continue` アクション

**編集ファイル:**
- `src/engine/state.js` — `createDemoPlayer()` のステータス変更
- `src/engine/combat.js` — デモバトルのターン制限・演出変更
- `src/ui/screens.js` — `screenDemoTransition()` の遷移画面テキスト
- `src/ui/events.js` — デモバトルのフロー変更

### 11. 特殊アイテム（転移の巻物等）の追加
**読むファイル:**
- `src/data/items.js` — アイテム定義フォーマット
- `src/engine/economy.js` — `useItemFromInventory()` の特殊処理分岐
- `src/ui/screens.js` — `screenStatus()` のアイテムタブ（`warp_scroll` の特殊表示）

**編集ファイル:**
- `src/data/items.js` — 新アイテム定義
- `src/data/shops.js` — 販売店追加
- `src/engine/economy.js` — `useItemFromInventory()` に特殊処理分岐を追加
- `src/ui/screens.js` — アイテムタブの `canUse` 条件と説明文を追加

---

## 計算式リファレンス

### レベルアップ成長期待値 (1レベルあたり)
```
成長[stat] = job.base[stat] + job.rate[stat] (期待値)
```

### Lv30までの累計成長 (29レベル分)
```
累計[stat] = (job.base[stat] + job.rate[stat]) × 29
```

### 転職時の引き継ぎ
```
引き継ぎ[stat] = (INIT_STATS[stat] + 累計[stat] - INIT_STATS[stat]) × CARRY_RATIO_BASIC
             = 累計[stat] × CARRY_RATIO_BASIC
```

### Nループ後のステータス (下級職で周回)
```
loop_stats[stat] = Σ(i=1..N-1) 累計[stat] × CARRY_RATIO^i + 現周回の累計[stat]
               ≈ 累計[stat] × (CARRY_RATIO^N - CARRY_RATIO) / (CARRY_RATIO - 1) + 累計[stat] (等比級数)
簡易: N回目のループ開始時のbase = 累計 × CARRY_RATIO × (1 - CARRY_RATIO^(N-1)) / (1 - CARRY_RATIO)
```

### 最終ステータス (装備込み)
```
final[stat] = INIT_STATS[stat] + baseStats[stat] + growthStats[stat] + equip.s[stat] + enhancement_bonus
```

### ダメージ計算
```
物理ダメージ = max(1, floor(ATK - DEF × 0.5) ± 2)
魔法ダメージ = max(1, floor(MATK - MDEF × 0.5) ± 2)
```

---

## ビルド・テスト

```bash
cd browser-rpg
bash build.sh && node test.js
```

テスト項目の期待値はtest.jsのデータ定義数チェックで管理。
装備・アイテム・モンスター・ボスを追加した場合はtest.jsの期待値も更新すること。
