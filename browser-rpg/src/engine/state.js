/* ═══════════════════════════════════════
   ゲーム状態管理
   ═══════════════════════════════════════ */
const G = {
  screen: 'title',       // 現在の画面
  screenStack: [],       // 画面履歴 (戻る用)
  player: null,          // プレイヤーデータ
  battle: null,          // 戦闘中のデータ
  log: [],               // ゲームログ
  shopId: null,          // 現在開いてるショップ
  shopTab: 'buy',        // buy / sell
  statusTab: 'stats',    // stats / equip / items / skills
  settings: {
    battleSpeed: 600,
    strategy: 'balanced',
  },
};

function newPlayer(name, jobId) {
  return {
    name,
    jobId,
    level: 1,
    exp: 0,
    hp: 0, mp: 0,             // 現在値 (init後に設定)
    baseStats: { hp:0, mp:0, atk:0, def:0, matk:0, mdef:0, spd:0 },
    growthStats: { hp:0, mp:0, atk:0, def:0, matk:0, mdef:0, spd:0 },
    gold: 100,
    bankGold: 0,
    equipment: { weapon:null, armor:null, accessory:null },
    // equipObj: 装備中のオブジェクト {baseId, enhancement, durability, maxDurability}
    equipObjs: { weapon:null, armor:null, accessory:null },
    items: [],            // [{id, count}] 消耗品・素材
    equipBag: [],         // [{baseId, enhancement, durability, maxDurability}] 装備バッグ
    warehouse: [],        // [{id, count}] アイテム倉庫
    warehouseEquips: [],  // 装備倉庫
    location: { type:'town', id:'town1' },
    lastTown: 'town1',
    titles: [],
    bossDefeats: {},      // bossKey: count
    arenaProgress: 0,
    arenaUndefeated: true,
    jobHistory: [],       // 経験済み職業
  };
}

// 画面遷移
function pushScreen(screen) {
  G.screenStack.push(G.screen);
  G.screen = screen;
  render();
}

function popScreen() {
  G.screen = G.screenStack.pop() || 'town';
  render();
}

function setScreen(screen) {
  G.screenStack = [];
  G.screen = screen;
  render();
}

// ログ
function addLog(msg, cls) {
  cls = cls || 'system';
  G.log.push({ msg, cls, t: Date.now() });
  if (G.log.length > 80) G.log.splice(0, G.log.length - 60);
}

// ユーティリティ
function rand(min, max) { return Math.floor(Math.random() * (max - min + 1)) + min; }
function clamp(v, lo, hi) { return Math.max(lo, Math.min(hi, v)); }
function delay(ms) { return new Promise(r => setTimeout(r, ms)); }
