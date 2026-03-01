/* ═══════════════════════════════════════
   セーブ・ロード
   ═══════════════════════════════════════ */

function saveGame() {
  try {
    const data = {
      version: 1,
      player: G.player,
      settings: G.settings,
    };
    localStorage.setItem(SAVE_KEY, JSON.stringify(data));
  } catch (e) {
    console.warn('Save failed:', e);
  }
}

function loadGame() {
  try {
    const raw = localStorage.getItem(SAVE_KEY);
    if (!raw) return false;
    const data = JSON.parse(raw);
    if (!data.player) return false;
    G.player = data.player;
    G.settings = data.settings || G.settings;
    // マイグレーション: 古いセーブデータの互換性
    if (!G.player.equipObjs) G.player.equipObjs = { weapon:null, armor:null, accessory:null };
    if (!G.player.equipBag) G.player.equipBag = [];
    if (!G.player.warehouse) G.player.warehouse = [];
    if (!G.player.warehouseEquips) G.player.warehouseEquips = [];
    if (!G.player.bossDefeats) G.player.bossDefeats = {};
    if (!G.player.jobHistory) G.player.jobHistory = [];
    if (!G.player.titles) G.player.titles = [];
    if (G.player.bankGold === undefined) G.player.bankGold = 0;
    return true;
  } catch (e) {
    console.warn('Load failed:', e);
    return false;
  }
}

function deleteSave() {
  localStorage.removeItem(SAVE_KEY);
}

function hasSave() {
  return !!localStorage.getItem(SAVE_KEY);
}
