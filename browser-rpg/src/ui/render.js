/* ═══════════════════════════════════════
   レンダリングエンジン
   ═══════════════════════════════════════ */

function render() {
  document.getElementById('hdr').innerHTML = renderHeader();
  document.getElementById('main').innerHTML = renderScreen();
  document.getElementById('log').innerHTML = renderLog();
  // ログ自動スクロール
  const logEl = document.getElementById('log');
  if (logEl) logEl.scrollTop = logEl.scrollHeight;
  // エリアに応じた背景切り替え
  updateBodyBg();
}

function updateBodyBg() {
  const body = document.body;
  const prev = [...body.classList].find(c => c.startsWith('bg-'));
  if (prev) body.classList.remove(prev);

  if (G.screen === 'title' || G.screen === 'naming') {
    body.classList.add('bg-title');
    return;
  }
  if (G.screen === 'battle') {
    body.classList.add('bg-battle');
    return;
  }
  if (!G.player) return;

  const loc = G.player.location;
  if (loc.type === 'town') {
    body.classList.add('bg-town');
  } else if (loc.area) {
    const areaMap = {
      grassland: 'bg-grassland',
      mountain: 'bg-mountain',
      mine: 'bg-mine',
      lost_forest: 'bg-forest',
      demon_forest: 'bg-forest',
      wasteland: 'bg-wasteland',
      old_castle: 'bg-castle',
      old_castle_hidden: 'bg-castle',
      last_dungeon: 'bg-lastdungeon',
    };
    body.classList.add(areaMap[loc.area] || 'bg-title');
  }
}

function renderScreen() {
  switch (G.screen) {
    case 'title':       return screenTitle();
    case 'naming':      return screenNaming();
    case 'town':        return screenTown();
    case 'field':       return screenField();
    case 'battle':      return screenBattle();
    case 'shop':        return screenShop();
    case 'status':      return screenStatus();
    case 'jobchange':   return screenJobChange();
    case 'inn':         return screenInn();
    case 'arena':       return screenArena();
    case 'bank':        return screenBank();
    case 'warehouse':   return screenWarehouse();
    case 'blacksmith':  return screenBlacksmith();
    case 'synthesis':   return screenSynthesis();
    case 'enhancement': return screenEnhancement();
    case 'guild':       return screenGuild();
    case 'demo_transition': return screenDemoTransition();
    default:            return '<p class="text-center text-muted">画面が見つかりません</p>';
  }
}
