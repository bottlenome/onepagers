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
    default:            return '<p class="text-center text-muted">画面が見つかりません</p>';
  }
}
