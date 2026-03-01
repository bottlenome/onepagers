/* ═══════════════════════════════════════
   ナビゲーション・移動
   ═══════════════════════════════════════ */

function moveTo(loc) {
  const p = G.player;
  p.location = loc;
  if (loc.type === 'town') {
    p.lastTown = loc.id;
    G.screen = 'town';
    saveGame();
  } else {
    G.screen = 'field';
  }
  render();
}

function explore() {
  const p = G.player;
  if (p.location.type !== 'field') return;
  const { area, layer } = p.location;
  const monster = spawnMonster(area, layer);
  if (!monster) { addLog('モンスターは現れなかった', 'system'); return; }
  saveGame(); // 戦闘前にセーブ
  startBattle(monster);
}

function enterArena() {
  const p = G.player;
  if (p.gold < ARENA_ENTRY_FEE) { addLog('参加費100Gが必要', 'danger'); render(); return; }
  const opp = createArenaOpponent(p.arenaProgress);
  if (!opp) { addLog('闘技場の全対戦者に勝利済み', 'system'); render(); return; }
  p.gold -= ARENA_ENTRY_FEE;
  opp.arena = true;
  // 闘技場戦闘開始
  startBattle(opp);
}

// 闘技場戦闘後の処理 (combat.jsのhandleVictory/Defeatで呼ばれる想定)
// → handleVictory 内で arena フラグを確認して処理
// 上書きではなく、handleVictory 内で arena チェックを行う

function locationName(loc) {
  if (!loc) return '';
  if (loc.type === 'town') return TOWN_INFO[loc.id] ? TOWN_INFO[loc.id].name : loc.id;
  if (loc.type === 'field') {
    const info = AREA_INFO[loc.area];
    return (info ? info.name : loc.area) + ' 階層' + loc.layer;
  }
  return '';
}
