/* ═══════════════════════════════════════
   クラフトシステム (鍛冶・合成・強化)
   ═══════════════════════════════════════ */

// --- 鍛冶 (鉱山の町) ---

// 作成可能かチェック
function canSmith(recipe) {
  const p = G.player;
  if (p.gold < recipe.fee) return false;
  for (const inp of recipe.inputs) {
    if (!hasItem(p, inp.id, inp.count)) return false;
  }
  return true;
}

// 鍛冶実行
function doSmith(recipeIndex) {
  const recipe = SMITH_RECIPES[recipeIndex];
  if (!recipe || !canSmith(recipe)) { addLog('素材かゴールドが足りない', 'danger'); render(); return; }
  const p = G.player;
  // 素材・手数料消費
  p.gold -= recipe.fee;
  for (const inp of recipe.inputs) {
    removeItem(p, inp.id, inp.count);
  }
  // 成否判定
  if (Math.random() < recipe.rate) {
    const eq = createEquip(recipe.output, 0);
    p.equipBag.push(eq);
    const base = EQUIPS[recipe.output];
    addLog(`鍛冶成功！${base.name}を作成した！`, 'reward');
  } else {
    addLog('鍛冶失敗…素材は失われた。', 'danger');
  }
  saveGame();
  render();
}

// --- 修理 (鍛冶屋) ---
function canRepair(eo) {
  if (!eo || eo.maxDurability === 0) return false;
  return eo.durability < eo.maxDurability;
}

function getRepairCost(eo) {
  const base = EQUIPS[eo.baseId];
  return Math.max(5, Math.floor(base.price * 0.2));
}

function doRepair(slot) {
  const p = G.player;
  const eo = (slot === 'bag') ? null : p.equipObjs[slot];
  // bagから修理する場合は別途処理
  if (!eo || !canRepair(eo)) { addLog('修理の必要がない', 'system'); render(); return; }
  const cost = getRepairCost(eo);
  if (p.gold < cost) { addLog('ゴールドが足りない', 'danger'); render(); return; }
  p.gold -= cost;
  // 最大耐久値を5%減少 (修理のたびに劣化)
  eo.maxDurability = Math.max(1, Math.floor(eo.maxDurability * 0.95));
  eo.durability = eo.maxDurability;
  addLog(`${equipName(eo)}を修理した（${cost}G, 最大耐久${eo.maxDurability}）`, 'system');
  saveGame();
  render();
}

function doRepairBag(bagIndex) {
  const p = G.player;
  const eo = p.equipBag[bagIndex];
  if (!eo || !canRepair(eo)) { addLog('修理の必要がない', 'system'); render(); return; }
  const cost = getRepairCost(eo);
  if (p.gold < cost) { addLog('ゴールドが足りない', 'danger'); render(); return; }
  p.gold -= cost;
  eo.maxDurability = Math.max(1, Math.floor(eo.maxDurability * 0.95));
  eo.durability = eo.maxDurability;
  addLog(`${equipName(eo)}を修理した（${cost}G, 最大耐久${eo.maxDurability}）`, 'system');
  saveGame();
  render();
}

// --- 合成 (エルフの里) ---
function canSynth(recipe) {
  const p = G.player;
  for (const id of recipe.inputs) {
    if (!hasItem(p, id, 1)) return false;
  }
  return true;
}

function doSynth(recipeIndex) {
  const recipe = SYNTH_RECIPES[recipeIndex];
  if (!recipe || !canSynth(recipe)) { addLog('素材が足りない', 'danger'); render(); return; }
  const p = G.player;
  // 素材消費 (失敗時も消費)
  for (const id of recipe.inputs) {
    removeItem(p, id, 1);
  }
  if (Math.random() < recipe.rate) {
    if (recipe.output.isEquip) {
      p.equipBag.push(createEquip(recipe.output.id, 0));
      addLog(`合成成功！${EQUIPS[recipe.output.id].name}を作成した！`, 'reward');
    } else {
      addItemToPlayer(p, recipe.output.id, recipe.outputCount || 1);
      addLog(`合成成功！${ITEMS[recipe.output.id].name}を作成した！`, 'reward');
    }
  } else {
    addLog('合成失敗…素材は失われた。', 'danger');
  }
  saveGame();
  render();
}

// --- 強化 (エルフの里) ---
function getEnhanceCost(eo) {
  const base = EQUIPS[eo.baseId];
  return Math.floor(base.price * (eo.enhancement + 1) * 0.3);
}

function getEnhanceRate(eo) {
  if (eo.enhancement >= MAX_ENHANCE) return 0;
  return ENHANCE_RATES[eo.enhancement] || 0;
}

// 強化対象: 装備中 or バッグから (weapon/armor のみ)
function canEnhance(eo) {
  if (!eo) return false;
  const base = EQUIPS[eo.baseId];
  if (!base) return false;
  if (base.slot !== 'weapon' && base.slot !== 'armor') return false;
  if (eo.enhancement >= MAX_ENHANCE) return false;
  return true;
}

function doEnhance(source, index) {
  // source: 'equipped_weapon', 'equipped_armor', 'bag'
  const p = G.player;
  let eo, slot, bagIdx;

  if (source === 'equipped_weapon') {
    eo = p.equipObjs.weapon; slot = 'weapon';
  } else if (source === 'equipped_armor') {
    eo = p.equipObjs.armor; slot = 'armor';
  } else {
    bagIdx = index;
    eo = p.equipBag[bagIdx];
  }

  if (!eo || !canEnhance(eo)) { addLog('この装備は強化できない', 'danger'); render(); return; }
  const cost = getEnhanceCost(eo);
  if (p.gold < cost) { addLog('ゴールドが足りない', 'danger'); render(); return; }

  const rate = getEnhanceRate(eo);
  const name = equipName(eo);
  p.gold -= cost;

  if (Math.random() < rate) {
    eo.enhancement++;
    addLog(`強化成功！${name} → ${equipName(eo)}！`, 'reward');
  } else {
    // 失敗: 装備破壊
    if (slot) {
      p.equipObjs[slot] = null;
    } else {
      p.equipBag.splice(bagIdx, 1);
    }
    addLog(`強化失敗…${name}は壊れてしまった！`, 'danger');
  }
  const st = calcStats(p);
  p.hp = Math.min(p.hp, st.maxHp);
  p.mp = Math.min(p.mp, st.maxMp);
  saveGame();
  render();
}
