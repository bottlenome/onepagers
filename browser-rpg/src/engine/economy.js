/* ═══════════════════════════════════════
   経済システム (ショップ・銀行・倉庫)
   ═══════════════════════════════════════ */

// --- アイテム操作 ---
function hasItem(p, id, count) {
  const slot = p.items.find(i => i.id === id);
  return slot && slot.count >= count;
}

function addItemToPlayer(p, id, count) {
  const slot = p.items.find(i => i.id === id);
  if (slot) { slot.count += count; }
  else { p.items.push({ id, count }); }
}

function removeItem(p, id, count) {
  const slot = p.items.find(i => i.id === id);
  if (!slot) return false;
  slot.count -= count;
  if (slot.count <= 0) p.items.splice(p.items.indexOf(slot), 1);
  return true;
}

// --- ショップ購入 ---
function buyShopItem(shopItemDef) {
  const p = G.player;
  if (shopItemDef.isEquip) {
    const eq = EQUIPS[shopItemDef.id];
    if (!eq) return;
    if (p.gold < eq.price) { addLog('ゴールドが足りない！', 'danger'); return; }
    p.gold -= eq.price;
    p.equipBag.push(createEquip(shopItemDef.id, 0));
    addLog(`${eq.name}を購入した！`, 'reward');
  } else {
    const item = ITEMS[shopItemDef.id];
    if (!item) return;
    if (p.gold < item.price) { addLog('ゴールドが足りない！', 'danger'); return; }
    p.gold -= item.price;
    addItemToPlayer(p, shopItemDef.id, 1);
    addLog(`${item.name}を購入した！`, 'reward');
  }
  saveGame();
  render();
}

// --- ショップ売却 ---
function sellItem(itemId, isEquip, bagIndex) {
  const p = G.player;
  if (isEquip) {
    if (bagIndex < 0 || bagIndex >= p.equipBag.length) return;
    const eo = p.equipBag[bagIndex];
    const base = EQUIPS[eo.baseId];
    const price = Math.floor(base.price * 0.5);
    p.gold += price;
    p.equipBag.splice(bagIndex, 1);
    addLog(`${equipName(eo)}を${price}Gで売却した`, 'reward');
  } else {
    const item = ITEMS[itemId];
    if (!item || !hasItem(p, itemId, 1)) return;
    const price = Math.floor(item.price * 0.5);
    p.gold += price;
    removeItem(p, itemId, 1);
    addLog(`${item.name}を${price}Gで売却した`, 'reward');
  }
  saveGame();
  render();
}

// --- 装備 ---
function equipItem(bagIndex) {
  const p = G.player;
  if (bagIndex < 0 || bagIndex >= p.equipBag.length) return;
  const eo = p.equipBag[bagIndex];
  const base = EQUIPS[eo.baseId];
  const slot = base.slot;
  // 今装備中のものをバッグに戻す
  if (p.equipObjs[slot]) {
    p.equipBag.push(p.equipObjs[slot]);
  }
  p.equipObjs[slot] = eo;
  p.equipBag.splice(bagIndex, 1);
  const st = calcStats(p);
  p.hp = Math.min(p.hp, st.maxHp);
  p.mp = Math.min(p.mp, st.maxMp);
  addLog(`${equipName(eo)}を装備した`, 'system');
  saveGame();
  render();
}

function unequipItem(slot) {
  const p = G.player;
  if (!p.equipObjs[slot]) return;
  p.equipBag.push(p.equipObjs[slot]);
  p.equipObjs[slot] = null;
  const st = calcStats(p);
  p.hp = Math.min(p.hp, st.maxHp);
  p.mp = Math.min(p.mp, st.maxMp);
  addLog('装備を外した', 'system');
  saveGame();
  render();
}

// --- 宿屋 ---
function stayAtInn(cost) {
  const p = G.player;
  if (p.gold < cost) { addLog('ゴールドが足りない！', 'danger'); render(); return; }
  p.gold -= cost;
  const st = calcStats(p);
  p.hp = st.maxHp;
  p.mp = st.maxMp;
  addLog(`宿屋に泊まった。HP・MPが全回復した！(${cost}G)`, 'heal');
  saveGame();
  render();
}

// --- アイテム使用 ---
function useItemFromInventory(itemId) {
  const p = G.player;
  const item = ITEMS[itemId];
  if (!item || !hasItem(p, itemId, 1)) return;
  if (item.type !== 'consumable') { addLog('このアイテムは使えない', 'danger'); render(); return; }
  if (item.healHp === 0 && item.healMp === 0) { addLog('今は使えない', 'danger'); render(); return; }
  removeItem(p, itemId, 1);
  const st = calcStats(p);
  if (item.healHp) {
    const amt = item.healHp === -1 ? st.maxHp : item.healHp;
    p.hp = Math.min(p.hp + amt, st.maxHp);
  }
  if (item.healMp) {
    const amt = item.healMp === -1 ? st.maxMp : item.healMp;
    p.mp = Math.min(p.mp + amt, st.maxMp);
  }
  addLog(`${item.name}を使った！`, 'heal');
  saveGame();
  render();
}

// --- 銀行 ---
function bankDeposit(amount) {
  const p = G.player;
  if (amount <= 0 || p.gold < amount) return;
  const fee = Math.max(1, Math.floor(amount * 0.05));
  const total = amount + fee;
  if (p.gold < total) { addLog(`手数料込み${total}G必要（手数料${fee}G）`, 'danger'); render(); return; }
  p.gold -= total;
  p.bankGold += amount;
  addLog(`${amount}Gを預けた（手数料${fee}G）`, 'reward');
  saveGame();
  render();
}

function bankWithdraw(amount) {
  const p = G.player;
  if (amount <= 0 || p.bankGold < amount) return;
  p.bankGold -= amount;
  p.gold += amount;
  addLog(`${amount}Gを引き出した`, 'reward');
  saveGame();
  render();
}

// --- 倉庫 ---
function warehouseStore(itemId, isEquip, bagIndex) {
  const p = G.player;
  const fee = 10;
  if (p.gold < fee) { addLog('手数料10Gが必要', 'danger'); render(); return; }
  p.gold -= fee;
  if (isEquip) {
    const eo = p.equipBag.splice(bagIndex, 1)[0];
    p.warehouseEquips.push(eo);
    addLog(`${equipName(eo)}を預けた`, 'system');
  } else {
    if (!hasItem(p, itemId, 1)) return;
    removeItem(p, itemId, 1);
    const ws = p.warehouse.find(i => i.id === itemId);
    if (ws) ws.count++; else p.warehouse.push({ id:itemId, count:1 });
    addLog(`${(ITEMS[itemId]||{}).name||itemId}を預けた`, 'system');
  }
  saveGame();
  render();
}

function warehouseRetrieve(itemId, isEquip, whIndex) {
  const p = G.player;
  if (isEquip) {
    const eo = p.warehouseEquips.splice(whIndex, 1)[0];
    p.equipBag.push(eo);
    addLog(`${equipName(eo)}を引き出した`, 'system');
  } else {
    const ws = p.warehouse.find(i => i.id === itemId);
    if (!ws || ws.count <= 0) return;
    ws.count--;
    if (ws.count <= 0) p.warehouse.splice(p.warehouse.indexOf(ws), 1);
    addItemToPlayer(p, itemId, 1);
    addLog(`${(ITEMS[itemId]||{}).name||itemId}を引き出した`, 'system');
  }
  saveGame();
  render();
}

// --- ヘルパー ---
function equipName(eo) {
  const base = EQUIPS[eo.baseId];
  let n = base ? base.name : eo.baseId;
  if (eo.enhancement > 0) n += '+' + eo.enhancement;
  return n;
}

function equipStatText(eo) {
  const base = EQUIPS[eo.baseId];
  if (!base) return '';
  const parts = [];
  for (const [k,v] of Object.entries(base.s)) {
    let total = v;
    if (eo.enhancement > 0) {
      if (base.slot === 'weapon' && k === 'atk') total += eo.enhancement * ENHANCE_BONUS.weapon;
      if (base.slot === 'armor' && k === 'def') total += eo.enhancement * ENHANCE_BONUS.armor;
    }
    parts.push(STAT_NAMES[k] + '+' + total);
  }
  return parts.join(' ');
}
