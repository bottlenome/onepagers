/* ═══════════════════════════════════════
   画面レンダリング
   ═══════════════════════════════════════ */

// --- タイトル画面 ---
function screenTitle() {
  const canContinue = hasSave();
  return `
    <div class="title-screen">
      <a class="back" href="../index.html">&larr; OnePagers</a>
      <div class="icon">⚔️</div>
      <h1>Loveless Chronicle</h1>
      <p class="sub">転職・スキル・自動戦闘RPG</p>
      <div class="btn-row">
        <button class="btn primary" data-a="newgame">はじめから</button>
        ${canContinue ? '<button class="btn" data-a="continue">つづきから</button>' : ''}
      </div>
    </div>`;
}

// --- 名前・職業選択 ---
function screenNaming() {
  const jobs = Object.entries(JOBS).filter(([,j]) => j.type === 'basic');
  return `
    <div class="naming">
      <h2>冒険者の名前を入力</h2>
      <input type="text" id="name-input" maxlength="8" placeholder="なまえ" value="勇者">
      <h2 class="mt-2">職業を選択</h2>
      <div class="job-grid">
        ${jobs.map(([id,j]) => `
          <div class="job-card" data-a="selectjob" data-p="${id}" id="jc-${id}">
            <div class="name">${j.name}</div>
            <div class="desc">${j.desc}</div>
            <div class="stats">${STAT_KEYS.map(k => STAT_NAMES[k]+':'+j.base[k]).join(' ')}</div>
          </div>`).join('')}
      </div>
      <button class="btn primary mt-2" data-a="startgame" id="btn-start" disabled>冒険に出発！</button>
    </div>`;
}

// --- 町画面 ---
function screenTown() {
  const p = G.player;
  const tid = p.location.id;
  const town = TOWN_INFO[tid];
  const facilities = TOWN_FACILITIES[tid] || [];
  const exits = TOWN_EXITS[tid] || [];

  return `
    <h2>${town ? town.name : tid}</h2>
    <div class="card-grid">
      ${facilities.map((f,i) => `
        <div class="facility-btn" data-a="facility" data-p="${f.id}" data-p2="${f.shopId||f.cost||f.advanced||''}" data-p3="${i}">
          <div class="icon">${f.icon}</div>
          <div class="label">${f.label}</div>
        </div>`).join('')}
    </div>
    <div class="sep"></div>
    <h3>移動</h3>
    <div class="btn-row">
      ${exits.map(e => `<button class="btn small" data-a="movefield" data-p="${e.area}" data-p2="${e.layer}">${e.label}</button>`).join('')}
    </div>`;
}

// --- フィールド画面 ---
function screenField() {
  const p = G.player;
  const { area, layer } = p.location;
  const info = AREA_INFO[area];
  const exits = getFieldExits(area, layer);

  // 古城隠し通路判定
  const showHidden = area === 'old_castle' && layer === 25 &&
    (p.bossDefeats.old_castle_boss_defeats || 0) >= 10;

  return `
    <div class="field-info">
      <div class="area-name">${info ? info.name : area}</div>
      <div class="layer">階層 ${layer}</div>
      ${info && info.dungeon ? '<div class="text-muted" style="font-size:0.8rem">ダンジョン</div>' : ''}
    </div>
    <div class="btn-row" style="justify-content:center">
      <button class="btn primary" data-a="explore">探索する</button>
      <button class="btn" data-a="screen" data-p="status">ステータス</button>
    </div>
    <div class="sep"></div>
    <h3>移動</h3>
    <div class="btn-row">
      ${exits.map(e => {
        if (e.type === 'town') return `<button class="btn small" data-a="movetown" data-p="${e.id}">${e.label}</button>`;
        return `<button class="btn small" data-a="movefield" data-p="${e.area}" data-p2="${e.layer}">${e.label}</button>`;
      }).join('')}
      ${showHidden ? '<button class="btn small danger" data-a="movefield" data-p="old_castle_hidden" data-p2="25">隠し通路へ…</button>' : ''}
    </div>`;
}

// --- 戦闘画面 ---
function screenBattle() {
  if (!G.battle) return '<p>...</p>';
  const e = G.battle.enemy;
  const hpPct = Math.max(0, e.hp / e.maxHp * 100);
  return `
    <div class="battle-enemy">
      <div class="emoji">${e.emoji}</div>
      <div class="name">${e.name} Lv.${e.level}${e.boss?' [BOSS]':''}</div>
      <div style="max-width:200px;margin:4px auto">
        <div class="bar-track"><div class="bar-fill hp" id="enemy-hp" style="width:${hpPct}%"></div></div>
        <div class="text-muted" style="font-size:0.75rem" id="enemy-hp-num">${Math.max(0,e.hp)}/${e.maxHp}</div>
      </div>
    </div>
    <div class="btn-row" style="justify-content:center">
      <button class="btn small" data-a="battlespeed">${G.settings.battleSpeed <= 200 ? '通常速度' : '高速'}</button>
    </div>
    <div class="battle-log" id="battle-log">
      ${G.battle.log.map(l => `<div class="bl ${l.cls}">${l.msg}</div>`).join('')}
    </div>
    <div class="text-center mt-1">
      <button class="btn primary hidden" id="battle-continue" data-a="battleend">続ける</button>
    </div>`;
}

// --- ショップ画面 ---
function screenShop() {
  const shop = SHOPS[G.shopId];
  if (!shop) return backBtn() + '<p>ショップが見つからない</p>';
  const p = G.player;

  let itemsHtml = '';
  if (G.shopTab === 'buy') {
    itemsHtml = shop.items.map((si, i) => {
      const info = si.isEquip ? EQUIPS[si.id] : ITEMS[si.id];
      if (!info) return '';
      const price = info.price;
      const canBuy = p.gold >= price;
      const detail = si.isEquip ? equipStatSummary(si.id) : info.desc;
      return `<div class="shop-item">
        <div class="info"><div class="name">${info.name}</div><div class="detail">${detail}</div></div>
        <div class="price">${price}G</div>
        <button class="btn small${canBuy?'':' disabled'}" data-a="buy" data-p="${i}" ${canBuy?'':'disabled'}>購入</button>
      </div>`;
    }).join('');
  } else {
    // 売却: アイテム
    const sellItems = p.items.filter(it => (ITEMS[it.id] || {}).price > 0).map(it => {
      const info = ITEMS[it.id];
      return `<div class="shop-item">
        <div class="info"><div class="name">${info.name} x${it.count}</div></div>
        <div class="price">${Math.floor(info.price*0.5)}G</div>
        <button class="btn small" data-a="sell" data-p="${it.id}" data-p2="item">売却</button>
      </div>`;
    }).join('');
    const sellEquips = p.equipBag.map((eo, i) => {
      const base = EQUIPS[eo.baseId];
      return `<div class="shop-item">
        <div class="info"><div class="name">${equipName(eo)}</div><div class="detail">${equipStatText(eo)}</div></div>
        <div class="price">${Math.floor(base.price*0.5)}G</div>
        <button class="btn small" data-a="sell" data-p="${i}" data-p2="equip">売却</button>
      </div>`;
    }).join('');
    itemsHtml = sellItems + sellEquips;
    if (!itemsHtml) itemsHtml = '<p class="text-muted text-center">売れるものがない</p>';
  }

  return `
    ${backBtn()}
    <h2>${shop.name}</h2>
    <div class="tabs">
      <div class="tab ${G.shopTab==='buy'?'active':''}" data-a="shoptab" data-p="buy">購入</div>
      <div class="tab ${G.shopTab==='sell'?'active':''}" data-a="shoptab" data-p="sell">売却</div>
    </div>
    <div class="panel">${itemsHtml}</div>`;
}

function equipStatSummary(eqId) {
  const eq = EQUIPS[eqId];
  if (!eq) return '';
  const parts = Object.entries(eq.s).map(([k,v]) => STAT_NAMES[k]+'+'+v);
  if (eq.dur > 0) parts.push('耐久'+eq.dur);
  return parts.join(' ');
}

// --- ステータス画面 ---
function screenStatus() {
  const p = G.player;
  const st = calcStats(p);
  const job = JOBS[p.jobId];
  const tab = G.statusTab;

  let content = '';
  if (tab === 'stats') {
    content = `
      <table class="stat-table">
        ${STAT_KEYS.filter(k=>k!=='hp'&&k!=='mp').map(k =>
          `<tr><td class="label">${STAT_NAMES[k]}</td><td class="val">${st[k]}</td></tr>`
        ).join('')}
      </table>
      <div class="mt-1 text-muted" style="font-size:0.8rem">
        職業: ${job.name} | 経験済: ${p.jobHistory.map(j=>JOBS[j].name).join(', ')||'なし'}<br>
        称号: ${p.titles.join(', ')||'なし'}
      </div>`;
  } else if (tab === 'equip') {
    content = ['weapon','armor','accessory'].map(slot => {
      const eo = p.equipObjs[slot];
      const slotName = {weapon:'武器',armor:'防具',accessory:'アクセサリー'}[slot];
      if (!eo) return `<div class="equip-slot"><span class="slot-label">${slotName}</span><span class="slot-empty">なし</span></div>`;
      return `<div class="equip-slot">
        <span class="slot-label">${slotName}</span>
        <span class="slot-item">${equipName(eo)} ${durabilityText(eo)}<br><span class="text-muted" style="font-size:0.75rem">${equipStatText(eo)}</span></span>
        <button class="btn small" data-a="unequip" data-p="${slot}">外す</button>
      </div>`;
    }).join('') +
    '<div class="sep"></div><h3>装備バッグ</h3>' +
    (p.equipBag.length === 0 ? '<p class="text-muted">なし</p>' :
      p.equipBag.map((eo,i) => {
        const base = EQUIPS[eo.baseId];
        return `<div class="shop-item">
          <div class="info"><div class="name">${equipName(eo)} ${durabilityText(eo)}</div><div class="detail">${equipStatText(eo)}</div></div>
          <button class="btn small" data-a="equip" data-p="${i}">装備</button>
        </div>`;
      }).join(''));
  } else if (tab === 'items') {
    content = p.items.length === 0 ? '<p class="text-muted">アイテムなし</p>' :
      p.items.map(it => {
        const info = ITEMS[it.id];
        if (!info) return '';
        const canUse = info.type === 'consumable' && (info.healHp || info.healMp);
        return `<div class="shop-item">
          <div class="info"><div class="name">${info.name} x${it.count}</div><div class="detail">${info.desc}</div></div>
          ${canUse ? `<button class="btn small" data-a="useitem" data-p="${it.id}">使う</button>` : ''}
        </div>`;
      }).join('');
  } else if (tab === 'skills') {
    const skills = getAvailableSkills(p);
    content = skills.length === 0 ? '<p class="text-muted">スキルなし</p>' :
      skills.map(id => {
        const sk = SKILLS[id];
        if (!sk) return '';
        return `<div class="shop-item">
          <div class="info"><div class="name">${sk.name}</div><div class="detail">${sk.desc} | MP${sk.cost||0}</div></div>
        </div>`;
      }).join('');
  }

  // 作戦選択
  const stratHtml = STRATEGIES.map(s =>
    `<button class="btn small ${G.settings.strategy===s.id?'primary':''}" data-a="strategy" data-p="${s.id}">${s.name}</button>`
  ).join('');

  return `
    ${backBtn()}
    <h2>ステータス</h2>
    <div class="tabs">
      <div class="tab ${tab==='stats'?'active':''}" data-a="statustab" data-p="stats">能力</div>
      <div class="tab ${tab==='equip'?'active':''}" data-a="statustab" data-p="equip">装備</div>
      <div class="tab ${tab==='items'?'active':''}" data-a="statustab" data-p="items">持ち物</div>
      <div class="tab ${tab==='skills'?'active':''}" data-a="statustab" data-p="skills">スキル</div>
    </div>
    <div class="panel">${content}</div>
    <div class="sep"></div>
    <h3>作戦</h3>
    <div class="btn-row">${stratHtml}</div>`;
}

// --- 転職画面 ---
function screenJobChange() {
  const p = G.player;
  const advanced = G.jobChangeAdvanced;
  const isCurrentAdvanced = JOBS[p.jobId].type === 'advanced';
  const available = Object.entries(JOBS).filter(([id, j]) => {
    if (advanced) return j.type === 'advanced' && p.level >= 15;
    return j.type === 'basic';
  });
  return `
    ${backBtn()}
    <h2>${advanced ? '上級職転職場' : '転職場'}</h2>
    <div class="panel">
      <p class="text-muted mb-1">${advanced
        ? 'レベル・ステータスはそのまま上級職に転職できます。'
        : '転職するとLv.1に戻ります。ステータスの70%を引き継ぎます。'}</p>
      ${advanced && p.level < 15 ? '<p class="text-danger">上級職にはLv.15以上必要です</p>' : ''}
      ${advanced && isCurrentAdvanced ? '<p class="text-danger">上級職からは転職できません。下級職に戻してから転職してください。</p>' : ''}
    </div>
    <div class="job-grid">
      ${available.map(([id,j]) => `
        <div class="job-card" data-a="dojobchange" data-p="${id}">
          <div class="name">${j.name}${id===p.jobId?' (現在)':''}</div>
          <div class="desc">${j.desc}</div>
          <div class="stats">${STAT_KEYS.map(k => STAT_NAMES[k]+':'+j.base[k]).join(' ')}</div>
        </div>`).join('')}
    </div>`;
}

// --- 宿屋画面 ---
function screenInn() {
  const cost = G.innCost || 10;
  const p = G.player;
  const st = calcStats(p);
  const full = p.hp >= st.maxHp && p.mp >= st.maxMp;
  return `
    ${backBtn()}
    <h2>宿屋</h2>
    <div class="msg-box">
      <p>一晩${cost}Gで泊まれます。HP・MPが全回復します。</p>
      <p class="mt-1">HP: ${p.hp}/${st.maxHp} | MP: ${p.mp}/${st.maxMp}</p>
      <button class="btn primary mt-2 ${full || p.gold < cost ? 'disabled' : ''}"
        data-a="doinn" data-p="${cost}"
        ${full || p.gold < cost ? 'disabled' : ''}>
        ${full ? '全回復済み' : p.gold < cost ? 'ゴールド不足' : `泊まる (${cost}G)`}
      </button>
    </div>`;
}

// --- 闘技場画面 ---
function screenArena() {
  const p = G.player;
  const prog = p.arenaProgress;
  const opp = ARENA_OPPONENTS[prog];
  const allDone = !opp;

  return `
    ${backBtn()}
    <h2>闘技場</h2>
    <div class="panel">
      <p class="text-muted">参加費: ${ARENA_ENTRY_FEE}G | 勝利賞金: 対戦相手Lv×20G</p>
      <p class="text-muted">全勝で称号獲得！負けると最初から。</p>
      ${p.arenaUndefeated ? '<p class="text-success">現在無敗</p>' : '<p class="text-danger">再挑戦中</p>'}
    </div>
    <h3>進捗: ${prog}/${ARENA_OPPONENTS.length}</h3>
    ${ARENA_OPPONENTS.map((o,i) => `
      <div class="shop-item">
        <div class="info">
          <div class="name">${o.emoji} ${o.name} Lv.${o.level}</div>
          <div class="detail">賞金: ${o.level*20}G</div>
        </div>
        <span>${i < prog ? '✅' : i === prog ? '⚔️' : '🔒'}</span>
      </div>`).join('')}
    ${allDone
      ? '<div class="msg-box"><p class="text-success">全対戦者に勝利！</p></div>'
      : `<button class="btn primary mt-1" data-a="doarena" ${p.gold<ARENA_ENTRY_FEE?'disabled':''}>挑戦する (${ARENA_ENTRY_FEE}G)</button>`
    }`;
}

// --- 銀行画面 ---
function screenBank() {
  const p = G.player;
  return `
    ${backBtn()}
    <h2>銀行</h2>
    <div class="panel">
      <p>所持金: <span class="text-gold">${p.gold.toLocaleString()}G</span></p>
      <p>預金: <span class="text-gold">${p.bankGold.toLocaleString()}G</span></p>
      <p class="text-muted" style="font-size:0.8rem">預入手数料: 5%</p>
    </div>
    <div class="btn-row">
      <button class="btn" data-a="bankdeposit" data-p="100" ${p.gold<105?'disabled':''}>100G預ける</button>
      <button class="btn" data-a="bankdeposit" data-p="1000" ${p.gold<1050?'disabled':''}>1000G預ける</button>
    </div>
    <div class="btn-row">
      <button class="btn" data-a="bankwithdraw" data-p="100" ${p.bankGold<100?'disabled':''}>100G引き出す</button>
      <button class="btn" data-a="bankwithdraw" data-p="1000" ${p.bankGold<1000?'disabled':''}>1000G引き出す</button>
    </div>`;
}

// --- 倉庫画面 ---
function screenWarehouse() {
  const p = G.player;
  // 預ける
  const storeItems = p.items.map(it => {
    const info = ITEMS[it.id];
    return `<div class="shop-item">
      <div class="info"><div class="name">${info?info.name:it.id} x${it.count}</div></div>
      <button class="btn small" data-a="whstore" data-p="${it.id}" data-p2="item">預ける(10G)</button>
    </div>`;
  }).join('');
  const storeEquips = p.equipBag.map((eo,i) =>
    `<div class="shop-item">
      <div class="info"><div class="name">${equipName(eo)}</div></div>
      <button class="btn small" data-a="whstore" data-p="${i}" data-p2="equip">預ける(10G)</button>
    </div>`).join('');
  // 引き出す
  const retItems = p.warehouse.map(it => {
    const info = ITEMS[it.id];
    return `<div class="shop-item">
      <div class="info"><div class="name">${info?info.name:it.id} x${it.count}</div></div>
      <button class="btn small" data-a="whretrieve" data-p="${it.id}" data-p2="item">引き出す</button>
    </div>`;
  }).join('');
  const retEquips = p.warehouseEquips.map((eo,i) =>
    `<div class="shop-item">
      <div class="info"><div class="name">${equipName(eo)}</div></div>
      <button class="btn small" data-a="whretrieve" data-p="${i}" data-p2="equip">引き出す</button>
    </div>`).join('');

  return `
    ${backBtn()}
    <h2>倉庫</h2>
    <div class="panel"><p class="text-muted">預け手数料: 1個10G / 引き出し無料</p></div>
    <h3>預ける</h3>
    <div class="panel">${storeItems}${storeEquips || '<p class="text-muted">なし</p>'}</div>
    <h3>引き出す</h3>
    <div class="panel">${retItems}${retEquips || '<p class="text-muted">なし</p>'}</div>`;
}

// --- 鍛冶屋画面 ---
function screenBlacksmith() {
  const p = G.player;
  // 製造
  const craftHtml = SMITH_RECIPES.map((r,i) => {
    const can = canSmith(r);
    const outEq = EQUIPS[r.output];
    return `<div class="recipe-item">
      <div class="recipe-name">${outEq?outEq.name:r.output}</div>
      <div class="recipe-mats">${r.desc} | ${r.fee}G</div>
      <div class="recipe-rate">成功率: ${rateText(r.rate)}</div>
      <button class="btn small mt-1 ${can?'':'disabled'}" data-a="dosmith" data-p="${i}" ${can?'':'disabled'}>製造</button>
    </div>`;
  }).join('');

  // 修理
  const repairTargets = [];
  if (p.equipObjs.weapon && canRepair(p.equipObjs.weapon)) {
    const eo = p.equipObjs.weapon;
    repairTargets.push(`<div class="shop-item">
      <div class="info"><div class="name">${equipName(eo)} ${durabilityText(eo)}</div></div>
      <div class="price">${getRepairCost(eo)}G</div>
      <button class="btn small" data-a="dorepair" data-p="weapon">修理</button>
    </div>`);
  }
  p.equipBag.forEach((eo,i) => {
    if (canRepair(eo)) {
      repairTargets.push(`<div class="shop-item">
        <div class="info"><div class="name">${equipName(eo)} ${durabilityText(eo)}</div></div>
        <div class="price">${getRepairCost(eo)}G</div>
        <button class="btn small" data-a="dorepairbag" data-p="${i}">修理</button>
      </div>`);
    }
  });

  return `
    ${backBtn()}
    <h2>鍛冶屋</h2>
    <h3>製造</h3>
    <div class="panel">${craftHtml}</div>
    <h3>修理</h3>
    <div class="panel">
      <p class="text-muted mb-1">修理のたびに最大耐久値が5%低下します</p>
      ${repairTargets.length ? repairTargets.join('') : '<p class="text-muted">修理が必要な武器なし</p>'}
    </div>`;
}

// --- 合成屋画面 ---
function screenSynthesis() {
  const synthHtml = SYNTH_RECIPES.map((r,i) => {
    const can = canSynth(r);
    return `<div class="recipe-item">
      <div class="recipe-name">${r.desc}</div>
      <div class="recipe-rate">成功率: ${rateText(r.rate)} <span class="text-danger" style="font-size:0.75rem">失敗で素材消失</span></div>
      <button class="btn small mt-1 ${can?'':'disabled'}" data-a="dosynth" data-p="${i}" ${can?'':'disabled'}>合成</button>
    </div>`;
  }).join('');

  return `
    ${backBtn()}
    <h2>合成屋</h2>
    <div class="panel"><p class="text-muted">2つのアイテムを合成して新しいアイテムを作ります。失敗すると両方失われます。</p></div>
    <div class="panel">${synthHtml}</div>`;
}

// --- 強化所画面 ---
function screenEnhancement() {
  const p = G.player;
  const targets = [];

  // 装備中の武器・防具
  for (const slot of ['weapon','armor']) {
    const eo = p.equipObjs[slot];
    if (eo && canEnhance(eo)) {
      const cost = getEnhanceCost(eo);
      const rate = getEnhanceRate(eo);
      targets.push(`<div class="recipe-item">
        <div class="recipe-name">${equipName(eo)} → +${eo.enhancement+1}</div>
        <div class="recipe-mats">${equipStatText(eo)}</div>
        <div class="recipe-rate">成功率: ${rateText(rate)} | ${cost}G <span class="text-danger" style="font-size:0.75rem">失敗で装備消滅</span></div>
        <button class="btn small mt-1 ${p.gold>=cost?'':'disabled'}" data-a="doenhance" data-p="equipped_${slot}" ${p.gold>=cost?'':'disabled'}>強化</button>
      </div>`);
    }
  }
  // バッグ内装備
  p.equipBag.forEach((eo,i) => {
    if (canEnhance(eo)) {
      const cost = getEnhanceCost(eo);
      const rate = getEnhanceRate(eo);
      targets.push(`<div class="recipe-item">
        <div class="recipe-name">${equipName(eo)} → +${eo.enhancement+1}</div>
        <div class="recipe-mats">${equipStatText(eo)}</div>
        <div class="recipe-rate">成功率: ${rateText(rate)} | ${cost}G <span class="text-danger" style="font-size:0.75rem">失敗で装備消滅</span></div>
        <button class="btn small mt-1 ${p.gold>=cost?'':'disabled'}" data-a="doenhance" data-p="bag" data-p2="${i}" ${p.gold>=cost?'':'disabled'}>強化</button>
      </div>`);
    }
  });

  return `
    ${backBtn()}
    <h2>強化所</h2>
    <div class="panel"><p class="text-muted">武器・防具を強化します（最大+${MAX_ENHANCE}）。強化値が高いほど失敗しやすくなり、失敗すると装備が壊れます。</p></div>
    ${targets.length ? targets.join('') : '<p class="text-muted text-center">強化可能な装備がありません</p>'}`;
}
