/* ═══════════════════════════════════════
   戦闘システム (自動戦闘)
   ═══════════════════════════════════════ */

function startBattle(enemy) {
  G.battle = {
    enemy,
    log: [],
    over: false,
    won: false,
    turn: 0,
    playerEffects: [],  // [{id, turns}]
    enemyEffects: [],
    specialUsed: false,
    specialReady: false,
  };
  G.screen = 'battle';
  render();
  runBattle();
}

function addBattleLog(msg, cls) {
  cls = cls || 'sys';
  G.battle.log.push({ msg, cls });
  updateBattleLog();
}

function updateBattleLog() {
  const el = document.getElementById('battle-log');
  if (!el) return;
  el.innerHTML = G.battle.log.map(e => `<div class="bl ${e.cls}">${e.msg}</div>`).join('');
  el.scrollTop = el.scrollHeight;
  // ヘッダー更新
  document.getElementById('hdr').innerHTML = renderHeader();
  // 敵HP更新
  const ehp = document.getElementById('enemy-hp');
  if (ehp && G.battle.enemy) {
    const e = G.battle.enemy;
    const pct = Math.max(0, e.hp / e.maxHp * 100);
    ehp.style.width = pct + '%';
  }
  const ehpNum = document.getElementById('enemy-hp-num');
  if (ehpNum && G.battle.enemy) {
    ehpNum.textContent = Math.max(0, G.battle.enemy.hp) + '/' + G.battle.enemy.maxHp;
  }
}

async function runBattle() {
  const p = G.player;
  const e = G.battle.enemy;
  const spd = G.settings.battleSpeed;

  if (G.demo) {
    addBattleLog('--- 遠い未来の戦いの記憶… ---', 'sys');
    await delay(spd);
  }
  addBattleLog(`${e.emoji} ${e.name} Lv.${e.level} が現れた！`, 'sys');
  if (e.def > e.mdef * 1.2) addBattleLog('堅い守り…呪文が効きそうだ', 'sys');
  else if (e.mdef > e.def * 1.2) addBattleLog('魔力の障壁…力技が有効だ', 'sys');
  await delay(spd);

  while (!G.battle.over) {
    G.battle.turn++;
    // デモバトル: 最大15ターンで打ち切り
    if (G.demo && G.battle.turn > 15) {
      G.battle.over = true;
      G.battle.won = true;
      handleVictory(p, e);
      break;
    }
    const pStats = calcStats(p);
    // 魔法使いパッシブ: 毎ターンMP回復
    const mpPassive = JOBS[p.jobId].passive;
    if (mpPassive && mpPassive.id === 'mp_regen') {
      p.mp = Math.min(p.mp + mpPassive.value, pStats.maxMp);
    }
    const playerFirst = pStats.spd >= e.spd;

    if (playerFirst) {
      await doPlayerAction(p, e, pStats);
      if (G.battle.over) break;
      await doEnemyAction(p, e, pStats);
    } else {
      await doEnemyAction(p, e, pStats);
      if (G.battle.over) break;
      await doPlayerAction(p, e, pStats);
    }
  }
}

async function doPlayerAction(p, e, pStats) {
  const spd = G.battle.specialReady ? G.settings.battleSpeed * 2 : G.settings.battleSpeed;
  // 効果チェック
  if (hasEffect(G.battle.playerEffects, 'stun')) {
    addBattleLog(`${p.name}は動けない！`, 'sys');
    tickEffects(G.battle.playerEffects);
    await delay(spd);
    return;
  }

  // 必殺技チェック
  if (G.battle.specialReady) {
    G.battle.specialReady = false;
    G.battle.specialUsed = true;
    G.battle.playerEffects.push({ id:'vulnerable', turns:2 });

    const skills = getAvailableSkills(p);
    const allAttacks = skills
      .filter(id => SKILLS[id] && ['physical','magical','hybrid'].includes(SKILLS[id].type))
      .sort((a,b) => (SKILLS[b].power||0) - (SKILLS[a].power||0));

    addBattleLog('— 必殺技発動！ —', 'lvup');
    if (allAttacks.length) {
      const sk = SKILLS[allAttacks[0]];
      const savedMp = p.mp;
      executeSkill(p, e, pStats, sk, allAttacks[0], true);
      p.mp = savedMp;
    } else {
      const dmg = calcPhysDamage(pStats.atk * 2, e.def);
      e.hp -= dmg;
      addBattleLog(`${p.name}の渾身の一撃！${dmg}のダメージ！`, 'p-atk');
    }
    addBattleLog('しかし隙が生じた…！', 'danger');
    await delay(spd);
    checkBattleEnd(p, e);
    tickEffects(G.battle.playerEffects);
    const specBtn = document.getElementById('btn-special');
    if (specBtn) specBtn.classList.add('hidden');
    return;
  }

  const action = selectPlayerAction(p, e, pStats);

  if (action.type === 'item') {
    const item = ITEMS[action.id];
    removeItem(p, action.id, 1);
    if (item.healHp) {
      const amt = item.healHp === -1 ? pStats.maxHp : item.healHp;
      p.hp = Math.min(p.hp + amt, pStats.maxHp);
    }
    if (item.healMp) {
      const amt = item.healMp === -1 ? pStats.maxMp : item.healMp;
      p.mp = Math.min(p.mp + amt, pStats.maxMp);
    }
    addBattleLog(`${p.name}は${item.name}を使った！`, 'p-heal');
  } else if (action.type === 'skill') {
    const sk = SKILLS[action.id];
    p.mp -= sk.cost;
    executeSkill(p, e, pStats, sk, action.id, true);
  } else if (action.type === 'defend') {
    G.battle.playerEffects.push({ id:'guard', turns:1 });
    addBattleLog(`${p.name}は身を守っている！`, 'sys');
  } else {
    // 通常攻撃
    const dmg = calcPhysDamage(pStats.atk, e.def);
    const crit = Math.random() < 0.05;
    const finalDmg = crit ? dmg * 2 : dmg;
    e.hp -= finalDmg;
    addBattleLog(`${p.name}の攻撃！${finalDmg}のダメージ！${crit ? '会心の一撃！' : ''}`, 'p-atk');
  }
  await delay(spd);
  checkBattleEnd(p, e);
  tickEffects(G.battle.playerEffects);
}

async function doEnemyAction(p, e, pStats) {
  const spd = G.battle.specialReady ? G.settings.battleSpeed * 2 : G.settings.battleSpeed;
  const isVuln = hasEffect(G.battle.playerEffects, 'vulnerable');
  if (hasEffect(G.battle.enemyEffects, 'stun')) {
    addBattleLog(`${e.name}は動けない！`, 'sys');
    tickEffects(G.battle.enemyEffects);
    await delay(spd);
    return;
  }
  // 特殊攻撃 (ボスごとの発動率, デフォルト30%)
  if (e.special && Math.random() < (e.specialRate || 0.30)) {
    const sk = SKILLS[e.special];
    if (sk) {
      const isMag = sk.type === 'magical' || sk.type === 'hybrid';
      const power = sk.power || 1.5;
      const dmg = isMag
        ? calcMagDamage(e.matk * power, pStats.mdef)
        : calcPhysDamage(e.atk * power, pStats.def);
      let reduced = applyDefenseEffects(dmg, G.battle.playerEffects, isMag);
      // 戦士パッシブ: 被ダメ軽減
      const psvS = JOBS[G.player.jobId].passive;
      if (psvS && psvS.id === 'dmg_reduce') reduced = Math.max(1, Math.floor(reduced * (1 - psvS.value)));
      p.hp -= reduced;
      addBattleLog(`${e.name}の${sk.name}！${reduced}のダメージ！`, 'e-atk');
      if (isVuln) flashRed();
      await delay(spd);
      checkBattleEnd(p, e);
      tickEffects(G.battle.enemyEffects);
      return;
    }
  }
  // 通常攻撃
  const dmg = calcPhysDamage(e.atk, pStats.def);
  let reduced = applyDefenseEffects(dmg, G.battle.playerEffects, false);
  // 戦士パッシブ: 被ダメ軽減
  const psvN = JOBS[G.player.jobId].passive;
  if (psvN && psvN.id === 'dmg_reduce') reduced = Math.max(1, Math.floor(reduced * (1 - psvN.value)));
  p.hp -= reduced;
  addBattleLog(`${e.name}の攻撃！${reduced}のダメージ！`, 'e-atk');
  if (isVuln) flashRed();
  await delay(spd);
  checkBattleEnd(p, e);
  tickEffects(G.battle.enemyEffects);
}

function executeSkill(user, target, userStats, sk, skillId, isPlayer) {
  const prefix = isPlayer ? G.player.name : G.battle.enemy.name;
  const atkCls = isPlayer ? 'p-atk' : 'e-atk';
  const magCls = isPlayer ? 'p-mag' : 'e-atk';
  const healCls = isPlayer ? 'p-heal' : 'sys';

  if (sk.type === 'physical') {
    const baseDmg = calcPhysDamage(userStats.atk * sk.power, target.def || calcStats(target).def || 0);
    const hits = sk.hits || 1;
    let totalDmg = 0;
    const crit = Math.random() < (sk.crit || 0.05);
    for (let i = 0; i < hits; i++) {
      let d = crit ? baseDmg * 2 : baseDmg;
      if (!isPlayer) d = applyDefenseEffects(d, G.battle.playerEffects, false);
      totalDmg += d;
    }
    if (isPlayer) { G.battle.enemy.hp -= totalDmg; }
    else { G.player.hp -= totalDmg; }
    addBattleLog(`${prefix}の${sk.name}！${totalDmg}のダメージ！${crit?'会心！':''}`, atkCls);
    if (sk.stun && Math.random() < sk.stun) {
      const effects = isPlayer ? G.battle.enemyEffects : G.battle.playerEffects;
      effects.push({ id:'stun', turns:1 });
      addBattleLog(`${isPlayer ? G.battle.enemy.name : G.player.name}は気絶した！`, 'sys');
    }
  } else if (sk.type === 'magical') {
    const dmg = calcMagDamage(userStats.matk * sk.power, target.mdef || 0);
    const finalDmg = isPlayer ? dmg : applyDefenseEffects(dmg, G.battle.playerEffects, true);
    if (isPlayer) { G.battle.enemy.hp -= finalDmg; }
    else { G.player.hp -= finalDmg; }
    addBattleLog(`${prefix}の${sk.name}！${finalDmg}のダメージ！`, magCls);
    if (sk.healPct && isPlayer) {
      const heal = Math.floor(calcStats(G.player).maxHp * sk.healPct);
      G.player.hp = Math.min(G.player.hp + heal, calcStats(G.player).maxHp);
      addBattleLog(`HPが${heal}回復した！`, 'p-heal');
    }
  } else if (sk.type === 'hybrid') {
    const pDmg = calcPhysDamage(userStats.atk * sk.power, target.def || 0);
    const mDmg = calcMagDamage(userStats.matk * sk.power, target.mdef || 0);
    const total = Math.floor((pDmg + mDmg) / 2);
    if (isPlayer) { G.battle.enemy.hp -= total; }
    else { G.player.hp -= applyDefenseEffects(total, G.battle.playerEffects, false); }
    addBattleLog(`${prefix}の${sk.name}！${total}のダメージ！`, atkCls);
  } else if (sk.type === 'heal') {
    const st = calcStats(G.player);
    const amt = Math.floor(st.maxHp * sk.power);
    G.player.hp = Math.min(G.player.hp + amt, st.maxHp);
    addBattleLog(`${prefix}の${sk.name}！HPが${amt}回復！`, healCls);
  } else if (sk.type === 'buff') {
    const effects = isPlayer ? G.battle.playerEffects : G.battle.enemyEffects;
    effects.push({ id:sk.effect, turns:3 });
    addBattleLog(`${prefix}の${sk.name}！`, 'sys');
  }
}

// AI: プレイヤー行動選択
function selectPlayerAction(p, e, pStats) {
  const skills = getAvailableSkills(p);
  const hpRatio = p.hp / pStats.maxHp;
  const strat = G.settings.strategy;

  // 利用可能スキル (MP足りるもの)
  const usable = skills.filter(id => SKILLS[id] && p.mp >= SKILLS[id].cost);
  const heals = usable.filter(id => SKILLS[id].type === 'heal');
  const attacks = usable
    .filter(id => ['physical','magical','hybrid'].includes(SKILLS[id].type))
    .sort((a,b) => (SKILLS[b].power||0) - (SKILLS[a].power||0));
  const healItem = findHealItem(p);

  switch (strat) {
    case 'physical': {
      // 力技: 物理スキル優先、攻め重視
      if (hpRatio < 0.2 && heals.length) return { type:'skill', id:heals[0] };
      if (hpRatio < 0.15 && healItem) return { type:'item', id:healItem };
      const phys = attacks.filter(id => SKILLS[id].type === 'physical');
      if (phys.length) return { type:'skill', id:phys[0] };
      if (attacks.length) return { type:'skill', id:attacks[0] };
      return { type:'attack' };
    }
    case 'magical': {
      // 呪文: 魔法スキル優先、攻め重視
      if (hpRatio < 0.2 && heals.length) return { type:'skill', id:heals[0] };
      if (hpRatio < 0.15 && healItem) return { type:'item', id:healItem };
      const mags = attacks.filter(id => ['magical','hybrid'].includes(SKILLS[id].type));
      if (mags.length) return { type:'skill', id:mags[0] };
      if (attacks.length) return { type:'skill', id:attacks[0] };
      return { type:'attack' };
    }
    default: {
      // 万能: 弱点自動判定、安全重視
      if (hpRatio < 0.4 && heals.length) return { type:'skill', id:heals[0] };
      if (hpRatio < 0.35 && healItem) return { type:'item', id:healItem };
      const preferMag = e.mdef < e.def;
      const pref = preferMag
        ? attacks.filter(id => ['magical','hybrid'].includes(SKILLS[id].type))
        : attacks.filter(id => SKILLS[id].type === 'physical');
      if (pref.length) return { type:'skill', id:pref[0] };
      if (attacks.length) return { type:'skill', id:attacks[0] };
      return { type:'attack' };
    }
  }
}

function findHealItem(p) {
  for (const id of ['elixir','world_branch','hi_herb','herb']) {
    if (hasItem(p, id, 1)) return id;
  }
  return null;
}

// ダメージ計算
function calcPhysDamage(atk, def) {
  return Math.max(1, Math.floor(atk - def * 0.5) + rand(-2, 2));
}
function calcMagDamage(matk, mdef) {
  return Math.max(1, Math.floor(matk - mdef * 0.5) + rand(-2, 2));
}

// 防御効果適用
function applyDefenseEffects(dmg, effects, isMagic) {
  if (hasEffect(effects, 'invincible')) {
    removeEffect(effects, 'invincible');
    return 0;
  }
  if (hasEffect(effects, 'guard')) dmg = Math.floor(dmg * 0.5);
  if (hasEffect(effects, 'ironwall')) dmg = Math.floor(dmg * 0.3);
  if (hasEffect(effects, 'smoke') && Math.random() < 0.5) return 0;
  if (hasEffect(effects, 'evade') && Math.random() < 0.5) return 0;
  if (isMagic && hasEffect(effects, 'mbarrier')) dmg = Math.floor(dmg * 0.5);
  if (hasEffect(effects, 'vulnerable')) dmg = Math.floor(dmg * 2);
  return Math.max(1, dmg);
}

// 効果管理
function hasEffect(effects, id) { return effects.some(e => e.id === id); }
function removeEffect(effects, id) {
  const idx = effects.findIndex(e => e.id === id);
  if (idx >= 0) effects.splice(idx, 1);
}
function tickEffects(effects) {
  for (let i = effects.length - 1; i >= 0; i--) {
    effects[i].turns--;
    if (effects[i].turns <= 0) effects.splice(i, 1);
  }
}

// 戦闘終了チェック
function checkBattleEnd(p, e) {
  if (e.hp <= 0) {
    e.hp = 0;
    G.battle.over = true;
    G.battle.won = true;
    handleVictory(p, e);
  } else if (p.hp <= 0) {
    p.hp = 0;
    G.battle.over = true;
    G.battle.won = false;
    handleDefeat(p, e);
  }
}

async function handleVictory(p, e) {
  const spd = G.settings.battleSpeed;
  addBattleLog(`${e.name}を倒した！`, 'reward');
  await delay(spd);

  // デモバトル: 報酬処理スキップ
  if (G.demo) {
    addBattleLog('勝利！', 'lvup');
    await delay(spd * 2);
    G.battle.continueOverride = '<button class="btn primary" data-a="battleend">続ける</button>';
    G.battle.showContinue = true;
    const cont = document.getElementById('battle-continue');
    if (cont) {
      cont.innerHTML = G.battle.continueOverride;
      cont.classList.remove('hidden');
    }
    return;
  }

  // 僧侶パッシブ: 戦闘勝利後HP回復
  const priestPsv = JOBS[p.jobId].passive;
  if (priestPsv && priestPsv.id === 'post_heal') {
    const stH = calcStats(p);
    const healAmt = Math.floor(stH.maxHp * priestPsv.value);
    p.hp = Math.min(p.hp + healAmt, stH.maxHp);
    addBattleLog(`祝福の力でHPが${healAmt}回復した`, 'p-heal');
    await delay(spd);
  }

  // EXP
  const exp = e.boss ? Math.floor(e.level * 5) : calcExpGain(p.level, e.level);
  if (exp > 0) {
    p.exp += exp;
    addBattleLog(`経験値${exp}を獲得！`, 'reward');
  }

  // ゴールド
  const gold = e.boss ? e.level * 30 : e.level * 3 + rand(0, e.level * 2);
  p.gold += gold;
  addBattleLog(`${gold}Gを獲得！`, 'reward');
  await delay(spd);

  // ドロップ
  if (e.drops) {
    const thiefPsv = JOBS[p.jobId].passive;
    const dropBonus = (thiefPsv && thiefPsv.id === 'drop_bonus') ? thiefPsv.value : 0;
    for (const d of e.drops) {
      if (Math.random() < d.rate + dropBonus) {
        addItemToPlayer(p, d.id, 1);
        const info = ITEMS[d.id] || EQUIPS[d.id];
        addBattleLog(`${info ? info.name : d.id}を手に入れた！`, 'reward');
        await delay(spd);
      }
    }
  }

  // ダンジョン宝箱
  const areaId = p.location.type === 'field' ? p.location.area : null;
  const isDungeon = areaId && AREA_INFO[areaId] && AREA_INFO[areaId].dungeon;
  if (isDungeon && !e.boss && Math.random() < 0.15) {
    const chest = openTreasureChest(e.level);
    addBattleLog(`宝箱を発見！${chest}`, 'reward');
    await delay(spd);
  }

  // ボス称号
  if (e.boss && e.title && !p.titles.includes(e.title)) {
    p.titles.push(e.title);
    addBattleLog(`称号「${e.title}」を獲得！`, 'lvup');
    await delay(spd);
  }

  // ボス撃破カウント
  if (e.boss && e.defeatKey) {
    p.bossDefeats[e.defeatKey] = (p.bossDefeats[e.defeatKey] || 0) + 1;
  }

  // レベルアップ
  while (p.exp >= expForNextLevel(p.level) && p.level < MAX_LEVEL) {
    p.exp -= expForNextLevel(p.level);
    const { gains, bonuses } = processLevelUp(p);
    addBattleLog(`レベルアップ！Lv.${p.level-1} → Lv.${p.level}`, 'lvup');
    const parts = STAT_KEYS.filter(k => gains[k] > 0).map(k => {
      if (bonuses[k]) return `<span class="bonus-growth">${STAT_NAMES[k]}+${gains[k]} ★</span>`;
      return STAT_NAMES[k]+'+'+gains[k];
    });
    if (parts.length) addBattleLog(parts.join(' '), 'lvup');
    // 転職後初回レベルアップメッセージ
    if (p.postTransferLevelUp && (p.jobChangeCount || 0) > 0) {
      addBattleLog('以前の経験が体に染み付いている…前より強い気がする', 'sys');
      p.postTransferLevelUp = false;
    }
    // 新スキル習得チェック
    const job = JOBS[p.jobId];
    if (job.skills) {
      for (const js of job.skills) {
        if (js.lv === p.level) {
          addBattleLog(`${SKILLS[js.id].name}を習得した！`, 'lvup');
        }
      }
    }
    await delay(spd);
  }

  // 武器耐久値減少
  degradeWeapon(p);

  saveGame();
  // 戻るボタン表示
  G.battle.showContinue = true;
  const cont = document.getElementById('battle-continue');
  if (cont) cont.classList.remove('hidden');
}

async function handleDefeat(p, e) {
  addBattleLog(`${p.name}は力尽きた…`, 'danger');
  await delay(800);

  // デモバトル: ペナルティなし
  if (G.demo) {
    addBattleLog('…だが、諦めない。', 'sys');
    await delay(600);
    G.battle.continueOverride = '<button class="btn primary" data-a="battleend">続ける</button>';
    G.battle.showContinue = true;
    const cont = document.getElementById('battle-continue');
    if (cont) {
      cont.innerHTML = G.battle.continueOverride;
      cont.classList.remove('hidden');
    }
    return;
  }

  // ゴールドペナルティ
  const lostGold = Math.floor(p.gold * DEATH_GOLD_PENALTY);
  if (lostGold > 0) {
    p.gold -= lostGold;
    addBattleLog(`${lostGold}Gを落としてしまった…`, 'danger');
    await delay(400);
  }
  if (p.bankGold > 0) {
    addBattleLog(`銀行の預金${p.bankGold.toLocaleString()}Gは無事だ`, 'sys');
    await delay(400);
  }
  addBattleLog('最後に訪れた町で目を覚ました…', 'sys');
  p.hp = 1;
  p.location = { type:'town', id: p.lastTown || 'town1' };
  saveGame();
  G.battle.continueOverride = '<button class="btn primary" data-a="battleend">続ける</button>';
  G.battle.showContinue = true;
  const cont = document.getElementById('battle-continue');
  if (cont) {
    cont.innerHTML = G.battle.continueOverride;
    cont.classList.remove('hidden');
  }
}

// 宝箱
function openTreasureChest(level) {
  const r = Math.random();
  if (r < 0.5) {
    const g = level * 10 + rand(0, level * 5);
    G.player.gold += g;
    return `${g}G入っていた！`;
  } else if (r < 0.8) {
    const items = ['herb','hi_herb','magic_water','tent'];
    const id = items[rand(0, items.length-1)];
    addItemToPlayer(G.player, id, 1);
    return `${ITEMS[id].name}が入っていた！`;
  } else {
    const rare = ['mithril_ore','spirit_stone','dark_crystal'];
    const id = rare[rand(0, rare.length-1)];
    addItemToPlayer(G.player, id, 1);
    return `${ITEMS[id].name}が入っていた！`;
  }
}

// 武器耐久値減少
function degradeWeapon(p) {
  const wep = p.equipObjs.weapon;
  if (!wep || wep.maxDurability === 0) return;
  wep.durability--;
  if (wep.durability <= 0) {
    const name = EQUIPS[wep.baseId].name;
    p.equipObjs.weapon = null;
    addBattleLog(`${name}が壊れた！`, 'danger');
    addLog(`${name}が壊れた！`, 'danger');
  }
}
