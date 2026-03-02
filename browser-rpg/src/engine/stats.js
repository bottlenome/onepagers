/* ═══════════════════════════════════════
   ステータス計算・成長システム
   ═══════════════════════════════════════ */

// 装備なしの素のステータス
function calcNakedStats(p) {
  const s = {};
  for (const k of STAT_KEYS) {
    s[k] = INIT_STATS[k] + (p.baseStats[k] || 0) + (p.growthStats[k] || 0);
  }
  return s;
}

// 装備込みの完全ステータス
function calcStats(p) {
  const s = calcNakedStats(p);
  for (const slot of ['weapon','armor','accessory']) {
    const eo = p.equipObjs[slot];
    if (!eo) continue;
    const base = EQUIPS[eo.baseId];
    if (!base) continue;
    for (const [k,v] of Object.entries(base.s)) {
      s[k] = (s[k] || 0) + v;
    }
    // 強化ボーナス
    if (eo.enhancement > 0) {
      if (slot === 'weapon') s.atk += eo.enhancement * ENHANCE_BONUS.weapon;
      if (slot === 'armor')  s.def += eo.enhancement * ENHANCE_BONUS.armor;
    }
  }
  return { maxHp:s.hp, maxMp:s.mp, atk:s.atk, def:s.def, matk:s.matk, mdef:s.mdef, spd:s.spd };
}

// 成長率取得 (隠しパラメータ: 職業 + 装備)
function getGrowthRates(p) {
  const job = JOBS[p.jobId];
  const rates = {};
  for (const k of STAT_KEYS) rates[k] = job.rate[k] || 0;
  // 装備の成長率ボーナス
  for (const slot of ['weapon','armor','accessory']) {
    const eo = p.equipObjs[slot];
    if (!eo) continue;
    const base = EQUIPS[eo.baseId];
    if (!base || !base.g) continue;
    for (const [k,v] of Object.entries(base.g)) {
      rates[k] = Math.min(0.95, (rates[k] || 0) + v);
    }
  }
  return rates;
}

// レベルアップ処理
function processLevelUp(p) {
  const job = JOBS[p.jobId];
  const rates = getGrowthRates(p);
  const gains = {};
  for (const k of STAT_KEYS) {
    let g = job.base[k] || 0;
    if (Math.random() < (rates[k] || 0)) g += 1; // 隠し成長ボーナス
    p.growthStats[k] = (p.growthStats[k] || 0) + g;
    gains[k] = g;
  }
  p.level++;
  const st = calcStats(p);
  p.hp = Math.min(p.hp + gains.hp, st.maxHp);
  p.mp = Math.min(p.mp + gains.mp, st.maxMp);
  return gains;
}

// 経験値関連
function expForNextLevel(level) { return level * 10; }

function calcExpGain(playerLv, monsterLv) {
  if (playerLv > monsterLv) {
    // 高レベルで低い階層: 差が大きいほど経験値減少、差5超で0
    const diff = playerLv - monsterLv;
    if (diff > 5) return 0;
    return Math.max(1, Math.floor(15 + monsterLv - diff * 4));
  } else {
    // 低レベルで高い階層: 差が大きいほどボーナス
    const diff = monsterLv - playerLv;
    return Math.floor(15 + monsterLv + diff * 2);
  }
}

// 転職処理
function changeJob(p, newJobId) {
  const isBasic = JOBS[newJobId].type === 'basic';
  if (!p.jobHistory.includes(p.jobId)) p.jobHistory.push(p.jobId);
  if (isBasic) {
    // 下級職転職: Lv.1に戻り、成長分の70%を引き継ぐ
    const naked = calcNakedStats(p);
    const newBase = {};
    for (const k of STAT_KEYS) {
      const grown = (naked[k] || 0) - INIT_STATS[k];
      newBase[k] = Math.floor(grown * CARRY_RATIO_BASIC);
    }
    p.baseStats = newBase;
    p.growthStats = { hp:0, mp:0, atk:0, def:0, matk:0, mdef:0, spd:0 };
    p.level = 1;
    p.exp = 0;
  } else {
    // 上級職転職: ステータスボーナスを付与
    const advJob = JOBS[newJobId];
    for (const k of STAT_KEYS) {
      const bonus = Math.floor((advJob.base[k] || 0) * 3);
      p.growthStats[k] = (p.growthStats[k] || 0) + bonus;
    }
  }
  p.jobId = newJobId;
  const st = calcStats(p);
  p.hp = st.maxHp;
  p.mp = st.maxMp;
}

// 利用可能スキル一覧
function getAvailableSkills(p) {
  const skills = [];
  const job = JOBS[p.jobId];
  // 上級職スキル
  if (job.skills) {
    for (const js of job.skills) {
      if (p.level >= js.lv) skills.push(js.id);
    }
  }
  // 装備スキル
  for (const slot of ['weapon','armor','accessory']) {
    const eo = p.equipObjs[slot];
    if (!eo) continue;
    const base = EQUIPS[eo.baseId];
    if (!base) continue;
    const skillId = SUBTYPE_SKILL[base.sub];
    if (skillId && !skills.includes(skillId)) skills.push(skillId);
    // 鍛冶で付与された貴重スキル
    if (eo.grantedSkill && !skills.includes(eo.grantedSkill)) skills.push(eo.grantedSkill);
  }
  return skills;
}
