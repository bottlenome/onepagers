/* ═══════════════════════════════════════
   装備データ
   slot: weapon / armor / accessory
   sub: サブタイプ (スキル決定用)
   dur: 耐久値 (weaponのみ)
   s: ステータスボーナス
   g: 成長率ボーナス (隠しパラメータ)
   ═══════════════════════════════════════ */
const EQUIPS = {};
[
  // --- 武器: 剣 ---
  //  id                  name          slot     sub     price dur  stats                    growthBonus
  ['wooden_stick',       '木の棒',     'weapon','sword', 10,   15, {atk:2},                 {}],
  ['copper_sword',       '銅の剣',     'weapon','sword', 50,   25, {atk:5},                 {atk:.05}],
  ['iron_sword',         '鉄の剣',     'weapon','sword', 200,  35, {atk:10},                {atk:.08}],
  ['steel_sword',        '鋼の剣',     'weapon','sword', 500,  45, {atk:18},                {atk:.10}],
  ['mithril_sword',      'ミスリルの剣','weapon','sword',1500, 60, {atk:30},                {atk:.12}],
  ['legendary_sword',    '伝説の剣',   'weapon','sword', 0,   100, {atk:50},                {atk:.15}],
  ['orichalcum_sword',   'オリハルコンの剣','weapon','sword',0,  0, {atk:60},                {atk:.18}],

  // --- 武器: 短剣 ---
  ['dagger',             'ダガー',     'weapon','dagger', 30,  20, {atk:3,spd:2},           {spd:.05}],
  ['ninja_blade',        '忍者刀',     'weapon','dagger', 500, 30, {atk:12,spd:5},          {atk:.05,spd:.08}],

  // --- 武器: 杖 ---
  ['wooden_staff',       '木の杖',     'weapon','staff',  15,  15, {matk:3},                {}],
  ['magic_staff',        '魔法の杖',   'weapon','staff', 200,  30, {matk:10},               {matk:.08}],
  ['sage_staff',         '賢者の杖',   'weapon','staff', 700,  40, {matk:18},               {matk:.10}],
  ['spirit_staff',       '精霊の杖',   'weapon','staff',1200,  50, {matk:25,mdef:8},        {matk:.12}],
  ['demon_staff',        '魔王の杖',   'weapon','staff',   0,   0, {matk:40,mdef:12},       {matk:.15}],

  // --- 武器: 弓 ---
  ['elf_bow',            'エルフの弓', 'weapon','bow',  1200,  50, {atk:25,spd:8},          {atk:.08,spd:.08}],

  // --- 防具: 重装 ---
  ['cloth',              '布の服',     'armor','light',   10, 0, {def:2},                   {}],
  ['leather',            '皮の鎧',     'armor','light',   80, 0, {def:5},                   {def:.05}],
  ['chainmail',          '鎖帷子',     'armor','heavy',  300, 0, {def:12},                  {def:.08}],
  ['iron_armor',         '鉄の鎧',     'armor','heavy',  700, 0, {def:20},                  {def:.10}],
  ['mithril_armor',      'ミスリルの鎧','armor','heavy', 2000, 0, {def:30,mdef:10},         {def:.12}],
  ['spirit_armor',       '精霊の鎧',   'armor','heavy', 1500, 0, {def:25,mdef:15},         {def:.08,mdef:.08}],
  ['orichalcum_armor',   'オリハルコンの鎧','armor','heavy',  0, 0, {def:40,mdef:15},        {def:.15}],

  // --- 防具: ローブ ---
  ['robe',               'ローブ',     'armor','robe',    60, 0, {def:3,mdef:5},            {mdef:.05}],
  ['magic_robe',         '魔法のローブ','armor','robe',   400, 0, {def:6,mdef:12},          {mdef:.08}],
  ['elf_robe',           'エルフのローブ','armor','robe', 1200, 0, {def:15,mdef:20},        {mdef:.10}],
  ['demon_robe',         '魔王のローブ', 'armor','robe',    0, 0, {def:20,mdef:35},        {mdef:.15}],

  // --- 防具: 軽装 ---
  ['ninja_garb',         '忍び装束',   'armor','light',  350, 0, {def:8,spd:5},             {spd:.05}],

  // --- アクセサリー ---
  ['power_ring',         '力の指輪',   'accessory','power',     200, 0, {atk:5},            {atk:.05}],
  ['guard_ring',         '守りの指輪', 'accessory','guard_acc', 200, 0, {def:5},             {def:.05}],
  ['magic_amulet',       '魔力の首飾り','accessory','magic_acc', 200, 0, {matk:5},           {matk:.05}],
  ['swift_boots',        '疾風のブーツ','accessory','speed',    200, 0, {spd:5},             {spd:.05}],
  ['hp_ring',            'HP指輪',     'accessory','hp_acc',    300, 0, {hp:30},             {hp:.05}],
  ['dragon_amulet',      '竜の首飾り', 'accessory','dragon',      0, 0, {atk:3,def:3,matk:3,mdef:3,spd:3}, {atk:.05,def:.05,matk:.05,mdef:.05,spd:.05}],

  // --- 古城系装備 ---
  ['cursed_sword',       '呪われた剣', 'weapon','sword', 0, 80, {atk:35,matk:10},        {atk:.10,matk:.05}],
  ['cursed_armor',       '呪われた鎧', 'armor','heavy',  0,  0, {def:22,mdef:18},        {def:.10,mdef:.08}],

  // --- 古城深層系装備 ---
  ['phantom_blade',      '幻影の刃',   'weapon','dagger',0, 60, {atk:30,spd:10,matk:10}, {atk:.10,spd:.10}],
  ['phantom_armor',      '幻影の鎧',   'armor','light',  0,  0, {def:20,mdef:20,spd:8},  {def:.08,mdef:.08,spd:.05}],
].forEach(([id,name,slot,sub,price,dur,s,g]) => {
  EQUIPS[id] = { id, name, slot, sub, price, dur, s, g };
});

// 装備オブジェクト生成 (インベントリ用)
function createEquip(baseId, enhancement) {
  const base = EQUIPS[baseId];
  if (!base) return null;
  return {
    baseId,
    enhancement: enhancement || 0,
    durability: base.dur,
    maxDurability: base.dur,
  };
}
