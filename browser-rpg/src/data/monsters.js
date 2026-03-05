/* ═══════════════════════════════════════
   モンスターデータ
   area: 出現エリアID
   minLv/maxLv: 出現レベル範囲
   special: 特殊攻撃スキルID (null=なし)
   drops: [{id, rate}] 追加ドロップ
   resist: 'p'=物理耐性(高DEF/低MDEF→呪文有効), 'm'=魔法耐性(高MDEF/低DEF→力技有効), 省略=均等
   ═══════════════════════════════════════ */
const MONSTER_POOL = [
  // --- 草原 (grassland) 1-15 ---
  { name:'スライム',     emoji:'🟢', area:'grassland', minLv:1,  maxLv:3,  special:null, drops:[] },
  { name:'コボルト',     emoji:'👹', area:'grassland', minLv:1,  maxLv:4,  special:null, drops:[], resist:'p' },
  { name:'大カブト',     emoji:'🪲', area:'grassland', minLv:2,  maxLv:5,  special:null, drops:[], resist:'p' },
  { name:'狼',           emoji:'🐺', area:'grassland', minLv:3,  maxLv:6,  special:null, drops:[] },
  { name:'オーク',       emoji:'👺', area:'grassland', minLv:5,  maxLv:9,  special:null, drops:[], resist:'p' },
  { name:'ゴブリン',     emoji:'👾', area:'grassland', minLv:5,  maxLv:8,  special:null, drops:[], resist:'m' },
  { name:'大蛇',         emoji:'🐍', area:'grassland', minLv:7,  maxLv:11, special:null, drops:[], resist:'m' },
  { name:'バンディット', emoji:'🗡️', area:'grassland', minLv:8,  maxLv:12, special:null, drops:[] },
  { name:'リザードマン', emoji:'🦎', area:'grassland', minLv:10, maxLv:13, special:null, drops:[], resist:'p' },
  { name:'ハーピー',     emoji:'🦅', area:'grassland', minLv:11, maxLv:14, special:null, drops:[], resist:'m' },
  { name:'トロール',     emoji:'🧌', area:'grassland', minLv:13, maxLv:15, special:null, drops:[], resist:'p' },
  { name:'グリフォン',   emoji:'🦁', area:'grassland', minLv:14, maxLv:15, special:null, drops:[] },

  // --- 山道 (mountain) 11-20 ---
  { name:'ロックゴーレム', emoji:'🪨', area:'mountain', minLv:11, maxLv:15, special:null, drops:[], resist:'p' },
  { name:'コカトリス',     emoji:'🐓', area:'mountain', minLv:11, maxLv:14, special:null, drops:[], resist:'m' },
  { name:'ガーゴイル',     emoji:'🗿', area:'mountain', minLv:12, maxLv:16, special:null, drops:[], resist:'p' },
  { name:'ワイバーン',     emoji:'🐉', area:'mountain', minLv:14, maxLv:18, special:null, drops:[] },
  { name:'マンティコア',   emoji:'🦂', area:'mountain', minLv:16, maxLv:20, special:null, drops:[], resist:'m' },
  { name:'山賊頭',         emoji:'⚔️', area:'mountain', minLv:17, maxLv:20, special:null, drops:[], resist:'p' },

  // --- 鉱山 (mine) 21-30 ダンジョン ---
  { name:'スケルトン',     emoji:'💀', area:'mine', minLv:21, maxLv:24, special:null, drops:[{id:'copper_ore',rate:.30}], resist:'m' },
  { name:'ダークナイト',   emoji:'🖤', area:'mine', minLv:21, maxLv:25, special:null, drops:[{id:'iron_ore',rate:.25}], resist:'p' },
  { name:'ミミック',       emoji:'📦', area:'mine', minLv:22, maxLv:26, special:null, drops:[{id:'iron_ore',rate:.30}], resist:'p' },
  { name:'デーモン',       emoji:'😈', area:'mine', minLv:24, maxLv:28, special:null, drops:[{id:'mithril_ore',rate:.12}], resist:'m' },
  { name:'ケルベロス',     emoji:'🐕', area:'mine', minLv:25, maxLv:29, special:null, drops:[{id:'mithril_ore',rate:.15}] },
  { name:'ドラゴンゾンビ', emoji:'🦴', area:'mine', minLv:27, maxLv:29, special:null, drops:[{id:'mithril_ore',rate:.20}] },

  // --- 迷いの森 (lost_forest) 16-25 ---
  { name:'トレント',       emoji:'🌳', area:'lost_forest', minLv:16, maxLv:19, special:null, drops:[{id:'world_branch',rate:.05}], resist:'p' },
  { name:'フェアリー',     emoji:'🧚', area:'lost_forest', minLv:17, maxLv:20, special:null, drops:[{id:'spirit_stone',rate:.08}], resist:'m' },
  { name:'ダークエルフ',   emoji:'🧝', area:'lost_forest', minLv:18, maxLv:22, special:null, drops:[], resist:'m' },
  { name:'ユニコーン',     emoji:'🦄', area:'lost_forest', minLv:20, maxLv:23, special:null, drops:[{id:'spirit_stone',rate:.10}], resist:'m' },
  { name:'オーガ',         emoji:'👹', area:'lost_forest', minLv:22, maxLv:25, special:null, drops:[], resist:'p' },
  { name:'キメラ',         emoji:'🐲', area:'lost_forest', minLv:23, maxLv:25, special:null, drops:[] },

  // --- 魔の森 (demon_forest) 26-30 ダンジョン ---
  { name:'デーモンロード', emoji:'😈', area:'demon_forest', minLv:26, maxLv:28, special:null, drops:[{id:'dark_crystal',rate:.15}] },
  { name:'ヴァンパイア',   emoji:'🧛', area:'demon_forest', minLv:27, maxLv:29, special:null, drops:[{id:'dark_crystal',rate:.15},{id:'spirit_stone',rate:.08}], resist:'m' },
  { name:'リッチ',         emoji:'☠️', area:'demon_forest', minLv:28, maxLv:30, special:null, drops:[{id:'dark_crystal',rate:.20},{id:'spirit_stone',rate:.10}], resist:'m' },
  { name:'ダークドラゴン', emoji:'🐉', area:'demon_forest', minLv:29, maxLv:30, special:'fireball', drops:[{id:'dark_crystal',rate:.15}], resist:'p' },
  { name:'堕天使',         emoji:'👼', area:'demon_forest', minLv:28, maxLv:30, special:null, drops:[{id:'spirit_stone',rate:.15},{id:'dark_crystal',rate:.10}], resist:'m' },

  // --- 荒野の道 (wasteland) 11-25 ---
  { name:'サンドワーム',   emoji:'🪱', area:'wasteland', minLv:11, maxLv:15, special:null, drops:[] },
  { name:'スコーピオン',   emoji:'🦂', area:'wasteland', minLv:12, maxLv:16, special:null, drops:[] },
  { name:'デスクロウ',     emoji:'🦅', area:'wasteland', minLv:14, maxLv:18, special:null, drops:[], resist:'m' },
  { name:'サンドゴーレム', emoji:'🏜️', area:'wasteland', minLv:16, maxLv:20, special:null, drops:[], resist:'p' },
  { name:'バジリスク',     emoji:'🐍', area:'wasteland', minLv:18, maxLv:22, special:null, drops:[], resist:'m' },
  { name:'デスナイト',     emoji:'⚔️', area:'wasteland', minLv:20, maxLv:25, special:null, drops:[], resist:'p' },
  { name:'サンドドラゴン', emoji:'🐉', area:'wasteland', minLv:22, maxLv:25, special:'fireball', drops:[] },

  // --- 古城 (old_castle) 21-25 ダンジョン ---
  { name:'リビングアーマー', emoji:'🛡️', area:'old_castle', minLv:21, maxLv:23, special:null, drops:[{id:'iron_ore',rate:.20},{id:'cursed_bone',rate:.08}], resist:'p' },
  { name:'ゴースト',         emoji:'👻', area:'old_castle', minLv:21, maxLv:23, special:null, drops:[{id:'cursed_bone',rate:.10}], resist:'m' },
  { name:'デュラハン',       emoji:'🗡️', area:'old_castle', minLv:22, maxLv:24, special:null, drops:[{id:'cursed_bone',rate:.12}], resist:'p' },
  { name:'ヴァンパイアロード',emoji:'🧛', area:'old_castle', minLv:23, maxLv:25, special:null, drops:[{id:'dark_crystal',rate:.10},{id:'cursed_bone',rate:.10}], resist:'m' },
  { name:'死霊術師',         emoji:'☠️', area:'old_castle', minLv:24, maxLv:25, special:'blizzard', drops:[{id:'cursed_bone',rate:.15}], resist:'m' },

  // --- 古城・隠し (old_castle_hidden) 25-35 ---
  { name:'ファントム',     emoji:'👻', area:'old_castle_hidden', minLv:25, maxLv:28, special:null, drops:[{id:'phantom_cloth',rate:.10}], resist:'m' },
  { name:'デスロード',     emoji:'💀', area:'old_castle_hidden', minLv:27, maxLv:30, special:null, drops:[{id:'dark_crystal',rate:.20},{id:'phantom_cloth',rate:.08}], resist:'m' },
  { name:'エンシェントナイト',emoji:'🗡️', area:'old_castle_hidden', minLv:29, maxLv:32, special:'power_strike', drops:[{id:'phantom_cloth',rate:.12}], resist:'p' },
  { name:'伝説の魔術師',   emoji:'🧙', area:'old_castle_hidden', minLv:30, maxLv:34, special:'meteor', drops:[{id:'phantom_cloth',rate:.15},{id:'spirit_stone',rate:.10}], resist:'m' },
  { name:'堕落の騎士',     emoji:'🖤', area:'old_castle_hidden', minLv:32, maxLv:35, special:'devastating_blow', drops:[{id:'phantom_cloth',rate:.12},{id:'dark_crystal',rate:.15}], resist:'p' },

  // --- ラストダンジョン (last_dungeon) 25-35 ---
  { name:'カオスナイト',   emoji:'⚔️', area:'last_dungeon', minLv:25, maxLv:28, special:null, drops:[{id:'orichalcum',rate:.05}], resist:'p' },
  { name:'ベヒーモス',     emoji:'🦏', area:'last_dungeon', minLv:27, maxLv:30, special:null, drops:[{id:'orichalcum',rate:.06}], resist:'p' },
  { name:'キングケルベロス',emoji:'🐕', area:'last_dungeon', minLv:28, maxLv:31, special:null, drops:[{id:'orichalcum',rate:.08}] },
  { name:'アークデーモン',  emoji:'😈', area:'last_dungeon', minLv:30, maxLv:33, special:'thunder', drops:[{id:'dark_crystal',rate:.25},{id:'orichalcum',rate:.10}], resist:'m' },
  { name:'混沌竜',         emoji:'🐉', area:'last_dungeon', minLv:32, maxLv:35, special:'fireball', drops:[{id:'dragon_scale',rate:.10},{id:'orichalcum',rate:.12}] },
];

// ボスデータ (通常の計算式ではなく固定ステータス)
// 難易度設計: 引き継ぎ率50%での転職ループ回数基準
const BOSSES = {
  // 2ループでやっと倒せる (戦士→騎士 + 伝説の剣 + ミスリル鎧)
  mine_30: {
    name:'ドラゴン', emoji:'🐲', level:30, boss:true,
    hp:2000, maxHp:2000, atk:150, def:90, matk:80, mdef:70, spd:50,
    special:'fireball', drops:[{id:'dragon_scale',rate:1.0}],
    title:'ドラゴンスレイヤー',
  },
  // 4ループ・魔防+攻撃特化でやっと倒せる (ブリザードが脅威、物理は弱い)
  demon_forest_30: {
    name:'堕ちたエルフ王', emoji:'👑', level:30, boss:true,
    hp:4000, maxHp:4000, atk:80, def:70, matk:180, mdef:170, spd:65,
    special:'blizzard', specialRate:0.45, drops:[{id:'spirit_stone',rate:1.0},{id:'dark_crystal',rate:1.0}],
    title:'エルフの救世主',
  },
  // 4ループ・魔攻+防御特化でやっと倒せる (物理が脅威、高DEFで物理攻撃が通りにくい)
  old_castle_25: {
    name:'古城の主', emoji:'🏰', level:25, boss:true,
    hp:3000, maxHp:3000, atk:170, def:160, matk:60, mdef:80, spd:50,
    special:'power_strike', drops:[{id:'dark_crystal',rate:1.0}],
    title:'古城の解放者',
    defeatKey:'old_castle_boss_defeats',
  },
  // 20ループ+装備+5でやっと倒せる (全能力が高い超強敵)
  old_castle_hidden_35: {
    name:'伝説のプレイヤーたち', emoji:'⚔️', level:35, boss:true,
    hp:6000, maxHp:6000, atk:180, def:120, matk:100, mdef:200, spd:90,
    special:'sacred_blade', drops:[],
    title:'真の勇者',
  },
  // 10ループ・HP+魔防+防御特化でやっと倒せる (メテオが超強力)
  last_dungeon_35: {
    name:'魔神', emoji:'👿', level:35, boss:true,
    hp:5000, maxHp:5000, atk:200, def:120, matk:80, mdef:140, spd:75,
    special:'meteor', drops:[],
    title:'世界の救世主',
  },
};

// 通常モンスターのステータス計算
function calcMonsterStats(level) {
  return {
    hp: level * 10 + 10,
    maxHp: level * 10 + 10,
    atk: Math.floor(level * 3 + 2),
    def: level * 2,
    matk: level * 2,
    mdef: level * 2,
    spd: level * 2 + 2,
  };
}

// モンスター生成
function spawnMonster(areaId, layer) {
  // ボスチェック
  const bossKey = areaId + '_' + layer;
  if (BOSSES[bossKey]) return { ...BOSSES[bossKey] };

  const pool = MONSTER_POOL.filter(m => m.area === areaId && m.minLv <= layer && m.maxLv >= layer);
  if (pool.length === 0) {
    // フォールバック: 最も近いモンスターを使う
    const all = MONSTER_POOL.filter(m => m.area === areaId);
    if (all.length === 0) return null;
    pool.push(all[Math.floor(Math.random() * all.length)]);
  }
  const tmpl = pool[Math.floor(Math.random() * pool.length)];
  const stats = calcMonsterStats(layer);
  // 耐性補正: p=物理耐性(呪文有効), m=魔法耐性(力技有効)
  if (tmpl.resist === 'p') { stats.def = Math.floor(stats.def * 1.4); stats.mdef = Math.floor(stats.mdef * 0.7); }
  if (tmpl.resist === 'm') { stats.mdef = Math.floor(stats.mdef * 1.4); stats.def = Math.floor(stats.def * 0.7); }
  return {
    name: tmpl.name,
    emoji: tmpl.emoji,
    level: layer,
    ...stats,
    boss: false,
    special: tmpl.special,
    drops: tmpl.drops || [],
  };
}
