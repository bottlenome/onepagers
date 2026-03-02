/* ═══════════════════════════════════════
   モンスターデータ
   area: 出現エリアID
   minLv/maxLv: 出現レベル範囲
   special: 特殊攻撃スキルID (null=なし)
   drops: [{id, rate}] 追加ドロップ
   ═══════════════════════════════════════ */
const MONSTER_POOL = [
  // --- 草原 (grassland) 1-15 ---
  { name:'スライム',     emoji:'🟢', area:'grassland', minLv:1,  maxLv:3,  special:null, drops:[] },
  { name:'コボルト',     emoji:'👹', area:'grassland', minLv:1,  maxLv:4,  special:null, drops:[] },
  { name:'大カブト',     emoji:'🪲', area:'grassland', minLv:2,  maxLv:5,  special:null, drops:[] },
  { name:'狼',           emoji:'🐺', area:'grassland', minLv:3,  maxLv:6,  special:null, drops:[] },
  { name:'オーク',       emoji:'👺', area:'grassland', minLv:5,  maxLv:9,  special:null, drops:[] },
  { name:'ゴブリン',     emoji:'👾', area:'grassland', minLv:5,  maxLv:8,  special:null, drops:[] },
  { name:'大蛇',         emoji:'🐍', area:'grassland', minLv:7,  maxLv:11, special:null, drops:[] },
  { name:'バンディット', emoji:'🗡️', area:'grassland', minLv:8,  maxLv:12, special:null, drops:[] },
  { name:'リザードマン', emoji:'🦎', area:'grassland', minLv:10, maxLv:13, special:null, drops:[] },
  { name:'ハーピー',     emoji:'🦅', area:'grassland', minLv:11, maxLv:14, special:null, drops:[] },
  { name:'トロール',     emoji:'🧌', area:'grassland', minLv:13, maxLv:15, special:null, drops:[] },
  { name:'グリフォン',   emoji:'🦁', area:'grassland', minLv:14, maxLv:15, special:null, drops:[] },

  // --- 山道 (mountain) 11-20 ---
  { name:'ロックゴーレム', emoji:'🪨', area:'mountain', minLv:11, maxLv:15, special:null, drops:[] },
  { name:'コカトリス',     emoji:'🐓', area:'mountain', minLv:11, maxLv:14, special:null, drops:[] },
  { name:'ガーゴイル',     emoji:'🗿', area:'mountain', minLv:12, maxLv:16, special:null, drops:[] },
  { name:'ワイバーン',     emoji:'🐉', area:'mountain', minLv:14, maxLv:18, special:null, drops:[] },
  { name:'マンティコア',   emoji:'🦂', area:'mountain', minLv:16, maxLv:20, special:null, drops:[] },
  { name:'山賊頭',         emoji:'⚔️', area:'mountain', minLv:17, maxLv:20, special:null, drops:[] },

  // --- 鉱山 (mine) 21-30 ダンジョン ---
  { name:'スケルトン',     emoji:'💀', area:'mine', minLv:21, maxLv:24, special:null, drops:[{id:'copper_ore',rate:.30}] },
  { name:'ダークナイト',   emoji:'🖤', area:'mine', minLv:21, maxLv:25, special:null, drops:[{id:'iron_ore',rate:.25}] },
  { name:'ミミック',       emoji:'📦', area:'mine', minLv:22, maxLv:26, special:null, drops:[{id:'iron_ore',rate:.30}] },
  { name:'デーモン',       emoji:'😈', area:'mine', minLv:24, maxLv:28, special:null, drops:[{id:'mithril_ore',rate:.12}] },
  { name:'ケルベロス',     emoji:'🐕', area:'mine', minLv:25, maxLv:29, special:null, drops:[{id:'mithril_ore',rate:.15}] },
  { name:'ドラゴンゾンビ', emoji:'🦴', area:'mine', minLv:27, maxLv:29, special:null, drops:[{id:'mithril_ore',rate:.20}] },

  // --- 迷いの森 (lost_forest) 16-25 ---
  { name:'トレント',       emoji:'🌳', area:'lost_forest', minLv:16, maxLv:19, special:null, drops:[{id:'world_branch',rate:.05}] },
  { name:'フェアリー',     emoji:'🧚', area:'lost_forest', minLv:17, maxLv:20, special:null, drops:[{id:'spirit_stone',rate:.08}] },
  { name:'ダークエルフ',   emoji:'🧝', area:'lost_forest', minLv:18, maxLv:22, special:null, drops:[] },
  { name:'ユニコーン',     emoji:'🦄', area:'lost_forest', minLv:20, maxLv:23, special:null, drops:[{id:'spirit_stone',rate:.10}] },
  { name:'オーガ',         emoji:'👹', area:'lost_forest', minLv:22, maxLv:25, special:null, drops:[] },
  { name:'キメラ',         emoji:'🐲', area:'lost_forest', minLv:23, maxLv:25, special:null, drops:[] },

  // --- 魔の森 (demon_forest) 26-30 ダンジョン ---
  { name:'デーモンロード', emoji:'😈', area:'demon_forest', minLv:26, maxLv:28, special:null, drops:[{id:'dark_crystal',rate:.15}] },
  { name:'ヴァンパイア',   emoji:'🧛', area:'demon_forest', minLv:27, maxLv:29, special:null, drops:[{id:'dark_crystal',rate:.15}] },
  { name:'リッチ',         emoji:'☠️', area:'demon_forest', minLv:28, maxLv:30, special:null, drops:[{id:'dark_crystal',rate:.20}] },
  { name:'ダークドラゴン', emoji:'🐉', area:'demon_forest', minLv:29, maxLv:30, special:'fireball', drops:[] },
  { name:'堕天使',         emoji:'👼', area:'demon_forest', minLv:28, maxLv:30, special:null, drops:[{id:'spirit_stone',rate:.15}] },

  // --- 荒野の道 (wasteland) 11-25 ---
  { name:'サンドワーム',   emoji:'🪱', area:'wasteland', minLv:11, maxLv:15, special:null, drops:[] },
  { name:'スコーピオン',   emoji:'🦂', area:'wasteland', minLv:12, maxLv:16, special:null, drops:[] },
  { name:'デスクロウ',     emoji:'🦅', area:'wasteland', minLv:14, maxLv:18, special:null, drops:[] },
  { name:'サンドゴーレム', emoji:'🏜️', area:'wasteland', minLv:16, maxLv:20, special:null, drops:[] },
  { name:'バジリスク',     emoji:'🐍', area:'wasteland', minLv:18, maxLv:22, special:null, drops:[] },
  { name:'デスナイト',     emoji:'⚔️', area:'wasteland', minLv:20, maxLv:25, special:null, drops:[] },
  { name:'サンドドラゴン', emoji:'🐉', area:'wasteland', minLv:22, maxLv:25, special:'fireball', drops:[] },

  // --- 古城 (old_castle) 21-25 ダンジョン ---
  { name:'リビングアーマー', emoji:'🛡️', area:'old_castle', minLv:21, maxLv:23, special:null, drops:[{id:'iron_ore',rate:.20}] },
  { name:'ゴースト',         emoji:'👻', area:'old_castle', minLv:21, maxLv:23, special:null, drops:[] },
  { name:'デュラハン',       emoji:'🗡️', area:'old_castle', minLv:22, maxLv:24, special:null, drops:[] },
  { name:'ヴァンパイアロード',emoji:'🧛', area:'old_castle', minLv:23, maxLv:25, special:null, drops:[{id:'dark_crystal',rate:.10}] },
  { name:'死霊術師',         emoji:'☠️', area:'old_castle', minLv:24, maxLv:25, special:'blizzard', drops:[] },

  // --- 古城・隠し (old_castle_hidden) 25-35 ---
  { name:'ファントム',     emoji:'👻', area:'old_castle_hidden', minLv:25, maxLv:28, special:null, drops:[] },
  { name:'デスロード',     emoji:'💀', area:'old_castle_hidden', minLv:27, maxLv:30, special:null, drops:[{id:'dark_crystal',rate:.20}] },
  { name:'エンシェントナイト',emoji:'🗡️', area:'old_castle_hidden', minLv:29, maxLv:32, special:'power_strike', drops:[] },
  { name:'伝説の魔術師',   emoji:'🧙', area:'old_castle_hidden', minLv:30, maxLv:34, special:'meteor', drops:[] },
  { name:'堕落の騎士',     emoji:'🖤', area:'old_castle_hidden', minLv:32, maxLv:35, special:'devastating_blow', drops:[] },

  // --- ラストダンジョン (last_dungeon) 25-35 ---
  { name:'カオスナイト',   emoji:'⚔️', area:'last_dungeon', minLv:25, maxLv:28, special:null, drops:[] },
  { name:'ベヒーモス',     emoji:'🦏', area:'last_dungeon', minLv:27, maxLv:30, special:null, drops:[] },
  { name:'キングケルベロス',emoji:'🐕', area:'last_dungeon', minLv:28, maxLv:31, special:null, drops:[] },
  { name:'アークデーモン',  emoji:'😈', area:'last_dungeon', minLv:30, maxLv:33, special:'thunder', drops:[{id:'dark_crystal',rate:.25}] },
  { name:'混沌竜',         emoji:'🐉', area:'last_dungeon', minLv:32, maxLv:35, special:'fireball', drops:[{id:'dragon_scale',rate:.10}] },
];

// ボスデータ (通常の計算式ではなく固定ステータス)
const BOSSES = {
  mine_30: {
    name:'ドラゴン', emoji:'🐲', level:30, boss:true,
    hp:500, maxHp:500, atk:100, def:60, matk:80, mdef:50, spd:40,
    special:'fireball', drops:[{id:'dragon_scale',rate:1.0}],
    title:'ドラゴンスレイヤー',
  },
  demon_forest_30: {
    name:'堕ちたエルフ王', emoji:'👑', level:30, boss:true,
    hp:600, maxHp:600, atk:90, def:70, matk:110, mdef:80, spd:55,
    special:'holy', drops:[{id:'spirit_stone',rate:1.0},{id:'dark_crystal',rate:1.0}],
    title:'エルフの救世主',
  },
  old_castle_25: {
    name:'古城の主', emoji:'🏰', level:25, boss:true,
    hp:400, maxHp:400, atk:80, def:55, matk:70, mdef:50, spd:35,
    special:'power_strike', drops:[{id:'dark_crystal',rate:1.0}],
    title:'古城の解放者',
    defeatKey:'old_castle_boss_defeats',
  },
  old_castle_hidden_35: {
    name:'伝説のプレイヤーたち', emoji:'⚔️', level:35, boss:true,
    hp:900, maxHp:900, atk:130, def:90, matk:120, mdef:85, spd:65,
    special:'sacred_blade', drops:[],
    title:'真の勇者',
  },
  last_dungeon_35: {
    name:'魔神', emoji:'👿', level:35, boss:true,
    hp:1000, maxHp:1000, atk:140, def:100, matk:140, mdef:100, spd:60,
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
