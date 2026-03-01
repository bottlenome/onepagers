/* ═══════════════════════════════════════
   アイテムデータ
   type: consumable / material
   healHp/healMp: 回復量 (0=なし, -1=全回復)
   ═══════════════════════════════════════ */
const ITEMS = {};
[
  // id              name            type          price  healHp healMp  desc
  ['herb',          '薬草',         'consumable',  10,    30,    0,   'HPを30回復'],
  ['hi_herb',       '上薬草',       'consumable',  50,   100,    0,   'HPを100回復'],
  ['elixir',        '万能薬',       'consumable', 500,    -1,   -1,   'HP・MP全回復'],
  ['magic_water',   '魔法の水',     'consumable',  20,     0,   30,   'MPを30回復'],
  ['antidote',      '毒消し',       'consumable',   8,     0,    0,   '毒を治療'],
  ['tent',          'テント',       'consumable', 100,    -1,   -1,   'HP・MP全回復(フィールド用)'],
  ['world_branch',  '世界樹の枝',   'consumable', 300,    -1,   -1,   'HP・MP全回復+状態治療'],
  // --- 素材 ---
  ['copper_ore',    '銅鉱石',       'material',    15,     0,    0,   '鍛冶の素材'],
  ['iron_ore',      '鉄鉱石',       'material',    40,     0,    0,   '鍛冶の素材'],
  ['mithril_ore',   'ミスリル鉱石', 'material',   150,     0,    0,   '鍛冶の素材'],
  ['dragon_scale',  '竜鱗',         'material',   500,     0,    0,   '伝説の素材'],
  ['spirit_stone',  '精霊石',       'material',   200,     0,    0,   '合成の素材'],
  ['dark_crystal',  '闇の結晶',     'material',   300,     0,    0,   '高位合成の素材'],
].forEach(([id,name,type,price,healHp,healMp,desc]) => {
  ITEMS[id] = { id, name, type, price, healHp, healMp, desc };
});
