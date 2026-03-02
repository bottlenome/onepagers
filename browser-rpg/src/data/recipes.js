/* ═══════════════════════════════════════
   レシピデータ
   ═══════════════════════════════════════ */

// 合成レシピ (エルフの里)
// inputs: [itemId, itemId] 消費される。失敗時も消費
// output: { id, isEquip } 成功時に獲得
// rate: 成功率
const SYNTH_RECIPES = [
  { inputs:['herb','herb'],             output:{id:'hi_herb',isEquip:false},      rate:0.80, desc:'薬草×2 → 上薬草' },
  { inputs:['hi_herb','magic_water'],   output:{id:'elixir',isEquip:false},       rate:0.65, desc:'上薬草+魔法の水 → 万能薬' },
  { inputs:['spirit_stone','magic_water'], output:{id:'world_branch',isEquip:false}, rate:0.70, desc:'精霊石+魔法の水 → 世界樹の枝' },
  { inputs:['power_ring','magic_amulet'], output:{id:'dragon_amulet',isEquip:true}, rate:0.40, desc:'力の指輪+魔力の首飾り → 竜の首飾り' },
  { inputs:['dark_crystal','spirit_stone'], output:{id:'legendary_sword',isEquip:true}, rate:0.30, desc:'闇の結晶+精霊石 → 伝説の剣' },
  { inputs:['dark_crystal','dark_crystal'], output:{id:'dragon_amulet',isEquip:true}, rate:0.35, desc:'闇の結晶×2 → 竜の首飾り' },
  // 魔の森素材で魔術師系装備
  { inputs:['dark_crystal','spirit_stone'], output:{id:'demon_staff',isEquip:true}, rate:0.25, desc:'闇の結晶+精霊石 → 魔王の杖' },
  { inputs:['spirit_stone','spirit_stone'], output:{id:'demon_robe',isEquip:true}, rate:0.25, desc:'精霊石×2 → 魔王のローブ' },
];

// 鍛冶レシピ (鉱山の町)
// inputs: [{id, count}] 素材消費。失敗時も消費
// output: 装備ID
// fee: ゴールド手数料
const SMITH_RECIPES = [
  { inputs:[{id:'copper_ore',count:2}],                      output:'copper_sword',  rate:0.90, fee:20,   desc:'銅鉱石×2 → 銅の剣' },
  { inputs:[{id:'copper_ore',count:3}],                      output:'chainmail',     rate:0.85, fee:40,   desc:'銅鉱石×3 → 鎖帷子' },
  { inputs:[{id:'iron_ore',count:2}],                        output:'iron_sword',    rate:0.85, fee:80,   desc:'鉄鉱石×2 → 鉄の剣' },
  { inputs:[{id:'iron_ore',count:3}],                        output:'iron_armor',    rate:0.80, fee:150,  desc:'鉄鉱石×3 → 鉄の鎧' },
  { inputs:[{id:'iron_ore',count:2},{id:'copper_ore',count:1}], output:'steel_sword', rate:0.80, fee:150, desc:'鉄鉱石×2+銅鉱石 → 鋼の剣' },
  { inputs:[{id:'mithril_ore',count:2}],                     output:'mithril_sword', rate:0.70, fee:300,  desc:'ミスリル鉱石×2 → ミスリルの剣' },
  { inputs:[{id:'mithril_ore',count:3}],                     output:'mithril_armor', rate:0.65, fee:500,  desc:'ミスリル鉱石×3 → ミスリルの鎧' },
  { inputs:[{id:'dragon_scale',count:1},{id:'mithril_ore',count:2}], output:'legendary_sword', rate:0.40, fee:1000, desc:'竜鱗+ミスリル鉱石×2 → 伝説の剣' },
  // オリハルコン装備 (ラストダンジョン素材)
  { inputs:[{id:'orichalcum',count:2},{id:'dragon_scale',count:1}], output:'orichalcum_sword', rate:0.35, fee:2000, desc:'オリハルコン×2+竜鱗 → オリハルコンの剣' },
  { inputs:[{id:'orichalcum',count:3}],                             output:'orichalcum_armor', rate:0.30, fee:3000, desc:'オリハルコン×3 → オリハルコンの鎧' },
  // 古城装備 (古城素材)
  { inputs:[{id:'cursed_bone',count:3}],                             output:'cursed_sword',     rate:0.60, fee:400,  desc:'呪われた骨×3 → 呪われた剣' },
  { inputs:[{id:'cursed_bone',count:4}],                             output:'cursed_armor',     rate:0.55, fee:600,  desc:'呪われた骨×4 → 呪われた鎧' },
  // 古城深層装備 (古城深層素材)
  { inputs:[{id:'phantom_cloth',count:3},{id:'dark_crystal',count:1}], output:'phantom_blade',  rate:0.40, fee:1500, desc:'幻影の布×3+闇の結晶 → 幻影の刃' },
  { inputs:[{id:'phantom_cloth',count:4}],                            output:'phantom_armor',   rate:0.35, fee:2000, desc:'幻影の布×4 → 幻影の鎧' },
];
