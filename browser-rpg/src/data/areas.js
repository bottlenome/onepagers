/* ═══════════════════════════════════════
   エリア・マップ定義
   ═══════════════════════════════════════ */
const AREA_INFO = {
  grassland:         { name:'草原',       minLv:1,  maxLv:15, dungeon:false },
  mountain:          { name:'山道',       minLv:11, maxLv:20, dungeon:false },
  mine:              { name:'鉱山',       minLv:21, maxLv:30, dungeon:true  },
  lost_forest:       { name:'迷いの森',   minLv:16, maxLv:25, dungeon:false },
  demon_forest:      { name:'魔の森',     minLv:26, maxLv:30, dungeon:true  },
  wasteland:         { name:'荒野の道',   minLv:11, maxLv:25, dungeon:false },
  old_castle:        { name:'古城',       minLv:15, maxLv:25, dungeon:true  },
  old_castle_hidden: { name:'古城・深層', minLv:25, maxLv:35, dungeon:true  },
  last_dungeon:      { name:'ラストダンジョン', minLv:25, maxLv:35, dungeon:true },
};

const TOWN_INFO = {
  town1:      { name:'始まりの町', layer:1  },
  porttown:   { name:'港町',       layer:10 },
  castle:     { name:'城',         layer:15 },
  minetown:   { name:'鉱山の町',   layer:20 },
  elfvillage: { name:'エルフの里', layer:25 },
  lasttown:   { name:'最後の街',   layer:25 },
};

// フィールド→町 接続 (この階層にいると町に入れる)
const FIELD_TOWN_MAP = {
  'grassland_1':  'town1',
  'grassland_10': 'porttown',
  'grassland_15': 'castle',
  'mountain_20':  'minetown',
  'lost_forest_25': 'elfvillage',
  'wasteland_25': 'lasttown',
};

// 町の出口一覧
const TOWN_EXITS = {
  town1:      [{ area:'grassland', layer:1,  label:'草原 階層1へ' }],
  porttown:   [
    { area:'grassland', layer:11, label:'草原 階層11へ' },
    { area:'mountain',  layer:11, label:'山道 階層11へ' },
    { area:'grassland', layer:10, label:'草原 階層10へ(戻る)' },
  ],
  castle:     [
    { area:'grassland',   layer:15, label:'草原 階層15へ' },
    { area:'lost_forest', layer:16, label:'迷いの森 階層16へ' },
    { area:'wasteland',   layer:11, label:'荒野の道 階層11へ' },
  ],
  minetown:   [
    { area:'mountain', layer:19, label:'山道 階層19へ(戻る)' },
    { area:'mine',     layer:21, label:'鉱山 階層21へ' },
  ],
  elfvillage: [
    { area:'lost_forest',  layer:24, label:'迷いの森 階層24へ(戻る)' },
    { area:'demon_forest', layer:26, label:'魔の森 階層26へ' },
  ],
  lasttown:   [
    { area:'wasteland',    layer:24, label:'荒野の道 階層24へ(戻る)' },
    { area:'last_dungeon', layer:25, label:'ラストダンジョン 階層25へ' },
  ],
};

// フィールドの接続ルール (area, layer) → 移動可能な先
function getFieldExits(area, layer) {
  const info = AREA_INFO[area];
  if (!info) return [];
  const exits = [];

  // 町への入口
  const townKey = area + '_' + layer;
  if (FIELD_TOWN_MAP[townKey]) {
    const tid = FIELD_TOWN_MAP[townKey];
    exits.push({ type:'town', id:tid, label:TOWN_INFO[tid].name + 'に入る' });
  }

  // 古城入口 (荒野の道 階層15から)
  if (area === 'wasteland' && layer === 15) {
    exits.push({ type:'field', area:'old_castle', layer:15, label:'古城に入る' });
  }

  // 古城→隠し通路 (条件付き)
  if (area === 'old_castle' && layer === 25) {
    // 隠し通路は古城ボス10回撃破後に出現
    exits.push({ type:'field', area:'old_castle', layer:24, label:'古城 階層24へ戻る' });
    // 隠し通路判定は render 時に G.player を見て追加
  }

  // 前進
  if (layer < info.maxLv) {
    exits.push({ type:'field', area, layer:layer+1, label:info.name+' 階層'+(layer+1)+'へ進む' });
  }
  // 後退
  if (layer > info.minLv) {
    exits.push({ type:'field', area, layer:layer-1, label:info.name+' 階層'+(layer-1)+'へ戻る' });
  }

  // エリア端からの帰還
  if (area === 'mountain'    && layer === 11) exits.push({ type:'town', id:'porttown', label:'港町へ戻る' });
  if (area === 'mine'        && layer === 21) exits.push({ type:'town', id:'minetown', label:'鉱山の町へ戻る' });
  if (area === 'lost_forest' && layer === 16) exits.push({ type:'town', id:'castle', label:'城へ戻る' });
  if (area === 'demon_forest'&& layer === 26) exits.push({ type:'town', id:'elfvillage', label:'エルフの里へ戻る' });
  if (area === 'wasteland'   && layer === 11) exits.push({ type:'town', id:'castle', label:'城へ戻る' });
  if (area === 'old_castle'  && layer === 15) exits.push({ type:'field', area:'wasteland', layer:15, label:'荒野の道へ戻る' });
  if (area === 'old_castle_hidden' && layer === 25) exits.push({ type:'field', area:'old_castle', layer:25, label:'古城 階層25へ戻る' });
  if (area === 'last_dungeon'&& layer === 25) exits.push({ type:'town', id:'lasttown', label:'最後の街へ戻る' });

  return exits;
}

// 町の施設一覧
const TOWN_FACILITIES = {
  town1: [
    { id:'inn',      icon:'🏨', label:'宿屋',   cost:10 },
    { id:'shop',     icon:'🏪', label:'よろずや', shopId:'town1_general' },
    { id:'jobchange', icon:'🔄', label:'転職場',  advanced:false },
    { id:'status',   icon:'📊', label:'ステータス' },
  ],
  porttown: [
    { id:'inn',       icon:'🏨', label:'宿屋',       cost:30 },
    { id:'shop',      icon:'⚔️', label:'武器屋',     shopId:'port_weapon' },
    { id:'shop',      icon:'🛡️', label:'防具屋',     shopId:'port_armor' },
    { id:'shop',      icon:'🧪', label:'アイテム屋', shopId:'port_item' },
    { id:'jobchange', icon:'⬆️', label:'上級職転職場', advanced:true },
    { id:'arena',     icon:'🏟️', label:'闘技場' },
    { id:'status',    icon:'📊', label:'ステータス' },
  ],
  castle: [
    { id:'inn',       icon:'🏨', label:'宿屋',   cost:100 },
    { id:'bank',      icon:'🏦', label:'銀行' },
    { id:'warehouse', icon:'📦', label:'倉庫' },
    { id:'social_arena', icon:'🏟️', label:'闘技場(対人)', plugin:true },
    { id:'social_tavern', icon:'🍺', label:'酒場', plugin:true },
    { id:'status',    icon:'📊', label:'ステータス' },
  ],
  minetown: [
    { id:'inn',       icon:'🏨', label:'宿屋',   cost:50 },
    { id:'shop',      icon:'🏪', label:'よろずや', shopId:'mine_general' },
    { id:'blacksmith', icon:'🔨', label:'鍛冶屋' },
    { id:'status',    icon:'📊', label:'ステータス' },
  ],
  elfvillage: [
    { id:'shop',       icon:'⚔️', label:'武器屋',   shopId:'elf_weapon' },
    { id:'shop',       icon:'🛡️', label:'防具屋',   shopId:'elf_armor' },
    { id:'shop',       icon:'🧪', label:'アイテム屋', shopId:'elf_item' },
    { id:'synthesis',  icon:'⚗️', label:'合成屋' },
    { id:'enhancement', icon:'✨', label:'強化所' },
    { id:'status',     icon:'📊', label:'ステータス' },
  ],
  lasttown: [
    { id:'inn',   icon:'🏨', label:'宿屋',       cost:80 },
    { id:'shop',  icon:'⚔️', label:'武器屋',     shopId:'last_weapon' },
    { id:'shop',  icon:'🛡️', label:'防具屋',     shopId:'last_armor' },
    { id:'shop',  icon:'🧪', label:'アイテム屋', shopId:'last_item' },
    { id:'status', icon:'📊', label:'ステータス' },
  ],
};
