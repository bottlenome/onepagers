/* ═══════════════════════════════════════
   定数
   ═══════════════════════════════════════ */
const STAT_KEYS = ['hp','mp','atk','def','matk','mdef','spd'];
const STAT_NAMES = { hp:'HP', mp:'MP', atk:'攻撃', def:'防御', matk:'魔攻', mdef:'魔防', spd:'速さ' };
const INIT_STATS = { hp:35, mp:10, atk:5, def:5, matk:5, mdef:5, spd:5 };
const MAX_LEVEL = 30;
const MAX_ENHANCE = 10;
const ENHANCE_BONUS = { weapon:2, armor:2 }; // +N per enhancement level
const ENHANCE_RATES = [0.90, 0.80, 0.70, 0.55, 0.40, 0.30, 0.20, 0.15, 0.10, 0.05];
const CARRY_RATIO_BASIC = 0.5;    // 下級職転職時の引き継ぎ率
const INVENTORY_MAX = 30;
const STRATEGIES = [
  { id:'aggressive', name:'猛攻', desc:'物理スキル+30%・回復控えめ' },
  { id:'balanced',   name:'標準', desc:'ボーナスなし・安全重視' },
  { id:'careful',    name:'堅守', desc:'魔法スキル+30%・回復控えめ' },
];
const DEATH_GOLD_PENALTY = 0.15;  // 死亡時に所持金の15%を失う
const SAVE_KEY = 'onepagers-browser-rpg';

// --- 共鳴システム ---
// 装備サブタイプ → 共鳴タイプ
const RESONANCE_TYPE_MAP = {
  sword:'fury', dagger:'chain', staff:'surge', bow:'chain',
  heavy:'counter', light:'chain', robe:'surge',
};
const RESONANCE_INFO = {
  fury:    { name:'猛る刃',     turns:3, strat:'aggressive', desc:'猛攻を維持すると武器が共鳴する' },
  surge:   { name:'魔力の奔流', turns:3, strat:'careful',    desc:'堅守を維持すると魔力が共鳴する' },
  counter: { name:'反撃の構え', hits:2,  strat:'careful',    desc:'堅守で耐え猛攻に切替えると反撃する' },
  chain:   { name:'一閃の連鎖', desc:'会心の一撃で追加攻撃が発生する' },
};
const RESONANCE_ENHANCE_BONUS = 0.02; // 強化+1ごとの共鳴率加算
const RESONANCE_DROP_BONUS = 0.15;    // 共鳴発動時のドロップ率加算
const RESONANCE_CHAIN_DROP_BONUS = 0.10;
// エリア別 共鳴限定ドロップ
const RESONANCE_AREA_DROPS = {
  grassland:    { id:'shining_scale',   rate:0.30 },
  mountain:     { id:'gleaming_ore',    rate:0.25 },
  mine:         { id:'gleaming_ore',    rate:0.30 },
  lost_forest:  { id:'spirit_drop',     rate:0.25 },
  demon_forest: { id:'spirit_drop',     rate:0.30 },
  wasteland:    { id:'shining_scale',   rate:0.25 },
  old_castle:   { id:'grudge_shard',    rate:0.25 },
  old_castle_hidden: { id:'grudge_shard', rate:0.30 },
  last_dungeon: { id:'spirit_drop',     rate:0.25 },
};
