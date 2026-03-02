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
  { id:'aggressive', name:'猛攻', desc:'最強スキル優先・ほぼ回復しない' },
  { id:'balanced',   name:'標準', desc:'バランスよく戦う' },
  { id:'careful',    name:'堅守', desc:'回復を優先・安全重視' },
];
const DEATH_GOLD_PENALTY = 0.15;  // 死亡時に所持金の15%を失う
const SAVE_KEY = 'onepagers-browser-rpg';
