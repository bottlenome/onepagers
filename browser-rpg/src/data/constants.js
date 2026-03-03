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
  { id:'physical', name:'力技', desc:'物理スキル優先・攻め重視' },
  { id:'magical',  name:'呪文', desc:'魔法スキル優先・攻め重視' },
  { id:'balanced', name:'万能', desc:'弱点自動判定・安全重視' },
];
const DEATH_GOLD_PENALTY = 0.15;  // 死亡時に所持金の15%を失う
const SAVE_KEY = 'onepagers-browser-rpg';
