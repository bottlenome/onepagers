/* ═══════════════════════════════════════
   闘技場データ (港町NPC戦)
   ═══════════════════════════════════════ */
const ARENA_ENTRY_FEE = 100;
const ARENA_OPPONENTS = [
  { name:'見習い剣士',   emoji:'🗡️', level:15 },
  { name:'魔法戦士',     emoji:'🔮', level:18 },
  { name:'熟練の騎士',   emoji:'🛡️', level:21 },
  { name:'闘士',         emoji:'💪', level:24 },
  { name:'剣聖',         emoji:'⚔️', level:27 },
  { name:'闘技場王',     emoji:'👑', level:30 },
];

// 闘技場モンスター生成
function createArenaOpponent(index) {
  const opp = ARENA_OPPONENTS[index];
  if (!opp) return null;
  const stats = calcMonsterStats(opp.level);
  // 闘技場の相手は少し強め
  return {
    name: opp.name,
    emoji: opp.emoji,
    level: opp.level,
    hp: Math.floor(stats.hp * 1.3),
    maxHp: Math.floor(stats.hp * 1.3),
    atk: Math.floor(stats.atk * 1.2),
    def: Math.floor(stats.def * 1.2),
    matk: Math.floor(stats.matk * 1.2),
    mdef: Math.floor(stats.mdef * 1.2),
    spd: stats.spd,
    boss: false,
    special: null,
    drops: [],
    arena: true,
  };
}
