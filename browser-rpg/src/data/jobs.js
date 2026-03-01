/* ═══════════════════════════════════════
   職業データ
   base: レベルアップ時の確定成長値
   rate: レベルアップ時のボーナス+1確率 (隠しパラメータ)
   skills: 上級職のみ [{lv, id}]
   ═══════════════════════════════════════ */
const JOBS = {
  warrior: {
    name:'戦士', type:'basic',
    desc:'高いHPと攻撃力を持つ前衛職',
    base:{ hp:5, mp:0, atk:2, def:2, matk:0, mdef:0, spd:1 },
    rate:{ hp:.80, mp:.20, atk:.50, def:.50, matk:.10, mdef:.15, spd:.30 },
  },
  mage: {
    name:'魔法使い', type:'basic',
    desc:'強力な魔法で攻撃する後衛職',
    base:{ hp:3, mp:3, atk:0, def:0, matk:2, mdef:2, spd:0 },
    rate:{ hp:.40, mp:.80, atk:.10, def:.15, matk:.70, mdef:.60, spd:.25 },
  },
  priest: {
    name:'僧侶', type:'basic',
    desc:'回復魔法を使えるバランス型',
    base:{ hp:4, mp:2, atk:1, def:1, matk:1, mdef:2, spd:0 },
    rate:{ hp:.60, mp:.70, atk:.30, def:.35, matk:.40, mdef:.60, spd:.25 },
  },
  thief: {
    name:'盗賊', type:'basic',
    desc:'素早さに優れた軽快な職業',
    base:{ hp:3, mp:1, atk:2, def:1, matk:0, mdef:0, spd:3 },
    rate:{ hp:.50, mp:.30, atk:.55, def:.20, matk:.15, mdef:.20, spd:.80 },
  },
  knight: {
    name:'騎士', type:'advanced',
    desc:'鉄壁の守りを誇る上級戦士',
    base:{ hp:6, mp:1, atk:3, def:3, matk:0, mdef:1, spd:0 },
    rate:{ hp:.95, mp:.30, atk:.65, def:.75, matk:.10, mdef:.35, spd:.20 },
    skills:[{lv:3,id:'shield_bash'},{lv:8,id:'power_strike'},{lv:15,id:'iron_wall'},{lv:25,id:'devastating_blow'}],
  },
  archmage: {
    name:'魔導士', type:'advanced',
    desc:'最強の攻撃魔法を操る魔術師',
    base:{ hp:3, mp:4, atk:0, def:0, matk:3, mdef:2, spd:0 },
    rate:{ hp:.45, mp:.90, atk:.10, def:.15, matk:.85, mdef:.70, spd:.20 },
    skills:[{lv:3,id:'fireball'},{lv:8,id:'blizzard'},{lv:15,id:'thunder'},{lv:25,id:'meteor'}],
  },
  paladin: {
    name:'聖騎士', type:'advanced',
    desc:'攻守回復のオールラウンダー',
    base:{ hp:5, mp:2, atk:2, def:2, matk:1, mdef:2, spd:0 },
    rate:{ hp:.80, mp:.60, atk:.50, def:.55, matk:.35, mdef:.55, spd:.25 },
    skills:[{lv:3,id:'holy_light'},{lv:8,id:'divine_shield'},{lv:15,id:'judgment'},{lv:25,id:'sacred_blade'}],
  },
  ninja: {
    name:'忍者', type:'advanced',
    desc:'圧倒的な速さと一撃必殺の暗殺者',
    base:{ hp:4, mp:1, atk:3, def:1, matk:0, mdef:1, spd:4 },
    rate:{ hp:.55, mp:.35, atk:.70, def:.25, matk:.15, mdef:.25, spd:.90 },
    skills:[{lv:3,id:'shadow_strike'},{lv:8,id:'smoke_bomb'},{lv:15,id:'twin_strike'},{lv:25,id:'fatal_blow'}],
  },
  sage: {
    name:'賢者', type:'advanced',
    desc:'攻撃魔法と回復魔法を両立する知者',
    base:{ hp:3, mp:3, atk:0, def:1, matk:2, mdef:2, spd:1 },
    rate:{ hp:.50, mp:.75, atk:.10, def:.30, matk:.75, mdef:.70, spd:.30 },
    skills:[{lv:3,id:'heal'},{lv:8,id:'fire'},{lv:15,id:'ice'},{lv:25,id:'holy'}],
  },
};
