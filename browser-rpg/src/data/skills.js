/* ═══════════════════════════════════════
   スキルデータ
   type: physical / magical / hybrid / heal / buff
   power: ダメージ倍率 or 回復割合
   cost: MP消費
   ═══════════════════════════════════════ */
const SKILLS = {
  // --- 装備スキル (武器サブタイプ) ---
  slash:       { name:'斬撃',     type:'physical', power:1.5, cost:3,  desc:'剣で力強く斬りつける' },
  magic_bolt:  { name:'魔弾',     type:'magical',  power:1.5, cost:5,  desc:'魔力の弾を放つ' },
  quick_stab:  { name:'急所突き', type:'physical', power:1.3, cost:2,  crit:0.3, desc:'急所を狙って突く' },
  arrow_rain:  { name:'矢の雨',   type:'physical', power:1.4, cost:4,  desc:'矢を連射する' },

  // --- 装備スキル (防具サブタイプ) ---
  guard:         { name:'ガード',     type:'buff', effect:'guard',    cost:0, desc:'身を守り被ダメージ半減' },
  evasion:       { name:'回避姿勢',   type:'buff', effect:'evade',    cost:0, desc:'回避に専念する' },
  magic_barrier: { name:'魔法障壁',   type:'buff', effect:'mbarrier', cost:8, desc:'魔法ダメージを軽減' },

  // --- 装備スキル (アクセサリーサブタイプ) ---
  power_charge: { name:'力溜め',   type:'buff',     effect:'atkup',  cost:0,  desc:'次の攻撃力2倍' },
  protect:      { name:'守護',     type:'buff',     effect:'defup',  cost:0,  desc:'防御力を一時上昇' },
  focus:        { name:'精神集中', type:'buff',     effect:'matkup', cost:0,  desc:'次の魔法攻撃力2倍' },
  gale:         { name:'疾風',     type:'physical', power:1.2, cost:2, first:true, desc:'先制の素早い一撃' },
  vitality:     { name:'生命力',   type:'heal',     power:0.2, cost:0, desc:'HPを20%回復' },
  dragon_breath:{ name:'竜の息吹', type:'magical',  power:2.0, cost:15, desc:'竜の炎で焼き尽くす' },

  // --- 騎士スキル ---
  shield_bash:      { name:'シールドバッシュ', type:'physical', power:1.5, cost:5,  stun:0.3, desc:'盾で殴り気絶させる' },
  power_strike:     { name:'パワーストライク', type:'physical', power:2.0, cost:8,  desc:'渾身の一撃' },
  iron_wall:        { name:'鉄壁',             type:'buff',     effect:'ironwall', cost:10, desc:'防御力大幅アップ' },
  devastating_blow: { name:'壊滅撃',           type:'physical', power:3.0, cost:15, desc:'全てを砕く必殺の一撃' },

  // --- 魔導士スキル ---
  fireball: { name:'ファイアボール', type:'magical', power:2.0, cost:8,  desc:'炎の玉を放つ' },
  blizzard: { name:'ブリザード',     type:'magical', power:2.0, cost:12, desc:'氷の嵐を起こす' },
  thunder:  { name:'サンダー',       type:'magical', power:2.5, cost:15, desc:'雷を落とす' },
  meteor:   { name:'メテオ',         type:'magical', power:4.0, cost:30, desc:'隕石を降らせる' },

  // --- 聖騎士スキル ---
  holy_light:    { name:'ホーリーライト', type:'heal',    power:0.3,  cost:8,  desc:'聖なる光でHP回復' },
  divine_shield: { name:'聖なる盾',       type:'buff',    effect:'invincible', cost:12, desc:'1度だけ攻撃無効' },
  judgment:      { name:'ジャッジメント', type:'hybrid',  power:2.0,  cost:20, desc:'聖なる裁きを下す' },
  sacred_blade:  { name:'聖剣',           type:'hybrid',  power:3.0,  cost:25, desc:'聖なる力を纏った一撃' },

  // --- 忍者スキル ---
  shadow_strike: { name:'影斬り', type:'physical', power:1.5, cost:5,  first:true, desc:'影から斬りつける' },
  smoke_bomb:    { name:'煙幕',   type:'buff',     effect:'smoke', cost:10, desc:'煙幕で攻撃を回避' },
  twin_strike:   { name:'二刀流', type:'physical', power:1.2, cost:12, hits:2, desc:'二回連続攻撃' },
  fatal_blow:    { name:'必殺',   type:'physical', power:4.0, cost:20, crit:0.5, desc:'一撃必殺を狙う' },

  // --- 賢者スキル ---
  heal: { name:'ヒール',   type:'heal',    power:0.5,  cost:10, desc:'HPを大きく回復' },
  fire: { name:'ファイア', type:'magical', power:1.8,  cost:6,  desc:'炎で攻撃' },
  ice:  { name:'アイス',   type:'magical', power:2.0,  cost:10, desc:'氷で攻撃' },
  holy: { name:'ホーリー', type:'magical', power:3.5,  cost:25, healPct:0.3, desc:'聖なる光で攻撃しHP回復' },

  // --- ルーンナイトスキル ---
  rune_slash:  { name:'ルーンスラッシュ', type:'physical', power:1.5, cost:4,  desc:'符術を纏った斬撃' },
  rune_ward:   { name:'ルーンウォード',   type:'buff',     effect:'mbarrier', cost:5, desc:'魔法防御の符術を展開' },
  rune_strike: { name:'ルーンストライク', type:'physical', power:2.5, cost:12, desc:'符術で強化した一撃' },
  rune_burst:  { name:'ルーンバースト',   type:'physical', power:3.5, cost:20, desc:'最大出力の符術斬り' },
};

// 装備サブタイプ → スキルID マッピング
const SUBTYPE_SKILL = {
  sword:'slash', staff:'magic_bolt', dagger:'quick_stab', bow:'arrow_rain',
  heavy:'guard', light:'evasion', robe:'magic_barrier',
  power:'power_charge', guard_acc:'protect', magic_acc:'focus',
  speed:'gale', hp_acc:'vitality', dragon:'dragon_breath',
};

// 鍛冶で稀に付与される貴重スキル
const SMITH_RARE_SKILLS = {
  weapon: [
    { id:'power_strike',  weight:3 },
    { id:'twin_strike',   weight:2 },
    { id:'fireball',      weight:2 },
    { id:'thunder',       weight:1 },
  ],
  armor: [
    { id:'iron_wall',      weight:3 },
    { id:'divine_shield',  weight:1 },
    { id:'magic_barrier',  weight:2 },
  ],
};
const SMITH_RARE_SKILL_CHANCE = 0.08; // 8%の確率
