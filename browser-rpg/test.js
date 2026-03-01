const fs = require('fs');
const html = fs.readFileSync('/home/user/onepagers/browser-rpg/index.html','utf-8');
const match = html.match(/<script>([\s\S]*?)<\/script>/);
if (!match) { console.log('No script found'); process.exit(1); }
const js = match[1];

// Minimal DOM mock
global.document = {
  createElement: () => ({ textContent:'', get innerHTML(){ return this.textContent; } }),
  getElementById: () => ({ innerHTML:'', scrollTop:0, scrollHeight:0,
    addEventListener:()=>{}, classList:{remove:()=>{}, add:()=>{}},
    querySelectorAll:()=>[], style:{} }),
  querySelectorAll: () => [],
  addEventListener: () => {},
};
global.localStorage = {
  _d:{}, getItem(k){return this._d[k]||null}, setItem(k,v){this._d[k]=v}, removeItem(k){delete this._d[k]}
};
global.setTimeout = (fn,ms) => fn();

// テストも含めて eval 内で実行 (strict mode + const スコープ対策)
const testCode = js + `
;(function(){
  console.log('Jobs:', Object.keys(JOBS).length);
  console.log('Skills:', Object.keys(SKILLS).length);
  console.log('Equips:', Object.keys(EQUIPS).length);
  console.log('Items:', Object.keys(ITEMS).length);
  console.log('Monsters:', MONSTER_POOL.length);
  console.log('Bosses:', Object.keys(BOSSES).length);

  var p = newPlayer('テスト', 'warrior');
  p.equipObjs.weapon = createEquip('wooden_stick', 0);
  p.equipObjs.armor = createEquip('cloth', 0);
  var st = calcStats(p);
  p.hp = st.maxHp; p.mp = st.maxMp;
  console.log('Player stats:', JSON.stringify(st));

  var m = spawnMonster('grassland', 1);
  console.log('Monster:', m.name, 'Lv.'+m.level, 'HP:'+m.hp);
  console.log('EXP gain (lv1 vs lv1):', calcExpGain(1,1));
  console.log('EXP for next level (lv1):', expForNextLevel(1));

  var rates = getGrowthRates(p);
  console.log('Growth rates:', JSON.stringify(rates));

  // Test level up
  var gains = processLevelUp(p);
  console.log('LevelUp gains:', JSON.stringify(gains));

  // Test field exits
  var exits = getFieldExits('grassland', 5);
  console.log('Field exits at grassland 5:', exits.length);

  console.log('\\n✓ All basic tests passed');
})();
`;
try {
  eval(testCode);
} catch(e) {
  console.error('✗ Error:', e.message);
  console.error(e.stack);
  process.exit(1);
}
