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

  // Test grassland 15 → wasteland 16 connection
  var exits15 = getFieldExits('grassland', 15);
  var toWasteland = exits15.find(function(e){ return e.area === 'wasteland' && e.layer === 16; });
  if (!toWasteland) throw new Error('grassland 15 -> wasteland 16 connection missing');
  console.log('Grassland 15 → wasteland 16: OK');

  // Test wasteland 16 → grassland 15 return
  var wExits16 = getFieldExits('wasteland', 16);
  var toGrassland = wExits16.find(function(e){ return e.area === 'grassland' && e.layer === 15; });
  if (!toGrassland) throw new Error('wasteland 16 -> grassland 15 return missing');
  console.log('Wasteland 16 → grassland 15: OK');

  // Test castle no longer connects to wasteland
  var castleExits = TOWN_EXITS['castle'];
  var castleToWasteland = castleExits.find(function(e){ return e.area === 'wasteland'; });
  if (castleToWasteland) throw new Error('castle should not connect to wasteland directly');
  console.log('Castle → wasteland removed: OK');

  // Test job selection for all basic jobs
  var basicJobs = Object.keys(JOBS).filter(function(k){ return JOBS[k].type === 'basic'; });
  basicJobs.forEach(function(jobId) {
    var tp = newPlayer('test', jobId);
    if (tp.jobId !== jobId) throw new Error('Job selection failed: expected ' + jobId + ' got ' + tp.jobId);
    if (JOBS[tp.jobId].name !== JOBS[jobId].name) throw new Error('Job name mismatch for ' + jobId);
  });
  console.log('Job selection (all basic jobs): OK');

  // === マップ接続整合性テスト ===
  // 町の出口から到達した先に、元の町(または経由地)へ戻れる経路があるか検証
  var connErrors = [];

  // 1. 町の出口→フィールド の帰還路チェック
  Object.keys(TOWN_EXITS).forEach(function(townId) {
    TOWN_EXITS[townId].forEach(function(exit) {
      var destExits = getFieldExits(exit.area, exit.layer);
      // 出口先から元の町に戻れるか(直接 or 隣接階層経由)
      var canReturn = destExits.some(function(e) {
        return (e.type === 'town' && e.id === townId) ||
               (e.type === 'field' && FIELD_TOWN_MAP[e.area + '_' + e.layer] === townId);
      });
      if (!canReturn) {
        connErrors.push(TOWN_INFO[townId].name + ' → ' + AREA_INFO[exit.area].name + ' 階層' + exit.layer + ' から ' + TOWN_INFO[townId].name + ' に戻れない');
      }
    });
  });

  // 2. フィールド間接続の双方向チェック (エリア間接続のみ)
  var interAreaLinks = [];
  Object.keys(AREA_INFO).forEach(function(area) {
    var info = AREA_INFO[area];
    for (var lv = info.minLv; lv <= info.maxLv; lv++) {
      var fe = getFieldExits(area, lv);
      fe.forEach(function(e) {
        if (e.type === 'field' && e.area !== area) {
          interAreaLinks.push({ from: area, fromLv: lv, to: e.area, toLv: e.layer });
        }
      });
    }
  });
  // 条件付き接続 (ゲーム内条件で出現するため getFieldExits には含まれない)
  var conditionalLinks = [
    { from: 'old_castle', fromLv: 25, to: 'old_castle_hidden', toLv: 25 }, // 隠し通路: ボス10回撃破で出現
  ];
  function isConditional(from, fromLv, to, toLv) {
    return conditionalLinks.some(function(c) {
      return c.from === from && c.fromLv === fromLv && c.to === to && c.toLv === toLv;
    });
  }
  interAreaLinks.forEach(function(link) {
    var reverseExits = getFieldExits(link.to, link.toLv);
    var hasReverse = reverseExits.some(function(e) {
      // フィールドで同エリア内に戻れる or 町に戻れる or 元エリアに戻れる
      return (e.type === 'field' && e.area === link.from) ||
             (e.type === 'town');
    });
    // 逆方向が条件付きの場合はスキップ
    if (!hasReverse && !isConditional(link.to, link.toLv, link.from, link.fromLv)) {
      connErrors.push(AREA_INFO[link.from].name + ' 階層' + link.fromLv + ' → ' + AREA_INFO[link.to].name + ' 階層' + link.toLv + ' に逆方向の接続がない');
    }
  });

  // 3. エリア端(minLv)が孤立していないかチェック: minLv に町入口 or 帰還路があるか
  Object.keys(AREA_INFO).forEach(function(area) {
    var info = AREA_INFO[area];
    var minExits = getFieldExits(area, info.minLv);
    var hasEscape = minExits.some(function(e) {
      return e.type === 'town' || (e.type === 'field' && e.area !== area);
    });
    if (!hasEscape) {
      connErrors.push(AREA_INFO[area].name + ' 階層' + info.minLv + ' (エリア端) に町/他エリアへの出口がない');
    }
  });

  if (connErrors.length > 0) {
    throw new Error('マップ接続エラー:\\n  ' + connErrors.join('\\n  '));
  }
  console.log('Map connectivity check: OK (' + interAreaLinks.length + ' inter-area links verified)');

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
