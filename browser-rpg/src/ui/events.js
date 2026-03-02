/* ═══════════════════════════════════════
   イベントハンドリング
   ═══════════════════════════════════════ */

let selectedJob = null;

// デバッグキャラプリセット (特定の名前で開始すると使える)
const DEBUG_PRESETS = {
  // ドラゴン戦テスト: 2ループ戦士→騎士 + 伝説の剣 + ミスリル鎧
  'DRAGON': {
    jobId:'knight', baseStats:{hp:84,mp:2,atk:36,def:36,matk:1,mdef:2,spd:18},
    growthStats:{hp:201,mp:37,atk:105,def:108,matk:2,mdef:39,spd:5},
    weapon:'legendary_sword', armor:'mithril_armor', accessory:'dragon_amulet',
    weaponEnhance:0, armorEnhance:0,
    location:{type:'town',id:'minetown'}, lastTown:'minetown',
  },
  // エルフ王戦テスト: 4ループ(戦士→僧侶→戦士→僧侶)→ルーンナイト (魔防+攻撃特化)
  'ELFKING': {
    jobId:'rune_knight', baseStats:{hp:135,mp:50,atk:45,def:46,matk:25,mdef:48,spd:15},
    growthStats:{hp:181,mp:75,atk:113,def:40,matk:4,mdef:114,spd:5},
    weapon:'legendary_sword', armor:'spirit_armor', accessory:'dragon_amulet',
    weaponEnhance:0, armorEnhance:0,
    location:{type:'town',id:'elfvillage'}, lastTown:'elfvillage',
  },
  // 古城の主戦テスト: 4ループ僧侶→聖騎士 (魔攻+防御特化)
  'CASTLE': {
    jobId:'paladin', baseStats:{hp:116,mp:68,atk:32,def:34,matk:35,mdef:65,spd:6},
    growthStats:{hp:168,mp:75,atk:72,def:73,matk:39,mdef:73,spd:7},
    weapon:'spirit_staff', armor:'spirit_armor', accessory:'magic_amulet',
    weaponEnhance:0, armorEnhance:0,
    location:{type:'town',id:'lasttown'}, lastTown:'lasttown',
  },
  // 魔神戦テスト: 10ループ僧侶→聖騎士 (HP+魔防+防御特化)
  'DEMON': {
    jobId:'paladin', baseStats:{hp:132,mp:77,atk:36,def:38,matk:39,mdef:74,spd:6},
    growthStats:{hp:168,mp:75,atk:72,def:73,matk:39,mdef:73,spd:7},
    weapon:'legendary_sword', armor:'mithril_armor', accessory:'dragon_amulet',
    weaponEnhance:0, armorEnhance:0,
    location:{type:'town',id:'lasttown'}, lastTown:'lasttown',
  },
  // 古城隠しボス戦テスト: 20ループ戦士→騎士 + 装備+5
  'LEGEND': {
    jobId:'knight', baseStats:{hp:168,mp:5,atk:72,def:72,matk:2,mdef:4,spd:37},
    growthStats:{hp:201,mp:37,atk:105,def:108,matk:2,mdef:39,spd:5},
    weapon:'legendary_sword', armor:'mithril_armor', accessory:'dragon_amulet',
    weaponEnhance:5, armorEnhance:5,
    location:{type:'town',id:'lasttown'}, lastTown:'lasttown',
    bossDefeats:{old_castle_boss_defeats:10},
  },
};

function setupEvents() {
  document.getElementById('main').addEventListener('click', (e) => {
    const btn = e.target.closest('[data-a]');
    if (!btn) return;
    const action = btn.dataset.a;
    const p1 = btn.dataset.p;
    const p2 = btn.dataset.p2;
    handleAction(action, p1, p2);
  });
}

function handleAction(action, p1, p2) {
  const p = G.player;
  switch (action) {
    // --- タイトル ---
    case 'newgame':
      G.screen = 'naming';
      selectedJob = null;
      render();
      break;
    case 'continue':
      if (loadGame()) {
        G.screen = p ? (G.player.location.type === 'town' ? 'town' : 'field') : 'title';
        if (G.player && G.player.location.type === 'town') G.screen = 'town';
        else if (G.player) G.screen = 'field';
        render();
      }
      break;

    // --- 名前・職業選択 ---
    case 'selectjob': {
      selectedJob = p1;
      document.querySelectorAll('.job-card').forEach(el => el.classList.remove('selected'));
      const jc = document.getElementById('jc-' + p1);
      if (jc) jc.classList.add('selected');
      const startBtn = document.getElementById('btn-start');
      if (startBtn) startBtn.disabled = false;
      break;
    }
    case 'startgame': {
      const nameInput = document.getElementById('name-input');
      const name = nameInput ? nameInput.value.trim() : '勇者';
      if (!name || !selectedJob) break;
      const preset = DEBUG_PRESETS[name];
      if (preset) {
        // デバッグキャラ: プリセットのステータスで開始
        G.player = newPlayer(name, preset.jobId);
        G.player.level = 30;
        G.player.baseStats = { ...preset.baseStats };
        G.player.growthStats = { ...preset.growthStats };
        G.player.equipObjs.weapon = createEquip(preset.weapon, preset.weaponEnhance || 0);
        G.player.equipObjs.armor = createEquip(preset.armor, preset.armorEnhance || 0);
        if (preset.accessory) G.player.equipObjs.accessory = createEquip(preset.accessory, 0);
        addItemToPlayer(G.player, 'tent', 99);
        addItemToPlayer(G.player, 'elixir', 10);
        addItemToPlayer(G.player, 'hi_herb', 10);
        G.player.gold = 99999;
        G.player.location = { ...preset.location };
        G.player.lastTown = preset.lastTown;
        if (preset.bossDefeats) G.player.bossDefeats = { ...preset.bossDefeats };
        // 上級職スキルをすべて習得済み扱い (Lv30)
        if (!G.player.jobHistory.includes(selectedJob)) G.player.jobHistory.push(selectedJob);
        const st = calcStats(G.player);
        G.player.hp = st.maxHp;
        G.player.mp = st.maxMp;
        addLog('デバッグキャラ「' + name + '」で冒険開始！', 'lvup');
        saveGame();
        setScreen(G.player.location.type === 'town' ? 'town' : 'field');
      } else {
        // 通常のゲーム開始
        G.player = newPlayer(name, selectedJob);
        G.player.equipObjs.weapon = createEquip('wooden_stick', 0);
        G.player.equipObjs.armor = createEquip('cloth', 0);
        addItemToPlayer(G.player, 'herb', 3);
        const st = calcStats(G.player);
        G.player.hp = st.maxHp;
        G.player.mp = st.maxMp;
        addLog('冒険が始まった！', 'system');
        saveGame();
        setScreen('town');
      }
      break;
    }

    // --- 町施設 ---
    case 'facility':
      handleFacility(p1, p2);
      break;

    // --- 移動 ---
    case 'movetown':
      moveTo({ type:'town', id:p1 });
      break;
    case 'movefield': {
      const destArea = p1;
      const destLayer = parseInt(p2);
      moveTo({ type:'field', area:destArea, layer:destLayer });
      const mon = spawnMonster(destArea, destLayer);
      if (mon) { saveGame(); startBattle(mon); }
      break;
    }

    // --- フィールド ---
    case 'explore':
      G.battle = null;
      explore();
      break;
    case 'screen':
      pushScreen(p1);
      break;

    // --- 戦闘 ---
    case 'battlespeed':
      G.settings.battleSpeed = G.settings.battleSpeed <= 200 ? 600 : 200;
      render();
      break;
    case 'battleend':
      // 闘技場の結果処理
      if (G.battle && G.battle.enemy && G.battle.enemy.arena) {
        if (G.battle.won) {
          const prize = G.battle.enemy.level * 20;
          G.player.gold += prize;
          G.player.arenaProgress++;
          addLog(`闘技場勝利！賞金${prize}Gを獲得！`, 'reward');
          if (G.player.arenaProgress >= ARENA_OPPONENTS.length && G.player.arenaUndefeated) {
            if (!G.player.titles.includes('闘技場の覇者')) {
              G.player.titles.push('闘技場の覇者');
              addLog('称号「闘技場の覇者」を獲得！', 'lvup');
            }
          }
        } else {
          G.player.arenaProgress = 0;
          G.player.arenaUndefeated = false;
        }
        saveGame();
      }
      G.battle = null;
      if (G.player.location.type === 'town') setScreen('town');
      else setScreen('field');
      break;
    case 'battleend-status':
      G.battle = null;
      G.screen = G.player.location.type === 'town' ? 'town' : 'field';
      G.screenStack = [];
      pushScreen('status');
      break;
    case 'battleend-movetown':
      G.battle = null;
      moveTo({ type:'town', id:p1 });
      break;
    case 'battleend-movefield': {
      G.battle = null;
      const destArea2 = p1;
      const destLayer2 = parseInt(p2);
      moveTo({ type:'field', area:destArea2, layer:destLayer2 });
      const mon2 = spawnMonster(destArea2, destLayer2);
      if (mon2) { saveGame(); startBattle(mon2); }
      break;
    }

    // --- ショップ ---
    case 'shoptab':
      G.shopTab = p1;
      render();
      break;
    case 'buy': {
      const shop = SHOPS[G.shopId];
      if (shop) buyShopItem(shop.items[parseInt(p1)]);
      break;
    }
    case 'sell':
      if (p2 === 'equip') sellItem(null, true, parseInt(p1));
      else sellItem(p1, false, 0);
      break;

    // --- 装備 ---
    case 'equip':
      equipItem(parseInt(p1));
      break;
    case 'unequip':
      unequipItem(p1);
      break;

    // --- アイテム使用 ---
    case 'useitem':
      useItemFromInventory(p1);
      break;

    // --- ステータスタブ ---
    case 'statustab':
      G.statusTab = p1;
      render();
      break;

    // --- 作戦 ---
    case 'strategy':
      G.settings.strategy = p1;
      saveGame();
      render();
      break;

    // --- 宿屋 ---
    case 'doinn':
      stayAtInn(parseInt(p1));
      break;

    // --- 転職 ---
    case 'dojobchange':
      if (p1 === G.player.jobId) { addLog('現在の職業と同じです', 'system'); render(); break; }
      if (G.jobChangeAdvanced && G.player.level < 15) { addLog('Lv.15以上必要です', 'danger'); render(); break; }
      if (G.jobChangeAdvanced && JOBS[G.player.jobId].type === 'advanced') { addLog('上級職からは転職できません。下級職に戻してから転職してください。', 'danger'); render(); break; }
      {
        const isAdv = JOBS[p1].type === 'advanced';
        const prevSt = isAdv ? calcStats(G.player) : null;
        changeJob(G.player, p1);
        addLog(`${JOBS[p1].name}に転職した！`, 'lvup');
        if (isAdv && prevSt) {
          const newSt = calcStats(G.player);
          const boosts = STAT_KEYS
            .filter(k => {
              const prev = k === 'hp' ? prevSt.maxHp : k === 'mp' ? prevSt.maxMp : prevSt[k];
              const now = k === 'hp' ? newSt.maxHp : k === 'mp' ? newSt.maxMp : newSt[k];
              return now > prev;
            })
            .map(k => {
              const prev = k === 'hp' ? prevSt.maxHp : k === 'mp' ? prevSt.maxMp : prevSt[k];
              const now = k === 'hp' ? newSt.maxHp : k === 'mp' ? newSt.maxMp : newSt[k];
              return STAT_NAMES[k] + '+' + (now - prev);
            });
          if (boosts.length) addLog(`ステータスアップ！ ${boosts.join(' ')}`, 'lvup');
        }
      }
      saveGame();
      render();
      break;

    // --- 闘技場 ---
    case 'doarena':
      enterArena();
      break;

    // --- 銀行 ---
    case 'bankdeposit':
      bankDeposit(parseInt(p1));
      break;
    case 'bankwithdraw':
      bankWithdraw(parseInt(p1));
      break;

    // --- 倉庫 ---
    case 'whstore':
      if (p2 === 'equip') warehouseStore(null, true, parseInt(p1));
      else warehouseStore(p1, false, 0);
      break;
    case 'whretrieve':
      if (p2 === 'equip') warehouseRetrieve(null, true, parseInt(p1));
      else warehouseRetrieve(p1, false, 0);
      break;

    // --- 鍛冶 ---
    case 'dosmith':
      doSmith(parseInt(p1));
      break;
    case 'dorepair':
      doRepair(p1);
      break;
    case 'dorepairbag':
      doRepairBag(parseInt(p1));
      break;

    // --- 合成 ---
    case 'dosynth':
      doSynth(parseInt(p1));
      break;

    // --- 強化 ---
    case 'doenhance':
      doEnhance(p1, parseInt(p2));
      break;

    // --- 戻る ---
    case 'back':
      popScreen();
      break;
  }
}

function handleFacility(facilityId, param) {
  switch (facilityId) {
    case 'inn':
      G.innCost = parseInt(param) || 10;
      pushScreen('inn');
      break;
    case 'shop':
      G.shopId = param;
      G.shopTab = 'buy';
      pushScreen('shop');
      break;
    case 'jobchange':
      G.jobChangeAdvanced = (param === 'true');
      pushScreen('jobchange');
      break;
    case 'arena':
      pushScreen('arena');
      break;
    case 'bank':
      pushScreen('bank');
      break;
    case 'warehouse':
      pushScreen('warehouse');
      break;
    case 'blacksmith':
      pushScreen('blacksmith');
      break;
    case 'synthesis':
      pushScreen('synthesis');
      break;
    case 'enhancement':
      pushScreen('enhancement');
      break;
    case 'status':
      pushScreen('status');
      break;
    case 'social_arena':
    case 'social_tavern':
      addLog('この機能は今後のアップデートで追加予定です', 'system');
      render();
      break;
  }
}
