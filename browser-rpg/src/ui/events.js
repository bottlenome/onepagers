/* ═══════════════════════════════════════
   イベントハンドリング
   ═══════════════════════════════════════ */

let selectedJob = null;

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
    case 'selectjob':
      selectedJob = p1;
      document.querySelectorAll('.job-card').forEach(el => el.classList.remove('selected'));
      const jc = document.getElementById('jc-' + p1);
      if (jc) jc.classList.add('selected');
      const startBtn = document.getElementById('btn-start');
      if (startBtn) startBtn.disabled = false;
      break;
    case 'startgame': {
      const nameInput = document.getElementById('name-input');
      const name = nameInput ? nameInput.value.trim() : '勇者';
      if (!name || !selectedJob) break;
      G.player = newPlayer(name, selectedJob);
      // 初期装備
      G.player.equipObjs.weapon = createEquip('wooden_stick', 0);
      G.player.equipObjs.armor = createEquip('cloth', 0);
      // 初期アイテム
      addItemToPlayer(G.player, 'herb', 3);
      // HP/MP設定
      const st = calcStats(G.player);
      G.player.hp = st.maxHp;
      G.player.mp = st.maxMp;
      addLog('冒険が始まった！', 'system');
      saveGame();
      setScreen('town');
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
      changeJob(G.player, p1);
      addLog(`${JOBS[p1].name}に転職した！`, 'lvup');
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
