/* ═══════════════════════════════════════
   UIコンポーネント (再利用可能パーツ)
   ═══════════════════════════════════════ */

function renderHeader() {
  if (!G.player) return '<div class="hdr-top"><span class="hdr-name">Loveless Chronicle</span></div>';
  const p = G.player;
  const st = calcStats(p);
  const job = JOBS[p.jobId];
  const hpPct = Math.max(0, p.hp / st.maxHp * 100);
  const mpPct = Math.max(0, p.mp / st.maxMp * 100);
  const expPct = p.level >= MAX_LEVEL ? 100 : (p.exp / expForNextLevel(p.level) * 100);

  return `
    <div class="hdr-top">
      <span><span class="hdr-name">${esc(p.name)}</span> <span class="hdr-job">Lv.${p.level} ${job.name}</span></span>
      <span class="hdr-gold">${p.gold.toLocaleString()}G</span>
    </div>
    <div class="hdr-bars">
      <div class="bar-wrap">
        <span class="bar-label hp">HP</span>
        <div class="bar-track"><div class="bar-fill hp" style="width:${hpPct}%"></div></div>
        <span class="bar-num">${p.hp}/${st.maxHp}</span>
      </div>
      <div class="bar-wrap">
        <span class="bar-label mp">MP</span>
        <div class="bar-track"><div class="bar-fill mp" style="width:${mpPct}%"></div></div>
        <span class="bar-num">${p.mp}/${st.maxMp}</span>
      </div>
    </div>
    <div style="margin-top:2px">
      <div class="bar-wrap">
        <span class="bar-label" style="color:var(--accent);width:28px">EXP</span>
        <div class="bar-track"><div class="bar-fill exp" style="width:${expPct}%"></div></div>
        <span class="bar-num">${p.level>=MAX_LEVEL?'MAX':p.exp+'/'+expForNextLevel(p.level)}</span>
      </div>
    </div>
    <div class="hdr-loc">${locationName(p.location)}</div>`;
}

function renderLog() {
  if (G.log.length === 0) return '';
  return G.log.slice(-15).map(e => `<div class="log-entry ${e.cls}">${e.msg}</div>`).join('');
}

// HP バー (ミニ)
function miniBar(current, max, cls) {
  const pct = Math.max(0, current / max * 100);
  return `<div class="bar-track" style="height:6px"><div class="bar-fill ${cls}" style="width:${pct}%"></div></div>`;
}

// 耐久値表示
function durabilityText(eo) {
  if (!eo || eo.maxDurability === 0) return '';
  const ratio = eo.durability / eo.maxDurability;
  const cls = ratio > 0.5 ? 'dur-ok' : ratio > 0.2 ? 'dur-warn' : 'dur-danger';
  return `<span class="durability ${cls}">[耐久 ${eo.durability}/${eo.maxDurability}]</span>`;
}

// 成功率表示
function rateText(rate) {
  const pct = Math.floor(rate * 100);
  const cls = pct >= 70 ? 'rate-high' : pct >= 40 ? 'rate-mid' : 'rate-low';
  return `<span class="${cls}">${pct}%</span>`;
}

// エスケープ
function esc(s) {
  const d = document.createElement('div');
  d.textContent = s;
  return d.innerHTML;
}

// 戻るボタン
function backBtn(label) {
  label = label || '戻る';
  return `<button class="btn small" data-a="back">&larr; ${label}</button>`;
}
