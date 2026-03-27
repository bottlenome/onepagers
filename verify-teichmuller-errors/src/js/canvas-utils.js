// ===== Canvas描画ユーティリティ =====

function getCtx(canvasId) {
  const c = document.getElementById(canvasId);
  if (!c) return null;
  c.width = c.offsetWidth * (window.devicePixelRatio || 1);
  c.height = c.offsetHeight * (window.devicePixelRatio || 1);
  const ctx = c.getContext('2d');
  ctx.scale(window.devicePixelRatio || 1, window.devicePixelRatio || 1);
  return { ctx, w: c.offsetWidth, h: c.offsetHeight };
}

function clearCanvas(canvasId) {
  const r = getCtx(canvasId);
  if (!r) return null;
  r.ctx.clearRect(0, 0, r.w, r.h);
  return r;
}

// 棒グラフ描画
function drawBarChart(canvasId, labels, values, colors, title, yLabel) {
  const r = clearCanvas(canvasId);
  if (!r) return;
  const { ctx, w, h } = r;
  const pad = { top: 40, right: 20, bottom: 50, left: 70 };
  const cw = w - pad.left - pad.right;
  const ch = h - pad.top - pad.bottom;

  // タイトル
  ctx.fillStyle = '#e2e8f0';
  ctx.font = '13px sans-serif';
  ctx.textAlign = 'center';
  ctx.fillText(title, w / 2, 20);

  // 最大値
  const maxVal = Math.max(...values.map(Math.abs), 1);

  // Y軸
  ctx.fillStyle = '#64748b';
  ctx.font = '10px sans-serif';
  ctx.textAlign = 'right';
  for (let i = 0; i <= 4; i++) {
    const y = pad.top + ch - (i / 4) * ch;
    const v = (i / 4) * maxVal;
    ctx.fillText(v.toFixed(1), pad.left - 8, y + 3);
    ctx.strokeStyle = '#1e293b';
    ctx.beginPath(); ctx.moveTo(pad.left, y); ctx.lineTo(w - pad.right, y); ctx.stroke();
  }
  // Y軸ラベル
  ctx.save();
  ctx.translate(14, pad.top + ch / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.textAlign = 'center';
  ctx.fillStyle = '#94a3b8';
  ctx.font = '10px sans-serif';
  ctx.fillText(yLabel || '', 0, 0);
  ctx.restore();

  // 棒
  const barW = Math.min(cw / labels.length * 0.7, 50);
  const gap = cw / labels.length;
  labels.forEach((label, i) => {
    const barH = (Math.abs(values[i]) / maxVal) * ch;
    const x = pad.left + gap * i + (gap - barW) / 2;
    const y = pad.top + ch - barH;
    ctx.fillStyle = colors[i % colors.length];
    ctx.fillRect(x, y, barW, barH);
    // ラベル
    ctx.fillStyle = '#94a3b8';
    ctx.font = '9px sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText(label, x + barW / 2, pad.top + ch + 14);
    // 値
    ctx.fillStyle = '#e2e8f0';
    ctx.fillText(values[i].toFixed(1), x + barW / 2, y - 5);
  });
}

// 折れ線グラフ描画
function drawLineChart(canvasId, datasets, title, xLabel, yLabel) {
  const r = clearCanvas(canvasId);
  if (!r) return;
  const { ctx, w, h } = r;
  const pad = { top: 40, right: 20, bottom: 50, left: 70 };
  const cw = w - pad.left - pad.right;
  const ch = h - pad.top - pad.bottom;

  ctx.fillStyle = '#e2e8f0';
  ctx.font = '13px sans-serif';
  ctx.textAlign = 'center';
  ctx.fillText(title, w / 2, 20);

  // 全データの範囲
  let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
  datasets.forEach(ds => {
    ds.points.forEach(([x, y]) => {
      if (x < minX) minX = x; if (x > maxX) maxX = x;
      if (y < minY) minY = y; if (y > maxY) maxY = y;
    });
  });
  if (maxX === minX) maxX = minX + 1;
  if (maxY === minY) maxY = minY + 1;
  const rangeX = maxX - minX;
  const rangeY = maxY - minY;

  // グリッド
  ctx.strokeStyle = '#1e293b';
  ctx.fillStyle = '#64748b';
  ctx.font = '9px sans-serif';
  for (let i = 0; i <= 4; i++) {
    const y = pad.top + ch - (i / 4) * ch;
    ctx.beginPath(); ctx.moveTo(pad.left, y); ctx.lineTo(w - pad.right, y); ctx.stroke();
    ctx.textAlign = 'right';
    ctx.fillText((minY + (i / 4) * rangeY).toFixed(1), pad.left - 5, y + 3);
  }
  for (let i = 0; i <= 5; i++) {
    const x = pad.left + (i / 5) * cw;
    ctx.textAlign = 'center';
    ctx.fillText((minX + (i / 5) * rangeX).toFixed(0), x, pad.top + ch + 15);
  }

  // 軸ラベル
  ctx.fillStyle = '#94a3b8';
  ctx.font = '10px sans-serif';
  ctx.textAlign = 'center';
  ctx.fillText(xLabel || '', pad.left + cw / 2, h - 5);
  ctx.save();
  ctx.translate(14, pad.top + ch / 2);
  ctx.rotate(-Math.PI / 2);
  ctx.fillText(yLabel || '', 0, 0);
  ctx.restore();

  // データ線
  datasets.forEach(ds => {
    ctx.strokeStyle = ds.color;
    ctx.lineWidth = 2;
    ctx.beginPath();
    ds.points.forEach(([x, y], i) => {
      const px = pad.left + ((x - minX) / rangeX) * cw;
      const py = pad.top + ch - ((y - minY) / rangeY) * ch;
      if (i === 0) ctx.moveTo(px, py); else ctx.lineTo(px, py);
    });
    ctx.stroke();
    // 凡例
    if (ds.label) {
      const lastPt = ds.points[ds.points.length - 1];
      const lx = pad.left + ((lastPt[0] - minX) / rangeX) * cw;
      const ly = pad.top + ch - ((lastPt[1] - minY) / rangeY) * ch;
      ctx.fillStyle = ds.color;
      ctx.font = '10px sans-serif';
      ctx.textAlign = 'left';
      ctx.fillText(ds.label, lx + 5, ly + 3);
    }
  });
  ctx.lineWidth = 1;
}
