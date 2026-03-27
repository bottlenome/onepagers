// ===== Sim-C: 対数殻サイズ vs 不定性の比較 =====
// 複数素数にわたる累積効果を可視化

function runSimC() {
  const numPrimes = parseInt(document.getElementById('simC-primes').value) || 5;
  const l = parseInt(document.getElementById('simC-l').value) || 11;
  const a = parseInt(document.getElementById('simC-a').value) || 2;
  const lStar = (l - 1) / 2;

  const usedPrimes = PRIMES.slice(0, numPrimes);
  const sumJ2 = sumOfSquares(lStar);

  let totalLogShell = 0;
  let totalThetaVol = 0;
  const rows = [];

  usedPrimes.forEach(p => {
    const mu = logShellSize(p);
    const logP = Math.log(p);
    const thetaVol = a * sumJ2 * logP;
    const ind2 = lStar * mu;

    totalLogShell += ind2;
    totalThetaVol += thetaVol;

    rows.push({
      p: p,
      mu: mu,
      ind2: ind2,
      thetaVol: thetaVol,
      ratio: thetaVol / ind2
    });
  });

  const totalQVol = usedPrimes.reduce((s, p) => s + a * Math.log(p), 0);
  const coverageRatio = totalLogShell / totalThetaVol;

  let html = '<h3>対数殻 vs テータ値歪み（' + numPrimes + '素数, l=' + l + '）</h3>';
  html += '<table class="result-table">';
  html += '<tr><th>素数 p</th><th>μ(I_p)</th><th>Ind2累積</th><th>テータ歪み</th><th>カバー率</th></tr>';
  rows.forEach(r => {
    const pct = (r.ind2 / r.thetaVol * 100).toFixed(2);
    html += '<tr><td>' + r.p + '</td>';
    html += '<td>' + r.mu.toFixed(4) + '</td>';
    html += '<td>' + r.ind2.toFixed(3) + '</td>';
    html += '<td>' + r.thetaVol.toFixed(3) + '</td>';
    html += '<td style="color:' + (parseFloat(pct) < 5 ? '#ef4444' : '#f59e0b') + '">' + pct + '%</td></tr>';
  });
  html += '<tr style="font-weight:bold;border-top:2px solid #475569">';
  html += '<td>合計</td><td>-</td>';
  html += '<td>' + totalLogShell.toFixed(3) + '</td>';
  html += '<td>' + totalThetaVol.toFixed(3) + '</td>';
  html += '<td style="color:#ef4444">' + (coverageRatio * 100).toFixed(2) + '%</td></tr>';
  html += '</table>';

  // ht(E) ≈ 6 * totalQVol として ABC不等式をチェック
  const htE = 6 * totalQVol;
  const lhs = totalQVol; // (1/6) * ht(E)

  html += '<h3>ABC不等式への影響</h3>';
  html += '<table class="result-table">';
  html += '<tr><th>項目</th><th>値</th></tr>';
  html += '<tr><td>左辺 (1/6)·ht(E) ≈ Σ v_p(q)·log(p)</td><td>' + lhs.toFixed(3) + '</td></tr>';
  html += '<tr><td>Ind2による累積補正</td><td>' + totalLogShell.toFixed(3) + '</td></tr>';
  html += '<tr><td>Ind2/左辺 比率</td><td>' + (totalLogShell / lhs).toFixed(2) + '倍</td></tr>';
  html += '</table>';

  html += '<div class="verdict ng">';
  html += '<h4>対数殻の制約力: テータ歪みの ' + (coverageRatio * 100).toFixed(2) + '% しかカバーできない</h4>';
  html += '<p>対数殻は各素数でのInd2を制御するが、テータ値の歪み（Σj² ≈ ' + sumJ2 + '）に比べて';
  html += '遥かに小さい。Ind1がこの差分を埋められなければ、不等式は非自明にならない。<br>';
  html += '素数の数を増やすと累積効果はさらに顕著になる。</p>';
  html += '</div>';

  document.getElementById('simC-result').innerHTML = html;

  // グラフ: 素数ごとの対数殻 vs テータ歪み
  const labels = rows.map(r => 'p=' + r.p);
  const shellVals = rows.map(r => r.ind2);
  const thetaVals = rows.map(r => r.thetaVol);

  drawBarChart('simC-canvas',
    labels.concat(labels),
    shellVals.concat(thetaVals),
    shellVals.map(() => '#22c55e').concat(thetaVals.map(() => '#ef4444')),
    '緑=対数殻(Ind2)  赤=テータ歪み  (素数別)',
    '対数体積');
}
