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

    rows.push({ p, mu, ind2, thetaVol, ratio: thetaVol / ind2 });
  });

  const totalQVol = usedPrimes.reduce((s, p) => s + a * Math.log(p), 0);
  const coverageRatio = totalLogShell / totalThetaVol;
  const coveragePct = (coverageRatio * 100);

  // ★グラフの読み方
  let html = '<div class="verdict">';
  html += '<h4>グラフの読み方</h4>';
  html += '<p>各素数について2本の棒を表示:<br>';
  html += '<strong style="color:#22c55e">緑の棒</strong> = 対数殻のサイズ（不定性を吸収できる「クッション」の大きさ）<br>';
  html += '<strong style="color:#ef4444">赤の棒</strong> = テータ値の歪み（Θ-リンクが生む「圧縮」の大きさ）<br><br>';
  html += '→ <strong>赤が緑を大幅に上回る</strong>ほど、対数殻では歪みを吸収しきれない。<br>';
  html += '→ 素数を増やすと、この差が累積的に拡大する。</p>';
  html += '</div>';

  html += '<h3>素数別: 対数殻 vs テータ歪み</h3>';
  html += '<table class="result-table">';
  html += '<tr><th>素数 p</th><th>対数殻 μ(I_p)</th><th style="color:#22c55e">クッション合計</th>';
  html += '<th style="color:#ef4444">テータ歪み</th><th>カバー率</th><th>意味</th></tr>';
  rows.forEach(r => {
    const pct = (r.ind2 / r.thetaVol * 100);
    const meaning = pct < 2 ? '深刻な不足' : pct < 10 ? '大幅な不足' : '不足';
    html += '<tr><td>' + r.p + '</td>';
    html += '<td>' + r.mu.toFixed(4) + '</td>';
    html += '<td style="color:#22c55e">' + r.ind2.toFixed(3) + '</td>';
    html += '<td style="color:#ef4444">' + r.thetaVol.toFixed(3) + '</td>';
    html += '<td style="color:' + (pct < 5 ? '#ef4444' : '#f59e0b') + ';font-weight:bold">' + pct.toFixed(2) + '%</td>';
    html += '<td>' + meaning + '</td></tr>';
  });
  html += '<tr style="font-weight:bold;border-top:2px solid #475569">';
  html += '<td>全素数合計</td><td>-</td>';
  html += '<td style="color:#22c55e">' + totalLogShell.toFixed(3) + '</td>';
  html += '<td style="color:#ef4444">' + totalThetaVol.toFixed(3) + '</td>';
  html += '<td style="color:#ef4444">' + coveragePct.toFixed(2) + '%</td>';
  html += '<td></td></tr>';
  html += '</table>';

  html += '<div class="verdict ng">';
  html += '<h4>結論: 対数殻はテータ歪みの ' + coveragePct.toFixed(2) + '% しか吸収できない</h4>';
  html += '<p>残り ' + (100 - coveragePct).toFixed(2) + '% の歪みは、';
  html += '「Ind1（内部自己同型の不定性）が対数殻の中に収まる」という仮定でカバーされる。<br><br>';
  html += '<strong>この仮定が IUT 証明の最大の未証明部分</strong>であり、Scholze-Stix の批判はまさにこの点を突いている。<br>';
  html += '素数の数を増やすと（スライダーで試してみてください）、カバー率はさらに下がり、';
  html += '未証明部分への依存度が上がる。</p>';
  html += '</div>';

  document.getElementById('simC-result').innerHTML = html;

  // グラフ: 素数ごとに緑（対数殻）と赤（テータ歪み）を並べる
  // 2グループ描画のため、交互に配置
  const allLabels = [];
  const allVals = [];
  const allColors = [];
  rows.forEach(r => {
    allLabels.push(r.p + ':殻');
    allVals.push(r.ind2);
    allColors.push('#22c55e');
    allLabels.push(r.p + ':歪');
    allVals.push(r.thetaVol);
    allColors.push('#ef4444');
  });

  drawBarChart('simC-canvas', allLabels, allVals, allColors,
    '素数別: 緑=対数殻(クッション)  赤=テータ歪み(圧縮)', '対数体積');
}
