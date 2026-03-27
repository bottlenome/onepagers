// ===== Sim-A: Θ-リンクの数値シミュレーション =====
// テータ値列 {q^{j²}} の生成とΘ-リンクの動作を可視化

function runSimA() {
  const p = parseInt(document.getElementById('simA-p').value) || 5;
  const a = parseInt(document.getElementById('simA-a').value) || 2;
  const l = parseInt(document.getElementById('simA-l').value) || 11;
  const lStar = (l - 1) / 2;

  // テータ値列の付値
  const thetaVals = thetaValuations(a, lStar);
  const sumTheta = thetaVals.reduce((s, v) => s + v, 0);
  const qVal = a;

  // 対数体積
  const logP = Math.log(p);
  const logVolTheta = sumTheta * logP;
  const logVolQ = qVal * logP;
  const ratio = sumTheta / qVal;

  // 対数殻サイズ
  const muI = logShellSize(p);
  const ind2Total = lStar * muI;

  // 結果テーブル
  let html = '<h3>テータ値列 (p=' + p + ', q=p^' + a + ', l=' + l + ', l*=' + lStar + ')</h3>';
  html += '<table class="result-table"><tr><th>j</th><th>j²</th><th>v_p(q^{j²})</th><th>q^{j²}</th></tr>';
  for (let j = 1; j <= lStar; j++) {
    const vp = a * j * j;
    html += '<tr><td>' + j + '</td><td>' + (j*j) + '</td><td>' + vp + '</td><td>' + p + '^' + vp + '</td></tr>';
  }
  html += '</table>';

  // 比較表
  html += '<h3>Θ-リンクの歪み分析</h3>';
  html += '<table class="result-table">';
  html += '<tr><th>項目</th><th>値</th></tr>';
  html += '<tr><td>テータ値付値の合計 Σv_p(q^{j²})</td><td>' + sumTheta + '</td></tr>';
  html += '<tr><td>q-パラメータの付値 v_p(q)</td><td>' + qVal + '</td></tr>';
  html += '<tr><td><strong>歪み率 Σj²</strong></td><td><strong>' + ratio + '</strong></td></tr>';
  html += '<tr><td>対数体積(テータ側)</td><td>' + logVolTheta.toFixed(3) + '</td></tr>';
  html += '<tr><td>対数体積(q側)</td><td>' + logVolQ.toFixed(3) + '</td></tr>';
  html += '<tr><td>対数殻サイズ μ(I_v)</td><td>' + muI.toFixed(4) + '</td></tr>';
  html += '<tr><td>Ind2累積 l*×μ(I_v)</td><td>' + ind2Total.toFixed(4) + '</td></tr>';
  html += '</table>';

  // 判定
  html += '<div class="verdict ng">';
  html += '<h4>歪み分析の結論</h4>';
  html += '<p>歪み率 = ' + ratio + ' に対して、対数殻による補正は ' + ind2Total.toFixed(3) + ' のみ。';
  html += '歪みの ' + (logVolTheta / ind2Total).toFixed(1) + '倍の対数殻が必要 → ';
  html += 'Ind1が対数殻に収まらなければ不等式は自明化する。</p>';
  html += '</div>';

  document.getElementById('simA-result').innerHTML = html;

  // グラフ: 付値の比較
  const labels = [];
  const vals = [];
  for (let j = 1; j <= lStar; j++) {
    labels.push('j=' + j);
    vals.push(a * j * j);
  }
  labels.push('q');
  vals.push(qVal);
  const colors = labels.map((_, i) => i < lStar ? '#60a5fa' : '#ef4444');
  drawBarChart('simA-canvas', labels, vals, colors,
    'Θ-リンク: テータ値 vs q-パラメータの付値', 'v_p(・)');
}
