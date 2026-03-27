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
  const gapMultiple = (logVolTheta / ind2Total);

  // 結果テーブル
  let html = '<h3>テータ値列 (p=' + p + ', q=p^' + a + ', l=' + l + ', l*=' + lStar + ')</h3>';

  // ★グラフの読み方
  html += '<div class="verdict">';
  html += '<h4>グラフの読み方</h4>';
  html += '<p><strong style="color:#60a5fa">青い棒</strong> = テータ値の付値 v_p(q^{j²})。j が大きいほど j² で急成長する。<br>';
  html += '<strong style="color:#ef4444">赤い棒</strong> = q-パラメータの付値 v_p(q)。Θ-リンクは青い棒すべてを赤い棒1本に「圧縮」する。<br>';
  html += '→ 青と赤の<strong>落差が大きいほど「歪み」が大きい</strong>。この歪みがABC不等式の源泉。<br>';
  html += '→ しかし圧縮の過程で足し算の情報が失われる（不定性の発生）。</p>';
  html += '</div>';

  html += '<table class="result-table"><tr><th>j</th><th>j²</th><th>v_p(q^{j²})</th><th>q^{j²}</th><th>意味</th></tr>';
  for (let j = 1; j <= lStar; j++) {
    const vp = a * j * j;
    const isMax = (j === lStar);
    html += '<tr><td>' + j + '</td><td>' + (j*j) + '</td><td>' + vp + '</td>';
    html += '<td>' + p + '<sup>' + vp + '</sup></td>';
    html += '<td>' + (isMax ? '← 最大のテータ値（最大の歪み）' : '') + '</td></tr>';
  }
  html += '</table>';

  // 比較表
  html += '<h3>歪みの定量分析</h3>';
  html += '<table class="result-table">';
  html += '<tr><th>項目</th><th>値</th><th>何を意味するか</th></tr>';
  html += '<tr><td>テータ値付値の合計</td><td>' + sumTheta + '</td><td>世界A側の「情報量」</td></tr>';
  html += '<tr><td>q-パラメータの付値</td><td>' + qVal + '</td><td>世界B側の「受け皿」</td></tr>';
  html += '<tr style="color:#f59e0b"><td><strong>歪み率 Σj²</strong></td><td><strong>×' + ratio + '</strong></td>';
  html += '<td>テータ側は q 側の ' + ratio + '倍の情報量</td></tr>';
  html += '<tr><td>対数殻サイズ μ(I_v)</td><td>' + muI.toFixed(4) + '</td><td>不定性を吸収できる「クッション」</td></tr>';
  html += '<tr><td>Ind2累積 l*×μ(I_v)</td><td>' + ind2Total.toFixed(4) + '</td><td>全 j にわたるクッションの合計</td></tr>';
  html += '</table>';

  // 判定
  html += '<div class="verdict ng">';
  html += '<h4>核心的な数値: 歪みはクッションの ' + gapMultiple.toFixed(1) + '倍</h4>';
  html += '<p>テータ値の歪み（= ' + logVolTheta.toFixed(1) + '）に対して、';
  html += '対数殻のクッション（= ' + ind2Total.toFixed(3) + '）は<strong>わずか ';
  html += (100/gapMultiple).toFixed(2) + '%</strong> しかカバーしない。<br>';
  html += '残り ' + (100 - 100/gapMultiple).toFixed(2) + '% は「Ind1が対数殻に収まる」という';
  html += '<strong style="color:#ef4444">未証明の仮定</strong>に依存している。<br>';
  html += 'これが Scholze-Stix 批判の定量的な核心。</p>';
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
    '青=テータ値の付値  赤=q-パラメータの付値（圧縮先）', 'v_p(・)');
}
