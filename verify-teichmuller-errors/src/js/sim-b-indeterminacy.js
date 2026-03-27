// ===== Sim-B: 不定性の爆発シミュレーション =====
// Ind1の自由度を変化させたとき、不等式が自明化する様子を可視化

function runSimB() {
  const p = parseInt(document.getElementById('simB-p').value) || 5;
  const a = parseInt(document.getElementById('simB-a').value) || 2;
  const l = parseInt(document.getElementById('simB-l').value) || 11;
  const lStar = (l - 1) / 2;
  const logP = Math.log(p);

  // 基本値
  const sumJ2 = sumOfSquares(lStar);
  const logVolTheta = a * sumJ2 * logP;
  const logVolQ = a * logP;
  const muI = logShellSize(p);

  // Ind1の制御パラメータ α: Ind1の効果 = α × logVolTheta
  // α=0 → 望月モデル（Ind1効果なし）
  // α=1 → Scholzeモデル（Ind1が全情報を飲み込む）
  const alphaSteps = 50;
  const points_ineq = []; // 不等式の左辺 - 右辺（負なら成立）
  const points_mochi = []; // 望月モデルの値
  const points_scholze = []; // Scholzeモデルの値
  const tableRows = [];

  for (let i = 0; i <= alphaSteps; i++) {
    const alpha = i / alphaSteps;

    // 不等式: -|log(q)| ≤ -|log(Θ)| + Ind1補正 + Ind2補正
    // = -(logVolTheta) + α * logVolTheta + lStar * muI
    // 成立条件: -logVolQ ≤ -logVolTheta + α * logVolTheta + lStar * muI
    // ⟺ logVolTheta - logVolQ ≤ α * logVolTheta + lStar * muI
    // ⟺ logVolTheta * (1 - α) - logVolQ ≤ lStar * muI

    const lhs = logVolQ; // |log(q)|
    const rhs_thetaPart = logVolTheta * (1 - alpha); // Ind1で残る部分
    const rhs_ind2 = lStar * muI;
    const inequality = rhs_thetaPart - rhs_ind2 - lhs; // >0なら非自明

    points_ineq.push([alpha, inequality]);
    points_mochi.push([alpha, rhs_thetaPart]);
    points_scholze.push([alpha, lhs]);

    if (i % 10 === 0) {
      tableRows.push({
        alpha: alpha.toFixed(2),
        ind1Effect: (alpha * logVolTheta).toFixed(2),
        remaining: rhs_thetaPart.toFixed(2),
        trivial: inequality <= 0 ? '自明' : '非自明'
      });
    }
  }

  // 自明化の閾値
  const critAlpha = 1 - (logVolQ + lStar * muI) / logVolTheta;

  let html = '<h3>Ind1制御パラメータ α の効果</h3>';
  html += '<p>α=0: 望月モデル（Ind1の効果なし）<br>';
  html += 'α=1: Scholzeモデル（Ind1が全情報を破壊）</p>';

  html += '<table class="result-table"><tr><th>α</th><th>Ind1の効果</th><th>残存情報</th><th>判定</th></tr>';
  tableRows.forEach(r => {
    const cls = r.trivial === '自明' ? 'style="color:#ef4444"' : 'style="color:#22c55e"';
    html += '<tr><td>' + r.alpha + '</td><td>' + r.ind1Effect + '</td><td>' + r.remaining + '</td>';
    html += '<td ' + cls + '><strong>' + r.trivial + '</strong></td></tr>';
  });
  html += '</table>';

  html += '<div class="verdict ng">';
  html += '<h4>自明化の閾値: α = ' + critAlpha.toFixed(4) + '</h4>';
  html += '<p>Ind1がテータ値情報のわずか ' + ((1-critAlpha)*100).toFixed(2) + '% を破壊するだけで不等式は自明化する。<br>';
  html += '望月の主張（α=0）が成立するには、Ind1が対数殻内で完全に制御される必要がある。<br>';
  html += 'Scholzeの主張（α→1）では不等式は完全に自明。</p>';
  html += '</div>';

  document.getElementById('simB-result').innerHTML = html;

  // グラフ
  drawLineChart('simB-canvas', [
    { points: points_ineq, color: '#f59e0b', label: '非自明性' },
    { points: [[critAlpha, -logVolTheta * 0.5], [critAlpha, logVolTheta * 0.5]], color: '#ef4444', label: '閾値' }
  ], 'Ind1制御率 α vs 不等式の非自明性', 'α (Ind1制御パラメータ)', '非自明性 (>0で非自明)');
}
