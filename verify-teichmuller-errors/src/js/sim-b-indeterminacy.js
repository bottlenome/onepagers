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
  const points_ineq = [];
  const tableRows = [];

  for (let i = 0; i <= alphaSteps; i++) {
    const alpha = i / alphaSteps;
    const lhs = logVolQ;
    const rhs_thetaPart = logVolTheta * (1 - alpha);
    const rhs_ind2 = lStar * muI;
    const inequality = rhs_thetaPart - rhs_ind2 - lhs;
    points_ineq.push([alpha, inequality]);

    if (i % 5 === 0) {
      tableRows.push({
        alpha: alpha,
        ind1Effect: (alpha * logVolTheta),
        remaining: rhs_thetaPart,
        inequality: inequality,
        trivial: inequality <= 0
      });
    }
  }

  // 自明化の閾値
  const critAlpha = 1 - (logVolQ + lStar * muI) / logVolTheta;
  const critPct = ((1 - critAlpha) * 100);

  // ★グラフの読み方
  let html = '<div class="verdict">';
  html += '<h4>グラフの読み方</h4>';
  html += '<p>横軸 α = 「Ind1がテータ値情報をどれだけ破壊するか」<br>';
  html += '&nbsp;&nbsp;α=0（左端）: 望月の主張 — Ind1は情報を一切壊さない<br>';
  html += '&nbsp;&nbsp;α=1（右端）: Scholzeの主張 — Ind1が情報を完全に壊す<br><br>';
  html += '<strong style="color:#f59e0b">黄色い線</strong> = 不等式の「非自明性」の値<br>';
  html += '&nbsp;&nbsp;線が<strong>0より上</strong>: 不等式が意味のある情報を含む（非自明）<br>';
  html += '&nbsp;&nbsp;線が<strong>0以下</strong>: 不等式が何も言っていないのと同じ（自明）<br><br>';
  html += '<strong style="color:#ef4444">赤い線</strong> = 自明化の閾値。この線より右では不等式が崩壊する。</p>';
  html += '</div>';

  html += '<h3>αを変化させたときの不等式の状態</h3>';
  html += '<table class="result-table"><tr><th>α</th><th>Ind1が壊す量</th><th>残る情報</th><th>非自明性</th><th>判定</th></tr>';
  tableRows.forEach(r => {
    const cls = r.trivial ? 'style="color:#ef4444;font-weight:bold"' : 'style="color:#22c55e"';
    html += '<tr><td>' + r.alpha.toFixed(2) + '</td>';
    html += '<td>' + r.ind1Effect.toFixed(2) + '</td>';
    html += '<td>' + r.remaining.toFixed(2) + '</td>';
    html += '<td>' + r.inequality.toFixed(2) + '</td>';
    html += '<td ' + cls + '>' + (r.trivial ? '✗ 自明' : '✓ 非自明') + '</td></tr>';
  });
  html += '</table>';

  html += '<div class="verdict ng">';
  html += '<h4>発見: Ind1がわずか ' + critPct.toFixed(2) + '% 効くだけで不等式は崩壊する</h4>';
  html += '<p>自明化の閾値 α = ' + critAlpha.toFixed(4) + '<br>';
  html += 'つまり、Ind1がテータ値情報の <strong>' + critPct.toFixed(2) + '%</strong> を破壊するだけで、';
  html += '系3.12の不等式は何の情報も含まなくなる。<br><br>';
  html += '望月の証明が成立するには α=0（Ind1の効果がゼロ）が必要だが、';
  html += 'Scholzeは α≈1 と主張している。<br>';
  html += '仮に Scholze が間違っていて α がとても小さかったとしても、';
  html += 'α > ' + critAlpha.toFixed(4) + ' ならば証明は成立しない。<br>';
  html += '<strong>この閾値がいかに小さいか</strong>が、証明のギャップの深刻さを示している。</p>';
  html += '</div>';

  document.getElementById('simB-result').innerHTML = html;

  // グラフ
  drawLineChart('simB-canvas', [
    { points: points_ineq, color: '#f59e0b', label: '非自明性' },
    { points: [[critAlpha, -logVolTheta * 0.3], [critAlpha, logVolTheta * 0.8]], color: '#ef4444', label: '閾値 α=' + critAlpha.toFixed(3) },
    { points: [[0, 0], [1, 0]], color: '#475569', label: '自明化ライン' }
  ], 'Ind1制御率 α vs 不等式の非自明性（0以下で自明）', 'α（0=望月, 1=Scholze）', '非自明性');
}
