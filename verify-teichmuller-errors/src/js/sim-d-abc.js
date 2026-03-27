// ===== Sim-D: ABC予想の不等式検証 =====
// IUT IV Theorem 1.10 の不等式を具体的なABC tripleで検証

function findABCTriples(maxC) {
  const triples = [];
  for (let c = 3; c <= maxC; c++) {
    for (let a = 1; a < c; a++) {
      const b = c - a;
      if (b <= a) continue;
      if (gcd(a, b) !== 1) continue;
      const rad = radical(a * b * c);
      const quality = Math.log(c) / Math.log(rad);
      if (quality > 1.0) {
        triples.push({ a, b, c, rad, quality });
      }
    }
  }
  return triples.sort((x, y) => y.quality - x.quality);
}

function gcd(a, b) { return b === 0 ? a : gcd(b, a % b); }

function radical(n) {
  let rad = 1;
  let m = Math.abs(n);
  for (let p = 2; p * p <= m; p++) {
    if (m % p === 0) {
      rad *= p;
      while (m % p === 0) m = m / p;
    }
  }
  if (m > 1) rad *= m;
  return rad;
}

function szpiroRatio(a, b, c) {
  const logDelta = Math.log(16) + 2 * Math.log(a * b * c);
  const logN = Math.log(radical(a * b * c));
  return logDelta / logN;
}

function runSimD() {
  const maxC = parseInt(document.getElementById('simD-maxC').value) || 1000;
  const l = parseInt(document.getElementById('simD-l').value) || 11;
  const lStar = (l - 1) / 2;

  const triples = findABCTriples(maxC).slice(0, 20);
  const sumJ2 = sumOfSquares(lStar);

  // ★グラフの読み方
  let html = '<div class="verdict">';
  html += '<h4>グラフの読み方</h4>';
  html += '<p>ABC予想: a+b=c, gcd(a,b)=1 のとき、c < rad(abc)^{1+ε} が（ほぼ）常に成立<br>';
  html += '<strong>quality</strong> = log(c)/log(rad(abc)) — これが1を超えると「珍しい」triple<br><br>';
  html += '<strong style="color:#60a5fa">青い線</strong> = quality値（1を超えるものを表示）<br>';
  html += '<strong style="color:#f59e0b">黄色い線</strong> = Szpiro比（楕円曲線版の指標）<br>';
  html += '<strong style="color:#ef4444">赤い線</strong> = IUT Theorem 1.10 が主張する上界<br><br>';
  html += '→ 黄色が赤を超えたら IUT の主張に反する反例（見つかっていない）<br>';
  html += '→ ABC予想自体は真と広く信じられている。問題は<strong>証明の正しさ</strong>。</p>';
  html += '</div>';

  html += '<h3>ABC triple (quality > 1.0, c ≤ ' + maxC + ')</h3>';
  html += '<table class="result-table">';
  html += '<tr><th>a</th><th>b</th><th>c=a+b</th><th>rad(abc)</th><th>quality</th><th>Szpiro比</th><th>IUT上界</th></tr>';

  const qualityPts = [];
  const szpiroPts = [];
  const iutBoundPts = [];

  triples.forEach((t, i) => {
    const sz = szpiroRatio(t.a, t.b, t.c);
    const epsilon = 20 / l;
    const iutUpper = 6 * (1 + epsilon);

    qualityPts.push([i, t.quality]);
    szpiroPts.push([i, sz]);
    iutBoundPts.push([i, iutUpper]);

    const qColor = t.quality > 1.4 ? '#ef4444' : t.quality > 1.2 ? '#f59e0b' : '#e2e8f0';
    html += '<tr><td>' + t.a + '</td><td>' + t.b + '</td><td>' + t.c + '</td>';
    html += '<td>' + t.rad + '</td>';
    html += '<td style="color:' + qColor + ';font-weight:bold">' + t.quality.toFixed(4) + '</td>';
    html += '<td>' + sz.toFixed(3) + '</td>';
    html += '<td>' + iutUpper.toFixed(3) + '</td></tr>';
  });
  html += '</table>';

  html += '<h3>既知の高品質ABC triple（参考）</h3>';
  html += '<table class="result-table">';
  html += '<tr><th>triple</th><th>quality</th><th>発見者</th></tr>';
  html += '<tr><td>2 + 3<sup>10</sup>·109 = 23<sup>5</sup></td><td>1.6299</td><td>Reyssat</td></tr>';
  html += '<tr><td>11<sup>2</sup> + 3<sup>2</sup>·5<sup>6</sup>·7<sup>3</sup> = 2<sup>21</sup>·23</td><td>1.6260</td><td>de Smit</td></tr>';
  html += '</table>';

  const maxQuality = triples.length > 0 ? triples[0].quality : 1;
  const maxSzpiro = triples.length > 0 ? szpiroRatio(triples[0].a, triples[0].b, triples[0].c) : 6;

  html += '<div class="verdict ok">';
  html += '<h4>ABC予想の数値的証拠: 圧倒的に支持</h4>';
  html += '<p>c ≤ ' + maxC + ' の範囲で最大quality = ' + maxQuality.toFixed(4) + '<br>';
  html += 'quality > 2 の triple は発見されていない（予想は quality < 1+ε を主張）<br>';
  html += '→ ABC予想自体は真である可能性が極めて高い。</p>';
  html += '</div>';

  html += '<div class="verdict ng">';
  html += '<h4>ただし: 予想が真でも証明が正しいとは限らない</h4>';
  html += '<p>「答え」が正しくても「解法」に誤りがあることは数学では珍しくない。<br>';
  html += '有名な例: ケンプの四色定理の証明（1879年、11年後に誤り発覚）<br>';
  html += 'IUT理論の場合、ABC予想の真偽と系3.12の証明の正しさは独立な問題。<br>';
  html += '本プロジェクトが検証しているのは<strong>証明の論理的健全性</strong>であり、予想の真偽ではない。</p>';
  html += '</div>';

  document.getElementById('simD-result').innerHTML = html;

  if (triples.length > 0) {
    drawLineChart('simD-canvas', [
      { points: szpiroPts, color: '#f59e0b', label: 'Szpiro比' },
      { points: iutBoundPts, color: '#ef4444', label: 'IUT上界' },
      { points: qualityPts, color: '#60a5fa', label: 'quality' }
    ], '青=quality  黄=Szpiro比  赤=IUT上界（黄が赤を超えたら反例）', 'triple番号', '比率');
  }
}
