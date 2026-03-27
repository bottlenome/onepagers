// ===== Sim-D: ABC予想の不等式検証 =====
// IUT IV Theorem 1.10 の不等式を具体的な楕円曲線で検証

// ABC triple (a,b,c) where a+b=c, gcd(a,b)=1
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
        triples.push({ a, b, c, rad, quality: quality });
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

// Szpiro比 (楕円曲線版)
// E: y² = x(x-a)(x+b) に対応する Frey curve
// Δ = 16(abc)² , N = rad(abc)
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

  let html = '<h3>ABC triple (quality > 1.0, c ≤ ' + maxC + ')</h3>';
  html += '<p>quality = log(c)/log(rad(abc)) — 1を超えるものがABC予想の「境界」</p>';
  html += '<table class="result-table">';
  html += '<tr><th>a</th><th>b</th><th>c</th><th>rad(abc)</th><th>quality</th><th>Szpiro比</th><th>IUT上界</th></tr>';

  const qualityPts = [];
  const szpiroPts = [];
  const iutBoundPts = [];

  triples.forEach((t, i) => {
    const sz = szpiroRatio(t.a, t.b, t.c);
    // IUT Theorem 1.10 の上界を簡略計算
    // (1/6)·log(Δ) ≤ (1+ε)·(log-diff + log-cond) + C
    // → Szpiro比 ≤ 6(1+ε) + C/log(N)
    const epsilon = 20 / l; // d_mod/l ≈ 1/l の近似
    const iutUpper = 6 * (1 + epsilon);

    qualityPts.push([i, t.quality]);
    szpiroPts.push([i, sz]);
    iutBoundPts.push([i, iutUpper]);

    html += '<tr><td>' + t.a + '</td><td>' + t.b + '</td><td>' + t.c + '</td>';
    html += '<td>' + t.rad + '</td>';
    html += '<td style="color:' + (t.quality > 1.4 ? '#ef4444' : '#f59e0b') + '">' + t.quality.toFixed(4) + '</td>';
    html += '<td>' + sz.toFixed(3) + '</td>';
    html += '<td>' + iutUpper.toFixed(3) + '</td></tr>';
  });
  html += '</table>';

  // 既知のhigh-quality triples
  html += '<h3>既知の高品質ABC triple</h3>';
  html += '<table class="result-table">';
  html += '<tr><th>triple</th><th>quality</th><th>発見者</th></tr>';
  html += '<tr><td>2 + 3¹⁰·109 = 23⁵</td><td>1.6299</td><td>Reyssat</td></tr>';
  html += '<tr><td>11² + 3²·5⁶·7³ = 2²¹·23</td><td>1.6260</td><td>de Smit</td></tr>';
  html += '<tr><td>19·1307 + 7·29²·31⁸ = 2⁸·3²²·5⁴</td><td>1.6235</td><td>de Smit</td></tr>';
  html += '</table>';

  // IUT不等式の検証
  html += '<h3>IUT不等式の検証</h3>';

  const maxQuality = triples.length > 0 ? triples[0].quality : 1;
  const maxSzpiro = triples.length > 0 ? szpiroRatio(triples[0].a, triples[0].b, triples[0].c) : 6;

  html += '<div class="verdict">';
  html += '<h4>検証結果</h4>';
  html += '<p>観測された最大quality: ' + maxQuality.toFixed(4) + '<br>';
  html += '観測された最大Szpiro比: ' + maxSzpiro.toFixed(3) + '<br>';
  html += 'IUT上界 (l=' + l + '): ' + (6 * (1 + 20/l)).toFixed(3) + '<br><br>';
  html += '<strong>注意</strong>: ABC予想自体は広く真と信じられており、数値的証拠も圧倒的に支持している。';
  html += '問題は予想の真偽ではなく、IUT理論による<em>証明</em>が正しいかどうかである。';
  html += '予想が正しくても証明が不完全という状況は数学史上珍しくない。</p>';
  html += '</div>';

  document.getElementById('simD-result').innerHTML = html;

  // グラフ
  if (triples.length > 0) {
    drawLineChart('simD-canvas', [
      { points: szpiroPts, color: '#f59e0b', label: 'Szpiro比' },
      { points: iutBoundPts, color: '#ef4444', label: 'IUT上界' },
      { points: qualityPts, color: '#60a5fa', label: 'quality' }
    ], 'ABC triples: Szpiro比 vs IUT上界', 'triple番号', '比率');
  }
}
