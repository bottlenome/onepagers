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

// Szpiro比 (楕円曲線版)
// Frey curve: y² = x(x-a)(x+b)
// Δ = 16(abc)², N = rad(abc)
function szpiroRatio(a, b, c) {
  const logDelta = Math.log(16) + 2 * Math.log(a * b * c);
  const logN = Math.log(radical(a * b * c));
  return logDelta / logN;
}

// IUT IV Theorem 1.10 の完全な上界
// (1/6)·log(q) ≤ (1 + 20·d_mod/l)·(log(d) + log(f)) + 20·(e*_mod·l + η_prm)
//
// Szpiro比の上界に変換すると:
//   log(Δ)/log(N) ≤ 6·(1 + 20/l) + 6·20·(e*·l + η) / log(N)
//                    ~~~~~~~~~~~~   ~~~~~~~~~~~~~~~~~~~~~~~~~~
//                    乗法的部分      加法的定数 / log(N)
//
// d_mod=1, e*_mod ≈ 2^12·3^3·5 = 552960 (IUT IV定義), η_prm ≈ 4 (素数分布定数)
function iutFullBound(l, logN) {
  const dMod = 1;
  const eStarMod = 2*2*2*2 * 3*3*3 * 5; // 2^4·3^3·5 = 2160 (簡略化した見積もり)
  const etaPrm = 4; // 素数分布の定数
  const multiplicative = 6 * (1 + 20 * dMod / l);
  const additive = 6 * 20 * (eStarMod * l + etaPrm) / Math.max(logN, 1);
  return multiplicative + additive;
}

function runSimD() {
  const maxC = parseInt(document.getElementById('simD-maxC').value) || 1000;
  const l = parseInt(document.getElementById('simD-l').value) || 11;
  const lStar = (l - 1) / 2;

  const triples = findABCTriples(maxC).slice(0, 20);

  // ★グラフの読み方
  let html = '<div class="verdict">';
  html += '<h4>グラフの読み方</h4>';
  html += '<p>ABC予想: a+b=c, gcd(a,b)=1 のとき、c < rad(abc)^{1+ε} が（ほぼ）常に成立<br>';
  html += '<strong>quality</strong> = log(c)/log(rad(abc)) — これが1を超えると「珍しい」triple<br><br>';
  html += '<strong style="color:#60a5fa">青い線</strong> = quality値（1を超えるものを表示）<br>';
  html += '<strong style="color:#f59e0b">黄色い線</strong> = Szpiro比（楕円曲線版の指標）<br>';
  html += '<strong style="color:#ef4444">赤い線</strong> = IUT Theorem 1.10 の完全な上界（乗法項 + 加法定数）<br>';
  html += '<strong style="color:#475569">灰色の線</strong> = 乗法項のみ（加法定数なし）の簡略上界<br><br>';
  html += '→ 黄色が赤を超えたらIUTの反例。加法定数を含めると上界は非常に大きくなる。<br>';
  html += '→ ABC予想自体は真と広く信じられている。問題は<strong>証明の正しさ</strong>。</p>';
  html += '</div>';

  html += '<h3>ABC triple (quality > 1.0, c ≤ ' + maxC + ')</h3>';

  // IUTパラメータの説明
  const multOnly = 6 * (1 + 20 / l);
  html += '<div class="verdict">';
  html += '<h4>IUT Theorem 1.10 のパラメータ (l=' + l + ')</h4>';
  html += '<p>乗法的部分: 6×(1 + 20/' + l + ') = <strong>' + multOnly.toFixed(3) + '</strong><br>';
  html += '加法的定数: 6×20×(e*_mod·l + η_prm) / log(N) — triple ごとに異なる（<strong>l に比例して増大</strong>）<br>';
  html += '→ l を大きくすると乗法項はタイトになるが、加法定数が爆発する。<br>';
  html += '→ IUT IV では l ∼ ht(E) に選ぶことでバランスを取る。</p>';
  html += '</div>';

  html += '<table class="result-table">';
  html += '<tr><th>a</th><th>b</th><th>c=a+b</th><th>rad</th><th>quality</th>';
  html += '<th>Szpiro比</th><th>乗法項のみ</th><th>完全な上界</th><th>判定</th></tr>';

  const qualityPts = [];
  const szpiroPts = [];
  const iutMultPts = [];
  const iutFullPts = [];
  let anyExceed = false;

  triples.forEach((t, i) => {
    const sz = szpiroRatio(t.a, t.b, t.c);
    const logN = Math.log(radical(t.a * t.b * t.c));
    const fullBound = iutFullBound(l, logN);
    const exceedsMult = sz > multOnly;
    const exceedsFull = sz > fullBound;

    qualityPts.push([i, t.quality]);
    szpiroPts.push([i, sz]);
    iutMultPts.push([i, multOnly]);
    iutFullPts.push([i, Math.min(fullBound, 100)]); // 表示上100で切る

    if (exceedsFull) anyExceed = true;

    const qColor = t.quality > 1.4 ? '#ef4444' : t.quality > 1.2 ? '#f59e0b' : '#e2e8f0';
    html += '<tr><td>' + t.a + '</td><td>' + t.b + '</td><td>' + t.c + '</td>';
    html += '<td>' + t.rad + '</td>';
    html += '<td style="color:' + qColor + ';font-weight:bold">' + t.quality.toFixed(4) + '</td>';
    html += '<td>' + sz.toFixed(3) + '</td>';
    html += '<td>' + multOnly.toFixed(3) + '</td>';
    html += '<td>' + fullBound.toFixed(1) + '</td>';
    if (exceedsMult) {
      html += '<td style="color:#f59e0b">⚠ 乗法項超え<br>(加法定数で救済)</td>';
    } else {
      html += '<td style="color:#22c55e">✓ OK</td>';
    }
    html += '</tr>';
  });
  html += '</table>';

  // 乗法項を超えるケースの解説
  const exceedsMultCount = triples.filter(t => szpiroRatio(t.a, t.b, t.c) > multOnly).length;
  if (exceedsMultCount > 0) {
    html += '<div class="verdict">';
    html += '<h4>⚠ 乗法項のみでは ' + exceedsMultCount + '個のtripleが上界を超える</h4>';
    html += '<p>これは <strong>IUT の反例ではない</strong>。IUT Theorem 1.10 の不等式には';
    html += '加法定数 20·(e*_mod·l + η_prm) が含まれており、この項が上界を大幅に引き上げる。<br>';
    html += 'l=' + l + ' の場合、加法定数は非常に大きく（e*_mod ∼ 数千）、';
    html += '小さな c に対しては Szpiro比を簡単に飲み込む。<br><br>';
    html += '<strong>要するに</strong>: IUT の上界は「乗法項 + 巨大な加法定数」の形をしており、';
    html += '小さい数の範囲では加法定数が支配的。';
    html += 'これは不等式としては非常にゆるい（＝情報量が少ない）ことを意味する。</p>';
    html += '</div>';
  }

  html += '<h3>既知の高品質ABC triple（参考）</h3>';
  html += '<table class="result-table">';
  html += '<tr><th>triple</th><th>quality</th><th>発見者</th></tr>';
  html += '<tr><td>2 + 3<sup>10</sup>·109 = 23<sup>5</sup></td><td>1.6299</td><td>Reyssat</td></tr>';
  html += '<tr><td>11<sup>2</sup> + 3<sup>2</sup>·5<sup>6</sup>·7<sup>3</sup> = 2<sup>21</sup>·23</td><td>1.6260</td><td>de Smit</td></tr>';
  html += '</table>';

  html += '<div class="verdict ok">';
  html += '<h4>ABC予想の数値的証拠: 圧倒的に支持</h4>';
  html += '<p>既知の最大quality ≈ 1.63（ABC予想は任意の ε > 0 に対して quality < 1+ε を主張）。<br>';
  html += 'quality > 2 の triple は発見されていない。予想は真である可能性が極めて高い。</p>';
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
      { points: iutMultPts, color: '#475569', label: '乗法項のみ' },
      { points: qualityPts, color: '#60a5fa', label: 'quality' }
    ], '青=quality  黄=Szpiro比  灰=IUT乗法項（完全上界は遥かに上）', 'triple番号', '比率');
  }
}
