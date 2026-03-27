// ===== 数学定数・初期データ =====
const PRIMES = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97];

// 対数殻サイズ μ(I_v) = log(p)/(p-1)  (正規化済み)
function logShellSize(p) {
  return Math.log(p) / (p - 1);
}

// テータ値列 { q^{j²} } の付値列
function thetaValuations(a, lStar) {
  const vals = [];
  for (let j = 1; j <= lStar; j++) {
    vals.push(a * j * j);
  }
  return vals;
}

// Σ j² for j=1..n
function sumOfSquares(n) {
  return n * (n + 1) * (2 * n + 1) / 6;
}

// IUT IV Theorem 1.10 の最終不等式の右辺
function iutBound(logQ, dMod, l, logD, logF, eMod, etaPrm) {
  return (1 + 20 * dMod / l) * (logD + logF) + 20 * (eMod * l + etaPrm);
}
