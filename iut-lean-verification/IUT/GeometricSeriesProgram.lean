/-
# M178: 幾何級数プログラムの総括 capstone（柱C）

第101弾で建設した幾何級数〜逆元近似の一連（M163〜M177）を、**単一の
レコード `GeometricSeriesProgramData` に束ねて一括 certification** する。
witness は全て既存定理名のみ——**新規証明ゼロ**（§7.5 の capstone 束ね）。
`#print axioms geometricSeriesProgramData` が全鎖の choice-free 性を
一度に確認する。

収録する 12 の柱石:

  1. `geom_closed`（M163） — 環の閉形式 (1−r)·s_k = 1 − r^k
  2. `geom_rec_left`（M170） — 環の左漸化式 s_{k+1} = 1 + r·s_k
  3. `geom_residual`（M170） — 環の残差 (1−r)·s_k + r^k = 1
  4. `real_geom_closed`（M165） — 実数の閉形式
  5. `real_geom_rec_left`（M168） — 実数の左漸化式
  6. `realPow_add`（M166） — 実数冪の指数法則 r^{m+n} ≈ r^m·r^n
  7. `rabs_pow`（M169） — 絶対値の冪 |r^k| ≈ |r|^k
  8. `rabs_triangle`（M174） — 三角不等式 |x+y| ≤ |x|+|y|
  9. `rabs_geomSum_le`（M175） — 絶対値評価 |Σrⁱ| ≤ Σ|r|ⁱ
  10. `isValAtLeast_inv_approx`（M176） — 環の逆元近似 (1−r)·s_k−1 ∈ (λ^{km})
  11. `real_geom_inv_error`（M177） — 実数の誤差 (1⊖r)·s_k⊖1 ≈ ⊖r^k
  12. `rabs_geom_inv_error`（M177） — 誤差の絶対値 |(1⊖r)·s_k⊖1| ≈ |r|^k

意義: 幾何級数の代数（閉形式・漸化式・残差）が環と実数の双方で成立し、
それが冪法則・絶対値・三角不等式・順序と結合して、**1−r の逆元近似**
（環では誤差 ∈ (λ^{km})、実数では |誤差| = |r|^k）まで一気通貫で
choice なしに閉じることを、単一レコードで証拠化する。局所類体論の主
単数（M31/M172）と実数解析（M165〜M175）を橋渡しする土台の総括。

正直な限定: 収束そのもの（k → ∞ の極限 = 実際の逆元 (1−r)⁻¹）は
順序完備性・rate-bound の次層。本 capstone は有限 k での全恒等式・
不等式・合同を束ねたもの。

全て選択公理不使用。
-/
import IUT.LambdaInvApprox
import IUT.RealGeomInv
import IUT.RealGeomAbs

namespace IUT

/-! ## M178-1: プログラム総括レコード -/

/-- **M178-1: 幾何級数プログラムの総括** — M163〜M177 の 12 柱石を束ねる。 -/
structure GeometricSeriesProgramData where
  /-- 環の閉形式 (1−r)·s_k = 1 − r^k。 -/
  ring_closed : ∀ (R : CRing) (r : R.carrier) (k : Nat),
    R.mul (R.add R.one (R.neg r)) (crGeomSum R r k)
      = R.add R.one (R.neg (rpow R r k))
  /-- 環の左漸化式 s_{k+1} = 1 + r·s_k。 -/
  ring_rec_left : ∀ (R : CRing) (r : R.carrier) (k : Nat),
    crGeomSum R r (k + 1) = R.add R.one (R.mul r (crGeomSum R r k))
  /-- 環の残差 (1−r)·s_k + r^k = 1。 -/
  ring_residual : ∀ (R : CRing) (r : R.carrier) (k : Nat),
    R.add (R.mul (R.add R.one (R.neg r)) (crGeomSum R r k)) (rpow R r k)
      = R.one
  /-- 実数の閉形式 (1⊖r)·s_k ≈ 1⊖r^k。 -/
  real_closed : ∀ (r : RReal) (k : Nat),
    realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) (realGeomSum r k))
      (realAdd (qToReal ratRing.one) (realNeg (realPow r k)))
  /-- 実数の左漸化式 s_{k+1} ≈ 1 ⊕ r·s_k。 -/
  real_rec_left : ∀ (r : RReal) (k : Nat),
    realEq (realGeomSum r (k + 1))
      (realAdd (qToReal ratRing.one) (rmul r (realGeomSum r k)))
  /-- 実数冪の指数法則 r^{m+n} ≈ r^m·r^n。 -/
  real_pow_add : ∀ (r : RReal) (m n : Nat),
    realEq (realPow r (m + n)) (rmul (realPow r m) (realPow r n))
  /-- 絶対値の冪 |r^k| ≈ |r|^k。 -/
  abs_pow : ∀ (r : RReal) (k : Nat),
    realEq (rabs (realPow r k)) (realPow (rabs r) k)
  /-- 三角不等式 |x+y| ≤ |x|+|y|。 -/
  triangle : ∀ x y : RReal,
    rLe (rabs (realAdd x y)) (realAdd (rabs x) (rabs y))
  /-- 絶対値評価 |Σrⁱ| ≤ Σ|r|ⁱ。 -/
  geomSum_abs_le : ∀ (r : RReal) (k : Nat),
    rLe (rabs (realGeomSum r k)) (realGeomSum (rabs r) k)
  /-- 環の逆元近似 (1−r)·s_k − 1 ∈ (λ^{km})。 -/
  ring_inv_approx : ∀ (R : CRing) (lam r : R.carrier) (m : Nat),
    IsValAtLeast R lam r m → ∀ k,
    IsValAtLeast R lam
      (R.add (R.mul (R.add R.one (R.neg r)) (crGeomSum R r k)) (R.neg R.one))
      (k * m)
  /-- 実数の誤差 (1⊖r)·s_k ⊖ 1 ≈ ⊖r^k。 -/
  real_inv_error : ∀ (r : RReal) (k : Nat),
    realEq (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realNeg (qToReal ratRing.one)))
      (realNeg (realPow r k))
  /-- 誤差の絶対値 |(1⊖r)·s_k ⊖ 1| ≈ |r|^k。 -/
  abs_inv_error : ∀ (r : RReal) (k : Nat),
    realEq (rabs (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realNeg (qToReal ratRing.one))))
      (realPow (rabs r) k)

/-- **M178-2: witness** — 全て既存定理名（新規証明ゼロ）。 -/
def geometricSeriesProgramData : GeometricSeriesProgramData where
  ring_closed := geom_closed
  ring_rec_left := geom_rec_left
  ring_residual := geom_residual
  real_closed := real_geom_closed
  real_rec_left := real_geom_rec_left
  real_pow_add := realPow_add
  abs_pow := rabs_pow
  triangle := rabs_triangle
  geomSum_abs_le := rabs_geomSum_le
  ring_inv_approx := fun _ _ _ _ hr k => isValAtLeast_inv_approx hr k
  real_inv_error := real_geom_inv_error
  abs_inv_error := rabs_geom_inv_error

/-- **M178-3: 存在** — 幾何級数プログラムの一括 certification。 -/
theorem geometricSeriesProgram_exists : Nonempty GeometricSeriesProgramData :=
  ⟨geometricSeriesProgramData⟩

end IUT
