/-
# M176: 幾何級数による逆元近似 — (1−r)·s_k ≡ 1 mod (λ^{km})（柱B）

M170（環の幾何級数の残差 (1−r)·s_k + r^k = 1）と M164（膜のイデアル・
冪法則 r ∈ (λ^m) ⟹ r^k ∈ (λ^{km})）の合流。**公比 r が (λ^m) に
入るとき、幾何部分和 s_k は 1−r の逆元を精度 (λ^{km}) で近似する**
（(1−r)·s_k は 1 と (λ^{km}) を法として合同）ことを choice なしで
閉じる。付値環で「1−r で割る」ことの定量版。

  * M176-1 `sub_one_eq_neg_of_add_eq_one` — 環の整形補題
    a + b = 1 ⟹ a − 1 = −b
  * M176-2 **`isValAtLeast_inv_approx`** — 逆元近似:
    r ∈ (λ^m) ⟹ (1−r)·s_k − 1 ∈ (λ^{km})
    （残差 M170 で (1−r)·s_k − 1 = −r^k、冪法則 M164 で r^k ∈ (λ^{km})）
  * M176-3 `LambdaInvApproxData` — 総括

意義: 幾何級数 ∑r^i が 1−r の逆元の近似列であること——その誤差
(1−r)·s_k − 1 = −r^k が深さ km で 0 に近づく——を定量的に示す。
これは完備付値環で 1−r（r が位相的に小さい）が可逆であることの
**代数的核心**（誤差が (λ) の高冪に沈む）で、M172（s_k ≡ 1）を
「逆元近似」の水準へ引き上げる。k → ∞ で誤差 → 0（完備性）が
実際の逆元を与える。

正直な限定: 実際の逆元 (1−r)⁻¹ の存在（k → ∞ の極限 = ∩(λ^{km}) = 0
の完備性・∑r^i の収束）は位相・完備化を要し次層。本層は各有限 k での
誤差の所属（イデアル合同）のみ。

全て選択公理不使用。
-/
import IUT.GeomSeriesRec
import IUT.LambdaIdeal

namespace IUT

/-! ## M176-1: 環の整形補題 -/

/-- **補題 (M176-1): a + b = 1 ⟹ a − 1 = −b** — 残差式から誤差式への
    移項。a, b を不透明に扱い、a 内部の 1 と衝突させない。 -/
theorem sub_one_eq_neg_of_add_eq_one (R : CRing) {a b : R.carrier}
    (h : R.add a b = R.one) : R.add a (R.neg R.one) = R.neg b := by
  rw [← h, CRing.neg_add_dist, ← R.add_assoc, CRing.add_neg, R.zero_add]

/-! ## M176-2: 逆元近似 -/

/-- **定理 (M176-2): 逆元近似** — r ∈ (λ^m) なら (1−r)·s_k − 1 ∈ (λ^{km})。
    M170 残差 (1−r)·s_k + r^k = 1 より誤差 (1−r)·s_k − 1 = −r^k、
    M164 冪法則で r^k ∈ (λ^{km})、反元閉性で −r^k ∈ (λ^{km})。
    幾何部分和は 1−r の逆元を精度 (λ^{km}) で近似する。 -/
theorem isValAtLeast_inv_approx {R : CRing} {lam r : R.carrier} {m : Nat}
    (hr : IsValAtLeast R lam r m) (k : Nat) :
    IsValAtLeast R lam
      (R.add (R.mul (R.add R.one (R.neg r)) (crGeomSum R r k)) (R.neg R.one))
      (k * m) := by
  rw [sub_one_eq_neg_of_add_eq_one R (geom_residual R r k)]
  exact isValAtLeast_neg (isValAtLeast_pow hr k)

/-! ## M176-3: 総括 -/

/-- **M176-3a: 総括** — 幾何級数の逆元近似データ。 -/
structure LambdaInvApproxData where
  /-- a + b = 1 ⟹ a − 1 = −b。 -/
  sub_one : ∀ (R : CRing) (a b : R.carrier),
    R.add a b = R.one → R.add a (R.neg R.one) = R.neg b
  /-- r ∈ (λ^m) ⟹ (1−r)·s_k − 1 ∈ (λ^{km})。 -/
  inv_approx : ∀ (R : CRing) (lam r : R.carrier) (m : Nat),
    IsValAtLeast R lam r m → ∀ k,
    IsValAtLeast R lam
      (R.add (R.mul (R.add R.one (R.neg r)) (crGeomSum R r k)) (R.neg R.one))
      (k * m)

/-- **M176-3b: witness**。 -/
def lambdaInvApproxData : LambdaInvApproxData where
  sub_one := fun R _ _ h => sub_one_eq_neg_of_add_eq_one R h
  inv_approx := fun _ _ _ _ hr k => isValAtLeast_inv_approx hr k

/-- **M176-3c: 存在**。 -/
theorem lambdaInvApprox_exists : Nonempty LambdaInvApproxData :=
  ⟨lambdaInvApproxData⟩

end IUT
