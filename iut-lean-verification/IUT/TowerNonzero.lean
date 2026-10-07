/-
# M119: 塔の λ の非零性（正則性を法とする完全解決）

M111（剰余塔）は「λₙ 非単元」まで与えたが「λₙ₊₁ ≠ 0」は残った。
本層はこれを**一段下の λₙ の正則性（非零因子性）に還元**する:

  λₙ が Oₙ の正則元かつ非単元 ⟹ λₙ₊₁ ≠ 0 in Oₙ₊₁。

証明の核: Y = h·(πY + Y^p − λ) と書けたとすると、
Y⁰ 係数: 0 = h₀·(−λ) → 正則性で h₀ = 0、
Y¹ 係数: 1 = h₀·π + h₁·(−λ) = −h₁λ → λ が単元 → M111 に矛盾。
つまり **λ の非単元性（M111 の剰余塔）と正則性が合流して非零性を生む**。

  * M119-1 `psMul_coeff_one` — 積級数の 1 次係数 (fg)₁ = f₀g₁ + f₁g₀
  * M119-2 `towerStepPoly_coeff_one` — 一段多項式の 1 次係数は π
  * M119-3 `IsRegularElem` — 正則元（非零因子）述語
  * M119-4 `towerLam_ne_zero` — 一般環での本丸
  * M119-5 `tower_lam_step_ne_zero` — 塔への instance
    （非単元性は M111 の tower_lam_not_unit が無条件供給）
  * M119-6 `TowerNonzeroData` — 総括

正直な限定: 基底 λ₁ = eisLambda の**平明な正則性**（∀h, hλ = 0 → h = 0）
は witness 形整域性（M91F/M93F/M96F）からは選択公理なしに出ない
（x ≠ 0 から witness を取り出せない）。平明正則性は簡約係数の
単射性（座標系 O ≅ ℤ_p^{p−1} の忠実性）として次層の課題。
本層の還元により、それが済めば λₙ ≠ 0 が全レベルに伝播する。

全て選択公理不使用。
-/
import IUT.ResidueTower

namespace IUT

/-! ## 係数補題 -/

/-- **M119-1: 積級数の 1 次係数** (fg)₁ = f₀g₁ + f₁g₀。 -/
theorem psMul_coeff_one (R : CRing) (f g : PS R) :
    psMul R f g 1 = R.add (R.mul (f 0) (g 1)) (R.mul (f 1) (g 0)) := by
  show R.add (R.add R.zero (R.mul (f 0) (g 1))) (R.mul (f 1) (g 0))
    = R.add (R.mul (f 0) (g 1)) (R.mul (f 1) (g 0))
  rw [R.zero_add]

/-- **M119-2: 一段多項式の 1 次係数** (πY + Y^p − λ)₁ = π
    （p ≥ 2 で Y^p は 1 次に寄与しない）。 -/
theorem towerStepPoly_coeff_one (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) :
    towerStepPoly p R piR lamR 1 = piR := by
  show R.add (R.add (psSingle R piR 1 1) (psMono R p 1))
      (R.neg (psC R lamR 1)) = piR
  rw [show psSingle R piR 1 1 = piR from if_pos rfl,
    show psMono R p 1 = R.zero from if_neg (by omega),
    show psC R lamR 1 = R.zero from if_neg (by omega),
    CRing.neg_zero R, CRing.add_zero R, CRing.add_zero R]

/-! ## 正則元 -/

/-- **M119-3: 正則元（非零因子）** — a との積が 0 なら相手は 0。 -/
def IsRegularElem (R : CRing) (a : R.carrier) : Prop :=
  ∀ h, R.mul h a = R.zero → h = R.zero

/-- 反元が 0 なら元も 0（neg の対合性）。 -/
theorem neg_eq_zero_iff (R : CRing) {a : R.carrier}
    (h : R.neg a = R.zero) : a = R.zero := by
  rw [← CRing.neg_neg R a, h, CRing.neg_zero R]

/-! ## 本丸: 一般環での非零性 -/

/-- **定理 (M119-4): 塔の一意化元の非零性（一般形）** —
    λ が正則かつ非単元なら Y mod (πY + Y^p − λ) ≠ 0。
    Y = h·(πY + Y^p − λ) の 0 次・1 次係数比較で
    h₀ = 0（正則性）→ 1 = −h₁λ（λ 単元）→ 矛盾。 -/
theorem towerLam_ne_zero (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (hreg : IsRegularElem R lamR)
    (hnu : ∀ v, R.mul lamR v ≠ R.one) :
    towerLam p R piR lamR ≠ (towerStep p R piR lamR).zero := by
  intro h
  have hrel : idealRel (psRing R) (towerStepPoly p R piR lamR)
      (psX R) (psRing R).zero :=
    quot_exact_ideal (psRing R) (towerStepPoly p R piR lamR) h
  obtain ⟨w, hw⟩ := hrel
  -- 0 次係数: 0 = w₀·(−λ)
  have h0 : R.add (psX R 0) (R.neg (psZero R 0))
      = psMul R w (towerStepPoly p R piR lamR) 0 := congrFun hw 0
  have h0' : R.zero = R.mul (w 0) (R.neg lamR) := by
    have e1 : R.add (psX R 0) (R.neg (psZero R 0)) = R.zero := by
      show R.add R.zero (R.neg R.zero) = R.zero
      rw [CRing.neg_zero R, R.zero_add]
    have e2 : psMul R w (towerStepPoly p R piR lamR) 0
        = R.mul (w 0) (R.neg lamR) := by
      rw [psMul_coeff_zero R w (towerStepPoly p R piR lamR),
        towerStepPoly_coeff_zero p (by omega) R piR lamR]
    exact e1.symm.trans (h0.trans e2)
  have hw0 : w 0 = R.zero := by
    apply hreg (w 0)
    have h3 : R.neg (R.mul (w 0) lamR) = R.zero := by
      rw [← CRing.mul_neg R (w 0) lamR]
      exact h0'.symm
    exact neg_eq_zero_iff R h3
  -- 1 次係数: 1 = −(λ·w₁)
  have h1 : R.add (psX R 1) (R.neg (psZero R 1))
      = psMul R w (towerStepPoly p R piR lamR) 1 := congrFun hw 1
  have h1' : R.one = R.neg (R.mul lamR (w 1)) := by
    have e1 : R.add (psX R 1) (R.neg (psZero R 1)) = R.one := by
      show R.add R.one (R.neg R.zero) = R.one
      rw [CRing.neg_zero R, CRing.add_zero R]
    have e2 : psMul R w (towerStepPoly p R piR lamR) 1
        = R.neg (R.mul lamR (w 1)) := by
      rw [psMul_coeff_one R w (towerStepPoly p R piR lamR),
        towerStepPoly_coeff_one p hp R piR lamR,
        towerStepPoly_coeff_zero p (by omega) R piR lamR,
        hw0, CRing.zero_mul R, R.zero_add,
        CRing.mul_neg R (w 1) lamR, R.mul_comm (w 1) lamR]
    exact e1.symm.trans (h1.trans e2)
  -- λ·(−w₁) = 1 は非単元性に矛盾
  exact hnu (R.neg (w 1)) (by
    rw [CRing.mul_neg R lamR (w 1)]
    exact h1'.symm)

/-! ## 塔への instance -/

/-- **定理 (M119-5a): 一段昇りの非零性** — λₙ が正則なら
    λₙ₊₁ ≠ 0（非単元性は M111 が無条件供給）。 -/
theorem tower_lam_step_ne_zero (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (hreg : IsRegularElem (towerLevel p n).ring (towerLevel p n).lam) :
    (towerLevel p (n + 1)).lam ≠ (towerLevel p (n + 1)).ring.zero :=
  towerLam_ne_zero p hp (towerLevel p n).ring (towerLevel p n).pi
    (towerLevel p n).lam hreg (tower_lam_not_unit p hp n)

/-- **M119-5b: 基底形** — λ₁ = eisLambda の平明正則性から λ₂ ≠ 0
    （O₁ = eisRing への読み替えは定義から defeq）。 -/
theorem tower_lam_one_ne_zero_of_base (p : Nat) (hp : 2 ≤ p)
    (hreg : IsRegularElem (eisRing p) (eisLambda p)) :
    (towerLevel p 1).lam ≠ (towerLevel p 1).ring.zero :=
  tower_lam_step_ne_zero p hp 0 hreg

/-! ## 総括 -/

/-- **M119-6a: 総括** — 塔の非零性の正則性への還元。 -/
structure TowerNonzeroData (p : Nat) (hp : 2 ≤ p) where
  /-- 一般環での非零性。 -/
  generic : ∀ (R : CRing) (piR lamR : R.carrier),
    IsRegularElem R lamR → (∀ v, R.mul lamR v ≠ R.one) →
    towerLam p R piR lamR ≠ (towerStep p R piR lamR).zero
  /-- 塔の一段昇り: λₙ 正則 ⟹ λₙ₊₁ ≠ 0。 -/
  step : ∀ n,
    IsRegularElem (towerLevel p n).ring (towerLevel p n).lam →
    (towerLevel p (n + 1)).lam ≠ (towerLevel p (n + 1)).ring.zero
  /-- 基底形: eisLambda の正則性 ⟹ λ₂ ≠ 0。 -/
  base : IsRegularElem (eisRing p) (eisLambda p) →
    (towerLevel p 1).lam ≠ (towerLevel p 1).ring.zero

/-- **M119-6b: witness**。 -/
def towerNonzeroData (p : Nat) (hp : 2 ≤ p) : TowerNonzeroData p hp where
  generic := fun R piR lamR hreg hnu =>
    towerLam_ne_zero p hp R piR lamR hreg hnu
  step := fun n hreg => tower_lam_step_ne_zero p hp n hreg
  base := fun hreg => tower_lam_one_ne_zero_of_base p hp hreg

/-- **M119-6c: 存在**。 -/
theorem towerNonzero_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (TowerNonzeroData p hp) :=
  ⟨towerNonzeroData p hp⟩

end IUT
