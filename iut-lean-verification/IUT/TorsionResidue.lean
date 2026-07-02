/-
# M113F: 捻れ元は極大イデアルに入る — ρₙ(捻れ) = 0

M112F（TowerTorsion）の捻れ述語 IsTowerTorsion と M111（ResidueTower）の
剰余射 ρₙ : Oₙ → ℤ/p を統合する。鍵は「ρₙ(π) = 0 だから、ℤ/p では
LT 反復 [πᵏ] が単なる p^k 乗写像に退化する」こと: ℤ/p は零因子なし
（M103-2）なので x^{p^k} = 0 ⟹ x = 0、よって捻れ元の剰余像は 0。

  * M113F-1 `rpow_rpow` — 冪の合成則 (t^a)^b = t^{ab}
  * M113F-2 `ringF_pi_zero` / `ringFIter_pi_zero` — π = 0 の環では
    f_π(t) = t^p、[πᵏ]t = t^{p^k}（LT 作用の剰余体での退化）
  * M113F-3 `one_le_pow` / `zmod_rpow_eq_zero` — ℤ/p は被約:
    x^m = 0 (m ≥ 1) ⟹ x = 0（零因子なしの帰納）
  * M113F-4 `towerTorsion_res_zero` — **本丸**: 捻れ元 t ∈ Λₖ は
    剰余射の核に入る ρₙ(t) = 0
  * M113F-5 `towerTorsion_not_unit` — 従って捻れ元は非単元
    （t·v = 1 なら ℤ/p で 0 = 1 となり矛盾）
  * M113F-6 `TorsionResidueData` / `torsionResidueData` /
    `torsionResidue_exists` — 総括レコードと witness・存在定理

意義: 捻れ元（Λₙ の元）は剰余射の核に入り、したがって全て非単元。
塔の捻れ加群が極大イデアル内にあることの形式化。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.ResidueTower
import IUT.TowerTorsion
import IUT.PrimitiveRoot
import IUT.EisensteinUpper

namespace IUT

/-! ## 冪の合成則 -/

/-- **定理 (M113F-1): 冪の合成則** (t^a)^b = t^{ab}
    （b の帰納 + 指数加法則 rpow_add）。 -/
theorem rpow_rpow (R : CRing) (t : R.carrier) (a : Nat) :
    ∀ b, rpow R (rpow R t a) b = rpow R t (a * b) := by
  intro b
  induction b with
  | zero =>
    rw [Nat.mul_zero]
    rfl
  | succ b ih =>
    show R.mul (rpow R (rpow R t a) b) (rpow R t a) = rpow R t (a * (b + 1))
    rw [ih, Nat.mul_succ]
    exact (rpow_add R t (a * b) a).symm

/-! ## π = 0 の環での LT 作用の退化 -/

/-- **M113F-2a: π = 0 なら f_π(t) = t^p** — f_π(t) = π·t + t^p の
    第一項が消える。 -/
theorem ringF_pi_zero (p : Nat) (R : CRing) (t : R.carrier) :
    ringF p R R.zero t = rpow R t p := by
  show R.add (R.mul R.zero t) (rpow R t p) = rpow R t p
  rw [CRing.zero_mul R t]
  exact R.zero_add (rpow R t p)

/-- **定理 (M113F-2b): π = 0 なら [πᵏ]t = t^{p^k}** — LT 反復は
    剰余体上では p^k 乗写像に退化する（k の帰納 + M113F-1/2a）。 -/
theorem ringFIter_pi_zero (p : Nat) (R : CRing) :
    ∀ (k : Nat) (t : R.carrier),
    ringFIter p R R.zero k t = rpow R t (p ^ k) := by
  intro k
  induction k with
  | zero =>
    intro t
    rw [Nat.pow_zero]
    exact (R.one_mul t).symm
  | succ k ih =>
    intro t
    show ringFIter p R R.zero k (ringF p R R.zero t) = rpow R t (p ^ (k + 1))
    rw [ih (ringF p R R.zero t), ringF_pi_zero p R t,
      rpow_rpow R t p (p ^ k),
      show p * p ^ k = p ^ (k + 1) from by
        rw [Nat.pow_succ]; exact Nat.mul_comm p (p ^ k)]

/-! ## ℤ/p は被約: 冪零元は 0 のみ -/

/-- **M113F-3a: 1 ≤ p ⟹ 1 ≤ p^k**（k の帰納、選択公理回避のため
    自作）。 -/
theorem one_le_pow (p : Nat) (hp : 1 ≤ p) : ∀ k, 1 ≤ p ^ k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
    rw [Nat.pow_succ]
    have h := Nat.mul_le_mul ih hp
    omega

/-- **定理 (M113F-3b): ℤ/p は被約** — x^m = 0 (m ≥ 1) ⟹ x = 0
    （零因子なし zmod_no_zero_div の m 帰納。m = 1 の境界では
    x^0 = 1 ≠ 0 を使う）。 -/
theorem zmod_rpow_eq_zero (l : Nat) (hl : IsPrime l) :
    ∀ (m : Nat) (x : (zmodRing (l ^ 1)).carrier), 1 ≤ m →
    rpow (zmodRing (l ^ 1)) x m = (zmodRing (l ^ 1)).zero →
    x = (zmodRing (l ^ 1)).zero := by
  intro m
  induction m with
  | zero =>
    intro x h _
    exact absurd h (by omega)
  | succ m ih =>
    intro x _ hh
    have hmul : (zmodRing (l ^ 1)).mul (rpow (zmodRing (l ^ 1)) x m) x
        = (zmodRing (l ^ 1)).zero := hh
    cases zmod_no_zero_div l hl (rpow (zmodRing (l ^ 1)) x m) x hmul with
    | inr h2 => exact h2
    | inl h1 =>
      cases m with
      | zero =>
        exact absurd h1 (zmod_one_ne_zero (l ^ 1)
          (two_le_pow l hl.1 1 (Nat.le_refl 1)))
      | succ m' =>
        exact ih x (by omega) h1

/-! ## 本丸: 捻れ元は剰余射の核に入る -/

/-- **定理 (M113F-4): 捻れ元の剰余像は 0（本丸）** — t ∈ Λₖ なら
    ρₙ(t) = 0。証明: 剰余射は捻れを運ぶ（M112F-3e）ので
    [ρ(π)ᵏ](ρ(t)) = 0。ρ(π) = 0（M111-6）だから左辺は ρ(t)^{p^k}
    （M113F-2b）、ℤ/p の被約性（M113F-3b）で ρ(t) = 0。 -/
theorem towerTorsion_res_zero (p : Nat) (hp : IsPrime p) (n k : Nat)
    (t : (towerLevel p n).ring.carrier)
    (ht : IsTowerTorsion p (towerLevel p n).ring (towerLevel p n).pi k t) :
    (towerRes p hp.1 n).res.map t = (zmodRing (p ^ 1)).zero := by
  have h1 : IsTowerTorsion p (zmodRing (p ^ 1))
      ((towerRes p hp.1 n).res.map (towerLevel p n).pi) k
      ((towerRes p hp.1 n).res.map t) :=
    towerTorsion_hom p (towerRes p hp.1 n).res (towerLevel p n).pi ht
  rw [(towerRes p hp.1 n).res_pi] at h1
  have h2 : rpow (zmodRing (p ^ 1)) ((towerRes p hp.1 n).res.map t) (p ^ k)
      = (zmodRing (p ^ 1)).zero :=
    (ringFIter_pi_zero p (zmodRing (p ^ 1)) k
      ((towerRes p hp.1 n).res.map t)).symm.trans h1
  exact zmod_rpow_eq_zero p hp (p ^ k) ((towerRes p hp.1 n).res.map t)
    (one_le_pow p (Nat.le_of_succ_le hp.1) k) h2

/-! ## 捻れ元は非単元 -/

/-- **定理 (M113F-5): 捻れ元は単元でない** — t ∈ Λₖ、t·v = 1 なら
    剰余射で 0·ρ(v) = 1 in ℤ/p となり 1 ≠ 0 に矛盾
    （M111-8b tower_lam_not_unit と同じ論法 + M113F-4）。 -/
theorem towerTorsion_not_unit (p : Nat) (hp : IsPrime p) (n k : Nat)
    (t v : (towerLevel p n).ring.carrier)
    (ht : IsTowerTorsion p (towerLevel p n).ring (towerLevel p n).pi k t) :
    (towerLevel p n).ring.mul t v ≠ (towerLevel p n).ring.one := by
  intro h
  have h1 := congrArg (towerRes p hp.1 n).res.map h
  rw [(towerRes p hp.1 n).res.map_mul,
    towerTorsion_res_zero p hp n k t ht,
    CRing.zero_mul (zmodRing (p ^ 1)),
    (towerRes p hp.1 n).res.map_one] at h1
  exact zmod_one_ne_zero (p ^ 1) (two_le_pow p hp.1 1 (Nat.le_refl 1))
    h1.symm

/-! ## 総括 -/

/-- **M113F-6a: 総括** — 捻れ元は剰余射の核（極大イデアル）に入り、
    したがって全て非単元。 -/
structure TorsionResidueData (p : Nat) (hp : IsPrime p) where
  /-- 捻れ元の剰余像は 0（M113F-4）。 -/
  res_zero : ∀ (n k : Nat) (t : (towerLevel p n).ring.carrier),
    IsTowerTorsion p (towerLevel p n).ring (towerLevel p n).pi k t →
    (towerRes p hp.1 n).res.map t = (zmodRing (p ^ 1)).zero
  /-- 捻れ元は単元でない（M113F-5）。 -/
  not_unit : ∀ (n k : Nat) (t v : (towerLevel p n).ring.carrier),
    IsTowerTorsion p (towerLevel p n).ring (towerLevel p n).pi k t →
    (towerLevel p n).ring.mul t v ≠ (towerLevel p n).ring.one

/-- **M113F-6b: witness**。 -/
def torsionResidueData (p : Nat) (hp : IsPrime p) :
    TorsionResidueData p hp where
  res_zero := fun n k t ht => towerTorsion_res_zero p hp n k t ht
  not_unit := fun n k t v ht => towerTorsion_not_unit p hp n k t v ht

/-- **M113F-6c: 存在**。 -/
theorem torsionResidue_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (TorsionResidueData p hp) :=
  ⟨torsionResidueData p hp⟩

end IUT
