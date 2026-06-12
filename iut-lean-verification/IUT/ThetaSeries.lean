/-
  IUT/ThetaSeries.lean — M88（q-級数環とテータ級数: 柱E・E2+E3）

  * M88-1 `qLaurent R := psRing (laurentRing R)` — **q-級数環
    R[u^{±1}][[q]]**。psRing の一行適用で M39 以来の PS 理論
    （rsum 補題・psComp・psMap …）を**無償取得**（E2 完了）
  * M88-2 `isgn` — 符号 (−1)^n（n : Int、偶奇で定義）と反転則
  * M88-3 `tri_bound` — **三角数の台**: 2m = n(n+1) なら
    |n| ≤ 2m + 1（テータ係数の有界台の根拠。非線形部は
    Int.mul_le_mul_of_nonneg_left で処理）
  * M88-4 `thetaRep` / `theta` — **テータ級数の実構成**:
    Θ(q, u) = Σ_{n∈ℤ} (−1)^n q^{n(n+1)/2} u^n を「q^m の係数 =
    Σ_{2m = n(n+1)} (−1)^n u^n」として各係数が有界台 Laurent に
    なる形で定義（分母を払った 2m = n(n+1) 条件 = house style）
  * M88-5 `theta_zero_coeff` — 検算: Θ の q^0 係数 = 1 − u^{−1}
    （n = 0 と n = −1 の二点、古典的な先頭項）

  関数等式 q·u·Θ(q, qu) = −Θ(q, u)（E4）・捻れ値の q^{j²} 簿記
  （E5）は次層。全て選択公理不使用。
-/
import IUT.LaurentRing

namespace IUT

/-! ## q-級数環（E2） -/

/-- **M88-1: q-級数環** R[u^{±1}][[q]]。PS 理論を無償取得。 -/
def qLaurent (R : CRing) : CRing := psRing (laurentRing R)

/-! ## 符号と三角数 -/

/-- **M88-2: 符号** (−1)^n（n : Int、natAbs の偶奇 — 偶奇は
    natAbs で保たれる）。 -/
def isgn (R : CRing) (n : Int) : R.carrier :=
  if n.natAbs % 2 = 0 then R.one else R.neg R.one

theorem isgn_succ (R : CRing) (n : Int) :
    isgn R (n + 1) = R.neg (isgn R n) := by
  show (if (n + 1).natAbs % 2 = 0 then R.one else R.neg R.one)
    = R.neg (if n.natAbs % 2 = 0 then R.one else R.neg R.one)
  cases Nat.decEq (n.natAbs % 2) 0 with
  | isTrue h =>
    rw [if_pos h, if_neg (show ¬(n + 1).natAbs % 2 = 0 by omega)]
  | isFalse h =>
    rw [if_neg h, if_pos (show (n + 1).natAbs % 2 = 0 by omega),
      CRing.neg_neg R]

/-- **M88-3: 三角数の台** — 2m = n(n+1) なら |n| ≤ 2m + 1。 -/
theorem tri_bound (m : Nat) (n : Int)
    (h : 2 * (m : Int) = n * (n + 1)) : n.natAbs ≤ 2 * m + 1 := by
  cases Int.lt_or_le n 0 with
  | inr hpos =>
    -- n ≥ 0: n = n·1 ≤ n·(n+1) = 2m
    have h1 : n * 1 ≤ n * (n + 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hpos
    omega
  | inl hneg =>
    -- n ≤ −1: −n−1 = (−n−1)·1 ≤ (−n−1)·(−n) = n(n+1) = 2m
    have h1 : (-n - 1) * 1 ≤ (-n - 1) * (-n) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h2 : (-n - 1) * (-n) = n * (n + 1) := by
      rw [Int.sub_mul, Int.neg_mul_neg, Int.one_mul, Int.mul_add,
        Int.mul_one]
      omega
    omega

/-! ## テータ級数（E3） -/

/-- **M88-4a: テータ係数の有界台表現** — q^m の係数
    Σ_{2m = n(n+1)} (−1)^n u^n。 -/
def thetaRep (R : CRing) (m : Nat) : LRep R where
  coeff := fun n => if 2 * (m : Int) = n * (n + 1) then isgn R n
    else R.zero
  bnd := 2 * m + 1
  supp := fun n hn => if_neg (fun hc =>
    absurd (tri_bound m n hc) (by omega))

/-- **M88-4b: テータ級数の実構成** —
    Θ(q, u) = Σ_n (−1)^n q^{n(n+1)/2} u^n ∈ R[u^{±1}][[q]]。 -/
def theta (R : CRing) : PS (laurentRing R) :=
  fun m => Quot.mk (laurentRel R) (thetaRep R m)

/-! ## 検算: 先頭係数 -/

/-- **M88-5: Θ の q^0 係数 = 1 − u^{−1}**（n = 0 と n = −1 の二点）。 -/
theorem theta_zero_coeff (R : CRing) :
    (thetaRep R 0).coeff
      = (lAdd R (lOne R) (lNeg R (uMon R (-1)))).coeff := by
  funext n
  show (if 2 * ((0 : Nat) : Int) = n * (n + 1) then isgn R n
      else R.zero)
    = R.add (if n = 0 then R.one else R.zero)
        (R.neg (if n = -1 then R.one else R.zero))
  cases Int.decEq n 0 with
  | isTrue h0 =>
    subst h0
    rw [if_pos (by decide), if_pos rfl,
      if_neg (show (0 : Int) ≠ -1 by decide)]
    show isgn R 0 = R.add R.one (R.neg R.zero)
    rw [show isgn R 0 = R.one from if_pos rfl,
      show R.neg R.zero = R.zero from
        (CRing.add_zero R (R.neg R.zero)).symm.trans (R.neg_add R.zero)]
    exact (CRing.add_zero R R.one).symm
  | isFalse h0 =>
    cases Int.decEq n (-1) with
    | isTrue h1 =>
      subst h1
      rw [if_pos (by decide), if_neg h0, if_pos rfl]
      show isgn R (-1) = R.add R.zero (R.neg R.one)
      rw [show isgn R (-1) = R.neg R.one from
        if_neg (show ¬(-1 : Int).natAbs % 2 = 0 by decide)]
      exact (R.zero_add (R.neg R.one)).symm
    | isFalse h1 =>
      rw [if_neg (fun hc : 2 * ((0 : Nat) : Int) = n * (n + 1) => by
          have hz : n * (n + 1) = 0 := by omega
          cases Int.mul_eq_zero.mp hz with
          | inl h => exact h0 h
          | inr h => exact h1 (by omega)),
        if_neg h0, if_neg h1]
      rw [show R.neg R.zero = R.zero from
        (CRing.add_zero R (R.neg R.zero)).symm.trans (R.neg_add R.zero)]
      exact (R.zero_add R.zero).symm

end IUT
