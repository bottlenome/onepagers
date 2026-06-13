/-
  IUT/ThetaFunctional.lean — M89（テータの関数等式: 柱E・E4）

  **q·u·Θ(q, qu) = −Θ(q, u)** を完全証明する。代入 u ↦ qu は
  u^n q^j ↦ u^n q^{j+n} で、(qu)-倍込みの合成作用素
  T(F) := q·u·F(q, qu) は monomial を u^n q^j ↦ u^{n+1} q^{j+n+1}
  に送る。よって T(Θ) の q^m 係数の u^n 成分は Θ_{m−n} の
  u^{n−1} 係数（n ≤ m の範囲）であり、これを係数公式として
  **Θ 専用に直接定義**する（一般の係数列 F に対しては u の
  大負冪が F の高次 q 係数を呼び込むため LRep の一様 bound が
  取れない——Θ では三角数の台 tri_bound が両裾を切る）。

  関数等式の本体は**再添字化 n ↦ n−1 の一撃**: 三角数の橋
  n(n+1) = (n−1)n + 2n により条件 2(m−n) = (n−1)n ⟺ 2m = n(n+1)、
  符号は isgn_succ、ガードは tri_le（2m = n(n+1) ⟹ n ≤ m）で吸収。

  * M89-1 `tThetaRep` — 作用素 T = (qu)·(u ↦ qu 代入) の Θ への
    作用の係数公式（bound は三角数の台で証明、choice なし）
  * M89-2 `tri_step` / `tri_le` — 三角数の橋とガード
  * M89-3 `theta_funeq_coeff` / `theta_funeq` — **関数等式（本丸）**:
    T(Θ) = −Θ（係数レベル + 級数（Quot）レベル）

  T の一般 monomial 検算・捻れ値 q^{j²} 簿記（E5）は次層。
  全て選択公理不使用。
-/
import IUT.ThetaSeries
import IUT.LaurentMonomial

namespace IUT

/-! ## 三角数の橋 -/

/-- **M89-2a: 三角数の橋** n(n+1) = (n−1)n + 2n。 -/
theorem tri_step (n : Int) : n * (n + 1) = (n - 1) * n + 2 * n := by
  rw [Int.mul_add, Int.mul_one, Int.sub_mul, Int.one_mul]
  omega

/-- **M89-2b: ガード** — 2m = n(n+1) なら n ≤ m。 -/
theorem tri_le (m : Nat) (n : Int)
    (h : 2 * (m : Int) = n * (n + 1)) : n ≤ (m : Int) := by
  cases Int.lt_or_le n 1 with
  | inl hn => omega
  | inr hn =>
    have h1 : n * 2 ≤ n * (n + 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega

/-! ## 作用素 T = (qu)·(u ↦ qu 代入) の Θ への作用 -/

/-- **M89-1: T(Θ) の q^m 係数**（u^n 係数 = Θ_{m−n} の u^{n−1}
    係数、n ≤ m の範囲 — u^n q^j ↦ u^{n+1} q^{j+n+1} の逆読み）。
    bound 2m+2 は三角数の台 tri_bound で証明。 -/
def tThetaRep (R : CRing) (m : Nat) : LRep R where
  coeff := fun n => if n ≤ (m : Int)
    then (thetaRep R ((m : Int) - n).toNat).coeff (n - 1) else R.zero
  bnd := 2 * m + 2
  supp := fun n hn => by
    cases Int.decLe n (m : Int) with
    | isFalse h => exact if_neg h
    | isTrue h =>
      rw [if_pos h]
      show (if 2 * ((((m : Int) - n).toNat : Nat) : Int)
          = (n - 1) * ((n - 1) + 1) then isgn R (n - 1) else R.zero)
        = R.zero
      refine if_neg (fun hc => ?_)
      have hcast : ((((m : Int) - n).toNat : Nat) : Int) = (m : Int) - n :=
        Int.toNat_of_nonneg (by omega)
      rw [hcast, show (n - 1) + 1 = n by omega] at hc
      -- 2(m−n) = (n−1)n ⟹ 2m = n(n+1) ⟹ |n| ≤ 2m+1 < |n| で矛盾
      have hbridge : n * (n + 1) = (n - 1) * n + 2 * n := tri_step n
      have h2 : 2 * (m : Int) = n * (n + 1) := by omega
      have hbnd := tri_bound m n h2
      omega

/-! ## 関数等式（本丸） -/

/-- **定理 (M89-3a): 関数等式の係数形** — T(Θ)_m = −Θ_m。 -/
theorem theta_funeq_coeff (R : CRing) (m : Nat) :
    (tThetaRep R m).coeff = (lNeg R (thetaRep R m)).coeff := by
  funext n
  show (if n ≤ (m : Int)
      then (thetaRep R ((m : Int) - n).toNat).coeff (n - 1) else R.zero)
    = R.neg (if 2 * (m : Int) = n * (n + 1) then isgn R n else R.zero)
  have hneg0 : R.neg R.zero = R.zero :=
    (CRing.add_zero R (R.neg R.zero)).symm.trans (R.neg_add R.zero)
  cases Int.decLe n (m : Int) with
  | isFalse h =>
    -- n > m: 右辺の条件も成り立たない（tri_le の対偶）
    rw [if_neg h, if_neg (fun hc => h (tri_le m n hc)), hneg0]
  | isTrue h =>
    rw [if_pos h]
    show (if 2 * ((((m : Int) - n).toNat : Nat) : Int)
        = (n - 1) * ((n - 1) + 1) then isgn R (n - 1) else R.zero)
      = R.neg (if 2 * (m : Int) = n * (n + 1) then isgn R n else R.zero)
    have hcast : ((((m : Int) - n).toNat : Nat) : Int) = (m : Int) - n :=
      Int.toNat_of_nonneg (by omega)
    have hbridge : n * (n + 1) = (n - 1) * n + 2 * n := tri_step n
    cases Int.decEq (2 * (m : Int)) (n * (n + 1)) with
    | isTrue hc =>
      rw [if_pos (show 2 * ((((m : Int) - n).toNat : Nat) : Int)
          = (n - 1) * ((n - 1) + 1) from by
        rw [hcast, show (n - 1) + 1 = n by omega]
        omega),
        if_pos hc]
      -- isgn (n−1) = neg (isgn n)
      have hs := isgn_succ R (n - 1)
      rw [show (n - 1) + 1 = n by omega] at hs
      rw [hs, CRing.neg_neg R]
    | isFalse hc =>
      rw [if_neg (show ¬2 * ((((m : Int) - n).toNat : Nat) : Int)
          = (n - 1) * ((n - 1) + 1) from fun hcontra => by
        rw [hcast, show (n - 1) + 1 = n by omega] at hcontra
        exact hc (by omega)),
        if_neg hc, hneg0]

/-- **定理 (M89-3b): テータの関数等式** —
    q·u·Θ(q, qu) = −Θ(q, u)（級数レベル）。 -/
theorem theta_funeq (R : CRing) :
    (fun m => Quot.mk (laurentRel R) (tThetaRep R m))
      = psNeg (laurentRing R) (theta R) := by
  funext m
  exact Quot.sound (theta_funeq_coeff R m)

end IUT
