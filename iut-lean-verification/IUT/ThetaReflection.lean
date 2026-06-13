/-
  IUT/ThetaReflection.lean — M98（テータの反転対称性: 柱E）

  テータ係数の **u^n ↔ u^{-(n+1)} 反転対称性**を機械検証する。
  古典的テータ Θ(q,u) = Σ_n (−1)^n q^{n(n+1)/2} u^n の指数は
  n ↦ −(n+1) のもとで n(n+1)/2 を不変に保つ（三角数の中心対称
  n(n+1) = (−(n+1))(−(n+1)+1)）一方、符号 (−1)^n は反転する。
  よって**係数の反転 J(F)_n := F_{−(n+1)} は Θ 上で −Θ を与える**。

  M89 の関数等式 q·u·Θ(q,qu) = −Θ も −Θ を与えるので、両者は
  Θ 上で一致する——**反転作用素 J と (qu)-代入作用素 T は Θ 上で
  同一**（theta_refl_eq_funeq）。これはテータの自己双対性の係数版。
  J は反転作用素として対合（reflRep_involutive: J² = id）。

  * M98-1 `reflRep` / `reflRep_involutive` — 反転作用素と対合性
  * M98-2 `isgn_neg` / `isgn_neg_succ` — 符号の反転則
  * M98-3 `theta_refl_coeff` — **反転対称性（本丸、係数形）** J(Θ) = −Θ
  * M98-4 `thetaRefl` / `theta_refl` — 級数（Quot）レベル
  * M98-5 `theta_refl_eq_funeq` — **J = T on Θ**（M89 との合流）

  l-捻れ係数での反転（mod-l テータ群の ±-構造）は次層。
  全て選択公理不使用。
-/
import IUT.ThetaFunctional

namespace IUT

/-! ## 反転作用素 -/

/-- **M98-1a: 反転作用素** J(F) の u^n 係数 = F の u^{−(n+1)} 係数。 -/
def reflRep (R : CRing) (F : LRep R) : LRep R where
  coeff := fun k => F.coeff (-(k + 1))
  bnd := F.bnd + 1
  supp := fun k hk => F.supp (-(k + 1)) (by
    have hnat : (-(k + 1)).natAbs = (k + 1).natAbs := Int.natAbs_neg (k + 1)
    rw [hnat]
    omega)

/-- **M98-1b: 反転は対合** — J² = id（係数レベル）。 -/
theorem reflRep_involutive (R : CRing) (F : LRep R) :
    (reflRep R (reflRep R F)).coeff = F.coeff := by
  funext k
  show F.coeff (-(-(k + 1) + 1)) = F.coeff k
  exact congrArg F.coeff (by omega)

/-! ## 符号の反転則 -/

/-- **M98-2a: 符号は反転で不変**（natAbs しか見ない）。 -/
theorem isgn_neg (R : CRing) (n : Int) : isgn R (-n) = isgn R n := by
  show (if (-n).natAbs % 2 = 0 then R.one else R.neg R.one)
    = (if n.natAbs % 2 = 0 then R.one else R.neg R.one)
  rw [Int.natAbs_neg]

/-- **M98-2b: 反転後継の符号** — (−1)^{−(n+1)} = −(−1)^n。 -/
theorem isgn_neg_succ (R : CRing) (n : Int) :
    isgn R (-(n + 1)) = R.neg (isgn R n) :=
  (isgn_neg R (n + 1)).trans (isgn_succ R n)

/-! ## 反転対称性（本丸） -/

/-- **定理 (M98-3): 反転対称性の係数形** — J(Θ) = −Θ。
    三角数の中心対称 n(n+1) = (−(n+1))(−(n+1)+1) が台を保ち、
    符号の反転則 isgn_neg_succ が −1 を供給する。 -/
theorem theta_refl_coeff (R : CRing) (m : Nat) :
    (reflRep R (thetaRep R m)).coeff = (lNeg R (thetaRep R m)).coeff := by
  funext n
  show (if 2 * (m : Int) = (-(n + 1)) * ((-(n + 1)) + 1)
      then isgn R (-(n + 1)) else R.zero)
    = R.neg (if 2 * (m : Int) = n * (n + 1) then isgn R n else R.zero)
  have hneg0 : R.neg R.zero = R.zero :=
    (CRing.add_zero R (R.neg R.zero)).symm.trans (R.neg_add R.zero)
  have hcond : (-(n + 1)) * ((-(n + 1)) + 1) = n * (n + 1) := by
    have h1 : (-(n + 1)) + 1 = -n := by omega
    rw [h1, Int.neg_mul_neg, Int.mul_comm]
  rw [hcond]
  cases Int.decEq (2 * (m : Int)) (n * (n + 1)) with
  | isTrue h => rw [if_pos h, if_pos h, isgn_neg_succ]
  | isFalse h => rw [if_neg h, if_neg h, hneg0]

/-! ## 級数（Quot）レベル -/

/-- **M98-4a: 反転テータの級数** J(Θ) ∈ R[u^{±1}][[q]]。 -/
def thetaRefl (R : CRing) : PS (laurentRing R) :=
  fun m => Quot.mk (laurentRel R) (reflRep R (thetaRep R m))

/-- **定理 (M98-4b): 反転対称性（級数レベル）** — J(Θ) = −Θ。 -/
theorem theta_refl (R : CRing) :
    thetaRefl R = psNeg (laurentRing R) (theta R) := by
  funext m
  exact Quot.sound (theta_refl_coeff R m)

/-! ## M89 との合流 -/

/-- **定理 (M98-5): 反転作用素 = (qu)-代入作用素（Θ 上）** —
    係数反転 J と M89 の合成作用素 T は Θ 上で一致する
    （ともに −Θ を与える）。テータの自己双対性の係数版。 -/
theorem theta_refl_eq_funeq (R : CRing) (m : Nat) :
    (reflRep R (thetaRep R m)).coeff = (tThetaRep R m).coeff :=
  (theta_refl_coeff R m).trans (theta_funeq_coeff R m).symm

end IUT
