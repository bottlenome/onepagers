/-
  IUT/ThetaGauss.lean — M90（反復関数等式とガウス簿記: 柱E・E5）

  M89 の作用素 T（T(F) = q·u·F(q, qu)）を **j 回反復**し、
  T^j = q^{j(j+1)/2}·u^j·(u ↦ q^j u 代入) のガウス指数簿記を
  機械検証する。係数列 tCoeff（j 段の反復を構造的再帰で定義）
  に対し:

  (1) **反復関数等式** tCoeff j = (−1)^j Θ（M89 の theta_funeq_coeff
      を j 重否定 negPow ごしに帰納で持ち上げ）;
  (2) **ガウス簿記（代入の閉形式）**: 2m = 2i + 2jn − j(j−1) なら
      tCoeff j m n = Θ_i の u^{n−j} 係数 —— q-次数の降下
      m − i = jn − j(j−1)/2 が **u^j 対角（n = j）でちょうど
      j(j+1)/2** になる（IUT の捻れ値 q^{j²/2l} 系簿記の分母を
      払った形）。非線形の橋は gauss_bridge 一本に隔離;
  (3) **対角ガウス値**: 2m = j(j+1) のとき tCoeff j m (u^j) = 1
      （(−1)^j × (−1)^j = 1 — negPow_isgn）;
  (4) 級数（Quot）レベル: thetaIter の閉形式 T^{2k}(Θ) = Θ・
      T^{2k+1}(Θ) = −Θ。

  * M90-1 `negPow` / `negPow_neg` / `negPow_zero_val` — j 重否定
  * M90-2 `tCoeff` / `tCoeff_one` — T の j 回反復の係数列（M89 の
    tThetaRep と j = 1 で一致する検算込み）
  * M90-3 `tCoeff_eq` — **反復関数等式（本丸 1）** T^j(Θ) = (−1)^j Θ
  * M90-4 `gauss_bridge` / `tCoeff_shift` — **ガウス簿記（本丸 2）**
  * M90-5 `tGaussRep` / `thetaIter` / `thetaIter_even` / `thetaIter_odd`
    — 級数レベルの閉形式
  * M90-6 `negPow_isgn` / `theta_gauss` — 対角ガウス値 = 1

  Tate 点群 ℚ_p^×/q^ℤ（E6）・mono-theta witness（E7）は次層。
  全て選択公理不使用。
-/
import IUT.ThetaFunctional

namespace IUT

/-! ## j 重否定 -/

/-- **M90-1: j 重否定** negPow j x = (−1)^j x。 -/
def negPow (R : CRing) : Nat → R.carrier → R.carrier
  | 0, x => x
  | j + 1, x => R.neg (negPow R j x)

theorem negPow_neg (R : CRing) (j : Nat) (x : R.carrier) :
    negPow R j (R.neg x) = R.neg (negPow R j x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show R.neg (negPow R j (R.neg x)) = R.neg (R.neg (negPow R j x))
    rw [ih]

theorem negPow_zero_val (R : CRing) (j : Nat) :
    negPow R j R.zero = R.zero := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show R.neg (negPow R j R.zero) = R.zero
    rw [ih]
    exact (CRing.add_zero R (R.neg R.zero)).symm.trans (R.neg_add R.zero)

/-! ## T の j 回反復の係数列 -/

/-- **M90-2: T^j(Θ) の係数列**（j について構造的再帰 — 一段は
    M89 の tThetaRep と同じ係数公式）。 -/
def tCoeff (R : CRing) : Nat → Nat → Int → R.carrier
  | 0, m, n => (thetaRep R m).coeff n
  | j + 1, m, n => if n ≤ (m : Int)
      then tCoeff R j ((m : Int) - n).toNat (n - 1) else R.zero

/-- 検算: j = 1 は M89 の tThetaRep と一致。 -/
theorem tCoeff_one (R : CRing) (m : Nat) :
    tCoeff R 1 m = (tThetaRep R m).coeff :=
  funext fun _ => rfl

/-! ## 反復関数等式（本丸 1） -/

/-- **定理 (M90-3): 反復関数等式の係数形** — T^j(Θ) = (−1)^j Θ。
    M89 の theta_funeq_coeff を negPow ごしに j で帰納。 -/
theorem tCoeff_eq (R : CRing) :
    ∀ j m (n : Int), tCoeff R j m n = negPow R j ((thetaRep R m).coeff n) := by
  intro j
  induction j with
  | zero => intro m n; rfl
  | succ j ih =>
    intro m n
    show (if n ≤ (m : Int)
        then tCoeff R j ((m : Int) - n).toNat (n - 1) else R.zero)
      = R.neg (negPow R j ((thetaRep R m).coeff n))
    have hpt : (if n ≤ (m : Int)
        then (thetaRep R ((m : Int) - n).toNat).coeff (n - 1) else R.zero)
      = R.neg ((thetaRep R m).coeff n) := congrFun (theta_funeq_coeff R m) n
    cases Int.decLe n (m : Int) with
    | isTrue h =>
      rw [if_pos h] at hpt
      rw [if_pos h, ih (((m : Int) - n).toNat) (n - 1), hpt, negPow_neg]
    | isFalse h =>
      have hz : (thetaRep R m).coeff n = R.zero :=
        if_neg (fun hc => h (tri_le m n hc))
      rw [if_neg h, hz, negPow_zero_val]
      exact ((CRing.add_zero R (R.neg R.zero)).symm.trans (R.neg_add R.zero)).symm

/-! ## ガウス簿記（本丸 2） -/

/-- **M90-4a: 非線形の橋** — (n−d)(n−d+1) + 2dn − d(d−1) = n(n+1)。 -/
theorem gauss_bridge (d n : Int) :
    (n - d) * (n - d + 1) + 2 * (d * n) - d * (d - 1) = n * (n + 1) := by
  have e1 : (n - d) * (n - d + 1) = (n - d) * (n - d) + (n - d) := by
    rw [Int.mul_add, Int.mul_one]
  have e2 : (n - d) * (n - d) = n * (n - d) - d * (n - d) :=
    Int.sub_mul n d (n - d)
  have e3 : n * (n - d) = n * n - n * d := Int.mul_sub n n d
  have e4 : d * (n - d) = d * n - d * d := Int.mul_sub d n d
  have e5 : d * (d - 1) = d * d - d := by rw [Int.mul_sub, Int.mul_one]
  have e6 : n * (n + 1) = n * n + n := by rw [Int.mul_add, Int.mul_one]
  have e7 : n * d = d * n := Int.mul_comm n d
  omega

/-- **定理 (M90-4b): ガウス簿記（代入の閉形式）** —
    2m = 2i + 2jn − j(j−1)（分母を払った q-次数の降下式）なら
    T^j(Θ)_m の uⁿ 係数 = Θ_i の u^{n−j} 係数。u^j 対角（n = j）で
    降下量は m − i = j(j+1)/2: **ガウス指数の機械検証**。 -/
theorem tCoeff_shift (R : CRing) :
    ∀ (j : Nat) (m i : Nat) (n : Int),
      2 * (m : Int) = 2 * (i : Int) + 2 * ((j : Int) * n)
        - (j : Int) * ((j : Int) - 1) →
      tCoeff R j m n = (thetaRep R i).coeff (n - (j : Int)) := by
  intro j
  induction j with
  | zero =>
    intro m i n h
    have hmi : m = i := by omega
    subst hmi
    exact congrArg (thetaRep R m).coeff (by omega)
  | succ j ih =>
    intro m i n h
    have hc1 : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
    rw [hc1] at h ⊢
    show (if n ≤ (m : Int)
        then tCoeff R j ((m : Int) - n).toNat (n - 1) else R.zero)
      = (thetaRep R i).coeff (n - ((j : Int) + 1))
    cases Int.decLe n (m : Int) with
    | isTrue h' =>
      -- h を原子 (j:Int)*n, (j:Int)*(j:Int) の線形式に展開
      have e2 : (j : Int) + 1 - 1 = (j : Int) := by omega
      rw [e2] at h
      have e1 : ((j : Int) + 1) * n = (j : Int) * n + n := by
        rw [Int.add_mul, Int.one_mul]
      have e3 : ((j : Int) + 1) * (j : Int) = (j : Int) * (j : Int) + (j : Int) := by
        rw [Int.add_mul, Int.one_mul]
      rw [e1, e3] at h
      have hcast : ((((m : Int) - n).toNat : Nat) : Int) = (m : Int) - n :=
        Int.toNat_of_nonneg (by omega)
      have e5 : (j : Int) * (n - 1) = (j : Int) * n - (j : Int) := by
        rw [Int.mul_sub, Int.mul_one]
      have e4 : (j : Int) * ((j : Int) - 1) = (j : Int) * (j : Int) - (j : Int) := by
        rw [Int.mul_sub, Int.mul_one]
      have hIH : 2 * ((((m : Int) - n).toNat : Nat) : Int)
          = 2 * (i : Int) + 2 * ((j : Int) * (n - 1))
            - (j : Int) * ((j : Int) - 1) := by
        rw [hcast, e5, e4]
        omega
      rw [if_pos h', ih (((m : Int) - n).toNat) i (n - 1) hIH]
      exact congrArg (thetaRep R i).coeff (by omega)
    | isFalse h' =>
      rw [if_neg h']
      show R.zero = (if 2 * (i : Int)
          = (n - ((j : Int) + 1)) * (n - ((j : Int) + 1) + 1)
        then isgn R (n - ((j : Int) + 1)) else R.zero)
      refine (if_neg fun hc => h' ?_).symm
      have hb := gauss_bridge ((j : Int) + 1) n
      exact tri_le m n (by omega)

/-! ## 級数（Quot）レベルの閉形式 -/

/-- **M90-5a: T^j(Θ) の有界台表現** — 台は Θ と同一（反復関数等式
    より係数は符号しか変わらない）。 -/
def tGaussRep (R : CRing) (j m : Nat) : LRep R where
  coeff := tCoeff R j m
  bnd := 2 * m + 1
  supp := fun n hn => by
    rw [tCoeff_eq R j m n, (thetaRep R m).supp n hn]
    exact negPow_zero_val R j

/-- **M90-5b: 級数レベルの反復列** T^j(Θ) ∈ R[u^{±1}][[q]]。 -/
def thetaIter (R : CRing) (j : Nat) : PS (laurentRing R) :=
  fun m => Quot.mk (laurentRel R) (tGaussRep R j m)

theorem thetaIter_zero (R : CRing) : thetaIter R 0 = theta R := by
  funext m
  exact Quot.sound (funext fun _ => rfl)

/-- **定理 (M90-5c): 一段 = M89 の関数等式** —
    T^{j+1}(Θ) = −T^j(Θ)（級数レベル）。 -/
theorem thetaIter_succ (R : CRing) (j : Nat) :
    thetaIter R (j + 1) = psNeg (laurentRing R) (thetaIter R j) := by
  funext m
  refine Quot.sound (funext fun n => ?_)
  show tCoeff R (j + 1) m n = R.neg (tCoeff R j m n)
  rw [tCoeff_eq R (j + 1) m n, tCoeff_eq R j m n]
  rfl

/-- **定理 (M90-5d): 偶数回で復元** T^{2k}(Θ) = Θ。 -/
theorem thetaIter_even (R : CRing) : ∀ k, thetaIter R (2 * k) = theta R := by
  intro k
  induction k with
  | zero => exact thetaIter_zero R
  | succ k ih =>
    have h1 := thetaIter_succ R (2 * k + 1)
    have h2 := thetaIter_succ R (2 * k)
    show thetaIter R (2 * k + 1 + 1) = theta R
    rw [h1, h2, ih]
    funext m
    exact CRing.neg_neg (laurentRing R) (theta R m)

/-- **定理 (M90-5e): 奇数回で反転** T^{2k+1}(Θ) = −Θ。 -/
theorem thetaIter_odd (R : CRing) (k : Nat) :
    thetaIter R (2 * k + 1) = psNeg (laurentRing R) (theta R) := by
  rw [thetaIter_succ R (2 * k), thetaIter_even R k]

/-! ## 対角ガウス値 -/

theorem negPow_isgn (R : CRing) :
    ∀ j : Nat, negPow R j (isgn R (j : Int)) = R.one := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    show R.neg (negPow R j (isgn R ((j + 1 : Nat) : Int))) = R.one
    have hc : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
    rw [hc, isgn_succ R ((j : Int)), negPow_neg, CRing.neg_neg R, ih]

/-- **定理 (M90-6): 対角ガウス値 = 1** — 2m = j(j+1)（u^j 対角 =
    ガウス点）のとき T^j(Θ)_m の u^j 係数 = (−1)^j·(−1)^j = 1。
    捻れ値 q^{j(j+1)/2} の係数簿記の頂点。 -/
theorem theta_gauss (R : CRing) (j m : Nat)
    (h : 2 * (m : Int) = (j : Int) * ((j : Int) + 1)) :
    tCoeff R j m ((j : Int)) = R.one := by
  rw [tCoeff_eq R j m ((j : Int))]
  show negPow R j (if 2 * (m : Int) = (j : Int) * ((j : Int) + 1)
      then isgn R ((j : Int)) else R.zero) = R.one
  rw [if_pos h]
  exact negPow_isgn R j

end IUT
