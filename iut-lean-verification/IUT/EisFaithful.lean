/-
# M122: 座標忠実性 — Weierstrass 割り算と λ の平明正則性

M93F の簡約係数写像 c_i : O → ℤ_p（i < p−1）の**単射性**を、
Eisenstein 多項式 E = X^{p−1} + π による **Weierstrass 割り算**
f = q·E + r（r = Σ_{i<p−1} c_i(f) X^i）の明示構成で証明する。
商の係数は q_k = Σ_j (−π)^j f_{k+(j+1)(p−1)} — M93F と同じ
レベル打ち切り機構で ℤ_p 元として安定化する（eisCoeffStab）。

帰結（本キャンペーンの要）:
  * **λ の平明正則性** IsRegularElem O λ（∀h, hλ = 0 → h = 0）—
    witness 形整域性（M91F/M93F/M96F）では届かなかった選言なしの形
  * M119 と合成して **λ₂ ≠ 0 が無条件に成立**（tower_lam_two_ne_zero）

  * M122-1 `eisCoeffZp_val_stable` — 打ち切り安定性（余分な項は
    (−π)^j の p 進消滅で死ぬ）
  * M122-2 `eisCoeffStab` — 安定化された簡約係数（ℤ_p 元）
  * M122-3 `eisCoeffStab_rec` / `eisCoeffStab_solve` — 係数再帰
    c_k = f_k + (−π)·c_{k+(p−1)} とその解 f_k = c_{k+(p−1)}·π + c_k
  * M122-4 `eisDivQ`/`eisDivR`/`weierstrass_division` — 割り算
    f = q·E + r（係数ごとの検証、psMul_eisPoly_low/high）
  * M122-5 `eisCoeff_faithful` — **単射性（本丸）**: 全簡約係数が
    全レベルで 0 なら x = 0
  * M122-6 `zp_pi_regular` — π の平明正則性（p_mul_val_zero の束）
  * M122-7 `eisLambda_regular` — **λ の平明正則性**（シフト簿記
    M93F-2a/2b で λx = 0 から全係数消滅へ）
  * M122-8 `tower_lam_two_ne_zero` — **λ₂ ≠ 0（無条件）**
  * M122-9 `EisFaithfulData` — 総括

正直な限定: 高レベル λₙ (n ≥ 2) の正則性（→ λₙ₊₁ ≠ 0 の伝播）は
各レベルの座標理論（本層の塔版）として次層。

全て選択公理不使用。
-/
import IUT.EisDomain
import IUT.TowerNonzero

namespace IUT

/-! ## 打ち切り安定性 -/

/-- **M122-1: 打ち切り安定性** — レベル i の射影は i 項以降の
    打ち切りに依らない（追加項は (−π)^j, j ≥ i で消滅）。 -/
theorem eisCoeffZp_val_stable (p : Nat) (f : PS (zpRing p)) (k : Nat) :
    ∀ (j : Nat) {i : Nat}, i ≤ j →
    (eisCoeffZp p f k j).val i = (eisCoeffZp p f k i).val i := by
  intro j
  induction j with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    rw [this]
  | succ j ih =>
    intro i hi
    cases Nat.lt_or_ge i (j + 1) with
    | inl hlt =>
      have hij : i ≤ j := by omega
      show ((zpRing p).add (eisCoeffZp p f k j)
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
            (f (k + j * (p - 1))))).val i
        = (eisCoeffZp p f k i).val i
      show (zmodRing (p ^ i)).add ((eisCoeffZp p f k j).val i)
          (((zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
            (f (k + j * (p - 1)))).val i)
        = (eisCoeffZp p f k i).val i
      rw [val_negPiPow_mul p hij (f (k + j * (p - 1)))]
      show (zmodRing (p ^ i)).add ((eisCoeffZp p f k j).val i)
          (zmodRing (p ^ i)).zero = (eisCoeffZp p f k i).val i
      rw [CRing.add_zero (zmodRing (p ^ i))]
      exact ih hij
    | inr hge =>
      have : i = j + 1 := by omega
      rw [this]

/-! ## 安定化された簡約係数 -/

/-- **M122-2: 安定化簡約係数** c_k(f) = Σ_j (−π)^j f_{k+j(p−1)}
    （レベル n 成分 = n 打ち切りの n 射影、安定性が整合性を供給）。 -/
def eisCoeffStab (p : Nat) (f : PS (zpRing p)) (k : Nat) :
    (Zp p).carrier :=
  ⟨fun n => (eisCoeffZp p f k n).val n, by
    intro i j hij
    show (zmodTrans (pow_dvd_mono p hij)).map ((eisCoeffZp p f k j).val j)
      = (eisCoeffZp p f k i).val i
    rw [(eisCoeffZp p f k j).property hij]
    exact eisCoeffZp_val_stable p f k j hij⟩

/-! ## 係数再帰 -/

/-- 打ち切り (n+1) の頭剥がし: n+1 項和 = f_k + (−π)·(シフト n 項和)。 -/
theorem eisCoeffZp_head (p : Nat) (f : PS (zpRing p)) (k n : Nat) :
    eisCoeffZp p f k (n + 1)
      = (zpRing p).add (f k)
          ((zpRing p).mul (zpNegPi p) (eisCoeffZp p f (k + (p - 1)) n)) := by
  show rsum (zpRing p)
      (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
        (f (k + j * (p - 1)))) (n + 1)
    = (zpRing p).add (f k)
        ((zpRing p).mul (zpNegPi p) (eisCoeffZp p f (k + (p - 1)) n))
  rw [rsum_head (zpRing p) _ n]
  have h0 : (zpRing p).mul (rpow (zpRing p) (zpNegPi p) 0)
      (f (k + 0 * (p - 1))) = f k := by
    rw [show k + 0 * (p - 1) = k from by omega]
    exact (zpRing p).one_mul (f k)
  have hsh : rsum (zpRing p)
      (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) (j + 1))
        (f (k + (j + 1) * (p - 1)))) n
      = (zpRing p).mul (zpNegPi p) (eisCoeffZp p f (k + (p - 1)) n) := by
    have hcong : ∀ j, j < n →
        (zpRing p).mul (rpow (zpRing p) (zpNegPi p) (j + 1))
          (f (k + (j + 1) * (p - 1)))
        = (zpRing p).mul (zpNegPi p)
            ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
              (f ((k + (p - 1)) + j * (p - 1)))) := by
      intro j _
      have hidx : k + (j + 1) * (p - 1) = (k + (p - 1)) + j * (p - 1) := by
        have h1 : (j + 1) * (p - 1) = j * (p - 1) + (p - 1) := by
          rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [hidx]
      show (zpRing p).mul
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) j) (zpNegPi p))
          (f ((k + (p - 1)) + j * (p - 1)))
        = (zpRing p).mul (zpNegPi p)
            ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
              (f ((k + (p - 1)) + j * (p - 1))))
      rw [(zpRing p).mul_comm (rpow (zpRing p) (zpNegPi p) j) (zpNegPi p),
        (zpRing p).mul_assoc]
    rw [rsum_congr (zpRing p) n hcong,
      ← rsum_mul_left (zpRing p) _ (zpNegPi p) n]
    rfl
  rw [h0, hsh]

/-- **定理 (M122-3a): 係数再帰** c_k = f_k + (−π)·c_{k+(p−1)}
    （ℤ_p 元の等式 — レベルごとに頭剥がし + 打ち切り安定性）。 -/
theorem eisCoeffStab_rec (p : Nat) (f : PS (zpRing p)) (k : Nat) :
    eisCoeffStab p f k
      = (zpRing p).add (f k)
          ((zpRing p).mul (zpNegPi p) (eisCoeffStab p f (k + (p - 1)))) := by
  apply Subtype.ext
  funext n
  show (eisCoeffZp p f k n).val n
    = ((zpRing p).add (f k)
        ((zpRing p).mul (zpNegPi p) (eisCoeffStab p f (k + (p - 1))))).val n
  have h1 : (eisCoeffZp p f k n).val n
      = (eisCoeffZp p f k (n + 1)).val n :=
    (eisCoeffZp_val_stable p f k (n + 1) (Nat.le_succ n)).symm
  rw [h1, eisCoeffZp_head p f k n]
  show (zmodRing (p ^ n)).add ((f k).val n)
      (((zpRing p).mul (zpNegPi p) (eisCoeffZp p f (k + (p - 1)) n)).val n)
    = (zmodRing (p ^ n)).add ((f k).val n)
      (((zpRing p).mul (zpNegPi p) (eisCoeffStab p f (k + (p - 1)))).val n)
  show (zmodRing (p ^ n)).add ((f k).val n)
      ((zmodRing (p ^ n)).mul ((zpNegPi p).val n)
        ((eisCoeffZp p f (k + (p - 1)) n).val n))
    = (zmodRing (p ^ n)).add ((f k).val n)
      ((zmodRing (p ^ n)).mul ((zpNegPi p).val n)
        ((eisCoeffStab p f (k + (p - 1))).val n))
  rfl

/-- **M122-3b: 再帰の解** f_k = c_{k+(p−1)}·π + c_k
    （割り算の係数検証で使う形）。 -/
theorem eisCoeffStab_solve (p : Nat) (f : PS (zpRing p)) (k : Nat) :
    f k = (zpRing p).add
        ((zpRing p).mul (eisCoeffStab p f (k + (p - 1))) (zpPi p))
        (eisCoeffStab p f k) := by
  have h := eisCoeffStab_rec p f k
  have h2 : (zpRing p).add (eisCoeffStab p f k)
      ((zpRing p).neg ((zpRing p).mul (zpNegPi p)
        (eisCoeffStab p f (k + (p - 1))))) = f k := by
    rw [h, (zpRing p).add_assoc,
      CRing.add_neg (zpRing p)
        ((zpRing p).mul (zpNegPi p) (eisCoeffStab p f (k + (p - 1)))),
      CRing.add_zero (zpRing p)]
  have h3 : (zpRing p).neg ((zpRing p).mul (zpNegPi p)
        (eisCoeffStab p f (k + (p - 1))))
      = (zpRing p).mul (eisCoeffStab p f (k + (p - 1))) (zpPi p) := by
    show (zpRing p).neg ((zpRing p).mul ((zpRing p).neg (zpPi p))
        (eisCoeffStab p f (k + (p - 1))))
      = (zpRing p).mul (eisCoeffStab p f (k + (p - 1))) (zpPi p)
    rw [CRing.neg_mul (zpRing p) (zpPi p)
        (eisCoeffStab p f (k + (p - 1))),
      CRing.neg_neg (zpRing p),
      (zpRing p).mul_comm (zpPi p) (eisCoeffStab p f (k + (p - 1)))]
  rw [h3] at h2
  rw [← h2, (zpRing p).add_comm]

/-! ## Weierstrass 割り算 -/

/-- **M122-4a: 商** q_k = c_{k+(p−1)}(f)。 -/
def eisDivQ (p : Nat) (f : PS (zpRing p)) : PS (zpRing p) :=
  fun k => eisCoeffStab p f (k + (p - 1))

/-- **M122-4b: 余り** r = Σ_{i<p−1} c_i(f) X^i（次数 < p−1）。 -/
def eisDivR (p : Nat) (f : PS (zpRing p)) : PS (zpRing p) :=
  fun m => if m < p - 1 then eisCoeffStab p f m else (zpRing p).zero

/-- **定理 (M122-4c): Weierstrass 割り算** f = q·E + r
    （係数ごと: 低域は psMul_eisPoly_low、高域は …_high + 再帰の解）。 -/
theorem weierstrass_division (p : Nat) (hp : 2 ≤ p) (f : PS (zpRing p)) :
    f = psAdd (zpRing p)
        (psMul (zpRing p) (eisDivQ p f) (eisPoly p)) (eisDivR p f) := by
  funext m
  show f m = (zpRing p).add
      (psMul (zpRing p) (eisDivQ p f) (eisPoly p) m) (eisDivR p f m)
  cases Nat.lt_or_ge m (p - 1) with
  | inl hm =>
    rw [psMul_eisPoly_low p (eisDivQ p f) m hm,
      show eisDivR p f m = eisCoeffStab p f m from if_pos hm]
    exact eisCoeffStab_solve p f m
  | inr hm =>
    rw [psMul_eisPoly_high p hp (eisDivQ p f) m hm,
      show eisDivR p f m = (zpRing p).zero from if_neg (by omega),
      CRing.add_zero (zpRing p)]
    show f m = (zpRing p).add (eisCoeffStab p f ((m - (p - 1)) + (p - 1)))
        ((zpRing p).mul (eisCoeffStab p f (m + (p - 1))) (zpPi p))
    rw [show (m - (p - 1)) + (p - 1) = m from by omega,
      (zpRing p).add_comm]
    exact eisCoeffStab_solve p f m

/-! ## 単射性（本丸） -/

/-- 零級数の簡約係数は 0。 -/
theorem eisCoeffZp_zero_series (p : Nat) (i : Nat) : ∀ n,
    eisCoeffZp p (psZero (zpRing p)) i n = (zpRing p).zero := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (zpRing p).add (eisCoeffZp p (psZero (zpRing p)) i n)
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n) (zpRing p).zero)
      = (zpRing p).zero
    rw [ih, CRing.mul_zero (zpRing p), (zpRing p).zero_add]

/-- **定理 (M122-5): 座標忠実性（単射性・本丸）** — 全ての簡約係数が
    全レベルで消えるなら x = 0（Weierstrass 割り算で f = q·E）。 -/
theorem eisCoeff_faithful (p : Nat) (hp : 2 ≤ p) (x : EisCarrier p)
    (h : ∀ (i n : Nat) (hi : i < p - 1),
      eisCoeff p i n hi x = Quot.mk (modCong (p ^ n)).rel 0) :
    x = (eisRing p).zero := by
  induction x using Quot.ind; rename_i f
  have hstab : ∀ i, i < p - 1 →
      eisCoeffStab p f i = (zpRing p).zero := by
    intro i hi
    apply Subtype.ext
    funext n
    exact h i n hi
  have hr : eisDivR p f = psZero (zpRing p) := by
    funext m
    show (if m < p - 1 then eisCoeffStab p f m else (zpRing p).zero)
      = (zpRing p).zero
    cases Nat.lt_or_ge m (p - 1) with
    | inl hm => rw [if_pos hm]; exact hstab m hm
    | inr hm => exact if_neg (by omega)
  have hdiv := weierstrass_division p hp f
  rw [hr] at hdiv
  have hplus : psAdd (zpRing p)
      (psMul (zpRing p) (eisDivQ p f) (eisPoly p)) (psZero (zpRing p))
      = psMul (zpRing p) (eisDivQ p f) (eisPoly p) := by
    funext m
    exact CRing.add_zero (zpRing p)
      (psMul (zpRing p) (eisDivQ p f) (eisPoly p) m)
  have hf : f = psMul (zpRing p) (eisDivQ p f) (eisPoly p) :=
    hdiv.trans hplus
  apply Quot.sound
  refine ⟨eisDivQ p f, ?_⟩
  show psAdd (zpRing p) f (psNeg (zpRing p) (psZero (zpRing p)))
    = psMul (zpRing p) (eisDivQ p f) (eisPoly p)
  have hz : psAdd (zpRing p) f (psNeg (zpRing p) (psZero (zpRing p)))
      = f := by
    funext m
    show (zpRing p).add (f m) ((zpRing p).neg (zpRing p).zero) = f m
    rw [CRing.neg_zero (zpRing p), CRing.add_zero (zpRing p)]
  rw [hz]
  exact hf

/-! ## π と λ の平明正則性 -/

/-- **M122-6: π の平明正則性** — π·y = 0 なら y = 0
    （p_mul_val_zero の全レベル束）。 -/
theorem zp_pi_regular (p : Nat) (hp : 2 ≤ p) (y : (Zp p).carrier)
    (h : (zpRing p).mul (zpPi p) y = (zpRing p).zero) :
    y = (zpRing p).zero := by
  apply Subtype.ext
  funext n
  apply p_mul_val_zero p hp y n
  exact congrArg (fun z => z.val (n + 1)) h

/-- **定理 (M122-7): λ の平明正則性（本キャンペーンの要）** —
    x·λ = 0 なら x = 0。witness 形整域性では届かなかった選言なしの
    正則性が、座標忠実性 + シフト簿記（M93F-2a/2b）で閉じる。 -/
theorem eisLambda_regular (p : Nat) (hp : 2 ≤ p) :
    IsRegularElem (eisRing p) (eisLambda p) := by
  intro x hx
  have hlx : (eisRing p).mul (eisLambda p) x = (eisRing p).zero := by
    rw [(eisRing p).mul_comm]
    exact hx
  apply eisCoeff_faithful p hp x
  intro i n hi
  -- λx の全係数は 0
  have hcoeff : ∀ (i' n' : Nat) (hi' : i' < p - 1),
      eisCoeff p i' n' hi' ((eisRing p).mul (eisLambda p) x)
        = Quot.mk (modCong (p ^ n')).rel 0 := by
    intro i' n' hi'
    rw [hlx]
    show (eisCoeffZp p (psZero (zpRing p)) i' n').val n'
      = Quot.mk (modCong (p ^ n')).rel 0
    rw [eisCoeffZp_zero_series p i' n']
    rfl
  cases Nat.lt_or_ge i (p - 2) with
  | inl hi2 =>
    -- 域内: c_i(x) = c_{i+1}(λx) = 0
    have hshift := eisCoeff_lambda_mul p x i n (by omega)
    rw [hcoeff (i + 1) n (by omega)] at hshift
    exact hshift.symm
  | inr hi2 =>
    -- 巻き戻り: i = p−2、c₀(λx)@(n+1) = −π·c_{p−2}(x)@n
    have hieq : i = p - 2 := by omega
    induction x using Quot.ind; rename_i g
    -- λ·(mk g) = mk (X·g)
    have hwrap := eisCoeffZp_X_wrap p hp g n
    -- c₀(λx) のレベル n+1 射影は 0
    have hzero : (eisCoeffZp p
        (psMul (zpRing p) (psX (zpRing p)) g) 0 (n + 1)).val (n + 1)
        = Quot.mk (modCong (p ^ (n + 1))).rel 0 :=
      hcoeff 0 (n + 1) (by omega)
    rw [hwrap] at hzero
    -- (−π)·c = 0 at n+1 → π·c = 0 at n+1 → c = 0 at n
    have hneg : ((zpRing p).mul (zpPi p)
        (eisCoeffZp p g (p - 2) n)).val (n + 1)
        = Quot.mk (modCong (p ^ (n + 1))).rel 0 := by
      have e1 : (zpRing p).mul (zpNegPi p) (eisCoeffZp p g (p - 2) n)
          = (zpRing p).neg ((zpRing p).mul (zpPi p)
              (eisCoeffZp p g (p - 2) n)) :=
        CRing.neg_mul (zpRing p) (zpPi p) (eisCoeffZp p g (p - 2) n)
      rw [e1] at hzero
      have e2 : ((zpRing p).mul (zpPi p)
          (eisCoeffZp p g (p - 2) n))
          = (zpRing p).neg ((zpRing p).neg ((zpRing p).mul (zpPi p)
              (eisCoeffZp p g (p - 2) n))) :=
        (CRing.neg_neg (zpRing p) _).symm
      rw [e2]
      show ((zmodRing (p ^ (n + 1))).neg
          (((zpRing p).neg ((zpRing p).mul (zpPi p)
            (eisCoeffZp p g (p - 2) n))).val (n + 1)))
        = Quot.mk (modCong (p ^ (n + 1))).rel 0
      rw [hzero]
      apply Quot.sound
      show ((p ^ (n + 1) : Nat) : Int) ∣ -0 - 0
      exact ⟨0, by omega⟩
    have hc := p_mul_val_zero p hp (eisCoeffZp p g (p - 2) n) n hneg
    show (eisCoeffZp p g i n).val n = Quot.mk (modCong (p ^ n)).rel 0
    rw [hieq]
    exact hc

/-! ## 帰結: λ₂ ≠ 0（無条件） -/

/-- **定理 (M122-8): λ₂ ≠ 0 無条件** — λ の平明正則性（M122-7）を
    M119 の一段昇り定理に食わせる。塔の第二層の非自明性が公理仮定
    なしで成立。 -/
theorem tower_lam_two_ne_zero (p : Nat) (hp : 2 ≤ p) :
    (towerLevel p 1).lam ≠ (towerLevel p 1).ring.zero :=
  tower_lam_one_ne_zero_of_base p hp (eisLambda_regular p hp)

/-! ## 総括 -/

/-- **M122-9a: 総括** — 座標忠実性と平明正則性。 -/
structure EisFaithfulData (p : Nat) (hp : 2 ≤ p) where
  /-- Weierstrass 割り算 f = q·E + r。 -/
  division : ∀ f : PS (zpRing p),
    f = psAdd (zpRing p)
        (psMul (zpRing p) (eisDivQ p f) (eisPoly p)) (eisDivR p f)
  /-- 座標忠実性（単射性）。 -/
  faithful : ∀ (x : EisCarrier p),
    (∀ (i n : Nat) (hi : i < p - 1),
      eisCoeff p i n hi x = Quot.mk (modCong (p ^ n)).rel 0) →
    x = (eisRing p).zero
  /-- π の平明正則性。 -/
  pi_regular : ∀ y, (zpRing p).mul (zpPi p) y = (zpRing p).zero →
    y = (zpRing p).zero
  /-- λ の平明正則性。 -/
  lambda_regular : IsRegularElem (eisRing p) (eisLambda p)
  /-- λ₂ ≠ 0（無条件）。 -/
  lam_two_nonzero :
    (towerLevel p 1).lam ≠ (towerLevel p 1).ring.zero

/-- **M122-9b: witness**。 -/
def eisFaithfulData (p : Nat) (hp : 2 ≤ p) : EisFaithfulData p hp where
  division := weierstrass_division p hp
  faithful := eisCoeff_faithful p hp
  pi_regular := zp_pi_regular p hp
  lambda_regular := eisLambda_regular p hp
  lam_two_nonzero := tower_lam_two_ne_zero p hp

/-- **M122-9c: 存在**。 -/
theorem eisFaithful_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (EisFaithfulData p hp) :=
  ⟨eisFaithfulData p hp⟩

end IUT
