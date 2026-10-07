/-
# M144: λ の全レベル伝播 — 塔の非退化性の完結（柱B 本線）

第88〜89弾の 3 段リレー（M111 剰余塔 → M119 一段昇り → M122 座標
忠実性 = λ₂ ≠ 0 無条件）の**最終段**。M119 の正直申告
「λₙ の平明正則性が全レベルに伝播すれば λₙ ≠ 0 が全レベルで出る」
の伝播そのものを閉じる。

**鍵となる発見**: R[[Y]] で Y は**環の仮定なしに正則**（係数シフト）。
これにより λₙ 正則 ⟹ λₙ₊₁ 正則の一段昇りが座標理論なしで回る:

  h·Y = w·(πY + Y^p − λ) の 0 次係数 ⟹ w₀·λ = 0 ⟹ w₀ = 0（λ 正則）
  ⟹ w = Y·w'（シフト） ⟹ h·Y = Y·(w'·g) ⟹ h = w'·g（Y の正則性）
  ⟹ [h] = 0

  * M144-1 `rsum_tail_single` / `psMul_X_coeff_succ` — Y-乗算の
    係数シフト (h·Y)_{m+1} = h_m
  * M144-2 `psMul_shift_zero` — w₀ = 0 なら (w·g)_{m+1} = (w'·g)_m
  * M144-3 **`towerLam_regular_step`（本丸）** — λ 正則 ⟹
    Y mod (πY + Y^p − λ) が商環で正則
  * M144-4 `tower_lam_regular` — 基底 M122-7（eisLambda_regular）
    から全レベルへ帰納
  * M144-5 `regular_ne_zero` / **`tower_lam_ne_zero_all`（見出し）** —
    **∀ n, λₙ₊₁ ≠ 0**: Lubin–Tate 塔の全レベルの非退化性が
    公理仮定なしに成立（M122-8 の λ₂ ≠ 0 を全レベルに拡張）
  * M144-6 `LambdaPropagationData` — 総括

正直な限定: 本層が伝播させるのは正則性と非零性であり、λ-adic
付値（v(λₙ) = 1/(p−1)ⁿ 型の分岐簿記）や Oₙ の座標系
Oₙ ≅ O_{n−1}^{p-1} の忠実性（M122 の塔版）は次層。

全て選択公理不使用。
-/
import IUT.EisFaithful

namespace IUT

/-! ## M144-1: Y-乗算の係数シフト -/

/-- 末項以外が消える有限和は末項のみ。 -/
theorem rsum_tail_single (R : CRing) (f : Nat → R.carrier) : ∀ m,
    (∀ k, k < m → f k = R.zero) → rsum R f (m + 1) = f m := by
  intro m
  induction m with
  | zero =>
    intro _
    show R.add R.zero (f 0) = f 0
    rw [R.zero_add]
  | succ m ih =>
    intro h
    show R.add (rsum R f (m + 1)) (f (m + 1)) = f (m + 1)
    rw [ih (fun k hk => h k (by omega)), h m (by omega), R.zero_add]

/-- **定理 (M144-1): Y-乗算はシフト** — (h·Y)_{m+1} = h_m。
    Y の係数 (0,1,0,…) が Cauchy 積の m 番目だけを拾う。 -/
theorem psMul_X_coeff_succ (R : CRing) (h : PS R) (m : Nat) :
    psMul R h (psX R) (m + 1) = h m := by
  show rsum R (fun k => R.mul (h k) (psX R (m + 1 - k))) (m + 2) = h m
  have hlast : R.mul (h (m + 1)) (psX R (m + 1 - (m + 1))) = R.zero := by
    rw [show m + 1 - (m + 1) = 0 from by omega,
      show psX R 0 = R.zero from if_neg (by omega),
      R.mul_comm (h (m + 1)) R.zero, CRing.zero_mul R]
  have e1 : rsum R (fun k => R.mul (h k) (psX R (m + 1 - k))) (m + 2)
      = R.add (rsum R (fun k => R.mul (h k) (psX R (m + 1 - k))) (m + 1))
          (R.mul (h (m + 1)) (psX R (m + 1 - (m + 1)))) := rfl
  rw [e1, hlast, CRing.add_zero R,
    rsum_tail_single R _ m (fun k hk => by
      show R.mul (h k) (psX R (m + 1 - k)) = R.zero
      rw [show psX R (m + 1 - k) = R.zero from if_neg (by omega),
        R.mul_comm (h k) R.zero, CRing.zero_mul R]),
    show m + 1 - m = 1 from by omega,
    show psX R 1 = R.one from if_pos rfl,
    R.mul_comm (h m) R.one, R.one_mul]

/-! ## M144-2: 先頭消滅のシフト -/

/-- **定理 (M144-2): 先頭が消える積のシフト** — w₀ = 0 なら
    (w·g)_{m+1} = (w'·g)_m（w' = シフト列）。rsum_head の頭出しで
    先頭項を落とし、添字を付け替える。 -/
theorem psMul_shift_zero (R : CRing) (w g : PS R) (hw0 : w 0 = R.zero)
    (m : Nat) :
    psMul R w g (m + 1)
      = psMul R (fun k => w (k + 1)) g m := by
  show rsum R (fun k => R.mul (w k) (g (m + 1 - k))) (m + 2)
    = rsum R (fun k => R.mul (w (k + 1)) (g (m - k))) (m + 1)
  rw [rsum_head R (fun k => R.mul (w k) (g (m + 1 - k))) (m + 1)]
  show R.add (R.mul (w 0) (g (m + 1 - 0)))
      (rsum R (fun k => R.mul (w (k + 1)) (g (m + 1 - (k + 1)))) (m + 1))
    = rsum R (fun k => R.mul (w (k + 1)) (g (m - k))) (m + 1)
  rw [hw0, CRing.zero_mul R, R.zero_add]
  apply rsum_congr
  intro k _
  show R.mul (w (k + 1)) (g (m + 1 - (k + 1)))
    = R.mul (w (k + 1)) (g (m - k))
  rw [show m + 1 - (k + 1) = m - k from by omega]

/-! ## M144-3: 一段昇りの正則性（本丸） -/

/-- **定理 (M144-3): 正則性の一段昇り（本丸）** — λ が R で正則なら
    λ' = Y mod (πY + Y^p − λ) は R[[Y]]/(…) で正則。
    h·Y ∈ (g) ⟹ 0 次で w₀λ = 0 ⟹ w₀ = 0 ⟹ w = Y·w'
    ⟹ h = w'·g ∈ (g)。環の整域性は一切使わない。 -/
theorem towerLam_regular_step (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (hreg : IsRegularElem R lamR) :
    IsRegularElem (towerStep p R piR lamR) (towerLam p R piR lamR) := by
  intro x hx
  induction x using Quot.ind; rename_i h
  have hx' : Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR))
      (psMul R h (psX R))
      = Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR))
        (psRing R).zero := hx
  obtain ⟨w, hw⟩ :=
    quot_exact_ideal (psRing R) (towerStepPoly p R piR lamR) hx'
  -- 係数抽出: (h·Y)_n = (w·g)_n
  have hco : ∀ n, psMul R h (psX R) n
      = psMul R w (towerStepPoly p R piR lamR) n := by
    intro n
    have e : R.add (psMul R h (psX R) n) (R.neg R.zero)
        = psMul R w (towerStepPoly p R piR lamR) n := congrFun hw n
    rw [CRing.neg_zero R, CRing.add_zero R] at e
    exact e
  -- 0 次: w₀·λ = 0 → w₀ = 0
  have hc0 := hco 0
  have hL : psMul R h (psX R) 0 = R.zero := by
    rw [psMul_coeff_zero R h (psX R),
      show psX R 0 = R.zero from if_neg (by omega),
      R.mul_comm (h 0) R.zero, CRing.zero_mul R]
  have hR : psMul R w (towerStepPoly p R piR lamR) 0
      = R.mul (w 0) (R.neg lamR) := by
    rw [psMul_coeff_zero R w (towerStepPoly p R piR lamR),
      towerStepPoly_coeff_zero p (by omega) R piR lamR]
  rw [hL, hR] at hc0
  have hw0 : w 0 = R.zero := by
    apply hreg (w 0)
    have h3 : R.neg (R.mul (w 0) lamR) = R.zero := by
      rw [← CRing.mul_neg R (w 0) lamR]
      exact hc0.symm
    exact neg_eq_zero_iff R h3
  -- 全係数: h_m = (w'·g)_m
  have hkey : ∀ m, h m
      = psMul R (fun k => w (k + 1)) (towerStepPoly p R piR lamR) m := by
    intro m
    have e2 := hco (m + 1)
    rw [psMul_X_coeff_succ R h m,
      psMul_shift_zero R w (towerStepPoly p R piR lamR) hw0 m] at e2
    exact e2
  -- 商で [h] = 0
  show Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR)) h
    = Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR))
      (psRing R).zero
  apply Quot.sound
  refine ⟨fun k => w (k + 1), ?_⟩
  funext n
  show R.add (h n) (R.neg R.zero)
    = psMul R (fun k => w (k + 1)) (towerStepPoly p R piR lamR) n
  rw [CRing.neg_zero R, CRing.add_zero R]
  exact hkey n

/-! ## M144-4: 全レベルへの帰納 -/

/-- **定理 (M144-4): λ の全レベル正則性** — 基底 M122-7
    （eisLambda_regular、座標忠実性経由）+ M144-3 の帰納。 -/
theorem tower_lam_regular (p : Nat) (hp : 2 ≤ p) : ∀ n,
    IsRegularElem (towerLevel p n).ring (towerLevel p n).lam := by
  intro n
  induction n with
  | zero => exact eisLambda_regular p hp
  | succ n ih =>
    exact towerLam_regular_step p hp (towerLevel p n).ring
      (towerLevel p n).pi (towerLevel p n).lam ih

/-! ## M144-5: 全レベル非零性（見出し） -/

/-- 非自明環の正則元は非零（1·a = 0 なら 1 = 0）。 -/
theorem regular_ne_zero (R : CRing) (hone : R.one ≠ R.zero)
    {a : R.carrier} (hreg : IsRegularElem R a) : a ≠ R.zero := by
  intro h0
  apply hone
  apply hreg R.one
  rw [h0, R.mul_comm R.one R.zero, CRing.zero_mul R]

/-- **定理 (M144-5): λₙ ≠ 0 の全レベル伝播（キャンペーン完結の
    見出し）** — Lubin–Tate 塔の全レベルで一意化元が非零。
    M111（非自明性・非単元性）× M122（基底の正則性）× M144-3
    （正則性の伝播）の合流。M122-8 の λ₂ ≠ 0 を ∀ n に拡張する。 -/
theorem tower_lam_ne_zero_all (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    (towerLevel p n).lam ≠ (towerLevel p n).ring.zero :=
  regular_ne_zero (towerLevel p n).ring (tower_one_ne_zero p hp n)
    (tower_lam_regular p hp n)

/-! ## M144-6: 総括 -/

/-- **M144-6a: 総括** — λ 伝播のデータ。 -/
structure LambdaPropagationData (p : Nat) (hp : 2 ≤ p) where
  /-- 一段昇りの正則性（一般環）。 -/
  step_regular : ∀ (R : CRing) (piR lamR : R.carrier),
    IsRegularElem R lamR →
    IsRegularElem (towerStep p R piR lamR) (towerLam p R piR lamR)
  /-- 全レベルの正則性。 -/
  all_regular : ∀ n,
    IsRegularElem (towerLevel p n).ring (towerLevel p n).lam
  /-- 全レベルの非零性。 -/
  all_ne_zero : ∀ n,
    (towerLevel p n).lam ≠ (towerLevel p n).ring.zero

/-- **M144-6b: witness**。 -/
def lambdaPropagationData (p : Nat) (hp : 2 ≤ p) :
    LambdaPropagationData p hp where
  step_regular := fun R piR lamR hreg =>
    towerLam_regular_step p hp R piR lamR hreg
  all_regular := tower_lam_regular p hp
  all_ne_zero := tower_lam_ne_zero_all p hp

/-- **M144-6c: 存在**。 -/
theorem lambdaPropagation_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaPropagationData p hp) :=
  ⟨lambdaPropagationData p hp⟩

end IUT
