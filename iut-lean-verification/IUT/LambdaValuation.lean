/-
# M151F: λ-adic 付値の階段 — イデアル膜 (λ^k) の厳密降下と値の井戸定義性

M146F（λₙ^k ≠ 0 の全レベル・全冪伝播）の直上に立つ柱B の一歩。
イデアル膜 (λ^k) の**厳密な階段**を証明し、「x の λ-adic 値 ≥ k」を
選言・choice なしの ∃-述語 `IsValAtLeast` として定式化、
**λ^j の所属レベルが冪指数 j を一意に切り出す**（v(λ^j) = j の
井戸定義性）ことを閉じる。

  * M151F-1 `IsValAtLeast` — イデアル (λ^k) 所属 = 「値 ≥ k」の
    ∃-述語（データなし Prop、choice 不使用）
  * M151F-2 `isValAtLeast_zero` — 全元は値 ≥ 0（(λ^0) = (1) = R）
  * M151F-3 `isValAtLeast_step` / `isValAtLeast_mono` — 膜の入れ子:
    値 ≥ k+1 なら値 ≥ k（(λ^{k+1}) ⊆ (λ^k)）、および単調降下
  * M151F-4 `lam_pow_self_val` / `lam_pow_val_le` — λ^j は値 ≥ j、
    より一般に k ≤ j なら λ^j ∈ (λ^k)
  * M151F-5 **`lam_pow_strict`（本丸）** — λ 正則・非単元なら
    **λ^k ∉ (λ^{k+1})**: 膜が各段で真に落ちる（厳密降下）
  * M151F-6 `lam_pow_val_exact` — **排他性**: λ^j ∈ (λ^k) ↔ k ≤ j。
    所属レベルの最大値が冪指数 j を一意に切り出す = v(λ^j) = j
  * M151F-7 **`tower_lam_staircase` / `tower_lam_val_exact`（見出し）**
    — **Lubin–Tate 塔の全レベルで λ-adic 値 v(λ^j) = j が井戸定義
    （イデアル膜の所属レベルが冪指数を一意に切り出す）**。
    M144（tower_lam_regular）× M111（tower_lam_not_unit）の合流
  * M151F-8 `LambdaValuationData` — 総括（nest・self・strict・exact）

意義: M146F の λₙ^k ≠ 0 を強化: 膜が各段で真に落ちる
（λ^k ∉ (λ^{k+1})）ので、λ-adic 値が ∃-述語の所属レベルとして
choice なしに定まる。付値の加法性 v(xy) = v(x)+v(y) は座標理論
（M147F の次層）を要し次層。

正直な限定: 本層が与えるのは λ の冪自身に対する値の井戸定義性
（階段の厳密性と排他性）であり、一般元 x への付値関数 v(x) の
全域的構成（min の実現）と加法性は次層。`lam_pow_val_exact` の
→ 側は指示書の直接計算（λ^j = λ^j·(h·λ^{k−j}) の正則簡約）と
同値な道筋として、`isValAtLeast_mono` の降下で k > j の仮定を
(j+1) 段まで下ろし `lam_pow_strict` に衝突させる形で閉じた
（同じ矛盾を部品の再利用で得る、選言なし）。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RegularPowers

namespace IUT

/-! ## M151F-1: λ-adic 値 ≥ k の ∃-述語 -/

/-- **M151F-1: 値 ≥ k の述語** — x がイデアル (λ^k) に属する、
    すなわち x = h·λ^k なる h が存在する。データなし Prop であり、
    選言も choice も使わない。 -/
def IsValAtLeast (R : CRing) (lam x : R.carrier) (k : Nat) : Prop :=
  ∃ h : R.carrier, x = R.mul h (rpow R lam k)

/-! ## M151F-2: 底段 — 全元は値 ≥ 0 -/

/-- **定理 (M151F-2): 全元は値 ≥ 0** — (λ^0) = (1) = R。
    witness は x 自身（x = x·1）。 -/
theorem isValAtLeast_zero (R : CRing) (lam x : R.carrier) :
    IsValAtLeast R lam x 0 :=
  ⟨x, by
    show x = R.mul x R.one
    rw [CRing.mul_one]⟩

/-! ## M151F-3: 膜の入れ子 — 値 ≥ k+1 → 値 ≥ k -/

/-- **定理 (M151F-3a): 膜の入れ子** — x = h·λ^{k+1} = h·(λ^k·λ)
    = (h·λ)·λ^k なので (λ^{k+1}) ⊆ (λ^k)。rpow の succ 展開は
    show で defeq 固定、mul_comm/mul_assoc の付け替え。 -/
theorem isValAtLeast_step (R : CRing) (lam x : R.carrier) (k : Nat) :
    IsValAtLeast R lam x (k + 1) → IsValAtLeast R lam x k := by
  intro hv
  obtain ⟨h, hx⟩ := hv
  refine ⟨R.mul h lam, ?_⟩
  rw [hx]
  show R.mul h (R.mul (rpow R lam k) lam)
      = R.mul (R.mul h lam) (rpow R lam k)
  rw [R.mul_comm (rpow R lam k) lam, ← R.mul_assoc]

/-- **定理 (M151F-3b): 単調降下** — 値 ≥ k なら任意の m ≤ k で
    値 ≥ m（M151F-3a の反復、k の帰納）。 -/
theorem isValAtLeast_mono (R : CRing) (lam x : R.carrier) :
    ∀ k m, m ≤ k → IsValAtLeast R lam x k → IsValAtLeast R lam x m := by
  intro k
  induction k with
  | zero =>
    intro m hm hv
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    rw [hm0]
    exact hv
  | succ k ih =>
    intro m hm hv
    cases Nat.lt_or_ge m (k + 1) with
    | inl hlt =>
      exact ih m (Nat.le_of_lt_succ hlt)
        (isValAtLeast_step R lam x k hv)
    | inr hge =>
      have hm1 : m = k + 1 := Nat.le_antisymm hm hge
      rw [hm1]
      exact hv

/-! ## M151F-4: λ^j の所属 — 値 ≥ j（および k ≤ j 側全部） -/

/-- **定理 (M151F-4a): λ^j は値 ≥ j** — witness は 1（λ^j = 1·λ^j）。 -/
theorem lam_pow_self_val (R : CRing) (lam : R.carrier) (j : Nat) :
    IsValAtLeast R lam (rpow R lam j) j :=
  ⟨R.one, (R.one_mul (rpow R lam j)).symm⟩

/-- **定理 (M151F-4b): k ≤ j なら λ^j ∈ (λ^k)** —
    λ^j = λ^{j−k}·λ^k（rpow_add と (j−k)+k = j の簿記）。 -/
theorem lam_pow_val_le {R : CRing} {lam : R.carrier} (j k : Nat)
    (hkj : k ≤ j) : IsValAtLeast R lam (rpow R lam j) k := by
  have h1 : rpow R lam ((j - k) + k)
      = R.mul (rpow R lam (j - k)) (rpow R lam k) :=
    rpow_add R lam (j - k) k
  have hj : (j - k) + k = j := Nat.sub_add_cancel hkj
  rw [hj] at h1
  exact ⟨rpow R lam (j - k), h1⟩

/-! ## M151F-5: 本丸 — 膜の厳密降下 λ^k ∉ (λ^{k+1}) -/

/-- **定理 (M151F-5): 厳密降下（本丸）** — λ が正則かつ非単元なら
    λ^k ∉ (λ^{k+1})。λ^k = h·λ^{k+1} = (h·λ)·λ^k と仮定すると
    (1 − h·λ)·λ^k = 0（right_distrib + neg_mul + add_neg）、
    λ^k の正則性（M146F-3 regular_rpow）で 1 − h·λ = 0、
    eq_of_sub_eq_zero で 1 = h·λ、mul_comm で λ·h = 1 となり
    非単元性 hnu に矛盾。M119 towerLam_ne_zero の係数比較後半と
    同じ道具立て。 -/
theorem lam_pow_strict (R : CRing) {lam : R.carrier}
    (hreg : IsRegularElem R lam) (hnu : ∀ v, R.mul lam v ≠ R.one)
    (k : Nat) : ¬ IsValAtLeast R lam (rpow R lam k) (k + 1) := by
  intro hv
  obtain ⟨h, hx⟩ := hv
  -- h·λ^{k+1} = h·(λ^k·λ) = (h·λ)·λ^k
  have hstep : R.mul h (rpow R lam (k + 1))
      = R.mul (R.mul h lam) (rpow R lam k) := by
    show R.mul h (R.mul (rpow R lam k) lam)
        = R.mul (R.mul h lam) (rpow R lam k)
    rw [R.mul_comm (rpow R lam k) lam, ← R.mul_assoc]
  have hx' : rpow R lam k = R.mul (R.mul h lam) (rpow R lam k) :=
    hx.trans hstep
  -- (1 − h·λ)·λ^k = λ^k − (h·λ)·λ^k = λ^k − λ^k = 0
  have hzero : R.mul (R.add R.one (R.neg (R.mul h lam))) (rpow R lam k)
      = R.zero := by
    rw [CRing.right_distrib, R.one_mul, CRing.neg_mul, ← hx',
      CRing.add_neg]
  -- λ^k の正則性で 1 − h·λ = 0
  have hone : R.add R.one (R.neg (R.mul h lam)) = R.zero :=
    regular_rpow R hreg k _ hzero
  -- 1 = h·λ → λ·h = 1 で非単元性に矛盾
  have heq : R.one = R.mul h lam := CRing.eq_of_sub_eq_zero R hone
  apply hnu h
  rw [R.mul_comm lam h]
  exact heq.symm

/-! ## M151F-6: 排他性 — λ^j ∈ (λ^k) ↔ k ≤ j（v(λ^j) = j） -/

/-- **定理 (M151F-6): 排他性** — λ^j の所属レベルは k ≤ j と正確に
    一致する。→ 側: k > j なら（cases Nat.lt_or_ge、選言の直接消去）
    M151F-3b の降下で所属を j+1 段へ下ろし、M151F-5 の厳密降下に
    衝突。← 側: M151F-4b。所属レベルの最大値が冪指数 j を一意に
    切り出す = **v(λ^j) = j の井戸定義性**。 -/
theorem lam_pow_val_exact (R : CRing) {lam : R.carrier}
    (hreg : IsRegularElem R lam) (hnu : ∀ v, R.mul lam v ≠ R.one)
    (j k : Nat) :
    IsValAtLeast R lam (rpow R lam j) k ↔ k ≤ j := by
  constructor
  · intro hv
    cases Nat.lt_or_ge j k with
    | inl hlt =>
      exact absurd
        (isValAtLeast_mono R lam (rpow R lam j) k (j + 1) hlt hv)
        (lam_pow_strict R hreg hnu j)
    | inr hge => exact hge
  · intro hkj
    exact lam_pow_val_le j k hkj

/-! ## M151F-7: 塔 instance（見出し） -/

/-- **定理 (M151F-7a): 塔の λ 階段（見出し）** —
    **Lubin–Tate 塔の全レベルで λ-adic 値 v(λ^j) = j が井戸定義
    （イデアル膜の所属レベルが冪指数を一意に切り出す）**: 各 n, k で
    λₙ^k ∈ (λₙ^k) かつ λₙ^k ∉ (λₙ^{k+1})。M144（tower_lam_regular）
    と M111（tower_lam_not_unit）を M151F-4a・M151F-5 に食わせる。 -/
theorem tower_lam_staircase (p : Nat) (hp : 2 ≤ p) (n k : Nat) :
    IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam
      (rpow (towerLevel p n).ring (towerLevel p n).lam k) k ∧
    ¬ IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam
      (rpow (towerLevel p n).ring (towerLevel p n).lam k) (k + 1) :=
  ⟨lam_pow_self_val (towerLevel p n).ring (towerLevel p n).lam k,
   lam_pow_strict (towerLevel p n).ring (tower_lam_regular p hp n)
     (tower_lam_not_unit p hp n) k⟩

/-- **定理 (M151F-7b): 塔の排他性** — 全レベルで
    λₙ^j ∈ (λₙ^k) ↔ k ≤ j。 -/
theorem tower_lam_val_exact (p : Nat) (hp : 2 ≤ p) (n j k : Nat) :
    IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam
      (rpow (towerLevel p n).ring (towerLevel p n).lam j) k ↔ k ≤ j :=
  lam_pow_val_exact (towerLevel p n).ring (tower_lam_regular p hp n)
    (tower_lam_not_unit p hp n) j k

/-! ## M151F-8: 総括 -/

/-- **M151F-8a: 総括** — λ-adic 付値の階段データ
    （入れ子・所属・厳密降下・排他性）。 -/
structure LambdaValuationData (p : Nat) (hp : 2 ≤ p) where
  /-- 膜の入れ子（一般環）: 値 ≥ k+1 → 値 ≥ k。 -/
  nest : ∀ (R : CRing) (lam x : R.carrier) (k : Nat),
    IsValAtLeast R lam x (k + 1) → IsValAtLeast R lam x k
  /-- λₙ^k は値 ≥ k（全レベル・全冪）。 -/
  self_val : ∀ n k,
    IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam
      (rpow (towerLevel p n).ring (towerLevel p n).lam k) k
  /-- 厳密降下: λₙ^k ∉ (λₙ^{k+1})（全レベル・全冪）。 -/
  strict : ∀ n k,
    ¬ IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam
      (rpow (towerLevel p n).ring (towerLevel p n).lam k) (k + 1)
  /-- 排他性: λₙ^j ∈ (λₙ^k) ↔ k ≤ j（v(λₙ^j) = j の井戸定義性）。 -/
  exact_val : ∀ n j k,
    IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam
      (rpow (towerLevel p n).ring (towerLevel p n).lam j) k ↔ k ≤ j

/-- **M151F-8b: witness**。 -/
def lambdaValuationData (p : Nat) (hp : 2 ≤ p) :
    LambdaValuationData p hp where
  nest := fun R lam x k => isValAtLeast_step R lam x k
  self_val := fun n k => (tower_lam_staircase p hp n k).1
  strict := fun n k => (tower_lam_staircase p hp n k).2
  exact_val := fun n j k => tower_lam_val_exact p hp n j k

/-- **M151F-8c: 存在**。 -/
theorem lambdaValuation_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaValuationData p hp) :=
  ⟨lambdaValuationData p hp⟩

end IUT
