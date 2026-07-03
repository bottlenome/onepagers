/-
# M161: λ-adic 付値の加法性・第一切片 — 積の値の下界と単元の厳密性（柱B）

M151F（λ-adic 値 v(λ^j) = j の井戸定義性と膜 (λ^k) の厳密降下）の直上に
立つ柱B の一歩。付値の**加法性の第一切片**を二方向で閉じる:

  * M161-1 `mul_middle4` — 可換環の中央四項入替
    (p·q)·(r·s) = (p·r)·(q·s)（assoc/comm のみ、choice 不使用）
  * M161-2 **`isValAtLeast_mul`（本丸1）** — 値の加法性（下界側）:
    x ∈ (λ^j)・y ∈ (λ^k) ⟹ x·y ∈ (λ^{j+k})。witness は係数の積
    a·b、λ^{j+k} = λ^j·λ^k（rpow_add）と中央四項入替で着地
  * M161-3 `tower_isValAtLeast_mul` — 塔全レベルへの特殊化
  * M161-4 **`lam_pow_mul_unit_strict`（本丸2）** — 逆向きの第一歩:
    λ 正則・非単元、u 単元なら **λ^j·u ∉ (λ^{j+1})**。
    λ^j·u = h·λ^{j+1} と仮定 → λ^j の正則性で u = h·λ →
    単元性 u·w = 1 から λ·(h·w) = 1 で非単元性に矛盾。
    M151F-5 `lam_pow_strict`（u = 1 の場合）の一般化
  * M161-5 `tower_lam_pow_mul_unit_strict` — 塔全レベルへの特殊化
  * M161-6 `LambdaValMulData` — 総括

意義: M151F は λ の冪 λ^j 自身の値の井戸定義性を与えた。本層は
「値の加法性 v(xy) = v(x)+v(y)」のうち**下界 v(xy) ≥ v(x)+v(y)**
（イデアルの積の所属、`isValAtLeast_mul`）と、**単元倍が値を上げない**
（λ^j·u は正確に j 段目で止まる、`lam_pow_mul_unit_strict`）を閉じる。
後者は λ^j·(単元) の値がちょうど j であること = 値が単元倍で不変で
あることを意味し、付値の乗法的性質の核心の第一歩。

正直な限定: 完全な加法性 v(xy) = v(x)+v(y)（等号、とくに上界側の
一般元版 = min の実現と一般座標の追跡）は M147F 座標理論の次層のまま。
本層が与えるのは下界の所属（積のイデアル包含）と、単元倍に対する
厳密性（λ の冪 × 単元という特別な形での上界）であり、一般元 x·y の
値の上界そのものではない。ここは過大主張しない。

全て選択公理不使用。
-/
import IUT.LambdaValuation

namespace IUT

/-! ## M161-1: 可換環の中央四項入替 -/

/-- **補題 (M161-1): 中央四項入替** — (p·q)·(r·s) = (p·r)·(q·s)。
    assoc/comm の付け替えのみ（choice 不使用）。積のイデアル所属の
    witness 整形に使う。 -/
theorem mul_middle4 (R : CRing) (p q r s : R.carrier) :
    R.mul (R.mul p q) (R.mul r s) = R.mul (R.mul p r) (R.mul q s) := by
  rw [R.mul_assoc p q (R.mul r s), ← R.mul_assoc q r s, R.mul_comm q r,
    R.mul_assoc r q s, ← R.mul_assoc p r (R.mul q s)]

/-! ## M161-2: 値の加法性（下界側）— 積の所属 -/

/-- **定理 (M161-2, 本丸1): 積の値の下界** — x ∈ (λ^j)・y ∈ (λ^k) なら
    x·y ∈ (λ^{j+k})。x = a·λ^j, y = b·λ^k から
    x·y = (a·λ^j)·(b·λ^k) = (a·b)·(λ^j·λ^k) = (a·b)·λ^{j+k}
    （中央四項入替 + rpow_add）。witness は a·b。 -/
theorem isValAtLeast_mul {R : CRing} {lam x y : R.carrier} {j k : Nat}
    (hx : IsValAtLeast R lam x j) (hy : IsValAtLeast R lam y k) :
    IsValAtLeast R lam (R.mul x y) (j + k) := by
  obtain ⟨a, hxa⟩ := hx
  obtain ⟨b, hyb⟩ := hy
  refine ⟨R.mul a b, ?_⟩
  rw [hxa, hyb, rpow_add R lam j k]
  exact mul_middle4 R a (rpow R lam j) b (rpow R lam k)

/-! ## M161-3: 塔全レベルへの特殊化 -/

/-- **定理 (M161-3): 塔の積の値の下界** — Lubin–Tate 塔の全レベルで
    x ∈ (λₙ^j)・y ∈ (λₙ^k) なら x·y ∈ (λₙ^{j+k})。 -/
theorem tower_isValAtLeast_mul (p : Nat) (n : Nat)
    {x y : (towerLevel p n).ring.carrier} {j k : Nat}
    (hx : IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam x j)
    (hy : IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam y k) :
    IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam
      ((towerLevel p n).ring.mul x y) (j + k) :=
  isValAtLeast_mul hx hy

/-! ## M161-4: 単元倍の厳密性（逆向きの第一歩） -/

/-- **定理 (M161-4, 本丸2): 単元倍は値を上げない** — λ 正則・非単元、
    u 単元（∃ w, u·w = 1）なら λ^j·u ∉ (λ^{j+1})。
    λ^j·u = h·λ^{j+1} = (h·λ)·λ^j と仮定すると u·λ^j = (h·λ)·λ^j、
    λ^j の正則性（M146F-3 regular_rpow）で u = h·λ、
    単元性 u·w = 1 に代入して λ·(h·w) = 1 となり非単元性 hnu に矛盾。
    M151F-5 `lam_pow_strict`（u = 1 に相当）の一般化。 -/
theorem lam_pow_mul_unit_strict (R : CRing) {lam : R.carrier}
    (hreg : IsRegularElem R lam) (hnu : ∀ v, R.mul lam v ≠ R.one)
    (j : Nat) {u : R.carrier} (hu : ∃ w, R.mul u w = R.one) :
    ¬ IsValAtLeast R lam (R.mul (rpow R lam j) u) (j + 1) := by
  intro hv
  obtain ⟨h, hx⟩ := hv
  obtain ⟨w, hw⟩ := hu
  -- u·λ^j = (h·λ)·λ^j （λ^{j+1} = λ^j·λ を展開して整形）
  have key : R.mul u (rpow R lam j) = R.mul (R.mul h lam) (rpow R lam j) := by
    rw [R.mul_comm u (rpow R lam j)]
    rw [hx]
    show R.mul h (R.mul (rpow R lam j) lam)
        = R.mul (R.mul h lam) (rpow R lam j)
    rw [R.mul_comm (rpow R lam j) lam, ← R.mul_assoc]
  -- (u − h·λ)·λ^j = 0
  have hz : R.mul (R.add u (R.neg (R.mul h lam))) (rpow R lam j) = R.zero := by
    rw [CRing.right_distrib, CRing.neg_mul, key, CRing.add_neg]
  -- λ^j の正則性で u = h·λ
  have hsub : R.add u (R.neg (R.mul h lam)) = R.zero :=
    regular_rpow R hreg j _ hz
  have hueq : u = R.mul h lam := CRing.eq_of_sub_eq_zero R hsub
  -- 単元性に代入: λ·(h·w) = 1 で非単元性に矛盾
  rw [hueq] at hw
  apply hnu (R.mul h w)
  rw [← R.mul_assoc, R.mul_comm lam h]
  exact hw

/-! ## M161-5: 塔全レベルへの特殊化 -/

/-- **定理 (M161-5): 塔の単元倍の厳密性** — 全レベルで
    λₙ^j·u ∉ (λₙ^{j+1})（u 単元）。M144（tower_lam_regular）・
    M111（tower_lam_not_unit）を M161-4 に食わせる。 -/
theorem tower_lam_pow_mul_unit_strict (p : Nat) (hp : 2 ≤ p) (n j : Nat)
    {u : (towerLevel p n).ring.carrier}
    (hu : ∃ w, (towerLevel p n).ring.mul u w = (towerLevel p n).ring.one) :
    ¬ IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam
      ((towerLevel p n).ring.mul
        (rpow (towerLevel p n).ring (towerLevel p n).lam j) u) (j + 1) :=
  lam_pow_mul_unit_strict (towerLevel p n).ring (tower_lam_regular p hp n)
    (tower_lam_not_unit p hp n) j hu

/-! ## M161-6: 総括 -/

/-- **M161-6a: 総括** — λ-adic 付値の加法性・第一切片データ
    （積の下界・単元倍の厳密性）。 -/
structure LambdaValMulData (p : Nat) (hp : 2 ≤ p) where
  /-- 積の値の下界（一般環）: x ∈ (λ^j)・y ∈ (λ^k) → x·y ∈ (λ^{j+k})。 -/
  val_mul : ∀ (R : CRing) (lam x y : R.carrier) (j k : Nat),
    IsValAtLeast R lam x j → IsValAtLeast R lam y k →
    IsValAtLeast R lam (R.mul x y) (j + k)
  /-- 塔の積の値の下界。 -/
  tower_val_mul : ∀ n (x y : (towerLevel p n).ring.carrier) (j k : Nat),
    IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam x j →
    IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam y k →
    IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam
      ((towerLevel p n).ring.mul x y) (j + k)
  /-- 塔の単元倍の厳密性: λₙ^j·u ∉ (λₙ^{j+1})（u 単元）。 -/
  unit_strict : ∀ n j (u : (towerLevel p n).ring.carrier),
    (∃ w, (towerLevel p n).ring.mul u w = (towerLevel p n).ring.one) →
    ¬ IsValAtLeast (towerLevel p n).ring (towerLevel p n).lam
      ((towerLevel p n).ring.mul
        (rpow (towerLevel p n).ring (towerLevel p n).lam j) u) (j + 1)

/-- **M161-6b: witness**。 -/
def lambdaValMulData (p : Nat) (hp : 2 ≤ p) : LambdaValMulData p hp where
  val_mul := fun _ _ _ _ _ _ hx hy => isValAtLeast_mul hx hy
  tower_val_mul := fun n _ _ _ _ hx hy => tower_isValAtLeast_mul p n hx hy
  unit_strict := fun n j _ hu => tower_lam_pow_mul_unit_strict p hp n j hu

/-- **M161-6c: 存在**。 -/
theorem lambdaValMul_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaValMulData p hp) :=
  ⟨lambdaValMulData p hp⟩

end IUT
