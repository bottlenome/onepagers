/-
# M156F: 構成的順序体の総括 capstone — スクラッチ ℝ の全法則の一括 certification

第87〜99弾で建設したスクラッチ構成的 ℝ（正則 Cauchy 列 RReal / realEq）の
全法則を**単一レコード `ConstructiveOrderedFieldData` に束ね、witness を
既存定理の組み立てのみ（新規証明ゼロ）で閉じる** M134 方式の capstone。

  * M156F-1 `ConstructiveOrderedFieldData` — 構成的順序体の全景レコード:
    - 等値（M117F）: eq_refl・eq_symm・eq_trans
    - 加法群（M117F）: add_assoc・add_comm・add_zero・add_neg・
      add_congr_left/right
    - 乗法可換モノイド（M123F）: mul_comm・mul_one・mul_zero・
      mul_congr_left/right
    - 環法則（M150）: mul_assoc・mul_distrib_r/l
    - 順序（M125/M130/M136F）: le_refl・le_trans・le_antisym（→ realEq）・
      le_congr・le_add・lt_trans・lt_cotrans・lt_irrefl・le_iff_not_lt
    - 正値乗法（M129F）: pos_mul・lt_mul_pos
    - 絶対値（M127F）: abs_mul
    - max 束（M139/M140F）: le_max_left/right・max_least・
      max_comm・max_idem・max_assoc・max_congr
    - 完備性（M128）: lim_close・lim_unique（対角極限 rlim の witness 形）
    - 逆元（M145/M153F）: pos_inv・apart_cases（符号二分法）・apart_inv
    - master rate-bound（M150）: rate_bound —
      |wₙ − w'ₙ| ≤ C/(n+1) ⇒ realEq w w'
    - 埋め込み ℚ → ℝ（M115F/M131F/M132）: embed_add・embed_mul・
      embed_mono・nat_mono
  * M156F-2 `constructiveOrderedFieldData` — witness。全フィールドが
    既存定理の名前（+ 引数順の eta 展開のみ）で埋まる — 新規証明ゼロ
  * M156F-3 `constructiveOrderedField_exists` — Nonempty 形の存在
  * M156F-4 単文見出し: `real_field_complete_profile`（apart 逆元 —
    IsPos |x| → ∃ y, x·y ≈ 1 の再輸出）・`real_field_distrib`
    （分配律の再輸出）

## 意義

第87〜99弾（M115F ℚ → M117F 加法群 → M123F 乗法 → M125/M130/M136F 順序 →
M127F 絶対値 → M128 完備性 → M139/M140F max → M145/M153F 逆元 →
M150 環法則）の全鎖が単一 witness で閉じ、
`#print axioms constructiveOrderedFieldData = [propext, Quot.sound]` が
choice-free 性の一括確認になる。新規証明ゼロで閉じること自体が
各層の総括設計の正しさの証明。

## 正直な申告

* 除算の代数法則（逆元の一意性・(x·y)⁻¹ ≈ y⁻¹·x⁻¹ 等）・log/exp は次層。
* realEq を本物の等号にする商型（setoid 商 ℝ）の構成そのものは次層 —
  本レコードは「realEq を等号と読む」構成的順序体の全景。
* natToReal の順序忠実性 natToReal_reflect（M142F）は IntRealBridge 側に
  あり本ファイルの最小 import 閉包の外なので束には含めない（単調性
  nat_mono までを収録）。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealRingLaws
import IUT.ApartInv
import IUT.RealMaxLaws
import IUT.RealOrderComplete

namespace IUT

/-! ## M156F-1: 構成的順序体の全景レコード -/

/-- **M156F-1: 構成的順序体の総括レコード** — スクラッチ ℝ
    （RReal / realEq）が満たす全法則の一括束。各フィールドは
    第87〜99弾の主要定理をそのまま型に写したもの。 -/
structure ConstructiveOrderedFieldData where
  /- ### 等値（M117F） -/
  /-- 反射律。 -/
  eq_refl : ∀ x : RReal, realEq x x
  /-- 対称律。 -/
  eq_symm : ∀ x y : RReal, realEq x y → realEq y x
  /-- 推移律。 -/
  eq_trans : ∀ x y z : RReal, realEq x y → realEq y z → realEq x z
  /- ### 加法群（M117F） -/
  /-- 加法の結合律。 -/
  add_assoc : ∀ x y z : RReal,
    realEq (realAdd (realAdd x y) z) (realAdd x (realAdd y z))
  /-- 加法の可換律。 -/
  add_comm : ∀ x y : RReal, realEq (realAdd x y) (realAdd y x)
  /-- 右零元。 -/
  add_zero : ∀ x : RReal, realEq (realAdd x realZero) x
  /-- 反元法則。 -/
  add_neg : ∀ x : RReal, realEq (realAdd x (realNeg x)) realZero
  /-- 加法の左 congruence。 -/
  add_congr_left : ∀ x x' y : RReal,
    realEq x x' → realEq (realAdd x y) (realAdd x' y)
  /-- 加法の右 congruence。 -/
  add_congr_right : ∀ x y y' : RReal,
    realEq y y' → realEq (realAdd x y) (realAdd x y')
  /- ### 乗法可換モノイド（M123F） -/
  /-- 乗法の可換律。 -/
  mul_comm : ∀ x y : RReal, realEq (rmul x y) (rmul y x)
  /-- 右単位元 1。 -/
  mul_one : ∀ x : RReal, realEq (rmul x (qToReal ratRing.one)) x
  /-- 零元の吸収。 -/
  mul_zero : ∀ x : RReal, realEq (rmul x realZero) realZero
  /-- 乗法の左 congruence。 -/
  mul_congr_left : ∀ x x' y : RReal,
    realEq x x' → realEq (rmul x y) (rmul x' y)
  /-- 乗法の右 congruence。 -/
  mul_congr_right : ∀ x y y' : RReal,
    realEq y y' → realEq (rmul x y) (rmul x y')
  /- ### 環法則（M150） -/
  /-- 乗法の結合律（M150-4）。 -/
  mul_assoc : ∀ x y z : RReal,
    realEq (rmul (rmul x y) z) (rmul x (rmul y z))
  /-- 右分配律（M150-3）。 -/
  mul_distrib_r : ∀ x y z : RReal,
    realEq (rmul (realAdd x y) z) (realAdd (rmul x z) (rmul y z))
  /-- 左分配律（M150-3）。 -/
  mul_distrib_l : ∀ x y z : RReal,
    realEq (rmul z (realAdd x y)) (realAdd (rmul z x) (rmul z y))
  /- ### 順序（M125/M130/M136F） -/
  /-- rLe の反射律。 -/
  le_refl : ∀ x : RReal, rLe x x
  /-- rLe の推移律。 -/
  le_trans : ∀ x y z : RReal, rLe x y → rLe y z → rLe x z
  /-- 反対称律 — 両向き ≤ から realEq。 -/
  le_antisym : ∀ x y : RReal, rLe x y → rLe y x → realEq x y
  /-- rLe の realEq 両立。 -/
  le_congr : ∀ x x' y y' : RReal,
    realEq x x' → realEq y y' → rLe x y → rLe x' y'
  /-- 加法との両立。 -/
  le_add : ∀ x y z : RReal, rLe x y → rLe (realAdd x z) (realAdd y z)
  /-- rLt の推移律。 -/
  lt_trans : ∀ x y z : RReal, rLt x y → rLt y z → rLt x z
  /-- 余推移律（構成的順序の核）。 -/
  lt_cotrans : ∀ x y : RReal, rLt x y → ∀ z : RReal, rLt x z ∨ rLt z y
  /-- rLt の非反射律。 -/
  lt_irrefl : ∀ x : RReal, ¬ rLt x x
  /-- rLe ⟺ ¬rLt（M136F-2）。 -/
  le_iff_not_lt : ∀ x y : RReal, rLe x y ↔ ¬ rLt y x
  /- ### 正値乗法（M129F） -/
  /-- 正値の乗法閉性。 -/
  pos_mul : ∀ x y : RReal, IsPos x → IsPos y → IsPos (rmul x y)
  /-- 0 < x・0 < y ⇒ 0 < x·y。 -/
  lt_mul_pos : ∀ x y : RReal,
    rLt realZero x → rLt realZero y → rLt realZero (rmul x y)
  /- ### 絶対値（M127F） -/
  /-- 乗法性 |x·y| ≈ |x|·|y|。 -/
  abs_mul : ∀ x y : RReal, realEq (rabs (rmul x y)) (rmul (rabs x) (rabs y))
  /- ### max 束（M139/M140F） -/
  /-- 左上界性。 -/
  le_max_left : ∀ x y : RReal, rLe x (rmax x y)
  /-- 右上界性。 -/
  le_max_right : ∀ x y : RReal, rLe y (rmax x y)
  /-- 最小上界性。 -/
  max_least : ∀ x y z : RReal, rLe x z → rLe y z → rLe (rmax x y) z
  /-- max の可換律。 -/
  max_comm : ∀ x y : RReal, realEq (rmax x y) (rmax y x)
  /-- max の冪等律。 -/
  max_idem : ∀ x : RReal, realEq (rmax x x) x
  /-- max の結合律。 -/
  max_assoc : ∀ x y z : RReal,
    realEq (rmax (rmax x y) z) (rmax x (rmax y z))
  /-- max の realEq 両立（M140F 本丸）。 -/
  max_congr : ∀ x x' y y' : RReal,
    realEq x x' → realEq y y' → realEq (rmax x y) (rmax x' y')
  /- ### 完備性（M128） -/
  /-- 対角極限の収束（witness 形）: |rlim − X_m| ≤ 1/(m+1)。 -/
  lim_close : ∀ (X : Nat → RReal) (hX : IsCauchyReals X) (m j : Nat),
    qLe (qAbs (qAdd ((rlim X hX).seq j) (qNeg ((X m).seq j))))
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac j) (qUnitFrac j)))
  /-- 対角極限の一意性。 -/
  lim_unique : ∀ (X : Nat → RReal) (hX : IsCauchyReals X) (Z : RReal),
    (∀ m j, qLe (qAbs (qAdd (Z.seq j) (qNeg ((X m).seq j))))
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac j) (qUnitFrac j)))) →
    realEq (rlim X hX) Z
  /- ### 逆元（M145/M153F） -/
  /-- 正の実数の乗法逆元（M145）。 -/
  pos_inv : ∀ x : RReal, IsPos x →
    ∃ y : RReal, realEq (rmul x y) (qToReal ratRing.one)
  /-- 符号二分法（M153F 本丸1）: IsPos |x| → IsPos x ∨ IsPos (−x)。 -/
  apart_cases : ∀ x : RReal, IsPos (rabs x) → IsPos x ∨ IsPos (realNeg x)
  /-- apart 一般の乗法逆元（M153F 本丸2）。 -/
  apart_inv : ∀ x : RReal, IsPos (rabs x) →
    ∃ y : RReal, realEq (rmul x y) (qToReal ratRing.one)
  /- ### master rate-bound（M150） -/
  /-- 速度 C の点ごと近似から realEq（M150 master）。 -/
  rate_bound : ∀ (w w' : RReal) (C : Nat),
    (∀ k, qLe (qAbs (qAdd (w.seq k) (qNeg (w'.seq k)))) (qFrac C k)) →
    realEq w w'
  /- ### 埋め込み ℚ → ℝ（M115F/M131F/M132） -/
  /-- 埋め込みの加法性。 -/
  embed_add : ∀ a b : QRat,
    realEq (realAdd (qToReal a) (qToReal b)) (qToReal (qAdd a b))
  /-- 埋め込みの乗法性。 -/
  embed_mul : ∀ a b : QRat,
    realEq (rmul (qToReal a) (qToReal b)) (qToReal (qMul a b))
  /-- 埋め込みの単調性。 -/
  embed_mono : ∀ a b : QRat, qLe a b → rLe (qToReal a) (qToReal b)
  /-- 自然数埋め込みの単調性。 -/
  nat_mono : ∀ a b : Nat, a ≤ b → rLe (natToReal a) (natToReal b)

/-! ## M156F-2: witness — 既存定理の組み立てのみ（新規証明ゼロ） -/

/-- **M156F-2: witness** — 全フィールドが第87〜99弾の既存定理の名前
    （implicit 引数の eta 展開のみ）で埋まる。
    `#print axioms constructiveOrderedFieldData` が [propext, Quot.sound]
    のみであることが全鎖の choice-free 性の一括 certification。 -/
def constructiveOrderedFieldData : ConstructiveOrderedFieldData where
  eq_refl := realEq_refl
  eq_symm := fun _ _ h => realEq_symm h
  eq_trans := fun _ _ _ h1 h2 => realEq_trans h1 h2
  add_assoc := realAdd_assoc
  add_comm := realAdd_comm
  add_zero := realAdd_zero
  add_neg := realAdd_neg
  add_congr_left := fun _ _ y h => realAdd_congr_left y h
  add_congr_right := fun x _ _ h => realAdd_congr_right x h
  mul_comm := rmul_comm
  mul_one := rmul_one
  mul_zero := rmul_zero
  mul_congr_left := fun _ _ y h => rmul_congr_left y h
  mul_congr_right := fun x _ _ h => rmul_congr_right x h
  mul_assoc := rmul_assoc_real
  mul_distrib_r := rmul_add_right
  mul_distrib_l := rmul_add_left
  le_refl := rLe_refl
  le_trans := fun _ _ _ h1 h2 => rLe_trans h1 h2
  le_antisym := fun _ _ h1 h2 => rLe_antisym h1 h2
  le_congr := fun _ _ _ _ hx hy h => rLe_congr hx hy h
  le_add := fun _ _ z h => rLe_add z h
  lt_trans := fun _ _ _ h1 h2 => rLt_trans h1 h2
  lt_cotrans := fun _ _ h z => rLt_cotrans h z
  lt_irrefl := rLt_irrefl
  le_iff_not_lt := IUT.le_iff_not_lt
  pos_mul := fun _ _ hx hy => isPos_mul hx hy
  lt_mul_pos := fun _ _ hx hy => rLt_mul_pos hx hy
  abs_mul := rabs_mul
  le_max_left := rLe_max_left
  le_max_right := rLe_max_right
  max_least := fun _ _ _ h1 h2 => rmax_least h1 h2
  max_comm := rmax_comm
  max_idem := rmax_idem
  max_assoc := rmax_assoc
  max_congr := fun _ _ _ _ hx hy => rmax_congr hx hy
  lim_close := rlim_close
  lim_unique := rlim_unique
  pos_inv := pos_inv_exists
  apart_cases := isPos_abs_cases
  apart_inv := apart_inv_exists
  rate_bound := realEq_of_rate_bound
  embed_add := qToReal_add
  embed_mul := qToReal_mul
  embed_mono := fun _ _ h => qToReal_mono h
  nat_mono := fun _ _ h => natToReal_mono h

/-! ## M156F-3: 存在 -/

/-- **M156F-3: 存在** — 構成的順序体の全景データは空でない。 -/
theorem constructiveOrderedField_exists : Nonempty ConstructiveOrderedFieldData :=
  ⟨constructiveOrderedFieldData⟩

/-! ## M156F-4: 単文見出し -/

/-- **M156F-4a: 完全性プロファイル** — 束を経ない代表的単文の再輸出:
    0 から構成的に離れた（apart な）実数は乗法逆元を持つ
    （構成的 Heyting 体の逆元公理、M153F）。 -/
theorem real_field_complete_profile :
    ∀ x : RReal, IsPos (rabs x) →
      ∃ y : RReal, realEq (rmul x y) (qToReal ratRing.one) :=
  apart_inv_exists

/-- **M156F-4b: 分配律の再輸出**（M150-3、bound-chain 係数問題の
    全面解決の帰結）。 -/
theorem real_field_distrib :
    ∀ x y z : RReal,
      realEq (rmul (realAdd x y) z) (realAdd (rmul x z) (rmul y z)) :=
  rmul_add_right

end IUT
