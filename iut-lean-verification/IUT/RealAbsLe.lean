/-
# M173: 絶対値の順序基本則 — 「絶対値が支配する」（柱C）

M127F（rabs の点ごと witness 法則）と M130（非厳密順序 rLe）の合流。
実数の絶対値 rabs が満たす基本的な**順序**の事実——0 ≤ |x|・x ≤ |x|・
−x ≤ |x|——を rLe（非厳密順序）として閉じる。要となる再利用可能な
補題 `rLe_of_seq_le`（点ごとの ℚ 不等式から rLe を作る）も新設する。

  * M173-1 **`rLe_of_seq_le`** — 点ごと ℚ 不等式 → rLe:
    (∀n, x_n ≤ y_n) ⟹ rLe x y。以後の順序証明の汎用装置
    （rLe の 2u_n スラックを一括処理）
  * M173-2 `rabs_nonneg` — 0 ≤ |x|
  * M173-3 `rLe_self_rabs` — x ≤ |x|
  * M173-4 `rLe_neg_rabs` — −x ≤ |x|
  * M173-5 `RealAbsLeData` — 総括

意義: 「絶対値が支配する」（x も −x も |x| 以下、|x| は非負）という
順序論の最も基本的な三点。これは実数の三角不等式・級数の絶対収束
（|Σ| ≤ Σ|·|）の順序側の土台であり、M169（|r^k| = |r|^k）の順序版の
入口。`rLe_of_seq_le` は「点ごとに ≤ が言えれば rLe」という橋で、
今後の順序補題（単調性・評価）を大幅に簡略化する再利用部品。

正直な限定: 三角不等式そのもの（|x+y| ≤ |x|+|y| の rLe 形）・
狭義順序 rLt との連携・順序と乗法の相互作用は次層。本層は絶対値の
片側支配（3 つの rLe）と汎用ブリッジのみ。

全て選択公理不使用。
-/
import IUT.RealAbs
import IUT.RealLe
import IUT.RealOrder

namespace IUT

/-! ## M173-1: 点ごと ℚ 不等式 → rLe -/

/-- **定理 (M173-1): 点ごと ≤ から rLe** — 各項で x_n ≤ y_n なら rLe x y。
    rLe の定義は x_n ≤ y_n + 2u_n なので、点ごとの ≤ に非負の 2u_n を
    足すだけ（qFrac_nonneg + qAdd_zero の整形）。以後の順序証明の汎用
    装置。 -/
theorem rLe_of_seq_le {x y : RReal} (h : ∀ n, qLe (x.seq n) (y.seq n)) :
    rLe x y := by
  intro n
  have h2u : qLe ratRing.zero (qAdd (qUnitFrac n) (qUnitFrac n)) := by
    have hh := qLe_add_two (qFrac_nonneg 1 n) (qFrac_nonneg 1 n)
    rwa [qAdd_zero_left ratRing.zero] at hh
  have hself : qLe (y.seq n)
      (qAdd (y.seq n) (qAdd (qUnitFrac n) (qUnitFrac n))) := by
    have hh := qLe_add_two (qLe_refl (y.seq n)) h2u
    rwa [qAdd_zero (y.seq n)] at hh
  exact qLe_trans _ _ _ (h n) hself

/-! ## M173-2: 非負性 -/

/-- **定理 (M173-2): 絶対値の非負性** — 0 ≤ |x|。各項 0 ≤ |x_n|
    （qAbs_nonneg）を M173-1 で持ち上げ。 -/
theorem rabs_nonneg (x : RReal) : rLe realZero (rabs x) :=
  rLe_of_seq_le (fun n => qAbs_nonneg (x.seq n))

/-! ## M173-3: x ≤ |x| -/

/-- **定理 (M173-3): 自身 ≤ 絶対値** — x ≤ |x|。各項 x_n ≤ |x_n|
    （qLe_self_abs）を M173-1 で持ち上げ。 -/
theorem rLe_self_rabs (x : RReal) : rLe x (rabs x) :=
  rLe_of_seq_le (fun n => qLe_self_abs (x.seq n))

/-! ## M173-4: −x ≤ |x| -/

/-- **定理 (M173-4): 反元 ≤ 絶対値** — −x ≤ |x|。各項で
    −x_n ≤ |−x_n| = |x_n|（qLe_self_abs + qAbs_neg）を M173-1 で持ち上げ。
    (realNeg x).seq n = qNeg (x_n) は defeq。 -/
theorem rLe_neg_rabs (x : RReal) : rLe (realNeg x) (rabs x) :=
  rLe_of_seq_le (fun n => by
    show qLe (qNeg (x.seq n)) (qAbs (x.seq n))
    have hh := qLe_self_abs (qNeg (x.seq n))
    rwa [qAbs_neg (x.seq n)] at hh)

/-! ## M173-5: 総括 -/

/-- **M173-5a: 総括** — 絶対値の順序基本則データ。 -/
structure RealAbsLeData where
  /-- 点ごと ≤ → rLe。 -/
  of_seq_le : ∀ {x y : RReal}, (∀ n, qLe (x.seq n) (y.seq n)) → rLe x y
  /-- 0 ≤ |x|。 -/
  abs_nonneg : ∀ x : RReal, rLe realZero (rabs x)
  /-- x ≤ |x|。 -/
  self_le_abs : ∀ x : RReal, rLe x (rabs x)
  /-- −x ≤ |x|。 -/
  neg_le_abs : ∀ x : RReal, rLe (realNeg x) (rabs x)

/-- **M173-5b: witness**。 -/
def realAbsLeData : RealAbsLeData where
  of_seq_le := fun h => rLe_of_seq_le h
  abs_nonneg := rabs_nonneg
  self_le_abs := rLe_self_rabs
  neg_le_abs := rLe_neg_rabs

/-- **M173-5c: 存在**。 -/
theorem realAbsLe_exists : Nonempty RealAbsLeData := ⟨realAbsLeData⟩

end IUT
