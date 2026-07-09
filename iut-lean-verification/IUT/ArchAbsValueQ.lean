/-
  IUT/ArchAbsValueQ.lean — ℚ の実アルキメデス素点（place at ∞）の本物の絶対値 |·|_∞

  ── 主要成果の分類: **[実]**（本物の ℚ 値アルキメデス絶対値と絶対値公理の本物証明）。

  complete_pct 影響: **柱A の実数体 K の「実素点（アルキメデス素点）の不在」を埋める
  §2(b) 本物の先行建設**。監査は「数体 K に実アルキメデス素点（place at ∞）が
  一つも形式化されていない」と名指しした。本モジュールはその第一歩として、
  有理数体 ℚ（M115F の QRat = Quot ratRel、M264F の ratIUTField）上に
  **実際の ℚ≥0 値をとるアルキメデス絶対値** |·|_∞ を本物構成し、絶対値の 3 公理
  （非退化 |x|=0↔x=0・乗法性 |xy|=|x||y|・三角不等式 |x+y|≤|x|+|y|）を
  本物証明して、それらを「実素点 = ArchPlace」の実構造として束ねる。身代わり
  （toy 模型・surrogate 群・Bool 軌道）は一切用いない。

  * 絶対値の本体は既存 M115F の `qAbs`（代表 r = num/den に対し
    |r| = |num|/den、intAbs で分子の符号を落とす本物の ℚ 値関数）を再利用する。
  * 乗法性 `arp_abs_mul` は既存の実定理 `qAbs_mul`（分子の `intAbs_mul` から）、
    三角不等式 `arp_abs_triangle` は既存の実定理 `qAbs_add_le`（共通分母への
    通分＋分子の符号場合分け、ℚ の順序 `qLe` で述べる）を「実素点構造」の
    フィールドへ昇格させる。
  * 非退化 `arp_abs_zero_iff`（|x| = 0 ↔ x = 0）は既存になかった公理であり、
    本モジュールで**ゼロから本物証明**する（分子 intAbs r.num = 0 と
    `int_le_intAbs` / `int_neg_le_intAbs` の挟み撃ちで r.num = 0 を導く）。

  ## 検証する定理（全て sorry なし・新規 choice なし）

  * `arpAbs`            — 実 ℚ 値アルキメデス絶対値 |·|_∞（= qAbs）
  * `arp_abs_zero_iff`  — 非退化: |x| = 0 ↔ x = 0（本物・新規証明）
  * `arp_abs_mul`       — 乗法性: |x·y| = |x|·|y|（qAbs_mul の昇格）
  * `arp_abs_triangle`  — 三角不等式: |x+y| ≤ |x|+|y|（qAbs_add_le の昇格、qLe）
  * `ArchPlace`         — 実アルキメデス素点の構造（絶対値 + 3 公理）
  * `arpPlaceQ`         — witness（ℚ の place at ∞）
  * `arp_exists`        — capstone: 実アルキメデス素点は存在する

  ## 正直な限定（何が本物で何が未達か）

  * **本物**: |·|_∞ は実際の ℚ≥0 値関数（分子分母から本物に構成）で、上記 3 公理は
    全て ℚ の順序 API（qLe）と整数絶対値 API（intAbs）からの完全証明である。
    三角不等式も**通っている**（qAbs_add_le をそのまま実素点の公理に昇格）。
  * **未達（正直申告）**: これは ℚ の**唯一の**アルキメデス素点（Ostrowski で
    絶対値の同値類は一つ）だが、(1) 値域は ℝ≥0 でなく ℚ≥0 に留まり完備化
    （ℝ = ℚ_∞）は未構成、(2) 実素点と複素素点の区別・複素埋め込みは未形式化、
    (3) 一般の数体 K の実素点（K → ℝ の埋め込み全体）ではなく K = ℚ の
    一素点のみ。これらは後続で完備化 ℝ・埋め込み・Ostrowski 分類へ接続する。
  * 本モジュール単独では complete_pct を主張しない（親が統合時に判断）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
-/
import IUT.Field

namespace IUT

/-! ## 実アルキメデス絶対値 |·|_∞ -/

/-- **arpAbs**: ℚ 上の実アルキメデス絶対値 |·|_∞。既存 M115F の `qAbs`
    （代表 r = num/den に対し |r| = intAbs(num)/den）を再利用した**本物の
    ℚ≥0 値関数**。`ratIUTField.carrier` は QRat なので型は整合する。 -/
def arpAbs (x : ratIUTField.carrier) : ratIUTField.carrier := qAbs x

/-! ## 絶対値の 3 公理 -/

/-- **非退化（本物・新規証明）**: |x| = 0 ↔ x = 0。
    ⟸ は x = 0 のとき intAbs 0 = 0 で |0| = 0。
    ⟹ は |x| = 0 の代表分離から intAbs r.num = 0 を得て、
    `int_le_intAbs` / `int_neg_le_intAbs` の挟み撃ち（omega）で r.num = 0。 -/
theorem arp_abs_zero_iff (x : ratIUTField.carrier) :
    arpAbs x = ratIUTField.zero ↔ x = ratIUTField.zero := by
  induction x using Quot.ind
  rename_i r
  constructor
  · intro h
    have hrel : ratRel (prAbs r) prZero := quot_exact_rat h
    have hr : intAbs r.num * (1 : Int) = (0 : Int) * r.den := hrel
    have hnum : intAbs r.num = 0 := by omega
    have h1 : r.num ≤ intAbs r.num := int_le_intAbs r.num
    have h2 : -r.num ≤ intAbs r.num := int_neg_le_intAbs r.num
    have hr0 : r.num = 0 := by omega
    apply Quot.sound
    show r.num * (1 : Int) = (0 : Int) * r.den
    rw [hr0, Int.zero_mul, Int.zero_mul]
  · intro h
    have hrel : ratRel r prZero := quot_exact_rat h
    have hr : r.num * (1 : Int) = (0 : Int) * r.den := hrel
    have hr0 : r.num = 0 := by omega
    apply Quot.sound
    show intAbs r.num * (1 : Int) = (0 : Int) * r.den
    rw [hr0, intAbs_of_nonneg (Int.le_refl 0), Int.zero_mul, Int.zero_mul]

/-- **乗法性（本物・qAbs_mul の昇格）**: |x·y| = |x|·|y|。 -/
theorem arp_abs_mul (x y : ratIUTField.carrier) :
    arpAbs (ratIUTField.mul x y) = ratIUTField.mul (arpAbs x) (arpAbs y) :=
  qAbs_mul x y

/-- **三角不等式（本物・qAbs_add_le の昇格、ℚ の順序 qLe）**:
    |x + y| ≤ |x| + |y|。 -/
theorem arp_abs_triangle (x y : ratIUTField.carrier) :
    qLe (arpAbs (ratIUTField.add x y)) (ratIUTField.add (arpAbs x) (arpAbs y)) :=
  qAbs_add_le x y

/-! ## 実アルキメデス素点の構造 -/

/-- **ArchPlace**: ℚ 上の実アルキメデス素点（place at ∞）— ℚ≥0 値絶対値と
    絶対値の 3 公理（非退化・乗法性・三角不等式）を束ねた実構造。 -/
structure ArchPlace where
  /-- ℚ≥0 値絶対値 |·|_∞。 -/
  abs : ratIUTField.carrier → ratIUTField.carrier
  /-- 非退化: |x| = 0 ↔ x = 0。 -/
  abs_zero_iff : ∀ x, abs x = ratIUTField.zero ↔ x = ratIUTField.zero
  /-- 乗法性: |x·y| = |x|·|y|。 -/
  abs_mul : ∀ x y, abs (ratIUTField.mul x y) = ratIUTField.mul (abs x) (abs y)
  /-- 三角不等式: |x + y| ≤ |x| + |y|。 -/
  abs_triangle : ∀ x y,
    qLe (abs (ratIUTField.add x y)) (ratIUTField.add (abs x) (abs y))

/-- **witness**: ℚ の実アルキメデス素点（place at ∞）。 -/
def arpPlaceQ : ArchPlace where
  abs := arpAbs
  abs_zero_iff := arp_abs_zero_iff
  abs_mul := arp_abs_mul
  abs_triangle := arp_abs_triangle

/-- **capstone**: ℚ の実アルキメデス素点は存在する（実素点の不在の第一歩を埋める）。 -/
theorem arp_exists : Nonempty ArchPlace := ⟨arpPlaceQ⟩

end IUT
