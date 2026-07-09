/-
  IUT/ArchValueInteger.lean — B5 積公式スライス「アルキメデス側の実橋」

  ── 主要成果の分類: **[実]**（本物の ℚ 上で |x|_∞ = |num|/den を厳密な
     ℚ 等式として確定し、その逆数積 (a/b)(b/a)=1 の実等式まで通す）。

  complete_pct 影響: **未設定**（本スライス単独では complete_pct を主張しない。
     親が統合時に判断する）。§2(b) 本物の先行建設に該当し、既存の実アルキメデス
     絶対値 `arpAbs`(=`qAbs`) と実 ℚ（QRat = Quot ratRel）だけを用いる。p 進側
     （他スライス）には一切依存しない独立スライス。

  ## 目的（B5 積公式 |x|_∞·∏_p|x|_p = 1 のアルキメデス側 |x|_∞）

  最終の積公式で |x|_∞ = a/b（a = |num| = intAbs x.num, b = den = x.den）と
  ∏_{p∈S}|x|_p = b/a（他スライスが供給）を掛けて (a/b)(b/a) = 1 とする。その
  **a/b 側を実 ℚ 等式で確定**するのが本スライス。qAbs の Quot.lift 計算規則で
  |x|_∞ = mk(⟨intAbs x.num, x.den⟩) に展開し、分子 = intAbs num・分母 = den の
  本物の ℚ 値を取り出す。

  ## 検証する定理（全て sorry なし・新規 choice なし）

  * `avi_abs_num_den`    — |x|_∞ = |num|/den（分子 intAbs num・分母 den の実 ℚ 等式）
  * `avi_abs_int`        — |n|_∞ = |n|（整数 n の絶対値、ℤ→ℚ 埋め込み上）
  * `avi_ratio`          — a/b の実 ℚ 元（正分母 b）
  * `avi_intAbs_pos`     — num ≠ 0 なら分子側 a = intAbs num は正整数
  * `avi_ratio_mul_swap` — (a/b)·(b/a) = 1（B5 で ∏_p = b/a を掛ける素地・実等式）
  * `avi_abs_as_ratio`   — |x|_∞ = a/b（a = intAbs num, b = den）
  * `avi_abs_mul_recip`  — |x|_∞·(den/|num|) = 1（num ≠ 0）— 積公式の一因子確定
  * `AviRationalPlaceData` / `aviRationalPlaceData` — ℚ の実素点 ∞ データの束ね

  ## 正直な限定（何が本物で何が未達か）

  * **本物**: |x|_∞ = intAbs(x.num)/x.den は実 ℚ（Quot ratRel）上の厳密な等式で、
    qAbs の定義展開（prAbs = ⟨intAbs num, den⟩）から得る。逆数積 (a/b)(b/a)=1 も
    prMul と Quot.sound（交差積 a·b·1 = 1·(b·a)）で本物証明する。
  * **未達（正直申告）**: 本スライスはアルキメデス側 |x|_∞ = a/b **のみ**を確定する。
    ∏_p|x|_p = b/a（p 進側スライス）と B5 の最終組み立て |x|_∞·∏_p|x|_p = 1 は
    本ファイルの範囲外（他スライス・親統合で接続）。値域は ℚ≥0 に留まり ℝ 完備化は
    未構成。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
-/
import IUT.ArchAbsValueQ

namespace IUT

/-! ## 実 ℚ 上の比 a/b と分子側の正整数性 -/

/-- **avi_ratio**: 正分母 b をもつ実 ℚ 元 a/b（= `Quot.mk ratRel ⟨a, b, hb⟩`）。
    B5 のアルキメデス側 |x|_∞ = a/b と、その逆 b/a を同じ道具で表すための本物の
    ℚ 値コンストラクタ。 -/
def avi_ratio (a b : Int) (hb : 0 < b) : QRat := Quot.mk ratRel ⟨a, b, hb⟩

/-- **avi_intAbs_pos**: num ≠ 0 なら分子側 a = intAbs num は正整数。B5 で
    b/a（a = |num|）を作る際に分母 a > 0 を保証する（挟み撃ち + omega）。 -/
theorem avi_intAbs_pos {a : Int} (h : a ≠ 0) : 0 < intAbs a := by
  have h1 : a ≤ intAbs a := int_le_intAbs a
  have h2 : -a ≤ intAbs a := int_neg_le_intAbs a
  have h3 : 0 ≤ intAbs a := intAbs_nonneg a
  omega

/-! ## アルキメデス側 |x|_∞ = |num|/den の実 ℚ 等式 -/

/-- **avi_abs_num_den（主定理）**: x = num/den のアルキメデス絶対値は
    **|num|/den**（分子 = intAbs num・分母 = den）に等しい。`arpAbs = qAbs` の
    Quot.lift 計算規則（qAbs(mk x) = mk(prAbs x)）と prAbs x = ⟨intAbs num, den⟩
    の定義展開で得る本物の ℚ 等式。 -/
theorem avi_abs_num_den (x : PreRat) :
    arpAbs (Quot.mk ratRel x)
      = Quot.mk ratRel (⟨intAbs x.num, x.den, x.den_pos⟩ : PreRat) := rfl

/-- **avi_abs_as_ratio**: 上を avi_ratio 表示に言い換えたもの — |x|_∞ = a/b
    （a = intAbs x.num, b = x.den）。B5 組み立てで逆 b/a を掛けるための形。 -/
theorem avi_abs_as_ratio (x : PreRat) :
    arpAbs (Quot.mk ratRel x) = avi_ratio (intAbs x.num) x.den x.den_pos := rfl

/-- **avi_abs_int**: 整数 n の絶対値は |n| に等しい（ℤ→ℚ 埋め込み `ratOfInt` の
    像の上で |n|_∞ = |n|）。分母が 1 で共通のため代表の PreRat 等式に落ちる。 -/
theorem avi_abs_int (n : Int) :
    arpAbs (ratOfInt.map n) = ratOfInt.map (intAbs n) := by
  show Quot.mk ratRel (prAbs (intToPreRat n))
    = Quot.mk ratRel (intToPreRat (intAbs n))
  exact congrArg (Quot.mk ratRel) (preRat_ext rfl rfl)

/-! ## 逆数積 (a/b)·(b/a) = 1（B5 の掛けて 1 の素地・実等式） -/

/-- **avi_ratio_mul_swap**: a/b と b/a の積は 1。分子分母を入れ替えた比の積が
    (a·b)/(b·a) = 1 になる本物の ℚ 等式（prMul + Quot.sound、交差積
    a·b·1 = 1·(b·a) を Int.mul_comm で閉じる）。B5 で |x|_∞ = a/b に
    ∏_p|x|_p = b/a を掛けて 1 にする組み立ての中核。 -/
theorem avi_ratio_mul_swap (a b : Int) (ha : 0 < a) (hb : 0 < b) :
    ratRing.mul (avi_ratio a b hb) (avi_ratio b a ha) = Quot.mk ratRel prOne := by
  show Quot.mk ratRel (prMul ⟨a, b, hb⟩ ⟨b, a, ha⟩) = Quot.mk ratRel prOne
  apply Quot.sound
  show a * b * 1 = 1 * (b * a)
  rw [Int.mul_one, Int.one_mul, Int.mul_comm a b]

/-- **avi_abs_mul_recip**: num ≠ 0 のとき、アルキメデス側 |x|_∞ にその逆
    den/|num| を掛けると 1。すなわち |x|_∞·(b/a) = 1（a = |num|, b = den）。
    B5 積公式 |x|_∞·∏_p|x|_p = 1 で ∏_p|x|_p = b/a を掛けると 1 になる、その
    一因子（アルキメデス側）を実 ℚ 等式で確定したもの。 -/
theorem avi_abs_mul_recip (x : PreRat) (hx : x.num ≠ 0) :
    ratRing.mul (arpAbs (Quot.mk ratRel x))
      (avi_ratio x.den (intAbs x.num) (avi_intAbs_pos hx))
      = Quot.mk ratRel prOne := by
  rw [avi_abs_as_ratio x]
  exact avi_ratio_mul_swap (intAbs x.num) x.den (avi_intAbs_pos hx) x.den_pos

/-! ## ℚ の実素点データ（∞ の ArchPlace を含む束ね） -/

/-- **AviRationalPlaceData**: ℚ の実素点データのうち、B5 積公式アルキメデス側に
    必要な部分を束ねた実構造。∞ の `ArchPlace`（実アルキメデス絶対値 + 3 公理）に
    加え、(1) |x|_∞ = |num|/den の実 ℚ 等式、(2) 逆数積 (a/b)(b/a)=1 を持つ。 -/
structure AviRationalPlaceData where
  /-- ∞ の実アルキメデス素点（既存 ArchPlace）。 -/
  archPlace : ArchPlace
  /-- |x|_∞ = |num|/den（分子 intAbs num・分母 den の実 ℚ 等式）。 -/
  abs_num_den : ∀ x : PreRat,
    archPlace.abs (Quot.mk ratRel x)
      = Quot.mk ratRel (⟨intAbs x.num, x.den, x.den_pos⟩ : PreRat)
  /-- 逆数積 (a/b)·(b/a) = 1（B5 の掛けて 1 の素地）。 -/
  ratio_mul_swap : ∀ (a b : Int) (ha : 0 < a) (hb : 0 < b),
    ratRing.mul (avi_ratio a b hb) (avi_ratio b a ha) = Quot.mk ratRel prOne

/-- **witness**: ℚ の実素点データ（∞）。`arpPlaceQ` と本スライスの実等式で埋める。 -/
def aviRationalPlaceData : AviRationalPlaceData where
  archPlace := arpPlaceQ
  abs_num_den := avi_abs_num_den
  ratio_mul_swap := avi_ratio_mul_swap

/-- **capstone**: ℚ の実素点データ（B5 アルキメデス側）は存在する。 -/
theorem aviRationalPlaceData_exists : Nonempty AviRationalPlaceData :=
  ⟨aviRationalPlaceData⟩

end IUT
