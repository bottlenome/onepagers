/-
# M153F: apart 一般の逆元 — 符号二分法と負側の逆元（柱C、M145 の拡張）

M145 の正直申告「負の実数・apart（IsPos |x|）一般の逆元は符号分岐を
経由して次層」を解消する。apart 条件 IsPos (rabs x)（= x が 0 から
構成的に離れている）だけから乗法逆元の存在を導く。

  * M153F-1 `qAbs_of_nonneg` / `qAbs_of_nonpos` — ℚ の絶対値の符号場合
    分け（代表レベル: 分子の符号 + intAbs_of_nonneg/nonpos + preRat_ext）
  * M153F-2 **`isPos_abs_cases`（本丸1）** — 符号二分法
    IsPos |x| → IsPos x ∨ IsPos (−x)。witness 精度での qLe_total 分岐
    なので構成的（実数の符号判定そのものは決定不能だが、witness の
    「そのレベルの代表有理数」の符号は決定できる）
  * M153F-3 `rBound_neg` — 標準上界の反元不変性（qAbs_neg の Nat 等式）
  * M153F-4 `rmul_neg_right` / `rmul_neg_left` — 負号の引き出し
    x·(−y) ≈ −(x·y)・(−x)·y ≈ −(x·y)（rBound_neg で添字スケール K が
    一致し、点ごと qMul_neg_right/left で列が等しい）
  * M153F-5 `realNeg_neg` — 二重反元 −(−x) ≈ x（点ごと qNeg_neg）
  * M153F-6 **`apart_inv_exists`（本丸2）** — IsPos |x| なら
    ∃ y, x·y ≈ 1。正側は M145 の pos_inv_exists、負側は
    pos_inv_exists (−x) の逆元 y₀ に対して y = −y₀ を取り
    x·(−y₀) ≈ −(x·y₀) ≈ (−x)·y₀ ≈ 1 の合成
  * M153F-7 `ApartInvData` — 総括

意義: 構成的 apartness（IsPos |x|）だけから逆元が出る = 自前 ℝ が
**構成的（Heyting）体**の乗法逆元公理を満たす。対比として、論理的
非零 x ≠ 0（¬ realEq x 0）からは逆元は出ない — それは「¬¬apart →
apart」相当で排中律に相当する（Markov 原理の実数版）。ここも正直申告。

正直な限定: 逆元の一意性（y ≈ y'）・除算の代数法則（(x·y)⁻¹ ≈
y⁻¹·x⁻¹ など）・apart の加法两立（|x+y| 正 → |x| 正 ∨ |y| 正）は
次層。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealInv

namespace IUT

/-! ## M153F-1: ℚ の絶対値の符号場合分け -/

/-- **M153F-1a: 非負なら |a| = a** — 代表レベルで 0·den ≤ num·1 から
    分子非負を読み、intAbs_of_nonneg + preRat_ext。 -/
theorem qAbs_of_nonneg {a : QRat} (h : qLe ratRing.zero a) :
    qAbs a = a := by
  induction a using Quot.ind
  rename_i x
  have h' : (0 : Int) * x.den ≤ x.num * 1 := h
  have hnum : (0 : Int) ≤ x.num := by omega
  exact congrArg (Quot.mk ratRel) (preRat_ext (intAbs_of_nonneg hnum) rfl)

/-- **M153F-1b: 非正なら |a| = −a** — 代表レベルで num·1 ≤ 0·den から
    分子非正を読み、intAbs_of_nonpos + preRat_ext。 -/
theorem qAbs_of_nonpos {a : QRat} (h : qLe a ratRing.zero) :
    qAbs a = qNeg a := by
  induction a using Quot.ind
  rename_i x
  have h' : x.num * 1 ≤ (0 : Int) * x.den := h
  have hnum : x.num ≤ (0 : Int) := by omega
  exact congrArg (Quot.mk ratRel) (preRat_ext (intAbs_of_nonpos hnum) rfl)

/-! ## M153F-2: 符号二分法（本丸1） -/

/-- **定理 (M153F-2): 符号二分法** IsPos |x| → IsPos x ∨ IsPos (−x)。
    witness ⟨n, 2/(n+1) ≤ |xₙ|⟩ に対し qLe_total で xₙ の符号を判定:
    0 ≤ xₙ なら |xₙ| = xₙ で右辺そのまま IsPos x の witness、
    xₙ ≤ 0 なら |xₙ| = −xₙ = (realNeg x)ₙ（defeq）で IsPos (−x) の
    witness。実数そのものの符号判定は決定不能だが、witness レベルの
    代表有理数の符号は qLe_total で決定できる — ここが構成的に通る鍵。 -/
theorem isPos_abs_cases (x : RReal) (h : IsPos (rabs x)) :
    IsPos x ∨ IsPos (realNeg x) := by
  obtain ⟨n, hn⟩ := h
  have hn' : qLe (qFrac 2 n) (qAbs (x.seq n)) := hn
  cases qLe_total (x.seq n) ratRing.zero with
  | inl hle =>
    rw [qAbs_of_nonpos hle] at hn'
    exact Or.inr ⟨n, hn'⟩
  | inr hge =>
    rw [qAbs_of_nonneg hge] at hn'
    exact Or.inl ⟨n, hn'⟩

/-! ## M153F-3: 標準上界の反元不変性 -/

/-- **M153F-3: rBound (−x) = rBound x** — rBound の定義
    qFloorNat (qAbs (x₀)) + 3 の中の qAbs (qNeg x₀) を qAbs_neg で潰す
    Nat 等式（(realNeg x).seq 0 = qNeg (x.seq 0) は defeq）。 -/
theorem rBound_neg (x : RReal) : rBound (realNeg x) = rBound x := by
  show qFloorNat (qAbs (qNeg (x.seq 0))) + 3
    = qFloorNat (qAbs (x.seq 0)) + 3
  rw [qAbs_neg]

/-! ## M153F-4: 負号の引き出し -/

/-- **定理 (M153F-4a): 右反元の引き出し** x·(−y) ≈ −(x·y)。
    rBound_neg で両辺の添字スケール K = rBound x + rBound y が一致し、
    点ごと qMul_neg_right で列が等しい（realEq_of_seq_eq）。 -/
theorem rmul_neg_right (x y : RReal) :
    realEq (rmul x (realNeg y)) (realNeg (rmul x y)) := by
  apply realEq_of_seq_eq
  intro n
  show qMul (x.seq (mulIdx (rBound x + rBound (realNeg y)) n))
      (qNeg (y.seq (mulIdx (rBound x + rBound (realNeg y)) n)))
    = qNeg (qMul (x.seq (mulIdx (rBound x + rBound y) n))
      (y.seq (mulIdx (rBound x + rBound y) n)))
  rw [rBound_neg y, qMul_neg_right]

/-- **定理 (M153F-4b): 左反元の引き出し** (−x)·y ≈ −(x·y)（4a と対称、
    点ごと qMul_neg_left）。 -/
theorem rmul_neg_left (x y : RReal) :
    realEq (rmul (realNeg x) y) (realNeg (rmul x y)) := by
  apply realEq_of_seq_eq
  intro n
  show qMul (qNeg (x.seq (mulIdx (rBound (realNeg x) + rBound y) n)))
      (y.seq (mulIdx (rBound (realNeg x) + rBound y) n))
    = qNeg (qMul (x.seq (mulIdx (rBound x + rBound y) n))
      (y.seq (mulIdx (rBound x + rBound y) n)))
  rw [rBound_neg x, qMul_neg_left]

/-! ## M153F-5: 二重反元 -/

/-- **M153F-5: −(−x) ≈ x**（点ごと qNeg_neg で列が等しい）。 -/
theorem realNeg_neg (x : RReal) : realEq (realNeg (realNeg x)) x :=
  realEq_of_seq_eq (fun n => qNeg_neg (x.seq n))

/-! ## M153F-6: apart 一般の逆元存在（本丸2） -/

/-- **定理 (M153F-6): apart 実数の逆元存在** — IsPos |x| なら
    ∃ y, x·y ≈ 1。符号二分法で分岐:
    正側は M145 の pos_inv_exists そのまま、
    負側は pos_inv_exists (−x) の逆元 y₀（(−x)·y₀ ≈ 1）に対し
    y = −y₀ を取り、x·(−y₀) ≈ −(x·y₀) ≈ (−x)·y₀ ≈ 1 の合成
    （rmul_neg_right → rmul_neg_left の逆読み → hy₀）。
    ∃ から ∃ への写像なので witness 抽出（choice）は不要。 -/
theorem apart_inv_exists (x : RReal) (h : IsPos (rabs x)) :
    ∃ y : RReal, realEq (rmul x y) (qToReal ratRing.one) := by
  cases isPos_abs_cases x h with
  | inl hp => exact pos_inv_exists x hp
  | inr hn =>
    obtain ⟨y₀, hy₀⟩ := pos_inv_exists (realNeg x) hn
    refine ⟨realNeg y₀, ?_⟩
    exact realEq_trans (rmul_neg_right x y₀)
      (realEq_trans (realEq_symm (rmul_neg_left x y₀)) hy₀)

/-! ## M153F-7: 総括 -/

/-- **M153F-7a: 総括** — apart 逆元のデータ。 -/
structure ApartInvData where
  /-- 符号二分法。 -/
  sign_cases : ∀ x : RReal, IsPos (rabs x) → IsPos x ∨ IsPos (realNeg x)
  /-- 右反元の引き出し。 -/
  neg_right : ∀ x y : RReal, realEq (rmul x (realNeg y)) (realNeg (rmul x y))
  /-- 左反元の引き出し。 -/
  neg_left : ∀ x y : RReal, realEq (rmul (realNeg x) y) (realNeg (rmul x y))
  /-- 二重反元。 -/
  neg_neg : ∀ x : RReal, realEq (realNeg (realNeg x)) x
  /-- apart 実数の逆元存在（Heyting 体の乗法逆元公理）。 -/
  apart_inv : ∀ x : RReal, IsPos (rabs x) →
    ∃ y : RReal, realEq (rmul x y) (qToReal ratRing.one)

/-- **M153F-7b: witness**。 -/
def apartInvData : ApartInvData where
  sign_cases := isPos_abs_cases
  neg_right := rmul_neg_right
  neg_left := rmul_neg_left
  neg_neg := realNeg_neg
  apart_inv := apart_inv_exists

/-- **M153F-7c: 存在**。 -/
theorem apartInv_exists : Nonempty ApartInvData := ⟨apartInvData⟩

end IUT
