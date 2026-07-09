/-
  IUT/CbrtCofactor.lean — CCO（A1 実数体 ℚ(∛2) = ℚ[x]/(x³−2) の
  Wave 1 / N6: 完全割り葉の余因子が一次であること・頂点係数論法）

  ── 分類 **[実／承認済み足場(c)]**（本物の先行建設への足場。骨格でなく
  実 ℚ・実 f = x³−2 の本物の頂点係数論法・sorry 皆無・新規 Classical.choice
  皆無・模型ゼロ）。名前付き実ターゲット: A1「実数体 K = ℚ[x]/(f) を実際の
  商環として構成」の最初の本物のインスタンス **実三次数体 ℚ(∛2)**（設計書
  `audit/A1-real-numberfield-plan.md` §2.4）。本層は Wave 2（N7 = 本丸
  `cbrtTwo_bezout`）のユークリッド鎖の「完全割り葉」で、
  ct0PS = q₁·r（r 二次・r₂≠0）から**余因子 q₁ が一次**（q₁₂=0・q₁₁≠0）で
  あることを、既存 M268F の頂点係数公式で本物に取り出す。後続 Wave 2 が
  この一次性を使い「r×q₁ を葉補題（N4 `cbrt_linear_factor_root`）に g:=q₁
  で渡す」。

  **complete_pct 影響**: 本層単体では **complete_pct 未設定（0 前進）**。
  A1 の complete_pct はイデアル極大性（Wave 2）と体化（Wave 3）が本物で
  揃った時に動かす。本層はその「本コース」への足場（頂点係数論法の本物実装）
  であり、水増しの束ねではない。

  内容（設計 §2.4）:
   * `cco_cofactor_deg2_top` — ct0PS = q₁·r（r 二次 bound 3・r₂≠0、q₁ bound 3）
     から **q₁₂ = 0**。核: `psMul_g_top_coeff268`（M268F-6a）で
     (q₁·r)₄ = q₁₂·r₂、`ct0_bound` で ct0PS 4 = 0 ⟹ q₁₂·r₂ = 0、
     `mul_eq_zero_left268`（M268F-2、invf=qInv・r₂≠0）で q₁₂ = 0。
   * `cco_cofactor_deg1_nonzero` — 同前提で **q₁₁ ≠ 0**。核: q₁₂=0 で q₁ を
     bound 2 に締め、(q₁·r)₃ = q₁₁·r₂、`ct0PS_coeff3` で ct0PS 3 = 1 ⟹
     q₁₁·r₂ = 1。もし q₁₁=0 なら 0 = 1 で `one_ne_zero ratIUTField` に反する。
   * `cco_cofactor_linear` — まとめ: `IsPolyBounded ratRing q₁ 2 ∧ q₁ 1 ≠ 0`
     （q₁ が bound 2 頂点 q₁₁≠0 の一次多項式であることの本物の証明）。

  既存 M268F 補題の実例化:
   - `psMul_g_top_coeff268 ratRing r 2 hr q₁ M hw` — 右因子 g:=r（m=2、
     bound 3 = m+1）、左因子 w:=q₁。M=2 で (q₁·r)₄=q₁₂·r₂、M=1 で
     (q₁·r)₃=q₁₁·r₂（q₁ を bound 2 に締めた hw を渡す）。
   - `mul_eq_zero_left268 ratRing qInv ratIUTField.mul_inv_cancel hr2 _`
     — 体の整域性（invf=qInv、hinv=ratIUTField.mul_inv_cancel）。

  正直な限定（本層に含めないもの・§4 規約により消さない）:
   - 本層は「完全割り葉が実際に起きる」ことは示さない（前提として受ける）。
     ユークリッド鎖の分岐で完全割りが起きた葉でだけ本層を呼ぶのは Wave 2。
   - r が二次であること（r₂≠0）も前提。r の次数場合分けは Wave 2 の主語。
   - 単一 f = x³−2 のみ（一般既約 f は設計 §5 の名前付き後続）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.CbrtTwoBase
import IUT.PolyFieldDivision
import IUT.SimpleExtension
import IUT.RatZeroDecide
import IUT.Field

namespace IUT

/-! ## CCO-1: 余因子の二次係数は消える（頂点係数論法・その1） -/

/-- **CCO-1 (`cco_cofactor_deg2_top`)**: ct0PS = q₁·r で r が二次（bound 3・
    先頭 r₂ ≠ 0）、q₁ が bound 3 なら **q₁ の二次係数は 0**。
    頂点係数論法: 積の 4 次係数 (q₁·r)₄ = q₁₂·r₂（`psMul_g_top_coeff268`、
    右因子 r の m=2・左因子 q₁ の M=2）だが ct0PS 4 = 0（`ct0_bound`）なので
    q₁₂·r₂ = 0、r₂ ≠ 0 の整域性（`mul_eq_zero_left268`）で q₁₂ = 0。 -/
theorem cco_cofactor_deg2_top
    (q₁ r : PS ratRing)
    (hq1 : IsPolyBounded ratRing q₁ 3)
    (hr : IsPolyBounded ratRing r 3)
    (hr2 : r 2 ≠ ratRing.zero)
    (heq : ct0PS = psMul ratRing q₁ r) :
    q₁ 2 = ratRing.zero := by
  have htop : psMul ratRing q₁ r (2 + 2) = ratRing.mul (q₁ 2) (r 2) :=
    psMul_g_top_coeff268 ratRing r 2 hr q₁ 2 hq1
  have hz : ratRing.mul (q₁ 2) (r 2) = ratRing.zero := by
    rw [← htop, ← heq]
    exact ct0_bound (2 + 2) (by omega)
  exact mul_eq_zero_left268 ratRing qInv ratIUTField.mul_inv_cancel hr2 hz

/-! ## CCO-2: 余因子の一次係数は非零（頂点係数論法・その2） -/

/-- **CCO-2 (`cco_cofactor_deg1_nonzero`)**: 同前提で **q₁ の一次係数は
    ≠ 0**。q₁₂ = 0（CCO-1）で q₁ は bound 2 に締まる。積の 3 次係数
    (q₁·r)₃ = q₁₁·r₂（`psMul_g_top_coeff268`、M=1）で、ct0PS 3 = 1
    （`ct0PS_coeff3`）ゆえ q₁₁·r₂ = 1。もし q₁₁ = 0 なら 0·r₂ = 0 = 1 で
    `one_ne_zero ratIUTField`（実 ℚ の非自明性）に反する。 -/
theorem cco_cofactor_deg1_nonzero
    (q₁ r : PS ratRing)
    (hq1 : IsPolyBounded ratRing q₁ 3)
    (hr : IsPolyBounded ratRing r 3)
    (hr2 : r 2 ≠ ratRing.zero)
    (heq : ct0PS = psMul ratRing q₁ r) :
    q₁ 1 ≠ ratRing.zero := by
  have hq2 : q₁ 2 = ratRing.zero := cco_cofactor_deg2_top q₁ r hq1 hr hr2 heq
  -- q₁ を bound 2 に締める（i = 2 は hq2、i ≥ 3 は hq1）。
  have hq1' : ∀ i, 2 ≤ i → q₁ i = ratRing.zero := by
    intro i hi
    cases Nat.lt_or_ge i 3 with
    | inl hlt =>
      rw [show i = 2 from by omega]
      exact hq2
    | inr hge => exact hq1 i hge
  have htop : psMul ratRing q₁ r (1 + 2) = ratRing.mul (q₁ 1) (r 2) :=
    psMul_g_top_coeff268 ratRing r 2 hr q₁ 1 hq1'
  have h3 : ratRing.mul (q₁ 1) (r 2) = ratRing.one := by
    rw [← htop, ← heq]
    exact ct0PS_coeff3
  intro hz0
  have hcontra : ratRing.one = ratRing.zero := by
    rw [← h3, hz0]
    exact CRing.zero_mul ratRing (r 2)
  exact ratIUTField.one_ne_zero hcontra

/-! ## CCO-3: 余因子は一次（まとめ） -/

/-- **CCO-3 (`cco_cofactor_linear`)**: ct0PS = q₁·r（r 二次・r₂≠0、q₁ bound 3）
    の完全割り葉では **余因子 q₁ は一次**: `IsPolyBounded ratRing q₁ 2`
    （二次以上の係数が消える）かつ `q₁ 1 ≠ 0`（一次係数は非零）。
    後続 Wave 2 が「r × q₁ を葉補題（N4）に g:=q₁ で渡す」ために使う一次性。 -/
theorem cco_cofactor_linear
    (q₁ r : PS ratRing)
    (hq1 : IsPolyBounded ratRing q₁ 3)
    (hr : IsPolyBounded ratRing r 3)
    (hr2 : r 2 ≠ ratRing.zero)
    (heq : ct0PS = psMul ratRing q₁ r) :
    IsPolyBounded ratRing q₁ 2 ∧ q₁ 1 ≠ ratRing.zero := by
  have hq2 : q₁ 2 = ratRing.zero := cco_cofactor_deg2_top q₁ r hq1 hr hr2 heq
  have hne : q₁ 1 ≠ ratRing.zero :=
    cco_cofactor_deg1_nonzero q₁ r hq1 hr hr2 heq
  refine ⟨?_, hne⟩
  intro i hi
  cases Nat.lt_or_ge i 3 with
  | inl hlt =>
    rw [show i = 2 from by omega]
    exact hq2
  | inr hge => exact hq1 i hge

end IUT
