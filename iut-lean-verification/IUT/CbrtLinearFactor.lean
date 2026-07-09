/-
  IUT/CbrtLinearFactor.lean — CLF（A1 実数体 ℚ(∛2) = ℚ[x]/(x³−2) の
  既約性の葉補題・Wave 1 / N4）

  ── 分類 **[実／承認済み足場(c)]**（本物の先行建設への足場。骨格でなく
  実 ℚ・実 f = x³−2 の本物の評価計算・sorry 皆無・新規 Classical.choice
  皆無・模型ゼロ）。名前付き実ターゲット: A1「実数体 K = ℚ[x]/(f) を実際の
  商環として構成」の Bezout（イデアル極大性・Wave 2 = N7 = `cbrtTwo_bezout`）
  が消費する「一次因子 ⟹ 有理立方根」の葉補題（設計書
  `audit/A1-real-numberfield-plan.md` §3）。後続: N7 でこの生産物
  `∃t, t³ = 2` を親スライスの `no_rat_cube_two`（∀t, t³ ≠ 2）で反駁し、
  三次多項式 f = x³−2 の既約性（一次因子を持たない）を確立して
  イデアル (f) の極大性 = 体化（Wave 3）へつなぐ。

  **complete_pct 影響**: 本層単体では **complete_pct 未設定（0 前進）**。
  A1 の complete_pct はイデアル極大性（Wave 2）と体化（Wave 3）が本物で
  揃った時に動かす。本層はその「本コース」への計算的難所を実 ℚ の評価
  準同型 M274F（evalSum/evalHom_id_mul/evalHom_stable）だけで本当に閉じ、
  水増しの束ねではなく後続 Wave が import する既約性入力を実 ℚ・実 f で
  確定する。

  内容（設計 §3 の葉補題）:
   * `clf_g_eval` — 一次因子 g（g 1 ≠ 0）の根 t := −(g₀·g₁⁻¹) での評価
     ev_t(g)|₂ = g₀·1 + g₁·t = 0（`qMul_inv` = `ratIUTField.mul_inv_cancel`
     で g₁·(g₀/g₁) = g₀、add_neg で消える）。
   * `clf_root_of_eval` — 抽象根 t で ev_t(g)|₂ = 0 なら、f = w·g の
     打ち切り評価 ev_t(f)|₄ = ev_t(w)·ev_t(g) = ev_t(w)·0 = 0（`evalHom_id_mul`
     + `evalHom_stable`）から f の係数展開 t³ + (−2) = 0 を取り、t³ = 2 を導く。
   * `clf_linear_factor_root`（主定理・§3）— f = x³−2 が一次因子 g を持つなら
     ∃t : ℚ, t·(t·t) = 2（= ct0Two）を **生産**する（矛盾はここでは出さず
     依存を切る。設計 §3 の外部インターフェース分離）。

  正直な限定（本層に含めないもの・§4 規約により消さない）:
   - **矛盾は出さない**: 本層は `∃t, t³ = 2` を生産するだけで、それが偽で
     ある（∛2 ∉ ℚ）ことは親スライスの `no_rat_cube_two` が供給し、
     Wave 2（`cbrtTwo_bezout`）だけが消費する（設計 §3）。
   - **単一 f = x³−2 のみ**。一般既約 f の一次因子論は未達（設計 §5 の
     名前付き後続）。
   - 逆元は後続でも ∃ 形（全域 inv 付き IUTField 昇格は別スライス）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.CbrtTwoBase
import IUT.EvaluationHom
import IUT.PolyPSUtil
import IUT.Field
import IUT.LubinTateZp
import IUT.LTErrorDivisible
import IUT.Binomial2

namespace IUT

/-! ## CLF-1: 一次因子の根での評価が消える -/

/-- **CLF-1: 根 t = −(g₀·g₁⁻¹) での一次因子 g の評価は 0** —
    ev_t(g)|₂ = g₀·α⁰ + g₁·α¹ = g₀ + g₁·t。t の定義と `qMul_inv`
    （= `ratIUTField.mul_inv_cancel`, g₁ ≠ 0）で g₁·t = g₁·(−g₀·g₁⁻¹)
    = −(g₀·(g₁·g₁⁻¹)) = −g₀、add_neg で g₀ + (−g₀) = 0。 -/
theorem clf_g_eval (g : PS ratRing) (hg1 : g 1 ≠ ratRing.zero) :
    evalSum (evalHomId ratRing)
      (ratRing.neg (ratRing.mul (g 0) (qInv (g 1)))) g 2 = ratRing.zero := by
  show ratRing.add (ratRing.add ratRing.zero
      (ratRing.mul (g 0)
        (rpow ratRing (ratRing.neg (ratRing.mul (g 0) (qInv (g 1)))) 0)))
      (ratRing.mul (g 1)
        (rpow ratRing (ratRing.neg (ratRing.mul (g 0) (qInv (g 1)))) 1))
    = ratRing.zero
  rw [show rpow ratRing (ratRing.neg (ratRing.mul (g 0) (qInv (g 1)))) 0
        = ratRing.one from rfl,
    show rpow ratRing (ratRing.neg (ratRing.mul (g 0) (qInv (g 1)))) 1
        = ratRing.mul ratRing.one (ratRing.neg (ratRing.mul (g 0) (qInv (g 1))))
        from rfl,
    ratRing.one_mul (ratRing.neg (ratRing.mul (g 0) (qInv (g 1)))),
    CRing.mul_one ratRing (g 0),
    ratRing.zero_add (g 0)]
  have hinv : ratRing.mul (g 1) (qInv (g 1)) = ratRing.one :=
    ratIUTField.mul_inv_cancel (g 1) hg1
  have hmid : ratRing.mul (g 1) (ratRing.mul (g 0) (qInv (g 1))) = g 0 := by
    rw [← ratRing.mul_assoc, ratRing.mul_comm (g 1) (g 0), ratRing.mul_assoc,
      hinv, CRing.mul_one ratRing (g 0)]
  rw [CRing.mul_neg ratRing (g 1) (ratRing.mul (g 0) (qInv (g 1))), hmid]
  exact CRing.add_neg ratRing (g 0)

/-! ## CLF-2: 抽象根での評価 0 から t³ = 2 を導く -/

/-- **CLF-2: 抽象根での t³ = 2** — 抽象 t で ev_t(g)|₂ = 0（`hA`）かつ
    f = w·g（`heq`）なら、`evalHom_id_mul`（M274F-9c）で
    ev_t(f)|_{Nw'+2+1} = ev_t(w)·ev_t(g) = ev_t(w)·0 = 0、
    `evalHom_stable`（M274F-3）で打ち切り点 4 と同定し、f = x³−2 の係数
    展開 ev_t(f)|₄ = (−2) + t³ から (−2) + t³ = 0、移項で t³ = 2。 -/
theorem clf_root_of_eval (w g : PS ratRing) (Nw : Nat) (t : QRat)
    (hw : IsPolyBounded ratRing w Nw)
    (hg : IsPolyBounded ratRing g 2)
    (hA : evalSum (evalHomId ratRing) t g 2 = ratRing.zero)
    (heq : ct0PS = psMul ratRing w g) :
    ratRing.mul t (ratRing.mul t t) = ct0Two := by
  have hw' : IsPolyBounded ratRing w (Nw + 1) :=
    ppu_bounded_mono ratRing (by omega) hw
  have hmul : evalSum (evalHomId ratRing) t (psMul ratRing w g) (Nw + 1 + 2 + 1)
      = ratRing.mul (evalSum (evalHomId ratRing) t w (Nw + 1))
          (evalSum (evalHomId ratRing) t g 2) :=
    evalHom_id_mul ratRing t w g (Nw + 1) 2 hw' hg
  have hzero_mul : evalSum (evalHomId ratRing) t (psMul ratRing w g) (Nw + 1 + 2 + 1)
      = ratRing.zero := by
    rw [hmul, hA]
    exact CRing.mul_zero ratRing (evalSum (evalHomId ratRing) t w (Nw + 1))
  have hct4' : evalSum (evalHomId ratRing) t ct0PS (Nw + 1 + 2 + 1) = ratRing.zero := by
    rw [heq]; exact hzero_mul
  have hstab : evalSum (evalHomId ratRing) t ct0PS (Nw + 1 + 2 + 1)
      = evalSum (evalHomId ratRing) t ct0PS 4 :=
    evalHom_stable (evalHomId ratRing) t ct0PS 4 ct0_bound (Nw + 1 + 2 + 1) (by omega)
  have hct4 : evalSum (evalHomId ratRing) t ct0PS 4 = ratRing.zero := by
    rw [← hstab]; exact hct4'
  have hexpand : evalSum (evalHomId ratRing) t ct0PS 4
      = ratRing.add cbpNegTwo (rpow ratRing t 3) := by
    show ratRing.add (ratRing.add (ratRing.add (ratRing.add ratRing.zero
        (ratRing.mul (ct0PS 0) (rpow ratRing t 0)))
        (ratRing.mul (ct0PS 1) (rpow ratRing t 1)))
        (ratRing.mul (ct0PS 2) (rpow ratRing t 2)))
        (ratRing.mul (ct0PS 3) (rpow ratRing t 3))
      = ratRing.add cbpNegTwo (rpow ratRing t 3)
    rw [ct0PS_coeff0, ct0PS_coeff1, ct0PS_coeff2, ct0PS_coeff3,
      show rpow ratRing t 0 = ratRing.one from rfl,
      CRing.mul_one ratRing cbpNegTwo,
      CRing.zero_mul ratRing (rpow ratRing t 1),
      CRing.zero_mul ratRing (rpow ratRing t 2),
      ratRing.one_mul (rpow ratRing t 3),
      ratRing.zero_add cbpNegTwo,
      CRing.add_zero ratRing cbpNegTwo,
      CRing.add_zero ratRing cbpNegTwo]
  have hkey : ratRing.add cbpNegTwo (rpow ratRing t 3) = ratRing.zero := by
    rw [← hexpand]; exact hct4
  have hneg : cbpNegTwo = ratRing.neg ct0Two := by
    show ratOfInt.map (-2 : Int) = ratRing.neg (ratOfInt.map (2 : Int))
    exact RingHom.map_neg ratOfInt (2 : Int)
  have hrp3 : rpow ratRing t 3 = ct0Two := by
    apply CRing.eq_of_sub_eq_zero ratRing
    rw [← hneg, ratRing.add_comm (rpow ratRing t 3) cbpNegTwo]
    exact hkey
  show ratRing.mul t (ratRing.mul t t) = ct0Two
  rw [← hrp3]
  show ratRing.mul t (ratRing.mul t t)
    = ratRing.mul (ratRing.mul (ratRing.mul ratRing.one t) t) t
  rw [ratRing.one_mul t]
  exact (ratRing.mul_assoc t t t).symm

/-! ## CLF-3: 主定理 — 一次因子 ⟹ 有理立方根の生産 -/

/-- **CLF-3（主定理・設計 §3 葉補題）: f = x³−2 の一次因子は有理立方根を生む** —
    f = w·g で g が一次（`hg : IsPolyBounded g 2`・`hg1 : g 1 ≠ 0`）なら、
    根 t := −(g₀·g₁⁻¹) が t³ = 2（= ct0Two）を満たす。矛盾はここでは出さず
    ∃t を **生産**するだけにして親スライス `no_rat_cube_two` への依存を切る
    （設計 §3）。証明は `clf_g_eval`（根での一次因子の消滅）と
    `clf_root_of_eval`（積の評価 + 係数展開 + 移項）の合成。 -/
theorem clf_linear_factor_root (w g : PS ratRing) (Nw : Nat)
    (hw : IsPolyBounded ratRing w Nw) (hg : IsPolyBounded ratRing g 2)
    (hg1 : g 1 ≠ ratRing.zero) (heq : ct0PS = psMul ratRing w g) :
    ∃ t : QRat, ratRing.mul t (ratRing.mul t t) = ct0Two :=
  ⟨ratRing.neg (ratRing.mul (g 0) (qInv (g 1))),
    clf_root_of_eval w g Nw (ratRing.neg (ratRing.mul (g 0) (qInv (g 1))))
      hw hg (clf_g_eval g hg1) heq⟩

end IUT

#print axioms IUT.clf_linear_factor_root
