/-
  IUT/Cq3BezoutChain.lean — CQ1（A1 実数体 ℚ(ζ₃) = ℚ[x]/(x²+x+1) の
  SimpleExtData.bezout 充填 = 次数2固定ユークリッド鎖・本丸 + 一次因子葉補題）

  ── 分類 **[実／承認済み足場(c)]**（本物の先行建設。骨格でなく実 ℚ・実
  f = Φ₃ = x²+x+1（円分多項式）の**イデアル極大性そのものの完全証明**・
  sorry 皆無・新規 Classical.choice 皆無・模型ゼロ）。名前付き実ターゲット:
  A1「実数体 K = ℚ[x]/(f) を実際の商環として構成」の第二の本物のインスタンス
  **実二次数体 ℚ(ζ₃)**（ℚ(∛2) 建設 `CbrtBezoutChain`（CBC）の**次数2版
  アナロジー**）。本層は `Cq3Base`（CQ0）が bezout 以外の全 field を確定した
  `SimpleExtData` の唯一の残件 `SimpleExtData.bezout`（f のイデアルが極大 =
  割り切れない任意元と互いに素）を、f = x²+x+1 で **本物に証明**する。
  deg Φ₃ = 2 なので剰余次数が 2→1→0 と最大 2 回の除法で必ず停止する有限深度
  ユークリッド鎖（x³−2 版 CBC の 3 回より 1 段浅い）を、既存の実部品
  （field_division_exists・cbz_const/cbz_descend・clf_g_eval・
  cq0_no_rat_root・rzd_zero_or_ne）の合成だけで組み立てる。完全割り葉は
  1 種類（Φ₃ = q₁·r で r 一次）で、そこでの矛盾は本物の **`cq0_no_rat_root`
  （Φ₃ は有理根を持たない）**に本当に落ちる（surrogate 反駁ではない）。

  **complete_pct 影響**: 本タスクでは complete_pct は**未設定（動かさない）**
  （親が ℚ(ζ₃) 体化と併せて A1 二軸を更新する）。本層はイデアル極大性の
  本物の充填であり、水増しの束ねではない。

  内容:
   * cq1_root_of_eval — 抽象根 t で ev_t(g)|₂ = 0 かつ Φ₃ = w·g なら、
     Φ₃ の打ち切り評価 ev_t(Φ₃)|₃ = ev_t(w)·ev_t(g) = 0 から係数展開
     ev_t(Φ₃)|₃ = t²+t+1 を取り、t²+t+1 = 0 を導く（evalHom_id_mul +
     evalHom_stable、CBC の clf_root_of_eval の次数2版）。
   * cq1_linear_factor_root — 一次因子葉補題: Φ₃ = w·g で g 一次
     （g 1 ≠ 0）なら根 t := −(g₀·g₁⁻¹) が t²+t+1 = 0 を満たす（∃t を生産、
     clf_g_eval の生成物 + cq1_root_of_eval の合成）。
   * cq1_refute — refutation アダプタ: cq1_linear_factor_root の ∃t を
     `cq0_no_rat_root`（∀r, r²+r+1 ≠ 0）で反駁して False。
   * cq1_idealRel_zero_iff — idealRel P Φ₃ a 0 ↔ ∃ h, a = h·Φ₃
     （neg_zero/add_zero、CBC cbc_idealRel_zero_iff の次数2版）。
   * cq1_bezB_cq0 — PS レベルの鎖本体（4 葉）: a ÷ cq0PS の剰余 r（次数 ≤ 1）
     の係数零判定（rzd_zero_or_ne）で最大 2 重に場合分けし、非零定数葉は
     cbz_const、割り切れ葉（Φ₃ = q₁·r で r 一次因子）は cq1_linear_factor_root
     + cq1_refute で矛盾、完全割り（r=0）は idealRel を作って前提と矛盾。各段の
     Bezout は cbz_descend で降下し BezB(a, cq0PS) を得る。
   * cq1_bezout — 本丸: SimpleExtData.bezout の型そのもの。PS 版を
     Poly（Subtype）へ梱包し、u·Φ₃ + v·a = 1 の Poly 等式を ppu_poly_ext で
     組む。前提 ¬idealRel は cq1_idealRel_zero_iff で PS 版 ¬∃q へ翻訳。

  正直な限定（§4 規約により消さない）:
   - **単一 f = x²+x+1 のみ**。一般既約 f への Bezout（一般拡張ユークリッド
     互除法 + 一般次数簿記）は未達（CBC と同じく名前付き後続）。
   - 逆元は後続でも ∃ 形（全域 inv 付き IUTField 昇格は別スライス）。
   - 有理根なし（Φ₃ の一次因子なし）は既に `cq0_no_rat_root`（本物）で
     閉じているため本層に仮説引数は残らない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.Cq3Base
import IUT.CbrtBezB
import IUT.CbrtLinearFactor
import IUT.RatZeroDecide
import IUT.PolyPSUtil
import IUT.PolyFieldDivision
import IUT.SimpleExtension
import IUT.EvaluationHom

namespace IUT

/-! ## CQ1-1: 抽象根での評価 0 から t²+t+1 = 0 を導く -/

/-- **CQ1-1: 抽象根での t²+t+1 = 0** — 抽象 t で ev_t(g)|₂ = 0（`hA`）かつ
    Φ₃ = w·g（`heq`）なら、`evalHom_id_mul`（M274F-9c）で
    ev_t(Φ₃)|_{Nw+1+2+1} = ev_t(w)·ev_t(g) = ev_t(w)·0 = 0、
    `evalHom_stable`（M274F-3）で打ち切り点 3 と同定し、Φ₃ = x²+x+1 の係数
    展開 ev_t(Φ₃)|₃ = ((1 + t) + t²) を並べ替えて (t²+t)+1 = 0。CBC
    `clf_root_of_eval` の次数2版（打ち切り 4→3・係数 −2,0,0,1 → 1,1,1）。 -/
theorem cq1_root_of_eval (w g : PS ratRing) (Nw : Nat) (t : QRat)
    (hw : IsPolyBounded ratRing w Nw)
    (hg : IsPolyBounded ratRing g 2)
    (hA : evalSum (evalHomId ratRing) t g 2 = ratRing.zero)
    (heq : cq0PS = psMul ratRing w g) :
    ratRing.add (ratRing.add (ratRing.mul t t) t) ratRing.one = ratRing.zero := by
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
  have hcq' : evalSum (evalHomId ratRing) t cq0PS (Nw + 1 + 2 + 1) = ratRing.zero := by
    rw [heq]; exact hzero_mul
  have hstab : evalSum (evalHomId ratRing) t cq0PS (Nw + 1 + 2 + 1)
      = evalSum (evalHomId ratRing) t cq0PS 3 :=
    evalHom_stable (evalHomId ratRing) t cq0PS 3 cq0_bound (Nw + 1 + 2 + 1) (by omega)
  have hcq3 : evalSum (evalHomId ratRing) t cq0PS 3 = ratRing.zero := by
    rw [← hstab]; exact hcq'
  have hval : evalSum (evalHomId ratRing) t cq0PS 3
      = ratRing.add (ratRing.add (ratRing.mul t t) t) ratRing.one := by
    show ratRing.add (ratRing.add (ratRing.add ratRing.zero
        (ratRing.mul (cq0PS 0) (rpow ratRing t 0)))
        (ratRing.mul (cq0PS 1) (rpow ratRing t 1)))
        (ratRing.mul (cq0PS 2) (rpow ratRing t 2))
      = ratRing.add (ratRing.add (ratRing.mul t t) t) ratRing.one
    rw [cq0PS_coeff0, cq0PS_coeff1, cq0PS_coeff2,
      show rpow ratRing t 0 = ratRing.one from rfl,
      show rpow ratRing t 1 = ratRing.mul ratRing.one t from rfl,
      show rpow ratRing t 2 = ratRing.mul (ratRing.mul ratRing.one t) t from rfl,
      ratRing.one_mul ratRing.one,
      ratRing.zero_add ratRing.one,
      ratRing.one_mul (ratRing.mul (ratRing.mul ratRing.one t) t),
      ratRing.one_mul t, ratRing.one_mul t,
      ratRing.add_assoc ratRing.one t (ratRing.mul t t),
      ratRing.add_comm ratRing.one (ratRing.add t (ratRing.mul t t)),
      ratRing.add_comm t (ratRing.mul t t)]
  rw [← hval]; exact hcq3

/-! ## CQ1-2: 一次因子葉補題 — 一次因子 ⟹ Φ₃ の有理根の生産 -/

/-- **CQ1-2: Φ₃ = x²+x+1 の一次因子は有理根を生む** — Φ₃ = w·g で g が一次
    （`hg : IsPolyBounded g 2`・`hg1 : g 1 ≠ 0`）なら、根 t := −(g₀·g₁⁻¹) が
    t²+t+1 = 0 を満たす。矛盾はここでは出さず ∃t を **生産**する（CBC
    clf_linear_factor_root の次数2版）。証明は `clf_g_eval`（根での一次因子の
    消滅・次数によらない汎用）と `cq1_root_of_eval`（積の評価 + 係数展開 +
    並べ替え）の合成。 -/
theorem cq1_linear_factor_root (w g : PS ratRing) (Nw : Nat)
    (hw : IsPolyBounded ratRing w Nw) (hg : IsPolyBounded ratRing g 2)
    (hg1 : g 1 ≠ ratRing.zero) (heq : cq0PS = psMul ratRing w g) :
    ∃ t : QRat, ratRing.add (ratRing.add (ratRing.mul t t) t) ratRing.one
      = ratRing.zero :=
  ⟨ratRing.neg (ratRing.mul (g 0) (qInv (g 1))),
    cq1_root_of_eval w g Nw (ratRing.neg (ratRing.mul (g 0) (qInv (g 1))))
      hw hg (clf_g_eval g hg1) heq⟩

/-! ## CQ1-3: refutation アダプタ -/

/-- **CQ1-3: refutation アダプタ** — `cq1_linear_factor_root` の生産物
    `∃ t, t²+t+1 = 0` を `cq0_no_rat_root`（`∀ r, r²+r+1 ≠ 0`）で反駁して
    False を得る（本物の有理根非存在に落ちる・surrogate ではない）。 -/
theorem cq1_refute
    (h : ∃ t : QRat, ratRing.add (ratRing.add (ratRing.mul t t) t) ratRing.one
      = ratRing.zero) : False := by
  obtain ⟨t, ht⟩ := h
  exact cq0_no_rat_root t ht

/-! ## CQ1-4: idealRel 整形 -/

/-- **CQ1-4: idealRel の零右辺整形** — f = cq0Modulus で
    `idealRel P Φ₃ a 0 ↔ ∃ h, a = h·Φ₃`。`idealRel S E f g = ∃ h, f + (−g) = h·E`
    の g = 0 を neg_zero/add_zero で消す。CBC cbc_idealRel_zero_iff の次数2版。 -/
theorem cq1_idealRel_zero_iff (a : Poly ratRing) :
    idealRel (polyCRing ratRing) cq0Modulus a (polyCRing ratRing).zero
      ↔ ∃ h : Poly ratRing, a = (polyCRing ratRing).mul h cq0Modulus := by
  have hsimp : (polyCRing ratRing).add a
      ((polyCRing ratRing).neg (polyCRing ratRing).zero) = a := by
    rw [CRing.neg_zero (polyCRing ratRing)]
    exact CRing.add_zero (polyCRing ratRing) a
  apply Iff.intro
  · intro h
    obtain ⟨w, hw⟩ := h
    exact ⟨w, hsimp.symm.trans hw⟩
  · intro h
    obtain ⟨w, hw⟩ := h
    exact ⟨w, hsimp.trans hw⟩

/-! ## CQ1-5: PS レベルの鎖本体（次数2・4 葉） -/

/-- **CQ1-5: PS レベル Bezout 鎖** — a が有界（多項式）で、a が cq0PS(= Φ₃)
    で割り切れない（`¬∃q, a = q·Φ₃`）なら、a と Φ₃ は互いに素
    （`cbzBezB a cq0PS`）。deg Φ₃ = 2 の有限深度ユークリッド鎖で、
    a ÷ Φ₃ の剰余 r（次数 ≤ 1）から始め r の係数の零判定（`rzd_zero_or_ne`）で
    最大 2 重に場合分け（4 葉）。非零定数葉は `cbz_const`、Φ₃ = q₁·r（r 一次因子）
    の割り切れ葉は `cq1_linear_factor_root` + `cq1_refute` で矛盾、完全割り葉
    （r = 0）は idealRel を作って前提に反する。各段は `cbz_descend` で Bezout を
    降下。CBC cbc_bezB_ct0（8 葉）の次数2版（4 葉・除法最大 2 回）。 -/
theorem cq1_bezB_cq0 (a : PS ratRing) (Na : Nat)
    (hb : IsPolyBounded ratRing a Na)
    (hnd : ¬ ∃ q : PS ratRing, IsPoly ratRing q ∧
      ∀ j, a j = psMul ratRing q cq0PS j) :
    cbzBezB a cq0PS := by
  -- 段0: a ÷ cq0PS（m = 2, N = Na）→ a = q·Φ₃ + r, deg r ≤ 1
  obtain ⟨q, r, hq, hr, hdiv⟩ :=
    field_division_exists ratRing qInv ratIUTField.mul_inv_cancel
      cq0PS 2 cq0_bound cq0_lead Na a
      (ppu_bounded_mono ratRing (by omega : Na ≤ Na + 2) hb)
  have hdiv0f : a = psAdd ratRing (psMul ratRing q cq0PS) r := funext hdiv
  -- 各 build 葉共通の最終降下: BezB(cq0PS, r) → BezB(a, cq0PS)
  have hfinal : cbzBezB cq0PS r → cbzBezB a cq0PS :=
    fun hfr => cbz_descend a q cq0PS r (Na + 1) hq hdiv0f hfr
  cases rzd_zero_or_ne (r 1) with
  | inr hr1 =>
    -- deg r = 1: cq0PS ÷ r（m = 1, N = 2）→ Φ₃ = q₁·r + r₁, r₁ 定数（bound 1）
    obtain ⟨q₁, r₁, hq₁, hr₁, hdiv1⟩ :=
      field_division_exists ratRing qInv ratIUTField.mul_inv_cancel
        r 1 hr hr1 2 cq0PS cq0_bound
    have hdiv1f : cq0PS = psAdd ratRing (psMul ratRing q₁ r) r₁ := funext hdiv1
    cases rzd_zero_or_ne (r₁ 0) with
    | inr hr₁0 =>
      -- 葉1（build）: r₁ 非零定数 → cbz_const → descend
      have h1 : cbzBezB r r₁ := cbz_const r r₁ hr₁ hr₁0
      have h3 : cbzBezB cq0PS r := cbz_descend cq0PS q₁ r r₁ 3 hq₁ hdiv1f h1
      exact hfinal h3
    | inl hr₁0 =>
      -- 葉2（矛盾）: Φ₃ = q₁·r 完全割り, r 一次因子 → 葉補題 → cq0_no_rat_root
      have hr₁z : r₁ = psZero ratRing :=
        ppu_psZero_of_coeffs ratRing hr₁
          (fun i hi => by rw [show i = 0 from by omega]; exact hr₁0)
      have heqf : cq0PS = psMul ratRing q₁ r :=
        funext (fun j => (hdiv1 j).trans (congrFun (by
          rw [hr₁z]
          exact CRing.add_zero (psRing ratRing) (psMul ratRing q₁ r)) j))
      exact (cq1_refute
        (cq1_linear_factor_root q₁ r 3 hq₁ hr hr1 heqf)).elim
  | inl hr1 =>
    have hrB1 : IsPolyBounded ratRing r 1 := ppu_bound_drop ratRing hr hr1
    cases rzd_zero_or_ne (r 0) with
    | inr hr0 =>
      -- 葉3（build）: r 非零定数 → cbz_const（直接 BezB(cq0PS, r)）
      have h3 : cbzBezB cq0PS r := cbz_const cq0PS r hrB1 hr0
      exact hfinal h3
    | inl hr0 =>
      -- 葉4: r = 0 完全割り → a = q·Φ₃ → idealRel → 前提 ¬∃q に矛盾
      have hrz : r = psZero ratRing :=
        ppu_psZero_of_coeffs ratRing hr (fun i hi => by
          cases Nat.lt_or_ge i 1 with
          | inl h => rw [show i = 0 from by omega]; exact hr0
          | inr h => rw [show i = 1 from by omega]; exact hr1)
      have heqa : ∀ j, a j = psMul ratRing q cq0PS j :=
        fun j => (hdiv j).trans (congrFun (by
          rw [hrz]
          exact CRing.add_zero (psRing ratRing) (psMul ratRing q cq0PS)) j)
      exact (hnd ⟨q, ⟨Na + 1, hq⟩, heqa⟩).elim

/-! ## CQ1-6: 本丸 — SimpleExtData.bezout の充填 -/

/-- **CQ1-6（本丸）: f = x²+x+1 のイデアルは極大（Bezout）** —
    cq0Modulus = Φ₃ で割り切れない任意の多項式 a は Φ₃ と互いに素:
    ∃ u v, u·Φ₃ + v·a = 1。型は `SimpleExtData.bezout`（cq0Field・cq0PS・deg 2）
    そのもの。前提 `¬idealRel` を `cq1_idealRel_zero_iff` で PS 版 `¬∃q` に翻訳し、
    PS 鎖 `cq1_bezB_cq0` の `cbzBezB a cq0PS`（= ∃ u v, u·a + v·Φ₃ = 1）を得て、
    u,v を入れ替え add_comm で並べ、witness を Poly（Subtype）へ梱包する
    （`ppu_poly_ext`・val(polyMul)=psMul は defeq）。CBC cbc_bezout の次数2版。 -/
theorem cq1_bezout : ∀ a : Poly ratRing,
    ¬ idealRel (polyCRing ratRing) cq0Modulus a (polyCRing ratRing).zero →
    ∃ u v : Poly ratRing,
      (polyCRing ratRing).add
        ((polyCRing ratRing).mul u cq0Modulus)
        ((polyCRing ratRing).mul v a) = (polyCRing ratRing).one := by
  intro a hnd
  obtain ⟨Na, hNa⟩ := a.property
  -- 前提 ¬idealRel を PS 版 ¬∃q へ翻訳
  have hnd' : ¬ ∃ q : PS ratRing, IsPoly ratRing q ∧
      ∀ j, a.val j = psMul ratRing q cq0PS j := by
    intro hex
    obtain ⟨q, hqP, heq⟩ := hex
    apply hnd
    refine (cq1_idealRel_zero_iff a).mpr ⟨⟨q, hqP⟩, ?_⟩
    exact ppu_poly_ext ratRing (fun j => heq j)
  -- PS 鎖本体
  have hbez : cbzBezB a.val cq0PS := cq1_bezB_cq0 a.val Na hNa hnd'
  obtain ⟨u, v, Nu, Nv, hu, hv, huv⟩ := hbez
  -- u·a + v·Φ₃ = 1 を並べ替え v·Φ₃ + u·a = 1
  have hfull : psAdd ratRing (psMul ratRing v cq0PS) (psMul ratRing u a.val)
      = psOne ratRing :=
    ((psRing ratRing).add_comm (psMul ratRing v cq0PS)
      (psMul ratRing u a.val)).trans huv
  -- Poly へ梱包（coeff of Φ₃ = v, coeff of a = u）
  exact ⟨⟨v, ⟨Nv, hv⟩⟩, ⟨u, ⟨Nu, hu⟩⟩,
    ppu_poly_ext ratRing (fun j => congrFun hfull j)⟩

end IUT

#print axioms IUT.cq1_bezout
