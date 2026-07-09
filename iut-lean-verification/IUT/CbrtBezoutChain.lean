/-
  IUT/CbrtBezoutChain.lean — CBC（A1 実数体 ℚ(∛2) = ℚ[x]/(x³−2) の
  Wave 2 / N7: SimpleExtData.bezout の充填 = 次数3固定ユークリッド鎖・本丸）

  ── 分類 **[実]**（本物の先行建設。骨格でなく実 ℚ・実 f = x³−2 の
  イデアル極大性そのものの完全証明・sorry 皆無・新規 Classical.choice 皆無・
  模型ゼロ）。名前付き実ターゲット: A1「実数体 K = ℚ[x]/(f) を実際の商環
  として構成」の最初の本物のインスタンス **実三次数体 ℚ(∛2)**（設計書
  `audit/A1-real-numberfield-plan.md` §2.2・§2.4・§3・§4 N7）。本層は
  M269F の honest 仮説として持ち回られていた `SimpleExtData.bezout`
  （f のイデアルが極大 = 割り切れない任意元と互いに素）を、f = x³−2 で
  **本物に証明**する。deg f3 = 3 なので剰余次数が 3→2→1→0 と最大 3 回の
  除法で必ず停止する有限深度ユークリッド鎖（設計 §2.1(ii)）を、既存の
  実部品（field_division_exists・cbz_const/cbz_descend・clf_linear_factor_root・
  cco_cofactor_linear・crt_two_not_cube・rzd_zero_or_ne）の合成だけで組み立てる。

  **complete_pct 影響**: 本タスクでは complete_pct は**未設定（動かさない）**
  （親が Wave 3 での体化 N8/N9 と併せて A1 二軸を更新する）。本層は
  イデアル極大性の本物の充填であり、水増しの束ねではない。

  内容:
   * cbc_factor_algebra — 完全割り葉の因子分解の純代数
     (q₁·r + r₁ で r = q₂·r₁ なら = (q₁·q₂+1)·r₁)（一般 CRing）。
   * cbc_refute — refutation アダプタ: clf の生産物 ∃t,t·(t·t)=ct0Two を
     crt_two_not_cube（∀r,(r·r)·r≠ratOfTwo）で反駁して False。
     ct0Two = ratOfTwo は ratOfInt.map 2 と ⟨2,1,_⟩ の defeq、
     t·(t·t)=(t·t)·t は mul_comm。
   * cbc_idealRel_zero_iff — N7' 整形補題:
     idealRel P F3 a 0 ↔ ∃ h, a = h·F3（neg_zero/add_zero）。
   * cbc_bezB_ct0 — PS レベルの鎖本体（設計 §2.2 の 8 分岐）:
     a ÷ ct0PS の剰余 r の係数零判定（rzd_zero_or_ne）で最大 3 重に場合分けし、
     非零定数葉は cbz_const、割り切れ葉（一次因子 r₁ / 一次余因子 q₁）は
     clf_linear_factor_root + cbc_refute で矛盾、完全割り（r=0）は
     idealRel を作って前提と矛盾。各段の Bezout は cbz_descend で降下し
     BezB(a, ct0PS) を得る。
   * cbc_bezout — 本丸: SimpleExtData.bezout の型そのもの。PS 版を
     Poly（Subtype）へ梱包し、u·F3 + v·a = 1 の Poly 等式を ppu_poly_ext で
     組む。前提 ¬idealRel は cbc_idealRel_zero_iff で PS 版 ¬∃q へ翻訳。

  正直な限定（§4 規約により消さない）:
   - **単一 f = x³−2 のみ**。一般既約 f への Bezout（一般拡張ユークリッド
     互除法 + 一般次数簿記 + 「約元は単元 or 同伴」）は未達（設計 §2.1(i)・
     §5 の名前付き後続）。
   - 逆元は後続でも ∃ 形（全域 inv 付き IUTField 昇格は別スライス）。
   - N0 相当（∛2∉ℚ）は既に `crt_two_not_cube`（本物）で閉じているため
     本層に仮説引数は残らない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.CbrtTwoBase
import IUT.CbrtBezB
import IUT.CbrtLinearFactor
import IUT.CbrtCofactor
import IUT.CubeRootTwoIrrational
import IUT.RatZeroDecide
import IUT.PolyPSUtil
import IUT.PolyFieldDivision
import IUT.SimpleExtension

namespace IUT

/-! ## CBC-1: 完全割り葉の因子分解（純代数） -/

/-- **CBC-1: 因子分解の純代数** — r = q₂·r₁ のとき q₁·r + r₁ = (q₁·q₂ + 1)·r₁。
    設計 §2.2 の「r₁ を一次因子として括り出す」完全割り葉で使う（一般 CRing）。 -/
theorem cbc_factor_algebra (R : CRing) (q₁ q₂ r r₁ : R.carrier)
    (hr : r = R.mul q₂ r₁) :
    R.add (R.mul q₁ r) r₁ = R.mul (R.add (R.mul q₁ q₂) R.one) r₁ := by
  rw [CRing.right_distrib R (R.mul q₁ q₂) R.one r₁, R.one_mul r₁,
    R.mul_assoc q₁ q₂ r₁, ← hr]

/-! ## CBC-2: refutation アダプタ -/

/-- ct0Two（= ratOfInt.map 2 = 2/1）と ratOfTwo（= ⟨2,1,_⟩）は同一の有理数。
    どちらも `Quot.mk ratRel ⟨2,1,_⟩`（PreRat の den_pos は Prop なので
    proof irrelevance で defeq）。 -/
theorem cbc_ct0Two_eq_ratOfTwo : ct0Two = ratOfTwo := rfl

/-- **CBC-2: refutation アダプタ** — `clf_linear_factor_root` の生産物
    `∃ t, t·(t·t) = ct0Two` を `crt_two_not_cube`（`∀ r, (r·r)·r ≠ ratOfTwo`）で
    反駁して False を得る。t·(t·t) = (t·t)·t（mul_comm）と ct0Two = ratOfTwo で整える。 -/
theorem cbc_refute
    (h : ∃ t : QRat, ratRing.mul t (ratRing.mul t t) = ct0Two) : False := by
  obtain ⟨t, ht⟩ := h
  apply crt_two_not_cube
  refine ⟨t, ?_⟩
  rw [ratRing.mul_comm (ratRing.mul t t) t, ht]
  exact cbc_ct0Two_eq_ratOfTwo

/-! ## CBC-3: idealRel 整形（N7'） -/

/-- **CBC-3 (N7'): idealRel の零右辺整形** — f3 = ct0Modulus で
    `idealRel P F3 a 0 ↔ ∃ h, a = h·F3`。`idealRel S E f g = ∃ h, f + (−g) = h·E`
    の g = 0 を neg_zero/add_zero で消す。PS 版鎖の `¬∃q` 前提と Poly 版
    `¬idealRel` 前提を繋ぐ。 -/
theorem cbc_idealRel_zero_iff (a : Poly ratRing) :
    idealRel (polyCRing ratRing) ct0Modulus a (polyCRing ratRing).zero
      ↔ ∃ h : Poly ratRing, a = (polyCRing ratRing).mul h ct0Modulus := by
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

/-! ## CBC-4: PS レベルの鎖本体（設計 §2.2 の 8 分岐） -/

/-- **CBC-4: PS レベル Bezout 鎖** — a が有界（多項式）で、a が ct0PS(= x³−2)
    で割り切れない（`¬∃q, a = q·ct0PS`）なら、a と ct0PS は互いに素
    （`cbzBezB a ct0PS`）。deg ct0PS = 3 の有限深度ユークリッド鎖で、
    a ÷ ct0PS の剰余 r（次数 ≤ 2）から始め r の係数の零判定（`rzd_zero_or_ne`）で
    最大 3 重に場合分け（8 葉）。非零定数葉は `cbz_const`、一次因子/一次余因子の
    割り切れ葉は `clf_linear_factor_root` + `cbc_refute` で矛盾、完全割り葉は
    idealRel を作って前提に反する。各段は `cbz_descend` で Bezout を降下。 -/
theorem cbc_bezB_ct0 (a : PS ratRing) (Na : Nat)
    (hb : IsPolyBounded ratRing a Na)
    (hnd : ¬ ∃ q : PS ratRing, IsPoly ratRing q ∧
      ∀ j, a j = psMul ratRing q ct0PS j) :
    cbzBezB a ct0PS := by
  -- 段0: a ÷ ct0PS（m = 3, N = Na）→ a = q·ct0PS + r, deg r ≤ 2
  obtain ⟨q, r, hq, hr, hdiv⟩ :=
    field_division_exists ratRing qInv ratIUTField.mul_inv_cancel
      ct0PS 3 ct0_bound ct0_lead Na a
      (ppu_bounded_mono ratRing (by omega : Na ≤ Na + 3) hb)
  have hdiv0f : a = psAdd ratRing (psMul ratRing q ct0PS) r := funext hdiv
  -- 各 build 葉共通の最終降下: BezB(ct0PS, r) → BezB(a, ct0PS)
  have hfinal : cbzBezB ct0PS r → cbzBezB a ct0PS :=
    fun hfr => cbz_descend a q ct0PS r (Na + 1) hq hdiv0f hfr
  cases rzd_zero_or_ne (r 2) with
  | inr hr2 =>
    -- deg r = 2: ct0PS ÷ r（m = 2, N = 2）→ ct0PS = q₁·r + r₁, deg r₁ ≤ 1
    obtain ⟨q₁, r₁, hq₁, hr₁, hdiv1⟩ :=
      field_division_exists ratRing qInv ratIUTField.mul_inv_cancel
        r 2 hr hr2 2 ct0PS ct0_bound
    have hdiv1f : ct0PS = psAdd ratRing (psMul ratRing q₁ r) r₁ := funext hdiv1
    cases rzd_zero_or_ne (r₁ 1) with
    | inr hr₁1 =>
      -- deg r₁ = 1: r ÷ r₁（m = 1, N = 2）→ r = q₂·r₁ + r₂, r₂ 定数
      obtain ⟨q₂, r₂, hq₂, hr₂, hdiv2⟩ :=
        field_division_exists ratRing qInv ratIUTField.mul_inv_cancel
          r₁ 1 hr₁ hr₁1 2 r hr
      have hdiv2f : r = psAdd ratRing (psMul ratRing q₂ r₁) r₂ := funext hdiv2
      cases rzd_zero_or_ne (r₂ 0) with
      | inr hr₂0 =>
        -- 葉1（build）: r₂ 非零定数 → cbz_const → descend×2
        have h1 : cbzBezB r₁ r₂ := cbz_const r₁ r₂ hr₂ hr₂0
        have h2 : cbzBezB r r₁ := cbz_descend r q₂ r₁ r₂ 3 hq₂ hdiv2f h1
        have h3 : cbzBezB ct0PS r := cbz_descend ct0PS q₁ r r₁ 3 hq₁ hdiv1f h2
        exact hfinal h3
      | inl hr₂0 =>
        -- 葉2（矛盾）: r = q₂·r₁ 完全割り → ct0PS = (q₁·q₂+1)·r₁, r₁ 一次因子
        have hr₂z : r₂ = psZero ratRing :=
          ppu_psZero_of_coeffs ratRing hr₂
            (fun i hi => by rw [show i = 0 from by omega]; exact hr₂0)
        have heqr : r = psMul ratRing q₂ r₁ :=
          funext (fun j => (hdiv2 j).trans (congrFun (by
            rw [hr₂z]
            exact CRing.add_zero (psRing ratRing) (psMul ratRing q₂ r₁)) j))
        have hOne : IsPolyBounded ratRing (psOne ratRing) 1 :=
          fun i hi => if_neg (by omega)
        have hwB : IsPolyBounded ratRing
            (psAdd ratRing (psMul ratRing q₁ q₂) (psOne ratRing)) ((3 + 3) + 1) :=
          simpleExt_add_bounded ratRing
            (simpleExt_mul_bounded ratRing hq₁ hq₂) hOne
        have heqW : ct0PS = psMul ratRing
            (psAdd ratRing (psMul ratRing q₁ q₂) (psOne ratRing)) r₁ :=
          hdiv1f.trans (cbc_factor_algebra (psRing ratRing) q₁ q₂ r r₁ heqr)
        exact (cbc_refute (clf_linear_factor_root
          (psAdd ratRing (psMul ratRing q₁ q₂) (psOne ratRing)) r₁
          ((3 + 3) + 1) hwB hr₁ hr₁1 heqW)).elim
    | inl hr₁1 =>
      cases rzd_zero_or_ne (r₁ 0) with
      | inr hr₁0 =>
        -- 葉3（build）: r₁ 非零定数 → cbz_const → descend
        have hr₁B1 : IsPolyBounded ratRing r₁ 1 := ppu_bound_drop ratRing hr₁ hr₁1
        have h1 : cbzBezB r r₁ := cbz_const r r₁ hr₁B1 hr₁0
        have h3 : cbzBezB ct0PS r := cbz_descend ct0PS q₁ r r₁ 3 hq₁ hdiv1f h1
        exact hfinal h3
      | inl hr₁0 =>
        -- 葉4（矛盾）: ct0PS = q₁·r 完全割り → 頂点係数論法で q₁ 一次 → 葉補題
        have hr₁z : r₁ = psZero ratRing :=
          ppu_psZero_of_coeffs ratRing hr₁ (fun i hi => by
            cases Nat.lt_or_ge i 1 with
            | inl h => rw [show i = 0 from by omega]; exact hr₁0
            | inr h => rw [show i = 1 from by omega]; exact hr₁1)
        have heqf : ct0PS = psMul ratRing q₁ r :=
          funext (fun j => (hdiv1 j).trans (congrFun (by
            rw [hr₁z]
            exact CRing.add_zero (psRing ratRing) (psMul ratRing q₁ r)) j))
        obtain ⟨hq₁b2, hq₁1⟩ := cco_cofactor_linear q₁ r hq₁ hr hr2 heqf
        have heqf' : ct0PS = psMul ratRing r q₁ :=
          heqf.trans ((psRing ratRing).mul_comm q₁ r)
        exact (cbc_refute
          (clf_linear_factor_root r q₁ 3 hr hq₁b2 hq₁1 heqf')).elim
  | inl hr2 =>
    have hrB2 : IsPolyBounded ratRing r 2 := ppu_bound_drop ratRing hr hr2
    cases rzd_zero_or_ne (r 1) with
    | inr hr1 =>
      -- deg r = 1: ct0PS ÷ r（m = 1, N = 3）→ ct0PS = q₁·r + r₁, r₁ 定数
      obtain ⟨q₁, r₁, hq₁, hr₁, hdiv1⟩ :=
        field_division_exists ratRing qInv ratIUTField.mul_inv_cancel
          r 1 hrB2 hr1 3 ct0PS ct0_bound
      have hdiv1f : ct0PS = psAdd ratRing (psMul ratRing q₁ r) r₁ := funext hdiv1
      cases rzd_zero_or_ne (r₁ 0) with
      | inr hr₁0 =>
        -- 葉5（build）: r₁ 非零定数 → cbz_const → descend
        have h1 : cbzBezB r r₁ := cbz_const r r₁ hr₁ hr₁0
        have h3 : cbzBezB ct0PS r := cbz_descend ct0PS q₁ r r₁ 4 hq₁ hdiv1f h1
        exact hfinal h3
      | inl hr₁0 =>
        -- 葉6（矛盾）: ct0PS = q₁·r 完全割り, r 一次因子 → 葉補題
        have hr₁z : r₁ = psZero ratRing :=
          ppu_psZero_of_coeffs ratRing hr₁
            (fun i hi => by rw [show i = 0 from by omega]; exact hr₁0)
        have heqf : ct0PS = psMul ratRing q₁ r :=
          funext (fun j => (hdiv1 j).trans (congrFun (by
            rw [hr₁z]
            exact CRing.add_zero (psRing ratRing) (psMul ratRing q₁ r)) j))
        exact (cbc_refute
          (clf_linear_factor_root q₁ r 4 hq₁ hrB2 hr1 heqf)).elim
    | inl hr1 =>
      cases rzd_zero_or_ne (r 0) with
      | inr hr0 =>
        -- 葉7（build）: r 非零定数 → cbz_const（直接 BezB(ct0PS, r)）
        have hrB1 : IsPolyBounded ratRing r 1 := ppu_bound_drop ratRing hrB2 hr1
        have h3 : cbzBezB ct0PS r := cbz_const ct0PS r hrB1 hr0
        exact hfinal h3
      | inl hr0 =>
        -- 葉8: r = 0 完全割り → a = q·ct0PS → idealRel → 前提 ¬∃q に矛盾
        have hrz : r = psZero ratRing :=
          ppu_psZero_of_coeffs ratRing hr (fun i hi => by
            cases Nat.lt_or_ge i 1 with
            | inl h => rw [show i = 0 from by omega]; exact hr0
            | inr h =>
              cases Nat.lt_or_ge i 2 with
              | inl h2 => rw [show i = 1 from by omega]; exact hr1
              | inr h2 => rw [show i = 2 from by omega]; exact hr2)
        have heqa : ∀ j, a j = psMul ratRing q ct0PS j :=
          fun j => (hdiv j).trans (congrFun (by
            rw [hrz]
            exact CRing.add_zero (psRing ratRing) (psMul ratRing q ct0PS)) j)
        exact (hnd ⟨q, ⟨Na + 1, hq⟩, heqa⟩).elim

/-! ## CBC-5: 本丸 — SimpleExtData.bezout の充填 -/

/-- **CBC-5（本丸・N7）: f = x³−2 のイデアルは極大（Bezout）** —
    ct0Modulus = f3 で割り切れない任意の多項式 a は f3 と互いに素:
    ∃ u v, u·f3 + v·a = 1。型は `SimpleExtData.bezout`（ct0Field・ct0PS・deg 3）
    そのもの。前提 `¬idealRel` を `cbc_idealRel_zero_iff` で PS 版 `¬∃q` に翻訳し、
    PS 鎖 `cbc_bezB_ct0` の `cbzBezB a ct0PS`（= ∃ u v, u·a + v·f3 = 1）を得て、
    u,v を入れ替え add_comm で並べ、witness を Poly（Subtype）へ梱包する
    （`ppu_poly_ext`・val(polyMul)=psMul は defeq）。 -/
theorem cbc_bezout : ∀ a : Poly ratRing,
    ¬ idealRel (polyCRing ratRing) ct0Modulus a (polyCRing ratRing).zero →
    ∃ u v : Poly ratRing,
      (polyCRing ratRing).add
        ((polyCRing ratRing).mul u ct0Modulus)
        ((polyCRing ratRing).mul v a) = (polyCRing ratRing).one := by
  intro a hnd
  obtain ⟨Na, hNa⟩ := a.property
  -- 前提 ¬idealRel を PS 版 ¬∃q へ翻訳
  have hnd' : ¬ ∃ q : PS ratRing, IsPoly ratRing q ∧
      ∀ j, a.val j = psMul ratRing q ct0PS j := by
    intro hex
    obtain ⟨q, hqP, heq⟩ := hex
    apply hnd
    refine (cbc_idealRel_zero_iff a).mpr ⟨⟨q, hqP⟩, ?_⟩
    exact ppu_poly_ext ratRing (fun j => heq j)
  -- PS 鎖本体
  have hbez : cbzBezB a.val ct0PS := cbc_bezB_ct0 a.val Na hNa hnd'
  obtain ⟨u, v, Nu, Nv, hu, hv, huv⟩ := hbez
  -- u·a + v·f3 = 1 を並べ替え v·f3 + u·a = 1
  have hfull : psAdd ratRing (psMul ratRing v ct0PS) (psMul ratRing u a.val)
      = psOne ratRing :=
    ((psRing ratRing).add_comm (psMul ratRing v ct0PS)
      (psMul ratRing u a.val)).trans huv
  -- Poly へ梱包（coeff of f3 = v, coeff of a = u）
  exact ⟨⟨v, ⟨Nv, hv⟩⟩, ⟨u, ⟨Nu, hu⟩⟩,
    ppu_poly_ext ratRing (fun j => congrFun hfull j)⟩

end IUT

#print axioms IUT.cbc_bezout
