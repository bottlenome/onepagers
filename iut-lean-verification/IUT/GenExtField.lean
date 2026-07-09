/-
  IUT/GenExtField.lean — GEF（**一般構成器「∀ 既約 f, ℚ[x]/(f) は実体」**:
  A1 一般化の統合本丸。単一 f = x³−2（CBC）の Bezout 充填を、**任意の
  既約多項式 f** に一般化する）

  ── 分類 **[実]**（本物の先行建設・(a) 昇格。骨格でなく本物の証明・
  sorry 皆無・新規 Classical.choice 皆無・模型ゼロ・toy 主語なし）。
  CBC（`CbrtBezoutChain.lean`）は f = x³−2 という**単一の実 f** に対して
  `SimpleExtData.bezout`（イデアル極大性）を証明したが、本層はそれを
  **一般の既約 f**（`pibIrreducible ratRing f`）へ引き上げ、
  「ℚ[x]/(f) は体」を **f を量化した一般命題**として本物に出す。

  **complete_pct 影響**: 柱A「実 Galois 理論／実 π₁^ét」の (a) 昇格
  ——CBC の単一 f を、既存の本物の部品
  （`pgbBezoutQ`＝実 ℚ[X] の有界余因子 Bezout・`pib_gcd_unit_of_not_dvd`
  ＝既約 ⟹ gcd 単元・`pbz_scale_comb`＝単元正規化）の**直線的合成**で
  一般化する。CBC の「次数3固定ユークリッド鎖」を、一般 f では
  `pgbBezoutQ`（拡張ユークリッド全段の有界余因子追跡・hlead_oracle は
  `plo_lead_oracle_Q` で choice-free 充填済み）+ `pib`（既約性の橋）+
  単元正規化 の三段合成に置換する。complete_pct は**未設定（動かさない）**
  ——親が A1 二軸を統合時に更新する。本層は水増しの束ねでなく、
  イデアル極大性を**一般既約 f で本物に充填**する昇格である。

  * GEF-1 `gef_idealRel_iff_pdbDvd` — **橋補題**: Poly 版 `idealRel`
    （単項イデアル合同）を PS 版有界整除 `pdbDvd ratRing f a.val` へ翻訳。
    idealRel P E a 0 = ∃ h, a + (−0) = h·E を neg_zero/add_zero で
    a = h·E に整え、E.val = f・h.val は IsPoly（`h.property`）で
    pdbDvd f a.val（余因子 h.val）へ。逆は余因子 c を Poly ⟨c, hc⟩ に
    包み `ppu_poly_ext` で戻す。
  * GEF-2 `gef_bezout` — **本丸（一般 hBez）**: 既約 f で割り切れない
    任意 a は f と互いに素（∃ u v, u·f + v·a = 1、Poly 版）。
    (i) ¬idealRel を GEF-1 で ¬pdbDvd f a.val へ、
    (ii) a.val ≠ 0（さもなくば pdbDvd f a.val で矛盾）を
       `plo_lead_oracle_Q` で先頭係数位置 ma を取り確定、
    (iii) `pgbBezoutQ f a.val` で gcd gg と s,t,c を取り、
    (iv) `pib_gcd_unit_of_not_dvd` で gg が単元、`pib_unit_eq_psC` で
       gg = psC c（c ≠ 0）、
    (v) 単元正規化（u = c⁻¹·s, v = c⁻¹·t、`pbz_scale_comb` +
       `psConstHom.map_mul` + `mul_inv_cancel`）で u·f + v·a.val = 1。
       u,v は s,t の IsPoly（`pgbBezoutQ` が返す）から Poly 化して梱包。
  * GEF-3 `gefExtData` — 一般構成器: `SimpleExtData pbzRatField` を
    modulus:=f, deg:=nf, bezout:=`gef_bezout` で埋める。
  * GEF-4 `gefField` — `SimpleFieldExt pbzRatField`（体拡大レコード）。
  * GEF-5 `gef_field_exists` — capstone: **∀ 既約 f, ℚ[x]/(f) は実体**
    （非零元に逆元が存在）。

  正直な限定（§4 により消さない）:
   - **本物**: 一般既約 f（`pibIrreducible ratRing f`）に対する
     イデアル極大性（Bezout）と「ℚ[x]/(f) は体」の含意は完全証明
     （sorry 皆無・新規 Classical.choice 皆無・`#print axioms` =
     propext, Quot.sound のみ）。CBC の単一 f を一般 f へ昇格した。
   - **単元正規化の再掲**: `pbzBezout_one_of_unit`（M270F-7）の恒等式は、
     Poly 梱包に必要な **Bezout 係数 u,v の IsPoly** を保つため、
     同じ `pbz_scale_comb` エンジンで**明示 witness（u = c⁻¹·s,
     v = c⁻¹·t）つきに inline 再現**する（数学的内容は同一・§4 に
     反する弱化なし）。s,t の IsPoly は `pgbBezoutQ` が本物に返す。
   - 逆元は `Field268` と同精神の構成的 ∃ 形（全域 inv 函数への昇格は
     選択原理を要するため対象外）。
   - 既約性 `pibIrreducible ratRing f`・次数上界 hb・先頭係数 hl は
     入力仮説として受け取る（有限台性からの次数抽出・既約性の
     多項式因数分解判定は本層に含めない・既存 M26xF/M27xF と同方針）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.PolyBezoutBounded
import IUT.PolyIrreducibleBounded
import IUT.PolyBezoutQ
import IUT.PolyLeadOracleQ
import IUT.PolyPSUtil
import IUT.SimpleExtension

namespace IUT

/-! ## GEF-1: 橋補題（idealRel ↔ 有界整除 pdbDvd） -/

/-- **定理 (GEF-1): idealRel ↔ pdbDvd** — Poly 版の単項イデアル合同
    `idealRel P E a 0`（E = f を法とする a ≡ 0）は、PS 版の本物の
    有界余因子整除 `pdbDvd ratRing f a.val`（f ∣ a）に一致する。
    `idealRel S E f g = ∃ h, f + (−g) = h·E` の g = 0 を neg_zero/add_zero
    で消し、E.val = f・余因子の IsPoly（`Poly.property`）を橋渡しする。
    CBC の `cbc_idealRel_zero_iff` の一般 f 版（右辺を pdbDvd へ直結）。 -/
theorem gef_idealRel_iff_pdbDvd (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (a : Poly ratRing) :
    idealRel (polyCRing ratRing) (simpleExtModulus pbzRatField f nf hb) a
        (polyCRing ratRing).zero
      ↔ pdbDvd ratRing f a.val := by
  have hsimp : (polyCRing ratRing).add a
      ((polyCRing ratRing).neg (polyCRing ratRing).zero) = a := by
    rw [CRing.neg_zero (polyCRing ratRing)]
    exact CRing.add_zero (polyCRing ratRing) a
  apply Iff.intro
  · intro h
    obtain ⟨w, hw⟩ := h
    have heq : a = (polyCRing ratRing).mul w (simpleExtModulus pbzRatField f nf hb) :=
      hsimp.symm.trans hw
    have hval : a.val = psMul ratRing w.val f :=
      congrArg (fun t : Poly ratRing => t.val) heq
    exact ⟨w.val, w.property, hval⟩
  · intro h
    obtain ⟨c, hc, hce⟩ := h
    refine ⟨⟨c, hc⟩, ?_⟩
    refine hsimp.trans ?_
    apply ppu_poly_ext ratRing
    intro j
    exact congrFun hce j

/-! ## GEF-2: 本丸 — 一般 hBez（∀ 既約 f のイデアル極大性） -/

/-- **定理 (GEF-2・本丸): 一般既約 f のイデアルは極大（Bezout）** —
    `pibIrreducible ratRing f`（本物の有界整除上の既約性）を満たす f で
    割り切れない任意多項式 a は f と互いに素:
    ∃ u v, u·f + v·a = 1（Poly 版・`SimpleExtData.bezout` の型そのもの）。

    CBC（f = x³−2）の次数3固定ユークリッド鎖を、一般 f では
    `pgbBezoutQ f a.val`（拡張ユークリッド全段の有界余因子 Bezout・
    hlead_oracle は `plo_lead_oracle_Q` で choice-free 充填済み）+
    `pib_gcd_unit_of_not_dvd`（既約 f・gg∣f・gg∣a・f∤a ⟹ gg 単元）+
    単元正規化 の**直線的合成**に置換する。 -/
theorem gef_bezout (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hirr : pibIrreducible ratRing f) :
    ∀ a : Poly ratRing,
      ¬ idealRel (polyCRing ratRing) (simpleExtModulus pbzRatField f nf hb) a
        (polyCRing ratRing).zero →
      ∃ u v : Poly ratRing,
        (polyCRing ratRing).add
          ((polyCRing ratRing).mul u (simpleExtModulus pbzRatField f nf hb))
          ((polyCRing ratRing).mul v a) = (polyCRing ratRing).one := by
  intro a hnd
  -- (i) ¬idealRel を ¬pdbDvd f a.val へ翻訳（GEF-1）
  have hnd' : ¬ pdbDvd ratRing f a.val := fun hd =>
    hnd ((gef_idealRel_iff_pdbDvd f nf hb a).mpr hd)
  -- (ii) a.val ≠ 0: 先頭係数位置 ma を確定（さもなくば pdbDvd f a.val で矛盾）
  obtain ⟨Na, hNa⟩ := a.property
  obtain ⟨ma, hma_ne, hma_b⟩ : ∃ d, a.val d ≠ ratRing.zero ∧
      IsPolyBounded ratRing a.val (d + 1) := by
    cases plo_lead_oracle_Q a.val Na hNa with
    | inr hex => exact hex
    | inl hz =>
      have haz : a.val = psZero ratRing := funext (fun i => hz i)
      have hdvd0 : pdbDvd ratRing f a.val :=
        ⟨psZero ratRing, pgb_isPoly_zero ratRing,
          haz.trans (CRing.zero_mul (psRing ratRing) f).symm⟩
      exact absurd hdvd0 hnd'
  -- (iii) f と a.val の gcd（有界余因子 Bezout）
  obtain ⟨s, t, gg, mg, hcomb, hggb, hggl, hgf, hga, hsP, htP⟩ :=
    pgbBezoutQ f a.val (nf + 1) ma hb hma_b hma_ne
  -- (iv) 既約性の橋: gg は単元、gg = psC c（c ≠ 0）
  have hggP : IsPoly ratRing gg := ⟨mg + 1, hggb⟩
  have hunit : pdvIsUnit ratRing gg :=
    pib_gcd_unit_of_not_dvd ratRing f a.val gg hirr hggP hgf hga hnd'
  obtain ⟨c, hc, hunitEq⟩ := pib_unit_eq_psC ratRing gg hunit
  -- (v) 単元正規化: u = c⁻¹·s, v = c⁻¹·t（IsPoly 保存つき inline 再現）
  have hpsC : IsPoly ratRing (psC ratRing (qInv c)) :=
    ⟨1, fun i _ => if_neg (by omega)⟩
  have hcombeq : psAdd ratRing (psMul ratRing s f) (psMul ratRing t a.val)
      = psC ratRing c := hcomb.symm.trans hunitEq
  have hmm : psMul ratRing (psC ratRing (qInv c)) (psC ratRing c)
      = psC ratRing (ratRing.mul (qInv c) c) :=
    ((psConstHom ratRing).map_mul (qInv c) c).symm
  have hcancel : ratRing.mul (qInv c) c = ratRing.one := by
    rw [ratRing.mul_comm]
    exact ratIUTField.mul_inv_cancel c hc
  -- pbz_scale_comb は (psRing).add/.mul 形（psAdd/psMul と defeq）で述べられて
  -- いるので rw の構文一致は使えない。defeq を許す `.trans` 連鎖で組む。
  have hstep1 : psAdd ratRing
        (psMul ratRing (psMul ratRing (psC ratRing (qInv c)) s) f)
        (psMul ratRing (psMul ratRing (psC ratRing (qInv c)) t) a.val)
      = psMul ratRing (psC ratRing (qInv c))
          (psAdd ratRing (psMul ratRing s f) (psMul ratRing t a.val)) :=
    pbz_scale_comb (psRing ratRing) (psC ratRing (qInv c)) s t f a.val
  have hstep2 : psMul ratRing (psC ratRing (qInv c))
          (psAdd ratRing (psMul ratRing s f) (psMul ratRing t a.val))
      = psMul ratRing (psC ratRing (qInv c)) (psC ratRing c) :=
    congrArg (psMul ratRing (psC ratRing (qInv c))) hcombeq
  have hone : psAdd ratRing
      (psMul ratRing (psMul ratRing (psC ratRing (qInv c)) s) f)
      (psMul ratRing (psMul ratRing (psC ratRing (qInv c)) t) a.val)
      = psOne ratRing :=
    hstep1.trans (hstep2.trans (hmm.trans (congrArg (psC ratRing) hcancel)))
  -- Poly 梱包（u,v は s,t の IsPoly から Poly 化・ppu_poly_ext で戻す）
  exact ⟨⟨psMul ratRing (psC ratRing (qInv c)) s, pgb_isPoly_mul ratRing hpsC hsP⟩,
    ⟨psMul ratRing (psC ratRing (qInv c)) t, pgb_isPoly_mul ratRing hpsC htP⟩,
    ppu_poly_ext ratRing (fun j => congrFun hone j)⟩

/-! ## GEF-3: 一般構成器 SimpleExtData -/

/-- **定義 (GEF-3): 一般構成器** — 既約多項式 f（次数 nf ≥ 1・先頭係数 ≠ 0）
    から `SimpleExtData pbzRatField`（= ℚ[x]/(f) の入力データ）を構成する。
    honest 仮説だった `bezout`（イデアル極大性）を、本物の一般 hBez
    `gef_bezout` で**本物に充填**する。CBC の単一 f 版（`ct0ExtData` 相当）を
    ∀ 既約 f へ一般化した本丸。 -/
def gefExtData (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) :
    SimpleExtData pbzRatField where
  modulus := f
  deg := nf
  bound := hb
  lead := hl
  deg_pos := hn
  base_nontrivial := ratIUTField.one_ne_zero
  bezout := gef_bezout f nf hb hl hirr

/-! ## GEF-4: 体拡大レコード -/

/-- **定義 (GEF-4): 一般体拡大** — 一般構成器 `gefExtData` の入力から、
    体拡大レコード `SimpleFieldExt pbzRatField`（拡大環・単射埋め込み・
    非自明・逆元）を本物に組み上げる。 -/
def gefField (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) :
    SimpleFieldExt pbzRatField :=
  (gefExtData f nf hb hl hn hirr).build pbzRatField

/-! ## GEF-5: capstone — ∀ 既約 f, ℚ[x]/(f) は実体 -/

/-- **定理 (GEF-5・capstone): ∀ 既約 f, ℚ[x]/(f) は実体** —
    任意の既約多項式 f（`pibIrreducible ratRing f`・次数 nf ≥ 1・
    先頭係数 ≠ 0）に対し、体拡大 ℚ[x]/(f) が存在し、その非零元は必ず
    乗法逆元を持つ（構成的 ∃ 形）。A1 一般化「実数体 K = ℚ[x]/(f) を
    実際の商環として構成」の**任意既約 f 版**の本物のインスタンス。 -/
theorem gef_field_exists (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) :
    ∃ E : SimpleFieldExt pbzRatField,
      ∀ x, x ≠ E.ring.zero → ∃ y, E.ring.mul x y = E.ring.one :=
  ⟨gefField f nf hb hl hn hirr,
    (gefField f nf hb hl hn hirr).has_inverses⟩

end IUT

#print axioms IUT.gef_field_exists
