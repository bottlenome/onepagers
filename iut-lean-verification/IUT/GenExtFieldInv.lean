/-
  IUT/GenExtFieldInv.lean — Wave3/F6（A1 0.80→0.85 設計 §1 F6）:
  正規形担体 `GefNF` 上の**全域 inv 関数** `gefNFInv` と体インスタンス
  `gefNFIUTField : IUTField` / `gefNF268 : Field268`（(A) 全域 inv の頂点）

  ── 主要成果の分類: **[実]**（本物の先行建設・(a) 昇格。既存 Quot 担体上の
     `has_inverses`（∃ 形・choice-free 不可能）を、正規形担体 `GefNF`（次数 < nf
     の剰余代表）の上で**全域 inv 関数**へ昇格し、実 ℚ[x]/(f) の第二表示を本物の
     体（IUTField / Field268）にする）。

  **complete_pct 影響**: A1（実 ℚ[x]/(f)・全域 inv 付き実体）の (a) 昇格の頂点。
  F5（`gefNFRing`＝NF 担体の可換環）の上に、拡張ユークリッド関数 `pefBezout`
  （F4）で得た Bezout 係数を単元正規化した剰余として **全域 inv 関数 `gefNFInv`**
  を建て、`gefNF_mul_inv_cancel`（非零元 x の逆元性）を設計 §F6 の (i)〜(v) で
  本物に閉じる。これにより Quot 担体では ∃ 形に留まった逆元が、NF 担体上では
  choice-free の全域関数となり `IUTField` / `Field268` が完成する。
  complete_pct は本ファイル単体では未前進（A1 は独立再監査で確定）。
  complete_pct 未設定。

  本物性（全域 inv は本物・choice-free）:
   - `gefNFInv x` は `ploFind`（F1・Bool 零判定に基づく Type 値探索）で x の
     先頭係数位置 d を取り、`pefBezout f x.val`（F4・拡張ユークリッド関数）の
     Bezout 係数 t を単元 gg = psC c で正規化した `pfdRed f nf (c⁻¹·t)` を返す
     全域関数。x = 0 の枝は `ploFind = none` から `inv 0 = 0`（規約）。
     模型・代理・toy 主語なし。新規 Classical.choice を導入しない。
   - `gefNF_mul_inv_cancel` は設計 §F6 の (i)〜(v):
     (i) x ≠ 0 ⟹ ploFind = some d（`ploFind_none` の対偶）、
     (ii) f ∤ x.val（f∣x なら `pdb_dvd_deg_le` で nf ≤ d だが d < nf で矛盾）、
     (iii) `pefBezout_spec` + `pib_gcd_unit_of_not_dvd` + `pib_unit_eq_psC` で
       gg = psC c（c ≠ 0）、gg 先頭位置 mg = 0・gg mg = c、
     (iv) 単元正規化 inline（`pbz_scale_comb`・`psConstHom.map_mul`・
       `mul_inv_cancel`）で (c⁻¹s)f + (c⁻¹t)x = 1、
     (v) `pfdRed_char`（剰余の一意特徴付け）で mul x (inv x) = red(x·c⁻¹t) = 1
       ——合同代数 `gnfCong`（F5）の伝播で本物に閉じる。仮説・sorry での
       誤魔化しなし。

  正直な限定:
   - 全域 inv は NF 表示（`GefNF`）上であり、既存 Quot 表示（M269F/GEF）の
     `has_inverses` は ∃ 形のまま（設計 0.2 の choice-free 非存在。消さない）。
   - 対象体は実 ℚ（ratRing・qInv・ratIUTField.mul_inv_cancel）に固定。
   - 上界 nf は型パラメータ（データ）。既約性 hirr は逆元性（体性）に必要。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]・IUTField/Field268
  まで含め Classical.choice ゼロ）。禁止タクティク不使用。サブエージェント新規
  部品（共有ファイル不更新）。
-/
import IUT.GenExtFieldNF
import IUT.PolyEuclidFn
import IUT.PolyIrreducibleBounded
import IUT.PolyDvdBounded
import IUT.PolyBezoutQ
import IUT.Field

namespace IUT

/-! ## F6-1: 全域 inv の生値関数 `gefNFInvRaw`（担体を外した PS 値・単元正規化） -/

/-- **F6-1: 全域 inv の生値** — x の先頭係数位置 d（`ploFind`）を取り、
    `pefBezout f x` の Bezout 係数 t を単元 gg = psC c で正規化した剰余
    `pfdRed f nf (c⁻¹·t)` を返す（x = 0 ⟹ ploFind = none ⟹ 0）。担体
    （subtype）を外した生の PS 値関数（`gefNFInv` の中身）。 -/
def gefNFInvRaw (f : PS ratRing) (nf : Nat) (w : PS ratRing) : PS ratRing :=
  match ploFind w nf with
  | none => psZero ratRing
  | some d =>
      pfdRed f nf (pefBezout f w (nf + 1) (d + 1) d).Nt
        (psMul ratRing
          (psC ratRing (qInv ((pefBezout f w (nf + 1) (d + 1) d).gg
            (pefBezout f w (nf + 1) (d + 1) d).mg)))
          (pefBezout f w (nf + 1) (d + 1) d).t)

/-- 生値の none 枝展開（`ploFind = none` なら 0）。 -/
theorem gefNFInvRaw_none (f : PS ratRing) (nf : Nat) (w : PS ratRing)
    (h : ploFind w nf = none) : gefNFInvRaw f nf w = psZero ratRing := by
  have hunf : gefNFInvRaw f nf w
      = (match ploFind w nf with
        | none => psZero ratRing
        | some d =>
            pfdRed f nf (pefBezout f w (nf + 1) (d + 1) d).Nt
              (psMul ratRing
                (psC ratRing (qInv ((pefBezout f w (nf + 1) (d + 1) d).gg
                  (pefBezout f w (nf + 1) (d + 1) d).mg)))
                (pefBezout f w (nf + 1) (d + 1) d).t)) := rfl
  rw [hunf, h]

/-- 生値の some 枝展開（`ploFind = some d` なら単元正規化剰余）。 -/
theorem gefNFInvRaw_some (f : PS ratRing) (nf : Nat) (w : PS ratRing) (d : Nat)
    (h : ploFind w nf = some d) :
    gefNFInvRaw f nf w
      = pfdRed f nf (pefBezout f w (nf + 1) (d + 1) d).Nt
          (psMul ratRing
            (psC ratRing (qInv ((pefBezout f w (nf + 1) (d + 1) d).gg
              (pefBezout f w (nf + 1) (d + 1) d).mg)))
            (pefBezout f w (nf + 1) (d + 1) d).t) := by
  have hunf : gefNFInvRaw f nf w
      = (match ploFind w nf with
        | none => psZero ratRing
        | some d =>
            pfdRed f nf (pefBezout f w (nf + 1) (d + 1) d).Nt
              (psMul ratRing
                (psC ratRing (qInv ((pefBezout f w (nf + 1) (d + 1) d).gg
                  (pefBezout f w (nf + 1) (d + 1) d).mg)))
                (pefBezout f w (nf + 1) (d + 1) d).t)) := rfl
  rw [hunf, h]

/-- 生値は常に nf 有界（担体 `GefNF` に収まる）。none 枝は 0、some 枝は
    `pfdRed_bound`（剰余は deg < nf）。 -/
theorem gefNFInvRaw_bound (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (x : GefNF f nf) :
    IsPolyBounded ratRing (gefNFInvRaw f nf x.val) nf := by
  cases hpf : ploFind x.val nf with
  | none =>
    rw [gefNFInvRaw_none f nf x.val hpf]
    exact fun _ _ => rfl
  | some d =>
    rw [gefNFInvRaw_some f nf x.val d hpf]
    obtain ⟨hxd_ne, hxd_b⟩ := ploFind_some x.val nf x.property hpf
    obtain ⟨_, _, _, _, _, _, htNt⟩ :=
      pefBezout_spec f x.val (nf + 1) (d + 1) d hb hxd_b hxd_ne
    apply pfdRed_bound f nf hb hl (pefBezout f x.val (nf + 1) (d + 1) d).Nt
    apply pbzBound_mono ratRing
      (simpleExt_mul_bounded ratRing
        (show IsPolyBounded ratRing
            (psC ratRing (qInv ((pefBezout f x.val (nf + 1) (d + 1) d).gg
              (pefBezout f x.val (nf + 1) (d + 1) d).mg))) 1
          from fun i hi => if_neg (by omega))
        htNt)
    omega

/-! ## F6-2: 全域 inv 関数 `gefNFInv`（担体 `GefNF` 値） -/

/-- **F6-2: 全域 inv 関数** — 生値 `gefNFInvRaw` を担体 `GefNF`（nf 有界）に
    包んだ全域関数。choice-free（`ploFind`/`pefBezout`/`pfdRed` は全て Type 値・
    選択公理不使用）。 -/
def gefNFInv (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (x : GefNF f nf) : GefNF f nf :=
  ⟨gefNFInvRaw f nf x.val, gefNFInvRaw_bound f nf hb hl hn x⟩

/-! ## F6-3: inv 0 = 0（規約） -/

/-- **F6-3: inv 0 = 0** — 零元では `ploFind = none`（`ploFind_zero`）ゆえ
    生値が 0。 -/
theorem gefNF_inv_zero (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) :
    gefNFInv f nf hb hl hn (gefNFRing f nf hb hl hn).zero
      = (gefNFRing f nf hb hl hn).zero := by
  apply Subtype.ext
  show gefNFInvRaw f nf (psZero ratRing) = psZero ratRing
  exact gefNFInvRaw_none f nf (psZero ratRing) (ploFind_zero nf)

/-! ## F6-4: 逆元公理 `mul_inv_cancel`（設計 §F6 の (i)〜(v)） -/

/-- **F6-4: 全域 inv の逆元性** — 既約 f の NF 担体で、非零元 x は
    `gefNFInv x` を逆元に持つ: mul x (inv x) = one。設計 §F6 の (i)〜(v):
    (i) x ≠ 0 ⟹ ploFind = some d、(ii) f ∤ x.val（`pdb_dvd_deg_le`）、
    (iii) gg = psC c・mg = 0・gg mg = c（`pib_gcd_unit_of_not_dvd` +
    `pib_unit_eq_psC`）、(iv) 単元正規化で (c⁻¹s)f + (c⁻¹t)x = 1、
    (v) 合同伝播 + `pfdRed_char` で red(x·c⁻¹t) = 1。 -/
theorem gefNF_mul_inv_cancel (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) :
    ∀ x : GefNF f nf, x ≠ (gefNFRing f nf hb hl hn).zero →
      (gefNFRing f nf hb hl hn).mul x (gefNFInv f nf hb hl hn x)
        = (gefNFRing f nf hb hl hn).one := by
  intro x hx
  apply Subtype.ext
  show pfdRed f nf nf (psMul ratRing x.val (gefNFInvRaw f nf x.val)) = psOne ratRing
  cases hpf : ploFind x.val nf with
  | none =>
    -- (i) x ≠ 0 なので none 枝は起こらない（起きれば x = 0 で矛盾）
    exfalso
    apply hx
    apply Subtype.ext
    show x.val = psZero ratRing
    exact funext (ploFind_none x.val nf x.property hpf)
  | some d =>
    obtain ⟨hxd_ne, hxd_b⟩ := ploFind_some x.val nf x.property hpf
    -- (ii) d < nf（x は nf 有界・x d ≠ 0）かつ f ∤ x.val
    have hdlt : d < nf := by
      cases Nat.lt_or_ge d nf with
      | inl h => exact h
      | inr h => exact absurd (x.property d h) hxd_ne
    have hnd' : ¬ pdbDvd ratRing f x.val := by
      intro hdvd
      have hle : nf ≤ d := pdb_dvd_deg_le pbzRatField hb hl hxd_b hxd_ne hdvd
      omega
    -- (iii) Bezout + 既約性 ⟹ gg = psC c（c ≠ 0）・mg = 0・gg mg = c
    obtain ⟨hcomb, hggb, hggl, hgf, hga, hsNs, htNt⟩ :=
      pefBezout_spec f x.val (nf + 1) (d + 1) d hb hxd_b hxd_ne
    have hggP : IsPoly ratRing (pefBezout f x.val (nf + 1) (d + 1) d).gg :=
      ⟨(pefBezout f x.val (nf + 1) (d + 1) d).mg + 1, hggb⟩
    have hunit : pdvIsUnit ratRing (pefBezout f x.val (nf + 1) (d + 1) d).gg :=
      pib_gcd_unit_of_not_dvd ratRing f x.val
        (pefBezout f x.val (nf + 1) (d + 1) d).gg hirr hggP hgf hga hnd'
    obtain ⟨c, hc, hunitEq⟩ :=
      pib_unit_eq_psC ratRing (pefBezout f x.val (nf + 1) (d + 1) d).gg hunit
    have hmg0 : (pefBezout f x.val (nf + 1) (d + 1) d).mg = 0 := by
      cases Nat.eq_zero_or_pos (pefBezout f x.val (nf + 1) (d + 1) d).mg with
      | inl h => exact h
      | inr h =>
        exfalso
        apply hggl
        rw [hunitEq]
        show (if (pefBezout f x.val (nf + 1) (d + 1) d).mg = 0 then c else ratRing.zero)
          = ratRing.zero
        exact if_neg (by omega)
    have hggc : (pefBezout f x.val (nf + 1) (d + 1) d).gg
        (pefBezout f x.val (nf + 1) (d + 1) d).mg = c := by
      rw [hunitEq, hmg0]
      show (if (0 : Nat) = 0 then c else ratRing.zero) = c
      exact if_pos rfl
    -- 生値を単元正規化形（qInv c）へ書き換え
    rw [gefNFInvRaw_some f nf x.val d hpf, hggc]
    -- 補助有界性
    have hpsC1 : IsPolyBounded ratRing (psC ratRing (qInv c)) 1 :=
      fun i hi => if_neg (by omega)
    have htt_bN : IsPolyBounded ratRing
        (psMul ratRing (psC ratRing (qInv c))
          (pefBezout f x.val (nf + 1) (d + 1) d).t)
        ((pefBezout f x.val (nf + 1) (d + 1) d).Nt + nf) :=
      pbzBound_mono ratRing (simpleExt_mul_bounded ratRing hpsC1 htNt) (by omega)
    have hxpoly : IsPoly ratRing x.val := ⟨nf, x.property⟩
    -- (iv) 単元正規化: (c⁻¹s)·f + (c⁻¹t)·x = 1（GEF-2(v) と同じ inline 再現）
    have hbez : psAdd ratRing
        (psMul ratRing (pefBezout f x.val (nf + 1) (d + 1) d).s f)
        (psMul ratRing (pefBezout f x.val (nf + 1) (d + 1) d).t x.val)
        = psC ratRing c := hcomb.symm.trans hunitEq
    have hcancel : ratRing.mul (qInv c) c = ratRing.one := by
      rw [ratRing.mul_comm]
      exact ratIUTField.mul_inv_cancel c hc
    have hmm : psMul ratRing (psC ratRing (qInv c)) (psC ratRing c)
        = psC ratRing (ratRing.mul (qInv c) c) :=
      ((psConstHom ratRing).map_mul (qInv c) c).symm
    have hstep1 : psAdd ratRing
        (psMul ratRing
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).s) f)
        (psMul ratRing
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).t) x.val)
        = psMul ratRing (psC ratRing (qInv c))
            (psAdd ratRing
              (psMul ratRing (pefBezout f x.val (nf + 1) (d + 1) d).s f)
              (psMul ratRing (pefBezout f x.val (nf + 1) (d + 1) d).t x.val)) :=
      pbz_scale_comb (psRing ratRing) (psC ratRing (qInv c))
        (pefBezout f x.val (nf + 1) (d + 1) d).s
        (pefBezout f x.val (nf + 1) (d + 1) d).t f x.val
    have hstep2 : psMul ratRing (psC ratRing (qInv c))
          (psAdd ratRing
            (psMul ratRing (pefBezout f x.val (nf + 1) (d + 1) d).s f)
            (psMul ratRing (pefBezout f x.val (nf + 1) (d + 1) d).t x.val))
        = psMul ratRing (psC ratRing (qInv c)) (psC ratRing c) :=
      congrArg (psMul ratRing (psC ratRing (qInv c))) hbez
    have hone : psAdd ratRing
        (psMul ratRing
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).s) f)
        (psMul ratRing
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).t) x.val)
        = psOne ratRing :=
      hstep1.trans (hstep2.trans (hmm.trans (congrArg (psC ratRing) hcancel)))
    -- (v) 合同伝播: x·red(c⁻¹t) ≡ x·(c⁻¹t) ≡ 1 (mod f)、pfdRed_char で = 1
    have step_a : gnfCong f
        (pfdRed f nf (pefBezout f x.val (nf + 1) (d + 1) d).Nt
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).t))
        (psMul ratRing (psC ratRing (qInv c))
          (pefBezout f x.val (nf + 1) (d + 1) d).t) :=
      gnfCong_red f nf hb hl (pefBezout f x.val (nf + 1) (d + 1) d).Nt
        (psMul ratRing (psC ratRing (qInv c))
          (pefBezout f x.val (nf + 1) (d + 1) d).t) htt_bN
    have step_b : gnfCong f
        (psMul ratRing x.val
          (pfdRed f nf (pefBezout f x.val (nf + 1) (d + 1) d).Nt
            (psMul ratRing (psC ratRing (qInv c))
              (pefBezout f x.val (nf + 1) (d + 1) d).t)))
        (psMul ratRing x.val
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).t)) :=
      gnfCong_mul_left f x.val hxpoly step_a
    have step_c : gnfCong f
        (psMul ratRing x.val
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).t))
        (psMul ratRing
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).t) x.val) :=
      gnfCong_of_eq f _ _
        ((psRing ratRing).mul_comm x.val
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).t))
    have step_d : gnfCong f
        (psMul ratRing
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).t) x.val)
        (psOne ratRing) :=
      ⟨gnfCR.neg
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).s),
        ⟨1 + (pefBezout f x.val (nf + 1) (d + 1) d).Ns,
          simpleExt_neg_bounded ratRing
            (simpleExt_mul_bounded ratRing hpsC1 hsNs)⟩,
        gnfSubHelper gnfCR (psOne ratRing)
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).s)
          (psMul ratRing
            (psMul ratRing (psC ratRing (qInv c))
              (pefBezout f x.val (nf + 1) (d + 1) d).t) x.val)
          f hone.symm⟩
    have hcong : gnfCong f
        (psMul ratRing x.val
          (pfdRed f nf (pefBezout f x.val (nf + 1) (d + 1) d).Nt
            (psMul ratRing (psC ratRing (qInv c))
              (pefBezout f x.val (nf + 1) (d + 1) d).t)))
        (psOne ratRing) :=
      gnfCong_trans f step_b (gnfCong_trans f step_c step_d)
    obtain ⟨hh, ⟨Nhh, hhb⟩, hhe⟩ := hcong
    funext j
    exact pfdRed_char f nf hb hl nf
      (psMul ratRing x.val
        (pfdRed f nf (pefBezout f x.val (nf + 1) (d + 1) d).Nt
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).t)))
      (psOne ratRing)
      (simpleExt_mul_bounded ratRing x.property
        (pfdRed_bound f nf hb hl (pefBezout f x.val (nf + 1) (d + 1) d).Nt
          (psMul ratRing (psC ratRing (qInv c))
            (pefBezout f x.val (nf + 1) (d + 1) d).t) htt_bN))
      (fun i hi => if_neg (by omega))
      ⟨hh, Nhh, hhb, fun k => congrFun hhe k⟩ j

/-! ## F6-5: 体インスタンス `IUTField` / `Field268`（(A) の頂点） -/

/-- **F6-5a: 全域 inv 付き実体 `IUTField`** — NF 担体 `GefNF f nf`（実 ℚ[x]/(f)
    の第二表示）が、既約 f のもとで**全域 inv 付きの本物の体**（`IUTField`）を
    なす。逆元は全域関数 `gefNFInv`（∃ 形でなく）。 -/
def gefNFIUTField (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) : IUTField where
  toCRing := gefNFRing f nf hb hl hn
  inv := gefNFInv f nf hb hl hn
  mul_inv_cancel := gefNF_mul_inv_cancel f nf hb hl hn hirr
  inv_zero := gefNF_inv_zero f nf hb hl hn
  zero_ne_one := (gnf_zero_ne_one f nf hb hl hn).symm

/-- **F6-5b: `Field268` インスタンス** — 除法定理・拡張ユークリッドの入力
    （塔の次段 K[x]/(g) の基礎体）となる `Field268`（ring + invf +
    mul_inv_cancel）を `gefNFInv` で充填。課題文の `gefField268` に相当。 -/
def gefNF268 (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) : Field268 where
  ring := (gefNFIUTField f nf hb hl hn hirr).toCRing
  invf := gefNFInv f nf hb hl hn
  mul_inv_cancel := gefNF_mul_inv_cancel f nf hb hl hn hirr

end IUT

#print axioms IUT.gefNFIUTField
#print axioms IUT.gefNF268
