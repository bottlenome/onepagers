/-
  IUT/PolyEuclidFn.lean — Wave2/F4（A1 0.80→0.85 設計 §1 F4）:
  拡張ユークリッドの Type 値関数 `pefGcd`/`pefBezout`（数値上界データ付き）

  ── 主要成果の分類: **[実]**（本物の先行建設。既存 `pgbExtGcdAuxB`
     （PGB-3・∃ 定理）の witness を choice-free な Type 値関数へ昇格）。

  **complete_pct 影響**: A1（実 ℚ[x]/(f)・全域 inv 付き実体）への承認済み足場。
  M270F/PGB-3 `pgbExtGcdAuxB` は Bezout 係数 s,t・gcd gg を fuel 帰納の各段で
  明示構成するが、結論が ∃（Prop）かつ分岐が `hlead_oracle` の Prop 値 Or
  であるため witness を Type レベルで取り出せない。本層は **同じ fuel 帰納の
  witness をそのまま `def pefGcd`（`PefOut` 値の Type 値関数）に写経**し、
  分岐を `ploFind`（F1・Bool 零判定に基づく Type 値探索）へ置換、
  さらに Bezout 係数の多項式性を（PGB-3 の Prop 値 `IsPoly` ではなく）
  **数値上界データ `Ns`/`Nt`** として構造体に一緒に返す。NF 担体上の全域 inv
  （F6 `gefNFInv`）の入力。complete_pct は本ファイル単体では未前進
  （A1 は F5/F6 完了後の独立再監査で確定）。complete_pct 未設定。

  本物性: `pefGcd` は `pgbExtGcdAuxB` の証明本体の各段 witness を名前付き def に
  転記したもので、**新規 Classical.choice を導入しない**（除法は F3 `pfdDivMod`
  関数、零判定は F1 `qIsZero`/`ploFind` で choice-free）。`pefGcd_spec` は PGB-3 と
  同一の結論（∃ を `PefOut` の射影 s/t/gg/mg に、Prop 値 `IsPoly` を数値上界
  `Ns`/`Nt` に置換した形）を同一の fuel 帰納で（今度は関数の出力について）証明する。

  正直な限定:
   - 多項式は有限台の係数列 PS = ℕ→ℚ として扱い、次数上界は明示パラメータ。
   - 対象体は実 ℚ（ratRing・qInv 経由の pfdDivMod・ploFind）に固定。
     一般 Field268 への一般化は写経の反復で可能だが本層では ℚ 固定。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク不使用。
  サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyDivModFn
import IUT.PolyLeadFindQ
import IUT.PolyBezoutBounded
import IUT.SimpleExtension

namespace IUT

/-! ## F4-1: 拡張ユークリッドの出力構造体（Bezout 係数・gcd・数値上界データ） -/

/-- **F4-1: 拡張ユークリッド出力** — Bezout 係数 `s`, `t`、gcd `gg`、その先頭
    次数 `mg`（`gg mg ≠ 0`）と、`s`,`t` の数値上界 `Ns`,`Nt`。PGB-3 が Prop 値
    `IsPoly` で持ち回る係数の多項式性を **データ（Nat 上界）** として返す。 -/
structure PefOut where
  s : PS ratRing
  t : PS ratRing
  gg : PS ratRing
  mg : Nat
  Ns : Nat
  Nt : Nat

/-! ## F4-2: 拡張ユークリッド関数（`pgbExtGcdAuxB` の各段 witness を転記） -/

/-- **F4-2: 拡張ユークリッド互除法の Type 値関数** — 固定した f, g に対し、対
    (a, b)（各々 f,g の既知の組合せ・数値上界付き）を b で割り進め、gcd `gg` と
    その組合せ **gg = s·f + t·g**、係数 s,t とその上界 Ns,Nt を `PefOut` で返す。
    `pgbExtGcdAuxB`（PGB-3）の fuel 帰納の各段 witness をそのまま関数化:
    除法は `pfdDivMod`（F3）、剰余の零判定/先頭次数探索は `ploFind`（F1）。
    fuel=0 のダミー枝（到達しない）は `⟨sb,tb,b,mb,Nsb,Ntb⟩`。 -/
def pefGcd (f g : PS ratRing) :
    Nat →
    PS ratRing → PS ratRing →
    PS ratRing → PS ratRing → PS ratRing → PS ratRing →
    Nat → Nat → Nat → Nat → Nat → Nat →
    PefOut
  | 0, _, b, _, _, sb, tb, _, mb, _, _, Nsb, Ntb => ⟨sb, tb, b, mb, Nsb, Ntb⟩
  | fuel + 1, a, b, sa, ta, sb, tb, Na, mb, Nsa, Nta, Nsb, Ntb =>
      match ploFind (pfdDivMod b mb Na a).2 mb with
      | none => ⟨sb, tb, b, mb, Nsb, Ntb⟩
      | some dr =>
          pefGcd f g fuel b (pfdDivMod b mb Na a).2 sb tb
            (psAdd ratRing sa (psNeg ratRing (psMul ratRing (pfdDivMod b mb Na a).1 sb)))
            (psAdd ratRing ta (psNeg ratRing (psMul ratRing (pfdDivMod b mb Na a).1 tb)))
            (mb + 1) dr Nsb Ntb (Nsa + (Na + 1) + Nsb) (Nta + (Na + 1) + Ntb)

/-! ## F4-3: 仕様（PGB-3 と同一結論・同一 fuel 帰納で・関数の出力について） -/

/-- **F4-3: 拡張ユークリッド関数の仕様** — `pgbExtGcdAuxB`（PGB-3）の結論そのもの
    （∃ を `pefGcd` の射影 `out.s`/`out.t`/`out.gg`/`out.mg` に、Prop 値 `IsPoly`
    を数値上界 `out.Ns`/`out.Nt` に置換した形）。同一の fuel 帰納で、除法段は
    `pfdDivMod_spec`（F3）、零判定/探索は `ploFind_none`/`ploFind_some`（F1）に
    より写経して証明する。 -/
theorem pefGcd_spec (f g : PS ratRing) :
    ∀ (fuel : Nat) (a b sa ta sb tb : PS ratRing)
      (Na mb Nsa Nta Nsb Ntb : Nat),
      IsPolyBounded ratRing a Na → IsPolyBounded ratRing b (mb + 1) →
      b mb ≠ ratRing.zero → mb < fuel →
      a = psAdd ratRing (psMul ratRing sa f) (psMul ratRing ta g) →
      b = psAdd ratRing (psMul ratRing sb f) (psMul ratRing tb g) →
      IsPolyBounded ratRing sa Nsa → IsPolyBounded ratRing ta Nta →
      IsPolyBounded ratRing sb Nsb → IsPolyBounded ratRing tb Ntb →
      (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).gg
          = psAdd ratRing
              (psMul ratRing (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).s f)
              (psMul ratRing (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).t g) ∧
        IsPolyBounded ratRing (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).gg
          ((pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).mg + 1) ∧
        (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).gg
          (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).mg ≠ ratRing.zero ∧
        pdbDvd ratRing (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).gg a ∧
        pdbDvd ratRing (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).gg b ∧
        IsPolyBounded ratRing (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).s
          (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).Ns ∧
        IsPolyBounded ratRing (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).t
          (pefGcd f g fuel a b sa ta sb tb Na mb Nsa Nta Nsb Ntb).Nt := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b sa ta sb tb Na mb Nsa Nta Nsb Ntb _ _ _ hfuel _ _ _ _ _ _
    exact absurd hfuel (Nat.not_lt_zero mb)
  | succ k ih =>
    intro a b sa ta sb tb Na mb Nsa Nta Nsb Ntb hNa hb hbl hfuel hac hbc hsa hta hsb htb
    have haN : IsPolyBounded ratRing a (Na + mb) :=
      pbzBound_mono ratRing hNa (Nat.le_add_right Na mb)
    -- pefGcd (k+1) の 1 段展開（fuel 構造再帰の rfl）。
    have hunf : pefGcd f g (k + 1) a b sa ta sb tb Na mb Nsa Nta Nsb Ntb
        = match ploFind (pfdDivMod b mb Na a).2 mb with
          | none => (⟨sb, tb, b, mb, Nsb, Ntb⟩ : PefOut)
          | some dr =>
              pefGcd f g k b (pfdDivMod b mb Na a).2 sb tb
                (psAdd ratRing sa
                  (psNeg ratRing (psMul ratRing (pfdDivMod b mb Na a).1 sb)))
                (psAdd ratRing ta
                  (psNeg ratRing (psMul ratRing (pfdDivMod b mb Na a).1 tb)))
                (mb + 1) dr Nsb Ntb (Nsa + (Na + 1) + Nsb) (Nta + (Na + 1) + Ntb) := rfl
    obtain ⟨hqb, hrb, heq⟩ := pfdDivMod_spec b mb hb hbl Na a haN
    -- 剰余の零判定で分岐し、各枝で pefGcd を「その枝の値」へ書き換えてから
    -- 除法商・剰余を不透明変数 q, r へ一般化する（`a` を含む射影を消す）。
    cases hpf : ploFind (pfdDivMod b mb Na a).2 mb with
    | none =>
      have hval : pefGcd f g (k + 1) a b sa ta sb tb Na mb Nsa Nta Nsb Ntb
          = (⟨sb, tb, b, mb, Nsb, Ntb⟩ : PefOut) := by rw [hunf, hpf]
      rw [hval]
      revert hpf hqb hrb heq
      generalize (pfdDivMod b mb Na a).2 = r
      generalize (pfdDivMod b mb Na a).1 = q
      intro hqb hrb heq hpf
      have ha : a = psAdd ratRing (psMul ratRing q b) r := funext heq
      have hqPoly : IsPoly ratRing q := ⟨Na + 1, hqb⟩
      have hrz : ∀ i, r i = ratRing.zero := ploFind_none r mb hrb hpf
      refine ⟨hbc, hb, hbl, ⟨q, hqPoly, ?_⟩, pgbDvd_refl ratRing b, hsb, htb⟩
      have hrz' : r = psZero ratRing := funext hrz
      rw [ha, hrz']
      exact CRing.add_zero (psRing ratRing) (psMul ratRing q b)
    | some dr =>
      have hval : pefGcd f g (k + 1) a b sa ta sb tb Na mb Nsa Nta Nsb Ntb
          = pefGcd f g k b (pfdDivMod b mb Na a).2 sb tb
              (psAdd ratRing sa
                (psNeg ratRing (psMul ratRing (pfdDivMod b mb Na a).1 sb)))
              (psAdd ratRing ta
                (psNeg ratRing (psMul ratRing (pfdDivMod b mb Na a).1 tb)))
              (mb + 1) dr Nsb Ntb (Nsa + (Na + 1) + Nsb) (Nta + (Na + 1) + Ntb) := by
        rw [hunf, hpf]
      rw [hval]
      revert hpf hqb hrb heq
      generalize (pfdDivMod b mb Na a).2 = r
      generalize (pfdDivMod b mb Na a).1 = q
      intro hqb hrb heq hpf
      have ha : a = psAdd ratRing (psMul ratRing q b) r := funext heq
      have hqPoly : IsPoly ratRing q := ⟨Na + 1, hqb⟩
      have hrc : r = psAdd ratRing
          (psMul ratRing (psAdd ratRing sa (psNeg ratRing (psMul ratRing q sb))) f)
          (psMul ratRing (psAdd ratRing ta (psNeg ratRing (psMul ratRing q tb))) g) := by
        have hr_eq : r = psAdd ratRing a (psNeg ratRing (psMul ratRing q b)) := by
          rw [ha]
          exact (pbz_sub_recover (psRing ratRing) (psMul ratRing q b) r).symm
        rw [hr_eq, hac, hbc]
        exact pbz_comb_sub (psRing ratRing) f g q sa ta sb tb
      obtain ⟨hdr_ne, hdr_bound⟩ := ploFind_some r mb hrb hpf
      have hdrlt : dr < mb := by
        cases Nat.lt_or_ge dr mb with
        | inl h => exact h
        | inr h => exact absurd (hrb dr h) hdr_ne
      have hdrk : dr < k := by omega
      have hsr : IsPolyBounded ratRing
          (psAdd ratRing sa (psNeg ratRing (psMul ratRing q sb)))
          (Nsa + (Na + 1) + Nsb) :=
        pbzBound_mono ratRing
          (simpleExt_add_bounded ratRing hsa
            (simpleExt_neg_bounded ratRing (simpleExt_mul_bounded ratRing hqb hsb)))
          (by omega)
      have htr : IsPolyBounded ratRing
          (psAdd ratRing ta (psNeg ratRing (psMul ratRing q tb)))
          (Nta + (Na + 1) + Ntb) :=
        pbzBound_mono ratRing
          (simpleExt_add_bounded ratRing hta
            (simpleExt_neg_bounded ratRing (simpleExt_mul_bounded ratRing hqb htb)))
          (by omega)
      obtain ⟨hgc, hgbd, hgld, hdvd_gb, hdvd_gr, hsNs, htNt⟩ :=
        ih b r sb tb
          (psAdd ratRing sa (psNeg ratRing (psMul ratRing q sb)))
          (psAdd ratRing ta (psNeg ratRing (psMul ratRing q tb)))
          (mb + 1) dr Nsb Ntb (Nsa + (Na + 1) + Nsb) (Nta + (Na + 1) + Ntb)
          hb hdr_bound hdr_ne hdrk hbc hrc hsb htb hsr htr
      -- 再帰結果を不透明 `out` に一般化（`gg = out.gg` が b, r を含まないように
      -- して、上向き伝播の余因子計算で b/r の誤書換えを防ぐ）。
      revert hgc hgbd hgld hdvd_gb hdvd_gr hsNs htNt
      generalize pefGcd f g k b r sb tb
        (psAdd ratRing sa (psNeg ratRing (psMul ratRing q sb)))
        (psAdd ratRing ta (psNeg ratRing (psMul ratRing q tb)))
        (mb + 1) dr Nsb Ntb (Nsa + (Na + 1) + Nsb) (Nta + (Na + 1) + Ntb) = out
      intro hgc hgbd hgld hdvd_gb hdvd_gr hsNs htNt
      refine ⟨hgc, hgbd, hgld, ?_, hdvd_gb, hsNs, htNt⟩
      obtain ⟨cb, hcbP, hcb⟩ := hdvd_gb
      obtain ⟨cr, hcrP, hcr⟩ := hdvd_gr
      refine ⟨psAdd ratRing (psMul ratRing q cb) cr, ?_, ?_⟩
      · exact pgb_isPoly_add ratRing (pgb_isPoly_mul ratRing hqPoly hcbP) hcrP
      · rw [ha, hcb, hcr]
        exact pbz_dvd_comb (psRing ratRing) q cb cr out.gg

/-! ## F4-4: Bezout（初期組合せ 1,0,0,1・fuel = deg b + 1） -/

/-- **F4-4: Bezout 恒等式の Type 値版** — f・a（a の先頭係数 a mb ≠ 0）から
    gcd `gg` と Bezout 係数 s,t を取り、`pgbBezoutB`（PGB-4）に対応する
    `PefOut` を返す。初期対 (f, a) の組合せ係数 1, 0, 0, 1（上界 1,0,0,1）で
    `pefGcd` を fuel = mb + 1 で回す。 -/
def pefBezout (f a : PS ratRing) (Nf Na mb : Nat) : PefOut :=
  pefGcd f a (mb + 1) f a (psOne ratRing) (psZero ratRing) (psZero ratRing) (psOne ratRing)
    Nf mb 1 0 0 1

/-- **F4-5: Bezout 関数の仕様** — `pgbBezoutB`（PGB-4）に対応: gg = s·f + t·a、
    gg は (mg+1) 有界・先頭 ≠ 0、gg は f・a を有界余因子で割り、s,t は数値上界
    Ns,Nt で有界。初期組合せ 1,0,0,1・fuel = mb+1 で `pefGcd_spec` を適用する。 -/
theorem pefBezout_spec (f a : PS ratRing) (Nf Na mb : Nat)
    (hf : IsPolyBounded ratRing f Nf)
    (ha : IsPolyBounded ratRing a (mb + 1))
    (hal : a mb ≠ ratRing.zero) :
    (pefBezout f a Nf Na mb).gg
        = psAdd ratRing (psMul ratRing (pefBezout f a Nf Na mb).s f)
            (psMul ratRing (pefBezout f a Nf Na mb).t a) ∧
      IsPolyBounded ratRing (pefBezout f a Nf Na mb).gg
        ((pefBezout f a Nf Na mb).mg + 1) ∧
      (pefBezout f a Nf Na mb).gg (pefBezout f a Nf Na mb).mg ≠ ratRing.zero ∧
      pdbDvd ratRing (pefBezout f a Nf Na mb).gg f ∧
      pdbDvd ratRing (pefBezout f a Nf Na mb).gg a ∧
      IsPolyBounded ratRing (pefBezout f a Nf Na mb).s (pefBezout f a Nf Na mb).Ns ∧
      IsPolyBounded ratRing (pefBezout f a Nf Na mb).t (pefBezout f a Nf Na mb).Nt := by
  have hOne : IsPolyBounded ratRing (psOne ratRing) 1 := by
    intro i hi
    show (if i = 0 then ratRing.one else ratRing.zero) = ratRing.zero
    exact if_neg (by omega)
  have hZero : IsPolyBounded ratRing (psZero ratRing) 0 := by
    intro i _
    rfl
  have hfc : f = psAdd ratRing (psMul ratRing (psOne ratRing) f)
      (psMul ratRing (psZero ratRing) a) := by
    rw [show psMul ratRing (psOne ratRing) f = f from (psRing ratRing).one_mul f,
      show psMul ratRing (psZero ratRing) a = psZero ratRing
        from CRing.zero_mul (psRing ratRing) a]
    exact (CRing.add_zero (psRing ratRing) f).symm
  have hac : a = psAdd ratRing (psMul ratRing (psZero ratRing) f)
      (psMul ratRing (psOne ratRing) a) := by
    rw [show psMul ratRing (psZero ratRing) f = psZero ratRing
        from CRing.zero_mul (psRing ratRing) f,
      show psMul ratRing (psOne ratRing) a = a from (psRing ratRing).one_mul a]
    exact ((psRing ratRing).zero_add a).symm
  exact pefGcd_spec f a (mb + 1) f a (psOne ratRing) (psZero ratRing)
    (psZero ratRing) (psOne ratRing) Nf mb 1 0 0 1
    hf ha hal (Nat.lt_succ_self mb) hfc hac hOne hZero hZero hOne

end IUT
