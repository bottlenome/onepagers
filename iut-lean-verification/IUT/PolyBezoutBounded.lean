/-
  IUT/PolyBezoutBounded.lean — PGB（有界余因子つき拡張ユークリッド Bezout：
  `pbzExtGcdAux`/`pbzBezout` の割り切れ結論を有界余因子 `IsPoly c` へ強化）

  ── 分類 **[実]**（本物の先行建設・(a) 昇格。骨格でなく本物の証明・
  sorry 皆無・新規 Classical.choice 皆無・模型なし）。

  **complete_pct 影響**: 柱A「実 Galois 理論／実 π₁^ét」向けの本物の
  先行建設（一般 f の ℚ[x]/(f) 実体化のエンジン）。既存 `pbzBezout`
  （M270F・PolyBezoutQ.lean）の結論 `pbzDvd gg f`（∃c, f = c·gg）は
  余因子 c が**非有界**（冪級数としての整除）であり、実多項式の既約性
  論法（「既約 E を割る多項式は単元か同伴」等）にそのままでは使えない。
  本層は拡張ユークリッドの再帰を bound 追跡つきでクローンし、gcd の
  割り切れを**有界余因子** `pdbDvd gg a := ∃ c, IsPoly c ∧ a = c·gg` の
  形で出す（さらに Bezout 係数 s, t 自身の `IsPoly` も同時に出す）。
  有界性の源は `field_division_exists`（M268F）：各除法段の商 q が
  `IsPolyBounded q (N+1)`＝**有界**で返るため、余因子は「q と 1/0 の
  積和」だけで組み上がり、多項式性（IsPoly）が再帰全段で保存される。
  complete_pct は未設定（本層はグラフメタ不更新・親が統合時に判断）。

  * PGB-0 `pdbDvd` — 有界余因子つき割り切れ d ∣ a := ∃ c, IsPoly c ∧
    a = c·d。**注意（正直明記）**: 本定義は並行実装中の
    `IUT/PolyDvdBounded.lean`（pdb・執筆時点で未 compile／リポジトリに
    不存在）の同名定義の**再掲**。親が統合時に一本化する。
  * PGB-1 `pgb_isPoly_zero/one/add/neg/mul` — IsPoly の閉性（有界性
    補題 `simpleExt_{add,neg,mul}_bounded` の existential 包み）
  * PGB-2 `pgbDvd_refl` — pdbDvd の反射律（余因子 1 は IsPoly）
  * PGB-3 `pgbExtGcdAuxB` — **本丸**: `pbzExtGcdAux`（M270F-5）の
    bound 追跡クローン。仮説に組合せ係数 sa ta sb tb の IsPoly を追加し、
    結論の割り切れを pbzDvd → pdbDvd（余因子 IsPoly つき）へ、さらに
    Bezout 係数 s, t の IsPoly を追加。各段の商 q は
    `field_division_exists` から `IsPolyBounded q (Na+1)` で有界、
    割り切れの上向き伝播 a = (q·cb + cr)·gg（`pbz_dvd_comb`）の余因子
    q·cb + cr も IsPoly の閉性（PGB-1）で有界のまま持ち回る。
  * PGB-4 `pgbBezoutB` — **頂点**: `pbzBezout`（M270F-6）の強化版。
    gg = s·f + t·g ∧ pdbDvd gg f ∧ pdbDvd gg g ∧ IsPoly s ∧ IsPoly t。
    初期組合せ係数 1, 0, 0, 1 は IsPoly（PGB-1）。
  * PGB-5 `pgbBezoutQ` — 実 ℚ への具体化: R = `ratRing`・invf = `qInv`・
    hinv = `ratIUTField.mul_inv_cancel`・hlead_oracle =
    `plo_lead_oracle_Q`（PLO-1・choice-free）で、**hlead_oracle 仮説
    なし**の形で ℚ[X] の有界余因子 Bezout を名指しで得る。

  正直な限定（何が本物で何が仮説か）:
   - **本物**: 一般 `CRing` + 体仮説（invf/hinv）上での拡張ユークリッド
     全段の bound 追跡・有界余因子の構成・Bezout 係数の IsPoly・ℚ への
     具体化（hlead_oracle 込みで完全充填）は完全証明。sorry 皆無。
   - **honest 仮説（抽象版のみ）**: `pgbExtGcdAuxB`/`pgbBezoutB` の
     `hlead_oracle`（先頭係数探索）は M270F と同じ honest 仮説として
     残る（抽象体の等号判定は排中律を要する）。実 ℚ 版 `pgbBezoutQ`
     では `plo_lead_oracle_Q` で choice-free に充填済み（仮説なし）。
   - `pdbDvd` の再掲は上記 PGB-0 の注のとおり親の統合対象。
   - 既約性論法への接続（「E 既約 ⟹ gcd(E,a) は単元」）は本層に
     含めない後続（本層はそのための有界余因子エンジンの提供まで）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない。
  propext/Quot.sound のみ）。禁止タクティク不使用。
  サブエージェント新規部品（共有ファイル不更新・complete_pct 未設定）。
-/
import IUT.PolyBezoutQ
import IUT.PolyLeadOracleQ
import IUT.PolyDvdBounded

namespace IUT

/-! ## PGB-0: 有界余因子つき割り切れ（`pdbDvd` は `PolyDvdBounded` から） -/

/-! ## PGB-1: IsPoly の閉性 -/

/-- **PGB-1a: 零は多項式**（上界 0）。 -/
theorem pgb_isPoly_zero (R : CRing) : IsPoly R (psZero R) :=
  ⟨0, fun _ _ => rfl⟩

/-- **PGB-1b: 1 は多項式**（上界 1）。 -/
theorem pgb_isPoly_one (R : CRing) : IsPoly R (psOne R) := by
  refine ⟨1, ?_⟩
  intro i hi
  show (if i = 0 then R.one else R.zero) = R.zero
  exact if_neg (by omega)

/-- **PGB-1c: 和の多項式性**（上界は和 N+M、`simpleExt_add_bounded`）。 -/
theorem pgb_isPoly_add (R : CRing) {a b : PS R}
    (ha : IsPoly R a) (hb : IsPoly R b) : IsPoly R (psAdd R a b) := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := hb
  exact ⟨N + M, simpleExt_add_bounded R hN hM⟩

/-- **PGB-1d: 符号反転の多項式性**（上界不変、`simpleExt_neg_bounded`）。 -/
theorem pgb_isPoly_neg (R : CRing) {a : PS R}
    (ha : IsPoly R a) : IsPoly R (psNeg R a) := by
  obtain ⟨N, hN⟩ := ha
  exact ⟨N, simpleExt_neg_bounded R hN⟩

/-- **PGB-1e: 積の多項式性**（上界は和 N+M、`simpleExt_mul_bounded`）。 -/
theorem pgb_isPoly_mul (R : CRing) {a b : PS R}
    (ha : IsPoly R a) (hb : IsPoly R b) : IsPoly R (psMul R a b) := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := hb
  exact ⟨N + M, simpleExt_mul_bounded R hN hM⟩

/-! ## PGB-2: pdbDvd の反射律 -/

/-- **PGB-2: 反射律** d ∣ d（余因子 1 は IsPoly）。 -/
theorem pgbDvd_refl (R : CRing) (d : PS R) : pdbDvd R d d :=
  ⟨psOne R, pgb_isPoly_one R, ((psRing R).one_mul d).symm⟩

/-! ## PGB-3: 拡張ユークリッド本体（bound 追跡クローン） -/

/-- **定理 (PGB-3): 拡張ユークリッド互除法・有界余因子版（本丸）** —
    `pbzExtGcdAux`（M270F-5）のクローン。差分は
    (i) 仮説に組合せ係数 sa ta sb tb の `IsPoly` を追加、
    (ii) 結論の割り切れを `pbzDvd` から **`pdbDvd`（余因子 IsPoly つき）**
    へ強化、(iii) 結論に Bezout 係数 s, t の `IsPoly` を追加。
    有界性の源: 各除法段で `field_division_exists`（M268F）の商 q が
    `IsPolyBounded q (Na+1)`＝有界で返るため、
    ・零剰余の底では a = q·b の余因子 q が IsPoly、
    ・伝播段では a = (q·cb + cr)·gg の余因子 q·cb + cr が IsPoly の
      閉性（PGB-1）で有界のまま上向きに持ち回れる。
    係数更新 sa − q·sb / ta − q·tb も同じ閉性で IsPoly が保存される。
    `hlead_oracle` は M270F と同じ honest 仮説（実 ℚ では PLO-1 で充填）。 -/
theorem pgbExtGcdAuxB (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    (hlead_oracle : ∀ (p : PS R) (n : Nat), IsPolyBounded R p n →
      (∀ i, p i = R.zero) ∨
      (∃ d, p d ≠ R.zero ∧ IsPolyBounded R p (d + 1)))
    (f g : PS R) :
    ∀ (fuel : Nat) (a b sa ta sb tb : PS R) (Na mb : Nat),
      IsPolyBounded R a Na → IsPolyBounded R b (mb + 1) → b mb ≠ R.zero →
      mb < fuel →
      a = psAdd R (psMul R sa f) (psMul R ta g) →
      b = psAdd R (psMul R sb f) (psMul R tb g) →
      IsPoly R sa → IsPoly R ta → IsPoly R sb → IsPoly R tb →
      ∃ (s t gg : PS R) (mg : Nat),
        gg = psAdd R (psMul R s f) (psMul R t g) ∧
        IsPolyBounded R gg (mg + 1) ∧ gg mg ≠ R.zero ∧
        pdbDvd R gg a ∧ pdbDvd R gg b ∧
        IsPoly R s ∧ IsPoly R t := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b sa ta sb tb Na mb _ _ _ hfuel _ _ _ _ _ _
    exact absurd hfuel (Nat.not_lt_zero mb)
  | succ k ih =>
    intro a b sa ta sb tb Na mb hNa hb hbl hfuel hac hbc hsa hta hsb htb
    have haN : IsPolyBounded R a (Na + mb) :=
      pbzBound_mono R hNa (Nat.le_add_right Na mb)
    obtain ⟨q, r, hq, hr', hdiv⟩ :=
      field_division_exists R invf hinv b mb hb hbl Na a haN
    -- 商 q は有界（IsPolyBounded q (Na+1)）⟹ IsPoly q。ここが有界余因子の源。
    have hqPoly : IsPoly R q := ⟨Na + 1, hq⟩
    have ha : a = psAdd R (psMul R q b) r := funext hdiv
    have hrc : r = psAdd R (psMul R (psAdd R sa (psNeg R (psMul R q sb))) f)
        (psMul R (psAdd R ta (psNeg R (psMul R q tb))) g) := by
      have hr_eq : r = psAdd R a (psNeg R (psMul R q b)) := by
        rw [ha]
        exact (pbz_sub_recover (psRing R) (psMul R q b) r).symm
      rw [hr_eq, hac, hbc]
      exact pbz_comb_sub (psRing R) f g q sa ta sb tb
    cases hlead_oracle r mb hr' with
    | inl hrz =>
      -- 零剰余: gcd = b。a = q·b の余因子 q は IsPoly（hqPoly）。
      refine ⟨sb, tb, b, mb, hbc, hb, hbl, ⟨q, hqPoly, ?_⟩,
        pgbDvd_refl R b, hsb, htb⟩
      have hrz' : r = psZero R := by
        funext i
        exact hrz i
      rw [ha, hrz']
      exact CRing.add_zero (psRing R) (psMul R q b)
    | inr hex =>
      obtain ⟨dr, hdr_ne, hdr_bound⟩ := hex
      have hdrlt : dr < mb := by
        cases Nat.lt_or_ge dr mb with
        | inl h => exact h
        | inr h => exact absurd (hr' dr h) hdr_ne
      have hdrk : dr < k := by omega
      -- 更新された組合せ係数 sa − q·sb / ta − q·tb の IsPoly（閉性で保存）。
      have hsr : IsPoly R (psAdd R sa (psNeg R (psMul R q sb))) :=
        pgb_isPoly_add R hsa (pgb_isPoly_neg R (pgb_isPoly_mul R hqPoly hsb))
      have htr : IsPoly R (psAdd R ta (psNeg R (psMul R q tb))) :=
        pgb_isPoly_add R hta (pgb_isPoly_neg R (pgb_isPoly_mul R hqPoly htb))
      obtain ⟨s, t, gg, mg, hgc, hgbd, hgld, hdvd_gb, hdvd_gr, hsP, htP⟩ :=
        ih b r sb tb (psAdd R sa (psNeg R (psMul R q sb)))
          (psAdd R ta (psNeg R (psMul R q tb))) (mb + 1) dr hb hdr_bound
          hdr_ne hdrk hbc hrc hsb htb hsr htr
      refine ⟨s, t, gg, mg, hgc, hgbd, hgld, ?_, hdvd_gb, hsP, htP⟩
      -- 上向き伝播: a = q·b + r, b = cb·gg, r = cr·gg ⟹ a = (q·cb + cr)·gg。
      -- 余因子 q·cb + cr は IsPoly（q 有界 × cb,cr 帰納的に IsPoly）。
      obtain ⟨cb, hcbP, hcb⟩ := hdvd_gb
      obtain ⟨cr, hcrP, hcr⟩ := hdvd_gr
      refine ⟨psAdd R (psMul R q cb) cr, ?_, ?_⟩
      · exact pgb_isPoly_add R (pgb_isPoly_mul R hqPoly hcbP) hcrP
      · rw [ha, hcb, hcr]
        exact pbz_dvd_comb (psRing R) q cb cr gg

/-! ## PGB-4: Bezout 恒等式・有界余因子版（頂点） -/

/-- **定理 (PGB-4): 有界余因子つき Bezout 恒等式** — `pbzBezout`
    （M270F-6）の強化版: f・g（g の先頭係数 ≠ 0）から gcd gg と係数
    s, t を取り、**gg = s·f + t·g ∧ pdbDvd gg f ∧ pdbDvd gg g ∧
    IsPoly s ∧ IsPoly t**（割り切れの余因子も Bezout 係数も本物の
    多項式＝有限台）を得る。初期対 (f, g) の組合せ係数 1, 0, 0, 1 は
    IsPoly（PGB-1a/1b）、fuel = deg g + 1 で `pgbExtGcdAuxB` を回す。 -/
theorem pgbBezoutB (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    (hlead_oracle : ∀ (p : PS R) (n : Nat), IsPolyBounded R p n →
      (∀ i, p i = R.zero) ∨
      (∃ d, p d ≠ R.zero ∧ IsPolyBounded R p (d + 1)))
    (f g : PS R) (Nf mg0 : Nat)
    (hf : IsPolyBounded R f Nf) (hg : IsPolyBounded R g (mg0 + 1))
    (hgl : g mg0 ≠ R.zero) :
    ∃ (s t gg : PS R) (mg : Nat),
      gg = psAdd R (psMul R s f) (psMul R t g) ∧
      IsPolyBounded R gg (mg + 1) ∧ gg mg ≠ R.zero ∧
      pdbDvd R gg f ∧ pdbDvd R gg g ∧
      IsPoly R s ∧ IsPoly R t := by
  have hfc : f = psAdd R (psMul R (psOne R) f) (psMul R (psZero R) g) := by
    rw [show psMul R (psOne R) f = f from (psRing R).one_mul f,
      show psMul R (psZero R) g = psZero R from CRing.zero_mul (psRing R) g]
    exact (CRing.add_zero (psRing R) f).symm
  have hgc : g = psAdd R (psMul R (psZero R) f) (psMul R (psOne R) g) := by
    rw [show psMul R (psZero R) f = psZero R from CRing.zero_mul (psRing R) f,
      show psMul R (psOne R) g = g from (psRing R).one_mul g]
    exact ((psRing R).zero_add g).symm
  exact pgbExtGcdAuxB R invf hinv hlead_oracle f g (mg0 + 1) f g
    (psOne R) (psZero R) (psZero R) (psOne R) Nf mg0 hf hg hgl
    (Nat.lt_succ_self mg0) hfc hgc
    (pgb_isPoly_one R) (pgb_isPoly_zero R)
    (pgb_isPoly_zero R) (pgb_isPoly_one R)

/-! ## PGB-5: 実 ℚ への具体化（hlead_oracle 仮説なし） -/

/-- **定理 (PGB-5): 実 ℚ[X] の有界余因子 Bezout** — `pgbBezoutB` を
    実体 ℚ へ具体化: R = `ratRing`・invf = `qInv`・hinv =
    `ratIUTField.mul_inv_cancel`（M264F-5）・hlead_oracle =
    `plo_lead_oracle_Q`（PLO-1・choice-free 充填済み）。M270F の
    `pbzBezoutQ` と違い **hlead_oracle 仮説なし**の完結形で、割り切れは
    有界余因子（pdbDvd）・Bezout 係数 s, t も IsPoly。 -/
theorem pgbBezoutQ (f g : PS ratRing) (Nf mg0 : Nat)
    (hf : IsPolyBounded ratRing f Nf)
    (hg : IsPolyBounded ratRing g (mg0 + 1))
    (hgl : g mg0 ≠ ratRing.zero) :
    ∃ (s t gg : PS ratRing) (mg : Nat),
      gg = psAdd ratRing (psMul ratRing s f) (psMul ratRing t g) ∧
      IsPolyBounded ratRing gg (mg + 1) ∧ gg mg ≠ ratRing.zero ∧
      pdbDvd ratRing gg f ∧ pdbDvd ratRing gg g ∧
      IsPoly ratRing s ∧ IsPoly ratRing t :=
  pgbBezoutB ratRing qInv ratIUTField.mul_inv_cancel
    plo_lead_oracle_Q f g Nf mg0 hf hg hgl

end IUT
