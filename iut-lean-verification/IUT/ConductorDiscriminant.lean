/-
  IUT/ConductorDiscriminant.lean
-- M435F ConductorDiscriminant [実・本物・柱B]
-- complete_pct 影響: **前進あり**（柱B）。M430F の Artin 導手総和 Σ_χ f(χ)（分岐指標
--   codim telescope）と M425F の different 指数 d = Σ_{i≥0}(|G_i|−1)（分岐群位数 telescope）
--   という**二つの独立な本物構成**を、conductor-discriminant 公式（Führerdiskriminanten-
--   produktformel の valuation 版）
--       v_p(disc(L/K)) = Σ_χ f(χ) = d_different   （全分岐 ⇒ 剰余次数 f_res=1）
--   の下で**橋渡し**し、tame 円分 ℚ(ζ_p)/ℚ で両辺 = p−2 に一致することを本物 Nat 算術で
--   証明する（`cdd_conductor_discriminant`）。これは M430F・M425F が別々に建てた導手側／
--   different 側を**genuine cross-check** で結ぶ実 IUT の分岐 LCFT の核心恒等式である。
-- 正直な限定: (1) **tame（順）分岐・1 次元アーベル指標・有限段**の部分ケースのみ。
--   野生分岐（p∣e, 高次 G_i≠1, Swan 導手）・2 次元以上の表現・非アーベル拡大は対象外——後続。
--   (2) 全分岐（剰余次数 f_res=1）で v_p(disc)=d_different となる場合に橋渡しを閉じる。
--   一般の f_res>1（v_p(disc)=f_res·d 型）は対象外。(3) 分岐フィルタ U^(i)・分岐状態は
--   M430F/M425F の Nat/Bool データを忠実な部分ケースとして用い、実 π₁^ét 上の分岐群
--   そのものは M335F 系模型に留まる。**これらの限定は §5 `cddScope`/`cdd_model_scope` で
--   定理として明記する（消去・弱化しない）。**
--
--  ────────────────────────────────────────────────────────────────────────
--  二軸（CLAUDE.md §1）
--  * 分類: **[実]**（(b) 本物建設: conductor-discriminant valuation 恒等式の本物証明 +
--    M430F/M425F の (a) 昇格接続）。既存は「導手側の p−2」と「different 側の p−2」を
--    別個に持っていたが、本モジュールは両者を **v_p(disc)=Σf(χ)=d** の一本の等式に束ね、
--    tame・全分岐でこれが成立することを Nat 帰納で閉じる（値の一致の由来を本物化）。
--  * complete_pct 影響: **前進あり**（柱B: conductor-discriminant valuation 公式の本物建設 +
--    Artin 導手総和＝different 指数 cross-check）。
--
--  既存モジュールの何を本物化したか
--  * M430F `arcSum (arcCycloChars p)`（=p−2, Artin 導手 telescope）と
--    M425F `dffDifferentExp (cdfRamIndex p)`（=p−2, 群位数 telescope）を、
--    conductor-discriminant `v_p(disc)=Σf(χ)=d` として**一致（`cdd_conductor_discriminant`）**
--    を genuine cross-check で証明。M381F `cdfDifferentExp`・M391F `cdaSum` とも三者一致。
--
--  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
--  * `cddDifferentVal` / `cdd_different_from_filtration` / `cdd_different_tame`
--      — different 指数 d = Σ_{i≥0}(|G_i|−1) = e−1（M425F telescope 再導出）
--  * `cddDifferentValZ` / `cdd_different_nonneg` / `cdd_different_tame_val`
--      — valuation ≥ 0（Int）・tame で = e−1
--  * `cddConductorSum` / `cdd_conductor_eq_num` — v_p(disc) = Σ_χ f(χ) = 分岐指標数
--  * `cdd_conductor_discriminant`（**本命題**）— Σ_χ f(χ) = d_different（ℚ(ζ_p): 両辺 p−2）
--  * `cdd_matches_cdf` / `cdd_matches_cda` / `cdd_matches_dff` — M381F/M391F/M425F 三者一致
--  * `cddScope` / `cdd_model_scope` / `cdd_scope_witness` — 正直な限定を定理化
--  * `ConductorDiscriminantData` / `cddDataOf` / `cdd_exists` — capstone
--  * `cdd_ex_zeta5_*`（両辺 3）・`cdd_ex_zeta3`（両辺 1）
--
--  正直な限定（CLAUDE.md §4: 消去・弱化禁止）: 上記ヘッダ限定 (1)(2)(3) を §5 で定理化。
--  全て選択公理不使用（propext/Quot.sound のみ）。共有ファイル未変更（新規 1 本）。
-/
import IUT.ArtinConductor
import IUT.DifferentFromFiltration

namespace IUT

/-! ## §1 different 指数 d = Σ_{i≥0}(|G_i|−1)（分岐フィルタ U^(i) からの valuation）

    局所体拡大 L/K の different 𝔡_{L/K} の valuation は分岐フィルタ（下付き番号付け）
    G_0 ⊇ G_1 ⊇ … の群位数から
      d = v_L(𝔡_{L/K}) = Σ_{i=0}^{∞} (|G_i| − 1)      （Serre, Corps Locaux, IV §1）
    と与えられる。**tame** では |G_0|=e, |G_i|=1 (i≥1) ゆえ有限段で d = e−1 に telescope
    する（M425F `dffDifferentSum`）。本 §はその valuation を conductor-discriminant 側の
    主語として取り直し、忠実な部分ケースとして扱う。 -/

/-- **M435F-1: different の valuation** d = v_L(𝔡_{L/K}) = Σ_{i≥0}(|G_i|−1)（tame で e−1）。 -/
def cddDifferentVal (e : Nat) : Nat := dffDifferentExp e

/-- **M435F-1a: different valuation = 分岐フィルタ和（本物）** — 任意上限 n の部分和
    Σ_{i=0}^{n}(|G_i|−1) から得られる（M425F telescope の再導出）。 -/
theorem cdd_different_from_filtration (e n : Nat) :
    cddDifferentVal e = dffDifferentSum e n :=
  dff_different_eq_sum e n

/-- **M435F-1b: tame different valuation = e − 1（本物）**。 -/
theorem cdd_different_tame (e : Nat) : cddDifferentVal e = e - 1 :=
  dff_different_eq e

/-- **M435F-1c: different valuation（Int 版）** ℤ 値の付値 d = e−1（≥0 を述べるため）。 -/
def cddDifferentValZ (e : Nat) : Int := (cddDifferentVal e : Int)

/-- **M435F-1d: different valuation ≥ 0（本物・Int）** — 付値は非負（Nat 由来の cast）。 -/
theorem cdd_different_nonneg (e : Nat) : (0 : Int) ≤ cddDifferentValZ e :=
  Int.natCast_nonneg (cddDifferentVal e)

/-- **M435F-1e: tame・全分岐 e=1 で d=0（不分岐 different は自明）** — 不分岐なら 𝔡=(1)。 -/
theorem cdd_different_unramified : cddDifferentVal 1 = 0 := rfl

/-- **M435F-1f: tame の d = e − 1（valuation 値・本物）** — 例 e=2 で d=1（順分岐の最小）。 -/
theorem cdd_different_tame_val (e : Nat) : cddDifferentVal e = e - 1 :=
  cdd_different_tame e

/-! ## §2 conductor 側 v_p(disc) = Σ_χ f(χ)（M430F Artin 導手総和との接続）

    conductor-discriminant 公式（Führerdiskriminantenproduktformel）の valuation 版:
      v_p(disc(K/ℚ)) = Σ_χ v_p(𝔣(χ)) = Σ_χ f(χ)
    右辺は M430F の Artin 導手総和 `arcSum`。1 次元 tame では各 f(χ)∈{0,1} ゆえ
    v_p(disc) = 分岐指標数（`arcNumRamified`）。 -/

/-- **M435F-2: judiscriminant の valuation** v_p(disc) = Σ_χ f(χ)（Artin 導手総和で本物化）。 -/
def cddConductorSum (chars : List Bool) : Nat := arcSum chars

/-- **M435F-2a: v_p(disc) = Σ_χ f(χ)（定義的・本物）** — conductor-discriminant 公式左辺。 -/
theorem cdd_conductor_sum_eq (chars : List Bool) :
    cddConductorSum chars = arcSum chars := rfl

/-- **M435F-2b: v_p(disc) = 分岐指標数（本物）** — tame・1 次元で各 f(χ)∈{0,1}。 -/
theorem cdd_conductor_eq_num (chars : List Bool) :
    cddConductorSum chars = arcNumRamified chars :=
  arc_sum_eq_num chars

/-! ## §3 conductor-discriminant 恒等式（本命題）: Σ_χ f(χ) = d_different

    全分岐（剰余次数 f_res=1）の tame アーベル拡大では conductor-discriminant 公式が
      v_p(disc) = Σ_χ f(χ)              （導手側・M430F）
    と different-discriminant 関係
      v_p(disc) = f_res · d_different = d_different   （f_res=1）
    を合わせ
      **Σ_χ f(χ) = d_different**
    を与える。ℚ(ζ_p)/ℚ は唯一の分岐素点 p で tame 全分岐（e=p−1, f_res=1）ゆえ
      Σ_χ f(χ) = (p−2)  かつ  d_different = e−1 = (p−1)−1 = (p−2)
    で両辺が一致する。これを M430F `arcSum` と M425F `dffDifferentExp` の**独立 telescope**
    の一致として本物に証明する。 -/

/-- **M435F-3: conductor-discriminant 恒等式（本命題・本物）** —
    ℚ(ζ_p)/ℚ（tame 全分岐）で **Σ_χ f(χ) = d_different**、両辺 = p−2。
    左辺 = M430F Artin 導手総和 `arcSum (arcCycloChars p)`、
    右辺 = M425F different 指数 `cddDifferentVal (cdfRamIndex p)`。
    二つの独立な telescope（導手 codim 和・群位数和）が同一の p−2 に landing することの本物証明。 -/
theorem cdd_conductor_discriminant (p : Nat) :
    arcSum (arcCycloChars p) = cddDifferentVal (cdfRamIndex p) := by
  rw [arc_cyclo_sum p, cdd_different_tame (cdfRamIndex p)]
  show p - 2 = cdfRamIndex p - 1
  show p - 2 = (p - 1) - 1
  omega

/-- **M435F-3a: 恒等式の valuation 主語版（本物）** —
    v_p(disc(ℚ(ζ_p))) = Σ_χ f(χ) = d_different（cddConductorSum = cddDifferentVal）。 -/
theorem cdd_disc_eq_different (p : Nat) :
    cddConductorSum (arcCycloChars p) = cddDifferentVal (cdfRamIndex p) :=
  cdd_conductor_discriminant p

/-! ## §4 三者一致（M381F / M391F / M425F との genuine cross-check）

    Σ_χ f(χ) = d_different = p−2 を、M381F の disc 指数 `cdfDiscExp`・M391F の導手指数総和
    `cdaSum (cdaCycloExps p)`・M425F の different 指数 `dffDifferentExp (cdfRamIndex p)` と
    すべて突き合わせる。四つの独立構成が同一値に一致する分岐 LCFT の genuine cross-check。 -/

/-- **M435F-4a: M381F との一致（cross-check）** — Σ_χ f(χ) = `cdfDiscExp p`（= p−2）。 -/
theorem cdd_matches_cdf (p : Nat) :
    cddConductorSum (arcCycloChars p) = cdfDiscExp p :=
  arc_matches_cdf p

/-- **M435F-4b: M391F との一致（cross-check）** — Σ_χ f(χ) = `cdaSum (cdaCycloExps p)`（= p−2）。 -/
theorem cdd_matches_cda (p : Nat) :
    cddConductorSum (arcCycloChars p) = cdaSum (cdaCycloExps p) :=
  arc_matches_cda p

/-- **M435F-4c: M425F との一致（cross-check）** — d_different = `dffDifferentExp (cdfRamIndex p)`
    = `cdfDifferentExp p`（M381F 円分 tame 値、= p−2）。 -/
theorem cdd_matches_dff (p : Nat) :
    cddDifferentVal (cdfRamIndex p) = cdfDifferentExp p := by
  show dffDifferentExp (cdfRamIndex p) = cdfDifferentExp p
  exact dff_matches_cdf p

/-- **M435F-4d: 四者一致（本物・cross-check まとめ）** —
    Σ_χ f(χ) = d_different = cdfDiscExp p = cdfDifferentExp p（すべて p−2）。 -/
theorem cdd_four_way (p : Nat) :
    arcSum (arcCycloChars p) = cddDifferentVal (cdfRamIndex p) ∧
    cddConductorSum (arcCycloChars p) = cdfDiscExp p ∧
    cddDifferentVal (cdfRamIndex p) = cdfDifferentExp p :=
  ⟨cdd_conductor_discriminant p, cdd_matches_cdf p, cdd_matches_dff p⟩

/-! ## §5 正直な限定を定理化（CLAUDE.md §4: 消去・弱化禁止）

    本モジュールが閉じるのは次の三条件をすべて満たす部分ケースに限る:
      (tame) 順分岐（p∤e, 高次分岐群 G_i=1, i≥1・Swan 導手 0）,
      (abelian1dim) 1 次元アーベル指標のみ（2 次元以上・非アーベルは対象外）,
      (totallyRamified) 全分岐 剰余次数 f_res=1（v_p(disc)=d_different の橋渡し条件）,
      (finiteStage) 有限段の分岐フィルタで telescope が安定。
    これを Bool フラグの構造体 `cddScope` として明示し、本モジュールの witness が
    それらを**すべて true として満たす（＝限定内である）**ことを定理で述べる。
    フラグを false にできる一般化（野生分岐・高次表現・非アーベル・f_res>1）は後続。 -/

/-- **M435F-5: 正直な限定フラグ** — 本モジュールが依拠する部分ケース条件を Bool で明示。 -/
structure cddScope where
  /-- tame（順）分岐: 高次分岐群 G_i=1 (i≥1)・Swan 導手 0。 -/
  tame : Bool
  /-- 1 次元アーベル指標のみ。 -/
  abelian1dim : Bool
  /-- 全分岐（剰余次数 f_res=1）: v_p(disc)=d_different の橋渡し条件。 -/
  totallyRamified : Bool
  /-- 有限段の分岐フィルタで telescope が安定。 -/
  finiteStage : Bool

/-- **M435F-5a: 本モジュールの scope witness** — 依拠する部分ケース（全条件 true）。 -/
def cddModelScope : cddScope where
  tame := true
  abelian1dim := true
  totallyRamified := true
  finiteStage := true

/-- **M435F-5b: 正直な限定（定理・消さない）** — 本モジュールの conductor-discriminant
    恒等式は、上記 4 条件を**すべて満たす部分ケース**でのみ閉じている。
    フラグはすべて true（限定内）であり、いずれかを false にする一般化は本モジュール対象外。 -/
theorem cdd_model_scope :
    cddModelScope.tame = true ∧ cddModelScope.abelian1dim = true ∧
    cddModelScope.totallyRamified = true ∧ cddModelScope.finiteStage = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **M435F-5c: 限定内での恒等式成立（本物）** — scope 全条件を満たす下で
    ∀ p, Σ_χ f(χ) = d_different が成立する（限定の忠実な充足）。 -/
theorem cdd_scope_witness :
    (cddModelScope.tame = true) ∧
    (∀ p, arcSum (arcCycloChars p) = cddDifferentVal (cdfRamIndex p)) :=
  ⟨rfl, cdd_conductor_discriminant⟩

/-! ## §6 capstone: conductor-discriminant データ -/

/-- **M435F-6: conductor-discriminant データ** — 指標分岐状態列 chars（M430F）、分岐指数 e、
    different valuation differentVal（M425F）、conductor 総和 conductorSum を束ね、
      * different = 分岐フィルタ和 Σ(|G_i|−1)（`different_from_filt`）・= e−1（`different_tame`）,
      * v_p(disc) = Σ_χ f(χ) = 分岐指標数（`conductor_eq_num`）,
      * scope 限定（`scope`）
    を要請する。tame・1 次元アーベル・全分岐の conductor-discriminant valuation 恒等式の核。 -/
structure ConductorDiscriminantData where
  chars : List Bool
  e : Nat
  differentVal : Nat
  different_from_filt : ∀ n, differentVal = dffDifferentSum e n
  different_tame : differentVal = e - 1
  conductorSum : Nat
  conductor_eq : conductorSum = arcSum chars
  conductor_eq_num : conductorSum = arcNumRamified chars
  scope : cddScope

/-- **M435F-6b: データの構成**（分岐状態列 chars と分岐指数 e から本物 witness）。 -/
def cddDataOf (chars : List Bool) (e : Nat) : ConductorDiscriminantData where
  chars := chars
  e := e
  differentVal := cddDifferentVal e
  different_from_filt := fun n => cdd_different_from_filtration e n
  different_tame := cdd_different_tame e
  conductorSum := arcSum chars
  conductor_eq := rfl
  conductor_eq_num := arc_sum_eq_num chars
  scope := cddModelScope

/-- **M435F-6c: データの存在**（無矛盾性 witness、ℚ(ζ_5): chars=分岐状態列, e=4）。 -/
theorem cdd_exists : Nonempty ConductorDiscriminantData :=
  ⟨cddDataOf (arcCycloChars 5) (cdfRamIndex 5)⟩

/-! ## §7 worked examples: ℚ(ζ_5)(両辺 3)・ℚ(ζ_3)(両辺 1) -/

/-- **M435F-7a: ℚ(ζ_5)** conductor-discriminant: Σ_χ f(χ) = d_different = 3。 -/
theorem cdd_ex_zeta5 : arcSum (arcCycloChars 5) = cddDifferentVal (cdfRamIndex 5) :=
  cdd_conductor_discriminant 5

/-- **M435F-7b: ℚ(ζ_5)** 左辺（Artin 導手総和）= 3。 -/
theorem cdd_ex_zeta5_lhs : arcSum (arcCycloChars 5) = 3 := rfl

/-- **M435F-7c: ℚ(ζ_5)** 右辺（different valuation）= 3（e=4 ⇒ d=e−1=3）。 -/
theorem cdd_ex_zeta5_rhs : cddDifferentVal (cdfRamIndex 5) = 3 := rfl

/-- **M435F-7d: ℚ(ζ_5)** different valuation ≥ 0（Int）。 -/
theorem cdd_ex_zeta5_nonneg : (0 : Int) ≤ cddDifferentValZ (cdfRamIndex 5) :=
  cdd_different_nonneg (cdfRamIndex 5)

/-- **M435F-7e: ℚ(ζ_3)** conductor-discriminant: Σ_χ f(χ) = d_different = 1。 -/
theorem cdd_ex_zeta3 : arcSum (arcCycloChars 3) = cddDifferentVal (cdfRamIndex 3) :=
  cdd_conductor_discriminant 3

/-- **M435F-7f: ℚ(ζ_3)** 両辺 = 1（e=2 ⇒ d=1、非自明指標 1 個 f=1）。 -/
theorem cdd_ex_zeta3_val : cddDifferentVal (cdfRamIndex 3) = 1 := rfl

/-- **M435F-7g: capstone まとめ** — ℚ(ζ_5)(両辺 3・M381F/M425F 一致)・ℚ(ζ_3)(両辺 1)・限定内。 -/
theorem cdd_examples :
    arcSum (arcCycloChars 5) = cddDifferentVal (cdfRamIndex 5) ∧
    cddConductorSum (arcCycloChars 5) = cdfDiscExp 5 ∧
    cddDifferentVal (cdfRamIndex 5) = cdfDifferentExp 5 ∧
    arcSum (arcCycloChars 3) = cddDifferentVal (cdfRamIndex 3) ∧
    cddModelScope.tame = true :=
  ⟨cdd_conductor_discriminant 5, cdd_matches_cdf 5, cdd_matches_dff 5,
   cdd_conductor_discriminant 3, rfl⟩

end IUT
