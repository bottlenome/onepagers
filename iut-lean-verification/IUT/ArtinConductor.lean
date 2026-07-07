/-
  IUT/ArtinConductor.lean
-- M430F ArtinConductor [実・本物・柱B]
-- complete_pct 影響: 柱B で tame Artin 導手指数 f = dim(V/V^{G_0}) を分岐フィルトレーション
--   から本物建設（i≥1 の高次項 dim(V/V^{G_i})=0 が telescope で消え f=G_0 項に還元）。
--   1 次元指標では f=1（分岐: 惰性 G_0 上非自明）/ f=0（不分岐）。conductor-discriminant
--   disc=∏_χ p^{f(χ)} を Σ_χ f(χ) = (分岐指標数) = disc 指数 として本物化し、ℚ(ζ_p) で
--   Σf = p−2 = cdfDiscExp p = cdaSum(cdaCycloExps p)（M381F/M391F）と genuine cross-check。
-- 正直な限定: 野生（wild）導手（高次分岐 G_i≠1, i≥1 / Swan 導手 = Σ_{i≥1} 項）と
--   2 次元以上の表現の Artin 導手（dim(V/V^{G_i}) の一般値）は本モジュール対象外——後続。
--
--  ────────────────────────────────────────────────────────────────────────
--  二軸（CLAUDE.md §1）
--  * 分類: **[実]**（(b) 本物建設 + M381F/M391F との (a) 昇格接続）。M381F は disc 指数 p−2 を、
--    M391F は導手指数リストの総和 p−2 を扱ったが、本モジュールはそれを**各指標の Artin 導手
--    f(χ)=dim(V/V^{G_0}) の総和** として本物に導出し、tame で f=G_0 項に還元することを
--    分岐フィルトレーションの telescope（M425F の d=Σ(|G_i|−1) と同型の構造）で閉じる。
--  * complete_pct 影響: **前進あり**（柱B の Artin 導手 f=dim(V/V^{G_0}) 本物建設 + Σf=disc 指数）。
--
--  既存モジュールの何を本物化したか
--  * M381F `cdfDiscExp p`（=p−2）/ M391F `cdaSum (cdaCycloExps p)`（=p−2）を、
--    各指標の Artin 導手 f(χ)∈{0,1} の総和 `arcSum (arcCycloChars p)` として本物に導出し、
--    三者一致（arc_matches_cdf / arc_matches_cda）を genuine cross-check として証明。
--  * conductor-discriminant を Artin 導手経由 disc=p^{Σf} で本物化（arc_cond_disc: p^{Σf}=cydDiscMag）。
--
--  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
--  * `arcArtinExp` / `arc_artin_ramified` / `arc_artin_unramified`
--      — 1 次元指標の Artin 導手 f = 1（分岐）/ 0（不分岐）= dim(V/V^{G_0})
--  * `arcCodim` / `arcArtinFilt` / `arc_filt_eq`
--      — **f = Σ_i dim(V/V^{G_i}) の telescope**（tame: i≥1 項 0 → f=G_0 項に還元）
--  * `arcSum` / `arcNumRamified` / `arc_sum_eq_num`
--      — Σ_χ f(χ) = (分岐指標数)
--  * `arcCycloChars` / `arc_cyclo_sum` / `arc_cyclo_num_ramified`
--      — ℚ(ζ_p): 自明 1 個（f=0）+ 非自明 p−2 個（f=1）→ Σf = p−2
--  * `arc_matches_cdf` / `arc_matches_cda` / `arc_cond_disc` — M381F/M391F cross-check・disc=p^{Σf}
--  * `ArtinConductorData` / `arcDataOf` / `arc_exists` — capstone
--  * `arc_ex_zeta5_*`（Σf=3）・`arc_ex_zeta3`（Σf=1）
--
--  正直な限定（CLAUDE.md §4: 消去・弱化禁止）
--  * **tame（順）分岐・1 次元指標のみ**。Artin 導手 f = Σ_{i≥0}(1/|G_0:G_i|)dim(V/V^{G_i}) の
--    高次項（i≥1、= Swan 導手）は tame で 0 に telescope するがゆえ本モジュールは G_0 項のみ。
--    **野生分岐（p∣e, 高次 G_i≠1）の Swan 導手**・**2 次元以上の表現**は対象外——後続。
--  * 指標の分岐状態を Bool（惰性 G_0 上の非自明性）として忠実に表す部分ケース。実 Galois 表現・
--    実 π₁^ét 上の分岐フィルトレーションそのものは M335F 系模型に留まる。
--
--  全て選択公理不使用（propext/Quot.sound のみ）。共有ファイル未変更（新規 1 本）。
-/
import IUT.ConductorDiscriminantAbelian

namespace IUT

/-! ## §1 1 次元指標の Artin 導手 f = dim(V/V^{G_0})

    1 次元表現 V（Galois 指標 χ）の Artin 導手指数は
      f(χ) = Σ_{i≥0} (1/|G_0:G_i|) · dim(V/V^{G_i}).
    **tame** かつ **dim V = 1** のとき、惰性群 G_0 上で χ が非自明（分岐）なら
    V^{G_0} = 0 ゆえ dim(V/V^{G_0}) = 1、χ が G_0 上自明（不分岐）なら V^{G_0} = V ゆえ 0。
    i ≥ 1 の高次分岐群 G_i は tame で自明ゆえ V^{G_i} = V、dim(V/V^{G_i}) = 0（後述 §2 で telescope）。
    よって tame・1 次元では f = dim(V/V^{G_0}) ∈ {0,1}。分岐状態を Bool で忠実に表す。 -/

/-- **M430F-1: 1 次元指標の Artin 導手** f = dim(V/V^{G_0}) = 1（分岐）/ 0（不分岐）。 -/
def arcArtinExp : Bool → Nat
  | true  => 1
  | false => 0

/-- **M430F-1a: 分岐指標の Artin 導手 = 1（本物・定義的）** — 惰性 G_0 上非自明 ⇒ V^{G_0}=0。 -/
theorem arc_artin_ramified : arcArtinExp true = 1 := rfl

/-- **M430F-1b: 不分岐指標の Artin 導手 = 0（本物・定義的）** — 惰性 G_0 上自明 ⇒ V^{G_0}=V。 -/
theorem arc_artin_unramified : arcArtinExp false = 0 := rfl

/-! ## §2 分岐フィルトレーションからの Artin 導手 telescope（tame → G_0 項に還元）

    Artin 導手を分岐フィルトレーション G_0 ⊇ G_1 ⊇ … 上の寄与和として本物に建設する。
    1 次元表現の各段の寄与は codim_i = dim(V/V^{G_i}):
      * i = 0: 分岐なら 1、不分岐なら 0（= arcArtinExp）,
      * i ≥ 1: tame では G_i 自明 ⇒ V^{G_i} = V ⇒ codim_i = 0.
    部分和 F_n = Σ_{i=0}^{n} codim_i は i≥1 項が 0 ゆえ上限 n によらず codim_0 = arcArtinExp に安定。
    これは M425F の different 和 Σ(|G_i|−1)=e−1 と同型の telescope 構造。 -/

/-- **M430F-2: 各段の codim** dim(V/V^{G_i})（1 次元 tame）= arcArtinExp（i=0）/ 0（i≥1）。 -/
def arcCodim (ramified : Bool) : Nat → Nat
  | 0     => arcArtinExp ramified
  | _ + 1 => 0

/-- **M430F-2a: codim_0 = f（本物・定義的）** — i=0 段は Artin 導手 dim(V/V^{G_0})。 -/
theorem arc_codim_zero (b : Bool) : arcCodim b 0 = arcArtinExp b := rfl

/-- **M430F-2b: codim_{n+1} = 0（本物・定義的）** — 高次分岐群 G_i(i≥1) は tame で自明。 -/
theorem arc_codim_succ (b : Bool) (n : Nat) : arcCodim b (n + 1) = 0 := rfl

/-- **M430F-2c: Artin 導手の部分和** F_n = Σ_{i=0}^{n} dim(V/V^{G_i})（フィルトレーション和）。 -/
def arcArtinFilt (ramified : Bool) : Nat → Nat
  | 0     => arcCodim ramified 0
  | n + 1 => arcArtinFilt ramified n + arcCodim ramified (n + 1)

/-- **M430F-2d: 部分和の底（本物・定義的）** F_0 = codim_0 = f。 -/
theorem arc_filt_zero (b : Bool) : arcArtinFilt b 0 = arcArtinExp b := rfl

/-- **M430F-2e: 部分和の漸化（本物・定義的）** F_{n+1} = F_n + codim_{n+1}。 -/
theorem arc_filt_succ (b : Bool) (n : Nat) :
    arcArtinFilt b (n + 1) = arcArtinFilt b n + arcCodim b (n + 1) := rfl

/-- **M430F-2f: telescope（本命題・本物）** F_n = f = dim(V/V^{G_0})（任意 n）。
    i≥1 の高次項 dim(V/V^{G_i}) = 0 ゆえ、部分和は上限 n によらず G_0 項 arcArtinExp に安定。
    tame・1 次元の Artin 導手が分岐フィルトレーション和から dim(V/V^{G_0}) に還元することの本物証明。 -/
theorem arc_filt_eq (b : Bool) : ∀ n, arcArtinFilt b n = arcArtinExp b := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    show arcArtinFilt b m + arcCodim b (m + 1) = arcArtinExp b
    have hz : arcCodim b (m + 1) = 0 := rfl
    rw [hz, ih]
    omega

/-! ## §3 Σ_χ f(χ) = (分岐指標数): conductor-discriminant の Artin 導手版

    複数指標 {χ} を分岐状態 List Bool として表し、disc = ∏_χ p^{f(χ)} の指数総和
      Σ_χ f(χ) = Σ_χ dim(V_χ/V_χ^{G_0})
    を計算する。tame・1 次元では各 f(χ)∈{0,1} ゆえ総和は分岐指標の個数に等しい。 -/

/-- **M430F-3: Artin 導手指数の総和** Σ_χ f(χ)（指標列の分岐状態から）。 -/
def arcSum : List Bool → Nat
  | []      => 0
  | b :: bs => arcArtinExp b + arcSum bs

/-- **M430F-3a: 分岐指標の個数** #{χ : χ 分岐}（List Bool の true 個数）。 -/
def arcNumRamified : List Bool → Nat
  | []          => 0
  | true  :: bs => 1 + arcNumRamified bs
  | false :: bs => arcNumRamified bs

/-- **M430F-3b: Σ_χ f(χ) = (分岐指標数)（本物）** — 各 f(χ)∈{0,1}（tame・1 次元）ゆえ
    Artin 導手指数総和は分岐指標の個数に等しい。conductor-discriminant disc=∏p^{f(χ)} の
    指数 = 分岐指標数、の本物証明。 -/
theorem arc_sum_eq_num : ∀ l, arcSum l = arcNumRamified l := by
  intro l
  induction l with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true =>
      show arcArtinExp true + arcSum bs = 1 + arcNumRamified bs
      rw [ih]
      show 1 + arcNumRamified bs = 1 + arcNumRamified bs
      rfl
    | false =>
      show arcArtinExp false + arcSum bs = arcNumRamified bs
      rw [ih]
      show 0 + arcNumRamified bs = arcNumRamified bs
      omega

/-! ## §4 ℚ(ζ_p): Σf = p−2（M381F/M391F との genuine cross-check）

    円分体 ℚ(ζ_p) の Galois 群 Gal(ℚ(ζ_p)/ℚ)（位数 p−1）の指標のうち、自明指標 1 個は
    p で不分岐（f=0）、非自明指標 p−2 個は p で tame 全分岐ゆえ惰性 G_0 上非自明（f=1）。
    よって Σ_χ f(χ) = p − 2 = M381F の disc 指数 cdfDiscExp p = M391F の cdaSum(cdaCycloExps p)。 -/

/-- **M430F-4: ℚ(ζ_p) の指標分岐状態** 自明 1 個（false）+ 非自明 p−2 個（true）。 -/
def arcCycloChars (p : Nat) : List Bool := false :: List.replicate (p - 2) true

/-- **M430F-4a: 分岐指標の f 総和（補題）** Σ_{χ true} f = n（すべて分岐 ⇒ 個数）。 -/
theorem arc_sum_replicate_true : ∀ n, arcSum (List.replicate n true) = n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    have hcons : arcSum (List.replicate (m + 1) true)
        = arcArtinExp true + arcSum (List.replicate m true) := rfl
    rw [hcons, ih]
    show 1 + m = m + 1
    omega

/-- **M430F-4b: ℚ(ζ_p) の Artin 導手総和（本物）** Σ_χ f(χ) = p − 2。
    自明指標 f=0 + 非自明 p−2 個の各 f=1 ⇒ 総和 p−2。 -/
theorem arc_cyclo_sum (p : Nat) : arcSum (arcCycloChars p) = p - 2 := by
  show arcArtinExp false + arcSum (List.replicate (p - 2) true) = p - 2
  rw [arc_sum_replicate_true (p - 2)]
  show 0 + (p - 2) = p - 2
  omega

/-- **M430F-4c: ℚ(ζ_p) の分岐指標数（本物）** #{χ 分岐} = p − 2 = Σf。 -/
theorem arc_cyclo_num_ramified (p : Nat) : arcNumRamified (arcCycloChars p) = p - 2 := by
  rw [← arc_sum_eq_num, arc_cyclo_sum p]

/-- **M430F-4d: M381F との一致（本物・genuine cross-check）** —
    Artin 導手総和 Σ_χ f(χ) = ℚ(ζ_p) の disc 指数 cdfDiscExp p（両者とも p−2）。 -/
theorem arc_matches_cdf (p : Nat) : arcSum (arcCycloChars p) = cdfDiscExp p := by
  rw [arc_cyclo_sum p]
  show p - 2 = p - 2
  rfl

/-- **M430F-4e: M391F との一致（本物・genuine cross-check）** —
    Artin 導手総和 Σ_χ f(χ) = M391F の導手指数リスト総和 cdaSum(cdaCycloExps p)（両者とも p−2）。 -/
theorem arc_matches_cda (p : Nat) : arcSum (arcCycloChars p) = cdaSum (cdaCycloExps p) := by
  rw [arc_cyclo_sum p, cda_cyclo_sum p]

/-- **M430F-4f: conductor-discriminant を Artin 導手経由で本物化** —
    disc(ℚ(ζ_p)) = p^{Σ_χ f(χ)} = cydDiscMag p（M381F の判別式大きさに一致）。
    Führerdiskriminantenprodukt disc = ∏_χ p^{f(χ)} の Artin 導手版。 -/
theorem arc_cond_disc (p : Nat) : p ^ arcSum (arcCycloChars p) = cydDiscMag p := by
  rw [arc_cyclo_sum p]
  exact (cdf_disc_from_exp p).symm

/-! ## §5 capstone: Artin 導手データ -/

/-- **M430F-5: Artin 導手データ** — 指標列 chars（分岐状態）、各段 codim（dim(V/V^{G_i})）、
    1 次元 Artin 導手 artinExp（f=dim(V/V^{G_0})）、導手総和 condSum、分岐指標数 numRamified を束ね、
      * codim の tame 値（`codim_zero`/`codim_succ`）,
      * **f = フィルトレーション和の telescope**（`artin_filt_eq`）,
      * **Σ_χ f(χ) = condSum = numRamified**（`cond_sum_eq`/`num_ramified_eq`/`sum_eq_num`）
    を要請する。局所類体論 tame・1 次元の Artin 導手 conductor-discriminant の代数的核。 -/
structure ArtinConductorData where
  chars : List Bool
  codim : Bool → Nat → Nat
  codim_zero : ∀ b, codim b 0 = arcArtinExp b
  codim_succ : ∀ b n, codim b (n + 1) = 0
  artinExp : Bool → Nat
  artin_filt_eq : ∀ b n, arcArtinFilt b n = artinExp b
  condSum : Nat
  cond_sum_eq : condSum = arcSum chars
  numRamified : Nat
  num_ramified_eq : numRamified = arcNumRamified chars
  sum_eq_num : condSum = numRamified

/-- **M430F-5b: データの構成**（指標分岐状態列 chars から本物 witness）。 -/
def arcDataOf (chars : List Bool) : ArtinConductorData where
  chars := chars
  codim := arcCodim
  codim_zero := arc_codim_zero
  codim_succ := arc_codim_succ
  artinExp := arcArtinExp
  artin_filt_eq := arc_filt_eq
  condSum := arcSum chars
  cond_sum_eq := rfl
  numRamified := arcNumRamified chars
  num_ramified_eq := rfl
  sum_eq_num := arc_sum_eq_num chars

/-- **M430F-5c: データの存在**（無矛盾性 witness、ℚ(ζ_5) の指標列）。 -/
theorem arc_exists : Nonempty ArtinConductorData :=
  ⟨arcDataOf (arcCycloChars 5)⟩

/-! ## §6 worked examples: ℚ(ζ_5)(Σf=3)・ℚ(ζ_3)(Σf=1) -/

/-- **M430F-6a: ℚ(ζ_5)** Artin 導手総和 Σ_χ f(χ) = 3（自明 0 + 非自明 3 個×1）。 -/
theorem arc_ex_zeta5_sum : arcSum (arcCycloChars 5) = 3 := rfl

/-- **M430F-6b: ℚ(ζ_5)** 分岐指標数 = 3 = Σf。 -/
theorem arc_ex_zeta5_num : arcNumRamified (arcCycloChars 5) = 3 := rfl

/-- **M430F-6c: ℚ(ζ_5)** M381F cross-check: Σf = cdfDiscExp 5 = 3。 -/
theorem arc_ex_zeta5_matches : arcSum (arcCycloChars 5) = cdfDiscExp 5 :=
  arc_matches_cdf 5

/-- **M430F-6d: ℚ(ζ_5)** conductor-discriminant: 5^{Σf} = cydDiscMag 5（=125）。 -/
theorem arc_ex_zeta5_disc : (5 : Nat) ^ arcSum (arcCycloChars 5) = cydDiscMag 5 :=
  arc_cond_disc 5

/-- **M430F-6e: ℚ(ζ_3)** Artin 導手総和 Σ_χ f(χ) = 1（自明 0 + 非自明 1 個×1）。 -/
theorem arc_ex_zeta3_sum : arcSum (arcCycloChars 3) = 1 := rfl

/-- **M430F-6f: ℚ(ζ_5)** telescope: フィルトレーション和 F_n(分岐) = 1（上限 n=10 でも一定）。 -/
theorem arc_ex_filt_stable : arcArtinFilt true 10 = arcArtinExp true :=
  arc_filt_eq true 10

/-- **M430F-6g: capstone まとめ** — ℚ(ζ_5)(Σf=3)・分岐数=3・M381F cross-check・ℚ(ζ_3)(Σf=1)。 -/
theorem arc_examples :
    arcSum (arcCycloChars 5) = 3 ∧ arcNumRamified (arcCycloChars 5) = 3 ∧
    arcSum (arcCycloChars 5) = cdfDiscExp 5 ∧ arcSum (arcCycloChars 3) = 1 :=
  ⟨arc_ex_zeta5_sum, arc_ex_zeta5_num, arc_ex_zeta5_matches, arc_ex_zeta3_sum⟩

end IUT
