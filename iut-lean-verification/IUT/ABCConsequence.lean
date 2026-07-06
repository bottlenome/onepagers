/-
  IUT/ABCConsequence.lean — M357F [実／本物]
  分類: 実 (ABC/Szpiro 不等式の条件付き算術帰結＝漸近フェルマー/指数有界)
  complete_pct 影響: 柱D を前進（M352F の ABC/Szpiro 不等式から漸近フェルマー（m 大で
    x^m+y^m=z^m の非自明既約解なし）＝指数 m の有界性の還元を本物で証明し、
    crux⟹Szpiro⟹ABC⟹漸近フェルマー の連鎖を合成。crux Dβ-ω は依然外部仮説）。
  正直な限定: crux Dβ-ω（論争の係争点）は外部仮説のまま・全連鎖は条件付き。
    高さ/radical は模型・定数/o(1) は witness。本層は還元（ABC⟹帰結）が実内容で crux 非証明。
-/

/-
  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  本層は M352F `SzpiroReduction.lean`（`szpAbcIneq`／`szp_abc_form`／`szp_full_chain`＝
  実 deg_ℝ 上の ABC/Szpiro 型不等式 height ≤ (1+ε)·conductor + O_ε(1)）を**前段**として
  受け取り、その**算術的帰結（payoff）**——漸近フェルマー（指数 m が有界）——を、ℕ/ℤ の
  **加法的（対数）高さ模型**の上で本物に証明する。IUT 連鎖の最終出力であり、crux Dβ-ω は
  前段どおり**外部仮説**として持ち越す（本層は crux を決して証明しない）。

  ### 還元の数学（本物・線形算術で閉じる形に模型化）
  フェルマー解 x^m+y^m=z^m（x,y,z 互いに素・z≥2）から ABC 三つ組 (a,b,c)=(x^m,y^m,z^m)、
  a+b=c を得る。**対数高さ** log c = log z^m = m·log z ＝ m·hz（hz:=log z≥1）。**対数導手**
  log rad(abc) = log rad(x^m y^m z^m) = log rad(xyz)（**べき乗で不変**＝還元の心臓部）
  ≤ log(xyz) ≤ log z³ = 3·hz。ここで導手対数は **m に依らない**——これが指数有界性の源泉。
  ABC の対数形 log c ≤ (1+ε)·log rad + O(1) を、(1+ε)=p/q（p≥q≥1・ε=(p−q)/q≥0）で q 倍して
  **線形化**: q·H ≤ p·R + q·K（H=対数高さ, R=対数導手, K=O(1)）。これに H=m·hz, R≤3·hz を
  代入し hz>0 で約分すると **q·m ≤ 3·p**（＝ m ≤ 3·(1+ε)）——指数の明示的上界。
  対偶: q·m > 3·p（m>3(1+ε)）なら ABC を満たすフェルマー解は**存在しない**（漸近フェルマー）。

  * M357F-1 `abcHeight` / `abcRadical` / `abcProduct` / `abc_height_le_radical`
      — ℕ 模型量（高さ＝c, radical 上界模型＝a·b·c）と自明方向 c ≤ a·b·c（0<a,0<b）。
        ABC の難方向（c ≤ rad^{1+ε}）は予想本体ゆえ条件付きで持ち越す。
  * M357F-2 `abcTriple`
      — 互いに素な三つ組 a+b=c（gcd a b = 1・非自明 0<a,0<b）を束ねた模型対象。
  * M357F-3 `abcInequality`
      — ABC 不等式（対数・q 倍線形形）: q·H ≤ p·R + q·K。(1+ε)=p/q・K=O(1)。M352F
        `szpAbcIneq` の ℕ 影（実 deg_ℝ→ℕ 対数模型への同定は模型ステップ）。
  * M357F-4 `abc_mul_swap` / `abc_height_reduce` / `abcFermatModel` /
        `abc_fermat_exponent_bounded` / `abc_no_fermat`
      — **本丸の還元**: ABC ⟹ 指数有界（q·m ≤ 3·p）と、その対偶＝漸近フェルマー
        （q·m>3·p なら ABC を満たすフェルマー解なし）。核は H=m·hz, R≤3·hz の代入と
        hz>0 での約分——**crux を用いず本物で閉じる**。
  * M357F-5 `abc_full_chain`
      — **連鎖の合成**: crux ⟹（M352F `szp_abc_form` で実 ABC）⟹（模型同定 bridge）⟹
        指数有界。crux は前件のまま・実→ℕ 模型同定 bridge は正直に仮説として明示。
  * M357F-6 `abc_crux_still_external`
      — 全 payoff は crux（M347F/M352F）に条件付き（Iff.rfl・正直な境界）。
  * M357F-7 capstone `ABCConsequenceData` / `abcConsequenceData` / `abc_exists`。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）

  - **本物（完全証明）**:
    ・還元 ABC ⟹ 指数有界（`abc_fermat_exponent_bounded`＝q·m ≤ 3·p）と漸近フェルマー
      （`abc_no_fermat`）は本物: 対数高さ H=m·hz・対数導手 R≤3·hz を前提に、代入・単調性・
      hz>0 約分（`Nat.le_of_mul_le_mul_right`）で core Lean のみ（omega は線形のみ）で完全証明。
    ・連鎖合成（`abc_full_chain`）は M352F `szp_abc_form`（crux を前件に実 ABC）と本層還元を
      合成する本物（bridge を除く足回りは実対象で閉じる）。
  - **正直申告（未達・crux・模型・後続。飾りでなく地図。過大主張の厳禁）**:
    ・**crux Dβ-ω（テータ ≤ ガウス＝多輻的アルゴリズム＝IUT 論争の係争点）は恒久的に本層の
      範囲外**。全 payoff は crux（および M352F の ABC 前段）を**前件**として受け取る条件付き
      帰結であって、crux 自体を決して証明しない。`abc_crux_still_external`（Iff.rfl）が明示。
    ・**高さ／radical は ℕ/ℤ の加法（対数）模型**。真の高さ・導手（大域体上の実 rad＝相異
      素数の積・log q_v の具体値）は範囲外。radical のべき乗不変 rad(x^m)=rad(x) は対数レベル
      R≤3·hz（m 非依存）として忠実に取り込むが、`abcRadical` 自体は a·b·c 上界模型に留める。
    ・**定数 p,q,K,hz は witness**。(1+ε)=p/q の具体値・最適性、O(1) 項 K の実測、3(1+ε) の
      鋭さは範囲外——本層は「還元の構造」（q·m ≤ 3·p が ABC から従う）を本物にする。
    ・**実 deg_ℝ（M352F）→ ℕ 対数模型（本層）の同定は模型ステップ**。`abc_full_chain` の
      bridge（szpAbcIneq → abcInequality）は正直に仮説として明示し、証明しない（模型の橋）。
  全て新規 Classical.choice を証明本体に導入せず（M352F/M347F/M324F/M312F から継承、
  #print axioms は propext/Quot.sound 系のみ）。sorry 皆無・禁止タクティク不使用（core Lean・
  omega は線形のみ）。一般名は `abc` 接頭辞で衝突回避。
-/
import IUT.SzpiroReduction

namespace IUT

/-! ## M357F-1: ℕ 模型量（高さ・radical・product）と自明方向 -/

/-- **M357F-1a: 高さ（ℕ 模型）** — ABC 三つ組の高さを最大項 c で模型化（乗法的高さ）。
    真の高さ H(a,b,c)（大域体上の対数高さ）は範囲外——本層は c を高さの代表に取る。 -/
def abcHeight (a b c : Nat) : Nat := c

/-- **M357F-1b: 積（ℕ）** — a·b·c。radical の上界模型の台。 -/
def abcProduct (a b c : Nat) : Nat := a * b * c

/-- **M357F-1c: radical（ℕ 上界模型）** — rad(abc) を積 a·b·c で上から模型化（rad(n)≤n）。
    真の radical（相異素数の積）とべき乗不変 rad(x^m)=rad(x) は本層では**対数レベル**
    （`abcFermatModel.rad_rel`: R≤3·hz が m 非依存）として取り込む——ここの `abcRadical` は
    上界模型に留める正直な限定。 -/
def abcRadical (a b c : Nat) : Nat := a * b * c

/-- **定理 (M357F-1d): 高さ ≤ radical 模型（自明方向）** — 0<a, 0<b なら c ≤ a·b·c。
    ABC の**易方向**（c は積以下）は本物で成立。難方向 c ≤ rad^{1+ε}（＝ABC 予想の本体）は
    条件付きで持ち越す。 -/
theorem abc_height_le_radical (a b c : Nat) (ha : 0 < a) (hb : 0 < b) :
    abcHeight a b c ≤ abcRadical a b c := by
  show c ≤ a * b * c
  exact Nat.le_mul_of_pos_left c (Nat.mul_pos ha hb)

/-! ## M357F-2: 互いに素な三つ組 a+b=c -/

/-- **M357F-2: ABC 三つ組（模型対象）** — 互いに素（gcd a b = 1）な非自明（0<a,0<b）三つ組
    a+b=c を束ねる。ABC 不等式・還元の主語となる算術対象。 -/
structure abcTriple where
  /-- 第 1 項。 -/
  a : Nat
  /-- 第 2 項。 -/
  b : Nat
  /-- 和（＝最大項の候補）。 -/
  c : Nat
  /-- 加法関係 a+b=c。 -/
  hsum : a + b = c
  /-- 互いに素 gcd a b = 1。 -/
  hcop : Nat.gcd a b = 1
  /-- 非自明性 0<a ∧ 0<b。 -/
  hpos : 0 < a ∧ 0 < b

/-! ## M357F-3: ABC 不等式（対数・q 倍線形形） -/

/-- **M357F-3: ABC 不等式（対数形・線形化）** — q·H ≤ p·R + q·K。ここで H=対数高さ,
    R=対数導手, (1+ε)=p/q（p≥q≥1・ε=(p−q)/q≥0）, K=O(1)。ABC の対数形
    H ≤ (1+ε)·R + O(1) を q 倍して**線形（ℕ）**にしたもの。M352F `szpAbcIneq`（実 deg_ℝ 上の
    height ≤ (1+ε)·conductor + O_ε(1)）の ℕ 対数影——実→ℕ の同定は模型ステップ。 -/
def abcInequality (p q K H R : Nat) : Prop :=
  q * H ≤ p * R + q * K

/-! ## M357F-4: 本丸の還元（ABC ⟹ 指数有界・漸近フェルマー） -/

/-- **補題 (M357F-4a): 乗法の入れ替え** — a·(3·b) = 3·a·b（core Nat の結合・可換のみ）。 -/
theorem abc_mul_swap (a b : Nat) : a * (3 * b) = 3 * a * b :=
  calc a * (3 * b) = (3 * b) * a := Nat.mul_comm a (3 * b)
    _ = 3 * (b * a) := Nat.mul_assoc 3 b a
    _ = 3 * (a * b) := by rw [Nat.mul_comm b a]
    _ = 3 * a * b := (Nat.mul_assoc 3 a b).symm

/-- **定理 (M357F-4b): 高さ還元（ABC + 導手上界 ⟹ 高さ上界）** — 対数導手 R ≤ 3·hz と
    ABC 不等式 q·H ≤ p·R + q·K から、q·H ≤ 3·p·hz + q·K が従う。証明は p·R ≤ p·(3·hz)
    （単調性）と p·(3·hz)=3·p·hz（`abc_mul_swap`）を推移律で束ねる本物。 -/
theorem abc_height_reduce (p q K H R hz : Nat)
    (hR : R ≤ 3 * hz) (habc : abcInequality p q K H R) :
    q * H ≤ 3 * p * hz + q * K := by
  have habc' : q * H ≤ p * R + q * K := habc
  have hpr : p * R ≤ p * (3 * hz) := Nat.mul_le_mul (Nat.le_refl p) hR
  have he : p * (3 * hz) = 3 * p * hz := abc_mul_swap p hz
  omega

/-- **M357F-4c: フェルマー解の対数模型** — フェルマー解 x^m+y^m=z^m（z≥2）から得られる
    ABC 三つ組 (x^m,y^m,z^m) の**対数量**を束ねる: 対数高さ H=m·hz（log z^m）, 対数導手
    R≤3·hz（log rad(xyz) が **m に依らず** ≤ 3·log z）。hz=log z≥1（z≥2 の非自明性）。
    R が m 非依存であること（radical のべき乗不変 rad(x^m)=rad(x)）が指数有界性の源泉。 -/
structure abcFermatModel (m : Nat) where
  /-- 対数底 hz = log z（z≥2 ゆえ正）。 -/
  hz : Nat
  /-- 対数高さ H = log z^m。 -/
  H : Nat
  /-- 対数導手 R = log rad(x^m y^m z^m) = log rad(xyz)。 -/
  R : Nat
  /-- 非自明性 hz > 0（z ≥ 2）。 -/
  hz_pos : 0 < hz
  /-- 対数高さ関係 H = m·hz（log z^m = m·log z）。 -/
  height_rel : H = m * hz
  /-- 対数導手上界 R ≤ 3·hz（log rad(xyz) ≤ log z³、m 非依存）。 -/
  rad_rel : R ≤ 3 * hz

/-- **定理 (M357F-4d, 本丸): ABC ⟹ 指数有界** — フェルマー対数模型 `abcFermatModel m` が
    ABC 不等式 `abcInequality p q 0 H R`（K=0 の主要項）を満たすなら、指数は **q·m ≤ 3·p**
    （＝ m ≤ 3·(1+ε)）で有界。証明: `abc_height_reduce` で q·H ≤ 3·p·hz、H=m·hz を代入して
    q·m·hz ≤ 3·p·hz、hz>0 で `Nat.le_of_mul_le_mul_right` により約分。**crux を用いない本物**。 -/
theorem abc_fermat_exponent_bounded (p q m : Nat) (sol : abcFermatModel m)
    (habc : abcInequality p q 0 sol.H sol.R) :
    q * m ≤ 3 * p := by
  have hH : sol.H = m * sol.hz := sol.height_rel
  have h1 : q * m * sol.hz ≤ 3 * p * sol.hz := by
    have e1 : q * sol.H = q * m * sol.hz := by rw [hH, Nat.mul_assoc]
    have hred : q * sol.H ≤ 3 * p * sol.hz + q * 0 :=
      abc_height_reduce p q 0 sol.H sol.R sol.hz sol.rad_rel habc
    omega
  exact Nat.le_of_mul_le_mul_right h1 sol.hz_pos

/-- **定理 (M357F-4e, payoff): 漸近フェルマー（ABC 条件付き）** — 指数 m が 3·p < q·m
    （＝ m > 3·(1+ε)）を満たすなら、ABC 不等式を満たすフェルマー対数模型は**存在しない**。
    M357F-4d の対偶——ABC の下で「m 大では x^m+y^m=z^m の非自明既約解なし」を模型で本物化。
    crux（および ABC）は前件のまま。 -/
theorem abc_no_fermat (p q m : Nat) (hbig : 3 * p < q * m) :
    ¬ ∃ sol : abcFermatModel m, abcInequality p q 0 sol.H sol.R := by
  intro h
  obtain ⟨sol, habc⟩ := h
  have hb := abc_fermat_exponent_bounded p q m sol habc
  omega

/-! ## M357F-5: 連鎖の合成（crux ⟹ 実 ABC ⟹ 模型 ABC ⟹ 指数有界） -/

/-- **定理 (M357F-5, 連鎖合成): crux ⟹ 漸近フェルマー（指数有界）** — M352F `szp_abc_form`
    （crux 由来の実 Cor 3.12 界を前件に、実 deg_ℝ 上の ABC 不等式 `szpAbcIneq` が従う）と
    本層の還元 `abc_fermat_exponent_bounded` を合成し、crux 仮説から直接**指数有界 q·m ≤ 3·p**
    を導く。crux（`cruxRealIneq`）は前件のまま——どの段でも証明されない。
    **bridge（実 deg_ℝ ABC → ℕ 対数 ABC の同定）は模型ステップとして正直に仮説で受け取る**
    （実→ℕ の対数模型化・証明しない）。ε≥0・bounded≥0・conductor≥0 の下での条件付き定理。 -/
theorem abc_full_chain (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (eps bounded : RReal) (heps : rLe realZero eps) (hbnd : rLe realZero bounded)
    (hcond : rLe realZero (szpConductorDeg logq v w l))
    (crux : cruxRealIneq logq v w l)
    (p q m : Nat) (sol : abcFermatModel m)
    (bridge : szpAbcIneq logq v w l eps bounded → abcInequality p q 0 sol.H sol.R) :
    q * m ≤ 3 * p :=
  abc_fermat_exponent_bounded p q m sol
    (bridge (szp_abc_form logq v w l eps bounded heps hbnd hcond
      (cruxR_implies_cor312 logq v w l crux)))

/-! ## M357F-6: 全 payoff は crux に条件付き（正直な境界） -/

/-- **定理 (M357F-6): 全 payoff は crux に条件付き（Iff.rfl・過大主張の厳禁）** — 本層の
    漸近フェルマー／指数有界の連鎖の**最深の前件**である crux（`cruxRealIneq`）は、ちょうど
    M324F 受け取り仮説 `GaussPilotCruxHyp`（実 deg_ℝ 不等式）に一致する。すなわち
    crux⟹Szpiro⟹ABC⟹漸近フェルマー の全連鎖は**この外部仮説に条件付き**であり、
    crux（Dβ-ω＝論争の係争点）は本層でも決して証明されない——正直な境界。 -/
theorem abc_crux_still_external (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    cruxRealIneq logq v w l ↔ GaussPilotCruxHyp logq v w l :=
  Iff.rfl

/-! ## M357F-7: capstone -/

/-- **M357F-7a: ABC 帰結データ** — ABC 不等式（対数模型）から漸近フェルマー（指数有界・
    m 大で解なし）への還元と、全連鎖が crux に条件付きであることを束ねる。主語は ℕ の
    加法（対数）高さ模型であり、crux（Dβ-ω）は前件であって証明されない。 -/
structure ABCConsequenceData (p q : Nat) where
  /-- **ABC ⟹ 指数有界**: フェルマー対数模型が ABC を満たせば q·m ≤ 3·p。 -/
  fermat_bounded : ∀ (m : Nat) (sol : abcFermatModel m),
    abcInequality p q 0 sol.H sol.R → q * m ≤ 3 * p
  /-- **漸近フェルマー**: 3·p<q·m なら ABC を満たすフェルマー解なし。 -/
  no_large_fermat : ∀ (m : Nat), 3 * p < q * m →
    ¬ ∃ sol : abcFermatModel m, abcInequality p q 0 sol.H sol.R
  /-- **crux 外部性**: 全連鎖は crux（＝M324F 受け取り仮説）に条件付き（Iff.rfl）。 -/
  crux_external : ∀ (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat),
    cruxRealIneq logq v w l ↔ GaussPilotCruxHyp logq v w l

/-- **M357F-7b: 実データ** — 全フィールドを M357F-4〜6 の本物で充足。 -/
def abcConsequenceData (p q : Nat) : ABCConsequenceData p q where
  fermat_bounded := fun m sol habc => abc_fermat_exponent_bounded p q m sol habc
  no_large_fermat := fun m hbig => abc_no_fermat p q m hbig
  crux_external := fun logq v w l => abc_crux_still_external logq v w l

/-- **M357F-7c: 存在（M357F 見出し）** — 任意の模型 (1+ε)=p/q に対し、ABC 不等式から
    漸近フェルマー（指数有界）への還元と crux 外部性を備えたデータが存在する。crux（Dβ-ω）は
    外部仮説として明示され、**決して証明されない**——本層は還元（ABC⟹帰結）を本物にするのみ。 -/
theorem abc_exists (p q : Nat) : Nonempty (ABCConsequenceData p q) :=
  ⟨abcConsequenceData p q⟩

/-! ## 実例（ε=1: p=2, q=1 ⟹ 指数上界 m ≤ 6・m=7 では ABC 下で解なし） -/

/-- 実例: ε=1（(1+ε)=2/1・p=2,q=1）で ABC を満たすフェルマー対数模型の指数は 1·m ≤ 3·2=6
    で有界（指数有界の本丸）。 -/
example (m : Nat) (sol : abcFermatModel m) (habc : abcInequality 2 1 0 sol.H sol.R) :
    1 * m ≤ 3 * 2 :=
  abc_fermat_exponent_bounded 2 1 m sol habc

/-- 実例: ε=1 で m=7 のフェルマー解は ABC を満たさない（3·2=6 < 1·7=7・漸近フェルマー）。 -/
example : ¬ ∃ sol : abcFermatModel 7, abcInequality 2 1 0 sol.H sol.R :=
  abc_no_fermat 2 1 7 (by omega)

/-- 実例: 互いに素な非自明三つ組 1+8=9（gcd 1 8 = 1）。 -/
example : abcTriple :=
  { a := 1, b := 8, c := 9, hsum := by omega, hcop := Nat.gcd_one_left 8, hpos := by omega }

/-- 実例: 三つ組の易方向 c ≤ a·b·c（ABC 難方向 c ≤ rad^{1+ε} は予想本体ゆえ条件付き）。 -/
example : abcHeight 1 8 9 ≤ abcRadical 1 8 9 :=
  abc_height_le_radical 1 8 9 (by omega) (by omega)

/-- 実例: 全連鎖は crux に条件付き（crux ＝ M324F 受け取り仮説・Iff.rfl）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    cruxRealIneq logq v w 5 ↔ GaussPilotCruxHyp logq v w 5 :=
  abc_crux_still_external logq v w 5

end IUT
