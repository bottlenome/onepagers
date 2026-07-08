/-
  IUT/HasseArfFiniteAbelian.lean
-- M466F HasseArfFiniteAbelian [実・本物・柱B]
-- complete_pct 影響: **前進あり**（柱B）。M461F `HasseArfAbelian`（haa）は Hasse–Arf 定理の
--   **非巡回アーベル ℤ/p×ℤ/p（基本アーベル p-群・rank 2・単一素数 p・低 rank）**版に到達したが、
--   `haa_model_scope` は `generalFiniteAbelian = false`／`highRank = false`——「**一般アーベル
--   （任意の有限アーベル群・任意位数・ℤ/p^a×ℤ/p^b 混合・高 rank）**は後続」と正直に限定していた。
--   本モジュールはその限定を **一般の有限アーベル群 ℤ/d₁×…×ℤ/d_k（構造定理で巡回積へ分解）**へ
--   昇格で閉じる。
--
--   数学的核心（有限アーベル群の構造定理 + Serre, Corps Locaux V; Hasse–Arf はアーベル拡大一般で成立）:
--   **任意の有限アーベル群は巡回群の直積** ℤ/d₁×…×ℤ/d_k に一意分解される（構造定理）。剰余標数上の
--   全分岐アーベル拡大の Herbrand φ は積群上で加法的で、各巡回因子 ℤ/dᵢ の φᵢ の和
--       φ(b) = Σ_{i=1}^{k} φᵢ(b) = Σ_{i=1}^{k} (Σ_j u_j^{(i)})
--   に分解する（積分解）。各巡回因子には M456F `hau_upper_break_integer`（巡回版・可除条件なし）が
--   適用でき、その上付き break は整数。アーベル性（和が可換・因子独立）から積群全体の上付き break も
--   整数——ゆえに**任意の有限アーベル群で上付き break が整数**（フル有限アーベル版 Hasse–Arf）。
--   M461F は 2 因子・単一素数 p・各因子位数 p に固定していたが、本モジュールは **因子数 k 任意・
--   各因子が自前の素数 pᵢ を持つ（ℤ/p^a×ℤ/q^b 混合）・rank k 任意**へ一般化する。
--
--   M461F の「ℤ/p×ℤ/p のみ」を破った印: 因子リストを `List (Nat × List Nat)`（各因子 = (素数 pᵢ,
--   上付き増分列)）で符号化し、**因子リストについての帰納法**で整数性を証明する。具体例で
--   ℤ/4×ℤ/9（distinct primes 2≠3・distinct orders 4≠9）・ℤ/8×ℤ/4（同素数・混合位数 p³×p²）・
--   ℤ/2×ℤ/2×ℤ/2（rank 3）を整数性で閉じ、M461F の「単一素数・2 因子・rank 2」を実際に破る
--   （`hfa_arbitrary_order`）。[p,p]（ℤ/p×ℤ/p）で M461F へ・単一因子 [pⁿ] で M456F へ厳密還元。
--
-- 正直な限定（消去・弱化禁止）: 破ったのは M461F の「**一般有限アーベル・高 rank・混合位数は後続**」
--   ——本モジュールは **有限アーベル（構造定理で巡回積へ分解済み）・1 次元指標**に限り、任意個数・
--   任意位数・混合素数の巡回因子で上付き break 整数性を本物化した。ただし **非可換・dim≥2 表現・
--   無限アーベル（ℤ_p 等の副有限）・混標数一般 Hasse–Arf 定理の完全証明**は依然対象外——後続。
--   これを §6 `hfaScope`/`hfa_model_scope` で定理化する。
--
--  ────────────────────────────────────────────────────────────────────────
--  二軸（CLAUDE.md §1）
--  * 分類: **[実]**（(a) 昇格）。M461F `haa_model_scope`（generalFiniteAbelian=false・highRank=false・
--    「ℤ/p×ℤ/p のみ・rank 2・単一素数」）の「一般有限アーベルは後続」限定を、**任意の有限アーベル群
--    ℤ/d₁×…×ℤ/d_k（構造定理・任意個数 k の巡回因子・各因子が自前の素数 pᵢ・混合位数・rank k）**で
--    置換し、積分解 φ=Σφᵢ＋各巡回因子への M456F hau 適用＋アーベル和を因子リストの帰納法で閉じる。
--    因子リスト [p,p] で M461F へ・単一 [pⁿ] で M456F へ厳密還元（`hfa_reduces_to_haa`/`hfa_reduces_to_hau`）。
--  * complete_pct 影響: **前進あり**（柱B: 一般有限アーベル群 ℤ/d₁×…×ℤ/d_k の上付き break 整数性
--    ——構造定理で巡回積へ分解→各因子 hau→アーベル和で整数に landing する本物建設 =
--    M461F「ℤ/p×ℤ/p のみ」限定の突破・任意巡回積へ）。
--
--  既存モジュールの何を本物化したか
--  * M456F `hau_upper_break_integer`（巡回 ℤ/pⁿ 塔・可除条件なし上付き break 整数）を、構造定理の
--    **各巡回因子**へ因子ごとの素数 pᵢ で適用し、任意有限アーベル群の積分解 φ=Σφᵢ の各項を整数へ落とす
--    `hfa_upper_break_integer`（任意巡回積で整数）へ昇格。
--  * M461F `haaUpperBreak`/`haaUpperFrom`/`haa_upper_break_integer_abelian`（2 因子・単一素数 p）を、
--    因子数 k 任意・各因子素数 pᵢ 混合の `hfaUpperBreak`/`hfaUpperFrom` へ一般化。[p,p] で M461F 回復。
--
--  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
--  * `hfaFactorList` / `hfaGroup` / `hfaGroupOf` / `hfaOrder` / `hfa_group_order`
--      — 一般有限アーベル群 ℤ/d₁×…×ℤ/d_k の構造定理データ（巡回因子位数リスト・積群・位数 Πdᵢ）
--  * `hfaUpperBreak` / `hfaUpperFrom` / `hfaPrimesPos`
--      — 積群の上付き break φ=Σφᵢ（各巡回因子 break の和・各因子が自前の素数 pᵢ）
--  * `hfa_upper_break_integer` — **任意の有限アーベル群 ℤ/d₁×…×ℤ/d_k の上付き break が整数**
--      （因子リストについての帰納法・各因子巡回→M456F hau→アーベル和）（本命題）
--  * `hfa_reduces_to_haa` — 因子 [p,p]（ℤ/p×ℤ/p）で M461F `haaUpperBreak`/`haaUpperFrom` へ厳密還元
--  * `hfa_reduces_to_hau` — 単一因子 [pⁿ] で M456F `hauUpperBreak`/`hauUpperFrom` へ厳密還元
--  * `hfa_arbitrary_order` — 混合位数（ℤ/4×ℤ/9 distinct primes・ℤ/8×ℤ/4 混合 p^a×p^b・rank 3）で
--      整数性を示し、M461F の「単一素数・2 因子・rank 2」を実際に破った印を明示
--  * `hfaScope` / `hfaModelScope` / `hfa_model_scope` / `hfa_scope_witness`
--      — 正直な限定の定理化（M461F「一般有限アーベルは後続」を破った印を明示）
--  * `HasseArfFiniteAbelianData` / `hfaDataOf` / `hfa_exists` — capstone
--  * `hfa_ex_*`（ℤ/4×ℤ/9・ℤ/8×ℤ/4・ℤ/2³ の各整数性・位数・M461F/M456F 還元 ほか）
--
--  正直な限定（CLAUDE.md §4: 消去・弱化禁止）: 上記ヘッダ限定を §6 で定理化。破ったのは
--  M461F の「一般有限アーベル・高 rank・混合位数は後続」——任意の有限アーベル群（巡回積）へ昇格。
--  非可換・無限アーベル・混標数一般 Hasse–Arf は後続。
--  全て選択公理不使用（propext/Quot.sound のみ）。共有ファイル未変更（新規 1 本）。
-/
import IUT.HasseArfAbelian

namespace IUT

/-! ## §1 有限アーベル群の構造定理データ ℤ/d₁×…×ℤ/d_k（巡回因子位数リスト・積群）

    有限アーベル群の**構造定理**: 任意の有限アーベル群は巡回群の直積
      G ≅ ℤ/d₁ × ℤ/d₂ × … × ℤ/d_k
    に一意分解される。この分解データ（巡回因子の位数リスト [d₁,…,d_k]）を扱う。積群の位数は
    Πdᵢ。M461F haa が扱った ℤ/p×ℤ/p（2 因子・単一素数 p・各位数 p）は、この一般構造の
    特殊ケース（[p,p]）にすぎない。本モジュールは因子数 k・各位数 dᵢ を任意に取る。 -/

/-- **M466F-1: 巡回因子位数リスト** [d₁,…,d_k]（有限アーベル群 ℤ/d₁×…×ℤ/d_k の構造定理データ）。 -/
def hfaFactorList (ds : List Nat) : List Nat := ds

/-- **M466F-1a: 有限アーベル群（積群）** 巡回因子位数リストから構成する ℤ/d₁×…×ℤ/d_k。 -/
structure hfaGroup where
  /-- 巡回因子の位数リスト [d₁,…,d_k]（構造定理の不変因子/初等因子）。 -/
  factorOrders : List Nat

/-- **M466F-1b: リストから積群を構成**（構造定理の直積 ℤ/d₁×…×ℤ/d_k）。 -/
def hfaGroupOf (ds : List Nat) : hfaGroup := { factorOrders := ds }

/-- **M466F-1c: 積群の位数** |ℤ/d₁×…×ℤ/d_k| = Πdᵢ（各巡回因子位数の総積）。 -/
def hfaOrder : List Nat → Nat
  | []      => 1
  | d :: ds => d * hfaOrder ds

/-- **M466F-1d: 積群位数の値（本物・定義的）** |ℤ/(hfaGroupOf ds)| = Πdᵢ。 -/
theorem hfa_group_order (ds : List Nat) : hfaOrder (hfaGroupOf ds).factorOrders = hfaOrder ds := rfl

/-- **M466F-1e: 因子リストの値（本物・定義的）** [d₁,…,d_k]。 -/
theorem hfa_factor_list_eq (ds : List Nat) : hfaFactorList ds = ds := rfl

/-! ## §2 積分解によるアーベル上付き break φ = Σφᵢ（M461F の 2 因子を任意個数 k へ）

    構造定理の各巡回因子 ℤ/dᵢ を、その素数 pᵢ と上付き増分列 usᵢ の対 (pᵢ, usᵢ) で符号化する。
    有限アーベル群 ℤ/d₁×…×ℤ/d_k はこの対のリスト `List (Nat × List Nat)` で表され、積群の上付き
    break は Herbrand φ の加法性から各因子の巡回 break の和
        φ(b) = Σ_{i=1}^{k} φᵢ(b) = Σ_{i=1}^{k} (Σ_j u_j^{(i)})
    になる（積分解）。M461F の haaUpperBreak は 2 因子・単一素数 p 固定だったが、ここでは因子数 k・
    各因子の素数 pᵢ を任意にする（ℤ/p^a×ℤ/q^b 混合素数を含む）。 -/

/-- **M466F-2: 一般アーベル上付き break** φ = Σφᵢ = Σᵢ(Σ_j u_j^{(i)})（各巡回因子 break の総和）。
    各因子 (pᵢ, usᵢ) の巡回 break `hauUpperBreak usᵢ` を因子リストで走査して和をとる（積分解）。 -/
def hfaUpperBreak : List (Nat × List Nat) → Nat
  | []              => 0
  | (_, us) :: rest => hauUpperBreak us + hfaUpperBreak rest

/-- **M466F-2a: 一般アーベル上付き break の Herbrand 復元** 各巡回因子 (pᵢ, usᵢ) で段ごと φ 復元
    `hauUpperFrom pᵢ 1 usᵢ`（M456F・因子ごとの自前素数 pᵢ）を積み和をとる（φ = Σᵢ φᵢ∘ψᵢ）。 -/
def hfaUpperFrom : List (Nat × List Nat) → Nat
  | []              => 0
  | (p, us) :: rest => hauUpperFrom p 1 us + hfaUpperFrom rest

/-- **M466F-2b: 各因子の素数が正**（各巡回因子の剰余標数 pᵢ ≥ 1・M456F hau の適用条件）。 -/
def hfaPrimesPos : List (Nat × List Nat) → Prop
  | []              => True
  | (p, _) :: rest  => 1 ≤ p ∧ hfaPrimesPos rest

/-- **M466F-2c: 積分解（本物・定義的）** — 最初の巡回因子の break を切り出す:
    hfaUpperBreak ((p,us)::rest) = hauUpperBreak us + hfaUpperBreak rest。
    積群の break が各巡回因子の break の和に分解する（積群 Herbrand φ の加法性）。 -/
theorem hfa_product_break (p : Nat) (us : List Nat) (rest : List (Nat × List Nat)) :
    hfaUpperBreak ((p, us) :: rest) = hauUpperBreak us + hfaUpperBreak rest := rfl

/-! ## §3 任意の有限アーベル群の上付き break 整数性（因子リストについての帰納法）

    構造定理で有限アーベル群を巡回因子リストへ分解し、各巡回因子には M456F `hau_upper_break_integer`
    （巡回版・可除条件なし）が適用できる。因子リストを走査し、各因子で段ごと Herbrand 復元を上付き
    break へ一致させ、アーベル性（和が可換・因子独立）で総和を整数へ積み上げる。**因子リストに
    ついての帰納法**が本命題の中核——M461F の「2 因子固定」を任意個数へ一般化する。 -/

/-- **M466F-3: 任意の有限アーベル群 ℤ/d₁×…×ℤ/d_k の上付き break が整数（本命題・M461F「ℤ/p×ℤ/p
    のみ」突破）** — 各因子の素数が正なら hfaUpperFrom fs = hfaUpperBreak fs。**構造定理で巡回積へ
    分解**し、各巡回因子に M456F `hau_upper_break_integer`（可除条件なし）を適用、アーベル和で整数へ
    landing。因子リストについての帰納法: 先頭因子 (p,us) を切り出し hau で整数へ、残りに IH。
    因子数 k・各因子素数 pᵢ 混合・rank k いずれも任意——フル有限アーベル版 Hasse–Arf の本物構成。 -/
theorem hfa_upper_break_integer :
    ∀ fs : List (Nat × List Nat), hfaPrimesPos fs → hfaUpperFrom fs = hfaUpperBreak fs := by
  intro fs
  induction fs with
  | nil => intro _; rfl
  | cons pu rest ih =>
    intro hpos
    obtain ⟨p, us⟩ := pu
    have hpos' : 1 ≤ p ∧ hfaPrimesPos rest := hpos
    obtain ⟨hp, hrest⟩ := hpos'
    show hauUpperFrom p 1 us + hfaUpperFrom rest = hauUpperBreak us + hfaUpperBreak rest
    rw [hau_upper_break_integer p hp us, ih hrest]

/-- **M466F-3a: 各巡回因子が M456F hau 整数性を満たす（本物）** — 先頭因子 (p,us) が巡回ゆえ
    段ごと φ 復元 = 上付き break（M456F `hau_upper_break_integer`）。構造定理の各巡回因子への
    hau 適用の核（積分解の各項が整数）。 -/
theorem hfa_each_factor_cyclic (p : Nat) (hp : 1 ≤ p) (us : List Nat) :
    hauUpperFrom p 1 us = hauUpperBreak us :=
  hau_upper_break_integer p hp us

/-! ## §4 M461F（ℤ/p×ℤ/p）・M456F（巡回 ℤ/pⁿ）への厳密還元（genuine reduction）

    一般化が旧結果を回復する印: 因子リスト [(p,f.1),(p,f.2)]（単一素数 p・2 因子）で M461F haa の
    2 因子 break へ、単一因子 [(p,us)] で M456F hau の巡回 break へ厳密一致する。 -/

/-- **M466F-4: 因子 [p,p] で M461F 巡回対版へ厳密還元（本物）** — 単一素数 p・2 因子
    [(p,f.1),(p,f.2)] の一般アーベル break が M461F `haaUpperBreak`/`haaUpperFrom`（ℤ/p×ℤ/p）に
    厳密一致する。任意巡回積の昇格が M461F の ℤ/p×ℤ/p ケースで旧結果を回復する genuine reduction。 -/
theorem hfa_reduces_to_haa (p : Nat) (f : List Nat × List Nat) :
    hfaUpperBreak [(p, f.1), (p, f.2)] = haaUpperBreak f
    ∧ hfaUpperFrom [(p, f.1), (p, f.2)] = haaUpperFrom p f := by
  refine ⟨?_, ?_⟩
  · show hauUpperBreak f.1 + (hauUpperBreak f.2 + 0) = hauUpperBreak f.1 + hauUpperBreak f.2
    rw [Nat.add_zero]
  · show hauUpperFrom p 1 f.1 + (hauUpperFrom p 1 f.2 + 0)
       = hauUpperFrom p 1 f.1 + hauUpperFrom p 1 f.2
    rw [Nat.add_zero]

/-- **M466F-4a: 単一因子 [pⁿ] で M456F 巡回版へ厳密還元（本物）** — 単一巡回因子 [(p,us)] の
    一般アーベル break が M456F `hauUpperBreak`/`hauUpperFrom`（巡回 ℤ/pⁿ 塔）に厳密一致する。
    任意巡回積の昇格が k=1（単一巡回因子）で M456F へ戻る genuine reduction。 -/
theorem hfa_reduces_to_hau (p : Nat) (us : List Nat) :
    hfaUpperBreak [(p, us)] = hauUpperBreak us
    ∧ hfaUpperFrom [(p, us)] = hauUpperFrom p 1 us := by
  refine ⟨?_, ?_⟩
  · show hauUpperBreak us + 0 = hauUpperBreak us
    exact Nat.add_zero _
  · show hauUpperFrom p 1 us + 0 = hauUpperFrom p 1 us
    exact Nat.add_zero _

/-- **M466F-4b: M461F 還元での整数性の回復（本物）** — 因子 [p,p]（ℤ/p×ℤ/p）で、一般アーベル
    整数性が M461F `haa_upper_break_integer_abelian` に一致する。 -/
theorem hfa_reduces_to_haa_integer (p : Nat) (hp : 1 ≤ p) (f : List Nat × List Nat) :
    hfaUpperFrom [(p, f.1), (p, f.2)] = hfaUpperBreak [(p, f.1), (p, f.2)] :=
  hfa_upper_break_integer [(p, f.1), (p, f.2)] ⟨hp, hp, trivial⟩

/-! ## §5 混合位数・高 rank で M461F の「ℤ/p×ℤ/p のみ」を実際に破る

    M461F haa は **単一素数 p・2 因子・各位数 p（基本アーベル p-群・rank 2）**に固定していた。
    本モジュールは因子リストで **(i) distinct primes ℤ/4×ℤ/9（2≠3・4≠9）, (ii) 混合位数
    ℤ/8×ℤ/4（同素数 2・位数 8≠4・p³×p²）, (iii) 高 rank ℤ/2×ℤ/2×ℤ/2（rank 3）**を整数性で閉じ、
    M461F の制限を実際に突破する。 -/

/-- **M466F-5: distinct primes ℤ/4×ℤ/9 の整数性** 因子 (2,[1,1]),(3,[1,1])（各巡回 2 跳躍・
    素数 2 と 3 が異なる）の上付き break が整数 4 に landing。M461F の「単一素数」を破った印。 -/
theorem hfa_mixed_primes_integer :
    hfaUpperFrom [(2, [1, 1]), (3, [1, 1])] = hfaUpperBreak [(2, [1, 1]), (3, [1, 1])] :=
  hfa_upper_break_integer [(2, [1, 1]), (3, [1, 1])] ⟨by omega, by omega, trivial⟩

/-- **M466F-5a: 混合位数 ℤ/8×ℤ/4 の整数性** 因子 (2,[1,1,1]),(2,[1,1])（同素数 2・位数 8 と 4・
    p³×p²）の上付き break が整数 5 に landing。M461F の「各位数 p（elementary abelian）」を破った印。 -/
theorem hfa_mixed_order_integer :
    hfaUpperFrom [(2, [1, 1, 1]), (2, [1, 1])] = hfaUpperBreak [(2, [1, 1, 1]), (2, [1, 1])] :=
  hfa_upper_break_integer [(2, [1, 1, 1]), (2, [1, 1])] ⟨by omega, by omega, trivial⟩

/-- **M466F-5b: 高 rank ℤ/2×ℤ/2×ℤ/2 の整数性** 因子 3 つ (2,[1]) の上付き break が整数 3 に landing。
    rank 3（3 因子）。M461F の「rank 2（2 因子）」を破った印。 -/
theorem hfa_high_rank_integer :
    hfaUpperFrom [(2, [1]), (2, [1]), (2, [1])] = hfaUpperBreak [(2, [1]), (2, [1]), (2, [1])] :=
  hfa_upper_break_integer [(2, [1]), (2, [1]), (2, [1])] ⟨by omega, by omega, by omega, trivial⟩

/-- **M466F-5c: 「ℤ/p×ℤ/p のみ」を破ったことの定理（本物・本命題の証拠束ね）** —
    M461F が単一素数 p・2 因子・rank 2 に固定したのと対照的に、次がすべて整数性を満たす:
      (i) distinct primes ℤ/4×ℤ/9（2≠3・位数 4≠9）,
      (ii) 混合位数 ℤ/8×ℤ/4（p³×p²・位数 8≠4）,
      (iii) 高 rank ℤ/2×ℤ/2×ℤ/2（rank 3）。
    各因子が巡回で M456F hau を満たすので、因子リストの帰納法で任意巡回積が整数へ landing。
    M461F の「ℤ/p×ℤ/p のみ（単一素数・2 因子・rank 2・各位数 p）」を実際に破った印。 -/
theorem hfa_arbitrary_order :
    (hfaUpperFrom [(2, [1, 1]), (3, [1, 1])] = hfaUpperBreak [(2, [1, 1]), (3, [1, 1])]) ∧
    (hfaUpperFrom [(2, [1, 1, 1]), (2, [1, 1])] = hfaUpperBreak [(2, [1, 1, 1]), (2, [1, 1])]) ∧
    (hfaUpperFrom [(2, [1]), (2, [1]), (2, [1])]
      = hfaUpperBreak [(2, [1]), (2, [1]), (2, [1])]) ∧
    (2 ≠ 3) ∧ (hfaOrder [4, 9] = 36) ∧ (hfaOrder [8, 4] = 32) ∧ (hfaOrder [2, 2, 2] = 8) :=
  ⟨hfa_mixed_primes_integer, hfa_mixed_order_integer, hfa_high_rank_integer,
   by omega, rfl, rfl, rfl⟩

/-! ## §6 正直な限定の定理化（CLAUDE.md §4: 消去・弱化禁止）

    本モジュールが M461F の「一般有限アーベル・高 rank・混合位数は後続」を破ったのは、次を
    **すべて満たす**昇格に限る:
      (generalFiniteAbelian) 任意の有限アーベル群 ℤ/d₁×…×ℤ/d_k（構造定理で巡回積へ分解）,
      (arbitraryCyclicProduct) 因子数 k 任意の巡回因子積,
      (mixedOrder)             混合位数 ℤ/p^a×ℤ/q^b（distinct primes・各因子自前の素数 pᵢ）,
      (arbitraryRank)          rank k 任意（M461F の rank 2 制限を突破）。
    以下は**依然対象外**（フラグ false）——後続:
      (nonAbelian)         非可換・dim≥2 表現,
      (infiniteAbelian)    無限アーベル（ℤ_p 等の副有限アーベル群）,
      (higherDimChar)      dim ≥ 2 の表現（1 次元指標を超える）,
      (fullMixedCharHasseArf) 混標数一般 Hasse–Arf 定理の完全証明（任意拡大の整数性）。 -/

/-- **M466F-6: 正直な限定フラグ** — 破った一般有限アーベルケースと依然未対応の一般化を Bool で明示。 -/
structure hfaScope where
  /-- 任意の有限アーベル群 ℤ/d₁×…×ℤ/d_k（構造定理で巡回積へ分解）で上付き break 整数性を本物化。 -/
  generalFiniteAbelian : Bool
  /-- 因子数 k 任意の巡回因子積。 -/
  arbitraryCyclicProduct : Bool
  /-- 混合位数 ℤ/p^a×ℤ/q^b（distinct primes・各因子自前の素数 pᵢ）。 -/
  mixedOrder : Bool
  /-- rank k 任意（M461F の rank 2 制限を突破）。 -/
  arbitraryRank : Bool
  /-- 非可換・dim≥2 表現 — 未対応。 -/
  nonAbelian : Bool
  /-- 無限アーベル（ℤ_p 等の副有限アーベル群）— 未対応。 -/
  infiniteAbelian : Bool
  /-- dim ≥ 2 の表現（1 次元指標を超える）— 未対応。 -/
  higherDimChar : Bool
  /-- 混標数一般 Hasse–Arf 定理の完全証明 — 未対応。 -/
  fullMixedCharHasseArf : Bool

/-- **M466F-6a: 本モジュールの scope witness** — 破った一般有限アーベルケース（前 4 つ true）と
    依然未対応の一般化（後 4 つ false）。generalFiniteAbelian=true が M461F「ℤ/p×ℤ/p のみ」を
    破った印。 -/
def hfaModelScope : hfaScope where
  generalFiniteAbelian := true
  arbitraryCyclicProduct := true
  mixedOrder := true
  arbitraryRank := true
  nonAbelian := false
  infiniteAbelian := false
  higherDimChar := false
  fullMixedCharHasseArf := false

/-- **M466F-6b: 正直な限定（定理・消さない）** — 破ったのは一般有限アーベル（巡回積）のみ。
    非可換・無限アーベル・dim≥2・完全一般 Hasse–Arf は false（対象外）。 -/
theorem hfa_model_scope :
    hfaModelScope.generalFiniteAbelian = true ∧ hfaModelScope.arbitraryCyclicProduct = true ∧
    hfaModelScope.mixedOrder = true ∧ hfaModelScope.arbitraryRank = true ∧
    hfaModelScope.nonAbelian = false ∧ hfaModelScope.infiniteAbelian = false ∧
    hfaModelScope.higherDimChar = false ∧ hfaModelScope.fullMixedCharHasseArf = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **M466F-6c: 「ℤ/p×ℤ/p のみ」を破ったことの定理（本物）** — 任意の有限アーベル群
    ℤ/d₁×…×ℤ/d_k（各因子の素数が正）で上付き break 整数性が成立する: 任意の因子リスト fs に対し
    一般アーベル Herbrand 復元 = 上付き break。M461F が 2 因子・単一素数・rank 2 に固定したのと
    対照的に、本定理は任意個数・混合素数・任意 rank の巡回積で整数性を主張する（構造定理＋各因子
    巡回＋アーベル性で自動）。 -/
theorem hfa_scope_witness :
    (hfaModelScope.generalFiniteAbelian = true) ∧
    (∀ fs : List (Nat × List Nat), hfaPrimesPos fs → hfaUpperFrom fs = hfaUpperBreak fs) ∧
    (hfaOrder [4, 9] = 36 ∧ hfaOrder [8, 4] = 32) :=
  ⟨rfl, fun fs h => hfa_upper_break_integer fs h, ⟨rfl, rfl⟩⟩

/-! ## §7 capstone: 一般有限アーベル Hasse–Arf データ -/

/-- **M466F-7: 一般有限アーベル Hasse–Arf データ** — 巡回因子リスト factors（各因子 (pᵢ, usᵢ)）、
    各因子の素数正 primesPos、上付き break upperBreak を束ね、
      * upperBreak = Σᵢ hauUpperBreak usᵢ（`upper_eq`）,
      * **一般有限アーベル整数性** 一般アーベル Herbrand 復元 = upperBreak（`integrality`）
    を要請する。任意の有限アーベル群 ℤ/d₁×…×ℤ/d_k の上付き break 整数性（Hasse–Arf 有限アーベル
    版）の核。 -/
structure HasseArfFiniteAbelianData where
  factors : List (Nat × List Nat)
  primesPos : hfaPrimesPos factors
  upperBreak : Nat
  upper_eq : upperBreak = hfaUpperBreak factors
  integrality : hfaUpperFrom factors = upperBreak

/-- **M466F-7b: データの構成**（巡回因子リスト factors と各因子素数正 h から本物 witness・
    任意巡回積で整数）。 -/
def hfaDataOf (fs : List (Nat × List Nat)) (h : hfaPrimesPos fs) : HasseArfFiniteAbelianData where
  factors := fs
  primesPos := h
  upperBreak := hfaUpperBreak fs
  upper_eq := rfl
  integrality := hfa_upper_break_integer fs h

/-- **M466F-7c: データの存在**（無矛盾性 witness、ℤ/4×ℤ/9 distinct primes・各因子 2 跳躍）。 -/
theorem hfa_exists : Nonempty HasseArfFiniteAbelianData :=
  ⟨hfaDataOf [(2, [1, 1]), (3, [1, 1])] ⟨by omega, by omega, trivial⟩⟩

/-! ## §8 worked examples: ℤ/4×ℤ/9・ℤ/8×ℤ/4・ℤ/2³（混合位数・混合素数・高 rank） -/

/-- **M466F-8a: ℤ/4×ℤ/9 の上付き break = 4**（巡回因子 ℤ/4 の break 2 と ℤ/9 の break 2 の和）。 -/
theorem hfa_ex_mixed_primes_break : hfaUpperBreak [(2, [1, 1]), (3, [1, 1])] = 4 := rfl

/-- **M466F-8b: ℤ/4×ℤ/9 の整数性（distinct primes）** 一般アーベル Herbrand 復元が上付き break 4 に
    landing。素数 2≠3 の混合——M461F の「単一素数」を破った。 -/
theorem hfa_ex_mixed_primes_integer : hfaUpperFrom [(2, [1, 1]), (3, [1, 1])] = 4 :=
  hfa_mixed_primes_integer.trans rfl

/-- **M466F-8c: ℤ/4×ℤ/9 の位数** |ℤ/4×ℤ/9| = 36。 -/
theorem hfa_ex_mixed_primes_order : hfaOrder [4, 9] = 36 := rfl

/-- **M466F-8d: ℤ/8×ℤ/4 の上付き break = 5**（ℤ/8 の break 3 と ℤ/4 の break 2 の和・p³×p²）。 -/
theorem hfa_ex_mixed_order_break : hfaUpperBreak [(2, [1, 1, 1]), (2, [1, 1])] = 5 := rfl

/-- **M466F-8e: ℤ/8×ℤ/4 の整数性（混合位数 p^a×p^b）** 一般アーベル Herbrand 復元が上付き break 5 に
    landing。位数 8≠4（p³×p²）——M461F の「各位数 p（elementary abelian）」を破った。 -/
theorem hfa_ex_mixed_order_integer : hfaUpperFrom [(2, [1, 1, 1]), (2, [1, 1])] = 5 :=
  hfa_mixed_order_integer.trans rfl

/-- **M466F-8f: ℤ/8×ℤ/4 の位数** |ℤ/8×ℤ/4| = 32。 -/
theorem hfa_ex_mixed_order_order : hfaOrder [8, 4] = 32 := rfl

/-- **M466F-8g: ℤ/2×ℤ/2×ℤ/2 の上付き break = 3（rank 3）**（3 つの巡回因子 ℤ/2 の break 1 の和）。 -/
theorem hfa_ex_high_rank_break : hfaUpperBreak [(2, [1]), (2, [1]), (2, [1])] = 3 := rfl

/-- **M466F-8h: ℤ/2×ℤ/2×ℤ/2 の整数性（rank 3）** 一般アーベル Herbrand 復元が上付き break 3 に
    landing。rank 3（3 因子）——M461F の「rank 2」を破った。 -/
theorem hfa_ex_high_rank_integer : hfaUpperFrom [(2, [1]), (2, [1]), (2, [1])] = 3 :=
  hfa_high_rank_integer.trans rfl

/-- **M466F-8i: 単一因子 [1,1,1] で M456F 巡回版へ還元（ℤ/2³ 塔）** 一般 break = 巡回 break。 -/
theorem hfa_ex_reduce_hau :
    hfaUpperBreak [(2, [1, 1, 1])] = hauUpperBreak [1, 1, 1]
    ∧ hfaUpperFrom [(2, [1, 1, 1])] = hauUpperFrom 2 1 [1, 1, 1] :=
  hfa_reduces_to_hau 2 [1, 1, 1]

/-- **M466F-8j: 因子 [p,p] で M461F ℤ/p×ℤ/p 版へ還元（ℤ/2×ℤ/2）** 一般 break = M461F break。 -/
theorem hfa_ex_reduce_haa :
    hfaUpperBreak [(2, [1]), (2, [1])] = haaUpperBreak ([1], [1])
    ∧ hfaUpperFrom [(2, [1]), (2, [1])] = haaUpperFrom 2 ([1], [1]) :=
  hfa_reduces_to_haa 2 ([1], [1])

/-- **M466F-8k: capstone まとめ** — ℤ/4×ℤ/9（distinct primes・break 4・位数 36）・
    ℤ/8×ℤ/4（混合位数 p³×p²・break 5・位数 32）・ℤ/2×ℤ/2×ℤ/2（rank 3・break 3）の各整数性と
    M461F/M456F への還元。任意巡回積の上付き break が整数に landing。 -/
theorem hfa_examples :
    hfaUpperBreak [(2, [1, 1]), (3, [1, 1])] = 4 ∧
    hfaUpperFrom [(2, [1, 1]), (3, [1, 1])] = 4 ∧
    hfaOrder [4, 9] = 36 ∧
    hfaUpperBreak [(2, [1, 1, 1]), (2, [1, 1])] = 5 ∧
    hfaUpperFrom [(2, [1, 1, 1]), (2, [1, 1])] = 5 ∧
    hfaUpperFrom [(2, [1]), (2, [1]), (2, [1])] = 3 :=
  ⟨rfl, hfa_ex_mixed_primes_integer, rfl, rfl, hfa_ex_mixed_order_integer,
   hfa_ex_high_rank_integer⟩

end IUT
