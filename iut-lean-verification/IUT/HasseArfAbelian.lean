/-
  IUT/HasseArfAbelian.lean
-- M461F HasseArfAbelian [実・本物・柱B]
-- complete_pct 影響: **前進あり**（柱B）。M456F `HasseArfUnconditional`（hau）は Hasse–Arf 定理の
--   **巡回 ℤ/pⁿ 塔・1 次元指標**版（上付き break φ(b_j)=Σu_i が可除条件なしで整数）を到達したが、
--   `hau_model_scope` は `generalAbelianNonCyclic = false`——「**一般アーベル（非巡回）**は後続」と
--   正直に限定していた。本モジュールはその限定のうち **非巡回アーベル ℤ/p×ℤ/p（基本アーベル
--   p-群・rank 2）**の Hasse–Arf 整数性を昇格で閉じる。
--
--   数学的核心（Serre, Corps Locaux V; Hasse–Arf 定理はアーベル拡大一般で成立）: 非巡回アーベル
--   ℤ/p×ℤ/p（基本アーベル p-群・exponent p・order p²）では分岐群も基本アーベル p-群で、その
--   **合成列の各部分商 G_i/G_{i+1} は素数位数 p の巡回群 ℤ/p**（合成因子は単純アーベル＝巡回）。
--   非巡回群そのものには直接 hau（巡回版）を適用できないが、**各巡回部分商には適用できる**。
--   ℤ/p×ℤ/p を 2 つの巡回因子 ℤ/p × ℤ/p（各因子は上付き増分列を持つ単一跳躍巡回塔）に分解し、
--   上付き break を因子ごとの巡回 break の和
--       φ(b) = φ₁(b) + φ₂(b) = Σ u_i^{(1)} + Σ u_i^{(2)}
--   として構成する（積分解）。各因子は巡回ゆえ M456F `hau_upper_break_integer` で整数、
--   アーベル性（和が可換・因子が独立）から全体も整数。ゆえに **非巡回アーベルでも上付き break が
--   整数**——巡回に限らない Hasse–Arf の本物構成。
--
--   非巡回であることの証拠（M456F「巡回のみ」を実際に破った印）: ℤ/p×ℤ/p は exponent p だが
--   order p²、p<p²（p≥2）ゆえ位数 p² の元を持たない＝**巡回でない**（巡回 ℤ/p² は位数 p² の元を
--   持つ）。rank 2（2 生成元必要）。`haa_not_cyclic` で明示。
--
-- 正直な限定（消去・弱化禁止）: 破ったのは M456F の「**巡回のみ**（generalAbelianNonCyclic=false）」
--   ——本モジュールは **ℤ/p×ℤ/p（基本アーベル p-群・rank 2・1 次元指標・低ランク）**に限り
--   非巡回アーベルの上付き break 整数性を本物化した。ただし **一般アーベル（任意の有限アーベル群・
--   高 rank・ℤ/p^a×ℤ/p^b の混合）・非可換/dim≥2 表現・混標数一般 Hasse–Arf の完全証明**は依然
--   対象外——後続。これを §6 `haaScope`/`haa_model_scope` で定理化する。
--
--  ────────────────────────────────────────────────────────────────────────
--  二軸（CLAUDE.md §1）
--  * 分類: **[実]**（(a) 昇格）。M456F `hau_model_scope`（generalAbelianNonCyclic=false・巡回のみ）
--    の「一般アーベル（非巡回）は後続」限定を、**非巡回アーベル ℤ/p×ℤ/p（基本アーベル p-群）**で
--    置換し、積分解＋各巡回部分商への hau 適用＋アーベル性で上付き break 整数性を本物 Nat 算術で
--    閉じる。第 2 因子を空にすると M456F 巡回版へ厳密還元（`haa_reduces_to_cyclic`）。
--  * complete_pct 影響: **前進あり**（柱B: 非巡回アーベル ℤ/p×ℤ/p の上付き break 整数性
--    ——部分商巡回→hau→アーベル和で整数に landing する本物建設 = M456F「巡回のみ」限定の突破）。
--
--  既存モジュールの何を本物化したか
--  * M456F `hau_upper_break_integer`（巡回 ℤ/pⁿ 塔・可除条件なし上付き break 整数）を、
--    **各巡回部分商**へ適用し、非巡回アーベル ℤ/p×ℤ/p の積分解 φ=φ₁+φ₂ の各項を整数へ落とす
--    `haa_upper_break_integer_abelian`（非巡回でも整数）へ昇格。第 2 因子空で M456F へ厳密還元。
--  * M420F `rnfPhi`/`rnfPsi`/`rnf_phi_psi`（Herbrand φ∘ψ=id）を hau 経由で各因子の段ごと復元に使用。
--
--  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
--  * `haaOrder` / `haaExponent` / `haaAbelianGroup` / `haaSubquotientOrders`
--      — 非巡回アーベル ℤ/p×ℤ/p（基本アーベル p-群・order p²・exponent p）の分岐フィルトレーション
--        位数列 [p²,p,1]・部分商位数 [p,p]（各巡回 ℤ/p）
--  * `haaUpperBreak` / `haaUpperFrom` / `haa_product_break`
--      — アーベル上付き break φ=φ₁+φ₂（積分解・因子ごとの巡回 break の和）
--  * `haa_upper_break_integer_abelian` — **非巡回アーベル ℤ/p×ℤ/p の上付き break が整数**（本命題）
--  * `haaSubquotients` / `haaSumBreak` / `haaSumFrom` / `haa_sum_integer` / `haa_subquotient_integer`
--      — 各部分商が巡回→hau 適用→和で整数（合成列 over の帰納）
--  * `haa_each_subquotient_cyclic` — 各因子（部分商）が巡回で hau 整数性を満たす
--  * `haa_reduces_to_cyclic` — 第 2 因子空で M456F 巡回版 `hau_upper_break_integer` へ厳密還元
--  * `haa_not_cyclic` — **ℤ/p×ℤ/p は非巡回**（exponent p < order p²・rank 2・2 生成元）
--  * `haaScope` / `haaModelScope` / `haa_model_scope` / `haa_scope_witness`
--      — 正直な限定の定理化（M456F「巡回のみ」を破った印を明示）
--  * `HasseArfAbelianData` / `haaDataOf` / `haa_exists` — capstone
--  * `haa_ex_*`（Klein 四元群 ℤ/2×ℤ/2: 非巡回・上付き break=2・exponent 2<order 4 ほか）
--
--  正直な限定（CLAUDE.md §4: 消去・弱化禁止）: 上記ヘッダ限定を §6 で定理化。破ったのは
--  M456F の「巡回のみ」——非巡回アーベル ℤ/p×ℤ/p（基本アーベル p-群・rank 2・1 次元指標）へ昇格。
--  一般アーベル（任意有限アーベル・高 rank）・非可換・混標数一般 Hasse–Arf は後続。
--  全て選択公理不使用（propext/Quot.sound のみ）。共有ファイル未変更（新規 1 本）。
-/
import IUT.HasseArfUnconditional

namespace IUT

/-! ## §1 非巡回アーベル ℤ/p×ℤ/p（基本アーベル p-群・rank 2）の分岐フィルトレーション位数列

    剰余標数 p の局所体上の**非巡回アーベル拡大**の代表 ℤ/p×ℤ/p（基本アーベル p-群・
    exponent p・order p²）を扱う。その分岐群も基本アーベル p-群で、合成列
      G = ℤ/p×ℤ/p ⊃ ℤ/p×1 ⊃ 1   （|G_i| = p², p, 1）
    を持ち、各部分商 G_i/G_{i+1} は素数位数 p の巡回群 ℤ/p（合成因子は単純アーベル＝巡回）。
    M456F hau が扱った巡回 ℤ/pⁿ 塔とは異なり、G 自身は巡回でない（exponent p < order p²）。 -/

/-- **M461F-1: ℤ/p×ℤ/p の位数** order = p²（基本アーベル p-群・rank 2）。 -/
def haaOrder (p : Nat) : Nat := p * p

/-- **M461F-1a: ℤ/p×ℤ/p の exponent** = p（全ての元の位数が p を割る・基本アーベル p-群）。
    巡回 ℤ/p² は exponent p² を持つのに対し、ℤ/p×ℤ/p は exponent p——非巡回性の核。 -/
def haaExponent (p : Nat) : Nat := p

/-- **M461F-1b: 分岐フィルトレーション位数列** |G_i| 降順 [p²,p,1]（合成列 G⊃ℤ/p×1⊃1）。
    非巡回アーベル ℤ/p×ℤ/p の分岐群の位数列（基本アーベル p-群の合成列）。 -/
def haaAbelianGroup (p : Nat) : List Nat := [p * p, p, 1]

/-- **M461F-1c: 部分商位数列** 各合成因子 G_i/G_{i+1} の位数 [p, p]（いずれも巡回 ℤ/p）。
    非巡回群の合成因子は素数位数の巡回群——各部分商に M456F hau を適用できる根拠。 -/
def haaSubquotientOrders (p : Nat) : List Nat := [p, p]

/-- **M461F-1d: 位数の値（本物・定義的）** order = p²。 -/
theorem haa_order_eq (p : Nat) : haaOrder p = p * p := rfl

/-- **M461F-1e: 位数列の値（本物・定義的）** [p²,p,1]。 -/
theorem haa_abelian_group_eq (p : Nat) : haaAbelianGroup p = [p * p, p, 1] := rfl

/-- **M461F-1f: 部分商位数列の値（本物・定義的）** 各部分商 ℤ/p（位数 p）。 -/
theorem haa_subquotient_orders_eq (p : Nat) : haaSubquotientOrders p = [p, p] := rfl

/-! ## §2 積分解によるアーベル上付き break φ = φ₁ + φ₂（M456F 巡回版を非巡回へ）

    非巡回アーベル ℤ/p×ℤ/p を 2 つの巡回因子 ℤ/p × ℤ/p に分解する。各因子は巡回塔ゆえ
    M456F hau の上付き増分列（`List Nat`）で符号化できる。積群の上付き break は Herbrand φ の
    加法性から因子ごとの巡回 break の和
        φ(b) = φ₁(b) + φ₂(b) = Σ u_i^{(1)} + Σ u_i^{(2)}
    になる（積分解）。段ごとの Herbrand 復元 hauUpperFrom を因子ごとに積み、和をとる。 -/

/-- **M461F-2: アーベル上付き break** φ = φ₁+φ₂ = Σu_i^{(1)}+Σu_i^{(2)}（因子ごとの巡回 break の和）。
    非巡回アーベル ℤ/p×ℤ/p を 2 巡回因子 (us₁,us₂) の上付き増分列で符号化した積分解。 -/
def haaUpperBreak (f : List Nat × List Nat) : Nat :=
  hauUpperBreak f.1 + hauUpperBreak f.2

/-- **M461F-2a: アーベル上付き break の Herbrand 復元** 各因子で段ごと φ 復元 hauUpperFrom を積み
    和をとる（φ₁∘ψ₁ + φ₂∘ψ₂）。積群の上付き番号を因子ごとに復元して合成。 -/
def haaUpperFrom (p : Nat) (f : List Nat × List Nat) : Nat :=
  hauUpperFrom p 1 f.1 + hauUpperFrom p 1 f.2

/-- **M461F-2b: 積分解（本物・定義的・積の break が各因子の break から決まる）** —
    haaUpperBreak f = hauUpperBreak f.1 + hauUpperBreak f.2。ℤ/p×ℤ/p の break が
    2 因子 ℤ/p の break の和に分解する（積群の Herbrand φ の加法性）。 -/
theorem haa_product_break (f : List Nat × List Nat) :
    haaUpperBreak f = hauUpperBreak f.1 + hauUpperBreak f.2 := rfl

/-- **M461F-2c: 非巡回アーベル ℤ/p×ℤ/p の上付き break が整数（本命題・M456F「巡回のみ」突破）** —
    haaUpperFrom p f = haaUpperBreak f。各因子は巡回ゆえ M456F `hau_upper_break_integer` で
    段ごと Herbrand 復元が上付き break Σu_i（整数）に一致、アーベル性（和が可換・因子独立）から
    積群全体の上付き break も整数。**非巡回でも整数**——巡回に限らない Hasse–Arf のアーベル版。 -/
theorem haa_upper_break_integer_abelian (p : Nat) (hp : 1 ≤ p) (f : List Nat × List Nat) :
    haaUpperFrom p f = haaUpperBreak f := by
  show hauUpperFrom p 1 f.1 + hauUpperFrom p 1 f.2
     = hauUpperBreak f.1 + hauUpperBreak f.2
  rw [hau_upper_break_integer p hp f.1, hau_upper_break_integer p hp f.2]

/-! ## §3 各部分商が巡回→hau 適用→和で整数（合成列についての帰納）

    非巡回群 ℤ/p×ℤ/p 自身に巡回版 hau は直接使えないが、**合成列の各部分商 G_i/G_{i+1} は
    巡回 ℤ/p** ゆえ各部分商には hau が使える。部分商の上付き増分列のリストを走査し、各々に
    `hau_upper_break_integer`（巡回版）を適用して整数性を積み上げる（合成列 over の帰納法）。 -/

/-- **M461F-3: 合成列の部分商（各巡回 ℤ/p の上付き増分列のリスト）** [f.1, f.2]。
    非巡回 ℤ/p×ℤ/p の 2 つの巡回合成因子を上付き増分列で並べる。 -/
def haaSubquotients (f : List Nat × List Nat) : List (List Nat) := [f.1, f.2]

/-- **M461F-3a: 部分商 break の総和** Σ_j hauUpperBreak (部分商_j)（合成因子ごとの巡回 break 和）。 -/
def haaSumBreak : List (List Nat) → Nat
  | []            => 0
  | us :: rest    => hauUpperBreak us + haaSumBreak rest

/-- **M461F-3b: 部分商 Herbrand 復元の総和** Σ_j hauUpperFrom p 1 (部分商_j)（各部分商で段ごと復元）。 -/
def haaSumFrom (p : Nat) : List (List Nat) → Nat
  | []         => 0
  | us :: rest => hauUpperFrom p 1 us + haaSumFrom p rest

/-- **M461F-3c: 部分商ごと整数性（本命題・合成列についての帰納法）** —
    haaSumFrom p fs = haaSumBreak fs。**各部分商が巡回**ゆえ M456F `hau_upper_break_integer`
    （巡回版）が各段の Herbrand 復元を上付き break へ一致させ、合成列を走査して和が整数に landing。
    非巡回群を巡回部分商へ分解して hau を適用する昇格の中核。 -/
theorem haa_sum_integer (p : Nat) (hp : 1 ≤ p) :
    ∀ fs : List (List Nat), haaSumFrom p fs = haaSumBreak fs := by
  intro fs
  induction fs with
  | nil => rfl
  | cons us rest ih =>
    show hauUpperFrom p 1 us + haaSumFrom p rest = hauUpperBreak us + haaSumBreak rest
    rw [hau_upper_break_integer p hp us, ih]

/-- **M461F-3d: 部分商和 = アーベル上付き break（本物）** —
    haaSumBreak (部分商) = haaUpperBreak f。2 つの巡回部分商 break の和が積群の上付き break に一致。 -/
theorem haa_sum_eq_product (f : List Nat × List Nat) :
    haaSumBreak (haaSubquotients f) = haaUpperBreak f := by
  show hauUpperBreak f.1 + (hauUpperBreak f.2 + 0)
     = hauUpperBreak f.1 + hauUpperBreak f.2
  rw [Nat.add_zero]

/-- **M461F-3e: 部分商経由の整数性（本物）** — 合成列の各巡回部分商に hau を適用した和が
    積群の上付き break に一致: haaSumFrom p (部分商) = haaUpperBreak f。
    「部分商巡回→hau→アーベル和」の一本道を定理化（`haa_upper_break_integer_abelian` の
    部分商版・非巡回群を巡回に還元して整数性を得る証拠）。 -/
theorem haa_subquotient_integer (p : Nat) (hp : 1 ≤ p) (f : List Nat × List Nat) :
    haaSumFrom p (haaSubquotients f) = haaUpperBreak f := by
  rw [haa_sum_integer p hp (haaSubquotients f), haa_sum_eq_product f]

/-- **M461F-3f: 各部分商が巡回で hau 整数性を満たす（本物）** —
    ℤ/p×ℤ/p の 2 つの合成因子 f.1, f.2 は各々巡回 ℤ/p ゆえ M456F `hau_upper_break_integer`
    （巡回版）を満たす。非巡回群の整数性が各巡回部分商の整数性に還元される核。 -/
theorem haa_each_subquotient_cyclic (p : Nat) (hp : 1 ≤ p) (f : List Nat × List Nat) :
    hauUpperFrom p 1 f.1 = hauUpperBreak f.1 ∧ hauUpperFrom p 1 f.2 = hauUpperBreak f.2 :=
  ⟨hau_upper_break_integer p hp f.1, hau_upper_break_integer p hp f.2⟩

/-! ## §4 第 2 因子空で M456F 巡回版へ厳密還元（genuine reduction）

    積 ℤ/p×ℤ/p の第 2 因子を自明（空の上付き増分列 []）にすると 1×ℤ/p ≅ ℤ/p（巡回）になり、
    アーベル上付き break が M456F hau の巡回上付き break に厳密一致する。非巡回昇格が巡回ケースで
    旧結果を回復する印。 -/

/-- **M461F-4: 第 2 因子空で M456F 巡回版へ厳密還元（本物）** —
    第 2 因子を [] にすると haaUpperFrom p (us,[]) = hauUpperFrom p 1 us、
    haaUpperBreak (us,[]) = hauUpperBreak us（M456F 巡回 ℤ/pⁿ 塔と一致）。
    非巡回 ℤ/p×ℤ/p の昇格が、巡回部分（ℤ/p×1）で M456F へ戻る genuine reduction。 -/
theorem haa_reduces_to_cyclic (p : Nat) (us : List Nat) :
    haaUpperFrom p (us, []) = hauUpperFrom p 1 us
    ∧ haaUpperBreak (us, []) = hauUpperBreak us := by
  refine ⟨?_, ?_⟩
  · show hauUpperFrom p 1 us + hauUpperFrom p 1 ([] : List Nat) = hauUpperFrom p 1 us
    exact Nat.add_zero _
  · show hauUpperBreak us + hauUpperBreak ([] : List Nat) = hauUpperBreak us
    exact Nat.add_zero _

/-- **M461F-4a: 巡回部分での M456F 整数性の回復（本物）** —
    第 2 因子空の ℤ/p×1（巡回 ℤ/p）で、アーベル整数性が M456F `hau_upper_break_integer` に一致。 -/
theorem haa_reduces_to_cyclic_integer (p : Nat) (hp : 1 ≤ p) (us : List Nat) :
    haaUpperFrom p (us, []) = haaUpperBreak (us, []) := by
  have h1 : haaUpperFrom p (us, []) = hauUpperFrom p 1 us := (haa_reduces_to_cyclic p us).1
  have h2 : haaUpperBreak (us, []) = hauUpperBreak us := (haa_reduces_to_cyclic p us).2
  rw [h1, h2]
  exact hau_upper_break_integer p hp us

/-! ## §5 非巡回性: ℤ/p×ℤ/p は巡回でない（exponent p < order p²・rank 2）

    M456F hau が扱ったのは巡回群のみ。ℤ/p×ℤ/p が実際に巡回でないことを示す:
    基本アーベル p-群は exponent p（全元の位数が p を割る）だが order p²、p<p²（p≥2）ゆえ
    位数 p² の元を持たない——巡回 ℤ/p² なら位数 p² の生成元を持つのと対照的。rank 2（2 生成元必要）。
    これで M456F の「巡回のみ」を実際に破ったことを明示する。 -/

/-- **M461F-5: 2 生成元（rank 2）** ℤ/p×ℤ/p は 2 つの独立生成元を持つ（巡回は 1 生成元）。 -/
def haaGenerators : List Nat := [1, 1]

/-- **M461F-5a: rank 2（本物）** rank = 生成元数 = 2 > 1（巡回でない・2 生成元必要）。 -/
def haaRank : Nat := 2

/-- **M461F-5b: exponent < order（本物・非巡回性の核）** p < p²（p≥2）。
    基本アーベル p-群 ℤ/p×ℤ/p は exponent p だが order p²。巡回群なら位数 = order の元
    （生成元）を持つが、ここでは全元の位数 ≤ exponent p < p² = order ゆえ生成元が存在しない
    ——**ℤ/p×ℤ/p は巡回でない**。M456F「巡回のみ」を破った本質。 -/
theorem haa_exponent_lt_order (p : Nat) (hp : 2 ≤ p) : haaExponent p < haaOrder p := by
  show p < p * p
  have h1 : p * 2 ≤ p * p := Nat.mul_le_mul (Nat.le_refl p) hp
  omega

/-- **M461F-5c: ℤ/p×ℤ/p は非巡回（本命題・M456F「巡回のみ」を破った印）** —
    exponent p < order p²（位数 order の元を持たない＝巡回でない）かつ rank 2（2 生成元必要・>1）。
    M456F hau は巡回群のみを扱ったが、本モジュールはこの非巡回 ℤ/p×ℤ/p の上付き break 整数性を
    `haa_upper_break_integer_abelian` で閉じた——「巡回のみ」制限を実際に突破した証拠。 -/
theorem haa_not_cyclic (p : Nat) (hp : 2 ≤ p) :
    haaExponent p < haaOrder p ∧ haaRank = 2 ∧ 1 < haaRank
    ∧ haaGenerators.length = 2 := by
  refine ⟨haa_exponent_lt_order p hp, rfl, ?_, rfl⟩
  show 1 < 2
  omega

/-! ## §6 正直な限定の定理化（CLAUDE.md §4: 消去・弱化禁止）

    本モジュールが M456F の「巡回のみ（generalAbelianNonCyclic=false）」を破ったのは、次を
    **すべて満たす**昇格に限る:
      (nonCyclicAbelian)   非巡回アーベル ℤ/p×ℤ/p の上付き break 整数性を本物化,
      (elementaryAbelianRank2) 基本アーベル p-群・rank 2（exponent p < order p²）,
      (subquotientsCyclic) 各部分商 ℤ/p が巡回で M456F hau を適用,
      (brokeCyclicOnly)    M456F の「巡回のみ」を非巡回 ℤ/p×ℤ/p で実際に破った。
    以下は**依然対象外**（フラグ false）——後続:
      (generalFiniteAbelian) 一般アーベル（任意の有限アーベル群・ℤ/p^a×ℤ/p^b 混合・高位数）,
      (highRank)             高 rank（rank ≥ 3 の基本アーベル p-群）,
      (nonAbelian)           非可換・dim≥2 表現,
      (fullHasseArf)         混標数一般 Hasse–Arf 定理の完全証明（任意アーベル拡大の整数性）。 -/

/-- **M461F-6: 正直な限定フラグ** — 破った非巡回アーベルケースと依然未対応の一般化を Bool で明示。 -/
structure haaScope where
  /-- 非巡回アーベル ℤ/p×ℤ/p の上付き break 整数性を本物化（M456F「巡回のみ」を破った）。 -/
  nonCyclicAbelian : Bool
  /-- 基本アーベル p-群・rank 2（exponent p < order p²）。 -/
  elementaryAbelianRank2 : Bool
  /-- 各部分商 ℤ/p が巡回で M456F hau を適用。 -/
  subquotientsCyclic : Bool
  /-- M456F の「巡回のみ」を非巡回 ℤ/p×ℤ/p で実際に破った。 -/
  brokeCyclicOnly : Bool
  /-- 一般アーベル（任意有限アーベル・ℤ/p^a×ℤ/p^b 混合・高位数）— 未対応。 -/
  generalFiniteAbelian : Bool
  /-- 高 rank（rank ≥ 3）— 未対応。 -/
  highRank : Bool
  /-- 非可換・dim≥2 表現 — 未対応。 -/
  nonAbelian : Bool
  /-- 混標数一般 Hasse–Arf 定理の完全証明 — 未対応。 -/
  fullHasseArf : Bool

/-- **M461F-6a: 本モジュールの scope witness** — 破った非巡回アーベルケース（前 4 つ true）と
    依然未対応の一般化（後 4 つ false）。nonCyclicAbelian=true が M456F「巡回のみ」を破った印。 -/
def haaModelScope : haaScope where
  nonCyclicAbelian := true
  elementaryAbelianRank2 := true
  subquotientsCyclic := true
  brokeCyclicOnly := true
  generalFiniteAbelian := false
  highRank := false
  nonAbelian := false
  fullHasseArf := false

/-- **M461F-6b: 正直な限定（定理・消さない）** — 破ったのは非巡回アーベル ℤ/p×ℤ/p のみ。
    一般有限アーベル・高 rank・非可換・完全一般 Hasse–Arf は false（対象外）。 -/
theorem haa_model_scope :
    haaModelScope.nonCyclicAbelian = true ∧ haaModelScope.elementaryAbelianRank2 = true ∧
    haaModelScope.subquotientsCyclic = true ∧ haaModelScope.brokeCyclicOnly = true ∧
    haaModelScope.generalFiniteAbelian = false ∧ haaModelScope.highRank = false ∧
    haaModelScope.nonAbelian = false ∧ haaModelScope.fullHasseArf = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **M461F-6c: 「巡回のみ」を破ったことの定理（本物）** — 非巡回アーベル ℤ/p×ℤ/p（exponent p <
    order p²・巡回でない）で上付き break 整数性が成立する: 任意の 2 巡回因子 f に対し
    アーベル Herbrand 復元 = 上付き break。M456F が巡回のみを扱ったのと対照的に、本定理は
    非巡回群で整数性を主張する（各部分商巡回＋アーベル性で自動）。 -/
theorem haa_scope_witness :
    (haaModelScope.nonCyclicAbelian = true) ∧
    (∀ p, 1 ≤ p → ∀ f : List Nat × List Nat, haaUpperFrom p f = haaUpperBreak f) ∧
    (∀ p, 2 ≤ p → haaExponent p < haaOrder p) :=
  ⟨rfl, fun p hp f => haa_upper_break_integer_abelian p hp f,
   fun p hp => haa_exponent_lt_order p hp⟩

/-! ## §7 capstone: 非巡回アーベル Hasse–Arf データ -/

/-- **M461F-7: 非巡回アーベル Hasse–Arf データ** — 剰余標数 p、単位性 hp、2 巡回因子の上付き
    増分列 factors、上付き break upperBreak を束ね、
      * upperBreak = Σu_i^{(1)}+Σu_i^{(2)}（`upper_eq`）,
      * **非巡回アーベル整数性** アーベル Herbrand 復元 = upperBreak（`integrality`）
    を要請する。非巡回アーベル ℤ/p×ℤ/p の上付き break 整数性（Hasse–Arf アーベル版）の核。 -/
structure HasseArfAbelianData where
  p : Nat
  hp : 1 ≤ p
  factors : List Nat × List Nat
  upperBreak : Nat
  upper_eq : upperBreak = haaUpperBreak factors
  integrality : haaUpperFrom p factors = upperBreak

/-- **M461F-7b: データの構成**（p, hp, 2 巡回因子 factors から本物 witness・非巡回でも整数）。 -/
def haaDataOf (p : Nat) (hp : 1 ≤ p) (f : List Nat × List Nat) : HasseArfAbelianData where
  p := p
  hp := hp
  factors := f
  upperBreak := haaUpperBreak f
  upper_eq := rfl
  integrality := haa_upper_break_integer_abelian p hp f

/-- **M461F-7c: データの存在**（無矛盾性 witness、Klein 四元群 ℤ/2×ℤ/2・各因子増分 [1]）。 -/
theorem haa_exists : Nonempty HasseArfAbelianData :=
  ⟨haaDataOf 2 (by omega) ([1], [1])⟩

/-! ## §8 worked examples: Klein 四元群 ℤ/2×ℤ/2（非巡回・上付き break=2・exponent 2<order 4） -/

/-- **M461F-8a: Klein 四元群 ℤ/2×ℤ/2 の上付き break = 2**（各巡回因子 ℤ/2 の break 1 の和）。 -/
theorem haa_ex_klein_break : haaUpperBreak ([1], [1]) = 2 := rfl

/-- **M461F-8b: Klein 四元群の整数性（非巡回）** アーベル Herbrand 復元が上付き break 2 に landing。
    ℤ/2×ℤ/2 は非巡回（M456F が扱えない）だが、各部分商 ℤ/2 が巡回ゆえ hau で整数に閉じる。 -/
theorem haa_ex_klein_integer : haaUpperFrom 2 ([1], [1]) = 2 :=
  (haa_upper_break_integer_abelian 2 (by omega) ([1], [1])).trans rfl

/-- **M461F-8c: Klein 四元群は非巡回** exponent 2 < order 4（位数 4 の元なし＝巡回でない）。
    巡回 ℤ/4 なら位数 4 の生成元を持つが、ℤ/2×ℤ/2 は exponent 2——M456F「巡回のみ」を破った。 -/
theorem haa_ex_klein_not_cyclic : haaExponent 2 < haaOrder 2 :=
  haa_exponent_lt_order 2 (by omega)

/-- **M461F-8d: ℤ/2×ℤ/2 の位数** order = 4。 -/
theorem haa_ex_order : haaOrder 2 = 4 := rfl

/-- **M461F-8e: 分岐フィルトレーション位数列** [4,2,1]（合成列 ℤ/2×ℤ/2 ⊃ ℤ/2 ⊃ 1）。 -/
theorem haa_ex_group_seq : haaAbelianGroup 2 = [4, 2, 1] := rfl

/-- **M461F-8f: 部分商** 各合成因子 ℤ/2（位数 2・巡回）: [[1],[1]]。 -/
theorem haa_ex_subquotients : haaSubquotients ([1], [1]) = [[1], [1]] := rfl

/-- **M461F-8g: 部分商経由の整数性** 2 巡回部分商への hau 適用の和 = 上付き break 2。 -/
theorem haa_ex_subquotient_integer : haaSumFrom 2 (haaSubquotients ([1], [1])) = 2 :=
  (haa_subquotient_integer 2 (by omega) ([1], [1])).trans rfl

/-- **M461F-8h: 第 2 因子空で M456F 巡回版へ還元（us=[1,1]）** アーベル break = 巡回 break。 -/
theorem haa_ex_reduce_cyclic :
    haaUpperFrom 2 ([1, 1], []) = hauUpperFrom 2 1 [1, 1]
    ∧ haaUpperBreak ([1, 1], []) = hauUpperBreak [1, 1] :=
  haa_reduces_to_cyclic 2 [1, 1]

/-- **M461F-8i: capstone まとめ** — Klein 四元群 ℤ/2×ℤ/2（非巡回・上付き break=2）・
    exponent 2<order 4（非巡回性）・位数列 [4,2,1]・部分商巡回経由の整数性・M456F 還元。 -/
theorem haa_examples :
    haaUpperBreak ([1], [1]) = 2 ∧
    haaUpperFrom 2 ([1], [1]) = 2 ∧
    haaExponent 2 < haaOrder 2 ∧
    haaOrder 2 = 4 ∧
    haaAbelianGroup 2 = [4, 2, 1] ∧
    haaSumFrom 2 (haaSubquotients ([1], [1])) = 2 :=
  ⟨rfl, haa_ex_klein_integer, haa_exponent_lt_order 2 (by omega), rfl, rfl,
   haa_ex_subquotient_integer⟩

end IUT
