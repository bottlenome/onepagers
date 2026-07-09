/-
  IUT/PolyMonomialBasis.lean — F8/PMB（冪基底 {1, X, …, X^{n−1}} と
  座標読み出しの環非依存な土台: 柱A 実 Galois 理論／実代数体の下ごしらえ）

  ── 分類 **[実／承認済み足場(c)]**（本物の証明・sorry 皆無・新規
  Classical.choice 皆無・模型ゼロ）。

  **complete_pct 影響**: 0 前進（足場整備のみ・complete_pct 未設定）。
  本層は `audit/A1-to-085-plan.md` の基底（B）節・F8 の**名前付き実
  ターゲット** 「NF 担体上の冪基底 `gefPowBasis`（次数 = deg f）で
  {1, α, …, α^{n−1}} が ℚ-基底であること（span＋一次独立）を本物に
  証明する（F9）」への必要足場である。F8 は座標写像を
  `pmbLinComb_coeff` 経由で spans／独立に落とすための**環非依存**な
  下ごしらえであり、NF 担体固有部分（α = [X] の冪・剰余簡約）は F9
  （後段）で本物化する。後続計画: 本補題群（特に座標読み出し
  `pmbLinComb_coeff` と零判定 `pmbLinComb_zero_iff`＝一次独立の核）を
  一般 CRing 上で確立し、F9 で NF 担体 `{g // IsPolyBounded g nf}` へ
  特殊化して `gefNF_sum_coeff` / `gefNFMonBasis` に接続する。

  * pmbMono          — 単項式 X^i = psSingle R R.one i（一般 CRing）
  * pmbMono_coeff    — 単項式の係数（対角: j = i で one・他は zero）
  * pmbLinComb       — 有限線形結合 Σ_{i<n} coef i · X^i（n 再帰・
                       各項は psSingle R (coef i) i = coef i · X^i）
  * pmbLinComb_succ  — 再帰の一段展開（定義等式）
  * pmbLinComb_bound — 有界性 IsPolyBounded (pmbLinComb coef n) n
  * pmbLinComb_coeff — **座標読み出し**: j < n で (Σ) j = coef j
                       （i ≠ j の単項式が j 次で 0 に効く・一次独立の核）
  * pmbLinComb_zero_iff — **零判定**: Σ = 0 ↔ ∀ i < n, coef i = 0
                       （⟸ 各項 0・⟹ 座標読み出しで各 coef i = 0・
                       一次独立に直結）
  * pmbLinComb_add   — 結合の加法性（coef の点ごと和）
  * pmbLinComb_smul  — 結合の定数倍（各係数への左積）

  正直な限定（何が本物で何を含めないか）:
   - **本物**: 単項式族と有限線形結合の座標読み出し・零判定は一般
     可換環 `CRing R` 上で完全証明（sorry 皆無・新規 choice 皆無）。
     座標読み出しと零判定は**基底の一次独立の核**そのものであり、
     代理でも模型でもない。
   - **含めない（F9 の担当）**: NF 担体 `{g // IsPolyBounded g nf}` への
     特殊化・α = [X] の冪が単項式に一致すること・剰余簡約（red）を
     経る乗法・`TowerLawBasis` レコードの充填は本層に含めない（環乗法
     に依存するため F5/F9 で本物化する）。本層はそれらに非依存な
     係数列レベルの土台に限定する（早期並列のための切片）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.PolyPSUtil
import IUT.FrobeniusCharP

namespace IUT

/-! ## PMB-1: 単項式 X^i -/

/-- **PMB-1a: 単項式** X^i = (0,…,0,1,0,…)（i 次に one を置く）。
    一般 CRing 上の `psSingle R R.one i`。 -/
def pmbMono (R : CRing) (i : Nat) : PS R := psSingle R R.one i

/-- **PMB-1b: 単項式の係数** — (X^i)_j は対角（j = i で one・他は zero）。
    `psSingle` の定義そのもの（if 分岐）。 -/
theorem pmbMono_coeff (R : CRing) (i j : Nat) :
    pmbMono R i j = if j = i then R.one else R.zero := rfl

/-! ## PMB-2: 有限線形結合 Σ_{i<n} coef i · X^i -/

/-- **PMB-2a: 有限線形結合** Σ_{i<n} coef i · X^i。n に関する再帰で
    各段に単項式項 `psSingle R (coef n) n`（= coef n · X^n）を足す。 -/
def pmbLinComb (R : CRing) (coef : Nat → R.carrier) : Nat → PS R
  | 0 => psZero R
  | n + 1 => psAdd R (pmbLinComb R coef n) (psSingle R (coef n) n)

/-- **PMB-2b: 再帰の一段展開**（定義等式）。 -/
theorem pmbLinComb_succ (R : CRing) (coef : Nat → R.carrier) (n : Nat) :
    pmbLinComb R coef (n + 1)
      = psAdd R (pmbLinComb R coef n) (psSingle R (coef n) n) := rfl

/-! ## PMB-3: 有界性（次数 < n） -/

/-- **PMB-3: 有界性** — Σ_{i<n} coef i · X^i は n で有界（n 以上の係数は
    0）。n 帰納: 各段の単項式 `psSingle (coef n) n` は n 次のみ非零、
    帰納法の残りは n で有界。 -/
theorem pmbLinComb_bound (R : CRing) (coef : Nat → R.carrier) (n : Nat) :
    IsPolyBounded R (pmbLinComb R coef n) n := by
  induction n with
  | zero =>
    intro i _
    show psZero R i = R.zero
    rfl
  | succ n ih =>
    intro i hi
    show R.add (pmbLinComb R coef n i) (psSingle R (coef n) n i) = R.zero
    rw [ih i (by omega),
      show psSingle R (coef n) n i = R.zero from if_neg (by omega),
      R.zero_add]

/-! ## PMB-4: 座標読み出し（一次独立の核） -/

/-- **PMB-4: 座標読み出し** — j < n なら (Σ_{i<n} coef i · X^i)_j = coef j。
    j 次で効くのは i = j の単項式だけ（i > j の項はまだ足されておらず
    有界性で 0、i < j の項は j 次で 0）。これが基底の一次独立の核。 -/
theorem pmbLinComb_coeff (R : CRing) (coef : Nat → R.carrier) :
    ∀ (n j : Nat), j < n → pmbLinComb R coef n j = coef j := by
  intro n
  induction n with
  | zero =>
    intro j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro j hj
    show R.add (pmbLinComb R coef n j) (psSingle R (coef n) n j) = coef j
    cases Nat.lt_or_ge j n with
    | inl hlt =>
      rw [ih j hlt,
        show psSingle R (coef n) n j = R.zero from if_neg (by omega),
        CRing.add_zero R]
    | inr hge =>
      rw [show pmbLinComb R coef n j = R.zero
            from pmbLinComb_bound R coef n j hge,
        show psSingle R (coef n) n j = coef n from if_pos (by omega),
        R.zero_add, show j = n from by omega]

/-! ## PMB-5: 零判定（一次独立に直結） -/

/-- **PMB-5: 零判定** — Σ_{i<n} coef i · X^i = 0 ⟺ 各 coef i (i<n) が 0。
    ⟸ は全係数消滅（j<n は仮定・j≥n は有界性）。⟹ は座標読み出しで
    coef i = (Σ) i = 0。**{1, X, …, X^{n−1}} の一次独立そのもの**。 -/
theorem pmbLinComb_zero_iff (R : CRing) (coef : Nat → R.carrier) (n : Nat) :
    pmbLinComb R coef n = psZero R ↔ (∀ i, i < n → coef i = R.zero) := by
  constructor
  · intro h i hi
    have hci : pmbLinComb R coef n i = coef i := pmbLinComb_coeff R coef n i hi
    rw [← hci, h]
    rfl
  · intro h
    funext j
    show pmbLinComb R coef n j = R.zero
    cases Nat.lt_or_ge j n with
    | inl hlt =>
      rw [pmbLinComb_coeff R coef n j hlt]
      exact h j hlt
    | inr hge =>
      exact pmbLinComb_bound R coef n j hge

/-! ## PMB-6: 加法性・定数倍（余力） -/

/-- **PMB-6a: 結合の加法性** — 係数列の点ごと和の線形結合は、線形結合の
    点ごと和に等しい。j < n は座標読み出し、j ≥ n は有界性で照合。 -/
theorem pmbLinComb_add (R : CRing) (a b : Nat → R.carrier) (n : Nat) :
    pmbLinComb R (fun i => R.add (a i) (b i)) n
      = psAdd R (pmbLinComb R a n) (pmbLinComb R b n) := by
  funext j
  show pmbLinComb R (fun i => R.add (a i) (b i)) n j
    = R.add (pmbLinComb R a n j) (pmbLinComb R b n j)
  cases Nat.lt_or_ge j n with
  | inl hlt =>
    rw [pmbLinComb_coeff R (fun i => R.add (a i) (b i)) n j hlt,
      pmbLinComb_coeff R a n j hlt, pmbLinComb_coeff R b n j hlt]
  | inr hge =>
    rw [pmbLinComb_bound R (fun i => R.add (a i) (b i)) n j hge,
      pmbLinComb_bound R a n j hge, pmbLinComb_bound R b n j hge,
      R.zero_add]

/-- **PMB-6b: 結合の定数倍** — 各係数に左から c を掛けた線形結合の j 次
    係数は、元の線形結合の j 次係数に c を左から掛けたもの。 -/
theorem pmbLinComb_smul (R : CRing) (c : R.carrier)
    (coef : Nat → R.carrier) (n : Nat) :
    ∀ j, pmbLinComb R (fun i => R.mul c (coef i)) n j
      = R.mul c (pmbLinComb R coef n j) := by
  intro j
  cases Nat.lt_or_ge j n with
  | inl hlt =>
    rw [pmbLinComb_coeff R (fun i => R.mul c (coef i)) n j hlt,
      pmbLinComb_coeff R coef n j hlt]
  | inr hge =>
    rw [pmbLinComb_bound R (fun i => R.mul c (coef i)) n j hge,
      pmbLinComb_bound R coef n j hge, CRing.mul_zero R c]

end IUT
