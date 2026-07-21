/-
  IUT/Q3KummerNonicSplit.lean — q27ps（level-27 wild 分割 3 = π₂₇¹⁸·u₁₈・
    実 O_{M₂₇} = O_{M₉}[Z]/(Z³−ζ₉) 上の忠実性要石）

  ── 主要成果の分類: **[実／(c) 承認済み足場]**（named 実ターゲット = 柱A **A6**
     mono-anabelian 復元の **level-27 第 2 層 KILL キャンペーン**。本ファイルは
     scope（audit/level27-kill-scope-2026-07-11.md §1.3）が手計算で割った閉形式
       π₂₇ = Z−1・(Z−1)³ = π₉ + 3(Z−Z²) = π₉·w̃・w̃ = 1 + π₉⁵u₆·(Z−Z²)・
       u₁₈ := w̃⁻⁶·u₆・3 = π₂₇¹⁸·u₁₈
     を実 q27k 環（q27kRing・実係数環 q3kRing・実 ζ₉ ねじれ）の上で証明する
     level-9 q9ps（3 = π₉⁶·u₆）の 1 段上化。toy 主語なし——主語は実 q27k/q3k/q3rq/z3。
     これにより「3 := (18, 任意単数)」の模型に落ちず、u₁₈ が**本物の閉形式単数**
     （w̃ の実逆元 q27kInv 消費）として実在する——キャンペーンの [実] 分類の生命線。
     後続本物化計画（承認済み足場の昇格経路）: q27ci（M₉ 正則性パック）→ q27yp
     （Z 冪正規形）→ q27cs（12 座標降下 de-risk）→ q27c（μ₂₇ 完全性）→
     q27tl/q27mt/q27mr → q27mb（kill_mod27）→ crk27（mod-27 接続）。

  complete_pct 影響: **A6 level-27 wild 分割 — complete_pct 0 前進（本ファイル）**。
     本ファイルは kill も剛性もテータも橋も含まない分割恒等式の先行建設であり、
     実 IUT 完全証明率を動かさない。s_A6（現 0.61・帽子 ≤0.65）が動くのは
     キャンペーン末端の橋 q27mb ＋ mod-27 接続が閉じた時のみで、その時も帽子
     ≤0.65 の内側に留まる。本ファイルでは A6 status を一切動かさない（過大主張しない）。

  内容（scope §1.3 の閉形式の Lean 検証）:
   * q27psPi27 := Z−1・q27ps_pi27_coords — 一様化子の座標形 (−1, 1, 0)
   * q27psT := π₉⁵·u₆・q27ps_pi9_T — π₉·T = 3（q9ps_three_split の π₉ 括り出し）
   * q27psWt = 1 + T·Z − T·Z² （= w̃・Z-基底座標 (1, π₉⁵u₆, −π₉⁵u₆)）
   * q27ps_pi27_cubed_eq — **(Z−1)³ = π₉ + 3Z − 3Z²**（座標 (π₉, 3, −3)・閉形式検証）
   * q27ps_pi27_cube — **(Z−1)³ = embed(π₉)·w̃**（★ 要石 1）
   * q27ps_wt_normBase / q27ps_wt_norm_U15 — **N_{M₂₇/M₉}(w̃) = 1 + S・S ∈ π₉¹⁵O_{M₉}**
     （★ 正直な差分: N(w̃) は主単数 1+O(π₉¹⁵)。level-9 の綺麗な定数 N(w)=−1 は消える）
   * q27ps_ufilt6_unit — **U^(6) ⊆ O_{M₉}^×**（主単数 1+3s の実単数性・ノルム 3 段降下
     q9nf 機構＋q3mc レベル 1 判定で choice-free に証明。q27ps に局在する新しい単数論）
   * q27ps_wt_unit / q27psU18 / q27ps_u18_unit — w̃ 実単数・u₁₈ := w̃⁻⁶·u₆ 実単数
   * q27ps_three_split — **3 = π₂₇¹⁸·u₁₈**（★★★ 要石・v_{M₂₇}(3)=18 の代数的実現）
   * Q3KummerNonicSplitData / q27psData / q27ps_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・q3k/q9ps/q27k 継承の上に追記のみ）:
  1. **代数的分割レベルのみ**（付値論・位相なし）。e=18 wild 分岐は「3 = π₂₇¹⁸·u₁₈ の
     代数恒等式」として実現するが、v_{M₂₇} の付値理論・M₂₇ の完備化は範囲外。
     v_{M₂₇}(3)=18 は恒等式の指数 18 としてのみ実現（q9ps §1 継承）。
  2. **N(w̃) は主単数（1 + O(π₉¹⁵)・q27ps_wt_norm_U15）であって綺麗な定数ではない**。
     level-9 の N(w) = −1（q9ps_w_norm 1 行）に対応する閉じた定数形は level-27 には
     存在しない——これが scope §1.3 の「第 1 の正直な差分」であり、w̃ の単数性は
     主単数論（U^(6) ⊆ O_{M₉}^×・本ファイル q27ps_ufilt6_unit）を要する。
  3. **本ファイルは何も kill しない**（要石・foundation のみ）。テータ・μ₂₇ 完全性・
     剛性・橋は後続 q27c/q27mt/q27mr/q27mb。A6 status を動かさない。
  4. q3k/q9ps/q27k の正直限定を全継承（O と ^× のみ・体化なし・τ を超える Galois ゼロ・
     実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体・tmzLimit 橋なし）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3KummerNonic
import IUT.Q3NormFiltrationSpike

namespace IUT

/-! ## q27ps-0: ブリッジ（q27k 演算 ↔ q27kRing 演算） -/

/-- q27kAdd = q27kRing.add（rfl）。 -/
theorem q27ps_kA_eq : q27kAdd = q27kRing.add := rfl

/-- q27kNeg = q27kRing.neg（rfl）。 -/
theorem q27ps_kN_eq : q27kNeg = q27kRing.neg := rfl

/-- q27kOne = q27kRing.one（rfl）。 -/
theorem q27ps_kO_eq : q27kOne = q27kRing.one := rfl

/-- 乗法 4 因子入替（q27kMul 形）。 -/
theorem q27ps_mmmc (a b c d : q27kCar) :
    q27kMul (q27kMul a b) (q27kMul c d) = q27kMul (q27kMul a c) (q27kMul b d) := by
  rw [q27k_kM_eq]
  exact q27kRing.mul_mul_mul_comm a b c d

/-- 乗法結合（q27kMul 形）。 -/
theorem q27ps_massoc (a b c : q27kCar) :
    q27kMul (q27kMul a b) c = q27kMul a (q27kMul b c) := by
  rw [q27k_kM_eq]
  exact q27kRing.mul_assoc a b c

/-! ## q27ps-1: 3 の橋（3_{M₉} = embed_{M₉}(3_{L₂})・3_{M₂₇} = embed_{M₂₇}(3_{M₉})） -/

/-- **3_{M₉} = q3kEmbed(3_{L₂})**（q27kThree の embed 形）。 -/
theorem q27ps_threeM : q27kThree = q3kEmbed q3rqThreeElt := by
  apply q3k_ext
  · show q3rqAdd q3rqOne (q3rqAdd q3rqOne q3rqOne) = q3rqThreeElt
    exact q9ps_three_eq
  · show q3rqAdd q3rqZero (q3rqAdd q3rqZero q3rqZero) = q3rqZero
    rw [q3k_A_eq, q3k_Z_eq, q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.add_zero q3rqRing.zero]
  · show q3rqAdd q3rqZero (q3rqAdd q3rqZero q3rqZero) = q3rqZero
    rw [q3k_A_eq, q3k_Z_eq, q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.add_zero q3rqRing.zero]

/-- **3_{M₂₇} = q27kEmbed(3_{M₉})**（1+1+1 in O_{M₂₇} の embed 形）。 -/
theorem q27ps_threeM27 :
    q27kAdd q27kOne (q27kAdd q27kOne q27kOne) = q27kEmbed q27kThree := by
  apply q27k_ext
  · rfl
  · show q3kAdd q3kZero (q3kAdd q3kZero q3kZero) = q3kZero
    rw [q27k_A_eq, q27k_Z_eq, q3kRing.add_zero q3kRing.zero,
        q3kRing.add_zero q3kRing.zero]
  · show q3kAdd q3kZero (q3kAdd q3kZero q3kZero) = q3kZero
    rw [q27k_A_eq, q27k_Z_eq, q3kRing.add_zero q3kRing.zero,
        q3kRing.add_zero q3kRing.zero]

/-! ## q27ps-2: 一様化子 π₂₇ = ζ₂₇ − 1 = Z − 1 -/

/-- **q27ps-2a: π₂₇ = ζ₂₇ − 1 = Z − 1**（e=18 wild 一様化子・代数段）。 -/
def q27psPi27 : q27kCar := q27kAdd q27kZeta27 (q27kNeg q27kOne)

/-- π₂₇ の座標形 (−1, 1, 0)（Z-基底）。 -/
theorem q27ps_pi27_coords :
    q27psPi27 = ((q3kNeg q3kOne, q3kOne, q3kZero) : q27kCar) := by
  apply q27k_ext
  · show q3kAdd q3kZero (q3kNeg q3kOne) = q3kNeg q3kOne
    rw [q27k_A_eq, q27k_Z_eq]
    exact q3kRing.zero_add (q3kNeg q3kOne)
  · show q3kAdd q3kOne (q3kNeg q3kZero) = q3kOne
    rw [q27k_A_eq, q27k_N_eq, q27k_Z_eq, q3kRing.neg_zero, q3kRing.add_zero]
  · show q3kAdd q3kZero (q3kNeg q3kZero) = q3kZero
    rw [q27k_A_eq, q27k_N_eq, q27k_Z_eq, q3kRing.neg_zero, q3kRing.add_zero]

/-! ## q27ps-3: T = π₉⁵·u₆ と π₉·T = 3（q9ps_three_split の π₉ 括り出し） -/

/-- **q27ps-3a: T := π₉⁵·u₆ ∈ O_{M₉}**（w̃ の Z 係数）。 -/
def q27psT : q3kCar := q3kMul (q9nfPiPow 5) q9psU6

/-- **q27ps-3b（★）: π₉·T = 3_{M₉}**（3 = π₉⁶·u₆ = π₉·(π₉⁵u₆)・q9ps 消費）。 -/
theorem q27ps_pi9_T : q3kMul q9psPi9 q27psT = q27kThree := by
  have h1 : q3kMul q9psPi9 q27psT = q3kMul (q3kMul q9psPi9 (q9nfPiPow 5)) q9psU6 := by
    show q3kMul q9psPi9 (q3kMul (q9nfPiPow 5) q9psU6) = _
    rw [q3k_kM_eq]
    exact (q3kRing.mul_assoc q9psPi9 (q9nfPiPow 5) q9psU6).symm
  have h2 : q3kMul q9psPi9 (q9nfPiPow 5) = q9psPi6 := by
    show q9nfPiPow 6 = q9psPi6
    exact q9nf_pipow6_eq
  rw [h1, h2, q9ps_three_split]
  exact q27ps_threeM.symm

/-- 3_{M₉} = π₉⁶·u₆（q9nfPiPow 形・divisibility witness 用）。 -/
theorem q27ps_three_pi6_u6 : q27kThree = q3kMul (q9nfPiPow 6) q9psU6 := by
  rw [q9nf_pipow6_eq, q9ps_three_split]
  exact q27ps_threeM

/-! ## q27ps-4: w̃ = 1 + T·Z − T·Z² と閉形式 (Z−1)³ = π₉ + 3Z − 3Z² = embed(π₉)·w̃ -/

/-- **q27ps-4a: w̃ = 1 + π₉⁵u₆·Z − π₉⁵u₆·Z²**（Z-基底座標 (1, T, −T)・主単数）。 -/
def q27psWt : q27kCar := ((q3kOne, q27psT, q3kNeg q27psT) : q27kCar)

/-- (Z−1)² = 1 − 2Z + Z²（座標計算）。 -/
theorem q27ps_pi27_sq :
    q27kMul ((q3kNeg q3kOne, q3kOne, q3kZero) : q27kCar)
        ((q3kNeg q3kOne, q3kOne, q3kZero) : q27kCar)
      = ((q3kOne, q3kNeg (q3kAdd q3kOne q3kOne), q3kOne) : q27kCar) := by
  apply q27k_ext
  · show q3kAdd (q3kMul (q3kNeg q3kOne) (q3kNeg q3kOne))
        (q3kMul q3kZeta9 (q3kAdd (q3kMul q3kOne q3kZero) (q3kMul q3kZero q3kOne)))
      = q3kOne
    rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq, q9ps_kO_eq,
        q3kRing.neg_mul q3kRing.one (q3kRing.neg q3kRing.one),
        q3kRing.one_mul (q3kRing.neg q3kRing.one), q3kRing.neg_neg,
        q3kRing.mul_zero q3kRing.one, q3kRing.zero_mul q3kRing.one,
        q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9,
        q3kRing.add_zero q3kRing.one]
  · show q3kAdd (q3kAdd (q3kMul (q3kNeg q3kOne) q3kOne) (q3kMul q3kOne (q3kNeg q3kOne)))
        (q3kMul q3kZeta9 (q3kMul q3kZero q3kZero))
      = q3kNeg (q3kAdd q3kOne q3kOne)
    rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq, q9ps_kO_eq,
        q3kRing.neg_mul q3kRing.one q3kRing.one, q3kRing.one_mul q3kRing.one,
        q3kRing.one_mul (q3kRing.neg q3kRing.one),
        q3kRing.mul_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9,
        q3kRing.add_zero (q3kRing.add (q3kRing.neg q3kRing.one) (q3kRing.neg q3kRing.one)),
        ← q3kRing.neg_add_dist q3kRing.one q3kRing.one]
  · show q3kAdd (q3kAdd (q3kMul (q3kNeg q3kOne) q3kZero) (q3kMul q3kOne q3kOne))
        (q3kMul q3kZero (q3kNeg q3kOne))
      = q3kOne
    rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq, q9ps_kO_eq,
        q3kRing.mul_zero (q3kRing.neg q3kRing.one), q3kRing.one_mul q3kRing.one,
        q3kRing.zero_add q3kRing.one, q3kRing.zero_mul (q3kRing.neg q3kRing.one),
        q3kRing.add_zero q3kRing.one]

/-- (1 − 2Z + Z²)·(Z−1) = π₉ + 3Z − 3Z²（★ 閉形式 §1.3・座標 (π₉, 3, −3)）。 -/
theorem q27ps_pi27_cube_coords :
    q27kMul ((q3kOne, q3kNeg (q3kAdd q3kOne q3kOne), q3kOne) : q27kCar)
        ((q3kNeg q3kOne, q3kOne, q3kZero) : q27kCar)
      = ((q9psPi9, q27kThree, q3kNeg q27kThree) : q27kCar) := by
  apply q27k_ext
  · show q3kAdd (q3kMul q3kOne (q3kNeg q3kOne))
        (q3kMul q3kZeta9 (q3kAdd (q3kMul (q3kNeg (q3kAdd q3kOne q3kOne)) q3kZero)
          (q3kMul q3kOne q3kOne)))
      = q3kAdd q3kZeta9 (q3kNeg q3kOne)
    rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq, q9ps_kO_eq,
        q3kRing.one_mul (q3kRing.neg q3kRing.one),
        q3kRing.mul_zero (q3kRing.neg (q3kRing.add q3kRing.one q3kRing.one)),
        q3kRing.one_mul q3kRing.one, q3kRing.zero_add q3kRing.one,
        q3kRing.mul_one q3kZeta9,
        q3kRing.add_comm (q3kRing.neg q3kRing.one) q3kZeta9]
  · show q3kAdd (q3kAdd (q3kMul q3kOne q3kOne)
        (q3kMul (q3kNeg (q3kAdd q3kOne q3kOne)) (q3kNeg q3kOne)))
        (q3kMul q3kZeta9 (q3kMul q3kOne q3kZero))
      = q3kAdd q3kOne (q3kAdd q3kOne q3kOne)
    rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq, q9ps_kO_eq,
        q3kRing.one_mul q3kRing.one,
        q3kRing.neg_mul (q3kRing.add q3kRing.one q3kRing.one) (q3kRing.neg q3kRing.one),
        q3kRing.mul_neg (q3kRing.add q3kRing.one q3kRing.one) q3kRing.one,
        q3kRing.mul_one (q3kRing.add q3kRing.one q3kRing.one),
        q3kRing.neg_neg (q3kRing.add q3kRing.one q3kRing.one),
        q3kRing.mul_zero q3kRing.one, q3kRing.mul_zero q3kZeta9,
        q3kRing.add_zero (q3kRing.add q3kRing.one (q3kRing.add q3kRing.one q3kRing.one))]
  · show q3kAdd (q3kAdd (q3kMul q3kOne q3kZero)
        (q3kMul (q3kNeg (q3kAdd q3kOne q3kOne)) q3kOne))
        (q3kMul q3kOne (q3kNeg q3kOne))
      = q3kNeg (q3kAdd q3kOne (q3kAdd q3kOne q3kOne))
    rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq, q9ps_kO_eq,
        q3kRing.mul_zero q3kRing.one,
        q3kRing.mul_one (q3kRing.neg (q3kRing.add q3kRing.one q3kRing.one)),
        q3kRing.zero_add (q3kRing.neg (q3kRing.add q3kRing.one q3kRing.one)),
        q3kRing.one_mul (q3kRing.neg q3kRing.one),
        ← q3kRing.neg_add_dist (q3kRing.add q3kRing.one q3kRing.one) q3kRing.one,
        q3kRing.add_comm (q3kRing.add q3kRing.one q3kRing.one) q3kRing.one]

/-- π₂₇³ = ((Z−1)(Z−1))(Z−1)。 -/
def q27psPi27Cubed : q27kCar := q27kMul (q27kMul q27psPi27 q27psPi27) q27psPi27

/-- **q27ps-4b（★ 閉形式 §1.3）: (Z−1)³ = π₉ + 3Z − 3Z²**
    （= (ζ₉−1) + 3(Z−Z²)・Z-基底座標 (π₉, 3_{M₉}, −3_{M₉})・手計算の Lean 検証）。 -/
theorem q27ps_pi27_cubed_eq :
    q27psPi27Cubed = ((q9psPi9, q27kThree, q3kNeg q27kThree) : q27kCar) := by
  show q27kMul (q27kMul q27psPi27 q27psPi27) q27psPi27 = _
  rw [q27ps_pi27_coords, q27ps_pi27_sq]
  exact q27ps_pi27_cube_coords

/-- embed(π₉)·w̃ の座標 = (π₉, 3, −3)（π₉·T = 3 消費）。 -/
theorem q27ps_embedPi_wt :
    q27kMul (q27kEmbed q9psPi9) q27psWt
      = ((q9psPi9, q27kThree, q3kNeg q27kThree) : q27kCar) := by
  apply q27k_ext
  · show q3kAdd (q3kMul q9psPi9 q3kOne)
        (q3kMul q3kZeta9 (q3kAdd (q3kMul q3kZero (q3kNeg q27psT))
          (q3kMul q3kZero q27psT)))
      = q9psPi9
    rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq, q9ps_kO_eq,
        q3kRing.mul_one q9psPi9,
        q3kRing.zero_mul (q3kRing.neg q27psT), q3kRing.zero_mul q27psT,
        q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9,
        q3kRing.add_zero q9psPi9]
  · show q3kAdd (q3kAdd (q3kMul q9psPi9 q27psT) (q3kMul q3kZero q3kOne))
        (q3kMul q3kZeta9 (q3kMul q3kZero (q3kNeg q27psT)))
      = q27kThree
    rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq, q9ps_kO_eq,
        q3kRing.zero_mul q3kRing.one,
        q3kRing.add_zero (q3kRing.mul q9psPi9 q27psT),
        q3kRing.zero_mul (q3kRing.neg q27psT), q3kRing.mul_zero q3kZeta9,
        q3kRing.add_zero (q3kRing.mul q9psPi9 q27psT), ← q27k_M_eq]
    exact q27ps_pi9_T
  · show q3kAdd (q3kAdd (q3kMul q9psPi9 (q3kNeg q27psT)) (q3kMul q3kZero q27psT))
        (q3kMul q3kZero q3kOne)
      = q3kNeg q27kThree
    rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq, q9ps_kO_eq,
        q3kRing.zero_mul q27psT,
        q3kRing.add_zero (q3kRing.mul q9psPi9 (q3kRing.neg q27psT)),
        q3kRing.zero_mul q3kRing.one,
        q3kRing.add_zero (q3kRing.mul q9psPi9 (q3kRing.neg q27psT)),
        q3kRing.mul_neg q9psPi9 q27psT, ← q27k_M_eq, q27ps_pi9_T]

/-- **q27ps-4c（★ 要石 1）: (Z−1)³ = embed(π₉)·w̃**（π₉ 括り出し・§1.3）。 -/
theorem q27ps_pi27_cube :
    q27psPi27Cubed = q27kMul (q27kEmbed q9psPi9) q27psWt :=
  q27ps_pi27_cubed_eq.trans q27ps_embedPi_wt.symm

/-! ## q27ps-5: N_{M₂₇/M₉}(w̃) = 1 + S・S ∈ π₉¹⁵O_{M₉}（正直な差分: 主単数） -/

/-- N(w̃) の主単数部 S = ζ₉T³ − ζ₉²T³ + 3ζ₉T²（T = π₉⁵u₆ ⟹ v_{π₉}(S) ≥ 15）。 -/
def q27psS : q3kCar :=
  q3kAdd
    (q3kAdd (q3kMul q3kZeta9 (q3kMul (q3kMul q27psT q27psT) q27psT))
      (q3kNeg (q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kMul (q3kMul q27psT q27psT) q27psT))))
    (q3kMul q27kThree (q3kMul q3kZeta9 (q3kMul q27psT q27psT)))

/-- **q27ps-5a: N(w̃) = 1 + S**（相対 3 次ノルム多項式を (1, T, −T) で計算）。 -/
theorem q27ps_wt_normBase : q27kNormBase q27psWt = q3kAdd q3kOne q27psS := by
  show q3kAdd
      (q3kAdd
        (q3kAdd (q3kMul (q3kMul q3kOne q3kOne) q3kOne)
          (q3kMul q3kZeta9 (q3kMul (q3kMul q27psT q27psT) q27psT)))
        (q3kMul (q3kMul q3kZeta9 q3kZeta9)
          (q3kMul (q3kMul (q3kNeg q27psT) (q3kNeg q27psT)) (q3kNeg q27psT))))
      (q3kNeg (q3kMul q27kThree
        (q3kMul q3kZeta9 (q3kMul (q3kMul q3kOne q27psT) (q3kNeg q27psT)))))
    = q3kAdd q3kOne
        (q3kAdd
          (q3kAdd (q3kMul q3kZeta9 (q3kMul (q3kMul q27psT q27psT) q27psT))
            (q3kNeg (q3kMul (q3kMul q3kZeta9 q3kZeta9)
              (q3kMul (q3kMul q27psT q27psT) q27psT))))
          (q3kMul q27kThree (q3kMul q3kZeta9 (q3kMul q27psT q27psT))))
  rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q9ps_kO_eq,
      q3kRing.mul_one (q3kRing.mul q3kRing.one q3kRing.one),
      q3kRing.one_mul q3kRing.one,
      q3kRing.neg_mul q27psT (q3kRing.neg q27psT),
      q3kRing.mul_neg q27psT q27psT,
      q3kRing.neg_neg (q3kRing.mul q27psT q27psT),
      q3kRing.mul_neg (q3kRing.mul q27psT q27psT) q27psT,
      q3kRing.mul_neg (q3kRing.mul q3kZeta9 q3kZeta9)
        (q3kRing.mul (q3kRing.mul q27psT q27psT) q27psT),
      q3kRing.one_mul q27psT,
      q3kRing.mul_neg q27psT q27psT,
      q3kRing.mul_neg q3kZeta9 (q3kRing.mul q27psT q27psT),
      q3kRing.mul_neg q27kThree (q3kRing.mul q3kZeta9 (q3kRing.mul q27psT q27psT)),
      q3kRing.neg_neg (q3kRing.mul q27kThree
        (q3kRing.mul q3kZeta9 (q3kRing.mul q27psT q27psT))),
      q3kRing.add_assoc q3kRing.one
        (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul q27psT q27psT) q27psT))
        (q3kRing.neg (q3kRing.mul (q3kRing.mul q3kZeta9 q3kZeta9)
          (q3kRing.mul (q3kRing.mul q27psT q27psT) q27psT))),
      q3kRing.add_assoc q3kRing.one
        (q3kRing.add
          (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul q27psT q27psT) q27psT))
          (q3kRing.neg (q3kRing.mul (q3kRing.mul q3kZeta9 q3kZeta9)
            (q3kRing.mul (q3kRing.mul q27psT q27psT) q27psT))))
        (q3kRing.mul q27kThree (q3kRing.mul q3kZeta9 (q3kRing.mul q27psT q27psT)))]

/-- d ∣ x ⟹ d ∣ y·x（左倍元）。 -/
theorem q27ps_dvd_mul_left {d x : q3kCar} (h : q9wrDvd d x) (y : q3kCar) :
    q9wrDvd d (q3kMul y x) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨q3kMul c y, ?_⟩
  rw [hc, q3k_kM_eq, q3kRing.mul_comm y (q3kRing.mul d c), q3kRing.mul_assoc d c y]

/-- d ∣ x ⟹ d ∣ −x。 -/
theorem q27ps_dvd_neg {d x : q3kCar} (h : q9wrDvd d x) : q9wrDvd d (q3kNeg x) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨q3kNeg c, ?_⟩
  rw [hc, q3k_kM_eq, q9ps_kN_eq, q3kRing.mul_neg d c]

/-- **q27ps-5b: π₉¹⁵ ∣ S**（T³ は π₉¹⁵-可除・3ζ₉T² は π₉¹⁶-可除）。 -/
theorem q27ps_S_dvd15 : q9wrDvd (q9nfPiPow 15) q27psS := by
  have hT5 : q9wrDvd (q9nfPiPow 5) q27psT := ⟨q9psU6, rfl⟩
  have hT3 : q9wrDvd (q9nfPiPow 15) (q3kMul (q3kMul q27psT q27psT) q27psT) :=
    q9nf_dvd_of_le (by omega) (q9nf_dvd_mul (q9nf_dvd_mul hT5 hT5) hT5)
  have hA : q9wrDvd (q9nfPiPow 15)
      (q3kMul q3kZeta9 (q3kMul (q3kMul q27psT q27psT) q27psT)) :=
    q27ps_dvd_mul_left hT3 q3kZeta9
  have hB : q9wrDvd (q9nfPiPow 15)
      (q3kNeg (q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kMul (q3kMul q27psT q27psT) q27psT))) :=
    q27ps_dvd_neg (q27ps_dvd_mul_left hT3 (q3kMul q3kZeta9 q3kZeta9))
  have h3d : q9wrDvd (q9nfPiPow 6) q27kThree := ⟨q9psU6, q27ps_three_pi6_u6⟩
  have hzT2 : q9wrDvd (q9nfPiPow 10) (q3kMul q3kZeta9 (q3kMul q27psT q27psT)) :=
    q27ps_dvd_mul_left (q9nf_dvd_mul hT5 hT5) q3kZeta9
  have hC : q9wrDvd (q9nfPiPow 15)
      (q3kMul q27kThree (q3kMul q3kZeta9 (q3kMul q27psT q27psT))) :=
    q9nf_dvd_of_le (by omega) (q9nf_dvd_mul h3d hzT2)
  exact q9nf_dvd_add (q9nf_dvd_add hA hB) hC

/-- **q27ps-5c（★ 正直な差分の Lean 実現）: N(w̃) ∈ U^(15)**——N(w̃) = 1 + O(π₉¹⁵) の
    **主単数**であり、level-9 の綺麗な定数 N(w) = −1 に対応する閉じた定数形は無い。 -/
theorem q27ps_wt_norm_U15 : q9nfUfilt 15 (q27kNormBase q27psWt) := by
  show q9wrDvd (q9nfPiPow 15) (q3kAdd (q27kNormBase q27psWt) (q3kNeg q3kOne))
  rw [q27ps_wt_normBase, q9nf_one_add_cancel]
  exact q27ps_S_dvd15

/-! ## q27ps-6: 主単数論 U^(6) ⊆ O_{M₉}^×（w̃ の単数性を支える新しい実単数判定） -/

/-- x ∈ U^(6) ⟹ embed(N(x)) ∈ U^(6)（q9nf ノルム展開＋trace kill・graded 移送）。 -/
theorem q27ps_norm_ufilt6 {x : q3kCar} (hx : q9nfUfilt 6 x) :
    q9nfUfilt 6 (q3kEmbed (q3kNormBase x)) := by
  obtain ⟨a, ha⟩ := q9nf_ufilt_decomp hx
  show q9wrDvd (q9nfPiPow 6) (q3kAdd (q3kEmbed (q3kNormBase x)) (q3kNeg q3kOne))
  rw [ha, q9nf_norm_expand (q3kMul (q9nfPiPow 6) a), q9nf_one_add_cancel]
  refine q9nf_dvd_add ?_ (q9nf_dvd_add ?_ ?_)
  · exact q9nf_trace_kill (q3kMul (q9nfPiPow 6) a)
  · exact q9nf_dvd_of_le (by omega) (q9nf_e2_dvd 6 (q3kMul (q9nfPiPow 6) a) ⟨a, rfl⟩)
  · exact q9nf_dvd_of_le (by omega) (q9nf_normterm_dvd 6 (q3kMul (q9nfPiPow 6) a) ⟨a, rfl⟩)

/-- u₆⁻¹（実閉形式逆元・q3kInv 消費）。 -/
def q27psU6inv : q3kCar := q3kInv q9psU6 q9ps_u6_unit

/-- π₉⁶ = 3·u₆⁻¹（3 = π₉⁶u₆ の並べ替え）。 -/
theorem q27ps_pi6_factor : q9psPi6 = q3kMul (q3kEmbed q3rqThreeElt) q27psU6inv := by
  have hu : q3kMul q9psU6 q27psU6inv = q3kOne := q3k_inv_mul q9psU6 q9ps_u6_unit
  have h : q3kMul (q3kEmbed q3rqThreeElt) q27psU6inv = q9psPi6 := by
    rw [← q9ps_three_split, q3k_kM_eq, q3kRing.mul_assoc q9psPi6 q9psU6 q27psU6inv]
    rw [q3k_kM_eq, q9ps_kO_eq] at hu
    rw [hu, q3kRing.mul_one q9psPi6]
  exact h.symm

/-- embed 倍の第 0 成分 (embed(n)·v)₀ = n·v₀。 -/
theorem q27ps_embed_mul_fst (n : q3rqCar) (v : q3kCar) :
    (q3kMul (q3kEmbed n) v).1 = q3rqMul n v.1 := by
  show q3rqAdd (q3rqMul n v.1)
      (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero v.2.2) (q3rqMul q3rqZero v.2.1)))
    = q3rqMul n v.1
  rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq,
      q3rqRing.zero_mul v.2.2, q3rqRing.zero_mul v.2.1,
      q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
      q3rqRing.add_zero (q3rqRing.mul n v.1)]

/-- 1 + (n − 1) = n（O_{L₂}）。 -/
theorem q27ps_one_add_sub (n : q3rqCar) :
    q3rqAdd q3rqOne (q3rqAdd n (q3rqNeg q3rqOne)) = n := by
  rw [q3k_A_eq, q3k_N_eq, q9ps_1_eq,
      q3rqRing.add_comm n (q3rqRing.neg q3rqRing.one),
      ← q3rqRing.add_assoc q3rqRing.one (q3rqRing.neg q3rqRing.one) n,
      q3rqRing.add_neg q3rqRing.one, q3rqRing.zero_add n]

/-- **q27ps-6a（★ レベル 1 判定）: q3rqNorm(1 + 3r) は ℤ₃ 単数**
    （レベル 1 値 ≡ 1 mod 3・q3mc 機構消費・choice-free）。 -/
theorem q27ps_qnorm_one_add_three_unit (r : q3rqCar) :
    IsZpUnit 3 (q3rqNorm (q3rqAdd q3rqOne (q3rqMul q3rqThreeElt r))) := by
  obtain ⟨k1, hk1⟩ := Quot.exists_rep ((r.1).val 1)
  obtain ⟨k2, hk2⟩ := Quot.exists_rep ((r.2).val 1)
  have hz0 : z3.zero.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := rfl
  have h1v : z3.one.val 1 = Quot.mk (modCong (3 ^ 1)).rel 1 := rfl
  have ha : ((q3rqAdd q3rqOne (q3rqMul q3rqThreeElt r)).1).val 1
      = Quot.mk (modCong (3 ^ 1)).rel (1 + (3 * k1 + (-3) * (0 * k2))) :=
    q3mc_add_val1 z3.one
      (z3.add (z3.mul q3rqThree r.1) (z3.mul q3rqD (z3.mul z3.zero r.2)))
      1 (3 * k1 + (-3) * (0 * k2)) h1v
      (q3mc_add_val1 (z3.mul q3rqThree r.1) (z3.mul q3rqD (z3.mul z3.zero r.2))
        (3 * k1) ((-3) * (0 * k2))
        (q3mc_mul_val1 q3rqThree r.1 3 k1 (q3rq_three_val 1) hk1.symm)
        (q3mc_mul_val1 q3rqD (z3.mul z3.zero r.2) (-3) (0 * k2) q3rq_D_val1
          (q3mc_mul_val1 z3.zero r.2 0 k2 hz0 hk2.symm)))
  have hb : ((q3rqAdd q3rqOne (q3rqMul q3rqThreeElt r)).2).val 1
      = Quot.mk (modCong (3 ^ 1)).rel (0 + (3 * k2 + 0 * k1)) :=
    q3mc_add_val1 z3.zero
      (z3.add (z3.mul q3rqThree r.2) (z3.mul z3.zero r.1))
      0 (3 * k2 + 0 * k1) hz0
      (q3mc_add_val1 (z3.mul q3rqThree r.2) (z3.mul z3.zero r.1)
        (3 * k2) (0 * k1)
        (q3mc_mul_val1 q3rqThree r.2 3 k2 (q3rq_three_val 1) hk2.symm)
        (q3mc_mul_val1 z3.zero r.1 0 k1 hz0 hk1.symm))
  rw [Int.zero_mul, Int.mul_zero, Int.add_zero] at ha
  rw [Int.zero_mul, Int.add_zero, Int.zero_add] at hb
  refine ⟨(1 + 3 * k1) * (1 + 3 * k1) + -((-3) * ((3 * k2) * (3 * k2))), ?_, ?_⟩
  · exact q3mc_norm_lev1 ((q3rqAdd q3rqOne (q3rqMul q3rqThreeElt r)).1)
      ((q3rqAdd q3rqOne (q3rqMul q3rqThreeElt r)).2)
      (1 + 3 * k1) (3 * k2) ha hb
  · intro hd
    have hexp : ((1 : Int) + 3 * k1) * (1 + 3 * k1)
        = (1 + 3 * k1) + (3 * k1 * 1 + 3 * k1 * (3 * k1)) := by
      rw [Int.add_mul, Int.one_mul, Int.mul_add]
    have hassoc : (3 : Int) * k1 * (3 * k1) = 3 * (k1 * (3 * k1)) :=
      Int.mul_assoc 3 k1 (3 * k1)
    have hassoc2 : ((3 : Int) * k2) * (3 * k2) = 3 * (k2 * (3 * k2)) :=
      Int.mul_assoc 3 k2 (3 * k2)
    rw [hexp, hassoc, hassoc2] at hd
    obtain ⟨c, hc⟩ := hd
    omega

/-- **q27ps-6b（★★ 主単数は実単数）: U^(6) ⊆ O_{M₉}^×**——x ≡ 1 mod π₉⁶（= mod 3）なら
    x は実単数。ノルム 3 段降下（M₉→L₂→ℤ₃）＋レベル 1 判定。level-9 に無かった
    q27ps 局在の実単数論（scope §1.3 の「N(w̃)=主単数」ギャップを閉じる補題）。 -/
theorem q27ps_ufilt6_unit {x : q3kCar} (hx : q9nfUfilt 6 x) : q3kUnitMem x := by
  have hN := q27ps_norm_ufilt6 hx
  obtain ⟨c, hc⟩ := hN
  rw [q9nf_pipow6_eq, q27ps_pi6_factor, q3k_kM_eq,
      q3kRing.mul_assoc (q3kEmbed q3rqThreeElt) q27psU6inv c, ← q3k_kM_eq] at hc
  have h1 := congrArg (fun z : q3kCar => z.1) hc
  have h2 : q3rqAdd (q3kNormBase x) (q3rqNeg q3rqOne)
      = q3rqMul q3rqThreeElt ((q3kMul q27psU6inv c).1) := by
    rw [← q27ps_embed_mul_fst q3rqThreeElt (q3kMul q27psU6inv c)]
    exact h1
  have h3 : q3kNormBase x
      = q3rqAdd q3rqOne (q3rqMul q3rqThreeElt ((q3kMul q27psU6inv c).1)) := by
    rw [← h2]
    exact (q27ps_one_add_sub (q3kNormBase x)).symm
  show IsZpUnit 3 (q3rqNorm (q3kNormBase x))
  rw [h3]
  exact q27ps_qnorm_one_add_three_unit ((q3kMul q27psU6inv c).1)

/-! ## q27ps-7: w̃ の実単数性・w̃⁻¹・u₁₈ = w̃⁻⁶·u₆ -/

/-- **q27ps-7a（★）: w̃ は実単数**（N(w̃) ∈ U^(15) ⊆ U^(6) ⊆ O_{M₉}^×）。 -/
theorem q27ps_wt_unit : q27kUnitMem q27psWt := by
  show q3kUnitMem (q27kNormBase q27psWt)
  exact q27ps_ufilt6_unit (q9nf_ufilt_antitone (i := 6) (k := 9) q27ps_wt_norm_U15)

/-- w̃⁻¹（実閉形式相対ノルム逆元・q27kInv 消費）。 -/
def q27psWtInv : q27kCar := q27kInv q27psWt q27ps_wt_unit

/-- N_{M₂₇/M₉}(embed n) = n³。 -/
theorem q27ps_normBase_embed (n : q3kCar) :
    q27kNormBase (q27kEmbed n) = q3kMul (q3kMul n n) n := by
  show q3kAdd
      (q3kAdd
        (q3kAdd (q3kMul (q3kMul n n) n)
          (q3kMul q3kZeta9 (q3kMul (q3kMul q3kZero q3kZero) q3kZero)))
        (q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kMul (q3kMul q3kZero q3kZero) q3kZero)))
      (q3kNeg (q3kMul q27kThree (q3kMul q3kZeta9 (q3kMul (q3kMul n q3kZero) q3kZero))))
    = q3kMul (q3kMul n n) n
  rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq,
      q3kRing.mul_zero (q3kRing.mul q3kRing.zero q3kRing.zero),
      q3kRing.mul_zero q3kZeta9,
      q3kRing.mul_zero (q3kRing.mul q3kZeta9 q3kZeta9),
      q3kRing.mul_zero (q3kRing.mul n q3kRing.zero),
      q3kRing.mul_zero q3kZeta9, q3kRing.mul_zero q27kThree,
      q3kRing.neg_zero,
      q3kRing.add_zero (q3kRing.mul (q3kRing.mul n n) n),
      q3kRing.add_zero (q3kRing.mul (q3kRing.mul n n) n),
      q3kRing.add_zero (q3kRing.mul (q3kRing.mul n n) n)]

/-- embed は単数を保つ（N(embed n) = n³ が実単数）。 -/
theorem q27ps_embed_unit (n : q3kCar) (hn : q3kUnitMem n) :
    q27kUnitMem (q27kEmbed n) := by
  show q3kUnitMem (q27kNormBase (q27kEmbed n))
  rw [q27ps_normBase_embed]
  exact q3k_unit_mul (q3k_unit_mul hn hn) hn

/-- w̃⁻³ = ((w̃⁻¹w̃⁻¹)w̃⁻¹)。 -/
def q27psWtInv3 : q27kCar := q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv

/-- w̃⁻⁶ = w̃⁻³·w̃⁻³。 -/
def q27psWtInv6 : q27kCar := q27kMul q27psWtInv3 q27psWtInv3

/-- **q27ps-7b: u₁₈ := w̃⁻⁶·u₆**（実閉形式単数・§1.3）。 -/
def q27psU18 : q27kCar := q27kMul q27psWtInv6 (q27kEmbed q9psU6)

/-- **q27ps-7c: u₁₈ は実単数**（w̃⁻¹ 単数 ×6・embed(u₆) 単数）。 -/
theorem q27ps_u18_unit : q27kUnitMem q27psU18 := by
  have hV : q27kUnitMem q27psWtInv := q27k_unit_inv q27psWt q27ps_wt_unit
  have hV3 : q27kUnitMem q27psWtInv3 := q27k_unit_mul (q27k_unit_mul hV hV) hV
  have hV6 : q27kUnitMem q27psWtInv6 := q27k_unit_mul hV3 hV3
  exact q27k_unit_mul hV6 (q27ps_embed_unit q9psU6 q9ps_u6_unit)

/-! ## q27ps-8: ★★★ 要石 3 = π₂₇¹⁸·u₁₈ -/

/-- π₂₇⁹ = (π₂₇³·π₂₇³)·π₂₇³。 -/
def q27psPi27Pow9 : q27kCar :=
  q27kMul (q27kMul q27psPi27Cubed q27psPi27Cubed) q27psPi27Cubed

/-- π₂₇¹⁸ = π₂₇⁹·π₂₇⁹。 -/
def q27psPi18 : q27kCar := q27kMul q27psPi27Pow9 q27psPi27Pow9

/-- π₂₇⁹ = embed(π₉)³·w̃³（(Z−1)³ = embed(π₉)w̃ の 3 乗・因子分離）。 -/
theorem q27ps_pi27Pow9_eq :
    q27psPi27Pow9
      = q27kMul
          (q27kMul (q27kMul (q27kEmbed q9psPi9) (q27kEmbed q9psPi9)) (q27kEmbed q9psPi9))
          (q27kMul (q27kMul q27psWt q27psWt) q27psWt) := by
  show q27kMul (q27kMul q27psPi27Cubed q27psPi27Cubed) q27psPi27Cubed = _
  rw [q27ps_pi27_cube,
      q27ps_mmmc (q27kEmbed q9psPi9) q27psWt (q27kEmbed q9psPi9) q27psWt,
      q27ps_mmmc (q27kMul (q27kEmbed q9psPi9) (q27kEmbed q9psPi9))
        (q27kMul q27psWt q27psWt) (q27kEmbed q9psPi9) q27psWt]

/-- π₂₇¹⁸ = embed(π₉)⁶·w̃⁶（因子分離）。 -/
theorem q27ps_pi18_eq :
    q27psPi18
      = q27kMul
          (q27kMul
            (q27kMul (q27kMul (q27kEmbed q9psPi9) (q27kEmbed q9psPi9)) (q27kEmbed q9psPi9))
            (q27kMul (q27kMul (q27kEmbed q9psPi9) (q27kEmbed q9psPi9)) (q27kEmbed q9psPi9)))
          (q27kMul
            (q27kMul (q27kMul q27psWt q27psWt) q27psWt)
            (q27kMul (q27kMul q27psWt q27psWt) q27psWt)) := by
  show q27kMul q27psPi27Pow9 q27psPi27Pow9 = _
  rw [q27ps_pi27Pow9_eq,
      q27ps_mmmc
        (q27kMul (q27kMul (q27kEmbed q9psPi9) (q27kEmbed q9psPi9)) (q27kEmbed q9psPi9))
        (q27kMul (q27kMul q27psWt q27psWt) q27psWt)
        (q27kMul (q27kMul (q27kEmbed q9psPi9) (q27kEmbed q9psPi9)) (q27kEmbed q9psPi9))
        (q27kMul (q27kMul q27psWt q27psWt) q27psWt)]

/-- w̃⁶·w̃⁻⁶ = 1（因子入替で (w̃w̃⁻¹)⁶ に畳む）。 -/
theorem q27ps_wt6_inv6 :
    q27kMul
        (q27kMul (q27kMul (q27kMul q27psWt q27psWt) q27psWt)
          (q27kMul (q27kMul q27psWt q27psWt) q27psWt))
        (q27kMul (q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv)
          (q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv))
      = q27kOne := by
  have hWV : q27kMul q27psWt q27psWtInv = q27kOne :=
    q27k_inv_mul q27psWt q27ps_wt_unit
  rw [q27ps_mmmc (q27kMul (q27kMul q27psWt q27psWt) q27psWt)
        (q27kMul (q27kMul q27psWt q27psWt) q27psWt)
        (q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv)
        (q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv),
      q27ps_mmmc (q27kMul q27psWt q27psWt) q27psWt
        (q27kMul q27psWtInv q27psWtInv) q27psWtInv,
      q27ps_mmmc q27psWt q27psWt q27psWtInv q27psWtInv,
      hWV, q27k_one_mul q27kOne, q27k_one_mul q27kOne, q27k_one_mul q27kOne]

/-- **q27ps-8a（★★★ 要石）: 3 = π₂₇¹⁸·u₁₈**
    （3_{M₂₇} = embed(3_{M₉})・v_{M₂₇}(3) = 18 の代数的実現・§1.3）。 -/
theorem q27ps_three_split :
    q27kMul q27psPi18 q27psU18 = q27kEmbed q27kThree := by
  show q27kMul q27psPi18
      (q27kMul
        (q27kMul (q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv)
          (q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv))
        (q27kEmbed q9psU6))
    = q27kEmbed q27kThree
  rw [q27ps_pi18_eq,
      q27ps_massoc
        (q27kMul
          (q27kMul (q27kMul (q27kEmbed q9psPi9) (q27kEmbed q9psPi9)) (q27kEmbed q9psPi9))
          (q27kMul (q27kMul (q27kEmbed q9psPi9) (q27kEmbed q9psPi9)) (q27kEmbed q9psPi9)))
        (q27kMul
          (q27kMul (q27kMul q27psWt q27psWt) q27psWt)
          (q27kMul (q27kMul q27psWt q27psWt) q27psWt))
        (q27kMul
          (q27kMul (q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv)
            (q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv))
          (q27kEmbed q9psU6)),
      ← q27ps_massoc
        (q27kMul
          (q27kMul (q27kMul q27psWt q27psWt) q27psWt)
          (q27kMul (q27kMul q27psWt q27psWt) q27psWt))
        (q27kMul (q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv)
          (q27kMul (q27kMul q27psWtInv q27psWtInv) q27psWtInv))
        (q27kEmbed q9psU6),
      q27ps_wt6_inv6, q27k_one_mul (q27kEmbed q9psU6),
      q27k_embed_mul q9psPi9 q9psPi9,
      q27k_embed_mul (q3kMul q9psPi9 q9psPi9) q9psPi9,
      q27k_embed_mul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
        (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9),
      q27k_embed_mul
        (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
          (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)) q9psU6]
  show q27kEmbed (q3kMul q9psPi6 q9psU6) = q27kEmbed q27kThree
  rw [q9ps_three_split, q27ps_threeM]

/-- **q27ps-8b: 系（M₂₇ 内在形）**——1+1+1 = π₂₇¹⁸·u₁₈ in O_{M₂₇}。 -/
theorem q27ps_three_split_intrinsic :
    q27kMul q27psPi18 q27psU18 = q27kAdd q27kOne (q27kAdd q27kOne q27kOne) := by
  rw [q27ps_threeM27]
  exact q27ps_three_split

/-! ## q27ps-9: capstone -/

/-- **q27ps-9a: level-27 wild 分割データ** — π₂₇ = Z−1・w̃（N(w̃) ∈ U^(15) 主単数・
    実単数）・u₁₈ = w̃⁻⁶u₆・(Z−1)³ = embed(π₉)·w̃・恒等式 3 = π₂₇¹⁸·u₁₈。
    v_{M₂₇}(3) = 18 は恒等式の指数 18 として代数的にのみ実現（付値論は範囲外）。 -/
structure Q3KummerNonicSplitData where
  /-- 一様化子 π₂₇ = ζ₂₇ − 1 = Z − 1（e=18 wild・代数段）。 -/
  pi27 : q27kCar
  /-- 主単数 w̃ = 1 + π₉⁵u₆·Z − π₉⁵u₆·Z²。 -/
  wt : q27kCar
  /-- u₁₈ = w̃⁻⁶·u₆。 -/
  u18 : q27kCar
  /-- (Z−1)³ = π₉ + 3Z − 3Z²（閉形式・座標 (π₉, 3, −3)）。 -/
  pi27_cubed : q27kMul (q27kMul pi27 pi27) pi27
    = ((q9psPi9, q27kThree, q3kNeg q27kThree) : q27kCar)
  /-- (Z−1)³ = embed(π₉)·w̃（π₉ 括り出し）。 -/
  pi27_cube : q27kMul (q27kMul pi27 pi27) pi27 = q27kMul (q27kEmbed q9psPi9) wt
  /-- N(w̃) ∈ U^(15)（正直な差分: 主単数 1+O(π₉¹⁵)・level-9 の N(w)=−1 は無い）。 -/
  wt_norm_principal : q9nfUfilt 15 (q27kNormBase wt)
  /-- w̃ は実単数。 -/
  wt_unit : q27kUnitMem wt
  /-- u₁₈ は実単数。 -/
  u18_unit : q27kUnitMem u18
  /-- 3 = π₂₇¹⁸·u₁₈（要石・v_{M₂₇}(3)=18 の代数的実現）。 -/
  three_split :
    q27kMul
      (q27kMul
        (q27kMul (q27kMul (q27kMul (q27kMul pi27 pi27) pi27)
            (q27kMul (q27kMul pi27 pi27) pi27))
          (q27kMul (q27kMul pi27 pi27) pi27))
        (q27kMul (q27kMul (q27kMul (q27kMul pi27 pi27) pi27)
            (q27kMul (q27kMul pi27 pi27) pi27))
          (q27kMul (q27kMul pi27 pi27) pi27)))
      u18
    = q27kEmbed q27kThree

/-- **q27ps-9b: 見出し実例** — 実 M₂₇ = q27k 上の wild 分割 3 = π₂₇¹⁸·u₁₈。 -/
def q27psData : Q3KummerNonicSplitData where
  pi27 := q27psPi27
  wt := q27psWt
  u18 := q27psU18
  pi27_cubed := q27ps_pi27_cubed_eq
  pi27_cube := q27ps_pi27_cube
  wt_norm_principal := q27ps_wt_norm_U15
  wt_unit := q27ps_wt_unit
  u18_unit := q27ps_u18_unit
  three_split := q27ps_three_split

/-- **q27ps-9c: wild 分割の存在**（実 M₂₇ = q27k 上・実単数 u₁₈ = 閉形式）。 -/
theorem q27ps_exists : Nonempty Q3KummerNonicSplitData := ⟨q27psData⟩

end IUT
