/-
  IUT/Q3KummerPiSplit.lean — F-wild level-9 テータ kill / wild 分割の忠実性要石
    （実巡回 3 次 Kummer 代数 M = q3k 上の分割恒等式 3 = π₉⁶·u₆）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**（骨格・模型・代理でなく、q3k で建てた
     実 O_M = L₂[Y]/(Y³−ζ₃) の上に、level-9 テータ kill が消費する **wild 分割恒等式**
     3 = π₉⁶·u₆ をゼロから割る。π₉ = ζ₉−1 = Y−1（e=6 wild 一様化子）・λ = √−3・
     w = (ζ₃+1) − λY + λY²（N(w) = −1 の実単数）・u₆ = −(w⁻¹)² を**実 q3k/q3rq の元**
     として構成し、3_M = q3kEmbed(3) = −λ² = π₉⁶·u₆ を実数体上で証明する。toy 主語なし
     ——主語は実 q3k/q3rq（m202fVol 型・Bool 軌道・surrogate 群を一切使わない）。
     これにより群提示 M^× = ℤ(v_π) × U₃ の元 3 の単数部 u₆ が**本物の閉形式単数**であり、
     "3 := (6, 任意単数)" の模型に落ちない——[実] 分類の生命線。）

  complete_pct 影響: **0 前進（level-9 kill の忠実性要石・foundation）**。本モジュール単体は
  何も kill せず（分割恒等式のみ）、kill 本体は後続 q9mt/q9mr/q9mb。「complete_pct 0 前進
  （骨格でなく本物基盤の先行建設）」と正直申告する。

  内容（§2.2 of audit/level9-theta-kill-detail-2026-07-11.md）:
   * q9psPi9 := Y−1（=(−1,1,0)）・q9psW := (ζ₃+1, −λ, λ)
   * q9ps_pi9_cube — (Y−1)³ = λ·w（q9ci_cube_0/1/2 消費 + 座標計算）
   * q9ps_w_norm — N(w) = −1（実単数）・q9ps_w_unit
   * q9psWinv = w⁻¹・q9psU6 = −(w⁻¹)²・q9ps_u6_unit
   * q9ps_three_split（★ 要石）— 3_M = π₉⁶·u₆・q9ps_three_eq_pi6_u6
   * Q3KummerPiSplitData / q9ps_data / q9ps_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・q3k/q9ci 継承の上に追記のみ）:
  1. **代数的分割レベルのみ**（付値論・位相なし）。e=6 wild 分岐は「3 = π₉⁶·u₆ の
     代数恒等式」として実現するが、v_π(3)=6 の付値理論・M の完備化は範囲外。
  2. **本ファイルは何も kill しない**（要石・foundation のみ）。テータ群・μ₉ 完全性・
     剛性・橋は後続モジュール。
  3. q3k/q9ci の正直限定を全継承（O_M と M^× のみ・体化なし・σ を超える Galois ゼロ・
     実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3KummerCubeIdent

namespace IUT

/-! ## q9ps-0: 局所ブリッジ（q3k 演算 ↔ q3kRing 演算・q3rq の one 橋） -/

/-- q3kNeg = q3kRing.neg（構造体フィールド・rfl）。 -/
theorem q9ps_kN_eq : q3kNeg = q3kRing.neg := rfl

/-- q3rqOne = q3rqRing.one（rfl）。 -/
theorem q9ps_1_eq : q3rqOne = q3rqRing.one := rfl

/-- q3kOne = q3kRing.one（rfl）。 -/
theorem q9ps_kO_eq : q3kOne = q3kRing.one := rfl

/-! ## q9ps-1: q3rq レベルの円分・λ 補題（q3rqRing 形・名前付き消費） -/

/-- ζ·ζ² = 1（q3rqRing 形）。 -/
theorem q9ps_zzs' : q3rqRing.mul q3rqZeta q3rqZetaSq = q3rqRing.one := q3rq_zeta_mul_zetaSq
/-- ζ²·ζ² = ζ（q3rqRing 形）。 -/
theorem q9ps_zszs' : q3rqRing.mul q3rqZetaSq q3rqZetaSq = q3rqZeta := q3rq_zetaSq_mul_zetaSq

/-- **ζ₃+1 = −ζ₃²**（1+ζ₃+ζ₃²=0 の並べ替え）。 -/
theorem q9ps_zeta_add_one :
    q3rqRing.add q3rqZeta q3rqRing.one = q3rqRing.neg q3rqZetaSq := by
  have hsum : q3rqRing.add q3rqOne (q3rqRing.add q3rqZeta q3rqZetaSq) = q3rqRing.zero :=
    q3k_zeta_sum_zero
  rw [← q3rqRing.add_assoc, q3rqRing.add_comm q3rqOne q3rqZeta] at hsum
  have h0 := q3rqRing.neg_eq_of_add_eq_zero hsum
  have h1 := congrArg q3rqRing.neg h0
  rw [q3rqRing.neg_neg] at h1
  exact h1

/-- **λ² = −3**（q3rqRing 形・分岐 e=2）。 -/
theorem q9ps_lamsq' :
    q3rqRing.mul q3rqLambda q3rqLambda = q3rqRing.neg q3rqThreeElt := by
  have h : q3rqRing.mul q3rqLambda q3rqLambda = ((z3.neg q3rqThree, z3.zero) : q3rqCar) :=
    q3rq_lambda_sq
  rw [h]
  apply q3rq_ext
  · rfl
  · exact (z3.neg_zero).symm

/-- **ζ₃²−ζ₃ = −λ**（実円分。ζ₃−ζ₃² = √−3 = λ の反数）。 -/
theorem q9ps_zeta2_sub :
    q3rqRing.add (q3rqRing.neg q3rqZeta) q3rqZetaSq = q3rqRing.neg q3rqLambda := by
  have hzsq : q3rqZetaSq = ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar) :=
    q3rq_zeta_sq_eq
  rw [hzsq]
  apply q3rq_ext
  · show z3.add (z3.neg (z3.neg q3rqHalf)) (z3.neg q3rqHalf) = z3.neg z3.zero
    rw [z3.neg_neg, z3.add_neg, z3.neg_zero]
  · show z3.add (z3.neg q3rqHalf) (z3.neg q3rqHalf) = z3.neg z3.one
    rw [← z3.neg_add_dist q3rqHalf q3rqHalf, q3rq_half_add_half]

/-- 3 = (1+1)+1（q3kThree）= q3rqThreeElt。 -/
theorem q9ps_three_eq : q3kThree = q3rqThreeElt := by
  show q3rqAdd q3rqOne (q3rqAdd q3rqOne q3rqOne) = q3rqThreeElt
  rw [q3k_A_eq, ← q3rqRing.add_assoc]
  exact q9ci_three_pair

/-- 9 = 3·3 ∈ O_{L₂}。 -/
def q9psNine : q3rqCar := q3rqRing.mul q3rqThreeElt q3rqThreeElt

/-! ## q9ps-2: π₉ = Y−1 と w = (ζ₃+1, −λ, λ) -/

/-- **q9ps-2a: π₉ = ζ₉ − 1 = Y − 1**（e=6 wild 一様化子）。 -/
def q9psPi9 : q3kCar := q3kAdd q3kZeta9 (q3kNeg q3kOne)

/-- π₉ の座標形 (−1, 1, 0)。 -/
theorem q9ps_pi9_coords :
    q9psPi9 = ((q3rqNeg q3rqOne, q3rqOne, q3rqZero) : q3kCar) := by
  apply q3k_ext
  · show q3rqAdd q3rqZero (q3rqNeg q3rqOne) = q3rqNeg q3rqOne
    rw [q3k_A_eq]; exact q3rqRing.zero_add (q3rqNeg q3rqOne)
  · show q3rqAdd q3rqOne (q3rqNeg q3rqZero) = q3rqOne
    rw [q3k_A_eq, q3k_N_eq, q3k_Z_eq, q3rqRing.neg_zero, q3rqRing.add_zero]
  · show q3rqAdd q3rqZero (q3rqNeg q3rqZero) = q3rqZero
    rw [q3k_A_eq, q3k_N_eq, q3k_Z_eq, q3rqRing.neg_zero, q3rqRing.add_zero]

/-- **q9ps-2b: w = (ζ₃+1) − λY + λY²**（座標 (ζ₃+1, −λ, λ)）。 -/
def q9psW : q3kCar :=
  ((q3rqAdd q3rqZeta q3rqOne, q3rqNeg q3rqLambda, q3rqLambda) : q3kCar)

/-! ## q9ps-3: 立方 (Y−1)³ の座標簡約補題（q9ci_cube を x=(−1,1,0) で消費） -/

/-- (−1)³ = −1。 -/
theorem q9ps_neg1_cube :
    q3rqRing.mul (q3rqRing.mul (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqRing.one))
      (q3rqRing.neg q3rqRing.one) = q3rqRing.neg q3rqRing.one := by
  rw [q3rqRing.neg_mul q3rqRing.one (q3rqRing.neg q3rqRing.one),
      q3rqRing.one_mul (q3rqRing.neg q3rqRing.one), q3rqRing.neg_neg,
      q3rqRing.one_mul (q3rqRing.neg q3rqRing.one)]

/-- coord0 の項 b: ζ₃·(1³) = ζ₃。 -/
theorem q9ps_c0b :
    q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul q3rqRing.one q3rqRing.one) q3rqRing.one)
      = q3rqZeta := by
  rw [q3rqRing.one_mul q3rqRing.one, q3rqRing.one_mul q3rqRing.one, q3rqRing.mul_one q3rqZeta]

/-- coord0 の項 c: ζ₃²·(0³) = 0。 -/
theorem q9ps_c0c :
    q3rqRing.mul q3rqZetaSq (q3rqRing.mul (q3rqRing.mul q3rqRing.zero q3rqRing.zero) q3rqRing.zero)
      = q3rqRing.zero := by
  rw [q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_zero q3rqRing.zero,
      q3rqRing.mul_zero q3rqZetaSq]

/-- coord0 の 6ζabc 項 T6: ζ₃·((−1)·(1·0)) = 0。 -/
theorem q9ps_c0t6 :
    q3rqRing.mul q3rqZeta
        (q3rqRing.mul (q3rqRing.neg q3rqRing.one) (q3rqRing.mul q3rqRing.one q3rqRing.zero))
      = q3rqRing.zero := by
  rw [q3rqRing.mul_zero q3rqRing.one, q3rqRing.mul_zero (q3rqRing.neg q3rqRing.one),
      q3rqRing.mul_zero q3rqZeta]

/-- **coord0 のキー恒等式**: λ·(ζ₃+1) = −1 + ζ₃（= ζ₃−1）。 -/
theorem q9ps_coord0 :
    q3rqRing.mul q3rqLambda (q3rqRing.add q3rqZeta q3rqRing.one)
      = q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZeta := by
  apply q3rq_ext
  · -- .1: −3·h = −1 + (−h)
    show z3.add (z3.mul z3.zero (z3.add (z3.neg q3rqHalf) z3.one))
          (z3.mul q3rqD (z3.mul z3.one (z3.add q3rqHalf z3.zero)))
        = z3.add (z3.neg z3.one) (z3.neg q3rqHalf)
    rw [z3.zero_mul (z3.add (z3.neg q3rqHalf) z3.one), z3.zero_add,
        z3.one_mul (z3.add q3rqHalf z3.zero), z3.add_zero q3rqHalf,
        q3rq_D_eq, z3.neg_mul q3rqThree q3rqHalf]
    -- goal: z3.neg (z3.mul q3rqThree q3rqHalf) = z3.add (z3.neg z3.one) (z3.neg q3rqHalf)
    have h3h : z3.mul q3rqThree q3rqHalf = z3.add z3.one q3rqHalf := by
      show z3.mul (z3.add q3rqTwoZ z3.one) q3rqHalf = z3.add z3.one q3rqHalf
      rw [z3.right_distrib q3rqTwoZ z3.one q3rqHalf, q3rq_two_half, z3.one_mul q3rqHalf]
    rw [h3h, z3.neg_add_dist z3.one q3rqHalf]
  · -- .2: −h + 1 = h
    show z3.add (z3.mul z3.zero (z3.add q3rqHalf z3.zero))
          (z3.mul z3.one (z3.add (z3.neg q3rqHalf) z3.one))
        = z3.add (z3.neg z3.zero) q3rqHalf
    rw [z3.zero_mul (z3.add q3rqHalf z3.zero), z3.zero_add,
        z3.one_mul (z3.add (z3.neg q3rqHalf) z3.one),
        z3.neg_zero, z3.zero_add q3rqHalf,
        ← q3rq_half_add_half, ← z3.add_assoc, z3.neg_add, z3.zero_add]

/-- (−1)·(−1) = 1。 -/
theorem q9ps_neg1_sq :
    q3rqRing.mul (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqRing.one) = q3rqRing.one := by
  rw [q3rqRing.neg_mul q3rqRing.one (q3rqRing.neg q3rqRing.one),
      q3rqRing.one_mul (q3rqRing.neg q3rqRing.one), q3rqRing.neg_neg]

/-- coord1 の共通項 S₁ = a²b + ζac² + ζb²c = 1（a=−1,b=1,c=0）。 -/
theorem q9ps_S1 :
    q3rqRing.add
      (q3rqRing.add
        (q3rqRing.mul (q3rqRing.mul (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqRing.one)) q3rqRing.one)
        (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.neg q3rqRing.one) (q3rqRing.mul q3rqRing.zero q3rqRing.zero))))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul q3rqRing.one q3rqRing.one) q3rqRing.zero))
      = q3rqRing.one := by
  rw [q3rqRing.mul_one (q3rqRing.mul (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqRing.one)),
      q9ps_neg1_sq,
      q3rqRing.mul_zero q3rqRing.zero,
      q3rqRing.mul_zero (q3rqRing.neg q3rqRing.one),
      q3rqRing.mul_zero (q3rqRing.mul q3rqRing.one q3rqRing.one),
      q3rqRing.mul_zero q3rqZeta,
      q3rqRing.add_zero, q3rqRing.add_zero]

/-- coord2 の共通項 S₂ = a²c + ab² + ζbc² = −1（a=−1,b=1,c=0）。 -/
theorem q9ps_S2 :
    q3rqRing.add
      (q3rqRing.add
        (q3rqRing.mul (q3rqRing.mul (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqRing.one)) q3rqRing.zero)
        (q3rqRing.mul (q3rqRing.neg q3rqRing.one) (q3rqRing.mul q3rqRing.one q3rqRing.one)))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqRing.one (q3rqRing.mul q3rqRing.zero q3rqRing.zero)))
      = q3rqRing.neg q3rqRing.one := by
  rw [q3rqRing.mul_zero (q3rqRing.mul (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqRing.one)),
      q3rqRing.one_mul q3rqRing.one,
      q3rqRing.mul_one (q3rqRing.neg q3rqRing.one),
      q3rqRing.mul_zero q3rqRing.zero,
      q3rqRing.mul_zero q3rqRing.one,
      q3rqRing.mul_zero q3rqZeta,
      q3rqRing.add_zero, q3rqRing.zero_add]

/-! ## q9ps-4: 立方分割恒等式 (Y−1)³ = λ·w -/

/-- **q9ps-4a（★）: (Y−1)³ = λ·w**（q9ci_cube_0/1/2 を x=(−1,1,0) で消費）。 -/
theorem q9ps_pi9_cube :
    q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9 = q3kMul (q3kEmbed q3rqLambda) q9psW := by
  rw [q9ps_pi9_coords]
  apply q3k_ext
  · -- coord 0
    rw [q9ci_cube_0 ((q3rqNeg q3rqOne, q3rqOne, q3rqZero) : q3kCar),
        q3kMul_0 (q3kEmbed q3rqLambda) q9psW]
    show q3rqAdd
        (q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne)) (q3rqNeg q3rqOne))
            (q3rqMul q3rqZeta (q3rqMul (q3rqMul q3rqOne q3rqOne) q3rqOne)))
          (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul q3rqZero q3rqZero) q3rqZero)))
        (q3rqAdd
          (q3rqAdd
            (q3rqAdd
              (q3rqAdd
                (q3rqAdd (q3rqMul q3rqZeta (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqOne q3rqZero)))
                         (q3rqMul q3rqZeta (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqOne q3rqZero))))
                (q3rqMul q3rqZeta (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqOne q3rqZero))))
              (q3rqMul q3rqZeta (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqOne q3rqZero))))
            (q3rqMul q3rqZeta (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqOne q3rqZero))))
          (q3rqMul q3rqZeta (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqOne q3rqZero))))
      = q3rqAdd (q3rqMul q3rqLambda (q3rqAdd q3rqZeta q3rqOne))
          (q3rqMul q3rqZeta
            (q3rqAdd (q3rqMul q3rqZero q3rqLambda) (q3rqMul q3rqZero (q3rqNeg q3rqLambda))))
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q3k_Z_eq, q9ps_1_eq]
    rw [q9ps_neg1_cube, q9ps_c0b, q9ps_c0c, q9ps_c0t6,
        q3rqRing.zero_mul q3rqLambda, q3rqRing.zero_mul (q3rqRing.neg q3rqLambda),
        q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero, q3rqRing.add_zero, q3rqRing.add_zero, q3rqRing.add_zero,
        q3rqRing.add_zero, q3rqRing.add_zero, q3rqRing.add_zero]
    exact q9ps_coord0.symm
  · -- coord 1
    rw [q9ci_cube_1 ((q3rqNeg q3rqOne, q3rqOne, q3rqZero) : q3kCar),
        q3kMul_1 (q3kEmbed q3rqLambda) q9psW]
    show q3rqAdd
        (q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne)) q3rqOne)
            (q3rqMul q3rqZeta (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqZero q3rqZero))))
          (q3rqMul q3rqZeta (q3rqMul (q3rqMul q3rqOne q3rqOne) q3rqZero)))
        (q3rqAdd
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne)) q3rqOne)
              (q3rqMul q3rqZeta (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqZero q3rqZero))))
            (q3rqMul q3rqZeta (q3rqMul (q3rqMul q3rqOne q3rqOne) q3rqZero)))
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne)) q3rqOne)
              (q3rqMul q3rqZeta (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqZero q3rqZero))))
            (q3rqMul q3rqZeta (q3rqMul (q3rqMul q3rqOne q3rqOne) q3rqZero))))
      = q3rqAdd
          (q3rqAdd (q3rqMul q3rqLambda (q3rqNeg q3rqLambda))
            (q3rqMul q3rqZero (q3rqAdd q3rqZeta q3rqOne)))
          (q3rqMul q3rqZeta (q3rqMul q3rqZero q3rqLambda))
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q3k_Z_eq, q9ps_1_eq]
    rw [q9ps_S1,
        q3rqRing.mul_neg q3rqLambda q3rqLambda, q9ps_lamsq', q3rqRing.neg_neg,
        q3rqRing.zero_mul (q3rqRing.add q3rqZeta q3rqRing.one),
        q3rqRing.zero_mul q3rqLambda, q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero, q3rqRing.add_zero]
    exact q9ps_three_eq
  · -- coord 2
    rw [q9ci_cube_2 ((q3rqNeg q3rqOne, q3rqOne, q3rqZero) : q3kCar),
        q3kMul_2 (q3kEmbed q3rqLambda) q9psW]
    show q3rqAdd
        (q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne)) q3rqZero)
            (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqOne q3rqOne)))
          (q3rqMul q3rqZeta (q3rqMul q3rqOne (q3rqMul q3rqZero q3rqZero))))
        (q3rqAdd
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne)) q3rqZero)
              (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqOne q3rqOne)))
            (q3rqMul q3rqZeta (q3rqMul q3rqOne (q3rqMul q3rqZero q3rqZero))))
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne)) q3rqZero)
              (q3rqMul (q3rqNeg q3rqOne) (q3rqMul q3rqOne q3rqOne)))
            (q3rqMul q3rqZeta (q3rqMul q3rqOne (q3rqMul q3rqZero q3rqZero)))))
      = q3rqAdd
          (q3rqAdd (q3rqMul q3rqLambda q3rqLambda)
            (q3rqMul q3rqZero (q3rqNeg q3rqLambda)))
          (q3rqMul q3rqZero (q3rqAdd q3rqZeta q3rqOne))
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q3k_Z_eq, q9ps_1_eq]
    rw [q9ps_S2, q9ps_lamsq',
        q3rqRing.zero_mul (q3rqRing.neg q3rqLambda),
        q3rqRing.zero_mul (q3rqRing.add q3rqZeta q3rqRing.one),
        q3rqRing.add_zero, q3rqRing.add_zero,
        ← q3rqRing.neg_add_dist q3rqRing.one q3rqRing.one,
        ← q3rqRing.neg_add_dist q3rqRing.one (q3rqRing.add q3rqRing.one q3rqRing.one)]
    exact congrArg q3rqRing.neg q9ps_three_eq

/-! ## q9ps-5: 実ノルム N(w) = −1（単数） -/

/-- **q9ps-5a（★）: N(w) = −1**（実単数。a³+ζb³+ζ²c³−3ζabc を (ζ₃+1,−λ,λ) で計算）。 -/
theorem q9ps_w_norm : q3kNormBase q9psW = q3rqNeg q3rqOne := by
  show q3rqAdd
      (q3rqAdd
        (q3rqAdd (q3rqMul (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne)) (q3rqAdd q3rqZeta q3rqOne))
          (q3rqMul q3rqZeta (q3rqMul (q3rqMul (q3rqNeg q3rqLambda) (q3rqNeg q3rqLambda)) (q3rqNeg q3rqLambda))))
        (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul q3rqLambda q3rqLambda) q3rqLambda)))
      (q3rqNeg (q3rqMul q3kThree (q3rqMul q3rqZeta (q3rqMul (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqNeg q3rqLambda)) q3rqLambda))))
    = q3rqNeg q3rqOne
  rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq]
  -- W0 = add ζ 1, W1 = neg λ, W2 = λ
  have hA : q3rqRing.mul (q3rqRing.mul (q3rqRing.add q3rqZeta q3rqRing.one) (q3rqRing.add q3rqZeta q3rqRing.one))
        (q3rqRing.add q3rqZeta q3rqRing.one) = q3rqRing.neg q3rqRing.one := by
    rw [q9ps_zeta_add_one,
        q3rqRing.neg_mul q3rqZetaSq (q3rqRing.neg q3rqZetaSq),
        q3rqRing.mul_neg q3rqZetaSq q3rqZetaSq, q3rqRing.neg_neg,
        q3rqRing.mul_neg (q3rqRing.mul q3rqZetaSq q3rqZetaSq) q3rqZetaSq,
        q9ps_zszs', q9ps_zzs']
  have hBC : q3rqRing.add
        (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul (q3rqRing.neg q3rqLambda) (q3rqRing.neg q3rqLambda)) (q3rqRing.neg q3rqLambda)))
        (q3rqRing.mul q3rqZetaSq (q3rqRing.mul (q3rqRing.mul q3rqLambda q3rqLambda) q3rqLambda))
      = q3rqRing.neg (q3rqRing.mul q3rqThreeElt q3rqThreeElt) := by
    rw [q3rqRing.neg_mul q3rqLambda (q3rqRing.neg q3rqLambda),
        q3rqRing.mul_neg q3rqLambda q3rqLambda, q3rqRing.neg_neg,
        q3rqRing.mul_neg (q3rqRing.mul q3rqLambda q3rqLambda) q3rqLambda,
        q3rqRing.mul_neg q3rqZeta (q3rqRing.mul (q3rqRing.mul q3rqLambda q3rqLambda) q3rqLambda),
        ← q3rqRing.neg_mul q3rqZeta (q3rqRing.mul (q3rqRing.mul q3rqLambda q3rqLambda) q3rqLambda),
        ← q3rqRing.right_distrib (q3rqRing.neg q3rqZeta) q3rqZetaSq (q3rqRing.mul (q3rqRing.mul q3rqLambda q3rqLambda) q3rqLambda),
        q9ps_zeta2_sub,
        q3rqRing.neg_mul q3rqLambda (q3rqRing.mul (q3rqRing.mul q3rqLambda q3rqLambda) q3rqLambda),
        q3rqRing.mul_assoc q3rqLambda q3rqLambda q3rqLambda,
        ← q3rqRing.mul_assoc q3rqLambda q3rqLambda (q3rqRing.mul q3rqLambda q3rqLambda),
        q9ps_lamsq',
        q3rqRing.neg_mul q3rqThreeElt (q3rqRing.neg q3rqThreeElt),
        q3rqRing.mul_neg q3rqThreeElt q3rqThreeElt, q3rqRing.neg_neg]
  have hD : q3rqRing.mul q3kThree
        (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul (q3rqRing.add q3rqZeta q3rqRing.one) (q3rqRing.neg q3rqLambda)) q3rqLambda))
      = q3rqRing.neg (q3rqRing.mul q3rqThreeElt q3rqThreeElt) := by
    rw [q9ps_zeta_add_one,
        q3rqRing.neg_mul q3rqZetaSq (q3rqRing.neg q3rqLambda),
        q3rqRing.mul_neg q3rqZetaSq q3rqLambda, q3rqRing.neg_neg,
        q3rqRing.mul_assoc q3rqZetaSq q3rqLambda q3rqLambda,
        ← q3rqRing.mul_assoc q3rqZeta q3rqZetaSq (q3rqRing.mul q3rqLambda q3rqLambda),
        q9ps_zzs', q3rqRing.one_mul (q3rqRing.mul q3rqLambda q3rqLambda),
        q9ps_three_eq, q9ps_lamsq',
        q3rqRing.mul_neg q3rqThreeElt q3rqThreeElt]
  rw [q3rqRing.add_assoc
        (q3rqRing.mul (q3rqRing.mul (q3rqRing.add q3rqZeta q3rqRing.one) (q3rqRing.add q3rqZeta q3rqRing.one)) (q3rqRing.add q3rqZeta q3rqRing.one))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul (q3rqRing.neg q3rqLambda) (q3rqRing.neg q3rqLambda)) (q3rqRing.neg q3rqLambda)))
        (q3rqRing.mul q3rqZetaSq (q3rqRing.mul (q3rqRing.mul q3rqLambda q3rqLambda) q3rqLambda)),
      hA, hBC, hD, q3rqRing.neg_neg,
      q3rqRing.add_assoc (q3rqRing.neg q3rqRing.one) (q3rqRing.neg (q3rqRing.mul q3rqThreeElt q3rqThreeElt)) (q3rqRing.mul q3rqThreeElt q3rqThreeElt),
      q3rqRing.neg_add (q3rqRing.mul q3rqThreeElt q3rqThreeElt), q3rqRing.add_zero]

/-- N(−1) = 1 の z3 計算。 -/
theorem q9ps_norm_neg_one : q3rqNorm (q3rqNeg q3rqOne) = z3.one := by
  show z3.add (z3.mul (z3.neg z3.one) (z3.neg z3.one))
      (z3.neg (z3.mul q3rqD (z3.mul (z3.neg z3.zero) (z3.neg z3.zero)))) = z3.one
  rw [z3.neg_mul z3.one (z3.neg z3.one), z3.one_mul (z3.neg z3.one), z3.neg_neg,
      z3.neg_zero, z3.mul_zero z3.zero, z3.mul_zero q3rqD, z3.neg_zero, z3.add_zero]

/-- **q9ps-5b: w は単数**（N(w)=−1 は ℤ₃^× の元）。 -/
theorem q9ps_w_unit : q3kUnitMem q9psW := by
  show q3rqUnitMem (q3kNormBase q9psW)
  rw [q9ps_w_norm]
  show IsZpUnit 3 (q3rqNorm (q3rqNeg q3rqOne))
  rw [q9ps_norm_neg_one]
  exact ⟨1, rfl, not_dvd_one 3 (by omega)⟩

/-! ## q9ps-6: w⁻¹ と u₆ = −(w⁻¹)² -/

/-- **q9ps-6a: w⁻¹**（閉形式 3 次ノルム逆元）。 -/
def q9psWinv : q3kCar := q3kInv q9psW q9ps_w_unit

/-- w·w⁻¹ = 1。 -/
theorem q9ps_w_inv_mul : q3kMul q9psW q9psWinv = q3kOne :=
  q3k_inv_mul q9psW q9ps_w_unit

/-- embed の反数整合 −embed(n) = embed(−n)。 -/
theorem q9ps_embed_neg (n : q3rqCar) :
    q3kRing.neg (q3kEmbed n) = q3kEmbed (q3rqNeg n) := by
  apply q3k_ext
  · rfl
  · show q3rqNeg q3rqZero = q3rqZero
    rw [q3k_N_eq, q3k_Z_eq, q3rqRing.neg_zero]
  · show q3rqNeg q3rqZero = q3rqZero
    rw [q3k_N_eq, q3k_Z_eq, q3rqRing.neg_zero]

/-- N の embed 版 N(embed n) = n³。 -/
theorem q9ps_normBase_embed (n : q3rqCar) :
    q3kNormBase (q3kEmbed n) = q3rqMul (q3rqMul n n) n := by
  show q3rqAdd
      (q3rqAdd
        (q3rqAdd (q3rqMul (q3rqMul n n) n)
          (q3rqMul q3rqZeta (q3rqMul (q3rqMul q3rqZero q3rqZero) q3rqZero)))
        (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul q3rqZero q3rqZero) q3rqZero)))
      (q3rqNeg (q3rqMul q3kThree (q3rqMul q3rqZeta (q3rqMul (q3rqMul n q3rqZero) q3rqZero))))
    = q3rqMul (q3rqMul n n) n
  rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q3k_Z_eq,
      q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_zero q3rqRing.zero,
      q3rqRing.mul_zero n, q3rqRing.mul_zero q3rqRing.zero,
      q3rqRing.mul_zero q3rqZeta, q3rqRing.mul_zero q3rqZetaSq,
      q3rqRing.mul_zero q3kThree, q3rqRing.neg_zero,
      q3rqRing.add_zero, q3rqRing.add_zero, q3rqRing.add_zero]

/-- −1 = q3kNeg q3kOne = embed(−1)。 -/
theorem q9ps_n1_embed : q3kNeg q3kOne = q3kEmbed (q3rqNeg q3rqOne) := by
  apply q3k_ext
  · rfl
  · show q3rqNeg q3rqZero = q3rqZero
    rw [q3k_N_eq, q3k_Z_eq, q3rqRing.neg_zero]
  · show q3rqNeg q3rqZero = q3rqZero
    rw [q3k_N_eq, q3k_Z_eq, q3rqRing.neg_zero]

/-- N(−1_M) = −1。 -/
theorem q9ps_neg_one_normBase : q3kNormBase (q3kNeg q3kOne) = q3rqNeg q3rqOne := by
  rw [q9ps_n1_embed, q9ps_normBase_embed, q3k_M_eq]
  exact q9ps_neg1_cube

/-- **−1_M は単数**。 -/
theorem q9ps_neg_one_unit : q3kUnitMem (q3kNeg q3kOne) := by
  show q3rqUnitMem (q3kNormBase (q3kNeg q3kOne))
  rw [q9ps_neg_one_normBase]
  show IsZpUnit 3 (q3rqNorm (q3rqNeg q3rqOne))
  rw [q9ps_norm_neg_one]
  exact ⟨1, rfl, not_dvd_one 3 (by omega)⟩

/-- −z = (−1)·z（環の反数＝−1 倍）。 -/
theorem q9ps_neg_one_mul (z : q3kCar) : q3kMul (q3kNeg q3kOne) z = q3kNeg z := by
  rw [q3k_kM_eq, q9ps_kN_eq, q3kRing.neg_mul q3kOne z, q9ps_kO_eq, q3kRing.one_mul z]

/-- **q9ps-6b: u₆ = −(w⁻¹)²**（実閉形式単数）。 -/
def q9psU6 : q3kCar := q3kNeg (q3kMul q9psWinv q9psWinv)

/-- **q9ps-6c: u₆ は単数**。 -/
theorem q9ps_u6_unit : q3kUnitMem q9psU6 := by
  show q3kUnitMem (q3kNeg (q3kMul q9psWinv q9psWinv))
  rw [← q9ps_neg_one_mul (q3kMul q9psWinv q9psWinv)]
  exact q3k_unit_mul q9ps_neg_one_unit
    (q3k_unit_mul (q3k_unit_inv q9psW q9ps_w_unit) (q3k_unit_inv q9psW q9ps_w_unit))

/-! ## q9ps-7: 要石 3 = π₉⁶·u₆ -/

/-- π₉³ = (Y−1)³。 -/
def q9psPi9Cubed : q3kCar := q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9

/-- π₉⁶ = (π₉³)²。 -/
def q9psPi6 : q3kCar := q3kMul q9psPi9Cubed q9psPi9Cubed

/-- L·L = embed(λ²)。 -/
theorem q9ps_LL :
    q3kRing.mul (q3kEmbed q3rqLambda) (q3kEmbed q3rqLambda)
      = q3kEmbed (q3rqMul q3rqLambda q3rqLambda) :=
  q3k_embed_mul q3rqLambda q3rqLambda

/-- **q9ps-7a（★★★ 要石）: 3_M = π₉⁶·u₆**（wild 分割・3_M = q3kEmbed(3)）。 -/
theorem q9ps_three_split :
    q3kMul q9psPi6 q9psU6 = q3kEmbed q3rqThreeElt := by
  show q3kMul (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
      (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)) (q3kNeg (q3kMul q9psWinv q9psWinv))
    = q3kEmbed q3rqThreeElt
  rw [q9ps_pi9_cube]
  rw [q3k_kM_eq, q9ps_kN_eq]
  have hwinv : q3kRing.mul q9psW q9psWinv = q3kOne := q9ps_w_inv_mul
  rw [q3kRing.mul_mul_mul_comm (q3kEmbed q3rqLambda) q9psW (q3kEmbed q3rqLambda) q9psW,
      q3kRing.mul_neg (q3kRing.mul (q3kRing.mul (q3kEmbed q3rqLambda) (q3kEmbed q3rqLambda))
        (q3kRing.mul q9psW q9psW)) (q3kRing.mul q9psWinv q9psWinv),
      q3kRing.mul_assoc (q3kRing.mul (q3kEmbed q3rqLambda) (q3kEmbed q3rqLambda))
        (q3kRing.mul q9psW q9psW) (q3kRing.mul q9psWinv q9psWinv),
      q3kRing.mul_mul_mul_comm q9psW q9psW q9psWinv q9psWinv,
      hwinv, q9ps_kO_eq, q3kRing.one_mul q3kRing.one,
      q3kRing.mul_one (q3kRing.mul (q3kEmbed q3rqLambda) (q3kEmbed q3rqLambda)),
      q9ps_LL, q9ps_embed_neg (q3rqMul q3rqLambda q3rqLambda),
      ← q3rq_three_eq_neg_lambda_sq]

/-- **q9ps-7b: 系（3 = π₉⁶·u₆ の正順）**。 -/
theorem q9ps_three_eq_pi6_u6 :
    q3kEmbed q3rqThreeElt = q3kMul q9psPi6 q9psU6 :=
  q9ps_three_split.symm

/-! ## q9ps-8: capstone -/

/-- **q9ps-8a: wild 分割データ** — π₉=Y−1・w（N(w)=−1）・w⁻¹・u₆・恒等式 3=π₉⁶·u₆。 -/
structure Q3KummerPiSplitData where
  /-- 一様化子 π₉ = ζ₉−1 = Y−1（e=6 wild）。 -/
  pi9 : q3kCar
  /-- 実単数 w = (ζ₃+1)−λY+λY²。 -/
  w : q3kCar
  /-- u₆ = −(w⁻¹)²。 -/
  u6 : q3kCar
  /-- (Y−1)³ = λ·w。 -/
  pi9_cube : q3kMul (q3kMul pi9 pi9) pi9 = q3kMul (q3kEmbed q3rqLambda) w
  /-- N(w) = −1（実単数）。 -/
  w_norm : q3kNormBase w = q3rqNeg q3rqOne
  /-- w は単数。 -/
  w_unit : q3kUnitMem w
  /-- u₆ は単数。 -/
  u6_unit : q3kUnitMem u6
  /-- 3_M = π₉⁶·u₆（要石）。 -/
  three_split : q3kMul (q3kMul (q3kMul (q3kMul pi9 pi9) pi9) (q3kMul (q3kMul pi9 pi9) pi9)) u6
    = q3kEmbed q3rqThreeElt

/-- **q9ps-8b: 見出し実例** — 実 M=q3k 上の wild 分割 3 = π₉⁶·u₆。 -/
def q9ps_data : Q3KummerPiSplitData where
  pi9 := q9psPi9
  w := q9psW
  u6 := q9psU6
  pi9_cube := q9ps_pi9_cube
  w_norm := q9ps_w_norm
  w_unit := q9ps_w_unit
  u6_unit := q9ps_u6_unit
  three_split := q9ps_three_split

/-- **q9ps-8c: wild 分割の存在**（実 M=q3k 上・実単数 u₆＝閉形式）。 -/
theorem q9ps_exists : Nonempty Q3KummerPiSplitData := ⟨q9ps_data⟩

end IUT
