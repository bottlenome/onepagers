/-
  IUT/Q3GradedNormBreak.lean — 柱B・B2 M2: level-6 graded ノルム公式と break の零性
    （B2 local-reciprocity crux「4 = 1+3 ∉ N_{M/L₂}(M^×)」への足場）

  ── 主要成果の分類: **[実／(c) 承認済み足場]**（named scaffolding）。
  B2 の真の crux「4 ∉ N」（audit/pillar-B2-level6-cokernel-detail-2026-07-11.md §2.3・§3 M2）
  へ向けた M2。実 O_M = q3kRing 上で、graded ノルム写像の **level-6/level-9 での零性**
  （§2.3 の打ち消し機構: Tr(π₉²a)+N(π₉²a) = 3[(π₉²a)₀−ζ₃N(a)] ∈ 3λO・Fermat a³≡a）を
  本物の実 π₉ 資産（q9rf 残余体・q9nf ノルム展開・q9ps wild 分割・q9wr 可除性）で建てる。
  toy 主語なし——主語は実 q3kRing・実 q3rqRing・実 z3。

  complete_pct 影響: **B2 は 0 のまま（監査次第 0→0.05–0.10・status mover は M3）**。
  本モジュール単体は非ノルムを何も証明しない（graded 零性のみ）。後続計画（§2(c)）:
   * M3 `Q3LocalReciprocityReal.lean`（仮）— **crux 4∉N**（初の status mover・s_B2 0→0.25–0.35）
  本 M2 はその M3 が step1（level-1 先頭項分離 q9gn_norm_U1_sharp）と最終降下
  （N(U^(2))⊆U^(9) = q9gn_norm_U2）で消費する graded 公式を供給する。

  真水（本物へ昇格・新規建設）:
   * q9gn_two_e2（★ 対称式恒等式 2·E₂ = Tr²−Tr∘sq・純環）— E₂ の鋭い評価の本体
   * q9gn_e2_kill（∀t π₉⁶∣E₂）・q9gn_e2_U2_kill（π₉²a で π₉⁹∣E₂・λ 因子）
   * q9gn_break_cancel（★ §2.3 の打ち消し）— Tr(π₉²a)+N(π₉²a) ∈ (π₉⁹)、res_L 核 + Fermat
   * q9gn_norm_U2（★★ 鍵）— **N(U^(2)) ⊆ U^(9)**（M3 最終降下の入力）
   * q9gn_norm_U1_sharp（level-1 先頭項分離）・q9gn_fermat3（3∣c³−c in ℤ₃）

  正直な限定（§4 規約により消さない・弱めない・q3k/q9ps/q9nf/q9wr/q3rq/q9rf 継承の上に追記のみ）:
  1. **単一拡大 M/L₂/ℚ₃**（q3k 兄弟担体・拡大 1 個）。より高次の拡大塔ゼロ。
  2. **U^(2)/level-6 に焦点**（graded 写像の零性のみ・cokernel の同型ゼロ）。非ノルム性は M3。
  3. **可除性形式**（q9wrDvd・v_M 不使用）。付値関数を建てない B1 正直限定に整合。
  4. q3k/q9ps/q9nf/q9wr/q3rq/q9rf の正直限定を全継承（O_M と M^× のみ・体化なし・
     σ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ）。
  5. **非ノルム性（4∉N）はゼロ**（M3 本体）。本 M2 は crux への足場に留まる。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3ResidueFieldReal

namespace IUT

/-! ## q9gn-0: 純環の対称式恒等式 2·E₂(t) = Tr(t)² − Tr(t²) の骨格 -/

/-- **(x+(y+z))² = (x²+(y²+z²)) + 2·(xy+(xz+yz))**（純可換環・平方展開）。 -/
theorem q9gn_sq_lemma (R : CRing) (x y z : R.carrier) :
    R.mul (R.add x (R.add y z)) (R.add x (R.add y z))
    = R.add (R.add (R.mul x x) (R.add (R.mul y y) (R.mul z z)))
        (R.add (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))
               (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))) := by
  rw [R.left_distrib (R.add x (R.add y z)) x (R.add y z),
      R.right_distrib x (R.add y z) x,
      R.right_distrib x (R.add y z) (R.add y z),
      R.left_distrib x y z,
      R.right_distrib y z x,
      R.right_distrib y z (R.add y z),
      R.left_distrib y y z,
      R.left_distrib z y z]
  rw [R.mul_comm y x, R.mul_comm z x, R.mul_comm z y]
  rw [R.add_assoc (R.mul x x) (R.add (R.mul x y) (R.mul x z))
        (R.add (R.add (R.mul x y) (R.mul x z)) (R.add (R.add (R.mul y y) (R.mul y z)) (R.add (R.mul y z) (R.mul z z)))),
      R.add_assoc (R.mul x y) (R.mul x z)
        (R.add (R.add (R.mul x y) (R.mul x z)) (R.add (R.add (R.mul y y) (R.mul y z)) (R.add (R.mul y z) (R.mul z z)))),
      R.add_assoc (R.mul x y) (R.mul x z) (R.add (R.add (R.mul y y) (R.mul y z)) (R.add (R.mul y z) (R.mul z z))),
      R.add_assoc (R.mul y y) (R.mul y z) (R.add (R.mul y z) (R.mul z z))]
  rw [R.add_assoc (R.mul x x) (R.add (R.mul y y) (R.mul z z))
        (R.add (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z))) (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))),
      R.add_assoc (R.mul y y) (R.mul z z)
        (R.add (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z))) (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))),
      R.add_assoc (R.mul x y) (R.add (R.mul x z) (R.mul y z)) (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z))),
      R.add_assoc (R.mul x z) (R.mul y z) (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))]
  rw [q9nf_add_swap R (R.mul x z) (R.mul y y) (R.add (R.mul y z) (R.add (R.mul y z) (R.mul z z))),
      q9nf_add_swap R (R.mul x y) (R.mul y y) (R.add (R.mul x z) (R.add (R.mul y z) (R.add (R.mul y z) (R.mul z z)))),
      q9nf_add_swap R (R.mul x z) (R.mul y y) (R.add (R.mul x y) (R.add (R.mul x z) (R.add (R.mul y z) (R.add (R.mul y z) (R.mul z z))))),
      q9nf_add_swap R (R.mul x y) (R.mul y y) (R.add (R.mul x z) (R.add (R.mul x y) (R.add (R.mul x z) (R.add (R.mul y z) (R.add (R.mul y z) (R.mul z z))))))]
  rw [R.add_comm (R.mul y z) (R.mul z z),
      q9nf_add_swap R (R.mul y z) (R.mul z z) (R.mul y z),
      q9nf_add_swap R (R.mul x z) (R.mul z z) (R.add (R.mul y z) (R.mul y z)),
      q9nf_add_swap R (R.mul x y) (R.mul z z) (R.add (R.mul x z) (R.add (R.mul y z) (R.mul y z))),
      q9nf_add_swap R (R.mul x z) (R.mul z z) (R.add (R.mul x y) (R.add (R.mul x z) (R.add (R.mul y z) (R.mul y z)))),
      q9nf_add_swap R (R.mul x y) (R.mul z z) (R.add (R.mul x z) (R.add (R.mul x y) (R.add (R.mul x z) (R.add (R.mul y z) (R.mul y z)))))]
  rw [q9nf_add_swap R (R.mul x z) (R.mul y z) (R.mul y z),
      q9nf_add_swap R (R.mul x y) (R.mul y z) (R.add (R.mul x z) (R.mul y z))]

/-- **2·E₂ = Tr² − Tr∘sq**（抽象環版・sq_lemma からの相殺）。 -/
theorem q9gn_two_e2_ring (R : CRing) (x y z : R.carrier) :
    R.add (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))
          (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))
    = R.add (R.mul (R.add x (R.add y z)) (R.add x (R.add y z)))
        (R.neg (R.add (R.mul x x) (R.add (R.mul y y) (R.mul z z)))) := by
  rw [q9gn_sq_lemma R x y z,
      R.add_comm (R.add (R.mul x x) (R.add (R.mul y y) (R.mul z z)))
        (R.add (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))
               (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))),
      R.add_assoc
        (R.add (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))
               (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z))))
        (R.add (R.mul x x) (R.add (R.mul y y) (R.mul z z)))
        (R.neg (R.add (R.mul x x) (R.add (R.mul y y) (R.mul z z)))),
      R.add_neg (R.add (R.mul x x) (R.add (R.mul y y) (R.mul z z))),
      R.add_zero
        (R.add (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z)))
               (R.add (R.mul x y) (R.add (R.mul x z) (R.mul y z))))]

/-- 加法再配置補助（p+q=0 のとき (p+b)+(b+(q+b)) = b+(b+b)）。 -/
theorem q9gn_pqb (R : CRing) (p q b : R.carrier) (h : R.add p q = R.zero) :
    R.add (R.add p b) (R.add b (R.add q b)) = R.add b (R.add b b) := by
  rw [R.add_assoc p b (R.add b (R.add q b)),
      R.add_left_comm b q b,
      R.add_left_comm b q (R.add b b),
      ← R.add_assoc p q (R.add b (R.add b b)),
      h, R.zero_add]

/-! ## q9gn-1: 実 2 = 1+1 は単数・可除性の一般補助 -/

/-- 実 2_M = 1+1 ∈ O_M。 -/
def q9gnTwoM : q3kCar := q3kAdd q3kOne q3kOne

/-- 実 2 ∈ O_{L₂}。 -/
def q9gnTwoElt : q3rqCar := q3rqAdd q3rqOne q3rqOne

/-- 2_M = embed(2)。 -/
theorem q9gn_twoM_embed : q9gnTwoM = q3kEmbed q9gnTwoElt := by
  show q3kAdd q3kOne q3kOne = q3kEmbed (q3rqAdd q3rqOne q3rqOne)
  rw [q9rf_embed_add q3rqOne q3rqOne, q3k_embed_one]

/-- 2_{L₂} = (2,0)。 -/
theorem q9gn_twoElt_eq : q9gnTwoElt = ((q3rqTwoZ, z3.zero) : q3rqCar) := by
  apply q3rq_ext
  · rfl
  · show z3.add z3.zero z3.zero = z3.zero
    exact z3.add_zero z3.zero

/-- 2_{L₂} は実単数。 -/
theorem q9gn_twoElt_unit : q3rqUnitMem q9gnTwoElt := by
  rw [q9gn_twoElt_eq]; exact q3rq_pair_unit q3rqTwoZ q3rq_two_unit

/-- 2_M は実単数。 -/
theorem q9gn_twoM_unit : q3kUnitMem q9gnTwoM := by
  rw [q9gn_twoM_embed]; exact q9wr_embed_unit q9gnTwoElt q9gn_twoElt_unit

/-- 2_M の逆元。 -/
def q9gnTwoInv : q3kCar := q3kInv q9gnTwoM q9gn_twoM_unit

/-- 2⁻¹·2 = 1。 -/
theorem q9gn_twoInv_mul : q3kMul q9gnTwoInv q9gnTwoM = q3kOne :=
  q3k_inv_mul' q9gnTwoM q9gn_twoM_unit

/-- 2_M·y = y + y。 -/
theorem q9gn_two_mul (y : q3kCar) : q3kMul q9gnTwoM y = q3kAdd y y := by
  show q3kMul (q3kAdd q3kOne q3kOne) y = q3kAdd y y
  rw [q3k_kM_eq, q9nf_kA_eq, q9ps_kO_eq,
      CRing.right_distrib q3kRing q3kRing.one q3kRing.one y, q3kRing.one_mul y]

/-- 単数消去: uinv·u = 1 かつ d ∣ u·y ⟹ d ∣ y。 -/
theorem q9gn_unit_dvd_cancel {d u uinv y : q3kCar}
    (hu : q3kMul uinv u = q3kOne) (h : q9wrDvd d (q3kMul u y)) : q9wrDvd d y := by
  obtain ⟨c, hc⟩ := h
  refine ⟨q3kMul uinv c, ?_⟩
  have hy : y = q3kMul uinv (q3kMul d c) := by
    have hcc := congrArg (q3kMul uinv) hc
    rw [← q3k_mul_assoc uinv u y, hu, q3k_one_mul] at hcc
    exact hcc
  rw [hy, q3k_kM_eq]
  exact CRing.mul_left_comm q3kRing uinv d c

/-- 2_M による可除性消去: d ∣ 2·y ⟹ d ∣ y。 -/
theorem q9gn_two_dvd_cancel {d y : q3kCar}
    (h : q9wrDvd d (q3kMul q9gnTwoM y)) : q9wrDvd d y :=
  q9gn_unit_dvd_cancel q9gn_twoInv_mul h

/-- d ∣ y ⟹ d ∣ (−y)。 -/
theorem q9gn_dvd_neg {d y : q3kCar} (h : q9wrDvd d y) : q9wrDvd d (q3kNeg y) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨q3kNeg c, ?_⟩
  rw [hc, q3k_kM_eq, q9ps_kN_eq]
  exact (CRing.mul_neg q3kRing d c).symm

/-! ## q9gn-2: embed(3·λ·s) ∈ (π₉⁹) の可除性ハブ -/

/-- π₉⁶ ∣ embed(3)（3 = π₉⁶·u₆）。 -/
theorem q9gn_embed_three_dvd6 : q9wrDvd (q9nfPiPow 6) (q3kEmbed q3rqThreeElt) := by
  refine ⟨q9psU6, ?_⟩
  rw [q9nf_pipow6_eq]
  exact q9ps_three_eq_pi6_u6

/-- π₉³ ∣ embed(λ·s)（λ = π₉³·w⁻¹）。 -/
theorem q9gn_embed_lambda_dvd3 (s : q3rqCar) :
    q9wrDvd (q9nfPiPow 3) (q3kEmbed (q3rqMul q3rqLambda s)) := by
  refine ⟨q3kMul q9psWinv (q3kEmbed s), ?_⟩
  rw [← q3k_embed_mul q3rqLambda s, q9nf_embed_lambda, q3k_kM_eq,
      q3kRing.mul_assoc (q9nfPiPow 3) q9psWinv (q3kEmbed s)]

/-- **π₉⁹ ∣ embed(3·(λ·s))**（3 の π₉⁶ と λ の π₉³ の合流）。 -/
theorem q9gn_embed_3lam_dvd9 (s : q3rqCar) :
    q9wrDvd (q9nfPiPow 9) (q3kEmbed (q3rqMul q3rqThreeElt (q3rqMul q3rqLambda s))) := by
  obtain ⟨c6, hc6⟩ := q9gn_embed_three_dvd6
  obtain ⟨c3, hc3⟩ := q9gn_embed_lambda_dvd3 s
  refine ⟨q3kMul c6 c3, ?_⟩
  have h9 : q9nfPiPow 9 = q3kMul (q9nfPiPow 6) (q9nfPiPow 3) := q9nf_pipow_add 6 3
  rw [← q3k_embed_mul q3rqThreeElt (q3rqMul q3rqLambda s), hc6, hc3, h9, q3k_kM_eq,
      q3kRing.mul_mul_mul_comm (q9nfPiPow 6) c6 (q9nfPiPow 3) c3]

/-! ## q9gn-3: 対称式恒等式の q3k 化と E₂ kill -/

/-- **q9gn-3a（★ 対称式恒等式）: 2·E₂(t) = Tr(t)² − Tr(t·t)**。 -/
theorem q9gn_two_e2 (t : q3kCar) :
    q3kMul q9gnTwoM (q9nfE2 t)
    = q3kAdd (q3kMul (q9nfTr t) (q9nfTr t)) (q3kNeg (q9nfTr (q3kMul t t))) := by
  rw [q9gn_two_mul (q9nfE2 t)]
  have htt : q9nfTr (q3kMul t t)
      = q3kAdd (q3kMul t t)
          (q3kAdd (q3kMul (q3kSigma t) (q3kSigma t)) (q3kMul (q3kSigma2 t) (q3kSigma2 t))) := by
    show q3kAdd (q3kMul t t) (q3kAdd (q3kSigma (q3kMul t t)) (q3kSigma2 (q3kMul t t))) = _
    rw [q3k_sigma_mul t t, q3k_sigma2_mul t t]
  rw [htt]
  exact q9gn_two_e2_ring q3kRing t (q3kSigma t) (q3kSigma2 t)

/-- **q9gn-3b: π₉⁶ ∣ E₂(t)（∀t）** — Tr²∈π₉¹²・Tr(t·t)∈π₉⁶・2 単数消去。 -/
theorem q9gn_e2_kill (t : q3kCar) : q9wrDvd (q9nfPiPow 6) (q9nfE2 t) := by
  apply q9gn_two_dvd_cancel
  rw [q9gn_two_e2 t]
  refine q9nf_dvd_add ?_ (q9gn_dvd_neg ?_)
  · exact q9nf_dvd_of_le (by omega)
      (q9nf_dvd_mul (q9nf_trace_kill t) (q9nf_trace_kill t))
  · exact q9nf_trace_kill (q3kMul t t)

/-! ## q9gn-4: π₉² の座標と π₉⁴ の λ 因子分解 -/

/-- π₉² = π₉·π₉。 -/
theorem q9gn_pi2_eq : q9nfPiPow 2 = q3kMul q9psPi9 q9psPi9 := by
  show q3kMul q9psPi9 (q3kMul q9psPi9 q3kOne) = q3kMul q9psPi9 q9psPi9
  rw [q3k_kM_eq, q9ps_kO_eq, q3kRing.mul_one q9psPi9]

/-- **π₉² = (1, −2, 1)**（(Y−1)² = Y²−2Y+1）。 -/
theorem q9gn_pi2_coords :
    q9nfPiPow 2 = ((q3rqOne, q3rqNeg (q3rqAdd q3rqOne q3rqOne), q3rqOne) : q3kCar) := by
  rw [q9gn_pi2_eq, q9ps_pi9_coords]
  apply q3k_ext
  · show q3rqAdd (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne))
        (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqOne q3rqZero) (q3rqMul q3rqZero q3rqOne))) = q3rqOne
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q3k_Z_eq, q9ps_1_eq,
        CRing.neg_mul q3rqRing q3rqRing.one (q3rqRing.neg q3rqRing.one),
        q3rqRing.one_mul (q3rqRing.neg q3rqRing.one),
        CRing.neg_neg q3rqRing q3rqRing.one,
        q3rqRing.mul_zero q3rqRing.one, q3rqRing.zero_mul q3rqRing.one,
        q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero q3rqRing.one]
  · show q3rqAdd (q3rqAdd (q3rqMul (q3rqNeg q3rqOne) q3rqOne) (q3rqMul q3rqOne (q3rqNeg q3rqOne)))
        (q3rqMul q3rqZeta (q3rqMul q3rqZero q3rqZero)) = q3rqNeg (q3rqAdd q3rqOne q3rqOne)
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q3k_Z_eq, q9ps_1_eq,
        CRing.neg_mul q3rqRing q3rqRing.one q3rqRing.one, q3rqRing.one_mul q3rqRing.one,
        CRing.mul_neg q3rqRing q3rqRing.one q3rqRing.one, q3rqRing.mul_one q3rqRing.one,
        q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqRing.one)),
        CRing.neg_add_dist q3rqRing q3rqRing.one q3rqRing.one]
  · show q3rqAdd (q3rqAdd (q3rqMul (q3rqNeg q3rqOne) q3rqZero) (q3rqMul q3rqOne q3rqOne))
        (q3rqMul q3rqZero (q3rqNeg q3rqOne)) = q3rqOne
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q3k_Z_eq, q9ps_1_eq,
        q3rqRing.mul_zero (q3rqRing.neg q3rqRing.one), q3rqRing.one_mul q3rqRing.one,
        q3rqRing.zero_mul (q3rqRing.neg q3rqRing.one),
        q3rqRing.zero_add q3rqRing.one, q3rqRing.add_zero q3rqRing.one]

/-- **π₉⁴ = embed(λ)·(w·π₉)**（λ = π₉³·w⁻¹ より）。 -/
theorem q9gn_pi4_eq :
    q3kMul (q3kEmbed q3rqLambda) (q3kMul q9psW q9psPi9) = q9nfPiPow 4 := by
  have hww : q3kRing.mul q9psWinv q9psW = q3kRing.one := by
    have h := q9ps_w_inv_mul
    rw [q3k_kM_eq, q9ps_kO_eq] at h
    rw [q3kRing.mul_comm q9psWinv q9psW]; exact h
  rw [q9nf_embed_lambda, q3k_kM_eq,
      q3kRing.mul_assoc (q9nfPiPow 3) q9psWinv (q3kRing.mul q9psW q9psPi9),
      ← q3kRing.mul_assoc q9psWinv q9psW q9psPi9, hww, q3kRing.one_mul q9psPi9]
  show q3kRing.mul (q9nfPiPow 3) q9psPi9 = q3kMul q9psPi9 (q9nfPiPow 3)
  rw [q3k_kM_eq]
  exact q3kRing.mul_comm (q9nfPiPow 3) q9psPi9

/-! ## q9gn-5: E₂(π₉²a) は level 9（π₉⁹∣・λ 因子で trace の sharp 化） -/

/-- t·t = π₉⁴·a² = embed(λ)·(w·π₉·a²)。 -/
theorem q9gn_tsq_lambda (a : q3kCar) :
    q3kMul (q3kMul (q9nfPiPow 2) a) (q3kMul (q9nfPiPow 2) a)
    = q3kMul (q3kEmbed q3rqLambda) (q3kMul (q3kMul q9psW q9psPi9) (q3kMul a a)) := by
  have h1 : q3kMul (q3kMul (q9nfPiPow 2) a) (q3kMul (q9nfPiPow 2) a)
      = q3kMul (q3kMul (q9nfPiPow 2) (q9nfPiPow 2)) (q3kMul a a) := by
    rw [q3k_kM_eq]; exact q3kRing.mul_mul_mul_comm (q9nfPiPow 2) a (q9nfPiPow 2) a
  have h2 : q3kMul (q9nfPiPow 2) (q9nfPiPow 2) = q9nfPiPow 4 := (q9nf_pipow_add 2 2).symm
  rw [h1, h2, ← q9gn_pi4_eq, q3k_kM_eq,
      q3kRing.mul_assoc (q3kEmbed q3rqLambda) (q3kRing.mul q9psW q9psPi9) (q3kRing.mul a a)]

/-- (t·t) の第 0 座標 = λ·G.1（λ 因子）。 -/
theorem q9gn_tsq_coord0 (a : q3kCar) :
    (q3kMul (q3kMul (q9nfPiPow 2) a) (q3kMul (q9nfPiPow 2) a)).1
    = q3rqMul q3rqLambda (q3kMul (q3kMul q9psW q9psPi9) (q3kMul a a)).1 := by
  rw [q9gn_tsq_lambda a, q3kMul_0, q3kEmbed_0, q3kEmbed_1, q3kEmbed_2, q3k_M_eq, q3k_A_eq, q3k_Z_eq,
      q3rqRing.zero_mul (q3kMul (q3kMul q9psW q9psPi9) (q3kMul a a)).2.2,
      q3rqRing.zero_mul (q3kMul (q3kMul q9psW q9psPi9) (q3kMul a a)).2.1,
      q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
      q3rqRing.add_zero (q3rqRing.mul q3rqLambda (q3kMul (q3kMul q9psW q9psPi9) (q3kMul a a)).1)]

/-- π₉⁹ ∣ Tr(t·t)（t = π₉²a、λ 因子で 3λ 化）。 -/
theorem q9gn_tr_tsq_dvd (a : q3kCar) :
    q9wrDvd (q9nfPiPow 9)
      (q9nfTr (q3kMul (q3kMul (q9nfPiPow 2) a) (q3kMul (q9nfPiPow 2) a))) := by
  rw [q9nf_tr_embed (q3kMul (q3kMul (q9nfPiPow 2) a) (q3kMul (q9nfPiPow 2) a)),
      q9ps_three_eq, q9gn_tsq_coord0 a]
  exact q9gn_embed_3lam_dvd9 (q3kMul (q3kMul q9psW q9psPi9) (q3kMul a a)).1

/-- **q9gn-5a（★）: π₉⁹ ∣ E₂(π₉²a)** — level 9（Tr²∈π₉¹²・Tr(t·t)∈π₉⁹・2 消去）。 -/
theorem q9gn_e2_U2_kill (a : q3kCar) :
    q9wrDvd (q9nfPiPow 9) (q9nfE2 (q3kMul (q9nfPiPow 2) a)) := by
  apply q9gn_two_dvd_cancel
  rw [q9gn_two_e2 (q3kMul (q9nfPiPow 2) a)]
  refine q9nf_dvd_add ?_ (q9gn_dvd_neg ?_)
  · exact q9nf_dvd_of_le (by omega)
      (q9nf_dvd_mul (q9nf_trace_kill (q3kMul (q9nfPiPow 2) a))
        (q9nf_trace_kill (q3kMul (q9nfPiPow 2) a)))
  · exact q9gn_tr_tsq_dvd a

/-! ## q9gn-6: 𝔽₃ 残余の cube / neg / one 補助と Fermat -/

/-- 𝔽₃ Fermat（左結合形）: (r·r)·r = r。 -/
theorem q9gn_f3_cube_l (r : q9rfF3.carrier) : q9rfF3.mul (q9rfF3.mul r r) r = r :=
  (q9rfF3.mul_assoc r r r).trans (q9rf_f3_cube r)

/-- resL(−X) = −resL(X)。 -/
theorem q9gn_resL_neg (X : q3rqCar) : q9rfResL (q3rqNeg X) = q9rfF3.neg (q9rfResL X) :=
  q9rf_res3_neg X.1

/-- resL(1) = 1。 -/
theorem q9gn_resL_one : q9rfResL q3rqOne = q9rfF3.one := q9rf_res3_one

/-- 𝔽₃: −(1+1) = 1。 -/
theorem q9gn_f3_neg_two : q9rfF3.neg (q9rfF3.add q9rfF3.one q9rfF3.one) = q9rfF3.one := by
  show Quot.mk (modCong 3).rel (-(1 + 1)) = Quot.mk (modCong 3).rel 1
  apply Quot.sound
  show ((3 : Nat) : Int) ∣ (-(1 + 1)) - 1
  exact ⟨-1, by omega⟩

/-- **q9gn_fermat3: 3 ∣ c³−c in ℤ₃**（Fermat・res₃ 経由・div-by-3 witness）。 -/
theorem q9gn_fermat3 (c : z3.carrier) :
    ∃ k, z3.add (z3.mul (z3.mul c c) c) (z3.neg c) = z3.mul q3rqThree k := by
  apply q9rf_div3
  rw [q9rf_res3_add, q9rf_res3_neg, q9rf_res3_mul, q9rf_res3_mul]
  rw [q9gn_f3_cube_l (q9rfRes3 c)]
  exact q9rfF3.add_neg (q9rfRes3 c)

/-! ## q9gn-7: res_L(bracket) = 0 と λ ∣ bracket（§2.3 の Fermat 打ち消し） -/

/-- resL 核: resL(n) = 0 ⟹ λ ∣ n（n.1 = 3k ⟹ n = λ·(n.2, −k)）。 -/
theorem q9gn_resL_lambda_dvd (n : q3rqCar) (h : q9rfResL n = q9rfF3.zero) :
    ∃ m : q3rqCar, n = q3rqMul q3rqLambda m := by
  obtain ⟨k, hk⟩ := q9rf_div3 n.1 h
  refine ⟨((n.2, z3.neg k) : q3rqCar), ?_⟩
  apply q3rq_ext
  · show n.1 = z3.add (z3.mul z3.zero n.2) (z3.mul q3rqD (z3.mul z3.one (z3.neg k)))
    rw [z3.zero_mul n.2, z3.zero_add, z3.one_mul (z3.neg k),
        q3rq_D_eq, z3.neg_mul q3rqThree (z3.neg k), z3.mul_neg q3rqThree k, z3.neg_neg, hk]
  · show n.2 = z3.add (z3.mul z3.zero (z3.neg k)) (z3.mul z3.one n.2)
    rw [z3.zero_mul (z3.neg k), z3.zero_add, z3.one_mul n.2]

/-- resL(N(a)) = res(a₀) + res(a₁) + res(a₂)（Fermat a³=a・3ζabc→0）。 -/
theorem q9gn_resL_normBase (a : q3kCar) :
    q9rfResL (q3kNormBase a)
    = q9rfF3.add (q9rfResL a.1) (q9rfF3.add (q9rfResL a.2.1) (q9rfResL a.2.2)) := by
  have hP0 : q9rfResL (q3rqMul (q3rqMul a.1 a.1) a.1) = q9rfResL a.1 := by
    rw [q9rf_resL_mul, q9rf_resL_mul]; exact q9gn_f3_cube_l (q9rfResL a.1)
  have hP1 : q9rfResL (q3rqMul q3rqZeta (q3rqMul (q3rqMul a.2.1 a.2.1) a.2.1)) = q9rfResL a.2.1 := by
    rw [q9rf_resL_mul, q9rf_resL_zeta, q9rf_resL_mul, q9rf_resL_mul, q9rfF3.one_mul]
    exact q9gn_f3_cube_l (q9rfResL a.2.1)
  have hP2 : q9rfResL (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul a.2.2 a.2.2) a.2.2)) = q9rfResL a.2.2 := by
    rw [q9rf_resL_mul, q9rf_resL_zetaSq, q9rf_resL_mul, q9rf_resL_mul, q9rfF3.one_mul]
    exact q9gn_f3_cube_l (q9rfResL a.2.2)
  have hT : q9rfResL (q3rqMul q3kThree (q3rqMul q3rqZeta (q3rqMul (q3rqMul a.1 a.2.1) a.2.2)))
      = q9rfF3.zero := by
    rw [q9rf_resL_mul, q9ps_three_eq, q9rf_resL_three, q9rfF3.zero_mul]
  show q9rfResL (q3rqAdd (q3rqAdd (q3rqAdd (q3rqMul (q3rqMul a.1 a.1) a.1)
      (q3rqMul q3rqZeta (q3rqMul (q3rqMul a.2.1 a.2.1) a.2.1)))
      (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul a.2.2 a.2.2) a.2.2)))
    (q3rqNeg (q3rqMul q3kThree (q3rqMul q3rqZeta (q3rqMul (q3rqMul a.1 a.2.1) a.2.2))))) = _
  rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_add, q9gn_resL_neg,
      hP0, hP1, hP2, hT, q9rfF3.neg_zero,
      q9rfF3.add_zero (q9rfF3.add (q9rfF3.add (q9rfResL a.1) (q9rfResL a.2.1)) (q9rfResL a.2.2)),
      q9rfF3.add_assoc (q9rfResL a.1) (q9rfResL a.2.1) (q9rfResL a.2.2)]

/-- resL((π₉²a)₀) = res(a₀) + res(a₁) + res(a₂)（π₉²=(1,−2,1)・−2≡1）。 -/
theorem q9gn_resL_t1 (a : q3kCar) :
    q9rfResL (q3kMul (q9nfPiPow 2) a).1
    = q9rfF3.add (q9rfResL a.1) (q9rfF3.add (q9rfResL a.2.1) (q9rfResL a.2.2)) := by
  rw [q9gn_pi2_coords]
  show q9rfResL (q3rqAdd (q3rqMul q3rqOne a.1)
      (q3rqMul q3rqZeta (q3rqAdd (q3rqMul (q3rqNeg (q3rqAdd q3rqOne q3rqOne)) a.2.2)
        (q3rqMul q3rqOne a.2.1)))) = _
  rw [q9rf_resL_add, q9rf_resL_mul, q9gn_resL_one, q9rfF3.one_mul,
      q9rf_resL_mul, q9rf_resL_zeta, q9rfF3.one_mul,
      q9rf_resL_add, q9rf_resL_mul, q9gn_resL_neg, q9rf_resL_add, q9gn_resL_one,
      q9gn_f3_neg_two, q9rfF3.one_mul, q9rf_resL_mul, q9gn_resL_one, q9rfF3.one_mul,
      q9rfF3.add_comm (q9rfResL a.2.2) (q9rfResL a.2.1)]

/-- **q9gn-7a: bracket = (π₉²a)₀ − ζ₃N(a) は λ 可除**（res_L 核・Fermat 打ち消し）。 -/
theorem q9gn_bracket_lambda (a : q3kCar) :
    ∃ m : q3rqCar,
      q3rqAdd (q3kMul (q9nfPiPow 2) a).1 (q3rqNeg (q3rqMul q3rqZeta (q3kNormBase a)))
      = q3rqMul q3rqLambda m := by
  apply q9gn_resL_lambda_dvd
  rw [q9rf_resL_add, q9gn_resL_neg, q9rf_resL_mul, q9rf_resL_zeta, q9rfF3.one_mul,
      q9gn_resL_t1 a, q9gn_resL_normBase a]
  exact q9rfF3.add_neg (q9rfF3.add (q9rfResL a.1) (q9rfF3.add (q9rfResL a.2.1) (q9rfResL a.2.2)))

/-! ## q9gn-8: N(π₉²) = −3ζ₃ と N(π₉²a) の閉形式 -/

/-- **(ζ₃−1)² = −3ζ₃**（純環・ζ₃²=−1−ζ₃）。 -/
theorem q9gn_nu_sq :
    q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta)
    = q3rqMul q3rqThreeElt (q3rqNeg q3rqZeta) := by
  have hzsq : q3rqZetaSq = q3rqRing.add (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqZeta) := by
    have h : q3rqRing.add q3rqRing.one (q3rqRing.add q3rqZeta q3rqZetaSq) = q3rqRing.zero := by
      have h0 := q3k_zeta_sum_zero; rw [q3k_A_eq, q3k_Z_eq] at h0; exact h0
    rw [← q3rqRing.add_assoc q3rqRing.one q3rqZeta q3rqZetaSq] at h
    have h2 := q3rqRing.neg_eq_of_add_eq_zero h
    rw [← h2, q3rqRing.neg_add_dist q3rqRing.one q3rqZeta]
  rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq,
      q3rqRing.right_distrib (q3rqRing.neg q3rqRing.one) q3rqZeta (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZeta),
      q3rqRing.left_distrib (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqRing.one) q3rqZeta,
      q3rqRing.left_distrib q3rqZeta (q3rqRing.neg q3rqRing.one) q3rqZeta,
      CRing.neg_mul q3rqRing q3rqRing.one (q3rqRing.neg q3rqRing.one),
      q3rqRing.one_mul (q3rqRing.neg q3rqRing.one),
      CRing.neg_neg q3rqRing q3rqRing.one,
      CRing.neg_mul q3rqRing q3rqRing.one q3rqZeta,
      q3rqRing.one_mul q3rqZeta,
      CRing.mul_neg q3rqRing q3rqZeta q3rqRing.one,
      q3rqRing.mul_one q3rqZeta,
      q3k_z_zR, hzsq,
      CRing.mul_neg q3rqRing q3rqThreeElt q3rqZeta, ← q9ps_three_eq, q3k_three_K q3rqZeta]
  exact q9gn_pqb q3rqRing q3rqRing.one (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqZeta)
    (q3rqRing.add_neg q3rqRing.one)

/-- N(π₉²) = −3ζ₃。 -/
theorem q9gn_normBase_pi2 :
    q3kNormBase (q9nfPiPow 2) = q3rqMul q3rqThreeElt (q3rqNeg q3rqZeta) := by
  rw [q9gn_pi2_eq, q3k_normBase_mul q9psPi9 q9psPi9, q9wr_normBase_pi9]
  exact q9gn_nu_sq

/-- **N(π₉²·a) = 3·(−ζ₃·N(a))**（乗法性 + −3ζ₃）。 -/
theorem q9gn_Nt_closed (a : q3kCar) :
    q3kNormBase (q3kMul (q9nfPiPow 2) a)
    = q3rqMul q3rqThreeElt (q3rqNeg (q3rqMul q3rqZeta (q3kNormBase a))) := by
  rw [q3k_normBase_mul (q9nfPiPow 2) a, q9gn_normBase_pi2, q3k_M_eq, q3k_N_eq,
      q3rqRing.mul_assoc q3rqThreeElt (q3rqRing.neg q3rqZeta) (q3kNormBase a),
      CRing.neg_mul q3rqRing q3rqZeta (q3kNormBase a)]

/-! ## q9gn-9: ★ break cancellation（§2.3）: Tr(π₉²a)+N(π₉²a) ∈ (π₉⁹） -/

/-- **q9gn-9a（★★ break cancel）: π₉⁹ ∣ Tr(π₉²a) + embed(N(π₉²a))**。
    Tr + embed N = embed(3·[(π₉²a)₀ − ζ₃N(a)]) で括弧が λ 可除（Fermat）。 -/
theorem q9gn_break_cancel (a : q3kCar) :
    q9wrDvd (q9nfPiPow 9)
      (q3kAdd (q9nfTr (q3kMul (q9nfPiPow 2) a))
        (q3kEmbed (q3kNormBase (q3kMul (q9nfPiPow 2) a)))) := by
  obtain ⟨m, hm⟩ := q9gn_bracket_lambda a
  rw [q9nf_tr_embed (q3kMul (q9nfPiPow 2) a), q9ps_three_eq,
      ← q9rf_embed_add (q3rqMul q3rqThreeElt (q3kMul (q9nfPiPow 2) a).1)
        (q3kNormBase (q3kMul (q9nfPiPow 2) a))]
  have hm' : q3rqRing.add (q3kMul (q9nfPiPow 2) a).1
        (q3rqRing.neg (q3rqRing.mul q3rqZeta (q3kNormBase a)))
      = q3rqRing.mul q3rqLambda m := by
    rw [← q3k_A_eq, ← q3k_N_eq, ← q3k_M_eq]; exact hm
  have hD : q3rqAdd (q3rqMul q3rqThreeElt (q3kMul (q9nfPiPow 2) a).1)
        (q3kNormBase (q3kMul (q9nfPiPow 2) a))
      = q3rqMul q3rqThreeElt (q3rqMul q3rqLambda m) := by
    rw [q9gn_Nt_closed a, q3k_M_eq, q3k_A_eq, q3k_N_eq,
        ← q3rqRing.left_distrib q3rqThreeElt (q3kMul (q9nfPiPow 2) a).1
          (q3rqRing.neg (q3rqRing.mul q3rqZeta (q3kNormBase a))), hm']
  rw [hD]
  exact q9gn_embed_3lam_dvd9 m

/-! ## q9gn-10: ★★ 鍵——N(U^(2)) ⊆ U^(9) と level-1 先頭項分離 -/

/-- **q9gn-10a（★★ 鍵）: N(U^(2)) ⊆ U^(9)** — break cancel + E₂ level 9 の合成。 -/
theorem q9gn_norm_U2 {x : q3kCar} (hx : q9nfUfilt 2 x) :
    q9nfUfilt 9 (q3kEmbed (q3kNormBase x)) := by
  obtain ⟨a, ha⟩ := q9nf_ufilt_decomp hx
  show q9wrDvd (q9nfPiPow 9) (q3kAdd (q3kEmbed (q3kNormBase x)) (q3kNeg q3kOne))
  rw [ha, q9nf_norm_expand (q3kMul (q9nfPiPow 2) a), q9nf_one_add_cancel]
  have hre : q3kAdd (q9nfTr (q3kMul (q9nfPiPow 2) a))
        (q3kAdd (q9nfE2 (q3kMul (q9nfPiPow 2) a))
          (q3kEmbed (q3kNormBase (q3kMul (q9nfPiPow 2) a))))
      = q3kAdd (q3kAdd (q9nfTr (q3kMul (q9nfPiPow 2) a))
          (q3kEmbed (q3kNormBase (q3kMul (q9nfPiPow 2) a))))
          (q9nfE2 (q3kMul (q9nfPiPow 2) a)) := by
    rw [q9nf_kA_eq, q3kRing.add_comm (q9nfE2 (q3kMul (q9nfPiPow 2) a))
          (q3kEmbed (q3kNormBase (q3kMul (q9nfPiPow 2) a))),
        ← q3kRing.add_assoc (q9nfTr (q3kMul (q9nfPiPow 2) a))
          (q3kEmbed (q3kNormBase (q3kMul (q9nfPiPow 2) a)))
          (q9nfE2 (q3kMul (q9nfPiPow 2) a))]
  rw [hre]
  exact q9nf_dvd_add (q9gn_break_cancel a) (q9gn_e2_U2_kill a)

/-- **q9gn-10b: level-1 先頭項分離**（M3 step1 用）——
    x ∈ U^(1) なら x = 1+π₉·a かつ π₉⁶ ∣ (embed(Nx)−1−embed((ζ₃−1)N(a)))。
    先頭 graded 項 embed((ζ₃−1)N(a)) を差し引くと Tr+E₂（共に π₉⁶）が残る。 -/
theorem q9gn_norm_U1_sharp {x : q3kCar} (hx : q9nfUfilt 1 x) :
    ∃ a : q3kCar, x = q3kAdd q3kOne (q3kMul q9psPi9 a)
      ∧ q9wrDvd (q9nfPiPow 6)
          (q3kAdd (q3kAdd (q3kEmbed (q3kNormBase x)) (q3kNeg q3kOne))
            (q3kNeg (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a))))) := by
  obtain ⟨a, ha0⟩ := q9nf_ufilt_decomp hx
  have ha : x = q3kAdd q3kOne (q3kMul q9psPi9 a) := by rw [ha0, q9nf_pipow1_eq]
  refine ⟨a, ha, ?_⟩
  have hNt : q3kEmbed (q3kNormBase (q3kMul q9psPi9 a))
      = q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a)) := by
    rw [q3k_normBase_mul q9psPi9 a, q9wr_normBase_pi9]
  rw [ha, q9nf_norm_expand (q3kMul q9psPi9 a), q9nf_one_add_cancel, hNt,
      q9nf_kA_eq,
      q3kRing.add_assoc (q9nfTr (q3kMul q9psPi9 a))
        (q3kRing.add (q9nfE2 (q3kMul q9psPi9 a))
          (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a))))
        (q3kNeg (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a)))),
      q3kRing.add_assoc (q9nfE2 (q3kMul q9psPi9 a))
        (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a)))
        (q3kNeg (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a)))),
      q9ps_kN_eq,
      q3kRing.add_neg (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a))),
      q3kRing.add_zero (q9nfE2 (q3kMul q9psPi9 a))]
  exact q9nf_dvd_add (q9nf_trace_kill (q3kMul q9psPi9 a)) (q9gn_e2_kill (q3kMul q9psPi9 a))

/-! ## q9gn-11: capstone -/

/-- **q9gn-11a: graded ノルム break データ** — 対称式恒等式・E₂ kill・break cancel・N(U^(2))⊆U^(9)。 -/
structure Q3GradedNormBreakData where
  /-- 対称式恒等式 2·E₂ = Tr²−Tr∘sq。 -/
  two_e2 : ∀ t, q3kMul q9gnTwoM (q9nfE2 t)
    = q3kAdd (q3kMul (q9nfTr t) (q9nfTr t)) (q3kNeg (q9nfTr (q3kMul t t)))
  /-- E₂ の一般 kill: π₉⁶ ∣ E₂(t)。 -/
  e2_kill : ∀ t, q9wrDvd (q9nfPiPow 6) (q9nfE2 t)
  /-- break cancel: π₉⁹ ∣ Tr(π₉²a)+N(π₉²a)。 -/
  break_cancel : ∀ a, q9wrDvd (q9nfPiPow 9)
    (q3kAdd (q9nfTr (q3kMul (q9nfPiPow 2) a)) (q3kEmbed (q3kNormBase (q3kMul (q9nfPiPow 2) a))))
  /-- 鍵: N(U^(2)) ⊆ U^(9)。 -/
  norm_U2 : ∀ x, q9nfUfilt 2 x → q9nfUfilt 9 (q3kEmbed (q3kNormBase x))

/-- **q9gn-11b: 見出し実例** — 実 O_M = q3kRing の graded ノルム break。 -/
def q9gn_data : Q3GradedNormBreakData where
  two_e2 := q9gn_two_e2
  e2_kill := q9gn_e2_kill
  break_cancel := q9gn_break_cancel
  norm_U2 := fun _ hx => q9gn_norm_U2 hx

/-- **q9gn-11c: level-6 graded ノルム break の存在**（B2 crux 4∉N への足場）。 -/
theorem q9gn_exists : Nonempty Q3GradedNormBreakData := ⟨q9gn_data⟩

end IUT
