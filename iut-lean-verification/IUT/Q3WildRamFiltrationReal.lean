/-
  IUT/Q3WildRamFiltrationReal.lean — 柱B・B1 実野性分岐フィルトレーション
    （実 Gal(M/L₂)=⟨σ⟩ が実 O_M=q3kRing に作用する初の実分岐フィルトレーション）

  ── 主要成果の分類: **[実／(a) 昇格]**——既存 B の分岐フィルトレーション
     （wcd/mjw/ajw/hau＝**Nat 階段データ上**・監査が「Hasse–Arf 群は List Nat」と模型判定済み）
     と Eisenstein 塔（eisRing **模型環**上）を、実 Gal(M/L₂)=⟨q3kSigma⟩ が実 O_M=q3kRing に
     作用する**初の実野性分岐フィルトレーション**で置換する。主語は実 σ・実 π₉=Y−1・実 O_M
     ——toy 模型（m202fVol 型・Bool 軌道・surrogate 群）を一切使わない。核心の実データ:
       * σ(π₉)−π₉ = π₉³·u\*（u\* 閉形式実単数）— 実野性分岐の下付き break の実現
       * σ²(π₉)−π₉ = π₉³·u\*\*（同型）
       * 下付き G₀=G₁=G₂=⟨σ⟩・G₃∩{σ,σ²}=∅（break t=2）
       * 実 different (σπ₉−π₉)(σ²π₉−π₉) = π₉⁶·(u\*·u\*\*)（d(M/L₂)=6）
       * Nat 階段模型 wcdRamGroups 3 2（M441F）との genuine cross-check

  complete_pct 影響: **B1 0.5→(audit-decided, forecast 0.55–0.65)——display-moving**。
  本モジュールが動かす新規内容は **GALOIS 側データ σπ−π**（q9ps には Galois 作用が一切ない）。
  **3=π₉⁶·u₆ は q9ps_three_split（柱A）から CONSUME するのみで再主張しない**（e=6・v_π(3)=6 も
  q9ps 成果の消費）。ζ₃−1 系の正則性・q3rqNorm(ζ₃−1)=3 に至る単数論は本物の実計算。

  正直な限定（§4 規約により消さない・弱化しない・q3k/q9ps/q9ci/q9tl 継承の上に追記のみ）:
  1. **付値関数 v_M は建てない**。フィルトレーションは π₉ 冪の**可除性形式**（∃c, y=π₉ⁿ·c）で
     与える。完備化・位相・一般元 x∈O_M の v_π はゼロ。
  2. **G_i の定義は一様化子 π₉ への作用**（i_G(σ)=v(σπ−π) 形）。O_M=O_{L₂}[π₉] の単生成性から
     標準定義と一致するが、任意 x に対する σx−x の一様可除性との同値は形式化しない。
  3. **拡大 1 個（M/L₂）・下付き番号のみ**。上付き番号・Herbrand φ/ψ の実版・実 Hasse–Arf（B4）・
     Artin 導手の実表現論（B3）はゼロ——wcd/ajw/hau の Nat 模型が引き続きそれを担う。
  4. **3=π₉⁶·u₆・e=6 は q9ps 成果の消費**。d(M/ℚ₃)=9 の合成 different（推移公式）は範囲外。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3KummerPiSplit
import IUT.Q3KummerCubeIdent
import IUT.Q3TateCurveL9
import IUT.Q3LocalField
import IUT.WildConductorDiscriminant

namespace IUT

/-! ## q9wr-0: 単数論の補助（embed 単数・N(−x)=N(x)・ζ₃+1 単数・3·s は非単数） -/

/-- embed(n) が単数（N(embed n)=n³ が実 q3rq-単数）。 -/
theorem q9wr_embed_unit (n : q3rqCar) (hn : q3rqUnitMem n) : q3kUnitMem (q3kEmbed n) := by
  show q3rqUnitMem (q3kNormBase (q3kEmbed n))
  rw [q9ps_normBase_embed]
  exact q3rq_unit_mul (q3rq_unit_mul hn hn) hn

/-- N(−x) = N(x)（a²+3b² は符号反転で不変）。 -/
theorem q9wr_norm_neg (x : q3rqCar) : q3rqNorm (q3rqNeg x) = q3rqNorm x := by
  show z3.add (z3.mul (z3.neg x.1) (z3.neg x.1))
        (z3.neg (z3.mul q3rqD (z3.mul (z3.neg x.2) (z3.neg x.2))))
     = z3.add (z3.mul x.1 x.1) (z3.neg (z3.mul q3rqD (z3.mul x.2 x.2)))
  rw [z3.neg_mul x.1 (z3.neg x.1), z3.mul_neg x.1 x.1, z3.neg_neg,
      z3.neg_mul x.2 (z3.neg x.2), z3.mul_neg x.2 x.2, z3.neg_neg]

/-- **ζ₃+1 は実単数**（ζ₃+1 = −ζ₃²・N(−ζ₃²)=N(ζ₃²)=N(ζ₃)²=1）。 -/
theorem q9wr_zeta_add_one_unit : q3rqUnitMem (q3rqAdd q3rqZeta q3rqOne) := by
  show IsZpUnit 3 (q3rqNorm (q3rqAdd q3rqZeta q3rqOne))
  have hz : q3rqAdd q3rqZeta q3rqOne = q3rqNeg q3rqZetaSq := q9ps_zeta_add_one
  rw [hz, q9wr_norm_neg]
  show IsZpUnit 3 (q3rqNorm (q3rqMul q3rqZeta q3rqZeta))
  rw [q3rq_norm_mul, q3rq_zeta_norm, z3.one_mul z3.one]
  exact ⟨1, rfl, not_dvd_one 3 (by omega)⟩

/-- **3·s は ℤ₃-単数でない**（レベル 1 値が 3·k ≡ 0 mod 3 で矛盾）。 -/
theorem q9wr_three_mul_not_unit (s : z3.carrier) : ¬ IsZpUnit 3 (z3.mul q3rqThree s) := by
  intro h
  obtain ⟨a, ha, hpa⟩ := h
  obtain ⟨k, hk⟩ := Quot.exists_rep (s.val 1)
  have hmul : (z3.mul q3rqThree s).val 1 = Quot.mk (modCong (3 ^ 1)).rel (3 * k) :=
    q3mc_mul_val1 q3rqThree s 3 k (q3rq_three_val 1) hk.symm
  rw [hmul] at ha
  have hd := quot_exact intGrp (modCong (3 ^ 1)) ha
  rw [Nat.pow_one] at hd
  apply hpa
  obtain ⟨c, hc⟩ := hd
  exact ⟨k - c, by omega⟩

/-! ## q9wr-1: N(π₉) = ζ₃−1 と q3rqNorm(ζ₃−1) = 3 -/

/-- **N(π₉) = ζ₃−1 = −1+ζ₃**（3 次ノルムを π₉=(−1,1,0) で計算）。 -/
theorem q9wr_normBase_pi9 :
    q3kNormBase q9psPi9 = q3rqAdd (q3rqNeg q3rqOne) q3rqZeta := by
  rw [q9ps_pi9_coords]
  show q3rqAdd
      (q3rqAdd
        (q3rqAdd (q3rqMul (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne)) (q3rqNeg q3rqOne))
          (q3rqMul q3rqZeta (q3rqMul (q3rqMul q3rqOne q3rqOne) q3rqOne)))
        (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul q3rqZero q3rqZero) q3rqZero)))
      (q3rqNeg (q3rqMul q3kThree
        (q3rqMul q3rqZeta (q3rqMul (q3rqMul (q3rqNeg q3rqOne) q3rqOne) q3rqZero))))
    = q3rqAdd (q3rqNeg q3rqOne) q3rqZeta
  rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q3k_Z_eq,
      q9ps_neg1_cube, q9ps_c0b, q9ps_c0c,
      q3rqRing.mul_zero (q3rqRing.mul (q3rqRing.neg q3rqRing.one) q3rqRing.one),
      q3rqRing.mul_zero q3rqZeta,
      q3rqRing.mul_zero q3kThree,
      q3rqRing.neg_zero,
      q3rqRing.add_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZeta),
      q3rqRing.add_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZeta)]

/-- **q3rqNorm(ζ₃−1) = 3**（−1+ζ₃=(−1−h,h)・N=(−1−h)²+3h²=9/4+3/4=3・実計算）。 -/
theorem q9wr_qnorm_zeta_sub :
    q3rqNorm (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) = q3rqThree := by
  show z3.add
      (z3.mul (z3.add (z3.neg z3.one) (z3.neg q3rqHalf))
              (z3.add (z3.neg z3.one) (z3.neg q3rqHalf)))
      (z3.neg (z3.mul q3rqD
        (z3.mul (z3.add (z3.neg z3.zero) q3rqHalf)
                (z3.add (z3.neg z3.zero) q3rqHalf))))
    = q3rqThree
  rw [z3.neg_zero, z3.zero_add q3rqHalf,
      q3rq_D_eq, z3.neg_mul q3rqThree (z3.mul q3rqHalf q3rqHalf), z3.neg_neg,
      q3rq_three_hsq,
      z3.right_distrib (z3.neg z3.one) (z3.neg q3rqHalf)
        (z3.add (z3.neg z3.one) (z3.neg q3rqHalf)),
      z3.neg_mul z3.one (z3.add (z3.neg z3.one) (z3.neg q3rqHalf)),
      z3.one_mul (z3.add (z3.neg z3.one) (z3.neg q3rqHalf)),
      z3.neg_add_dist (z3.neg z3.one) (z3.neg q3rqHalf),
      z3.neg_neg z3.one, z3.neg_neg q3rqHalf,
      z3.neg_mul q3rqHalf (z3.add (z3.neg z3.one) (z3.neg q3rqHalf)),
      z3.left_distrib q3rqHalf (z3.neg z3.one) (z3.neg q3rqHalf),
      z3.mul_neg q3rqHalf z3.one, z3.mul_one q3rqHalf,
      z3.mul_neg q3rqHalf q3rqHalf,
      z3.neg_add_dist (z3.neg q3rqHalf) (z3.neg (z3.mul q3rqHalf q3rqHalf)),
      z3.neg_neg q3rqHalf, z3.neg_neg (z3.mul q3rqHalf q3rqHalf)]
  -- goal: ((one+H)+(H+H2)) + (H+H2) = 3
  rw [z3.add_assoc (z3.add z3.one q3rqHalf)
        (z3.add q3rqHalf (z3.mul q3rqHalf q3rqHalf))
        (z3.add q3rqHalf (z3.mul q3rqHalf q3rqHalf)),
      z3.add_assoc q3rqHalf (z3.mul q3rqHalf q3rqHalf)
        (z3.add q3rqHalf (z3.mul q3rqHalf q3rqHalf)),
      z3.add_comm (z3.mul q3rqHalf q3rqHalf)
        (z3.add q3rqHalf (z3.mul q3rqHalf q3rqHalf)),
      z3.add_assoc q3rqHalf (z3.mul q3rqHalf q3rqHalf) (z3.mul q3rqHalf q3rqHalf),
      q3rq_hsq_add_hsq,
      q3rq_half_add_half,
      z3.add_assoc z3.one q3rqHalf (z3.add q3rqHalf z3.one),
      ← z3.add_assoc q3rqHalf q3rqHalf z3.one,
      q3rq_half_add_half]
  exact (z3.add_assoc z3.one z3.one z3.one).symm

/-! ## q9wr-2: u\* の定義と実単数性（U2） -/

/-- **U2: u\* = w⁻¹·embed(ζ₃+1)·Y**（実閉形式単数）。 -/
def q9wrUStar : q3kCar :=
  q3kMul (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne))) q3kZeta9

/-- **U2: u\* は実単数**（w⁻¹・embed(ζ₃+1)・Y 各実単数の積）。 -/
theorem q9wr_ustar_unit : q3kUnitMem q9wrUStar :=
  q3k_unit_mul
    (q3k_unit_mul (q3k_unit_inv q9psW q9ps_w_unit)
      (q9wr_embed_unit (q3rqAdd q3rqZeta q3rqOne) q9wr_zeta_add_one_unit))
    q9tl_zeta9_unit

/-- **u\*\* = w⁻¹·embed((ζ₃+1)²)·Y**（σ² 側の実閉形式単数）。 -/
def q9wrUStarStar : q3kCar :=
  q3kMul (q3kMul q9psWinv
    (q3kEmbed (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne)))) q3kZeta9

/-- u\*\* は実単数。 -/
theorem q9wr_ustarstar_unit : q3kUnitMem q9wrUStarStar :=
  q3k_unit_mul
    (q3k_unit_mul (q3k_unit_inv q9psW q9ps_w_unit)
      (q9wr_embed_unit _
        (q3rq_unit_mul q9wr_zeta_add_one_unit q9wr_zeta_add_one_unit)))
    q9tl_zeta9_unit

/-! ## q9wr-3: U1 座標計算 σ(π₉)−π₉ = embed(ζ₃−1)·Y -/

/-- **U1: σ(π₉)−π₉ = embed(−1+ζ₃)·Y**（座標計算）。 -/
theorem q9wr_sigma_pi_sub :
    q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)
      = q3kMul (q3kEmbed (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta)) q3kZeta9 := by
  rw [q9ps_pi9_coords]
  apply q3k_ext
  · show q3rqAdd (q3rqNeg q3rqOne) (q3rqNeg (q3rqNeg q3rqOne))
       = q3rqAdd (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) q3rqZero)
           (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero q3rqZero) (q3rqMul q3rqZero q3rqOne)))
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q3k_Z_eq,
        q3rqRing.neg_neg q3rqRing.one,
        q3rqRing.neg_add q3rqRing.one,
        q3rqRing.mul_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZeta),
        q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.zero_mul q3rqRing.one,
        q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero q3rqRing.zero]
  · show q3rqAdd (q3rqMul q3rqZeta q3rqOne) (q3rqNeg q3rqOne)
       = q3rqAdd (q3rqAdd (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) q3rqOne)
             (q3rqMul q3rqZero q3rqZero))
           (q3rqMul q3rqZeta (q3rqMul q3rqZero q3rqZero))
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q3k_Z_eq,
        q3rqRing.mul_one q3rqZeta,
        q3rqRing.mul_one (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZeta),
        q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.add_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZeta),
        q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZeta),
        q3rqRing.add_comm q3rqZeta (q3rqRing.neg q3rqRing.one)]
  · show q3rqAdd (q3rqMul q3rqZetaSq q3rqZero) (q3rqNeg q3rqZero)
       = q3rqAdd (q3rqAdd (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) q3rqZero)
             (q3rqMul q3rqZero q3rqOne))
           (q3rqMul q3rqZero q3rqZero)
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q3k_Z_eq,
        q3rqRing.mul_zero q3rqZetaSq,
        q3rqRing.neg_zero,
        q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.mul_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZeta),
        q3rqRing.zero_mul q3rqRing.one,
        q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.add_zero q3rqRing.zero]

/-! ## q9wr-4: U3（★ 実野性分岐の核） σ(π₉)−π₉ = π₉³·u\* -/

/-- **U3（★）: σ(π₉)−π₉ = π₉³·u\***。q9ps_pi9_cube・q9ps_coord0・q9ps_w_inv_mul を消費。 -/
theorem q9wr_sigma_pi_eq :
    q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)
      = q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9wrUStar := by
  rw [q9wr_sigma_pi_sub, q9ps_pi9_cube]
  have hrr :
      q3kMul (q3kMul (q3kEmbed q3rqLambda) q9psW)
        (q3kMul (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne))) q3kZeta9)
      = q3kMul (q3kMul (q3kEmbed q3rqLambda) (q3kEmbed (q3rqAdd q3rqZeta q3rqOne))) q3kZeta9 := by
    rw [q3k_mul_assoc q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne)) q3kZeta9,
        ← q3k_mul_assoc (q3kMul (q3kEmbed q3rqLambda) q9psW) q9psWinv
            (q3kMul (q3kEmbed (q3rqAdd q3rqZeta q3rqOne)) q3kZeta9),
        q3k_mul_assoc (q3kEmbed q3rqLambda) q9psW q9psWinv,
        q9ps_w_inv_mul,
        q3k_mul_comm (q3kEmbed q3rqLambda) q3kOne,
        q3k_one_mul (q3kEmbed q3rqLambda),
        ← q3k_mul_assoc (q3kEmbed q3rqLambda) (q3kEmbed (q3rqAdd q3rqZeta q3rqOne)) q3kZeta9]
  show q3kMul (q3kEmbed (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta)) q3kZeta9
     = q3kMul (q3kMul (q3kEmbed q3rqLambda) q9psW)
         (q3kMul (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne))) q3kZeta9)
  rw [hrr, q3k_embed_mul q3rqLambda (q3rqAdd q3rqZeta q3rqOne)]
  have hAB : q3rqAdd (q3rqNeg q3rqOne) q3rqZeta
      = q3rqMul q3rqLambda (q3rqAdd q3rqZeta q3rqOne) := q9ps_coord0.symm
  rw [hAB]

/-! ## q9wr-5: U1'/U4 σ²(π₉)−π₉ = π₉³·u\*\* -/

/-- ζ₃²−1 = λ·(ζ₃+1)²（q9ps_coord0 × (ζ₃+1) の一行）。 -/
theorem q9wr_coord0_sq :
    q3rqMul q3rqLambda (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne))
      = q3rqAdd (q3rqNeg q3rqOne) q3rqZetaSq := by
  rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq,
      ← q3rqRing.mul_assoc q3rqLambda (q3rqRing.add q3rqZeta q3rqRing.one)
        (q3rqRing.add q3rqZeta q3rqRing.one),
      q9ps_coord0,
      q3rqRing.right_distrib (q3rqRing.neg q3rqRing.one) q3rqZeta
        (q3rqRing.add q3rqZeta q3rqRing.one),
      q3rqRing.neg_mul q3rqRing.one (q3rqRing.add q3rqZeta q3rqRing.one),
      q3rqRing.one_mul (q3rqRing.add q3rqZeta q3rqRing.one),
      q3rqRing.left_distrib q3rqZeta q3rqZeta q3rqRing.one,
      q3rqRing.mul_one q3rqZeta,
      q3k_z_zR,
      q3rqRing.neg_add_dist q3rqZeta q3rqRing.one,
      q3rqRing.add_assoc (q3rqRing.neg q3rqZeta) (q3rqRing.neg q3rqRing.one)
        (q3rqRing.add q3rqZetaSq q3rqZeta),
      ← q3rqRing.add_assoc (q3rqRing.neg q3rqRing.one) q3rqZetaSq q3rqZeta,
      q3rqRing.add_comm (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZetaSq) q3rqZeta,
      ← q3rqRing.add_assoc (q3rqRing.neg q3rqZeta) q3rqZeta
        (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZetaSq),
      q3rqRing.neg_add q3rqZeta,
      q3rqRing.zero_add (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZetaSq)]

/-- **U1': σ²(π₉)−π₉ = embed(−1+ζ₃²)·Y**（座標計算）。 -/
theorem q9wr_sigma2_pi_sub :
    q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)
      = q3kMul (q3kEmbed (q3rqAdd (q3rqNeg q3rqOne) q3rqZetaSq)) q3kZeta9 := by
  rw [q9ps_pi9_coords]
  apply q3k_ext
  · show q3rqAdd (q3rqNeg q3rqOne) (q3rqNeg (q3rqNeg q3rqOne))
       = q3rqAdd (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZetaSq) q3rqZero)
           (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero q3rqZero) (q3rqMul q3rqZero q3rqOne)))
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q3k_Z_eq,
        q3rqRing.neg_neg q3rqRing.one,
        q3rqRing.neg_add q3rqRing.one,
        q3rqRing.mul_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZetaSq),
        q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.zero_mul q3rqRing.one,
        q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero q3rqRing.zero]
  · show q3rqAdd (q3rqMul q3rqZetaSq q3rqOne) (q3rqNeg q3rqOne)
       = q3rqAdd (q3rqAdd (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZetaSq) q3rqOne)
             (q3rqMul q3rqZero q3rqZero))
           (q3rqMul q3rqZeta (q3rqMul q3rqZero q3rqZero))
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q3k_Z_eq,
        q3rqRing.mul_one q3rqZetaSq,
        q3rqRing.mul_one (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZetaSq),
        q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.add_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZetaSq),
        q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZetaSq),
        q3rqRing.add_comm q3rqZetaSq (q3rqRing.neg q3rqRing.one)]
  · show q3rqAdd (q3rqMul q3rqZeta q3rqZero) (q3rqNeg q3rqZero)
       = q3rqAdd (q3rqAdd (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZetaSq) q3rqZero)
             (q3rqMul q3rqZero q3rqOne))
           (q3rqMul q3rqZero q3rqZero)
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q3k_Z_eq,
        q3rqRing.mul_zero q3rqZeta,
        q3rqRing.neg_zero,
        q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.mul_zero (q3rqRing.add (q3rqRing.neg q3rqRing.one) q3rqZetaSq),
        q3rqRing.zero_mul q3rqRing.one,
        q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.add_zero q3rqRing.zero]

/-- **U4: σ²(π₉)−π₉ = π₉³·u\*\***。 -/
theorem q9wr_sigma2_pi_eq :
    q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)
      = q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9wrUStarStar := by
  rw [q9wr_sigma2_pi_sub, q9ps_pi9_cube]
  have hrr :
      q3kMul (q3kMul (q3kEmbed q3rqLambda) q9psW)
        (q3kMul (q3kMul q9psWinv
          (q3kEmbed (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne)))) q3kZeta9)
      = q3kMul (q3kMul (q3kEmbed q3rqLambda)
          (q3kEmbed (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne)))) q3kZeta9 := by
    rw [q3k_mul_assoc q9psWinv
          (q3kEmbed (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne))) q3kZeta9,
        ← q3k_mul_assoc (q3kMul (q3kEmbed q3rqLambda) q9psW) q9psWinv
            (q3kMul (q3kEmbed (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne)))
              q3kZeta9),
        q3k_mul_assoc (q3kEmbed q3rqLambda) q9psW q9psWinv,
        q9ps_w_inv_mul,
        q3k_mul_comm (q3kEmbed q3rqLambda) q3kOne,
        q3k_one_mul (q3kEmbed q3rqLambda),
        ← q3k_mul_assoc (q3kEmbed q3rqLambda)
            (q3kEmbed (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne))) q3kZeta9]
  show q3kMul (q3kEmbed (q3rqAdd (q3rqNeg q3rqOne) q3rqZetaSq)) q3kZeta9
     = q3kMul (q3kMul (q3kEmbed q3rqLambda) q9psW)
         (q3kMul (q3kMul q9psWinv
           (q3kEmbed (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne)))) q3kZeta9)
  rw [hrr, q3k_embed_mul q3rqLambda (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne))]
  have hAB : q3rqAdd (q3rqNeg q3rqOne) q3rqZetaSq
      = q3rqMul q3rqLambda (q3rqMul (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd q3rqZeta q3rqOne)) :=
    q9wr_coord0_sq.symm
  rw [hAB]

/-! ## q9wr-6: U5 下付きフィルトレーション（可除性形式） -/

/-- 可除性 d ∣ x（∃c, x = d·c）。付値関数を建てない B1 正直限定に整合。 -/
def q9wrDvd (d x : q3kCar) : Prop := ∃ c : q3kCar, x = q3kMul d c

/-- **U5: π₉³ ∣ (σᵏπ₉−π₉) (k=1,2)**（σ,σ²∈G₂ の下付きフィルトレーション）。 -/
theorem q9wr_G2_mem :
    q9wrDvd (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
      (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
    ∧ q9wrDvd (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
      (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)) :=
  ⟨⟨q9wrUStar, q9wr_sigma_pi_eq⟩, ⟨q9wrUStarStar, q9wr_sigma2_pi_eq⟩⟩

/-! ## q9wr-7: U6 break の上界 ¬ π₉⁴ ∣ (σπ₉−π₉) -/

/-- π₉ 正則性による相殺: π₉·a = π₉·b ⟹ a = b（q9ci_pi9_reg 消費）。 -/
theorem q9wr_pi9_cancel {a b : q3kCar}
    (h : q3kMul q9psPi9 a = q3kMul q9psPi9 b) : a = b := by
  have hmn : q3kMul q9psPi9 (q3kNeg b) = q3kNeg (q3kMul q9psPi9 b) := by
    rw [q3k_kM_eq, q9ps_kN_eq, q3kRing.mul_neg q9psPi9 b]
  have hz : q3kMul q9psPi9 (q3kAdd a (q3kNeg b)) = q3kZero := by
    rw [q3k_left_distrib q9psPi9 a (q3kNeg b), hmn, h]
    exact q3kRing.add_neg (q3kMul q9psPi9 b)
  have hab : q3kAdd a (q3kNeg b) = q3kZero := q9ci_pi9_reg (q3kAdd a (q3kNeg b)) hz
  have h1 : q3kRing.neg a = q3kRing.neg b := q3kRing.neg_eq_of_add_eq_zero hab
  have h2 := congrArg q3kRing.neg h1
  rw [q3kRing.neg_neg, q3kRing.neg_neg] at h2
  exact h2

/-- π₉³ 正則性による相殺: π₉³·a = π₉³·b ⟹ a = b。 -/
theorem q9wr_pi3_cancel {a b : q3kCar}
    (h : q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) a
       = q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) b) : a = b := by
  rw [q3k_mul_assoc (q3kMul q9psPi9 q9psPi9) q9psPi9 a,
      q3k_mul_assoc q9psPi9 q9psPi9 (q3kMul q9psPi9 a),
      q3k_mul_assoc (q3kMul q9psPi9 q9psPi9) q9psPi9 b,
      q3k_mul_assoc q9psPi9 q9psPi9 (q3kMul q9psPi9 b)] at h
  exact q9wr_pi9_cancel (q9wr_pi9_cancel (q9wr_pi9_cancel h))

/-- **U6（★ break 上界）: ¬ π₉⁴ ∣ (σπ₉−π₉)**。π₉ 正則消去→ノルム 2 段→3·s は非単数で矛盾。 -/
theorem q9wr_G3_trivial :
    ¬ q9wrDvd (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psPi9)
        (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)) := by
  intro hd
  obtain ⟨x, hx⟩ := hd
  have hcomb : q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9wrUStar
      = q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) (q3kMul q9psPi9 x) := by
    have hcc := q9wr_sigma_pi_eq.symm.trans hx
    rw [q3k_mul_assoc (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psPi9 x] at hcc
    exact hcc
  have hux : q9wrUStar = q3kMul q9psPi9 x := q9wr_pi3_cancel hcomb
  have hnorm : q3kNormBase q9wrUStar
      = q3rqMul (q3kNormBase q9psPi9) (q3kNormBase x) := by
    rw [hux, q3k_normBase_mul q9psPi9 x]
  rw [q9wr_normBase_pi9] at hnorm
  have huu : IsZpUnit 3 (q3rqNorm (q3kNormBase q9wrUStar)) := q9wr_ustar_unit
  rw [hnorm, q3rq_norm_mul, q9wr_qnorm_zeta_sub] at huu
  exact q9wr_three_mul_not_unit (q3rqNorm (q3kNormBase x)) huu

/-! ## q9wr-8: U7 実分岐フィルトレーション（break t=2） -/

/-- **U7: break t=2 の実分岐フィルトレーション**——σ,σ²∈G₂（π₉³∣）かつ σ∉G₃（¬π₉⁴∣）。 -/
theorem q9wr_break :
    q9wrDvd (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
      (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
    ∧ q9wrDvd (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
      (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))
    ∧ ¬ q9wrDvd (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psPi9)
        (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)) :=
  ⟨q9wr_G2_mem.1, q9wr_G2_mem.2, q9wr_G3_trivial⟩

/-! ## q9wr-9: U8 実 different d(M/L₂)=6 -/

/-- **U8: (σπ₉−π₉)(σ²π₉−π₉) = π₉⁶·(u\*·u\*\*)**＝実 different 生成元・d(M/L₂)=6。 -/
theorem q9wr_different :
    q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
           (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))
      = q3kMul q9psPi6 (q3kMul q9wrUStar q9wrUStarStar) := by
  rw [q9wr_sigma_pi_eq, q9wr_sigma2_pi_eq]
  show q3kMul (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9wrUStar)
        (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9wrUStarStar)
     = q3kMul (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
          (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)) (q3kMul q9wrUStar q9wrUStarStar)
  rw [q3k_kM_eq]
  exact q3kRing.mul_mul_mul_comm
      (q3kRing.mul (q3kRing.mul q9psPi9 q9psPi9) q9psPi9) q9wrUStar
      (q3kRing.mul (q3kRing.mul q9psPi9 q9psPi9) q9psPi9) q9wrUStarStar

/-! ## q9wr-10: U9 Nat 階段模型 wcd との genuine cross-check -/

/-- **U9: Nat 階段模型 wcdRamGroups 3 2（M441F）との cross-check**。
    実側 U7/U8 が実現する階段 |G₀|=|G₁|=|G₂|=3, |G₃|=1・d=6 を Nat 模型が同値に持つ。 -/
theorem q9wr_matches_wcd :
    wcdDiffSum (wcdRamGroups 3 2) 2 = 6
    ∧ wcdRamGroups 3 2 0 = 3 ∧ wcdRamGroups 3 2 1 = 3
    ∧ wcdRamGroups 3 2 2 = 3 ∧ wcdRamGroups 3 2 3 = 1 :=
  ⟨rfl, wcd_ram_zero 3 2, wcd_ram_le 3 1 2 (by omega),
    wcd_ram_le 3 2 2 (by omega), wcd_ram_gt 3 3 2 (by omega)⟩

/-! ## q9wr-11: capstone -/

/-- **U10: 実野性分岐フィルトレーションデータ**——実 σ の break t=2・実 different d=6・
    Nat 模型 cross-check を束ねる（新規証明ゼロ・束ねのみ）。 -/
structure Q3WildRamFiltrationRealData where
  /-- σ(π₉)−π₉ = π₉³·u\*（実野性分岐の核）。 -/
  sigma_pi : q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)
    = q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9wrUStar
  /-- σ²(π₉)−π₉ = π₉³·u\*\*。 -/
  sigma2_pi : q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)
    = q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9wrUStarStar
  /-- u\* は実単数。 -/
  ustar_unit : q3kUnitMem q9wrUStar
  /-- σ,σ²∈G₂（π₉³∣）。 -/
  g2_sigma : q9wrDvd (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
    (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
  /-- σ∉G₃（break の上界 ¬π₉⁴∣）。 -/
  g3_trivial : ¬ q9wrDvd (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psPi9)
    (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
  /-- 実 different (σπ₉−π₉)(σ²π₉−π₉) = π₉⁶·(u\*·u\*\*)。 -/
  different : q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
      (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))
    = q3kMul q9psPi6 (q3kMul q9wrUStar q9wrUStarStar)
  /-- Nat 階段模型 d=6 の cross-check。 -/
  wcd_diff : wcdDiffSum (wcdRamGroups 3 2) 2 = 6

/-- **見出し実例** — 実 Gal(M/L₂) の break t=2・different d=6 の実野性分岐フィルトレーション。 -/
def q9wr_data : Q3WildRamFiltrationRealData where
  sigma_pi := q9wr_sigma_pi_eq
  sigma2_pi := q9wr_sigma2_pi_eq
  ustar_unit := q9wr_ustar_unit
  g2_sigma := q9wr_G2_mem.1
  g3_trivial := q9wr_G3_trivial
  different := q9wr_different
  wcd_diff := q9wr_matches_wcd.1

/-- **実野性分岐フィルトレーションの存在**（実 σ・実 O_M・break t=2・d=6）。 -/
theorem q9wr_exists : Nonempty Q3WildRamFiltrationRealData := ⟨q9wr_data⟩

end IUT
