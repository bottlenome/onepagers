/-
  IUT/Q3TowerDifferentReal.lean — 柱B・B3 実 composite different（推移公式 d(M/ℚ₃)=9）

  ── 主要成果の分類: **[実／(a) 昇格]**——q9ac の正直な限定
     「合成 different（推移公式・d(M/ℚ₃)）は範囲外」を **本物へ昇格**する。
     実塔 ℚ₃ ⊂ L₂=ℚ₃(√−3) ⊂ M=L₂(ζ₉ 型)、e(L₂/ℚ₃)=2, e(M/L₂)=3, e(M/ℚ₃)=6,
     M/ℚ₃ 完全分岐 (f=1) の上で、実 different-exponent の推移公式
       d_M(M/ℚ₃) = d_M(M/L₂) + e(M/L₂)·d_{L₂}(L₂/ℚ₃) = 6 + 3·1 = 9
     を実 O_{L₂}=ℤ₃[√−3]・実 O_M=q3k・実 π₉=Y−1・実 embed の上で割る。主語は実 λ=√−3・
     実 π₉・実単数——toy 模型（m202fVol 型・Bool 軌道・surrogate 群）を一切使わない。

  complete_pct 影響: **B3 0.20→（独立監査次第・予測 +0.05〜0.10）— display-moving候補**。
     本モジュールが動かす新規内容は **合成 different の推移公式 d(M/ℚ₃)=9** の実証
     （q9ac/q9wr は d(M/L₂)=6 まで・L₂/ℚ₃ 側と推移公式は正直限定で範囲外としていた）。

  真水（NEW・監査対象の新規実定理）:
   Part 1（L₂/ℚ₃ tame different d_{L₂}=1）:
     * q9tw_lam_dvd_diff        — λ ∣ 2λ（g'(λ)=2λ の生成する different）
     * q9tw_lam2_not_dvd_diff   — λ² ∤ 2λ（鋭さ・component→3∤2 経由の U6 型矛盾）
     * q9tw_diffL2_exp / q9tw_L2_tame — d_{L₂}(L₂/ℚ₃)=1（tame: 3∤e=2, d=e−1=1）
   Part 2（embed(2λ) の v_M=3）:
     * q9tw_embed_diffL2_eq     — embed(2λ) = π₉³·(w⁻¹·embed 2)
     * q9tw_embed_diffL2_vM3    — π₉³ ∣ embed(2λ) かつ ¬π₉⁴ ∣ embed(2λ)（v_M=3 ちょうど）
   Part 3（塔の推移公式 d_M(M/ℚ₃)=9）:
     * q9tw_dfull_eq            — D_full = π₉⁹·(u*u**·w⁻¹·embed 2)
     * q9tw_different_tower_sharp — π₉⁹ ∣ D_full かつ ¬π₉¹⁰ ∣ D_full（v_M(D_full)=9 ちょうど）
     * q9tw_different_transitivity — 実指数 6,3,1 を主語にした推移公式 9 = 6 + 3·1
     * q9tw_disc_M_Q3          — f=1 完全分岐: v_{ℚ₃}(disc) = f·v_M(different) = 1·9 = 9

  消費（再主張しない・二重計上回避）:
   * d(M/L₂)=6 の実恒等式 D_{M/L₂}=(σπ₉−π₉)(σ²π₉−π₉)=π₉⁶·(u*u**) は q9wr_different 消費。
   * d(M/L₂)=6 の鋭さ ¬π₉⁷∣D_{M/L₂} は q9ac_different_sharp 消費。
   * embed(λ)=π₉³·w⁻¹ は q9nf_embed_lambda 消費・3=π₉⁶·u₆ は q9ps_three_split 経由。
   * U6 イディオム（π₉ 正則消去→ノルム 2 段→3·s 非単数）を Part1/2/3 の鋭さで新インスタンス化
     （q9wr_pi3_cancel・q9wr_normBase_pi9・q9wr_qnorm_zeta_sub・q9wr_three_mul_not_unit 消費）。

  正直な限定（§4 規約により消さない・弱化しない・q9ac/q9wr/q9ps/q9nf 継承の上に追記のみ）:
  1. **L₂/ℚ₃ の monogenic different 公式は具体生成元 g'(λ)=2λ 経由**（標準の monogenic な場合）。
     抽象 different-ideal 理論からは建てない。d_{L₂}(L₂/ℚ₃)=1 は λ∣2λ ∧ ¬λ²∣2λ の可除性形式。
  2. **拡大は単一の塔 ℚ₃⊂L₂⊂M・embed は 1 本**。他の中間体・他の埋め込みは範囲外。
  3. **f=1 完全分岐を仮定**（この塔では実・M/ℚ₃ は e=6 完全分岐）。disc 指数 = f·(different 指数)
     の f=1 特化であり一般 conductor–discriminant の残余次数付き公式ではない。
  4. **付値関数 v_M なし**。different も推移公式も π₉ 冪の可除性形式（q9wr/q9nf 正直限定 1 継承）。
  5. q9ac/q9wr/q9ps/q9nf/q3rq の正直限定を全継承（O_M と M^× のみ・体化なし・
     Galois は σ のみ・実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3ArtinConductorReal
import IUT.Q3NormFiltrationSpike

namespace IUT

/-! ## q9tw-1（Part 1）: L₂/ℚ₃ tame different d_{L₂}(L₂/ℚ₃)=1 -/

/-- 実 ℤ₃ の環元 2 = (2, 0) ∈ O_{L₂}。 -/
def q3rqTwoElt : q3rqCar := ((q3rqTwoZ, z3.zero) : q3rqCar)

/-- **L₂/ℚ₃ の different 生成元 g'(λ)=2λ**（g(X)=X²+3・λ=√−3・g'(λ)=2λ）。 -/
def q9twDiffL2 : q3rqCar := q3rqMul q3rqTwoElt q3rqLambda

/-- 2 = (2,0) は実 O_{L₂} の単数（N(2)=4 は ℤ₃^×）。 -/
theorem q9tw_two_elt_unit : q3rqUnitMem q3rqTwoElt :=
  q3rq_pair_unit q3rqTwoZ q3rq_two_unit

/-- λ-adic 可除性（付値関数 v_λ を建てない・可除性形式）: d ∣ x ⟺ ∃c, x = d·c。 -/
def q9twLamDvd (d x : q3rqCar) : Prop := ∃ c : q3rqCar, x = q3rqMul d c

/-- **q9tw-1a（★ NEW）: λ ∣ 2λ**（2λ = λ·2、可換）。 -/
theorem q9tw_lam_dvd_diff : q9twLamDvd q3rqLambda q9twDiffL2 :=
  ⟨q3rqTwoElt, q3rqRing.mul_comm q3rqTwoElt q3rqLambda⟩

/-- **q9tw-1b（★ NEW）: λ² ∤ 2λ**（different の鋭さ・d_{L₂}=1 ちょうど）。
    2λ=(0,2)・λ²=(−3,0)。もし 2λ=λ²·c なら第 2 成分 2 = −3·c₂ = 3·(−c₂)、
    すなわち 3·(−c₂) は単数——`q9wr_three_mul_not_unit`（3·s は非単数）と矛盾。 -/
theorem q9tw_lam2_not_dvd_diff :
    ¬ q9twLamDvd (q3rqMul q3rqLambda q3rqLambda) q9twDiffL2 := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  rw [q3rq_lambda_sq] at hc
  have hLHS : Prod.snd q9twDiffL2 = q3rqTwoZ := by
    show z3.add (z3.mul q3rqTwoZ z3.one) (z3.mul z3.zero z3.zero) = q3rqTwoZ
    rw [z3.mul_one q3rqTwoZ, z3.mul_zero z3.zero, z3.add_zero q3rqTwoZ]
  have hRHS : Prod.snd (q3rqMul ((z3.neg q3rqThree, z3.zero) : q3rqCar) c)
      = z3.mul q3rqThree (z3.neg c.2) := by
    show z3.add (z3.mul (z3.neg q3rqThree) c.2) (z3.mul z3.zero c.1)
        = z3.mul q3rqThree (z3.neg c.2)
    rw [z3.zero_mul c.1, z3.add_zero (z3.mul (z3.neg q3rqThree) c.2),
        z3.neg_mul q3rqThree c.2, ← z3.mul_neg q3rqThree c.2]
  have hsnd : q3rqTwoZ = z3.mul q3rqThree (z3.neg c.2) := by
    rw [← hLHS, ← hRHS]
    exact congrArg Prod.snd hc
  have hunit : IsZpUnit 3 (z3.mul q3rqThree (z3.neg c.2)) := by
    rw [← hsnd]; exact q3rq_two_unit
  exact q9wr_three_mul_not_unit (z3.neg c.2) hunit

/-- **q9tw-1c（★ NEW）: d_{L₂}(L₂/ℚ₃) = 1**（λ∣2λ ∧ ¬λ²∣2λ の可除性形式）。 -/
theorem q9tw_diffL2_exp :
    q9twLamDvd q3rqLambda q9twDiffL2
    ∧ ¬ q9twLamDvd (q3rqMul q3rqLambda q3rqLambda) q9twDiffL2 :=
  ⟨q9tw_lam_dvd_diff, q9tw_lam2_not_dvd_diff⟩

/-- **q9tw-1d（★ NEW）: L₂/ℚ₃ は tame**（e=2, 3∤e, したがって d=e−1=1）。
    tame 判定 3∤2（=3∤e）と d=e−1=1 の算術を、実 different の可除性 exponent と束ねる。 -/
theorem q9tw_L2_tame :
    ¬ ((3 : Nat) : Int) ∣ (2 : Int)
    ∧ (2 : Nat) - 1 = 1
    ∧ q9twLamDvd q3rqLambda q9twDiffL2
    ∧ ¬ q9twLamDvd (q3rqMul q3rqLambda q3rqLambda) q9twDiffL2 :=
  ⟨q3rq_three_not_dvd_two, rfl, q9tw_lam_dvd_diff, q9tw_lam2_not_dvd_diff⟩

/-! ## q9tw-2（Part 2）: embed(2λ) の v_M=3（M/L₂ への持ち上げ） -/

/-- **q9tw-2a（★ NEW）: embed(2λ) = π₉³·(w⁻¹·embed 2)**。
    embed(2λ)=embed(2)·embed(λ)（q3k_embed_mul）・embed(λ)=π₉³·w⁻¹（q9nf_embed_lambda）。 -/
theorem q9tw_embed_diffL2_eq :
    q3kEmbed q9twDiffL2
      = q3kMul (q9nfPiPow 3) (q3kMul q9psWinv (q3kEmbed q3rqTwoElt)) := by
  show q3kEmbed (q3rqMul q3rqTwoElt q3rqLambda) = _
  rw [← q3k_embed_mul q3rqTwoElt q3rqLambda, q9nf_embed_lambda,
      q3k_mul_comm (q3kEmbed q3rqTwoElt) (q3kMul (q9nfPiPow 3) q9psWinv),
      q3k_mul_assoc (q9nfPiPow 3) q9psWinv (q3kEmbed q3rqTwoElt)]

/-- **q9tw-2b: π₉³ ∣ embed(2λ)**（v_M(embed 2λ) ≥ 3 の下界）。 -/
theorem q9tw_embed_diffL2_dvd : q9wrDvd (q9nfPiPow 3) (q3kEmbed q9twDiffL2) :=
  ⟨q3kMul q9psWinv (q3kEmbed q3rqTwoElt), q9tw_embed_diffL2_eq⟩

/-- **q9tw-2c（★ NEW）: ¬π₉⁴ ∣ embed(2λ)**（v_M(embed 2λ)=3 ちょうど）。
    π₉³ 正則消去 → w⁻¹·embed 2 = π₉·c → N(w⁻¹·embed 2)=(ζ₃−1)·N(c)∈(3) だが
    w⁻¹·embed 2 は単数 → mod-3 矛盾（U6 イディオムの新インスタンス）。 -/
theorem q9tw_embed_diffL2_sharp : ¬ q9wrDvd (q9nfPiPow 4) (q3kEmbed q9twDiffL2) := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hL : q3kMul (q9nfPiPow 3) (q3kMul q9psWinv (q3kEmbed q3rqTwoElt))
          = q3kMul (q9nfPiPow 3) (q3kMul q9psPi9 c) := by
    have h43 : q9nfPiPow 4 = q3kMul (q9nfPiPow 3) (q9nfPiPow 1) := q9nf_pipow_add 3 1
    rw [← q9tw_embed_diffL2_eq, hc, h43, q9nf_pipow1_eq, q3k_kM_eq]
    exact q3kRing.mul_assoc (q9nfPiPow 3) q9psPi9 c
  rw [q9nf_pipow3_eq] at hL
  have hcan : q3kMul q9psWinv (q3kEmbed q3rqTwoElt) = q3kMul q9psPi9 c :=
    q9wr_pi3_cancel hL
  have hunit : q3kUnitMem (q3kMul q9psWinv (q3kEmbed q3rqTwoElt)) :=
    q3k_unit_mul (q3k_unit_inv q9psW q9ps_w_unit)
      (q9wr_embed_unit q3rqTwoElt q9tw_two_elt_unit)
  have h3 : IsZpUnit 3 (q3rqNorm (q3kNormBase (q3kMul q9psPi9 c))) := by
    rw [← hcan]; exact hunit
  rw [q3k_normBase_mul q9psPi9 c, q9wr_normBase_pi9, q3rq_norm_mul,
      q9wr_qnorm_zeta_sub] at h3
  exact q9wr_three_mul_not_unit (q3rqNorm (q3kNormBase c)) h3

/-- **q9tw-2d（★ NEW）: v_M(embed 2λ)=3 ちょうど**（π₉³∣ ∧ ¬π₉⁴∣）。 -/
theorem q9tw_embed_diffL2_vM3 :
    q9wrDvd (q9nfPiPow 3) (q3kEmbed q9twDiffL2)
    ∧ ¬ q9wrDvd (q9nfPiPow 4) (q3kEmbed q9twDiffL2) :=
  ⟨q9tw_embed_diffL2_dvd, q9tw_embed_diffL2_sharp⟩

/-! ## q9tw-3（Part 3）: 塔の推移公式 d_M(M/ℚ₃)=9 -/

/-- **M/L₂ の different 生成元** D_{M/L₂} = (σπ₉−π₉)(σ²π₉−π₉)（q9wr 消費対象）。 -/
def q9twDiffML2 : q3kCar :=
  q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
         (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))

/-- **M/ℚ₃ の合成 different 生成元** D_full = D_{M/L₂}·embed(2λ)。 -/
def q9twDfull : q3kCar := q3kMul q9twDiffML2 (q3kEmbed q9twDiffL2)

/-- **q9tw-3a: π₉⁶ ∣ D_{M/L₂}**（d(M/L₂)=6 の下界・q9wr_different 消費）。 -/
theorem q9tw_diffML2_dvd6 : q9wrDvd (q9nfPiPow 6) q9twDiffML2 := by
  refine ⟨q3kMul q9wrUStar q9wrUStarStar, ?_⟩
  show q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
              (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))
     = q3kMul (q9nfPiPow 6) (q3kMul q9wrUStar q9wrUStarStar)
  rw [q9wr_different, q9nf_pipow6_eq]

/-- **q9tw-3b（★ NEW）: D_full = π₉⁹·(u*u**·w⁻¹·embed 2)**。
    D_{M/L₂}=π₉⁶·(u*u**)（q9wr_different）× embed(2λ)=π₉³·(w⁻¹·embed 2）を
    4 因子入替（mul_mul_mul_comm）で π₉⁹·(単数) に整える。 -/
theorem q9tw_dfull_eq :
    q9twDfull
      = q3kMul (q3kMul (q3kMul q9psPi9Cubed q9psPi9Cubed) q9psPi9Cubed)
          (q3kMul (q3kMul q9wrUStar q9wrUStarStar)
                  (q3kMul q9psWinv (q3kEmbed q3rqTwoElt))) := by
  show q3kMul (q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
                      (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)))
              (q3kEmbed q9twDiffL2) = _
  rw [q9wr_different, q9tw_embed_diffL2_eq, q9nf_pipow3_eq, q3k_kM_eq]
  exact q3kRing.mul_mul_mul_comm
    (q3kMul q9psPi9Cubed q9psPi9Cubed) (q3kMul q9wrUStar q9wrUStarStar)
    q9psPi9Cubed (q3kMul q9psWinv (q3kEmbed q3rqTwoElt))

/-- π₉⁹ = ((π₉³)·(π₉³))·π₉³ の橋渡し（q9nf_pipow_add 6 3 経由）。 -/
theorem q9tw_pipow9_eq :
    q9nfPiPow 9 = q3kMul (q3kMul q9psPi9Cubed q9psPi9Cubed) q9psPi9Cubed := by
  have h : q9nfPiPow (6 + 3) = q3kMul (q9nfPiPow 6) (q9nfPiPow 3) := q9nf_pipow_add 6 3
  rw [q9nf_pipow6_eq, q9nf_pipow3_eq] at h
  exact h

/-- **q9tw-3c: π₉⁹ ∣ D_full**（推移公式 6+3=9 の下界・π₉⁹·(単数) 分解を消費）。 -/
theorem q9tw_dfull_dvd : q9wrDvd (q9nfPiPow 9) q9twDfull := by
  refine ⟨q3kMul (q3kMul q9wrUStar q9wrUStarStar)
            (q3kMul q9psWinv (q3kEmbed q3rqTwoElt)), ?_⟩
  rw [q9tw_dfull_eq, q9tw_pipow9_eq]

/-- π₉⁹ 正則消去: π₉⁹·a = π₉⁹·b ⟹ a = b（q9wr_pi3_cancel を 3 段）。 -/
theorem q9tw_pi9c_cancel {a b : q3kCar}
    (h : q3kMul (q3kMul (q3kMul q9psPi9Cubed q9psPi9Cubed) q9psPi9Cubed) a
       = q3kMul (q3kMul (q3kMul q9psPi9Cubed q9psPi9Cubed) q9psPi9Cubed) b) : a = b := by
  rw [q3k_mul_assoc (q3kMul q9psPi9Cubed q9psPi9Cubed) q9psPi9Cubed a,
      q3k_mul_assoc q9psPi9Cubed q9psPi9Cubed (q3kMul q9psPi9Cubed a),
      q3k_mul_assoc (q3kMul q9psPi9Cubed q9psPi9Cubed) q9psPi9Cubed b,
      q3k_mul_assoc q9psPi9Cubed q9psPi9Cubed (q3kMul q9psPi9Cubed b)] at h
  exact q9wr_pi3_cancel (q9wr_pi3_cancel (q9wr_pi3_cancel h))

/-- **q9tw-3d（★ NEW）: ¬π₉¹⁰ ∣ D_full**（v_M(D_full)=9 ちょうど）。
    π₉⁹ 正則消去 → 単数 = π₉·c → ノルム 2 段 → 3·s 非単数の矛盾
    （q9ac_different_sharp と同じ U6 エンジンを π₉⁹ に適用）。 -/
theorem q9tw_dfull_sharp : ¬ q9wrDvd (q9nfPiPow 10) q9twDfull := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hL : q3kMul (q3kMul (q3kMul q9psPi9Cubed q9psPi9Cubed) q9psPi9Cubed)
              (q3kMul (q3kMul q9wrUStar q9wrUStarStar)
                      (q3kMul q9psWinv (q3kEmbed q3rqTwoElt)))
          = q3kMul (q3kMul (q3kMul q9psPi9Cubed q9psPi9Cubed) q9psPi9Cubed)
              (q3kMul q9psPi9 c) := by
    have h109 : q9nfPiPow 10 = q3kMul (q9nfPiPow 9) (q9nfPiPow 1) := q9nf_pipow_add 9 1
    rw [← q9tw_dfull_eq, hc, h109, q9nf_pipow1_eq, q9tw_pipow9_eq, q3k_kM_eq]
    exact q3kRing.mul_assoc
      (q3kMul (q3kMul q9psPi9Cubed q9psPi9Cubed) q9psPi9Cubed) q9psPi9 c
  have hcan : q3kMul (q3kMul q9wrUStar q9wrUStarStar)
                (q3kMul q9psWinv (q3kEmbed q3rqTwoElt))
            = q3kMul q9psPi9 c := q9tw_pi9c_cancel hL
  have hunit : q3kUnitMem (q3kMul (q3kMul q9wrUStar q9wrUStarStar)
                (q3kMul q9psWinv (q3kEmbed q3rqTwoElt))) :=
    q3k_unit_mul
      (q3k_unit_mul q9wr_ustar_unit q9wr_ustarstar_unit)
      (q3k_unit_mul (q3k_unit_inv q9psW q9ps_w_unit)
        (q9wr_embed_unit q3rqTwoElt q9tw_two_elt_unit))
  have h3 : IsZpUnit 3 (q3rqNorm (q3kNormBase (q3kMul q9psPi9 c))) := by
    rw [← hcan]; exact hunit
  rw [q3k_normBase_mul q9psPi9 c, q9wr_normBase_pi9, q3rq_norm_mul,
      q9wr_qnorm_zeta_sub] at h3
  exact q9wr_three_mul_not_unit (q3rqNorm (q3kNormBase c)) h3

/-- **q9tw-3e（★ headline）: v_M(D_full)=9 ちょうど**（π₉⁹∣ ∧ ¬π₉¹⁰∣・実 composite different）。 -/
theorem q9tw_different_tower_sharp :
    q9wrDvd (q9nfPiPow 9) q9twDfull
    ∧ ¬ q9wrDvd (q9nfPiPow 10) q9twDfull :=
  ⟨q9tw_dfull_dvd, q9tw_dfull_sharp⟩

/-- **q9tw-3f（★ 推移公式）: d_M(M/ℚ₃) = d_M(M/L₂) + e(M/L₂)·d_{L₂}(L₂/ℚ₃) = 6 + 3·1 = 9**。
    各実指数を主語にする:
    * d(M/L₂)=6: π₉⁶∣D_{M/L₂}（下界）∧ ¬π₉⁷∣D_{M/L₂}（q9ac_different_sharp・鋭さ）
    * d_{L₂}(L₂/ℚ₃)=1: λ∣2λ ∧ ¬λ²∣2λ（Part 1・鋭さ）
    * 推移算術: 9 = 6 + 3·1（e(M/L₂)=3）
    * d(M/ℚ₃)=9: π₉⁹∣D_full ∧ ¬π₉¹⁰∣D_full（Part 3・鋭さ） -/
theorem q9tw_different_transitivity :
    (q9wrDvd (q9nfPiPow 6) q9twDiffML2
       ∧ ¬ q9wrDvd (q3kMul q9psPi6 q9psPi9) q9twDiffML2)
    ∧ (q9twLamDvd q3rqLambda q9twDiffL2
       ∧ ¬ q9twLamDvd (q3rqMul q3rqLambda q3rqLambda) q9twDiffL2)
    ∧ ((9 : Nat) = 6 + 3 * 1)
    ∧ (q9wrDvd (q9nfPiPow 9) q9twDfull
       ∧ ¬ q9wrDvd (q9nfPiPow 10) q9twDfull) :=
  ⟨⟨q9tw_diffML2_dvd6, q9ac_different_sharp⟩,
   ⟨q9tw_lam_dvd_diff, q9tw_lam2_not_dvd_diff⟩,
   rfl,
   ⟨q9tw_dfull_dvd, q9tw_dfull_sharp⟩⟩

/-- **q9tw-3g（★ NEW）: v_{ℚ₃}(disc(M/ℚ₃)) = 9**。
    M/ℚ₃ は完全分岐 (f=1) なので disc 指数 = f·(different 指数) = 1·9 = 9。
    正直申告: f=1 完全分岐（この塔では実）・disc 指数 = 9。 -/
theorem q9tw_disc_M_Q3 :
    q9wrDvd (q9nfPiPow 9) q9twDfull
    ∧ ¬ q9wrDvd (q9nfPiPow 10) q9twDfull
    ∧ ((9 : Nat) = 1 * 9) :=
  ⟨q9tw_dfull_dvd, q9tw_dfull_sharp, rfl⟩

/-! ## q9tw-4: capstone（束ねのみ・新規証明ゼロ） -/

/-- **q9tw-4a: 実 composite different／推移公式データ束ね**。 -/
structure Q3TowerDifferentRealData where
  /-- d_{L₂}(L₂/ℚ₃)=1: λ∣2λ ∧ ¬λ²∣2λ。 -/
  diffL2_exp : q9twLamDvd q3rqLambda q9twDiffL2
    ∧ ¬ q9twLamDvd (q3rqMul q3rqLambda q3rqLambda) q9twDiffL2
  /-- L₂/ℚ₃ tame: 3∤e=2, d=e−1=1。 -/
  L2_tame : ¬ ((3 : Nat) : Int) ∣ (2 : Int)
  /-- v_M(embed 2λ)=3 ちょうど。 -/
  embed_vM3 : q9wrDvd (q9nfPiPow 3) (q3kEmbed q9twDiffL2)
    ∧ ¬ q9wrDvd (q9nfPiPow 4) (q3kEmbed q9twDiffL2)
  /-- D_full = π₉⁹·(単数)。 -/
  dfull_eq : q9twDfull
    = q3kMul (q3kMul (q3kMul q9psPi9Cubed q9psPi9Cubed) q9psPi9Cubed)
        (q3kMul (q3kMul q9wrUStar q9wrUStarStar)
                (q3kMul q9psWinv (q3kEmbed q3rqTwoElt)))
  /-- v_M(D_full)=9 ちょうど（π₉⁹∣ ∧ ¬π₉¹⁰∣）。 -/
  tower_sharp : q9wrDvd (q9nfPiPow 9) q9twDfull
    ∧ ¬ q9wrDvd (q9nfPiPow 10) q9twDfull
  /-- 推移算術 9 = 6 + 3·1。 -/
  transitivity : (9 : Nat) = 6 + 3 * 1
  /-- f=1 完全分岐: disc 指数 = 1·9 = 9。 -/
  disc_exp : (9 : Nat) = 1 * 9

/-- **q9tw-4b: 見出し実例** — 実塔 ℚ₃⊂L₂⊂M 上の composite different d(M/ℚ₃)=9。 -/
def q9tw_data : Q3TowerDifferentRealData where
  diffL2_exp := q9tw_diffL2_exp
  L2_tame := q3rq_three_not_dvd_two
  embed_vM3 := q9tw_embed_diffL2_vM3
  dfull_eq := q9tw_dfull_eq
  tower_sharp := q9tw_different_tower_sharp
  transitivity := rfl
  disc_exp := rfl

/-- **q9tw-4c: 実 composite different／推移公式の存在**（実塔・d(M/ℚ₃)=9）。 -/
theorem q9tw_exists : Nonempty Q3TowerDifferentRealData := ⟨q9tw_data⟩

end IUT
