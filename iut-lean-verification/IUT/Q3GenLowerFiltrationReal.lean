/-
  IUT/Q3GenLowerFiltrationReal.lean — 柱B・B1 一般元下付き分岐フィルトレーション
    （q9wr の π₉ 専用フィルトレーションを**任意 x∈O_M への一様可除性**へ昇格）

  ── 主要成果の分類: **[実／(a) 昇格]**——q9wr（Q3WildRamFiltrationReal）は
     下付き分岐群 G_i を一様化子 π₉ ただ一つへの作用 i_G(σ)=v(σπ₉−π₉) でのみ定義し、
     「任意 x に対する σx−x の一様可除性との同値は形式化しない」を**正直な限定 #2**
     として残していた。本モジュールはその限定を**閉じる**: O_M=O_{L₂}[Y]/(Y³−ζ₃) の
     単生成性（基底 {1,Y,Y²}）を実 Lean で使い、**すべての x∈O_M** に対し
       σx−x ∈ (π₉³)  かつ  σ²x−x ∈ (π₉³)
     を証明する（= G_2 の membership が生成元非依存＝標準定義と一致する実内容）。
     主語は実 σ・実 σ²・実 O_M・実 π₉——toy 模型（m202fVol 型・Bool 軌道・
     surrogate 群）を一切使わない。q9wr の π₉-witness（σπ₉−π₉=π₉³·u\*）を CONSUME し、
     一般元へ σ が環準同型（q3k_sigma_mul/q9nf_sigma_add）・base 固定（σ∘embed=embed）
     で伝播する事実で拡張する。

  真水（本物へ昇格した内容・新規実数学）:
   * q9gl_embedY / q9gl_embedY2 — 基底積 embed(a)·Y=(0,a,0)・embed(a)·Y²=(0,0,a) の実計算
   * q9gl_decomp — 任意 x の実基底展開 x = embed(x₀)+embed(x₁)·Y+embed(x₂)·Y²
   * q9gl_sigma_embed / q9gl_sigma2_embed — σ,σ² は base O_{L₂}=embed 像を固定（実 hom）
   * q9gl_cring_sq_diff / q9gl_sq_diff — 実 O_M 内の差の平方公式 a²−b²=(a−b)(a+b)
   * q9gl_diff_general_aux — 任意 ring-hom τ（加法・乗法・embed 固定・π₉³∣(τY−Y)）に対し
     τx−x∈(π₉³) ∀x（σ・σ² を一括に生む一般補題）
   * q9gl_sigma_diff_general（★）— ∀x, σx−x∈(π₉³)（G_2 membership・一般元・生成元非依存）
   * q9gl_sigma2_diff_general（★）— ∀x, σ²x−x∈(π₉³)（同・σ²）
   * q9gl_G2_all — 一般元 G_2=全群（σ,σ² 双方が x を (π₉³) へ持ち上げる）
   * q9gl_break_sharp / q9gl_sharp_witness — break の鋭さを一般元レベルで保持
     （x=π₉ が ¬π₉⁴∣(σx−x)＝q9wr_G3_trivial の消費・vacuous でない同じ break t=2）

  complete_pct 影響: **B1 0.60→（独立監査次第・予測 +0.03〜0.08）**。q9wr 正直限定 #2
  （π₉ 専用フィルトレーション）を本物に置換し、G_2 membership を全 x へ拡張する
  display-moving な昇格。動かす新規内容は「生成元非依存性」——q9wr は π₉ のみ、本モジュールは
  ∀x を割る。break の鋭さ（¬π₉⁴）は q9wr から CONSUME のみで再主張しない。

  正直な限定（§4 規約により消さない・弱化しない・q9wr/q9nf/q9ps/q3k 継承の上に追記のみ）:
  1. **依然として可除性形式**（付値関数 v_M は建てない）。フィルトレーション所属は
     ∃c, y=π₉ⁿ·c の可除性で与える（q9wr 正直限定 #1 継承）。
  2. **拡大 1 個（M/L₂）・下付き番号のみ**。上付き番号・Herbrand・実 Hasse–Arf・
     Artin 導手はゼロ（q9wr 正直限定 #3 継承）。
  3. **G_2 と break レベルのみを一般元へ昇格**。一般 x に対する高次 G_i（i≥3 の
     厳密可除性の上界）は π₉-witness レベルに留まる——一般元での完全な i_G 関数の値は
     v_M を要し未形式化（break の鋭さは π₉ witness で担保・membership は全 x で完全）。
  4. **3=π₉⁶·u₆・e=6・different d=6 は q9ps/q9wr 成果の消費**（本モジュールは再計算しない）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3NormFiltrationSpike

namespace IUT

/-! ## q9gl-0: base 固定（σ・σ² は embed 像＝O_{L₂} を動かさない） -/

/-- **σ は base O_{L₂}=embed 像を固定**（σ(embed n)=embed n・座標 ζ·0=0）。 -/
theorem q9gl_sigma_embed (n : q3rqCar) : q3kSigma (q3kEmbed n) = q3kEmbed n := by
  apply q3k_ext
  · rfl
  · show q3rqRing.mul q3rqZeta q3rqRing.zero = q3rqRing.zero
    exact q3rqRing.mul_zero q3rqZeta
  · show q3rqRing.mul q3rqZetaSq q3rqRing.zero = q3rqRing.zero
    exact q3rqRing.mul_zero q3rqZetaSq

/-- **σ² も base を固定**。 -/
theorem q9gl_sigma2_embed (n : q3rqCar) : q3kSigma2 (q3kEmbed n) = q3kEmbed n := by
  apply q3k_ext
  · rfl
  · show q3rqRing.mul q3rqZetaSq q3rqRing.zero = q3rqRing.zero
    exact q3rqRing.mul_zero q3rqZetaSq
  · show q3rqRing.mul q3rqZeta q3rqRing.zero = q3rqRing.zero
    exact q3rqRing.mul_zero q3rqZeta

/-! ## q9gl-1: 基底積 embed(a)·Y と embed(a)·Y² の実計算 -/

/-- **embed(a)·Y = (0,a,0)**（O_{L₂}-係数の Y 成分注入）。 -/
theorem q9gl_embedY (a : q3rqCar) :
    q3kMul (q3kEmbed a) q3kZeta9 = ((q3rqZero, a, q3rqZero) : q3kCar) := by
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul a q3rqRing.zero)
        (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero)
          (q3rqRing.mul q3rqRing.zero q3rqRing.one))) = q3rqRing.zero
    rw [q3rqRing.mul_zero a, q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.zero_mul q3rqRing.one, q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul a q3rqRing.one)
        (q3rqRing.mul q3rqRing.zero q3rqRing.zero))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqRing.zero q3rqRing.zero)) = a
    rw [q3rqRing.mul_one a, q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero a, q3rqRing.add_zero a]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul a q3rqRing.zero)
        (q3rqRing.mul q3rqRing.zero q3rqRing.one))
        (q3rqRing.mul q3rqRing.zero q3rqRing.zero) = q3rqRing.zero
    rw [q3rqRing.mul_zero a, q3rqRing.zero_mul q3rqRing.one,
        q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.add_zero q3rqRing.zero]

/-- **embed(a)·Y² = (0,0,a)**（O_{L₂}-係数の Y² 成分注入）。 -/
theorem q9gl_embedY2 (a : q3rqCar) :
    q3kMul (q3kEmbed a) (q3kMul q3kZeta9 q3kZeta9) = ((q3rqZero, q3rqZero, a) : q3kCar) := by
  rw [q3k_zeta9_sq]
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul a q3rqRing.zero)
        (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.one)
          (q3rqRing.mul q3rqRing.zero q3rqRing.zero))) = q3rqRing.zero
    rw [q3rqRing.mul_zero a, q3rqRing.zero_mul q3rqRing.one,
        q3rqRing.zero_add (q3rqRing.mul q3rqRing.zero q3rqRing.zero),
        q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul a q3rqRing.zero)
        (q3rqRing.mul q3rqRing.zero q3rqRing.zero))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqRing.zero q3rqRing.one)) = q3rqRing.zero
    rw [q3rqRing.mul_zero a, q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.add_zero q3rqRing.zero, q3rqRing.zero_mul q3rqRing.one,
        q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul a q3rqRing.one)
        (q3rqRing.mul q3rqRing.zero q3rqRing.zero))
        (q3rqRing.mul q3rqRing.zero q3rqRing.zero) = a
    rw [q3rqRing.mul_one a, q3rqRing.mul_zero q3rqRing.zero,
        q3rqRing.add_zero a, q3rqRing.add_zero a]

/-- **任意 x の実基底展開** x = embed(x₀) + embed(x₁)·Y + embed(x₂)·Y²
    （O_M=O_{L₂}[Y]/(Y³−ζ₃) の単生成性の実 Lean 形）。 -/
theorem q9gl_decomp (a0 a1 a2 : q3rqCar) :
    ((a0, a1, a2) : q3kCar)
      = q3kAdd (q3kEmbed a0) (q3kAdd (q3kMul (q3kEmbed a1) q3kZeta9)
          (q3kMul (q3kEmbed a2) (q3kMul q3kZeta9 q3kZeta9))) := by
  rw [q9gl_embedY a1, q9gl_embedY2 a2]
  apply q3k_ext
  · show a0 = q3rqRing.add a0 (q3rqRing.add q3rqRing.zero q3rqRing.zero)
    rw [q3rqRing.add_zero q3rqRing.zero, q3rqRing.add_zero a0]
  · show a1 = q3rqRing.add q3rqRing.zero (q3rqRing.add a1 q3rqRing.zero)
    rw [q3rqRing.add_zero a1, q3rqRing.zero_add a1]
  · show a2 = q3rqRing.add q3rqRing.zero (q3rqRing.add q3rqRing.zero a2)
    rw [q3rqRing.zero_add a2, q3rqRing.zero_add a2]

/-! ## q9gl-2: 差の平方公式 a²−b² = (a−b)(a+b)（実 O_M） -/

/-- **一般可換環の差の平方**: a²−b² = (a−b)(a+b)。 -/
theorem q9gl_cring_sq_diff (R : CRing) (a b : R.carrier) :
    R.add (R.mul a a) (R.neg (R.mul b b)) = R.mul (R.add a (R.neg b)) (R.add a b) := by
  rw [R.right_distrib a (R.neg b) (R.add a b),
      R.left_distrib a a b,
      R.left_distrib (R.neg b) a b,
      R.neg_mul b a, R.neg_mul b b,
      R.mul_comm b a,
      R.add_assoc (R.mul a a) (R.mul a b)
        (R.add (R.neg (R.mul a b)) (R.neg (R.mul b b))),
      ← R.add_assoc (R.mul a b) (R.neg (R.mul a b)) (R.neg (R.mul b b)),
      R.add_neg (R.mul a b), R.zero_add (R.neg (R.mul b b))]

/-- 実 O_M への差の平方（q3kRing 特殊化）。 -/
theorem q9gl_sq_diff (a b : q3kCar) :
    q3kAdd (q3kMul a a) (q3kNeg (q3kMul b b))
      = q3kMul (q3kAdd a (q3kNeg b)) (q3kAdd a b) :=
  q9gl_cring_sq_diff q3kRing a b

/-! ## q9gl-3: π₉³ ∣ (σᵏY−Y)（q9wr の π₉-witness の Y=1+π₉ への移送） -/

/-- π₉³ ∣ (σπ₉−π₉)（q9wr_G2_mem を q9nfPiPow 3 形へブリッジ・CONSUME）。 -/
theorem q9gl_sigma_pi_dvd :
    q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)) := by
  rw [q9nf_pipow3_eq]
  exact q9wr_G2_mem.1

/-- π₉³ ∣ (σ²π₉−π₉)。 -/
theorem q9gl_sigma2_pi_dvd :
    q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)) := by
  rw [q9nf_pipow3_eq]
  exact q9wr_G2_mem.2

/-- **σY−Y = σπ₉−π₉**（Y=1+π₉・σ(1)=1 で 1 が相殺）。 -/
theorem q9gl_sigma_zeta9_diff :
    q3kAdd (q3kSigma q3kZeta9) (q3kNeg q3kZeta9)
      = q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9) := by
  rw [q9nf_zeta9_eq_one_add_pi9, q9nf_sigma_add q3kOne q9psPi9, q3k_sigma_one,
      q9nf_kA_eq, q9ps_kN_eq, q9ps_kO_eq,
      q3kRing.neg_add_dist q3kRing.one q9psPi9,
      q3kRing.add_comm q3kRing.one (q3kSigma q9psPi9),
      q3kRing.add_assoc (q3kSigma q9psPi9) q3kRing.one
        (q3kRing.add (q3kRing.neg q3kRing.one) (q3kRing.neg q9psPi9)),
      ← q3kRing.add_assoc q3kRing.one (q3kRing.neg q3kRing.one) (q3kRing.neg q9psPi9),
      q3kRing.add_neg q3kRing.one, q3kRing.zero_add (q3kRing.neg q9psPi9)]

/-- **σ²Y−Y = σ²π₉−π₉**。 -/
theorem q9gl_sigma2_zeta9_diff :
    q3kAdd (q3kSigma2 q3kZeta9) (q3kNeg q3kZeta9)
      = q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9) := by
  rw [q9nf_zeta9_eq_one_add_pi9, q9nf_sigma2_add q3kOne q9psPi9, q3k_sigma2_one,
      q9nf_kA_eq, q9ps_kN_eq, q9ps_kO_eq,
      q3kRing.neg_add_dist q3kRing.one q9psPi9,
      q3kRing.add_comm q3kRing.one (q3kSigma2 q9psPi9),
      q3kRing.add_assoc (q3kSigma2 q9psPi9) q3kRing.one
        (q3kRing.add (q3kRing.neg q3kRing.one) (q3kRing.neg q9psPi9)),
      ← q3kRing.add_assoc q3kRing.one (q3kRing.neg q3kRing.one) (q3kRing.neg q9psPi9),
      q3kRing.add_neg q3kRing.one, q3kRing.zero_add (q3kRing.neg q9psPi9)]

/-- π₉³ ∣ (σY−Y)。 -/
theorem q9gl_sigma_zeta9_dvd :
    q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma q3kZeta9) (q3kNeg q3kZeta9)) := by
  rw [q9gl_sigma_zeta9_diff]
  exact q9gl_sigma_pi_dvd

/-- π₉³ ∣ (σ²Y−Y)。 -/
theorem q9gl_sigma2_zeta9_dvd :
    q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma2 q3kZeta9) (q3kNeg q3kZeta9)) := by
  rw [q9gl_sigma2_zeta9_diff]
  exact q9gl_sigma2_pi_dvd

/-! ## q9gl-4: 一般補題——ring-hom τ に対し τx−x∈(π₉³) ∀x -/

/-- **一般元 G_2 補題**: τ が加法的・乗法的・base 固定で π₉³∣(τY−Y) なら
    **∀x, π₉³ ∣ (τx−x)**。σ・σ² を一括に生む本体。
    証明: x=embed(x₀)+embed(x₁)·Y+embed(x₂)·Y²（q9gl_decomp）に τ を通し、base が
    消えて τx−x = embed(x₁)·(τY−Y) + embed(x₂)·(τY²−Y²)。τY²−Y²=(τY−Y)(τY+Y)
    （差の平方・τ 乗法性）ゆえ両項とも (π₉³) の倍元。 -/
theorem q9gl_diff_general_aux
    (τ : q3kCar → q3kCar)
    (hadd : ∀ a b : q3kCar, τ (q3kAdd a b) = q3kAdd (τ a) (τ b))
    (hmul : ∀ a b : q3kCar, τ (q3kMul a b) = q3kMul (τ a) (τ b))
    (hembed : ∀ n : q3rqCar, τ (q3kEmbed n) = q3kEmbed n)
    (hDY : q9wrDvd (q9nfPiPow 3) (q3kAdd (τ q3kZeta9) (q3kNeg q3kZeta9)))
    (x : q3kCar) :
    q9wrDvd (q9nfPiPow 3) (q3kAdd (τ x) (q3kNeg x)) := by
  obtain ⟨a0, a1, a2⟩ := x
  have hx : ((a0, a1, a2) : q3kCar)
      = q3kAdd (q3kEmbed a0) (q3kAdd (q3kMul (q3kEmbed a1) q3kZeta9)
          (q3kMul (q3kEmbed a2) (q3kMul q3kZeta9 q3kZeta9))) := q9gl_decomp a0 a1 a2
  -- 一般 Y² の π₉³ 可除性（差の平方）
  have hDY2 : q9wrDvd (q9nfPiPow 3)
      (q3kAdd (τ (q3kMul q3kZeta9 q3kZeta9)) (q3kNeg (q3kMul q3kZeta9 q3kZeta9))) := by
    rw [hmul q3kZeta9 q3kZeta9, q9gl_sq_diff (τ q3kZeta9) q3kZeta9]
    exact q9nf_dvd_mul_right hDY (q3kAdd (τ q3kZeta9) q3kZeta9)
  -- 核心恒等式: τx−x = embed(x₁)·(τY−Y) + embed(x₂)·(τY²−Y²)
  have hkey : q3kAdd (τ ((a0, a1, a2) : q3kCar)) (q3kNeg ((a0, a1, a2) : q3kCar))
      = q3kAdd (q3kMul (q3kEmbed a1) (q3kAdd (τ q3kZeta9) (q3kNeg q3kZeta9)))
          (q3kMul (q3kEmbed a2)
            (q3kAdd (τ (q3kMul q3kZeta9 q3kZeta9)) (q3kNeg (q3kMul q3kZeta9 q3kZeta9)))) := by
    rw [hx,
        hadd (q3kEmbed a0)
          (q3kAdd (q3kMul (q3kEmbed a1) q3kZeta9)
            (q3kMul (q3kEmbed a2) (q3kMul q3kZeta9 q3kZeta9))),
        hadd (q3kMul (q3kEmbed a1) q3kZeta9)
          (q3kMul (q3kEmbed a2) (q3kMul q3kZeta9 q3kZeta9)),
        hmul (q3kEmbed a1) q3kZeta9,
        hmul (q3kEmbed a2) (q3kMul q3kZeta9 q3kZeta9),
        hembed a0, hembed a1, hembed a2,
        q3k_kM_eq, q9nf_kA_eq, q9ps_kN_eq]
    -- RHS の分配
    rw [q3kRing.left_distrib (q3kEmbed a1) (τ q3kZeta9) (q3kRing.neg q3kZeta9),
        q3kRing.mul_neg (q3kEmbed a1) q3kZeta9,
        q3kRing.left_distrib (q3kEmbed a2) (τ (q3kRing.mul q3kZeta9 q3kZeta9))
          (q3kRing.neg (q3kRing.mul q3kZeta9 q3kZeta9)),
        q3kRing.mul_neg (q3kEmbed a2) (q3kRing.mul q3kZeta9 q3kZeta9)]
    -- LHS の neg 分配と再配置
    rw [q3kRing.neg_add_dist (q3kEmbed a0)
          (q3kRing.add (q3kRing.mul (q3kEmbed a1) q3kZeta9)
            (q3kRing.mul (q3kEmbed a2) (q3kRing.mul q3kZeta9 q3kZeta9))),
        q3kRing.neg_add_dist (q3kRing.mul (q3kEmbed a1) q3kZeta9)
          (q3kRing.mul (q3kEmbed a2) (q3kRing.mul q3kZeta9 q3kZeta9)),
        q3kRing.add_add_add_comm (q3kEmbed a0)
          (q3kRing.add (q3kRing.mul (q3kEmbed a1) (τ q3kZeta9))
            (q3kRing.mul (q3kEmbed a2) (τ (q3kRing.mul q3kZeta9 q3kZeta9))))
          (q3kRing.neg (q3kEmbed a0))
          (q3kRing.add (q3kRing.neg (q3kRing.mul (q3kEmbed a1) q3kZeta9))
            (q3kRing.neg (q3kRing.mul (q3kEmbed a2) (q3kRing.mul q3kZeta9 q3kZeta9)))),
        q3kRing.add_neg (q3kEmbed a0),
        q3kRing.zero_add
          (q3kRing.add
            (q3kRing.add (q3kRing.mul (q3kEmbed a1) (τ q3kZeta9))
              (q3kRing.mul (q3kEmbed a2) (τ (q3kRing.mul q3kZeta9 q3kZeta9))))
            (q3kRing.add (q3kRing.neg (q3kRing.mul (q3kEmbed a1) q3kZeta9))
              (q3kRing.neg (q3kRing.mul (q3kEmbed a2) (q3kRing.mul q3kZeta9 q3kZeta9))))),
        q3kRing.add_add_add_comm
          (q3kRing.mul (q3kEmbed a1) (τ q3kZeta9))
          (q3kRing.mul (q3kEmbed a2) (τ (q3kRing.mul q3kZeta9 q3kZeta9)))
          (q3kRing.neg (q3kRing.mul (q3kEmbed a1) q3kZeta9))
          (q3kRing.neg (q3kRing.mul (q3kEmbed a2) (q3kRing.mul q3kZeta9 q3kZeta9)))]
  rw [hkey]
  refine q9nf_dvd_add ?_ ?_
  · rw [q3k_mul_comm (q3kEmbed a1) (q3kAdd (τ q3kZeta9) (q3kNeg q3kZeta9))]
    exact q9nf_dvd_mul_right hDY (q3kEmbed a1)
  · rw [q3k_mul_comm (q3kEmbed a2)
        (q3kAdd (τ (q3kMul q3kZeta9 q3kZeta9)) (q3kNeg (q3kMul q3kZeta9 q3kZeta9)))]
    exact q9nf_dvd_mul_right hDY2 (q3kEmbed a2)

/-! ## q9gl-5: ★ 一般元 G_2 membership（σ・σ²） -/

/-- **★ 一般元 σ の G_2 membership**: ∀x, σx−x ∈ (π₉³)。
    q9wr 正直限定 #2（π₉ 専用フィルトレーション）を閉じる本物の昇格——
    G_2 membership が生成元非依存＝標準定義と一致することの実証。 -/
theorem q9gl_sigma_diff_general (x : q3kCar) :
    q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma x) (q3kNeg x)) :=
  q9gl_diff_general_aux q3kSigma q9nf_sigma_add q3k_sigma_mul
    q9gl_sigma_embed q9gl_sigma_zeta9_dvd x

/-- **★ 一般元 σ² の G_2 membership**: ∀x, σ²x−x ∈ (π₉³)。 -/
theorem q9gl_sigma2_diff_general (x : q3kCar) :
    q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma2 x) (q3kNeg x)) :=
  q9gl_diff_general_aux q3kSigma2 q9nf_sigma2_add q3k_sigma2_mul
    q9gl_sigma2_embed q9gl_sigma2_zeta9_dvd x

/-- **一般元 G_2 = 全群**: ∀x, σ,σ² が双方 x を (π₉³) へ持ち上げる
    （実 Gal(M/L₂)=⟨σ⟩ 全体が一般元レベルで G_2 に属する）。 -/
theorem q9gl_G2_all (x : q3kCar) :
    q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma x) (q3kNeg x))
    ∧ q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma2 x) (q3kNeg x)) :=
  ⟨q9gl_sigma_diff_general x, q9gl_sigma2_diff_general x⟩

/-! ## q9gl-6: break の鋭さ（一般元レベルでも同じ break t=2） -/

/-- **★ break の鋭さ（一般元レベル保持）**: ¬π₉⁴ ∣ (σπ₉−π₉)。q9wr_G3_trivial を
    q9nfPiPow 4 形へブリッジ・CONSUME——一般化された G_2 は vacuous でなく、
    同じ break t=2（G_2≠0・G_3=0）で真にジャンプする。 -/
theorem q9gl_break_sharp :
    ¬ q9wrDvd (q9nfPiPow 4) (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)) := by
  intro h
  apply q9wr_G3_trivial
  have h4 : q9nfPiPow 4
      = q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psPi9 := by
    rw [q9nf_pipow_add 3 1, q9nf_pipow1_eq, q9nf_pipow3_eq]
    rfl
  rw [h4] at h
  exact h

/-- **一般元 witness の鋭さ**: x=π₉ が σx−x∈(π₉³) かつ ¬(σx−x∈(π₉⁴))
    ——一般 membership 定理（q9gl_sigma_diff_general）を具体元で実行し、break が
    非退化に t=2 で立つことを実証（vacuous ⊆ でない）。 -/
theorem q9gl_sharp_witness :
    ∃ x : q3kCar,
      q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma x) (q3kNeg x))
      ∧ ¬ q9wrDvd (q9nfPiPow 4) (q3kAdd (q3kSigma x) (q3kNeg x)) :=
  ⟨q9psPi9, q9gl_sigma_diff_general q9psPi9, q9gl_break_sharp⟩

/-! ## q9gl-7: capstone -/

/-- **一般元下付き分岐フィルトレーションデータ**——∀x での σ・σ² の G_2 membership
    （生成元非依存）と break の鋭さ（一般元レベル保持）を束ねる。 -/
structure Q3GenLowerFiltrationRealData where
  /-- ∀x, σx−x ∈ (π₉³)（一般元 G_2・生成元非依存）。 -/
  sigma_gen : ∀ x : q3kCar,
    q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma x) (q3kNeg x))
  /-- ∀x, σ²x−x ∈ (π₉³)。 -/
  sigma2_gen : ∀ x : q3kCar,
    q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kSigma2 x) (q3kNeg x))
  /-- break の鋭さ: ¬π₉⁴ ∣ (σπ₉−π₉)（同じ break t=2）。 -/
  break_sharp :
    ¬ q9wrDvd (q9nfPiPow 4) (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))

/-- **見出し実例** — 一般元下付き分岐フィルトレーション（∀x で G_2・break t=2）。 -/
def q9gl_data : Q3GenLowerFiltrationRealData where
  sigma_gen := q9gl_sigma_diff_general
  sigma2_gen := q9gl_sigma2_diff_general
  break_sharp := q9gl_break_sharp

/-- **一般元下付き分岐フィルトレーションの存在**（π₉ 専用限定の昇格・∀x G_2・break t=2）。 -/
theorem q9gl_exists : Nonempty Q3GenLowerFiltrationRealData := ⟨q9gl_data⟩

end IUT

