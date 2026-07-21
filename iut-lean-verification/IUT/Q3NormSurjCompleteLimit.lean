/-
  IUT/Q3NormSurjCompleteLimit.lean — 柱B・B2 T3-M3: **完備性の残り全段（M3a-2/3・M3b・M3c）＝
    T3-core 厳密等式 N(x) = u の確立**
    （逐次近似塔 q9ncSeq の極限 q9clLim を z3cLim の 6 座標適用で choice-free に構成し、
     N の連続性（望遠鏡恒等式）と O_M 分離性で近似を厳密等式に昇格する。）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（T3-core の厳密等式を実 O_M/O_{L₂} 上で
     閉じる・toy 主語なし）。主語は実 O_M = q3kRing（実 ℤ₃ の 6 座標整合族）・実 3 次ノルム
     q3kNormBase・実 π₉ フィルトレーション・M27 完備性 z3cLim。

  complete_pct 影響: **B2 T3-M3 完了 = T3-core 確立**（監査次第・設計予測 s_B2 0.44→0.48–0.52）。
    本ラウンドで閉じるのは M3 梯子（audit/pillar-B2-T3-M2-M3-completeness-detail-2026-07-11.md §4）
    の残り全段:
    (i) **M3a-2（O_M 6 座標ブリッジ）** `q9cl_dvd_three_iff`:
        (∃e, z = 3^k·e in O_M) ⟺ 6 個の z3 座標すべてが z3vGe 3 · k（q9cm_dvd_pow_iff の 6 重化。
        スカラー 3 の乗法は座標ごと zpMul 3 q9cmThreeZ——`q9cl_three_rq`/`q9cl_three_k`）。
    (ii) **M3a-3（π₉ ⇔ 3 変換）** `q9cl_pi6_iff_three`: π₉^{6k}∣z ⟺ 3^k∣z（k 帰納・
        3 = π₉⁶·u₆［q9ps_three_split］・u₆ 単数消去・全部品実在）。
    (iii) **M2d'（塔 coherence・witness 陽・無条件）** `q9cl_step_dvd`/`q9cl_tower_dvd`:
        π₉^{3n+5}∣(x_{m}−x_{n})（n ≤ m・望遠鏡・witness = x_n·a_n が式そのもの）。
    (iv) **M3b（極限構成）** `q9clLim` = z3cLim の 6 座標適用（modulus M(t)=2t の閉じた式・
        choice ゼロ）+ 収束 `q9cl_lim_conv`: ∀t ∀i≥2t, π₉^{6t}∣(x_i − q9clLim u)。
    (v) **M3c-1（N の連続性）** `q9cl_norm_cont`: π₉^m∣(x−y) ⟹ π₉^m∣(embed(Nx)−embed(Ny))
        （純環望遠鏡恒等式 `q9cl_tele_ring` + q9nf_dvd_sigma/sigma2）。
    (vi) **M3c-2（O_M 分離性）** `q9cl_sep`: (∀k, π₉^{6k}∣z) ⟹ z = 0（M3a-3 → M3a-2 →
        zp 分離 q9cm_sep × 6）。
    (vii) ★★★ **M3c-3（T3-core）** `q9cl_norm_exact`: u ∈ U^{(9)} ⟹ N(q9clLim u) = u
        **厳密等式**、および `q9cl_norm_surj`: u ∈ U^{(9)} 単数 ⟹ ∃x 単数, N(x) = u。
        主単数レベルの実ノルム全射性（T3-core）。

  ── **正直な限定（§4 規約により消さない・弱めない）:**
  0. **本ファイルの成果は U^{(9)}（主単数・λ-レベル 3 深度）⊆ N(M^×) の主単数レベル**である。
     - **U^{(3)}⊆N の全体・index(U_{L₂}:N(U_M)) ≤ 3（M4）は別段**であり本ファイルでは主張しない。
     - **cap(b)（分数元込み L₂^×/N(M^×) 全体）・Artin 正規化・一般局所体は未達**（T3 スコープ外）。
  1. 完備性は **modulus 形のみ**（z3c の正直限定を継承）。本塔は構成により modulus M(t)=2t が
     閉じた式で読めるため choice-free に閉じる（∃ 形 Cauchy の可算選択は不要かつ不使用）。
  2. q9cm/q9nc/q9na/q9npg/q9ns/q9nf/q9gn/q9ps/q9rf/q9wr/q3k/q3rq/z3c の正直限定を全継承
     （可除性・付値関係形式のみ・total v_M 不使用・O_M と M^× のみ・体化なし・
      σ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体・
      拡大 1 個 M/L₂/ℚ₃・p = 3 固定）。
  3. 塔 coherence（M2d'）と極限 q9clLim は u の仮定なしに定義されるが、**N(q9clLim u) = u は
     u ∈ U^{(9)}（q9nfUfilt 9 (q3kEmbed u)）の下でのみ**成立を主張する。

  全て選択公理不使用（新規 Classical.choice なし・sorry 皆無・極限は z3cLim の閉じた式・
  omega は Int/Nat atom のみ）。#print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3NormSurjComplete

namespace IUT

/-! ## q9cl-0: スカラー 3 の座標展開（M3a-2 の部品） -/

/-- **q9cl-0a: q9cmThreeZ = q3rqThree**（実 ℤ₃ の 3・q9rf_zvp_eq_three の別名）。 -/
theorem q9cl_threeZ_eq : q9cmThreeZ = q3rqThree := q9rf_zvp_eq_three

/-- **q9cl-0b: O_{L₂} のスカラー 3 は座標ごと 3 倍** — 3_{L₂}·m = (3·m₁, 3·m₂)。 -/
theorem q9cl_three_rq (m : q3rqCar) :
    q3rqMul q3rqThreeElt m
      = ((zpMul 3 q9cmThreeZ m.1, zpMul 3 q9cmThreeZ m.2) : q3rqCar) := by
  apply q3rq_ext
  · show z3.add (z3.mul q3rqThree m.1) (z3.mul q3rqD (z3.mul z3.zero m.2))
      = z3.mul q9cmThreeZ m.1
    rw [q9cl_threeZ_eq, z3.zero_mul m.2, z3.mul_zero q3rqD,
        z3.add_zero (z3.mul q3rqThree m.1)]
  · show z3.add (z3.mul q3rqThree m.2) (z3.mul z3.zero m.1)
      = z3.mul q9cmThreeZ m.2
    rw [q9cl_threeZ_eq, z3.zero_mul m.1, z3.add_zero (z3.mul q3rqThree m.2)]

/-- **q9cl-0c: O_M のスカラー 3 は座標ごと 3_{L₂} 倍** — 3_M·z = (3·z₀, 3·z₁, 3·z₂)。 -/
theorem q9cl_three_k (z : q3kCar) :
    q3kMul (q3kEmbed q3rqThreeElt) z
      = ((q3rqMul q3rqThreeElt z.1, q3rqMul q3rqThreeElt z.2.1,
          q3rqMul q3rqThreeElt z.2.2) : q3kCar) := by
  apply q3k_ext
  · show q3rqAdd (q3rqMul q3rqThreeElt z.1)
        (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero z.2.2) (q3rqMul q3rqZero z.2.1)))
      = q3rqMul q3rqThreeElt z.1
    rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul z.2.2, q3rqRing.zero_mul z.2.1,
        q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero (q3rqRing.mul q3rqThreeElt z.1)]
  · show q3rqAdd (q3rqAdd (q3rqMul q3rqThreeElt z.2.1) (q3rqMul q3rqZero z.1))
        (q3rqMul q3rqZeta (q3rqMul q3rqZero z.2.2))
      = q3rqMul q3rqThreeElt z.2.1
    rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul z.1,
        q3rqRing.add_zero (q3rqRing.mul q3rqThreeElt z.2.1), q3rqRing.zero_mul z.2.2,
        q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero (q3rqRing.mul q3rqThreeElt z.2.1)]
  · show q3rqAdd (q3rqAdd (q3rqMul q3rqThreeElt z.2.2) (q3rqMul q3rqZero z.2.1))
        (q3rqMul q3rqZero z.1)
      = q3rqMul q3rqThreeElt z.2.2
    rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul z.2.1,
        q3rqRing.add_zero (q3rqRing.mul q3rqThreeElt z.2.2), q3rqRing.zero_mul z.1,
        q3rqRing.add_zero (q3rqRing.mul q3rqThreeElt z.2.2)]

/-! ## q9cl-1: M3a-2 — O_M の 3^k 乗と 6 座標ブリッジ -/

/-- **q9cl-1a: O_M の 3^k 乗**（3_M 倍の k 回反復・data 関数）。 -/
def q9clMul3Pow : Nat → q3kCar → q3kCar
  | 0, z => z
  | (k + 1), z => q3kMul (q3kEmbed q3rqThreeElt) (q9clMul3Pow k z)

/-- **q9cl-1b: 1 段展開**（rfl）。 -/
theorem q9cl_mul3pow_succ (k : Nat) (z : q3kCar) :
    q9clMul3Pow (k + 1) z = q3kMul (q3kEmbed q3rqThreeElt) (q9clMul3Pow k z) := rfl

/-- **q9cl-1c: O_M の 3^k 乗は 6 座標の z3 3^k 乗**（k 帰納・座標閉形式）。 -/
theorem q9cl_mul3pow_coord (k : Nat) (z : q3kCar) :
    q9clMul3Pow k z
      = ((((q9cmMul3Pow k z.1.1, q9cmMul3Pow k z.1.2) : q3rqCar),
          ((q9cmMul3Pow k z.2.1.1, q9cmMul3Pow k z.2.1.2) : q3rqCar),
          ((q9cmMul3Pow k z.2.2.1, q9cmMul3Pow k z.2.2.2) : q3rqCar)) : q3kCar) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [q9cl_mul3pow_succ k z, ih, q9cl_three_k, q9cl_three_rq, q9cl_three_rq,
        q9cl_three_rq]
    rfl

/-- **q9cl-1d（★ M3a-2）: O_M の 3^k 可除性 ⟺ 6 座標の level-k 消滅**
    （q9cm_dvd_pow_iff の 6 重化・witness は zpDivP 反復がデータ供給）。 -/
theorem q9cl_dvd_three_iff (k : Nat) (z : q3kCar) :
    (∃ e, z = q9clMul3Pow k e) ↔
      (z3vGe 3 z.1.1 k ∧ z3vGe 3 z.1.2 k ∧ z3vGe 3 z.2.1.1 k ∧
       z3vGe 3 z.2.1.2 k ∧ z3vGe 3 z.2.2.1 k ∧ z3vGe 3 z.2.2.2 k) := by
  constructor
  · intro ⟨e, he⟩
    rw [he, q9cl_mul3pow_coord k e]
    exact ⟨(q9cm_dvd_pow_iff k (q9cmMul3Pow k e.1.1)).mp ⟨e.1.1, rfl⟩,
      (q9cm_dvd_pow_iff k (q9cmMul3Pow k e.1.2)).mp ⟨e.1.2, rfl⟩,
      (q9cm_dvd_pow_iff k (q9cmMul3Pow k e.2.1.1)).mp ⟨e.2.1.1, rfl⟩,
      (q9cm_dvd_pow_iff k (q9cmMul3Pow k e.2.1.2)).mp ⟨e.2.1.2, rfl⟩,
      (q9cm_dvd_pow_iff k (q9cmMul3Pow k e.2.2.1)).mp ⟨e.2.2.1, rfl⟩,
      (q9cm_dvd_pow_iff k (q9cmMul3Pow k e.2.2.2)).mp ⟨e.2.2.2, rfl⟩⟩
  · intro ⟨h1, h2, h3, h4, h5, h6⟩
    obtain ⟨e1, he1⟩ := (q9cm_dvd_pow_iff k z.1.1).mpr h1
    obtain ⟨e2, he2⟩ := (q9cm_dvd_pow_iff k z.1.2).mpr h2
    obtain ⟨e3, he3⟩ := (q9cm_dvd_pow_iff k z.2.1.1).mpr h3
    obtain ⟨e4, he4⟩ := (q9cm_dvd_pow_iff k z.2.1.2).mpr h4
    obtain ⟨e5, he5⟩ := (q9cm_dvd_pow_iff k z.2.2.1).mpr h5
    obtain ⟨e6, he6⟩ := (q9cm_dvd_pow_iff k z.2.2.2).mpr h6
    refine ⟨((((e1, e2) : q3rqCar), ((e3, e4) : q3rqCar), ((e5, e6) : q3rqCar)) : q3kCar), ?_⟩
    rw [q9cl_mul3pow_coord]
    exact q3k_ext (q3rq_ext he1 he2) (q3rq_ext he3 he4) (q3rq_ext he5 he6)

/-! ## q9cl-2: M3a-3 — π₉^{6k} ⟺ 3^k 変換（3 = π₉⁶·u₆ 経由） -/

/-- **q9cl-2a: u₆⁻¹**（閉形式単数逆元・choice-free）。 -/
def q9clU6Inv : q3kCar := q3kInv q9psU6 q9ps_u6_unit

/-- **q9cl-2b: u₆·u₆⁻¹ = 1**。 -/
theorem q9cl_u6_mul_inv : q3kRing.mul q9psU6 q9clU6Inv = q3kRing.one :=
  q3k_inv_mul q9psU6 q9ps_u6_unit

/-- **q9cl-2c（★ M3a-3）: π₉^{6k} ∣ z ⟺ 3^k ∣ z**（k 帰納・3 = π₉⁶·u₆・u₆ 単数消去）。 -/
theorem q9cl_pi6_iff_three (k : Nat) (z : q3kCar) :
    q9wrDvd (q9nfPiPow (6 * k)) z ↔ (∃ e, z = q9clMul3Pow k e) := by
  induction k generalizing z with
  | zero =>
    constructor
    · intro _
      exact ⟨z, rfl⟩
    · intro _
      exact ⟨z, (q3k_one_mul z).symm⟩
  | succ k ih =>
    have h6 : 6 * (k + 1) = 6 * k + 6 := by omega
    constructor
    · intro ⟨c, hc⟩
      have hc' : z = q3kMul (q3kEmbed q3rqThreeElt)
          (q3kMul q9clU6Inv (q3kMul (q9nfPiPow (6 * k)) c)) := by
        rw [hc, h6, q9nf_pipow_add (6 * k) 6, ← q9ps_three_split, ← q9nf_pipow6_eq,
            q3k_kM_eq,
            q3kRing.mul_assoc (q9nfPiPow 6) q9psU6
              (q3kRing.mul q9clU6Inv (q3kRing.mul (q9nfPiPow (6 * k)) c)),
            ← q3kRing.mul_assoc q9psU6 q9clU6Inv (q3kRing.mul (q9nfPiPow (6 * k)) c),
            q9cl_u6_mul_inv,
            q3kRing.one_mul (q3kRing.mul (q9nfPiPow (6 * k)) c),
            q3kRing.mul_comm (q9nfPiPow (6 * k)) (q9nfPiPow 6),
            q3kRing.mul_assoc (q9nfPiPow 6) (q9nfPiPow (6 * k)) c]
      have hy : q9wrDvd (q9nfPiPow (6 * k))
          (q3kMul q9clU6Inv (q3kMul (q9nfPiPow (6 * k)) c)) :=
        ⟨q3kMul q9clU6Inv c, by
          rw [q3k_kM_eq]
          exact CRing.mul_left_comm q3kRing q9clU6Inv (q9nfPiPow (6 * k)) c⟩
      obtain ⟨e, he⟩ := (ih (q3kMul q9clU6Inv (q3kMul (q9nfPiPow (6 * k)) c))).mp hy
      refine ⟨e, ?_⟩
      rw [q9cl_mul3pow_succ k e, ← he]
      exact hc'
    · intro ⟨e, he⟩
      obtain ⟨c, hcc⟩ := (ih (q9clMul3Pow k e)).mpr ⟨e, rfl⟩
      refine ⟨q3kMul q9psU6 c, ?_⟩
      rw [he, q9cl_mul3pow_succ k e, hcc, ← q9ps_three_split, h6,
          q9nf_pipow_add (6 * k) 6, ← q9nf_pipow6_eq, q3k_kM_eq,
          q3kRing.mul_mul_mul_comm (q9nfPiPow 6) q9psU6 (q9nfPiPow (6 * k)) c,
          q3kRing.mul_comm (q9nfPiPow 6) (q9nfPiPow (6 * k))]

/-- **q9cl-2d: π₉^{6k} 可除 ⟹ 6 座標 level-k 消滅**（M3a-3 → M3a-2 合成・正方向）。 -/
theorem q9cl_dvd6_coords (k : Nat) {z : q3kCar}
    (h : q9wrDvd (q9nfPiPow (6 * k)) z) :
    z3vGe 3 z.1.1 k ∧ z3vGe 3 z.1.2 k ∧ z3vGe 3 z.2.1.1 k ∧
    z3vGe 3 z.2.1.2 k ∧ z3vGe 3 z.2.2.1 k ∧ z3vGe 3 z.2.2.2 k :=
  (q9cl_dvd_three_iff k z).mp ((q9cl_pi6_iff_three k z).mp h)

/-- **q9cl-2e: 6 座標 level-k 消滅 ⟹ π₉^{6k} 可除**（逆方向・witness 再組立て）。 -/
theorem q9cl_coords_dvd6 (k : Nat) {z : q3kCar}
    (h : z3vGe 3 z.1.1 k ∧ z3vGe 3 z.1.2 k ∧ z3vGe 3 z.2.1.1 k ∧
         z3vGe 3 z.2.1.2 k ∧ z3vGe 3 z.2.2.1 k ∧ z3vGe 3 z.2.2.2 k) :
    q9wrDvd (q9nfPiPow (6 * k)) z :=
  (q9cl_pi6_iff_three k z).mpr ((q9cl_dvd_three_iff k z).mpr h)

/-! ## q9cl-3: M3c-2 — O_M の分離性（Hausdorff 条件） -/

/-- **q9cl-3a（★ M3c-2）: O_M 分離性** — (∀k, π₉^{6k}∣z) ⟹ z = 0
    （6 座標へ落として zp 分離 q9cm_sep）。 -/
theorem q9cl_sep (z : q3kCar) (h : ∀ k, q9wrDvd (q9nfPiPow (6 * k)) z) :
    z = q3kZero := by
  have h11 : z.1.1 = z3.zero := q9cm_sep z.1.1 (fun k => (q9cl_dvd6_coords k (h k)).1)
  have h12 : z.1.2 = z3.zero := q9cm_sep z.1.2 (fun k => (q9cl_dvd6_coords k (h k)).2.1)
  have h21 : z.2.1.1 = z3.zero := q9cm_sep z.2.1.1 (fun k => (q9cl_dvd6_coords k (h k)).2.2.1)
  have h22 : z.2.1.2 = z3.zero := q9cm_sep z.2.1.2 (fun k => (q9cl_dvd6_coords k (h k)).2.2.2.1)
  have h31 : z.2.2.1 = z3.zero := q9cm_sep z.2.2.1 (fun k => (q9cl_dvd6_coords k (h k)).2.2.2.2.1)
  have h32 : z.2.2.2 = z3.zero := q9cm_sep z.2.2.2 (fun k => (q9cl_dvd6_coords k (h k)).2.2.2.2.2)
  exact q3k_ext (q3rq_ext h11 h12) (q3rq_ext h21 h22) (q3rq_ext h31 h32)

/-! ## q9cl-4: M2d' — 塔 coherence（witness 陽・無条件） -/

/-- 差の合流 (a−c) + (c−b) = a−b（純環簿記）。 -/
theorem q9cl_sub_merge (R : CRing) (a c b : R.carrier) :
    R.add (R.add a (R.neg c)) (R.add c (R.neg b)) = R.add a (R.neg b) := by
  rw [R.add_assoc a (R.neg c) (R.add c (R.neg b)),
      ← R.add_assoc (R.neg c) c (R.neg b),
      R.neg_add c, R.zero_add (R.neg b)]

/-- 塔 1 段の純環恒等式 x·(1+P·a) − x = P·(a·x)。 -/
theorem q9cl_step_ring (R : CRing) (x P a : R.carrier) :
    R.add (R.mul x (R.add R.one (R.mul P a))) (R.neg x) = R.mul P (R.mul a x) := by
  rw [R.left_distrib x R.one (R.mul P a), R.mul_one x,
      R.add_comm x (R.mul x (R.mul P a)),
      R.add_assoc (R.mul x (R.mul P a)) x (R.neg x),
      R.add_neg x, R.add_zero (R.mul x (R.mul P a)),
      R.mul_left_comm x P a, R.mul_comm x a]

/-- 塔の 1 段展開（rfl）。 -/
theorem q9cl_seq_succ (u : q3rqCar) (n : Nat) :
    q9ncSeq u (n + 1) = q3kMul (q9ncSeq u n) (q9ncV u (q9ncSeq u n) n) := rfl

/-- peel 因子の展開（rfl）。 -/
theorem q9cl_V_eq (u : q3rqCar) (x : q3kCar) (n : Nat) :
    q9ncV u x n = q3kAdd q3kOne (q3kMul (q9nfPiPow (3 * n + 5)) (q9ncCorr u x n)) := rfl

/-- **q9cl-4a: 塔 1 段の可除性**（witness = a_n·x_n が式そのもの・u の仮定不要）:
    π₉^{3n+5} ∣ (x_{n+1} − x_n)。 -/
theorem q9cl_step_dvd (u : q3rqCar) (n : Nat) :
    q9wrDvd (q9nfPiPow (3 * n + 5))
      (q3kAdd (q9ncSeq u (n + 1)) (q3kNeg (q9ncSeq u n))) := by
  refine ⟨q3kMul (q9ncCorr u (q9ncSeq u n) n) (q9ncSeq u n), ?_⟩
  rw [q9cl_seq_succ u n, q9cl_V_eq u (q9ncSeq u n) n,
      q3k_kM_eq, q9nf_kA_eq, q9ps_kN_eq, q9ps_kO_eq]
  exact q9cl_step_ring q3kRing (q9ncSeq u n) (q9nfPiPow (3 * n + 5))
    (q9ncCorr u (q9ncSeq u n) n)

/-- **q9cl-4b（★ M2d'）: 塔 coherence** — n ≤ m ⟹ π₉^{3n+5} ∣ (x_m − x_n)
    （望遠鏡・各段は q9cl_step_dvd + 指数単調）。 -/
theorem q9cl_tower_dvd (u : q3rqCar) (n : Nat) :
    ∀ m, n ≤ m → q9wrDvd (q9nfPiPow (3 * n + 5))
      (q3kAdd (q9ncSeq u m) (q3kNeg (q9ncSeq u n))) := by
  intro m
  induction m with
  | zero =>
    intro h0
    have hn : n = 0 := Nat.le_zero.mp h0
    subst hn
    have hz : q3kAdd (q9ncSeq u 0) (q3kNeg (q9ncSeq u 0)) = q3kZero := by
      rw [q9nf_kA_eq, q9ps_kN_eq, q9nf_kZ_eq]
      exact q3kRing.add_neg (q9ncSeq u 0)
    rw [hz]
    exact q9nf_dvd_zero _
  | succ m ih =>
    intro hnm
    cases Nat.lt_or_ge n (m + 1) with
    | inl hlt =>
      have hle : n ≤ m := Nat.lt_succ_iff.mp hlt
      have h1 := ih hle
      have h2 : q9wrDvd (q9nfPiPow (3 * n + 5))
          (q3kAdd (q9ncSeq u (m + 1)) (q3kNeg (q9ncSeq u m))) :=
        q9nf_dvd_of_le (show 3 * n + 5 ≤ 3 * m + 5 by omega) (q9cl_step_dvd u m)
      have hsplit : q3kAdd (q9ncSeq u (m + 1)) (q3kNeg (q9ncSeq u n))
          = q3kAdd (q3kAdd (q9ncSeq u (m + 1)) (q3kNeg (q9ncSeq u m)))
              (q3kAdd (q9ncSeq u m) (q3kNeg (q9ncSeq u n))) := by
        rw [q9nf_kA_eq, q9ps_kN_eq]
        exact (q9cl_sub_merge q3kRing (q9ncSeq u (m + 1)) (q9ncSeq u m)
          (q9ncSeq u n)).symm
      rw [hsplit]
      exact q9nf_dvd_add h2 h1
    | inr hge =>
      have heq : n = m + 1 := Nat.le_antisymm hnm hge
      subst heq
      have hz : q3kAdd (q9ncSeq u (m + 1)) (q3kNeg (q9ncSeq u (m + 1))) = q3kZero := by
        rw [q9nf_kA_eq, q9ps_kN_eq, q9nf_kZ_eq]
        exact q3kRing.add_neg (q9ncSeq u (m + 1))
      rw [hz]
      exact q9nf_dvd_zero _

/-! ## q9cl-5: M3b — 極限構成（z3cLim の 6 座標適用・modulus M(t)=2t） -/

/-- **q9cl-5a: 差の π₉^{6t} 可除 ⟹ 6 座標のレベル t 成分一致**（M3a ブリッジ + z3c_sub_eq）。 -/
theorem q9cl_sub_val_eq {a b : q3kCar} {t : Nat}
    (h : q9wrDvd (q9nfPiPow (6 * t)) (q3kAdd a (q3kNeg b))) :
    a.1.1.val t = b.1.1.val t ∧ a.1.2.val t = b.1.2.val t ∧
    a.2.1.1.val t = b.2.1.1.val t ∧ a.2.1.2.val t = b.2.1.2.val t ∧
    a.2.2.1.val t = b.2.2.1.val t ∧ a.2.2.2.val t = b.2.2.2.val t := by
  have hc := q9cl_dvd6_coords t h
  exact ⟨z3c_sub_eq (a := a.1.1) (b := b.1.1) hc.1,
    z3c_sub_eq (a := a.1.2) (b := b.1.2) hc.2.1,
    z3c_sub_eq (a := a.2.1.1) (b := b.2.1.1) hc.2.2.1,
    z3c_sub_eq (a := a.2.1.2) (b := b.2.1.2) hc.2.2.2.1,
    z3c_sub_eq (a := a.2.2.1) (b := b.2.2.1) hc.2.2.2.2.1,
    z3c_sub_eq (a := a.2.2.2) (b := b.2.2.2) hc.2.2.2.2.2⟩

/-- **q9cl-5b: 塔の 6 座標レベル一致**（modulus M(t)=2t: 2t ≤ i, j ⟹ レベル t 成分一致。
    3·(2t)+5 = 6t+5 ≥ 6t の閉じた式・∃ 消去不要）。 -/
theorem q9cl_seq_val (u : q3rqCar) (t i j : Nat) (hi : 2 * t ≤ i) (hj : 2 * t ≤ j) :
    (q9ncSeq u i).1.1.val t = (q9ncSeq u j).1.1.val t ∧
    (q9ncSeq u i).1.2.val t = (q9ncSeq u j).1.2.val t ∧
    (q9ncSeq u i).2.1.1.val t = (q9ncSeq u j).2.1.1.val t ∧
    (q9ncSeq u i).2.1.2.val t = (q9ncSeq u j).2.1.2.val t ∧
    (q9ncSeq u i).2.2.1.val t = (q9ncSeq u j).2.2.1.val t ∧
    (q9ncSeq u i).2.2.2.val t = (q9ncSeq u j).2.2.2.val t := by
  cases Nat.le_total j i with
  | inl hji =>
    exact q9cl_sub_val_eq
      (q9nf_dvd_of_le (show 6 * t ≤ 3 * j + 5 by omega) (q9cl_tower_dvd u j i hji))
  | inr hij =>
    have h6 := q9cl_sub_val_eq
      (q9nf_dvd_of_le (show 6 * t ≤ 3 * i + 5 by omega) (q9cl_tower_dvd u i j hij))
    exact ⟨h6.1.symm, h6.2.1.symm, h6.2.2.1.symm, h6.2.2.2.1.symm,
      h6.2.2.2.2.1.symm, h6.2.2.2.2.2.symm⟩

/-- 座標 1 の modulus-Cauchy 性。 -/
theorem q9cl_cauchy1 (u : q3rqCar) :
    z3cIsModCauchy (fun n => (q9ncSeq u n).1.1) (fun t => 2 * t) :=
  fun t i j hi hj => (q9cl_seq_val u t i j hi hj).1

/-- 座標 2 の modulus-Cauchy 性。 -/
theorem q9cl_cauchy2 (u : q3rqCar) :
    z3cIsModCauchy (fun n => (q9ncSeq u n).1.2) (fun t => 2 * t) :=
  fun t i j hi hj => (q9cl_seq_val u t i j hi hj).2.1

/-- 座標 3 の modulus-Cauchy 性。 -/
theorem q9cl_cauchy3 (u : q3rqCar) :
    z3cIsModCauchy (fun n => (q9ncSeq u n).2.1.1) (fun t => 2 * t) :=
  fun t i j hi hj => (q9cl_seq_val u t i j hi hj).2.2.1

/-- 座標 4 の modulus-Cauchy 性。 -/
theorem q9cl_cauchy4 (u : q3rqCar) :
    z3cIsModCauchy (fun n => (q9ncSeq u n).2.1.2) (fun t => 2 * t) :=
  fun t i j hi hj => (q9cl_seq_val u t i j hi hj).2.2.2.1

/-- 座標 5 の modulus-Cauchy 性。 -/
theorem q9cl_cauchy5 (u : q3rqCar) :
    z3cIsModCauchy (fun n => (q9ncSeq u n).2.2.1) (fun t => 2 * t) :=
  fun t i j hi hj => (q9cl_seq_val u t i j hi hj).2.2.2.2.1

/-- 座標 6 の modulus-Cauchy 性。 -/
theorem q9cl_cauchy6 (u : q3rqCar) :
    z3cIsModCauchy (fun n => (q9ncSeq u n).2.2.2) (fun t => 2 * t) :=
  fun t i j hi hj => (q9cl_seq_val u t i j hi hj).2.2.2.2.2

/-- **q9cl-5c（★★ M3b）: 逐次近似塔の極限** — z3cLim の 6 座標適用
    （modulus M(t)=2t の閉じた式・choice ゼロ・データ関数）。 -/
def q9clLim (u : q3rqCar) : q3kCar :=
  ((((z3cLim (fun n => (q9ncSeq u n).1.1) (fun t => 2 * t) (q9cl_cauchy1 u),
      z3cLim (fun n => (q9ncSeq u n).1.2) (fun t => 2 * t) (q9cl_cauchy2 u)) : q3rqCar),
    ((z3cLim (fun n => (q9ncSeq u n).2.1.1) (fun t => 2 * t) (q9cl_cauchy3 u),
      z3cLim (fun n => (q9ncSeq u n).2.1.2) (fun t => 2 * t) (q9cl_cauchy4 u)) : q3rqCar),
    ((z3cLim (fun n => (q9ncSeq u n).2.2.1) (fun t => 2 * t) (q9cl_cauchy5 u),
      z3cLim (fun n => (q9ncSeq u n).2.2.2) (fun t => 2 * t) (q9cl_cauchy6 u)) : q3rqCar)) : q3kCar)

/-- **q9cl-5d: 単調化 modulus の閉形式** — M(t)=2t は既に単調なので M'(t) = 2t。 -/
theorem q9cl_modUp_eq (t : Nat) : z3cModUp (fun t => 2 * t) t = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show Nat.max (2 * (t + 1)) (z3cModUp (fun t => 2 * t) t) = 2 * (t + 1)
    rw [ih]
    exact Nat.max_eq_left (by omega)

/-- **q9cl-5e（★★ M3b 収束）: ∀t ∀i≥2t, π₉^{6t} ∣ (x_i − q9clLim u)**
    （z3c_converges の 6 座標 witness を M3a ブリッジで O_M witness に再組立て）。 -/
theorem q9cl_lim_conv (u : q3rqCar) (t i : Nat) (hi : 2 * t ≤ i) :
    q9wrDvd (q9nfPiPow (6 * t))
      (q3kAdd (q9ncSeq u i) (q3kNeg (q9clLim u))) := by
  have hi' : z3cModUp (fun t => 2 * t) t ≤ i := by
    rw [q9cl_modUp_eq t]
    exact hi
  exact q9cl_coords_dvd6 t
    ⟨z3c_converges (fun n => (q9ncSeq u n).1.1) (fun t => 2 * t) (q9cl_cauchy1 u) t i hi',
     z3c_converges (fun n => (q9ncSeq u n).1.2) (fun t => 2 * t) (q9cl_cauchy2 u) t i hi',
     z3c_converges (fun n => (q9ncSeq u n).2.1.1) (fun t => 2 * t) (q9cl_cauchy3 u) t i hi',
     z3c_converges (fun n => (q9ncSeq u n).2.1.2) (fun t => 2 * t) (q9cl_cauchy4 u) t i hi',
     z3c_converges (fun n => (q9ncSeq u n).2.2.1) (fun t => 2 * t) (q9cl_cauchy5 u) t i hi',
     z3c_converges (fun n => (q9ncSeq u n).2.2.2) (fun t => 2 * t) (q9cl_cauchy6 u) t i hi'⟩

/-! ## q9cl-6: M3c-1 — N の連続性（望遠鏡恒等式 + σ の可除性保存） -/

/-- σ は反元と可換。 -/
theorem q9cl_sigma_neg (y : q3kCar) : q3kSigma (q3kNeg y) = q3kNeg (q3kSigma y) := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta (q3rqNeg y.2.1) = q3rqNeg (q3rqMul q3rqZeta y.2.1)
    rw [q3k_M_eq, q3k_N_eq]
    exact q3rqRing.mul_neg q3rqZeta y.2.1
  · show q3rqMul q3rqZetaSq (q3rqNeg y.2.2) = q3rqNeg (q3rqMul q3rqZetaSq y.2.2)
    rw [q3k_M_eq, q3k_N_eq]
    exact q3rqRing.mul_neg q3rqZetaSq y.2.2

/-- σ² は反元と可換。 -/
theorem q9cl_sigma2_neg (y : q3kCar) : q3kSigma2 (q3kNeg y) = q3kNeg (q3kSigma2 y) := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZetaSq (q3rqNeg y.2.1) = q3rqNeg (q3rqMul q3rqZetaSq y.2.1)
    rw [q3k_M_eq, q3k_N_eq]
    exact q3rqRing.mul_neg q3rqZetaSq y.2.1
  · show q3rqMul q3rqZeta (q3rqNeg y.2.2) = q3rqNeg (q3rqMul q3rqZeta y.2.2)
    rw [q3k_M_eq, q3k_N_eq]
    exact q3rqRing.mul_neg q3rqZeta y.2.2

/-- σ(x−y) = σx − σy。 -/
theorem q9cl_sigma_sub (x y : q3kCar) :
    q3kSigma (q3kAdd x (q3kNeg y)) = q3kAdd (q3kSigma x) (q3kNeg (q3kSigma y)) := by
  rw [q9nf_sigma_add x (q3kNeg y), q9cl_sigma_neg y]

/-- σ²(x−y) = σ²x − σ²y。 -/
theorem q9cl_sigma2_sub (x y : q3kCar) :
    q3kSigma2 (q3kAdd x (q3kNeg y)) = q3kAdd (q3kSigma2 x) (q3kNeg (q3kSigma2 y)) := by
  rw [q9nf_sigma2_add x (q3kNeg y), q9cl_sigma2_neg y]

/-- d ∣ x ⟹ d ∣ y·x（左乗法）。 -/
theorem q9cl_dvd_mul_left {d x : q3kCar} (h : q9wrDvd d x) (y : q3kCar) :
    q9wrDvd d (q3kMul y x) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨q3kMul y c, ?_⟩
  rw [hc, q3k_kM_eq]
  exact CRing.mul_left_comm q3kRing y d c

/-- **q9cl-6a: 3 積の望遠鏡恒等式**（純可換環）:
    a·sa·ta − b·sb·tb = (a−b)·sa·ta + b·(sa−sb)·ta + b·sb·(ta−tb)。 -/
theorem q9cl_tele_ring (R : CRing) (a b sa sb ta tb : R.carrier) :
    R.add (R.mul a (R.mul sa ta)) (R.neg (R.mul b (R.mul sb tb)))
      = R.add (R.mul (R.add a (R.neg b)) (R.mul sa ta))
          (R.add (R.mul b (R.mul (R.add sa (R.neg sb)) ta))
            (R.mul b (R.mul sb (R.add ta (R.neg tb))))) := by
  rw [CRing.right_distrib R a (R.neg b) (R.mul sa ta),
      R.neg_mul b (R.mul sa ta),
      CRing.right_distrib R sa (R.neg sb) ta,
      R.neg_mul sb ta,
      R.left_distrib b (R.mul sa ta) (R.neg (R.mul sb ta)),
      R.mul_neg b (R.mul sb ta),
      R.left_distrib sb ta (R.neg tb),
      R.mul_neg sb tb,
      R.left_distrib b (R.mul sb ta) (R.neg (R.mul sb tb)),
      R.mul_neg b (R.mul sb tb),
      q9cl_sub_merge R (R.mul b (R.mul sa ta)) (R.mul b (R.mul sb ta))
        (R.mul b (R.mul sb tb)),
      q9cl_sub_merge R (R.mul a (R.mul sa ta)) (R.mul b (R.mul sa ta))
        (R.mul b (R.mul sb tb))]

/-- **q9cl-6b（★★ M3c-1）: N の連続性（π₉-Lipschitz）** —
    π₉^m ∣ (x−y) ⟹ π₉^m ∣ (embed(Nx) − embed(Ny))
    （N = x·σx·σ²x の望遠鏡分解 + σ/σ² の可除性保存）。 -/
theorem q9cl_norm_cont (m : Nat) (x y : q3kCar)
    (h : q9wrDvd (q9nfPiPow m) (q3kAdd x (q3kNeg y))) :
    q9wrDvd (q9nfPiPow m)
      (q3kAdd (q3kEmbed (q3kNormBase x)) (q3kNeg (q3kEmbed (q3kNormBase y)))) := by
  have hs : q9wrDvd (q9nfPiPow m) (q3kAdd (q3kSigma x) (q3kNeg (q3kSigma y))) := by
    have hσ := q9nf_dvd_sigma m (q3kAdd x (q3kNeg y)) h
    rw [q9cl_sigma_sub x y] at hσ
    exact hσ
  have hs2 : q9wrDvd (q9nfPiPow m) (q3kAdd (q3kSigma2 x) (q3kNeg (q3kSigma2 y))) := by
    have hσ2 := q9nf_dvd_sigma2 m (q3kAdd x (q3kNeg y)) h
    rw [q9cl_sigma2_sub x y] at hσ2
    exact hσ2
  have htele : q3kAdd (q3kEmbed (q3kNormBase x)) (q3kNeg (q3kEmbed (q3kNormBase y)))
      = q3kAdd (q3kMul (q3kAdd x (q3kNeg y)) (q3kMul (q3kSigma x) (q3kSigma2 x)))
          (q3kAdd
            (q3kMul y (q3kMul (q3kAdd (q3kSigma x) (q3kNeg (q3kSigma y))) (q3kSigma2 x)))
            (q3kMul y (q3kMul (q3kSigma y)
              (q3kAdd (q3kSigma2 x) (q3kNeg (q3kSigma2 y)))))) := by
    rw [← q3k_norm_eq x, ← q3k_norm_eq y, q3k_kM_eq, q9nf_kA_eq, q9ps_kN_eq]
    exact q9cl_tele_ring q3kRing x y (q3kSigma x) (q3kSigma y) (q3kSigma2 x) (q3kSigma2 y)
  rw [htele]
  apply q9nf_dvd_add
  · exact q9nf_dvd_mul_right h (q3kMul (q3kSigma x) (q3kSigma2 x))
  apply q9nf_dvd_add
  · exact q9cl_dvd_mul_left (q9nf_dvd_mul_right hs (q3kSigma2 x)) y
  · exact q9cl_dvd_mul_left (q9cl_dvd_mul_left hs2 (q3kSigma y)) y

/-! ## q9cl-7: M3c-3 — 組み立て（★★★ T3-core: N(q9clLim u) = u） -/

/-- **q9cl-7a: 近似の π₉ 形** — u ∈ U^{(9)} ⟹ π₉^{3(3+n)} ∣ (embed u − embed(N x_n))
    （q9nc_approx の λ 番号を embed(λ^j) = π₉^{3j}·(w⁻¹)^j で π₉ 番号へ）。 -/
theorem q9cl_approx_pi (u : q3rqCar) (hu : q9nfUfilt 9 (q3kEmbed u)) (n : Nat) :
    q9wrDvd (q9nfPiPow (3 * (3 + n)))
      (q3kAdd (q3kEmbed u) (q3kNeg (q3kEmbed (q3kNormBase (q9ncSeq u n))))) := by
  obtain ⟨f, hf⟩ := q9nc_approx u hu n
  refine ⟨q3kMul (q9ncWinvPow (3 + n)) (q3kEmbed f), ?_⟩
  rw [q9ps_kN_eq, q9ps_embed_neg (q3kNormBase (q9ncSeq u n)),
      ← q9rf_embed_add u (q3rqNeg (q3kNormBase (q9ncSeq u n))), hf,
      ← q3k_embed_mul (q3rqLamPow (3 + n)) f, q9nc_embed_lampow (3 + n), q3k_kM_eq]
  exact q3kRing.mul_assoc (q9nfPiPow (3 * (3 + n))) (q9ncWinvPow (3 + n)) (q3kEmbed f)

/-- **q9cl-7b: 全レベル可除** — u ∈ U^{(9)} ⟹ ∀t, π₉^{6t} ∣ (embed u − embed(N(q9clLim u)))
    （n = 2t で M2 近似（π₉^{6t+9}）+ M3b 収束 + M3c-1 連続性を合流）。 -/
theorem q9cl_gap_dvd (u : q3rqCar) (hu : q9nfUfilt 9 (q3kEmbed u)) (t : Nat) :
    q9wrDvd (q9nfPiPow (6 * t))
      (q3kAdd (q3kEmbed u) (q3kNeg (q3kEmbed (q3kNormBase (q9clLim u))))) := by
  have hA : q9wrDvd (q9nfPiPow (6 * t))
      (q3kAdd (q3kEmbed u) (q3kNeg (q3kEmbed (q3kNormBase (q9ncSeq u (2 * t)))))) :=
    q9nf_dvd_of_le (show 6 * t ≤ 3 * (3 + 2 * t) by omega) (q9cl_approx_pi u hu (2 * t))
  have hB : q9wrDvd (q9nfPiPow (6 * t))
      (q3kAdd (q3kEmbed (q3kNormBase (q9ncSeq u (2 * t))))
        (q3kNeg (q3kEmbed (q3kNormBase (q9clLim u))))) :=
    q9cl_norm_cont (6 * t) (q9ncSeq u (2 * t)) (q9clLim u)
      (q9cl_lim_conv u t (2 * t) (Nat.le_refl _))
  have hsplit : q3kAdd (q3kEmbed u) (q3kNeg (q3kEmbed (q3kNormBase (q9clLim u))))
      = q3kAdd
          (q3kAdd (q3kEmbed u) (q3kNeg (q3kEmbed (q3kNormBase (q9ncSeq u (2 * t))))))
          (q3kAdd (q3kEmbed (q3kNormBase (q9ncSeq u (2 * t))))
            (q3kNeg (q3kEmbed (q3kNormBase (q9clLim u))))) := by
    rw [q9nf_kA_eq, q9ps_kN_eq]
    exact (q9cl_sub_merge q3kRing (q3kEmbed u)
      (q3kEmbed (q3kNormBase (q9ncSeq u (2 * t))))
      (q3kEmbed (q3kNormBase (q9clLim u)))).symm
  rw [hsplit]
  exact q9nf_dvd_add hA hB

/-- **q9cl-7c（★★★ T3-core・厳密等式）: u ∈ U^{(9)} ⟹ N(q9clLim u) = u**
    （全レベル可除 + O_M 分離性 + embed 単射）。主単数 u は**厳密に**ノルムである。 -/
theorem q9cl_norm_exact (u : q3rqCar) (hu : q9nfUfilt 9 (q3kEmbed u)) :
    q3kNormBase (q9clLim u) = u := by
  have hz : q3kAdd (q3kEmbed u) (q3kNeg (q3kEmbed (q3kNormBase (q9clLim u)))) = q3kZero :=
    q9cl_sep _ (q9cl_gap_dvd u hu)
  have hz' : q3kEmbed u = q3kEmbed (q3kNormBase (q9clLim u)) :=
    CRing.eq_of_sub_eq_zero q3kRing hz
  exact (q3k_embed_inj hz').symm

/-- **q9cl-7d（★★★ T3-core・ノルム全射性・主単数レベル）**:
    u ∈ U^{(9)} 単数 ⟹ ∃ x ∈ O_M^×, N(x) = u（構成 x = q9clLim u・choice 無縁）。 -/
theorem q9cl_norm_surj (u : q3rqCar) (huU : q3rqUnitMem u)
    (hu : q9nfUfilt 9 (q3kEmbed u)) :
    ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = u := by
  refine ⟨q9clLim u, ?_, q9cl_norm_exact u hu⟩
  show q3rqUnitMem (q3kNormBase (q9clLim u))
  rw [q9cl_norm_exact u hu]
  exact huU

/-! ## q9cl-8: capstone（T3-M3 完了データ） -/

/-- **q9cl-8a: T3-M3 完了データ**（座標ブリッジ・π₉⇔3・極限・収束・連続性・分離・厳密等式）。 -/
structure Q3NormSurjCompleteLimitData where
  /-- M3a-3: π₉^{6k} ∣ z ⟺ 3^k ∣ z。 -/
  pi6_iff_three : ∀ (k : Nat) (z : q3kCar),
    q9wrDvd (q9nfPiPow (6 * k)) z ↔ (∃ e, z = q9clMul3Pow k e)
  /-- M3b: 極限収束（∀t ∀i≥2t, π₉^{6t}∣(x_i − lim)）。 -/
  lim_conv : ∀ (u : q3rqCar) (t i : Nat), 2 * t ≤ i →
    q9wrDvd (q9nfPiPow (6 * t)) (q3kAdd (q9ncSeq u i) (q3kNeg (q9clLim u)))
  /-- M3c-1: N の連続性（π₉-Lipschitz）。 -/
  norm_cont : ∀ (m : Nat) (x y : q3kCar),
    q9wrDvd (q9nfPiPow m) (q3kAdd x (q3kNeg y)) →
    q9wrDvd (q9nfPiPow m)
      (q3kAdd (q3kEmbed (q3kNormBase x)) (q3kNeg (q3kEmbed (q3kNormBase y))))
  /-- M3c-2: O_M 分離性。 -/
  sep : ∀ z : q3kCar, (∀ k, q9wrDvd (q9nfPiPow (6 * k)) z) → z = q3kZero
  /-- ★★★ M3c-3（T3-core）: 厳密等式 N(q9clLim u) = u。 -/
  norm_exact : ∀ u : q3rqCar, q9nfUfilt 9 (q3kEmbed u) → q3kNormBase (q9clLim u) = u
  /-- ★★★ T3-core: 主単数レベルのノルム全射性。 -/
  norm_surj : ∀ u : q3rqCar, q3rqUnitMem u → q9nfUfilt 9 (q3kEmbed u) →
    ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = u

/-- **q9cl-8b: 見出し実例** — 実 O_M/O_{L₂} 上の T3-M3 完了。 -/
def q9cl_data : Q3NormSurjCompleteLimitData where
  pi6_iff_three := q9cl_pi6_iff_three
  lim_conv := q9cl_lim_conv
  norm_cont := q9cl_norm_cont
  sep := q9cl_sep
  norm_exact := q9cl_norm_exact
  norm_surj := q9cl_norm_surj

/-- **q9cl-8c: T3-M3 完了の存在**（T3-core 厳密等式 N(x)=u の実 Lean 化）。 -/
theorem q9cl_exists : Nonempty Q3NormSurjCompleteLimitData := ⟨q9cl_data⟩

end IUT
