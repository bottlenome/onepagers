/-
  IUT/Q3ResidueFieldReal.lean — 柱B・B2 M1: 実残余体 𝔽₃ と O_M の局所性
    （B2 local-reciprocity crux「4 = 1+3 ∉ N_{M/L₂}(M^×)」への足場）

  ── 主要成果の分類: **[実／(c) 承認済み足場]**（named scaffolding）。
  B2 の真の crux「4 ∉ N」（audit/pillar-B2-level6-cokernel-detail-2026-07-11.md §3・
  M3 = 初の status mover）へ向けた M1。実 O_M = q3kRing（実巡回 3 次 Kummer 代数
  M = ℚ₃(ζ₉)）と実 O_{L₂} = q3rqRing の上に、**実残余体 𝔽₃ への還元写像**（環準同型）
  と **O_M の局所性（¬単数 ⟹ π₉ ∣ x・核 = 極大イデアル (π₉)）** を本物の
  実測（Zp3ValuationRing の実 ℤ₃ 剰余体機構・q9ps/q9nf/q9wr の実 π₉ 資産）で建てる。
  toy 主語なし——主語は実 z3 = zpRing 3・実 q3rqRing・実 q3kRing。

  complete_pct 影響: **B2 は 0 のまま（M1 は crux 4∉N への足場・status mover は M3）**。
  本モジュール単体は非ノルムを何も証明しない（残余体・局所性のみ）。後続計画（§2(c)）:
   * M2 `Q3GradedNormBreak.lean`（仮）— level-6 graded 公式と零性（2E₂=Tr²−Tr∘sq・打ち消し）
   * M3 `Q3LocalReciprocityReal.lean`（仮）— **crux 4∉N**（初の status mover・s_B2 0→0.25–0.35）
  本 M1 はその M2/M3 が消費する「res : O_M ↠ 𝔽₃（環準同型）・局所性・div-by-3 witness」を供給する。

  内容:
   * q9rfF3 / q9rfRes3 — 実残余体 𝔽₃ = zmodRing 3 と還元写像 ℤ₃ ↠ 𝔽₃（val-1 射影・構成的）
   * q9rf_res3_add / _mul / _one / _zero / _neg / _three / _three_mul — res の環準同型性・res(3)=0
   * q9rf_div3（★ divide-by-3 witness）— res(c)=0 ⟹ ∃k, c = 3·k（zp_dvd_p_iff 消費・choice-free）
   * q9rfResL — L₂-残余 O_{L₂} ↠ 𝔽₃（λ=√−3 ↦ 0・第 1 座標の res）・環準同型（resL_add/mul）
   * q9rf_resL_zeta / _zetaSq / _lambda / _three — ζ₃↦1・ζ₃²↦1・λ↦0・3↦0
   * q9rfResM — M-残余 O_M ↠ 𝔽₃（Y≡1 mod π₉ で 3 座標を潰す）
   * q9rf_resM_add / _mul（★ 環準同型）— 補正項 (ζ₃−1)·Q が res で消える（残余レベルの本体）
   * q9rf_res_norm（★ res∘N = res³ = res）— Fermat a³=a on 𝔽₃（resM σ 不変性経由）
   * q9rf_kernel（★ 核完全性 ker res = (π₉)）— res(x)=0 ⟹ π₉ ∣ x（div-by-3 + 座標分解）
   * q9rf_local（★ O_M は局所）— ¬単数 ⟹ π₉ ∣ x（res≠0 ⟹ 単数の対偶）
   * Q3ResidueFieldRealData / q9rf_data / q9rf_exists — capstone

  正直な限定（§4 規約により消さない・弱めない・q3k/q9ps/q9nf/q9wr/q3rq 継承の上に追記のみ）:
  1. **残余体は 𝔽₃ のみ**（degree-1・単一拡大 M/L₂/ℚ₃ の完全分岐残余体）。より高次の
     residue extension・剰余体の Galois 理論はゼロ。
  2. **局所性・核は π₉-レベル**（可除性形式 q9wrDvd・v_M 不使用）。極大イデアル (π₉) の
     完全性はレベル 1（核 = (π₉)）で割るが、フィルトレーション U^(i) の完全図式は M2 以降。
  3. **res∘N = res は 𝔽₃ 上の Fermat a³=a 経由**（level-1 のノルム挙動）。高次の graded
     ノルム挙動は M2。
  4. q3k/q9ps/q9nf/q9wr/q3rq の正直限定を全継承（O_M と M^× のみ・体化なし・σ を超える
     Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体・拡大 1 個 M/L₂）。
  5. **非ノルム性（4∉N）はゼロ**（M3 本体）。本 M1 は crux への足場に留まる。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3NormFiltrationSpike
import IUT.PadicDivision
import IUT.Q3Mu3Completeness
import IUT.Q3Mu9Completeness

namespace IUT

/-! ## q9rf-0: 実残余体 𝔽₃ と還元写像 ℤ₃ ↠ 𝔽₃ -/

/-- **実残余体 𝔽₃ = ℤ₃/3ℤ₃ = zmodRing 3**（既設・A2a-8 の剰余体の値域）。 -/
@[reducible] def q9rfF3 : CRing := zmodRing 3

/-- **q9rf-0a: 還元写像 res : ℤ₃ ↠ 𝔽₃**（レベル 1 射影・構成的・choice-free）。 -/
def q9rfRes3 (x : z3.carrier) : q9rfF3.carrier := x.val 1

/-- res は加法を保つ（レベル 1 環準同型 projRing 3 1）。 -/
theorem q9rf_res3_add (a b : z3.carrier) :
    q9rfRes3 (z3.add a b) = q9rfF3.add (q9rfRes3 a) (q9rfRes3 b) :=
  (projRing 3 1).map_add a b

/-- res は乗法を保つ。 -/
theorem q9rf_res3_mul (a b : z3.carrier) :
    q9rfRes3 (z3.mul a b) = q9rfF3.mul (q9rfRes3 a) (q9rfRes3 b) :=
  (projRing 3 1).map_mul a b

/-- res(1) = 1。 -/
theorem q9rf_res3_one : q9rfRes3 z3.one = q9rfF3.one := (projRing 3 1).map_one

/-- res(0) = 0。 -/
theorem q9rf_res3_zero : q9rfRes3 z3.zero = q9rfF3.zero := rfl

/-- res(−a) = −res(a)。 -/
theorem q9rf_res3_neg (a : z3.carrier) :
    q9rfRes3 (z3.neg a) = q9rfF3.neg (q9rfRes3 a) := rfl

/-- **q9rf-0b: res(3) = 0**（3 ≡ 0 mod 3）。 -/
theorem q9rf_res3_three : q9rfRes3 q3rqThree = q9rfF3.zero := by
  show q3rqThree.val 1 = Quot.mk (modCong 3).rel 0
  rw [q3rq_three_val 1]
  apply Quot.sound
  show ((3 ^ 1 : Nat) : Int) ∣ 3 - 0
  rw [Nat.pow_one]
  exact ⟨1, by omega⟩

/-- **q9rf-0c: res(3·x) = 0**。 -/
theorem q9rf_res3_three_mul (x : z3.carrier) :
    q9rfRes3 (z3.mul q3rqThree x) = q9rfF3.zero := by
  rw [q9rf_res3_mul, q9rf_res3_three, q9rfF3.zero_mul]

/-! ## q9rf-1: divide-by-3 witness（★ HELP スポット・zp_dvd_p_iff 消費） -/

/-- (toZp 3).map 3 = q3rqThree（同じ実 ℤ₃ の元 3 の 2 通りの構成の一致）。 -/
theorem q9rf_zvp_eq_three : (toZp 3).map ((3 : Nat) : Int) = q3rqThree := by
  apply Subtype.ext
  funext n
  show ((toZp 3).map ((3 : Nat) : Int)).val n = q3rqThree.val n
  exact (q3rq_three_val n).symm

/-- **q9rf-1a（★ divide-by-3 witness）: res(c) = 0 ⟹ ∃k, c = 3·k**。
    zp_dvd_p_iff（可除性の level-1 判定・M43 の p 除算 zpDivP 経由・choice-free）を
    消費して 3 の witness を陽に構成する。 -/
theorem q9rf_div3 (c : z3.carrier) (h : q9rfRes3 c = q9rfF3.zero) :
    ∃ k, c = z3.mul q3rqThree k := by
  have hx : c.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := h
  obtain ⟨e, he⟩ := (zp_dvd_p_iff 3 (by omega) c).mpr hx
  refine ⟨e, ?_⟩
  rw [he]
  exact congrArg (fun t => zpMul 3 t e) q9rf_zvp_eq_three

/-! ## q9rf-2: L₂-残余 O_{L₂} ↠ 𝔽₃（λ=√−3 ↦ 0・第 1 座標の res） -/

/-- **q9rf-2a: L₂-残余 res_{L₂}**（第 1 座標 = 有理整数部の res・√−3 を潰す）。 -/
def q9rfResL (n : q3rqCar) : q9rfF3.carrier := q9rfRes3 n.1

/-- resL は加法を保つ。 -/
theorem q9rf_resL_add (x y : q3rqCar) :
    q9rfResL (q3rqAdd x y) = q9rfF3.add (q9rfResL x) (q9rfResL y) :=
  q9rf_res3_add x.1 y.1

/-- **q9rf-2b: resL は乗法を保つ**（第 1 座標の D=−3·b·d 項は res で消える）。 -/
theorem q9rf_resL_mul (x y : q3rqCar) :
    q9rfResL (q3rqMul x y) = q9rfF3.mul (q9rfResL x) (q9rfResL y) := by
  show q9rfRes3 (z3.add (z3.mul x.1 y.1) (z3.mul q3rqD (z3.mul x.2 y.2)))
      = q9rfF3.mul (q9rfRes3 x.1) (q9rfRes3 y.1)
  rw [q9rf_res3_add, q9rf_res3_mul]
  have hz : q9rfRes3 (z3.mul q3rqD (z3.mul x.2 y.2)) = q9rfF3.zero := by
    rw [q3rq_D_eq, z3.neg_mul q3rqThree (z3.mul x.2 y.2), q9rf_res3_neg,
        q9rf_res3_three_mul, q9rfF3.neg_zero]
  rw [hz, q9rfF3.add_zero]

/-- **q9rf-2c: resL(λ) = 0**（λ = √−3 = (0,1)・第 1 座標 = 0）。 -/
theorem q9rf_resL_lambda : q9rfResL q3rqLambda = q9rfF3.zero := q9rf_res3_zero

/-- **q9rf-2d: res(1/2) = 2**（2·(1/2)=1 の res・2·? = 1 mod 3 ⟹ ? = 2）。 -/
theorem q9rf_res3_half : q3rqHalf.val 1 = Quot.mk (modCong (3 ^ 1)).rel 2 := by
  obtain ⟨c, hc⟩ := Quot.exists_rep (q3rqHalf.val 1)
  have h2h : (z3.mul q3rqTwoZ q3rqHalf).val 1 = z3.one.val 1 :=
    congrArg (fun z => z.val 1) q3rq_two_half
  rw [q3mc_mul_val1 q3rqTwoZ q3rqHalf 2 c q9c_two_val1 hc.symm] at h2h
  have hone : z3.one.val 1 = Quot.mk (modCong (3 ^ 1)).rel 1 := rfl
  rw [hone] at h2h
  obtain ⟨t, ht⟩ := quot_exact intGrp (modCong (3 ^ 1)) h2h
  rw [Nat.pow_one] at ht
  rw [← hc]
  apply Quot.sound
  show ((3 ^ 1 : Nat) : Int) ∣ c - 2
  rw [Nat.pow_one]
  omega

/-- **q9rf-2e: resL(ζ₃) = 1**（ζ₃ = (−1/2, 1/2)・res(−1/2) = −2 = 1 mod 3）。 -/
theorem q9rf_resL_zeta : q9rfResL q3rqZeta = q9rfF3.one := by
  show q9rfRes3 (z3.neg q3rqHalf) = q9rfF3.one
  rw [q9rf_res3_neg]
  show q9rfF3.neg (q3rqHalf.val 1) = q9rfF3.one
  rw [q9rf_res3_half]
  apply Quot.sound
  show ((3 ^ 1 : Nat) : Int) ∣ (-2) - 1
  rw [Nat.pow_one]
  exact ⟨-1, by omega⟩

/-- **q9rf-2f: resL(ζ₃²) = 1**（ζ₃² = ζ₃·ζ₃ の res = 1·1 = 1）。 -/
theorem q9rf_resL_zetaSq : q9rfResL q3rqZetaSq = q9rfF3.one := by
  show q9rfResL (q3rqMul q3rqZeta q3rqZeta) = q9rfF3.one
  rw [q9rf_resL_mul, q9rf_resL_zeta, q9rfF3.one_mul]

/-- **q9rf-2g: resL(3) = 0**（3 = q3rqThreeElt = (3,0)）。 -/
theorem q9rf_resL_three : q9rfResL q3rqThreeElt = q9rfF3.zero :=
  q9rf_res3_three

/-! ## q9rf-3: M-残余 O_M ↠ 𝔽₃（Y ≡ 1 mod π₉ で 3 座標を潰す） -/

/-- **q9rf-3a: Y=1 評価** — S(x) = x₀ + x₁ + x₂ ∈ O_{L₂}。 -/
def q9rfSum (x : q3kCar) : q3rqCar := q3rqAdd x.1 (q3rqAdd x.2.1 x.2.2)

/-- **q9rf-3b: M-残余 res_M**（Y ≡ 1 mod π₉ で 3 座標を潰した後 resL）。 -/
def q9rfResM (x : q3kCar) : q9rfF3.carrier := q9rfResL (q9rfSum x)

/-- **q9rf-3c: res_M(embed n) = resL(n)**（embed n = (n,0,0)・S = n）。 -/
theorem q9rf_resM_embed (n : q3rqCar) : q9rfResM (q3kEmbed n) = q9rfResL n := by
  show q9rfResL (q3rqAdd n (q3rqAdd q3rqZero q3rqZero)) = q9rfResL n
  have h : q3rqAdd n (q3rqAdd q3rqZero q3rqZero) = n := by
    rw [q3k_A_eq, q3k_Z_eq, q3rqRing.add_zero q3rqRing.zero, q3rqRing.add_zero n]
  rw [h]

/-! ## q9rf-4: 抽象 𝔽₃ 恒等式（加法・乗法の再配置・純環演算） -/

/-- **6 項加法再配置**（res_M 加法性の本体）。 -/
theorem q9rf_f3_add_id (R : CRing) (a0 a1 a2 b0 b1 b2 : R.carrier) :
    R.add (R.add a0 b0) (R.add (R.add a1 b1) (R.add a2 b2))
      = R.add (R.add a0 (R.add a1 a2)) (R.add b0 (R.add b1 b2)) := by
  rw [R.add_add_add_comm a0 (R.add a1 a2) b0 (R.add b1 b2),
      R.add_add_add_comm a1 a2 b1 b2]

/-- **9 項乗積再配置**（res_M 乗法性の本体・分配 + 加法再配置・負符号なし）。 -/
theorem q9rf_f3_mul_id (R : CRing) (a0 a1 a2 b0 b1 b2 : R.carrier) :
    R.add (R.add (R.mul a0 b0) (R.add (R.mul a1 b2) (R.mul a2 b1)))
          (R.add (R.add (R.add (R.mul a0 b1) (R.mul a1 b0)) (R.mul a2 b2))
                 (R.add (R.add (R.mul a0 b2) (R.mul a1 b1)) (R.mul a2 b0)))
      = R.mul (R.add a0 (R.add a1 a2)) (R.add b0 (R.add b1 b2)) := by
  have hR :
      R.mul (R.add a0 (R.add a1 a2)) (R.add b0 (R.add b1 b2))
      = R.add (R.mul a0 b0) (R.add (R.mul a0 b1) (R.add (R.mul a0 b2)
          (R.add (R.mul a1 b0) (R.add (R.mul a1 b1) (R.add (R.mul a1 b2)
            (R.add (R.mul a2 b0) (R.add (R.mul a2 b1) (R.mul a2 b2)))))))) := by
    rw [R.right_distrib a0 (R.add a1 a2) (R.add b0 (R.add b1 b2)),
        R.right_distrib a1 a2 (R.add b0 (R.add b1 b2)),
        R.left_distrib a0 b0 (R.add b1 b2), R.left_distrib a0 b1 b2,
        R.left_distrib a1 b0 (R.add b1 b2), R.left_distrib a1 b1 b2,
        R.left_distrib a2 b0 (R.add b1 b2), R.left_distrib a2 b1 b2,
        R.add_assoc (R.mul a0 b0) (R.add (R.mul a0 b1) (R.mul a0 b2))
          (R.add (R.add (R.mul a1 b0) (R.add (R.mul a1 b1) (R.mul a1 b2)))
                 (R.add (R.mul a2 b0) (R.add (R.mul a2 b1) (R.mul a2 b2)))),
        R.add_assoc (R.mul a0 b1) (R.mul a0 b2)
          (R.add (R.add (R.mul a1 b0) (R.add (R.mul a1 b1) (R.mul a1 b2)))
                 (R.add (R.mul a2 b0) (R.add (R.mul a2 b1) (R.mul a2 b2)))),
        R.add_assoc (R.mul a1 b0) (R.add (R.mul a1 b1) (R.mul a1 b2))
          (R.add (R.mul a2 b0) (R.add (R.mul a2 b1) (R.mul a2 b2))),
        R.add_assoc (R.mul a1 b1) (R.mul a1 b2)
          (R.add (R.mul a2 b0) (R.add (R.mul a2 b1) (R.mul a2 b2)))]
  rw [hR]
  -- LHS を flat 化（順序 [00,12,21,01,10,22,02,11,20]）
  rw [R.add_assoc (R.mul a0 b0) (R.add (R.mul a1 b2) (R.mul a2 b1))
        (R.add (R.add (R.add (R.mul a0 b1) (R.mul a1 b0)) (R.mul a2 b2))
               (R.add (R.add (R.mul a0 b2) (R.mul a1 b1)) (R.mul a2 b0))),
      R.add_assoc (R.mul a1 b2) (R.mul a2 b1)
        (R.add (R.add (R.add (R.mul a0 b1) (R.mul a1 b0)) (R.mul a2 b2))
               (R.add (R.add (R.mul a0 b2) (R.mul a1 b1)) (R.mul a2 b0))),
      R.add_assoc (R.add (R.mul a0 b1) (R.mul a1 b0)) (R.mul a2 b2)
        (R.add (R.add (R.mul a0 b2) (R.mul a1 b1)) (R.mul a2 b0)),
      R.add_assoc (R.mul a0 b1) (R.mul a1 b0)
        (R.add (R.mul a2 b2) (R.add (R.add (R.mul a0 b2) (R.mul a1 b1)) (R.mul a2 b0))),
      R.add_assoc (R.mul a0 b2) (R.mul a1 b1) (R.mul a2 b0)]
  -- flat: p00 + (p12 + (p21 + (p01 + (p10 + (p22 + (p02 + (p11 + p20)))))))
  -- 13 回の swap で [01,02,10,11,12,20,21,22] へ整列
  rw [q9nf_add_swap R (R.mul a2 b1) (R.mul a0 b1),
      q9nf_add_swap R (R.mul a1 b2) (R.mul a0 b1),
      q9nf_add_swap R (R.mul a2 b2) (R.mul a0 b2),
      q9nf_add_swap R (R.mul a1 b0) (R.mul a0 b2),
      q9nf_add_swap R (R.mul a2 b1) (R.mul a0 b2),
      q9nf_add_swap R (R.mul a1 b2) (R.mul a0 b2),
      q9nf_add_swap R (R.mul a2 b1) (R.mul a1 b0),
      q9nf_add_swap R (R.mul a1 b2) (R.mul a1 b0),
      q9nf_add_swap R (R.mul a2 b2) (R.mul a1 b1),
      q9nf_add_swap R (R.mul a2 b1) (R.mul a1 b1),
      q9nf_add_swap R (R.mul a1 b2) (R.mul a1 b1),
      R.add_comm (R.mul a2 b2) (R.mul a2 b0),
      q9nf_add_swap R (R.mul a2 b1) (R.mul a2 b0)]

/-! ## q9rf-5: res_M の環準同型性 -/

/-- **q9rf-5a: res_M は加法を保つ**。 -/
theorem q9rf_resM_add (x y : q3kCar) :
    q9rfResM (q3kAdd x y) = q9rfF3.add (q9rfResM x) (q9rfResM y) := by
  have hL : q9rfResM (q3kAdd x y)
      = q9rfF3.add (q9rfF3.add (q9rfResL x.1) (q9rfResL y.1))
          (q9rfF3.add (q9rfF3.add (q9rfResL x.2.1) (q9rfResL y.2.1))
            (q9rfF3.add (q9rfResL x.2.2) (q9rfResL y.2.2))) := by
    show q9rfResL (q3rqAdd (q3rqAdd x.1 y.1)
        (q3rqAdd (q3rqAdd x.2.1 y.2.1) (q3rqAdd x.2.2 y.2.2))) = _
    rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_add, q9rf_resL_add, q9rf_resL_add]
  have hR : q9rfF3.add (q9rfResM x) (q9rfResM y)
      = q9rfF3.add (q9rfF3.add (q9rfResL x.1) (q9rfF3.add (q9rfResL x.2.1) (q9rfResL x.2.2)))
          (q9rfF3.add (q9rfResL y.1) (q9rfF3.add (q9rfResL y.2.1) (q9rfResL y.2.2))) := by
    show q9rfF3.add (q9rfResL (q3rqAdd x.1 (q3rqAdd x.2.1 x.2.2)))
        (q9rfResL (q3rqAdd y.1 (q3rqAdd y.2.1 y.2.2))) = _
    rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_add, q9rf_resL_add]
  rw [hL, hR]
  exact q9rf_f3_add_id q9rfF3 (q9rfResL x.1) (q9rfResL x.2.1) (q9rfResL x.2.2)
    (q9rfResL y.1) (q9rfResL y.2.1) (q9rfResL y.2.2)

/-- **q9rf-5b（★）: res_M は乗法を保つ** — 残余レベルで ζ₃↦1・補正項 (ζ₃−1)·Q↦0。 -/
theorem q9rf_resM_mul (x y : q3kCar) :
    q9rfResM (q3kMul x y) = q9rfF3.mul (q9rfResM x) (q9rfResM y) := by
  have hC0 : q9rfResL (q3kMul x y).1
      = q9rfF3.add (q9rfF3.mul (q9rfResL x.1) (q9rfResL y.1))
          (q9rfF3.add (q9rfF3.mul (q9rfResL x.2.1) (q9rfResL y.2.2))
            (q9rfF3.mul (q9rfResL x.2.2) (q9rfResL y.2.1))) := by
    show q9rfResL (q3rqAdd (q3rqMul x.1 y.1)
        (q3rqMul q3rqZeta (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1)))) = _
    rw [q9rf_resL_add, q9rf_resL_mul, q9rf_resL_mul, q9rf_resL_zeta,
        q9rf_resL_add, q9rf_resL_mul, q9rf_resL_mul, q9rfF3.one_mul]
  have hC1 : q9rfResL (q3kMul x y).2.1
      = q9rfF3.add (q9rfF3.add (q9rfF3.mul (q9rfResL x.1) (q9rfResL y.2.1))
          (q9rfF3.mul (q9rfResL x.2.1) (q9rfResL y.1)))
          (q9rfF3.mul (q9rfResL x.2.2) (q9rfResL y.2.2)) := by
    show q9rfResL (q3rqAdd (q3rqAdd (q3rqMul x.1 y.2.1) (q3rqMul x.2.1 y.1))
        (q3rqMul q3rqZeta (q3rqMul x.2.2 y.2.2))) = _
    rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_mul, q9rf_resL_mul,
        q9rf_resL_mul, q9rf_resL_zeta, q9rf_resL_mul, q9rfF3.one_mul]
  have hC2 : q9rfResL (q3kMul x y).2.2
      = q9rfF3.add (q9rfF3.add (q9rfF3.mul (q9rfResL x.1) (q9rfResL y.2.2))
          (q9rfF3.mul (q9rfResL x.2.1) (q9rfResL y.2.1)))
          (q9rfF3.mul (q9rfResL x.2.2) (q9rfResL y.1)) := by
    show q9rfResL (q3rqAdd (q3rqAdd (q3rqMul x.1 y.2.2) (q3rqMul x.2.1 y.2.1))
        (q3rqMul x.2.2 y.1)) = _
    rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_mul, q9rf_resL_mul, q9rf_resL_mul]
  have hL : q9rfResM (q3kMul x y)
      = q9rfF3.add (q9rfF3.add (q9rfF3.mul (q9rfResL x.1) (q9rfResL y.1))
            (q9rfF3.add (q9rfF3.mul (q9rfResL x.2.1) (q9rfResL y.2.2))
              (q9rfF3.mul (q9rfResL x.2.2) (q9rfResL y.2.1))))
          (q9rfF3.add
            (q9rfF3.add (q9rfF3.add (q9rfF3.mul (q9rfResL x.1) (q9rfResL y.2.1))
              (q9rfF3.mul (q9rfResL x.2.1) (q9rfResL y.1)))
              (q9rfF3.mul (q9rfResL x.2.2) (q9rfResL y.2.2)))
            (q9rfF3.add (q9rfF3.add (q9rfF3.mul (q9rfResL x.1) (q9rfResL y.2.2))
              (q9rfF3.mul (q9rfResL x.2.1) (q9rfResL y.2.1)))
              (q9rfF3.mul (q9rfResL x.2.2) (q9rfResL y.1)))) := by
    show q9rfResL (q3rqAdd (q3kMul x y).1
        (q3rqAdd (q3kMul x y).2.1 (q3kMul x y).2.2)) = _
    rw [q9rf_resL_add, q9rf_resL_add, hC0, hC1, hC2]
  have hR : q9rfF3.mul (q9rfResM x) (q9rfResM y)
      = q9rfF3.mul (q9rfF3.add (q9rfResL x.1) (q9rfF3.add (q9rfResL x.2.1) (q9rfResL x.2.2)))
          (q9rfF3.add (q9rfResL y.1) (q9rfF3.add (q9rfResL y.2.1) (q9rfResL y.2.2))) := by
    show q9rfF3.mul (q9rfResL (q3rqAdd x.1 (q3rqAdd x.2.1 x.2.2)))
        (q9rfResL (q3rqAdd y.1 (q3rqAdd y.2.1 y.2.2))) = _
    rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_add, q9rf_resL_add]
  rw [hL, hR]
  exact q9rf_f3_mul_id q9rfF3 (q9rfResL x.1) (q9rfResL x.2.1) (q9rfResL x.2.2)
    (q9rfResL y.1) (q9rfResL y.2.1) (q9rfResL y.2.2)

/-! ## q9rf-6: res∘N = res³ = res（Fermat a³=a on 𝔽₃） -/

/-- **𝔽₃ の Fermat: r·(r·r) = r**（a³ ≡ a mod 3）。 -/
theorem q9rf_f3_cube (r : q9rfF3.carrier) : q9rfF3.mul r (q9rfF3.mul r r) = r := by
  induction r using Quot.ind
  rename_i a
  show Quot.mk (modCong 3).rel (a * (a * a)) = Quot.mk (modCong 3).rel a
  apply Quot.sound
  show ((3 : Nat) : Int) ∣ (a * (a * a)) - a
  have hf : ((3 : Nat) : Int) ∣ ipow a 3 - a := by
    have := fermat_little 3 isPrime_three a
    exact this
  have hi : ipow a 3 = a * (a * a) := by
    show ipow a 2 * a = a * (a * a)
    show (ipow a 1 * a) * a = a * (a * a)
    show ((ipow a 0 * a) * a) * a = a * (a * a)
    show ((1 * a) * a) * a = a * (a * a)
    rw [Int.one_mul, Int.mul_assoc]
  rw [← hi]
  exact hf

/-- **q9rf-6a: res_M(σx) = res_M(x)**（ζ₃≡1 mod λ で σ は残余を固定）。 -/
theorem q9rf_resM_sigma (x : q3kCar) : q9rfResM (q3kSigma x) = q9rfResM x := by
  have hL : q9rfResM (q3kSigma x)
      = q9rfF3.add (q9rfResL x.1) (q9rfF3.add (q9rfResL x.2.1) (q9rfResL x.2.2)) := by
    show q9rfResL (q3rqAdd x.1
        (q3rqAdd (q3rqMul q3rqZeta x.2.1) (q3rqMul q3rqZetaSq x.2.2))) = _
    rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_mul, q9rf_resL_mul,
        q9rf_resL_zeta, q9rf_resL_zetaSq, q9rfF3.one_mul, q9rfF3.one_mul]
  have hR : q9rfResM x
      = q9rfF3.add (q9rfResL x.1) (q9rfF3.add (q9rfResL x.2.1) (q9rfResL x.2.2)) := by
    show q9rfResL (q3rqAdd x.1 (q3rqAdd x.2.1 x.2.2)) = _
    rw [q9rf_resL_add, q9rf_resL_add]
  rw [hL, hR]

/-- **q9rf-6b: res_M(σ²x) = res_M(x)**。 -/
theorem q9rf_resM_sigma2 (x : q3kCar) : q9rfResM (q3kSigma2 x) = q9rfResM x := by
  have hL : q9rfResM (q3kSigma2 x)
      = q9rfF3.add (q9rfResL x.1) (q9rfF3.add (q9rfResL x.2.1) (q9rfResL x.2.2)) := by
    show q9rfResL (q3rqAdd x.1
        (q3rqAdd (q3rqMul q3rqZetaSq x.2.1) (q3rqMul q3rqZeta x.2.2))) = _
    rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_mul, q9rf_resL_mul,
        q9rf_resL_zetaSq, q9rf_resL_zeta, q9rfF3.one_mul, q9rfF3.one_mul]
  have hR : q9rfResM x
      = q9rfF3.add (q9rfResL x.1) (q9rfF3.add (q9rfResL x.2.1) (q9rfResL x.2.2)) := by
    show q9rfResL (q3rqAdd x.1 (q3rqAdd x.2.1 x.2.2)) = _
    rw [q9rf_resL_add, q9rf_resL_add]
  rw [hL, hR]

/-- **q9rf-6c（★ res∘N = res）: resL(N(x)) = res_M(x)** — N(x) ≡ x³ ≡ x mod π₉
    （Fermat a³=a on 𝔽₃・res_M σ 不変性経由）。 -/
theorem q9rf_res_norm (x : q3kCar) : q9rfResL (q3kNormBase x) = q9rfResM x := by
  have h1 : q9rfResL (q3kNormBase x) = q9rfResM (q3kEmbed (q3kNormBase x)) :=
    (q9rf_resM_embed (q3kNormBase x)).symm
  rw [h1, ← q3k_norm_eq x, q9rf_resM_mul, q9rf_resM_mul,
      q9rf_resM_sigma, q9rf_resM_sigma2]
  exact q9rf_f3_cube (q9rfResM x)

/-! ## q9rf-7: 核完全性 ker res = (π₉)（★） -/

/-- embed は加法を保つ。 -/
theorem q9rf_embed_add (p q : q3rqCar) :
    q3kEmbed (q3rqAdd p q) = q3kAdd (q3kEmbed p) (q3kEmbed q) := by
  apply q3k_ext
  · rfl
  · show q3rqZero = q3rqAdd q3rqZero q3rqZero
    rw [q3k_A_eq, q3k_Z_eq, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqZero = q3rqAdd q3rqZero q3rqZero
    rw [q3k_A_eq, q3k_Z_eq, q3rqRing.add_zero q3rqRing.zero]

/-- π₉ ∣ y ⟹ π₉ ∣ x·y（右因子の可除性）。 -/
theorem q9rf_dvd_mul_left {d b : q3kCar} (h : q9wrDvd d b) (a : q3kCar) :
    q9wrDvd d (q3kMul a b) := by
  rw [q3k_mul_comm a b]
  exact q9nf_dvd_mul_right h a

/-- π₉ ∣ embed(3)（3 = π₉⁶·u₆ ∈ (π₉)）。 -/
theorem q9rf_pi9_dvd_three : q9wrDvd q9psPi9 (q3kEmbed q3rqThreeElt) := by
  have h6 : q9wrDvd (q9nfPiPow 6) (q3kEmbed q3rqThreeElt) := by
    have hw : q9wrDvd (q9nfPiPow 6)
        (q3kAdd (q3kAdd q3kOne (q3kEmbed q3rqThreeElt)) (q3kNeg q3kOne)) :=
      q9nf_retarget_witness
    rw [q9nf_one_add_cancel] at hw
    exact hw
  have hd := q9nf_dvd_of_le (m := 1) (n := 6) (by omega) h6
  rw [q9nf_pipow1_eq] at hd
  exact hd

/-- π₉ ∣ embed(λ)（λ = π₉³·w⁻¹ ∈ (π₉)）。 -/
theorem q9rf_pi9_dvd_lambda : q9wrDvd q9psPi9 (q3kEmbed q3rqLambda) := by
  refine ⟨q3kMul (q9nfPiPow 2) q9psWinv, ?_⟩
  rw [q9nf_embed_lambda, q3k_kM_eq]
  exact q3kRing.mul_assoc q9psPi9 (q9nfPiPow 2) q9psWinv

/-- **q9rf-7a: 座標分解** x = embed(S) + π₉·R（S = x₀+x₁+x₂・R = (x₁+x₂, x₂, 0)）。 -/
theorem q9rf_decomp (x : q3kCar) :
    x = q3kAdd (q3kEmbed (q9rfSum x))
      (q3kMul q9psPi9 ((q3rqAdd x.2.1 x.2.2, x.2.2, q3rqZero) : q3kCar)) := by
  rw [q9ps_pi9_coords]
  apply q3k_ext
  · show x.1 = q3rqAdd (q9rfSum x)
        (q3rqAdd (q3rqMul (q3rqNeg q3rqOne) (q3rqAdd x.2.1 x.2.2))
          (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqOne q3rqZero)
            (q3rqMul q3rqZero x.2.2))))
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q3k_Z_eq]
    rw [q3rqRing.one_mul q3rqRing.zero, q3rqRing.zero_mul x.2.2,
        q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero (q3rqRing.mul (q3rqRing.neg q3rqRing.one)
          (q3rqRing.add x.2.1 x.2.2)),
        q3rqRing.neg_mul q3rqRing.one (q3rqRing.add x.2.1 x.2.2),
        q3rqRing.one_mul (q3rqRing.add x.2.1 x.2.2)]
    show x.1 = q3rqRing.add (q3rqRing.add x.1 (q3rqRing.add x.2.1 x.2.2))
        (q3rqRing.neg (q3rqRing.add x.2.1 x.2.2))
    rw [q3rqRing.add_assoc x.1 (q3rqRing.add x.2.1 x.2.2)
          (q3rqRing.neg (q3rqRing.add x.2.1 x.2.2)),
        q3rqRing.add_neg (q3rqRing.add x.2.1 x.2.2),
        q3rqRing.add_zero x.1]
  · show x.2.1 = q3rqAdd q3rqZero
        (q3rqAdd (q3rqAdd (q3rqMul (q3rqNeg q3rqOne) x.2.2)
            (q3rqMul q3rqOne (q3rqAdd x.2.1 x.2.2)))
          (q3rqMul q3rqZeta (q3rqMul q3rqZero q3rqZero)))
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q3k_Z_eq]
    rw [q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero (q3rqRing.add (q3rqRing.mul (q3rqRing.neg q3rqRing.one) x.2.2)
          (q3rqRing.mul q3rqRing.one (q3rqRing.add x.2.1 x.2.2))),
        q3rqRing.zero_add (q3rqRing.add (q3rqRing.mul (q3rqRing.neg q3rqRing.one) x.2.2)
          (q3rqRing.mul q3rqRing.one (q3rqRing.add x.2.1 x.2.2))),
        q3rqRing.one_mul (q3rqRing.add x.2.1 x.2.2),
        q3rqRing.neg_mul q3rqRing.one x.2.2, q3rqRing.one_mul x.2.2]
    show x.2.1 = q3rqRing.add (q3rqRing.neg x.2.2) (q3rqRing.add x.2.1 x.2.2)
    rw [q3rqRing.add_comm x.2.1 x.2.2,
        ← q3rqRing.add_assoc (q3rqRing.neg x.2.2) x.2.2 x.2.1,
        q3rqRing.neg_add x.2.2, q3rqRing.zero_add x.2.1]
  · show x.2.2 = q3rqAdd q3rqZero
        (q3rqAdd (q3rqAdd (q3rqMul (q3rqNeg q3rqOne) q3rqZero)
            (q3rqMul q3rqOne x.2.2)) (q3rqMul q3rqZero (q3rqAdd x.2.1 x.2.2)))
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q3k_Z_eq]
    rw [q3rqRing.mul_zero (q3rqRing.neg q3rqRing.one),
        q3rqRing.zero_mul (q3rqRing.add x.2.1 x.2.2),
        q3rqRing.add_zero (q3rqRing.add q3rqRing.zero (q3rqRing.mul q3rqRing.one x.2.2)),
        q3rqRing.zero_add (q3rqRing.add q3rqRing.zero (q3rqRing.mul q3rqRing.one x.2.2)),
        q3rqRing.zero_add (q3rqRing.mul q3rqRing.one x.2.2),
        q3rqRing.one_mul x.2.2]

/-- **q9rf-7b（★ 核完全性 ker res = (π₉)）: res_M(x) = 0 ⟹ π₉ ∣ x**。 -/
theorem q9rf_kernel (x : q3kCar) (h : q9rfResM x = q9rfF3.zero) :
    q9wrDvd q9psPi9 x := by
  obtain ⟨k, hk⟩ := q9rf_div3 (q9rfSum x).1 h
  have hS : q9rfSum x
      = q3rqAdd (((q9rfSum x).1, z3.zero) : q3rqCar)
          ((z3.zero, (q9rfSum x).2) : q3rqCar) :=
    q3rq_ext
      (by show (q9rfSum x).1 = z3.add (q9rfSum x).1 z3.zero; rw [z3.add_zero])
      (by show (q9rfSum x).2 = z3.add z3.zero (q9rfSum x).2; rw [z3.zero_add])
  rw [hk] at hS
  have hemb : q9wrDvd q9psPi9 (q3kEmbed (q9rfSum x)) := by
    rw [hS, q9rf_embed_add]
    refine q9nf_dvd_add ?_ ?_
    · have h30 : ((z3.mul q3rqThree k, z3.zero) : q3rqCar)
          = q3rqMul q3rqThreeElt ((k, z3.zero) : q3rqCar) :=
        (q3rq_pair_mul q3rqThree k).symm
      rw [h30, ← q3k_embed_mul]
      exact q9nf_dvd_mul_right q9rf_pi9_dvd_three (q3kEmbed ((k, z3.zero) : q3rqCar))
    · have h0s : ((z3.zero, (q9rfSum x).2) : q3rqCar)
          = q3rqMul (((q9rfSum x).2, z3.zero) : q3rqCar) q3rqLambda := by
        apply q3rq_ext
        · show z3.zero = z3.add (z3.mul (q9rfSum x).2 z3.zero)
              (z3.mul q3rqD (z3.mul z3.zero z3.one))
          rw [z3.mul_zero (q9rfSum x).2, z3.zero_mul z3.one, z3.mul_zero q3rqD,
              z3.add_zero z3.zero]
        · show (q9rfSum x).2 = z3.add (z3.mul (q9rfSum x).2 z3.one)
              (z3.mul z3.zero z3.zero)
          rw [z3.mul_one (q9rfSum x).2, z3.mul_zero z3.zero,
              z3.add_zero (q9rfSum x).2]
      rw [h0s, ← q3k_embed_mul]
      exact q9rf_dvd_mul_left q9rf_pi9_dvd_lambda
        (q3kEmbed (((q9rfSum x).2, z3.zero) : q3rqCar))
  rw [q9rf_decomp x]
  exact q9nf_dvd_add hemb
    ⟨((q3rqAdd x.2.1 x.2.2, x.2.2, q3rqZero) : q3kCar), rfl⟩

/-! ## q9rf-8: O_M は局所（¬単数 ⟹ π₉ ∣ x）（★） -/

/-- res(m.1) ≠ 0（3∤a₁）⟹ N(m) = a₁²+3b₁² は単数（a₁² ≢ 0 mod 3）。 -/
theorem q9rf_norm_not_dvd (a b : Int) (h : a % 3 ≠ 0) :
    ¬ ((3 : Int) ∣ (a * a + (-((-3) * (b * b))))) := by
  have htri : a % 3 = 1 ∨ a % 3 = 2 := by omega
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  rw [Int.neg_mul, Int.neg_neg] at hc
  have hd1 : (3 : Int) ∣ (a * a + 3 * (b * b)) := ⟨c, hc⟩
  have hd2 : (3 : Int) ∣ (3 * (b * b)) := ⟨b * b, rfl⟩
  have hsub := Int.dvd_sub hd1 hd2
  rw [Int.add_sub_cancel] at hsub
  obtain ⟨d, hd⟩ := hsub
  have hmod : (a * a) % 3 = ((a % 3) * (a % 3)) % 3 := Int.mul_emod a a 3
  rw [hd] at hmod
  rw [Int.mul_emod_right] at hmod
  clear hc hd1 hd2 hd
  obtain hr | hr := htri
  · rw [hr, show (1 * 1 : Int) % 3 = 1 from rfl] at hmod
    exact absurd hmod Int.zero_ne_one
  · rw [hr, show (2 * 2 : Int) % 3 = 1 from rfl] at hmod
    exact absurd hmod Int.zero_ne_one

/-- **q9rf-8a（★ O_M は局所）: ¬ q3kUnitMem x ⟹ π₉ ∣ x**
    （res_M(x) ≠ 0 なら x は単数——その対偶。res(N x).1 ≠ 0 ⟹ N(x) 単数）。 -/
theorem q9rf_local (x : q3kCar) (h : ¬ q3kUnitMem x) : q9wrDvd q9psPi9 x := by
  apply q9rf_kernel
  rw [← q9rf_res_norm]
  obtain ⟨a, ha⟩ : ∃ a : Int, Quot.mk (modCong (3 ^ 1)).rel a = (q3kNormBase x).1.val 1 :=
    Quot.exists_rep _
  obtain h0 | h0 :=
    (if hh : a % 3 = 0 then Or.inl hh else Or.inr hh : a % 3 = 0 ∨ a % 3 ≠ 0)
  · show (q3kNormBase x).1.val 1 = q9rfF3.zero
    rw [← ha]
    apply Quot.sound
    show ((3 ^ 1 : Nat) : Int) ∣ a - 0
    rw [Nat.pow_one, Int.sub_zero]
    exact Int.dvd_of_emod_eq_zero h0
  · exfalso
    apply h
    obtain ⟨b, hb⟩ : ∃ b : Int, Quot.mk (modCong (3 ^ 1)).rel b = (q3kNormBase x).2.val 1 :=
      Quot.exists_rep _
    show IsZpUnit 3 (q3rqNorm (q3kNormBase x))
    apply z3v_unit_of_lev1 3 (q3rqNorm (q3kNormBase x))
    intro hge
    have hge' : (q3rqNorm (q3kNormBase x)).val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := hge
    have hnorm : (q3rqNorm (q3kNormBase x)).val 1
        = Quot.mk (modCong (3 ^ 1)).rel (a * a + (-((-3) * (b * b)))) :=
      q3mc_norm_lev1 (q3kNormBase x).1 (q3kNormBase x).2 a b ha.symm hb.symm
    have heq : Quot.mk (modCong (3 ^ 1)).rel (a * a + (-((-3) * (b * b))))
        = Quot.mk (modCong (3 ^ 1)).rel 0 := hnorm.symm.trans hge'
    obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (3 ^ 1)) heq
    rw [Nat.pow_one] at hk
    exact q9rf_norm_not_dvd a b h0 ⟨k, by omega⟩

/-! ## q9rf-9: capstone -/

/-- **q9rf-9a: 実残余体データ** — 環準同型 res_M : O_M ↠ 𝔽₃・核完全性・局所性を束ねる。 -/
structure Q3ResidueFieldRealData where
  /-- res_M は加法を保つ（環準同型・加法）。 -/
  resM_add : ∀ x y, q9rfResM (q3kAdd x y) = q9rfF3.add (q9rfResM x) (q9rfResM y)
  /-- res_M は乗法を保つ（環準同型・乗法）。 -/
  resM_mul : ∀ x y, q9rfResM (q3kMul x y) = q9rfF3.mul (q9rfResM x) (q9rfResM y)
  /-- res∘N = res_M（Fermat a³=a on 𝔽₃）。 -/
  res_norm : ∀ x, q9rfResL (q3kNormBase x) = q9rfResM x
  /-- 核完全性: res_M(x) = 0 ⟹ π₉ ∣ x（ker res = (π₉)）。 -/
  kernel : ∀ x, q9rfResM x = q9rfF3.zero → q9wrDvd q9psPi9 x
  /-- O_M は局所: ¬単数 ⟹ π₉ ∣ x。 -/
  local_ring : ∀ x, ¬ q3kUnitMem x → q9wrDvd q9psPi9 x

/-- **q9rf-9b: 見出し実例** — 実 O_M = q3kRing の残余体 𝔽₃ と局所性。 -/
def q9rf_data : Q3ResidueFieldRealData where
  resM_add := q9rf_resM_add
  resM_mul := q9rf_resM_mul
  res_norm := q9rf_res_norm
  kernel := q9rf_kernel
  local_ring := q9rf_local

/-- **q9rf-9c: 実残余体 𝔽₃ と O_M の局所性の存在**（B2 crux 4∉N への足場）。 -/
theorem q9rf_exists : Nonempty Q3ResidueFieldRealData := ⟨q9rf_data⟩

end IUT
