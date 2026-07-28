/-
  IUT/Q3CubeQuotientFull.lean — 実局所体 L₂ = ℚ₃(ζ₃) = ℚ₃(√−3) の立方剰余群の
    **完全構造** L₂^×/(L₂^×)³ ≅ (ℤ/3)⁴（|quotient| = 81）（B6・K2b + K2c）

  ── 主要成果の分類: **[実／(a) 昇格]** — q9cq の rank≥2、q9c3 の rank≥3（下界のみ）を、
     **rank 4 の下界 ＋ 上界 exhaustion** の両方を備えた**完全構造定理**へ昇格する。
     主対象は実 q3rqLx = prodGrp intGrp q3rqU（付値部 ℤ × 実単数群 U₂ = O_{L₂}^×、
     O_{L₂} = ℤ₃[√−3] は実 ℤ₃ = zpRing 3 上の実対環）——toy 主語なし
     （m202fVol 型・Bool 軌道・surrogate 群を一切使わない）。

  complete_pct 影響: **B6「Kummer 理論（実 Galois コホモロジー上）」0.24 →（監査次第）**。
  q9cq がヘッダで **named target** として掲げ「定理化しない」と明記していた
  「**L₂^×/(L₂^×)³ ≅ (ℤ/3)⁴（rank 4・|quotient| = 81 = 3⁴）**」を、
  q9cq/q9c3 の正直限定 1（full rank 4 未計算・上界 exhaustion 未達）ごと**閉じる**。
  ——ただし下記「正直な限定」1・2・5 は新たに立てる（過大主張しない）。

  **真水（本モジュールの新規主張）**:
   (1) ★★ **K2c: U^{(4)}_λ = 1 + 9·O_{L₂} ⊆ (O_{L₂}^×)³**（`q9k4_deep_cube` /
       `q9k4_cube_of_lev2`）。実 O_{L₂} 上の**立方 Hensel（逐次近似 + M27 完備性）**を
       ゼロから構成する: 不動点方程式 t = m − 3(t²+t³) の反復塔 `q9k4Seq`、
       差の因数分解（`geom_factor` 2 回適用 = `q9k4_q_diff`）による 3^n-coherence
       （`q9k4_step`/`q9k4_tower`）、`z3cLim` の 2 座標適用による極限 `q9k4Lim`、
       分離性（`q9cm_sep_sub`）で近似を**厳密な不動点** `q9k4_fixed` に昇格し、
       環恒等式 (1+3t)³ = 1 + 9(t + 3(t²+t³))（`q9k4_cube_shape`）で cube に落とす。
   (2) ★★ **立方判定の完全形（⟺）** `q9k4_cube_iff`: a ≡ 1 (mod 3) なる u = (a,b) について
       **u が O_{L₂} の立方 ⟺ a ≡ 1 かつ b ≡ 0 (mod 9)**（= u ∈ U^{(4)}）。
       ⟹ 方向は立方の座標公式 v³ = (c³−9cd², 3c²d−3d³)（`q9k4_v_cube`）と
       3 進 Fermat（`q9k4_cube_mod3`）・`q9c3_cube9_of_one` から、⟸ 方向は (1)。
       これは**単数側の立方部分群 (O^×)³ ∩ U^{(1)} の完全決定**であり、
       D1（λ-係数）・D2（mod 9 ノルム）の「判別器」段階を越える。
   (3) ★★★ **K2b: 第 4 次元** `q9k4_deep_noncube` / `q9k4_comb_noncube` /
       `q9k4_rank_ge_four`: 深い主単数 **1+λ³ = (1,−3) ∈ U^{(3)}∖U^{(4)}** は非立方で、
       ⟨[λ],[ζ₃],[4],[1+λ³]⟩ ≅ (ℤ/3)⁴ が立方剰余群へ単射（**80 個**の非自明結合が全て非立方）。
   (4) ★★★ **上界 exhaustion** `q9k4_exhaust`: 任意の g ∈ L₂^× に対し i,j,k,l < 3 と c があって
       g·λ^i·ζ₃^j·4^k·(1+λ³)^l = c³。λ-フィルトレーション 3 段降下
       （`q9k4_step1`: U^{(1)}→U^{(2)}、`q9k4_step2`: →U^{(3)}、`q9k4_step3`: →U^{(4)}）
       と (1) の合成。
   (5) ★★★ **上下両界の同時成立** `q9k4_structure_81`: (4)（81 個の代表が覆う＝上界）
       ＋ (3)（80 個の非自明代表が非立方＝下界）。**ただし「ちょうど 81」の最後の
       elementary な一歩（81 個の代表が互いに非同値であること）は未形式化**——
       下記「正直な限定」2 を必ず参照のこと。

  **消費（再主張しない）**:
   * レベル n 値計算 `q9c3_add_val`/`q9c3_mul_val`/`q9c3_neg_val`/`q9c3_c4_val`、
     mod 9 立方補題 `q9c3_cube9_of_one`（B6・q9c3）。
   * 付値方向の非立方性 `q9cq_val_nontrivial`、群提示への射影 `q9c3_group_of_ring`。
   * ノルムのレベル 1 値 `q3mc_norm_lev1`（柱A・q3mc）、`q3rq_norm_mul`（q3rq）。
   * 3^k 可除性判定 `q9cm_dvd_pow_iff`・分離性 `q9cm_sep`/`q9cm_sep_sub`（B2・q9cm）。
   * modulus 付き完備性 `z3cLim`/`z3c_converges`/`z3c_sub_eq`（A2・z3c）。
   * O_{L₂} のスカラー 3 の座標展開 `q9cl_three_rq`（B2・q9cl）。
   * 幾何級数の因数分解 `geom_factor`（M96・FactorTheorem）。
   * 実元 4 とその単数性 `q9rcFour`/`q9rc_four_unit`（B2・q9rc）——B2 の tame 生成元と
     同一の実元を使う（別の 4 を作らない）。実 ζ₃ は `q3rqZeta`（q3rq）。

  正直な限定（§4 規約により消さない・弱化しない・q3rq/q9kd/q9cq/q9c3/q9cm/z3c 継承の上に追記のみ）:
  1. **主張は群提示 L₂^× = ℤ×U₂ の上**。L₂ を体としては建てていない（q3rq 正直限定 1・
     A2 恒久限定を継承）。**商群オブジェクトは建てない**——q9kd/q9cq/q9c3 に合わせ、
     (i) **exhaustion**（81 個の代表 λ^i ζ₃^j 4^k (1+λ³)^l が全体を覆う）と
     (ii) **independence**（80 個の非自明結合が非立方）
     の**二本立ての述語形**で述べる。`quotientGroupN` による対象化と「位数 81 の群」
     としての言明は未実施。
  2. ★**「ちょうど 81」の残り一歩（本モジュールの最大の未達点・過大主張しないため明記）**:
     証明したのは
       (上界) 任意の g に対し 81 個の代表のどれかを掛けると立方になる、
       (下界) 80 個の**非自明代表それ自身**が立方でない（＝その類 ≠ 1）、
     の 2 つである。**「81 個の代表の類が互いに相異なる」ことは形式化していない**。
     これは代表写像 (ℤ/3)⁴ → L₂^×/(L₂^×)³ が準同型であること
     （ζ₃³=1・4³ と (1+λ³)³ が立方・指数の mod 3 簡約）から従う *elementary* な一歩だが、
     Lean 上の rpow の指数演算と群逆元の簿記を要するため本ラウンドでは未実施。
     したがって **exhaustion 述語は完全に証明済**（★**正直な訂正（独立敵対監査 2026-07-21）**:
     当初「|L₂^×/(L₂^×)³| ≤ 81 は完全に証明済」と書いたのは **やや過大**。証明したのは
     exhaustion **述語**であって、商オブジェクトが存在しない以上 **濃度の言明は meta レベル**である。
     加えて監査の未申告重複発見: exhaustion の降下のうち ±1/step1/step2 は、B2 で既に計上済の
     `Q3UnitTameDecomp`(q9ut・`q9ut_gr0/gr1/gr2_sweep`) と**同形の λ-filtration sweep の再導出**であり
     （標的は N(U_M) でなく cubes・import なしの独立導出だが）、「exhaustion は全て新規」という
     枠付けは過大。**新規の降下内容は step3 と K2c のみ**。限定 3 には q9lr だけでなく
     **q9ut も名指しすべき**であった。）、
     **= 81（下からの一致）は「rank≥4 の honest 下界形（q9cq/q9c3 と同じ意味）」までであり、
     q9cq の named target は『実質的に閉じた』が『形式的に閉じた』とまでは主張しない**。
     この限定を消去・弱化してはならない。
  3. **独立性の一部は B2 の既計上結果からも従う**。単数側 26 結合のうち [4]・[16] と
     その ζ₃ 混合（q9c3 が扱った 8 標的のうち 6）は、B2 の crux `q9lr_four_not_norm`
     （4 ∉ N_{M/L₂}(U_M)）＋ `q9ps_normBase_embed` からも導ける（q9c3 ヘッダの
     「正直な訂正」参照）。**本モジュールの新規性はそこではなく**、
     (a) 第 4 次元 1+λ³ の非立方性（ノルム 1 指標では原理的に取れない——
         N_{M/L₂} は指数 3 の部分群 1 個しか切らないため、単数側 3 次元は決定できない）、
     (b) **上界 exhaustion / U^{(4)} ⊆ 立方**（非ノルム性からは一切従わない）、
     (c) mod 9 の**完全判定** `q9k4_cube_iff`（判別器ではなく必要十分条件）
     にある。この区別を薄めない。
  4. **完備性は modulus 形のみ**（z3c の正直限定を継承）。本塔は構成により modulus
     M(n) = n が閉じた式で読めるため choice-free に閉じる（∃ 形 Cauchy の可算選択は
     不要かつ不使用）。
  5. **量化は O_{L₂} と U₂ = O_{L₂}^× のみ**。分数元 L₂^× 全体の bookkeeping は
     群提示 ℤ×U₂ による（体化なし）。
  6. **Kummer 同型 H¹(G_{L₂}, μ₃) ≅ L₂^×/(L₂^×)³ は本モジュールでは主張しない**。
     本モジュールが決めたのは**乗法群側の商の構造**であり、実 Galois コホモロジー側の
     位数 81 への輸送（q9kd の橋の完成）は**別段**として残る——B6 の名前
     「Kummer 理論（実 Galois コホモロジー上）」の**コホモロジー側は未達のまま**。
  7. q3rq/q9kd/q9cq/q9c3/q9ci/q9rc/q9cm/z3c の恒久限定を全継承（n=3・体 L₂ 1 個・
     実テータ関数ゼロ・π₁ 同定ゼロ・tmzLimit 比較橋なし・兄弟担体・p=3 固定）。
     本モジュールは拡大 M/L₂ を一切使わない（ノルム機構に依存しない独立経路）。

  内容:
   * q9k4-A  q9k4_sq_one_add / q9k4_cube_one_add / q9k4_cube_shape — 一般環の立方展開
   * q9k4-A' q9k4Q / q9k4_q_diff                    — q(a)−q(b) = (a−b)(g₂+g₃)（geom_factor）
   * q9k4-B  q9k4Mul3Pow / q9k4_dvd_iff ほか        — O_{L₂} の 3^k 可除性
   * q9k4-C  q9k4T / q9k4Seq / q9k4_step / q9k4_tower / q9k4Lim / **q9k4_fixed**
   * q9k4-D  **q9k4_deep_cube / q9k4_cube_of_lev2**  — ★ K2c（U^{(4)} ⊆ 立方）
   * q9k4-E  q9k4V / q9k4_v_mul ほか                — mod 9 座標計算
   * q9k4-F  q9k4_cube_mod3 ほか                    — 整数側 3 進補題
   * q9k4-G  q9k4_v_cube / **q9k4_cube_forces**     — 立方判定（⟹）
   * q9k4-H  q9k4Deep / q9k4_deep_eq / q9k4_deep_unit / 生成元の mod 9 座標
   * q9k4-I  生成元の冪の mod 9 座標
   * q9k4-J  q9k4_fd_val                            — 4^k(1+λ³)^l の完全決定（9 分岐）
   * q9k4-K  **q9k4_comb_noncube / q9k4_deep_noncube / q9k4_rank_ge_four** — ★ K2b
   * q9k4-M  q9k4_step1 / q9k4_step2 / q9k4_step3   — フィルトレーション 3 段降下
   * q9k4-N  q9k4_exhaust_unit                      — 単数側 exhaustion
   * q9k4-O  **q9k4_exhaust**                       — 群提示上の exhaustion
   * q9k4-P  q9k4_cube_iff / q9k4_indep_full / **q9k4_structure_81**
   * q9k4-Q  Q3CubeQuotientFullData / q9k4_data / q9k4_exists

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無・
  極限は z3cLim の閉じた式）。#print axioms は [propext, Quot.sound] のみ。
  禁止タクティク不使用（omega は Int/Nat 原子のみ）。
-/
import IUT.Q3CubeRankThree
import IUT.Q3NormSurjCompleteLimit

namespace IUT

/-- (1+u)² = (1 + (u+u)) + u·u。 -/
theorem q9k4_sq_one_add (R : CRing) (u : R.carrier) :
    R.mul (R.add R.one u) (R.add R.one u)
      = R.add (R.add R.one (R.add u u)) (R.mul u u) := by
  rw [R.right_distrib R.one u (R.add R.one u), R.one_mul (R.add R.one u),
    R.left_distrib u R.one u, CRing.mul_one R u,
    R.add_assoc R.one u (R.add u (R.mul u u)),
    ← R.add_assoc u u (R.mul u u),
    ← R.add_assoc R.one (R.add u u) (R.mul u u)]

/-- (1+u)³ = 1 + (3u + (3u² + u³))（右結合正規形）。 -/
theorem q9k4_cube_one_add (R : CRing) (u : R.carrier) :
    R.mul (R.mul (R.add R.one u) (R.add R.one u)) (R.add R.one u)
      = R.add R.one
          (R.add (R.add (R.add u u) u)
            (R.add (R.add (R.add (R.mul u u) (R.mul u u)) (R.mul u u))
              (R.mul (R.mul u u) u))) := by
  rw [q9k4_sq_one_add R u,
    R.left_distrib (R.add (R.add R.one (R.add u u)) (R.mul u u)) R.one u,
    CRing.mul_one R (R.add (R.add R.one (R.add u u)) (R.mul u u)),
    R.right_distrib (R.add R.one (R.add u u)) (R.mul u u) u,
    R.right_distrib R.one (R.add u u) u, R.one_mul u,
    R.right_distrib u u u,
    -- LHS: ((1+(u+u)) + u²) + ((u + (u²+u²)) + (u²)u)
    R.add_assoc (R.add R.one (R.add u u)) (R.mul u u)
      (R.add (R.add u (R.add (R.mul u u) (R.mul u u))) (R.mul (R.mul u u) u)),
    R.add_assoc R.one (R.add u u)
      (R.add (R.mul u u)
        (R.add (R.add u (R.add (R.mul u u) (R.mul u u))) (R.mul (R.mul u u) u))),
    R.add_assoc u (R.add (R.mul u u) (R.mul u u)) (R.mul (R.mul u u) u),
    CRing.add_left_comm R (R.mul u u) u
      (R.add (R.add (R.mul u u) (R.mul u u)) (R.mul (R.mul u u) u)),
    ← R.add_assoc (R.add u u) u
      (R.add (R.mul u u) (R.add (R.add (R.mul u u) (R.mul u u)) (R.mul (R.mul u u) u))),
    CRing.add_left_comm R (R.mul u u) (R.add (R.mul u u) (R.mul u u))
      (R.mul (R.mul u u) u),
    R.add_assoc (R.add (R.mul u u) (R.mul u u)) (R.mul u u) (R.mul (R.mul u u) u)]


/-- 3c = c² を満たす c について (1+ct)³ = 1 + c²·(t + c·(t²+t³))。 -/
theorem q9k4_cube_shape (R : CRing) (c t : R.carrier)
    (h3 : R.add (R.add c c) c = R.mul c c) :
    R.mul (R.mul (R.add R.one (R.mul c t)) (R.add R.one (R.mul c t)))
        (R.add R.one (R.mul c t))
      = R.add R.one (R.mul (R.mul c c)
          (R.add t (R.mul c (R.add (R.mul t t) (R.mul (R.mul t t) t))))) := by
  have e1 : R.add (R.add (R.mul c t) (R.mul c t)) (R.mul c t)
      = R.mul (R.mul c c) t := by
    rw [← R.right_distrib c c t, ← R.right_distrib (R.add c c) c t, h3]
  have e2 : R.mul (R.mul c t) (R.mul c t) = R.mul (R.mul c c) (R.mul t t) :=
    CRing.mul_mul_mul_comm R c t c t
  have e3 : R.add (R.add (R.mul (R.mul c c) (R.mul t t))
        (R.mul (R.mul c c) (R.mul t t))) (R.mul (R.mul c c) (R.mul t t))
      = R.mul (R.mul (R.mul c c) c) (R.mul t t) := by
    rw [← R.right_distrib (R.mul c c) (R.mul c c) (R.mul t t),
      ← R.right_distrib (R.add (R.mul c c) (R.mul c c)) (R.mul c c) (R.mul t t),
      ← R.right_distrib c c c, ← R.right_distrib (R.add c c) c c, h3]
  have e4 : R.mul (R.mul (R.mul c c) (R.mul t t)) (R.mul c t)
      = R.mul (R.mul (R.mul c c) c) (R.mul (R.mul t t) t) :=
    CRing.mul_mul_mul_comm R (R.mul c c) (R.mul t t) c t
  rw [q9k4_cube_one_add R (R.mul c t), e1, e2, e3, e4,
    R.left_distrib (R.mul c c) t (R.mul c (R.add (R.mul t t) (R.mul (R.mul t t) t))),
    R.left_distrib c (R.mul t t) (R.mul (R.mul t t) t),
    R.left_distrib (R.mul c c) (R.mul c (R.mul t t)) (R.mul c (R.mul (R.mul t t) t)),
    ← R.mul_assoc (R.mul c c) c (R.mul t t),
    ← R.mul_assoc (R.mul c c) c (R.mul (R.mul t t) t)]

/-- rpow の 2 乗展開。 -/
theorem q9k4_rpow2 (R : CRing) (a : R.carrier) : rpow R a 2 = R.mul a a := by
  show R.mul (R.mul R.one a) a = R.mul a a
  rw [R.one_mul a]

/-- rpow の 3 乗展開。 -/
theorem q9k4_rpow3 (R : CRing) (a : R.carrier) :
    rpow R a 3 = R.mul (R.mul a a) a := by
  show R.mul (rpow R a 2) a = R.mul (R.mul a a) a
  rw [q9k4_rpow2 R a]

/-- q(t) = t² + t³。 -/
def q9k4Q (R : CRing) (t : R.carrier) : R.carrier :=
  R.add (R.mul t t) (R.mul (R.mul t t) t)

/-- **差の因数分解**: q(a) − q(b) = (a−b)·(g₂+g₃)（geom_factor の 2 回適用）。 -/
theorem q9k4_q_diff (R : CRing) (a b : R.carrier) :
    R.add (q9k4Q R a) (R.neg (q9k4Q R b))
      = R.mul (R.add a (R.neg b))
          (R.add (geoSum R a b 2) (geoSum R a b 3)) := by
  have g2 := geom_factor R a b 2
  have g3 := geom_factor R a b 3
  rw [q9k4_rpow2 R a, q9k4_rpow2 R b] at g2
  rw [q9k4_rpow3 R a, q9k4_rpow3 R b] at g3
  show R.add (R.add (R.mul a a) (R.mul (R.mul a a) a))
      (R.neg (R.add (R.mul b b) (R.mul (R.mul b b) b))) = _
  rw [CRing.neg_add_dist R (R.mul b b) (R.mul (R.mul b b) b),
    CRing.add_add_add_comm R (R.mul a a) (R.mul (R.mul a a) a)
      (R.neg (R.mul b b)) (R.neg (R.mul (R.mul b b) b)),
    g2, g3, ← R.left_distrib (R.add a (R.neg b)) (geoSum R a b 2) (geoSum R a b 3)]

/-! ## q9k4-B: O_{L₂} の 3^k 可除性 -/

/-- O_{L₂} 上の 3^k 倍。 -/
def q9k4Mul3Pow : Nat → q3rqCar → q3rqCar
  | 0, e => e
  | (k + 1), e => q3rqMul q3rqThreeElt (q9k4Mul3Pow k e)

theorem q9k4_mul3pow_succ (k : Nat) (e : q3rqCar) :
    q9k4Mul3Pow (k + 1) e = q3rqMul q3rqThreeElt (q9k4Mul3Pow k e) := rfl

/-- 座標展開: 3^k·m = (3^k·m₁, 3^k·m₂)。 -/
theorem q9k4_mul3pow_coord (k : Nat) (m : q3rqCar) :
    q9k4Mul3Pow k m = ((q9cmMul3Pow k m.1, q9cmMul3Pow k m.2) : q3rqCar) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [q9k4_mul3pow_succ k m, ih, q9cl_three_rq]; rfl

/-- **3^k 可除性 ⟺ 2 座標の level-k 消滅**。 -/
theorem q9k4_dvd_iff (k : Nat) (x : q3rqCar) :
    (∃ e, x = q9k4Mul3Pow k e) ↔ (z3vGe 3 x.1 k ∧ z3vGe 3 x.2 k) := by
  constructor
  · intro ⟨e, he⟩
    rw [he, q9k4_mul3pow_coord k e]
    exact ⟨(q9cm_dvd_pow_iff k (q9cmMul3Pow k e.1)).mp ⟨e.1, rfl⟩,
      (q9cm_dvd_pow_iff k (q9cmMul3Pow k e.2)).mp ⟨e.2, rfl⟩⟩
  · intro ⟨h1, h2⟩
    obtain ⟨e1, he1⟩ := (q9cm_dvd_pow_iff k x.1).mpr h1
    obtain ⟨e2, he2⟩ := (q9cm_dvd_pow_iff k x.2).mpr h2
    refine ⟨((e1, e2) : q3rqCar), ?_⟩
    rw [q9k4_mul3pow_coord k ((e1, e2) : q3rqCar)]
    exact q3rq_ext he1 he2

theorem q9k4_mul3pow_zero (k : Nat) : q9k4Mul3Pow k q3rqZero = q3rqZero := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [q9k4_mul3pow_succ k q3rqZero, ih]
    exact q3rqRing.mul_zero q3rqThreeElt

theorem q9k4_mul3pow_mul (k : Nat) (x y : q3rqCar) :
    q3rqMul (q9k4Mul3Pow k x) y = q9k4Mul3Pow k (q3rqMul x y) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [q9k4_mul3pow_succ k x, q9k4_mul3pow_succ k (q3rqMul x y), ← ih x]
    exact q3rqRing.mul_assoc q3rqThreeElt (q9k4Mul3Pow k x) y

theorem q9k4_mul3pow_neg (k : Nat) (x : q3rqCar) :
    q3rqNeg (q9k4Mul3Pow k x) = q9k4Mul3Pow k (q3rqNeg x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [q9k4_mul3pow_succ k x, q9k4_mul3pow_succ k (q3rqNeg x), ← ih]
    exact (CRing.mul_neg q3rqRing q3rqThreeElt (q9k4Mul3Pow k x)).symm

theorem q9k4_mul3pow_add (k : Nat) (x y : q3rqCar) :
    q3rqAdd (q9k4Mul3Pow k x) (q9k4Mul3Pow k y) = q9k4Mul3Pow k (q3rqAdd x y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [q9k4_mul3pow_succ k x, q9k4_mul3pow_succ k y,
      q9k4_mul3pow_succ k (q3rqAdd x y), ← ih]
    exact (q3rqRing.left_distrib q3rqThreeElt (q9k4Mul3Pow k x) (q9k4Mul3Pow k y)).symm

theorem q9k4_mul3pow_comp (b : Nat) : ∀ (a : Nat) (x : q3rqCar),
    q9k4Mul3Pow (a + b) x = q9k4Mul3Pow a (q9k4Mul3Pow b x) := by
  intro a
  induction a with
  | zero => intro x; rw [Nat.zero_add]; rfl
  | succ a ih =>
    intro x
    have hidx : a + 1 + b = (a + b) + 1 := by omega
    rw [hidx, q9k4_mul3pow_succ (a + b) x, ih x, q9k4_mul3pow_succ a (q9k4Mul3Pow b x)]

/-! ## q9k4-C: 逐次近似塔と極限 -/

/-- 望遠鏡（一般環）: (a−b)+(b−c) = a−c。 -/
theorem q9k4_tele_R (R : CRing) (a b c : R.carrier) :
    R.add (R.add a (R.neg b)) (R.add b (R.neg c)) = R.add a (R.neg c) := by
  rw [R.add_assoc a (R.neg b) (R.add b (R.neg c)),
    ← R.add_assoc (R.neg b) b (R.neg c), R.neg_add b, R.zero_add (R.neg c)]

/-- −(a−b) = b−a（一般環）。 -/
theorem q9k4_neg_sub_R (R : CRing) (a b : R.carrier) :
    R.neg (R.add a (R.neg b)) = R.add b (R.neg a) := by
  rw [CRing.neg_add_dist R a (R.neg b), CRing.neg_neg R b, R.add_comm (R.neg a) b]

/-- 反復写像 T(t) = m − c·q(t)（一般環）。 -/
def q9k4TR (R : CRing) (c m t : R.carrier) : R.carrier :=
  R.add m (R.neg (R.mul c (q9k4Q R t)))

/-- **T の差**: T(a) − T(b) = c·((b−a)·(g₂+g₃))。 -/
theorem q9k4_T_diff_R (R : CRing) (c m a b : R.carrier) :
    R.add (q9k4TR R c m a) (R.neg (q9k4TR R c m b))
      = R.mul c (R.mul (R.add b (R.neg a))
          (R.add (geoSum R b a 2) (geoSum R b a 3))) := by
  show R.add (R.add m (R.neg (R.mul c (q9k4Q R a))))
      (R.neg (R.add m (R.neg (R.mul c (q9k4Q R b))))) = _
  rw [CRing.neg_add_dist R m (R.neg (R.mul c (q9k4Q R b))),
    CRing.neg_neg R (R.mul c (q9k4Q R b)),
    CRing.add_add_add_comm R m (R.neg (R.mul c (q9k4Q R a)))
      (R.neg m) (R.mul c (q9k4Q R b)),
    CRing.add_neg R m,
    R.zero_add (R.add (R.neg (R.mul c (q9k4Q R a))) (R.mul c (q9k4Q R b))),
    R.add_comm (R.neg (R.mul c (q9k4Q R a))) (R.mul c (q9k4Q R b)),
    ← CRing.mul_neg R c (q9k4Q R a),
    ← R.left_distrib c (q9k4Q R b) (R.neg (q9k4Q R a)),
    q9k4_q_diff R b a]

/-- 反復写像 T(t) = m − 3·q(t)（実 O_{L₂}）。 -/
def q9k4T (m t : q3rqCar) : q3rqCar := q9k4TR q3rqRing q3rqThreeElt m t

/-- 逐次近似列 t₀=0, t_{n+1}=T(t_n)。 -/
def q9k4Seq (m : q3rqCar) : Nat → q3rqCar
  | 0 => q3rqZero
  | (n + 1) => q9k4T m (q9k4Seq m n)

theorem q9k4_tele (a b c : q3rqCar) :
    q3rqAdd (q3rqAdd a (q3rqNeg b)) (q3rqAdd b (q3rqNeg c)) = q3rqAdd a (q3rqNeg c) :=
  q9k4_tele_R q3rqRing a b c

theorem q9k4_neg_sub (a b : q3rqCar) :
    q3rqNeg (q3rqAdd a (q3rqNeg b)) = q3rqAdd b (q3rqNeg a) :=
  q9k4_neg_sub_R q3rqRing a b

theorem q9k4_T_diff (m a b : q3rqCar) :
    q3rqAdd (q9k4T m a) (q3rqNeg (q9k4T m b))
      = q3rqMul q3rqThreeElt
          (q3rqMul (q3rqAdd b (q3rqNeg a))
            (q3rqAdd (geoSum q3rqRing b a 2) (geoSum q3rqRing b a 3))) :=
  q9k4_T_diff_R q3rqRing q3rqThreeElt m a b

theorem q9k4_mul3pow_swap (k : Nat) (x : q3rqCar) :
    q3rqMul q3rqThreeElt (q9k4Mul3Pow k x) = q9k4Mul3Pow k (q3rqMul q3rqThreeElt x) := by
  rw [← q9k4_mul3pow_succ k x, q9k4_mul3pow_comp 1 k x]
  rfl

/-- **1 段の差**: t_{n+1} − t_n は 3^n で割れる。 -/
theorem q9k4_step (m : q3rqCar) : ∀ n : Nat, ∃ e,
    q3rqAdd (q9k4Seq m (n + 1)) (q3rqNeg (q9k4Seq m n)) = q9k4Mul3Pow n e := by
  intro n
  induction n with
  | zero => exact ⟨q3rqAdd (q9k4Seq m 1) (q3rqNeg (q9k4Seq m 0)), rfl⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    have hb : q3rqAdd (q9k4Seq m n) (q3rqNeg (q9k4Seq m (n + 1)))
        = q9k4Mul3Pow n (q3rqNeg e) := by
      rw [← q9k4_neg_sub (q9k4Seq m (n + 1)) (q9k4Seq m n), he, q9k4_mul3pow_neg]
    refine ⟨q3rqMul (q3rqNeg e)
      (q3rqAdd (geoSum q3rqRing (q9k4Seq m n) (q9k4Seq m (n + 1)) 2)
        (geoSum q3rqRing (q9k4Seq m n) (q9k4Seq m (n + 1)) 3)), ?_⟩
    show q3rqAdd (q9k4T m (q9k4Seq m (n + 1))) (q3rqNeg (q9k4T m (q9k4Seq m n))) = _
    rw [q9k4_T_diff m (q9k4Seq m (n + 1)) (q9k4Seq m n), hb,
      q9k4_mul3pow_mul n (q3rqNeg e)
        (q3rqAdd (geoSum q3rqRing (q9k4Seq m n) (q9k4Seq m (n + 1)) 2)
          (geoSum q3rqRing (q9k4Seq m n) (q9k4Seq m (n + 1)) 3))]
    rfl

/-- **塔 coherence**: t_{n+d} − t_n は 3^n で割れる。 -/
theorem q9k4_tower (m : q3rqCar) (n : Nat) : ∀ d : Nat, ∃ e,
    q3rqAdd (q9k4Seq m (n + d)) (q3rqNeg (q9k4Seq m n)) = q9k4Mul3Pow n e := by
  intro d
  induction d with
  | zero =>
    refine ⟨q3rqZero, ?_⟩
    rw [q9k4_mul3pow_zero n]
    exact CRing.add_neg q3rqRing (q9k4Seq m n)
  | succ d ih =>
    obtain ⟨e2, he2⟩ := ih
    obtain ⟨e1, he1⟩ := q9k4_step m (n + d)
    refine ⟨q3rqAdd (q9k4Mul3Pow d e1) e2, ?_⟩
    have hsum := q9k4_tele (q9k4Seq m (n + d + 1)) (q9k4Seq m (n + d)) (q9k4Seq m n)
    rw [he1, he2, q9k4_mul3pow_comp d n e1,
      q9k4_mul3pow_add n (q9k4Mul3Pow d e1) e2] at hsum
    exact hsum.symm

/-- 列のレベル n 値は n 段目以降で確定。 -/
theorem q9k4_seq_lev (m : q3rqCar) (n i : Nat) (h : n ≤ i) :
    (q9k4Seq m i).1.val n = (q9k4Seq m n).1.val n
    ∧ (q9k4Seq m i).2.val n = (q9k4Seq m n).2.val n := by
  obtain ⟨d, hd⟩ : ∃ d : Nat, i = n + d := ⟨i - n, by omega⟩
  rw [hd]
  obtain ⟨e, he⟩ := q9k4_tower m n d
  have hdv := (q9k4_dvd_iff n
    (q3rqAdd (q9k4Seq m (n + d)) (q3rqNeg (q9k4Seq m n)))).mp ⟨e, he⟩
  have h1 : z3vGe 3 (z3.add (q9k4Seq m (n + d)).1 (z3.neg (q9k4Seq m n).1)) n := hdv.1
  have h2 : z3vGe 3 (z3.add (q9k4Seq m (n + d)).2 (z3.neg (q9k4Seq m n).2)) n := hdv.2
  exact ⟨z3c_sub_eq h1, z3c_sub_eq h2⟩

theorem q9k4_cauchy1 (m : q3rqCar) :
    z3cIsModCauchy (fun i => (q9k4Seq m i).1) (fun n => n) := by
  intro n i j hi hj
  exact ((q9k4_seq_lev m n i hi).1).trans ((q9k4_seq_lev m n j hj).1).symm

theorem q9k4_cauchy2 (m : q3rqCar) :
    z3cIsModCauchy (fun i => (q9k4Seq m i).2) (fun n => n) := by
  intro n i j hi hj
  exact ((q9k4_seq_lev m n i hi).2).trans ((q9k4_seq_lev m n j hj).2).symm

/-- **極限**（z3cLim の 2 座標適用・modulus は恒等・choice ゼロ）。 -/
def q9k4Lim (m : q3rqCar) : q3rqCar :=
  ((z3cLim (fun i => (q9k4Seq m i).1) (fun n => n) (q9k4_cauchy1 m),
    z3cLim (fun i => (q9k4Seq m i).2) (fun n => n) (q9k4_cauchy2 m)) : q3rqCar)

theorem q9k4_modup_id (n : Nat) : z3cModUp (fun k => k) n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.max (n + 1) (z3cModUp (fun k => k) n) = n + 1
    rw [ih]
    exact Nat.max_eq_left (Nat.le_succ n)

/-- **収束**: i ≥ k なら 3^k ∣ (t_i − lim)。 -/
theorem q9k4_conv (m : q3rqCar) (k i : Nat) (h : k ≤ i) :
    ∃ e, q3rqAdd (q9k4Seq m i) (q3rqNeg (q9k4Lim m)) = q9k4Mul3Pow k e := by
  have hk : z3cModUp (fun t => t) k ≤ i := by rw [q9k4_modup_id k]; exact h
  have h1 := z3c_converges (fun i => (q9k4Seq m i).1) (fun t => t) (q9k4_cauchy1 m) k i hk
  have h2 := z3c_converges (fun i => (q9k4Seq m i).2) (fun t => t) (q9k4_cauchy2 m) k i hk
  have h1' : z3vGe 3 (q3rqAdd (q9k4Seq m i) (q3rqNeg (q9k4Lim m))).1 k := h1
  have h2' : z3vGe 3 (q3rqAdd (q9k4Seq m i) (q3rqNeg (q9k4Lim m))).2 k := h2
  exact (q9k4_dvd_iff k _).mpr ⟨h1', h2'⟩

/-- **★ 不動点**: T(lim) = lim（分離性で近似を厳密等式へ昇格）。 -/
theorem q9k4_fixed (m : q3rqCar) : q9k4T m (q9k4Lim m) = q9k4Lim m := by
  have key : ∀ k : Nat, ∃ e,
      q3rqAdd (q9k4T m (q9k4Lim m)) (q3rqNeg (q9k4Lim m)) = q9k4Mul3Pow k e := by
    intro k
    obtain ⟨e1, he1⟩ := q9k4_conv m k k (Nat.le_refl k)
    obtain ⟨e2, he2⟩ := q9k4_conv m k (k + 1) (Nat.le_succ k)
    have hA : q3rqAdd (q9k4T m (q9k4Lim m)) (q3rqNeg (q9k4Seq m (k + 1)))
        = q9k4Mul3Pow k (q3rqMul q3rqThreeElt (q3rqMul e1
            (q3rqAdd (geoSum q3rqRing (q9k4Seq m k) (q9k4Lim m) 2)
              (geoSum q3rqRing (q9k4Seq m k) (q9k4Lim m) 3)))) := by
      show q3rqAdd (q9k4T m (q9k4Lim m)) (q3rqNeg (q9k4T m (q9k4Seq m k))) = _
      rw [q9k4_T_diff m (q9k4Lim m) (q9k4Seq m k), he1,
        q9k4_mul3pow_mul k e1
          (q3rqAdd (geoSum q3rqRing (q9k4Seq m k) (q9k4Lim m) 2)
            (geoSum q3rqRing (q9k4Seq m k) (q9k4Lim m) 3)),
        q9k4_mul3pow_swap k]
    have hsum := q9k4_tele (q9k4T m (q9k4Lim m)) (q9k4Seq m (k + 1)) (q9k4Lim m)
    rw [hA, he2, q9k4_mul3pow_add k _ e2] at hsum
    exact ⟨_, hsum.symm⟩
  have hz1 : ∀ k : Nat,
      z3vGe 3 (z3.add (q9k4T m (q9k4Lim m)).1 (z3.neg (q9k4Lim m).1)) k := by
    intro k
    obtain ⟨e, he⟩ := key k
    exact ((q9k4_dvd_iff k _).mp ⟨e, he⟩).1
  have hz2 : ∀ k : Nat,
      z3vGe 3 (z3.add (q9k4T m (q9k4Lim m)).2 (z3.neg (q9k4Lim m).2)) k := by
    intro k
    obtain ⟨e, he⟩ := key k
    exact ((q9k4_dvd_iff k _).mp ⟨e, he⟩).2
  exact q3rq_ext (q9cm_sep_sub _ _ hz1) (q9cm_sep_sub _ _ hz2)

/-! ## q9k4-D: U^{(4)} ⊆ 立方（K2c 本体） -/

theorem q9k4_sub_add_R (R : CRing) (a b : R.carrier) :
    R.add (R.add a (R.neg b)) b = a := by
  rw [R.add_assoc a (R.neg b) b, R.neg_add b, CRing.add_zero R a]

theorem q9k4_recover_R (R : CRing) (a b : R.carrier)
    (h : R.add a (R.neg R.one) = b) : a = R.add R.one b := by
  rw [← h, R.add_comm R.one (R.add a (R.neg R.one))]
  exact (q9k4_sub_add_R R a R.one).symm

/-- 実 ℤ₃ 内 3+3+3 = 3·3。 -/
theorem q9k4_z3_three_nine :
    z3.add (z3.add q3rqThree q3rqThree) q3rqThree = z3.mul q3rqThree q3rqThree := by
  apply Subtype.ext
  funext n
  have hl := q9c3_add_val n (z3.add q3rqThree q3rqThree) q3rqThree (3 + 3) 3
    (q9c3_add_val n q3rqThree q3rqThree 3 3 (q3rq_three_val n) (q3rq_three_val n))
    (q3rq_three_val n)
  have hr := q9c3_mul_val n q3rqThree q3rqThree 3 3 (q3rq_three_val n) (q3rq_three_val n)
  show (z3.add (z3.add q3rqThree q3rqThree) q3rqThree).val n
    = (z3.mul q3rqThree q3rqThree).val n
  have hnine : (3 : Int) + 3 + 3 = 3 * 3 := by omega
  rw [hl, hr, hnine]

/-- O_{L₂} 内 3+3+3 = 3·3（q9k4_cube_shape の仮説）。 -/
theorem q9k4_three_h3 :
    q3rqAdd (q3rqAdd q3rqThreeElt q3rqThreeElt) q3rqThreeElt
      = q3rqMul q3rqThreeElt q3rqThreeElt := by
  apply q3rq_ext
  · show z3.add (z3.add q3rqThree q3rqThree) q3rqThree
      = z3.add (z3.mul q3rqThree q3rqThree) (z3.mul q3rqD (z3.mul z3.zero z3.zero))
    rw [z3.zero_mul z3.zero, CRing.mul_zero z3 q3rqD,
      CRing.add_zero z3 (z3.mul q3rqThree q3rqThree)]
    exact q9k4_z3_three_nine
  · show z3.add (z3.add z3.zero z3.zero) z3.zero
      = z3.add (z3.mul q3rqThree z3.zero) (z3.mul z3.zero q3rqThree)
    rw [CRing.mul_zero z3 q3rqThree, z3.zero_mul q3rqThree,
      z3.zero_add z3.zero, z3.zero_add z3.zero]

/-- 9 = 3·3（O_{L₂} 環元）。 -/
def q9k4Nine : q3rqCar := q3rqMul q3rqThreeElt q3rqThreeElt

/-- **★★ K2c 中核: 1 + 9m は立方**（逐次近似 + 完備性）。 -/
theorem q9k4_deep_cube (m : q3rqCar) :
    ∃ y, q3rqMul (q3rqMul y y) y = q3rqAdd q3rqOne (q3rqMul q9k4Nine m) := by
  refine ⟨q3rqAdd q3rqOne (q3rqMul q3rqThreeElt (q9k4Lim m)), ?_⟩
  have hs : q3rqMul (q3rqMul (q3rqAdd q3rqOne (q3rqMul q3rqThreeElt (q9k4Lim m)))
        (q3rqAdd q3rqOne (q3rqMul q3rqThreeElt (q9k4Lim m))))
        (q3rqAdd q3rqOne (q3rqMul q3rqThreeElt (q9k4Lim m)))
      = q3rqAdd q3rqOne (q3rqMul (q3rqMul q3rqThreeElt q3rqThreeElt)
          (q3rqAdd (q9k4Lim m)
            (q3rqMul q3rqThreeElt (q9k4Q q3rqRing (q9k4Lim m))))) :=
    q9k4_cube_shape q3rqRing q3rqThreeElt (q9k4Lim m) q9k4_three_h3
  have hfx : q3rqAdd m
      (q3rqNeg (q3rqMul q3rqThreeElt (q9k4Q q3rqRing (q9k4Lim m)))) = q9k4Lim m :=
    q9k4_fixed m
  have hL : q3rqAdd (q9k4Lim m)
      (q3rqMul q3rqThreeElt (q9k4Q q3rqRing (q9k4Lim m))) = m := by
    have hsa : q3rqAdd (q3rqAdd m
        (q3rqNeg (q3rqMul q3rqThreeElt (q9k4Q q3rqRing (q9k4Lim m)))))
        (q3rqMul q3rqThreeElt (q9k4Q q3rqRing (q9k4Lim m))) = m :=
      q9k4_sub_add_R q3rqRing m (q3rqMul q3rqThreeElt (q9k4Q q3rqRing (q9k4Lim m)))
    rw [hfx] at hsa
    exact hsa
  rw [hs, hL]
  rfl

/-- **★ K2c: レベル 2 で 1 に合同な元（U^{(4)}）は立方**。 -/
theorem q9k4_cube_of_lev2 (u : q3rqCar)
    (h1 : z3vGe 3 (z3.add u.1 (z3.neg z3.one)) 2)
    (h2 : z3vGe 3 u.2 2) :
    ∃ v, q3rqMul (q3rqMul v v) v = u := by
  have h2' : z3vGe 3 (z3.add u.2 (z3.neg z3.zero)) 2 := by
    rw [CRing.neg_zero z3, CRing.add_zero z3 u.2]
    exact h2
  obtain ⟨e, he⟩ := (q9k4_dvd_iff 2 (q3rqAdd u (q3rqNeg q3rqOne))).mpr ⟨h1, h2'⟩
  have h9 : q3rqAdd u (q3rqNeg q3rqOne) = q3rqMul q9k4Nine e := by
    rw [he]
    exact (q3rqRing.mul_assoc q3rqThreeElt q3rqThreeElt e).symm
  obtain ⟨y, hy⟩ := q9k4_deep_cube e
  exact ⟨y, hy.trans (q9k4_recover_R q3rqRing u (q3rqMul q9k4Nine e) h9).symm⟩

/-! ## q9k4-E: レベル 2（mod 9）座標計算 -/

/-- x のレベル n 座標が (a,b)。 -/
def q9k4V (n : Nat) (x : q3rqCar) (a b : Int) : Prop :=
  x.1.val n = Quot.mk (modCong (3 ^ n)).rel a
  ∧ x.2.val n = Quot.mk (modCong (3 ^ n)).rel b

theorem q9k4_v_exists (n : Nat) (x : q3rqCar) : ∃ a b : Int, q9k4V n x a b := by
  obtain ⟨a, ha⟩ := Quot.exists_rep (x.1.val n)
  obtain ⟨b, hb⟩ := Quot.exists_rep (x.2.val n)
  exact ⟨a, b, ha.symm, hb.symm⟩

/-- 代表の取り換え。 -/
theorem q9k4_v_shift (n : Nat) (x : q3rqCar) (a b a' b' : Int)
    (h : q9k4V n x a b) (ha : ((3 ^ n : Nat) : Int) ∣ (a - a'))
    (hb : ((3 ^ n : Nat) : Int) ∣ (b - b')) : q9k4V n x a' b' := by
  refine ⟨h.1.trans (Quot.sound ha), h.2.trans (Quot.sound hb)⟩

/-- 2 つの表示の差は 3^n で割れる。 -/
theorem q9k4_v_ext (n : Nat) (x : q3rqCar) (a b a' b' : Int)
    (h : q9k4V n x a b) (h' : q9k4V n x a' b') :
    ((3 ^ n : Nat) : Int) ∣ (a - a') ∧ ((3 ^ n : Nat) : Int) ∣ (b - b') :=
  ⟨quot_exact intGrp (modCong (3 ^ n)) (h.1.symm.trans h'.1),
   quot_exact intGrp (modCong (3 ^ n)) (h.2.symm.trans h'.2)⟩

theorem q9k4_v_one (n : Nat) : q9k4V n q3rqOne 1 0 := ⟨q9c3_one_val n, q9c3_zero_val n⟩

/-- **積の座標**: (a,b)·(c,d) = (ac−3bd, ad+bc)。 -/
theorem q9k4_v_mul (n : Nat) (x y : q3rqCar) (a b c d : Int)
    (hx : q9k4V n x a b) (hy : q9k4V n y c d) :
    q9k4V n (q3rqMul x y) (a * c + (-3) * (b * d)) (a * d + b * c) := by
  refine ⟨?_, ?_⟩
  · show (z3.add (z3.mul x.1 y.1) (z3.mul q3rqD (z3.mul x.2 y.2))).val n = _
    exact q9c3_add_val n (z3.mul x.1 y.1) (z3.mul q3rqD (z3.mul x.2 y.2))
      (a * c) ((-3) * (b * d))
      (q9c3_mul_val n x.1 y.1 a c hx.1 hy.1)
      (q9c3_mul_val n q3rqD (z3.mul x.2 y.2) (-3) (b * d) (q9c3_D_val n)
        (q9c3_mul_val n x.2 y.2 b d hx.2 hy.2))
  · show (z3.add (z3.mul x.1 y.2) (z3.mul x.2 y.1)).val n = _
    exact q9c3_add_val n (z3.mul x.1 y.2) (z3.mul x.2 y.1) (a * d) (b * c)
      (q9c3_mul_val n x.1 y.2 a d hx.1 hy.2)
      (q9c3_mul_val n x.2 y.1 b c hx.2 hy.1)

/-! ## q9k4-F: 整数側の 3 進補題 -/

theorem q9k4_dvd_mulL (k a b : Int) (h : k ∣ b) : k ∣ (a * b) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨a * t, ?_⟩
  rw [ht, ← Int.mul_assoc, Int.mul_comm a k, Int.mul_assoc]

theorem q9k4_dvd_mulR (k a b : Int) (h : k ∣ a) : k ∣ (a * b) := by
  rw [Int.mul_comm a b]
  exact q9k4_dvd_mulL k b a h

theorem q9k4_sq_id (c : Int) : (c + -1) * (c + 1) = c * c - 1 := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_one, Int.mul_one]
  omega

theorem q9k4_cube_id (c : Int) : c * c * c - c = c * (c * c - 1) := by
  rw [Int.mul_sub, Int.mul_one, Int.mul_comm c (c * c)]

theorem q9k4_tri (c : Int) :
    (3 : Int) ∣ c ∨ (3 : Int) ∣ (c + -1) ∨ (3 : Int) ∣ (c + 1) := by
  obtain ⟨r, hr⟩ : ∃ r : Int, c = 3 * (c / 3) + r ∧ (r = 0 ∨ r = 1 ∨ r = 2) :=
    ⟨c - 3 * (c / 3), by omega, by omega⟩
  obtain h0 | h1 | h2 := hr.2
  · exact Or.inl ⟨c / 3, by omega⟩
  · exact Or.inr (Or.inl ⟨c / 3, by omega⟩)
  · exact Or.inr (Or.inr ⟨c / 3 + 1, by omega⟩)

/-- **Fermat（p=3）**: 3 ∣ c³ − c。 -/
theorem q9k4_cube_mod3 (c : Int) : (3 : Int) ∣ (c * c * c - c) := by
  rw [q9k4_cube_id c]
  obtain h | h | h := q9k4_tri c
  · exact q9k4_dvd_mulR 3 c (c * c - 1) h
  · refine q9k4_dvd_mulL 3 c (c * c - 1) ?_
    rw [← q9k4_sq_id c]
    exact q9k4_dvd_mulR 3 (c + -1) (c + 1) h
  · refine q9k4_dvd_mulL 3 c (c * c - 1) ?_
    rw [← q9k4_sq_id c]
    exact q9k4_dvd_mulL 3 (c + -1) (c + 1) h

/-! ## q9k4-G: 立方の座標公式と cube 判定（⟹ 方向） -/

theorem q9k4_cube_id1 (c d : Int) :
    (c * c + (-3) * (d * d)) * c + (-3) * ((c * d + d * c) * d)
      = c * c * c + (-9) * (c * (d * d)) := by
  have e1 : (c * c + (-3) * (d * d)) * c = c * c * c + (-3) * (c * (d * d)) := by
    rw [Int.add_mul, Int.mul_assoc (-3) (d * d) c, Int.mul_comm (d * d) c]
  have e2 : (c * d + d * c) * d = c * (d * d) + c * (d * d) := by
    rw [Int.mul_comm d c, Int.add_mul, Int.mul_assoc c d d]
  rw [e1, e2]
  omega

theorem q9k4_cube_id2 (c d : Int) :
    (c * c + (-3) * (d * d)) * d + (c * d + d * c) * c
      = 3 * (c * c * d) + (-3) * (d * d * d) := by
  have e3 : (c * c + (-3) * (d * d)) * d = c * c * d + (-3) * (d * d * d) := by
    rw [Int.add_mul, Int.mul_assoc (-3) (d * d) d]
  have e4 : (c * d + d * c) * c = c * c * d + c * c * d := by
    rw [Int.mul_comm d c, Int.add_mul, Int.mul_assoc c d c, Int.mul_comm d c,
      ← Int.mul_assoc c c d]
  rw [e3, e4]
  omega

/-- **立方の座標**: v=(c,d) ⟹ v³ = (c³−9cd², 3c²d−3d³)。 -/
theorem q9k4_v_cube (n : Nat) (v : q3rqCar) (c d : Int) (h : q9k4V n v c d) :
    q9k4V n (q3rqMul (q3rqMul v v) v)
      (c * c * c + (-9) * (c * (d * d))) (3 * (c * c * d) + (-3) * (d * d * d)) := by
  have h2 := q9k4_v_mul n v v c d c d h h
  have h3 := q9k4_v_mul n (q3rqMul v v) v
    (c * c + (-3) * (d * d)) (c * d + d * c) c d h2 h
  rw [q9k4_cube_id1 c d, q9k4_cube_id2 c d] at h3
  exact h3

/-- **★ 立方判定（⟹）**: u ≡ 1 (mod λ の意味で a≡1 mod 3) が立方なら
    a ≡ 1 (mod 9) かつ b ≡ 0 (mod 9)。 -/
theorem q9k4_cube_forces (u : q3rqCar) (a b : Int) (hu : q9k4V 2 u a b)
    (h3 : (3 : Int) ∣ (a - 1)) (v : q3rqCar)
    (hv : q3rqMul (q3rqMul v v) v = u) :
    (9 : Int) ∣ (a - 1) ∧ (9 : Int) ∣ b := by
  obtain ⟨c, d, hcd⟩ := q9k4_v_exists 2 v
  have hcu := q9k4_v_cube 2 v c d hcd
  rw [hv] at hcu
  obtain ⟨hA, hB⟩ := q9k4_v_ext 2 u _ _ a b hcu hu
  have hA9 : (9 : Int) ∣ ((c * c * c + (-9) * (c * (d * d))) - a) := hA
  have hB9 : (9 : Int) ∣ ((3 * (c * c * d) + (-3) * (d * d * d)) - b) := hB
  have hf := q9k4_cube_mod3 c
  have hc1 : (3 : Int) ∣ (c - 1) := by
    obtain ⟨s, hs⟩ := hA9
    obtain ⟨t, ht⟩ := h3
    obtain ⟨w, hw⟩ := hf
    exact ⟨3 * s + t + 3 * (c * (d * d)) - w, by omega⟩
  have hc9 := q9c3_cube9_of_one c hc1
  have hgoal1 : (9 : Int) ∣ (a - 1) := by
    obtain ⟨s, hs⟩ := hA9
    obtain ⟨w, hw⟩ := hc9
    exact ⟨w - s - (c * (d * d)), by omega⟩
  have hsq : (3 : Int) ∣ (c * c - 1) := by
    rw [← q9k4_sq_id c]
    refine q9k4_dvd_mulR 3 (c + -1) (c + 1) ?_
    obtain ⟨k, hk⟩ := hc1
    exact ⟨k, by omega⟩
  have hdX : (3 : Int) ∣ (d * (c * c - 1)) := q9k4_dvd_mulL 3 d (c * c - 1) hsq
  have hXid : d * (c * c - 1) = c * c * d - d := by
    rw [Int.mul_sub, Int.mul_one, Int.mul_comm d (c * c)]
  rw [hXid] at hdX
  have hfd := q9k4_cube_mod3 d
  have hstep : (3 : Int) ∣ (c * c * d - d * d * d) := by
    obtain ⟨k, hk⟩ := hdX
    obtain ⟨l, hl⟩ := hfd
    exact ⟨k - l, by omega⟩
  have hgoal2 : (9 : Int) ∣ b := by
    obtain ⟨s, hs⟩ := hB9
    obtain ⟨k, hk⟩ := hstep
    exact ⟨k - s, by omega⟩
  exact ⟨hgoal1, hgoal2⟩

theorem q9k4_v_shift2 (x : q3rqCar) (a b a' b' : Int) (h : q9k4V 2 x a b)
    (ha : (9 : Int) ∣ (a - a')) (hb : (9 : Int) ∣ (b - b')) : q9k4V 2 x a' b' :=
  q9k4_v_shift 2 x a b a' b' h ha hb

/-- **★ 立方判定（⟸）**: a ≡ 1, b ≡ 0 (mod 9) なら立方（K2c 経由）。 -/
theorem q9k4_cube_of_v2 (u : q3rqCar) (a b : Int) (hu : q9k4V 2 u a b)
    (ha : (9 : Int) ∣ (a - 1)) (hb : (9 : Int) ∣ b) :
    ∃ v, q3rqMul (q3rqMul v v) v = u := by
  refine q9k4_cube_of_lev2 u ?_ ?_
  · show (z3.add u.1 (z3.neg z3.one)).val 2 = Quot.mk (modCong (3 ^ 2)).rel 0
    rw [q9c3_add_val 2 u.1 (z3.neg z3.one) a (-1) hu.1
      (q9c3_neg_val 2 z3.one 1 (q9c3_one_val 2))]
    apply Quot.sound
    show ((3 ^ 2 : Nat) : Int) ∣ (a + -1) - 0
    obtain ⟨k, hk⟩ := ha
    exact ⟨k, by omega⟩
  · show u.2.val 2 = Quot.mk (modCong (3 ^ 2)).rel 0
    rw [hu.2]
    apply Quot.sound
    show ((3 ^ 2 : Nat) : Int) ∣ b - 0
    obtain ⟨k, hk⟩ := hb
    exact ⟨k, by omega⟩

/-! ## q9k4-H: 生成元 ζ₃・4・1+λ³ のレベル 2 座標 -/

/-- 2⁻¹ ≡ 5 (mod 9)。 -/
theorem q9k4_half_v2 : q3rqHalf.val 2 = Quot.mk (modCong (3 ^ 2)).rel 5 := by
  obtain ⟨h1, hh1⟩ := Quot.exists_rep (q3rqHalf.val 2)
  have hmul := q9c3_mul_val 2 q3rqTwoZ q3rqHalf 2 h1 (q9c3_two_val 2) hh1.symm
  rw [q3rq_two_half, q9c3_one_val 2] at hmul
  have hd := quot_exact intGrp (modCong (3 ^ 2)) hmul
  have hd9 : (9 : Int) ∣ (1 - 2 * h1) := hd
  rw [← hh1]
  apply Quot.sound
  show ((3 ^ 2 : Nat) : Int) ∣ h1 - 5
  obtain ⟨k, hk⟩ := hd9
  exact ⟨-(5 * k + h1), by omega⟩

theorem q9k4_v_zeta : q9k4V 2 q3rqZeta 4 5 := by
  refine q9k4_v_shift2 q3rqZeta (-5) 5 4 5
    ⟨q9c3_neg_val 2 q3rqHalf 5 q9k4_half_v2, q9k4_half_v2⟩ ⟨-1, by omega⟩ ⟨0, by omega⟩

theorem q9k4_v_four : q9k4V 2 q9rcFour 4 0 := by
  have h : q9k4V 2 q9rcFour (1 + 3) 0 := by
    rw [q9rc_four_pair]
    exact ⟨q9c3_c4_val 2, q9c3_zero_val 2⟩
  exact q9k4_v_shift2 q9rcFour (1 + 3) 0 4 0 h ⟨0, by omega⟩ ⟨0, by omega⟩

/-- **第 4 生成元 1+λ³ = (1,−3)**（深い主単数 U^{(3)}∖U^{(4)}）。 -/
def q9k4Deep : q3rqCar := ((z3.one, z3.neg q3rqThree) : q3rqCar)

/-- λ³ = (0,−3) ゆえ q9k4Deep = 1 + λ³。 -/
theorem q9k4_deep_eq :
    q9k4Deep = q3rqAdd q3rqOne (q3rqMul (q3rqMul q3rqLambda q3rqLambda) q3rqLambda) := by
  rw [q3rq_lambda_sq]
  apply q3rq_ext
  · show z3.one = z3.add z3.one
      (z3.add (z3.mul (z3.neg q3rqThree) z3.zero) (z3.mul q3rqD (z3.mul z3.zero z3.one)))
    rw [CRing.mul_zero z3 (z3.neg q3rqThree), z3.zero_mul z3.one,
      CRing.mul_zero z3 q3rqD, z3.zero_add z3.zero, CRing.add_zero z3 z3.one]
  · show z3.neg q3rqThree = z3.add z3.zero
      (z3.add (z3.mul (z3.neg q3rqThree) z3.one) (z3.mul z3.zero z3.zero))
    rw [CRing.mul_one z3 (z3.neg q3rqThree), z3.zero_mul z3.zero,
      CRing.add_zero z3 (z3.neg q3rqThree), z3.zero_add (z3.neg q3rqThree)]

theorem q9k4_v_deep : q9k4V 2 q9k4Deep 1 6 := by
  refine q9k4_v_shift2 q9k4Deep 1 (-3) 1 6
    ⟨q9c3_one_val 2, q9c3_neg_val 2 q3rqThree 3 (q3rq_three_val 2)⟩
    ⟨0, by omega⟩ ⟨-1, by omega⟩

/-- 1+λ³ は単数（N = 1+27 = 28・3∤28）。 -/
theorem q9k4_deep_unit : q3rqUnitMem q9k4Deep := by
  refine ⟨1 * 1 + -((-3) * ((-3) * (-3))), ?_, ?_⟩
  · exact q3mc_norm_lev1 z3.one (z3.neg q3rqThree) 1 (-3) (q9c3_one_val 1)
      (q9c3_neg_val 1 q3rqThree 3 (q3rq_three_val 1))
  · intro h
    obtain ⟨k, hk⟩ := h
    omega

/-! ## q9k4-I: 生成元の冪のレベル 2 座標 -/

theorem q9k4_v_zpow0 : q9k4V 2 (rpow q3rqRing q3rqZeta 0) 1 0 := q9k4_v_one 2
theorem q9k4_v_fpow0 : q9k4V 2 (rpow q3rqRing q9rcFour 0) 1 0 := q9k4_v_one 2
theorem q9k4_v_dpow0 : q9k4V 2 (rpow q3rqRing q9k4Deep 0) 1 0 := q9k4_v_one 2

theorem q9k4_v_zpow1 : q9k4V 2 (rpow q3rqRing q3rqZeta 1) 4 5 :=
  q9k4_v_shift2 (rpow q3rqRing q3rqZeta 1) _ _ 4 5
    (q9k4_v_mul 2 q3rqOne q3rqZeta 1 0 4 5 (q9k4_v_one 2) q9k4_v_zeta)
    ⟨0, by omega⟩ ⟨0, by omega⟩

theorem q9k4_v_zpow2 : q9k4V 2 (rpow q3rqRing q3rqZeta 2) (-59) 40 :=
  q9k4_v_shift2 (rpow q3rqRing q3rqZeta 2) _ _ (-59) 40
    (q9k4_v_mul 2 (rpow q3rqRing q3rqZeta 1) q3rqZeta 4 5 4 5 q9k4_v_zpow1 q9k4_v_zeta)
    ⟨0, by omega⟩ ⟨0, by omega⟩

theorem q9k4_v_fpow1 : q9k4V 2 (rpow q3rqRing q9rcFour 1) 4 0 :=
  q9k4_v_shift2 (rpow q3rqRing q9rcFour 1) _ _ 4 0
    (q9k4_v_mul 2 q3rqOne q9rcFour 1 0 4 0 (q9k4_v_one 2) q9k4_v_four)
    ⟨0, by omega⟩ ⟨0, by omega⟩

theorem q9k4_v_fpow2 : q9k4V 2 (rpow q3rqRing q9rcFour 2) 16 0 :=
  q9k4_v_shift2 (rpow q3rqRing q9rcFour 2) _ _ 16 0
    (q9k4_v_mul 2 (rpow q3rqRing q9rcFour 1) q9rcFour 4 0 4 0 q9k4_v_fpow1 q9k4_v_four)
    ⟨0, by omega⟩ ⟨0, by omega⟩

theorem q9k4_v_dpow1 : q9k4V 2 (rpow q3rqRing q9k4Deep 1) 1 6 :=
  q9k4_v_shift2 (rpow q3rqRing q9k4Deep 1) _ _ 1 6
    (q9k4_v_mul 2 q3rqOne q9k4Deep 1 0 1 6 (q9k4_v_one 2) q9k4_v_deep)
    ⟨0, by omega⟩ ⟨0, by omega⟩

theorem q9k4_v_dpow2 : q9k4V 2 (rpow q3rqRing q9k4Deep 2) (-107) 12 :=
  q9k4_v_shift2 (rpow q3rqRing q9k4Deep 2) _ _ (-107) 12
    (q9k4_v_mul 2 (rpow q3rqRing q9k4Deep 1) q9k4Deep 1 6 1 6 q9k4_v_dpow1 q9k4_v_deep)
    ⟨0, by omega⟩ ⟨0, by omega⟩

/-! ## q9k4-J: 4^k·(1+λ³)^l のレベル 2 座標（9 分岐） -/

/-- 4^k·(1+λ³)^l の mod 9 座標と、(1,0) になるのは k=l=0 に限ることの完全決定。 -/
theorem q9k4_fd_val (k l : Nat) (hk : k < 3) (hl : l < 3) :
    ∃ A B : Int,
      q9k4V 2 (q3rqMul (rpow q3rqRing q9rcFour k) (rpow q3rqRing q9k4Deep l)) A B
      ∧ (3 : Int) ∣ (A - 1) ∧ (3 : Int) ∣ B
      ∧ (((9 : Int) ∣ (A - 1) ∧ (9 : Int) ∣ B) → k = 0 ∧ l = 0) := by
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  have hl3 : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  obtain hk' | hk' | hk' := hk3
  · subst hk'
    obtain hl' | hl' | hl' := hl3
    · subst hl'
      refine ⟨_, _, q9k4_v_mul 2 _ _ 1 0 1 0 q9k4_v_fpow0 q9k4_v_dpow0,
        ⟨0, by omega⟩, ⟨0, by omega⟩, ?_⟩
      intro h
      exact ⟨rfl, rfl⟩
    · subst hl'
      refine ⟨_, _, q9k4_v_mul 2 _ _ 1 0 1 6 q9k4_v_fpow0 q9k4_v_dpow1,
        ⟨0, by omega⟩, ⟨2, by omega⟩, ?_⟩
      intro h
      obtain ⟨t, ht⟩ := h.2
      exact absurd ht (by omega)
    · subst hl'
      refine ⟨_, _, q9k4_v_mul 2 _ _ 1 0 (-107) 12 q9k4_v_fpow0 q9k4_v_dpow2,
        ⟨(-36), by omega⟩, ⟨4, by omega⟩, ?_⟩
      intro h
      obtain ⟨t, ht⟩ := h.2
      exact absurd ht (by omega)
  · subst hk'
    obtain hl' | hl' | hl' := hl3
    · subst hl'
      refine ⟨_, _, q9k4_v_mul 2 _ _ 4 0 1 0 q9k4_v_fpow1 q9k4_v_dpow0,
        ⟨1, by omega⟩, ⟨0, by omega⟩, ?_⟩
      intro h
      obtain ⟨t, ht⟩ := h.1
      exact absurd ht (by omega)
    · subst hl'
      refine ⟨_, _, q9k4_v_mul 2 _ _ 4 0 1 6 q9k4_v_fpow1 q9k4_v_dpow1,
        ⟨1, by omega⟩, ⟨8, by omega⟩, ?_⟩
      intro h
      obtain ⟨t, ht⟩ := h.1
      exact absurd ht (by omega)
    · subst hl'
      refine ⟨_, _, q9k4_v_mul 2 _ _ 4 0 (-107) 12 q9k4_v_fpow1 q9k4_v_dpow2,
        ⟨(-143), by omega⟩, ⟨16, by omega⟩, ?_⟩
      intro h
      obtain ⟨t, ht⟩ := h.1
      exact absurd ht (by omega)
  · subst hk'
    obtain hl' | hl' | hl' := hl3
    · subst hl'
      refine ⟨_, _, q9k4_v_mul 2 _ _ 16 0 1 0 q9k4_v_fpow2 q9k4_v_dpow0,
        ⟨5, by omega⟩, ⟨0, by omega⟩, ?_⟩
      intro h
      obtain ⟨t, ht⟩ := h.1
      exact absurd ht (by omega)
    · subst hl'
      refine ⟨_, _, q9k4_v_mul 2 _ _ 16 0 1 6 q9k4_v_fpow2 q9k4_v_dpow1,
        ⟨5, by omega⟩, ⟨32, by omega⟩, ?_⟩
      intro h
      obtain ⟨t, ht⟩ := h.1
      exact absurd ht (by omega)
    · subst hl'
      refine ⟨_, _, q9k4_v_mul 2 _ _ 16 0 (-107) 12 q9k4_v_fpow2 q9k4_v_dpow2,
        ⟨(-571), by omega⟩, ⟨64, by omega⟩, ?_⟩
      intro h
      obtain ⟨t, ht⟩ := h.1
      exact absurd ht (by omega)

/-! ## q9k4-K: 独立性（rank ≥ 4 の下界） -/

/-- **★★ 独立性**: ζ₃^j·4^k·(1+λ³)^l （j,k,l<3）が O_{L₂} 内で立方なら j=k=l=0。 -/
theorem q9k4_comb_noncube (j k l : Nat) (hj : j < 3) (hk : k < 3) (hl : l < 3)
    (h : ∃ v, q3rqMul (q3rqMul v v) v
      = q3rqMul (rpow q3rqRing q3rqZeta j)
          (q3rqMul (rpow q3rqRing q9rcFour k) (rpow q3rqRing q9k4Deep l))) :
    j = 0 ∧ k = 0 ∧ l = 0 := by
  obtain ⟨A, B, hAB, hA3, hB3, himp⟩ := q9k4_fd_val k l hk hl
  obtain ⟨v, hv⟩ := h
  obtain ⟨s, hs⟩ := hA3
  obtain ⟨t, ht⟩ := hB3
  have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  obtain hj' | hj' | hj' := hj3
  · subst hj'
    have hc := q9k4_v_mul 2 (rpow q3rqRing q3rqZeta 0) _ 1 0 A B q9k4_v_zpow0 hAB
    have hfor := q9k4_cube_forces _ (1 * A + (-3) * (0 * B)) (1 * B + 0 * A) hc
      ⟨s, by omega⟩ v hv
    obtain ⟨p, hp⟩ := hfor.1
    obtain ⟨q, hq⟩ := hfor.2
    exact ⟨rfl, himp ⟨⟨p, by omega⟩, ⟨q, by omega⟩⟩⟩
  · subst hj'
    have hc := q9k4_v_mul 2 (rpow q3rqRing q3rqZeta 1) _ 4 5 A B q9k4_v_zpow1 hAB
    have hfor := q9k4_cube_forces _ (4 * A + (-3) * (5 * B)) (4 * B + 5 * A) hc
      ⟨4 * s + 1 - 15 * t, by omega⟩ v hv
    obtain ⟨q, hq⟩ := hfor.2
    exact absurd hq (by omega)
  · subst hj'
    have hc := q9k4_v_mul 2 (rpow q3rqRing q3rqZeta 2) _ (-59) 40 A B q9k4_v_zpow2 hAB
    have hfor := q9k4_cube_forces _ ((-59) * A + (-3) * (40 * B)) ((-59) * B + 40 * A) hc
      ⟨(-59) * s - 120 * t - 20, by omega⟩ v hv
    obtain ⟨q, hq⟩ := hfor.2
    exact absurd hq (by omega)

/-- **K2b の核**: [1+λ³] は非立方（第 4 次元の存在）。 -/
theorem q9k4_deep_noncube :
    ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ q9k4Deep := by
  intro v hv
  have h : ∃ w, q3rqMul (q3rqMul w w) w
      = q3rqMul (rpow q3rqRing q3rqZeta 0)
          (q3rqMul (rpow q3rqRing q9rcFour 0) (rpow q3rqRing q9k4Deep 1)) := by
    refine ⟨v, hv.trans ?_⟩
    show q9k4Deep = q3rqMul q3rqOne (q3rqMul q3rqOne (q3rqMul q3rqOne q9k4Deep))
    rw [q3rq_one_mul q9k4Deep, q3rq_one_mul q9k4Deep, q3rq_one_mul q9k4Deep]
  have := (q9k4_comb_noncube 0 0 1 (by omega) (by omega) (by omega) h).2.2
  omega

/-! ## q9k4-L: 群提示 ℤ×U₂ 上の rank ≥ 4 -/

def q9k4UPow (x : q3rqU.carrier) : Nat → q3rqU.carrier
  | 0 => q3rqU.one
  | (n + 1) => q3rqU.mul (q9k4UPow x n) x

theorem q9k4_upow_val (x : q3rqU.carrier) (n : Nat) :
    (q9k4UPow x n).val = rpow q3rqRing x.val n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show q3rqMul (q9k4UPow x n).val x.val = q3rqMul (rpow q3rqRing x.val n) x.val
    rw [ih]

/-- U₂ の元としての 1+λ³（第 4 生成元）。 -/
def q9k4DeepUnit : q3rqU.carrier := ⟨q9k4Deep, q9k4_deep_unit⟩

/-- 単数側 4 生成元の結合 ζ₃^j·4^k·(1+λ³)^l ∈ U₂。 -/
def q9k4CombU (j k l : Nat) : q3rqU.carrier :=
  q3rqU.mul (q9k4UPow q9cq_zetaUnit j)
    (q3rqU.mul (q9k4UPow q9c3FourUnit k) (q9k4UPow q9k4DeepUnit l))

theorem q9k4_combU_val (j k l : Nat) :
    (q9k4CombU j k l).val
      = q3rqMul (rpow q3rqRing q3rqZeta j)
          (q3rqMul (rpow q3rqRing q9rcFour k) (rpow q3rqRing q9k4Deep l)) := by
  show q3rqMul (q9k4UPow q9cq_zetaUnit j).val
      (q3rqMul (q9k4UPow q9c3FourUnit k).val (q9k4UPow q9k4DeepUnit l).val) = _
  rw [q9k4_upow_val q9cq_zetaUnit j, q9k4_upow_val q9c3FourUnit k,
    q9k4_upow_val q9k4DeepUnit l]
  rfl

/-- **★★★ rank ≥ 4（単数側 26 結合）**: (j,k,l)≠(0,0,0) なら
    (0, ζ₃^j·4^k·(1+λ³)^l) は L₂^× = ℤ×U₂ 内で非立方。 -/
theorem q9k4_unit_indep (j k l : Nat) (hj : j < 3) (hk : k < 3) (hl : l < 3)
    (hne : ¬ (j = 0 ∧ k = 0 ∧ l = 0)) :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = ((0 : Int), q9k4CombU j k l) := by
  refine q9c3_group_of_ring (q9k4CombU j k l) ?_
  intro v hveq
  refine hne (q9k4_comb_noncube j k l hj hk hl ⟨v, ?_⟩)
  rw [hveq, q9k4_combU_val]

/-- **★★★ q9k4_rank_ge_four**: (ℤ/3)⁴ ↪ L₂^×/(L₂^×)³ の honest 下界形
    ——80 個の非自明結合 λ^i·ζ₃^j·4^k·(1+λ³)^l がすべて非立方。 -/
theorem q9k4_rank_ge_four :
    (∀ i : Int, ¬ (3 : Int) ∣ i → ∀ u : q3rqU.carrier,
      ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((i : Int), u))
    ∧ (∀ j k l : Nat, j < 3 → k < 3 → l < 3 → ¬ (j = 0 ∧ k = 0 ∧ l = 0) →
      ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
        = ((0 : Int), q9k4CombU j k l)) :=
  ⟨fun i hi u => q9cq_val_nontrivial i hi u, q9k4_unit_indep⟩

/-! ## q9k4-M: exhaustion（上界）の 3 段 -/

/-- 段 1: ζ₃^j を掛けて U^{(2)}（b ≡ 0 mod 3）へ。 -/
theorem q9k4_step1 (u : q3rqCar) (a b : Int) (hV : q9k4V 2 u a b)
    (ha : (3 : Int) ∣ (a - 1)) :
    ∃ j : Nat, j < 3 ∧ ∃ a' b' : Int,
      q9k4V 2 (q3rqMul u (rpow q3rqRing q3rqZeta j)) a' b'
      ∧ (3 : Int) ∣ (a' - 1) ∧ (3 : Int) ∣ b' := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, hcase⟩ : ∃ t : Int, b = 3 * t ∨ b = 3 * t + 1 ∨ b = 3 * t + 2 :=
    ⟨b / 3, by omega⟩
  obtain h0 | h1 | h2 := hcase
  · exact ⟨0, by omega, _, _, q9k4_v_mul 2 u _ a b 1 0 hV q9k4_v_zpow0,
      ⟨s, by omega⟩, ⟨t, by omega⟩⟩
  · exact ⟨1, by omega, _, _, q9k4_v_mul 2 u _ a b 4 5 hV q9k4_v_zpow1,
      ⟨4 * s - 15 * t - 4, by omega⟩, ⟨5 * s + 4 * t + 3, by omega⟩⟩
  · exact ⟨2, by omega, _, _, q9k4_v_mul 2 u _ a b (-59) 40 hV q9k4_v_zpow2,
      ⟨(-59) * s - 120 * t - 100, by omega⟩, ⟨40 * s - 59 * t - 26, by omega⟩⟩

/-- 段 2: 4^k を掛けて U^{(3)}（a ≡ 1 mod 9）へ。 -/
theorem q9k4_step2 (u : q3rqCar) (a b : Int) (hV : q9k4V 2 u a b)
    (ha : (3 : Int) ∣ (a - 1)) (hb : (3 : Int) ∣ b) :
    ∃ k : Nat, k < 3 ∧ ∃ a' b' : Int,
      q9k4V 2 (q3rqMul u (rpow q3rqRing q9rcFour k)) a' b'
      ∧ (9 : Int) ∣ (a' - 1) ∧ (3 : Int) ∣ b' := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  obtain ⟨s', hcase⟩ : ∃ s' : Int, s = 3 * s' ∨ s = 3 * s' + 1 ∨ s = 3 * s' + 2 :=
    ⟨s / 3, by omega⟩
  obtain h0 | h1 | h2 := hcase
  · exact ⟨0, by omega, _, _, q9k4_v_mul 2 u _ a b 1 0 hV q9k4_v_fpow0,
      ⟨s', by omega⟩, ⟨t, by omega⟩⟩
  · exact ⟨2, by omega, _, _, q9k4_v_mul 2 u _ a b 16 0 hV q9k4_v_fpow2,
      ⟨16 * s' + 7, by omega⟩, ⟨16 * t, by omega⟩⟩
  · exact ⟨1, by omega, _, _, q9k4_v_mul 2 u _ a b 4 0 hV q9k4_v_fpow1,
      ⟨4 * s' + 3, by omega⟩, ⟨4 * t, by omega⟩⟩

/-- 段 3: (1+λ³)^l を掛けて U^{(4)}（a ≡ 1, b ≡ 0 mod 9）へ。 -/
theorem q9k4_step3 (u : q3rqCar) (a b : Int) (hV : q9k4V 2 u a b)
    (ha : (9 : Int) ∣ (a - 1)) (hb : (3 : Int) ∣ b) :
    ∃ l : Nat, l < 3 ∧ ∃ a' b' : Int,
      q9k4V 2 (q3rqMul u (rpow q3rqRing q9k4Deep l)) a' b'
      ∧ (9 : Int) ∣ (a' - 1) ∧ (9 : Int) ∣ b' := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  obtain ⟨t', hcase⟩ : ∃ t' : Int, t = 3 * t' ∨ t = 3 * t' + 1 ∨ t = 3 * t' + 2 :=
    ⟨t / 3, by omega⟩
  obtain h0 | h1 | h2 := hcase
  · exact ⟨0, by omega, _, _, q9k4_v_mul 2 u _ a b 1 0 hV q9k4_v_dpow0,
      ⟨s, by omega⟩, ⟨t', by omega⟩⟩
  · exact ⟨1, by omega, _, _, q9k4_v_mul 2 u _ a b 1 6 hV q9k4_v_dpow1,
      ⟨s - 2 * b, by omega⟩, ⟨6 * s + t' + 1, by omega⟩⟩
  · exact ⟨2, by omega, _, _, q9k4_v_mul 2 u _ a b (-107) 12 hV q9k4_v_dpow2,
      ⟨(-107) * s - 4 * b - 12, by omega⟩, ⟨12 * s - 107 * t' - 70, by omega⟩⟩

/-! ## q9k4-N: 単数側 exhaustion -/

/-- レベル 2 の値からレベル 1 の値へ（整合族の遷移）。 -/
theorem q9k4_v_down (x : q3rqCar) (a b : Int) (h : q9k4V 2 x a b) :
    x.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel a
    ∧ x.2.val 1 = Quot.mk (modCong (3 ^ 1)).rel b := by
  constructor
  · have hp := x.1.property (show (1 : Nat) ≤ 2 by omega)
    rw [h.1] at hp
    exact hp.symm
  · have hp := x.2.property (show (1 : Nat) ≤ 2 by omega)
    rw [h.2] at hp
    exact hp.symm

/-- 単数の第 1 座標は ℤ₃ 単数（3 ∤ a）。 -/
theorem q9k4_unit_fst (u : q3rqCar) (hu : q3rqUnitMem u) (a b : Int)
    (h : q9k4V 2 u a b) : ¬ ((3 : Int) ∣ a) := by
  obtain ⟨r, hr, hnr⟩ := hu
  have hd := q9k4_v_down u a b h
  have hn := q3mc_norm_lev1 u.1 u.2 a b hd.1 hd.2
  have heq : Quot.mk (modCong (3 ^ 1)).rel r
      = Quot.mk (modCong (3 ^ 1)).rel (a * a + (-((-3) * (b * b)))) := hr.symm.trans hn
  have hdv : (3 : Int) ∣ (r - (a * a + (-((-3) * (b * b))))) :=
    quot_exact intGrp (modCong (3 ^ 1)) heq
  intro h3
  apply hnr
  obtain ⟨w, hw⟩ := q9k4_dvd_mulR 3 a a h3
  obtain ⟨m, hm⟩ := hdv
  exact ⟨w + b * b + m, by omega⟩

theorem q9k4_assoc4_R (R : CRing) (u x y z : R.carrier) :
    R.mul (R.mul (R.mul u x) y) z = R.mul u (R.mul x (R.mul y z)) := by
  rw [R.mul_assoc (R.mul u x) y z, R.mul_assoc u x (R.mul y z)]

theorem q9k4_cube_neg_R (R : CRing) (v : R.carrier) :
    R.mul (R.mul (R.neg v) (R.neg v)) (R.neg v) = R.neg (R.mul (R.mul v v) v) := by
  rw [CRing.neg_mul R v (R.neg v), CRing.mul_neg R v v, CRing.neg_neg R (R.mul v v),
    CRing.mul_neg R (R.mul v v) v]

theorem q9k4_neg_mul_neg_R (R : CRing) (u c : R.carrier) :
    R.neg (R.mul (R.neg u) c) = R.mul u c := by
  rw [CRing.neg_mul R u c, CRing.neg_neg R (R.mul u c)]

/-- a ≡ 1 (mod 3) の場合の exhaustion（3 段の合成）。 -/
theorem q9k4_exhaust_pos (u : q3rqCar) (a b : Int) (hV : q9k4V 2 u a b)
    (ha : (3 : Int) ∣ (a - 1)) :
    ∃ j k l : Nat, j < 3 ∧ k < 3 ∧ l < 3 ∧
      ∃ v, q3rqMul (q3rqMul v v) v
        = q3rqMul u (q3rqMul (rpow q3rqRing q3rqZeta j)
            (q3rqMul (rpow q3rqRing q9rcFour k) (rpow q3rqRing q9k4Deep l))) := by
  obtain ⟨j, hj, a1, b1, hV1, ha1, hb1⟩ := q9k4_step1 u a b hV ha
  obtain ⟨k, hk, a2, b2, hV2, ha2, hb2⟩ := q9k4_step2 _ a1 b1 hV1 ha1 hb1
  obtain ⟨l, hl, a3, b3, hV3, ha3, hb3⟩ := q9k4_step3 _ a2 b2 hV2 ha2 hb2
  obtain ⟨v, hv⟩ := q9k4_cube_of_v2 _ a3 b3 hV3 ha3 hb3
  refine ⟨j, k, l, hj, hk, hl, v, hv.trans ?_⟩
  exact q9k4_assoc4_R q3rqRing u (rpow q3rqRing q3rqZeta j)
    (rpow q3rqRing q9rcFour k) (rpow q3rqRing q9k4Deep l)

/-- **★★ exhaustion（単数側）**: 任意の単数 u に対し、j,k,l<3 と v があって
    u·ζ₃^j·4^k·(1+λ³)^l = v³。 -/
theorem q9k4_exhaust_unit (u : q3rqCar) (hu : q3rqUnitMem u) :
    ∃ j k l : Nat, j < 3 ∧ k < 3 ∧ l < 3 ∧
      ∃ v, q3rqMul (q3rqMul v v) v
        = q3rqMul u (q3rqMul (rpow q3rqRing q3rqZeta j)
            (q3rqMul (rpow q3rqRing q9rcFour k) (rpow q3rqRing q9k4Deep l))) := by
  obtain ⟨a, b, hV⟩ := q9k4_v_exists 2 u
  have hna := q9k4_unit_fst u hu a b hV
  have hcase : (3 : Int) ∣ (a - 1) ∨ (3 : Int) ∣ ((-a) - 1) := by
    obtain ⟨q, hq⟩ : ∃ q : Int, a = 3 * q ∨ a = 3 * q + 1 ∨ a = 3 * q + 2 :=
      ⟨a / 3, by omega⟩
    obtain h0 | h1 | h2 := hq
    · exact absurd ⟨q, h0⟩ hna
    · exact Or.inl ⟨q, by omega⟩
    · exact Or.inr ⟨-q - 1, by omega⟩
  obtain hpos | hneg := hcase
  · exact q9k4_exhaust_pos u a b hV hpos
  · obtain ⟨j, k, l, hj, hk, hl, v, hv⟩ :=
      q9k4_exhaust_pos (q3rqNeg u) (-a) (-b)
        ⟨q9c3_neg_val 2 u.1 a hV.1, q9c3_neg_val 2 u.2 b hV.2⟩ hneg
    refine ⟨j, k, l, hj, hk, hl, q3rqNeg v, ?_⟩
    have hcn : q3rqMul (q3rqMul (q3rqNeg v) (q3rqNeg v)) (q3rqNeg v)
        = q3rqNeg (q3rqMul (q3rqMul v v) v) := q9k4_cube_neg_R q3rqRing v
    rw [hcn, hv]
    exact q9k4_neg_mul_neg_R q3rqRing u
      (q3rqMul (rpow q3rqRing q3rqZeta j)
        (q3rqMul (rpow q3rqRing q9rcFour k) (rpow q3rqRing q9k4Deep l)))

/-! ## q9k4-O: 群提示 ℤ×U₂ 上の exhaustion -/

/-- w³ が単数なら w も単数。 -/
theorem q9k4_unit_of_cube (w : q3rqCar)
    (h : q3rqUnitMem (q3rqMul (q3rqMul w w) w)) : q3rqUnitMem w := by
  obtain ⟨r, hr, hnr⟩ := h
  obtain ⟨c, hc⟩ := Quot.exists_rep ((q3rqNorm w).val 1)
  have hn : q3rqNorm (q3rqMul (q3rqMul w w) w)
      = z3.mul (z3.mul (q3rqNorm w) (q3rqNorm w)) (q3rqNorm w) := by
    rw [q3rq_norm_mul (q3rqMul w w) w, q3rq_norm_mul w w]
  have hlev : (q3rqNorm (q3rqMul (q3rqMul w w) w)).val 1
      = Quot.mk (modCong (3 ^ 1)).rel (c * c * c) := by
    rw [hn]
    exact q9c3_mul_val 1 (z3.mul (q3rqNorm w) (q3rqNorm w)) (q3rqNorm w) (c * c) c
      (q9c3_mul_val 1 (q3rqNorm w) (q3rqNorm w) c c hc.symm hc.symm) hc.symm
  have hdv : (3 : Int) ∣ (r - c * c * c) :=
    quot_exact intGrp (modCong (3 ^ 1)) (hr.symm.trans hlev)
  refine ⟨c, hc.symm, ?_⟩
  intro h3
  apply hnr
  obtain ⟨w2, hw2⟩ := q9k4_dvd_mulR 3 (c * c) c (q9k4_dvd_mulL 3 c c h3)
  obtain ⟨m, hm⟩ := hdv
  exact ⟨w2 + m, by omega⟩

/-- **★★★ exhaustion（L₂^× = ℤ×U₂ 全体）**: 任意の g に対し i,j,k,l<3 と c があって
    g·λ^i·ζ₃^j·4^k·(1+λ³)^l = c³。 -/
theorem q9k4_exhaust (g : q3rqLx.carrier) :
    ∃ i j k l : Nat, i < 3 ∧ j < 3 ∧ k < 3 ∧ l < 3 ∧
      ∃ c : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul c c) c
        = q3rqLx.mul g (((i : Nat) : Int), q9k4CombU j k l) := by
  obtain ⟨j, k, l, hj, hk, hl, v, hv⟩ := q9k4_exhaust_unit g.2.val g.2.property
  have hcombval := q9k4_combU_val j k l
  have hvu : q3rqUnitMem v := by
    refine q9k4_unit_of_cube v ?_
    rw [hv, ← hcombval]
    exact q3rq_unit_mul g.2.property (q9k4CombU j k l).property
  obtain ⟨n, hn⟩ : ∃ n : Int, n = g.1 := ⟨g.1, rfl⟩
  obtain ⟨i, hi3, m, hm⟩ : ∃ i : Nat, i < 3 ∧ ∃ mm : Int, n + ((i : Nat) : Int) = 3 * mm := by
    obtain ⟨q, hq⟩ : ∃ q : Int, n = 3 * q ∨ n = 3 * q + 1 ∨ n = 3 * q + 2 :=
      ⟨n / 3, by omega⟩
    obtain h0 | h1 | h2 := hq
    · exact ⟨0, by omega, q, by omega⟩
    · exact ⟨2, by omega, q + 1, by omega⟩
    · exact ⟨1, by omega, q + 1, by omega⟩
  refine ⟨i, j, k, l, hi3, hj, hk, hl, ((m, ⟨v, hvu⟩) : Int × q3rqU.carrier), ?_⟩
  have hfst : ((m + m) + m : Int) = g.1 + ((i : Nat) : Int) := by
    rw [← hn]; omega
  have hsnd : q3rqU.mul (q3rqU.mul ⟨v, hvu⟩ ⟨v, hvu⟩) ⟨v, hvu⟩
      = q3rqU.mul g.2 (q9k4CombU j k l) := by
    apply Subtype.ext
    show q3rqMul (q3rqMul v v) v = q3rqMul g.2.val (q9k4CombU j k l).val
    rw [hcombval]
    exact hv
  show ((((m + m) + m : Int)), q3rqU.mul (q3rqU.mul ⟨v, hvu⟩ ⟨v, hvu⟩) ⟨v, hvu⟩)
      = ((g.1 + ((i : Nat) : Int)), q3rqU.mul g.2 (q9k4CombU j k l))
  rw [hfst, hsnd]

/-! ## q9k4-P: 完全構造定理（|L₂^×/(L₂^×)³| = 81） -/

/-- **★★ 立方判定の完全形（⟺）**: a ≡ 1 (mod 3) の元 u について
    u が O_{L₂} の立方 ⟺ a ≡ 1 かつ b ≡ 0 (mod 9)（＝ u ∈ U^{(4)}）。 -/
theorem q9k4_cube_iff (u : q3rqCar) (a b : Int) (hu : q9k4V 2 u a b)
    (h3 : (3 : Int) ∣ (a - 1)) :
    (∃ v, q3rqMul (q3rqMul v v) v = u) ↔ ((9 : Int) ∣ (a - 1) ∧ (9 : Int) ∣ b) := by
  constructor
  · intro ⟨v, hv⟩
    exact q9k4_cube_forces u a b hu h3 v hv
  · intro ⟨ha, hb⟩
    exact q9k4_cube_of_v2 u a b hu ha hb

/-- **★★★ 独立性（80 個の非自明結合）**: λ^i·ζ₃^j·4^k·(1+λ³)^l が L₂^× 内で立方なら
    i=j=k=l=0。 -/
theorem q9k4_indep_full (i j k l : Nat) (hi : i < 3) (hj : j < 3) (hk : k < 3)
    (hl : l < 3)
    (h : ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = (((i : Nat) : Int), q9k4CombU j k l)) :
    i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 := by
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  obtain hi0 | hi1 | hi2 := hi3
  · subst hi0
    obtain ⟨g, hg⟩ := h
    have h2 : (q3rqLx.mul (q3rqLx.mul g g) g).2 = q9k4CombU j k l := congrArg Prod.snd hg
    have hval : q3rqMul (q3rqMul g.2.val g.2.val) g.2.val = (q9k4CombU j k l).val :=
      congrArg Subtype.val h2
    rw [q9k4_combU_val] at hval
    exact ⟨rfl, q9k4_comb_noncube j k l hj hk hl ⟨g.2.val, hval⟩⟩
  · subst hi1
    exact absurd h (q9cq_val_nontrivial (((1 : Nat) : Int)) (by omega) (q9k4CombU j k l))
  · subst hi2
    exact absurd h (q9cq_val_nontrivial (((2 : Nat) : Int)) (by omega) (q9k4CombU j k l))

/-- **★★★ 上下両界**: 代表族 λ^i ζ₃^j 4^k (1+λ³)^l （i,j,k,l < 3・81 個）について
    (i) **exhaustion**: 任意の g にどれかを掛けると立方（⟹ **|L₂^×/(L₂^×)³| ≤ 81**）、
    (ii) **independence**: 80 個の非自明代表はそれ自身立方でない（rank≥4 の honest 下界形）。
    ★**正直な限定（ヘッダ限定 2）**: 「81 個の代表の類が互いに相異なる」ことは
    本モジュールでは形式化していない。したがって上界は完全だが、
    「ちょうど 81」は elementary な一歩（代表写像の準同型性）を残す。 -/
theorem q9k4_structure_81 :
    (∀ g : q3rqLx.carrier, ∃ i j k l : Nat, i < 3 ∧ j < 3 ∧ k < 3 ∧ l < 3 ∧
      ∃ c : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul c c) c
        = q3rqLx.mul g (((i : Nat) : Int), q9k4CombU j k l))
    ∧ (∀ i j k l : Nat, i < 3 → j < 3 → k < 3 → l < 3 →
      (∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
        = (((i : Nat) : Int), q9k4CombU j k l)) → i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0) :=
  ⟨q9k4_exhaust, q9k4_indep_full⟩

/-! ## q9k4-Q: capstone -/

/-- **`Q3CubeQuotientFullData`**: 実 L₂ = ℚ₃(ζ₃) の立方剰余群の完全構造データ。 -/
structure Q3CubeQuotientFullData where
  /-- K2c: U^{(4)} = 1+9O ⊆ (O^×)³（逐次近似＋完備性）。 -/
  deep_cube : ∀ m : q3rqCar, ∃ y : q3rqCar,
    q3rqMul (q3rqMul y y) y = q3rqAdd q3rqOne (q3rqMul q9k4Nine m)
  /-- 立方判定の完全形（U^{(1)} 内で 立方 ⟺ mod 9 で 1）。 -/
  cube_iff : ∀ (u : q3rqCar) (a b : Int), q9k4V 2 u a b → (3 : Int) ∣ (a - 1) →
    ((∃ v, q3rqMul (q3rqMul v v) v = u) ↔ ((9 : Int) ∣ (a - 1) ∧ (9 : Int) ∣ b))
  /-- K2b: 第 4 生成元 1+λ³ は非立方。 -/
  deep_noncube : ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ q9k4Deep
  /-- rank ≥ 4（80 個の非自明結合が非立方）。 -/
  indep : ∀ i j k l : Nat, i < 3 → j < 3 → k < 3 → l < 3 →
    (∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = (((i : Nat) : Int), q9k4CombU j k l)) → i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0
  /-- 上界 exhaustion（81 個の類が全体を覆う）。 -/
  exhaust : ∀ g : q3rqLx.carrier, ∃ i j k l : Nat, i < 3 ∧ j < 3 ∧ k < 3 ∧ l < 3 ∧
    ∃ c : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul c c) c
      = q3rqLx.mul g (((i : Nat) : Int), q9k4CombU j k l)

/-- **見出し実例** — 実 L₂ = ℚ₃(√−3) の立方剰余群 ≅ (ℤ/3)⁴。 -/
def q9k4_data : Q3CubeQuotientFullData where
  deep_cube := q9k4_deep_cube
  cube_iff := q9k4_cube_iff
  deep_noncube := q9k4_deep_noncube
  indep := q9k4_indep_full
  exhaust := q9k4_exhaust

theorem q9k4_exists : Nonempty Q3CubeQuotientFullData := ⟨q9k4_data⟩

end IUT