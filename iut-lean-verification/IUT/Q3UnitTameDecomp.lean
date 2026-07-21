/-
  IUT/Q3UnitTameDecomp.lean — 柱B・B2 T3-M4-a: tame/torsion 掃き出し
    （U_{L₂} の単数を torsion ノルム × 4^c で U^{(3)}_λ 深部へ掃き出す tame 分解）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（骨格・模型・代理でなく、実 O_{L₂} =
     q3rqRing・実 O_M = q3kRing・実 3 次ノルム q3kNormBase の上で、任意の実単数
     u ∈ U_{L₂} を「torsion ノルム（−1 = N(−1)・ζ₃^d = N(ζ₉^d)）× 4^c × U^{(3)}_λ 深部」
     へ分解する。audit/pillar-B2-T3-M4-index-detail-2026-07-20.md §3 M4-a の実装。
     toy 主語なし——主語は実局所環の実単数群。）

  complete_pct 影響: **B2 T3-M4-a（tame 掃き出し・M3 独立枠）・s_B2 予測 +0.01〜0.03**。
  T3-M4（[U_{L₂}:N(U_M)] ≤ 3）の前半を閉じる: 単数 u に対し
  ∃ g ∈ Gal(M/L₂), ∃ w ∈ U_M, u·N(w)·φ(g) ∈ U^{(3)}_λ（q9nfUfilt 9 の embed 形・
  単数性込み）。**単体では index ≤ 3 を主張しない**（M4-b が M3 の T3-core
  U^{(3)}_λ ⊆ N(U_M) と合成して初めて index = 3・Gal ≅ 余核が閉じる）。

  内容（M4-a1〜a6・設計書 §3 準拠）:
   * q9ut_f3_tri / q9ut_res3_unit_ne / q9ut_unit_resL_ne / q9ut_unit_res_pm
       — a1: 𝔽₃ 三分法（r = 0 ∨ 1 ∨ −1・choice-free）と unit ⟹ res_L ≠ 0
         （res_L(u)=0 ⟹ λ∣u ⟹ N(u)=3·N(f) ⟹ 3∣N(u)、単数性に矛盾）
   * q9utIsNorm / q9ut_isNorm_neg_one / q9ut_isNorm_zeta / q9ut_isNorm_zetaSq /
     q9ut_isNorm_mul
       — a2: torsion ノルム帳簿（−1 = N(−1)・ζ₃ = N(ζ₉)・ζ₃² = N(ζ₉²)・積閉）。
         消費: q9ps_neg_one_normBase・q9nf_zeta_is_norm（= q9tl_normBase_zeta9 の束ね）
   * q9utUL / q9ut_step_ring / q9ut_sweep_step / q9ut_ul_deepen
       — λ-side 単数フィルトレーション U^{(j)}_λ と乗法的掃き出しの一般段
         （(1+λ^j m)(1+λ^j c) − 1 = λ^j(m+c+λ^j mc)・gr^j 剰余の加法性）
   * q9ut_gr0_sweep — a3: ∀u unit, ∃s∈{1,−1} ノルム, u·s ∈ U^{(1)}_λ
   * q9ut_gr1_sweep — a4: u ∈ U^{(1)}_λ ⟹ ∃ζ₃^d ノルム, u·ζ₃^d ∈ U^{(2)}_λ
         （ζ₃−1 = λ(ζ₃+1) = q9nf_zeta_sub_one_split の L₂ 側形 q9ps_coord0、
          res_L(ζ₃+1) = 1+1 = −1 を**計算で**取得——§5-3 の教訓遵守）
   * q9ut_gr2_sweep — a5: u ∈ U^{(2)}_λ ⟹ ∃c∈{0,1,2}, u·4^c ∈ U^{(3)}_λ
         （4−1 = 3 = −λ²・q3rq_three_eq_neg_lambda_sq の厳密等式・gr² 剰余 −1）
   * q9ut_tame_decomp — a6（★ M4-a 主定理）: ∀u unit, ∃g, ∃w unit,
         u·N(w)·(q9rgPhi g) ∈ U^{(3)}_λ（q9nfUfilt 9 の embed 着地・q9na_lam_ascent）
   * q9ut_tame_z3 — 上界側（掃き出し完全被覆）と下界側（q9rc_z3_injects の
         {[1],[4],[16]} pairwise 相異）の束ね——tame 商 ≅ ℤ/3 の element-level 形
   * Q3UnitTameDecompData / q9ut_data / q9ut_exists — capstone

  正直な限定（§4 規約により消さない・弱めない・q9rc/q9rg/q9gn/q9nf/q9ps/q9rf/q3k/q3rq
  継承の上に追記のみ）:
  1. **M4-a は tame/torsion 掃き出しのみ**。完全な [U_{L₂}:N(U_M)] ≤ 3 は未達——
     wild 部 U^{(3)}_λ ⊆ N(U_M)（M3 の T3-core・厳密 N(x)=u）と M4-b の index 勘定
     （∀u, ∃g, q9rcCongMod (q9rgPhi g) u ⟹ q9qcGalHom 全射）が必要。本ファイルは
     tame 側の構造（掃き出し 18 類のうち torsion 6 類 + 4^c transversal）のみを確立する。
  2. **余核 ℤ/3 の同定は element-level**（q9rc 限定 2 の継承）。tame 商 ≅ ℤ/3 は
     「掃き出し被覆（上界側 infrastructure）+ 三類 pairwise 相異（q9rc_z3_injects）」の
     対として表現し、商群対象上の同型は主張しない。
  3. **単一拡大 M/L₂/ℚ₃ のみ・σ を超える Galois ゼロ・可除性 witness 形式**
     （v_M/v_λ 付値関数不使用・q9wrDvd/λ^j witness）。分数元 M^× の bookkeeping はゼロ
     （整単数のみ）。
  4. q9rgPhi（e↦1, s↦4, s2↦16）は「単射になる生成元対応」であって Frobenius 正規化された
     Artin 写像ではない（q9rg 限定の継承）。
  5. q9rc/q9rg/q9gn/q9nf/q9ps/q9rf/q9wr/q3k/q3rq の正直限定を全継承（O_M と M^× のみ・
     体化なし・実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用
  （omega は Int/Nat 原子のみ）。
-/
import IUT.Q3ReciprocityGalReal
import IUT.Q3NormSurjApproxClose

namespace IUT

/-! ## q9ut-0: λ 冪の簿記（q3rqLamPow の小展開と res_L） -/

/-- λ¹ = λ。 -/
theorem q9ut_lampow_one : q3rqLamPow 1 = q3rqLambda := by
  show q3rqMul q3rqLambda q3rqOne = q3rqLambda
  exact q3rq_mul_one q3rqLambda

/-- λ² = λ·λ。 -/
theorem q9ut_lampow_two : q3rqLamPow 2 = q3rqMul q3rqLambda q3rqLambda := by
  show q3rqMul q3rqLambda (q3rqLamPow 1) = q3rqMul q3rqLambda q3rqLambda
  rw [q9ut_lampow_one]

/-- res_L(λ^{k+1}) = 0（λ ↦ 0 と乗法性）。 -/
theorem q9ut_resL_lampow_succ (k : Nat) :
    q9rfResL (q3rqLamPow (k + 1)) = q9rfF3.zero := by
  rw [q9na_lampow_succ k, q9rf_resL_mul, q9rf_resL_lambda,
      q9rfF3.zero_mul (q9rfResL (q3rqLamPow k))]

/-- res_L(λ¹) = 0。 -/
theorem q9ut_resL_lampow_one : q9rfResL (q3rqLamPow 1) = q9rfF3.zero :=
  q9ut_resL_lampow_succ 0

/-- res_L(λ²) = 0。 -/
theorem q9ut_resL_lampow_two : q9rfResL (q3rqLamPow 2) = q9rfF3.zero :=
  q9ut_resL_lampow_succ 1

/-! ## q9ut-1: a1 前半——𝔽₃ 三分法（choice-free・Quot.ind + Quot.sound） -/

/-- Int の 3-剰余三分法（omega・division witness 陽構成）。 -/
theorem q9ut_int_tri (a : Int) :
    ((3 : Nat) : Int) ∣ (a - 0) ∨ ((3 : Nat) : Int) ∣ (a - 1) ∨
      ((3 : Nat) : Int) ∣ (a - (-1)) := by
  have h3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  obtain h | h | h := h3
  · exact Or.inl ⟨a / 3, by omega⟩
  · exact Or.inr (Or.inl ⟨a / 3, by omega⟩)
  · exact Or.inr (Or.inr ⟨(a + 1) / 3, by omega⟩)

/-- **q9ut-1a（★ a1・𝔽₃ 三分法）: 任意の r ∈ 𝔽₃ は 0, 1, −1 のいずれか**。
    代表 a を Quot.ind で取り、Int 側三分法（q9ut_int_tri）を Quot.sound で
    類の等式へ持ち上げる。witness 抽出なし・choice-free。 -/
theorem q9ut_f3_tri (r : q9rfF3.carrier) :
    r = q9rfF3.zero ∨ r = q9rfF3.one ∨ r = q9rfF3.neg q9rfF3.one := by
  induction r using Quot.ind
  rename_i a
  obtain h | h | h := q9ut_int_tri a
  · exact Or.inl (Quot.sound h)
  · exact Or.inr (Or.inl (Quot.sound h))
  · exact Or.inr (Or.inr (Quot.sound h))

/-- 𝔽₃: (−1)·(−1) = 1。 -/
theorem q9ut_f3_negone_sq :
    q9rfF3.mul (q9rfF3.neg q9rfF3.one) (q9rfF3.neg q9rfF3.one) = q9rfF3.one := by
  rw [q9rfF3.neg_mul q9rfF3.one (q9rfF3.neg q9rfF3.one),
      q9rfF3.one_mul (q9rfF3.neg q9rfF3.one),
      q9rfF3.neg_neg q9rfF3.one]

/-- 𝔽₃: (−1) + (−1) = 1（= −2 ≡ 1・q9nc_two_negone 消費）。 -/
theorem q9ut_f3_negone_add_negone :
    q9rfF3.add (q9rfF3.neg q9rfF3.one) (q9rfF3.neg q9rfF3.one) = q9rfF3.one := by
  rw [← q9rfF3.neg_add_dist q9rfF3.one q9rfF3.one, q9nc_two_negone,
      q9rfF3.neg_neg q9rfF3.one]

/-! ## q9ut-2: a1 後半——unit ⟹ res_L ≠ 0（§2 A4 の解体の実装） -/

/-- **ℤ₃ 単数の level-1 剰余は非零**（IsZpUnit の代表 a・3∤a を quot_exact で降ろす）。 -/
theorem q9ut_res3_unit_ne (x : z3.carrier) (hx : IsZpUnit 3 x) :
    q9rfRes3 x ≠ q9rfF3.zero := by
  intro h0
  obtain ⟨a, hval, hnd⟩ := hx
  have h1 : x.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := h0
  rw [hval] at h1
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (3 ^ 1)) h1
  rw [Nat.pow_one] at hk
  exact hnd ⟨k, by omega⟩

/-- **N(λ) = 3**（λ = (0,1) のノルム = 0² + 3·1² = 3）。 -/
theorem q9ut_norm_lambda : q3rqNorm q3rqLambda = q3rqThree := by
  show z3.add (z3.mul z3.zero z3.zero)
      (z3.neg (z3.mul q3rqD (z3.mul z3.one z3.one))) = q3rqThree
  rw [z3.zero_mul z3.zero, z3.one_mul z3.one, z3.mul_one q3rqD, q3rq_D_eq,
      z3.neg_neg q3rqThree, z3.zero_add q3rqThree]

/-- **q9ut-2a（★ a1・unit ⟹ res_L ≠ 0）**: res_L(u) = 0 なら λ∣u
    （q9gn_resL_lambda_dvd）、N(u) = N(λ)·N(f) = 3·N(f)（Brahmagupta）で
    3∣N(u) となり単数性（IsZpUnit 3 (N u)）に矛盾。 -/
theorem q9ut_unit_resL_ne (u : q3rqCar) (hu : q3rqUnitMem u) :
    q9rfResL u ≠ q9rfF3.zero := by
  intro h0
  obtain ⟨m, hm⟩ := q9gn_resL_lambda_dvd u h0
  have hN : q3rqNorm u = z3.mul q3rqThree (q3rqNorm m) := by
    rw [hm, q3rq_norm_mul q3rqLambda m, q9ut_norm_lambda]
  have hu' : IsZpUnit 3 (z3.mul q3rqThree (q3rqNorm m)) := by
    rw [← hN]
    exact hu
  exact q9wr_three_mul_not_unit (q3rqNorm m) hu'

/-- **単数の三分法**: unit u の res_L は 1 か −1（三分法 + 非零）。 -/
theorem q9ut_unit_res_pm (u : q3rqCar) (hu : q3rqUnitMem u) :
    q9rfResL u = q9rfF3.one ∨ q9rfResL u = q9rfF3.neg q9rfF3.one := by
  obtain h | h | h := q9ut_f3_tri (q9rfResL u)
  · exact absurd h (q9ut_unit_resL_ne u hu)
  · exact Or.inl h
  · exact Or.inr h

/-- res_L(−1) = −1。 -/
theorem q9ut_resL_negone : q9rfResL (q3rqNeg q3rqOne) = q9rfF3.neg q9rfF3.one := by
  rw [q9gn_resL_neg q3rqOne, q9gn_resL_one]

/-! ## q9ut-3: a2——torsion ノルム帳簿（−1 = N(−1)・ζ₃^d = N(ζ₉^d)・積閉） -/

/-- **ノルム像所属**（単数 witness 込み・element-level）。 -/
def q9utIsNorm (a : q3rqCar) : Prop :=
  ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = a

/-- 1 = N(1)。 -/
theorem q9ut_isNorm_one : q9utIsNorm q3rqOne :=
  ⟨q3kOne, q3k_unit_one, q3k_normBase_one⟩

/-- **q9ut-3a（★ a2）: −1 = N(−1)**（奇数次拡大の torsion ノルム・
    q9ps_neg_one_normBase 消費）。 -/
theorem q9ut_isNorm_neg_one : q9utIsNorm (q3rqNeg q3rqOne) :=
  ⟨q3kNeg q3kOne, q9ps_neg_one_unit, q9ps_neg_one_normBase⟩

/-- **q9ut-3b（★ a2）: ζ₃ = N(ζ₉)**（torsion ノルム・q9nf_zeta_is_norm =
    q9tl_normBase_zeta9 の束ね消費）。 -/
theorem q9ut_isNorm_zeta : q9utIsNorm q3rqZeta := q9nf_zeta_is_norm

/-- **ノルム像は積で閉じる**（witness x·y・N の乗法性）。 -/
theorem q9ut_isNorm_mul {a b : q3rqCar} (ha : q9utIsNorm a) (hb : q9utIsNorm b) :
    q9utIsNorm (q3rqMul a b) := by
  obtain ⟨x, hx, hxa⟩ := ha
  obtain ⟨y, hy, hyb⟩ := hb
  exact ⟨q3kMul x y, q3k_unit_mul hx hy, by rw [q3k_normBase_mul x y, hxa, hyb]⟩

/-- **q9ut-3c（a2）: ζ₃² = N(ζ₉²)**（積閉から）。 -/
theorem q9ut_isNorm_zetaSq : q9utIsNorm q3rqZetaSq :=
  q9ut_isNorm_mul q9ut_isNorm_zeta q9ut_isNorm_zeta

/-! ## q9ut-4: λ-side 単数フィルトレーション U^{(j)}_λ と掃き出しの一般段 -/

/-- **U^{(j)}_λ 所属**（λ^j ∣ (u − 1) の witness 形・L₂ 側）。 -/
def q9utUL (j : Nat) (u : q3rqCar) : Prop :=
  ∃ m : q3rqCar, q3rqAdd u (q3rqNeg q3rqOne) = q3rqMul (q3rqLamPow j) m

/-- 1 + (a − 1) = a（シフト分解の巻き戻し）。 -/
theorem q9ut_one_add_shift (a : q3rqCar) :
    q3rqAdd q3rqOne (q3rqAdd a (q3rqNeg q3rqOne)) = a := by
  rw [q3k_A_eq, q3k_N_eq, q9ps_1_eq,
      q3rqRing.add_comm a (q3rqRing.neg q3rqRing.one),
      ← q3rqRing.add_assoc q3rqRing.one (q3rqRing.neg q3rqRing.one) a,
      q3rqRing.add_neg q3rqRing.one, q3rqRing.zero_add a]

/-- **q9ut-4a（★ 掃き出しの純環恒等式）**:
    (1 + Lm)(1 + Lc) − 1 = L·(m + c + L·mc)（gr 剰余の加法性の実体・
    q9nc_step_ring と同型の CRing 恒等式）。 -/
theorem q9ut_step_ring (R : CRing) (L m c : R.carrier) :
    R.add (R.mul (R.add R.one (R.mul L m)) (R.add R.one (R.mul L c))) (R.neg R.one)
      = R.mul L (R.add m (R.add c (R.mul L (R.mul m c)))) := by
  rw [R.right_distrib R.one (R.mul L m) (R.add R.one (R.mul L c)),
      R.one_mul (R.add R.one (R.mul L c)),
      R.left_distrib (R.mul L m) R.one (R.mul L c),
      R.mul_one (R.mul L m),
      R.mul_mul_mul_comm L m L c,
      R.mul_assoc L L (R.mul m c),
      R.add_comm
        (R.add (R.add R.one (R.mul L c))
          (R.add (R.mul L m) (R.mul L (R.mul L (R.mul m c)))))
        (R.neg R.one),
      ← R.add_assoc (R.neg R.one) (R.add R.one (R.mul L c))
        (R.add (R.mul L m) (R.mul L (R.mul L (R.mul m c)))),
      ← R.add_assoc (R.neg R.one) R.one (R.mul L c),
      R.neg_add R.one,
      R.zero_add (R.mul L c),
      R.left_distrib L m (R.add c (R.mul L (R.mul m c))),
      R.left_distrib L c (R.mul L (R.mul m c)),
      R.add_left_comm (R.mul L c) (R.mul L m) (R.mul L (R.mul L (R.mul m c)))]

/-- **q9ut-4b（★ 掃き出しの一般段）**: u = 1 + λ^{j+1}m, t = 1 + λ^{j+1}c で
    res(m) + res(c) = 0 なら u·t ∈ U^{(j+2)}_λ。
    証明: u·t − 1 = λ^{j+1}·S（S = m + c + λ^{j+1}mc）で res(S) = res(m)+res(c) = 0
    ⟹ λ∣S（q9gn_resL_lambda_dvd）⟹ λ^{j+2} ∣ u·t − 1。 -/
theorem q9ut_sweep_step (j : Nat) (u t m c : q3rqCar)
    (hu : u = q3rqAdd q3rqOne (q3rqMul (q3rqLamPow (j + 1)) m))
    (ht : t = q3rqAdd q3rqOne (q3rqMul (q3rqLamPow (j + 1)) c))
    (hres : q9rfF3.add (q9rfResL m) (q9rfResL c) = q9rfF3.zero) :
    q9utUL (j + 2) (q3rqMul u t) := by
  have h1 : q3rqAdd (q3rqMul u t) (q3rqNeg q3rqOne)
      = q3rqMul (q3rqLamPow (j + 1))
          (q3rqAdd m (q3rqAdd c (q3rqMul (q3rqLamPow (j + 1)) (q3rqMul m c)))) := by
    rw [hu, ht, q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq]
    exact q9ut_step_ring q3rqRing (q3rqLamPow (j + 1)) m c
  have h2 : q9rfResL
      (q3rqAdd m (q3rqAdd c (q3rqMul (q3rqLamPow (j + 1)) (q3rqMul m c))))
      = q9rfF3.zero := by
    rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_mul, q9ut_resL_lampow_succ j,
        q9rfF3.zero_mul (q9rfResL (q3rqMul m c)),
        q9rfF3.add_zero (q9rfResL c)]
    exact hres
  obtain ⟨k, hk⟩ := q9gn_resL_lambda_dvd
    (q3rqAdd m (q3rqAdd c (q3rqMul (q3rqLamPow (j + 1)) (q3rqMul m c)))) h2
  refine ⟨k, ?_⟩
  rw [h1, hk]
  show q3rqMul (q3rqLamPow (j + 1)) (q3rqMul q3rqLambda k)
      = q3rqMul (q3rqMul q3rqLambda (q3rqLamPow (j + 1))) k
  rw [q3k_M_eq, q3rqRing.mul_left_comm (q3rqLamPow (j + 1)) q3rqLambda k,
      q3rqRing.mul_assoc q3rqLambda (q3rqLamPow (j + 1)) k]

/-- **q9ut-4c（深化段・掃き出し係数 0 の場合）**: u − 1 = λ^j·m で res(m) = 0 なら
    u ∈ U^{(j+1)}_λ（補正因子なしで 1 段深まる）。 -/
theorem q9ut_ul_deepen (j : Nat) (u m : q3rqCar)
    (hm : q3rqAdd u (q3rqNeg q3rqOne) = q3rqMul (q3rqLamPow j) m)
    (h0 : q9rfResL m = q9rfF3.zero) : q9utUL (j + 1) u := by
  obtain ⟨k, hk⟩ := q9gn_resL_lambda_dvd m h0
  refine ⟨k, ?_⟩
  rw [hm, hk]
  show q3rqMul (q3rqLamPow j) (q3rqMul q3rqLambda k)
      = q3rqMul (q3rqMul q3rqLambda (q3rqLamPow j)) k
  rw [q3k_M_eq, q3rqRing.mul_left_comm (q3rqLamPow j) q3rqLambda k,
      q3rqRing.mul_assoc q3rqLambda (q3rqLamPow j) k]

/-! ## q9ut-5: 具体シフト分解——ζ₃ = 1 + λ(ζ₃+1)・4 = 1 + λ²(−1) と res 計算 -/

/-- ζ₃ の gr¹ 係数 c = ζ₃ + 1。 -/
def q9utZetaC : q3rqCar := q3rqAdd q3rqZeta q3rqOne

/-- **ζ₃ − 1 = λ¹·(ζ₃+1)**（q9ps_coord0 = q9nf_zeta_sub_one_split の L₂ 側厳密等式）。 -/
theorem q9ut_zeta_sub_one :
    q3rqAdd q3rqZeta (q3rqNeg q3rqOne) = q3rqMul (q3rqLamPow 1) q9utZetaC := by
  rw [q9ut_lampow_one]
  show q3rqAdd q3rqZeta (q3rqNeg q3rqOne)
      = q3rqMul q3rqLambda (q3rqAdd q3rqZeta q3rqOne)
  rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq, q9ps_coord0]
  exact q3rqRing.add_comm q3rqZeta (q3rqRing.neg q3rqRing.one)

/-- ζ₃ = 1 + λ¹·(ζ₃+1)（分解形）。 -/
theorem q9ut_zeta_decomp :
    q3rqZeta = q3rqAdd q3rqOne (q3rqMul (q3rqLamPow 1) q9utZetaC) := by
  rw [← q9ut_zeta_sub_one]
  exact (q9ut_one_add_shift q3rqZeta).symm

/-- **res_L(ζ₃+1) = 1 + 1 = −1**（計算で取得・付録 A の数値と整合・§5-3 教訓）。 -/
theorem q9ut_resL_zetaC : q9rfResL q9utZetaC = q9rfF3.neg q9rfF3.one := by
  show q9rfResL (q3rqAdd q3rqZeta q3rqOne) = q9rfF3.neg q9rfF3.one
  rw [q9rf_resL_add, q9rf_resL_zeta, q9gn_resL_one]
  exact q9nc_two_negone

/-- ζ₃² の gr¹ 係数（step_ring の S 形・c = ζ₃+1 の自己積）。 -/
def q9utZetaSqC : q3rqCar :=
  q3rqAdd q9utZetaC (q3rqAdd q9utZetaC
    (q3rqMul (q3rqLamPow 1) (q3rqMul q9utZetaC q9utZetaC)))

/-- **ζ₃² − 1 = λ¹·S₂**（ζ₃² = ζ₃·ζ₃ に step_ring を適用）。 -/
theorem q9ut_zetaSq_sub_one :
    q3rqAdd q3rqZetaSq (q3rqNeg q3rqOne) = q3rqMul (q3rqLamPow 1) q9utZetaSqC := by
  show q3rqAdd (q3rqMul q3rqZeta q3rqZeta) (q3rqNeg q3rqOne)
      = q3rqMul (q3rqLamPow 1)
          (q3rqAdd q9utZetaC (q3rqAdd q9utZetaC
            (q3rqMul (q3rqLamPow 1) (q3rqMul q9utZetaC q9utZetaC))))
  rw [q9ut_zeta_decomp, q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq]
  exact q9ut_step_ring q3rqRing (q3rqLamPow 1) q9utZetaC q9utZetaC

/-- ζ₃² = 1 + λ¹·S₂（分解形）。 -/
theorem q9ut_zetaSq_decomp :
    q3rqZetaSq = q3rqAdd q3rqOne (q3rqMul (q3rqLamPow 1) q9utZetaSqC) := by
  rw [← q9ut_zetaSq_sub_one]
  exact (q9ut_one_add_shift q3rqZetaSq).symm

/-- **res_L(S₂) = (−1) + (−1) = 1**（ζ₃² の gr¹ 剰余・計算で取得）。 -/
theorem q9ut_resL_zetaSqC : q9rfResL q9utZetaSqC = q9rfF3.one := by
  show q9rfResL (q3rqAdd q9utZetaC (q3rqAdd q9utZetaC
      (q3rqMul (q3rqLamPow 1) (q3rqMul q9utZetaC q9utZetaC)))) = q9rfF3.one
  rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_mul, q9ut_resL_lampow_one,
      q9rfF3.zero_mul (q9rfResL (q3rqMul q9utZetaC q9utZetaC)),
      q9rfF3.add_zero (q9rfResL q9utZetaC),
      q9ut_resL_zetaC]
  exact q9ut_f3_negone_add_negone

/-- λ²·(−1) = 3（q3rq_three_eq_neg_lambda_sq の掃き出し形）。 -/
theorem q9ut_lam2_negone :
    q3rqMul (q3rqLamPow 2) (q3rqNeg q3rqOne) = q3rqThreeElt := by
  rw [q9ut_lampow_two, q3k_M_eq, q3k_N_eq, q9ps_1_eq,
      q3rqRing.mul_neg (q3rqRing.mul q3rqLambda q3rqLambda) q3rqRing.one,
      q3rqRing.mul_one (q3rqRing.mul q3rqLambda q3rqLambda)]
  exact q3rq_three_eq_neg_lambda_sq.symm

/-- **4 − 1 = 3 = λ²·(−1)**（gr² 剰余 −1 の厳密実現）。 -/
theorem q9ut_four_sub_one :
    q3rqAdd q9rcFour (q3rqNeg q3rqOne) = q3rqMul (q3rqLamPow 2) (q3rqNeg q3rqOne) := by
  rw [q9ut_lam2_negone]
  show q3rqAdd (q3rqAdd q3rqOne q3rqThreeElt) (q3rqNeg q3rqOne) = q3rqThreeElt
  rw [q3k_A_eq, q3k_N_eq, q9ps_1_eq,
      q3rqRing.add_comm q3rqRing.one q3rqThreeElt,
      q3rqRing.add_assoc q3rqThreeElt q3rqRing.one (q3rqRing.neg q3rqRing.one),
      q3rqRing.add_neg q3rqRing.one,
      q3rqRing.add_zero q3rqThreeElt]

/-- 4 = 1 + λ²·(−1)（分解形）。 -/
theorem q9ut_four_decomp :
    q9rcFour = q3rqAdd q3rqOne (q3rqMul (q3rqLamPow 2) (q3rqNeg q3rqOne)) := by
  rw [← q9ut_four_sub_one]
  exact (q9ut_one_add_shift q9rcFour).symm

/-- 16 の gr² 係数（step_ring の S 形・c = −1 の自己積）。 -/
def q9utC16 : q3rqCar :=
  q3rqAdd (q3rqNeg q3rqOne) (q3rqAdd (q3rqNeg q3rqOne)
    (q3rqMul (q3rqLamPow 2) (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne))))

/-- **16 − 1 = λ²·C₁₆**（16 = 4·4 に step_ring を適用）。 -/
theorem q9ut_foursq_sub_one :
    q3rqAdd q9rcFourSq (q3rqNeg q3rqOne) = q3rqMul (q3rqLamPow 2) q9utC16 := by
  show q3rqAdd (q3rqMul q9rcFour q9rcFour) (q3rqNeg q3rqOne)
      = q3rqMul (q3rqLamPow 2)
          (q3rqAdd (q3rqNeg q3rqOne) (q3rqAdd (q3rqNeg q3rqOne)
            (q3rqMul (q3rqLamPow 2) (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne)))))
  rw [q9ut_four_decomp, q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq]
  exact q9ut_step_ring q3rqRing (q3rqLamPow 2)
    (q3rqRing.neg q3rqRing.one) (q3rqRing.neg q3rqRing.one)

/-- 16 = 1 + λ²·C₁₆（分解形）。 -/
theorem q9ut_foursq_decomp :
    q9rcFourSq = q3rqAdd q3rqOne (q3rqMul (q3rqLamPow 2) q9utC16) := by
  rw [← q9ut_foursq_sub_one]
  exact (q9ut_one_add_shift q9rcFourSq).symm

/-- **res_L(C₁₆) = (−1) + (−1) = 1**（16 の gr² 剰余・計算で取得）。 -/
theorem q9ut_resL_c16 : q9rfResL q9utC16 = q9rfF3.one := by
  show q9rfResL (q3rqAdd (q3rqNeg q3rqOne) (q3rqAdd (q3rqNeg q3rqOne)
      (q3rqMul (q3rqLamPow 2) (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne)))))
    = q9rfF3.one
  rw [q9rf_resL_add, q9rf_resL_add, q9rf_resL_mul, q9ut_resL_lampow_two,
      q9rfF3.zero_mul (q9rfResL (q3rqMul (q3rqNeg q3rqOne) (q3rqNeg q3rqOne))),
      q9rfF3.add_zero (q9rfResL (q3rqNeg q3rqOne)),
      q9ut_resL_negone]
  exact q9ut_f3_negone_add_negone

/-! ## q9ut-6: a3/a4/a5——gr⁰・gr¹・gr² の掃き出し -/

/-- **q9ut-6a（★ a3・gr⁰ 掃き）**: 任意の単数 u に対し s ∈ {1, −1}（torsion ノルム）で
    u·s ∈ U^{(1)}_λ。res_L(u) = ±1 の場合分けで s = res_L(u)⁻¹ 側を選ぶ。 -/
theorem q9ut_gr0_sweep (u : q3rqCar) (hu : q3rqUnitMem u) :
    ∃ s : q3rqCar, (s = q3rqOne ∨ s = q3rqNeg q3rqOne) ∧ q9utIsNorm s ∧
      q9utUL 1 (q3rqMul u s) := by
  obtain h | h := q9ut_unit_res_pm u hu
  · refine ⟨q3rqOne, Or.inl rfl, q9ut_isNorm_one, ?_⟩
    have h0 : q9rfResL (q3rqAdd u (q3rqNeg q3rqOne)) = q9rfF3.zero := by
      rw [q9rf_resL_add, q9ut_resL_negone, h]
      exact q9rfF3.add_neg q9rfF3.one
    obtain ⟨k, hk⟩ := q9gn_resL_lambda_dvd (q3rqAdd u (q3rqNeg q3rqOne)) h0
    rw [q3rq_mul_one u]
    refine ⟨k, ?_⟩
    rw [hk, q9ut_lampow_one]
  · refine ⟨q3rqNeg q3rqOne, Or.inr rfl, q9ut_isNorm_neg_one, ?_⟩
    have h0 : q9rfResL (q3rqAdd (q3rqMul u (q3rqNeg q3rqOne)) (q3rqNeg q3rqOne))
        = q9rfF3.zero := by
      rw [q9rf_resL_add, q9rf_resL_mul, h, q9ut_resL_negone, q9ut_f3_negone_sq]
      exact q9rfF3.add_neg q9rfF3.one
    obtain ⟨k, hk⟩ := q9gn_resL_lambda_dvd
      (q3rqAdd (q3rqMul u (q3rqNeg q3rqOne)) (q3rqNeg q3rqOne)) h0
    refine ⟨k, ?_⟩
    rw [hk, q9ut_lampow_one]

/-- **q9ut-6b（★ a4・gr¹ 掃き）**: u ∈ U^{(1)}_λ（witness m）なら t ∈ {1, ζ₃, ζ₃²}
    （全て torsion ノルム）で u·t ∈ U^{(2)}_λ。gr¹ 剰余 res(m) の三分法で
    ζ₃ の gr¹ 剰余 −1（q9ut_resL_zetaC）を消す指数 d を選ぶ。 -/
theorem q9ut_gr1_sweep (u m : q3rqCar)
    (hm : q3rqAdd u (q3rqNeg q3rqOne) = q3rqMul (q3rqLamPow 1) m) :
    ∃ t : q3rqCar, (t = q3rqOne ∨ t = q3rqZeta ∨ t = q3rqZetaSq) ∧ q9utIsNorm t ∧
      q9utUL 2 (q3rqMul u t) := by
  have hu' : u = q3rqAdd q3rqOne (q3rqMul (q3rqLamPow 1) m) := by
    rw [← hm]
    exact (q9ut_one_add_shift u).symm
  obtain h0 | h1 | hn := q9ut_f3_tri (q9rfResL m)
  · refine ⟨q3rqOne, Or.inl rfl, q9ut_isNorm_one, ?_⟩
    rw [q3rq_mul_one u]
    exact q9ut_ul_deepen 1 u m hm h0
  · refine ⟨q3rqZeta, Or.inr (Or.inl rfl), q9ut_isNorm_zeta, ?_⟩
    refine q9ut_sweep_step 0 u q3rqZeta m q9utZetaC hu' q9ut_zeta_decomp ?_
    rw [h1, q9ut_resL_zetaC]
    exact q9rfF3.add_neg q9rfF3.one
  · refine ⟨q3rqZetaSq, Or.inr (Or.inr rfl), q9ut_isNorm_zetaSq, ?_⟩
    refine q9ut_sweep_step 0 u q3rqZetaSq m q9utZetaSqC hu' q9ut_zetaSq_decomp ?_
    rw [hn, q9ut_resL_zetaSqC]
    exact q9rfF3.neg_add q9rfF3.one

/-- **q9ut-6c（★ a5・gr² 掃き）**: u ∈ U^{(2)}_λ（witness m）なら f ∈ {1, 4, 16}
    （余核 transversal・**ノルムではない**）で u·f ∈ U^{(3)}_λ。
    4 の gr² 剰余 −1（4−1 = 3 = −λ² 厳密）を res(m) の三分法で消す。 -/
theorem q9ut_gr2_sweep (u m : q3rqCar)
    (hm : q3rqAdd u (q3rqNeg q3rqOne) = q3rqMul (q3rqLamPow 2) m) :
    ∃ f : q3rqCar, (f = q3rqOne ∨ f = q9rcFour ∨ f = q9rcFourSq) ∧
      q9utUL 3 (q3rqMul u f) := by
  have hu' : u = q3rqAdd q3rqOne (q3rqMul (q3rqLamPow 2) m) := by
    rw [← hm]
    exact (q9ut_one_add_shift u).symm
  obtain h0 | h1 | hn := q9ut_f3_tri (q9rfResL m)
  · refine ⟨q3rqOne, Or.inl rfl, ?_⟩
    rw [q3rq_mul_one u]
    exact q9ut_ul_deepen 2 u m hm h0
  · refine ⟨q9rcFour, Or.inr (Or.inl rfl), ?_⟩
    refine q9ut_sweep_step 1 u q9rcFour m (q3rqNeg q3rqOne) hu' q9ut_four_decomp ?_
    rw [h1, q9ut_resL_negone]
    exact q9rfF3.add_neg q9rfF3.one
  · refine ⟨q9rcFourSq, Or.inr (Or.inr rfl), ?_⟩
    refine q9ut_sweep_step 1 u q9rcFourSq m q9utC16 hu' q9ut_foursq_decomp ?_
    rw [hn, q9ut_resL_c16]
    exact q9rfF3.neg_add q9rfF3.one

/-! ## q9ut-7: a6——束ね（M4-a 主定理・embed 側 U^{(9)}_{π₉} 着地） -/

/-- embed(Y) − 1 = embed(Y − 1)（embed の加法・反数整合）。 -/
theorem q9ut_embed_sub_one (Y : q3rqCar) :
    q3kAdd (q3kEmbed Y) (q3kNeg q3kOne) = q3kEmbed (q3rqAdd Y (q3rqNeg q3rqOne)) := by
  rw [q9ps_kN_eq, q9rf_embed_add Y (q3rqNeg q3rqOne), ← q9ps_embed_neg q3rqOne,
      q3k_embed_one]

/-- **組立補題**: s·t がノルム（witness w）で u·s·t·f ∈ U^{(3)}_λ かつ f = φ(g) なら、
    u·N(w)·φ(g) は単数で embed 側 U^{(9)}_{π₉}（= λ-level 3）に入る。
    λ→π₉ の昇りは q9na_lam_ascent（embed(λ³·m) は π₉⁹ 可除）。 -/
theorem q9ut_assemble (u s t f : q3rqCar) (g : q9kdGCar)
    (hu : q3rqUnitMem u)
    (hsn : q9utIsNorm s) (htn : q9utIsNorm t)
    (hgf : q9rgPhi g = f) (hfu : q3rqUnitMem f)
    (h3 : q9utUL 3 (q3rqMul (q3rqMul (q3rqMul u s) t) f)) :
    ∃ g' : q9kdGCar, ∃ w : q3kCar, q3kUnitMem w ∧
      q3rqUnitMem (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g')) ∧
      q9nfUfilt 9 (q3kEmbed (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g'))) := by
  obtain ⟨w, hw, hwN⟩ := q9ut_isNorm_mul hsn htn
  have hE : q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)
      = q3rqMul (q3rqMul (q3rqMul u s) t) f := by
    rw [hwN, hgf, q3k_M_eq, q3rqRing.mul_assoc u s t]
  refine ⟨g, w, hw, ?_, ?_⟩
  · have hphi : q3rqUnitMem (q9rgPhi g) := by
      rw [hgf]
      exact hfu
    exact q3rq_unit_mul (q3rq_unit_mul hu hw) hphi
  · obtain ⟨m3, hm3⟩ := h3
    show q9wrDvd (q9nfPiPow 9)
      (q3kAdd (q3kEmbed (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)))
        (q3kNeg q3kOne))
    rw [q9ut_embed_sub_one (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)), hE]
    exact q9na_lam_ascent 3
      (q3rqAdd (q3rqMul (q3rqMul (q3rqMul u s) t) f) (q3rqNeg q3rqOne)) ⟨m3, hm3⟩

/-- **q9ut-7a（★★★ M4-a 主定理・tame/torsion 掃き出し）**:
    任意の実単数 u ∈ U_{L₂} に対し、Galois 元 g ∈ Gal(M/L₂) と単数 w ∈ U_M が存在して
    u·N(w)·φ(g) は単数かつ U^{(3)}_λ（embed 側 q9nfUfilt 9）に入る。
    すなわち U_{L₂} = ⟨torsion ノルム⟩·{4^c}·U^{(3)}_λ——tame 18 類のうち 6 類は
    torsion ノルムで打たれ、残る transversal は ⟨[4]⟩ = {1, 4, 16} の 3 類。
    **M3（T3-core: U^{(3)}_λ ⊆ N(U_M)）と合成すれば index ≤ 3 が出る**（M4-b・未達）。 -/
theorem q9ut_tame_decomp (u : q3rqCar) (hu : q3rqUnitMem u) :
    ∃ g : q9kdGCar, ∃ w : q3kCar, q3kUnitMem w ∧
      q3rqUnitMem (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)) ∧
      q9nfUfilt 9 (q3kEmbed (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g))) := by
  obtain ⟨s, hsor, hsn, hs1⟩ := q9ut_gr0_sweep u hu
  obtain ⟨m1, hm1⟩ := hs1
  obtain ⟨t, htor, htn, ht2⟩ := q9ut_gr1_sweep (q3rqMul u s) m1 hm1
  obtain ⟨m2, hm2⟩ := ht2
  obtain ⟨f, hfor, hf3⟩ := q9ut_gr2_sweep (q3rqMul (q3rqMul u s) t) m2 hm2
  obtain hf | hf | hf := hfor
  · refine q9ut_assemble u s t f q9kdGCar.e hu hsn htn ?_ ?_ hf3
    · rw [hf]
      rfl
    · rw [hf]
      exact q3rq_unit_one
  · refine q9ut_assemble u s t f q9kdGCar.s hu hsn htn ?_ ?_ hf3
    · rw [hf]
      rfl
    · rw [hf]
      exact q9rc_four_unit
  · refine q9ut_assemble u s t f q9kdGCar.s2 hu hsn htn ?_ ?_ hf3
    · rw [hf]
      rfl
    · rw [hf]
      exact q3rq_unit_mul q9rc_four_unit q9rc_four_unit

/-- **q9ut-7b: tame 商 ≅ ℤ/3 の element-level 束ね**——
    上界側 infrastructure（掃き出し完全被覆: 任意の単数は torsion ノルム × 4^c を
    法として U^{(3)}_λ）と下界側（{[1],[4],[16]} pairwise 相異 = q9rc_z3_injects）。
    **注意（正直な限定 1・2）**: これは「tame 部の transversal がちょうど ⟨[4]⟩」の
    element-level 表現であって [U_{L₂}:N(U_M)] = 3 そのものではない（M3 + M4-b 待ち）。 -/
theorem q9ut_tame_z3 :
    (∀ u : q3rqCar, q3rqUnitMem u →
      ∃ g : q9kdGCar, ∃ w : q3kCar, q3kUnitMem w ∧
        q3rqUnitMem (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)) ∧
        q9nfUfilt 9 (q3kEmbed (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)))) ∧
    (q9rcCongMod q3rqOne q9rcFourCube ∧
      (¬ q9rcCongMod q3rqOne q9rcFour) ∧
      (¬ q9rcCongMod q3rqOne q9rcFourSq) ∧
      (¬ q9rcCongMod q9rcFour q9rcFourSq)) :=
  ⟨q9ut_tame_decomp, q9rc_z3_injects⟩

/-! ## q9ut-8: capstone -/

/-- **q9ut-8a: tame/torsion 掃き出しデータ**（T3-M4-a）——𝔽₃ 三分法・unit⟹res≠0・
    torsion ノルム帳簿・gr⁰/gr¹/gr² 掃き出し・主定理・ℤ/3 transversal を束ねる。 -/
structure Q3UnitTameDecompData where
  /-- 𝔽₃ 三分法（a1）。 -/
  f3_tri : ∀ r : q9rfF3.carrier,
    r = q9rfF3.zero ∨ r = q9rfF3.one ∨ r = q9rfF3.neg q9rfF3.one
  /-- unit ⟹ res_L ≠ 0（a1）。 -/
  unit_res_ne : ∀ u : q3rqCar, q3rqUnitMem u → q9rfResL u ≠ q9rfF3.zero
  /-- −1 = N(−1)（a2）。 -/
  neg_one_norm : q9utIsNorm (q3rqNeg q3rqOne)
  /-- ζ₃ = N(ζ₉)（a2）。 -/
  zeta_norm : q9utIsNorm q3rqZeta
  /-- ζ₃² = N(ζ₉²)（a2）。 -/
  zetaSq_norm : q9utIsNorm q3rqZetaSq
  /-- gr⁰ 掃き（a3）。 -/
  gr0 : ∀ u : q3rqCar, q3rqUnitMem u →
    ∃ s : q3rqCar, (s = q3rqOne ∨ s = q3rqNeg q3rqOne) ∧ q9utIsNorm s ∧
      q9utUL 1 (q3rqMul u s)
  /-- 主定理（a6）: u·N(w)·φ(g) ∈ U^{(3)}_λ（単数性込み・embed 側 Ufilt 9）。 -/
  tame_decomp : ∀ u : q3rqCar, q3rqUnitMem u →
    ∃ g : q9kdGCar, ∃ w : q3kCar, q3kUnitMem w ∧
      q3rqUnitMem (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)) ∧
      q9nfUfilt 9 (q3kEmbed (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)))
  /-- transversal {[1],[4],[16]} pairwise 相異（下界側・q9rc 消費）。 -/
  transversal_distinct :
    q9rcCongMod q3rqOne q9rcFourCube ∧
      (¬ q9rcCongMod q3rqOne q9rcFour) ∧
      (¬ q9rcCongMod q3rqOne q9rcFourSq) ∧
      (¬ q9rcCongMod q9rcFour q9rcFourSq)

/-- **q9ut-8b: 見出し実例**——実 O_{L₂} = q3rqRing・実 O_M = q3kRing 上の
    tame/torsion 掃き出し。 -/
def q9ut_data : Q3UnitTameDecompData where
  f3_tri := q9ut_f3_tri
  unit_res_ne := q9ut_unit_resL_ne
  neg_one_norm := q9ut_isNorm_neg_one
  zeta_norm := q9ut_isNorm_zeta
  zetaSq_norm := q9ut_isNorm_zetaSq
  gr0 := q9ut_gr0_sweep
  tame_decomp := q9ut_tame_decomp
  transversal_distinct := q9rc_z3_injects

/-- **q9ut-8c: tame/torsion 掃き出しの存在**（B2 T3-M4-a）。 -/
theorem q9ut_exists : Nonempty Q3UnitTameDecompData := ⟨q9ut_data⟩

end IUT
