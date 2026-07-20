/-
  IUT/Q3NormSurjPeelBase.lean — 柱B・B2 T3-M1: **基底 j=3 の単一 peel 段の剰余整合全射性**
    （実 π₉ ノルム展開の level-9 先頭剰余 res_M : 𝔽₃ への全射・q9ns_tr_pi5 の消費）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（T3-core 上界機構の基底 peel の実現）。
  q9ns_tr_pi5（Tr(π₉⁵a) = π₉⁹·(w⁻¹u₆·embed((π₉²(wa))₀)) の**厳密等式**）の上に、
  N(1+π₉⁵a)−1 の level-9 先頭剰余（res_M : O_M ↠ 𝔽₃）が
  **c ↦ a の choice-free 𝔽₃ 切断（q9nsCorr/q9nsLiftInt）で全射**であることを本物で建てる。
  toy 主語なし——主語は実 O_M = q3kRing・実トレース q9nfTr・実残余体 𝔽₃・実 π₉ フィルトレーション。

  complete_pct 影響: **B2 base-case peel（監査次第・予測 +0.01〜0.03）**。本ファイルは
  T3-M1 の**基底 j=3 の単一 peel 段の存在証明**（∀c ∃a, level-9 先頭剰余 = c）を厳密等式
  q9ns_tr_pi5 + tail 深さ（q9nf_e2_dvd/q9nf_normterm_dvd の j=3）+ res_M 環準同型で閉じる。
  一般 j・逐次近似・完備性は未着手のため単体の complete_pct は監査次第（過大主張しない）。

  真水（本物へ昇格・新規建設）:
   * q9np_resM_unfold — res_M x = resL(x₀)+(resL(x₁)+resL(x₂))（res_M 定義の展開）。
   * q9np_resM_pi9（res_M(π₉) = 0）— π₉=(−1,1,0) の座標剰余の相殺。
   * q9np_winv_u6_w（w⁻¹·u₆·w = u₆）・q9np_u6_w_w（u₆·w·w = −1）— 実単数 w/u₆ の消去恒等式。
   * q9np_resM_u6（★ res_M(u₆) = −1）— u₆·w² = −1 と res_M(w)² = 1 の合成。
   * q9np_resM_L（★ res_M(先頭係数 L(a)) = res_M(u₆)·res_M(a)）— q9gn_resL_t1 + λ 再帰先頭項。
   * q9np_resM_corr（res_M(q9nsCorr r) = r）— choice-free 𝔽₃ 切断の剰余整合。
   * q9np_peel_base_step（★ 任意 a で N(1+π₉⁵a)−1 = π₉⁹·b・res_M(b) = res_M(u₆)·res_M(a)）。
   * q9np_peel_base（★★ 基底 peel 全射性）— ∀c ∃a, level-9 先頭剰余 = c。

  正直な限定（§4 規約により消さない・弱めない・q9ns/q9nf/q9gn/q9ps/q9rf/q3k/q3rq 継承の上に追記のみ）:
  1. **基底 j=3 のみ**（一般 j は未着手・T3-M1 の残段）。q9ns_tr_pi5 が j=3 の閉形式であり
     一般 j の λ-再帰は本ファイルでは配線しない。
  2. **単一 peel 段のみ**であって U^{(3)}⊆N の全体ではない（後者は T3-M2 逐次近似 +
     T3-M3 完備性＝無限積を要する）。「level-9 先頭剰余が c」は 1 段の剰余整合であり
     「u はノルム」は主張しない。
  3. 全射性は **level-9 先頭剰余（res_M∘先頭係数）への全射**であり、N の値そのものの
     全射ではない（tail は level ≥ 10 で res_M に寄与しないことを q9nf_e2_dvd/normterm で使うが、
     厳密等式 N(x)=u は M3 本体）。
  4. q9ns/q9nf/q9gn/q9ps/q9rf/q3k/q3rq の正直限定を全継承（可除性形式・v_M 不使用・
     O_M と M^× のみ・体化なし・σ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・
     兄弟担体・拡大 1 個 M/L₂/ℚ₃）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無・𝔽₃ 切断は
  q9nsLiftInt の Quot.lift ベースで choice-free）。#print axioms は [propext, Quot.sound] のみ。
  禁止タクティク不使用。
-/
import IUT.Q3NormSurjGraded

namespace IUT

/-! ## q9np-0: res_M の展開と π₉ の剰余 -/

/-- **q9np-0a: res_M x = resL(x₀) + (resL(x₁) + resL(x₂))**（res_M 定義の resL 展開）。 -/
theorem q9np_resM_unfold (x : q3kCar) :
    q9rfResM x
      = q9rfF3.add (q9rfResL x.1) (q9rfF3.add (q9rfResL x.2.1) (q9rfResL x.2.2)) := by
  show q9rfResL (q3rqAdd x.1 (q3rqAdd x.2.1 x.2.2))
      = q9rfF3.add (q9rfResL x.1) (q9rfF3.add (q9rfResL x.2.1) (q9rfResL x.2.2))
  rw [q9rf_resL_add, q9rf_resL_add]

/-- resL(0) = 0（第 1 座標の res₃(0)）。 -/
theorem q9np_resL_zero : q9rfResL q3rqZero = q9rfF3.zero := by
  show q9rfRes3 q3rqZero.1 = q9rfF3.zero
  exact q9rf_res3_zero

/-- **q9np-0b: res_M(π₉) = 0**（π₉ = (−1,1,0)・剰余 −1+1+0 = 0）。 -/
theorem q9np_resM_pi9 : q9rfResM q9psPi9 = q9rfF3.zero := by
  rw [q9ps_pi9_coords]
  show q9rfResL (q3rqAdd (q3rqNeg q3rqOne) (q3rqAdd q3rqOne q3rqZero)) = q9rfF3.zero
  rw [q9rf_resL_add, q9rf_resL_add, q9gn_resL_neg, q9gn_resL_one, q9np_resL_zero,
      q9rfF3.add_zero q9rfF3.one, q9rfF3.neg_add q9rfF3.one]

/-! ## q9np-1: 実単数 w / u₆ の消去恒等式 -/

/-- w⁻¹·w = 1（q9ps_w_inv_mul を可換に）。 -/
theorem q9np_winv_w : q3kRing.mul q9psWinv q9psW = q3kRing.one := by
  have h := q9ps_w_inv_mul
  rw [q3k_kM_eq, q9ps_kO_eq] at h
  rw [q3kRing.mul_comm q9psWinv q9psW]; exact h

/-- **q9np-1a: (w⁻¹·u₆)·w = u₆**（可換環で w⁻¹·w が相殺）。 -/
theorem q9np_winv_u6_w :
    q3kMul (q3kMul q9psWinv q9psU6) q9psW = q9psU6 := by
  rw [q3k_kM_eq]
  rw [q3kRing.mul_assoc q9psWinv q9psU6 q9psW,
      q3kRing.mul_comm q9psU6 q9psW,
      ← q3kRing.mul_assoc q9psWinv q9psW q9psU6,
      q9np_winv_w, q3kRing.one_mul q9psU6]

/-- **q9np-1b: (u₆·w)·w = −1**（u₆ = −(w⁻¹)²・(w⁻¹·w)² = 1）。 -/
theorem q9np_u6_w_w :
    q3kMul (q3kMul q9psU6 q9psW) q9psW = q3kNeg q3kOne := by
  show q3kMul (q3kMul (q3kNeg (q3kMul q9psWinv q9psWinv)) q9psW) q9psW = q3kNeg q3kOne
  rw [q3k_kM_eq, q9ps_kN_eq, q9ps_kO_eq,
      q3kRing.neg_mul (q3kRing.mul q9psWinv q9psWinv) q9psW,
      q3kRing.neg_mul (q3kRing.mul (q3kRing.mul q9psWinv q9psWinv) q9psW) q9psW]
  apply congrArg q3kRing.neg
  rw [q3kRing.mul_assoc (q3kRing.mul q9psWinv q9psWinv) q9psW q9psW,
      q3kRing.mul_mul_mul_comm q9psWinv q9psWinv q9psW q9psW,
      q9np_winv_w, q3kRing.mul_one q3kRing.one]

/-! ## q9np-2: 𝔽₃ の平方恒等式と res_M(−1) / res_M(u₆) -/

/-- 𝔽₃: (1+1)·(1+1) = 1（2·2 = 4 ≡ 1 mod 3）。 -/
theorem q9np_f3_two_sq :
    q9rfF3.mul (q9rfF3.add q9rfF3.one q9rfF3.one)
        (q9rfF3.add q9rfF3.one q9rfF3.one) = q9rfF3.one := by
  show Quot.mk (modCong 3).rel ((1 + 1) * (1 + 1)) = Quot.mk (modCong 3).rel 1
  apply Quot.sound
  show ((3 : Nat) : Int) ∣ (1 + 1) * (1 + 1) - 1
  exact ⟨1, by omega⟩

/-- 𝔽₃: (−1)·(−1) = 1。 -/
theorem q9np_f3_neg1_sq :
    q9rfF3.mul (q9rfF3.neg q9rfF3.one) (q9rfF3.neg q9rfF3.one) = q9rfF3.one := by
  rw [q9rfF3.neg_mul q9rfF3.one (q9rfF3.neg q9rfF3.one),
      q9rfF3.one_mul (q9rfF3.neg q9rfF3.one), q9rfF3.neg_neg]

/-- res_M(−1_M) = −1（−1_M = embed(−1)・resL(−1) = −resL(1)）。 -/
theorem q9np_resM_negone : q9rfResM (q3kNeg q3kOne) = q9rfF3.neg q9rfF3.one := by
  rw [q9ps_n1_embed, q9rf_resM_embed, q9gn_resL_neg, q9gn_resL_one]

/-- **q9np-2a（★ res_M(u₆) = −1）**（u₆·w² = −1・res_M(w)² = (1+1)² = 1 で割る）。 -/
theorem q9np_resM_u6 : q9rfResM q9psU6 = q9rfF3.neg q9rfF3.one := by
  have h1 : q9rfResM (q3kMul (q3kMul q9psU6 q9psW) q9psW) = q9rfResM (q3kNeg q3kOne) :=
    congrArg q9rfResM q9np_u6_w_w
  rw [q9rf_resM_mul, q9rf_resM_mul, q9ns_resM_w, q9np_resM_negone,
      q9rfF3.mul_assoc (q9rfResM q9psU6)
        (q9rfF3.add q9rfF3.one q9rfF3.one) (q9rfF3.add q9rfF3.one q9rfF3.one),
      q9np_f3_two_sq, q9rfF3.mul_one (q9rfResM q9psU6)] at h1
  exact h1

/-! ## q9np-3: 先頭係数 L(a) の剰余（★ λ-再帰先頭項の 𝔽₃ 挙動） -/

/-- **q9np-3a（★）: res_M(L(a)) = res_M(u₆)·res_M(a)**
    （L(a) = w⁻¹·u₆·embed((π₉²(wa))₀)・q9gn_resL_t1 で resL((π₉²(wa))₀) = res_M(wa)・
    w⁻¹·u₆·w = u₆ で先頭単数を u₆ に集約）。 -/
theorem q9np_resM_L (a : q3kCar) :
    q9rfResM (q3kMul (q3kMul q9psWinv q9psU6)
        (q3kEmbed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1))
      = q9rfF3.mul (q9rfResM q9psU6) (q9rfResM a) := by
  rw [q9rf_resM_mul (q3kMul q9psWinv q9psU6)
        (q3kEmbed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1),
      q9rf_resM_embed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1,
      q9gn_resL_t1 (q3kMul q9psW a),
      ← q9np_resM_unfold (q3kMul q9psW a),
      q9rf_resM_mul q9psW a,
      ← q9rfF3.mul_assoc (q9rfResM (q3kMul q9psWinv q9psU6)) (q9rfResM q9psW) (q9rfResM a),
      ← q9rf_resM_mul (q3kMul q9psWinv q9psU6) q9psW,
      q9np_winv_u6_w]

/-! ## q9np-4: choice-free 𝔽₃ 切断からの補正元の剰余 -/

/-- **q9np-4a: res_M(q9nsCorr r) = r**（r%3 の Quot.lift 切断・q9ns_sect_section）。 -/
theorem q9np_resM_corr (r : q9rfF3.carrier) : q9rfResM (q9nsCorr r) = r := by
  show q9rfResM (q3kEmbed (((toZp 3).map (q9nsLiftInt r), z3.zero) : q3rqCar)) = r
  rw [q9rf_resM_embed]
  exact q9ns_sect_section r

/-! ## q9np-5: 純環の π₉⁹ 括り出し補助 -/

/-- **π₉⁹·L + (π₉⁹π₉·e + π₉⁹π₉·nt) = π₉⁹·(L + (π₉·e + π₉·nt))**（分配 + 結合）。 -/
theorem q9np_dist9 (p q L e nt : q3kCar) :
    q3kAdd (q3kMul p L)
        (q3kAdd (q3kMul (q3kMul p q) e) (q3kMul (q3kMul p q) nt))
      = q3kMul p (q3kAdd L (q3kAdd (q3kMul q e) (q3kMul q nt))) := by
  rw [q3k_kM_eq, q9nf_kA_eq,
      q3kRing.left_distrib p L (q3kRing.add (q3kRing.mul q e) (q3kRing.mul q nt)),
      q3kRing.left_distrib p (q3kRing.mul q e) (q3kRing.mul q nt),
      ← q3kRing.mul_assoc p q e, ← q3kRing.mul_assoc p q nt]

/-! ## q9np-6: ★ 基底 j=3 の単一 peel 段（任意 a・閉形式 b と剰余） -/

/-- **q9np-6a（★ 基底 peel 段）: 任意 a で N(1+π₉⁵a)−1 = π₉⁹·b かつ
    res_M(b) = res_M(u₆)·res_M(a)**。tail（E₂・ノルム 3 次項）は level ≥ 10 で
    π₉⁹·(π₉·…) に押し込まれ res_M に寄与しないので、先頭 Tr（q9ns_tr_pi5 の厳密等式）が
    level-9 先頭剰余を支配する。 -/
theorem q9np_peel_base_step (a : q3kCar) :
    ∃ b : q3kCar,
      q3kAdd (q3kEmbed (q3kNormBase (q3kAdd q3kOne (q3kMul (q9nfPiPow 5) a))))
          (q3kNeg q3kOne)
        = q3kMul (q9nfPiPow 9) b
      ∧ q9rfResM b = q9rfF3.mul (q9rfResM q9psU6) (q9rfResM a) := by
  have hE2 : q9wrDvd (q9nfPiPow 10) (q9nfE2 (q3kMul (q9nfPiPow 5) a)) :=
    q9nf_e2_dvd 5 (q3kMul (q9nfPiPow 5) a) ⟨a, rfl⟩
  have hNT : q9wrDvd (q9nfPiPow 10)
      (q3kEmbed (q3kNormBase (q3kMul (q9nfPiPow 5) a))) :=
    q9nf_dvd_of_le (show (10 : Nat) ≤ 5 + (5 + 5) by omega)
      (q9nf_normterm_dvd 5 (q3kMul (q9nfPiPow 5) a) ⟨a, rfl⟩)
  obtain ⟨e2w, he2⟩ := hE2
  obtain ⟨ntw, hnt⟩ := hNT
  have hp10 : q9nfPiPow 10 = q3kMul (q9nfPiPow 9) q9psPi9 := by
    have h := q9nf_pipow_add 9 1
    rw [q9nf_pipow1_eq] at h
    exact h
  refine ⟨q3kAdd (q3kMul (q3kMul q9psWinv q9psU6)
      (q3kEmbed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1))
      (q3kAdd (q3kMul q9psPi9 e2w) (q3kMul q9psPi9 ntw)), ?_, ?_⟩
  · rw [q9nf_norm_expand (q3kMul (q9nfPiPow 5) a), q9nf_one_add_cancel,
        q9ns_tr_pi5 a, he2, hnt, hp10]
    exact q9np_dist9 (q9nfPiPow 9) q9psPi9
      (q3kMul (q3kMul q9psWinv q9psU6)
        (q3kEmbed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1)) e2w ntw
  · rw [q9rf_resM_add, q9rf_resM_add, q9np_resM_L a, q9rf_resM_mul, q9rf_resM_mul,
        q9np_resM_pi9, q9rfF3.zero_mul, q9rfF3.zero_mul, q9rfF3.add_zero,
        q9rfF3.add_zero]

/-! ## q9np-7: ★★ 基底 peel の 𝔽₃ 全射性（剰余整合） -/

/-- **q9np-7a（★★ 基底 peel 全射性）: ∀ c : 𝔽₃, ∃ a b,
    N(1+π₉⁵a)−1 = π₉⁹·b ∧ res_M(b) = c**。
    a := q9nsCorr((−1)·c)（choice-free 𝔽₃ 切断）とすると
    res_M(b) = res_M(u₆)·res_M(a) = (−1)·((−1)·c) = c。基底 j=3 の単一 peel 段の
    level-9 先頭剰余が 𝔽₃ 全体を被覆する（正直な限定: 一般 j・完備性は未着手）。 -/
theorem q9np_peel_base (c : q9rfF3.carrier) :
    ∃ a : q3kCar, ∃ b : q3kCar,
      q3kAdd (q3kEmbed (q3kNormBase (q3kAdd q3kOne (q3kMul (q9nfPiPow 5) a))))
          (q3kNeg q3kOne)
        = q3kMul (q9nfPiPow 9) b
      ∧ q9rfResM b = c := by
  obtain ⟨b, heq, hres⟩ :=
    q9np_peel_base_step (q9nsCorr (q9rfF3.mul (q9rfF3.neg q9rfF3.one) c))
  refine ⟨q9nsCorr (q9rfF3.mul (q9rfF3.neg q9rfF3.one) c), b, heq, ?_⟩
  rw [hres, q9np_resM_u6, q9np_resM_corr,
      ← q9rfF3.mul_assoc (q9rfF3.neg q9rfF3.one) (q9rfF3.neg q9rfF3.one) c,
      q9np_f3_neg1_sq, q9rfF3.one_mul]

/-! ## q9np-8: capstone -/

/-- **q9np-8a: 基底 peel 全射性データ**（level-9 先頭係数の剰余・全射性）。 -/
structure Q3NormSurjPeelBaseData where
  /-- 先頭係数 L(a) の剰余 = res_M(u₆)·res_M(a)。 -/
  resM_L : ∀ a : q3kCar,
    q9rfResM (q3kMul (q3kMul q9psWinv q9psU6)
        (q3kEmbed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1))
      = q9rfF3.mul (q9rfResM q9psU6) (q9rfResM a)
  /-- res_M(u₆) = −1（先頭単数の剰余）。 -/
  resM_u6 : q9rfResM q9psU6 = q9rfF3.neg q9rfF3.one
  /-- 基底 peel の level-9 先頭剰余は 𝔽₃ 全射。 -/
  peel_surj : ∀ c : q9rfF3.carrier, ∃ a : q3kCar, ∃ b : q3kCar,
      q3kAdd (q3kEmbed (q3kNormBase (q3kAdd q3kOne (q3kMul (q9nfPiPow 5) a))))
          (q3kNeg q3kOne)
        = q3kMul (q9nfPiPow 9) b
      ∧ q9rfResM b = c

/-- **q9np-8b: 見出し実例** — 実 O_M = q3kRing 上の基底 j=3 peel 全射性。 -/
def q9np_data : Q3NormSurjPeelBaseData where
  resM_L := q9np_resM_L
  resM_u6 := q9np_resM_u6
  peel_surj := q9np_peel_base

/-- **q9np-8c: 基底 peel 全射性の存在**（T3-M1 基底 j=3 の実 Lean 化）。 -/
theorem q9np_exists : Nonempty Q3NormSurjPeelBaseData := ⟨q9np_data⟩

end IUT
