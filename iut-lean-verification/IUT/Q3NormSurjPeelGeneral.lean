/-
  IUT/Q3NormSurjPeelGeneral.lean — 柱B・B2 T3-M1: **一般 level j≥3 の単一 peel 段の
    剰余整合全射性**（λ-再帰による基底 j=3 の全 level への持ち上げ・T3-M1 general-j 完了）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（T3-core 上界機構の per-level peel を
  基底 j=3 から**全 level j≥3** へ一般化）。q9ns_lambda_rec（λ-再帰・厳密等式
  Tr(π₉^{i+3}a) = embed(λ)·Tr(π₉^i·(w·a))）を (j−3) 回適用して level-3j 先頭項閉形式
  Tr(π₉^{3j−4}a) = π₉^{3j}·Lead_j(a) を帰納で建て、res_M(Lead_j(a)) = res_M(u₆)·res_M(a)
  が**全 j で不変**（1 段ごとに res_M(w⁻¹)·res_M(w)=1 で交代 (−1)² が相殺）であることを
  厳密に証明する。toy 主語なし——主語は実 O_M = q3kRing・実トレース q9nfTr・実 π₉
  フィルトレーション・実残余体 𝔽₃。基底 q9np_peel_base（j=3）を実 λ-再帰で全 level に昇格。

  complete_pct 影響: **B2 T3-M1 general-j（監査次第・予測 +0.02〜0.05）**。基底 1 段のみ
  だった peel 全射性を**全 level j≥3** に持ち上げる——T3-M2 逐次近似（level を跨いだ合成）の
  唯一の per-level 入力を全レベルで供給する鍵。単体では単一 peel 段の per-level 剰余全射で
  あり、逐次近似・完備性は未着手のため前進幅は監査次第（過大主張しない）。

  真水（本物へ昇格・新規建設）:
   * q9npg_tr_lead（★★ 一般 level 先頭項閉形式・k 帰納）— ∀ a ∃ b,
     Tr(π₉^{3k+5}a) = π₉^{3k+9}·b ∧ res_M(b) = res_M(u₆)·res_M(a)。λ-再帰 1 段
     （i=3k+5）+ embed(λ)=π₉³·w⁻¹ の集約 + res_M(w⁻¹)·res_M(w)=1 の相殺で閉じる。
     **基底 q9ns_tr_pi5/q9np_resM_L を k=0 に、λ-再帰を段に**据えた実帰納。
   * q9npg_resM_winv_w（res_M(w⁻¹)·res_M(w) = 1）— w⁻¹·w=1（q9np_winv_w）+ res_M(1)=1。
   * q9npg_tr_lead_j（★ j≥3 形への橋渡し）— 3j−4=3k+5・3j=3k+9（k=j−3・omega）。
   * q9npg_peel_step（★ 一般 j 単一 peel 段）— 任意 a で N(1+π₉^{3j−4}a)−1 = π₉^{3j}·b・
     res_M(b) = res_M(u₆)·res_M(a)。tail（E₂・ノルム 3 次項）は q9ns_e2_deep/normterm_deep で
     level ≥ 3j+1 に落ち res_M に寄与しない（q9np_resM_pi9 の一般 j 版）。
   * q9npg_peel_general（★★ 一般 j peel 全射性）— ∀ j≥3 ∀c∈𝔽₃ ∃a b, level-3j 先頭剰余 = c。
     a := q9nsCorr((−1)·c)（choice-free 𝔽₃ 切断）で res_M(b) = (−1)·((−1)·c) = c。

  正直な限定（§4 規約により消さない・弱めない・q9ns/q9np/q9nf/q9gn/q9ps/q9rf/q3k/q3rq
  継承の上に追記のみ）:
  1. **依然として level ごとの単一 peel 段**（全 j に対して各 1 段）。level を跨いだ**合成**
     （逐次近似）= T3-M2 は未着手・本ファイルはその per-level 入力を全 j で供給するのみ。
  2. 全射性は **level-3j 先頭剰余（res_M∘先頭係数）への全射**であり、N の値そのものの
     全射（＝厳密ノルム値）ではない（M3 本体）。tail は level ≥ 3j+1 で res_M に非寄与。
  3. U^{(3)}⊆N の全体・index≤3 の結論は未主張（T3-M2 逐次近似 + T3-M3 完備性＝無限積 +
     T3-M4 を要する）。「level-3j 先頭剰余が c」は 1 段の剰余整合。
  4. q9ns/q9np/q9nf/q9gn/q9ps/q9rf/q3k/q3rq の正直限定を全継承（可除性形式・v_M 不使用・
     O_M と M^× のみ・体化なし・σ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・
     兄弟担体・拡大 1 個 M/L₂/ℚ₃）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無・𝔽₃ 切断は
  q9nsLiftInt の Quot.lift ベースで choice-free・omega は Int/Nat atom 目標のみ）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3NormSurjPeelBase

namespace IUT

/-! ## q9npg-0: res_M(1) = 1 と res_M(w⁻¹)·res_M(w) = 1（交代の相殺） -/

/-- **q9npg-0a: res_M(1_M) = 1**（1_M = embed(1)・resL(1) = 1）。 -/
theorem q9npg_resM_one : q9rfResM q3kOne = q9rfF3.one := by
  rw [← q3k_embed_one, q9rf_resM_embed, q9gn_resL_one]

/-- **q9npg-0b（★ 交代の相殺）: res_M(w⁻¹)·res_M(w) = 1**。
    w⁻¹·w = 1（q9np_winv_w）と res_M の乗法性・res_M(1)=1 の合成。
    λ-再帰 1 段ごとに現れる (−1)·(−1) = 1 の相殺の残余レベル実測。 -/
theorem q9npg_resM_winv_w :
    q9rfF3.mul (q9rfResM q9psWinv) (q9rfResM q9psW) = q9rfF3.one := by
  rw [← q9rf_resM_mul q9psWinv q9psW, q3k_kM_eq, q9np_winv_w, ← q9ps_kO_eq]
  exact q9npg_resM_one

/-! ## q9npg-1: ★★ 一般 level 先頭項閉形式（k 帰納・λ-再帰の全 level 実現） -/

/-- **q9npg-1a（★★ 一般 level 先頭項閉形式）**: ∀ a ∃ b,
    Tr(π₉^{3k+5}·a) = π₉^{3k+9}·b ∧ res_M(b) = res_M(u₆)·res_M(a)。
    k=0 は基底閉形式 q9ns_tr_pi5 + q9np_resM_L（level-9）。段 k→k+1 は λ-再帰 1 段
    （i=3k+5）で embed(λ) を外へ括り、embed(λ)=π₉³·w⁻¹ を π₉³ に集約して level を +3、
    res は res_M(w⁻¹)·(res_M(u₆)·(res_M(w)·res_M(a))) = res_M(u₆)·res_M(a)（相殺）へ。
    j=k+3 で index 3k+5 = 3j−4・level 3k+9 = 3j。 -/
theorem q9npg_tr_lead (k : Nat) : ∀ a : q3kCar,
    ∃ b : q3kCar,
      q9nfTr (q3kMul (q9nfPiPow (3 * k + 5)) a) = q3kMul (q9nfPiPow (3 * k + 9)) b
      ∧ q9rfResM b = q9rfF3.mul (q9rfResM q9psU6) (q9rfResM a) := by
  induction k with
  | zero =>
    intro a
    refine ⟨q3kMul (q3kMul q9psWinv q9psU6)
        (q3kEmbed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1), ?_, ?_⟩
    · show q9nfTr (q3kMul (q9nfPiPow 5) a)
          = q3kMul (q9nfPiPow 9)
              (q3kMul (q3kMul q9psWinv q9psU6)
                (q3kEmbed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1))
      exact q9ns_tr_pi5 a
    · exact q9np_resM_L a
  | succ k ih =>
    intro a
    obtain ⟨b', hb'eq, hb'res⟩ := ih (q3kMul q9psW a)
    refine ⟨q3kMul q9psWinv b', ?_, ?_⟩
    · show q9nfTr (q3kMul (q9nfPiPow (3 * k + 5 + 3)) a)
          = q3kMul (q9nfPiPow (3 * k + 9 + 3)) (q3kMul q9psWinv b')
      rw [q9ns_lambda_rec (3 * k + 5) a, hb'eq, q9nf_embed_lambda,
          q9nf_pipow_add (3 * k + 9) 3, q3k_kM_eq,
          q3kRing.mul_mul_mul_comm (q9nfPiPow 3) q9psWinv (q9nfPiPow (3 * k + 9)) b',
          q3kRing.mul_comm (q9nfPiPow 3) (q9nfPiPow (3 * k + 9))]
    · rw [q9rf_resM_mul q9psWinv b', hb'res, q9rf_resM_mul q9psW a,
          q9rfF3.mul_left_comm (q9rfResM q9psWinv) (q9rfResM q9psU6)
            (q9rfF3.mul (q9rfResM q9psW) (q9rfResM a)),
          ← q9rfF3.mul_assoc (q9rfResM q9psWinv) (q9rfResM q9psW) (q9rfResM a),
          q9npg_resM_winv_w, q9rfF3.one_mul (q9rfResM a)]

/-! ## q9npg-2: ★ j≥3 形への橋渡し（3j−4 = 3k+5・3j = 3k+9・k=j−3） -/

/-- **q9npg-2a（★ j 形の先頭項閉形式）**: 任意 j≥3・a で ∃ b,
    Tr(π₉^{3j−4}·a) = π₉^{3j}·b ∧ res_M(b) = res_M(u₆)·res_M(a)。
    k := j−3 で q9npg_tr_lead を呼び、Nat 指数 3j−4 = 3k+5・3j = 3k+9 を omega で橋渡し。 -/
theorem q9npg_tr_lead_j (j : Nat) (hj : 3 ≤ j) (a : q3kCar) :
    ∃ b : q3kCar,
      q9nfTr (q3kMul (q9nfPiPow (3 * j - 4)) a) = q3kMul (q9nfPiPow (3 * j)) b
      ∧ q9rfResM b = q9rfF3.mul (q9rfResM q9psU6) (q9rfResM a) := by
  obtain ⟨k, hk⟩ := Nat.le.dest hj
  have e1 : 3 * j - 4 = 3 * k + 5 := by omega
  have e2 : 3 * j = 3 * k + 9 := by omega
  obtain ⟨b, heq, hres⟩ := q9npg_tr_lead k a
  refine ⟨b, ?_, hres⟩
  rw [e1, e2]
  exact heq

/-! ## q9npg-3: ★ 一般 j の単一 peel 段（任意 a・閉形式 b と剰余） -/

/-- **q9npg-3a（★ 一般 j peel 段）**: 任意 j≥3・a で N(1+π₉^{3j−4}a)−1 = π₉^{3j}·b かつ
    res_M(b) = res_M(u₆)·res_M(a)。tail（E₂・ノルム 3 次項）は q9ns_e2_deep/q9ns_normterm_deep で
    level ≥ 3j+1 = π₉^{3j}·(π₉·…) に押し込まれ res_M に寄与しない（q9np_resM_pi9 の一般 j 版）。
    先頭 Tr（q9npg_tr_lead_j の閉形式）が level-3j 先頭剰余を支配する。 -/
theorem q9npg_peel_step (j : Nat) (hj : 3 ≤ j) (a : q3kCar) :
    ∃ b : q3kCar,
      q3kAdd (q3kEmbed (q3kNormBase (q3kAdd q3kOne (q3kMul (q9nfPiPow (3 * j - 4)) a))))
          (q3kNeg q3kOne)
        = q3kMul (q9nfPiPow (3 * j)) b
      ∧ q9rfResM b = q9rfF3.mul (q9rfResM q9psU6) (q9rfResM a) := by
  obtain ⟨tb, hteq, htres⟩ := q9npg_tr_lead_j j hj a
  obtain ⟨e2w, he2⟩ := q9ns_e2_deep j hj a
  obtain ⟨ntw, hnt⟩ := q9ns_normterm_deep j hj a
  have hp : q9nfPiPow (3 * j + 1) = q3kMul (q9nfPiPow (3 * j)) q9psPi9 := by
    have h := q9nf_pipow_add (3 * j) 1
    rw [q9nf_pipow1_eq] at h
    exact h
  refine ⟨q3kAdd tb (q3kAdd (q3kMul q9psPi9 e2w) (q3kMul q9psPi9 ntw)), ?_, ?_⟩
  · rw [q9nf_norm_expand (q3kMul (q9nfPiPow (3 * j - 4)) a), q9nf_one_add_cancel,
        hteq, he2, hnt, hp]
    exact q9np_dist9 (q9nfPiPow (3 * j)) q9psPi9 tb e2w ntw
  · rw [q9rf_resM_add, q9rf_resM_add, htres, q9rf_resM_mul, q9rf_resM_mul,
        q9np_resM_pi9, q9rfF3.zero_mul, q9rfF3.zero_mul, q9rfF3.add_zero,
        q9rfF3.add_zero]

/-! ## q9npg-4: ★★ 一般 j peel の 𝔽₃ 全射性（剰余整合・全 level） -/

/-- **q9npg-4a（★★ 一般 j peel 全射性）**: 任意 j≥3・∀ c : 𝔽₃, ∃ a b,
    N(1+π₉^{3j−4}a)−1 = π₉^{3j}·b ∧ res_M(b) = c。
    a := q9nsCorr((−1)·c)（choice-free 𝔽₃ 切断）で
    res_M(b) = res_M(u₆)·res_M(a) = (−1)·((−1)·c) = c。基底 j=3（q9np_peel_base）を
    λ-再帰で**全 level j≥3** に持ち上げた per-level 剰余全射（正直な限定: 逐次近似・完備性は未着手）。 -/
theorem q9npg_peel_general (j : Nat) (hj : 3 ≤ j) (c : q9rfF3.carrier) :
    ∃ a : q3kCar, ∃ b : q3kCar,
      q3kAdd (q3kEmbed (q3kNormBase (q3kAdd q3kOne (q3kMul (q9nfPiPow (3 * j - 4)) a))))
          (q3kNeg q3kOne)
        = q3kMul (q9nfPiPow (3 * j)) b
      ∧ q9rfResM b = c := by
  obtain ⟨b, heq, hres⟩ :=
    q9npg_peel_step j hj (q9nsCorr (q9rfF3.mul (q9rfF3.neg q9rfF3.one) c))
  refine ⟨q9nsCorr (q9rfF3.mul (q9rfF3.neg q9rfF3.one) c), b, heq, ?_⟩
  rw [hres, q9np_resM_u6, q9np_resM_corr,
      ← q9rfF3.mul_assoc (q9rfF3.neg q9rfF3.one) (q9rfF3.neg q9rfF3.one) c,
      q9np_f3_neg1_sq, q9rfF3.one_mul]

/-! ## q9npg-5: capstone -/

/-- **q9npg-5a: 一般 j peel 全射性データ**（全 level j≥3 の level-3j 先頭剰余全射）。 -/
structure Q3NormSurjPeelGeneralData where
  /-- 一般 level 先頭項閉形式（level 3j への等式・res は u₆ 剰余で不変）。 -/
  tr_lead_j : ∀ (j : Nat), 3 ≤ j → ∀ a : q3kCar,
    ∃ b : q3kCar,
      q9nfTr (q3kMul (q9nfPiPow (3 * j - 4)) a) = q3kMul (q9nfPiPow (3 * j)) b
      ∧ q9rfResM b = q9rfF3.mul (q9rfResM q9psU6) (q9rfResM a)
  /-- 一般 j の level-3j 先頭剰余は 𝔽₃ 全射（全 level）。 -/
  peel_surj : ∀ (j : Nat), 3 ≤ j → ∀ c : q9rfF3.carrier,
    ∃ a : q3kCar, ∃ b : q3kCar,
      q3kAdd (q3kEmbed (q3kNormBase (q3kAdd q3kOne (q3kMul (q9nfPiPow (3 * j - 4)) a))))
          (q3kNeg q3kOne)
        = q3kMul (q9nfPiPow (3 * j)) b
      ∧ q9rfResM b = c

/-- **q9npg-5b: 見出し実例** — 実 O_M = q3kRing 上の一般 j peel 全射性。 -/
def q9npg_data : Q3NormSurjPeelGeneralData where
  tr_lead_j := q9npg_tr_lead_j
  peel_surj := q9npg_peel_general

/-- **q9npg-5c: 一般 j peel 全射性の存在**（T3-M1 general-j の実 Lean 化）。 -/
theorem q9npg_exists : Nonempty Q3NormSurjPeelGeneralData := ⟨q9npg_data⟩

end IUT
