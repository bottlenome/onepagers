/-
  IUT/Q3NormSurjGraded.lean — 柱B・B2 T3-M1: graded ノルムの per-level 全射性の
    閉形式イディオム（λ-再帰 + Tr の O_{L₂}-線形性 + 𝔽₃ 構成的切断）
    （index(U_{L₂} : N(U_M)) ≤ 3 の上界機構への実 Lean 化・第 1 段）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（T3-core 上界機構の中核イディオム）。
  audit/pillar-B2-T3-index-artin-detail-2026-07-11.md §3（λ-再帰の閉形式）・§4 T3-M1 の
  設計をそのまま実 q3k/q3rq/q9nf/q9ps/q9rf 資産の上に建てる。toy 主語なし——主語は
  実 O_M = q3kRing・実トレース q9nfTr・実 π₉ フィルトレーション・実残余体 𝔽₃。

  complete_pct 影響: **B2 0.36→（独立監査次第・予測 0.39–0.40・T3-M1）**。ただし本ラウンド
  で建てるのは T3-M1 の**中核イディオム 3 本 + 深さ下界 + 基底 j=3 の先頭項閉形式**であり、
  剰余整合による peel の存在証明（∀u ∃a …）そのものの配線は**本ファイルでは未完**
  （正直な限定を参照）。したがって本ファイル単体の complete_pct 前進は **0**（T3-M1 の
  本物イディオム基盤の先行建設）と正直申告する。剰余整合 peel を閉じる後続ラウンドで
  0.39–0.40 に到達する見込み（監査次第）。

  真水（本物へ昇格・新規建設）:
   * q9ns_tr_linear（★ Tr の O_{L₂}-線形性）— Tr(embed(c)·t) = embed(c)·Tr(t)。
     §3 の座標 1 本補題。トレース閉形式 q9nf_tr_embed の消費。
   * q9ns_lambda_rec（★★ λ-再帰）— Tr(π₉^{i+3}·a) = embed(λ)·Tr(π₉^i·(w·a))。
     π₉³ = embed(λ)·w（q9ps_pi9_cube）+ Tr 線形性の合成。§3 の鍵イディオム。
   * q9nsLiftInt / q9ns_sect_section（★ 𝔽₃ 構成的切断）— r ↦ r%3 の Quot.lift。
     **choice-free**（Classical 不使用・可算選択不使用）。Quot.mk∘lift = id の切断性。
   * q9ns_e2_deep / q9ns_normterm_deep — i=3j−4 (j≥3) で E₂∈(π₉^{3j+1})・
     ノルム 3 次項∈(π₉^{3j+1})（他項が先頭 level 3j より深い一様下界）。
   * q9ns_tr_pi5（★ 基底 j=3 の先頭項閉形式）— Tr(π₉⁵a) = π₉⁹·(w⁻¹u₆·embed((π₉²(wa))₀))。
     λ-再帰 1 段 + Tr 閉形式 + 3=π₉⁶u₆ + λ=π₉³w⁻¹ の合成で先頭項を**厳密等式**として
     π₉-level 9 = 3j に持ち込む（可除性下界でなく等式・§3 の予言 res=±ā の実現の骨格）。
   * q9ns_resM_w（res_M(w) = 2 = −1）— §3 の「1 段ごとに w̄=−1 が掛かる」交代の実測。
   * Q3NormSurjGradedIdioms / q9ns_idioms / q9ns_exists — capstone（束ね）。

  正直な限定（§4 規約により消さない・弱めない・q3k/q9ps/q9nf/q9rf/q9gn/q3rq 継承の上に追記のみ）:
  1. **per-level イディオムのみ・peel 存在証明は未配線**。本ファイルは T3-M1 の中核イディオム
     （λ-再帰・Tr 線形性・𝔽₃ 切断・深さ下界・基底 j=3 先頭項閉形式）を本物で建てるが、
     「∀ u（λ-level j 以深の単数）∃ a, u·N(1+π₉^{3j−4}a)⁻¹ ∈ U^{(3(j+1))}」の**剰余整合
     による存在証明そのものは閉じていない**（先頭 level-3j 剰余抽出 + 𝔽₃ での逆元選択 +
     level ≥ 3j+1 への降下 + embed(O_{L₂}) 内の level 隙間補間の配線が残る）。
  2. これは **per-level（単一 peel 段）** であって U^{(3)}⊆N の全体ではない
     （後者は T3-M2 逐次近似 + T3-M3 完備性＝無限積を要する）。index≤3 の結論は T3-M4。
  3. cap(b)（分数元込みの L₂^×/N(M^×) 完全配線）・M^× の Artin 正規化は未配線
     （q9qc 限定 1 の継承）。単一拡大 M/L₂/ℚ₃ のみ。
  4. q9nf/q9gn/q9ps/q9rf/q9wr/q3k/q3rq の正直限定を全継承（可除性形式・v_M 不使用・
     O_M と M^× のみ・体化なし・σ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・
     兄弟担体・拡大 1 個）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無・
  𝔽₃ 切断は Quot.lift ベースで choice-free）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3GradedNormBreak

namespace IUT

/-! ## q9ns-0: 一般可換環の再配置ハブ -/

/-- **5 因子の再配置** (A·B)·((C·D)·E) = (A·C)·((B·D)·E)（純可換環）。
    λ-再帰の先頭項閉形式で {π₉³, w⁻¹, π₉⁶, u₆, embed} を集約する骨格。 -/
theorem q9ns_regroup (R : CRing) (A B C D E : R.carrier) :
    R.mul (R.mul A B) (R.mul (R.mul C D) E)
      = R.mul (R.mul A C) (R.mul (R.mul B D) E) := by
  rw [← R.mul_assoc (R.mul A B) (R.mul C D) E,
      R.mul_mul_mul_comm A B C D,
      R.mul_assoc (R.mul A C) (R.mul B D) E]

/-! ## q9ns-1: ★ Tr の O_{L₂}-線形性（§3 の座標 1 本補題） -/

/-- **q9ns-1a（★）: Tr(embed(c)·t) = embed(c)·Tr(t)**（Tr の O_{L₂}-線形性）。
    Tr(s) = embed(3·s₀)（q9nf_tr_embed）と (embed(c)·t)₀ = c·t₀ の合成。 -/
theorem q9ns_tr_linear (c : q3rqCar) (t : q3kCar) :
    q9nfTr (q3kMul (q3kEmbed c) t) = q3kMul (q3kEmbed c) (q9nfTr t) := by
  rw [q9nf_tr_embed (q3kMul (q3kEmbed c) t), q9nf_tr_embed t,
      q3k_embed_mul c (q3rqMul q3kThree t.1)]
  apply congrArg q3kEmbed
  have hc : (q3kMul (q3kEmbed c) t).1 = q3rqMul c t.1 := by
    show q3rqAdd (q3rqMul c t.1)
        (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero t.2.2) (q3rqMul q3rqZero t.2.1)))
      = q3rqMul c t.1
    rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq,
        q3rqRing.zero_mul t.2.2, q3rqRing.zero_mul t.2.1,
        q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero (q3rqRing.mul c t.1)]
  rw [hc, q3k_M_eq]
  exact q3rqRing.mul_left_comm q3kThree c t.1

/-! ## q9ns-2: ★★ λ-再帰（§3 の鍵イディオム） -/

/-- **q9ns-2a（★★）: λ-再帰** Tr(π₉^{i+3}·a) = embed(λ)·Tr(π₉^i·(w·a))。
    π₉^{i+3} = π₉^i·π₉³ = π₉^i·(embed(λ)·w)（q9ps_pi9_cube）で embed(λ) を外へ括り、
    Tr の O_{L₂}-線形性（q9ns_tr_linear）で閉じる。可除性下界でなく**等式**。 -/
theorem q9ns_lambda_rec (i : Nat) (a : q3kCar) :
    q9nfTr (q3kMul (q9nfPiPow (i + 3)) a)
      = q3kMul (q3kEmbed q3rqLambda)
          (q9nfTr (q3kMul (q9nfPiPow i) (q3kMul q9psW a))) := by
  have hp3 : q9nfPiPow 3 = q3kMul (q3kEmbed q3rqLambda) q9psW :=
    q9nf_pipow3_eq.trans q9ps_pi9_cube
  have hkey : q3kMul (q9nfPiPow (i + 3)) a
      = q3kMul (q3kEmbed q3rqLambda) (q3kMul (q9nfPiPow i) (q3kMul q9psW a)) := by
    rw [q9nf_pipow_add i 3, hp3, q3k_kM_eq,
        q3kRing.mul_assoc (q9nfPiPow i) (q3kRing.mul (q3kEmbed q3rqLambda) q9psW) a,
        q3kRing.mul_assoc (q3kEmbed q3rqLambda) q9psW a,
        q3kRing.mul_left_comm (q9nfPiPow i) (q3kEmbed q3rqLambda) (q3kRing.mul q9psW a)]
  rw [hkey]
  exact q9ns_tr_linear q3rqLambda (q3kMul (q9nfPiPow i) (q3kMul q9psW a))

/-! ## q9ns-3: ★ 𝔽₃ 構成的切断（Quot.lift of r↦r%3・choice-free） -/

/-- **q9ns-3a（★ 𝔽₃ 構成的切断）: 𝔽₃ → Int**（r ↦ r%3 の Quot.lift）。
    r%3 は modCong 3 類上定数（3∣a−b ⟹ a%3=b%3）なので Quot.lift が定義でき、
    **可算選択も Classical も不要**の choice-free 切断となる。 -/
def q9nsLiftInt (r : q9rfF3.carrier) : Int :=
  Quot.lift (fun a : Int => a % 3)
    (fun a b (h : (modCong 3).rel a b) => by
      have hd : ((3 : Nat) : Int) ∣ (a - b) := h
      show a % 3 = b % 3
      omega) r

/-- **q9ns-3b（★ 切断性）: Quot.mk ∘ q9nsLiftInt = id**（𝔽₃ → Int → 𝔽₃ の往復が恒等）。
    これにより剰余類から**データとして**代表 r%3 を取り出せる（choice-free）。 -/
theorem q9ns_sect_section (r : q9rfF3.carrier) :
    (Quot.mk (modCong 3).rel (q9nsLiftInt r) : q9rfF3.carrier) = r := by
  induction r using Quot.ind
  rename_i a
  show Quot.mk (modCong 3).rel (a % 3) = Quot.mk (modCong 3).rel a
  apply Quot.sound
  show ((3 : Nat) : Int) ∣ (a % 3 - a)
  omega

/-- **q9ns-3c: 剰余からの実補正元 a : q3kCar**（切断 r%3 を ℤ₃↪O_{L₂}↪O_M で埋め込む）。
    構成的（choice-free）——後続の剰余整合 peel が消費する陽な補正の担い手。 -/
def q9nsCorr (r : q9rfF3.carrier) : q3kCar :=
  q3kEmbed (((toZp 3).map (q9nsLiftInt r), z3.zero) : q3rqCar)

/-! ## q9ns-4: 他項の深さ下界（i=3j−4・j≥3 で先頭 level 3j より深い） -/

/-- **q9ns-4a: E₂ の深さ**（i=3j−4 で E₂(π₉^i·a) ∈ (π₉^{3j+1})）。
    q9nf_e2_dvd の 2i = 6j−8 ≥ 3j+1 ⟺ j≥3。 -/
theorem q9ns_e2_deep (j : Nat) (hj : 3 ≤ j) (a : q3kCar) :
    q9wrDvd (q9nfPiPow (3 * j + 1)) (q9nfE2 (q3kMul (q9nfPiPow (3 * j - 4)) a)) := by
  have hb := q9nf_e2_dvd (3 * j - 4) (q3kMul (q9nfPiPow (3 * j - 4)) a) ⟨a, rfl⟩
  exact q9nf_dvd_of_le (by omega) hb

/-- **q9ns-4b: ノルム 3 次項の深さ**（i=3j−4 で embed(N(π₉^i·a)) ∈ (π₉^{3j+1})）。
    q9nf_normterm_dvd の 3i = 9j−12 ≥ 3j+1 ⟺ j≥3。 -/
theorem q9ns_normterm_deep (j : Nat) (hj : 3 ≤ j) (a : q3kCar) :
    q9wrDvd (q9nfPiPow (3 * j + 1))
      (q3kEmbed (q3kNormBase (q3kMul (q9nfPiPow (3 * j - 4)) a))) := by
  have hb := q9nf_normterm_dvd (3 * j - 4) (q3kMul (q9nfPiPow (3 * j - 4)) a) ⟨a, rfl⟩
  exact q9nf_dvd_of_le (by omega) hb

/-! ## q9ns-5: ★ 基底 j=3 の先頭項閉形式（λ-再帰の実現） -/

/-- **q9ns-5a（★ 基底 j=3 先頭項閉形式）: Tr(π₉⁵a) = π₉⁹·(w⁻¹u₆·embed((π₉²(wa))₀))**。
    λ-再帰 1 段（i=2）→ Tr(π₉²(wa)) = embed(3·(π₉²(wa))₀) = embed(3)·embed(…)、
    3 = π₉⁶u₆・embed(λ) = π₉³w⁻¹ を集約（q9ns_regroup）。先頭項を π₉-level 9 = 3·3 に
    **可除性下界でなく等式として**持ち込む（§3 の閉形式）。 -/
theorem q9ns_tr_pi5 (a : q3kCar) :
    q9nfTr (q3kMul (q9nfPiPow 5) a)
      = q3kMul (q9nfPiPow 9)
          (q3kMul (q3kMul q9psWinv q9psU6)
            (q3kEmbed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1)) := by
  have h1 : q9nfTr (q3kMul (q9nfPiPow 5) a)
      = q3kMul (q3kEmbed q3rqLambda)
          (q9nfTr (q3kMul (q9nfPiPow 2) (q3kMul q9psW a))) :=
    q9ns_lambda_rec 2 a
  have h9 : q3kRing.mul (q9nfPiPow 3) (q9nfPiPow 6) = q9nfPiPow 9 := by
    rw [← q3k_kM_eq]; exact (q9nf_pipow_add 3 6).symm
  rw [h1, q9nf_tr_embed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)), q9ps_three_eq,
      ← q3k_embed_mul q3rqThreeElt (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1,
      q9nf_embed_lambda, q9ps_three_eq_pi6_u6, ← q9nf_pipow6_eq, q3k_kM_eq,
      q9ns_regroup q3kRing (q9nfPiPow 3) q9psWinv (q9nfPiPow 6) q9psU6 _,
      h9]

/-! ## q9ns-6: res_M(w) = −1（§3 の交代 ±ā の実測） -/

/-- **q9ns-6a: res_M(w) = 2 = −1**（w = (ζ₃+1, −λ, λ)・resL(ζ₃+1)=2・resL(±λ)=0）。
    §3 の「λ-再帰 1 段ごとに w̄ = −1 が掛かる」交代（先頭剰余 ±ā）の実測。 -/
theorem q9ns_resM_w : q9rfResM q9psW = q9rfF3.add q9rfF3.one q9rfF3.one := by
  show q9rfResL (q3rqAdd (q3rqAdd q3rqZeta q3rqOne)
      (q3rqAdd (q3rqNeg q3rqLambda) q3rqLambda)) = q9rfF3.add q9rfF3.one q9rfF3.one
  rw [q9rf_resL_add (q3rqAdd q3rqZeta q3rqOne) (q3rqAdd (q3rqNeg q3rqLambda) q3rqLambda),
      q9rf_resL_add q3rqZeta q3rqOne,
      q9rf_resL_add (q3rqNeg q3rqLambda) q3rqLambda,
      q9rf_resL_zeta, q9gn_resL_one, q9gn_resL_neg q3rqLambda, q9rf_resL_lambda,
      q9rfF3.neg_zero, q9rfF3.add_zero q9rfF3.zero,
      q9rfF3.add_zero (q9rfF3.add q9rfF3.one q9rfF3.one)]

/-! ## q9ns-7: capstone -/

/-- **q9ns-7a: T3-M1 の中核イディオム束**（λ-再帰・Tr 線形性・𝔽₃ 切断・
    深さ下界・基底 j=3 先頭項閉形式）。剰余整合 peel の存在証明は未配線（正直な限定 1）。 -/
structure Q3NormSurjGradedIdioms where
  /-- Tr の O_{L₂}-線形性。 -/
  tr_linear : ∀ (c : q3rqCar) (t : q3kCar),
    q9nfTr (q3kMul (q3kEmbed c) t) = q3kMul (q3kEmbed c) (q9nfTr t)
  /-- λ-再帰 Tr(π₉^{i+3}a) = embed(λ)·Tr(π₉^i·(w·a))。 -/
  lambda_rec : ∀ (i : Nat) (a : q3kCar),
    q9nfTr (q3kMul (q9nfPiPow (i + 3)) a)
      = q3kMul (q3kEmbed q3rqLambda) (q9nfTr (q3kMul (q9nfPiPow i) (q3kMul q9psW a)))
  /-- 𝔽₃ 構成的切断の切断性（choice-free）。 -/
  sect_section : ∀ r : q9rfF3.carrier,
    (Quot.mk (modCong 3).rel (q9nsLiftInt r) : q9rfF3.carrier) = r
  /-- 基底 j=3 の先頭項閉形式（level 9 への等式）。 -/
  tr_pi5 : ∀ a : q3kCar,
    q9nfTr (q3kMul (q9nfPiPow 5) a)
      = q3kMul (q9nfPiPow 9)
          (q3kMul (q3kMul q9psWinv q9psU6)
            (q3kEmbed (q3kMul (q9nfPiPow 2) (q3kMul q9psW a)).1))
  /-- E₂ の深さ（i=3j−4・j≥3 で level ≥ 3j+1）。 -/
  e2_deep : ∀ (j : Nat), 3 ≤ j → ∀ a : q3kCar,
    q9wrDvd (q9nfPiPow (3 * j + 1)) (q9nfE2 (q3kMul (q9nfPiPow (3 * j - 4)) a))

/-- **q9ns-7b: 見出し実例** — 実 O_M = q3kRing 上の T3-M1 中核イディオム。 -/
def q9ns_idioms : Q3NormSurjGradedIdioms where
  tr_linear := q9ns_tr_linear
  lambda_rec := q9ns_lambda_rec
  sect_section := q9ns_sect_section
  tr_pi5 := q9ns_tr_pi5
  e2_deep := q9ns_e2_deep

/-- **q9ns-7c: T3-M1 中核イディオムの存在**（graded 全射性 peel への実 Lean 足場）。 -/
theorem q9ns_exists : Nonempty Q3NormSurjGradedIdioms := ⟨q9ns_idioms⟩

end IUT
