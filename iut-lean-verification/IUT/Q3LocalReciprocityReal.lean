/-
  IUT/Q3LocalReciprocityReal.lean — 柱B・B2 M3: 実局所類体論の crux「4 = 1+3 ∉ N_{M/L₂}(M^×)」
    （B2 local-reciprocity の初の genuine 非ノルム——本物の IUT-core LCFT 内容）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（genuine new IUT-core math）。
  B2 の真の crux「4 ∉ N」（audit/pillar-B2-level6-cokernel-detail-2026-07-11.md §3 M3・
  初の status mover）を、M1（q9rf 実残余体 𝔽₃・O_M 局所性）と M2（q9gn level-6 graded
  ノルム break）と q9nf 再標的スパイクの上で、実 O_M = q3kRing・実 O_{L₂} = q3rqRing 上に
  完全に割る。x∈O_M（整単数）に対し N(x) = 4 = 1+3 は不可能——3 段降下
  （res∘N で U^(1) → break cancel の先頭項分離で U^(2)）＋ 再標的 witness の矛盾
  （N(U^(2)) ⊆ U^(9) ⊆ U^(7) だが 1+3 ∉ U^(7)）で示す。
  toy 主語なし——主語は実 q3kRing・実 q3rqRing・実 z3・実残余体 𝔽₃。

  complete_pct 影響: **B2 0→（独立監査次第・予測 0.25–0.35・status-mover）**。
  本モジュールが retarget 後の crux を実 Lean で閉じ、(T1) 値群側 + 単数余核の非自明性
  （非ノルム単数の実在）を確立する。

  真水（本物へ昇格・新規建設）:
   * q9lrFour（= 4 = 1+3 ∈ O_{L₂}）と q9lr_embed_four（embed 加法性で retarget subject に一致）
   * q9lr_resM_pi9（res_M(π₉)=0）・q9lr_resM_of_pi9_dvd（π₉∣x ⟹ res_M(x)=0）
   * q9lr_step0（★ res∘N 段: N(x)=4 ⟹ x∈U^(1)）
   * q9lr_step1（★★ break-cancel 先頭項降下: N(x)=4 ⟹ x∈U^(2)）
   * q9lr_contra（★ 再標的矛盾: x∈U^(2) ⟹ N(x)≠4）
   * q9lr_four_not_norm（★★★ CRUX: ¬∃x単数, N(x)=4——初の genuine 非ノルム）

  正直な限定（§4 規約により消さない・弱めない・q3k/q9ps/q9nf/q9wr/q3rq/q9rf/q9gn 継承の上に追記のみ）:
  1. **量化は x ∈ O_M（整元 = q3kCar）に限る**。分数元 π₉^{-k}u ∈ M^× への拡張は M^× の
     群提示（q9ps ヘッダの ℤ×U₃）上の値群 bookkeeping（N(x) 単数 ⟹ k=0）であり、
     群提示が未 wire のため **honest limitation として残す**——整単数に対する crux が
     本物の内容であることは変わらない（非ノルム単数の実在が余核の非自明性そのもの）。
  2. **単一拡大 M/L₂/ℚ₃**（q3k 兄弟担体・拡大 1 個）。より高次の拡大塔ゼロ。
  3. **余核 ℤ/3 の full index（T3・指数 ≤3・Artin 写像）は M5/research（範囲外）**。本 M3 は
     (T2) の下界側（非ノルムの実在）のみ。類 [4] の位数 3 と Gal 対応（M4）は後続。
  4. q3k/q9ps/q9nf/q9wr/q3rq/q9rf/q9gn の正直限定を全継承（O_M と M^× のみ・体化なし・
     σ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・可除性形式 v_M 不使用）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3GradedNormBreak

namespace IUT

/-! ## q9lr-0: 4 = 1+3 の定義と retarget subject への一致 -/

/-- **q9lr-0a: 4 = 1 + 3 ∈ O_{L₂}**（retarget 候補・§3 M3）。 -/
def q9lrFour : q3rqCar := q3rqAdd q3rqOne q3rqThreeElt

/-- **q9lr-0b: embed(4) = 1 + embed(3)**（embed 加法性）——q9nf_retarget_sharp の主語に一致。 -/
theorem q9lr_embed_four : q3kEmbed q9lrFour = q3kAdd q3kOne (q3kEmbed q3rqThreeElt) := by
  show q3kEmbed (q3rqAdd q3rqOne q3rqThreeElt) = q3kAdd q3kOne (q3kEmbed q3rqThreeElt)
  rw [q9rf_embed_add, q3k_embed_one]

/-- **q9lr-0c: resL(4) = 1**（resL(1)=1・resL(3)=0）。 -/
theorem q9lr_resL_four : q9rfResL q9lrFour = q9rfF3.one := by
  show q9rfResL (q3rqAdd q3rqOne q3rqThreeElt) = q9rfF3.one
  rw [q9rf_resL_add, q9gn_resL_one, q9rf_resL_three, q9rfF3.add_zero]

/-! ## q9lr-1: 残余の局所性補助（res_M(π₉)=0・π₉∣x ⟹ res_M(x)=0） -/

/-- resL(0) = 0。 -/
theorem q9lr_resL_zero : q9rfResL q3rqZero = q9rfF3.zero := rfl

/-- **q9lr-1a: res_M(π₉) = 0**（π₉ = (−1,1,0)・座標和 = 0）。 -/
theorem q9lr_resM_pi9 : q9rfResM q9psPi9 = q9rfF3.zero := by
  rw [q9ps_pi9_coords]
  show q9rfResL (q3rqAdd (q3rqNeg q3rqOne) (q3rqAdd q3rqOne q3rqZero)) = q9rfF3.zero
  rw [q9rf_resL_add, q9rf_resL_add, q9gn_resL_neg, q9gn_resL_one,
      q9lr_resL_zero, q9rfF3.add_zero, q9rfF3.neg_add]

/-- **q9lr-1b: π₉ ∣ x ⟹ res_M(x) = 0**（res_M(π₉)=0・環準同型）。 -/
theorem q9lr_resM_of_pi9_dvd {x : q3kCar} (h : q9wrDvd q9psPi9 x) :
    q9rfResM x = q9rfF3.zero := by
  obtain ⟨c, hc⟩ := h
  rw [hc, q9rf_resM_mul, q9lr_resM_pi9, q9rfF3.zero_mul]

/-- res_M(1) = 1。 -/
theorem q9lr_resM_one : q9rfResM q3kOne = q9rfF3.one := by
  rw [← q3k_embed_one, q9rf_resM_embed, q9gn_resL_one]

/-- res_M(0) = 0。 -/
theorem q9lr_resM_zero : q9rfResM q3kZero = q9rfF3.zero := by
  show q9rfResL (q3rqAdd q3rqZero (q3rqAdd q3rqZero q3rqZero)) = q9rfF3.zero
  rw [q9rf_resL_add, q9rf_resL_add, q9lr_resL_zero, q9rfF3.add_zero, q9rfF3.add_zero]

/-- res_M(−1) = −1（1+(−1)=0 の res 加法性）。 -/
theorem q9lr_resM_neg_one : q9rfResM (q3kNeg q3kOne) = q9rfF3.neg q9rfF3.one := by
  have hz : q3kAdd q3kOne (q3kNeg q3kOne) = q3kZero := by
    rw [q9nf_kA_eq, q9ps_kN_eq, q9ps_kO_eq, q3kRing.add_neg q3kRing.one, ← q9nf_kZ_eq]
  have hsum : q9rfF3.add q9rfF3.one (q9rfResM (q3kNeg q3kOne)) = q9rfF3.zero := by
    rw [← q9lr_resM_one, ← q9rf_resM_add, hz, q9lr_resM_zero]
  exact (q9rfF3.neg_eq_of_add_eq_zero hsum).symm

/-! ## q9lr-2: 単数 U*（= embed(ζ₃−1) の π₉³ を割った単数）の存在 -/

/-- **q9lr-2a: U\* = w⁻¹·embed(ζ₃+1) は単数**（embed(ζ₃−1) = π₉³·U\* の単数因子）。 -/
theorem q9lr_uu_unit :
    q3kUnitMem (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne))) :=
  q3k_unit_mul (q3k_unit_inv q9psW q9ps_w_unit)
    (q9wr_embed_unit (q3rqAdd q3rqZeta q3rqOne) q9wr_zeta_add_one_unit)

/-! ## q9lr-3: ★ 降下段 step0（res∘N: N(x)=4 ⟹ x∈U^(1)） -/

/-- **q9lr-3a（★ step0）: q3kUnitMem x → N(x)=4 → x ∈ U^(1)**。
    res∘N（q9rf_res_norm）で res_M(x)=resL(4)=1、よって res_M(x−1)=0、核完全性で π₉∣(x−1)。 -/
theorem q9lr_step0 {x : q3kCar} (_hu : q3kUnitMem x)
    (hN : q3kNormBase x = q9lrFour) : q9nfUfilt 1 x := by
  have h1 : q9rfResM x = q9rfF3.one := by
    rw [← q9rf_res_norm x, hN, q9lr_resL_four]
  have hres : q9rfResM (q3kAdd x (q3kNeg q3kOne)) = q9rfF3.zero := by
    rw [q9rf_resM_add, h1, q9lr_resM_neg_one, q9rfF3.add_neg]
  show q9wrDvd (q9nfPiPow 1) (q3kAdd x (q3kNeg q3kOne))
  rw [q9nf_pipow1_eq]
  exact q9rf_kernel (q3kAdd x (q3kNeg q3kOne)) hres

/-! ## q9lr-4: ★★ 降下段 step1（break-cancel 先頭項降下: N(x)=4 ⟹ x∈U^(2)） -/

/-- **q9lr-4a（★★ step1）: q3kUnitMem x → N(x)=4 → x ∈ U^(2)**。
    step0 で x=1+π₉a、q9gn_norm_U1_sharp で先頭項 embed((ζ₃−1)N(a)) を分離、
    N(x)=4 ⟹ embed(N x)−1 = embed(3) ∈(π₉⁶) より π₉⁶∣embed((ζ₃−1)N(a))。
    embed(ζ₃−1)=π₉³·U\* を剥がして π₉³∣embed(N a)、res_M(a)=resL(N a)=0、核完全性で π₉∣a、
    x=1+π₉(π₉a')=1+π₉²a'。 -/
theorem q9lr_step1 {x : q3kCar} (hu : q3kUnitMem x)
    (hN : q3kNormBase x = q9lrFour) : q9nfUfilt 2 x := by
  have hx1 : q9nfUfilt 1 x := q9lr_step0 hu hN
  obtain ⟨a, hxa, hsharp⟩ := q9gn_norm_U1_sharp hx1
  -- N(x)=4 で先頭項式を embed(3) へ書き換え
  rw [hN, q9lr_embed_four, q9nf_one_add_cancel] at hsharp
  -- hsharp : π₉⁶ ∣ (embed(3) − embed((ζ₃−1)·N a))
  have hE3 : q9wrDvd (q9nfPiPow 6) (q3kEmbed q3rqThreeElt) := q9gn_embed_three_dvd6
  -- π₉⁶ ∣ embed((ζ₃−1)·N a)
  have hBdvd : q9wrDvd (q9nfPiPow 6)
      (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a))) := by
    have hnegB : q3kNeg (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a)))
        = q3kAdd (q3kNeg (q3kEmbed q3rqThreeElt))
            (q3kAdd (q3kEmbed q3rqThreeElt)
              (q3kNeg (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a))))) := by
      rw [q9nf_kA_eq, q9ps_kN_eq,
          ← q3kRing.add_assoc (q3kRing.neg (q3kEmbed q3rqThreeElt)) (q3kEmbed q3rqThreeElt)
            (q3kRing.neg (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a)))),
          q3kRing.neg_add (q3kEmbed q3rqThreeElt),
          q3kRing.zero_add (q3kRing.neg (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a))))]
    have h1 : q9wrDvd (q9nfPiPow 6)
        (q3kNeg (q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a)))) := by
      rw [hnegB]
      exact q9nf_dvd_add (q9gn_dvd_neg hE3) hsharp
    have h2 := q9gn_dvd_neg h1
    rwa [q9ps_kN_eq, q3kRing.neg_neg] at h2
  -- 閉形式 embed((ζ₃−1)·N a) = π₉³·(U\*·embed(N a))
  have hBform : q3kEmbed (q3rqMul (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) (q3kNormBase a))
      = q3kMul (q9nfPiPow 3)
          (q3kMul (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne)))
            (q3kEmbed (q3kNormBase a))) := by
    rw [← q3k_embed_mul, q9nf_zeta_sub_one_split,
        q3k_mul_assoc (q9nfPiPow 3)
          (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne)))
          (q3kEmbed (q3kNormBase a))]
  obtain ⟨cc, hcc⟩ := hBdvd
  have h63 : q9nfPiPow 6 = q3kMul (q9nfPiPow 3) (q9nfPiPow 3) := q9nf_pipow_add 3 3
  have hcomb : q3kMul (q9nfPiPow 3) (q3kMul (q9nfPiPow 3) cc)
      = q3kMul (q9nfPiPow 3)
          (q3kMul (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne)))
            (q3kEmbed (q3kNormBase a))) := by
    rw [← q3k_mul_assoc (q9nfPiPow 3) (q9nfPiPow 3) cc, ← h63, ← hcc, hBform]
  rw [q9nf_pipow3_eq] at hcomb
  have hUcancel := q9wr_pi3_cancel hcomb
  -- π₉³ ∣ (U\*·embed(N a))
  have hdvd3 : q9wrDvd (q9nfPiPow 3)
      (q3kMul (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne)))
        (q3kEmbed (q3kNormBase a))) := by
    refine ⟨cc, ?_⟩
    rw [q9nf_pipow3_eq]
    exact hUcancel.symm
  -- 単数 U\* を剥がして π₉³ ∣ embed(N a)
  have hNAdvd3 : q9wrDvd (q9nfPiPow 3) (q3kEmbed (q3kNormBase a)) :=
    q9gn_unit_dvd_cancel
      (q3k_inv_mul' (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne))) q9lr_uu_unit)
      hdvd3
  have hNApi9 : q9wrDvd q9psPi9 (q3kEmbed (q3kNormBase a)) := by
    have hd := q9nf_dvd_of_le (m := 1) (n := 3) (by omega) hNAdvd3
    rw [q9nf_pipow1_eq] at hd
    exact hd
  -- res_M(a) = resL(N a) = 0 ⟹ π₉ ∣ a
  have hResA : q9rfResM a = q9rfF3.zero := by
    have h0 := q9lr_resM_of_pi9_dvd hNApi9
    rw [q9rf_resM_embed] at h0
    rw [← q9rf_res_norm a]
    exact h0
  have haPi9 : q9wrDvd q9psPi9 a := q9rf_kernel a hResA
  obtain ⟨a', ha'⟩ := haPi9
  -- x − 1 = π₉·a = π₉·(π₉·a') = π₉²·a'
  show q9wrDvd (q9nfPiPow 2) (q3kAdd x (q3kNeg q3kOne))
  refine ⟨a', ?_⟩
  rw [hxa, q9nf_one_add_cancel, ha', q9gn_pi2_eq, q3k_mul_assoc q9psPi9 q9psPi9 a']

/-! ## q9lr-5: ★ 矛盾段 contra（x∈U^(2) ⟹ N(x)≠4） -/

/-- **q9lr-5a（★ contra）: x ∈ U^(2) → N(x) ≠ 4**。
    q9gn_norm_U2: embed(N x)∈U^(9)⊆U^(7)、一方 embed(4)=1+embed(3)∉U^(7)（q9nf_retarget_sharp）。 -/
theorem q9lr_contra {x : q3kCar} (hx : q9nfUfilt 2 x) :
    q3kNormBase x ≠ q9lrFour := by
  intro heq
  have h9 : q9nfUfilt 9 (q3kEmbed (q3kNormBase x)) := q9gn_norm_U2 hx
  rw [heq, q9lr_embed_four] at h9
  have h7 : q9nfUfilt 7 (q3kAdd q3kOne (q3kEmbed q3rqThreeElt)) :=
    q9nf_ufilt_antitone (i := 7) (k := 2) h9
  exact q9nf_retarget_sharp h7

/-! ## q9lr-6: ★★★ CRUX——4 = 1+3 は非ノルム -/

/-- **q9lr-6a（★★★ CRUX）: ¬ ∃ x 単数, N(x) = 4 = 1+3**——初の genuine 非ノルム。
    step0 → step1 → contra の合成。x ∈ O_M（整単数）に対する N_{M/L₂}(x) = 4 は不可能。 -/
theorem q9lr_four_not_norm :
    ¬ ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9lrFour := by
  intro h
  obtain ⟨x, hu, heq⟩ := h
  exact q9lr_contra (q9lr_step1 hu heq) heq

/-! ## q9lr-7: capstone -/

/-- **q9lr-7a: 実局所類体論 crux データ** — 非ノルム性（4∉N）と矛盾段を束ねる。 -/
structure Q3LocalReciprocityRealData where
  /-- CRUX: ¬∃x単数, N(x)=4（初の genuine 非ノルム）。 -/
  four_not_norm : ¬ ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9lrFour
  /-- 矛盾段: x∈U^(2) ⟹ N(x)≠4。 -/
  contra : ∀ x, q9nfUfilt 2 x → q3kNormBase x ≠ q9lrFour
  /-- 降下段: N(x)=4 ⟹ x∈U^(2)。 -/
  descent : ∀ x, q3kUnitMem x → q3kNormBase x = q9lrFour → q9nfUfilt 2 x

/-- **q9lr-7b: 見出し実例** — 実 O_M = q3kRing 上の非ノルム crux。 -/
def q9lr_data : Q3LocalReciprocityRealData where
  four_not_norm := q9lr_four_not_norm
  contra := fun _ hx => q9lr_contra hx
  descent := fun _ hu hN => q9lr_step1 hu hN

/-- **q9lr-7c: crux の存在**（B2 (T2) 下界・非ノルム単数の実在）。 -/
theorem q9lr_exists : Nonempty Q3LocalReciprocityRealData := ⟨q9lr_data⟩

end IUT
