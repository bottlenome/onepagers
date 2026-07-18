/-
  IUT/Q3ReciprocityCokernelReal.lean — 柱B・B2 M4: 余核 L₂^×/N(M^×) の genuine ℤ/3 下界
    （crux 4∉N（M3）を「類 [4] の位数ちょうど 3」へ昇格——本物の IUT-core LCFT 内容）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（genuine new IUT-core math）。
  audit/pillar-B2-level6-cokernel-detail-2026-07-11.md §3 M4（order-3 argument）・
  audit/reaudit-q9lr-b2crux-fournotnorm-2026-07-11.md §4/§7（cokernel が「非自明のみ」
  だった点を ℤ/3 へ閉じる次増分）の実装。M3（q9lr: 4∉N）の上に、実 O_M = q3kRing・
  実 O_{L₂} = q3rqRing 上で:
   * 4²=16 ∉ N（q9rc_foursq_not_norm）——もし 4²=N(x) なら y=embed(4)·x⁻¹ が単数で
     N(y)=4³·(4²)⁻¹=4 となり M3 に矛盾。
   * 4³=64 ∈ N（q9rc_fourcube_is_norm）——witness embed(4)、N(embed 4)=4³。
  よって類 [4] は L₂^×/N(M^×) で位数ちょうど 3（4∉N, 4²∉N, 4³∈N）——genuine ℤ/3 下界。
  toy 主語なし——主語は実 q3kRing・実 q3rqRing・実 z3・実 3 次ノルム。

  complete_pct 影響: **B2 0.22→（独立監査次第・予測 +0.05〜0.10・T2 ℤ/3 下界完成）**。
  M3 は cokernel「非自明のみ」を確立した。本 M4 は [4] の位数を 3 に確定し、
  ℤ/3 ↪ L₂^×/N(M^×) の genuine 下界（(T2) の下界側）を閉じる。

  真水（本物へ昇格・新規建設）:
   * q9rcFour/q9rcFourSq/q9rcFourCube（= 4, 16, 64 ∈ O_{L₂}）
   * q9rc_four_unit（4 は実 ℤ₃-単数・N(4,0)=16 unit）・q9rc_embed_four_unit
   * q9rc_mul_cube_inv（q3rq 恒等式 4³·(4²)⁻¹=4 の一般形）・q9rc_four_cancel（4 単数消去）
   * q9rc_fourcube_is_norm（★ 4³∈N）
   * q9rc_foursq_not_norm（★★ 4²∉N——位数 3 の鍵）
   * q9rc_order3（★★★ element-level 位数 3 データ: 4∉N ∧ 4²∉N ∧ 4³∈N）
   * q9rc_z3_injects（三類 [4⁰],[4¹],[4²] が N を法として pairwise 相異——ℤ/3 ↪ cokernel）

  正直な限定（§4 規約により消さない・弱めない・q9lr/q9rf/q9gn/q9ps/q3k/q3rq 継承の上に追記のみ）:
  1. **量化は x ∈ O_M（整元 = q3kCar）に限る**（M3 から継承）。M^× 自体（分数元 π₉^{-k}u）は
     未形式化——値群 bookkeeping（N(x) 単数 ⟹ x integral 単数）は未 wire。honest limitation。
  2. **余核は element-level で表現**（quotient object 未建設）。したがって「ℤ/3 下界」は
     element-level の位数 3 事実（4∉N, 4²∉N, 4³∈N）＋ pairwise-distinct 類（q9rc_z3_injects）
     として実現する。群商そのものへの同型（および Gal(M/L₂)=q9kdG との正規化された対応
     ——Artin 写像 4↦σ vs σ²）は未建設——honest limitation として明記。
  3. **T3（指数 ≤3・U_{L₂}^(3) ⊆ N・Artin 写像）は M5/research（範囲外）**。本 M4 は (T2) の
     下界側（[4] 位数 3）のみ。
  4. q9lr/q9rf/q9gn/q9ps/q9wr/q3k/q3rq の正直限定を全継承（O_M と M^× のみ・体化なし・
     σ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・単一拡大 M/L₂/ℚ₃）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3LocalReciprocityReal

namespace IUT

/-! ## q9rc-0: 4, 4², 4³ ∈ O_{L₂} -/

/-- **q9rc-0a: 4 = 1+3 ∈ O_{L₂}**（= q9lrFour・M3 の crux subject）。 -/
def q9rcFour : q3rqCar := q9lrFour

/-- **q9rc-0b: 4² = 16 ∈ O_{L₂}**。 -/
def q9rcFourSq : q3rqCar := q3rqMul q9rcFour q9rcFour

/-- **q9rc-0c: 4³ = 64 ∈ O_{L₂}**。 -/
def q9rcFourCube : q3rqCar := q3rqMul q9rcFourSq q9rcFour

/-! ## q9rc-1: 4 は実 ℤ₃-単数（N(4,0)=16 unit） -/

/-- 4 = (1+3, 0) の対形（第 2 成分 = 0）。 -/
theorem q9rc_four_pair : q9rcFour = ((z3.add z3.one q3rqThree, z3.zero) : q3rqCar) := by
  show q3rqAdd q3rqOne q3rqThreeElt = ((z3.add z3.one q3rqThree, z3.zero) : q3rqCar)
  apply q3rq_ext
  · rfl
  · show z3.add z3.zero z3.zero = z3.zero
    exact z3.add_zero z3.zero

/-- 実 ℤ₃ の元 4 = 1+3 は単数（レベル 1 剰余 = 4 ≡ 1・3∤4）。 -/
theorem q9rc_scalar_four_unit : IsZpUnit 3 (z3.add z3.one q3rqThree) := by
  refine ⟨4, ?_, ?_⟩
  · rfl
  · intro h
    have h1 : ((3 : Nat) : Int).natAbs ∣ ((4 : Int)).natAbs :=
      Int.natAbs_dvd_natAbs.mpr h
    rw [Int.natAbs_natCast] at h1
    have h2 : (3 : Nat) ∣ ((4 : Int)).natAbs := h1
    have h3 : ((4 : Int)).natAbs = 4 := rfl
    rw [h3] at h2
    obtain ⟨k, hk⟩ := h2
    omega

/-- **q9rc-1a（★）: 4 は実 ℤ₃-単数**（q3rq_pair_unit で N(4,0)=16 unit）。 -/
theorem q9rc_four_unit : q3rqUnitMem q9rcFour := by
  rw [q9rc_four_pair]
  exact q3rq_pair_unit (z3.add z3.one q3rqThree) q9rc_scalar_four_unit

/-- **q9rc-1b: embed(4) は実 O_M-単数**（q9wr_embed_unit）。 -/
theorem q9rc_embed_four_unit : q3kUnitMem (q3kEmbed q9rcFour) :=
  q9wr_embed_unit q9rcFour q9rc_four_unit

/-! ## q9rc-2: q3rq 単数演算補題（4³·(4²)⁻¹=4・4 単数消去） -/

/-- **q9rc-2a: 一般恒等式 (u²·u)·(u²)⁻¹ = u**（q3rq 単数演算・4³·(4²)⁻¹=4 の抽象形）。 -/
theorem q9rc_mul_cube_inv (A NS : q3rqCar) (hu : q3rqUnitMem NS)
    (hNS : NS = q3rqMul A A) :
    q3rqMul (q3rqMul (q3rqMul A A) A) (q3rqInv NS hu) = A := by
  have hinv : q3rqRing.mul NS (q3rqInv NS hu) = q3rqRing.one := by
    have h := q3rq_inv_mul NS hu
    rw [q3k_M_eq] at h
    rw [q3rqRing.mul_comm NS (q3rqInv NS hu), ← q9ps_1_eq]
    exact h
  rw [q3k_M_eq]
  have hNS' : q3rqRing.mul A A = NS := by rw [← q3k_M_eq]; exact hNS.symm
  rw [hNS', q3rqRing.mul_comm NS A,
      q3rqRing.mul_assoc A NS (q3rqInv NS hu), hinv, q3rqRing.mul_one A]

/-- **q9rc-2b: 4 による左消去** 4·a = 4·b ⟹ a = b（4 は単数）。 -/
theorem q9rc_four_cancel {a b : q3rqCar}
    (h : q3rqMul q9rcFour a = q3rqMul q9rcFour b) : a = b := by
  have hinv' : q3rqRing.mul (q3rqInv q9rcFour q9rc_four_unit) q9rcFour = q3rqRing.one := by
    have h0 := q3rq_inv_mul q9rcFour q9rc_four_unit
    rw [q3k_M_eq] at h0
    rw [← q9ps_1_eq]
    exact h0
  have key := congrArg (q3rqMul (q3rqInv q9rcFour q9rc_four_unit)) h
  rw [q3k_M_eq] at key
  rw [← q3rqRing.mul_assoc (q3rqInv q9rcFour q9rc_four_unit) q9rcFour a,
      ← q3rqRing.mul_assoc (q3rqInv q9rcFour q9rc_four_unit) q9rcFour b,
      hinv', q3rqRing.one_mul a, q3rqRing.one_mul b] at key
  exact key

/-! ## q9rc-3: ★ 4³ ∈ N（3 乗はノルム） -/

/-- **q9rc-3a（★）: 4³ ∈ N**——witness embed(4)、N(embed 4) = 4·4·4 = 4³。 -/
theorem q9rc_fourcube_is_norm :
    ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9rcFourCube := by
  refine ⟨q3kEmbed q9rcFour, q9rc_embed_four_unit, ?_⟩
  rw [q9ps_normBase_embed]
  rfl

/-! ## q9rc-4: ★★ 4² ∉ N（位数 3 の鍵） -/

/-- **q9rc-4a（★★）: 4² = 16 ∉ N**。
    もし ⟨x, hx, N(x)=16⟩ なら y = embed(4)·x⁻¹ は単数で
    N(y) = N(embed 4)·N(x⁻¹) = 4³·(4²)⁻¹ = 4——M3（q9lr_four_not_norm）に矛盾。 -/
theorem q9rc_foursq_not_norm :
    ¬ ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9rcFourSq := by
  intro h
  obtain ⟨x, hx, hN⟩ := h
  have hy_unit : q3kUnitMem (q3kMul (q3kEmbed q9rcFour) (q3kInv x hx)) :=
    q3k_unit_mul q9rc_embed_four_unit (q3k_unit_inv x hx)
  have hNy : q3kNormBase (q3kMul (q3kEmbed q9rcFour) (q3kInv x hx)) = q9rcFour := by
    rw [q3k_normBase_mul, q9ps_normBase_embed, q3k_normBase_inv]
    exact q9rc_mul_cube_inv q9rcFour (q3kNormBase x) hx hN
  exact q9lr_four_not_norm ⟨_, hy_unit, hNy⟩

/-! ## q9rc-5: ★★★ element-level 位数 3 データ -/

/-- **q9rc-5a（★★★）: 類 [4] の位数ちょうど 3**（genuine ℤ/3 下界の element-level 形）。
    4∉N ∧ 4²∉N ∧ 4³∈N——[4] は L₂^×/N(M^×) で位数 3。 -/
theorem q9rc_order3 :
    (¬ ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9rcFour) ∧
    (¬ ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9rcFourSq) ∧
    (∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9rcFourCube) :=
  ⟨q9lr_four_not_norm, q9rc_foursq_not_norm, q9rc_fourcube_is_norm⟩

/-! ## q9rc-6: ℤ/3 ↪ cokernel（pairwise-distinct 類・element-level） -/

/-- **q9rc-6a: N を法とする合同** b ≡ a （∃ 単数 x, a·N(x) = b）——余核類の相等（element-level）。 -/
def q9rcCongMod (a b : q3rqCar) : Prop :=
  ∃ x : q3kCar, q3kUnitMem x ∧ q3rqMul a (q3kNormBase x) = b

/-- **q9rc-6b: [4³] = [1]**（位数 3 の collapse・witness embed(4)）。 -/
theorem q9rc_cong_cube_one : q9rcCongMod q3rqOne q9rcFourCube := by
  refine ⟨q3kEmbed q9rcFour, q9rc_embed_four_unit, ?_⟩
  rw [q3rq_one_mul, q9ps_normBase_embed]
  rfl

/-- **q9rc-6c: [4] ≠ [1]**（4∉N）。 -/
theorem q9rc_not_cong_01 : ¬ q9rcCongMod q3rqOne q9rcFour := by
  intro h
  obtain ⟨x, hx, he⟩ := h
  rw [q3rq_one_mul] at he
  exact q9lr_four_not_norm ⟨x, hx, he⟩

/-- **q9rc-6d: [4²] ≠ [1]**（4²∉N）。 -/
theorem q9rc_not_cong_02 : ¬ q9rcCongMod q3rqOne q9rcFourSq := by
  intro h
  obtain ⟨x, hx, he⟩ := h
  rw [q3rq_one_mul] at he
  exact q9rc_foursq_not_norm ⟨x, hx, he⟩

/-- **q9rc-6e: [4²] ≠ [4]**（4·Nx = 4² ⟹ Nx = 4、4 消去で 4∉N に矛盾）。 -/
theorem q9rc_not_cong_12 : ¬ q9rcCongMod q9rcFour q9rcFourSq := by
  intro h
  obtain ⟨x, hx, he⟩ := h
  have hcancel : q3kNormBase x = q9rcFour := q9rc_four_cancel he
  exact q9lr_four_not_norm ⟨x, hx, hcancel⟩

/-- **q9rc-6f（★）: ℤ/3 ↪ L₂^×/N(M^×)**——三類 [4⁰],[4¹],[4²] は N を法として pairwise 相異、
    かつ [4³]=[1]（位数 3）。quotient object 未建設のため element-level で表現（honest）。 -/
theorem q9rc_z3_injects :
    q9rcCongMod q3rqOne q9rcFourCube ∧
    (¬ q9rcCongMod q3rqOne q9rcFour) ∧
    (¬ q9rcCongMod q3rqOne q9rcFourSq) ∧
    (¬ q9rcCongMod q9rcFour q9rcFourSq) :=
  ⟨q9rc_cong_cube_one, q9rc_not_cong_01, q9rc_not_cong_02, q9rc_not_cong_12⟩

/-! ## q9rc-7: capstone -/

/-- **q9rc-7a: 余核 ℤ/3 下界データ** — 4∉N・4²∉N・4³∈N（位数 3）と pairwise-distinct 類を束ねる。 -/
structure Q3ReciprocityCokernelRealData where
  /-- 4 は実 ℤ₃-単数。 -/
  four_unit : q3rqUnitMem q9rcFour
  /-- 4 ∉ N（M3 の crux）。 -/
  four_not_norm : ¬ ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9rcFour
  /-- 4² ∉ N（位数 3 の鍵）。 -/
  foursq_not_norm : ¬ ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9rcFourSq
  /-- 4³ ∈ N（位数 3 の collapse）。 -/
  fourcube_is_norm : ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9rcFourCube
  /-- 三類 pairwise 相異（ℤ/3 ↪ cokernel・element-level）。 -/
  z3_injects :
    q9rcCongMod q3rqOne q9rcFourCube ∧
    (¬ q9rcCongMod q3rqOne q9rcFour) ∧
    (¬ q9rcCongMod q3rqOne q9rcFourSq) ∧
    (¬ q9rcCongMod q9rcFour q9rcFourSq)

/-- **q9rc-7b: 見出し実例** — 実 O_M = q3kRing 上の余核 ℤ/3 下界。 -/
def q9rc_data : Q3ReciprocityCokernelRealData where
  four_unit := q9rc_four_unit
  four_not_norm := q9lr_four_not_norm
  foursq_not_norm := q9rc_foursq_not_norm
  fourcube_is_norm := q9rc_fourcube_is_norm
  z3_injects := q9rc_z3_injects

/-- **q9rc-7c: 余核 ℤ/3 下界の存在**（B2 (T2) 下界・[4] 位数 3）。 -/
theorem q9rc_exists : Nonempty Q3ReciprocityCokernelRealData := ⟨q9rc_data⟩

end IUT
