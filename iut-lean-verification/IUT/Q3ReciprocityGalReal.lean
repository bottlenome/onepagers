/-
  IUT/Q3ReciprocityGalReal.lean — 柱B・B2 M4b: 局所相互律の対応 Gal(M/L₂) ↪ L₂^×/N(M^×)
    （audit cap (a) を閉じる——q9rcCongMod を genuine 同値関係へ・q9kdG↪cokernel を
     単射群準同型（mod N）として建設）

  ── 主要成果の分類: **[実／(a) 昇格]**。
  audit/reaudit-q9rc-b2-m4-order3-2026-07-11.md（s_B2=0.30・cap (a):「商群対象なし
  （q9rcCongMod が同値関係と未証明）・正規化 Gal(M/L₂)↪cokernel 対応なし」）を、
  **部分レベルで閉じる**。M3（q9lr: 4∉N）・M4（q9rc: [4] 位数 3）の element-level 内容を、
   (1) q9rcCongMod が実 O_M ノルム群を法とする genuine 同値関係（refl/symm/trans）、
   (2) 乗法整合性（cong_mul——商への群演算の降下データ）、
   (3) 単射群準同型（mod N）φ = q9rgPhi : Gal(M/L₂) = q9kdG ↪ L₂^×/N(M^×)、
  へ昇格する。φ の像は位数 3 の部分群 ⟨[4]⟩＝{[1],[4],[16]}。toy 主語なし——主語は実
  q9kdG（実環自己同型 σ の 3 元群）・実 q3rqMul・実 3 次ノルム q3kNormBase。

  complete_pct 影響: **B2 0.30→（独立監査次第・予測 +0.02〜0.05・cap(a) 解消）**。
  M4 は cokernel の ℤ/3 下界を element-level で確立した。本 M4b は同値関係＋単射準同型
  へ昇格し、「Gal ↪ cokernel」という本物の相互律対応（部分群レベル）を閉じる。

  真水（本物へ昇格・新規建設）:
   * q9rg_cong_refl / _symm / _trans（★ q9rcCongMod が genuine 同値関係）
   * q9rg_cong_mul（★ 乗法整合——商群演算の降下データ）
   * q9rgPhi（Gal → 代表元 e↦1, s↦4, s2↦16 = 4^index）
   * q9rg_hom（★★ φ は準同型 mod N——9 ケース・巻き戻し 4³≡1 を q9rc_cong_cube_one で処理）
   * q9rg_inj（★★ φ は類上単射——9 ケース・q9rc_not_cong_* で相異）
   * q9rg_gal_embeds（★★★ Gal ↪ cokernel の単射群準同型（mod N）の束ね）
   * Q3ReciprocityGalRealData（capstone）

  正直な限定（§4 規約により消さない・弱めない・q9rc/q9lr/q9rf/q9gn/q9kd/q3k/q3rq 継承の上に追記のみ）:
  1. **これは Gal ↪ cokernel（位数 3 部分群 ⟨[4]⟩ への単射準同型）であって Gal ≅ cokernel ではない**。
     全射性（cokernel = ちょうど ℤ/3・指数 ≤3・U_{L₂}^(3)⊆N・Artin 写像の正規化）は
     **T3/research（範囲外・主張しない）**。φ の像は ⟨[4]⟩ に限る。
  2. **量化は x ∈ O_M（整元 = q3kCar）に限る**（M3 から継承）。M^× 自体（分数元）は未 wire。
  3. **literal な Quotient 型は建設しない**。同値関係（refl/symm/trans）＋乗法整合（cong_mul）
     ＋単射準同型（hom/inj）は「商群の完全なデータ」だが、Quotient オブジェクトそのものは
     未構成——honest limitation として明記。
  4. q9rc/q9lr/q9rf/q9gn/q9kd/q3k/q3rq の正直限定を全継承（O_M と M^× のみ・体化なし・
     σ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・単一拡大 M/L₂/ℚ₃）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3ReciprocityCokernelReal
import IUT.Q3KummerDualityReal

namespace IUT

/-! ## q9rg-0: q3rq 乗法補題（q3rqMul は q3rqRing.mul と定義的に等しい） -/

/-- q3rq 乗法の結合律（q3rqMul 版）。 -/
theorem q9rg_mul_assoc (a b c : q3rqCar) :
    q3rqMul (q3rqMul a b) c = q3rqMul a (q3rqMul b c) :=
  q3rqRing.mul_assoc a b c

/-- q3rq 乗法の可換律（q3rqMul 版）。 -/
theorem q9rg_mul_comm (a b : q3rqCar) : q3rqMul a b = q3rqMul b a :=
  q3rqRing.mul_comm a b

/-! ## q9rg-1: q9rcCongMod は実 O_M ノルム群を法とする genuine 同値関係 -/

/-- **q9rg-1a（★）: 反射律** a ≡ a（witness 1・N(1)=1・a·1=a）。 -/
theorem q9rg_cong_refl (a : q3rqCar) : q9rcCongMod a a :=
  ⟨q3kOne, q3k_unit_one, by rw [q3k_normBase_one]; exact q3rq_mul_one a⟩

/-- **q9rg-1b（★）: 対称律** a ≡ b ⟹ b ≡ a（witness x⁻¹・N(x)·N(x⁻¹)=N(x·x⁻¹)=N(1)=1）。 -/
theorem q9rg_cong_symm (a b : q3rqCar) (h : q9rcCongMod a b) : q9rcCongMod b a := by
  obtain ⟨x, hx, he⟩ := h
  refine ⟨q3kInv x hx, q3k_unit_inv x hx, ?_⟩
  have hN : q3rqMul (q3kNormBase x) (q3kNormBase (q3kInv x hx)) = q3rqOne := by
    rw [← q3k_normBase_mul x (q3kInv x hx), q3k_inv_mul x hx, q3k_normBase_one]
  rw [← he, q9rg_mul_assoc a (q3kNormBase x) (q3kNormBase (q3kInv x hx)), hN, q3rq_mul_one]

/-- **q9rg-1c（★）: 推移律** a ≡ b, b ≡ c ⟹ a ≡ c（witness 合成 x·y・N(x·y)=N(x)·N(y)）。 -/
theorem q9rg_cong_trans (a b c : q3rqCar)
    (h1 : q9rcCongMod a b) (h2 : q9rcCongMod b c) : q9rcCongMod a c := by
  obtain ⟨x, hx, hex⟩ := h1
  obtain ⟨y, hy, hey⟩ := h2
  refine ⟨q3kMul x y, q3k_unit_mul hx hy, ?_⟩
  rw [q3k_normBase_mul x y, ← q9rg_mul_assoc a (q3kNormBase x) (q3kNormBase y), hex, hey]

/-- **q9rg-1d（★）: 乗法整合** a ≡ b, c ≡ d ⟹ a·c ≡ b·d（商群演算の降下データ・witness x·y）。 -/
theorem q9rg_cong_mul (a b c d : q3rqCar)
    (h1 : q9rcCongMod a b) (h2 : q9rcCongMod c d) :
    q9rcCongMod (q3rqMul a c) (q3rqMul b d) := by
  obtain ⟨x, hx, hex⟩ := h1
  obtain ⟨y, hy, hey⟩ := h2
  refine ⟨q3kMul x y, q3k_unit_mul hx hy, ?_⟩
  rw [q3k_normBase_mul x y, q3rq_mmmc a c (q3kNormBase x) (q3kNormBase y), hex, hey]

/-! ## q9rg-2: 相互律の埋め込み Gal(M/L₂) ↪ cokernel -/

/-- **q9rg-2a: φ : Gal → 代表元** e↦1, s↦4, s2↦16（＝ 4^index・⟨[4]⟩ への写像）。 -/
def q9rgPhi : q9kdGCar → q3rqCar
  | .e => q3rqOne
  | .s => q9rcFour
  | .s2 => q9rcFourSq

/-- **q9rg-2b（★★）: φ は準同型 mod N** φ(g·h) ≡ φ(g)·φ(h)。
    非巻き戻しは等号（refl-cong）、巻き戻し（4³≡1）は q9rc_cong_cube_one を用いる。 -/
theorem q9rg_hom (g h : q9kdGCar) :
    q9rcCongMod (q9rgPhi (q9kdGMul g h)) (q3rqMul (q9rgPhi g) (q9rgPhi h)) := by
  cases g with
  | e =>
    cases h with
    | e =>
      show q9rcCongMod q3rqOne (q3rqMul q3rqOne q3rqOne)
      rw [q3rq_mul_one q3rqOne]; exact q9rg_cong_refl q3rqOne
    | s =>
      show q9rcCongMod q9rcFour (q3rqMul q3rqOne q9rcFour)
      rw [q3rq_one_mul q9rcFour]; exact q9rg_cong_refl q9rcFour
    | s2 =>
      show q9rcCongMod q9rcFourSq (q3rqMul q3rqOne q9rcFourSq)
      rw [q3rq_one_mul q9rcFourSq]; exact q9rg_cong_refl q9rcFourSq
  | s =>
    cases h with
    | e =>
      show q9rcCongMod q9rcFour (q3rqMul q9rcFour q3rqOne)
      rw [q3rq_mul_one q9rcFour]; exact q9rg_cong_refl q9rcFour
    | s =>
      -- gh = s2 = 16, RHS = 4·4 = 16（等号・refl-cong）
      exact q9rg_cong_refl q9rcFourSq
    | s2 =>
      -- gh = e = 1, RHS = 4·16 = 16·4 = 64 ≡ 1（巻き戻し・cube_one + comm）
      show q9rcCongMod q3rqOne (q3rqMul q9rcFour q9rcFourSq)
      rw [q9rg_mul_comm q9rcFour q9rcFourSq]
      exact q9rc_cong_cube_one
  | s2 =>
    cases h with
    | e =>
      show q9rcCongMod q9rcFourSq (q3rqMul q9rcFourSq q3rqOne)
      rw [q3rq_mul_one q9rcFourSq]; exact q9rg_cong_refl q9rcFourSq
    | s =>
      -- gh = e = 1, RHS = 16·4 = 64 ≡ 1（巻き戻し・cube_one 直接）
      exact q9rc_cong_cube_one
    | s2 =>
      -- gh = s = 4, RHS = 16·16 = 256 = 4·64 ≡ 4·1 = 4（巻き戻し・cong_mul + cube_one）
      have h256 : q3rqMul q9rcFourSq q9rcFourSq = q3rqMul q9rcFour q9rcFourCube := by
        show q3rqMul (q3rqMul q9rcFour q9rcFour) (q3rqMul q9rcFour q9rcFour)
            = q3rqMul q9rcFour (q3rqMul (q3rqMul q9rcFour q9rcFour) q9rcFour)
        rw [q9rg_mul_assoc q9rcFour q9rcFour (q3rqMul q9rcFour q9rcFour),
            ← q9rg_mul_assoc q9rcFour q9rcFour q9rcFour]
      have base : q9rcCongMod (q3rqMul q9rcFour q3rqOne) (q3rqMul q9rcFour q9rcFourCube) :=
        q9rg_cong_mul q9rcFour q9rcFour q3rqOne q9rcFourCube
          (q9rg_cong_refl q9rcFour) q9rc_cong_cube_one
      rw [q3rq_mul_one q9rcFour, ← h256] at base
      exact base

/-- **q9rg-2c（★★）: φ は類上単射** φ(g) ≡ φ(h) ⟹ g = h。
    相異 g,h は q9rc_not_cong_* で非合同（+ 対称律）——同一 g,h は自明。 -/
theorem q9rg_inj (g h : q9kdGCar)
    (hcong : q9rcCongMod (q9rgPhi g) (q9rgPhi h)) : g = h := by
  cases g with
  | e =>
    cases h with
    | e => rfl
    | s => exact absurd hcong q9rc_not_cong_01
    | s2 => exact absurd hcong q9rc_not_cong_02
  | s =>
    cases h with
    | e => exact absurd (q9rg_cong_symm _ _ hcong) q9rc_not_cong_01
    | s => rfl
    | s2 => exact absurd hcong q9rc_not_cong_12
  | s2 =>
    cases h with
    | e => exact absurd (q9rg_cong_symm _ _ hcong) q9rc_not_cong_02
    | s => exact absurd (q9rg_cong_symm _ _ hcong) q9rc_not_cong_12
    | s2 => rfl

/-- **q9rg-2d（★★★）: Gal(M/L₂) ↪ L₂^×/N(M^×)** — 単射群準同型（mod N）の束ね:
    (1) φ の準同型性（乗法 mod N）、(2) φ の類上単射性、(3) φ(e) = 1（単位元保存）。
    φ の像は位数 3 の部分群 ⟨[4]⟩＝{[1],[4],[16]}。**これは Gal ↪ cokernel であって
    Gal ≅ cokernel ではない**（全射性 = T3/research・範囲外）。 -/
theorem q9rg_gal_embeds :
    (∀ g h, q9rcCongMod (q9rgPhi (q9kdGMul g h)) (q3rqMul (q9rgPhi g) (q9rgPhi h)))
    ∧ (∀ g h, q9rcCongMod (q9rgPhi g) (q9rgPhi h) → g = h)
    ∧ q9rgPhi q9kdGCar.e = q3rqOne :=
  ⟨q9rg_hom, q9rg_inj, rfl⟩

/-! ## q9rg-3: capstone -/

/-- **q9rg-3a: 相互律対応データ束ね** — 同値関係（refl/symm/trans）＋乗法整合＋単射群準同型。 -/
structure Q3ReciprocityGalRealData where
  /-- q9rcCongMod は反射的。 -/
  cong_refl : ∀ a, q9rcCongMod a a
  /-- q9rcCongMod は対称的。 -/
  cong_symm : ∀ a b, q9rcCongMod a b → q9rcCongMod b a
  /-- q9rcCongMod は推移的。 -/
  cong_trans : ∀ a b c, q9rcCongMod a b → q9rcCongMod b c → q9rcCongMod a c
  /-- q9rcCongMod は乗法整合（商群演算の降下データ）。 -/
  cong_mul : ∀ a b c d, q9rcCongMod a b → q9rcCongMod c d →
    q9rcCongMod (q3rqMul a c) (q3rqMul b d)
  /-- φ は準同型 mod N。 -/
  hom : ∀ g h, q9rcCongMod (q9rgPhi (q9kdGMul g h)) (q3rqMul (q9rgPhi g) (q9rgPhi h))
  /-- φ は類上単射（Gal ↪ cokernel）。 -/
  inj : ∀ g h, q9rcCongMod (q9rgPhi g) (q9rgPhi h) → g = h
  /-- φ は単位元を保存（φ(e) = 1）。 -/
  phi_one : q9rgPhi q9kdGCar.e = q3rqOne

/-- **q9rg-3b: 見出し実例** — 実 q9kdG = Gal(M/L₂) の cokernel への単射埋め込み。 -/
def q9rg_data : Q3ReciprocityGalRealData where
  cong_refl := q9rg_cong_refl
  cong_symm := q9rg_cong_symm
  cong_trans := q9rg_cong_trans
  cong_mul := q9rg_cong_mul
  hom := q9rg_hom
  inj := q9rg_inj
  phi_one := rfl

/-- **q9rg-3c: 相互律対応（部分群レベル）の存在**（B2 cap(a) 解消・Gal ↪ ⟨[4]⟩）。 -/
theorem q9rg_exists : Nonempty Q3ReciprocityGalRealData := ⟨q9rg_data⟩

end IUT
