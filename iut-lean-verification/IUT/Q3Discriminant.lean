/-
  IUT/Q3Discriminant.lean — 柱B・B3 実 DISCRIMINANT disc(M/L₂) = N_{M/L₂}(𝔡_{M/L₂})
    （different ideal 𝔡=(π₉⁶) の相対ノルムとして判別式イデアル 𝔇=(λ⁶)⊆O_{L₂} を実建設）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]** — q9di が建てた本物の different ideal
     𝔡_{M/L₂}=(π₉⁶)⊆O_M を、実 3 次ノルム q3kNormBase（N_{M/L₂}: O_M → O_{L₂}・
     Brahmagupta 型乗法性 q3k_normBase_mul）で L₂ 側へ押し下げ、**判別式
     disc(M/L₂) = N_{M/L₂}(𝔡_{M/L₂}) = (N(D)) = (λ⁶) ⊆ O_{L₂}** を本物の環イデアル
     `primeSpecIdeal q3rqRing` として実現する。核心の新実定理は
     (i) N(π₉) = ζ₃−1 = λ·(h,h)（L₂ 一様化子 λ=√−3 の associate・実単数 (h,h), h=2⁻¹）、
     (ii) N(D) = λ⁶·(単数)（disc 生成元の実分解）、(iii) N は 𝔡 を 𝔇 に写す
     （イデアルのノルム関係の元ごとの実証）、(iv) 𝔇 = (N(D)) = (λ⁶) ちょうど
     （associate 両包含・実逆元 q3rqInv）、(v) 鋭さ ¬λ⁷∣N(D)（v_{L₂}(disc)=6 ちょうど・
     ノルム 2 段 + ℤ₃ の 3-正則性 zp_pi_regular による新 U6 型矛盾）。
     主語は実 λ・実 π₉・実 different D=(σπ₉−π₉)(σ²π₉−π₉)・実ノルム——toy 模型
     （Bool 軌道・surrogate 群）を一切使わない（§3 遵守）。

  complete_pct 影響: **B3（audit-decided・予測 +0.01〜0.03・discriminant 実化）**。
     動かす新規内容は「different-discriminant 関係 disc = N(𝔡) を、M 側の
     ideal object（q9di）から L₂ 側の genuine な ideal object 𝔇=(λ⁶) への実ノルム
     押し下げとして割る」こと。B3 は d(M/L₂)=6（q9dv）・d(M/ℚ₃)=9（q9tw）・
     𝔡=(π₉⁶)（q9di）・𝔡⁻¹（q9fc）まで持っていたが、判別式そのもの
     （conductor-discriminant 鎖の右端）は未建設だった。v_{L₂}(disc)=f·d=1·6=6 を
     イデアル等式＋鋭さの実形で閉じる。

  核心の実データ（真水・NEW）:
   * q9ds_zeta_sub_factor — ζ₃−1 = λ·(h,h)（N(π₉) の λ-associate 分解・成分実計算）
   * q9ds_HH_norm / q9ds_HH_unit — N_{L₂/ℚ₃}(h,h) = 4h² = 1（(h,h) は実単数）
   * q9ds_normBase_pi6 — N(π₉⁶) = (N π₉)⁶（ノルム乗法性の 6 冪インスタンス）
   * q9ds_disc_factor — **★ disc 生成元の実分解** N(D) = λ⁶·(単数 (h,h)⁶·N(u*u**))
   * q9dsDiscIdeal — **★ 判別式イデアル 𝔇 = (λ⁶) ∈ primeSpecIdeal q3rqRing**
     （O_{L₂}-イデアル公理 zero/add/smul を実で充足）
   * q9ds_norm_maps_ideal — **★ N(𝔡) ⊆ 𝔇**（x∈𝔡 ⟹ N(x)∈𝔇・イデアルノルムの元ごと実証）
   * q9ds_disc_gen — **★ 𝔇 = (N(D)) = (λ⁶) ちょうど**（associate 両包含・q3rqInv 消費）
   * q9ds_disc_sharp — **★ ¬λ⁷ ∣ N(D)**（v_{L₂}(disc)=6 ちょうど。N を ℚ₃ へもう 1 段
     押し下げ 3⁶·N(U)=3⁷·N(c) とし、ℤ₃ の 3-正則性（zp_pi_regular・regular_mul）で
     3⁶ を消去 → N(U)=3·N(c) → 単数性と矛盾）
   * q9ds_disc_val6 / Q3DiscriminantData — v_{L₂}(disc)=6 ちょうど・capstone（束ね）

  正直な限定（§4 規約により消さない・弱めない・q9di/q9dv/q9tf/q9fc/q3k/q3rq 継承の上に追記のみ）:
  1. **拡大 1 個（M/L₂/ℚ₃）・特定の判別式イデアル (λ⁶) のみ**。一般の判別式理論
     （基底の判別式 det(Tr(eᵢeⱼ))・一般 Dedekind 拡大の disc=N(𝔡) 定理・一般アーベル拡大の
     conductor-discriminant 公式）は範囲外——本ファイルはこの塔の specific な
     disc(M/L₂) を N(D) の生成するイデアルとして建てる。
  2. **「disc = N(𝔡)」はここでは (a) 生成元関係 disc-gen = N(𝔡-gen)（定義 q9dsDisc）、
     (b) N(𝔡)⊆𝔇 の元ごとの写像性 q9ds_norm_maps_ideal、(c) 𝔇=(N D)=(λ⁶) の
     イデアル等式 q9ds_disc_gen の 3 本で表現**する。イデアルの像 N(I) を一般構成して
     イデアル等式 N(𝔡)=𝔇 を抽象的に述べる一般機構（イデアルノルム函手）は建てない。
  3. **可除性形式**: 𝔇 の membership は λ⁶∣x（q9twLamDvd）。L₂ 側の TOTAL な付値関数
     v_{L₂} は建てない（q9v の choice-free 障壁と同型・q9tw 正直限定 4 継承）。
  4. disc(M/ℚ₃) の塔版（f=1: v_{ℚ₃}(disc(M/ℚ₃))=9）は q9tw_disc_M_Q3 が既に可除性形式で
     保持しており、本ファイルは再主張しない（二重計上回避）。ここの新規は M/L₂ 段の
     判別式イデアル 𝔇=(λ⁶) と disc=N(different) 関係の実化。
  5. q9di/q9dv/q9wr/q9ps/q9nf/q3k/q3rq の正直限定を全継承（O_M・O_{L₂} と単数群のみ・
     体化なし・Galois は σ のみ・実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用
  （omega は Nat 原子 2≤3 のみ）。
-/
import IUT.Q3DifferentIdeal
import IUT.Q3TowerDifferentReal
import IUT.Q3UnitTameDecomp
import IUT.RegularPowers
import IUT.EisFaithful

namespace IUT

/-! ## q9ds-0: O_{L₂} 側の環簿記ブリッジ（q3rqMul 形・全て defeq 再輸出） -/

/-- 結合律（q3rqMul 形）。 -/
theorem q9ds_rq_mul_assoc (a b c : q3rqCar) :
    q3rqMul (q3rqMul a b) c = q3rqMul a (q3rqMul b c) := q3rqRing.mul_assoc a b c

/-- 可換律（q3rqMul 形）。 -/
theorem q9ds_rq_mul_comm (a b : q3rqCar) :
    q3rqMul a b = q3rqMul b a := q3rqRing.mul_comm a b

/-- 4 因子入替（q3rqMul 形）。 -/
theorem q9ds_rq_mmmc (a b c d : q3rqCar) :
    q3rqMul (q3rqMul a b) (q3rqMul c d) = q3rqMul (q3rqMul a c) (q3rqMul b d) :=
  CRing.mul_mul_mul_comm q3rqRing a b c d

/-- 左交換（q3rqMul 形）。 -/
theorem q9ds_rq_mul_left_comm (a b c : q3rqCar) :
    q3rqMul a (q3rqMul b c) = q3rqMul b (q3rqMul a c) :=
  CRing.mul_left_comm q3rqRing a b c

/-- 単位律（q3rqMul 形）。 -/
theorem q9ds_rq_one_mul (a : q3rqCar) : q3rqMul q3rqOne a = a := q3rqRing.one_mul a

/-- 零吸収（q3rqMul 形）。 -/
theorem q9ds_rq_mul_zero (a : q3rqCar) : q3rqMul a q3rqZero = q3rqZero :=
  CRing.mul_zero q3rqRing a

/-- 左分配（q3rqMul 形）。 -/
theorem q9ds_rq_left_distrib (a b c : q3rqCar) :
    q3rqMul a (q3rqAdd b c) = q3rqAdd (q3rqMul a b) (q3rqMul a c) :=
  q3rqRing.left_distrib a b c

/-! ## q9ds-1: 冪の骨組（3 乗・6 乗、M 側 π₉⁶ の形を鏡映） -/

/-- 3 乗 t³ = (t·t)·t（q9psPi9Cubed の形の L₂ 側鏡映）。 -/
def q9dsCube (t : q3rqCar) : q3rqCar := q3rqMul (q3rqMul t t) t

/-- 6 乗 t⁶ = t³·t³（q9psPi6 の形の L₂ 側鏡映）。 -/
def q9dsPow6 (t : q3rqCar) : q3rqCar := q3rqMul (q9dsCube t) (q9dsCube t)

/-- 3 乗の乗法性 (ab)³ = a³·b³（4 因子入替 2 回）。 -/
theorem q9ds_cube_mul (a b : q3rqCar) :
    q9dsCube (q3rqMul a b) = q3rqMul (q9dsCube a) (q9dsCube b) := by
  show q3rqMul (q3rqMul (q3rqMul a b) (q3rqMul a b)) (q3rqMul a b)
     = q3rqMul (q3rqMul (q3rqMul a a) a) (q3rqMul (q3rqMul b b) b)
  rw [q9ds_rq_mmmc a b a b,
      q9ds_rq_mmmc (q3rqMul a a) (q3rqMul b b) a b]

/-- 6 乗の乗法性 (ab)⁶ = a⁶·b⁶。 -/
theorem q9ds_pow6_mul (a b : q3rqCar) :
    q9dsPow6 (q3rqMul a b) = q3rqMul (q9dsPow6 a) (q9dsPow6 b) := by
  show q3rqMul (q9dsCube (q3rqMul a b)) (q9dsCube (q3rqMul a b))
     = q3rqMul (q3rqMul (q9dsCube a) (q9dsCube a)) (q3rqMul (q9dsCube b) (q9dsCube b))
  rw [q9ds_cube_mul a b,
      q9ds_rq_mmmc (q9dsCube a) (q9dsCube b) (q9dsCube a) (q9dsCube b)]

/-- 3 乗は単数を保つ。 -/
theorem q9ds_cube_unit {t : q3rqCar} (ht : q3rqUnitMem t) :
    q3rqUnitMem (q9dsCube t) := by
  show q3rqUnitMem (q3rqMul (q3rqMul t t) t)
  exact q3rq_unit_mul (q3rq_unit_mul ht ht) ht

/-- 6 乗は単数を保つ。 -/
theorem q9ds_pow6_unit {t : q3rqCar} (ht : q3rqUnitMem t) :
    q3rqUnitMem (q9dsPow6 t) := by
  show q3rqUnitMem (q3rqMul (q9dsCube t) (q9dsCube t))
  exact q3rq_unit_mul (q9ds_cube_unit ht) (q9ds_cube_unit ht)

/-! ## q9ds-2: N(π₉) = ζ₃−1 = λ·(h,h) — L₂ 一様化子の associate 分解 -/

/-- 実単数 (h,h) = h + h√−3（h = 2⁻¹ ∈ ℤ₃）——ζ₃−1 = λ·(h,h) の単数因子。 -/
def q9dsHH : q3rqCar := ((q3rqHalf, q3rqHalf) : q3rqCar)

/-- 3·h = 1 + h（2h = 1 から）。 -/
theorem q9ds_three_half : z3.mul q3rqThree q3rqHalf = z3.add z3.one q3rqHalf := by
  show z3.mul (z3.add q3rqTwoZ z3.one) q3rqHalf = z3.add z3.one q3rqHalf
  rw [z3.right_distrib q3rqTwoZ z3.one q3rqHalf, q3rq_two_half, z3.one_mul q3rqHalf]

/-- **q9ds-2a（★）: ζ₃−1 = λ·(h,h)**——N(π₉)=ζ₃−1（q9wr_normBase_pi9）が L₂ 一様化子
    λ=√−3 の associate であることの実成分計算。 -/
theorem q9ds_zeta_sub_factor :
    q3rqAdd (q3rqNeg q3rqOne) q3rqZeta = q3rqMul q3rqLambda q9dsHH := by
  apply q3rq_ext
  · show z3.add (z3.neg z3.one) (z3.neg q3rqHalf)
       = z3.add (z3.mul z3.zero q3rqHalf) (z3.mul q3rqD (z3.mul z3.one q3rqHalf))
    rw [z3.zero_mul q3rqHalf,
        z3.zero_add (z3.mul q3rqD (z3.mul z3.one q3rqHalf)),
        z3.one_mul q3rqHalf, q3rq_D_eq, z3.neg_mul q3rqThree q3rqHalf,
        q9ds_three_half, z3.neg_add_dist z3.one q3rqHalf]
  · show z3.add (z3.neg z3.zero) q3rqHalf
       = z3.add (z3.mul z3.zero q3rqHalf) (z3.mul z3.one q3rqHalf)
    rw [z3.neg_zero, z3.zero_add q3rqHalf, z3.zero_mul q3rqHalf,
        z3.zero_add (z3.mul z3.one q3rqHalf), z3.one_mul q3rqHalf]

/-- **q9ds-2b: N_{L₂/ℚ₃}(h,h) = h² + 3h² = 4h² = 1**（(h,h) の単数性の実計算）。 -/
theorem q9ds_HH_norm : q3rqNorm q9dsHH = z3.one := by
  show z3.add (z3.mul q3rqHalf q3rqHalf)
      (z3.neg (z3.mul q3rqD (z3.mul q3rqHalf q3rqHalf))) = z3.one
  rw [q3rq_D_eq, z3.neg_mul q3rqThree (z3.mul q3rqHalf q3rqHalf),
      z3.neg_neg (z3.mul q3rqThree (z3.mul q3rqHalf q3rqHalf)),
      q3rq_three_hsq,
      ← z3.add_assoc (z3.mul q3rqHalf q3rqHalf) q3rqHalf (z3.mul q3rqHalf q3rqHalf),
      z3.add_comm (z3.mul q3rqHalf q3rqHalf) q3rqHalf,
      z3.add_assoc q3rqHalf (z3.mul q3rqHalf q3rqHalf) (z3.mul q3rqHalf q3rqHalf),
      q3rq_hsq_add_hsq, q3rq_half_add_half]

/-- (h,h) は実単数。 -/
theorem q9ds_HH_unit : q3rqUnitMem q9dsHH := by
  show IsZpUnit 3 (q3rqNorm q9dsHH)
  rw [q9ds_HH_norm]
  exact ⟨1, rfl, not_dvd_one 3 (by omega)⟩

/-- **q9ds-2c: N(π₉) = λ·(h,h)**（q9wr_normBase_pi9 と 2a の合成）。 -/
theorem q9ds_norm_pi9_factor :
    q3kNormBase q9psPi9 = q3rqMul q3rqLambda q9dsHH :=
  q9wr_normBase_pi9.trans q9ds_zeta_sub_factor

/-! ## q9ds-3: N(π₉⁶) = (N π₉)⁶ とノルムの 6 冪押し下げ -/

/-- N(π₉³) = (N π₉)³（ノルム乗法性 2 回）。 -/
theorem q9ds_normBase_cubed :
    q3kNormBase q9psPi9Cubed = q9dsCube (q3kNormBase q9psPi9) := by
  show q3kNormBase (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
     = q3rqMul (q3rqMul (q3kNormBase q9psPi9) (q3kNormBase q9psPi9)) (q3kNormBase q9psPi9)
  rw [q3k_normBase_mul (q3kMul q9psPi9 q9psPi9) q9psPi9, q3k_normBase_mul q9psPi9 q9psPi9]

/-- **q9ds-3a: N(π₉⁶) = (N π₉)⁶**（ノルム乗法性の 6 冪インスタンス）。 -/
theorem q9ds_normBase_pi6 :
    q3kNormBase q9psPi6 = q9dsPow6 (q3kNormBase q9psPi9) := by
  show q3kNormBase (q3kMul q9psPi9Cubed q9psPi9Cubed)
     = q3rqMul (q9dsCube (q3kNormBase q9psPi9)) (q9dsCube (q3kNormBase q9psPi9))
  rw [q3k_normBase_mul q9psPi9Cubed q9psPi9Cubed, q9ds_normBase_cubed]

/-! ## q9ds-4: 判別式生成元 disc-gen = N(D) とその実分解 λ⁶·(単数) -/

/-- **判別式生成元** disc(M/L₂) の生成元 = N_{M/L₂}(D)（different-discriminant 関係
    disc = N(𝔡) の生成元レベルの定義的実現）。 -/
def q9dsDisc : q3rqCar := q3kNormBase q9diD

/-- λ⁶ ∈ O_{L₂}（判別式イデアルの標準生成元）。 -/
def q9dsLam6 : q3rqCar := q9dsPow6 q3rqLambda

/-- λ⁷ = λ⁶·λ（鋭さの比較対象）。 -/
def q9dsLam7 : q3rqCar := q3rqMul q9dsLam6 q3rqLambda

/-- disc 生成元の単数因子 U = (h,h)⁶·N(u*·u**)。 -/
def q9dsUnit : q3rqCar := q3rqMul (q9dsPow6 q9dsHH) (q3kNormBase q9diUnit)

/-- N(u*·u**) は実 L₂ 単数（q9di_unit_isUnit の defeq 読み替え）。 -/
theorem q9ds_normUnit_unit : q3rqUnitMem (q3kNormBase q9diUnit) := q9di_unit_isUnit

/-- U は実 L₂ 単数。 -/
theorem q9ds_unit_isUnit : q3rqUnitMem q9dsUnit := by
  show q3rqUnitMem (q3rqMul (q9dsPow6 q9dsHH) (q3kNormBase q9diUnit))
  exact q3rq_unit_mul (q9ds_pow6_unit q9ds_HH_unit) q9ds_normUnit_unit

/-- disc = N(D) は定義そのもの（different-discriminant 関係の定義的アンカー）。 -/
theorem q9ds_disc_eq_norm_different : q9dsDisc = q3kNormBase q9diD := rfl

/-- **q9ds-4a（★ headline）: disc 生成元の実分解 N(D) = λ⁶·U**（U 実単数）。
    D = π₉⁶·(u*u**)（q9di_different_factor）→ N の乗法性 → N(π₉)⁶·N(u*u**) →
    (λ·(h,h))⁶·N(u*u**) = λ⁶·((h,h)⁶·N(u*u**))。 -/
theorem q9ds_disc_factor : q9dsDisc = q3rqMul q9dsLam6 q9dsUnit := by
  show q3kNormBase q9diD
     = q3rqMul (q9dsPow6 q3rqLambda) (q3rqMul (q9dsPow6 q9dsHH) (q3kNormBase q9diUnit))
  rw [q9di_different_factor, q3k_normBase_mul q9psPi6 q9diUnit,
      q9ds_normBase_pi6, q9ds_norm_pi9_factor, q9ds_pow6_mul q3rqLambda q9dsHH,
      q9ds_rq_mul_assoc (q9dsPow6 q3rqLambda) (q9dsPow6 q9dsHH) (q3kNormBase q9diUnit)]

/-! ## q9ds-5: 判別式イデアル 𝔇 = (λ⁶) を本物の環イデアルとして実現 -/

/-- **𝔇 = (λ⁶) の所属述語** x ∈ 𝔇 ⟺ λ⁶ ∣ x（q9twLamDvd・可除性形式）。 -/
def q9dsMem (x : q3rqCar) : Prop := q9twLamDvd q9dsLam6 x

/-- 0 ∈ 𝔇。 -/
theorem q9ds_ideal_zero : q9dsMem q3rqZero :=
  ⟨q3rqZero, (q9ds_rq_mul_zero q9dsLam6).symm⟩

/-- 加法閉性: x,y ∈ 𝔇 ⟹ x+y ∈ 𝔇。 -/
theorem q9ds_ideal_add (x y : q3rqCar) (hx : q9dsMem x) (hy : q9dsMem y) :
    q9dsMem (q3rqAdd x y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨q3rqAdd a b, ?_⟩
  rw [ha, hb]
  exact (q9ds_rq_left_distrib q9dsLam6 a b).symm

/-- O_{L₂}-環倍吸収: x ∈ 𝔇 ⟹ r·x ∈ 𝔇。 -/
theorem q9ds_ideal_smul (r x : q3rqCar) (hx : q9dsMem x) : q9dsMem (q3rqMul r x) := by
  obtain ⟨c, hc⟩ := hx
  refine ⟨q3rqMul r c, ?_⟩
  rw [hc]
  exact q9ds_rq_mul_left_comm r q9dsLam6 c

/-- **q9ds-5a（★ IDEAL OBJECT）: 判別式イデアル 𝔇 = disc(M/L₂) = (λ⁶) を
    本物の環イデアル**（`primeSpecIdeal q3rqRing`・O_{L₂}-イデアル公理 zero/add/smul）
    として実現。 -/
def q9dsDiscIdeal : primeSpecIdeal q3rqRing where
  mem := q9dsMem
  zero_mem := q9ds_ideal_zero
  add_mem := q9ds_ideal_add
  smul_mem := q9ds_ideal_smul

/-- disc 生成元は 𝔇 に属する（N(D) ∈ (λ⁶)）。 -/
theorem q9ds_disc_mem : q9dsMem q9dsDisc := ⟨q9dsUnit, q9ds_disc_factor⟩

/-! ## q9ds-6: ★ N は 𝔡 を 𝔇 へ写す（disc = N(𝔡) の元ごとの実証） -/

/-- **q9ds-6（★）: N(𝔡) ⊆ 𝔇**——x ∈ 𝔡=(π₉⁶) なら N_{M/L₂}(x) ∈ 𝔇=(λ⁶)。
    different ideal のノルムが判別式イデアルに入ることの元ごとの実証
    （x=π₉⁶·c → N(x)=(λ·(h,h))⁶·N(c)=λ⁶·((h,h)⁶·N(c))）。 -/
theorem q9ds_norm_maps_ideal (x : q3kCar) (hx : q9diMem x) :
    q9dsMem (q3kNormBase x) := by
  obtain ⟨c, hc⟩ := hx
  refine ⟨q3rqMul (q9dsPow6 q9dsHH) (q3kNormBase c), ?_⟩
  show q3kNormBase x
     = q3rqMul (q9dsPow6 q3rqLambda) (q3rqMul (q9dsPow6 q9dsHH) (q3kNormBase c))
  rw [hc, q9nf_pipow6_eq, q3k_normBase_mul q9psPi6 c,
      q9ds_normBase_pi6, q9ds_norm_pi9_factor, q9ds_pow6_mul q3rqLambda q9dsHH,
      q9ds_rq_mul_assoc (q9dsPow6 q3rqLambda) (q9dsPow6 q9dsHH) (q3kNormBase c)]

/-! ## q9ds-7: ★ 𝔇 = (N(D)) = (λ⁶) ちょうど（associate 両包含） -/

/-- **q9ds-7（★ headline）: 𝔇 = (N(D)) = (λ⁶) ちょうど**——disc 生成元 N(D) で生成される
    イデアル (N(D))={x : N(D)∣x} が (λ⁶) と一致（N(D)=λ⁶·U・U 実単数の associate
    両包含・⟸ 向きは実逆元 q3rqInv を消費）。disc(M/L₂) が genuine な ideal-object
    として (λ⁶) に等しいことの実証。 -/
theorem q9ds_disc_gen (x : q3rqCar) : q9twLamDvd q9dsDisc x ↔ q9dsMem x := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    refine ⟨q3rqMul q9dsUnit c, ?_⟩
    rw [hc, q9ds_disc_factor, q9ds_rq_mul_assoc q9dsLam6 q9dsUnit c]
  · intro h
    obtain ⟨c, hc⟩ := h
    refine ⟨q3rqMul (q3rqInv q9dsUnit q9ds_unit_isUnit) c, ?_⟩
    rw [hc, q9ds_disc_factor,
        q9ds_rq_mul_assoc q9dsLam6 q9dsUnit
          (q3rqMul (q3rqInv q9dsUnit q9ds_unit_isUnit) c),
        ← q9ds_rq_mul_assoc q9dsUnit (q3rqInv q9dsUnit q9ds_unit_isUnit) c,
        q9ds_rq_mul_comm q9dsUnit (q3rqInv q9dsUnit q9ds_unit_isUnit),
        q3rq_inv_mul q9dsUnit q9ds_unit_isUnit, q9ds_rq_one_mul c]

/-! ## q9ds-8: ★ 鋭さ ¬λ⁷ ∣ N(D)（v_{L₂}(disc) = 6 ちょうど） -/

/-- N(x³)（L₂→ℚ₃ ノルムの 3 冪展開）。 -/
theorem q9ds_norm_cube_rq (t : q3rqCar) :
    q3rqNorm (q9dsCube t)
      = z3.mul (z3.mul (q3rqNorm t) (q3rqNorm t)) (q3rqNorm t) := by
  show q3rqNorm (q3rqMul (q3rqMul t t) t) = _
  rw [q3rq_norm_mul (q3rqMul t t) t, q3rq_norm_mul t t]

/-- 3³ ∈ ℤ₃（ℚ₃ 側の判別式ノルムの半分）。 -/
def q9dsThreeCubeZ : z3.carrier := z3.mul (z3.mul q3rqThree q3rqThree) q3rqThree

/-- 3⁶ ∈ ℤ₃。 -/
def q9dsThreeSixZ : z3.carrier := z3.mul q9dsThreeCubeZ q9dsThreeCubeZ

/-- N_{L₂/ℚ₃}(λ⁶) = 3⁶（N(λ)=3 の 6 冪）。 -/
theorem q9ds_norm_lam6 : q3rqNorm q9dsLam6 = q9dsThreeSixZ := by
  show q3rqNorm (q3rqMul (q9dsCube q3rqLambda) (q9dsCube q3rqLambda))
     = z3.mul (z3.mul (z3.mul q3rqThree q3rqThree) q3rqThree)
              (z3.mul (z3.mul q3rqThree q3rqThree) q3rqThree)
  rw [q3rq_norm_mul (q9dsCube q3rqLambda) (q9dsCube q3rqLambda),
      q9ds_norm_cube_rq q3rqLambda, q9ut_norm_lambda]

/-- N_{L₂/ℚ₃}(λ⁷) = 3⁶·3。 -/
theorem q9ds_norm_lam7 : q3rqNorm q9dsLam7 = z3.mul q9dsThreeSixZ q3rqThree := by
  show q3rqNorm (q3rqMul q9dsLam6 q3rqLambda) = z3.mul q9dsThreeSixZ q3rqThree
  rw [q3rq_norm_mul q9dsLam6 q3rqLambda, q9ds_norm_lam6, q9ut_norm_lambda]

/-- **ℤ₃ の 3 = zpPi 3**（実完備化対角像との同定・レベルごとに代表 (1+1)+1 = 3）。 -/
theorem q9ds_three_eq_pi : q3rqThree = zpPi 3 := by
  apply Subtype.ext
  funext n
  rfl

/-- **3 は ℤ₃ の正則元**（zp_pi_regular の q3rqThree 形・3y=0 ⟹ y=0）。 -/
theorem q9ds_three_regular : IsRegularElem z3 q3rqThree := by
  intro h hh
  apply zp_pi_regular 3 (by omega) h
  rw [(zpRing 3).mul_comm (zpPi 3) h, ← q9ds_three_eq_pi]
  exact hh

/-- 3⁶ は ℤ₃ の正則元（regular_mul の 6 冪合成）。 -/
theorem q9ds_threeSix_regular : IsRegularElem z3 q9dsThreeSixZ := by
  have hc : IsRegularElem z3 q9dsThreeCubeZ :=
    regular_mul z3 (regular_mul z3 q9ds_three_regular q9ds_three_regular)
      q9ds_three_regular
  exact regular_mul z3 hc hc

/-- **q9ds-8（★）: ¬λ⁷ ∣ N(D)**——v_{L₂}(disc(M/L₂)) = 6 **ちょうど**。
    もし N(D)=λ⁷·c なら、ℚ₃ へのノルム 2 段押し下げで 3⁶·N(U) = 3⁶·(3·N(c))、
    ℤ₃ の 3-正則性（zp_pi_regular）で 3⁶ を消去して N(U) = 3·N(c)——
    U の単数性（q9ds_unit_isUnit）と 3·s 非単数（q9wr_three_mul_not_unit）が矛盾。 -/
theorem q9ds_disc_sharp : ¬ q9twLamDvd q9dsLam7 q9dsDisc := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hN1 : q3rqNorm q9dsDisc = z3.mul q9dsThreeSixZ (q3rqNorm q9dsUnit) := by
    rw [q9ds_disc_factor, q3rq_norm_mul q9dsLam6 q9dsUnit, q9ds_norm_lam6]
  have hN2 : q3rqNorm q9dsDisc
      = z3.mul (z3.mul q9dsThreeSixZ q3rqThree) (q3rqNorm c) := by
    rw [hc, q3rq_norm_mul q9dsLam7 c, q9ds_norm_lam7]
  have heq : z3.mul q9dsThreeSixZ (q3rqNorm q9dsUnit)
      = z3.mul q9dsThreeSixZ (z3.mul q3rqThree (q3rqNorm c)) := by
    have h := hN1.symm.trans hN2
    rw [z3.mul_assoc q9dsThreeSixZ q3rqThree (q3rqNorm c)] at h
    exact h
  have hzero : z3.mul q9dsThreeSixZ
      (z3.add (q3rqNorm q9dsUnit) (z3.neg (z3.mul q3rqThree (q3rqNorm c))))
      = z3.zero := by
    rw [z3.left_distrib q9dsThreeSixZ (q3rqNorm q9dsUnit)
          (z3.neg (z3.mul q3rqThree (q3rqNorm c))),
        z3.mul_neg q9dsThreeSixZ (z3.mul q3rqThree (q3rqNorm c)), heq]
    exact CRing.add_neg z3 (z3.mul q9dsThreeSixZ (z3.mul q3rqThree (q3rqNorm c)))
  have hdiff : z3.add (q3rqNorm q9dsUnit)
      (z3.neg (z3.mul q3rqThree (q3rqNorm c))) = z3.zero := by
    apply q9ds_threeSix_regular
    rw [z3.mul_comm
        (z3.add (q3rqNorm q9dsUnit) (z3.neg (z3.mul q3rqThree (q3rqNorm c))))
        q9dsThreeSixZ]
    exact hzero
  have hNU : q3rqNorm q9dsUnit = z3.mul q3rqThree (q3rqNorm c) :=
    CRing.eq_of_sub_eq_zero z3 hdiff
  have hUnit : IsZpUnit 3 (q3rqNorm q9dsUnit) := q9ds_unit_isUnit
  rw [hNU] at hUnit
  exact q9wr_three_mul_not_unit (q3rqNorm c) hUnit

/-- **q9ds-8b（★）: v_{L₂}(disc(M/L₂)) = 6 ちょうど**（λ⁶∣N(D) ∧ ¬λ⁷∣N(D)）。 -/
theorem q9ds_disc_val6 :
    q9dsMem q9dsDisc ∧ ¬ q9twLamDvd q9dsLam7 q9dsDisc :=
  ⟨q9ds_disc_mem, q9ds_disc_sharp⟩

/-! ## q9ds-9: capstone（束ね・新規証明ゼロ）

  disc(M/ℚ₃) の塔版（v_{ℚ₃}=9）は q9tw_disc_M_Q3 が可除性形式で保持済み（再主張しない）。
  一般アーベル拡大の conductor-discriminant 公式・イデアルノルム函手は範囲外
  （正直な限定 1–2・toy を作らず honest scope）。 -/

/-- **q9ds-9: 実判別式データ**——disc = N(𝔡) の生成元関係・λ⁶·単数分解・本物の
    環イデアル 𝔇=(λ⁶)・N(𝔡)⊆𝔇・𝔇=(N D) ちょうど・鋭さ v_{L₂}(disc)=6・
    f=1 算術 6=1·6 を束ねる（新規証明ゼロ）。 -/
structure Q3DiscriminantData where
  /-- disc 生成元 = N_{M/L₂}(D)（different-discriminant 関係の定義的アンカー）。 -/
  disc_eq_norm : q9dsDisc = q3kNormBase q9diD
  /-- N(D) = λ⁶·U（U 実単数）。 -/
  disc_factor : q9dsDisc = q3rqMul q9dsLam6 q9dsUnit
  /-- U は実単数。 -/
  unit_isUnit : q3rqUnitMem q9dsUnit
  /-- 本物の環イデアル対象 𝔇 = (λ⁶) ∈ `primeSpecIdeal q3rqRing`。 -/
  ideal : primeSpecIdeal q3rqRing
  /-- N(D) ∈ 𝔇。 -/
  disc_mem : q9dsMem q9dsDisc
  /-- N(𝔡) ⊆ 𝔇（元ごとのイデアルノルム関係）。 -/
  norm_maps : ∀ x : q3kCar, q9diMem x → q9dsMem (q3kNormBase x)
  /-- 𝔇 = (N(D)) = (λ⁶) ちょうど（associate 両包含）。 -/
  gen_eq : ∀ x : q3rqCar, q9twLamDvd q9dsDisc x ↔ q9dsMem x
  /-- ¬λ⁷ ∣ N(D)（v_{L₂}(disc)=6 ちょうど）。 -/
  sharp : ¬ q9twLamDvd q9dsLam7 q9dsDisc
  /-- f(M/L₂)=1 完全分岐: v_{L₂}(disc) = f·d(M/L₂) = 1·6 = 6。 -/
  disc_exp : (6 : Nat) = 1 * 6

/-- **見出し実例** — 実 M/L₂ 上の genuine な判別式イデアル disc(M/L₂)=N(𝔡)=(λ⁶)。 -/
def q9ds_data : Q3DiscriminantData where
  disc_eq_norm := q9ds_disc_eq_norm_different
  disc_factor := q9ds_disc_factor
  unit_isUnit := q9ds_unit_isUnit
  ideal := q9dsDiscIdeal
  disc_mem := q9ds_disc_mem
  norm_maps := q9ds_norm_maps_ideal
  gen_eq := q9ds_disc_gen
  sharp := q9ds_disc_sharp
  disc_exp := rfl

/-- **実判別式データの存在**（disc(M/L₂) = N(𝔡) = (λ⁶) を本物の環イデアルとして）。 -/
theorem q9ds_exists : Nonempty Q3DiscriminantData := ⟨q9ds_data⟩

end IUT
