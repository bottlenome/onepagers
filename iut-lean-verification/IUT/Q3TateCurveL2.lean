/-
  IUT/Q3TateCurveL2.lean — R2b（level-3 実 Tate 曲線 E₂₇ = L₂^×/27^ℤ・q=27 立方トリック）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、R1 の実分岐 2 次局所
     拡大 L₂^× = q3rqLx = ℤ(v_λ) × U₂ の上に、level-3 の実 Tate 曲線
     E₂₇ = L₂^×/27^ℤ を quotientGroupN の一般部品で**本物の商群**として建てる。
     27 = q3tQ 3 = 3³ を選ぶ立方トリック（§2(b)）により q^{1/3}=3 が ℚ₃ 内で実になり、
     分岐 3 次拡大なしに level-3 が L₂ 単独で閉じる。3-torsion E₂₇[3] の実生成元
     [ζ₃]（R1 の実 ζ₃）と [3]（3³=27=q ゆえ位数 3）を実に取り、両者の位数ちょうど 3
     を非自明性込みで証明する。toy 主語なし——主語は実 q3rqLx（実 z3 = zpRing 3 上）。）

  complete_pct 影響: **R2b foundation**（level-3 テータ群 R3 が乗る中心対象＝実 E₂₇ の
  建設）。own move ~0（基盤・kill は未達）。R1→R4 の ℤ₃^× kill キャンペーンの舞台。
  q=27 は §2(b) の忠実部分ケース（[EtTh] の q^{1/l} 添加の full-faithful 版は named
  future target）。本ラウンドは「complete_pct 0 前進（骨格でなく本物基盤の先行建設）」と
  正直申告する。

  内容（q3tCurve = level-2 テンプレートの L₂^× 版）:
   * q3tlComm / q3tlNormal            — L₂^× は可換・可換群では任意部分群が正規
   * q3tlNegOneU / q3tl3 / q3tlQ       — 単数 −1・元 3=(2,−1)・27=(6,−1)（群提示座標）
   * q3tl_cube_elt                     — **27 = 3³**（(2,−1)³=(6,−1)）
   * q3tlSubgroup / q3tlCurve          — 27^ℤ ⊂ L₂^×・**E₂₇ = L₂^×/27^ℤ**
   * q3tlProj / q3tl_proj_surjective   — 射影（全射）
   * q3tl_curve_abelian / q3tl_period  — E₂₇ アーベル・周期性 [x]=[27x]
   * q3tlZeta3 / q3tl3pt               — 3-torsion 点 [ζ₃]・[3]
   * q3tl_zeta3_tor / q3tl_3pt_tor     — **[ζ₃]³=1・[3]³=1**（ζ₃³=1・3³=27=q）
   * q3tl_zeta3_ne_one / q3tl_3pt_ne_one — **位数ちょうど 3**（非自明・付値成分 6ℤ で分離）
   * Q3TateCurveL2Data / q3tlData / q3tl_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・追記のみ）:
  1. **foundation（kill は未達）**。E₂₇ と実 3-torsion 点は実在するが、テータ群・
     mono-theta 剛性・ℤ₃^× kill そのものは後続 R3/R4。本ファイルは何も殺さない。
  2. **q=27 は忠実部分ケース**（§2(b)）。q^{1/3}=3∈ℚ₃ の立方トリックであって [EtTh] の
     q 固定 q^{1/l} 添加そのものではない。6 次暴分岐体経路は full-faithful 版の named target。
  3. **L₂ level のみ**。μ_{3ⁿ}（n≥2・wild）・full ℤ₃^× kill は F-wild の後続 named target。
  4. **E₂₇[3] ≅ (ℤ/3)² の完全分類は主張しない**。実生成元 [ζ₃]・[3] の位数ちょうど 3 と、
     付値成分による [3]・[ζ₃] の非自明性までを本物に証明する。独立性（[ζ₃]∉⟨[3]⟩）と
     網羅性（全 3-torsion が [ζ₃^i 3^j] 形）は R3 後続（過大主張しない）。
  5. **テータ群・実テータ関数・π₁ 同定・Galois 作用は依然ゼロ**（R1/q3th/q3mr の正直限定を継承）。
  6. **K-point の影**（群提示 ℤ×U₂ の商であって {x:L₂ // x≠0} の商そのものではない・
     A2 恒久限定を継承）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3RamifiedQuadratic
import IUT.Q3Mu3Completeness

namespace IUT

/-! ## q3tl-0: 単数 −1 ∈ U₂ と level-3 の群元 3, 27 -/

/-- **−1 ∈ ℤ₃^×**（レベル 1 剰余 [−1]・3∤−1）。 -/
theorem q3tl_neg_one_zpunit : IsZpUnit 3 (z3.neg z3.one) := by
  refine ⟨-1, ?_, q3t_three_not_dvd_neg_one⟩
  show (z3.neg z3.one).val 1 = Quot.mk (modCong (3 ^ 1)).rel (-1)
  rfl

/-- **q3tl-0a: 単数 −1 ∈ U₂**（=(−1,0)・N=1）。3=−λ² の単数部・27 の単数部。 -/
def q3tlNegOneU : q3rqU.carrier :=
  ⟨((z3.neg z3.one, z3.zero) : q3rqCar),
    q3rq_pair_unit (z3.neg z3.one) q3tl_neg_one_zpunit⟩

/-- **(−1)² = 1 in U₂**。 -/
theorem q3tl_negU_sq : q3rqU.mul q3tlNegOneU q3tlNegOneU = q3rqU.one := by
  apply Subtype.ext
  show q3rqMul ((z3.neg z3.one, z3.zero) : q3rqCar) ((z3.neg z3.one, z3.zero) : q3rqCar)
      = ((z3.one, z3.zero) : q3rqCar)
  rw [q3rq_pair_mul (z3.neg z3.one) (z3.neg z3.one),
    z3.neg_mul z3.one (z3.neg z3.one), z3.mul_neg z3.one z3.one, z3.neg_neg,
    z3.one_mul z3.one]

/-- **(−1)³ = −1 in U₂**（27=(6,−1) の単数部が 3=(2,−1) の単数部の 3 乗であること）。 -/
theorem q3tl_negU_cube :
    q3rqU.mul (q3rqU.mul q3tlNegOneU q3tlNegOneU) q3tlNegOneU = q3tlNegOneU := by
  rw [q3tl_negU_sq]
  exact q3rqU.one_mul q3tlNegOneU

/-- **q3tl-0b: 実 ζ₃ ∈ U₂**（R1 の実 ζ₃=(−1+√−3)/2・位数 3 の円分元）。 -/
def q3tlZeta3U : q3rqU.carrier := ⟨q3rqZeta, q3rq_zeta_unit⟩

/-- **ζ₃³ = 1 in U₂**（R1 q3rq_zeta_cube）。 -/
theorem q3tl_zetaU_cube :
    q3rqU.mul (q3rqU.mul q3tlZeta3U q3tlZeta3U) q3tlZeta3U = q3rqU.one :=
  Subtype.ext q3rq_zeta_cube

/-! ## q3tl-1: 可換性・正規性（q3t の L₂^× 版） -/

/-- **q3tl-1a: L₂^× = ℤ × U₂ は可換**（ℤ 加法可換 × U₂ 可換 q3rqU_comm）。 -/
theorem q3tlComm (x y : q3rqLx.carrier) : q3rqLx.mul x y = q3rqLx.mul y x := by
  show (intGrp.mul x.1 y.1, q3rqU.mul x.2 y.2)
     = (intGrp.mul y.1 x.1, q3rqU.mul y.2 x.2)
  have h1 : intGrp.mul x.1 y.1 = intGrp.mul y.1 x.1 := Int.add_comm x.1 y.1
  rw [h1, q3rqU_comm x.2 y.2]

/-- **q3tl-1b: 可換群 L₂^× では任意の部分群が正規**（q3t_normal の L₂^× 版）。 -/
theorem q3tlNormal (H : Subgroup q3rqLx) : IsNormalSubgroup q3rqLx H := by
  intro g n hn
  have hconj : q3rqLx.mul (q3rqLx.mul g n) (q3rqLx.inv g) = n := by
    rw [q3tlComm g n, q3rqLx.mul_assoc, q3rqLx.mul_inv, q3rqLx.mul_one]
  rw [hconj]
  exact hn

/-! ## q3tl-2: level-3 の群元 3=(2,−1)・27=(6,−1) と 27=3³ -/

/-- **q3tl-2a: 元 3 = (2, −1) ∈ L₂^×**（3=−λ²・v_λ(3)=2・単数部 −1）。 -/
def q3tl3 : q3rqLx.carrier := ((2 : Int), q3tlNegOneU)

/-- **q3tl-2b（★）: Tate パラメータ 27 = (6, −1) ∈ L₂^×**（q=27=q3tQ 3=3³・v_λ(27)=6）。
    q^{1/3}=3∈ℚ₃ の立方トリックで level-3 が L₂ 単独で閉じる。 -/
def q3tlQ : q3rqLx.carrier := ((6 : Int), q3tlNegOneU)

/-- level-3 の円分群元 ζ₃ = (0, ζ₃) ∈ L₂^×（付値 0・単数部 ζ₃）。 -/
def q3tlZeta3Elt : q3rqLx.carrier := ((0 : Int), q3tlZeta3U)

/-- **q3tl-2c（★）: 27 = 3³**（(2,−1)³ = (6, (−1)³) = (6,−1)）— 立方トリックの核。
    第 1 成分 2+2+2=6・第 2 成分 (−1)³=−1。 -/
theorem q3tl_cube_elt :
    q3rqLx.mul (q3rqLx.mul q3tl3 q3tl3) q3tl3 = q3tlQ := by
  show (intGrp.mul (intGrp.mul (2 : Int) 2) 2,
        q3rqU.mul (q3rqU.mul q3tlNegOneU q3tlNegOneU) q3tlNegOneU)
      = ((6 : Int), q3tlNegOneU)
  have hfst : intGrp.mul (intGrp.mul (2 : Int) 2) 2 = (6 : Int) := by
    show (2 : Int) + 2 + 2 = 6; omega
  rw [hfst, q3tl_negU_cube]

/-- **q3tl-2d: ζ₃³ = 1**（(0,ζ₃)³ = (0, ζ₃³) = (0,1) = 1）— 群レベルの円分位数 3。 -/
theorem q3tl_zeta3_cube_elt :
    q3rqLx.mul (q3rqLx.mul q3tlZeta3Elt q3tlZeta3Elt) q3tlZeta3Elt = q3rqLx.one := by
  show (intGrp.mul (intGrp.mul (0 : Int) 0) 0,
        q3rqU.mul (q3rqU.mul q3tlZeta3U q3tlZeta3U) q3tlZeta3U)
      = ((0 : Int), q3rqU.one)
  have hfst : intGrp.mul (intGrp.mul (0 : Int) 0) 0 = (0 : Int) := by
    show (0 : Int) + 0 + 0 = 0; omega
  rw [hfst, q3tl_zetaU_cube]

/-! ## q3tl-3: 実 Tate 曲線 E₂₇ = L₂^×/27^ℤ -/

/-- **q3tl-3a: 27^ℤ 部分群**（tateQPowersSubgroup を実 L₂^×・実 q=27 で消費）。 -/
def q3tlSubgroup : Subgroup q3rqLx := tateQPowersSubgroup q3rqLx q3tlQ

/-- **q3tl-3b（★）: level-3 実 Tate 曲線 E₂₇ = L₂^×/27^ℤ**（quotientGroupN）。
    R3 の level-3 テータ群が乗る中心対象を、実 L₂^×・実 q=27 の上で本物の商群として構成。 -/
def q3tlCurve : Grp :=
  quotientGroupN q3rqLx q3tlSubgroup (q3tlNormal q3tlSubgroup)

/-- **q3tl-3c: 射影 L₂^× → E₂₇**（全射準同型）。 -/
def q3tlProj : Hom q3rqLx q3tlCurve :=
  quotientProjN q3rqLx q3tlSubgroup (q3tlNormal q3tlSubgroup)

/-- **q3tl-3d: 射影は全射**。 -/
theorem q3tl_proj_surjective : ∀ x, ∃ a, q3tlProj.map a = x :=
  quotientProjN_surjective q3rqLx q3tlSubgroup (q3tlNormal q3tlSubgroup)

/-- **q3tl-3e: E₂₇ はアーベル群**（可換群 L₂^× の商）。 -/
theorem q3tl_curve_abelian :
    ∀ x y : q3tlCurve.carrier, q3tlCurve.mul x y = q3tlCurve.mul y x := by
  intro x y
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  show Quot.mk _ (q3rqLx.mul a b) = Quot.mk _ (q3rqLx.mul b a)
  rw [q3tlComm a b]

/-- **q3tl-3f（★）: 周期性 [x] = [27x]**（Tate 曲線の本質）— 27^ℤ で割ることで
    x と 27·x が E₂₇ 上で同一点になる。核: x⁻¹·(27·x) = 27 ∈ 27^ℤ（可換性で整理）。 -/
theorem q3tl_period (x : q3rqLx.carrier) :
    q3tlProj.map x = q3tlProj.map (q3rqLx.mul q3tlQ x) := by
  apply Quot.sound
  show q3tlSubgroup.mem (q3rqLx.mul (q3rqLx.inv x) (q3rqLx.mul q3tlQ x))
  have heq : q3rqLx.mul (q3rqLx.inv x) (q3rqLx.mul q3tlQ x) = q3tlQ := by
    rw [q3tlComm q3tlQ x, ← q3rqLx.mul_assoc, q3rqLx.inv_mul, q3rqLx.one_mul]
  rw [heq]
  exact tate_gen_mem q3rqLx q3tlQ

/-! ## q3tl-4: 3-torsion 点 [ζ₃]・[3] と位数 3 -/

/-- **q3tl-4a: 3-torsion 点 [ζ₃] ∈ E₂₇**（R1 の実 ζ₃ の像）。 -/
def q3tlZeta3 : q3tlCurve.carrier := q3tlProj.map q3tlZeta3Elt

/-- **q3tl-4b: 3-torsion 点 [3] ∈ E₂₇**（3=(2,−1) の像・3³=27=q ゆえ位数 3）。 -/
def q3tl3pt : q3tlCurve.carrier := q3tlProj.map q3tl3

/-- **q3tl-4c（★）: [ζ₃]³ = 1**（ζ₃³=1・準同型で E₂₇ へ降下）。 -/
theorem q3tl_zeta3_tor :
    q3tlCurve.mul (q3tlCurve.mul q3tlZeta3 q3tlZeta3) q3tlZeta3 = q3tlCurve.one := by
  show q3tlCurve.mul (q3tlCurve.mul (q3tlProj.map q3tlZeta3Elt) (q3tlProj.map q3tlZeta3Elt))
      (q3tlProj.map q3tlZeta3Elt) = q3tlCurve.one
  rw [← q3tlProj.map_mul, ← q3tlProj.map_mul, q3tl_zeta3_cube_elt, q3tlProj.map_one]

/-- **q3tl-4d（★）: [3]³ = 1**（3³=27=q ∈ 27^ℤ ゆえ [3³]=[27]=[1]）— 立方トリックの帰結。 -/
theorem q3tl_3pt_tor :
    q3tlCurve.mul (q3tlCurve.mul q3tl3pt q3tl3pt) q3tl3pt = q3tlCurve.one := by
  show q3tlCurve.mul (q3tlCurve.mul (q3tlProj.map q3tl3) (q3tlProj.map q3tl3))
      (q3tlProj.map q3tl3) = q3tlCurve.one
  rw [← q3tlProj.map_mul, ← q3tlProj.map_mul, q3tl_cube_elt]
  exact (quotientProjN_ker q3rqLx q3tlSubgroup (q3tlNormal q3tlSubgroup) q3tlQ).mpr
    (tate_gen_mem q3rqLx q3tlQ)

/-! ## q3tl-5: 位数ちょうど 3（付値成分 6ℤ による非自明性の分離） -/

/-- 付値成分（第 1 成分）の自然数冪則: (gⁿ).1 = (intGrp 内の g.1 の n 乗)。 -/
theorem q3tl_npow_fst (g : q3rqLx.carrier) : ∀ n : Nat,
    (tateNpow q3rqLx g n).1 = tateNpow intGrp g.1 n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show intGrp.mul (tateNpow q3rqLx g k).1 g.1
        = intGrp.mul (tateNpow intGrp g.1 k) g.1
    rw [ih]

/-- 付値成分の整数冪則: (g^t).1 = (intGrp 内の g.1 の t 乗)（負冪込み）。 -/
theorem q3tl_zpow_fst (g : q3rqLx.carrier) : ∀ t : Int,
    (tateZpow q3rqLx g t).1 = tateZpow intGrp g.1 t := by
  intro t
  cases t with
  | ofNat n => exact q3tl_npow_fst g n
  | negSucc n =>
    show (tateNpow q3rqLx (q3rqLx.inv g) (n + 1)).1
        = tateNpow intGrp (intGrp.inv g.1) (n + 1)
    have hinv : (q3rqLx.inv g).1 = intGrp.inv g.1 := rfl
    rw [← hinv]
    exact q3tl_npow_fst (q3rqLx.inv g) (n + 1)

/-- intGrp（加法群 ℤ）の自然数冪 = n·v。 -/
theorem tateNpow_intGrp (v : Int) : ∀ n : Nat, tateNpow intGrp v n = (n : Int) * v := by
  intro n
  induction n with
  | zero =>
    show intGrp.one = ((0 : Nat) : Int) * v
    have h0 : ((0 : Nat) : Int) = (0 : Int) := by omega
    rw [h0, Int.zero_mul]
  | succ k ih =>
    show intGrp.mul (tateNpow intGrp v k) v = (((k + 1 : Nat)) : Int) * v
    rw [ih]
    show (k : Int) * v + v = (((k + 1 : Nat)) : Int) * v
    have hc : (((k + 1 : Nat)) : Int) = (k : Int) + 1 := by omega
    rw [hc, Int.add_mul, Int.one_mul]

/-- intGrp（加法群 ℤ）の整数冪 = t·v（負冪込み）。 -/
theorem tateZpow_intGrp (v : Int) : ∀ t : Int, tateZpow intGrp v t = t * v := by
  intro t
  cases t with
  | ofNat n =>
    show tateNpow intGrp v n = (Int.ofNat n) * v
    rw [tateNpow_intGrp v n]
    show (n : Int) * v = (Int.ofNat n) * v
    rfl
  | negSucc n =>
    show tateNpow intGrp (intGrp.inv v) (n + 1) = (Int.negSucc n) * v
    rw [tateNpow_intGrp (intGrp.inv v) (n + 1)]
    show (((n + 1 : Nat)) : Int) * (intGrp.inv v) = (Int.negSucc n) * v
    have hinv : intGrp.inv v = -v := rfl
    have hns : (Int.negSucc n) = -(((n + 1 : Nat)) : Int) := by omega
    rw [hinv, hns, Int.mul_neg, Int.neg_mul]

/-- **q3tl-5a: 27^ℤ の付値成分は 6·t**（v_λ(27ᵗ)=6t）— 非自明性の分離部品。 -/
theorem q3tl_pow_fst (t : Int) : (tateZpow q3rqLx q3tlQ t).1 = t * 6 := by
  have h6 : q3tlQ.1 = (6 : Int) := rfl
  rw [q3tl_zpow_fst q3tlQ t, tateZpow_intGrp q3tlQ.1, h6]

/-- **q3tl-5b（★）: [3] ≠ 1**（真の位数 3 の点）— [3]∈27^ℤ ⟹ 27ᵗ=3・付値 6t=2 は
    整数解なし。v_λ(3)=2 が 6ℤ に入らないことによる分離。 -/
theorem q3tl_3pt_ne_one : q3tl3pt ≠ q3tlCurve.one := by
  intro h
  have hmem := (quotientProjN_ker q3rqLx q3tlSubgroup (q3tlNormal q3tlSubgroup) q3tl3).mp h
  obtain ⟨t, ht⟩ := hmem
  have key : (2 : Int) = t * 6 := by
    have e1 : q3tl3.1 = t * 6 := by rw [← ht]; exact q3tl_pow_fst t
    exact e1
  omega

/-- **q3tl-5c（★）: [ζ₃] ≠ 1**（真の位数 3 の点）— [ζ₃]∈27^ℤ ⟹ 付値 6t=0 ⟹ t=0 ⟹
    ζ₃=1（単数部）に矛盾（R1 q3rq_zeta_ne_one）。 -/
theorem q3tl_zeta3_ne_one : q3tlZeta3 ≠ q3tlCurve.one := by
  intro h
  have hmem :=
    (quotientProjN_ker q3rqLx q3tlSubgroup (q3tlNormal q3tlSubgroup) q3tlZeta3Elt).mp h
  obtain ⟨t, ht⟩ := hmem
  have key : (0 : Int) = t * 6 := by
    have e1 : q3tlZeta3Elt.1 = t * 6 := by rw [← ht]; exact q3tl_pow_fst t
    exact e1
  have ht0 : t = 0 := by omega
  rw [ht0] at ht
  have hsnd : (tateZpow q3rqLx q3tlQ 0).2 = q3tlZeta3Elt.2 :=
    congrArg (fun p : Int × q3rqU.carrier => p.2) ht
  have hval : (q3rqU.one).val = q3rqZeta := congrArg Subtype.val hsnd
  exact q3rq_zeta_ne_one hval.symm

/-! ## q3tl-6: capstone -/

/-- **q3tl-6a: level-3 実 Tate 曲線データ** — 実 E₂₇=L₂^×/27^ℤ（アーベル・周期性）・
    27=3³（立方トリック）・実 3-torsion 点 [ζ₃]・[3]（位数ちょうど 3）を束ねる。 -/
structure Q3TateCurveL2Data where
  /-- E₂₇ はアーベル群。 -/
  abelian : ∀ x y : q3tlCurve.carrier, q3tlCurve.mul x y = q3tlCurve.mul y x
  /-- 射影は全射。 -/
  proj_surjective : ∀ x, ∃ a, q3tlProj.map a = x
  /-- 周期性 [x]=[27x]。 -/
  period : ∀ x, q3tlProj.map x = q3tlProj.map (q3rqLx.mul q3tlQ x)
  /-- 27 = 3³（q=27 立方トリック）。 -/
  cube_eq : q3rqLx.mul (q3rqLx.mul q3tl3 q3tl3) q3tl3 = q3tlQ
  /-- [3]³ = 1（3³=27=q）。 -/
  three_pt_tor : q3tlCurve.mul (q3tlCurve.mul q3tl3pt q3tl3pt) q3tl3pt = q3tlCurve.one
  /-- [ζ₃]³ = 1。 -/
  zeta3_tor : q3tlCurve.mul (q3tlCurve.mul q3tlZeta3 q3tlZeta3) q3tlZeta3 = q3tlCurve.one
  /-- [3] ≠ 1（真の位数 3）。 -/
  three_pt_ne_one : q3tl3pt ≠ q3tlCurve.one
  /-- [ζ₃] ≠ 1（真の位数 3）。 -/
  zeta3_ne_one : q3tlZeta3 ≠ q3tlCurve.one

/-- **q3tl-6b: 見出し実例** — level-3 実 Tate 曲線 E₂₇ = L₂^×/27^ℤ（q=27=3³）。 -/
def q3tlData : Q3TateCurveL2Data where
  abelian := q3tl_curve_abelian
  proj_surjective := q3tl_proj_surjective
  period := q3tl_period
  cube_eq := q3tl_cube_elt
  three_pt_tor := q3tl_3pt_tor
  zeta3_tor := q3tl_zeta3_tor
  three_pt_ne_one := q3tl_3pt_ne_one
  zeta3_ne_one := q3tl_zeta3_ne_one

/-- **q3tl-6c: level-3 実 Tate 曲線の存在**（実 L₂^×・実 q=27=3³・実 3-torsion）。 -/
theorem q3tl_exists : Nonempty Q3TateCurveL2Data := ⟨q3tlData⟩

end IUT
