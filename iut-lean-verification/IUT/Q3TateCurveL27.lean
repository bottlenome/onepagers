/-
  IUT/Q3TateCurveL27.lean — q27tl: level-27 実 Tate 曲線 E_{3²⁷} = M₂₇^×/q^ℤ
  （q=3²⁷・q^{1/27}=3∈M₂₇・q9tl（Q3TateCurveL9）の level-27 忠実クローン）

  ── 主要成果の分類: **[実／(c) 承認済み足場]**（named 実ターゲット = 柱A **A6**
     mono-anabelian 復元の **level-27 第 2 層 KILL キャンペーン**
     （audit/level27-kill-scope-2026-07-11.md §4: q27k→q27ps→…→q27tl→q27mt/q27mr→q27mb）。
     本ファイルはその Tate 曲線段——q9tl（level-9 の E_{3⁹}=M₉^×/q^ℤ）の忠実な 1 段上
     クローンとして、q27k で建てた実 O_{M₂₇} = O_{M₉}[Z]/(Z³−ζ₉) の単数群 U₂₇ = q27kU
     の上に、level-27 の実 Tate 曲線 E_{3²⁷} = M₂₇^×/q^ℤ を quotientGroupN の一般部品で
     **本物の商群**として建てる。q = 3²⁷ を選ぶ 27 乗トリック（scope §1.2: v(q)=486・e=18）
     により q^{1/27}=3 が ℚ₃ ⊂ M₂₇ 内で実になり、追加拡大なしに level-27 が M₂₇ 単独で
     閉じる。元 3 = (18, u₁₈) の単数部 u₁₈ は q27ps の **wild 分割恒等式 3 = π₂₇¹⁸·u₁₈**
     の実閉形式単数 q27psU18 を消費——"3 := (18, 任意単数)" の模型に落ちず [実]。
     E_{3²⁷}[27] の実生成元 [3]（3²⁷=q ゆえ位数 27）と [ζ₂₇]（実 ζ₂₇=Z・位数 27）の
     **位数ちょうど 27** を非自明性込みで証明する。toy 主語なし——主語は実
     M₂₇^× = ℤ(v_π) × U₂₇（実 q27k・実 q27psU18・実 q27kZeta27 の上）。

  complete_pct 影響: **0 前進（level-27 kill の foundation・q9tl の忠実クローン）**。
  本モジュール単体は何も kill せず（E_{3²⁷} と実 27-torsion 点の建設のみ）、テータ群・
  μ₂₇ 完全性・剛性・橋の kill 本体は後続 q27mt/q27mr/q27mb。s_A6 = 0.61（帽子 ≤0.65）は
  本ファイルでは**一切動かさない**。「complete_pct 0 前進（骨格でなく承認済みキャンペーン
  内の本物基盤クローン）」と正直申告する。

  内容（q9tl の level-27 写経・scope §1.2 の付値表 q=3²⁷/v(q)=486/e=18 に整合）:
   * q27tlMx = prodGrp intGrp q27kU       — M₂₇^× = ℤ(v_π) × U₂₇
   * q27tl_normBase_zeta27 / q27tl_zeta27_unit — N_{M₂₇/M₉}(Z) = ζ₉（実単数）⟹ ζ₂₇U ∈ U₂₇
   * q27tl3 = (18, u₁₈) / q27tlQ = (486, u₁₈²⁷) / q27tlZeta27Elt = (0, ζ₂₇U)
   * q27tlComm / q27tlNormal              — M₂₇^× は可換・可換群では任意部分群が正規
   * q27tlSubgroup / q27tlCurve           — q^ℤ ⊂ M₂₇^×・**E_{3²⁷} = M₂₇^×/q^ℤ**
   * q27tlProj / q27tl_proj_surjective    — 射影（全射）
   * q27tl_curve_abelian / q27tl_period   — E_{3²⁷} アーベル・周期性 [x]=[qx]
   * q27tl3pt / q27tlZeta27               — 27-torsion 点 [3]・[ζ₂₇]
   * q27tl_pow27_elt                      — **q = 3²⁷**（q27tl3^27 = q27tlQ）— 27 乗トリックの核
   * q27tl_3pt_pow27 / q27tl_zeta27_pow27 — **[3]²⁷=1・[ζ₂₇]²⁷=1**（27-torsion・μ₂₇ 関係）
   * q27tl_3_tor / q27tl_zeta27_tor       — **位数ちょうど 27**（0<k<27 で [3]^k≠1・[ζ₂₇]^k≠1）
        [3]: 付値 18k=486t⟹k=27t（omega）。[ζ₂₇]: 付値 0=486t⟹t=0⟹U₂₇ 内 Z^k=1⟹
        Z 冪正規形（本ファイル §7 で導出）に矛盾
   * q27tl_zpow1..q27tl_zpow27            — **Z 冪正規形**（Z^{3j}=embed(ζ₉ʲ)・
        Z^{3j+1}=(0,ζ₉ʲ,0)・Z^{3j+2}=(0,0,ζ₉ʲ)・Z²⁷=1）— q9yp（M₉ の Y 冪正規形）消費
   * Q3TateCurveL27Data / q27tl_data / q27tl_exists — capstone

  正直な限定（§4 規約により消さない・弱めない・q27k/q27ps/q3k/q9ps/q9yp/q9tl 継承の上に追記のみ）:
  1. **foundation（kill は未達）**。E_{3²⁷} と実 27-torsion 点は実在するが、テータ群・
     mono-theta 剛性・(1+9ℤ₃)/(1+27ℤ₃) kill そのものは後続 q27mt/q27mr/q27mb。
     本ファイルは何も殺さない。A6 status を一切動かさない。
  2. **q = 3²⁷ は忠実部分ケースの 3 乗**（scope §1.2）。q^{1/27}=3∈ℚ₃ の 27 乗トリックで
     あって [EtTh] の q 固定 q^{1/l} 添加そのものではない。full-faithful 版は named future
     target のまま（q9tl 正直限定 2 の level-27 継承）。
  3. **群提示 ℤ×U₂₇ の商**であって {x:M₂₇ // x≠0}/q^ℤ ではない（A2 恒久限定・q9tl §3 継承）。
  4. **E_{3²⁷}[27] ≅ (ℤ/27)² の完全分類は主張しない**。実生成元 [3]・[ζ₂₇] の位数ちょうど
     27 と付値/スロット成分による非自明性までを本物に証明する。独立性・網羅性は後続。
  5. **計画上の q27yp（Z 冪正規形モジュール）は未着工**のため、本ファイルが必要とする
     Z 冪正規形（Z^k の 3 スロット標準形・Z^k≠1 for 0<k<27）は §7 で **q27k の実環恒等式
     ＋ q9yp（M₉ の Y 冪正規形）から本ファイル内で導出**した（True への弱化・公理追加なし）。
     後続 q27yp が立った場合は §7 をそちらへ吸収・再輸出してよい。
  6. **テータ群・実テータ関数・π₁ 同定・Galois 作用は依然ゼロ**（q27k/q27ps の正直限定を継承）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3TateCurveL9
import IUT.Q3KummerNonicSplit

namespace IUT

/-! ## q27tl-0: M₂₇^× = ℤ(v_π) × U₂₇ -/

/-- **q27tl-0a: M₂₇^× = ℤ(v_π) × U₂₇**（= prodGrp intGrp q27kU・第 1 成分は π₂₇=Z−1 の
    付値 e(M₂₇/ℚ₃)=18・第 2 成分は実単数群 U₂₇=q27kU）。q9tlMx=ℤ(v_π)×U₃ の level-27 平行。 -/
def q27tlMx : Grp := prodGrp intGrp q27kU

/-! ## q27tl-1: N_{M₂₇/M₉}(Z) = ζ₉ と ζ₂₇ = Z ∈ U₂₇ -/

/-- **q27tl-1a: N(Z) = ζ₉**（相対 3 次ノルム a³+ζ₉b³+ζ₉²c³−3ζ₉abc を (0,1,0) で計算
    ⟹ ζ₉·1=ζ₉）。q9tl_normBase_zeta9（N(Y)=ζ₃）の level-27 平行。 -/
theorem q27tl_normBase_zeta27 : q27kNormBase q27kZeta27 = q3kZeta9 := by
  show q3kAdd (q3kAdd (q3kAdd (q3kMul (q3kMul q3kZero q3kZero) q3kZero)
        (q3kMul q3kZeta9 (q3kMul (q3kMul q3kOne q3kOne) q3kOne)))
        (q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kMul (q3kMul q3kZero q3kZero) q3kZero)))
      (q3kNeg (q3kMul q27kThree
        (q3kMul q3kZeta9 (q3kMul (q3kMul q3kZero q3kOne) q3kZero)))) = q3kZeta9
  rw [q27k_M_eq, q27k_A_eq, q27k_N_eq, q27k_Z_eq, q9ps_kO_eq]
  rw [q3kRing.mul_zero (q3kRing.mul q3kRing.zero q3kRing.zero),
      q3kRing.mul_one (q3kRing.mul q3kRing.one q3kRing.one),
      q3kRing.mul_one q3kRing.one,
      q3kRing.mul_one q3kZeta9,
      q3kRing.mul_zero (q3kRing.mul q3kZeta9 q3kZeta9),
      q3kRing.mul_zero (q3kRing.mul q3kRing.zero q3kRing.one),
      q3kRing.mul_zero q3kZeta9,
      q3kRing.mul_zero q27kThree,
      q3kRing.neg_zero,
      q3kRing.zero_add q3kZeta9,
      q3kRing.add_zero q3kZeta9,
      q3kRing.add_zero q3kZeta9]

/-- **q27tl-1b: ζ₂₇ = Z は U₂₇ の単数**（N(Z)=ζ₉・ζ₉ は q3k-単数 q9tl_zeta9_unit）。 -/
theorem q27tl_zeta27_unit : q27kUnitMem q27kZeta27 := by
  show q3kUnitMem (q27kNormBase q27kZeta27)
  rw [q27tl_normBase_zeta27]
  exact q9tl_zeta9_unit

/-- **q27tl-1c: 単数元 ζ₂₇U = ⟨Z, unit⟩ ∈ U₂₇**。 -/
def q27tlZeta27U : q27kU.carrier := ⟨q27kZeta27, q27tl_zeta27_unit⟩

/-- **q27tl-1d: 単数元 u₁₈ = ⟨q27psU18, unit⟩ ∈ U₂₇**（q27ps の実 wild 分割単数 u₁₈）。 -/
def q27tlU18 : q27kU.carrier := ⟨q27psU18, q27ps_u18_unit⟩

/-! ## q27tl-2: 群元 3 = (18, u₁₈)・q = 3²⁷ = (486, u₁₈²⁷)・ζ₂₇ = (0, ζ₂₇U) -/

/-- **q27tl-2a: 元 3 = (18, u₁₈) ∈ M₂₇^×**（3=π₂₇¹⁸·u₁₈・v_π(3)=18・単数部 u₁₈＝実閉形式）。 -/
def q27tl3 : q27tlMx.carrier := ((18 : Int), q27tlU18)

/-- **q27tl-2b（★）: Tate パラメータ q = 3²⁷ = (486, u₁₈²⁷) ∈ M₂₇^×**（q=3²⁷・v_π(q)=486・
    単数部 u₁₈²⁷＝U₂₇ 内 27 乗）。q^{1/27}=3∈ℚ₃ の 27 乗トリックで level-27 が M₂₇ 単独で閉じる。 -/
def q27tlQ : q27tlMx.carrier := ((486 : Int), tateNpow q27kU q27tlU18 27)

/-- level-27 の円分群元 ζ₂₇ = (0, ζ₂₇U) ∈ M₂₇^×（付値 0・単数部 ζ₂₇U）。 -/
def q27tlZeta27Elt : q27tlMx.carrier := ((0 : Int), q27tlZeta27U)

/-! ## q27tl-3: 可換性・正規性（q9tl の M₂₇^× 版） -/

/-- **q27tl-3a: M₂₇^× = ℤ × U₂₇ は可換**（ℤ 加法可換 × U₂₇ 可換 q27k_mul_comm）。 -/
theorem q27tlComm (x y : q27tlMx.carrier) : q27tlMx.mul x y = q27tlMx.mul y x := by
  show (intGrp.mul x.1 y.1, q27kU.mul x.2 y.2)
     = (intGrp.mul y.1 x.1, q27kU.mul y.2 x.2)
  have h1 : intGrp.mul x.1 y.1 = intGrp.mul y.1 x.1 := Int.add_comm x.1 y.1
  have h2 : q27kU.mul x.2 y.2 = q27kU.mul y.2 x.2 :=
    Subtype.ext (q27k_mul_comm x.2.val y.2.val)
  rw [h1, h2]

/-- **q27tl-3b: 可換群 M₂₇^× では任意の部分群が正規**（q9tlNormal の M₂₇^× 版）。 -/
theorem q27tlNormal (H : Subgroup q27tlMx) : IsNormalSubgroup q27tlMx H := by
  intro g n hn
  have hconj : q27tlMx.mul (q27tlMx.mul g n) (q27tlMx.inv g) = n := by
    rw [q27tlComm g n, q27tlMx.mul_assoc, q27tlMx.mul_inv, q27tlMx.mul_one]
  rw [hconj]
  exact hn

/-! ## q27tl-4: 実 Tate 曲線 E_{3²⁷} = M₂₇^×/q^ℤ -/

/-- **q27tl-4a: q^ℤ 部分群**（tateQPowersSubgroup を実 M₂₇^×・実 q=3²⁷ で消費）。 -/
def q27tlSubgroup : Subgroup q27tlMx := tateQPowersSubgroup q27tlMx q27tlQ

/-- **q27tl-4b（★）: level-27 実 Tate 曲線 E_{3²⁷} = M₂₇^×/q^ℤ**（quotientGroupN）。
    後続 level-27 テータ群が乗る中心対象を、実 M₂₇^×・実 q=3²⁷ の上で本物の商群として構成。 -/
def q27tlCurve : Grp :=
  quotientGroupN q27tlMx q27tlSubgroup (q27tlNormal q27tlSubgroup)

/-- **q27tl-4c: 射影 M₂₇^× → E_{3²⁷}**（全射準同型）。 -/
def q27tlProj : Hom q27tlMx q27tlCurve :=
  quotientProjN q27tlMx q27tlSubgroup (q27tlNormal q27tlSubgroup)

/-- **q27tl-4d: 射影は全射**。 -/
theorem q27tl_proj_surjective : ∀ x, ∃ a, q27tlProj.map a = x :=
  quotientProjN_surjective q27tlMx q27tlSubgroup (q27tlNormal q27tlSubgroup)

/-- **q27tl-4e: E_{3²⁷} はアーベル群**（可換群 M₂₇^× の商）。 -/
theorem q27tl_curve_abelian :
    ∀ x y : q27tlCurve.carrier, q27tlCurve.mul x y = q27tlCurve.mul y x := by
  intro x y
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  show Quot.mk _ (q27tlMx.mul a b) = Quot.mk _ (q27tlMx.mul b a)
  rw [q27tlComm a b]

/-- **q27tl-4f（★）: 周期性 [x] = [qx]**（Tate 曲線の本質）— q^ℤ で割ることで x と q·x が
    E_{3²⁷} 上で同一点になる。核: x⁻¹·(q·x) = q ∈ q^ℤ（可換性で整理）。 -/
theorem q27tl_period (x : q27tlMx.carrier) :
    q27tlProj.map x = q27tlProj.map (q27tlMx.mul q27tlQ x) := by
  apply Quot.sound
  show q27tlSubgroup.mem (q27tlMx.mul (q27tlMx.inv x) (q27tlMx.mul q27tlQ x))
  have heq : q27tlMx.mul (q27tlMx.inv x) (q27tlMx.mul q27tlQ x) = q27tlQ := by
    rw [q27tlComm q27tlQ x, ← q27tlMx.mul_assoc, q27tlMx.inv_mul, q27tlMx.one_mul]
  rw [heq]
  exact tate_gen_mem q27tlMx q27tlQ

/-! ## q27tl-5: 27-torsion 点 [3]・[ζ₂₇] -/

/-- **q27tl-5a: 27-torsion 点 [3] ∈ E_{3²⁷}**（3=(18,u₁₈) の像・3²⁷=q ゆえ位数 27）。 -/
def q27tl3pt : q27tlCurve.carrier := q27tlProj.map q27tl3

/-- **q27tl-5b: 27-torsion 点 [ζ₂₇] ∈ E_{3²⁷}**（実 ζ₂₇=Z の像・μ₂₇ 関係の実現）。 -/
def q27tlZeta27 : q27tlCurve.carrier := q27tlProj.map q27tlZeta27Elt

/-! ## q27tl-6: 付値成分（第 1 成分）と単数成分（第 2 成分）の冪則 -/

/-- 付値成分の自然数冪則: (gⁿ).1 = (intGrp 内の g.1 の n 乗)。 -/
theorem q27tl_npow_fst (g : q27tlMx.carrier) : ∀ n : Nat,
    (tateNpow q27tlMx g n).1 = tateNpow intGrp g.1 n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show intGrp.mul (tateNpow q27tlMx g k).1 g.1
        = intGrp.mul (tateNpow intGrp g.1 k) g.1
    rw [ih]

/-- 付値成分の整数冪則: (g^t).1 = (intGrp 内の g.1 の t 乗)（負冪込み）。 -/
theorem q27tl_zpow_fst (g : q27tlMx.carrier) : ∀ t : Int,
    (tateZpow q27tlMx g t).1 = tateZpow intGrp g.1 t := by
  intro t
  cases t with
  | ofNat n => exact q27tl_npow_fst g n
  | negSucc n =>
    show (tateNpow q27tlMx (q27tlMx.inv g) (n + 1)).1
        = tateNpow intGrp (intGrp.inv g.1) (n + 1)
    have hinv : (q27tlMx.inv g).1 = intGrp.inv g.1 := rfl
    rw [← hinv]
    exact q27tl_npow_fst (q27tlMx.inv g) (n + 1)

/-- 単数成分の自然数冪則: (gⁿ).2 = (U₂₇ 内の g.2 の n 乗)。 -/
theorem q27tl_npow_snd (g : q27tlMx.carrier) : ∀ n : Nat,
    (tateNpow q27tlMx g n).2 = tateNpow q27kU g.2 n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show q27kU.mul (tateNpow q27tlMx g k).2 g.2 = q27kU.mul (tateNpow q27kU g.2 k) g.2
    rw [ih]

/-- **q27tl-6a: q^ℤ の付値成分は 486·t**（v_π(qᵗ)=486t）— [3] 非自明性の分離部品。 -/
theorem q27tl_pow_fst (t : Int) : (tateZpow q27tlMx q27tlQ t).1 = t * 486 := by
  rw [q27tl_zpow_fst q27tlQ t, tateZpow_intGrp q27tlQ.1]
  have h486 : q27tlQ.1 = (486 : Int) := rfl
  rw [h486]

/-- **q27tl-6b: 3^k の付値成分は 18·k**（v_π(3ᵏ)=18k）。 -/
theorem q27tl_npow_fst_val (n : Nat) : (tateNpow q27tlMx q27tl3 n).1 = (n : Int) * 18 := by
  rw [q27tl_npow_fst q27tl3 n, tateNpow_intGrp q27tl3.1]
  have h18 : q27tl3.1 = (18 : Int) := rfl
  rw [h18]

/-- **q27tl-6c: ζ₂₇^k の付値成分は 0**（v_π(ζ₂₇ᵏ)=0）。 -/
theorem q27tl_npow_zeta_fst (n : Nat) : (tateNpow q27tlMx q27tlZeta27Elt n).1 = (0 : Int) := by
  rw [q27tl_npow_fst q27tlZeta27Elt n, tateNpow_intGrp q27tlZeta27Elt.1]
  have h0 : q27tlZeta27Elt.1 = (0 : Int) := rfl
  rw [h0, Int.mul_zero]

/-- **q27tl-6d: 射影は冪を保つ**（proj(gⁿ) = [g]ⁿ）。 -/
theorem q27tl_proj_npow (g : q27tlMx.carrier) : ∀ n : Nat,
    q27tlProj.map (tateNpow q27tlMx g n) = tateNpow q27tlCurve (q27tlProj.map g) n := by
  intro n
  induction n with
  | zero => exact q27tlProj.map_one
  | succ k ih =>
    show q27tlProj.map (q27tlMx.mul (tateNpow q27tlMx g k) g)
        = q27tlCurve.mul (tateNpow q27tlCurve (q27tlProj.map g) k) (q27tlProj.map g)
    rw [q27tlProj.map_mul, ih]

/-! ## q27tl-7: U₂₇ 内の Z-冪正規形 ζ₂₇U^k（q27yp 未着工のため本ファイルで導出・正直限定 5）

  正規形: Z^{3j} = embed(ζ₉ʲ)・Z^{3j+1} = (0, ζ₉ʲ, 0)・Z^{3j+2} = (0, 0, ζ₉ʲ)（Z³=ζ₉ の
  ねじれ・ζ₉ʲ は q9yp の M₉ 実 Y 冪正規形）。3 つの片段乗法補題（embed·Z・mid·Z・hi·Z）で
  27 段を機械的に降ろす。 -/

/-- **q27tl-7a: embed(a)·Z = (0, a, 0)**（片段乗法・定数部→Z 部）。 -/
theorem q27tl_embed_mulZ (a : q3kCar) :
    q27kMul (q27kEmbed a) q27kZeta27 = ((q3kZero, a, q3kZero) : q27kCar) := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul a q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
          (q3kRing.mul q3kRing.zero q3kRing.one))) = q3kRing.zero
    rw [q3kRing.mul_zero a, q3kRing.mul_zero q3kRing.zero, q3kRing.zero_mul q3kRing.one,
        q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9,
        q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul a q3kRing.one)
        (q3kRing.mul q3kRing.zero q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul q3kRing.zero q3kRing.zero)) = a
    rw [q3kRing.mul_one a, q3kRing.mul_zero q3kRing.zero, q3kRing.add_zero a,
        q3kRing.mul_zero q3kZeta9, q3kRing.add_zero a]
  · show q3kRing.add (q3kRing.add (q3kRing.mul a q3kRing.zero)
        (q3kRing.mul q3kRing.zero q3kRing.one)) (q3kRing.mul q3kRing.zero q3kRing.zero)
        = q3kRing.zero
    rw [q3kRing.mul_zero a, q3kRing.zero_mul q3kRing.one, q3kRing.add_zero q3kRing.zero,
        q3kRing.mul_zero q3kRing.zero, q3kRing.add_zero q3kRing.zero]

/-- **q27tl-7b: (0, a, 0)·Z = (0, 0, a)**（片段乗法・Z 部→Z² 部）。 -/
theorem q27tl_mid_mulZ (a : q3kCar) :
    q27kMul ((q3kZero, a, q3kZero) : q27kCar) q27kZeta27
      = ((q3kZero, q3kZero, a) : q27kCar) := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul a q3kRing.zero)
          (q3kRing.mul q3kRing.zero q3kRing.one))) = q3kRing.zero
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.mul_zero a, q3kRing.zero_mul q3kRing.one,
        q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9,
        q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.one)
        (q3kRing.mul a q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul q3kRing.zero q3kRing.zero)) = q3kRing.zero
    rw [q3kRing.zero_mul q3kRing.one, q3kRing.mul_zero a, q3kRing.add_zero q3kRing.zero,
        q3kRing.mul_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9,
        q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul a q3kRing.one)) (q3kRing.mul q3kRing.zero q3kRing.zero) = a
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.mul_one a, q3kRing.zero_add a,
        q3kRing.add_zero a]

/-- **q27tl-7c: (0, 0, a)·Z = embed(ζ₉·a)**（片段乗法・Z³=ζ₉ のねじれで定数部へ）。 -/
theorem q27tl_hi_mulZ (a : q3kCar) :
    q27kMul ((q3kZero, q3kZero, a) : q27kCar) q27kZeta27
      = q27kEmbed (q3kMul q3kZeta9 a) := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
          (q3kRing.mul a q3kRing.one))) = q3kRing.mul q3kZeta9 a
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.mul_one a, q3kRing.zero_add a,
        q3kRing.zero_add (q3kRing.mul q3kZeta9 a)]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.one)
        (q3kRing.mul q3kRing.zero q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul a q3kRing.zero)) = q3kRing.zero
    rw [q3kRing.zero_mul q3kRing.one, q3kRing.mul_zero q3kRing.zero,
        q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero a, q3kRing.mul_zero q3kZeta9,
        q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kRing.zero q3kRing.one)) (q3kRing.mul a q3kRing.zero) = q3kRing.zero
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.zero_mul q3kRing.one,
        q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero a, q3kRing.add_zero q3kRing.zero]

/-- **q27tl-7d: ζ₉·Y⁸ = 1**（M₉ 内・Y⁹=1 の片段形・q9yp 正規形消費）。 -/
theorem q27tl_y9_one : q3kMul q3kZeta9 q9ypY8 = q3kOne := by
  rw [q3k_mul_comm q3kZeta9 q9ypY8, q9yp_y8, q9yp_mulY_001 q3rqZetaSq,
      q3rq_zeta_mul_zetaSq]
  exact q3k_embed_one

/-- ζ₂₇U¹ = Z。 -/
theorem q27tl_zpow1 : (tateNpow q27kU q27tlZeta27U 1).val = q27kZeta27 := by
  show q27kMul q27kOne q27kZeta27 = q27kZeta27
  exact q27k_one_mul q27kZeta27

/-- ζ₂₇U² = Z² = (0,0,1)。 -/
theorem q27tl_zpow2 :
    (tateNpow q27kU q27tlZeta27U 2).val = ((q3kZero, q3kZero, q3kOne) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 1).val q27kZeta27 = _
  rw [q27tl_zpow1]
  exact q27tl_mid_mulZ q3kOne

/-- ζ₂₇U³ = embed(ζ₉)。 -/
theorem q27tl_zpow3 : (tateNpow q27kU q27tlZeta27U 3).val = q27kEmbed q3kZeta9 := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 2).val q27kZeta27 = q27kEmbed q3kZeta9
  rw [q27tl_zpow2, q27tl_hi_mulZ q3kOne, q3k_mul_comm q3kZeta9 q3kOne,
      q3k_one_mul q3kZeta9]

/-- ζ₂₇U⁴ = (0, ζ₉, 0)。 -/
theorem q27tl_zpow4 :
    (tateNpow q27kU q27tlZeta27U 4).val = ((q3kZero, q3kZeta9, q3kZero) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 3).val q27kZeta27 = _
  rw [q27tl_zpow3]
  exact q27tl_embed_mulZ q3kZeta9

/-- ζ₂₇U⁵ = (0, 0, ζ₉)。 -/
theorem q27tl_zpow5 :
    (tateNpow q27kU q27tlZeta27U 5).val = ((q3kZero, q3kZero, q3kZeta9) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 4).val q27kZeta27 = _
  rw [q27tl_zpow4]
  exact q27tl_mid_mulZ q3kZeta9

/-- ζ₂₇U⁶ = embed(Y²)。 -/
theorem q27tl_zpow6 : (tateNpow q27kU q27tlZeta27U 6).val = q27kEmbed q9ypY2 := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 5).val q27kZeta27 = q27kEmbed q9ypY2
  rw [q27tl_zpow5]
  exact q27tl_hi_mulZ q3kZeta9

/-- ζ₂₇U⁷ = (0, Y², 0)。 -/
theorem q27tl_zpow7 :
    (tateNpow q27kU q27tlZeta27U 7).val = ((q3kZero, q9ypY2, q3kZero) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 6).val q27kZeta27 = _
  rw [q27tl_zpow6]
  exact q27tl_embed_mulZ q9ypY2

/-- ζ₂₇U⁸ = (0, 0, Y²)。 -/
theorem q27tl_zpow8 :
    (tateNpow q27kU q27tlZeta27U 8).val = ((q3kZero, q3kZero, q9ypY2) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 7).val q27kZeta27 = _
  rw [q27tl_zpow7]
  exact q27tl_mid_mulZ q9ypY2

/-- ζ₂₇U⁹ = embed(Y³)。 -/
theorem q27tl_zpow9 : (tateNpow q27kU q27tlZeta27U 9).val = q27kEmbed q9ypY3 := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 8).val q27kZeta27 = q27kEmbed q9ypY3
  rw [q27tl_zpow8, q27tl_hi_mulZ q9ypY2, q3k_mul_comm q3kZeta9 q9ypY2]
  rfl

/-- ζ₂₇U¹⁰ = (0, Y³, 0)。 -/
theorem q27tl_zpow10 :
    (tateNpow q27kU q27tlZeta27U 10).val = ((q3kZero, q9ypY3, q3kZero) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 9).val q27kZeta27 = _
  rw [q27tl_zpow9]
  exact q27tl_embed_mulZ q9ypY3

/-- ζ₂₇U¹¹ = (0, 0, Y³)。 -/
theorem q27tl_zpow11 :
    (tateNpow q27kU q27tlZeta27U 11).val = ((q3kZero, q3kZero, q9ypY3) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 10).val q27kZeta27 = _
  rw [q27tl_zpow10]
  exact q27tl_mid_mulZ q9ypY3

/-- ζ₂₇U¹² = embed(Y⁴)。 -/
theorem q27tl_zpow12 : (tateNpow q27kU q27tlZeta27U 12).val = q27kEmbed q9ypY4 := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 11).val q27kZeta27 = q27kEmbed q9ypY4
  rw [q27tl_zpow11, q27tl_hi_mulZ q9ypY3, q3k_mul_comm q3kZeta9 q9ypY3]
  rfl

/-- ζ₂₇U¹³ = (0, Y⁴, 0)。 -/
theorem q27tl_zpow13 :
    (tateNpow q27kU q27tlZeta27U 13).val = ((q3kZero, q9ypY4, q3kZero) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 12).val q27kZeta27 = _
  rw [q27tl_zpow12]
  exact q27tl_embed_mulZ q9ypY4

/-- ζ₂₇U¹⁴ = (0, 0, Y⁴)。 -/
theorem q27tl_zpow14 :
    (tateNpow q27kU q27tlZeta27U 14).val = ((q3kZero, q3kZero, q9ypY4) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 13).val q27kZeta27 = _
  rw [q27tl_zpow13]
  exact q27tl_mid_mulZ q9ypY4

/-- ζ₂₇U¹⁵ = embed(Y⁵)。 -/
theorem q27tl_zpow15 : (tateNpow q27kU q27tlZeta27U 15).val = q27kEmbed q9ypY5 := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 14).val q27kZeta27 = q27kEmbed q9ypY5
  rw [q27tl_zpow14, q27tl_hi_mulZ q9ypY4, q3k_mul_comm q3kZeta9 q9ypY4]
  rfl

/-- ζ₂₇U¹⁶ = (0, Y⁵, 0)。 -/
theorem q27tl_zpow16 :
    (tateNpow q27kU q27tlZeta27U 16).val = ((q3kZero, q9ypY5, q3kZero) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 15).val q27kZeta27 = _
  rw [q27tl_zpow15]
  exact q27tl_embed_mulZ q9ypY5

/-- ζ₂₇U¹⁷ = (0, 0, Y⁵)。 -/
theorem q27tl_zpow17 :
    (tateNpow q27kU q27tlZeta27U 17).val = ((q3kZero, q3kZero, q9ypY5) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 16).val q27kZeta27 = _
  rw [q27tl_zpow16]
  exact q27tl_mid_mulZ q9ypY5

/-- ζ₂₇U¹⁸ = embed(Y⁶)。 -/
theorem q27tl_zpow18 : (tateNpow q27kU q27tlZeta27U 18).val = q27kEmbed q9ypY6 := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 17).val q27kZeta27 = q27kEmbed q9ypY6
  rw [q27tl_zpow17, q27tl_hi_mulZ q9ypY5, q3k_mul_comm q3kZeta9 q9ypY5]
  rfl

/-- ζ₂₇U¹⁹ = (0, Y⁶, 0)。 -/
theorem q27tl_zpow19 :
    (tateNpow q27kU q27tlZeta27U 19).val = ((q3kZero, q9ypY6, q3kZero) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 18).val q27kZeta27 = _
  rw [q27tl_zpow18]
  exact q27tl_embed_mulZ q9ypY6

/-- ζ₂₇U²⁰ = (0, 0, Y⁶)。 -/
theorem q27tl_zpow20 :
    (tateNpow q27kU q27tlZeta27U 20).val = ((q3kZero, q3kZero, q9ypY6) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 19).val q27kZeta27 = _
  rw [q27tl_zpow19]
  exact q27tl_mid_mulZ q9ypY6

/-- ζ₂₇U²¹ = embed(Y⁷)。 -/
theorem q27tl_zpow21 : (tateNpow q27kU q27tlZeta27U 21).val = q27kEmbed q9ypY7 := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 20).val q27kZeta27 = q27kEmbed q9ypY7
  rw [q27tl_zpow20, q27tl_hi_mulZ q9ypY6, q3k_mul_comm q3kZeta9 q9ypY6]
  rfl

/-- ζ₂₇U²² = (0, Y⁷, 0)。 -/
theorem q27tl_zpow22 :
    (tateNpow q27kU q27tlZeta27U 22).val = ((q3kZero, q9ypY7, q3kZero) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 21).val q27kZeta27 = _
  rw [q27tl_zpow21]
  exact q27tl_embed_mulZ q9ypY7

/-- ζ₂₇U²³ = (0, 0, Y⁷)。 -/
theorem q27tl_zpow23 :
    (tateNpow q27kU q27tlZeta27U 23).val = ((q3kZero, q3kZero, q9ypY7) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 22).val q27kZeta27 = _
  rw [q27tl_zpow22]
  exact q27tl_mid_mulZ q9ypY7

/-- ζ₂₇U²⁴ = embed(Y⁸)。 -/
theorem q27tl_zpow24 : (tateNpow q27kU q27tlZeta27U 24).val = q27kEmbed q9ypY8 := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 23).val q27kZeta27 = q27kEmbed q9ypY8
  rw [q27tl_zpow23, q27tl_hi_mulZ q9ypY7, q3k_mul_comm q3kZeta9 q9ypY7]
  rfl

/-- ζ₂₇U²⁵ = (0, Y⁸, 0)。 -/
theorem q27tl_zpow25 :
    (tateNpow q27kU q27tlZeta27U 25).val = ((q3kZero, q9ypY8, q3kZero) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 24).val q27kZeta27 = _
  rw [q27tl_zpow24]
  exact q27tl_embed_mulZ q9ypY8

/-- ζ₂₇U²⁶ = (0, 0, Y⁸)。 -/
theorem q27tl_zpow26 :
    (tateNpow q27kU q27tlZeta27U 26).val = ((q3kZero, q3kZero, q9ypY8) : q27kCar) := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 25).val q27kZeta27 = _
  rw [q27tl_zpow25]
  exact q27tl_mid_mulZ q9ypY8

/-- **q27tl-7e: ζ₂₇U²⁷ = Z²⁷ = 1**（(0,0,Y⁸)·Z = embed(ζ₉Y⁸) = embed(1) = 1）。 -/
theorem q27tl_zpow27 : (tateNpow q27kU q27tlZeta27U 27).val = q27kOne := by
  show q27kMul (tateNpow q27kU q27tlZeta27U 26).val q27kZeta27 = q27kOne
  rw [q27tl_zpow26, q27tl_hi_mulZ q9ypY8, q27tl_y9_one]
  exact q27k_embed_one

/-- (0, a, 0) ≠ 1（定数部スロット 0≠1 で分離）。 -/
theorem q27tl_mid_ne_one (a : q3kCar) :
    ((q3kZero, a, q3kZero) : q27kCar) ≠ q27kOne := by
  intro h
  have h1 : q3kZero = q3kOne := congrArg (fun z : q27kCar => z.1) h
  have h2 : q3rqZero = q3rqOne := congrArg (fun p : q3kCar => p.1) h1
  have h3 : z3.zero = z3.one := congrArg (fun p : q3rqCar => p.1) h2
  exact q3rq_z3_one_ne_zero h3.symm

/-- (0, 0, a) ≠ 1（定数部スロット 0≠1 で分離）。 -/
theorem q27tl_hi_ne_one (a : q3kCar) :
    ((q3kZero, q3kZero, a) : q27kCar) ≠ q27kOne := by
  intro h
  have h1 : q3kZero = q3kOne := congrArg (fun z : q27kCar => z.1) h
  have h2 : q3rqZero = q3rqOne := congrArg (fun p : q3kCar => p.1) h1
  have h3 : z3.zero = z3.one := congrArg (fun p : q3rqCar => p.1) h2
  exact q3rq_z3_one_ne_zero h3.symm

/-- embed(a) ≠ 1 for a ≠ 1（embed 単射で M₉ へ降下）。 -/
theorem q27tl_embed_ne_one {a : q3kCar} (ha : a ≠ q3kOne) : q27kEmbed a ≠ q27kOne := by
  intro h
  apply ha
  apply q27k_embed_inj
  rw [q27k_embed_one]
  exact h

/-- **q27tl-7f: U₂₇ 内で ζ₂₇U^k ≠ 1 (0<k<27)**（位数ちょうど 27 の単数成分・
    Z 冪正規形と q9yp Yʲ≠1 を消費）。 -/
theorem q27tl_zeta27U_pow_ne (k : Nat) (hk0 : 0 < k) (hk27 : k < 27) :
    tateNpow q27kU q27tlZeta27U k ≠ q27kU.one := by
  match k, hk0, hk27 with
  | 0, h, _ => exact absurd h (by omega)
  | 1, _, _ => exact fun h => q27tl_mid_ne_one q3kOne ((q27tl_zpow1).symm.trans (congrArg Subtype.val h))
  | 2, _, _ => exact fun h => q27tl_hi_ne_one q3kOne ((q27tl_zpow2).symm.trans (congrArg Subtype.val h))
  | 3, _, _ => exact fun h => q27tl_embed_ne_one q9yp_y1_ne_one ((q27tl_zpow3).symm.trans (congrArg Subtype.val h))
  | 4, _, _ => exact fun h => q27tl_mid_ne_one q3kZeta9 ((q27tl_zpow4).symm.trans (congrArg Subtype.val h))
  | 5, _, _ => exact fun h => q27tl_hi_ne_one q3kZeta9 ((q27tl_zpow5).symm.trans (congrArg Subtype.val h))
  | 6, _, _ => exact fun h => q27tl_embed_ne_one q9yp_y2_ne_one ((q27tl_zpow6).symm.trans (congrArg Subtype.val h))
  | 7, _, _ => exact fun h => q27tl_mid_ne_one q9ypY2 ((q27tl_zpow7).symm.trans (congrArg Subtype.val h))
  | 8, _, _ => exact fun h => q27tl_hi_ne_one q9ypY2 ((q27tl_zpow8).symm.trans (congrArg Subtype.val h))
  | 9, _, _ => exact fun h => q27tl_embed_ne_one q9yp_y3_ne_one ((q27tl_zpow9).symm.trans (congrArg Subtype.val h))
  | 10, _, _ => exact fun h => q27tl_mid_ne_one q9ypY3 ((q27tl_zpow10).symm.trans (congrArg Subtype.val h))
  | 11, _, _ => exact fun h => q27tl_hi_ne_one q9ypY3 ((q27tl_zpow11).symm.trans (congrArg Subtype.val h))
  | 12, _, _ => exact fun h => q27tl_embed_ne_one q9yp_y4_ne_one ((q27tl_zpow12).symm.trans (congrArg Subtype.val h))
  | 13, _, _ => exact fun h => q27tl_mid_ne_one q9ypY4 ((q27tl_zpow13).symm.trans (congrArg Subtype.val h))
  | 14, _, _ => exact fun h => q27tl_hi_ne_one q9ypY4 ((q27tl_zpow14).symm.trans (congrArg Subtype.val h))
  | 15, _, _ => exact fun h => q27tl_embed_ne_one q9yp_y5_ne_one ((q27tl_zpow15).symm.trans (congrArg Subtype.val h))
  | 16, _, _ => exact fun h => q27tl_mid_ne_one q9ypY5 ((q27tl_zpow16).symm.trans (congrArg Subtype.val h))
  | 17, _, _ => exact fun h => q27tl_hi_ne_one q9ypY5 ((q27tl_zpow17).symm.trans (congrArg Subtype.val h))
  | 18, _, _ => exact fun h => q27tl_embed_ne_one q9yp_y6_ne_one ((q27tl_zpow18).symm.trans (congrArg Subtype.val h))
  | 19, _, _ => exact fun h => q27tl_mid_ne_one q9ypY6 ((q27tl_zpow19).symm.trans (congrArg Subtype.val h))
  | 20, _, _ => exact fun h => q27tl_hi_ne_one q9ypY6 ((q27tl_zpow20).symm.trans (congrArg Subtype.val h))
  | 21, _, _ => exact fun h => q27tl_embed_ne_one q9yp_y7_ne_one ((q27tl_zpow21).symm.trans (congrArg Subtype.val h))
  | 22, _, _ => exact fun h => q27tl_mid_ne_one q9ypY7 ((q27tl_zpow22).symm.trans (congrArg Subtype.val h))
  | 23, _, _ => exact fun h => q27tl_hi_ne_one q9ypY7 ((q27tl_zpow23).symm.trans (congrArg Subtype.val h))
  | 24, _, _ => exact fun h => q27tl_embed_ne_one q9yp_y8_ne_one ((q27tl_zpow24).symm.trans (congrArg Subtype.val h))
  | 25, _, _ => exact fun h => q27tl_mid_ne_one q9ypY8 ((q27tl_zpow25).symm.trans (congrArg Subtype.val h))
  | 26, _, _ => exact fun h => q27tl_hi_ne_one q9ypY8 ((q27tl_zpow26).symm.trans (congrArg Subtype.val h))
  | (n + 27), _, h => exact absurd h (by omega)

/-! ## q27tl-8: 位数ちょうど 27（[3] は付値 18ℤ/486ℤ・[ζ₂₇] は U₂₇ の Z-冪で分離） -/

/-- **q27tl-8a（★）: [3] の位数ちょうど 27**（0<k<27 ⟹ [3]^k≠1）— [3]^k=1 ⟹ 3^k∈q^ℤ ⟹
    付値 18k=486t ⟹ k=27t ⟹ 0<k<27 で整数解なし（omega）。 -/
theorem q27tl_3_tor (k : Nat) (hk0 : 0 < k) (hk27 : k < 27) :
    tateNpow q27tlCurve q27tl3pt k ≠ q27tlCurve.one := by
  intro h
  have h' : q27tlProj.map (tateNpow q27tlMx q27tl3 k) = q27tlCurve.one := by
    rw [q27tl_proj_npow q27tl3 k]; exact h
  have hmem := (quotientProjN_ker q27tlMx q27tlSubgroup (q27tlNormal q27tlSubgroup)
    (tateNpow q27tlMx q27tl3 k)).mp h'
  obtain ⟨t, ht⟩ := hmem
  have key : t * 486 = (k : Int) * 18 := by
    have hc := congrArg Prod.fst ht
    rw [q27tl_pow_fst t, q27tl_npow_fst_val k] at hc
    exact hc
  omega

/-- **q27tl-8b（★）: [ζ₂₇] の位数ちょうど 27**（0<k<27 ⟹ [ζ₂₇]^k≠1）— [ζ₂₇]^k=1 ⟹
    ζ₂₇^k∈q^ℤ ⟹ 付値 0=486t ⟹ t=0 ⟹ U₂₇ 内 Z^k=1 ⟹ Z 冪正規形（§7）に矛盾。 -/
theorem q27tl_zeta27_tor (k : Nat) (hk0 : 0 < k) (hk27 : k < 27) :
    tateNpow q27tlCurve q27tlZeta27 k ≠ q27tlCurve.one := by
  intro h
  have h' : q27tlProj.map (tateNpow q27tlMx q27tlZeta27Elt k) = q27tlCurve.one := by
    rw [q27tl_proj_npow q27tlZeta27Elt k]; exact h
  have hmem := (quotientProjN_ker q27tlMx q27tlSubgroup (q27tlNormal q27tlSubgroup)
    (tateNpow q27tlMx q27tlZeta27Elt k)).mp h'
  obtain ⟨t, ht⟩ := hmem
  have hfst : t * 486 = (0 : Int) := by
    have hc := congrArg Prod.fst ht
    rw [q27tl_pow_fst t, q27tl_npow_zeta_fst k] at hc
    exact hc
  have ht0 : t = 0 := by omega
  rw [ht0] at ht
  have hsnd : tateNpow q27kU q27tlZeta27U k = q27kU.one := by
    have hc := congrArg Prod.snd ht
    rw [q27tl_npow_snd q27tlZeta27Elt k] at hc
    exact hc.symm
  exact q27tl_zeta27U_pow_ne k hk0 hk27 hsnd

/-! ## q27tl-9: q = 3²⁷ と 27-torsion（[3]²⁷=1・[ζ₂₇]²⁷=1） -/

/-- **q27tl-9a（★）: q = 3²⁷**（q27tl3^27 = q27tlQ）— 27 乗トリックの核。第 1 成分
    27×18=486・第 2 成分 u₁₈²⁷（tateNpow q27kU q27tlU18 27）。 -/
theorem q27tl_pow27_elt : tateNpow q27tlMx q27tl3 27 = q27tlQ := by
  have h2 : (tateNpow q27tlMx q27tl3 27).2 = q27tlQ.2 := q27tl_npow_snd q27tl3 27
  have h1 : (tateNpow q27tlMx q27tl3 27).1 = q27tlQ.1 := by
    rw [q27tl_npow_fst_val 27]; rfl
  exact Prod.ext h1 h2

/-- **q27tl-9b（★）: [3]²⁷ = 1**（3²⁷=q ∈ q^ℤ ゆえ [3²⁷]=[q]=[1]）— 27 乗トリックの帰結。 -/
theorem q27tl_3pt_pow27 : tateNpow q27tlCurve q27tl3pt 27 = q27tlCurve.one := by
  have h' : q27tlProj.map (tateNpow q27tlMx q27tl3 27) = tateNpow q27tlCurve q27tl3pt 27 :=
    q27tl_proj_npow q27tl3 27
  rw [← h', q27tl_pow27_elt]
  exact (quotientProjN_ker q27tlMx q27tlSubgroup (q27tlNormal q27tlSubgroup) q27tlQ).mpr
    (tate_gen_mem q27tlMx q27tlQ)

/-- ζ₂₇^27 = 1 in M₂₇^×（付値 0・単数部 Z²⁷=1）。 -/
theorem q27tl_zeta27_pow27_one : tateNpow q27tlMx q27tlZeta27Elt 27 = q27tlMx.one := by
  have h1 : (tateNpow q27tlMx q27tlZeta27Elt 27).1 = (q27tlMx.one).1 := by
    have hz : (q27tlMx.one).1 = (0 : Int) := rfl
    rw [q27tl_npow_zeta_fst 27, hz]
  have h2 : (tateNpow q27tlMx q27tlZeta27Elt 27).2 = (q27tlMx.one).2 := by
    rw [q27tl_npow_snd q27tlZeta27Elt 27]
    apply Subtype.ext
    show (tateNpow q27kU q27tlZeta27U 27).val = q27kOne
    exact q27tl_zpow27
  exact Prod.ext h1 h2

/-- **q27tl-9c（★）: [ζ₂₇]²⁷ = 1**（実 ζ₂₇=Z・Z²⁷=1・準同型で E_{3²⁷} へ降下・μ₂₇ 関係）。 -/
theorem q27tl_zeta27_pow27 : tateNpow q27tlCurve q27tlZeta27 27 = q27tlCurve.one := by
  have h' : q27tlProj.map (tateNpow q27tlMx q27tlZeta27Elt 27)
      = tateNpow q27tlCurve q27tlZeta27 27 :=
    q27tl_proj_npow q27tlZeta27Elt 27
  rw [← h', q27tl_zeta27_pow27_one]
  exact q27tlProj.map_one

/-! ## q27tl-10: capstone -/

/-- **q27tl-10a: level-27 実 Tate 曲線データ** — 実 E_{3²⁷}=M₂₇^×/q^ℤ（アーベル・周期性）・
    q=3²⁷（27 乗トリック）・実 27-torsion 点 [3]・[ζ₂₇]（位数ちょうど 27・[·]²⁷=1 かつ
    0<k<27 で [·]^k≠1）を束ねる。 -/
structure Q3TateCurveL27Data where
  /-- E_{3²⁷} はアーベル群。 -/
  abelian : ∀ x y : q27tlCurve.carrier, q27tlCurve.mul x y = q27tlCurve.mul y x
  /-- 射影は全射。 -/
  proj_surjective : ∀ x, ∃ a, q27tlProj.map a = x
  /-- 周期性 [x]=[qx]。 -/
  period : ∀ x, q27tlProj.map x = q27tlProj.map (q27tlMx.mul q27tlQ x)
  /-- q = 3²⁷（27 乗トリック）。 -/
  pow27_eq : tateNpow q27tlMx q27tl3 27 = q27tlQ
  /-- [3]²⁷ = 1。 -/
  three_pt_pow27 : tateNpow q27tlCurve q27tl3pt 27 = q27tlCurve.one
  /-- [ζ₂₇]²⁷ = 1。 -/
  zeta27_pow27 : tateNpow q27tlCurve q27tlZeta27 27 = q27tlCurve.one
  /-- [3] は位数ちょうど 27（0<k<27 ⟹ [3]^k≠1）。 -/
  three_pt_ord27 : ∀ k : Nat, 0 < k → k < 27 → tateNpow q27tlCurve q27tl3pt k ≠ q27tlCurve.one
  /-- [ζ₂₇] は位数ちょうど 27（0<k<27 ⟹ [ζ₂₇]^k≠1）。 -/
  zeta27_ord27 : ∀ k : Nat, 0 < k → k < 27 → tateNpow q27tlCurve q27tlZeta27 k ≠ q27tlCurve.one

/-- **q27tl-10b: 見出し実例** — level-27 実 Tate 曲線 E_{3²⁷} = M₂₇^×/q^ℤ（q=3²⁷）。 -/
def q27tl_data : Q3TateCurveL27Data where
  abelian := q27tl_curve_abelian
  proj_surjective := q27tl_proj_surjective
  period := q27tl_period
  pow27_eq := q27tl_pow27_elt
  three_pt_pow27 := q27tl_3pt_pow27
  zeta27_pow27 := q27tl_zeta27_pow27
  three_pt_ord27 := q27tl_3_tor
  zeta27_ord27 := q27tl_zeta27_tor

/-- **q27tl-10c: level-27 実 Tate 曲線の存在**（実 M₂₇^×・実 q=3²⁷・実 27-torsion）。 -/
theorem q27tl_exists : Nonempty Q3TateCurveL27Data := ⟨q27tl_data⟩

end IUT
