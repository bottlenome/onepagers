/-
  IUT/Q3TateCurveL9.lean — F-wild level-9 実 Tate 曲線 E_{3⁹} = M^×/q^ℤ（q=3⁹・q^{1/9}=3∈M）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**（骨格・模型・代理でなく、q3k で建てた実
     巡回 3 次 Kummer 代数 M = O_M = L₂[Y]/(Y³−ζ₃) の単数群 U₃ = q3kU の上に、level-9 の
     実 Tate 曲線 E_{3⁹} = M^×/q^ℤ を quotientGroupN の一般部品で**本物の商群**として建てる。
     q = 3⁹ = q9tl3^9 を選ぶ 9 乗トリック（§2.1）により q^{1/9}=3 が ℚ₃ ⊂ M 内で実になり、
     追加拡大なしに level-9 が M 単独で閉じる（27=3³ の立方トリック q3tl を level 9 に写経）。
     元 3 = (6, u₆) の単数部 u₆ は q9ps の **wild 分割恒等式 3 = π₉⁶·u₆** の実閉形式単数を消費
     ——"3 := (6, 任意単数)" の模型に落ちず [実]。E_{3⁹}[9] の実生成元 [3]（3⁹=q ゆえ位数 9）と
     [ζ₉]（実 ζ₉=Y・位数 9）の**位数ちょうど 9**を非自明性込みで証明する。toy 主語なし
     ——主語は実 M^× = ℤ(v_π) × U₃（実 q3k・実 q9psU6・実 q3kZeta9 の上）。）

  complete_pct 影響: **0 前進（level-9 kill の foundation・q3tl の忠実部分ケースの 2 乗）**。
  本モジュール単体は何も kill せず（E_{3⁹} と実 9-torsion 点の建設のみ）、テータ群・μ₉ 完全性・
  剛性・橋の kill 本体は後続 q9mt/q9mr/q9mb。「complete_pct 0 前進（骨格でなく本物基盤の
  先行建設）」と正直申告する。

  内容（§2.1/§2.3 of audit/level9-theta-kill-detail-2026-07-11.md・q3tl の level-9 写経）:
   * q9tlMx = prodGrp intGrp q3kU        — M^× = ℤ(v_π) × U₃
   * q9tl_normBase_zeta9 / q9tl_zeta9_unit — N(Y) = ζ₃（実単数）⟹ ζ₉U = ⟨Y, unit⟩ ∈ U₃
   * q9tl3 = (6, u₆) / q9tlQ = (54, u₆⁹) / q9tlZeta9Elt = (0, ζ₉U) — 群提示座標（3・q=3⁹・ζ₉）
   * q9tlComm / q9tlNormal               — M^× は可換・可換群では任意部分群が正規
   * q9tlSubgroup / q9tlCurve            — q^ℤ ⊂ M^×・**E_{3⁹} = M^×/q^ℤ**
   * q9tlProj / q9tl_proj_surjective     — 射影（全射）
   * q9tl_curve_abelian / q9tl_period    — E_{3⁹} アーベル・周期性 [x]=[qx]
   * q9tl3pt / q9tlZeta9                 — 9-torsion 点 [3]・[ζ₉]
   * q9tl_ninth_elt                      — **q = 3⁹**（q9tl3^9 = q9tlQ）— 9 乗トリックの核
   * q9tl_3pt_pow9 / q9tl_zeta9_pow9     — **[3]⁹=1・[ζ₉]⁹=1**（9-torsion）
   * q9tl_3_tor / q9tl_zeta9_tor         — **位数ちょうど 9**（0<k<9 で [3]^k≠1・[ζ₉]^k≠1）
        [3]: 付値 6k=54t⟹k=9t（omega）。[ζ₉]: 付値 0=54t⟹t=0⟹Y^k=1⟹q9yp Yᵏ≠1 消費
   * Q3TateCurveL9Data / q9tl_data / q9tl_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・q3k/q9ps/q9yp/q3tl 継承の上に追記のみ）:
  1. **foundation（kill は未達）**。E_{3⁹} と実 9-torsion 点は実在するが、テータ群・mono-theta
     剛性・(1+3ℤ₃)/(1+9ℤ₃) kill そのものは後続 q9mt/q9mr/q9mb。本ファイルは何も殺さない。
  2. **q = 3⁹ は忠実部分ケースの 2 乗**（§2.1）。q^{1/9}=3∈ℚ₃ の 9 乗トリックであって [EtTh] の
     q 固定 q^{1/l} 添加そのものではない。full-faithful 版は named future target のまま。
  3. **群提示 ℤ×U₃ の商**であって {x:M // x≠0}/q^ℤ ではない（A2 恒久限定・K-point の影を継承）。
  4. **E_{3⁹}[9] ≅ (ℤ/9)² の完全分類は主張しない**。実生成元 [3]・[ζ₉] の位数ちょうど 9 と
     付値/スロット成分による非自明性までを本物に証明する。独立性・網羅性は後続（過大主張しない）。
  5. **テータ群・実テータ関数・π₁ 同定・Galois 作用は依然ゼロ**（q3k/q9ps/q9yp/q3tl の正直限定を継承）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3TateCurveL2
import IUT.Q3KummerPiSplit
import IUT.Q3KummerYPow

namespace IUT

/-! ## q9tl-0: M^× = ℤ(v_π) × U₃ -/

/-- **q9tl-0a: M^× = ℤ(v_π) × U₃**（= prodGrp intGrp q3kU・第 1 成分は π₉=Y−1 の付値
    e(M/ℚ₃)=6・第 2 成分は実単数群 U₃=q3kU）。q3rqLx=ℤ(v_λ)×U₂ の level-9 平行。 -/
def q9tlMx : Grp := prodGrp intGrp q3kU

/-! ## q9tl-1: N(Y) = ζ₃ と ζ₉ = Y ∈ U₃ -/

/-- **q9tl-1a: N(Y) = ζ₃**（3 次ノルム a³+ζ₃b³+ζ₃²c³−3ζ₃abc を (0,1,0) で計算 ⟹ ζ₃·1=ζ₃）。 -/
theorem q9tl_normBase_zeta9 : q3kNormBase q3kZeta9 = q3rqZeta := by
  show q3rqAdd (q3rqAdd (q3rqAdd (q3rqMul (q3rqMul q3rqZero q3rqZero) q3rqZero)
        (q3rqMul q3rqZeta (q3rqMul (q3rqMul q3rqOne q3rqOne) q3rqOne)))
        (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul q3rqZero q3rqZero) q3rqZero)))
      (q3rqNeg (q3rqMul q3kThree
        (q3rqMul q3rqZeta (q3rqMul (q3rqMul q3rqZero q3rqOne) q3rqZero)))) = q3rqZeta
  rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q3k_Z_eq, q9ps_1_eq]
  rw [q3rqRing.mul_zero (q3rqRing.mul q3rqRing.zero q3rqRing.zero),
      q3rqRing.mul_one (q3rqRing.mul q3rqRing.one q3rqRing.one),
      q3rqRing.mul_one q3rqRing.one,
      q3rqRing.mul_one q3rqZeta,
      q3rqRing.mul_zero q3rqZetaSq,
      q3rqRing.mul_zero (q3rqRing.mul q3rqRing.zero q3rqRing.one),
      q3rqRing.mul_zero q3rqZeta,
      q3rqRing.mul_zero q3kThree,
      q3rqRing.neg_zero,
      q3rqRing.zero_add q3rqZeta,
      q3rqRing.add_zero q3rqZeta,
      q3rqRing.add_zero q3rqZeta]

/-- **q9tl-1b: ζ₉ = Y は U₃ の単数**（N(Y)=ζ₃・ζ₃ は q3rq-単数 q3rq_zeta_unit）。 -/
theorem q9tl_zeta9_unit : q3kUnitMem q3kZeta9 := by
  show q3rqUnitMem (q3kNormBase q3kZeta9)
  rw [q9tl_normBase_zeta9]
  exact q3rq_zeta_unit

/-- **q9tl-1c: 単数元 ζ₉U = ⟨Y, unit⟩ ∈ U₃**。 -/
def q9tlZeta9U : q3kU.carrier := ⟨q3kZeta9, q9tl_zeta9_unit⟩

/-- **q9tl-1d: 単数元 u₆ = ⟨q9psU6, unit⟩ ∈ U₃**（q9ps の実 wild 分割単数 u₆）。 -/
def q9tlU3 : q3kU.carrier := ⟨q9psU6, q9ps_u6_unit⟩

/-! ## q9tl-2: 群元 3 = (6, u₆)・q = 3⁹ = (54, u₆⁹)・ζ₉ = (0, ζ₉U) -/

/-- **q9tl-2a: 元 3 = (6, u₆) ∈ M^×**（3=π₉⁶·u₆・v_π(3)=6・単数部 u₆＝実閉形式）。 -/
def q9tl3 : q9tlMx.carrier := ((6 : Int), q9tlU3)

/-- **q9tl-2b（★）: Tate パラメータ q = 3⁹ = (54, u₆⁹) ∈ M^×**（q=3⁹・v_π(q)=54・単数部
    u₆⁹＝U₃ 内 9 乗）。q^{1/9}=3∈ℚ₃ の 9 乗トリックで level-9 が M 単独で閉じる。 -/
def q9tlQ : q9tlMx.carrier := ((54 : Int), tateNpow q3kU q9tlU3 9)

/-- level-9 の円分群元 ζ₉ = (0, ζ₉U) ∈ M^×（付値 0・単数部 ζ₉U）。 -/
def q9tlZeta9Elt : q9tlMx.carrier := ((0 : Int), q9tlZeta9U)

/-! ## q9tl-3: 可換性・正規性（q3tl の M^× 版） -/

/-- **q9tl-3a: M^× = ℤ × U₃ は可換**（ℤ 加法可換 × U₃ 可換 q3k_mul_comm）。 -/
theorem q9tlComm (x y : q9tlMx.carrier) : q9tlMx.mul x y = q9tlMx.mul y x := by
  show (intGrp.mul x.1 y.1, q3kU.mul x.2 y.2)
     = (intGrp.mul y.1 x.1, q3kU.mul y.2 x.2)
  have h1 : intGrp.mul x.1 y.1 = intGrp.mul y.1 x.1 := Int.add_comm x.1 y.1
  have h2 : q3kU.mul x.2 y.2 = q3kU.mul y.2 x.2 :=
    Subtype.ext (q3k_mul_comm x.2.val y.2.val)
  rw [h1, h2]

/-- **q9tl-3b: 可換群 M^× では任意の部分群が正規**（q3tlNormal の M^× 版）。 -/
theorem q9tlNormal (H : Subgroup q9tlMx) : IsNormalSubgroup q9tlMx H := by
  intro g n hn
  have hconj : q9tlMx.mul (q9tlMx.mul g n) (q9tlMx.inv g) = n := by
    rw [q9tlComm g n, q9tlMx.mul_assoc, q9tlMx.mul_inv, q9tlMx.mul_one]
  rw [hconj]
  exact hn

/-! ## q9tl-4: 実 Tate 曲線 E_{3⁹} = M^×/q^ℤ -/

/-- **q9tl-4a: q^ℤ 部分群**（tateQPowersSubgroup を実 M^×・実 q=3⁹ で消費）。 -/
def q9tlSubgroup : Subgroup q9tlMx := tateQPowersSubgroup q9tlMx q9tlQ

/-- **q9tl-4b（★）: level-9 実 Tate 曲線 E_{3⁹} = M^×/q^ℤ**（quotientGroupN）。
    後続 level-9 テータ群が乗る中心対象を、実 M^×・実 q=3⁹ の上で本物の商群として構成。 -/
def q9tlCurve : Grp :=
  quotientGroupN q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup)

/-- **q9tl-4c: 射影 M^× → E_{3⁹}**（全射準同型）。 -/
def q9tlProj : Hom q9tlMx q9tlCurve :=
  quotientProjN q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup)

/-- **q9tl-4d: 射影は全射**。 -/
theorem q9tl_proj_surjective : ∀ x, ∃ a, q9tlProj.map a = x :=
  quotientProjN_surjective q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup)

/-- **q9tl-4e: E_{3⁹} はアーベル群**（可換群 M^× の商）。 -/
theorem q9tl_curve_abelian :
    ∀ x y : q9tlCurve.carrier, q9tlCurve.mul x y = q9tlCurve.mul y x := by
  intro x y
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  show Quot.mk _ (q9tlMx.mul a b) = Quot.mk _ (q9tlMx.mul b a)
  rw [q9tlComm a b]

/-- **q9tl-4f（★）: 周期性 [x] = [qx]**（Tate 曲線の本質）— q^ℤ で割ることで x と q·x が
    E_{3⁹} 上で同一点になる。核: x⁻¹·(q·x) = q ∈ q^ℤ（可換性で整理）。 -/
theorem q9tl_period (x : q9tlMx.carrier) :
    q9tlProj.map x = q9tlProj.map (q9tlMx.mul q9tlQ x) := by
  apply Quot.sound
  show q9tlSubgroup.mem (q9tlMx.mul (q9tlMx.inv x) (q9tlMx.mul q9tlQ x))
  have heq : q9tlMx.mul (q9tlMx.inv x) (q9tlMx.mul q9tlQ x) = q9tlQ := by
    rw [q9tlComm q9tlQ x, ← q9tlMx.mul_assoc, q9tlMx.inv_mul, q9tlMx.one_mul]
  rw [heq]
  exact tate_gen_mem q9tlMx q9tlQ

/-! ## q9tl-5: 9-torsion 点 [3]・[ζ₉] -/

/-- **q9tl-5a: 9-torsion 点 [3] ∈ E_{3⁹}**（3=(6,u₆) の像・3⁹=q ゆえ位数 9）。 -/
def q9tl3pt : q9tlCurve.carrier := q9tlProj.map q9tl3

/-- **q9tl-5b: 9-torsion 点 [ζ₉] ∈ E_{3⁹}**（実 ζ₉=Y の像）。 -/
def q9tlZeta9 : q9tlCurve.carrier := q9tlProj.map q9tlZeta9Elt

/-! ## q9tl-6: 付値成分（第 1 成分）と単数成分（第 2 成分）の冪則 -/

/-- 付値成分の自然数冪則: (gⁿ).1 = (intGrp 内の g.1 の n 乗)。 -/
theorem q9tl_npow_fst (g : q9tlMx.carrier) : ∀ n : Nat,
    (tateNpow q9tlMx g n).1 = tateNpow intGrp g.1 n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show intGrp.mul (tateNpow q9tlMx g k).1 g.1
        = intGrp.mul (tateNpow intGrp g.1 k) g.1
    rw [ih]

/-- 付値成分の整数冪則: (g^t).1 = (intGrp 内の g.1 の t 乗)（負冪込み）。 -/
theorem q9tl_zpow_fst (g : q9tlMx.carrier) : ∀ t : Int,
    (tateZpow q9tlMx g t).1 = tateZpow intGrp g.1 t := by
  intro t
  cases t with
  | ofNat n => exact q9tl_npow_fst g n
  | negSucc n =>
    show (tateNpow q9tlMx (q9tlMx.inv g) (n + 1)).1
        = tateNpow intGrp (intGrp.inv g.1) (n + 1)
    have hinv : (q9tlMx.inv g).1 = intGrp.inv g.1 := rfl
    rw [← hinv]
    exact q9tl_npow_fst (q9tlMx.inv g) (n + 1)

/-- 単数成分の自然数冪則: (gⁿ).2 = (U₃ 内の g.2 の n 乗)。 -/
theorem q9tl_npow_snd (g : q9tlMx.carrier) : ∀ n : Nat,
    (tateNpow q9tlMx g n).2 = tateNpow q3kU g.2 n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show q3kU.mul (tateNpow q9tlMx g k).2 g.2 = q3kU.mul (tateNpow q3kU g.2 k) g.2
    rw [ih]

/-- **q9tl-6a: q^ℤ の付値成分は 54·t**（v_π(qᵗ)=54t）— [3] 非自明性の分離部品。 -/
theorem q9tl_pow_fst (t : Int) : (tateZpow q9tlMx q9tlQ t).1 = t * 54 := by
  rw [q9tl_zpow_fst q9tlQ t, tateZpow_intGrp q9tlQ.1]
  have h54 : q9tlQ.1 = (54 : Int) := rfl
  rw [h54]

/-- **q9tl-6b: 3^k の付値成分は 6·k**（v_π(3ᵏ)=6k）。 -/
theorem q9tl_npow_fst_val (n : Nat) : (tateNpow q9tlMx q9tl3 n).1 = (n : Int) * 6 := by
  rw [q9tl_npow_fst q9tl3 n, tateNpow_intGrp q9tl3.1]
  have h6 : q9tl3.1 = (6 : Int) := rfl
  rw [h6]

/-- **q9tl-6c: ζ₉^k の付値成分は 0**（v_π(ζ₉ᵏ)=0）。 -/
theorem q9tl_npow_zeta_fst (n : Nat) : (tateNpow q9tlMx q9tlZeta9Elt n).1 = (0 : Int) := by
  rw [q9tl_npow_fst q9tlZeta9Elt n, tateNpow_intGrp q9tlZeta9Elt.1]
  have h0 : q9tlZeta9Elt.1 = (0 : Int) := rfl
  rw [h0, Int.mul_zero]

/-- **q9tl-6d: 射影は冪を保つ**（proj(gⁿ) = [g]ⁿ）。 -/
theorem q9tl_proj_npow (g : q9tlMx.carrier) : ∀ n : Nat,
    q9tlProj.map (tateNpow q9tlMx g n) = tateNpow q9tlCurve (q9tlProj.map g) n := by
  intro n
  induction n with
  | zero => exact q9tlProj.map_one
  | succ k ih =>
    show q9tlProj.map (q9tlMx.mul (tateNpow q9tlMx g k) g)
        = q9tlCurve.mul (tateNpow q9tlCurve (q9tlProj.map g) k) (q9tlProj.map g)
    rw [q9tlProj.map_mul, ih]

/-! ## q9tl-7: U₃ 内の Y-冪 ζ₉U^k = Yᵏ（q9yp 正規形への橋） -/

/-- ζ₉U¹ = Y。 -/
theorem q9tl_zpow1 : (tateNpow q3kU q9tlZeta9U 1).val = q3kZeta9 := by
  show q3kMul q3kOne q3kZeta9 = q3kZeta9
  exact q3k_one_mul q3kZeta9

/-- ζ₉U² = Y²。 -/
theorem q9tl_zpow2 : (tateNpow q3kU q9tlZeta9U 2).val = q9ypY2 := by
  show q3kMul (tateNpow q3kU q9tlZeta9U 1).val q3kZeta9 = q3kMul q3kZeta9 q3kZeta9
  rw [q9tl_zpow1]

/-- ζ₉U³ = Y³。 -/
theorem q9tl_zpow3 : (tateNpow q3kU q9tlZeta9U 3).val = q9ypY3 := by
  show q3kMul (tateNpow q3kU q9tlZeta9U 2).val q3kZeta9 = q3kMul q9ypY2 q3kZeta9
  rw [q9tl_zpow2]

/-- ζ₉U⁴ = Y⁴。 -/
theorem q9tl_zpow4 : (tateNpow q3kU q9tlZeta9U 4).val = q9ypY4 := by
  show q3kMul (tateNpow q3kU q9tlZeta9U 3).val q3kZeta9 = q3kMul q9ypY3 q3kZeta9
  rw [q9tl_zpow3]

/-- ζ₉U⁵ = Y⁵。 -/
theorem q9tl_zpow5 : (tateNpow q3kU q9tlZeta9U 5).val = q9ypY5 := by
  show q3kMul (tateNpow q3kU q9tlZeta9U 4).val q3kZeta9 = q3kMul q9ypY4 q3kZeta9
  rw [q9tl_zpow4]

/-- ζ₉U⁶ = Y⁶。 -/
theorem q9tl_zpow6 : (tateNpow q3kU q9tlZeta9U 6).val = q9ypY6 := by
  show q3kMul (tateNpow q3kU q9tlZeta9U 5).val q3kZeta9 = q3kMul q9ypY5 q3kZeta9
  rw [q9tl_zpow5]

/-- ζ₉U⁷ = Y⁷。 -/
theorem q9tl_zpow7 : (tateNpow q3kU q9tlZeta9U 7).val = q9ypY7 := by
  show q3kMul (tateNpow q3kU q9tlZeta9U 6).val q3kZeta9 = q3kMul q9ypY6 q3kZeta9
  rw [q9tl_zpow6]

/-- ζ₉U⁸ = Y⁸。 -/
theorem q9tl_zpow8 : (tateNpow q3kU q9tlZeta9U 8).val = q9ypY8 := by
  show q3kMul (tateNpow q3kU q9tlZeta9U 7).val q3kZeta9 = q3kMul q9ypY7 q3kZeta9
  rw [q9tl_zpow7]

/-- **q9tl-7a: ζ₉U⁹ = Y⁹ = 1**（Y⁸·Y = (0,0,ζ₃²)·Y = embed(ζ₃·ζ₃²) = embed 1 = 1）。 -/
theorem q9tl_zpow9 : (tateNpow q3kU q9tlZeta9U 9).val = q3kOne := by
  show q3kMul (tateNpow q3kU q9tlZeta9U 8).val q3kZeta9 = q3kOne
  rw [q9tl_zpow8, q9yp_y8, q9yp_mulY_001 q3rqZetaSq, q3rq_zeta_mul_zetaSq, q3k_embed_one]

/-- **q9tl-7b: U₃ 内で ζ₉U^k ≠ 1 (0<k<9)**（位数ちょうど 9 の単数成分・q9yp Yᵏ≠1 を消費）。 -/
theorem q9tl_zeta9U_pow_ne (k : Nat) (hk0 : 0 < k) (hk9 : k < 9) :
    tateNpow q3kU q9tlZeta9U k ≠ q3kU.one := by
  match k, hk0, hk9 with
  | 0, h, _ => exact absurd h (by omega)
  | 1, _, _ => exact fun h => q9yp_y1_ne_one ((q9tl_zpow1).symm.trans (congrArg Subtype.val h))
  | 2, _, _ => exact fun h => q9yp_y2_ne_one ((q9tl_zpow2).symm.trans (congrArg Subtype.val h))
  | 3, _, _ => exact fun h => q9yp_y3_ne_one ((q9tl_zpow3).symm.trans (congrArg Subtype.val h))
  | 4, _, _ => exact fun h => q9yp_y4_ne_one ((q9tl_zpow4).symm.trans (congrArg Subtype.val h))
  | 5, _, _ => exact fun h => q9yp_y5_ne_one ((q9tl_zpow5).symm.trans (congrArg Subtype.val h))
  | 6, _, _ => exact fun h => q9yp_y6_ne_one ((q9tl_zpow6).symm.trans (congrArg Subtype.val h))
  | 7, _, _ => exact fun h => q9yp_y7_ne_one ((q9tl_zpow7).symm.trans (congrArg Subtype.val h))
  | 8, _, _ => exact fun h => q9yp_y8_ne_one ((q9tl_zpow8).symm.trans (congrArg Subtype.val h))
  | (n + 9), _, h => exact absurd h (by omega)

/-! ## q9tl-8: 位数ちょうど 9（[3] は付値 6ℤ/54ℤ・[ζ₉] は U₃ の Y-冪で分離） -/

/-- **q9tl-8a（★）: [3] の位数ちょうど 9**（0<k<9 ⟹ [3]^k≠1）— [3]^k=1 ⟹ 3^k∈q^ℤ ⟹
    付値 6k=54t ⟹ k=9t ⟹ 0<k<9 で整数解なし（omega）。 -/
theorem q9tl_3_tor (k : Nat) (hk0 : 0 < k) (hk9 : k < 9) :
    tateNpow q9tlCurve q9tl3pt k ≠ q9tlCurve.one := by
  intro h
  have h' : q9tlProj.map (tateNpow q9tlMx q9tl3 k) = q9tlCurve.one := by
    rw [q9tl_proj_npow q9tl3 k]; exact h
  have hmem := (quotientProjN_ker q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup)
    (tateNpow q9tlMx q9tl3 k)).mp h'
  obtain ⟨t, ht⟩ := hmem
  have key : t * 54 = (k : Int) * 6 := by
    have hc := congrArg Prod.fst ht
    rw [q9tl_pow_fst t, q9tl_npow_fst_val k] at hc
    exact hc
  omega

/-- **q9tl-8b（★）: [ζ₉] の位数ちょうど 9**（0<k<9 ⟹ [ζ₉]^k≠1）— [ζ₉]^k=1 ⟹ ζ₉^k∈q^ℤ ⟹
    付値 0=54t ⟹ t=0 ⟹ U₃ 内 Y^k=1 ⟹ q9yp Yᵏ≠1 (k=1..8) に矛盾。 -/
theorem q9tl_zeta9_tor (k : Nat) (hk0 : 0 < k) (hk9 : k < 9) :
    tateNpow q9tlCurve q9tlZeta9 k ≠ q9tlCurve.one := by
  intro h
  have h' : q9tlProj.map (tateNpow q9tlMx q9tlZeta9Elt k) = q9tlCurve.one := by
    rw [q9tl_proj_npow q9tlZeta9Elt k]; exact h
  have hmem := (quotientProjN_ker q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup)
    (tateNpow q9tlMx q9tlZeta9Elt k)).mp h'
  obtain ⟨t, ht⟩ := hmem
  have hfst : t * 54 = (0 : Int) := by
    have hc := congrArg Prod.fst ht
    rw [q9tl_pow_fst t, q9tl_npow_zeta_fst k] at hc
    exact hc
  have ht0 : t = 0 := by omega
  rw [ht0] at ht
  have hsnd : tateNpow q3kU q9tlZeta9U k = q3kU.one := by
    have hc := congrArg Prod.snd ht
    rw [q9tl_npow_snd q9tlZeta9Elt k] at hc
    exact hc.symm
  exact q9tl_zeta9U_pow_ne k hk0 hk9 hsnd

/-! ## q9tl-9: q = 3⁹ と 9-torsion（[3]⁹=1・[ζ₉]⁹=1） -/

/-- **q9tl-9a（★）: q = 3⁹**（q9tl3^9 = q9tlQ）— 9 乗トリックの核。第 1 成分 9×6=54・
    第 2 成分 u₆⁹（tateNpow q3kU q9tlU3 9）。 -/
theorem q9tl_ninth_elt : tateNpow q9tlMx q9tl3 9 = q9tlQ := by
  have h2 : (tateNpow q9tlMx q9tl3 9).2 = q9tlQ.2 := q9tl_npow_snd q9tl3 9
  have h1 : (tateNpow q9tlMx q9tl3 9).1 = q9tlQ.1 := by
    rw [q9tl_npow_fst_val 9]; rfl
  exact Prod.ext h1 h2

/-- **q9tl-9b（★）: [3]⁹ = 1**（3⁹=q ∈ q^ℤ ゆえ [3⁹]=[q]=[1]）— 9 乗トリックの帰結。 -/
theorem q9tl_3pt_pow9 : tateNpow q9tlCurve q9tl3pt 9 = q9tlCurve.one := by
  have h' : q9tlProj.map (tateNpow q9tlMx q9tl3 9) = tateNpow q9tlCurve q9tl3pt 9 :=
    q9tl_proj_npow q9tl3 9
  rw [← h', q9tl_ninth_elt]
  exact (quotientProjN_ker q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup) q9tlQ).mpr
    (tate_gen_mem q9tlMx q9tlQ)

/-- ζ₉^9 = 1 in M^×（付値 0・単数部 Y⁹=1）。 -/
theorem q9tl_zeta9_ninth_one : tateNpow q9tlMx q9tlZeta9Elt 9 = q9tlMx.one := by
  have h1 : (tateNpow q9tlMx q9tlZeta9Elt 9).1 = (q9tlMx.one).1 := by
    have hz : (q9tlMx.one).1 = (0 : Int) := rfl
    rw [q9tl_npow_zeta_fst 9, hz]
  have h2 : (tateNpow q9tlMx q9tlZeta9Elt 9).2 = (q9tlMx.one).2 := by
    rw [q9tl_npow_snd q9tlZeta9Elt 9]
    apply Subtype.ext
    show (tateNpow q3kU q9tlZeta9U 9).val = q3kOne
    exact q9tl_zpow9
  exact Prod.ext h1 h2

/-- **q9tl-9c（★）: [ζ₉]⁹ = 1**（実 ζ₉=Y・Y⁹=1・準同型で E_{3⁹} へ降下）。 -/
theorem q9tl_zeta9_pow9 : tateNpow q9tlCurve q9tlZeta9 9 = q9tlCurve.one := by
  have h' : q9tlProj.map (tateNpow q9tlMx q9tlZeta9Elt 9) = tateNpow q9tlCurve q9tlZeta9 9 :=
    q9tl_proj_npow q9tlZeta9Elt 9
  rw [← h', q9tl_zeta9_ninth_one]
  exact q9tlProj.map_one

/-! ## q9tl-10: capstone -/

/-- **q9tl-10a: level-9 実 Tate 曲線データ** — 実 E_{3⁹}=M^×/q^ℤ（アーベル・周期性）・
    q=3⁹（9 乗トリック）・実 9-torsion 点 [3]・[ζ₉]（位数ちょうど 9・[·]⁹=1 かつ 0<k<9 で [·]^k≠1）
    を束ねる。 -/
structure Q3TateCurveL9Data where
  /-- E_{3⁹} はアーベル群。 -/
  abelian : ∀ x y : q9tlCurve.carrier, q9tlCurve.mul x y = q9tlCurve.mul y x
  /-- 射影は全射。 -/
  proj_surjective : ∀ x, ∃ a, q9tlProj.map a = x
  /-- 周期性 [x]=[qx]。 -/
  period : ∀ x, q9tlProj.map x = q9tlProj.map (q9tlMx.mul q9tlQ x)
  /-- q = 3⁹（9 乗トリック）。 -/
  ninth_eq : tateNpow q9tlMx q9tl3 9 = q9tlQ
  /-- [3]⁹ = 1。 -/
  three_pt_pow9 : tateNpow q9tlCurve q9tl3pt 9 = q9tlCurve.one
  /-- [ζ₉]⁹ = 1。 -/
  zeta9_pow9 : tateNpow q9tlCurve q9tlZeta9 9 = q9tlCurve.one
  /-- [3] は位数ちょうど 9（0<k<9 ⟹ [3]^k≠1）。 -/
  three_pt_ord9 : ∀ k : Nat, 0 < k → k < 9 → tateNpow q9tlCurve q9tl3pt k ≠ q9tlCurve.one
  /-- [ζ₉] は位数ちょうど 9（0<k<9 ⟹ [ζ₉]^k≠1）。 -/
  zeta9_ord9 : ∀ k : Nat, 0 < k → k < 9 → tateNpow q9tlCurve q9tlZeta9 k ≠ q9tlCurve.one

/-- **q9tl-10b: 見出し実例** — level-9 実 Tate 曲線 E_{3⁹} = M^×/q^ℤ（q=3⁹）。 -/
def q9tl_data : Q3TateCurveL9Data where
  abelian := q9tl_curve_abelian
  proj_surjective := q9tl_proj_surjective
  period := q9tl_period
  ninth_eq := q9tl_ninth_elt
  three_pt_pow9 := q9tl_3pt_pow9
  zeta9_pow9 := q9tl_zeta9_pow9
  three_pt_ord9 := q9tl_3_tor
  zeta9_ord9 := q9tl_zeta9_tor

/-- **q9tl-10c: level-9 実 Tate 曲線の存在**（実 M^×・実 q=3⁹・実 9-torsion）。 -/
theorem q9tl_exists : Nonempty Q3TateCurveL9Data := ⟨q9tl_data⟩

end IUT
