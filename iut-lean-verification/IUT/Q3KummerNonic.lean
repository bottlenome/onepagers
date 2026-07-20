/-
  IUT/Q3KummerNonic.lean — q27k（level-27 Kummer 環オープナー・実 O_{M₂₇} =
    O_{M₉}[Z]/(Z³−ζ₉)・O_{M₉}=q3kRing 係数）

  ── 主要成果の分類: **[実／(c) 承認済み足場]**（named 実ターゲット = 柱A **A6**
     mono-anabelian 復元の **level-27 第 2 層 KILL キャンペーン**。本ファイルはその
     opener 足場——q3k（Q3KummerCubic.lean・level-9 の O_M=O_{L₂}[Y]/(Y³−ζ₃)）の
     忠実な 1 段上クローンとして、実 O_{M₂₇} = O_{M₉}[Z]/(Z³−ζ₉) を O_{M₉}-基底
     {1, Z, Z²}・Z³ = ζ₉（= q3kZeta9）のねじれ畳み込み乗法として本物に建てる。
     base = 実可換環 q3kRing（Q3KummerCubic:454）・ねじれ d = 実 ζ₉ = q3kZeta9
     を抽象環元として扱う（q3k の環公理節が d を抽象扱いする設計をそのまま輸送）。
     相対 Galois τ: Z↦ζ₃Z（ζ₃ = q3kEmbed q3rqZeta ∈ M₉・位数 3）・相対 3 次ノルム
     N_{M₂₇/M₉}(x)=x·τx·τ²x = embed(a³+ζ₉b³+ζ₉²c³−3ζ₉abc)・単数群・閉形式逆元
     （q3kInv 消費）・実 ζ₂₇ = Z（位数ちょうど 27）を実に構成する。toy 主語なし。
     後続本物化計画（承認済み足場の昇格経路）: q27ci（M₉ 正則性パック）→ q27yp
     （Z 冪正規形）→ q27ps（wild 分割 3=π₂₇¹⁸u₁₈）→ q27c（B6 降下・q27cs 消費）→
     q27tl/q27mt/q27mr → q27mb（kill_mod27）→ crk27（crk の mod-27 torsor 縮小接続）。

  complete_pct 影響: **A6 level-27 opener — complete_pct 0 前進（本ファイル・環 opener）**。
     本ファイルは kill も剛性もテータも橋も含まない環の先行建設であり、実 IUT 完全証明率
     を動かさない。s_A6（現 0.61・帽子 ≤0.65）が動くのはキャンペーン末端の橋 q27mb ＋
     crk27 接続が閉じた時のみで、その時も帽子 ≤0.65 の内側に留まる（π₁ 連続 χ・幾何
     cyclotome 未のあいだ帽子は外れない——crk 正直限定 (3) 継承）。本ファイルでは
     A6 status を一切動かさない（過大主張しない）。

  内容:
   * q27kCar / q27kAdd / q27kNeg / q27kMul / q27kRing
        — 実 O_{M₂₇} = O_{M₉}[Z]/(Z³−ζ₉)（三つ組 (a,b,c) ↔ a+bZ+cZ²・可換環）
   * q27kSigma / q27k_sigma_mul / q27k_sigma3_id
        — 実相対 Galois τ: Z↦ζ₃Z（ring hom・τ³=id・位数 3）
   * q27kNormBase / q27k_norm_eq
        — 実相対 3 次ノルム N(x)=x·τx·τ²x=embed(a³+ζ₉b³+ζ₉²c³−3ζ₉abc)
   * q27kUnitMem / q27kInv / q27k_inv_mul
        — 単数判定・閉形式相対ノルム逆元（q3kInv 消費・体エンジン不使用）
   * q27kU / q27k_unit_mul / q27k_normBase_mul — 単数群・ノルムの乗法性
   * q27kZeta27 / q27k_zeta27_pow27 / q27k_zeta27_pow9_ne_one
        — **実 ζ₂₇ = Z（位数ちょうど 27）**・Z²⁷=1・Z⁹=ζ₃≠1
   * Q3KummerNonicData / q27kData / q27k_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・q3k/q9c 継承の上に追記のみ）:
  1. **本ファイルは代数段の環のみ**（O_{M₂₇} と M₂₇^×）。テータ・剛性・kill は一切
     含まない（後続 q27c/q27mt/q27mb の仕事）。A6 status を動かさない。
  2. **O_{M₂₇} と M₂₇^× のみ**（整数環＋単数群）。体としては建てない——total inverse は
     無く逆元は単数（相対ノルムが M₉^× の元）に限る閉形式（q3kInv 消費）。q3k §1 継承。
  3. **相対 Galois は位数 3 の τ のみ**（実 G_{ℚ₃} は無い）。q3k §3 継承。
  4. **wild 分割 3 = π₂₇¹⁸·u₁₈（π₂₇=Z−1）・M₉ 正則性は本ファイルでは未形式化**
     （付値・位相・単数判定補題族は後続 q27ps/q27ci モジュール）。Z-adic 構造は代数的に
     のみ扱う。q3k §4 継承（e=6→e=18 の wild 分岐は範囲外）。
  5. **tmzLimit への比較橋は含めない**（二重計上防止・q3k §5 継承）。
  6. 担体は**兄弟担体**（同型輸送は主張しない・q3k §6 継承）。
  7. **τ を超える Galois 作用ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ**（q3k §7 継承）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3KummerCubic

namespace IUT

/-! ## q27k-0: 座標変換ブリッジ（q3kMul/q3kAdd = q3kRing.mul/add） -/

/-- 乗法ブリッジ（rw で係数環 q3kRing の抽象公理へ橋渡し）。 -/
theorem q27k_M_eq : q3kMul = q3kRing.mul := rfl

/-- 加法ブリッジ。 -/
theorem q27k_A_eq : q3kAdd = q3kRing.add := rfl

/-! ## q27k-1: 台 M = O_{L₂}[Y]/(Y³−ζ₃)（三つ組 (a,b,c) ↔ a+bY+cY²） -/

/-- **q27k-1a: 台** — O_{L₂}³（第 1=定数部、第 2.1=Y 部、第 2.2=Y² 部）。 -/
def q27kCar : Type := q3kCar × q3kCar × q3kCar

/-- 三つ組の外延性。 -/
theorem q27k_ext : ∀ {x y : q27kCar}, x.1 = y.1 → x.2.1 = y.2.1 → x.2.2 = y.2.2 → x = y
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl, rfl => rfl

/-- 加法（成分ごと q3kAdd）。 -/
def q27kAdd (x y : q27kCar) : q27kCar :=
  ((q3kAdd x.1 y.1, q3kAdd x.2.1 y.2.1, q3kAdd x.2.2 y.2.2) : q27kCar)

/-- 加法の第 0 成分展開。 -/
theorem q27kAdd_0 (x y : q27kCar) : (q27kAdd x y).1 = q3kAdd x.1 y.1 := rfl

/-- 加法の第 1 成分展開。 -/
theorem q27kAdd_1 (x y : q27kCar) : (q27kAdd x y).2.1 = q3kAdd x.2.1 y.2.1 := rfl

/-- 加法の第 2 成分展開。 -/
theorem q27kAdd_2 (x y : q27kCar) : (q27kAdd x y).2.2 = q3kAdd x.2.2 y.2.2 := rfl

/-- 反元（成分ごと q3kNeg）。 -/
def q27kNeg (x : q27kCar) : q27kCar :=
  ((q3kNeg x.1, q3kNeg x.2.1, q3kNeg x.2.2) : q27kCar)

/-- 0 = (0,0,0)。 -/
def q27kZero : q27kCar := ((q3kZero, q3kZero, q3kZero) : q27kCar)

/-- 1 = (1,0,0)。 -/
def q27kOne : q27kCar := ((q3kOne, q3kZero, q3kZero) : q27kCar)

/-- **q27k-1b（★）: ねじれ畳み込み乗法** Y³ = ζ₃ = d。
    (a+bY+cY²)(a'+b'Y+c'Y²) を Y³→d・Y⁴→dY で還元:
    定数 = aa' + d(bc'+cb')・Y = ab'+ba'+d cc'・Y² = ac'+bb'+ca'。 -/
def q27kMul (x y : q27kCar) : q27kCar :=
  ((q3kAdd (q3kMul x.1 y.1)
      (q3kMul q3kZeta9 (q3kAdd (q3kMul x.2.1 y.2.2) (q3kMul x.2.2 y.2.1))),
    q3kAdd (q3kAdd (q3kMul x.1 y.2.1) (q3kMul x.2.1 y.1))
      (q3kMul q3kZeta9 (q3kMul x.2.2 y.2.2)),
    q3kAdd (q3kAdd (q3kMul x.1 y.2.2) (q3kMul x.2.1 y.2.1))
      (q3kMul x.2.2 y.1)) : q27kCar)

/-- 乗法の第 0 成分展開（rw 補助）。 -/
theorem q27kMul_0 (x y : q27kCar) : (q27kMul x y).1
    = q3kAdd (q3kMul x.1 y.1)
      (q3kMul q3kZeta9 (q3kAdd (q3kMul x.2.1 y.2.2) (q3kMul x.2.2 y.2.1))) := rfl

/-- 乗法の第 1（Y）成分展開。 -/
theorem q27kMul_1 (x y : q27kCar) : (q27kMul x y).2.1
    = q3kAdd (q3kAdd (q3kMul x.1 y.2.1) (q3kMul x.2.1 y.1))
      (q3kMul q3kZeta9 (q3kMul x.2.2 y.2.2)) := rfl

/-- 乗法の第 2（Y²）成分展開。 -/
theorem q27kMul_2 (x y : q27kCar) : (q27kMul x y).2.2
    = q3kAdd (q3kAdd (q3kMul x.1 y.2.2) (q3kMul x.2.1 y.2.1))
      (q3kMul x.2.2 y.1) := rfl

/-! ## q27k-2: 可換環公理（d = ζ₃ を抽象環元として扱う） -/

/-- 1·x = x。 -/
theorem q27k_one_mul (x : q27kCar) : q27kMul q27kOne x = x := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul q3kRing.one x.1)
        (q3kRing.mul q3kZeta9 (q3kRing.add
          (q3kRing.mul q3kRing.zero x.2.2) (q3kRing.mul q3kRing.zero x.2.1))) = x.1
    rw [q3kRing.one_mul, q3kRing.zero_mul, q3kRing.zero_mul,
      q3kRing.zero_add, q3kRing.mul_zero, q3kRing.add_zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.one x.2.1)
        (q3kRing.mul q3kRing.zero x.1))
        (q3kRing.mul q3kZeta9 (q3kRing.mul q3kRing.zero x.2.2)) = x.2.1
    rw [q3kRing.one_mul, q3kRing.zero_mul, q3kRing.add_zero,
      q3kRing.zero_mul, q3kRing.mul_zero, q3kRing.add_zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.one x.2.2)
        (q3kRing.mul q3kRing.zero x.2.1)) (q3kRing.mul q3kRing.zero x.1) = x.2.2
    rw [q3kRing.one_mul, q3kRing.zero_mul, q3kRing.add_zero,
      q3kRing.zero_mul, q3kRing.add_zero]

/-- **q27k-2b: 乗法可換**。 -/
theorem q27k_mul_comm (x y : q27kCar) : q27kMul x y = q27kMul y x := by
  apply q27k_ext
  · rw [q27kMul_0, q27kMul_0, q27k_M_eq, q27k_A_eq]
    rw [q3kRing.mul_comm x.1 y.1, q3kRing.mul_comm x.2.1 y.2.2,
      q3kRing.mul_comm x.2.2 y.2.1,
      q3kRing.add_comm (q3kRing.mul y.2.2 x.2.1) (q3kRing.mul y.2.1 x.2.2)]
  · rw [q27kMul_1, q27kMul_1, q27k_M_eq, q27k_A_eq]
    rw [q3kRing.mul_comm x.1 y.2.1, q3kRing.mul_comm x.2.1 y.1,
      q3kRing.add_comm (q3kRing.mul y.2.1 x.1) (q3kRing.mul y.1 x.2.1),
      q3kRing.mul_comm x.2.2 y.2.2]
  · rw [q27kMul_2, q27kMul_2, q27k_M_eq, q27k_A_eq]
    rw [q3kRing.mul_comm x.1 y.2.2, q3kRing.mul_comm x.2.1 y.2.1,
      q3kRing.mul_comm x.2.2 y.1,
      q3kRing.add_assoc (q3kRing.mul y.2.2 x.1) (q3kRing.mul y.2.1 x.2.1)
        (q3kRing.mul y.1 x.2.2),
      q3kRing.add_comm (q3kRing.mul y.2.2 x.1)
        (q3kRing.add (q3kRing.mul y.2.1 x.2.1) (q3kRing.mul y.1 x.2.2)),
      q3kRing.add_comm (q3kRing.mul y.2.1 x.2.1) (q3kRing.mul y.1 x.2.2)]

/-- **q27k-2c: 左分配**。 -/
theorem q27k_left_distrib (x y z : q27kCar) :
    q27kMul x (q27kAdd y z) = q27kAdd (q27kMul x y) (q27kMul x z) := by
  apply q27k_ext
  · rw [q27kMul_0, q27kAdd_0, q27kAdd_1, q27kAdd_2, q27kAdd_0, q27kMul_0, q27kMul_0,
      q27k_M_eq, q27k_A_eq]
    rw [q3kRing.left_distrib x.1 y.1 z.1,
      q3kRing.left_distrib x.2.1 y.2.2 z.2.2,
      q3kRing.left_distrib x.2.2 y.2.1 z.2.1,
      q3kRing.add_add_add_comm (q3kRing.mul x.2.1 y.2.2)
        (q3kRing.mul x.2.1 z.2.2) (q3kRing.mul x.2.2 y.2.1)
        (q3kRing.mul x.2.2 z.2.1),
      q3kRing.left_distrib q3kZeta9
        (q3kRing.add (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1))
        (q3kRing.add (q3kRing.mul x.2.1 z.2.2) (q3kRing.mul x.2.2 z.2.1)),
      q3kRing.add_add_add_comm (q3kRing.mul x.1 y.1) (q3kRing.mul x.1 z.1)
        (q3kRing.mul q3kZeta9
          (q3kRing.add (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1)))
        (q3kRing.mul q3kZeta9
          (q3kRing.add (q3kRing.mul x.2.1 z.2.2) (q3kRing.mul x.2.2 z.2.1)))]
  · rw [q27kMul_1, q27kAdd_0, q27kAdd_1, q27kAdd_2, q27kAdd_1, q27kMul_1, q27kMul_1,
      q27k_M_eq, q27k_A_eq]
    rw [q3kRing.left_distrib x.1 y.2.1 z.2.1,
      q3kRing.left_distrib x.2.1 y.1 z.1,
      q3kRing.add_add_add_comm (q3kRing.mul x.1 y.2.1) (q3kRing.mul x.1 z.2.1)
        (q3kRing.mul x.2.1 y.1) (q3kRing.mul x.2.1 z.1),
      q3kRing.left_distrib x.2.2 y.2.2 z.2.2,
      q3kRing.left_distrib q3kZeta9 (q3kRing.mul x.2.2 y.2.2)
        (q3kRing.mul x.2.2 z.2.2),
      q3kRing.add_add_add_comm
        (q3kRing.add (q3kRing.mul x.1 y.2.1) (q3kRing.mul x.2.1 y.1))
        (q3kRing.add (q3kRing.mul x.1 z.2.1) (q3kRing.mul x.2.1 z.1))
        (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 y.2.2))
        (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 z.2.2))]
  · rw [q27kMul_2, q27kAdd_0, q27kAdd_1, q27kAdd_2, q27kAdd_2, q27kMul_2, q27kMul_2,
      q27k_M_eq, q27k_A_eq]
    rw [q3kRing.left_distrib x.1 y.2.2 z.2.2,
      q3kRing.left_distrib x.2.1 y.2.1 z.2.1,
      q3kRing.add_add_add_comm (q3kRing.mul x.1 y.2.2) (q3kRing.mul x.1 z.2.2)
        (q3kRing.mul x.2.1 y.2.1) (q3kRing.mul x.2.1 z.2.1),
      q3kRing.left_distrib x.2.2 y.1 z.1,
      q3kRing.add_add_add_comm
        (q3kRing.add (q3kRing.mul x.1 y.2.2) (q3kRing.mul x.2.1 y.2.1))
        (q3kRing.add (q3kRing.mul x.1 z.2.2) (q3kRing.mul x.2.1 z.2.1))
        (q3kRing.mul x.2.2 y.1) (q3kRing.mul x.2.2 z.1)]


/-! ## q27k-2d: 乗法結合律の順列補題（可換環 q3kRing 内の 9 項和の再配置） -/

theorem q27k_add_swap (u v w : q3kCar) :
    q3kRing.add u (q3kRing.add v w) = q3kRing.add v (q3kRing.add u w) := by
  rw [← q3kRing.add_assoc u v w, q3kRing.add_comm u v, q3kRing.add_assoc v u w]

theorem q27k_perm_chain (p1 p2 p3 p4 p5 p6 p7 p8 p9 : q3kCar) :
    q3kRing.add p1 (q3kRing.add p2 (q3kRing.add p3 (q3kRing.add p4
      (q3kRing.add p5 (q3kRing.add p6 (q3kRing.add p7 (q3kRing.add p8 p9)))))))
    = q3kRing.add p1 (q3kRing.add p4 (q3kRing.add p7 (q3kRing.add p5
      (q3kRing.add p8 (q3kRing.add p2 (q3kRing.add p9 (q3kRing.add p3 p6))))))) := by
  rw [q27k_add_swap p3 p4 (q3kRing.add p5 (q3kRing.add p6 (q3kRing.add p7 (q3kRing.add p8 p9)))),
      q27k_add_swap p2 p4 (q3kRing.add p3 (q3kRing.add p5 (q3kRing.add p6 (q3kRing.add p7 (q3kRing.add p8 p9))))),
      q27k_add_swap p6 p7 (q3kRing.add p8 p9),
      q27k_add_swap p5 p7 (q3kRing.add p6 (q3kRing.add p8 p9)),
      q27k_add_swap p3 p7 (q3kRing.add p5 (q3kRing.add p6 (q3kRing.add p8 p9))),
      q27k_add_swap p2 p7 (q3kRing.add p3 (q3kRing.add p5 (q3kRing.add p6 (q3kRing.add p8 p9)))),
      q27k_add_swap p3 p5 (q3kRing.add p6 (q3kRing.add p8 p9)),
      q27k_add_swap p2 p5 (q3kRing.add p3 (q3kRing.add p6 (q3kRing.add p8 p9))),
      q27k_add_swap p6 p8 p9,
      q27k_add_swap p3 p8 (q3kRing.add p6 p9),
      q27k_add_swap p2 p8 (q3kRing.add p3 (q3kRing.add p6 p9)),
      q3kRing.add_comm p6 p9,
      q27k_add_swap p3 p9 p6]

-- comp0 shapes
theorem q27k_perm0 (p1 p2 p3 p4 p5 p6 p7 p8 p9 : q3kCar) :
    q3kRing.add (q3kRing.add p1 (q3kRing.add p2 p3))
      (q3kRing.add (q3kRing.add (q3kRing.add p4 p5) p6) (q3kRing.add (q3kRing.add p7 p8) p9))
    = q3kRing.add (q3kRing.add p1 (q3kRing.add p4 p7))
      (q3kRing.add (q3kRing.add (q3kRing.add p5 p8) p2) (q3kRing.add (q3kRing.add p9 p3) p6)) := by
  rw [q3kRing.add_assoc p1 (q3kRing.add p2 p3) (q3kRing.add (q3kRing.add (q3kRing.add p4 p5) p6) (q3kRing.add (q3kRing.add p7 p8) p9)),
      q3kRing.add_assoc p2 p3 (q3kRing.add (q3kRing.add (q3kRing.add p4 p5) p6) (q3kRing.add (q3kRing.add p7 p8) p9)),
      q3kRing.add_assoc (q3kRing.add p4 p5) p6 (q3kRing.add (q3kRing.add p7 p8) p9),
      q3kRing.add_assoc p4 p5 (q3kRing.add p6 (q3kRing.add (q3kRing.add p7 p8) p9)),
      q3kRing.add_assoc p7 p8 p9,
      q3kRing.add_assoc p1 (q3kRing.add p4 p7) (q3kRing.add (q3kRing.add (q3kRing.add p5 p8) p2) (q3kRing.add (q3kRing.add p9 p3) p6)),
      q3kRing.add_assoc p4 p7 (q3kRing.add (q3kRing.add (q3kRing.add p5 p8) p2) (q3kRing.add (q3kRing.add p9 p3) p6)),
      q3kRing.add_assoc (q3kRing.add p5 p8) p2 (q3kRing.add (q3kRing.add p9 p3) p6),
      q3kRing.add_assoc p5 p8 (q3kRing.add p2 (q3kRing.add (q3kRing.add p9 p3) p6)),
      q3kRing.add_assoc p9 p3 p6]
  exact q27k_perm_chain p1 p2 p3 p4 p5 p6 p7 p8 p9

-- comp1 shapes
theorem q27k_perm1 (p1 p2 p3 p4 p5 p6 p7 p8 p9 : q3kCar) :
    q3kRing.add (q3kRing.add (q3kRing.add p1 (q3kRing.add p2 p3)) (q3kRing.add (q3kRing.add p4 p5) p6))
      (q3kRing.add (q3kRing.add p7 p8) p9)
    = q3kRing.add (q3kRing.add (q3kRing.add (q3kRing.add p1 p4) p7) (q3kRing.add p5 (q3kRing.add p8 p2)))
      (q3kRing.add (q3kRing.add p9 p3) p6) := by
  rw [q3kRing.add_assoc (q3kRing.add p1 (q3kRing.add p2 p3)) (q3kRing.add (q3kRing.add p4 p5) p6) (q3kRing.add (q3kRing.add p7 p8) p9),
      q3kRing.add_assoc p1 (q3kRing.add p2 p3) (q3kRing.add (q3kRing.add (q3kRing.add p4 p5) p6) (q3kRing.add (q3kRing.add p7 p8) p9)),
      q3kRing.add_assoc p2 p3 (q3kRing.add (q3kRing.add (q3kRing.add p4 p5) p6) (q3kRing.add (q3kRing.add p7 p8) p9)),
      q3kRing.add_assoc (q3kRing.add p4 p5) p6 (q3kRing.add (q3kRing.add p7 p8) p9),
      q3kRing.add_assoc p4 p5 (q3kRing.add p6 (q3kRing.add (q3kRing.add p7 p8) p9)),
      q3kRing.add_assoc p7 p8 p9,
      q3kRing.add_assoc (q3kRing.add (q3kRing.add p1 p4) p7) (q3kRing.add p5 (q3kRing.add p8 p2)) (q3kRing.add (q3kRing.add p9 p3) p6),
      q3kRing.add_assoc (q3kRing.add p1 p4) p7 (q3kRing.add (q3kRing.add p5 (q3kRing.add p8 p2)) (q3kRing.add (q3kRing.add p9 p3) p6)),
      q3kRing.add_assoc p1 p4 (q3kRing.add p7 (q3kRing.add (q3kRing.add p5 (q3kRing.add p8 p2)) (q3kRing.add (q3kRing.add p9 p3) p6))),
      q3kRing.add_assoc p5 (q3kRing.add p8 p2) (q3kRing.add (q3kRing.add p9 p3) p6),
      q3kRing.add_assoc p8 p2 (q3kRing.add (q3kRing.add p9 p3) p6),
      q3kRing.add_assoc p9 p3 p6]
  exact q27k_perm_chain p1 p2 p3 p4 p5 p6 p7 p8 p9

-- comp2 shapes
theorem q27k_perm2 (p1 p2 p3 p4 p5 p6 p7 p8 p9 : q3kCar) :
    q3kRing.add (q3kRing.add (q3kRing.add p1 (q3kRing.add p2 p3)) (q3kRing.add (q3kRing.add p4 p5) p6))
      (q3kRing.add (q3kRing.add p7 p8) p9)
    = q3kRing.add (q3kRing.add (q3kRing.add (q3kRing.add p1 p4) p7) (q3kRing.add (q3kRing.add p5 p8) p2))
      (q3kRing.add p9 (q3kRing.add p3 p6)) := by
  rw [q3kRing.add_assoc (q3kRing.add p1 (q3kRing.add p2 p3)) (q3kRing.add (q3kRing.add p4 p5) p6) (q3kRing.add (q3kRing.add p7 p8) p9),
      q3kRing.add_assoc p1 (q3kRing.add p2 p3) (q3kRing.add (q3kRing.add (q3kRing.add p4 p5) p6) (q3kRing.add (q3kRing.add p7 p8) p9)),
      q3kRing.add_assoc p2 p3 (q3kRing.add (q3kRing.add (q3kRing.add p4 p5) p6) (q3kRing.add (q3kRing.add p7 p8) p9)),
      q3kRing.add_assoc (q3kRing.add p4 p5) p6 (q3kRing.add (q3kRing.add p7 p8) p9),
      q3kRing.add_assoc p4 p5 (q3kRing.add p6 (q3kRing.add (q3kRing.add p7 p8) p9)),
      q3kRing.add_assoc p7 p8 p9,
      q3kRing.add_assoc (q3kRing.add (q3kRing.add p1 p4) p7) (q3kRing.add (q3kRing.add p5 p8) p2) (q3kRing.add p9 (q3kRing.add p3 p6)),
      q3kRing.add_assoc (q3kRing.add p1 p4) p7 (q3kRing.add (q3kRing.add (q3kRing.add p5 p8) p2) (q3kRing.add p9 (q3kRing.add p3 p6))),
      q3kRing.add_assoc p1 p4 (q3kRing.add p7 (q3kRing.add (q3kRing.add (q3kRing.add p5 p8) p2) (q3kRing.add p9 (q3kRing.add p3 p6)))),
      q3kRing.add_assoc (q3kRing.add p5 p8) p2 (q3kRing.add p9 (q3kRing.add p3 p6)),
      q3kRing.add_assoc p5 p8 (q3kRing.add p2 (q3kRing.add p9 (q3kRing.add p3 p6)))]
  exact q27k_perm_chain p1 p2 p3 p4 p5 p6 p7 p8 p9

/-- **q27k-2e（★ 重い結合律）: 乗法結合律** — 3 成分を各 9 項の標準形へ展開し、
    係数環 q3kRing の分配・結合・可換で再配置（perm0/1/2）。d=ζ₃ は抽象環元扱い。 -/
theorem q27k_mul_assoc (x y z : q27kCar) :
    q27kMul (q27kMul x y) z = q27kMul x (q27kMul y z) := by
  apply q27k_ext
  · -- 成分 0（定数部）
    rw [q27kMul_0, q27kMul_0, q27kMul_1, q27kMul_2,
        q27kMul_0, q27kMul_0, q27kMul_1, q27kMul_2,
        q27k_M_eq, q27k_A_eq]
    rw [q3kRing.right_distrib (q3kRing.mul x.1 y.1)
          (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1))) z.1,
        q3kRing.mul_assoc q3kZeta9 (q3kRing.add (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1)) z.1,
        q3kRing.right_distrib (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1) z.1,
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.2.2) z.1) (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.1)]
    rw [q3kRing.right_distrib (q3kRing.add (q3kRing.mul x.1 y.2.1) (q3kRing.mul x.2.1 y.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 y.2.2)) z.2.2,
        q3kRing.right_distrib (q3kRing.mul x.1 y.2.1) (q3kRing.mul x.2.1 y.1) z.2.2,
        q3kRing.mul_assoc q3kZeta9 (q3kRing.mul x.2.2 y.2.2) z.2.2,
        q3kRing.right_distrib (q3kRing.add (q3kRing.mul x.1 y.2.2) (q3kRing.mul x.2.1 y.2.1)) (q3kRing.mul x.2.2 y.1) z.2.1,
        q3kRing.right_distrib (q3kRing.mul x.1 y.2.2) (q3kRing.mul x.2.1 y.2.1) z.2.1]
    rw [q3kRing.left_distrib q3kZeta9
          (q3kRing.add (q3kRing.add (q3kRing.mul (q3kRing.mul x.1 y.2.1) z.2.2) (q3kRing.mul (q3kRing.mul x.2.1 y.1) z.2.2)) (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.2) z.2.2)))
          (q3kRing.add (q3kRing.add (q3kRing.mul (q3kRing.mul x.1 y.2.2) z.2.1) (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.1)) (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.2.1)),
        q3kRing.left_distrib q3kZeta9 (q3kRing.add (q3kRing.mul (q3kRing.mul x.1 y.2.1) z.2.2) (q3kRing.mul (q3kRing.mul x.2.1 y.1) z.2.2)) (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.2) z.2.2)),
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 y.2.1) z.2.2) (q3kRing.mul (q3kRing.mul x.2.1 y.1) z.2.2),
        q3kRing.left_distrib q3kZeta9 (q3kRing.add (q3kRing.mul (q3kRing.mul x.1 y.2.2) z.2.1) (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.1)) (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.2.1),
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 y.2.2) z.2.1) (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.1)]
    -- ===== RHS normalization: Part A (M a v0) =====
    rw [q3kRing.left_distrib x.1 (q3kRing.mul y.1 z.1) (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1))),
        ← q3kRing.mul_assoc x.1 y.1 z.1,
        ← q3kRing.mul_assoc x.1 q3kZeta9 (q3kRing.add (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1)),
        q3kRing.mul_comm x.1 q3kZeta9,
        q3kRing.mul_assoc q3kZeta9 x.1 (q3kRing.add (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1)),
        q3kRing.left_distrib x.1 (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1),
        ← q3kRing.mul_assoc x.1 y.2.1 z.2.2,
        ← q3kRing.mul_assoc x.1 y.2.2 z.2.1,
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 y.2.1) z.2.2) (q3kRing.mul (q3kRing.mul x.1 y.2.2) z.2.1)]
    -- ===== RHS normalization: Part B (M D (M b v2 + M c v1)) =====
    rw [q3kRing.left_distrib x.2.1 (q3kRing.add (q3kRing.mul y.1 z.2.2) (q3kRing.mul y.2.1 z.2.1)) (q3kRing.mul y.2.2 z.1),
        q3kRing.left_distrib x.2.1 (q3kRing.mul y.1 z.2.2) (q3kRing.mul y.2.1 z.2.1),
        ← q3kRing.mul_assoc x.2.1 y.1 z.2.2,
        ← q3kRing.mul_assoc x.2.1 y.2.1 z.2.1,
        ← q3kRing.mul_assoc x.2.1 y.2.2 z.1,
        q3kRing.left_distrib x.2.2 (q3kRing.add (q3kRing.mul y.1 z.2.1) (q3kRing.mul y.2.1 z.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul y.2.2 z.2.2)),
        q3kRing.left_distrib x.2.2 (q3kRing.mul y.1 z.2.1) (q3kRing.mul y.2.1 z.1),
        ← q3kRing.mul_assoc x.2.2 y.1 z.2.1,
        ← q3kRing.mul_assoc x.2.2 y.2.1 z.1,
        ← q3kRing.mul_assoc x.2.2 q3kZeta9 (q3kRing.mul y.2.2 z.2.2),
        q3kRing.mul_comm x.2.2 q3kZeta9,
        q3kRing.mul_assoc q3kZeta9 x.2.2 (q3kRing.mul y.2.2 z.2.2),
        ← q3kRing.mul_assoc x.2.2 y.2.2 z.2.2]
    rw [q3kRing.left_distrib q3kZeta9
          (q3kRing.add (q3kRing.add (q3kRing.mul (q3kRing.mul x.2.1 y.1) z.2.2) (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.1)) (q3kRing.mul (q3kRing.mul x.2.1 y.2.2) z.1))
          (q3kRing.add (q3kRing.add (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.2.1) (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.2) z.2.2))),
        q3kRing.left_distrib q3kZeta9 (q3kRing.add (q3kRing.mul (q3kRing.mul x.2.1 y.1) z.2.2) (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.1)) (q3kRing.mul (q3kRing.mul x.2.1 y.2.2) z.1),
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.1) z.2.2) (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.1),
        q3kRing.left_distrib q3kZeta9 (q3kRing.add (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.2.1) (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.2) z.2.2)),
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.2.1) (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.1)]
    exact q27k_perm0
      (q3kRing.mul (q3kRing.mul x.1 y.1) z.1)
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.2.2) z.1))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.1))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 y.2.1) z.2.2))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.1) z.2.2))
      (q3kRing.mul q3kZeta9 (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.2) z.2.2)))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 y.2.2) z.2.1))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.1))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.2.1))
  · -- 成分 1（Y 部）
    rw [q27kMul_1, q27kMul_0, q27kMul_1, q27kMul_2,
        q27kMul_1, q27kMul_1, q27kMul_0, q27kMul_2,
        q27k_M_eq, q27k_A_eq]
    rw [q3kRing.right_distrib (q3kRing.mul x.1 y.1) (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1))) z.2.1,
        q3kRing.mul_assoc q3kZeta9 (q3kRing.add (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1)) z.2.1,
        q3kRing.right_distrib (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1) z.2.1,
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.2.2) z.2.1) (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.2.1),
        q3kRing.right_distrib (q3kRing.add (q3kRing.mul x.1 y.2.1) (q3kRing.mul x.2.1 y.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 y.2.2)) z.1,
        q3kRing.right_distrib (q3kRing.mul x.1 y.2.1) (q3kRing.mul x.2.1 y.1) z.1,
        q3kRing.mul_assoc q3kZeta9 (q3kRing.mul x.2.2 y.2.2) z.1,
        q3kRing.right_distrib (q3kRing.add (q3kRing.mul x.1 y.2.2) (q3kRing.mul x.2.1 y.2.1)) (q3kRing.mul x.2.2 y.1) z.2.2,
        q3kRing.right_distrib (q3kRing.mul x.1 y.2.2) (q3kRing.mul x.2.1 y.2.1) z.2.2,
        q3kRing.left_distrib q3kZeta9 (q3kRing.add (q3kRing.mul (q3kRing.mul x.1 y.2.2) z.2.2) (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.2)) (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.2.2),
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 y.2.2) z.2.2) (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.2)]
    rw [q3kRing.left_distrib x.1 (q3kRing.add (q3kRing.mul y.1 z.2.1) (q3kRing.mul y.2.1 z.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul y.2.2 z.2.2)),
        q3kRing.left_distrib x.1 (q3kRing.mul y.1 z.2.1) (q3kRing.mul y.2.1 z.1),
        ← q3kRing.mul_assoc x.1 y.1 z.2.1,
        ← q3kRing.mul_assoc x.1 y.2.1 z.1,
        ← q3kRing.mul_assoc x.1 q3kZeta9 (q3kRing.mul y.2.2 z.2.2),
        q3kRing.mul_comm x.1 q3kZeta9,
        q3kRing.mul_assoc q3kZeta9 x.1 (q3kRing.mul y.2.2 z.2.2),
        ← q3kRing.mul_assoc x.1 y.2.2 z.2.2,
        q3kRing.left_distrib x.2.1 (q3kRing.mul y.1 z.1) (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1))),
        ← q3kRing.mul_assoc x.2.1 y.1 z.1,
        ← q3kRing.mul_assoc x.2.1 q3kZeta9 (q3kRing.add (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1)),
        q3kRing.mul_comm x.2.1 q3kZeta9,
        q3kRing.mul_assoc q3kZeta9 x.2.1 (q3kRing.add (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1)),
        q3kRing.left_distrib x.2.1 (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1),
        ← q3kRing.mul_assoc x.2.1 y.2.1 z.2.2,
        ← q3kRing.mul_assoc x.2.1 y.2.2 z.2.1,
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.2) (q3kRing.mul (q3kRing.mul x.2.1 y.2.2) z.2.1),
        q3kRing.left_distrib x.2.2 (q3kRing.add (q3kRing.mul y.1 z.2.2) (q3kRing.mul y.2.1 z.2.1)) (q3kRing.mul y.2.2 z.1),
        q3kRing.left_distrib x.2.2 (q3kRing.mul y.1 z.2.2) (q3kRing.mul y.2.1 z.2.1),
        ← q3kRing.mul_assoc x.2.2 y.1 z.2.2,
        ← q3kRing.mul_assoc x.2.2 y.2.1 z.2.1,
        ← q3kRing.mul_assoc x.2.2 y.2.2 z.1,
        q3kRing.left_distrib q3kZeta9 (q3kRing.add (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.2.2) (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.2.1)) (q3kRing.mul (q3kRing.mul x.2.2 y.2.2) z.1),
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.2.2) (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.2.1)]
    exact q27k_perm1
      (q3kRing.mul (q3kRing.mul x.1 y.1) z.2.1)
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.2.2) z.2.1))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.2.1))
      (q3kRing.mul (q3kRing.mul x.1 y.2.1) z.1)
      (q3kRing.mul (q3kRing.mul x.2.1 y.1) z.1)
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.2) z.1))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 y.2.2) z.2.2))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.2.2))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.2.2))
  · -- 成分 2（Y² 部）
    rw [q27kMul_2, q27kMul_0, q27kMul_1, q27kMul_2,
        q27kMul_2, q27kMul_2, q27kMul_1, q27kMul_0,
        q27k_M_eq, q27k_A_eq]
    rw [q3kRing.right_distrib (q3kRing.mul x.1 y.1) (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1))) z.2.2,
        q3kRing.mul_assoc q3kZeta9 (q3kRing.add (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1)) z.2.2,
        q3kRing.right_distrib (q3kRing.mul x.2.1 y.2.2) (q3kRing.mul x.2.2 y.2.1) z.2.2,
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.2.2) z.2.2) (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.2.2),
        q3kRing.right_distrib (q3kRing.add (q3kRing.mul x.1 y.2.1) (q3kRing.mul x.2.1 y.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 y.2.2)) z.2.1,
        q3kRing.right_distrib (q3kRing.mul x.1 y.2.1) (q3kRing.mul x.2.1 y.1) z.2.1,
        q3kRing.mul_assoc q3kZeta9 (q3kRing.mul x.2.2 y.2.2) z.2.1,
        q3kRing.right_distrib (q3kRing.add (q3kRing.mul x.1 y.2.2) (q3kRing.mul x.2.1 y.2.1)) (q3kRing.mul x.2.2 y.1) z.1,
        q3kRing.right_distrib (q3kRing.mul x.1 y.2.2) (q3kRing.mul x.2.1 y.2.1) z.1]
    rw [q3kRing.left_distrib x.1 (q3kRing.add (q3kRing.mul y.1 z.2.2) (q3kRing.mul y.2.1 z.2.1)) (q3kRing.mul y.2.2 z.1),
        q3kRing.left_distrib x.1 (q3kRing.mul y.1 z.2.2) (q3kRing.mul y.2.1 z.2.1),
        ← q3kRing.mul_assoc x.1 y.1 z.2.2,
        ← q3kRing.mul_assoc x.1 y.2.1 z.2.1,
        ← q3kRing.mul_assoc x.1 y.2.2 z.1,
        q3kRing.left_distrib x.2.1 (q3kRing.add (q3kRing.mul y.1 z.2.1) (q3kRing.mul y.2.1 z.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul y.2.2 z.2.2)),
        q3kRing.left_distrib x.2.1 (q3kRing.mul y.1 z.2.1) (q3kRing.mul y.2.1 z.1),
        ← q3kRing.mul_assoc x.2.1 y.1 z.2.1,
        ← q3kRing.mul_assoc x.2.1 y.2.1 z.1,
        ← q3kRing.mul_assoc x.2.1 q3kZeta9 (q3kRing.mul y.2.2 z.2.2),
        q3kRing.mul_comm x.2.1 q3kZeta9,
        q3kRing.mul_assoc q3kZeta9 x.2.1 (q3kRing.mul y.2.2 z.2.2),
        ← q3kRing.mul_assoc x.2.1 y.2.2 z.2.2,
        q3kRing.left_distrib x.2.2 (q3kRing.mul y.1 z.1) (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1))),
        ← q3kRing.mul_assoc x.2.2 y.1 z.1,
        ← q3kRing.mul_assoc x.2.2 q3kZeta9 (q3kRing.add (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1)),
        q3kRing.mul_comm x.2.2 q3kZeta9,
        q3kRing.mul_assoc q3kZeta9 x.2.2 (q3kRing.add (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1)),
        q3kRing.left_distrib x.2.2 (q3kRing.mul y.2.1 z.2.2) (q3kRing.mul y.2.2 z.2.1),
        ← q3kRing.mul_assoc x.2.2 y.2.1 z.2.2,
        ← q3kRing.mul_assoc x.2.2 y.2.2 z.2.1,
        q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.2.2) (q3kRing.mul (q3kRing.mul x.2.2 y.2.2) z.2.1)]
    exact q27k_perm2
      (q3kRing.mul (q3kRing.mul x.1 y.1) z.2.2)
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 y.2.2) z.2.2))
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.1) z.2.2))
      (q3kRing.mul (q3kRing.mul x.1 y.2.1) z.2.1)
      (q3kRing.mul (q3kRing.mul x.2.1 y.1) z.2.1)
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 y.2.2) z.2.1))
      (q3kRing.mul (q3kRing.mul x.1 y.2.2) z.1)
      (q3kRing.mul (q3kRing.mul x.2.1 y.2.1) z.1)
      (q3kRing.mul (q3kRing.mul x.2.2 y.1) z.1)

/-- **q27k-2f（★）: 可換環 O_M = M = L₂[Y]/(Y³−ζ₃)**。 -/
def q27kRing : CRing where
  carrier := q27kCar
  add := q27kAdd
  zero := q27kZero
  neg := q27kNeg
  mul := q27kMul
  one := q27kOne
  add_assoc := fun a b c => q27k_ext (q3kRing.add_assoc a.1 b.1 c.1)
    (q3kRing.add_assoc a.2.1 b.2.1 c.2.1) (q3kRing.add_assoc a.2.2 b.2.2 c.2.2)
  zero_add := fun a => q27k_ext (q3kRing.zero_add a.1) (q3kRing.zero_add a.2.1)
    (q3kRing.zero_add a.2.2)
  neg_add := fun a => q27k_ext (q3kRing.neg_add a.1) (q3kRing.neg_add a.2.1)
    (q3kRing.neg_add a.2.2)
  add_comm := fun a b => q27k_ext (q3kRing.add_comm a.1 b.1)
    (q3kRing.add_comm a.2.1 b.2.1) (q3kRing.add_comm a.2.2 b.2.2)
  mul_assoc := q27k_mul_assoc
  one_mul := q27k_one_mul
  mul_comm := q27k_mul_comm
  left_distrib := q27k_left_distrib

/-! ## q27k-3: ζ₃ = q3kEmbed q3rqZeta の q3kRing 形補題（相対 Galois τ 用・embed 経由） -/

/-- 相対 Galois スカラー ζ₃ = M₉ 内の実 1 の原始 3 乗根（= embed(q3rqZeta)）。 -/
def q27kZeta3 : q3kCar := q3kEmbed q3rqZeta
/-- ζ₃² = embed(q3rqZetaSq)。 -/
def q27kZeta3Sq : q3kCar := q3kEmbed q3rqZetaSq

/-- ζ₃·ζ₃² = 1（q3kRing 形・embed 経由）。 -/
theorem q27k_z_zsqR1 : q3kRing.mul q27kZeta3 q27kZeta3Sq = q3kRing.one := by
  show q3kMul (q3kEmbed q3rqZeta) (q3kEmbed q3rqZetaSq) = q3kOne
  rw [q3k_embed_mul]
  show q3kEmbed (q3rqRing.mul q3rqZeta q3rqZetaSq) = q3kOne
  rw [q3k_z_zsqR1]; exact q3k_embed_one
/-- ζ₃²·ζ₃ = 1。 -/
theorem q27k_zsq_zR1 : q3kRing.mul q27kZeta3Sq q27kZeta3 = q3kRing.one := by
  show q3kMul (q3kEmbed q3rqZetaSq) (q3kEmbed q3rqZeta) = q3kOne
  rw [q3k_embed_mul]
  show q3kEmbed (q3rqRing.mul q3rqZetaSq q3rqZeta) = q3kOne
  rw [q3k_zsq_zR1]; exact q3k_embed_one
/-- ζ₃²·ζ₃² = ζ₃。 -/
theorem q27k_zsq_zsqR : q3kRing.mul q27kZeta3Sq q27kZeta3Sq = q27kZeta3 := by
  show q3kMul (q3kEmbed q3rqZetaSq) (q3kEmbed q3rqZetaSq) = q3kEmbed q3rqZeta
  rw [q3k_embed_mul]
  show q3kEmbed (q3rqRing.mul q3rqZetaSq q3rqZetaSq) = q3kEmbed q3rqZeta
  rw [q3k_zsq_zsqR]
/-- ζ₃·ζ₃ = ζ₃²。 -/
theorem q27k_z_zR : q3kRing.mul q27kZeta3 q27kZeta3 = q27kZeta3Sq := by
  show q3kMul (q3kEmbed q3rqZeta) (q3kEmbed q3rqZeta) = q3kEmbed q3rqZetaSq
  rw [q3k_embed_mul]
  show q3kEmbed (q3rqRing.mul q3rqZeta q3rqZeta) = q3kEmbed q3rqZetaSq
  rw [q3k_z_zR]
/-- ζ₃³ = 1。 -/
theorem q27k_z3R : q3kRing.mul (q3kRing.mul q27kZeta3 q27kZeta3) q27kZeta3 = q3kRing.one := by
  show q3kMul (q3kMul (q3kEmbed q3rqZeta) (q3kEmbed q3rqZeta)) (q3kEmbed q3rqZeta) = q3kOne
  rw [q3k_embed_mul, q3k_embed_mul]
  show q3kEmbed (q3rqRing.mul (q3rqRing.mul q3rqZeta q3rqZeta) q3rqZeta) = q3kOne
  rw [q3k_z3R]; exact q3k_embed_one

/-- embed の加法準同型（成分ごと・0+0=0）。 -/
theorem q27k_embed_add (a b : q3rqCar) :
    q3kAdd (q3kEmbed a) (q3kEmbed b) = q3kEmbed (q3rqAdd a b) := by
  apply q3k_ext
  · rfl
  · exact q3rqRing.zero_add q3rqZero
  · exact q3rqRing.zero_add q3rqZero

/-- **q27k-3a（★）: 1 + ζ₃ + ζ₃² = 0**（M₉ 内の実円分関係・τ ノルムの Z,Z² 消去の要）。 -/
theorem q27k_zeta_sum_zero :
    q3kAdd q3kOne (q3kAdd q27kZeta3 q27kZeta3Sq) = q3kZero := by
  show q3kAdd (q3kEmbed q3rqOne) (q3kAdd (q3kEmbed q3rqZeta) (q3kEmbed q3rqZetaSq)) = q3kZero
  rw [q27k_embed_add q3rqZeta q3rqZetaSq]
  show q3kAdd (q3kEmbed q3rqOne) (q3kEmbed (q3rqAdd q3rqZeta q3rqZetaSq)) = q3kZero
  rw [q27k_embed_add q3rqOne (q3rqAdd q3rqZeta q3rqZetaSq), q3k_zeta_sum_zero]
  rfl

/-! ## q27k-4: 相対 Galois σ（Y ↦ ζ₃Y・位数 3） -/

/-- **q27k-4a: σ** = a + ζ₃bY + ζ₃²cY²（相対 Galois 自己同型）。 -/
def q27kSigma (x : q27kCar) : q27kCar :=
  ((x.1, q3kMul q27kZeta3 x.2.1, q3kMul q27kZeta3Sq x.2.2) : q27kCar)
theorem q27kSigma_0 (x : q27kCar) : (q27kSigma x).1 = x.1 := rfl
theorem q27kSigma_1 (x : q27kCar) : (q27kSigma x).2.1 = q3kMul q27kZeta3 x.2.1 := rfl
theorem q27kSigma_2 (x : q27kCar) : (q27kSigma x).2.2 = q3kMul q27kZeta3Sq x.2.2 := rfl

/-- σ(1) = 1。 -/
theorem q27k_sigma_one : q27kSigma q27kOne = q27kOne := by
  apply q27k_ext
  · rfl
  · exact q3kRing.mul_zero q27kZeta3
  · exact q3kRing.mul_zero q27kZeta3Sq

/-- **q27k-4b（★）: σ は環準同型** σ(xy)=σx·σy（ζ₃·ζ₃²=1 等で ζ 冪を還元）。 -/
theorem q27k_sigma_mul (x y : q27kCar) :
    q27kSigma (q27kMul x y) = q27kMul (q27kSigma x) (q27kSigma y) := by
  apply q27k_ext
  · rw [q27kSigma_0, q27kMul_0, q27kMul_0, q27kSigma_0, q27kSigma_0,
        q27kSigma_1, q27kSigma_2, q27kSigma_2, q27kSigma_1, q27k_M_eq, q27k_A_eq]
    rw [q3kRing.mul_mul_mul_comm q27kZeta3 x.2.1 q27kZeta3Sq y.2.2,
        q3kRing.mul_mul_mul_comm q27kZeta3Sq x.2.2 q27kZeta3 y.2.1,
        q27k_z_zsqR1, q27k_zsq_zR1,
        q3kRing.one_mul (q3kRing.mul x.2.1 y.2.2),
        q3kRing.one_mul (q3kRing.mul x.2.2 y.2.1)]
  · rw [q27kSigma_1, q27kMul_1, q27kMul_1, q27kSigma_0, q27kSigma_1, q27kSigma_1,
        q27kSigma_0, q27kSigma_2, q27kSigma_2, q27k_M_eq, q27k_A_eq]
    rw [q3kRing.mul_mul_mul_comm q27kZeta3Sq x.2.2 q27kZeta3Sq y.2.2, q27k_zsq_zsqR,
        q3kRing.left_distrib q27kZeta3 (q3kRing.add (q3kRing.mul x.1 y.2.1) (q3kRing.mul x.2.1 y.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 y.2.2)),
        q3kRing.left_distrib q27kZeta3 (q3kRing.mul x.1 y.2.1) (q3kRing.mul x.2.1 y.1),
        ← q3kRing.mul_assoc q27kZeta3 x.1 y.2.1, q3kRing.mul_comm q27kZeta3 x.1, q3kRing.mul_assoc x.1 q27kZeta3 y.2.1,
        ← q3kRing.mul_assoc q27kZeta3 x.2.1 y.1,
        ← q3kRing.mul_assoc q27kZeta3 q3kZeta9 (q3kRing.mul x.2.2 y.2.2),
        q3kRing.mul_comm q27kZeta3 q3kZeta9,
        q3kRing.mul_assoc q3kZeta9 q27kZeta3 (q3kRing.mul x.2.2 y.2.2)]
  · rw [q27kSigma_2, q27kMul_2, q27kMul_2, q27kSigma_0, q27kSigma_2, q27kSigma_1,
        q27kSigma_1, q27kSigma_2, q27kSigma_0, q27k_M_eq, q27k_A_eq]
    rw [q3kRing.mul_mul_mul_comm q27kZeta3 x.2.1 q27kZeta3 y.2.1, q27k_z_zR,
        q3kRing.left_distrib q27kZeta3Sq (q3kRing.add (q3kRing.mul x.1 y.2.2) (q3kRing.mul x.2.1 y.2.1)) (q3kRing.mul x.2.2 y.1),
        q3kRing.left_distrib q27kZeta3Sq (q3kRing.mul x.1 y.2.2) (q3kRing.mul x.2.1 y.2.1),
        ← q3kRing.mul_assoc q27kZeta3Sq x.1 y.2.2, q3kRing.mul_comm q27kZeta3Sq x.1, q3kRing.mul_assoc x.1 q27kZeta3Sq y.2.2,
        ← q3kRing.mul_assoc q27kZeta3Sq x.2.2 y.1]

/-- **q27k-4c: σ²** = a + ζ₃²bY + ζ₃cY²（還元済み・σ∘σ に一致）。 -/
def q27kSigma2 (x : q27kCar) : q27kCar :=
  ((x.1, q3kMul q27kZeta3Sq x.2.1, q3kMul q27kZeta3 x.2.2) : q27kCar)
theorem q27kSigma2_0 (x : q27kCar) : (q27kSigma2 x).1 = x.1 := rfl
theorem q27kSigma2_1 (x : q27kCar) : (q27kSigma2 x).2.1 = q3kMul q27kZeta3Sq x.2.1 := rfl
theorem q27kSigma2_2 (x : q27kCar) : (q27kSigma2 x).2.2 = q3kMul q27kZeta3 x.2.2 := rfl

/-- σ² = σ∘σ。 -/
theorem q27k_sigma2_comp (x : q27kCar) : q27kSigma2 x = q27kSigma (q27kSigma x) := by
  apply q27k_ext
  · rfl
  · show q3kMul q27kZeta3Sq x.2.1 = q3kMul q27kZeta3 (q3kMul q27kZeta3 x.2.1)
    rw [q27k_M_eq, ← q3kRing.mul_assoc q27kZeta3 q27kZeta3 x.2.1, q27k_z_zR]
  · show q3kMul q27kZeta3 x.2.2 = q3kMul q27kZeta3Sq (q3kMul q27kZeta3Sq x.2.2)
    rw [q27k_M_eq, ← q3kRing.mul_assoc q27kZeta3Sq q27kZeta3Sq x.2.2, q27k_zsq_zsqR]

/-- **q27k-4d（★）: σ³ = id**（位数ちょうど 3・ζ₃³=1）。 -/
theorem q27k_sigma3_id (x : q27kCar) :
    q27kSigma (q27kSigma (q27kSigma x)) = x := by
  apply q27k_ext
  · rfl
  · show q3kMul q27kZeta3 (q3kMul q27kZeta3 (q3kMul q27kZeta3 x.2.1)) = x.2.1
    rw [q27k_M_eq, ← q3kRing.mul_assoc q27kZeta3 q27kZeta3 (q3kRing.mul q27kZeta3 x.2.1),
        ← q3kRing.mul_assoc (q3kRing.mul q27kZeta3 q27kZeta3) q27kZeta3 x.2.1, q27k_z3R,
        q3kRing.one_mul x.2.1]
  · show q3kMul q27kZeta3Sq (q3kMul q27kZeta3Sq (q3kMul q27kZeta3Sq x.2.2)) = x.2.2
    rw [q27k_M_eq, ← q3kRing.mul_assoc q27kZeta3Sq q27kZeta3Sq (q3kRing.mul q27kZeta3Sq x.2.2),
        q27k_zsq_zsqR, ← q3kRing.mul_assoc q27kZeta3 q27kZeta3Sq x.2.2, q27k_z_zsqR1,
        q3kRing.one_mul x.2.2]

end IUT
