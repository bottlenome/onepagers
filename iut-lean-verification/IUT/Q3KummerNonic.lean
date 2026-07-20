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

/-- 反元ブリッジ。 -/
theorem q27k_N_eq : q3kNeg = q3kRing.neg := rfl

/-- t·(1+ζ₃+ζ₃²) = 0（円分関係の乗法版）。 -/
theorem q27k_sum3 (t : q3kCar) :
    q3kRing.add (q3kRing.add t (q3kRing.mul q27kZeta3 t)) (q3kRing.mul q27kZeta3Sq t)
      = q3kRing.zero := by
  have h : q3kRing.mul t (q3kRing.add q3kRing.one (q3kRing.add q27kZeta3 q27kZeta3Sq))
      = q3kRing.zero := by
    rw [show q3kRing.add q3kRing.one (q3kRing.add q27kZeta3 q27kZeta3Sq) = q3kZero
          from q27k_zeta_sum_zero]
    exact q3kRing.mul_zero t
  rw [q3kRing.left_distrib t q3kRing.one (q3kRing.add q27kZeta3 q27kZeta3Sq),
      q3kRing.left_distrib t q27kZeta3 q27kZeta3Sq, q3kRing.mul_one t,
      q3kRing.mul_comm t q27kZeta3, q3kRing.mul_comm t q27kZeta3Sq,
      ← q3kRing.add_assoc t (q3kRing.mul q27kZeta3 t) (q3kRing.mul q27kZeta3Sq t)] at h
  exact h
/-- t + ζ₃²t = −ζ₃t。 -/
theorem q27k_bc (t : q3kCar) :
    q3kRing.add t (q3kRing.mul q27kZeta3Sq t) = q3kRing.neg (q3kRing.mul q27kZeta3 t) := by
  have h := q27k_sum3 t
  rw [q3kRing.add_assoc t (q3kRing.mul q27kZeta3 t) (q3kRing.mul q27kZeta3Sq t),
      q3kRing.add_comm (q3kRing.mul q27kZeta3 t) (q3kRing.mul q27kZeta3Sq t),
      ← q3kRing.add_assoc t (q3kRing.mul q27kZeta3Sq t) (q3kRing.mul q27kZeta3 t)] at h
  have h3 := congrArg q3kRing.neg (q3kRing.neg_eq_of_add_eq_zero h)
  rw [q3kRing.neg_neg] at h3
  exact h3
/-- ζ₃²t + ζ₃t = −t。 -/
theorem q27k_bc2 (t : q3kCar) :
    q3kRing.add (q3kRing.mul q27kZeta3Sq t) (q3kRing.mul q27kZeta3 t) = q3kRing.neg t := by
  have h := q27k_sum3 t
  rw [q3kRing.add_assoc t (q3kRing.mul q27kZeta3 t) (q3kRing.mul q27kZeta3Sq t),
      q3kRing.add_comm t (q3kRing.add (q3kRing.mul q27kZeta3 t) (q3kRing.mul q27kZeta3Sq t)),
      q3kRing.add_comm (q3kRing.mul q27kZeta3 t) (q3kRing.mul q27kZeta3Sq t)] at h
  have h3 := congrArg q3kRing.neg (q3kRing.neg_eq_of_add_eq_zero h)
  rw [q3kRing.neg_neg] at h3
  exact h3
/-- ζ₃t + ζ₃²t = −t。 -/
theorem q27k_bc3 (t : q3kCar) :
    q3kRing.add (q3kRing.mul q27kZeta3 t) (q3kRing.mul q27kZeta3Sq t) = q3kRing.neg t := by
  rw [q3kRing.add_comm (q3kRing.mul q27kZeta3 t) (q3kRing.mul q27kZeta3Sq t)]
  exact q27k_bc2 t
/-- **q27k-5a: w = σx·σ²x**（共役積の閉形式・1+ζ₃+ζ₃²=0 使用）。 -/
def q27kWt (x : q27kCar) : q27kCar :=
  ((q3kAdd (q3kMul x.1 x.1) (q3kNeg (q3kMul q3kZeta9 (q3kMul x.2.1 x.2.2))),
    q3kAdd (q3kNeg (q3kMul x.1 x.2.1)) (q3kMul q3kZeta9 (q3kMul x.2.2 x.2.2)),
    q3kAdd (q3kMul x.2.1 x.2.1) (q3kNeg (q3kMul x.1 x.2.2))) : q27kCar)
theorem q27kWt_0 (x : q27kCar) : (q27kWt x).1 = q3kAdd (q3kMul x.1 x.1) (q3kNeg (q3kMul q3kZeta9 (q3kMul x.2.1 x.2.2))) := rfl
theorem q27kWt_1 (x : q27kCar) : (q27kWt x).2.1 = q3kAdd (q3kNeg (q3kMul x.1 x.2.1)) (q3kMul q3kZeta9 (q3kMul x.2.2 x.2.2)) := rfl
theorem q27kWt_2 (x : q27kCar) : (q27kWt x).2.2 = q3kAdd (q3kMul x.2.1 x.2.1) (q3kNeg (q3kMul x.1 x.2.2)) := rfl
/-- 基底環の埋め込み O_{L₂} ↪ M, n ↦ (n,0,0)。 -/
def q27kEmbed (n : q3kCar) : q27kCar := ((n, q3kZero, q3kZero) : q27kCar)
theorem q27kEmbed_0 (n : q3kCar) : (q27kEmbed n).1 = n := rfl
theorem q27kEmbed_1 (n : q3kCar) : (q27kEmbed n).2.1 = q3kZero := rfl
theorem q27kEmbed_2 (n : q3kCar) : (q27kEmbed n).2.2 = q3kZero := rfl

/-- 6 項相殺（Y 成分消去）。 -/
theorem q27k_cancel6a (A1 A2 A3 : q3kCar) :
    q3kRing.add (q3kRing.add (q3kRing.add (q3kRing.neg A1) A2) (q3kRing.add A1 (q3kRing.neg A3)))
      (q3kRing.add A3 (q3kRing.neg A2)) = q3kRing.zero := by
  rw [q3kRing.add_assoc (q3kRing.add (q3kRing.neg A1) A2) (q3kRing.add A1 (q3kRing.neg A3)) (q3kRing.add A3 (q3kRing.neg A2)),
      q3kRing.add_assoc A1 (q3kRing.neg A3) (q3kRing.add A3 (q3kRing.neg A2)),
      ← q3kRing.add_assoc (q3kRing.neg A3) A3 (q3kRing.neg A2), q3kRing.neg_add A3, q3kRing.zero_add (q3kRing.neg A2),
      q3kRing.add_assoc (q3kRing.neg A1) A2 (q3kRing.add A1 (q3kRing.neg A2)),
      ← q3kRing.add_assoc A2 A1 (q3kRing.neg A2), q3kRing.add_comm A2 A1, q3kRing.add_assoc A1 A2 (q3kRing.neg A2),
      q3kRing.add_neg A2, q3kRing.add_zero A1, q3kRing.neg_add A1]
/-- 6 項相殺（Y² 成分消去）。 -/
theorem q27k_cancel6b (B1 B2 B3 : q3kCar) :
    q3kRing.add (q3kRing.add (q3kRing.add B1 (q3kRing.neg B2)) (q3kRing.add (q3kRing.neg B1) B3))
      (q3kRing.add B2 (q3kRing.neg B3)) = q3kRing.zero := by
  rw [q3kRing.add_assoc (q3kRing.add B1 (q3kRing.neg B2)) (q3kRing.add (q3kRing.neg B1) B3) (q3kRing.add B2 (q3kRing.neg B3)),
      q3kRing.add_assoc (q3kRing.neg B1) B3 (q3kRing.add B2 (q3kRing.neg B3)),
      ← q3kRing.add_assoc B3 B2 (q3kRing.neg B3), q3kRing.add_comm B3 B2, q3kRing.add_assoc B2 B3 (q3kRing.neg B3),
      q3kRing.add_neg B3, q3kRing.add_zero B2,
      q3kRing.add_assoc B1 (q3kRing.neg B2) (q3kRing.add (q3kRing.neg B1) B2),
      ← q3kRing.add_assoc (q3kRing.neg B2) (q3kRing.neg B1) B2, q3kRing.add_comm (q3kRing.neg B2) (q3kRing.neg B1),
      q3kRing.add_assoc (q3kRing.neg B1) (q3kRing.neg B2) B2, q3kRing.neg_add B2, q3kRing.add_zero (q3kRing.neg B1),
      q3kRing.add_neg B1]
/-- 実 3 = 1+1+1 ∈ O_{L₂}。 -/
def q27kThree : q3kCar := q3kAdd q3kOne (q3kAdd q3kOne q3kOne)
/-- −(3·K) = −K + (−K + −K)。 -/
theorem q27k_three_K (K : q3kCar) :
    q3kRing.neg (q3kRing.mul q27kThree K)
      = q3kRing.add (q3kRing.neg K) (q3kRing.add (q3kRing.neg K) (q3kRing.neg K)) := by
  show q3kRing.neg (q3kRing.mul (q3kRing.add q3kRing.one (q3kRing.add q3kRing.one q3kRing.one)) K) = _
  rw [q3kRing.right_distrib q3kRing.one (q3kRing.add q3kRing.one q3kRing.one) K,
      q3kRing.right_distrib q3kRing.one q3kRing.one K, q3kRing.one_mul K,
      q3kRing.neg_add_dist K (q3kRing.add K K), q3kRing.neg_add_dist K K]
/-- 3 次ノルムの −3K 収集（多項式簿記）。 -/
theorem q27k_norm_collect (P Q R K : q3kCar) :
    q3kRing.add (q3kRing.add P (q3kRing.neg K))
      (q3kRing.add (q3kRing.add Q (q3kRing.neg K)) (q3kRing.add (q3kRing.neg K) R))
    = q3kRing.add (q3kRing.add (q3kRing.add P Q) R) (q3kRing.neg (q3kRing.mul q27kThree K)) := by
  rw [q27k_three_K K,
      q3kRing.add_assoc P (q3kRing.neg K) (q3kRing.add (q3kRing.add Q (q3kRing.neg K)) (q3kRing.add (q3kRing.neg K) R)),
      q3kRing.add_assoc Q (q3kRing.neg K) (q3kRing.add (q3kRing.neg K) R),
      q3kRing.add_assoc (q3kRing.add P Q) R (q3kRing.add (q3kRing.neg K) (q3kRing.add (q3kRing.neg K) (q3kRing.neg K))),
      q3kRing.add_assoc P Q (q3kRing.add R (q3kRing.add (q3kRing.neg K) (q3kRing.add (q3kRing.neg K) (q3kRing.neg K)))),
      q27k_add_swap (q3kRing.neg K) Q (q3kRing.add (q3kRing.neg K) (q3kRing.add (q3kRing.neg K) R)),
      q3kRing.add_comm (q3kRing.neg K) R,
      q27k_add_swap (q3kRing.neg K) R (q3kRing.neg K),
      q27k_add_swap (q3kRing.neg K) R (q3kRing.add (q3kRing.neg K) (q3kRing.neg K))]

/-- **q27k-5c: 相対 3 次ノルム多項式** N=a³+ζ₉b³+ζ₉²c³−3ζ₉abc（O_{M₉} 値・ζ₉=q3kZeta9 は twist）。 -/
def q27kNormBase (x : q27kCar) : q3kCar :=
  q3kAdd (q3kAdd (q3kAdd (q3kMul (q3kMul x.1 x.1) x.1)
      (q3kMul q3kZeta9 (q3kMul (q3kMul x.2.1 x.2.1) x.2.1)))
      (q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kMul (q3kMul x.2.2 x.2.2) x.2.2)))
    (q3kNeg (q3kMul q27kThree (q3kMul q3kZeta9 (q3kMul (q3kMul x.1 x.2.1) x.2.2))))
/-- **q27k-5b（★）: σx·σ²x = w**（ζ 冪還元＋円分関係）。 -/
theorem q27k_w_eq (x : q27kCar) : q27kMul (q27kSigma x) (q27kSigma2 x) = q27kWt x := by
  apply q27k_ext
  · rw [q27kMul_0, q27kSigma_0, q27kSigma2_0, q27kSigma_1, q27kSigma2_2, q27kSigma_2, q27kSigma2_1,
        q27kWt_0, q27k_M_eq, q27k_A_eq, q27k_N_eq,
        q3kRing.mul_mul_mul_comm q27kZeta3 x.2.1 q27kZeta3 x.2.2, q27k_z_zR,
        q3kRing.mul_mul_mul_comm q27kZeta3Sq x.2.2 q27kZeta3Sq x.2.1, q27k_zsq_zsqR,
        q3kRing.mul_comm x.2.2 x.2.1,
        q27k_bc2 (q3kRing.mul x.2.1 x.2.2),
        q3kRing.mul_neg q3kZeta9 (q3kRing.mul x.2.1 x.2.2)]
  · rw [q27kMul_1, q27kSigma_0, q27kSigma2_1, q27kSigma_1, q27kSigma2_0, q27kSigma_2, q27kSigma2_2,
        q27kWt_1, q27k_M_eq, q27k_A_eq, q27k_N_eq,
        q3kRing.mul_mul_mul_comm q27kZeta3Sq x.2.2 q27kZeta3 x.2.2, q27k_zsq_zR1, q3kRing.one_mul (q3kRing.mul x.2.2 x.2.2),
        ← q3kRing.mul_assoc x.1 q27kZeta3Sq x.2.1, q3kRing.mul_comm x.1 q27kZeta3Sq, q3kRing.mul_assoc q27kZeta3Sq x.1 x.2.1,
        q3kRing.mul_assoc q27kZeta3 x.2.1 x.1, q3kRing.mul_comm x.2.1 x.1,
        q27k_bc2 (q3kRing.mul x.1 x.2.1)]
  · rw [q27kMul_2, q27kSigma_0, q27kSigma2_2, q27kSigma_1, q27kSigma2_1, q27kSigma_2, q27kSigma2_0,
        q27kWt_2, q27k_M_eq, q27k_A_eq, q27k_N_eq,
        q3kRing.mul_mul_mul_comm q27kZeta3 x.2.1 q27kZeta3Sq x.2.1, q27k_z_zsqR1, q3kRing.one_mul (q3kRing.mul x.2.1 x.2.1),
        ← q3kRing.mul_assoc x.1 q27kZeta3 x.2.2, q3kRing.mul_comm x.1 q27kZeta3, q3kRing.mul_assoc q27kZeta3 x.1 x.2.2,
        q3kRing.mul_assoc q27kZeta3Sq x.2.2 x.1, q3kRing.mul_comm x.2.2 x.1,
        q3kRing.add_assoc (q3kRing.mul q27kZeta3 (q3kRing.mul x.1 x.2.2)) (q3kRing.mul x.2.1 x.2.1) (q3kRing.mul q27kZeta3Sq (q3kRing.mul x.1 x.2.2)),
        q3kRing.add_comm (q3kRing.mul x.2.1 x.2.1) (q3kRing.mul q27kZeta3Sq (q3kRing.mul x.1 x.2.2)),
        ← q3kRing.add_assoc (q3kRing.mul q27kZeta3 (q3kRing.mul x.1 x.2.2)) (q3kRing.mul q27kZeta3Sq (q3kRing.mul x.1 x.2.2)) (q3kRing.mul x.2.1 x.2.1),
        q27k_bc3 (q3kRing.mul x.1 x.2.2),
        q3kRing.add_comm (q3kRing.neg (q3kRing.mul x.1 x.2.2)) (q3kRing.mul x.2.1 x.2.1)]
/-- N の定数成分 = ノルム多項式。 -/
theorem q27k_xwt_0 (x : q27kCar) : (q27kMul x (q27kWt x)).1 = q27kNormBase x := by
  rw [q27kMul_0, q27kWt_0, q27kWt_1, q27kWt_2, q27k_M_eq, q27k_A_eq, q27k_N_eq]
  show _ = q3kRing.add (q3kRing.add (q3kRing.add (q3kRing.mul (q3kRing.mul x.1 x.1) x.1)
      (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 x.2.1) x.2.1)))
      (q3kRing.mul (q3kRing.mul q3kZeta9 q3kZeta9) (q3kRing.mul (q3kRing.mul x.2.2 x.2.2) x.2.2)))
    (q3kRing.neg (q3kRing.mul q27kThree (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 x.2.1) x.2.2))))
  rw [q3kRing.left_distrib x.1 (q3kRing.mul x.1 x.1) (q3kRing.neg (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.1 x.2.2))),
      ← q3kRing.mul_assoc x.1 x.1 x.1,
      q3kRing.mul_neg x.1 (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.1 x.2.2)),
      ← q3kRing.mul_assoc x.1 q3kZeta9 (q3kRing.mul x.2.1 x.2.2),
      q3kRing.mul_comm x.1 q3kZeta9,
      q3kRing.mul_assoc q3kZeta9 x.1 (q3kRing.mul x.2.1 x.2.2),
      ← q3kRing.mul_assoc x.1 x.2.1 x.2.2,
      q3kRing.left_distrib x.2.1 (q3kRing.mul x.2.1 x.2.1) (q3kRing.neg (q3kRing.mul x.1 x.2.2)),
      ← q3kRing.mul_assoc x.2.1 x.2.1 x.2.1,
      q3kRing.mul_neg x.2.1 (q3kRing.mul x.1 x.2.2),
      ← q3kRing.mul_assoc x.2.1 x.1 x.2.2,
      q3kRing.mul_comm x.2.1 x.1,
      q3kRing.left_distrib x.2.2 (q3kRing.neg (q3kRing.mul x.1 x.2.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 x.2.2)),
      q3kRing.mul_neg x.2.2 (q3kRing.mul x.1 x.2.1),
      q3kRing.mul_comm x.2.2 (q3kRing.mul x.1 x.2.1),
      ← q3kRing.mul_assoc x.2.2 q3kZeta9 (q3kRing.mul x.2.2 x.2.2),
      q3kRing.mul_comm x.2.2 q3kZeta9,
      q3kRing.mul_assoc q3kZeta9 x.2.2 (q3kRing.mul x.2.2 x.2.2),
      ← q3kRing.mul_assoc x.2.2 x.2.2 x.2.2,
      q3kRing.left_distrib q3kZeta9 (q3kRing.add (q3kRing.mul (q3kRing.mul x.2.1 x.2.1) x.2.1) (q3kRing.neg (q3kRing.mul (q3kRing.mul x.1 x.2.1) x.2.2))) (q3kRing.add (q3kRing.neg (q3kRing.mul (q3kRing.mul x.1 x.2.1) x.2.2)) (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 x.2.2) x.2.2))),
      q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 x.2.1) x.2.1) (q3kRing.neg (q3kRing.mul (q3kRing.mul x.1 x.2.1) x.2.2)),
      q3kRing.mul_neg q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 x.2.1) x.2.2),
      q3kRing.left_distrib q3kZeta9 (q3kRing.neg (q3kRing.mul (q3kRing.mul x.1 x.2.1) x.2.2)) (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 x.2.2) x.2.2)),
      q3kRing.mul_neg q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 x.2.1) x.2.2),
      ← q3kRing.mul_assoc q3kZeta9 q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.2 x.2.2) x.2.2)]
  rw [q27k_norm_collect (q3kRing.mul (q3kRing.mul x.1 x.1) x.1)
        (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 x.2.1) x.2.1))
        (q3kRing.mul (q3kRing.mul q3kZeta9 q3kZeta9) (q3kRing.mul (q3kRing.mul x.2.2 x.2.2) x.2.2))
        (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 x.2.1) x.2.2))]
/-- N の Y 成分 = 0（相殺）。 -/
theorem q27k_xwt_1 (x : q27kCar) : (q27kMul x (q27kWt x)).2.1 = q3kZero := by
  rw [q27kMul_1, q27kWt_0, q27kWt_1, q27kWt_2, q27k_M_eq, q27k_A_eq, q27k_N_eq]
  rw [q3kRing.left_distrib x.1 (q3kRing.neg (q3kRing.mul x.1 x.2.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 x.2.2)),
      q3kRing.mul_neg x.1 (q3kRing.mul x.1 x.2.1),
      ← q3kRing.mul_assoc x.1 x.1 x.2.1,
      ← q3kRing.mul_assoc x.1 q3kZeta9 (q3kRing.mul x.2.2 x.2.2),
      q3kRing.mul_comm x.1 q3kZeta9,
      q3kRing.mul_assoc q3kZeta9 x.1 (q3kRing.mul x.2.2 x.2.2),
      ← q3kRing.mul_assoc x.1 x.2.2 x.2.2,
      q3kRing.left_distrib x.2.1 (q3kRing.mul x.1 x.1) (q3kRing.neg (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.1 x.2.2))),
      q3kRing.mul_comm x.2.1 (q3kRing.mul x.1 x.1),
      q3kRing.mul_neg x.2.1 (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.1 x.2.2)),
      ← q3kRing.mul_assoc x.2.1 q3kZeta9 (q3kRing.mul x.2.1 x.2.2),
      q3kRing.mul_comm x.2.1 q3kZeta9,
      q3kRing.mul_assoc q3kZeta9 x.2.1 (q3kRing.mul x.2.1 x.2.2),
      ← q3kRing.mul_assoc x.2.1 x.2.1 x.2.2,
      q3kRing.left_distrib x.2.2 (q3kRing.mul x.2.1 x.2.1) (q3kRing.neg (q3kRing.mul x.1 x.2.2)),
      q3kRing.mul_comm x.2.2 (q3kRing.mul x.2.1 x.2.1),
      q3kRing.mul_neg x.2.2 (q3kRing.mul x.1 x.2.2),
      q3kRing.mul_comm x.2.2 (q3kRing.mul x.1 x.2.2),
      q3kRing.left_distrib q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 x.2.1) x.2.2) (q3kRing.neg (q3kRing.mul (q3kRing.mul x.1 x.2.2) x.2.2)),
      q3kRing.mul_neg q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 x.2.2) x.2.2)]
  exact q27k_cancel6a (q3kRing.mul (q3kRing.mul x.1 x.1) x.2.1)
    (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.1 x.2.2) x.2.2))
    (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 x.2.1) x.2.2))
/-- N の Y² 成分 = 0（相殺）。 -/
theorem q27k_xwt_2 (x : q27kCar) : (q27kMul x (q27kWt x)).2.2 = q3kZero := by
  rw [q27kMul_2, q27kWt_0, q27kWt_1, q27kWt_2, q27k_M_eq, q27k_A_eq, q27k_N_eq]
  rw [q3kRing.left_distrib x.1 (q3kRing.mul x.2.1 x.2.1) (q3kRing.neg (q3kRing.mul x.1 x.2.2)),
      ← q3kRing.mul_assoc x.1 x.2.1 x.2.1,
      q3kRing.mul_neg x.1 (q3kRing.mul x.1 x.2.2),
      ← q3kRing.mul_assoc x.1 x.1 x.2.2,
      q3kRing.left_distrib x.2.1 (q3kRing.neg (q3kRing.mul x.1 x.2.1)) (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 x.2.2)),
      q3kRing.mul_neg x.2.1 (q3kRing.mul x.1 x.2.1),
      q3kRing.mul_comm x.2.1 (q3kRing.mul x.1 x.2.1),
      ← q3kRing.mul_assoc x.2.1 q3kZeta9 (q3kRing.mul x.2.2 x.2.2),
      q3kRing.mul_comm x.2.1 q3kZeta9,
      q3kRing.mul_assoc q3kZeta9 x.2.1 (q3kRing.mul x.2.2 x.2.2),
      ← q3kRing.mul_assoc x.2.1 x.2.2 x.2.2,
      q3kRing.left_distrib x.2.2 (q3kRing.mul x.1 x.1) (q3kRing.neg (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.1 x.2.2))),
      q3kRing.mul_comm x.2.2 (q3kRing.mul x.1 x.1),
      q3kRing.mul_neg x.2.2 (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.1 x.2.2)),
      ← q3kRing.mul_assoc x.2.2 q3kZeta9 (q3kRing.mul x.2.1 x.2.2),
      q3kRing.mul_comm x.2.2 q3kZeta9,
      q3kRing.mul_assoc q3kZeta9 x.2.2 (q3kRing.mul x.2.1 x.2.2),
      q3kRing.mul_comm x.2.2 (q3kRing.mul x.2.1 x.2.2)]
  exact q27k_cancel6b (q3kRing.mul (q3kRing.mul x.1 x.2.1) x.2.1)
    (q3kRing.mul (q3kRing.mul x.1 x.1) x.2.2)
    (q3kRing.mul q3kZeta9 (q3kRing.mul (q3kRing.mul x.2.1 x.2.2) x.2.2))
/-- x·w = embed(N)。 -/
theorem q27k_x_wt (x : q27kCar) : q27kMul x (q27kWt x) = q27kEmbed (q27kNormBase x) :=
  q27k_ext (q27k_xwt_0 x) (q27k_xwt_1 x) (q27k_xwt_2 x)

/-- **q27k-5d（★★）: 3 次ノルム恒等式** N(x)=x·σx·σ²x = embed(a³+ζ₃b³+ζ₃²c³−3ζ₃abc)。 -/
theorem q27k_norm_eq (x : q27kCar) :
    q27kMul x (q27kMul (q27kSigma x) (q27kSigma2 x)) = q27kEmbed (q27kNormBase x) := by
  rw [q27k_w_eq]; exact q27k_x_wt x
/-- 零元ブリッジ。 -/
theorem q27k_Z_eq : q3kZero = q3kRing.zero := rfl

/-- **q27k-5e: embed は環準同型（積）** embed(p)·embed(q)=embed(pq)。 -/
theorem q27k_embed_mul (p q : q3kCar) :
    q27kMul (q27kEmbed p) (q27kEmbed q) = q27kEmbed (q3kMul p q) := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul p q) (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul q3kZero q3kZero) (q3kRing.mul q3kZero q3kZero))) = q3kRing.mul p q
    rw [q27k_Z_eq, q3kRing.mul_zero q3kRing.zero, q3kRing.zero_add q3kRing.zero, q3kRing.mul_zero q3kZeta9, q3kRing.add_zero (q3kRing.mul p q)]
  · show q3kRing.add (q3kRing.add (q3kRing.mul p q3kZero) (q3kRing.mul q3kZero q)) (q3kRing.mul q3kZeta9 (q3kRing.mul q3kZero q3kZero)) = q3kRing.zero
    rw [q27k_Z_eq, q3kRing.mul_zero p, q3kRing.zero_mul q, q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9, q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul p q3kZero) (q3kRing.mul q3kZero q3kZero)) (q3kRing.mul q3kZero q) = q3kRing.zero
    rw [q27k_Z_eq, q3kRing.mul_zero p, q3kRing.mul_zero q3kRing.zero, q3kRing.add_zero q3kRing.zero, q3kRing.zero_mul q, q3kRing.add_zero q3kRing.zero]

/-- embed(1)=1。 -/
theorem q27k_embed_one : q27kEmbed q3kOne = q27kOne := rfl

/-- embed は単射。 -/
theorem q27k_embed_inj {p q : q3kCar} (h : q27kEmbed p = q27kEmbed q) : p = q :=
  congrArg (fun z : q27kCar => z.1) h
/-! ## q27k-6: 単数群 U₃ = O_M^× と閉形式 3 次ノルム逆元 -/

theorem q27k_kM_eq : q27kMul = q27kRing.mul := rfl

theorem q27k_sigma2_one : q27kSigma2 q27kOne = q27kOne := by
  apply q27k_ext
  · rfl
  · exact q3kRing.mul_zero q27kZeta3Sq
  · exact q3kRing.mul_zero q27kZeta3

theorem q27k_sigma2_mul (x y : q27kCar) :
    q27kSigma2 (q27kMul x y) = q27kMul (q27kSigma2 x) (q27kSigma2 y) := by
  rw [q27k_sigma2_comp (q27kMul x y), q27k_sigma_mul x y, q27k_sigma_mul (q27kSigma x) (q27kSigma y),
      ← q27k_sigma2_comp x, ← q27k_sigma2_comp y]

theorem q27k_six_reorder (x y a b c d : q27kCar) :
    q27kMul (q27kMul x y) (q27kMul (q27kMul a b) (q27kMul c d))
      = q27kMul (q27kMul x (q27kMul a c)) (q27kMul y (q27kMul b d)) := by
  rw [q27k_kM_eq, q27kRing.mul_mul_mul_comm a b c d,
      q27kRing.mul_mul_mul_comm x y (q27kRing.mul a c) (q27kRing.mul b d)]

theorem q27k_normBase_mul (x y : q27kCar) :
    q27kNormBase (q27kMul x y) = q3kMul (q27kNormBase x) (q27kNormBase y) := by
  apply q27k_embed_inj
  rw [← q27k_norm_eq (q27kMul x y), q27k_sigma_mul x y, q27k_sigma2_mul x y,
      q27k_six_reorder x y (q27kSigma x) (q27kSigma y) (q27kSigma2 x) (q27kSigma2 y),
      q27k_norm_eq x, q27k_norm_eq y, q27k_embed_mul (q27kNormBase x) (q27kNormBase y)]

theorem q27k_normBase_one : q27kNormBase q27kOne = q3kOne := by
  apply q27k_embed_inj
  rw [← q27k_norm_eq q27kOne, q27k_sigma_one, q27k_sigma2_one, q27k_one_mul, q27k_one_mul]
  exact q27k_embed_one.symm

def q27kUnitMem (x : q27kCar) : Prop := q3kUnitMem (q27kNormBase x)
def q27kInv (x : q27kCar) (hx : q27kUnitMem x) : q27kCar :=
  q27kMul (q27kMul (q27kSigma x) (q27kSigma2 x)) (q27kEmbed (q3kInv (q27kNormBase x) hx))

theorem q27k_inv_mul (x : q27kCar) (hx : q27kUnitMem x) :
    q27kMul x (q27kInv x hx) = q27kOne := by
  show q27kMul x (q27kMul (q27kMul (q27kSigma x) (q27kSigma2 x)) (q27kEmbed (q3kInv (q27kNormBase x) hx))) = q27kOne
  rw [← q27k_mul_assoc x (q27kMul (q27kSigma x) (q27kSigma2 x)) (q27kEmbed (q3kInv (q27kNormBase x) hx)),
      q27k_norm_eq x, q27k_embed_mul (q27kNormBase x) (q3kInv (q27kNormBase x) hx)]
  have hn : q3kMul (q27kNormBase x) (q3kInv (q27kNormBase x) hx) = q3kOne :=
    (q3kRing.mul_comm (q27kNormBase x) (q3kInv (q27kNormBase x) hx)).trans
      (q3k_inv_mul' (q27kNormBase x) hx)
  rw [hn]
  exact q27k_embed_one

theorem q27k_inv_mul' (x : q27kCar) (hx : q27kUnitMem x) :
    q27kMul (q27kInv x hx) x = q27kOne := by
  rw [q27k_mul_comm]; exact q27k_inv_mul x hx

theorem q27k_normBase_inv (x : q27kCar) (hx : q27kUnitMem x) :
    q27kNormBase (q27kInv x hx) = q3kInv (q27kNormBase x) hx := by
  have h1 : q3kMul (q27kNormBase x) (q27kNormBase (q27kInv x hx)) = q3kOne := by
    rw [← q27k_normBase_mul x (q27kInv x hx), q27k_inv_mul x hx, q27k_normBase_one]
  have key : q3kInv (q27kNormBase x) hx = q27kNormBase (q27kInv x hx) :=
    calc q3kInv (q27kNormBase x) hx
        = q3kMul (q3kInv (q27kNormBase x) hx) q3kOne := (q3kRing.mul_one _).symm
      _ = q3kMul (q3kInv (q27kNormBase x) hx)
            (q3kMul (q27kNormBase x) (q27kNormBase (q27kInv x hx))) := by rw [h1]
      _ = q3kMul (q3kMul (q3kInv (q27kNormBase x) hx) (q27kNormBase x))
            (q27kNormBase (q27kInv x hx)) := (q3kRing.mul_assoc _ _ _).symm
      _ = q3kMul q3kOne (q27kNormBase (q27kInv x hx)) := by rw [q3k_inv_mul' (q27kNormBase x) hx]
      _ = q27kNormBase (q27kInv x hx) := q3k_one_mul _
  exact key.symm

theorem q27k_unit_mul {x y : q27kCar} (hx : q27kUnitMem x) (hy : q27kUnitMem y) :
    q27kUnitMem (q27kMul x y) := by
  show q3kUnitMem (q27kNormBase (q27kMul x y))
  rw [q27k_normBase_mul x y]
  exact q3k_unit_mul hx hy

theorem q27k_unit_one : q27kUnitMem q27kOne := by
  show q3kUnitMem (q27kNormBase q27kOne)
  rw [q27k_normBase_one]; exact q3k_unit_one

theorem q27k_unit_inv (x : q27kCar) (hx : q27kUnitMem x) : q27kUnitMem (q27kInv x hx) := by
  show q3kUnitMem (q27kNormBase (q27kInv x hx))
  rw [q27k_normBase_inv x hx]
  exact q3k_unit_inv (q27kNormBase x) hx

def q27kU : Grp where
  carrier := { x : q27kCar // q27kUnitMem x }
  mul := fun x y => ⟨q27kMul x.val y.val, q27k_unit_mul x.property y.property⟩
  one := ⟨q27kOne, q27k_unit_one⟩
  inv := fun x => ⟨q27kInv x.val x.property, q27k_unit_inv x.val x.property⟩
  mul_assoc := fun x y z => Subtype.ext (q27k_mul_assoc x.val y.val z.val)
  one_mul := fun x => Subtype.ext (q27k_one_mul x.val)
  inv_mul := fun x => Subtype.ext (q27k_inv_mul' x.val x.property)
def q27kZeta27 : q27kCar := ((q3kZero, q3kOne, q3kZero) : q27kCar)

theorem q27k_zeta27_sq : q27kMul q27kZeta27 q27kZeta27 = ((q3kZero, q3kZero, q3kOne) : q27kCar) := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul q3kRing.one q3kRing.zero) (q3kRing.mul q3kRing.zero q3kRing.one))) = q3kRing.zero
    rw [q3kRing.mul_zero q3kRing.one, q3kRing.zero_mul q3kRing.one, q3kRing.add_zero q3kRing.zero,
        q3kRing.mul_zero q3kZeta9, q3kRing.mul_zero q3kRing.zero, q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.one) (q3kRing.mul q3kRing.one q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul q3kRing.zero q3kRing.zero)) = q3kRing.zero
    rw [q3kRing.zero_mul q3kRing.one, q3kRing.mul_zero q3kRing.one, q3kRing.add_zero q3kRing.zero,
        q3kRing.mul_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9, q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero) (q3kRing.mul q3kRing.one q3kRing.one))
        (q3kRing.mul q3kRing.zero q3kRing.zero) = q3kRing.one
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.one_mul q3kRing.one, q3kRing.zero_add q3kRing.one,
        q3kRing.add_zero q3kRing.one]

theorem q27k_zeta27_cube : q27kMul (q27kMul q27kZeta27 q27kZeta27) q27kZeta27 = q27kEmbed q3kZeta9 := by
  rw [q27k_zeta27_sq]
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero) (q3kRing.mul q3kRing.one q3kRing.one))) = q3kZeta9
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.one_mul q3kRing.one, q3kRing.zero_add q3kRing.one,
        q3kRing.mul_one q3kZeta9, q3kRing.zero_add q3kZeta9]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.one) (q3kRing.mul q3kRing.zero q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul q3kRing.one q3kRing.zero)) = q3kRing.zero
    rw [q3kRing.zero_mul q3kRing.one, q3kRing.mul_zero q3kRing.zero, q3kRing.add_zero q3kRing.zero,
        q3kRing.mul_zero q3kRing.one, q3kRing.mul_zero q3kZeta9, q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero) (q3kRing.mul q3kRing.zero q3kRing.one))
        (q3kRing.mul q3kRing.one q3kRing.zero) = q3kRing.zero
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.zero_mul q3kRing.one, q3kRing.add_zero q3kRing.zero,
        q3kRing.mul_zero q3kRing.one, q3kRing.add_zero q3kRing.zero]

/-! ## q27k-7: 実 ζ₂₇ = Z（位数ちょうど 27）・Z³=ζ₉・Z⁹=ζ₃≠1・Z²⁷=1 -/

/-- ζ₃ = q3kEmbed q3rqZeta ≠ 1（M₉ 内・q3k_zeta9_cube_ne_one 経由）。 -/
theorem q27k_zeta3_ne_one : q27kZeta3 ≠ q3kOne := by
  intro h
  apply q3k_zeta9_cube_ne_one
  rw [q3k_zeta9_cube]
  exact h

/-- Z⁹ = ((Z³)(Z³))(Z³)（9 乗の閉じた括り）。 -/
def q27kZ9 : q27kCar :=
  q27kMul (q27kMul (q27kMul (q27kMul q27kZeta27 q27kZeta27) q27kZeta27)
                   (q27kMul (q27kMul q27kZeta27 q27kZeta27) q27kZeta27))
          (q27kMul (q27kMul q27kZeta27 q27kZeta27) q27kZeta27)

/-- **Z⁹ = ζ₃**（= q27kEmbed q27kZeta3・= embed(ζ₉³)）。 -/
theorem q27k_zeta27_pow9 : q27kZ9 = q27kEmbed q27kZeta3 := by
  show q27kMul (q27kMul (q27kMul (q27kMul q27kZeta27 q27kZeta27) q27kZeta27)
                   (q27kMul (q27kMul q27kZeta27 q27kZeta27) q27kZeta27))
          (q27kMul (q27kMul q27kZeta27 q27kZeta27) q27kZeta27)
      = q27kEmbed q27kZeta3
  rw [q27k_zeta27_cube, q27k_embed_mul, q27k_embed_mul, q3k_zeta9_cube]
  rfl

/-- **Z²⁷ = 1**（= (Z⁹)³ = ζ₃³）。位数は 27 を割る。 -/
theorem q27k_zeta27_pow27 :
    q27kMul (q27kMul q27kZ9 q27kZ9) q27kZ9 = q27kOne := by
  rw [q27k_zeta27_pow9, q27k_embed_mul, q27k_embed_mul]
  show q27kEmbed (q3kRing.mul (q3kRing.mul q27kZeta3 q27kZeta3) q27kZeta3) = q27kOne
  rw [q27k_z3R]
  exact q27k_embed_one

/-- **Z ≠ 1**。 -/
theorem q27k_zeta27_ne_one : q27kZeta27 ≠ q27kOne := by
  intro h
  have h1 : q3kOne = q3kZero := congrArg (fun z : q27kCar => z.2.1) h
  have h2 : q3rqOne = q3rqZero := congrArg (fun p : q3kCar => p.1) h1
  have h3 : z3.one = z3.zero := congrArg (fun p : q3rqCar => p.1) h2
  exact q3rq_z3_one_ne_zero h3

/-- **Z⁹ = ζ₃ ≠ 1**（位数ちょうど 27 の核心——位数は 9 を割らない）。 -/
theorem q27k_zeta27_pow9_ne_one : q27kZ9 ≠ q27kOne := by
  rw [q27k_zeta27_pow9]
  intro h
  apply q27k_zeta3_ne_one
  apply q27k_embed_inj
  rw [q27k_embed_one]
  exact h

/-! ## q27k-8: capstone -/

/-- **q27k-8a: 実巡回 3 次 Kummer 拡大データ（level-27）** — 実 O_{M₂₇}=M₂₇（可換環）・
    実相対 Galois τ（位数 3）・実相対 3 次ノルム閉形式・単数群（閉形式逆元）・
    実 ζ₂₇（位数ちょうど 27）。 -/
structure Q3KummerNonicData where
  /-- 可換環 O_{M₂₇} = M₉[Z]/(Z³−ζ₉)。 -/
  ring : CRing
  /-- 相対 Galois τ（Z↦ζ₃Z）。 -/
  sigma : q27kCar → q27kCar
  /-- τ²。 -/
  sigma2 : q27kCar → q27kCar
  /-- 相対 3 次ノルム多項式 O_{M₂₇}→O_{M₉}。 -/
  norm : q27kCar → q3kCar
  /-- 単数群 U = O_{M₂₇}^×。 -/
  units : Grp
  /-- 実 ζ₂₇ = Z。 -/
  zeta27 : q27kCar
  /-- τ は環準同型。 -/
  sigma_mul : ∀ x y, sigma (q27kMul x y) = q27kMul (sigma x) (sigma y)
  /-- τ³ = id（位数 3）。 -/
  sigma3_id : ∀ x, sigma (sigma (sigma x)) = x
  /-- N(x)=x·τx·τ²x = embed(ノルム多項式)。 -/
  norm_eq : ∀ x, q27kMul x (q27kMul (sigma x) (sigma2 x)) = q27kEmbed (norm x)
  /-- 単数の閉形式逆元性 x·x⁻¹=1。 -/
  inv_closed : ∀ (x : q27kCar) (hx : q27kUnitMem x), q27kMul x (q27kInv x hx) = q27kOne
  /-- Z³ = ζ₉（埋め込み）。 -/
  zeta27_cube : q27kMul (q27kMul zeta27 zeta27) zeta27 = q27kEmbed q3kZeta9
  /-- ζ₂₇ ≠ 1。 -/
  zeta27_ne_one : zeta27 ≠ q27kOne
  /-- Z²⁷ = 1（位数は 27 を割る）。 -/
  zeta27_pow27 : q27kMul (q27kMul q27kZ9 q27kZ9) q27kZ9 = q27kOne
  /-- Z⁹ = ζ₃ ≠ 1（位数ちょうど 27・27 を割り 9 を割らない）。 -/
  zeta27_pow9_ne_one : q27kZ9 ≠ q27kOne

/-- **q27k-8b: 見出し実例** — 実 M₂₇ = M₉[Z]/(Z³−ζ₉)。 -/
def q27kData : Q3KummerNonicData where
  ring := q27kRing
  sigma := q27kSigma
  sigma2 := q27kSigma2
  norm := q27kNormBase
  units := q27kU
  zeta27 := q27kZeta27
  sigma_mul := q27k_sigma_mul
  sigma3_id := q27k_sigma3_id
  norm_eq := q27k_norm_eq
  inv_closed := q27k_inv_mul
  zeta27_cube := q27k_zeta27_cube
  zeta27_ne_one := q27k_zeta27_ne_one
  zeta27_pow27 := q27k_zeta27_pow27
  zeta27_pow9_ne_one := q27k_zeta27_pow9_ne_one

/-- **q27k-8c: 実巡回 3 次 Kummer 拡大（level-27）の存在**（実 O_{M₉} 上・単数群＋実 τ＋実 ζ₂₇）。 -/
theorem q27k_exists : Nonempty Q3KummerNonicData := ⟨q27kData⟩

end IUT
