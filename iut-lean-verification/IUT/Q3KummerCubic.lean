/-
  IUT/Q3KummerCubic.lean — F-wild R1（実巡回 3 次 Kummer 拡大 M = ℚ₃(ζ₉) =
    L₂[Y]/(Y³ − ζ₃)・O_{L₂}=q3rqRing 係数）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**（骨格・模型・代理でなく、
     R1 で建てた**実** O_{L₂} = ℤ₃[√−3] = q3rqRing の上に、実巡回 3 次 Kummer 拡大
     M = ℚ₃(ζ₉) = L₂[Y]/(Y³ − ζ₃) を O_{L₂}-基底 {1, Y, Y²}・Y³ = ζ₃ の
     ねじれ畳み込み乗法として本物に建てる。実相対 Galois σ（Y ↦ ζ₃Y・位数 3）・
     実 3 次ノルム閉形式 N(x)=x·σx·σ²x = 多項式 a³+ζ₃b³+ζ₃²c³−3ζ₃abc・
     単数群 U₃ = O_M^×（q3rqInv 消費・体エンジン不使用の閉形式逆元）・
     実 ζ₉ = Y（位数ちょうど 9）を実に構成する。toy 主語なし——主語は実
     q3rq-係数 3 次代数（m202fVol 型・Bool 軌道・surrogate 群を一切使わない）。）

  complete_pct 影響: **ℤ₃^× kill（F-wild）全体の FOUNDATION**。q3rq（R1）正直限定 4 が
  「1+3ℤ₃ の pro-3 主単数部分は n≥2＝F-wild まで残存」と named した wild 段の
  第 1 モジュール。単体では complete_pct 丸め値 ~0 前進（正直に「complete_pct 0 前進
  （骨格でなく本物基盤の先行建設）」）。実ターゲット（level-9 kill / pro-3 bulk）は
  後続 F-wild ラウンドで到達する。

  内容:
   * q3kCar / q3kAdd / q3kNeg / q3kMul / q3kRing
        — 実 M = O_{L₂}[Y]/(Y³−ζ₃)（三つ組 (a,b,c) ↔ a+bY+cY²・可換環）
   * q3kSigma / q3k_sigma_mul / q3k_sigma3_id
        — 実相対 Galois σ: Y↦ζ₃Y（ring hom・σ³=id・位数 3）
   * q3kNormBase / q3k_norm_eq
        — 実 3 次ノルム多項式 N(x)=x·σx·σ²x=embed(a³+ζ₃b³+ζ₃²c³−3ζ₃abc)
          （1+ζ₃+ζ₃²=0 が Y・Y² 成分を消す本物の恒等式）
   * q3kUnitMem / q3kInv / q3k_inv_mul
        — 単数判定・**閉形式 3 次ノルム逆元**（q3rqInv 消費・体エンジン不使用）
   * q3kU / q3k_unit_mul / q3k_normBase_mul
        — 単数群 U₃ = O_M^×・ノルムの乗法性
   * q3kZeta9 / q3k_zeta9_pow9 / q3k_zeta9_cube_ne_one
        — **実 ζ₉ = Y（位数ちょうど 9）**・Y⁹=1・Y³=ζ₃≠1
   * Q3KummerCubicData / q3kData / q3k_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・R1 継承の上に追記のみ）:
  1. **O_M と M^× のみ**（整数環＋単数群）。M を体としては建てない——total inverse は
     無く A2 恒久限定を継承。逆元は**単数（ノルムが ℤ₃^× の元）に限る**閉形式
     （q3rqInv 消費・体エンジン不使用）。
  2. **本モジュールは何も kill しない**（foundation のみ）。μ₉ 完全性・level-9
     テータ群・剛性は後続モジュール。ℤ₃^× 不定性を一切殺さない。
  3. **相対 Galois は位数 3 の σ のみ**（実 G_{ℚ₃} は無い）。
  4. **e=6 wild 分岐（π₉=ζ₉−1）は本ファイルでは未形式化**（付値・位相は範囲外・
     Y-adic 構造は代数的にのみ扱う）。
  5. **tmzLimit への比較橋は含めない**（二重計上防止・q3rq §5 継承）。
  6. 担体は**兄弟担体**（同型輸送は主張しない・q3rq §6 継承）。
  7. **σ を超える Galois 作用ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ**（q3rq §7 継承）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3RamifiedQuadratic

namespace IUT

/-! ## q3k-0: 座標変換ブリッジ（q3rqMul/q3rqAdd = q3rqRing.mul/add） -/

/-- 乗法ブリッジ（rw で係数環 q3rqRing の抽象公理へ橋渡し）。 -/
theorem q3k_M_eq : q3rqMul = q3rqRing.mul := rfl

/-- 加法ブリッジ。 -/
theorem q3k_A_eq : q3rqAdd = q3rqRing.add := rfl

/-! ## q3k-1: 台 M = O_{L₂}[Y]/(Y³−ζ₃)（三つ組 (a,b,c) ↔ a+bY+cY²） -/

/-- **q3k-1a: 台** — O_{L₂}³（第 1=定数部、第 2.1=Y 部、第 2.2=Y² 部）。 -/
def q3kCar : Type := q3rqCar × q3rqCar × q3rqCar

/-- 三つ組の外延性。 -/
theorem q3k_ext : ∀ {x y : q3kCar}, x.1 = y.1 → x.2.1 = y.2.1 → x.2.2 = y.2.2 → x = y
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl, rfl => rfl

/-- 加法（成分ごと q3rqAdd）。 -/
def q3kAdd (x y : q3kCar) : q3kCar :=
  ((q3rqAdd x.1 y.1, q3rqAdd x.2.1 y.2.1, q3rqAdd x.2.2 y.2.2) : q3kCar)

/-- 加法の第 0 成分展開。 -/
theorem q3kAdd_0 (x y : q3kCar) : (q3kAdd x y).1 = q3rqAdd x.1 y.1 := rfl

/-- 加法の第 1 成分展開。 -/
theorem q3kAdd_1 (x y : q3kCar) : (q3kAdd x y).2.1 = q3rqAdd x.2.1 y.2.1 := rfl

/-- 加法の第 2 成分展開。 -/
theorem q3kAdd_2 (x y : q3kCar) : (q3kAdd x y).2.2 = q3rqAdd x.2.2 y.2.2 := rfl

/-- 反元（成分ごと q3rqNeg）。 -/
def q3kNeg (x : q3kCar) : q3kCar :=
  ((q3rqNeg x.1, q3rqNeg x.2.1, q3rqNeg x.2.2) : q3kCar)

/-- 0 = (0,0,0)。 -/
def q3kZero : q3kCar := ((q3rqZero, q3rqZero, q3rqZero) : q3kCar)

/-- 1 = (1,0,0)。 -/
def q3kOne : q3kCar := ((q3rqOne, q3rqZero, q3rqZero) : q3kCar)

/-- **q3k-1b（★）: ねじれ畳み込み乗法** Y³ = ζ₃ = d。
    (a+bY+cY²)(a'+b'Y+c'Y²) を Y³→d・Y⁴→dY で還元:
    定数 = aa' + d(bc'+cb')・Y = ab'+ba'+d cc'・Y² = ac'+bb'+ca'。 -/
def q3kMul (x y : q3kCar) : q3kCar :=
  ((q3rqAdd (q3rqMul x.1 y.1)
      (q3rqMul q3rqZeta (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1))),
    q3rqAdd (q3rqAdd (q3rqMul x.1 y.2.1) (q3rqMul x.2.1 y.1))
      (q3rqMul q3rqZeta (q3rqMul x.2.2 y.2.2)),
    q3rqAdd (q3rqAdd (q3rqMul x.1 y.2.2) (q3rqMul x.2.1 y.2.1))
      (q3rqMul x.2.2 y.1)) : q3kCar)

/-- 乗法の第 0 成分展開（rw 補助）。 -/
theorem q3kMul_0 (x y : q3kCar) : (q3kMul x y).1
    = q3rqAdd (q3rqMul x.1 y.1)
      (q3rqMul q3rqZeta (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1))) := rfl

/-- 乗法の第 1（Y）成分展開。 -/
theorem q3kMul_1 (x y : q3kCar) : (q3kMul x y).2.1
    = q3rqAdd (q3rqAdd (q3rqMul x.1 y.2.1) (q3rqMul x.2.1 y.1))
      (q3rqMul q3rqZeta (q3rqMul x.2.2 y.2.2)) := rfl

/-- 乗法の第 2（Y²）成分展開。 -/
theorem q3kMul_2 (x y : q3kCar) : (q3kMul x y).2.2
    = q3rqAdd (q3rqAdd (q3rqMul x.1 y.2.2) (q3rqMul x.2.1 y.2.1))
      (q3rqMul x.2.2 y.1) := rfl

/-! ## q3k-2: 可換環公理（d = ζ₃ を抽象環元として扱う） -/

/-- 1·x = x。 -/
theorem q3k_one_mul (x : q3kCar) : q3kMul q3kOne x = x := by
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul q3rqRing.one x.1)
        (q3rqRing.mul q3rqZeta (q3rqRing.add
          (q3rqRing.mul q3rqRing.zero x.2.2) (q3rqRing.mul q3rqRing.zero x.2.1))) = x.1
    rw [q3rqRing.one_mul, q3rqRing.zero_mul, q3rqRing.zero_mul,
      q3rqRing.zero_add, q3rqRing.mul_zero, q3rqRing.add_zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul q3rqRing.one x.2.1)
        (q3rqRing.mul q3rqRing.zero x.1))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqRing.zero x.2.2)) = x.2.1
    rw [q3rqRing.one_mul, q3rqRing.zero_mul, q3rqRing.add_zero,
      q3rqRing.zero_mul, q3rqRing.mul_zero, q3rqRing.add_zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul q3rqRing.one x.2.2)
        (q3rqRing.mul q3rqRing.zero x.2.1)) (q3rqRing.mul q3rqRing.zero x.1) = x.2.2
    rw [q3rqRing.one_mul, q3rqRing.zero_mul, q3rqRing.add_zero,
      q3rqRing.zero_mul, q3rqRing.add_zero]

/-- **q3k-2b: 乗法可換**。 -/
theorem q3k_mul_comm (x y : q3kCar) : q3kMul x y = q3kMul y x := by
  apply q3k_ext
  · rw [q3kMul_0, q3kMul_0, q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.mul_comm x.1 y.1, q3rqRing.mul_comm x.2.1 y.2.2,
      q3rqRing.mul_comm x.2.2 y.2.1,
      q3rqRing.add_comm (q3rqRing.mul y.2.2 x.2.1) (q3rqRing.mul y.2.1 x.2.2)]
  · rw [q3kMul_1, q3kMul_1, q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.mul_comm x.1 y.2.1, q3rqRing.mul_comm x.2.1 y.1,
      q3rqRing.add_comm (q3rqRing.mul y.2.1 x.1) (q3rqRing.mul y.1 x.2.1),
      q3rqRing.mul_comm x.2.2 y.2.2]
  · rw [q3kMul_2, q3kMul_2, q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.mul_comm x.1 y.2.2, q3rqRing.mul_comm x.2.1 y.2.1,
      q3rqRing.mul_comm x.2.2 y.1,
      q3rqRing.add_assoc (q3rqRing.mul y.2.2 x.1) (q3rqRing.mul y.2.1 x.2.1)
        (q3rqRing.mul y.1 x.2.2),
      q3rqRing.add_comm (q3rqRing.mul y.2.2 x.1)
        (q3rqRing.add (q3rqRing.mul y.2.1 x.2.1) (q3rqRing.mul y.1 x.2.2)),
      q3rqRing.add_comm (q3rqRing.mul y.2.1 x.2.1) (q3rqRing.mul y.1 x.2.2)]

/-- **q3k-2c: 左分配**。 -/
theorem q3k_left_distrib (x y z : q3kCar) :
    q3kMul x (q3kAdd y z) = q3kAdd (q3kMul x y) (q3kMul x z) := by
  apply q3k_ext
  · rw [q3kMul_0, q3kAdd_0, q3kAdd_1, q3kAdd_2, q3kAdd_0, q3kMul_0, q3kMul_0,
      q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.left_distrib x.1 y.1 z.1,
      q3rqRing.left_distrib x.2.1 y.2.2 z.2.2,
      q3rqRing.left_distrib x.2.2 y.2.1 z.2.1,
      q3rqRing.add_add_add_comm (q3rqRing.mul x.2.1 y.2.2)
        (q3rqRing.mul x.2.1 z.2.2) (q3rqRing.mul x.2.2 y.2.1)
        (q3rqRing.mul x.2.2 z.2.1),
      q3rqRing.left_distrib q3rqZeta
        (q3rqRing.add (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1))
        (q3rqRing.add (q3rqRing.mul x.2.1 z.2.2) (q3rqRing.mul x.2.2 z.2.1)),
      q3rqRing.add_add_add_comm (q3rqRing.mul x.1 y.1) (q3rqRing.mul x.1 z.1)
        (q3rqRing.mul q3rqZeta
          (q3rqRing.add (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1)))
        (q3rqRing.mul q3rqZeta
          (q3rqRing.add (q3rqRing.mul x.2.1 z.2.2) (q3rqRing.mul x.2.2 z.2.1)))]
  · rw [q3kMul_1, q3kAdd_0, q3kAdd_1, q3kAdd_2, q3kAdd_1, q3kMul_1, q3kMul_1,
      q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.left_distrib x.1 y.2.1 z.2.1,
      q3rqRing.left_distrib x.2.1 y.1 z.1,
      q3rqRing.add_add_add_comm (q3rqRing.mul x.1 y.2.1) (q3rqRing.mul x.1 z.2.1)
        (q3rqRing.mul x.2.1 y.1) (q3rqRing.mul x.2.1 z.1),
      q3rqRing.left_distrib x.2.2 y.2.2 z.2.2,
      q3rqRing.left_distrib q3rqZeta (q3rqRing.mul x.2.2 y.2.2)
        (q3rqRing.mul x.2.2 z.2.2),
      q3rqRing.add_add_add_comm
        (q3rqRing.add (q3rqRing.mul x.1 y.2.1) (q3rqRing.mul x.2.1 y.1))
        (q3rqRing.add (q3rqRing.mul x.1 z.2.1) (q3rqRing.mul x.2.1 z.1))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.2 y.2.2))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.2 z.2.2))]
  · rw [q3kMul_2, q3kAdd_0, q3kAdd_1, q3kAdd_2, q3kAdd_2, q3kMul_2, q3kMul_2,
      q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.left_distrib x.1 y.2.2 z.2.2,
      q3rqRing.left_distrib x.2.1 y.2.1 z.2.1,
      q3rqRing.add_add_add_comm (q3rqRing.mul x.1 y.2.2) (q3rqRing.mul x.1 z.2.2)
        (q3rqRing.mul x.2.1 y.2.1) (q3rqRing.mul x.2.1 z.2.1),
      q3rqRing.left_distrib x.2.2 y.1 z.1,
      q3rqRing.add_add_add_comm
        (q3rqRing.add (q3rqRing.mul x.1 y.2.2) (q3rqRing.mul x.2.1 y.2.1))
        (q3rqRing.add (q3rqRing.mul x.1 z.2.2) (q3rqRing.mul x.2.1 z.2.1))
        (q3rqRing.mul x.2.2 y.1) (q3rqRing.mul x.2.2 z.1)]


/-! ## q3k-2d: 乗法結合律の順列補題（可換環 q3rqRing 内の 9 項和の再配置） -/

theorem q3k_add_swap (u v w : q3rqCar) :
    q3rqRing.add u (q3rqRing.add v w) = q3rqRing.add v (q3rqRing.add u w) := by
  rw [← q3rqRing.add_assoc u v w, q3rqRing.add_comm u v, q3rqRing.add_assoc v u w]

theorem q3k_perm_chain (p1 p2 p3 p4 p5 p6 p7 p8 p9 : q3rqCar) :
    q3rqRing.add p1 (q3rqRing.add p2 (q3rqRing.add p3 (q3rqRing.add p4
      (q3rqRing.add p5 (q3rqRing.add p6 (q3rqRing.add p7 (q3rqRing.add p8 p9)))))))
    = q3rqRing.add p1 (q3rqRing.add p4 (q3rqRing.add p7 (q3rqRing.add p5
      (q3rqRing.add p8 (q3rqRing.add p2 (q3rqRing.add p9 (q3rqRing.add p3 p6))))))) := by
  rw [q3k_add_swap p3 p4 (q3rqRing.add p5 (q3rqRing.add p6 (q3rqRing.add p7 (q3rqRing.add p8 p9)))),
      q3k_add_swap p2 p4 (q3rqRing.add p3 (q3rqRing.add p5 (q3rqRing.add p6 (q3rqRing.add p7 (q3rqRing.add p8 p9))))),
      q3k_add_swap p6 p7 (q3rqRing.add p8 p9),
      q3k_add_swap p5 p7 (q3rqRing.add p6 (q3rqRing.add p8 p9)),
      q3k_add_swap p3 p7 (q3rqRing.add p5 (q3rqRing.add p6 (q3rqRing.add p8 p9))),
      q3k_add_swap p2 p7 (q3rqRing.add p3 (q3rqRing.add p5 (q3rqRing.add p6 (q3rqRing.add p8 p9)))),
      q3k_add_swap p3 p5 (q3rqRing.add p6 (q3rqRing.add p8 p9)),
      q3k_add_swap p2 p5 (q3rqRing.add p3 (q3rqRing.add p6 (q3rqRing.add p8 p9))),
      q3k_add_swap p6 p8 p9,
      q3k_add_swap p3 p8 (q3rqRing.add p6 p9),
      q3k_add_swap p2 p8 (q3rqRing.add p3 (q3rqRing.add p6 p9)),
      q3rqRing.add_comm p6 p9,
      q3k_add_swap p3 p9 p6]

-- comp0 shapes
theorem q3k_perm0 (p1 p2 p3 p4 p5 p6 p7 p8 p9 : q3rqCar) :
    q3rqRing.add (q3rqRing.add p1 (q3rqRing.add p2 p3))
      (q3rqRing.add (q3rqRing.add (q3rqRing.add p4 p5) p6) (q3rqRing.add (q3rqRing.add p7 p8) p9))
    = q3rqRing.add (q3rqRing.add p1 (q3rqRing.add p4 p7))
      (q3rqRing.add (q3rqRing.add (q3rqRing.add p5 p8) p2) (q3rqRing.add (q3rqRing.add p9 p3) p6)) := by
  rw [q3rqRing.add_assoc p1 (q3rqRing.add p2 p3) (q3rqRing.add (q3rqRing.add (q3rqRing.add p4 p5) p6) (q3rqRing.add (q3rqRing.add p7 p8) p9)),
      q3rqRing.add_assoc p2 p3 (q3rqRing.add (q3rqRing.add (q3rqRing.add p4 p5) p6) (q3rqRing.add (q3rqRing.add p7 p8) p9)),
      q3rqRing.add_assoc (q3rqRing.add p4 p5) p6 (q3rqRing.add (q3rqRing.add p7 p8) p9),
      q3rqRing.add_assoc p4 p5 (q3rqRing.add p6 (q3rqRing.add (q3rqRing.add p7 p8) p9)),
      q3rqRing.add_assoc p7 p8 p9,
      q3rqRing.add_assoc p1 (q3rqRing.add p4 p7) (q3rqRing.add (q3rqRing.add (q3rqRing.add p5 p8) p2) (q3rqRing.add (q3rqRing.add p9 p3) p6)),
      q3rqRing.add_assoc p4 p7 (q3rqRing.add (q3rqRing.add (q3rqRing.add p5 p8) p2) (q3rqRing.add (q3rqRing.add p9 p3) p6)),
      q3rqRing.add_assoc (q3rqRing.add p5 p8) p2 (q3rqRing.add (q3rqRing.add p9 p3) p6),
      q3rqRing.add_assoc p5 p8 (q3rqRing.add p2 (q3rqRing.add (q3rqRing.add p9 p3) p6)),
      q3rqRing.add_assoc p9 p3 p6]
  exact q3k_perm_chain p1 p2 p3 p4 p5 p6 p7 p8 p9

-- comp1 shapes
theorem q3k_perm1 (p1 p2 p3 p4 p5 p6 p7 p8 p9 : q3rqCar) :
    q3rqRing.add (q3rqRing.add (q3rqRing.add p1 (q3rqRing.add p2 p3)) (q3rqRing.add (q3rqRing.add p4 p5) p6))
      (q3rqRing.add (q3rqRing.add p7 p8) p9)
    = q3rqRing.add (q3rqRing.add (q3rqRing.add (q3rqRing.add p1 p4) p7) (q3rqRing.add p5 (q3rqRing.add p8 p2)))
      (q3rqRing.add (q3rqRing.add p9 p3) p6) := by
  rw [q3rqRing.add_assoc (q3rqRing.add p1 (q3rqRing.add p2 p3)) (q3rqRing.add (q3rqRing.add p4 p5) p6) (q3rqRing.add (q3rqRing.add p7 p8) p9),
      q3rqRing.add_assoc p1 (q3rqRing.add p2 p3) (q3rqRing.add (q3rqRing.add (q3rqRing.add p4 p5) p6) (q3rqRing.add (q3rqRing.add p7 p8) p9)),
      q3rqRing.add_assoc p2 p3 (q3rqRing.add (q3rqRing.add (q3rqRing.add p4 p5) p6) (q3rqRing.add (q3rqRing.add p7 p8) p9)),
      q3rqRing.add_assoc (q3rqRing.add p4 p5) p6 (q3rqRing.add (q3rqRing.add p7 p8) p9),
      q3rqRing.add_assoc p4 p5 (q3rqRing.add p6 (q3rqRing.add (q3rqRing.add p7 p8) p9)),
      q3rqRing.add_assoc p7 p8 p9,
      q3rqRing.add_assoc (q3rqRing.add (q3rqRing.add p1 p4) p7) (q3rqRing.add p5 (q3rqRing.add p8 p2)) (q3rqRing.add (q3rqRing.add p9 p3) p6),
      q3rqRing.add_assoc (q3rqRing.add p1 p4) p7 (q3rqRing.add (q3rqRing.add p5 (q3rqRing.add p8 p2)) (q3rqRing.add (q3rqRing.add p9 p3) p6)),
      q3rqRing.add_assoc p1 p4 (q3rqRing.add p7 (q3rqRing.add (q3rqRing.add p5 (q3rqRing.add p8 p2)) (q3rqRing.add (q3rqRing.add p9 p3) p6))),
      q3rqRing.add_assoc p5 (q3rqRing.add p8 p2) (q3rqRing.add (q3rqRing.add p9 p3) p6),
      q3rqRing.add_assoc p8 p2 (q3rqRing.add (q3rqRing.add p9 p3) p6),
      q3rqRing.add_assoc p9 p3 p6]
  exact q3k_perm_chain p1 p2 p3 p4 p5 p6 p7 p8 p9

-- comp2 shapes
theorem q3k_perm2 (p1 p2 p3 p4 p5 p6 p7 p8 p9 : q3rqCar) :
    q3rqRing.add (q3rqRing.add (q3rqRing.add p1 (q3rqRing.add p2 p3)) (q3rqRing.add (q3rqRing.add p4 p5) p6))
      (q3rqRing.add (q3rqRing.add p7 p8) p9)
    = q3rqRing.add (q3rqRing.add (q3rqRing.add (q3rqRing.add p1 p4) p7) (q3rqRing.add (q3rqRing.add p5 p8) p2))
      (q3rqRing.add p9 (q3rqRing.add p3 p6)) := by
  rw [q3rqRing.add_assoc (q3rqRing.add p1 (q3rqRing.add p2 p3)) (q3rqRing.add (q3rqRing.add p4 p5) p6) (q3rqRing.add (q3rqRing.add p7 p8) p9),
      q3rqRing.add_assoc p1 (q3rqRing.add p2 p3) (q3rqRing.add (q3rqRing.add (q3rqRing.add p4 p5) p6) (q3rqRing.add (q3rqRing.add p7 p8) p9)),
      q3rqRing.add_assoc p2 p3 (q3rqRing.add (q3rqRing.add (q3rqRing.add p4 p5) p6) (q3rqRing.add (q3rqRing.add p7 p8) p9)),
      q3rqRing.add_assoc (q3rqRing.add p4 p5) p6 (q3rqRing.add (q3rqRing.add p7 p8) p9),
      q3rqRing.add_assoc p4 p5 (q3rqRing.add p6 (q3rqRing.add (q3rqRing.add p7 p8) p9)),
      q3rqRing.add_assoc p7 p8 p9,
      q3rqRing.add_assoc (q3rqRing.add (q3rqRing.add p1 p4) p7) (q3rqRing.add (q3rqRing.add p5 p8) p2) (q3rqRing.add p9 (q3rqRing.add p3 p6)),
      q3rqRing.add_assoc (q3rqRing.add p1 p4) p7 (q3rqRing.add (q3rqRing.add (q3rqRing.add p5 p8) p2) (q3rqRing.add p9 (q3rqRing.add p3 p6))),
      q3rqRing.add_assoc p1 p4 (q3rqRing.add p7 (q3rqRing.add (q3rqRing.add (q3rqRing.add p5 p8) p2) (q3rqRing.add p9 (q3rqRing.add p3 p6)))),
      q3rqRing.add_assoc (q3rqRing.add p5 p8) p2 (q3rqRing.add p9 (q3rqRing.add p3 p6)),
      q3rqRing.add_assoc p5 p8 (q3rqRing.add p2 (q3rqRing.add p9 (q3rqRing.add p3 p6)))]
  exact q3k_perm_chain p1 p2 p3 p4 p5 p6 p7 p8 p9

/-- **q3k-2e（★ 重い結合律）: 乗法結合律** — 3 成分を各 9 項の標準形へ展開し、
    係数環 q3rqRing の分配・結合・可換で再配置（perm0/1/2）。d=ζ₃ は抽象環元扱い。 -/
theorem q3k_mul_assoc (x y z : q3kCar) :
    q3kMul (q3kMul x y) z = q3kMul x (q3kMul y z) := by
  apply q3k_ext
  · -- 成分 0（定数部）
    rw [q3kMul_0, q3kMul_0, q3kMul_1, q3kMul_2,
        q3kMul_0, q3kMul_0, q3kMul_1, q3kMul_2,
        q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.right_distrib (q3rqRing.mul x.1 y.1)
          (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1))) z.1,
        q3rqRing.mul_assoc q3rqZeta (q3rqRing.add (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1)) z.1,
        q3rqRing.right_distrib (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1) z.1,
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.2) z.1) (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.1)]
    rw [q3rqRing.right_distrib (q3rqRing.add (q3rqRing.mul x.1 y.2.1) (q3rqRing.mul x.2.1 y.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.2 y.2.2)) z.2.2,
        q3rqRing.right_distrib (q3rqRing.mul x.1 y.2.1) (q3rqRing.mul x.2.1 y.1) z.2.2,
        q3rqRing.mul_assoc q3rqZeta (q3rqRing.mul x.2.2 y.2.2) z.2.2,
        q3rqRing.right_distrib (q3rqRing.add (q3rqRing.mul x.1 y.2.2) (q3rqRing.mul x.2.1 y.2.1)) (q3rqRing.mul x.2.2 y.1) z.2.1,
        q3rqRing.right_distrib (q3rqRing.mul x.1 y.2.2) (q3rqRing.mul x.2.1 y.2.1) z.2.1]
    rw [q3rqRing.left_distrib q3rqZeta
          (q3rqRing.add (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.1 y.2.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.1 y.1) z.2.2)) (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.2) z.2.2)))
          (q3rqRing.add (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.1 y.2.2) z.2.1) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.1)) (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.2.1)),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.1 y.2.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.1 y.1) z.2.2)) (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.2) z.2.2)),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 y.2.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.1 y.1) z.2.2),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.1 y.2.2) z.2.1) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.1)) (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.2.1),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 y.2.2) z.2.1) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.1)]
    -- ===== RHS normalization: Part A (M a v0) =====
    rw [q3rqRing.left_distrib x.1 (q3rqRing.mul y.1 z.1) (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1))),
        ← q3rqRing.mul_assoc x.1 y.1 z.1,
        ← q3rqRing.mul_assoc x.1 q3rqZeta (q3rqRing.add (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1)),
        q3rqRing.mul_comm x.1 q3rqZeta,
        q3rqRing.mul_assoc q3rqZeta x.1 (q3rqRing.add (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1)),
        q3rqRing.left_distrib x.1 (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1),
        ← q3rqRing.mul_assoc x.1 y.2.1 z.2.2,
        ← q3rqRing.mul_assoc x.1 y.2.2 z.2.1,
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 y.2.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.1 y.2.2) z.2.1)]
    -- ===== RHS normalization: Part B (M D (M b v2 + M c v1)) =====
    rw [q3rqRing.left_distrib x.2.1 (q3rqRing.add (q3rqRing.mul y.1 z.2.2) (q3rqRing.mul y.2.1 z.2.1)) (q3rqRing.mul y.2.2 z.1),
        q3rqRing.left_distrib x.2.1 (q3rqRing.mul y.1 z.2.2) (q3rqRing.mul y.2.1 z.2.1),
        ← q3rqRing.mul_assoc x.2.1 y.1 z.2.2,
        ← q3rqRing.mul_assoc x.2.1 y.2.1 z.2.1,
        ← q3rqRing.mul_assoc x.2.1 y.2.2 z.1,
        q3rqRing.left_distrib x.2.2 (q3rqRing.add (q3rqRing.mul y.1 z.2.1) (q3rqRing.mul y.2.1 z.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul y.2.2 z.2.2)),
        q3rqRing.left_distrib x.2.2 (q3rqRing.mul y.1 z.2.1) (q3rqRing.mul y.2.1 z.1),
        ← q3rqRing.mul_assoc x.2.2 y.1 z.2.1,
        ← q3rqRing.mul_assoc x.2.2 y.2.1 z.1,
        ← q3rqRing.mul_assoc x.2.2 q3rqZeta (q3rqRing.mul y.2.2 z.2.2),
        q3rqRing.mul_comm x.2.2 q3rqZeta,
        q3rqRing.mul_assoc q3rqZeta x.2.2 (q3rqRing.mul y.2.2 z.2.2),
        ← q3rqRing.mul_assoc x.2.2 y.2.2 z.2.2]
    rw [q3rqRing.left_distrib q3rqZeta
          (q3rqRing.add (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.2.1 y.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.1)) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.2) z.1))
          (q3rqRing.add (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.2.1) (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.2) z.2.2))),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.2.1 y.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.1)) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.2) z.1),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.1),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.2.1) (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.2) z.2.2)),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.2.1) (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.1)]
    exact q3k_perm0
      (q3rqRing.mul (q3rqRing.mul x.1 y.1) z.1)
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.2) z.1))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.1))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 y.2.1) z.2.2))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.1) z.2.2))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.2) z.2.2)))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 y.2.2) z.2.1))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.1))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.2.1))
  · -- 成分 1（Y 部）
    rw [q3kMul_1, q3kMul_0, q3kMul_1, q3kMul_2,
        q3kMul_1, q3kMul_1, q3kMul_0, q3kMul_2,
        q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.right_distrib (q3rqRing.mul x.1 y.1) (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1))) z.2.1,
        q3rqRing.mul_assoc q3rqZeta (q3rqRing.add (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1)) z.2.1,
        q3rqRing.right_distrib (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1) z.2.1,
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.2) z.2.1) (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.2.1),
        q3rqRing.right_distrib (q3rqRing.add (q3rqRing.mul x.1 y.2.1) (q3rqRing.mul x.2.1 y.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.2 y.2.2)) z.1,
        q3rqRing.right_distrib (q3rqRing.mul x.1 y.2.1) (q3rqRing.mul x.2.1 y.1) z.1,
        q3rqRing.mul_assoc q3rqZeta (q3rqRing.mul x.2.2 y.2.2) z.1,
        q3rqRing.right_distrib (q3rqRing.add (q3rqRing.mul x.1 y.2.2) (q3rqRing.mul x.2.1 y.2.1)) (q3rqRing.mul x.2.2 y.1) z.2.2,
        q3rqRing.right_distrib (q3rqRing.mul x.1 y.2.2) (q3rqRing.mul x.2.1 y.2.1) z.2.2,
        q3rqRing.left_distrib q3rqZeta (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.1 y.2.2) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.2)) (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.2.2),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 y.2.2) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.2)]
    rw [q3rqRing.left_distrib x.1 (q3rqRing.add (q3rqRing.mul y.1 z.2.1) (q3rqRing.mul y.2.1 z.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul y.2.2 z.2.2)),
        q3rqRing.left_distrib x.1 (q3rqRing.mul y.1 z.2.1) (q3rqRing.mul y.2.1 z.1),
        ← q3rqRing.mul_assoc x.1 y.1 z.2.1,
        ← q3rqRing.mul_assoc x.1 y.2.1 z.1,
        ← q3rqRing.mul_assoc x.1 q3rqZeta (q3rqRing.mul y.2.2 z.2.2),
        q3rqRing.mul_comm x.1 q3rqZeta,
        q3rqRing.mul_assoc q3rqZeta x.1 (q3rqRing.mul y.2.2 z.2.2),
        ← q3rqRing.mul_assoc x.1 y.2.2 z.2.2,
        q3rqRing.left_distrib x.2.1 (q3rqRing.mul y.1 z.1) (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1))),
        ← q3rqRing.mul_assoc x.2.1 y.1 z.1,
        ← q3rqRing.mul_assoc x.2.1 q3rqZeta (q3rqRing.add (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1)),
        q3rqRing.mul_comm x.2.1 q3rqZeta,
        q3rqRing.mul_assoc q3rqZeta x.2.1 (q3rqRing.add (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1)),
        q3rqRing.left_distrib x.2.1 (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1),
        ← q3rqRing.mul_assoc x.2.1 y.2.1 z.2.2,
        ← q3rqRing.mul_assoc x.2.1 y.2.2 z.2.1,
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.2) z.2.1),
        q3rqRing.left_distrib x.2.2 (q3rqRing.add (q3rqRing.mul y.1 z.2.2) (q3rqRing.mul y.2.1 z.2.1)) (q3rqRing.mul y.2.2 z.1),
        q3rqRing.left_distrib x.2.2 (q3rqRing.mul y.1 z.2.2) (q3rqRing.mul y.2.1 z.2.1),
        ← q3rqRing.mul_assoc x.2.2 y.1 z.2.2,
        ← q3rqRing.mul_assoc x.2.2 y.2.1 z.2.1,
        ← q3rqRing.mul_assoc x.2.2 y.2.2 z.1,
        q3rqRing.left_distrib q3rqZeta (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.2.1)) (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.2) z.1),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.2.1)]
    exact q3k_perm1
      (q3rqRing.mul (q3rqRing.mul x.1 y.1) z.2.1)
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.2) z.2.1))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.2.1))
      (q3rqRing.mul (q3rqRing.mul x.1 y.2.1) z.1)
      (q3rqRing.mul (q3rqRing.mul x.2.1 y.1) z.1)
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.2) z.1))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 y.2.2) z.2.2))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.2.2))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.2.2))
  · -- 成分 2（Y² 部）
    rw [q3kMul_2, q3kMul_0, q3kMul_1, q3kMul_2,
        q3kMul_2, q3kMul_2, q3kMul_1, q3kMul_0,
        q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.right_distrib (q3rqRing.mul x.1 y.1) (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1))) z.2.2,
        q3rqRing.mul_assoc q3rqZeta (q3rqRing.add (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1)) z.2.2,
        q3rqRing.right_distrib (q3rqRing.mul x.2.1 y.2.2) (q3rqRing.mul x.2.2 y.2.1) z.2.2,
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.2) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.2.2),
        q3rqRing.right_distrib (q3rqRing.add (q3rqRing.mul x.1 y.2.1) (q3rqRing.mul x.2.1 y.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.2 y.2.2)) z.2.1,
        q3rqRing.right_distrib (q3rqRing.mul x.1 y.2.1) (q3rqRing.mul x.2.1 y.1) z.2.1,
        q3rqRing.mul_assoc q3rqZeta (q3rqRing.mul x.2.2 y.2.2) z.2.1,
        q3rqRing.right_distrib (q3rqRing.add (q3rqRing.mul x.1 y.2.2) (q3rqRing.mul x.2.1 y.2.1)) (q3rqRing.mul x.2.2 y.1) z.1,
        q3rqRing.right_distrib (q3rqRing.mul x.1 y.2.2) (q3rqRing.mul x.2.1 y.2.1) z.1]
    rw [q3rqRing.left_distrib x.1 (q3rqRing.add (q3rqRing.mul y.1 z.2.2) (q3rqRing.mul y.2.1 z.2.1)) (q3rqRing.mul y.2.2 z.1),
        q3rqRing.left_distrib x.1 (q3rqRing.mul y.1 z.2.2) (q3rqRing.mul y.2.1 z.2.1),
        ← q3rqRing.mul_assoc x.1 y.1 z.2.2,
        ← q3rqRing.mul_assoc x.1 y.2.1 z.2.1,
        ← q3rqRing.mul_assoc x.1 y.2.2 z.1,
        q3rqRing.left_distrib x.2.1 (q3rqRing.add (q3rqRing.mul y.1 z.2.1) (q3rqRing.mul y.2.1 z.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul y.2.2 z.2.2)),
        q3rqRing.left_distrib x.2.1 (q3rqRing.mul y.1 z.2.1) (q3rqRing.mul y.2.1 z.1),
        ← q3rqRing.mul_assoc x.2.1 y.1 z.2.1,
        ← q3rqRing.mul_assoc x.2.1 y.2.1 z.1,
        ← q3rqRing.mul_assoc x.2.1 q3rqZeta (q3rqRing.mul y.2.2 z.2.2),
        q3rqRing.mul_comm x.2.1 q3rqZeta,
        q3rqRing.mul_assoc q3rqZeta x.2.1 (q3rqRing.mul y.2.2 z.2.2),
        ← q3rqRing.mul_assoc x.2.1 y.2.2 z.2.2,
        q3rqRing.left_distrib x.2.2 (q3rqRing.mul y.1 z.1) (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1))),
        ← q3rqRing.mul_assoc x.2.2 y.1 z.1,
        ← q3rqRing.mul_assoc x.2.2 q3rqZeta (q3rqRing.add (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1)),
        q3rqRing.mul_comm x.2.2 q3rqZeta,
        q3rqRing.mul_assoc q3rqZeta x.2.2 (q3rqRing.add (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1)),
        q3rqRing.left_distrib x.2.2 (q3rqRing.mul y.2.1 z.2.2) (q3rqRing.mul y.2.2 z.2.1),
        ← q3rqRing.mul_assoc x.2.2 y.2.1 z.2.2,
        ← q3rqRing.mul_assoc x.2.2 y.2.2 z.2.1,
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.2.2) (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.2) z.2.1)]
    exact q3k_perm2
      (q3rqRing.mul (q3rqRing.mul x.1 y.1) z.2.2)
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.2) z.2.2))
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.1) z.2.2))
      (q3rqRing.mul (q3rqRing.mul x.1 y.2.1) z.2.1)
      (q3rqRing.mul (q3rqRing.mul x.2.1 y.1) z.2.1)
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 y.2.2) z.2.1))
      (q3rqRing.mul (q3rqRing.mul x.1 y.2.2) z.1)
      (q3rqRing.mul (q3rqRing.mul x.2.1 y.2.1) z.1)
      (q3rqRing.mul (q3rqRing.mul x.2.2 y.1) z.1)

/-- **q3k-2f（★）: 可換環 O_M = M = L₂[Y]/(Y³−ζ₃)**。 -/
def q3kRing : CRing where
  carrier := q3kCar
  add := q3kAdd
  zero := q3kZero
  neg := q3kNeg
  mul := q3kMul
  one := q3kOne
  add_assoc := fun a b c => q3k_ext (q3rqRing.add_assoc a.1 b.1 c.1)
    (q3rqRing.add_assoc a.2.1 b.2.1 c.2.1) (q3rqRing.add_assoc a.2.2 b.2.2 c.2.2)
  zero_add := fun a => q3k_ext (q3rqRing.zero_add a.1) (q3rqRing.zero_add a.2.1)
    (q3rqRing.zero_add a.2.2)
  neg_add := fun a => q3k_ext (q3rqRing.neg_add a.1) (q3rqRing.neg_add a.2.1)
    (q3rqRing.neg_add a.2.2)
  add_comm := fun a b => q3k_ext (q3rqRing.add_comm a.1 b.1)
    (q3rqRing.add_comm a.2.1 b.2.1) (q3rqRing.add_comm a.2.2 b.2.2)
  mul_assoc := q3k_mul_assoc
  one_mul := q3k_one_mul
  mul_comm := q3k_mul_comm
  left_distrib := q3k_left_distrib

/-! ## q3k-3: ζ₃ の q3rqRing 形補題（相対 Galois σ 用） -/

/-- ζ₃·ζ₃² = 1（q3rqRing 形）。 -/
theorem q3k_z_zsqR1 : q3rqRing.mul q3rqZeta q3rqZetaSq = q3rqRing.one := q3rq_zeta_mul_zetaSq
/-- ζ₃²·ζ₃ = 1。 -/
theorem q3k_zsq_zR1 : q3rqRing.mul q3rqZetaSq q3rqZeta = q3rqRing.one :=
  (q3rqRing.mul_comm q3rqZetaSq q3rqZeta).trans q3rq_zeta_mul_zetaSq
/-- ζ₃²·ζ₃² = ζ₃。 -/
theorem q3k_zsq_zsqR : q3rqRing.mul q3rqZetaSq q3rqZetaSq = q3rqZeta := q3rq_zetaSq_mul_zetaSq
/-- ζ₃·ζ₃ = ζ₃²（定義）。 -/
theorem q3k_z_zR : q3rqRing.mul q3rqZeta q3rqZeta = q3rqZetaSq := rfl
/-- ζ₃³ = 1。 -/
theorem q3k_z3R : q3rqRing.mul (q3rqRing.mul q3rqZeta q3rqZeta) q3rqZeta = q3rqRing.one := q3rq_zeta_cube
/-- ζ₃² = (−h,−h)（z3 座標）。 -/
theorem q3k_zsq_eq : q3rqZetaSq = ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar) := q3rq_zeta_sq_eq

/-- **q3k-3a（★）: 1 + ζ₃ + ζ₃² = 0**（O_{L₂} 内の実円分関係。3 次ノルムの
    Y・Y² 成分消去の要）。 -/
theorem q3k_zeta_sum_zero :
    q3rqAdd q3rqOne (q3rqAdd q3rqZeta q3rqZetaSq) = q3rqZero := by
  rw [q3k_zsq_eq]
  apply q3rq_ext
  · show z3.add z3.one (z3.add (z3.neg q3rqHalf) (z3.neg q3rqHalf)) = z3.zero
    rw [← z3.neg_add_dist q3rqHalf q3rqHalf, q3rq_half_add_half, z3.add_neg]
  · show z3.add z3.zero (z3.add q3rqHalf (z3.neg q3rqHalf)) = z3.zero
    rw [z3.add_neg, z3.add_zero]

/-! ## q3k-4: 相対 Galois σ（Y ↦ ζ₃Y・位数 3） -/

/-- **q3k-4a: σ** = a + ζ₃bY + ζ₃²cY²（相対 Galois 自己同型）。 -/
def q3kSigma (x : q3kCar) : q3kCar :=
  ((x.1, q3rqMul q3rqZeta x.2.1, q3rqMul q3rqZetaSq x.2.2) : q3kCar)
theorem q3kSigma_0 (x : q3kCar) : (q3kSigma x).1 = x.1 := rfl
theorem q3kSigma_1 (x : q3kCar) : (q3kSigma x).2.1 = q3rqMul q3rqZeta x.2.1 := rfl
theorem q3kSigma_2 (x : q3kCar) : (q3kSigma x).2.2 = q3rqMul q3rqZetaSq x.2.2 := rfl

/-- σ(1) = 1。 -/
theorem q3k_sigma_one : q3kSigma q3kOne = q3kOne := by
  apply q3k_ext
  · rfl
  · exact q3rqRing.mul_zero q3rqZeta
  · exact q3rqRing.mul_zero q3rqZetaSq

/-- **q3k-4b（★）: σ は環準同型** σ(xy)=σx·σy（ζ₃·ζ₃²=1 等で ζ 冪を還元）。 -/
theorem q3k_sigma_mul (x y : q3kCar) :
    q3kSigma (q3kMul x y) = q3kMul (q3kSigma x) (q3kSigma y) := by
  apply q3k_ext
  · rw [q3kSigma_0, q3kMul_0, q3kMul_0, q3kSigma_0, q3kSigma_0,
        q3kSigma_1, q3kSigma_2, q3kSigma_2, q3kSigma_1, q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.mul_mul_mul_comm q3rqZeta x.2.1 q3rqZetaSq y.2.2,
        q3rqRing.mul_mul_mul_comm q3rqZetaSq x.2.2 q3rqZeta y.2.1,
        q3k_z_zsqR1, q3k_zsq_zR1,
        q3rqRing.one_mul (q3rqRing.mul x.2.1 y.2.2),
        q3rqRing.one_mul (q3rqRing.mul x.2.2 y.2.1)]
  · rw [q3kSigma_1, q3kMul_1, q3kMul_1, q3kSigma_0, q3kSigma_1, q3kSigma_1,
        q3kSigma_0, q3kSigma_2, q3kSigma_2, q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.mul_mul_mul_comm q3rqZetaSq x.2.2 q3rqZetaSq y.2.2, q3k_zsq_zsqR,
        q3rqRing.left_distrib q3rqZeta (q3rqRing.add (q3rqRing.mul x.1 y.2.1) (q3rqRing.mul x.2.1 y.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.2 y.2.2)),
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul x.1 y.2.1) (q3rqRing.mul x.2.1 y.1),
        ← q3rqRing.mul_assoc q3rqZeta x.1 y.2.1, q3rqRing.mul_comm q3rqZeta x.1, q3rqRing.mul_assoc x.1 q3rqZeta y.2.1,
        ← q3rqRing.mul_assoc q3rqZeta x.2.1 y.1]
  · rw [q3kSigma_2, q3kMul_2, q3kMul_2, q3kSigma_0, q3kSigma_2, q3kSigma_1,
        q3kSigma_1, q3kSigma_2, q3kSigma_0, q3k_M_eq, q3k_A_eq]
    rw [q3rqRing.mul_mul_mul_comm q3rqZeta x.2.1 q3rqZeta y.2.1, q3k_z_zR,
        q3rqRing.left_distrib q3rqZetaSq (q3rqRing.add (q3rqRing.mul x.1 y.2.2) (q3rqRing.mul x.2.1 y.2.1)) (q3rqRing.mul x.2.2 y.1),
        q3rqRing.left_distrib q3rqZetaSq (q3rqRing.mul x.1 y.2.2) (q3rqRing.mul x.2.1 y.2.1),
        ← q3rqRing.mul_assoc q3rqZetaSq x.1 y.2.2, q3rqRing.mul_comm q3rqZetaSq x.1, q3rqRing.mul_assoc x.1 q3rqZetaSq y.2.2,
        ← q3rqRing.mul_assoc q3rqZetaSq x.2.2 y.1]

/-- **q3k-4c: σ²** = a + ζ₃²bY + ζ₃cY²（還元済み・σ∘σ に一致）。 -/
def q3kSigma2 (x : q3kCar) : q3kCar :=
  ((x.1, q3rqMul q3rqZetaSq x.2.1, q3rqMul q3rqZeta x.2.2) : q3kCar)
theorem q3kSigma2_0 (x : q3kCar) : (q3kSigma2 x).1 = x.1 := rfl
theorem q3kSigma2_1 (x : q3kCar) : (q3kSigma2 x).2.1 = q3rqMul q3rqZetaSq x.2.1 := rfl
theorem q3kSigma2_2 (x : q3kCar) : (q3kSigma2 x).2.2 = q3rqMul q3rqZeta x.2.2 := rfl

/-- σ² = σ∘σ。 -/
theorem q3k_sigma2_comp (x : q3kCar) : q3kSigma2 x = q3kSigma (q3kSigma x) := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZetaSq x.2.1 = q3rqMul q3rqZeta (q3rqMul q3rqZeta x.2.1)
    rw [q3k_M_eq, ← q3rqRing.mul_assoc q3rqZeta q3rqZeta x.2.1, q3k_z_zR]
  · show q3rqMul q3rqZeta x.2.2 = q3rqMul q3rqZetaSq (q3rqMul q3rqZetaSq x.2.2)
    rw [q3k_M_eq, ← q3rqRing.mul_assoc q3rqZetaSq q3rqZetaSq x.2.2, q3k_zsq_zsqR]

/-- **q3k-4d（★）: σ³ = id**（位数ちょうど 3・ζ₃³=1）。 -/
theorem q3k_sigma3_id (x : q3kCar) :
    q3kSigma (q3kSigma (q3kSigma x)) = x := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta (q3rqMul q3rqZeta (q3rqMul q3rqZeta x.2.1)) = x.2.1
    rw [q3k_M_eq, ← q3rqRing.mul_assoc q3rqZeta q3rqZeta (q3rqRing.mul q3rqZeta x.2.1),
        ← q3rqRing.mul_assoc (q3rqRing.mul q3rqZeta q3rqZeta) q3rqZeta x.2.1, q3k_z3R,
        q3rqRing.one_mul x.2.1]
  · show q3rqMul q3rqZetaSq (q3rqMul q3rqZetaSq (q3rqMul q3rqZetaSq x.2.2)) = x.2.2
    rw [q3k_M_eq, ← q3rqRing.mul_assoc q3rqZetaSq q3rqZetaSq (q3rqRing.mul q3rqZetaSq x.2.2),
        q3k_zsq_zsqR, ← q3rqRing.mul_assoc q3rqZeta q3rqZetaSq x.2.2, q3k_z_zsqR1,
        q3rqRing.one_mul x.2.2]


/-! ## q3k-5: 3 次ノルム N(x)=x·σx·σ²x（多項式恒等式・1+ζ₃+ζ₃²=0 で Y,Y² 消去） -/

/-- 反元ブリッジ。 -/
theorem q3k_N_eq : q3rqNeg = q3rqRing.neg := rfl

/-- t·(1+ζ₃+ζ₃²) = 0（円分関係の乗法版）。 -/
theorem q3k_sum3 (t : q3rqCar) :
    q3rqRing.add (q3rqRing.add t (q3rqRing.mul q3rqZeta t)) (q3rqRing.mul q3rqZetaSq t)
      = q3rqRing.zero := by
  have h : q3rqRing.mul t (q3rqRing.add q3rqRing.one (q3rqRing.add q3rqZeta q3rqZetaSq))
      = q3rqRing.zero := by
    rw [show q3rqRing.add q3rqRing.one (q3rqRing.add q3rqZeta q3rqZetaSq) = q3rqZero
          from q3k_zeta_sum_zero]
    exact q3rqRing.mul_zero t
  rw [q3rqRing.left_distrib t q3rqRing.one (q3rqRing.add q3rqZeta q3rqZetaSq),
      q3rqRing.left_distrib t q3rqZeta q3rqZetaSq, q3rqRing.mul_one t,
      q3rqRing.mul_comm t q3rqZeta, q3rqRing.mul_comm t q3rqZetaSq,
      ← q3rqRing.add_assoc t (q3rqRing.mul q3rqZeta t) (q3rqRing.mul q3rqZetaSq t)] at h
  exact h
/-- t + ζ₃²t = −ζ₃t。 -/
theorem q3k_bc (t : q3rqCar) :
    q3rqRing.add t (q3rqRing.mul q3rqZetaSq t) = q3rqRing.neg (q3rqRing.mul q3rqZeta t) := by
  have h := q3k_sum3 t
  rw [q3rqRing.add_assoc t (q3rqRing.mul q3rqZeta t) (q3rqRing.mul q3rqZetaSq t),
      q3rqRing.add_comm (q3rqRing.mul q3rqZeta t) (q3rqRing.mul q3rqZetaSq t),
      ← q3rqRing.add_assoc t (q3rqRing.mul q3rqZetaSq t) (q3rqRing.mul q3rqZeta t)] at h
  have h3 := congrArg q3rqRing.neg (q3rqRing.neg_eq_of_add_eq_zero h)
  rw [q3rqRing.neg_neg] at h3
  exact h3
/-- ζ₃²t + ζ₃t = −t。 -/
theorem q3k_bc2 (t : q3rqCar) :
    q3rqRing.add (q3rqRing.mul q3rqZetaSq t) (q3rqRing.mul q3rqZeta t) = q3rqRing.neg t := by
  have h := q3k_sum3 t
  rw [q3rqRing.add_assoc t (q3rqRing.mul q3rqZeta t) (q3rqRing.mul q3rqZetaSq t),
      q3rqRing.add_comm t (q3rqRing.add (q3rqRing.mul q3rqZeta t) (q3rqRing.mul q3rqZetaSq t)),
      q3rqRing.add_comm (q3rqRing.mul q3rqZeta t) (q3rqRing.mul q3rqZetaSq t)] at h
  have h3 := congrArg q3rqRing.neg (q3rqRing.neg_eq_of_add_eq_zero h)
  rw [q3rqRing.neg_neg] at h3
  exact h3
/-- ζ₃t + ζ₃²t = −t。 -/
theorem q3k_bc3 (t : q3rqCar) :
    q3rqRing.add (q3rqRing.mul q3rqZeta t) (q3rqRing.mul q3rqZetaSq t) = q3rqRing.neg t := by
  rw [q3rqRing.add_comm (q3rqRing.mul q3rqZeta t) (q3rqRing.mul q3rqZetaSq t)]
  exact q3k_bc2 t

/-- **q3k-5a: w = σx·σ²x**（共役積の閉形式・1+ζ₃+ζ₃²=0 使用）。 -/
def q3kWt (x : q3kCar) : q3kCar :=
  ((q3rqAdd (q3rqMul x.1 x.1) (q3rqNeg (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2))),
    q3rqAdd (q3rqNeg (q3rqMul x.1 x.2.1)) (q3rqMul q3rqZeta (q3rqMul x.2.2 x.2.2)),
    q3rqAdd (q3rqMul x.2.1 x.2.1) (q3rqNeg (q3rqMul x.1 x.2.2))) : q3kCar)
theorem q3kWt_0 (x : q3kCar) : (q3kWt x).1 = q3rqAdd (q3rqMul x.1 x.1) (q3rqNeg (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2))) := rfl
theorem q3kWt_1 (x : q3kCar) : (q3kWt x).2.1 = q3rqAdd (q3rqNeg (q3rqMul x.1 x.2.1)) (q3rqMul q3rqZeta (q3rqMul x.2.2 x.2.2)) := rfl
theorem q3kWt_2 (x : q3kCar) : (q3kWt x).2.2 = q3rqAdd (q3rqMul x.2.1 x.2.1) (q3rqNeg (q3rqMul x.1 x.2.2)) := rfl
/-- **q3k-5b（★）: σx·σ²x = w**（ζ 冪還元＋円分関係）。 -/
theorem q3k_w_eq (x : q3kCar) : q3kMul (q3kSigma x) (q3kSigma2 x) = q3kWt x := by
  apply q3k_ext
  · rw [q3kMul_0, q3kSigma_0, q3kSigma2_0, q3kSigma_1, q3kSigma2_2, q3kSigma_2, q3kSigma2_1,
        q3kWt_0, q3k_M_eq, q3k_A_eq, q3k_N_eq,
        q3rqRing.mul_mul_mul_comm q3rqZeta x.2.1 q3rqZeta x.2.2, q3k_z_zR,
        q3rqRing.mul_mul_mul_comm q3rqZetaSq x.2.2 q3rqZetaSq x.2.1, q3k_zsq_zsqR,
        q3rqRing.mul_comm x.2.2 x.2.1,
        q3rqRing.left_distrib q3rqZeta (q3rqRing.mul q3rqZetaSq (q3rqRing.mul x.2.1 x.2.2)) (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.1 x.2.2)),
        ← q3rqRing.mul_assoc q3rqZeta q3rqZetaSq (q3rqRing.mul x.2.1 x.2.2), q3k_z_zsqR1, q3rqRing.one_mul (q3rqRing.mul x.2.1 x.2.2),
        ← q3rqRing.mul_assoc q3rqZeta q3rqZeta (q3rqRing.mul x.2.1 x.2.2), q3k_z_zR,
        q3k_bc (q3rqRing.mul x.2.1 x.2.2)]
  · rw [q3kMul_1, q3kSigma_0, q3kSigma2_1, q3kSigma_1, q3kSigma2_0, q3kSigma_2, q3kSigma2_2,
        q3kWt_1, q3k_M_eq, q3k_A_eq, q3k_N_eq,
        q3rqRing.mul_mul_mul_comm q3rqZetaSq x.2.2 q3rqZeta x.2.2, q3k_zsq_zR1, q3rqRing.one_mul (q3rqRing.mul x.2.2 x.2.2),
        ← q3rqRing.mul_assoc x.1 q3rqZetaSq x.2.1, q3rqRing.mul_comm x.1 q3rqZetaSq, q3rqRing.mul_assoc q3rqZetaSq x.1 x.2.1,
        q3rqRing.mul_assoc q3rqZeta x.2.1 x.1, q3rqRing.mul_comm x.2.1 x.1,
        q3k_bc2 (q3rqRing.mul x.1 x.2.1)]
  · rw [q3kMul_2, q3kSigma_0, q3kSigma2_2, q3kSigma_1, q3kSigma2_1, q3kSigma_2, q3kSigma2_0,
        q3kWt_2, q3k_M_eq, q3k_A_eq, q3k_N_eq,
        q3rqRing.mul_mul_mul_comm q3rqZeta x.2.1 q3rqZetaSq x.2.1, q3k_z_zsqR1, q3rqRing.one_mul (q3rqRing.mul x.2.1 x.2.1),
        ← q3rqRing.mul_assoc x.1 q3rqZeta x.2.2, q3rqRing.mul_comm x.1 q3rqZeta, q3rqRing.mul_assoc q3rqZeta x.1 x.2.2,
        q3rqRing.mul_assoc q3rqZetaSq x.2.2 x.1, q3rqRing.mul_comm x.2.2 x.1,
        q3rqRing.add_assoc (q3rqRing.mul q3rqZeta (q3rqRing.mul x.1 x.2.2)) (q3rqRing.mul x.2.1 x.2.1) (q3rqRing.mul q3rqZetaSq (q3rqRing.mul x.1 x.2.2)),
        q3rqRing.add_comm (q3rqRing.mul x.2.1 x.2.1) (q3rqRing.mul q3rqZetaSq (q3rqRing.mul x.1 x.2.2)),
        ← q3rqRing.add_assoc (q3rqRing.mul q3rqZeta (q3rqRing.mul x.1 x.2.2)) (q3rqRing.mul q3rqZetaSq (q3rqRing.mul x.1 x.2.2)) (q3rqRing.mul x.2.1 x.2.1),
        q3k_bc3 (q3rqRing.mul x.1 x.2.2),
        q3rqRing.add_comm (q3rqRing.neg (q3rqRing.mul x.1 x.2.2)) (q3rqRing.mul x.2.1 x.2.1)]

/-- 実 3 = 1+1+1 ∈ O_{L₂}。 -/
def q3kThree : q3rqCar := q3rqAdd q3rqOne (q3rqAdd q3rqOne q3rqOne)
/-- −(3·K) = −K + (−K + −K)。 -/
theorem q3k_three_K (K : q3rqCar) :
    q3rqRing.neg (q3rqRing.mul q3kThree K)
      = q3rqRing.add (q3rqRing.neg K) (q3rqRing.add (q3rqRing.neg K) (q3rqRing.neg K)) := by
  show q3rqRing.neg (q3rqRing.mul (q3rqRing.add q3rqRing.one (q3rqRing.add q3rqRing.one q3rqRing.one)) K) = _
  rw [q3rqRing.right_distrib q3rqRing.one (q3rqRing.add q3rqRing.one q3rqRing.one) K,
      q3rqRing.right_distrib q3rqRing.one q3rqRing.one K, q3rqRing.one_mul K,
      q3rqRing.neg_add_dist K (q3rqRing.add K K), q3rqRing.neg_add_dist K K]
/-- 3 次ノルムの −3K 収集（多項式簿記）。 -/
theorem q3k_norm_collect (P Q R K : q3rqCar) :
    q3rqRing.add (q3rqRing.add P (q3rqRing.neg K))
      (q3rqRing.add (q3rqRing.add Q (q3rqRing.neg K)) (q3rqRing.add (q3rqRing.neg K) R))
    = q3rqRing.add (q3rqRing.add (q3rqRing.add P Q) R) (q3rqRing.neg (q3rqRing.mul q3kThree K)) := by
  rw [q3k_three_K K,
      q3rqRing.add_assoc P (q3rqRing.neg K) (q3rqRing.add (q3rqRing.add Q (q3rqRing.neg K)) (q3rqRing.add (q3rqRing.neg K) R)),
      q3rqRing.add_assoc Q (q3rqRing.neg K) (q3rqRing.add (q3rqRing.neg K) R),
      q3rqRing.add_assoc (q3rqRing.add P Q) R (q3rqRing.add (q3rqRing.neg K) (q3rqRing.add (q3rqRing.neg K) (q3rqRing.neg K))),
      q3rqRing.add_assoc P Q (q3rqRing.add R (q3rqRing.add (q3rqRing.neg K) (q3rqRing.add (q3rqRing.neg K) (q3rqRing.neg K)))),
      q3k_add_swap (q3rqRing.neg K) Q (q3rqRing.add (q3rqRing.neg K) (q3rqRing.add (q3rqRing.neg K) R)),
      q3rqRing.add_comm (q3rqRing.neg K) R,
      q3k_add_swap (q3rqRing.neg K) R (q3rqRing.neg K),
      q3k_add_swap (q3rqRing.neg K) R (q3rqRing.add (q3rqRing.neg K) (q3rqRing.neg K))]

/-- **q3k-5c: 3 次ノルム多項式** N=a³+ζ₃b³+ζ₃²c³−3ζ₃abc（O_{L₂} 値）。 -/
def q3kNormBase (x : q3kCar) : q3rqCar :=
  q3rqAdd (q3rqAdd (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.1)
      (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)))
      (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)))
    (q3rqNeg (q3rqMul q3kThree (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.1 x.2.1) x.2.2))))

/-- 基底環の埋め込み O_{L₂} ↪ M, n ↦ (n,0,0)。 -/
def q3kEmbed (n : q3rqCar) : q3kCar := ((n, q3rqZero, q3rqZero) : q3kCar)
theorem q3kEmbed_0 (n : q3rqCar) : (q3kEmbed n).1 = n := rfl
theorem q3kEmbed_1 (n : q3rqCar) : (q3kEmbed n).2.1 = q3rqZero := rfl
theorem q3kEmbed_2 (n : q3rqCar) : (q3kEmbed n).2.2 = q3rqZero := rfl

/-- 6 項相殺（Y 成分消去）。 -/
theorem q3k_cancel6a (A1 A2 A3 : q3rqCar) :
    q3rqRing.add (q3rqRing.add (q3rqRing.add (q3rqRing.neg A1) A2) (q3rqRing.add A1 (q3rqRing.neg A3)))
      (q3rqRing.add A3 (q3rqRing.neg A2)) = q3rqRing.zero := by
  rw [q3rqRing.add_assoc (q3rqRing.add (q3rqRing.neg A1) A2) (q3rqRing.add A1 (q3rqRing.neg A3)) (q3rqRing.add A3 (q3rqRing.neg A2)),
      q3rqRing.add_assoc A1 (q3rqRing.neg A3) (q3rqRing.add A3 (q3rqRing.neg A2)),
      ← q3rqRing.add_assoc (q3rqRing.neg A3) A3 (q3rqRing.neg A2), q3rqRing.neg_add A3, q3rqRing.zero_add (q3rqRing.neg A2),
      q3rqRing.add_assoc (q3rqRing.neg A1) A2 (q3rqRing.add A1 (q3rqRing.neg A2)),
      ← q3rqRing.add_assoc A2 A1 (q3rqRing.neg A2), q3rqRing.add_comm A2 A1, q3rqRing.add_assoc A1 A2 (q3rqRing.neg A2),
      q3rqRing.add_neg A2, q3rqRing.add_zero A1, q3rqRing.neg_add A1]
/-- 6 項相殺（Y² 成分消去）。 -/
theorem q3k_cancel6b (B1 B2 B3 : q3rqCar) :
    q3rqRing.add (q3rqRing.add (q3rqRing.add B1 (q3rqRing.neg B2)) (q3rqRing.add (q3rqRing.neg B1) B3))
      (q3rqRing.add B2 (q3rqRing.neg B3)) = q3rqRing.zero := by
  rw [q3rqRing.add_assoc (q3rqRing.add B1 (q3rqRing.neg B2)) (q3rqRing.add (q3rqRing.neg B1) B3) (q3rqRing.add B2 (q3rqRing.neg B3)),
      q3rqRing.add_assoc (q3rqRing.neg B1) B3 (q3rqRing.add B2 (q3rqRing.neg B3)),
      ← q3rqRing.add_assoc B3 B2 (q3rqRing.neg B3), q3rqRing.add_comm B3 B2, q3rqRing.add_assoc B2 B3 (q3rqRing.neg B3),
      q3rqRing.add_neg B3, q3rqRing.add_zero B2,
      q3rqRing.add_assoc B1 (q3rqRing.neg B2) (q3rqRing.add (q3rqRing.neg B1) B2),
      ← q3rqRing.add_assoc (q3rqRing.neg B2) (q3rqRing.neg B1) B2, q3rqRing.add_comm (q3rqRing.neg B2) (q3rqRing.neg B1),
      q3rqRing.add_assoc (q3rqRing.neg B1) (q3rqRing.neg B2) B2, q3rqRing.neg_add B2, q3rqRing.add_zero (q3rqRing.neg B1),
      q3rqRing.add_neg B1]

/-- N の定数成分 = ノルム多項式。 -/
theorem q3k_xwt_0 (x : q3kCar) : (q3kMul x (q3kWt x)).1 = q3kNormBase x := by
  rw [q3kMul_0, q3kWt_0, q3kWt_1, q3kWt_2, q3k_M_eq, q3k_A_eq, q3k_N_eq]
  show _ = q3rqRing.add (q3rqRing.add (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.1 x.1) x.1)
      (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 x.2.1) x.2.1)))
      (q3rqRing.mul q3rqZetaSq (q3rqRing.mul (q3rqRing.mul x.2.2 x.2.2) x.2.2)))
    (q3rqRing.neg (q3rqRing.mul q3kThree (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 x.2.1) x.2.2))))
  rw [q3rqRing.left_distrib x.1 (q3rqRing.mul x.1 x.1) (q3rqRing.neg (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.1 x.2.2))),
      ← q3rqRing.mul_assoc x.1 x.1 x.1,
      q3rqRing.mul_neg x.1 (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.1 x.2.2)),
      ← q3rqRing.mul_assoc x.1 q3rqZeta (q3rqRing.mul x.2.1 x.2.2),
      q3rqRing.mul_comm x.1 q3rqZeta,
      q3rqRing.mul_assoc q3rqZeta x.1 (q3rqRing.mul x.2.1 x.2.2),
      ← q3rqRing.mul_assoc x.1 x.2.1 x.2.2,
      q3rqRing.left_distrib x.2.1 (q3rqRing.mul x.2.1 x.2.1) (q3rqRing.neg (q3rqRing.mul x.1 x.2.2)),
      ← q3rqRing.mul_assoc x.2.1 x.2.1 x.2.1,
      q3rqRing.mul_neg x.2.1 (q3rqRing.mul x.1 x.2.2),
      ← q3rqRing.mul_assoc x.2.1 x.1 x.2.2,
      q3rqRing.mul_comm x.2.1 x.1,
      q3rqRing.left_distrib x.2.2 (q3rqRing.neg (q3rqRing.mul x.1 x.2.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.2 x.2.2)),
      q3rqRing.mul_neg x.2.2 (q3rqRing.mul x.1 x.2.1),
      q3rqRing.mul_comm x.2.2 (q3rqRing.mul x.1 x.2.1),
      ← q3rqRing.mul_assoc x.2.2 q3rqZeta (q3rqRing.mul x.2.2 x.2.2),
      q3rqRing.mul_comm x.2.2 q3rqZeta,
      q3rqRing.mul_assoc q3rqZeta x.2.2 (q3rqRing.mul x.2.2 x.2.2),
      ← q3rqRing.mul_assoc x.2.2 x.2.2 x.2.2,
      q3rqRing.left_distrib q3rqZeta (q3rqRing.add (q3rqRing.mul (q3rqRing.mul x.2.1 x.2.1) x.2.1) (q3rqRing.neg (q3rqRing.mul (q3rqRing.mul x.1 x.2.1) x.2.2))) (q3rqRing.add (q3rqRing.neg (q3rqRing.mul (q3rqRing.mul x.1 x.2.1) x.2.2)) (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 x.2.2) x.2.2))),
      q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 x.2.1) x.2.1) (q3rqRing.neg (q3rqRing.mul (q3rqRing.mul x.1 x.2.1) x.2.2)),
      q3rqRing.mul_neg q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 x.2.1) x.2.2),
      q3rqRing.left_distrib q3rqZeta (q3rqRing.neg (q3rqRing.mul (q3rqRing.mul x.1 x.2.1) x.2.2)) (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 x.2.2) x.2.2)),
      q3rqRing.mul_neg q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 x.2.1) x.2.2),
      ← q3rqRing.mul_assoc q3rqZeta q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.2 x.2.2) x.2.2),
      q3k_z_zR]
  rw [q3k_norm_collect (q3rqRing.mul (q3rqRing.mul x.1 x.1) x.1)
        (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 x.2.1) x.2.1))
        (q3rqRing.mul q3rqZetaSq (q3rqRing.mul (q3rqRing.mul x.2.2 x.2.2) x.2.2))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 x.2.1) x.2.2))]
/-- N の Y 成分 = 0（相殺）。 -/
theorem q3k_xwt_1 (x : q3kCar) : (q3kMul x (q3kWt x)).2.1 = q3rqZero := by
  rw [q3kMul_1, q3kWt_0, q3kWt_1, q3kWt_2, q3k_M_eq, q3k_A_eq, q3k_N_eq]
  rw [q3rqRing.left_distrib x.1 (q3rqRing.neg (q3rqRing.mul x.1 x.2.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.2 x.2.2)),
      q3rqRing.mul_neg x.1 (q3rqRing.mul x.1 x.2.1),
      ← q3rqRing.mul_assoc x.1 x.1 x.2.1,
      ← q3rqRing.mul_assoc x.1 q3rqZeta (q3rqRing.mul x.2.2 x.2.2),
      q3rqRing.mul_comm x.1 q3rqZeta,
      q3rqRing.mul_assoc q3rqZeta x.1 (q3rqRing.mul x.2.2 x.2.2),
      ← q3rqRing.mul_assoc x.1 x.2.2 x.2.2,
      q3rqRing.left_distrib x.2.1 (q3rqRing.mul x.1 x.1) (q3rqRing.neg (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.1 x.2.2))),
      q3rqRing.mul_comm x.2.1 (q3rqRing.mul x.1 x.1),
      q3rqRing.mul_neg x.2.1 (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.1 x.2.2)),
      ← q3rqRing.mul_assoc x.2.1 q3rqZeta (q3rqRing.mul x.2.1 x.2.2),
      q3rqRing.mul_comm x.2.1 q3rqZeta,
      q3rqRing.mul_assoc q3rqZeta x.2.1 (q3rqRing.mul x.2.1 x.2.2),
      ← q3rqRing.mul_assoc x.2.1 x.2.1 x.2.2,
      q3rqRing.left_distrib x.2.2 (q3rqRing.mul x.2.1 x.2.1) (q3rqRing.neg (q3rqRing.mul x.1 x.2.2)),
      q3rqRing.mul_comm x.2.2 (q3rqRing.mul x.2.1 x.2.1),
      q3rqRing.mul_neg x.2.2 (q3rqRing.mul x.1 x.2.2),
      q3rqRing.mul_comm x.2.2 (q3rqRing.mul x.1 x.2.2),
      q3rqRing.left_distrib q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 x.2.1) x.2.2) (q3rqRing.neg (q3rqRing.mul (q3rqRing.mul x.1 x.2.2) x.2.2)),
      q3rqRing.mul_neg q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 x.2.2) x.2.2)]
  exact q3k_cancel6a (q3rqRing.mul (q3rqRing.mul x.1 x.1) x.2.1)
    (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.1 x.2.2) x.2.2))
    (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 x.2.1) x.2.2))
/-- N の Y² 成分 = 0（相殺）。 -/
theorem q3k_xwt_2 (x : q3kCar) : (q3kMul x (q3kWt x)).2.2 = q3rqZero := by
  rw [q3kMul_2, q3kWt_0, q3kWt_1, q3kWt_2, q3k_M_eq, q3k_A_eq, q3k_N_eq]
  rw [q3rqRing.left_distrib x.1 (q3rqRing.mul x.2.1 x.2.1) (q3rqRing.neg (q3rqRing.mul x.1 x.2.2)),
      ← q3rqRing.mul_assoc x.1 x.2.1 x.2.1,
      q3rqRing.mul_neg x.1 (q3rqRing.mul x.1 x.2.2),
      ← q3rqRing.mul_assoc x.1 x.1 x.2.2,
      q3rqRing.left_distrib x.2.1 (q3rqRing.neg (q3rqRing.mul x.1 x.2.1)) (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.2 x.2.2)),
      q3rqRing.mul_neg x.2.1 (q3rqRing.mul x.1 x.2.1),
      q3rqRing.mul_comm x.2.1 (q3rqRing.mul x.1 x.2.1),
      ← q3rqRing.mul_assoc x.2.1 q3rqZeta (q3rqRing.mul x.2.2 x.2.2),
      q3rqRing.mul_comm x.2.1 q3rqZeta,
      q3rqRing.mul_assoc q3rqZeta x.2.1 (q3rqRing.mul x.2.2 x.2.2),
      ← q3rqRing.mul_assoc x.2.1 x.2.2 x.2.2,
      q3rqRing.left_distrib x.2.2 (q3rqRing.mul x.1 x.1) (q3rqRing.neg (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.1 x.2.2))),
      q3rqRing.mul_comm x.2.2 (q3rqRing.mul x.1 x.1),
      q3rqRing.mul_neg x.2.2 (q3rqRing.mul q3rqZeta (q3rqRing.mul x.2.1 x.2.2)),
      ← q3rqRing.mul_assoc x.2.2 q3rqZeta (q3rqRing.mul x.2.1 x.2.2),
      q3rqRing.mul_comm x.2.2 q3rqZeta,
      q3rqRing.mul_assoc q3rqZeta x.2.2 (q3rqRing.mul x.2.1 x.2.2),
      q3rqRing.mul_comm x.2.2 (q3rqRing.mul x.2.1 x.2.2)]
  exact q3k_cancel6b (q3rqRing.mul (q3rqRing.mul x.1 x.2.1) x.2.1)
    (q3rqRing.mul (q3rqRing.mul x.1 x.1) x.2.2)
    (q3rqRing.mul q3rqZeta (q3rqRing.mul (q3rqRing.mul x.2.1 x.2.2) x.2.2))

/-- x·w = embed(N)。 -/
theorem q3k_x_wt (x : q3kCar) : q3kMul x (q3kWt x) = q3kEmbed (q3kNormBase x) :=
  q3k_ext (q3k_xwt_0 x) (q3k_xwt_1 x) (q3k_xwt_2 x)

/-- **q3k-5d（★★）: 3 次ノルム恒等式** N(x)=x·σx·σ²x = embed(a³+ζ₃b³+ζ₃²c³−3ζ₃abc)。 -/
theorem q3k_norm_eq (x : q3kCar) :
    q3kMul x (q3kMul (q3kSigma x) (q3kSigma2 x)) = q3kEmbed (q3kNormBase x) := by
  rw [q3k_w_eq]; exact q3k_x_wt x

/-- 零元ブリッジ。 -/
theorem q3k_Z_eq : q3rqZero = q3rqRing.zero := rfl

/-- **q3k-5e: embed は環準同型（積）** embed(p)·embed(q)=embed(pq)。 -/
theorem q3k_embed_mul (p q : q3rqCar) :
    q3kMul (q3kEmbed p) (q3kEmbed q) = q3kEmbed (q3rqMul p q) := by
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul p q) (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul q3rqZero q3rqZero) (q3rqRing.mul q3rqZero q3rqZero))) = q3rqRing.mul p q
    rw [q3k_Z_eq, q3rqRing.mul_zero q3rqRing.zero, q3rqRing.zero_add q3rqRing.zero, q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero (q3rqRing.mul p q)]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul p q3rqZero) (q3rqRing.mul q3rqZero q)) (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqZero q3rqZero)) = q3rqRing.zero
    rw [q3k_Z_eq, q3rqRing.mul_zero p, q3rqRing.zero_mul q, q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul p q3rqZero) (q3rqRing.mul q3rqZero q3rqZero)) (q3rqRing.mul q3rqZero q) = q3rqRing.zero
    rw [q3k_Z_eq, q3rqRing.mul_zero p, q3rqRing.mul_zero q3rqRing.zero, q3rqRing.add_zero q3rqRing.zero, q3rqRing.zero_mul q, q3rqRing.add_zero q3rqRing.zero]

/-- embed(1)=1。 -/
theorem q3k_embed_one : q3kEmbed q3rqOne = q3kOne := rfl

/-- embed は単射。 -/
theorem q3k_embed_inj {p q : q3rqCar} (h : q3kEmbed p = q3kEmbed q) : p = q :=
  congrArg (fun z : q3kCar => z.1) h

/-! ## q3k-6: 単数群 U₃ = O_M^× と閉形式 3 次ノルム逆元 -/

theorem q3k_kM_eq : q3kMul = q3kRing.mul := rfl

theorem q3k_sigma2_one : q3kSigma2 q3kOne = q3kOne := by
  apply q3k_ext
  · rfl
  · exact q3rqRing.mul_zero q3rqZetaSq
  · exact q3rqRing.mul_zero q3rqZeta

theorem q3k_sigma2_mul (x y : q3kCar) :
    q3kSigma2 (q3kMul x y) = q3kMul (q3kSigma2 x) (q3kSigma2 y) := by
  rw [q3k_sigma2_comp (q3kMul x y), q3k_sigma_mul x y, q3k_sigma_mul (q3kSigma x) (q3kSigma y),
      ← q3k_sigma2_comp x, ← q3k_sigma2_comp y]

theorem q3k_six_reorder (x y a b c d : q3kCar) :
    q3kMul (q3kMul x y) (q3kMul (q3kMul a b) (q3kMul c d))
      = q3kMul (q3kMul x (q3kMul a c)) (q3kMul y (q3kMul b d)) := by
  rw [q3k_kM_eq, q3kRing.mul_mul_mul_comm a b c d,
      q3kRing.mul_mul_mul_comm x y (q3kRing.mul a c) (q3kRing.mul b d)]

theorem q3k_normBase_mul (x y : q3kCar) :
    q3kNormBase (q3kMul x y) = q3rqMul (q3kNormBase x) (q3kNormBase y) := by
  apply q3k_embed_inj
  rw [← q3k_norm_eq (q3kMul x y), q3k_sigma_mul x y, q3k_sigma2_mul x y,
      q3k_six_reorder x y (q3kSigma x) (q3kSigma y) (q3kSigma2 x) (q3kSigma2 y),
      q3k_norm_eq x, q3k_norm_eq y, q3k_embed_mul (q3kNormBase x) (q3kNormBase y)]

theorem q3k_normBase_one : q3kNormBase q3kOne = q3rqOne := by
  apply q3k_embed_inj
  rw [← q3k_norm_eq q3kOne, q3k_sigma_one, q3k_sigma2_one, q3k_one_mul, q3k_one_mul]
  exact q3k_embed_one.symm

def q3kUnitMem (x : q3kCar) : Prop := q3rqUnitMem (q3kNormBase x)
def q3kInv (x : q3kCar) (hx : q3kUnitMem x) : q3kCar :=
  q3kMul (q3kMul (q3kSigma x) (q3kSigma2 x)) (q3kEmbed (q3rqInv (q3kNormBase x) hx))

theorem q3k_inv_mul (x : q3kCar) (hx : q3kUnitMem x) :
    q3kMul x (q3kInv x hx) = q3kOne := by
  show q3kMul x (q3kMul (q3kMul (q3kSigma x) (q3kSigma2 x)) (q3kEmbed (q3rqInv (q3kNormBase x) hx))) = q3kOne
  rw [← q3k_mul_assoc x (q3kMul (q3kSigma x) (q3kSigma2 x)) (q3kEmbed (q3rqInv (q3kNormBase x) hx)),
      q3k_norm_eq x, q3k_embed_mul (q3kNormBase x) (q3rqInv (q3kNormBase x) hx)]
  have hn : q3rqMul (q3kNormBase x) (q3rqInv (q3kNormBase x) hx) = q3rqOne :=
    (q3rqRing.mul_comm (q3kNormBase x) (q3rqInv (q3kNormBase x) hx)).trans
      (q3rq_inv_mul (q3kNormBase x) hx)
  rw [hn]
  exact q3k_embed_one

theorem q3k_inv_mul' (x : q3kCar) (hx : q3kUnitMem x) :
    q3kMul (q3kInv x hx) x = q3kOne := by
  rw [q3k_mul_comm]; exact q3k_inv_mul x hx

theorem q3k_normBase_inv (x : q3kCar) (hx : q3kUnitMem x) :
    q3kNormBase (q3kInv x hx) = q3rqInv (q3kNormBase x) hx := by
  have h1 : q3rqMul (q3kNormBase x) (q3kNormBase (q3kInv x hx)) = q3rqOne := by
    rw [← q3k_normBase_mul x (q3kInv x hx), q3k_inv_mul x hx, q3k_normBase_one]
  have key : q3rqInv (q3kNormBase x) hx = q3kNormBase (q3kInv x hx) :=
    calc q3rqInv (q3kNormBase x) hx
        = q3rqMul (q3rqInv (q3kNormBase x) hx) q3rqOne := (q3rq_mul_one _).symm
      _ = q3rqMul (q3rqInv (q3kNormBase x) hx)
            (q3rqMul (q3kNormBase x) (q3kNormBase (q3kInv x hx))) := by rw [h1]
      _ = q3rqMul (q3rqMul (q3rqInv (q3kNormBase x) hx) (q3kNormBase x))
            (q3kNormBase (q3kInv x hx)) := (q3rqRing.mul_assoc _ _ _).symm
      _ = q3rqMul q3rqOne (q3kNormBase (q3kInv x hx)) := by rw [q3rq_inv_mul (q3kNormBase x) hx]
      _ = q3kNormBase (q3kInv x hx) := q3rq_one_mul _
  exact key.symm

theorem q3k_unit_mul {x y : q3kCar} (hx : q3kUnitMem x) (hy : q3kUnitMem y) :
    q3kUnitMem (q3kMul x y) := by
  show q3rqUnitMem (q3kNormBase (q3kMul x y))
  rw [q3k_normBase_mul x y]
  exact q3rq_unit_mul hx hy

theorem q3k_unit_one : q3kUnitMem q3kOne := by
  show q3rqUnitMem (q3kNormBase q3kOne)
  rw [q3k_normBase_one]; exact q3rq_unit_one

theorem q3k_unit_inv (x : q3kCar) (hx : q3kUnitMem x) : q3kUnitMem (q3kInv x hx) := by
  show q3rqUnitMem (q3kNormBase (q3kInv x hx))
  rw [q3k_normBase_inv x hx]
  exact q3rq_unit_inv (q3kNormBase x) hx

def q3kU : Grp where
  carrier := { x : q3kCar // q3kUnitMem x }
  mul := fun x y => ⟨q3kMul x.val y.val, q3k_unit_mul x.property y.property⟩
  one := ⟨q3kOne, q3k_unit_one⟩
  inv := fun x => ⟨q3kInv x.val x.property, q3k_unit_inv x.val x.property⟩
  mul_assoc := fun x y z => Subtype.ext (q3k_mul_assoc x.val y.val z.val)
  one_mul := fun x => Subtype.ext (q3k_one_mul x.val)
  inv_mul := fun x => Subtype.ext (q3k_inv_mul' x.val x.property)

/-! ## q3k-7: 実 ζ₉ = Y（位数ちょうど 9） -/


def q3kZeta9 : q3kCar := ((q3rqZero, q3rqOne, q3rqZero) : q3kCar)

theorem q3k_zeta9_sq : q3kMul q3kZeta9 q3kZeta9 = ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) := by
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero)
        (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul q3rqRing.one q3rqRing.zero) (q3rqRing.mul q3rqRing.zero q3rqRing.one))) = q3rqRing.zero
    rw [q3rqRing.mul_zero q3rqRing.one, q3rqRing.zero_mul q3rqRing.one, q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.mul_zero q3rqZeta, q3rqRing.mul_zero q3rqRing.zero, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.one) (q3rqRing.mul q3rqRing.one q3rqRing.zero))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqRing.zero q3rqRing.zero)) = q3rqRing.zero
    rw [q3rqRing.zero_mul q3rqRing.one, q3rqRing.mul_zero q3rqRing.one, q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero) (q3rqRing.mul q3rqRing.one q3rqRing.one))
        (q3rqRing.mul q3rqRing.zero q3rqRing.zero) = q3rqRing.one
    rw [q3rqRing.mul_zero q3rqRing.zero, q3rqRing.one_mul q3rqRing.one, q3rqRing.zero_add q3rqRing.one,
        q3rqRing.add_zero q3rqRing.one]

theorem q3k_zeta9_cube : q3kMul (q3kMul q3kZeta9 q3kZeta9) q3kZeta9 = q3kEmbed q3rqZeta := by
  rw [q3k_zeta9_sq]
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero)
        (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero) (q3rqRing.mul q3rqRing.one q3rqRing.one))) = q3rqZeta
    rw [q3rqRing.mul_zero q3rqRing.zero, q3rqRing.one_mul q3rqRing.one, q3rqRing.zero_add q3rqRing.one,
        q3rqRing.mul_one q3rqZeta, q3rqRing.zero_add q3rqZeta]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.one) (q3rqRing.mul q3rqRing.zero q3rqRing.zero))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqRing.one q3rqRing.zero)) = q3rqRing.zero
    rw [q3rqRing.zero_mul q3rqRing.one, q3rqRing.mul_zero q3rqRing.zero, q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.mul_zero q3rqRing.one, q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero) (q3rqRing.mul q3rqRing.zero q3rqRing.one))
        (q3rqRing.mul q3rqRing.one q3rqRing.zero) = q3rqRing.zero
    rw [q3rqRing.mul_zero q3rqRing.zero, q3rqRing.zero_mul q3rqRing.one, q3rqRing.add_zero q3rqRing.zero,
        q3rqRing.mul_zero q3rqRing.one, q3rqRing.add_zero q3rqRing.zero]

theorem q3k_zeta9_pow9 :
    q3kMul (q3kMul (q3kMul (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) (q3kMul (q3kMul q3kZeta9 q3kZeta9) q3kZeta9))
      (q3kMul (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) = q3kOne := by
  rw [q3k_zeta9_cube, q3k_embed_mul, q3k_embed_mul, q3rq_zeta_cube]
  rfl

theorem q3k_zeta9_ne_one : q3kZeta9 ≠ q3kOne := by
  intro h
  have h1 : q3rqOne = q3rqZero := congrArg (fun z : q3kCar => z.2.1) h
  have h2 : z3.one = z3.zero := congrArg (fun p : q3rqCar => p.1) h1
  exact q3rq_z3_one_ne_zero h2

theorem q3k_zeta9_cube_ne_one : q3kMul (q3kMul q3kZeta9 q3kZeta9) q3kZeta9 ≠ q3kOne := by
  rw [q3k_zeta9_cube]
  intro h
  have h1 : q3rqZeta = q3rqOne := congrArg (fun z : q3kCar => z.1) h
  exact q3rq_zeta_ne_one h1

/-! ## q3k-8: capstone -/

/-- **q3k-8a: 実巡回 3 次 Kummer 拡大データ** — 実 O_M=M（可換環）・実相対 Galois σ
    （位数 3）・実 3 次ノルム閉形式・単数群 U₃（閉形式逆元）・実 ζ₉（位数ちょうど 9）。 -/
structure Q3KummerCubicData where
  /-- 可換環 O_M = M = L₂[Y]/(Y³−ζ₃)。 -/
  ring : CRing
  /-- 相対 Galois σ（Y↦ζ₃Y）。 -/
  sigma : q3kCar → q3kCar
  /-- σ²。 -/
  sigma2 : q3kCar → q3kCar
  /-- 3 次ノルム多項式 O_M→O_{L₂}。 -/
  norm : q3kCar → q3rqCar
  /-- 単数群 U₃ = O_M^×。 -/
  units : Grp
  /-- 実 ζ₉ = Y。 -/
  zeta9 : q3kCar
  /-- σ は環準同型。 -/
  sigma_mul : ∀ x y, sigma (q3kMul x y) = q3kMul (sigma x) (sigma y)
  /-- σ³ = id（位数 3）。 -/
  sigma3_id : ∀ x, sigma (sigma (sigma x)) = x
  /-- N(x)=x·σx·σ²x = embed(ノルム多項式)。 -/
  norm_eq : ∀ x, q3kMul x (q3kMul (sigma x) (sigma2 x)) = q3kEmbed (norm x)
  /-- 単数の閉形式逆元性 x·x⁻¹=1。 -/
  inv_closed : ∀ (x : q3kCar) (hx : q3kUnitMem x), q3kMul x (q3kInv x hx) = q3kOne
  /-- Y³ = ζ₃（埋め込み）。 -/
  zeta9_cube : q3kMul (q3kMul zeta9 zeta9) zeta9 = q3kEmbed q3rqZeta
  /-- ζ₉ ≠ 1。 -/
  zeta9_ne_one : zeta9 ≠ q3kOne
  /-- ζ₉³ = ζ₃ ≠ 1（位数ちょうど 9 の核）。 -/
  zeta9_cube_ne_one : q3kMul (q3kMul zeta9 zeta9) zeta9 ≠ q3kOne

/-- **q3k-8b: 見出し実例** — 実 M = ℚ₃(ζ₉) = L₂[Y]/(Y³−ζ₃)。 -/
def q3kData : Q3KummerCubicData where
  ring := q3kRing
  sigma := q3kSigma
  sigma2 := q3kSigma2
  norm := q3kNormBase
  units := q3kU
  zeta9 := q3kZeta9
  sigma_mul := q3k_sigma_mul
  sigma3_id := q3k_sigma3_id
  norm_eq := q3k_norm_eq
  inv_closed := q3k_inv_mul
  zeta9_cube := q3k_zeta9_cube
  zeta9_ne_one := q3k_zeta9_ne_one
  zeta9_cube_ne_one := q3k_zeta9_cube_ne_one

/-- **q3k-8c: 実巡回 3 次 Kummer 拡大の存在**（実 O_{L₂} 上・単数群＋実 σ＋実 ζ₉）。 -/
theorem q3k_exists : Nonempty Q3KummerCubicData := ⟨q3kData⟩


end IUT
