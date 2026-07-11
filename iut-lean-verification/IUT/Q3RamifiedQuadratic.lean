/-
  IUT/Q3RamifiedQuadratic.lean — R1（実分岐 2 次局所拡大 O_{ℚ₃(ζ₃)} = ℤ₃[√−3]）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**（骨格・模型・代理でなく、実 ℤ₃ =
     zpRing 3 の上に、分岐 2 次拡大 L₂ = ℚ₃(ζ₃) = ℚ₃(√−3) の**整数環 O_{L₂} = ℤ₃[√−3]**
     を実際の対 (a,b) ↔ a+b√−3 として建て、その**単数群 U₂ = O_{L₂}^×** を
     **共役ノルム型の閉形式逆元**（zpUnitInv 消費・体エンジン不使用）で本物に構成する。
     さらに実 ζ₃ = (−1+√−3)/2（2⁻¹∈ℤ₃ は閉形式）・μ₃ ⊂ U₂・分岐 e=2（3=−λ²）・
     ℚ₃^×↪L₂^× を実に立てる。toy 主語なし——主語は実 z3 = zpRing 3 上の実対環。）

  complete_pct 影響: **A7 の named prerequisite の本物 discharge**（q3mr 正直限定 1 が
  named future target と明記した「実 ℚ₃(ζ₃) 分岐 2 次拡大」を本物化）。μ_{3ⁿ} テータ／
  ℤ₃^× kill キャンペーン（R1→R4）の**FOUNDATION**。単体では complete_pct 丸め値の前進は
  ~0（foundation 建設・named-blocker discharge）——A7 の実ターゲットは level-3 kill
  （後続 R3/R4）で到達する。本ラウンドは「complete_pct 0 前進（骨格でなく本物基盤の
  先行建設）」と正直申告する。

  内容（§6 の 8 項）:
   * q3rqCar / q3rqMul / q3rqRing         — 実 O_{L₂} = ℤ₃×ℤ₃（Gauss 積・可換環）
   * q3rqNorm / q3rq_norm_mul             — ノルム N=a²+3b²・Brahmagupta N(xy)=N(x)N(y)
                                            （共役 ring-hom x·x̄=(N,0) 経由・機械的多項式
                                             恒等式を回避）
   * q3rqUnitMem / q3rqInv / q3rq_inv_mul — 単数判定・**閉形式共役ノルム逆元**・逆元性
   * q3rqU / q3rqLx                       — **単数群 U₂ = O_{L₂}^×**・L₂^× = ℤ×U₂
   * q3rqHalf / q3rq_two_half             — 実 2⁻¹∈ℤ₃（zpUnitInv・閉形式）
   * q3rqZeta / q3rq_zeta_cube / q3rq_mu3_closed
                                          — **実 ζ₃=(−1+√−3)/2・ζ₃³=1・位数ちょうど 3・
                                             μ₃⊂U₂**（コードベース初の実局所環内 μ₃）
   * q3rqLambda / q3rq_lambda_sq / q3rq_three_cube
                                          — λ=(0,1)・λ²=(−3,0)（e=2 実現・3=−λ²）・3³
   * q3rqEmbed / q3rq_embed_inj / q3rq_ramification
                                          — **ℚ₃^×↪L₂^×**・単射・v_λ∘embed=2·v₃（分岐指数 2）
   * Q3RamQuadData / q3rqData / q3rq_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・追記のみ）:
  1. **O_L と L^× のみ**（整数環＋単数群）。L を体としては建てない——total inverse は
     無く A2 恒久限定を継承する。逆元は**単数（ノルムが ℤ₃^× の元）に限る**閉形式。
  2. **kill は未達（foundation）**。μ₃ ⊂ L^× は実在するが、テータ群・mono-theta 剛性は
     後続 R3/R4。本ファイルは ℤ₃^× 不定性を一切殺さない。
  3. **e=2 分岐は整数レベルの実現**（3 = −λ²・λ=(0,1)）。付値理論・位相・完備化は範囲外
     （群提示 ℤ×U₂ の第 1 成分が v_λ の代数的実現）。
  4. R1–R4 完了後の ℤ₃^× kill は **mod-3 成分（Aut(μ₃)≅ℤ/2）のみ**。1+3ℤ₃ の pro-3
     主単数部分は n≥2＝F-wild まで残存。
  5. **tmzLimit（tmi の ℤ₃(1)）への比較準同型は含めない**（二重計上防止・q3mr §4-6 と
     同方針）。R1–R4 は tmi の不定性を殺したとは主張しない。
  6. L₂ の担体は**第 3 の兄弟担体**（cq3Field=ℚ(√−3)/ℚ・eisRing 3=Quot 版 と並ぶ ℤ₃ 対版）。
     同型輸送は主張しない（cnf (iii) 前例）。
  7. **Galois 作用ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ**（q3mr/q3th 正直限定を継承）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Zp3ValuationRing
import IUT.ZpUnits
import IUT.Q3TateCurve
import IUT.QuadraticNorm
import IUT.FormalGroupExists
import IUT.LTIterate

namespace IUT

/-! ## q3rq-0: スカラー定数 2, 3, −3（実 ℤ₃ の元） -/

/-- 実 ℤ₃ の元 2 = 1 + 1。 -/
def q3rqTwoZ : z3.carrier := z3.add z3.one z3.one

/-- 実 ℤ₃ の元 3 = 2 + 1。 -/
def q3rqThree : z3.carrier := z3.add q3rqTwoZ z3.one

/-- ガウス乗数 D = −3（√−3² = −3 の実現）。 -/
def q3rqD : z3.carrier := z3.neg q3rqThree

/-- D = −3 の展開（rw 補助）。 -/
theorem q3rq_D_eq : q3rqD = z3.neg q3rqThree := rfl

/-- 3 は 2 を割らない（単数性の witness）。 -/
theorem q3rq_three_not_dvd_two : ¬ ((3 : Nat) : Int) ∣ (2 : Int) := by
  intro h
  have h1 : ((3 : Nat) : Int).natAbs ∣ ((2 : Int)).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_natCast] at h1
  have h2 : (3 : Nat) ∣ ((2 : Int)).natAbs := h1
  have h3 : ((2 : Int)).natAbs = 2 := rfl
  rw [h3] at h2
  have := Nat.le_of_dvd (by omega) h2
  omega

/-- **2 は ℤ₃ の単数**（レベル 1 剰余 = 2・3∤2）。 -/
theorem q3rq_two_unit : IsZpUnit 3 q3rqTwoZ := by
  refine ⟨2, ?_, q3rq_three_not_dvd_two⟩
  show (z3.add z3.one z3.one).val 1 = Quot.mk (modCong (3 ^ 1)).rel 2
  show (zmod (3 ^ 1)).mul ((zpOne 3).val 1) ((zpOne 3).val 1)
    = Quot.mk (modCong (3 ^ 1)).rel 2
  show Quot.mk (modCong (3 ^ 1)).rel (1 + 1) = Quot.mk (modCong (3 ^ 1)).rel 2
  rfl

/-! ## q3rq-1: 実 2⁻¹ ∈ ℤ₃（閉形式・zpUnitInv） -/

/-- **q3rq-5a: 実 2⁻¹ ∈ ℤ₃**（zpUnitInv による閉形式の整合列。代表元抽出なし・
    choice-free）。レベル n では代表 (3ⁿ+1)/2 に一致するが、ここでは既存の
    幾何級数逆元 zpUnitInv を消費する。 -/
def q3rqHalf : z3.carrier := zpUnitInv 3 isPrime_three q3rqTwoZ q3rq_two_unit

/-- **q3rq-5b: 2·h = 1**（h = 2⁻¹）。 -/
theorem q3rq_two_half : z3.mul q3rqTwoZ q3rqHalf = z3.one := by
  have h := zpUnitInv_mul 3 isPrime_three q3rqTwoZ q3rq_two_unit
  show z3.mul q3rqTwoZ q3rqHalf = z3.one
  rw [z3.mul_comm q3rqTwoZ q3rqHalf]
  exact h

/-! ## q3rq-1': 台とガウス演算 — 実 ℤ₃×ℤ₃（(a,b) は a+b√−3） -/

/-- **q3rq-1a: 台** — 実 ℤ₃×ℤ₃（第 1 成分 = 有理整数部、第 2 成分 = √−3 部）。 -/
def q3rqCar : Type := z3.carrier × z3.carrier

/-- 対の外延性。 -/
theorem q3rq_ext : ∀ {x y : q3rqCar}, x.1 = y.1 → x.2 = y.2 → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

/-- 加法 (a,b)+(c,d) = (a+c, b+d)。 -/
def q3rqAdd (x y : q3rqCar) : q3rqCar :=
  ((z3.add x.1 y.1, z3.add x.2 y.2) : q3rqCar)

/-- 反元 −(a,b) = (−a,−b)。 -/
def q3rqNeg (x : q3rqCar) : q3rqCar :=
  ((z3.neg x.1, z3.neg x.2) : q3rqCar)

/-- 0 = (0,0)。 -/
def q3rqZero : q3rqCar := ((z3.zero, z3.zero) : q3rqCar)

/-- 1 = (1,0)。 -/
def q3rqOne : q3rqCar := ((z3.one, z3.zero) : q3rqCar)

/-- **ガウス型乗法** (a,b)·(c,d) = (ac + D·bd, ad + bc)、D = −3。 -/
def q3rqMul (x y : q3rqCar) : q3rqCar :=
  ((z3.add (z3.mul x.1 y.1) (z3.mul q3rqD (z3.mul x.2 y.2)),
    z3.add (z3.mul x.1 y.2) (z3.mul x.2 y.1)) : q3rqCar)

/-- **実ノルム** N(a,b) = a² − D·b² = a² + 3b²（ℤ₃ 値）。 -/
def q3rqNorm (x : q3rqCar) : z3.carrier :=
  z3.add (z3.mul x.1 x.1) (z3.neg (z3.mul q3rqD (z3.mul x.2 x.2)))

/-! ## q3rq-2: 実可換環 O_{L₂} -/

/-- **q3rq-1b（★）: O_{L₂} = ℤ₃[√−3] は実可換環** — 加法成分ごと・乗法 D=−3 の
    ガウス則。結合・可換・分配は z3 の環公理からの明示計算（cq3Ring の写経を z3 で）。 -/
def q3rqRing : CRing where
  carrier := q3rqCar
  add := q3rqAdd
  zero := q3rqZero
  neg := q3rqNeg
  mul := q3rqMul
  one := q3rqOne
  add_assoc := fun x y z =>
    q3rq_ext (z3.add_assoc x.1 y.1 z.1) (z3.add_assoc x.2 y.2 z.2)
  zero_add := fun x =>
    q3rq_ext (z3.zero_add x.1) (z3.zero_add x.2)
  neg_add := fun x =>
    q3rq_ext (z3.neg_add x.1) (z3.neg_add x.2)
  add_comm := fun x y =>
    q3rq_ext (z3.add_comm x.1 y.1) (z3.add_comm x.2 y.2)
  mul_assoc := by
    intro x y z
    apply q3rq_ext
    · show z3.add
            (z3.mul
              (z3.add (z3.mul x.1 y.1)
                (z3.mul q3rqD (z3.mul x.2 y.2))) z.1)
            (z3.mul q3rqD
              (z3.mul
                (z3.add (z3.mul x.1 y.2) (z3.mul x.2 y.1)) z.2))
          = z3.add
            (z3.mul x.1
              (z3.add (z3.mul y.1 z.1)
                (z3.mul q3rqD (z3.mul y.2 z.2))))
            (z3.mul q3rqD
              (z3.mul x.2
                (z3.add (z3.mul y.1 z.2) (z3.mul y.2 z.1))))
      rw [z3.right_distrib (z3.mul x.1 y.1)
            (z3.mul q3rqD (z3.mul x.2 y.2)) z.1,
          z3.right_distrib (z3.mul x.1 y.2) (z3.mul x.2 y.1) z.2,
          z3.left_distrib q3rqD (z3.mul (z3.mul x.1 y.2) z.2)
            (z3.mul (z3.mul x.2 y.1) z.2),
          z3.left_distrib x.1 (z3.mul y.1 z.1)
            (z3.mul q3rqD (z3.mul y.2 z.2)),
          z3.left_distrib x.2 (z3.mul y.1 z.2) (z3.mul y.2 z.1),
          z3.left_distrib q3rqD (z3.mul x.2 (z3.mul y.1 z.2))
            (z3.mul x.2 (z3.mul y.2 z.1)),
          z3.mul_assoc x.1 y.1 z.1,
          z3.mul_assoc q3rqD (z3.mul x.2 y.2) z.1,
          z3.mul_assoc x.2 y.2 z.1,
          z3.mul_assoc x.1 y.2 z.2,
          ← z3.mul_assoc q3rqD x.1 (z3.mul y.2 z.2),
          z3.mul_comm q3rqD x.1,
          z3.mul_assoc x.1 q3rqD (z3.mul y.2 z.2),
          z3.mul_assoc x.2 y.1 z.2,
          z3.add_add_add_comm (z3.mul x.1 (z3.mul y.1 z.1))
            (z3.mul q3rqD (z3.mul x.2 (z3.mul y.2 z.1)))
            (z3.mul x.1 (z3.mul q3rqD (z3.mul y.2 z.2)))
            (z3.mul q3rqD (z3.mul x.2 (z3.mul y.1 z.2))),
          z3.add_comm (z3.mul q3rqD (z3.mul x.2 (z3.mul y.2 z.1)))
            (z3.mul q3rqD (z3.mul x.2 (z3.mul y.1 z.2)))]
    · show z3.add
            (z3.mul
              (z3.add (z3.mul x.1 y.1)
                (z3.mul q3rqD (z3.mul x.2 y.2))) z.2)
            (z3.mul
              (z3.add (z3.mul x.1 y.2) (z3.mul x.2 y.1)) z.1)
          = z3.add
            (z3.mul x.1
              (z3.add (z3.mul y.1 z.2) (z3.mul y.2 z.1)))
            (z3.mul x.2
              (z3.add (z3.mul y.1 z.1)
                (z3.mul q3rqD (z3.mul y.2 z.2))))
      rw [z3.right_distrib (z3.mul x.1 y.1)
            (z3.mul q3rqD (z3.mul x.2 y.2)) z.2,
          z3.right_distrib (z3.mul x.1 y.2) (z3.mul x.2 y.1) z.1,
          z3.left_distrib x.1 (z3.mul y.1 z.2) (z3.mul y.2 z.1),
          z3.left_distrib x.2 (z3.mul y.1 z.1)
            (z3.mul q3rqD (z3.mul y.2 z.2)),
          z3.mul_assoc x.1 y.1 z.2,
          z3.mul_assoc q3rqD (z3.mul x.2 y.2) z.2,
          z3.mul_assoc x.2 y.2 z.2,
          ← z3.mul_assoc q3rqD x.2 (z3.mul y.2 z.2),
          z3.mul_comm q3rqD x.2,
          z3.mul_assoc x.2 q3rqD (z3.mul y.2 z.2),
          z3.mul_assoc x.1 y.2 z.1,
          z3.mul_assoc x.2 y.1 z.1,
          z3.add_add_add_comm (z3.mul x.1 (z3.mul y.1 z.2))
            (z3.mul x.2 (z3.mul q3rqD (z3.mul y.2 z.2)))
            (z3.mul x.1 (z3.mul y.2 z.1))
            (z3.mul x.2 (z3.mul y.1 z.1)),
          z3.add_comm (z3.mul x.2 (z3.mul q3rqD (z3.mul y.2 z.2)))
            (z3.mul x.2 (z3.mul y.1 z.1))]
  one_mul := by
    intro x
    apply q3rq_ext
    · show z3.add (z3.mul z3.one x.1)
            (z3.mul q3rqD (z3.mul z3.zero x.2)) = x.1
      rw [z3.one_mul x.1, z3.zero_mul x.2, z3.mul_zero q3rqD,
        z3.add_zero x.1]
    · show z3.add (z3.mul z3.one x.2)
            (z3.mul z3.zero x.1) = x.2
      rw [z3.one_mul x.2, z3.zero_mul x.1, z3.add_zero x.2]
  mul_comm := by
    intro x y
    apply q3rq_ext
    · show z3.add (z3.mul x.1 y.1)
            (z3.mul q3rqD (z3.mul x.2 y.2))
          = z3.add (z3.mul y.1 x.1)
            (z3.mul q3rqD (z3.mul y.2 x.2))
      rw [z3.mul_comm x.1 y.1, z3.mul_comm x.2 y.2]
    · show z3.add (z3.mul x.1 y.2) (z3.mul x.2 y.1)
          = z3.add (z3.mul y.1 x.2) (z3.mul y.2 x.1)
      rw [z3.mul_comm x.1 y.2, z3.mul_comm x.2 y.1,
        z3.add_comm (z3.mul y.2 x.1) (z3.mul y.1 x.2)]
  left_distrib := by
    intro x y z
    apply q3rq_ext
    · show z3.add (z3.mul x.1 (z3.add y.1 z.1))
            (z3.mul q3rqD (z3.mul x.2 (z3.add y.2 z.2)))
          = z3.add
            (z3.add (z3.mul x.1 y.1)
              (z3.mul q3rqD (z3.mul x.2 y.2)))
            (z3.add (z3.mul x.1 z.1)
              (z3.mul q3rqD (z3.mul x.2 z.2)))
      rw [z3.left_distrib x.1 y.1 z.1, z3.left_distrib x.2 y.2 z.2,
        z3.left_distrib q3rqD (z3.mul x.2 y.2) (z3.mul x.2 z.2),
        z3.add_add_add_comm (z3.mul x.1 y.1) (z3.mul x.1 z.1)
          (z3.mul q3rqD (z3.mul x.2 y.2))
          (z3.mul q3rqD (z3.mul x.2 z.2))]
    · show z3.add (z3.mul x.1 (z3.add y.2 z.2))
            (z3.mul x.2 (z3.add y.1 z.1))
          = z3.add
            (z3.add (z3.mul x.1 y.2) (z3.mul x.2 y.1))
            (z3.add (z3.mul x.1 z.2) (z3.mul x.2 z.1))
      rw [z3.left_distrib x.1 y.2 z.2, z3.left_distrib x.2 y.1 z.1,
        z3.add_add_add_comm (z3.mul x.1 y.2) (z3.mul x.1 z.2)
          (z3.mul x.2 y.1) (z3.mul x.2 z.1)]

/-! ## q3rq-2': ノルムの乗法性（Brahmagupta・共役 ring-hom 経由） -/

/-- **共役** (a,b)̄ = (a, −b)。 -/
def q3rqConj (x : q3rqCar) : q3rqCar := ((x.1, z3.neg x.2) : q3rqCar)

/-- ノルムを環元として持つ (N(x), 0)。 -/
def q3rqEn (x : q3rqCar) : q3rqCar := ((q3rqNorm x, z3.zero) : q3rqCar)

/-- 4 因子入替（q3rqRing 版）。 -/
theorem q3rq_mmmc (a b c d : q3rqCar) :
    q3rqMul (q3rqMul a b) (q3rqMul c d) = q3rqMul (q3rqMul a c) (q3rqMul b d) :=
  q3rqRing.mul_mul_mul_comm a b c d

/-- **q3rq-2a: x·x̄ = (N(x), 0)** — 第 1 成分 a²−Db²=N・第 2 成分 −ab+ba=0。 -/
theorem q3rq_mul_conj (x : q3rqCar) : q3rqMul x (q3rqConj x) = q3rqEn x := by
  apply q3rq_ext
  · show z3.add (z3.mul x.1 x.1) (z3.mul q3rqD (z3.mul x.2 (z3.neg x.2)))
        = z3.add (z3.mul x.1 x.1) (z3.neg (z3.mul q3rqD (z3.mul x.2 x.2)))
    rw [z3.mul_neg x.2 x.2, z3.mul_neg q3rqD (z3.mul x.2 x.2)]
  · show z3.add (z3.mul x.1 (z3.neg x.2)) (z3.mul x.2 x.1) = z3.zero
    rw [z3.mul_neg x.1 x.2, z3.mul_comm x.2 x.1]
    exact z3.neg_add (z3.mul x.1 x.2)

/-- **q3rq-2b: 共役は乗法的** (xy)̄ = x̄·ȳ。 -/
theorem q3rq_conj_mul (x y : q3rqCar) :
    q3rqConj (q3rqMul x y) = q3rqMul (q3rqConj x) (q3rqConj y) := by
  apply q3rq_ext
  · show z3.add (z3.mul x.1 y.1) (z3.mul q3rqD (z3.mul x.2 y.2))
        = z3.add (z3.mul x.1 y.1)
            (z3.mul q3rqD (z3.mul (z3.neg x.2) (z3.neg y.2)))
    rw [z3.neg_mul x.2 (z3.neg y.2), z3.mul_neg x.2 y.2, z3.neg_neg]
  · show z3.neg (z3.add (z3.mul x.1 y.2) (z3.mul x.2 y.1))
        = z3.add (z3.mul x.1 (z3.neg y.2)) (z3.mul (z3.neg x.2) y.1)
    rw [z3.mul_neg x.1 y.2, z3.neg_mul x.2 y.1,
      z3.neg_add_dist (z3.mul x.1 y.2) (z3.mul x.2 y.1)]

/-- (v,0)·(w,0) = (vw, 0)（対角部分環の乗法）。 -/
theorem q3rq_pair_mul (v w : z3.carrier) :
    q3rqMul ((v, z3.zero) : q3rqCar) ((w, z3.zero) : q3rqCar)
      = ((z3.mul v w, z3.zero) : q3rqCar) := by
  apply q3rq_ext
  · show z3.add (z3.mul v w) (z3.mul q3rqD (z3.mul z3.zero z3.zero))
        = z3.mul v w
    rw [z3.mul_zero z3.zero, z3.mul_zero q3rqD, z3.add_zero (z3.mul v w)]
  · show z3.add (z3.mul v z3.zero) (z3.mul z3.zero w) = z3.zero
    rw [z3.mul_zero v, z3.zero_mul w, z3.add_zero z3.zero]

/-- **q3rq-2c（★ Brahmagupta）: N(x·y) = N(x)·N(y)** — 共役 ring-hom
    x·x̄=(N,0) と (xy)̄=x̄ȳ ・4 因子入替から。多項式恒等式の機械展開を回避。 -/
theorem q3rq_norm_mul (x y : q3rqCar) :
    q3rqNorm (q3rqMul x y) = z3.mul (q3rqNorm x) (q3rqNorm y) := by
  have hchain : q3rqEn (q3rqMul x y)
      = q3rqMul (q3rqEn x) (q3rqEn y) := by
    rw [← q3rq_mul_conj (q3rqMul x y), q3rq_conj_mul x y,
      ← q3rq_mmmc x (q3rqConj x) y (q3rqConj y),
      q3rq_mul_conj x, q3rq_mul_conj y]
  have hfst : (q3rqEn (q3rqMul x y)).1
      = (q3rqMul (q3rqEn x) (q3rqEn y)).1 := congrArg Prod.fst hchain
  show q3rqNorm (q3rqMul x y) = z3.mul (q3rqNorm x) (q3rqNorm y)
  have hrhs : (q3rqMul (q3rqEn x) (q3rqEn y)).1
      = z3.mul (q3rqNorm x) (q3rqNorm y) := by
    show z3.add (z3.mul (q3rqNorm x) (q3rqNorm y))
        (z3.mul q3rqD (z3.mul z3.zero z3.zero))
      = z3.mul (q3rqNorm x) (q3rqNorm y)
    rw [z3.mul_zero z3.zero, z3.mul_zero q3rqD,
      z3.add_zero (z3.mul (q3rqNorm x) (q3rqNorm y))]
  exact hfst.trans hrhs

/-! ## q3rq-3: 単数群 U₂ = O_{L₂}^× と閉形式共役ノルム逆元 -/

/-- **q3rq-3a: 単数判定** — ノルムが実 ℤ₃ の単数（IsZpUnit 3）。 -/
def q3rqUnitMem (x : q3rqCar) : Prop := IsZpUnit 3 (q3rqNorm x)

/-- **q3rq-3b: 単数は積で閉じる**（norm_mul + isZpUnit_mul）。 -/
theorem q3rq_unit_mul {x y : q3rqCar}
    (hx : q3rqUnitMem x) (hy : q3rqUnitMem y) : q3rqUnitMem (q3rqMul x y) := by
  show IsZpUnit 3 (q3rqNorm (q3rqMul x y))
  rw [q3rq_norm_mul x y]
  exact isZpUnit_mul 3 isPrime_three hx hy

/-- **q3rq-3c（★ 閉形式共役ノルム逆元）** (a,b)⁻¹ = (a·N⁻¹, (−b)·N⁻¹)、
    N⁻¹ = zpUnitInv 3 (norm)（Fermat＋幾何級数・choice-free）。体エンジン不使用——
    A2 恒久限定（ℚ₃ に IUTField なし）を正面回避せず、単数のみに閉じた逆元で迂回。 -/
def q3rqInv (x : q3rqCar) (hx : q3rqUnitMem x) : q3rqCar :=
  ((z3.mul x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
    z3.mul (z3.neg x.2) (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)) : q3rqCar)

/-- N = a²+3b² の別表記（q3rqNorm の展開）を単数逆元へ橋渡し。 -/
theorem q3rq_norm_val_eq (x : q3rqCar) :
    q3rqNorm x = z3.add (z3.mul x.1 x.1)
      (z3.neg (z3.mul q3rqD (z3.mul x.2 x.2))) := rfl

/-- **q3rq-3d（★）: 逆元性** (a,b)⁻¹·(a,b) = 1
    — 第 1 成分 = (a²−Db²)·N⁻¹ = N·N⁻¹ = 1、第 2 成分 = 0。 -/
theorem q3rq_inv_mul (x : q3rqCar) (hx : q3rqUnitMem x) :
    q3rqMul (q3rqInv x hx) x = q3rqOne := by
  have hNinv : z3.mul (q3rqNorm x) (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)
      = z3.one := by
    rw [z3.mul_comm (q3rqNorm x) (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)]
    exact zpUnitInv_mul 3 isPrime_three (q3rqNorm x) hx
  apply q3rq_ext
  · show z3.add
          (z3.mul (z3.mul x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)) x.1)
          (z3.mul q3rqD
            (z3.mul (z3.mul (z3.neg x.2)
              (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)) x.2))
        = z3.one
    rw [z3.mul_comm (z3.mul x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)) x.1,
      ← z3.mul_assoc x.1 x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
      z3.mul_comm (z3.mul (z3.neg x.2)
          (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)) x.2,
      ← z3.mul_assoc x.2 (z3.neg x.2)
          (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
      z3.mul_neg x.2 x.2,
      z3.neg_mul (z3.mul x.2 x.2) (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
      z3.mul_neg q3rqD
        (z3.mul (z3.mul x.2 x.2) (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)),
      ← z3.mul_assoc q3rqD (z3.mul x.2 x.2)
        (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
      ← z3.neg_mul (z3.mul q3rqD (z3.mul x.2 x.2))
        (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
      ← z3.right_distrib (z3.mul x.1 x.1)
        (z3.neg (z3.mul q3rqD (z3.mul x.2 x.2)))
        (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)]
    exact hNinv
  · show z3.add
          (z3.mul (z3.mul x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)) x.2)
          (z3.mul (z3.mul (z3.neg x.2)
            (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)) x.1)
        = z3.zero
    rw [z3.mul_comm (z3.mul x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)) x.2,
      ← z3.mul_assoc x.2 x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
      z3.mul_comm (z3.mul (z3.neg x.2)
          (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)) x.1,
      ← z3.mul_assoc x.1 (z3.neg x.2)
          (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
      z3.mul_neg x.1 x.2,
      z3.neg_mul (z3.mul x.1 x.2) (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
      z3.mul_comm x.2 x.1]
    exact z3.add_neg (z3.mul (z3.mul x.1 x.2)
      (zpUnitInv 3 isPrime_three (q3rqNorm x) hx))

/-- N(1) = 1（(1,0) のノルム = 1·1 − D·0·0 = 1）。 -/
theorem q3rq_norm_one : q3rqNorm q3rqOne = z3.one := by
  show z3.add (z3.mul z3.one z3.one)
      (z3.neg (z3.mul q3rqD (z3.mul z3.zero z3.zero))) = z3.one
  rw [z3.one_mul z3.one, z3.mul_zero z3.zero, z3.mul_zero q3rqD,
    z3.neg_zero, z3.add_zero z3.one]

/-- **1 = (1,0) は単数**。 -/
theorem q3rq_unit_one : q3rqUnitMem q3rqOne := by
  show IsZpUnit 3 (q3rqNorm q3rqOne)
  rw [q3rq_norm_one]
  exact ⟨1, rfl, not_dvd_one 3 (by omega)⟩

/-- **q3rq-3e: ノルムの逆元表示** N((a,b)⁻¹) = N(a,b)⁻¹
    — 逆元 (aN⁻¹, −bN⁻¹) のノルム = (a²−Db²)N⁻¹² = N·N⁻¹·N⁻¹ = N⁻¹。 -/
theorem q3rq_norm_inv (x : q3rqCar) (hx : q3rqUnitMem x) :
    q3rqNorm (q3rqInv x hx)
      = zpUnitInv 3 isPrime_three (q3rqNorm x) hx := by
  have hNinv : z3.mul (q3rqNorm x) (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)
      = z3.one := by
    rw [z3.mul_comm (q3rqNorm x) (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)]
    exact zpUnitInv_mul 3 isPrime_three (q3rqNorm x) hx
  -- N(inv) = a²N⁻¹² − D b² N⁻¹² = (a²−Db²)·N⁻¹·N⁻¹ = (N·N⁻¹)·N⁻¹ = N⁻¹
  show z3.add
      (z3.mul (z3.mul x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx))
        (z3.mul x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)))
      (z3.neg (z3.mul q3rqD
        (z3.mul (z3.mul (z3.neg x.2) (zpUnitInv 3 isPrime_three (q3rqNorm x) hx))
          (z3.mul (z3.neg x.2)
            (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)))))
    = zpUnitInv 3 isPrime_three (q3rqNorm x) hx
  rw [z3.mul_mul_mul_comm x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)
      x.1 (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
    z3.mul_mul_mul_comm (z3.neg x.2)
      (zpUnitInv 3 isPrime_three (q3rqNorm x) hx) (z3.neg x.2)
      (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
    z3.neg_mul x.2 (z3.neg x.2), z3.mul_neg x.2 x.2, z3.neg_neg,
    ← z3.mul_assoc q3rqD (z3.mul x.2 x.2)
      (z3.mul (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)
        (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)),
    ← z3.neg_mul (z3.mul q3rqD (z3.mul x.2 x.2))
      (z3.mul (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)
        (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)),
    ← z3.right_distrib (z3.mul x.1 x.1)
      (z3.neg (z3.mul q3rqD (z3.mul x.2 x.2)))
      (z3.mul (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)
        (zpUnitInv 3 isPrime_three (q3rqNorm x) hx))]
  show z3.mul (q3rqNorm x)
      (z3.mul (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)
        (zpUnitInv 3 isPrime_three (q3rqNorm x) hx))
    = zpUnitInv 3 isPrime_three (q3rqNorm x) hx
  rw [← z3.mul_assoc (q3rqNorm x)
      (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)
      (zpUnitInv 3 isPrime_three (q3rqNorm x) hx),
    hNinv, z3.one_mul (zpUnitInv 3 isPrime_three (q3rqNorm x) hx)]

/-- **逆元は単数**（N(inv)=N⁻¹ は単数）。 -/
theorem q3rq_unit_inv (x : q3rqCar) (hx : q3rqUnitMem x) :
    q3rqUnitMem (q3rqInv x hx) := by
  show IsZpUnit 3 (q3rqNorm (q3rqInv x hx))
  rw [q3rq_norm_inv x hx]
  exact isZpUnit_inv 3 isPrime_three (q3rqNorm x) hx

/-- **q3rq-4a（★）: 単数群 U₂ = O_{L₂}^× : Grp** — 群法則は全て環公理と
    q3rq_inv_mul に帰着（アーベル群）。 -/
def q3rqU : Grp where
  carrier := { x : q3rqCar // q3rqUnitMem x }
  mul := fun x y => ⟨q3rqMul x.val y.val, q3rq_unit_mul x.property y.property⟩
  one := ⟨q3rqOne, q3rq_unit_one⟩
  inv := fun x => ⟨q3rqInv x.val x.property, q3rq_unit_inv x.val x.property⟩
  mul_assoc := fun x y z =>
    Subtype.ext (q3rqRing.mul_assoc x.val y.val z.val)
  one_mul := fun x => Subtype.ext (q3rqRing.one_mul x.val)
  inv_mul := fun x => Subtype.ext (q3rq_inv_mul x.val x.property)

/-- U₂ はアーベル群。 -/
theorem q3rqU_comm (x y : q3rqU.carrier) :
    q3rqU.mul x y = q3rqU.mul y x :=
  Subtype.ext (q3rqRing.mul_comm x.val y.val)

/-- **q3rq-4b（★）: L₂^× = ℤ × U₂** — 付値部 ℤ（v_λ）× 単数部 U₂。
    QpUnits と完全並行の実群提示。 -/
def q3rqLx : Grp := prodGrp intGrp q3rqU

/-! ## q3rq-5': 実 ζ₃ = (−1+√−3)/2 と μ₃ ⊂ U₂ -/

/-- z3 の 1 ≠ 0（レベル 1 剰余 1 ≠ 0 mod 3）。 -/
theorem q3rq_z3_one_ne_zero : z3.one ≠ z3.zero := by
  intro h
  have hlev : (z3.one).val 1 = (z3.zero).val 1 := congrArg (fun z => z.val 1) h
  have hq : Quot.mk (modCong (3 ^ 1)).rel (1 : Int)
      = Quot.mk (modCong (3 ^ 1)).rel (0 : Int) := hlev
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (3 ^ 1)) hq
  rw [Nat.pow_one] at hk
  omega

/-- **q3rq-5c: h = 2⁻¹ ≠ 0**（2h=1 と 1≠0）。 -/
theorem q3rq_half_ne_zero : q3rqHalf ≠ z3.zero := by
  intro h
  have h1 : z3.mul q3rqTwoZ q3rqHalf = z3.mul q3rqTwoZ z3.zero := congrArg (z3.mul q3rqTwoZ) h
  rw [q3rq_two_half, z3.mul_zero q3rqTwoZ] at h1
  exact q3rq_z3_one_ne_zero h1

/-- −h ≠ 0。 -/
theorem q3rq_neg_half_ne_zero : z3.neg q3rqHalf ≠ z3.zero := by
  intro h
  have h1 : z3.neg (z3.neg q3rqHalf) = z3.neg z3.zero := congrArg z3.neg h
  rw [z3.neg_neg, z3.neg_zero] at h1
  exact q3rq_half_ne_zero h1

/-- **q3rq-6a（★★）: 実 ζ₃ = (−1+√−3)/2 = (−h, h)** — U₂ 内の実元。 -/
def q3rqZeta : q3rqCar := ((z3.neg q3rqHalf, q3rqHalf) : q3rqCar)

/-- h² の略記補題: 2·h² = h。 -/
theorem q3rq_two_hsq : z3.mul q3rqTwoZ (z3.mul q3rqHalf q3rqHalf) = q3rqHalf := by
  rw [← z3.mul_assoc q3rqTwoZ q3rqHalf q3rqHalf, q3rq_two_half, z3.one_mul q3rqHalf]

/-- h² + h² = h。 -/
theorem q3rq_hsq_add_hsq :
    z3.add (z3.mul q3rqHalf q3rqHalf) (z3.mul q3rqHalf q3rqHalf) = q3rqHalf := by
  have h2 : z3.mul q3rqTwoZ (z3.mul q3rqHalf q3rqHalf)
      = z3.add (z3.mul q3rqHalf q3rqHalf) (z3.mul q3rqHalf q3rqHalf) := by
    show z3.mul (z3.add z3.one z3.one) (z3.mul q3rqHalf q3rqHalf)
      = z3.add (z3.mul q3rqHalf q3rqHalf) (z3.mul q3rqHalf q3rqHalf)
    rw [z3.right_distrib z3.one z3.one (z3.mul q3rqHalf q3rqHalf),
      z3.one_mul (z3.mul q3rqHalf q3rqHalf)]
  rw [← h2, q3rq_two_hsq]

/-- h + h = 1。 -/
theorem q3rq_half_add_half : z3.add q3rqHalf q3rqHalf = z3.one := by
  have h2 : z3.mul q3rqTwoZ q3rqHalf = z3.add q3rqHalf q3rqHalf := by
    show z3.mul (z3.add z3.one z3.one) q3rqHalf = z3.add q3rqHalf q3rqHalf
    rw [z3.right_distrib z3.one z3.one q3rqHalf, z3.one_mul q3rqHalf]
  rw [← h2, q3rq_two_half]

/-- 3·h² = h + h²（three = 2+1）。 -/
theorem q3rq_three_hsq :
    z3.mul q3rqThree (z3.mul q3rqHalf q3rqHalf)
      = z3.add q3rqHalf (z3.mul q3rqHalf q3rqHalf) := by
  show z3.mul (z3.add q3rqTwoZ z3.one) (z3.mul q3rqHalf q3rqHalf)
    = z3.add q3rqHalf (z3.mul q3rqHalf q3rqHalf)
  rw [z3.right_distrib q3rqTwoZ z3.one (z3.mul q3rqHalf q3rqHalf),
    z3.one_mul (z3.mul q3rqHalf q3rqHalf), q3rq_two_hsq]

/-- **q3rq-6b: ζ₃² = (−h, −h)**（本物のガウス乗法）。 -/
theorem q3rq_zeta_sq_eq :
    q3rqMul q3rqZeta q3rqZeta = ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar) := by
  apply q3rq_ext
  · show z3.add (z3.mul (z3.neg q3rqHalf) (z3.neg q3rqHalf))
          (z3.mul q3rqD (z3.mul q3rqHalf q3rqHalf))
        = z3.neg q3rqHalf
    rw [z3.neg_mul q3rqHalf (z3.neg q3rqHalf), z3.mul_neg q3rqHalf q3rqHalf,
      z3.neg_neg,
      q3rq_D_eq, z3.neg_mul q3rqThree (z3.mul q3rqHalf q3rqHalf), q3rq_three_hsq,
      z3.neg_add_dist q3rqHalf (z3.mul q3rqHalf q3rqHalf),
      ← z3.add_assoc (z3.mul q3rqHalf q3rqHalf) (z3.neg q3rqHalf)
        (z3.neg (z3.mul q3rqHalf q3rqHalf)),
      z3.add_comm (z3.mul q3rqHalf q3rqHalf) (z3.neg q3rqHalf),
      z3.add_assoc (z3.neg q3rqHalf) (z3.mul q3rqHalf q3rqHalf)
        (z3.neg (z3.mul q3rqHalf q3rqHalf)),
      z3.add_neg (z3.mul q3rqHalf q3rqHalf),
      z3.add_zero (z3.neg q3rqHalf)]
  · show z3.add (z3.mul (z3.neg q3rqHalf) q3rqHalf)
          (z3.mul q3rqHalf (z3.neg q3rqHalf))
        = z3.neg q3rqHalf
    rw [z3.neg_mul q3rqHalf q3rqHalf, z3.mul_neg q3rqHalf q3rqHalf,
      ← z3.neg_add_dist (z3.mul q3rqHalf q3rqHalf) (z3.mul q3rqHalf q3rqHalf),
      q3rq_hsq_add_hsq]

/-- **q3rq-6c: N(ζ₃) = 1 ⟹ ζ₃ ∈ U₂**（N = h²+3h² = 4h² = 1）。 -/
theorem q3rq_zeta_norm : q3rqNorm q3rqZeta = z3.one := by
  show z3.add (z3.mul (z3.neg q3rqHalf) (z3.neg q3rqHalf))
      (z3.neg (z3.mul q3rqD (z3.mul q3rqHalf q3rqHalf))) = z3.one
  rw [z3.neg_mul q3rqHalf (z3.neg q3rqHalf), z3.mul_neg q3rqHalf q3rqHalf,
    z3.neg_neg,
    q3rq_D_eq, z3.neg_mul q3rqThree (z3.mul q3rqHalf q3rqHalf), z3.neg_neg,
    q3rq_three_hsq,
    ← z3.add_assoc (z3.mul q3rqHalf q3rqHalf) q3rqHalf
      (z3.mul q3rqHalf q3rqHalf),
    z3.add_comm (z3.mul q3rqHalf q3rqHalf) q3rqHalf,
    z3.add_assoc q3rqHalf (z3.mul q3rqHalf q3rqHalf)
      (z3.mul q3rqHalf q3rqHalf),
    q3rq_hsq_add_hsq, q3rq_half_add_half]

theorem q3rq_zeta_unit : q3rqUnitMem q3rqZeta := by
  show IsZpUnit 3 (q3rqNorm q3rqZeta)
  rw [q3rq_zeta_norm]
  exact ⟨1, rfl, not_dvd_one 3 (by omega)⟩

/-- **q3rq-6d（★★★）: ζ₃³ = 1** — ζ₃²·ζ₃ = 1（本物のガウス乗法）。
    第 1 成分 = h² + 3h² = 4h² = (2h)² = 1、第 2 成分 = 0。 -/
theorem q3rq_zeta_cube :
    q3rqMul (q3rqMul q3rqZeta q3rqZeta) q3rqZeta = q3rqOne := by
  rw [q3rq_zeta_sq_eq]
  apply q3rq_ext
  · show z3.add (z3.mul (z3.neg q3rqHalf) (z3.neg q3rqHalf))
          (z3.mul q3rqD (z3.mul (z3.neg q3rqHalf) q3rqHalf))
        = z3.one
    rw [z3.neg_mul q3rqHalf (z3.neg q3rqHalf), z3.mul_neg q3rqHalf q3rqHalf,
      z3.neg_neg,
      z3.neg_mul q3rqHalf q3rqHalf,
      z3.mul_neg q3rqD (z3.mul q3rqHalf q3rqHalf),
      q3rq_D_eq, z3.neg_mul q3rqThree (z3.mul q3rqHalf q3rqHalf), z3.neg_neg,
      q3rq_three_hsq,
      ← z3.add_assoc (z3.mul q3rqHalf q3rqHalf) q3rqHalf
        (z3.mul q3rqHalf q3rqHalf),
      z3.add_comm (z3.mul q3rqHalf q3rqHalf) q3rqHalf,
      z3.add_assoc q3rqHalf (z3.mul q3rqHalf q3rqHalf)
        (z3.mul q3rqHalf q3rqHalf),
      q3rq_hsq_add_hsq, q3rq_half_add_half]
  · show z3.add (z3.mul (z3.neg q3rqHalf) q3rqHalf)
          (z3.mul (z3.neg q3rqHalf) (z3.neg q3rqHalf))
        = z3.zero
    rw [z3.neg_mul q3rqHalf q3rqHalf,
      z3.neg_mul q3rqHalf (z3.neg q3rqHalf), z3.mul_neg q3rqHalf q3rqHalf,
      z3.neg_neg,
      z3.add_comm (z3.neg (z3.mul q3rqHalf q3rqHalf))
        (z3.mul q3rqHalf q3rqHalf),
      z3.add_neg (z3.mul q3rqHalf q3rqHalf)]

/-- **q3rq-6e: ζ₃ ≠ 1**（第 2 成分 h ≠ 0）。 -/
theorem q3rq_zeta_ne_one : q3rqZeta ≠ q3rqOne := by
  intro h
  have h2 : q3rqHalf = z3.zero := congrArg (fun p : q3rqCar => p.2) h
  exact q3rq_half_ne_zero h2

/-- **q3rq-6f: ζ₃² ≠ 1**（位数ちょうど 3。第 2 成分 −h ≠ 0）。 -/
theorem q3rq_zeta_sq_ne_one : q3rqMul q3rqZeta q3rqZeta ≠ q3rqOne := by
  rw [q3rq_zeta_sq_eq]
  intro h
  have h2 : z3.neg q3rqHalf = z3.zero := congrArg (fun p : q3rqCar => p.2) h
  exact q3rq_neg_half_ne_zero h2

/-! ## q3rq-6'': 実円分群 μ₃ = {1, ζ₃, ζ₃²} ⊂ U₂ -/

/-- ζ₃² の略記。 -/
def q3rqZetaSq : q3rqCar := q3rqMul q3rqZeta q3rqZeta

/-- 1·x = x。 -/
theorem q3rq_one_mul (a : q3rqCar) : q3rqMul q3rqOne a = a := q3rqRing.one_mul a

/-- x·1 = x。 -/
theorem q3rq_mul_one (a : q3rqCar) : q3rqMul a q3rqOne = a := by
  show q3rqRing.mul a q3rqOne = a
  rw [q3rqRing.mul_comm a q3rqOne]; exact q3rqRing.one_mul a

/-- ζ₃·ζ₃² = 1（可換 + ζ₃³=1）。 -/
theorem q3rq_zeta_mul_zetaSq : q3rqMul q3rqZeta q3rqZetaSq = q3rqOne := by
  show q3rqRing.mul q3rqZeta (q3rqMul q3rqZeta q3rqZeta) = q3rqOne
  rw [q3rqRing.mul_comm q3rqZeta (q3rqMul q3rqZeta q3rqZeta)]
  exact q3rq_zeta_cube

/-- ζ₃²·ζ₃² = ζ₃（= ζ₃⁴、本物の乗法計算）。第 1 成分 = h²+3h² = neg h...
    実際は (−h,−h)(−h,−h) の計算で ζ₃ = (−h,h) に戻る。 -/
theorem q3rq_zetaSq_mul_zetaSq : q3rqMul q3rqZetaSq q3rqZetaSq = q3rqZeta := by
  show q3rqMul (q3rqMul q3rqZeta q3rqZeta) (q3rqMul q3rqZeta q3rqZeta) = q3rqZeta
  rw [q3rq_zeta_sq_eq]
  apply q3rq_ext
  · show z3.add (z3.mul (z3.neg q3rqHalf) (z3.neg q3rqHalf))
          (z3.mul q3rqD (z3.mul (z3.neg q3rqHalf) (z3.neg q3rqHalf)))
        = z3.neg q3rqHalf
    rw [z3.neg_mul q3rqHalf (z3.neg q3rqHalf), z3.mul_neg q3rqHalf q3rqHalf,
      z3.neg_neg,
      q3rq_D_eq, z3.neg_mul q3rqThree (z3.mul q3rqHalf q3rqHalf), q3rq_three_hsq,
      z3.neg_add_dist q3rqHalf (z3.mul q3rqHalf q3rqHalf),
      ← z3.add_assoc (z3.mul q3rqHalf q3rqHalf) (z3.neg q3rqHalf)
        (z3.neg (z3.mul q3rqHalf q3rqHalf)),
      z3.add_comm (z3.mul q3rqHalf q3rqHalf) (z3.neg q3rqHalf),
      z3.add_assoc (z3.neg q3rqHalf) (z3.mul q3rqHalf q3rqHalf)
        (z3.neg (z3.mul q3rqHalf q3rqHalf)),
      z3.add_neg (z3.mul q3rqHalf q3rqHalf),
      z3.add_zero (z3.neg q3rqHalf)]
  · show z3.add (z3.mul (z3.neg q3rqHalf) (z3.neg q3rqHalf))
          (z3.mul (z3.neg q3rqHalf) (z3.neg q3rqHalf))
        = q3rqHalf
    rw [z3.neg_mul q3rqHalf (z3.neg q3rqHalf), z3.mul_neg q3rqHalf q3rqHalf,
      z3.neg_neg, q3rq_hsq_add_hsq]

/-- **q3rq-6''a: 実円分群 μ₃** = {1, ζ₃, ζ₃²}。 -/
def q3rqMu3 (x : q3rqCar) : Prop :=
  x = q3rqOne ∨ x = q3rqZeta ∨ x = q3rqZetaSq

/-- **q3rq-6''b（★）: μ₃ は乗法で閉じる**（実局所環内 μ₃ ⊂ U₂）— 9 通りの積を
    単位法則と ζ₃³=1 で 1・ζ₃・ζ₃² に帰着。 -/
theorem q3rq_mu3_closed (x y : q3rqCar) (hx : q3rqMu3 x) (hy : q3rqMu3 y) :
    q3rqMu3 (q3rqMul x y) := by
  obtain hx | hx | hx := hx
  · obtain hy | hy | hy := hy
    · rw [hx, hy]; exact Or.inl (q3rq_one_mul q3rqOne)
    · rw [hx, hy]; exact Or.inr (Or.inl (q3rq_one_mul q3rqZeta))
    · rw [hx, hy]; exact Or.inr (Or.inr (q3rq_one_mul q3rqZetaSq))
  · obtain hy | hy | hy := hy
    · rw [hx, hy]; exact Or.inr (Or.inl (q3rq_mul_one q3rqZeta))
    · rw [hx, hy]; exact Or.inr (Or.inr rfl)
    · rw [hx, hy]; exact Or.inl q3rq_zeta_mul_zetaSq
  · obtain hy | hy | hy := hy
    · rw [hx, hy]; exact Or.inr (Or.inr (q3rq_mul_one q3rqZetaSq))
    · rw [hx, hy]; exact Or.inl q3rq_zeta_cube
    · rw [hx, hy]; exact Or.inr (Or.inl q3rq_zetaSq_mul_zetaSq)

/-! ## q3rq-7: λ = √−3・λ² = −3（分岐 e=2 の実現）・3 と 3³ -/

/-- **q3rq-7a: 一様化子 λ = √−3 = (0,1)**。 -/
def q3rqLambda : q3rqCar := ((z3.zero, z3.one) : q3rqCar)

/-- 環元 3 = (3,0)。 -/
def q3rqThreeElt : q3rqCar := ((q3rqThree, z3.zero) : q3rqCar)

/-- **q3rq-7b（★）: λ² = (−3, 0)** — 分岐 e=2 の整数レベル実現。 -/
theorem q3rq_lambda_sq :
    q3rqMul q3rqLambda q3rqLambda = ((z3.neg q3rqThree, z3.zero) : q3rqCar) := by
  apply q3rq_ext
  · show z3.add (z3.mul z3.zero z3.zero) (z3.mul q3rqD (z3.mul z3.one z3.one))
        = z3.neg q3rqThree
    rw [z3.zero_mul z3.zero, z3.one_mul z3.one, z3.mul_one q3rqD,
      z3.zero_add q3rqD]
    exact q3rq_D_eq
  · show z3.add (z3.mul z3.zero z3.one) (z3.mul z3.one z3.zero) = z3.zero
    rw [z3.zero_mul z3.one, z3.mul_zero z3.one, z3.add_zero z3.zero]

/-- **q3rq-7c: 3 = −λ²**（e=2 の別表記・3=λ²·(−1)）。 -/
theorem q3rq_three_eq_neg_lambda_sq :
    q3rqThreeElt = q3rqNeg (q3rqMul q3rqLambda q3rqLambda) := by
  rw [q3rq_lambda_sq]
  apply q3rq_ext
  · show q3rqThree = z3.neg (z3.neg q3rqThree)
    rw [z3.neg_neg]
  · show z3.zero = z3.neg z3.zero
    rw [z3.neg_zero]

/-- **q3rq-7d: 3³ = (3³, 0)**（R2b の q = 27 = q3tQ 3 接続点。環元 3 の立方）。 -/
theorem q3rq_three_cube :
    q3rqMul (q3rqMul q3rqThreeElt q3rqThreeElt) q3rqThreeElt
      = ((z3.mul (z3.mul q3rqThree q3rqThree) q3rqThree, z3.zero) : q3rqCar) := by
  show q3rqMul (q3rqMul ((q3rqThree, z3.zero) : q3rqCar) ((q3rqThree, z3.zero) : q3rqCar))
      ((q3rqThree, z3.zero) : q3rqCar)
    = ((z3.mul (z3.mul q3rqThree q3rqThree) q3rqThree, z3.zero) : q3rqCar)
  rw [q3rq_pair_mul q3rqThree q3rqThree,
    q3rq_pair_mul (z3.mul q3rqThree q3rqThree) q3rqThree]

/-! ## q3rq-8: ℚ₃^× ↪ L₂^×（分岐指数 2） -/

/-- (v,0) の単数部への埋め込み — v が ℤ₃ の単数なら (v,0) ∈ U₂。 -/
theorem q3rq_pair_norm (v : z3.carrier) :
    q3rqNorm ((v, z3.zero) : q3rqCar) = z3.mul v v := by
  show z3.add (z3.mul v v) (z3.neg (z3.mul q3rqD (z3.mul z3.zero z3.zero)))
    = z3.mul v v
  rw [z3.mul_zero z3.zero, z3.mul_zero q3rqD, z3.neg_zero, z3.add_zero (z3.mul v v)]

theorem q3rq_pair_unit (v : z3.carrier) (hv : IsZpUnit 3 v) :
    q3rqUnitMem ((v, z3.zero) : q3rqCar) := by
  show IsZpUnit 3 (q3rqNorm ((v, z3.zero) : q3rqCar))
  rw [q3rq_pair_norm v]
  exact isZpUnit_mul 3 isPrime_three hv hv

/-- **単数の埋め込み** φ: ℤ₃^× → U₂, u ↦ (u, 0)。 -/
def q3rqPhi (u : (zpUnits 3 isPrime_three).carrier) : q3rqU.carrier :=
  ⟨((u.val, z3.zero) : q3rqCar), q3rq_pair_unit u.val u.property⟩

/-- φ は乗法的。 -/
theorem q3rq_phi_mul (u v : (zpUnits 3 isPrime_three).carrier) :
    q3rqPhi ((zpUnits 3 isPrime_three).mul u v)
      = q3rqU.mul (q3rqPhi u) (q3rqPhi v) := by
  apply Subtype.ext
  show ((z3.mul u.val v.val, z3.zero) : q3rqCar)
    = q3rqMul ((u.val, z3.zero) : q3rqCar) ((v.val, z3.zero) : q3rqCar)
  rw [q3rq_pair_mul u.val v.val]

/-- φ は単射。 -/
theorem q3rq_phi_inj (u v : (zpUnits 3 isPrime_three).carrier)
    (h : q3rqPhi u = q3rqPhi v) : u = v := by
  have hval : ((u.val, z3.zero) : q3rqCar) = ((v.val, z3.zero) : q3rqCar) :=
    congrArg Subtype.val h
  have h1 : u.val = v.val := congrArg (fun p : q3rqCar => p.1) hval
  exact Subtype.ext h1

/-- **q3rq-8a（★）: ℚ₃^× ↪ L₂^×** (j,u) ↦ (2j, φ u)。第 1 成分（λ-付値）は
    3-付値の 2 倍——分岐指数 2 の実現。 -/
def q3rqEmbed : Hom q3tGrp q3rqLx where
  map := fun x => ((2 * x.1, q3rqPhi x.2) : Int × q3rqU.carrier)
  map_mul := by
    intro x y
    show ((2 * intGrp.mul x.1 y.1, q3rqPhi ((zpUnits 3 isPrime_three).mul x.2 y.2))
        : Int × q3rqU.carrier)
      = ((intGrp.mul (2 * x.1) (2 * y.1),
          q3rqU.mul (q3rqPhi x.2) (q3rqPhi y.2)) : Int × q3rqU.carrier)
    have h1 : 2 * intGrp.mul x.1 y.1 = intGrp.mul (2 * x.1) (2 * y.1) := by
      show (2 : Int) * (x.1 + y.1) = (2 * x.1) + (2 * y.1)
      rw [Int.mul_add]
    rw [h1, q3rq_phi_mul x.2 y.2]

/-- **q3rq-8b（★）: 埋め込みは単射**。 -/
theorem q3rq_embed_inj : q3rqEmbed.Injective := by
  intro x y h
  have h1 : (2 * x.1, q3rqPhi x.2) = (2 * y.1, q3rqPhi y.2) := h
  have hfst : (2 : Int) * x.1 = 2 * y.1 := congrArg Prod.fst h1
  have key : ∀ a b : Int, 2 * a = 2 * b → a = b := fun a b h => by omega
  have hx1 : x.1 = y.1 := key x.1 y.1 hfst
  have hsnd : q3rqPhi x.2 = q3rqPhi y.2 := congrArg Prod.snd h1
  have hx2 : x.2 = y.2 := q3rq_phi_inj x.2 y.2 hsnd
  show x = y
  have : (x.1, x.2) = (y.1, y.2) := by rw [hx1, hx2]
  exact this

/-- **q3rq-8c（★）: 分岐指数 2** — v_λ(embed x) = 2·v₃(x)。第 1 成分（λ-付値）が
    ℚ₃^× の付値の 2 倍。ℚ₃(ζ₃)/ℚ₃ の分岐指数 e=2 の群提示レベルの実定理。 -/
theorem q3rq_ramification (x : q3tGrp.carrier) :
    (q3rqEmbed.map x).1 = 2 * x.1 := rfl

/-! ## q3rq-9: capstone -/

/-- **q3rq-9a: 実分岐 2 次局所拡大データ** — 実 O_{L₂}=ℤ₃[√−3]（可換環）・
    実単数群 U₂（閉形式逆元）・実 ζ₃（位数 3・μ₃⊂U₂）・分岐 e=2（3=−λ²）・
    ℚ₃^×↪L₂^×（分岐指数 2）を束ねる。 -/
structure Q3RamQuadData where
  /-- 単数群 U₂ = O_{L₂}^×。 -/
  units : Grp
  /-- L₂^× = ℤ × U₂。 -/
  lstar : Grp
  /-- 実 ζ₃ ∈ O_{L₂}。 -/
  zeta : q3rqCar
  /-- ζ₃³ = 1。 -/
  zeta_cube : q3rqMul (q3rqMul zeta zeta) zeta = q3rqOne
  /-- ζ₃ ≠ 1。 -/
  zeta_ne_one : zeta ≠ q3rqOne
  /-- ζ₃² ≠ 1（位数ちょうど 3）。 -/
  zeta_sq_ne_one : q3rqMul zeta zeta ≠ q3rqOne
  /-- ζ₃ は単数。 -/
  zeta_unit : q3rqUnitMem zeta
  /-- μ₃ は乗法で閉じる。 -/
  mu3_closed : ∀ a b, q3rqMu3 a → q3rqMu3 b → q3rqMu3 (q3rqMul a b)
  /-- λ² = −3（分岐 e=2）。 -/
  lambda_sq : q3rqMul q3rqLambda q3rqLambda = ((z3.neg q3rqThree, z3.zero) : q3rqCar)
  /-- ℚ₃^× ↪ L₂^× は単射。 -/
  embed_inj : q3rqEmbed.Injective
  /-- 分岐指数 2。 -/
  ramified : ∀ x : q3tGrp.carrier, (q3rqEmbed.map x).1 = 2 * x.1

/-- **q3rq-9b: 見出し実例** — 実 ℚ₃(ζ₃) = ℚ₃(√−3)。 -/
def q3rqData : Q3RamQuadData where
  units := q3rqU
  lstar := q3rqLx
  zeta := q3rqZeta
  zeta_cube := q3rq_zeta_cube
  zeta_ne_one := q3rq_zeta_ne_one
  zeta_sq_ne_one := q3rq_zeta_sq_ne_one
  zeta_unit := q3rq_zeta_unit
  mu3_closed := q3rq_mu3_closed
  lambda_sq := q3rq_lambda_sq
  embed_inj := q3rq_embed_inj
  ramified := q3rq_ramification

/-- **q3rq-9c: 実分岐 2 次局所拡大の存在**（実 ℤ₃ 上・単数群＋実 ζ₃＋e=2）。 -/
theorem q3rq_exists : Nonempty Q3RamQuadData := ⟨q3rqData⟩

end IUT
