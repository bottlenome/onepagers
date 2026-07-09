/-
  IUT/CyclotomicFieldQ3.lean — CQ3F: 実円分体 ℚ(ζ_3) = ℚ(√−3) と 1 の 3 乗根群 μ_3

  ── 主要成果の分類: **[実]**（本物の二次円分体 ℚ(√−3) と、その中に実際に
  構成した 1 の原始 3 乗根 ζ_3 と実円分群 μ_3 = {1, ζ_3, ζ_3²}）。

  complete_pct 影響: **E6「実 μ_l ⊂ 実体」を本物で埋める本物建設**。既存 μ_l
  （`MuLSubgroup`）は Zp p 内の Teichmüller だが、こちらは**実円分体の中の
  実 3 乗根群**。ガウス体 ℚ(i)=ℚ(ζ_4)（`GaussianRationalField`）の実 ℚ×ℚ 技法を
  そのまま √−3 版へ移し、
  * carrier は**実際の ℚ×ℚ**（(a,b) ↔ a + b√−3、Bool/Fin/ラベルの身代わりなし）、
  * 乗法は √−3² = −3 を実現する本物のガウス型乗法
    (a,b)·(c,d) = (ac + (−3)bd, ad + bc)（−3 = cq3D は本物の有理数）、
  * 逆元は**実ノルム** N = a² + 3b² による本物のガウス逆元
    (a,b)⁻¹ = (a·N⁻¹, (−b)·N⁻¹)、
  * 体公理 `mul_inv_cancel` は ℚ の**形式的実性**（a²+3b² = 0 ⟹ a = b = 0、
    平方非負 + 3 ≥ 0 + 整域性）から本物に証明、
  * **本丸**: ζ_3 = (−1/2, 1/2) = (−1+√−3)/2 を carrier 内に実構成し、
    `cq3_zeta_cube_one`（ζ_3³ = 1、本物のガウス乗法で計算）・
    `cq3_zeta_ne_one`（ζ_3 ≠ 1）・`cq3_zeta_sq_ne_one`（ζ_3² ≠ 1、位数ちょうど 3）、
  * `cq3Mu3 = {1, ζ_3, ζ_3²}` が乗法で閉じる `cq3_mu3_closed`（実円分群 μ_3 ⊂ 実体）
  を完全証明する。

  * cq3-0 定数 cq3D = −3 / cq3Three = 3 と符号・順序・非零（代表計算）
  * cq3-1 台とガウス演算（実 ℚ×ℚ、cq3D = −3 による乗法）
  * cq3-2 cq3Ring — ℚ(√−3) は可換環（結合・可換・分配を ℚ の環公理から）
  * cq3-3 cq3_normsq_ne_zero — 形式的実性 (a,b) ≠ (0,0) ⟹ a²+3b² ≠ 0
  * cq3-4 cq3Field : IUTField — 本物の体（実ガウス逆元・mul_inv_cancel 本物）
  * cq3-5 ζ_3 の実構成と ζ_3³ = 1・ζ_3 ≠ 1・ζ_3² ≠ 1（位数ちょうど 3）
  * cq3-6 μ_3 = {1, ζ_3, ζ_3²} の乗法閉性 cq3_mu3_closed
  * cq3-7 capstone cq3_exists（原始 3 乗根を持つ本物の体が存在）

  正直な限定（何が本物で何が未達か）:
  - **本物**: 台 ℚ×ℚ は実際の有理数対。逆元は実ガウス逆元、体公理・環公理・
    形式的実性・ζ_3³ = 1・位数 3・μ_3 の閉性の全証明は sorry 皆無・新規
    Classical.choice 皆無（propext/Quot.sound のみ）。ζ_3 = (−1/2,1/2) は
    carrier 内の実元で、ζ_3³ = 1 は代表 ℚ 上の本物の乗法計算で確定。
  - **未達（正直申告）**: (1) μ_3 ≅ ℤ/3（群同型・位数ちょうど 3 の群論的確定）は
    「ζ_3 ≠ 1 かつ ζ_3² ≠ 1 かつ ζ_3³ = 1」までで、抽象巡回群との同型射は別切片。
    (2) ℚ(ζ_3)/ℚ の Galois 群・分岐・完全な円分理論は未形式化（本ファイルは
    体と μ_3 の代数的実構成のみ）。(3) 商 ℚ のゼロ判定選言は排中律を要するため
    非零性は否定形/仮説形で扱う（形式的実性は二重否定経由で構成的に証明）。

  選択公理不使用（新規 choice なし）。禁止タクティク（simp/decide/ring 等）不使用。
-/
import IUT.GaussianRationalField

namespace IUT

/-! ## cq3-0: 有理数定数 −3 と 3（代表計算） -/

/-- 有理数 −3（√−3² = −3 を実現する乗数）。 -/
def cq3D : QRat := Quot.mk ratRel ⟨-3, 1, by omega⟩

/-- 有理数 3（ノルム N = a² + 3b² の係数）。 -/
def cq3Three : QRat := Quot.mk ratRel ⟨3, 1, by omega⟩

/-- **−(−3) = 3**（代表の Quot.sound）。 -/
theorem cq3_neg_D : ratRing.neg cq3D = cq3Three := by
  apply Quot.sound
  show -(-3) * 1 = 3 * 1
  omega

/-- **0 ≤ 3**（代表の prLe）。 -/
theorem cq3_three_nonneg : qLe ratRing.zero cq3Three := by
  show (0 : Int) * 1 ≤ 3 * 1
  omega

/-- **3 ≠ 0**（quot_exact で分離、Int の 3 ≠ 0）。 -/
theorem cq3_three_ne_zero : cq3Three ≠ ratRing.zero := by
  intro h
  have h2 : (3 : Int) * 1 = 0 * 1 := quot_exact_rat h
  omega

/-! ## cq3-1: 台とガウス演算 — 実 ℚ×ℚ（(a,b) は a + b√−3） -/

/-- **cq3-1a: ℚ(√−3) の台** — 実際の ℚ×ℚ（第 1 成分 = 有理部、第 2 成分 = √−3 部）。 -/
def cq3Carrier : Type := ratIUTField.carrier × ratIUTField.carrier

/-- 対の外延性。 -/
theorem cq3_ext : ∀ {x y : cq3Carrier}, x.1 = y.1 → x.2 = y.2 → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

/-- 加法 (a,b)+(c,d) = (a+c, b+d)。 -/
def cq3Add (x y : cq3Carrier) : cq3Carrier :=
  ((ratRing.add x.1 y.1, ratRing.add x.2 y.2) : cq3Carrier)

/-- 反元 −(a,b) = (−a,−b)。 -/
def cq3Neg (x : cq3Carrier) : cq3Carrier :=
  ((ratRing.neg x.1, ratRing.neg x.2) : cq3Carrier)

/-- 0 = (0,0)。 -/
def cq3Zero : cq3Carrier := ((ratRing.zero, ratRing.zero) : cq3Carrier)

/-- 1 = (1,0)。 -/
def cq3One : cq3Carrier := ((ratRing.one, ratRing.zero) : cq3Carrier)

/-- **ガウス型乗法** (a,b)·(c,d) = (ac + D·bd, ad + bc)、D = −3
    （√−3² = −3 の実現）。 -/
def cq3Mul (x y : cq3Carrier) : cq3Carrier :=
  ((ratRing.add (ratRing.mul x.1 y.1) (ratRing.mul cq3D (ratRing.mul x.2 y.2)),
    ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)) : cq3Carrier)

/-- **実ノルム** N(a,b) = a² − D·b² = a² + 3b²（ℚ に値を取る）。 -/
def cq3Norm (x : cq3Carrier) : QRat :=
  ratRing.add (ratRing.mul x.1 x.1)
    (ratRing.neg (ratRing.mul cq3D (ratRing.mul x.2 x.2)))

/-- **実ガウス逆元** (a,b)⁻¹ = (a·N⁻¹, (−b)·N⁻¹)（N⁻¹ は M115F の本物の
    ℚ 逆元 qInv）。 -/
def cq3Inv (x : cq3Carrier) : cq3Carrier :=
  ((ratRing.mul x.1 (qInv (cq3Norm x)),
    ratRing.mul (ratRing.neg x.2) (qInv (cq3Norm x))) : cq3Carrier)

/-! ## cq3-2: ℚ(√−3) は可換環 -/

/-- **cq3-2: ℚ(√−3) の可換環構造** — 加法は成分ごと、乗法は cq3D = −3 による
    ガウス則。結合・可換・分配は ℚ の環公理からの明示計算。 -/
def cq3Ring : CRing where
  carrier := cq3Carrier
  add := cq3Add
  zero := cq3Zero
  neg := cq3Neg
  mul := cq3Mul
  one := cq3One
  add_assoc := fun x y z =>
    cq3_ext (ratRing.add_assoc x.1 y.1 z.1) (ratRing.add_assoc x.2 y.2 z.2)
  zero_add := fun x =>
    cq3_ext (ratRing.zero_add x.1) (ratRing.zero_add x.2)
  neg_add := fun x =>
    cq3_ext (ratRing.neg_add x.1) (ratRing.neg_add x.2)
  add_comm := fun x y =>
    cq3_ext (ratRing.add_comm x.1 y.1) (ratRing.add_comm x.2 y.2)
  mul_assoc := by
    intro x y z
    apply cq3_ext
    · show ratRing.add
            (ratRing.mul
              (ratRing.add (ratRing.mul x.1 y.1)
                (ratRing.mul cq3D (ratRing.mul x.2 y.2))) z.1)
            (ratRing.mul cq3D
              (ratRing.mul
                (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)) z.2))
          = ratRing.add
            (ratRing.mul x.1
              (ratRing.add (ratRing.mul y.1 z.1)
                (ratRing.mul cq3D (ratRing.mul y.2 z.2))))
            (ratRing.mul cq3D
              (ratRing.mul x.2
                (ratRing.add (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1))))
      rw [ratRing.right_distrib (ratRing.mul x.1 y.1)
            (ratRing.mul cq3D (ratRing.mul x.2 y.2)) z.1,
          ratRing.right_distrib (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1) z.2,
          ratRing.left_distrib cq3D (ratRing.mul (ratRing.mul x.1 y.2) z.2)
            (ratRing.mul (ratRing.mul x.2 y.1) z.2),
          ratRing.left_distrib x.1 (ratRing.mul y.1 z.1)
            (ratRing.mul cq3D (ratRing.mul y.2 z.2)),
          ratRing.left_distrib x.2 (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1),
          ratRing.left_distrib cq3D (ratRing.mul x.2 (ratRing.mul y.1 z.2))
            (ratRing.mul x.2 (ratRing.mul y.2 z.1)),
          ratRing.mul_assoc x.1 y.1 z.1,
          ratRing.mul_assoc cq3D (ratRing.mul x.2 y.2) z.1,
          ratRing.mul_assoc x.2 y.2 z.1,
          ratRing.mul_assoc x.1 y.2 z.2,
          ← ratRing.mul_assoc cq3D x.1 (ratRing.mul y.2 z.2),
          ratRing.mul_comm cq3D x.1,
          ratRing.mul_assoc x.1 cq3D (ratRing.mul y.2 z.2),
          ratRing.mul_assoc x.2 y.1 z.2,
          ratRing.add_add_add_comm (ratRing.mul x.1 (ratRing.mul y.1 z.1))
            (ratRing.mul cq3D (ratRing.mul x.2 (ratRing.mul y.2 z.1)))
            (ratRing.mul x.1 (ratRing.mul cq3D (ratRing.mul y.2 z.2)))
            (ratRing.mul cq3D (ratRing.mul x.2 (ratRing.mul y.1 z.2))),
          ratRing.add_comm (ratRing.mul cq3D (ratRing.mul x.2 (ratRing.mul y.2 z.1)))
            (ratRing.mul cq3D (ratRing.mul x.2 (ratRing.mul y.1 z.2)))]
    · show ratRing.add
            (ratRing.mul
              (ratRing.add (ratRing.mul x.1 y.1)
                (ratRing.mul cq3D (ratRing.mul x.2 y.2))) z.2)
            (ratRing.mul
              (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)) z.1)
          = ratRing.add
            (ratRing.mul x.1
              (ratRing.add (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1)))
            (ratRing.mul x.2
              (ratRing.add (ratRing.mul y.1 z.1)
                (ratRing.mul cq3D (ratRing.mul y.2 z.2))))
      rw [ratRing.right_distrib (ratRing.mul x.1 y.1)
            (ratRing.mul cq3D (ratRing.mul x.2 y.2)) z.2,
          ratRing.right_distrib (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1) z.1,
          ratRing.left_distrib x.1 (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1),
          ratRing.left_distrib x.2 (ratRing.mul y.1 z.1)
            (ratRing.mul cq3D (ratRing.mul y.2 z.2)),
          ratRing.mul_assoc x.1 y.1 z.2,
          ratRing.mul_assoc cq3D (ratRing.mul x.2 y.2) z.2,
          ratRing.mul_assoc x.2 y.2 z.2,
          ← ratRing.mul_assoc cq3D x.2 (ratRing.mul y.2 z.2),
          ratRing.mul_comm cq3D x.2,
          ratRing.mul_assoc x.2 cq3D (ratRing.mul y.2 z.2),
          ratRing.mul_assoc x.1 y.2 z.1,
          ratRing.mul_assoc x.2 y.1 z.1,
          ratRing.add_add_add_comm (ratRing.mul x.1 (ratRing.mul y.1 z.2))
            (ratRing.mul x.2 (ratRing.mul cq3D (ratRing.mul y.2 z.2)))
            (ratRing.mul x.1 (ratRing.mul y.2 z.1))
            (ratRing.mul x.2 (ratRing.mul y.1 z.1)),
          ratRing.add_comm (ratRing.mul x.2 (ratRing.mul cq3D (ratRing.mul y.2 z.2)))
            (ratRing.mul x.2 (ratRing.mul y.1 z.1))]
  one_mul := by
    intro x
    apply cq3_ext
    · show ratRing.add (ratRing.mul ratRing.one x.1)
            (ratRing.mul cq3D (ratRing.mul ratRing.zero x.2)) = x.1
      rw [ratRing.one_mul x.1, ratRing.zero_mul x.2, ratRing.mul_zero cq3D,
        ratRing.add_zero x.1]
    · show ratRing.add (ratRing.mul ratRing.one x.2)
            (ratRing.mul ratRing.zero x.1) = x.2
      rw [ratRing.one_mul x.2, ratRing.zero_mul x.1, ratRing.add_zero x.2]
  mul_comm := by
    intro x y
    apply cq3_ext
    · show ratRing.add (ratRing.mul x.1 y.1)
            (ratRing.mul cq3D (ratRing.mul x.2 y.2))
          = ratRing.add (ratRing.mul y.1 x.1)
            (ratRing.mul cq3D (ratRing.mul y.2 x.2))
      rw [ratRing.mul_comm x.1 y.1, ratRing.mul_comm x.2 y.2]
    · show ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)
          = ratRing.add (ratRing.mul y.1 x.2) (ratRing.mul y.2 x.1)
      rw [ratRing.mul_comm x.1 y.2, ratRing.mul_comm x.2 y.1,
        ratRing.add_comm (ratRing.mul y.2 x.1) (ratRing.mul y.1 x.2)]
  left_distrib := by
    intro x y z
    apply cq3_ext
    · show ratRing.add (ratRing.mul x.1 (ratRing.add y.1 z.1))
            (ratRing.mul cq3D (ratRing.mul x.2 (ratRing.add y.2 z.2)))
          = ratRing.add
            (ratRing.add (ratRing.mul x.1 y.1)
              (ratRing.mul cq3D (ratRing.mul x.2 y.2)))
            (ratRing.add (ratRing.mul x.1 z.1)
              (ratRing.mul cq3D (ratRing.mul x.2 z.2)))
      rw [ratRing.left_distrib x.1 y.1 z.1, ratRing.left_distrib x.2 y.2 z.2,
        ratRing.left_distrib cq3D (ratRing.mul x.2 y.2) (ratRing.mul x.2 z.2),
        ratRing.add_add_add_comm (ratRing.mul x.1 y.1) (ratRing.mul x.1 z.1)
          (ratRing.mul cq3D (ratRing.mul x.2 y.2))
          (ratRing.mul cq3D (ratRing.mul x.2 z.2))]
    · show ratRing.add (ratRing.mul x.1 (ratRing.add y.2 z.2))
            (ratRing.mul x.2 (ratRing.add y.1 z.1))
          = ratRing.add
            (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1))
            (ratRing.add (ratRing.mul x.1 z.2) (ratRing.mul x.2 z.1))
      rw [ratRing.left_distrib x.1 y.2 z.2, ratRing.left_distrib x.2 y.1 z.1,
        ratRing.add_add_add_comm (ratRing.mul x.1 y.2) (ratRing.mul x.1 z.2)
          (ratRing.mul x.2 y.1) (ratRing.mul x.2 z.1)]

/-! ## cq3-3: 形式的実性 — (a,b) ≠ (0,0) ⟹ N = a²+3b² ≠ 0 -/

/-- 非負元 u, v で u+v = 0 なら u = 0（平方非負 + 反対称律）。 -/
theorem cq3_add_nonneg_left {u v : QRat} (hu : qLe ratRing.zero u)
    (hv : qLe ratRing.zero v) (h : ratRing.add u v = ratRing.zero) :
    u = ratRing.zero := by
  have h3 : qLe (ratRing.add ratRing.zero u) (ratRing.add v u) :=
    gqi_q_le_add u hv
  rw [ratRing.zero_add u, ratRing.add_comm v u, h] at h3
  exact qLe_antisym u ratRing.zero h3 hu

/-- 非負元 u, v で u+v = 0 なら v = 0。 -/
theorem cq3_add_nonneg_right {u v : QRat} (hu : qLe ratRing.zero u)
    (hv : qLe ratRing.zero v) (h : ratRing.add u v = ratRing.zero) :
    v = ratRing.zero := by
  have h' : ratRing.add v u = ratRing.zero := by
    rw [ratRing.add_comm v u]; exact h
  exact cq3_add_nonneg_left hv hu h'

/-- **cq3-3: ノルムの非退化性（ℚ の形式的実性）** — (a,b) ≠ (0,0) なら
    a² + 3b² ≠ 0。証明: a²+3b² = 0 と仮定すると a² ≥ 0・3b² ≥ 0（3 ≥ 0）と
    反対称律から a² = 0 かつ 3b² = 0、整域性（3 ≠ 0）で b² = 0、非零選言を
    構成的に剥がして (a,b) = (0,0) を得、矛盾。choice 不使用。 -/
theorem cq3_normsq_ne_zero (x : cq3Carrier) (hx : x ≠ cq3Zero) :
    cq3Norm x ≠ ratRing.zero := by
  intro hN
  have hu : qLe ratRing.zero (ratRing.mul x.1 x.1) := gqi_q_sq_nonneg x.1
  have hv_eq : ratRing.neg (ratRing.mul cq3D (ratRing.mul x.2 x.2))
      = ratRing.mul cq3Three (ratRing.mul x.2 x.2) := by
    rw [← ratRing.neg_mul cq3D (ratRing.mul x.2 x.2), cq3_neg_D]
  have hv : qLe ratRing.zero
      (ratRing.neg (ratRing.mul cq3D (ratRing.mul x.2 x.2))) := by
    rw [hv_eq]
    exact gqi_q_mul_nonneg cq3Three (ratRing.mul x.2 x.2) cq3_three_nonneg
      (gqi_q_sq_nonneg x.2)
  have hsum : ratRing.add (ratRing.mul x.1 x.1)
      (ratRing.neg (ratRing.mul cq3D (ratRing.mul x.2 x.2))) = ratRing.zero := hN
  have ha : ratRing.mul x.1 x.1 = ratRing.zero :=
    cq3_add_nonneg_left hu hv hsum
  have hb0 : ratRing.neg (ratRing.mul cq3D (ratRing.mul x.2 x.2))
      = ratRing.zero := cq3_add_nonneg_right hu hv hsum
  rw [hv_eq] at hb0
  have hbb : ratRing.mul x.2 x.2 = ratRing.zero :=
    ratIUTField.eq_zero_of_mul_eq_zero_left hb0 cq3_three_ne_zero
  apply gqi_q_not_ne_of_sq_zero ha
  intro h1
  apply gqi_q_not_ne_of_sq_zero hbb
  intro h2
  apply hx
  exact cq3_ext h1 h2

/-! ## cq3-4: ℚ(√−3) は本物の体 -/

/-- **体公理の本体** — x ≠ 0 なら x·x⁻¹ = 1。第 1 成分は
    a·(aN⁻¹) + D·(b·(−bN⁻¹)) = (a² − D·b²)·N⁻¹ = N·N⁻¹ = 1、
    第 2 成分は a·(−bN⁻¹) + b·(aN⁻¹) = 0。 -/
theorem cq3_mul_inv_cancel (x : cq3Carrier) (hx : x ≠ cq3Zero) :
    cq3Mul x (cq3Inv x) = cq3One := by
  have hN : cq3Norm x ≠ ratRing.zero := cq3_normsq_ne_zero x hx
  have hcancel : ratRing.mul (cq3Norm x) (qInv (cq3Norm x)) = ratRing.one :=
    ratIUTField.mul_inv_cancel (cq3Norm x) hN
  apply cq3_ext
  · show ratRing.add
          (ratRing.mul x.1 (ratRing.mul x.1 (qInv (cq3Norm x))))
          (ratRing.mul cq3D
            (ratRing.mul x.2
              (ratRing.mul (ratRing.neg x.2) (qInv (cq3Norm x)))))
        = ratRing.one
    rw [← ratRing.mul_assoc x.1 x.1 (qInv (cq3Norm x)),
      ← ratRing.mul_assoc x.2 (ratRing.neg x.2) (qInv (cq3Norm x)),
      ratRing.mul_neg x.2 x.2,
      ratRing.neg_mul (ratRing.mul x.2 x.2) (qInv (cq3Norm x)),
      ratRing.mul_neg cq3D (ratRing.mul (ratRing.mul x.2 x.2) (qInv (cq3Norm x))),
      ← ratRing.mul_assoc cq3D (ratRing.mul x.2 x.2) (qInv (cq3Norm x)),
      ← ratRing.neg_mul (ratRing.mul cq3D (ratRing.mul x.2 x.2)) (qInv (cq3Norm x)),
      ← ratRing.right_distrib (ratRing.mul x.1 x.1)
        (ratRing.neg (ratRing.mul cq3D (ratRing.mul x.2 x.2))) (qInv (cq3Norm x))]
    exact hcancel
  · show ratRing.add
          (ratRing.mul x.1 (ratRing.mul (ratRing.neg x.2) (qInv (cq3Norm x))))
          (ratRing.mul x.2 (ratRing.mul x.1 (qInv (cq3Norm x))))
        = ratRing.zero
    rw [← ratRing.mul_assoc x.1 (ratRing.neg x.2) (qInv (cq3Norm x)),
      ratRing.mul_neg x.1 x.2,
      ratRing.neg_mul (ratRing.mul x.1 x.2) (qInv (cq3Norm x)),
      ← ratRing.mul_assoc x.2 x.1 (qInv (cq3Norm x)),
      ratRing.mul_comm x.2 x.1]
    exact ratRing.neg_add (ratRing.mul (ratRing.mul x.1 x.2) (qInv (cq3Norm x)))

/-- 0⁻¹ = 0。 -/
theorem cq3_inv_zero : cq3Inv cq3Zero = cq3Zero := by
  apply cq3_ext
  · show ratRing.mul ratRing.zero (qInv (cq3Norm cq3Zero)) = ratRing.zero
    exact ratRing.zero_mul (qInv (cq3Norm cq3Zero))
  · show ratRing.mul (ratRing.neg ratRing.zero) (qInv (cq3Norm cq3Zero))
        = ratRing.zero
    rw [gqi_q_neg_zero]
    exact ratRing.zero_mul (qInv (cq3Norm cq3Zero))

/-- (0,0) ≠ (1,0)。 -/
theorem cq3_zero_ne_one : cq3Zero ≠ cq3One := by
  intro h
  have h1 : ratRing.zero = ratRing.one :=
    congrArg (fun p : cq3Carrier => p.1) h
  exact ratIUTField.zero_ne_one h1

/-- **cq3-4: ℚ(√−3) は本物の体** — 台は実 ℚ×ℚ、逆元は実ガウス逆元、
    体公理は形式的実性から完全証明。 -/
def cq3Field : IUTField where
  toCRing := cq3Ring
  inv := cq3Inv
  mul_inv_cancel := cq3_mul_inv_cancel
  inv_zero := cq3_inv_zero
  zero_ne_one := cq3_zero_ne_one

/-! ## cq3-5: 1 の原始 3 乗根 ζ_3 の実構成と位数 3 -/

/-- 有理数 −1/2。 -/
def cq3NHalf : QRat := Quot.mk ratRel ⟨-1, 2, by omega⟩

/-- 有理数 1/2。 -/
def cq3PHalf : QRat := Quot.mk ratRel ⟨1, 2, by omega⟩

/-- **cq3-5a: 1 の原始 3 乗根** ζ_3 = (−1/2, 1/2) = (−1+√−3)/2 — carrier 内の実元。 -/
def cq3Zeta : cq3Carrier := ((cq3NHalf, cq3PHalf) : cq3Carrier)

/-- **ζ_3² = ζ_3·ζ_3**（本物のガウス乗法）。 -/
def cq3ZetaSq : cq3Carrier := cq3Mul cq3Zeta cq3Zeta

/-- **ζ_3² = (−1/2, −1/2)**（= (−1−√−3)/2、本物の乗法計算）。 -/
theorem cq3_zetaSq_eq : cq3ZetaSq = ((cq3NHalf, cq3NHalf) : cq3Carrier) := by
  apply cq3_ext
  · apply Quot.sound
    show (((-1) * (-1)) * (1 * (2 * 2)) + ((-3) * (1 * 1)) * (2 * 2)) * 2
        = (-1) * ((2 * 2) * (1 * (2 * 2)))
    omega
  · apply Quot.sound
    show (((-1) * 1) * (2 * 2) + (1 * (-1)) * (2 * 2)) * 2
        = (-1) * ((2 * 2) * (2 * 2))
    omega

/-- **cq3-5b（本丸）: ζ_3³ = 1** — ζ_3²·ζ_3 = 1（本物のガウス乗法で計算）。 -/
theorem cq3_zeta_cube_one : cq3Mul cq3ZetaSq cq3Zeta = cq3One := by
  rw [cq3_zetaSq_eq]
  apply cq3_ext
  · apply Quot.sound
    show (((-1) * (-1)) * (1 * (2 * 2)) + ((-3) * ((-1) * 1)) * (2 * 2)) * 1
        = 1 * ((2 * 2) * (1 * (2 * 2)))
    omega
  · apply Quot.sound
    show (((-1) * 1) * (2 * 2) + ((-1) * (-1)) * (2 * 2)) * 1
        = 0 * ((2 * 2) * (2 * 2))
    omega

/-- **cq3-5c: ζ_3 ≠ 1**（第 1 成分 −1/2 ≠ 1）。 -/
theorem cq3_zeta_ne_one : cq3Zeta ≠ cq3One := by
  intro h
  have h1 : cq3NHalf = ratRing.one := congrArg (fun p : cq3Carrier => p.1) h
  have h3 : (-1 : Int) * 1 = 1 * 2 := quot_exact_rat h1
  omega

/-- **cq3-5d: ζ_3² ≠ 1**（位数ちょうど 3。第 1 成分 −1/2 ≠ 1）。 -/
theorem cq3_zeta_sq_ne_one : cq3ZetaSq ≠ cq3One := by
  rw [cq3_zetaSq_eq]
  intro h
  have h1 : cq3NHalf = ratRing.one := congrArg (fun p : cq3Carrier => p.1) h
  have h3 : (-1 : Int) * 1 = 1 * 2 := quot_exact_rat h1
  omega

/-! ## cq3-6: 実円分群 μ_3 = {1, ζ_3, ζ_3²} ⊂ 実体 -/

/-- **cq3-6a: 実円分群 μ_3** = {1, ζ_3, ζ_3²}（実部分集合）。 -/
def cq3Mu3 (x : cq3Carrier) : Prop :=
  x = cq3One ∨ x = cq3Zeta ∨ x = cq3ZetaSq

/-- 1·x = x。 -/
theorem cq3_one_mul (a : cq3Carrier) : cq3Mul cq3One a = a := cq3Ring.one_mul a

/-- x·1 = x。 -/
theorem cq3_mul_one (a : cq3Carrier) : cq3Mul a cq3One = a := by
  show cq3Ring.mul a cq3One = a
  rw [cq3Ring.mul_comm a cq3One]; exact cq3Ring.one_mul a

/-- ζ_3·ζ_3² = 1（可換性 + ζ_3³ = 1）。 -/
theorem cq3_zeta_mul_zetaSq : cq3Mul cq3Zeta cq3ZetaSq = cq3One := by
  show cq3Ring.mul cq3Zeta cq3ZetaSq = cq3One
  rw [cq3Ring.mul_comm cq3Zeta cq3ZetaSq]
  exact cq3_zeta_cube_one

/-- ζ_3²·ζ_3² = ζ_3（= ζ_3⁴、本物の乗法計算）。 -/
theorem cq3_zetaSq_mul_zetaSq : cq3Mul cq3ZetaSq cq3ZetaSq = cq3Zeta := by
  rw [cq3_zetaSq_eq]
  apply cq3_ext
  · apply Quot.sound
    show (((-1) * (-1)) * (1 * (2 * 2)) + ((-3) * ((-1) * (-1))) * (2 * 2)) * 2
        = (-1) * ((2 * 2) * (1 * (2 * 2)))
    omega
  · apply Quot.sound
    show (((-1) * (-1)) * (2 * 2) + ((-1) * (-1)) * (2 * 2)) * 2
        = 1 * ((2 * 2) * (2 * 2))
    omega

/-- **cq3-6b: μ_3 は乗法で閉じる**（実円分群 μ_3 ⊂ 実体）— 9 通りの
    積を 1・ζ_3・ζ_3² のいずれかに帰着（単位法則と ζ_3³ = 1）。 -/
theorem cq3_mu3_closed (x y : cq3Carrier) (hx : cq3Mu3 x) (hy : cq3Mu3 y) :
    cq3Mu3 (cq3Mul x y) := by
  obtain hx | hx | hx := hx
  · obtain hy | hy | hy := hy
    · rw [hx, hy]; exact Or.inl (cq3_one_mul cq3One)
    · rw [hx, hy]; exact Or.inr (Or.inl (cq3_one_mul cq3Zeta))
    · rw [hx, hy]; exact Or.inr (Or.inr (cq3_one_mul cq3ZetaSq))
  · obtain hy | hy | hy := hy
    · rw [hx, hy]; exact Or.inr (Or.inl (cq3_mul_one cq3Zeta))
    · rw [hx, hy]; exact Or.inr (Or.inr rfl)
    · rw [hx, hy]; exact Or.inl cq3_zeta_mul_zetaSq
  · obtain hy | hy | hy := hy
    · rw [hx, hy]; exact Or.inr (Or.inr (cq3_mul_one cq3ZetaSq))
    · rw [hx, hy]; exact Or.inl cq3_zeta_cube_one
    · rw [hx, hy]; exact Or.inr (Or.inl cq3_zetaSq_mul_zetaSq)

/-! ## cq3-7: capstone -/

/-- **cq3-7: capstone** — 1 の原始 3 乗根を持つ本物の体が存在する
    （witness: ℚ(√−3) と ζ_3 = (−1+√−3)/2、ζ_3³ = 1・ζ_3 ≠ 1・ζ_3² ≠ 1）。 -/
theorem cq3_exists :
    ∃ F : IUTField, ∃ z : F.carrier,
      z ≠ F.one ∧ F.mul (F.mul z z) z = F.one ∧ F.mul z z ≠ F.one :=
  ⟨cq3Field, cq3Zeta, cq3_zeta_ne_one, cq3_zeta_cube_one, cq3_zeta_sq_ne_one⟩

end IUT
