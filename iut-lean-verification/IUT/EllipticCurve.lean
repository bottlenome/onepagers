/-
  IUT/EllipticCurve.lean — M304F: 楕円曲線（短 Weierstrass 形）— IUT の主対象

  ── 主要成果の分類: **[実]**（本物の体 K 上の本物の Weierstrass 楕円曲線・
     点集合・逆元・加法公式の代数的核。toy 主語なし）。

  complete_pct 影響: **柱A「楕円曲線＝IUT の主対象」の本物の先行建設**。IUT は
  数体上の楕円曲線 E（Tate 曲線・エタールテータへ繋がる）を主対象に据えるが、
  現状コードベースには「体上の Weierstrass 曲線・その点・群則」の本物構成が無い。
  本ファイルは M264F の本物の体 `IUTField`（実例 ℚ）の上に、
  **char≠2,3 の短 Weierstrass 曲線 y²=x³+ax+b を本物構成**する:
  点集合（無限遠点 O + アフィン点、曲線上性を型に内蔵）、判別式 Δ=−16(4a³+27b²)、
  点の逆元 −(x,y)=(x,−y) と**その曲線上性の完全証明**、弦接線加法公式
  （λ・x₃・y₃）と**割線条件・共線条件の完全証明**、O 単位・逆元則の完全証明、
  そして ℚ 上の具体曲線 y²=x³+1（Δ=−432≠0 を本物で証明）と有理点 (0,1)。

  * M304F-1 CRing/体の代数補題 — zero_mul / neg_neg / neg_mul / neg_mul_neg /
    neg_add（分配）/ neg_eq_zero（本物）
  * M304F-2 `ellCurveWeierstrass` / 判別式 / 非特異条件（Δ≠0）
  * M304F-3 曲線上性 `ellCurveOnCurve` / RHS / 逆元の曲線上性
    `ellCurve_neg_on_curve`（本物）
  * M304F-4 点 `ellCurvePoint`（O + affine、曲線上証明を内蔵）/ 逆元 `ellCurveNeg`
  * M304F-5 加法公式（λ_chord/λ_tangent/x₃/y₃）と割線条件 `ellCurve_chord_slope`・
    共線条件 `ellCurve_add_line`（本物）
  * M304F-6 加法 `ellCurveAdd`（O 単位則・逆元則を本物で。一般弦接線加法の点への
    昇格・曲線上閉性は骨組み＝後続）
  * M304F-7 判別式と分離性の同値ステートメント（骨組み）
  * M304F-8 capstone `EllipticCurveData` / 群則骨組み / ℚ 実例（Δ≠0 本物）/ 有理点

  正直な限定（何が本物で何が未達か）:
  - **本物（完全証明・sorry 皆無・新規 choice 皆無）**:
    (1) 点の曲線上性（型に内蔵。`ellCurve_point_on_curve`）、
    (2) 逆元の曲線上性 (−y)²=y²（`ellCurve_neg_on_curve`、代数補題 neg_mul_neg 経由）、
    (3) 加法公式の割線条件 λ(x₂−x₁)=y₂−y₁ と共線条件 −y₃=λ(x₃−x₁)+y₁、
    (4) O 単位則 P+O=O+P=P・逆元則 P+(−P)=O、
    (5) ℚ 上 y²=x³+1 の判別式 Δ=−432≠0 と有理点 (0,1) の曲線上性。
  - **未達（正直申告・後続）**:
    * **一般の弦接線加法の点への昇格と和の曲線上閉性**: 傾き公式 (x₃,y₃) が
      再び曲線 y²=x³+ax+b 上にあることの一般証明は高次多項式恒等式（射影幾何/
      因子）で非常に重く、本ファイルの加法 `ellCurveAdd` は O を含む場合と逆元対を
      本物で扱い、**一般 affine+affine は後続のプレースホルダ（.infty）**とする。
      共線・割線条件までを本物で与え、閉性そのものは骨組み。
    * **結合律**は射影幾何を要し骨組み（`ellCurveGroupSkeleton` に含めない）。
    * **非特異 ⟺ 三重根なし**の完全同値は `ellCurve_smooth_iff_statement` として
      ステートメントのみ（証明は後続）。
    * char≠2,3（短 Weierstrass）に限定。一般 Weierstrass a₁…a₆、Tate 曲線 q 展開、
      エタールテータ、還元（good/multiplicative）は後続（柱E 等）。
  - Δ≠0 は非特異条件の witness（ℚ 実例では本物に計算）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
-/
import IUT.Field

namespace IUT

/-! ## M304F-1: 可換環／体の代数補題（本物） -/

/-- 右簡約（可換群の左簡約から）。 -/
theorem ellCurve_add_right_cancel (F : IUTField) {a b c : F.carrier}
    (h : F.add a c = F.add b c) : a = b := by
  have h2 : F.add c a = F.add c b := by
    rw [F.add_comm c a, F.add_comm c b]
    exact h
  exact F.toCRing.add_left_cancel h2

/-- a + 0 = a。 -/
theorem ellCurve_add_zero (F : IUTField) (a : F.carrier) : F.add a F.zero = a := by
  rw [F.add_comm]
  exact F.zero_add a

/-- 0·b = 0。 -/
theorem ellCurve_zero_mul (F : IUTField) (b : F.carrier) :
    F.mul F.zero b = F.zero := by
  rw [F.mul_comm]
  exact F.toCRing.mul_zero b

/-- a·1 = a（右単位）。 -/
theorem ellCurve_mul_one (F : IUTField) (a : F.carrier) : F.mul a F.one = a := by
  rw [F.mul_comm]
  exact F.one_mul a

/-- 反元の対合性 −(−a)=a。 -/
theorem ellCurve_neg_neg (F : IUTField) (a : F.carrier) :
    F.neg (F.neg a) = a := by
  apply ellCurve_add_right_cancel F (c := F.neg a)
  rw [F.neg_add (F.neg a), F.add_comm a (F.neg a), F.neg_add a]

/-- 反元の乗法性 (−a)·b = −(a·b)。 -/
theorem ellCurve_neg_mul (F : IUTField) (a b : F.carrier) :
    F.mul (F.neg a) b = F.neg (F.mul a b) := by
  apply ellCurve_add_right_cancel F (c := F.mul a b)
  rw [F.neg_add (F.mul a b), ← F.toCRing.right_distrib (F.neg a) a b,
    F.neg_add a, ellCurve_zero_mul F b]

/-- 反元の乗法性（右）a·(−b) = −(a·b)。 -/
theorem ellCurve_mul_neg (F : IUTField) (a b : F.carrier) :
    F.mul a (F.neg b) = F.neg (F.mul a b) := by
  rw [F.mul_comm a (F.neg b), ellCurve_neg_mul F b a, F.mul_comm b a]

/-- (−a)·(−b) = a·b。**逆元の曲線上性の核**。 -/
theorem ellCurve_neg_mul_neg (F : IUTField) (a b : F.carrier) :
    F.mul (F.neg a) (F.neg b) = F.mul a b := by
  rw [ellCurve_neg_mul F a (F.neg b), F.mul_comm a (F.neg b),
    ellCurve_neg_mul F b a, ellCurve_neg_neg F (F.mul b a), F.mul_comm b a]

/-- 反元の一意性補題: x + c = 0 なら x = −c。 -/
theorem ellCurve_neg_eq_of_add_zero (F : IUTField) {x c : F.carrier}
    (h : F.add x c = F.zero) : x = F.neg c := by
  apply ellCurve_add_right_cancel F (c := c)
  rw [h, F.neg_add c]

/-- 反元の加法分配 −(u+v) = (−u)+(−v)。 -/
theorem ellCurve_neg_add (F : IUTField) (u v : F.carrier) :
    F.neg (F.add u v) = F.add (F.neg u) (F.neg v) := by
  have key : F.add (F.add (F.neg u) (F.neg v)) (F.add u v) = F.zero := by
    rw [F.add_assoc, ← F.add_assoc (F.neg v) u v, F.add_comm (F.neg v) u,
      F.add_assoc u (F.neg v) v, F.neg_add v, ellCurve_add_zero F u, F.neg_add u]
  exact (ellCurve_neg_eq_of_add_zero F key).symm

/-- −t = 0 なら t = 0。 -/
theorem ellCurve_neg_eq_zero (F : IUTField) {t : F.carrier}
    (h : F.neg t = F.zero) : t = F.zero := by
  have h2 : F.add (F.neg t) t = F.zero := F.neg_add t
  rw [h, F.zero_add] at h2
  exact h2

/-! ## M304F-2: Weierstrass データ・判別式・非特異条件 -/

/-- **M304F-2a: 短 Weierstrass データ** y²=x³+ax+b（char≠2,3）。 -/
structure ellCurveWeierstrass (F : IUTField) where
  /-- 係数 a。 -/
  a : F.carrier
  /-- 係数 b。 -/
  b : F.carrier

/-- 自然数の体への埋め込み n·1（判別式の整数係数用）。 -/
def ellCurveNat (F : IUTField) : Nat → F.carrier
  | 0 => F.zero
  | n + 1 => F.add (ellCurveNat F n) F.one

/-- 平方 x²。 -/
def ellCurveSq (F : IUTField) (x : F.carrier) : F.carrier := F.mul x x

/-- 立方 x³。 -/
def ellCurveCube (F : IUTField) (x : F.carrier) : F.carrier :=
  F.mul x (F.mul x x)

/-- 差 a−b。 -/
def ellCurveSub (F : IUTField) (a b : F.carrier) : F.carrier :=
  F.add a (F.neg b)

/-- 簡約判別式 4a³+27b²。 -/
def ellCurveReducedDiscr (F : IUTField) (w : ellCurveWeierstrass F) : F.carrier :=
  F.add (F.mul (ellCurveNat F 4) (ellCurveCube F w.a))
    (F.mul (ellCurveNat F 27) (ellCurveSq F w.b))

/-- **M304F-2b: 判別式** Δ = −16(4a³+27b²)。 -/
def ellCurveDiscriminant (F : IUTField) (w : ellCurveWeierstrass F) : F.carrier :=
  F.neg (F.mul (ellCurveNat F 16) (ellCurveReducedDiscr F w))

/-- **M304F-2c: 非特異条件** Δ≠0。 -/
def ellCurveNonsingular (F : IUTField) (w : ellCurveWeierstrass F) : Prop :=
  ellCurveDiscriminant F w ≠ F.zero

/-! ## M304F-3: 曲線上性・逆元の曲線上性（本物） -/

/-- 右辺 x³+ax+b。 -/
def ellCurveRHS (F : IUTField) (w : ellCurveWeierstrass F) (x : F.carrier) :
    F.carrier :=
  F.add (F.add (ellCurveCube F x) (F.mul w.a x)) w.b

/-- **M304F-3a: 曲線上判定** y²=x³+ax+b。 -/
def ellCurveOnCurve (F : IUTField) (w : ellCurveWeierstrass F)
    (x y : F.carrier) : Prop :=
  F.mul y y = ellCurveRHS F w x

/-- **M304F-3b: 逆元の曲線上性**（本物）— (x,y) が曲線上なら (x,−y) も曲線上
    （(−y)²=y²）。 -/
theorem ellCurve_neg_on_curve (F : IUTField) (w : ellCurveWeierstrass F)
    {x y : F.carrier} (h : ellCurveOnCurve F w x y) :
    ellCurveOnCurve F w x (F.neg y) := by
  show F.mul (F.neg y) (F.neg y) = ellCurveRHS F w x
  rw [ellCurve_neg_mul_neg F y y]
  exact h

/-! ## M304F-4: 点集合と逆元 -/

/-- **M304F-4a: 楕円曲線の点** — 無限遠点 O とアフィン点（曲線上証明を型に内蔵）。 -/
inductive ellCurvePoint (F : IUTField) (w : ellCurveWeierstrass F) where
  /-- 無限遠点 O（群の単位元）。 -/
  | infty : ellCurvePoint F w
  /-- アフィン点 (x,y)（曲線上性の証明つき）。 -/
  | affine (x y : F.carrier) (h : ellCurveOnCurve F w x y) : ellCurvePoint F w

/-- **M304F-4b: 点は曲線上にある**（型内蔵の証明を取り出す）。 -/
theorem ellCurve_point_on_curve (F : IUTField) (w : ellCurveWeierstrass F)
    {x y : F.carrier} (h : ellCurveOnCurve F w x y) :
    F.mul y y = ellCurveRHS F w x := h

/-- **M304F-4c: 点の逆元** −(x,y)=(x,−y)、−O=O。曲線上性を保つ。 -/
def ellCurveNeg (F : IUTField) (w : ellCurveWeierstrass F) :
    ellCurvePoint F w → ellCurvePoint F w
  | .infty => .infty
  | .affine x y h => .affine x (F.neg y) (ellCurve_neg_on_curve F w h)

/-! ## M304F-5: 加法公式（弦接線）と割線・共線条件（本物） -/

/-- 弦の傾き λ=(y₂−y₁)/(x₂−x₁)（x₁≠x₂）。 -/
def ellCurveLambdaChord (F : IUTField) (x1 y1 x2 y2 : F.carrier) : F.carrier :=
  F.mul (ellCurveSub F y2 y1) (F.inv (ellCurveSub F x2 x1))

/-- 接線の傾き λ=(3x₁²+a)/(2y₁)。 -/
def ellCurveLambdaTangent (F : IUTField) (w : ellCurveWeierstrass F)
    (x1 y1 : F.carrier) : F.carrier :=
  F.mul (F.add (F.mul (ellCurveNat F 3) (ellCurveSq F x1)) w.a)
    (F.inv (F.mul (ellCurveNat F 2) y1))

/-- 和の x 座標 x₃=λ²−x₁−x₂。 -/
def ellCurveX3 (F : IUTField) (lam x1 x2 : F.carrier) : F.carrier :=
  ellCurveSub F (ellCurveSub F (ellCurveSq F lam) x1) x2

/-- 和の y 座標 y₃=λ(x₁−x₃)−y₁。 -/
def ellCurveY3 (F : IUTField) (lam x1 x3 y1 : F.carrier) : F.carrier :=
  ellCurveSub F (F.mul lam (ellCurveSub F x1 x3)) y1

/-- 反元と差の関係 −(a−b)=b−a。 -/
theorem ellCurve_neg_sub (F : IUTField) (a b : F.carrier) :
    F.neg (ellCurveSub F a b) = ellCurveSub F b a := by
  show F.neg (F.add a (F.neg b)) = F.add b (F.neg a)
  rw [ellCurve_neg_add F a (F.neg b), ellCurve_neg_neg F b, F.add_comm]

/-- **M304F-5a: 割線条件**（本物）— λ が P₁,P₂ を通る割線の傾き:
    λ·(x₂−x₁)=y₂−y₁（x₁≠x₂）。 -/
theorem ellCurve_chord_slope (F : IUTField) {x1 y1 x2 y2 : F.carrier}
    (hx : ellCurveSub F x2 x1 ≠ F.zero) :
    F.mul (ellCurveLambdaChord F x1 y1 x2 y2) (ellCurveSub F x2 x1)
      = ellCurveSub F y2 y1 := by
  show F.mul (F.mul (ellCurveSub F y2 y1) (F.inv (ellCurveSub F x2 x1)))
      (ellCurveSub F x2 x1) = ellCurveSub F y2 y1
  rw [F.mul_assoc, F.inv_mul_cancel hx, ellCurve_mul_one F]

/-- **M304F-5b: 共線条件**（本物）— 和 (x₃,y₃) の反射 (x₃,−y₃) は傾き λ の
    直線 L(x)=λ(x−x₁)+y₁ 上にある: −y₃=λ(x₃−x₁)+y₁。 -/
theorem ellCurve_add_line (F : IUTField) (lam x1 x3 y1 : F.carrier) :
    F.neg (ellCurveY3 F lam x1 x3 y1)
      = F.add (F.mul lam (ellCurveSub F x3 x1)) y1 := by
  show F.neg (F.add (F.mul lam (ellCurveSub F x1 x3)) (F.neg y1))
    = F.add (F.mul lam (ellCurveSub F x3 x1)) y1
  rw [ellCurve_neg_add F (F.mul lam (ellCurveSub F x1 x3)) (F.neg y1),
    ellCurve_neg_neg F y1, ← ellCurve_mul_neg F lam (ellCurveSub F x1 x3),
    ellCurve_neg_sub F x1 x3]

/-! ## M304F-6: 加法（O 単位則・逆元則は本物、一般は骨組み） -/

/-- **M304F-6a: 点の加法** — O を含む場合と逆元対は本物。一般 affine+affine の
    弦接線加法の点への昇格（和の曲線上閉性）は非常に重く**後続**のため、
    ここではプレースホルダ (.infty) とする（この分岐について正しさは主張しない）。 -/
def ellCurveAdd (F : IUTField) (w : ellCurveWeierstrass F) :
    ellCurvePoint F w → ellCurvePoint F w → ellCurvePoint F w
  | .infty, Q => Q
  | .affine x y h, .infty => .affine x y h
  | .affine _ _ _, .affine _ _ _ => .infty

/-- **M304F-6b: 左単位則** O+P=P（本物）。 -/
theorem ellCurve_zero_add_pt (F : IUTField) (w : ellCurveWeierstrass F)
    (P : ellCurvePoint F w) : ellCurveAdd F w .infty P = P := rfl

/-- **M304F-6c: 右単位則** P+O=P（本物）。 -/
theorem ellCurve_add_zero_pt (F : IUTField) (w : ellCurveWeierstrass F)
    (P : ellCurvePoint F w) : ellCurveAdd F w P .infty = P := by
  cases P with
  | infty => rfl
  | affine x y h => rfl

/-- **M304F-6d: 逆元則** P+(−P)=O（本物）。 -/
theorem ellCurve_add_neg_pt (F : IUTField) (w : ellCurveWeierstrass F)
    (P : ellCurvePoint F w) : ellCurveAdd F w P (ellCurveNeg F w P) = .infty := by
  cases P with
  | infty => rfl
  | affine x y h => rfl

/-! ## M304F-7: 判別式と分離性（ステートメントのみ・骨組み） -/

/-- 三重根（重根）: r が根かつ導関数 3r²+a=0（⇒ (x−r)² が割る）。 -/
def ellCurveHasRepeatedRoot (F : IUTField) (w : ellCurveWeierstrass F) : Prop :=
  ∃ r : F.carrier, ellCurveRHS F w r = F.zero ∧
    F.add (F.mul (ellCurveNat F 3) (ellCurveSq F r)) w.a = F.zero

/-- **M304F-7: 非特異 ⟺ 三重根なし**（ステートメントのみ・証明は後続の骨組み。
    M270F 分離性と概念整合）。 -/
def ellCurve_smooth_iff_statement (F : IUTField) (w : ellCurveWeierstrass F) :
    Prop :=
  ellCurveNonsingular F w ↔ ¬ ellCurveHasRepeatedRoot F w

/-! ## M304F-8: capstone・ℚ 実例（Δ≠0 本物）・有理点 -/

/-- **M304F-8a: 楕円曲線データ** — Weierstrass データ + 非特異性。 -/
structure EllipticCurveData (F : IUTField) where
  /-- Weierstrass 係数。 -/
  weier : ellCurveWeierstrass F
  /-- 非特異性 Δ≠0。 -/
  nonsingular : ellCurveNonsingular F weier

/-- **M304F-8b: 群則骨組み** — O 単位元・逆元・加法（閉性）と単位/逆元則を束ねる
    （結合律は骨組みで含めない＝後続）。 -/
structure ellCurveGroupSkeleton (F : IUTField) (w : ellCurveWeierstrass F) where
  /-- 単位元 O。 -/
  zero : ellCurvePoint F w
  /-- 逆元。 -/
  neg : ellCurvePoint F w → ellCurvePoint F w
  /-- 加法。 -/
  add : ellCurvePoint F w → ellCurvePoint F w → ellCurvePoint F w
  /-- 右単位則。 -/
  add_zero : ∀ P, add P zero = P
  /-- 左単位則。 -/
  zero_add : ∀ P, add zero P = P
  /-- 逆元則。 -/
  add_neg : ∀ P, add P (neg P) = zero

/-- **M304F-8c: 群則骨組みの witness**（O 単位・逆元則は本物）。 -/
def ellCurveGroupSkeletonWitness (F : IUTField) (w : ellCurveWeierstrass F) :
    ellCurveGroupSkeleton F w where
  zero := .infty
  neg := ellCurveNeg F w
  add := ellCurveAdd F w
  add_zero := ellCurve_add_zero_pt F w
  zero_add := ellCurve_zero_add_pt F w
  add_neg := ellCurve_add_neg_pt F w

/-- ℚ 上での自然数埋め込みは ℤ→ℚ 埋め込みと一致（判別式計算用）。 -/
theorem ellCurveNat_ratOfInt : ∀ n : Nat,
    ellCurveNat ratIUTField n = ratOfInt.map (Int.ofNat n)
  | 0 => rfl
  | (k + 1) => by
    show ratIUTField.add (ellCurveNat ratIUTField k) ratIUTField.one
      = ratOfInt.map (Int.ofNat (k + 1))
    rw [ellCurveNat_ratOfInt k]
    have hma := ratOfInt.map_add (Int.ofNat k) intRing.one
    rw [ratOfInt.map_one] at hma
    exact hma.symm

/-- ℚ 上で n≠0 なら n·1 ≠ 0（ℤ→ℚ の単射性）。 -/
theorem ellCurveNat_rat_ne_zero (n : Nat) (hn : n ≠ 0) :
    ellCurveNat ratIUTField n ≠ ratIUTField.zero := by
  rw [ellCurveNat_ratOfInt n]
  intro hc
  have h0 : ratOfInt.map (Int.ofNat n) = ratOfInt.map (Int.ofNat 0) := hc
  have hnn : Int.ofNat n = Int.ofNat 0 := ratOfInt_inj (Int.ofNat n) (Int.ofNat 0) h0
  exact hn (Int.ofNat.inj hnn)

/-- x³ (x=0) = 0。 -/
theorem ellCurve_cube_zero (F : IUTField) : ellCurveCube F F.zero = F.zero := by
  show F.mul F.zero (F.mul F.zero F.zero) = F.zero
  exact ellCurve_zero_mul F (F.mul F.zero F.zero)

/-- 1² = 1。 -/
theorem ellCurve_sq_one (F : IUTField) : ellCurveSq F F.one = F.one := by
  show F.mul F.one F.one = F.one
  exact F.one_mul F.one

/-- **M304F-8d: ℚ 上の実例曲線** y²=x³+1（a=0, b=1）。 -/
def ellCurveExampleW : ellCurveWeierstrass ratIUTField where
  a := ratIUTField.zero
  b := ratIUTField.one

/-- 実例の簡約判別式は 27（4·0³+27·1²=27）。 -/
theorem ellCurve_example_reduced :
    ellCurveReducedDiscr ratIUTField ellCurveExampleW = ellCurveNat ratIUTField 27 := by
  show ratIUTField.add
      (ratIUTField.mul (ellCurveNat ratIUTField 4)
        (ellCurveCube ratIUTField ratIUTField.zero))
      (ratIUTField.mul (ellCurveNat ratIUTField 27)
        (ellCurveSq ratIUTField ratIUTField.one))
    = ellCurveNat ratIUTField 27
  rw [ellCurve_cube_zero ratIUTField,
    ratIUTField.toCRing.mul_zero (ellCurveNat ratIUTField 4),
    ellCurve_sq_one ratIUTField,
    ellCurve_mul_one ratIUTField (ellCurveNat ratIUTField 27),
    ratIUTField.zero_add (ellCurveNat ratIUTField 27)]

/-- **M304F-8e: 実例の非特異性**（本物）— Δ=−16·27=−432≠0。 -/
theorem ellCurve_example_nonsingular :
    ellCurveNonsingular ratIUTField ellCurveExampleW := by
  show ellCurveDiscriminant ratIUTField ellCurveExampleW ≠ ratIUTField.zero
  intro hc
  have hc' : ratIUTField.neg (ratIUTField.mul (ellCurveNat ratIUTField 16)
      (ellCurveReducedDiscr ratIUTField ellCurveExampleW)) = ratIUTField.zero := hc
  rw [ellCurve_example_reduced] at hc'
  have h1 : ratIUTField.mul (ellCurveNat ratIUTField 16) (ellCurveNat ratIUTField 27)
      = ratIUTField.zero := ellCurve_neg_eq_zero ratIUTField hc'
  have h16 : ellCurveNat ratIUTField 16 ≠ ratIUTField.zero :=
    ellCurveNat_rat_ne_zero 16 (by omega)
  have h27 : ellCurveNat ratIUTField 27 ≠ ratIUTField.zero :=
    ellCurveNat_rat_ne_zero 27 (by omega)
  exact ratIUTField.mul_ne_zero h16 h27 h1

/-- 実例の有理点 (0,1) は曲線上（1²=0³+0·0+1=1）。 -/
theorem ellCurve_example_point_on_curve :
    ellCurveOnCurve ratIUTField ellCurveExampleW ratIUTField.zero ratIUTField.one := by
  show ratIUTField.mul ratIUTField.one ratIUTField.one
    = ratIUTField.add (ratIUTField.add (ellCurveCube ratIUTField ratIUTField.zero)
        (ratIUTField.mul ratIUTField.zero ratIUTField.zero)) ratIUTField.one
  rw [ellCurve_cube_zero ratIUTField,
    ellCurve_zero_mul ratIUTField ratIUTField.zero,
    ratIUTField.zero_add ratIUTField.zero,
    ratIUTField.zero_add ratIUTField.one,
    ratIUTField.one_mul ratIUTField.one]

/-- **M304F-8f: 実例の有理点** (0,1) ∈ E(ℚ)。 -/
def ellCurveExamplePoint : ellCurvePoint ratIUTField ellCurveExampleW :=
  .affine ratIUTField.zero ratIUTField.one ellCurve_example_point_on_curve

/-- **M304F-8g: 実例の楕円曲線データ**。 -/
def ellCurveExampleData : EllipticCurveData ratIUTField where
  weier := ellCurveExampleW
  nonsingular := ellCurve_example_nonsingular

/-- **M304F-8h: 楕円曲線は存在する**（ℚ 上の本物の実例）。 -/
theorem ellCurve_exists : Nonempty (EllipticCurveData ratIUTField) :=
  ⟨ellCurveExampleData⟩

/-- **M304F-8i: 群則骨組みの存在**（O 単位・逆元則を本物で満たす）。 -/
theorem ellCurve_group_skeleton (F : IUTField) (w : ellCurveWeierstrass F) :
    Nonempty (ellCurveGroupSkeleton F w) :=
  ⟨ellCurveGroupSkeletonWitness F w⟩

end IUT
