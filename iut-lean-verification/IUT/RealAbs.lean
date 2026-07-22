/-
# M127F: 実数の絶対値 — 逆三角不等式と正則性

柱C（issue #37）「ℝ の自前構成」の第五段（M115F ℚ → M117F 正則列 →
M120F 床関数 → M123F 乗法に続く）。順序・完備性の前提部品となる
**実数の絶対値 rabs**（点ごと qAbs）とその法則。

  * M127F-1 `intAbs_le_of` / `intAbs_sub_intAbs` — Int の逆三角不等式
    ||x| − |y|| ≤ |x − y|（符号 4 場合の cases + omega、外側は
    「t ≤ M かつ −t ≤ M なら |t| ≤ M」の片側化補題で閉じる）
  * M127F-2 `qAbs_abs_sub_abs` — **有理数の逆三角不等式**
    ||a| − |b|| ≤ |a − b|。qAbs は分母保存（prAbs は分子のみ絶対値）
    なので代表レベルで同分母となり、|num·den'| = |num|·den' の
    乗法性で Int の逆三角に直結する
  * M127F-3 `rabs` — 実数の絶対値（点ごと qAbs、添字加速なし）。
    正則性は ||x_m| − |x_n|| ≤ |x_m − x_n| ≤ u_m + u_n の 2 段 trans
  * M127F-4 法則 — `rabs_congr`（≈ との両立）・`rabs_neg`・`rabs_zero`・
    `qToReal_abs`（埋め込みとの両立）・`rabs_add_le`（三角不等式の
    点ごと witness 形、添字が両辺 2n+1 で自動的に揃う）・
    `rabs_mul`（乗法性、rBound の qAbs 冪等性で添字が揃う）・
    `rabs_nonneg_seq`（非負性の点ごと witness 形）
  * M127F-5 `RealAbsData` — 総括

意義: 柱C（#37）順序・完備性の前提部品。||a|−|b|| ≤ |a−b|
（Int → ℚ → ℝ の 3 段持ち上げ）で点ごと qAbs が正則性を保つ。
乗法との両立は rBound の qAbs 冪等性（`qAbs_idem` の Nat 等式化）で
添字が自動的に揃う。

正直申告: `rabs_add_le`・`rabs_nonneg_seq` は realEq/順序による総括形
ではなく点ごと witness 形（実数の順序 x ≤ y は次層で導入されるため）。
rBound (rabs x) = rBound x は defeq では通らず（qFloorNat の中の
qAbs (qAbs …) の書き換えが必要）、`rBound_rabs` の Nat 等式を経由した。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealMul

namespace IUT

/-! ## M127F-1: Int の逆三角不等式 -/

/-- **M127F-1a: 絶対値の片側化** — t ≤ M かつ −t ≤ M なら |t| ≤ M
    （t の符号で cases、choice なし）。 -/
theorem intAbs_le_of {t M : Int} (h1 : t ≤ M) (h2 : -t ≤ M) :
    intAbs t ≤ M := by
  cases Int.le_total t 0 with
  | inl h =>
    rw [intAbs_of_nonpos h]
    exact h2
  | inr h =>
    rw [intAbs_of_nonneg h]
    exact h1

/-- **定理 (M127F-1b): Int の逆三角不等式** ||x| − |y|| ≤ |x − y|
    （外側は片側化補題、内側は x・y の符号 4 場合の cases + omega、
    |x−y| は原子として ±(x−y) ≤ |x−y| の 2 事実だけで線形に閉じる）。 -/
theorem intAbs_sub_intAbs (x y : Int) :
    intAbs (intAbs x - intAbs y) ≤ intAbs (x - y) := by
  have h1 := int_le_intAbs (x - y)
  have h2 := int_neg_le_intAbs (x - y)
  apply intAbs_le_of
  · cases Int.le_total x 0 with
    | inl hx =>
      rw [intAbs_of_nonpos hx]
      cases Int.le_total y 0 with
      | inl hy =>
        rw [intAbs_of_nonpos hy]
        omega
      | inr hy =>
        rw [intAbs_of_nonneg hy]
        omega
    | inr hx =>
      rw [intAbs_of_nonneg hx]
      cases Int.le_total y 0 with
      | inl hy =>
        rw [intAbs_of_nonpos hy]
        omega
      | inr hy =>
        rw [intAbs_of_nonneg hy]
        omega
  · cases Int.le_total x 0 with
    | inl hx =>
      rw [intAbs_of_nonpos hx]
      cases Int.le_total y 0 with
      | inl hy =>
        rw [intAbs_of_nonpos hy]
        omega
      | inr hy =>
        rw [intAbs_of_nonneg hy]
        omega
    | inr hx =>
      rw [intAbs_of_nonneg hx]
      cases Int.le_total y 0 with
      | inl hy =>
        rw [intAbs_of_nonpos hy]
        omega
      | inr hy =>
        rw [intAbs_of_nonneg hy]
        omega

/-! ## M127F-2: 有理数の逆三角不等式 -/

/-- **定理 (M127F-2a): 有理数の逆三角不等式** ||a| − |b|| ≤ |a − b|。
    qAbs は分母保存なので代表レベルで両辺の分母が x.den·y.den に一致し、
    |x.num·y.den| = |x.num|·y.den（乗法性 + 正分母）の書き換えで
    Int の逆三角 `intAbs_sub_intAbs` の交差積形に直結する。 -/
theorem qAbs_abs_sub_abs (a b : QRat) :
    qLe (qAbs (qAdd (qAbs a) (qNeg (qAbs b)))) (qAbs (qAdd a (qNeg b))) := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  show intAbs (intAbs x.num * y.den + -(intAbs y.num) * x.den)
      * (x.den * y.den)
    ≤ intAbs (x.num * y.den + -y.num * x.den) * (x.den * y.den)
  have eX : intAbs (x.num * y.den) = intAbs x.num * y.den := by
    rw [intAbs_mul, intAbs_of_nonneg (Int.le_of_lt y.den_pos)]
  have eY : intAbs (y.num * x.den) = intAbs y.num * x.den := by
    rw [intAbs_mul, intAbs_of_nonneg (Int.le_of_lt x.den_pos)]
  have core := intAbs_sub_intAbs (x.num * y.den) (y.num * x.den)
  rw [eX, eY] at core
  have e1 : intAbs x.num * y.den + -(intAbs y.num) * x.den
      = intAbs x.num * y.den - intAbs y.num * x.den := by
    rw [Int.neg_mul]
    omega
  have e2 : x.num * y.den + -y.num * x.den
      = x.num * y.den - y.num * x.den := by
    rw [Int.neg_mul]
    omega
  rw [e1, e2]
  exact Int.mul_le_mul_of_nonneg_right core
    (Int.le_of_lt (Int.mul_pos x.den_pos y.den_pos))

/-! ## M127F-3: 実数の絶対値 -/

/-- **M127F-3a: 実数の絶対値** — 点ごと qAbs（添字加速なし）。
    正則性は逆三角 ||x_m| − |x_n|| ≤ |x_m − x_n| ≤ u_m + u_n。 -/
def rabs (x : RReal) : RReal where
  seq := fun n => qAbs (x.seq n)
  reg := by
    intro m n
    exact qLe_trans _ _ _ (qAbs_abs_sub_abs (x.seq m) (x.seq n)) (x.reg m n)

/-! ## M127F-4: 法則 -/

/-- **定理 (M127F-4a): ≈ との両立** — x ≈ y なら |x| ≈ |y|
    （点ごと逆三角 + h n の trans、ε-消去不要）。 -/
theorem rabs_congr {x y : RReal} (h : realEq x y) :
    realEq (rabs x) (rabs y) := by
  intro n
  exact qLe_trans _ _ _ (qAbs_abs_sub_abs (x.seq n) (y.seq n)) (h n)

/-- **定理 (M127F-4b): 反元との両立** |−x| ≈ |x|（点ごと qAbs_neg で
    列が等しい）。 -/
theorem rabs_neg (x : RReal) : realEq (rabs (realNeg x)) (rabs x) :=
  realEq_of_seq_eq (fun n => qAbs_neg (x.seq n))

/-- **定理 (M127F-4c): 零の絶対値** |0| ≈ 0（点ごと qAbs_zero）。 -/
theorem rabs_zero : realEq (rabs realZero) realZero :=
  realEq_of_seq_eq (fun _ => qAbs_zero)

/-- **定理 (M127F-4d): 埋め込みとの両立** |q↑| ≈ (|q|)↑
    （定数列は点ごと rfl）。 -/
theorem qToReal_abs (q : QRat) :
    realEq (rabs (qToReal q)) (qToReal (qAbs q)) :=
  realEq_of_seq_eq (fun _ => rfl)

/-- **定理 (M127F-4e): 三角不等式（点ごと witness 形）** —
    |x + y| の第 n 項 ≤ |x| + |y| の第 n 項。両辺とも添字 2n+1 の
    評価なので qAbs_add_le がそのまま効く（実数順序は次層）。 -/
theorem rabs_add_le (x y : RReal) (n : Nat) :
    qLe ((rabs (realAdd x y)).seq n) ((realAdd (rabs x) (rabs y)).seq n) :=
  qAbs_add_le (x.seq (2 * n + 1)) (y.seq (2 * n + 1))

/-- **M127F-4f: intAbs の冪等性** ||a|| = |a|（|a| ≥ 0 に nonneg 展開）。 -/
theorem intAbs_idem (a : Int) : intAbs (intAbs a) = intAbs a :=
  intAbs_of_nonneg (intAbs_nonneg a)

/-- **M127F-4g: qAbs の冪等性** ||a|| = |a|（代表 + intAbs_idem）。 -/
theorem qAbs_idem (a : QRat) : qAbs (qAbs a) = qAbs a := by
  induction a using Quot.ind; rename_i x
  exact congrArg (Quot.mk ratRel) (preRat_ext (intAbs_idem x.num) rfl)

/-- **定理 (M127F-4h): 標準上界の qAbs 不変性** rBound |x| = rBound x
    （qFloorNat の中の qAbs (qAbs x₀) を冪等性で潰す Nat 等式）。 -/
theorem rBound_rabs (x : RReal) : rBound (rabs x) = rBound x := by
  show qFloorNat (qAbs (qAbs (x.seq 0))) + 3 = qFloorNat (qAbs (x.seq 0)) + 3
  rw [qAbs_idem]

/-- **定理 (M127F-4i): 乗法性** |x·y| ≈ |x|·|y| — rBound の qAbs 不変性で
    両辺の添字スケール K が一致し、点ごと qAbs_mul で列が等しい。 -/
theorem rabs_mul (x y : RReal) :
    realEq (rabs (rmul x y)) (rmul (rabs x) (rabs y)) := by
  apply realEq_of_seq_eq
  intro n
  show qAbs (qMul (x.seq (mulIdx (rBound x + rBound y) n))
      (y.seq (mulIdx (rBound x + rBound y) n)))
    = qMul (qAbs (x.seq (mulIdx (rBound (rabs x) + rBound (rabs y)) n)))
      (qAbs (y.seq (mulIdx (rBound (rabs x) + rBound (rabs y)) n)))
  rw [rBound_rabs x, rBound_rabs y, qAbs_mul]

/-- **定理 (M127F-4j): 非負性（点ごと witness 形）** 0 ≤ |x| の各項。 -/
theorem rabs_nonneg_seq (x : RReal) (n : Nat) :
    qLe ratRing.zero ((rabs x).seq n) :=
  qAbs_nonneg (x.seq n)

/-! ## M127F-5: 総括 -/

/-- **M127F-5a: 総括** — 実数の絶対値の法則束（≈ の下 + 点ごと witness）。 -/
structure RealAbsData where
  /-- ≈ との両立。 -/
  abs_congr : ∀ {x y : RReal}, realEq x y → realEq (rabs x) (rabs y)
  /-- 反元との両立 |−x| ≈ |x|。 -/
  abs_neg : ∀ x : RReal, realEq (rabs (realNeg x)) (rabs x)
  /-- 零の絶対値 |0| ≈ 0。 -/
  abs_zero : realEq (rabs realZero) realZero
  /-- 埋め込みとの両立 |q↑| ≈ (|q|)↑。 -/
  embed_abs : ∀ q : QRat, realEq (rabs (qToReal q)) (qToReal (qAbs q))
  /-- 三角不等式（点ごと witness 形）。 -/
  abs_add_le : ∀ (x y : RReal) (n : Nat),
    qLe ((rabs (realAdd x y)).seq n) ((realAdd (rabs x) (rabs y)).seq n)
  /-- 乗法性 |x·y| ≈ |x|·|y|。 -/
  abs_mul : ∀ x y : RReal, realEq (rabs (rmul x y)) (rmul (rabs x) (rabs y))
  /-- 非負性（点ごと witness 形）。 -/
  abs_nonneg : ∀ (x : RReal) (n : Nat), qLe ratRing.zero ((rabs x).seq n)

/-- **M127F-5b: witness**。 -/
def realAbsData : RealAbsData where
  abs_congr := rabs_congr
  abs_neg := rabs_neg
  abs_zero := rabs_zero
  embed_abs := qToReal_abs
  abs_add_le := rabs_add_le
  abs_mul := rabs_mul
  abs_nonneg := rabs_nonneg_seq

/-- **M127F-5c: 存在**。 -/
theorem realAbs_exists : Nonempty RealAbsData := ⟨realAbsData⟩

end IUT
