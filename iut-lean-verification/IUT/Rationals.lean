/-
  IUT/Rationals.lean — M115F: 有理数体 ℚ の構成 — 柱C ℝ 基盤・第一段

  * M115F-1 `PreRat` / `ratRel` — 前分数（分子・正分母）と交差積関係
    a₁/d₁ ~ a₂/d₂ ⟺ a₁d₂ = a₂d₁（既約化なし）。推移律は正分母 d₂ による
    消去（`int_mul_cancel_right`: (a−b)d = 0 と `Int.mul_eq_zero` に帰着）
  * M115F-2 `prAdd` / `prNeg` / `prMul` / `prZero` / `prOne` — 代表演算と
    片側ずつの well-definedness（交差積の恒等式、4 因子入れ替え補題で整理）
  * M115F-3 `QRat` / `qAdd` / `qNeg` / `qMul` / `ratRing` — Quot 商と
    **ℚ は可換環**（分母が一致する法則は PreRat の等式 + congrArg、
    neg_add / left_distrib は分母が真に異なるため `prScale` 経由の
    Quot.sound で落とす）
  * M115F-4 `ratOfInt` / `quot_exact_rat` / `ratOfInt_inj` — **ℤ → ℚ は
    単射環準同型**（分離性は propext lift の標準トリック、Quot.exact 不使用）
  * M115F-5 `prLe` / `qLe` — 順序（交差積 ≤、well-definedness は分母消去で
    propext lift）と全法則: refl / trans / antisym / total / 加法両立 /
    非負積閉性
  * M115F-6 `prInv` / `qInv` / `qMul_inv` — 逆元（natAbs 分母 + 符号分子、
    x.num = 0 は prZero に全域化）と**体の公理（witness 形）**
  * M115F-7 `prAbs` / `qAbs` / `qAbs_add_le` / `qAbs_mul` — 絶対値・
    三角不等式・乗法性
  * M115F-8 `rat_archimedean` — アルキメデス性（代表ごとの witness 形:
    x ≤ |num x| は den ≥ 1 から）
  * M115F-9 `RatFieldData` — 総括レコードと witness

  意義: 柱C（#37）の共通基盤 ℝ 自前構成の第一段。交差積 Quot 商による
  ℚ = CRing + 全順序 + witness 付き逆元 + アルキメデス性。次層で
  Bishop 流正則列による ℝ へ。

  正直申告: 商上のゼロ判定選言（∀ q : QRat, q = 0 ∨ q ≠ 0）は排中律が
  要るため対象外。逆元の体公理は代表 witness 形（x.num ≠ 0 を仮定に取る）。
  アルキメデス性も商から Nat を choice なしで取り出せないため代表 witness 形。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.Ring

namespace IUT

/-! ## Int 演算の補助補題（omega は変数積を扱えないため明示計算） -/

/-- 右 2 因子の入れ替え a·b·c = a·c·b。 -/
theorem int_mul_right_swap (a b c : Int) : a * b * c = a * c * b := by
  rw [Int.mul_assoc, Int.mul_comm b c, ← Int.mul_assoc]

/-- 4 因子の対角入れ替え a·b·(c·d) = a·d·(c·b)。 -/
theorem int_mul_mul_swap (a b c d : Int) : a * b * (c * d) = a * d * (c * b) := by
  have h : b * (c * d) = d * (c * b) := by
    rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm b c, Int.mul_comm d c,
      Int.mul_assoc, Int.mul_assoc, Int.mul_comm b d]
  rw [Int.mul_assoc, h, ← Int.mul_assoc]

/-- 4 因子の中間入れ替え a·b·(c·d) = a·c·(b·d)。 -/
theorem int_mul_mul_swap' (a b c d : Int) : a * b * (c * d) = a * c * (b * d) := by
  have h : b * (c * d) = c * (b * d) := by
    rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm b c]
  rw [Int.mul_assoc, h, ← Int.mul_assoc]

/-- **消去補題**: 正の d で右から割れる（(a−b)d = 0 と `Int.mul_eq_zero`）。 -/
theorem int_mul_cancel_right {a b : Int} (d : Int) (hd : 0 < d)
    (h : a * d = b * d) : a = b := by
  have h1 : (a - b) * d = 0 := by rw [Int.sub_mul, h, Int.sub_self]
  cases Int.mul_eq_zero.mp h1 with
  | inl h2 => omega
  | inr h2 => omega

/-- **順序の消去補題**: 正の d で右から割っても ≤ は保存。 -/
theorem int_le_cancel_right {a b : Int} (d : Int) (hd : 0 < d)
    (h : a * d ≤ b * d) : a ≤ b := by
  cases Int.lt_or_le b a with
  | inl hba => exact absurd h (Int.not_le.mpr (Int.mul_lt_mul_of_pos_right hba hd))
  | inr hab => exact hab

/-- 正×正の積が正なら左因子は正（符号伝播、choice なしの Or 場合分け）。 -/
theorem int_pos_of_mul_pos {a b : Int} (hb : 0 < b) (h : 0 < a * b) : 0 < a := by
  cases Int.lt_or_le 0 a with
  | inl h1 => exact h1
  | inr h1 =>
    have h2 : a * b ≤ 0 * b := Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hb)
    rw [Int.zero_mul] at h2
    exact absurd h (Int.not_lt.mpr h2)

/-- 正因子との積が負なら左因子は負。 -/
theorem int_neg_of_mul_neg {a b : Int} (hb : 0 < b) (h : a * b < 0) : a < 0 := by
  cases Int.lt_or_le a 0 with
  | inl h1 => exact h1
  | inr h1 =>
    have h2 : 0 ≤ a * b := Int.mul_nonneg h1 (Int.le_of_lt hb)
    exact absurd h (Int.not_lt.mpr h2)

/-- 正因子との積が非負なら左因子は非負。 -/
theorem int_nonneg_of_mul_nonneg {a b : Int} (hb : 0 < b) (h : 0 ≤ a * b) :
    0 ≤ a := by
  cases Int.lt_or_le a 0 with
  | inl h1 =>
    have h2 : a * b < 0 := Int.mul_neg_of_neg_of_pos h1 hb
    exact absurd h (Int.not_le.mpr h2)
  | inr h1 => exact h1

/-! ## Int の絶対値（if 式、choice なし） -/

/-- Int の絶対値（`if 0 ≤ a`、DecidableEq ベースで choice なし）。 -/
def intAbs (a : Int) : Int := if 0 ≤ a then a else -a

/-- 非負なら |a| = a。 -/
theorem intAbs_of_nonneg {a : Int} (h : 0 ≤ a) : intAbs a = a := if_pos h

/-- 非正なら |a| = −a（a = 0 の縁も含む）。 -/
theorem intAbs_of_nonpos {a : Int} (h : a ≤ 0) : intAbs a = -a := by
  cases Int.lt_or_le a 0 with
  | inl h1 => exact if_neg (Int.not_le.mpr h1)
  | inr h1 =>
    have h2 : a = 0 := by omega
    rw [h2, show intAbs 0 = 0 from if_pos (Int.le_refl 0)]
    omega

/-- a ≤ |a|。 -/
theorem int_le_intAbs (a : Int) : a ≤ intAbs a := by
  cases Int.lt_or_le a 0 with
  | inl h1 => rw [intAbs_of_nonpos (Int.le_of_lt h1)]; omega
  | inr h1 => rw [intAbs_of_nonneg h1]; exact Int.le_refl a

/-- −a ≤ |a|。 -/
theorem int_neg_le_intAbs (a : Int) : -a ≤ intAbs a := by
  cases Int.lt_or_le a 0 with
  | inl h1 => rw [intAbs_of_nonpos (Int.le_of_lt h1)]; exact Int.le_refl _
  | inr h1 => rw [intAbs_of_nonneg h1]; omega

/-- 0 ≤ |a|。 -/
theorem intAbs_nonneg (a : Int) : 0 ≤ intAbs a := by
  cases Int.lt_or_le a 0 with
  | inl h1 => rw [intAbs_of_nonpos (Int.le_of_lt h1)]; omega
  | inr h1 => rw [intAbs_of_nonneg h1]; exact h1

/-- **絶対値の乗法性** |ab| = |a||b|（符号 4 場合の Or 分解）。 -/
theorem intAbs_mul (a b : Int) : intAbs (a * b) = intAbs a * intAbs b := by
  cases Int.lt_or_le a 0 with
  | inl ha =>
    cases Int.lt_or_le b 0 with
    | inl hb =>
      rw [intAbs_of_nonneg (Int.le_of_lt (Int.mul_pos_of_neg_of_neg ha hb)),
        intAbs_of_nonpos (Int.le_of_lt ha), intAbs_of_nonpos (Int.le_of_lt hb),
        Int.neg_mul_neg]
    | inr hb =>
      have h1 : a * b ≤ 0 := by
        have h2 : a * b ≤ 0 * b :=
          Int.mul_le_mul_of_nonneg_right (Int.le_of_lt ha) hb
        rw [Int.zero_mul] at h2
        exact h2
      rw [intAbs_of_nonpos h1, intAbs_of_nonpos (Int.le_of_lt ha),
        intAbs_of_nonneg hb, Int.neg_mul]
  | inr ha =>
    cases Int.lt_or_le b 0 with
    | inl hb =>
      have h1 : a * b ≤ 0 := by
        have h2 : a * b ≤ a * 0 :=
          Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hb) ha
        rw [Int.mul_zero] at h2
        exact h2
      rw [intAbs_of_nonpos h1, intAbs_of_nonneg ha,
        intAbs_of_nonpos (Int.le_of_lt hb), Int.mul_neg]
    | inr hb =>
      rw [intAbs_of_nonneg (Int.mul_nonneg ha hb), intAbs_of_nonneg ha,
        intAbs_of_nonneg hb]

/-! ## M115F-1: 前分数と交差積関係 -/

/-- **M115F-1a: 前分数**（分子は任意の Int、分母は正の Int）。 -/
structure PreRat where
  /-- 分子。 -/
  num : Int
  /-- 分母。 -/
  den : Int
  /-- 分母は正。 -/
  den_pos : 0 < den

/-- PreRat の外延性（den_pos は Prop なので proof irrelevance で消える）。 -/
theorem preRat_ext : ∀ {x y : PreRat}, x.num = y.num → x.den = y.den → x = y
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

/-- **M115F-1b: 交差積関係** a₁/d₁ ~ a₂/d₂ ⟺ a₁d₂ = a₂d₁（既約化なし）。 -/
def ratRel (x y : PreRat) : Prop := x.num * y.den = y.num * x.den

/-- 反射律。 -/
theorem ratRel_refl (x : PreRat) : ratRel x x := rfl

/-- 対称律（等式の交換）。 -/
theorem ratRel_symm {x y : PreRat} (h : ratRel x y) : ratRel y x := by
  have h' : x.num * y.den = y.num * x.den := h
  show y.num * x.den = x.num * y.den
  exact h'.symm

/-- **M115F-1c: 推移律** — 両辺に d₂ を掛けて a₂ 経由で繋ぎ、正分母
    d₂ を `int_mul_cancel_right` で消す。 -/
theorem ratRel_trans {x y z : PreRat} (h1 : ratRel x y) (h2 : ratRel y z) :
    ratRel x z := by
  have h1' : x.num * y.den = y.num * x.den := h1
  have h2' : y.num * z.den = z.num * y.den := h2
  show x.num * z.den = z.num * x.den
  apply int_mul_cancel_right y.den y.den_pos
  rw [int_mul_right_swap x.num z.den y.den, h1',
    int_mul_right_swap z.num x.den y.den, ← h2',
    int_mul_right_swap y.num x.den z.den]

/-! ## M115F-2: 代表演算 -/

/-- **M115F-2a: 加法の代表** a/d + b/e = (ae + bd)/(de)。 -/
def prAdd (x y : PreRat) : PreRat :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den,
    Int.mul_pos x.den_pos y.den_pos⟩

/-- **M115F-2b: 反元の代表**。 -/
def prNeg (x : PreRat) : PreRat := ⟨-x.num, x.den, x.den_pos⟩

/-- **M115F-2c: 乗法の代表**。 -/
def prMul (x y : PreRat) : PreRat :=
  ⟨x.num * y.num, x.den * y.den, Int.mul_pos x.den_pos y.den_pos⟩

/-- 0 の代表 0/1。 -/
def prZero : PreRat := ⟨0, 1, by omega⟩

/-- 1 の代表 1/1。 -/
def prOne : PreRat := ⟨1, 1, by omega⟩

/-- 正の c による分子分母の同時スケール（左分配の Quot.sound 用）。 -/
def prScale (c : Int) (hc : 0 < c) (x : PreRat) : PreRat :=
  ⟨c * x.num, c * x.den, Int.mul_pos hc x.den_pos⟩

/-- スケールは関係を変えない（cn·d = n·(cd)）。 -/
theorem ratRel_scale (c : Int) (hc : 0 < c) (x : PreRat) :
    ratRel (prScale c hc x) x := by
  show c * x.num * x.den = x.num * (c * x.den)
  rw [Int.mul_comm c x.num, Int.mul_assoc]

/-! ## M115F-2d: 演算の well-definedness（片側ずつ、交差積の恒等式） -/

/-- 加法は第 2 引数の関係を保つ。 -/
theorem ratRel_add_left (x : PreRat) {y y' : PreRat} (h : ratRel y y') :
    ratRel (prAdd x y) (prAdd x y') := by
  have h' : y.num * y'.den = y'.num * y.den := h
  show (x.num * y.den + y.num * x.den) * (x.den * y'.den)
    = (x.num * y'.den + y'.num * x.den) * (x.den * y.den)
  rw [Int.add_mul, Int.add_mul,
    int_mul_mul_swap x.num y.den x.den y'.den,
    int_mul_mul_swap y.num x.den x.den y'.den, h',
    int_mul_mul_swap y'.num y.den x.den x.den]

/-- 加法は第 1 引数の関係を保つ。 -/
theorem ratRel_add_right (y : PreRat) {x x' : PreRat} (h : ratRel x x') :
    ratRel (prAdd x y) (prAdd x' y) := by
  have h' : x.num * x'.den = x'.num * x.den := h
  show (x.num * y.den + y.num * x.den) * (x'.den * y.den)
    = (x'.num * y.den + y.num * x'.den) * (x.den * y.den)
  rw [Int.add_mul, Int.add_mul,
    int_mul_mul_swap' x.num y.den x'.den y.den, h',
    ← int_mul_mul_swap' x'.num y.den x.den y.den,
    int_mul_mul_swap' y.num x.den x'.den y.den]

/-- 反元は関係を保つ。 -/
theorem ratRel_neg {x x' : PreRat} (h : ratRel x x') :
    ratRel (prNeg x) (prNeg x') := by
  have h' : x.num * x'.den = x'.num * x.den := h
  show -x.num * x'.den = -x'.num * x.den
  rw [Int.neg_mul, Int.neg_mul, h']

/-- 乗法は第 2 引数の関係を保つ。 -/
theorem ratRel_mul_left (x : PreRat) {y y' : PreRat} (h : ratRel y y') :
    ratRel (prMul x y) (prMul x y') := by
  have h' : y.num * y'.den = y'.num * y.den := h
  show x.num * y.num * (x.den * y'.den) = x.num * y'.num * (x.den * y.den)
  rw [int_mul_mul_swap' x.num y.num x.den y'.den, h',
    int_mul_mul_swap' x.num y'.num x.den y.den]

/-- 乗法は第 1 引数の関係を保つ。 -/
theorem ratRel_mul_right (y : PreRat) {x x' : PreRat} (h : ratRel x x') :
    ratRel (prMul x y) (prMul x' y) := by
  have h' : x.num * x'.den = x'.num * x.den := h
  show x.num * y.num * (x'.den * y.den) = x'.num * y.num * (x.den * y.den)
  rw [int_mul_mul_swap' x.num y.num x'.den y.den, h',
    int_mul_mul_swap' x'.num y.num x.den y.den]

/-! ## M115F-3: Quot 商 ℚ と環構造 -/

/-- **M115F-3a: ℚ の台** = PreRat / 交差積関係（Quot ベース）。 -/
def QRat := Quot ratRel

/-- **M115F-3b: 加法**（二重 Quot.lift、well-definedness は ratRel_add_*）。 -/
def qAdd (a b : QRat) : QRat :=
  Quot.lift
    (fun x => Quot.lift
      (fun y => Quot.mk ratRel (prAdd x y))
      (fun _ _ hy => Quot.sound (ratRel_add_left x hy)) b)
    (fun _ _ hx => by
      induction b using Quot.ind
      rename_i y
      exact Quot.sound (ratRel_add_right y hx)) a

/-- **M115F-3c: 反元**。 -/
def qNeg (a : QRat) : QRat :=
  Quot.lift (fun x => Quot.mk ratRel (prNeg x))
    (fun _ _ hx => Quot.sound (ratRel_neg hx)) a

/-- **M115F-3d: 乗法**。 -/
def qMul (a b : QRat) : QRat :=
  Quot.lift
    (fun x => Quot.lift
      (fun y => Quot.mk ratRel (prMul x y))
      (fun _ _ hy => Quot.sound (ratRel_mul_left x hy)) b)
    (fun _ _ hx => by
      induction b using Quot.ind
      rename_i y
      exact Quot.sound (ratRel_mul_right y hx)) a

/-- 加法の結合律（PreRat の等式 — 分母は Int.mul_assoc で一致）。 -/
theorem prAdd_assoc (x y z : PreRat) :
    prAdd (prAdd x y) z = prAdd x (prAdd y z) := by
  apply preRat_ext
  · show (x.num * y.den + y.num * x.den) * z.den + z.num * (x.den * y.den)
      = x.num * (y.den * z.den) + (y.num * z.den + z.num * y.den) * x.den
    rw [Int.add_mul, Int.add_mul, Int.add_assoc,
      Int.mul_assoc x.num y.den z.den,
      int_mul_right_swap y.num x.den z.den,
      int_mul_right_swap z.num y.den x.den,
      Int.mul_assoc z.num x.den y.den]
  · show x.den * y.den * z.den = x.den * (y.den * z.den)
    exact Int.mul_assoc x.den y.den z.den

/-- 加法の可換律（PreRat の等式）。 -/
theorem prAdd_comm (x y : PreRat) : prAdd x y = prAdd y x := by
  apply preRat_ext
  · show x.num * y.den + y.num * x.den = y.num * x.den + x.num * y.den
    exact Int.add_comm _ _
  · exact Int.mul_comm x.den y.den

/-- 左零元（PreRat の等式）。 -/
theorem prZero_add (x : PreRat) : prAdd prZero x = x := by
  apply preRat_ext
  · show 0 * x.den + x.num * 1 = x.num
    rw [Int.zero_mul, Int.mul_one, Int.zero_add]
  · show 1 * x.den = x.den
    exact Int.one_mul x.den

/-- 左反元（分母 d² ≠ 1 のため PreRat 等式では閉じず **Quot.sound 必須**）。 -/
theorem prNeg_add_rel (x : PreRat) : ratRel (prAdd (prNeg x) x) prZero := by
  show (-x.num * x.den + x.num * x.den) * 1 = 0 * (x.den * x.den)
  rw [Int.mul_one, Int.zero_mul, Int.neg_mul, Int.add_left_neg]

/-- 乗法の結合律（PreRat の等式）。 -/
theorem prMul_assoc (x y z : PreRat) :
    prMul (prMul x y) z = prMul x (prMul y z) := by
  apply preRat_ext
  · exact Int.mul_assoc x.num y.num z.num
  · exact Int.mul_assoc x.den y.den z.den

/-- 左単位元（PreRat の等式）。 -/
theorem prOne_mul (x : PreRat) : prMul prOne x = x := by
  apply preRat_ext
  · exact Int.one_mul x.num
  · exact Int.one_mul x.den

/-- 乗法の可換律（PreRat の等式）。 -/
theorem prMul_comm (x y : PreRat) : prMul x y = prMul y x := by
  apply preRat_ext
  · exact Int.mul_comm x.num y.num
  · exact Int.mul_comm x.den y.den

/-- 左分配は「x.den 倍スケール」との PreRat 等式に落ちる（分母が真に
    異なるため congrArg では閉じず、この等式 + ratRel_scale の
    **Quot.sound 経由必須**）。 -/
theorem prLeftDistrib_scale (x y z : PreRat) :
    prAdd (prMul x y) (prMul x z)
      = prScale x.den x.den_pos (prMul x (prAdd y z)) := by
  apply preRat_ext
  · show x.num * y.num * (x.den * z.den) + x.num * z.num * (x.den * y.den)
      = x.den * (x.num * (y.num * z.den + z.num * y.den))
    rw [Int.mul_add x.num, Int.mul_add x.den,
      int_mul_mul_swap' x.num y.num x.den z.den,
      int_mul_mul_swap' x.num z.num x.den y.den,
      ← Int.mul_assoc x.den x.num (y.num * z.den),
      ← Int.mul_assoc x.den x.num (z.num * y.den),
      Int.mul_comm x.den x.num]
  · show x.den * y.den * (x.den * z.den) = x.den * (x.den * (y.den * z.den))
    rw [int_mul_mul_swap' x.den y.den x.den z.den, Int.mul_assoc]

/-- **定理 (M115F-3e): ℚ は可換環** — 分母が一致する法則は代表の
    PreRat 等式 + congrArg、neg_add / left_distrib は Quot.sound。 -/
def ratRing : CRing where
  carrier := QRat
  add := qAdd
  zero := Quot.mk ratRel prZero
  neg := qNeg
  mul := qMul
  one := Quot.mk ratRel prOne
  add_assoc := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    exact congrArg (Quot.mk ratRel) (prAdd_assoc x y z)
  zero_add := by
    intro a
    induction a using Quot.ind; rename_i x
    exact congrArg (Quot.mk ratRel) (prZero_add x)
  neg_add := by
    intro a
    induction a using Quot.ind; rename_i x
    exact Quot.sound (prNeg_add_rel x)
  add_comm := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    exact congrArg (Quot.mk ratRel) (prAdd_comm x y)
  mul_assoc := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    exact congrArg (Quot.mk ratRel) (prMul_assoc x y z)
  one_mul := by
    intro a
    induction a using Quot.ind; rename_i x
    exact congrArg (Quot.mk ratRel) (prOne_mul x)
  mul_comm := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    exact congrArg (Quot.mk ratRel) (prMul_comm x y)
  left_distrib := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    show Quot.mk ratRel (prMul x (prAdd y z))
      = Quot.mk ratRel (prAdd (prMul x y) (prMul x z))
    rw [prLeftDistrib_scale x y z]
    exact (Quot.sound (ratRel_scale x.den x.den_pos (prMul x (prAdd y z)))).symm

/-! ## M115F-4: ℤ の埋め込みと単射性 -/

/-- 整数 n の代表 n/1。 -/
def intToPreRat (n : Int) : PreRat := ⟨n, 1, by omega⟩

/-- **M115F-4a: ℤ → ℚ は環準同型**（n ↦ n/1）。 -/
def ratOfInt : RingHom intRing ratRing where
  map := fun n => Quot.mk ratRel (intToPreRat n)
  map_add := fun (a b : Int) => by
    show Quot.mk ratRel (intToPreRat (a + b))
      = Quot.mk ratRel (prAdd (intToPreRat a) (intToPreRat b))
    apply congrArg (Quot.mk ratRel)
    apply preRat_ext
    · show a + b = a * 1 + b * 1
      rw [Int.mul_one, Int.mul_one]
    · show (1 : Int) = 1 * 1
      rw [Int.one_mul]
  map_mul := fun (a b : Int) => by
    show Quot.mk ratRel (intToPreRat (a * b))
      = Quot.mk ratRel (prMul (intToPreRat a) (intToPreRat b))
    apply congrArg (Quot.mk ratRel)
    apply preRat_ext
    · exact rfl
    · show (1 : Int) = 1 * 1
      rw [Int.one_mul]
  map_one := rfl

/-- **定理 (M115F-4b): 分離性** — mk x = mk y なら ratRel x y
    （propext lift の標準トリック、Quot.exact 不使用）。 -/
theorem quot_exact_rat {x y : PreRat}
    (h : Quot.mk ratRel x = Quot.mk ratRel y) : ratRel x y := by
  have hf : Quot.lift (ratRel x)
      (fun _ _ hxy => propext
        ⟨fun hfx => ratRel_trans hfx hxy,
         fun hfy => ratRel_trans hfy (ratRel_symm hxy)⟩)
      (Quot.mk ratRel x) := ratRel_refl x
  rw [h] at hf
  exact hf

/-- **定理 (M115F-4c): ℤ → ℚ は単射**（分離性で a·1 = b·1 に落とす）。 -/
theorem ratOfInt_inj (a b : Int) (h : ratOfInt.map a = ratOfInt.map b) :
    a = b := by
  have h1 : ratRel (intToPreRat a) (intToPreRat b) := quot_exact_rat h
  have h2 : a * 1 = b * 1 := h1
  omega

/-! ## M115F-5: 順序 -/

/-- **M115F-5a: 順序の代表** a/d ≤ b/e ⟺ ae ≤ bd。 -/
def prLe (x y : PreRat) : Prop := x.num * y.den ≤ y.num * x.den

/-- prLe は第 1 引数の関係で保存（分母消去）。 -/
theorem prLe_of_rel_left {x x' : PreRat} (hx : ratRel x x') (y : PreRat)
    (h : prLe x y) : prLe x' y := by
  have hx' : x.num * x'.den = x'.num * x.den := hx
  have h' : x.num * y.den ≤ y.num * x.den := h
  show x'.num * y.den ≤ y.num * x'.den
  apply int_le_cancel_right x.den x.den_pos
  have h2 : x.num * y.den * x'.den ≤ y.num * x.den * x'.den :=
    Int.mul_le_mul_of_nonneg_right h' (Int.le_of_lt x'.den_pos)
  rw [int_mul_right_swap x.num y.den x'.den, hx',
    int_mul_right_swap x'.num x.den y.den,
    int_mul_right_swap y.num x.den x'.den] at h2
  exact h2

/-- prLe は第 2 引数の関係で保存（分母消去）。 -/
theorem prLe_of_rel_right (x : PreRat) {y y' : PreRat} (hy : ratRel y y')
    (h : prLe x y) : prLe x y' := by
  have hy' : y.num * y'.den = y'.num * y.den := hy
  have h' : x.num * y.den ≤ y.num * x.den := h
  show x.num * y'.den ≤ y'.num * x.den
  apply int_le_cancel_right y.den y.den_pos
  have h2 : x.num * y.den * y'.den ≤ y.num * x.den * y'.den :=
    Int.mul_le_mul_of_nonneg_right h' (Int.le_of_lt y'.den_pos)
  rw [int_mul_right_swap x.num y.den y'.den,
    int_mul_right_swap y.num x.den y'.den, hy',
    int_mul_right_swap y'.num y.den x.den] at h2
  exact h2

/-- **M115F-5b: 商上の順序**（Prop 値の二重 Quot.lift、propext で両立）。 -/
def qLe (a b : QRat) : Prop :=
  Quot.lift
    (fun x => Quot.lift (fun y => prLe x y)
      (fun _ _ hy => propext
        ⟨fun h => prLe_of_rel_right x hy h,
         fun h => prLe_of_rel_right x (ratRel_symm hy) h⟩) b)
    (fun _ x' hx => by
      induction b using Quot.ind
      rename_i y
      exact propext
        ⟨fun h => prLe_of_rel_left hx y h,
         fun h => prLe_of_rel_left (ratRel_symm hx) y h⟩) a

/-- **M115F-5c: 反射律**。 -/
theorem qLe_refl (a : QRat) : qLe a a := by
  induction a using Quot.ind; rename_i x
  show x.num * x.den ≤ x.num * x.den
  exact Int.le_refl _

/-- **定理 (M115F-5d): 推移律**（中間分母 y.den の消去）。 -/
theorem qLe_trans (a b c : QRat) (h1 : qLe a b) (h2 : qLe b c) : qLe a c := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  induction c using Quot.ind; rename_i z
  have h1' : x.num * y.den ≤ y.num * x.den := h1
  have h2' : y.num * z.den ≤ z.num * y.den := h2
  show x.num * z.den ≤ z.num * x.den
  apply int_le_cancel_right y.den y.den_pos
  have ha : x.num * y.den * z.den ≤ y.num * x.den * z.den :=
    Int.mul_le_mul_of_nonneg_right h1' (Int.le_of_lt z.den_pos)
  have hb : y.num * z.den * x.den ≤ z.num * y.den * x.den :=
    Int.mul_le_mul_of_nonneg_right h2' (Int.le_of_lt x.den_pos)
  rw [int_mul_right_swap y.num x.den z.den] at ha
  have hc : x.num * y.den * z.den ≤ z.num * y.den * x.den :=
    Int.le_trans ha hb
  rw [int_mul_right_swap x.num y.den z.den,
    int_mul_right_swap z.num y.den x.den] at hc
  exact hc

/-- **定理 (M115F-5e): 反対称律**（Int.le_antisymm が ratRel を与え
    Quot.sound で商の等式に）。 -/
theorem qLe_antisym (a b : QRat) (h1 : qLe a b) (h2 : qLe b a) : a = b := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  have h1' : x.num * y.den ≤ y.num * x.den := h1
  have h2' : y.num * x.den ≤ x.num * y.den := h2
  exact Quot.sound (Int.le_antisymm h1' h2')

/-- **定理 (M115F-5f): 全順序性**（Int.le_total の Or 場合分け、choice なし）。 -/
theorem qLe_total (a b : QRat) : qLe a b ∨ qLe b a := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  cases Int.le_total (x.num * y.den) (y.num * x.den) with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr h

/-- **定理 (M115F-5g): 加法との両立** — 両辺に同じ元を足しても ≤ 保存。 -/
theorem qLe_add (a b c : QRat) (h : qLe a b) :
    qLe (qAdd a c) (qAdd b c) := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  induction c using Quot.ind; rename_i z
  have h' : x.num * y.den ≤ y.num * x.den := h
  show (x.num * z.den + z.num * x.den) * (y.den * z.den)
    ≤ (y.num * z.den + z.num * y.den) * (x.den * z.den)
  rw [Int.add_mul, Int.add_mul,
    int_mul_mul_swap' x.num z.den y.den z.den,
    int_mul_mul_swap' y.num z.den x.den z.den,
    int_mul_mul_swap z.num x.den y.den z.den,
    int_mul_mul_swap z.num y.den x.den z.den,
    Int.mul_comm y.den x.den]
  apply Int.add_le_add_right
  exact Int.mul_le_mul_of_nonneg_right h'
    (Int.mul_nonneg (Int.le_of_lt z.den_pos) (Int.le_of_lt z.den_pos))

/-- **定理 (M115F-5h): 非負積の閉性** — 0 ≤ x, 0 ≤ y なら 0 ≤ xy。 -/
theorem qLe_mul_nonneg (a b : QRat) (ha : qLe ratRing.zero a)
    (hb : qLe ratRing.zero b) : qLe ratRing.zero (qMul a b) := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  have ha' : (0 : Int) * x.den ≤ x.num * 1 := ha
  have hb' : (0 : Int) * y.den ≤ y.num * 1 := hb
  rw [Int.zero_mul, Int.mul_one] at ha'
  rw [Int.zero_mul, Int.mul_one] at hb'
  show (0 : Int) * (x.den * y.den) ≤ x.num * y.num * 1
  rw [Int.zero_mul, Int.mul_one]
  exact Int.mul_nonneg ha' hb'

/-! ## M115F-6: 逆元（witness 形の体公理） -/

/-- 逆元の分子（符号を分子から分母へ移す）。 -/
def prInvNum (x : PreRat) : Int := if 0 ≤ x.num then x.den else -x.den

/-- 逆元の分母 |num|。 -/
def prInvDen (x : PreRat) : Int := (x.num.natAbs : Int)

/-- num ≠ 0 なら逆元の分母は正。 -/
theorem prInvDen_pos {x : PreRat} (hz : x.num ≠ 0) : 0 < prInvDen x := by
  show 0 < (x.num.natAbs : Int)
  omega

/-- **M115F-6a: 逆元の代表** — num = 0 のときは prZero に全域化
    （Int の = は DecidableEq で choice なし）。 -/
def prInv (x : PreRat) : PreRat :=
  if hz : x.num = 0 then prZero
  else ⟨prInvNum x, prInvDen x, prInvDen_pos hz⟩

/-- num = 0 側の展開。 -/
theorem prInv_of_eq {x : PreRat} (hz : x.num = 0) : prInv x = prZero :=
  dif_pos hz

/-- num ≠ 0 側の展開。 -/
theorem prInv_of_ne {x : PreRat} (hz : x.num ≠ 0) :
    prInv x = ⟨prInvNum x, prInvDen x, prInvDen_pos hz⟩ :=
  dif_neg hz

/-- **定理 (M115F-6b): 逆元の well-definedness** — num = 0 ⟺ 相手も 0
    （交差積 + 正分母）、非零側は符号場合分け。 -/
theorem ratRel_inv {x y : PreRat} (h : ratRel x y) :
    ratRel (prInv x) (prInv y) := by
  have h' : x.num * y.den = y.num * x.den := h
  cases Decidable.em (x.num = 0) with
  | inl hz =>
    have h1 : y.num * x.den = 0 := by rw [← h', hz, Int.zero_mul]
    cases Int.mul_eq_zero.mp h1 with
    | inl h2 =>
      rw [prInv_of_eq hz, prInv_of_eq h2]
      exact ratRel_refl prZero
    | inr h2 =>
      have hd := x.den_pos
      exact absurd h2 (by omega)
  | inr hz =>
    have hy0 : y.num ≠ 0 := by
      intro hy
      have h'' : x.num * y.den = y.num * x.den := h
      rw [hy, Int.zero_mul] at h''
      cases Int.mul_eq_zero.mp h'' with
      | inl h1 => exact hz h1
      | inr h1 =>
        have hd := y.den_pos
        omega
    rw [prInv_of_ne hz, prInv_of_ne hy0]
    show prInvNum x * prInvDen y = prInvNum y * prInvDen x
    cases Int.lt_or_le x.num 0 with
    | inl hxneg =>
      have h1 : y.num * x.den < 0 := by
        rw [← h']
        exact Int.mul_neg_of_neg_of_pos hxneg y.den_pos
      have hyneg : y.num < 0 := int_neg_of_mul_neg x.den_pos h1
      rw [show prInvNum x = -x.den from if_neg (Int.not_le.mpr hxneg),
        show prInvNum y = -y.den from if_neg (Int.not_le.mpr hyneg),
        show prInvDen y = -y.num from
          Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hyneg),
        show prInvDen x = -x.num from
          Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hxneg),
        Int.neg_mul_neg, Int.neg_mul_neg,
        Int.mul_comm x.den y.num, Int.mul_comm y.den x.num]
      exact h'.symm
    | inr hxnn =>
      have hxpos : 0 < x.num := by omega
      have h1 : 0 < y.num * x.den := by
        rw [← h']
        exact Int.mul_pos hxpos y.den_pos
      have hypos : 0 < y.num := int_pos_of_mul_pos x.den_pos h1
      rw [show prInvNum x = x.den from if_pos hxnn,
        show prInvNum y = y.den from if_pos (Int.le_of_lt hypos),
        show prInvDen y = y.num from Int.natAbs_of_nonneg (Int.le_of_lt hypos),
        show prInvDen x = x.num from Int.natAbs_of_nonneg hxnn,
        Int.mul_comm x.den y.num, Int.mul_comm y.den x.num]
      exact h'.symm

/-- **M115F-6c: 商上の逆元**。 -/
def qInv (a : QRat) : QRat :=
  Quot.lift (fun x => Quot.mk ratRel (prInv x))
    (fun _ _ hx => Quot.sound (ratRel_inv hx)) a

/-- **定理 (M115F-6d): 体の公理（witness 形）** — num ≠ 0 なる代表 x に
    対し x · x⁻¹ = 1。符号の場合分けは Or の cases（choice なし）。
    商上のゼロ判定選言そのものは排中律のため対象外（正直申告）。 -/
theorem qMul_inv (x : PreRat) (hx : x.num ≠ 0) :
    qMul (Quot.mk ratRel x) (qInv (Quot.mk ratRel x))
      = Quot.mk ratRel prOne := by
  show Quot.mk ratRel (prMul x (prInv x)) = Quot.mk ratRel prOne
  rw [prInv_of_ne hx]
  apply Quot.sound
  show x.num * prInvNum x * 1 = 1 * (x.den * prInvDen x)
  rw [Int.mul_one, Int.one_mul]
  cases Int.lt_or_le x.num 0 with
  | inl hneg =>
    rw [show prInvNum x = -x.den from if_neg (Int.not_le.mpr hneg),
      show prInvDen x = -x.num from
        Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg),
      Int.mul_neg, Int.mul_neg, Int.mul_comm x.num x.den]
  | inr hnn =>
    rw [show prInvNum x = x.den from if_pos hnn,
      show prInvDen x = x.num from Int.natAbs_of_nonneg hnn,
      Int.mul_comm x.num x.den]

/-! ## M115F-7: 絶対値 -/

/-- **M115F-7a: 絶対値の代表**（分子の絶対値、分母はそのまま）。 -/
def prAbs (x : PreRat) : PreRat := ⟨intAbs x.num, x.den, x.den_pos⟩

/-- **M115F-7b: 絶対値の well-definedness**（符号は交差積 + 正分母で伝播）。 -/
theorem ratRel_abs {x y : PreRat} (h : ratRel x y) :
    ratRel (prAbs x) (prAbs y) := by
  have h' : x.num * y.den = y.num * x.den := h
  show intAbs x.num * y.den = intAbs y.num * x.den
  cases Int.lt_or_le x.num 0 with
  | inl hx =>
    have h1 : y.num * x.den < 0 := by
      rw [← h']
      exact Int.mul_neg_of_neg_of_pos hx y.den_pos
    have hy : y.num < 0 := int_neg_of_mul_neg x.den_pos h1
    rw [intAbs_of_nonpos (Int.le_of_lt hx), intAbs_of_nonpos (Int.le_of_lt hy),
      Int.neg_mul, Int.neg_mul, h']
  | inr hx =>
    have h1 : 0 ≤ y.num * x.den := by
      rw [← h']
      exact Int.mul_nonneg hx (Int.le_of_lt y.den_pos)
    have hy : 0 ≤ y.num := int_nonneg_of_mul_nonneg x.den_pos h1
    rw [intAbs_of_nonneg hx, intAbs_of_nonneg hy]
    exact h'

/-- **M115F-7c: 商上の絶対値**。 -/
def qAbs (a : QRat) : QRat :=
  Quot.lift (fun x => Quot.mk ratRel (prAbs x))
    (fun _ _ hx => Quot.sound (ratRel_abs hx)) a

/-- **定理 (M115F-7d): 三角不等式** |x + y| ≤ |x| + |y|（分母が共通なので
    分子の不等式に帰着、符号は Or の cases）。 -/
theorem qAbs_add_le (a b : QRat) :
    qLe (qAbs (qAdd a b)) (qAdd (qAbs a) (qAbs b)) := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  have hA : x.num * y.den ≤ intAbs x.num * y.den :=
    Int.mul_le_mul_of_nonneg_right (int_le_intAbs x.num) (Int.le_of_lt y.den_pos)
  have hB : y.num * x.den ≤ intAbs y.num * x.den :=
    Int.mul_le_mul_of_nonneg_right (int_le_intAbs y.num) (Int.le_of_lt x.den_pos)
  have hA' : -(x.num * y.den) ≤ intAbs x.num * y.den := by
    rw [← Int.neg_mul]
    exact Int.mul_le_mul_of_nonneg_right (int_neg_le_intAbs x.num)
      (Int.le_of_lt y.den_pos)
  have hB' : -(y.num * x.den) ≤ intAbs y.num * x.den := by
    rw [← Int.neg_mul]
    exact Int.mul_le_mul_of_nonneg_right (int_neg_le_intAbs y.num)
      (Int.le_of_lt x.den_pos)
  have habs : intAbs (x.num * y.den + y.num * x.den)
      ≤ intAbs x.num * y.den + intAbs y.num * x.den := by
    cases Int.lt_or_le (x.num * y.den + y.num * x.den) 0 with
    | inl hs =>
      rw [intAbs_of_nonpos (Int.le_of_lt hs), Int.neg_add]
      exact Int.add_le_add hA' hB'
    | inr hs =>
      rw [intAbs_of_nonneg hs]
      exact Int.add_le_add hA hB
  show intAbs (x.num * y.den + y.num * x.den) * (x.den * y.den)
    ≤ (intAbs x.num * y.den + intAbs y.num * x.den) * (x.den * y.den)
  exact Int.mul_le_mul_of_nonneg_right habs
    (Int.le_of_lt (Int.mul_pos x.den_pos y.den_pos))

/-- **定理 (M115F-7e): 絶対値の乗法性** |xy| = |x||y|（分母共通なので
    PreRat の等式 + congrArg で閉じる）。 -/
theorem qAbs_mul (a b : QRat) : qAbs (qMul a b) = qMul (qAbs a) (qAbs b) := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  exact congrArg (Quot.mk ratRel)
    (preRat_ext (intAbs_mul x.num y.num) rfl)

/-! ## M115F-8: アルキメデス性 -/

/-- **定理 (M115F-8): アルキメデス性（代表ごとの witness 形）** —
    num/den ≤ |num|（den ≥ 1 から）。商から Nat を choice なしで
    取り出せないため代表 witness 形で述べる（正直申告）。 -/
theorem rat_archimedean (x : PreRat) :
    qLe (Quot.mk ratRel x) (ratOfInt.map ((x.num.natAbs : Nat) : Int)) := by
  have hd : 0 < x.den := x.den_pos
  show x.num * 1 ≤ ((x.num.natAbs : Nat) : Int) * x.den
  have h1 : x.num ≤ ((x.num.natAbs : Nat) : Int) := by omega
  have h2 : ((x.num.natAbs : Nat) : Int) * 1 ≤ ((x.num.natAbs : Nat) : Int) * x.den :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  rw [Int.mul_one] at h2
  rw [Int.mul_one]
  exact Int.le_trans h1 h2

/-! ## M115F-9: 総括レコード -/

/-- **M115F-9a: 総括** — ℚ = 可換環 + 全順序 + witness 付き逆元 +
    絶対値 + アルキメデス性 + ℤ の単射埋め込み。 -/
structure RatFieldData where
  /-- 環構造（ratRing）。 -/
  ring : CRing
  /-- 順序の反射律。 -/
  le_refl : ∀ a : QRat, qLe a a
  /-- 順序の推移律。 -/
  le_trans : ∀ a b c : QRat, qLe a b → qLe b c → qLe a c
  /-- 順序の反対称律。 -/
  le_antisym : ∀ a b : QRat, qLe a b → qLe b a → a = b
  /-- 全順序性。 -/
  le_total : ∀ a b : QRat, qLe a b ∨ qLe b a
  /-- 加法との両立。 -/
  le_add : ∀ a b c : QRat, qLe a b → qLe (qAdd a c) (qAdd b c)
  /-- 非負積の閉性。 -/
  mul_nonneg : ∀ a b : QRat,
    qLe ratRing.zero a → qLe ratRing.zero b → qLe ratRing.zero (qMul a b)
  /-- 体の公理（witness 形）。 -/
  inv_witness : ∀ x : PreRat, x.num ≠ 0 →
    qMul (Quot.mk ratRel x) (qInv (Quot.mk ratRel x)) = Quot.mk ratRel prOne
  /-- 三角不等式。 -/
  abs_add_le : ∀ a b : QRat, qLe (qAbs (qAdd a b)) (qAdd (qAbs a) (qAbs b))
  /-- 絶対値の乗法性。 -/
  abs_mul : ∀ a b : QRat, qAbs (qMul a b) = qMul (qAbs a) (qAbs b)
  /-- アルキメデス性（代表 witness 形）。 -/
  archimedean : ∀ x : PreRat,
    qLe (Quot.mk ratRel x) (ratOfInt.map ((x.num.natAbs : Nat) : Int))
  /-- ℤ の埋め込みの単射性。 -/
  int_inj : ∀ a b : Int, ratOfInt.map a = ratOfInt.map b → a = b

/-- **M115F-9b: witness**。 -/
def ratFieldData : RatFieldData where
  ring := ratRing
  le_refl := qLe_refl
  le_trans := qLe_trans
  le_antisym := qLe_antisym
  le_total := qLe_total
  le_add := qLe_add
  mul_nonneg := qLe_mul_nonneg
  inv_witness := qMul_inv
  abs_add_le := qAbs_add_le
  abs_mul := qAbs_mul
  archimedean := rat_archimedean
  int_inj := ratOfInt_inj

/-- **M115F-9c: 存在**。 -/
theorem ratField_exists : Nonempty RatFieldData := ⟨ratFieldData⟩

end IUT
