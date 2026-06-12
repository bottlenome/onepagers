/-
  IUT/Ring.lean — M38（可換環の基盤: ℤ・ℤ/n・ℤ_p は可換環）

  Lubin–Tate 形式群キャンペーンの第一層。LT 形式群法則 F(X,Y) の係数は
  ℤ_p に住むため、形式冪級数環 ℤ_p[[X]] を建てる前に**環構造そのもの**を
  自前で定義し、これまでに構成した加法群（M13/M27）と乗法構造
  （M29/M35）を**可換環として束ねる**。

  ロードマップ: M38 環構造 → M39 形式冪級数環 R[[X]] → M40 合成と
  Lubin–Tate 補題（係数帰納による一意存在）→ M41 形式群法則 F_f。

  * M38-1 `CRing` — 可換環の公理系（加法群 + 可換モノイド + 左分配。
    右分配・mul_zero 等は導出）と加法簿記（`add_left_cancel`）
  * M38-2 `CRing.toGrp` — 加法群への忘却（既存の Grp 理論との接続）
  * M38-3 `intRing` — ℤ は可換環（core の Int 法則で充足）
  * M38-4 `zmodRing` — **ℤ/n は可換環**（加法 = M13 の商群、乗法 =
    M29 の zmodMul、法則は代表の Int 法則に帰着）
  * M38-5 `zpRing` — **ℤ_p は可換環**（加法 = M27 の逆極限群、乗法 =
    M29 の zpMul。結合・単位・可換は M29/M35 の既証明、分配は成分計算）
  * M38-6 `RingHom` / `toZpRing` / `projRing` — 環準同型と
    **ℤ → ℤ_p**・**ℤ_p → ℤ/p^n** が環準同型であること

  全て選択公理不使用。
-/
import IUT.FullReciprocity

namespace IUT

/-! ## 可換環の公理系 -/

/-- **M38-1: 可換環**（加法群 + 乗法可換モノイド + 左分配）。 -/
structure CRing where
  carrier : Type
  add : carrier → carrier → carrier
  zero : carrier
  neg : carrier → carrier
  mul : carrier → carrier → carrier
  one : carrier
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  neg_add : ∀ a, add (neg a) a = zero
  add_comm : ∀ a b, add a b = add b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_comm : ∀ a b, mul a b = mul b a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

namespace CRing

/-- 右分配（可換性から導出）。 -/
theorem right_distrib (R : CRing) (a b c : R.carrier) :
    R.mul (R.add a b) c = R.add (R.mul a c) (R.mul b c) := by
  rw [R.mul_comm (R.add a b) c, R.left_distrib, R.mul_comm c a, R.mul_comm c b]

/-- 加法の左簡約。 -/
theorem add_left_cancel (R : CRing) {a b c : R.carrier}
    (h : R.add a b = R.add a c) : b = c := by
  have h1 : R.add (R.neg a) (R.add a b) = R.add (R.neg a) (R.add a c) := by
    rw [h]
  rw [← R.add_assoc, ← R.add_assoc, R.neg_add, R.zero_add, R.zero_add] at h1
  exact h1

/-- a·0 = 0（分配と簡約から導出）。 -/
theorem mul_zero (R : CRing) (a : R.carrier) : R.mul a R.zero = R.zero := by
  apply R.add_left_cancel (a := R.mul a R.zero)
  rw [← R.left_distrib]
  rw [show R.add R.zero R.zero = R.zero from R.zero_add R.zero,
    show R.add (R.mul a R.zero) R.zero
      = R.add R.zero (R.mul a R.zero) from R.add_comm _ _,
    R.zero_add]

/-- **M38-2: 加法群への忘却**（既存の Grp 理論との接続）。 -/
def toGrp (R : CRing) : Grp where
  carrier := R.carrier
  mul := R.add
  one := R.zero
  inv := R.neg
  mul_assoc := R.add_assoc
  one_mul := R.zero_add
  inv_mul := R.neg_add

end CRing

/-! ## ℤ は可換環 -/

/-- **M38-3: ℤ は可換環**。 -/
def intRing : CRing where
  carrier := Int
  add := fun a b => a + b
  zero := 0
  neg := fun a => -a
  mul := fun a b => a * b
  one := 1
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  neg_add := Int.add_left_neg
  add_comm := Int.add_comm
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_comm := Int.mul_comm
  left_distrib := Int.mul_add

/-! ## ℤ/n は可換環 -/

/-- **M38-4: ℤ/n は可換環** — 加法 = M13 の商群、乗法 = M29 の
    zmodMul、法則は代表の Int 法則に帰着。 -/
def zmodRing (n : Nat) : CRing where
  carrier := (zmod n).carrier
  add := (zmod n).mul
  zero := (zmod n).one
  neg := (zmod n).inv
  mul := zmodMul n
  one := Quot.mk (modCong n).rel 1
  add_assoc := (zmod n).mul_assoc
  zero_add := (zmod n).one_mul
  neg_add := (zmod n).inv_mul
  add_comm := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show Quot.mk (modCong n).rel (a + b) = Quot.mk (modCong n).rel (b + a)
    rw [Int.add_comm]
  mul_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    induction z using Quot.ind; rename_i c
    show Quot.mk (modCong n).rel (a * b * c)
      = Quot.mk (modCong n).rel (a * (b * c))
    rw [Int.mul_assoc]
  one_mul := by
    intro x
    induction x using Quot.ind; rename_i a
    show Quot.mk (modCong n).rel (1 * a) = Quot.mk (modCong n).rel a
    rw [Int.one_mul]
  mul_comm := zmodMul_comm n
  left_distrib := by
    intro x y z
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    induction z using Quot.ind; rename_i c
    show Quot.mk (modCong n).rel (a * (b + c))
      = Quot.mk (modCong n).rel (a * b + a * c)
    rw [Int.mul_add]

/-! ## ℤ_p は可換環 -/

/-- ℤ_p の加法は可換（成分ごと）。 -/
theorem zpAdd_comm (p : Nat) (x y : (Zp p).carrier) :
    (Zp p).mul x y = (Zp p).mul y x := by
  apply Subtype.ext
  funext n
  show (zmod (p ^ n)).mul (x.val n) (y.val n)
    = (zmod (p ^ n)).mul (y.val n) (x.val n)
  induction x.val n using Quot.ind; rename_i a
  induction y.val n using Quot.ind; rename_i b
  show Quot.mk (modCong (p ^ n)).rel (a + b)
    = Quot.mk (modCong (p ^ n)).rel (b + a)
  rw [Int.add_comm]

/-- ℤ_p の分配法則（成分ごと）。 -/
theorem zpMul_distrib (p : Nat) (x y z : (Zp p).carrier) :
    zpMul p x ((Zp p).mul y z) = (Zp p).mul (zpMul p x y) (zpMul p x z) := by
  apply Subtype.ext
  funext n
  show zmodMul (p ^ n) (x.val n) ((zmod (p ^ n)).mul (y.val n) (z.val n))
    = (zmod (p ^ n)).mul (zmodMul (p ^ n) (x.val n) (y.val n))
      (zmodMul (p ^ n) (x.val n) (z.val n))
  induction x.val n using Quot.ind; rename_i a
  induction y.val n using Quot.ind; rename_i b
  induction z.val n using Quot.ind; rename_i c
  show Quot.mk (modCong (p ^ n)).rel (a * (b + c))
    = Quot.mk (modCong (p ^ n)).rel (a * b + a * c)
  rw [Int.mul_add]

/-- **定理 (M38-5): ℤ_p は可換環** — 加法 = M27 の逆極限群、乗法 =
    M29 の zpMul。Lubin–Tate 級数の係数環。 -/
def zpRing (p : Nat) : CRing where
  carrier := (Zp p).carrier
  add := (Zp p).mul
  zero := (Zp p).one
  neg := (Zp p).inv
  mul := zpMul p
  one := zpOne p
  add_assoc := (Zp p).mul_assoc
  zero_add := (Zp p).one_mul
  neg_add := (Zp p).inv_mul
  add_comm := zpAdd_comm p
  mul_assoc := zpMul_assoc p
  one_mul := zpOne_mul p
  mul_comm := zpMul_comm p
  left_distrib := zpMul_distrib p

/-! ## 環準同型 -/

/-- **M38-6a: 環準同型**。 -/
structure RingHom (R S : CRing) where
  map : R.carrier → S.carrier
  map_add : ∀ a b, map (R.add a b) = S.add (map a) (map b)
  map_mul : ∀ a b, map (R.mul a b) = S.mul (map a) (map b)
  map_one : map R.one = S.one

/-- **M38-6b: ℤ → ℤ_p は環準同型**（M27 の toZp の環構造両立）。 -/
def toZpRing (p : Nat) : RingHom intRing (zpRing p) where
  map := (toZp p).map
  map_add := (toZp p).map_mul
  map_mul := fun a b => by
    apply Subtype.ext
    funext n
    rfl
  map_one := by
    apply Subtype.ext
    funext n
    rfl

/-- **M38-6c: ℤ_p → ℤ/p^n は環準同型**（レベル射影の環構造両立）。 -/
def projRing (p n : Nat) : RingHom (zpRing p) (zmodRing (p ^ n)) where
  map := fun x => x.val n
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_one := rfl

end IUT
