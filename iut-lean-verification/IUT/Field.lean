/-
  IUT/Field.lean — M264F: 体（Field）— 実 π₁^ét／遠アーベル復元の最下層

  ── 主要成果の分類: **[実]**（本物の体の公理系と本物の体の実例）。

  complete_pct 影響: **柱A の実 π₁^ét／遠アーベルの本物の先行建設**。遠アーベル
  幾何・π₁^ét 復元は「基礎体 K の体構造」を最下層に要求するが、現状コードベースの
  gap 分析では `Field` 構造は 0 ファイルであった。本ファイルはその最下層を
  **本物の体（可換環 + 逆元 + 体公理）として実構成**する。既存 `CRing`（M38）を
  extend し、逆元 `inv`・非自明性 `zero_ne_one`・逆元公理 `mul_inv_cancel` を加え、
  逆元の一意性・対合性（inv∘inv=id）・乗法性・**整域性（零因子なし）**・`inv 1 = 1`
  を本物に証明する。さらに既存の有理数体 ℚ（M115F の QRat = Quot ratRel）が
  この `IUTField` 構造をなすことを実例として確定する（体は空でない）。

  * M264F-1 `IUTField`      — 体の公理系（CRing を extend + inv + zero_ne_one）
  * M264F-2 一意性・対合性  — inv_unique / inv_inv / inv_ne_zero
  * M264F-3 整域性          — eq_zero_of_mul_eq_zero_{left,right} / mul_ne_zero
  * M264F-4 乗法性・単位    — inv_mul（逆元の乗法性）/ inv_one
  * M264F-5 実例 ℚ          — ratIUTField（QRat は本物の IUTField）
  * M264F-6 capstone        — IUTFieldData / iutField_exists / iutFieldData_exists

  正直な限定（何が本物で何が未達か）:
  - **本物**: 体の公理系そのもの、上記の全定理（一意性・対合・乗法性・整域性・
    inv 1 = 1）、そして「ℚ が本物の体をなす」という実例は完全証明（sorry 皆無・
    新規 choice 皆無）。
  - **未達（正直申告）**: 整域性は `x ≠ 0 → (xy = 0 → y = 0)` の**仮説形**で述べる。
    選言形 `xy = 0 → x = 0 ∨ y = 0` は抽象体上で x = 0 の判定に排中律を要し、
    本規約が証明本体での Classical.choice 導入を禁ずるため対象外とした
    （選言そのものは古典論理でのみ成立し、構成的な仮説形が本物の整域内容）。
  - 本ファイルは体の**代数構造**のみ。位相・付値・ガロア群・π₁^ét 本体は未構成で、
    これらは上位層（既存の AbstractGalois 等）と後続で接続する。

  全て選択公理不使用（新規 choice を証明本体に導入しない）。
-/
import IUT.Rationals

namespace IUT

/-! ## M264F-1: 体の公理系 -/

/-- **M264F-1: 体**（可換環 `CRing` を extend し、逆元 `inv` と体公理を加える）。
    `mul_inv_cancel`: 非零元 x は乗法逆元を持つ。`inv_zero`: 0 の逆元は 0（規約）。
    `zero_ne_one`: 非自明性（0 ≠ 1）。 -/
structure IUTField extends CRing where
  /-- 乗法逆元。 -/
  inv : carrier → carrier
  /-- 逆元公理: 非零元は逆元を持つ。 -/
  mul_inv_cancel : ∀ x, x ≠ zero → mul x (inv x) = one
  /-- 規約: 0 の逆元は 0。 -/
  inv_zero : inv zero = zero
  /-- 非自明性: 0 ≠ 1。 -/
  zero_ne_one : zero ≠ one

namespace IUTField

/-! ## M264F-2: 逆元の一意性・対合性 -/

/-- **逆元の一意性** — 可換モノイドで x·y = 1 かつ x·z = 1 なら y = z。 -/
theorem inv_unique (F : IUTField) {x y z : F.carrier}
    (h1 : F.mul x y = F.one) (h2 : F.mul x z = F.one) : y = z := by
  have e : z = y := by
    rw [← F.one_mul z, ← h1, F.mul_assoc, F.mul_comm y z, ← F.mul_assoc, h2, F.one_mul]
  exact e.symm

/-- 1 ≠ 0（非自明性の対称形）。 -/
theorem one_ne_zero (F : IUTField) : F.one ≠ F.zero :=
  fun h => F.zero_ne_one h.symm

/-- 逆元は左からも消去する: (inv x)·x = 1（可換性）。 -/
theorem inv_mul_cancel (F : IUTField) {x : F.carrier} (hx : x ≠ F.zero) :
    F.mul (F.inv x) x = F.one := by
  rw [F.mul_comm]
  exact F.mul_inv_cancel x hx

/-- **非零元の逆元は非零**（inv x = 0 なら 1 = x·0 = 0 で矛盾）。 -/
theorem inv_ne_zero (F : IUTField) {x : F.carrier} (hx : x ≠ F.zero) :
    F.inv x ≠ F.zero := by
  intro hc
  apply F.one_ne_zero
  have h1 : F.mul x (F.inv x) = F.one := F.mul_inv_cancel x hx
  rw [hc, F.toCRing.mul_zero x] at h1
  exact h1.symm

/-- **逆元の対合性** — x ≠ 0 なら inv (inv x) = x（inv x の逆元が x と inv (inv x)
    の二通りあり一意性で一致）。 -/
theorem inv_inv (F : IUTField) {x : F.carrier} (hx : x ≠ F.zero) :
    F.inv (F.inv x) = x := by
  have hinv : F.inv x ≠ F.zero := F.inv_ne_zero hx
  have h1 : F.mul (F.inv x) (F.inv (F.inv x)) = F.one :=
    F.mul_inv_cancel (F.inv x) hinv
  have h2 : F.mul (F.inv x) x = F.one := F.inv_mul_cancel hx
  exact F.inv_unique h1 h2

/-! ## M264F-3: 整域性（零因子なし） -/

/-- **整域性（左）** — x·y = 0 かつ x ≠ 0 なら y = 0（inv x を左から掛ける）。 -/
theorem eq_zero_of_mul_eq_zero_left (F : IUTField) {x y : F.carrier}
    (h : F.mul x y = F.zero) (hx : x ≠ F.zero) : y = F.zero := by
  have h2 : F.mul (F.inv x) (F.mul x y) = F.zero := by
    rw [h, F.toCRing.mul_zero (F.inv x)]
  rw [← F.mul_assoc, F.inv_mul_cancel hx, F.one_mul] at h2
  exact h2

/-- **整域性（右）** — x·y = 0 かつ y ≠ 0 なら x = 0。 -/
theorem eq_zero_of_mul_eq_zero_right (F : IUTField) {x y : F.carrier}
    (h : F.mul x y = F.zero) (hy : y ≠ F.zero) : x = F.zero := by
  have h' : F.mul y x = F.zero := by
    rw [F.mul_comm]
    exact h
  exact F.eq_zero_of_mul_eq_zero_left h' hy

/-- **非零の積は非零**（整域性の対偶）。 -/
theorem mul_ne_zero (F : IUTField) {x y : F.carrier}
    (hx : x ≠ F.zero) (hy : y ≠ F.zero) : F.mul x y ≠ F.zero := by
  intro hc
  exact hy (F.eq_zero_of_mul_eq_zero_left hc hx)

/-! ## M264F-4: 逆元の乗法性・単位 -/

/-- 4 因子の入れ替え (a·b)·(c·d) = (a·c)·(b·d)（結合・可換から）。 -/
theorem mul_mul_mul_comm (F : IUTField) (a b c d : F.carrier) :
    F.mul (F.mul a b) (F.mul c d) = F.mul (F.mul a c) (F.mul b d) := by
  rw [F.mul_assoc a b (F.mul c d), ← F.mul_assoc b c d, F.mul_comm b c,
    F.mul_assoc c b d, ← F.mul_assoc a c (F.mul b d)]

/-- **逆元の乗法性** — x,y ≠ 0 なら inv (x·y) = (inv x)·(inv y)。 -/
theorem inv_mul (F : IUTField) {x y : F.carrier}
    (hx : x ≠ F.zero) (hy : y ≠ F.zero) :
    F.inv (F.mul x y) = F.mul (F.inv x) (F.inv y) := by
  have hxy : F.mul x y ≠ F.zero := F.mul_ne_zero hx hy
  have h1 : F.mul (F.mul x y) (F.inv (F.mul x y)) = F.one :=
    F.mul_inv_cancel (F.mul x y) hxy
  have h2 : F.mul (F.mul x y) (F.mul (F.inv x) (F.inv y)) = F.one := by
    rw [F.mul_mul_mul_comm x y (F.inv x) (F.inv y),
      F.mul_inv_cancel x hx, F.mul_inv_cancel y hy, F.one_mul]
  exact F.inv_unique h1 h2

/-- **inv 1 = 1**（1·(inv 1) = 1 かつ 1·(inv 1) = inv 1）。 -/
theorem inv_one (F : IUTField) : F.inv F.one = F.one := by
  have h := F.mul_inv_cancel F.one F.one_ne_zero
  rw [F.one_mul] at h
  exact h

end IUTField

/-! ## M264F-5: 実例 — 有理数体 ℚ は本物の IUTField -/

/-- **M264F-5: ℚ は本物の体** — 既存 M115F の `ratRing`（可換環）を土台に、
    witness 形の逆元 `qInv` を体の逆元へと総合する。非零性は代表の分子が
    非零であることに帰着（`Quot.sound` で 0 の代表と分離）。 -/
def ratIUTField : IUTField where
  toCRing := ratRing
  inv := qInv
  mul_inv_cancel := by
    intro x
    induction x using Quot.ind
    rename_i r
    intro hx
    apply qMul_inv r
    intro hr0
    apply hx
    show Quot.mk ratRel r = Quot.mk ratRel prZero
    apply Quot.sound
    show r.num * (1 : Int) = (0 : Int) * r.den
    rw [hr0, Int.zero_mul, Int.zero_mul]
  inv_zero := by
    show Quot.mk ratRel (prInv prZero) = Quot.mk ratRel prZero
    exact congrArg (Quot.mk ratRel) (prInv_of_eq rfl)
  zero_ne_one := by
    intro h
    have h2 : (0 : Int) * 1 = 1 * 1 := quot_exact_rat h
    omega

/-! ## M264F-6: capstone -/

/-- **M264F-6a: 体の総括レコード** — 逆元一意性・整域性・逆元の対合性/乗法性・
    inv 1 = 1 を束ねる。 -/
structure IUTFieldData where
  /-- 台となる体。 -/
  toField : IUTField
  /-- 整域性（仮説形）。 -/
  is_domain : ∀ {x y : toField.carrier},
    toField.mul x y = toField.zero → x ≠ toField.zero → y = toField.zero
  /-- 逆元の対合性。 -/
  inv_involutive : ∀ {x : toField.carrier},
    x ≠ toField.zero → toField.inv (toField.inv x) = x
  /-- 逆元の乗法性。 -/
  inv_multiplicative : ∀ {x y : toField.carrier},
    x ≠ toField.zero → y ≠ toField.zero →
      toField.inv (toField.mul x y) = toField.mul (toField.inv x) (toField.inv y)
  /-- 単位の逆元。 -/
  one_inv : toField.inv toField.one = toField.one

/-- **M264F-6b: ℚ の総括 witness**。 -/
def ratIUTFieldData : IUTFieldData where
  toField := ratIUTField
  is_domain := by
    intro x y h hx
    exact ratIUTField.eq_zero_of_mul_eq_zero_left h hx
  inv_involutive := by
    intro x hx
    exact ratIUTField.inv_inv hx
  inv_multiplicative := by
    intro x y hx hy
    exact ratIUTField.inv_mul hx hy
  one_inv := ratIUTField.inv_one

/-- **M264F-6c: 体は空でない**（本物の体の実例 ℚ が存在）。 -/
theorem iutField_exists : Nonempty IUTField := ⟨ratIUTField⟩

/-- **M264F-6d: 総括の存在**。 -/
theorem iutFieldData_exists : Nonempty IUTFieldData := ⟨ratIUTFieldData⟩

end IUT
