/-
# M164: λ-adic 膜 (λ^k) のイデアル構造と冪法則（柱B）

M151F（値の ∃-述語 `IsValAtLeast` と膜 (λ^k) の厳密降下）・M161（積の
値の下界 `isValAtLeast_mul`）の直上。膜 (λ^k) = 「値 ≥ k の元」が
**イデアルの公理をすべて満たす**ことと、元の冪に対する値の下界
（v(x^n) ≥ n·v(x)）を、M161 の下界則の系として choice なしで閉じる。

  * M164-1 `isValAtLeast_add` — 加法閉性: x,y ∈ (λ^k) ⟹ x+y ∈ (λ^k)
  * M164-2 `isValAtLeast_neg` — 反元閉性: x ∈ (λ^k) ⟹ −x ∈ (λ^k)
  * M164-3 `isValAtLeast_smul` — 環倍閉性: x ∈ (λ^k) ⟹ r·x ∈ (λ^k)
    （任意の環元 r で）——これで (λ^k) は**イデアル**
  * M164-4 **`isValAtLeast_pow`** — 冪法則: x ∈ (λ^j) ⟹ x^n ∈ (λ^{n·j})
    （M161 `isValAtLeast_mul` の n 回反復、v(x^n) ≥ n·v(x)）
  * M164-5 `LambdaIdealData` — 総括

意義: M151F は「値 ≥ k」を ∃-述語として定式化しただけで、その集合が
イデアルであること（加法群 + 環倍で閉じる）は未証明だった。本層で
(λ^k) が正真正銘のイデアルであることが閉じ、**λ-adic フィルトレーション
R = (λ^0) ⊇ (λ^1) ⊇ … が「イデアルの降下鎖」である**ことが確立する。
冪法則 v(x^n) ≥ n·v(x) は M161 の積の下界の直接の系。

正直な限定: これらは値の**下界**（イデアル所属）の閉性のみ。等号
（v(x+y) = min など非アルキメデス付値の等式・v(x^n) = n·v(x) の上界）は
一般元の付値関数の全域構成（M147F 座標理論の次層）を要し対象外。
イデアルの生成元・商環 R/(λ^k) の構造も次層。

全て選択公理不使用。
-/
import IUT.LambdaValuationMul

namespace IUT

/-! ## M164-1: 加法閉性 -/

/-- **定理 (M164-1): 膜の加法閉性** — x,y ∈ (λ^k) ⟹ x+y ∈ (λ^k)。
    x = a·λ^k, y = b·λ^k から x+y = (a+b)·λ^k（right_distrib）。 -/
theorem isValAtLeast_add {R : CRing} {lam x y : R.carrier} {k : Nat}
    (hx : IsValAtLeast R lam x k) (hy : IsValAtLeast R lam y k) :
    IsValAtLeast R lam (R.add x y) k := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨R.add a b, ?_⟩
  rw [ha, hb, CRing.right_distrib]

/-! ## M164-2: 反元閉性 -/

/-- **定理 (M164-2): 膜の反元閉性** — x ∈ (λ^k) ⟹ −x ∈ (λ^k)。
    x = a·λ^k から −x = (−a)·λ^k（neg_mul）。 -/
theorem isValAtLeast_neg {R : CRing} {lam x : R.carrier} {k : Nat}
    (hx : IsValAtLeast R lam x k) :
    IsValAtLeast R lam (R.neg x) k := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨R.neg a, ?_⟩
  rw [ha, CRing.neg_mul]

/-! ## M164-3: 環倍閉性（イデアル性） -/

/-- **定理 (M164-3): 膜の環倍閉性** — x ∈ (λ^k) ⟹ r·x ∈ (λ^k)（任意の
    環元 r で）。x = a·λ^k から r·x = (r·a)·λ^k（mul_assoc）。加法群
    閉性（M164-1/2）と併せて (λ^k) は**イデアル**。 -/
theorem isValAtLeast_smul {R : CRing} {lam x : R.carrier} {k : Nat}
    (r : R.carrier) (hx : IsValAtLeast R lam x k) :
    IsValAtLeast R lam (R.mul r x) k := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨R.mul r a, ?_⟩
  rw [ha, R.mul_assoc]

/-! ## M164-4: 冪法則 -/

/-- **定理 (M164-4): 冪の値の下界** — x ∈ (λ^j) ⟹ x^n ∈ (λ^{n·j})。
    v(x^n) ≥ n·v(x) の下界形。n の帰納: 0 は λ^0 = 1 ∈ (λ^0)、
    n+1 は x^{n+1} = x^n·x に M161 `isValAtLeast_mul` を適用し
    (n·j) + j = (n+1)·j（Nat.succ_mul）。 -/
theorem isValAtLeast_pow {R : CRing} {lam x : R.carrier} {j : Nat}
    (hx : IsValAtLeast R lam x j) :
    ∀ n, IsValAtLeast R lam (rpow R x n) (n * j) := by
  intro n
  induction n with
  | zero =>
    show IsValAtLeast R lam (rpow R x 0) (0 * j)
    rw [Nat.zero_mul]
    exact isValAtLeast_zero R lam (rpow R x 0)
  | succ n ih =>
    show IsValAtLeast R lam (R.mul (rpow R x n) x) ((n + 1) * j)
    rw [Nat.succ_mul]
    exact isValAtLeast_mul ih hx

/-! ## M164-5: 総括 -/

/-- **M164-5a: 総括** — (λ^k) のイデアル構造データ（加法群閉性・環倍
    閉性・冪法則）。 -/
structure LambdaIdealData where
  /-- 加法閉性。 -/
  add_closed : ∀ (R : CRing) (lam x y : R.carrier) (k : Nat),
    IsValAtLeast R lam x k → IsValAtLeast R lam y k →
    IsValAtLeast R lam (R.add x y) k
  /-- 反元閉性。 -/
  neg_closed : ∀ (R : CRing) (lam x : R.carrier) (k : Nat),
    IsValAtLeast R lam x k → IsValAtLeast R lam (R.neg x) k
  /-- 環倍閉性（イデアル性）。 -/
  smul_closed : ∀ (R : CRing) (lam x : R.carrier) (k : Nat) (r : R.carrier),
    IsValAtLeast R lam x k → IsValAtLeast R lam (R.mul r x) k
  /-- 冪法則 v(x^n) ≥ n·v(x)。 -/
  pow_law : ∀ (R : CRing) (lam x : R.carrier) (j : Nat),
    IsValAtLeast R lam x j →
    ∀ n, IsValAtLeast R lam (rpow R x n) (n * j)

/-- **M164-5b: witness**。 -/
def lambdaIdealData : LambdaIdealData where
  add_closed := fun _ _ _ _ _ hx hy => isValAtLeast_add hx hy
  neg_closed := fun _ _ _ _ hx => isValAtLeast_neg hx
  smul_closed := fun _ _ _ _ r hx => isValAtLeast_smul r hx
  pow_law := fun _ _ _ _ hx => isValAtLeast_pow hx

/-- **M164-5c: 存在**。 -/
theorem lambdaIdeal_exists : Nonempty LambdaIdealData := ⟨lambdaIdealData⟩

end IUT
