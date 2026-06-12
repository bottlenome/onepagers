/-
  IUT/FormalGroupComm.lean — M62（LT 形式群法則の可換性）

  **可換性定理**: LT 形式群法則 F は F(X, Y) = F(Y, X)、すなわち
  全係数で F_{i,j} = F_{j,i} を満たす。

  証明はエレガントな一意性の応用: 変数交換作用素 swap（swapPS2 F = F i j
  を (j, i) に置く）が **環自己同型**であり、**LT 形式群法則を
  LT 形式群法則に移す**（f が X, Y に対称に作用するため）ことを示し、
  M61 の一意性から swap F = F を得る。

  鍵となる新道具は**二重有限和の交換（矩形 Fubini）** rsum_exchange:
  Σ_{k<A} Σ_{l<B} g(k,l) = Σ_{l<B} Σ_{k<A} g(k,l)。これで swap が
  Cauchy 積を保つこと（swap_mul）が二重和の添字交換に帰着する。

  * M62-1 `rsum_exchange` — **矩形 Fubini**（二重帰納）
  * M62-2 `swapPS2` / `swap_add` / `swap_one` / `swap_mul` /
    `swap_pow` — swap は環自己同型（係数 (j,i) ↦ (i,j)）
  * M62-3 `swap_comp1` — swap は 1→2 変数代入と交換
    （swap(f∘F) = f∘(swap F)、swap_pow 経由）
  * M62-4 `swap_rhs` — swap は方程式右辺と交換
    （swap(F(fX, fY)) = (swap F)(fX, fY)、lt2_rhs_coeff + rsum_exchange
    + mul_comm。f が両変数に対称なのが効く）
  * M62-5 `swap_is_formal_group` — swap F も LT 形式群法則
  * M62-6 `lt_formal_group_comm` / `lt_formal_group_law_comm` —
    **可換性**: F_{i,j} = F_{j,i}（M61 の一意性で swap F = F）と
    lt2Sol への適用

  全て選択公理不使用。
-/
import IUT.FormalGroupUnique

namespace IUT

/-! ## 矩形 Fubini -/

/-- **定理 (M62-1): 二重有限和の交換（矩形 Fubini）** —
    Σ_{k<A} Σ_{l<B} g(k,l) = Σ_{l<B} Σ_{k<A} g(k,l)。A についての帰納。 -/
theorem rsum_exchange (R : CRing) (g : Nat → Nat → R.carrier) :
    ∀ A B, rsum R (fun k => rsum R (fun l => g k l) B) A
      = rsum R (fun l => rsum R (fun k => g k l) A) B := by
  intro A
  induction A with
  | zero =>
    intro B
    show R.zero = rsum R (fun l => rsum R (fun k => g k l) 0) B
    rw [show (fun l => rsum R (fun k => g k l) 0) = (fun _ : Nat => R.zero)
        from rfl, rsum_const_zero R B]
  | succ A' ih =>
    intro B
    show R.add (rsum R (fun k => rsum R (fun l => g k l) B) A')
        (rsum R (fun l => g A' l) B)
      = rsum R (fun l => rsum R (fun k => g k l) (A' + 1)) B
    rw [ih B,
      show (fun l => rsum R (fun k => g k l) (A' + 1))
        = (fun l => R.add (rsum R (fun k => g k l) A') (g A' l)) from rfl,
      rsum_add R (fun l => rsum R (fun k => g k l) A')
        (fun l => g A' l) B]

/-! ## swap は環自己同型 -/

/-- 変数交換: (swap F)_{j,i} = F_{i,j}。 -/
def swapPS2 (R : CRing) (F : PS2 R) : PS2 R := fun j i => F i j

/-- swap は対合（往復で恒等）。 -/
theorem swap_swap (R : CRing) (F : PS2 R) : swapPS2 R (swapPS2 R F) = F := rfl

/-- swap は加法を保つ。 -/
theorem swap_add (R : CRing) (A B : PS2 R) :
    swapPS2 R (psAdd (psRing R) A B)
      = psAdd (psRing R) (swapPS2 R A) (swapPS2 R B) := rfl

/-- swap は 1 を保つ（対称な単項式 δ_{(0,0)}）。 -/
theorem swap_one (R : CRing) :
    swapPS2 R (psRing (psRing R)).one = (psRing (psRing R)).one := by
  funext j i
  show ((psOne (psRing R)) i) j = ((psOne (psRing R)) j) i
  cases Nat.decEq i 0 with
  | isTrue hi =>
    cases Nat.decEq j 0 with
    | isTrue hj => rw [hi, hj]
    | isFalse hj =>
      rw [show ((psOne (psRing R)) i) j = R.zero from by
            rw [hi]
            show (psOne R) j = R.zero
            exact if_neg hj,
        show ((psOne (psRing R)) j) i = R.zero from by
            show (if j = 0 then (psRing R).one else (psRing R).zero) i = R.zero
            rw [if_neg hj]
            rfl]
  | isFalse hi =>
    rw [show ((psOne (psRing R)) i) j = R.zero from by
          show (if i = 0 then (psRing R).one else (psRing R).zero) j = R.zero
          rw [if_neg hi]
          rfl,
      show ((psOne (psRing R)) j) i = R.zero from by
          cases Nat.decEq j 0 with
          | isTrue hj =>
            rw [hj]
            show (psOne R) i = R.zero
            exact if_neg hi
          | isFalse hj =>
            show (if j = 0 then (psRing R).one else (psRing R).zero) i = R.zero
            rw [if_neg hj]
            rfl]

/-- **定理 (M62-2): swap は Cauchy 積を保つ** — swap(A·B) =
    swap(A)·swap(B)。二重 Cauchy 係数公式（M57）+ 矩形 Fubini。 -/
theorem swap_mul (R : CRing) (A B : PS2 R) :
    swapPS2 R (psMul (psRing R) A B)
      = psMul (psRing R) (swapPS2 R A) (swapPS2 R B) := by
  funext j i
  show psMul (psRing R) A B i j
      = psMul (psRing R) (swapPS2 R A) (swapPS2 R B) j i
  rw [ps2Mul_coeff R A B i j,
    ps2Mul_coeff R (swapPS2 R A) (swapPS2 R B) j i,
    rsum_exchange R (fun k l => R.mul (swapPS2 R A k l)
      (swapPS2 R B (j - k) (i - l))) (j + 1) (i + 1)]
  exact rsum_congr R (i + 1) (fun k _ =>
    rsum_congr R (j + 1) (fun l _ => rfl))

/-- **定理 (M62-2'): swap は冪を保つ** — swap(F^k) = (swap F)^k。 -/
theorem swap_pow (R : CRing) (F : PS2 R) : ∀ k,
    swapPS2 R (psPow (psRing R) F k) = psPow (psRing R) (swapPS2 R F) k := by
  intro k
  induction k with
  | zero => exact swap_one R
  | succ k ih =>
    show swapPS2 R (psMul (psRing R) (psPow (psRing R) F k) F)
      = psMul (psRing R) (psPow (psRing R) (swapPS2 R F) k) (swapPS2 R F)
    rw [swap_mul R (psPow (psRing R) F k) F, ih]

/-! ## swap は代入と交換 -/

/-- **定理 (M62-3): swap は 1→2 変数代入と交換** —
    swap(f∘F) = f∘(swap F)（swap_pow 経由）。 -/
theorem swap_comp1 (R : CRing) (f : PS R) (F : PS2 R) :
    swapPS2 R (ps2Comp1 R f F) = ps2Comp1 R f (swapPS2 R F) := by
  funext j i
  show rsum R (fun k => R.mul (f k) (psPow (psRing R) F k i j)) (j + i + 1)
      = rsum R (fun k => R.mul (f k)
          (psPow (psRing R) (swapPS2 R F) k j i)) (i + j + 1)
  rw [show j + i + 1 = i + j + 1 from by omega]
  refine rsum_congr R (i + j + 1) (fun k _ => ?_)
  rw [show psPow (psRing R) (swapPS2 R F) k
      = swapPS2 R (psPow (psRing R) F k) from (swap_pow R F k).symm]
  rfl

/-- **定理 (M62-4): swap は方程式右辺と交換** —
    swap(F(f(X), f(Y))) = (swap F)(f(X), f(Y))。lt2_rhs_coeff（一変数化）
    + 矩形 Fubini + mul_comm。f が両変数に対称なのが効く。 -/
theorem swap_rhs (R : CRing) (f : PS R) (F : PS2 R) :
    swapPS2 R (ps2Comp2 R F (psC (psRing R) f) (psMap (psConstHom R) f))
      = ps2Comp2 R (swapPS2 R F) (psC (psRing R) f)
          (psMap (psConstHom R) f) := by
  funext j i
  show ps2Comp2 R F (psC (psRing R) f) (psMap (psConstHom R) f) i j
      = ps2Comp2 R (swapPS2 R F) (psC (psRing R) f)
          (psMap (psConstHom R) f) j i
  rw [lt2_rhs_coeff R f F i j,
    lt2_rhs_coeff R f (swapPS2 R F) j i,
    rsum_exchange R (fun b a => R.mul (F b a)
      (R.mul (psPow R f a j) (psPow R f b i))) (j + i + 1) (j + i + 1),
    show j + i + 1 = i + j + 1 from by omega]
  exact rsum_congr R (i + j + 1) (fun b _ =>
    rsum_congr R (i + j + 1) (fun a _ =>
      congrArg (R.mul (F a b))
        (R.mul_comm (psPow R f b j) (psPow R f a i))))

/-! ## swap F も LT 形式群法則 / 可換性 -/

/-- **定理 (M62-5): swap F も LT 形式群法則** — swap が方程式と一次条件を
    保つ（一次条件は対称、方程式は M62-3/4 の合流）。 -/
theorem swap_is_formal_group (p : Nat) (F : PS2 (zpRing p))
    (hF : IsLTFormalGroup p F) : IsLTFormalGroup p (swapPS2 (zpRing p) F) := by
  refine ⟨hF.1, hF.2.2.1, hF.2.1, ?_⟩
  calc ps2Comp1 (zpRing p) (ltPoly p) (swapPS2 (zpRing p) F)
      = swapPS2 (zpRing p) (ps2Comp1 (zpRing p) (ltPoly p) F) :=
        (swap_comp1 (zpRing p) (ltPoly p) F).symm
    _ = swapPS2 (zpRing p) (ps2Comp2 (zpRing p) F
          (psC (psRing (zpRing p)) (ltPoly p))
          (psMap (psConstHom (zpRing p)) (ltPoly p))) :=
        congrArg (swapPS2 (zpRing p)) hF.2.2.2
    _ = ps2Comp2 (zpRing p) (swapPS2 (zpRing p) F)
          (psC (psRing (zpRing p)) (ltPoly p))
          (psMap (psConstHom (zpRing p)) (ltPoly p)) :=
        swap_rhs (zpRing p) (ltPoly p) F

/-- **定理 (M62-6): LT 形式群法則の可換性** — F_{i,j} = F_{j,i}
    （M61 の一意性: swap F も LT 形式群法則ゆえ swap F = F）。 -/
theorem lt_formal_group_comm (p : Nat) (hp : IsPrime p) (F : PS2 (zpRing p))
    (hF : IsLTFormalGroup p F) : ∀ i j, F i j = F j i := by
  have hsf := lt_formal_group_unique p hp (swapPS2 (zpRing p) F) F
    (swap_is_formal_group p F hF) hF
  intro i j
  exact congrFun (congrFun hsf j) i

/-- **系 (M62-6'): 構成した解 lt2Sol は可換**
    — F(X, Y) = F(Y, X) の係数形。 -/
theorem lt2Sol_comm (p : Nat) (hp : IsPrime p) :
    ∀ i j, lt2Sol p hp i j = lt2Sol p hp j i :=
  lt_formal_group_comm p hp (lt2Sol p hp) (lt2Sol_is_formal_group p hp)

end IUT
