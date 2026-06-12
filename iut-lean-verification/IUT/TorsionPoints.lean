/-
  IUT/TorsionPoints.lean — M79F（点レベルの [π]-作用と πⁿ-捻れ点:
  分岐 LCFT への入口）

  M77/M78F/M79 の評価パッケージと M72F の反復 f^{∘n} を合流させ、
  **点レベルの [πⁿ]-作用**と **πⁿ-捻れ点の述語**を構成する。
  f^{∘(n+1)}(x) = f^{∘n}(f(x))（f(x) = πx + x^p は zpEval_ltPoly）が
  点の漸化式として成立し、捻れ点 Λ_n = ker [πⁿ] が定義できる。

  * M79F-1 `rpow_zero_pos` — k ≥ 1 で 0^k = 0（環冪の補題）
  * M79F-2 `zpEval_at_zero` — **零点での評価** F(0) = 0
    （定数項 0 のとき。部分和の k = 0 項は hF で、k ≥ 1 項は
    0^k = 0 で消滅）
  * M79F-3 `zero_point_witness` — 零点の標準 witness 0 = p·0
  * M79F-4 `zpEval_eq_at_zero` — y = 0 なら F(y) = 0（witness つき
    評価の零点への輸送: subst + witness 非依存性）
  * M79F-5 `zpEval_ltIter_succ` — **点レベルの [πⁿ]-作用の漸化式**
    [πⁿ⁺¹](x) = [πⁿ](f(x))（合成両立 M79-4 の特殊化）
  * M79F-6 `IsTorsionPoint` — **πⁿ-捻れ点の述語** [πⁿ](x) = 0
  * M79F-7 `zero_is_torsion` / `torsion_zero_iff` / `torsion_mono` —
    0 は捻れ点・π⁰-捻れ ⟺ x = 0・n-捻れ ⟹ (n+1)-捻れ
  * M79F-8 `torsion_le` — 捻れの単調性 n ≤ m ⟹ (n-捻れ ⟹ m-捻れ)

  捻れ点の非自明性（ℤ_p 内では Λ_n = 0）・分岐拡大の構成・
  点の群の群法則は未形式化/並行開発。
  全て選択公理不使用。サブエージェント並行部品・分岐 LCFT への入口。
-/
import IUT.FormalGroupPointsComp
import IUT.LTIterate

namespace IUT

/-! ## 零点での評価 -/

/-- **M79F-1: 正冪での 0 の冪** — 1 ≤ k なら 0^k = 0。 -/
theorem rpow_zero_pos (R : CRing) : ∀ k, 1 ≤ k →
    rpow R R.zero k = R.zero := by
  intro k hk
  cases k with
  | zero => exact absurd hk (by omega)
  | succ k' =>
    show R.mul (rpow R R.zero k') R.zero = R.zero
    exact R.mul_zero _

/-- **M79F-2: 零点での評価** — F(0) = 0（定数項 0 のとき）。
    部分和の k = 0 項は F_0·1 = 0（hF）、k ≥ 1 項は 0^k = 0 で消滅。 -/
theorem zpEval_at_zero (p : Nat) (F : PS (zpRing p))
    (hF : F 0 = (zpRing p).zero) (e₀ : (Zp p).carrier)
    (h0 : (zpRing p).zero
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e₀) :
    zpEval p F ((zpRing p).zero) e₀ h0 = (zpRing p).zero := by
  apply Subtype.ext
  funext n
  show (zpEvalSeg p F ((zpRing p).zero) n).val n = ((zpRing p).zero).val n
  have hseg : zpEvalSeg p F ((zpRing p).zero) n = (zpRing p).zero := by
    show rsum (zpRing p) (fun k =>
        (zpRing p).mul (F k) (rpow (zpRing p) ((zpRing p).zero) k)) n
      = (zpRing p).zero
    have hc : rsum (zpRing p) (fun k =>
          (zpRing p).mul (F k) (rpow (zpRing p) ((zpRing p).zero) k)) n
        = rsum (zpRing p) (fun _ => (zpRing p).zero) n :=
      rsum_congr (zpRing p) n (fun k _ => by
        show (zpRing p).mul (F k) (rpow (zpRing p) ((zpRing p).zero) k)
          = (zpRing p).zero
        cases k with
        | zero =>
          rw [hF]
          exact (zpRing p).zero_mul _
        | succ k' =>
          rw [rpow_zero_pos (zpRing p) (k' + 1) (by omega)]
          exact (zpRing p).mul_zero _)
    rw [hc]
    exact rsum_const_zero (zpRing p) n
  rw [hseg]

/-- **M79F-3: 零点の標準 witness** — 0 = p·0。 -/
theorem zero_point_witness (p : Nat) :
    (zpRing p).zero
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ((zpRing p).zero) :=
  ((zpRing p).mul_zero _).symm

/-- **M79F-4: 零点への輸送** — y = 0 なら F(y) = 0（定数項 0 のとき。
    subst で y を 0 に置換し M79F-2 に帰着）。 -/
theorem zpEval_eq_at_zero (p : Nat) (F : PS (zpRing p))
    (hF : F 0 = (zpRing p).zero) (y e' : (Zp p).carrier)
    (hy' : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e')
    (hy0 : y = (zpRing p).zero) :
    zpEval p F y e' hy' = (zpRing p).zero := by
  subst hy0
  exact zpEval_at_zero p F hF e' hy'

/-! ## 点レベルの [πⁿ]-作用 -/

/-- **定理 (M79F-5): [πⁿ]-作用の漸化式** —
    [πⁿ⁺¹](x) = [πⁿ](f(x))（f(x) = πx + x^p は zpEval_ltPoly）。
    f^{∘(n+1)} = f^{∘n}∘f なので合成両立の完結形 M79-4 の特殊化。 -/
theorem zpEval_ltIter_succ (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltIter p (n + 1)) x e hx
      = zpEval p (ltIter p n) (zpEval p (ltPoly p) x e hx)
          ((zpRing p).mul e
            (zpEval p (psShift (zpRing p) (ltPoly p)) x e hx))
          (zpEval_closed p hp (ltPoly p) (ltPoly_coeff_zero p hp) x e hx) := by
  show zpEval p (psComp (zpRing p) (ltIter p n) (ltPoly p)) x e hx = _
  exact zpEval_comp_closed p hp (ltIter p n) (ltPoly p)
    (ltPoly_coeff_zero p hp) x e hx

/-! ## 捻れ点の述語 -/

/-- **M79F-6: πⁿ-捻れ点** — x ∈ pℤ_p が Lubin–Tate 形式群の
    πⁿ-捻れ点であるとは [πⁿ](x) = f^{∘n}(x) = 0 となること。 -/
def IsTorsionPoint (p : Nat) (n : Nat) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) : Prop :=
  zpEval p (ltIter p n) x e hx = (zpRing p).zero

/-- **M79F-7a: 0 は捻れ点** — すべての n で [πⁿ](0) = 0。 -/
theorem zero_is_torsion (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    IsTorsionPoint p n ((zpRing p).zero) ((zpRing p).zero)
      (zero_point_witness p) :=
  zpEval_at_zero p (ltIter p n) (ltIter_coeff_zero p hp n)
    ((zpRing p).zero) (zero_point_witness p)

/-- **M79F-7b: π⁰-捻れの自明性** — [π⁰] = X なので
    π⁰-捻れ点 ⟺ x = 0。 -/
theorem torsion_zero_iff (p : Nat) (hp : 2 ≤ p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    IsTorsionPoint p 0 x e hx ↔ x = (zpRing p).zero := by
  show zpEval p (psX (zpRing p)) x e hx = (zpRing p).zero
    ↔ x = (zpRing p).zero
  rw [zpEval_X p hp x e hx]

/-- **定理 (M79F-7c): 捻れの段差単調性** — n-捻れ ⟹ (n+1)-捻れ。
    f^{∘(n+1)} = f∘f^{∘n}（ltIter_comm で順序を反転）なので
    [πⁿ⁺¹](x) = f([πⁿ](x)) = f(0) = 0。 -/
theorem torsion_mono (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    (h : IsTorsionPoint p n x e hx) :
    IsTorsionPoint p (n + 1) x e hx := by
  show zpEval p (ltIter p (n + 1)) x e hx = (zpRing p).zero
  have h1 : zpEval p (ltIter p (n + 1)) x e hx
      = zpEval p (psComp (zpRing p) (ltPoly p) (ltIter p n)) x e hx :=
    congrArg (fun H => zpEval p H x e hx) (ltIter_comm p hp n)
  rw [h1, zpEval_comp_closed p hp (ltPoly p) (ltIter p n)
    (ltIter_coeff_zero p hp n) x e hx]
  exact zpEval_eq_at_zero p (ltPoly p) (ltPoly_coeff_zero p hp)
    (zpEval p (ltIter p n) x e hx)
    ((zpRing p).mul e
      (zpEval p (psShift (zpRing p) (ltIter p n)) x e hx))
    (zpEval_closed p hp (ltIter p n) (ltIter_coeff_zero p hp n) x e hx)
    h

/-- **M79F-8: 捻れの単調性** — n ≤ m なら n-捻れ ⟹ m-捻れ
    （差分 d の帰納 + M79F-7c）。 -/
theorem torsion_le (p : Nat) (hp : 2 ≤ p) {n m : Nat} (h : n ≤ m)
    (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    (ht : IsTorsionPoint p n x e hx) :
    IsTorsionPoint p m x e hx := by
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  clear h
  induction d with
  | zero => exact ht
  | succ d ih => exact torsion_mono p hp (n + d) x e hx ih

end IUT
