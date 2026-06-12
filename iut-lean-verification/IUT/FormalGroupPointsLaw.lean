/-
  IUT/FormalGroupPointsLaw.lean — M81（群法則の点への輸送:
  点の群キャンペーン第五層）

  M80 の輸送連鎖律 (F(P,Q))(t) = F(P(t), Q(t)) を実行し、
  級数レベルで証明済みの群法則恒等式を**点の等式**にする:

  * M81-1 `lt2Sol_comp_X_zero` — 級数準備: F(X, 0) = X
    （M76 の加法則 [1]⊕[0] = [1] の正規化）
  * M81-2 `lt_point_unit` — **単位法則 F(x, 0) = x**
  * M81-3 `lt_point_comm` — **可換性 F(x, y) = F(y, x)**
    （独立な 2 点。係数対称性 lt2Sol_comm（M62）の二重和転写）
  * M81-4 `lt_point_inverse` — **逆元 F(x, ι(x)) = 0**
    （M75 の級数恒等式の輸送）
  * M81-5 `lt_point_module_add` — **[a]-加群則 F([a](x), [b](x)) = [a+b](x)**
    （M76 の輸送 — 点の集合への ℤ_p-作用）

  これで F(pℤ_p) は**単位・可換・逆元・ℤ_p-作用を備えた点の集合**
  （結合則の点輸送は 3 変数評価が必要 — 未形式化、正直申告）。
  全て選択公理不使用。
-/
import IUT.FormalGroupPoints2
import IUT.TorsionPoints

namespace IUT

/-! ## 級数準備 -/

/-- **M81-1: F(X, 0) = X**（[1]⊕[0] = [1] の正規化、M76）。 -/
theorem lt2Sol_comp_X_zero (p : Nat) (hp : IsPrime p) :
    ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p))
      (psZero (zpRing p)) = psX (zpRing p) := by
  have h := lt_module_add p hp ((zpRing p).one) ((zpRing p).zero)
  rw [CRing.add_zero (zpRing p) ((zpRing p).one), ltSol_one p hp,
    ltSol_zero p hp] at h
  exact h

/-! ## 単位法則 -/

/-- **定理 (M81-2): 単位法則の点版** — F(x, 0) = x。 -/
theorem lt_point_unit (p : Nat) (hp : IsPrime p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval2 p (lt2Sol p hp) x e ((zpRing p).zero) ((zpRing p).zero)
      hx (zero_point_witness p) = x := by
  have hchain := zpEval_ps21Comp p (lt2Sol p hp) (psX (zpRing p))
    (psZero (zpRing p)) rfl rfl x e hx
    ((zpRing p).mul e
      (zpEval p (psShift (zpRing p) (psX (zpRing p))) x e hx))
    ((zpRing p).mul e
      (zpEval p (psShift (zpRing p) (psZero (zpRing p))) x e hx))
    (zpEval_closed p hp.1 (psX (zpRing p)) rfl x e hx)
    (zpEval_closed p hp.1 (psZero (zpRing p)) rfl x e hx)
  have hser : zpEval p (ps21Comp (zpRing p) (lt2Sol p hp)
      (psX (zpRing p)) (psZero (zpRing p))) x e hx = x :=
    (congrArg (fun H => zpEval p H x e hx)
      (lt2Sol_comp_X_zero p hp)).trans (zpEval_X p hp.1 x e hx)
  refine Eq.trans ?_ (hchain.symm.trans hser)
  exact zpEval2_congr_points p (lt2Sol p hp) x e
    ((zpRing p).zero) ((zpRing p).zero)
    (zpEval p (psX (zpRing p)) x e hx) _
    (zpEval p (psZero (zpRing p)) x e hx) _
    hx (zero_point_witness p)
    (zpEval_closed p hp.1 (psX (zpRing p)) rfl x e hx)
    (zpEval_closed p hp.1 (psZero (zpRing p)) rfl x e hx)
    (zpEval_X p hp.1 x e hx).symm
    (zpEval_zero p x e hx).symm

/-! ## 可換性 -/

/-- **定理 (M81-3): 可換性の点版** — F(x, y) = F(y, x)
    （独立な 2 点。係数対称性 M62 の二重和転写）。 -/
theorem lt_point_comm (p : Nat) (hp : IsPrime p)
    (x ex y ey : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey) :
    zpEval2 p (lt2Sol p hp) x ex y ey hx hy
      = zpEval2 p (lt2Sol p hp) y ey x ex hy hx := by
  apply Subtype.ext
  funext n
  show (zpEval2Seg p (lt2Sol p hp) x y n).val n
    = (zpEval2Seg p (lt2Sol p hp) y x n).val n
  have hseg : zpEval2Seg p (lt2Sol p hp) y x n
      = zpEval2Seg p (lt2Sol p hp) x y n := by
    show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (lt2Sol p hp b a)
          ((zpRing p).mul (rpow (zpRing p) y a) (rpow (zpRing p) x b)))
        n) n
      = rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
          (zpRing p).mul (lt2Sol p hp b a)
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
          n) n
    rw [rsum_exchange (zpRing p) (fun b a =>
      (zpRing p).mul (lt2Sol p hp b a)
        ((zpRing p).mul (rpow (zpRing p) y a) (rpow (zpRing p) x b)))
      n n]
    refine rsum_congr (zpRing p) n (fun a _ => ?_)
    refine rsum_congr (zpRing p) n (fun b _ => ?_)
    show (zpRing p).mul (lt2Sol p hp b a)
        ((zpRing p).mul (rpow (zpRing p) y a) (rpow (zpRing p) x b))
      = (zpRing p).mul (lt2Sol p hp a b)
          ((zpRing p).mul (rpow (zpRing p) x b) (rpow (zpRing p) y a))
    rw [lt2Sol_comm p hp b a,
      (zpRing p).mul_comm (rpow (zpRing p) y a) (rpow (zpRing p) x b)]
  rw [hseg]

/-! ## 逆元 -/

/-- **定理 (M81-4): 逆元の点版** — F(x, ι(x)) = 0
    （M75 の級数恒等式の輸送）。 -/
theorem lt_point_inverse (p : Nat) (hp : IsPrime p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval2 p (lt2Sol p hp) x e
      (zpEval p (ltInv p hp) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltInv p hp)) x e hx))
      hx (zpEval_closed p hp.1 (ltInv p hp) rfl x e hx)
    = (zpRing p).zero := by
  have hchain := zpEval_ps21Comp p (lt2Sol p hp) (psX (zpRing p))
    (ltInv p hp) rfl rfl x e hx
    ((zpRing p).mul e
      (zpEval p (psShift (zpRing p) (psX (zpRing p))) x e hx))
    ((zpRing p).mul e
      (zpEval p (psShift (zpRing p) (ltInv p hp)) x e hx))
    (zpEval_closed p hp.1 (psX (zpRing p)) rfl x e hx)
    (zpEval_closed p hp.1 (ltInv p hp) rfl x e hx)
  have hser : zpEval p (ps21Comp (zpRing p) (lt2Sol p hp)
      (psX (zpRing p)) (ltInv p hp)) x e hx = (zpRing p).zero :=
    (congrArg (fun H => zpEval p H x e hx)
      (lt_formal_group_inverse p hp)).trans (zpEval_zero p x e hx)
  refine Eq.trans ?_ (hchain.symm.trans hser)
  exact zpEval2_congr_points p (lt2Sol p hp) x e
    (zpEval p (ltInv p hp) x e hx) _
    (zpEval p (psX (zpRing p)) x e hx) _
    (zpEval p (ltInv p hp) x e hx) _
    hx (zpEval_closed p hp.1 (ltInv p hp) rfl x e hx)
    (zpEval_closed p hp.1 (psX (zpRing p)) rfl x e hx)
    (zpEval_closed p hp.1 (ltInv p hp) rfl x e hx)
    (zpEval_X p hp.1 x e hx).symm rfl

/-! ## [a]-加群則 -/

/-- **定理 (M81-5): [a]-加群則の点版** — F([a](x), [b](x)) = [a+b](x)
    （M76 の輸送 — 点の集合への ℤ_p-作用の加法性）。 -/
theorem lt_point_module_add (p : Nat) (hp : IsPrime p)
    (a b : (Zp p).carrier) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval2 p (lt2Sol p hp)
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval p (ltSol p hp b) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp b)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
      (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
    = zpEval p (ltSol p hp ((zpRing p).add a b)) x e hx :=
  (zpEval_ps21Comp p (lt2Sol p hp) (ltSol p hp a) (ltSol p hp b)
    rfl rfl x e hx _ _
    (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
    (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)).symm.trans
    (congrArg (fun H => zpEval p H x e hx) (lt_module_add p hp a b))

end IUT
