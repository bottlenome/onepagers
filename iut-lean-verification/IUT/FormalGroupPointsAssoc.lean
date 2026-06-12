/-
  IUT/FormalGroupPointsAssoc.lean — M85（結合則の点輸送:
  点の群キャンペーン最終層）

  結合則 **F(F(x,y), z) = F(x, F(y,z))** を pℤ_p の点で完全証明し、
  **F(pℤ_p) の群公理（単位・可換・逆元・結合・ℤ_p-作用）を完結**させる。

  * M85-1 `zpEval3_liftYZ` / `zpEval2_ps2X` / `zpEval3_ps3X` —
    lift と座標の評価の残り（(liftYZ F)(x,y,z) = F(y,z)・X(x,y) = x・
    X(x,y,z) = x）
  * M85-2 `zpEval2_val_one` / `zpEval2_closed'` — F₀₀ = 0 なら
    F(x,y) ∈ pℤ_p（witness は M43 の zpDivP による明示構成）
  * M85-3 `proj_zpEval3Seg` / `proj_xyz_pow_low` — 3 変数部分和の
    射影平坦化と三重単項式のレベル消滅
  * M85-4 `zpEval3_ps23Comp` — **代入連鎖律**
    (F(P,Q))(x,y,z) = F(P(x,y,z), Q(x,y,z))
  * M85-5 `lt_point_assoc` — **結合則の点版（本丸）**

  全て選択公理不使用。
-/
import IUT.FormalGroupPointsMul3

namespace IUT

/-! ## lift と座標の評価（残り） -/

/-- **M85-1a: lift の評価** — (liftYZ F)(x, y, z) = F(y, z)
    （各行で a = 0 への一点集中・x⁰ = 1）。 -/
theorem zpEval3_liftYZ (p : Nat) (F : PS2 (zpRing p))
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez) :
    zpEval3 p (liftYZ (zpRing p) F) x ex y ey z ez hx hy hz
      = zpEval2 p F y ey z ez hy hz := by
  apply Subtype.ext
  funext n
  show (zpEval3Seg p (liftYZ (zpRing p) F) x y z n).val n
    = (zpEval2Seg p F y z n).val n
  have hseg : zpEval3Seg p (liftYZ (zpRing p) F) x y z n
      = zpEval2Seg p F y z n := by
    cases n with
    | zero => rfl
    | succ m =>
      show rsum (zpRing p) (fun c => (zpRing p).mul
          (zpEval2Seg p (liftYZ (zpRing p) F c) x y (m + 1))
          (rpow (zpRing p) z c)) (m + 1)
        = rsum (zpRing p) (fun c => rsum (zpRing p) (fun b =>
            (zpRing p).mul (F c b)
              ((zpRing p).mul (rpow (zpRing p) y b)
                (rpow (zpRing p) z c))) (m + 1)) (m + 1)
      refine rsum_congr (zpRing p) (m + 1) (fun c _ => ?_)
      have hrow : zpEval2Seg p (liftYZ (zpRing p) F c) x y (m + 1)
          = rsum (zpRing p) (fun b => (zpRing p).mul (F c b)
              ((zpRing p).mul (rpow (zpRing p) x 0)
                (rpow (zpRing p) y b))) (m + 1) := by
        show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
            (zpRing p).mul (liftYZ (zpRing p) F c b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))) (m + 1)) (m + 1) = _
        refine rsum_congr (zpRing p) (m + 1) (fun b _ => ?_)
        show rsum (zpRing p) (fun a =>
            (zpRing p).mul (liftYZ (zpRing p) F c b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))) (m + 1)
          = (zpRing p).mul (F c b)
              ((zpRing p).mul (rpow (zpRing p) x 0)
                (rpow (zpRing p) y b))
        have hs := rsum_single (zpRing p) (fun a =>
            (zpRing p).mul (liftYZ (zpRing p) F c b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))) 0 (m + 1) (by omega)
          (fun a _ ha => by
            show (zpRing p).mul (liftYZ (zpRing p) F c b a)
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y b)) = (zpRing p).zero
            rw [show liftYZ (zpRing p) F c b a = (zpRing p).zero from
              if_neg ha]
            exact (zpRing p).zero_mul _)
        rw [hs]
        rfl
      rw [hrow, rsum_mul_right (zpRing p) (fun b =>
          (zpRing p).mul (F c b)
            ((zpRing p).mul (rpow (zpRing p) x 0)
              (rpow (zpRing p) y b)))
          (rpow (zpRing p) z c) (m + 1)]
      refine rsum_congr (zpRing p) (m + 1) (fun b _ => ?_)
      show (zpRing p).mul ((zpRing p).mul (F c b)
          ((zpRing p).mul (rpow (zpRing p) x 0) (rpow (zpRing p) y b)))
          (rpow (zpRing p) z c)
        = (zpRing p).mul (F c b)
            ((zpRing p).mul (rpow (zpRing p) y b) (rpow (zpRing p) z c))
      rw [show (zpRing p).mul (rpow (zpRing p) x 0) (rpow (zpRing p) y b)
          = rpow (zpRing p) y b from (zpRing p).one_mul _]
      exact (zpRing p).mul_assoc (F c b) (rpow (zpRing p) y b)
        (rpow (zpRing p) z c)
  rw [hseg]

/-- **M85-1b: 座標の 2 変数評価** — X(x, y) = x。 -/
theorem zpEval2_ps2X (p : Nat) (hp : 2 ≤ p) (x ex y ey : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey) :
    zpEval2 p (ps2X (zpRing p)) x ex y ey hx hy = x := by
  apply Subtype.ext
  funext n
  show (zpEval2Seg p (ps2X (zpRing p)) x y n).val n = x.val n
  -- 行 b ≠ 0 は 0、行 b = 0 は psX
  have hrowz : ∀ b, b ≠ 0 → ∀ N, rsum (zpRing p) (fun a =>
      (zpRing p).mul (ps2X (zpRing p) b a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      N = (zpRing p).zero := by
    intro b hb N
    have hz : rsum (zpRing p) (fun a =>
        (zpRing p).mul (ps2X (zpRing p) b a)
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        N = rsum (zpRing p) (fun _ => (zpRing p).zero) N :=
      rsum_congr (zpRing p) N (fun a _ => by
        rw [show ps2X (zpRing p) b = (psRing (zpRing p)).zero from
          if_neg hb]
        exact (zpRing p).zero_mul _)
    rw [hz]
    exact rsum_const_zero (zpRing p) N
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ m =>
    have houter : zpEval2Seg p (ps2X (zpRing p)) x y (m + 1)
        = rsum (zpRing p) (fun a =>
            (zpRing p).mul (ps2X (zpRing p) 0 a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y 0))) (m + 1) := by
      show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
          (zpRing p).mul (ps2X (zpRing p) b a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y b))) (m + 1)) (m + 1) = _
      exact rsum_single (zpRing p) (fun b => rsum (zpRing p) (fun a =>
          (zpRing p).mul (ps2X (zpRing p) b a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y b))) (m + 1)) 0 (m + 1) (by omega)
        (fun b _ hb => by
          show rsum (zpRing p) (fun a =>
              (zpRing p).mul (ps2X (zpRing p) b a)
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y b))) (m + 1) = (zpRing p).zero
          exact hrowz b hb (m + 1))
    cases m with
    | zero =>
      have h1 : zpEval2Seg p (ps2X (zpRing p)) x y 1 = (zpRing p).zero := by
        rw [houter]
        show (zpRing p).add (zpRing p).zero
            ((zpRing p).mul (psX (zpRing p) 0)
              ((zpRing p).mul (rpow (zpRing p) x 0)
                (rpow (zpRing p) y 0))) = (zpRing p).zero
        rw [show psX (zpRing p) 0 = (zpRing p).zero from rfl,
          (zpRing p).zero_mul, (zpRing p).zero_add]
      have hx1 : x.val 1 = Quot.mk (modCong (p ^ 1)).rel 0 :=
        (zp_dvd_p_iff p hp x).mp ⟨ex, hx⟩
      rw [h1, hx1]
      rfl
    | succ m' =>
      have hseg : zpEval2Seg p (ps2X (zpRing p)) x y (m' + 2) = x := by
        rw [houter]
        have hs := rsum_single (zpRing p) (fun a =>
            (zpRing p).mul (psX (zpRing p) a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y 0))) 1 (m' + 2) (by omega)
          (fun a _ ha => by
            show (zpRing p).mul (psX (zpRing p) a)
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y 0)) = (zpRing p).zero
            rw [show psX (zpRing p) a = (zpRing p).zero from if_neg ha]
            exact (zpRing p).zero_mul _)
        show rsum (zpRing p) (fun a =>
            (zpRing p).mul (psX (zpRing p) a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y 0))) (m' + 2) = x
        rw [hs]
        show (zpRing p).mul (psX (zpRing p) 1)
            ((zpRing p).mul (rpow (zpRing p) x 1) (rpow (zpRing p) y 0))
          = x
        rw [show psX (zpRing p) 1 = (zpRing p).one from rfl,
          (zpRing p).one_mul,
          show (zpRing p).mul (rpow (zpRing p) x 1) (rpow (zpRing p) y 0)
            = rpow (zpRing p) x 1 from by
            rw [(zpRing p).mul_comm]
            exact (zpRing p).one_mul _]
        show (zpRing p).mul ((zpRing p).one) x = x
        exact (zpRing p).one_mul x
      rw [hseg]

/-- **M85-1c: 座標の 3 変数評価** — X(x, y, z) = x
    （c = 0 集中 + M85-1b）。 -/
theorem zpEval3_ps3X (p : Nat) (hp : 2 ≤ p)
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez) :
    zpEval3 p (ps3X (zpRing p)) x ex y ey z ez hx hy hz = x := by
  apply Subtype.ext
  funext n
  show (zpEval3Seg p (ps3X (zpRing p)) x y z n).val n = x.val n
  have hseg : zpEval3Seg p (ps3X (zpRing p)) x y z n
      = zpEval2Seg p (ps2X (zpRing p)) x y n := by
    cases n with
    | zero => rfl
    | succ m =>
      have hs := rsum_single (zpRing p) (fun c => (zpRing p).mul
          (zpEval2Seg p (ps3X (zpRing p) c) x y (m + 1))
          (rpow (zpRing p) z c)) 0 (m + 1) (by omega)
        (fun c _ hc => by
          show (zpRing p).mul
              (zpEval2Seg p (ps3X (zpRing p) c) x y (m + 1))
              (rpow (zpRing p) z c) = (zpRing p).zero
          rw [show ps3X (zpRing p) c = (psRing (psRing (zpRing p))).zero
              from if_neg hc,
            zpEval2Seg_zero p x y (m + 1)]
          exact (zpRing p).zero_mul _)
      show rsum (zpRing p) (fun c => (zpRing p).mul
          (zpEval2Seg p (ps3X (zpRing p) c) x y (m + 1))
          (rpow (zpRing p) z c)) (m + 1)
        = zpEval2Seg p (ps2X (zpRing p)) x y (m + 1)
      rw [hs]
      show (zpRing p).mul
          (zpEval2Seg p (ps2X (zpRing p)) x y (m + 1)) ((zpRing p).one)
        = zpEval2Seg p (ps2X (zpRing p)) x y (m + 1)
      rw [(zpRing p).mul_comm]
      exact (zpRing p).one_mul _
  rw [hseg]
  exact congrFun (congrArg Subtype.val
    (zpEval2_ps2X p hp x ex y ey hx hy)) n

/-! ## F(x,y) ∈ pℤ_p（witness の明示供給） -/

/-- **M85-2a: 一次成分の消滅** — F₀₀ = 0 なら F(x,y) のレベル 1
    成分は 0。 -/
theorem zpEval2_val_one (p : Nat) (F : PS2 (zpRing p))
    (hF : F 0 0 = (zpRing p).zero) (x ex y ey : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey) :
    (zpEval2 p F x ex y ey hx hy).val 1
      = Quot.mk (modCong (p ^ 1)).rel 0 := by
  show (zpEval2Seg p F x y 1).val 1 = Quot.mk (modCong (p ^ 1)).rel 0
  have h1 : zpEval2Seg p F x y 1 = (zpRing p).zero := by
    show (zpRing p).add (zpRing p).zero
        ((zpRing p).add (zpRing p).zero
          ((zpRing p).mul (F 0 0)
            ((zpRing p).mul (rpow (zpRing p) x 0)
              (rpow (zpRing p) y 0)))) = (zpRing p).zero
    rw [hF, (zpRing p).zero_mul, (zpRing p).zero_add,
      (zpRing p).zero_add]
  rw [h1]
  rfl

/-- **M85-2b: F(x,y) ∈ pℤ_p の明示 witness**（M43 の zpDivP）。 -/
theorem zpEval2_closed' (p : Nat) (hp : 2 ≤ p) (F : PS2 (zpRing p))
    (hF : F 0 0 = (zpRing p).zero) (x ex y ey : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey) :
    zpEval2 p F x ex y ey hx hy
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          (zpDivP p hp (zpEval2 p F x ex y ey hx hy)) :=
  (zpDivP_mul_cancel p hp (zpEval2 p F x ex y ey hx hy)
    (zpEval2_val_one p F hF x ex y ey hx hy)).symm

/-! ## 平坦化と消滅補題 -/

/-- **M85-3a: 3 変数部分和の平坦化**（純 ℤ_p レベル）。 -/
theorem zpEval3Seg_flat (p : Nat) (W : PS3 (zpRing p))
    (x y z : (Zp p).carrier) (n : Nat) :
    zpEval3Seg p W x y z n
      = rsum (zpRing p) (fun c => rsum (zpRing p) (fun b =>
          rsum (zpRing p) (fun a => (zpRing p).mul (W c b a)
            ((zpRing p).mul
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))
              (rpow (zpRing p) z c))) n) n) n := by
  show rsum (zpRing p) (fun c => (zpRing p).mul
      (zpEval2Seg p (W c) x y n) (rpow (zpRing p) z c)) n = _
  refine rsum_congr (zpRing p) n (fun c _ => ?_)
  show (zpRing p).mul (rsum (zpRing p) (fun b =>
      rsum (zpRing p) (fun a => (zpRing p).mul (W c b a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      n) n) (rpow (zpRing p) z c) = _
  rw [rsum_mul_right (zpRing p) (fun b =>
      rsum (zpRing p) (fun a => (zpRing p).mul (W c b a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      n) (rpow (zpRing p) z c) n]
  refine rsum_congr (zpRing p) n (fun b _ => ?_)
  show (zpRing p).mul (rsum (zpRing p) (fun a =>
      (zpRing p).mul (W c b a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      n) (rpow (zpRing p) z c) = _
  rw [rsum_mul_right (zpRing p) (fun a =>
      (zpRing p).mul (W c b a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      (rpow (zpRing p) z c) n]
  exact rsum_congr (zpRing p) n (fun a _ =>
    (zpRing p).mul_assoc (W c b a) _ _)

/-- **M85-3b: 三重単項式のレベル消滅** — n ≤ a + b + c なら
    proj_n(x^a·y^b·z^c) = 0（p^{a+b+c} 因子の抽出）。 -/
theorem proj_xyz_pow_low (p : Nat) (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez)
    {n a b c : Nat} (h : n ≤ a + b + c) :
    (projRing p n).map ((zpRing p).mul
      ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
      (rpow (zpRing p) z c)) = (zmodRing (p ^ n)).zero := by
  have hsplit : (zpRing p).mul
      ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
      (rpow (zpRing p) z c)
      = (zpRing p).mul
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (a + b + c))
          ((zpRing p).mul
            ((zpRing p).mul (rpow (zpRing p) ex a) (rpow (zpRing p) ey b))
            (rpow (zpRing p) ez c)) := by
    rw [hx, hy, hz,
      rpow_mul_dist (zpRing p) ((toZp p).map ((p : Nat) : Int)) ex a,
      rpow_mul_dist (zpRing p) ((toZp p).map ((p : Nat) : Int)) ey b,
      rpow_mul_dist (zpRing p) ((toZp p).map ((p : Nat) : Int)) ez c,
      CRing.mul_mul_comm (zpRing p)
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) a)
        (rpow (zpRing p) ex a)
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) b)
        (rpow (zpRing p) ey b),
      CRing.mul_mul_comm (zpRing p)
        ((zpRing p).mul
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) a)
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) b))
        ((zpRing p).mul (rpow (zpRing p) ex a) (rpow (zpRing p) ey b))
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) c)
        (rpow (zpRing p) ez c),
      ← rpow_add (zpRing p) ((toZp p).map ((p : Nat) : Int)) a b,
      ← rpow_add (zpRing p) ((toZp p).map ((p : Nat) : Int)) (a + b) c]
  have hexp : rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (a + b + c)
      = (zpRing p).mul
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n)
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))
            (a + b + c - n)) :=
    (congrArg (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)))
      (show a + b + c = n + (a + b + c - n) by omega)).trans
      (rpow_add (zpRing p) ((toZp p).map ((p : Nat) : Int)) n
        (a + b + c - n))
  rw [hsplit, hexp, (projRing p n).map_mul, (projRing p n).map_mul,
    proj_rpow_p_zero p n, CRing.zero_mul (zmodRing (p ^ n)),
    CRing.zero_mul (zmodRing (p ^ n))]

/-- **M85-3c: 冪積の部分和の高次消滅** — n ≤ a₁ + b₁ なら
    proj_n(Seg3(P^{a₁}·Q^{b₁}) n) = 0（係数は総次数 ≥ a₁+b₁ にのみ
    分布し、その単項式はレベル n で消える）。 -/
theorem proj_Seg3_powpow_high (p : Nat) (P Q : PS3 (zpRing p))
    (hP : P 0 0 0 = (zpRing p).zero) (hQ : Q 0 0 0 = (zpRing p).zero)
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez)
    {n a₁ b₁ : Nat} (h : n ≤ a₁ + b₁) :
    (projRing p n).map (zpEval3Seg p
      (psMul (psRing (psRing (zpRing p)))
        (psPow (psRing (psRing (zpRing p))) P a₁)
        (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n)
      = (zmodRing (p ^ n)).zero := by
  rw [zpEval3Seg_flat p (psMul (psRing (psRing (zpRing p)))
      (psPow (psRing (psRing (zpRing p))) P a₁)
      (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n,
    ringHom_rsum (projRing p n) _ n]
  have hzz : rsum (zmodRing (p ^ n)) (fun c =>
      (projRing p n).map (rsum (zpRing p) (fun b =>
        rsum (zpRing p) (fun a => (zpRing p).mul
          (psMul (psRing (psRing (zpRing p)))
            (psPow (psRing (psRing (zpRing p))) P a₁)
            (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
          ((zpRing p).mul
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
            (rpow (zpRing p) z c))) n) n)) n
      = rsum (zmodRing (p ^ n)) (fun _ => (zmodRing (p ^ n)).zero) n :=
    rsum_congr (zmodRing (p ^ n)) n (fun c _ => by
      rw [ringHom_rsum (projRing p n) _ n]
      have hz2 : rsum (zmodRing (p ^ n)) (fun b =>
          (projRing p n).map (rsum (zpRing p) (fun a =>
            (zpRing p).mul
              (psMul (psRing (psRing (zpRing p)))
                (psPow (psRing (psRing (zpRing p))) P a₁)
                (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
              ((zpRing p).mul
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y b))
                (rpow (zpRing p) z c))) n)) n
          = rsum (zmodRing (p ^ n)) (fun _ => (zmodRing (p ^ n)).zero)
              n :=
        rsum_congr (zmodRing (p ^ n)) n (fun b _ => by
          rw [ringHom_rsum (projRing p n) _ n]
          have hz3 : rsum (zmodRing (p ^ n)) (fun a =>
              (projRing p n).map ((zpRing p).mul
                (psMul (psRing (psRing (zpRing p)))
                  (psPow (psRing (psRing (zpRing p))) P a₁)
                  (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
                ((zpRing p).mul
                  ((zpRing p).mul (rpow (zpRing p) x a)
                    (rpow (zpRing p) y b))
                  (rpow (zpRing p) z c)))) n
              = rsum (zmodRing (p ^ n))
                  (fun _ => (zmodRing (p ^ n)).zero) n :=
            rsum_congr (zmodRing (p ^ n)) n (fun a _ => by
              rw [(projRing p n).map_mul]
              cases Nat.lt_or_ge (a + b + c) (a₁ + b₁) with
              | inl hlow =>
                rw [ps3PowPow_low (zpRing p) P Q hP hQ a₁ b₁ c b a hlow,
                  RingHom.map_zero (projRing p n)]
                exact CRing.zero_mul (zmodRing (p ^ n)) _
              | inr hhigh =>
                rw [proj_xyz_pow_low p x ex y ey z ez hx hy hz
                  (show n ≤ a + b + c by omega)]
                exact CRing.mul_zero (zmodRing (p ^ n)) _)
          show rsum (zmodRing (p ^ n)) (fun a =>
              (projRing p n).map ((zpRing p).mul
                (psMul (psRing (psRing (zpRing p)))
                  (psPow (psRing (psRing (zpRing p))) P a₁)
                  (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
                ((zpRing p).mul
                  ((zpRing p).mul (rpow (zpRing p) x a)
                    (rpow (zpRing p) y b))
                  (rpow (zpRing p) z c)))) n = (zmodRing (p ^ n)).zero
          rw [hz3]
          exact rsum_const_zero (zmodRing (p ^ n)) n)
      show rsum (zmodRing (p ^ n)) (fun b =>
          (projRing p n).map (rsum (zpRing p) (fun a =>
            (zpRing p).mul
              (psMul (psRing (psRing (zpRing p)))
                (psPow (psRing (psRing (zpRing p))) P a₁)
                (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
              ((zpRing p).mul
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y b))
                (rpow (zpRing p) z c))) n)) n = (zmodRing (p ^ n)).zero
      rw [hz2]
      exact rsum_const_zero (zmodRing (p ^ n)) n)
  rw [hzz]
  exact rsum_const_zero (zmodRing (p ^ n)) n

/-! ## 代入連鎖律 -/

/-- **M85-4a: 部分和の代入恒等式**（純 ℤ_p レベル・境界 3n） —
    Seg3(F(P,Q)) = Σ_{b₁,a₁<3n} F_{b₁a₁}·Seg3(P^{a₁}Q^{b₁})。 -/
theorem zpEval3Seg_ps23Comp (p : Nat) (F : PS2 (zpRing p))
    (P Q : PS3 (zpRing p))
    (hP : P 0 0 0 = (zpRing p).zero) (hQ : Q 0 0 0 = (zpRing p).zero)
    (x y z : (Zp p).carrier) (n : Nat) :
    zpEval3Seg p (ps23Comp (zpRing p) F P Q) x y z n
      = rsum (zpRing p) (fun b₁ => rsum (zpRing p) (fun a₁ =>
          (zpRing p).mul (F b₁ a₁)
            (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
              (psPow (psRing (psRing (zpRing p))) P a₁)
              (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n))
          (3 * n)) (3 * n) := by
  rw [zpEval3Seg_flat p (ps23Comp (zpRing p) F P Q) x y z n]
  have hA : rsum (zpRing p) (fun c => rsum (zpRing p) (fun b =>
        rsum (zpRing p) (fun a => (zpRing p).mul
          (ps23Comp (zpRing p) F P Q c b a)
          ((zpRing p).mul
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
            (rpow (zpRing p) z c))) n) n) n
      = rsum (zpRing p) (fun c => rsum (zpRing p) (fun b =>
          rsum (zpRing p) (fun a => rsum (zpRing p) (fun b₁ =>
            rsum (zpRing p) (fun a₁ => (zpRing p).mul (F b₁ a₁)
              ((zpRing p).mul
                (psMul (psRing (psRing (zpRing p)))
                  (psPow (psRing (psRing (zpRing p))) P a₁)
                  (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
                ((zpRing p).mul
                  ((zpRing p).mul (rpow (zpRing p) x a)
                    (rpow (zpRing p) y b))
                  (rpow (zpRing p) z c)))) (3 * n)) (3 * n)) n) n) n :=
    rsum_congr (zpRing p) n (fun c hc =>
      rsum_congr (zpRing p) n (fun b hb =>
        rsum_congr (zpRing p) n (fun a ha => by
          rw [ps23Comp_pad3 (zpRing p) F P Q hP hQ (3 * n) c b a
              (by omega),
            rsum_mul_right (zpRing p) _
              ((zpRing p).mul
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y b))
                (rpow (zpRing p) z c)) (3 * n)]
          refine rsum_congr (zpRing p) (3 * n) (fun b₁ _ => ?_)
          rw [rsum_mul_right (zpRing p) _
            ((zpRing p).mul
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))
              (rpow (zpRing p) z c)) (3 * n)]
          exact rsum_congr (zpRing p) (3 * n) (fun a₁ _ =>
            (zpRing p).mul_assoc (F b₁ a₁) _ _))))
  rw [hA]
  -- 添字交換 ×6: (c,b,a,b₁,a₁) → (b₁,a₁,c,b,a)
  have e1 : ∀ c b, c < n → b < n →
      rsum (zpRing p) (fun a => rsum (zpRing p) (fun b₁ =>
        rsum (zpRing p) (fun a₁ => (zpRing p).mul (F b₁ a₁)
          ((zpRing p).mul
            (psMul (psRing (psRing (zpRing p)))
              (psPow (psRing (psRing (zpRing p))) P a₁)
              (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
            ((zpRing p).mul
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))
              (rpow (zpRing p) z c)))) (3 * n)) (3 * n)) n
      = rsum (zpRing p) (fun b₁ => rsum (zpRing p) (fun a₁ =>
          rsum (zpRing p) (fun a => (zpRing p).mul (F b₁ a₁)
            ((zpRing p).mul
              (psMul (psRing (psRing (zpRing p)))
                (psPow (psRing (psRing (zpRing p))) P a₁)
                (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
              ((zpRing p).mul
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y b))
                (rpow (zpRing p) z c)))) n) (3 * n)) (3 * n) := by
    intro c b _ _
    rw [rsum_exchange (zpRing p) (fun a b₁ =>
      rsum (zpRing p) (fun a₁ => (zpRing p).mul (F b₁ a₁)
        ((zpRing p).mul
          (psMul (psRing (psRing (zpRing p)))
            (psPow (psRing (psRing (zpRing p))) P a₁)
            (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
          ((zpRing p).mul
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y b))
            (rpow (zpRing p) z c)))) (3 * n)) n (3 * n)]
    exact rsum_congr (zpRing p) (3 * n) (fun b₁ _ =>
      rsum_exchange (zpRing p) (fun a a₁ =>
        (zpRing p).mul (F b₁ a₁)
          ((zpRing p).mul
            (psMul (psRing (psRing (zpRing p)))
              (psPow (psRing (psRing (zpRing p))) P a₁)
              (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
            ((zpRing p).mul
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))
              (rpow (zpRing p) z c)))) n (3 * n))
  have e2 : ∀ c, c < n →
      rsum (zpRing p) (fun b => rsum (zpRing p) (fun b₁ =>
        rsum (zpRing p) (fun a₁ => rsum (zpRing p) (fun a =>
          (zpRing p).mul (F b₁ a₁)
            ((zpRing p).mul
              (psMul (psRing (psRing (zpRing p)))
                (psPow (psRing (psRing (zpRing p))) P a₁)
                (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
              ((zpRing p).mul
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y b))
                (rpow (zpRing p) z c)))) n) (3 * n)) (3 * n)) n
      = rsum (zpRing p) (fun b₁ => rsum (zpRing p) (fun a₁ =>
          rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
            (zpRing p).mul (F b₁ a₁)
              ((zpRing p).mul
                (psMul (psRing (psRing (zpRing p)))
                  (psPow (psRing (psRing (zpRing p))) P a₁)
                  (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
                ((zpRing p).mul
                  ((zpRing p).mul (rpow (zpRing p) x a)
                    (rpow (zpRing p) y b))
                  (rpow (zpRing p) z c)))) n) n) (3 * n)) (3 * n) := by
    intro c _
    rw [rsum_exchange (zpRing p) (fun b b₁ =>
      rsum (zpRing p) (fun a₁ => rsum (zpRing p) (fun a =>
        (zpRing p).mul (F b₁ a₁)
          ((zpRing p).mul
            (psMul (psRing (psRing (zpRing p)))
              (psPow (psRing (psRing (zpRing p))) P a₁)
              (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
            ((zpRing p).mul
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))
              (rpow (zpRing p) z c)))) n) (3 * n)) n (3 * n)]
    exact rsum_congr (zpRing p) (3 * n) (fun b₁ _ =>
      rsum_exchange (zpRing p) (fun b a₁ =>
        rsum (zpRing p) (fun a => (zpRing p).mul (F b₁ a₁)
          ((zpRing p).mul
            (psMul (psRing (psRing (zpRing p)))
              (psPow (psRing (psRing (zpRing p))) P a₁)
              (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
            ((zpRing p).mul
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))
              (rpow (zpRing p) z c)))) n) n (3 * n))
  have e3 : rsum (zpRing p) (fun c => rsum (zpRing p) (fun b₁ =>
        rsum (zpRing p) (fun a₁ => rsum (zpRing p) (fun b =>
          rsum (zpRing p) (fun a => (zpRing p).mul (F b₁ a₁)
            ((zpRing p).mul
              (psMul (psRing (psRing (zpRing p)))
                (psPow (psRing (psRing (zpRing p))) P a₁)
                (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
              ((zpRing p).mul
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y b))
                (rpow (zpRing p) z c)))) n) n) (3 * n)) (3 * n)) n
      = rsum (zpRing p) (fun b₁ => rsum (zpRing p) (fun a₁ =>
          rsum (zpRing p) (fun c => rsum (zpRing p) (fun b =>
            rsum (zpRing p) (fun a => (zpRing p).mul (F b₁ a₁)
              ((zpRing p).mul
                (psMul (psRing (psRing (zpRing p)))
                  (psPow (psRing (psRing (zpRing p))) P a₁)
                  (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
                ((zpRing p).mul
                  ((zpRing p).mul (rpow (zpRing p) x a)
                    (rpow (zpRing p) y b))
                  (rpow (zpRing p) z c)))) n) n) n) (3 * n)) (3 * n) := by
    rw [rsum_exchange (zpRing p) (fun c b₁ =>
      rsum (zpRing p) (fun a₁ => rsum (zpRing p) (fun b =>
        rsum (zpRing p) (fun a => (zpRing p).mul (F b₁ a₁)
          ((zpRing p).mul
            (psMul (psRing (psRing (zpRing p)))
              (psPow (psRing (psRing (zpRing p))) P a₁)
              (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
            ((zpRing p).mul
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))
              (rpow (zpRing p) z c)))) n) n) (3 * n)) n (3 * n)]
    exact rsum_congr (zpRing p) (3 * n) (fun b₁ _ =>
      rsum_exchange (zpRing p) (fun c a₁ =>
        rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
          (zpRing p).mul (F b₁ a₁)
            ((zpRing p).mul
              (psMul (psRing (psRing (zpRing p)))
                (psPow (psRing (psRing (zpRing p))) P a₁)
                (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
              ((zpRing p).mul
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y b))
                (rpow (zpRing p) z c)))) n) n) n (3 * n))
  rw [rsum_congr (zpRing p) n (fun c hc =>
      rsum_congr (zpRing p) n (fun b hb => e1 c b hc hb)),
    rsum_congr (zpRing p) n (fun c hc => e2 c hc), e3]
  -- 折りたたみ: 各 (b₁,a₁) で F を括り出し flat を畳む
  refine rsum_congr (zpRing p) (3 * n) (fun b₁ _ => ?_)
  refine rsum_congr (zpRing p) (3 * n) (fun a₁ _ => ?_)
  rw [zpEval3Seg_flat p (psMul (psRing (psRing (zpRing p)))
      (psPow (psRing (psRing (zpRing p))) P a₁)
      (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n,
    rsum_mul_left (zpRing p) (fun c => rsum (zpRing p) (fun b =>
      rsum (zpRing p) (fun a => (zpRing p).mul
        (psMul (psRing (psRing (zpRing p)))
          (psPow (psRing (psRing (zpRing p))) P a₁)
          (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
        ((zpRing p).mul
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
          (rpow (zpRing p) z c))) n) n) (F b₁ a₁) n]
  refine rsum_congr (zpRing p) n (fun c _ => ?_)
  show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
      (zpRing p).mul (F b₁ a₁)
        ((zpRing p).mul
          (psMul (psRing (psRing (zpRing p)))
            (psPow (psRing (psRing (zpRing p))) P a₁)
            (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
          ((zpRing p).mul
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
            (rpow (zpRing p) z c)))) n) n
    = (zpRing p).mul (F b₁ a₁) (rsum (zpRing p) (fun b =>
        rsum (zpRing p) (fun a => (zpRing p).mul
          (psMul (psRing (psRing (zpRing p)))
            (psPow (psRing (psRing (zpRing p))) P a₁)
            (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
          ((zpRing p).mul
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
            (rpow (zpRing p) z c))) n) n)
  rw [rsum_mul_left (zpRing p) (fun b => rsum (zpRing p) (fun a =>
      (zpRing p).mul
        (psMul (psRing (psRing (zpRing p)))
          (psPow (psRing (psRing (zpRing p))) P a₁)
          (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
        ((zpRing p).mul
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
          (rpow (zpRing p) z c))) n) (F b₁ a₁) n]
  refine rsum_congr (zpRing p) n (fun b _ => ?_)
  show rsum (zpRing p) (fun a => (zpRing p).mul (F b₁ a₁)
      ((zpRing p).mul
        (psMul (psRing (psRing (zpRing p)))
          (psPow (psRing (psRing (zpRing p))) P a₁)
          (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
        ((zpRing p).mul
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
          (rpow (zpRing p) z c)))) n
    = (zpRing p).mul (F b₁ a₁) (rsum (zpRing p) (fun a =>
        (zpRing p).mul
          (psMul (psRing (psRing (zpRing p)))
            (psPow (psRing (psRing (zpRing p))) P a₁)
            (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
          ((zpRing p).mul
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
            (rpow (zpRing p) z c))) n)
  exact (rsum_mul_left (zpRing p) (fun a => (zpRing p).mul
      (psMul (psRing (psRing (zpRing p)))
        (psPow (psRing (psRing (zpRing p))) P a₁)
        (psPow (psRing (psRing (zpRing p))) Q b₁) c b a)
      ((zpRing p).mul
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))
        (rpow (zpRing p) z c))) (F b₁ a₁) n).symm

/-- **定理 (M85-4b): 代入連鎖律** —
    (F(P,Q))(x,y,z) = F(P(x,y,z), Q(x,y,z))。 -/
theorem zpEval3_ps23Comp (p : Nat) (F : PS2 (zpRing p))
    (P Q : PS3 (zpRing p))
    (hP : P 0 0 0 = (zpRing p).zero) (hQ : Q 0 0 0 = (zpRing p).zero)
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez)
    (eu ev : (Zp p).carrier)
    (hu : zpEval3 p P x ex y ey z ez hx hy hz
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) eu)
    (hv : zpEval3 p Q x ex y ey z ez hx hy hz
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ev) :
    zpEval3 p (ps23Comp (zpRing p) F P Q) x ex y ey z ez hx hy hz
      = zpEval2 p F (zpEval3 p P x ex y ey z ez hx hy hz) eu
          (zpEval3 p Q x ex y ey z ez hx hy hz) ev hu hv := by
  apply Subtype.ext
  funext n
  have hR : zpEval2Seg p F (zpEval3 p P x ex y ey z ez hx hy hz)
      (zpEval3 p Q x ex y ey z ez hx hy hz) n
      = rsum (zpRing p) (fun b₁ => rsum (zpRing p) (fun a₁ =>
          (zpRing p).mul (F b₁ a₁)
            (zpEval3 p (psMul (psRing (psRing (zpRing p)))
              (psPow (psRing (psRing (zpRing p))) P a₁)
              (psPow (psRing (psRing (zpRing p))) Q b₁))
              x ex y ey z ez hx hy hz)) n) n := by
    show rsum (zpRing p) (fun b₁ => rsum (zpRing p) (fun a₁ =>
        (zpRing p).mul (F b₁ a₁)
          ((zpRing p).mul
            (rpow (zpRing p)
              (zpEval3 p P x ex y ey z ez hx hy hz) a₁)
            (rpow (zpRing p)
              (zpEval3 p Q x ex y ey z ez hx hy hz) b₁))) n) n = _
    refine rsum_congr (zpRing p) n (fun b₁ _ => ?_)
    refine rsum_congr (zpRing p) n (fun a₁ _ => ?_)
    rw [← zpEval3_pow p P x ex y ey z ez hx hy hz a₁,
      ← zpEval3_pow p Q x ex y ey z ez hx hy hz b₁,
      ← zpEval3_mul p (psPow (psRing (psRing (zpRing p))) P a₁)
        (psPow (psRing (psRing (zpRing p))) Q b₁)
        x ex y ey z ez hx hy hz]
  show (zpEval3Seg p (ps23Comp (zpRing p) F P Q) x y z n).val n
    = (zpEval2Seg p F (zpEval3 p P x ex y ey z ez hx hy hz)
        (zpEval3 p Q x ex y ey z ez hx hy hz) n).val n
  rw [zpEval3Seg_ps23Comp p F P Q hP hQ x y z n, hR]
  show (projRing p n).map (rsum (zpRing p) (fun b₁ =>
      rsum (zpRing p) (fun a₁ => (zpRing p).mul (F b₁ a₁)
        (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
          (psPow (psRing (psRing (zpRing p))) P a₁)
          (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n))
        (3 * n)) (3 * n))
    = (projRing p n).map (rsum (zpRing p) (fun b₁ =>
        rsum (zpRing p) (fun a₁ => (zpRing p).mul (F b₁ a₁)
          (zpEval3 p (psMul (psRing (psRing (zpRing p)))
            (psPow (psRing (psRing (zpRing p))) P a₁)
            (psPow (psRing (psRing (zpRing p))) Q b₁))
            x ex y ey z ez hx hy hz)) n) n)
  rw [ringHom_rsum (projRing p n) _ (3 * n),
    ringHom_rsum (projRing p n) _ n]
  -- 外側 b₁ を 3n → n に pad
  have hpadb : rsum (zmodRing (p ^ n)) (fun b₁ =>
      (projRing p n).map (rsum (zpRing p) (fun a₁ =>
        (zpRing p).mul (F b₁ a₁)
          (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
            (psPow (psRing (psRing (zpRing p))) P a₁)
            (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n))
        (3 * n))) (3 * n)
      = rsum (zmodRing (p ^ n)) (fun b₁ =>
          (projRing p n).map (rsum (zpRing p) (fun a₁ =>
            (zpRing p).mul (F b₁ a₁)
              (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
                (psPow (psRing (psRing (zpRing p))) P a₁)
                (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n))
            (3 * n))) n :=
    rsum_pad (zmodRing (p ^ n)) _ (by omega) (fun b₁ hb₁ => by
      show (projRing p n).map (rsum (zpRing p) (fun a₁ =>
          (zpRing p).mul (F b₁ a₁)
            (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
              (psPow (psRing (psRing (zpRing p))) P a₁)
              (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n))
          (3 * n)) = (zmodRing (p ^ n)).zero
      rw [ringHom_rsum (projRing p n) _ (3 * n)]
      have hz0 : rsum (zmodRing (p ^ n)) (fun a₁ =>
          (projRing p n).map ((zpRing p).mul (F b₁ a₁)
            (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
              (psPow (psRing (psRing (zpRing p))) P a₁)
              (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n)))
          (3 * n)
          = rsum (zmodRing (p ^ n)) (fun _ => (zmodRing (p ^ n)).zero)
              (3 * n) :=
        rsum_congr (zmodRing (p ^ n)) (3 * n) (fun a₁ _ => by
          rw [(projRing p n).map_mul,
            proj_Seg3_powpow_high p P Q hP hQ x ex y ey z ez hx hy hz
              (Nat.le_trans hb₁ (Nat.le_add_left b₁ a₁))]
          exact CRing.mul_zero (zmodRing (p ^ n)) _)
      rw [hz0]
      exact rsum_const_zero (zmodRing (p ^ n)) (3 * n))
  rw [hpadb]
  refine rsum_congr (zmodRing (p ^ n)) n (fun b₁ hb₁ => ?_)
  show (projRing p n).map (rsum (zpRing p) (fun a₁ =>
      (zpRing p).mul (F b₁ a₁)
        (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
          (psPow (psRing (psRing (zpRing p))) P a₁)
          (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n))
      (3 * n))
    = (projRing p n).map (rsum (zpRing p) (fun a₁ =>
        (zpRing p).mul (F b₁ a₁)
          (zpEval3 p (psMul (psRing (psRing (zpRing p)))
            (psPow (psRing (psRing (zpRing p))) P a₁)
            (psPow (psRing (psRing (zpRing p))) Q b₁))
            x ex y ey z ez hx hy hz)) n)
  rw [ringHom_rsum (projRing p n) _ (3 * n),
    ringHom_rsum (projRing p n) _ n]
  -- 内側 a₁ を 3n → n に pad
  have hpada : rsum (zmodRing (p ^ n)) (fun a₁ =>
      (projRing p n).map ((zpRing p).mul (F b₁ a₁)
        (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
          (psPow (psRing (psRing (zpRing p))) P a₁)
          (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n)))
      (3 * n)
      = rsum (zmodRing (p ^ n)) (fun a₁ =>
          (projRing p n).map ((zpRing p).mul (F b₁ a₁)
            (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
              (psPow (psRing (psRing (zpRing p))) P a₁)
              (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n)))
          n :=
    rsum_pad (zmodRing (p ^ n)) _ (by omega) (fun a₁ ha₁ => by
      show (projRing p n).map ((zpRing p).mul (F b₁ a₁)
          (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
            (psPow (psRing (psRing (zpRing p))) P a₁)
            (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n))
        = (zmodRing (p ^ n)).zero
      rw [(projRing p n).map_mul,
        proj_Seg3_powpow_high p P Q hP hQ x ex y ey z ez hx hy hz
          (Nat.le_trans ha₁ (Nat.le_add_right a₁ b₁))]
      exact CRing.mul_zero (zmodRing (p ^ n)) _)
  rw [hpada]
  refine rsum_congr (zmodRing (p ^ n)) n (fun a₁ _ => ?_)
  show (projRing p n).map ((zpRing p).mul (F b₁ a₁)
      (zpEval3Seg p (psMul (psRing (psRing (zpRing p)))
        (psPow (psRing (psRing (zpRing p))) P a₁)
        (psPow (psRing (psRing (zpRing p))) Q b₁)) x y z n))
    = (projRing p n).map ((zpRing p).mul (F b₁ a₁)
        (zpEval3 p (psMul (psRing (psRing (zpRing p)))
          (psPow (psRing (psRing (zpRing p))) P a₁)
          (psPow (psRing (psRing (zpRing p))) Q b₁))
          x ex y ey z ez hx hy hz))
  rw [(projRing p n).map_mul, (projRing p n).map_mul]
  rfl

/-! ## 結合則の点版（本丸） -/

/-- **定理 (M85-5): 結合則の点版** — F(F(x,y), z) = F(x, F(y,z))。
    M71 の級数恒等式 assocL = assocR を代入連鎖律と lift/座標の評価で
    点に輸送する。これで **F(pℤ_p) は単位・可換・逆元・結合・ℤ_p-作用
    を備えた可換群**。 -/
theorem lt_point_assoc (p : Nat) (hp : IsPrime p)
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez) :
    zpEval2 p (lt2Sol p hp)
      (zpEval2 p (lt2Sol p hp) x ex y ey hx hy)
      (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) x ex y ey hx hy))
      z ez
      (zpEval2_closed' p hp.1 (lt2Sol p hp)
        (lt2Sol_is_formal_group p hp).1 x ex y ey hx hy)
      hz
    = zpEval2 p (lt2Sol p hp) x ex
        (zpEval2 p (lt2Sol p hp) y ey z ez hy hz)
        (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) y ey z ez hy hz))
        hx
        (zpEval2_closed' p hp.1 (lt2Sol p hp)
          (lt2Sol_is_formal_group p hp).1 y ey z ez hy hz) := by
  have hF := lt2Sol_is_formal_group p hp
  have hP000L : liftXY (zpRing p) (lt2Sol p hp) 0 0 0
      = (zpRing p).zero := hF.1
  have hQ000R : liftYZ (zpRing p) (lt2Sol p hp) 0 0 0
      = (zpRing p).zero := hF.1
  -- 連鎖律の点の witness
  have huL : zpEval3 p (liftXY (zpRing p) (lt2Sol p hp))
      x ex y ey z ez hx hy hz
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) x ex y ey hx hy)) := by
    rw [zpEval3_liftXY p (lt2Sol p hp) x ex y ey z ez hx hy hz]
    exact zpEval2_closed' p hp.1 (lt2Sol p hp) hF.1 x ex y ey hx hy
  have hvL : zpEval3 p (ps3Z (zpRing p)) x ex y ey z ez hx hy hz
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez := by
    rw [zpEval3_ps3Z p hp.1 x ex y ey z ez hx hy hz]
    exact hz
  have huR : zpEval3 p (ps3X (zpRing p)) x ex y ey z ez hx hy hz
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex := by
    rw [zpEval3_ps3X p hp.1 x ex y ey z ez hx hy hz]
    exact hx
  have hvR : zpEval3 p (liftYZ (zpRing p) (lt2Sol p hp))
      x ex y ey z ez hx hy hz
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) y ey z ez hy hz)) := by
    rw [zpEval3_liftYZ p (lt2Sol p hp) x ex y ey z ez hx hy hz]
    exact zpEval2_closed' p hp.1 (lt2Sol p hp) hF.1 y ey z ez hy hz
  -- assocL の評価
  have hLeft : zpEval3 p (assocL p hp) x ex y ey z ez hx hy hz
      = zpEval2 p (lt2Sol p hp)
          (zpEval2 p (lt2Sol p hp) x ex y ey hx hy)
          (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) x ex y ey hx hy))
          z ez
          (zpEval2_closed' p hp.1 (lt2Sol p hp) hF.1 x ex y ey hx hy)
          hz := by
    show zpEval3 p (ps23Comp (zpRing p) (lt2Sol p hp)
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p)))
        x ex y ey z ez hx hy hz = _
    rw [zpEval3_ps23Comp p (lt2Sol p hp)
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p))
        hP000L rfl x ex y ey z ez hx hy hz _ _ huL hvL]
    exact zpEval2_congr_points p (lt2Sol p hp)
      (zpEval3 p (liftXY (zpRing p) (lt2Sol p hp))
        x ex y ey z ez hx hy hz)
      (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) x ex y ey hx hy))
      (zpEval3 p (ps3Z (zpRing p)) x ex y ey z ez hx hy hz) ez
      (zpEval2 p (lt2Sol p hp) x ex y ey hx hy)
      (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) x ex y ey hx hy))
      z ez
      huL hvL
      (zpEval2_closed' p hp.1 (lt2Sol p hp) hF.1 x ex y ey hx hy)
      hz
      (zpEval3_liftXY p (lt2Sol p hp) x ex y ey z ez hx hy hz)
      (zpEval3_ps3Z p hp.1 x ex y ey z ez hx hy hz)
  -- assocR の評価
  have hRight : zpEval3 p (assocR p hp) x ex y ey z ez hx hy hz
      = zpEval2 p (lt2Sol p hp) x ex
          (zpEval2 p (lt2Sol p hp) y ey z ez hy hz)
          (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) y ey z ez hy hz))
          hx
          (zpEval2_closed' p hp.1 (lt2Sol p hp) hF.1 y ey z ez hy hz)
        := by
    show zpEval3 p (ps23Comp (zpRing p) (lt2Sol p hp)
        (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp)))
        x ex y ey z ez hx hy hz = _
    rw [zpEval3_ps23Comp p (lt2Sol p hp) (ps3X (zpRing p))
        (liftYZ (zpRing p) (lt2Sol p hp))
        rfl hQ000R x ex y ey z ez hx hy hz _ _ huR hvR]
    exact zpEval2_congr_points p (lt2Sol p hp)
      (zpEval3 p (ps3X (zpRing p)) x ex y ey z ez hx hy hz) ex
      (zpEval3 p (liftYZ (zpRing p) (lt2Sol p hp))
        x ex y ey z ez hx hy hz)
      (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) y ey z ez hy hz))
      x ex
      (zpEval2 p (lt2Sol p hp) y ey z ez hy hz)
      (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) y ey z ez hy hz))
      huR hvR
      hx
      (zpEval2_closed' p hp.1 (lt2Sol p hp) hF.1 y ey z ez hy hz)
      (zpEval3_ps3X p hp.1 x ex y ey z ez hx hy hz)
      (zpEval3_liftYZ p (lt2Sol p hp) x ex y ey z ez hx hy hz)
  -- M71 の級数恒等式で接合
  have hmid : zpEval3 p (assocL p hp) x ex y ey z ez hx hy hz
      = zpEval3 p (assocR p hp) x ex y ey z ez hx hy hz :=
    congrArg (fun G => zpEval3 p G x ex y ey z ez hx hy hz)
      (lt_formal_group_assoc p hp)
  exact hLeft.symm.trans (hmid.trans hRight)

end IUT
