/-
  IUT/FormalGroupPoints3.lean — M82（3 変数評価:
  点の群キャンペーン第六層・結合則輸送の第一段）

  3 変数級数 G ∈ ℤ_p[[X,Y,Z]] の点 (x, y, z) ∈ (pℤ_p)³ での値
  G(x, y, z) ∈ ℤ_p を構成する。設計の鍵: **入れ子定義**
  G(x,y,z) の部分和 = Σ_{c<N} (行 G_c の 2 変数部分和)·z^c により、
  安定性は **M80 の 2 変数安定性 + M78F の「z^c はレベル i ≤ c で
  消える」をレベル射影の側で合成するだけ**（要素レベルの三段分割が
  不要になる）。

  * M82-1 `zpEval3Seg` / `zpEval3Seg_stable` — 入れ子部分和と安定性
    （射影レベルの pad + M80 安定性の行ごと適用）
  * M82-2 `zpEval3` / `zpEval3_witness_irrel` — 評価の本体
  * M82-3 `zpEval2Seg_one` — 2 変数 1 の部分和 = 1（二重一点集中）
  * M82-4 `zpEval3_liftXY` — **lift の評価 (liftXY F)(x,y,z) = F(x,y)**
    （c = 0 への一点集中）
  * M82-5 `zpEval3_ps3Z` — **座標の評価 Z(x,y,z) = z**

  liftYZ・ps3X の評価・3 変数の乗法性・代入連鎖律・結合則の点輸送
  F(F(x,y),z) = F(x,F(y,z)) は次層以降。全て選択公理不使用。
-/
import IUT.FormalGroupPointsLaw

namespace IUT

/-! ## 入れ子部分和と安定性 -/

/-- **M82-1a: 3 変数部分和**（入れ子: 行 G_c の 2 変数部分和に z^c）。 -/
def zpEval3Seg (p : Nat) (G : PS3 (zpRing p)) (x y z : (Zp p).carrier)
    (N : Nat) : (Zp p).carrier :=
  rsum (zpRing p) (fun c =>
    (zpRing p).mul (zpEval2Seg p (G c) x y N) (rpow (zpRing p) z c)) N

/-- **定理 (M82-1b): 安定性** — 射影レベルで c ≥ i の行は z^c が殺し
    （M78F の proj_rpow_x_low）、c < i の行は M80 の 2 変数安定性。 -/
theorem zpEval3Seg_stable (p : Nat) (G : PS3 (zpRing p))
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez)
    {i j : Nat} (h : i ≤ j) :
    (zpEval3Seg p G x y z j).val i = (zpEval3Seg p G x y z i).val i := by
  show (projRing p i).map (rsum (zpRing p) (fun c =>
      (zpRing p).mul (zpEval2Seg p (G c) x y j) (rpow (zpRing p) z c)) j)
    = (projRing p i).map (rsum (zpRing p) (fun c =>
        (zpRing p).mul (zpEval2Seg p (G c) x y i) (rpow (zpRing p) z c)) i)
  rw [ringHom_rsum (projRing p i) (fun c =>
      (zpRing p).mul (zpEval2Seg p (G c) x y j) (rpow (zpRing p) z c)) j,
    ringHom_rsum (projRing p i) (fun c =>
      (zpRing p).mul (zpEval2Seg p (G c) x y i) (rpow (zpRing p) z c)) i]
  have hpad : rsum (zmodRing (p ^ i)) (fun c =>
        (projRing p i).map ((zpRing p).mul (zpEval2Seg p (G c) x y j)
          (rpow (zpRing p) z c))) j
      = rsum (zmodRing (p ^ i)) (fun c =>
          (projRing p i).map ((zpRing p).mul (zpEval2Seg p (G c) x y j)
            (rpow (zpRing p) z c))) i :=
    rsum_pad (zmodRing (p ^ i)) (fun c =>
        (projRing p i).map ((zpRing p).mul (zpEval2Seg p (G c) x y j)
          (rpow (zpRing p) z c))) h
      (fun c hc => by
        show (projRing p i).map ((zpRing p).mul
            (zpEval2Seg p (G c) x y j) (rpow (zpRing p) z c))
          = (zmodRing (p ^ i)).zero
        rw [(projRing p i).map_mul, proj_rpow_x_low p z ez hz hc]
        exact CRing.mul_zero (zmodRing (p ^ i)) _)
  rw [hpad]
  refine rsum_congr (zmodRing (p ^ i)) i (fun c hc => ?_)
  show (projRing p i).map ((zpRing p).mul (zpEval2Seg p (G c) x y j)
      (rpow (zpRing p) z c))
    = (projRing p i).map ((zpRing p).mul (zpEval2Seg p (G c) x y i)
        (rpow (zpRing p) z c))
  rw [(projRing p i).map_mul, (projRing p i).map_mul,
    show (projRing p i).map (zpEval2Seg p (G c) x y j)
        = (projRing p i).map (zpEval2Seg p (G c) x y i) from
      zpEval2Seg_stable p (G c) x ex y ey hx hy h]

/-! ## 評価の本体 -/

/-- **M82-2a: 3 変数評価** G(x, y, z) ∈ ℤ_p。 -/
def zpEval3 (p : Nat) (G : PS3 (zpRing p))
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez) :
    (Zp p).carrier :=
  ⟨fun n => (zpEval3Seg p G x y z n).val n, by
    intro i j h
    have h1 : (zmodTrans (pow_dvd_mono p h)).map
        ((zpEval3Seg p G x y z j).val j)
        = (zpEval3Seg p G x y z j).val i :=
      (zpEval3Seg p G x y z j).property h
    show (zmodTrans (pow_dvd_mono p h)).map
        ((zpEval3Seg p G x y z j).val j)
      = (zpEval3Seg p G x y z i).val i
    rw [h1]
    exact zpEval3Seg_stable p G x ex y ey z ez hx hy hz h⟩

/-- **M82-2b: witness 非依存性**。 -/
theorem zpEval3_witness_irrel (p : Nat) (G : PS3 (zpRing p))
    (x ex ex' y ey ey' z ez ez' : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hx' : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex')
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hy' : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey')
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez)
    (hz' : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez') :
    zpEval3 p G x ex y ey z ez hx hy hz
      = zpEval3 p G x ex' y ey' z ez' hx' hy' hz' :=
  Subtype.ext rfl

/-! ## lift と座標の評価 -/

/-- **M82-3: 2 変数 1 の部分和 = 1**（(b,a) = (0,0) への二重一点集中、
    境界 ≥ 1）。 -/
theorem zpEval2Seg_one (p : Nat) (x y : (Zp p).carrier) (m : Nat) :
    zpEval2Seg p (psOne (psRing (zpRing p))) x y (m + 1)
      = (zpRing p).one := by
  show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
      (zpRing p).mul (psOne (psRing (zpRing p)) b a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      (m + 1)) (m + 1) = (zpRing p).one
  have houter : rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
      (zpRing p).mul (psOne (psRing (zpRing p)) b a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      (m + 1)) (m + 1)
      = rsum (zpRing p) (fun a =>
          (zpRing p).mul (psOne (psRing (zpRing p)) 0 a)
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y 0)))
          (m + 1) :=
    rsum_single (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (psOne (psRing (zpRing p)) b a)
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        (m + 1)) 0 (m + 1) (by omega)
      (fun b _ hb => by
        show rsum (zpRing p) (fun a =>
            (zpRing p).mul (psOne (psRing (zpRing p)) b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))) (m + 1) = (zpRing p).zero
        have hz2 : rsum (zpRing p) (fun a =>
            (zpRing p).mul (psOne (psRing (zpRing p)) b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))) (m + 1)
            = rsum (zpRing p) (fun _ => (zpRing p).zero) (m + 1) :=
          rsum_congr (zpRing p) (m + 1) (fun a _ => by
            rw [show psOne (psRing (zpRing p)) b
                = (psRing (zpRing p)).zero from if_neg hb]
            exact (zpRing p).zero_mul _)
        rw [hz2]
        exact rsum_const_zero (zpRing p) (m + 1))
  rw [houter]
  have hinner : rsum (zpRing p) (fun a =>
      (zpRing p).mul (psOne (psRing (zpRing p)) 0 a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y 0)))
      (m + 1)
      = (zpRing p).mul (psOne (psRing (zpRing p)) 0 0)
          ((zpRing p).mul (rpow (zpRing p) x 0) (rpow (zpRing p) y 0)) :=
    rsum_single (zpRing p) (fun a =>
        (zpRing p).mul (psOne (psRing (zpRing p)) 0 a)
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y 0)))
      0 (m + 1) (by omega)
      (fun a _ ha => by
        show (zpRing p).mul (psOne (psRing (zpRing p)) 0 a)
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y 0))
          = (zpRing p).zero
        rw [show psOne (psRing (zpRing p)) 0 a = (zpRing p).zero from
          if_neg ha]
        exact (zpRing p).zero_mul _)
  rw [hinner]
  show (zpRing p).mul ((zpRing p).one)
      ((zpRing p).mul ((zpRing p).one) ((zpRing p).one))
    = (zpRing p).one
  rw [(zpRing p).one_mul, (zpRing p).one_mul]

/-- **定理 (M82-4): lift の評価** — (liftXY F)(x, y, z) = F(x, y)
    （c = 0 への一点集中・z^0 = 1）。 -/
theorem zpEval3_liftXY (p : Nat) (F : PS2 (zpRing p))
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez) :
    zpEval3 p (liftXY (zpRing p) F) x ex y ey z ez hx hy hz
      = zpEval2 p F x ex y ey hx hy := by
  apply Subtype.ext
  funext n
  show (zpEval3Seg p (liftXY (zpRing p) F) x y z n).val n
    = (zpEval2Seg p F x y n).val n
  have hseg : zpEval3Seg p (liftXY (zpRing p) F) x y z n
      = zpEval2Seg p F x y n := by
    cases n with
    | zero => rfl
    | succ m =>
      have hs : rsum (zpRing p) (fun c =>
            (zpRing p).mul
              (zpEval2Seg p (liftXY (zpRing p) F c) x y (m + 1))
              (rpow (zpRing p) z c)) (m + 1)
          = (zpRing p).mul
              (zpEval2Seg p (liftXY (zpRing p) F 0) x y (m + 1))
              (rpow (zpRing p) z 0) :=
        rsum_single (zpRing p) (fun c =>
            (zpRing p).mul
              (zpEval2Seg p (liftXY (zpRing p) F c) x y (m + 1))
              (rpow (zpRing p) z c)) 0 (m + 1) (by omega)
          (fun c _ hc => by
            show (zpRing p).mul
                (zpEval2Seg p (liftXY (zpRing p) F c) x y (m + 1))
                (rpow (zpRing p) z c) = (zpRing p).zero
            have hrow : zpEval2Seg p (liftXY (zpRing p) F c) x y (m + 1)
                = (zpRing p).zero := by
              show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
                  (zpRing p).mul (liftXY (zpRing p) F c b a)
                    ((zpRing p).mul (rpow (zpRing p) x a)
                      (rpow (zpRing p) y b))) (m + 1)) (m + 1)
                = (zpRing p).zero
              have hz2 : rsum (zpRing p) (fun b =>
                    rsum (zpRing p) (fun a =>
                      (zpRing p).mul (liftXY (zpRing p) F c b a)
                        ((zpRing p).mul (rpow (zpRing p) x a)
                          (rpow (zpRing p) y b))) (m + 1)) (m + 1)
                  = rsum (zpRing p) (fun _ => (zpRing p).zero) (m + 1) :=
                rsum_congr (zpRing p) (m + 1) (fun b _ => by
                  have hz3 : rsum (zpRing p) (fun a =>
                        (zpRing p).mul (liftXY (zpRing p) F c b a)
                          ((zpRing p).mul (rpow (zpRing p) x a)
                            (rpow (zpRing p) y b))) (m + 1)
                      = rsum (zpRing p) (fun _ => (zpRing p).zero)
                          (m + 1) :=
                    rsum_congr (zpRing p) (m + 1) (fun a _ => by
                      rw [show liftXY (zpRing p) F c
                          = (psRing (psRing (zpRing p))).zero from
                        if_neg hc]
                      exact (zpRing p).zero_mul _)
                  show rsum (zpRing p) (fun a =>
                      (zpRing p).mul (liftXY (zpRing p) F c b a)
                        ((zpRing p).mul (rpow (zpRing p) x a)
                          (rpow (zpRing p) y b))) (m + 1)
                    = (zpRing p).zero
                  rw [hz3]
                  exact rsum_const_zero (zpRing p) (m + 1))
              rw [hz2]
              exact rsum_const_zero (zpRing p) (m + 1)
            rw [hrow]
            exact (zpRing p).zero_mul _)
      show rsum (zpRing p) (fun c =>
          (zpRing p).mul
            (zpEval2Seg p (liftXY (zpRing p) F c) x y (m + 1))
            (rpow (zpRing p) z c)) (m + 1)
        = zpEval2Seg p F x y (m + 1)
      rw [hs]
      show (zpRing p).mul (zpEval2Seg p F x y (m + 1)) ((zpRing p).one)
        = zpEval2Seg p F x y (m + 1)
      rw [(zpRing p).mul_comm, (zpRing p).one_mul]
  rw [hseg]

/-- **定理 (M82-5): 座標の評価** — Z(x, y, z) = z
    （c = 1 への一点集中・2 変数 1 の部分和 = 1）。 -/
theorem zpEval3_ps3Z (p : Nat) (hp : 2 ≤ p)
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez) :
    zpEval3 p (ps3Z (zpRing p)) x ex y ey z ez hx hy hz = z := by
  apply Subtype.ext
  funext n
  show (zpEval3Seg p (ps3Z (zpRing p)) x y z n).val n = z.val n
  -- 行 c の 2 変数部分和: c = 1 で 1、その他で 0
  have hrowz : ∀ c, c ≠ 1 → ∀ N,
      zpEval2Seg p (ps3Z (zpRing p) c) x y N = (zpRing p).zero := by
    intro c hc N
    show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (ps3Z (zpRing p) c b a)
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        N) N = (zpRing p).zero
    have hz2 : rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
          (zpRing p).mul (ps3Z (zpRing p) c b a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y b))) N) N
        = rsum (zpRing p) (fun _ => (zpRing p).zero) N :=
      rsum_congr (zpRing p) N (fun b _ => by
        have hz3 : rsum (zpRing p) (fun a =>
              (zpRing p).mul (ps3Z (zpRing p) c b a)
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y b))) N
            = rsum (zpRing p) (fun _ => (zpRing p).zero) N :=
          rsum_congr (zpRing p) N (fun a _ => by
            rw [show ps3Z (zpRing p) c
                = (psRing (psRing (zpRing p))).zero from if_neg hc]
            exact (zpRing p).zero_mul _)
        show rsum (zpRing p) (fun a =>
            (zpRing p).mul (ps3Z (zpRing p) c b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))) N = (zpRing p).zero
        rw [hz3]
        exact rsum_const_zero (zpRing p) N)
    rw [hz2]
    exact rsum_const_zero (zpRing p) N
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ m =>
    cases m with
    | zero =>
      -- レベル 1: 部分和 = 行 0 のみ = 0、z.val 1 = 0
      have h1 : zpEval3Seg p (ps3Z (zpRing p)) x y z 1
          = (zpRing p).zero := by
        show (zpRing p).add (zpRing p).zero
            ((zpRing p).mul (zpEval2Seg p (ps3Z (zpRing p) 0) x y 1)
              (rpow (zpRing p) z 0)) = (zpRing p).zero
        rw [hrowz 0 (by omega) 1, (zpRing p).zero_mul,
          (zpRing p).zero_add]
      have hz1 : z.val 1 = Quot.mk (modCong (p ^ 1)).rel 0 :=
        (zp_dvd_p_iff p hp z).mp ⟨ez, hz⟩
      rw [h1, hz1]
      rfl
    | succ m' =>
      have hs : rsum (zpRing p) (fun c =>
            (zpRing p).mul
              (zpEval2Seg p (ps3Z (zpRing p) c) x y (m' + 2))
              (rpow (zpRing p) z c)) (m' + 2)
          = (zpRing p).mul
              (zpEval2Seg p (ps3Z (zpRing p) 1) x y (m' + 2))
              (rpow (zpRing p) z 1) :=
        rsum_single (zpRing p) (fun c =>
            (zpRing p).mul
              (zpEval2Seg p (ps3Z (zpRing p) c) x y (m' + 2))
              (rpow (zpRing p) z c)) 1 (m' + 2) (by omega)
          (fun c _ hc => by
            show (zpRing p).mul
                (zpEval2Seg p (ps3Z (zpRing p) c) x y (m' + 2))
                (rpow (zpRing p) z c) = (zpRing p).zero
            rw [hrowz c hc (m' + 2)]
            exact (zpRing p).zero_mul _)
      have hseg : zpEval3Seg p (ps3Z (zpRing p)) x y z (m' + 2) = z := by
        show rsum (zpRing p) (fun c =>
            (zpRing p).mul
              (zpEval2Seg p (ps3Z (zpRing p) c) x y (m' + 2))
              (rpow (zpRing p) z c)) (m' + 2) = z
        rw [hs,
          show zpEval2Seg p (ps3Z (zpRing p) 1) x y (m' + 2)
              = (zpRing p).one from zpEval2Seg_one p x y (m' + 1),
          (zpRing p).one_mul]
        show (zpRing p).mul ((zpRing p).one) z = z
        rw [(zpRing p).one_mul]
      rw [hseg]

end IUT
