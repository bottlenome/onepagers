/-
  IUT/FormalGroupPointsMul2.lean — M83（2 変数評価の乗法性:
  点の群キャンペーン第七層・結合則輸送の第二段）

  2 変数評価の乗法性

    **(F·G)(x, y) = F(x, y)·G(x, y)**

  を完全証明する。設計の鍵: レベル m+1 の検証を**射影先 ℤ/p^{m+1} の
  世界で行う**と、はみ出し項（指数和 > m）は射影が本当に 0 にする
  （x̄^k = 0、k ≥ m+1 — M78F）ので、**M69b の抽象四重和再添字化
  quad_sum_reindex の消滅仮説が文字どおり成立**し、係数環レベルの
  装置がそのまま再登板する（M78 の 1 変数三角形論法の 2 変数版を
  ゼロから書かずに済む）。

  * M83-1 `proj_rpow_point_low` / `rpow_pair_mul` — 簿記
    （射影点の冪のレベル消滅・冪対の融合）
  * M83-2 `zpEval2_mul` — **乗法性（本丸）**: Cauchy 側 =
    ps2Mul_coeff の射影展開 + 添字付け替え、積側 = 矩形四重和、
    接合 = quad_sum_reindex in ℤ/p^{m+1}
  * M83-3 `zpEval2_one` / `zpEval2_pow` — 1 の評価と冪の評価

  liftYZ・ps3X の評価・3 変数の乗法性と代入連鎖律・結合則の点輸送は
  次層。全て選択公理不使用。
-/
import IUT.FormalGroupPoints3

namespace IUT

/-! ## 簿記 -/

/-- **M83-1a: 射影点の冪のレベル消滅** — x̄^k = 0 in ℤ/p^n（n ≤ k）。 -/
theorem proj_rpow_point_low (p : Nat) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    {n k : Nat} (h : n ≤ k) :
    rpow (zmodRing (p ^ n)) ((projRing p n).map x) k
      = (zmodRing (p ^ n)).zero := by
  rw [← ringHom_rpow (projRing p n) x k]
  exact proj_rpow_x_low p x e hx h

/-- **M83-1b: 冪対の融合** — (u^{a₁}v^{b₁})·(u^{a₂}v^{b₂})
    = u^{a₁+a₂}·v^{b₁+b₂}（任意の可換環）。 -/
theorem rpow_pair_mul (S : CRing) (u v : S.carrier)
    (a₁ b₁ a₂ b₂ : Nat) :
    S.mul (S.mul (rpow S u a₁) (rpow S v b₁))
      (S.mul (rpow S u a₂) (rpow S v b₂))
    = S.mul (rpow S u (a₁ + a₂)) (rpow S v (b₁ + b₂)) := by
  rw [rpow_add S u a₁ a₂, rpow_add S v b₁ b₂]
  exact CRing.mul_mul_comm S (rpow S u a₁) (rpow S v b₁)
    (rpow S u a₂) (rpow S v b₂)

/-! ## 乗法性 -/

/-- **定理 (M83-2): 2 変数評価の乗法性（本丸）** —
    (F·G)(x, y) = F(x, y)·G(x, y)。レベル m+1 を ℤ/p^{m+1} で検証し、
    M69b の quad_sum_reindex を射影先で再登板させる。 -/
theorem zpEval2_mul (p : Nat) (F G : PS2 (zpRing p))
    (x ex y ey : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey) :
    zpEval2 p (psMul (psRing (zpRing p)) F G) x ex y ey hx hy
      = (zpRing p).mul (zpEval2 p F x ex y ey hx hy)
          (zpEval2 p G x ex y ey hx hy) := by
  apply Subtype.ext
  funext n
  show (zpEval2Seg p (psMul (psRing (zpRing p)) F G) x y n).val n
    = ((zpRing p).mul (zpEval2Seg p F x y n) (zpEval2Seg p G x y n)).val n
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ m =>
    -- 以下 S := ℤ/p^{m+1}・φ := レベル m+1 射影
    -- Cauchy 側: 射影して四重和（三角形形）へ
    have hL : (projRing p (m + 1)).map
        (zpEval2Seg p (psMul (psRing (zpRing p)) F G) x y (m + 1))
        = rsum (zmodRing (p ^ (m + 1))) (fun b =>
            rsum (zmodRing (p ^ (m + 1))) (fun a =>
              rsum (zmodRing (p ^ (m + 1))) (fun b₁ =>
                rsum (zmodRing (p ^ (m + 1))) (fun a₁ =>
                  (zmodRing (p ^ (m + 1))).mul
                    ((zmodRing (p ^ (m + 1))).mul
                      ((projRing p (m + 1)).map (F b₁ a₁))
                      ((projRing p (m + 1)).map (G (b - b₁) (a - a₁))))
                    ((zmodRing (p ^ (m + 1))).mul
                      (rpow (zmodRing (p ^ (m + 1)))
                        ((projRing p (m + 1)).map x) (a₁ + (a - a₁)))
                      (rpow (zmodRing (p ^ (m + 1)))
                        ((projRing p (m + 1)).map y) (b₁ + (b - b₁)))))
                  (a + 1)) (b + 1)) (m + 1)) (m + 1) := by
      show (projRing p (m + 1)).map (rsum (zpRing p) (fun b =>
          rsum (zpRing p) (fun a =>
            (zpRing p).mul (psMul (psRing (zpRing p)) F G b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))) (m + 1)) (m + 1)) = _
      rw [ringHom_rsum (projRing p (m + 1)) _ (m + 1)]
      refine rsum_congr (zmodRing (p ^ (m + 1))) (m + 1) (fun b _ => ?_)
      show (projRing p (m + 1)).map (rsum (zpRing p) (fun a =>
          (zpRing p).mul (psMul (psRing (zpRing p)) F G b a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y b))) (m + 1)) = _
      rw [ringHom_rsum (projRing p (m + 1)) _ (m + 1)]
      refine rsum_congr (zmodRing (p ^ (m + 1))) (m + 1) (fun a _ => ?_)
      show (projRing p (m + 1)).map ((zpRing p).mul
          (psMul (psRing (zpRing p)) F G b a)
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        = _
      rw [(projRing p (m + 1)).map_mul, ps2Mul_coeff (zpRing p) F G b a,
        ringHom_rsum (projRing p (m + 1)) _ (b + 1),
        rsum_mul_right (zmodRing (p ^ (m + 1))) _
          ((projRing p (m + 1)).map
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
          (b + 1)]
      refine rsum_congr (zmodRing (p ^ (m + 1))) (b + 1) (fun b₁ _ => ?_)
      show (zmodRing (p ^ (m + 1))).mul
          ((projRing p (m + 1)).map (rsum (zpRing p) (fun a₁ =>
            (zpRing p).mul (F b₁ a₁) (G (b - b₁) (a - a₁))) (a + 1)))
          ((projRing p (m + 1)).map
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        = _
      rw [ringHom_rsum (projRing p (m + 1)) _ (a + 1),
        rsum_mul_right (zmodRing (p ^ (m + 1))) _
          ((projRing p (m + 1)).map
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
          (a + 1)]
      refine rsum_congr (zmodRing (p ^ (m + 1))) (a + 1) (fun a₁ ha₁ => ?_)
      show (zmodRing (p ^ (m + 1))).mul
          ((projRing p (m + 1)).map
            ((zpRing p).mul (F b₁ a₁) (G (b - b₁) (a - a₁))))
          ((projRing p (m + 1)).map
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        = _
      rw [(projRing p (m + 1)).map_mul, (projRing p (m + 1)).map_mul,
        ringHom_rpow (projRing p (m + 1)) x a,
        ringHom_rpow (projRing p (m + 1)) y b,
        show a₁ + (a - a₁) = a by omega,
        show b₁ + (b - b₁) = b by omega]
    -- 積側: 射影して矩形四重和へ
    have hR : (projRing p (m + 1)).map
        ((zpRing p).mul (zpEval2Seg p F x y (m + 1))
          (zpEval2Seg p G x y (m + 1)))
        = rsum (zmodRing (p ^ (m + 1))) (fun b₁ =>
            rsum (zmodRing (p ^ (m + 1))) (fun a₁ =>
              rsum (zmodRing (p ^ (m + 1))) (fun b₂ =>
                rsum (zmodRing (p ^ (m + 1))) (fun a₂ =>
                  (zmodRing (p ^ (m + 1))).mul
                    ((zmodRing (p ^ (m + 1))).mul
                      ((projRing p (m + 1)).map (F b₁ a₁))
                      ((projRing p (m + 1)).map (G b₂ a₂)))
                    ((zmodRing (p ^ (m + 1))).mul
                      (rpow (zmodRing (p ^ (m + 1)))
                        ((projRing p (m + 1)).map x) (a₁ + a₂))
                      (rpow (zmodRing (p ^ (m + 1)))
                        ((projRing p (m + 1)).map y) (b₁ + b₂))))
                  (m + 1)) (m + 1)) (m + 1)) (m + 1) := by
      rw [(projRing p (m + 1)).map_mul]
      show (zmodRing (p ^ (m + 1))).mul
          ((projRing p (m + 1)).map (rsum (zpRing p) (fun b₁ =>
            rsum (zpRing p) (fun a₁ =>
              (zpRing p).mul (F b₁ a₁)
                ((zpRing p).mul (rpow (zpRing p) x a₁)
                  (rpow (zpRing p) y b₁))) (m + 1)) (m + 1)))
          ((projRing p (m + 1)).map (rsum (zpRing p) (fun b₂ =>
            rsum (zpRing p) (fun a₂ =>
              (zpRing p).mul (G b₂ a₂)
                ((zpRing p).mul (rpow (zpRing p) x a₂)
                  (rpow (zpRing p) y b₂))) (m + 1)) (m + 1))) = _
      rw [ringHom_rsum (projRing p (m + 1)) _ (m + 1),
        ringHom_rsum (projRing p (m + 1)) _ (m + 1),
        rsum_mul_right (zmodRing (p ^ (m + 1))) _ _ (m + 1)]
      refine rsum_congr (zmodRing (p ^ (m + 1))) (m + 1) (fun b₁ _ => ?_)
      show (zmodRing (p ^ (m + 1))).mul
          ((projRing p (m + 1)).map (rsum (zpRing p) (fun a₁ =>
            (zpRing p).mul (F b₁ a₁)
              ((zpRing p).mul (rpow (zpRing p) x a₁)
                (rpow (zpRing p) y b₁))) (m + 1)))
          (rsum (zmodRing (p ^ (m + 1))) (fun b₂ =>
            (projRing p (m + 1)).map (rsum (zpRing p) (fun a₂ =>
              (zpRing p).mul (G b₂ a₂)
                ((zpRing p).mul (rpow (zpRing p) x a₂)
                  (rpow (zpRing p) y b₂))) (m + 1))) (m + 1)) = _
      rw [ringHom_rsum (projRing p (m + 1)) _ (m + 1),
        rsum_mul_right (zmodRing (p ^ (m + 1))) _ _ (m + 1)]
      refine rsum_congr (zmodRing (p ^ (m + 1))) (m + 1) (fun a₁ _ => ?_)
      show (zmodRing (p ^ (m + 1))).mul
          ((projRing p (m + 1)).map ((zpRing p).mul (F b₁ a₁)
            ((zpRing p).mul (rpow (zpRing p) x a₁)
              (rpow (zpRing p) y b₁))))
          (rsum (zmodRing (p ^ (m + 1))) (fun b₂ =>
            (projRing p (m + 1)).map (rsum (zpRing p) (fun a₂ =>
              (zpRing p).mul (G b₂ a₂)
                ((zpRing p).mul (rpow (zpRing p) x a₂)
                  (rpow (zpRing p) y b₂))) (m + 1))) (m + 1)) = _
      rw [rsum_mul_left (zmodRing (p ^ (m + 1))) _ _ (m + 1)]
      refine rsum_congr (zmodRing (p ^ (m + 1))) (m + 1) (fun b₂ _ => ?_)
      show (zmodRing (p ^ (m + 1))).mul
          ((projRing p (m + 1)).map ((zpRing p).mul (F b₁ a₁)
            ((zpRing p).mul (rpow (zpRing p) x a₁)
              (rpow (zpRing p) y b₁))))
          ((projRing p (m + 1)).map (rsum (zpRing p) (fun a₂ =>
            (zpRing p).mul (G b₂ a₂)
              ((zpRing p).mul (rpow (zpRing p) x a₂)
                (rpow (zpRing p) y b₂))) (m + 1))) = _
      rw [ringHom_rsum (projRing p (m + 1)) _ (m + 1),
        rsum_mul_left (zmodRing (p ^ (m + 1))) _ _ (m + 1)]
      refine rsum_congr (zmodRing (p ^ (m + 1))) (m + 1) (fun a₂ _ => ?_)
      show (zmodRing (p ^ (m + 1))).mul
          ((projRing p (m + 1)).map ((zpRing p).mul (F b₁ a₁)
            ((zpRing p).mul (rpow (zpRing p) x a₁)
              (rpow (zpRing p) y b₁))))
          ((projRing p (m + 1)).map ((zpRing p).mul (G b₂ a₂)
            ((zpRing p).mul (rpow (zpRing p) x a₂)
              (rpow (zpRing p) y b₂)))) = _
      rw [(projRing p (m + 1)).map_mul, (projRing p (m + 1)).map_mul,
        (projRing p (m + 1)).map_mul, (projRing p (m + 1)).map_mul,
        ringHom_rpow (projRing p (m + 1)) x a₁,
        ringHom_rpow (projRing p (m + 1)) y b₁,
        ringHom_rpow (projRing p (m + 1)) x a₂,
        ringHom_rpow (projRing p (m + 1)) y b₂,
        CRing.mul_mul_comm (zmodRing (p ^ (m + 1)))
          ((projRing p (m + 1)).map (F b₁ a₁))
          ((zmodRing (p ^ (m + 1))).mul
            (rpow (zmodRing (p ^ (m + 1)))
              ((projRing p (m + 1)).map x) a₁)
            (rpow (zmodRing (p ^ (m + 1)))
              ((projRing p (m + 1)).map y) b₁))
          ((projRing p (m + 1)).map (G b₂ a₂))
          ((zmodRing (p ^ (m + 1))).mul
            (rpow (zmodRing (p ^ (m + 1)))
              ((projRing p (m + 1)).map x) a₂)
            (rpow (zmodRing (p ^ (m + 1)))
              ((projRing p (m + 1)).map y) b₂)),
        rpow_pair_mul (zmodRing (p ^ (m + 1)))
          ((projRing p (m + 1)).map x) ((projRing p (m + 1)).map y)
          a₁ b₁ a₂ b₂]
    -- 接合: quad_sum_reindex in ℤ/p^{m+1}（消滅仮説は射影が本当に満たす）
    have hquad := quad_sum_reindex (zmodRing (p ^ (m + 1)))
      (fun b₁ a₁ b₂ a₂ =>
        (zmodRing (p ^ (m + 1))).mul
          ((zmodRing (p ^ (m + 1))).mul
            ((projRing p (m + 1)).map (F b₁ a₁))
            ((projRing p (m + 1)).map (G b₂ a₂)))
          ((zmodRing (p ^ (m + 1))).mul
            (rpow (zmodRing (p ^ (m + 1)))
              ((projRing p (m + 1)).map x) (a₁ + a₂))
            (rpow (zmodRing (p ^ (m + 1)))
              ((projRing p (m + 1)).map y) (b₁ + b₂)))) m
      (fun b₁ a₁ b₂ a₂ h => by
        show (zmodRing (p ^ (m + 1))).mul _
            ((zmodRing (p ^ (m + 1))).mul _
              (rpow (zmodRing (p ^ (m + 1)))
                ((projRing p (m + 1)).map y) (b₁ + b₂)))
          = (zmodRing (p ^ (m + 1))).zero
        rw [proj_rpow_point_low p y ey hy (show m + 1 ≤ b₁ + b₂ by omega),
          CRing.mul_zero (zmodRing (p ^ (m + 1)))]
        exact CRing.mul_zero (zmodRing (p ^ (m + 1))) _)
      (fun b₁ a₁ b₂ a₂ h => by
        show (zmodRing (p ^ (m + 1))).mul _
            ((zmodRing (p ^ (m + 1))).mul
              (rpow (zmodRing (p ^ (m + 1)))
                ((projRing p (m + 1)).map x) (a₁ + a₂)) _)
          = (zmodRing (p ^ (m + 1))).zero
        rw [proj_rpow_point_low p x ex hx (show m + 1 ≤ a₁ + a₂ by omega),
          CRing.zero_mul (zmodRing (p ^ (m + 1)))]
        exact CRing.mul_zero (zmodRing (p ^ (m + 1))) _)
    show (projRing p (m + 1)).map
        (zpEval2Seg p (psMul (psRing (zpRing p)) F G) x y (m + 1))
      = (projRing p (m + 1)).map
          ((zpRing p).mul (zpEval2Seg p F x y (m + 1))
            (zpEval2Seg p G x y (m + 1)))
    rw [hL, hR, hquad]

/-! ## 1 と冪の評価 -/

/-- **M83-3a: 1 の評価** — 1(x, y) = 1。 -/
theorem zpEval2_one (p : Nat) (x ex y ey : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey) :
    zpEval2 p (psOne (psRing (zpRing p))) x ex y ey hx hy
      = (zpRing p).one := by
  apply Subtype.ext
  funext n
  show (zpEval2Seg p (psOne (psRing (zpRing p))) x y n).val n
    = ((zpRing p).one).val n
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ m => rw [zpEval2Seg_one p x y m]

/-- **M83-3b: 冪の評価** — (F^k)(x, y) = F(x, y)^k。 -/
theorem zpEval2_pow (p : Nat) (F : PS2 (zpRing p))
    (x ex y ey : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey) :
    ∀ k, zpEval2 p (psPow (psRing (zpRing p)) F k) x ex y ey hx hy
      = rpow (zpRing p) (zpEval2 p F x ex y ey hx hy) k := by
  intro k
  induction k with
  | zero => exact zpEval2_one p x ex y ey hx hy
  | succ k ih =>
    show zpEval2 p (psMul (psRing (zpRing p))
        (psPow (psRing (zpRing p)) F k) F) x ex y ey hx hy
      = (zpRing p).mul
          (rpow (zpRing p) (zpEval2 p F x ex y ey hx hy) k)
          (zpEval2 p F x ex y ey hx hy)
    rw [zpEval2_mul p (psPow (psRing (zpRing p)) F k) F x ex y ey hx hy,
      ih]

end IUT
