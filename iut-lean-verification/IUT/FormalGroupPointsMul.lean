/-
  IUT/FormalGroupPointsMul.lean — M78（評価の乗法性:
  点の群キャンペーン第二層)

  M77 の点での評価 zpEval の**乗法性**

    **(F·G)(x) = F(x)·G(x)**   （x ∈ pℤ_p）

  を完全証明する。レベル m+1 で: Cauchy 積の部分和は三角和交換
  （M39 の rsum_triangle が再登板）で Σ_{j}Σ_{l<m+1−j} に、積の
  部分和は矩形 Σ_{j}Σ_{l<m+1} になり、**差 = はみ出し（j+l ≥ m+1）は
  各項が x^{m+1} 因子を持つ**のでレベル m+1 射影が殺す（M77 の
  安定性と同じ構図の二重和版）。

  * M78-1 `CRing.mul_left_comm` / `proj_rpow_x_zero` — 簿記と
    「x^n はレベル n で消える」（M77-2b の x 版）
  * M78-2 `zpEval_mul` — **乗法性（本丸）**: Cauchy 側 = 三角形・
    積側 = 矩形・差 = x^{m+1}·(何か)
  * M78-3 `zpEval_pow` — 冪の評価 (F^k)(x) = F(x)^k（帰納適用、
    基底は psOne = psC 1 の定義的一致で M77 の zpEval_const）

  合成との両立 (F∘G)(x) = F(G(x))・点の群の群法則・[πⁿ]-捻れは
  次層以降。全て選択公理不使用。
-/
import IUT.FormalGroupPoints

namespace IUT

/-! ## 簿記 -/

/-- a·(b·c) = b·(a·c)（左交換）。 -/
theorem CRing.mul_left_comm (R : CRing) (a b c : R.carrier) :
    R.mul a (R.mul b c) = R.mul b (R.mul a c) := by
  rw [← R.mul_assoc, R.mul_comm a b, R.mul_assoc]

/-- **M78-1: x^n はレベル n で消える**（x = p·e、M77-2b の x 版）。 -/
theorem proj_rpow_x_zero (p : Nat) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    (n : Nat) :
    (projRing p n).map (rpow (zpRing p) x n)
      = (zmodRing (p ^ n)).zero := by
  rw [hx, rpow_mul_dist (zpRing p) ((toZp p).map ((p : Nat) : Int)) e n,
    (projRing p n).map_mul, proj_rpow_p_zero p n]
  exact CRing.zero_mul (zmodRing (p ^ n)) _

/-! ## 乗法性 -/

/-- **定理 (M78-2): 評価の乗法性（本丸）** — (F·G)(x) = F(x)·G(x)。 -/
theorem zpEval_mul (p : Nat) (F G : PS (zpRing p)) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (psMul (zpRing p) F G) x e hx
      = (zpRing p).mul (zpEval p F x e hx) (zpEval p G x e hx) := by
  apply Subtype.ext
  funext n
  show (zpEvalSeg p (psMul (zpRing p) F G) x n).val n
    = ((zpRing p).mul (zpEvalSeg p F x n) (zpEvalSeg p G x n)).val n
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ m =>
    -- Cauchy 側: 部分和を二重和に展開
    have hA : zpEvalSeg p (psMul (zpRing p) F G) x (m + 1)
        = rsum (zpRing p) (fun k => rsum (zpRing p) (fun j =>
            (zpRing p).mul ((zpRing p).mul (F j) (G (k - j)))
              (rpow (zpRing p) x k)) (k + 1)) (m + 1) := by
      show rsum (zpRing p) (fun k =>
          (zpRing p).mul (psMul (zpRing p) F G k) (rpow (zpRing p) x k))
          (m + 1) = _
      refine rsum_congr (zpRing p) (m + 1) (fun k _ => ?_)
      show (zpRing p).mul
          (rsum (zpRing p) (fun j =>
            (zpRing p).mul (F j) (G (k - j))) (k + 1))
          (rpow (zpRing p) x k) = _
      rw [rsum_mul_right (zpRing p) (fun j =>
          (zpRing p).mul (F j) (G (k - j))) (rpow (zpRing p) x k) (k + 1)]
    -- 三角和交換で (j, l) 添字へ
    have hB : rsum (zpRing p) (fun k => rsum (zpRing p) (fun j =>
          (zpRing p).mul ((zpRing p).mul (F j) (G (k - j)))
            (rpow (zpRing p) x k)) (k + 1)) (m + 1)
        = rsum (zpRing p) (fun j => rsum (zpRing p) (fun l =>
            (zpRing p).mul ((zpRing p).mul (F j) (G l))
              (rpow (zpRing p) x (j + l))) (m + 1 - j)) (m + 1) :=
      (rsum_congr (zpRing p) (m + 1) (fun k _ =>
        rsum_congr (zpRing p) (k + 1) (fun j hj => by
          rw [show j + (k - j) = k by omega]))).symm.trans
        (rsum_triangle (zpRing p) (fun j l =>
          (zpRing p).mul ((zpRing p).mul (F j) (G l))
            (rpow (zpRing p) x (j + l))) m)
    -- 積側: 矩形二重和に展開
    have hC : (zpRing p).mul (zpEvalSeg p F x (m + 1))
        (zpEvalSeg p G x (m + 1))
        = rsum (zpRing p) (fun j => rsum (zpRing p) (fun l =>
            (zpRing p).mul ((zpRing p).mul (F j) (G l))
              (rpow (zpRing p) x (j + l))) (m + 1)) (m + 1) := by
      show (zpRing p).mul
          (rsum (zpRing p) (fun j =>
            (zpRing p).mul (F j) (rpow (zpRing p) x j)) (m + 1))
          (rsum (zpRing p) (fun l =>
            (zpRing p).mul (G l) (rpow (zpRing p) x l)) (m + 1)) = _
      rw [rsum_mul_right (zpRing p) (fun j =>
          (zpRing p).mul (F j) (rpow (zpRing p) x j))
          (rsum (zpRing p) (fun l =>
            (zpRing p).mul (G l) (rpow (zpRing p) x l)) (m + 1)) (m + 1)]
      refine rsum_congr (zpRing p) (m + 1) (fun j _ => ?_)
      show (zpRing p).mul ((zpRing p).mul (F j) (rpow (zpRing p) x j))
          (rsum (zpRing p) (fun l =>
            (zpRing p).mul (G l) (rpow (zpRing p) x l)) (m + 1)) = _
      rw [rsum_mul_left (zpRing p) (fun l =>
          (zpRing p).mul (G l) (rpow (zpRing p) x l))
          ((zpRing p).mul (F j) (rpow (zpRing p) x j)) (m + 1)]
      refine rsum_congr (zpRing p) (m + 1) (fun l _ => ?_)
      show (zpRing p).mul ((zpRing p).mul (F j) (rpow (zpRing p) x j))
          ((zpRing p).mul (G l) (rpow (zpRing p) x l))
        = (zpRing p).mul ((zpRing p).mul (F j) (G l))
            (rpow (zpRing p) x (j + l))
      rw [rpow_add (zpRing p) x j l]
      exact CRing.mul_mul_comm (zpRing p) (F j) (rpow (zpRing p) x j)
        (G l) (rpow (zpRing p) x l)
    -- 矩形 = 三角形 + x^{m+1}·(はみ出し)
    have hj : ∀ j, j < m + 1 →
        rsum (zpRing p) (fun l =>
          (zpRing p).mul ((zpRing p).mul (F j) (G l))
            (rpow (zpRing p) x (j + l))) (m + 1)
        = (zpRing p).add
            (rsum (zpRing p) (fun l =>
              (zpRing p).mul ((zpRing p).mul (F j) (G l))
                (rpow (zpRing p) x (j + l))) (m + 1 - j))
            ((zpRing p).mul (rpow (zpRing p) x (m + 1))
              (rsum (zpRing p) (fun k =>
                (zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
                  (rpow (zpRing p) x k)) j)) := by
      intro j hjlt
      have hsplit := rsum_split (zpRing p) (fun l =>
        (zpRing p).mul ((zpRing p).mul (F j) (G l))
          (rpow (zpRing p) x (j + l))) (m + 1 - j) j
      rw [show m + 1 - j + j = m + 1 by omega] at hsplit
      rw [hsplit]
      have htailterm : ∀ k, k < j →
          (zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
            (rpow (zpRing p) x (j + (m + 1 - j + k)))
          = (zpRing p).mul (rpow (zpRing p) x (m + 1))
              ((zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
                (rpow (zpRing p) x k)) := by
        intro k _
        rw [show j + (m + 1 - j + k) = (m + 1) + k by omega,
          rpow_add (zpRing p) x (m + 1) k]
        exact CRing.mul_left_comm (zpRing p)
          ((zpRing p).mul (F j) (G (m + 1 - j + k)))
          (rpow (zpRing p) x (m + 1)) (rpow (zpRing p) x k)
      have htail : rsum (zpRing p) (fun k =>
            (zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
              (rpow (zpRing p) x (j + (m + 1 - j + k)))) j
          = (zpRing p).mul (rpow (zpRing p) x (m + 1))
              (rsum (zpRing p) (fun k =>
                (zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
                  (rpow (zpRing p) x k)) j) :=
        (rsum_congr (zpRing p) j htailterm).trans
          ((rsum_mul_left (zpRing p) (fun k =>
              (zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
                (rpow (zpRing p) x k))
            (rpow (zpRing p) x (m + 1)) j).symm)
      rw [htail]
    have hcongr : rsum (zpRing p) (fun j => rsum (zpRing p) (fun l =>
          (zpRing p).mul ((zpRing p).mul (F j) (G l))
            (rpow (zpRing p) x (j + l))) (m + 1)) (m + 1)
        = rsum (zpRing p) (fun j => (zpRing p).add
            (rsum (zpRing p) (fun l =>
              (zpRing p).mul ((zpRing p).mul (F j) (G l))
                (rpow (zpRing p) x (j + l))) (m + 1 - j))
            ((zpRing p).mul (rpow (zpRing p) x (m + 1))
              (rsum (zpRing p) (fun k =>
                (zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
                  (rpow (zpRing p) x k)) j))) (m + 1) :=
      rsum_congr (zpRing p) (m + 1) hj
    have hE : rsum (zpRing p) (fun j => rsum (zpRing p) (fun l =>
          (zpRing p).mul ((zpRing p).mul (F j) (G l))
            (rpow (zpRing p) x (j + l))) (m + 1)) (m + 1)
        = (zpRing p).add
            (rsum (zpRing p) (fun j => rsum (zpRing p) (fun l =>
              (zpRing p).mul ((zpRing p).mul (F j) (G l))
                (rpow (zpRing p) x (j + l))) (m + 1 - j)) (m + 1))
            ((zpRing p).mul (rpow (zpRing p) x (m + 1))
              (rsum (zpRing p) (fun j =>
                rsum (zpRing p) (fun k =>
                  (zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
                    (rpow (zpRing p) x k)) j) (m + 1))) := by
      rw [hcongr,
        rsum_add (zpRing p) (fun j =>
          rsum (zpRing p) (fun l =>
            (zpRing p).mul ((zpRing p).mul (F j) (G l))
              (rpow (zpRing p) x (j + l))) (m + 1 - j))
          (fun j => (zpRing p).mul (rpow (zpRing p) x (m + 1))
            (rsum (zpRing p) (fun k =>
              (zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
                (rpow (zpRing p) x k)) j)) (m + 1),
        rsum_mul_left (zpRing p) (fun j =>
          rsum (zpRing p) (fun k =>
            (zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
              (rpow (zpRing p) x k)) j)
          (rpow (zpRing p) x (m + 1)) (m + 1)]
    -- 仕上げ: レベル m+1 射影で x^{m+1} 因子が消える
    rw [hA, hB, hC, hE]
    show (projRing p (m + 1)).map
        (rsum (zpRing p) (fun j => rsum (zpRing p) (fun l =>
          (zpRing p).mul ((zpRing p).mul (F j) (G l))
            (rpow (zpRing p) x (j + l))) (m + 1 - j)) (m + 1))
      = (projRing p (m + 1)).map
          ((zpRing p).add
            (rsum (zpRing p) (fun j => rsum (zpRing p) (fun l =>
              (zpRing p).mul ((zpRing p).mul (F j) (G l))
                (rpow (zpRing p) x (j + l))) (m + 1 - j)) (m + 1))
            ((zpRing p).mul (rpow (zpRing p) x (m + 1))
              (rsum (zpRing p) (fun j =>
                rsum (zpRing p) (fun k =>
                  (zpRing p).mul ((zpRing p).mul (F j) (G (m + 1 - j + k)))
                    (rpow (zpRing p) x k)) j) (m + 1))))
    rw [(projRing p (m + 1)).map_add, (projRing p (m + 1)).map_mul,
      proj_rpow_x_zero p x e hx (m + 1),
      CRing.zero_mul (zmodRing (p ^ (m + 1))),
      CRing.add_zero (zmodRing (p ^ (m + 1)))]

/-! ## 冪の評価 -/

/-- **M78-3: 冪の評価** — (F^k)(x) = F(x)^k（乗法性の帰納適用）。 -/
theorem zpEval_pow (p : Nat) (F : PS (zpRing p)) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    ∀ k, zpEval p (psPow (zpRing p) F k) x e hx
      = rpow (zpRing p) (zpEval p F x e hx) k := by
  intro k
  induction k with
  | zero => exact zpEval_const p ((zpRing p).one) x e hx
  | succ k ih =>
    show zpEval p (psMul (zpRing p) (psPow (zpRing p) F k) F) x e hx
      = (zpRing p).mul (rpow (zpRing p) (zpEval p F x e hx) k)
          (zpEval p F x e hx)
    rw [zpEval_mul p (psPow (zpRing p) F k) F x e hx, ih]

end IUT
