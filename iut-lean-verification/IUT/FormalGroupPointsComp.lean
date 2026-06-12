/-
  IUT/FormalGroupPointsComp.lean — M79（合成と評価の両立:
  点の群キャンペーン第三層）

  M77/M78 の点での評価 zpEval と級数の合成の両立

    **(F∘G)(x) = F(G(x))**   （x ∈ pℤ_p、G(0) = 0）

  を完全証明する。外側の点 y = G(x) ∈ pℤ_p の可除性 witness は
  引数で受ける（witness の実構成 = 閉性 G(x) ∈ pℤ_p は並行開発の
  psShift 因数分解と M78 の乗法性から次の統合で与える）。

  鍵となる**部分和の純環レベル恒等式**（射影不要）:
    Σ_{k<n} (F∘G)_k x^k = Σ_{j<n} F_j·(Σ_{k<n} (G^j)_k x^k)
  （pad: (G^j)_k = 0 for k < j・添字交換・F_j の括り出し）。
  右辺の内側和 = zpEvalSeg (G^j) は **zpEval (G^j) とレベル n で
  定義的に一致**し、zpEval_pow（M78）で G(x)^j に折りたためる。

  * M79-1 `zpEvalSeg_comp` — 部分和の合成恒等式（環レベル）
  * M79-2 `zpEval_comp` — **合成との両立（本丸）**

  点の群 F(pℤ_p) の群法則・[πⁿ]-捻れは次層以降。
  全て選択公理不使用。
-/
import IUT.FormalGroupPointsMul

namespace IUT

/-- **M79-1: 部分和の合成恒等式**（環レベル・射影不要） —
    Σ_{k<n} (F∘G)_k x^k = Σ_{j<n} F_j·zpEvalSeg (G^j) n
    （G(0) = 0 の truncation で j-和を n まで pad できる）。 -/
theorem zpEvalSeg_comp (p : Nat) (F G : PS (zpRing p))
    (hG : G 0 = (zpRing p).zero) (x : (Zp p).carrier) (n : Nat) :
    zpEvalSeg p (psComp (zpRing p) F G) x n
      = rsum (zpRing p) (fun j =>
          (zpRing p).mul (F j)
            (zpEvalSeg p (psPow (zpRing p) G j) x n)) n := by
  show rsum (zpRing p) (fun k =>
      (zpRing p).mul (psComp (zpRing p) F G k) (rpow (zpRing p) x k)) n
    = _
  -- 各 k で (F∘G)_k を展開し、j-境界を k+1 → n に pad、x^k を内側へ
  have hA : rsum (zpRing p) (fun k =>
        (zpRing p).mul (psComp (zpRing p) F G k) (rpow (zpRing p) x k)) n
      = rsum (zpRing p) (fun k => rsum (zpRing p) (fun j =>
          (zpRing p).mul
            ((zpRing p).mul (F j) (psPow (zpRing p) G j k))
            (rpow (zpRing p) x k)) n) n :=
    rsum_congr (zpRing p) n (fun k hk => by
      show (zpRing p).mul
          (rsum (zpRing p) (fun j =>
            (zpRing p).mul (F j) (psPow (zpRing p) G j k)) (k + 1))
          (rpow (zpRing p) x k) = _
      rw [show rsum (zpRing p) (fun j =>
            (zpRing p).mul (F j) (psPow (zpRing p) G j k)) (k + 1)
          = rsum (zpRing p) (fun j =>
              (zpRing p).mul (F j) (psPow (zpRing p) G j k)) n
        from (rsum_pad (zpRing p) (fun j =>
            (zpRing p).mul (F j) (psPow (zpRing p) G j k))
          (by omega) (fun j hj => by
            show (zpRing p).mul (F j) (psPow (zpRing p) G j k)
              = (zpRing p).zero
            rw [psPow_coeff_zero (zpRing p) G hG j k (by omega)]
            exact (zpRing p).mul_zero (F j))).symm,
        rsum_mul_right (zpRing p) (fun j =>
          (zpRing p).mul (F j) (psPow (zpRing p) G j k))
          (rpow (zpRing p) x k) n])
  rw [hA, rsum_exchange (zpRing p) (fun k j =>
    (zpRing p).mul ((zpRing p).mul (F j) (psPow (zpRing p) G j k))
      (rpow (zpRing p) x k)) n n]
  refine rsum_congr (zpRing p) n (fun j _ => ?_)
  show rsum (zpRing p) (fun k =>
      (zpRing p).mul ((zpRing p).mul (F j) (psPow (zpRing p) G j k))
        (rpow (zpRing p) x k)) n
    = (zpRing p).mul (F j)
        (rsum (zpRing p) (fun k =>
          (zpRing p).mul (psPow (zpRing p) G j k) (rpow (zpRing p) x k))
          n)
  rw [rsum_mul_left (zpRing p) (fun k =>
      (zpRing p).mul (psPow (zpRing p) G j k) (rpow (zpRing p) x k))
      (F j) n]
  exact rsum_congr (zpRing p) n (fun k _ =>
    (zpRing p).mul_assoc (F j) (psPow (zpRing p) G j k)
      (rpow (zpRing p) x k))

/-- **定理 (M79-2): 合成との両立（本丸）** — (F∘G)(x) = F(G(x))
    （G(0) = 0。外側の点 G(x) ∈ pℤ_p の witness e' は引数で受ける）。 -/
theorem zpEval_comp (p : Nat) (F G : PS (zpRing p))
    (hG : G 0 = (zpRing p).zero) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    (e' : (Zp p).carrier)
    (hx' : zpEval p G x e hx
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e') :
    zpEval p (psComp (zpRing p) F G) x e hx
      = zpEval p F (zpEval p G x e hx) e' hx' := by
  apply Subtype.ext
  funext n
  -- 右辺の部分和: rpow y j を zpEval (G^j) に折りたたむ（要素レベル）
  have hR : zpEvalSeg p F (zpEval p G x e hx) n
      = rsum (zpRing p) (fun j =>
          (zpRing p).mul (F j)
            (zpEval p (psPow (zpRing p) G j) x e hx)) n := by
    show rsum (zpRing p) (fun j =>
        (zpRing p).mul (F j)
          (rpow (zpRing p) (zpEval p G x e hx) j)) n = _
    exact rsum_congr (zpRing p) n (fun j _ => by
      rw [← zpEval_pow p G x e hx j])
  -- 両辺をレベル n の和に落とし、項ごとに定義的一致
  show (zpEvalSeg p (psComp (zpRing p) F G) x n).val n
    = (zpEvalSeg p F (zpEval p G x e hx) n).val n
  rw [zpEvalSeg_comp p F G hG x n, hR]
  show (projRing p n).map (rsum (zpRing p) (fun j =>
      (zpRing p).mul (F j) (zpEvalSeg p (psPow (zpRing p) G j) x n)) n)
    = (projRing p n).map (rsum (zpRing p) (fun j =>
        (zpRing p).mul (F j) (zpEval p (psPow (zpRing p) G j) x e hx)) n)
  rw [ringHom_rsum (projRing p n) (fun j =>
      (zpRing p).mul (F j) (zpEvalSeg p (psPow (zpRing p) G j) x n)) n,
    ringHom_rsum (projRing p n) (fun j =>
      (zpRing p).mul (F j) (zpEval p (psPow (zpRing p) G j) x e hx)) n]
  refine rsum_congr (zmodRing (p ^ n)) n (fun j _ => ?_)
  show (projRing p n).map ((zpRing p).mul (F j)
      (zpEvalSeg p (psPow (zpRing p) G j) x n))
    = (projRing p n).map ((zpRing p).mul (F j)
        (zpEval p (psPow (zpRing p) G j) x e hx))
  rw [(projRing p n).map_mul, (projRing p n).map_mul]
  rfl

end IUT
