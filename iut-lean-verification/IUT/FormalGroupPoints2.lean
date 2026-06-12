/-
  IUT/FormalGroupPoints2.lean — M80（2 変数評価と輸送連鎖律:
  点の群キャンペーン第四層）

  2 変数級数 F ∈ ℤ_p[[X,Y]] の点 (x, y) ∈ pℤ_p × pℤ_p での値
  F(x, y) ∈ ℤ_p を構成し（M77 の二重和版）、**輸送連鎖律**

    **(F(P,Q))(t) = F(P(t), Q(t))**

  を完全証明する。これにより M62〜M76 で証明済みの**級数レベルの
  群法則恒等式が 1 パラメータ径路上の点へ輸送**できる
  （例: F(X,ι) = 0 ⟹ F(x, ι(x)) = 0 — 次層）。

  * M80-1 `zpEval2Seg` / `zpEval2Seg_stable` — 二重部分和と安定性
    （行ごとの x-pad と行束の y-split、はみ出しは x^i・y^i 因子で
    レベル i 射影が殺す — M77-4 の二重版）
  * M80-2 `zpEval2` / `zpEval2_witness_irrel` / `zpEval2_congr_points` —
    評価の本体・witness 非依存性・点の置換
  * M80-3 `zpEvalSeg_ps21Comp` — 部分和の代入恒等式（純環レベル:
    M79-1 の二重版、psPowPow_low の pad ×2 + 添字移送）
  * M80-4 `zpEval_ps21Comp` — **輸送連鎖律（本丸）**

  群法則の点への輸送（可換・逆元・[a]-加群則）と点の群 F(pℤ_p) の
  パッケージングは次層。全て選択公理不使用。
-/
import IUT.FormalGroupPointsComp

namespace IUT

/-! ## 二重部分和と安定性 -/

/-- **M80-1a: 二重部分和** Σ_{b<N}Σ_{a<N} F_{b,a}·x^a·y^b ∈ ℤ_p。 -/
def zpEval2Seg (p : Nat) (F : PS2 (zpRing p)) (x y : (Zp p).carrier)
    (N : Nat) : (Zp p).carrier :=
  rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
    (zpRing p).mul (F b a)
      ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b))) N) N

/-- **定理 (M80-1b): 二重部分和の安定性** — x = p·ex・y = p·ey、
    i ≤ j のときレベル i では二重和は境界 i で打ち切れる。 -/
theorem zpEval2Seg_stable (p : Nat) (F : PS2 (zpRing p))
    (x ex y ey : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    {i j : Nat} (h : i ≤ j) :
    (zpEval2Seg p F x y j).val i = (zpEval2Seg p F x y i).val i := by
  obtain ⟨d, hd⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  subst hd
  -- 各行 b: 内側 a-和を i で分割し、尻尾から x^i を括り出す
  have hinner : ∀ b, rsum (zpRing p) (fun a =>
        (zpRing p).mul (F b a)
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        (i + d)
      = (zpRing p).add
          (rsum (zpRing p) (fun a =>
            (zpRing p).mul (F b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))) i)
          ((zpRing p).mul (rpow (zpRing p) x i)
            (rsum (zpRing p) (fun k =>
              (zpRing p).mul (F b (i + k))
                ((zpRing p).mul (rpow (zpRing p) x k)
                  (rpow (zpRing p) y b))) d)) := by
    intro b
    rw [rsum_split (zpRing p) (fun a =>
      (zpRing p).mul (F b a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      i d]
    refine congrArg ((zpRing p).add _) ?_
    have hterm : ∀ k, k < d →
        (zpRing p).mul (F b (i + k))
          ((zpRing p).mul (rpow (zpRing p) x (i + k))
            (rpow (zpRing p) y b))
        = (zpRing p).mul (rpow (zpRing p) x i)
            ((zpRing p).mul (F b (i + k))
              ((zpRing p).mul (rpow (zpRing p) x k)
                (rpow (zpRing p) y b))) := by
      intro k _
      rw [rpow_add (zpRing p) x i k,
        (zpRing p).mul_assoc (rpow (zpRing p) x i) (rpow (zpRing p) x k)
          (rpow (zpRing p) y b)]
      exact CRing.mul_left_comm (zpRing p) (F b (i + k))
        (rpow (zpRing p) x i)
        ((zpRing p).mul (rpow (zpRing p) x k) (rpow (zpRing p) y b))
    exact (rsum_congr (zpRing p) d hterm).trans
      ((rsum_mul_left (zpRing p) (fun k =>
          (zpRing p).mul (F b (i + k))
            ((zpRing p).mul (rpow (zpRing p) x k)
              (rpow (zpRing p) y b)))
        (rpow (zpRing p) x i) d).symm)
  -- 行束を i で分割し、b ≥ i の行から y^i を括り出す
  have hrowterm : ∀ k, k < d → ∀ a, a < i →
      (zpRing p).mul (F (i + k) a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y (i + k)))
      = (zpRing p).mul (rpow (zpRing p) y i)
          ((zpRing p).mul (F (i + k) a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y k))) := by
    intro k _ a _
    rw [rpow_add (zpRing p) y i k,
      CRing.mul_left_comm (zpRing p) (rpow (zpRing p) x a)
        (rpow (zpRing p) y i) (rpow (zpRing p) y k)]
    exact CRing.mul_left_comm (zpRing p) (F (i + k) a)
      (rpow (zpRing p) y i)
      ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y k))
  have hrows : rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (F b a)
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        i) (i + d)
      = (zpRing p).add (zpEval2Seg p F x y i)
          ((zpRing p).mul (rpow (zpRing p) y i)
            (rsum (zpRing p) (fun k => rsum (zpRing p) (fun a =>
              (zpRing p).mul (F (i + k) a)
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y k))) i) d)) := by
    rw [rsum_split (zpRing p) (fun b => rsum (zpRing p) (fun a =>
      (zpRing p).mul (F b a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      i) i d]
    refine congrArg ((zpRing p).add (zpEval2Seg p F x y i)) ?_
    have hrow : ∀ k, k < d →
        rsum (zpRing p) (fun a =>
          (zpRing p).mul (F (i + k) a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y (i + k)))) i
        = (zpRing p).mul (rpow (zpRing p) y i)
            (rsum (zpRing p) (fun a =>
              (zpRing p).mul (F (i + k) a)
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y k))) i) :=
      fun k hk =>
        (rsum_congr (zpRing p) i (fun a ha => hrowterm k hk a ha)).trans
          ((rsum_mul_left (zpRing p) (fun a =>
              (zpRing p).mul (F (i + k) a)
                ((zpRing p).mul (rpow (zpRing p) x a)
                  (rpow (zpRing p) y k)))
            (rpow (zpRing p) y i) i).symm)
    exact (rsum_congr (zpRing p) d hrow).trans
      ((rsum_mul_left (zpRing p) (fun k => rsum (zpRing p) (fun a =>
          (zpRing p).mul (F (i + k) a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y k))) i)
        (rpow (zpRing p) y i) d).symm)
  -- 全体: S(i+d) = (S(i) + y^i·B) + x^i·A
  have hS : zpEval2Seg p F x y (i + d)
      = (zpRing p).add
          ((zpRing p).add (zpEval2Seg p F x y i)
            ((zpRing p).mul (rpow (zpRing p) y i)
              (rsum (zpRing p) (fun k => rsum (zpRing p) (fun a =>
                (zpRing p).mul (F (i + k) a)
                  ((zpRing p).mul (rpow (zpRing p) x a)
                    (rpow (zpRing p) y k))) i) d)))
          ((zpRing p).mul (rpow (zpRing p) x i)
            (rsum (zpRing p) (fun b => rsum (zpRing p) (fun k =>
              (zpRing p).mul (F b (i + k))
                ((zpRing p).mul (rpow (zpRing p) x k)
                  (rpow (zpRing p) y b))) d) (i + d))) := by
    show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (F b a)
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        (i + d)) (i + d) = _
    rw [rsum_congr (zpRing p) (i + d) (fun b _ => hinner b),
      rsum_add (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (F b a)
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        i)
        (fun b => (zpRing p).mul (rpow (zpRing p) x i)
          (rsum (zpRing p) (fun k =>
            (zpRing p).mul (F b (i + k))
              ((zpRing p).mul (rpow (zpRing p) x k)
                (rpow (zpRing p) y b))) d)) (i + d),
      rsum_mul_left (zpRing p) (fun b => rsum (zpRing p) (fun k =>
        (zpRing p).mul (F b (i + k))
          ((zpRing p).mul (rpow (zpRing p) x k)
            (rpow (zpRing p) y b))) d)
        (rpow (zpRing p) x i) (i + d),
      hrows]
  -- レベル i 射影: x^i・y^i 因子が消える
  show (projRing p i).map (zpEval2Seg p F x y (i + d))
    = (projRing p i).map (zpEval2Seg p F x y i)
  rw [hS, (projRing p i).map_add, (projRing p i).map_add,
    (projRing p i).map_mul, (projRing p i).map_mul,
    proj_rpow_x_zero p x ex hx i, proj_rpow_x_zero p y ey hy i,
    CRing.zero_mul (zmodRing (p ^ i)), CRing.zero_mul (zmodRing (p ^ i)),
    CRing.add_zero (zmodRing (p ^ i)), CRing.add_zero (zmodRing (p ^ i))]

/-! ## 評価の本体 -/

/-- **M80-2a: 2 変数評価** F(x, y) ∈ ℤ_p。 -/
def zpEval2 (p : Nat) (F : PS2 (zpRing p)) (x ex y ey : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey) :
    (Zp p).carrier :=
  ⟨fun n => (zpEval2Seg p F x y n).val n, by
    intro i j h
    have h1 : (zmodTrans (pow_dvd_mono p h)).map
        ((zpEval2Seg p F x y j).val j) = (zpEval2Seg p F x y j).val i :=
      (zpEval2Seg p F x y j).property h
    show (zmodTrans (pow_dvd_mono p h)).map ((zpEval2Seg p F x y j).val j)
      = (zpEval2Seg p F x y i).val i
    rw [h1]
    exact zpEval2Seg_stable p F x ex y ey hx hy h⟩

/-- **M80-2b: witness 非依存性**（成分は witness に言及しない）。 -/
theorem zpEval2_witness_irrel (p : Nat) (F : PS2 (zpRing p))
    (x ex ex' y ey ey' : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hx' : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex')
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hy' : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey') :
    zpEval2 p F x ex y ey hx hy = zpEval2 p F x ex' y ey' hx' hy' :=
  Subtype.ext rfl

/-- **M80-2c: 点の置換** — 値が等しい点では評価も等しい
    （witness は付け替え可能）。 -/
theorem zpEval2_congr_points (p : Nat) (F : PS2 (zpRing p))
    (x ex y ey x' ex' y' ey' : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hx' : x' = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex')
    (hy' : y' = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey')
    (hxx : x = x') (hyy : y = y') :
    zpEval2 p F x ex y ey hx hy = zpEval2 p F x' ex' y' ey' hx' hy' := by
  subst hxx
  subst hyy
  exact zpEval2_witness_irrel p F x ex ex' y ey ey' hx hx' hy hy'

/-! ## 輸送連鎖律 -/

/-- **M80-3: 部分和の代入恒等式**（純環レベル・射影不要） —
    Σ_{k<n} (F(P,Q))_k t^k = Σ_{b<n}Σ_{a<n} F_{b,a}·zpEvalSeg (P^a·Q^b) n
    （psPowPow_low の truncation で (b,a)-和を n まで pad できる）。 -/
theorem zpEvalSeg_ps21Comp (p : Nat) (F : PS2 (zpRing p))
    (P Q : PS (zpRing p))
    (hP : P 0 = (zpRing p).zero) (hQ : Q 0 = (zpRing p).zero)
    (t : (Zp p).carrier) (n : Nat) :
    zpEvalSeg p (ps21Comp (zpRing p) F P Q) t n
      = rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
          (zpRing p).mul (F b a)
            (zpEvalSeg p (psMul (zpRing p) (psPow (zpRing p) P a)
              (psPow (zpRing p) Q b)) t n)) n) n := by
  show rsum (zpRing p) (fun k =>
      (zpRing p).mul (ps21Comp (zpRing p) F P Q k) (rpow (zpRing p) t k))
      n = _
  -- 各 k で (b,a)-境界を k+1 → n に pad、t^k を内側へ
  have hA : rsum (zpRing p) (fun k =>
        (zpRing p).mul (ps21Comp (zpRing p) F P Q k)
          (rpow (zpRing p) t k)) n
      = rsum (zpRing p) (fun k => rsum (zpRing p) (fun b =>
          rsum (zpRing p) (fun a =>
            (zpRing p).mul
              ((zpRing p).mul (F b a)
                (psMul (zpRing p) (psPow (zpRing p) P a)
                  (psPow (zpRing p) Q b) k))
              (rpow (zpRing p) t k)) n) n) n :=
    rsum_congr (zpRing p) n (fun k hk => by
      show (zpRing p).mul (ps21Comp (zpRing p) F P Q k)
          (rpow (zpRing p) t k) = _
      rw [ps21Comp_pad (zpRing p) F P Q hP hQ n k (by omega),
        rsum_mul_right (zpRing p) (fun b => rsum (zpRing p) (fun a =>
          (zpRing p).mul (F b a)
            (psMul (zpRing p) (psPow (zpRing p) P a)
              (psPow (zpRing p) Q b) k)) n) (rpow (zpRing p) t k) n]
      refine rsum_congr (zpRing p) n (fun b _ => ?_)
      show (zpRing p).mul (rsum (zpRing p) (fun a =>
          (zpRing p).mul (F b a)
            (psMul (zpRing p) (psPow (zpRing p) P a)
              (psPow (zpRing p) Q b) k)) n) (rpow (zpRing p) t k) = _
      rw [rsum_mul_right (zpRing p) (fun a =>
        (zpRing p).mul (F b a)
          (psMul (zpRing p) (psPow (zpRing p) P a)
            (psPow (zpRing p) Q b) k)) (rpow (zpRing p) t k) n])
  rw [hA, rsum_exchange (zpRing p) (fun k b => rsum (zpRing p) (fun a =>
    (zpRing p).mul
      ((zpRing p).mul (F b a)
        (psMul (zpRing p) (psPow (zpRing p) P a)
          (psPow (zpRing p) Q b) k))
      (rpow (zpRing p) t k)) n) n n]
  refine rsum_congr (zpRing p) n (fun b _ => ?_)
  show rsum (zpRing p) (fun k => rsum (zpRing p) (fun a =>
      (zpRing p).mul
        ((zpRing p).mul (F b a)
          (psMul (zpRing p) (psPow (zpRing p) P a)
            (psPow (zpRing p) Q b) k))
        (rpow (zpRing p) t k)) n) n = _
  rw [rsum_exchange (zpRing p) (fun k a =>
    (zpRing p).mul
      ((zpRing p).mul (F b a)
        (psMul (zpRing p) (psPow (zpRing p) P a)
          (psPow (zpRing p) Q b) k))
      (rpow (zpRing p) t k)) n n]
  refine rsum_congr (zpRing p) n (fun a _ => ?_)
  show rsum (zpRing p) (fun k =>
      (zpRing p).mul
        ((zpRing p).mul (F b a)
          (psMul (zpRing p) (psPow (zpRing p) P a)
            (psPow (zpRing p) Q b) k))
        (rpow (zpRing p) t k)) n
    = (zpRing p).mul (F b a)
        (rsum (zpRing p) (fun k =>
          (zpRing p).mul
            (psMul (zpRing p) (psPow (zpRing p) P a)
              (psPow (zpRing p) Q b) k)
            (rpow (zpRing p) t k)) n)
  rw [rsum_mul_left (zpRing p) (fun k =>
      (zpRing p).mul
        (psMul (zpRing p) (psPow (zpRing p) P a)
          (psPow (zpRing p) Q b) k)
        (rpow (zpRing p) t k)) (F b a) n]
  exact rsum_congr (zpRing p) n (fun k _ =>
    (zpRing p).mul_assoc (F b a)
      (psMul (zpRing p) (psPow (zpRing p) P a)
        (psPow (zpRing p) Q b) k)
      (rpow (zpRing p) t k))

/-- **定理 (M80-4): 輸送連鎖律（本丸）** —
    (F(P,Q))(t) = F(P(t), Q(t))（P(0) = Q(0) = 0、点の witness は
    引数渡し）。級数レベルの群法則恒等式を点へ輸送する装置。 -/
theorem zpEval_ps21Comp (p : Nat) (F : PS2 (zpRing p))
    (P Q : PS (zpRing p))
    (hP : P 0 = (zpRing p).zero) (hQ : Q 0 = (zpRing p).zero)
    (t e : (Zp p).carrier)
    (ht : t = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    (ex ey : (Zp p).carrier)
    (hx : zpEval p P t e ht
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : zpEval p Q t e ht
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey) :
    zpEval p (ps21Comp (zpRing p) F P Q) t e ht
      = zpEval2 p F (zpEval p P t e ht) ex (zpEval p Q t e ht) ey
          hx hy := by
  apply Subtype.ext
  funext n
  -- 右辺の二重部分和: (P(t))^a·(Q(t))^b を zpEval (P^a·Q^b) に折りたたむ
  have hR : zpEval2Seg p F (zpEval p P t e ht) (zpEval p Q t e ht) n
      = rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
          (zpRing p).mul (F b a)
            (zpEval p (psMul (zpRing p) (psPow (zpRing p) P a)
              (psPow (zpRing p) Q b)) t e ht)) n) n := by
    show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (F b a)
          ((zpRing p).mul (rpow (zpRing p) (zpEval p P t e ht) a)
            (rpow (zpRing p) (zpEval p Q t e ht) b))) n) n = _
    refine rsum_congr (zpRing p) n (fun b _ => ?_)
    refine rsum_congr (zpRing p) n (fun a _ => ?_)
    rw [← zpEval_pow p P t e ht a, ← zpEval_pow p Q t e ht b,
      ← zpEval_mul p (psPow (zpRing p) P a) (psPow (zpRing p) Q b)
        t e ht]
  show (zpEvalSeg p (ps21Comp (zpRing p) F P Q) t n).val n
    = (zpEval2Seg p F (zpEval p P t e ht) (zpEval p Q t e ht) n).val n
  rw [zpEvalSeg_ps21Comp p F P Q hP hQ t n, hR]
  -- レベル n の和に落とし、項ごとに定義的一致
  show (projRing p n).map (rsum (zpRing p) (fun b =>
      rsum (zpRing p) (fun a =>
        (zpRing p).mul (F b a)
          (zpEvalSeg p (psMul (zpRing p) (psPow (zpRing p) P a)
            (psPow (zpRing p) Q b)) t n)) n) n)
    = (projRing p n).map (rsum (zpRing p) (fun b =>
        rsum (zpRing p) (fun a =>
          (zpRing p).mul (F b a)
            (zpEval p (psMul (zpRing p) (psPow (zpRing p) P a)
              (psPow (zpRing p) Q b)) t e ht)) n) n)
  rw [ringHom_rsum (projRing p n) (fun b => rsum (zpRing p) (fun a =>
      (zpRing p).mul (F b a)
        (zpEvalSeg p (psMul (zpRing p) (psPow (zpRing p) P a)
          (psPow (zpRing p) Q b)) t n)) n) n,
    ringHom_rsum (projRing p n) (fun b => rsum (zpRing p) (fun a =>
      (zpRing p).mul (F b a)
        (zpEval p (psMul (zpRing p) (psPow (zpRing p) P a)
          (psPow (zpRing p) Q b)) t e ht)) n) n]
  refine rsum_congr (zmodRing (p ^ n)) n (fun b _ => ?_)
  show (projRing p n).map (rsum (zpRing p) (fun a =>
      (zpRing p).mul (F b a)
        (zpEvalSeg p (psMul (zpRing p) (psPow (zpRing p) P a)
          (psPow (zpRing p) Q b)) t n)) n)
    = (projRing p n).map (rsum (zpRing p) (fun a =>
        (zpRing p).mul (F b a)
          (zpEval p (psMul (zpRing p) (psPow (zpRing p) P a)
            (psPow (zpRing p) Q b)) t e ht)) n)
  rw [ringHom_rsum (projRing p n) (fun a =>
      (zpRing p).mul (F b a)
        (zpEvalSeg p (psMul (zpRing p) (psPow (zpRing p) P a)
          (psPow (zpRing p) Q b)) t n)) n,
    ringHom_rsum (projRing p n) (fun a =>
      (zpRing p).mul (F b a)
        (zpEval p (psMul (zpRing p) (psPow (zpRing p) P a)
          (psPow (zpRing p) Q b)) t e ht)) n]
  refine rsum_congr (zmodRing (p ^ n)) n (fun a _ => ?_)
  show (projRing p n).map ((zpRing p).mul (F b a)
      (zpEvalSeg p (psMul (zpRing p) (psPow (zpRing p) P a)
        (psPow (zpRing p) Q b)) t n))
    = (projRing p n).map ((zpRing p).mul (F b a)
        (zpEval p (psMul (zpRing p) (psPow (zpRing p) P a)
          (psPow (zpRing p) Q b)) t e ht))
  rw [(projRing p n).map_mul, (projRing p n).map_mul]
  rfl

end IUT
