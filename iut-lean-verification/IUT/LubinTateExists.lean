/-
  IUT/LubinTateExists.lean — M49（Lubin–Tate 存在定理: 最終層）

  f = pX + X^p に対し、任意の a : ℤ_p で

    F(0) = 0、F(1) = a、F∘f = p·F + F^p

  を満たす F ∈ ℤ_p[[X]] を**構成的に**建て、M42 の一意性と合わせて
  **Lubin–Tate 補題（[a] 系列の存在と一意性）を完成**する。

  係数の再帰構成: F₀ = 0、F₁ = a、n = m+2 では係数方程式
  F_n·(p^n − p) = D_n（D_n = 部分解の M48 誤差項の n 次係数、
  F_{<n} のみに依存）を

    F_n := u_n^{-1} · (D_n / p)、 p^n − p = p·u_n、u_n = p^{n−1} − 1（単数）

  で解く。除算の正当性は **M48 の誤差整除性**（mod-p 還元 +
  Frobenius 定理）、u_n の逆元は **M36 の単元理論**、p での除算は
  **M43 の zpDivP** による — 全キャンペーンの部品がここで合流する。

  * M49-1 `not_dvd_pow_sub_one` / `ipow_sub_p_factor` /
    `CRing.add_transfer` / `psPow_coeff_congr'` — 簿記
  * M49-2 `ltErr` / `ltNext` / `ltSeg` / `ltSol` — **係数の再帰構成**
    （初期切片 ltSeg N を一段ずつ拡張、choice-free）
  * M49-3 切片の整合性（stable・eq_sol・high）と低次値 F₀ = 0・F₁ = a
  * M49-4 `ltSol_div` 系 — **除算恒等式** π·(u·F_n) = D_n
  * M49-5 `ltSol_equation` — **方程式の全係数検証**（n = 0, 1 は直接、
    n ≥ 2 は一意性証明と同じ分解 L + F_n·p^n = p·F_n + T を逆向きに）
  * M49-6 `lubin_tate_exists` / `lubin_tate` — **Lubin–Tate 補題**
    （存在 + 一意性のパッケージ）

  全て選択公理不使用。
-/
import IUT.LTErrorDivisible

namespace IUT

/-! ## 簿記 -/

/-- p ∤ p^{m+1} − 1（M42 の単数性の核、独立補題化）。 -/
theorem not_dvd_pow_sub_one (p : Nat) (hp : IsPrime p) (m : Nat) :
    ¬ ((p : Nat) : Int) ∣ (ipow ((p : Nat) : Int) (m + 1) - 1) := by
  intro hd
  apply not_dvd_one p hp.1
  have hdp : ((p : Nat) : Int) ∣ ipow ((p : Nat) : Int) (m + 1) :=
    ⟨ipow ((p : Nat) : Int) m, by
      show ipow ((p : Nat) : Int) m * ((p : Nat) : Int)
        = ((p : Nat) : Int) * ipow ((p : Nat) : Int) m
      exact Int.mul_comm _ _⟩
  obtain ⟨x, hx⟩ := hdp
  obtain ⟨y, hy⟩ := hd
  refine ⟨x - y, ?_⟩
  rw [Int.mul_sub, ← hx, ← hy]
  generalize ipow ((p : Nat) : Int) (m + 1) = W
  omega

/-- p^{m+2} − p = p·(p^{m+1} − 1)（M42 の分解、独立補題化）。 -/
theorem ipow_sub_p_factor (p m : Nat) :
    ipow ((p : Nat) : Int) (m + 2) - ((p : Nat) : Int)
      = ((p : Nat) : Int) * (ipow ((p : Nat) : Int) (m + 1) - 1) := by
  rw [Int.mul_sub, Int.mul_one]
  have he : ((p : Nat) : Int) * ipow ((p : Nat) : Int) (m + 1)
      = ipow ((p : Nat) : Int) (m + 2) := by
    show ((p : Nat) : Int) * ipow ((p : Nat) : Int) (m + 1)
      = ipow ((p : Nat) : Int) (m + 1) * ((p : Nat) : Int)
    exact Int.mul_comm _ _
  rw [he]

/-- 移項簿記: X − Y = T − L なら L + X = Y + T。 -/
theorem CRing.add_transfer (R : CRing) {X Y T L : R.carrier}
    (h : R.add X (R.neg Y) = R.add T (R.neg L)) :
    R.add L X = R.add Y T := by
  have h2 : R.add (R.add X (R.neg Y)) (R.add Y L)
      = R.add (R.add T (R.neg L)) (R.add L Y) := by
    rw [h, R.add_comm Y L]
  rw [R.add_assoc X (R.neg Y) (R.add Y L), ← R.add_assoc (R.neg Y) Y L,
    R.neg_add, R.zero_add] at h2
  rw [R.add_assoc T (R.neg L) (R.add L Y), ← R.add_assoc (R.neg L) L Y,
    R.neg_add, R.zero_add] at h2
  rw [R.add_comm L X, h2, R.add_comm T Y]

/-- psPow_coeff_congr の指数一般形（q ≥ 2）。 -/
theorem psPow_coeff_congr' (R : CRing) (F F' : PS R) (n : Nat)
    (hF : F 0 = R.zero) (hF' : F' 0 = R.zero)
    (hagree : ∀ j, j < n → F j = F' j) (q : Nat) (hq : 2 ≤ q) :
    psPow R F q n = psPow R F' q n := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  subst hk
  exact psPow_coeff_congr R F F' n hF hF' hagree k

/-! ## 係数の再帰構成 -/

/-- M48 の誤差項（級数として命名）: E(G) = (p·G + G^p) − G∘f。 -/
def ltErr (p : Nat) (G : PS (zpRing p)) : PS (zpRing p) :=
  psAdd (zpRing p)
    (psAdd (zpRing p)
      (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) G)
      (psPow (zpRing p) G p))
    (psNeg (zpRing p) (psComp (zpRing p) G (ltPoly p)))

/-- 次の係数: F₀ = 0、F₁ = a、F_{m+2} = u^{-1}·(E(部分解)_{m+2} / p)。 -/
def ltNext (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier)
    (N : Nat) (G : PS (zpRing p)) : (Zp p).carrier :=
  match N with
  | 0 => (zpRing p).zero
  | 1 => a
  | m + 2 =>
    zpMul p
      (zpUnitInv p hp ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
        ⟨ipow ((p : Nat) : Int) (m + 1) - 1, rfl, not_dvd_pow_sub_one p hp m⟩)
      (zpDivP p hp.1 (ltErr p G (m + 2)))

/-- 初期切片: N 未満の係数まで構成、以降は 0。 -/
def ltSeg (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) : Nat → PS (zpRing p)
  | 0 => psZero (zpRing p)
  | N + 1 => fun n =>
      if n = N then ltNext p hp a N (ltSeg p hp a N) else ltSeg p hp a N n

/-- **M49-2: 解** F_n = （n+1 段目の切片の n 次係数）。 -/
def ltSol (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) : PS (zpRing p) :=
  fun n => ltSeg p hp a (n + 1) n

/-! ## 切片の整合性 -/

/-- 切片は安定: N ≤ M なら n < N で一致。 -/
theorem ltSeg_stable (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) :
    ∀ {N M : Nat}, N ≤ M → ∀ n, n < N →
    ltSeg p hp a M n = ltSeg p hp a N n := by
  intro N M h
  induction h with
  | refl => intro n _; rfl
  | @step M' h' ih =>
    intro n hn
    have hNM : N ≤ M' := h'
    show (if n = M' then ltNext p hp a M' (ltSeg p hp a M')
        else ltSeg p hp a M' n) = ltSeg p hp a N n
    rw [if_neg (show ¬ n = M' by omega)]
    exact ih n hn

/-- 切片は解と一致（n < N）。 -/
theorem ltSeg_eq_sol (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier)
    (N n : Nat) (h : n < N) :
    ltSeg p hp a N n = ltSol p hp a n :=
  ltSeg_stable p hp a (show n + 1 ≤ N by omega) n (by omega)

/-- 切片は境界以上で 0。 -/
theorem ltSeg_high (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) :
    ∀ N n, N ≤ n → ltSeg p hp a N n = (zpRing p).zero := by
  intro N
  induction N with
  | zero => intro n _; rfl
  | succ N ih =>
    intro n hn
    show (if n = N then ltNext p hp a N (ltSeg p hp a N)
        else ltSeg p hp a N n) = (zpRing p).zero
    rw [if_neg (show ¬ n = N by omega)]
    exact ih n (by omega)

/-- F_{m+2} の明示形。 -/
theorem ltSol_succ2 (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) (m : Nat) :
    ltSol p hp a (m + 2)
      = ltNext p hp a (m + 2) (ltSeg p hp a (m + 2)) := by
  show (if m + 2 = m + 2 then ltNext p hp a (m + 2) (ltSeg p hp a (m + 2))
      else ltSeg p hp a (m + 2) (m + 2)) = _
  exact if_pos rfl

/-! ## 除算恒等式 -/

/-- 誤差項係数の mod-p 消滅（M48 の係数形）。 -/
theorem ltErr_level_one (p : Nat) (hp : IsPrime p) (G : PS (zpRing p))
    (n : Nat) :
    (ltErr p G n).val 1 = Quot.mk (modCong (p ^ 1)).rel 0 :=
  congrFun (ltError_reduction p hp G) n

/-- u·F_{m+2} = E(切片)_{m+2} / p。 -/
theorem ltSol_u_mul (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) (m : Nat) :
    zpMul p ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
      (ltSol p hp a (m + 2))
      = zpDivP p hp.1 (ltErr p (ltSeg p hp a (m + 2)) (m + 2)) := by
  rw [ltSol_succ2 p hp a m]
  show zpMul p ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
      (zpMul p
        (zpUnitInv p hp ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
          ⟨ipow ((p : Nat) : Int) (m + 1) - 1, rfl, not_dvd_pow_sub_one p hp m⟩)
        (zpDivP p hp.1 (ltErr p (ltSeg p hp a (m + 2)) (m + 2)))) = _
  rw [← zpMul_assoc,
    zpMul_comm p ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
      (zpUnitInv p hp ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
        ⟨ipow ((p : Nat) : Int) (m + 1) - 1, rfl, not_dvd_pow_sub_one p hp m⟩),
    zpUnitInv_mul p hp ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
      ⟨ipow ((p : Nat) : Int) (m + 1) - 1, rfl, not_dvd_pow_sub_one p hp m⟩,
    zpOne_mul]

/-- **定理 (M49-4): 除算恒等式** π·(u·F_{m+2}) = E(切片)_{m+2}。 -/
theorem ltSol_div (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) (m : Nat) :
    zpMul p ((toZp p).map ((p : Nat) : Int))
      (zpMul p ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
        (ltSol p hp a (m + 2)))
      = ltErr p (ltSeg p hp a (m + 2)) (m + 2) := by
  rw [ltSol_u_mul p hp a m]
  exact zpDivP_mul_cancel p hp.1 _ (ltErr_level_one p hp _ (m + 2))

/-! ## 方程式の検証 -/

/-- **定理 (M49-5): ltSol は LT 方程式を満たす** —
    F∘f = p·F + F^p（全係数で検証）。 -/
theorem ltSol_equation (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) :
    psComp (zpRing p) (ltSol p hp a) (ltPoly p)
      = (psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) (ltSol p hp a))
          (psPow (zpRing p) (ltSol p hp a) p) := by
  funext n
  match n with
  | 0 =>
    show (zpRing p).add (zpRing p).zero
        ((zpRing p).mul (ltSol p hp a 0) (psPow (zpRing p) (ltPoly p) 0 0))
      = (zpRing p).add
          ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) (ltSol p hp a 0))
          (psPow (zpRing p) (ltSol p hp a) p 0)
    rw [show ltSol p hp a 0 = (zpRing p).zero from rfl,
      CRing.zero_mul (zpRing p) _, CRing.mul_zero (zpRing p) _,
      psPow_coeff_zero (zpRing p) (ltSol p hp a) rfl p 0
        (by have := hp.1; omega),
      (zpRing p).zero_add]
  | 1 =>
    show (zpRing p).add
        ((zpRing p).add (zpRing p).zero
          ((zpRing p).mul (ltSol p hp a 0) (psPow (zpRing p) (ltPoly p) 0 1)))
        ((zpRing p).mul (ltSol p hp a 1) (psPow (zpRing p) (ltPoly p) 1 1))
      = (zpRing p).add
          ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) (ltSol p hp a 1))
          (psPow (zpRing p) (ltSol p hp a) p 1)
    rw [psPow_coeff_diag (zpRing p) (ltPoly p) (ltPoly_coeff_zero p hp.1) 1,
      ltPoly_coeff_one p hp.1,
      show rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1
        = (zpRing p).mul (zpRing p).one ((toZp p).map ((p : Nat) : Int))
        from rfl,
      (zpRing p).one_mul,
      show ltSol p hp a 0 = (zpRing p).zero from rfl,
      CRing.zero_mul (zpRing p) _,
      (zpRing p).zero_add, (zpRing p).zero_add,
      psPow_coeff_zero (zpRing p) (ltSol p hp a) rfl p 1
        (by have := hp.1; omega),
      (zpRing p).add_zero]
    exact (zpRing p).mul_comm _ _
  | (m + 2) =>
    show (zpRing p).add
        (rsum (zpRing p) (fun k => (zpRing p).mul (ltSol p hp a k)
          (psPow (zpRing p) (ltPoly p) k (m + 2))) (m + 2))
        ((zpRing p).mul (ltSol p hp a (m + 2))
          (psPow (zpRing p) (ltPoly p) (m + 2) (m + 2)))
      = (zpRing p).add
          ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
            (ltSol p hp a (m + 2)))
          (psPow (zpRing p) (ltSol p hp a) p (m + 2))
    rw [psPow_coeff_diag (zpRing p) (ltPoly p) (ltPoly_coeff_zero p hp.1) (m + 2),
      ltPoly_coeff_one p hp.1]
    have hagree : ∀ j, j < m + 2 → ltSol p hp a j = ltSeg p hp a (m + 2) j :=
      fun j hj => (ltSeg_eq_sol p hp a (m + 2) j hj).symm
    have hL : rsum (zpRing p) (fun k => (zpRing p).mul (ltSol p hp a k)
          (psPow (zpRing p) (ltPoly p) k (m + 2))) (m + 2)
        = rsum (zpRing p) (fun k => (zpRing p).mul (ltSeg p hp a (m + 2) k)
          (psPow (zpRing p) (ltPoly p) k (m + 2))) (m + 2) :=
      rsum_congr (zpRing p) (m + 2) (fun k hk => by rw [hagree k (by omega)])
    have hseg0 : ltSeg p hp a (m + 2) 0 = (zpRing p).zero := by
      rw [ltSeg_eq_sol p hp a (m + 2) 0 (by omega)]
      rfl
    have hT : psPow (zpRing p) (ltSol p hp a) p (m + 2)
        = psPow (zpRing p) (ltSeg p hp a (m + 2)) p (m + 2) :=
      psPow_coeff_congr' (zpRing p) _ _ (m + 2) rfl hseg0 hagree p
        (by have := hp.1; omega)
    rw [hL, hT]
    have hseg_top : ltSeg p hp a (m + 2) (m + 2) = (zpRing p).zero :=
      ltSeg_high p hp a (m + 2) (m + 2) (Nat.le_refl _)
    have hD : ltErr p (ltSeg p hp a (m + 2)) (m + 2)
        = (zpRing p).add
            (psPow (zpRing p) (ltSeg p hp a (m + 2)) p (m + 2))
            ((zpRing p).neg (rsum (zpRing p)
              (fun k => (zpRing p).mul (ltSeg p hp a (m + 2) k)
                (psPow (zpRing p) (ltPoly p) k (m + 2))) (m + 2))) := by
      show (zpRing p).add
          ((zpRing p).add
            ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
              (ltSeg p hp a (m + 2) (m + 2)))
            (psPow (zpRing p) (ltSeg p hp a (m + 2)) p (m + 2)))
          ((zpRing p).neg ((zpRing p).add
            (rsum (zpRing p) (fun k => (zpRing p).mul (ltSeg p hp a (m + 2) k)
              (psPow (zpRing p) (ltPoly p) k (m + 2))) (m + 2))
            ((zpRing p).mul (ltSeg p hp a (m + 2) (m + 2))
              (psPow (zpRing p) (ltPoly p) (m + 2) (m + 2))))) = _
      rw [hseg_top, CRing.mul_zero (zpRing p) _, CRing.zero_mul (zpRing p) _,
        (zpRing p).zero_add, (zpRing p).add_zero]
    have hsub : (zpRing p).add
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 2))
        ((zpRing p).neg ((toZp p).map ((p : Nat) : Int)))
        = (zpRing p).mul ((toZp p).map ((p : Nat) : Int))
            ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1)) := by
      rw [rpow_toZp p ((p : Nat) : Int) (m + 2),
        toZp_sub p (ipow ((p : Nat) : Int) (m + 2)) ((p : Nat) : Int),
        ipow_sub_p_factor p m]
      exact (toZpRing p).map_mul ((p : Nat) : Int)
        (ipow ((p : Nat) : Int) (m + 1) - 1)
    have h1 : (zpRing p).mul
        ((zpRing p).add
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 2))
          ((zpRing p).neg ((toZp p).map ((p : Nat) : Int))))
        (ltSol p hp a (m + 2))
        = (zpRing p).add
          ((zpRing p).mul
            (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 2))
            (ltSol p hp a (m + 2)))
          ((zpRing p).neg ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
            (ltSol p hp a (m + 2)))) := by
      rw [(zpRing p).right_distrib,
        CRing.neg_mul (zpRing p) ((toZp p).map ((p : Nat) : Int))
          (ltSol p hp a (m + 2))]
    have hXY : (zpRing p).add
        ((zpRing p).mul (ltSol p hp a (m + 2))
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 2)))
        ((zpRing p).neg ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          (ltSol p hp a (m + 2))))
        = ltErr p (ltSeg p hp a (m + 2)) (m + 2) := by
      rw [(zpRing p).mul_comm (ltSol p hp a (m + 2))
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 2)),
        ← h1, hsub,
        (zpRing p).mul_assoc ((toZp p).map ((p : Nat) : Int))
          ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
          (ltSol p hp a (m + 2))]
      exact ltSol_div p hp a m
    exact (zpRing p).add_transfer (hXY.trans hD)

/-! ## Lubin–Tate 補題 -/

/-- **定理 (M49-6a): 存在** — F(0) = 0、F(1) = a、F∘f = p·F + F^p を
    満たす F の構成的存在。 -/
theorem lubin_tate_exists (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) :
    ∃ F : PS (zpRing p), F 0 = (zpRing p).zero ∧ F 1 = a ∧
      psComp (zpRing p) F (ltPoly p)
        = (psRing (zpRing p)).add
            (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F)
            (psPow (zpRing p) F p) :=
  ⟨ltSol p hp a, rfl, rfl, ltSol_equation p hp a⟩

/-- **定理 (M49-6b): Lubin–Tate 補題** — 存在と一意性のパッケージ
    （一意性は M42、存在は M49 の構成）。[a]_f 系列の理論の核。 -/
theorem lubin_tate (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) :
    ∃ F : PS (zpRing p),
      (F 0 = (zpRing p).zero ∧ F 1 = a ∧
        psComp (zpRing p) F (ltPoly p)
          = (psRing (zpRing p)).add
              (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F)
              (psPow (zpRing p) F p)) ∧
      ∀ F' : PS (zpRing p),
        F' 0 = (zpRing p).zero → F' 1 = a →
        psComp (zpRing p) F' (ltPoly p)
          = (psRing (zpRing p)).add
              (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F')
              (psPow (zpRing p) F' p) →
        F' = ltSol p hp a := by
  refine ⟨ltSol p hp a, ⟨rfl, rfl, ltSol_equation p hp a⟩, ?_⟩
  intro F' h0 h1 heq
  exact lubin_tate_unique_zp p hp (ltPoly p) (ltPoly_coeff_zero p hp.1)
    (ltPoly_coeff_one p hp.1) p (by have := hp.1; omega) F' (ltSol p hp a)
    h0 rfl h1 heq (ltSol_equation p hp a)

end IUT
