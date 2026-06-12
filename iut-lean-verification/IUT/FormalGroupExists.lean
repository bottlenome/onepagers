/-
  IUT/FormalGroupExists.lean — M60（LT 形式群法則の存在: 形式群最終層）

  **Lubin–Tate 形式群法則の存在定理**: 任意の素数 p に対し
  F ∈ ℤ_p[[X, Y]] で

    F₀₀ = 0・F₀₁ = F₁₀ = 1（F ≡ X + Y mod 総次数 2）かつ
    f∘F = F(f(X), f(Y))   （f = pX + X^p）

  を満たすものが存在する（IsLTFormalGroup p F の witness）。

  構成は M49（一変数 Lubin–Tate 補題）のスキーマの総次数版:
  総次数 0 は 0・総次数 1 は X + Y・総次数 m+2 の各係数は

    F_{j,i} := u⁻¹·(E(部分解)_{j,i} / p)、u = π^{m+1} − 1（単数）

  で一斉に決める（E = 誤差、M56 の choice-free 除算）。方程式の検証は
  M57（F^p の低次依存）・M58（左辺分解 π·F + F^p）・M59（右辺対角分離）
  の合流で π·u·F_{j,i} = E(部分解)_{j,i} に帰着し、移項簿記
  （M49 の add_transfer）で閉じる。

  * M60-1 `CRing.neg_zero` / `rpow_add` / `psPow_one_eq` — 簿記
  * M60-2 `lt2Next` / `lt2Seg` / `lt2Sol` — **係数の再帰構成**
    （層 N は総次数 N の係数だけを埋め、高次は 0 のまま）
  * M60-3 安定性（`lt2Seg_stable`・`lt2Seg_eq_sol`・`lt2Seg_high`）
  * M60-4 `lt2Sol_div` — **除算恒等式** π·(u·F_{j,i}) = E(部分解)_{j,i}
    （M36 単数逆元 + M43 zpDivP + M56 整除性の合流）
  * M60-5 `lt2Sol_equation` — **方程式の全係数検証**（総次数 0・1 は
    直接計算、m+2 は対角分離 + 移項）
  * M60-6 `lt_formal_group_exists` — **存在定理**
    ∃ F, IsLTFormalGroup p F

  これで M50–M60 の **11 層の形式群キャンペーンが完成**: 一変数
  Lubin–Tate 補題（M38–M49）に続き、二変数形式群法則の存在まで
  mathlib なし・選択公理なしで機械検証された。
-/
import IUT.FormalGroupDiag

namespace IUT

/-! ## 簿記 -/

/-- −0 = 0。 -/
theorem CRing.neg_zero (R : CRing) : R.neg R.zero = R.zero := by
  have h := CRing.add_neg R R.zero
  rw [R.zero_add] at h
  exact h

/-- 冪の指数加法則: x^{m+n} = x^m·x^n。 -/
theorem rpow_add (R : CRing) (x : R.carrier) (m : Nat) :
    ∀ n, rpow R x (m + n) = R.mul (rpow R x m) (rpow R x n) := by
  intro n
  induction n with
  | zero =>
    show rpow R x m = R.mul (rpow R x m) R.one
    rw [CRing.mul_one R _]
  | succ n ih =>
    show R.mul (rpow R x (m + n)) x
        = R.mul (rpow R x m) (R.mul (rpow R x n) x)
    rw [ih, R.mul_assoc]

/-- Q¹ = Q（一変数）。 -/
theorem psPow_one_eq (R : CRing) (Q : PS R) : psPow R Q 1 = Q :=
  (psRing R).one_mul Q

/-- 線形部の折りたたみ（右型）: (0+((0+0)+0)) + ((0+x)+0) = x。 -/
theorem lin_collapse_right (R : CRing) (x : R.carrier) :
    R.add (R.add R.zero (R.add (R.add R.zero R.zero) R.zero))
      (R.add (R.add R.zero x) R.zero) = x := by
  rw [R.zero_add R.zero, R.zero_add R.zero, R.zero_add R.zero,
    R.zero_add x, CRing.add_zero R x, R.zero_add x]

/-- 線形部の折りたたみ（左型）: (0+((0+0)+x)) + ((0+0)+0) = x。 -/
theorem lin_collapse_left (R : CRing) (x : R.carrier) :
    R.add (R.add R.zero (R.add (R.add R.zero R.zero) x))
      (R.add (R.add R.zero R.zero) R.zero) = x := by
  rw [R.zero_add R.zero, R.zero_add R.zero, R.zero_add x,
    R.zero_add x, CRing.add_zero R x]

/-! ## 係数の再帰構成 -/

/-- 総次数 N のスロット (j, i) の値: 次数 0 は 0・次数 1 は 1
    （線形部 X + Y）・次数 m+2 は u⁻¹·(E(部分解)_{j,i} / p)。 -/
def lt2Next (p : Nat) (hp : IsPrime p) (G : PS2 (zpRing p))
    (N : Nat) (j i : Nat) : (Zp p).carrier :=
  match N with
  | 0 => (zpRing p).zero
  | 1 => (zpRing p).one
  | m + 2 =>
    zpMul p
      (zpUnitInv p hp ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
        ⟨ipow ((p : Nat) : Int) (m + 1) - 1, rfl, not_dvd_pow_sub_one p hp m⟩)
      (zpDivP p hp.1 (lt2Err p G j i))

/-- 初期切片: 総次数 ≤ N の係数まで構成、高次は 0。 -/
def lt2Seg (p : Nat) (hp : IsPrime p) : Nat → PS2 (zpRing p)
  | 0 => fun _ _ => (zpRing p).zero
  | N + 1 => fun j i =>
      if i + j = N + 1 then lt2Next p hp (lt2Seg p hp N) (N + 1) j i
      else lt2Seg p hp N j i

/-- **M60-2: 解** F_{j,i} = （総次数 i+j 段目の切片の係数）。 -/
def lt2Sol (p : Nat) (hp : IsPrime p) : PS2 (zpRing p) :=
  fun j i => lt2Seg p hp (i + j) j i

/-! ## 切片の整合性 -/

/-- 切片は安定: N ≤ M なら総次数 ≤ N で一致。 -/
theorem lt2Seg_stable (p : Nat) (hp : IsPrime p) :
    ∀ {N M : Nat}, N ≤ M → ∀ j i, i + j ≤ N →
    lt2Seg p hp M j i = lt2Seg p hp N j i := by
  intro N M h
  induction h with
  | refl => intro j i _; rfl
  | @step M' h' ih =>
    intro j i hn
    have hNM : N ≤ M' := h'
    show (if i + j = M' + 1 then lt2Next p hp (lt2Seg p hp M') (M' + 1) j i
        else lt2Seg p hp M' j i) = lt2Seg p hp N j i
    rw [if_neg (show ¬ i + j = M' + 1 by omega)]
    exact ih j i hn

/-- 切片は解と一致（総次数 ≤ N）。 -/
theorem lt2Seg_eq_sol (p : Nat) (hp : IsPrime p) (N j i : Nat)
    (h : i + j ≤ N) : lt2Seg p hp N j i = lt2Sol p hp j i :=
  lt2Seg_stable p hp h j i (Nat.le_refl (i + j))

/-- 切片は境界を超えると 0。 -/
theorem lt2Seg_high (p : Nat) (hp : IsPrime p) :
    ∀ N j i, N < i + j → lt2Seg p hp N j i = (zpRing p).zero := by
  intro N
  induction N with
  | zero => intro j i _; rfl
  | succ N ih =>
    intro j i hn
    show (if i + j = N + 1 then lt2Next p hp (lt2Seg p hp N) (N + 1) j i
        else lt2Seg p hp N j i) = (zpRing p).zero
    rw [if_neg (show ¬ i + j = N + 1 by omega)]
    exact ih j i (by omega)

/-- 切片の定数項は常に 0。 -/
theorem lt2Seg_00 (p : Nat) (hp : IsPrime p) (N : Nat) :
    lt2Seg p hp N 0 0 = (zpRing p).zero :=
  lt2Seg_eq_sol p hp N 0 0 (Nat.zero_le N)

/-- F_{j,i}（総次数 m+2）の明示形。 -/
theorem lt2Sol_succ2 (p : Nat) (hp : IsPrime p) (m j i : Nat)
    (hdeg : i + j = m + 2) :
    lt2Sol p hp j i
      = lt2Next p hp (lt2Seg p hp (m + 1)) (m + 2) j i := by
  show lt2Seg p hp (i + j) j i = _
  rw [hdeg]
  show (if i + j = m + 1 + 1
      then lt2Next p hp (lt2Seg p hp (m + 1)) (m + 1 + 1) j i
      else lt2Seg p hp (m + 1) j i) = _
  rw [if_pos (show i + j = m + 1 + 1 by omega)]

/-! ## 除算恒等式 -/

/-- 誤差項係数の mod-p 消滅（係数形）。 -/
theorem lt2Err_level_one (p : Nat) (hp : IsPrime p) (G : PS2 (zpRing p))
    (hG : G 0 0 = (zpRing p).zero) (j i : Nat) :
    (lt2Err p G j i).val 1 = Quot.mk (modCong (p ^ 1)).rel 0 :=
  congrFun (congrFun
    (lt2Err_reduction p hp G (ps2Map_zero_cond p G hG)) j) i

/-- u·F_{j,i} = E(切片)_{j,i} / p。 -/
theorem lt2Sol_u_mul (p : Nat) (hp : IsPrime p) (m j i : Nat)
    (hdeg : i + j = m + 2) :
    zpMul p ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
      (lt2Sol p hp j i)
      = zpDivP p hp.1 (lt2Err p (lt2Seg p hp (m + 1)) j i) := by
  rw [lt2Sol_succ2 p hp m j i hdeg]
  show zpMul p ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
      (zpMul p
        (zpUnitInv p hp ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
          ⟨ipow ((p : Nat) : Int) (m + 1) - 1, rfl, not_dvd_pow_sub_one p hp m⟩)
        (zpDivP p hp.1 (lt2Err p (lt2Seg p hp (m + 1)) j i))) = _
  rw [← zpMul_assoc,
    zpMul_comm p ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
      (zpUnitInv p hp ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
        ⟨ipow ((p : Nat) : Int) (m + 1) - 1, rfl, not_dvd_pow_sub_one p hp m⟩),
    zpUnitInv_mul p hp ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
      ⟨ipow ((p : Nat) : Int) (m + 1) - 1, rfl, not_dvd_pow_sub_one p hp m⟩,
    zpOne_mul]

/-- **定理 (M60-4): 除算恒等式** π·(u·F_{j,i}) = E(切片)_{j,i}。 -/
theorem lt2Sol_div (p : Nat) (hp : IsPrime p) (m j i : Nat)
    (hdeg : i + j = m + 2) :
    zpMul p ((toZp p).map ((p : Nat) : Int))
      (zpMul p ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
        (lt2Sol p hp j i))
      = lt2Err p (lt2Seg p hp (m + 1)) j i := by
  rw [lt2Sol_u_mul p hp m j i hdeg]
  exact zpDivP_mul_cancel p hp.1 _
    (lt2Err_level_one p hp _ (lt2Seg_00 p hp (m + 1)) j i)

/-! ## 方程式の全係数検証 -/

/-- **定理 (M60-5): lt2Sol は形式群方程式の誤差を消す** —
    ∀ (j, i), E(F)_{j,i} = 0。 -/
theorem lt2Sol_equation (p : Nat) (hp : IsPrime p) :
    ∀ j i, lt2Err p (lt2Sol p hp) j i = (zpRing p).zero := by
  intro j i
  have hp2 : 2 ≤ p := hp.1
  have hF00 : lt2Sol p hp 0 0 = (zpRing p).zero := rfl
  match hdeg : i + j with
  | 0 =>
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi
    subst hj
    show (zpRing p).add
        (ps2Comp1 (zpRing p) (ltPoly p) (lt2Sol p hp) 0 0)
        ((zpRing p).neg (ps2Comp2 (zpRing p) (lt2Sol p hp)
          (psC (psRing (zpRing p)) (ltPoly p))
          (psMap (psConstHom (zpRing p)) (ltPoly p)) 0 0))
      = (zpRing p).zero
    have hLHS : ps2Comp1 (zpRing p) (ltPoly p) (lt2Sol p hp) 0 0
        = (zpRing p).zero := by
      rw [lt2_lhs_decomp p (lt2Sol p hp) hF00 0 0, hF00,
        CRing.mul_zero (zpRing p) _,
        ps2Pow_tcoeff_zero (zpRing p) (lt2Sol p hp) hF00 p 0 0
          (by omega),
        (zpRing p).zero_add]
    have hRHS : ps2Comp2 (zpRing p) (lt2Sol p hp)
        (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p)) 0 0
        = (zpRing p).zero := by
      rw [lt2_rhs_coeff (zpRing p) (ltPoly p) (lt2Sol p hp) 0 0]
      show (zpRing p).add (zpRing p).zero
          ((zpRing p).add (zpRing p).zero
            ((zpRing p).mul (lt2Sol p hp 0 0)
              ((zpRing p).mul (psPow (zpRing p) (ltPoly p) 0 0)
                (psPow (zpRing p) (ltPoly p) 0 0))))
        = (zpRing p).zero
      rw [hF00, CRing.zero_mul (zpRing p) _, (zpRing p).zero_add,
        (zpRing p).zero_add]
    rw [hLHS, hRHS, CRing.neg_zero (zpRing p), (zpRing p).zero_add]
  | 1 =>
    -- 線形部: (j,i) = (0,1) または (1,0)。両側とも π。
    have hLHS : ps2Comp1 (zpRing p) (ltPoly p) (lt2Sol p hp) j i
        = (toZp p).map ((p : Nat) : Int) := by
      rw [lt2_lhs_decomp p (lt2Sol p hp) hF00 j i,
        show lt2Sol p hp j i = (zpRing p).one from by
          show lt2Seg p hp (i + j) j i = (zpRing p).one
          rw [hdeg]
          show (if i + j = 0 + 1
              then lt2Next p hp (lt2Seg p hp 0) (0 + 1) j i
              else lt2Seg p hp 0 j i) = (zpRing p).one
          rw [if_pos (show i + j = 0 + 1 by omega)]
          rfl,
        CRing.mul_one (zpRing p) _,
        ps2Pow_tcoeff_zero (zpRing p) (lt2Sol p hp) hF00 p i j
          (by omega),
        (zpRing p).add_zero]
    have hRHS : ps2Comp2 (zpRing p) (lt2Sol p hp)
        (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p)) j i
        = (toZp p).map ((p : Nat) : Int) := by
      rw [lt2_rhs_coeff (zpRing p) (ltPoly p) (lt2Sol p hp) j i]
      cases Nat.decEq i 0 with
      | isTrue hi =>
        have hj : j = 1 := by omega
        subst hi
        subst hj
        show (zpRing p).add
            ((zpRing p).add (zpRing p).zero
              ((zpRing p).add ((zpRing p).add (zpRing p).zero
                ((zpRing p).mul (lt2Sol p hp 0 0)
                  ((zpRing p).mul (psPow (zpRing p) (ltPoly p) 0 0)
                    (psPow (zpRing p) (ltPoly p) 0 1))))
                ((zpRing p).mul (lt2Sol p hp 0 1)
                  ((zpRing p).mul (psPow (zpRing p) (ltPoly p) 1 0)
                    (psPow (zpRing p) (ltPoly p) 0 1)))))
            ((zpRing p).add ((zpRing p).add (zpRing p).zero
              ((zpRing p).mul (lt2Sol p hp 1 0)
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) 0 0)
                  (psPow (zpRing p) (ltPoly p) 1 1))))
              ((zpRing p).mul (lt2Sol p hp 1 1)
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) 1 0)
                  (psPow (zpRing p) (ltPoly p) 1 1))))
          = (toZp p).map ((p : Nat) : Int)
        rw [hF00, CRing.zero_mul (zpRing p) _,
          show psPow (zpRing p) (ltPoly p) 1 0 = (zpRing p).zero from by
            rw [psPow_one_eq (zpRing p) (ltPoly p)]
            exact ltPoly_coeff_zero p hp2,
          CRing.zero_mul (zpRing p) (psPow (zpRing p) (ltPoly p) 0 1),
          CRing.zero_mul (zpRing p) (psPow (zpRing p) (ltPoly p) 1 1),
          CRing.mul_zero (zpRing p) (lt2Sol p hp 0 1),
          CRing.mul_zero (zpRing p) (lt2Sol p hp 1 1),
          show psPow (zpRing p) (ltPoly p) 1 1
              = (toZp p).map ((p : Nat) : Int) from by
            rw [psPow_one_eq (zpRing p) (ltPoly p)]
            exact ltPoly_coeff_one p hp2,
          show psPow (zpRing p) (ltPoly p) 0 0 = (zpRing p).one from rfl,
          (zpRing p).one_mul ((toZp p).map ((p : Nat) : Int)),
          show lt2Sol p hp 1 0 = (zpRing p).one from rfl,
          (zpRing p).one_mul ((toZp p).map ((p : Nat) : Int))]
        exact lin_collapse_right (zpRing p) ((toZp p).map ((p : Nat) : Int))
      | isFalse hi =>
        have hi1 : i = 1 := by omega
        have hj : j = 0 := by omega
        subst hi1
        subst hj
        show (zpRing p).add
            ((zpRing p).add (zpRing p).zero
              ((zpRing p).add ((zpRing p).add (zpRing p).zero
                ((zpRing p).mul (lt2Sol p hp 0 0)
                  ((zpRing p).mul (psPow (zpRing p) (ltPoly p) 0 1)
                    (psPow (zpRing p) (ltPoly p) 0 0))))
                ((zpRing p).mul (lt2Sol p hp 0 1)
                  ((zpRing p).mul (psPow (zpRing p) (ltPoly p) 1 1)
                    (psPow (zpRing p) (ltPoly p) 0 0)))))
            ((zpRing p).add ((zpRing p).add (zpRing p).zero
              ((zpRing p).mul (lt2Sol p hp 1 0)
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) 0 1)
                  (psPow (zpRing p) (ltPoly p) 1 0))))
              ((zpRing p).mul (lt2Sol p hp 1 1)
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) 1 1)
                  (psPow (zpRing p) (ltPoly p) 1 0))))
          = (toZp p).map ((p : Nat) : Int)
        rw [hF00, CRing.zero_mul (zpRing p) _,
          show psPow (zpRing p) (ltPoly p) 1 0 = (zpRing p).zero from by
            rw [psPow_one_eq (zpRing p) (ltPoly p)]
            exact ltPoly_coeff_zero p hp2,
          CRing.mul_zero (zpRing p) (psPow (zpRing p) (ltPoly p) 0 1),
          CRing.mul_zero (zpRing p) (psPow (zpRing p) (ltPoly p) 1 1),
          CRing.mul_zero (zpRing p) (lt2Sol p hp 1 0),
          CRing.mul_zero (zpRing p) (lt2Sol p hp 1 1),
          show psPow (zpRing p) (ltPoly p) 1 1
              = (toZp p).map ((p : Nat) : Int) from by
            rw [psPow_one_eq (zpRing p) (ltPoly p)]
            exact ltPoly_coeff_one p hp2,
          show psPow (zpRing p) (ltPoly p) 0 0 = (zpRing p).one from rfl,
          CRing.mul_one (zpRing p) ((toZp p).map ((p : Nat) : Int)),
          show lt2Sol p hp 0 1 = (zpRing p).one from rfl,
          (zpRing p).one_mul ((toZp p).map ((p : Nat) : Int))]
        exact lin_collapse_left (zpRing p) ((toZp p).map ((p : Nat) : Int))
    show (zpRing p).add
        (ps2Comp1 (zpRing p) (ltPoly p) (lt2Sol p hp) j i)
        ((zpRing p).neg (ps2Comp2 (zpRing p) (lt2Sol p hp)
          (psC (psRing (zpRing p)) (ltPoly p))
          (psMap (psConstHom (zpRing p)) (ltPoly p)) j i))
      = (zpRing p).zero
    rw [hLHS, hRHS]
    exact CRing.add_neg (zpRing p) _
  | (m + 2) =>
    -- 主場合: 対角分離 + 除算恒等式 + 移項
    have hG00 : lt2Seg p hp (m + 1) 0 0 = (zpRing p).zero :=
      lt2Seg_00 p hp (m + 1)
    have hagree : ∀ b a, a + b < i + j →
        lt2Sol p hp b a = lt2Seg p hp (m + 1) b a :=
      fun b a hab =>
        (lt2Seg_eq_sol p hp (m + 1) b a (by omega)).symm
    have hGtop : lt2Seg p hp (m + 1) j i = (zpRing p).zero :=
      lt2Seg_high p hp (m + 1) j i (by omega)
    -- LHS の冪は切片で計算できる
    have hT : psPow (psRing (zpRing p)) (lt2Sol p hp) p j i
        = psPow (psRing (zpRing p)) (lt2Seg p hp (m + 1)) p j i :=
      ps2Pow_coeff_congr' (zpRing p) (i + j) hF00 hG00 hagree p hp2 j i
        (Nat.le_refl (i + j))
    -- RHS の対角分離（G の対角は 0）
    have hRHS : ps2Comp2 (zpRing p) (lt2Sol p hp)
        (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p)) j i
        = (zpRing p).add
            (ps2Comp2 (zpRing p) (lt2Seg p hp (m + 1))
              (psC (psRing (zpRing p)) (ltPoly p))
              (psMap (psConstHom (zpRing p)) (ltPoly p)) j i)
            ((zpRing p).mul (lt2Sol p hp j i)
              ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                (psPow (zpRing p) (ltPoly p) j j))) := by
      rw [lt2_rhs_split p hp2 (lt2Sol p hp) (lt2Seg p hp (m + 1)) j i
          hagree,
        hGtop, CRing.zero_mul (zpRing p) _, CRing.neg_zero (zpRing p),
        (zpRing p).add_zero]
    -- E(切片) の分解（切片の対角は 0）
    have hEG : lt2Err p (lt2Seg p hp (m + 1)) j i
        = (zpRing p).add
            (psPow (psRing (zpRing p)) (lt2Seg p hp (m + 1)) p j i)
            ((zpRing p).neg
              (ps2Comp2 (zpRing p) (lt2Seg p hp (m + 1))
                (psC (psRing (zpRing p)) (ltPoly p))
                (psMap (psConstHom (zpRing p)) (ltPoly p)) j i)) := by
      show (zpRing p).add
          (ps2Comp1 (zpRing p) (ltPoly p) (lt2Seg p hp (m + 1)) j i)
          ((zpRing p).neg
            (ps2Comp2 (zpRing p) (lt2Seg p hp (m + 1))
              (psC (psRing (zpRing p)) (ltPoly p))
              (psMap (psConstHom (zpRing p)) (ltPoly p)) j i)) = _
      rw [lt2_lhs_decomp p (lt2Seg p hp (m + 1)) hG00 j i, hGtop,
        CRing.mul_zero (zpRing p) _, (zpRing p).zero_add]
    -- 対角係数 C = π^{m+2}
    have hCpow : (zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
        (psPow (zpRing p) (ltPoly p) j j)
        = rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 2) := by
      rw [ltPow_diag p hp2 i, ltPow_diag p hp2 j,
        ← rpow_add (zpRing p) ((toZp p).map ((p : Nat) : Int)) i j]
      exact congrArg (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))) hdeg
    -- π^{m+2} − π = π·u
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
    -- (π^{m+2} − π)·S の分配
    have h1 : (zpRing p).mul
        ((zpRing p).add
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 2))
          ((zpRing p).neg ((toZp p).map ((p : Nat) : Int))))
        (lt2Sol p hp j i)
        = (zpRing p).add
          ((zpRing p).mul
            (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 2))
            (lt2Sol p hp j i))
          ((zpRing p).neg ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
            (lt2Sol p hp j i))) := by
      rw [(zpRing p).right_distrib,
        CRing.neg_mul (zpRing p) ((toZp p).map ((p : Nat) : Int))
          (lt2Sol p hp j i)]
    -- 除算恒等式（zpMul を環演算へ型強制）
    have hdiv : (zpRing p).mul ((toZp p).map ((p : Nat) : Int))
        ((zpRing p).mul ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
          (lt2Sol p hp j i))
        = lt2Err p (lt2Seg p hp (m + 1)) j i :=
      lt2Sol_div p hp m j i hdeg
    -- 移項の左辺: S·C − π·S = E(切片)
    have hXY : (zpRing p).add
        ((zpRing p).mul (lt2Sol p hp j i)
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
            (psPow (zpRing p) (ltPoly p) j j)))
        ((zpRing p).neg ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          (lt2Sol p hp j i)))
        = lt2Err p (lt2Seg p hp (m + 1)) j i := by
      rw [hCpow,
        (zpRing p).mul_comm (lt2Sol p hp j i)
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 2)),
        ← h1, hsub,
        (zpRing p).mul_assoc ((toZp p).map ((p : Nat) : Int))
          ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
          (lt2Sol p hp j i)]
      exact hdiv
    -- 仕上げ: LHS = RHS を移項で得て add_neg で閉じる
    have hmain : ps2Comp1 (zpRing p) (ltPoly p) (lt2Sol p hp) j i
        = ps2Comp2 (zpRing p) (lt2Sol p hp)
            (psC (psRing (zpRing p)) (ltPoly p))
            (psMap (psConstHom (zpRing p)) (ltPoly p)) j i := by
      rw [lt2_lhs_decomp p (lt2Sol p hp) hF00 j i, hT, hRHS]
      exact ((zpRing p).add_transfer (hXY.trans hEG)).symm
    show (zpRing p).add
        (ps2Comp1 (zpRing p) (ltPoly p) (lt2Sol p hp) j i)
        ((zpRing p).neg (ps2Comp2 (zpRing p) (lt2Sol p hp)
          (psC (psRing (zpRing p)) (ltPoly p))
          (psMap (psConstHom (zpRing p)) (ltPoly p)) j i))
      = (zpRing p).zero
    rw [hmain]
    exact CRing.add_neg (zpRing p) _

/-! ## 存在定理 -/

/-- **定理 (M60-6a): lt2Sol は LT 形式群法則**。 -/
theorem lt2Sol_is_formal_group (p : Nat) (hp : IsPrime p) :
    IsLTFormalGroup p (lt2Sol p hp) :=
  ⟨rfl, rfl, rfl,
    (lt2Err_zero_iff_equation p (lt2Sol p hp)).mp
      (funext fun j => funext fun i => lt2Sol_equation p hp j i)⟩

/-- **定理 (M60-6b): LT 形式群法則の存在** —
    任意の素数 p に対し IsLTFormalGroup p F なる F が存在する。
    M50–M60 の形式群キャンペーンの最終定理。 -/
theorem lt_formal_group_exists (p : Nat) (hp : IsPrime p) :
    ∃ F : PS2 (zpRing p), IsLTFormalGroup p F :=
  ⟨lt2Sol p hp, lt2Sol_is_formal_group p hp⟩

end IUT
