/-
  IUT/FormalGroupEvalComp.lean — M74（連鎖律 CR1/CR2 の 1 変数版と
  注入の橋渡し: 逆元キャンペーン第三層）

  逆元の方程式検証に必要な連鎖律を M70a/M70b（3 変数版）の精密な
  1 変数ミラーで完全証明する。

  * M74-1 `ps21Comp_comp1`（CR1） — f∘(F(P,Q)) = (f∘₂F)(P,Q)
    （F₀₀ = P(0) = Q(0) = 0。冪の代入 + 族和表示 + m-和の移送 +
    打ち切り padding）
  * M74-2 `ps21Comp_comp2`（CR2） — (F(U,V))(P,Q) = F(U(P,Q), V(P,Q))
    （U₀₀ = V₀₀ = 0・P(0) = Q(0) = 0。両辺を共通の四重和に正規化、
    ps2Comp2_pad（M70b）は 2 変数の補題なのでそのまま再登板）
  * M74-3 `ps21Comp_inX` / `ps21Comp_inY` — **注入の橋渡し**:
    (in2X f)(P,Q) = f∘P・(in2Y f)(P,Q) = f∘Q（一点集中和、無条件）

  後合成 (F(P,Q))∘g = F(P∘g, Q∘g) は psComp の乗法性（M72F）と
  合流する次層。全て選択公理不使用。
-/
import IUT.FormalGroupEvalMult

namespace IUT

/-! ## 連鎖律 CR1 -/

/-- **定理 (M74-1): 連鎖律 CR1 の 1 変数版** —
    f∘(F(P,Q)) = (f∘₂F)(P,Q)（F₀₀ = P(0) = Q(0) = 0）。 -/
theorem ps21Comp_comp1 (R : CRing) (f : PS R) (F : PS2 R) (P Q : PS R)
    (hF : F 0 0 = R.zero) (hP : P 0 = R.zero) (hQ : Q 0 = R.zero) :
    psComp R f (ps21Comp R F P Q)
      = ps21Comp R (ps2Comp1 R f F) P Q := by
  funext n
  -- 左辺: 冪の代入 + 族和表示で三重和へ
  have hL : psComp R f (ps21Comp R F P Q) n
      = rsum R (fun m => rsum R (fun b => rsum R (fun a =>
          R.mul (f m) (R.mul (psPow (psRing R) F m b a)
            (psMul R (psPow R P a) (psPow R Q b) n)))
          (n + 1)) (n + 1)) (n + 1) := by
    show rsum R (fun m => R.mul (f m)
        (psPow R (ps21Comp R F P Q) m n)) (n + 1) = _
    refine rsum_congr R (n + 1) (fun m _ => ?_)
    rw [← ps21Comp_pow R F P Q hP hQ m,
      ps21Comp_eq_fam R (psPow (psRing R) F m) P Q hP hQ
        (n + 1) n (by omega)]
    show R.mul (f m) (rsum R (fun b => rsum R (fun a =>
        R.mul (psPow (psRing R) F m b a)
          (psMul R (psPow R P a) (psPow R Q b) n))
        (n + 1)) (n + 1)) = _
    rw [rsum_mul_left R _ (f m) (n + 1)]
    refine rsum_congr R (n + 1) (fun b _ => ?_)
    rw [rsum_mul_left R _ (f m) (n + 1)]
  -- 右辺: (f∘₂F) の係数の m-和を境界 n+1 に padding して三重和へ
  have hR : ps21Comp R (ps2Comp1 R f F) P Q n
      = rsum R (fun b => rsum R (fun a => rsum R (fun m =>
          R.mul (R.mul (f m) (psPow (psRing R) F m b a))
            (psMul R (psPow R P a) (psPow R Q b) n))
          (n + 1)) (n + 1)) (n + 1) := by
    show rsum R (fun b => rsum R (fun a =>
        R.mul (ps2Comp1 R f F b a)
          (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1) = _
    refine rsum_congr R (n + 1) (fun b hb => ?_)
    refine rsum_congr R (n + 1) (fun a ha => ?_)
    cases Nat.lt_or_ge n (a + b) with
    | inl hhigh =>
      rw [psPowPow_low R P Q hP hQ a b n hhigh,
        R.mul_zero (ps2Comp1 R f F b a)]
      have hz : rsum R (fun m =>
            R.mul (R.mul (f m) (psPow (psRing R) F m b a)) R.zero)
            (n + 1)
          = rsum R (fun _ => R.zero) (n + 1) :=
        rsum_congr R (n + 1) (fun m _ =>
          R.mul_zero (R.mul (f m) (psPow (psRing R) F m b a)))
      rw [hz, rsum_const_zero]
    | inr hlow =>
      have hpad : rsum R (fun m => R.mul (f m)
            (psPow (psRing R) F m b a)) (n + 1)
          = rsum R (fun m => R.mul (f m)
              (psPow (psRing R) F m b a)) (a + b + 1) :=
        rsum_pad R (fun m => R.mul (f m) (psPow (psRing R) F m b a))
          (by omega)
          (fun m hm => by
            show R.mul (f m) (psPow (psRing R) F m b a) = R.zero
            rw [ps2Pow_tcoeff_zero R F hF m a b (by omega)]
            exact R.mul_zero _)
      show R.mul (rsum R (fun m => R.mul (f m)
          (psPow (psRing R) F m b a)) (a + b + 1))
          (psMul R (psPow R P a) (psPow R Q b) n) = _
      rw [← hpad,
        rsum_mul_right R (fun m => R.mul (f m) (psPow (psRing R) F m b a))
          (psMul R (psPow R P a) (psPow R Q b) n) (n + 1)]
  rw [hL, hR]
  -- m-和を内側へ移送（exchange ×2）+ 結合律
  have hx1 : rsum R (fun m => rsum R (fun b => rsum R (fun a =>
        R.mul (f m) (R.mul (psPow (psRing R) F m b a)
          (psMul R (psPow R P a) (psPow R Q b) n)))
        (n + 1)) (n + 1)) (n + 1)
      = rsum R (fun b => rsum R (fun m => rsum R (fun a =>
          R.mul (f m) (R.mul (psPow (psRing R) F m b a)
            (psMul R (psPow R P a) (psPow R Q b) n)))
          (n + 1)) (n + 1)) (n + 1) :=
    rsum_exchange R (fun m b => rsum R (fun a =>
        R.mul (f m) (R.mul (psPow (psRing R) F m b a)
          (psMul R (psPow R P a) (psPow R Q b) n)))
        (n + 1)) (n + 1) (n + 1)
  rw [hx1]
  refine rsum_congr R (n + 1) (fun b _ => ?_)
  have hx2 : rsum R (fun m => rsum R (fun a =>
        R.mul (f m) (R.mul (psPow (psRing R) F m b a)
          (psMul R (psPow R P a) (psPow R Q b) n)))
        (n + 1)) (n + 1)
      = rsum R (fun a => rsum R (fun m =>
          R.mul (f m) (R.mul (psPow (psRing R) F m b a)
            (psMul R (psPow R P a) (psPow R Q b) n)))
          (n + 1)) (n + 1) :=
    rsum_exchange R (fun m a =>
        R.mul (f m) (R.mul (psPow (psRing R) F m b a)
          (psMul R (psPow R P a) (psPow R Q b) n)))
        (n + 1) (n + 1)
  rw [hx2]
  refine rsum_congr R (n + 1) (fun a _ => ?_)
  exact rsum_congr R (n + 1) (fun m _ =>
    (R.mul_assoc (f m) (psPow (psRing R) F m b a) _).symm)

/-! ## 連鎖律 CR2 -/

/-- **定理 (M74-2): 連鎖律 CR2 の 1 変数版** —
    (F(U,V))(P,Q) = F(U(P,Q), V(P,Q))
    （U₀₀ = V₀₀ = 0・P(0) = Q(0) = 0）。 -/
theorem ps21Comp_comp2 (R : CRing) (F U V : PS2 R) (P Q : PS R)
    (hU : U 0 0 = R.zero) (hV : V 0 0 = R.zero)
    (hP : P 0 = R.zero) (hQ : Q 0 = R.zero) :
    ps21Comp R (ps2Comp2 R F U V) P Q
      = ps21Comp R F (ps21Comp R U P Q) (ps21Comp R V P Q) := by
  funext n
  -- 左辺 → 共通形 Z
  have hZL : ps21Comp R (ps2Comp2 R F U V) P Q n
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ =>
            R.mul (F b₁ a₁)
              (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                  (psPow (psRing R) V b₁)) b a)
                (psMul R (psPow R P a) (psPow R Q b) n)))
            (n + 1)) (n + 1)) (n + 1)) (n + 1) := by
    show rsum R (fun b => rsum R (fun a =>
        R.mul (ps2Comp2 R F U V b a)
          (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1) = _
    refine rsum_congr R (n + 1) (fun b hb => ?_)
    refine rsum_congr R (n + 1) (fun a ha => ?_)
    cases Nat.lt_or_ge n (a + b) with
    | inl hhigh =>
      rw [psPowPow_low R P Q hP hQ a b n hhigh,
        R.mul_zero (ps2Comp2 R F U V b a)]
      have hz : rsum R (fun b₁ => rsum R (fun a₁ =>
            R.mul (F b₁ a₁)
              (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                  (psPow (psRing R) V b₁)) b a) R.zero))
            (n + 1)) (n + 1)
          = rsum R (fun _ => R.zero) (n + 1) :=
        rsum_congr R (n + 1) (fun b₁ _ => by
          have hz2 : rsum R (fun a₁ =>
                R.mul (F b₁ a₁)
                  (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                      (psPow (psRing R) V b₁)) b a) R.zero))
                (n + 1)
              = rsum R (fun _ => R.zero) (n + 1) :=
            rsum_congr R (n + 1) (fun a₁ _ => by
              rw [R.mul_zero ((psMul (psRing R) (psPow (psRing R) U a₁)
                  (psPow (psRing R) V b₁)) b a),
                R.mul_zero (F b₁ a₁)])
          rw [hz2]
          exact rsum_const_zero R (n + 1))
      rw [hz, rsum_const_zero]
    | inr hlow =>
      rw [ps2Comp2_pad R F U V hU hV (n + 1) b a (by omega),
        rsum_mul_right R _
          (psMul R (psPow R P a) (psPow R Q b) n) (n + 1)]
      refine rsum_congr R (n + 1) (fun b₁ _ => ?_)
      rw [rsum_mul_right R _
        (psMul R (psPow R P a) (psPow R Q b) n) (n + 1)]
      exact rsum_congr R (n + 1) (fun a₁ _ =>
        R.mul_assoc (F b₁ a₁) _ _)
  -- 右辺 → Z'（添字順 (b₁,a₁,b,a)）
  have hZR : ps21Comp R F (ps21Comp R U P Q) (ps21Comp R V P Q) n
      = rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun b =>
          rsum R (fun a =>
            R.mul (F b₁ a₁)
              (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                  (psPow (psRing R) V b₁)) b a)
                (psMul R (psPow R P a) (psPow R Q b) n)))
            (n + 1)) (n + 1)) (n + 1)) (n + 1) := by
    show rsum R (fun b₁ => rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          (psMul R (psPow R (ps21Comp R U P Q) a₁)
            (psPow R (ps21Comp R V P Q) b₁) n)) (n + 1)) (n + 1) = _
    refine rsum_congr R (n + 1) (fun b₁ _ => ?_)
    refine rsum_congr R (n + 1) (fun a₁ _ => ?_)
    rw [← ps21Comp_pow R U P Q hP hQ a₁, ← ps21Comp_pow R V P Q hP hQ b₁,
      ← ps21Comp_mul R (psPow (psRing R) U a₁) (psPow (psRing R) V b₁)
        P Q hP hQ,
      ps21Comp_eq_fam R (psMul (psRing R) (psPow (psRing R) U a₁)
        (psPow (psRing R) V b₁)) P Q hP hQ (n + 1) n (by omega)]
    show R.mul (F b₁ a₁) (rsum R (fun b => rsum R (fun a =>
        R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
            (psPow (psRing R) V b₁)) b a)
          (psMul R (psPow R P a) (psPow R Q b) n))
        (n + 1)) (n + 1)) = _
    rw [rsum_mul_left R _ (F b₁ a₁) (n + 1)]
    refine rsum_congr R (n + 1) (fun b _ => ?_)
    rw [rsum_mul_left R _ (F b₁ a₁) (n + 1)]
  rw [hZL, hZR]
  -- 添字交換 (b₁,a₁,b,a) → (b,a,b₁,a₁)
  have e1 : rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun b =>
        rsum R (fun a => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            (psMul R (psPow R P a) (psPow R Q b) n)))
          (n + 1)) (n + 1)) (n + 1)) (n + 1)
      = rsum R (fun b₁ => rsum R (fun b => rsum R (fun a₁ =>
          rsum R (fun a => R.mul (F b₁ a₁)
            (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                (psPow (psRing R) V b₁)) b a)
              (psMul R (psPow R P a) (psPow R Q b) n)))
            (n + 1)) (n + 1)) (n + 1)) (n + 1) :=
    rsum_congr R (n + 1) (fun b₁ _ =>
      rsum_exchange R (fun a₁ b => rsum R (fun a => R.mul (F b₁ a₁)
        (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
            (psPow (psRing R) V b₁)) b a)
          (psMul R (psPow R P a) (psPow R Q b) n)))
        (n + 1)) (n + 1) (n + 1))
  have e2 : rsum R (fun b₁ => rsum R (fun b => rsum R (fun a₁ =>
        rsum R (fun a => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            (psMul R (psPow R P a) (psPow R Q b) n)))
          (n + 1)) (n + 1)) (n + 1)) (n + 1)
      = rsum R (fun b => rsum R (fun b₁ => rsum R (fun a₁ =>
          rsum R (fun a => R.mul (F b₁ a₁)
            (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                (psPow (psRing R) V b₁)) b a)
              (psMul R (psPow R P a) (psPow R Q b) n)))
            (n + 1)) (n + 1)) (n + 1)) (n + 1) :=
    rsum_exchange R (fun b₁ b => rsum R (fun a₁ =>
        rsum R (fun a => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            (psMul R (psPow R P a) (psPow R Q b) n)))
          (n + 1)) (n + 1)) (n + 1) (n + 1)
  have e3 : rsum R (fun b => rsum R (fun b₁ => rsum R (fun a₁ =>
        rsum R (fun a => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            (psMul R (psPow R P a) (psPow R Q b) n)))
          (n + 1)) (n + 1)) (n + 1)) (n + 1)
      = rsum R (fun b => rsum R (fun b₁ => rsum R (fun a =>
          rsum R (fun a₁ => R.mul (F b₁ a₁)
            (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                (psPow (psRing R) V b₁)) b a)
              (psMul R (psPow R P a) (psPow R Q b) n)))
            (n + 1)) (n + 1)) (n + 1)) (n + 1) :=
    rsum_congr R (n + 1) (fun b _ =>
      rsum_congr R (n + 1) (fun b₁ _ =>
        rsum_exchange R (fun a₁ a => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            (psMul R (psPow R P a) (psPow R Q b) n)))
          (n + 1) (n + 1)))
  have e4 : rsum R (fun b => rsum R (fun b₁ => rsum R (fun a =>
        rsum R (fun a₁ => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            (psMul R (psPow R P a) (psPow R Q b) n)))
          (n + 1)) (n + 1)) (n + 1)) (n + 1)
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ => R.mul (F b₁ a₁)
            (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                (psPow (psRing R) V b₁)) b a)
              (psMul R (psPow R P a) (psPow R Q b) n)))
            (n + 1)) (n + 1)) (n + 1)) (n + 1) :=
    rsum_congr R (n + 1) (fun b _ =>
      rsum_exchange R (fun b₁ a => rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            (psMul R (psPow R P a) (psPow R Q b) n)))
        (n + 1)) (n + 1) (n + 1))
  rw [e1, e2, e3, e4]

/-! ## 注入の橋渡し -/

/-- **M74-3a: X 注入の橋渡し** — (in2X f)(P,Q) = f∘P
    （b = 0 への一点集中・Q^0 = 1 の除去、無条件）。 -/
theorem ps21Comp_inX (R : CRing) (f : PS R) (P Q : PS R) :
    ps21Comp R (psC (psRing R) f) P Q = psComp R f P := by
  funext n
  show rsum R (fun b => rsum R (fun a =>
      R.mul (psC (psRing R) f b a)
        (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1)
    = psComp R f P n
  have houter : rsum R (fun b => rsum R (fun a =>
      R.mul (psC (psRing R) f b a)
        (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1)
      = rsum R (fun a =>
          R.mul (psC (psRing R) f 0 a)
            (psMul R (psPow R P a) (psPow R Q 0) n)) (n + 1) :=
    rsum_single R (fun b => rsum R (fun a =>
        R.mul (psC (psRing R) f b a)
          (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) 0 (n + 1)
      (by omega)
      (fun b _ hb => by
        show rsum R (fun a =>
            R.mul (psC (psRing R) f b a)
              (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1) = R.zero
        have hz : rsum R (fun a =>
            R.mul (psC (psRing R) f b a)
              (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)
            = rsum R (fun _ => R.zero) (n + 1) :=
          rsum_congr R (n + 1) (fun a _ => by
            rw [show psC (psRing R) f b = (psRing R).zero from if_neg hb]
            exact R.zero_mul _)
        rw [hz]
        exact rsum_const_zero R (n + 1))
  rw [houter]
  have hone : ∀ a, psMul R (psPow R P a) (psPow R Q 0) = psPow R P a :=
    fun a => by
      show (psRing R).mul (psPow R P a) ((psRing R).one) = psPow R P a
      rw [(psRing R).mul_comm, (psRing R).one_mul]
  refine rsum_congr R (n + 1) (fun a _ => ?_)
  rw [hone a]
  rfl

/-- **M74-3b: Y 注入の橋渡し** — (in2Y f)(P,Q) = f∘Q
    （各 b で a = 0 への一点集中・P^0 = 1 の除去、無条件）。 -/
theorem ps21Comp_inY (R : CRing) (f : PS R) (P Q : PS R) :
    ps21Comp R (psMap (psConstHom R) f) P Q = psComp R f Q := by
  funext n
  show rsum R (fun b => rsum R (fun a =>
      R.mul (psC R (f b) a)
        (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1)
    = psComp R f Q n
  have hinner : ∀ b, rsum R (fun a =>
      R.mul (psC R (f b) a)
        (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)
      = R.mul (psC R (f b) 0)
          (psMul R (psPow R P 0) (psPow R Q b) n) :=
    fun b => rsum_single R (fun a =>
        R.mul (psC R (f b) a)
          (psMul R (psPow R P a) (psPow R Q b) n)) 0 (n + 1)
      (by omega)
      (fun a _ ha => by
        show R.mul (psC R (f b) a)
            (psMul R (psPow R P a) (psPow R Q b) n) = R.zero
        rw [show psC R (f b) a = R.zero from if_neg ha]
        exact R.zero_mul _)
  have hone : ∀ b, psMul R (psPow R P 0) (psPow R Q b) = psPow R Q b :=
    fun b => (psRing R).one_mul (psPow R Q b)
  refine rsum_congr R (n + 1) (fun b _ => ?_)
  rw [hinner b, hone b]
  rfl

end IUT
