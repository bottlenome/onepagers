/-
  IUT/FormalGroupChain.lean — M68（連鎖律の基盤: 結合則キャンペーン第六層）

  結合則の方程式成分（f∘A = A(fX,fY,fZ) for A = F(F(X,Y),Z) 等）を
  検証するための連鎖律の基盤層。

  * M68-1 `ps3Mul_low_zero` / `ps3PowPow_low` — **積の下方消滅**:
    A が総次数 dA 未満で消え B が dB 未満で消えるなら A·B は
    dA + dB 未満で消える。冪積 P^aQ^b は総次数 a+b 未満で消える
    （P₀₀₀ = Q₀₀₀ = 0）— 代入の打ち切り正当化の一般形
  * M68-2 `liftXY_mul/pow/comp1`・`liftYZ_mul/pow/comp1` —
    **lift は環準同型かつ代入と交換**: liftXY = psC（定数埋め込み =
    psConstHom の map）・liftYZ = psMap（係数ごとの持ち上げ）なので
    mul・pow は ring-hom 性から一行、**f∘₃(lift F) = lift(f∘₂F)** は
    係数計算（j = 0 / i = 0 の層で 2 変数の代入と一致、外では両辺 0）
  * M68-3 `ps3X_eq_in3X` 等・`ps3Comp1_in3X/Y/Z` — 座標 = 注入の
    psX 像、**f∘₃(in3• g) = in3•(f∘₁g)**（一変数 psComp に落ちる —
    M65 の in3•_pow の合流）

  これらの合流で、結合則の両辺の方程式検証は「ps23Comp の乗法性
  （次層）+ 本層の交換則」に帰着する。全て選択公理不使用。
-/
import IUT.FormalGroupAssocDef

namespace IUT

/-! ## 積の下方消滅 -/

/-- **定理 (M68-1a): 積の下方消滅** — A が総次数 dA 未満で消え
    B が dB 未満で消えるなら、A·B は dA + dB 未満で消える。 -/
theorem ps3Mul_low_zero (R : CRing) (A B : PS3 R) (dA dB : Nat)
    (hA : ∀ c b a, a + b + c < dA → A c b a = R.zero)
    (hB : ∀ c b a, a + b + c < dB → B c b a = R.zero)
    (j k i : Nat) (h : i + k + j < dA + dB) :
    psMul (psRing (psRing R)) A B j k i = R.zero := by
  rw [ps3Mul_coeff R A B j k i]
  have hz : rsum R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul (A c b a) (B (j - c) (k - b) (i - a))) (i + 1)) (k + 1))
        (j + 1)
      = rsum R (fun _ => R.zero) (j + 1) :=
    rsum_congr R (j + 1) (fun c hc => by
      have hz2 : rsum R (fun b => rsum R (fun a =>
            R.mul (A c b a) (B (j - c) (k - b) (i - a))) (i + 1)) (k + 1)
          = rsum R (fun _ => R.zero) (k + 1) :=
        rsum_congr R (k + 1) (fun b hb => by
          have hz3 : rsum R (fun a =>
                R.mul (A c b a) (B (j - c) (k - b) (i - a))) (i + 1)
              = rsum R (fun _ => R.zero) (i + 1) :=
            rsum_congr R (i + 1) (fun a ha => by
              cases Nat.lt_or_ge (a + b + c) dA with
              | inl hlt =>
                rw [hA c b a hlt]
                exact R.zero_mul _
              | inr hge =>
                rw [hB (j - c) (k - b) (i - a) (by omega)]
                exact R.mul_zero _)
          rw [hz3]
          exact rsum_const_zero R (i + 1))
      rw [hz2]
      exact rsum_const_zero R (k + 1))
  rw [hz]
  exact rsum_const_zero R (j + 1)

/-- **定理 (M68-1b): 冪積の下方消滅** — P₀₀₀ = Q₀₀₀ = 0 なら
    P^a·Q^b は総次数 a + b 未満で消える（代入の打ち切り正当化）。 -/
theorem ps3PowPow_low (R : CRing) (P Q : PS3 R)
    (hP : P 0 0 0 = R.zero) (hQ : Q 0 0 0 = R.zero) (a b : Nat)
    (j k i : Nat) (h : i + k + j < a + b) :
    psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
      (psPow (psRing (psRing R)) Q b) j k i = R.zero :=
  ps3Mul_low_zero R (psPow (psRing (psRing R)) P a)
    (psPow (psRing (psRing R)) Q b) a b
    (fun c' b' a' h' => ps3Pow_tcoeff_zero R P hP a a' b' c' h')
    (fun c' b' a' h' => ps3Pow_tcoeff_zero R Q hQ b a' b' c' h')
    j k i h

/-! ## lift は環準同型かつ代入と交換 -/

/-- liftXY は積を保つ（psConstHom の map_mul）。 -/
theorem liftXY_mul (R : CRing) (F G : PS2 R) :
    liftXY R (psMul (psRing R) F G)
      = psMul (psRing (psRing R)) (liftXY R F) (liftXY R G) :=
  (psConstHom (psRing (psRing R))).map_mul F G

/-- liftXY は冪を保つ。 -/
theorem liftXY_pow (R : CRing) (F : PS2 R) (m : Nat) :
    psPow (psRing (psRing R)) (liftXY R F) m
      = liftXY R (psPow (psRing R) F m) := by
  show psPow (psRing (psRing R)) (psC (psRing (psRing R)) F) m = _
  rw [psPow_psC (psRing (psRing R)) F m,
    ← psPow_eq_rpow (psRing R) F m]
  rfl

/-- liftYZ は積を保つ（psMap の乗法性）。 -/
theorem liftYZ_mul (R : CRing) (F G : PS2 R) :
    liftYZ R (psMul (psRing R) F G)
      = psMul (psRing (psRing R)) (liftYZ R F) (liftYZ R G) :=
  psMap_mul (psRingHom (psConstHom R)) F G

/-- liftYZ は冪を保つ。 -/
theorem liftYZ_pow (R : CRing) (F : PS2 R) (m : Nat) :
    psPow (psRing (psRing R)) (liftYZ R F) m
      = liftYZ R (psPow (psRing R) F m) :=
  (psMap_pow (psRingHom (psConstHom R)) F m).symm

/-- **定理 (M68-2a): liftXY は 1 変数代入と交換** —
    f∘₃(liftXY F) = liftXY(f∘₂F)（j = 0 層では 2 変数の代入と一致、
    j ≥ 1 では両辺 0）。 -/
theorem liftXY_comp1 (R : CRing) (f : PS R) (F : PS2 R) :
    ps3Comp1 R f (liftXY R F) = liftXY R (ps2Comp1 R f F) := by
  funext j k i
  cases Nat.decEq j 0 with
  | isTrue hj =>
    subst hj
    show rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) (liftXY R F) m 0 k i)) (i + k + 0 + 1)
      = ps2Comp1 R f F k i
    show rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) (liftXY R F) m 0 k i)) (i + k + 1)
      = rsum R (fun m => R.mul (f m)
          (psPow (psRing R) F m k i)) (i + k + 1)
    exact rsum_congr R (i + k + 1) (fun m _ => by
      rw [liftXY_pow R F m]
      rfl)
  | isFalse hj =>
    show rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) (liftXY R F) m j k i)) (i + k + j + 1)
      = ((if j = 0 then ps2Comp1 R f F
          else (psRing (psRing R)).zero) : PS2 R) k i
    rw [if_neg hj]
    have hz : rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (liftXY R F) m j k i))
          (i + k + j + 1)
        = rsum R (fun _ => R.zero) (i + k + j + 1) :=
      rsum_congr R (i + k + j + 1) (fun m _ => by
        rw [liftXY_pow R F m,
          show liftXY R (psPow (psRing R) F m) j
              = (psRing (psRing R)).zero from if_neg hj]
        exact R.mul_zero _)
    rw [hz, rsum_const_zero]
    rfl

/-- **定理 (M68-2b): liftYZ は 1 変数代入と交換** —
    f∘₃(liftYZ F) = liftYZ(f∘₂F)（i = 0 層では 2 変数の代入と一致、
    i ≥ 1 では両辺 0）。 -/
theorem liftYZ_comp1 (R : CRing) (f : PS R) (F : PS2 R) :
    ps3Comp1 R f (liftYZ R F) = liftYZ R (ps2Comp1 R f F) := by
  funext j k i
  cases Nat.decEq i 0 with
  | isTrue hi =>
    subst hi
    show rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) (liftYZ R F) m j k 0)) (0 + k + j + 1)
      = ps2Comp1 R f F j k
    rw [show (0 : Nat) + k + j + 1 = k + j + 1 from by omega]
    show rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) (liftYZ R F) m j k 0)) (k + j + 1)
      = rsum R (fun m => R.mul (f m)
          (psPow (psRing R) F m j k)) (k + j + 1)
    exact rsum_congr R (k + j + 1) (fun m _ => by
      rw [liftYZ_pow R F m]
      rfl)
  | isFalse hi =>
    show rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) (liftYZ R F) m j k i)) (i + k + j + 1)
      = ((if i = 0 then ps2Comp1 R f F j k else R.zero) : R.carrier)
    rw [if_neg hi]
    have hz : rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (liftYZ R F) m j k i))
          (i + k + j + 1)
        = rsum R (fun _ => R.zero) (i + k + j + 1) :=
      rsum_congr R (i + k + j + 1) (fun m _ => by
        rw [liftYZ_pow R F m,
          show liftYZ R (psPow (psRing R) F m) j k i = R.zero from
            if_neg hi]
        exact R.mul_zero _)
    rw [hz]
    exact rsum_const_zero R (i + k + j + 1)

/-! ## 座標 = 注入の psX 像と、注入への代入 -/

/-- 座標 X は in3X(X)。 -/
theorem ps3X_eq_in3X (R : CRing) : ps3X R = in3X R (psX R) := rfl

/-- 座標 Y は in3Y(X)（M52 の psMap_constHom_psX）。 -/
theorem ps3Y_eq_in3Y (R : CRing) : ps3Y R = in3Y R (psX R) :=
  congrArg (psC (psRing (psRing R))) (psMap_constHom_psX R).symm

/-- 座標 Z は in3Z(X)。 -/
theorem ps3Z_eq_in3Z (R : CRing) : ps3Z R = in3Z R (psX R) := by
  funext j
  cases Nat.decEq j 1 with
  | isTrue hj =>
    subst hj
    rfl
  | isFalse hj =>
    show (if j = 1 then (psRing (psRing R)).one
        else (psRing (psRing R)).zero)
      = psC (psRing R) (psC R (psX R j))
    rw [if_neg hj, show psX R j = R.zero from if_neg hj, psC_zero R]
    exact (psC_zero (psRing R)).symm

/-- **定理 (M68-3a): X 注入への代入** —
    f∘₃(in3X g) = in3X(f∘₁g)（j = k = 0 層で一変数 psComp に落ちる）。 -/
theorem ps3Comp1_in3X (R : CRing) (f g : PS R) :
    ps3Comp1 R f (in3X R g) = in3X R (psComp R f g) := by
  funext j k i
  cases Nat.decEq j 0 with
  | isTrue hj =>
    subst hj
    cases Nat.decEq k 0 with
    | isTrue hk =>
      subst hk
      show rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3X R g) m 0 0 i)) (i + 0 + 0 + 1)
        = psComp R f g i
      show rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3X R g) m 0 0 i)) (i + 1)
        = rsum R (fun m => R.mul (f m) (psPow R g m i)) (i + 1)
      exact rsum_congr R (i + 1) (fun m _ => by
        rw [in3X_pow R g m]
        rfl)
    | isFalse hk =>
      show rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3X R g) m 0 k i)) (i + k + 0 + 1)
        = ((if k = 0 then psComp R f g else psZero R) : PS R) i
      rw [if_neg hk]
      have hz : rsum R (fun m => R.mul (f m)
            (psPow (psRing (psRing R)) (in3X R g) m 0 k i))
            (i + k + 0 + 1)
          = rsum R (fun _ => R.zero) (i + k + 0 + 1) :=
        rsum_congr R (i + k + 0 + 1) (fun m _ => by
          rw [in3X_pow R g m,
            show in3X R (psPow R g m) 0 k i = R.zero from by
              show psC (psRing R) (psPow R g m) k i = R.zero
              rw [show psC (psRing R) (psPow R g m) k
                  = (psRing R).zero from if_neg hk]
              rfl]
          exact R.mul_zero _)
      rw [hz]
      exact rsum_const_zero R (i + k + 0 + 1)
  | isFalse hj =>
    show rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) (in3X R g) m j k i)) (i + k + j + 1)
      = ((if j = 0 then psC (psRing R) (psComp R f g)
          else (psRing (psRing R)).zero) : PS2 R) k i
    rw [if_neg hj]
    have hz : rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3X R g) m j k i))
          (i + k + j + 1)
        = rsum R (fun _ => R.zero) (i + k + j + 1) :=
      rsum_congr R (i + k + j + 1) (fun m _ => by
        rw [in3X_pow R g m,
          show in3X R (psPow R g m) j
              = (psRing (psRing R)).zero from if_neg hj]
        exact R.mul_zero _)
    rw [hz, rsum_const_zero]
    rfl

/-- **定理 (M68-3b): Y 注入への代入** — f∘₃(in3Y g) = in3Y(f∘₁g)。 -/
theorem ps3Comp1_in3Y (R : CRing) (f g : PS R) :
    ps3Comp1 R f (in3Y R g) = in3Y R (psComp R f g) := by
  funext j k i
  cases Nat.decEq j 0 with
  | isTrue hj =>
    subst hj
    cases Nat.decEq i 0 with
    | isTrue hi =>
      subst hi
      show rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3Y R g) m 0 k 0)) (0 + k + 0 + 1)
        = psComp R f g k
      rw [show (0 : Nat) + k + 0 + 1 = k + 1 from by omega]
      show rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3Y R g) m 0 k 0)) (k + 1)
        = rsum R (fun m => R.mul (f m) (psPow R g m k)) (k + 1)
      exact rsum_congr R (k + 1) (fun m _ => by
        rw [in3Y_pow R g m]
        rfl)
    | isFalse hi =>
      show rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3Y R g) m 0 k i)) (i + k + 0 + 1)
        = ((if i = 0 then psComp R f g k else R.zero) : R.carrier)
      rw [if_neg hi]
      have hz : rsum R (fun m => R.mul (f m)
            (psPow (psRing (psRing R)) (in3Y R g) m 0 k i))
            (i + k + 0 + 1)
          = rsum R (fun _ => R.zero) (i + k + 0 + 1) :=
        rsum_congr R (i + k + 0 + 1) (fun m _ => by
          rw [in3Y_pow R g m,
            show in3Y R (psPow R g m) 0 k i = R.zero from if_neg hi]
          exact R.mul_zero _)
      rw [hz]
      exact rsum_const_zero R (i + k + 0 + 1)
  | isFalse hj =>
    show rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) (in3Y R g) m j k i)) (i + k + j + 1)
      = ((if j = 0 then psMap (psConstHom R) (psComp R f g)
          else (psRing (psRing R)).zero) : PS2 R) k i
    rw [if_neg hj]
    have hz : rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3Y R g) m j k i))
          (i + k + j + 1)
        = rsum R (fun _ => R.zero) (i + k + j + 1) :=
      rsum_congr R (i + k + j + 1) (fun m _ => by
        rw [in3Y_pow R g m,
          show in3Y R (psPow R g m) j
              = (psRing (psRing R)).zero from if_neg hj]
        exact R.mul_zero _)
    rw [hz, rsum_const_zero]
    rfl

/-- **定理 (M68-3c): Z 注入への代入** — f∘₃(in3Z g) = in3Z(f∘₁g)。 -/
theorem ps3Comp1_in3Z (R : CRing) (f g : PS R) :
    ps3Comp1 R f (in3Z R g) = in3Z R (psComp R f g) := by
  funext j k i
  cases Nat.decEq k 0 with
  | isTrue hk =>
    cases Nat.decEq i 0 with
    | isTrue hi =>
      subst hk
      subst hi
      show rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3Z R g) m j 0 0)) (0 + 0 + j + 1)
        = psComp R f g j
      rw [show (0 : Nat) + 0 + j + 1 = j + 1 from by omega]
      show rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3Z R g) m j 0 0)) (j + 1)
        = rsum R (fun m => R.mul (f m) (psPow R g m j)) (j + 1)
      exact rsum_congr R (j + 1) (fun m _ => by
        rw [in3Z_pow R g m]
        rfl)
    | isFalse hi =>
      subst hk
      show rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3Z R g) m j 0 i)) (i + 0 + j + 1)
        = ((if i = 0 then psComp R f g j else R.zero) : R.carrier)
      rw [if_neg hi]
      have hz : rsum R (fun m => R.mul (f m)
            (psPow (psRing (psRing R)) (in3Z R g) m j 0 i))
            (i + 0 + j + 1)
          = rsum R (fun _ => R.zero) (i + 0 + j + 1) :=
        rsum_congr R (i + 0 + j + 1) (fun m _ => by
          rw [in3Z_pow R g m,
            show in3Z R (psPow R g m) j 0 i = R.zero from by
              show psC R (psPow R g m j) i = R.zero
              exact if_neg hi]
          exact R.mul_zero _)
      rw [hz]
      exact rsum_const_zero R (i + 0 + j + 1)
  | isFalse hk =>
    show rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) (in3Z R g) m j k i)) (i + k + j + 1)
      = ((if k = 0 then psC R (psComp R f g j) else psZero R) : PS R) i
    rw [if_neg hk]
    have hz : rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) (in3Z R g) m j k i))
          (i + k + j + 1)
        = rsum R (fun _ => R.zero) (i + k + j + 1) :=
      rsum_congr R (i + k + j + 1) (fun m _ => by
        rw [in3Z_pow R g m,
          show in3Z R (psPow R g m) j k i = R.zero from by
            show (if k = 0 then psC R (psPow R g m j)
                else (psRing R).zero) i = R.zero
            rw [if_neg hk]
            rfl]
        exact R.mul_zero _)
    rw [hz]
    exact rsum_const_zero R (i + k + j + 1)

end IUT
