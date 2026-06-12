/-
  M70d: lift の代入互換（結合則キャンペーン第十二層）

  結合則の方程式検証の最終組み立てに必要な lift / 座標まわりの互換則:
  - 恒等代入の三変数版 X∘₃W = W と座標の ps23Comp 代入 X(P,Q) = P / Y(P,Q) = Q
  - **lift の ps3Comp3 崩落**: (liftXY G)∘(W₁,W₂,W₃) = G∘(W₁,W₂) と
    (liftYZ G)∘(W₁,W₂,W₃) = G∘(W₂,W₃)（c-和 / a-和の一点集中）
  - **lift と ps2Comp2 の交換**: liftXY(G∘₂(U,V)) = G∘(liftXY U, liftXY V) と
    liftYZ 版（lift の環準同型性 M68 + 層ごとの一致）
  - **lift は注入を注入へ**: liftXY(in2X f) = in3X f / liftXY(in2Y f) = in3Y f
    （定義的）・liftYZ(in2X f) = in3Y f / liftYZ(in2Y f) = in3Z f・
    liftYZ(Y) = Z
  - **座標の ps3Comp3 代入** X∘(W⃗) = W₁ / Y∘(W⃗) = W₂ / Z∘(W⃗) = W₃

  正直な範囲: 恒等代入系のみ定数項 0 を要求（打ち切り境界 1 の隅のため）、
  lift 系は全て仮定なし。選択公理不使用。
-/
import IUT.FormalGroupBridge
import IUT.FormalGroupMult3

namespace IUT

/-! ## 恒等代入と座標の ps23Comp 代入 -/

/-- **M70d-1a: 恒等代入の三変数版** X∘₃W = W（W₀₀₀ = 0）。 -/
theorem ps3Comp1_X (R : CRing) (W : PS3 R) (hW : W 0 0 0 = R.zero) :
    ps3Comp1 R (psX R) W = W := by
  funext j k i
  show rsum R (fun m => R.mul (psX R m)
      (psPow (psRing (psRing R)) W m j k i)) (i + k + j + 1) = W j k i
  cases Nat.lt_or_ge 1 (i + k + j + 1) with
  | inl h1 =>
    have hz : ∀ m, m < i + k + j + 1 → m ≠ 1 →
        (fun m => R.mul (psX R m)
          (psPow (psRing (psRing R)) W m j k i)) m = R.zero := by
      intro m _ hm
      show R.mul (psX R m) (psPow (psRing (psRing R)) W m j k i) = R.zero
      have hx : psX R m = R.zero := by
        show (if m = 1 then R.one else R.zero) = R.zero
        rw [if_neg hm]
      rw [hx, R.zero_mul]
    have hs := rsum_single R
      (fun m => R.mul (psX R m) (psPow (psRing (psRing R)) W m j k i))
      1 (i + k + j + 1) h1 hz
    rw [hs]
    show R.mul (psX R 1) (psPow (psRing (psRing R)) W 1 j k i) = W j k i
    rw [psPow_one (psRing (psRing R)) W]
    exact R.one_mul (W j k i)
  | inr h1 =>
    have hi : i = 0 := by omega
    have hk : k = 0 := by omega
    have hj : j = 0 := by omega
    subst hi; subst hk; subst hj
    show R.add R.zero (R.mul (psX R 0)
        (psPow (psRing (psRing R)) W 0 0 0 0)) = W 0 0 0
    rw [show psX R 0 = R.zero from rfl, R.zero_mul, R.zero_add]
    exact hW.symm

/-- **M70d-1b: 座標 X の代入** X(P,Q) = P（P₀₀₀ = 0）。 -/
theorem ps23Comp_X (R : CRing) (P Q : PS3 R) (hP : P 0 0 0 = R.zero) :
    ps23Comp R (ps2X R) P Q = P := by
  have h : ps2X R = psC (psRing R) (psX R) := rfl
  rw [h, ps23Comp_inX, ps3Comp1_X R P hP]

/-- **M70d-1c: 座標 Y の代入** Y(P,Q) = Q（Q₀₀₀ = 0）。 -/
theorem ps23Comp_Y (R : CRing) (P Q : PS3 R) (hQ : Q 0 0 0 = R.zero) :
    ps23Comp R (ps2Y R) P Q = Q := by
  have h : ps2Y R = psMap (psConstHom R) (psX R) :=
    (psMap_constHom_psX R).symm
  rw [h, ps23Comp_inY, ps3Comp1_X R Q hQ]

/-! ## lift の ps3Comp3 崩落 -/

/-- **M70d-2a: liftXY の崩落** —
    (liftXY G)∘(W₁,W₂,W₃) = G∘(W₁,W₂)（c-和が c = 0 に一点集中・
    W₃⁰ = 1。仮定なし）。 -/
theorem ps3Comp3_liftXY (R : CRing) (G : PS2 R) (W₁ W₂ W₃ : PS3 R) :
    ps3Comp3 R (liftXY R G) W₁ W₂ W₃ = ps23Comp R G W₁ W₂ := by
  funext j k i
  show rsum R (fun c => rsum R (fun b => rsum R (fun a =>
      R.mul (liftXY R G c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i))
      (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1)
    = rsum R (fun b => rsum R (fun a =>
        R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b)) j k i))
        (i + k + j + 1)) (i + k + j + 1)
  have hz : ∀ c, c < i + k + j + 1 → c ≠ 0 →
      (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul (liftXY R G c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i))
        (i + k + j + 1)) (i + k + j + 1)) c = R.zero := by
    intro c _ hc
    show rsum R (fun b => rsum R (fun a =>
        R.mul (liftXY R G c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i))
        (i + k + j + 1)) (i + k + j + 1) = R.zero
    have hcz : ∀ b a, liftXY R G c b a = R.zero := by
      intro b a
      show (if c = 0 then G else (psRing (psRing R)).zero) b a = R.zero
      rw [if_neg hc]
      rfl
    have h1 : rsum R (fun b => rsum R (fun a =>
        R.mul (liftXY R G c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i))
        (i + k + j + 1)) (i + k + j + 1)
        = rsum R (fun _ => R.zero) (i + k + j + 1) := by
      apply rsum_congr
      intro b _
      show rsum R (fun a =>
          R.mul (liftXY R G c b a)
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ c)) j k i))
          (i + k + j + 1) = R.zero
      have h2 : rsum R (fun a =>
          R.mul (liftXY R G c b a)
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ c)) j k i))
          (i + k + j + 1)
          = rsum R (fun _ => R.zero) (i + k + j + 1) := by
        apply rsum_congr
        intro a _
        show R.mul (liftXY R G c b a)
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ c)) j k i) = R.zero
        rw [hcz b a, R.zero_mul]
      rw [h2]
      exact rsum_const_zero R (i + k + j + 1)
    rw [h1]
    exact rsum_const_zero R (i + k + j + 1)
  have hs := rsum_single R (fun c => rsum R (fun b => rsum R (fun a =>
      R.mul (liftXY R G c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i))
      (i + k + j + 1)) (i + k + j + 1)) 0 (i + k + j + 1) (by omega) hz
  rw [hs]
  show rsum R (fun b => rsum R (fun a =>
      R.mul (liftXY R G 0 b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ 0)) j k i))
      (i + k + j + 1)) (i + k + j + 1)
    = rsum R (fun b => rsum R (fun a =>
        R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b)) j k i))
        (i + k + j + 1)) (i + k + j + 1)
  apply rsum_congr
  intro b _
  apply rsum_congr
  intro a _
  show R.mul (liftXY R G 0 b a)
      ((psMul (psRing (psRing R))
        (psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₁ a)
          (psPow (psRing (psRing R)) W₂ b))
        (psPow (psRing (psRing R)) W₃ 0)) j k i)
    = R.mul (G b a)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₁ a)
          (psPow (psRing (psRing R)) W₂ b)) j k i)
  have hone : psMul (psRing (psRing R))
      (psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) W₁ a)
        (psPow (psRing (psRing R)) W₂ b))
      (psPow (psRing (psRing R)) W₃ 0)
      = psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₁ a)
          (psPow (psRing (psRing R)) W₂ b) := by
    show (psRing (psRing (psRing R))).mul
        (psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₁ a)
          (psPow (psRing (psRing R)) W₂ b))
        (psRing (psRing (psRing R))).one
      = psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₁ a)
          (psPow (psRing (psRing R)) W₂ b)
    rw [(psRing (psRing (psRing R))).mul_comm]
    exact (psRing (psRing (psRing R))).one_mul _
  rw [hone]
  rfl

/-- **M70d-2b: liftYZ の崩落** —
    (liftYZ G)∘(W₁,W₂,W₃) = G∘(W₂,W₃)（a-和が a = 0 に一点集中・
    W₁⁰ = 1。仮定なし）。 -/
theorem ps3Comp3_liftYZ (R : CRing) (G : PS2 R) (W₁ W₂ W₃ : PS3 R) :
    ps3Comp3 R (liftYZ R G) W₁ W₂ W₃ = ps23Comp R G W₂ W₃ := by
  funext j k i
  show rsum R (fun c => rsum R (fun b => rsum R (fun a =>
      R.mul (liftYZ R G c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i))
      (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1)
    = rsum R (fun b => rsum R (fun a =>
        R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₂ a)
            (psPow (psRing (psRing R)) W₃ b)) j k i))
        (i + k + j + 1)) (i + k + j + 1)
  apply rsum_congr
  intro c _
  show rsum R (fun b => rsum R (fun a =>
      R.mul (liftYZ R G c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i))
      (i + k + j + 1)) (i + k + j + 1)
    = rsum R (fun a =>
        R.mul (G c a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₂ a)
            (psPow (psRing (psRing R)) W₃ c)) j k i))
        (i + k + j + 1)
  apply rsum_congr
  intro b _
  show rsum R (fun a =>
      R.mul (liftYZ R G c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i))
      (i + k + j + 1)
    = R.mul (G c b)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₂ b)
          (psPow (psRing (psRing R)) W₃ c)) j k i)
  have hz : ∀ a, a < i + k + j + 1 → a ≠ 0 →
      (fun a => R.mul (liftYZ R G c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i)) a = R.zero := by
    intro a _ ha
    show R.mul (liftYZ R G c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i) = R.zero
    have h0 : liftYZ R G c b a = R.zero := by
      show (if a = 0 then G c b else R.zero) = R.zero
      rw [if_neg ha]
    rw [h0, R.zero_mul]
  have hs := rsum_single R
    (fun a => R.mul (liftYZ R G c b a)
      ((psMul (psRing (psRing R))
        (psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₁ a)
          (psPow (psRing (psRing R)) W₂ b))
        (psPow (psRing (psRing R)) W₃ c)) j k i))
    0 (i + k + j + 1) (by omega) hz
  rw [hs]
  show R.mul (liftYZ R G c b 0)
      ((psMul (psRing (psRing R))
        (psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₁ 0)
          (psPow (psRing (psRing R)) W₂ b))
        (psPow (psRing (psRing R)) W₃ c)) j k i)
    = R.mul (G c b)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₂ b)
          (psPow (psRing (psRing R)) W₃ c)) j k i)
  have hone : psMul (psRing (psRing R))
      (psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) W₁ 0)
        (psPow (psRing (psRing R)) W₂ b))
      (psPow (psRing (psRing R)) W₃ c)
      = psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₂ b)
          (psPow (psRing (psRing R)) W₃ c) := by
    have h1 : psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) W₁ 0)
        (psPow (psRing (psRing R)) W₂ b)
        = psPow (psRing (psRing R)) W₂ b := by
      show (psRing (psRing (psRing R))).mul
          (psRing (psRing (psRing R))).one
          (psPow (psRing (psRing R)) W₂ b)
        = psPow (psRing (psRing R)) W₂ b
      exact (psRing (psRing (psRing R))).one_mul _
    rw [h1]
  rw [hone]
  rfl

/-! ## lift と ps2Comp2 の交換 -/

/-- **M70d-3a: liftXY と ps2Comp2 の交換** —
    liftXY(G∘₂(U,V)) = G∘(liftXY U, liftXY V)（仮定なし）。 -/
theorem liftXY_comp2 (R : CRing) (G U V : PS2 R) :
    liftXY R (ps2Comp2 R G U V)
      = ps23Comp R G (liftXY R U) (liftXY R V) := by
  funext j k i
  cases Nat.decEq j 0 with
  | isTrue hj =>
    subst hj
    show rsum R (fun b => rsum R (fun a => R.mul (G b a)
        ((psMul (psRing R) (psPow (psRing R) U a)
          (psPow (psRing R) V b)) k i))
        (i + k + 1)) (i + k + 1)
      = rsum R (fun b => rsum R (fun a => R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (liftXY R U) a)
            (psPow (psRing (psRing R)) (liftXY R V) b)) 0 k i))
          (i + k + 1)) (i + k + 1)
    apply rsum_congr
    intro b _
    apply rsum_congr
    intro a _
    show R.mul (G b a)
        ((psMul (psRing R) (psPow (psRing R) U a)
          (psPow (psRing R) V b)) k i)
      = R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (liftXY R U) a)
            (psPow (psRing (psRing R)) (liftXY R V) b)) 0 k i)
    have hlift : psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) (liftXY R U) a)
        (psPow (psRing (psRing R)) (liftXY R V) b)
        = liftXY R (psMul (psRing R)
            (psPow (psRing R) U a) (psPow (psRing R) V b)) := by
      rw [liftXY_pow R U a, liftXY_pow R V b, ← liftXY_mul]
    rw [hlift]
    rfl
  | isFalse hj =>
    have hL : liftXY R (ps2Comp2 R G U V) j k i = R.zero := by
      show (if j = 0 then ps2Comp2 R G U V
          else (psRing (psRing R)).zero) k i = R.zero
      rw [if_neg hj]
      rfl
    have hR : ps23Comp R G (liftXY R U) (liftXY R V) j k i = R.zero := by
      show rsum R (fun b => rsum R (fun a => R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (liftXY R U) a)
            (psPow (psRing (psRing R)) (liftXY R V) b)) j k i))
          (i + k + j + 1)) (i + k + j + 1) = R.zero
      have h1 : rsum R (fun b => rsum R (fun a => R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (liftXY R U) a)
            (psPow (psRing (psRing R)) (liftXY R V) b)) j k i))
          (i + k + j + 1)) (i + k + j + 1)
          = rsum R (fun _ => R.zero) (i + k + j + 1) := by
        apply rsum_congr
        intro b _
        show rsum R (fun a => R.mul (G b a)
            ((psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) (liftXY R U) a)
              (psPow (psRing (psRing R)) (liftXY R V) b)) j k i))
            (i + k + j + 1) = R.zero
        have h2 : rsum R (fun a => R.mul (G b a)
            ((psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) (liftXY R U) a)
              (psPow (psRing (psRing R)) (liftXY R V) b)) j k i))
            (i + k + j + 1)
            = rsum R (fun _ => R.zero) (i + k + j + 1) := by
          apply rsum_congr
          intro a _
          show R.mul (G b a)
              ((psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) (liftXY R U) a)
                (psPow (psRing (psRing R)) (liftXY R V) b)) j k i) = R.zero
          have h3 : (psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) (liftXY R U) a)
              (psPow (psRing (psRing R)) (liftXY R V) b)) j k i = R.zero := by
            rw [liftXY_pow R U a, liftXY_pow R V b, ← liftXY_mul]
            show (if j = 0 then psMul (psRing R)
                (psPow (psRing R) U a) (psPow (psRing R) V b)
              else (psRing (psRing R)).zero) k i = R.zero
            rw [if_neg hj]
            rfl
          rw [h3, R.mul_zero]
        rw [h2]
        exact rsum_const_zero R (i + k + j + 1)
      rw [h1]
      exact rsum_const_zero R (i + k + j + 1)
    rw [hL, hR]

/-- **M70d-3b: liftYZ と ps2Comp2 の交換** —
    liftYZ(G∘₂(U,V)) = G∘(liftYZ U, liftYZ V)（仮定なし）。 -/
theorem liftYZ_comp2 (R : CRing) (G U V : PS2 R) :
    liftYZ R (ps2Comp2 R G U V)
      = ps23Comp R G (liftYZ R U) (liftYZ R V) := by
  funext j k i
  cases Nat.decEq i 0 with
  | isTrue hi =>
    subst hi
    show rsum R (fun b => rsum R (fun a => R.mul (G b a)
        ((psMul (psRing R) (psPow (psRing R) U a)
          (psPow (psRing R) V b)) j k))
        (k + j + 1)) (k + j + 1)
      = rsum R (fun b => rsum R (fun a => R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (liftYZ R U) a)
            (psPow (psRing (psRing R)) (liftYZ R V) b)) j k 0))
          (0 + k + j + 1)) (0 + k + j + 1)
    rw [Nat.zero_add k]
    apply rsum_congr
    intro b _
    apply rsum_congr
    intro a _
    show R.mul (G b a)
        ((psMul (psRing R) (psPow (psRing R) U a)
          (psPow (psRing R) V b)) j k)
      = R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (liftYZ R U) a)
            (psPow (psRing (psRing R)) (liftYZ R V) b)) j k 0)
    have hlift : psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) (liftYZ R U) a)
        (psPow (psRing (psRing R)) (liftYZ R V) b)
        = liftYZ R (psMul (psRing R)
            (psPow (psRing R) U a) (psPow (psRing R) V b)) := by
      rw [liftYZ_pow R U a, liftYZ_pow R V b, ← liftYZ_mul]
    rw [hlift]
    rfl
  | isFalse hi =>
    have hL : liftYZ R (ps2Comp2 R G U V) j k i = R.zero := by
      show (if i = 0 then ps2Comp2 R G U V j k else R.zero) = R.zero
      rw [if_neg hi]
    have hR : ps23Comp R G (liftYZ R U) (liftYZ R V) j k i = R.zero := by
      show rsum R (fun b => rsum R (fun a => R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (liftYZ R U) a)
            (psPow (psRing (psRing R)) (liftYZ R V) b)) j k i))
          (i + k + j + 1)) (i + k + j + 1) = R.zero
      have h1 : rsum R (fun b => rsum R (fun a => R.mul (G b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (liftYZ R U) a)
            (psPow (psRing (psRing R)) (liftYZ R V) b)) j k i))
          (i + k + j + 1)) (i + k + j + 1)
          = rsum R (fun _ => R.zero) (i + k + j + 1) := by
        apply rsum_congr
        intro b _
        show rsum R (fun a => R.mul (G b a)
            ((psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) (liftYZ R U) a)
              (psPow (psRing (psRing R)) (liftYZ R V) b)) j k i))
            (i + k + j + 1) = R.zero
        have h2 : rsum R (fun a => R.mul (G b a)
            ((psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) (liftYZ R U) a)
              (psPow (psRing (psRing R)) (liftYZ R V) b)) j k i))
            (i + k + j + 1)
            = rsum R (fun _ => R.zero) (i + k + j + 1) := by
          apply rsum_congr
          intro a _
          show R.mul (G b a)
              ((psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) (liftYZ R U) a)
                (psPow (psRing (psRing R)) (liftYZ R V) b)) j k i) = R.zero
          have h3 : (psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) (liftYZ R U) a)
              (psPow (psRing (psRing R)) (liftYZ R V) b)) j k i = R.zero := by
            rw [liftYZ_pow R U a, liftYZ_pow R V b, ← liftYZ_mul]
            show (if i = 0 then (psMul (psRing R)
                (psPow (psRing R) U a) (psPow (psRing R) V b)) j k
              else R.zero) = R.zero
            rw [if_neg hi]
          rw [h3, R.mul_zero]
        rw [h2]
        exact rsum_const_zero R (i + k + j + 1)
      rw [h1]
      exact rsum_const_zero R (i + k + j + 1)
    rw [hL, hR]

/-! ## lift は注入を注入へ -/

/-- **M70d-4a**: liftXY(in2X f) = in3X f（定義的）。 -/
theorem liftXY_in2X (R : CRing) (f : PS R) :
    liftXY R (psC (psRing R) f) = in3X R f := rfl

/-- **M70d-4b**: liftXY(in2Y f) = in3Y f（定義的）。 -/
theorem liftXY_in2Y (R : CRing) (f : PS R) :
    liftXY R (psMap (psConstHom R) f) = in3Y R f := rfl

/-- **M70d-4c**: liftYZ(in2X f) = in3Y f（X 方向は Y 方向へ）。 -/
theorem liftYZ_in2X (R : CRing) (f : PS R) :
    liftYZ R (psC (psRing R) f) = in3Y R f := by
  funext c
  show psMap (psConstHom R) (if c = 0 then f else (psRing R).zero)
    = (if c = 0 then psMap (psConstHom R) f else (psRing (psRing R)).zero)
  cases Nat.decEq c 0 with
  | isTrue hc =>
    rw [if_pos hc, if_pos hc]
  | isFalse hc =>
    rw [if_neg hc, if_neg hc]
    funext n
    exact (psConstHom R).map_zero

/-- 補助: psMap は定数項埋め込みと交換（psMap φ (psC r) = psC (φ r)）。 -/
theorem psMap_psC {R S : CRing} (φ : RingHom R S) (r : R.carrier) :
    psMap φ (psC R r) = psC S (φ.map r) := by
  funext n
  show φ.map (if n = 0 then r else R.zero)
    = (if n = 0 then φ.map r else S.zero)
  cases Nat.decEq n 0 with
  | isTrue hn => rw [if_pos hn, if_pos hn]
  | isFalse hn =>
    rw [if_neg hn, if_neg hn]
    exact φ.map_zero

/-- **M70d-4d**: liftYZ(in2Y f) = in3Z f（Y 方向は Z 方向へ）。 -/
theorem liftYZ_in2Y (R : CRing) (f : PS R) :
    liftYZ R (psMap (psConstHom R) f) = in3Z R f := by
  funext c
  show psMap (psConstHom R) (psC R (f c))
    = psC (psRing R) (psC R (f c))
  rw [psMap_psC (psConstHom R) (f c)]
  rfl

/-- **M70d-4e**: liftYZ(Y) = Z（座標 Y は座標 Z へ）。 -/
theorem liftYZ_ps2Y (R : CRing) : liftYZ R (ps2Y R) = ps3Z R := by
  funext c
  show psMap (psConstHom R)
      (if c = 1 then (psRing R).one else (psRing R).zero)
    = (if c = 1 then (psRing (psRing R)).one else (psRing (psRing R)).zero)
  cases Nat.decEq c 1 with
  | isTrue hc =>
    rw [if_pos hc, if_pos hc]
    exact (psRingHom (psConstHom R)).map_one
  | isFalse hc =>
    rw [if_neg hc, if_neg hc]
    exact RingHom.map_zero (psRingHom (psConstHom R))

/-! ## 座標の ps3Comp3 代入 -/

/-- **M70d-5a**: X∘(W₁,W₂,W₃) = W₁（W₁の定数項 0）。 -/
theorem ps3Comp3_ps3X (R : CRing) (W₁ W₂ W₃ : PS3 R)
    (hW₁ : W₁ 0 0 0 = R.zero) :
    ps3Comp3 R (ps3X R) W₁ W₂ W₃ = W₁ := by
  have h : ps3X R = liftXY R (ps2X R) := rfl
  rw [h, ps3Comp3_liftXY, ps23Comp_X R W₁ W₂ hW₁]

/-- **M70d-5b**: Y∘(W₁,W₂,W₃) = W₂（W₂の定数項 0）。 -/
theorem ps3Comp3_ps3Y (R : CRing) (W₁ W₂ W₃ : PS3 R)
    (hW₂ : W₂ 0 0 0 = R.zero) :
    ps3Comp3 R (ps3Y R) W₁ W₂ W₃ = W₂ := by
  have h : ps3Y R = liftXY R (ps2Y R) := rfl
  rw [h, ps3Comp3_liftXY, ps23Comp_Y R W₁ W₂ hW₂]

/-- **M70d-5c**: Z∘(W₁,W₂,W₃) = W₃（W₃の定数項 0）。 -/
theorem ps3Comp3_ps3Z (R : CRing) (W₁ W₂ W₃ : PS3 R)
    (hW₃ : W₃ 0 0 0 = R.zero) :
    ps3Comp3 R (ps3Z R) W₁ W₂ W₃ = W₃ := by
  rw [← liftYZ_ps2Y R, ps3Comp3_liftYZ, ps23Comp_Y R W₂ W₃ hW₃]

end IUT
