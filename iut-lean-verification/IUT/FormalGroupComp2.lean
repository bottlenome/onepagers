/-
  IUT/FormalGroupComp2.lean — M70b（連鎖律 CR2: 結合則キャンペーン第十層）

  第二の連鎖律

    **(F(U,V))∘(P,Q) = F(U∘(P,Q), V∘(P,Q))**   （CR2）

  すなわち ps23Comp (ps2Comp2 F U V) P Q
         = ps23Comp F (ps23Comp U P Q) (ps23Comp V P Q)
  （U₀₀ = V₀₀ = 0・P₀₀₀ = Q₀₀₀ = 0）を完全証明する。
  結合則の方程式検証で「F の方程式を適用した後の二変数代入」を
  三変数の代入に押し出す柱。

  戦略: 係数 (j,k,i)・N := i+k+j+1 を固定し、両辺を共通の四重和

    Σ_{b<N}Σ_{a<N}Σ_{b₁<N}Σ_{a₁<N} F_{b₁a₁}·((U^{a₁}V^{b₁})_{b,a}·T(a,b))

  に落とす（T(a,b) := (P^aQ^b)_{j,k,i}）。
  * 左辺: ps2Comp2 の内側境界 a+b+1 を N へ padding（`ps2Comp2_pad`、
    二変数冪積の下方消滅 M70a）+ rsum_mul_right ×2 + 結合律。
    高総次数 (a+b > n) のスロットは T = 0 で両形とも消滅
  * 右辺: 族和表示（eq_fam）+ **冪の代入・乗法性による融合**
    (P'^{a₁}Q'^{b₁}) = (U^{a₁}V^{b₁})∘(P,Q)（M69b/M70a）+ 再び
    eq_fam + rsum_mul_left ×2 → 四重和、添字交換 ×4 で整列

  全て選択公理不使用。
-/
import IUT.FormalGroupComp1

namespace IUT

/-! ## ps2Comp2 の境界 padding -/

/-- **M70b-1: ps2Comp2 の境界 padding** — U₀₀ = V₀₀ = 0 のとき、
    係数 (b,a)（a+b < N）で内側境界 a+b+1 を N に広げられる
    （超過項は二変数冪積の下方消滅で 0）。 -/
theorem ps2Comp2_pad (R : CRing) (F U V : PS2 R)
    (hU : U 0 0 = R.zero) (hV : V 0 0 = R.zero)
    (N b a : Nat) (hN : a + b < N) :
    ps2Comp2 R F U V b a
      = rsum R (fun b₁ => rsum R (fun a₁ =>
          R.mul (F b₁ a₁)
            ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)) N) N := by
  show rsum R (fun b₁ => rsum R (fun a₁ =>
      R.mul (F b₁ a₁)
        ((psMul (psRing R) (psPow (psRing R) U a₁)
          (psPow (psRing R) V b₁)) b a)) (a + b + 1)) (a + b + 1) = _
  have hinner : ∀ b₁, rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          ((psMul (psRing R) (psPow (psRing R) U a₁)
            (psPow (psRing R) V b₁)) b a)) N
      = rsum R (fun a₁ =>
          R.mul (F b₁ a₁)
            ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)) (a + b + 1) :=
    fun b₁ => rsum_pad R _ (by omega) (fun a₁ ha₁ => by
      rw [ps2PowPow_low R U V hU hV a₁ b₁ b a (by omega)]
      exact R.mul_zero _)
  have houter : rsum R (fun b₁ => rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          ((psMul (psRing R) (psPow (psRing R) U a₁)
            (psPow (psRing R) V b₁)) b a)) N) N
      = rsum R (fun b₁ => rsum R (fun a₁ =>
          R.mul (F b₁ a₁)
            ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)) N) (a + b + 1) :=
    rsum_pad R _ (by omega) (fun b₁ hb₁ => by
      have hz : rsum R (fun a₁ =>
            R.mul (F b₁ a₁)
              ((psMul (psRing R) (psPow (psRing R) U a₁)
                (psPow (psRing R) V b₁)) b a)) N
          = rsum R (fun _ => R.zero) N :=
        rsum_congr R N (fun a₁ _ => by
          rw [ps2PowPow_low R U V hU hV a₁ b₁ b a (by omega)]
          exact R.mul_zero _)
      show rsum R (fun a₁ =>
          R.mul (F b₁ a₁)
            ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)) N = R.zero
      rw [hz]
      exact rsum_const_zero R N)
  rw [houter]
  exact rsum_congr R (a + b + 1) (fun b₁ _ => (hinner b₁).symm)

/-! ## 連鎖律 CR2 -/

/-- **定理 (M70b-2): 連鎖律 CR2** —
    (F(U,V))∘(P,Q) = F(U∘(P,Q), V∘(P,Q))
    （U₀₀ = V₀₀ = 0・P₀₀₀ = Q₀₀₀ = 0）。 -/
theorem ps23Comp_comp2 (R : CRing) (F U V : PS2 R) (P Q : PS3 R)
    (hU : U 0 0 = R.zero) (hV : V 0 0 = R.zero)
    (hP : P 0 0 0 = R.zero) (hQ : Q 0 0 0 = R.zero) :
    ps23Comp R (ps2Comp2 R F U V) P Q
      = ps23Comp R F (ps23Comp R U P Q) (ps23Comp R V P Q) := by
  funext j k i
  -- 共通形 Z: Σ_b Σ_a Σ_{b₁} Σ_{a₁} F_{b₁a₁}·((U^{a₁}V^{b₁})_{ba}·T(a,b))
  -- 左辺 → Z
  have hZL : ps23Comp R (ps2Comp2 R F U V) P Q j k i
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ =>
            R.mul (F b₁ a₁)
              (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                  (psPow (psRing R) V b₁)) b a)
                ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                  (psPow (psRing (psRing R)) Q b)) j k i)))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1) := by
    show rsum R (fun b => rsum R (fun a =>
        R.mul (ps2Comp2 R F U V b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i))
        (i + k + j + 1)) (i + k + j + 1) = _
    refine rsum_congr R (i + k + j + 1) (fun b hb => ?_)
    refine rsum_congr R (i + k + j + 1) (fun a ha => ?_)
    cases Nat.lt_or_ge (i + k + j) (a + b) with
    | inl hhigh =>
      rw [ps3PowPow_low R P Q hP hQ a b j k i hhigh,
        R.mul_zero (ps2Comp2 R F U V b a)]
      have hz : rsum R (fun b₁ => rsum R (fun a₁ =>
            R.mul (F b₁ a₁)
              (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                  (psPow (psRing R) V b₁)) b a) R.zero))
            (i + k + j + 1)) (i + k + j + 1)
          = rsum R (fun _ => R.zero) (i + k + j + 1) :=
        rsum_congr R (i + k + j + 1) (fun b₁ _ => by
          have hz2 : rsum R (fun a₁ =>
                R.mul (F b₁ a₁)
                  (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                      (psPow (psRing R) V b₁)) b a) R.zero))
                (i + k + j + 1)
              = rsum R (fun _ => R.zero) (i + k + j + 1) :=
            rsum_congr R (i + k + j + 1) (fun a₁ _ => by
              rw [R.mul_zero ((psMul (psRing R) (psPow (psRing R) U a₁)
                  (psPow (psRing R) V b₁)) b a),
                R.mul_zero (F b₁ a₁)])
          rw [hz2]
          exact rsum_const_zero R (i + k + j + 1))
      rw [hz, rsum_const_zero]
    | inr hlow =>
      rw [ps2Comp2_pad R F U V hU hV (i + k + j + 1) b a (by omega),
        rsum_mul_right R _ ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i) (i + k + j + 1)]
      refine rsum_congr R (i + k + j + 1) (fun b₁ _ => ?_)
      rw [rsum_mul_right R _ ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i) (i + k + j + 1)]
      exact rsum_congr R (i + k + j + 1) (fun a₁ _ =>
        R.mul_assoc (F b₁ a₁) _ _)
  -- 右辺 → Z'（添字順 (b₁,a₁,b,a)）
  have hZR : ps23Comp R F (ps23Comp R U P Q) (ps23Comp R V P Q) j k i
      = rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun b =>
          rsum R (fun a =>
            R.mul (F b₁ a₁)
              (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                  (psPow (psRing R) V b₁)) b a)
                ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                  (psPow (psRing (psRing R)) Q b)) j k i)))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1) := by
    show rsum R (fun b₁ => rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (ps23Comp R U P Q) a₁)
            (psPow (psRing (psRing R)) (ps23Comp R V P Q) b₁)) j k i))
        (i + k + j + 1)) (i + k + j + 1) = _
    refine rsum_congr R (i + k + j + 1) (fun b₁ _ => ?_)
    refine rsum_congr R (i + k + j + 1) (fun a₁ _ => ?_)
    rw [ps23Comp_pow R U P Q hP hQ a₁, ps23Comp_pow R V P Q hP hQ b₁,
      ← ps23Comp_mul R (psPow (psRing R) U a₁) (psPow (psRing R) V b₁)
        P Q hP hQ,
      ps23Comp_eq_fam R (psMul (psRing R) (psPow (psRing R) U a₁)
        (psPow (psRing R) V b₁)) P Q hP hQ (i + k + j + 1) j k i
        (by omega)]
    show R.mul (F b₁ a₁) (rsum R (fun b => rsum R (fun a =>
        R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
            (psPow (psRing R) V b₁)) b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i))
        (i + k + j + 1)) (i + k + j + 1)) = _
    rw [rsum_mul_left R _ (F b₁ a₁) (i + k + j + 1)]
    refine rsum_congr R (i + k + j + 1) (fun b _ => ?_)
    rw [rsum_mul_left R _ (F b₁ a₁) (i + k + j + 1)]
  rw [hZL, hZR]
  -- 添字交換 (b₁,a₁,b,a) → (b,a,b₁,a₁)
  have e1 : rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun b =>
        rsum R (fun a => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
        (i + k + j + 1)
      = rsum R (fun b₁ => rsum R (fun b => rsum R (fun a₁ =>
          rsum R (fun a => R.mul (F b₁ a₁)
            (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                (psPow (psRing R) V b₁)) b a)
              ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                (psPow (psRing (psRing R)) Q b)) j k i)))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1) :=
    rsum_congr R (i + k + j + 1) (fun b₁ _ =>
      rsum_exchange R (fun a₁ b => rsum R (fun a => R.mul (F b₁ a₁)
        (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
            (psPow (psRing R) V b₁)) b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)))
        (i + k + j + 1)) (i + k + j + 1) (i + k + j + 1))
  have e2 : rsum R (fun b₁ => rsum R (fun b => rsum R (fun a₁ =>
        rsum R (fun a => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
        (i + k + j + 1)
      = rsum R (fun b => rsum R (fun b₁ => rsum R (fun a₁ =>
          rsum R (fun a => R.mul (F b₁ a₁)
            (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                (psPow (psRing R) V b₁)) b a)
              ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                (psPow (psRing (psRing R)) Q b)) j k i)))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1) :=
    rsum_exchange R (fun b₁ b => rsum R (fun a₁ =>
        rsum R (fun a => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1)
        (i + k + j + 1)
  have e3 : rsum R (fun b => rsum R (fun b₁ => rsum R (fun a₁ =>
        rsum R (fun a => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
        (i + k + j + 1)
      = rsum R (fun b => rsum R (fun b₁ => rsum R (fun a =>
          rsum R (fun a₁ => R.mul (F b₁ a₁)
            (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                (psPow (psRing R) V b₁)) b a)
              ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                (psPow (psRing (psRing R)) Q b)) j k i)))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1) :=
    rsum_congr R (i + k + j + 1) (fun b _ =>
      rsum_congr R (i + k + j + 1) (fun b₁ _ =>
        rsum_exchange R (fun a₁ a => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)))
          (i + k + j + 1) (i + k + j + 1)))
  have e4 : rsum R (fun b => rsum R (fun b₁ => rsum R (fun a =>
        rsum R (fun a₁ => R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
        (i + k + j + 1)
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ => R.mul (F b₁ a₁)
            (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
                (psPow (psRing R) V b₁)) b a)
              ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                (psPow (psRing (psRing R)) Q b)) j k i)))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1) :=
    rsum_congr R (i + k + j + 1) (fun b _ =>
      rsum_exchange R (fun b₁ a => rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          (R.mul ((psMul (psRing R) (psPow (psRing R) U a₁)
              (psPow (psRing R) V b₁)) b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)))
        (i + k + j + 1)) (i + k + j + 1) (i + k + j + 1))
  rw [e1, e2, e3, e4]

end IUT
