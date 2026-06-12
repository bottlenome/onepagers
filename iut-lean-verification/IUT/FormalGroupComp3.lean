/-
  IUT/FormalGroupComp3.lean — M70e（連鎖律 CR3: 結合則キャンペーン第十三層）

  第三の連鎖律

    **(F(P,Q))∘(W₁,W₂,W₃) = F(P∘W⃗, Q∘W⃗)**   （CR3）

  すなわち ps3Comp3 (ps23Comp F P Q) W₁ W₂ W₃
         = ps23Comp F (ps3Comp3 P W⃗) (ps3Comp3 Q W⃗)
  （P₀₀₀ = Q₀₀₀ = 0・W₁₀₀₀ = W₂₀₀₀ = W₃₀₀₀ = 0）を完全証明する。
  結合則の方程式検証の右辺（A(f⃗) の分解）を担う最後の連鎖律。

  戦略は CR2（M70b）の精密ミラー: 係数 (j,k,i)・N := i+k+j+1 を固定し、
  両辺を共通の五重和

    Σ_c Σ_b Σ_a Σ_{b₁} Σ_{a₁} F_{b₁a₁}·((P^{a₁}Q^{b₁})_{c,b,a}·T₃(a,b,c))

  に落とす（T₃(a,b,c) := ((W₁^a·W₂^b)·W₃^c)_{j,k,i}）。
  * 左辺: ps23Comp の内側境界 a+b+c+1 を N へ padding（`ps23Comp_pad3`、
    三変数冪積の下方消滅 M68）+ rsum_mul_right ×2 + 結合律。
    高総次数 (a+b+c > n) のスロットは T₃ = 0（M70F の三重下方消滅）で
    両形とも消滅
  * 右辺: 冪の代入・乗法性による融合（M70F）
    (P'^{a₁}Q'^{b₁}) = (P^{a₁}Q^{b₁})∘W⃗ + 打ち切り安定性（M70F の
    eq_fam）+ rsum_mul_left ×3 → 五重和（添字順 b₁,a₁,c,b,a）
  * 接合: 抽象五重和の並べ替え `quint_reorder`（rsum_exchange ×6）

  全て選択公理不使用。
-/
import IUT.FormalGroupMult3

namespace IUT

/-! ## ps23Comp の境界 padding（三変数係数版） -/

/-- **M70e-1: ps23Comp の境界 padding** — P₀₀₀ = Q₀₀₀ = 0 のとき、
    係数 (c,b,a)（a+b+c < N）で内側境界 a+b+c+1 を N に広げられる
    （超過項は三変数冪積の下方消滅で 0）。 -/
theorem ps23Comp_pad3 (R : CRing) (F : PS2 R) (P Q : PS3 R)
    (hP : P 0 0 0 = R.zero) (hQ : Q 0 0 0 = R.zero)
    (N c b a : Nat) (hN : a + b + c < N) :
    ps23Comp R F P Q c b a
      = rsum R (fun b₁ => rsum R (fun a₁ =>
          R.mul (F b₁ a₁)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
              (psPow (psRing (psRing R)) Q b₁)) c b a)) N) N := by
  show rsum R (fun b₁ => rsum R (fun a₁ =>
      R.mul (F b₁ a₁)
        ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
          (psPow (psRing (psRing R)) Q b₁)) c b a))
      (a + b + c + 1)) (a + b + c + 1) = _
  have hinner : ∀ b₁, rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
            (psPow (psRing (psRing R)) Q b₁)) c b a)) N
      = rsum R (fun a₁ =>
          R.mul (F b₁ a₁)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
              (psPow (psRing (psRing R)) Q b₁)) c b a)) (a + b + c + 1) :=
    fun b₁ => rsum_pad R _ (by omega) (fun a₁ ha₁ => by
      rw [ps3PowPow_low R P Q hP hQ a₁ b₁ c b a (by omega)]
      exact R.mul_zero _)
  have houter : rsum R (fun b₁ => rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
            (psPow (psRing (psRing R)) Q b₁)) c b a)) N) N
      = rsum R (fun b₁ => rsum R (fun a₁ =>
          R.mul (F b₁ a₁)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
              (psPow (psRing (psRing R)) Q b₁)) c b a)) N) (a + b + c + 1) :=
    rsum_pad R _ (by omega) (fun b₁ hb₁ => by
      have hz : rsum R (fun a₁ =>
            R.mul (F b₁ a₁)
              ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
                (psPow (psRing (psRing R)) Q b₁)) c b a)) N
          = rsum R (fun _ => R.zero) N :=
        rsum_congr R N (fun a₁ _ => by
          rw [ps3PowPow_low R P Q hP hQ a₁ b₁ c b a (by omega)]
          exact R.mul_zero _)
      show rsum R (fun a₁ =>
          R.mul (F b₁ a₁)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
              (psPow (psRing (psRing R)) Q b₁)) c b a)) N = R.zero
      rw [hz]
      exact rsum_const_zero R N)
  rw [houter]
  exact rsum_congr R (a + b + c + 1) (fun b₁ _ => (hinner b₁).symm)

/-! ## 抽象五重和の並べ替え -/

/-- **M70e-2: 五重和の並べ替え** — 固定境界 N の五重和で
    (b₁,a₁,c,b,a) → (c,b,a,b₁,a₁)（rsum_exchange ×6・条件なし）。 -/
theorem quint_reorder (R : CRing)
    (φ : Nat → Nat → Nat → Nat → Nat → R.carrier) (N : Nat) :
    rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun c => rsum R (fun b =>
        rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N) N
      = rsum R (fun c => rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ => φ b₁ a₁ c b a) N) N) N) N) N := by
  have e1 : rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun c =>
        rsum R (fun b => rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N) N
      = rsum R (fun b₁ => rsum R (fun c => rsum R (fun a₁ =>
          rsum R (fun b => rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N) N :=
    rsum_congr R N (fun b₁ _ =>
      rsum_exchange R (fun a₁ c =>
        rsum R (fun b => rsum R (fun a => φ b₁ a₁ c b a) N) N) N N)
  have e2 : rsum R (fun b₁ => rsum R (fun c => rsum R (fun a₁ =>
        rsum R (fun b => rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N) N
      = rsum R (fun c => rsum R (fun b₁ => rsum R (fun a₁ =>
          rsum R (fun b => rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N) N :=
    rsum_exchange R (fun b₁ c => rsum R (fun a₁ =>
      rsum R (fun b => rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N N
  have e3 : rsum R (fun c => rsum R (fun b₁ => rsum R (fun a₁ =>
        rsum R (fun b => rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N) N
      = rsum R (fun c => rsum R (fun b₁ => rsum R (fun b =>
          rsum R (fun a₁ => rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N) N :=
    rsum_congr R N (fun c _ =>
      rsum_congr R N (fun b₁ _ =>
        rsum_exchange R (fun a₁ b =>
          rsum R (fun a => φ b₁ a₁ c b a) N) N N))
  have e4 : rsum R (fun c => rsum R (fun b₁ => rsum R (fun b =>
        rsum R (fun a₁ => rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N) N
      = rsum R (fun c => rsum R (fun b => rsum R (fun b₁ =>
          rsum R (fun a₁ => rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N) N :=
    rsum_congr R N (fun c _ =>
      rsum_exchange R (fun b₁ b => rsum R (fun a₁ =>
        rsum R (fun a => φ b₁ a₁ c b a) N) N) N N)
  have e5 : rsum R (fun c => rsum R (fun b => rsum R (fun b₁ =>
        rsum R (fun a₁ => rsum R (fun a => φ b₁ a₁ c b a) N) N) N) N) N
      = rsum R (fun c => rsum R (fun b => rsum R (fun b₁ =>
          rsum R (fun a => rsum R (fun a₁ => φ b₁ a₁ c b a) N) N) N) N) N :=
    rsum_congr R N (fun c _ =>
      rsum_congr R N (fun b _ =>
        rsum_congr R N (fun b₁ _ =>
          rsum_exchange R (fun a₁ a => φ b₁ a₁ c b a) N N)))
  have e6 : rsum R (fun c => rsum R (fun b => rsum R (fun b₁ =>
        rsum R (fun a => rsum R (fun a₁ => φ b₁ a₁ c b a) N) N) N) N) N
      = rsum R (fun c => rsum R (fun b => rsum R (fun a =>
          rsum R (fun b₁ => rsum R (fun a₁ => φ b₁ a₁ c b a) N) N) N) N) N :=
    rsum_congr R N (fun c _ =>
      rsum_congr R N (fun b _ =>
        rsum_exchange R (fun b₁ a =>
          rsum R (fun a₁ => φ b₁ a₁ c b a) N) N N))
  rw [e1, e2, e3, e4, e5, e6]

/-! ## 連鎖律 CR3 -/

/-- **定理 (M70e-3): 連鎖律 CR3** —
    (F(P,Q))∘(W₁,W₂,W₃) = F(P∘W⃗, Q∘W⃗)
    （P₀₀₀ = Q₀₀₀ = 0・W₁₀₀₀ = W₂₀₀₀ = W₃₀₀₀ = 0）。 -/
theorem ps3Comp3_comp23 (R : CRing) (F : PS2 R) (P Q W₁ W₂ W₃ : PS3 R)
    (hP : P 0 0 0 = R.zero) (hQ : Q 0 0 0 = R.zero)
    (hW₁ : W₁ 0 0 0 = R.zero) (hW₂ : W₂ 0 0 0 = R.zero)
    (hW₃ : W₃ 0 0 0 = R.zero) :
    ps3Comp3 R (ps23Comp R F P Q) W₁ W₂ W₃
      = ps23Comp R F (ps3Comp3 R P W₁ W₂ W₃) (ps3Comp3 R Q W₁ W₂ W₃) := by
  funext j k i
  -- 共通形 Z: Σ_c Σ_b Σ_a Σ_{b₁} Σ_{a₁} F_{b₁a₁}·((P^{a₁}Q^{b₁})_{cba}·T₃(a,b,c))
  -- 左辺 → Z
  have hZL : ps3Comp3 R (ps23Comp R F P Q) W₁ W₂ W₃ j k i
      = rsum R (fun c => rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ =>
            R.mul (F b₁ a₁)
              (R.mul ((psMul (psRing (psRing R))
                  (psPow (psRing (psRing R)) P a₁)
                  (psPow (psRing (psRing R)) Q b₁)) c b a)
                ((psMul (psRing (psRing R))
                  (psMul (psRing (psRing R))
                    (psPow (psRing (psRing R)) W₁ a)
                    (psPow (psRing (psRing R)) W₂ b))
                  (psPow (psRing (psRing R)) W₃ c)) j k i)))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1)) (i + k + j + 1) := by
    show rsum R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul (ps23Comp R F P Q c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i))
        (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) = _
    refine rsum_congr R (i + k + j + 1) (fun c hc => ?_)
    refine rsum_congr R (i + k + j + 1) (fun b hb => ?_)
    refine rsum_congr R (i + k + j + 1) (fun a ha => ?_)
    cases Nat.lt_or_ge (i + k + j) (a + b + c) with
    | inl hhigh =>
      rw [ps3TriplePow_low R W₁ W₂ W₃ hW₁ hW₂ hW₃ a b c j k i hhigh,
        R.mul_zero (ps23Comp R F P Q c b a)]
      have hz : rsum R (fun b₁ => rsum R (fun a₁ =>
            R.mul (F b₁ a₁)
              (R.mul ((psMul (psRing (psRing R))
                  (psPow (psRing (psRing R)) P a₁)
                  (psPow (psRing (psRing R)) Q b₁)) c b a) R.zero))
            (i + k + j + 1)) (i + k + j + 1)
          = rsum R (fun _ => R.zero) (i + k + j + 1) :=
        rsum_congr R (i + k + j + 1) (fun b₁ _ => by
          have hz2 : rsum R (fun a₁ =>
                R.mul (F b₁ a₁)
                  (R.mul ((psMul (psRing (psRing R))
                      (psPow (psRing (psRing R)) P a₁)
                      (psPow (psRing (psRing R)) Q b₁)) c b a) R.zero))
                (i + k + j + 1)
              = rsum R (fun _ => R.zero) (i + k + j + 1) :=
            rsum_congr R (i + k + j + 1) (fun a₁ _ => by
              rw [R.mul_zero ((psMul (psRing (psRing R))
                  (psPow (psRing (psRing R)) P a₁)
                  (psPow (psRing (psRing R)) Q b₁)) c b a),
                R.mul_zero (F b₁ a₁)])
          rw [hz2]
          exact rsum_const_zero R (i + k + j + 1))
      rw [hz, rsum_const_zero]
    | inr hlow =>
      rw [ps23Comp_pad3 R F P Q hP hQ (i + k + j + 1) c b a (by omega),
        rsum_mul_right R _ ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i) (i + k + j + 1)]
      refine rsum_congr R (i + k + j + 1) (fun b₁ _ => ?_)
      rw [rsum_mul_right R _ ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i) (i + k + j + 1)]
      exact rsum_congr R (i + k + j + 1) (fun a₁ _ =>
        R.mul_assoc (F b₁ a₁) _ _)
  -- 右辺 → Z'（添字順 (b₁,a₁,c,b,a)）
  have hZR : ps23Comp R F (ps3Comp3 R P W₁ W₂ W₃)
        (ps3Comp3 R Q W₁ W₂ W₃) j k i
      = rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun c => rsum R (fun b =>
          rsum R (fun a =>
            R.mul (F b₁ a₁)
              (R.mul ((psMul (psRing (psRing R))
                  (psPow (psRing (psRing R)) P a₁)
                  (psPow (psRing (psRing R)) Q b₁)) c b a)
                ((psMul (psRing (psRing R))
                  (psMul (psRing (psRing R))
                    (psPow (psRing (psRing R)) W₁ a)
                    (psPow (psRing (psRing R)) W₂ b))
                  (psPow (psRing (psRing R)) W₃ c)) j k i)))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1)) (i + k + j + 1) := by
    show rsum R (fun b₁ => rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (ps3Comp3 R P W₁ W₂ W₃) a₁)
            (psPow (psRing (psRing R)) (ps3Comp3 R Q W₁ W₂ W₃) b₁)) j k i))
        (i + k + j + 1)) (i + k + j + 1) = _
    refine rsum_congr R (i + k + j + 1) (fun b₁ _ => ?_)
    refine rsum_congr R (i + k + j + 1) (fun a₁ _ => ?_)
    rw [ps3Comp3_pow R P W₁ W₂ W₃ hW₁ hW₂ hW₃ a₁,
      ps3Comp3_pow R Q W₁ W₂ W₃ hW₁ hW₂ hW₃ b₁,
      ← ps3Comp3_mul R (psPow (psRing (psRing R)) P a₁)
        (psPow (psRing (psRing R)) Q b₁) W₁ W₂ W₃ hW₁ hW₂ hW₃,
      ps3Comp3_eq_fam R (psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) P a₁)
        (psPow (psRing (psRing R)) Q b₁)) W₁ W₂ W₃ hW₁ hW₂ hW₃
        (i + k + j + 1) j k i (by omega)]
    show R.mul (F b₁ a₁) (rsum R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) P a₁)
            (psPow (psRing (psRing R)) Q b₁)) c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i))
        (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1)) = _
    rw [rsum_mul_left R _ (F b₁ a₁) (i + k + j + 1)]
    refine rsum_congr R (i + k + j + 1) (fun c _ => ?_)
    rw [rsum_mul_left R _ (F b₁ a₁) (i + k + j + 1)]
    refine rsum_congr R (i + k + j + 1) (fun b _ => ?_)
    rw [rsum_mul_left R _ (F b₁ a₁) (i + k + j + 1)]
  rw [hZL, hZR]
  exact (quint_reorder R (fun b₁ a₁ c b a =>
    R.mul (F b₁ a₁)
      (R.mul ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a₁)
          (psPow (psRing (psRing R)) Q b₁)) c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i)))
    (i + k + j + 1)).symm

end IUT
