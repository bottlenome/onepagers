/-
  IUT/FormalGroupMult.lean — M69b（ps23Comp の乗法性: 結合則キャンペーン第八層）

  結合則の最難所:

    **(F·G)∘(P,Q) = (F∘(P,Q))·(G∘(P,Q))**   （P₀₀₀ = Q₀₀₀ = 0）

  を完全証明する。戦略は M69a の装置の総力戦:

  係数 (j,k,i)・n := i+k+j・N := n+1 を固定し、
  * 右辺: 因子を族和表示に置換（ps3Mul_congr_le + 打ち切り安定性）し、
    族和の分配（ps3Fam_mul_right/left）とスカラー積の合成則
    （ps3Smul_mul_smul）・冪積の結合（ps3PowPow_mul）で
    **四重族和** Σ_{b₁}Σ_{a₁}Σ_{b₂}Σ_{a₂} (F_{b₁a₁}G_{b₂a₂})•(P^{a₁+a₂}Q^{b₁+b₂})
    に展開（全て環レベル — 係数掘りなし）
  * 左辺: 打ち切り安定性 + Cauchy 係数（ps2Mul_coeff）+ rsum_mul_right で
    Σ_{b}Σ_{a}Σ_{b₁≤b}Σ_{a₁≤a} (F_{b₁a₁}G_{b−b₁,a−a₁})·(P^aQ^b)_{jki}
  * 接合: **抽象四重和の再添字化 quad_sum_reindex**（添字交換
    rsum_exchange + 高位 padding rsum_pad + 三角和交換 rsum_triangle —
    M39 の三角和交換が 13 キャンペーンぶりに再登板）

  * M69b-1 `quad_sum_reindex` — 四重和の (b₁,a₁,b₂,a₂) ⇄ (b,a,b₁,a₁)
    再添字化（対角外消滅つき）
  * M69b-2 `ps23Comp_mul` — **乗法性**（本丸）

  次層で連鎖律 → 結合則。全て選択公理不使用。
-/
import IUT.FormalGroupFam

namespace IUT

/-! ## 四重和の再添字化 -/

/-- **定理 (M69b-1): 四重和の再添字化** — 対角外（b₁+b₂ > n または
    a₁+a₂ > n）で消える φ について
    Σ_{b₁<n+1}Σ_{a₁<n+1}Σ_{b₂<n+1}Σ_{a₂<n+1} φ(b₁,a₁,b₂,a₂)
    = Σ_{b<n+1}Σ_{a<n+1}Σ_{b₁≤b}Σ_{a₁≤a} φ(b₁,a₁,b−b₁,a−a₁)。
    （添字交換 + 高位 padding + 三角和交換 ×2。） -/
theorem quad_sum_reindex (R : CRing)
    (φ : Nat → Nat → Nat → Nat → R.carrier) (n : Nat)
    (hb : ∀ b₁ a₁ b₂ a₂, n < b₁ + b₂ → φ b₁ a₁ b₂ a₂ = R.zero)
    (ha : ∀ b₁ a₁ b₂ a₂, n < a₁ + a₂ → φ b₁ a₁ b₂ a₂ = R.zero) :
    rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun b₂ =>
        rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1)) (n + 1))
        (n + 1)
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ => φ b₁ a₁ (b - b₁) (a - a₁)) (a + 1))
          (b + 1)) (n + 1)) (n + 1) := by
  -- Step A: 各 b₁ で a₁ と b₂ を交換
  have hA : rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun b₂ =>
        rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1)) (n + 1))
        (n + 1)
      = rsum R (fun b₁ => rsum R (fun b₂ => rsum R (fun a₁ =>
          rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1)) (n + 1))
          (n + 1) :=
    rsum_congr R (n + 1) (fun b₁ _ =>
      rsum_exchange R (fun a₁ b₂ =>
        rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1) (n + 1))
  rw [hA]
  -- Step B+D: 各 (b₁, b₂) の内側を a-三角形に変換してから b-三角形
  -- まず各 b₁ で b₂ の範囲を n+1−b₁ に padding
  have hB : rsum R (fun b₁ => rsum R (fun b₂ => rsum R (fun a₁ =>
        rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1)) (n + 1))
        (n + 1)
      = rsum R (fun b₁ => rsum R (fun b₂ => rsum R (fun a₁ =>
          rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1))
          (n + 1 - b₁)) (n + 1) :=
    rsum_congr R (n + 1) (fun b₁ hb₁ =>
      rsum_pad R (fun b₂ => rsum R (fun a₁ =>
          rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1))
        (by omega)
        (fun b₂ hb₂ => by
          have hz : rsum R (fun a₁ =>
                rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1)
              = rsum R (fun _ => R.zero) (n + 1) :=
            rsum_congr R (n + 1) (fun a₁ _ => by
              have hz2 : rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)
                  = rsum R (fun _ => R.zero) (n + 1) :=
                rsum_congr R (n + 1) (fun a₂ _ =>
                  hb b₁ a₁ b₂ a₂ (by omega))
              rw [hz2]
              exact rsum_const_zero R (n + 1))
          show rsum R (fun a₁ =>
              rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1) = R.zero
          rw [hz]
          exact rsum_const_zero R (n + 1)))
  rw [hB]
  -- b-三角形（逆向き）
  have hC : rsum R (fun b₁ => rsum R (fun b₂ => rsum R (fun a₁ =>
        rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1))
        (n + 1 - b₁)) (n + 1)
      = rsum R (fun b => rsum R (fun b₁ => rsum R (fun a₁ =>
          rsum R (fun a₂ => φ b₁ a₁ (b - b₁) a₂) (n + 1)) (n + 1))
          (b + 1)) (n + 1) :=
    (rsum_triangle R (fun b₁ b₂ => rsum R (fun a₁ =>
      rsum R (fun a₂ => φ b₁ a₁ b₂ a₂) (n + 1)) (n + 1)) n).symm
  rw [hC]
  -- 各 (b, b₁) で a-対を padding + 三角形
  have hD : ∀ b b₁, rsum R (fun a₁ =>
        rsum R (fun a₂ => φ b₁ a₁ (b - b₁) a₂) (n + 1)) (n + 1)
      = rsum R (fun a => rsum R (fun a₁ =>
          φ b₁ a₁ (b - b₁) (a - a₁)) (a + 1)) (n + 1) := by
    intro b b₁
    have hpad : rsum R (fun a₁ =>
          rsum R (fun a₂ => φ b₁ a₁ (b - b₁) a₂) (n + 1)) (n + 1)
        = rsum R (fun a₁ =>
            rsum R (fun a₂ => φ b₁ a₁ (b - b₁) a₂) (n + 1 - a₁))
            (n + 1) :=
      rsum_congr R (n + 1) (fun a₁ ha₁ =>
        (rsum_pad R (fun a₂ => φ b₁ a₁ (b - b₁) a₂) (by omega)
          (fun a₂ ha₂ => ha b₁ a₁ (b - b₁) a₂ (by omega))).symm.symm)
    rw [hpad]
    exact ((rsum_triangle R (fun a₁ a₂ => φ b₁ a₁ (b - b₁) a₂) n).symm)
  have hD' : rsum R (fun b => rsum R (fun b₁ => rsum R (fun a₁ =>
        rsum R (fun a₂ => φ b₁ a₁ (b - b₁) a₂) (n + 1)) (n + 1))
        (b + 1)) (n + 1)
      = rsum R (fun b => rsum R (fun b₁ => rsum R (fun a =>
          rsum R (fun a₁ => φ b₁ a₁ (b - b₁) (a - a₁)) (a + 1))
          (n + 1)) (b + 1)) (n + 1) :=
    rsum_congr R (n + 1) (fun b _ =>
      rsum_congr R (b + 1) (fun b₁ _ => hD b b₁))
  rw [hD']
  -- Step E: 各 b で b₁ と a を交換
  exact rsum_congr R (n + 1) (fun b _ =>
    rsum_exchange R (fun b₁ a => rsum R (fun a₁ =>
      φ b₁ a₁ (b - b₁) (a - a₁)) (a + 1)) (b + 1) (n + 1))

/-! ## 乗法性 -/

/-- **定理 (M69b-2): ps23Comp の乗法性** —
    (F·G)∘(P,Q) = (F∘(P,Q))·(G∘(P,Q))（P₀₀₀ = Q₀₀₀ = 0）。
    結合則キャンペーンの最難所。 -/
theorem ps23Comp_mul (R : CRing) (F G : PS2 R) (P Q : PS3 R)
    (hP : P 0 0 0 = R.zero) (hQ : Q 0 0 0 = R.zero) :
    ps23Comp R (psMul (psRing R) F G) P Q
      = psMul (psRing (psRing R)) (ps23Comp R F P Q) (ps23Comp R G P Q)
    := by
  funext j k i
  -- 右辺: 因子を境界 N = i+k+j+1 の族和に置換
  have hRHS : psMul (psRing (psRing R)) (ps23Comp R F P Q)
      (ps23Comp R G P Q) j k i
      = psMul (psRing (psRing R))
          (ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
            ps3Smul R (F b a)
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                (psPow (psRing (psRing R)) Q b))) (i + k + j + 1))
            (i + k + j + 1))
          (ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
            ps3Smul R (G b a)
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                (psPow (psRing (psRing R)) Q b))) (i + k + j + 1))
            (i + k + j + 1)) j k i :=
    ps3Mul_congr_le R (i + k + j)
      (fun c' b' a' h =>
        ps23Comp_eq_fam R F P Q hP hQ (i + k + j + 1) c' b' a' (by omega))
      (fun c' b' a' h =>
        ps23Comp_eq_fam R G P Q hP hQ (i + k + j + 1) c' b' a' (by omega))
      j k i (Nat.le_refl (i + k + j))
  -- 族和の積を四重族和に展開（環レベル）
  have hfam : psMul (psRing (psRing R))
      (ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
        ps3Smul R (F b a)
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b))) (i + k + j + 1))
        (i + k + j + 1))
      (ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
        ps3Smul R (G b a)
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b))) (i + k + j + 1))
        (i + k + j + 1))
      = ps3Fam_sum R (fun b₁ => ps3Fam_sum R (fun a₁ =>
          ps3Fam_sum R (fun b₂ => ps3Fam_sum R (fun a₂ =>
            ps3Smul R (R.mul (F b₁ a₁) (G b₂ a₂))
              (psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) P (a₁ + a₂))
                (psPow (psRing (psRing R)) Q (b₁ + b₂))))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1) := by
    rw [ps3Fam_mul_right R (fun b₁ => ps3Fam_sum R (fun a₁ =>
      ps3Smul R (F b₁ a₁)
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
          (psPow (psRing (psRing R)) Q b₁))) (i + k + j + 1)) _
      (i + k + j + 1)]
    refine ps3Fam_congr R (i + k + j + 1) (fun b₁ _ => ?_)
    rw [ps3Fam_mul_right R (fun a₁ =>
      ps3Smul R (F b₁ a₁)
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
          (psPow (psRing (psRing R)) Q b₁))) _ (i + k + j + 1)]
    refine ps3Fam_congr R (i + k + j + 1) (fun a₁ _ => ?_)
    rw [ps3Fam_mul_left R (fun b₂ => ps3Fam_sum R (fun a₂ =>
      ps3Smul R (G b₂ a₂)
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₂)
          (psPow (psRing (psRing R)) Q b₂))) (i + k + j + 1)) _
      (i + k + j + 1)]
    refine ps3Fam_congr R (i + k + j + 1) (fun b₂ _ => ?_)
    rw [ps3Fam_mul_left R (fun a₂ =>
      ps3Smul R (G b₂ a₂)
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₂)
          (psPow (psRing (psRing R)) Q b₂))) _ (i + k + j + 1)]
    refine ps3Fam_congr R (i + k + j + 1) (fun a₂ _ => ?_)
    rw [ps3Smul_mul_smul R (F b₁ a₁) (G b₂ a₂)
      (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
        (psPow (psRing (psRing R)) Q b₁))
      (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₂)
        (psPow (psRing (psRing R)) Q b₂)),
      ps3PowPow_mul R P Q a₁ b₁ a₂ b₂]
  -- 左辺: 打ち切り安定性 + Cauchy 展開
  have hLHS : ps23Comp R (psMul (psRing R) F G) P Q j k i
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ =>
            R.mul (R.mul (F b₁ a₁) (G (b - b₁) (a - a₁)))
              ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                (psPow (psRing (psRing R)) Q b)) j k i)) (a + 1)) (b + 1))
          (i + k + j + 1)) (i + k + j + 1) := by
    rw [ps23Comp_eq_fam R (psMul (psRing R) F G) P Q hP hQ
      (i + k + j + 1) j k i (by omega)]
    show rsum R (fun b => rsum R (fun a =>
        R.mul (psMul (psRing R) F G b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)) (i + k + j + 1))
        (i + k + j + 1) = _
    refine rsum_congr R (i + k + j + 1) (fun b _ => ?_)
    refine rsum_congr R (i + k + j + 1) (fun a _ => ?_)
    rw [ps2Mul_coeff R F G b a,
      rsum_mul_right R _
        ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i) (b + 1)]
    refine rsum_congr R (b + 1) (fun b₁ _ => ?_)
    rw [rsum_mul_right R _
      ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
        (psPow (psRing (psRing R)) Q b)) j k i) (a + 1)]
  -- 四重族和の係数 = 再添字化した四重和
  have hquad : ps3Fam_sum R (fun b₁ => ps3Fam_sum R (fun a₁ =>
        ps3Fam_sum R (fun b₂ => ps3Fam_sum R (fun a₂ =>
          ps3Smul R (R.mul (F b₁ a₁) (G b₂ a₂))
            (psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) P (a₁ + a₂))
              (psPow (psRing (psRing R)) Q (b₁ + b₂))))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
        (i + k + j + 1) j k i
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ =>
            R.mul (R.mul (F b₁ a₁) (G (b - b₁) (a - a₁)))
              ((psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) P (a₁ + (a - a₁)))
                (psPow (psRing (psRing R)) Q (b₁ + (b - b₁)))) j k i))
            (a + 1)) (b + 1)) (i + k + j + 1)) (i + k + j + 1) :=
    quad_sum_reindex R (fun b₁ a₁ b₂ a₂ =>
        R.mul (R.mul (F b₁ a₁) (G b₂ a₂))
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) P (a₁ + a₂))
            (psPow (psRing (psRing R)) Q (b₁ + b₂))) j k i))
      (i + k + j)
      (fun b₁ a₁ b₂ a₂ h => by
        show R.mul (R.mul (F b₁ a₁) (G b₂ a₂))
            ((psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) P (a₁ + a₂))
              (psPow (psRing (psRing R)) Q (b₁ + b₂))) j k i) = R.zero
        rw [ps3PowPow_low R P Q hP hQ (a₁ + a₂) (b₁ + b₂) j k i
          (by omega)]
        exact R.mul_zero _)
      (fun b₁ a₁ b₂ a₂ h => by
        show R.mul (R.mul (F b₁ a₁) (G b₂ a₂))
            ((psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) P (a₁ + a₂))
              (psPow (psRing (psRing R)) Q (b₁ + b₂))) j k i) = R.zero
        rw [ps3PowPow_low R P Q hP hQ (a₁ + a₂) (b₁ + b₂) j k i
          (by omega)]
        exact R.mul_zero _)
  -- 添字の簡約 a₁+(a−a₁) = a・b₁+(b−b₁) = b
  have hcollapse : rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
        rsum R (fun a₁ =>
          R.mul (R.mul (F b₁ a₁) (G (b - b₁) (a - a₁)))
            ((psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) P (a₁ + (a - a₁)))
              (psPow (psRing (psRing R)) Q (b₁ + (b - b₁)))) j k i))
          (a + 1)) (b + 1)) (i + k + j + 1)) (i + k + j + 1)
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ =>
            R.mul (R.mul (F b₁ a₁) (G (b - b₁) (a - a₁)))
              ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                (psPow (psRing (psRing R)) Q b)) j k i)) (a + 1)) (b + 1))
          (i + k + j + 1)) (i + k + j + 1) :=
    rsum_congr R (i + k + j + 1) (fun b _ =>
      rsum_congr R (i + k + j + 1) (fun a _ =>
        rsum_congr R (b + 1) (fun b₁ hb₁ =>
          rsum_congr R (a + 1) (fun a₁ ha₁ => by
            rw [show a₁ + (a - a₁) = a by omega,
              show b₁ + (b - b₁) = b by omega]))))
  -- 仕上げ
  rw [hLHS, hRHS,
    show psMul (psRing (psRing R))
        (ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
          ps3Smul R (F b a)
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b))) (i + k + j + 1))
          (i + k + j + 1))
        (ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
          ps3Smul R (G b a)
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b))) (i + k + j + 1))
          (i + k + j + 1)) j k i
      = ps3Fam_sum R (fun b₁ => ps3Fam_sum R (fun a₁ =>
          ps3Fam_sum R (fun b₂ => ps3Fam_sum R (fun a₂ =>
            ps3Smul R (R.mul (F b₁ a₁) (G b₂ a₂))
              (psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) P (a₁ + a₂))
                (psPow (psRing (psRing R)) Q (b₁ + b₂))))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1) j k i from
      congrFun (congrFun (congrFun hfam j) k) i,
    hquad, hcollapse]

end IUT
