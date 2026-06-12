/-
  IUT/FormalGroupMult3.lean — M70F（ps3Comp3 の乗法性パッケージ: 結合則キャンペーン並行部品）

  結合則 F(F(X,Y),Z) = F(X,F(Y,Z)) の方程式検証では、三変数 → 三変数
  代入 ps3Comp3（M63: G(P,Q,W)_{j,k,i} = Σ_{c,b,a} G_{c,b,a}·
  ((P^a·Q^b)·W^c)_{j,k,i}）が truncated ring hom であることが要る。
  本層は二変数版（M69a の族和代数・M69b の乗法性・M70a の 1/冪の代入）
  の**精密な三変数ミラー**として、その全部品を一挙に建設する:

  * M70F-1 `ps3TriplePow_low` — **三重冪積の下方消滅**:
    W₁₀₀₀ = W₂₀₀₀ = W₃₀₀₀ = 0 のとき総次数 a+b+c 未満で
    ((W₁^a·W₂^b)·W₃^c)_{j,k,i} = 0（M68 の ps3Mul_low_zero を
    内側 ps3PowPow_low + 外側 W₃^c の総次数 truncation に二段適用）
  * M70F-2 `ps3TriplePow_mul` — **三重冪積の結合**:
    T₃(a₁,b₁,c₁)·T₃(a₂,b₂,c₂) = T₃(a₁+a₂, b₁+b₂, c₁+c₂)
    （M69a の ps3PowPow_mul + 冪指数加法 rpow_add + CRing interchange）
  * M70F-3 `ps3Comp3_eq_fam` — **打ち切り安定性**: 総次数 i+k+j < N の
    係数で ps3Comp3 は境界 N の三重族和 Fam_c Fam_b Fam_a
    smul(G_{c,b,a}) T₃(a,b,c) に一致（M69a の ps23Comp_eq_fam の三重版。
    境界差は rsum_pad ×3 + 三重冪積の下方消滅で吸収）
  * M70F-4 `hex_sum_reindex` — **六重和の再添字化**: 対角外
    （c₁+c₂ > n ∨ b₁+b₂ > n ∨ a₁+a₂ > n）で消える φ について
    Σ_{c₁}Σ_{b₁}Σ_{a₁}Σ_{c₂}Σ_{b₂}Σ_{a₂} φ
    = Σ_{c}Σ_{b}Σ_{a}Σ_{c₁≤c}Σ_{b₁≤b}Σ_{a₁≤a} φ(c₁,b₁,a₁,c−c₁,b−b₁,a−a₁)。
    戦略: 添字交換 rsum_exchange ×2 で c 対を隣接 → 高位 padding
    rsum_pad + 三角和交換 rsum_triangle で c 対を三角化 → 残る内側の
    四重和は **M69b の quad_sum_reindex がそのまま再登板** →
    rsum_exchange ×2 で並べ替え
  * M70F-5 `ps3Comp3_mul`（本丸） — **乗法性**:
    (G·H)∘(W₁,W₂,W₃) = (G∘(W₁,W₂,W₃))·(H∘(W₁,W₂,W₃))
    （W₁₀₀₀ = W₂₀₀₀ = W₃₀₀₀ = 0）。M69b の ps23Comp_mul の三変数
    ミラー: 右辺は族和表示（ps3Mul_congr_le + 打ち切り安定性）→
    族和の分配 ×6 + スカラー積の合成則 + 三重冪積の結合で**六重族和**、
    左辺は安定性 + 三重 Cauchy（M63）+ rsum_mul_right ×3 で六重和、
    接合は hex_sum_reindex + 添字簡約 a₁+(a−a₁) = a
  * M70F-6 `ps3Comp3_one` / `ps3Comp3_pow` — **1 の代入 = 1**
    （(c,b,a) = (0,0,0) への三重一点集中和）と**冪の代入**
    (G∘(W₁,W₂,W₃))^m = (G^m)∘(W₁,W₂,W₃)（乗法性の帰納適用）

  これで ps3Comp3(−, W₁, W₂, W₃) は truncated ring hom（1・積・冪を
  保存）。連鎖律 CR2 とその先の結合則検証の土台になる。
  全て選択公理不使用。
-/
import IUT.FormalGroupComp1

namespace IUT

/-! ## 三重冪積の下方消滅 -/

/-- **定理 (M70F-1): 三重冪積の下方消滅** — W₁₀₀₀ = W₂₀₀₀ = W₃₀₀₀ = 0
    なら (W₁^a·W₂^b)·W₃^c は総次数 a + b + c 未満で消える
    （内側の冪積は M68 の ps3PowPow_low、外側は ps3Mul_low_zero）。 -/
theorem ps3TriplePow_low (R : CRing) (W₁ W₂ W₃ : PS3 R)
    (hW₁ : W₁ 0 0 0 = R.zero) (hW₂ : W₂ 0 0 0 = R.zero)
    (hW₃ : W₃ 0 0 0 = R.zero) (a b c : Nat)
    (j k i : Nat) (h : i + k + j < a + b + c) :
    psMul (psRing (psRing R))
      (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
        (psPow (psRing (psRing R)) W₂ b))
      (psPow (psRing (psRing R)) W₃ c) j k i = R.zero :=
  ps3Mul_low_zero R
    (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
      (psPow (psRing (psRing R)) W₂ b))
    (psPow (psRing (psRing R)) W₃ c) (a + b) c
    (fun c' b' a' h' => ps3PowPow_low R W₁ W₂ hW₁ hW₂ a b c' b' a' h')
    (fun c' b' a' h' => ps3Pow_tcoeff_zero R W₃ hW₃ c a' b' c' h')
    j k i h

/-! ## 三重冪積の結合 -/

/-- **定理 (M70F-2): 三重冪積の結合** —
    ((W₁^{a₁}W₂^{b₁})W₃^{c₁})·((W₁^{a₂}W₂^{b₂})W₃^{c₂})
    = (W₁^{a₁+a₂}W₂^{b₁+b₂})W₃^{c₁+c₂}
    （M69a の冪積の結合 + 冪指数加法 + CRing interchange）。 -/
theorem ps3TriplePow_mul (R : CRing) (W₁ W₂ W₃ : PS3 R)
    (a₁ b₁ c₁ a₂ b₂ c₂ : Nat) :
    psMul (psRing (psRing R))
      (psMul (psRing (psRing R))
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₁)
          (psPow (psRing (psRing R)) W₂ b₁))
        (psPow (psRing (psRing R)) W₃ c₁))
      (psMul (psRing (psRing R))
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₂)
          (psPow (psRing (psRing R)) W₂ b₂))
        (psPow (psRing (psRing R)) W₃ c₂))
    = psMul (psRing (psRing R))
        (psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) W₁ (a₁ + a₂))
          (psPow (psRing (psRing R)) W₂ (b₁ + b₂)))
        (psPow (psRing (psRing R)) W₃ (c₁ + c₂)) := by
  have hW : psPow (psRing (psRing R)) W₃ (c₁ + c₂)
      = psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₃ c₁)
          (psPow (psRing (psRing R)) W₃ c₂) := by
    rw [psPow_eq_rpow (psRing (psRing R)) W₃ (c₁ + c₂),
      rpow_add (psRing (psRing (psRing R))) W₃ c₁ c₂,
      ← psPow_eq_rpow (psRing (psRing R)) W₃ c₁,
      ← psPow_eq_rpow (psRing (psRing R)) W₃ c₂]
    rfl
  rw [← ps3PowPow_mul R W₁ W₂ a₁ b₁ a₂ b₂, hW]
  exact CRing.mul_mul_comm (psRing (psRing (psRing R)))
    (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₁)
      (psPow (psRing (psRing R)) W₂ b₁))
    (psPow (psRing (psRing R)) W₃ c₁)
    (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₂)
      (psPow (psRing (psRing R)) W₂ b₂))
    (psPow (psRing (psRing R)) W₃ c₂)

/-! ## 打ち切り安定性 -/

/-- **定理 (M70F-3): ps3Comp3 の族和表示（打ち切り安定性）** —
    総次数 i+k+j < N の係数で、ps3Comp3 G W₁ W₂ W₃ は境界 N の三重族和
    Fam_c Fam_b Fam_a smul(G_{c,b,a}) ((W₁^a·W₂^b)·W₃^c) に一致する
    （W₁₀₀₀ = W₂₀₀₀ = W₃₀₀₀ = 0。境界差は三重冪積の下方消滅で吸収）。 -/
theorem ps3Comp3_eq_fam (R : CRing) (G W₁ W₂ W₃ : PS3 R)
    (hW₁ : W₁ 0 0 0 = R.zero) (hW₂ : W₂ 0 0 0 = R.zero)
    (hW₃ : W₃ 0 0 0 = R.zero)
    (N j k i : Nat) (hN : i + k + j < N) :
    ps3Comp3 R G W₁ W₂ W₃ j k i
      = ps3Fam_sum R (fun c => ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
          ps3Smul R (G c b a)
            (psMul (psRing (psRing R))
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ c))) N) N) N j k i := by
  show rsum R (fun c => rsum R (fun b => rsum R (fun a =>
      R.mul (G c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i))
      (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1)
    = rsum R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul (G c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i)) N) N) N
  -- 最内 a の境界を N → i+k+j+1 に詰め替え（a ≥ i+k+j+1 で冪積消滅）
  have hinner : ∀ c b, rsum R (fun a =>
        R.mul (G c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i)) N
      = rsum R (fun a =>
          R.mul (G c b a)
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ c)) j k i)) (i + k + j + 1) :=
    fun c b => rsum_pad R (fun a =>
        R.mul (G c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i)) (by omega)
      (fun a ha => by
        show R.mul (G c b a)
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ c)) j k i) = R.zero
        rw [ps3TriplePow_low R W₁ W₂ W₃ hW₁ hW₂ hW₃ a b c j k i (by omega)]
        exact R.mul_zero _)
  -- 中段 b の境界を詰め替え（b ≥ i+k+j+1 では a の全項が消滅）
  have hmid : ∀ c, rsum R (fun b => rsum R (fun a =>
        R.mul (G c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i)) N) N
      = rsum R (fun b => rsum R (fun a =>
          R.mul (G c b a)
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ c)) j k i)) N) (i + k + j + 1) :=
    fun c => rsum_pad R (fun b => rsum R (fun a =>
        R.mul (G c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i)) N) (by omega)
      (fun b hb => by
        show rsum R (fun a =>
            R.mul (G c b a)
              ((psMul (psRing (psRing R))
                (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                  (psPow (psRing (psRing R)) W₂ b))
                (psPow (psRing (psRing R)) W₃ c)) j k i)) N = R.zero
        have hz : rsum R (fun a =>
              R.mul (G c b a)
                ((psMul (psRing (psRing R))
                  (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                    (psPow (psRing (psRing R)) W₂ b))
                  (psPow (psRing (psRing R)) W₃ c)) j k i)) N
            = rsum R (fun _ => R.zero) N :=
          rsum_congr R N (fun a _ => by
            rw [ps3TriplePow_low R W₁ W₂ W₃ hW₁ hW₂ hW₃ a b c j k i
              (by omega)]
            exact R.mul_zero _)
        rw [hz]
        exact rsum_const_zero R N)
  -- 最外 c の境界を詰め替え（c ≥ i+k+j+1 では b・a の全項が消滅）
  have houter : rsum R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul (G c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i)) N) N) N
      = rsum R (fun c => rsum R (fun b => rsum R (fun a =>
          R.mul (G c b a)
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ c)) j k i)) N) N)
          (i + k + j + 1) :=
    rsum_pad R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul (G c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i)) N) N) (by omega)
      (fun c hc => by
        show rsum R (fun b => rsum R (fun a =>
            R.mul (G c b a)
              ((psMul (psRing (psRing R))
                (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                  (psPow (psRing (psRing R)) W₂ b))
                (psPow (psRing (psRing R)) W₃ c)) j k i)) N) N = R.zero
        have hz : rsum R (fun b => rsum R (fun a =>
              R.mul (G c b a)
                ((psMul (psRing (psRing R))
                  (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                    (psPow (psRing (psRing R)) W₂ b))
                  (psPow (psRing (psRing R)) W₃ c)) j k i)) N) N
            = rsum R (fun _ => R.zero) N :=
          rsum_congr R N (fun b _ => by
            have hz2 : rsum R (fun a =>
                  R.mul (G c b a)
                    ((psMul (psRing (psRing R))
                      (psMul (psRing (psRing R))
                        (psPow (psRing (psRing R)) W₁ a)
                        (psPow (psRing (psRing R)) W₂ b))
                      (psPow (psRing (psRing R)) W₃ c)) j k i)) N
                = rsum R (fun _ => R.zero) N :=
              rsum_congr R N (fun a _ => by
                rw [ps3TriplePow_low R W₁ W₂ W₃ hW₁ hW₂ hW₃ a b c j k i
                  (by omega)]
                exact R.mul_zero _)
            show rsum R (fun a =>
                R.mul (G c b a)
                  ((psMul (psRing (psRing R))
                    (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                      (psPow (psRing (psRing R)) W₂ b))
                    (psPow (psRing (psRing R)) W₃ c)) j k i)) N = R.zero
            rw [hz2]
            exact rsum_const_zero R N)
        rw [hz]
        exact rsum_const_zero R N)
  rw [houter]
  refine rsum_congr R (i + k + j + 1) (fun c _ => ?_)
  rw [hmid c]
  exact rsum_congr R (i + k + j + 1) (fun b _ => (hinner c b).symm)

/-! ## 六重和の再添字化 -/

/-- **定理 (M70F-4): 六重和の再添字化** — 対角外（c₁+c₂ > n または
    b₁+b₂ > n または a₁+a₂ > n）で消える φ について
    Σ_{c₁}Σ_{b₁}Σ_{a₁}Σ_{c₂}Σ_{b₂}Σ_{a₂} φ(c₁,b₁,a₁,c₂,b₂,a₂)
    = Σ_{c}Σ_{b}Σ_{a}Σ_{c₁≤c}Σ_{b₁≤b}Σ_{a₁≤a}
        φ(c₁,b₁,a₁,c−c₁,b−b₁,a−a₁)（全外側境界 n+1）。
    M69b の quad_sum_reindex の三対版: 添字交換 ×2 で c 対を隣接 →
    padding + 三角和交換で c 対を (c, c₁≤c) に → 内側の四重和は
    quad_sum_reindex がそのまま適用 → 添字交換 ×2 で並べ替え。 -/
theorem hex_sum_reindex (R : CRing)
    (φ : Nat → Nat → Nat → Nat → Nat → Nat → R.carrier) (n : Nat)
    (hc : ∀ c₁ b₁ a₁ c₂ b₂ a₂, n < c₁ + c₂ → φ c₁ b₁ a₁ c₂ b₂ a₂ = R.zero)
    (hb : ∀ c₁ b₁ a₁ c₂ b₂ a₂, n < b₁ + b₂ → φ c₁ b₁ a₁ c₂ b₂ a₂ = R.zero)
    (ha : ∀ c₁ b₁ a₁ c₂ b₂ a₂, n < a₁ + a₂ → φ c₁ b₁ a₁ c₂ b₂ a₂ = R.zero) :
    rsum R (fun c₁ => rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun c₂ =>
        rsum R (fun b₂ => rsum R (fun a₂ => φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1))
        (n + 1)) (n + 1)) (n + 1)) (n + 1)) (n + 1)
      = rsum R (fun c => rsum R (fun b => rsum R (fun a => rsum R (fun c₁ =>
          rsum R (fun b₁ => rsum R (fun a₁ =>
            φ c₁ b₁ a₁ (c - c₁) (b - b₁) (a - a₁)) (a + 1)) (b + 1))
          (c + 1)) (n + 1)) (n + 1)) (n + 1) := by
  -- Step A1: 各 (c₁, b₁) で a₁ と c₂ を交換
  have hA1 : rsum R (fun c₁ => rsum R (fun b₁ => rsum R (fun a₁ =>
        rsum R (fun c₂ => rsum R (fun b₂ => rsum R (fun a₂ =>
          φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1)) (n + 1))
        (n + 1)
      = rsum R (fun c₁ => rsum R (fun b₁ => rsum R (fun c₂ =>
          rsum R (fun a₁ => rsum R (fun b₂ => rsum R (fun a₂ =>
            φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1)) (n + 1))
          (n + 1) :=
    rsum_congr R (n + 1) (fun c₁ _ =>
      rsum_congr R (n + 1) (fun b₁ _ =>
        rsum_exchange R (fun a₁ c₂ => rsum R (fun b₂ => rsum R (fun a₂ =>
          φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1) (n + 1)))
  rw [hA1]
  -- Step A2: 各 c₁ で b₁ と c₂ を交換
  have hA2 : rsum R (fun c₁ => rsum R (fun b₁ => rsum R (fun c₂ =>
        rsum R (fun a₁ => rsum R (fun b₂ => rsum R (fun a₂ =>
          φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1)) (n + 1))
        (n + 1)
      = rsum R (fun c₁ => rsum R (fun c₂ => rsum R (fun b₁ =>
          rsum R (fun a₁ => rsum R (fun b₂ => rsum R (fun a₂ =>
            φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1)) (n + 1))
          (n + 1) :=
    rsum_congr R (n + 1) (fun c₁ _ =>
      rsum_exchange R (fun b₁ c₂ => rsum R (fun a₁ => rsum R (fun b₂ =>
        rsum R (fun a₂ => φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1))
        (n + 1) (n + 1))
  rw [hA2]
  -- Step B: 各 c₁ で c₂ の範囲を n+1−c₁ に padding（対角外消滅）
  have hB : rsum R (fun c₁ => rsum R (fun c₂ => rsum R (fun b₁ =>
        rsum R (fun a₁ => rsum R (fun b₂ => rsum R (fun a₂ =>
          φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1)) (n + 1))
        (n + 1)
      = rsum R (fun c₁ => rsum R (fun c₂ => rsum R (fun b₁ =>
          rsum R (fun a₁ => rsum R (fun b₂ => rsum R (fun a₂ =>
            φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1))
          (n + 1 - c₁)) (n + 1) :=
    rsum_congr R (n + 1) (fun c₁ hc₁ =>
      rsum_pad R (fun c₂ => rsum R (fun b₁ => rsum R (fun a₁ =>
          rsum R (fun b₂ => rsum R (fun a₂ =>
            φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1))
        (by omega)
        (fun c₂ hc₂ => by
          show rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun b₂ =>
              rsum R (fun a₂ => φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1))
              (n + 1)) (n + 1) = R.zero
          have hz1 : rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun b₂ =>
                rsum R (fun a₂ => φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1))
                (n + 1)) (n + 1)
              = rsum R (fun _ => R.zero) (n + 1) :=
            rsum_congr R (n + 1) (fun b₁ _ => by
              have hz2 : rsum R (fun a₁ => rsum R (fun b₂ =>
                    rsum R (fun a₂ => φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1))
                    (n + 1)
                  = rsum R (fun _ => R.zero) (n + 1) :=
                rsum_congr R (n + 1) (fun a₁ _ => by
                  have hz3 : rsum R (fun b₂ => rsum R (fun a₂ =>
                        φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)
                      = rsum R (fun _ => R.zero) (n + 1) :=
                    rsum_congr R (n + 1) (fun b₂ _ => by
                      have hz4 : rsum R (fun a₂ =>
                            φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)
                          = rsum R (fun _ => R.zero) (n + 1) :=
                        rsum_congr R (n + 1) (fun a₂ _ =>
                          hc c₁ b₁ a₁ c₂ b₂ a₂ (by omega))
                      show rsum R (fun a₂ =>
                          φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1) = R.zero
                      rw [hz4]
                      exact rsum_const_zero R (n + 1))
                  show rsum R (fun b₂ => rsum R (fun a₂ =>
                      φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1) = R.zero
                  rw [hz3]
                  exact rsum_const_zero R (n + 1))
              show rsum R (fun a₁ => rsum R (fun b₂ => rsum R (fun a₂ =>
                  φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1) = R.zero
              rw [hz2]
              exact rsum_const_zero R (n + 1))
          rw [hz1]
          exact rsum_const_zero R (n + 1)))
  rw [hB]
  -- Step C: c 対の三角和交換（逆向き）
  have hC : rsum R (fun c₁ => rsum R (fun c₂ => rsum R (fun b₁ =>
        rsum R (fun a₁ => rsum R (fun b₂ => rsum R (fun a₂ =>
          φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1))
        (n + 1 - c₁)) (n + 1)
      = rsum R (fun c => rsum R (fun c₁ => rsum R (fun b₁ =>
          rsum R (fun a₁ => rsum R (fun b₂ => rsum R (fun a₂ =>
            φ c₁ b₁ a₁ (c - c₁) b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1))
          (c + 1)) (n + 1) :=
    (rsum_triangle R (fun c₁ c₂ => rsum R (fun b₁ => rsum R (fun a₁ =>
      rsum R (fun b₂ => rsum R (fun a₂ =>
        φ c₁ b₁ a₁ c₂ b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1)) n).symm
  rw [hC]
  -- Step D: 各 (c, c₁) で内側の四重和に quad_sum_reindex を適用
  have hD : ∀ c c₁, rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun b₂ =>
        rsum R (fun a₂ => φ c₁ b₁ a₁ (c - c₁) b₂ a₂) (n + 1)) (n + 1))
        (n + 1)) (n + 1)
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ => φ c₁ b₁ a₁ (c - c₁) (b - b₁) (a - a₁)) (a + 1))
          (b + 1)) (n + 1)) (n + 1) :=
    fun c c₁ => quad_sum_reindex R
      (fun b₁ a₁ b₂ a₂ => φ c₁ b₁ a₁ (c - c₁) b₂ a₂) n
      (fun b₁ a₁ b₂ a₂ h => hb c₁ b₁ a₁ (c - c₁) b₂ a₂ h)
      (fun b₁ a₁ b₂ a₂ h => ha c₁ b₁ a₁ (c - c₁) b₂ a₂ h)
  have hD' : rsum R (fun c => rsum R (fun c₁ => rsum R (fun b₁ =>
        rsum R (fun a₁ => rsum R (fun b₂ => rsum R (fun a₂ =>
          φ c₁ b₁ a₁ (c - c₁) b₂ a₂) (n + 1)) (n + 1)) (n + 1)) (n + 1))
        (c + 1)) (n + 1)
      = rsum R (fun c => rsum R (fun c₁ => rsum R (fun b =>
          rsum R (fun a => rsum R (fun b₁ => rsum R (fun a₁ =>
            φ c₁ b₁ a₁ (c - c₁) (b - b₁) (a - a₁)) (a + 1)) (b + 1))
          (n + 1)) (n + 1)) (c + 1)) (n + 1) :=
    rsum_congr R (n + 1) (fun c _ =>
      rsum_congr R (c + 1) (fun c₁ _ => hD c c₁))
  rw [hD']
  -- Step E: 各 c で c₁ と b を交換
  have hE : rsum R (fun c => rsum R (fun c₁ => rsum R (fun b =>
        rsum R (fun a => rsum R (fun b₁ => rsum R (fun a₁ =>
          φ c₁ b₁ a₁ (c - c₁) (b - b₁) (a - a₁)) (a + 1)) (b + 1)) (n + 1))
        (n + 1)) (c + 1)) (n + 1)
      = rsum R (fun c => rsum R (fun b => rsum R (fun c₁ =>
          rsum R (fun a => rsum R (fun b₁ => rsum R (fun a₁ =>
            φ c₁ b₁ a₁ (c - c₁) (b - b₁) (a - a₁)) (a + 1)) (b + 1)) (n + 1))
          (c + 1)) (n + 1)) (n + 1) :=
    rsum_congr R (n + 1) (fun c _ =>
      rsum_exchange R (fun c₁ b => rsum R (fun a => rsum R (fun b₁ =>
        rsum R (fun a₁ => φ c₁ b₁ a₁ (c - c₁) (b - b₁) (a - a₁)) (a + 1))
        (b + 1)) (n + 1)) (c + 1) (n + 1))
  rw [hE]
  -- Step F: 各 (c, b) で c₁ と a を交換
  exact rsum_congr R (n + 1) (fun c _ =>
    rsum_congr R (n + 1) (fun b _ =>
      rsum_exchange R (fun c₁ a => rsum R (fun b₁ => rsum R (fun a₁ =>
        φ c₁ b₁ a₁ (c - c₁) (b - b₁) (a - a₁)) (a + 1)) (b + 1))
        (c + 1) (n + 1)))

/-! ## 乗法性 -/

/-- **定理 (M70F-5): ps3Comp3 の乗法性** —
    (G·H)∘(W₁,W₂,W₃) = (G∘(W₁,W₂,W₃))·(H∘(W₁,W₂,W₃))
    （W₁₀₀₀ = W₂₀₀₀ = W₃₀₀₀ = 0）。M69b の ps23Comp_mul の三変数ミラー。 -/
theorem ps3Comp3_mul (R : CRing) (G H W₁ W₂ W₃ : PS3 R)
    (hW₁ : W₁ 0 0 0 = R.zero) (hW₂ : W₂ 0 0 0 = R.zero)
    (hW₃ : W₃ 0 0 0 = R.zero) :
    ps3Comp3 R (psMul (psRing (psRing R)) G H) W₁ W₂ W₃
      = psMul (psRing (psRing R)) (ps3Comp3 R G W₁ W₂ W₃)
          (ps3Comp3 R H W₁ W₂ W₃) := by
  funext j k i
  -- 右辺: 因子を境界 N = i+k+j+1 の三重族和に置換
  have hRHS : psMul (psRing (psRing R)) (ps3Comp3 R G W₁ W₂ W₃)
      (ps3Comp3 R H W₁ W₂ W₃) j k i
      = psMul (psRing (psRing R))
          (ps3Fam_sum R (fun c => ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
            ps3Smul R (G c b a)
              (psMul (psRing (psRing R))
                (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                  (psPow (psRing (psRing R)) W₂ b))
                (psPow (psRing (psRing R)) W₃ c))) (i + k + j + 1))
            (i + k + j + 1)) (i + k + j + 1))
          (ps3Fam_sum R (fun c => ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
            ps3Smul R (H c b a)
              (psMul (psRing (psRing R))
                (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                  (psPow (psRing (psRing R)) W₂ b))
                (psPow (psRing (psRing R)) W₃ c))) (i + k + j + 1))
            (i + k + j + 1)) (i + k + j + 1)) j k i :=
    ps3Mul_congr_le R (i + k + j)
      (fun c' b' a' h =>
        ps3Comp3_eq_fam R G W₁ W₂ W₃ hW₁ hW₂ hW₃ (i + k + j + 1) c' b' a'
          (by omega))
      (fun c' b' a' h =>
        ps3Comp3_eq_fam R H W₁ W₂ W₃ hW₁ hW₂ hW₃ (i + k + j + 1) c' b' a'
          (by omega))
      j k i (Nat.le_refl (i + k + j))
  -- 族和の積を六重族和に展開（環レベル — 係数掘りなし）
  have hfam : psMul (psRing (psRing R))
      (ps3Fam_sum R (fun c => ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
        ps3Smul R (G c b a)
          (psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c))) (i + k + j + 1))
        (i + k + j + 1)) (i + k + j + 1))
      (ps3Fam_sum R (fun c => ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
        ps3Smul R (H c b a)
          (psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c))) (i + k + j + 1))
        (i + k + j + 1)) (i + k + j + 1))
      = ps3Fam_sum R (fun c₁ => ps3Fam_sum R (fun b₁ => ps3Fam_sum R (fun a₁ =>
          ps3Fam_sum R (fun c₂ => ps3Fam_sum R (fun b₂ =>
            ps3Fam_sum R (fun a₂ =>
              ps3Smul R (R.mul (G c₁ b₁ a₁) (H c₂ b₂ a₂))
                (psMul (psRing (psRing R))
                  (psMul (psRing (psRing R))
                    (psPow (psRing (psRing R)) W₁ (a₁ + a₂))
                    (psPow (psRing (psRing R)) W₂ (b₁ + b₂)))
                  (psPow (psRing (psRing R)) W₃ (c₁ + c₂))))
              (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) := by
    rw [ps3Fam_mul_right R (fun c₁ => ps3Fam_sum R (fun b₁ =>
      ps3Fam_sum R (fun a₁ =>
        ps3Smul R (G c₁ b₁ a₁)
          (psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₁)
              (psPow (psRing (psRing R)) W₂ b₁))
            (psPow (psRing (psRing R)) W₃ c₁))) (i + k + j + 1))
      (i + k + j + 1)) _ (i + k + j + 1)]
    refine ps3Fam_congr R (i + k + j + 1) (fun c₁ _ => ?_)
    rw [ps3Fam_mul_right R (fun b₁ => ps3Fam_sum R (fun a₁ =>
      ps3Smul R (G c₁ b₁ a₁)
        (psMul (psRing (psRing R))
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₁)
            (psPow (psRing (psRing R)) W₂ b₁))
          (psPow (psRing (psRing R)) W₃ c₁))) (i + k + j + 1)) _
      (i + k + j + 1)]
    refine ps3Fam_congr R (i + k + j + 1) (fun b₁ _ => ?_)
    rw [ps3Fam_mul_right R (fun a₁ =>
      ps3Smul R (G c₁ b₁ a₁)
        (psMul (psRing (psRing R))
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₁)
            (psPow (psRing (psRing R)) W₂ b₁))
          (psPow (psRing (psRing R)) W₃ c₁))) _ (i + k + j + 1)]
    refine ps3Fam_congr R (i + k + j + 1) (fun a₁ _ => ?_)
    rw [ps3Fam_mul_left R (fun c₂ => ps3Fam_sum R (fun b₂ =>
      ps3Fam_sum R (fun a₂ =>
        ps3Smul R (H c₂ b₂ a₂)
          (psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₂)
              (psPow (psRing (psRing R)) W₂ b₂))
            (psPow (psRing (psRing R)) W₃ c₂))) (i + k + j + 1))
      (i + k + j + 1)) _ (i + k + j + 1)]
    refine ps3Fam_congr R (i + k + j + 1) (fun c₂ _ => ?_)
    rw [ps3Fam_mul_left R (fun b₂ => ps3Fam_sum R (fun a₂ =>
      ps3Smul R (H c₂ b₂ a₂)
        (psMul (psRing (psRing R))
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₂)
            (psPow (psRing (psRing R)) W₂ b₂))
          (psPow (psRing (psRing R)) W₃ c₂))) (i + k + j + 1)) _
      (i + k + j + 1)]
    refine ps3Fam_congr R (i + k + j + 1) (fun b₂ _ => ?_)
    rw [ps3Fam_mul_left R (fun a₂ =>
      ps3Smul R (H c₂ b₂ a₂)
        (psMul (psRing (psRing R))
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₂)
            (psPow (psRing (psRing R)) W₂ b₂))
          (psPow (psRing (psRing R)) W₃ c₂))) _ (i + k + j + 1)]
    refine ps3Fam_congr R (i + k + j + 1) (fun a₂ _ => ?_)
    rw [ps3Smul_mul_smul R (G c₁ b₁ a₁) (H c₂ b₂ a₂)
      (psMul (psRing (psRing R))
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₁)
          (psPow (psRing (psRing R)) W₂ b₁))
        (psPow (psRing (psRing R)) W₃ c₁))
      (psMul (psRing (psRing R))
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a₂)
          (psPow (psRing (psRing R)) W₂ b₂))
        (psPow (psRing (psRing R)) W₃ c₂)),
      ps3TriplePow_mul R W₁ W₂ W₃ a₁ b₁ c₁ a₂ b₂ c₂]
  -- 左辺: 打ち切り安定性 + 三重 Cauchy 展開
  have hLHS : ps3Comp3 R (psMul (psRing (psRing R)) G H) W₁ W₂ W₃ j k i
      = rsum R (fun c => rsum R (fun b => rsum R (fun a => rsum R (fun c₁ =>
          rsum R (fun b₁ => rsum R (fun a₁ =>
            R.mul (R.mul (G c₁ b₁ a₁) (H (c - c₁) (b - b₁) (a - a₁)))
              ((psMul (psRing (psRing R))
                (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                  (psPow (psRing (psRing R)) W₂ b))
                (psPow (psRing (psRing R)) W₃ c)) j k i)) (a + 1)) (b + 1))
          (c + 1)) (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) := by
    rw [ps3Comp3_eq_fam R (psMul (psRing (psRing R)) G H) W₁ W₂ W₃
      hW₁ hW₂ hW₃ (i + k + j + 1) j k i (by omega)]
    show rsum R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul (psMul (psRing (psRing R)) G H c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i)) (i + k + j + 1))
        (i + k + j + 1)) (i + k + j + 1) = _
    refine rsum_congr R (i + k + j + 1) (fun c _ => ?_)
    refine rsum_congr R (i + k + j + 1) (fun b _ => ?_)
    refine rsum_congr R (i + k + j + 1) (fun a _ => ?_)
    rw [ps3Mul_coeff R G H c b a,
      rsum_mul_right R _
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i) (c + 1)]
    refine rsum_congr R (c + 1) (fun c₁ _ => ?_)
    rw [rsum_mul_right R _
      ((psMul (psRing (psRing R))
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
          (psPow (psRing (psRing R)) W₂ b))
        (psPow (psRing (psRing R)) W₃ c)) j k i) (b + 1)]
    refine rsum_congr R (b + 1) (fun b₁ _ => ?_)
    rw [rsum_mul_right R _
      ((psMul (psRing (psRing R))
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
          (psPow (psRing (psRing R)) W₂ b))
        (psPow (psRing (psRing R)) W₃ c)) j k i) (a + 1)]
  -- 六重族和の係数 = 再添字化した六重和
  have hhex : ps3Fam_sum R (fun c₁ => ps3Fam_sum R (fun b₁ =>
        ps3Fam_sum R (fun a₁ => ps3Fam_sum R (fun c₂ =>
          ps3Fam_sum R (fun b₂ => ps3Fam_sum R (fun a₂ =>
            ps3Smul R (R.mul (G c₁ b₁ a₁) (H c₂ b₂ a₂))
              (psMul (psRing (psRing R))
                (psMul (psRing (psRing R))
                  (psPow (psRing (psRing R)) W₁ (a₁ + a₂))
                  (psPow (psRing (psRing R)) W₂ (b₁ + b₂)))
                (psPow (psRing (psRing R)) W₃ (c₁ + c₂))))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) j k i
      = rsum R (fun c => rsum R (fun b => rsum R (fun a => rsum R (fun c₁ =>
          rsum R (fun b₁ => rsum R (fun a₁ =>
            R.mul (R.mul (G c₁ b₁ a₁) (H (c - c₁) (b - b₁) (a - a₁)))
              ((psMul (psRing (psRing R))
                (psMul (psRing (psRing R))
                  (psPow (psRing (psRing R)) W₁ (a₁ + (a - a₁)))
                  (psPow (psRing (psRing R)) W₂ (b₁ + (b - b₁))))
                (psPow (psRing (psRing R)) W₃ (c₁ + (c - c₁)))) j k i))
            (a + 1)) (b + 1)) (c + 1)) (i + k + j + 1)) (i + k + j + 1))
          (i + k + j + 1) :=
    hex_sum_reindex R (fun c₁ b₁ a₁ c₂ b₂ a₂ =>
        R.mul (R.mul (G c₁ b₁ a₁) (H c₂ b₂ a₂))
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R))
              (psPow (psRing (psRing R)) W₁ (a₁ + a₂))
              (psPow (psRing (psRing R)) W₂ (b₁ + b₂)))
            (psPow (psRing (psRing R)) W₃ (c₁ + c₂))) j k i))
      (i + k + j)
      (fun c₁ b₁ a₁ c₂ b₂ a₂ h => by
        show R.mul (R.mul (G c₁ b₁ a₁) (H c₂ b₂ a₂))
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) W₁ (a₁ + a₂))
                (psPow (psRing (psRing R)) W₂ (b₁ + b₂)))
              (psPow (psRing (psRing R)) W₃ (c₁ + c₂))) j k i) = R.zero
        rw [ps3TriplePow_low R W₁ W₂ W₃ hW₁ hW₂ hW₃ (a₁ + a₂) (b₁ + b₂)
          (c₁ + c₂) j k i (by omega)]
        exact R.mul_zero _)
      (fun c₁ b₁ a₁ c₂ b₂ a₂ h => by
        show R.mul (R.mul (G c₁ b₁ a₁) (H c₂ b₂ a₂))
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) W₁ (a₁ + a₂))
                (psPow (psRing (psRing R)) W₂ (b₁ + b₂)))
              (psPow (psRing (psRing R)) W₃ (c₁ + c₂))) j k i) = R.zero
        rw [ps3TriplePow_low R W₁ W₂ W₃ hW₁ hW₂ hW₃ (a₁ + a₂) (b₁ + b₂)
          (c₁ + c₂) j k i (by omega)]
        exact R.mul_zero _)
      (fun c₁ b₁ a₁ c₂ b₂ a₂ h => by
        show R.mul (R.mul (G c₁ b₁ a₁) (H c₂ b₂ a₂))
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) W₁ (a₁ + a₂))
                (psPow (psRing (psRing R)) W₂ (b₁ + b₂)))
              (psPow (psRing (psRing R)) W₃ (c₁ + c₂))) j k i) = R.zero
        rw [ps3TriplePow_low R W₁ W₂ W₃ hW₁ hW₂ hW₃ (a₁ + a₂) (b₁ + b₂)
          (c₁ + c₂) j k i (by omega)]
        exact R.mul_zero _)
  -- 添字の簡約 a₁+(a−a₁) = a・b₁+(b−b₁) = b・c₁+(c−c₁) = c
  have hcollapse : rsum R (fun c => rsum R (fun b => rsum R (fun a =>
        rsum R (fun c₁ => rsum R (fun b₁ => rsum R (fun a₁ =>
          R.mul (R.mul (G c₁ b₁ a₁) (H (c - c₁) (b - b₁) (a - a₁)))
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R))
                (psPow (psRing (psRing R)) W₁ (a₁ + (a - a₁)))
                (psPow (psRing (psRing R)) W₂ (b₁ + (b - b₁))))
              (psPow (psRing (psRing R)) W₃ (c₁ + (c - c₁)))) j k i))
          (a + 1)) (b + 1)) (c + 1)) (i + k + j + 1)) (i + k + j + 1))
        (i + k + j + 1)
      = rsum R (fun c => rsum R (fun b => rsum R (fun a =>
          rsum R (fun c₁ => rsum R (fun b₁ => rsum R (fun a₁ =>
            R.mul (R.mul (G c₁ b₁ a₁) (H (c - c₁) (b - b₁) (a - a₁)))
              ((psMul (psRing (psRing R))
                (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                  (psPow (psRing (psRing R)) W₂ b))
                (psPow (psRing (psRing R)) W₃ c)) j k i)) (a + 1)) (b + 1))
            (c + 1)) (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) :=
    rsum_congr R (i + k + j + 1) (fun c _ =>
      rsum_congr R (i + k + j + 1) (fun b _ =>
        rsum_congr R (i + k + j + 1) (fun a _ =>
          rsum_congr R (c + 1) (fun c₁ hc₁ =>
            rsum_congr R (b + 1) (fun b₁ hb₁ =>
              rsum_congr R (a + 1) (fun a₁ ha₁ => by
                rw [show a₁ + (a - a₁) = a by omega,
                  show b₁ + (b - b₁) = b by omega,
                  show c₁ + (c - c₁) = c by omega]))))))
  -- 仕上げ
  rw [hLHS, hRHS,
    show psMul (psRing (psRing R))
        (ps3Fam_sum R (fun c => ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
          ps3Smul R (G c b a)
            (psMul (psRing (psRing R))
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ c))) (i + k + j + 1))
          (i + k + j + 1)) (i + k + j + 1))
        (ps3Fam_sum R (fun c => ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
          ps3Smul R (H c b a)
            (psMul (psRing (psRing R))
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ c))) (i + k + j + 1))
          (i + k + j + 1)) (i + k + j + 1)) j k i
      = ps3Fam_sum R (fun c₁ => ps3Fam_sum R (fun b₁ =>
          ps3Fam_sum R (fun a₁ => ps3Fam_sum R (fun c₂ =>
            ps3Fam_sum R (fun b₂ => ps3Fam_sum R (fun a₂ =>
              ps3Smul R (R.mul (G c₁ b₁ a₁) (H c₂ b₂ a₂))
                (psMul (psRing (psRing R))
                  (psMul (psRing (psRing R))
                    (psPow (psRing (psRing R)) W₁ (a₁ + a₂))
                    (psPow (psRing (psRing R)) W₂ (b₁ + b₂)))
                  (psPow (psRing (psRing R)) W₃ (c₁ + c₂))))
              (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1))
            (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) j k i from
      congrFun (congrFun (congrFun hfam j) k) i,
    hhex, hcollapse]

/-! ## ps3Comp3 は truncated ring hom -/

/-- **定理 (M70F-6a): 1 の代入** — 1∘(W₁,W₂,W₃) = 1
    （(c,b,a) = (0,0,0) への三重一点集中和。M70a の ps23Comp_one の
    三変数ミラー）。 -/
theorem ps3Comp3_one (R : CRing) (W₁ W₂ W₃ : PS3 R) :
    ps3Comp3 R (psOne (psRing (psRing R))) W₁ W₂ W₃
      = (psRing (psRing (psRing R))).one := by
  funext j k i
  show rsum R (fun c => rsum R (fun b => rsum R (fun a =>
      R.mul (psOne (psRing (psRing R)) c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i)) (i + k + j + 1))
      (i + k + j + 1)) (i + k + j + 1)
    = (psRing (psRing (psRing R))).one j k i
  -- c の和を c = 0 に集中
  have houter : rsum R (fun c => rsum R (fun b => rsum R (fun a =>
      R.mul (psOne (psRing (psRing R)) c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ c)) j k i)) (i + k + j + 1))
      (i + k + j + 1)) (i + k + j + 1)
      = rsum R (fun b => rsum R (fun a =>
          R.mul (psOne (psRing (psRing R)) 0 b a)
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ b))
              (psPow (psRing (psRing R)) W₃ 0)) j k i)) (i + k + j + 1))
          (i + k + j + 1) :=
    rsum_single R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul (psOne (psRing (psRing R)) c b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ c)) j k i)) (i + k + j + 1))
        (i + k + j + 1)) 0 (i + k + j + 1) (by omega)
      (fun c _ hc => by
        show rsum R (fun b => rsum R (fun a =>
            R.mul (psOne (psRing (psRing R)) c b a)
              ((psMul (psRing (psRing R))
                (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                  (psPow (psRing (psRing R)) W₂ b))
                (psPow (psRing (psRing R)) W₃ c)) j k i)) (i + k + j + 1))
            (i + k + j + 1) = R.zero
        have hz : rsum R (fun b => rsum R (fun a =>
              R.mul (psOne (psRing (psRing R)) c b a)
                ((psMul (psRing (psRing R))
                  (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                    (psPow (psRing (psRing R)) W₂ b))
                  (psPow (psRing (psRing R)) W₃ c)) j k i)) (i + k + j + 1))
              (i + k + j + 1)
            = rsum R (fun _ => R.zero) (i + k + j + 1) :=
          rsum_congr R (i + k + j + 1) (fun b _ => by
            have hz2 : rsum R (fun a =>
                  R.mul (psOne (psRing (psRing R)) c b a)
                    ((psMul (psRing (psRing R))
                      (psMul (psRing (psRing R))
                        (psPow (psRing (psRing R)) W₁ a)
                        (psPow (psRing (psRing R)) W₂ b))
                      (psPow (psRing (psRing R)) W₃ c)) j k i))
                  (i + k + j + 1)
                = rsum R (fun _ => R.zero) (i + k + j + 1) :=
              rsum_congr R (i + k + j + 1) (fun a _ => by
                rw [show psOne (psRing (psRing R)) c
                    = (psRing (psRing R)).zero from if_neg hc]
                exact R.zero_mul _)
            show rsum R (fun a =>
                R.mul (psOne (psRing (psRing R)) c b a)
                  ((psMul (psRing (psRing R))
                    (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                      (psPow (psRing (psRing R)) W₂ b))
                    (psPow (psRing (psRing R)) W₃ c)) j k i))
                (i + k + j + 1) = R.zero
            rw [hz2]
            exact rsum_const_zero R (i + k + j + 1))
        rw [hz]
        exact rsum_const_zero R (i + k + j + 1))
  rw [houter]
  -- b の和を b = 0 に集中
  have hmid : rsum R (fun b => rsum R (fun a =>
      R.mul (psOne (psRing (psRing R)) 0 b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ b))
          (psPow (psRing (psRing R)) W₃ 0)) j k i)) (i + k + j + 1))
      (i + k + j + 1)
      = rsum R (fun a =>
          R.mul (psOne (psRing (psRing R)) 0 0 a)
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ 0))
              (psPow (psRing (psRing R)) W₃ 0)) j k i)) (i + k + j + 1) :=
    rsum_single R (fun b => rsum R (fun a =>
        R.mul (psOne (psRing (psRing R)) 0 b a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ b))
            (psPow (psRing (psRing R)) W₃ 0)) j k i)) (i + k + j + 1))
      0 (i + k + j + 1) (by omega)
      (fun b _ hb => by
        show rsum R (fun a =>
            R.mul (psOne (psRing (psRing R)) 0 b a)
              ((psMul (psRing (psRing R))
                (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                  (psPow (psRing (psRing R)) W₂ b))
                (psPow (psRing (psRing R)) W₃ 0)) j k i)) (i + k + j + 1)
          = R.zero
        have hz : rsum R (fun a =>
              R.mul (psOne (psRing (psRing R)) 0 b a)
                ((psMul (psRing (psRing R))
                  (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                    (psPow (psRing (psRing R)) W₂ b))
                  (psPow (psRing (psRing R)) W₃ 0)) j k i)) (i + k + j + 1)
            = rsum R (fun _ => R.zero) (i + k + j + 1) :=
          rsum_congr R (i + k + j + 1) (fun a _ => by
            rw [show psOne (psRing (psRing R)) 0 b = (psRing R).zero from by
              show (if b = 0 then (psRing R).one else (psRing R).zero)
                = (psRing R).zero
              exact if_neg hb]
            exact R.zero_mul _)
        rw [hz]
        exact rsum_const_zero R (i + k + j + 1))
  rw [hmid]
  -- a の和を a = 0 に集中
  have hinner : rsum R (fun a =>
      R.mul (psOne (psRing (psRing R)) 0 0 a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
            (psPow (psRing (psRing R)) W₂ 0))
          (psPow (psRing (psRing R)) W₃ 0)) j k i)) (i + k + j + 1)
      = R.mul (psOne (psRing (psRing R)) 0 0 0)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ 0)
              (psPow (psRing (psRing R)) W₂ 0))
            (psPow (psRing (psRing R)) W₃ 0)) j k i) :=
    rsum_single R (fun a =>
        R.mul (psOne (psRing (psRing R)) 0 0 a)
          ((psMul (psRing (psRing R))
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
              (psPow (psRing (psRing R)) W₂ 0))
            (psPow (psRing (psRing R)) W₃ 0)) j k i)) 0 (i + k + j + 1)
      (by omega)
      (fun a _ ha => by
        show R.mul (psOne (psRing (psRing R)) 0 0 a)
            ((psMul (psRing (psRing R))
              (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ a)
                (psPow (psRing (psRing R)) W₂ 0))
              (psPow (psRing (psRing R)) W₃ 0)) j k i) = R.zero
        rw [show psOne (psRing (psRing R)) 0 0 a = R.zero from by
          show (if a = 0 then R.one else R.zero) = R.zero
          exact if_neg ha]
        exact R.zero_mul _)
  rw [hinner,
    show psOne (psRing (psRing R)) 0 0 0 = R.one from rfl,
    show psMul (psRing (psRing R))
        (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ 0)
          (psPow (psRing (psRing R)) W₂ 0))
        (psPow (psRing (psRing R)) W₃ 0)
      = (psRing (psRing (psRing R))).one from by
      rw [show psMul (psRing (psRing R)) (psPow (psRing (psRing R)) W₁ 0)
          (psPow (psRing (psRing R)) W₂ 0)
          = (psRing (psRing (psRing R))).one from
        (psRing (psRing (psRing R))).one_mul
          ((psRing (psRing (psRing R))).one)]
      exact (psRing (psRing (psRing R))).one_mul
        ((psRing (psRing (psRing R))).one)]
  exact R.one_mul _

/-- **定理 (M70F-6b): 冪の代入** —
    (G∘(W₁,W₂,W₃))^m = (G^m)∘(W₁,W₂,W₃)（乗法性 M70F-5 の帰納適用 +
    1 の代入。M70a の ps23Comp_pow の三変数ミラー）。 -/
theorem ps3Comp3_pow (R : CRing) (G W₁ W₂ W₃ : PS3 R)
    (hW₁ : W₁ 0 0 0 = R.zero) (hW₂ : W₂ 0 0 0 = R.zero)
    (hW₃ : W₃ 0 0 0 = R.zero) : ∀ m,
    psPow (psRing (psRing R)) (ps3Comp3 R G W₁ W₂ W₃) m
      = ps3Comp3 R (psPow (psRing (psRing R)) G m) W₁ W₂ W₃ := by
  intro m
  induction m with
  | zero => exact (ps3Comp3_one R W₁ W₂ W₃).symm
  | succ m ih =>
    show psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) (ps3Comp3 R G W₁ W₂ W₃) m)
        (ps3Comp3 R G W₁ W₂ W₃)
      = ps3Comp3 R
          (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) G m) G)
          W₁ W₂ W₃
    rw [ih, ps3Comp3_mul R (psPow (psRing (psRing R)) G m) G W₁ W₂ W₃
      hW₁ hW₂ hW₃]

end IUT
