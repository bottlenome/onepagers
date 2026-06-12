/-
  IUT/FormalGroupEvalMult.lean — M73（ps21Comp の乗法性:
  逆元キャンペーン第二層）

  ps21Comp（2 変数法則への 1 変数代入、M72）の truncated ring hom 性
  （乗法性・1 の代入・冪の代入）を、結合則キャンペーンの M69a/M69b
  （ps23Comp 版）の精密な 1 変数ミラーで完全証明する。
  抽象四重和の再添字化 quad_sum_reindex（M69b）は係数環レベルの
  恒等式なのでそのまま再登板する。

  * M73-1 `psFam_sum` と代数則 — 1 変数族和（congr・右積/左積の分配・
    スカラー和の抽出 psSmul_rsum）
  * M73-2 `psMul_congr_le` — 次数 ≤ n の一致から積の係数一致（無条件版）
  * M73-3 `psPowPow_mul` — 冪積の結合 (P^{a₁}Q^{b₁})·(P^{a₂}Q^{b₂})
    = P^{a₁+a₂}Q^{b₁+b₂}
  * M73-4 `psSmul_mul_smul` — スカラー積の合成則 (c•A)·(d•B) = (cd)•(A·B)
    （1 変数では Cauchy 係数で直接証明）
  * M73-5 `ps21Comp_eq_fam` — 打ち切り安定性（M72 の pad の族和表示）
  * M73-6 `ps21Comp_mul` — **乗法性 (F·G)(P,Q) = F(P,Q)·G(P,Q)**（本丸）
  * M73-7 `ps21Comp_one` / `ps21Comp_pow` — 1 の代入 = 1・冪の代入

  次層で連鎖律（CR1/CR2 の 1 変数版・後合成）→ 逆元の検証。
  全て選択公理不使用。
-/
import IUT.FormalGroupEval

namespace IUT

/-! ## 1 変数族和の代数 -/

/-- **M73-1a: 族和** — (Fam v N)_n = Σ_{t<N} (v t)_n。 -/
def psFam_sum (R : CRing) (v : Nat → PS R) (N : Nat) : PS R :=
  fun n => rsum R (fun t => v t n) N

/-- 族和の項別書き換え。 -/
theorem psFam_congr (R : CRing) {v w : Nat → PS R} (N : Nat)
    (h : ∀ t, t < N → v t = w t) :
    psFam_sum R v N = psFam_sum R w N := by
  funext n
  exact rsum_congr R N (fun t ht => by rw [h t ht])

/-- **M73-1b: 族和は右からの積と分配** — (Fam v N)·W = Fam (v·W) N。 -/
theorem psFam_mul_right (R : CRing) (v : Nat → PS R) (W : PS R) :
    ∀ N, psMul R (psFam_sum R v N) W
      = psFam_sum R (fun t => psMul R (v t) W) N := by
  intro N
  induction N with
  | zero =>
    show psMul R (psFam_sum R v 0) W = _
    have h0 : psFam_sum R v 0 = (psRing R).zero := rfl
    rw [h0]
    exact CRing.zero_mul (psRing R) W
  | succ N ih =>
    show (psRing R).mul ((psRing R).add (psFam_sum R v N) (v N)) W
      = (psRing R).add (psFam_sum R (fun t => psMul R (v t) W) N)
          ((psRing R).mul (v N) W)
    have ih' : (psRing R).mul (psFam_sum R v N) W
        = psFam_sum R (fun t => psMul R (v t) W) N := ih
    rw [(psRing R).right_distrib (psFam_sum R v N) (v N) W, ih']

/-- **M73-1c: 族和は左からの積と分配** — W·(Fam v N) = Fam (W·v) N。 -/
theorem psFam_mul_left (R : CRing) (v : Nat → PS R) (W : PS R) :
    ∀ N, psMul R W (psFam_sum R v N)
      = psFam_sum R (fun t => psMul R W (v t)) N := by
  intro N
  induction N with
  | zero =>
    show psMul R W (psFam_sum R v 0) = _
    have h0 : psFam_sum R v 0 = (psRing R).zero := rfl
    rw [h0]
    exact CRing.mul_zero (psRing R) W
  | succ N ih =>
    show (psRing R).mul W ((psRing R).add (psFam_sum R v N) (v N))
      = (psRing R).add (psFam_sum R (fun t => psMul R W (v t)) N)
          ((psRing R).mul W (v N))
    have ih' : (psRing R).mul W (psFam_sum R v N)
        = psFam_sum R (fun t => psMul R W (v t)) N := ih
    rw [(psRing R).left_distrib W (psFam_sum R v N) (v N), ih']

/-- **M73-1d: スカラー和の抽出** —
    psSmul (Σ_{t<N} f t) A = Fam (fun t => psSmul (f t) A) N。 -/
theorem psSmul_rsum (R : CRing) (f : Nat → R.carrier) (A : PS R) :
    ∀ N, psSmul R (rsum R f N) A
      = psFam_sum R (fun t => psSmul R (f t) A) N := by
  intro N
  induction N with
  | zero =>
    funext n
    exact R.zero_mul (A n)
  | succ N ih =>
    funext n
    show R.mul (R.add (rsum R f N) (f N)) (A n)
      = R.add (psFam_sum R (fun t => psSmul R (f t) A) N n)
          (R.mul (f N) (A n))
    rw [R.right_distrib (rsum R f N) (f N) (A n)]
    have hih : R.mul (rsum R f N) (A n)
        = psFam_sum R (fun t => psSmul R (f t) A) N n :=
      congrFun ih n
    rw [hih]

/-! ## 積の係数一致と冪積の結合 -/

/-- **M73-2: 積の係数一致（無条件版）** — A と A'・B と B' が次数 ≤ n で
    一致するなら、積の次数 m ≤ n の係数は一致する。 -/
theorem psMul_congr_le (R : CRing) {A A' B B' : PS R} (n : Nat)
    (hA : ∀ m, m ≤ n → A m = A' m)
    (hB : ∀ m, m ≤ n → B m = B' m)
    (m : Nat) (hdeg : m ≤ n) :
    psMul R A B m = psMul R A' B' m := by
  show rsum R (fun k => R.mul (A k) (B (m - k))) (m + 1)
    = rsum R (fun k => R.mul (A' k) (B' (m - k))) (m + 1)
  exact rsum_congr R (m + 1) (fun k hk => by
    rw [hA k (by omega), hB (m - k) (by omega)])

/-- **M73-3: 冪積の結合** —
    (P^{a₁}Q^{b₁})·(P^{a₂}Q^{b₂}) = P^{a₁+a₂}Q^{b₁+b₂}。 -/
theorem psPowPow_mul (R : CRing) (P Q : PS R) (a₁ b₁ a₂ b₂ : Nat) :
    psMul R (psMul R (psPow R P a₁) (psPow R Q b₁))
      (psMul R (psPow R P a₂) (psPow R Q b₂))
    = psMul R (psPow R P (a₁ + a₂)) (psPow R Q (b₁ + b₂)) := by
  have hP : psPow R P (a₁ + a₂)
      = psMul R (psPow R P a₁) (psPow R P a₂) := by
    rw [psPow_eq_rpow R P (a₁ + a₂), rpow_add (psRing R) P a₁ a₂,
      ← psPow_eq_rpow R P a₁, ← psPow_eq_rpow R P a₂]
    rfl
  have hQ : psPow R Q (b₁ + b₂)
      = psMul R (psPow R Q b₁) (psPow R Q b₂) := by
    rw [psPow_eq_rpow R Q (b₁ + b₂), rpow_add (psRing R) Q b₁ b₂,
      ← psPow_eq_rpow R Q b₁, ← psPow_eq_rpow R Q b₂]
    rfl
  rw [hP, hQ]
  exact CRing.mul_mul_comm (psRing R)
    (psPow R P a₁) (psPow R Q b₁) (psPow R P a₂) (psPow R Q b₂)

/-- **M73-4: スカラー積の合成則** — (c•A)·(d•B) = (c·d)•(A·B)
    （1 変数 Cauchy 係数で直接）。 -/
theorem psSmul_mul_smul (R : CRing) (c d : R.carrier) (A B : PS R) :
    psMul R (psSmul R c A) (psSmul R d B)
      = psSmul R (R.mul c d) (psMul R A B) := by
  funext n
  show rsum R (fun k => R.mul (R.mul c (A k)) (R.mul d (B (n - k)))) (n + 1)
    = R.mul (R.mul c d) (rsum R (fun k => R.mul (A k) (B (n - k))) (n + 1))
  rw [rsum_mul_left R (fun k => R.mul (A k) (B (n - k))) (R.mul c d) (n + 1)]
  exact rsum_congr R (n + 1) (fun k _ =>
    CRing.mul_mul_comm R c (A k) d (B (n - k)))

/-! ## 打ち切り安定性 -/

/-- **M73-5: ps21Comp の族和表示（打ち切り安定性）** — n < N の係数で
    ps21Comp F P Q は境界 N の二重族和に一致する（M72 の pad の言い換え）。 -/
theorem ps21Comp_eq_fam (R : CRing) (F : PS2 R) (P Q : PS R)
    (hP : P 0 = R.zero) (hQ : Q 0 = R.zero)
    (N n : Nat) (hN : n < N) :
    ps21Comp R F P Q n
      = psFam_sum R (fun b => psFam_sum R (fun a =>
          psSmul R (F b a)
            (psMul R (psPow R P a) (psPow R Q b))) N) N n := by
  show ps21Comp R F P Q n
    = rsum R (fun b => rsum R (fun a =>
        R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n)) N) N
  exact ps21Comp_pad R F P Q hP hQ N n hN

/-! ## 乗法性 -/

/-- **定理 (M73-6): ps21Comp の乗法性** —
    (F·G)(P,Q) = F(P,Q)·G(P,Q)（P(0) = Q(0) = 0）。
    M69b の ps23Comp_mul の 1 変数ミラー（quad_sum_reindex 再登板）。 -/
theorem ps21Comp_mul (R : CRing) (F G : PS2 R) (P Q : PS R)
    (hP : P 0 = R.zero) (hQ : Q 0 = R.zero) :
    ps21Comp R (psMul (psRing R) F G) P Q
      = psMul R (ps21Comp R F P Q) (ps21Comp R G P Q) := by
  funext n
  -- 右辺: 因子を境界 N = n+1 の族和に置換
  have hRHS : psMul R (ps21Comp R F P Q) (ps21Comp R G P Q) n
      = psMul R
          (psFam_sum R (fun b => psFam_sum R (fun a =>
            psSmul R (F b a)
              (psMul R (psPow R P a) (psPow R Q b))) (n + 1)) (n + 1))
          (psFam_sum R (fun b => psFam_sum R (fun a =>
            psSmul R (G b a)
              (psMul R (psPow R P a) (psPow R Q b))) (n + 1)) (n + 1)) n :=
    psMul_congr_le R n
      (fun m h => ps21Comp_eq_fam R F P Q hP hQ (n + 1) m (by omega))
      (fun m h => ps21Comp_eq_fam R G P Q hP hQ (n + 1) m (by omega))
      n (Nat.le_refl n)
  -- 族和の積を四重族和に展開（環レベル）
  have hfam : psMul R
      (psFam_sum R (fun b => psFam_sum R (fun a =>
        psSmul R (F b a)
          (psMul R (psPow R P a) (psPow R Q b))) (n + 1)) (n + 1))
      (psFam_sum R (fun b => psFam_sum R (fun a =>
        psSmul R (G b a)
          (psMul R (psPow R P a) (psPow R Q b))) (n + 1)) (n + 1))
      = psFam_sum R (fun b₁ => psFam_sum R (fun a₁ =>
          psFam_sum R (fun b₂ => psFam_sum R (fun a₂ =>
            psSmul R (R.mul (F b₁ a₁) (G b₂ a₂))
              (psMul R (psPow R P (a₁ + a₂)) (psPow R Q (b₁ + b₂))))
            (n + 1)) (n + 1)) (n + 1)) (n + 1) := by
    rw [psFam_mul_right R (fun b₁ => psFam_sum R (fun a₁ =>
      psSmul R (F b₁ a₁)
        (psMul R (psPow R P a₁) (psPow R Q b₁))) (n + 1)) _ (n + 1)]
    refine psFam_congr R (n + 1) (fun b₁ _ => ?_)
    rw [psFam_mul_right R (fun a₁ =>
      psSmul R (F b₁ a₁)
        (psMul R (psPow R P a₁) (psPow R Q b₁))) _ (n + 1)]
    refine psFam_congr R (n + 1) (fun a₁ _ => ?_)
    rw [psFam_mul_left R (fun b₂ => psFam_sum R (fun a₂ =>
      psSmul R (G b₂ a₂)
        (psMul R (psPow R P a₂) (psPow R Q b₂))) (n + 1)) _ (n + 1)]
    refine psFam_congr R (n + 1) (fun b₂ _ => ?_)
    rw [psFam_mul_left R (fun a₂ =>
      psSmul R (G b₂ a₂)
        (psMul R (psPow R P a₂) (psPow R Q b₂))) _ (n + 1)]
    refine psFam_congr R (n + 1) (fun a₂ _ => ?_)
    rw [psSmul_mul_smul R (F b₁ a₁) (G b₂ a₂)
      (psMul R (psPow R P a₁) (psPow R Q b₁))
      (psMul R (psPow R P a₂) (psPow R Q b₂)),
      psPowPow_mul R P Q a₁ b₁ a₂ b₂]
  -- 左辺: 打ち切り安定性 + Cauchy 展開
  have hLHS : ps21Comp R (psMul (psRing R) F G) P Q n
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ =>
            R.mul (R.mul (F b₁ a₁) (G (b - b₁) (a - a₁)))
              (psMul R (psPow R P a) (psPow R Q b) n)) (a + 1)) (b + 1))
          (n + 1)) (n + 1) := by
    rw [ps21Comp_eq_fam R (psMul (psRing R) F G) P Q hP hQ
      (n + 1) n (by omega)]
    show rsum R (fun b => rsum R (fun a =>
        R.mul (psMul (psRing R) F G b a)
          (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1) = _
    refine rsum_congr R (n + 1) (fun b _ => ?_)
    refine rsum_congr R (n + 1) (fun a _ => ?_)
    rw [ps2Mul_coeff R F G b a,
      rsum_mul_right R _
        (psMul R (psPow R P a) (psPow R Q b) n) (b + 1)]
    refine rsum_congr R (b + 1) (fun b₁ _ => ?_)
    rw [rsum_mul_right R _
      (psMul R (psPow R P a) (psPow R Q b) n) (a + 1)]
  -- 四重族和の係数 = 再添字化した四重和
  have hquad : psFam_sum R (fun b₁ => psFam_sum R (fun a₁ =>
        psFam_sum R (fun b₂ => psFam_sum R (fun a₂ =>
          psSmul R (R.mul (F b₁ a₁) (G b₂ a₂))
            (psMul R (psPow R P (a₁ + a₂)) (psPow R Q (b₁ + b₂))))
          (n + 1)) (n + 1)) (n + 1)) (n + 1) n
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ =>
            R.mul (R.mul (F b₁ a₁) (G (b - b₁) (a - a₁)))
              (psMul R (psPow R P (a₁ + (a - a₁)))
                (psPow R Q (b₁ + (b - b₁))) n))
            (a + 1)) (b + 1)) (n + 1)) (n + 1) :=
    quad_sum_reindex R (fun b₁ a₁ b₂ a₂ =>
        R.mul (R.mul (F b₁ a₁) (G b₂ a₂))
          (psMul R (psPow R P (a₁ + a₂)) (psPow R Q (b₁ + b₂)) n))
      n
      (fun b₁ a₁ b₂ a₂ h => by
        show R.mul (R.mul (F b₁ a₁) (G b₂ a₂))
            (psMul R (psPow R P (a₁ + a₂)) (psPow R Q (b₁ + b₂)) n)
          = R.zero
        rw [psPowPow_low R P Q hP hQ (a₁ + a₂) (b₁ + b₂) n (by omega)]
        exact R.mul_zero _)
      (fun b₁ a₁ b₂ a₂ h => by
        show R.mul (R.mul (F b₁ a₁) (G b₂ a₂))
            (psMul R (psPow R P (a₁ + a₂)) (psPow R Q (b₁ + b₂)) n)
          = R.zero
        rw [psPowPow_low R P Q hP hQ (a₁ + a₂) (b₁ + b₂) n (by omega)]
        exact R.mul_zero _)
  -- 添字の簡約 a₁+(a−a₁) = a・b₁+(b−b₁) = b
  have hcollapse : rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
        rsum R (fun a₁ =>
          R.mul (R.mul (F b₁ a₁) (G (b - b₁) (a - a₁)))
            (psMul R (psPow R P (a₁ + (a - a₁)))
              (psPow R Q (b₁ + (b - b₁))) n))
          (a + 1)) (b + 1)) (n + 1)) (n + 1)
      = rsum R (fun b => rsum R (fun a => rsum R (fun b₁ =>
          rsum R (fun a₁ =>
            R.mul (R.mul (F b₁ a₁) (G (b - b₁) (a - a₁)))
              (psMul R (psPow R P a) (psPow R Q b) n)) (a + 1)) (b + 1))
          (n + 1)) (n + 1) :=
    rsum_congr R (n + 1) (fun b _ =>
      rsum_congr R (n + 1) (fun a _ =>
        rsum_congr R (b + 1) (fun b₁ hb₁ =>
          rsum_congr R (a + 1) (fun a₁ ha₁ => by
            rw [show a₁ + (a - a₁) = a by omega,
              show b₁ + (b - b₁) = b by omega]))))
  rw [hLHS, hRHS,
    show psMul R
        (psFam_sum R (fun b => psFam_sum R (fun a =>
          psSmul R (F b a)
            (psMul R (psPow R P a) (psPow R Q b))) (n + 1)) (n + 1))
        (psFam_sum R (fun b => psFam_sum R (fun a =>
          psSmul R (G b a)
            (psMul R (psPow R P a) (psPow R Q b))) (n + 1)) (n + 1)) n
      = psFam_sum R (fun b₁ => psFam_sum R (fun a₁ =>
          psFam_sum R (fun b₂ => psFam_sum R (fun a₂ =>
            psSmul R (R.mul (F b₁ a₁) (G b₂ a₂))
              (psMul R (psPow R P (a₁ + a₂)) (psPow R Q (b₁ + b₂))))
            (n + 1)) (n + 1)) (n + 1)) (n + 1) n from
      congrFun hfam n,
    hquad, hcollapse]

/-! ## 1 の代入と冪の代入 -/

/-- **M73-7a: 1 の代入** — 1(P,Q) = 1（(b,a) = (0,0) への二重一点集中）。 -/
theorem ps21Comp_one (R : CRing) (P Q : PS R) :
    ps21Comp R (psRing (psRing R)).one P Q = psOne R := by
  funext n
  show rsum R (fun b => rsum R (fun a =>
      R.mul (psOne (psRing R) b a)
        (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1)
    = psOne R n
  have houter : rsum R (fun b => rsum R (fun a =>
      R.mul (psOne (psRing R) b a)
        (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1)
      = rsum R (fun a =>
          R.mul (psOne (psRing R) 0 a)
            (psMul R (psPow R P a) (psPow R Q 0) n)) (n + 1) :=
    rsum_single R (fun b => rsum R (fun a =>
        R.mul (psOne (psRing R) b a)
          (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) 0 (n + 1)
      (by omega)
      (fun b _ hb => by
        show rsum R (fun a =>
            R.mul (psOne (psRing R) b a)
              (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1) = R.zero
        have hz : rsum R (fun a =>
            R.mul (psOne (psRing R) b a)
              (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)
            = rsum R (fun _ => R.zero) (n + 1) :=
          rsum_congr R (n + 1) (fun a _ => by
            rw [show psOne (psRing R) b a = R.zero from by
              show (if b = 0 then (psRing R).one else (psRing R).zero) a
                = R.zero
              rw [if_neg hb]
              rfl]
            exact R.zero_mul _)
        rw [hz]
        exact rsum_const_zero R (n + 1))
  rw [houter]
  have hinner : rsum R (fun a =>
      R.mul (psOne (psRing R) 0 a)
        (psMul R (psPow R P a) (psPow R Q 0) n)) (n + 1)
      = R.mul (psOne (psRing R) 0 0)
          (psMul R (psPow R P 0) (psPow R Q 0) n) :=
    rsum_single R (fun a =>
        R.mul (psOne (psRing R) 0 a)
          (psMul R (psPow R P a) (psPow R Q 0) n)) 0 (n + 1)
      (by omega)
      (fun a _ ha => by
        show R.mul (psOne (psRing R) 0 a)
            (psMul R (psPow R P a) (psPow R Q 0) n) = R.zero
        rw [show psOne (psRing R) 0 a = R.zero from by
          show psOne R a = R.zero
          exact if_neg ha]
        exact R.zero_mul _)
  rw [hinner]
  have hone : psMul R (psPow R P 0) (psPow R Q 0) = psOne R :=
    (psRing R).one_mul ((psRing R).one)
  rw [hone]
  show R.mul R.one (psOne R n) = psOne R n
  exact R.one_mul _

/-- **M73-7b: 冪の代入** — (F^m)(P,Q) = (F(P,Q))^m（乗法性の帰納適用）。 -/
theorem ps21Comp_pow (R : CRing) (F : PS2 R) (P Q : PS R)
    (hP : P 0 = R.zero) (hQ : Q 0 = R.zero) :
    ∀ m, ps21Comp R (psPow (psRing R) F m) P Q
      = psPow R (ps21Comp R F P Q) m := by
  intro m
  induction m with
  | zero => exact ps21Comp_one R P Q
  | succ m ih =>
    show ps21Comp R (psMul (psRing R) (psPow (psRing R) F m) F) P Q
      = psMul R (psPow R (ps21Comp R F P Q) m) (ps21Comp R F P Q)
    rw [ps21Comp_mul R (psPow (psRing R) F m) F P Q hP hQ, ih]

end IUT
