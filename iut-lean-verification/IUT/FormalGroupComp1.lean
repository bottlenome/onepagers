/-
  IUT/FormalGroupComp1.lean — M70a（合成の代数と連鎖律 CR1: 結合則キャンペーン第九層）

  M69b の乗法性を起点に ps23Comp の環準同型性を完備化し、
  第一の連鎖律

    **f∘₃(F∘(P,Q)) = (f∘₂F)∘(P,Q)**   （CR1）

  を完全証明する。結合則の方程式検証で左辺 f∘₃assocL を
  「F の方程式が使える形」に変換する第一歩。

  * M70a-1 `ps23Comp_one` / `ps23Comp_add` — 1 の代入 = 1・F-加法性
    （乗法性 M69b と合わせ ps23Comp(−, P, Q) は truncated ring hom）
  * M70a-2 `ps2Mul_low_zero` / `ps2PowPow_low` — 二変数の積の下方消滅
    （M68 の三変数版の二変数ミラー）
  * M70a-3 `ps23Comp_pow` — **冪の代入** (F∘(P,Q))^m = (F^m)∘(P,Q)
    （乗法性の帰納適用）
  * M70a-4 `ps23Comp_comp1`（CR1） — f∘₃(F∘(P,Q)) = (f∘₂F)∘(P,Q)
    （係数ごとに: 冪の代入 + 族和表示 + m-和の内側への移送
    （rsum_exchange ×2）+ 打ち切り padding（F₀₀ = 0 の二変数 truncation））

  全て選択公理不使用。
-/
import IUT.FormalGroupMult

namespace IUT

/-! ## ps23Comp は truncated ring hom -/

/-- **M70a-1a: 1 の代入** — 1∘(P,Q) = 1（(b,a) = (0,0) への
    二重一点集中和）。 -/
theorem ps23Comp_one (R : CRing) (P Q : PS3 R) :
    ps23Comp R (psOne (psRing R)) P Q
      = (psRing (psRing (psRing R))).one := by
  funext j k i
  show rsum R (fun b => rsum R (fun a =>
      R.mul (psOne (psRing R) b a)
        ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i))
      (i + k + j + 1)) (i + k + j + 1)
    = (psRing (psRing (psRing R))).one j k i
  have houter : rsum R (fun b => rsum R (fun a =>
      R.mul (psOne (psRing R) b a)
        ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i))
      (i + k + j + 1)) (i + k + j + 1)
      = rsum R (fun a =>
          R.mul (psOne (psRing R) 0 a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q 0)) j k i)) (i + k + j + 1) :=
    rsum_single R (fun b => rsum R (fun a =>
        R.mul (psOne (psRing R) b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)) (i + k + j + 1))
      0 (i + k + j + 1) (by omega)
      (fun b _ hb => by
        have hz : rsum R (fun a =>
            R.mul (psOne (psRing R) b a)
              ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                (psPow (psRing (psRing R)) Q b)) j k i))
            (i + k + j + 1)
            = rsum R (fun _ => R.zero) (i + k + j + 1) :=
          rsum_congr R (i + k + j + 1) (fun a _ => by
            rw [show psOne (psRing R) b = (psRing R).zero from if_neg hb]
            exact R.zero_mul _)
        show rsum R (fun a =>
            R.mul (psOne (psRing R) b a)
              ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
                (psPow (psRing (psRing R)) Q b)) j k i))
            (i + k + j + 1) = R.zero
        rw [hz]
        exact rsum_const_zero R (i + k + j + 1))
  rw [houter]
  have hinner : rsum R (fun a =>
      R.mul (psOne (psRing R) 0 a)
        ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q 0)) j k i)) (i + k + j + 1)
      = R.mul (psOne (psRing R) 0 0)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P 0)
            (psPow (psRing (psRing R)) Q 0)) j k i) :=
    rsum_single R (fun a =>
        R.mul (psOne (psRing R) 0 a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q 0)) j k i)) 0 (i + k + j + 1)
      (by omega)
      (fun a _ ha => by
        show R.mul (psOne (psRing R) 0 a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q 0)) j k i) = R.zero
        rw [show psOne (psRing R) 0 a = R.zero from by
          show (if a = 0 then R.one else R.zero) = R.zero
          rw [if_neg ha]]
        exact R.zero_mul _)
  rw [hinner,
    show psOne (psRing R) 0 0 = R.one from rfl,
    show psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P 0)
        (psPow (psRing (psRing R)) Q 0)
      = (psRing (psRing (psRing R))).one from
      (psRing (psRing (psRing R))).one_mul
        ((psRing (psRing (psRing R))).one)]
  exact R.one_mul _

/-- **M70a-1b: F-加法性** — (F + G)∘(P,Q) = F∘(P,Q) + G∘(P,Q)。 -/
theorem ps23Comp_add (R : CRing) (F G : PS2 R) (P Q : PS3 R) :
    ps23Comp R (psAdd (psRing R) F G) P Q
      = (psRing (psRing (psRing R))).add (ps23Comp R F P Q)
          (ps23Comp R G P Q) := by
  funext j k i
  show rsum R (fun b => rsum R (fun a =>
      R.mul (R.add (F b a) (G b a))
        ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i))
      (i + k + j + 1)) (i + k + j + 1)
    = R.add (ps23Comp R F P Q j k i) (ps23Comp R G P Q j k i)
  show rsum R (fun b => rsum R (fun a =>
      R.mul (R.add (F b a) (G b a))
        ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i))
      (i + k + j + 1)) (i + k + j + 1)
    = R.add
        (rsum R (fun b => rsum R (fun a => R.mul (F b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i))
          (i + k + j + 1)) (i + k + j + 1))
        (rsum R (fun b => rsum R (fun a => R.mul (G b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i))
          (i + k + j + 1)) (i + k + j + 1))
  rw [← rsum_add R _ _ (i + k + j + 1)]
  refine rsum_congr R (i + k + j + 1) (fun b _ => ?_)
  show rsum R (fun a => R.mul (R.add (F b a) (G b a))
      ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
        (psPow (psRing (psRing R)) Q b)) j k i)) (i + k + j + 1)
    = R.add
        (rsum R (fun a => R.mul (F b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)) (i + k + j + 1))
        (rsum R (fun a => R.mul (G b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)) (i + k + j + 1))
  rw [← rsum_add R _ _ (i + k + j + 1)]
  exact rsum_congr R (i + k + j + 1) (fun a _ =>
    R.right_distrib (F b a) (G b a) _)

/-! ## 二変数の積の下方消滅 -/

/-- **M70a-2a: 二変数の積の下方消滅**（M68 の二変数ミラー）。 -/
theorem ps2Mul_low_zero (R : CRing) (A B : PS2 R) (dA dB : Nat)
    (hA : ∀ b a, a + b < dA → A b a = R.zero)
    (hB : ∀ b a, a + b < dB → B b a = R.zero)
    (j i : Nat) (h : i + j < dA + dB) :
    psMul (psRing R) A B j i = R.zero := by
  rw [ps2Mul_coeff R A B j i]
  have hz : rsum R (fun k => rsum R (fun l =>
        R.mul (A k l) (B (j - k) (i - l))) (i + 1)) (j + 1)
      = rsum R (fun _ => R.zero) (j + 1) :=
    rsum_congr R (j + 1) (fun k hk => by
      have hz2 : rsum R (fun l =>
            R.mul (A k l) (B (j - k) (i - l))) (i + 1)
          = rsum R (fun _ => R.zero) (i + 1) :=
        rsum_congr R (i + 1) (fun l hl => by
          cases Nat.lt_or_ge (l + k) dA with
          | inl hlt =>
            rw [hA k l hlt]
            exact R.zero_mul _
          | inr hge =>
            rw [hB (j - k) (i - l) (by omega)]
            exact R.mul_zero _)
      rw [hz2]
      exact rsum_const_zero R (i + 1))
  rw [hz]
  exact rsum_const_zero R (j + 1)

/-- **M70a-2b: 二変数の冪積の下方消滅**。 -/
theorem ps2PowPow_low (R : CRing) (U V : PS2 R)
    (hU : U 0 0 = R.zero) (hV : V 0 0 = R.zero) (a b : Nat)
    (j i : Nat) (h : i + j < a + b) :
    psMul (psRing R) (psPow (psRing R) U a) (psPow (psRing R) V b)
      j i = R.zero :=
  ps2Mul_low_zero R (psPow (psRing R) U a) (psPow (psRing R) V b) a b
    (fun b' a' h' => ps2Pow_tcoeff_zero R U hU a a' b' h')
    (fun b' a' h' => ps2Pow_tcoeff_zero R V hV b a' b' h')
    j i h

/-! ## 冪の代入 -/

/-- **定理 (M70a-3): 冪の代入** — (F∘(P,Q))^m = (F^m)∘(P,Q)
    （乗法性 M69b の帰納適用 + 1 の代入）。 -/
theorem ps23Comp_pow (R : CRing) (F : PS2 R) (P Q : PS3 R)
    (hP : P 0 0 0 = R.zero) (hQ : Q 0 0 0 = R.zero) : ∀ m,
    psPow (psRing (psRing R)) (ps23Comp R F P Q) m
      = ps23Comp R (psPow (psRing R) F m) P Q := by
  intro m
  induction m with
  | zero => exact (ps23Comp_one R P Q).symm
  | succ m ih =>
    show psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) (ps23Comp R F P Q) m)
        (ps23Comp R F P Q)
      = ps23Comp R (psMul (psRing R) (psPow (psRing R) F m) F) P Q
    rw [ih, ps23Comp_mul R (psPow (psRing R) F m) F P Q hP hQ]

/-! ## 連鎖律 CR1 -/

/-- **定理 (M70a-4): 連鎖律 CR1** —
    f∘₃(F∘(P,Q)) = (f∘₂F)∘(P,Q)（F₀₀ = P₀₀₀ = Q₀₀₀ = 0）。
    結合則の方程式検証の第一の柱。 -/
theorem ps23Comp_comp1 (R : CRing) (f : PS R) (F : PS2 R) (P Q : PS3 R)
    (hF : F 0 0 = R.zero) (hP : P 0 0 0 = R.zero)
    (hQ : Q 0 0 0 = R.zero) :
    ps3Comp1 R f (ps23Comp R F P Q)
      = ps23Comp R (ps2Comp1 R f F) P Q := by
  funext j k i
  -- 左辺: 冪の代入 + 族和表示で三重和へ
  have hL : ps3Comp1 R f (ps23Comp R F P Q) j k i
      = rsum R (fun m => rsum R (fun b => rsum R (fun a =>
          R.mul (f m) (R.mul (psPow (psRing R) F m b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) := by
    show rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) (ps23Comp R F P Q) m j k i))
        (i + k + j + 1) = _
    refine rsum_congr R (i + k + j + 1) (fun m _ => ?_)
    rw [ps23Comp_pow R F P Q hP hQ m,
      ps23Comp_eq_fam R (psPow (psRing R) F m) P Q hP hQ
        (i + k + j + 1) j k i (by omega)]
    show R.mul (f m) (rsum R (fun b => rsum R (fun a =>
        R.mul (psPow (psRing R) F m b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i))
        (i + k + j + 1)) (i + k + j + 1)) = _
    rw [rsum_mul_left R _ (f m) (i + k + j + 1)]
    refine rsum_congr R (i + k + j + 1) (fun b _ => ?_)
    rw [rsum_mul_left R _ (f m) (i + k + j + 1)]
  -- 右辺: (f∘₂F) の係数の m-和を境界 N に padding して三重和へ
  have hR : ps23Comp R (ps2Comp1 R f F) P Q j k i
      = rsum R (fun b => rsum R (fun a => rsum R (fun m =>
          R.mul (R.mul (f m) (psPow (psRing R) F m b a))
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) := by
    show rsum R (fun b => rsum R (fun a =>
        R.mul (ps2Comp1 R f F b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i))
        (i + k + j + 1)) (i + k + j + 1) = _
    refine rsum_congr R (i + k + j + 1) (fun b hb => ?_)
    refine rsum_congr R (i + k + j + 1) (fun a ha => ?_)
    cases Nat.lt_or_ge (i + k + j) (a + b) with
    | inl hhigh =>
      -- 高総次数: T-因子が消滅して両辺 0
      rw [ps3PowPow_low R P Q hP hQ a b j k i hhigh,
        R.mul_zero (ps2Comp1 R f F b a)]
      have hz : rsum R (fun m =>
            R.mul (R.mul (f m) (psPow (psRing R) F m b a)) R.zero)
            (i + k + j + 1)
          = rsum R (fun _ => R.zero) (i + k + j + 1) :=
        rsum_congr R (i + k + j + 1) (fun m _ =>
          R.mul_zero (R.mul (f m) (psPow (psRing R) F m b a)))
      rw [hz, rsum_const_zero]
    | inr hlow =>
      -- 低総次数: m-和を境界 N に padding（F₀₀ = 0 の truncation）
      have hpad : rsum R (fun m => R.mul (f m)
            (psPow (psRing R) F m b a)) (i + k + j + 1)
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
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i) = _
      rw [← hpad,
        rsum_mul_right R (fun m => R.mul (f m) (psPow (psRing R) F m b a))
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i) (i + k + j + 1)]
  rw [hL, hR]
  -- m-和を内側へ移送（exchange ×2）+ 結合律
  have hx1 : rsum R (fun m => rsum R (fun b => rsum R (fun a =>
        R.mul (f m) (R.mul (psPow (psRing R) F m b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)))
        (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1)
      = rsum R (fun b => rsum R (fun m => rsum R (fun a =>
          R.mul (f m) (R.mul (psPow (psRing R) F m b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) :=
    rsum_exchange R (fun m b => rsum R (fun a =>
        R.mul (f m) (R.mul (psPow (psRing R) F m b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)))
        (i + k + j + 1)) (i + k + j + 1) (i + k + j + 1)
  rw [hx1]
  refine rsum_congr R (i + k + j + 1) (fun b _ => ?_)
  have hx2 : rsum R (fun m => rsum R (fun a =>
        R.mul (f m) (R.mul (psPow (psRing R) F m b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)))
        (i + k + j + 1)) (i + k + j + 1)
      = rsum R (fun a => rsum R (fun m =>
          R.mul (f m) (R.mul (psPow (psRing R) F m b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)))
          (i + k + j + 1)) (i + k + j + 1) :=
    rsum_exchange R (fun m a =>
        R.mul (f m) (R.mul (psPow (psRing R) F m b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)))
        (i + k + j + 1) (i + k + j + 1)
  rw [hx2]
  refine rsum_congr R (i + k + j + 1) (fun a _ => ?_)
  exact rsum_congr R (i + k + j + 1) (fun m _ =>
    (R.mul_assoc (f m) (psPow (psRing R) F m b a) _).symm)

end IUT
