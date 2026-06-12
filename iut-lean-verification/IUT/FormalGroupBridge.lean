/-
  M70c: 注入の橋渡し補題（結合則キャンペーン第十一層）

  結合則の方程式検証の接合部を担う橋渡し:
  - X^k の係数公式（X^k = 一点集中）と恒等代入 f∘X = f
  - 2→3 変数代入 ps23Comp に X 方向注入 psC f を与えると ps3Comp1 f P
    （Y 因子 Q は無関係に消える）
  - Y 方向注入 psMap psConstHom f を与えると ps3Comp1 f Q
  - 座標への 1→3 代入 f∘₃X = in3X f / f∘₃Y = in3Y f / f∘₃Z = in3Z f

  正直な範囲: 全て仮定なし（定数項条件も不要 — 両辺の打ち切り境界が
  i+k+j+1 で一致するため）。選択公理不使用。
-/
import IUT.FormalGroupComp2

namespace IUT

/-! ## X の冪の係数と恒等代入 -/

/-- **M70c-1a: X^k の係数公式** — (X^k)_n = δ_{n,k}。 -/
theorem psX_pow_coeff (R : CRing) : ∀ (k n : Nat),
    psPow R (psX R) k n = if n = k then R.one else R.zero := by
  intro k
  induction k with
  | zero =>
    intro n
    rfl
  | succ k ih =>
    intro n
    show rsum R (fun m => R.mul (psPow R (psX R) k m) (psX R (n - m))) (n + 1)
      = if n = k + 1 then R.one else R.zero
    cases Nat.lt_or_ge k (n + 1) with
    | inl hk =>
      have hz : ∀ m, m < n + 1 → m ≠ k →
          (fun m => R.mul (psPow R (psX R) k m) (psX R (n - m))) m
            = R.zero := by
        intro m _ hm
        show R.mul (psPow R (psX R) k m) (psX R (n - m)) = R.zero
        rw [ih m, if_neg hm, R.zero_mul]
      have hs := rsum_single R
        (fun m => R.mul (psPow R (psX R) k m) (psX R (n - m)))
        k (n + 1) hk hz
      rw [hs]
      show R.mul (psPow R (psX R) k k) (psX R (n - k))
        = if n = k + 1 then R.one else R.zero
      rw [ih k, if_pos rfl, R.one_mul]
      show (if n - k = 1 then R.one else R.zero)
        = if n = k + 1 then R.one else R.zero
      cases Nat.decEq n (k + 1) with
      | isTrue he =>
        rw [if_pos he, if_pos (show n - k = 1 by omega)]
      | isFalse he =>
        rw [if_neg he, if_neg (show ¬ n - k = 1 by omega)]
    | inr hk =>
      have hc : rsum R
          (fun m => R.mul (psPow R (psX R) k m) (psX R (n - m))) (n + 1)
          = rsum R (fun _ => R.zero) (n + 1) := by
        apply rsum_congr
        intro m hm
        show R.mul (psPow R (psX R) k m) (psX R (n - m)) = R.zero
        rw [ih m, if_neg (show ¬ m = k by omega), R.zero_mul]
      rw [hc, rsum_const_zero R (n + 1),
        if_neg (show ¬ n = k + 1 by omega)]

/-- **M70c-1b: 恒等代入** f∘X = f（psComp_X の右版）。 -/
theorem psComp_X_right (R : CRing) (f : PS R) :
    psComp R f (psX R) = f := by
  funext n
  show rsum R (fun m => R.mul (f m) (psPow R (psX R) m n)) (n + 1) = f n
  have hz : ∀ m, m < n + 1 → m ≠ n →
      (fun m => R.mul (f m) (psPow R (psX R) m n)) m = R.zero := by
    intro m _ hm
    show R.mul (f m) (psPow R (psX R) m n) = R.zero
    rw [psX_pow_coeff R m n, if_neg (show ¬ n = m by omega), R.mul_zero]
  have hs := rsum_single R
    (fun m => R.mul (f m) (psPow R (psX R) m n)) n (n + 1) (by omega) hz
  rw [hs]
  show R.mul (f n) (psPow R (psX R) n n) = f n
  rw [psX_pow_coeff R n n, if_pos rfl, R.mul_comm, R.one_mul]

/-! ## 注入と ps23Comp の橋渡し -/

/-- **M70c-2a: X 方向注入の代入** —
    (psC f)∘(P,Q) = f∘₃P（F が Y を含まないので Q は消える。仮定なし）。 -/
theorem ps23Comp_inX (R : CRing) (f : PS R) (P Q : PS3 R) :
    ps23Comp R (psC (psRing R) f) P Q = ps3Comp1 R f P := by
  funext j k i
  show rsum R (fun b => rsum R (fun a =>
      R.mul (psC (psRing R) f b a)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i))
      (i + k + j + 1)) (i + k + j + 1)
    = rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) P m j k i)) (i + k + j + 1)
  have hz : ∀ b, b < i + k + j + 1 → b ≠ 0 →
      (fun b => rsum R (fun a =>
        R.mul (psC (psRing R) f b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i))
        (i + k + j + 1)) b = R.zero := by
    intro b _ hb
    show rsum R (fun a =>
        R.mul (psC (psRing R) f b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i))
        (i + k + j + 1) = R.zero
    have hc : rsum R (fun a =>
        R.mul (psC (psRing R) f b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i))
        (i + k + j + 1)
        = rsum R (fun _ => R.zero) (i + k + j + 1) := by
      apply rsum_congr
      intro a _
      show R.mul (psC (psRing R) f b a)
          ((psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i) = R.zero
      have hcf : psC (psRing R) f b a = R.zero := by
        show (if b = 0 then f else (psRing R).zero) a = R.zero
        rw [if_neg hb]
        rfl
      rw [hcf, R.zero_mul]
    rw [hc]
    exact rsum_const_zero R (i + k + j + 1)
  have hs := rsum_single R (fun b => rsum R (fun a =>
      R.mul (psC (psRing R) f b a)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i))
      (i + k + j + 1)) 0 (i + k + j + 1) (by omega) hz
  rw [hs]
  show rsum R (fun a =>
      R.mul (psC (psRing R) f 0 a)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q 0)) j k i))
      (i + k + j + 1)
    = rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) P m j k i)) (i + k + j + 1)
  apply rsum_congr
  intro a _
  show R.mul (psC (psRing R) f 0 a)
      ((psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) P a)
        (psPow (psRing (psRing R)) Q 0)) j k i)
    = R.mul (f a) (psPow (psRing (psRing R)) P a j k i)
  have hone : psMul (psRing (psRing R))
      (psPow (psRing (psRing R)) P a)
      (psPow (psRing (psRing R)) Q 0)
      = psPow (psRing (psRing R)) P a := by
    show (psRing (psRing (psRing R))).mul
        (psPow (psRing (psRing R)) P a)
        (psRing (psRing (psRing R))).one
      = psPow (psRing (psRing R)) P a
    rw [(psRing (psRing (psRing R))).mul_comm]
    exact (psRing (psRing (psRing R))).one_mul _
  rw [hone]
  rfl

/-- **M70c-2b: Y 方向注入の代入** —
    (psMap psConstHom f)∘(P,Q) = f∘₃Q（F が X を含まないので P は消える）。 -/
theorem ps23Comp_inY (R : CRing) (f : PS R) (P Q : PS3 R) :
    ps23Comp R (psMap (psConstHom R) f) P Q = ps3Comp1 R f Q := by
  funext j k i
  show rsum R (fun b => rsum R (fun a =>
      R.mul (psMap (psConstHom R) f b a)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i))
      (i + k + j + 1)) (i + k + j + 1)
    = rsum R (fun m => R.mul (f m)
        (psPow (psRing (psRing R)) Q m j k i)) (i + k + j + 1)
  apply rsum_congr
  intro b _
  show rsum R (fun a =>
      R.mul (psMap (psConstHom R) f b a)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i))
      (i + k + j + 1)
    = R.mul (f b) (psPow (psRing (psRing R)) Q b j k i)
  have hz : ∀ a, a < i + k + j + 1 → a ≠ 0 →
      (fun a => R.mul (psMap (psConstHom R) f b a)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i)) a = R.zero := by
    intro a _ ha
    show R.mul (psMap (psConstHom R) f b a)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i) = R.zero
    have hcf : psMap (psConstHom R) f b a = R.zero := by
      show (if a = 0 then f b else R.zero) = R.zero
      rw [if_neg ha]
    rw [hcf, R.zero_mul]
  have hs := rsum_single R
    (fun a => R.mul (psMap (psConstHom R) f b a)
      ((psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) P a)
        (psPow (psRing (psRing R)) Q b)) j k i))
    0 (i + k + j + 1) (by omega) hz
  rw [hs]
  show R.mul (psMap (psConstHom R) f b 0)
      ((psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) P 0)
        (psPow (psRing (psRing R)) Q b)) j k i)
    = R.mul (f b) (psPow (psRing (psRing R)) Q b j k i)
  have hone : psMul (psRing (psRing R))
      (psPow (psRing (psRing R)) P 0)
      (psPow (psRing (psRing R)) Q b)
      = psPow (psRing (psRing R)) Q b := by
    show (psRing (psRing (psRing R))).mul
        (psRing (psRing (psRing R))).one
        (psPow (psRing (psRing R)) Q b)
      = psPow (psRing (psRing R)) Q b
    exact (psRing (psRing (psRing R))).one_mul _
  rw [hone]
  rfl

/-! ## 座標への 1→3 代入 -/

/-- **M70c-3a**: f∘₃X = in3X f。 -/
theorem ps3Comp1_ps3X (R : CRing) (f : PS R) :
    ps3Comp1 R f (ps3X R) = in3X R f := by
  rw [ps3X_eq_in3X, ps3Comp1_in3X, psComp_X_right]

/-- **M70c-3b**: f∘₃Y = in3Y f。 -/
theorem ps3Comp1_ps3Y (R : CRing) (f : PS R) :
    ps3Comp1 R f (ps3Y R) = in3Y R f := by
  rw [ps3Y_eq_in3Y, ps3Comp1_in3Y, psComp_X_right]

/-- **M70c-3c**: f∘₃Z = in3Z f。 -/
theorem ps3Comp1_ps3Z (R : CRing) (f : PS R) :
    ps3Comp1 R f (ps3Z R) = in3Z R f := by
  rw [ps3Z_eq_in3Z, ps3Comp1_in3Z, psComp_X_right]

end IUT
