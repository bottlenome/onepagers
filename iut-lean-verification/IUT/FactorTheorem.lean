/-
  IUT/FactorTheorem.lean — M96（因数定理と根の個数: 柱B 分類の最終鍵）

  **「次数 d・最高次係数 ≠ 0 の多項式は d+1 個の相異なる根を持てない」**
  を任意の可換環 + 零因子なし（NoZeroDiv、M90F）の下で完全証明する。
  これが M95（σ(λ) ∈ Λ₁・Eisenstein 根への分類）と M84F（p−1 個の
  相異なる共役根）を「σ(λ) = ω(a)λ 完全分類」に閉じる最後の鍵。

  設計の鍵: 除算恒等式 P(x) = (x−r)·Q(x) + P(r) を、商係数
  q_k = Σ_i c_{k+1+i} r^i の**明示式**に対し **d の帰納 + 最高次
  剥がし**で証明する。帰納の一段で現れる差は係数 1 本分の
  c_{d+1}(x^{d+1} − r^{d+1}) であり、これは**幾何級数の因数分解**
  x^k − r^k = (x−r)·Σ x^j r^{k−1−j} が吸収する——三角形二重和の
  交換（重い）を完全に回避する経路。

  * M96-1 `pEval` / `pEval_zero` / `pEval_succ` — 多項式の評価
  * M96-2 `geoSum` / `geom_factor` — **幾何級数の因数分解**
  * M96-3 `qCoeff` / `qCoeff_top` / `qCoeff_lead` / `qCoeff_peel` —
    商係数の明示式とその簿記
  * M96-4 `lin_div` / `pEval_div` — **除算恒等式（本丸 1）**
  * M96-5 `pEval_root_factor` / `roots_bound` — **根の個数 ≤ 次数
    （本丸 2）**: NoZeroDiv の下で d+1 個の相異なる根は矛盾
  * M96-6 `cBin` / `pEval_bin` / `bin_roots_bound` — 二項多項式
    x^n − a への特化（n+1 個の相異なる n 乗根は矛盾）
  * M96-7 `eis_roots_bound` — **Eisenstein 方程式 t^{p−1} = −π の
    相異なる根は p−1 個以下**（柱B 上界の最終段、1 ≠ 0 は M82F の
    eis_one_ne_zero を再利用）

  M84F の共役族（p−1 個の相異なる根）との結合による
  「Λ₁ = {0} ∪ {ω(a)λ}」の明示分類は次層。全て選択公理不使用。
-/
import IUT.EisensteinUpper

namespace IUT

/-! ## 多項式の評価 -/

/-- **M96-1a: 多項式の評価** P(x) = Σ_{k≤d} c_k x^k。 -/
def pEval (R : CRing) (c : Nat → R.carrier) (d : Nat) (x : R.carrier) :
    R.carrier :=
  rsum R (fun k => R.mul (c k) (rpow R x k)) (d + 1)

theorem pEval_zero (R : CRing) (c : Nat → R.carrier) (x : R.carrier) :
    pEval R c 0 x = c 0 := by
  show R.add R.zero (R.mul (c 0) R.one) = c 0
  rw [R.zero_add, R.mul_one]

/-- 最高次剥がし（定義から）。 -/
theorem pEval_succ (R : CRing) (c : Nat → R.carrier) (d : Nat)
    (x : R.carrier) :
    pEval R c (d + 1) x
      = R.add (pEval R c d x) (R.mul (c (d + 1)) (rpow R x (d + 1))) := rfl

/-! ## 幾何級数の因数分解 -/

/-- **M96-2a: 幾何級数** Σ_{j<k} x^j r^{k−1−j}。 -/
def geoSum (R : CRing) (x r : R.carrier) (k : Nat) : R.carrier :=
  rsum R (fun j => R.mul (rpow R x j) (rpow R r (k - 1 - j))) k

/-- **定理 (M96-2b): 幾何級数の因数分解** —
    x^k − r^k = (x − r)·Σ_{j<k} x^j r^{k−1−j}。 -/
theorem geom_factor (R : CRing) (x r : R.carrier) :
    ∀ k, R.add (rpow R x k) (R.neg (rpow R r k))
      = R.mul (R.add x (R.neg r)) (geoSum R x r k) := by
  intro k
  induction k with
  | zero =>
    show R.add R.one (R.neg R.one) = R.mul (R.add x (R.neg r)) R.zero
    rw [R.add_neg, R.mul_zero (R.add x (R.neg r))]
  | succ k ih =>
    -- geom_{k+1} = r·geom_k + x^k
    have hgeom : geoSum R x r (k + 1)
        = R.add (R.mul r (geoSum R x r k)) (rpow R x k) := by
      show R.add
          (rsum R (fun j => R.mul (rpow R x j) (rpow R r (k + 1 - 1 - j))) k)
          (R.mul (rpow R x k) (rpow R r (k + 1 - 1 - k)))
        = R.add (R.mul r (geoSum R x r k)) (rpow R x k)
      have h1 : ∀ j, j < k →
          R.mul (rpow R x j) (rpow R r (k + 1 - 1 - j))
            = R.mul r (R.mul (rpow R x j) (rpow R r (k - 1 - j))) := by
        intro j hj
        have he : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
        rw [he]
        show R.mul (rpow R x j) (R.mul (rpow R r (k - 1 - j)) r)
          = R.mul r (R.mul (rpow R x j) (rpow R r (k - 1 - j)))
        rw [← R.mul_assoc,
          R.mul_comm (R.mul (rpow R x j) (rpow R r (k - 1 - j))) r]
      have h2 : k + 1 - 1 - k = 0 := by omega
      rw [rsum_congr R k h1, ← rsum_mul_left, h2]
      show R.add (R.mul r (geoSum R x r k)) (R.mul (rpow R x k) R.one)
        = R.add (R.mul r (geoSum R x r k)) (rpow R x k)
      rw [R.mul_one]
    -- 本体: x^{k+1} − r^{k+1} = (x−r)·(r·geom_k + x^k) を展開して整理
    show R.add (R.mul (rpow R x k) x) (R.neg (R.mul (rpow R r k) r))
      = R.mul (R.add x (R.neg r)) (geoSum R x r (k + 1))
    rw [hgeom,
      R.left_distrib (R.add x (R.neg r)) (R.mul r (geoSum R x r k))
        (rpow R x k),
      ← R.mul_assoc (R.add x (R.neg r)) r (geoSum R x r k),
      R.mul_comm (R.add x (R.neg r)) r,
      R.mul_assoc r (R.add x (R.neg r)) (geoSum R x r k),
      ← ih,
      R.left_distrib r (rpow R x k) (R.neg (rpow R r k)),
      R.mul_neg r (rpow R r k),
      R.right_distrib x (R.neg r) (rpow R x k),
      R.neg_mul r (rpow R x k),
      R.add_comm (R.mul x (rpow R x k)) (R.neg (R.mul r (rpow R x k))),
      R.add_add_add_comm (R.mul r (rpow R x k))
        (R.neg (R.mul r (rpow R r k))) (R.neg (R.mul r (rpow R x k)))
        (R.mul x (rpow R x k)),
      R.add_neg (R.mul r (rpow R x k)), R.zero_add,
      R.add_comm (R.neg (R.mul r (rpow R r k))) (R.mul x (rpow R x k)),
      R.mul_comm (rpow R x k) x, R.mul_comm (rpow R r k) r]

/-! ## 商係数の明示式 -/

/-- **M96-3a: 商係数** q_k = Σ_{i<d−k} c_{k+1+i} r^i。 -/
def qCoeff (R : CRing) (c : Nat → R.carrier) (d : Nat) (r : R.carrier)
    (k : Nat) : R.carrier :=
  rsum R (fun i => R.mul (c (k + 1 + i)) (rpow R r i)) (d - k)

/-- 次数を超える商係数は 0。 -/
theorem qCoeff_top (R : CRing) (c : Nat → R.carrier) (d : Nat)
    (r : R.carrier) : qCoeff R c d r d = R.zero := by
  show rsum R _ (d - d) = R.zero
  rw [Nat.sub_self]
  rfl

/-- **M96-3b: 商の最高次係数 = 元の最高次係数**。 -/
theorem qCoeff_lead (R : CRing) (c : Nat → R.carrier) (d : Nat)
    (r : R.carrier) : qCoeff R c (d + 1) r d = c (d + 1) := by
  show rsum R (fun i => R.mul (c (d + 1 + i)) (rpow R r i)) (d + 1 - d)
    = c (d + 1)
  have h : d + 1 - d = 1 := by omega
  rw [h]
  show R.add R.zero (R.mul (c (d + 1 + 0)) R.one) = c (d + 1)
  rw [R.zero_add, R.mul_one]

/-- **M96-3c: 商係数の次数剥がし** —
    q^{(d+1)}_k = q^{(d)}_k + c_{d+1}·r^{d−k}（k ≤ d）。 -/
theorem qCoeff_peel (R : CRing) (c : Nat → R.carrier) (r : R.carrier)
    (d k : Nat) (hk : k ≤ d) :
    qCoeff R c (d + 1) r k
      = R.add (qCoeff R c d r k) (R.mul (c (d + 1)) (rpow R r (d - k))) := by
  show rsum R (fun i => R.mul (c (k + 1 + i)) (rpow R r i)) (d + 1 - k) = _
  have h : d + 1 - k = (d - k) + 1 := by omega
  rw [h]
  show R.add (rsum R (fun i => R.mul (c (k + 1 + i)) (rpow R r i)) (d - k))
      (R.mul (c (k + 1 + (d - k))) (rpow R r (d - k))) = _
  have hidx : k + 1 + (d - k) = d + 1 := by omega
  rw [hidx]
  rfl

/-! ## 除算恒等式（本丸 1） -/

/-- 一次の整理補題: (x−r)·b + (a + b·r) = a + b·x。 -/
theorem lin_div (R : CRing) (a b x r : R.carrier) :
    R.add (R.mul (R.add x (R.neg r)) b) (R.add a (R.mul b r))
      = R.add a (R.mul b x) := by
  rw [R.right_distrib x (R.neg r) b, R.neg_mul r b, R.mul_comm x b,
    R.mul_comm r b,
    R.add_add_add_comm (R.mul b x) (R.neg (R.mul b r)) a (R.mul b r),
    R.add_comm (R.neg (R.mul b r)) (R.mul b r),
    R.add_neg (R.mul b r), R.add_zero,
    R.add_comm (R.mul b x) a]

/-- **定理 (M96-4): 除算恒等式（本丸 1）** —
    P(x) = (x − r)·Q(x) + P(r)、Q の係数は qCoeff の明示式。
    d の帰納 + 最高次剥がし + 幾何級数の因数分解。 -/
theorem pEval_div (R : CRing) (c : Nat → R.carrier) (r : R.carrier) :
    ∀ d x, pEval R c (d + 1) x
      = R.add (R.mul (R.add x (R.neg r))
          (pEval R (qCoeff R c (d + 1) r) d x))
        (pEval R c (d + 1) r) := by
  intro d
  induction d with
  | zero =>
    intro x
    rw [pEval_succ R c 0 x, pEval_succ R c 0 r, pEval_zero R c x,
      pEval_zero R c r, pEval_zero R (qCoeff R c (0 + 1) r) x,
      qCoeff_lead R c 0 r]
    have hx1 : rpow R x (0 + 1) = R.mul R.one x := rfl
    have hr1 : rpow R r (0 + 1) = R.mul R.one r := rfl
    rw [hx1, hr1, R.mul_comm R.one x, R.mul_comm R.one r,
      R.mul_one x, R.mul_one r]
    exact (lin_div R (c 0) (c (0 + 1)) x r).symm
  | succ d ih =>
    intro x
    have hpeel : ∀ k, k < d + 1 + 1 →
        R.mul (qCoeff R c (d + 1 + 1) r k) (rpow R x k)
          = R.add (R.mul (qCoeff R c (d + 1) r k) (rpow R x k))
              (R.mul (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 - k)))
                (rpow R x k)) := by
      intro k hk
      rw [qCoeff_peel R c r (d + 1) k (by omega),
        R.right_distrib (qCoeff R c (d + 1) r k)
          (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 - k))) (rpow R x k)]
    have h3 : rsum R
        (fun k => R.mul (qCoeff R c (d + 1) r k) (rpow R x k)) (d + 1 + 1)
        = pEval R (qCoeff R c (d + 1) r) d x := by
      show R.add (rsum R
          (fun k => R.mul (qCoeff R c (d + 1) r k) (rpow R x k)) (d + 1))
        (R.mul (qCoeff R c (d + 1) r (d + 1)) (rpow R x (d + 1)))
        = pEval R (qCoeff R c (d + 1) r) d x
      rw [qCoeff_top R c (d + 1) r,
        R.mul_comm R.zero (rpow R x (d + 1)),
        R.mul_zero (rpow R x (d + 1)), R.add_zero]
      rfl
    have h5 : ∀ k, k < d + 1 + 1 →
        R.mul (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 - k))) (rpow R x k)
          = R.mul (c (d + 1 + 1))
              (R.mul (rpow R x k) (rpow R r (d + 1 + 1 - 1 - k))) := by
      intro k hk
      have he : d + 1 + 1 - 1 - k = d + 1 - k := by omega
      rw [he, R.mul_assoc (c (d + 1 + 1)) (rpow R r (d + 1 - k))
        (rpow R x k), R.mul_comm (rpow R r (d + 1 - k)) (rpow R x k)]
    have h4 : rsum R
        (fun k => R.mul (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 - k)))
          (rpow R x k)) (d + 1 + 1)
        = R.mul (c (d + 1 + 1)) (geoSum R x r (d + 1 + 1)) := by
      rw [rsum_congr R (d + 1 + 1) h5, ← rsum_mul_left]
      rfl
    have hq : pEval R (qCoeff R c (d + 1 + 1) r) (d + 1) x
        = R.add (pEval R (qCoeff R c (d + 1) r) d x)
            (R.mul (c (d + 1 + 1)) (geoSum R x r (d + 1 + 1))) := by
      show rsum R
          (fun k => R.mul (qCoeff R c (d + 1 + 1) r k) (rpow R x k))
          (d + 1 + 1) = _
      rw [rsum_congr R (d + 1 + 1) hpeel,
        rsum_add R (fun k => R.mul (qCoeff R c (d + 1) r k) (rpow R x k))
          (fun k => R.mul (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 - k)))
            (rpow R x k)) (d + 1 + 1),
        h3, h4]
    have hXAg : R.mul (R.add x (R.neg r))
        (R.mul (c (d + 1 + 1)) (geoSum R x r (d + 1 + 1)))
        = R.add (R.mul (c (d + 1 + 1)) (rpow R x (d + 1 + 1)))
            (R.neg (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 + 1)))) := by
      rw [← R.mul_assoc (R.add x (R.neg r)) (c (d + 1 + 1))
          (geoSum R x r (d + 1 + 1)),
        R.mul_comm (R.add x (R.neg r)) (c (d + 1 + 1)),
        R.mul_assoc (c (d + 1 + 1)) (R.add x (R.neg r))
          (geoSum R x r (d + 1 + 1)),
        ← geom_factor R x r (d + 1 + 1),
        R.left_distrib (c (d + 1 + 1)) (rpow R x (d + 1 + 1))
          (R.neg (rpow R r (d + 1 + 1))),
        R.mul_neg (c (d + 1 + 1)) (rpow R r (d + 1 + 1))]
    rw [pEval_succ R c (d + 1) x, pEval_succ R c (d + 1) r, hq, ih x,
      R.left_distrib (R.add x (R.neg r))
        (pEval R (qCoeff R c (d + 1) r) d x)
        (R.mul (c (d + 1 + 1)) (geoSum R x r (d + 1 + 1))),
      hXAg,
      R.add_add_add_comm
        (R.mul (R.add x (R.neg r)) (pEval R (qCoeff R c (d + 1) r) d x))
        (R.add (R.mul (c (d + 1 + 1)) (rpow R x (d + 1 + 1)))
          (R.neg (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 + 1)))))
        (pEval R c (d + 1) r)
        (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 + 1))),
      R.add_assoc (R.mul (c (d + 1 + 1)) (rpow R x (d + 1 + 1)))
        (R.neg (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 + 1))))
        (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 + 1))),
      R.add_comm (R.neg (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 + 1))))
        (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 + 1))),
      R.add_neg (R.mul (c (d + 1 + 1)) (rpow R r (d + 1 + 1))),
      R.add_zero (R.mul (c (d + 1 + 1)) (rpow R x (d + 1 + 1)))]

/-! ## 根の個数 ≤ 次数（本丸 2） -/

/-- 根での因数分解: P(r) = 0 なら P(x) = (x − r)·Q(x)。 -/
theorem pEval_root_factor (R : CRing) (c : Nat → R.carrier)
    (r : R.carrier) (d : Nat) (hr : pEval R c (d + 1) r = R.zero) :
    ∀ x, pEval R c (d + 1) x
      = R.mul (R.add x (R.neg r)) (pEval R (qCoeff R c (d + 1) r) d x) := by
  intro x
  rw [pEval_div R c r d x, hr, R.add_zero]

/-- **定理 (M96-5): 根の個数 ≤ 次数（本丸 2）** — NoZeroDiv の下で、
    次数 d・最高次係数 ≠ 0 の多項式に d+1 個の相異なる根があれば
    矛盾。d の帰納: 最後の根で因数分解 → 残りの根は商の根
    （零因子なし）→ 商は次数 d−1・最高次係数は元と同じ。 -/
theorem roots_bound (R : CRing) (hD : NoZeroDiv R) :
    ∀ d (c : Nat → R.carrier), c d ≠ R.zero →
    ∀ r : Nat → R.carrier,
    (∀ i j, i < j → j ≤ d → r i ≠ r j) →
    (∀ i, i ≤ d → pEval R c d (r i) = R.zero) → False := by
  intro d
  induction d with
  | zero =>
    intro c hlead r _ hroots
    have h0 := hroots 0 (Nat.le_refl 0)
    rw [pEval_zero] at h0
    exact hlead h0
  | succ d ih =>
    intro c hlead r hdist hroots
    have hfac := pEval_root_factor R c (r (d + 1)) d
      (hroots (d + 1) (Nat.le_refl (d + 1)))
    refine ih (qCoeff R c (d + 1) (r (d + 1))) ?_ r ?_ ?_
    · rw [qCoeff_lead R c d (r (d + 1))]
      exact hlead
    · intro i j hij hj
      exact hdist i j hij (by omega)
    · intro i hi
      have hri := hroots i (by omega)
      rw [hfac (r i)] at hri
      cases hD _ _ hri with
      | inl h1 =>
        exact absurd (CRing.eq_of_sub_eq_zero R h1)
          (hdist i (d + 1) (by omega) (by omega))
      | inr h2 => exact h2

/-! ## 二項多項式 x^n − a への特化 -/

/-- **M96-6a: 二項多項式の係数** x^n − a。 -/
def cBin (R : CRing) (n : Nat) (a : R.carrier) : Nat → R.carrier :=
  fun k => if k = 0 then R.neg a else if k = n then R.one else R.zero

/-- 最高次係数 = 1。 -/
theorem cBin_top (R : CRing) (m : Nat) (a : R.carrier) :
    cBin R (m + 1) a (m + 1) = R.one := by
  show (if m + 1 = 0 then R.neg a
    else if m + 1 = m + 1 then R.one else R.zero) = R.one
  rw [if_neg (by omega : ¬ m + 1 = 0), if_pos rfl]

/-- 低次部分の評価 = −a（中間係数は全部 0）。 -/
theorem pEval_bin_low (R : CRing) (n : Nat) (a x : R.carrier) :
    ∀ m, m < n → pEval R (cBin R n a) m x = R.neg a := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [pEval_zero]
    rfl
  | succ m ihm =>
    intro hm
    rw [pEval_succ R (cBin R n a) m x]
    have hz : cBin R n a (m + 1) = R.zero := by
      show (if m + 1 = 0 then R.neg a
        else if m + 1 = n then R.one else R.zero) = R.zero
      rw [if_neg (by omega : ¬ m + 1 = 0),
        if_neg (by omega : ¬ m + 1 = n)]
    rw [hz, R.mul_comm R.zero (rpow R x (m + 1)),
      R.mul_zero (rpow R x (m + 1)), R.add_zero, ihm (by omega)]

/-- **M96-6b: 二項多項式の評価** P(x) = x^{m+1} − a。 -/
theorem pEval_bin (R : CRing) (m : Nat) (a x : R.carrier) :
    pEval R (cBin R (m + 1) a) (m + 1) x
      = R.add (R.neg a) (rpow R x (m + 1)) := by
  rw [pEval_succ R (cBin R (m + 1) a) m x,
    pEval_bin_low R (m + 1) a x m (by omega), cBin_top R m a,
    R.mul_comm R.one (rpow R x (m + 1)), R.mul_one (rpow R x (m + 1))]

/-- **定理 (M96-6c): n 乗根の個数 ≤ n** — NoZeroDiv + 1 ≠ 0 の環で、
    x^{m+1} = a の相異なる解は m+1 個以下。 -/
theorem bin_roots_bound (R : CRing) (hD : NoZeroDiv R)
    (hone : R.one ≠ R.zero) (a : R.carrier) (m : Nat)
    (r : Nat → R.carrier)
    (hdist : ∀ i j, i < j → j ≤ m + 1 → r i ≠ r j)
    (hroots : ∀ i, i ≤ m + 1 → rpow R (r i) (m + 1) = a) : False := by
  refine roots_bound R hD (m + 1) (cBin R (m + 1) a)
    (fun h => hone ((cBin_top R m a).symm.trans h)) r hdist ?_
  intro i hi
  rw [pEval_bin R m a (r i), hroots i hi, R.neg_add a]

/-! ## Eisenstein 方程式への特化（柱B 上界の最終段） -/

/-- **定理 (M96-7): Eisenstein 方程式の根の個数 ≤ p−1** —
    NoZeroDiv の下で t^{p−1} = −π の相異なる根は p−1 個以下
    （p 個の相異なる根は矛盾）。M84F の p−1 個の相異なる共役根
    ω(a)λ と合わせ、Λ₁ の上界が（hD を法として）閉じる。 -/
theorem eis_roots_bound (p : Nat) (hodd : 3 ≤ p)
    (hD : NoZeroDiv (eisRing p))
    (r : Nat → (eisRing p).carrier)
    (hdist : ∀ i j, i < j → j ≤ p - 1 → r i ≠ r j)
    (hroots : ∀ i, i ≤ p - 1 → rpow (eisRing p) (r i) (p - 1)
      = (eisRing p).neg
          ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))) : False := by
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = m + 1 := ⟨p - 2, by omega⟩
  rw [hm] at hdist hroots
  exact bin_roots_bound (eisRing p) hD (eis_one_ne_zero p (by omega))
    ((eisRing p).neg ((eisOf p).map ((toZp p).map ((p : Nat) : Int))))
    m r hdist hroots

end IUT
