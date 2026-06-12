/-
  IUT/Composition.lean — M40（形式冪級数の合成: Lubin–Tate 第三層）

  Lubin–Tate 補題の方程式 f∘F = F∘f を書くための言語。合成を

    (P∘Q)_n = Σ_{k≤n} P_k · (Q^k)_n

  と**有限和**で定義する。Q の定数項が 0 なら (Q^k)_n = 0（k > n）と
  なるため、これは真の合成と一致する（truncation の正当化が M40-3）。

  * M40-1 `rsum_single` — 一点集中和: 範囲内で一点以外 0 なら和はその点
  * M40-2 `psPow` / `psPow_one` / `psPow_add` — 冪 Q^k と指数法則
    （psRing の環法則から）
  * M40-3 `psPow_coeff_zero` — **truncation**: Q(0) = 0 なら
    n < k ⟹ (Q^k)_n = 0（場合分け: 低次冪は帰納法、対角は Q(0) = 0）
  * M40-4 `psComp` / `psComp_add` / `psComp_one` — 合成と
    P ↦ P∘Q の加法性・単位元保存
  * M40-5 `psComp_X` — **X∘Q = Q**（恒等級数の合成、Q(0) = 0 を使用）
  * M40-6 `psComp_coeff_zero` / `psComp_coeff_one` — 低次係数公式
    (P∘Q)_0 = P_0、(P∘Q)_1 = P_1·Q_1。M41 の係数帰納の出発点

  注: 合成の乗法性 (PP')∘Q = (P∘Q)(P'∘Q) は計画中の LT 経路では不要
  （f = pX + X^p は f∘F = p·F + F^p と環演算で直接展開する）のため
  保留。全て選択公理不使用。
-/
import IUT.PowerSeries

namespace IUT

/-! ## 一点集中和 -/

/-- **M40-1: 一点集中和** — 範囲内で k₀ 以外の項が全て 0 なら
    和は f k₀。 -/
theorem rsum_single (R : CRing) (f : Nat → R.carrier) (k0 : Nat) : ∀ m,
    k0 < m → (∀ j, j < m → j ≠ k0 → f j = R.zero) → rsum R f m = f k0 := by
  intro m
  induction m with
  | zero => intro h _; exact absurd h (by omega)
  | succ m ih =>
    intro hk0 hz
    show R.add (rsum R f m) (f m) = f k0
    cases Nat.decEq m k0 with
    | isTrue he =>
      subst he
      have h0 : rsum R f m = R.zero := by
        have hc : rsum R f m = rsum R (fun _ => R.zero) m :=
          rsum_congr R m (fun j hj => hz j (by omega) (by omega))
        rw [hc]
        exact rsum_const_zero R m
      rw [h0, R.zero_add]
    | isFalse he =>
      have h1 : f m = R.zero := hz m (by omega) he
      rw [h1, R.add_zero]
      exact ih (by omega) (fun j hj hne => hz j (by omega) hne)

/-! ## 冪 -/

/-- 冪 Q^k（psRing の乗法の反復）。 -/
def psPow (R : CRing) (Q : PS R) : Nat → PS R
  | 0 => (psRing R).one
  | k + 1 => (psRing R).mul (psPow R Q k) Q

/-- Q^1 = Q。 -/
theorem psPow_one (R : CRing) (Q : PS R) : psPow R Q 1 = Q :=
  (psRing R).one_mul Q

/-- **M40-2: 冪の指数法則** Q^{i+j} = Q^i · Q^j。 -/
theorem psPow_add (R : CRing) (Q : PS R) (i : Nat) : ∀ j,
    psPow R Q (i + j) = (psRing R).mul (psPow R Q i) (psPow R Q j) := by
  intro j
  induction j with
  | zero =>
    show psPow R Q i = (psRing R).mul (psPow R Q i) ((psRing R).one)
    rw [(psRing R).mul_comm, (psRing R).one_mul]
  | succ j ih =>
    show (psRing R).mul (psPow R Q (i + j)) Q
      = (psRing R).mul (psPow R Q i) ((psRing R).mul (psPow R Q j) Q)
    rw [ih, (psRing R).mul_assoc]

/-- **定理 (M40-3): truncation** — Q(0) = 0 なら n < k ⟹ (Q^k)_n = 0。
    合成の有限和定義の正当化。 -/
theorem psPow_coeff_zero (R : CRing) (Q : PS R) (hQ : Q 0 = R.zero) :
    ∀ k n, n < k → psPow R Q k n = R.zero := by
  intro k
  induction k with
  | zero => intro n hn; exact absurd hn (by omega)
  | succ k ih =>
    intro n hn
    show rsum R (fun j => R.mul (psPow R Q k j) (Q (n - j))) (n + 1) = R.zero
    have hc : rsum R (fun j => R.mul (psPow R Q k j) (Q (n - j))) (n + 1)
        = rsum R (fun _ => R.zero) (n + 1) :=
      rsum_congr R (n + 1) (fun j hj => by
        cases Nat.lt_or_ge j k with
        | inl hlt =>
          rw [ih j hlt]
          exact R.zero_mul _
        | inr hge =>
          have hj0 : n - j = 0 := by omega
          rw [hj0, hQ]
          exact R.mul_zero _)
    rw [hc]
    exact rsum_const_zero R (n + 1)

/-! ## 合成 -/

/-- **M40-4a: 合成** (P∘Q)_n = Σ_{k≤n} P_k·(Q^k)_n
    （Q(0) = 0 のとき truncation により真の合成と一致）。 -/
def psComp (R : CRing) (P Q : PS R) : PS R :=
  fun n => rsum R (fun k => R.mul (P k) (psPow R Q k n)) (n + 1)

/-- **M40-4b: 合成の加法性** (P + P')∘Q = P∘Q + P'∘Q。 -/
theorem psComp_add (R : CRing) (P P' Q : PS R) :
    psComp R ((psRing R).add P P') Q
      = (psRing R).add (psComp R P Q) (psComp R P' Q) := by
  funext n
  show rsum R (fun k => R.mul (R.add (P k) (P' k)) (psPow R Q k n)) (n + 1)
    = R.add (rsum R (fun k => R.mul (P k) (psPow R Q k n)) (n + 1))
        (rsum R (fun k => R.mul (P' k) (psPow R Q k n)) (n + 1))
  have hc : rsum R (fun k => R.mul (R.add (P k) (P' k)) (psPow R Q k n)) (n + 1)
      = rsum R (fun k => R.add (R.mul (P k) (psPow R Q k n))
          (R.mul (P' k) (psPow R Q k n))) (n + 1) :=
    rsum_congr R (n + 1) (fun k _ => R.right_distrib _ _ _)
  rw [hc]
  exact rsum_add R _ _ (n + 1)

/-- **M40-4c: 単位元の合成** 1∘Q = 1。 -/
theorem psComp_one (R : CRing) (Q : PS R) : psComp R (psOne R) Q = psOne R := by
  funext n
  show rsum R (fun k => R.mul (psOne R k) (psPow R Q k n)) (n + 1) = psOne R n
  have hs : rsum R (fun k => R.mul (psOne R k) (psPow R Q k n)) (n + 1)
      = R.mul (psOne R 0) (psPow R Q 0 n) :=
    rsum_single R _ 0 (n + 1) (by omega) (fun j _ hj => by
      have h0 : psOne R j = R.zero := if_neg hj
      rw [h0]
      exact R.zero_mul _)
  rw [hs]
  show R.mul R.one (psOne R n) = psOne R n
  exact R.one_mul _

/-- **定理 (M40-5): 恒等級数の合成** X∘Q = Q（Q(0) = 0）。 -/
theorem psComp_X (R : CRing) (Q : PS R) (hQ : Q 0 = R.zero) :
    psComp R (psX R) Q = Q := by
  funext n
  show rsum R (fun k => R.mul (psX R k) (psPow R Q k n)) (n + 1) = Q n
  cases n with
  | zero =>
    show R.add R.zero (R.mul (psX R 0) (psPow R Q 0 0)) = Q 0
    have h0 : psX R 0 = R.zero := if_neg (by omega)
    rw [h0, R.zero_mul, R.zero_add, hQ]
  | succ m =>
    have hs : rsum R (fun k => R.mul (psX R k) (psPow R Q k (m + 1))) (m + 2)
        = R.mul (psX R 1) (psPow R Q 1 (m + 1)) :=
      rsum_single R _ 1 (m + 2) (by omega) (fun j _ hj => by
        have h0 : psX R j = R.zero := if_neg hj
        rw [h0]
        exact R.zero_mul _)
    rw [hs]
    show R.mul R.one (psPow R Q 1 (m + 1)) = Q (m + 1)
    rw [R.one_mul, psPow_one]

/-- **M40-6a: 定数項** (P∘Q)_0 = P_0。 -/
theorem psComp_coeff_zero (R : CRing) (P Q : PS R) :
    psComp R P Q 0 = P 0 := by
  show R.add R.zero (R.mul (P 0) (psPow R Q 0 0)) = P 0
  show R.add R.zero (R.mul (P 0) R.one) = P 0
  rw [R.zero_add, R.mul_comm, R.one_mul]

/-- **M40-6b: 一次係数** (P∘Q)_1 = P_1·Q_1（M41 の係数帰納の出発点:
    合成の一次部分は一次部分の積）。 -/
theorem psComp_coeff_one (R : CRing) (P Q : PS R) :
    psComp R P Q 1 = R.mul (P 1) (Q 1) := by
  have h1 : psPow R Q 1 = Q := psPow_one R Q
  show R.add (R.add R.zero (R.mul (P 0) (psOne R 1)))
      (R.mul (P 1) (psPow R Q 1 1)) = R.mul (P 1) (Q 1)
  rw [h1]
  show R.add (R.add R.zero (R.mul (P 0) R.zero))
      (R.mul (P 1) (Q 1)) = R.mul (P 1) (Q 1)
  rw [R.mul_zero, R.zero_add, R.zero_add]

end IUT
