/-
  IUT/FormalGroupEval.lean — M72（逆元キャンペーン第一層:
  2 変数法則への 1 変数代入）

  形式群の逆元 [-1] 級数キャンペーンの基盤。2 変数級数 F(X,Y) に
  1 変数級数 P(T)・Q(T) を代入した 1 変数級数 F(P(T), Q(T)) を構成し、
  打ち切り不変性（pad）と定数項・一次係数を検証する。

  * M72-1 `psPowPow_low` — 冪積の低次消滅 (P^a·Q^b)_n = 0
    （n < a + b。冪の対角下消滅は既存の M40-3 psPow_coeff_zero）
  * M72-2 `ps21Comp` — **2 変数 → 1 変数代入** F(P,Q)_n
    = Σ_{b,a ≤ n} F_{b,a}·(P^a Q^b)_n（P(0) = Q(0) = 0 のとき
    truncation により真の代入と一致）
  * M72-3 `ps21Comp_pad` — 打ち切り境界の付け替え（n + 1 → N）
  * M72-4 `ps21Comp_zero_coeff` / `ps21Comp_lin` — 定数項 = F₀₀
    （無条件）と一次係数 = F₀₁·P₁ + F₁₀·Q₁（master 補題、
    M67 の ps23Comp_lin の 1 変数版）

  逆元の本体（ι = ltSol p hp (−1) と F(X, ι(X)) = 0）は次層以降。
  全て選択公理不使用。
-/
import IUT.FormalGroupAssoc

namespace IUT

/-! ## 冪積の低次消滅 -/

/-- **M72-1: 冪の積の低次消滅** — P(0) = Q(0) = 0 なら
    (P^a·Q^b)_n = 0（n < a + b。各冪は M40-3 の対角下消滅）。 -/
theorem psPowPow_low (R : CRing) (P Q : PS R)
    (hP : P 0 = R.zero) (hQ : Q 0 = R.zero)
    (a b n : Nat) (h : n < a + b) :
    psMul R (psPow R P a) (psPow R Q b) n = R.zero := by
  show rsum R (fun m => R.mul (psPow R P a m) (psPow R Q b (n - m))) (n + 1)
    = R.zero
  have hz : rsum R (fun m =>
        R.mul (psPow R P a m) (psPow R Q b (n - m))) (n + 1)
      = rsum R (fun _ => R.zero) (n + 1) :=
    rsum_congr R (n + 1) (fun m hm => by
      cases Nat.lt_or_ge m a with
      | inl hma =>
        rw [psPow_coeff_zero R P hP a m hma]
        exact R.zero_mul _
      | inr hma =>
        rw [psPow_coeff_zero R Q hQ b (n - m) (by omega)]
        exact R.mul_zero _)
  rw [hz]
  exact rsum_const_zero R (n + 1)

/-! ## 2 変数 → 1 変数代入 -/

/-- **M72-2: 2 変数 → 1 変数代入** F(P, Q)_n
    = Σ_{b,a ≤ n} F_{b,a}·(P^a Q^b)_n（P が X・Q が Y に入る。
    P(0) = Q(0) = 0 のとき truncation により真の代入と一致）。 -/
def ps21Comp (R : CRing) (F : PS2 R) (P Q : PS R) : PS R :=
  fun n =>
    rsum R (fun b => rsum R (fun a =>
      R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1)

/-- **M72-3: 打ち切り境界の付け替え** — n < N なら境界 n + 1 を N に
    広げてよい（はみ出た項は psPowPow_low で消える）。 -/
theorem ps21Comp_pad (R : CRing) (F : PS2 R) (P Q : PS R)
    (hP : P 0 = R.zero) (hQ : Q 0 = R.zero)
    (N n : Nat) (hN : n < N) :
    ps21Comp R F P Q n
      = rsum R (fun b => rsum R (fun a =>
          R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n)) N) N := by
  show rsum R (fun b => rsum R (fun a =>
      R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1)
    = _
  have hinner : ∀ b, rsum R (fun a =>
        R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n)) N
      = rsum R (fun a =>
          R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1) :=
    fun b => rsum_pad R _ (by omega) (fun a ha => by
      rw [psPowPow_low R P Q hP hQ a b n (by omega)]
      exact R.mul_zero _)
  have houter : rsum R (fun b => rsum R (fun a =>
        R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n)) N) N
      = rsum R (fun b => rsum R (fun a =>
          R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n)) N) (n + 1) :=
    rsum_pad R _ (by omega) (fun b hb => by
      have hz : rsum R (fun a =>
            R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n)) N
          = rsum R (fun _ => R.zero) N :=
        rsum_congr R N (fun a _ => by
          rw [psPowPow_low R P Q hP hQ a b n (by omega)]
          exact R.mul_zero _)
      show rsum R (fun a =>
          R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n)) N = R.zero
      rw [hz]
      exact rsum_const_zero R N)
  rw [houter]
  exact rsum_congr R (n + 1) (fun b _ => (hinner b).symm)

/-! ## 定数項と一次係数 -/

/-- **M72-4a: 代入の定数項** F(P,Q)_0 = F₀₀（無条件）。 -/
theorem ps21Comp_zero_coeff (R : CRing) (F : PS2 R) (P Q : PS R) :
    ps21Comp R F P Q 0 = F 0 0 := by
  show R.add R.zero (R.add R.zero
      (R.mul (F 0 0) (R.add R.zero (R.mul R.one R.one)))) = F 0 0
  rw [R.zero_add, R.zero_add, R.zero_add, R.one_mul, R.mul_comm, R.one_mul]

/-- **M72-4b: 代入の一次係数**（master 補題）— P(0) = Q(0) = 0 なら
    F(P,Q)_1 = F₀₁·P₁ + F₁₀·Q₁（4 項展開、(0,0) 項と (1,1) 項は消滅）。 -/
theorem ps21Comp_lin (R : CRing) (F : PS2 R) (P Q : PS R)
    (hP : P 0 = R.zero) (hQ : Q 0 = R.zero) :
    ps21Comp R F P Q 1
      = R.add (R.mul (F 0 1) (P 1)) (R.mul (F 1 0) (Q 1)) := by
  show R.add
      (R.add R.zero
        (R.add (R.add R.zero
            (R.mul (F 0 0) (psMul R (psPow R P 0) (psPow R Q 0) 1)))
          (R.mul (F 0 1) (psMul R (psPow R P 1) (psPow R Q 0) 1))))
      (R.add (R.add R.zero
          (R.mul (F 1 0) (psMul R (psPow R P 0) (psPow R Q 1) 1)))
        (R.mul (F 1 1) (psMul R (psPow R P 1) (psPow R Q 1) 1)))
    = R.add (R.mul (F 0 1) (P 1)) (R.mul (F 1 0) (Q 1))
  rw [psPow_one R P, psPow_one R Q]
  have h00 : psMul R (psPow R P 0) (psPow R Q 0) 1 = R.zero := by
    show R.add (R.add R.zero (R.mul R.one R.zero)) (R.mul R.zero R.one)
      = R.zero
    rw [R.mul_zero, R.zero_mul, R.zero_add, R.zero_add]
  have h10 : psMul R P (psPow R Q 0) 1 = P 1 := by
    show R.add (R.add R.zero (R.mul (P 0) R.zero)) (R.mul (P 1) R.one) = P 1
    rw [R.mul_zero, R.zero_add, R.zero_add, R.mul_comm, R.one_mul]
  have h01 : psMul R (psPow R P 0) Q 1 = Q 1 := by
    show R.add (R.add R.zero (R.mul R.one (Q 1))) (R.mul R.zero (Q 0)) = Q 1
    rw [R.one_mul, R.zero_mul, R.zero_add, R.add_zero]
  have h11 : psMul R P Q 1 = R.zero := by
    show R.add (R.add R.zero (R.mul (P 0) (Q 1))) (R.mul (P 1) (Q 0)) = R.zero
    rw [hP, hQ, R.zero_mul, R.mul_zero, R.zero_add, R.zero_add]
  rw [h00, h10, h01, h11, R.mul_zero, R.mul_zero, R.zero_add, R.zero_add,
    R.zero_add, R.add_zero, R.zero_add]

end IUT
