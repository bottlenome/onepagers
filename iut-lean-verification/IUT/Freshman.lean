/-
  IUT/Freshman.lean — M45（新入生の夢: 環レベルと級数レベル、第八層）

  Lubin–Tate 誤差項の p-整除性の中核。M44 の二変数二項定理から

    (x + y)^p = x^p + y^p + p·c   （任意の可換環、c は明示構成）

  を導き、これを冪級数環 PS(R) に持ち上げ、係数環 ℤ_p では
  「p·c」部分が各係数の p-整除性（zpMul (toZp p)）に翻訳されることを
  示す。中間項の因子は Nat 除算 chs p k / p で**正準化**し、∃ からの
  関数抽出（= 選択公理）を回避する。

  * M45-1 `rpow_zero` / `rofNat_one` / `CRing.add_rotate` — 簿記
  * M45-2 `freshman_ring` — **(x+y)^p = x^p + y^p + p·c**
    （境界項 k = 0, p は C = 1、中間項は p-因子を括り出して
    rsum_mul_left で集約）
  * M45-3 `psPow_eq_rpow` / `freshman_ps` — **級数版**:
    (A+B)^p = A^p + B^p + p·C in PS(R)
  * M45-4 `rofNat_ps_eq_psC` / `psC_mul_coeff` — rofNat の定数級数性と
    定数級数の積の係数公式（一点集中和）
  * M45-5 `rofNat_zp` / `freshman_zp` — **ℤ_p 係数版**: 各係数 n で
    ((A+B)^p)_n = (A^p)_n + (B^p)_n + p·(C_n)（p-整除性の witness 付き）

  残り: 誤差項 f∘F − F∘g の p-整除性 → 係数の再帰構成（存在定理）。
  全て選択公理不使用。
-/
import IUT.Binomial2

namespace IUT

/-! ## 簿記 -/

/-- x^0 = 1。 -/
theorem rpow_zero (R : CRing) (x : R.carrier) : rpow R x 0 = R.one := rfl

/-- rofNat 1 = 1。 -/
theorem rofNat_one (R : CRing) : rofNat R 1 = R.one := R.zero_add R.one

/-- (a + b) + c = (c + a) + b。 -/
theorem CRing.add_rotate (R : CRing) (a b c : R.carrier) :
    R.add (R.add a b) c = R.add (R.add c a) b := by
  rw [R.add_comm (R.add a b) c, ← R.add_assoc]

/-! ## 環レベルの新入生の夢 -/

/-- **定理 (M45-2): 新入生の夢（環レベル）** —
    (x+y)^p = x^p + y^p + p·c（c は明示構成、中間項の因子は
    Nat 除算で正準化）。 -/
theorem freshman_ring (R : CRing) (p : Nat) (hp : IsPrime p) (x y : R.carrier) :
    ∃ c, rpow R (R.add x y) p
      = R.add (R.add (rpow R x p) (rpow R y p)) (R.mul (rofNat R p) c) := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.1; omega⟩
  subst hm
  refine ⟨rsum R (fun k => R.mul (rofNat R (chs (m + 2) (k + 1) / (m + 2)))
      (R.mul (rpow R x (k + 1)) (rpow R y (m + 2 - (k + 1))))) (m + 1), ?_⟩
  rw [binomial2 R x y (m + 2)]
  have hsplit : rsum R (fun k => R.mul (rofNat R (chs (m + 2) k))
        (R.mul (rpow R x k) (rpow R y (m + 2 - k)))) (m + 2 + 1)
      = R.add (R.add (R.mul (rofNat R (chs (m + 2) 0))
            (R.mul (rpow R x 0) (rpow R y (m + 2))))
          (rsum R (fun k => R.mul (rofNat R (chs (m + 2) (k + 1)))
            (R.mul (rpow R x (k + 1)) (rpow R y (m + 2 - (k + 1))))) (m + 1)))
        (R.mul (rofNat R (chs (m + 2) (m + 2)))
          (R.mul (rpow R x (m + 2)) (rpow R y (m + 2 - (m + 2))))) := by
    have h1 : rsum R (fun k => R.mul (rofNat R (chs (m + 2) k))
          (R.mul (rpow R x k) (rpow R y (m + 2 - k)))) (m + 2)
        = R.add (R.mul (rofNat R (chs (m + 2) 0))
            (R.mul (rpow R x 0) (rpow R y (m + 2))))
          (rsum R (fun k => R.mul (rofNat R (chs (m + 2) (k + 1)))
            (R.mul (rpow R x (k + 1)) (rpow R y (m + 2 - (k + 1))))) (m + 1)) :=
      rsum_head R _ (m + 1)
    show R.add (rsum R (fun k => R.mul (rofNat R (chs (m + 2) k))
          (R.mul (rpow R x k) (rpow R y (m + 2 - k)))) (m + 2))
        (R.mul (rofNat R (chs (m + 2) (m + 2)))
          (R.mul (rpow R x (m + 2)) (rpow R y (m + 2 - (m + 2))))) = _
    rw [h1]
  have hmid : rsum R (fun k => R.mul (rofNat R (chs (m + 2) (k + 1)))
        (R.mul (rpow R x (k + 1)) (rpow R y (m + 2 - (k + 1))))) (m + 1)
      = R.mul (rofNat R (m + 2))
          (rsum R (fun k => R.mul (rofNat R (chs (m + 2) (k + 1) / (m + 2)))
            (R.mul (rpow R x (k + 1)) (rpow R y (m + 2 - (k + 1))))) (m + 1)) := by
    have h2 : R.mul (rofNat R (m + 2))
          (rsum R (fun k => R.mul (rofNat R (chs (m + 2) (k + 1) / (m + 2)))
            (R.mul (rpow R x (k + 1)) (rpow R y (m + 2 - (k + 1))))) (m + 1))
        = rsum R (fun k => R.mul (rofNat R (m + 2))
            (R.mul (rofNat R (chs (m + 2) (k + 1) / (m + 2)))
              (R.mul (rpow R x (k + 1)) (rpow R y (m + 2 - (k + 1)))))) (m + 1) :=
      rsum_mul_left R _ _ (m + 1)
    rw [h2]
    exact rsum_congr R (m + 1) (fun k hk => by
      have hdvd : (m + 2) ∣ chs (m + 2) (k + 1) :=
        prime_dvd_chs (m + 2) hp (k + 1) (by omega) (by omega)
      have key : ∀ d t, chs (m + 2) (k + 1) = (m + 2) * d →
          R.mul (rofNat R (chs (m + 2) (k + 1))) t
            = R.mul (rofNat R (m + 2)) (R.mul (rofNat R d) t) := by
        intro d t hd
        rw [hd, rofNat_mul, R.mul_assoc]
      exact key (chs (m + 2) (k + 1) / (m + 2)) _ (Nat.mul_div_cancel' hdvd).symm)
  rw [hsplit, hmid, chs_zero (m + 2), chs_self (m + 2), rofNat_one,
    rpow_zero R x, R.one_mul, R.one_mul,
    show m + 2 - (m + 2) = 0 by omega, rpow_zero R y, R.mul_one, R.one_mul]
  exact R.add_rotate _ _ _

/-! ## 級数レベルへの持ち上げ -/

/-- psPow は psRing 上の rpow と一致。 -/
theorem psPow_eq_rpow (R : CRing) (Q : PS R) : ∀ n,
    psPow R Q n = rpow (psRing R) Q n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (psRing R).mul (psPow R Q n) Q = (psRing R).mul (rpow (psRing R) Q n) Q
    rw [ih]

/-- **定理 (M45-3): 新入生の夢（級数レベル）** —
    (A+B)^p = A^p + B^p + p·C in PS(R)。 -/
theorem freshman_ps (R : CRing) (p : Nat) (hp : IsPrime p) (A B : PS R) :
    ∃ C, psPow R (psAdd R A B) p
      = (psRing R).add ((psRing R).add (psPow R A p) (psPow R B p))
          ((psRing R).mul (rofNat (psRing R) p) C) := by
  obtain ⟨C, hC⟩ := freshman_ring (psRing R) p hp A B
  refine ⟨C, ?_⟩
  rw [psPow_eq_rpow R (psAdd R A B) p, psPow_eq_rpow R A p, psPow_eq_rpow R B p]
  exact hC

/-! ## 係数への転送 -/

/-- rofNat の PS 係数: 定数項に rofNat、他は 0。 -/
theorem rofNat_ps_coeff (R : CRing) : ∀ (n m : Nat),
    rofNat (psRing R) n m = if m = 0 then rofNat R n else R.zero := by
  intro n
  induction n with
  | zero =>
    intro m
    cases m with
    | zero => rfl
    | succ j => rfl
  | succ n ih =>
    intro m
    cases m with
    | zero =>
      show R.add (rofNat (psRing R) n 0) R.one = rofNat R (n + 1)
      rw [ih 0]
      rfl
    | succ j =>
      show R.add (rofNat (psRing R) n (j + 1)) R.zero = R.zero
      rw [ih (j + 1)]
      show R.add R.zero R.zero = R.zero
      rw [R.zero_add]

/-- **M45-4a**: rofNat (PS) は定数級数。 -/
theorem rofNat_ps_eq_psC (R : CRing) (n : Nat) :
    rofNat (psRing R) n = psC R (rofNat R n) := by
  funext m
  rw [rofNat_ps_coeff R n m]
  rfl

/-- **M45-4b: 定数級数の積の係数** — (psC a · C)_n = a·C_n
    （一点集中和）。 -/
theorem psC_mul_coeff (R : CRing) (a : R.carrier) (C : PS R) (n : Nat) :
    psMul R (psC R a) C n = R.mul a (C n) := by
  show rsum R (fun k => R.mul (psC R a k) (C (n - k))) (n + 1) = R.mul a (C n)
  have hs : rsum R (fun k => R.mul (psC R a k) (C (n - k))) (n + 1)
      = R.mul (psC R a 0) (C (n - 0)) :=
    rsum_single R _ 0 (n + 1) (by omega) (fun j _ hj => by
      have h0 : psC R a j = R.zero := if_neg hj
      rw [h0]
      exact R.zero_mul _)
  rw [hs]
  rfl

/-- rofNat (zpRing) = 完備化像 toZp。 -/
theorem rofNat_zp (p : Nat) : ∀ n,
    rofNat (zpRing p) n = (toZp p).map ((n : Nat) : Int) := by
  intro n
  induction n with
  | zero => exact (Hom.map_one (toZp p)).symm
  | succ n ih =>
    show (Zp p).mul (rofNat (zpRing p) n) (zpOne p)
      = (toZp p).map ((n + 1 : Nat) : Int)
    rw [ih, show zpOne p = (toZp p).map 1 from ((toZpRing p).map_one).symm,
      ← (toZp p).map_mul]
    show (toZp p).map (((n : Nat) : Int) + 1) = (toZp p).map ((n + 1 : Nat) : Int)
    rw [show ((n : Nat) : Int) + 1 = ((n + 1 : Nat) : Int) by omega]

/-- **定理 (M45-5): 新入生の夢（ℤ_p 係数版）** — 各係数 n で
    ((A+B)^p)_n = (A^p)_n + (B^p)_n + p·(C_n)。誤差項の p-整除性の
    供給源。 -/
theorem freshman_zp (p : Nat) (hp : IsPrime p) (A B : PS (zpRing p)) :
    ∃ C : PS (zpRing p), ∀ n,
      psPow (zpRing p) (psAdd (zpRing p) A B) p n
        = (zpRing p).add
            ((zpRing p).add (psPow (zpRing p) A p n) (psPow (zpRing p) B p n))
            (zpMul p ((toZp p).map ((p : Nat) : Int)) (C n)) := by
  obtain ⟨C, hC⟩ := freshman_ps (zpRing p) p hp A B
  refine ⟨C, fun n => ?_⟩
  have h1 := congrFun hC n
  rw [h1]
  show (zpRing p).add
      ((zpRing p).add (psPow (zpRing p) A p n) (psPow (zpRing p) B p n))
      (psMul (zpRing p) (rofNat (psRing (zpRing p)) p) C n)
    = (zpRing p).add
      ((zpRing p).add (psPow (zpRing p) A p n) (psPow (zpRing p) B p n))
      (zpMul p ((toZp p).map ((p : Nat) : Int)) (C n))
  rw [rofNat_ps_eq_psC (zpRing p) p, psC_mul_coeff (zpRing p) (rofNat (zpRing p) p) C n,
    rofNat_zp p p]
  rfl

end IUT
