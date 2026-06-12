/-
  IUT/FrobeniusCharP.lean — M47（標数 p の Frobenius 定理: F^p = F∘X^p）

  Lubin–Tate 誤差項 p-整除性の核心定理。係数環 S := ℤ/p（= zmodRing (p^1)）
  の冪級数環で

    F^p = F ∘ X^p   （すなわち (F^p)_{pk} = F_k、p ∤ n では (F^p)_n = 0）

  を完全証明する。証明は truncation（打ち切り）の帰納:
  trunc F (N+1) = trunc F N + F_N·X^N と分解し、**char p では M45 の
  新入生の夢が正確な等式になる**（p·C 項が rofNat S p = 0 で消滅）
  ことと、単項式の冪 (c·X^N)^p = c^p·X^{Np} = c·X^{Np}（係数 FLT）で
  一段ずつ剥がす。係数 n での一般の F への帰着は M41 の psPow_congr
  （冪の係数は有限個の係数で決まる）による。

  * M47-1 `rofNat_zmod` / `zmod_char` / `rpow_zmod` / `zmod_flt` —
    ℤ/p の標数 p と係数 FLT c^p = c
  * M47-2 `psC_zero` / `freshman_exact` — **char p の正確な新入生の夢**
    (A+B)^p = A^p + B^p
  * M47-3 `psTrunc` / `psSingle` — 打ち切りと単項式、分解
    trunc (N+1) = trunc N + F_N·X^N、**(c·X^m)^k = c^k·X^{mk}**
  * M47-4 `psComp_single` — 単項式の合成 (c·X^N)∘X^m = c·X^{mN}
  * M47-5 `frobenius_trunc` / `frobenius_charp` — **Frobenius 定理**
    F^p = F∘X^p（truncation 帰納 → psPow_congr で一般化）

  残り: mod-p 還元（M46 の psMap）で LT 誤差項の p-整除性 →
  係数の再帰構成。全て選択公理不使用。
-/
import IUT.PSFunctor

namespace IUT

/-! ## ℤ/p の標数と係数 FLT -/

/-- rofNat (ℤ/n) = 剰余類。 -/
theorem rofNat_zmod (n : Nat) : ∀ m,
    rofNat (zmodRing n) m = Quot.mk (modCong n).rel ((m : Nat) : Int) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    show (zmod n).mul (rofNat (zmodRing n) m) (Quot.mk (modCong n).rel 1)
      = Quot.mk (modCong n).rel ((m + 1 : Nat) : Int)
    rw [ih]
    show Quot.mk (modCong n).rel (((m : Nat) : Int) + 1)
      = Quot.mk (modCong n).rel ((m + 1 : Nat) : Int)
    rw [show ((m : Nat) : Int) + 1 = ((m + 1 : Nat) : Int) by omega]

/-- **M47-1a: 標数 p** — rofNat (ℤ/p) p = 0。 -/
theorem zmod_char (p : Nat) :
    rofNat (zmodRing (p ^ 1)) p = (zmodRing (p ^ 1)).zero := by
  rw [rofNat_zmod (p ^ 1) p]
  show Quot.mk (modCong (p ^ 1)).rel ((p : Nat) : Int)
    = Quot.mk (modCong (p ^ 1)).rel 0
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ ((p : Nat) : Int) - 0
  rw [Nat.pow_one]
  exact ⟨1, by omega⟩

/-- rpow (ℤ/n) は代表の ipow。 -/
theorem rpow_zmod (n : Nat) (a : Int) : ∀ k,
    rpow (zmodRing n) (Quot.mk (modCong n).rel a) k
      = Quot.mk (modCong n).rel (ipow a k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show zmodMul n (rpow (zmodRing n) (Quot.mk (modCong n).rel a) k)
        (Quot.mk (modCong n).rel a) = Quot.mk (modCong n).rel (ipow a k * a)
    rw [ih]
    rfl

/-- **M47-1b: 係数 FLT** — ℤ/p で c^p = c。 -/
theorem zmod_flt (p : Nat) (hp : IsPrime p) (c : (zmodRing (p ^ 1)).carrier) :
    rpow (zmodRing (p ^ 1)) c p = c := by
  induction c using Quot.ind
  rename_i a
  rw [rpow_zmod (p ^ 1) a p]
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ ipow a p - a
  rw [Nat.pow_one]
  exact fermat_little p hp a

/-! ## char p の正確な新入生の夢 -/

/-- psC 0 = 0。 -/
theorem psC_zero (R : CRing) : psC R R.zero = psZero R := by
  funext n
  cases n with
  | zero => rfl
  | succ m => rfl

/-- **定理 (M47-2): 正確な新入生の夢（char p）** —
    (A+B)^p = A^p + B^p in PS(ℤ/p)。 -/
theorem freshman_exact (p : Nat) (hp : IsPrime p)
    (A B : PS (zmodRing (p ^ 1))) :
    psPow (zmodRing (p ^ 1)) (psAdd (zmodRing (p ^ 1)) A B) p
      = (psRing (zmodRing (p ^ 1))).add (psPow (zmodRing (p ^ 1)) A p)
          (psPow (zmodRing (p ^ 1)) B p) := by
  obtain ⟨C, hC⟩ := freshman_ps (zmodRing (p ^ 1)) p hp A B
  rw [hC, rofNat_ps_eq_psC (zmodRing (p ^ 1)) p, zmod_char p, psC_zero,
    show (psRing (zmodRing (p ^ 1))).mul (psZero (zmodRing (p ^ 1))) C
      = (psRing (zmodRing (p ^ 1))).zero from CRing.zero_mul (psRing _) C]
  exact CRing.add_zero (psRing _) _

/-! ## 打ち切りと単項式 -/

/-- 打ち切り（N 次未満を残す）。 -/
def psTrunc (R : CRing) (F : PS R) (N : Nat) : PS R :=
  fun n => if n < N then F n else R.zero

/-- 単項式 c·X^m。 -/
def psSingle (R : CRing) (c : R.carrier) (m : Nat) : PS R :=
  fun n => if n = m then c else R.zero

theorem psTrunc_zero (R : CRing) (F : PS R) : psTrunc R F 0 = psZero R := by
  funext n
  exact if_neg (by omega)

theorem psTrunc_agree (R : CRing) (F : PS R) (N : Nat) {i : Nat} (h : i < N) :
    psTrunc R F N i = F i := if_pos h

/-- 打ち切りの一段分解: trunc (N+1) = trunc N + F_N·X^N。 -/
theorem psTrunc_succ (R : CRing) (F : PS R) (N : Nat) :
    psTrunc R F (N + 1) = psAdd R (psTrunc R F N) (psSingle R (F N) N) := by
  funext n
  show psTrunc R F (N + 1) n = R.add (psTrunc R F N n) (psSingle R (F N) N n)
  cases Nat.lt_or_ge n N with
  | inl h =>
    rw [show psTrunc R F (N + 1) n = F n from if_pos (by omega),
      show psTrunc R F N n = F n from if_pos h,
      show psSingle R (F N) N n = R.zero from if_neg (by omega),
      R.add_zero]
  | inr h =>
    cases Nat.decEq n N with
    | isTrue he =>
      rw [show psTrunc R F (N + 1) n = F n from if_pos (by omega),
        show psTrunc R F N n = R.zero from if_neg (by omega),
        show psSingle R (F N) N n = F N from if_pos he,
        R.zero_add, he]
    | isFalse he =>
      rw [show psTrunc R F (N + 1) n = R.zero from if_neg (by omega),
        show psTrunc R F N n = R.zero from if_neg (by omega),
        show psSingle R (F N) N n = R.zero from if_neg he,
        R.zero_add]

/-- 単項式 = 定数 × X^m。 -/
theorem psSingle_eq (R : CRing) (c : R.carrier) (m : Nat) :
    psSingle R c m = psMul R (psC R c) (psMono R m) := by
  funext n
  rw [psC_mul_coeff R c (psMono R m) n]
  cases Nat.decEq n m with
  | isTrue he =>
    rw [show psSingle R c m n = c from if_pos he,
      show psMono R m n = R.one from if_pos he, R.mul_one]
  | isFalse he =>
    rw [show psSingle R c m n = R.zero from if_neg he,
      show psMono R m n = R.zero from if_neg he, R.mul_zero]

/-- **M47-3: 単項式の冪** (c·X^m)^k = c^k·X^{mk}。 -/
theorem psSingle_pow (R : CRing) (c : R.carrier) (m k : Nat) :
    psPow R (psSingle R c m) k = psSingle R (rpow R c k) (m * k) := by
  have hC : psPow R (psC R c) k = psC R (rpow R c k) := by
    rw [psPow_eq_rpow R (psC R c) k]
    exact (ringHom_rpow (psConstHom R) c k).symm
  have hdist : rpow (psRing R) (psMul R (psC R c) (psMono R m)) k
      = (psRing R).mul (rpow (psRing R) (psC R c) k)
          (rpow (psRing R) (psMono R m) k) :=
    rpow_mul_dist (psRing R) (psC R c) (psMono R m) k
  rw [psSingle_eq R c m, psSingle_eq R (rpow R c k) (m * k),
    psPow_eq_rpow R (psMul R (psC R c) (psMono R m)) k, hdist,
    ← psPow_eq_rpow R (psC R c) k, ← psPow_eq_rpow R (psMono R m) k,
    hC, psMono_pow R m k]
  rfl

/-- 0^{k+1} = 0（級数）。 -/
theorem psPow_zero_base (R : CRing) (k : Nat) :
    psPow R (psZero R) (k + 1) = psZero R := by
  show (psRing R).mul (psPow R (psZero R) k) (psZero R) = psZero R
  exact CRing.mul_zero (psRing R) _

/-- 0∘Q = 0。 -/
theorem psComp_zero_left (R : CRing) (Q : PS R) :
    psComp R (psZero R) Q = psZero R := by
  funext n
  show rsum R (fun k => R.mul (psZero R k) (psPow R Q k n)) (n + 1) = R.zero
  have hc : rsum R (fun k => R.mul (psZero R k) (psPow R Q k n)) (n + 1)
      = rsum R (fun _ => R.zero) (n + 1) :=
    rsum_congr R (n + 1) (fun k _ => R.zero_mul _)
  rw [hc]
  exact rsum_const_zero R (n + 1)

/-- 合成の左引数係数依存性: (F∘Q)_n は F_0..F_n のみ。 -/
theorem psComp_congr_left (R : CRing) {F F' : PS R} (Q : PS R) (n : Nat)
    (h : ∀ k, k ≤ n → F k = F' k) :
    psComp R F Q n = psComp R F' Q n := by
  show rsum R (fun k => R.mul (F k) (psPow R Q k n)) (n + 1)
    = rsum R (fun k => R.mul (F' k) (psPow R Q k n)) (n + 1)
  exact rsum_congr R (n + 1) (fun k hk => by rw [h k (by omega)])

/-- **定理 (M47-4): 単項式の合成** (c·X^N)∘X^m = c·X^{mN}。 -/
theorem psComp_single (R : CRing) (c : R.carrier) (N m : Nat) (hm : 1 ≤ m) :
    psComp R (psSingle R c N) (psMono R m) = psSingle R c (m * N) := by
  funext n
  show rsum R (fun k => R.mul (psSingle R c N k) (psPow R (psMono R m) k n))
      (n + 1) = psSingle R c (m * N) n
  cases Nat.lt_or_ge n N with
  | inl hlt =>
    have hc : rsum R (fun k => R.mul (psSingle R c N k)
          (psPow R (psMono R m) k n)) (n + 1)
        = rsum R (fun _ => R.zero) (n + 1) :=
      rsum_congr R (n + 1) (fun k hk => by
        rw [show psSingle R c N k = R.zero from if_neg (by omega)]
        exact R.zero_mul _)
    rw [hc, rsum_const_zero]
    have hmN : n ≠ m * N := by
      have h1 : 1 * N ≤ m * N := Nat.mul_le_mul_right N hm
      rw [Nat.one_mul] at h1
      omega
    exact (show psSingle R c (m * N) n = R.zero from if_neg hmN).symm
  | inr hge =>
    have hs : rsum R (fun k => R.mul (psSingle R c N k)
          (psPow R (psMono R m) k n)) (n + 1)
        = R.mul (psSingle R c N N) (psPow R (psMono R m) N n) :=
      rsum_single R _ N (n + 1) (by omega) (fun j hj hne => by
        rw [show psSingle R c N j = R.zero from if_neg hne]
        exact R.zero_mul _)
    have hp : psPow R (psMono R m) N n = psMono R (m * N) n :=
      congrFun (psMono_pow R m N) n
    rw [hs, show psSingle R c N N = c from if_pos rfl, hp]
    cases Nat.decEq n (m * N) with
    | isTrue he =>
      rw [show psMono R (m * N) n = R.one from if_pos he, R.mul_one,
        show psSingle R c (m * N) n = c from if_pos he]
    | isFalse he =>
      rw [show psMono R (m * N) n = R.zero from if_neg he, R.mul_zero,
        show psSingle R c (m * N) n = R.zero from if_neg he]

/-! ## Frobenius 定理 -/

/-- **M47-5a: 打ち切りの Frobenius** — (trunc F N)^p = (trunc F N)∘X^p
    （truncation 帰納 + 正確な新入生の夢 + 係数 FLT）。 -/
theorem frobenius_trunc (p : Nat) (hp : IsPrime p)
    (F : PS (zmodRing (p ^ 1))) : ∀ N,
    psPow (zmodRing (p ^ 1)) (psTrunc (zmodRing (p ^ 1)) F N) p
      = psComp (zmodRing (p ^ 1)) (psTrunc (zmodRing (p ^ 1)) F N)
          (psMono (zmodRing (p ^ 1)) p) := by
  intro N
  induction N with
  | zero =>
    rw [psTrunc_zero, psComp_zero_left]
    obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.1; omega⟩
    rw [hm]
    exact psPow_zero_base _ m
  | succ N ih =>
    rw [psTrunc_succ]
    rw [freshman_exact p hp (psTrunc (zmodRing (p ^ 1)) F N)
      (psSingle (zmodRing (p ^ 1)) (F N) N)]
    rw [ih, psSingle_pow (zmodRing (p ^ 1)) (F N) N p, zmod_flt p hp (F N)]
    have hca : psComp (zmodRing (p ^ 1))
        (psAdd (zmodRing (p ^ 1)) (psTrunc (zmodRing (p ^ 1)) F N)
          (psSingle (zmodRing (p ^ 1)) (F N) N)) (psMono (zmodRing (p ^ 1)) p)
        = (psRing (zmodRing (p ^ 1))).add
            (psComp (zmodRing (p ^ 1)) (psTrunc (zmodRing (p ^ 1)) F N)
              (psMono (zmodRing (p ^ 1)) p))
            (psComp (zmodRing (p ^ 1)) (psSingle (zmodRing (p ^ 1)) (F N) N)
              (psMono (zmodRing (p ^ 1)) p)) :=
      psComp_add (zmodRing (p ^ 1)) _ _ _
    rw [hca, psComp_single (zmodRing (p ^ 1)) (F N) N p (by have := hp.1; omega),
      show N * p = p * N from Nat.mul_comm N p]

/-- **定理 (M47-5b): Frobenius 定理（char p）** — F^p = F∘X^p
    in PS(ℤ/p)。係数 n の値は trunc F (n+1) に一致させて打ち切り版に
    帰着（M41 の psPow_congr と合成の左係数依存性）。 -/
theorem frobenius_charp (p : Nat) (hp : IsPrime p)
    (F : PS (zmodRing (p ^ 1))) :
    psPow (zmodRing (p ^ 1)) F p
      = psComp (zmodRing (p ^ 1)) F (psMono (zmodRing (p ^ 1)) p) := by
  funext n
  have h1 : psPow (zmodRing (p ^ 1)) F p n
      = psPow (zmodRing (p ^ 1)) (psTrunc (zmodRing (p ^ 1)) F (n + 1)) p n :=
    psPow_congr (zmodRing (p ^ 1)) F (psTrunc (zmodRing (p ^ 1)) F (n + 1)) n
      (fun i hi => (psTrunc_agree (zmodRing (p ^ 1)) F (n + 1) (by omega)).symm)
      p n (Nat.le_refl n)
  have h2 : psComp (zmodRing (p ^ 1)) F (psMono (zmodRing (p ^ 1)) p) n
      = psComp (zmodRing (p ^ 1)) (psTrunc (zmodRing (p ^ 1)) F (n + 1))
          (psMono (zmodRing (p ^ 1)) p) n :=
    psComp_congr_left (zmodRing (p ^ 1)) (psMono (zmodRing (p ^ 1)) p) n
      (fun k hk => (psTrunc_agree (zmodRing (p ^ 1)) F (n + 1) (by omega)).symm)
  rw [h1, h2]
  exact congrFun (frobenius_trunc p hp F (n + 1)) n

end IUT
