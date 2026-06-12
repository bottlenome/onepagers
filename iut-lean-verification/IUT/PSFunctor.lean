/-
  IUT/PSFunctor.lean — M46（冪級数の関手性とモノミアル代数: 第九層）

  Lubin–Tate 誤差項の p-整除性は「方程式を mod p に落とすと消える」
  ことの形式化であり、そのために**係数環の環準同型 φ : R → S が
  冪級数環の構造（加法・乗法・冪・合成）を全て保存して持ち上がる**
  ことを示す。誤差項の検証は PS(ℤ_p) → PS(ℤ/p) の還元で
  char p の世界に移して行える。

  併せて単項式 X^m の代数を整備する。mod p で f ≡ X^p となるため、
  F∘f の還元は F̄∘X^p となり、その係数は**伸長公式**
  (F∘X^m)_{mk} = F_k・(F∘X^m)_n = 0 (m ∤ n) で読める。

  * M46-1 `RingHom.map_zero` / `ringHom_rsum` / `ringHom_rpow` —
    環準同型は 0・有限和・冪を保つ
  * M46-2 `rpow_mul_dist` — (ab)^k = a^k b^k（可換環）
  * M46-3 `psMap` — **係数ごとの持ち上げ** PS R → PS S と
    加法・乗法・冪・**合成**の保存
  * M46-4 `psMono` / `psMono_mul` / `psMono_pow` — 単項式の代数
    X^a·X^b = X^{a+b}・(X^m)^k = X^{mk}
  * M46-5 `psComp_mono_coeff` / `psComp_mono_coeff_zero` —
    **伸長公式**: (F∘X^m)_{mk} = F_k、m ∤ n では 0

  残り: char p の Frobenius 定理 F^p = F∘X^p → 誤差項整除性 →
  係数の再帰構成。全て選択公理不使用。
-/
import IUT.Freshman

namespace IUT

/-! ## 環準同型の基本保存則 -/

/-- 環準同型は 0 を保つ。 -/
theorem RingHom.map_zero {R S : CRing} (φ : RingHom R S) :
    φ.map R.zero = S.zero := by
  have h : S.add (φ.map R.zero) (φ.map R.zero) = S.add (φ.map R.zero) S.zero := by
    rw [← φ.map_add, R.zero_add, S.add_zero]
  exact S.add_left_cancel h

/-- 環準同型は有限和を保つ。 -/
theorem ringHom_rsum {R S : CRing} (φ : RingHom R S) (f : Nat → R.carrier) :
    ∀ n, φ.map (rsum R f n) = rsum S (fun k => φ.map (f k)) n := by
  intro n
  induction n with
  | zero => exact φ.map_zero
  | succ n ih =>
    show φ.map (R.add (rsum R f n) (f n))
      = S.add (rsum S (fun k => φ.map (f k)) n) (φ.map (f n))
    rw [φ.map_add, ih]

/-- 環準同型は冪を保つ。 -/
theorem ringHom_rpow {R S : CRing} (φ : RingHom R S) (a : R.carrier) :
    ∀ k, φ.map (rpow R a k) = rpow S (φ.map a) k := by
  intro k
  induction k with
  | zero => exact φ.map_one
  | succ k ih =>
    show φ.map (R.mul (rpow R a k) a) = S.mul (rpow S (φ.map a) k) (φ.map a)
    rw [φ.map_mul, ih]

/-- **M46-2**: (ab)^k = a^k·b^k。 -/
theorem rpow_mul_dist (R : CRing) (a b : R.carrier) : ∀ k,
    rpow R (R.mul a b) k = R.mul (rpow R a k) (rpow R b k) := by
  intro k
  induction k with
  | zero =>
    show R.one = R.mul R.one R.one
    rw [R.one_mul]
  | succ k ih =>
    show R.mul (rpow R (R.mul a b) k) (R.mul a b)
      = R.mul (R.mul (rpow R a k) a) (R.mul (rpow R b k) b)
    rw [ih, R.mul_assoc (rpow R a k) (rpow R b k) (R.mul a b),
      ← R.mul_assoc (rpow R b k) a b,
      R.mul_comm (rpow R b k) a,
      R.mul_assoc a (rpow R b k) b,
      ← R.mul_assoc (rpow R a k) a (R.mul (rpow R b k) b)]

/-! ## 係数ごとの持ち上げ -/

/-- **M46-3a: 係数ごとの持ち上げ** PS R → PS S。 -/
def psMap {R S : CRing} (φ : RingHom R S) (P : PS R) : PS S :=
  fun n => φ.map (P n)

/-- psMap は加法を保つ。 -/
theorem psMap_add {R S : CRing} (φ : RingHom R S) (P Q : PS R) :
    psMap φ (psAdd R P Q) = psAdd S (psMap φ P) (psMap φ Q) := by
  funext n
  exact φ.map_add (P n) (Q n)

/-- **M46-3b: psMap は乗法を保つ**（Cauchy 積と有限和保存）。 -/
theorem psMap_mul {R S : CRing} (φ : RingHom R S) (P Q : PS R) :
    psMap φ (psMul R P Q) = psMul S (psMap φ P) (psMap φ Q) := by
  funext n
  have h1 : φ.map (rsum R (fun k => R.mul (P k) (Q (n - k))) (n + 1))
      = rsum S (fun k => φ.map (R.mul (P k) (Q (n - k)))) (n + 1) :=
    ringHom_rsum φ _ (n + 1)
  show φ.map (rsum R (fun k => R.mul (P k) (Q (n - k))) (n + 1))
    = rsum S (fun k => S.mul (psMap φ P k) (psMap φ Q (n - k))) (n + 1)
  rw [h1]
  exact rsum_congr S (n + 1) (fun k _ => φ.map_mul (P k) (Q (n - k)))

/-- psMap は冪を保つ。 -/
theorem psMap_pow {R S : CRing} (φ : RingHom R S) (P : PS R) : ∀ k,
    psMap φ (psPow R P k) = psPow S (psMap φ P) k := by
  intro k
  induction k with
  | zero =>
    funext n
    cases n with
    | zero => exact φ.map_one
    | succ m => exact φ.map_zero
  | succ k ih =>
    have h1 : psMap φ (psMul R (psPow R P k) P)
        = psMul S (psMap φ (psPow R P k)) (psMap φ P) := psMap_mul φ _ _
    show psMap φ (psMul R (psPow R P k) P)
      = psMul S (psPow S (psMap φ P) k) (psMap φ P)
    rw [h1, ih]

/-- **定理 (M46-3c): psMap は合成を保つ** — mod-p 還元で
    F∘g ↦ F̄∘ḡ となることの一般形。 -/
theorem psMap_comp {R S : CRing} (φ : RingHom R S) (P Q : PS R) :
    psMap φ (psComp R P Q) = psComp S (psMap φ P) (psMap φ Q) := by
  funext n
  have h1 : φ.map (rsum R (fun k => R.mul (P k) (psPow R Q k n)) (n + 1))
      = rsum S (fun k => φ.map (R.mul (P k) (psPow R Q k n))) (n + 1) :=
    ringHom_rsum φ _ (n + 1)
  show φ.map (rsum R (fun k => R.mul (P k) (psPow R Q k n)) (n + 1))
    = rsum S (fun k => S.mul (psMap φ P k) (psPow S (psMap φ Q) k n)) (n + 1)
  rw [h1]
  exact rsum_congr S (n + 1) (fun k _ => by
    have h2 : φ.map (psPow R Q k n) = psPow S (psMap φ Q) k n :=
      congrFun (psMap_pow φ Q k) n
    rw [φ.map_mul (P k) (psPow R Q k n), h2]
    rfl)

/-! ## モノミアル代数 -/

/-- 単項式 X^m（係数 1）。 -/
def psMono (R : CRing) (m : Nat) : PS R :=
  fun n => if n = m then R.one else R.zero

/-- **M46-4a**: X^a·X^b = X^{a+b}。 -/
theorem psMono_mul (R : CRing) (a b : Nat) :
    psMul R (psMono R a) (psMono R b) = psMono R (a + b) := by
  funext n
  show rsum R (fun k => R.mul (psMono R a k) (psMono R b (n - k))) (n + 1)
    = psMono R (a + b) n
  cases Nat.decEq n (a + b) with
  | isTrue he =>
    subst he
    have hs : rsum R (fun k => R.mul (psMono R a k) (psMono R b (a + b - k)))
          (a + b + 1)
        = R.mul (psMono R a a) (psMono R b (a + b - a)) :=
      rsum_single R _ a (a + b + 1) (by omega) (fun j hj hne => by
        rw [show psMono R a j = R.zero from if_neg hne]
        exact R.zero_mul _)
    rw [hs, show a + b - a = b by omega,
      show psMono R a a = R.one from if_pos rfl,
      show psMono R b b = R.one from if_pos rfl,
      show psMono R (a + b) (a + b) = R.one from if_pos rfl,
      R.one_mul]
  | isFalse hne =>
    have hc : rsum R (fun k => R.mul (psMono R a k) (psMono R b (n - k))) (n + 1)
        = rsum R (fun _ => R.zero) (n + 1) :=
      rsum_congr R (n + 1) (fun k hk => by
        cases Nat.decEq k a with
        | isFalse hka =>
          rw [show psMono R a k = R.zero from if_neg hka]
          exact R.zero_mul _
        | isTrue hka =>
          have hnb : n - k ≠ b := by omega
          rw [show psMono R b (n - k) = R.zero from if_neg hnb]
          exact R.mul_zero _)
    rw [hc, rsum_const_zero]
    exact (show psMono R (a + b) n = R.zero from if_neg hne).symm

/-- **M46-4b**: (X^m)^k = X^{mk}。 -/
theorem psMono_pow (R : CRing) (m : Nat) : ∀ k,
    psPow R (psMono R m) k = psMono R (m * k) := by
  intro k
  induction k with
  | zero =>
    show psOne R = psMono R (m * 0)
    rfl
  | succ k ih =>
    show psMul R (psPow R (psMono R m) k) (psMono R m) = psMono R (m * (k + 1))
    rw [ih, psMono_mul]
    rfl

/-! ## 伸長公式 -/

/-- **定理 (M46-5a): 伸長公式（生存項）** — (F∘X^m)_{mk} = F_k。 -/
theorem psComp_mono_coeff (R : CRing) (F : PS R) (m k : Nat) (hm : 1 ≤ m) :
    psComp R F (psMono R m) (m * k) = F k := by
  have hkb : k ≤ m * k := by
    have h1 : 1 * k ≤ m * k := Nat.mul_le_mul_right k hm
    rw [Nat.one_mul] at h1
    exact h1
  show rsum R (fun j => R.mul (F j) (psPow R (psMono R m) j (m * k))) (m * k + 1)
    = F k
  have hs : rsum R (fun j => R.mul (F j) (psPow R (psMono R m) j (m * k)))
        (m * k + 1)
      = R.mul (F k) (psPow R (psMono R m) k (m * k)) :=
    rsum_single R _ k (m * k + 1) (by omega) (fun j hj hne => by
      have hp : psPow R (psMono R m) j (m * k) = psMono R (m * j) (m * k) :=
        congrFun (psMono_pow R m j) (m * k)
      rw [hp, show psMono R (m * j) (m * k) = R.zero from if_neg (fun h =>
        hne (Nat.eq_of_mul_eq_mul_left (by omega) h).symm)]
      exact R.mul_zero _)
  rw [hs]
  have hp : psPow R (psMono R m) k (m * k) = psMono R (m * k) (m * k) :=
    congrFun (psMono_pow R m k) (m * k)
  rw [hp, show psMono R (m * k) (m * k) = R.one from if_pos rfl, R.mul_one]

/-- **定理 (M46-5b): 伸長公式（消滅項）** — m ∤ n なら (F∘X^m)_n = 0。 -/
theorem psComp_mono_coeff_zero (R : CRing) (F : PS R) (m n : Nat)
    (h : ¬ m ∣ n) : psComp R F (psMono R m) n = R.zero := by
  show rsum R (fun j => R.mul (F j) (psPow R (psMono R m) j n)) (n + 1) = R.zero
  have hc : rsum R (fun j => R.mul (F j) (psPow R (psMono R m) j n)) (n + 1)
      = rsum R (fun _ => R.zero) (n + 1) :=
    rsum_congr R (n + 1) (fun j hj => by
      have hp : psPow R (psMono R m) j n = psMono R (m * j) n :=
        congrFun (psMono_pow R m j) n
      rw [hp, show psMono R (m * j) n = R.zero from if_neg (fun he =>
        h ⟨j, he⟩)]
      exact R.mul_zero _)
  rw [hc]
  exact rsum_const_zero R (n + 1)

end IUT
