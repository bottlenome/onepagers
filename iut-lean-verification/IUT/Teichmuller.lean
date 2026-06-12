/-
  IUT/Teichmuller.lean — M33（Teichmüller 持ち上げ ω(a) = lim a^{p^n}）

  O^× = μ_{p−1} × (1+m) 分解の μ 部。各レベルで a^{p^n} mod p^n を
  取る族が逆極限の整合族をなすことを M32 の Fermat の小定理から導き、
  **Teichmüller 持ち上げ ω : ℤ → ℤ_p を実構成**する。

  * M33-1 `ipow_add` / `ipow_mul` / `mul_ipow` / `one_ipow` — 冪の指数法則
  * M33-2 `facSum` / `pow_sub_factor` — **因数分解**
    x^n − y^n = (x−y)·Σ_{k<n} x^k y^{n−1−k}（再帰形 S_{n+1} = x·S_n + y^n
    で添字操作を回避）
  * M33-3 `facSum_congr` / `facSum_diag` — 因数和の合同両立と対角値
    Σ_{k<n+1} x^k x^{n−k} = (n+1)·x^n
  * M33-4 `pow_lift` — **持ち上げ補題**: x ≡ y (mod p^n)、n ≥ 1 なら
    x^p ≡ y^p (mod p^{n+1})。x^p − y^p = (x−y)·S で p^n ∣ x−y、
    p ∣ S（S ≡ (p 項の対角和) = p·x^{p−1} mod p）
  * M33-5 `teich_step` / `teich_coherent` — **整合性**:
    p^{n+1} ∣ a^{p^{n+1}} − a^{p^n}（基底 = Fermat の小定理、帰納段 =
    持ち上げ補題）とその望遠鏡和
  * M33-6 `teich` — **Teichmüller 持ち上げ ω(a) = lim a^{p^n} : ℤ_p**
  * M33-7 `teich_reduction` — ω(a) ≡ a (mod p)（レベル 1 で a を復元 =
    「剰余体の持ち上げ」。証明は FLT そのもの）
  * M33-8 `teich_mul` / `teich_one` — **乗法性** ω(ab) = ω(a)·ω(b)、
    ω(1) = 1（Teichmüller 代表系が乗法的切断であること）
  * M33-9 `teich_frobenius` — **Frobenius 不変性** ω(a^p) = ω(a)
    （X^p = X の根であることの引数側表現）

  未形式化: ω の像が μ_{p−1}（1 の冪根）と一致すること（x^{p−1} = 1 の
  根の個数の評価が必要）、O^× = μ × U^(1) の直積分解そのもの。
  全て選択公理不使用。
-/
import IUT.Fermat

namespace IUT

/-! ## 冪の指数法則 -/

/-- 指数の加法: a^{i+j} = a^i · a^j。 -/
theorem ipow_add (a : Int) (i : Nat) : ∀ j, ipow a (i + j) = ipow a i * ipow a j := by
  intro j
  induction j with
  | zero =>
    show ipow a i = ipow a i * 1
    rw [Int.mul_one]
  | succ j ih =>
    show ipow a (i + j) * a = ipow a i * (ipow a j * a)
    rw [ih, Int.mul_assoc]

/-- 指数の乗法: a^{mk} = (a^m)^k。 -/
theorem ipow_mul (a : Int) (m : Nat) : ∀ k, ipow a (m * k) = ipow (ipow a m) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show ipow a (m * k + m) = ipow (ipow a m) k * ipow a m
    rw [ipow_add, ih]

/-- 底の乗法: (ab)^k = a^k · b^k。 -/
theorem mul_ipow (a b : Int) : ∀ k, ipow (a * b) k = ipow a k * ipow b k := by
  intro k
  induction k with
  | zero =>
    show (1 : Int) = 1 * 1
    rw [Int.one_mul]
  | succ k ih =>
    show ipow (a * b) k * (a * b) = ipow a k * a * (ipow b k * b)
    rw [ih, Int.mul_assoc (ipow a k) (ipow b k) (a * b),
      ← Int.mul_assoc (ipow b k) a b,
      Int.mul_comm (ipow b k) a,
      Int.mul_assoc a (ipow b k) b,
      ← Int.mul_assoc (ipow a k) a (ipow b k * b)]

/-- 1^k = 1。 -/
theorem one_ipow : ∀ k, ipow (1 : Int) k = 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show ipow 1 k * 1 = 1
    rw [Int.mul_one, ih]

/-! ## 因数分解 x^n − y^n = (x − y)·S -/

/-- 因数和 Σ_{k<n} x^k y^{n−1−k}（再帰形 S_{n+1} = x·S_n + y^n）。 -/
def facSum (x y : Int) : Nat → Int
  | 0 => 0
  | n + 1 => x * facSum x y n + ipow y n

/-- **M33-2: 因数分解** x^n − y^n = (x−y)·facSum x y n。 -/
theorem pow_sub_factor (x y : Int) : ∀ n,
    ipow x n - ipow y n = (x - y) * facSum x y n := by
  intro n
  induction n with
  | zero =>
    show (1 : Int) - 1 = (x - y) * 0
    rw [Int.mul_zero]
    omega
  | succ n ih =>
    show ipow x n * x - ipow y n * y = (x - y) * (x * facSum x y n + ipow y n)
    rw [Int.mul_add]
    have h1 : (x - y) * (x * facSum x y n) = x * ((x - y) * facSum x y n) := by
      rw [← Int.mul_assoc, Int.mul_comm (x - y) x, Int.mul_assoc]
    rw [h1, ← ih, Int.mul_sub, Int.sub_mul,
      Int.mul_comm x (ipow x n), Int.mul_comm x (ipow y n), Int.mul_comm y (ipow y n)]
    generalize ipow x n * x = A
    generalize ipow y n * x = B
    generalize ipow y n * y = C
    omega

/-- 補題: N ∣ A−B なら N ∣ cA − cB。 -/
theorem dvd_sub_mul_left {N A B : Int} (h : N ∣ A - B) (c : Int) :
    N ∣ c * A - c * B := by
  obtain ⟨k, hk⟩ := h
  refine ⟨c * k, ?_⟩
  rw [← Int.mul_sub, hk, ← Int.mul_assoc, Int.mul_comm c N, Int.mul_assoc]

/-- **M33-3a: 因数和の合同両立** — N ∣ x−y なら
    N ∣ facSum x y n − facSum x x n。 -/
theorem facSum_congr {N x y : Int} (h : N ∣ x - y) : ∀ n,
    N ∣ facSum x y n - facSum x x n := by
  intro n
  induction n with
  | zero => exact dvd_sub_refl _ _
  | succ n ih =>
    exact dvd_sub_add (dvd_sub_mul_left ih x) (dvd_sub_ipow (dvd_sub_symm h) n)

/-- **M33-3b: 因数和の対角値** — facSum x x (n+1) = (n+1)·x^n。 -/
theorem facSum_diag (x : Int) : ∀ n,
    facSum x x (n + 1) = ((n + 1 : Nat) : Int) * ipow x n := by
  intro n
  induction n with
  | zero =>
    show x * 0 + 1 = ((1 : Nat) : Int) * 1
    omega
  | succ n ih =>
    show x * facSum x x (n + 1) + ipow x (n + 1)
      = ((n + 2 : Nat) : Int) * ipow x (n + 1)
    rw [ih]
    have hc : ((n + 2 : Nat) : Int) = ((n + 1 : Nat) : Int) + 1 := by omega
    rw [hc, Int.add_mul, Int.one_mul]
    have hx : x * (((n + 1 : Nat) : Int) * ipow x n)
        = ((n + 1 : Nat) : Int) * ipow x (n + 1) := by
      show x * (((n + 1 : Nat) : Int) * ipow x n)
        = ((n + 1 : Nat) : Int) * (ipow x n * x)
      rw [← Int.mul_assoc, Int.mul_comm x ((n + 1 : Nat) : Int), Int.mul_assoc,
        Int.mul_comm x (ipow x n)]
    rw [hx]

/-- **定理 (M33-4): 持ち上げ補題** — x ≡ y (mod p^n)、n ≥ 1 なら
    x^p ≡ y^p (mod p^{n+1})。Teichmüller 整合性の帰納段。 -/
theorem pow_lift (p : Nat) (hp : IsPrime p) {x y : Int} {n : Nat}
    (h : ((p ^ n : Nat) : Int) ∣ x - y) (hn : 1 ≤ n) :
    ((p ^ (n + 1) : Nat) : Int) ∣ ipow x p - ipow y p := by
  have hfac := pow_sub_factor x y p
  have hpx : ((p : Nat) : Int) ∣ x - y :=
    Int.dvd_trans (cast_dvd_pow p n hn) h
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.1; omega⟩
  have hdiag : ((p : Nat) : Int) ∣ facSum x x p := by
    rw [hm, facSum_diag x m]
    exact ⟨ipow x m, rfl⟩
  have hS : ((p : Nat) : Int) ∣ facSum x y p := by
    obtain ⟨c1, hc1⟩ := facSum_congr hpx p
    obtain ⟨c2, hc2⟩ := hdiag
    refine ⟨c1 + c2, ?_⟩
    rw [Int.mul_add, ← hc1, ← hc2]
    generalize facSum x y p = S
    generalize facSum x x p = D
    omega
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := hS
  refine ⟨a * b, ?_⟩
  rw [hfac, ha, hb, cast_pow_succ, Int.mul_assoc,
    ← Int.mul_assoc a ((p : Nat) : Int) b,
    Int.mul_comm a ((p : Nat) : Int),
    Int.mul_assoc ((p : Nat) : Int) a b,
    ← Int.mul_assoc]

/-! ## Teichmüller 整合性と持ち上げの構成 -/

/-- **M33-5a: 一段の整合性** — p^{n+1} ∣ a^{p^{n+1}} − a^{p^n}
    （基底 = Fermat の小定理、帰納段 = 持ち上げ補題）。 -/
theorem teich_step (p : Nat) (hp : IsPrime p) (a : Int) : ∀ n,
    ((p ^ (n + 1) : Nat) : Int) ∣ ipow a (p ^ (n + 1)) - ipow a (p ^ n) := by
  intro n
  induction n with
  | zero =>
    show ((p ^ 1 : Nat) : Int) ∣ ipow a (p ^ 1) - ipow a (p ^ 0)
    rw [Nat.pow_one, Nat.pow_zero]
    have h1 : ipow a 1 = a := by
      show (1 : Int) * a = a
      rw [Int.one_mul]
    rw [h1]
    exact fermat_little p hp a
  | succ n ih =>
    have hl := pow_lift p hp ih (by omega)
    rw [← ipow_mul, ← ipow_mul, ← Nat.pow_succ, ← Nat.pow_succ] at hl
    exact hl

/-- **M33-5b: 整合性の望遠鏡和** — i ≤ j なら
    p^i ∣ a^{p^j} − a^{p^i}。 -/
theorem teich_coherent (p : Nat) (hp : IsPrime p) (a : Int) {i j : Nat}
    (h : i ≤ j) :
    ((p ^ i : Nat) : Int) ∣ ipow a (p ^ j) - ipow a (p ^ i) := by
  induction h with
  | refl => exact dvd_sub_refl _ _
  | @step m h' ih =>
    have hstep' : ((p ^ i : Nat) : Int)
        ∣ ipow a (p ^ (m + 1)) - ipow a (p ^ m) :=
      Int.dvd_trans (Int.ofNat_dvd.mpr (pow_dvd_mono p (Nat.le_trans h' (Nat.le_succ m))))
        (teich_step p hp a m)
    exact dvd_sub_trans hstep' ih

/-- **定理 (M33-6): Teichmüller 持ち上げ** ω(a) = lim a^{p^n} : ℤ_p
    の実構成。整合性は M33-5。 -/
def teich (p : Nat) (hp : IsPrime p) (a : Int) : (Zp p).carrier :=
  ⟨fun n => Quot.mk (modCong (p ^ n)).rel (ipow a (p ^ n)), by
    intro i j h
    show (zmodTrans (pow_dvd_mono p h)).map
        (Quot.mk (modCong (p ^ j)).rel (ipow a (p ^ j)))
      = Quot.mk (modCong (p ^ i)).rel (ipow a (p ^ i))
    exact Quot.sound (teich_coherent p hp a h)⟩

/-- **定理 (M33-7): 剰余の復元** — ω(a) ≡ a (mod p)。レベル 1 への
    射影が a を返す（証明の中身は Fermat の小定理そのもの）。 -/
theorem teich_reduction (p : Nat) (hp : IsPrime p) (a : Int) :
    (teich p hp a).val 1 = Quot.mk (modCong (p ^ 1)).rel a := by
  show Quot.mk (modCong (p ^ 1)).rel (ipow a (p ^ 1))
    = Quot.mk (modCong (p ^ 1)).rel a
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ ipow a (p ^ 1) - a
  rw [Nat.pow_one]
  exact fermat_little p hp a

/-- **定理 (M33-8a): 乗法性** — ω(ab) = ω(a)·ω(b)。Teichmüller 代表系
    が乗法的切断であること。 -/
theorem teich_mul (p : Nat) (hp : IsPrime p) (a b : Int) :
    teich p hp (a * b) = zpMul p (teich p hp a) (teich p hp b) := by
  apply Subtype.ext
  funext n
  show Quot.mk (modCong (p ^ n)).rel (ipow (a * b) (p ^ n))
    = zmodMul (p ^ n) (Quot.mk (modCong (p ^ n)).rel (ipow a (p ^ n)))
      (Quot.mk (modCong (p ^ n)).rel (ipow b (p ^ n)))
  rw [mul_ipow]
  rfl

/-- **M33-8b**: ω(1) = 1。 -/
theorem teich_one (p : Nat) (hp : IsPrime p) : teich p hp 1 = zpOne p := by
  apply Subtype.ext
  funext n
  show Quot.mk (modCong (p ^ n)).rel (ipow 1 (p ^ n))
    = Quot.mk (modCong (p ^ n)).rel 1
  rw [one_ipow]

/-- **定理 (M33-9): Frobenius 不変性** — ω(a^p) = ω(a)。
    Teichmüller 代表が X^p = X の根であることの引数側表現。 -/
theorem teich_frobenius (p : Nat) (hp : IsPrime p) (a : Int) :
    teich p hp (ipow a p) = teich p hp a := by
  apply Subtype.ext
  funext n
  show Quot.mk (modCong (p ^ n)).rel (ipow (ipow a p) (p ^ n))
    = Quot.mk (modCong (p ^ n)).rel (ipow a (p ^ n))
  apply Quot.sound
  show ((p ^ n : Nat) : Int) ∣ ipow (ipow a p) (p ^ n) - ipow a (p ^ n)
  have he : ipow (ipow a p) (p ^ n) = ipow a (p ^ (n + 1)) := by
    rw [← ipow_mul]
    have hexp : p * p ^ n = p ^ (n + 1) := by
      rw [Nat.mul_comm, ← Nat.pow_succ]
    rw [hexp]
  rw [he]
  exact teich_coherent p hp a (Nat.le_succ n)

end IUT
