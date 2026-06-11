/-
  IUT/Fermat.lean — M32（Fermat の小定理の自前証明: Teichmüller 持ち上げの鍵）

  Teichmüller 代表系 ω(a) = lim a^{p^n}（O^× = μ × (1+m) 分解の μ 部）の
  整合性は a^{p^{n+1}} ≡ a^{p^n} (mod p^{n+1}) に懸かっており、その基底が
  **Fermat の小定理** a^p ≡ a (mod p) である。本モジュールは FLT を
  mathlib なし・core のみで完全証明する。経路:

  * M32-1 `chs` — 二項係数の自前定義（Pascal 漸化式）と基本値
    （chs n 0 = 1・chs n n = 1・n < k ⟹ chs n k = 0・chs n 1 = n）
  * M32-2 `succ_mul_chs` — **委員会恒等式** (n+1)·C(n,k) = (k+1)·C(n+1,k+1)
    （二重帰納法、Int を経由しない Nat 証明）
  * M32-3 `bezout` — **Bézout の補題** gcd(a,b) = ax + by（x,y : ℤ）を
    Euclid 互除法の帰納で構成的に証明（燃料付き帰納、選択公理不要）
  * M32-4 `IsPrime` / `euclid` — 素数の定義（2 ≤ p かつ約数は 1 と p のみ）
    と **Euclid の補題** p ∣ ab ⟹ p ∣ a ∨ p ∣ b（Bézout から、決定可能性
    のみ使用）。witness: `isPrime_two`・`isPrime_three`
  * M32-5 `prime_dvd_chs` — **p ∣ C(p,k)**（0 < k < p）: 委員会恒等式
    p·C(p−1,k−1) = k·C(p,k) と Euclid から
  * M32-6 `isum` / `binomial` — 有限和と**二項定理**
    (x+1)^n = Σ_{k≤n} C(n,k) x^k（帰納法 + Pascal、完全証明）
  * M32-7 `freshman` — **新入生の夢** p ∣ (x+1)^p − x^p − 1
    （中間項が全て p で消える）
  * M32-8 `fermat_little` — **Fermat の小定理** p ∣ a^p − a（全ての a : ℤ。
    Nat 帰納 + 剰余による還元）

  全て選択公理不使用。
-/
import IUT.UnitFiltration

namespace IUT

/-! ## 二項係数 -/

/-- 二項係数（Pascal 漸化式による自前定義）。 -/
def chs : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => chs n k + chs n (k + 1)

/-- C(n,0) = 1。 -/
theorem chs_zero : ∀ n, chs n 0 = 1 := by
  intro n
  cases n with
  | zero => rfl
  | succ m => rfl

/-- n < k なら C(n,k) = 0。 -/
theorem chs_gt : ∀ n k, n < k → chs n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    cases k with
    | zero => exact absurd hk (by omega)
    | succ k => rfl
  | succ n ih =>
    intro k hk
    cases k with
    | zero => exact absurd hk (by omega)
    | succ k =>
      show chs n k + chs n (k + 1) = 0
      rw [ih k (by omega), ih (k + 1) (by omega)]

/-- C(n,n) = 1。 -/
theorem chs_self : ∀ n, chs n n = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show chs n n + chs n (n + 1) = 1
    rw [ih, chs_gt n (n + 1) (Nat.lt_succ_self n)]

/-- C(n,1) = n。 -/
theorem chs_one : ∀ n, chs n 1 = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show chs n 0 + chs n 1 = n + 1
    rw [chs_zero, ih]
    omega

/-- 委員会恒等式の帰納段の簿記（Nat、Pascal 展開後の線形結合）。 -/
theorem committee_step (m j A B D : Nat)
    (h1 : m * A = j * (A + B))
    (h2 : m * B = (j + 1) * D) :
    (m + 1) * (A + B) = (j + 1) * (A + B + D) := by
  rw [Nat.add_mul m 1 (A + B), Nat.one_mul,
    Nat.mul_add (j + 1) (A + B) D,
    Nat.add_mul j 1 (A + B), Nat.one_mul,
    Nat.mul_add m A B, h1, h2,
    Nat.mul_add j A B,
    Nat.add_mul j 1 D, Nat.one_mul]
  generalize j * A = P
  generalize j * B = Q
  generalize j * D = R
  omega

/-- **定理 (M32-2): 委員会恒等式** — (n+1)·C(n,k) = (k+1)·C(n+1,k+1)。
    「委員長付き委員会の二重勘定」。p ∣ C(p,k) の鍵。 -/
theorem succ_mul_chs : ∀ n k, (n + 1) * chs n k = (k + 1) * chs (n + 1) (k + 1) := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => rfl
    | succ k =>
      show 1 * chs 0 (k + 1) = (k + 2) * (chs 0 (k + 1) + chs 0 (k + 2))
      show 1 * 0 = (k + 2) * (0 + 0)
      omega
  | succ n ih =>
    intro k
    cases k with
    | zero =>
      show (n + 2) * 1 = 1 * chs (n + 2) 1
      rw [chs_one]
      omega
    | succ k =>
      show (n + 2) * chs (n + 1) (k + 1) = (k + 2) * chs (n + 2) (k + 2)
      have hP : chs (n + 1) (k + 1) = chs n k + chs n (k + 1) := rfl
      have hQ : chs (n + 2) (k + 2) = chs (n + 1) (k + 1) + chs (n + 1) (k + 2) := rfl
      rw [hP, hQ, hP]
      exact committee_step (n + 1) (k + 1) (chs n k) (chs n (k + 1))
        (chs (n + 1) (k + 2)) (ih k) (ih (k + 1))

/-! ## Bézout と Euclid の補題 -/

/-- Bézout の簿記補題（Int 束縛）: A·Q + R = B、G = R·X + A·Y なら
    G = A·(Y − Q·X) + B·X。 -/
theorem bezout_step (G A B Q R X Y : Int) (h1 : A * Q + R = B)
    (h2 : G = R * X + A * Y) : G = A * (Y - Q * X) + B * X := by
  have hR : R = B - A * Q := by
    revert h1
    generalize A * Q = W
    intro h1
    omega
  rw [h2, hR, Int.sub_mul, Int.mul_sub, ← Int.mul_assoc]
  generalize B * X = m1
  generalize A * Q * X = m2
  generalize A * Y = m3
  omega

/-- Bézout の補題（燃料付き帰納）。 -/
theorem bezout_aux : ∀ N a b, a ≤ N →
    ∃ x y : Int, ((Nat.gcd a b : Nat) : Int) = ((a : Nat) : Int) * x + ((b : Nat) : Int) * y := by
  intro N
  induction N with
  | zero =>
    intro a b ha
    have ha0 : a = 0 := Nat.le_zero.mp ha
    subst ha0
    refine ⟨0, 1, ?_⟩
    rw [Nat.gcd_zero_left]
    omega
  | succ N ihN =>
    intro a b ha
    cases a with
    | zero =>
      refine ⟨0, 1, ?_⟩
      rw [Nat.gcd_zero_left]
      omega
    | succ a' =>
      have hlt : b % (a' + 1) < a' + 1 := Nat.mod_lt b (by omega)
      obtain ⟨x, y, hxy⟩ := ihN (b % (a' + 1)) (a' + 1) (by omega)
      have hdm := Nat.div_add_mod b (a' + 1)
      have hdmZ : ((a' + 1 : Nat) : Int) * ((b / (a' + 1) : Nat) : Int)
          + ((b % (a' + 1) : Nat) : Int) = ((b : Nat) : Int) := by
        rw [← Int.natCast_mul, ← Int.natCast_add, hdm]
      refine ⟨y - ((b / (a' + 1) : Nat) : Int) * x, x, ?_⟩
      rw [Nat.gcd_rec (a' + 1) b]
      exact bezout_step _ _ _ _ _ _ _ hdmZ hxy

/-- **定理 (M32-3): Bézout の補題** — gcd(a,b) = ax + by となる
    整数 x, y が存在する（Euclid 互除法による構成的証明）。 -/
theorem bezout (a b : Nat) :
    ∃ x y : Int, ((Nat.gcd a b : Nat) : Int) = ((a : Nat) : Int) * x + ((b : Nat) : Int) * y :=
  bezout_aux a a b (Nat.le_refl a)

/-- **M32-4a: 素数の定義** — 2 ≤ p かつ約数は 1 と p のみ。 -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ k, k ∣ p → k = 1 ∨ k = p

/-- 素数と割り切らない数は互いに素。 -/
theorem prime_gcd_one (p : Nat) (hp : IsPrime p) (k : Nat) (hk : ¬ p ∣ k) :
    Nat.gcd p k = 1 := by
  cases hp.2 (Nat.gcd p k) (Nat.gcd_dvd_left p k) with
  | inl h => exact h
  | inr h =>
    exfalso
    apply hk
    rw [← h]
    exact Nat.gcd_dvd_right p k

/-- Euclid の簿記補題（Int 束縛）: 1 = PX + AY、AB = PC なら
    B = P(XB + CY)。 -/
theorem euclid_combine {P A B X Y C : Int} (h1 : 1 = P * X + A * Y)
    (h2 : A * B = P * C) : B = P * (X * B + C * Y) :=
  calc B = 1 * B := by rw [Int.one_mul]
    _ = (P * X + A * Y) * B := by rw [← h1]
    _ = P * X * B + A * Y * B := by rw [Int.add_mul]
    _ = P * (X * B) + A * Y * B := by rw [Int.mul_assoc P X B]
    _ = P * (X * B) + A * (Y * B) := by rw [Int.mul_assoc A Y B]
    _ = P * (X * B) + A * (B * Y) := by rw [Int.mul_comm Y B]
    _ = P * (X * B) + A * B * Y := by rw [← Int.mul_assoc A B Y]
    _ = P * (X * B) + P * C * Y := by rw [h2]
    _ = P * (X * B) + P * (C * Y) := by rw [Int.mul_assoc P C Y]
    _ = P * (X * B + C * Y) := by rw [← Int.mul_add]

/-- **定理 (M32-4b): Euclid の補題** — p 素数、p ∣ ab なら
    p ∣ a または p ∣ b（Bézout 経由、決定可能性のみで分岐）。 -/
theorem euclid (p : Nat) (hp : IsPrime p) {a b : Nat} (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  cases Nat.decEq (a % p) 0 with
  | isTrue ht => exact Or.inl (Nat.dvd_of_mod_eq_zero ht)
  | isFalse hf =>
    right
    have hnd : ¬ p ∣ a := fun hd => hf (Nat.mod_eq_zero_of_dvd hd)
    obtain ⟨x, y, hxy⟩ := bezout p a
    rw [prime_gcd_one p hp a hnd] at hxy
    have h1 : (1 : Int) = ((p : Nat) : Int) * x + ((a : Nat) : Int) * y := hxy
    obtain ⟨c, hc⟩ := h
    have h2 : ((a : Nat) : Int) * ((b : Nat) : Int)
        = ((p : Nat) : Int) * ((c : Nat) : Int) := by
      rw [← Int.natCast_mul, ← Int.natCast_mul, hc]
    exact Int.ofNat_dvd.mp ⟨x * ((b : Nat) : Int) + ((c : Nat) : Int) * y,
      euclid_combine h1 h2⟩

/-- witness: 2 は素数。 -/
theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, fun k hk => ?_⟩
  have h2 : k ≤ 2 := Nat.le_of_dvd (by omega) hk
  have h0 : k ≠ 0 := by
    intro h
    subst h
    exact absurd (Nat.eq_zero_of_zero_dvd hk) (by omega)
  cases Nat.lt_or_ge k 2 with
  | inl h => left; omega
  | inr h => right; omega

/-- witness: 3 は素数。 -/
theorem isPrime_three : IsPrime 3 := by
  refine ⟨by omega, fun k hk => ?_⟩
  have h3 : k ≤ 3 := Nat.le_of_dvd (by omega) hk
  have h0 : k ≠ 0 := by
    intro h
    subst h
    exact absurd (Nat.eq_zero_of_zero_dvd hk) (by omega)
  have h2 : k ≠ 2 := by
    intro h
    subst h
    obtain ⟨c, hc⟩ := hk
    omega
  cases Nat.lt_or_ge k 2 with
  | inl h => left; omega
  | inr h => right; omega

/-- **定理 (M32-5): p ∣ C(p,k)**（0 < k < p、p 素数）—
    委員会恒等式 p·C(p−1,k−1) = k·C(p,k) と Euclid の補題から。 -/
theorem prime_dvd_chs (p : Nat) (hp : IsPrime p) (k : Nat)
    (hk0 : 0 < k) (hkp : k < p) : p ∣ chs p k := by
  obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := hp.1; omega⟩
  obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  subst hp' hk'
  have hdvd : (p' + 1) ∣ (k' + 1) * chs (p' + 1) (k' + 1) :=
    ⟨chs p' k', (succ_mul_chs p' k').symm⟩
  cases euclid (p' + 1) hp hdvd with
  | inl h => exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  | inr h => exact h

/-! ## 有限和と二項定理 -/

/-- 有限和 Σ_{k<n} f k。 -/
def isum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => isum f n + f n

/-- 有限和は範囲内の値だけで決まる。 -/
theorem isum_congr {f g : Nat → Int} : ∀ n, (∀ k, k < n → f k = g k) →
    isum f n = isum g n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    show isum f n + f n = isum g n + g n
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

/-- 有限和の加法性。 -/
theorem isum_add (f g : Nat → Int) : ∀ n,
    isum (fun k => f k + g k) n = isum f n + isum g n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show isum (fun k => f k + g k) n + (f n + g n)
      = (isum f n + f n) + (isum g n + g n)
    rw [ih]
    generalize isum f n = S
    generalize isum g n = T
    generalize f n = A
    generalize g n = B
    omega

/-- 有限和と定数倍。 -/
theorem isum_mul (f : Nat → Int) (c : Int) : ∀ n,
    isum f n * c = isum (fun k => f k * c) n := by
  intro n
  induction n with
  | zero =>
    show (0 : Int) * c = 0
    rw [Int.zero_mul]
  | succ n ih =>
    show (isum f n + f n) * c = isum (fun k => f k * c) n + f n * c
    rw [Int.add_mul, ih]

/-- 有限和の頭出し: Σ_{k<n+1} f k = f 0 + Σ_{k<n} f (k+1)。 -/
theorem isum_shift (f : Nat → Int) : ∀ n,
    isum f (n + 1) = f 0 + isum (fun k => f (k + 1)) n := by
  intro n
  induction n with
  | zero =>
    show (0 : Int) + f 0 = f 0 + 0
    generalize f 0 = a
    omega
  | succ n ih =>
    show isum f (n + 1) + f (n + 1)
      = f 0 + (isum (fun k => f (k + 1)) n + f (n + 1))
    rw [ih]
    generalize f 0 = a
    generalize isum (fun k => f (k + 1)) n = S
    generalize f (n + 1) = b
    omega

/-- 各項が割り切れれば和も割り切れる。 -/
theorem isum_dvd (N : Int) (f : Nat → Int) : ∀ n,
    (∀ k, k < n → N ∣ f k) → N ∣ isum f n := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, ?_⟩
    show (0 : Int) = N * 0
    rw [Int.mul_zero]
  | succ n ih =>
    intro h
    obtain ⟨c, hc⟩ := ih (fun k hk => h k (by omega))
    obtain ⟨d, hd⟩ := h n (by omega)
    refine ⟨c + d, ?_⟩
    show isum f n + f n = N * (c + d)
    rw [Int.mul_add, ← hc, ← hd]

/-- **定理 (M32-6): 二項定理** — (x+1)^n = Σ_{k≤n} C(n,k) x^k
    （帰納法 + Pascal 漸化式による完全証明）。 -/
theorem binomial (x : Int) : ∀ n,
    ipow (x + 1) n = isum (fun k => ((chs n k : Nat) : Int) * ipow x k) (n + 1) := by
  intro n
  induction n with
  | zero =>
    show (1 : Int) = 0 + ((1 : Nat) : Int) * 1
    omega
  | succ n ih =>
    have hM : isum (fun k => ((chs n k : Nat) : Int) * ipow x k) (n + 1) * x
        = isum (fun k => ((chs n k : Nat) : Int) * ipow x k * x) (n + 1) :=
      isum_mul _ x (n + 1)
    have hL : isum (fun k => ((chs n k : Nat) : Int) * ipow x k * x) (n + 1)
        = isum (fun k => ((chs n k : Nat) : Int) * ipow x (k + 1)) (n + 1) :=
      isum_congr (n + 1) (fun k _ => Int.mul_assoc _ _ _)
    have hR : isum (fun k => ((chs (n + 1) k : Nat) : Int) * ipow x k) (n + 2)
        = ((chs (n + 1) 0 : Nat) : Int) * ipow x 0
          + isum (fun k => ((chs (n + 1) (k + 1) : Nat) : Int) * ipow x (k + 1)) (n + 1) :=
      isum_shift _ (n + 1)
    have hP' : isum (fun k => ((chs (n + 1) (k + 1) : Nat) : Int) * ipow x (k + 1)) (n + 1)
        = isum (fun k => ((chs n k : Nat) : Int) * ipow x (k + 1)
            + ((chs n (k + 1) : Nat) : Int) * ipow x (k + 1)) (n + 1) :=
      isum_congr (n + 1) (fun k _ => by
        show ((chs n k + chs n (k + 1) : Nat) : Int) * ipow x (k + 1)
          = ((chs n k : Nat) : Int) * ipow x (k + 1)
            + ((chs n (k + 1) : Nat) : Int) * ipow x (k + 1)
        rw [Int.natCast_add, Int.add_mul])
    have hPA : isum (fun k => ((chs n k : Nat) : Int) * ipow x (k + 1)
          + ((chs n (k + 1) : Nat) : Int) * ipow x (k + 1)) (n + 1)
        = isum (fun k => ((chs n k : Nat) : Int) * ipow x (k + 1)) (n + 1)
          + isum (fun k => ((chs n (k + 1) : Nat) : Int) * ipow x (k + 1)) (n + 1) :=
      isum_add _ _ (n + 1)
    have hS : isum (fun k => ((chs n k : Nat) : Int) * ipow x k) (n + 1)
        = ((chs n 0 : Nat) : Int) * ipow x 0
          + isum (fun k => ((chs n (k + 1) : Nat) : Int) * ipow x (k + 1)) n :=
      isum_shift _ n
    have hT : isum (fun k => ((chs n (k + 1) : Nat) : Int) * ipow x (k + 1)) (n + 1)
        = isum (fun k => ((chs n (k + 1) : Nat) : Int) * ipow x (k + 1)) n
          + ((chs n (n + 1) : Nat) : Int) * ipow x (n + 1) := rfl
    show ipow (x + 1) n * (x + 1)
      = isum (fun k => ((chs (n + 1) k : Nat) : Int) * ipow x k) (n + 2)
    rw [ih, Int.mul_add, Int.mul_one, hM, hL, hR, hP', hPA, hS, hT,
      chs_zero n, chs_zero (n + 1), chs_gt n (n + 1) (Nat.lt_succ_self n)]
    generalize isum (fun k => ((chs n k : Nat) : Int) * ipow x (k + 1)) (n + 1) = L
    generalize isum (fun k => ((chs n (k + 1) : Nat) : Int) * ipow x (k + 1)) n = M
    generalize ipow x 0 = P
    generalize ipow x (n + 1) = X
    omega

/-- **定理 (M32-7): 新入生の夢** — p ∣ (x+1)^p − x^p − 1
    （二項展開の中間項 C(p,k) x^k が全て p で消える）。 -/
theorem freshman (p : Nat) (hp : IsPrime p) (x : Int) :
    ((p : Nat) : Int) ∣ ipow (x + 1) p - ipow x p - 1 := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.1; omega⟩
  subst hm
  have hbin := binomial x (m + 2)
  have hdec : isum (fun k => ((chs (m + 2) k : Nat) : Int) * ipow x k) (m + 2 + 1)
      = ((chs (m + 2) 0 : Nat) : Int) * ipow x 0
        + isum (fun k => ((chs (m + 2) (k + 1) : Nat) : Int) * ipow x (k + 1)) (m + 1)
        + ((chs (m + 2) (m + 2) : Nat) : Int) * ipow x (m + 2) := by
    have h1 : isum (fun k => ((chs (m + 2) k : Nat) : Int) * ipow x k) (m + 2 + 1)
        = isum (fun k => ((chs (m + 2) k : Nat) : Int) * ipow x k) (m + 2)
          + ((chs (m + 2) (m + 2) : Nat) : Int) * ipow x (m + 2) := rfl
    have h2 : isum (fun k => ((chs (m + 2) k : Nat) : Int) * ipow x k) (m + 2)
        = ((chs (m + 2) 0 : Nat) : Int) * ipow x 0
          + isum (fun k => ((chs (m + 2) (k + 1) : Nat) : Int) * ipow x (k + 1)) (m + 1) :=
      isum_shift _ (m + 1)
    rw [h1, h2]
  rw [hdec, chs_zero, chs_self] at hbin
  have hmid : ((m + 2 : Nat) : Int)
      ∣ isum (fun k => ((chs (m + 2) (k + 1) : Nat) : Int) * ipow x (k + 1)) (m + 1) := by
    apply isum_dvd
    intro k hk
    obtain ⟨c, hc⟩ := prime_dvd_chs (m + 2) hp (k + 1) (by omega) (by omega)
    have hcast : ((chs (m + 2) (k + 1) : Nat) : Int)
        = ((m + 2 : Nat) : Int) * ((c : Nat) : Int) := by
      rw [hc, Int.natCast_mul]
    refine ⟨((c : Nat) : Int) * ipow x (k + 1), ?_⟩
    rw [hcast, Int.mul_assoc]
  obtain ⟨w, hw⟩ := hmid
  refine ⟨w, ?_⟩
  rw [hbin, hw]
  have h0 : ipow x 0 = (1 : Int) := rfl
  rw [h0]
  generalize ((m + 2 : Nat) : Int) * w = W
  generalize ipow x (m + 2) = X
  omega

/-- FLT の Nat 部分: 全ての m : ℕ で p ∣ m^p − m（帰納法）。 -/
theorem flt_nat (p : Nat) (hp : IsPrime p) : ∀ m : Nat,
    ((p : Nat) : Int) ∣ ipow ((m : Nat) : Int) p - ((m : Nat) : Int) := by
  intro m
  induction m with
  | zero =>
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.1; omega⟩
    refine ⟨0, ?_⟩
    rw [hq]
    show ipow (0 : Int) (q + 1) - (0 : Int) = ((q + 1 : Nat) : Int) * 0
    have h00 : ipow (0 : Int) (q + 1) = 0 := by
      show ipow (0 : Int) q * 0 = 0
      exact Int.mul_zero _
    rw [h00]
    omega
  | succ m ih =>
    have hf := freshman p hp ((m : Nat) : Int)
    have hcast : ((m + 1 : Nat) : Int) = ((m : Nat) : Int) + 1 := by omega
    rw [hcast]
    obtain ⟨u, hu⟩ := hf
    obtain ⟨v, hv⟩ := ih
    refine ⟨u + v, ?_⟩
    rw [Int.mul_add, ← hu, ← hv]
    generalize ipow (((m : Nat) : Int) + 1) p = A
    generalize ipow ((m : Nat) : Int) p = B
    omega

/-- **定理 (M32-8): Fermat の小定理** — p 素数なら全ての a : ℤ で
    p ∣ a^p − a。Teichmüller 持ち上げ ω(a) = lim a^{p^n} の整合性の基底。 -/
theorem fermat_little (p : Nat) (hp : IsPrime p) (a : Int) :
    ((p : Nat) : Int) ∣ ipow a p - a := by
  have hp0 : ((p : Nat) : Int) ≠ 0 := by have := hp.1; omega
  have hr0 : 0 ≤ a % ((p : Nat) : Int) := Int.emod_nonneg a hp0
  have hcast : (((a % ((p : Nat) : Int)).toNat : Nat) : Int) = a % ((p : Nat) : Int) :=
    Int.toNat_of_nonneg hr0
  have hsub : ((p : Nat) : Int)
      ∣ a - (((a % ((p : Nat) : Int)).toNat : Nat) : Int) := by
    rw [hcast]
    refine ⟨a / ((p : Nat) : Int), ?_⟩
    have hdm := Int.mul_ediv_add_emod a ((p : Nat) : Int)
    revert hdm
    generalize ((p : Nat) : Int) * (a / ((p : Nat) : Int)) = W
    generalize a % ((p : Nat) : Int) = R
    intro hdm
    omega
  obtain ⟨u, hu⟩ := dvd_sub_ipow hsub p
  obtain ⟨v, hv⟩ := flt_nat p hp (a % ((p : Nat) : Int)).toNat
  obtain ⟨w, hw⟩ := hsub
  refine ⟨u + v - w, ?_⟩
  rw [Int.mul_sub, Int.mul_add, ← hu, ← hv, ← hw]
  generalize ipow a p = A
  generalize ipow (((a % ((p : Nat) : Int)).toNat : Nat) : Int) p = B
  generalize (((a % ((p : Nat) : Int)).toNat : Nat) : Int) = r
  omega

end IUT
