/-
  IUT/NatPrimeParts.lean — M103 前段（自然数の素因数分解の基本補題）

  M103 が参照する素因数の存在・素冪抽出・互いに素の性質・
  付値ギャップ（gcd の商が持つ素因数の指数ギャップ）を、
  mathlib なし・Lean 4 core のみで from-scratch に証明する。

  * `prime_factor_exists` — 2 以上の自然数は素因数を持つ
    （2 以上 n 以下の範囲の燃料付き最小約数探索で構成）
  * `prime_pow_extract` — n = q^α · n'（q ∤ n'）という素冪分解が取れる
    （n の強い帰納法、q で割れる限り指数を増やす）
  * `prime_dvd_prime_pow` — ρ ∣ q^β（ρ, q 素数）なら ρ = q
    （β の帰納法、Euclid の補題を反復適用）
  * `coprime_dvd_cancel` — gcd(d,e) = 1、d ∣ ek なら d ∣ k
    （Bézout の Int 版簿記、Fermat.euclid と同型の変換）
  * `coprime_mul_dvd` — gcd(d,e) = 1、d ∣ k、e ∣ k なら de ∣ k
  * `coprime_of_not_dvd_prime_pow` — q ∤ n' なら gcd(n', q^β) = 1
  * `dvd_or_valuation_gap` — s ∤ m（s, m ≥ 1）なら、ある素数 q の指数が
    s 側で m 側より真に大きいという「付値ギャップ」が存在する

  全て選択公理不使用。
-/
import IUT.Fermat

namespace IUT

/-! ## 素因数の存在 -/

/-- 燃料付き最小約数探索: `k` から `n` まで走査し、最初に見つかる
    `n` の約数（2 以上）を返す。見つからなければ `n` 自身を返す
    （`n ∣ n` なので常に停止する）。 -/
def leastDivisorFrom (n : Nat) : Nat → Nat → Nat
  | 0, _ => n
  | _fuel + 1, k =>
    if h : k ∣ n then k else leastDivisorFrom n _fuel (k + 1)

/-- `leastDivisorFrom` は常に `n` の約数を返す（fuel と探索範囲に関する
    帰納法）。 -/
theorem leastDivisorFrom_dvd (n : Nat) (hn : 2 ≤ n) :
    ∀ fuel k, k + fuel = n + 1 → leastDivisorFrom n fuel k ∣ n := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk
    have : k = n + 1 := by omega
    show n ∣ n
    exact Nat.dvd_refl n
  | succ fuel ih =>
    intro k hk
    show (if h : k ∣ n then k else leastDivisorFrom n fuel (k + 1)) ∣ n
    cases Nat.decidable_dvd k n with
    | isTrue h => rw [dif_pos h]; exact h
    | isFalse h =>
      rw [dif_neg h]
      exact ih (k + 1) (by omega)

/-- `leastDivisorFrom` が返す値は探索開始点 `k` 以上である
    （範囲外なら `n` を返すが `k ≤ n + 1 ≤ ...` の形で管理）。
    ここでは `2 ≤ k` の場合に `2 ≤ leastDivisorFrom n fuel k` を示す。 -/
theorem leastDivisorFrom_ge (n : Nat) (hn : 2 ≤ n) :
    ∀ fuel k, 2 ≤ k → 2 ≤ leastDivisorFrom n fuel k := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk
    show 2 ≤ n
    omega
  | succ fuel ih =>
    intro k hk
    show 2 ≤ (if h : k ∣ n then k else leastDivisorFrom n fuel (k + 1))
    cases Nat.decidable_dvd k n with
    | isTrue h => rw [dif_pos h]; exact hk
    | isFalse h => rw [dif_neg h]; exact ih (k + 1) (by omega)

/-- **最小性**: 探索開始点 `k`（2 ≤ k）から `leastDivisorFrom n fuel k`
    未満の範囲には `n` の約数が存在しない。 -/
theorem leastDivisorFrom_min (n : Nat) (hn : 2 ≤ n) :
    ∀ fuel k, k + fuel = n + 1 → 2 ≤ k →
      ∀ e, k ≤ e → e < leastDivisorFrom n fuel k → ¬ e ∣ n := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk hk2 e he1 he2
    exfalso
    show False
    have hd : leastDivisorFrom n 0 k = n := rfl
    omega
  | succ fuel ih =>
    intro k hk hk2 e he1 he2
    cases Nat.decidable_dvd k n with
    | isTrue h =>
      have hd : leastDivisorFrom n (fuel + 1) k = k := by
        show (if h : k ∣ n then k else leastDivisorFrom n fuel (k + 1)) = k
        rw [dif_pos h]
      rw [hd] at he2
      omega
    | isFalse h =>
      have hd : leastDivisorFrom n (fuel + 1) k = leastDivisorFrom n fuel (k + 1) := by
        show (if h : k ∣ n then k else leastDivisorFrom n fuel (k + 1))
          = leastDivisorFrom n fuel (k + 1)
        rw [dif_neg h]
      rw [hd] at he2
      cases Nat.decEq e k with
      | isTrue hek => subst hek; exact h
      | isFalse hek => exact ih (k + 1) (by omega) (by omega) e (by omega) he2

/-- **定理: 素因数の存在** — 2 以上の自然数は素因数を持つ。
    `leastDivisorFrom n n 2` が求める素因数（2 以上 n 以下の最小約数）。 -/
theorem prime_factor_exists : ∀ n, 2 ≤ n → ∃ q, IsPrime q ∧ q ∣ n := by
  intro n hn
  let d := leastDivisorFrom n (n - 1) 2
  have hdvd : d ∣ n := leastDivisorFrom_dvd n hn (n - 1) 2 (by omega)
  have hge : 2 ≤ d := leastDivisorFrom_ge n hn (n - 1) 2 (by omega)
  have hmin : ∀ e, 2 ≤ e → e < d → ¬ e ∣ n :=
    fun e he1 he2 => leastDivisorFrom_min n hn (n - 1) 2 (by omega) (by omega) e he1 he2
  refine ⟨d, ⟨hge, ?_⟩, hdvd⟩
  intro k hk
  -- k ∣ d ∣ n。k = 0 なら d = 0 で hge に矛盾。k ≥ 2 かつ k < d なら
  -- k ∣ n（k ∣ d ∣ n から）で最小性に矛盾。よって k = 1 または k = d。
  have hkd : k ∣ n := Nat.dvd_trans hk hdvd
  have hk0 : k ≠ 0 := by
    intro h0
    subst h0
    have := Nat.eq_zero_of_zero_dvd hk
    omega
  cases Nat.lt_or_ge k 2 with
  | inl h => left; omega
  | inr h2 =>
    right
    cases Nat.lt_or_ge k d with
    | inl hlt => exact absurd hkd (hmin k h2 hlt)
    | inr hge2 =>
      have hkd2 : k ≤ d := Nat.le_of_dvd (by omega) hk
      omega

/-! ## 素冪抽出 -/

/-- **定理: 素冪抽出** — 素数 `q` に対し、1 以上の任意の `n` は
    `n = q^α * n'`（`q ∤ n'`）の形に書ける。 -/
theorem prime_pow_extract (q : Nat) (hq : IsPrime q) :
    ∀ n, 1 ≤ n → ∃ α n', n = q ^ α * n' ∧ ¬ q ∣ n' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    cases Nat.decidable_dvd q n with
    | isFalse hnd =>
      refine ⟨0, n, ?_, hnd⟩
      show n = 1 * n
      rw [Nat.one_mul]
    | isTrue hd =>
      obtain ⟨n1, hn1⟩ := hd
      have hq2 : 2 ≤ q := hq.1
      have hn1pos : 1 ≤ n1 := by
        cases Nat.eq_zero_or_pos n1 with
        | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hn1; omega
        | inr hpos => exact hpos
      have hlt : n1 < n := by
        rw [hn1]
        have hmm : 1 * n1 < q * n1 := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        calc n1 = 1 * n1 := (Nat.one_mul n1).symm
          _ < q * n1 := hmm
      obtain ⟨α, n', hα, hqn'⟩ := ih n1 hlt hn1pos
      refine ⟨α + 1, n', ?_, hqn'⟩
      rw [hn1, hα, Nat.pow_succ]
      rw [Nat.mul_comm (q ^ α) q, Nat.mul_assoc]

/-! ## 素数が素冪を割るなら等しい -/

/-- **定理**: `ρ` が素数で `ρ ∣ q^β`（`q` も素数）なら `ρ = q`。 -/
theorem prime_dvd_prime_pow (ρ q : Nat) (hρ : IsPrime ρ) (hq : IsPrime q) :
    ∀ β, ρ ∣ q ^ β → ρ = q := by
  intro β
  induction β with
  | zero =>
    intro h
    exfalso
    have : ρ ∣ 1 := by
      have : q ^ 0 = 1 := rfl
      rwa [this] at h
    have hle : ρ ≤ 1 := Nat.le_of_dvd (by omega) this
    have := hρ.1
    omega
  | succ β ih =>
    intro h
    have hstep : q ^ (β + 1) = q ^ β * q := Nat.pow_succ q β
    rw [hstep] at h
    cases euclid ρ hρ h with
    | inl h1 => exact ih h1
    | inr h1 =>
      cases hq.2 ρ h1 with
      | inl h2 => exfalso; have := hρ.1; omega
      | inr h2 => exact h2

/-! ## 互いに素と割り算 -/

/-- **定理**: `gcd(d,e) = 1`、`d ∣ ek` なら `d ∣ k`（Bézout の Int 版簿記）。 -/
theorem coprime_dvd_cancel {d e k : Nat} (h : Nat.gcd d e = 1) (hdvd : d ∣ e * k) :
    d ∣ k := by
  obtain ⟨x, y, hxy⟩ := bezout d e
  rw [h] at hxy
  have h1 : (1 : Int) = ((d : Nat) : Int) * x + ((e : Nat) : Int) * y := hxy
  obtain ⟨c, hc⟩ := hdvd
  have h2 : ((e : Nat) : Int) * ((k : Nat) : Int) = ((d : Nat) : Int) * ((c : Nat) : Int) := by
    rw [← Int.natCast_mul, ← Int.natCast_mul, hc]
  -- k = 1 * k = (d x + e y) k = d x k + e y k = d x k + d c y = d (x k + c y)
  have h3 : ((k : Nat) : Int) = ((d : Nat) : Int) * (x * ((k : Nat) : Int) + ((c : Nat) : Int) * y) :=
    euclid_combine h1 h2
  exact Int.ofNat_dvd.mp ⟨x * ((k : Nat) : Int) + ((c : Nat) : Int) * y, h3⟩

/-- **定理**: `gcd(d,e) = 1`、`d ∣ k`、`e ∣ k` なら `d * e ∣ k`。 -/
theorem coprime_mul_dvd {d e k : Nat} (h : Nat.gcd d e = 1) (hd : d ∣ k) (he : e ∣ k) :
    d * e ∣ k := by
  obtain ⟨t, ht⟩ := hd
  have he2 : e ∣ d * t := by rw [← ht]; exact he
  have hcomm : Nat.gcd e d = 1 := by rw [Nat.gcd_comm]; exact h
  have het : e ∣ t := coprime_dvd_cancel hcomm he2
  obtain ⟨u, hu⟩ := het
  refine ⟨u, ?_⟩
  rw [ht, hu, Nat.mul_assoc]

/-! ## 素冪と互いに素 -/

/-- **定理**: `q ∤ n'`（`q` 素数）なら `n'` は `q^β` と互いに素。 -/
theorem coprime_of_not_dvd_prime_pow {q n' : Nat} (hq : IsPrime q) (hn : ¬ q ∣ n')
    (β : Nat) : Nat.gcd n' (q ^ β) = 1 := by
  have hn'pos : n' ≠ 0 := by
    intro h0
    apply hn
    rw [h0]
    exact Nat.dvd_zero q
  have hgpos : Nat.gcd n' (q ^ β) ≠ 0 := by
    intro h0
    exact hn'pos (Nat.eq_zero_of_gcd_eq_zero_left h0)
  cases Nat.lt_or_ge (Nat.gcd n' (q ^ β)) 2 with
  | inl hlt => omega
  | inr hge =>
    exfalso
    obtain ⟨ρ, hρ, hρg⟩ := prime_factor_exists (Nat.gcd n' (q ^ β)) hge
    have hρn' : ρ ∣ n' := Nat.dvd_trans hρg (Nat.gcd_dvd_left n' (q ^ β))
    have hρq : ρ ∣ q ^ β := Nat.dvd_trans hρg (Nat.gcd_dvd_right n' (q ^ β))
    have hρeq : ρ = q := prime_dvd_prime_pow ρ q hρ hq β hρq
    rw [hρeq] at hρn'
    exact hn hρn'

/-! ## 付値ギャップ -/

/-- **定理: 付値ギャップ** — `s ∤ m`（`s, m ≥ 1`）なら、ある素数 `q` が
    存在し、`s` 側の `q`-指数 `β` が `m` 側の `q`-指数 `α` より真に大きい。 -/
theorem dvd_or_valuation_gap {s m : Nat} (hs : 1 ≤ s) (hm : 1 ≤ m) (hnd : ¬ s ∣ m) :
    ∃ q α β s' m', IsPrime q ∧ s = q ^ β * s' ∧ ¬ q ∣ s' ∧
      m = q ^ α * m' ∧ ¬ q ∣ m' ∧ α < β := by
  let g := Nat.gcd s m
  have hgpos : g ≠ 0 := by
    intro h0
    exact (by omega : s ≠ 0) (Nat.eq_zero_of_gcd_eq_zero_left h0)
  have hgdvd_s : g ∣ s := Nat.gcd_dvd_left s m
  have hgdvd_m : g ∣ m := Nat.gcd_dvd_right s m
  let d := s / g
  have hd_def : d = s / g := rfl
  have hsdg : s = g * d := by
    rw [hd_def, Nat.mul_comm]
    exact (Nat.div_mul_cancel hgdvd_s).symm
  have hd2 : 2 ≤ d := by
    cases Nat.eq_zero_or_pos d with
    | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hsdg; omega
    | inr hpos =>
      cases Nat.lt_or_ge d 2 with
      | inr h => exact h
      | inl h =>
        exfalso
        have hd1 : d = 1 := by omega
        rw [hd1, Nat.mul_one] at hsdg
        apply hnd
        rw [hsdg]
        exact hgdvd_m
  obtain ⟨q, hq, hqd⟩ := prime_factor_exists d hd2
  have hqs : q ∣ s := by
    rw [hsdg]
    exact Nat.dvd_trans hqd (Nat.dvd_mul_left d g)
  obtain ⟨β, s', hβ, hqs'⟩ := prime_pow_extract q hq s hs
  obtain ⟨α, m', hα, hqm'⟩ := prime_pow_extract q hq m hm
  refine ⟨q, α, β, s', m', hq, hβ, hqs', hα, hqm', ?_⟩
  cases Nat.lt_or_ge α β with
  | inl h => exact h
  | inr hge =>
    exfalso
    have hqβα : q ^ β ∣ q ^ α := Nat.pow_dvd_pow q hge
    have hqβm : q ^ β ∣ m := by
      rw [hα]
      exact Nat.dvd_trans hqβα (Nat.dvd_mul_right (q ^ α) m')
    have hqβs : q ^ β ∣ s := by rw [hβ]; exact Nat.dvd_mul_right (q ^ β) s'
    have hqβg : q ^ β ∣ g := Nat.dvd_gcd hqβs hqβm
    obtain ⟨t, ht⟩ := hqβg
    have hq2 : 2 ≤ q := hq.1
    have hqβpos : 0 < q ^ β := Nat.pow_pos (by omega)
    -- g = q^β * t, s = g * d = q^β * t * d = q^β * s'
    have hsc : q ^ β * (t * d) = q ^ β * s' := by
      rw [← Nat.mul_assoc, ← ht, ← hsdg, hβ]
    have htd_eq : t * d = s' := Nat.eq_of_mul_eq_mul_left hqβpos hsc
    -- t ∣ s' since s' = t * d
    have htdvd : t ∣ s' := ⟨d, htd_eq.symm⟩
    -- d = s / g = (q^β s') / (q^β t) = s' / t
    have hdeq : d = s' / t := by
      have h1 : s / g = s' / t := by
        rw [hβ, ht]
        exact Nat.mul_div_mul_left s' t hqβpos
      exact hd_def.trans h1
    have htpos : t ≠ 0 := by
      intro h0
      rw [h0, Nat.mul_zero] at ht
      exact hgpos ht
    have hqd2 : q ∣ d := hqd
    rw [hdeq] at hqd2
    obtain ⟨w, hw⟩ := hqd2
    have hs'eq : s' = t * (s' / t) := (Nat.div_mul_cancel htdvd).symm.trans (Nat.mul_comm _ _)
    rw [hw] at hs'eq
    apply hqs'
    refine ⟨t * w, ?_⟩
    rw [hs'eq]
    rw [Nat.mul_comm t (q * w), Nat.mul_assoc, Nat.mul_comm w t]

end IUT
