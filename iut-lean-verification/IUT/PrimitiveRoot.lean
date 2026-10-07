/-
  IUT/PrimitiveRoot.lean — M103（B-3 後半完結: 原始根の存在 = (ℤ/p)^× の巡回性）

  M102 の位数理論と M102F の Nat 素数道具、M96 の roots_bound を合流させ、
  **(ℤ/p)^× に位数 p−1 の元（原始根）が存在する**ことを完全証明する。
  経路は「指数（exponent）論法」:

    (1) 互いに素な位数の積の位数 = 積（Bezout 系の簡約）
    (2) 位数結合: 任意の 2 単数 a, b に対し ord a と ord b を共に割り切る
        位数を持つ単数 c が存在（s ∤ r なら付値ギャップの素数 q で
        q 冪部分を移植して位数を**厳密に増大**させる — 位数 ≤ p−1 が
        燃料になり再帰が停止する）
    (3) 全単数の位数を割る「指数元」g を 1..p−1 の畳み込みで構成
    (4) ord g < p−1 なら 1..(ord g)+1 の相異なる剰余が X^{ord g} − 1 の
        ord g + 1 個の根になり roots_bound（M96）に矛盾 → ord g = p−1

  * M103-1 `zmodPow_mul_dist` / `zmodPow_succ` / `zmodMul_one` — 冪の
    乗法分配・冪の剥がし・右単位元（レベル環の補完）
  * M103-2 `zmod_no_zero_div` — **ℤ/p は零因子なし**（Euclid の補題、
    roots_bound への入口）と `zmodRing_one_ne_zero`
  * M103-3 `zmodPow_eq_rpow` — zmodPow = 環冪 rpow の橋（M96 接続）
  * M103-4 `zmodOrd_mul_coprime` — **(1) 互いに素な位数の積**
  * M103-5 `zmodOrd_combine` — **(2) 位数結合**（燃料 = p−1 − ord a）
  * M103-6 `exponent_fold` / `exponent_element` — **(3) 指数元**
    （剰余正規化 c = mk (a % p) で任意の単数を 1..p−1 に帰着）
  * M103-7 `primitive_root_exists` — **(4) 原始根の存在**（本丸）:
    ∃ g, IsZmodUnit p g ∧ zmodOrd p g = p − 1

  未形式化（正直申告）: 「全ての単数が g の冪」（被覆）は、g の p−1 個の
  冪の相異性（M102-8）+ roots_bound の同型の論法 + 有界探索で従うが
  次層に残す。μ_{p−1} への移送（M101 の同型経由）も同様。
  全て選択公理不使用。
-/
import IUT.ZmodOrder
import IUT.NatPrimeParts
import IUT.FactorTheorem

namespace IUT

/-! ## レベル環の補完 -/

/-- **M103-1a: 冪の乗法分配** (cd)^k = c^k·d^k。 -/
theorem zmodPow_mul_dist (n : Nat) (c d : (zmod n).carrier) (k : Nat) :
    zmodPow n (zmodMul n c d) k
      = zmodMul n (zmodPow n c k) (zmodPow n d k) := by
  induction c using Quot.ind; rename_i a
  induction d using Quot.ind; rename_i b
  show Quot.mk (modCong n).rel (ipow (a * b) k)
    = Quot.mk (modCong n).rel (ipow a k * ipow b k)
  rw [mul_ipow]

/-- **M103-1b: 冪の剥がし** c^{k+1} = c^k·c。 -/
theorem zmodPow_succ (n : Nat) (c : (zmod n).carrier) (k : Nat) :
    zmodPow n c (k + 1) = zmodMul n (zmodPow n c k) c := by
  induction c using Quot.ind; rename_i a
  rfl

/-- **M103-1c**: 1 は右単位元。 -/
theorem zmodMul_one (n : Nat) (x : (zmod n).carrier) :
    zmodMul n x (Quot.mk (modCong n).rel 1) = x := by
  rw [zmodMul_comm]
  exact zmodOne_mul n x

/-! ## ℤ/p は零因子なし -/

/-- **定理 (M103-2a): ℤ/p は零因子なし**（Euclid の補題の商への降下。
    roots_bound への入口）。 -/
theorem zmod_no_zero_div (p : Nat) (hp : IsPrime p) :
    NoZeroDiv (zmodRing (p ^ 1)) := by
  intro x y hxy
  revert hxy
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  intro hxy
  have h1 : Quot.mk (modCong (p ^ 1)).rel (a * b)
      = Quot.mk (modCong (p ^ 1)).rel 0 := hxy
  have h2 := quot_exact intGrp (modCong (p ^ 1)) h1
  have h3 : ((p ^ 1 : Nat) : Int) ∣ a * b - 0 := h2
  rw [Nat.pow_one, Int.sub_zero] at h3
  have h5 : p ∣ (a * b).natAbs := by
    have h4 := Int.natAbs_dvd_natAbs.mpr h3
    rw [Int.natAbs_natCast] at h4
    exact h4
  rw [Int.natAbs_mul] at h5
  cases euclid p hp h5 with
  | inl h6 =>
    left
    apply Quot.sound
    show ((p ^ 1 : Nat) : Int) ∣ a - 0
    rw [Nat.pow_one, Int.sub_zero]
    apply Int.natAbs_dvd_natAbs.mp
    rw [Int.natAbs_natCast]
    exact h6
  | inr h6 =>
    right
    apply Quot.sound
    show ((p ^ 1 : Nat) : Int) ∣ b - 0
    rw [Nat.pow_one, Int.sub_zero]
    apply Int.natAbs_dvd_natAbs.mp
    rw [Int.natAbs_natCast]
    exact h6

/-- **M103-2b**: ℤ/p で 1 ≠ 0。 -/
theorem zmodRing_one_ne_zero (p : Nat) (hp : IsPrime p) :
    (zmodRing (p ^ 1)).one ≠ (zmodRing (p ^ 1)).zero := by
  intro h
  have h1 : Quot.mk (modCong (p ^ 1)).rel (1 : Int)
      = Quot.mk (modCong (p ^ 1)).rel 0 := h
  have h2 := quot_exact intGrp (modCong (p ^ 1)) h1
  have h3 : ((p ^ 1 : Nat) : Int) ∣ (1 : Int) - 0 := h2
  rw [Nat.pow_one, Int.sub_zero] at h3
  exact not_dvd_one p hp.1 h3

/-! ## zmodPow = 環冪 rpow の橋 -/

/-- **M103-3: zmodPow と rpow の一致**（M96 の多項式評価への橋）。 -/
theorem zmodPow_eq_rpow (n : Nat) (c : (zmod n).carrier) : ∀ k,
    zmodPow n c k = rpow (zmodRing n) c k := by
  intro k
  induction k with
  | zero =>
    induction c using Quot.ind; rename_i a
    rfl
  | succ k ih =>
    rw [zmodPow_succ n c k, ih]
    rfl

/-- 補助: 指数の狭義単調性 q^α < q^β（α < β、2 ≤ q）。core の
    Nat.pow_lt_pow_right は Classical.choice に依存するため自前で
    choice-free に証明する。 -/
theorem pow_lt_pow_exp {q : Nat} (hq : 2 ≤ q) {α β : Nat} (h : α < β) :
    q ^ α < q ^ β := by
  have he : β = α + (β - α) := by omega
  have h1 : q ^ β = q ^ (α + (β - α)) := congrArg (q ^ ·) he
  have hpow : q ^ β = q ^ α * q ^ (β - α) := by
    rw [h1, Nat.pow_add]
  have hge : 2 ≤ q ^ (β - α) := by
    have h2 : q ^ 1 ≤ q ^ (β - α) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.pow_one] at h2
    omega
  have hmul : q ^ α * 2 ≤ q ^ α * q ^ (β - α) := Nat.mul_le_mul_left _ hge
  have hpos : 1 ≤ q ^ α := Nat.pow_pos (by omega)
  omega

/-! ## 互いに素な位数の積 -/

/-- **定理 (M103-4): 互いに素な位数の積の位数 = 積** —
    gcd(ord u, ord v) = 1 なら ord(uv) = ord u · ord v
    （両向き整除: (uv)^{m₁m₂} = 1 と、(uv)^e = 1 から Bezout 消去で
    m₁ ∣ e・m₂ ∣ e）。 -/
theorem zmodOrd_mul_coprime (p : Nat) (hp : IsPrime p)
    {u v : (zmod (p ^ 1)).carrier} (hu : IsZmodUnit p u) (hv : IsZmodUnit p v)
    (hco : Nat.gcd (zmodOrd p u) (zmodOrd p v) = 1) :
    zmodOrd p (zmodMul (p ^ 1) u v) = zmodOrd p u * zmodOrd p v := by
  have huv : IsZmodUnit p (zmodMul (p ^ 1) u v) := isZmodUnit_mul p hp hu hv
  -- (uv)^{m₁m₂} = 1
  have hA : zmodPow (p ^ 1) (zmodMul (p ^ 1) u v) (zmodOrd p u * zmodOrd p v)
      = Quot.mk (modCong (p ^ 1)).rel 1 := by
    rw [zmodPow_mul_dist]
    have h1 : zmodPow (p ^ 1) u (zmodOrd p u * zmodOrd p v)
        = Quot.mk (modCong (p ^ 1)).rel 1 := by
      rw [zmodPow_mul, zmodOrd_pow_eq_one p hp hu, zmodPow_one_base]
    have h2 : zmodPow (p ^ 1) v (zmodOrd p u * zmodOrd p v)
        = Quot.mk (modCong (p ^ 1)).rel 1 := by
      have he : zmodPow (p ^ 1) v (zmodOrd p u * zmodOrd p v)
          = zmodPow (p ^ 1) v (zmodOrd p v * zmodOrd p u) :=
        congrArg (zmodPow (p ^ 1) v) (Nat.mul_comm _ _)
      rw [he, zmodPow_mul, zmodOrd_pow_eq_one p hp hv, zmodPow_one_base]
    rw [h1, h2, zmodOne_mul]
  have hdvdA : zmodOrd p (zmodMul (p ^ 1) u v) ∣ zmodOrd p u * zmodOrd p v :=
    zmodOrd_dvd p hp huv hA
  -- u^{e·m₂} = 1（v 側が消える）
  have hB : zmodPow (p ^ 1) u (zmodOrd p (zmodMul (p ^ 1) u v) * zmodOrd p v)
      = Quot.mk (modCong (p ^ 1)).rel 1 := by
    have h1 : zmodPow (p ^ 1) (zmodMul (p ^ 1) u v)
        (zmodOrd p (zmodMul (p ^ 1) u v) * zmodOrd p v)
        = Quot.mk (modCong (p ^ 1)).rel 1 := by
      rw [zmodPow_mul, zmodOrd_pow_eq_one p hp huv, zmodPow_one_base]
    rw [zmodPow_mul_dist] at h1
    have h2 : zmodPow (p ^ 1) v
        (zmodOrd p (zmodMul (p ^ 1) u v) * zmodOrd p v)
        = Quot.mk (modCong (p ^ 1)).rel 1 := by
      have he : zmodPow (p ^ 1) v
          (zmodOrd p (zmodMul (p ^ 1) u v) * zmodOrd p v)
          = zmodPow (p ^ 1) v
            (zmodOrd p v * zmodOrd p (zmodMul (p ^ 1) u v)) :=
        congrArg (zmodPow (p ^ 1) v) (Nat.mul_comm _ _)
      rw [he, zmodPow_mul, zmodOrd_pow_eq_one p hp hv, zmodPow_one_base]
    rw [h2, zmodMul_one] at h1
    exact h1
  have hm1 : zmodOrd p u ∣ zmodOrd p (zmodMul (p ^ 1) u v) := by
    have hd := zmodOrd_dvd p hp hu hB
    have hd' : zmodOrd p u ∣ zmodOrd p v * zmodOrd p (zmodMul (p ^ 1) u v) := by
      have he : zmodOrd p (zmodMul (p ^ 1) u v) * zmodOrd p v
          = zmodOrd p v * zmodOrd p (zmodMul (p ^ 1) u v) := Nat.mul_comm _ _
      rw [← he]
      exact hd
    exact coprime_dvd_cancel hco hd'
  -- v^{e·m₁} = 1（u 側が消える）
  have hC : zmodPow (p ^ 1) v (zmodOrd p (zmodMul (p ^ 1) u v) * zmodOrd p u)
      = Quot.mk (modCong (p ^ 1)).rel 1 := by
    have h1 : zmodPow (p ^ 1) (zmodMul (p ^ 1) u v)
        (zmodOrd p (zmodMul (p ^ 1) u v) * zmodOrd p u)
        = Quot.mk (modCong (p ^ 1)).rel 1 := by
      rw [zmodPow_mul, zmodOrd_pow_eq_one p hp huv, zmodPow_one_base]
    rw [zmodPow_mul_dist] at h1
    have h2 : zmodPow (p ^ 1) u
        (zmodOrd p (zmodMul (p ^ 1) u v) * zmodOrd p u)
        = Quot.mk (modCong (p ^ 1)).rel 1 := by
      have he : zmodPow (p ^ 1) u
          (zmodOrd p (zmodMul (p ^ 1) u v) * zmodOrd p u)
          = zmodPow (p ^ 1) u
            (zmodOrd p u * zmodOrd p (zmodMul (p ^ 1) u v)) :=
        congrArg (zmodPow (p ^ 1) u) (Nat.mul_comm _ _)
      rw [he, zmodPow_mul, zmodOrd_pow_eq_one p hp hu, zmodPow_one_base]
    rw [h2, zmodOne_mul] at h1
    exact h1
  have hm2 : zmodOrd p v ∣ zmodOrd p (zmodMul (p ^ 1) u v) := by
    have hd := zmodOrd_dvd p hp hv hC
    have hd' : zmodOrd p v ∣ zmodOrd p u * zmodOrd p (zmodMul (p ^ 1) u v) := by
      have he : zmodOrd p (zmodMul (p ^ 1) u v) * zmodOrd p u
          = zmodOrd p u * zmodOrd p (zmodMul (p ^ 1) u v) := Nat.mul_comm _ _
      rw [← he]
      exact hd
    have hco' : Nat.gcd (zmodOrd p v) (zmodOrd p u) = 1 := by
      rw [Nat.gcd_comm]
      exact hco
    exact coprime_dvd_cancel hco' hd'
  exact Nat.dvd_antisymm hdvdA (coprime_mul_dvd hco hm1 hm2)

/-! ## 位数結合 -/

/-- **定理 (M103-5): 位数結合** — 任意の 2 単数 a, b に対し、ord a と
    ord b を共に割り切る位数の単数 c が存在する。s := ord b ∤ r := ord a
    のときは付値ギャップ（M102F）の素数 q について a の q 冪部分を捨て
    b の q 冪部分を移植した積で位数が **q^{β−α} 倍に厳密増大**し、
    位数 ≤ p−1（M102-5）ゆえ燃料 fuel = p−1−ord a で再帰が停止する。 -/
theorem zmodOrd_combine (p : Nat) (hp : IsPrime p) : ∀ (fuel : Nat)
    (a b : (zmod (p ^ 1)).carrier), IsZmodUnit p a → IsZmodUnit p b →
    p - 1 ≤ zmodOrd p a + fuel →
    ∃ c, IsZmodUnit p c ∧ zmodOrd p a ∣ zmodOrd p c
      ∧ zmodOrd p b ∣ zmodOrd p c := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b ha hb hbound
    have h1 : zmodOrd p a = p - 1 :=
      Nat.le_antisymm (zmodOrd_le p hp ha) (by omega)
    refine ⟨a, ha, Nat.dvd_refl _, ?_⟩
    rw [h1]
    exact zmodOrd_dvd_card p hp hb
  | succ fuel ih =>
    intro a b ha hb hbound
    cases Nat.eq_zero_or_pos (zmodOrd p a % zmodOrd p b) with
    | inl hz =>
      exact ⟨a, ha, Nat.dvd_refl _, Nat.dvd_of_mod_eq_zero hz⟩
    | inr hposmod =>
      have hnd : ¬ zmodOrd p b ∣ zmodOrd p a := by
        intro hd
        obtain ⟨t, ht⟩ := hd
        rw [ht, Nat.mul_mod_right] at hposmod
        omega
      obtain ⟨q, α, β, s', r', hq, hs, hqs', hr, hqr', hαβ⟩ :=
        dvd_or_valuation_gap (zmodOrd_pos p hp hb) (zmodOrd_pos p hp ha) hnd
      have hqpos : 1 ≤ q ^ α := Nat.pow_pos (by have := hq.1; omega)
      have hr'pos : 1 ≤ r' := by
        cases Nat.eq_zero_or_pos r' with
        | inl h0 =>
          exfalso
          have hord := zmodOrd_pos p hp ha
          rw [h0, Nat.mul_zero] at hr
          omega
        | inr h1 => exact h1
      have hs'pos : 1 ≤ s' := by
        cases Nat.eq_zero_or_pos s' with
        | inl h0 =>
          exfalso
          have hord := zmodOrd_pos p hp hb
          rw [h0, Nat.mul_zero] at hs
          omega
        | inr h1 => exact h1
      -- u₁ := a^{q^α}, ord = r'
      have hdvd_qa : q ^ α ∣ zmodOrd p a := ⟨r', hr⟩
      have hu1 : IsZmodUnit p (zmodPow (p ^ 1) a (q ^ α)) :=
        isZmodUnit_pow p hp ha (q ^ α)
      have hord_u1 : zmodOrd p (zmodPow (p ^ 1) a (q ^ α)) = r' := by
        rw [zmodOrd_pow_div p hp ha hqpos hdvd_qa, hr,
          Nat.mul_div_cancel_left r' (by omega : 0 < q ^ α)]
      -- v₁ := b^{s'}, ord = q^β
      have hdvd_sb : s' ∣ zmodOrd p b := ⟨q ^ β, by rw [hs, Nat.mul_comm]⟩
      have hv1 : IsZmodUnit p (zmodPow (p ^ 1) b s') :=
        isZmodUnit_pow p hp hb s'
      have hord_v1 : zmodOrd p (zmodPow (p ^ 1) b s') = q ^ β := by
        rw [zmodOrd_pow_div p hp hb hs'pos hdvd_sb, hs, Nat.mul_comm,
          Nat.mul_div_cancel_left (q ^ β) (by omega : 0 < s')]
      -- c₁ := u₁·v₁, ord = r'·q^β
      have hco : Nat.gcd (zmodOrd p (zmodPow (p ^ 1) a (q ^ α)))
          (zmodOrd p (zmodPow (p ^ 1) b s')) = 1 := by
        rw [hord_u1, hord_v1]
        exact coprime_of_not_dvd_prime_pow hq hqr' β
      have hc1 : IsZmodUnit p (zmodMul (p ^ 1) (zmodPow (p ^ 1) a (q ^ α))
          (zmodPow (p ^ 1) b s')) := isZmodUnit_mul p hp hu1 hv1
      have hord_c1 : zmodOrd p (zmodMul (p ^ 1) (zmodPow (p ^ 1) a (q ^ α))
          (zmodPow (p ^ 1) b s')) = r' * q ^ β := by
        rw [zmodOrd_mul_coprime p hp hu1 hv1 hco, hord_u1, hord_v1]
      -- ord a ∣ r'·q^β かつ ord a < r'·q^β
      have hdvd_a_c1 : zmodOrd p a ∣ r' * q ^ β := by
        rw [hr]
        have h1 : q ^ α ∣ q ^ β := Nat.pow_dvd_pow q (Nat.le_of_lt hαβ)
        obtain ⟨w, hw⟩ := h1
        refine ⟨w, ?_⟩
        rw [hw]
        have := Nat.mul_comm r' (q ^ α * w)
        calc r' * (q ^ α * w) = q ^ α * w * r' := Nat.mul_comm _ _
          _ = q ^ α * (w * r') := Nat.mul_assoc _ _ _
          _ = q ^ α * (r' * w) := by rw [Nat.mul_comm w r']
          _ = q ^ α * r' * w := (Nat.mul_assoc _ _ _).symm
      have hlt : zmodOrd p a < r' * q ^ β := by
        rw [hr]
        have hqlt : q ^ α < q ^ β := pow_lt_pow_exp hq.1 hαβ
        have hstep : r' * (q ^ α + 1) ≤ r' * q ^ β :=
          Nat.mul_le_mul_left r' (by omega)
        have hexpand : r' * (q ^ α + 1) = r' * q ^ α + r' := by
          rw [Nat.mul_add, Nat.mul_one]
        have hcomm : q ^ α * r' = r' * q ^ α := Nat.mul_comm _ _
        omega
      -- 再帰
      obtain ⟨c, hc, hd1, hd2⟩ := ih
        (zmodMul (p ^ 1) (zmodPow (p ^ 1) a (q ^ α)) (zmodPow (p ^ 1) b s')) b
        hc1 hb (by rw [hord_c1]; omega)
      refine ⟨c, hc, ?_, hd2⟩
      rw [hord_c1] at hd1
      exact Nat.dvd_trans hdvd_a_c1 hd1

/-! ## 指数元の構成 -/

/-- **M103-6a: 指数元の畳み込み** — 1..j の剰余の位数を全て割り切る
    位数の単数の存在（j の帰納 + 位数結合）。 -/
theorem exponent_fold (p : Nat) (hp : IsPrime p) : ∀ j, 1 ≤ j → j ≤ p - 1 →
    ∃ g, IsZmodUnit p g ∧ ∀ i, 1 ≤ i → i ≤ j →
      zmodOrd p (Quot.mk (modCong (p ^ 1)).rel ((i : Nat) : Int))
        ∣ zmodOrd p g := by
  intro j
  induction j with
  | zero =>
    intro h hh
    exact absurd h (by omega)
  | succ j ih =>
    intro h1 hj
    have hju : IsZmodUnit p
        (Quot.mk (modCong (p ^ 1)).rel ((j + 1 : Nat) : Int)) := by
      refine ⟨((j + 1 : Nat) : Int), rfl, ?_⟩
      intro hdvd
      have h2 : p ∣ j + 1 := Int.ofNat_dvd.mp hdvd
      have h3 := Nat.le_of_dvd (by omega) h2
      have := hp.1
      omega
    cases Nat.eq_zero_or_pos j with
    | inl hz =>
      refine ⟨Quot.mk (modCong (p ^ 1)).rel ((j + 1 : Nat) : Int), hju, ?_⟩
      intro i hi1 hi2
      have hi : i = j + 1 := by omega
      rw [hi]
      exact Nat.dvd_refl _
    | inr hpos =>
      obtain ⟨g, hg, hall⟩ := ih hpos (by omega)
      obtain ⟨c, hc, hdc1, hdc2⟩ := zmodOrd_combine p hp (p - 1) g
        (Quot.mk (modCong (p ^ 1)).rel ((j + 1 : Nat) : Int)) hg hju
        (by have := zmodOrd_pos p hp hg; omega)
      refine ⟨c, hc, ?_⟩
      intro i hi1 hi2
      cases Nat.lt_or_ge i (j + 1) with
      | inl hlt => exact Nat.dvd_trans (hall i hi1 (by omega)) hdc1
      | inr hge =>
        have hi : i = j + 1 := by omega
        rw [hi]
        exact hdc2

/-- **定理 (M103-6b): 指数元** — 全ての単数の位数を割り切る位数の
    単数 g が存在する（任意の単数は剰余正規化 c = mk (a % p) で
    1..p−1 の剰余に一致する）。 -/
theorem exponent_element (p : Nat) (hp : IsPrime p) :
    ∃ g, IsZmodUnit p g ∧ ∀ c, IsZmodUnit p c →
      zmodOrd p c ∣ zmodOrd p g := by
  obtain ⟨g, hg, hall⟩ := exponent_fold p hp (p - 1)
    (by have := hp.1; omega) (Nat.le_refl _)
  refine ⟨g, hg, ?_⟩
  intro c hc
  obtain ⟨a, ha, hpa⟩ := hc
  have hp2 := hp.1
  have hpne : ((p : Nat) : Int) ≠ 0 := by
    intro h
    omega
  have hnonneg : 0 ≤ a % ((p : Nat) : Int) := Int.emod_nonneg a hpne
  have hlt : a % ((p : Nat) : Int) < ((p : Nat) : Int) :=
    Int.emod_lt_of_pos a (by omega)
  have hne : a % ((p : Nat) : Int) ≠ 0 := by
    intro h
    exact hpa (Int.dvd_of_emod_eq_zero h)
  -- c = mk (a % p) = mk ↑i, i := (a % p).toNat ∈ [1, p−1]
  have hmod : c = Quot.mk (modCong (p ^ 1)).rel (a % ((p : Nat) : Int)) := by
    rw [ha]
    apply Quot.sound
    show ((p ^ 1 : Nat) : Int) ∣ a - a % ((p : Nat) : Int)
    rw [Nat.pow_one]
    have hdm := Int.mul_ediv_add_emod a ((p : Nat) : Int)
    have key : ∀ (X Q M : Int), Q + M = X → X - M = Q := by
      intro X Q M h
      omega
    exact ⟨a / ((p : Nat) : Int),
      (key a (((p : Nat) : Int) * (a / ((p : Nat) : Int)))
        (a % ((p : Nat) : Int)) hdm).symm ▸ rfl⟩
  have hcast : (((a % ((p : Nat) : Int)).toNat : Nat) : Int)
      = a % ((p : Nat) : Int) := Int.toNat_of_nonneg hnonneg
  have hci : c = Quot.mk (modCong (p ^ 1)).rel
      (((a % ((p : Nat) : Int)).toNat : Nat) : Int) := by
    rw [hmod]
    exact congrArg (Quot.mk (modCong (p ^ 1)).rel) hcast.symm
  rw [hci]
  apply hall
  · omega
  · omega

/-! ## 原始根の存在（本丸） -/

/-- **定理 (M103-7): 原始根の存在 = (ℤ/p)^× の巡回性** —
    位数 p−1 の単数 g が存在する。ord g < p−1 なら 1, 2, …, ord g + 1
    の相異なる剰余が X^{ord g} = 1 の ord g + 1 個の相異なる根となり
    roots_bound（M96）に矛盾。issue #36 B-3 の「巡回性」本体。 -/
theorem primitive_root_exists (p : Nat) (hp : IsPrime p) :
    ∃ g, IsZmodUnit p g ∧ zmodOrd p g = p - 1 := by
  obtain ⟨g, hg, hexp⟩ := exponent_element p hp
  refine ⟨g, hg, ?_⟩
  have hle : zmodOrd p g ≤ p - 1 := zmodOrd_le p hp hg
  cases Nat.lt_or_ge (zmodOrd p g) (p - 1) with
  | inr hge => exact Nat.le_antisymm hle hge
  | inl hlt =>
    exfalso
    have hpos := zmodOrd_pos p hp hg
    have hp2 := hp.1
    obtain ⟨m, hm⟩ : ∃ m, zmodOrd p g = m + 1 := ⟨zmodOrd p g - 1, by omega⟩
    -- 根の族 r i := mk ↑(i+1)（i ≤ m+1、値は 1..(ord g)+1 ≤ p−1）
    have hunit : ∀ i, i ≤ m + 1 →
        IsZmodUnit p (Quot.mk (modCong (p ^ 1)).rel ((i + 1 : Nat) : Int)) := by
      intro i hi
      refine ⟨((i + 1 : Nat) : Int), rfl, ?_⟩
      intro hdvd
      have h2 : p ∣ i + 1 := Int.ofNat_dvd.mp hdvd
      have h3 := Nat.le_of_dvd (by omega) h2
      omega
    have hdist : ∀ i j, i < j → j ≤ m + 1 →
        Quot.mk (modCong (p ^ 1)).rel ((i + 1 : Nat) : Int)
          ≠ Quot.mk (modCong (p ^ 1)).rel ((j + 1 : Nat) : Int) := by
      intro i j hij hj heq
      have h2 := quot_exact intGrp (modCong (p ^ 1)) heq
      have h3 : ((p ^ 1 : Nat) : Int)
          ∣ ((i + 1 : Nat) : Int) - ((j + 1 : Nat) : Int) := h2
      rw [Nat.pow_one] at h3
      have h4 : ((p : Nat) : Int)
          ∣ ((j + 1 : Nat) : Int) - ((i + 1 : Nat) : Int) := dvd_sub_symm h3
      have h5 : ((j + 1 : Nat) : Int) - ((i + 1 : Nat) : Int)
          = ((j - i : Nat) : Int) := by omega
      rw [h5] at h4
      have h6 : p ∣ j - i := Int.ofNat_dvd.mp h4
      have h7 := Nat.le_of_dvd (by omega) h6
      omega
    have hroots : ∀ i, i ≤ m + 1 →
        rpow (zmodRing (p ^ 1))
          (Quot.mk (modCong (p ^ 1)).rel ((i + 1 : Nat) : Int)) (m + 1)
        = (zmodRing (p ^ 1)).one := by
      intro i hi
      rw [← zmodPow_eq_rpow]
      have hu := hunit i hi
      have hdvd_i : zmodOrd p (Quot.mk (modCong (p ^ 1)).rel ((i + 1 : Nat) : Int))
          ∣ zmodOrd p g := hexp _ hu
      obtain ⟨t, ht⟩ := hdvd_i
      have he : m + 1
          = zmodOrd p (Quot.mk (modCong (p ^ 1)).rel ((i + 1 : Nat) : Int)) * t := by
        rw [← ht, ← hm]
      have hsplit : zmodPow (p ^ 1)
          (Quot.mk (modCong (p ^ 1)).rel ((i + 1 : Nat) : Int)) (m + 1)
          = Quot.mk (modCong (p ^ 1)).rel 1 := by
        have h8 : zmodPow (p ^ 1)
            (Quot.mk (modCong (p ^ 1)).rel ((i + 1 : Nat) : Int)) (m + 1)
            = zmodPow (p ^ 1)
              (Quot.mk (modCong (p ^ 1)).rel ((i + 1 : Nat) : Int))
              (zmodOrd p (Quot.mk (modCong (p ^ 1)).rel ((i + 1 : Nat) : Int)) * t) :=
          congrArg (zmodPow (p ^ 1) _) he
        rw [h8, zmodPow_mul, zmodOrd_pow_eq_one p hp hu, zmodPow_one_base]
      exact hsplit
    exact bin_roots_bound (zmodRing (p ^ 1)) (zmod_no_zero_div p hp)
      (zmodRing_one_ne_zero p hp) (zmodRing (p ^ 1)).one m
      (fun i => Quot.mk (modCong (p ^ 1)).rel ((i + 1 : Nat) : Int))
      hdist hroots

end IUT
