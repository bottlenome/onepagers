/-
  IUT/ZmodOrder.lean — M102（B-3 後半・第一層: (ℤ/p)^× の位数理論）

  巡回性（原始根の存在）に向けた位数（order）の理論を、レベル 1 剰余群
  (ℤ/p)^×（M101 の zmodUnits）の上で構成する。位数は **fuel 付き有界
  探索**で最小 witness として実構成し（決定手続き = M91F の Bool 判定の
  流儀、選択公理回避）、基本性質を完全証明する。

  * M102-1 `zmodIsOne` — ℤ/n の **1 判定の Bool 値関数**（代表の emod
    による Quot.lift、M91F zmodIsZero の 1 版）と正当性
    `zmodIsOne_true` / `zmodIsOne_one` / `zmodIsOne_false`
  * M102-2 `zmodMul_assoc` / `zmodOne_mul` / `zmodPow_add` /
    `zmodPow_mul` / `zmodPow_one_base` — レベル環の演算法則
    （成分ごとの Int 恒等式）
  * M102-3 `zmodUnit_pow_card` — **Fermat**: 単数 c は c^{p−1} = 1
  * M102-4 `ordSearch` / `ordSearch_spec` — **fuel 付き最小 witness
    探索**: 範囲末尾に witness があれば最小 witness を返す（fuel 帰納）
  * M102-5 `zmodOrd` / `zmodOrd_spec` — **位数の実構成**:
    c^d = 1・1 ≤ d ≤ p−1・最小性（j < d なら c^j ≠ 1）
  * M102-6 `zmodOrd_dvd` — **位数の整除性**: c^k = 1 ⟹ d ∣ k
    （除算 k = dq + r と最小性）。系 `zmodOrd_dvd_card`: d ∣ p−1
  * M102-7 `zmod_unit_cancel` — 単数の簡約律（u^{p−2} を掛ける）
  * M102-8 `zmodOrd_powers_distinct` — **c^0, …, c^{d−1} は相異なる**
    （簡約律 + 最小性。巡回部分群の位数 = d の内容）
  * M102-9 `zmodOrd_pow_div` — **冪の位数**: e ∣ d なら
    ord(c^e) = d / e（整除性の両方向からの挟み撃ち）

  未形式化（次層）: 位数 lcm の実現（互いに素な位数の積の位数 =
  積）→ 全単数の位数を割る「指数」元の構成 → roots_bound（M96）に
  よる指数 ≥ p−1 → 原始根の存在（巡回性）。Nat 側の素数道具は
  M102F（NatPrimeParts）が供給する。
  全て選択公理不使用。
-/
import IUT.MuUnits

namespace IUT

/-! ## ℤ/n の 1 判定（Bool 値、M91F の流儀） -/

/-- 補助: A ≡ B (mod n) なら (A−1) % n = (B−1) % n（Int 変数で
    一般化して omega を通す）。 -/
theorem sub_one_emod_congr (n : Nat) : ∀ (A B : Int),
    ((n : Nat) : Int) ∣ A - B →
    (A - 1) % ((n : Nat) : Int) = (B - 1) % ((n : Nat) : Int) := by
  intro A B hAB
  obtain ⟨k, hk⟩ := hAB
  have hA : A - 1 = (B - 1) + ((n : Nat) : Int) * k := by
    rw [← hk]
    omega
  rw [hA, Int.add_mul_emod_self_left]

/-- **M102-1a: ℤ/n の 1 判定**（代表の emod による Bool 値
    Quot.lift。well-defined 性は emod の加法公式から）。 -/
def zmodIsOne (n : Nat) : (zmod n).carrier → Bool :=
  Quot.lift (fun c => decide ((c - 1) % ((n : Nat) : Int) = 0))
    (fun a b hab => by
      show decide ((a - 1) % ((n : Nat) : Int) = 0)
        = decide ((b - 1) % ((n : Nat) : Int) = 0)
      rw [sub_one_emod_congr n a b hab])

/-- **M102-1b**: 判定が true なら成分は 1。 -/
theorem zmodIsOne_true {n : Nat} {x : (zmod n).carrier}
    (h : zmodIsOne n x = true) : x = Quot.mk (modCong n).rel 1 := by
  revert h
  induction x using Quot.ind; rename_i c
  intro h
  have h' : decide ((c - 1) % ((n : Nat) : Int) = 0) = true := h
  have hc : (c - 1) % ((n : Nat) : Int) = 0 := of_decide_eq_true h'
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hc
  apply Quot.sound
  show ((n : Nat) : Int) ∣ c - 1
  exact ⟨k, hk⟩

/-- **M102-1c**: 1 での判定は true。 -/
theorem zmodIsOne_one (n : Nat) :
    zmodIsOne n (Quot.mk (modCong n).rel 1) = true := by
  show decide (((1 : Int) - 1) % ((n : Nat) : Int) = 0) = true
  have h : ((1 : Int) - 1) = 0 := by omega
  rw [h, Int.zero_emod]
  exact decide_eq_true rfl

/-- **M102-1d**: 判定が false なら成分は 1 でない。 -/
theorem zmodIsOne_false {n : Nat} {x : (zmod n).carrier}
    (h : zmodIsOne n x = false) : x ≠ Quot.mk (modCong n).rel 1 := by
  intro h1
  rw [h1, zmodIsOne_one] at h
  exact Bool.noConfusion h

/-! ## レベル環の演算法則（standalone 形） -/

/-- **M102-2a**: zmodMul の結合則。 -/
theorem zmodMul_assoc (n : Nat) (x y z : (zmod n).carrier) :
    zmodMul n (zmodMul n x y) z = zmodMul n x (zmodMul n y z) := by
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  induction z using Quot.ind; rename_i c
  show Quot.mk (modCong n).rel (a * b * c)
    = Quot.mk (modCong n).rel (a * (b * c))
  rw [Int.mul_assoc]

/-- **M102-2b**: 1 は zmodMul の左単位元。 -/
theorem zmodOne_mul (n : Nat) (x : (zmod n).carrier) :
    zmodMul n (Quot.mk (modCong n).rel 1) x = x := by
  induction x using Quot.ind; rename_i a
  show Quot.mk (modCong n).rel (1 * a) = Quot.mk (modCong n).rel a
  rw [Int.one_mul]

/-- **M102-2c: 冪の加法則** c^{i+j} = c^i · c^j。 -/
theorem zmodPow_add (n : Nat) (c : (zmod n).carrier) (i j : Nat) :
    zmodPow n c (i + j) = zmodMul n (zmodPow n c i) (zmodPow n c j) := by
  induction c using Quot.ind; rename_i a
  show Quot.mk (modCong n).rel (ipow a (i + j))
    = Quot.mk (modCong n).rel (ipow a i * ipow a j)
  rw [ipow_add]

/-- **M102-2d: 冪の乗法則** c^{ij} = (c^i)^j。 -/
theorem zmodPow_mul (n : Nat) (c : (zmod n).carrier) (i j : Nat) :
    zmodPow n c (i * j) = zmodPow n (zmodPow n c i) j := by
  induction c using Quot.ind; rename_i a
  show Quot.mk (modCong n).rel (ipow a (i * j))
    = Quot.mk (modCong n).rel (ipow (ipow a i) j)
  rw [ipow_mul]

/-- **M102-2e**: 1^k = 1。 -/
theorem zmodPow_one_base (n : Nat) (k : Nat) :
    zmodPow n (Quot.mk (modCong n).rel 1) k = Quot.mk (modCong n).rel 1 := by
  show Quot.mk (modCong n).rel (ipow 1 k) = Quot.mk (modCong n).rel 1
  rw [one_ipow]

/-! ## Fermat（レベル 1、standalone 形） -/

/-- **定理 (M102-3): Fermat** — 単数 c は c^{p−1} = 1（flt_unit の
    レベル 1 読み）。 -/
theorem zmodUnit_pow_card (p : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c) :
    zmodPow (p ^ 1) c (p - 1) = Quot.mk (modCong (p ^ 1)).rel 1 := by
  obtain ⟨a, ha, hpa⟩ := hc
  rw [ha]
  show Quot.mk (modCong (p ^ 1)).rel (ipow a (p - 1))
    = Quot.mk (modCong (p ^ 1)).rel 1
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ ipow a (p - 1) - 1
  rw [Nat.pow_one]
  exact flt_unit p hp hpa

/-! ## fuel 付き最小 witness 探索 -/

/-- **M102-4a: fuel 付き探索** — k から fuel ステップの範囲で
    c^j = 1 となる最初の j を返す（見つからなければ走り切った位置）。 -/
def ordSearch (n : Nat) (c : (zmod n).carrier) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k =>
    if zmodIsOne n (zmodPow n c k) = true then k
    else ordSearch n c fuel (k + 1)

/-- **定理 (M102-4b): 探索の仕様** — 範囲の末尾 k + fuel に witness が
    あれば、返り値は範囲内の**最小** witness（fuel の帰納法）。 -/
theorem ordSearch_spec (n : Nat) (c : (zmod n).carrier) : ∀ fuel k,
    zmodIsOne n (zmodPow n c (k + fuel)) = true →
    zmodIsOne n (zmodPow n c (ordSearch n c fuel k)) = true
    ∧ k ≤ ordSearch n c fuel k ∧ ordSearch n c fuel k ≤ k + fuel
    ∧ ∀ j, k ≤ j → j < ordSearch n c fuel k
      → zmodIsOne n (zmodPow n c j) = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk
    refine ⟨hk, Nat.le_refl k, Nat.le_refl k, ?_⟩
    intro j hj1 hj2
    exact absurd (Nat.lt_of_le_of_lt hj1 hj2) (Nat.lt_irrefl k)
  | succ fuel ih =>
    intro k hk
    cases htest : zmodIsOne n (zmodPow n c k) with
    | true =>
      have hred : ordSearch n c (fuel + 1) k = k := by
        show (if zmodIsOne n (zmodPow n c k) = true then k
          else ordSearch n c fuel (k + 1)) = k
        rw [htest]
        rfl
      rw [hred]
      refine ⟨htest, Nat.le_refl k, by omega, ?_⟩
      intro j hj1 hj2
      exact absurd (Nat.lt_of_le_of_lt hj1 hj2) (Nat.lt_irrefl k)
    | false =>
      have hred : ordSearch n c (fuel + 1) k = ordSearch n c fuel (k + 1) := by
        show (if zmodIsOne n (zmodPow n c k) = true then k
          else ordSearch n c fuel (k + 1)) = ordSearch n c fuel (k + 1)
        rw [htest]
        rfl
      have hk' : zmodIsOne n (zmodPow n c (k + 1 + fuel)) = true := by
        have he : k + 1 + fuel = k + (fuel + 1) := by omega
        rw [he]
        exact hk
      obtain ⟨h1, h2, h3, h4⟩ := ih (k + 1) hk'
      rw [hred]
      refine ⟨h1, by omega, by omega, ?_⟩
      intro j hj1 hj2
      cases Nat.eq_or_lt_of_le hj1 with
      | inl heq =>
        rw [← heq]
        exact htest
      | inr hlt => exact h4 j hlt hj2

/-! ## 位数の実構成 -/

/-- **M102-5a: 位数** — 1 から始めて c^d = 1 となる最小の d
    （単数なら Fermat により d ≤ p−1 で必ず見つかる）。 -/
def zmodOrd (p : Nat) (c : (zmod (p ^ 1)).carrier) : Nat :=
  ordSearch (p ^ 1) c (p - 2) 1

/-- **定理 (M102-5b): 位数の仕様** — c^d = 1・1 ≤ d ≤ p−1・最小性。 -/
theorem zmodOrd_spec (p : Nat) (hp : IsPrime p) {c : (zmod (p ^ 1)).carrier}
    (hc : IsZmodUnit p c) :
    zmodPow (p ^ 1) c (zmodOrd p c) = Quot.mk (modCong (p ^ 1)).rel 1
    ∧ 1 ≤ zmodOrd p c ∧ zmodOrd p c ≤ p - 1
    ∧ ∀ j, 1 ≤ j → j < zmodOrd p c
      → zmodPow (p ^ 1) c j ≠ Quot.mk (modCong (p ^ 1)).rel 1 := by
  have hfermat : zmodIsOne (p ^ 1) (zmodPow (p ^ 1) c (1 + (p - 2))) = true := by
    have he : 1 + (p - 2) = p - 1 := by have := hp.1; omega
    rw [he, zmodUnit_pow_card p hp hc]
    exact zmodIsOne_one (p ^ 1)
  obtain ⟨h1, h2, h3, h4⟩ := ordSearch_spec (p ^ 1) c (p - 2) 1 hfermat
  refine ⟨zmodIsOne_true h1, h2, ?_, ?_⟩
  · show ordSearch (p ^ 1) c (p - 2) 1 ≤ p - 1
    have := hp.1
    omega
  · intro j hj1 hj2
    exact zmodIsOne_false (h4 j hj1 hj2)

/-- **M102-5c**: c^{ord c} = 1。 -/
theorem zmodOrd_pow_eq_one (p : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c) :
    zmodPow (p ^ 1) c (zmodOrd p c) = Quot.mk (modCong (p ^ 1)).rel 1 :=
  (zmodOrd_spec p hp hc).1

/-- **M102-5d**: 1 ≤ ord c ≤ p−1。 -/
theorem zmodOrd_pos (p : Nat) (hp : IsPrime p) {c : (zmod (p ^ 1)).carrier}
    (hc : IsZmodUnit p c) : 1 ≤ zmodOrd p c :=
  (zmodOrd_spec p hp hc).2.1

theorem zmodOrd_le (p : Nat) (hp : IsPrime p) {c : (zmod (p ^ 1)).carrier}
    (hc : IsZmodUnit p c) : zmodOrd p c ≤ p - 1 :=
  (zmodOrd_spec p hp hc).2.2.1

/-! ## 位数の整除性 -/

/-- **定理 (M102-6a): 位数の整除性** — c^k = 1 なら ord c ∣ k
    （k = dq + r に分解し、c^r = 1 と r < d の最小性から r = 0）。 -/
theorem zmodOrd_dvd (p : Nat) (hp : IsPrime p) {c : (zmod (p ^ 1)).carrier}
    (hc : IsZmodUnit p c) {k : Nat}
    (hk : zmodPow (p ^ 1) c k = Quot.mk (modCong (p ^ 1)).rel 1) :
    zmodOrd p c ∣ k := by
  obtain ⟨hpow, hpos, hle, hmin⟩ := zmodOrd_spec p hp hc
  have hdm : zmodOrd p c * (k / zmodOrd p c) + k % zmodOrd p c = k :=
    Nat.div_add_mod k (zmodOrd p c)
  have hsplit : zmodPow (p ^ 1) c k
      = zmodMul (p ^ 1)
        (zmodPow (p ^ 1) (zmodPow (p ^ 1) c (zmodOrd p c)) (k / zmodOrd p c))
        (zmodPow (p ^ 1) c (k % zmodOrd p c)) := by
    rw [← zmodPow_mul, ← zmodPow_add]
    exact congrArg (zmodPow (p ^ 1) c) hdm.symm
  rw [hpow, zmodPow_one_base, zmodOne_mul, hk] at hsplit
  cases Nat.eq_zero_or_pos (k % zmodOrd p c) with
  | inl hzero => exact ⟨k / zmodOrd p c, by omega⟩
  | inr hpos' =>
    exfalso
    exact hmin (k % zmodOrd p c) hpos'
      (Nat.mod_lt k (by omega)) hsplit.symm

/-- **系 (M102-6b): ord c ∣ p − 1**（Fermat）。 -/
theorem zmodOrd_dvd_card (p : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c) :
    zmodOrd p c ∣ p - 1 :=
  zmodOrd_dvd p hp hc (zmodUnit_pow_card p hp hc)

/-! ## 単数の簡約律 -/

/-- **定理 (M102-7): 単数の簡約律** — a·u = b·u（u 単数）なら a = b
    （u^{p−2} を右から掛けて u·u^{p−2} = 1 で消去）。 -/
theorem zmod_unit_cancel (p : Nat) (hp : IsPrime p)
    {u a b : (zmod (p ^ 1)).carrier} (hu : IsZmodUnit p u)
    (h : zmodMul (p ^ 1) a u = zmodMul (p ^ 1) b u) : a = b := by
  have h2 : zmodMul (p ^ 1) (zmodMul (p ^ 1) a u) (zmodPow (p ^ 1) u (p - 2))
      = zmodMul (p ^ 1) (zmodMul (p ^ 1) b u) (zmodPow (p ^ 1) u (p - 2)) := by
    rw [h]
  rw [zmodMul_assoc, zmodMul_assoc] at h2
  have hui : zmodMul (p ^ 1) u (zmodPow (p ^ 1) u (p - 2))
      = Quot.mk (modCong (p ^ 1)).rel 1 := by
    rw [zmodMul_comm]
    exact zmodUnit_inv_mul p hp hu
  rw [hui, zmodMul_comm (p ^ 1) a, zmodMul_comm (p ^ 1) b,
    zmodOne_mul, zmodOne_mul] at h2
  exact h2

/-! ## 冪の相異性 -/

/-- **定理 (M102-8): c^0, …, c^{d−1} は相異なる** — c^i = c^j
    （i < j < d）なら c^{j−i} = 1 が最小性に矛盾（巡回部分群の
    位数 = d の実質）。 -/
theorem zmodOrd_powers_distinct (p : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c) :
    ∀ i j, i < j → j < zmodOrd p c
      → zmodPow (p ^ 1) c i ≠ zmodPow (p ^ 1) c j := by
  intro i j hij hj heq
  obtain ⟨hpow, hpos, hle, hmin⟩ := zmodOrd_spec p hp hc
  have hsplit : zmodPow (p ^ 1) c j
      = zmodMul (p ^ 1) (zmodPow (p ^ 1) c (j - i)) (zmodPow (p ^ 1) c i) := by
    have he : zmodPow (p ^ 1) c j = zmodPow (p ^ 1) c ((j - i) + i) :=
      congrArg (zmodPow (p ^ 1) c) (by omega)
    rw [he, zmodPow_add]
  have h1 : zmodMul (p ^ 1) (Quot.mk (modCong (p ^ 1)).rel 1)
        (zmodPow (p ^ 1) c i)
      = zmodMul (p ^ 1) (zmodPow (p ^ 1) c (j - i)) (zmodPow (p ^ 1) c i) :=
    (zmodOne_mul (p ^ 1) (zmodPow (p ^ 1) c i)).trans (heq.trans hsplit)
  have hone := zmod_unit_cancel p hp (isZmodUnit_pow p hp hc i) h1
  exact hmin (j - i) (by omega) (by omega) hone.symm

/-! ## 冪の位数 -/

/-- **定理 (M102-9): 冪の位数** — e ∣ d（e ≥ 1）なら
    ord(c^e) = d / e（両向きの整除性による挟み撃ち）。lcm 実現
    （次層）で q 冪部分を切り出す際の主装置。 -/
theorem zmodOrd_pow_div (p : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c)
    {e : Nat} (he : 1 ≤ e) (hdvd : e ∣ zmodOrd p c) :
    zmodOrd p (zmodPow (p ^ 1) c e) = zmodOrd p c / e := by
  obtain ⟨m, hm⟩ := hdvd
  obtain ⟨hpow, hpos, hle, hmin⟩ := zmodOrd_spec p hp hc
  have hce : IsZmodUnit p (zmodPow (p ^ 1) c e) := isZmodUnit_pow p hp hc e
  have h1 : zmodPow (p ^ 1) (zmodPow (p ^ 1) c e) m
      = Quot.mk (modCong (p ^ 1)).rel 1 := by
    rw [← zmodPow_mul]
    have hh : zmodPow (p ^ 1) c (e * m) = zmodPow (p ^ 1) c (zmodOrd p c) :=
      congrArg (zmodPow (p ^ 1) c) hm.symm
    rw [hh]
    exact hpow
  have hdvd1 : zmodOrd p (zmodPow (p ^ 1) c e) ∣ m :=
    zmodOrd_dvd p hp hce h1
  have h2 : zmodPow (p ^ 1) c (e * zmodOrd p (zmodPow (p ^ 1) c e))
      = Quot.mk (modCong (p ^ 1)).rel 1 := by
    rw [zmodPow_mul]
    exact zmodOrd_pow_eq_one p hp hce
  have hdvd2 : zmodOrd p c ∣ e * zmodOrd p (zmodPow (p ^ 1) c e) :=
    zmodOrd_dvd p hp hc h2
  obtain ⟨t, ht⟩ := hdvd2
  have hd' : zmodOrd p (zmodPow (p ^ 1) c e) = m * t := by
    have hh : e * zmodOrd p (zmodPow (p ^ 1) c e) = e * (m * t) := by
      rw [ht, hm, Nat.mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left (by omega) hh
  have heq : zmodOrd p (zmodPow (p ^ 1) c e) = m :=
    Nat.dvd_antisymm hdvd1 ⟨t, hd'⟩
  rw [heq, hm, Nat.mul_div_cancel_left m (by omega : 0 < e)]

end IUT
