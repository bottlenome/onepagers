/-
  IUT/RootsOfUnity.lean — M34（ω の 1 の冪根性: Euler の定理と Teichmüller の可逆性）

  M33 で構成した Teichmüller 持ち上げ ω(a) が **(p−1) 乗で 1 になる**
  こと（μ_{p−1} に値を取ること）を完全証明する。鍵は Euler の定理の
  p 冪版 a^{p^n(p−1)} ≡ 1 (mod p^{n+1})（p ∤ a）で、これは古典形の
  Fermat の小定理 a^{p−1} ≡ 1 (mod p) を M33 の持ち上げ補題で
  反復昇格して得られる。

  * M34-1 `zmodPow` / `zpPow` — ℤ/p^n と ℤ_p の冪演算（商上 well-defined・
    遷移両立、`zpPow_succ` で zpMul と接続）
  * M34-2 `euclid_int` — **Euclid の補題の Int 版**: p ∣ xy、p ∤ x ⟹ p ∣ y
    （natAbs 経由で M32 の Nat 版に還元）
  * M34-3 `flt_unit` — **古典形 Fermat**: p ∤ a ⟹ a^{p−1} ≡ 1 (mod p)
    （a^p − a = a(a^{p−1} − 1) と Euclid）
  * M34-4 `euler_pow` — **Euler の定理（p 冪版）**:
    p^{n+1} ∣ a^{p^n(p−1)} − 1（基底 = M34-3、帰納段 = 持ち上げ補題）
  * M34-5 `teich_root_of_unity` — **ω(a)^{p−1} = 1**（p ∤ a）。
    Teichmüller 代表が 1 の (p−1) 乗根であること = μ_{p−1} への値域
  * M34-6 `teich_invertible` — **ω(a) は ℤ_p の単元**
    （逆元 = ω(a)^{p−2}、明示構成）

  未形式化: μ_{p−1} ≅ (ℤ/p)^×（巡回性）、O^× = μ × U^(1) の直積分解。
  全て選択公理不使用。
-/
import IUT.Teichmuller

namespace IUT

/-! ## ℤ/p^n と ℤ_p の冪演算 -/

/-- **M34-1a: ℤ/n の冪**（商上 well-defined、M30 の冪の合同両立から）。 -/
def zmodPow (n : Nat) (x : (zmod n).carrier) (k : Nat) : (zmod n).carrier :=
  Quot.lift (fun a => Quot.mk (modCong n).rel (ipow a k))
    (fun _ _ h => Quot.sound (dvd_sub_ipow h k)) x

/-- **M34-1b: ℤ_p の冪**（成分ごと、遷移両立）。 -/
def zpPow (p : Nat) (x : (Zp p).carrier) (k : Nat) : (Zp p).carrier :=
  ⟨fun n => zmodPow (p ^ n) (x.val n) k, by
    intro i j h
    have hcomp : (zmodTrans (pow_dvd_mono p h)).map (x.val j) = x.val i :=
      x.property h
    show (zmodTrans (pow_dvd_mono p h)).map (zmodPow (p ^ j) (x.val j) k)
      = zmodPow (p ^ i) (x.val i) k
    rw [← hcomp]
    induction x.val j using Quot.ind
    rfl⟩

/-- 冪と積の接続: x^{k+1} = x^k · x。 -/
theorem zpPow_succ (p : Nat) (x : (Zp p).carrier) (k : Nat) :
    zpPow p x (k + 1) = zpMul p (zpPow p x k) x := by
  apply Subtype.ext
  funext n
  show zmodPow (p ^ n) (x.val n) (k + 1)
    = zmodMul (p ^ n) (zmodPow (p ^ n) (x.val n) k) (x.val n)
  induction x.val n using Quot.ind
  rfl

/-! ## Euclid の補題（Int 版）と古典形 Fermat -/

/-- **定理 (M34-2): Euclid の補題の Int 版** — p ∣ xy、p ∤ x なら
    p ∣ y（natAbs 経由で Nat 版に還元）。 -/
theorem euclid_int (p : Nat) (hp : IsPrime p) {x y : Int}
    (h : ((p : Nat) : Int) ∣ x * y) (hx : ¬ ((p : Nat) : Int) ∣ x) :
    ((p : Nat) : Int) ∣ y := by
  have h1 : ((p : Nat) : Int).natAbs ∣ (x * y).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_natCast, Int.natAbs_mul] at h1
  cases euclid p hp h1 with
  | inl h2 =>
    exfalso
    apply hx
    have h3 : ((p : Nat) : Int).natAbs ∣ x.natAbs := by
      rw [Int.natAbs_natCast]
      exact h2
    exact Int.natAbs_dvd_natAbs.mp h3
  | inr h2 =>
    have h3 : ((p : Nat) : Int).natAbs ∣ y.natAbs := by
      rw [Int.natAbs_natCast]
      exact h2
    exact Int.natAbs_dvd_natAbs.mp h3

/-- **定理 (M34-3): 古典形 Fermat の小定理** — p ∤ a なら
    a^{p−1} ≡ 1 (mod p)。a^p − a = a·(a^{p−1} − 1) と Euclid から。 -/
theorem flt_unit (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    ((p : Nat) : Int) ∣ ipow a (p - 1) - 1 := by
  have hf := fermat_little p hp a
  have h1 : ipow a 1 = a := by
    show (1 : Int) * a = a
    rw [Int.one_mul]
  have hsplit : ipow a p = a * ipow a (p - 1) := by
    have h2 := ipow_add a 1 (p - 1)
    rw [h1] at h2
    rw [← h2]
    have h3 : p = 1 + (p - 1) := by have := hp.1; omega
    rw [← h3]
  have hfac : ipow a p - a = a * (ipow a (p - 1) - 1) := by
    rw [hsplit, Int.mul_sub, Int.mul_one]
  rw [hfac] at hf
  exact euclid_int p hp hf ha

/-- **定理 (M34-4): Euler の定理（p 冪版）** —
    p^{n+1} ∣ a^{p^n(p−1)} − 1（p ∤ a）。基底 = 古典形 Fermat、
    帰納段 = M33 の持ち上げ補題。 -/
theorem euler_pow (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) : ∀ n,
    ((p ^ (n + 1) : Nat) : Int) ∣ ipow a (p ^ n * (p - 1)) - 1 := by
  intro n
  induction n with
  | zero =>
    show ((p ^ 1 : Nat) : Int) ∣ ipow a (p ^ 0 * (p - 1)) - 1
    have he : p ^ 0 * (p - 1) = p - 1 := by
      rw [Nat.pow_zero, Nat.one_mul]
    rw [he, Nat.pow_one]
    exact flt_unit p hp ha
  | succ n ih =>
    have hl := pow_lift p hp ih (by omega)
    rw [← ipow_mul, one_ipow] at hl
    have he : p ^ n * (p - 1) * p = p ^ (n + 1) * (p - 1) := by
      rw [Nat.mul_assoc, Nat.mul_comm (p - 1) p, ← Nat.mul_assoc, ← Nat.pow_succ]
    rw [he] at hl
    exact hl

/-! ## Teichmüller 代表の 1 の冪根性 -/

/-- **定理 (M34-5): ω(a)^{p−1} = 1**（p ∤ a）— Teichmüller 代表は
    1 の (p−1) 乗根（値域 = μ_{p−1}）。レベル n では
    p^{n+1} ∣ a^{p^n(p−1)} − 1（Euler）の弱形を使う。 -/
theorem teich_root_of_unity (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    zpPow p (teich p hp a) (p - 1) = zpOne p := by
  apply Subtype.ext
  funext n
  show Quot.mk (modCong (p ^ n)).rel (ipow (ipow a (p ^ n)) (p - 1))
    = Quot.mk (modCong (p ^ n)).rel 1
  apply Quot.sound
  show ((p ^ n : Nat) : Int) ∣ ipow (ipow a (p ^ n)) (p - 1) - 1
  rw [← ipow_mul]
  exact Int.dvd_trans (Int.ofNat_dvd.mpr (pow_dvd_mono p (Nat.le_succ n)))
    (euler_pow p hp ha n)

/-- **定理 (M34-6): ω(a) は ℤ_p の単元** — 逆元 = ω(a)^{p−2} の
    明示構成（ω(a)^{p−2}·ω(a) = ω(a)^{p−1} = 1）。 -/
theorem teich_invertible (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    ∃ y, zpMul p y (teich p hp a) = zpOne p := by
  refine ⟨zpPow p (teich p hp a) (p - 2), ?_⟩
  have h1 : zpPow p (teich p hp a) (p - 2 + 1)
      = zpMul p (zpPow p (teich p hp a) (p - 2)) (teich p hp a) :=
    zpPow_succ p _ (p - 2)
  have h2 : p - 2 + 1 = p - 1 := by have := hp.1; omega
  rw [h2] at h1
  rw [← h1]
  exact teich_root_of_unity p hp ha

end IUT
