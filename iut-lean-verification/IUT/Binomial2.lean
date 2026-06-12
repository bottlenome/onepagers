/-
  IUT/Binomial2.lean — M44（可換環上の二変数二項定理: 第七層）

  Lubin–Tate 存在側の誤差項 p-整除性は「PS(ℤ_p) の新入生の夢
  (A+B)^p ≡ A^p + B^p (mod p)」に懸かっており、その代数的核心は
  **任意の可換環上の二変数二項定理**

    (x + y)^n = Σ_{k≤n} C(n,k) · x^k · y^{n−k}

  である（M32 の ℤ・一変数版 (x+1)^n の一般化）。係数 C(n,k) は
  自然数の環像 rofNat で送り、p ∣ C(p,k)（M32-5）が任意の環で
  「中間項は rofNat p の倍数」に翻訳される（M44-4）。

  * M44-1 `CRing.mul_one` / `CRing.add_left_comm` — 簿記
  * M44-2 `rofNat` / `rofNat_add` / `rofNat_mul` — **自然数の環像と
    その半環準同型性**（帰納法 + 分配）
  * M44-3 `binomial2` — **二変数二項定理**（Pascal 帰納。M32 と同じ
    分解 + y 冪の添字簿記。和の操作は全て M39 の rsum 補題）
  * M44-4 `rofNat_chs_factor` — **中間項の p-因子**: 0 < k < p なら
    rofNat C(p,k) = rofNat p · c（M32 の p ∣ C(p,k) の環像）

  残り: mod-p 還元 PS(ℤ_p) → PS(ℤ/p) と級数の新入生の夢 → 誤差項
  整除性 → 係数の再帰構成。全て選択公理不使用。
-/
import IUT.PadicDivision

namespace IUT

/-! ## 簿記 -/

/-- a·1 = a。 -/
theorem CRing.mul_one (R : CRing) (a : R.carrier) : R.mul a R.one = a := by
  rw [R.mul_comm]
  exact R.one_mul a

/-- a + (b + c) = b + (a + c)。 -/
theorem CRing.add_left_comm (R : CRing) (a b c : R.carrier) :
    R.add a (R.add b c) = R.add b (R.add a c) := by
  rw [← R.add_assoc, R.add_comm a b, R.add_assoc]

/-! ## 自然数の環像 -/

/-- 自然数の環像 n ↦ 1 + ⋯ + 1。 -/
def rofNat (R : CRing) : Nat → R.carrier
  | 0 => R.zero
  | n + 1 => R.add (rofNat R n) R.one

/-- rofNat は加法を保つ。 -/
theorem rofNat_add (R : CRing) (a : Nat) : ∀ b,
    rofNat R (a + b) = R.add (rofNat R a) (rofNat R b) := by
  intro b
  induction b with
  | zero =>
    show rofNat R a = R.add (rofNat R a) R.zero
    rw [R.add_zero]
  | succ b ih =>
    show R.add (rofNat R (a + b)) R.one
      = R.add (rofNat R a) (R.add (rofNat R b) R.one)
    rw [ih, R.add_assoc]

/-- rofNat は乗法を保つ。 -/
theorem rofNat_mul (R : CRing) (a : Nat) : ∀ b,
    rofNat R (a * b) = R.mul (rofNat R a) (rofNat R b) := by
  intro b
  induction b with
  | zero =>
    show R.zero = R.mul (rofNat R a) R.zero
    rw [R.mul_zero]
  | succ b ih =>
    show rofNat R (a * b + a) = R.mul (rofNat R a) (R.add (rofNat R b) R.one)
    rw [rofNat_add R (a * b) a, ih, R.left_distrib, R.mul_one]

/-! ## 二変数二項定理 -/

/-- **定理 (M44-3): 二変数二項定理** —
    (x+y)^n = Σ_{k≤n} C(n,k)·x^k·y^{n−k}（任意の可換環）。 -/
theorem binomial2 (R : CRing) (x y : R.carrier) : ∀ n,
    rpow R (R.add x y) n
      = rsum R (fun k => R.mul (rofNat R (chs n k))
          (R.mul (rpow R x k) (rpow R y (n - k)))) (n + 1) := by
  intro n
  induction n with
  | zero =>
    show R.one = R.add R.zero (R.mul (R.add R.zero R.one) (R.mul R.one R.one))
    rw [R.zero_add R.one, R.one_mul (R.mul R.one R.one), R.one_mul R.one,
      R.zero_add R.one]
  | succ n ih =>
    show R.mul (rpow R (R.add x y) n) (R.add x y)
      = rsum R (fun k => R.mul (rofNat R (chs (n + 1) k))
          (R.mul (rpow R x k) (rpow R y (n + 1 - k)))) (n + 2)
    rw [ih, R.left_distrib]
    have hSx : R.mul (rsum R (fun k => R.mul (rofNat R (chs n k))
          (R.mul (rpow R x k) (rpow R y (n - k)))) (n + 1)) x
        = rsum R (fun k => R.mul (rofNat R (chs n k))
            (R.mul (rpow R x (k + 1)) (rpow R y (n - k)))) (n + 1) := by
      have h1 : R.mul (rsum R (fun k => R.mul (rofNat R (chs n k))
            (R.mul (rpow R x k) (rpow R y (n - k)))) (n + 1)) x
          = rsum R (fun k => R.mul (R.mul (rofNat R (chs n k))
              (R.mul (rpow R x k) (rpow R y (n - k)))) x) (n + 1) :=
        rsum_mul_right R _ x (n + 1)
      rw [h1]
      exact rsum_congr R (n + 1) (fun k hk => by
        rw [R.mul_assoc (rofNat R (chs n k))
          (R.mul (rpow R x k) (rpow R y (n - k))) x]
        have hinner : R.mul (R.mul (rpow R x k) (rpow R y (n - k))) x
            = R.mul (rpow R x (k + 1)) (rpow R y (n - k)) := by
          rw [R.mul_assoc (rpow R x k) (rpow R y (n - k)) x,
            R.mul_comm (rpow R y (n - k)) x,
            ← R.mul_assoc (rpow R x k) x (rpow R y (n - k))]
          rfl
        rw [hinner])
    have hSy : R.mul (rsum R (fun k => R.mul (rofNat R (chs n k))
          (R.mul (rpow R x k) (rpow R y (n - k)))) (n + 1)) y
        = rsum R (fun k => R.mul (rofNat R (chs n k))
            (R.mul (rpow R x k) (rpow R y (n - k + 1)))) (n + 1) := by
      have h1 : R.mul (rsum R (fun k => R.mul (rofNat R (chs n k))
            (R.mul (rpow R x k) (rpow R y (n - k)))) (n + 1)) y
          = rsum R (fun k => R.mul (R.mul (rofNat R (chs n k))
              (R.mul (rpow R x k) (rpow R y (n - k)))) y) (n + 1) :=
        rsum_mul_right R _ y (n + 1)
      rw [h1]
      exact rsum_congr R (n + 1) (fun k hk => by
        rw [R.mul_assoc (rofNat R (chs n k))
          (R.mul (rpow R x k) (rpow R y (n - k))) y,
          R.mul_assoc (rpow R x k) (rpow R y (n - k)) y]
        rfl)
    rw [hSx, hSy]
    have hSyd : rsum R (fun k => R.mul (rofNat R (chs n k))
          (R.mul (rpow R x k) (rpow R y (n - k + 1)))) (n + 1)
        = R.add (R.mul (rofNat R (chs n 0))
            (R.mul (rpow R x 0) (rpow R y (n + 1))))
          (rsum R (fun k => R.mul (rofNat R (chs n (k + 1)))
            (R.mul (rpow R x (k + 1)) (rpow R y (n - (k + 1) + 1)))) n) :=
      rsum_head R _ n
    have hSyt : rsum R (fun k => R.mul (rofNat R (chs n (k + 1)))
          (R.mul (rpow R x (k + 1)) (rpow R y (n - (k + 1) + 1)))) n
        = rsum R (fun k => R.mul (rofNat R (chs n (k + 1)))
            (R.mul (rpow R x (k + 1)) (rpow R y (n - k)))) n :=
      rsum_congr R n (fun k hk => by
        rw [show n - (k + 1) + 1 = n - k by omega])
    rw [hSyd, hSyt]
    have hR : rsum R (fun k => R.mul (rofNat R (chs (n + 1) k))
          (R.mul (rpow R x k) (rpow R y (n + 1 - k)))) (n + 2)
        = R.add (R.mul (rofNat R (chs (n + 1) 0))
            (R.mul (rpow R x 0) (rpow R y (n + 1))))
          (rsum R (fun k => R.mul (rofNat R (chs (n + 1) (k + 1)))
            (R.mul (rpow R x (k + 1)) (rpow R y (n + 1 - (k + 1))))) (n + 1)) :=
      rsum_head R _ (n + 1)
    have hP : rsum R (fun k => R.mul (rofNat R (chs (n + 1) (k + 1)))
          (R.mul (rpow R x (k + 1)) (rpow R y (n + 1 - (k + 1))))) (n + 1)
        = rsum R (fun k => R.add
            (R.mul (rofNat R (chs n k))
              (R.mul (rpow R x (k + 1)) (rpow R y (n - k))))
            (R.mul (rofNat R (chs n (k + 1)))
              (R.mul (rpow R x (k + 1)) (rpow R y (n - k))))) (n + 1) :=
      rsum_congr R (n + 1) (fun k hk => by
        rw [show n + 1 - (k + 1) = n - k by omega]
        show R.mul (rofNat R (chs n k + chs n (k + 1)))
            (R.mul (rpow R x (k + 1)) (rpow R y (n - k))) = _
        rw [rofNat_add R (chs n k) (chs n (k + 1)), R.right_distrib])
    have hPA : rsum R (fun k => R.add
          (R.mul (rofNat R (chs n k))
            (R.mul (rpow R x (k + 1)) (rpow R y (n - k))))
          (R.mul (rofNat R (chs n (k + 1)))
            (R.mul (rpow R x (k + 1)) (rpow R y (n - k))))) (n + 1)
        = R.add (rsum R (fun k => R.mul (rofNat R (chs n k))
            (R.mul (rpow R x (k + 1)) (rpow R y (n - k)))) (n + 1))
          (rsum R (fun k => R.mul (rofNat R (chs n (k + 1)))
            (R.mul (rpow R x (k + 1)) (rpow R y (n - k)))) (n + 1)) :=
      rsum_add R _ _ (n + 1)
    have hP2 : rsum R (fun k => R.mul (rofNat R (chs n (k + 1)))
          (R.mul (rpow R x (k + 1)) (rpow R y (n - k)))) (n + 1)
        = R.add (rsum R (fun k => R.mul (rofNat R (chs n (k + 1)))
            (R.mul (rpow R x (k + 1)) (rpow R y (n - k)))) n)
          (R.mul (rofNat R (chs n (n + 1)))
            (R.mul (rpow R x (n + 1)) (rpow R y (n - n)))) := rfl
    have hzero : R.mul (rofNat R (chs n (n + 1)))
        (R.mul (rpow R x (n + 1)) (rpow R y (n - n))) = R.zero := by
      rw [chs_gt n (n + 1) (Nat.lt_succ_self n)]
      show R.mul R.zero (R.mul (rpow R x (n + 1)) (rpow R y (n - n))) = R.zero
      exact R.zero_mul _
    rw [hR, hP, hPA, hP2, hzero, R.add_zero, chs_zero n, chs_zero (n + 1)]
    exact R.add_left_comm _ _ _

/-! ## 中間項の p-因子 -/

/-- **定理 (M44-4): 中間項の p-因子** — 0 < k < p なら任意の環で
    rofNat C(p,k) = rofNat p · c（M32 の p ∣ C(p,k) の環像）。
    新入生の夢の「中間項は p で消える」の代数的内容。 -/
theorem rofNat_chs_factor (R : CRing) (p k : Nat) (hp : IsPrime p)
    (hk0 : 0 < k) (hkp : k < p) :
    ∃ c, rofNat R (chs p k) = R.mul (rofNat R p) c := by
  obtain ⟨c, hc⟩ := prime_dvd_chs p hp k hk0 hkp
  exact ⟨rofNat R c, by rw [hc, rofNat_mul]⟩

end IUT
