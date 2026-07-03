/-
# M167: 実数の冪法則 II — 積・反復・単位（柱C）

M166（指数法則 r^{m+n} ≈ r^m·r^n・底 congruence）の続き。実数の冪
realPow の残りの基本法則——底の積・指数の積（反復冪）・単位冪——を
realEq 下で閉じる。M162 の実数版中央四項入替 `rmul_mul_mul_comm` と
M166 の `realPow_add` を再利用する。

  * M167-1 `realPow_one` — r^1 ≈ r
  * M167-2 **`realPow_mul_base`** — 底の積: (r·s)^k ≈ r^k · s^k
    （k の帰納 + 中央四項入替 rmul_mul_mul_comm）
  * M167-3 **`realPow_mul_exp`** — 指数の積（反復冪）:
    r^{m·n} ≈ (r^m)^n（n の帰納 + realPow_add）
  * M167-4 `RealPowMulData` — 総括

意義: M166 と併せ、実数の冪 realPow が可換モノイド準同型的な全法則
（r^0 = 1・r^{m+n} = r^m·r^n・(r·s)^k = r^k·s^k・(r^m)^n = r^{m·n}）を
realEq 下で満たすことが確立。実数の冪級数・多項式評価の代数基盤。

正直な限定: 順序・収束（r^k の単調性や極限）は含まない（rate-bound
の次層）。純代数の冪法則のみ。

全て選択公理不使用。
-/
import IUT.RealPow
import IUT.RealDivision

namespace IUT

/-! ## M167-1: 単位冪 -/

/-- **定理 (M167-1): 単位冪** — r^1 ≈ r。r^1 = 1·r ≈ r（可換 + rmul_one）。 -/
theorem realPow_one (r : RReal) : realEq (realPow r 1) r :=
  realEq_trans (rmul_comm (qToReal ratRing.one) r) (rmul_one r)

/-! ## M167-2: 底の積 -/

/-- **定理 (M167-2): 底の積** — (r·s)^k ≈ r^k · s^k。
    k の帰納: 0 は 1 ≈ 1·1（rmul_one）、k+1 は
    (r·s)^k·(r·s) ≈ (r^k·s^k)·(r·s) ≈ (r^k·r)·(s^k·s)
    （IH の左 congruence + M162 中央四項入替）。 -/
theorem realPow_mul_base (r s : RReal) :
    ∀ k, realEq (realPow (rmul r s) k) (rmul (realPow r k) (realPow s k)) := by
  intro k
  induction k with
  | zero =>
    show realEq (qToReal ratRing.one)
        (rmul (qToReal ratRing.one) (qToReal ratRing.one))
    exact realEq_symm (rmul_one (qToReal ratRing.one))
  | succ k ih =>
    show realEq (rmul (realPow (rmul r s) k) (rmul r s))
        (rmul (rmul (realPow r k) r) (rmul (realPow s k) s))
    exact realEq_trans (rmul_congr_left (rmul r s) ih)
      (rmul_mul_mul_comm (realPow r k) (realPow s k) r s)

/-! ## M167-3: 指数の積（反復冪） -/

/-- **定理 (M167-3): 反復冪** — r^{m·n} ≈ (r^m)^n。
    n の帰納: 0 は m·0 = 0 で両辺 1（refl）、n+1 は m·(n+1) = m·n + m
    で realPow_add により r^{m·n}·r^m、IH の左 congruence で
    (r^m)^n·r^m = (r^m)^{n+1}。 -/
theorem realPow_mul_exp (r : RReal) (m : Nat) :
    ∀ n, realEq (realPow r (m * n)) (realPow (realPow r m) n) := by
  intro n
  induction n with
  | zero =>
    rw [Nat.mul_zero]
    exact realEq_refl (qToReal ratRing.one)
  | succ n ih =>
    rw [Nat.mul_succ]
    show realEq (realPow r (m * n + m))
        (rmul (realPow (realPow r m) n) (realPow r m))
    exact realEq_trans (realPow_add r (m * n) m)
      (rmul_congr_left (realPow r m) ih)

/-! ## M167-4: 総括 -/

/-- **M167-4a: 総括** — 実数の冪法則 II データ（単位・底の積・反復冪）。 -/
structure RealPowMulData where
  /-- 単位冪 r^1 ≈ r。 -/
  pow_one : ∀ r : RReal, realEq (realPow r 1) r
  /-- 底の積 (r·s)^k ≈ r^k · s^k。 -/
  pow_mul_base : ∀ (r s : RReal) (k : Nat),
    realEq (realPow (rmul r s) k) (rmul (realPow r k) (realPow s k))
  /-- 反復冪 r^{m·n} ≈ (r^m)^n。 -/
  pow_mul_exp : ∀ (r : RReal) (m n : Nat),
    realEq (realPow r (m * n)) (realPow (realPow r m) n)

/-- **M167-4b: witness**。 -/
def realPowMulData : RealPowMulData where
  pow_one := realPow_one
  pow_mul_base := realPow_mul_base
  pow_mul_exp := realPow_mul_exp

/-- **M167-4c: 存在**。 -/
theorem realPowMul_exists : Nonempty RealPowMulData := ⟨realPowMulData⟩

end IUT
