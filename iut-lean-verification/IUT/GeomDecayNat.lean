/-
# M179: 幾何減衰の算術核 — Bernoulli 型評価と減衰モジュラス（柱C）

幾何級数の**収束**（|r| < 1 ⟹ s_k → (1⊖r)⁻¹）の心臓部は「|r|^k → 0」
であり、それを支える純算術の核は Bernoulli 型不等式
(N+1)^k ≥ N^k·(1 + k/N) である。本モジュールはこの核を Nat の上で
（実数・有理数に依らず）choice なしで閉じ、**減衰のモジュラス**
（(N/(N+1))^k ≤ 1/(m+1) となる k の明示下界）を与える。

  * M179-1 `poly_step` — 帰納段の多項式補題 N·(N+k+1) ≤ (N+k)·(N+1)
  * M179-2 **`nat_geom_decay`** — Bernoulli 核:
    N^k·(N+k) ≤ N·(N+1)^k（⟺ (1+1/N)^k ≥ 1 + k/N）
  * M179-3 **`nat_geom_decay_modulus`** — 減衰モジュラス:
    N·m ≤ k ⟹ N^k·(m+1) ≤ (N+1)^k（⟺ (N/(N+1))^k ≤ 1/(m+1)）
  * M179-4 `GeomDecayNatData` — 総括

意義: 公比の絶対値が N/(N+1)（N ≥ 1）以下という有理的な上界を持てば、
その k 乗は 1/(m+1) 以下に、k ≥ N·m で確実に落ちる。これが幾何級数の
絶対収束（M175 |Σ| ≤ Σ|r|ⁱ・M177 誤差 = |r|^k）を実際の**収束**
（誤差 → 0）へ変換する算術エンジン。Archimedes 性の幾何級数版。

正直な限定: 本モジュールは Nat 上の算術核のみ。これを実数の収束
s_k → (1⊖r)⁻¹ に組み上げるには、(a) IsPos(1 ⊖ |r|) から有理上界
N/(N+1) を抽出、(b) |r|^k ≤ (N/(N+1))^k の実数単調性、(c) 本モジュラスで
|r|^k → 0（realEq 収束）、(d) s_k の IsCauchyReals 性と rlim（M128 完備性）
での極限構成、の 4 段が必要で、それらは次層（#48 に設計を集約）。

全て選択公理不使用。
-/
import IUT.Ring

namespace IUT

/-! ## M179-1: 多項式補題 -/

/-- **補題 (M179-1): 多項式段** — N·(N+k+1) ≤ (N+k)·(N+1)。
    両辺を mul_succ で展開すると (N+k)·N + N ≤ (N+k)·N + (N+k)、
    差は k ≥ 0（omega、積 (N+k)·N は同一綴りの原子）。 -/
theorem poly_step (N k : Nat) : N * (N + k + 1) ≤ (N + k) * (N + 1) := by
  rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_comm N (N + k)]
  omega

/-! ## M179-2: Bernoulli 核 -/

/-- **定理 (M179-2, 本丸): Bernoulli 核** — N^k·(N+k) ≤ N·(N+1)^k。
    (1+1/N)^k ≥ 1 + k/N の整数版。k の帰納: 段は IH に (N+1) を掛け、
    多項式補題 M179-1 と積の単調性で着地。 -/
theorem nat_geom_decay (N : Nat) :
    ∀ k, N ^ k * (N + k) ≤ N * (N + 1) ^ k := by
  intro k
  induction k with
  | zero => rw [Nat.pow_zero, Nat.pow_zero]; omega
  | succ k ih =>
    show N ^ (k + 1) * (N + k + 1) ≤ N * (N + 1) ^ (k + 1)
    have step1 : N ^ k * (N * (N + k + 1)) ≤ N ^ k * ((N + k) * (N + 1)) :=
      Nat.mul_le_mul (Nat.le_refl _) (poly_step N k)
    have step2 : N ^ k * ((N + k) * (N + 1)) = (N ^ k * (N + k)) * (N + 1) := by
      rw [Nat.mul_assoc]
    have step3 : (N ^ k * (N + k)) * (N + 1) ≤ (N * (N + 1) ^ k) * (N + 1) :=
      Nat.mul_le_mul ih (Nat.le_refl _)
    have combined : N ^ k * (N * (N + k + 1)) ≤ (N * (N + 1) ^ k) * (N + 1) :=
      Nat.le_trans step1 (Nat.le_trans (Nat.le_of_eq step2) step3)
    have lhs_eq : N ^ (k + 1) * (N + k + 1) = N ^ k * (N * (N + k + 1)) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have rhs_eq : (N * (N + 1) ^ k) * (N + 1) = N * (N + 1) ^ (k + 1) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [lhs_eq, ← rhs_eq]
    exact combined

/-! ## M179-3: 減衰モジュラス -/

/-- **定理 (M179-3, 本丸): 減衰モジュラス** — N ≥ 1・N·m ≤ k なら
    N^k·(m+1) ≤ (N+1)^k、すなわち (N/(N+1))^k ≤ 1/(m+1)。
    Bernoulli 核で N^k·(N+k) ≤ N·(N+1)^k、N+k ≥ N·(m+1)（k ≥ N·m）で
    N·(N^k·(m+1)) ≤ N·(N+1)^k、左簡約（N ≥ 1）。
    「k ≥ N·m で k 乗は 1/(m+1) 以下」= 幾何減衰の明示速度。 -/
theorem nat_geom_decay_modulus (N m k : Nat) (hN : 1 ≤ N) (hk : N * m ≤ k) :
    N ^ k * (m + 1) ≤ (N + 1) ^ k := by
  have h1 := nat_geom_decay N k
  have hms : N * (m + 1) = N * m + N := Nat.mul_succ N m
  have h2 : N * (m + 1) ≤ N + k := by omega
  have h3 : N ^ k * (N * (m + 1)) ≤ N * (N + 1) ^ k :=
    Nat.le_trans (Nat.mul_le_mul (Nat.le_refl _) h2) h1
  have e : N ^ k * (N * (m + 1)) = N * (N ^ k * (m + 1)) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (N ^ k) N, Nat.mul_assoc]
  rw [e] at h3
  exact Nat.le_of_mul_le_mul_left h3 hN

/-! ## M179-4: 総括 -/

/-- **M179-4a: 総括** — 幾何減衰の算術核データ。 -/
structure GeomDecayNatData where
  /-- Bernoulli 核 N^k·(N+k) ≤ N·(N+1)^k。 -/
  decay : ∀ (N k : Nat), N ^ k * (N + k) ≤ N * (N + 1) ^ k
  /-- 減衰モジュラス (N/(N+1))^k ≤ 1/(m+1)（k ≥ N·m）。 -/
  modulus : ∀ (N m k : Nat), 1 ≤ N → N * m ≤ k →
    N ^ k * (m + 1) ≤ (N + 1) ^ k

/-- **M179-4b: witness**。 -/
def geomDecayNatData : GeomDecayNatData where
  decay := nat_geom_decay
  modulus := nat_geom_decay_modulus

/-- **M179-4c: 存在**。 -/
theorem geomDecayNat_exists : Nonempty GeomDecayNatData := ⟨geomDecayNatData⟩

end IUT
