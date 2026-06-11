/-
  IUT/Arithmetic.lean

  テータ値 { q^{j²} } _{j=1,…,l⋇} に関する初等算術補題。

  IUT III 系3.12（およびその IUT IV §1 での使用）では、
  Θ-パイロット対象の「procession-normalized」な対数体積が
  j = 1,…,l⋇ にわたる j² の平均で重み付けされる。
  ここでは「j² の総和は l⋇ ≥ 2 で l⋇ 自身より真に大きい」
  という、Scholze–Stix の退化論法の核心となる不等式を証明する。

  参照: teichmuller/pdf/IUT_III_Canonical_Splittings.pdf p.174
        （系3.12 の statement: −|log(Θ)| ≥ −|log(q)|, |log(q)| > 0）
        teichmuller/pdf/IUT_IV_Log-volume_Computations.pdf §1

  依存: Lean 4 core のみ（mathlib 不使用）。
-/

namespace IUT

/-- `sumSq L = 1² + 2² + ⋯ + L²`。テータ値 q^{1²}, …, q^{L²} の
    次数（q の指数）の総和に対応する。 -/
def sumSq : Nat → Nat
  | 0 => 0
  | n + 1 => sumSq n + (n + 1) * (n + 1)

@[simp] theorem sumSq_zero : sumSq 0 = 0 := rfl

theorem sumSq_succ (n : Nat) : sumSq (n + 1) = sumSq n + (n + 1) * (n + 1) := rfl

/-- 検算: 1² + 2² = 5。 -/
example : sumSq 2 = 5 := rfl

/-- 検算: l = 7（l⋇ = 3）のとき 1² + 2² + 3² = 14。 -/
example : sumSq 3 = 14 := rfl

/-- 各項は正: `(n+1)² ≥ 1`。 -/
private theorem succ_sq_pos (n : Nat) : 1 ≤ (n + 1) * (n + 1) :=
  Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)

/-- 単調性: `sumSq L ≥ L`（各項 j² ≥ 1 より）。 -/
theorem sumSq_ge (L : Nat) : sumSq L ≥ L := by
  induction L with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [sumSq_succ]
    have h := succ_sq_pos n
    generalize (n + 1) * (n + 1) = m at h
    omega

/-- **核心補題**: `L ≥ 2` ならば `sumSq L > L`。

    すなわちテータ値の平均次数 (Σ j²)/l⋇ は 1 より真に大きい。
    q-パイロット（次数 1）と Θ-パイロット（平均次数 > 1）を
    「同じもの」と同一視すると、この差が矛盾を生む。

    IUT では l は 5 以上の素数で l⋇ = (l−1)/2 ≥ 2 なので、
    この仮定は常に満たされる。 -/
theorem sumSq_gt (L : Nat) (hL : L ≥ 2) : sumSq L > L := by
  induction L with
  | zero => omega
  | succ n ih =>
    rw [sumSq_succ]
    have h := succ_sq_pos n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · -- L = 1 は仮定に反し、L = 2 は直接計算 (sumSq 2 = 5 > 2)
      match n, hn with
      | 0, _ => omega
      | 1, _ => show sumSq 1 + 2 * 2 > 2; omega
    · have hs := ih hn
      generalize (n + 1) * (n + 1) = m at h
      omega

/-- 整数版: `L ≥ 2` ならば `(sumSq L : Int) > L`。 -/
theorem sumSq_gt_int (L : Nat) (hL : L ≥ 2) : (sumSq L : Int) > (L : Int) := by
  have := sumSq_gt L hL
  omega

/-- **閉形式**: `6 · Σ_{j=1}^{L} j² = L(L+1)(2L+1)`。
    IUT IV §1 の log-volume 計算でテータ値の平均次数
    (Σj²)/l⋇ = (l⋇+1)(2l⋇+1)/6 を評価する際の基礎式。 -/
theorem six_mul_sumSq (L : Nat) :
    6 * sumSq L = L * (L + 1) * (2 * L + 1) := by
  induction L with
  | zero => rfl
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
    -- 右辺の展開: (n+1)(n+2)(2n+3) = (n+1)·[n(2n+1) + (6n+6)]
    have e1 : (n + 1) * (n + 2) * (2 * n + 3)
        = (n + 1) * ((n + 2) * (2 * n + 3)) := Nat.mul_assoc _ _ _
    have e2 : (n + 2) * (2 * n + 3) = n * (2 * n + 1) + (6 * n + 6) := by
      have a1 : (n + 2) * (2 * n + 3) = n * (2 * n + 3) + 2 * (2 * n + 3) :=
        Nat.add_mul n 2 (2 * n + 3)
      have a2 : n * (2 * n + 3) = n * (2 * n + 1) + n * 2 := by
        rw [show 2 * n + 3 = 2 * n + 1 + 2 by omega, Nat.mul_add]
      rw [a1, a2]
      generalize n * (2 * n + 1) = A
      omega
    have e3 : (n + 1) * (n * (2 * n + 1) + (6 * n + 6))
        = (n + 1) * (n * (2 * n + 1)) + (n + 1) * (6 * n + 6) := Nat.mul_add _ _ _
    have e4 : (n + 1) * (n * (2 * n + 1)) = n * (n + 1) * (2 * n + 1) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (n + 1) n]
    have e5 : (n + 1) * (6 * n + 6) = 6 * ((n + 1) * (n + 1)) := by
      rw [show 6 * n + 6 = 6 * (n + 1) by omega, Nat.mul_left_comm]
    show 6 * (sumSq n + (n + 1) * (n + 1)) = (n + 1) * (n + 2) * (2 * n + 3)
    rw [Nat.mul_add, ih, e1, e2, e3, e4, e5]

end IUT
