/-
# M166: 実数の冪法則 — realPow の加法性と congruence（柱C）

M165 で定義した実数の冪 `realPow`（realPow r 0 = 1、
realPow r (k+1) = realPow r k · r）の基本法則を realEq 下で閉じる。
実数の級数・収束論のどこでも使う土台補題。

  * M166-1 `realPow_succ` — 一段展開 r^{k+1} = r^k · r（定義）
  * M166-2 **`realPow_add`** — 指数法則 r^{m+n} ≈ r^m · r^n
    （n の帰納 + rmul_one / rmul_assoc_real / congruence）
  * M166-3 `realPow_congr` — 底の congruence r ≈ r' ⟹ r^k ≈ r'^k
  * M166-4 `RealPowData` — 総括

意義: M165 の幾何級数と併せ、実数の冪級数を扱うための最小限の
代数語彙（指数法則 + 底の well-defined 性）を realEq 下で確立する。
とくに realPow_congr は「realEq を尊重する冪」= 冪が RReal/≈ 上の
写像として井戸定義であることの内容。

正直な限定: 実数の冪の順序的性質（0 ≤ r ≤ 1 での r^k の単調減少・
r^k → 0 の収束）は次層（rate-bound を要す）。本層は純代数の指数法則
と congruence のみ。

全て選択公理不使用。
-/
import IUT.RealGeom

namespace IUT

/-! ## M166-1: 一段展開 -/

/-- **M166-1: 一段展開** — r^{k+1} = r^k · r（定義そのもの）。 -/
theorem realPow_succ (r : RReal) (k : Nat) :
    realPow r (k + 1) = rmul (realPow r k) r := rfl

/-! ## M166-2: 指数法則 -/

/-- **定理 (M166-2): 指数法則** — r^{m+n} ≈ r^m · r^n（realEq 下）。
    n の帰納: n = 0 は r^m · r^0 = r^m · 1 ≈ r^m（rmul_one）、
    n+1 は r^{m+n}·r ≈ (r^m·r^n)·r ≈ r^m·(r^n·r)（IH の左 congruence
    + M150 結合）。 -/
theorem realPow_add (r : RReal) (m : Nat) :
    ∀ n, realEq (realPow r (m + n)) (rmul (realPow r m) (realPow r n)) := by
  intro n
  induction n with
  | zero =>
    show realEq (realPow r m) (rmul (realPow r m) (qToReal ratRing.one))
    exact realEq_symm (rmul_one (realPow r m))
  | succ n ih =>
    show realEq (rmul (realPow r (m + n)) r)
        (rmul (realPow r m) (rmul (realPow r n) r))
    exact realEq_trans (rmul_congr_left r ih)
      (rmul_assoc_real (realPow r m) (realPow r n) r)

/-! ## M166-3: 底の congruence -/

/-- **定理 (M166-3): 底の congruence** — r ≈ r' ⟹ r^k ≈ r'^k。
    k の帰納: 0 は両辺 1（refl）、k+1 は r^k·r ≈ r'^k·r'（左右
    congruence の合成）。冪が RReal/≈ 上で井戸定義であることの内容。 -/
theorem realPow_congr {r r' : RReal} (h : realEq r r') :
    ∀ k, realEq (realPow r k) (realPow r' k) := by
  intro k
  induction k with
  | zero => exact realEq_refl (qToReal ratRing.one)
  | succ k ih =>
    show realEq (rmul (realPow r k) r) (rmul (realPow r' k) r')
    exact realEq_trans (rmul_congr_left r ih)
      (rmul_congr_right (realPow r' k) h)

/-! ## M166-4: 総括 -/

/-- **M166-4a: 総括** — 実数の冪法則データ（指数法則・底 congruence）。 -/
structure RealPowData where
  /-- 指数法則 r^{m+n} ≈ r^m · r^n。 -/
  pow_add : ∀ (r : RReal) (m n : Nat),
    realEq (realPow r (m + n)) (rmul (realPow r m) (realPow r n))
  /-- 底の congruence r ≈ r' ⟹ r^k ≈ r'^k。 -/
  pow_congr : ∀ {r r' : RReal}, realEq r r' →
    ∀ k, realEq (realPow r k) (realPow r' k)

/-- **M166-4b: witness**。 -/
def realPowData : RealPowData where
  pow_add := fun r m n => realPow_add r m n
  pow_congr := fun h k => realPow_congr h k

/-- **M166-4c: 存在**。 -/
theorem realPow_exists : Nonempty RealPowData := ⟨realPowData⟩

end IUT
