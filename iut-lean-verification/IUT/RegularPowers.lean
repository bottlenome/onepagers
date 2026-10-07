/-
# M146F: 正則元の冪 — λₙ^k ≠ 0 の全レベル・全冪伝播（λ-adic 付値の台）

M144（λ の全レベル正則性）の直上に立つ柱B の一歩。正則元（非零因子）
が積と冪で閉じることを整備し、M144 の tower_lam_regular から
**λₙ の全冪 λₙ^k ≠ 0（∀ n, ∀ k）** を導く。分岐フィルトレーション
(λₙ^k)_{k≥1} の全段が潰れていないことの機械検証であり、λ-adic 付値
v(λₙ^k) = k の台（well-definedness の非零性側）となる。

  * M146F-1 `regular_one` — 1 は正則（h·1 = 0 → h = 0）
  * M146F-2 `regular_mul` — 正則元は積で閉じる（結合律の付け替え）
  * M146F-3 `regular_rpow` — 正則元の全冪は正則（帰納）
  * M146F-4 `regular_pow_ne_zero` — 非自明環で正則元の全冪は非零
    （k = 0 も rpow = 1 ≠ 0 で成立、場合分け不要）
  * M146F-5 **`tower_lam_pow_ne_zero_all`（見出し）** —
    **∀ n k, λₙ^k ≠ 0**: Lubin–Tate 塔の全レベルで一意化元の全冪が
    非零 = 分岐フィルトレーションの各段が生きている
  * M146F-6 `zp_pi_regular_elem` / `zp_one_ne_zero` /
    `zp_pi_pow_ne_zero` — π 側の基底: ℤ_p で π^k ≠ 0（M122-6 の
    平明正則性を IsRegularElem 形に包み直して全冪へ）
  * M146F-7 `RegularPowersData` — 総括

意義: M144 が閉じた「λₙ ≠ 0」は付値の第一段にすぎない。付値
v(λₙ^k) = k が意味を持つには全ての冪が非零（フィルトレーションが
無限降下しない）ことが要る。本層はその全段非退化を選言なし・
公理仮定なしで閉じ、λ-adic 簿記（柱B）の土台を敷く。

正直な限定: 付値関数 v(λₙ^k) = k そのもの（min の構成的定義）は
次層。本層が与えるのは付値の台 = 全冪の非零性である。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.LambdaPropagation

namespace IUT

/-! ## M146F-1: 単位元の正則性 -/

/-- **定理 (M146F-1): 1 は正則** — h·1 = 0 なら h = 0。 -/
theorem regular_one (R : CRing) : IsRegularElem R R.one := by
  intro h hh
  rw [R.mul_comm h R.one, R.one_mul h] at hh
  exact hh

/-! ## M146F-2: 積の正則性 -/

/-- **定理 (M146F-2): 正則元は積で閉じる** — h·(ab) = 0 なら
    (h·a)·b = 0（結合律）→ h·a = 0（b 正則）→ h = 0（a 正則）。 -/
theorem regular_mul (R : CRing) {a b : R.carrier}
    (ha : IsRegularElem R a) (hb : IsRegularElem R b) :
    IsRegularElem R (R.mul a b) := by
  intro h hh
  apply ha h
  apply hb (R.mul h a)
  rw [R.mul_assoc h a b]
  exact hh

/-! ## M146F-3: 冪の正則性 -/

/-- **定理 (M146F-3): 正則元の全冪は正則** — k = 0 は 1 の正則性、
    k+1 は rpow の展開と M146F-2。 -/
theorem regular_rpow (R : CRing) {a : R.carrier}
    (ha : IsRegularElem R a) : ∀ k, IsRegularElem R (rpow R a k) := by
  intro k
  induction k with
  | zero => exact regular_one R
  | succ k ih =>
    show IsRegularElem R (R.mul (rpow R a k) a)
    exact regular_mul R ih ha

/-! ## M146F-4: 非自明環での全冪非零性 -/

/-- **定理 (M146F-4): 正則元の全冪は非零** — 1 ≠ 0 の環で正則元 a の
    rpow a k ≠ 0（M144-5 の regular_ne_zero + M146F-3）。k = 0 でも
    rpow = 1 ≠ 0 で成立するため場合分けは不要。 -/
theorem regular_pow_ne_zero (R : CRing) (hone : R.one ≠ R.zero)
    {a : R.carrier} (ha : IsRegularElem R a) (k : Nat) :
    rpow R a k ≠ R.zero :=
  regular_ne_zero R hone (regular_rpow R ha k)

/-! ## M146F-5: λₙ^k ≠ 0 の全レベル・全冪伝播（見出し） -/

/-- **定理 (M146F-5): λₙ^k ≠ 0 全レベル・全冪（見出し）** —
    **Lubin–Tate 塔の全レベルで一意化元の全冪が非零 = 分岐フィルト
    レーション (λₙ^k) の各段が生きている**。M111（Oₙ ≠ 0）×
    M144（λₙ の全レベル正則性）× M146F-4 の合流。λ-adic 付値
    v(λₙ^k) = k の台。 -/
theorem tower_lam_pow_ne_zero_all (p : Nat) (hp : 2 ≤ p) (n k : Nat) :
    rpow (towerLevel p n).ring (towerLevel p n).lam k
      ≠ (towerLevel p n).ring.zero :=
  regular_pow_ne_zero (towerLevel p n).ring (tower_one_ne_zero p hp n)
    (tower_lam_regular p hp n) k

/-! ## M146F-6: π 側の基底 — ℤ_p で π^k ≠ 0 -/

/-- **M146F-6a: π の IsRegularElem 形** — M122-6 zp_pi_regular は
    π·y = 0 → y = 0（π が左）の形なので、mul_comm で
    IsRegularElem（π が右）に包み直す。 -/
theorem zp_pi_regular_elem (p : Nat) (hp : 2 ≤ p) :
    IsRegularElem (zpRing p) (zpPi p) := by
  intro h hh
  apply zp_pi_regular p hp h
  rw [(zpRing p).mul_comm (zpPi p) h]
  exact hh

/-- **M146F-6b: ℤ_p の非自明性** — 1 ≠ 0。レベル 1 の射影で
    ℤ/p の 1 ≠ 0（zmod_one_ne_zero、M93F）に帰着。 -/
theorem zp_one_ne_zero (p : Nat) (hp : 2 ≤ p) :
    (zpRing p).one ≠ (zpRing p).zero := by
  intro h
  exact zmod_one_ne_zero (p ^ 1) (two_le_pow p hp 1 (Nat.le_refl 1))
    (congrArg (fun z => z.val 1) h)

/-- **定理 (M146F-6c): π^k ≠ 0 in ℤ_p** — π 側の分岐基底。
    e = p−1 の分岐指数簿記 v(π) = 1 = v(λ^{p−1}) の非零性側。 -/
theorem zp_pi_pow_ne_zero (p : Nat) (hp : 2 ≤ p) (k : Nat) :
    rpow (zpRing p) (zpPi p) k ≠ (zpRing p).zero :=
  regular_pow_ne_zero (zpRing p) (zp_one_ne_zero p hp)
    (zp_pi_regular_elem p hp) k

/-! ## M146F-7: 総括 -/

/-- **M146F-7a: 総括** — 正則元の閉性と全冪非零性のデータ。 -/
structure RegularPowersData (p : Nat) (hp : 2 ≤ p) where
  /-- 正則元は積で閉じる（一般環）。 -/
  regular_closure_mul : ∀ (R : CRing) (a b : R.carrier),
    IsRegularElem R a → IsRegularElem R b →
    IsRegularElem R (R.mul a b)
  /-- 正則元は冪で閉じる（一般環）。 -/
  regular_closure_pow : ∀ (R : CRing) (a : R.carrier),
    IsRegularElem R a → ∀ k, IsRegularElem R (rpow R a k)
  /-- λₙ^k ≠ 0（全レベル・全冪）。 -/
  lam_pow_ne_zero : ∀ n k,
    rpow (towerLevel p n).ring (towerLevel p n).lam k
      ≠ (towerLevel p n).ring.zero
  /-- π^k ≠ 0 in ℤ_p（π 側の基底）。 -/
  pi_pow_ne_zero : ∀ k,
    rpow (zpRing p) (zpPi p) k ≠ (zpRing p).zero

/-- **M146F-7b: witness**。 -/
def regularPowersData (p : Nat) (hp : 2 ≤ p) :
    RegularPowersData p hp where
  regular_closure_mul := fun R _ _ ha hb => regular_mul R ha hb
  regular_closure_pow := fun R _ ha k => regular_rpow R ha k
  lam_pow_ne_zero := tower_lam_pow_ne_zero_all p hp
  pi_pow_ne_zero := zp_pi_pow_ne_zero p hp

/-- **M146F-7c: 存在**。 -/
theorem regularPowers_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (RegularPowersData p hp) :=
  ⟨regularPowersData p hp⟩

end IUT
