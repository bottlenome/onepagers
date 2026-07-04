/-
# M169: 絶対値の冪・単位・冪等法則（柱C）

M127F（rabs の基本法則: congruence・rabs_mul 乗法性・三角不等式）と
M166/M167（実数の冪 realPow）の合流。絶対値 rabs が**冪に対して
乗法的**（|r^k| ≈ |r|^k）であること、単位を固定すること（|1| ≈ 1）、
冪等であること（||x|| ≈ |x|）を realEq 下で閉じる。

  * M169-1 `rabs_one` — |1| ≈ 1
  * M169-2 `rabs_idem` — ||x|| ≈ |x|（絶対値の冪等性）
  * M169-3 **`rabs_pow`** — 冪の絶対値: |r^k| ≈ |r|^k
    （k の帰納 + M127F rabs_mul）
  * M169-4 `RealAbsPowData` — 総括

意義: |r^k| = |r|^k は「|r| < 1 なら |r^k| = |r|^k → 0」という収束論
（幾何級数 M165/M168 の残差評価）の中核の代数的下地。M167 で
realPow が可換モノイド準同型的な法則を満たすことを示したが、本層は
その絶対値版——rabs が realPow と可換（絶対値と冪の交換）——を与える。

正直な限定: |r^k| → 0（|r| < 1 のときの実際の収束）は次層
（rate-bound + 順序を要す）。本層は純代数の交換法則のみ。

全て選択公理不使用。
-/
import IUT.RealAbs
import IUT.RealPow

namespace IUT

/-! ## M169-1: 単位 -/

/-- **定理 (M169-1): 単位の絶対値** — |1| ≈ 1。定数列 1 の各項で
    qAbs 1 = 1（rfl）。 -/
theorem rabs_one : realEq (rabs (qToReal ratRing.one)) (qToReal ratRing.one) :=
  realEq_of_seq_eq (fun _ => rfl)

/-! ## M169-2: 冪等性 -/

/-- **定理 (M169-2): 絶対値の冪等性** — ||x|| ≈ |x|。各項で
    qAbs (qAbs a) = qAbs a（M127F qAbs_idem）。 -/
theorem rabs_idem (x : RReal) : realEq (rabs (rabs x)) (rabs x) :=
  realEq_of_seq_eq (fun n => qAbs_idem (x.seq n))

/-! ## M169-3: 冪の絶対値 -/

/-- **定理 (M169-3): 冪の絶対値** — |r^k| ≈ |r|^k。
    k の帰納: 0 は |1| ≈ 1（M169-1）、k+1 は
    |r^k · r| ≈ |r^k|·|r| ≈ |r|^k·|r|（rabs_mul + IH の左 congruence）。 -/
theorem rabs_pow (r : RReal) :
    ∀ k, realEq (rabs (realPow r k)) (realPow (rabs r) k) := by
  intro k
  induction k with
  | zero =>
    show realEq (rabs (qToReal ratRing.one)) (qToReal ratRing.one)
    exact rabs_one
  | succ k ih =>
    show realEq (rabs (rmul (realPow r k) r))
        (rmul (realPow (rabs r) k) (rabs r))
    exact realEq_trans (rabs_mul (realPow r k) r)
      (rmul_congr_left (rabs r) ih)

/-! ## M169-4: 総括 -/

/-- **M169-4a: 総括** — 絶対値の冪・単位・冪等法則データ。 -/
structure RealAbsPowData where
  /-- 単位 |1| ≈ 1。 -/
  abs_one : realEq (rabs (qToReal ratRing.one)) (qToReal ratRing.one)
  /-- 冪等 ||x|| ≈ |x|。 -/
  abs_idem : ∀ x : RReal, realEq (rabs (rabs x)) (rabs x)
  /-- 冪の絶対値 |r^k| ≈ |r|^k。 -/
  abs_pow : ∀ (r : RReal) (k : Nat),
    realEq (rabs (realPow r k)) (realPow (rabs r) k)

/-- **M169-4b: witness**。 -/
def realAbsPowData : RealAbsPowData where
  abs_one := rabs_one
  abs_idem := rabs_idem
  abs_pow := rabs_pow

/-- **M169-4c: 存在**。 -/
theorem realAbsPow_exists : Nonempty RealAbsPowData := ⟨realAbsPowData⟩

end IUT
