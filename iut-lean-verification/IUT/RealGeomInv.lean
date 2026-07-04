/-
# M177: 実数幾何級数の逆元近似誤差 — |(1⊖r)·s_k ⊖ 1| ≈ |r|^k（柱C）

M176（環版の逆元近似 (1−r)·s_k − 1 ∈ (λ^{km})）の**実数版**。M168（実数
残差 (1⊖r)·s_k ⊕ r^k ≈ 1）・M169（|r^k| ≈ |r|^k）の合流で、実数幾何
部分和が 1⊖r の逆元を近似するときの**誤差が正確に −r^k**であり、その
絶対値が |r|^k に等しいことを realEq 下で閉じる。

  * M177-1 `real_neg_of_add_eq_zero` — 実数の反元特徴付け:
    x ⊕ y ≈ 0 ⟹ x ≈ ⊖y（汎用補題）
  * M177-2 **`real_geom_inv_error`** — 逆元近似の誤差:
    (1⊖r)·s_k ⊖ 1 ≈ ⊖r^k（M168 残差の移項）
  * M177-3 **`rabs_geom_inv_error`** — 誤差の絶対値:
    |(1⊖r)·s_k ⊖ 1| ≈ |r|^k（M169 で |⊖r^k| = |r^k| = |r|^k）
  * M177-4 `RealGeomInvData` — 総括

意義: M176 が付値環で誤差が (λ^{km}) に沈むことを示したのに対し、本層は
実数で**誤差の大きさが正確に |r|^k である**ことを与える。|r| < 1 なら
|r|^k → 0（次層）なので、s_k が (1⊖r)⁻¹ に収束する**誤差の閉じた形**
（残差 = −r^k、|残差| = |r|^k）が確定する。M175（|Σ| ≤ Σ|·|）と併せ
幾何級数の実数的収束論の直前段。

正直な限定: 収束そのもの（|r|^k → 0 と極限 (1⊖r)⁻¹ の同定）は
rate-bound・順序完備性の次層。本層は各有限 k での誤差の閉形式のみ。

全て選択公理不使用。
-/
import IUT.RealGeomRec
import IUT.RealAbsPow

namespace IUT

/-! ## M177-1: 実数の反元特徴付け -/

/-- **補題 (M177-1): 反元特徴付け** — x ⊕ y ≈ 0 なら x ≈ ⊖y。
    x ≈ x ⊕ 0 ≈ x ⊕ (y ⊕ (⊖y)) ≈ (x ⊕ y) ⊕ (⊖y) ≈ 0 ⊕ (⊖y) ≈ ⊖y。 -/
theorem real_neg_of_add_eq_zero {x y : RReal}
    (h : realEq (realAdd x y) realZero) : realEq x (realNeg y) :=
  realEq_trans (realEq_symm (realAdd_zero x))
    (realEq_trans (realAdd_congr_right x (realEq_symm (realAdd_neg y)))
      (realEq_trans (realEq_symm (realAdd_assoc x y (realNeg y)))
        (realEq_trans (realAdd_congr_left (realNeg y) h)
          (realEq_trans (realAdd_comm realZero (realNeg y))
            (realAdd_zero (realNeg y))))))

/-! ## M177-2: 逆元近似の誤差 -/

/-- **定理 (M177-2): 逆元近似の誤差** — (1⊖r)·s_k ⊖ 1 ≈ ⊖r^k。
    M168 残差 (1⊖r)·s_k ⊕ r^k ≈ 1 を移項: 誤差 ⊕ r^k を整形して
    (残差 ⊖ 1) ≈ 0 に落とし、反元特徴付け M177-1 で誤差 ≈ ⊖r^k。 -/
theorem real_geom_inv_error (r : RReal) (k : Nat) :
    realEq (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realNeg (qToReal ratRing.one)))
      (realNeg (realPow r k)) := by
  apply real_neg_of_add_eq_zero
  refine realEq_trans (realAdd_assoc
      (rmul (realAdd (qToReal ratRing.one) (realNeg r)) (realGeomSum r k))
      (realNeg (qToReal ratRing.one)) (realPow r k)) ?_
  refine realEq_trans (realAdd_congr_right
      (rmul (realAdd (qToReal ratRing.one) (realNeg r)) (realGeomSum r k))
      (realAdd_comm (realNeg (qToReal ratRing.one)) (realPow r k))) ?_
  refine realEq_trans (realEq_symm (realAdd_assoc
      (rmul (realAdd (qToReal ratRing.one) (realNeg r)) (realGeomSum r k))
      (realPow r k) (realNeg (qToReal ratRing.one)))) ?_
  refine realEq_trans (realAdd_congr_left (realNeg (qToReal ratRing.one))
      (real_geom_residual r k)) ?_
  exact realAdd_neg (qToReal ratRing.one)

/-! ## M177-3: 誤差の絶対値 -/

/-- **定理 (M177-3): 誤差の絶対値** — |(1⊖r)·s_k ⊖ 1| ≈ |r|^k。
    M177-2 で誤差 ≈ ⊖r^k、|⊖r^k| ≈ |r^k|（rabs_neg）≈ |r|^k（M169）。 -/
theorem rabs_geom_inv_error (r : RReal) (k : Nat) :
    realEq (rabs (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realNeg (qToReal ratRing.one))))
      (realPow (rabs r) k) :=
  realEq_trans (rabs_congr (real_geom_inv_error r k))
    (realEq_trans (rabs_neg (realPow r k)) (rabs_pow r k))

/-! ## M177-4: 総括 -/

/-- **M177-4a: 総括** — 実数幾何級数の逆元近似誤差データ。 -/
structure RealGeomInvData where
  /-- 反元特徴付け x ⊕ y ≈ 0 ⟹ x ≈ ⊖y。 -/
  neg_of_add_zero : ∀ {x y : RReal},
    realEq (realAdd x y) realZero → realEq x (realNeg y)
  /-- 逆元近似の誤差 (1⊖r)·s_k ⊖ 1 ≈ ⊖r^k。 -/
  inv_error : ∀ (r : RReal) (k : Nat),
    realEq (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realNeg (qToReal ratRing.one)))
      (realNeg (realPow r k))
  /-- 誤差の絶対値 |(1⊖r)·s_k ⊖ 1| ≈ |r|^k。 -/
  abs_inv_error : ∀ (r : RReal) (k : Nat),
    realEq (rabs (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realNeg (qToReal ratRing.one))))
      (realPow (rabs r) k)

/-- **M177-4b: witness**。 -/
def realGeomInvData : RealGeomInvData where
  neg_of_add_zero := fun h => real_neg_of_add_eq_zero h
  inv_error := real_geom_inv_error
  abs_inv_error := rabs_geom_inv_error

/-- **M177-4c: 存在**。 -/
theorem realGeomInv_exists : Nonempty RealGeomInvData := ⟨realGeomInvData⟩

end IUT
