/-
# M175: 幾何部分和の絶対値評価 — |Σ rⁱ| ≤ Σ |r|ⁱ（柱C）

M174（三角不等式）・M169（|r^k| = |r|^k）・M173（順序ブリッジ）の合流。
実数幾何部分和の**絶対値の比較評価** |s_k(r)| ≤ s_k(|r|)——「和の
絶対値は絶対値の和以下」を幾何級数に適用したもの——を rLe として
閉じる。絶対収束評価の雛形。

  * M175-1 **`rabs_geomSum_le`** — |Σ_{i<k} rⁱ| ≤ Σ_{i<k} |r|ⁱ
    （k の帰納 + 三角不等式 + |r^k| = |r|^k + 加法の単調性）
  * M175-2 `RealGeomAbsData` — 総括

意義: 幾何部分和 s_k(r) の絶対値が、公比の絶対値 |r| による幾何部分和
s_k(|r|) で上から押さえられる。|r| < 1 のとき右辺 s_k(|r|) は
（次層で）(1 − |r|)⁻¹ に収束し有界なので、これは s_k(r) の**絶対
一様有界性**（絶対収束）の核心の不等式。三角不等式（M174）の
帰納的適用（有限和版三角不等式の幾何級数インスタンス）でもある。

正直な限定: 実際の収束・一様有界性（s_k(|r|) の上界の存在と極限）は
順序完備性・rate-bound の次層。本層は有限 k での比較不等式のみ。

全て選択公理不使用。
-/
import IUT.RealAbsTriangle
import IUT.RealAbsPow
import IUT.RealGeom

namespace IUT

/-! ## M175-1: 幾何部分和の絶対値評価 -/

/-- **定理 (M175-1): |Σ rⁱ| ≤ Σ |r|ⁱ** — 幾何部分和の絶対値は、公比の
    絶対値による幾何部分和で押さえられる。k の帰納:
    0 は |0| ≈ 0 ≤ 0、k+1 は
    |s_k ⊕ r^k| ≤ |s_k| ⊕ |r^k|（三角不等式 M174）
    ≤ s_k(|r|) ⊕ |r^k|（IH + 加法単調性 rLe_add）
    ≈ s_k(|r|) ⊕ |r|^k（|r^k| = |r|^k, M169）= s_{k+1}(|r|)。 -/
theorem rabs_geomSum_le (r : RReal) :
    ∀ k, rLe (rabs (realGeomSum r k)) (realGeomSum (rabs r) k) := by
  intro k
  induction k with
  | zero =>
    show rLe (rabs realZero) realZero
    exact rLe_of_realEq rabs_zero
  | succ k ih =>
    show rLe (rabs (realAdd (realGeomSum r k) (realPow r k)))
        (realAdd (realGeomSum (rabs r) k) (realPow (rabs r) k))
    exact rLe_trans (rabs_triangle (realGeomSum r k) (realPow r k))
      (rLe_trans (rLe_add (rabs (realPow r k)) ih)
        (rLe_of_realEq (realAdd_congr_right (realGeomSum (rabs r) k)
          (rabs_pow r k))))

/-! ## M175-2: 総括 -/

/-- **M175-2a: 総括** — 幾何部分和の絶対値評価データ。 -/
structure RealGeomAbsData where
  /-- |Σ rⁱ| ≤ Σ |r|ⁱ。 -/
  geomSum_abs_le : ∀ (r : RReal) (k : Nat),
    rLe (rabs (realGeomSum r k)) (realGeomSum (rabs r) k)

/-- **M175-2b: witness**。 -/
def realGeomAbsData : RealGeomAbsData where
  geomSum_abs_le := rabs_geomSum_le

/-- **M175-2c: 存在**。 -/
theorem realGeomAbs_exists : Nonempty RealGeomAbsData := ⟨realGeomAbsData⟩

end IUT
