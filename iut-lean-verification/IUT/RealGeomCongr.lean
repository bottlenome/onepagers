/-
# M171: 実数幾何級数の構造法則 — 比の congruence と望遠鏡増分（柱C）

M165/M168（実数幾何級数 realGeomSum の閉形式・漸化式）の続き。部分和
realGeomSum が満たす二つの構造的性質——公比 r に関する congruence
（realEq を尊重）と、隣接部分和の差が末尾項 r^k である（望遠鏡増分）
——を realEq 下で閉じる。

  * M171-1 `realGeomSum_congr` — 比の congruence:
    r ≈ r' ⟹ s_k(r) ≈ s_k(r')（realPow_congr の逐次適用）
  * M171-2 `realGeomSum_incr` — 望遠鏡増分:
    s_{k+1} ⊖ s_k ≈ r^k（隣接部分和の差 = 追加された末尾項）
  * M171-3 `RealGeomCongrData` — 総括

意義: congruence は realGeomSum が RReal/≈ 上の写像として井戸定義で
あること、望遠鏡増分は「Σ が差分の逆」であること（望遠鏡和の基礎）を
述べる。M166 の realPow_congr の級数版であり、実数の級数操作の
基本補題。

正直な限定: 収束・順序は含まない（次層）。純代数の realEq 恒等式のみ。

全て選択公理不使用。
-/
import IUT.RealGeom
import IUT.RealPow

namespace IUT

/-! ## M171-1: 比の congruence -/

/-- **定理 (M171-1): 比の congruence** — r ≈ r' なら s_k(r) ≈ s_k(r')。
    k の帰納: 0 は両辺 0（refl）、k+1 は s_k の congruence（IH）と
    末尾 r^k の congruence（M166 realPow_congr）の合成。 -/
theorem realGeomSum_congr {r r' : RReal} (h : realEq r r') :
    ∀ k, realEq (realGeomSum r k) (realGeomSum r' k) := by
  intro k
  induction k with
  | zero => exact realEq_refl realZero
  | succ k ih =>
    show realEq (realAdd (realGeomSum r k) (realPow r k))
        (realAdd (realGeomSum r' k) (realPow r' k))
    exact realEq_trans (realAdd_congr_left (realPow r k) ih)
      (realAdd_congr_right (realGeomSum r' k) (realPow_congr h k))

/-! ## M171-2: 望遠鏡増分 -/

/-- **定理 (M171-2): 望遠鏡増分** — s_{k+1} ⊖ s_k ≈ r^k。
    s_{k+1} = s_k ⊕ r^k なので (s_k ⊕ r^k) ⊖ s_k ≈ r^k
    （可換 + 結合 + s_k ⊖ s_k ≈ 0 + 0 の消去）。「Σ は差分の逆」。 -/
theorem realGeomSum_incr (r : RReal) (k : Nat) :
    realEq (realAdd (realGeomSum r (k + 1)) (realNeg (realGeomSum r k)))
      (realPow r k) := by
  show realEq (realAdd (realAdd (realGeomSum r k) (realPow r k))
      (realNeg (realGeomSum r k))) (realPow r k)
  exact realEq_trans
    (realAdd_congr_left (realNeg (realGeomSum r k))
      (realAdd_comm (realGeomSum r k) (realPow r k)))
    (realEq_trans
      (realAdd_assoc (realPow r k) (realGeomSum r k)
        (realNeg (realGeomSum r k)))
      (realEq_trans
        (realAdd_congr_right (realPow r k) (realAdd_neg (realGeomSum r k)))
        (realAdd_zero (realPow r k))))

/-! ## M171-3: 総括 -/

/-- **M171-3a: 総括** — 実数幾何級数の構造法則データ。 -/
structure RealGeomCongrData where
  /-- 比の congruence。 -/
  sum_congr : ∀ {r r' : RReal}, realEq r r' →
    ∀ k, realEq (realGeomSum r k) (realGeomSum r' k)
  /-- 望遠鏡増分 s_{k+1} ⊖ s_k ≈ r^k。 -/
  sum_incr : ∀ (r : RReal) (k : Nat),
    realEq (realAdd (realGeomSum r (k + 1)) (realNeg (realGeomSum r k)))
      (realPow r k)

/-- **M171-3b: witness**。 -/
def realGeomCongrData : RealGeomCongrData where
  sum_congr := fun h k => realGeomSum_congr h k
  sum_incr := realGeomSum_incr

/-- **M171-3c: 存在**。 -/
theorem realGeomCongr_exists : Nonempty RealGeomCongrData :=
  ⟨realGeomCongrData⟩

end IUT
