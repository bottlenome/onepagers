/-
# M172: 幾何級数と λ-adic 膜 — 部分和 ≡ 1 mod (λ^m)（柱B）

M163/M170（環の幾何級数 crGeomSum とその漸化式）と M164（膜 (λ^m) の
イデアル構造）の合流。**公比 r が膜 (λ^m) に入るとき、幾何部分和は
1 と (λ^m) を法として合同**（crGeomSum r (k+1) ≡ 1 mod (λ^m)）で
あることを、choice なしで閉じる。「1 + 位相的に小さいもの」の骨格。

  * M172-1 `isValAtLeast_ratio_mul` — r ∈ (λ^m) ⟹ r·s_k ∈ (λ^m)
    （M164 環倍閉性 + 可換）
  * M172-2 **`isValAtLeast_geomSum_sub_one`** — r ∈ (λ^m) ⟹
    s_{k+1} − 1 ∈ (λ^m)（M170 左漸化式 s_{k+1} = 1 + r·s_k で
    差が r·s_k に等しくなる）
  * M172-3 `LambdaGeomData` — 総括

意義: r が (λ^m) に入る（= r が「深さ m 以上で 0 に近い」）とき、
1 + r + r² + … + r^k は 1 と (λ^m) を法として一致する。これは局所体論
の**主単数** 1 + m·O の骨格（部分和が主単数フィルトレーションに
乗る）であり、M31（単数 filtration）・M170（幾何級数）を橋渡しする。
付値環での「1 − r で割る」操作（幾何級数による逆元近似）の第一歩。

正直な限定: 実際の逆元 (1 − r)⁻¹ の存在（∑r^i の収束・完備性）は
位相・完備化を要し次層。本層は有限部分和の合同（イデアル所属）のみ。

全て選択公理不使用。
-/
import IUT.GeomSeriesRec
import IUT.LambdaIdeal

namespace IUT

/-! ## M172-1: 比の倍は膜に留まる -/

/-- **定理 (M172-1): r·s_k ∈ (λ^m)** — r ∈ (λ^m) なら、部分和 s_k を
    掛けても膜に留まる。M164 環倍閉性（isValAtLeast_smul）+ 可換。 -/
theorem isValAtLeast_ratio_mul {R : CRing} {lam r : R.carrier} {m : Nat}
    (hr : IsValAtLeast R lam r m) (k : Nat) :
    IsValAtLeast R lam (R.mul r (crGeomSum R r k)) m := by
  rw [R.mul_comm r (crGeomSum R r k)]
  exact isValAtLeast_smul (crGeomSum R r k) hr

/-! ## M172-2: 部分和 ≡ 1 mod (λ^m) -/

/-- **定理 (M172-2): s_{k+1} − 1 ∈ (λ^m)** — r ∈ (λ^m) なら幾何部分和は
    1 と (λ^m) を法として合同。M170 左漸化式 s_{k+1} = 1 + r·s_k より
    s_{k+1} − 1 = r·s_k（(1 + X) + (−1) = X の整形）で M172-1 に帰着。 -/
theorem isValAtLeast_geomSum_sub_one {R : CRing} {lam r : R.carrier} {m : Nat}
    (hr : IsValAtLeast R lam r m) (k : Nat) :
    IsValAtLeast R lam (R.add (crGeomSum R r (k + 1)) (R.neg R.one)) m := by
  have e : R.add (crGeomSum R r (k + 1)) (R.neg R.one)
      = R.mul r (crGeomSum R r k) := by
    rw [geom_rec_left, R.add_comm R.one (R.mul r (crGeomSum R r k)),
      R.add_assoc, CRing.add_neg, CRing.add_zero]
  rw [e]
  exact isValAtLeast_ratio_mul hr k

/-! ## M172-3: 総括 -/

/-- **M172-3a: 総括** — 幾何級数の λ-adic 合同データ。 -/
structure LambdaGeomData where
  /-- r ∈ (λ^m) ⟹ r·s_k ∈ (λ^m)。 -/
  ratio_mul : ∀ (R : CRing) (lam r : R.carrier) (m : Nat),
    IsValAtLeast R lam r m → ∀ k,
    IsValAtLeast R lam (R.mul r (crGeomSum R r k)) m
  /-- r ∈ (λ^m) ⟹ s_{k+1} − 1 ∈ (λ^m)（部分和 ≡ 1 mod (λ^m)）。 -/
  geomSum_sub_one : ∀ (R : CRing) (lam r : R.carrier) (m : Nat),
    IsValAtLeast R lam r m → ∀ k,
    IsValAtLeast R lam (R.add (crGeomSum R r (k + 1)) (R.neg R.one)) m

/-- **M172-3b: witness**。 -/
def lambdaGeomData : LambdaGeomData where
  ratio_mul := fun _ _ _ _ hr k => isValAtLeast_ratio_mul hr k
  geomSum_sub_one := fun _ _ _ _ hr k => isValAtLeast_geomSum_sub_one hr k

/-- **M172-3c: 存在**。 -/
theorem lambdaGeom_exists : Nonempty LambdaGeomData := ⟨lambdaGeomData⟩

end IUT
