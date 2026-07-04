/-
# M170: 幾何級数（環）の漸化式と残差恒等式（柱C）

M163（任意可換環での幾何級数の閉形式 (1 − r)·s_k = 1 − r^k）の続き。
M168 が実数版で与えた漸化式・残差を、**環の厳密等式版**として補い、
環レベルの幾何級数 API を完成させる。

  * M170-1 **`geom_rec_left`** — 左漸化式 s_{k+1} = 1 + r·s_k
    （s_{k+1} = 1 + r + … + r^k = 1 + r·(1 + … + r^{k-1})）
  * M170-2 **`geom_residual`** — 残差恒等式 (1 − r)·s_k + r^k = 1
    （閉形式 M163 の移項形）
  * M170-3 `GeomSeriesRecData` — 総括

意義: M163 の閉形式と併せ、環の幾何級数が満たす標準的な三恒等式
（部分和の一段展開・左漸化式・(1−r) 倍の望遠鏡）が出揃う。付値環
（ℤ_p・eisRing・塔）での級数計算の代数的下地。実数版（M168）と対に
なり、環・実数の双方で同じ API が使える。

正直な限定: 収束は環では意味を持たない（位相・順序が要る）。実数版の
収束は M168 と同じく次層。本層は純代数の恒等式のみ。

全て選択公理不使用。
-/
import IUT.GeomSeries

namespace IUT

/-! ## M170-1: 左漸化式 -/

/-- **定理 (M170-1): 左漸化式** — s_{k+1} = 1 + r·s_k。
    k の帰納。succ 段は両辺を 1 + (r·s_k + r^{k+1}) に寄せる:
    左辺は IH を第一成分に入れ結合、右辺は s_{k+1} の展開 + 左分配 +
    r·r^k = r^k·r。 -/
theorem geom_rec_left (R : CRing) (r : R.carrier) (k : Nat) :
    crGeomSum R r (k + 1) = R.add R.one (R.mul r (crGeomSum R r k)) := by
  induction k with
  | zero =>
    show R.add R.zero R.one = R.add R.one (R.mul r R.zero)
    rw [R.zero_add, CRing.mul_zero, CRing.add_zero]
  | succ k ih =>
    show R.add (crGeomSum R r (k + 1)) (rpow R r (k + 1))
        = R.add R.one (R.mul r (crGeomSum R r (k + 1)))
    have hL : R.add (crGeomSum R r (k + 1)) (rpow R r (k + 1))
        = R.add R.one (R.add (R.mul r (crGeomSum R r k)) (rpow R r (k + 1))) := by
      rw [ih, R.add_assoc]
    have hR : R.add R.one (R.mul r (crGeomSum R r (k + 1)))
        = R.add R.one (R.add (R.mul r (crGeomSum R r k)) (rpow R r (k + 1))) := by
      show R.add R.one (R.mul r (R.add (crGeomSum R r k) (rpow R r k)))
          = R.add R.one (R.add (R.mul r (crGeomSum R r k)) (R.mul (rpow R r k) r))
      rw [R.left_distrib, R.mul_comm r (rpow R r k)]
    rw [hL, hR]

/-! ## M170-2: 残差恒等式 -/

/-- **定理 (M170-2): 残差恒等式** — (1 − r)·s_k + r^k = 1。
    閉形式 M163（(1 − r)·s_k = 1 − r^k）を代入し、
    (1 + (−r^k)) + r^k = 1 + ((−r^k) + r^k) = 1 + 0 = 1
    （add_assoc + neg_add + add_zero）。 -/
theorem geom_residual (R : CRing) (r : R.carrier) (k : Nat) :
    R.add (R.mul (R.add R.one (R.neg r)) (crGeomSum R r k)) (rpow R r k)
      = R.one := by
  rw [geom_closed, R.add_assoc, R.neg_add, CRing.add_zero]

/-! ## M170-3: 総括 -/

/-- **M170-3a: 総括** — 環の幾何級数の漸化式・残差データ。 -/
structure GeomSeriesRecData where
  /-- 左漸化式 s_{k+1} = 1 + r·s_k。 -/
  rec_left : ∀ (R : CRing) (r : R.carrier) (k : Nat),
    crGeomSum R r (k + 1) = R.add R.one (R.mul r (crGeomSum R r k))
  /-- 残差恒等式 (1 − r)·s_k + r^k = 1。 -/
  residual : ∀ (R : CRing) (r : R.carrier) (k : Nat),
    R.add (R.mul (R.add R.one (R.neg r)) (crGeomSum R r k)) (rpow R r k)
      = R.one

/-- **M170-3b: witness**。 -/
def geomSeriesRecData : GeomSeriesRecData where
  rec_left := geom_rec_left
  residual := geom_residual

/-- **M170-3c: 存在**。 -/
theorem geomSeriesRec_exists : Nonempty GeomSeriesRecData := ⟨geomSeriesRecData⟩

end IUT
