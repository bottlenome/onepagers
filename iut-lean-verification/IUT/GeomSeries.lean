/-
# M163: 幾何級数の代数核 — 部分和の閉形式（柱E→C 橋の入口）

ℝ 冪級数の入口（issue #48 §4 M163）のうち、**任意の可換環で成り立つ
代数的核**を先に確立する。部分和 s_k = Σ_{i<k} r^i の望遠鏡的閉形式
(1 − r)·s_k = 1 − r^k を choice なしで閉じる。

  * M163-1 `crGeomSum` — 部分和 s_k = Σ_{i<k} r^i の再帰定義
    （s_0 = 0, s_{k+1} = s_k + r^k）
  * M163-2 `crGeomSum_succ` — 一段展開 s_{k+1} = s_k + r^k（定義）
  * M163-3 `add_cancel_middle` — 相殺補題 (a + (−b)) + (b + d) = a + d
  * M163-4 **`geom_closed`（本丸）** — 望遠鏡的閉形式
    (1 − r)·s_k = 1 − r^k。k の帰納 + 分配 + 相殺
  * M163-5 `geom_closed_right` — 右版 s_k·(1 − r) = 1 − r^k（可換）
  * M163-6 `GeomSeriesData` — 総括

意義: 幾何級数は「ℝ 冪級数（テータ級数・log-volume の収束）」の
最も基本的な雛形。その**代数的骨格**（有限部分和の閉形式）は付値環
（ℤ_p・eisRing・塔）でも実数でも共通で、ここで一度証明しておけば
各具体環へ instance 化できる。とくに (1 − r)·s_k = 1 − r^k は
|r| < 1 での収束評価 s_k → (1 − r)⁻¹ の残差 r^k/(1 − r) を与える
出発点（次層）。

正直な限定: 本層は**有限部分和の恒等式のみ**。実数値 ℝ 上での収束
（rate-bound master による s_k の Cauchy 性と極限 (1 − r)⁻¹ の同定、
|r| < 1 = IsPos(1 − |r|) の仮定下）は次層（tier 高、rBound 設計を要す）。
テータ級数など具体的な級数への適用も次層。

全て選択公理不使用。
-/
import IUT.LambdaValuation

namespace IUT

/-! ## M163-1: 部分和の再帰定義 -/

/-- **M163-1: 幾何級数の部分和** — s_k = Σ_{i<k} r^i。
    s_0 = 0, s_{k+1} = s_k + r^k（末尾に r^k を足す）。 -/
def crGeomSum (R : CRing) (r : R.carrier) : Nat → R.carrier
  | 0 => R.zero
  | k + 1 => R.add (crGeomSum R r k) (rpow R r k)

/-! ## M163-2: 一段展開 -/

/-- **M163-2: 一段展開** — s_{k+1} = s_k + r^k（定義そのもの）。 -/
theorem crGeomSum_succ (R : CRing) (r : R.carrier) (k : Nat) :
    crGeomSum R r (k + 1) = R.add (crGeomSum R r k) (rpow R r k) := rfl

/-! ## M163-3: 相殺補題 -/

/-- **M163-3: 相殺補題** — (a + (−b)) + (b + d) = a + d。
    帰納段で「(1 − r^k) + (r^k + (−r^{k+1}))」を畳むのに使う
    （−b と b が中央で消える）。 -/
theorem add_cancel_middle (R : CRing) (a b d : R.carrier) :
    R.add (R.add a (R.neg b)) (R.add b d) = R.add a d := by
  rw [R.add_assoc, ← R.add_assoc (R.neg b) b d, R.neg_add, R.zero_add]

/-! ## M163-4: 本丸 — 望遠鏡的閉形式 -/

/-- **定理 (M163-4, 本丸): 幾何級数の閉形式** — (1 − r)·s_k = 1 − r^k。
    k = 0 は両辺 0（mul_zero・add_neg）。k+1 は分配で
    (1 − r)·(s_k + r^k) = (1 − r)·s_k + (1 − r)·r^k、
    IH で第一項 = 1 − r^k、第二項 = r^k − r^{k+1}（right_distrib +
    one_mul + neg_mul + comm）、相殺補題で 1 − r^{k+1} に畳む。 -/
theorem geom_closed (R : CRing) (r : R.carrier) (k : Nat) :
    R.mul (R.add R.one (R.neg r)) (crGeomSum R r k)
      = R.add R.one (R.neg (rpow R r k)) := by
  induction k with
  | zero =>
    show R.mul (R.add R.one (R.neg r)) R.zero = R.add R.one (R.neg R.one)
    rw [CRing.mul_zero, CRing.add_neg]
  | succ k ih =>
    show R.mul (R.add R.one (R.neg r)) (R.add (crGeomSum R r k) (rpow R r k))
        = R.add R.one (R.neg (R.mul (rpow R r k) r))
    have hmid : R.mul (R.add R.one (R.neg r)) (rpow R r k)
        = R.add (rpow R r k) (R.neg (R.mul (rpow R r k) r)) := by
      rw [CRing.right_distrib, R.one_mul, CRing.neg_mul, R.mul_comm r (rpow R r k)]
    rw [R.left_distrib, ih, hmid]
    exact add_cancel_middle R R.one (rpow R r k) (R.neg (R.mul (rpow R r k) r))

/-! ## M163-5: 右版 -/

/-- **定理 (M163-5): 右版閉形式** — s_k·(1 − r) = 1 − r^k（可換で右へ）。 -/
theorem geom_closed_right (R : CRing) (r : R.carrier) (k : Nat) :
    R.mul (crGeomSum R r k) (R.add R.one (R.neg r))
      = R.add R.one (R.neg (rpow R r k)) := by
  rw [R.mul_comm (crGeomSum R r k) (R.add R.one (R.neg r))]
  exact geom_closed R r k

/-! ## M163-6: 総括 -/

/-- **M163-6a: 総括** — 幾何級数の代数核データ（一段展開・閉形式）。 -/
structure GeomSeriesData where
  /-- 一段展開 s_{k+1} = s_k + r^k。 -/
  succ : ∀ (R : CRing) (r : R.carrier) (k : Nat),
    crGeomSum R r (k + 1) = R.add (crGeomSum R r k) (rpow R r k)
  /-- 望遠鏡的閉形式 (1 − r)·s_k = 1 − r^k。 -/
  closed : ∀ (R : CRing) (r : R.carrier) (k : Nat),
    R.mul (R.add R.one (R.neg r)) (crGeomSum R r k)
      = R.add R.one (R.neg (rpow R r k))

/-- **M163-6b: witness**。 -/
def geomSeriesData : GeomSeriesData where
  succ := crGeomSum_succ
  closed := geom_closed

/-- **M163-6c: 存在**。 -/
theorem geomSeries_exists : Nonempty GeomSeriesData := ⟨geomSeriesData⟩

end IUT
