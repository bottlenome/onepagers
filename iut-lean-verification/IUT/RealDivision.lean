/-
# M162: 除算代数 — 逆元の一意性・congruence・積の逆元（柱C）

M153F（apart 一般の逆元存在 `apart_inv_exists`）の正直申告
「逆元の一意性・除算の代数法則は次層」を解消する。自前 ℝ の乗法逆元
関係（realEq の下での x·y ≈ 1）が**体の除算法則**を満たすことを、
rate-bound を一切使わず既存の realEq 乗法代数（M123F 可換 + M150 結合
+ congruence）だけで閉じる。

  * M162-1 **`rinv_unique`（本丸1）** — 逆元の一意性:
    x·y ≈ 1 ∧ x·y' ≈ 1 ⟹ y ≈ y'。
    y ≈ y·1 ≈ y·(x·y') ≈ (y·x)·y' ≈ (x·y)·y' ≈ 1·y' ≈ y' の連鎖
  * M162-2 `rinv_congr` — 逆元の congruence:
    x ≈ x' ∧ x·y ≈ 1 ⟹ x'·y ≈ 1（底の付け替え）
  * M162-3 `rmul_mul_mul_comm` — 実数版中央四項入替
    (x·y)·(a·b) ≈ (x·a)·(y·b)（結合 + 可換 + congruence の連鎖）
  * M162-4 **`rmul_inv_mul`（本丸2）** — 積の逆元:
    x·a ≈ 1 ∧ y·b ≈ 1 ⟹ (x·y)·(a·b) ≈ 1。
    すなわち (xy)⁻¹ ≈ x⁻¹·y⁻¹（逆元関係のレベルでの定式化）
  * M162-5 `apart_inv_unique` — apart な x の逆元は一意
    （M153F `apart_inv_exists` × M162-1）
  * M162-6 `RealDivisionData` — 総括

意義: M153F は「apart なら逆元が存在する」を与えた。本層はその逆元が
**一意**であり、底の realEq に関して **congruent** であり、積の逆元が
**逆元の積**であることを示す。逆元関数を（choice で）取り出さずに、
逆元 **関係** x·y ≈ 1 のレベルで除算代数を閉じるのが要点
（∃ から関数を作らない設計、issue §2 の Quot/∃-述語方針と同じ）。
これで自前 ℝ が（apartness 前提の下で）構成的体の乗法構造を満たす。

正直な限定: ここで扱うのは逆元「関係」の代数則であり、全域的な逆元
**関数** r⁻¹ の構成（各元へ apartness 証明を伴わせる必要がある）や、
論理的非零 ¬(x ≈ 0) からの逆元（Markov 原理相当、M153F で既に正直
申告済み）は対象外。積の逆元も入力側の逆元 a, b を与えられた前提での
関係式であり、逆元関数の準同型性そのものではない。

全て選択公理不使用。
-/
import IUT.RealRingLaws
import IUT.ApartInv

namespace IUT

/-! ## M162-1: 逆元の一意性 -/

/-- **定理 (M162-1, 本丸1): 逆元の一意性** — x·y ≈ 1 かつ x·y' ≈ 1 なら
    y ≈ y'。連鎖:
    y ≈ y·1 ≈ y·(x·y') ≈ (y·x)·y' ≈ (x·y)·y' ≈ 1·y' ≈ y'。
    M150 結合 + M123F 可換 + congruence のみ（rate-bound 不使用）。 -/
theorem rinv_unique {x y y' : RReal}
    (h1 : realEq (rmul x y) (qToReal ratRing.one))
    (h2 : realEq (rmul x y') (qToReal ratRing.one)) :
    realEq y y' :=
  realEq_trans (realEq_symm (rmul_one y))
    (realEq_trans (rmul_congr_right y (realEq_symm h2))
      (realEq_trans (realEq_symm (rmul_assoc_real y x y'))
        (realEq_trans (rmul_congr_left y' (rmul_comm y x))
          (realEq_trans (rmul_congr_left y' h1)
            (realEq_trans (rmul_comm (qToReal ratRing.one) y')
              (rmul_one y'))))))

/-! ## M162-2: 逆元の congruence -/

/-- **定理 (M162-2): 逆元の congruence** — x ≈ x' かつ x·y ≈ 1 なら
    x'·y ≈ 1。x'·y ≈ x·y ≈ 1（左 congruence + 推移）。 -/
theorem rinv_congr {x x' y : RReal} (hx : realEq x x')
    (h : realEq (rmul x y) (qToReal ratRing.one)) :
    realEq (rmul x' y) (qToReal ratRing.one) :=
  realEq_trans (rmul_congr_left y (realEq_symm hx)) h

/-! ## M162-3: 実数版中央四項入替 -/

/-- **補題 (M162-3): 中央四項入替（realEq）** —
    (x·y)·(a·b) ≈ (x·a)·(y·b)。結合 + 可換 + congruence の連鎖で
    積の逆元の並べ替えに使う。 -/
theorem rmul_mul_mul_comm (x y a b : RReal) :
    realEq (rmul (rmul x y) (rmul a b)) (rmul (rmul x a) (rmul y b)) :=
  realEq_trans (rmul_assoc_real x y (rmul a b))
    (realEq_trans (rmul_congr_right x (realEq_symm (rmul_assoc_real y a b)))
      (realEq_trans (rmul_congr_right x (rmul_congr_left b (rmul_comm y a)))
        (realEq_trans (rmul_congr_right x (rmul_assoc_real a y b))
          (realEq_symm (rmul_assoc_real x a (rmul y b))))))

/-! ## M162-4: 積の逆元 -/

/-- **定理 (M162-4, 本丸2): 積の逆元** — x·a ≈ 1 かつ y·b ≈ 1 なら
    (x·y)·(a·b) ≈ 1。すなわち a が x の、b が y の逆元なら
    a·b が x·y の逆元 = (xy)⁻¹ ≈ x⁻¹·y⁻¹。
    (x·y)·(a·b) ≈ (x·a)·(y·b) ≈ 1·(y·b) ≈ (y·b) ≈ 1。 -/
theorem rmul_inv_mul {x y a b : RReal}
    (ha : realEq (rmul x a) (qToReal ratRing.one))
    (hb : realEq (rmul y b) (qToReal ratRing.one)) :
    realEq (rmul (rmul x y) (rmul a b)) (qToReal ratRing.one) :=
  realEq_trans (rmul_mul_mul_comm x y a b)
    (realEq_trans (rmul_congr_left (rmul y b) ha)
      (realEq_trans (rmul_comm (qToReal ratRing.one) (rmul y b))
        (realEq_trans (rmul_one (rmul y b)) hb)))

/-! ## M162-5: apart な元の逆元の一意性 -/

/-- **定理 (M162-5): apart な元の逆元は一意** — IsPos |x| なら
    x·y ≈ 1 を満たす y は realEq を除いて一意。M153F の存在
    `apart_inv_exists` と M162-1 の一意性の合流。 -/
theorem apart_inv_unique {x y y' : RReal}
    (h1 : realEq (rmul x y) (qToReal ratRing.one))
    (h2 : realEq (rmul x y') (qToReal ratRing.one)) :
    realEq y y' :=
  rinv_unique h1 h2

/-! ## M162-6: 総括 -/

/-- **M162-6a: 総括** — 除算代数データ（一意性・congruence・積の逆元）。 -/
structure RealDivisionData where
  /-- 逆元の一意性。 -/
  inv_unique : ∀ {x y y' : RReal},
    realEq (rmul x y) (qToReal ratRing.one) →
    realEq (rmul x y') (qToReal ratRing.one) → realEq y y'
  /-- 逆元の congruence。 -/
  inv_congr : ∀ {x x' y : RReal}, realEq x x' →
    realEq (rmul x y) (qToReal ratRing.one) →
    realEq (rmul x' y) (qToReal ratRing.one)
  /-- 積の逆元。 -/
  inv_mul : ∀ {x y a b : RReal},
    realEq (rmul x a) (qToReal ratRing.one) →
    realEq (rmul y b) (qToReal ratRing.one) →
    realEq (rmul (rmul x y) (rmul a b)) (qToReal ratRing.one)

/-- **M162-6b: witness**。 -/
def realDivisionData : RealDivisionData where
  inv_unique := fun h1 h2 => rinv_unique h1 h2
  inv_congr := fun hx h => rinv_congr hx h
  inv_mul := fun ha hb => rmul_inv_mul ha hb

/-- **M162-6c: 存在**。 -/
theorem realDivision_exists : Nonempty RealDivisionData :=
  ⟨realDivisionData⟩

end IUT
