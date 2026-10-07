/-
  IUT/PadicGeometric.lean — M114F: 主単数の幾何級数逆元 — (1+πd)⁻¹ = Σ (−πd)ⁿ

  M107F/M110F が実構成した p 進級数和 zpSeriesSum を使い、
  **主単数 1 + πd が ℤ_p の単元である**ことを choice なしで証明する。
  逆元は幾何級数 Σₙ πⁿ·(−d)ⁿ = Σₙ (−πd)ⁿ の実構成（zpSeriesSum）。

  鍵となる計算: S := Σₙ πⁿ(−d)ⁿ とおくと、頭出し分解（zpSeriesSum_head）
  とスカラー倍（zpSeriesSum_smul）から自己言及等式 S = 1 + π(−d)·S、
  すなわち S = 1 − (πd)·S が従う。よって
  (1 + πd)·S = S + (πd)·S = (1 − (πd)·S) + (πd)·S = 1。

  * M114F-1 `geomSeq` / `geomSeq_zero` / `geomSeq_succ` — 幾何級数の
    係数列 (−d)ⁿ（rpow による定義とその展開）
  * M114F-2 `principalUnitInv` — 逆元候補 S = Σₙ πⁿ(−d)ⁿ の実構成
  * M114F-3 `geomSeq_shift` / `principalUnitInv_shift` — シフト級数の
    スカラー化: Σ (geomSeq∘succ) = (−d)·S（funext + mul_comm +
    zpSeriesSum_smul）
  * M114F-4 `principalUnitInv_eq` — **自己言及等式** S = 1 + (π·(−d))·S
    （zpSeriesSum_head の一段適用 + mul_assoc）
  * M114F-5 `principal_unit_mul_inv` — **本丸: (1+πd)·S = 1**
    （right_distrib + mul_neg/neg_mul + add_assoc + neg_add の簿記）
  * M114F-6 `principal_unit_is_unit` — 系: 主単数 1+πd は単元（∃ 逆元）
  * M114F-7 `PadicGeometricData` / `padicGeometricData` /
    `padicGeometric_exists` — 総括レコード（inv・is_unit を束ねた witness）

  意義: ℤ_p^× = μ_{p−1} × (1+pℤ_p) の主単数側の単元性。M107 の
  u = ω(a)·(1+πd) 分解と合わせて単元群の完全記述に接近。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.PadicSeries2

namespace IUT

/-! ## 幾何級数の係数列 (−d)ⁿ -/

/-- **M114F-1a: 幾何級数の係数列** geomSeq p d n = (−d)ⁿ
    （zpRing の rpow による）。 -/
def geomSeq (p : Nat) (d : (Zp p).carrier) : Nat → (Zp p).carrier :=
  fun n => rpow (zpRing p) ((zpRing p).neg d) n

/-- **M114F-1b: 0 次項は 1**（rpow の 0 段、rfl）。 -/
theorem geomSeq_zero (p : Nat) (d : (Zp p).carrier) :
    geomSeq p d 0 = (zpRing p).one := rfl

/-- **M114F-1c: succ 展開** (−d)^{n+1} = (−d)ⁿ·(−d)（rpow の定義、rfl）。 -/
theorem geomSeq_succ (p : Nat) (d : (Zp p).carrier) (n : Nat) :
    geomSeq p d (n + 1) = (zpRing p).mul (geomSeq p d n) ((zpRing p).neg d) :=
  rfl

/-! ## 逆元候補の実構成 -/

/-- **M114F-2: 逆元候補** S = Σₙ πⁿ·(−d)ⁿ（zpSeriesSum による実構成、
    choice 不使用）。 -/
def principalUnitInv (p : Nat) (hp : 2 ≤ p) (d : (Zp p).carrier) :
    (Zp p).carrier :=
  zpSeriesSum p hp (geomSeq p d)

/-! ## シフト級数のスカラー化 -/

/-- **M114F-3a: 係数列のシフト** — (−d)^{n+1} = (−d)·(−d)ⁿ を関数の
    等式として（funext + geomSeq_succ + mul_comm）。 -/
theorem geomSeq_shift (p : Nat) (d : (Zp p).carrier) :
    (fun n => geomSeq p d (n + 1))
      = fun n => zpMul p ((zpRing p).neg d) (geomSeq p d n) := by
  funext n
  rw [geomSeq_succ p d n]
  exact (zpRing p).mul_comm (geomSeq p d n) ((zpRing p).neg d)

/-- **M114F-3b: シフト級数のスカラー化** — Σ (geomSeq∘succ) = (−d)·S
    （M114F-3a を congrArg で級数に持ち上げ、zpSeriesSum_smul の逆向き）。 -/
theorem principalUnitInv_shift (p : Nat) (hp : 2 ≤ p) (d : (Zp p).carrier) :
    zpSeriesSum p hp (fun n => geomSeq p d (n + 1))
      = zpMul p ((zpRing p).neg d) (zpSeriesSum p hp (geomSeq p d)) := by
  rw [congrArg (zpSeriesSum p hp) (geomSeq_shift p d)]
  exact (zpSeriesSum_smul p hp ((zpRing p).neg d) (geomSeq p d)).symm

/-! ## 自己言及等式 -/

/-- **定理 (M114F-4): 自己言及等式** — S = 1 + (π·(−d))·S。
    zpSeriesSum_head（頭出し分解）に M114F-3b（シフト級数のスカラー化）を
    代入し、mul_assoc で π·((−d)·S) = (π·(−d))·S に組み直す。 -/
theorem principalUnitInv_eq (p : Nat) (hp : 2 ≤ p) (d : (Zp p).carrier) :
    principalUnitInv p hp d
      = (zpRing p).add (zpRing p).one
        ((zpRing p).mul
          ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ((zpRing p).neg d))
          (principalUnitInv p hp d)) := by
  have hhead := zpSeriesSum_head p hp (geomSeq p d)
  rw [principalUnitInv_shift p hp d] at hhead
  have hassoc : zpMul p ((toZp p).map ((p : Nat) : Int))
      (zpMul p ((zpRing p).neg d) (zpSeriesSum p hp (geomSeq p d)))
      = (zpRing p).mul
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ((zpRing p).neg d))
        (zpSeriesSum p hp (geomSeq p d)) :=
    ((zpRing p).mul_assoc ((toZp p).map ((p : Nat) : Int)) ((zpRing p).neg d)
      (zpSeriesSum p hp (geomSeq p d))).symm
  rw [hassoc, geomSeq_zero p d] at hhead
  exact hhead

/-! ## 本丸: 主単数の単元性 -/

/-- **定理 (M114F-5): (1 + πd)·S = 1** — 主単数 1+πd に逆元候補 S を
    掛けると 1。計算: (1+πd)·S = 1·S + (πd)·S = S + (πd)·S（right_distrib +
    one_mul）。M114F-4 と mul_neg/neg_mul から S = 1 + (−((πd)·S)) なので
    S + (πd)·S = 1 + ((−((πd)·S)) + (πd)·S) = 1 + 0 = 1
    （add_assoc + neg_add + add_zero）。 -/
theorem principal_unit_mul_inv (p : Nat) (hp : 2 ≤ p) (d : (Zp p).carrier) :
    (zpRing p).mul
      ((zpRing p).add (zpRing p).one
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d))
      (principalUnitInv p hp d) = (zpRing p).one := by
  -- S = 1 + (π·(−d))·S を S = 1 + (−((πd)·S)) に整形
  have hS := principalUnitInv_eq p hp d
  have hneg : (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ((zpRing p).neg d)
      = (zpRing p).neg ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d) :=
    CRing.mul_neg (zpRing p) ((toZp p).map ((p : Nat) : Int)) d
  rw [hneg] at hS
  have hnegmul : (zpRing p).mul
      ((zpRing p).neg ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d))
      (principalUnitInv p hp d)
      = (zpRing p).neg ((zpRing p).mul
          ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d)
          (principalUnitInv p hp d)) :=
    CRing.neg_mul (zpRing p) ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d)
      (principalUnitInv p hp d)
  rw [hnegmul] at hS
  -- hS : S = 1 + (−((πd)·S))
  -- 左辺を分配: (1+πd)·S = 1·S + (πd)·S = S + (πd)·S
  have hdist : (zpRing p).mul
      ((zpRing p).add (zpRing p).one
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d))
      (principalUnitInv p hp d)
      = (zpRing p).add
        ((zpRing p).mul (zpRing p).one (principalUnitInv p hp d))
        ((zpRing p).mul ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d)
          (principalUnitInv p hp d)) :=
    CRing.right_distrib (zpRing p) (zpRing p).one
      ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d)
      (principalUnitInv p hp d)
  rw [hdist, (zpRing p).one_mul (principalUnitInv p hp d)]
  -- ゴール: S + (πd)·S = 1。最初の S だけを hS で置換（congrArg で片側指定）
  have hsubst : (zpRing p).add (principalUnitInv p hp d)
      ((zpRing p).mul ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d)
        (principalUnitInv p hp d))
      = (zpRing p).add
        ((zpRing p).add (zpRing p).one
          ((zpRing p).neg ((zpRing p).mul
            ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d)
            (principalUnitInv p hp d))))
        ((zpRing p).mul ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d)
          (principalUnitInv p hp d)) :=
    congrArg (fun x => (zpRing p).add x
      ((zpRing p).mul ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d)
        (principalUnitInv p hp d))) hS
  rw [hsubst, (zpRing p).add_assoc, (zpRing p).neg_add]
  exact CRing.add_zero (zpRing p) (zpRing p).one

/-! ## 系: 単元性 -/

/-- **定理 (M114F-6): 主単数は単元** — 1 + πd に対し右逆元が存在する
    （witness = principalUnitInv、choice 不使用の実構成）。 -/
theorem principal_unit_is_unit (p : Nat) (hp : 2 ≤ p) (d : (Zp p).carrier) :
    ∃ e, (zpRing p).mul
      ((zpRing p).add (zpRing p).one
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d))
      e = (zpRing p).one :=
  ⟨principalUnitInv p hp d, principal_unit_mul_inv p hp d⟩

/-! ## 総括レコード -/

/-- **定理 (M114F-7a): 主単数幾何級数逆元のインターフェース** —
    逆元の等式（inv）と単元性（is_unit）を束ねた構造。
    ℤ_p^× = μ_{p−1} × (1+pℤ_p) の主単数側の単元性を供給する。 -/
structure PadicGeometricData (p : Nat) (hp : 2 ≤ p) where
  inv : ∀ d : (Zp p).carrier,
    (zpRing p).mul
      ((zpRing p).add (zpRing p).one
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d))
      (principalUnitInv p hp d) = (zpRing p).one
  is_unit : ∀ d : (Zp p).carrier,
    ∃ e, (zpRing p).mul
      ((zpRing p).add (zpRing p).one
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) d))
      e = (zpRing p).one

/-- **定理 (M114F-7b): witness** — principalUnitInv が
    PadicGeometricData を完全証明で充足する（choice 不使用）。 -/
def padicGeometricData (p : Nat) (hp : 2 ≤ p) : PadicGeometricData p hp where
  inv := principal_unit_mul_inv p hp
  is_unit := principal_unit_is_unit p hp

/-- **定理 (M114F-7c)**: PadicGeometricData は充足可能（witness 存在）。 -/
theorem padicGeometric_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (PadicGeometricData p hp) :=
  ⟨padicGeometricData p hp⟩

end IUT
