/-
  IUT/MuP1Cyclic.lean — M192F: μ_{p−1} ≅ (ℤ/p)^× の巡回性同定 — 総括カプストーン（柱B B-3・並行部品）

  柱B の B-3「μ_{p−1} ≅ (ℤ/p)^× の巡回性同定」は、既に三層で完全に
  閉じている:
    * M101（MuUnits）      … 互いに逆な群準同型対 μ_{p−1} ≅ (ℤ/p)^×
    * M103（PrimitiveRoot）… 原始根の存在（位数 p−1 の単数 g）
    * M104（CyclicUnits）  … 被覆（全単数が g の冪）と μ 側への移送
  本モジュールはこれら三層を **一枚のカプストーン `MuP1CyclicData`** に
  束ね、B-3 の帰結を「対応する生成元の組 g ↔ ω̄(g)」の言葉で明示的に
  読める形に整える。新規の数学的入力は無く、既証明の合流・整流のみ。

  カプストーンが束ねる内容:
    1. (ℤ/p)^× 側の原始根 g（位数 = p−1）
    2. μ_{p−1} 側の対応生成元 ω̄(g)（= teichBar g、μ に属す）
    3. μ 側の巡回性 = 被覆（全 μ-root は ω̄(g) の冪 ≤ p−2）と
       冪の相異性（0..p−2 の p−1 個が相異なる ⇒ 位数 = p−1 = |μ_{p−1}|）
    4. (ℤ/p)^× 側の同内容（被覆・相異性）
    5. 群同型 μ_{p−1} ≅ (ℤ/p)^×（M101 の MuUnitsIsoData）

  * M192F-1 `MuP1CyclicData` — 総括レコード（生成元の組・両側の巡回性・
    同型を一括）
  * M192F-2 `muP1CyclicData` — witness（原始根 g を与えると全フィールドが
    既証明で埋まる純構成）
  * M192F-3 `muP1Cyclic_exists` — B-3 の総括存在定理
    `Nonempty (MuP1CyclicData p hp)`（原始根の存在 M103-7 でラップ）

  **意義**: B-3 の三層（同型・原始根・被覆）の結論を、対応する生成元の
  組 g ↔ ω̄(g) と両側の「p−1 個の相異なる冪による枚挙」という単一の
  データ構造に統合する。μ_{p−1}（Teichmüller 代表・剰余体単数群の巡回
  部分）の巡回性が (ℤ/p)^× の巡回性と生成元レベルで同定されることを、
  下流（O^× = μ × U^(1) の直積分解、Frobenius 作用の記述）が引ける
  単一 API として供給する。

  **正直な限定**: 本モジュールは新規証明を持たず、既存の M101/M103/M104
  の合流のみを行う純カプストーンである。巡回性は「生成元 ω̄(g) の冪
  {0,…,p−2} が μ_{p−1} を過不足なく枚挙する」（被覆 mu_covers ＋ 相異性
  mu_distinct）として表現しており、有限集合の基数 |μ_{p−1}| = p−1 を
  Finset・Fintype 等の基数概念で述べてはいない（本プロジェクトは
  mathlib 非依存で基数 API を持たないため、枚挙＋相異性で位数 p−1 を
  代替表現する）。同型は群準同型対＋左右の逆元法則（MuUnitsIsoData）で
  与えており、Grp の圏論的 Iso 型としては包んでいない。これらは表現上の
  限定であり、B-3 の数学的内容（μ_{p−1} ≅ (ℤ/p)^× が位数 p−1 の巡回群）
  は完全に閉じている。

  全て選択公理不使用。
-/
import IUT.CyclicUnits

namespace IUT

/-! ## 総括レコード -/

/-- **M192F-1: B-3 総括カプストーン** — μ_{p−1} ≅ (ℤ/p)^× の巡回性同定を
    「対応する生成元の組 gU ↔ ω̄(gU) と両側の枚挙・同型」として一括保持
    する純レコード。 -/
structure MuP1CyclicData (p : Nat) (hp : IsPrime p) where
  /-- (ℤ/p)^× 側の原始根（位数 p−1 の単数）。 -/
  gU : (zmod (p ^ 1)).carrier
  /-- gU は単数。 -/
  gU_unit : IsZmodUnit p gU
  /-- gU の位数はちょうど p−1（原始根）。 -/
  gU_ord : zmodOrd p gU = p - 1
  /-- μ_{p−1} 側の対応生成元。 -/
  gMu : (Zp p).carrier
  /-- 対応関係: gMu = ω̄(gU)（Teichmüller 持ち上げ）。 -/
  gMu_teich : gMu = teichBar p hp gU
  /-- gMu は μ_{p−1} に属す（1 の (p−1) 乗根）。 -/
  gMu_root : IsMuRoot p gMu
  /-- μ 側の被覆（巡回性）: 全ての μ-root は gMu の冪 g^k（k ≤ p−2）。 -/
  mu_covers : ∀ y, IsMuRoot p y → ∃ k, k ≤ p - 2 ∧ zpPow p gMu k = y
  /-- μ 側の冪の相異性: gMu^0, …, gMu^{p−2} は相異なる（位数 = p−1、
      すなわち枚挙が p−1 個の相異なる元を与える＝|μ_{p−1}| = p−1）。 -/
  mu_distinct : ∀ i j, i < j → j ≤ p - 2 → zpPow p gMu i ≠ zpPow p gMu j
  /-- (ℤ/p)^× 側の被覆（巡回性）。 -/
  units_covers : ∀ c, IsZmodUnit p c →
    ∃ k, k ≤ p - 2 ∧ zmodPow (p ^ 1) gU k = c
  /-- (ℤ/p)^× 側の冪の相異性。 -/
  units_distinct : ∀ i j, i < j → j ≤ p - 2 →
    zmodPow (p ^ 1) gU i ≠ zmodPow (p ^ 1) gU j
  /-- 群同型 μ_{p−1} ≅ (ℤ/p)^×（M101 の互いに逆な準同型対）。 -/
  iso : MuUnitsIsoData p hp

/-! ## witness の構成 -/

/-- **M192F-2: witness** — 原始根 g（位数 p−1 の単数）を与えると、全
    フィールドが既証明（M101/M103/M104）で埋まる純構成。μ 側生成元は
    ω̄(g)、被覆は M104-3/M104-5、相異性は M102-8/M104-5a、同型は M101-10。 -/
def muP1CyclicData (p : Nat) (hp : IsPrime p)
    (g : (zmod (p ^ 1)).carrier) (hg : IsZmodUnit p g)
    (hord : zmodOrd p g = p - 1) : MuP1CyclicData p hp where
  gU := g
  gU_unit := hg
  gU_ord := hord
  gMu := teichBar p hp g
  gMu_teich := rfl
  gMu_root := isMuRoot_teichBar p hp hg
  mu_covers := by
    intro y hy
    have hyu : IsZmodUnit p (y.val 1) := isZmodUnit_of_muRoot p hp hy
    obtain ⟨k, hk, hgk⟩ := generator_covers p hp hg hord (y.val 1) hyu
    refine ⟨k, hk, ?_⟩
    rw [← teichBar_pow, hgk]
    exact teichBar_of_muRoot p hp hy
  mu_distinct := by
    intro i j hij hj heq
    have hj' : j < zmodOrd p g := by rw [hord]; have := hp.1; omega
    exact mu_powers_distinct p hp hg hij hj' heq
  units_covers := generator_covers p hp hg hord
  units_distinct := by
    intro i j hij hj heq
    have hj' : j < zmodOrd p g := by rw [hord]; have := hp.1; omega
    exact zmodOrd_powers_distinct p hp hg i j hij hj' heq
  iso := muUnitsIsoData p hp

/-! ## B-3 の総括存在定理 -/

/-- **M192F-3: B-3 総括存在定理** — μ_{p−1} ≅ (ℤ/p)^× の巡回性同定
    カプストーンが存在する。原始根の存在（M103-7）を witness に渡す
    だけ。B-3 の三層の結論を単一の Nonempty に集約する最終形。 -/
theorem muP1Cyclic_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (MuP1CyclicData p hp) := by
  obtain ⟨g, hg, hord⟩ := primitive_root_exists p hp
  exact ⟨muP1CyclicData p hp g hg hord⟩

end IUT
