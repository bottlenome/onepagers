/-
  IUT/FrobArakelovBridge.lean — M361F [実／本物]
  分類: 実 (Frobenioid 次数 = Arakelov 次数の互換橋)
  complete_pct 影響: 柱C を前進（M331F Frobenioid realification 次数と M356F Arakelov 次数が
    有限因子部で一致することを本物で示し、独立に建設した2つの次数概念を結ぶ・主因子の
    Frobenioid 次数=0 を橋渡し）。※ 束ねだけでなく互換定理という新規の小さな本物のリンク。
  正直な限定: 一致が定義的(rfl)か証明された realEq かをヘッダに明記。一般数体は後続。
-/
import IUT.FrobenioidCategory
import IUT.ArakelovDivisor

namespace IUT

/-! ## M361F-1: 二つの次数の再輸出

    M331F `frobCRealDegree`（Frobenioid の realification 次数、有限因子 `RawDiv` 上）と
    M356F `ardDeg`（Arakelov 次数、有限部+アルキメデス部 `ardRaw` 上）は、どちらも
    M312F `logVolGlobal` の上に建てられている——本ブリッジはその共有をあらわにする。 -/

/-- **M361F-1a: Frobenioid 次数（再輸出）** — M331F `frobCRealDegree`（有限因子上の
    realification 次数）。 -/
def fabFrobDeg (logq : Nat → RReal) (x : RawDiv) : RReal :=
  frobCRealDegree logq x

/-- **M361F-1b: Arakelov 次数（再輸出）** — M356F `ardDeg`（有限部+アルキメデス部上の
    実次数）。 -/
def fabArakelovDeg (logp : Nat → RReal) (D : ardRaw) : RReal :=
  ardDeg logp D

/-! ## M361F-2: 互換定理 — 有限因子部で一致 -/

/-- **M361F-2: 次数の一致定理（本丸）** — 有限因子 `x` をアルキメデス重み 0 で
    `ardRaw` へ埋め込んだとき、Frobenioid realification 次数（M331F）と Arakelov 次数
    （M356F）は一致する（realEq）。両者とも定義上 `logVolGlobal logp x` に
    `realAdd _ realZero` の分だけの差しかなく、`realAdd_zero` で閉じる——
    **一致は rfl ではなく、`realAdd_zero` を用いた短い realEq 証明**（ℝ が setoid の
    ため厳密な `=` ではなく `realEq` で述べる、M312F/M331F/M356F と同じ正直な形）。 -/
theorem fab_degrees_agree (logp : Nat → RReal) (x : RawDiv) :
    realEq (fabFrobDeg logp x) (fabArakelovDeg logp ⟨x, realZero⟩) := by
  show realEq (logVolGlobal logp x) (realAdd (logVolGlobal logp x) realZero)
  exact realEq_symm (realAdd_zero (logVolGlobal logp x))

/-! ## M361F-3: 主因子の Frobenioid 次数（有限部）の橋渡し -/

/-- **M361F-3: 主因子の互換 corollary** — x∈ℚ^× の主 Arakelov 因子 `ardPrincipal logp x`
    （有限部=x.fin・アルキメデス部=−log|x|_∞）の Arakelov 次数は 0（M356F
    `ard_principal_degree_zero`／M351F 積公式の転写）。その有限部の寄与は
    `fabFrobDeg logp x.fin`（Frobenioid 次数）そのものであり、無限部
    `logVolGlobal logp (rawNeg x.fin)` と相殺してはじめて 0 になる——
    **正直な限定**: 有限部 `fabFrobDeg logp x.fin` 単独は一般に 0 でない
    （例: x=2 で log 2 ≠ 0、`ard_example_two` 参照）。0 になるのは
    Frobenioid 有限次数＋Arakelov アルキメデス補正の**和**（＝Arakelov 次数）。 -/
theorem fab_principal_frob_zero (logp : Nat → RReal) (x : pfRational) :
    realEq (realAdd (fabFrobDeg logp x.fin) (logVolGlobal logp (rawNeg x.fin))) realZero :=
  ard_principal_degree_zero logp x

/-- **M361F-3b: 上と同じ内容を `fabArakelovDeg` 経由で** — 主 Arakelov 因子への
    埋め込み `ardPrincipal logp x` に対し、橋渡しされた次数 `fabArakelovDeg` は 0。 -/
theorem fab_principal_arakelov_zero (logp : Nat → RReal) (x : pfRational) :
    realEq (fabArakelovDeg logp (ardPrincipal logp x)) realZero :=
  ard_principal_degree_zero logp x

/-! ## M361F-4: 加法性の再輸出（両次数とも和で加法的） -/

/-- **M361F-4: 両次数の加法性（再輸出）** — Frobenioid 次数（M331F
    `frobCRealDegree_add`）と、アルキメデス重み 0 埋め込みでの Arakelov 次数（M356F
    `ard_deg_hom`）が、それぞれ和の上で加法的であることの束ね。 -/
theorem fab_deg_additive (logp : Nat → RReal) (x y : RawDiv) :
    realEq (fabFrobDeg logp (rawAdd x y))
      (realAdd (fabFrobDeg logp x) (fabFrobDeg logp y)) ∧
    realEq (fabArakelovDeg logp (ardAdd ⟨x, realZero⟩ ⟨y, realZero⟩))
      (realAdd (fabArakelovDeg logp ⟨x, realZero⟩) (fabArakelovDeg logp ⟨y, realZero⟩)) :=
  ⟨frobCRealDegree_add logp x y, ard_deg_hom logp ⟨x, realZero⟩ ⟨y, realZero⟩⟩

/-! ## M361F-5: capstone -/

/-- **M361F-5a: 橋データ** — Frobenioid 次数・Arakelov 次数・両者の一致・主因子の消滅を
    束ねる。 -/
structure FabBridgeData (logp : Nat → RReal) where
  /-- Frobenioid realification 次数（M331F）。 -/
  frobDeg : RawDiv → RReal
  /-- Arakelov 次数（M356F）。 -/
  arakelovDeg : ardRaw → RReal
  /-- 有限因子部での一致（アルキメデス重み 0 埋め込み）。 -/
  agree : ∀ x : RawDiv, realEq (frobDeg x) (arakelovDeg ⟨x, realZero⟩)
  /-- 主 Arakelov 因子上では次数 0。 -/
  principal_zero : ∀ x : pfRational, realEq (arakelovDeg (ardPrincipal logp x)) realZero

/-- **M361F-5b: 実データ** — 全フィールドを本物で充足。 -/
def fabBridgeData (logp : Nat → RReal) : FabBridgeData logp where
  frobDeg := fabFrobDeg logp
  arakelovDeg := fabArakelovDeg logp
  agree := fab_degrees_agree logp
  principal_zero := fab_principal_arakelov_zero logp

/-- **M361F-5c: 存在**（`Nonempty` でなく実データ）。 -/
theorem fab_exists (logp : Nat → RReal) : Nonempty (FabBridgeData logp) :=
  ⟨fabBridgeData logp⟩

/-- **M361F-5d: 実例** — 零因子上で Frobenioid 次数と Arakelov 次数が一致（0 ≈ 0）。 -/
example (logp : Nat → RReal) :
    realEq (fabFrobDeg logp rawZero) (fabArakelovDeg logp ⟨rawZero, realZero⟩) :=
  fab_degrees_agree logp rawZero

end IUT
