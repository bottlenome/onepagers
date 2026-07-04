/-
  IUT/FormalEndRing.lean — M208F: End(F) の環パッケージング
  （柱B B-4・並行部品 — issue #36）

  M76（`FormalGroupOModule`）は a ↦ [a] := ltSol p hp a が
  形式 ℤ_p-加群をなすことを、M100（`FormalGroupEndRing`）は End(F) の像
  {[a]} が形式群加法 ⊕ = ps21Comp F と合成 ⊙ = psComp のもとで
  **可換環の全公理を満たす**ことを機械検証し、それを**専用レコード**
  `LTEndRingData`（ι : ℤ_p → End(F) の単射準同型 + 全公理）に束ねた。

  しかし M100 のパッケージは `Ring.lean`（M38）が用意した**汎用の
  環インターフェース `CRing` / `RingHom` そのものを実体化していない**
  ——公理は `ltSol` に関する等式命題として証明されているが、
  「End(F) を一個の `CRing` オブジェクトとして構成し、a ↦ [a] を
  一個の `RingHom` として与える」圏論的パッケージングは未完だった。
  本モジュール M208F がその穴を埋める。

  **設計**: End(F) の担体を**実際の自己準同型級数の集合**
  `{ g : PS // ∃ a, g = [a] }`（= Lubin–Tate 像）として取り、
  加法 ⊕ = ps21Comp F・乗法 ⊙ = psComp・**負元 ⊖g := [−1] ∘ g**
  （選択公理を使わず級数演算だけで全域に定義）・零 = 0 級数・単位 = X で
  `CRing` を構成する。各環公理は M100 の像上の補題へ Subtype.ext で還元。
  次に ι : a ↦ ⟨[a], _⟩ を**本物の `RingHom (zpRing p) formalEndRing`**
  として与え、単射性（`ltSol_injective`）と**全射性**（担体の定義から
  すべての元が [a] の形）を証明する。すなわち ι は**環同型**
  ℤ_p ≅ End(F)（Lubin–Tate の主定理の環版）を実体化する。

  * M208F-1 `cring_add_neg` / `cring_zero_mul` / `cring_neg_one_mul` —
    汎用 CRing 補題（a+(−a)=0・0·a=0・(−1)·a=−a）。負元定義の閉性に使用
  * M208F-2 `formalEndRing` — **End(F) を `CRing` として構成**
    （担体 = 自己準同型級数、⊕/⊙/⊖/0級数/X）
  * M208F-3 `oToEnd` — **ι : ℤ_p → End(F) を `RingHom` として構成**
  * M208F-4 `oToEnd_injective` / `oToEnd_surjective` — ι は全単射
    （= 環同型 ℤ_p ≅ End(F)）
  * M208F-5 `FormalEndRingData` / `formalEndRingData` /
    `formalEndRing_exists` — 総括 witness（環・準同型・全単射を一括束ね）

  **意義**: M100 が「像の上で環公理が成り立つ」ことを証明したのに対し、
  M208F は「End(F) が汎用インターフェース `CRing` の実体であり、
  a ↦ [a] が汎用 `RingHom` の実体で、しかも全単射（環同型）」である
  ことを構成する。M100 の専用レコードから**標準ライブラリの環概念への
  橋渡し**（圏論的パッケージング）が本モジュールの追加分である。

  **正直な限定**: 閉じるのは Lubin–Tate 像 = End(F)（主定理により
  ℤ_p ≅ End(F)）の上の**可換**環構造である。[a] の F-準同型性
  [a](F(X,Y)) = F([a]X,[a]Y)（M76F と同じく別項目）、および形式群の
  自己準同型「全体」が像で尽くされること（Lubin–Tate 全射性そのもの）は
  本モジュールの対象外——担体を像そのものと定義しているため、
  formalEndRing は「像としての End(F)」であって、独立に定義された
  自己準同型のなす環との一致は前提（M100 の申告を継承）。
  可換性は LT 像特有（一般の End は非可換）であることも M100 と同じ。
  全て選択公理不使用（継承する Classical はゼロ）。
-/
import IUT.FormalGroupEndRing

namespace IUT

/-! ## 汎用 CRing 補題（負元の全域定義に使用） -/

/-- **M208F-1a: a + (−a) = 0**（加法可換 + 左逆元）。 -/
theorem cring_add_neg (R : CRing) (a : R.carrier) :
    R.add a (R.neg a) = R.zero := by
  rw [R.add_comm]
  exact R.neg_add a

/-- **M208F-1b: 0 · a = 0**（可換性で `mul_zero` に還元）。 -/
theorem cring_zero_mul (R : CRing) (a : R.carrier) :
    R.mul R.zero a = R.zero := by
  rw [R.mul_comm]
  exact R.mul_zero a

/-- **M208F-1c: (−1) · a = −a**（分配 + 簡約）。負元 ⊖g := [−1]∘g の
    閉性証明（[−1]∘[a] = [(−1)a] = [−a]）に使う。 -/
theorem cring_neg_one_mul (R : CRing) (a : R.carrier) :
    R.mul (R.neg R.one) a = R.neg a := by
  apply R.add_left_cancel (a := a)
  have hrd : R.mul (R.add R.one (R.neg R.one)) a
      = R.add a (R.mul (R.neg R.one) a) := by
    rw [CRing.right_distrib, R.one_mul]
  rw [cring_add_neg R a, ← hrd, cring_add_neg R R.one, cring_zero_mul R a]

/-! ## End(F) を `CRing` として構成 -/

/-- **M208F-2: End(F) の環オブジェクト** — 担体は Lubin–Tate 像
    { g : PS // ∃ a, g = [a] }（= 実際の自己準同型級数の集合）。
    加法 ⊕ = ps21Comp F、乗法 ⊙ = psComp、負元 ⊖g = [−1]∘g、
    零 = 0 級数、単位 = X。各演算の閉性は M76 の [a]⊕[b]=[a+b]・
    [a]⊙[b]=[ab] と [−1]∘[a]=[−a] から従い、各環公理は M100 の
    像上補題へ Subtype.ext で還元する。可換環（LT 像特有の可換性）。 -/
def formalEndRing (p : Nat) (hp : IsPrime p) : CRing where
  carrier := { g : PS (zpRing p) // ∃ a, g = ltSol p hp a }
  add := fun x y => ⟨ps21Comp (zpRing p) (lt2Sol p hp) x.val y.val, by
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    refine ⟨(zpRing p).add a b, ?_⟩
    rw [ha, hb]
    exact lt_module_add p hp a b⟩
  zero := ⟨psZero (zpRing p), ⟨(zpRing p).zero, (ltSol_zero p hp).symm⟩⟩
  neg := fun x => ⟨psComp (zpRing p) (ltInv p hp) x.val, by
    obtain ⟨a, ha⟩ := x.property
    refine ⟨(zpRing p).neg a, ?_⟩
    rw [ha,
      show ltInv p hp = ltSol p hp ((zpRing p).neg (zpRing p).one) from rfl,
      lt_module_mul p hp ((zpRing p).neg (zpRing p).one) a,
      cring_neg_one_mul (zpRing p) a]⟩
  mul := fun x y => ⟨psComp (zpRing p) x.val y.val, by
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    refine ⟨(zpRing p).mul a b, ?_⟩
    rw [ha, hb]
    exact lt_module_mul p hp a b⟩
  one := ⟨psX (zpRing p), ⟨(zpRing p).one, (ltSol_one p hp).symm⟩⟩
  add_assoc := by
    intro x y z
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    obtain ⟨c, hc⟩ := z.property
    show ps21Comp (zpRing p) (lt2Sol p hp)
        (ps21Comp (zpRing p) (lt2Sol p hp) x.val y.val) z.val
      = ps21Comp (zpRing p) (lt2Sol p hp) x.val
          (ps21Comp (zpRing p) (lt2Sol p hp) y.val z.val)
    rw [ha, hb, hc]
    exact ltEnd_gAdd_assoc p hp a b c
  zero_add := by
    intro x
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    show ps21Comp (zpRing p) (lt2Sol p hp) (psZero (zpRing p)) x.val = x.val
    rw [ha, ← ltSol_zero p hp]
    exact ltEnd_gAdd_zero p hp a
  neg_add := by
    intro x
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    show ps21Comp (zpRing p) (lt2Sol p hp)
        (psComp (zpRing p) (ltInv p hp) x.val) x.val = psZero (zpRing p)
    rw [ha,
      show ltInv p hp = ltSol p hp ((zpRing p).neg (zpRing p).one) from rfl,
      lt_module_mul p hp ((zpRing p).neg (zpRing p).one) a,
      cring_neg_one_mul (zpRing p) a,
      lt_module_add p hp ((zpRing p).neg a) a,
      (zpRing p).neg_add a]
    exact ltSol_zero p hp
  add_comm := by
    intro x y
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    show ps21Comp (zpRing p) (lt2Sol p hp) x.val y.val
      = ps21Comp (zpRing p) (lt2Sol p hp) y.val x.val
    rw [ha, hb]
    exact ltEnd_gAdd_comm p hp a b
  mul_assoc := by
    intro x y z
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    obtain ⟨c, hc⟩ := z.property
    show psComp (zpRing p) (psComp (zpRing p) x.val y.val) z.val
      = psComp (zpRing p) x.val (psComp (zpRing p) y.val z.val)
    rw [ha, hb, hc]
    exact ltEnd_gMul_assoc p hp a b c
  one_mul := by
    intro x
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    show psComp (zpRing p) (psX (zpRing p)) x.val = x.val
    rw [ha, ← ltSol_one p hp]
    exact ltEnd_gMul_one p hp a
  mul_comm := by
    intro x y
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    show psComp (zpRing p) x.val y.val = psComp (zpRing p) y.val x.val
    rw [ha, hb]
    exact ltEnd_gMul_comm p hp a b
  left_distrib := by
    intro x y z
    apply Subtype.ext
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    obtain ⟨c, hc⟩ := z.property
    show psComp (zpRing p) x.val
        (ps21Comp (zpRing p) (lt2Sol p hp) y.val z.val)
      = ps21Comp (zpRing p) (lt2Sol p hp)
          (psComp (zpRing p) x.val y.val) (psComp (zpRing p) x.val z.val)
    rw [ha, hb, hc]
    exact ltEnd_left_distrib p hp a b c

/-! ## ι : ℤ_p → End(F) を `RingHom` として構成 -/

/-- **M208F-3: 包含環準同型** — ι : a ↦ ⟨[a], _⟩ を汎用の
    `RingHom (zpRing p) (formalEndRing p hp)` として実体化。
    map_add/mul は M76 の [a+b]=[a]⊕[b]・[ab]=[a]⊙[b]、
    map_one は [1]=X。 -/
def oToEnd (p : Nat) (hp : IsPrime p) :
    RingHom (zpRing p) (formalEndRing p hp) where
  map := fun a => ⟨ltSol p hp a, ⟨a, rfl⟩⟩
  map_add := fun a b => by
    apply Subtype.ext
    show ltSol p hp ((zpRing p).add a b)
      = ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a) (ltSol p hp b)
    exact (lt_module_add p hp a b).symm
  map_mul := fun a b => by
    apply Subtype.ext
    show ltSol p hp ((zpRing p).mul a b)
      = psComp (zpRing p) (ltSol p hp a) (ltSol p hp b)
    exact (lt_module_mul p hp a b).symm
  map_one := by
    apply Subtype.ext
    show ltSol p hp (zpRing p).one = psX (zpRing p)
    exact ltSol_one p hp

/-! ## ι は全単射（環同型 ℤ_p ≅ End(F)） -/

/-- **M208F-4a: ι は単射**（一次係数の読み出し = `ltSol_injective`）。 -/
theorem oToEnd_injective (p : Nat) (hp : IsPrime p)
    (a b : (Zp p).carrier)
    (h : (oToEnd p hp).map a = (oToEnd p hp).map b) : a = b :=
  ltSol_injective p hp a b (congrArg Subtype.val h)

/-- **M208F-4b: ι は全射** — 担体の定義（すべての元は [a] の形）から。
    単射性と併せ ι は**全単射環準同型 = 環同型** ℤ_p ≅ End(F)。 -/
theorem oToEnd_surjective (p : Nat) (hp : IsPrime p)
    (x : (formalEndRing p hp).carrier) :
    ∃ a, (oToEnd p hp).map a = x := by
  obtain ⟨a, ha⟩ := x.property
  refine ⟨a, ?_⟩
  apply Subtype.ext
  show ltSol p hp a = x.val
  exact ha.symm

/-! ## 総括 witness -/

/-- **M208F-5a: End(F) 環パッケージ（圏論版）** — End(F) を一個の
    `CRing`、包含 a ↦ [a] を一個の `RingHom`、そしてそれが全単射
    （= 環同型 ℤ_p ≅ End(F)）であることを束ねた純レコード。 -/
structure FormalEndRingData (p : Nat) (hp : IsPrime p) where
  /-- End(F) の環オブジェクト。 -/
  ring : CRing
  /-- 包含環準同型 ι : ℤ_p → End(F)。 -/
  incl : RingHom (zpRing p) ring
  /-- ι は単射。 -/
  incl_inj : ∀ a b, incl.map a = incl.map b → a = b
  /-- ι は全射（担体 = 像）。 -/
  incl_surj : ∀ x, ∃ a, incl.map a = x

/-- **M208F-5b: witness** — ring := formalEndRing、incl := oToEnd。 -/
def formalEndRingData (p : Nat) (hp : IsPrime p) :
    FormalEndRingData p hp where
  ring := formalEndRing p hp
  incl := oToEnd p hp
  incl_inj := fun a b h => oToEnd_injective p hp a b h
  incl_surj := fun x => oToEnd_surjective p hp x

/-- **M208F-5c: 非空性** — End(F) の環パッケージ（圏論版）は実在する。 -/
theorem formalEndRing_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (FormalEndRingData p hp) :=
  ⟨formalEndRingData p hp⟩

end IUT
