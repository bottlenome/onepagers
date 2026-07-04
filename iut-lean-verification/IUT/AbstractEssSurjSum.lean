/-
  # M186F: 抽象本質的全射性の有限和拡張 — 非推移的 Aut(A)-集合の実現（柱A A-2・並行部品）

  M161F (AbstractEssSurj) は商公理付き抽象 Galois 圏 `QuotientData` の
  下で「任意の**推移的** Aut(A)-集合は比較関手 Hom(A,−) の像にスパン
  同型で実現される」を完成したが、その正直な限定 (2) は「非推移的
  （= 有限和）対象への拡張は範囲外」と明記していた。一方 M26
  (SumDecomposition) は和完全性公理 `SumData` の下で「剰余類作用の
  有限直和の実現」（M26-4）を持つが、これは剰余類作用のリストに
  限られ、M161F の「任意の推移的 Aut(A)-集合」レベルの一般性とは
  未接続だった。本モジュールはこの二つを合成し、A-2 の残余のうち
  「**有限非推移的 Aut(A)-集合の実現**」を選択公理抜きで完結させる:

  * M186F-1 `sumActHom` / `sumActHom_bij` — 同変写像の二項和
    （componentwise）と、その全単射性が成分の全単射性から従うこと
  * M186F-2 `SpanIso.sum` — **スパン同型は二項和の合同**:
    SpanIso X₁ Y₁ と SpanIso X₂ Y₂ から
    SpanIso (X₁ ⊔ X₂) (Y₁ ⊔ Y₂)（頂点 = 頂点の直和、脚 = 脚の直和）
  * M186F-3 `SumData.hom_sum_spanIso` — M26-3 `hom_sum_realizes` の
    スパン形: Hom(A,X) ⊔ Hom(A,Y) と Hom(A, X⊕Y) はスパン同型
    （「比較関手は二項和を保つ」の SpanIso 語彙への翻訳）
  * M186F-4 `SumData.hom_initial_spanIso` — 空 Aut(A)-集合は
    Hom(A, O)（始対象の像）とスパン同型（G5: F(O) = ∅ から
    Hom(A,O) も空、基点 a₀ での evaluation による）
  * M186F-5 `PointedTransitive` / `pointedOrbit` — 基点付き推移的
    Aut(A)-集合（= 連結成分の choice-free の提示形）の束ね。
    任意の点の軌道はその標準例
  * M186F-6 `SumData.abstract_ess_surj_finite` — **主定理**:
    基点付き推移的 Aut(A)-集合の任意の**有限リスト** L に対し対象
    Xo（= 各成分の実現対象の有限和 ⊕ᵢ Xoᵢ）が存在して
    ⊔ᵢ Lᵢ ≅ Hom(A, Xo)（SpanIso）。リスト帰納法 +
    M161F-4（各成分）+ M186F-2（和の合同）+ M186F-3（和の保存）
  * M186F-7 `SumData.abstract_ess_surj_orbits` — 系: 任意の
    Aut(A)-集合 X と点の有限リスト pts に対し、軌道の直和
    ⊔_{x∈pts} orbit(x) が像に実現される（M16-3 との合成）
  * M186F-8 `AbstractEssSurjSumData` / `abstractEssSurjSumWitness` /
    `abstractEssSurjSum_exists` — 総括データ・証人・存在定理

  **意義**: SGA1 本質的全射性の対象レベルの主張が、抽象公理系
  （`SumData` = G1–G6 + 降下 + 商 + 和完全性）の内部で「推移的
  Aut(A)-集合」（M161F）から「**有限非推移的 Aut(A)-集合**（= 基点
  付き推移成分の有限和）」へ拡張された。M161F が明示的に残した
  A-2 残余の一項が閉じ、有限 Aut(A)-集合の標準提示（軌道分解形）
  の全体が比較関手の像に入ることが公理のみから従う。

  **正直な限定**: (1) 有限非推移的 Aut(A)-集合は「基点付き推移的
  成分の有限リスト L の直和 `sumListAction`」として**提示された形**
  で受け取る。抽象的に与えられた X（「軌道が有限個」という仮定のみ）
  を軌道リストへ分解する操作は、軌道代表元の選出と各点の所属軌道の
  決定（決定可能性）を要し、choice-free では不可能なため、リスト
  提示を標準形として採用した（有限 G-集合の軌道分解 X = ⊔ orbit(xᵢ)
  は数学的には常に可能であり、系 M186F-7 が代表点リストが与えられた
  場合の軌道直和の実現を与える。ただし「X 自身が ⊔ orbit(xᵢ) と
  スパン同型」という接続は代表点の網羅性・非重複性の議論を要し
  本切片の範囲外）。(2) 主定理は `QuotientData` でなく和完全性
  公理込みの `SumData` を仮定にとる（M26-1 の fsum_* 4 公理は
  G5「F は有限和を保つ」の和の部分であり、Galois 圏の標準公理の
  範囲内。モデル充足は M26-5 で証明済み）。(3) A-2 の残余のうち
  「ガロア対象の十分性」と pro-表現対象の構成は引き続き範囲外。
  (4) 本モジュールの全定理は D : SumData を仮定にとるパラメトリック
  な形であり、モデル固有の Classical.choice（M21-8 gsetGaloisData の
  G6 / M26-5 gsetSumData 等）は**継承せず、本モジュールの証明自体の
  choice 使用はゼロ** — 主定理群の公理は Quot.sound のみ
  （M161F-4 経由の剰余類空間 Quot 由来。M186F-1〜4 は公理ゼロ）。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.AbstractEssSurj
import IUT.SumDecomposition

namespace IUT

universe u

/-! ## M186F-1: 同変写像の二項和 -/

/-- **同変写像の二項和**（M186F-1a）: f : X₁ → Y₁ と g : X₂ → Y₂ の
    componentwise の和 X₁ ⊔ X₂ → Y₁ ⊔ Y₂。 -/
def sumActHom {G : Grp} {X₁ Y₁ X₂ Y₂ : GAction G}
    (f : ActHom X₁ Y₁) (g : ActHom X₂ Y₂) :
    ActHom (sumAction G X₁ X₂) (sumAction G Y₁ Y₂) :=
  ⟨fun s => match s with
    | .inl x => .inl (f.map x)
    | .inr y => .inr (g.map y),
   fun σ s => by
    cases s with
    | inl x =>
      show Sum.inl (f.map (X₁.act σ x)) = Sum.inl (Y₁.act σ (f.map x))
      rw [f.equivariant]
    | inr y =>
      show Sum.inr (g.map (X₂.act σ y)) = Sum.inr (Y₂.act σ (g.map y))
      rw [g.equivariant]⟩

/-- **補題（M186F-1b）: 和の全単射性** — 成分が同変全単射なら
    二項和も同変全単射。 -/
theorem sumActHom_bij {G : Grp} {X₁ Y₁ X₂ Y₂ : GAction G}
    {f : ActHom X₁ Y₁} {g : ActHom X₂ Y₂}
    (hf : f.Bij) (hg : g.Bij) : (sumActHom f g).Bij := by
  refine ⟨?_, ?_⟩
  · -- 単射性: 構成子ごとの場合分け（inl/inr の非交差は構成子の不一致）
    intro p q h
    cases p with
    | inl x =>
      cases q with
      | inl x' =>
        have h' : Sum.inl (f.map x) = Sum.inl (f.map x') := h
        rw [hf.1 x x' (Sum.inl.inj h')]
      | inr y' =>
        have h' : Sum.inl (f.map x) = Sum.inr (g.map y') := h
        cases h'
    | inr y =>
      cases q with
      | inl x' =>
        have h' : Sum.inr (g.map y) = Sum.inl (f.map x') := h
        cases h'
      | inr y' =>
        have h' : Sum.inr (g.map y) = Sum.inr (g.map y') := h
        rw [hg.1 y y' (Sum.inr.inj h')]
  · -- 全射性: 成分の全射性から原像を構成子ごとに持ち上げる
    intro s
    cases s with
    | inl y =>
      obtain ⟨x, hx⟩ := hf.2 y
      refine ⟨.inl x, ?_⟩
      show Sum.inl (f.map x) = Sum.inl y
      rw [hx]
    | inr y =>
      obtain ⟨x, hx⟩ := hg.2 y
      refine ⟨.inr x, ?_⟩
      show Sum.inr (g.map x) = Sum.inr y
      rw [hx]

/-! ## M186F-2: スパン同型は二項和の合同 -/

/-- **定理（M186F-2）: SpanIso の二項和合同** — X₁ ≅ Y₁ かつ
    X₂ ≅ Y₂（スパン同型）なら X₁ ⊔ X₂ ≅ Y₁ ⊔ Y₂。頂点は頂点の
    直和、脚は脚の直和（M186F-1）。choice 不要の明示構成。 -/
theorem SpanIso.sum {G : Grp} {X₁ Y₁ X₂ Y₂ : GAction G}
    (h₁ : SpanIso X₁ Y₁) (h₂ : SpanIso X₂ Y₂) :
    SpanIso (sumAction G X₁ X₂) (sumAction G Y₁ Y₂) := by
  obtain ⟨Z₁, f₁, g₁, hf₁, hg₁⟩ := h₁
  obtain ⟨Z₂, f₂, g₂, hf₂, hg₂⟩ := h₂
  exact ⟨sumAction G Z₁ Z₂, sumActHom f₁ f₂, sumActHom g₁ g₂,
    sumActHom_bij hf₁ hf₂, sumActHom_bij hg₁ hg₂⟩

/-! ## M186F-3/4: 比較関手は二項和と始対象を保つ（SpanIso 語彙） -/

/-- **定理（M186F-3）: 二項和の保存のスパン形** — A 連結のとき
    Hom(A,X) ⊔ Hom(A,Y) は Hom(A, X⊕Y) とスパン同型
    （M26-3 `hom_sum_realizes` の同変全単射を右脚、恒等を左脚と
    するスパン）。 -/
theorem SumData.hom_sum_spanIso (D : SumData.{u}) {A X Y : D.C.Obj}
    (hAc : D.toGaloisCatData.Connected A) :
    SpanIso
      (sumAction (D.toGaloisCatData.autGrp A)
        (D.toGaloisCatData.homGAction A X)
        (D.toGaloisCatData.homGAction A Y))
      (D.toGaloisCatData.homGAction A (D.Sm X Y)) := by
  obtain ⟨Ψ, hi, hs⟩ := D.hom_sum_realizes hAc
  exact ⟨sumAction (D.toGaloisCatData.autGrp A)
      (D.toGaloisCatData.homGAction A X)
      (D.toGaloisCatData.homGAction A Y),
    ActHom.idHom _, Ψ,
    ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩, ⟨hi, hs⟩⟩

/-- **定理（M186F-4）: 始対象の保存のスパン形** — 空 Aut(A)-集合は
    Hom(A, O) とスパン同型。G5（F(O) = ∅）により射 u : A → O は
    基点の像 F(u)(a₀) ∈ F(O) を持てず、Hom(A,O) も空。 -/
theorem SumData.hom_initial_spanIso (D : SumData.{u}) {A : D.C.Obj}
    (a₀ : D.F.onObj A) :
    SpanIso (emptyAction (D.toGaloisCatData.autGrp A))
      (D.toGaloisCatData.homGAction A D.O) :=
  ⟨emptyAction (D.toGaloisCatData.autGrp A),
   ActHom.idHom _,
   ⟨fun e => (nomatch e), fun _ e => (nomatch e)⟩,
   ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩,
   ⟨fun p => (nomatch p),
    fun u => (D.fO_empty (D.F.onHom u a₀)).elim⟩⟩

/-! ## M186F-5: 基点付き推移的 Aut(A)-集合（連結成分の提示形） -/

/-- **基点付き推移的 G-集合**（M186F-5a）: 有限 G-集合の連結成分の
    choice-free の提示形。基点を明示的に持つことで軌道代表元の
    選出（Classical.choice）を回避する。 -/
structure PointedTransitive (G : Grp) where
  /-- 台となる G-集合。 -/
  space : GAction G
  /-- 推移性（連結性）。 -/
  transitive : space.Transitive
  /-- 基点。 -/
  pt : space.carrier

/-- **標準例（M186F-5b）**: 任意の G-集合の任意の点の軌道は基点付き
    推移的 G-集合（M16-3 `orbit_transitive`）。 -/
def pointedOrbit {G : Grp} (X : GAction G) (x₀ : X.carrier) :
    PointedTransitive G :=
  ⟨orbitOf X x₀, orbit_transitive X x₀, ⟨x₀, orbitRel_refl X x₀⟩⟩

/-! ## M186F-6: 主定理 — 有限非推移的 Aut(A)-集合の抽象的実現 -/

/-- **定理（M186F-6）: 抽象本質的全射性・有限和版** — 和完全性付き
    抽象 Galois 圏 `SumData` の下、A ガロア・a₀ ∈ F(A) のとき、
    基点付き推移的 Aut(A)-集合の**任意の有限リスト** L に対し対象
    Xo（= 各成分の実現対象の有限和）が存在して、直和
    ⊔ᵢ Lᵢ は Hom(A, Xo) とスパン同型。M161F-4（推移的成分の実現）
    が M186F-2（和の合同）と M186F-3（和の保存）を経由して有限
    非推移的 Aut(A)-集合へ拡張される — M161F が明示的に残した
    A-2 残余の一項の完結。 -/
theorem SumData.abstract_ess_surj_finite (D : SumData.{u}) {A : D.C.Obj}
    (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A)
    (L : List (PointedTransitive (D.toGaloisCatData.autGrp A))) :
    ∃ Xo : D.C.Obj,
      SpanIso
        (sumListAction (D.toGaloisCatData.autGrp A)
          (L.map (fun P => P.space)))
        (D.toGaloisCatData.homGAction A Xo) := by
  induction L with
  | nil =>
    -- 空リスト: 空 Aut(A)-集合は始対象 O の像に実現（M186F-4）
    exact ⟨D.O, D.hom_initial_spanIso a₀⟩
  | cons P L ih =>
    -- 先頭成分は M161F-4 で、残りは帰納法の仮定で実現し、
    -- 和の合同（M186F-2）と和の保存（M186F-3）で貼り合わせる
    obtain ⟨XoL, hL⟩ := ih
    obtain ⟨Xo₁, h₁⟩ := D.toQuotientData.abstract_ess_surj_transitive
      hA a₀ P.space P.transitive P.pt
    exact ⟨D.Sm Xo₁ XoL,
      SpanIso.trans (SpanIso.sum h₁ hL) (D.hom_sum_spanIso hA.1)⟩

/-! ## M186F-7: 系 — 軌道の有限直和の実現 -/

/-- リスト簿記の補題: pointedOrbit のリストの台は軌道のリスト。 -/
theorem map_pointedOrbit_space {G : Grp} (X : GAction G)
    (pts : List X.carrier) :
    (pts.map (fun x => pointedOrbit X x)).map
        (fun P => PointedTransitive.space P)
      = pts.map (fun x => orbitOf X x) := by
  induction pts with
  | nil => rfl
  | cons x pts ih =>
    show orbitOf X x :: (pts.map (fun x => pointedOrbit X x)).map
        (fun P => PointedTransitive.space P)
      = orbitOf X x :: pts.map (fun x => orbitOf X x)
    rw [ih]

/-- **系（M186F-7）: 軌道の有限直和の実現** — 任意の Aut(A)-集合 X
    と点の有限リスト pts に対し、軌道の直和 ⊔_{x∈pts} orbit(x) は
    比較関手の像にスパン同型で実現される。M161F-5（単一軌道）の
    有限和版。 -/
theorem SumData.abstract_ess_surj_orbits (D : SumData.{u}) {A : D.C.Obj}
    (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A)
    (X : GAction (D.toGaloisCatData.autGrp A)) (pts : List X.carrier) :
    ∃ Xo : D.C.Obj,
      SpanIso
        (sumListAction (D.toGaloisCatData.autGrp A)
          (pts.map (fun x => orbitOf X x)))
        (D.toGaloisCatData.homGAction A Xo) := by
  obtain ⟨Xo, h⟩ := D.abstract_ess_surj_finite hA a₀
    (pts.map (fun x => pointedOrbit X x))
  refine ⟨Xo, ?_⟩
  rw [← map_pointedOrbit_space X pts]
  exact h

/-! ## M186F-8: 総括 -/

/-- **総括データ（M186F-8a）**: 有限和版抽象本質的全射性の証人 —
    ガロア対象 base・基点と、基点付き推移的 Aut(base)-集合の任意の
    有限リストの直和を比較関手の像にスパン同型で実現する対象の存在。 -/
structure AbstractEssSurjSumData (D : SumData.{u}) where
  /-- ガロア対象（被覆理論の「十分大きい被覆」）。 -/
  base : D.C.Obj
  /-- base は抽象 IsGalois を満たす。 -/
  galois : D.toGaloisCatData.IsGalois base
  /-- ファイバーの基点。 -/
  basept : D.F.onObj base
  /-- 実現: 基点付き推移的 Aut(base)-集合の任意の有限リストの直和は
      ある対象の Hom(base, −) 値とスパン同型。 -/
  realize : ∀ L : List (PointedTransitive (D.toGaloisCatData.autGrp base)),
    ∃ Xo : D.C.Obj,
      SpanIso
        (sumListAction (D.toGaloisCatData.autGrp base)
          (L.map (fun P => P.space)))
        (D.toGaloisCatData.homGAction base Xo)

/-- **証人（M186F-8b）**: ガロア対象と基点が与えられれば M186F-6 が
    総括データを与える。 -/
def abstractEssSurjSumWitness (D : SumData.{u}) {A : D.C.Obj}
    (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A) :
    AbstractEssSurjSumData D where
  base := A
  galois := hA
  basept := a₀
  realize := fun L => D.abstract_ess_surj_finite hA a₀ L

/-- **定理（M186F-8c）: 有限和版抽象本質的全射性データの存在**。 -/
theorem abstractEssSurjSum_exists (D : SumData.{u}) {A : D.C.Obj}
    (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A) :
    Nonempty (AbstractEssSurjSumData D) :=
  ⟨abstractEssSurjSumWitness D hA a₀⟩

end IUT
