/-
  IUT/SGA1Completion.lean — M22（SGA1 主定理の抽象完成: 比較関手の充満忠実性）

  M21 で公理系 G1–G6 から忠実性・evaluation 単射・ガロア対象の群復元を
  導出した。本モジュールは主定理の**射レベルを完成**させる:
  ガロア対象 A に対する比較関手 Hom(A,−) : C → Aut(A)-Set を抽象的に
  構成し、分裂対象の上で**充満忠実**であることを公理から証明する。

  * M22-1 `CatIso.ext` / `autGrp` — 同型射の外延性（逆は順で決まる）と
    **自己同型群の群化**（選択公理なし: 逆をデータとして持つ CatIso を
    台にする）
  * M22-2 `homGAction` / `homFunctor` — **比較関手の抽象構成**:
    X ↦ Hom(A,X)（Aut(A) は前合成で作用）、射は後合成（同変性込み）。
    SGA1 主定理の関手そのもの
  * M22-3 `Split` / `homFunctor_faithful` — A が X を分裂させる
    （evaluation が全射）とき比較関手は**忠実**
  * M22-4 `connected_hom_surjective` / `split_connected_transitive` —
    連結 X への射はファイバー全射（像が固有部分対象になれない）、
    したがって **Hom(A,X) は Aut(A) の単一軌道**（A ガロア・X 連結
    分裂のとき）
  * M22-5 `DescentData` — G3 の「強い」部分: **像エピに沿った降下**
    （imE の核対を等化する射は像を経由する）を公理データとして追加。
    SGA1 の G3「strict epi」の厳密性の内容
  * M22-6 `homFunctor_full` — **充満性**: 同変写像 φ : Hom(A,X) →
    Hom(A,Y) は必ず後合成 (−;f) の形。証明: u₀ の像への降下で f を
    構成し、軌道推移性（M22-4）と φ の同変性で全ての u に伝播させる。
    核対の等化条件はガロア推移性 + evaluation 単射性（M21-6）で検証
  * M22-7 `sga1_fully_faithful` — **主定理（射レベル）の完成**:
    比較関手は連結分裂対象の上で充満忠実
  * M22-8 `gsetDescentData` — モデル（G-Set 圏）は降下公理も満たす
    （無矛盾性。降下射の構成に Classical.choice——G6 と同様、
    選択原理の所在の特定）

  **位置づけ（正直な申告）**: 主定理の対象レベル（本質的全射性 =
  任意の連続 Aut-集合が Hom(A,X) として実現されること）は商公理
  （G2 後半: 有限自己同型群による商の存在）と pro-対象を要し未形式化。
  ただしモデル側の対象分類は M16/M20 で完成済みであり、抽象側も
  軌道分類（M16-5 が `homGAction` にそのまま適用可能）で軌道 =
  剰余類作用までは既に判っている。本モジュールにより、SGA1 主定理は
  「モデルで全部 + 抽象で射レベル全部・対象レベルは軌道分類まで」
  という形で完成する。
-/
import IUT.AbstractGalois

namespace IUT

universe u

/-- **同型射の外延性**（M22-1a）: hom 成分が一致すれば逆も一致する
    （逆の一意性）。 -/
theorem CatIso.ext {C : Cat.{u, 0}} {X Y : C.Obj} {σ τ : CatIso C X Y}
    (h : σ.hom = τ.hom) : σ = τ := by
  have hinv : σ.inv = τ.inv := by
    calc σ.inv = C.comp (C.id Y) σ.inv := (C.id_comp _).symm
      _ = C.comp (C.comp τ.inv τ.hom) σ.inv := by rw [τ.inv_hom]
      _ = C.comp τ.inv (C.comp τ.hom σ.inv) := C.assoc _ _ _
      _ = C.comp τ.inv (C.comp σ.hom σ.inv) := by rw [h]
      _ = C.comp τ.inv (C.id X) := by rw [σ.hom_inv]
      _ = τ.inv := C.comp_id _
  cases σ with | mk sh si h1 h2 =>
  cases τ with | mk th ti h3 h4 =>
  cases h
  cases hinv
  rfl

namespace GaloisCatData

variable (D : GaloisCatData.{u, 0})

/-- **自己同型群**（M22-1b）: 逆をデータとして持つ同型 `CatIso` を
    台にした群（選択公理なしの群化）。 -/
def autGrp (A : D.C.Obj) : Grp where
  carrier := CatIso D.C A A
  mul := fun σ τ =>
    ⟨D.C.comp σ.hom τ.hom, D.C.comp τ.inv σ.inv,
     by rw [D.C.assoc, ← D.C.assoc τ.hom τ.inv σ.inv, τ.hom_inv,
       D.C.id_comp, σ.hom_inv],
     by rw [D.C.assoc, ← D.C.assoc σ.inv σ.hom τ.hom, σ.inv_hom,
       D.C.id_comp, τ.inv_hom]⟩
  one := ⟨D.C.id A, D.C.id A, D.C.id_comp _, D.C.id_comp _⟩
  inv := fun σ => ⟨σ.inv, σ.hom, σ.inv_hom, σ.hom_inv⟩
  mul_assoc := fun σ τ ρ => CatIso.ext (D.C.assoc _ _ _)
  one_mul := fun σ => CatIso.ext (D.C.id_comp _)
  inv_mul := fun σ => CatIso.ext σ.inv_hom

/-- **比較関手の対象部**（M22-2a）: Hom(A,X) への Aut(A) の前合成作用。 -/
def homGAction (A X : D.C.Obj) : GAction (D.autGrp A) where
  carrier := D.C.Hom A X
  act := fun σ u => D.C.comp σ.hom u
  act_one := fun u => D.C.id_comp u
  act_mul := fun σ τ u => D.C.assoc σ.hom τ.hom u

/-- **比較関手**（M22-2b）: Hom(A,−) : C → Aut(A)-Set。
    SGA1 主定理「C ≃ π₁-Set」の左辺から右辺への関手の抽象構成。 -/
def homFunctor (A : D.C.Obj) : Functor D.C (GSetCat (D.autGrp A)) where
  onObj := fun X => D.homGAction A X
  onHom := fun {X Y} f =>
    ⟨fun u => D.C.comp u f, fun σ u => D.C.assoc σ.hom u f⟩
  map_id := fun X => ActHom.ext (fun u => D.C.comp_id u)
  map_comp := fun {X Y Z} f g => ActHom.ext (fun u => (D.C.assoc u f g).symm)

/-- **分裂性**: A は X を点 a₀ で分裂させる（evaluation の全射性）。 -/
def Split (A : D.C.Obj) (a₀ : D.F.onObj A) (X : D.C.Obj) : Prop :=
  ∀ b : D.F.onObj X, ∃ u : D.C.Hom A X, D.F.onHom u a₀ = b

/-- **定理 (M22-3): 比較関手の忠実性** — A が X を分裂させるとき、
    Hom(A,−) は X からの射の上で忠実（後合成作用が一致すれば
    元の射も一致）。 -/
theorem homFunctor_faithful {A X Y : D.C.Obj} (a₀ : D.F.onObj A)
    (hX : D.Split A a₀ X) (f g : D.C.Hom X Y)
    (h : ∀ u : D.C.Hom A X, D.C.comp u f = D.C.comp u g) : f = g := by
  apply D.fiber_faithful
  intro x
  obtain ⟨u, hu⟩ := hX x
  rw [← hu, ← D.fmap_comp, ← D.fmap_comp, h u]

/-- ガロア推移性の同型データ版: 任意の二点は CatIso で移り合う。 -/
theorem galois_trans_iso {A : D.C.Obj} (hA : D.IsGalois A)
    (a b : D.F.onObj A) :
    ∃ σ : CatIso D.C A A, D.F.onHom σ.hom a = b := by
  obtain ⟨σ, ⟨g, h1, h2⟩, hσ⟩ := hA.2 a b
  exact ⟨⟨σ, g, h1, h2⟩, hσ⟩

/-- **定理 (M22-4a): 連結対象への射はファイバー全射** — u₀ : A → X、
    X 連結、A のファイバー非空なら F(u₀) は全射（像が固有部分対象に
    なれないことの帰結）。 -/
theorem connected_hom_surjective {A X : D.C.Obj} (hXc : D.Connected X)
    (u₀ : D.C.Hom A X) (a₀ : D.F.onObj A) :
    ∀ b : D.F.onObj X, ∃ a : D.F.onObj A, D.F.onHom u₀ a = b := by
  -- u₀ = e ; m（像分解）。m は非空ファイバーのモノ ⟹ 連結性で同型
  have hm : D.Mono (D.imM u₀) :=
    D.mono_of_fiber_injective (D.imM u₀) (D.imM_fiber_inj u₀)
  have hne : Nonempty (D.F.onObj (D.Im u₀)) := ⟨D.F.onHom (D.imE u₀) a₀⟩
  obtain ⟨g, hg1, hg2⟩ := hXc.2 (D.imM u₀) hm hne
  intro b
  obtain ⟨x, hx⟩ := D.imE_fiber_surj u₀ (D.F.onHom g b)
  refine ⟨x, ?_⟩
  have h1 : D.F.onHom u₀ x = D.F.onHom (D.imM u₀) (D.F.onHom (D.imE u₀) x) := by
    rw [← D.fmap_comp, D.im_comp]
  rw [h1, hx, ← D.fmap_comp, hg2, D.fmap_id]

/-- **定理 (M22-4b): 軌道推移性** — A ガロア・X 連結なら Hom(A,X) は
    Aut(A) の前合成作用の単一軌道（u = σ ∘ u₀ なる同型 σ が存在）。 -/
theorem split_connected_transitive {A X : D.C.Obj} (hA : D.IsGalois A)
    (a₀ : D.F.onObj A) (hXc : D.Connected X)
    (u₀ u : D.C.Hom A X) :
    ∃ σ : CatIso D.C A A, D.C.comp σ.hom u₀ = u := by
  -- F u₀ は全射なので F u a₀ の原像 a があり、ガロア推移性で a₀ ↦ a
  obtain ⟨a, ha⟩ := D.connected_hom_surjective hXc u₀ a₀ (D.F.onHom u a₀)
  obtain ⟨σ, hσ⟩ := D.galois_trans_iso hA a₀ a
  refine ⟨σ, ?_⟩
  apply D.evaluation_injective hA.1 a₀
  rw [D.fmap_comp, hσ, ha]

end GaloisCatData

/-! ## M22-5: 降下公理（G3 の strict epi 性） -/

/-- **降下データ付き抽象 Galois 圏**: G3 の像分解の「強さ」——
    像エピ imE の核対を等化する射は像を一意に経由する——を
    公理データとして追加。SGA1 の strict epimorphism の内容。 -/
structure DescentData extends GaloisCatData.{u, 0} where
  im_descend : {X Y W : C.Obj} → (f : C.Hom X Y) → (g : C.Hom X W) →
    C.comp (pb₁ (imE f) (imE f)) g = C.comp (pb₂ (imE f) (imE f)) g →
    C.Hom (Im f) W
  im_descend_comp : ∀ {X Y W : C.Obj} (f : C.Hom X Y) (g : C.Hom X W)
    (h : C.comp (pb₁ (imE f) (imE f)) g = C.comp (pb₂ (imE f) (imE f)) g),
    C.comp (imE f) (im_descend f g h) = g

namespace DescentData

variable (D : DescentData.{u})

/-- **定理 (M22-6): 比較関手の充満性** — A ガロア・X 連結分裂のとき、
    同変写像 φ : Hom(A,X) → Hom(A,Y) は必ずある f : X → Y による
    後合成である。

    証明の骨格: u₀ : A → X を取り、φ(u₀) : A → Y を u₀ の像
    （≅ X、連結性）に**降下**させて f を作る。降下条件（核対の
    等化）は「同じ点に落ちる A の二点はデッキ変換 σ で移り合い
    （ガロア推移性）、σ∘u₀ = u₀（evaluation 単射性）、よって φ の
    同変性から σ∘φ(u₀) = φ(u₀)」により検証される。最後に軌道
    推移性（M22-4b）と同変性で u₀ から全ての u へ伝播する。 -/
theorem homFunctor_full {A X Y : D.C.Obj}
    (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A)
    (hXc : D.toGaloisCatData.Connected X)
    (φ : ActHom (D.toGaloisCatData.homGAction A X)
      (D.toGaloisCatData.homGAction A Y))
    (u₀ : D.C.Hom A X) :
    ∃ f : D.C.Hom X Y, ∀ u : D.C.Hom A X, D.C.comp u f = φ.map u := by
  -- (1) 降下条件: 核対は φ(u₀) を等化する
  have hdesc : D.C.comp (D.pb₁ (D.imE u₀) (D.imE u₀)) (φ.map u₀)
      = D.C.comp (D.pb₂ (D.imE u₀) (D.imE u₀)) (φ.map u₀) := by
    apply D.toGaloisCatData.fiber_faithful
    intro w
    -- 核対の点 w の両足 a, a' は F u₀ で同じ値を持つ
    have hee : D.F.onHom (D.imE u₀) (D.F.onHom (D.pb₁ (D.imE u₀) (D.imE u₀)) w)
        = D.F.onHom (D.imE u₀) (D.F.onHom (D.pb₂ (D.imE u₀) (D.imE u₀)) w) := by
      rw [← D.toGaloisCatData.fmap_comp, ← D.toGaloisCatData.fmap_comp, D.pb_comm]
    have hu₀ : D.F.onHom u₀ (D.F.onHom (D.pb₁ (D.imE u₀) (D.imE u₀)) w)
        = D.F.onHom u₀ (D.F.onHom (D.pb₂ (D.imE u₀) (D.imE u₀)) w) := by
      have h1 : ∀ x, D.F.onHom u₀ x
          = D.F.onHom (D.imM u₀) (D.F.onHom (D.imE u₀) x) := by
        intro x
        rw [← D.toGaloisCatData.fmap_comp, D.im_comp]
      rw [h1, h1, hee]
    -- デッキ変換 σ: a ↦ a'、σ∘u₀ = u₀、同変性で σ∘φ(u₀) = φ(u₀)
    obtain ⟨σ, hσ⟩ := D.toGaloisCatData.galois_trans_iso hA
      (D.F.onHom (D.pb₁ (D.imE u₀) (D.imE u₀)) w)
      (D.F.onHom (D.pb₂ (D.imE u₀) (D.imE u₀)) w)
    have hfix : D.C.comp σ.hom u₀ = u₀ := by
      apply D.toGaloisCatData.evaluation_injective hA.1
        (D.F.onHom (D.pb₁ (D.imE u₀) (D.imE u₀)) w)
      rw [D.toGaloisCatData.fmap_comp, hσ]
      exact hu₀.symm
    have hφfix : D.C.comp σ.hom (φ.map u₀) = φ.map u₀ := by
      have h2 := φ.equivariant σ u₀
      -- h2 : φ(σ∘u₀) = σ∘φ(u₀)
      have h3 : φ.map (D.C.comp σ.hom u₀) = D.C.comp σ.hom (φ.map u₀) := h2
      rw [hfix] at h3
      exact h3.symm
    -- 仕上げ: F(p₁;φu₀) w = F φu₀ a = F (σ;φu₀) a = F φu₀ a' = F(p₂;φu₀) w
    rw [D.toGaloisCatData.fmap_comp, D.toGaloisCatData.fmap_comp, ← hσ,
      ← D.toGaloisCatData.fmap_comp σ.hom (φ.map u₀)
        (D.F.onHom (D.pb₁ (D.imE u₀) (D.imE u₀)) w), hφfix]
  -- (2) 降下で h : Im(u₀) → Y、連結性で Im(u₀) ≅ X、f を合成で作る
  have hm : D.toGaloisCatData.Mono (D.imM u₀) :=
    D.toGaloisCatData.mono_of_fiber_injective (D.imM u₀) (D.imM_fiber_inj u₀)
  have hne : Nonempty (D.F.onObj (D.Im u₀)) := ⟨D.F.onHom (D.imE u₀) a₀⟩
  obtain ⟨g, hg1, hg2⟩ := hXc.2 (D.imM u₀) hm hne
  refine ⟨D.C.comp g (D.im_descend u₀ (φ.map u₀) hdesc), ?_⟩
  -- まず u₀ について検証
  have hu₀f : D.C.comp u₀ (D.C.comp g (D.im_descend u₀ (φ.map u₀) hdesc))
      = φ.map u₀ := by
    calc D.C.comp u₀ (D.C.comp g (D.im_descend u₀ (φ.map u₀) hdesc))
        = D.C.comp (D.C.comp (D.imE u₀) (D.imM u₀))
            (D.C.comp g (D.im_descend u₀ (φ.map u₀) hdesc)) := by
          rw [D.im_comp]
      _ = D.C.comp (D.imE u₀) (D.C.comp (D.imM u₀)
            (D.C.comp g (D.im_descend u₀ (φ.map u₀) hdesc))) := D.C.assoc _ _ _
      _ = D.C.comp (D.imE u₀) (D.C.comp (D.C.comp (D.imM u₀) g)
            (D.im_descend u₀ (φ.map u₀) hdesc)) := by
          rw [D.C.assoc]
      _ = D.C.comp (D.imE u₀) (D.C.comp (D.C.id (D.Im u₀))
            (D.im_descend u₀ (φ.map u₀) hdesc)) := by rw [hg1]
      _ = D.C.comp (D.imE u₀) (D.im_descend u₀ (φ.map u₀) hdesc) := by
          rw [D.C.id_comp]
      _ = φ.map u₀ := D.im_descend_comp u₀ (φ.map u₀) hdesc
  -- 軌道推移性で全ての u に伝播
  intro u
  obtain ⟨τ, hτ⟩ := D.toGaloisCatData.split_connected_transitive hA a₀ hXc u₀ u
  have hequiv : φ.map (D.C.comp τ.hom u₀) = D.C.comp τ.hom (φ.map u₀) :=
    φ.equivariant τ u₀
  calc D.C.comp u (D.C.comp g (D.im_descend u₀ (φ.map u₀) hdesc))
      = D.C.comp (D.C.comp τ.hom u₀)
          (D.C.comp g (D.im_descend u₀ (φ.map u₀) hdesc)) := by rw [hτ]
    _ = D.C.comp τ.hom (D.C.comp u₀
          (D.C.comp g (D.im_descend u₀ (φ.map u₀) hdesc))) := D.C.assoc _ _ _
    _ = D.C.comp τ.hom (φ.map u₀) := by rw [hu₀f]
    _ = φ.map (D.C.comp τ.hom u₀) := hequiv.symm
    _ = φ.map u := by rw [hτ]

/-- **定理 (M22-7): SGA1 主定理・射レベルの完成** — 比較関手
    Hom(A,−) は連結分裂対象の上で**充満忠実**（M22-3 + M22-6）。
    対象レベル（軌道 = 剰余類）は M16-5 が `homGAction` にそのまま
    適用される。 -/
theorem sga1_fully_faithful {A X Y : D.C.Obj}
    (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A)
    (hXc : D.toGaloisCatData.Connected X)
    (hX : D.toGaloisCatData.Split A a₀ X) (u₀ : D.C.Hom A X) :
    (∀ f g : D.C.Hom X Y,
      (∀ u : D.C.Hom A X, D.C.comp u f = D.C.comp u g) → f = g) ∧
    (∀ φ : ActHom (D.toGaloisCatData.homGAction A X)
        (D.toGaloisCatData.homGAction A Y),
      ∃ f : D.C.Hom X Y, ∀ u : D.C.Hom A X, D.C.comp u f = φ.map u) :=
  ⟨fun f g h => D.toGaloisCatData.homFunctor_faithful a₀ hX f g h,
   fun φ => D.homFunctor_full hA a₀ hXc φ u₀⟩

end DescentData

/-! ## M22-8: モデルの降下公理充足 -/

/-- モデルの核対条件の読み出し: 同じ f-値を持つ二点では g-値も等しい。 -/
theorem gset_descent_key (G : Grp) {X Y W : GAction G}
    (f : ActHom X Y) (g : ActHom X W)
    (h : (GSetCat G).comp ((gsetGaloisData G).pb₁ ((gsetGaloisData G).imE f)
        ((gsetGaloisData G).imE f)) g
      = (GSetCat G).comp ((gsetGaloisData G).pb₂ ((gsetGaloisData G).imE f)
        ((gsetGaloisData G).imE f)) g)
    (x x' : X.carrier) (hxx : f.map x = f.map x') :
    g.map x = g.map x' := by
  have h1 := congrFun (congrArg ActHom.map h)
    (⟨(x, x'), Subtype.ext hxx⟩ :
      (pullbackAction G ((gsetGaloisData G).imE f)
        ((gsetGaloisData G).imE f)).carrier)
  exact h1

/-- **定理 (M22-8): モデルは降下公理も満たす** — G-Set 圏で像エピ
    に沿った降下射を構成（preimage の選択に Classical.choice。
    G6 と同様、選択原理の所在の形式的特定）。 -/
noncomputable def gsetDescentData (G : Grp) : DescentData.{1} where
  toGaloisCatData := gsetGaloisData G
  im_descend := fun {X Y W} f g h =>
    ⟨fun w => g.map (Classical.choose w.property), by
      intro σ w
      have hc₀ := Classical.choose_spec w.property
      have hc₁ := Classical.choose_spec ((imageAction G f).act σ w).property
      -- 両者は同じ f-値を持つ: f(choose₁) = σ·w.val = f(σ·choose₀)
      have hf : f.map (Classical.choose ((imageAction G f).act σ w).property)
          = f.map (X.act σ (Classical.choose w.property)) := by
        rw [hc₁, f.equivariant, hc₀]
        rfl
      show g.map (Classical.choose ((imageAction G f).act σ w).property)
          = W.act σ (g.map (Classical.choose w.property))
      rw [gset_descent_key G f g h _ _ hf, g.equivariant]⟩
  im_descend_comp := fun {X Y W} f g h => by
    apply ActHom.ext
    intro x
    have hc := Classical.choose_spec (((gsetGaloisData G).imE f).map x).property
    -- hc : f(choose) = (imE x).val = f x
    exact gset_descent_key G f g h _ x hc

/-- 降下公理込みの公理系の無矛盾性。 -/
theorem descentData_consistent : Nonempty DescentData.{1} :=
  ⟨gsetDescentData intGrp⟩

end IUT
