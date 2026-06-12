/-
  IUT/CategoryTheory.lean — M19（圏論インフラと同値の輸送）の形式化

  SGA1 主定理の関手的パッケージング（M20）に必要な圏論を
  mathlib 非依存で建設する:

  * `Cat` / `Functor` / `NatTrans` / `CatIso` / `CatEquiv` —
    圏・関手・自然変換・同型・**圏同値**（宇宙多相）
  * `SetCat` — 集合（型）の圏。ファイバー関手の行き先
  * `GSetCat G` — **G-集合の圏**（M14 の `GAction`/`ActHom` を
    圏として組織化。`ActHom.ext` による射の外延性込み）
  * `restrictFunctor` — 群準同型 θ : H → G に沿った制限関手
    G-Set → H-Set
  * M19-1 `restrictEquiv` — **同値の輸送**: 互いに逆な群準同型の対
    （= 群同型）は作用圏の圏同値を誘導する。M20 で
    「G-Set ≃ Aut(F)-Set」を組み立てる際の橋
-/
import IUT.GaloisCategory

namespace IUT

universe u v u' v'

/-- 圏（宇宙多相）。 -/
structure Cat where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)

/-- 関手。 -/
structure Functor (C : Cat.{u, v}) (D : Cat.{u', v'}) where
  onObj : C.Obj → D.Obj
  onHom : {X Y : C.Obj} → C.Hom X Y → D.Hom (onObj X) (onObj Y)
  map_id : ∀ X, onHom (C.id X) = D.id (onObj X)
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    onHom (C.comp f g) = D.comp (onHom f) (onHom g)

/-- 自然変換。 -/
structure NatTrans {C : Cat.{u, v}} {D : Cat.{u', v'}}
    (F G : Functor C D) where
  app : (X : C.Obj) → D.Hom (F.onObj X) (G.onObj X)
  natural : ∀ {X Y : C.Obj} (f : C.Hom X Y),
    D.comp (F.onHom f) (app Y) = D.comp (app X) (G.onHom f)

/-- 圏の中の同型。 -/
structure CatIso (C : Cat.{u, v}) (X Y : C.Obj) where
  hom : C.Hom X Y
  inv : C.Hom Y X
  hom_inv : C.comp hom inv = C.id X
  inv_hom : C.comp inv hom = C.id Y

/-- **圏同値**（随伴同値データ: 両向き関手＋単位・余単位の自然同型）。 -/
structure CatEquiv (C : Cat.{u, v}) (D : Cat.{u', v'}) where
  F : Functor C D
  G : Functor D C
  unit : (X : C.Obj) → CatIso C X (G.onObj (F.onObj X))
  counit : (Y : D.Obj) → CatIso D (F.onObj (G.onObj Y)) Y
  unit_natural : ∀ {X X' : C.Obj} (f : C.Hom X X'),
    C.comp f (unit X').hom = C.comp (unit X).hom (G.onHom (F.onHom f))
  counit_natural : ∀ {Y Y' : D.Obj} (g : D.Hom Y Y'),
    D.comp (counit Y).hom g = D.comp (F.onHom (G.onHom g)) (counit Y').hom

/-- 集合（型）の圏。 -/
def SetCat : Cat where
  Obj := Type
  Hom := fun A B => A → B
  id := fun _ => fun a => a
  comp := fun f g => fun a => g (f a)
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-- 同変写像の外延性（射の等値は底写像で決まる）。 -/
theorem ActHom.ext {G : Grp} {X Y : GAction G} {f g : ActHom X Y}
    (h : ∀ x, f.map x = g.map x) : f = g := by
  cases f with | mk fmap fe =>
  cases g with | mk gmap ge =>
  have hm : fmap = gmap := funext h
  subst hm
  rfl

/-- 恒等同変写像。 -/
def ActHom.idHom {G : Grp} (X : GAction G) : ActHom X X :=
  ⟨fun x => x, fun _ _ => rfl⟩

/-- 同変写像の合成。 -/
def ActHom.comp {G : Grp} {X Y Z : GAction G}
    (f : ActHom X Y) (g : ActHom Y Z) : ActHom X Z :=
  ⟨fun x => g.map (f.map x), fun σ x => by
    show g.map (f.map (X.act σ x)) = Z.act σ (g.map (f.map x))
    rw [f.equivariant, g.equivariant]⟩

/-- **G-集合の圏**。SGA1 主定理の右辺（π₁-集合の圏）のモデル。 -/
def GSetCat (G : Grp) : Cat where
  Obj := GAction G
  Hom := ActHom
  id := ActHom.idHom
  comp := ActHom.comp
  id_comp := fun _ => ActHom.ext (fun _ => rfl)
  comp_id := fun _ => ActHom.ext (fun _ => rfl)
  assoc := fun _ _ _ => ActHom.ext (fun _ => rfl)

/-- 制限関手: θ : H → G に沿って G-作用を H-作用に引き戻す。 -/
def restrictFunctor {H G : Grp} (θ : Hom H G) :
    Functor (GSetCat G) (GSetCat H) where
  onObj := fun X =>
    { carrier := X.carrier
      act := fun h x => X.act (θ.map h) x
      act_one := fun x => by rw [θ.map_one, X.act_one]
      act_mul := fun g h x => by rw [θ.map_mul, X.act_mul] }
  onHom := fun f => ⟨f.map, fun h x => f.equivariant (θ.map h) x⟩
  map_id := fun _ => ActHom.ext (fun _ => rfl)
  map_comp := fun _ _ => ActHom.ext (fun _ => rfl)

/-- **定理 (M19-1): 同値の輸送** — 互いに逆な群準同型の対
    （= 群同型）θ : H ⇄ G : θ' は作用圏の圏同値
    G-Set ≃ H-Set を誘導する。 -/
def restrictEquiv {H G : Grp} (θ : Hom H G) (θ' : Hom G H)
    (h1 : ∀ g, θ.map (θ'.map g) = g) (h2 : ∀ h, θ'.map (θ.map h) = h) :
    CatEquiv (GSetCat G) (GSetCat H) where
  F := restrictFunctor θ
  G := restrictFunctor θ'
  unit := fun X =>
    { hom := ⟨fun x => x, fun g x => by
        show X.act g x = X.act (θ.map (θ'.map g)) x
        rw [h1]⟩
      inv := ⟨fun x => x, fun g x => by
        show X.act (θ.map (θ'.map g)) x = X.act g x
        rw [h1]⟩
      hom_inv := ActHom.ext (fun _ => rfl)
      inv_hom := ActHom.ext (fun _ => rfl) }
  counit := fun Y =>
    { hom := ⟨fun y => y, fun h y => by
        show Y.act (θ'.map (θ.map h)) y = Y.act h y
        rw [h2]⟩
      inv := ⟨fun y => y, fun h y => by
        show Y.act h y = Y.act (θ'.map (θ.map h)) y
        rw [h2]⟩
      hom_inv := ActHom.ext (fun _ => rfl)
      inv_hom := ActHom.ext (fun _ => rfl) }
  unit_natural := fun _ => ActHom.ext (fun _ => rfl)
  counit_natural := fun _ => ActHom.ext (fun _ => rfl)

end IUT
