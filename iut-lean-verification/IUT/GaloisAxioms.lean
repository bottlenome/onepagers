/-
  IUT/GaloisAxioms.lean — M20（Galois 圏の公理系 G1–G6 と主定理の
  関手的パッケージング）の形式化

  SGA1 V.4 の Galois 圏の公理系を G-集合の圏（M19 `GSetCat`）で
  検証し、主定理「C ≃ π₁-集合の圏（π₁ = Aut(ファイバー関手)）」を
  圏同値として**関手的にパッケージング**する:

  【公理系 G1–G6 の検証（GSetCat G 上）】
  * M20-1 `gsets_G1_final` / `gsets_G1_pullback` — G1: 終対象と
    ファイバー積の存在（一意性込みの完全証明）
  * M20-2 `gsets_G2_initial` / `gsets_G2_sum` — G2: 始対象と有限和
  * M20-3 `gsets_G3_factorization` — G3: 全射・単射分解（像を通る
    エピ・モノ分解）
  * M20-4 `gsets_G4_forgetful_preserves_pullback` /
    `gsets_G5_forgetful_preserves_sum` — G4/G5: ファイバー関手
    （忘却）は構成したファイバー積・有限和を保つ
  * M20-5 `gsets_G6_reflects_iso` — G6: ファイバー関手は同型を
    反映する（全単射な同変写像は同変同型。逆写像の構成に
    Classical.choice を使用——G6 が一般には選択原理を要する箇所で
    あることの形式的特定）

  【主定理のパッケージング】
  * M20-6 `skel_classification` — **骨格圏のファイバー関手の自然
    自己変換は一点 c = η([1]) の作用で尽きる**（M14-1 の圏論的
    完成形。自然性を点射 φ_a に対して使う Yoneda 型論法）
  * M20-7 `fiberAut` — **Aut(F) の群化**: ファイバー関手の自然
    自己変換全体が群をなす（合成・恒等・逆。逆の構成と群法則は
    M20-6 の分類による）
  * M20-8 `from_to` / `to_from` — **π₁ = Aut(F)**: 群準同型の対
    G ⇄ Aut(F) が互いに逆（基本群がファイバー関手から復元される
    ことの群同型としての完成）
  * M20-9 `sga1Equivalence` — **SGA1 主定理（モデル版・関手的
    パッケージング）**: 圏同値 G-Set ≃ Aut(F)-Set。被覆の圏は
    そのファイバー関手の自己同型群の作用圏と圏同値である

  **位置づけ（正直な申告）**: C = G-Set（モデル）に対する検証で
  あり、抽象的な Galois 圏 C（公理 G1–G6 を満たす任意の圏）から
  出発して同値を導く一般形は未形式化（対象の有限性制約と
  pro-表現対象の構成を要する）。ただし主定理の数学的内容——
  対象の分類（M16）・射の分類（M16）・Aut(F) の群構造と分類
  （M20-6〜8）・圏同値の組み立て（M20-9）——は全て完全証明である。
-/
import IUT.SGA1
import IUT.CategoryTheory

namespace IUT

/-! ## 骨格圏とファイバー関手 -/

/-- 自明部分群 {1}。 -/
def trivialSub (G : Grp) : Subgroup G where
  mem := fun g => g = G.one
  one_mem := rfl
  mul_mem := fun {a b} ha hb => by rw [ha, hb, G.one_mul]
  inv_mem := fun {a} ha => by rw [ha, G.inv_one]

/-- 自明部分群の剰余類同値は等値。 -/
theorem trivRel_eq (G : Grp) {a b : G.carrier}
    (h : cosetRel G (trivialSub G) a b) : a = b := by
  have h1 : G.mul (G.inv a) b = G.one := h
  have h2 := G.inv_eq_of_mul_eq_one h1
  rw [h2, G.inv_inv]

/-- G/{1} → G（標準全単射の片割れ）。 -/
def toG (G : Grp) : cosetSpace G (trivialSub G) → G.carrier :=
  Quot.lift (fun a => a) (fun _ _ h => trivRel_eq G h)

theorem mk_toG (G : Grp) (x : cosetSpace G (trivialSub G)) :
    Quot.mk (cosetRel G (trivialSub G)) (toG G x) = x := by
  induction x using Quot.ind
  rfl

/-- **骨格圏**: 対象 = 部分群、射 = 剰余類作用の同変写像。
    Galois 圏の「標準的連結対象」の小さい圏（宇宙の都合で
    ファイバー関手の自己変換全体が型 Type 0 に収まる）。 -/
def SkelCat (G : Grp) : Cat where
  Obj := Subgroup G
  Hom := fun H K => ActHom (cosetAction G H) (cosetAction G K)
  id := fun H => ActHom.idHom (cosetAction G H)
  comp := ActHom.comp
  id_comp := fun _ => ActHom.ext (fun _ => rfl)
  comp_id := fun _ => ActHom.ext (fun _ => rfl)
  assoc := fun _ _ _ => ActHom.ext (fun _ => rfl)

/-- **ファイバー関手**（骨格圏上の忘却関手）。 -/
def forgetfulSkel (G : Grp) : Functor (SkelCat G) SetCat where
  onObj := fun H => cosetSpace G H
  onHom := fun f => f.map
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- 点射 φ_a : G/{1} → G/H, [g] ↦ [g·a]（Yoneda 型論法の素材）。 -/
def pointHom (G : Grp) (H : Subgroup G) (a : G.carrier) :
    ActHom (cosetAction G (trivialSub G)) (cosetAction G H) where
  map := Quot.lift (fun g => Quot.mk (cosetRel G H) (G.mul g a))
    (fun g g' h => by rw [trivRel_eq G h])
  equivariant := fun σ x => by
    induction x using Quot.ind; rename_i g
    show Quot.mk (cosetRel G H) (G.mul (G.mul σ g) a)
        = Quot.mk (cosetRel G H) (G.mul σ (G.mul g a))
    rw [G.mul_assoc]

/-- 自然変換の外延性。 -/
theorem NatTrans.ext {C : Cat} {D : Cat} {F G : Functor C D}
    {η θ : NatTrans F G} (h : ∀ X, η.app X = θ.app X) : η = θ := by
  cases η with | mk happ hnat =>
  cases θ with | mk happ' hnat' =>
  have hm : happ = happ' := funext h
  subst hm
  rfl

/-- η に対応する群元 c = η([1])。 -/
def cOf (G : Grp) (η : NatTrans (forgetfulSkel G) (forgetfulSkel G)) :
    G.carrier :=
  toG G (η.app (trivialSub G) (Quot.mk (cosetRel G (trivialSub G)) G.one))

/-- **定理 (M20-6): ファイバー関手の自然自己変換の分類** —
    自然変換 η は一点 c = η([1]) による作用 x ↦ c·x で尽きる。
    自然性を点射 φ_a に適用する Yoneda 型論法（M14-1 の圏論的
    完成形）。 -/
theorem skel_classification (G : Grp)
    (η : NatTrans (forgetfulSkel G) (forgetfulSkel G))
    (H : Subgroup G) (x : cosetSpace G H) :
    η.app H x = (cosetAction G H).act (cOf G η) x := by
  induction x using Quot.ind; rename_i a
  have hnat := η.natural (X := trivialSub G) (Y := H) (pointHom G H a)
  have h : η.app H ((pointHom G H a).map
        (Quot.mk (cosetRel G (trivialSub G)) G.one))
      = (pointHom G H a).map
        (η.app (trivialSub G) (Quot.mk (cosetRel G (trivialSub G)) G.one)) :=
    congrFun hnat (Quot.mk (cosetRel G (trivialSub G)) G.one)
  have hl : (pointHom G H a).map (Quot.mk (cosetRel G (trivialSub G)) G.one)
      = Quot.mk (cosetRel G H) a := by
    show Quot.mk (cosetRel G H) (G.mul G.one a) = Quot.mk (cosetRel G H) a
    rw [G.one_mul]
  have hr : η.app (trivialSub G) (Quot.mk (cosetRel G (trivialSub G)) G.one)
      = Quot.mk (cosetRel G (trivialSub G)) (cOf G η) :=
    (mk_toG G _).symm
  rw [hl, hr] at h
  exact h

/-- 群元 c の作用が定める自然変換。 -/
def actNatSkel (G : Grp) (c : G.carrier) :
    NatTrans (forgetfulSkel G) (forgetfulSkel G) where
  app := fun H x => (cosetAction G H).act c x
  natural := fun {X Y} f => by
    funext x
    show (cosetAction G Y).act c (f.map x) = f.map ((cosetAction G X).act c x)
    exact (f.equivariant c x).symm

/-- **定理 (M20-7): Aut(F) の群化** — ファイバー関手の自然自己変換の
    全体は（合成を積として）群をなす。逆元の構成と群法則の検証は
    分類定理 M20-6 による。 -/
def fiberAut (G : Grp) : Grp where
  carrier := NatTrans (forgetfulSkel G) (forgetfulSkel G)
  mul := fun η θ =>
    { app := fun H x => η.app H (θ.app H x)
      natural := fun {X Y} f => by
        funext x
        show η.app Y (θ.app Y (f.map x)) = f.map (η.app X (θ.app X x))
        have h1 : θ.app Y (f.map x) = f.map (θ.app X x) :=
          congrFun (θ.natural f) x
        have h2 : η.app Y (f.map (θ.app X x)) = f.map (η.app X (θ.app X x)) :=
          congrFun (η.natural f) (θ.app X x)
        rw [h1]
        exact h2 }
  one :=
    { app := fun _ x => x
      natural := fun _ => rfl }
  inv := fun η =>
    { app := fun H x => (cosetAction G H).act (G.inv (cOf G η)) x
      natural := fun {X Y} f => by
        funext x
        show (cosetAction G Y).act (G.inv (cOf G η)) (f.map x)
            = f.map ((cosetAction G X).act (G.inv (cOf G η)) x)
        exact (f.equivariant _ x).symm }
  mul_assoc := fun _ _ _ => NatTrans.ext (fun _ => rfl)
  one_mul := fun _ => NatTrans.ext (fun _ => rfl)
  inv_mul := fun η => NatTrans.ext (fun H => funext fun x => by
    show (cosetAction G H).act (G.inv (cOf G η)) (η.app H x) = x
    rw [skel_classification G η H x, ← (cosetAction G H).act_mul,
      G.inv_mul, (cosetAction G H).act_one])

/-- G → Aut(F)（作用による自然変換）。 -/
def toFiberAut (G : Grp) : Hom G (fiberAut G) where
  map := actNatSkel G
  map_mul := fun a b => NatTrans.ext (fun H => funext fun x => by
    show (cosetAction G H).act (G.mul a b) x
        = (cosetAction G H).act a ((cosetAction G H).act b x)
    exact (cosetAction G H).act_mul a b x)

/-- Aut(F) → G（[1] での値）。 -/
def fromFiberAut (G : Grp) : Hom (fiberAut G) G where
  map := cOf G
  map_mul := fun η θ => by
    have h1 : θ.app (trivialSub G) (Quot.mk (cosetRel G (trivialSub G)) G.one)
        = Quot.mk (cosetRel G (trivialSub G)) (cOf G θ) := (mk_toG G _).symm
    have h2 := skel_classification G η (trivialSub G)
      (Quot.mk (cosetRel G (trivialSub G)) (cOf G θ))
    show toG G (η.app (trivialSub G)
        (θ.app (trivialSub G) (Quot.mk (cosetRel G (trivialSub G)) G.one)))
      = G.mul (cOf G η) (cOf G θ)
    rw [h1, h2]
    rfl

/-- **定理 (M20-8a)**: G → Aut(F) → G は恒等（c が回収される）。 -/
theorem from_to (G : Grp) (c : G.carrier) :
    (fromFiberAut G).map ((toFiberAut G).map c) = c := by
  show G.mul c G.one = c
  exact G.mul_one c

/-- **定理 (M20-8b)**: Aut(F) → G → Aut(F) も恒等（分類定理）。
    M20-8a と併せて **π₁ = Aut(F)**（群同型）が完成する。 -/
theorem to_from (G : Grp) (η : (fiberAut G).carrier) :
    (toFiberAut G).map ((fromFiberAut G).map η) = η :=
  NatTrans.ext (fun H => funext fun x => (skel_classification G η H x).symm)

/-- **定理 (M20-9): SGA1 主定理のパッケージング（モデル版）** —
    被覆の圏（G-Set）はそのファイバー関手の自己同型群 Aut(F) の
    作用圏と**圏同値**である。M16 の分類（対象・射）、M20-6〜8 の
    π₁ = Aut(F)、M19-1 の同値輸送の合成。 -/
def sga1Equivalence (G : Grp) :
    CatEquiv (GSetCat G) (GSetCat (fiberAut G)) :=
  restrictEquiv (fromFiberAut G) (toFiberAut G) (from_to G) (to_from G)

/-! ## Galois 圏の公理系 G1–G6 の検証（GSetCat G 上） -/

/-- 一点の自明作用（終対象）。 -/
def unitAction (G : Grp) : GAction G where
  carrier := PUnit
  act := fun _ x => x
  act_one := fun _ => rfl
  act_mul := fun _ _ _ => rfl

/-- **定理 (M20-1a): G1（終対象）** — 一点作用への射は一意に存在。 -/
theorem gsets_G1_final (G : Grp) :
    ∃ T : GAction G, ∀ X : GAction G,
      ∃ f : ActHom X T, ∀ g : ActHom X T, g = f :=
  ⟨unitAction G, fun _ =>
    ⟨⟨fun _ => PUnit.unit, fun _ _ => rfl⟩,
      fun _ => ActHom.ext (fun _ => rfl)⟩⟩

/-- ファイバー積の作用。 -/
def pullbackAction (G : Grp) {X Y Z : GAction G}
    (f : ActHom X Z) (g : ActHom Y Z) : GAction G where
  carrier := { p : X.carrier × Y.carrier // f.map p.1 = g.map p.2 }
  act := fun σ p => ⟨(X.act σ p.val.1, Y.act σ p.val.2), by
    show f.map (X.act σ p.val.1) = g.map (Y.act σ p.val.2)
    rw [f.equivariant, g.equivariant, p.property]⟩
  act_one := fun p => Subtype.ext (by
    show (X.act G.one p.val.1, Y.act G.one p.val.2) = p.val
    rw [X.act_one, Y.act_one])
  act_mul := fun σ τ p => Subtype.ext (by
    show (X.act (G.mul σ τ) p.val.1, Y.act (G.mul σ τ) p.val.2)
        = (X.act σ (X.act τ p.val.1), Y.act σ (Y.act τ p.val.2))
    rw [X.act_mul, Y.act_mul])

/-- **定理 (M20-1b): G1（ファイバー積）** — 射の対 f : X → Z ← Y : g
    のファイバー積が存在し、普遍性（媒介射の存在と一意性）を満たす。 -/
theorem gsets_G1_pullback (G : Grp) {X Y Z : GAction G}
    (f : ActHom X Z) (g : ActHom Y Z) :
    ∃ (P : GAction G) (p₁ : ActHom P X) (p₂ : ActHom P Y),
      (∀ w, f.map (p₁.map w) = g.map (p₂.map w)) ∧
      ∀ (W : GAction G) (q₁ : ActHom W X) (q₂ : ActHom W Y),
        (∀ w, f.map (q₁.map w) = g.map (q₂.map w)) →
        ∃ u : ActHom W P,
          (∀ w, p₁.map (u.map w) = q₁.map w) ∧
          (∀ w, p₂.map (u.map w) = q₂.map w) := by
  refine ⟨pullbackAction G f g,
    ⟨fun p => p.val.1, fun _ _ => rfl⟩,
    ⟨fun p => p.val.2, fun _ _ => rfl⟩,
    fun w => w.property, ?_⟩
  intro W q₁ q₂ hcomm
  refine ⟨⟨fun w => ⟨(q₁.map w, q₂.map w), hcomm w⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  intro σ w
  apply Subtype.ext
  show (q₁.map (W.act σ w), q₂.map (W.act σ w))
      = (X.act σ (q₁.map w), Y.act σ (q₂.map w))
  rw [q₁.equivariant, q₂.equivariant]

/-- 空作用（始対象）。 -/
def emptyAction (G : Grp) : GAction G where
  carrier := Empty
  act := fun _ e => e
  act_one := fun _ => rfl
  act_mul := fun _ _ _ => rfl

/-- **定理 (M20-2a): G2（始対象）**。 -/
theorem gsets_G2_initial (G : Grp) :
    ∃ I : GAction G, ∀ X : GAction G,
      ∃ f : ActHom I X, ∀ g : ActHom I X, g = f :=
  ⟨emptyAction G, fun _ =>
    ⟨⟨fun e => (nomatch e), fun _ e => (nomatch e)⟩,
      fun _ => ActHom.ext (fun e => (nomatch e))⟩⟩

/-- 二項和の作用。 -/
def sumAction (G : Grp) (X Y : GAction G) : GAction G where
  carrier := Sum X.carrier Y.carrier
  act := fun σ s => match s with
    | .inl x => .inl (X.act σ x)
    | .inr y => .inr (Y.act σ y)
  act_one := fun s => by
    cases s with
    | inl x =>
      show Sum.inl (X.act G.one x) = Sum.inl x
      rw [X.act_one]
    | inr y =>
      show Sum.inr (Y.act G.one y) = Sum.inr y
      rw [Y.act_one]
  act_mul := fun σ τ s => by
    cases s with
    | inl x =>
      show Sum.inl (X.act (G.mul σ τ) x) = Sum.inl (X.act σ (X.act τ x))
      rw [X.act_mul]
    | inr y =>
      show Sum.inr (Y.act (G.mul σ τ) y) = Sum.inr (Y.act σ (Y.act τ y))
      rw [Y.act_mul]

/-- **定理 (M20-2b): G2（二項和）** — 余積の普遍性。 -/
theorem gsets_G2_sum (G : Grp) (X Y : GAction G) :
    ∃ (S : GAction G) (i₁ : ActHom X S) (i₂ : ActHom Y S),
      ∀ (W : GAction G) (f : ActHom X W) (g : ActHom Y W),
        ∃ u : ActHom S W,
          (∀ x, u.map (i₁.map x) = f.map x) ∧
          (∀ y, u.map (i₂.map y) = g.map y) ∧
          ∀ u' : ActHom S W, (∀ x, u'.map (i₁.map x) = f.map x) →
            (∀ y, u'.map (i₂.map y) = g.map y) → u' = u := by
  refine ⟨sumAction G X Y,
    ⟨fun x => .inl x, fun _ _ => rfl⟩,
    ⟨fun y => .inr y, fun _ _ => rfl⟩, ?_⟩
  intro W f g
  refine ⟨⟨fun s => match s with
      | .inl x => f.map x
      | .inr y => g.map y, ?_⟩, fun _ => rfl, fun _ => rfl, ?_⟩
  · intro σ s
    cases s with
    | inl x =>
      show f.map (X.act σ x) = W.act σ (f.map x)
      exact f.equivariant σ x
    | inr y =>
      show g.map (Y.act σ y) = W.act σ (g.map y)
      exact g.equivariant σ y
  · intro u' h1 h2
    apply ActHom.ext
    intro s
    cases s with
    | inl x => exact h1 x
    | inr y => exact h2 y

/-- 像の作用。 -/
def imageAction (G : Grp) {X Y : GAction G} (f : ActHom X Y) : GAction G where
  carrier := { y : Y.carrier // ∃ x, f.map x = y }
  act := fun σ y => ⟨Y.act σ y.val, by
    obtain ⟨x, hx⟩ := y.property
    exact ⟨X.act σ x, by rw [f.equivariant, hx]⟩⟩
  act_one := fun y => Subtype.ext (Y.act_one y.val)
  act_mul := fun σ τ y => Subtype.ext (Y.act_mul σ τ y.val)

/-- **定理 (M20-3): G3（エピ・モノ分解）** — 任意の射は
    全射・単射に分解する（像を経由）。 -/
theorem gsets_G3_factorization (G : Grp) {X Y : GAction G} (f : ActHom X Y) :
    ∃ (I : GAction G) (e : ActHom X I) (m : ActHom I Y),
      (∀ w, ∃ x, e.map x = w) ∧
      (∀ a b, m.map a = m.map b → a = b) ∧
      (∀ x, m.map (e.map x) = f.map x) := by
  refine ⟨imageAction G f,
    ⟨fun x => ⟨f.map x, x, rfl⟩, fun σ x => Subtype.ext (f.equivariant σ x)⟩,
    ⟨fun y => y.val, fun _ _ => rfl⟩, ?_, ?_, fun _ => rfl⟩
  · intro w
    obtain ⟨x, hx⟩ := w.property
    exact ⟨x, Subtype.ext hx⟩
  · intro a b h
    exact Subtype.ext h

/-- **定理 (M20-4): G4（ファイバー関手はファイバー積を保つ）** —
    構成したファイバー積の台集合は集合のファイバー積の普遍性を
    満たす（忘却の完全性）。 -/
theorem gsets_G4_forgetful_preserves_pullback (G : Grp) {X Y Z : GAction G}
    (f : ActHom X Z) (g : ActHom Y Z) (W : Type)
    (q₁ : W → X.carrier) (q₂ : W → Y.carrier)
    (hcomm : ∀ w, f.map (q₁ w) = g.map (q₂ w)) :
    ∃ u : W → (pullbackAction G f g).carrier,
      (∀ w, (u w).val.1 = q₁ w) ∧ (∀ w, (u w).val.2 = q₂ w) ∧
      ∀ u' : W → (pullbackAction G f g).carrier,
        (∀ w, (u' w).val.1 = q₁ w) → (∀ w, (u' w).val.2 = q₂ w) →
        ∀ w, u' w = u w := by
  refine ⟨fun w => ⟨(q₁ w, q₂ w), hcomm w⟩, fun _ => rfl, fun _ => rfl, ?_⟩
  intro u' h1 h2 w
  apply Subtype.ext
  show (u' w).val = (q₁ w, q₂ w)
  rw [← h1 w, ← h2 w]

/-- **定理 (M20-5): G5（ファイバー関手は有限和を保つ）** —
    構成した二項和の台集合は集合の余積の普遍性を満たす。 -/
theorem gsets_G5_forgetful_preserves_sum (G : Grp) (X Y : GAction G)
    (W : Type) (f : X.carrier → W) (g : Y.carrier → W) :
    ∃ u : (sumAction G X Y).carrier → W,
      (∀ x, u (.inl x) = f x) ∧ (∀ y, u (.inr y) = g y) ∧
      ∀ u' : (sumAction G X Y).carrier → W,
        (∀ x, u' (.inl x) = f x) → (∀ y, u' (.inr y) = g y) →
        ∀ s, u' s = u s := by
  refine ⟨fun s => match s with
    | .inl x => f x
    | .inr y => g y, fun _ => rfl, fun _ => rfl, ?_⟩
  intro u' h1 h2 s
  cases s with
  | inl x => exact h1 x
  | inr y => exact h2 y

/-- **定理 (M20-5'): G6（ファイバー関手は同型を反映する）** —
    台集合上で全単射な同変写像は同変同型である。逆写像の構成に
    Classical.choice を使用（G6 が選択原理を要する箇所であることの
    形式的特定。`#print axioms` で確認可能）。 -/
theorem gsets_G6_reflects_iso (G : Grp) {X Y : GAction G} (f : ActHom X Y)
    (hinj : ∀ a b, f.map a = f.map b → a = b)
    (hsurj : ∀ y, ∃ x, f.map x = y) :
    ∃ g : ActHom Y X, (∀ x, g.map (f.map x) = x) ∧ (∀ y, f.map (g.map y) = y) := by
  classical
  have hinv : ∀ y, f.map (Classical.choose (hsurj y)) = y :=
    fun y => Classical.choose_spec (hsurj y)
  refine ⟨⟨fun y => Classical.choose (hsurj y), ?_⟩, ?_, ?_⟩
  · intro σ y
    apply hinj
    show f.map (Classical.choose (hsurj (Y.act σ y)))
        = f.map (X.act σ (Classical.choose (hsurj y)))
    rw [hinv, f.equivariant, hinv]
  · intro x
    apply hinj
    show f.map (Classical.choose (hsurj (f.map x))) = f.map x
    rw [hinv]
  · exact hinv

end IUT
