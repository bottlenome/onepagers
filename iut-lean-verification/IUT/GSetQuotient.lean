/-
  # M149F: G-集合の商構成 — 商公理（G2 後半）のモデル側充足（柱A A-2 入口）

  M22（IUT/SGA1Completion.lean）の正直申告: SGA1 主定理の対象レベル
  （本質的全射性）は**商公理（G2 後半: 有限自己同型群による商の存在）**
  と pro-対象を要し未形式化。本モジュールはこのうち**商公理のモデル側
  （G-Set 圏）充足**を閉じる: G-集合 X と同変自己写像のリスト as による
  軌道空間 X/as を `Quot` で構成し、G-作用の降下と普遍性を証明する。

  * M149F-1 `autOrbitRel` — 同変自己写像のリスト as が生成する一歩関係
    r x y :↔ ∃ a ∈ as, y = a x。`Quot r` は r が同値関係でなくても
    商として機能する（Quot.lift の健全性条件は r a b → f a = f b のみ）
    ので、推移閉包を取らずにこの一歩関係で商を構成できる
  * M149F-2 `gsetQuot` — **軌道空間の G-集合化**: carrier := Quot r、
    G-作用は g·[x] := [g·x]。well-definedness が本丸の非自明点:
    r x y（y = a x）のとき g·y = g·(a x) = a(g·x)（**a の同変性**）
    ゆえ r (g·x) (g·y)、Quot.sound で降りる
  * M149F-3 `gsetQuotProj` — 射影 X → X/as（同変射、同変性は rfl）
  * M149F-4 `gsetQuot_coeq` — **不変性**: 射影は as の各元を等化する
    （proj ∘ a = proj、Quot.sound の直接適用）
  * M149F-5 `gsetQuotLift` / `gsetQuot_univ` — **普遍性**: as-不変な
    同変写像 f : X → Y は商を一意に経由する（∃! の展開形: 存在 +
    一意性）。存在は Quot.lift、同変性は Quot.ind、一意性は
    Quot.ind + 射影の全射性
  * M149F-6 `QuotientAxiom` / `gsetQuotientAxiom` /
    `gset_satisfies_quotient` — **G2 商公理の定式化とモデル側充足**:
    圏 C に対する「有限自己同型族（CatIso のリスト、M22-1 の
    選択公理なし群化と同じ台）による余等化子の存在」を公理データ
    `QuotientAxiom C` として導入（抽象 Galois 圏 D には
    `QuotientAxiom D.C` として課す）し、G-Set モデル `GSetCat G` が
    これを満たすことを M149F-2〜5 を束ねて証明
  * M149F-7 `GSetQuotientData` / `gsetQuotient_exists` — 総括

  **意義**: SGA1 主定理の対象レベル（本質的全射性 = 柱A A-2）に必要な
  商公理（G2 後半）のモデル側が、Quot 構成により**選択公理なしに**
  充足される。M22-8（降下射の構成に Classical.choice）と対照的に、
  商対象の構成自体は choice-free であることの実証。

  **位置づけ（正直な申告）**: 本モジュールが与えるのは商公理の
  **モデル側**（G-Set 圏での充足）である。抽象側で商公理と pro-対象
  から本質的全射性を導出する部分（連結対象がガロア対象に支配される
  こと・pro-表現対象の構成）は次層。また `QuotientAxiom` は自己同型
  リストの「群をなす」条件を課さない一般形で述べた（商の存在・普遍性
  には不要であり、有限自己同型群による商はリストに群の元を並べた
  特殊例として含まれる）。橋渡し定理 `gset_satisfies_quotient` のみ
  Classical.choice に依存するが、これは型が M21-8 の `gsetGaloisData`
  （G6 に choice）に言及するためであり、商構成そのもの（M149F-1〜6）の
  公理は [Quot.sound] 以下。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.SGA1Completion

namespace IUT

universe u v

/-! ## M149F-0: リスト補題（core の名前変動を避けた自前版） -/

/-- map はメンバーシップを保つ。 -/
theorem listMemMap {α β : Type _} (f : α → β) {a : α} {l : List α}
    (h : a ∈ l) : f a ∈ List.map f l := by
  induction h with
  | head _ => exact List.Mem.head _
  | tail b _ ih => exact List.Mem.tail _ ih

/-- map されたリストの元は原像を持つ。 -/
theorem listExistsOfMemMap {α β : Type _} (f : α → β) {b : β} :
    ∀ {l : List α}, b ∈ List.map f l → ∃ a, a ∈ l ∧ f a = b := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons a as ih =>
    intro h
    cases h with
    | head => exact ⟨a, List.Mem.head _, rfl⟩
    | tail _ h' =>
      obtain ⟨a', ha', he⟩ := ih h'
      exact ⟨a', List.Mem.tail _ ha', he⟩

/-! ## M149F-1: 軌道関係（一歩版） -/

/-- **軌道関係（一歩版）**: 同変自己写像のリスト as が生成する関係
    r x y :↔ ∃ a ∈ as, y = a x。同値関係である必要はない
    （`Quot.lift` の健全性条件は一歩ぶんで足りる）。 -/
def autOrbitRel {G : Grp} (X : GAction G) (as : List (ActHom X X))
    (x y : X.carrier) : Prop :=
  ∃ a, a ∈ as ∧ y = a.map x

/-- 軌道関係は G-作用で保たれる（well-definedness の核心）:
    y = a x なら g·y = g·(a x) = a(g·x)（a の**同変性**）。 -/
theorem autOrbitRel_act {G : Grp} (X : GAction G) (as : List (ActHom X X))
    (g : G.carrier) {x y : X.carrier} (h : autOrbitRel X as x y) :
    autOrbitRel X as (X.act g x) (X.act g y) := by
  obtain ⟨a, ha, hy⟩ := h
  refine ⟨a, ha, ?_⟩
  rw [hy, a.equivariant]

/-! ## M149F-2: 軌道空間の G-集合化 -/

/-- **G-集合の商**（M149F-2）: carrier は `Quot (autOrbitRel X as)`、
    G-作用は代表元経由 g·[x] := [g·x]（well-definedness は
    `autOrbitRel_act` + Quot.sound）。選択公理不使用。 -/
def gsetQuot {G : Grp} (X : GAction G) (as : List (ActHom X X)) :
    GAction G where
  carrier := Quot (autOrbitRel X as)
  act := fun g => Quot.lift (fun x => Quot.mk _ (X.act g x))
    (fun x y hxy => Quot.sound (autOrbitRel_act X as g hxy))
  act_one := by
    intro q
    induction q using Quot.ind
    rename_i x
    exact congrArg (Quot.mk _) (X.act_one x)
  act_mul := by
    intro g h q
    induction q using Quot.ind
    rename_i x
    exact congrArg (Quot.mk _) (X.act_mul g h x)

/-! ## M149F-3: 射影 -/

/-- **同変射影**（M149F-3）: X → X/as, x ↦ [x]。同変性は定義から rfl。 -/
def gsetQuotProj {G : Grp} (X : GAction G) (as : List (ActHom X X)) :
    ActHom X (gsetQuot X as) :=
  ⟨fun x => Quot.mk _ x, fun _ _ => rfl⟩

/-- 射影は全射（Quot.mk の全射性 = Quot.ind）。 -/
theorem gsetQuotProj_surj {G : Grp} (X : GAction G)
    (as : List (ActHom X X)) (q : (gsetQuot X as).carrier) :
    ∃ x, (gsetQuotProj X as).map x = q := by
  induction q using Quot.ind
  rename_i x
  exact ⟨x, rfl⟩

/-! ## M149F-4: 不変性（余等化） -/

/-- **定理 (M149F-4): 射影は as の各元を等化する** — a ∈ as なら
    proj (a x) = proj x（Quot.sound の直接適用）。 -/
theorem gsetQuot_coeq {G : Grp} (X : GAction G) (as : List (ActHom X X))
    (a : ActHom X X) (ha : a ∈ as) (x : X.carrier) :
    (gsetQuotProj X as).map (a.map x) = (gsetQuotProj X as).map x :=
  (Quot.sound ⟨a, ha, rfl⟩).symm

/-! ## M149F-5: 普遍性 -/

/-- **降下写像**（M149F-5a）: as-不変な同変写像 f : X → Y を商に降ろす。
    健全性は不変性 hf そのもの、同変性は Quot.ind で代表元に還元。 -/
def gsetQuotLift {G : Grp} (X : GAction G) (as : List (ActHom X X))
    (Y : GAction G) (f : ActHom X Y)
    (hf : ∀ a, a ∈ as → ∀ x, f.map (a.map x) = f.map x) :
    ActHom (gsetQuot X as) Y where
  map := Quot.lift f.map (fun x y hxy => by
    obtain ⟨a, ha, hy⟩ := hxy
    rw [hy]
    exact (hf a ha x).symm)
  equivariant := by
    intro g q
    induction q using Quot.ind
    rename_i x
    exact f.equivariant g x

/-- 降下写像は射影を経由して f に戻る（定義から rfl）。 -/
theorem gsetQuotLift_comp {G : Grp} (X : GAction G)
    (as : List (ActHom X X)) (Y : GAction G) (f : ActHom X Y)
    (hf : ∀ a, a ∈ as → ∀ x, f.map (a.map x) = f.map x) :
    ActHom.comp (gsetQuotProj X as) (gsetQuotLift X as Y f hf) = f :=
  ActHom.ext (fun _ => rfl)

/-- **定理 (M149F-5b): 商の普遍性** — as-不変な同変写像 f : X → Y は
    商 X/as を**一意に**経由する（∃! の展開形: 存在 + 一意性。
    core Lean に ∃! 記法がないため明示形で述べる）。存在は Quot.lift、
    一意性は Quot.ind（射影の全射性）+ ActHom.ext（funext は
    Quot.sound 由来の core 定理なので選択公理不使用）。 -/
theorem gsetQuot_univ {G : Grp} (X : GAction G) (as : List (ActHom X X))
    (Y : GAction G) (f : ActHom X Y)
    (hf : ∀ a, a ∈ as → ∀ x, f.map (a.map x) = f.map x) :
    ∃ h : ActHom (gsetQuot X as) Y,
      ActHom.comp (gsetQuotProj X as) h = f ∧
      ∀ h' : ActHom (gsetQuot X as) Y,
        ActHom.comp (gsetQuotProj X as) h' = f → h' = h := by
  refine ⟨gsetQuotLift X as Y f hf, gsetQuotLift_comp X as Y f hf, ?_⟩
  intro h' hh'
  apply ActHom.ext
  intro q
  induction q using Quot.ind
  rename_i x
  show h'.map ((gsetQuotProj X as).map x)
      = (gsetQuotLift X as Y f hf).map ((gsetQuotProj X as).map x)
  have h1 : h'.map ((gsetQuotProj X as).map x) = f.map x :=
    congrFun (congrArg ActHom.map hh') x
  rw [h1]
  rfl

/-! ## M149F-6: G2 商公理の定式化とモデル側充足 -/

/-- **商公理（G2 後半）**: 圏 C における「有限自己同型族
    （`CatIso` のリスト — M22-1 の選択公理なし群化 `autGrp` と同じ台）
    による余等化子（商対象）の存在」。SGA1 の G2 が要求する
    『有限自己同型群による商の存在』の公理データ化。商対象 Qt・
    射影 qproj・不変性 qproj_coeq・降下 qlift とその普遍性
    （qlift_comp・qlift_unique）からなる。抽象 Galois 圏
    D : GaloisCatData には `QuotientAxiom D.C` として課す
    （公理は圏構造のみに言及するので Cat でパラメータ化——
    こうすることでモデル側充足が M21-8 の G6 の Classical.choice を
    継承しない）。 -/
structure QuotientAxiom (C : Cat.{u, v}) where
  Qt : (X : C.Obj) → List (CatIso C X X) → C.Obj
  qproj : (X : C.Obj) → (as : List (CatIso C X X)) →
    C.Hom X (Qt X as)
  qproj_coeq : ∀ (X : C.Obj) (as : List (CatIso C X X))
    (a : CatIso C X X), a ∈ as →
    C.comp a.hom (qproj X as) = qproj X as
  qlift : {X W : C.Obj} → (as : List (CatIso C X X)) →
    (f : C.Hom X W) → (∀ a, a ∈ as → C.comp a.hom f = f) →
    C.Hom (Qt X as) W
  qlift_comp : ∀ {X W : C.Obj} (as : List (CatIso C X X))
    (f : C.Hom X W) (hf : ∀ a, a ∈ as → C.comp a.hom f = f),
    C.comp (qproj X as) (qlift as f hf) = f
  qlift_unique : ∀ {X W : C.Obj} (as : List (CatIso C X X))
    (h h' : C.Hom (Qt X as) W),
    C.comp (qproj X as) h = C.comp (qproj X as) h' → h = h'

/-- CatIso のリストから hom 成分の同変自己写像リストへ（モデル側の
    語彙合わせ: `GSetCat G` の自己同型の台は `ActHom X X`）。 -/
def gsetIsoHoms {G : Grp} {X : GAction G}
    (as : List (CatIso (GSetCat G) X X)) : List (ActHom X X) :=
  List.map CatIso.hom as

/-- 射レベルの不変性の読み出し: GSetCat での comp a.hom f = f から
    各点での f (a x) = f x を取り出す。 -/
theorem gset_coeq_pointwise {G : Grp} {X W : GAction G}
    (f : ActHom X W) (a : ActHom X X)
    (h : ActHom.comp a f = f) (x : X.carrier) :
    f.map (a.map x) = f.map x :=
  congrFun (congrArg ActHom.map h) x

/-- **定理 (M149F-6): モデルは商公理を満たす** — G-Set 圏
    `GSetCat G` は `QuotientAxiom` の全フィールドを
    M149F-2〜5 の Quot 構成で充足する。**選択公理不使用**
    （M22-8 の降下射構成が Classical.choice を要したのと対照的に、
    商対象の構成自体は choice-free）。 -/
def gsetQuotientAxiom (G : Grp) : QuotientAxiom (GSetCat G) where
  Qt := fun X as => gsetQuot X (gsetIsoHoms as)
  qproj := fun X as => gsetQuotProj X (gsetIsoHoms as)
  qproj_coeq := fun X as a ha => ActHom.ext (fun x =>
    gsetQuot_coeq X (gsetIsoHoms as) a.hom
      (listMemMap CatIso.hom ha) x)
  qlift := fun {X W} as f hf =>
    gsetQuotLift X (gsetIsoHoms as) W f (by
      intro b hb x
      obtain ⟨a, ha, he⟩ := listExistsOfMemMap CatIso.hom hb
      rw [← he]
      exact gset_coeq_pointwise f a.hom (hf a ha) x)
  qlift_comp := fun _ _ _ => ActHom.ext (fun _ => rfl)
  qlift_unique := fun {X W} as h h' hcomp => by
    apply ActHom.ext
    intro q
    induction q using Quot.ind
    rename_i x
    exact congrFun (congrArg ActHom.map hcomp) x

/-- 商公理のモデル側充足の抽象 Galois 圏への橋渡し（存在形）:
    `(gsetGaloisData G).C = GSetCat G`（定義的等号）なので M149F-6 が
    そのまま通用する。**注**: この言明のみ Classical.choice に依存
    するが、それは型が `gsetGaloisData`（M21-8、G6 フィールドに
    choice）に言及するためであり、商構成自体（M149F-1〜6）は
    [Quot.sound] のみ。 -/
theorem gset_satisfies_quotient (G : Grp) :
    Nonempty (QuotientAxiom (gsetGaloisData G).C) :=
  ⟨gsetQuotientAxiom G⟩

/-! ## M149F-7: 総括 -/

/-- **総括データ**（M149F-7）: 群 G と、その G-Set 圏が商公理を
    満たすことの証拠の組。 -/
structure GSetQuotientData where
  G : Grp
  ax : QuotientAxiom (GSetCat G)

/-- 総括の witness（G = ℤ、M21-8/M22-8 の無矛盾性証明と同じモデル）。 -/
def gsetQuotientWitness : GSetQuotientData :=
  ⟨intGrp, gsetQuotientAxiom intGrp⟩

/-- **定理 (M149F-7): 商公理を満たす G-Set モデルの存在**。 -/
theorem gsetQuotient_exists : Nonempty GSetQuotientData :=
  ⟨gsetQuotientWitness⟩

end IUT
