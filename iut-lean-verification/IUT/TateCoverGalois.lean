/-
  # M195F: Tate 被覆圏の GaloisCatData 化 — 有限連続被覆圏を抽象 Galois 圏として実体化（柱A A-3β-3・並行部品）

  A-3（エタール的入力の代理化）β 系列の第三歩。A-3β-1（M188F
  `TateCoverGroup.lean`）の群三層束ね、A-3β-2（M191F
  `TateCoverCat.lean`）の有限連続被覆圏の操作構造を入力に、
  **Tate 曲線の有限連続被覆の圏を抽象 Galois 圏 `GaloisCatData`
  （M21 `AbstractGalois.lean`）のインスタンスとして実体化**する。
  これにより M21 が公理 G1–G6 だけから導いた抽象主定理の骨格
  （ファイバー関手の忠実性・evaluation の単射性・ガロア対象の
  群復元）が、そのまま Tate 被覆圏に適用可能になる。

  戦略: `gsetGaloisData`（G-Set 圏の GaloisCatData 充足、M21-8）を
  テンプレートに、圏 C を有限連続被覆圏に、ファイバー積・和・像・
  終始対象を **M191F が有限性・連続性の保存を既に証明した被覆操作**
  （`pullbackCover`・`sumCover`・`unitCover`・`emptyCover`）に置き換える。
  有限性/連続性の再証明はせず M191F の資産をそのまま再利用する。

  * M195F-1 `tateCoverCat` / `tateFiberFunctor` — 被覆圏（対象 =
    `TateCover`・射 = 連続同変写像 `ActHom`・恒等/合成は M19 の
    `ActHom.idHom`/`ActHom.comp`）と、ファイバー関手 F : C → Set
    （台集合への忘却）。M19 `GSetCat` の被覆部分圏版
  * M195F-2 `imageCover` — G3（エピ・モノ分解）の像被覆。像の台は
    標的の部分型で有限（M191F-3c `finite_subtype`）、作用は標的の
    作用の制限だから同レベルで連続。M191F が扱わなかった唯一の
    被覆操作をここで補う
  * M195F-3 `tateGaloisData` — **`GaloisCatData` インスタンス本体**。
    G1（終対象 `unitCover`・ファイバー積 `pullbackCover`）・
    G2（始対象 `emptyCover`・二項和 `sumCover`）・G3（像 `imageCover`）・
    G4（F はファイバー積と終対象を保つ）・G5（F は始対象を空に送る）・
    G6（F は同型を反映する、`gsets_G6_reflects_iso` の再利用）を充足
  * M195F-4 `tateGalois_consistent` / `tateGaloisData_faithful` —
    無矛盾性（`Nonempty GaloisCatData`）と、M21-4 のファイバー忠実性
    がこのインスタンスに適用された姿（G1+G4+G6 からの導出）
  * M195F-5 `tateGalois_profinite_compat` — A-3β-1 との接続: 被覆の
    作用はデッキ座標経由でも副有限完備化 ẑ 経由でも一致（M191F-7
    `cover_deck_profinite_compat` の Galois 圏文脈での再掲）
  * M195F-6 `TateCoverGaloisData` / `tateCoverGaloisData` /
    `tateCoverGalois_exists` — 総括データ・証人・存在定理

  **意義**: 「具体提示された π₁ の有限連続作用の圏」（M191F）が
  SGA1 V.4 の抽象 Galois 圏の公理系 G1–G6 を**全て充足する**ことが、
  既存資産（M191F の被覆操作の有限性・連続性保存 + M20 の GAction
  操作 + M21 の抽象公理系）の再利用だけで機械検証された。よって
  M21 が公理のみから導いた「ファイバー関手は忠実・連結被覆の射は
  一点で決まる・ガロア対象の自己同型群 ≅ ファイバー」という
  抽象主定理の骨格が、Tate 被覆圏にそのまま降りる。G6 の同型反映
  フィールドのみ `gsets_G6_reflects_iso` 経由で M20-5 の
  `Classical.choice` を継承する（新規の選択公理使用はなし）。

  **正直な限定**: (1) 充足するのは `GaloisCatData` の G1–G6
  フィールド（有限極限・余極限・像分解・ファイバー関手の保存性/
  同型反映）である。SGA1 一般論の後半——十分多くのガロア対象の
  存在・pro-表現対象の構成・それによる圏同値——は M21 と同じく
  未形式化（`AbstractGalois.lean` の正直申告を継承）。主定理
  `Aut(F) = π₁` の被覆圏版（ファイバー関手の自己同型群がテンパード
  π₁ ẑ を復元する完成形）は **A-3β-4** に譲る。
  (2) 被覆はデッキ群 ℤ（幾何的部分）の連続作用に限る。数論的 π₁ =
  Π 全体（G_K 方向）の作用や連結性・ガロア対象の実際の分類は
  扱わない。(3) 「連続性」は位相を導入せず「有限商 ℤ/n を経由
  （合同不変）」で代理する（M13/M191F と同じ代数側形式化）。
  (4) π₁ の提示は幾何からの**入力**（`tateModel`）であり、実際の
  Tate 曲線から計算された不変量でもスキーム論的エタール性でもない。
  デッキ群も玩具モデル ℤ である。(5) G6 の同型反映は
  `gsets_G6_reflects_iso`（M20-5）の再利用であり、その逆写像構成の
  `Classical.choice` を継承する。証明本体での新規 Classical.choice
  導入はなく、他フィールドは全て構成的。

  sorry なし・新規 Classical.choice なし。サブエージェント並行部品。
-/
import IUT.TateCoverCat

namespace IUT

/-! ## M195F-1: 被覆圏とファイバー関手 -/

/-- **Tate 有限連続被覆圏（M195F-1）**: 対象 = `TateCover`
    （有限連続被覆）・射 = 連続同変写像 `ActHom`。恒等/合成は M19 の
    `ActHom.idHom`/`ActHom.comp`。M19 `GSetCat` を有限連続被覆の
    部分圏へ制限したもの（`GaloisCatData` の圏 C）。 -/
def tateCoverCat : Cat where
  Obj := TateCover
  Hom := fun X Y => ActHom X.carrier Y.carrier
  id := fun X => ActHom.idHom X.carrier
  comp := ActHom.comp
  id_comp := fun _ => ActHom.ext (fun _ => rfl)
  comp_id := fun _ => ActHom.ext (fun _ => rfl)
  assoc := fun _ _ _ => ActHom.ext (fun _ => rfl)

/-- **ファイバー関手（M195F-1）**: 被覆をその台有限集合に送る忘却
    関手 F : C → Set。射は台写像。M20 のファイバー関手
    `forgetfulG` の被覆圏版（`GaloisCatData` の F）。 -/
def tateFiberFunctor : Functor tateCoverCat SetCat where
  onObj := fun X => X.carrier.carrier
  onHom := fun f => f.map
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-! ## M195F-2: 像被覆（G3 の分解対象） -/

/-- **像被覆（M195F-2）**: 射 f : X → Y の像（M20 の `imageAction`）を
    被覆として実体化する。台は標的 Y の台の部分型で有限（M191F-3c
    `finite_subtype`）、作用は Y の作用の `.val` 上への制限だから
    Y と同じレベル Y.level で連続（合同不変性を継承）。M191F が
    与えなかった唯一の被覆操作をここで補い、G3 のエピ・モノ分解を
    被覆圏内に閉じさせる。 -/
def imageCover (X Y : TateCover) (f : ActHom X.carrier Y.carrier) : TateCover where
  carrier := imageAction tateDeckGrp f
  finite := finite_subtype Y.finite
  level := Y.level
  level_pos := Y.level_pos
  factors := by
    intro g g' y hrel
    apply Subtype.ext
    show Y.carrier.act g y.val = Y.carrier.act g' y.val
    exact Y.factors g g' y.val hrel

/-! ## M195F-3: GaloisCatData インスタンス本体 -/

/-- **定理 (M195F-3): Tate 有限連続被覆圏は抽象 Galois 圏の公理系を
    充足する** — 圏 C = `tateCoverCat`・ファイバー関手 F =
    `tateFiberFunctor` に対し、G1（終対象 `unitCover`・ファイバー積
    `pullbackCover`）・G2（始対象 `emptyCover`・二項和 `sumCover`）・
    G3（像 `imageCover`）・G4（F はファイバー積と終対象を保つ）・
    G5（F は始対象を空に送る）・G6（F は同型を反映する）を全て満たす。
    有限性・連続性の保存は M191F の被覆操作から、極限/余極限/像の
    普遍性は M20 の GAction 操作から、それぞれ再利用する。G6 のみ
    `gsets_G6_reflects_iso`（M20-5）を経由し `Classical.choice` を継承
    （新規の選択公理使用なし）。M21-8 `gsetGaloisData` の被覆圏版。 -/
def tateGaloisData : GaloisCatData where
  C := tateCoverCat
  F := tateFiberFunctor
  -- G1a: 終対象（一点被覆）
  T := unitCover
  toT := fun X => toUnitHom X.carrier
  toT_unique := fun _ _ => ActHom.ext (fun _ => rfl)
  -- G1b: ファイバー積（M191F-4 `pullbackCover`）
  PB := fun {X Y Z} f g => pullbackCover X Y Z f g
  pb₁ := fun _ _ => ⟨fun p => p.val.1, fun _ _ => rfl⟩
  pb₂ := fun _ _ => ⟨fun p => p.val.2, fun _ _ => rfl⟩
  pb_comm := fun _ _ => ActHom.ext (fun w => w.property)
  pbLift := fun {W X Y Z} {f g} u v h =>
    ⟨fun w => ⟨(u.map w, v.map w), congrFun (congrArg ActHom.map h) w⟩,
      fun σ w => by
        apply Subtype.ext
        show (u.map (W.carrier.act σ w), v.map (W.carrier.act σ w))
            = (X.carrier.act σ (u.map w), Y.carrier.act σ (v.map w))
        rw [u.equivariant, v.equivariant]⟩
  pbLift₁ := fun _ _ _ => ActHom.ext (fun _ => rfl)
  pbLift₂ := fun _ _ _ => ActHom.ext (fun _ => rfl)
  pb_ext := fun {W X Y Z} {f g} w w' h1 h2 => by
    apply ActHom.ext
    intro x
    apply Subtype.ext
    have e1 : (w.map x).val.1 = (w'.map x).val.1 :=
      congrFun (congrArg ActHom.map h1) x
    have e2 : (w.map x).val.2 = (w'.map x).val.2 :=
      congrFun (congrArg ActHom.map h2) x
    show (w.map x).val = (w'.map x).val
    rw [show (w'.map x).val = ((w'.map x).val.1, (w'.map x).val.2) from rfl,
      ← e1, ← e2]
  -- G2: 始対象（空被覆）と二項和（M191F-4 `sumCover`）
  O := emptyCover
  fromO := fun _ => ⟨fun e => (nomatch e), fun _ e => (nomatch e)⟩
  fromO_unique := fun _ _ => ActHom.ext (fun e => (nomatch e))
  Sm := sumCover
  inl := fun _ _ => ⟨fun x => .inl x, fun _ _ => rfl⟩
  inr := fun _ _ => ⟨fun y => .inr y, fun _ _ => rfl⟩
  copair := fun {X Y W} f g =>
    ⟨fun s => match s with
      | .inl x => f.map x
      | .inr y => g.map y,
     fun σ s => by
      cases s with
      | inl x =>
        show f.map (X.carrier.act σ x) = W.carrier.act σ (f.map x)
        exact f.equivariant σ x
      | inr y =>
        show g.map (Y.carrier.act σ y) = W.carrier.act σ (g.map y)
        exact g.equivariant σ y⟩
  copair₁ := fun _ _ => ActHom.ext (fun _ => rfl)
  copair₂ := fun _ _ => ActHom.ext (fun _ => rfl)
  -- G3: エピ・モノ分解（M195F-2 `imageCover`）
  Im := fun {X Y} f => imageCover X Y f
  imE := fun f =>
    ⟨fun x => ⟨f.map x, x, rfl⟩, fun σ x => Subtype.ext (f.equivariant σ x)⟩
  imM := fun f => ⟨fun y => y.val, fun _ _ => rfl⟩
  im_comp := fun _ => ActHom.ext (fun _ => rfl)
  imE_fiber_surj := fun f w => by
    obtain ⟨x, hx⟩ := w.property
    exact ⟨x, Subtype.ext hx⟩
  imM_fiber_inj := fun f a b h => Subtype.ext h
  -- G4: F は終対象とファイバー積を保つ
  fT := PUnit.unit
  fT_unique := fun _ _ => rfl
  fpb_inj := fun f g w w' h1 h2 => by
    have e1 : w.val.1 = w'.val.1 := h1
    have e2 : w.val.2 = w'.val.2 := h2
    apply Subtype.ext
    show w.val = w'.val
    rw [show w'.val = (w'.val.1, w'.val.2) from rfl, ← e1, ← e2]
  fpb_surj := fun f g a b h => ⟨⟨(a, b), h⟩, rfl, rfl⟩
  -- G5: F は始対象を空に送る
  fO_empty := fun e => (nomatch e)
  -- G6: F は同型を反映する（M20-5 `gsets_G6_reflects_iso` の再利用・
  --     Classical.choice を継承）
  reflect_iso := fun {X Y} f hinj hsurj => by
    obtain ⟨g, hgf, hfg⟩ := gsets_G6_reflects_iso tateDeckGrp f hinj hsurj
    exact ⟨g, ActHom.ext hgf, ActHom.ext hfg⟩

/-! ## M195F-4: 無矛盾性と抽象主定理の適用（ファイバー忠実性） -/

/-- **定理 (M195F-4a): 公理系の充足の無矛盾性** — Tate 有限連続被覆圏は
    抽象 Galois 圏として無矛盾に存在する（M195F-3 の系）。 -/
theorem tateGalois_consistent : Nonempty GaloisCatData.{1, 0} :=
  ⟨tateGaloisData⟩

/-- **定理 (M195F-4b): ファイバー関手は忠実（被覆圏の抽象版）** —
    M21-4 `fiber_faithful`（公理 G1+G4+G6 だけからの導出）を
    `tateGaloisData` に適用した姿。台写像が各点で一致する被覆の射は
    等しい。M191F-6 `cover_fiber_faithful`（G-Set 事実の制限）を
    公理系からの導出として捉え直したもの。 -/
theorem tateGaloisData_faithful {X Y : tateCoverCat.Obj}
    (f g : tateCoverCat.Hom X Y)
    (h : ∀ x, tateFiberFunctor.onHom f x = tateFiberFunctor.onHom g x) :
    f = g :=
  tateGaloisData.fiber_faithful f g h

/-! ## M195F-5: A-3β-1（副有限完備化 ẑ）との接続 -/

/-- **定理 (M195F-5): 被覆の作用はデッキ座標でも副有限完備化でも
    一致** — 抽象 Galois 圏 `tateGaloisData` の対象（被覆）の作用は、
    数論的基本群 Π の元をデッキ射影で読んでも副有限完備化 ẑ の
    レベル射影で読んでも同じ。M191F-7 `cover_deck_profinite_compat`
    の Galois 圏文脈での再掲であり、実体化された Galois 圏全体が
    A-3β-1 の副有限完備化 ẑ を見ていることの内容。 -/
theorem tateGalois_profinite_compat (n : Nat) (X : GAction (zmod n))
    (g : tateCoverGrp.carrier) (x : X.carrier) :
    X.act ((profiniteLevel n).map (tateCompletion.map g)) x
      = X.act ((deckQuot n).map (tateDeckProj.map g)) x :=
  cover_deck_profinite_compat n X g x

/-! ## M195F-6: 総括 -/

/-- **Tate 被覆 Galois 圏データ（M195F-6）**: A-3β-3 の成果物の束。
    抽象 Galois 圏インスタンス本体・M191F の被覆圏操作構造・
    ファイバー忠実性・副有限完備化との整合を一つに束ねる。
    A-3β-4（Aut(F) = テンパード π₁ の復元）はこのデータを入力にとる。 -/
structure TateCoverGaloisData where
  /-- 抽象 Galois 圏データ本体（C = Tate 被覆圏・F = ファイバー関手・
      G1–G6 充足）。 -/
  galois : GaloisCatData.{1, 0}
  /-- M191F の被覆圏操作構造（終始対象・和・積・忠実ファイバー関手）。 -/
  covers : TateCoverCatData
  /-- ファイバー関手はこの圏上で忠実（M21-4 の被覆圏版・G1+G4+G6 由来）。 -/
  fiber_faithful : ∀ {X Y : galois.C.Obj} (f g : galois.C.Hom X Y),
    (∀ x, galois.F.onHom f x = galois.F.onHom g x) → f = g
  /-- 被覆の作用はデッキ座標でも副有限完備化 ẑ 経由でも一致
      （A-3β-1 接続）。 -/
  profinite_compat : ∀ (n : Nat) (X : GAction (zmod n))
    (g : tateCoverGrp.carrier) (x : X.carrier),
    X.act ((profiniteLevel n).map (tateCompletion.map g)) x
      = X.act ((deckQuot n).map (tateDeckProj.map g)) x

/-- **証人（M195F-6）**: 本モジュールの構成が Tate 被覆 Galois 圏
    データを実際に充足する。 -/
def tateCoverGaloisData : TateCoverGaloisData where
  galois := tateGaloisData
  covers := tateCoverCatData
  fiber_faithful := fun f g h => tateGaloisData.fiber_faithful f g h
  profinite_compat := cover_deck_profinite_compat

/-- **定理 (M195F-6): Tate 被覆 Galois 圏データの存在** — Tate 曲線の
    有限連続被覆の圏は、抽象 Galois 圏の公理系 G1–G6 を充足する
    Galois 圏として無矛盾に存在する。主定理 `Aut(F) = π₁` の復元
    （A-3β-4）はこのデータを土台とする。 -/
theorem tateCoverGalois_exists : Nonempty TateCoverGaloisData :=
  ⟨tateCoverGaloisData⟩

end IUT
