/-
  # M225F: 真の圏同値データの束ね（擬逆関手・unit・counit）（柱A A-3α/β）

  M217F（比較関手 towerComparison・忠実・自然・対象ごと全単射・
  本質的全射のレベル橋）と M221F（充満性）で「充満忠実 +
  本質的全射のレベル供給」まで到達したが、**真の圏同値
  （擬逆関手 Ψ・単位 η・余単位 ε の自然同型 = 2-out-of-3 の束ね）**
  は正直な限定として残っていた（A-3β）。本モジュールはその欠けた
  成分を、**抽象圏レベルで到達可能なスライス**として構成する:

  * M225F-1 `FullyFaithful` — **構造化された充満忠実性**: 関手 F の
    hom 上の逆写像 `homInv`（両側逆）をデータとして持つ充満忠実性。
    ∃ の充満性（M221F）から `homInv` を関数として抽出するには
    Classical.choice を要するため、本モジュールでは choice を持ち込まず
    「逆写像を含むデータ」として受け取り、そこから先を choice なしで
    組み立てる（`faithful` / `homInv_id` / `homInv_comp` を導出）
  * M225F-2 `conj_iso_comp` — 同型による共役 e_Y；g；e_{Y'}⁻¹ の
    関手性（合成を保つ）。純 Cat 語彙・assoc と inv_hom のみ
  * M225F-3 `QuasiInverseData` — **擬逆関手のデータ**: 対象写像
    `invObj`・構造化充満忠実 `ff`・**余単位同型** counitIso :
    F(invObj Y) ≅ Y（= 本質的全射性を「選ばれた同型込み」で持つ）
  * M225F-4 `QuasiInverseData.conjHom` / `quasiInverseFunctor` —
    **擬逆関手 Ψ : D → C** の構成: Ψ(Y)=invObj Y、
    Ψ(g)=homInv(counitIso Y；g；counitIso Y'⁻¹)。関手法則 map_id /
    map_comp は共役の関手性（M225F-2）と homInv の関手性から従う
    （choice なし）
  * M225F-5 `QuasiInverseData.unitIso` — **単位同型 η_X : X ≅ Ψ(F X)**
    の構成: homInv(counitIso(F X)⁻¹) とその逆。iso 則は homInv の
    関手性と counitIso の iso 則から（choice なし）
  * M225F-6 `catEquivOfQuasiInverse` — **capstone**: QuasiInverseData
    から `CatEquiv C D`（M19 の随伴同値データ = F/Ψ/η/ε + 両自然性）
    を組み立てる。unit_natural / counit_natural は忠実性への帰着 +
    共役計算で証明（choice なし）。SGA1 圏同値の「2-out-of-3 束ね」の
    抽象・データ駆動版
  * M225F-7 `CatEquiv.gFaithful` / `CatEquiv.fullyFaithfulF` /
    `CatEquiv.toQuasiInverseData` — **逆方向（無矛盾性・非空性）**:
    任意の `CatEquiv` から QuasiInverseData を復元（F の構造化充満忠実は
    unit/counit の自然性から choice なしで抽出、G の忠実性経由）。
    QuasiInverseData ⇔ CatEquiv を示し、本定式化が M19 の圏同値と
    同値の強さであることを保証する
  * M225F-8 `selfGSetEquiv` / `catEquiv_reconstructed` /
    `towerComparison_catEquiv_of_quasiInverse` — **具体化と IUT 接続**:
    (i) 任意群 G のモデルで自明群準同型による G-Set 上の圏同値を
    QuasiInverseData 経由で再構成（非空性の実証）、(ii) **条件付き
    主定理**: 正則塔の比較関手 towerComparison に対する
    QuasiInverseData が与えられれば（= 擬逆関手 + 構造化充満忠実 +
    余単位同型を供給すれば）、それは真の圏同値
    C ≃ π₁-Set（GSetCat pi1Tower）である

  **意義**: A-3β の欠片 — 「充満忠実 + 本質的全射 ⟹ 圏同値」の
  2-out-of-3 が、**擬逆関手・単位・余単位の明示構成**として初めて
  形式化された。核心は「充満忠実性を（∃ ではなく）逆写像込みの
  データ `homInv` として持てば、擬逆関手 Ψ・単位 η・余単位 ε の
  全成分と両自然性が Classical.choice を一切新規に使わずに構成できる」
  こと（M225F-3〜6）。逆に任意の CatEquiv からこのデータが復元でき
  （M225F-7）、両定式化が同値であることが確認された。M221F の
  正則対象上の充満忠実性と本モジュールを繋ぐ条件付き主定理
  （M225F-8）は、SGA1 主定理 C ≃ π₁-Set が「towerComparison に対する
  擬逆データの存在」に帰着することを明示する。

  **正直な限定**: (1) 本モジュールは**構造化充満忠実 + 余単位同型を
  データとして受け取る**スライスである。M221F の充満性は
  「∃ u, onHom u = φ」であり、そこから `homInv`（φ ↦ u の関数）を
  抽出するには Classical.choice を要する。同様に本質的全射性
  （M217F-12 のレベル橋）から余単位同型 F(invObj Y) ≅ Y を全対象で
  一斉に選ぶのも choice を要する。したがって towerComparison に対する
  QuasiInverseData の**無条件構成は本モジュールの範囲外**であり、
  M225F-8 の主定理は「その擬逆データが与えられれば」の**条件付き**
  である（choice を新規に持ち込まないための誠実な限定）。
  (2) 擬逆関手・単位・余単位そのものの構成（M225F-3〜7）と、G-Set
  上の再構成（M225F-8 の(i)）は choice を一切新規に使わない
  （`#print axioms` 実測: Quot 系・propext のみ、Classical なし）。
  (3) M225F-8 の(ii) の条件付き定理は QuasiInverseData を仮定として
  受け取るのみで、証明体に新規 choice はない（towerComparison の型が
  M24 transAut / G6 由来の choice を継承するのは既存事情のとおり）。

  全て選択公理の新規使用なし（仮定・型経由の継承を除く）。
  サブエージェント並行部品。
-/
import IUT.GaloisFullness

namespace IUT

universe u v u' v'

section AbstractFF

variable {C : Cat.{u, v}} {D : Cat.{u', v'}}

/-! ## M225F-1: 構造化された充満忠実性 -/

/-- **構造化充満忠実性（M225F-1a）**: 関手 F の hom 写像
    F.onHom : Hom(X,Y) → Hom(F X, F Y) の両側逆 `homInv` をデータとして
    持つ充満忠実性。充満性（∃ の逆像）を「選ばれた逆写像込み」で
    表すことで、以降の擬逆関手構成を Classical.choice なしで行う。 -/
structure FullyFaithful (F : Functor C D) where
  /-- hom 上の逆写像（充満性 + 忠実性を関数として保持）。 -/
  homInv : {X Y : C.Obj} → D.Hom (F.onObj X) (F.onObj Y) → C.Hom X Y
  /-- 左逆: homInv ∘ F.onHom = id。 -/
  homInv_left : ∀ {X Y : C.Obj} (f : C.Hom X Y), homInv (F.onHom f) = f
  /-- 右逆: F.onHom ∘ homInv = id。 -/
  homInv_right : ∀ {X Y : C.Obj} (g : D.Hom (F.onObj X) (F.onObj Y)),
    F.onHom (homInv g) = g

namespace FullyFaithful

variable {F : Functor C D}

/-- **忠実性（M225F-1b）**: homInv が左逆なので F.onHom は単射。 -/
theorem faithful (ff : FullyFaithful F) {X Y : C.Obj} {f g : C.Hom X Y}
    (h : F.onHom f = F.onHom g) : f = g := by
  have hc := congrArg ff.homInv h
  rw [ff.homInv_left, ff.homInv_left] at hc
  exact hc

/-- **単位の逆像（M225F-1c）**: homInv(id_{F X}) = id_X。 -/
theorem homInv_id (ff : FullyFaithful F) (X : C.Obj) :
    ff.homInv (D.id (F.onObj X)) = C.id X := by
  rw [← F.map_id, ff.homInv_left]

/-- **合成の逆像（M225F-1d）**: homInv は合成を保つ。 -/
theorem homInv_comp (ff : FullyFaithful F) {X Y Z : C.Obj}
    (g : D.Hom (F.onObj X) (F.onObj Y))
    (g' : D.Hom (F.onObj Y) (F.onObj Z)) :
    ff.homInv (D.comp g g') = C.comp (ff.homInv g) (ff.homInv g') := by
  have h : F.onHom (C.comp (ff.homInv g) (ff.homInv g')) = D.comp g g' := by
    rw [F.map_comp, ff.homInv_right, ff.homInv_right]
  rw [← h, ff.homInv_left]

end FullyFaithful

/-! ## M225F-2: 同型による共役の関手性 -/

/-- **共役の関手性（M225F-2）**: 同型 e_Y : W_Y ≅ Y に沿った共役
    g ↦ e_Y；g；e_{Y'}⁻¹ は合成を保つ（中間の e_{Y'}⁻¹；e_{Y'} が
    恒等に潰れる）。assoc と inv_hom のみ、choice なし。 -/
theorem conj_iso_comp {WY Y WY' Y' WZ Z : D.Obj}
    (eY : CatIso D WY Y) (eY' : CatIso D WY' Y') (eZ : CatIso D WZ Z)
    (g : D.Hom Y Y') (g' : D.Hom Y' Z) :
    D.comp (D.comp (D.comp eY.hom g) eY'.inv)
        (D.comp (D.comp eY'.hom g') eZ.inv)
      = D.comp (D.comp eY.hom (D.comp g g')) eZ.inv := by
  calc D.comp (D.comp (D.comp eY.hom g) eY'.inv)
          (D.comp (D.comp eY'.hom g') eZ.inv)
      = D.comp (D.comp eY.hom g)
          (D.comp eY'.inv (D.comp (D.comp eY'.hom g') eZ.inv)) :=
        D.assoc (D.comp eY.hom g) eY'.inv
          (D.comp (D.comp eY'.hom g') eZ.inv)
    _ = D.comp (D.comp eY.hom g)
          (D.comp (D.comp eY'.inv (D.comp eY'.hom g')) eZ.inv) := by
        rw [← D.assoc eY'.inv (D.comp eY'.hom g') eZ.inv]
    _ = D.comp (D.comp eY.hom g)
          (D.comp (D.comp (D.comp eY'.inv eY'.hom) g') eZ.inv) := by
        rw [← D.assoc eY'.inv eY'.hom g']
    _ = D.comp (D.comp eY.hom g)
          (D.comp (D.comp (D.id Y') g') eZ.inv) := by
        rw [eY'.inv_hom]
    _ = D.comp (D.comp eY.hom g) (D.comp g' eZ.inv) := by
        rw [D.id_comp]
    _ = D.comp eY.hom (D.comp g (D.comp g' eZ.inv)) :=
        D.assoc eY.hom g (D.comp g' eZ.inv)
    _ = D.comp eY.hom (D.comp (D.comp g g') eZ.inv) := by
        rw [← D.assoc g g' eZ.inv]
    _ = D.comp (D.comp eY.hom (D.comp g g')) eZ.inv := by
        rw [← D.assoc eY.hom (D.comp g g') eZ.inv]

/-! ## M225F-3: 擬逆関手のデータ -/

/-- **擬逆関手データ（M225F-3）**: 擬逆関手を構成するための入力 —
    対象写像 `invObj`、構造化充満忠実 `ff`、そして各 Y に対する
    **余単位同型** F(invObj Y) ≅ Y（本質的全射性を「選ばれた同型込み」
    で持つ）。SGA1 の「pro-表現対象からの擬逆」の抽象データ。 -/
structure QuasiInverseData (F : Functor C D) where
  /-- 擬逆関手の対象写像 Y ↦ invObj Y。 -/
  invObj : D.Obj → C.Obj
  /-- F の構造化充満忠実性（M225F-1）。 -/
  ff : FullyFaithful F
  /-- 余単位同型 ε_Y : F(invObj Y) ≅ Y（本質的全射 + 選ばれた同型）。 -/
  counitIso : (Y : D.Obj) → CatIso D (F.onObj (invObj Y)) Y

namespace QuasiInverseData

variable {F : Functor C D} (data : QuasiInverseData F)

/-! ## M225F-4: 擬逆関手 Ψ -/

/-- **共役 hom（M225F-4a）**: g : Y → Y' を
    counitIso Y；g；counitIso Y'⁻¹ : F(invObj Y) → F(invObj Y') へ。 -/
def conjHom {Y Y' : D.Obj} (g : D.Hom Y Y') :
    D.Hom (F.onObj (data.invObj Y)) (F.onObj (data.invObj Y')) :=
  D.comp (D.comp (data.counitIso Y).hom g) (data.counitIso Y').inv

/-! ## M225F-5: 単位同型 -/

/-- **単位同型（M225F-5）**: η_X : X ≅ invObj(F X) = Ψ(F X)。
    hom = homInv(counitIso(F X)⁻¹)、inv = homInv(counitIso(F X))。
    iso 則は homInv の関手性（M225F-1c/1d）と counitIso の iso 則
    から従う（choice なし）。 -/
def unitIso (X : C.Obj) : CatIso C X (data.invObj (F.onObj X)) where
  hom := data.ff.homInv (data.counitIso (F.onObj X)).inv
  inv := data.ff.homInv (data.counitIso (F.onObj X)).hom
  hom_inv := by
    show C.comp (data.ff.homInv (data.counitIso (F.onObj X)).inv)
        (data.ff.homInv (data.counitIso (F.onObj X)).hom) = C.id X
    rw [← data.ff.homInv_comp, (data.counitIso (F.onObj X)).inv_hom,
      data.ff.homInv_id]
  inv_hom := by
    show C.comp (data.ff.homInv (data.counitIso (F.onObj X)).hom)
        (data.ff.homInv (data.counitIso (F.onObj X)).inv)
      = C.id (data.invObj (F.onObj X))
    rw [← data.ff.homInv_comp, (data.counitIso (F.onObj X)).hom_inv,
      data.ff.homInv_id]

end QuasiInverseData

/-- **擬逆関手（M225F-4b）**: Ψ : D → C。Ψ(Y)=invObj Y、
    Ψ(g)=homInv(共役 g)。map_id は共役が恒等を保つこと、map_comp は
    共役の関手性（M225F-2）と homInv の関手性（M225F-1d）から。
    choice なし。 -/
def quasiInverseFunctor {F : Functor C D} (data : QuasiInverseData F) :
    Functor D C where
  onObj := data.invObj
  onHom := fun {_Y _Y'} g => data.ff.homInv (data.conjHom g)
  map_id := fun Y => by
    show data.ff.homInv
        (D.comp (D.comp (data.counitIso Y).hom (D.id Y))
          (data.counitIso Y).inv)
      = C.id (data.invObj Y)
    rw [D.comp_id, (data.counitIso Y).hom_inv, data.ff.homInv_id]
  map_comp := fun {Y Y' Z} g g' => by
    have hconj := conj_iso_comp (data.counitIso Y) (data.counitIso Y')
      (data.counitIso Z) g g'
    show data.ff.homInv
        (D.comp (D.comp (data.counitIso Y).hom (D.comp g g'))
          (data.counitIso Z).inv)
      = C.comp
          (data.ff.homInv
            (D.comp (D.comp (data.counitIso Y).hom g)
              (data.counitIso Y').inv))
          (data.ff.homInv
            (D.comp (D.comp (data.counitIso Y').hom g')
              (data.counitIso Z).inv))
    rw [← hconj, data.ff.homInv_comp]

/-! ## M225F-6: 圏同値データの束ね（capstone） -/

/-- **capstone（M225F-6）: 擬逆データから圏同値**。
    QuasiInverseData から `CatEquiv C D`（M19 の随伴同値データ =
    F・擬逆 Ψ・単位 η・余単位 ε + 両自然性）を組み立てる。
    unit_natural は忠実性（M225F-1b）への帰着 + 共役計算、
    counit_natural は共役計算で証明。**2-out-of-3 の束ね**の
    データ駆動・choice なし版。 -/
def catEquivOfQuasiInverse {F : Functor C D} (data : QuasiInverseData F) :
    CatEquiv C D where
  F := F
  G := quasiInverseFunctor data
  unit := data.unitIso
  counit := data.counitIso
  unit_natural := fun {X X'} f => by
    apply data.ff.faithful
    show F.onHom
        (C.comp f (data.ff.homInv (data.counitIso (F.onObj X')).inv))
      = F.onHom
          (C.comp (data.ff.homInv (data.counitIso (F.onObj X)).inv)
            (data.ff.homInv (data.conjHom (F.onHom f))))
    rw [F.map_comp, F.map_comp, data.ff.homInv_right, data.ff.homInv_right,
      data.ff.homInv_right]
    show D.comp (F.onHom f) (data.counitIso (F.onObj X')).inv
      = D.comp (data.counitIso (F.onObj X)).inv
          (D.comp (D.comp (data.counitIso (F.onObj X)).hom (F.onHom f))
            (data.counitIso (F.onObj X')).inv)
    rw [← D.assoc (data.counitIso (F.onObj X)).inv
          (D.comp (data.counitIso (F.onObj X)).hom (F.onHom f))
          (data.counitIso (F.onObj X')).inv,
        ← D.assoc (data.counitIso (F.onObj X)).inv
          (data.counitIso (F.onObj X)).hom (F.onHom f),
        (data.counitIso (F.onObj X)).inv_hom, D.id_comp]
  counit_natural := fun {Y Y'} g => by
    show D.comp (data.counitIso Y).hom g
      = D.comp (F.onHom (data.ff.homInv (data.conjHom g)))
          (data.counitIso Y').hom
    rw [data.ff.homInv_right]
    show D.comp (data.counitIso Y).hom g
      = D.comp
          (D.comp (D.comp (data.counitIso Y).hom g) (data.counitIso Y').inv)
          (data.counitIso Y').hom
    rw [D.assoc (D.comp (data.counitIso Y).hom g) (data.counitIso Y').inv
          (data.counitIso Y').hom,
        (data.counitIso Y').inv_hom, D.comp_id]

end AbstractFF

/-! ## M225F-7: 逆方向 — 任意の CatEquiv から擬逆データを復元 -/

namespace CatEquiv

variable {C : Cat.{u, v}} {D : Cat.{u', v'}}

/-- **G の忠実性（M225F-7a）**: CatEquiv の余単位が同型なので、
    右関手 G は忠実（counit_natural で FG を counit 共役に翻訳し、
    同型を簡約）。choice なし。 -/
theorem gFaithful (E : CatEquiv C D) {Y Y' : D.Obj}
    (a b : D.Hom Y Y') (h : E.G.onHom a = E.G.onHom b) : a = b := by
  have h1 : D.comp (E.counit Y).hom a = D.comp (E.counit Y).hom b := by
    rw [E.counit_natural a, E.counit_natural b, h]
  have h2 : D.comp (E.counit Y).inv (D.comp (E.counit Y).hom a)
      = D.comp (E.counit Y).inv (D.comp (E.counit Y).hom b) :=
    congrArg (D.comp (E.counit Y).inv) h1
  rw [← D.assoc, ← D.assoc, (E.counit Y).inv_hom, D.id_comp, D.id_comp]
    at h2
  exact h2

/-- **F の構造化充満忠実性（M225F-7b）**: CatEquiv の F は
    homInv g := unit_X；G(g)；unit_Y⁻¹ を逆写像として充満忠実。
    左逆は unit_natural、右逆は G の忠実性（M225F-7a）経由。choice
    なし。 -/
def fullyFaithfulF (E : CatEquiv C D) : FullyFaithful E.F where
  homInv := fun {X Y} g =>
    C.comp (C.comp (E.unit X).hom (E.G.onHom g)) (E.unit Y).inv
  homInv_left := fun {X Y} f => by
    show C.comp (C.comp (E.unit X).hom (E.G.onHom (E.F.onHom f)))
        (E.unit Y).inv = f
    rw [← E.unit_natural f, C.assoc, (E.unit Y).hom_inv, C.comp_id]
  homInv_right := fun {X Y} g => by
    apply E.gFaithful
    have hLHS : C.comp
        (C.comp (C.comp (E.unit X).hom (E.G.onHom g)) (E.unit Y).inv)
        (E.unit Y).hom
      = C.comp (E.unit X).hom (E.G.onHom g) := by
      rw [C.assoc, (E.unit Y).inv_hom, C.comp_id]
    have hn := E.unit_natural
      (C.comp (C.comp (E.unit X).hom (E.G.onHom g)) (E.unit Y).inv)
    rw [hLHS] at hn
    have hc : C.comp (E.unit X).inv (C.comp (E.unit X).hom (E.G.onHom g))
        = C.comp (E.unit X).inv (C.comp (E.unit X).hom
            (E.G.onHom (E.F.onHom
              (C.comp (C.comp (E.unit X).hom (E.G.onHom g))
                (E.unit Y).inv)))) :=
      congrArg (C.comp (E.unit X).inv) hn
    rw [← C.assoc, ← C.assoc, (E.unit X).inv_hom, C.id_comp, C.id_comp]
      at hc
    exact hc.symm

/-- **擬逆データの復元（M225F-7c）**: 任意の CatEquiv から
    QuasiInverseData を復元。invObj=G.onObj、ff=充満忠実（M225F-7b）、
    counitIso=余単位。QuasiInverseData ⇔ CatEquiv を確立し、本定式化が
    M19 の圏同値と同値の強さであることを保証する。 -/
def toQuasiInverseData (E : CatEquiv C D) : QuasiInverseData E.F where
  invObj := E.G.onObj
  ff := E.fullyFaithfulF
  counitIso := E.counit

end CatEquiv

/-! ## M225F-8: 具体化と IUT 接続 -/

/-- 群上の恒等準同型。 -/
def idGrpHom (G : Grp) : Hom G G := ⟨fun g => g, fun _ _ => rfl⟩

/-- **G-Set 上の自明な圏同値（M225F-8a）**: 恒等群準同型による
    restrictEquiv（M19-1）。QuasiInverseData 経由の再構成の材料。 -/
def selfGSetEquiv (G : Grp) : CatEquiv (GSetCat G) (GSetCat G) :=
  restrictEquiv (idGrpHom G) (idGrpHom G) (fun _ => rfl) (fun _ => rfl)

/-- **非空性（M225F-8b）**: 任意の CatEquiv から QuasiInverseData が
    得られる（本定式化が空でないこと）。 -/
theorem quasiInverseData_of_equiv {C : Cat.{u, v}} {D : Cat.{u', v'}}
    (E : CatEquiv C D) : Nonempty (QuasiInverseData E.F) :=
  ⟨E.toQuasiInverseData⟩

/-- **再構成（M225F-8c）**: 任意群 G のモデルで、G-Set 上の圏同値を
    QuasiInverseData（擬逆関手 + 構造化充満忠実 + 余単位同型）経由で
    再構成する。抽象 capstone（M225F-6）の実インスタンス。choice
    なし（`#print axioms` 実測: Quot 系・propext のみ）。 -/
theorem catEquiv_reconstructed (G : Grp) :
    Nonempty (CatEquiv (GSetCat G) (GSetCat G)) :=
  ⟨catEquivOfQuasiInverse (selfGSetEquiv G).toQuasiInverseData⟩

/-- **系（M225F-8d）: 無条件の存在**（無矛盾性）— 自明群で。 -/
theorem catEquiv_reconstructed_trivial :
    Nonempty (CatEquiv (GSetCat punitGrp) (GSetCat punitGrp)) :=
  catEquiv_reconstructed punitGrp

/-- **条件付き主定理（M225F-8e）: 比較関手の真の圏同値**。
    正則塔（M221F-8d）の比較関手 towerComparison : C → π₁-Set に対する
    **QuasiInverseData（擬逆関手 Ψ・構造化充満忠実・余単位同型）が
    与えられれば**、それは真の圏同値 C ≃ GSetCat(pi1Tower) である。
    M221F の正則対象上の充満忠実性（∃ 版）から `homInv` を、本質的全射
    から余単位同型を、それぞれ Classical.choice で抽出すればこの仮定は
    充足される — その choice を新規に持ち込まないための誠実な条件付き
    定式化。SGA1 主定理が「towerComparison の擬逆データの存在」に
    帰着することを明示する。 -/
theorem towerComparison_catEquiv_of_quasiInverse (G : Grp)
    (data : QuasiInverseData (regTower G).towerComparison) :
    Nonempty (CatEquiv (gsetGaloisData G).C
      (GSetCat (GaloisTower.pi1Tower (regTower G)))) :=
  ⟨catEquivOfQuasiInverse data⟩

end IUT
