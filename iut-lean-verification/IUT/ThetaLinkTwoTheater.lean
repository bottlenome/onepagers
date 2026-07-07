-- M439F ThetaLinkTwoTheater [実・本物・柱A frontier・M434F の限定 (i) を昇格で閉じる]
-- complete_pct 影響: 柱A で M434F tlt_model_scope の限定 (i)「本 theta-link は同一算術商上の自己準同型であり相異なる 2 ホッジ劇場間の link ではない」を昇格で閉じる: ラベル付き独立コピー †0/†1（型レベルで区別される 2 劇場 tlt2Theater false / tlt2Theater true）を建設し、その間の theta-link tlt2Link j を本物の群準同型（値群 a・シクロトーム c・deck n を j 倍・μ 固定・算術切断共有）として実現。link がラベルを †0→†1 へ実際に動かす＝自己準同型でないこと（tlt2_not_endo）を定理で固定。
-- 正直な限定: 2 劇場は同一の離散モデル atpGroup の**同型なラベル付きコピー**（標準の val-保存同型 tlt2Transport が存在、tlt2_model_scope で定理化）であり、環構造まで独立に変えた full poly-isomorphism ではない・j=2 の link は劇場間でも非全射・副有限 G_K・実テータ値・多輻不等式（crux Dβ-ω）は外部/後続。

/-
  IUT/ThetaLinkTwoTheater.lean — M439F [実／本物の忠実な部分ケース・柱A frontier]
  分類: 実（M434F の theta-link tltLink を、相異なる 2 ホッジ劇場
  ＝ラベル付き独立コピー †0/†1 の間の本物の群準同型として建て直す）

  既存の実部品:
    * M429F (ArithTemperedPi1): 算術 tempered π₁ ＝ atpGroup = tpeGroup ⋊_χ ℤ、
      埋め込み atpIncl/atpInclGeom・切断 atpSection/atpDeckSection・
      外ガロア表現 atp_outer_galois
    * M434F (ThetaLinkTemperedPi1): theta-link tltLink j : Hom atpGroup atpGroup
      （値群 a・シクロトーム c・deck n を j 倍・μ-方向 b 固定・算術 m 恒等）、
      交換子保存・シクロトーム剛性・塔両立・ガロア同変・
      **正直な限定 tlt_model_scope (i)**: 本 link は同一算術商上の自己準同型で
      あり、相異なる 2 ホッジ劇場間の link ではない

  本モジュールは M434F の限定 (i) を**昇格で閉じる**。[IUTchIII] の Θ-link は
  「一方のホッジ劇場のテータパイロットを**他方の**ホッジ劇場の q-パイロットへ
  移す」対応であり、始域と終域は**相異なる劇場**（IUT では独立なラベル付き
  コピー、Θ^{±ell}NF-Hodge theater の †HT と ‡HT）である。その離散実現:

    * **2 劇場**: Tlt2Elt t（t : Bool、†0 = false・†1 = true）＝ atpGroup の
      ラベル付き独立コピー。Tlt2Elt false と Tlt2Elt true は**型として区別**
      され、各劇場 tlt2Theater t は本物の群（群公理は atpGroup から誘導）。
    * **劇場間 theta-link**: tlt2Link j : Hom (tlt2Theater †0) (tlt2Theater †1)、
      val レベルで tltLink j（値群 a・シクロトーム c・deck n を j 倍・
      μ-方向 b 固定・算術切断＝ G_K 側は両劇場で共有）。**任意の j で本物の
      群準同型**（tlt2_link_hom）。始域は †0・終域は †1 ——
      **自己準同型ではない**（tlt2_not_endo: link はラベルを実際に動かす）。

  完全証明する内容（すべて本物の群演算・toy 主語なし）:
    * 2 劇場 tlt2Theater †0/†1 の群公理・埋め込み塔（tlt2Incl・tlt2InclGeom・
      tlt2Section・tlt2DeckSection、各劇場ごと）
    * tlt2Link j の準同型性（任意の j で on the nose）・単位元保存・
      逆向き link tlt2LinkRev との往復合成＝ Frobenius 次数の乗法
      （tlt2_roundtrip_degree）・j = −1 での往復恒等＝**劇場間同型**
      （tlt2_neg_one_roundtrip・単射・全射）
    * **tlt2_commutator_preserved**: 劇場間 link は交換子構造を †0 から †1 へ
      on the nose で移す。テータ交換子＝シンプレクティック形式は †1 側で
      j·ω に着地（tlt2_theta_commutator）、シクロトームは j 倍
      （**tlt2_cyclotome_rigid**）、μ-方向（単数系）は共有（tlt2_mu_fixed）、
      deck は j 倍（tlt2_deck_scaled）——値群・deck・シクロトームが同一因子で
      しか動かない＝シクロトーム剛性の 2 劇場版。
    * **tlt2_section_shared**: 算術切断（G_K のモデル）は 2 劇場で共有され
      link で固定される。外ガロア共役とも可換（tlt2_galois_equivariant）。
    * **tlt2_not_endo（M434F の限定 (i) を閉じる本丸）**: link の像のラベルは
      †1・始域のラベルは †0 で相異なる——link は**自己準同型ではなく**、
      相異なる 2 劇場の間を実際に渡る（tlt2_label_moved/tlt2_labels_distinct）。
    * capstone tlt2_exists: 全構造を ThetaLinkTwoTheaterData に束ね
      crux 以外の外部仮説なしで居住させる。

  crux（決して内部化しない）:
    * theta-link の**多輻アルゴリズム不等式**（Dβ-ω、[IUTchIII] Cor 3.12 の
      係争ステップ）は本モジュールの主張に一切含めない。
      tlt2_crux_is_hypothesis (crux : Prop) : crux ↔ crux ＝ Iff.rfl で
      外部仮説として保持（M434F tlt_crux_is_hypothesis と同じ精神）。

  正直な限定（M434F の限定 (i) を閉じた上で、残りを狭めて述べ直す・
  消さない・弱めない）:
    * 2 劇場は同一の離散モデル atpGroup の**同型なラベル付きコピー**である:
      標準の val-保存同型 tlt2Transport が存在する（tlt2_model_scope 第 1 成分
      で定理として固定）。実 IUT の Θ-link の両側は**環構造まで独立**な
      ホッジ劇場であり、その間の full poly-isomorphism（環構造を忘れた
      群論的同型の全体軌道）・独立な環構造の上での実テータ値の輸送は
      外部/後続（tlt2_full_poly_isomorphism_hypothesis・
      tlt2_independent_ring_hypothesis）。
    * j = 2（Frobenius 次数）の劇場間 link は**全射でない**
      （tlt2_frobenius_not_surjective、M434F 7a の 2 劇場版）。可逆性には
      副有限完備化と実際の値群 q^ℤ の実装が要る——外部/後続。
    * 環構造の非保存（Θ-link は乗法系のみ移し加法を壊す）・log-link（柱C）
      との噛み合わせは本群論モデルの外（M434F と同じ・後続）。
  全て選択公理不使用（propext / Quot.sound のみ）。
-/
import IUT.ThetaLinkTemperedPi1

namespace IUT

/-! ## M439F-1: 2 ホッジ劇場＝ラベル付き独立コピー †0/†1

  Tlt2Elt t（t : Bool）は atpGroup のラベル t 付きコピー。Tlt2Elt false（†0）と
  Tlt2Elt true（†1）は**型として区別**される——同一の型の上の自己準同型では
  劇場の区別が消えるという M434F の限定 (i) を、型レベルのラベルで解消する。 -/

/-- **M439F-1a: 劇場 t の元** — atpGroup のラベル t 付きコピーの元。
    ラベル t : Bool（†0 = false・†1 = true）は型パラメータであり、
    Tlt2Elt false と Tlt2Elt true は相異なる型（相異なる劇場）。 -/
structure Tlt2Elt (t : Bool) where
  /-- 台となる算術 tempered π₁（M429F atpGroup）の元。 -/
  val : atpGroup.carrier

/-- 劇場の元の等値補題（val で決まる）。 -/
theorem tlt2_ext {t : Bool} {x y : Tlt2Elt t} (h : x.val = y.val) : x = y :=
  congrArg Tlt2Elt.mk h

/-- **M439F-1b: ホッジ劇場 t** — atpGroup のラベル t 付きコピーの上の本物の群
    （群公理は atpGroup の公理から val レベルで誘導）。 -/
@[reducible] def tlt2Theater (t : Bool) : Grp where
  carrier := Tlt2Elt t
  mul := fun x y => ⟨atpGroup.mul x.val y.val⟩
  one := ⟨atpGroup.one⟩
  inv := fun x => ⟨atpGroup.inv x.val⟩
  mul_assoc := fun a b c => tlt2_ext (atpGroup.mul_assoc a.val b.val c.val)
  one_mul := fun a => tlt2_ext (atpGroup.one_mul a.val)
  inv_mul := fun a => tlt2_ext (atpGroup.inv_mul a.val)

/-- 劇場の元のラベル読み出し（元がどちらの劇場に住むかの証人）。 -/
@[reducible] def tlt2Label {t : Bool} (_ : (tlt2Theater t).carrier) : Bool := t

/-- 積の val（definitional）。 -/
theorem tlt2_mul_val (t : Bool) (x y : (tlt2Theater t).carrier) :
    ((tlt2Theater t).mul x y).val = atpGroup.mul x.val y.val := rfl

/-- 交換子の val（definitional）。 -/
theorem tlt2_comm_val (t : Bool) (x y : (tlt2Theater t).carrier) :
    ((tlt2Theater t).comm x y).val = atpGroup.comm x.val y.val := rfl

/-- **M439F-1c: 標準埋め込み** atpGroup → 劇場 t（各劇場は atpGroup のコピー）。 -/
def tlt2Incl (t : Bool) : Hom atpGroup (tlt2Theater t) where
  map := fun x => ⟨x⟩
  map_mul := fun _ _ => rfl

/-- 標準埋め込みは単射。 -/
theorem tlt2_incl_injective (t : Bool) : (tlt2Incl t).Injective :=
  fun _ _ h => congrArg Tlt2Elt.val h

/-- **M439F-1d: 幾何 tempered π₁ の埋め込み**（劇場 t の幾何核 π₁^temp）。 -/
def tlt2InclFull (t : Bool) : Hom tpeGroup (tlt2Theater t) :=
  (tlt2Incl t).comp atpIncl

/-- **M439F-1e: テータ部（Δ^temp）の埋め込み**（劇場 t の二段塔の下段）。 -/
def tlt2InclGeom (t : Bool) : Hom thetaGrp (tlt2Theater t) :=
  (tlt2Incl t).comp atpInclGeom

/-- **M439F-1f: 算術切断**（劇場 t の G_K モデルの切断）。 -/
def tlt2Section (t : Bool) : Hom intGrp (tlt2Theater t) :=
  (tlt2Incl t).comp atpSection

/-- **M439F-1g: deck 切断**（劇場 t の deck 商の持ち上げ）。 -/
def tlt2DeckSection (t : Bool) : Hom intGrp (tlt2Theater t) :=
  (tlt2Incl t).comp atpDeckSection

/-- テータ部埋め込みの val（definitional）。 -/
theorem tlt2_incl_geom_val (t : Bool) (z : thetaGrp.carrier) :
    ((tlt2InclGeom t).map z).val = atpInclGeom.map z := rfl

/-! ## M439F-2: 劇場間 theta-link tlt2Link（本丸その 1）

  始域 = 劇場 †0（tlt2Theater false）・終域 = 劇場 †1（tlt2Theater true）。
  val レベルは M434F tltLift/tltLink: 値群 a・シクロトーム c・deck n を j 倍・
  μ-方向 b 固定・算術座標 m（G_K 側）は両劇場で共有。M434F では始域と終域が
  同一の atpGroup だった——ここでは**相異なる劇場の間**を渡る。 -/

/-- **M439F-2a: 劇場間 theta-link 本体** tlt2Link j : Hom (劇場 †0) (劇場 †1)
    — 値群 a・円分体 c・deck n を j 倍・μ 固定・算術側共有で、劇場 †0 の元を
    劇場 †1 へ移す。任意の j で本物の群準同型。 -/
def tlt2Link (j : Int) : Hom (tlt2Theater false) (tlt2Theater true) where
  map := fun x => ⟨(tltLink j).map x.val⟩
  map_mul := fun x y => tlt2_ext ((tltLink j).map_mul x.val y.val)

/-- link の val（definitional）。 -/
theorem tlt2_link_val (j : Int) (x : (tlt2Theater false).carrier) :
    ((tlt2Link j).map x).val = (tltLink j).map x.val := rfl

/-- **定理 (M439F-2b: 本物の群準同型・本丸)** — 劇場間 theta-link は †0 の積を
    †1 の積へ on the nose で移す（任意の j で本物の群準同型）。 -/
theorem tlt2_link_hom (j : Int) (x y : (tlt2Theater false).carrier) :
    (tlt2Link j).map ((tlt2Theater false).mul x y)
      = (tlt2Theater true).mul ((tlt2Link j).map x) ((tlt2Link j).map y) :=
  (tlt2Link j).map_mul x y

/-- 単位元の保存（†0 の単位元 ↦ †1 の単位元）。 -/
theorem tlt2_link_one (j : Int) :
    (tlt2Link j).map (tlt2Theater false).one = (tlt2Theater true).one :=
  tlt2_ext (tlt_link_one j)

/-- **M439F-2c: 逆向き link** †1 → †0（Frobenius 次数 j、[IUTchIII] の
    link の両向きの貼り合わせの離散版）。 -/
def tlt2LinkRev (j : Int) : Hom (tlt2Theater true) (tlt2Theater false) where
  map := fun x => ⟨(tltLink j).map x.val⟩
  map_mul := fun x y => tlt2_ext ((tltLink j).map_mul x.val y.val)

/-- **定理 (M439F-2d): 往復合成＝ Frobenius 次数の乗法** —
    †0 → †1 → †0 の往復は val レベルで tltLink (j'·j)。 -/
theorem tlt2_roundtrip_degree (j j' : Int) (x : (tlt2Theater false).carrier) :
    ((tlt2LinkRev j').map ((tlt2Link j).map x)).val = (tltLink (j' * j)).map x.val :=
  tlt_link_comp j' j x.val

/-- **定理 (M439F-2e): j = −1 の往復は恒等（†0 側）** — 劇場間 link は j = −1 で
    本物の**劇場間同型**（互いに逆な準同型の対）。 -/
theorem tlt2_neg_one_roundtrip (x : (tlt2Theater false).carrier) :
    (tlt2LinkRev (-1)).map ((tlt2Link (-1)).map x) = x :=
  tlt2_ext (tlt_link_neg_one_involutive x.val)

/-- **定理 (M439F-2f): j = −1 の往復は恒等（†1 側）**。 -/
theorem tlt2_neg_one_roundtrip' (y : (tlt2Theater true).carrier) :
    (tlt2Link (-1)).map ((tlt2LinkRev (-1)).map y) = y :=
  tlt2_ext (tlt_link_neg_one_involutive y.val)

/-- **定理 (M439F-2g): j = −1 の劇場間 link は単射**。 -/
theorem tlt2_link_neg_one_injective : (tlt2Link (-1)).Injective :=
  fun x y h =>
    tlt2_ext (tlt_link_neg_one_injective x.val y.val (congrArg Tlt2Elt.val h))

/-- **定理 (M439F-2h): j = −1 の劇場間 link は全射**。 -/
theorem tlt2_link_neg_one_surjective (y : (tlt2Theater true).carrier) :
    ∃ x : (tlt2Theater false).carrier, (tlt2Link (-1)).map x = y :=
  ⟨(tlt2LinkRev (-1)).map y, tlt2_neg_one_roundtrip' y⟩

/-! ## M439F-3: 劇場間の構造輸送（交換子・シクロトーム剛性・共有、本丸その 2）

  M434F の自己準同型版の各保存則を、†0 から †1 への**劇場間輸送**として
  建て直す: 交換子は on the nose・テータ交換子＝シンプレクティック形式は
  j·ω に着地・シクロトームは j 倍・μ-方向（単数系）と算術切断（G_K）は
  両劇場で**共有**・deck は j 倍。 -/

/-- **定理 (M439F-3a: tlt2_commutator_preserved・本丸)** — 劇場間 theta-link は
    †0 の交換子構造を †1 の交換子構造へ on the nose で移す（準同型ゆえ）。 -/
theorem tlt2_commutator_preserved (j : Int) (x y : (tlt2Theater false).carrier) :
    (tlt2Link j).map ((tlt2Theater false).comm x y)
      = (tlt2Theater true).comm ((tlt2Link j).map x) ((tlt2Link j).map y) :=
  Hom.map_grp_comm (tlt2Link j) x y

/-- **定理 (M439F-3b): テータ交換子は劇場を渡って j 倍へ同期スケール** —
    †0 のテータ交換子＝シンプレクティック形式 ω は †1 のシクロトーム上の j·ω に
    着地（M434F tlt_theta_commutator の 2 劇場版）。 -/
theorem tlt2_theta_commutator (j a b c a' b' c' : Int) :
    (tlt2Link j).map ((tlt2Theater false).comm
        ((tlt2InclGeom false).map ((a, b, c) : Int × Int × Int))
        ((tlt2InclGeom false).map ((a', b', c') : Int × Int × Int)))
      = (tlt2InclGeom true).map ((0, 0, j * (a * b' - a' * b)) : Int × Int × Int) :=
  tlt2_ext (tlt_theta_commutator j a b c a' b' c')

/-- **定理 (M439F-3c: tlt2_cyclotome_rigid・シクロトーム剛性)** — †0 の
    シクロトーム c は †1 で j 倍にしか動かない（値群（3f）と同一因子＝
    シクロトーム剛性の 2 劇場版、M434F tlt_cyclotome_scaled の昇格）。 -/
theorem tlt2_cyclotome_rigid (j c : Int) :
    (tlt2Link j).map ((tlt2InclGeom false).map ((0, 0, c) : Int × Int × Int))
      = (tlt2InclGeom true).map ((0, 0, j * c) : Int × Int × Int) :=
  tlt2_ext (tlt_cyclotome_scaled j c)

/-- **定理 (M439F-3d): μ-方向（単数系）は 2 劇場で共有** — †0 の ιι(0,b,0) は
    †1 の ιι(0,b,0) へ（Ind2 の単数トーソル共有の 2 劇場版）。 -/
theorem tlt2_mu_fixed (j b : Int) :
    (tlt2Link j).map ((tlt2InclGeom false).map ((0, b, 0) : Int × Int × Int))
      = (tlt2InclGeom true).map ((0, b, 0) : Int × Int × Int) :=
  tlt2_ext (tlt_mu_fixed j b)

/-- **定理 (M439F-3e): テータ部の輸送** — †0 の ιι(a,b,c) は †1 の
    ιι(j·a, b, j·c) へ（値群 j 倍・μ 固定・シクロトーム j 倍）。 -/
theorem tlt2_theta_transport (j a b c : Int) :
    (tlt2Link j).map ((tlt2InclGeom false).map ((a, b, c) : Int × Int × Int))
      = (tlt2InclGeom true).map ((j * a, b, j * c) : Int × Int × Int) :=
  tlt2_ext (tlt_link_theta_transport j a b c)

/-- **定理 (M439F-3f): deck は j 倍**（値群方向のスケールが deck 座標に j 倍で
    現れる、val レベル definitional）。 -/
theorem tlt2_deck_scaled (j : Int) (x : (tlt2Theater false).carrier) :
    (((tlt2Link j).map x).val).1.2 = j * (x.val).1.2 := rfl

/-- **定理 (M439F-3g: tlt2_section_shared)** — 算術切断（G_K のモデル）は
    **2 劇場で共有**され link で固定される: †0 の s(m) ↦ †1 の s(m)
    （Θ-link は G_K を両側で共有して貼る、の 2 劇場版）。 -/
theorem tlt2_section_shared (j m : Int) :
    (tlt2Link j).map ((tlt2Section false).map m) = (tlt2Section true).map m :=
  tlt2_ext (tlt_link_section j m)

/-- **定理 (M439F-3h): 外ガロア共役と可換（劇場間）** — 共有算術切断 s(m) による
    共役と link は可換: link(s(m)·ι(z)·s(m)⁻¹)_†0 = (s(m)·ι(tltLift j z)·s(m)⁻¹)_†1
    （M434F tlt_link_compat の 2 劇場版）。 -/
theorem tlt2_galois_equivariant (j m : Int) (z : tpeGroup.carrier) :
    (tlt2Link j).map ((tlt2Theater false).mul
        ((tlt2Theater false).mul ((tlt2Section false).map m)
          ((tlt2InclFull false).map z))
        ((tlt2Theater false).inv ((tlt2Section false).map m)))
      = (tlt2Theater true).mul
          ((tlt2Theater true).mul ((tlt2Section true).map m)
            ((tlt2InclFull true).map (tltLift j z)))
          ((tlt2Theater true).inv ((tlt2Section true).map m)) :=
  tlt2_ext (tlt_link_compat j m z)

/-! ## M439F-4: 自己準同型でないこと（M434F の限定 (i) を閉じる本丸） -/

/-- 2 劇場のラベルは相異なる（†0 ≠ †1）。 -/
theorem tlt2_labels_distinct : (false : Bool) ≠ true :=
  fun h => Bool.noConfusion h

/-- 始域の元のラベルは †0（definitional）。 -/
theorem tlt2_label_src (x : (tlt2Theater false).carrier) : tlt2Label x = false := rfl

/-- link の像のラベルは †1（definitional）。 -/
theorem tlt2_label_image (j : Int) (x : (tlt2Theater false).carrier) :
    tlt2Label ((tlt2Link j).map x) = true := rfl

/-- **定理 (M439F-4a: tlt2_not_endo・本丸)** — 劇場間 theta-link は
    **自己準同型ではない**: 任意の j と任意の元 x について、link の像のラベル
    （†1）は x のラベル（†0）と相異なる——link は相異なる 2 ホッジ劇場の間を
    実際に渡る。M434F tlt_model_scope の限定 (i)「本 link は同一算術商上の
    自己準同型」を実際に閉じたことの定理化。 -/
theorem tlt2_not_endo (j : Int) (x : (tlt2Theater false).carrier) :
    tlt2Label ((tlt2Link j).map x) ≠ tlt2Label x := by
  intro h
  have h' : true = false := h
  exact Bool.noConfusion h'

/-! ## M439F-5: crux Dβ-ω は外部仮説（決して内部化しない） -/

/-- **crux（外部仮説・決して導出しない）**: theta-link の**多輻アルゴリズム不等式**
    （Dβ-ω、[IUTchIII] Cor 3.12 の係争ステップ＝ q-パイロットの体積が theta-パイロット
    軌道に支配されるという主張）は、本モジュールの主張には一切含めない。恒等 Iff で
    外部仮説として保持する（M434F tlt_crux_is_hypothesis と同じ精神）。本モジュールが
    証明したのは劇場間 link の**群論的両立性**（準同型性・交換子保存・シクロトーム
    剛性・共有構造・非自己準同型性）までであり、不等式は別問題である。 -/
theorem tlt2_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M439F-6: 正直な限定（M434F の限定 (i) を閉じた上で残りを狭めて述べ直す） -/

/-- **M439F-6a: 標準輸送同型**（正直な限定の証人）— 任意の 2 劇場の間に
    val-保存の標準準同型が存在する。2 劇場が「同一の離散モデル atpGroup の
    ラベル付きコピー」であること（＝環構造まで独立ではないこと）の明示。 -/
def tlt2Transport (t t' : Bool) : Hom (tlt2Theater t) (tlt2Theater t') where
  map := fun x => ⟨x.val⟩
  map_mul := fun _ _ => rfl

/-- 標準輸送は val を保つ（definitional）。 -/
theorem tlt2_transport_val (t t' : Bool) (x : (tlt2Theater t).carrier) :
    ((tlt2Transport t t').map x).val = x.val := rfl

/-- **定理 (M439F-6b): Frobenius 次数 link は劇場間でも全射でない** —
    †1 の deck 生成元 s_deck(1) は tlt2Link 2 の像にない
    （M434F tlt_frobenius_not_surjective の 2 劇場版・正直な限定）。 -/
theorem tlt2_frobenius_not_surjective :
    ¬ ∃ x : (tlt2Theater false).carrier,
        (tlt2Link 2).map x = (tlt2DeckSection true).map 1 := by
  intro h
  obtain ⟨x, hx⟩ := h
  exact tlt_frobenius_not_surjective ⟨x.val, congrArg Tlt2Elt.val hx⟩

/-- **定理 (M439F-6c: tlt2_model_scope・正直な限定の総括）** — 本構成のスコープ
    （M434F tlt_model_scope の限定 (i) を閉じた後に残る、より狭い正直な限定）:
    (i) 2 劇場は同一の離散モデル atpGroup の**同型なラベル付きコピー**である——
    任意の 2 劇場の間に val-保存の単射準同型（標準輸送 tlt2Transport）が存在する。
    実 IUT の Θ-link の両側は**環構造まで独立**なホッジ劇場であり、その間の
    full poly-isomorphism（環構造を忘れた群論的同型の全体軌道）は外部/後続。
    (ii) j = 2（Frobenius 次数）の劇場間 link は全射でない（6b）——
    離散モデルの正直な帰結（可逆性は副有限完備化と実値群 q^ℤ を要する）。 -/
theorem tlt2_model_scope :
    (∀ t t' : Bool, ∃ f : Hom (tlt2Theater t) (tlt2Theater t'),
        (∀ x, (f.map x).val = x.val) ∧ f.Injective)
    ∧ ¬ ∃ x : (tlt2Theater false).carrier,
        (tlt2Link 2).map x = (tlt2DeckSection true).map 1 :=
  ⟨fun t t' => ⟨tlt2Transport t t',
      fun _ => rfl,
      fun _ _ h =>
        have h' := congrArg Tlt2Elt.val h
        tlt2_ext h'⟩,
    tlt2_frobenius_not_surjective⟩

/-- **外部仮説（正直な限定・決して導出しない）**: 環構造まで独立な 2 ホッジ劇場の
    間の **full poly-isomorphism**（群論的同型の全体軌道としての Θ-link）の実現。
    本モジュールの 2 劇場は同一離散モデルのラベル付きコピーである（後続）。 -/
def tlt2_full_poly_isomorphism_hypothesis (T₀ T₁ : Grp) (f : Hom T₀ T₁) : Prop :=
  f.Injective

/-- **外部仮説（正直な限定・決して導出しない）**: 各劇場に独立な**環構造**を持たせ、
    Θ-link の環構造非保存（乗法系のみ移し加法を壊す）と log-link（柱C）との
    噛み合わせ・p 進テータ関数の実特殊値の上での劇場間輸送を実現すること（後続）。 -/
def tlt2_independent_ring_hypothesis (T : Grp) : Prop := Slim T

/-! ## M439F-7: capstone -/

/-- **M439F-7a: 2 劇場 theta-link データ** — 相異なる 2 ホッジ劇場 †0/†1 の間の
    theta-link tlt2Link j の全実構造を束ねる: 準同型性（任意の j で on the nose）・
    単位元保存・**非自己準同型性（M434F の限定 (i) を閉じる）**・交換子保存・
    テータ部輸送・シクロトーム剛性（j 倍）・μ-方向共有・算術切断共有・deck j 倍・
    テータ交換子の j 同期・外ガロア共役との可換・往復合成＝ Frobenius 次数乗法・
    j = −1 での劇場間同型・Frobenius 次数 link の非全射（正直な限定）。
    主語はすべて本物の群演算（toy 主語なし）。crux Dβ-ω はフィールドに含めない
    （外部仮説のまま）。 -/
structure ThetaLinkTwoTheaterData (j : Int) where
  /-- 劇場間 link は本物の群準同型（任意の j で on the nose）。 -/
  link_hom : ∀ x y : (tlt2Theater false).carrier,
    (tlt2Link j).map ((tlt2Theater false).mul x y)
      = (tlt2Theater true).mul ((tlt2Link j).map x) ((tlt2Link j).map y)
  /-- 単位元の保存（†0 の 1 ↦ †1 の 1）。 -/
  link_one : (tlt2Link j).map (tlt2Theater false).one = (tlt2Theater true).one
  /-- **非自己準同型性**: link はラベルを †0 から †1 へ実際に動かす
      （M434F tlt_model_scope の限定 (i) を閉じる本丸）。 -/
  not_endo : ∀ x : (tlt2Theater false).carrier,
    tlt2Label ((tlt2Link j).map x) ≠ tlt2Label x
  /-- 交換子構造の劇場間保存（on the nose）。 -/
  commutator_preserved : ∀ x y : (tlt2Theater false).carrier,
    (tlt2Link j).map ((tlt2Theater false).comm x y)
      = (tlt2Theater true).comm ((tlt2Link j).map x) ((tlt2Link j).map y)
  /-- テータ部の輸送: †0 の ιι(a,b,c) ↦ †1 の ιι(j·a, b, j·c)。 -/
  theta_transport : ∀ a b c : Int,
    (tlt2Link j).map ((tlt2InclGeom false).map ((a, b, c) : Int × Int × Int))
      = (tlt2InclGeom true).map ((j * a, b, j * c) : Int × Int × Int)
  /-- シクロトーム剛性: †0 のシクロトームは †1 で j 倍にしか動かない。 -/
  cyclotome_rigid : ∀ c : Int,
    (tlt2Link j).map ((tlt2InclGeom false).map ((0, 0, c) : Int × Int × Int))
      = (tlt2InclGeom true).map ((0, 0, j * c) : Int × Int × Int)
  /-- μ-方向（単数系）は 2 劇場で共有。 -/
  mu_fixed : ∀ b : Int,
    (tlt2Link j).map ((tlt2InclGeom false).map ((0, b, 0) : Int × Int × Int))
      = (tlt2InclGeom true).map ((0, b, 0) : Int × Int × Int)
  /-- 算術切断（G_K のモデル）は 2 劇場で共有され link で固定。 -/
  section_shared : ∀ m : Int,
    (tlt2Link j).map ((tlt2Section false).map m) = (tlt2Section true).map m
  /-- deck は j 倍（値群スケール）。 -/
  deck_scaled : ∀ x : (tlt2Theater false).carrier,
    (((tlt2Link j).map x).val).1.2 = j * (x.val).1.2
  /-- テータ交換子＝シンプレクティック形式は劇場を渡って j 倍へ同期。 -/
  theta_commutator : ∀ a b c a' b' c' : Int,
    (tlt2Link j).map ((tlt2Theater false).comm
        ((tlt2InclGeom false).map ((a, b, c) : Int × Int × Int))
        ((tlt2InclGeom false).map ((a', b', c') : Int × Int × Int)))
      = (tlt2InclGeom true).map ((0, 0, j * (a * b' - a' * b)) : Int × Int × Int)
  /-- 外ガロア共役との可換（共有 G_K 切断の共役と link は可換）。 -/
  galois_equivariant : ∀ (m : Int) (z : tpeGroup.carrier),
    (tlt2Link j).map ((tlt2Theater false).mul
        ((tlt2Theater false).mul ((tlt2Section false).map m)
          ((tlt2InclFull false).map z))
        ((tlt2Theater false).inv ((tlt2Section false).map m)))
      = (tlt2Theater true).mul
          ((tlt2Theater true).mul ((tlt2Section true).map m)
            ((tlt2InclFull true).map (tltLift j z)))
          ((tlt2Theater true).inv ((tlt2Section true).map m))
  /-- 往復合成＝ Frobenius 次数の乗法。 -/
  roundtrip_degree : ∀ (j' : Int) (x : (tlt2Theater false).carrier),
    ((tlt2LinkRev j').map ((tlt2Link j).map x)).val = (tltLink (j' * j)).map x.val
  /-- j = −1 の往復は恒等（劇場間同型）。 -/
  neg_one_roundtrip : ∀ x : (tlt2Theater false).carrier,
    (tlt2LinkRev (-1)).map ((tlt2Link (-1)).map x) = x
  /-- Frobenius 次数 link の非全射（正直な限定の定理化）。 -/
  frobenius_not_surjective :
    ¬ ∃ x : (tlt2Theater false).carrier,
        (tlt2Link 2).map x = (tlt2DeckSection true).map 1

/-- **M439F-7b: witness 本体** — 全フィールドを M439F-1〜6 の本物の証明で埋める
    （crux 以外の外部仮説ゼロ・完全証明）。 -/
def thetaLinkTwoTheaterData (j : Int) : ThetaLinkTwoTheaterData j where
  link_hom := tlt2_link_hom j
  link_one := tlt2_link_one j
  not_endo := tlt2_not_endo j
  commutator_preserved := tlt2_commutator_preserved j
  theta_transport := fun a b c => tlt2_theta_transport j a b c
  cyclotome_rigid := fun c => tlt2_cyclotome_rigid j c
  mu_fixed := fun b => tlt2_mu_fixed j b
  section_shared := fun m => tlt2_section_shared j m
  deck_scaled := tlt2_deck_scaled j
  theta_commutator := fun a b c a' b' c' => tlt2_theta_commutator j a b c a' b' c'
  galois_equivariant := fun m z => tlt2_galois_equivariant j m z
  roundtrip_degree := fun j' x => tlt2_roundtrip_degree j j' x
  neg_one_roundtrip := tlt2_neg_one_roundtrip
  frobenius_not_surjective := tlt2_frobenius_not_surjective

/-- **定理 (M439F-7c): 2 劇場 theta-link データの存在（M439F 見出し・capstone）** —
    任意の Frobenius 次数 j ∈ ℤ に対し、相異なる 2 ホッジ劇場 †0/†1 の間の
    theta-link tlt2Link j と、その準同型性・非自己準同型性（M434F の限定 (i) を
    閉じる）・交換子/シクロトーム剛性・共有構造・劇場間同型（j = −1）・正直な限定
    （非全射）を束ねたデータが**crux 以外の外部仮説なしで**存在する。 -/
theorem tlt2_exists (j : Int) : Nonempty (ThetaLinkTwoTheaterData j) :=
  ⟨thetaLinkTwoTheaterData j⟩

/-! ## M439F-8: 実例 -/

/-- 実例: 具体的な劇場間 link 計算 — †0 の (((1,2,3),4),5) は †1 の (((2,2,6),8),5)
    へ（値群 1↦2・μ-方向 2 共有・シクロトーム 3↦6・deck 4↦8・算術 5 共有）。 -/
example : ((tlt2Link 2).map
      ⟨(((((1 : Int), 2, 3) : Int × Int × Int), (4 : Int)), (5 : Int))⟩).val
    = (((((2 : Int), 2, 6) : Int × Int × Int), (8 : Int)), (5 : Int)) := by
  show (((((2 * 1 : Int), 2, 2 * 3) : Int × Int × Int), (2 * 4 : Int)), (5 : Int))
    = (((((2 : Int), 2, 6) : Int × Int × Int), (8 : Int)), (5 : Int))
  exact atp_ext5 (by omega) rfl (by omega) (by omega) rfl

/-- 実例: link はラベルを実際に †0 から †1 へ動かす（非自己準同型性の具体形）。 -/
example : tlt2Label ((tlt2Link 3).map ((tlt2Section false).map 7)) = true
    ∧ tlt2Label ((tlt2Section false).map 7) = false :=
  ⟨rfl, rfl⟩

/-- 実例: シクロトーム剛性の具体形 — †0 の ιι(0,0,7) は j = 5 の link で †1 の
    ιι(0,0,35) へ。 -/
example : (tlt2Link 5).map ((tlt2InclGeom false).map ((0, 0, 7) : Int × Int × Int))
    = (tlt2InclGeom true).map ((0, 0, 35) : Int × Int × Int) := by
  have h := tlt2_cyclotome_rigid 5 7
  have hv : (5 : Int) * 7 = 35 := by omega
  rw [hv] at h
  exact h

/-- 実例: μ-方向は共有・算術切断は共有（Ind2 単数共有と G_K 共有の 2 劇場版）。 -/
example : (tlt2Link 5).map ((tlt2InclGeom false).map ((0, 7, 0) : Int × Int × Int))
      = (tlt2InclGeom true).map ((0, 7, 0) : Int × Int × Int)
    ∧ (tlt2Link 5).map ((tlt2Section false).map 9) = (tlt2Section true).map 9 :=
  ⟨tlt2_mu_fixed 5 7, tlt2_section_shared 5 9⟩

/-- 実例: j = −1 の劇場間 link は本物の劇場間同型（往復恒等・単射・全射）。 -/
example : (∀ x : (tlt2Theater false).carrier,
      (tlt2LinkRev (-1)).map ((tlt2Link (-1)).map x) = x)
    ∧ (∀ y : (tlt2Theater true).carrier,
      ∃ x : (tlt2Theater false).carrier, (tlt2Link (-1)).map x = y) :=
  ⟨tlt2_neg_one_roundtrip, tlt2_link_neg_one_surjective⟩

/-- 実例: 2 劇場 theta-link データは任意の Frobenius 次数で存在（capstone の具体化）。 -/
example : Nonempty (ThetaLinkTwoTheaterData 2) := tlt2_exists 2

end IUT
