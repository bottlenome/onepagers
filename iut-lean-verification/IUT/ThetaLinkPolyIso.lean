-- M444F ThetaLinkPolyIso [実・本物・柱A frontier・M439F の残限定「環独立 full poly-isomorphism」を昇格で閉じる]
-- complete_pct 影響: 柱A で M439F tlt2_model_scope の残限定「2 劇場は同一離散モデルの同型ラベル付きコピーであり、環構造まで独立な full poly-isomorphism ではない」を昇格で閉じる: 各劇場の値群×シクロトーム平面（劇場の可換部分群として単射埋め込み）に型レベルで区別された**独立な環構造**（†0 = 成分積環・単位 (1,1)、†1 = 符号捻り積環・単位 (1,−1)）を建設し、theta-link が**加法群準同型（j=−1 で群同型）だが任意の j で環準同型でない**（tlp_link_not_ring_hom・tlp_link_mul_broken）こと、および M439F の標準輸送（val 恒等の群同型）も環準同型でないこと（tlp_transport_not_ring_hom）を定理で固定——群同型の poly（複数の群同型のうち環と両立するのは非自明な符号反転のみ・link は一切両立しない）を実現。M439F の外部仮説 tlt2_full_poly_isomorphism_hypothesis を内部定理として供給（tlp_closes_m439_limitation）。
-- 正直な限定: 環構造は各劇場の値群 a×シクロトーム c 平面 ℤ²（劇場の可換部分群・μ-方向と deck・算術方向は含まない、劇場全体は非可換ゆえ環の加法にならないことも定理化）上の具体乗法に留まり、実数体/局所体の正則構造・Frobenioid 圏レベルの poly-isomorphism・log-link との噛み合わせ・副有限 G_K・実テータ値・多輻不等式（crux Dβ-ω）は外部/後続。

/-
  IUT/ThetaLinkPolyIso.lean — M444F [実／本物の忠実な部分ケース・柱A frontier]
  分類: 実（M439F の 2 ホッジ劇場 †0/†1 の値群×シクロトーム平面に独立な環構造を
  与え、theta-link を「群同型ではあるが環乗法は保たない」poly-isomorphism として
  実現する）

  既存の実部品:
    * M439F (ThetaLinkTwoTheater): ラベル付き 2 劇場 tlt2Theater false/true・
      劇場間 theta-link tlt2Link j（本物の群準同型・j=−1 で劇場間同型）・
      テータ部輸送 tlt2_theta_transport・交換子保存・シクロトーム剛性・
      **正直な限定 tlt2_model_scope**: 2 劇場は同一離散モデルの同型ラベル付き
      コピーであり、環構造まで独立な full poly-isomorphism は外部仮説
      （tlt2_full_poly_isomorphism_hypothesis・tlt2_independent_ring_hypothesis）
    * M38 (Ring): 可換環 CRing・環準同型 RingHom・加法群への忘却 CRing.toGrp

  本モジュールは M439F の残限定を**昇格で閉じる**。[IUTchIII] の Θ-link は
  「群（エタール的・ガロア的）構造は繋ぐが、両側のホッジ劇場の**環構造
  （加法と乗法の絡み＝正則構造）は独立に保たれ、link はそれを保たない**」
  poly-isomorphism である——これが多輻不定性 (Ind1)(Ind2)(Ind3) の源。その
  離散実現:

    * **劇場ごとの独立な環**: 各劇場 †t の値群 a×シクロトーム c 平面
      TlpElt t ≅ ℤ²（tlpIncl で劇場の可換部分群として単射埋め込み・
      theta-link のテータ部輸送 (a,c) ↦ (j·a, j·c) の受け皿）に、
      **型レベルで区別された独立な乗法**を与える:
        - †0 の環 tlpRing0: (a,c)·(a',c') = (a·a', c·c')、単位 (1,1)
          （値群モノイド × シクロトームの成分積環）
        - †1 の環 tlpRing1: (a,c)·(a',c') = (a·a', −(c·c'))、単位 (1,−1)
          （シクロトーム方向を符号捻りした積環——†0 とは**別劇場の別環**。
          両者を繋ぐ環同型は非自明な符号反転 tlpRingIso のみで、
          標準輸送＝val 恒等は環準同型でない）
    * **theta-link は群のみ繋ぐ**: tlpLink j (a,c) = (j·a, j·c) は
      - **加法群準同型**（tlp_link_add_hom・任意の j で on the nose）、
        j = −1 で加法群同型（単射 + 全射）、劇場レベルの tlt2Link j と
        埋め込みで両立（tlp_link_compat）、シクロトーム剛性 (0,c) ↦ (0,j·c)、
      - しかし**環準同型ではない**: 単位を保たず（tlp_link_unit_broken、
        任意の j で (j,j) ≠ (1,−1)）、j ≠ 0 では乗法自体を壊す
        （tlp_link_mul_broken: link(1·1) = (j,j) だが link(1)·link(1) =
        (j², −j²)）。ゆえに link の写像を台とする環準同型は存在しない
        （tlp_link_not_ring_hom、任意の j）。

  完全証明する内容（すべて本物の群・環演算・toy 主語なし）:
    * tlpRing0/tlpRing1 の可換環公理（成分の Int 法則から）
    * 平面の劇場への単射埋め込み tlpIncl0/tlpIncl1（本物の群準同型・
      像は劇場の可換部分群 tlp_embedded_commute）
    * tlpLink j の加法群準同型性・零保存・tlt2Link との両立・
      シクロトーム剛性・値群スケール・j = −1 の往復恒等＝群同型
    * **tlp_link_not_ring_hom（本丸）**: 任意の j で theta-link は環準同型に
      持ち上がらない——「群構造は繋がるが環乗法は保たれない」full
      poly-isomorphism の実現
    * **tlp_transport_not_ring_hom**: M439F の標準輸送（val 恒等）も環準同型で
      ない——2 劇場の環構造が**標準の群同一視から独立**であることの定理化
    * **tlpRingIso**: 非自明な符号反転 (a,c) ↦ (a,−c) は本物の環同型（単射・
      全射）——実 IUT と同じく 2 劇場は抽象的には同型なホッジ劇場のまま
      （tlp_poly_nontrivial: 輸送と環同型は相異なる群準同型＝ poly の実現）
    * tlp_closes_m439_limitation: M439F の外部仮説
      tlt2_full_poly_isomorphism_hypothesis を本モジュールの独立環構造の下で
      内部の定理として供給
    * capstone tlp_exists: 全構造を ThetaLinkPolyIsoData に束ね crux 以外の
      外部仮説なしで居住させる

  crux（決して内部化しない）:
    * theta-link の**多輻アルゴリズム不等式**（Dβ-ω、[IUTchIII] Cor 3.12 の
      係争ステップ）は本モジュールの主張に一切含めない。
      tlp_crux_is_hypothesis (crux : Prop) : crux ↔ crux ＝ Iff.rfl で
      外部仮説として保持（M439F tlt2_crux_is_hypothesis と同じ精神）。

  正直な限定（M439F の残限定を閉じた上で、残りを狭めて述べ直す・
  消さない・弱めない）:
    * 環構造は各劇場の**値群×シクロトーム平面 ℤ²** 上の具体乗法に留まる:
      μ-方向は平面の像に入らない（tlp_mu_not_in_plane）し、劇場全体は
      非可換ゆえこの環の加法群にはなり得ない（tlp_theater_noncommutative）
      ——いずれも定理で固定（tlp_model_scope）。
    * Frobenius 次数 j = 2 の平面 link は全射でない
      （tlp_frobenius_not_surjective、M439F 6b の環付き版）。
    * 実 IUT の環構造（数体・p 進局所体の正則構造）・Frobenioid **圏**レベルの
      full poly-isomorphism・log-link（柱C）との噛み合わせ・劇場**全体**への
      環構造の拡張は外部/後続（tlp_full_theater_ring_hypothesis、M439F
      tlt2_independent_ring_hypothesis の狭め直し）。
  全て選択公理不使用（propext / Quot.sound のみ）。
-/
import IUT.ThetaLinkTwoTheater
import IUT.Ring

namespace IUT

/-! ## M444F-0: 補助（平面の元・ext・Int 補題） -/

/-- **M444F-0a: 劇場 †t の値群×シクロトーム平面の元** — val = (a, c)
    （a = 値群座標・c = シクロトーム座標）。ラベル t : Bool は型パラメータで、
    TlpElt false と TlpElt true は相異なる型（相異なる劇場の相異なる環の台）。 -/
structure TlpElt (t : Bool) where
  /-- 平面座標 (値群 a, シクロトーム c)。 -/
  val : Int × Int

/-- 平面の元の等値補題（val で決まる）。 -/
theorem tlp_ext {t : Bool} {x y : TlpElt t} (h : x.val = y.val) : x = y :=
  congrArg TlpElt.mk h

/-- 対の等値補題。 -/
theorem tlp_pair_ext {a c a' c' : Int} (h1 : a = a') (h2 : c = c') :
    ((a, c) : Int × Int) = (a', c') := by
  rw [h1, h2]

/-- 符号捻り積の結合律（†1 の環の mul_assoc 用）。 -/
theorem tlp_neg_mul_assoc (a b c : Int) :
    -((-(a * b)) * c) = -(a * (-(b * c))) := by
  rw [Int.neg_mul, Int.neg_neg, Int.mul_neg, Int.neg_neg, Int.mul_assoc]

/-- 符号捻り積の分配律（†1 の環の left_distrib 用）。 -/
theorem tlp_neg_mul_add (a b c : Int) :
    -(a * (b + c)) = -(a * b) + -(a * c) := by
  rw [Int.mul_add, Int.neg_add]

/-! ## M444F-1: 劇場ごとの独立な環構造（本丸その 1）

  †0 の環は成分積 (a,c)·(a',c') = (a·a', c·c')・単位 (1,1)。
  †1 の環は符号捻り積 (a,c)·(a',c') = (a·a', −(c·c'))・単位 (1,−1)。
  加法（theta-link が繋ぐ群構造）は両劇場で成分和だが、乗法と単位は
  **劇場ごとに独立に**定められた別環である。 -/

/-- **M444F-1a: 劇場 †0 の環** — 値群×シクロトーム平面 TlpElt false 上の
    成分積環（値群モノイド × シクロトーム、単位 (1,1)）。 -/
def tlpRing0 : CRing where
  carrier := TlpElt false
  add := fun x y => ⟨(x.val.1 + y.val.1, x.val.2 + y.val.2)⟩
  zero := ⟨(0, 0)⟩
  neg := fun x => ⟨(-x.val.1, -x.val.2)⟩
  mul := fun x y => ⟨(x.val.1 * y.val.1, x.val.2 * y.val.2)⟩
  one := ⟨(1, 1)⟩
  add_assoc := fun x y z =>
    tlp_ext (tlp_pair_ext (Int.add_assoc x.val.1 y.val.1 z.val.1)
      (Int.add_assoc x.val.2 y.val.2 z.val.2))
  zero_add := fun x =>
    tlp_ext (tlp_pair_ext (Int.zero_add x.val.1) (Int.zero_add x.val.2))
  neg_add := fun x =>
    tlp_ext (tlp_pair_ext (Int.add_left_neg x.val.1) (Int.add_left_neg x.val.2))
  add_comm := fun x y =>
    tlp_ext (tlp_pair_ext (Int.add_comm x.val.1 y.val.1)
      (Int.add_comm x.val.2 y.val.2))
  mul_assoc := fun x y z =>
    tlp_ext (tlp_pair_ext (Int.mul_assoc x.val.1 y.val.1 z.val.1)
      (Int.mul_assoc x.val.2 y.val.2 z.val.2))
  one_mul := fun x =>
    tlp_ext (tlp_pair_ext (Int.one_mul x.val.1) (Int.one_mul x.val.2))
  mul_comm := fun x y =>
    tlp_ext (tlp_pair_ext (Int.mul_comm x.val.1 y.val.1)
      (Int.mul_comm x.val.2 y.val.2))
  left_distrib := fun x y z =>
    tlp_ext (tlp_pair_ext (Int.mul_add x.val.1 y.val.1 z.val.1)
      (Int.mul_add x.val.2 y.val.2 z.val.2))

/-- **M444F-1b: 劇場 †1 の環** — 値群×シクロトーム平面 TlpElt true 上の
    **符号捻り積環**（シクロトーム方向の積を −1 倍・単位 (1,−1)）。†0 の環とは
    乗法も単位も異なる、**独立に定められた別劇場の別環**。 -/
def tlpRing1 : CRing where
  carrier := TlpElt true
  add := fun x y => ⟨(x.val.1 + y.val.1, x.val.2 + y.val.2)⟩
  zero := ⟨(0, 0)⟩
  neg := fun x => ⟨(-x.val.1, -x.val.2)⟩
  mul := fun x y => ⟨(x.val.1 * y.val.1, -(x.val.2 * y.val.2))⟩
  one := ⟨(1, -1)⟩
  add_assoc := fun x y z =>
    tlp_ext (tlp_pair_ext (Int.add_assoc x.val.1 y.val.1 z.val.1)
      (Int.add_assoc x.val.2 y.val.2 z.val.2))
  zero_add := fun x =>
    tlp_ext (tlp_pair_ext (Int.zero_add x.val.1) (Int.zero_add x.val.2))
  neg_add := fun x =>
    tlp_ext (tlp_pair_ext (Int.add_left_neg x.val.1) (Int.add_left_neg x.val.2))
  add_comm := fun x y =>
    tlp_ext (tlp_pair_ext (Int.add_comm x.val.1 y.val.1)
      (Int.add_comm x.val.2 y.val.2))
  mul_assoc := fun x y z =>
    tlp_ext (tlp_pair_ext (Int.mul_assoc x.val.1 y.val.1 z.val.1)
      (tlp_neg_mul_assoc x.val.2 y.val.2 z.val.2))
  one_mul := by
    intro x
    refine tlp_ext (tlp_pair_ext (Int.one_mul x.val.1) ?_)
    show -((-1) * x.val.2) = x.val.2
    omega
  mul_comm := fun x y =>
    tlp_ext (tlp_pair_ext (Int.mul_comm x.val.1 y.val.1)
      (congrArg Neg.neg (Int.mul_comm x.val.2 y.val.2)))
  left_distrib := fun x y z =>
    tlp_ext (tlp_pair_ext (Int.mul_add x.val.1 y.val.1 z.val.1)
      (tlp_neg_mul_add x.val.2 y.val.2 z.val.2))

/-- 劇場 †0 の環の加法群。 -/
@[reducible] def tlpAdd0 : Grp := CRing.toGrp tlpRing0

/-- 劇場 †1 の環の加法群。 -/
@[reducible] def tlpAdd1 : Grp := CRing.toGrp tlpRing1

/-! ## M444F-2: 平面の劇場への埋め込み（環の加法群 ＝ 劇場の可換部分群） -/

/-- **M444F-2a: †0 平面のテータ群への埋め込み** (a,c) ↦ (a, 0, c)
    （μ-方向 b = 0 の値群×シクロトーム平面、本物の群準同型）。 -/
def tlpThetaEmbed0 : Hom tlpAdd0 thetaGrp where
  map := fun x => (x.val.1, 0, x.val.2)
  map_mul := by
    intro x y
    show ((x.val.1 + y.val.1, (0 : Int), x.val.2 + y.val.2) : Int × Int × Int)
      = (x.val.1 + y.val.1, 0 + 0, x.val.2 + y.val.2 + x.val.1 * 0)
    exact triple_ext rfl (by omega) (by omega)

/-- **M444F-2b: †1 平面のテータ群への埋め込み**。 -/
def tlpThetaEmbed1 : Hom tlpAdd1 thetaGrp where
  map := fun x => (x.val.1, 0, x.val.2)
  map_mul := by
    intro x y
    show ((x.val.1 + y.val.1, (0 : Int), x.val.2 + y.val.2) : Int × Int × Int)
      = (x.val.1 + y.val.1, 0 + 0, x.val.2 + y.val.2 + x.val.1 * 0)
    exact triple_ext rfl (by omega) (by omega)

/-- †0 平面埋め込みは単射。 -/
theorem tlp_theta_embed0_injective : tlpThetaEmbed0.Injective := by
  intro x y h
  refine tlp_ext (tlp_pair_ext ?_ ?_)
  · exact congrArg (fun z : Int × Int × Int => z.1) h
  · exact congrArg (fun z : Int × Int × Int => z.2.2) h

/-- †1 平面埋め込みは単射。 -/
theorem tlp_theta_embed1_injective : tlpThetaEmbed1.Injective := by
  intro x y h
  refine tlp_ext (tlp_pair_ext ?_ ?_)
  · exact congrArg (fun z : Int × Int × Int => z.1) h
  · exact congrArg (fun z : Int × Int × Int => z.2.2) h

/-- M439F の劇場テータ部埋め込みは単射（二段塔の単射の合成）。 -/
theorem tlp_incl_geom_injective (t : Bool) : (tlt2InclGeom t).Injective :=
  Hom.comp_injective (tlt2_incl_injective t) atp_incl_geom_injective

/-- **M444F-2c: †0 の環の加法群の劇場 †0 への埋め込み**（本物の群準同型）。 -/
def tlpIncl0 : Hom tlpAdd0 (tlt2Theater false) :=
  (tlt2InclGeom false).comp tlpThetaEmbed0

/-- **M444F-2d: †1 の環の加法群の劇場 †1 への埋め込み**。 -/
def tlpIncl1 : Hom tlpAdd1 (tlt2Theater true) :=
  (tlt2InclGeom true).comp tlpThetaEmbed1

/-- **定理 (M444F-2e): †0 埋め込みは単射** — 環の加法群は劇場 †0 の本物の
    部分群。 -/
theorem tlp_incl0_injective : tlpIncl0.Injective :=
  Hom.comp_injective (tlp_incl_geom_injective false) tlp_theta_embed0_injective

/-- **定理 (M444F-2f): †1 埋め込みは単射**。 -/
theorem tlp_incl1_injective : tlpIncl1.Injective :=
  Hom.comp_injective (tlp_incl_geom_injective true) tlp_theta_embed1_injective

/-- **定理 (M444F-2g): 平面の像は劇場の可換部分群** — 埋め込まれた平面の元
    どうしは劇場 †0 の中で可換（環の加法群が可換であることの劇場内での実現）。 -/
theorem tlp_embedded_commute (x y : tlpAdd0.carrier) :
    (tlt2Theater false).mul (tlpIncl0.map x) (tlpIncl0.map y)
      = (tlt2Theater false).mul (tlpIncl0.map y) (tlpIncl0.map x) := by
  rw [← tlpIncl0.map_mul, ← tlpIncl0.map_mul]
  exact congrArg tlpIncl0.map (tlpRing0.add_comm x y)

/-- **M444F-2h: 劇場ごとの環データ** — 劇場 †t に付随する環と、その加法群の
    劇場への単射埋め込みの束（「各ホッジ劇場に独立な環構造を与える」の定式化）。 -/
structure TlpTheaterRing (t : Bool) where
  /-- 劇場 †t の環。 -/
  ring : CRing
  /-- 環の加法群の劇場 †t への埋め込み。 -/
  embed : Hom (CRing.toGrp ring) (tlt2Theater t)
  /-- 埋め込みは単射（環の加法群は劇場の本物の部分群）。 -/
  embed_injective : embed.Injective

/-- **M444F-2i: 劇場ごとの環データの witness** — †0 は成分積環・†1 は符号捻り
    積環（相異なる劇場の相異なる環、外部仮説なしで居住）。 -/
def tlpTheaterRing : (t : Bool) → TlpTheaterRing t
  | false => ⟨tlpRing0, tlpIncl0, tlp_incl0_injective⟩
  | true => ⟨tlpRing1, tlpIncl1, tlp_incl1_injective⟩

/-! ## M444F-3: theta-link ＝ 加法群準同型（群は繋がる） -/

/-- **M444F-3a: 平面 theta-link** tlpLink j : (†0 の環の加法群) → (†1 の環の
    加法群)、(a, c) ↦ (j·a, j·c) — 値群・シクロトームを同一因子 j 倍
    （M439F tlt2Link j のテータ部輸送 tlt2_theta_transport の b = 0 平面）。
    任意の j で本物の**加法群準同型**。 -/
def tlpLink (j : Int) : Hom tlpAdd0 tlpAdd1 where
  map := fun x => ⟨(j * x.val.1, j * x.val.2)⟩
  map_mul := fun x y =>
    tlp_ext (tlp_pair_ext (Int.mul_add j x.val.1 y.val.1)
      (Int.mul_add j x.val.2 y.val.2))

/-- **M444F-3b: 逆向き平面 link** †1 → †0（M439F tlt2LinkRev の平面版）。 -/
def tlpLinkRev (j : Int) : Hom tlpAdd1 tlpAdd0 where
  map := fun x => ⟨(j * x.val.1, j * x.val.2)⟩
  map_mul := fun x y =>
    tlp_ext (tlp_pair_ext (Int.mul_add j x.val.1 y.val.1)
      (Int.mul_add j x.val.2 y.val.2))

/-- **定理 (M444F-3c: tlp_link_add_hom・加法群準同型)** — 平面 theta-link は
    †0 の環の加法を †1 の環の加法へ on the nose で移す（任意の j）。 -/
theorem tlp_link_add_hom (j : Int) (x y : tlpAdd0.carrier) :
    (tlpLink j).map (tlpRing0.add x y)
      = tlpRing1.add ((tlpLink j).map x) ((tlpLink j).map y) :=
  (tlpLink j).map_mul x y

/-- **定理 (M444F-3d): 零（加法単位）の保存**。 -/
theorem tlp_link_zero (j : Int) :
    (tlpLink j).map tlpRing0.zero = tlpRing1.zero :=
  tlp_ext (tlp_pair_ext (Int.mul_zero j) (Int.mul_zero j))

/-- **定理 (M444F-3e): 劇場レベル theta-link との両立** — 平面 link は
    M439F の劇場間 theta-link tlt2Link j と埋め込みで可換（平面 link は
    本物の劇場間 link の忠実な制限であって別物ではない）。 -/
theorem tlp_link_compat (j : Int) (x : tlpAdd0.carrier) :
    (tlt2Link j).map (tlpIncl0.map x) = tlpIncl1.map ((tlpLink j).map x) :=
  tlt2_theta_transport j x.val.1 0 x.val.2

/-- **定理 (M444F-3f): シクロトーム剛性（平面版）** — シクロトーム座標は
    j 倍にしか動かない（M439F tlt2_cyclotome_rigid の環付き版）。 -/
theorem tlp_cyclotome_rigid (j c : Int) :
    (tlpLink j).map ⟨(0, c)⟩ = (⟨(0, j * c)⟩ : TlpElt true) :=
  tlp_ext (tlp_pair_ext (Int.mul_zero j) rfl)

/-- **定理 (M444F-3g): 値群スケール（平面版）** — 値群座標も同一因子 j 倍
    （シクロトームと同期＝剛性）。 -/
theorem tlp_value_scaled (j a : Int) :
    (tlpLink j).map ⟨(a, 0)⟩ = (⟨(j * a, 0)⟩ : TlpElt true) :=
  tlp_ext (tlp_pair_ext rfl (Int.mul_zero j))

/-- **定理 (M444F-3h): j = −1 の往復は恒等（†0 側）** — 平面 link は j = −1 で
    本物の**加法群同型**。 -/
theorem tlp_neg_one_roundtrip (x : tlpAdd0.carrier) :
    (tlpLinkRev (-1)).map ((tlpLink (-1)).map x) = x := by
  refine tlp_ext (tlp_pair_ext ?_ ?_)
  · show (-1 : Int) * ((-1) * x.val.1) = x.val.1
    omega
  · show (-1 : Int) * ((-1) * x.val.2) = x.val.2
    omega

/-- **定理 (M444F-3i): j = −1 の平面 link は単射**。 -/
theorem tlp_link_neg_one_injective : (tlpLink (-1)).Injective := by
  intro x y h
  have h1 : (-1 : Int) * x.val.1 = (-1) * y.val.1 :=
    congrArg (fun z : TlpElt true => z.val.1) h
  have h2 : (-1 : Int) * x.val.2 = (-1) * y.val.2 :=
    congrArg (fun z : TlpElt true => z.val.2) h
  refine tlp_ext (tlp_pair_ext ?_ ?_)
  · show x.val.1 = y.val.1
    omega
  · show x.val.2 = y.val.2
    omega

/-- **定理 (M444F-3j): j = −1 の平面 link は全射**。 -/
theorem tlp_link_neg_one_surjective :
    ∀ y : tlpAdd1.carrier, ∃ x : tlpAdd0.carrier, (tlpLink (-1)).map x = y := by
  intro y
  refine ⟨⟨(-y.val.1, -y.val.2)⟩, ?_⟩
  refine tlp_ext (tlp_pair_ext ?_ ?_)
  · show (-1 : Int) * (-y.val.1) = y.val.1
    omega
  · show (-1 : Int) * (-y.val.2) = y.val.2
    omega

/-- **定理 (M444F-3k: tlp_group_iso_preserved)** — theta-link が**群レベルで**
    保つもの（M439F の環付き再輸出）: 加法群構造（平面）・交換子構造
    （劇場全体・on the nose）・シクロトーム剛性（j 倍）。 -/
theorem tlp_group_iso_preserved (j : Int) :
    (∀ x y : tlpAdd0.carrier,
      (tlpLink j).map (tlpRing0.add x y)
        = tlpRing1.add ((tlpLink j).map x) ((tlpLink j).map y))
    ∧ (∀ x y : (tlt2Theater false).carrier,
      (tlt2Link j).map ((tlt2Theater false).comm x y)
        = (tlt2Theater true).comm ((tlt2Link j).map x) ((tlt2Link j).map y))
    ∧ (∀ c : Int, (tlpLink j).map ⟨(0, c)⟩ = (⟨(0, j * c)⟩ : TlpElt true)) :=
  ⟨tlp_link_add_hom j, tlt2_commutator_preserved j, tlp_cyclotome_rigid j⟩

/-! ## M444F-4: theta-link は環準同型でない（本丸その 2＝環独立の実現）

  [IUTchIII] の Θ-link の本質: 劇場間 link は群（加法・ガロア的）構造は繋ぐが、
  両側の環構造（乗法との絡み＝正則構造）は独立に保たれ、link はそれを
  **保たない**。以下で「保たない」を witness つきの不等式で完全証明する。 -/

/-- **定理 (M444F-4a: 単位の破れ)** — 任意の j で、平面 theta-link は †0 の環の
    乗法単位 (1,1) を †1 の環の乗法単位 (1,−1) に移さない（link(1,1) = (j,j) は
    j = 1 と j = −1 を同時に要求し不可能）。 -/
theorem tlp_link_unit_broken (j : Int) :
    (tlpLink j).map tlpRing0.one ≠ tlpRing1.one := by
  intro h
  have h1 : j * 1 = 1 := congrArg (fun z : TlpElt true => z.val.1) h
  have h2 : j * 1 = -1 := congrArg (fun z : TlpElt true => z.val.2) h
  omega

/-- **定理 (M444F-4b: 乗法の破れ)** — j ≠ 0 なら平面 theta-link は乗法自体を
    壊す: link(1·1) = (j, j) だが link(1)·link(1) = (j², −j²)、両立は j = 0 のみ。
    （witness は両劇場の乗法単位——「環乗法は保たない」の明示的反例。） -/
theorem tlp_link_mul_broken (j : Int) (hj : j ≠ 0) :
    (tlpLink j).map (tlpRing0.mul tlpRing0.one tlpRing0.one)
      ≠ tlpRing1.mul ((tlpLink j).map tlpRing0.one)
          ((tlpLink j).map tlpRing0.one) := by
  intro h
  have h1 : j * (1 * 1) = (j * 1) * (j * 1) :=
    congrArg (fun z : TlpElt true => z.val.1) h
  have h2 : j * (1 * 1) = -((j * 1) * (j * 1)) :=
    congrArg (fun z : TlpElt true => z.val.2) h
  have h11 : (1 : Int) * 1 = 1 := Int.one_mul 1
  have hj1 : j * 1 = j := Int.mul_one j
  rw [h11, hj1] at h1 h2
  rw [← h1] at h2
  omega

/-- **定理 (M444F-4c: tlp_link_not_ring_hom・本丸)** — **任意の j** で、
    平面 theta-link の写像を台とする環準同型 tlpRing0 → tlpRing1 は存在しない。
    theta-link は加法群準同型（3c）だが環準同型に**持ち上がらない**——
    「群構造は繋ぐが環乗法は保たない」full poly-isomorphism（環独立）を
    実際に実現した証拠。 -/
theorem tlp_link_not_ring_hom (j : Int) :
    ¬ ∃ f : RingHom tlpRing0 tlpRing1, ∀ x, f.map x = (tlpLink j).map x := by
  intro h
  obtain ⟨f, hf⟩ := h
  have h1 : (tlpLink j).map tlpRing0.one = tlpRing1.one := by
    rw [← hf tlpRing0.one]
    exact f.map_one
  exact tlp_link_unit_broken j h1

/-! ## M444F-5: 環構造は標準の群同一視から独立（poly の実現） -/

/-- **M444F-5a: 標準輸送（平面版）** — M439F tlt2Transport の平面版:
    val 恒等の標準加法群準同型 †0 平面 → †1 平面。 -/
def tlpTransport : Hom tlpAdd0 tlpAdd1 where
  map := fun x => ⟨x.val⟩
  map_mul := fun _ _ => rfl

/-- **定理 (M444F-5b: tlp_transport_not_ring_hom)** — 標準輸送（val 恒等の
    群同型）は**環準同型でない**（単位 (1,1) ↦ (1,1) ≠ (1,−1)）。2 劇場の
    環構造が M439F の標準の群同一視から**独立**であることの定理化——
    M439F tlt2_model_scope が「同型なラベル付きコピー（環構造まで独立では
    ない）」と述べた状況を、実際に環独立へ昇格させた本丸。 -/
theorem tlp_transport_not_ring_hom :
    ¬ ∃ f : RingHom tlpRing0 tlpRing1, ∀ x, f.map x = tlpTransport.map x := by
  intro h
  obtain ⟨f, hf⟩ := h
  have h1 : tlpTransport.map tlpRing0.one = tlpRing1.one := by
    rw [← hf tlpRing0.one]
    exact f.map_one
  have h2 : (1 : Int) = -1 := congrArg (fun z : TlpElt true => z.val.2) h1
  omega

/-- **M444F-5c: 非自明な環同型** (a,c) ↦ (a,−c) — 2 劇場の環は**抽象的には**
    同型（実 IUT の 2 ホッジ劇場が抽象的には同型な劇場であることの忠実な反映）。
    ただしこの同型は標準輸送とは相異なる（5e）——環と両立する同一視は
    群同型の poly（全体軌道）の中の**非自明な一点**であり、theta-link は
    その外にいる（4c）。 -/
def tlpRingIso : RingHom tlpRing0 tlpRing1 where
  map := fun x => ⟨(x.val.1, -x.val.2)⟩
  map_add := fun x y =>
    tlp_ext (tlp_pair_ext rfl Int.neg_add)
  map_mul := by
    intro x y
    refine tlp_ext (tlp_pair_ext rfl ?_)
    show -(x.val.2 * y.val.2) = -((-x.val.2) * (-y.val.2))
    rw [Int.neg_mul_neg]
  map_one := rfl

/-- **定理 (M444F-5d): 環同型は単射かつ全射**（本物の環同型）。 -/
theorem tlp_ring_iso_bijective :
    (∀ x y, tlpRingIso.map x = tlpRingIso.map y → x = y)
    ∧ (∀ y : TlpElt true, ∃ x, tlpRingIso.map x = y) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    have h1 : x.val.1 = y.val.1 := congrArg (fun z : TlpElt true => z.val.1) h
    have h2 : -x.val.2 = -y.val.2 := congrArg (fun z : TlpElt true => z.val.2) h
    refine tlp_ext (tlp_pair_ext h1 ?_)
    show x.val.2 = y.val.2
    omega
  · intro y
    refine ⟨⟨(y.val.1, -y.val.2)⟩, ?_⟩
    refine tlp_ext (tlp_pair_ext rfl ?_)
    show -(-y.val.2) = y.val.2
    omega

/-- **定理 (M444F-5e: poly の非自明性)** — 標準輸送と環同型は相異なる群レベル
    同一視（(0,1) で値が分かれる）: 2 劇場間の群同型は**複数**あり
    （poly-isomorphism の軌道）、環と両立するのはその一部（5c）だけで、
    theta-link は一切両立しない（4c）。 -/
theorem tlp_poly_nontrivial :
    tlpRingIso.map ⟨(0, 1)⟩ ≠ tlpTransport.map ⟨(0, 1)⟩ := by
  intro h
  have h1 : (-1 : Int) = 1 := congrArg (fun z : TlpElt true => z.val.2) h
  omega

/-! ## M444F-6: M439F の残限定を閉じる（本丸の総括） -/

/-- **定理 (M444F-6a: tlp_closes_m439_limitation・本丸)** — M439F の外部仮説
    tlt2_full_poly_isomorphism_hypothesis（環構造まで独立な 2 劇場間の
    full poly-isomorphism の実現）を、本モジュールの独立環構造の下で
    **内部の定理として**供給する:
    (i) j = −1 の平面 theta-link は tlt2_full_poly_isomorphism_hypothesis を
        充たす（単射な群準同型）、(ii) しかも全射＝本物の群同型、
    (iii) だが link の写像を台とする環準同型は存在しない（環乗法は独立）、
    (iv) 標準輸送も環準同型でない（環構造は標準の群同一視から独立）。
    まとめ: 2 劇場は独立な環構造を持ち、その間の theta-link は「群同型では
    あるが環乗法は保たない」——これが実現された full poly-isomorphism。 -/
theorem tlp_closes_m439_limitation :
    tlt2_full_poly_isomorphism_hypothesis tlpAdd0 tlpAdd1 (tlpLink (-1))
    ∧ (∀ y : tlpAdd1.carrier, ∃ x : tlpAdd0.carrier, (tlpLink (-1)).map x = y)
    ∧ (¬ ∃ f : RingHom tlpRing0 tlpRing1, ∀ x, f.map x = (tlpLink (-1)).map x)
    ∧ (¬ ∃ f : RingHom tlpRing0 tlpRing1, ∀ x, f.map x = tlpTransport.map x) :=
  ⟨tlp_link_neg_one_injective, tlp_link_neg_one_surjective,
    tlp_link_not_ring_hom (-1), tlp_transport_not_ring_hom⟩

/-! ## M444F-7: crux Dβ-ω は外部仮説（決して内部化しない） -/

/-- **crux（外部仮説・決して導出しない）**: theta-link の**多輻アルゴリズム
    不等式**（Dβ-ω、[IUTchIII] Cor 3.12 の係争ステップ＝ q-パイロットの体積が
    theta-パイロット軌道に支配されるという主張）は、本モジュールの主張には
    一切含めない。恒等 Iff で外部仮説として保持する（M439F
    tlt2_crux_is_hypothesis と同じ精神）。本モジュールが証明したのは
    「theta-link は群を繋ぎ環乗法を保たない」という poly-isomorphism の
    **構造的性質**までであり、不定性を体積不等式に変換する主張は別問題である。 -/
theorem tlp_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M444F-8: 正直な限定（M439F の残限定を閉じた上で残りを狭めて述べ直す） -/

/-- **定理 (M444F-8a): μ-方向は平面の外**（正直な限定の証人 1）— 環構造は
    値群×シクロトーム平面にのみ与えられ、μ-方向（単数系）ιι(0,1,0) は
    平面埋め込みの像に入らない。 -/
theorem tlp_mu_not_in_plane :
    ¬ ∃ x : tlpAdd0.carrier,
        tlpIncl0.map x = (tlt2InclGeom false).map ((0, 1, 0) : Int × Int × Int) := by
  intro h
  obtain ⟨x, hx⟩ := h
  have h1 : (0 : Int) = 1 :=
    congrArg (fun z : (tlt2Theater false).carrier => z.val.1.1.2.1) hx
  omega

/-- **定理 (M444F-8b): 劇場全体は非可換**（正直な限定の証人 2）— 劇場 †0 の
    群演算は可換でない（χ(1) = −1 が μ-方向を反転する M429F の証人の劇場版）
    ——ゆえに本環の可換加法は劇場**全体**には広がり得ず、平面上の環構造で
    あることは離散モデルの定理的帰結である。 -/
theorem tlp_theater_noncommutative :
    ¬ ∀ x y : (tlt2Theater false).carrier,
        (tlt2Theater false).mul x y = (tlt2Theater false).mul y x := by
  intro h
  have h1 : atpGroup.mul (atpSection.map 1)
        (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))
      = atpGroup.mul (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))
          (atpSection.map 1) :=
    congrArg Tlt2Elt.val
      (h ⟨atpSection.map 1⟩ ⟨atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int))⟩)
  exact atp_extension_not_central h1

/-- **定理 (M444F-8c): Frobenius 次数の平面 link は全射でない** —
    (1, 0) は tlpLink 2 の像にない（M439F 6b の環付き版・正直な限定）。 -/
theorem tlp_frobenius_not_surjective :
    ¬ ∃ x : tlpAdd0.carrier, (tlpLink 2).map x = (⟨(1, 0)⟩ : TlpElt true) := by
  intro h
  obtain ⟨x, hx⟩ := h
  have h1 : 2 * x.val.1 = 1 := congrArg (fun z : TlpElt true => z.val.1) hx
  omega

/-- **定理 (M444F-8d: tlp_model_scope・正直な限定の総括)** — 本構成のスコープ
    （M439F の残限定「環独立 full poly-isomorphism」を閉じた後に残る、より狭い
    正直な限定）:
    (i) 環構造は各劇場の値群×シクロトーム平面 ℤ² 上の具体乗法である——
        μ-方向は平面の像に入らない（8a）し、劇場全体は非可換なので本環の
        可換加法は劇場全体に広がり得ない（8b）。
    (ii) Frobenius 次数 j = 2 の平面 link は全射でない（8c）。
    実 IUT の環構造（数体・p 進局所体の正則構造）・Frobenioid **圏**レベルの
    full poly-isomorphism・log-link（柱C）との噛み合わせは外部/後続
    （tlp_full_theater_ring_hypothesis）。 -/
theorem tlp_model_scope :
    (¬ ∃ x : tlpAdd0.carrier,
        tlpIncl0.map x = (tlt2InclGeom false).map ((0, 1, 0) : Int × Int × Int))
    ∧ (¬ ∀ x y : (tlt2Theater false).carrier,
        (tlt2Theater false).mul x y = (tlt2Theater false).mul y x)
    ∧ (¬ ∃ x : tlpAdd0.carrier, (tlpLink 2).map x = (⟨(1, 0)⟩ : TlpElt true)) :=
  ⟨tlp_mu_not_in_plane, tlp_theater_noncommutative, tlp_frobenius_not_surjective⟩

/-- **外部仮説（正直な限定・決して導出しない）**: 平面環を**劇場全体**の実環構造
    （数体・p 進局所体の正則構造、Frobenioid 圏の対象）へ昇格させ、log-link
    （柱C）と噛み合わせること（M439F tlt2_independent_ring_hypothesis の
    狭め直し・後続）。 -/
def tlp_full_theater_ring_hypothesis (T : Grp) : Prop := Slim T

/-! ## M444F-9: capstone -/

/-- **M444F-9a: theta-link poly-isomorphism データ** — 独立環構造つき 2 劇場間の
    theta-link の全実構造を束ねる: 加法群準同型性・零保存・劇場 link との両立・
    シクロトーム剛性・値群スケール・交換子保存（劇場全体）・平面像の可換性・
    **単位の破れ＋環準同型の不在（M439F の残限定を閉じる本丸）**・標準輸送の
    環準同型の不在（環独立）・抽象環同型の存在（劇場は抽象的には同型のまま）・
    full poly-isomorphism 仮説の内部供給。主語はすべて本物の群・環演算
    （toy 主語なし）。crux Dβ-ω はフィールドに含めない（外部仮説のまま）。 -/
structure ThetaLinkPolyIsoData (j : Int) where
  /-- 平面 theta-link は加法群準同型（任意の j で on the nose）。 -/
  link_add_hom : ∀ x y : tlpAdd0.carrier,
    (tlpLink j).map (tlpRing0.add x y)
      = tlpRing1.add ((tlpLink j).map x) ((tlpLink j).map y)
  /-- 零（加法単位）の保存。 -/
  link_zero : (tlpLink j).map tlpRing0.zero = tlpRing1.zero
  /-- 劇場レベル theta-link（M439F tlt2Link）と埋め込みで両立。 -/
  theta_compat : ∀ x : tlpAdd0.carrier,
    (tlt2Link j).map (tlpIncl0.map x) = tlpIncl1.map ((tlpLink j).map x)
  /-- シクロトーム剛性: シクロトーム座標は j 倍にしか動かない。 -/
  cyclotome_rigid : ∀ c : Int,
    (tlpLink j).map ⟨(0, c)⟩ = (⟨(0, j * c)⟩ : TlpElt true)
  /-- 値群スケール: 値群座標も同一因子 j 倍（剛性の同期）。 -/
  value_scaled : ∀ a : Int,
    (tlpLink j).map ⟨(a, 0)⟩ = (⟨(j * a, 0)⟩ : TlpElt true)
  /-- 交換子構造の劇場間保存（劇場全体・M439F の再輸出）。 -/
  commutator_preserved : ∀ x y : (tlt2Theater false).carrier,
    (tlt2Link j).map ((tlt2Theater false).comm x y)
      = (tlt2Theater true).comm ((tlt2Link j).map x) ((tlt2Link j).map y)
  /-- 平面像は劇場の可換部分群（環の加法群の劇場内実現）。 -/
  embedded_commute : ∀ x y : tlpAdd0.carrier,
    (tlt2Theater false).mul (tlpIncl0.map x) (tlpIncl0.map y)
      = (tlt2Theater false).mul (tlpIncl0.map y) (tlpIncl0.map x)
  /-- **単位の破れ**: link は環の乗法単位を保たない（任意の j）。 -/
  unit_broken : (tlpLink j).map tlpRing0.one ≠ tlpRing1.one
  /-- **環準同型の不在（本丸）**: link の写像を台とする環準同型は存在しない。 -/
  not_ring_hom : ¬ ∃ f : RingHom tlpRing0 tlpRing1,
    ∀ x, f.map x = (tlpLink j).map x
  /-- 標準輸送（val 恒等の群同型）も環準同型でない（環構造の独立性）。 -/
  transport_not_ring_hom : ¬ ∃ f : RingHom tlpRing0 tlpRing1,
    ∀ x, f.map x = tlpTransport.map x
  /-- 2 劇場の環は抽象的には同型（非自明な符号反転・単射かつ全射）。 -/
  ring_iso_exists : ∃ f : RingHom tlpRing0 tlpRing1,
    (∀ x y, f.map x = f.map y → x = y) ∧ (∀ y, ∃ x, f.map x = y)
  /-- M439F の full poly-isomorphism 外部仮説の内部供給（j = −1 の群同型）。 -/
  full_poly : tlt2_full_poly_isomorphism_hypothesis tlpAdd0 tlpAdd1 (tlpLink (-1))

/-- **M444F-9b: witness 本体** — 全フィールドを M444F-1〜6 の本物の証明で埋める
    （crux 以外の外部仮説ゼロ・完全証明）。 -/
def thetaLinkPolyIsoData (j : Int) : ThetaLinkPolyIsoData j where
  link_add_hom := tlp_link_add_hom j
  link_zero := tlp_link_zero j
  theta_compat := tlp_link_compat j
  cyclotome_rigid := tlp_cyclotome_rigid j
  value_scaled := tlp_value_scaled j
  commutator_preserved := tlt2_commutator_preserved j
  embedded_commute := tlp_embedded_commute
  unit_broken := tlp_link_unit_broken j
  not_ring_hom := tlp_link_not_ring_hom j
  transport_not_ring_hom := tlp_transport_not_ring_hom
  ring_iso_exists := ⟨tlpRingIso, tlp_ring_iso_bijective.1, tlp_ring_iso_bijective.2⟩
  full_poly := tlp_link_neg_one_injective

/-- **定理 (M444F-9c): theta-link poly-isomorphism データの存在（M444F 見出し・
    capstone）** — 任意の Frobenius 次数 j ∈ ℤ に対し、独立な環構造を持つ
    2 ホッジ劇場の間の theta-link と、その加法群準同型性・劇場 link との両立・
    **環準同型の不在（M439F の残限定「環独立 full poly-isomorphism」を閉じる）**・
    抽象環同型の存在・正直な限定を束ねたデータが**crux 以外の外部仮説なしで**
    存在する。 -/
theorem tlp_exists (j : Int) : Nonempty (ThetaLinkPolyIsoData j) :=
  ⟨thetaLinkPolyIsoData j⟩

/-! ## M444F-10: 実例 -/

/-- 実例（Frobenius 次数 j = 2 の環乗法の破れ・具体計算）: link((1,1)·(1,1)) =
    (2,2) だが link(1,1)·link(1,1) = (4,−4) ——環乗法は保たれない。 -/
example :
    (tlpLink 2).map (tlpRing0.mul ⟨(1, 1)⟩ ⟨(1, 1)⟩) = (⟨(2, 2)⟩ : TlpElt true)
    ∧ tlpRing1.mul ((tlpLink 2).map ⟨(1, 1)⟩) ((tlpLink 2).map ⟨(1, 1)⟩)
        = (⟨(4, -4)⟩ : TlpElt true)
    ∧ ((⟨(2, 2)⟩ : TlpElt true) ≠ (⟨(4, -4)⟩ : TlpElt true)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine tlp_ext (tlp_pair_ext ?_ ?_)
    · show (2 : Int) * (1 * 1) = 2
      omega
    · show (2 : Int) * (1 * 1) = 2
      omega
  · refine tlp_ext (tlp_pair_ext ?_ ?_)
    · show ((2 : Int) * 1) * (2 * 1) = 4
      omega
    · show -(((2 : Int) * 1) * (2 * 1)) = -4
      omega
  · intro h
    have h1 : (2 : Int) = 4 := congrArg (fun z : TlpElt true => z.val.1) h
    omega

/-- 実例: シクロトーム剛性の具体形 — (0, 7) は j = 5 の平面 link で (0, 35) へ。 -/
example : (tlpLink 5).map ⟨(0, 7)⟩ = (⟨(0, 35)⟩ : TlpElt true) := by
  refine tlp_ext (tlp_pair_ext ?_ ?_)
  · show (5 : Int) * 0 = 0
    omega
  · show (5 : Int) * 7 = 35
    omega

/-- 実例: j = −1 の平面 link は本物の加法群同型（往復恒等・全射）だが、
    それでも環準同型ではない（poly-isomorphism の実感）。 -/
example :
    (∀ x : tlpAdd0.carrier, (tlpLinkRev (-1)).map ((tlpLink (-1)).map x) = x)
    ∧ (¬ ∃ f : RingHom tlpRing0 tlpRing1,
        ∀ x, f.map x = (tlpLink (-1)).map x) :=
  ⟨tlp_neg_one_roundtrip, tlp_link_not_ring_hom (-1)⟩

/-- 実例: 2 劇場の環単位は相異なる座標を持つ（独立に定められた別環の実感）。 -/
example : tlpRing0.one.val = ((1 : Int), (1 : Int))
    ∧ tlpRing1.one.val = ((1 : Int), (-1 : Int)) :=
  ⟨rfl, rfl⟩

/-- 実例: theta-link poly-isomorphism データは任意の Frobenius 次数で存在
    （capstone の具体化）。 -/
example : Nonempty (ThetaLinkPolyIsoData 2) := tlp_exists 2

end IUT
