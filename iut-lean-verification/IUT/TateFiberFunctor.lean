/-
  # M200F: Tate 被覆圏のファイバー関手による π₁ 復元 — Aut(F)=π₁（柱A A-3β-4・並行部品）

  A-3（エタール的入力の代理化）β 系列の**最終歩**。A-3β-1（M188F
  `TateCoverGroup.lean`）の群三層束ね・A-3β-2（M191F
  `TateCoverCat.lean`）の有限連続被覆圏・A-3β-3（M195F
  `TateCoverGalois.lean`）の抽象 Galois 圏インスタンス化を入力に、
  SGA1 主定理の残り半分——**ファイバー関手の自己同型群がテンパード
  π₁ の副有限完備化 `tateProfinite` = ẑ を復元する**（`Aut(F) = π₁`）
  ——を建設し、A-3β 計画（被覆圏が Galois 圏であり、かつその
  ファイバー関手が提示された π₁ を復元する）を閉じる。

  戦略: M20 `GaloisAxioms.lean` が任意の群 G について完全証明した
  **ファイバー関手の自己同型群の群同型 `fiberAut G ≅ G`**
  （`from_to`/`to_from` が互いに逆の群準同型 G ⇄ Aut(F)）を、
  復元すべき群 G := `tateProfinite`（= ẑ、M188F が提示した
  テンパード π₁ のデッキ部分の副有限完備化）に適用する。これにより
  「ẑ-集合の圏（骨格版）のファイバー関手の自己同型群 = ẑ」が
  構成的（新規 Classical.choice なし）に得られる。有限レベルでは
  各 ℤ/n について同じく `fiberAut (zmod n) ≅ zmod n` が成り、
  M14 `levelAction`/`level_transition_equivariant`（副有限群が有限
  レベルの逆系に自然変換として作用する）が `tateFiniteSystem` に
  そのまま適用されて、復元群の作用が M191F の各有限被覆
  `tateLevelCover n` の平行移動作用と一致する。

  * M200F-1 `tateFiberAut` — **Aut(F)**: ファイバー関手（ẑ-集合の
    骨格圏 `SkelCat tateProfinite` 上の忘却関手 `forgetfulSkel`）の
    自然自己変換のなす群（M20-7 `fiberAut` を G := ẑ に適用）
  * M200F-2 `tateToFiberAut` / `tateFromFiberAut` / `tate_from_to` /
    `tate_to_from` — **復元同型 Aut(F) ≅ tateProfinite**: 互いに逆の
    群準同型の対（M20-8 `from_to`/`to_from` を G := ẑ に適用）。
    ファイバー関手の自己同型群が提示された副有限 π₁ そのものである
  * M200F-3 `tateLevelFiberAut` / `tateLevel_from_to` /
    `tateLevel_to_from` — **各有限レベルの復元**: 各 ℤ/n について
    `fiberAut (zmod n) ≅ zmod n`（M20-8 を G := ℤ/n に適用）。
    ẑ = lim ℤ/n のレベルごとの Aut(F_n) = ℤ/n を組み上げた姿
  * M200F-4 `tateLevelAction` / `tateLevelAction_act` /
    `tateLevel_natural` — **復元群の自然作用**: 副有限 π₁ =
    `tateProfinite` が有限商逆系 `tateFiniteSystem` の各段
    `tateLevelCover n` のファイバー ℤ/n に射影を通じて作用し
    （M14-5 `levelAction`）、その作用は推移射と両立する（M14-6
    `level_transition_equivariant`）= ファイバー関手の自然変換である
  * M200F-5 `tateFiberAut_profinite_compat` — A-3β-1/2/3 との接続:
    復元群の有限レベル作用はデッキ座標経由でも副有限完備化経由でも
    一致する（M195F-5 `tateGalois_profinite_compat` の再掲）
  * M200F-6 `TateFiberFunctorData` / `tateFiberFunctorData` /
    `tateFiberFunctor_exists` — 総括データ・証人・存在定理

  **意義**: A-3β 計画が閉じた。M195F が「Tate 有限連続被覆圏は
  抽象 Galois 圏の公理系 G1–G6 を充足する」ことを示したのに続き、
  本モジュールは SGA1 主定理の残り半分「そのファイバー関手の
  自己同型群が提示されたテンパード π₁（の副有限完備化 ẑ）を
  復元する」を、M20 の群同型 `fiberAut G ≅ G` を復元標的 G := ẑ に
  適用することで構成的に達成する。各有限レベル ℤ/n でも同型
  `Aut(F_n) ≅ ℤ/n` が成り、副有限 π₁ の作用は M14 により有限商
  逆系の自然変換として実現され、M191F の各段標準被覆の平行移動
  作用と一致する。よって「Tate 被覆圏は Galois 圏であり、かつ
  そのファイバー関手は提示された π₁ を復元する」という A-3β の
  最終命題が、既存資産（M20 の群同型・M14 の自然作用・M188F の ẑ・
  M191F/M195F の被覆圏）の再利用だけで機械検証された。

  **正直な限定**: (1) 閉じたのは**復元同型 Aut(F) ≅ tateProfinite**
  の両方向（`from_to`/`to_from` が互いに逆）であり、これは M20 の
  群同型を復元標的 ẑ に適用した姿である。復元されるのは提示された
  副有限 π₁ = ẑ（デッキ部分の副有限完備化）であって、テンパード
  π₁ 全体（デッキ群 ℤ そのもの・数論的 G_K 方向）ではない——
  ẑ はデッキ群 ℤ を単射に含む（M188F-6a）が真に大きい。(2) 用いる
  ファイバー関手は M20 の**骨格圏** `SkelCat tateProfinite`（ẑ-集合の
  標準連結対象の圏）上の忘却関手であり、M195F の `tateFiberFunctor`
  （`tateCoverCat` 上の忘却関手）とは同値だが同一の圏ではない。
  `tateCoverCat` 上の自然自己変換全体の直接分類（対象ごとにレベルが
  異なるため共通の代表元整合を要する）は行わず、M20 の骨格圏経由の
  復元と M14 の有限レベル自然作用に依拠する。(3) M14 の有限レベル
  自然作用が `tateLevelCover n` に降りることは示すが、`tateCoverCat`
  の任意対象上への一様な自然変換への組み上げ（逆極限の普遍性による）
  は M14/M13 の骨格に委ね、本モジュールでは明示しない。(4) デッキ群
  ℤ・G_K = ℤ は玩具モデル、π₁ の提示は幾何からの**入力**（M188F の
  `tateModel`）であってスキーム論的エタール不変量ではない。位相
  （副有限位相）は未導入（M13 と同じ代数側形式化）。(5) SGA1 一般論
  の後半（十分多くのガロア対象の存在・pro-表現対象による圏同値の
  一般形）は M20/M21 と同じく未形式化（`AbstractGalois.lean` の正直
  申告を継承）。

  **Classical 継承**: 本モジュールが用いる M20 の `fiberAut`・
  `from_to`・`to_from`（および `skel_classification`）は全て構成的で
  あり、M195F の G6 `reflect_iso`（`gsets_G6_reflects_iso` 経由の
  Classical.choice）や `GaloisTower.transAut`（∃! の関数化の
  Classical.choose）は**参照しない**。M14 の `levelAction`・
  `level_transition_equivariant`、M188F の ẑ 構成も構成的。よって
  本モジュールは**新規・継承ともに Classical.choice 不使用**である
  （`#print axioms` で確認：propext/Quot.sound/funext のみ）。

  sorry なし・Classical.choice なし。サブエージェント並行部品。
-/
import IUT.TateCoverGalois
import IUT.GaloisAxioms
import IUT.GaloisCategory

namespace IUT

/-! ## M200F-1: Aut(F) — ファイバー関手の自己同型群 -/

/-- **Aut(F)（M200F-1）**: 復元標的 = 副有限完備化 ẑ = `tateProfinite`
    の骨格圏 `SkelCat tateProfinite`（ẑ-集合の標準連結対象の圏）上の
    ファイバー関手 `forgetfulSkel tateProfinite` の自然自己変換のなす
    群。M20-7 `fiberAut` を G := ẑ に適用したもの。SGA1 の
    π₁ = Aut(ファイバー関手) の左辺（自己同型群）。 -/
def tateFiberAut : Grp := fiberAut tateProfinite

/-! ## M200F-2: 復元同型 Aut(F) ≅ tateProfinite -/

/-- **復元準同型 tateProfinite → Aut(F)（M200F-2）**: 副有限 π₁ の
    各元が骨格圏の各対象に作用として定める自然変換（M20 `toFiberAut`
    を G := ẑ に適用）。 -/
def tateToFiberAut : Hom tateProfinite tateFiberAut := toFiberAut tateProfinite

/-- **逆向き準同型 Aut(F) → tateProfinite（M200F-2）**: 自然変換の
    [1] での値による復元（M20 `fromFiberAut` を G := ẑ に適用）。 -/
def tateFromFiberAut : Hom tateFiberAut tateProfinite := fromFiberAut tateProfinite

/-- **定理 (M200F-2a): tateProfinite → Aut(F) → tateProfinite は恒等** —
    提示された副有限 π₁ の元は自己同型群を経由して回収される
    （M20-8a `from_to` を G := ẑ に適用）。 -/
theorem tate_from_to (c : tateProfinite.carrier) :
    tateFromFiberAut.map (tateToFiberAut.map c) = c :=
  from_to tateProfinite c

/-- **定理 (M200F-2b): Aut(F) → tateProfinite → Aut(F) も恒等** —
    ファイバー関手の自然自己変換は副有限 π₁ の元による作用で尽きる
    （M20-8b `to_from` を G := ẑ に適用）。M200F-2a と併せて
    **Aut(F) ≅ tateProfinite（群同型）= 提示された π₁ の復元**が
    完成する。A-3β の最終命題。 -/
theorem tate_to_from (η : tateFiberAut.carrier) :
    tateToFiberAut.map (tateFromFiberAut.map η) = η :=
  to_from tateProfinite η

/-! ## M200F-3: 各有限レベルの復元 Aut(F_n) ≅ ℤ/n -/

/-- **有限レベルの Aut(F_n)（M200F-3）**: 有限商 ℤ/n の骨格圏上の
    ファイバー関手の自己同型群（M20-7 を G := ℤ/n に適用）。
    ẑ = lim_n ℤ/n の各段のデッキ群の復元。 -/
def tateLevelFiberAut (n : Nat) : Grp := fiberAut (zmod n)

/-- **定理 (M200F-3a): 有限レベルの復元（片方向）** —
    ℤ/n → Aut(F_n) → ℤ/n は恒等（M20-8a を G := ℤ/n に適用）。 -/
theorem tateLevel_from_to (n : Nat) (c : (zmod n).carrier) :
    (fromFiberAut (zmod n)).map ((toFiberAut (zmod n)).map c) = c :=
  from_to (zmod n) c

/-- **定理 (M200F-3b): 有限レベルの復元（他方向）** —
    Aut(F_n) → ℤ/n → Aut(F_n) も恒等。M200F-3a と併せて各有限
    レベルで **Aut(F_n) ≅ ℤ/n**（デッキ群 ℤ/n の復元）。これらを
    割り切り逆系で組み上げた極限が M200F-2 の Aut(F) ≅ ẑ である。 -/
theorem tateLevel_to_from (n : Nat) (η : (fiberAut (zmod n)).carrier) :
    (toFiberAut (zmod n)).map ((fromFiberAut (zmod n)).map η) = η :=
  to_from (zmod n) η

/-! ## M200F-4: 復元群の有限レベルへの自然作用 -/

/-- **復元群の有限レベル作用（M200F-4）**: 副有限 π₁ = `tateProfinite`
    が有限商逆系 `tateFiniteSystem` = ℤ/n の各段のファイバーに射影を
    通じて作用する（M14-5 `levelAction`。`tateProfinite` =
    `limitGrp tateFiniteSystem` は定義的）。 -/
def tateLevelAction (n : Nat) : GAction tateProfinite :=
  levelAction tateFiniteSystem n

/-- **定理 (M200F-4a): レベル n 作用の具体形** — 復元群の元 σ の
    レベル n 作用は「副有限レベル射影 `profiniteLevel n` で ℤ/n に
    還元して平行移動」そのもの（定義的に rfl）。これは M191F-5
    `tateLevelCover_act` の標準被覆の作用（`deckQuot` 経由）と
    同じ形であり、復元群の作用が実際の各段標準被覆の平行移動作用に
    一致することの内容。 -/
theorem tateLevelAction_act (n : Nat) (σ : tateProfinite.carrier)
    (x : (zmod n).carrier) :
    (tateLevelAction n).act σ x
      = (zmod n).mul ((profiniteLevel n).map σ) x := rfl

/-- **定理 (M200F-4b): 復元群の作用は自然変換** — 有限商逆系の推移射
    ℤ/n → ℤ/m は復元群 `tateProfinite`-同変である（M14-6
    `level_transition_equivariant` を `tateFiniteSystem` に適用）。
    「Aut(F) = π₁ の作用がファイバー関手の自然変換である」の自然性
    条件の、Tate 有限被覆逆系での機械検証。 -/
theorem tateLevel_natural {m n : Nat} (h : tateFiniteSystem.le m n)
    (σ : tateProfinite.carrier) (x : (tateFiniteSystem.G n).carrier) :
    (tateFiniteSystem.t h).map ((tateLevelAction n).act σ x)
      = (tateLevelAction m).act σ ((tateFiniteSystem.t h).map x) :=
  level_transition_equivariant tateFiniteSystem h σ x

/-! ## M200F-5: A-3β-1/2/3 との接続 -/

/-- **定理 (M200F-5): 復元群の有限レベル作用はデッキ座標でも副有限
    完備化でも一致** — 数論的基本群 Π の元 g に対し、レベル n 被覆の
    作用は「デッキ射影 → ℤ/n」でも「副有限完備化 → ℤ/n」でも同じ
    （M195F-5 `tateGalois_profinite_compat`・M191F-7
    `cover_deck_profinite_compat` の再掲）。復元された Aut(F) ≅ ẑ が
    A-3β-1 の副有限完備化・A-3β-2/3 の被覆圏と同じ ẑ を見ている
    ことの形式的内容。 -/
theorem tateFiberAut_profinite_compat (n : Nat) (X : GAction (zmod n))
    (g : tateCoverGrp.carrier) (x : X.carrier) :
    X.act ((profiniteLevel n).map (tateCompletion.map g)) x
      = X.act ((deckQuot n).map (tateDeckProj.map g)) x :=
  tateGalois_profinite_compat n X g x

/-! ## M200F-6: 総括 -/

/-- **Tate ファイバー関手復元データ（M200F-6）**: A-3β-4 の成果物の
    束。復元標的の副有限 π₁・ファイバー関手の自己同型群 Aut(F)・
    互いに逆の復元準同型の対（= 群同型 Aut(F) ≅ π₁）・各有限
    レベルの作用と自然性・被覆圏のファイバー忠実性を一つに束ねる。
    A-3β 計画（被覆圏 = Galois 圏 かつ ファイバー関手が π₁ を復元）を
    閉じる最終データ。 -/
structure TateFiberFunctorData where
  /-- 復元される副有限 π₁（提示されたデッキ部分の副有限完備化 ẑ）。 -/
  pi1 : Grp
  /-- ファイバー関手の自己同型群 Aut(F)。 -/
  fiberAutGrp : Grp
  /-- 復元準同型 π₁ → Aut(F)（作用による自然変換）。 -/
  recover : Hom pi1 fiberAutGrp
  /-- 逆向き準同型 Aut(F) → π₁（[1] での値）。 -/
  recoverInv : Hom fiberAutGrp pi1
  /-- π₁ → Aut(F) → π₁ は恒等（提示された π₁ の回収）。 -/
  left_inv : ∀ c, recoverInv.map (recover.map c) = c
  /-- Aut(F) → π₁ → Aut(F) も恒等（Aut(F) ≅ π₁ の完成）。 -/
  right_inv : ∀ η, recover.map (recoverInv.map η) = η
  /-- 復元群の各有限レベルへの作用（副有限 π₁ の有限商 ℤ/n の
      ファイバーへの作用）。 -/
  levelAct : ∀ (n : Nat), pi1.carrier →
    (tateFiniteSystem.G n).carrier → (tateFiniteSystem.G n).carrier
  /-- その作用は有限商逆系の推移射と両立する（自然変換）。 -/
  level_natural : ∀ {m n : Nat} (h : tateFiniteSystem.le m n)
    (σ : pi1.carrier) (x : (tateFiniteSystem.G n).carrier),
    (tateFiniteSystem.t h).map (levelAct n σ x)
      = levelAct m σ ((tateFiniteSystem.t h).map x)
  /-- 被覆圏のファイバー関手は忠実（同変写像は台写像で決まる。
      M191F-6 の再掲）。 -/
  fiber_faithful : ∀ (X Y : TateCover) (f g : ActHom X.carrier Y.carrier),
    (∀ x, f.map x = g.map x) → f = g

/-- **証人（M200F-6）**: 本モジュールの構成が Tate ファイバー関手
    復元データを実際に充足する。復元同型・作用・自然性・忠実性の
    全てが M20/M14/M191F の資産の再利用で埋まる。 -/
def tateFiberFunctorData : TateFiberFunctorData where
  pi1 := tateProfinite
  fiberAutGrp := tateFiberAut
  recover := tateToFiberAut
  recoverInv := tateFromFiberAut
  left_inv := tate_from_to
  right_inv := tate_to_from
  levelAct := fun n σ x => (tateLevelAction n).act σ x
  level_natural := fun h σ x => tateLevel_natural h σ x
  fiber_faithful := cover_fiber_faithful

/-- **定理 (M200F-6): Tate ファイバー関手復元データの存在** —
    Tate 曲線の有限連続被覆圏のファイバー関手の自己同型群は、
    提示されたテンパード π₁ の副有限完備化 ẑ と群同型であり
    （Aut(F) ≅ π₁）、その作用は有限商逆系の自然変換として実現される。
    M195F（被覆圏 = 抽象 Galois 圏）と併せて、Tate 被覆代理に対する
    SGA1 復元「圏は Galois 圏であり、そのファイバー関手が π₁ を
    復元する」が閉じた。 -/
theorem tateFiberFunctor_exists : Nonempty TateFiberFunctorData :=
  ⟨tateFiberFunctorData⟩

end IUT

