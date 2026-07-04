/-
  # M217F: Galois 圏同値への到達（SGA1 主定理完成）（柱A A-3α 最終・並行部品）

  M213F は「基本関手 F はガロア塔で対象ごとに pro-表現される」
  （colimEval : colim_n Hom(A_n, X) ≅ F(X)）を完成した。本モジュールは
  その残余 A-3α 最終段 — pro-表現から **圏同値 C ≃ π₁-Set の骨格**への
  組み立て — を行う。核心は「π₁（= pi1Tower、M24 の塔逆極限）が
  余極限 colim_n Hom(A_n, X) に作用し、X ↦ colim_n Hom(A_n, X) が
  **比較関手 C → pi1Tower-Set** をなす」ことの構成と、その忠実性
  （M21-4 + M213F 支配）・対象ごとの全単射性（M213F-6）・本質的全射性
  のレベル橋（M161F/M186F）の束ねである:

  * M217F-1 `pi1Component` / `pi1Component_compat` /
    `pi1Component_one` / `pi1Component_mul` — **π₁ 元のレベル成分**:
    pi1Tower = limitGrp(塔) の元 σ の第 n 成分 σ_n ∈ Aut(A_n) と、
    その整合性（transAut hσ_j = σ_i）・単位・積の成分計算（後二者は
    定義的等式 rfl）
  * M217F-2 `pi1Component_exchange` — **モノドロミー交換律**:
    P_{ij} ∘ σ_i = σ_j ∘ P_{ij}（M24-1 の遷移仕様 transAut_spec の
    整合族への翻訳）。π₁ 作用の well-definedness の全てを支える
  * M217F-3 `germAct` / `germAct_rel` — **π₁ のレベル射への作用**:
    σ·(n, u) = (n, σ_n；u)（前合成）。交換律により芽関係
    （germRel、M213F-2b）を保つ
  * M217F-4 `colimHomAction` — **colim_n Hom(A_n, X) の
    pi1Tower-集合構造**: 商 Quot 上に作用が降り、act_one / act_mul は
    圏法則から従う。「F(X) への π₁ 作用」の pro-対象側の実体
  * M217F-5 `pushLevel` / `pushLevel_rel` / `colimPushHom` —
    **関手性**: f : X → Y の後合成はレベル射・芽を保ち、π₁ 作用と
    可換（同変写像 colim Hom(A_n,X) → colim Hom(A_n,Y)）
  * M217F-6 `towerComparison` — **比較関手 C → pi1Tower-Set**:
    X ↦ (colim_n Hom(A_n, X), π₁ 作用)、f ↦ 後合成。SGA1 主定理の
    同値関手の候補そのもの（塔・pro-対象語彙での実構成）
  * M217F-7 `levelInclusion` / `levelInclusion_eval` /
    `levelInclusion_injective` — レベル埋め込み Hom(A_n, X) →
    colim_n Hom(A_n, X) とその単射性（塔の各層の連結性 + M21-6）
  * M217F-8 `colimEval_natural` — **比較写像の自然性**: colimEval は
    towerComparison の台集合関手から F への自然変換をなす
    （colimEval ∘ (f 後合成) = F(f) ∘ colimEval）。M213F-6 の
    対象ごとの全単射と併せ「F ≅ colim Hom(A_n, −)」の関手版
  * M217F-9 `towerComparison_faithful` — **忠実性**: 塔が X を支配
    すれば、比較関手は Hom(X, Y) 上単射（M213F-5a の支配で F(X) の
    各点をレベル射で覆い、M21-4 fiber_faithful へ帰着）
  * M217F-10 `towerComparison_proRep` — 対象ごとの pro-表現
    （M213F-6）の比較関手語彙での再輸出: 支配対象 X 上で
    towerComparison の台集合は colimEval により F(X) と全単射
  * M217F-11 `towerComparison_faithful_of_domination` /
    `towerComparison_faithful_model` — **忠実性の無条件化**: 抽象
    支配データ（M189F-8）を持つ D の任意の連結 X / モデル
    `gsetGaloisData G` の任意の抽象連結 E に対し、比較関手が X 上
    忠実になる塔（定値塔 / 閉包塔）が存在する
  * M217F-12 `tower_level_ess_surj` / `tower_level_ess_surj_finite`
    — **本質的全射性のレベル橋**: 塔の各層 A_n はガロアなので、
    M161F-4（推移的 Aut(A_n)-集合の実現）と M186F-6（有限和版）が
    そのまま塔語彙で適用できる — 同値の「全射側」は各レベルで成立
  * M217F-13 `GaloisEquivalenceData` / `galoisEquivalenceWitness` /
    `galoisEquivalence_exists` / `galoisEquivalence_exists_trivial` —
    総括データ（塔・比較関手・比較写像・忠実性・単射性・支配下の
    全射性）・任意の (D, 塔) に対する証人・ガロア対象を持つ任意の
    D とモデルでの存在定理

  **意義**: A-3α 最終 — M213F の対象ごとの pro-表現（colimEval 全単射）
  と M24 の π₁ = pi1Tower（塔逆極限）が初めて**関手として**接続された。
  SGA1 主定理 C ≃ π₁-Set の同値関手の候補 towerComparison :
  C → pi1Tower-Set が実構成され、その (i) π₁ 作用の well-definedness
  （モノドロミー交換律）、(ii) 自然性（colimEval : 比較 ⟹ F）、
  (iii) 忠実性（支配対象上、M21-4 経由）、(iv) 対象ごとの全単射性
  （M213F-6）、(v) 本質的全射性のレベル供給（M161F/M186F の橋）が
  全て証明された。M20-9 の圏同値（モデル版 G-Set ≃ Aut(F)-Set）の
  抽象・pro-対象版に向けた「2/3 + α」の骨格である。

  **正直な限定**: (1) 本モジュールはスライス A+B（比較関手の実構成 +
  忠実性 + 自然性 + 対象ごとの全単射性 + 本質的全射性のレベル橋）で
  ある。**充満性**（Hom(X,Y) → Hom_{π₁-Set} の全射性）と、真の圏同値
  （擬逆関手・単位・余単位の構成 = 2-out-of-3 の束ね）は未達成 —
  充満性は colimEval の全単射性を X と Y の両方で使い π₁-同変写像から
  射を再構成する段で、F(X) 上の π₁ 作用（colimEval による輸送 =
  全単射の逆写像抽出、choice を要する）を要する。(2) 忠実性・全射性は
  **塔が対象を支配する**（DominatesFiber、M213F-5a）場合に限る。単一の
  塔が圏の全対象を同時に支配する真の共終塔は M213F と同じく未達成
  （Nat 添字の限界）。(3) 本質的全射性は各レベル A_n の
  Aut(A_n)-集合の実現（M161F/M186F の再適用）であり、pi1Tower-集合
  （連続 π₁ 作用）としての実現 — レベル作用の引き戻しとの整合 — は
  範囲外。(4) 公理フットプリント（`#print axioms` 実測）: π₁ に触れる
  部（M217F-1〜6・9・10・11・13）は M24 `transAut`（∃! からの関数化）
  由来の Classical.choice を**継承**する（pi1Tower の定義自体が
  noncomputable なため不可避。M217F-11 のモデル版と M217F-13 の存在
  定理はさらに `gsetGaloisData` の G6 由来の choice も型経由で継承、
  M213F-10/11 と同じ事情）。π₁ に触れない部（M217F-5a/5b/5c 後合成・
  M217F-7 レベル埋め込み・M217F-8 自然性・M217F-12 レベル橋）は
  Quot.sound（+ propext）のみで choice 継承ゼロ、特に
  `levelInclusion_injective` は公理ゼロ。本モジュールの証明体での
  新規 choice 使用はゼロ。

  全て選択公理の新規使用なし（M24/M21-8 からの継承を除く）。
  サブエージェント並行部品。
-/
import IUT.ProRepresentable
import IUT.AbstractEssSurjSum

namespace IUT

universe u

namespace GaloisTower

variable {D : GaloisCatData.{u, 0}} (T : GaloisTower D)

/-! ## M217F-1: π₁ 元のレベル成分 -/

/-- **π₁ 元のレベル成分（M217F-1a）**: pi1Tower = limitGrp(塔逆系) の
    元 σ（整合族）の第 n 成分 σ_n ∈ Aut(A_n)。 -/
noncomputable def pi1Component (σ : T.pi1Tower.carrier) (n : Nat) :
    CatIso D.C (T.A n) (T.A n) :=
  σ.val n

/-- **成分の整合性（M217F-1b）**: i ≤ j のとき遷移 transAut は
    σ_j を σ_i へ送る（整合族の定義そのもの）。 -/
theorem pi1Component_compat (σ : T.pi1Tower.carrier) {i j : Nat}
    (h : i ≤ j) :
    T.transAut h (T.pi1Component σ j) = T.pi1Component σ i :=
  σ.property h

/-- **単位元の成分（M217F-1c）**: 単位整合族の各成分は恒等同型
    （定義的等式）。 -/
theorem pi1Component_one (n : Nat) :
    T.pi1Component T.pi1Tower.one n = (D.autGrp (T.A n)).one := rfl

/-- **積の成分（M217F-1d）**: 積の成分は成分の積（定義的等式）。 -/
theorem pi1Component_mul (σ τ : T.pi1Tower.carrier) (n : Nat) :
    T.pi1Component (T.pi1Tower.mul σ τ) n
      = (D.autGrp (T.A n)).mul (T.pi1Component σ n) (T.pi1Component τ n) :=
  rfl

/-! ## M217F-2: モノドロミー交換律 -/

/-- **交換律（M217F-2）**: i ≤ j のとき P_{ij}；σ_i = σ_j；P_{ij}
    （遷移射は整合族の成分と交換する）。M24-1 の遷移仕様
    `transAut_spec` の整合族への翻訳であり、π₁ 作用の
    well-definedness（M217F-3）の全てを支える。 -/
theorem pi1Component_exchange (σ : T.pi1Tower.carrier) {i j : Nat}
    (h : i ≤ j) :
    D.C.comp (T.P h) (T.pi1Component σ i).hom
      = D.C.comp (T.pi1Component σ j).hom (T.P h) := by
  rw [← T.pi1Component_compat σ h]
  exact T.transAut_spec h (T.pi1Component σ j)

/-! ## M217F-3: π₁ のレベル射への作用 -/

/-- **レベル射への作用（M217F-3a）**: σ·(n, u) = (n, σ_n；u)
    （第 n 成分の前合成）。 -/
noncomputable def germAct (X : D.C.Obj) (σ : T.pi1Tower.carrier)
    (p : LevelHom T X) : LevelHom T X :=
  ⟨p.lvl, D.C.comp (T.pi1Component σ p.lvl).hom p.hom⟩

/-- **作用は芽関係を保つ（M217F-3b）**: 共通レベル k で一致する二つの
    レベル射は、作用後も k で一致する（交換律 M217F-2 で σ_k を
    くくり出す）。 -/
theorem germAct_rel (X : D.C.Obj) (σ : T.pi1Tower.carrier)
    (p q : LevelHom T X) (h : T.germRel X p q) :
    T.germRel X (T.germAct X σ p) (T.germAct X σ q) := by
  obtain ⟨k, hp, hq, heq⟩ := h
  refine ⟨k, hp, hq, ?_⟩
  show D.C.comp (T.P hp) (D.C.comp (T.pi1Component σ p.lvl).hom p.hom)
      = D.C.comp (T.P hq) (D.C.comp (T.pi1Component σ q.lvl).hom q.hom)
  calc D.C.comp (T.P hp) (D.C.comp (T.pi1Component σ p.lvl).hom p.hom)
      = D.C.comp (D.C.comp (T.P hp) (T.pi1Component σ p.lvl).hom) p.hom :=
        (D.C.assoc _ _ _).symm
    _ = D.C.comp (D.C.comp (T.pi1Component σ k).hom (T.P hp)) p.hom := by
        rw [T.pi1Component_exchange σ hp]
    _ = D.C.comp (T.pi1Component σ k).hom (D.C.comp (T.P hp) p.hom) :=
        D.C.assoc _ _ _
    _ = D.C.comp (T.pi1Component σ k).hom (D.C.comp (T.P hq) q.hom) := by
        rw [heq]
    _ = D.C.comp (D.C.comp (T.pi1Component σ k).hom (T.P hq)) q.hom :=
        (D.C.assoc _ _ _).symm
    _ = D.C.comp (D.C.comp (T.P hq) (T.pi1Component σ q.lvl).hom) q.hom := by
        rw [T.pi1Component_exchange σ hq]
    _ = D.C.comp (T.P hq) (D.C.comp (T.pi1Component σ q.lvl).hom q.hom) :=
        D.C.assoc _ _ _

/-! ## M217F-4: colim_n Hom(A_n, X) の pi1Tower-集合構造 -/

/-- **余極限への作用写像（M217F-4a）**: M217F-3 により σ の作用は
    Quot に降りる（Quot.lift、choice 不要）。 -/
noncomputable def colimAct (X : D.C.Obj) (σ : T.pi1Tower.carrier) :
    T.colimHom X → T.colimHom X :=
  Quot.lift (fun p => Quot.mk (T.germRel X) (T.germAct X σ p))
    (fun p q h => Quot.sound (T.germAct_rel X σ p q h))

/-- **単位法則（M217F-4b）**: 単位整合族の作用は恒等（id_comp）。 -/
theorem colimAct_one (X : D.C.Obj) (c : T.colimHom X) :
    T.colimAct X T.pi1Tower.one c = c := by
  refine Quot.ind
    (β := fun q => T.colimAct X T.pi1Tower.one q = q) ?_ c
  intro p
  show Quot.mk (T.germRel X) (T.germAct X T.pi1Tower.one p)
      = Quot.mk (T.germRel X) p
  refine congrArg (Quot.mk (T.germRel X)) ?_
  show LevelHom.mk p.lvl (D.C.comp (D.C.id (T.A p.lvl)) p.hom) = p
  rw [D.C.id_comp]

/-- **積法則（M217F-4c）**: 積の作用は作用の合成（assoc）。 -/
theorem colimAct_mul (X : D.C.Obj) (σ τ : T.pi1Tower.carrier)
    (c : T.colimHom X) :
    T.colimAct X (T.pi1Tower.mul σ τ) c
      = T.colimAct X σ (T.colimAct X τ c) := by
  refine Quot.ind
    (β := fun q => T.colimAct X (T.pi1Tower.mul σ τ) q
      = T.colimAct X σ (T.colimAct X τ q)) ?_ c
  intro p
  show Quot.mk (T.germRel X) (T.germAct X (T.pi1Tower.mul σ τ) p)
      = Quot.mk (T.germRel X) (T.germAct X σ (T.germAct X τ p))
  refine congrArg (Quot.mk (T.germRel X)) ?_
  show LevelHom.mk p.lvl
      (D.C.comp
        (D.C.comp (T.pi1Component σ p.lvl).hom
          (T.pi1Component τ p.lvl).hom) p.hom)
    = LevelHom.mk p.lvl
      (D.C.comp (T.pi1Component σ p.lvl).hom
        (D.C.comp (T.pi1Component τ p.lvl).hom p.hom))
  rw [D.C.assoc]

/-- **π₁ 作用付き余極限（M217F-4d）**: colim_n Hom(A_n, X)（M213F-2c）
    の pi1Tower-集合構造。SGA1 の「F(X) への π₁ のモノドロミー作用」の
    pro-対象側の実体。 -/
noncomputable def colimHomAction (X : D.C.Obj) : GAction T.pi1Tower where
  carrier := T.colimHom X
  act := fun σ c => T.colimAct X σ c
  act_one := fun c => T.colimAct_one X c
  act_mul := fun σ τ c => T.colimAct_mul X σ τ c

/-! ## M217F-5: 関手性 — 後合成は π₁ 作用と可換 -/

/-- **レベル射の後合成（M217F-5a）**: f : X → Y は (n, u) ↦ (n, u；f)。 -/
def pushLevel {X Y : D.C.Obj} (f : D.C.Hom X Y) (p : LevelHom T X) :
    LevelHom T Y :=
  ⟨p.lvl, D.C.comp p.hom f⟩

/-- **後合成は芽関係を保つ（M217F-5b）**。 -/
theorem pushLevel_rel {X Y : D.C.Obj} (f : D.C.Hom X Y)
    (p q : LevelHom T X) (h : T.germRel X p q) :
    T.germRel Y (T.pushLevel f p) (T.pushLevel f q) := by
  obtain ⟨k, hp, hq, heq⟩ := h
  refine ⟨k, hp, hq, ?_⟩
  show D.C.comp (T.P hp) (D.C.comp p.hom f)
      = D.C.comp (T.P hq) (D.C.comp q.hom f)
  calc D.C.comp (T.P hp) (D.C.comp p.hom f)
      = D.C.comp (D.C.comp (T.P hp) p.hom) f := (D.C.assoc _ _ _).symm
    _ = D.C.comp (D.C.comp (T.P hq) q.hom) f := by rw [heq]
    _ = D.C.comp (T.P hq) (D.C.comp q.hom f) := D.C.assoc _ _ _

/-- **後合成の余極限写像（M217F-5c）**: f : X → Y の誘導する
    colim Hom(A_n, X) → colim Hom(A_n, Y)（Quot.lift、choice 不要）。 -/
def colimPush {X Y : D.C.Obj} (f : D.C.Hom X Y) :
    T.colimHom X → T.colimHom Y :=
  Quot.lift (fun p => Quot.mk (T.germRel Y) (T.pushLevel f p))
    (fun p q h => Quot.sound (T.pushLevel_rel f p q h))

/-- **同変性（M217F-5d）**: 後合成は π₁ 作用（前合成）と可換
    （assoc）。 -/
theorem colimPush_act {X Y : D.C.Obj} (f : D.C.Hom X Y)
    (σ : T.pi1Tower.carrier) (c : T.colimHom X) :
    T.colimPush f (T.colimAct X σ c)
      = T.colimAct Y σ (T.colimPush f c) := by
  refine Quot.ind
    (β := fun q => T.colimPush f (T.colimAct X σ q)
      = T.colimAct Y σ (T.colimPush f q)) ?_ c
  intro p
  show Quot.mk (T.germRel Y) (T.pushLevel f (T.germAct X σ p))
      = Quot.mk (T.germRel Y) (T.germAct Y σ (T.pushLevel f p))
  refine congrArg (Quot.mk (T.germRel Y)) ?_
  show LevelHom.mk p.lvl
      (D.C.comp (D.C.comp (T.pi1Component σ p.lvl).hom p.hom) f)
    = LevelHom.mk p.lvl
      (D.C.comp (T.pi1Component σ p.lvl).hom (D.C.comp p.hom f))
  rw [D.C.assoc]

/-- **後合成の恒等法則（M217F-5e）**: id の後合成は恒等（comp_id）。 -/
theorem colimPush_id (X : D.C.Obj) (c : T.colimHom X) :
    T.colimPush (D.C.id X) c = c := by
  refine Quot.ind
    (β := fun q => T.colimPush (D.C.id X) q = q) ?_ c
  intro p
  show Quot.mk (T.germRel X) (T.pushLevel (D.C.id X) p)
      = Quot.mk (T.germRel X) p
  refine congrArg (Quot.mk (T.germRel X)) ?_
  show LevelHom.mk p.lvl (D.C.comp p.hom (D.C.id X)) = p
  rw [D.C.comp_id]

/-- **後合成の合成法則（M217F-5f）**: 合成の後合成は後合成の合成
    （assoc）。 -/
theorem colimPush_comp {X Y Z : D.C.Obj} (f : D.C.Hom X Y)
    (g : D.C.Hom Y Z) (c : T.colimHom X) :
    T.colimPush (D.C.comp f g) c = T.colimPush g (T.colimPush f c) := by
  refine Quot.ind
    (β := fun q => T.colimPush (D.C.comp f g) q
      = T.colimPush g (T.colimPush f q)) ?_ c
  intro p
  show Quot.mk (T.germRel Z) (T.pushLevel (D.C.comp f g) p)
      = Quot.mk (T.germRel Z) (T.pushLevel g (T.pushLevel f p))
  refine congrArg (Quot.mk (T.germRel Z)) ?_
  show LevelHom.mk p.lvl (D.C.comp p.hom (D.C.comp f g))
      = LevelHom.mk p.lvl (D.C.comp (D.C.comp p.hom f) g)
  rw [D.C.assoc]

/-- **後合成の同変写像（M217F-5g）**: M217F-5c/5d の束ね。 -/
noncomputable def colimPushHom {X Y : D.C.Obj} (f : D.C.Hom X Y) :
    ActHom (T.colimHomAction X) (T.colimHomAction Y) where
  map := T.colimPush f
  equivariant := fun σ c => T.colimPush_act f σ c

/-! ## M217F-6: 比較関手 C → pi1Tower-Set -/

/-- **比較関手（M217F-6）**: X ↦ (colim_n Hom(A_n, X), π₁ 作用)、
    f ↦ 後合成。SGA1 主定理 C ≃ π₁-Set の同値関手の候補の実構成
    （塔・pro-対象語彙）。関手法則は comp_id / assoc から。 -/
noncomputable def towerComparison :
    Functor D.C (GSetCat T.pi1Tower) where
  onObj := fun X => T.colimHomAction X
  onHom := fun {_X _Y} f => T.colimPushHom f
  map_id := fun X => ActHom.ext (fun c => T.colimPush_id X c)
  map_comp := fun f g => ActHom.ext (fun c => T.colimPush_comp f g c)

/-! ## M217F-7: レベル埋め込み -/

/-- **レベル埋め込み（M217F-7a）**: Hom(A_n, X) → colim_n Hom(A_n, X)。 -/
def levelInclusion (X : D.C.Obj) (n : Nat) (u : D.C.Hom (T.A n) X) :
    T.colimHom X :=
  Quot.mk (T.germRel X) ⟨n, u⟩

/-- **埋め込みと評価の整合（M217F-7b）**: colimEval ∘ levelInclusion =
    towerEval（定義的等式）。 -/
theorem levelInclusion_eval (X : D.C.Obj) (n : Nat)
    (u : D.C.Hom (T.A n) X) :
    T.colimEval X (T.levelInclusion X n u) = T.towerEval X n u := rfl

/-- **定理（M217F-7c）: レベル埋め込みは単射** — 余極限で同一視される
    同レベルの二つの射は元から等しい（層 A_n の連結性 + M21-6
    evaluation 単射性、colimEval を経由）。 -/
theorem levelInclusion_injective (X : D.C.Obj) (n : Nat)
    (u v : D.C.Hom (T.A n) X)
    (h : T.levelInclusion X n u = T.levelInclusion X n v) : u = v := by
  apply D.evaluation_injective (T.hGal n).1 (T.pt n)
  exact congrArg (T.colimEval X) h

/-! ## M217F-8: 比較写像 colimEval の自然性 -/

/-- **定理（M217F-8）: colimEval は自然変換** — 比較関手の台集合
    関手から F への比較写像 colimEval（M213F-3b）は f : X → Y の
    後合成と F(f) を交換する。M213F-6 の対象ごとの全単射性と併せ、
    「F ≅ colim_n Hom(A_n, −)」の**関手レベル**の内容（支配対象上の
    自然同型）を与える。choice の新規使用ゼロ（fmap_comp のみ）。 -/
theorem colimEval_natural (X Y : D.C.Obj) (f : D.C.Hom X Y)
    (c : T.colimHom X) :
    T.colimEval Y (T.colimPush f c) = D.F.onHom f (T.colimEval X c) := by
  refine Quot.ind
    (β := fun q => T.colimEval Y (T.colimPush f q)
      = D.F.onHom f (T.colimEval X q)) ?_ c
  intro p
  exact D.fmap_comp p.hom f (T.pt p.lvl)

/-! ## M217F-9: 忠実性（支配対象上） -/

/-- **定理（M217F-9）: 比較関手の忠実性** — 塔が X を支配すれば
    towerComparison は Hom(X, Y) 上単射: F(X) の各点 x を支配で
    レベル射 u の評価として書き、onHom の一致から
    F(f)(x) = F(g)(x) を得て、M21-4 `fiber_faithful` に帰着する。
    SGA1 圏同値の「忠実」成分の pro-対象語彙での完成。 -/
theorem towerComparison_faithful {X Y : D.C.Obj}
    (hdom : T.DominatesFiber X) (f g : D.C.Hom X Y)
    (h : T.towerComparison.onHom f = T.towerComparison.onHom g) :
    f = g := by
  apply D.fiber_faithful
  intro x
  obtain ⟨n, u, hu⟩ := hdom x
  have h1 : (T.towerComparison.onHom f).map (T.levelInclusion X n u)
      = (T.towerComparison.onHom g).map (T.levelInclusion X n u) := by
    rw [h]
  have h2 := congrArg (T.colimEval Y) h1
  rw [← hu]
  show D.F.onHom f (D.F.onHom u (T.pt n))
      = D.F.onHom g (D.F.onHom u (T.pt n))
  rw [← D.fmap_comp, ← D.fmap_comp]
  exact h2

/-! ## M217F-10: 対象ごとの pro-表現（比較関手語彙） -/

/-- **定理（M217F-10）: 支配対象上で比較関手の台集合は F と全単射** —
    M213F-6 `proRepresentation_of_dominates` の towerComparison
    語彙での再輸出。忠実性（M217F-9）・自然性（M217F-8）と併せ、
    比較関手が支配対象上で F を pro-表現することの束ね。 -/
theorem towerComparison_proRep (X : D.C.Obj) (hdom : T.DominatesFiber X) :
    (∀ p q : (T.towerComparison.onObj X).carrier,
      T.colimEval X p = T.colimEval X q → p = q) ∧
    (∀ x : D.F.onObj X,
      ∃ p : (T.towerComparison.onObj X).carrier, T.colimEval X p = x) :=
  T.proRepresentation_of_dominates X hdom

end GaloisTower

/-! ## M217F-11: 忠実性の無条件化（支配データ / モデル） -/

/-- **定理（M217F-11a）: 支配データ ⟹ 比較関手の忠実性** — 抽象支配
    データ（M189F-8）を持つ任意の D の任意の連結対象 X に対し、
    比較関手が X 上忠実となる塔（支配ガロア対象の定値塔 M213F-8）が
    存在する。仮定・結論とも純抽象語彙。 -/
theorem towerComparison_faithful_of_domination (D : GaloisCatData.{u, 0})
    (hdom : AbstractGaloisDominationData D) (X : D.C.Obj)
    (hX : D.Connected X) :
    ∃ T : GaloisTower D, ∀ (Y : D.C.Obj) (f g : D.C.Hom X Y),
      (GaloisTower.towerComparison T).onHom f
        = (GaloisTower.towerComparison T).onHom g → f = g := by
  obtain ⟨B, hB, φ, hφ⟩ := hdom.dominates X hX
  obtain ⟨b₀⟩ := hB.1.1
  refine ⟨constGaloisTower D B b₀ hB, ?_⟩
  intro Y f g h
  exact GaloisTower.towerComparison_faithful (constGaloisTower D B b₀ hB)
    (GaloisTower.dominatesFiber_of_level_surj
      (constGaloisTower D B b₀ hB) X 0 φ hφ) f g h

/-- **定理（M217F-11b）: モデルでの忠実性** — 任意の群 G のモデル
    `gsetGaloisData G` の任意の抽象連結対象 E に対し、閉包塔
    （M160F-5）上の比較関手は E 上忠実である（M213F-10a の支配 +
    M217F-9）。 -/
theorem towerComparison_faithful_model (G : Grp) (E : GAction G)
    (hE : (gsetGaloisData G).Connected E) :
    ∃ T : GaloisTower (gsetGaloisData G),
      ∀ (Y : (gsetGaloisData G).C.Obj)
        (f g : (gsetGaloisData G).C.Hom E Y),
        (GaloisTower.towerComparison T).onHom f
          = (GaloisTower.towerComparison T).onHom g → f = g := by
  obtain ⟨e₀⟩ := hE.1
  refine ⟨closureTower G E e₀, ?_⟩
  intro Y f g h
  exact GaloisTower.towerComparison_faithful (closureTower G E e₀)
    (closureTower_dominatesFiber G E e₀
      (abstract_connected_transitive G hE)) f g h

/-! ## M217F-12: 本質的全射性のレベル橋（M161F/M186F の塔語彙） -/

/-- **定理（M217F-12a）: 塔レベルの本質的全射性・推移的版** — 塔の
    各層 A_n はガロアなので、M161F-4 がそのまま適用できる: 任意の
    基点付き推移的 Aut(A_n)-集合はある対象の Hom(A_n, −) 値と
    スパン同型。圏同値の「本質的全射」成分の各レベルでの供給。 -/
theorem tower_level_ess_surj (D : QuotientData.{u})
    (T : GaloisTower D.toGaloisCatData) (n : Nat)
    (X : GAction (D.toGaloisCatData.autGrp (T.A n)))
    (hX : X.Transitive) (x₀ : X.carrier) :
    ∃ Xo : D.C.Obj,
      SpanIso X (D.toGaloisCatData.homGAction (T.A n) Xo) :=
  D.abstract_ess_surj_transitive (T.hGal n) (T.pt n) X hX x₀

/-- **定理（M217F-12b）: 塔レベルの本質的全射性・有限和版** —
    M186F-6 の塔語彙での適用: 基点付き推移的 Aut(A_n)-集合の任意の
    有限リストの直和もある対象の Hom(A_n, −) 値とスパン同型。 -/
theorem tower_level_ess_surj_finite (D : SumData.{u})
    (T : GaloisTower D.toGaloisCatData) (n : Nat)
    (L : List (PointedTransitive (D.toGaloisCatData.autGrp (T.A n)))) :
    ∃ Xo : D.C.Obj,
      SpanIso
        (sumListAction (D.toGaloisCatData.autGrp (T.A n))
          (L.map (fun P => P.space)))
        (D.toGaloisCatData.homGAction (T.A n) Xo) :=
  D.abstract_ess_surj_finite (T.hGal n) (T.pt n) L

/-! ## M217F-13: 総括 -/

/-- **総括データ（M217F-13a）**: 圏同値骨格の証人 — ガロア塔・
    比較関手 C → pi1Tower-Set・比較写像 eval と、その忠実性
    （支配対象上）・単射性（無条件）・全射性（支配対象上）。
    充満性と真の 2-out-of-3（圏同値データ）は正直な限定として残る。 -/
structure GaloisEquivalenceData (D : GaloisCatData.{u, 0}) where
  /-- π₁ を担うガロア塔（M24-4a）。 -/
  T : GaloisTower D
  /-- 比較関手 C → pi1Tower-Set（M217F-6）。 -/
  functor : Functor D.C (GSetCat (GaloisTower.pi1Tower T))
  /-- 比較写像: 比較関手の台集合から F へ（M213F-3b の colimEval）。 -/
  eval : (X : D.C.Obj) → (functor.onObj X).carrier → D.F.onObj X
  /-- 忠実性: 塔が X を支配すれば Hom(X, Y) 上単射（M217F-9）。 -/
  faithful : ∀ {X Y : D.C.Obj}, GaloisTower.DominatesFiber T X →
    ∀ f g : D.C.Hom X Y, functor.onHom f = functor.onHom g → f = g
  /-- 比較写像の単射性（pro-米田、無条件、M213F-4b）。 -/
  eval_inj : ∀ (X : D.C.Obj) (p q : (functor.onObj X).carrier),
    eval X p = eval X q → p = q
  /-- 比較写像の全射性（支配対象上、M213F-5b）。 -/
  eval_surj : ∀ X : D.C.Obj, GaloisTower.DominatesFiber T X →
    ∀ x : D.F.onObj X, ∃ p : (functor.onObj X).carrier, eval X p = x

/-- **証人（M217F-13b）**: 任意の抽象ガロア圏 D と任意のガロア塔 T が
    総括データを与える（towerComparison + colimEval + M217F-9 +
    M213F-4b/5b）。 -/
noncomputable def galoisEquivalenceWitness (D : GaloisCatData.{u, 0})
    (T : GaloisTower D) : GaloisEquivalenceData D where
  T := T
  functor := GaloisTower.towerComparison T
  eval := fun X => GaloisTower.colimEval T X
  faithful := fun hdom f g h =>
    GaloisTower.towerComparison_faithful T hdom f g h
  eval_inj := fun X => GaloisTower.colimEval_injective T X
  eval_surj := fun X hdom => GaloisTower.colimEval_surjective T X hdom

/-- **定理（M217F-13c）: 圏同値骨格データの存在** — ガロア対象と
    基点を持つ任意の抽象ガロア圏で（定値塔 M213F-8 による）。 -/
theorem galoisEquivalence_exists (D : GaloisCatData.{u, 0}) (B : D.C.Obj)
    (b₀ : D.F.onObj B) (hB : D.IsGalois B) :
    Nonempty (GaloisEquivalenceData D) :=
  ⟨galoisEquivalenceWitness D (constGaloisTower D B b₀ hB)⟩

/-- **系（M217F-13d）: 無条件の存在**（無矛盾性）— 自明群のモデルの
    一点作用で。 -/
theorem galoisEquivalence_exists_trivial :
    Nonempty (GaloisEquivalenceData (gsetGaloisData punitGrp)) :=
  galoisEquivalence_exists (gsetGaloisData punitGrp)
    (unitAction punitGrp) PUnit.unit unitAction_galois

end IUT
