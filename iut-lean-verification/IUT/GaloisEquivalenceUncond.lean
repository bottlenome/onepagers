/-
  # M229F: 条件付き主定理の無条件化（choice 能動使用）（柱A A-3β 無条件スライス）

  M225F `GaloisEquivalenceBundle` は「擬逆データ `QuasiInverseData` が
  与えられれば真の圏同値である」という**条件付き主定理**
  （towerComparison_catEquiv_of_quasiInverse）までを、Classical.choice を
  新規に持ち込まずに構成した。残っていた誠実な限定は「M221F の充満性は
  `∃ u, onHom u = φ`（存在）であり、そこから擬逆データが要求する
  `homInv`（φ ↦ u の**関数**）を抽出するには Classical.choice を要する」
  ことであった。

  本モジュールは、**型継承ではなく Classical.choice を能動使用して**、
  M225F の条件付き主定理を**無条件化する**（M24 `transAut` の
  `∃!→関数` 抽出と同種の技法。本タスクは新規 choice の使用が
  許される）。核心:

  * M229F-1 `regEndCat` / `regEndPi1Cat` — **正則対象の一点自己準同型
    圏**: `regAction G`（M221F-8）と、その比較関手像 `F(regAction G)`
    のそれぞれの自己準同型モノイドを一点圏（Obj = PUnit、Hom = End）
    として組織化。GSetCat の恒等・合成・法則をそのまま継承
  * M229F-2 `regComparisonFunctor` / `regEndComparison` — 比較関手
    `towerComparison`（M217F-6）の正則自己準同型への制限関手
    `regEndCat → regEndPi1Cat`。関手法則は towerComparison から継承
  * M229F-3 `regHomInv` / `regFullyFaithful` — **∃→関数の choice 抽出**:
    M221F-8e `towerComparison_full_regular`（正則対象上の**無条件**充満性、
    `∃ u, onHom u = φ`）に `Classical.choose` を適用し、擬逆データが要求
    する両側逆写像 `homInv`（関数）を得る。左逆は M221F-8f
    `towerComparison_regular_fully_faithful` の**無条件**忠実性、
    右逆は `Classical.choose_spec`。これで M225F の
    `FullyFaithful (regEndComparison G)` が**無条件に**得られる
  * M229F-4 `regQuasiInverseData` — **無条件 QuasiInverseData**:
    invObj は一点写像、ff は M229F-3、余単位同型は一点圏の恒等同型
    （F(invObj •) = F(regAction G) = • なので恒等）。M225F-8e の仮説を
    正則スライスについて choice で discharge した無条件の擬逆データ
  * M229F-5 `towerComparison_catEquiv_regular`（+ Nonempty・自明群）—
    **capstone: 無条件の圏同値**。M229F-4 を M225F-6
    `catEquivOfQuasiInverse` に食わせ、正則対象の自己準同型圏について
    `CatEquiv (regEndCat G) (regEndPi1Cat G)` を**無条件に**得る。
    SGA1 主定理の充満忠実性 End(G_reg) ≅ End_{π₁-Set}(F(G_reg)) の
    圏同値としての無条件形

  **意義**: A-3β の欠片の無条件化 — M225F の条件付き主定理の仮説
  `QuasiInverseData` を、正則対象について **Classical.choice を能動使用**
  して discharge した。M221F が正則対象上で**無条件に**証明した
  「充満（∃ 版）+ 忠実」から、M24 `transAut` と同種の `∃→関数` 抽出で
  擬逆データの `homInv` を関数化し、M225F の抽象 capstone に接続する。
  条件付き（M225F-8e）→ 無条件（本 capstone）の橋。

  **正直な限定**: (1) 無条件化は**モデルの正則対象 `regAction G` の
  自己準同型スライス**についてである。M221F の充満性は
  「**源が `regAction G`** の射 `∃ u, onHom u = φ`」の形でのみ無条件で
  あり（一般の源対象 X 上の充満性は F-全射 A_n → X に沿った降下 =
  商の普遍性を要し未達成）、したがって比較関手**全体**に対する
  `FullyFaithful`（全対象対で両側逆）は依然構成できない。ゆえに本
  capstone は比較関手全体の圏同値 C ≃ π₁-Set ではなく、**正則対象の
  一点自己準同型圏**の圏同値 End(G_reg) ≅ End_{π₁-Set}(F(G_reg)) に
  限定される。一般連結 X・単一 cofinal 塔・比較関手全体の圏同値は
  依然スコープ外（別労力）。(2) 本モジュールは M24/G6 由来の
  choice を型経由で継承するだけでなく、**証明体で Classical.choice を
  能動使用する**（`regHomInv` の ∃→関数抽出）。これは本タスクの目的で
  あり許容される（M24 `transAut` と同種）。

  本モジュールは型継承でなく choice を能動使用して条件付き主定理を
  無条件化する（M24 `transAut` と同種）。`#print axioms` 実測想定:
  [propext, Classical.choice, Quot.sound]。
  サブエージェント並行部品。
-/
import IUT.GaloisEquivalenceBundle

namespace IUT

/-! ## M229F-1: 正則対象の一点自己準同型圏 -/

/-- **正則対象の自己準同型圏（M229F-1a）**: 一点圏（Obj = PUnit、
    Hom = End_{GSetCat G}(regAction G)）。GSetCat G の恒等・合成・
    法則をそのまま継承。 -/
noncomputable def regEndCat (G : Grp) : Cat where
  Obj := PUnit.{1}
  Hom := fun _ _ => (gsetGaloisData G).C.Hom (regAction G) (regAction G)
  id := fun _ => (gsetGaloisData G).C.id (regAction G)
  comp := fun f g => (gsetGaloisData G).C.comp f g
  id_comp := fun f => (gsetGaloisData G).C.id_comp f
  comp_id := fun f => (gsetGaloisData G).C.comp_id f
  assoc := fun f g h => (gsetGaloisData G).C.assoc f g h

/-- **比較関手（再輸出, M229F-1b）**: 正則塔の比較関手
    `towerComparison`（M217F-6）。 -/
noncomputable def regComparisonFunctor (G : Grp) :
    Functor (gsetGaloisData G).C
      (GSetCat (GaloisTower.pi1Tower (regTower G))) :=
  (regTower G).towerComparison

/-- **像の自己準同型圏（M229F-1c）**: 一点圏（Obj = PUnit、
    Hom = End_{π₁-Set}(F(regAction G))）。 -/
noncomputable def regEndPi1Cat (G : Grp) : Cat where
  Obj := PUnit.{1}
  Hom := fun _ _ =>
    (GSetCat (GaloisTower.pi1Tower (regTower G))).Hom
      ((regComparisonFunctor G).onObj (regAction G))
      ((regComparisonFunctor G).onObj (regAction G))
  id := fun _ =>
    (GSetCat (GaloisTower.pi1Tower (regTower G))).id
      ((regComparisonFunctor G).onObj (regAction G))
  comp := fun f g =>
    (GSetCat (GaloisTower.pi1Tower (regTower G))).comp f g
  id_comp := fun f =>
    (GSetCat (GaloisTower.pi1Tower (regTower G))).id_comp f
  comp_id := fun f =>
    (GSetCat (GaloisTower.pi1Tower (regTower G))).comp_id f
  assoc := fun f g h =>
    (GSetCat (GaloisTower.pi1Tower (regTower G))).assoc f g h

/-! ## M229F-2: 制限比較関手 -/

/-- **制限比較関手（M229F-2）**: `towerComparison` を正則自己準同型に
    制限した関手 `regEndCat → regEndPi1Cat`。関手法則は
    towerComparison の map_id / map_comp を継承。 -/
noncomputable def regEndComparison (G : Grp) :
    Functor (regEndCat G) (regEndPi1Cat G) where
  onObj := fun _ => PUnit.unit
  onHom := fun {_ _} f => (regComparisonFunctor G).onHom f
  map_id := fun _ => (regComparisonFunctor G).map_id (regAction G)
  map_comp := fun f g => (regComparisonFunctor G).map_comp f g

/-! ## M229F-3: ∃→関数の choice 抽出（無条件充満忠実） -/

/-- **choice による逆写像（M229F-3a）**: M221F-8e `towerComparison_full_regular`
    の無条件充満性 `∃ u, onHom u = g` に `Classical.choose` を適用して
    得た逆写像（φ ↦ u の**関数**）。M24 `transAut` と同種の ∃→関数抽出、
    ただし本モジュールでは choice を**能動使用**する。 -/
noncomputable def regHomInv (G : Grp)
    (g : (regEndPi1Cat G).Hom
      ((regEndComparison G).onObj PUnit.unit)
      ((regEndComparison G).onObj PUnit.unit)) :
    (regEndCat G).Hom PUnit.unit PUnit.unit :=
  Classical.choose (towerComparison_full_regular G (regAction G) g)

/-- **無条件充満忠実（M229F-3b）**: `regHomInv`（choice 抽出）を両側逆
    写像とする `FullyFaithful (regEndComparison G)`。右逆は
    `Classical.choose_spec`（充満性の実現）、左逆は M221F-8f
    `towerComparison_regular_fully_faithful` の**無条件**忠実性。
    M225F では受け取るしかなかった `homInv` を choice で無条件に構成。 -/
noncomputable def regFullyFaithful (G : Grp) :
    FullyFaithful (regEndComparison G) where
  homInv := fun {_ _} g => regHomInv G g
  homInv_left := fun {_ _} f => by
    have hspec := Classical.choose_spec
      (towerComparison_full_regular G (regAction G)
        ((regEndComparison G).onHom f))
    exact (towerComparison_regular_fully_faithful G (regAction G)).1 _ f hspec
  homInv_right := fun {_ _} g =>
    Classical.choose_spec (towerComparison_full_regular G (regAction G) g)

/-! ## M229F-4: 無条件 QuasiInverseData -/

/-- **無条件擬逆データ（M229F-4）**: `regEndComparison` に対する
    `QuasiInverseData` を**無条件に**構成。invObj は一点写像、
    ff は M229F-3b（choice で無条件化した充満忠実）、余単位同型は
    F(invObj •) = F(regAction G) = • ゆえ一点圏の恒等同型。
    M225F-8e の条件付き主定理の仮説を、正則スライスについて choice で
    discharge した無条件版。 -/
noncomputable def regQuasiInverseData (G : Grp) :
    QuasiInverseData (regEndComparison G) where
  invObj := fun _ => PUnit.unit
  ff := regFullyFaithful G
  counitIso := fun _ =>
    { hom := (regEndPi1Cat G).id PUnit.unit
      inv := (regEndPi1Cat G).id PUnit.unit
      hom_inv := (regEndPi1Cat G).id_comp ((regEndPi1Cat G).id PUnit.unit)
      inv_hom := (regEndPi1Cat G).id_comp ((regEndPi1Cat G).id PUnit.unit) }

/-! ## M229F-5: capstone — 無条件の圏同値 -/

/-- **capstone（M229F-5a）: 無条件の圏同値**。M229F-4 の無条件擬逆
    データを M225F-6 `catEquivOfQuasiInverse` に食わせ、正則対象の
    自己準同型圏について `CatEquiv (regEndCat G) (regEndPi1Cat G)` を
    **無条件に**得る。SGA1 主定理の充満忠実性
    End(G_reg) ≅ End_{π₁-Set}(F(G_reg)) の圏同値としての無条件形。
    M225F-8e の条件付き主定理を正則スライスについて無条件化した結果。 -/
noncomputable def towerComparison_catEquiv_regular (G : Grp) :
    CatEquiv (regEndCat G) (regEndPi1Cat G) :=
  catEquivOfQuasiInverse (regQuasiInverseData G)

/-- **系（M229F-5b）: 無条件圏同値の存在**（任意の群 G のモデル）。 -/
theorem towerComparison_catEquiv_regular_nonempty (G : Grp) :
    Nonempty (CatEquiv (regEndCat G) (regEndPi1Cat G)) :=
  ⟨towerComparison_catEquiv_regular G⟩

/-- **系（M229F-5c）: 無条件の存在**（無矛盾性）— 自明群で。 -/
theorem towerComparison_catEquiv_regular_trivial :
    Nonempty (CatEquiv (regEndCat punitGrp) (regEndPi1Cat punitGrp)) :=
  towerComparison_catEquiv_regular_nonempty punitGrp

end IUT
