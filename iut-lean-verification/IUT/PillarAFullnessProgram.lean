/-
  # M261F: 柱A ③ 充満性プログラムの総括 capstone（柱A A-3α ③・束ね capstone）

  M234F `IUT/GaloisFullnessConnected.lean`・M245F `IUT/GSetCoequalizer.lean`・
  M250F `IUT/IntermediateNormalCover.lean`・M255F `IUT/NormalPairBoundary.lean`
  の 4 モジュールで個別に確立された、柱A A-3α ③（比較関手の充満性・
  一般連結対象 X）に関する成果を **一つの証明記録に束ねる**。本モジュールは
  **新規の数学的主張を一切持たない**（M220F `IUT/PillarDInterface.lean`・
  M243F `IUT/LambdaTowerRamifCapstone.lean` と同じ束ね capstone イディオム）。
  全フィールドは既存定理 `constTower_full_connected` /
  `gsetHquot_of_fiberTransitive` / `intermediateNormalConnectedData_exists` /
  `normalPair_hfib_iff_normalizesSub` をそのまま代入するだけで埋まる。

  * M261F-1（③a）`connected_fullness` — **一般連結 X 上の条件付き充満性**
    （M234F-3 `constTower_full_connected`）: 支配ガロア対象 B・F-epi
    p : B → X・商の普遍性 hquot を仮定すれば、B 上定値塔の比較関手は
    X 上充満。
  * M261F-2（③b）`hquot_model` — **hquot の G-Set モデル discharge**
    （M245F-1 `gsetHquot_of_fiberTransitive`）: G-Set モデルで F-epi
    p : B → X とファイバー推移性 hfib を仮定すれば、deck 不変な v は
    p を経由して降りる（hquot の一般 discharge）。
  * M261F-3（③c）`intermediate_cover` — **中間正規被覆での discharge の
    存在**（M250F-3b `intermediateNormalConnectedData_exists`）: 任意の
    群 G・部分群 H に対し、中間正規被覆 G/core(H) → G/H で hquot を
    discharge した `ConnectedFullnessData` が存在する。
  * M261F-4（③d）`boundary_iff` — **hquot 境界の両方向特徴付け**
    （M255F-8b `normalPair_hfib_iff_normalizesSub`）: 被覆
    p : G/H₀ → G/H（H₀ ⊆ H）のファイバー推移性 hfib ⟺ H が H₀ を
    正規化する（H₀ ⊴ H）。
  * M261F-5 `PillarAFullnessProgramData` / `pillarAFullnessProgramData` /
    `pillarAFullnessProgram_exists` — 総括レコードと witness・存在。

  **意義**: 柱A A-3α ③（充満性プログラム）で個別に積み上げられた
  (i) 一般連結 X 上の条件付き充満性（M234F、hquot 仮定を明示的に
  切り出した無条件の軌道生成＋deck 不変性の自動導出込み）、
  (ii) hquot の G-Set モデルでの一般 discharge（M245F、ファイバー
  推移性 hfib のもとで）、
  (iii) 中間正規被覆 G/core(H) → G/H での非自明 witness の存在
  （M250F）、
  (iv) hquot/hfib 境界の正規性による両方向特徴付け（M255F）
  を、既存の型パラメータのまま一つの型 `PillarAFullnessProgramData`
  に固定し、new proof を一切追加せずに 4 モジュール（M234F・M245F・
  M250F・M255F）の合流点として閉じることを機械的に証明する。

  **正直な限定**: 本 capstone が束ねるのは
  「③ 充満性プログラム＝一般連結 X 充満性（hquot 仮定下）・hquot の
  モデル/中間被覆 discharge・正規性境界の特徴付けが揃った」ことの
  certification のみである。依然として
  (1) hquot（商の普遍性）は一般には仮定として明示切り出しされたまま
      であり（M234F 参照）、抽象 `GaloisCatData` の公理から無条件には
      導出されない。discharge できるのは G-Set モデルでファイバー
      推移的（正規/ガロア）被覆に限る対象クラスのみ（M245F/M250F/M255F）。
  (2) 非 Galois 対象（B がガロアでない場合）への充満性の拡張は範囲外
      （M234F の枠組みは常に「B はガロア・X は B に F-epi で支配される」
      形を前提とする）。
  (3) 単一の cofinal 塔（真の共終塔）への一般化は依然未達（塔は
      定値塔 B 上に限る、M234F の正直な限定 (3) を継承）。
  本モジュールはこれらの限定を変えず、既存 4 層の成果を並べて束ねる
  のみである。

  全て選択公理の新規使用なし（M234F/M245F/M250F/M255F から
  propext・Classical.choice（型経由の継承のみ）・Quot.sound を継承、
  本モジュールの証明体での新規 Classical.choice 使用はゼロ）。
  サブエージェント tier S（sonnet）・束ね capstone。
-/
import IUT.GaloisFullnessConnected
import IUT.GSetCoequalizer
import IUT.IntermediateNormalCover
import IUT.NormalPairBoundary

namespace IUT

universe u

/-! ## M261F-5: 柱A ③ 充満性プログラムの総括構造体 -/

/-- **M261F: 柱A A-3α ③ 充満性プログラムの総括** — ③ の四つの並行部品
    （一般連結 X 上の条件付き充満性・hquot の G-Set モデル discharge・
    中間正規被覆での discharge の存在・hquot/hfib 境界の特徴付け）を
    一つのレコードに束ねる bundling capstone。 -/
structure PillarAFullnessProgramData where
  /-- M234F-3: 一般連結対象 X 上の条件付き充満性（hquot 仮定下）。 -/
  connected_fullness : ∀ (D : GaloisCatData.{u, 0})
    (B : D.C.Obj) (b₀ : D.F.onObj B) (hB : D.IsGalois B)
    (X : D.C.Obj) (p : D.C.Hom B X)
    (_hp : ∀ y : D.F.onObj X, ∃ w : D.F.onObj B, D.F.onHom p w = y)
    (Y : D.C.Obj)
    (_hquot : ∀ v : D.C.Hom B Y,
      (∀ σ : CatIso D.C B B, D.C.comp σ.hom p = p → D.C.comp σ.hom v = v) →
      ∃ u : D.C.Hom X Y, D.C.comp p u = v)
    (φ : ActHom
      (GaloisTower.colimHomAction (constGaloisTower D B b₀ hB) X)
      (GaloisTower.colimHomAction (constGaloisTower D B b₀ hB) Y)),
    ∃ u : D.C.Hom X Y,
      (constGaloisTower D B b₀ hB).towerComparison.onHom u = φ
  /-- M245F-1: G-Set モデルでの hquot のファイバー推移性からの discharge。 -/
  hquot_model : ∀ {G : Grp} (B X Y : GAction G) (p : ActHom B X)
    (_hp : ∀ y : X.carrier, ∃ w : B.carrier, p.map w = y)
    (_hfib : ∀ b b' : B.carrier, p.map b = p.map b' →
      ∃ σ : CatIso (GSetCat G) B B,
        ActHom.comp σ.hom p = p ∧ σ.hom.map b = b')
    (v : ActHom B Y)
    (_hinv : ∀ σ : CatIso (GSetCat G) B B,
      ActHom.comp σ.hom p = p → ActHom.comp σ.hom v = v),
    ∃ u : ActHom X Y, ActHom.comp p u = v
  /-- M250F-3b: 中間正規被覆 G/core(H) → G/H での discharge の存在
      （任意の群 G・部分群 H）。 -/
  intermediate_cover : ∀ (G : Grp) (_H : Subgroup G),
    Nonempty (ConnectedFullnessData (gsetGaloisData G))
  /-- M255F-8b: hquot/hfib の境界の両方向特徴付け——被覆
      p : G/H₀ → G/H（H₀ ⊆ H）のファイバー推移性 hfib ⟺ H が H₀ を
      正規化する（H₀ ⊴ H）。 -/
  boundary_iff : ∀ (G : Grp) (H H₀ : Subgroup G)
    (hle : ∀ g, H₀.mem g → H.mem g),
    (∀ b b' : (cosetAction G H₀).carrier,
      (genDominates G H₀ H hle).map b = (genDominates G H₀ H hle).map b' →
      ∃ σ : CatIso (GSetCat G) (cosetAction G H₀) (cosetAction G H₀),
        ActHom.comp σ.hom (genDominates G H₀ H hle)
          = genDominates G H₀ H hle ∧
        σ.hom.map b = b')
      ↔ normalizesSub G H H₀

/-- **M261F-5a: 総括 witness 本体** — 各フィールドへ既存の
    定理をそのまま代入する choice-free コンストラクタ（本証明体での
    新規 choice 使用ゼロ）。新規証明ゼロ（再輸出のみ）。 -/
def pillarAFullnessProgramData : PillarAFullnessProgramData where
  connected_fullness := constTower_full_connected
  hquot_model := gsetHquot_of_fiberTransitive
  intermediate_cover := intermediateNormalConnectedData_exists
  boundary_iff := normalPair_hfib_iff_normalizesSub

/-- **定理 (M261F-5b): 柱A ③ 充満性プログラム総括の存在** — 四つの
    ③ 成果（一般連結 X 上の条件付き充満性・hquot の G-Set モデル
    discharge・中間正規被覆での discharge の存在・hquot/hfib 境界の
    特徴付け）を束ねた `PillarAFullnessProgramData` は充足可能。
    「充満性プログラム ③」が単一の `Nonempty` 命題として certify
    される。 -/
theorem pillarAFullnessProgram_exists :
    Nonempty PillarAFullnessProgramData :=
  ⟨pillarAFullnessProgramData⟩

end IUT
