/-
  # M234F: 一般連結対象 X 上の充満性への降下（柱A A-3α ③）

  M221F は比較関手 `towerComparison : C → π₁Tower-Set` の充満性を
  **ガロア対象 B 上（自己射⟹自己同型の条件付き）** および
  **モデルの正則対象 G_reg 上（無条件）** で証明し、M229F はその正則
  スライスを無条件の圏同値へ昇格した。両者に共通して残った「正直な
  限定」が、本タスクの本丸 ③ — **一般連結対象 X 上の充満性**（M229F の
  限定に「一般の源対象 X 上の充満性 = F-全射 A_n → X に沿った降下 =
  商の普遍性は未達成」と明記された当のもの）である。

  本モジュールは、X を支配するガロア対象 B（F-epi p : B → X）に沿って
  **正則/ガロア対象で確立済みの充満性の論理構造（M221F-2/3 の
  軌道生成 + 一点実現可能性）を X へ降下**させる。核心は充満性を二つの
  スライスに分けて、**片方（軌道生成）を一般 X で無条件に証明し**、
  もう片方（実現可能性）を商の普遍性（コエコライザ / 降下）という
  **明示仮定**へ切り出すことである:

  * M234F-1 `constTower_orbitGenerated_connected` — **一般 X の軌道生成
    （無条件・本モジュールの主要な前進）**: B がガロアで p : B → X が
    F-epi なら、定値塔（B 上）の比較関手について、X 上の余極限
    `colim_n Hom(B, X)` は基点類 `[p]`（= p の 0-レベル類）の π₁ 軌道で
    尽くされる。証明: 任意の類 [w]（w : B → X）に対し、F(w)(b₀) を
    F-epi p で F(B) に持ち上げ（点 v）、B のガロア推移性で b₀ を v へ
    運ぶ自己同型 ι を取り、evaluation 単射性（B 連結）で
    ι ; p = w（射レベルの一致）を得て σ = constPi1 ι の作用で
    [p] ↦ [ι;p] = [w] に到達する。**M221F-6a（X = B・hendo 条件付き）を
    一般 X（F-epi 支配のみ）へ拡張**した無条件版
  * M234F-2 `constTower_deckInvariant_of_equivariant` — **降下の必要
    条件の自動導出**: π₁-同変写像 φ の基点値 φ([p]) の代表射 v に対し、
    p の任意の被覆変換（deck 変換）σ（σ.hom ; p = p）が
    σ.hom ; v = v を満たすこと（v は p のファイバー上定値 = 降下可能性の
    必要条件）が **φ の同変性から自動的に従う**。証明: deck σ は
    constPi1 σ として基点類 [p] を固定するので、同変性から φ([p]) も
    固定され、levelInclusion 単射性で σ.hom ; v = v
  * M234F-3 `constTower_full_connected` — **一般連結 X 上の条件付き
    充満性（本モジュールの capstone 定理）**: F-epi 支配 p : B → X と、
    **商の普遍性 `hquot`**（「p の deck 変換で不変な v : B → Y は p を
    経由して降りる: ∃ u : X → Y, p ; u = v」）を仮定すれば、X 上
    比較関手は充満: 任意の π₁-同変 φ : colimHom X → colimHom Y は
    C の射 u : X → Y の後合成である。証明は M234F-1 の軌道生成 +
    M234F-2 で自動導出した deck 不変性 + hquot による実現可能性を
    M221F-3 `towerComparison_full_of_orbit` に食わせる
  * M234F-4 `ConnectedFullnessData` / `ConnectedFullnessData.full` /
    `connectedFullness_exists_trivial` — capstone データ（支配ガロア
    対象 B・被支配対象 X・F-epi p・商の普遍性）とそこからの X 上充満性、
    および無矛盾性（自明群・一点対象・p = id で商の普遍性が自明成立）

  **前進したスライス（正則対象を超えて一般 X にどこまで届いたか）**:
  充満性 = 「軌道生成」+「一点実現可能性」の分解（M221F-2/3）のうち、
  **軌道生成の側は一般 X（F-epi でガロア対象に支配される任意の対象）で
  無条件に証明された**（M234F-1）。これは M221F/M229F が正則・ガロア
  **自身**の対象に限っていた地点からの実質的前進である（源対象 X が
  ガロアである必要も、hendo「自己射⟹自己同型」も不要になった）。
  さらに、降下に必要な「v の deck 不変性」は φ の同変性から**自動で
  出る**ことを示した（M234F-2）ので、残る唯一の外部入力は
  **商の普遍性 hquot（X = B/Deck(p) というコエコライザの普遍性）**
  一点に純化された。

  **正直な限定**:
  (1) 一般 X 上の充満性は **hquot（商の普遍性 = 降下）を仮定した
      条件付き**である。hquot は「p の deck 変換 σ（σ;p = p）で不変な
      任意の v : B → Y が p を経由する」という X = B/Deck(p) の
      コエコライザ普遍性であり、現行 `GaloisCatData` の公理には
      コエコライザ/連結成分分解が無いため純公理からは導出できない
      （M189F の正直な限定 (1) と同根）。本モジュールはこの一点を
      **明示仮定として誠実に切り出し**、それ以外（軌道生成・deck 不変性
      の自動導出・実現からの充満性復元）を無条件に閉じた。
  (2) hquot を discharge した**無条件のモデル例**は、本モジュールでは
      自明群・一点対象・p = id（deck 条件が空で自明成立）の無矛盾性
      witness に留める。非自明な X での hquot のモデル証明（G-Set の
      コエコライザの明示構成）は別労力（範囲外）。したがって「正則
      対象を超えた**無条件**充満性」ではなく「一般 X 上の**条件付き**
      充満性 + 軌道生成の無条件化」が本モジュールの正確な到達点である。
  (3) 塔は定値塔（B 上）に限る（真の共終塔は M213F/M221F と同じく
      未達成）。充満 + 忠実からの真の圏同値（擬逆・単位・余単位）の
      束ねは A-3β（M229F が正則スライスで無条件化済み、一般 X は残余）。
  (4) 公理フットプリント（`#print axioms` 実測）: π₁ に触れる全定理は
      M24 `transAut`（∃!→関数）由来の Classical.choice を**継承**
      （不可避）。商操作は Quot.sound(+propext)。本モジュールの
      **証明体での新規 choice 使用はゼロ**（代表元抽出は
      `Quot.exists_rep`、自己同型の CatIso 化は IsGalois の witness を
      obtain するだけで choice の新規使用なし）。想定:
      [propext, Classical.choice, Quot.sound]。

  全て選択公理の新規使用なし（M24/M21-8 からの継承を除く）。
  サブエージェント並行部品（tier M / opus）。
-/
import IUT.GaloisFullness

namespace IUT

universe u

/-! ## M234F-1: 一般 X の軌道生成（無条件） -/

/-- **定理（M234F-1）: 一般連結対象 X 上の軌道生成（無条件）** —
    B がガロアで p : B → X が F-epi（∀ y ∈ F(X), ∃ w ∈ F(B), F(p)(w) = y）
    なら、B 上の定値塔（M213F-8）の比較関手について、X 上の余極限
    `colim_n Hom(B, X)` の全ての類は基点類 `[p]`（p の 0-レベル埋め込み、
    M217F-7a）の π₁ 軌道に入る。M221F-6a（X = B・hendo 条件付き）を
    一般 X（F-epi 支配のみ）へ拡張した無条件版。choice の新規使用ゼロ。 -/
theorem constTower_orbitGenerated_connected (D : GaloisCatData.{u, 0})
    (B : D.C.Obj) (b₀ : D.F.onObj B) (hB : D.IsGalois B)
    (X : D.C.Obj) (p : D.C.Hom B X)
    (hp : ∀ y : D.F.onObj X, ∃ w : D.F.onObj B, D.F.onHom p w = y) :
    GaloisTower.OrbitGenerated (constGaloisTower D B b₀ hB) X
      (GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p) := by
  intro c
  refine Quot.ind
    (β := fun q => ∃ σ : (constGaloisTower D B b₀ hB).pi1Tower.carrier,
      (constGaloisTower D B b₀ hB).colimAct X σ
        (GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p) = q)
    ?_ c
  intro pr
  obtain ⟨n, w⟩ := pr
  obtain ⟨v, hv⟩ := hp (D.F.onHom w b₀)
  obtain ⟨σ0, hσiso, hσv⟩ := hB.2 b₀ v
  obtain ⟨σinv, hsi1, hsi2⟩ := hσiso
  refine ⟨constPi1 D B b₀ hB ⟨σ0, σinv, hsi1, hsi2⟩, ?_⟩
  have hw : D.C.comp σ0 p = w := by
    apply D.evaluation_injective hB.1 b₀
    show D.F.onHom (D.C.comp σ0 p) b₀ = D.F.onHom w b₀
    rw [D.fmap_comp, hσv]
    exact hv
  show Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) X)
      ⟨0, D.C.comp σ0 p⟩
    = Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) X) ⟨n, w⟩
  refine Eq.trans
    (congrArg
      (Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) X))
      (congrArg
        (fun t =>
          (⟨0, t⟩ : GaloisTower.LevelHom (constGaloisTower D B b₀ hB) X))
        hw))
    (constTower_class_eq D B b₀ hB X 0 n w)

/-! ## M234F-2: 降下の必要条件（deck 不変性）の自動導出 -/

/-- **定理（M234F-2）: v の deck 不変性は φ の同変性から自動で従う** —
    π₁-同変写像 φ の基点値 φ([p]) の 0-レベル代表射 v（φ([p]) = [v]）に
    対し、p の任意の被覆変換 σ（σ.hom ; p = p、= Deck(p) の元）は
    σ.hom ; v = v を満たす。証明: constPi1 σ は基点類 [p] を固定するので
    同変性から φ([p]) も固定され、levelInclusion 単射性（M217F-7c）で
    射レベルの等式に落ちる。降下（商の普遍性）の必要条件が仮定でなく
    定理として出ることの確認。choice の新規使用ゼロ。 -/
theorem constTower_deckInvariant_of_equivariant (D : GaloisCatData.{u, 0})
    (B : D.C.Obj) (b₀ : D.F.onObj B) (hB : D.IsGalois B)
    (X Y : D.C.Obj) (p : D.C.Hom B X) (v : D.C.Hom B Y)
    (φ : ActHom
      (GaloisTower.colimHomAction (constGaloisTower D B b₀ hB) X)
      (GaloisTower.colimHomAction (constGaloisTower D B b₀ hB) Y))
    (hφc : φ.map
        (GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p)
      = Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) Y) ⟨0, v⟩)
    (σ : CatIso D.C B B) (hσp : D.C.comp σ.hom p = p) :
    D.C.comp σ.hom v = v := by
  have hfix : (constGaloisTower D B b₀ hB).colimAct X (constPi1 D B b₀ hB σ)
      (GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p)
    = GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p :=
    congrArg
      (fun t =>
        Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) X)
          (⟨0, t⟩ : GaloisTower.LevelHom (constGaloisTower D B b₀ hB) X))
      hσp
  have heq : φ.map
      ((constGaloisTower D B b₀ hB).colimAct X (constPi1 D B b₀ hB σ)
        (GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p))
    = (constGaloisTower D B b₀ hB).colimAct Y (constPi1 D B b₀ hB σ)
        (φ.map
          (GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p)) :=
    φ.equivariant (constPi1 D B b₀ hB σ)
      (GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p)
  rw [hfix, hφc] at heq
  have heq2 :
      GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) Y 0 v
    = GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) Y 0
        (D.C.comp σ.hom v) := heq
  exact ((constGaloisTower D B b₀ hB).levelInclusion_injective Y 0 v
    (D.C.comp σ.hom v) heq2).symm

/-! ## M234F-3: 一般連結 X 上の条件付き充満性（capstone 定理） -/

/-- **capstone 定理（M234F-3）: 一般連結対象 X 上の条件付き充満性** —
    B がガロア・p : B → X が F-epi で、かつ**商の普遍性**
    `hquot`（p の deck 変換で不変な v : B → Y は p を経由して降りる）を
    仮定すれば、B 上定値塔の比較関手は X 上充満: 任意の π₁-同変写像
    φ : colimHom X → colimHom Y は C の射 u : X → Y の後合成である。
    証明: 軌道生成（M234F-1・無条件）+ 一点実現可能性（φ([p]) の
    代表射 v の deck 不変性を M234F-2 で自動導出し、hquot で p 経由に
    降ろして実現子 u を得る）を M221F-3
    `towerComparison_full_of_orbit` に食わせる。SGA1 の「充満忠実性を
    普遍被覆 B から商 X = B/Deck(p) へ降ろす」段の形式化
    （降下 = 商の普遍性一点のみ明示仮定）。 -/
theorem constTower_full_connected (D : GaloisCatData.{u, 0})
    (B : D.C.Obj) (b₀ : D.F.onObj B) (hB : D.IsGalois B)
    (X : D.C.Obj) (p : D.C.Hom B X)
    (hp : ∀ y : D.F.onObj X, ∃ w : D.F.onObj B, D.F.onHom p w = y)
    (Y : D.C.Obj)
    (hquot : ∀ v : D.C.Hom B Y,
      (∀ σ : CatIso D.C B B, D.C.comp σ.hom p = p → D.C.comp σ.hom v = v) →
      ∃ u : D.C.Hom X Y, D.C.comp p u = v)
    (φ : ActHom
      (GaloisTower.colimHomAction (constGaloisTower D B b₀ hB) X)
      (GaloisTower.colimHomAction (constGaloisTower D B b₀ hB) Y)) :
    ∃ u : D.C.Hom X Y,
      (constGaloisTower D B b₀ hB).towerComparison.onHom u = φ := by
  obtain ⟨pr0, hrep⟩ := Quot.exists_rep
    (φ.map (GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p))
  obtain ⟨m, v⟩ := pr0
  have hφc : φ.map
      (GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p)
    = Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) Y)
        ⟨0, v⟩ :=
    hrep.symm.trans (constTower_class_eq D B b₀ hB Y m 0 v)
  have hdeck : ∀ σ : CatIso D.C B B,
      D.C.comp σ.hom p = p → D.C.comp σ.hom v = v :=
    fun σ hσp => constTower_deckInvariant_of_equivariant D B b₀ hB X Y p v
      φ hφc σ hσp
  obtain ⟨u, hu⟩ := hquot v hdeck
  refine GaloisTower.towerComparison_full_of_orbit (constGaloisTower D B b₀ hB)
    φ (GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) X 0 p)
    (constTower_orbitGenerated_connected D B b₀ hB X p hp) ⟨u, ?_⟩
  exact (congrArg
    (fun t =>
      Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) Y)
        (⟨0, t⟩ : GaloisTower.LevelHom (constGaloisTower D B b₀ hB) Y))
    hu).trans hφc.symm

/-! ## M234F-4: capstone データと無矛盾性 -/

/-- **capstone データ（M234F-4a）**: 一般連結対象 X 上の充満性の証人 —
    支配ガロア対象 B（基点 b₀）・被支配対象 X・F-epi p : B → X・
    商の普遍性（p の deck 変換で不変な射は p を経由）。M221F-9a
    `GaloisFullnessData`（ガロア対象 B 自身の上）を、F-epi で B に
    支配される**一般 X** の上へ拡張した構造体。 -/
structure ConnectedFullnessData (D : GaloisCatData.{u, 0}) where
  /-- 支配するガロア対象（普遍被覆側、M24-4a の塔の層）。 -/
  B : D.C.Obj
  /-- B の基点。 -/
  b₀ : D.F.onObj B
  /-- B のガロア性（M21-6/7）。 -/
  hB : D.IsGalois B
  /-- 被支配対象（一般連結対象）。 -/
  X : D.C.Obj
  /-- 支配射 p : B → X。 -/
  p : D.C.Hom B X
  /-- p は F-epi（M213F-5a の共終性ゲート）。 -/
  fepi : ∀ y : D.F.onObj X, ∃ w : D.F.onObj B, D.F.onHom p w = y
  /-- 商の普遍性（X = B/Deck(p) のコエコライザ、正直な限定 (1)）。 -/
  quotient : ∀ (Y : D.C.Obj) (v : D.C.Hom B Y),
    (∀ σ : CatIso D.C B B, D.C.comp σ.hom p = p → D.C.comp σ.hom v = v) →
    ∃ u : D.C.Hom X Y, D.C.comp p u = v

/-- **X 上の充満性（M234F-4b）**: capstone データから、B 上定値塔の
    比較関手が被支配対象 X 上で充満であること（M234F-3）。 -/
theorem ConnectedFullnessData.full {D : GaloisCatData.{u, 0}}
    (data : ConnectedFullnessData D) (Y : D.C.Obj)
    (φ : ActHom
      (GaloisTower.colimHomAction
        (constGaloisTower D data.B data.b₀ data.hB) data.X)
      (GaloisTower.colimHomAction
        (constGaloisTower D data.B data.b₀ data.hB) Y)) :
    ∃ u : D.C.Hom data.X Y,
      (constGaloisTower D data.B data.b₀ data.hB).towerComparison.onHom u
        = φ :=
  constTower_full_connected D data.B data.b₀ data.hB data.X data.p
    data.fepi Y (data.quotient Y) φ

/-- **無矛盾性 witness（M234F-4c）**: 自明群・一点対象・p = id では
    商の普遍性が自明に成立する（deck 条件は空、u = v）ので、一般 X 上
    充満性データが（自明例で）存在する。非自明な X での商の普遍性の
    モデル証明は範囲外（正直な限定 (2)）。 -/
def connectedFullnessWitness_trivial :
    ConnectedFullnessData (gsetGaloisData punitGrp) where
  B := unitAction punitGrp
  b₀ := PUnit.unit
  hB := unitAction_galois
  X := unitAction punitGrp
  p := (gsetGaloisData punitGrp).C.id (unitAction punitGrp)
  fepi := fun y => ⟨y, (gsetGaloisData punitGrp).fmap_id y⟩
  quotient := fun _ v _ =>
    ⟨v, (gsetGaloisData punitGrp).C.id_comp v⟩

/-- **系（M234F-4d）: 一般 X 上充満性データの存在**（無矛盾性）。 -/
theorem connectedFullness_exists_trivial :
    Nonempty (ConnectedFullnessData (gsetGaloisData punitGrp)) :=
  ⟨connectedFullnessWitness_trivial⟩

end IUT

