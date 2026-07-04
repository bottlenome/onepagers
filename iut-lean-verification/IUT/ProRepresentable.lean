/-
  # M213F: pro-表現対象（SGA1 後半）（柱A A-3α・並行部品）

  SGA1 V.4 後半の核心「基本関手 F はガロア対象の逆系で pro-表現される」
  — F(X) ≅ colim_n Hom(A_n, X)（A_n はガロア塔 M24 `GaloisTower`）—
  の骨格を、M189F（ガロア対象による支配 = 余極限の共終性ゲート）と
  M24（塔・π₁ = limitGrp）の上に組み立てる:

  * M213F-1 `towerEval` / `towerEval_transition` — **評価写像
    Hom(A_n, X) → F(X)**: u ↦ F(u)(pt n)。塔の遷移射 P との整合性
    （ev_j (P∘u) = ev_i u、P_pt から）により、評価は塔に沿った
    余極限図式の**錐**をなす
  * M213F-2 `LevelHom` / `germRel` / `colimHom` — **余極限
    colim_n Hom(A_n, X) の実構成**: レベル付き射 (n, u) の型と
    「ある共通レベル k で P∘u = P∘v」という芽（germ）関係、
    その Quot による余極限。choice 不要（Quot は構成的）
  * M213F-3 `towerEval_germRel` / `colimEval` — 評価は芽関係を
    潰す（M213F-1 の整合性）ので余極限から F(X) への写像
    **colimEval : colim_n Hom(A_n, X) → F(X)** が降りる
  * M213F-4 `towerEval_germ` / `colimEval_injective` — **pro-米田
    単射性**: 評価が等しい二つのレベル付き射は共通レベル
    max i j で既に等しい（塔の各層の連結性 + M21-6
    `evaluation_injective`）。よって colimEval は**単射**——
    任意の抽象ガロア圏 D・任意の塔で choice 不要に成立する
    pro-表現の「忠実性の半分」
  * M213F-5 `DominatesFiber` / `colimEval_surjective` — **共終性
    述語**: 塔が X のファイバーの全ての点を基点評価で覆うこと。
    これが成り立てば colimEval は**全射**
  * M213F-6 `proRepresentation_of_dominates` — **主定理（抽象）**:
    塔が X を支配すれば colimEval : colim_n Hom(A_n, X) ≅ F(X) は
    全単射 — **F は X において塔で pro-表現される**
  * M213F-7 `dominatesFiber_of_level_surj` — **ガロア昇格**: どこかの
    層 A_n から X への F-全射が一本あれば支配が従う（A_n のガロア性
    = 自己同型のファイバー推移性で任意の点へ基点を回す）。
    M189F の支配定理の結論（F-全射の存在）を M213F-5 の共終性へ
    翻訳する橋
  * M213F-8 `constGaloisTower` — 任意のガロア対象 + 基点から定値塔を
    作る汎用構成子（M24-4a の全フィールドを id で充足）
  * M213F-9 `proRepresentation_of_domination` — **抽象支配データ ⟹
    pro-表現**: M189F-8 の `AbstractGaloisDominationData D` を持つ
    任意の抽象ガロア圏 D で、任意の連結対象 X はある塔で
    pro-表現される（支配のガロア対象 B を M213F-8 で塔化し
    M213F-6/7 を適用）
  * M213F-10 `closureTower_dominatesFiber` / `connected_proRepresented`
    — **モデル実例での完結**: 任意の群 G のモデル `gsetGaloisData G` で、
    任意の抽象連結対象 E は閉包塔（M160F-5 `closureTower`）で
    pro-表現される。基点は M189F-6 の特徴づけで抽象 Connected から
    取り出す
  * M213F-11 `ProRepresentableData` / `proRepresentableWitness` /
    `proRepresentable_exists` — 総括データ（対象・塔・colimEval の
    全単射性）・モデル証人・存在定理（+ 自明群での無条件存在）

  **意義**: A-3α の本体 — M189F が用意した「十分多くのガロア対象」
  （支配ゲート）と M24 の塔機構（pi1Tower = limitGrp towerSystem）の
  間に残っていた**pro-表現そのもの**が接続された。余極限
  colim_n Hom(A_n, X) が実構成され、単射性（pro-米田）は任意の
  抽象ガロア圏で公理のみから、全射性は支配（共終性）から従う形に
  分解された。これは SGA1 後半「C ≃ π₁-Set」の関手 X ↦ F(X) が
  pro-対象 (A_n) で表現される、という主張のファイバー側の完全な骨格
  である。

  **正直な限定**: (1) 本モジュールはスライス A（支配からの共終塔 +
  対象ごとの pro-表現）である。pro-表現は**対象 X ごと**
  （X を支配する塔に対して）であり、**単一の塔が圏の全対象を同時に
  支配する**（真の共終塔 = pro-表現対象の一意存在）ことは未達成 —
  Nat 添字の塔で全対象を覆うには対象の可算枚挙（または有向極限の
  一般添字）が要り、現行の `GaloisTower`（Nat 鎖）の範囲外。
  (2) colimEval の全単射性から圏同値 C ≃ pi1Tower-Set（F(X) 上の
  pi1Tower 作用の構成と充満忠実性・本質的全射性の束ね）へ進む段も
  残余（A-3β）。(3) 連結でない X への拡張（軌道分解ごとの支配）は
  範囲外 — 定値塔は複数軌道を同時に覆えない。(4) M213F-1〜8 は任意の
  抽象 D でパラメトリックかつ choice の新規使用ゼロ。M213F-9 は
  `AbstractGaloisDominationData`（仮定）経由でやはり新規 choice ゼロ。
  M213F-10/11 は型が `gsetGaloisData G`（M21-8、G6 フィールドに
  Classical.choice）に言及するため公理リストに Classical.choice を
  **型経由で継承**する（M160F/M189F と同じ事情、本モジュールでの
  新規使用はゼロ）。

  全て選択公理不使用（型継承を除く）。サブエージェント並行部品。
-/
import IUT.AbstractGaloisDomination

namespace IUT

universe u

namespace GaloisTower

variable {D : GaloisCatData.{u, 0}} (T : GaloisTower D)

/-! ## M213F-1: 評価写像 Hom(A_n, X) → F(X) とその遷移整合性 -/

/-- **評価写像（M213F-1a）**: レベル n の射 u : A_n → X を塔の基点
    pt n で評価する ev_n(u) = F(u)(pt n)。pro-表現
    F(X) ≅ colim_n Hom(A_n, X) の候補写像の各レベル成分。 -/
def towerEval (X : D.C.Obj) (n : Nat) (u : D.C.Hom (T.A n) X) :
    D.F.onObj X :=
  D.F.onHom u (T.pt n)

/-- **評価の遷移整合性（M213F-1b）**: i ≤ j のとき、u : A_i → X を
    遷移射 P : A_j → A_i で引き戻しても評価値は変わらない
    （P_pt: 遷移は基点を保つ）。評価たちが余極限図式の錐をなす
    ことの内容。 -/
theorem towerEval_transition (X : D.C.Obj) {i j : Nat} (h : i ≤ j)
    (u : D.C.Hom (T.A i) X) :
    T.towerEval X j (D.C.comp (T.P h) u) = T.towerEval X i u := by
  show D.F.onHom (D.C.comp (T.P h) u) (T.pt j) = D.F.onHom u (T.pt i)
  rw [D.fmap_comp, T.P_pt h]

/-! ## M213F-2: 余極限 colim_n Hom(A_n, X) の実構成（Quot） -/

/-- **レベル付き射（M213F-2a）**: 余極限の生成元 — レベル n と
    射 A_n → X の組。 -/
structure LevelHom {D : GaloisCatData.{u, 0}} (T : GaloisTower D)
    (X : D.C.Obj) : Type where
  lvl : Nat
  hom : D.C.Hom (T.A lvl) X

/-- **芽関係（M213F-2b）**: 二つのレベル付き射が、ある共通レベル k へ
    遷移射で引き戻すと一致すること。有向余極限の標準的な同一視
    （filtered colimit の germ 関係）。 -/
def germRel (X : D.C.Obj) (p q : LevelHom T X) : Prop :=
  ∃ (k : Nat) (hp : p.lvl ≤ k) (hq : q.lvl ≤ k),
    D.C.comp (T.P hp) p.hom = D.C.comp (T.P hq) q.hom

/-- **余極限 colim_n Hom(A_n, X)**（M213F-2c）: 芽関係による商。
    Quot による構成なので choice 不要。 -/
def colimHom (X : D.C.Obj) : Type := Quot (T.germRel X)

/-! ## M213F-3: 評価は余極限に降りる -/

/-- **補題（M213F-3a）: 評価は芽関係を潰す** — 共通レベルで一致する
    二つのレベル付き射は同じ評価値を持つ（M213F-1b を両側に適用）。 -/
theorem towerEval_germRel (X : D.C.Obj) (p q : LevelHom T X)
    (h : T.germRel X p q) :
    T.towerEval X p.lvl p.hom = T.towerEval X q.lvl q.hom := by
  obtain ⟨k, hp, hq, heq⟩ := h
  rw [← T.towerEval_transition X hp p.hom, heq,
    T.towerEval_transition X hq q.hom]

/-- **余極限からの評価写像（M213F-3b）**:
    colimEval : colim_n Hom(A_n, X) → F(X)。pro-表現の比較写像の
    本体（Quot.lift、choice 不要）。 -/
def colimEval (X : D.C.Obj) : T.colimHom X → D.F.onObj X :=
  Quot.lift (fun p => T.towerEval X p.lvl p.hom)
    (fun p q h => T.towerEval_germRel X p q h)

/-! ## M213F-4: pro-米田単射性（公理のみ・任意の塔で成立） -/

/-- **補題（M213F-4a): 評価が等しければ芽が等しい** — ev_i(u) =
    ev_j(v) なら共通レベル max i j への引き戻しが既に等しい。
    max レベルの層 A_k はガロアゆえ連結であり、二つの引き戻しは
    基点 pt k で同じ値を取るから evaluation 単射性（M21-6）で一致。
    choice の新規使用ゼロ。 -/
theorem towerEval_germ (X : D.C.Obj) (p q : LevelHom T X)
    (h : T.towerEval X p.lvl p.hom = T.towerEval X q.lvl q.hom) :
    T.germRel X p q := by
  refine ⟨max p.lvl q.lvl, Nat.le_max_left p.lvl q.lvl,
    Nat.le_max_right p.lvl q.lvl, ?_⟩
  apply D.evaluation_injective (T.hGal (max p.lvl q.lvl)).1
    (T.pt (max p.lvl q.lvl))
  show T.towerEval X (max p.lvl q.lvl)
      (D.C.comp (T.P (Nat.le_max_left p.lvl q.lvl)) p.hom)
    = T.towerEval X (max p.lvl q.lvl)
      (D.C.comp (T.P (Nat.le_max_right p.lvl q.lvl)) q.hom)
  rw [T.towerEval_transition X (Nat.le_max_left p.lvl q.lvl) p.hom,
    T.towerEval_transition X (Nat.le_max_right p.lvl q.lvl) q.hom]
  exact h

/-- **定理（M213F-4b）: colimEval は単射**（pro-米田の忠実半分）—
    任意の抽象ガロア圏・任意のガロア塔・任意の対象 X で、公理のみ
    から成立する。 -/
theorem colimEval_injective (X : D.C.Obj) :
    ∀ p q : T.colimHom X, T.colimEval X p = T.colimEval X q → p = q := by
  refine Quot.ind ?_
  intro a
  refine Quot.ind ?_
  intro b h
  exact Quot.sound (T.towerEval_germ X a b h)

/-! ## M213F-5: 共終性述語と全射性 -/

/-- **共終性（塔による X の支配、M213F-5a）**: F(X) の全ての点が
    どこかのレベルの基点評価で覆われること。pro-表現可能性の
    ゲート条件（M189F の支配ステートメントの塔語彙版）。 -/
def DominatesFiber (X : D.C.Obj) : Prop :=
  ∀ x : D.F.onObj X, ∃ (n : Nat) (u : D.C.Hom (T.A n) X),
    T.towerEval X n u = x

/-- **定理（M213F-5b）: 支配があれば colimEval は全射**。 -/
theorem colimEval_surjective (X : D.C.Obj) (hdom : T.DominatesFiber X) :
    ∀ x : D.F.onObj X, ∃ p : T.colimHom X, T.colimEval X p = x := by
  intro x
  obtain ⟨n, u, hu⟩ := hdom x
  exact ⟨Quot.mk (T.germRel X) ⟨n, u⟩, hu⟩

/-! ## M213F-6: 主定理（抽象）— 支配 ⟹ pro-表現 -/

/-- **主定理（M213F-6）: 塔が X を支配すれば F は X において
    pro-表現される** — colimEval : colim_n Hom(A_n, X) → F(X) は
    全単射（単射 = M213F-4b は無条件、全射 = M213F-5b は支配から）。
    SGA1 の「F ≅ colim Hom(A_i, −)」の対象ごとの形。 -/
theorem proRepresentation_of_dominates (X : D.C.Obj)
    (hdom : T.DominatesFiber X) :
    (∀ p q : T.colimHom X, T.colimEval X p = T.colimEval X q → p = q) ∧
    (∀ x : D.F.onObj X, ∃ p : T.colimHom X, T.colimEval X p = x) :=
  ⟨fun p q h => T.colimEval_injective X p q h,
    T.colimEval_surjective X hdom⟩

/-! ## M213F-7: ガロア昇格 — 一本の F-全射から支配へ -/

/-- **補題（M213F-7）: どこかの層からの F-全射一本で支配が従う** —
    φ : A_n → X が F-全射なら、任意の x ∈ F(X) に対し φ の原像 w を
    取り、A_n のガロア性（自己同型のファイバー推移性）で基点 pt n を
    w へ運ぶ自己同型 σ を得て、u = σ；φ が ev_n(u) = x を満たす。
    M189F の支配定理の結論（∃ ガロア対象 + F-全射）を共終性
    （M213F-5a）へ翻訳する橋。choice の新規使用ゼロ。 -/
theorem dominatesFiber_of_level_surj (X : D.C.Obj) (n : Nat)
    (φ : D.C.Hom (T.A n) X)
    (hφ : ∀ y : D.F.onObj X, ∃ w : D.F.onObj (T.A n), D.F.onHom φ w = y) :
    T.DominatesFiber X := by
  intro x
  obtain ⟨w, hw⟩ := hφ x
  obtain ⟨σ, _, hσ⟩ := (T.hGal n).2 (T.pt n) w
  refine ⟨n, D.C.comp σ φ, ?_⟩
  show D.F.onHom (D.C.comp σ φ) (T.pt n) = x
  rw [D.fmap_comp, hσ, hw]

end GaloisTower

/-! ## M213F-8: 定値塔の汎用構成子 -/

/-- **定値塔（M213F-8）**: 任意のガロア対象 B と基点 b₀ から、全ての
    層が B・全ての遷移が恒等射の `GaloisTower`（M24-4a）を作る。
    M189F の支配が与える単一のガロア対象を M24 の塔機構
    （towerSystem / pi1Tower）へ入力するための最小の塔化。 -/
def constGaloisTower (D : GaloisCatData.{u, 0}) (B : D.C.Obj)
    (b₀ : D.F.onObj B) (hB : D.IsGalois B) : GaloisTower D where
  A := fun _ => B
  pt := fun _ => b₀
  hGal := fun _ => hB
  P := fun _ => D.C.id B
  P_self := fun _ _ => rfl
  P_comp := fun _ _ => D.C.id_comp _
  P_pt := fun _ => D.fmap_id b₀

/-! ## M213F-9: 抽象支配データ ⟹ pro-表現（任意の抽象ガロア圏） -/

/-- **定理（M213F-9）: 支配データを持つ任意の抽象ガロア圏で、任意の
    連結対象は pro-表現される** — M189F-8 の
    `AbstractGaloisDominationData D`（十分多くのガロア対象）から、
    連結な X を支配するガロア対象 B を取り、定値塔（M213F-8）に
    ガロア昇格（M213F-7）と主定理（M213F-6）を適用する。
    仮定・結論とも純抽象語彙であり choice の新規使用ゼロ。 -/
theorem proRepresentation_of_domination (D : GaloisCatData.{u, 0})
    (hdom : AbstractGaloisDominationData D) (X : D.C.Obj)
    (hX : D.Connected X) :
    ∃ T : GaloisTower D,
      (∀ p q : T.colimHom X, T.colimEval X p = T.colimEval X q → p = q) ∧
      (∀ x : D.F.onObj X, ∃ p : T.colimHom X, T.colimEval X p = x) := by
  obtain ⟨B, hB, φ, hφ⟩ := hdom.dominates X hX
  obtain ⟨b₀⟩ := hB.1.1
  refine ⟨constGaloisTower D B b₀ hB, ?_⟩
  exact GaloisTower.proRepresentation_of_dominates _ X
    (GaloisTower.dominatesFiber_of_level_surj _ X 0 φ hφ)

/-! ## M213F-10: モデル実例 — 閉包塔は連結対象を pro-表現する -/

/-- **補題（M213F-10a）: 閉包塔は E のファイバーを支配する** —
    M160F-5 の閉包塔の各層 G/core(Stab e₀) から E への F-全射
    （`closureTower_dominates`）にガロア昇格（M213F-7）を適用。 -/
theorem closureTower_dominatesFiber (G : Grp) (E : GAction G)
    (e₀ : E.carrier) (htrans : E.Transitive) :
    (closureTower G E e₀).DominatesFiber E := by
  refine GaloisTower.dominatesFiber_of_level_surj (closureTower G E e₀) E 0
    (closureHom G E e₀) ?_
  intro y
  exact closureHom_surjective G E e₀ htrans y

/-- **定理（M213F-10b）: モデルの任意の連結対象は pro-表現される** —
    任意の群 G のモデル `gsetGaloisData G` で、抽象 Connected な E は
    閉包塔により pro-表現される: colimEval : colim_n Hom(A_n, E) ≅ F(E)。
    基点は連結性の第一成分から、推移性は M189F-5b の特徴づけから
    取り出す。A-3α「pro-表現対象の組み立て」のモデル側完結。 -/
theorem connected_proRepresented (G : Grp) (E : GAction G)
    (hE : (gsetGaloisData G).Connected E) :
    ∃ T : GaloisTower (gsetGaloisData G),
      (∀ p q : T.colimHom E, T.colimEval E p = T.colimEval E q → p = q) ∧
      (∀ x : (gsetGaloisData G).F.onObj E,
        ∃ p : T.colimHom E, T.colimEval E p = x) := by
  obtain ⟨e₀⟩ := hE.1
  refine ⟨closureTower G E e₀, ?_⟩
  exact GaloisTower.proRepresentation_of_dominates (closureTower G E e₀) E
    (closureTower_dominatesFiber G E e₀ (abstract_connected_transitive G hE))

/-! ## M213F-11: 総括 -/

/-- **総括データ（M213F-11a）**: pro-表現の証人 — 対象 X・ガロア塔 T・
    比較写像 colimEval : colim_n Hom(A_n, X) → F(X) の全単射性。 -/
structure ProRepresentableData (D : GaloisCatData.{u, 0}) where
  /-- pro-表現される対象。 -/
  X : D.C.Obj
  /-- 表現するガロア塔（pro-対象、M24-4a）。 -/
  T : GaloisTower D
  /-- 比較写像の単射性（pro-米田、M213F-4b）。 -/
  eval_inj : ∀ p q : GaloisTower.colimHom T X,
    GaloisTower.colimEval T X p = GaloisTower.colimEval T X q → p = q
  /-- 比較写像の全射性（共終性、M213F-5b）。 -/
  eval_surj : ∀ x : D.F.onObj X,
    ∃ p : GaloisTower.colimHom T X, GaloisTower.colimEval T X p = x

/-- **証人（M213F-11b）**: 任意の群 G と基点付き推移的 E に対し、
    閉包塔が E の pro-表現データを与える。 -/
def proRepresentableWitness (G : Grp) (E : GAction G) (e₀ : E.carrier)
    (htrans : E.Transitive) :
    ProRepresentableData (gsetGaloisData G) where
  X := E
  T := closureTower G E e₀
  eval_inj := fun p q h =>
    GaloisTower.colimEval_injective (closureTower G E e₀) E p q h
  eval_surj := GaloisTower.colimEval_surjective (closureTower G E e₀) E
    (closureTower_dominatesFiber G E e₀ htrans)

/-- **定理（M213F-11c）: pro-表現データの存在** — 任意の群の任意の
    基点付き推移的作用（= モデルの連結対象）に対して。 -/
theorem proRepresentable_exists (G : Grp) (E : GAction G) (e₀ : E.carrier)
    (htrans : E.Transitive) :
    Nonempty (ProRepresentableData (gsetGaloisData G)) :=
  ⟨proRepresentableWitness G E e₀ htrans⟩

/-- **系（M213F-11d）: 無条件の存在**（無矛盾性）— 自明群の一点作用で。 -/
theorem proRepresentable_exists_trivial :
    Nonempty (ProRepresentableData (gsetGaloisData punitGrp)) :=
  ⟨proRepresentableWitness punitGrp (unitAction punitGrp) PUnit.unit
    (fun _ _ => ⟨PUnit.unit, rfl⟩)⟩

end IUT

