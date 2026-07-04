/-
  # M221F: 比較関手の充満性（Galois 圏同値の完成へ）（柱A A-3α・並行部品）

  M217F は比較関手 towerComparison : C → pi1Tower-Set の実構成・
  忠実性（支配対象上）・自然性・対象ごとの全単射性・本質的全射性の
  レベル橋を完成したが、**充満性**（任意の π₁-同変写像
  colimHom X → colimHom Y が C の射 X → Y の後合成から来ること）は
  正直な限定として残っていた。本モジュールはその充満性を
  **到達可能なスライス**で証明する:

  * M221F-1 `OrbitGenerated` — **π₁ 軌道生成述語**: 余極限
    colim_n Hom(A_n, X) が一つの類 c₀ の π₁ 軌道で尽くされること
    （充満性復元の「推移性」ゲート条件）
  * M221F-2 `towerComparison_onHom_eq_of_orbit` — **充満性判定基準**:
    π₁-同変写像 φ が一点 c₀ で後合成 colimPush u と一致し、c₀ の
    軌道が全体を生成すれば、towerComparison.onHom u = φ（同変性で
    一致が軌道全体へ伝播する。choice 不要の核心補題）
  * M221F-3 `towerComparison_full_of_orbit` — **条件付き充満性**:
    軌道生成 + 一点実現可能性（∃ u, colimPush u c₀ = φ c₀）から
    ∃ u, onHom u = φ。任意の塔・任意の対象で成立する充満性の
    条件付き一般形
  * M221F-4 `constBaseClass` / `constTower_class_eq` — 定値塔
    （M213F-8）の余極限の**レベル潰し**: 遷移が恒等なので同じ射の
    類はレベルに依らない。基点類は id_B の類
  * M221F-5 `constTower_transAut_const` / `constPi1` — 定値塔の
    π₁ 元の実構成: 任意の自己同型 ι ∈ Aut(B) の定値族は整合的
    （transAut の一意性 M24-1 から transAut ι = ι）
  * M221F-6 `constTower_orbitGenerated` / `constTower_realizable` —
    判定基準の両仮定の充足（定値塔・対象 B 上）: **B の全ての自己射が
    自己同型に持ち上がるなら**基点類の軌道は全体を生成し、
    一点実現可能性は表現元の抽出（Quot.ind、choice 不要）で常に成立
  * M221F-7 `constTower_full` / `constTower_dominatesFiber_self` /
    `constTower_faithful` — **主定理（抽象・条件付き）**: 自己射 ⟹
    自己同型の仮定の下、定値塔の比較関手はガロア対象 B 上**充満**、
    かつ（id_B の F-全射性による自己支配から）**忠実** — B 上
    Hom(B, Y) ≅ Hom_{π₁-Set}(colimHom B, colimHom Y)
  * M221F-8 `regAction_transitive` / `regAction_galois` /
    `regAction_endo_iso` / `regTower` / `towerComparison_full_regular` /
    `towerComparison_regular_fully_faithful` — **モデルでの無条件化**:
    任意の群 G の正則作用 G_reg はモデル `gsetGaloisData G` のガロア
    対象であり（M14-2 右移動の全単射性）、その同変自己射は全て右移動
    = 自己同型（M14-1）。よって正則対象上、比較関手は**無条件に
    充満かつ忠実**である（SGA1 の「普遍被覆上の充満忠実性」のモデル版）
  * M221F-9 capstone: `GaloisFullnessData` / `galoisFullnessWitness` /
    `galoisFullness_exists`（+ 自明群での無条件存在）と、M217F の
    同値骨格データとの束ね `GaloisEquivalenceFullData` /
    `galoisEquivalenceFullWitness` / `galoisEquivalenceFull_exists` —
    忠実性・単射性・全射性（M217F-13）**+ 充満性（本モジュール）**を
    同一の塔で持つ総括データの存在

  **意義**: A-3α の最後の欠片 — M217F が「忠実 + 自然 + 対象ごとの
  全単射 + 本質的全射のレベル橋」まで到達した比較関手に、初めて
  **充満性**が加わった。充満性の論理構造が「軌道生成（π₁ 作用の
  推移性）+ 一点実現可能性」に分解され（M221F-2/3、任意の塔で成立）、
  ガロア対象自身の上では両者が「自己射 ⟹ 自己同型」一つに帰着する
  こと（M221F-7）、そしてモデルの正則対象では無条件に成立すること
  （M221F-8）が確立した。これは SGA1 主定理の充満忠実性の
  「普遍被覆（pro-表現対象）上の germ」であり、M20-9 のモデル圏同値と
  M217F の抽象骨格を繋ぐ最初の充満性の実証明である。

  **正直な限定**: (1) 本モジュールは**条件付き + ガロア対象上 +
  モデル無条件**のスライスである。無条件の充満性は (i) 一般対象 X 上
  （条件: 軌道生成 M221F-1 + 一点実現可能性）、(ii) ガロア対象 B 上
  （条件: 自己射 ⟹ 自己同型。有限ファイバーの真のガロア圏では定理だが
  `GaloisCatData` はファイバーの有限性を課さないため公理からは
  導出不能）に条件が残る。モデルでは正則対象 G_reg 上でのみ無条件
  （一般の連結対象 X への拡張は F-全射 A_n → X に沿った降下 =
  商の普遍性を要し未達成）。(2) 塔は定値塔に限る（真の共終塔・
  一般の塔での軌道生成は逆極限の全射性 = 有限性/コンパクト性を要し
  M213F/M217F と同じく未達成）。(3) 充満性 + 忠実性が揃っても
  真の圏同値（擬逆関手・単位・余単位）の束ねは残余（A-3β）。
  (4) 公理フットプリント（`#print axioms` 実測）: π₁ に触れる全定理は
  M24 `transAut`（∃! の関数化）由来の Classical.choice を**継承**
  （M217F と同じく不可避）。モデル定理（M221F-8/9）はさらに
  `gsetGaloisData` の G6 由来の choice も型経由で継承。
  `constTower_class_eq` / `constTower_realizable` 等の商操作は
  Quot.sound（+ propext）。本モジュールの**証明体での新規 choice
  使用はゼロ**（表現元の抽出は Quot.ind、逆写像の構成は右移動の
  明示逆で回避）。

  全て選択公理の新規使用なし（M24/M21-8 からの継承を除く）。
  サブエージェント並行部品。
-/
import IUT.GaloisEquivalence

namespace IUT

universe u

namespace GaloisTower

variable {D : GaloisCatData.{u, 0}} (T : GaloisTower D)

/-! ## M221F-1: π₁ 軌道生成述語 -/

/-- **π₁ 軌道生成（M221F-1）**: 余極限 colim_n Hom(A_n, X) の全ての類が
    基点類 c₀ の π₁ 軌道に入ること。充満性復元の「推移性」ゲート条件
    （SGA1 では pro-表現対象のファイバーへの π₁ 作用の推移性に相当）。 -/
def OrbitGenerated (X : D.C.Obj) (c₀ : T.colimHom X) : Prop :=
  ∀ c : T.colimHom X, ∃ σ : T.pi1Tower.carrier, T.colimAct X σ c₀ = c

/-! ## M221F-2: 充満性判定基準 — 一点の一致が軌道全体へ伝播する -/

/-- **定理（M221F-2）: 充満性判定基準** — π₁-同変写像 φ :
    colimHom X → colimHom Y が基点類 c₀ で後合成 colimPush u と一致し
    （hu）、c₀ の軌道が全体を生成すれば（horb）、関手の像として
    towerComparison.onHom u = φ が成り立つ。証明は同変性の伝播:
    φ(σ·c₀) = σ·φ(c₀) = σ·(u 後合成 c₀) = u 後合成 (σ·c₀)
    （M217F-5d colimPush_act）。choice の新規使用ゼロ。 -/
theorem towerComparison_onHom_eq_of_orbit {X Y : D.C.Obj}
    (φ : ActHom (T.colimHomAction X) (T.colimHomAction Y))
    (c₀ : T.colimHom X) (horb : T.OrbitGenerated X c₀)
    (u : D.C.Hom X Y) (hu : T.colimPush u c₀ = φ.map c₀) :
    T.towerComparison.onHom u = φ := by
  apply ActHom.ext
  intro c
  obtain ⟨σ, hσ⟩ := horb c
  show T.colimPush u c = φ.map c
  rw [← hσ, T.colimPush_act u σ c₀, hu]
  exact (φ.equivariant σ c₀).symm

/-! ## M221F-3: 条件付き充満性（任意の塔・任意の対象） -/

/-- **定理（M221F-3）: 条件付き充満性** — 軌道生成 + 一点実現可能性
    （φ の基点値が何らかの C 射の後合成で書けること）から充満性
    ∃ u, towerComparison.onHom u = φ が従う。充満性の論理構造の分解:
    残る実質は二つの仮定の充足のみ（M221F-6/8 で定値塔・モデルに
    対して充足する）。 -/
theorem towerComparison_full_of_orbit {X Y : D.C.Obj}
    (φ : ActHom (T.colimHomAction X) (T.colimHomAction Y))
    (c₀ : T.colimHom X) (horb : T.OrbitGenerated X c₀)
    (hreal : ∃ u : D.C.Hom X Y, T.colimPush u c₀ = φ.map c₀) :
    ∃ u : D.C.Hom X Y, T.towerComparison.onHom u = φ := by
  obtain ⟨u, hu⟩ := hreal
  exact ⟨u, T.towerComparison_onHom_eq_of_orbit φ c₀ horb u hu⟩

end GaloisTower

/-! ## M221F-4: 定値塔の基点類とレベル潰し -/

section ConstTower

variable (D : GaloisCatData.{u, 0}) (B : D.C.Obj) (b₀ : D.F.onObj B)
  (hB : D.IsGalois B)

/-- **基点類（M221F-4a）**: 定値塔（M213F-8）上の恒等射 id_B の類。
    充満性復元の基点（SGA1 の「普遍被覆の標準点」に相当）。 -/
def constBaseClass :
    GaloisTower.colimHom (constGaloisTower D B b₀ hB) B :=
  GaloisTower.levelInclusion (constGaloisTower D B b₀ hB) B 0 (D.C.id B)

/-- **レベル潰し（M221F-4b）**: 定値塔では遷移が恒等射なので、同じ射
    w : B → X はどのレベルでも同じ類を定める（germRel の直接検証、
    Quot.sound のみ）。 -/
theorem constTower_class_eq (X : D.C.Obj) (m k : Nat) (w : D.C.Hom B X) :
    Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) X) ⟨m, w⟩
      = Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) X)
        ⟨k, w⟩ := by
  refine Quot.sound
    ⟨max m k, Nat.le_max_left m k, Nat.le_max_right m k, ?_⟩
  show D.C.comp (D.C.id B) w = D.C.comp (D.C.id B) w
  exact rfl

/-! ## M221F-5: 定値塔の π₁ 元（定値整合族） -/

/-- **遷移の定値性（M221F-5a）**: 定値塔の遷移 transAut は恒等写像で
    ある — 遷移射が id_B なので候補条件 id；ι = ι；id が自明に成立し、
    M24-1 の一意性（transAut_unique）から transAut ι = ι。 -/
theorem constTower_transAut_const {i j : Nat} (h : i ≤ j)
    (ι : CatIso D.C B B) :
    (constGaloisTower D B b₀ hB).transAut h ι = ι := by
  refine ((constGaloisTower D B b₀ hB).transAut_unique h ι ι ?_).symm
  show D.C.comp (D.C.id B) ι.hom = D.C.comp ι.hom (D.C.id B)
  rw [D.C.id_comp, D.C.comp_id]

/-- **定値 π₁ 元（M221F-5b）**: 自己同型 ι ∈ Aut(B) の定値族は
    整合的（M221F-5a）なので pi1Tower の元をなす。定値塔の
    π₁ ≅ Aut(B) の「⊇」側の実構成。 -/
noncomputable def constPi1 (ι : CatIso D.C B B) :
    (constGaloisTower D B b₀ hB).pi1Tower.carrier :=
  ⟨fun _ => ι, by
    intro i j h
    exact constTower_transAut_const D B b₀ hB h ι⟩

/-! ## M221F-6: 判定基準の両仮定の充足（定値塔・ガロア対象 B 上） -/

/-- **定理（M221F-6a）: 軌道生成の充足** — B の全ての自己射が自己同型
    に持ち上がるなら（hendo）、基点類 id_B の π₁ 軌道は
    colim_n Hom(A_n, B) の全体を生成する: 類 (n, w) に対し w を
    自己同型 ι に持ち上げ、定値 π₁ 元（M221F-5b）の作用
    ι·id_B = ι = w とレベル潰し（M221F-4b）で到達する。 -/
theorem constTower_orbitGenerated
    (hendo : ∀ w : D.C.Hom B B, ∃ ι : CatIso D.C B B, ι.hom = w) :
    GaloisTower.OrbitGenerated (constGaloisTower D B b₀ hB) B
      (constBaseClass D B b₀ hB) := by
  refine Quot.ind
    (β := fun q => ∃ σ : (constGaloisTower D B b₀ hB).pi1Tower.carrier,
      (constGaloisTower D B b₀ hB).colimAct B σ
        (constBaseClass D B b₀ hB) = q) ?_
  intro p
  obtain ⟨n, w⟩ := p
  obtain ⟨ι, hι⟩ := hendo w
  refine ⟨constPi1 D B b₀ hB ι, ?_⟩
  show Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) B)
      ⟨0, D.C.comp ι.hom (D.C.id B)⟩
    = Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) B) ⟨n, w⟩
  refine Eq.trans
    (congrArg
      (Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) B)) ?_)
    (constTower_class_eq D B b₀ hB B 0 n w)
  rw [D.C.comp_id, hι]

/-- **定理（M221F-6b）: 一点実現可能性の充足** — 定値塔では φ の
    基点値の任意の表現元 (n, v) がそのまま実現子になる:
    colimPush v (id_B の類) = (v の類) はレベル潰しで φ(c₀) に一致。
    表現元の抽出は Quot.ind（choice 不要）。 -/
theorem constTower_realizable (Y : D.C.Obj)
    (φ : ActHom
      (GaloisTower.colimHomAction (constGaloisTower D B b₀ hB) B)
      (GaloisTower.colimHomAction (constGaloisTower D B b₀ hB) Y)) :
    ∃ u : D.C.Hom B Y,
      (constGaloisTower D B b₀ hB).colimPush u (constBaseClass D B b₀ hB)
        = φ.map (constBaseClass D B b₀ hB) := by
  refine Quot.ind
    (β := fun q => q = φ.map (constBaseClass D B b₀ hB) →
      ∃ u : D.C.Hom B Y,
        (constGaloisTower D B b₀ hB).colimPush u
          (constBaseClass D B b₀ hB)
          = φ.map (constBaseClass D B b₀ hB)) ?_
    (φ.map (constBaseClass D B b₀ hB)) rfl
  intro p hp
  obtain ⟨n, v⟩ := p
  refine ⟨v, ?_⟩
  rw [← hp]
  show Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) Y)
      ⟨0, D.C.comp (D.C.id B) v⟩
    = Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) Y) ⟨n, v⟩
  refine Eq.trans
    (congrArg
      (Quot.mk (GaloisTower.germRel (constGaloisTower D B b₀ hB) Y)) ?_)
    (constTower_class_eq D B b₀ hB Y 0 n v)
  exact congrArg
    (fun t => (⟨0, t⟩ :
      GaloisTower.LevelHom (constGaloisTower D B b₀ hB) Y))
    (D.C.id_comp (X := B) (Y := Y) v)

/-! ## M221F-7: 主定理（抽象・条件付き）— ガロア対象上の充満忠実性 -/

/-- **主定理（M221F-7a）: 定値塔の比較関手はガロア対象 B 上で充満**
    （自己射 ⟹ 自己同型の条件付き）— M221F-3 の二仮定を M221F-6a/6b で
    充足する。任意の π₁-同変写像 colimHom B → colimHom Y は
    C の射 B → Y の後合成である。 -/
theorem constTower_full
    (hendo : ∀ w : D.C.Hom B B, ∃ ι : CatIso D.C B B, ι.hom = w)
    (Y : D.C.Obj)
    (φ : ActHom
      (GaloisTower.colimHomAction (constGaloisTower D B b₀ hB) B)
      (GaloisTower.colimHomAction (constGaloisTower D B b₀ hB) Y)) :
    ∃ u : D.C.Hom B Y,
      (constGaloisTower D B b₀ hB).towerComparison.onHom u = φ :=
  GaloisTower.towerComparison_full_of_orbit (constGaloisTower D B b₀ hB)
    φ (constBaseClass D B b₀ hB)
    (constTower_orbitGenerated D B b₀ hB hendo)
    (constTower_realizable D B b₀ hB Y φ)

/-- **自己支配（M221F-7b）**: 定値塔は自身の層 B を支配する
    （id_B は F-全射。M213F-7 のガロア昇格）。 -/
theorem constTower_dominatesFiber_self :
    (constGaloisTower D B b₀ hB).DominatesFiber B := by
  refine GaloisTower.dominatesFiber_of_level_surj
    (constGaloisTower D B b₀ hB) B 0 (D.C.id B) ?_
  intro y
  exact ⟨y, D.fmap_id y⟩

/-- **系（M221F-7c）: B 上の忠実性** — 自己支配（M221F-7b）と
    M217F-9 から、定値塔の比較関手は B 上忠実。M221F-7a と併せ、
    ガロア対象上で Hom(B, Y) ≅ Hom_{π₁-Set}(colimHom B, colimHom Y)
    （充満忠実性）が成立する。 -/
theorem constTower_faithful (Y : D.C.Obj) (f g : D.C.Hom B Y)
    (h : (constGaloisTower D B b₀ hB).towerComparison.onHom f
      = (constGaloisTower D B b₀ hB).towerComparison.onHom g) : f = g :=
  GaloisTower.towerComparison_faithful (constGaloisTower D B b₀ hB)
    (constTower_dominatesFiber_self D B b₀ hB) f g h

end ConstTower

/-! ## M221F-8: モデルでの無条件化 — 正則対象上の充満忠実性 -/

/-- **正則作用の推移性（M221F-8a）**: G の左移動は推移的
    （g := y·x⁻¹ で x ↦ y）。 -/
theorem regAction_transitive (G : Grp) : (regAction G).Transitive := by
  intro x y
  refine ⟨G.mul y (G.inv x), ?_⟩
  show G.mul (G.mul y (G.inv x)) x = y
  rw [G.mul_assoc, G.inv_mul, G.mul_one]

/-- **定理（M221F-8b）: 正則作用はモデルのガロア対象** — 連結性は
    基点 1 + 推移性から（M189F-6a）、自己同型のファイバー推移性は
    右移動 x ↦ x·(a⁻¹b)（M14-2: 明示逆 x ↦ x·(a⁻¹b)⁻¹ を持つ同変
    同型）が a を b へ運ぶことから。choice の新規使用ゼロ。 -/
theorem regAction_galois (G : Grp) :
    (gsetGaloisData G).IsGalois (regAction G) := by
  refine ⟨transitive_abstract_connected G G.one (regAction_transitive G),
    ?_⟩
  intro a b
  refine ⟨rightMul G (G.mul (G.inv a) b),
    ⟨rightMul G (G.inv (G.mul (G.inv a) b)), ?_, ?_⟩, ?_⟩
  · apply ActHom.ext
    intro x
    show G.mul (G.mul x (G.mul (G.inv a) b))
        (G.inv (G.mul (G.inv a) b)) = x
    rw [G.mul_assoc, G.mul_inv, G.mul_one]
  · apply ActHom.ext
    intro x
    show G.mul (G.mul x (G.inv (G.mul (G.inv a) b)))
        (G.mul (G.inv a) b) = x
    rw [G.mul_assoc, G.inv_mul, G.mul_one]
  · show G.mul a (G.mul (G.inv a) b) = b
    rw [← G.mul_assoc, G.mul_inv, G.one_mul]

/-- **定理（M221F-8c）: 正則作用の自己射は自己同型に持ち上がる** —
    M14-1（同変自己写像は右移動 x ↦ x·w(1)）により、逆は右移動
    x ↦ x·w(1)⁻¹ で明示構成できる（choice 不要）。M221F-7a の
    条件 hendo のモデルでの無条件充足。 -/
theorem regAction_endo_iso (G : Grp)
    (w : (gsetGaloisData G).C.Hom (regAction G) (regAction G)) :
    ∃ ι : CatIso (gsetGaloisData G).C (regAction G) (regAction G),
      ι.hom = w := by
  refine ⟨⟨w, rightMul G (G.inv (w.map G.one)), ?_, ?_⟩, rfl⟩
  · apply ActHom.ext
    intro x
    show G.mul (w.map x) (G.inv (w.map G.one)) = x
    rw [equivariant_is_right_mul G w x, G.mul_assoc, G.mul_inv,
      G.mul_one]
  · apply ActHom.ext
    intro x
    show w.map (G.mul x (G.inv (w.map G.one))) = x
    rw [equivariant_is_right_mul G w (G.mul x (G.inv (w.map G.one))),
      G.mul_assoc, G.inv_mul, G.mul_one]

/-- **正則塔（M221F-8d）**: 正則作用 G_reg 上の定値ガロア塔
    （基点 1）。SGA1 の「普遍被覆の pro-対象」のモデル実例。 -/
def regTower (G : Grp) : GaloisTower (gsetGaloisData G) :=
  constGaloisTower (gsetGaloisData G) (regAction G) G.one
    (regAction_galois G)

/-- **定理（M221F-8e）: 正則対象上の無条件充満性（モデル）** —
    任意の群 G・任意の対象 Y に対し、正則塔の比較関手は
    G_reg 上充満: 任意の π₁-同変写像は C 射の後合成である。
    M221F-7a + M221F-8b/8c。仮定なし。 -/
theorem towerComparison_full_regular (G : Grp)
    (Y : (gsetGaloisData G).C.Obj)
    (φ : ActHom
      (GaloisTower.colimHomAction (regTower G) (regAction G))
      (GaloisTower.colimHomAction (regTower G) Y)) :
    ∃ u : (gsetGaloisData G).C.Hom (regAction G) Y,
      (regTower G).towerComparison.onHom u = φ :=
  constTower_full (gsetGaloisData G) (regAction G) G.one
    (regAction_galois G) (fun w => regAction_endo_iso G w) Y φ

/-- **系（M221F-8f): 正則対象上の充満忠実性（モデル・無条件）** —
    正則塔の比較関手は G_reg 上で忠実（M221F-7c）かつ充満
    （M221F-8e）: onHom : Hom(G_reg, Y) → Hom_{π₁-Set} は全単射。 -/
theorem towerComparison_regular_fully_faithful (G : Grp)
    (Y : (gsetGaloisData G).C.Obj) :
    (∀ f g : (gsetGaloisData G).C.Hom (regAction G) Y,
      (regTower G).towerComparison.onHom f
        = (regTower G).towerComparison.onHom g → f = g) ∧
    (∀ φ : ActHom
        (GaloisTower.colimHomAction (regTower G) (regAction G))
        (GaloisTower.colimHomAction (regTower G) Y),
      ∃ u : (gsetGaloisData G).C.Hom (regAction G) Y,
        (regTower G).towerComparison.onHom u = φ) :=
  ⟨fun f g h => constTower_faithful (gsetGaloisData G) (regAction G)
      G.one (regAction_galois G) Y f g h,
    fun φ => towerComparison_full_regular G Y φ⟩

/-! ## M221F-9: 総括 -/

/-- **総括データ（M221F-9a）**: 充満性の証人 — ガロア塔 T・対象 X と、
    X 上の比較関手の充満性・忠実性（= X 上の充満忠実性）。
    M217F-13 の同値骨格データに欠けていた「充満」成分の構造体化。 -/
structure GaloisFullnessData (D : GaloisCatData.{u, 0}) where
  /-- π₁ を担うガロア塔（M24-4a）。 -/
  T : GaloisTower D
  /-- 充満性が成立する対象。 -/
  X : D.C.Obj
  /-- 充満性: 任意の π₁-同変写像は C 射の後合成（M221F-7a）。 -/
  full : ∀ (Y : D.C.Obj)
    (φ : ActHom (GaloisTower.colimHomAction T X)
      (GaloisTower.colimHomAction T Y)),
    ∃ u : D.C.Hom X Y, (GaloisTower.towerComparison T).onHom u = φ
  /-- 忠実性: 比較関手は X 上単射（M221F-7c）。 -/
  faithful : ∀ (Y : D.C.Obj) (f g : D.C.Hom X Y),
    (GaloisTower.towerComparison T).onHom f
      = (GaloisTower.towerComparison T).onHom g → f = g

/-- **証人（M221F-9b）**: 自己射 ⟹ 自己同型を満たす任意のガロア対象
    B とその定値塔が充満性データを与える（M221F-7a/7c）。 -/
noncomputable def galoisFullnessWitness (D : GaloisCatData.{u, 0})
    (B : D.C.Obj) (b₀ : D.F.onObj B) (hB : D.IsGalois B)
    (hendo : ∀ w : D.C.Hom B B, ∃ ι : CatIso D.C B B, ι.hom = w) :
    GaloisFullnessData D where
  T := constGaloisTower D B b₀ hB
  X := B
  full := fun Y φ => constTower_full D B b₀ hB hendo Y φ
  faithful := fun Y f g h => constTower_faithful D B b₀ hB Y f g h

/-- **定理（M221F-9c）: 充満性データの存在（モデル・無条件）** —
    任意の群 G のモデルで、正則対象と正則塔が充満性データを与える。 -/
theorem galoisFullness_exists (G : Grp) :
    Nonempty (GaloisFullnessData (gsetGaloisData G)) :=
  ⟨galoisFullnessWitness (gsetGaloisData G) (regAction G) G.one
    (regAction_galois G) (fun w => regAction_endo_iso G w)⟩

/-- **系（M221F-9d）: 無条件の存在**（無矛盾性）— 自明群で。 -/
theorem galoisFullness_exists_trivial :
    Nonempty (GaloisFullnessData (gsetGaloisData punitGrp)) :=
  galoisFullness_exists punitGrp

/-- **束ねデータ（M221F-9e）**: M217F-13 の同値骨格データ（忠実性・
    単射性・全射性）と本モジュールの充満性データを**同一の塔**で持つ
    総括 — SGA1 圏同値の全成分（忠実・充満・全単射比較・本質的全射の
    レベル橋）が一つの塔の上に揃ったことの構造体化。 -/
structure GaloisEquivalenceFullData (D : GaloisCatData.{u, 0}) where
  /-- M217F-13a の同値骨格データ。 -/
  skeleton : GaloisEquivalenceData D
  /-- 本モジュールの充満性データ。 -/
  fullness : GaloisFullnessData D
  /-- 両者は同じ塔を使う。 -/
  same_tower : fullness.T = skeleton.T

/-- **証人（M221F-9f）**: 任意の群 G のモデルで、正則塔上に同値骨格
    （M217F-13b）と充満性（M221F-9b）が同時に載る。 -/
noncomputable def galoisEquivalenceFullWitness (G : Grp) :
    GaloisEquivalenceFullData (gsetGaloisData G) where
  skeleton := galoisEquivalenceWitness (gsetGaloisData G) (regTower G)
  fullness := galoisFullnessWitness (gsetGaloisData G) (regAction G)
    G.one (regAction_galois G) (fun w => regAction_endo_iso G w)
  same_tower := rfl

/-- **定理（M221F-9g）: 束ねデータの存在（モデル・無条件）**。 -/
theorem galoisEquivalenceFull_exists (G : Grp) :
    Nonempty (GaloisEquivalenceFullData (gsetGaloisData G)) :=
  ⟨galoisEquivalenceFullWitness G⟩

/-- **系（M221F-9h）: 無条件の存在**（無矛盾性）— 自明群で。 -/
theorem galoisEquivalenceFull_exists_trivial :
    Nonempty (GaloisEquivalenceFullData (gsetGaloisData punitGrp)) :=
  galoisEquivalenceFull_exists punitGrp

end IUT
