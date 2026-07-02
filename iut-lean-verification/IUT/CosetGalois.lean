/-
  # M154F: 剰余類対象の抽象ガロア性 — M148F の閉包を抽象述語 IsGalois へ接合（柱A A-1）

  M148F (GaloisClosureModel) はガロア閉包を SGA1 の生の群・剰余類レベル
  （安定化群 = core・自己同変写像の推移性）で完結させた。本モジュールは
  その core 剰余類対象を **G-Set 圏 `GSetCat G` の対象として実現し、
  リポジトリの抽象ガロア述語（M21 AbstractGalois の `Connected` /
  `IsGalois`、ファイバー関手 = 忘却関手 `gsetGaloisData G`）を充足する**
  ことを証明する — 「モデル側閉包」と「抽象公理系」の接合点。

  * M154F-1 `cosetGSet` — 剰余類作用 G/K を `GSetCat G` の対象として
    実現（`(gsetGaloisData G).C = GSetCat G` は定義的等号なので
    ファイバー = 台 = `cosetSpace G K`）
  * M154F-2 `cosetGSet_transitive` — 剰余類空間上の左移動は推移的
    （Quot.ind ×2 + 代表 g := b·a⁻¹ の計算。連結性の実体）
  * M154F-3 `orbitHom` / `gset_mono_injective` — **圏論的モノは
    ファイバー単射**: 正則作用 `regAction G` からの軌道写像
    g ↦ g·e をテスト対象に使い、抽象 `Mono`（左簡約可能性）から
    台写像の単射性を取り出す（G-Set 圏の標準論法、choice 不要）
  * M154F-4 `basepoint_translate` / `cosetSection` /
    `cosetSection_section` — **逆射の明示構成**: ファイバーで [1] の
    上にある基点 e₀ をもつ単射同変射 m : E → G/K に対し
    [a] ↦ a·e₀ が well-defined な同変逆写像になる（well-definedness
    は m の単射性へ還元。全単射から逆関数を選択公理で取り出す
    代わりに、剰余類の代表元で逆射を**構成**する — choice 回避の要）
  * M154F-5 `cosetGSet_connected` — **抽象 Connected の充足**:
    G/K は M21 の意味で連結（ファイバー非空 + 非空ファイバーを持つ
    モノ部分対象は同型に限る）。M154F-2〜4 の組立て
  * M154F-6 `coreRightMul_isIso` / `cosetGSet_core_galois` —
    **本丸・抽象 IsGalois の充足**: G/core(H) は M21 の意味でガロア
    （連結 + 自己同型のファイバーへの推移性）。M148F の
    `coreRightMul`（右移動、正規性で降下）を `GSetCat` の同型射に
    包み（逆 = c⁻¹ の右移動）、推移性は `core_aut_transitive`
  * M154F-7 `galois_closure_abstract` — **総合定理**: 任意の剰余類
    対象 G/H は連結であり、抽象 IsGalois を満たす対象
    G/core(H) から `GSetCat G` の射（ファイバー全射 =
    支配射 `coreDominates`）で支配される — M148F-8
    `galois_closure_model` の抽象語彙版（A-1 のモデル内・抽象述語版）
  * M154F-8 `CosetGaloisData` / `cosetGaloisWitness` /
    `cosetGalois_exists` — 総括データ・証人・存在定理

  **意義**: M16-4/5（連結 G-集合の分類: 全て G/H の形）と合わせ、
  「G-Set モデルの任意の連結対象は、**抽象公理系の述語 IsGalois を
  満たす**対象から圏の射で支配される」が閉じる。M24 (ProObject) の
  正直申告「ガロア閉包は未形式化の入力」のうち、モデル側が M21 の
  抽象語彙のまま利用可能になった。

  **正直な申告**: (1) `Connected` / `IsGalois` / `Mono` / `IsIso` は
  すべて M21 の原形定義をそのまま充足した（スコープ置換なし）。
  (2) `gsetGaloisData G`（M21-8）は G6 フィールドに Classical.choice
  を含むため、**型がそれに言及する宣言（M154F-5〜8）は公理リストに
  Classical.choice を継承する**（M149F `gset_satisfies_quotient` と
  同じ事情）。本モジュールの証明自体は choice を一切使用せず
  （逆射は M154F-4 で明示構成）、gsetGaloisData に言及しない部品
  M154F-1〜4 は [Quot.sound] 以下（orbitHom は公理ゼロ）、
  gsetGaloisData に言及する M154F-5〜8（coreRightMul_isIso 含む）は
  [Classical.choice, Quot.sound]（choice は型経由の継承のみ）。(3) 抽象側の一般論（任意の抽象 Galois 圏で連結対象がガロア
  対象に支配されること）は本切片の範囲外 — ここで閉じたのはモデル
  （G-Set 圏 + 忘却関手）における充足である。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.GaloisClosureModel
import IUT.GSetQuotient

namespace IUT

/-! ## M154F-1: 剰余類対象の G-Set 圏への実現 -/

/-- **剰余類対象**（M154F-1）: 剰余類作用 G/K を `GSetCat G` の対象と
    して見る。`(gsetGaloisData G).C = GSetCat G` と
    `(gsetGaloisData G).F = forgetfulG G` は定義的等号なので、
    この対象の抽象ファイバーは台 `cosetSpace G K` そのもの。 -/
def cosetGSet (G : Grp) (K : Subgroup G) : (GSetCat G).Obj :=
  cosetAction G K

/-! ## M154F-2: 推移性（連結性の実体） -/

/-- **定理 (M154F-2): 剰余類対象の作用は推移的** — [a] を [b] に
    送る群元は g := b·a⁻¹（Quot.ind ×2 + 結合則の計算）。 -/
theorem cosetGSet_transitive (G : Grp) (K : Subgroup G) :
    ∀ x y : (cosetGSet G K).carrier, ∃ g, (cosetGSet G K).act g x = y := by
  intro x y
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  refine ⟨G.mul b (G.inv a), ?_⟩
  show Quot.mk (cosetRel G K) (G.mul (G.mul b (G.inv a)) a)
    = Quot.mk (cosetRel G K) b
  rw [G.mul_assoc, G.inv_mul, G.mul_one]

/-! ## M154F-3: 圏論的モノはファイバー単射（テスト対象 = 正則作用） -/

/-- **軌道写像**（M154F-3a）: 点 e ∈ E に対し g ↦ g·e は正則作用
    `regAction G` からの同変写像（同変性 = 作用の結合則）。
    圏論的モノからファイバー単射を取り出すテスト射。 -/
def orbitHom {G : Grp} (E : GAction G) (e : E.carrier) :
    ActHom (regAction G) E where
  map := fun g => E.act g e
  equivariant := fun σ x => E.act_mul σ x e

/-- **定理 (M154F-3b): 圏論的モノはファイバー単射** — m(a) = m(b) なら
    軌道写像 g ↦ g·a, g ↦ g·b の m との合成が一致（m の同変性）、
    モノ性で軌道写像自体が一致、g = 1 で評価して a = b。
    抽象 `Mono`（左簡約）→ 台写像の単射性、choice 不要。 -/
theorem gset_mono_injective (G : Grp) {E A : GAction G} (m : ActHom E A)
    (hm : ∀ {W : GAction G} (u v : ActHom W E),
      ActHom.comp u m = ActHom.comp v m → u = v) :
    ∀ a b : E.carrier, m.map a = m.map b → a = b := by
  intro a b hab
  have hcomp : ActHom.comp (orbitHom E a) m = ActHom.comp (orbitHom E b) m :=
    ActHom.ext (fun x => by
      show m.map (E.act x a) = m.map (E.act x b)
      rw [m.equivariant, m.equivariant, hab])
  have huv := hm (orbitHom E a) (orbitHom E b) hcomp
  have h1 : E.act G.one a = E.act G.one b :=
    congrFun (congrArg ActHom.map huv) G.one
  rw [E.act_one, E.act_one] at h1
  exact h1

/-! ## M154F-4: 逆射の明示構成（choice 回避の要） -/

/-- **補題 (M154F-4a): 基点の移動** — m(e₀) = [1] なら
    m(a·e₀) = a·[1] = [a]（同変性 + 単位律）。 -/
theorem basepoint_translate {G : Grp} {K : Subgroup G} {E : GAction G}
    (m : ActHom E (cosetAction G K)) (e₀ : E.carrier)
    (he0 : m.map e₀ = Quot.mk (cosetRel G K) G.one) (a : G.carrier) :
    m.map (E.act a e₀) = Quot.mk (cosetRel G K) a := by
  rw [m.equivariant, he0]
  show Quot.mk (cosetRel G K) (G.mul a G.one) = Quot.mk (cosetRel G K) a
  rw [G.mul_one]

/-- **逆射の構成 (M154F-4b)**: ファイバーで [1] の上に基点 e₀ を持つ
    単射同変射 m : E → G/K に対し、[a] ↦ a·e₀ は well-defined な
    同変写像 G/K → E。well-definedness は「m で送ると両者とも
    剰余類そのものになる」ことと m の単射性へ還元（Quot.lift、
    選択公理の代わりに剰余類の代表元で逆射を構成）。 -/
def cosetSection {G : Grp} {K : Subgroup G} {E : GAction G}
    (m : ActHom E (cosetAction G K))
    (hinj : ∀ a b : E.carrier, m.map a = m.map b → a = b)
    (e₀ : E.carrier) (he0 : m.map e₀ = Quot.mk (cosetRel G K) G.one) :
    ActHom (cosetAction G K) E where
  map := Quot.lift (fun a => E.act a e₀)
    (fun a b hab => hinj _ _ (by
      rw [basepoint_translate m e₀ he0 a, basepoint_translate m e₀ he0 b]
      exact Quot.sound hab))
  equivariant := by
    intro σ x
    induction x using Quot.ind; rename_i a
    show E.act (G.mul σ a) e₀ = E.act σ (E.act a e₀)
    exact E.act_mul σ a e₀

/-- **補題 (M154F-4c): 切断性** — m ∘ (cosetSection …) = id_{G/K}
    （各点: m(a·e₀) = [a]、M154F-4a の Quot.ind 版）。 -/
theorem cosetSection_section {G : Grp} {K : Subgroup G} {E : GAction G}
    (m : ActHom E (cosetAction G K))
    (hinj : ∀ a b : E.carrier, m.map a = m.map b → a = b)
    (e₀ : E.carrier) (he0 : m.map e₀ = Quot.mk (cosetRel G K) G.one) :
    ∀ y, m.map ((cosetSection m hinj e₀ he0).map y) = y := by
  intro y
  induction y using Quot.ind; rename_i a
  exact basepoint_translate m e₀ he0 a

/-! ## M154F-5: 抽象 Connected の充足 -/

/-- **定理 (M154F-5): 剰余類対象は M21 の意味で連結** —
    ファイバー（= cosetSpace G K）は [1] で非空。非空ファイバーを持つ
    モノ m : E → G/K は同型: モノ性からファイバー単射（M154F-3）、
    非空性 + 推移性（M154F-2）で [1] の上の基点 e₀ を得て、
    逆射を明示構成（M154F-4）。左逆は単射性、右逆は切断性。
    **注**: 型が `gsetGaloisData`（G6 に Classical.choice）に言及する
    ため公理リストに choice を継承するが、本証明は choice 不使用。 -/
theorem cosetGSet_connected (G : Grp) (K : Subgroup G) :
    (gsetGaloisData G).Connected (cosetGSet G K) := by
  refine ⟨⟨Quot.mk (cosetRel G K) G.one⟩, ?_⟩
  intro E m hm hne
  have hinj : ∀ a b : E.carrier, m.map a = m.map b → a = b :=
    gset_mono_injective G m hm
  obtain ⟨e⟩ := hne
  obtain ⟨g, hg⟩ := cosetGSet_transitive G K (m.map e)
    (Quot.mk (cosetRel G K) G.one)
  have he0 : m.map (E.act g e) = Quot.mk (cosetRel G K) G.one := by
    rw [m.equivariant]
    exact hg
  refine ⟨cosetSection m hinj (E.act g e) he0, ?_, ?_⟩
  · -- m ∘ ψ = id_E（図式順合成 comp m ψ）: 単射性へ還元
    exact ActHom.ext (fun x =>
      hinj _ _ (cosetSection_section m hinj (E.act g e) he0 (m.map x)))
  · -- ψ ∘ m = id_{G/K}: 切断性そのもの
    exact ActHom.ext (fun y =>
      cosetSection_section m hinj (E.act g e) he0 y)

/-! ## M154F-6: 抽象 IsGalois の充足（本丸） -/

/-- **補題 (M154F-6a): core 右移動は GSetCat の同型射** —
    M148F の `coreRightMul`（正規性により G/core(H) に降りる右移動）は
    c⁻¹ の右移動を逆に持つ（`coreRightMul_left_inv` / `_right_inv`）。
    抽象 `IsIso`（可逆射）の充足。 -/
theorem coreRightMul_isIso (G : Grp) (H : Subgroup G) (c : G.carrier) :
    (gsetGaloisData G).IsIso (X := cosetGSet G (coreSubgroup G H))
      (Y := cosetGSet G (coreSubgroup G H)) (coreRightMul G H c) :=
  ⟨coreRightMul G H (G.inv c),
    ActHom.ext (fun x => coreRightMul_left_inv G H c x),
    ActHom.ext (fun x => coreRightMul_right_inv G H c x)⟩

/-- **定理 (M154F-6b): G/core(H) は M21 の意味でガロア** —
    連結（M154F-5）+ 自己同型のファイバーへの推移性: 任意の
    ファイバー点 a, b に対し `core_aut_transitive`（M148F-7e）の
    右移動 c が a を b に送り、それは同型射（M154F-6a）。
    抽象述語 `IsGalois` の**原形のままの**充足。 -/
theorem cosetGSet_core_galois (G : Grp) (H : Subgroup G) :
    (gsetGaloisData G).IsGalois (cosetGSet G (coreSubgroup G H)) := by
  refine ⟨cosetGSet_connected G (coreSubgroup G H), ?_⟩
  intro a b
  obtain ⟨c, hc⟩ := core_aut_transitive G H a b
  exact ⟨coreRightMul G H c, coreRightMul_isIso G H c, hc⟩

/-! ## M154F-7: 総合定理（見出し） -/

/-- **定理 (M154F-7): ガロア閉包・抽象語彙版** — 任意の剰余類対象
    G/H は抽象的に連結であり、**抽象 IsGalois を満たす**対象
    G/core(H) から `GSetCat G` の射（ファイバー全射 = M148F の
    支配射 `coreDominates`）で支配される。M148F-8
    `galois_closure_model` の「安定化群 = core・ActHom 推移性」という
    モデル語彙が、M21 の公理系述語 `Connected` / `IsGalois` に
    置き換わった形（柱A A-1 のモデル内・抽象述語版の完結）。 -/
theorem galois_closure_abstract (G : Grp) (H : Subgroup G) :
    (gsetGaloisData G).Connected (cosetGSet G H) ∧
    ∃ φ : (GSetCat G).Hom (cosetGSet G (coreSubgroup G H)) (cosetGSet G H),
      (∀ y, ∃ x, φ.map x = y) ∧
      (gsetGaloisData G).IsGalois (cosetGSet G (coreSubgroup G H)) :=
  ⟨cosetGSet_connected G H,
    coreDominates G H, coreToCoset_surjective G H,
    cosetGSet_core_galois G H⟩

/-! ## M154F-8: 総括 -/

/-- **総括データ (M154F-8a)**: 剰余類対象 G/H の抽象ガロア閉包の全部品
    — 連結性・ガロア対象・支配射・ファイバー全射性。 -/
structure CosetGaloisData (G : Grp) (H : Subgroup G) where
  /-- ガロア閉包を与える対象（G/core(H)）。 -/
  galoisObj : (GSetCat G).Obj
  /-- G/H は抽象的に連結（M154F-5）。 -/
  base_connected : (gsetGaloisData G).Connected (cosetGSet G H)
  /-- 閉包対象は抽象 IsGalois を満たす（M154F-6b）。 -/
  galois : (gsetGaloisData G).IsGalois galoisObj
  /-- 支配射（GSetCat の射、M148F-4b）。 -/
  dom : (GSetCat G).Hom galoisObj (cosetGSet G H)
  /-- 支配射のファイバー全射性（M148F-4c）。 -/
  dom_surj : ∀ y, ∃ x, dom.map x = y

/-- **証人 (M154F-8b)**: galoisObj := G/core(H) が全条件を満たす。 -/
def cosetGaloisWitness (G : Grp) (H : Subgroup G) : CosetGaloisData G H where
  galoisObj := cosetGSet G (coreSubgroup G H)
  base_connected := cosetGSet_connected G H
  galois := cosetGSet_core_galois G H
  dom := coreDominates G H
  dom_surj := coreToCoset_surjective G H

/-- **定理 (M154F-8c): 抽象ガロア閉包データの存在**（無矛盾性）。 -/
theorem cosetGalois_exists (G : Grp) (H : Subgroup G) :
    Nonempty (CosetGaloisData G H) :=
  ⟨cosetGaloisWitness G H⟩

end IUT
