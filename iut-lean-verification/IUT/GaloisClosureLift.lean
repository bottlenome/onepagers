/-
  # M160F: ガロア閉包のモデル側リフト（柱A A-1・並行部品）

  M148F（core(H) によるモデル側閉包）・M154F（G/core(H) の抽象
  IsGalois 充足）は**剰余類対象 G/H に限った**閉包だった。本モジュール
  はこれを**任意の連結対象**（モデルの語彙: 基点付き推移的 G-作用）
  へリフトする — 「任意の連結対象はガロア対象に支配される」
  （ガロア閉包の存在・十分性、M24 ProObject の正直申告の残余）の
  モデル一般形。群 G は**任意**（M157F の可換 ℤ に限らない）。

  * M160F-1 `stabHom` / `stabHom_injective` / `stabHom_surjective` —
    **分類射の関数化**: 軌道-安定化定理（M16-4 `orbit_stabilizer`）は
    ∃ 形だったが、ここでは分類射 [g] ↦ g·e₀ : G/Stab(e₀) → E を
    Quot.lift で**定義として**構成（choice 不要で合成に使える）。
    単射は常に、全射は推移性から
  * M160F-2 `closureHom` / `closureHom_pt` / `closureHom_surjective` —
    **閉包支配射**: M148F の支配射 G/core(Stab e₀) ↠ G/Stab(e₀)
    （`coreDominates`）と分類射の合成 G/core(Stab e₀) → E。
    基点 [1] を e₀ に送り、E が推移的ならファイバー全射
  * M160F-3 `connected_dominated_by_galois` — **主定理**: 任意の群 G と
    基点付き推移的 G-作用 E に対し、抽象 IsGalois（M21 原形）を満たす
    対象 B = G/core(Stab e₀) と `GSetCat G` の射 B → E でファイバー
    全射なものが存在する — A-1「連結対象はガロア対象に支配される」の
    モデル一般形（剰余類対象への同型輸送を経由しない直接構成）
  * M160F-4 `orbit_dominated_by_galois` — **系**: 任意の G-集合 X の
    任意の点 x₀ の軌道（= 連結成分、M16-3）はガロア対象に支配される。
    G-集合は軌道に分解するから「モデルの全ての連結成分に閉包が在る」
  * M160F-5 `closureTower` / `closureTower_dominates` — **任意の群上の
    ガロア塔**: 閉包対象を各層とする定値塔が
    `GaloisTower (gsetGaloisData G)`（M24-4a）の全フィールドを満たし、
    全ての層が E をファイバー全射で支配する。M157F の塔は可換群 ℤ
    専用だったが、本塔は**任意の（非可換）G** で閉包を M24 の
    塔インターフェイス（π₁ = lim Aut の機構）へ接続する
  * M160F-6 `GaloisClosureLiftData` / `galoisClosureLiftWitness` /
    `galoisClosureLift_exists` — 総括データ・証人・存在定理

  **意義**: M148F/M154F の「G/H 限定」の閉包が、分類射の関数化に
  より任意の連結対象・任意の群へ広がった。M16-3（軌道分解）と
  合わせ「G-Set モデルの全ての連結対象はガロア対象に支配される」が
  ∃ の意味で完結し、さらに閉包が M24 GaloisTower の型に実際に
  入ることを任意の群で示した（A-1 の十分性のモデル側完結）。

  **正直な限定**: (1) 連結性はモデルの語彙（基点 + 推移性、M16）で
  取った。E 自身の抽象 Connected（M21）の導出は範囲外 — 一般の
  推移的 E への切断の構成は代表元系の選択を要し choice なしでは
  得られない（剰余類対象については M154F-5 が choice なしで済む
  理由は Quot の代表元が切断を与えるため）。(2) 塔は定値塔（各層が
  同一のガロア対象）であり、真に増大する鎖（M157F の ℤ/n! 型）の
  非可換一般化は範囲外。(3) 抽象公理系そのものの中でのガロア閉包
  （任意の抽象ガロア圏での存在定理）は依然として範囲外。
  (4) `gsetGaloisData G`（M21-8）は G6 フィールドに Classical.choice を
  含むため、型がそれに言及する宣言（M160F-3〜6）は公理リストに
  Classical.choice を**型経由で継承**する（M154F・M157F と同じ事情、
  継承であり本モジュールでの使用ゼロ）。M160F-1/2（stabHom・
  closureHom 系）は [Quot.sound] のみ。

  全て選択公理不使用（型継承を除く）。サブエージェント並行部品。
-/
import IUT.CosetGalois
import IUT.ProObject

namespace IUT

/-! ## M160F-1: 分類射の関数化 — G/Stab(e₀) → E -/

/-- **分類射 (M160F-1a)**: 基点 e₀ をもつ G-作用 E への評価写像
    [g] ↦ g·e₀ を `Quot.lift` で**定義として**構成する。
    well-definedness: g⁻¹g' ∈ Stab(e₀) なら g·e₀ = g'·e₀。
    M16-4 `orbit_stabilizer` の ∃ 形の φ と外延的に同じものだが、
    定義であるため choice なしで合成（M160F-2）に使える。 -/
def stabHom (G : Grp) (E : GAction G) (e₀ : E.carrier) :
    ActHom (cosetAction G (stabilizer G E e₀)) E where
  map := Quot.lift (fun g => E.act g e₀)
    (fun a b hab => by
      have h2 : E.act (G.mul (G.inv a) b) e₀ = e₀ := hab
      have h3 := congrArg (E.act a) h2
      rw [← E.act_mul, ← G.mul_assoc, G.mul_inv, G.one_mul] at h3
      exact h3.symm)
  equivariant := by
    intro g x
    induction x using Quot.ind; rename_i a
    show E.act (G.mul g a) e₀ = E.act g (E.act a e₀)
    exact E.act_mul g a e₀

/-- **補題 (M160F-1b): 分類射は単射** — g·e₀ = g'·e₀ から
    g⁻¹g' ∈ Stab(e₀)、すなわち [g] = [g']（M16-4 の単射部の
    関数化版）。 -/
theorem stabHom_injective (G : Grp) (E : GAction G) (e₀ : E.carrier) :
    ∀ p q, (stabHom G E e₀).map p = (stabHom G E e₀).map q → p = q := by
  intro p q h
  induction p using Quot.ind; rename_i g
  induction q using Quot.ind; rename_i g'
  have h' : E.act g e₀ = E.act g' e₀ := h
  have h2 := congrArg (E.act (G.inv g)) h'
  rw [← E.act_mul, ← E.act_mul, G.inv_mul, E.act_one] at h2
  apply Quot.sound
  show E.act (G.mul (G.inv g) g') e₀ = e₀
  exact h2.symm

/-- **補題 (M160F-1c): E が推移的なら分類射は全射** —
    e₀ を y に送る g がそのまま原像 [g] を与える。 -/
theorem stabHom_surjective (G : Grp) (E : GAction G) (e₀ : E.carrier)
    (htrans : E.Transitive) :
    ∀ y, ∃ p, (stabHom G E e₀).map p = y := by
  intro y
  obtain ⟨g, hg⟩ := htrans e₀ y
  exact ⟨Quot.mk (cosetRel G (stabilizer G E e₀)) g, hg⟩

/-! ## M160F-2: 閉包支配射 — G/core(Stab e₀) → E -/

/-- **閉包支配射 (M160F-2a)**: M148F の支配射
    G/core(Stab e₀) ↠ G/Stab(e₀)（`coreDominates`）と分類射
    （M160F-1a）の合成。定義域はガロア対象（M154F-6b）。 -/
def closureHom (G : Grp) (E : GAction G) (e₀ : E.carrier) :
    ActHom (cosetAction G (coreSubgroup G (stabilizer G E e₀))) E :=
  ActHom.comp (coreDominates G (stabilizer G E e₀)) (stabHom G E e₀)

/-- **補題 (M160F-2b): 閉包支配射は基点を保つ** — [1] ↦ 1·e₀ = e₀。 -/
theorem closureHom_pt (G : Grp) (E : GAction G) (e₀ : E.carrier) :
    (closureHom G E e₀).map
      (Quot.mk (cosetRel G (coreSubgroup G (stabilizer G E e₀))) G.one)
      = e₀ :=
  E.act_one e₀

/-- **補題 (M160F-2c): E が推移的なら閉包支配射はファイバー全射** —
    合成の各点値は [g] ↦ g·e₀ なので推移性の witness がそのまま効く。 -/
theorem closureHom_surjective (G : Grp) (E : GAction G) (e₀ : E.carrier)
    (htrans : E.Transitive) :
    ∀ y, ∃ x, (closureHom G E e₀).map x = y := by
  intro y
  obtain ⟨g, hg⟩ := htrans e₀ y
  exact ⟨Quot.mk (cosetRel G (coreSubgroup G (stabilizer G E e₀))) g, hg⟩

/-! ## M160F-3: 主定理 — 任意の連結対象はガロア対象に支配される -/

/-- **主定理 (M160F-3): ガロア閉包の存在・十分性（モデル一般形）** —
    任意の群 G と基点付き推移的 G-作用 E（= モデルの連結対象、M16）に
    対し、抽象 IsGalois（M21 原形）を満たす対象
    B = G/core(Stab e₀) と `GSetCat G` のファイバー全射 B → E が
    存在する。M154F-7 は剰余類対象 G/H に限っていたが、本定理は
    分類射の関数化（M160F-1）により**同型輸送を経由せず直接**
    任意の連結対象を支配する（A-1 十分性のモデル側一般形）。
    **注**: 型が `gsetGaloisData`（G6 に Classical.choice）に言及する
    ため公理リストに choice を継承するが、本証明は choice 不使用。 -/
theorem connected_dominated_by_galois (G : Grp) (E : GAction G)
    (e₀ : E.carrier) (htrans : E.Transitive) :
    ∃ B : (GSetCat G).Obj,
      (gsetGaloisData G).IsGalois B ∧
      ∃ φ : (GSetCat G).Hom B E, ∀ y, ∃ x, φ.map x = y :=
  ⟨cosetGSet G (coreSubgroup G (stabilizer G E e₀)),
    cosetGSet_core_galois G (stabilizer G E e₀),
    closureHom G E e₀, closureHom_surjective G E e₀ htrans⟩

/-! ## M160F-4: 系 — 全ての軌道（連結成分）に閉包が在る -/

/-- **系 (M160F-4): 任意の G-集合の任意の軌道はガロア対象に支配され
    る** — 軌道は推移的（M16-3 `orbit_transitive`）で x₀ 自身を基点に
    持つから主定理が適用できる。G-集合は軌道 = 連結成分に分解する
    （M16-3）ので、これは「モデルの全ての連結成分がガロア閉包を
    持つ」ことを意味する。 -/
theorem orbit_dominated_by_galois (G : Grp) (X : GAction G)
    (x₀ : X.carrier) :
    ∃ B : (GSetCat G).Obj,
      (gsetGaloisData G).IsGalois B ∧
      ∃ φ : (GSetCat G).Hom B (orbitOf X x₀), ∀ y, ∃ x, φ.map x = y :=
  connected_dominated_by_galois G (orbitOf X x₀)
    ⟨x₀, orbitRel_refl X x₀⟩ (orbit_transitive X x₀)

/-! ## M160F-5: 任意の群上のガロア塔への接続 -/

/-- **閉包塔 (M160F-5a)**: 閉包対象 G/core(Stab e₀) を全ての層とする
    定値塔が `GaloisTower (gsetGaloisData G)`（M24-4a）の全フィールド
    を満たす。M24-5 の自明塔は自明群上、M157F の階乗塔は可換群 ℤ 上
    だったが、本塔は**任意の（非可換）群 G** で M24 の π₁ 機構
    （`towerSystem` / `pi1Tower`）に入力できる初のガロア塔である。 -/
def closureTower (G : Grp) (E : GAction G) (e₀ : E.carrier) :
    GaloisTower (gsetGaloisData G) where
  A := fun _ => cosetGSet G (coreSubgroup G (stabilizer G E e₀))
  pt := fun _ =>
    Quot.mk (cosetRel G (coreSubgroup G (stabilizer G E e₀))) G.one
  hGal := fun _ => cosetGSet_core_galois G (stabilizer G E e₀)
  P := fun _ => (GSetCat G).id (cosetGSet G (coreSubgroup G (stabilizer G E e₀)))
  P_self := fun _ _ => rfl
  P_comp := fun _ _ => (GSetCat G).id_comp _
  P_pt := fun _ => rfl

/-- **定理 (M160F-5b): 閉包塔の全ての層は E を支配する** —
    各層からのファイバー全射（M160F-2）。「連結対象 E の上に、
    それを支配するガロア塔が立つ」という A-1 の塔の読み。 -/
theorem closureTower_dominates (G : Grp) (E : GAction G)
    (e₀ : E.carrier) (htrans : E.Transitive) :
    ∀ n : Nat,
      ∃ φ : (GSetCat G).Hom ((closureTower G E e₀).A n) E,
        ∀ y, ∃ x, φ.map x = y :=
  fun _ => ⟨closureHom G E e₀, closureHom_surjective G E e₀ htrans⟩

/-! ## M160F-6: 総括 -/

/-- **総括データ (M160F-6a)**: 連結対象 E のガロア閉包リフトの全部品
    — ガロア対象・ファイバー全射の支配射・E を支配するガロア塔。 -/
structure GaloisClosureLiftData (G : Grp) (E : GAction G) where
  /-- ガロア閉包対象（G/core(Stab e₀)）。 -/
  galoisObj : (GSetCat G).Obj
  /-- 閉包対象は抽象 IsGalois を満たす（M154F-6b）。 -/
  galois : (gsetGaloisData G).IsGalois galoisObj
  /-- 支配射（GSetCat の射、M160F-2a）。 -/
  dom : (GSetCat G).Hom galoisObj E
  /-- 支配射のファイバー全射性（M160F-2c）。 -/
  dom_surj : ∀ y, ∃ x, dom.map x = y
  /-- E を支配するガロア塔（M160F-5a）。 -/
  tower : GaloisTower (gsetGaloisData G)
  /-- 塔の全ての層は閉包対象そのもの。 -/
  tower_layer : ∀ n, tower.A n = galoisObj

/-- **証人 (M160F-6b)**: 基点と推移性から全部品が構成される。 -/
def galoisClosureLiftWitness (G : Grp) (E : GAction G)
    (e₀ : E.carrier) (htrans : E.Transitive) :
    GaloisClosureLiftData G E where
  galoisObj := cosetGSet G (coreSubgroup G (stabilizer G E e₀))
  galois := cosetGSet_core_galois G (stabilizer G E e₀)
  dom := closureHom G E e₀
  dom_surj := closureHom_surjective G E e₀ htrans
  tower := closureTower G E e₀
  tower_layer := fun _ => rfl

/-- **定理 (M160F-6c): ガロア閉包リフトデータの存在**（無矛盾性）—
    任意の群の任意の基点付き推移的作用に対して。 -/
theorem galoisClosureLift_exists (G : Grp) (E : GAction G)
    (e₀ : E.carrier) (htrans : E.Transitive) :
    Nonempty (GaloisClosureLiftData G E) :=
  ⟨galoisClosureLiftWitness G E e₀ htrans⟩

end IUT
