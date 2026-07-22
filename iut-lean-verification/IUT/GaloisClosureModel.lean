/-
  IUT/GaloisClosureModel.lean — M148F: ガロア閉包のモデル側 —
  core 部分群による支配（柱A A-1 の剰余類モデル完結）

  M24 (ProObject) の正直申告「ガロア閉包（任意の連結対象がガロア
  対象に支配されること）は未形式化の入力」のうち、**剰余類作用
  モデル側**を閉じる。M16 (SGA1) の分類定理により任意の連結
  G-集合は剰余類作用 G/H の形（every_orbit_is_coset）だから、
  モデルでのガロア閉包は純群論の主張になる: 任意の部分群 H に
  対し正規部分群 core(H) = ∩_a aHa⁻¹（剰余類作用 G/H の核）が
  存在し、G/core(H) が G/H を同変全射で支配し、G/core(H) は
  ガロア（= 全点で安定化群が core(H) に一致し、自己同変写像が
  ファイバーに推移的に作用する）。本モジュールはこの全てを
  選択公理なしに完全証明する:

  * M148F-1 `coreMem` / `coreSubgroup` — core(H) = {g | ∀a, a⁻¹ga ∈ H}
    の部分群性（単位元・積・逆元の閉性、Grp 公理計算のみ）
  * M148F-2 `core_le` — core(H) ⊆ H（a = 1 の共役）
  * M148F-3 `coreMem_conj` / `coreMem_of_conj` / `core_normal` —
    **正規性**: core(H) は全ての共役で不変（∀ b g, g ∈ core →
    bgb⁻¹ ∈ core、逆向きも）
  * M148F-4 `coreToCoset` / `coreDominates` / `coreToCoset_surjective`
    / `core_hom_pointed` — **支配射**: 同変全射
    G/core(H) ↠ G/H（Quot.lift による構成 + M16-6 coset_hom_iff
    の Galois 対応射側のインスタンス化）
  * M148F-5 `coset_stabilizer_mem` — 一般補題: G/K の剰余類 [a] の
    安定化群への所属 ⟺ a⁻¹ga ∈ K（軌道-安定化の局所形）
  * M148F-6 `core_stabilizer` / `core_stabilizer_all` — **ガロア性
    （安定化群の読み）**: G/core(H) の**全ての**点の安定化群が
    core(H) そのものに一致（正規性から基点に依存しない）
  * M148F-7 `cosetRel_right_core` / `coreRightMul` /
    `coreRightMul_left_inv` / `coreRightMul_right_inv` /
    `core_aut_transitive` — **ガロア性（自己同型の読み）**: 右移動
    が正規性により G/core(H) に降り、可逆な自己同変写像として
    ファイバーに推移的に作用する（M21 IsGalois「自己同型の
    ファイバーへの推移性」のモデル実現）
  * M148F-8 `galois_closure_model` / `GaloisClosureModelData` /
    `galoisClosureModelWitness` / `galoisClosureModel_exists` —
    総合定理: 任意の剰余類対象 G/H は正規部分群 core(H) による
    ガロア剰余類対象 G/core(H) から同変全射で支配される

  **意義**: SGA1 の π₁ 構成（M24 のガロア塔）が要求する「ガロア
  閉包の存在」が、モデル（G-集合圏）では選択公理なしの群論的
  構成 core(H) で実現されることの完全証明。M16-4/5（対象の分類:
  連結 = 剰余類）と合わせ、「モデルの任意の連結対象はガロア対象
  に支配される」が閉じる。

  **正直な申告**: (1) 位相的条件（core(H) の開性・有限指数）と
  pro-対象の塔（M24 GaloisTower）への実際の組み込みは本切片の
  範囲外。(2) 抽象公理系（M21 GaloisCatData の IsGalois、圏論的
  連結性込み）への接続も範囲外 — 本モジュールのガロア性は
  「全点の安定化群 = core（正規）」+「自己同変写像の推移性」
  というモデルの語彙（M16 の stabilizer / ActHom）で述べた。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.SGA1

namespace IUT

/-! ## §1 core 部分群の構成（M148F-1） -/

/-- **core への所属**（M148F-1a): 全ての共役 a⁻¹ga が H に入る。
    core(H) = ∩_a aHa⁻¹ = 剰余類作用 G/H の核。 -/
def coreMem (G : Grp) (H : Subgroup G) (g : G.carrier) : Prop :=
  ∀ a : G.carrier, H.mem (G.mul (G.mul (G.inv a) g) a)

/-- **core(H) は部分群**（M148F-1b): 単位元・積・逆元の閉性の
    完全証明（Grp の結合則パズルのみ、公理ゼロ）。 -/
def coreSubgroup (G : Grp) (H : Subgroup G) : Subgroup G where
  mem := coreMem G H
  one_mem := fun a => by
    rw [G.mul_one, G.inv_mul]
    exact H.one_mem
  mul_mem := fun {g₁ g₂} hg₁ hg₂ a => by
    have hgh := H.mul_mem (hg₁ a) (hg₂ a)
    rw [G.mul_assoc (G.mul (G.inv a) g₁) a (G.mul (G.mul (G.inv a) g₂) a),
      ← G.mul_assoc a (G.mul (G.inv a) g₂) a,
      ← G.mul_assoc a (G.inv a) g₂, G.mul_inv, G.one_mul,
      ← G.mul_assoc (G.mul (G.inv a) g₁) g₂ a,
      G.mul_assoc (G.inv a) g₁ g₂] at hgh
    exact hgh
  inv_mem := fun {g} hg a => by
    have h1 := H.inv_mem (hg a)
    rw [G.inv_mul_rev, G.inv_mul_rev, G.inv_inv] at h1
    rw [G.mul_assoc]
    exact h1

/-! ## §2 core ⊆ H と正規性（M148F-2, M148F-3） -/

/-- **定理 (M148F-2): core(H) ⊆ H** — a = 1 の共役を取る。 -/
theorem core_le (G : Grp) (H : Subgroup G) :
    ∀ g, coreMem G H g → H.mem g := by
  intro g hg
  have h1 := hg G.one
  rw [G.mul_one] at h1
  have hone : G.inv G.one = G.one := by
    have h2 := G.inv_mul G.one
    rw [G.mul_one] at h2
    exact h2
  rw [hone, G.one_mul] at h1
  exact h1

/-- **補題 (M148F-3a): core は共役で閉じる（下向き）** —
    g ∈ core(H) ⟹ a⁻¹ga ∈ core(H)（共役の付け替え c ↦ ac）。 -/
theorem coreMem_conj (G : Grp) (H : Subgroup G) (a : G.carrier)
    {g : G.carrier} (hg : coreMem G H g) :
    coreMem G H (G.mul (G.mul (G.inv a) g) a) := by
  intro c
  have h1 := hg (G.mul a c)
  rw [G.inv_mul_rev, G.mul_assoc (G.inv c) (G.inv a) g,
    ← G.mul_assoc (G.mul (G.inv c) (G.mul (G.inv a) g)) a c,
    G.mul_assoc (G.inv c) (G.mul (G.inv a) g) a] at h1
  exact h1

/-- **補題 (M148F-3b): core は共役で閉じる（上向き）** —
    a⁻¹ga ∈ core(H) ⟹ g ∈ core(H)（a⁻¹ で共役を戻す）。 -/
theorem coreMem_of_conj (G : Grp) (H : Subgroup G) (a : G.carrier)
    {g : G.carrier} (hg : coreMem G H (G.mul (G.mul (G.inv a) g) a)) :
    coreMem G H g := by
  have h1 := coreMem_conj G H (G.inv a) hg
  rw [G.inv_inv] at h1
  have key : G.mul (G.mul a (G.mul (G.mul (G.inv a) g) a)) (G.inv a) = g := by
    rw [← G.mul_assoc a (G.mul (G.inv a) g) a, ← G.mul_assoc a (G.inv a) g,
      G.mul_inv, G.one_mul, G.mul_assoc g a (G.inv a), G.mul_inv, G.mul_one]
  rw [key] at h1
  exact h1

/-- **定理 (M148F-3c): core(H) は正規部分群** —
    ∀ b g, g ∈ core(H) ⟹ bgb⁻¹ ∈ core(H)。 -/
theorem core_normal (G : Grp) (H : Subgroup G) :
    ∀ b g, coreMem G H g → coreMem G H (G.mul (G.mul b g) (G.inv b)) := by
  intro b g hg a
  have h1 := hg (G.mul (G.inv b) a)
  rw [G.inv_mul_rev, G.inv_inv,
    ← G.mul_assoc (G.mul (G.mul (G.inv a) b) g) (G.inv b) a,
    G.mul_assoc (G.inv a) b g,
    G.mul_assoc (G.inv a) (G.mul b g) (G.inv b)] at h1
  exact h1

/-! ## §3 支配射 G/core(H) ↠ G/H（M148F-4） -/

/-- **支配写像 (M148F-4a)**: core(H) ⊆ H（M148F-2）から剰余類
    同値が細分になるので Quot.lift で降りる。 -/
def coreToCoset (G : Grp) (H : Subgroup G) :
    cosetSpace G (coreSubgroup G H) → cosetSpace G H :=
  Quot.lift (fun a => Quot.mk (cosetRel G H) a)
    (fun _ _ hab => Quot.sound (core_le G H _ hab))

/-- **支配射 (M148F-4b)**: coreToCoset は同変（被覆の射）。 -/
def coreDominates (G : Grp) (H : Subgroup G) :
    ActHom (cosetAction G (coreSubgroup G H)) (cosetAction G H) where
  map := coreToCoset G H
  equivariant := by
    intro g x
    induction x using Quot.ind
    rfl

/-- 同変性の言明（M148F-4b の再掲、ActHom フィールドの外出し）。 -/
theorem coreToCoset_equivariant (G : Grp) (H : Subgroup G)
    (g : G.carrier) (x : cosetSpace G (coreSubgroup G H)) :
    coreToCoset G H ((cosetAction G (coreSubgroup G H)).act g x)
      = (cosetAction G H).act g (coreToCoset G H x) :=
  (coreDominates G H).equivariant g x

/-- **定理 (M148F-4c): 支配射は全射** — 代表元をそのまま持ち上げる。 -/
theorem coreToCoset_surjective (G : Grp) (H : Subgroup G) :
    ∀ y, ∃ x, (coreDominates G H).map x = y := by
  intro y
  induction y using Quot.ind; rename_i a
  exact ⟨Quot.mk (cosetRel G (coreSubgroup G H)) a, rfl⟩

/-- **定理 (M148F-4d): M16-6 Galois 対応のインスタンス化** —
    core(H) ⊆ H なので基点付き同変写像 G/core(H) → G/H が存在
    （coset_hom_iff の射側をそのまま適用）。 -/
theorem core_hom_pointed (G : Grp) (H : Subgroup G) :
    ∃ φ : ActHom (cosetAction G (coreSubgroup G H)) (cosetAction G H),
      φ.map (Quot.mk (cosetRel G (coreSubgroup G H)) G.one)
        = Quot.mk (cosetRel G H) G.one :=
  (coset_hom_iff G (coreSubgroup G H) H).mpr (core_le G H)

/-! ## §4 ガロア性・安定化群の読み（M148F-5, M148F-6） -/

/-- **補題 (M148F-5): 剰余類の安定化群の計算（一般形）** —
    G/K の点 [a] の安定化群への g の所属 ⟺ a⁻¹ga ∈ K。
    （安定化群 = aKa⁻¹、軌道-安定化定理の局所形。） -/
theorem coset_stabilizer_mem (G : Grp) (K : Subgroup G) (a g : G.carrier) :
    (stabilizer G (cosetAction G K) (Quot.mk (cosetRel G K) a)).mem g
    ↔ K.mem (G.mul (G.mul (G.inv a) g) a) := by
  constructor
  · intro hstab
    have h' : Quot.mk (cosetRel G K) (G.mul g a)
        = Quot.mk (cosetRel G K) a := hstab
    have h2 := quot_exact_of_equiv (cosetRel G K)
      (cosetRel_refl G K) (fun hab => cosetRel_symm G K hab)
      (fun hab hbc => cosetRel_trans G K hab hbc) h'
    have h2' : K.mem (G.mul (G.inv (G.mul g a)) a) := h2
    have h3 := K.inv_mem h2'
    rw [G.inv_mul_rev, G.inv_inv, ← G.mul_assoc] at h3
    exact h3
  · intro hK
    show Quot.mk (cosetRel G K) (G.mul g a) = Quot.mk (cosetRel G K) a
    apply Quot.sound
    show K.mem (G.mul (G.inv (G.mul g a)) a)
    rw [G.inv_mul_rev, G.mul_assoc]
    have h3 := K.inv_mem hK
    rw [G.inv_mul_rev, G.inv_mul_rev, G.inv_inv] at h3
    exact h3

/-- **定理 (M148F-6a): G/core(H) の安定化群は基点によらず core(H)**
    — 正規性（M148F-3）により a⁻¹ga ∈ core ⟺ g ∈ core。
    「ガロア対象 = 全ファイバー点で同じ（正規な）安定化群」の
    モデル実現。 -/
theorem core_stabilizer (G : Grp) (H : Subgroup G) (a g : G.carrier) :
    (stabilizer G (cosetAction G (coreSubgroup G H))
        (Quot.mk (cosetRel G (coreSubgroup G H)) a)).mem g
    ↔ coreMem G H g := by
  constructor
  · intro h
    exact coreMem_of_conj G H a
      ((coset_stabilizer_mem G (coreSubgroup G H) a g).mp h)
  · intro h
    exact (coset_stabilizer_mem G (coreSubgroup G H) a g).mpr
      (coreMem_conj G H a h)

/-- **定理 (M148F-6b): 全点版** — G/core(H) の**任意の**点 x の
    安定化群が core(H) に一致する（Quot.ind で代表に還元）。 -/
theorem core_stabilizer_all (G : Grp) (H : Subgroup G) :
    ∀ (x : cosetSpace G (coreSubgroup G H)) (g : G.carrier),
      (stabilizer G (cosetAction G (coreSubgroup G H)) x).mem g
      ↔ coreMem G H g := by
  intro x g
  induction x using Quot.ind; rename_i a
  exact core_stabilizer G H a g

/-! ## §5 ガロア性・自己同型の読み（M148F-7） -/

/-- **補題 (M148F-7a): 右移動は core の剰余類同値を保つ** —
    (ac)⁻¹(bc) = c⁻¹(a⁻¹b)c と正規性（M148F-3a）。
    正規部分群でのみ右移動が剰余類空間に降りる。 -/
theorem cosetRel_right_core (G : Grp) (H : Subgroup G) (c : G.carrier)
    {a b : G.carrier} (h : cosetRel G (coreSubgroup G H) a b) :
    cosetRel G (coreSubgroup G H) (G.mul a c) (G.mul b c) := by
  have h' : coreMem G H (G.mul (G.inv a) b) := h
  have h1 := coreMem_conj G H c h'
  show coreMem G H (G.mul (G.inv (G.mul a c)) (G.mul b c))
  rw [G.inv_mul_rev, ← G.mul_assoc (G.mul (G.inv c) (G.inv a)) b c,
    G.mul_assoc (G.inv c) (G.inv a) b]
  exact h1

/-- **自己同変写像 (M148F-7b)**: 右移動 [a] ↦ [ac] は G/core(H) の
    同変自己写像（左作用と右移動は可換）。 -/
def coreRightMul (G : Grp) (H : Subgroup G) (c : G.carrier) :
    ActHom (cosetAction G (coreSubgroup G H))
      (cosetAction G (coreSubgroup G H)) where
  map := Quot.lift
    (fun a => Quot.mk (cosetRel G (coreSubgroup G H)) (G.mul a c))
    (fun _ _ hab => Quot.sound (cosetRel_right_core G H c hab))
  equivariant := by
    intro g x
    induction x using Quot.ind; rename_i a
    show Quot.mk (cosetRel G (coreSubgroup G H)) (G.mul (G.mul g a) c)
      = Quot.mk (cosetRel G (coreSubgroup G H)) (G.mul g (G.mul a c))
    rw [G.mul_assoc]

/-- **補題 (M148F-7c): 右移動は可逆（左逆）** — c⁻¹ の右移動が
    c の右移動を打ち消す（自己**同型**であること）。 -/
theorem coreRightMul_left_inv (G : Grp) (H : Subgroup G) (c : G.carrier) :
    ∀ x, (coreRightMul G H (G.inv c)).map ((coreRightMul G H c).map x) = x := by
  intro x
  induction x using Quot.ind; rename_i a
  show Quot.mk (cosetRel G (coreSubgroup G H)) (G.mul (G.mul a c) (G.inv c))
    = Quot.mk (cosetRel G (coreSubgroup G H)) a
  rw [G.mul_assoc, G.mul_inv, G.mul_one]

/-- **補題 (M148F-7d): 右移動は可逆（右逆）**。 -/
theorem coreRightMul_right_inv (G : Grp) (H : Subgroup G) (c : G.carrier) :
    ∀ x, (coreRightMul G H c).map ((coreRightMul G H (G.inv c)).map x) = x := by
  intro x
  induction x using Quot.ind; rename_i a
  show Quot.mk (cosetRel G (coreSubgroup G H)) (G.mul (G.mul a (G.inv c)) c)
    = Quot.mk (cosetRel G (coreSubgroup G H)) a
  rw [G.mul_assoc, G.inv_mul, G.mul_one]

/-- **定理 (M148F-7e): 自己同変写像はファイバーに推移的** —
    任意の [a], [b] に対し c := a⁻¹b の右移動が [a] を [b] に送る。
    M21 の IsGalois「自己同型のファイバーへの推移性」のモデル実現
    （G/core(H) のガロア性・自己同型の読み）。 -/
theorem core_aut_transitive (G : Grp) (H : Subgroup G) :
    ∀ x y : cosetSpace G (coreSubgroup G H),
      ∃ c, (coreRightMul G H c).map x = y := by
  intro x y
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  refine ⟨G.mul (G.inv a) b, ?_⟩
  show Quot.mk (cosetRel G (coreSubgroup G H))
      (G.mul a (G.mul (G.inv a) b))
    = Quot.mk (cosetRel G (coreSubgroup G H)) b
  rw [← G.mul_assoc, G.mul_inv, G.one_mul]

/-! ## §6 総合定理（M148F-8） -/

/-- **定理 (M148F-8a): ガロア閉包・モデル側の総合定理** —
    任意の剰余類対象 G/H は、正規部分群 N = core(H) による剰余類
    対象 G/N から同変全射で支配され、G/N はガロア
    （全点の安定化群 = N、かつ自己同変写像がファイバーに推移的）。 -/
theorem galois_closure_model (G : Grp) (H : Subgroup G) :
    ∃ N : Subgroup G,
      (∀ g, N.mem g → H.mem g) ∧
      (∀ b g, N.mem g → N.mem (G.mul (G.mul b g) (G.inv b))) ∧
      (∃ φ : ActHom (cosetAction G N) (cosetAction G H),
        ∀ y, ∃ x, φ.map x = y) ∧
      (∀ (x : cosetSpace G N) (g : G.carrier),
        (stabilizer G (cosetAction G N) x).mem g ↔ N.mem g) ∧
      (∀ x y : cosetSpace G N,
        ∃ ψ : ActHom (cosetAction G N) (cosetAction G N), ψ.map x = y) := by
  refine ⟨coreSubgroup G H, core_le G H, core_normal G H,
    ⟨coreDominates G H, coreToCoset_surjective G H⟩,
    core_stabilizer_all G H, ?_⟩
  intro x y
  obtain ⟨c, hc⟩ := core_aut_transitive G H x y
  exact ⟨coreRightMul G H c, hc⟩

/-- **総括データ (M148F-8b)**: ガロア閉包・モデル側の全部品。 -/
structure GaloisClosureModelData (G : Grp) (H : Subgroup G) where
  /-- ガロア閉包を与える部分群（core(H)）。 -/
  N : Subgroup G
  /-- N ⊆ H（M148F-2）。 -/
  le : ∀ g, N.mem g → H.mem g
  /-- N の正規性（M148F-3c）。 -/
  normal : ∀ b g, N.mem g → N.mem (G.mul (G.mul b g) (G.inv b))
  /-- 支配射 G/N → G/H（M148F-4b）。 -/
  dom : ActHom (cosetAction G N) (cosetAction G H)
  /-- 支配射の全射性（M148F-4c）。 -/
  dom_surj : ∀ y, ∃ x, dom.map x = y
  /-- ガロア性・安定化群の読み: 全点で Stab = N（M148F-6b）。 -/
  stab : ∀ (x : cosetSpace G N) (g : G.carrier),
    (stabilizer G (cosetAction G N) x).mem g ↔ N.mem g
  /-- ガロア性・自己同型の読み: 自己同変写像の推移性（M148F-7e）。 -/
  aut_trans : ∀ x y : cosetSpace G N,
    ∃ ψ : ActHom (cosetAction G N) (cosetAction G N), ψ.map x = y

/-- **証人 (M148F-8c)**: N := core(H) が全条件を満たす。 -/
def galoisClosureModelWitness (G : Grp) (H : Subgroup G) :
    GaloisClosureModelData G H where
  N := coreSubgroup G H
  le := core_le G H
  normal := core_normal G H
  dom := coreDominates G H
  dom_surj := coreToCoset_surjective G H
  stab := core_stabilizer_all G H
  aut_trans := fun x y => by
    obtain ⟨c, hc⟩ := core_aut_transitive G H x y
    exact ⟨coreRightMul G H c, hc⟩

/-- **定理 (M148F-8d): ガロア閉包データの存在**（無矛盾性）。 -/
theorem galoisClosureModel_exists (G : Grp) (H : Subgroup G) :
    Nonempty (GaloisClosureModelData G H) :=
  ⟨galoisClosureModelWitness G H⟩

end IUT
