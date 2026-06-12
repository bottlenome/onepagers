/-
  IUT/SGA1.lean — M16（SGA1 主定理の核心: 被覆の分類定理）の形式化

  Galois 圏の主定理（SGA1 V.4–V.7）は「ファイバー関手 F を持つ
  Galois 圏 C は π₁ := Aut(F) の有限連続作用の圏と同値」と主張する。
  M14 でファイバー関手の復元機構 Aut(F) ≅ G を証明した。本モジュール
  はその続き——主定理の**対象・射の分類**にあたる三つの柱——を
  完全証明する:

  §1 群論の補強: 逆元の反転則・部分群・剰余類
  * M16-1 `Grp.inv_mul_rev` / `Grp.inv_inv` — 逆元の計算則（公理ゼロ）
  * M16-2 `cosetAction` — 部分群 H に対する剰余類作用 G/H の構成
    （剰余類同値 a ~ b ↔ a⁻¹b ∈ H が同値関係で左移動と両立する
    ことの完全証明）

  §2 主定理・対象側: **全ての軌道は剰余類作用に同型**
  * M16-3 `orbitOf` / `orbit_transitive` — 任意の G-集合は軌道に
    分解し、各軌道は推移的（連結成分分解）
  * M16-4 `orbit_stabilizer` — **軌道-安定化定理**: 推移的 G-集合 X
    と基点 x₀ に対し G/Stab(x₀) ≅ X（同変全単射）。
    Galois 圏で言えば「全ての連結被覆は G/H の形」——主定理の
    対象側の本体
  * M16-5 `every_orbit_is_coset` — M16-3 + M16-4 の合成: 任意の
    G-集合の任意の軌道は剰余類作用に同変同型

  §3 主定理・射側: **Galois 対応の実現**
  * M16-6 `coset_hom_iff` — 基点付き同変写像 G/H → G/K が存在する
    ⟺ H ⊆ K。M14 の抽象 Galois 接続（M14-7〜10）が、実際の
    部分群と剰余類作用で実現されることの完全証明（対応定理の
    射側の本体）

  §4 連続性条件（M15 との接続）: SGA1 の「π₁ の**連続**作用」
  * M16-7 `SmoothAction` / `levelAction_smooth` — 副有限群の作用が
    連続 ⟺ 各点の安定化群が開（射影核を含む）。有限レベル作用が
    この条件を満たすことの証明
  * M16-8 `levelAction_stabilizer_open` — 安定化群は M15 の意味で
    開な部分群を含む（SGA1 の連続性条件の機械検証）

  **位置づけ（正直な申告）**: SGA1 の Galois 圏の公理系（圏論的
  公理 G1–G6）と、それを満たす圏とファイバー関手から上記分類を
  経由して圏同値を組み立てる関手的パッケージングは未形式化。
  対象の分類（軌道 = 剰余類）・射の分類（Galois 対応）・連続性
  条件という主定理の数学的内容の三本柱は本モジュールで完全証明
  された。残る実質は「双曲的曲線の有限 étale 被覆の圏が Galois 圏
  をなす」という幾何的入力である。
-/
import IUT.GaloisCategory
import IUT.Topology

namespace IUT

/-! ## §1 群論の補強と剰余類作用 -/

/-- **定理 (M16-1a)**: 積の逆元は逆順の積（公理ゼロ）。 -/
theorem Grp.inv_mul_rev (G : Grp) (x y : G.carrier) :
    G.inv (G.mul x y) = G.mul (G.inv y) (G.inv x) := by
  have h : G.mul (G.mul x y) (G.mul (G.inv y) (G.inv x)) = G.one := by
    rw [G.mul_assoc, ← G.mul_assoc y (G.inv y) (G.inv x),
      G.mul_inv, G.one_mul, G.mul_inv]
  exact (G.inv_eq_of_mul_eq_one h).symm

/-- **定理 (M16-1b)**: 逆元の逆元（公理ゼロ）。 -/
theorem Grp.inv_inv (G : Grp) (a : G.carrier) : G.inv (G.inv a) = a :=
  (G.inv_eq_of_mul_eq_one (G.inv_mul a)).symm

/-- 部分群。 -/
structure Subgroup (G : Grp) where
  mem : G.carrier → Prop
  one_mem : mem G.one
  mul_mem : ∀ {a b}, mem a → mem b → mem (G.mul a b)
  inv_mem : ∀ {a}, mem a → mem (G.inv a)

/-- 剰余類の同値関係: a ~ b ⟺ a⁻¹b ∈ H。 -/
def cosetRel (G : Grp) (H : Subgroup G) (a b : G.carrier) : Prop :=
  H.mem (G.mul (G.inv a) b)

theorem cosetRel_refl (G : Grp) (H : Subgroup G) (a : G.carrier) :
    cosetRel G H a a := by
  show H.mem (G.mul (G.inv a) a)
  rw [G.inv_mul]
  exact H.one_mem

theorem cosetRel_symm (G : Grp) (H : Subgroup G) {a b : G.carrier}
    (h : cosetRel G H a b) : cosetRel G H b a := by
  have h1 := H.inv_mem h
  rw [G.inv_mul_rev, G.inv_inv] at h1
  exact h1

theorem cosetRel_trans (G : Grp) (H : Subgroup G) {a b c : G.carrier}
    (h1 : cosetRel G H a b) (h2 : cosetRel G H b c) : cosetRel G H a c := by
  have h3 := H.mul_mem h1 h2
  rw [G.mul_assoc, ← G.mul_assoc b (G.inv b) c, G.mul_inv, G.one_mul] at h3
  exact h3

/-- 剰余類同値は左移動と両立する。 -/
theorem cosetRel_left (G : Grp) (H : Subgroup G) (g : G.carrier)
    {a b : G.carrier} (h : cosetRel G H a b) :
    cosetRel G H (G.mul g a) (G.mul g b) := by
  show H.mem (G.mul (G.inv (G.mul g a)) (G.mul g b))
  rw [G.inv_mul_rev, G.mul_assoc, ← G.mul_assoc (G.inv g) g b,
    G.inv_mul, G.one_mul]
  exact h

/-- 剰余類空間 G/H。 -/
def cosetSpace (G : Grp) (H : Subgroup G) : Type := Quot (cosetRel G H)

/-- **剰余類作用 G/H**（M16-2）: G の左移動による作用。
    Galois 圏における「部分群 H に対応する連結被覆」。 -/
def cosetAction (G : Grp) (H : Subgroup G) : GAction G where
  carrier := cosetSpace G H
  act := fun g x =>
    Quot.lift (fun a => Quot.mk (cosetRel G H) (G.mul g a))
      (fun _ _ hab => Quot.sound (cosetRel_left G H g hab)) x
  act_one := by
    intro x
    induction x using Quot.ind; rename_i a
    show Quot.mk (cosetRel G H) (G.mul G.one a) = Quot.mk (cosetRel G H) a
    rw [G.one_mul]
  act_mul := by
    intro g h x
    induction x using Quot.ind; rename_i a
    show Quot.mk (cosetRel G H) (G.mul (G.mul g h) a)
        = Quot.mk (cosetRel G H) (G.mul g (G.mul h a))
    rw [G.mul_assoc]

/-- 同値関係の商の分離性（M13-3 の一般化、任意の同値関係版）。 -/
theorem quot_exact_of_equiv {α : Type} (r : α → α → Prop)
    (hrefl : ∀ a, r a a)
    (hsymm : ∀ {a b}, r a b → r b a)
    (htrans : ∀ {a b c}, r a b → r b c → r a c)
    {a b : α} (h : Quot.mk r a = Quot.mk r b) : r a b := by
  have hf : Quot.lift (r a)
      (fun _ _ hxy => propext
        ⟨fun hax => htrans hax hxy, fun hay => htrans hay (hsymm hxy)⟩)
      (Quot.mk r a) := hrefl a
  rw [h] at hf
  exact hf

/-! ## §2 主定理・対象側: 軌道の分類 -/

/-- 安定化部分群 Stab(x)。 -/
def stabilizer (G : Grp) (X : GAction G) (x : X.carrier) : Subgroup G where
  mem := fun g => X.act g x = x
  one_mem := X.act_one x
  mul_mem := fun {a b} ha hb => by
    rw [X.act_mul, hb, ha]
  inv_mem := fun {a} ha => by
    calc X.act (G.inv a) x
        = X.act (G.inv a) (X.act a x) := by rw [ha]
      _ = X.act (G.mul (G.inv a) a) x := (X.act_mul _ _ x).symm
      _ = x := by rw [G.inv_mul, X.act_one]

/-- 推移性（連結被覆のファイバーの条件）。 -/
def GAction.Transitive {G : Grp} (X : GAction G) : Prop :=
  ∀ x y : X.carrier, ∃ g, X.act g x = y

/-- **定理 (M16-4): 軌道-安定化定理（主定理・対象側）** —
    推移的 G-集合 X と基点 x₀ に対し、[g] ↦ g·x₀ は同変全単射
    G/Stab(x₀) ≅ X を与える。Galois 圏で言えば
    **「全ての連結被覆は G/H の形」**。 -/
theorem orbit_stabilizer (G : Grp) (X : GAction G) (x₀ : X.carrier)
    (htrans : X.Transitive) :
    ∃ φ : ActHom (cosetAction G (stabilizer G X x₀)) X,
      (∀ p q, φ.map p = φ.map q → p = q) ∧
      (∀ y, ∃ p, φ.map p = y) := by
  have key : ∀ g g', cosetRel G (stabilizer G X x₀) g g' →
      X.act g x₀ = X.act g' x₀ := by
    intro g g' h
    have h2 := congrArg (X.act g) h
    rw [← X.act_mul, ← G.mul_assoc, G.mul_inv, G.one_mul] at h2
    exact h2.symm
  refine ⟨{ map := Quot.lift (fun g => X.act g x₀) key,
            equivariant := ?_ }, ?_, ?_⟩
  · intro g x
    induction x using Quot.ind; rename_i a
    show X.act (G.mul g a) x₀ = X.act g (X.act a x₀)
    exact X.act_mul g a x₀
  · intro p q h
    induction p using Quot.ind; rename_i g
    induction q using Quot.ind; rename_i g'
    apply Quot.sound
    show X.act (G.mul (G.inv g) g') x₀ = x₀
    have h2 := congrArg (X.act (G.inv g)) h
    rw [← X.act_mul, ← X.act_mul, G.inv_mul, X.act_one] at h2
    exact h2.symm
  · intro y
    obtain ⟨g, hg⟩ := htrans x₀ y
    exact ⟨Quot.mk _ g, hg⟩

/-- 軌道関係 x ~ y ⟺ ∃ g, g·x = y。 -/
def orbitRel {G : Grp} (X : GAction G) (x y : X.carrier) : Prop :=
  ∃ g, X.act g x = y

theorem orbitRel_refl {G : Grp} (X : GAction G) (x : X.carrier) :
    orbitRel X x x :=
  ⟨G.one, X.act_one x⟩

/-- **軌道**（M16-3）: x₀ の軌道への作用の制限（連結成分）。 -/
def orbitOf {G : Grp} (X : GAction G) (x₀ : X.carrier) : GAction G where
  carrier := { y : X.carrier // orbitRel X x₀ y }
  act := fun g y => ⟨X.act g y.val, by
    obtain ⟨h, hh⟩ := y.property
    exact ⟨G.mul g h, by rw [X.act_mul, hh]⟩⟩
  act_one := fun y => Subtype.ext (X.act_one y.val)
  act_mul := fun g h y => Subtype.ext (X.act_mul g h y.val)

/-- **定理 (M16-3): 軌道は推移的**（連結性）。任意の G-集合は
    軌道（連結成分）に分解し、各成分は推移的である。 -/
theorem orbit_transitive {G : Grp} (X : GAction G) (x₀ : X.carrier) :
    (orbitOf X x₀).Transitive := by
  intro y z
  obtain ⟨g, hg⟩ := y.property
  obtain ⟨h, hh⟩ := z.property
  refine ⟨G.mul h (G.inv g), Subtype.ext ?_⟩
  show X.act (G.mul h (G.inv g)) y.val = z.val
  rw [← hg, ← X.act_mul, G.mul_assoc, G.inv_mul, G.mul_one, hh]

/-- **定理 (M16-5): 全ての軌道は剰余類作用に同型**（M16-3 + M16-4）—
    任意の G-集合の任意の点の軌道は、その安定化群の剰余類作用と
    同変全単射で結ばれる。SGA1 主定理の対象側の分類が完結する。 -/
theorem every_orbit_is_coset {G : Grp} (X : GAction G) (x₀ : X.carrier) :
    ∃ φ : ActHom
        (cosetAction G (stabilizer G (orbitOf X x₀) ⟨x₀, orbitRel_refl X x₀⟩))
        (orbitOf X x₀),
      (∀ p q, φ.map p = φ.map q → p = q) ∧
      (∀ y, ∃ p, φ.map p = y) :=
  orbit_stabilizer G (orbitOf X x₀) ⟨x₀, orbitRel_refl X x₀⟩
    (orbit_transitive X x₀)

/-! ## §3 主定理・射側: Galois 対応の実現 -/

/-- **定理 (M16-6): Galois 対応の実現（主定理・射側）** —
    基点付き同変写像 G/H → G/K が存在する ⟺ H ⊆ K。
    M14 の抽象 Galois 接続が実際の部分群・剰余類作用の対で
    実現される。「被覆の射 ⟷ 部分群の包含（反変）」の完全証明。 -/
theorem coset_hom_iff (G : Grp) (H K : Subgroup G) :
    (∃ φ : ActHom (cosetAction G H) (cosetAction G K),
        φ.map (Quot.mk (cosetRel G H) G.one) = Quot.mk (cosetRel G K) G.one) ↔
    (∀ h, H.mem h → K.mem h) := by
  constructor
  · intro ⟨φ, hφ⟩ h hH
    -- [h]_H = [1]_H なので φ の値も等しい
    have h1 : Quot.mk (cosetRel G H) h = Quot.mk (cosetRel G H) G.one := by
      apply Quot.sound
      show H.mem (G.mul (G.inv h) G.one)
      rw [G.mul_one]
      exact H.inv_mem hH
    -- 同変性: φ[h] = φ(h·[1]) = h·φ[1] = h·[1]_K = [h]_K
    have h2 : φ.map (Quot.mk (cosetRel G H) h) = Quot.mk (cosetRel G K) h := by
      have h3 : Quot.mk (cosetRel G H) h
          = (cosetAction G H).act h (Quot.mk (cosetRel G H) G.one) := by
        show Quot.mk (cosetRel G H) h = Quot.mk (cosetRel G H) (G.mul h G.one)
        rw [G.mul_one]
      rw [h3, φ.equivariant, hφ]
      show Quot.mk (cosetRel G K) (G.mul h G.one) = Quot.mk (cosetRel G K) h
      rw [G.mul_one]
    -- よって [h]_K = [1]_K、分離性から h ∈ K
    rw [h1, hφ] at h2
    have h4 := quot_exact_of_equiv (cosetRel G K)
      (cosetRel_refl G K) (fun hab => cosetRel_symm G K hab)
      (fun hab hbc => cosetRel_trans G K hab hbc) h2.symm
    -- h4 : K.mem (h⁻¹ · 1)
    have h4' : K.mem (G.mul (G.inv h) G.one) := h4
    rw [G.mul_one] at h4'
    have h5 := K.inv_mem h4'
    rw [G.inv_inv] at h5
    exact h5
  · intro hHK
    have wd : ∀ a b, cosetRel G H a b →
        Quot.mk (cosetRel G K) a = Quot.mk (cosetRel G K) b :=
      fun _ _ hab => Quot.sound (hHK _ hab)
    refine ⟨{ map := Quot.lift (fun a => Quot.mk (cosetRel G K) a) wd,
              equivariant := ?_ }, rfl⟩
    intro g x
    induction x using Quot.ind
    rfl

/-! ## §4 連続性条件（SGA1 の「連続な π₁-作用」、M15 接続） -/

/-- **滑らかな（連続な）作用**: 各点の安定化群がある射影核を含む。
    SGA1 が要求する「π₁ の有限集合への**連続**作用」の条件。 -/
def SmoothAction (S : InverseSystem) (X : GAction (limitGrp S)) : Prop :=
  ∀ x : X.carrier, ∃ i, ∀ σ : (limitGrp S).carrier,
    projKernel S i σ → X.act σ x = x

/-- **定理 (M16-7): 有限レベル作用は滑らか** — π₁^ét の各有限
    レベルへの作用（M14-5）は連続性条件を満たす。 -/
theorem levelAction_smooth (S : InverseSystem) (i : S.Idx) :
    SmoothAction S (levelAction S i) := by
  intro x
  refine ⟨i, fun σ hσ => ?_⟩
  show (S.G i).mul (σ.val i) x = x
  rw [hσ, (S.G i).one_mul]

/-- **定理 (M16-8): 安定化群は開部分群を含む**（SGA1 の連続性
    条件の位相的表現、M15 + M16 の接続）— 有限レベル作用の各点の
    安定化群は、開（M15-5a）かつ 1 を含む集合（射影核）を含む。 -/
theorem levelAction_stabilizer_open (S : InverseSystem) (i : S.Idx)
    (x : (S.G i).carrier) :
    ∃ U : (limitGrp S).carrier → Prop,
      (limitTopology S).IsOpen U ∧ U (limitGrp S).one ∧
      ∀ σ, U σ → (levelAction S i).act σ x = x := by
  refine ⟨projKernel S i, projKernel_isOpen S i, projKernel_one S i,
    fun σ hσ => ?_⟩
  show (S.G i).mul (σ.val i) x = x
  rw [hσ, (S.G i).one_mul]

end IUT
