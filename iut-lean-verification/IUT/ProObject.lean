/-
  IUT/ProObject.lean — M24（pro-対象: ガロア塔と π₁ の副有限構成）

  SGA1 の π₁ はガロア対象たちの自己同型群の逆極限（pro-有限群）で
  ある。本モジュールはその pro-構造を公理から構成する:

  * M24-1 `aut_transition_exists_unique` — 支配射 p : B → A（両者
    ガロア）に沿って Aut(B) の元は p∘τ = σ∘p なる τ ∈ Aut(A) を
    **一意に**誘導（存在 = ガロア推移性、一意性 = evaluation 単射性）
  * M24-2 `aut_transition_surjective` — 遷移は**全射**
    （π₁ ↠ 有限ガロア群の古典的全射性。F p の全射性は A の連結性
    M22-4a から従う）
  * M24-3 `natSystem` — Nat 鎖から逆系（M13）を作る汎用構成子
  * M24-4 `GaloisTower` / `autTransition` / `towerSystem` /
    `pi1Tower` — **ガロア塔の自己同型群の逆系と π₁ = limitGrp(塔)**。
    遷移は一意性から群準同型になり、整合性（t_self/t_comp）も
    一意性から従う。M13 の普遍性・M15 の位相（位相群性・開近傍基）
    が π₁ に自動適用される（`pi1Tower_mul_continuous`）
  * M24-5 `unitAction_galois` / `galoisTower_consistent` — 無矛盾性
    （自明群上の自明塔。unitAction のガロア性の完全証明込み）

  正直な申告: ガロア閉包（任意の連結対象がガロア対象に支配される
  こと = 塔の存在・十分性）は未形式化の入力（塔は構造体データ）。
  遷移の抽出は Classical.choice（∃! からの関数化）。
-/
import IUT.SGA1Object

namespace IUT

universe u

namespace GaloisCatData

variable (D : GaloisCatData.{u, 0})

/-- **定理 (M24-1): 自己同型の遷移の存在と一意性**。 -/
theorem aut_transition_exists_unique {B A : D.C.Obj}
    (hB : D.IsGalois B) (hA : D.IsGalois A) (p : D.C.Hom B A)
    (b₀ : D.F.onObj B) (σ : CatIso D.C B B) :
    ∃ τ : CatIso D.C A A, D.C.comp p τ.hom = D.C.comp σ.hom p ∧
      ∀ τ' : CatIso D.C A A,
        D.C.comp p τ'.hom = D.C.comp σ.hom p → τ' = τ := by
  obtain ⟨τ, hτ⟩ := D.galois_trans_iso hA (D.F.onHom p b₀)
    (D.F.onHom p (D.F.onHom σ.hom b₀))
  have heq : D.C.comp p τ.hom = D.C.comp σ.hom p := by
    apply D.evaluation_injective hB.1 b₀
    rw [D.fmap_comp, D.fmap_comp, hτ]
  refine ⟨τ, heq, ?_⟩
  intro τ' hτ'
  apply CatIso.ext
  apply D.evaluation_injective hA.1 (D.F.onHom p b₀)
  have h1 : D.F.onHom (D.C.comp p τ'.hom) b₀
      = D.F.onHom (D.C.comp p τ.hom) b₀ := by rw [hτ', heq]
  rw [D.fmap_comp, D.fmap_comp] at h1
  exact h1

/-- **定理 (M24-2): 遷移の全射性**（π₁ ↠ 有限ガロア群）。 -/
theorem aut_transition_surjective {B A : D.C.Obj}
    (hB : D.IsGalois B) (hA : D.IsGalois A) (p : D.C.Hom B A)
    (b₀ : D.F.onObj B) (τ : CatIso D.C A A) :
    ∃ σ : CatIso D.C B B, D.C.comp p τ.hom = D.C.comp σ.hom p := by
  obtain ⟨b₁, hb₁⟩ := D.connected_hom_surjective hA.1 p b₀
    (D.F.onHom τ.hom (D.F.onHom p b₀))
  obtain ⟨σ, hσ⟩ := D.galois_trans_iso hB b₀ b₁
  refine ⟨σ, ?_⟩
  apply D.evaluation_injective hB.1 b₀
  rw [D.fmap_comp, D.fmap_comp, hσ, hb₁]

end GaloisCatData

/-- **Nat 鎖からの逆系の汎用構成子**（M24-3）。 -/
@[reducible] def natSystem (G : Nat → Grp)
    (P : ∀ {i j : Nat}, i ≤ j → Hom (G j) (G i))
    (hself : ∀ (i : Nat) (x : (G i).carrier), (P (Nat.le_refl i)).map x = x)
    (hcomp : ∀ {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k)
      (x : (G k).carrier),
      (P hij).map ((P hjk).map x) = (P (Nat.le_trans hij hjk)).map x) :
    InverseSystem where
  Idx := Nat
  le := (· ≤ ·)
  le_refl := Nat.le_refl
  le_trans := fun h1 h2 => Nat.le_trans h1 h2
  directed := fun i j => ⟨max i j, Nat.le_max_left i j, Nat.le_max_right i j⟩
  G := G
  t := P
  t_self := hself
  t_comp := hcomp

/-- **ガロア塔**（M24-4a）: ガロア対象の Nat 鎖と整合的な支配射の族。 -/
structure GaloisTower (D : GaloisCatData.{u, 0}) where
  A : Nat → D.C.Obj
  pt : ∀ n, D.F.onObj (A n)
  hGal : ∀ n, D.IsGalois (A n)
  P : ∀ {i j : Nat}, i ≤ j → D.C.Hom (A j) (A i)
  P_self : ∀ (i : Nat) (h : i ≤ i), P h = D.C.id (A i)
  P_comp : ∀ {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k),
    D.C.comp (P hjk) (P hij) = P (Nat.le_trans hij hjk)
  P_pt : ∀ {i j : Nat} (h : i ≤ j), D.F.onHom (P h) (pt j) = pt i

namespace GaloisTower

variable {D : GaloisCatData.{u, 0}} (T : GaloisTower D)

/-- 遷移の生関数（M24-1 の一意な τ の抽出、Classical.choice）。 -/
noncomputable def transAut {i j : Nat} (h : i ≤ j)
    (σ : CatIso D.C (T.A j) (T.A j)) : CatIso D.C (T.A i) (T.A i) :=
  Classical.choose
    (D.aut_transition_exists_unique (T.hGal j) (T.hGal i) (T.P h) (T.pt j) σ)

theorem transAut_spec {i j : Nat} (h : i ≤ j)
    (σ : CatIso D.C (T.A j) (T.A j)) :
    D.C.comp (T.P h) (T.transAut h σ).hom = D.C.comp σ.hom (T.P h) :=
  (Classical.choose_spec (D.aut_transition_exists_unique
    (T.hGal j) (T.hGal i) (T.P h) (T.pt j) σ)).1

theorem transAut_unique {i j : Nat} (h : i ≤ j)
    (σ : CatIso D.C (T.A j) (T.A j)) (τ : CatIso D.C (T.A i) (T.A i))
    (hτ : D.C.comp (T.P h) τ.hom = D.C.comp σ.hom (T.P h)) :
    τ = T.transAut h σ :=
  (Classical.choose_spec (D.aut_transition_exists_unique
    (T.hGal j) (T.hGal i) (T.P h) (T.pt j) σ)).2 τ hτ

/-- 遷移は群準同型（一意性から）。 -/
theorem transAut_mul {i j : Nat} (h : i ≤ j)
    (σ σ' : CatIso D.C (T.A j) (T.A j)) :
    T.transAut h ((D.autGrp (T.A j)).mul σ σ')
      = (D.autGrp (T.A i)).mul (T.transAut h σ) (T.transAut h σ') := by
  refine ((T.transAut_unique h ((D.autGrp (T.A j)).mul σ σ') _ ?_)).symm
  show D.C.comp (T.P h)
      (D.C.comp (T.transAut h σ).hom (T.transAut h σ').hom)
    = D.C.comp (D.C.comp σ.hom σ'.hom) (T.P h)
  rw [← D.C.assoc, T.transAut_spec h σ, D.C.assoc, T.transAut_spec h σ',
    ← D.C.assoc]

/-- **遷移準同型 Aut(A_j) → Aut(A_i)**（M24-4b）。 -/
noncomputable def autTransition {i j : Nat} (h : i ≤ j) :
    Hom (D.autGrp (T.A j)) (D.autGrp (T.A i)) :=
  ⟨T.transAut h, T.transAut_mul h⟩

/-- **塔の逆系**（M24-4c）: Aut(A_n) たちの逆系。整合性は一意性から。 -/
noncomputable def towerSystem : InverseSystem :=
  natSystem (fun n => D.autGrp (T.A n)) (fun h => T.autTransition h)
    (fun i σ => by
      have hcand : D.C.comp (T.P (Nat.le_refl i)) σ.hom
          = D.C.comp σ.hom (T.P (Nat.le_refl i)) := by
        rw [T.P_self i (Nat.le_refl i), D.C.id_comp, D.C.comp_id]
      exact (T.transAut_unique (Nat.le_refl i) σ σ hcand).symm)
    (fun {i j k} hij hjk σ => by
      have hcand : D.C.comp (T.P (Nat.le_trans hij hjk))
          (T.transAut hij (T.transAut hjk σ)).hom
          = D.C.comp σ.hom (T.P (Nat.le_trans hij hjk)) := by
        rw [← T.P_comp hij hjk, D.C.assoc, T.transAut_spec hij,
          ← D.C.assoc, T.transAut_spec hjk, D.C.assoc]
      exact T.transAut_unique (Nat.le_trans hij hjk) σ _ hcand)

/-- **π₁ = ガロア塔の自己同型群の逆極限**（M24-4d）。
    M13 の普遍性・M15 の位相群性と開近傍基がそのまま適用される
    pro-有限群である。 -/
noncomputable def pi1Tower : Grp := limitGrp T.towerSystem

/-- π₁ は位相群（M15-3 の自動適用）。 -/
theorem pi1Tower_mul_continuous :
    Continuous (prodTopology (limitTopology T.towerSystem)
      (limitTopology T.towerSystem)) (limitTopology T.towerSystem)
      (fun p => T.pi1Tower.mul p.1 p.2) :=
  limit_mul_continuous T.towerSystem

end GaloisTower

/-! ## M24-5: 無矛盾性（自明群上の自明塔） -/

/-- 自明群。 -/
def punitGrp : Grp where
  carrier := PUnit
  mul := fun _ _ => PUnit.unit
  one := PUnit.unit
  inv := fun _ => PUnit.unit
  mul_assoc := fun _ _ _ => rfl
  one_mul := fun _ => rfl
  inv_mul := fun _ => rfl

/-- unitAction は（自明群のモデルで）ガロア対象である。 -/
theorem unitAction_galois :
    (gsetGaloisData punitGrp).IsGalois (unitAction punitGrp) := by
  constructor
  · -- 連結性
    refine ⟨⟨PUnit.unit⟩, ?_⟩
    intro E m hm hne
    obtain ⟨e₀⟩ := hne
    -- 定値写像（自明群なので同変）
    have hconst : ∀ σ : punitGrp.carrier, E.act σ e₀ = e₀ :=
      fun _ => E.act_one e₀
    refine ⟨⟨fun _ => e₀, fun σ _ => (hconst σ).symm⟩, ?_, ?_⟩
    · -- comp m g = id E: モノ性で id = const e₀
      have heq : (GSetCat punitGrp).comp (ActHom.idHom E) m
          = (GSetCat punitGrp).comp ⟨fun _ => e₀, fun σ _ => (hconst σ).symm⟩ m :=
        ActHom.ext (fun _ => rfl)
      have h2 := hm _ _ heq
      apply ActHom.ext
      intro e
      have h3 := congrFun (congrArg ActHom.map h2) e
      exact h3.symm
    · exact ActHom.ext (fun _ => rfl)
  · -- 推移性: 恒等同型で十分（ファイバーは一点）
    intro a b
    refine ⟨(GSetCat punitGrp).id (unitAction punitGrp),
      ⟨(GSetCat punitGrp).id _, (GSetCat punitGrp).id_comp _,
        (GSetCat punitGrp).id_comp _⟩, rfl⟩

/-- **無矛盾性**: 自明群上の自明な定値塔がガロア塔をなす。 -/
theorem galoisTower_consistent :
    Nonempty (GaloisTower (gsetGaloisData punitGrp)) := by
  refine ⟨{
    A := fun _ => unitAction punitGrp
    pt := fun _ => PUnit.unit
    hGal := fun _ => unitAction_galois
    P := fun _ => (GSetCat punitGrp).id (unitAction punitGrp)
    P_self := fun _ _ => rfl
    P_comp := fun _ _ => (GSetCat punitGrp).id_comp _
    P_pt := fun _ => rfl }⟩

end IUT
