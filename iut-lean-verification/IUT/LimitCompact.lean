/-
  IUT/LimitCompact.lean — M25（逆極限のコンパクト性）

  有限レベルの Nat 鎖逆系の極限（副有限群）が副有限位相（M15）で
  **コンパクト**であることを証明する。König の補題型の木論法:

  * M25-1 `cylCovered` / `assemble_level` — 柱状集合の有限被覆可能性と
    レベル枚挙からの大域有限被覆の組み立て
  * M25-2 `refine_step` — **木の無限枝の一歩**: レベル n の未被覆点の
    上にはレベル n+1 の未被覆点がある（さもなくば有限レベルの枚挙で
    被覆が組み上がる）
  * M25-3 `natSystem_compact` — **コンパクト性**: 有限部分被覆が
    なければ未被覆点の無限枝（König）が再帰で構成でき、その極限点の
    近傍基柱状集合（M15-6）が一member被覆を与えて矛盾。
    枝の構成に Classical.choice——**逆極限コンパクト性における
    選択原理の所在の形式的特定**
  * M25-4 `pi1Tower_compact` — ガロア塔の π₁（M24）はレベル有限なら
    コンパクト（SGA1 の π₁ が副有限**コンパクト**群であることの完成）
  * M25-5 `factChain_compact` — 具体例: **階乗鎖 ℤ/n! の極限
    （ẑ の鎖型表示）はコンパクト**
-/
import IUT.ProObject
import IUT.Compactness

namespace IUT

/-- 柱状集合（レベル n の値 = t）の有限被覆可能性。 -/
def cylCovered (S : InverseSystem)
    (Cov : ((limitGrp S).carrier → Prop) → Prop)
    (n : S.Idx) (t : (S.G n).carrier) : Prop :=
  ∃ L : List ((limitGrp S).carrier → Prop), (∀ U, U ∈ L → Cov U) ∧
    ∀ x : (limitGrp S).carrier, x.val n = t → ∃ U, U ∈ L ∧ U x

/-- **M25-1**: レベルの点のリストが全て被覆可能なら合併も有限被覆可能。 -/
theorem assemble_level (S : InverseSystem)
    (Cov : ((limitGrp S).carrier → Prop) → Prop) (n : S.Idx) :
    ∀ l : List (S.G n).carrier, (∀ t, t ∈ l → cylCovered S Cov n t) →
    ∃ L : List ((limitGrp S).carrier → Prop), (∀ U, U ∈ L → Cov U) ∧
      ∀ x : (limitGrp S).carrier, x.val n ∈ l → ∃ U, U ∈ L ∧ U x := by
  intro l
  induction l with
  | nil =>
    exact fun _ => ⟨[], fun U h => absurd h List.not_mem_nil,
      fun x h => absurd h List.not_mem_nil⟩
  | cons t l ih =>
    intro hall
    obtain ⟨L1, hL1, hcov1⟩ := hall t List.mem_cons_self
    obtain ⟨L2, hL2, hcov2⟩ := ih (fun t' ht' => hall t' (List.mem_cons_of_mem t ht'))
    refine ⟨L1 ++ L2, ?_, ?_⟩
    · intro U hU
      cases List.mem_append.mp hU with
      | inl h => exact hL1 U h
      | inr h => exact hL2 U h
    · intro x hx
      cases List.mem_cons.mp hx with
      | inl h =>
        obtain ⟨U, hUL, hUx⟩ := hcov1 x h
        exact ⟨U, List.mem_append.mpr (Or.inl hUL), hUx⟩
      | inr h =>
        obtain ⟨U, hUL, hUx⟩ := hcov2 x h
        exact ⟨U, List.mem_append.mpr (Or.inr hUL), hUx⟩

section NatChain

variable (G : Nat → Grp)
  (P : ∀ {i j : Nat}, i ≤ j → Hom (G j) (G i))
  (hself : ∀ (i : Nat) (x : (G i).carrier), (P (Nat.le_refl i)).map x = x)
  (hcomp : ∀ {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) (x : (G k).carrier),
    (P hij).map ((P hjk).map x) = (P (Nat.le_trans hij hjk)).map x)

/-- **M25-2: 木の一歩** — 未被覆点の上には未被覆点がある。 -/
theorem refine_step
    (Cov : ((limitGrp (natSystem G P hself hcomp)).carrier → Prop) → Prop)
    (hfin : ∀ n, Listable (G n).carrier) (n : Nat) (t : (G n).carrier)
    (hnc : ¬ cylCovered (natSystem G P hself hcomp) Cov n t) :
    ∃ s : (G (n + 1)).carrier, (P (Nat.le_succ n)).map s = t ∧
      ¬ cylCovered (natSystem G P hself hcomp) Cov (n + 1) s := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ s : (G (n + 1)).carrier, (P (Nat.le_succ n)).map s = t →
      cylCovered (natSystem G P hself hcomp) Cov (n + 1) s := by
    intro s hs
    cases Classical.em (cylCovered (natSystem G P hself hcomp) Cov (n + 1) s) with
    | inl hc => exact hc
    | inr hc => exact absurd ⟨s, hs, hc⟩ hno
  obtain ⟨l, hl⟩ := hfin (n + 1)
  have key : ∀ l' : List (G (n + 1)).carrier,
      ∃ L : List ((limitGrp (natSystem G P hself hcomp)).carrier → Prop),
        (∀ U, U ∈ L → Cov U) ∧
        ∀ x : (limitGrp (natSystem G P hself hcomp)).carrier,
          x.val n = t → x.val (n + 1) ∈ l' → ∃ U, U ∈ L ∧ U x := by
    intro l'
    induction l' with
    | nil =>
      exact ⟨[], fun U h => absurd h List.not_mem_nil,
        fun x _ h => absurd h List.not_mem_nil⟩
    | cons s l' ih =>
      obtain ⟨L2, hL2, hcov2⟩ := ih
      cases Classical.em ((P (Nat.le_succ n)).map s = t) with
      | inl hs =>
        obtain ⟨L1, hL1, hcov1⟩ := hall s hs
        refine ⟨L1 ++ L2, ?_, ?_⟩
        · intro U hU
          cases List.mem_append.mp hU with
          | inl h => exact hL1 U h
          | inr h => exact hL2 U h
        · intro x hxn hx1
          cases List.mem_cons.mp hx1 with
          | inl h =>
            obtain ⟨U, hUL, hUx⟩ := hcov1 x h
            exact ⟨U, List.mem_append.mpr (Or.inl hUL), hUx⟩
          | inr h =>
            obtain ⟨U, hUL, hUx⟩ := hcov2 x hxn h
            exact ⟨U, List.mem_append.mpr (Or.inr hUL), hUx⟩
      | inr hs =>
        refine ⟨L2, hL2, ?_⟩
        intro x hxn hx1
        cases List.mem_cons.mp hx1 with
        | inl h =>
          exfalso
          apply hs
          have hcompat : (P (Nat.le_succ n)).map (x.val (n + 1)) = x.val n :=
            x.property (Nat.le_succ n)
          rw [h] at hcompat
          rw [hcompat, hxn]
        | inr h => exact hcov2 x hxn h
  obtain ⟨L, hLC, hLcov⟩ := key l
  exact hnc ⟨L, hLC, fun x hx => hLcov x hx (hl _)⟩

/-- **定理 (M25-3): 有限レベル Nat 鎖の逆極限はコンパクト**
    （König の補題型の木論法。枝の構成に Classical.choice）。 -/
theorem natSystem_compact (hfin : ∀ n, Listable (G n).carrier) :
    Compact (limitTopology (natSystem G P hself hcomp)) := by
  intro Cov hopen hcov
  apply Classical.byContradiction
  intro hglob
  -- レベル 0 に未被覆点がある
  have hbase : ∃ t : (G 0).carrier,
      ¬ cylCovered (natSystem G P hself hcomp) Cov 0 t := by
    apply Classical.byContradiction
    intro hb
    have hallcov : ∀ t : (G 0).carrier,
        cylCovered (natSystem G P hself hcomp) Cov 0 t := by
      intro t
      cases Classical.em (cylCovered (natSystem G P hself hcomp) Cov 0 t) with
      | inl h => exact h
      | inr h => exact absurd ⟨t, h⟩ hb
    obtain ⟨l, hl⟩ := hfin 0
    obtain ⟨L, hLC, hLcov⟩ :=
      assemble_level (natSystem G P hself hcomp) Cov 0 l (fun t _ => hallcov t)
    exact hglob ⟨L, hLC, fun x => hLcov x (hl _)⟩
  -- 未被覆点の無限枝（König、Classical.choice）
  let bad : ∀ n : Nat,
      {t : (G n).carrier // ¬ cylCovered (natSystem G P hself hcomp) Cov n t} :=
    fun n => Nat.rec
      ⟨Classical.choose hbase, Classical.choose_spec hbase⟩
      (fun m prev =>
        ⟨Classical.choose (refine_step G P hself hcomp Cov hfin m prev.val prev.property),
         (Classical.choose_spec
           (refine_step G P hself hcomp Cov hfin m prev.val prev.property)).2⟩) n
  have bad_step : ∀ n, (P (Nat.le_succ n)).map (bad (n + 1)).val = (bad n).val :=
    fun n => (Classical.choose_spec
      (refine_step G P hself hcomp Cov hfin n (bad n).val (bad n).property)).1
  -- 枝の整合性（一般の i ≤ j）
  have compat_gen : ∀ (i j : Nat) (h : i ≤ j),
      (P h).map (bad j).val = (bad i).val := by
    intro i j
    induction j with
    | zero =>
      intro h
      have h0 : i = 0 := Nat.le_zero.mp h
      subst h0
      exact hself 0 (bad 0).val
    | succ j ih =>
      intro h
      by_cases hij : i = j + 1
      · subst hij
        exact hself (j + 1) (bad (j + 1)).val
      · have hij' : i ≤ j := by omega
        have hc := hcomp hij' (Nat.le_succ j) (bad (j + 1)).val
        rw [bad_step j, ih hij'] at hc
        exact hc.symm
  -- 極限点とその近傍基柱状集合で矛盾
  let xstar : (limitGrp (natSystem G P hself hcomp)).carrier :=
    ⟨fun n => (bad n).val, fun {i j} h => compat_gen i j h⟩
  obtain ⟨U, hU, hUx⟩ := hcov xstar
  obtain ⟨k, hk⟩ := cylinder_nbhd_basis (natSystem G P hself hcomp) 0 U
    (hopen U hU) xstar hUx
  refine (bad k).property ⟨[U], ?_, ?_⟩
  · intro V hV
    cases List.mem_cons.mp hV with
    | inl h => exact h ▸ hU
    | inr h => exact absurd h List.not_mem_nil
  · intro x hx
    exact ⟨U, List.mem_cons_self, hk x hx⟩

end NatChain

/-- **定理 (M25-4): ガロア塔の π₁ はコンパクト**（レベル有限のとき）。
    M24 の π₁ が副有限コンパクト群であることの完成。 -/
theorem pi1Tower_compact {D : GaloisCatData.{u, 0}} (T : GaloisTower D)
    (hfin : ∀ n, Listable (CatIso D.C (T.A n) (T.A n))) :
    Compact (limitTopology T.towerSystem) :=
  natSystem_compact (fun n => D.autGrp (T.A n))
    (fun {i j} h => T.autTransition h)
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
    hfin

/-- 階乗の割り切り単調性。 -/
theorem fact_dvd_mono : ∀ {i j : Nat}, i ≤ j → fact i ∣ fact j := by
  intro i j h
  induction j with
  | zero =>
    have h0 : i = 0 := Nat.le_zero.mp h
    subst h0
    exact Nat.dvd_refl _
  | succ j ih =>
    by_cases hij : i = j + 1
    · subst hij
      exact Nat.dvd_refl _
    · have h' : i ≤ j := by omega
      exact Nat.dvd_trans (ih h') (Nat.dvd_mul_left _ _)

/-- 階乗鎖 ℤ/n! の逆系（ẑ の鎖型表示）。 -/
def factChainSystem : InverseSystem :=
  natSystem (fun n => zmod (fact n)) (fun h => zmodTrans (fact_dvd_mono h))
    (fun i x => by induction x using Quot.ind; rfl)
    (fun hij hjk x => by induction x using Quot.ind; rfl)

/-- **定理 (M25-5): 階乗鎖の極限（ẑ の鎖型表示）はコンパクト**。 -/
theorem factChain_compact : Compact (limitTopology factChainSystem) :=
  natSystem_compact (fun n => zmod (fact n))
    (fun {i j} h => zmodTrans (fact_dvd_mono h))
    (fun i x => by induction x using Quot.ind; rfl)
    (fun hij hjk x => by induction x using Quot.ind; rfl)
    (fun n => zmod_listable (fact n) (fact_pos n))

end IUT
