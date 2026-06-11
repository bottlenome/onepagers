/-
  IUT/SumDecomposition.lean — M26（有限和分解の簿記: 非連結対象への拡張）

  M23 で推移的 Aut(A)-集合（= 連結被覆）の実現を完成した。本モジュール
  は**非連結（= 有限和）対象への拡張**の簿記を完成する:

  * M26-1 `SumData` — F の和完全性（G5 の和の部分）: inl/inr の
    ファイバー単射性・場合分け・非交差を公理データ化
  * M26-2 `connected_factors` — **連結対象からの射は和因子を経由する**
    （inl の引き戻しがモノ + ファイバー非空 ⟹ 連結性で同型）
  * M26-3 `hom_sum_realizes` — Hom(A, X⊕Y) ≅ Hom(A,X) ⊔ Hom(A,Y)
    （同変全単射。単射性 = モノ性と非交差、全射性 = M26-2）
  * M26-4 `sum_decomposition` — **有限和分解の簿記の完成**: 部分群の
    任意の有限リスト L に対し、剰余類作用の直和 ⊔_{H∈L} Aut(A)/H が
    Hom(A, ⊕_{H∈L} Qt(A,H)) と同変全単射。M16-5（任意の有限 G-集合は
    軌道 = 剰余類作用に分解）と併せて、SGA1 主定理の対象レベルが
    **有限和込みで完全**になる
  * M26-5 `gsetSumData` — モデルは和完全性を満たす（Sum 型の
    構成的性質そのもの）
-/
import IUT.SGA1Object

namespace IUT

universe u

/-- **和完全性付き抽象 Galois 圏**（M26-1、G5 の和の部分）。 -/
structure SumData extends QuotientData.{u} where
  fsum_inl_inj : ∀ {X Y : C.Obj} (x x' : F.onObj X),
    F.onHom (inl X Y) x = F.onHom (inl X Y) x' → x = x'
  fsum_inr_inj : ∀ {X Y : C.Obj} (y y' : F.onObj Y),
    F.onHom (inr X Y) y = F.onHom (inr X Y) y' → y = y'
  fsum_cases : ∀ {X Y : C.Obj} (s : F.onObj (Sm X Y)),
    (∃ x, F.onHom (inl X Y) x = s) ∨ (∃ y, F.onHom (inr X Y) y = s)
  fsum_disjoint : ∀ {X Y : C.Obj} (x : F.onObj X) (y : F.onObj Y),
    F.onHom (inl X Y) x ≠ F.onHom (inr X Y) y

namespace SumData

variable (D : SumData.{u})

/-- **定理 (M26-2): 連結対象からの射は和因子を経由する**。 -/
theorem connected_factors {A X Y : D.C.Obj}
    (hAc : D.toGaloisCatData.Connected A) (u : D.C.Hom A (D.Sm X Y)) :
    (∃ v : D.C.Hom A X, D.C.comp v (D.inl X Y) = u) ∨
    (∃ w : D.C.Hom A Y, D.C.comp w (D.inr X Y) = u) := by
  obtain ⟨a₀⟩ := hAc.1
  cases D.fsum_cases (D.F.onHom u a₀) with
  | inl hx =>
    obtain ⟨x₀, hx₀⟩ := hx
    left
    have hinj : ∀ w w',
        D.F.onHom (D.pb₁ u (D.inl X Y)) w = D.F.onHom (D.pb₁ u (D.inl X Y)) w' →
        w = w' := by
      intro w w' h1
      apply D.fpb_inj
      · exact h1
      · apply D.fsum_inl_inj
        show D.F.onHom (D.inl X Y) (D.F.onHom (D.pb₂ u (D.inl X Y)) w) = _
        rw [← D.toGaloisCatData.fmap_comp, ← D.toGaloisCatData.fmap_comp,
          ← D.pb_comm, D.toGaloisCatData.fmap_comp, D.toGaloisCatData.fmap_comp, h1]
    have hmono : D.toGaloisCatData.Mono (D.pb₁ u (D.inl X Y)) :=
      D.toGaloisCatData.mono_of_fiber_injective _ hinj
    obtain ⟨w₀, _, _⟩ := D.fpb_surj u (D.inl X Y) a₀ x₀ (by rw [hx₀])
    obtain ⟨s, _, hs2⟩ := hAc.2 (D.pb₁ u (D.inl X Y)) hmono ⟨w₀⟩
    refine ⟨D.C.comp s (D.pb₂ u (D.inl X Y)), ?_⟩
    calc D.C.comp (D.C.comp s (D.pb₂ u (D.inl X Y))) (D.inl X Y)
        = D.C.comp s (D.C.comp (D.pb₂ u (D.inl X Y)) (D.inl X Y)) :=
          D.C.assoc _ _ _
      _ = D.C.comp s (D.C.comp (D.pb₁ u (D.inl X Y)) u) := by rw [← D.pb_comm]
      _ = D.C.comp (D.C.comp s (D.pb₁ u (D.inl X Y))) u := (D.C.assoc _ _ _).symm
      _ = D.C.comp (D.C.id A) u := by rw [hs2]
      _ = u := D.C.id_comp u
  | inr hy =>
    obtain ⟨y₀, hy₀⟩ := hy
    right
    have hinj : ∀ w w',
        D.F.onHom (D.pb₁ u (D.inr X Y)) w = D.F.onHom (D.pb₁ u (D.inr X Y)) w' →
        w = w' := by
      intro w w' h1
      apply D.fpb_inj
      · exact h1
      · apply D.fsum_inr_inj
        show D.F.onHom (D.inr X Y) (D.F.onHom (D.pb₂ u (D.inr X Y)) w) = _
        rw [← D.toGaloisCatData.fmap_comp, ← D.toGaloisCatData.fmap_comp,
          ← D.pb_comm, D.toGaloisCatData.fmap_comp, D.toGaloisCatData.fmap_comp, h1]
    have hmono : D.toGaloisCatData.Mono (D.pb₁ u (D.inr X Y)) :=
      D.toGaloisCatData.mono_of_fiber_injective _ hinj
    obtain ⟨w₀, _, _⟩ := D.fpb_surj u (D.inr X Y) a₀ y₀ (by rw [hy₀])
    obtain ⟨s, _, hs2⟩ := hAc.2 (D.pb₁ u (D.inr X Y)) hmono ⟨w₀⟩
    refine ⟨D.C.comp s (D.pb₂ u (D.inr X Y)), ?_⟩
    calc D.C.comp (D.C.comp s (D.pb₂ u (D.inr X Y))) (D.inr X Y)
        = D.C.comp s (D.C.comp (D.pb₂ u (D.inr X Y)) (D.inr X Y)) :=
          D.C.assoc _ _ _
      _ = D.C.comp s (D.C.comp (D.pb₁ u (D.inr X Y)) u) := by rw [← D.pb_comm]
      _ = D.C.comp (D.C.comp s (D.pb₁ u (D.inr X Y))) u := (D.C.assoc _ _ _).symm
      _ = D.C.comp (D.C.id A) u := by rw [hs2]
      _ = u := D.C.id_comp u

/-- inl はモノ（ファイバー単射から）。 -/
theorem inl_mono {X Y : D.C.Obj} : D.toGaloisCatData.Mono (D.inl X Y) :=
  D.toGaloisCatData.mono_of_fiber_injective _
    (fun x x' h => D.fsum_inl_inj x x' h)

/-- inr はモノ。 -/
theorem inr_mono {X Y : D.C.Obj} : D.toGaloisCatData.Mono (D.inr X Y) :=
  D.toGaloisCatData.mono_of_fiber_injective _
    (fun y y' h => D.fsum_inr_inj y y' h)

/-- **定理 (M26-3): Hom(A, X⊕Y) ≅ Hom(A,X) ⊔ Hom(A,Y)**（同変全単射）。 -/
theorem hom_sum_realizes {A X Y : D.C.Obj}
    (hAc : D.toGaloisCatData.Connected A) :
    ∃ Ψ : ActHom (sumAction (D.toGaloisCatData.autGrp A)
        (D.toGaloisCatData.homGAction A X) (D.toGaloisCatData.homGAction A Y))
      (D.toGaloisCatData.homGAction A (D.Sm X Y)),
      (∀ p q, Ψ.map p = Ψ.map q → p = q) ∧
      (∀ u, ∃ p, Ψ.map p = u) := by
  obtain ⟨a₀⟩ := hAc.1
  refine ⟨⟨fun s => match s with
    | .inl v => D.C.comp v (D.inl X Y)
    | .inr w => D.C.comp w (D.inr X Y), ?_⟩, ?_, ?_⟩
  · intro σ s
    cases s with
    | inl v =>
      show D.C.comp (D.C.comp σ.hom v) (D.inl X Y)
          = D.C.comp σ.hom (D.C.comp v (D.inl X Y))
      exact D.C.assoc _ _ _
    | inr w =>
      show D.C.comp (D.C.comp σ.hom w) (D.inr X Y)
          = D.C.comp σ.hom (D.C.comp w (D.inr X Y))
      exact D.C.assoc _ _ _
  · intro p q h
    cases p with
    | inl v =>
      cases q with
      | inl v' =>
        have h' : D.C.comp v (D.inl X Y) = D.C.comp v' (D.inl X Y) := h
        rw [D.inl_mono v v' h']
      | inr w =>
        exfalso
        have h' : D.C.comp v (D.inl X Y) = D.C.comp w (D.inr X Y) := h
        have h1 : D.F.onHom (D.C.comp v (D.inl X Y)) a₀
            = D.F.onHom (D.C.comp w (D.inr X Y)) a₀ := by rw [h']
        rw [D.toGaloisCatData.fmap_comp, D.toGaloisCatData.fmap_comp] at h1
        exact D.fsum_disjoint _ _ h1
    | inr w =>
      cases q with
      | inl v =>
        exfalso
        have h' : D.C.comp w (D.inr X Y) = D.C.comp v (D.inl X Y) := h
        have h1 : D.F.onHom (D.C.comp v (D.inl X Y)) a₀
            = D.F.onHom (D.C.comp w (D.inr X Y)) a₀ := by rw [h']
        rw [D.toGaloisCatData.fmap_comp, D.toGaloisCatData.fmap_comp] at h1
        exact D.fsum_disjoint _ _ h1
      | inr w' =>
        have h' : D.C.comp w (D.inr X Y) = D.C.comp w' (D.inr X Y) := h
        rw [D.inr_mono w w' h']
  · intro u
    cases D.connected_factors hAc u with
    | inl hv =>
      obtain ⟨v, hv⟩ := hv
      exact ⟨.inl v, hv⟩
    | inr hw =>
      obtain ⟨w, hw⟩ := hw
      exact ⟨.inr w, hw⟩

end SumData

/-- 対象の有限和（リスト、M26-4 用）。 -/
@[reducible] def sumListObj (D : SumData.{u}) : List D.C.Obj → D.C.Obj
  | [] => D.O
  | X :: L => D.Sm X (sumListObj D L)

/-- 作用の有限和（リスト）。 -/
@[reducible] def sumListAction (G : Grp) : List (GAction G) → GAction G
  | [] => emptyAction G
  | X :: L => sumAction G X (sumListAction G L)

namespace SumData

variable (D : SumData.{u})

/-- **定理 (M26-4): 有限和分解の簿記の完成** — 部分群の任意の有限
    リスト L に対し、剰余類作用の直和 ⊔ Aut(A)/H は
    Hom(A, ⊕ Qt(A,H)) と同変全単射で結ばれる。M16-5 と併せて
    SGA1 主定理の対象レベルが有限和込みで完全になる。 -/
theorem sum_decomposition {A : D.C.Obj}
    (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A) :
    ∀ L : List (Subgroup (D.toGaloisCatData.autGrp A)),
    ∃ Ψ : ActHom
      (sumListAction (D.toGaloisCatData.autGrp A)
        (L.map (fun K => cosetAction (D.toGaloisCatData.autGrp A) K)))
      (D.toGaloisCatData.homGAction A
        (sumListObj D (L.map (fun K => D.Qt A K.mem)))),
      (∀ p q, Ψ.map p = Ψ.map q → p = q) ∧
      (∀ u, ∃ p, Ψ.map p = u) := by
  intro L
  induction L with
  | nil =>
    refine ⟨⟨fun e => (nomatch e), fun σ e => (nomatch e)⟩,
      fun p => (nomatch p), ?_⟩
    intro u
    exfalso
    exact D.fO_empty (D.F.onHom u a₀)
  | cons H L ih =>
    obtain ⟨Ψt, hti, hts⟩ := ih
    obtain ⟨Φ, hΦi, hΦs⟩ := D.toQuotientData.quotient_realizes_coset hA a₀ H
    refine ⟨⟨fun s => match s with
      | .inl p => D.C.comp (Φ.map p)
          (D.inl _ _)
      | .inr q => D.C.comp (Ψt.map q)
          (D.inr _ _),
      ?_⟩, ?_, ?_⟩
    · intro σ s
      cases s with
      | inl p =>
        show D.C.comp (Φ.map ((cosetAction (D.toGaloisCatData.autGrp A) H).act σ p))
            (D.inl _ _)
          = D.C.comp σ.hom (D.C.comp (Φ.map p)
            (D.inl _ _))
        rw [Φ.equivariant]
        show D.C.comp (D.C.comp σ.hom (Φ.map p))
            (D.inl _ _) = _
        exact D.C.assoc _ _ _
      | inr q =>
        show D.C.comp (Ψt.map ((sumListAction (D.toGaloisCatData.autGrp A)
            (L.map (fun K => cosetAction (D.toGaloisCatData.autGrp A) K))).act σ q))
            (D.inr _ _)
          = D.C.comp σ.hom (D.C.comp (Ψt.map q)
            (D.inr _ _))
        rw [Ψt.equivariant]
        show D.C.comp (D.C.comp σ.hom (Ψt.map q))
            (D.inr _ _) = _
        exact D.C.assoc _ _ _
    · intro p q h
      obtain ⟨a₀'⟩ := hA.1.1
      cases p with
      | inl p1 =>
        cases q with
        | inl p2 =>
          have h' : D.C.comp (Φ.map p1)
              (D.inl _ _)
            = D.C.comp (Φ.map p2)
              (D.inl _ _) := h
          rw [hΦi p1 p2 (D.inl_mono _ _ h')]
        | inr q2 =>
          exfalso
          have h' : D.C.comp (Φ.map p1)
              (D.inl _ _)
            = D.C.comp (Ψt.map q2)
              (D.inr _ _) := h
          have h1 : D.F.onHom (D.C.comp (Φ.map p1)
              (D.inl _ _)) a₀'
            = D.F.onHom (D.C.comp (Ψt.map q2)
              (D.inr _ _)) a₀' := by
            rw [h']
          rw [D.toGaloisCatData.fmap_comp, D.toGaloisCatData.fmap_comp] at h1
          exact D.fsum_disjoint _ _ h1
      | inr q1 =>
        cases q with
        | inl p2 =>
          exfalso
          have h' : D.C.comp (Ψt.map q1)
              (D.inr _ _)
            = D.C.comp (Φ.map p2)
              (D.inl _ _) := h
          have h1 : D.F.onHom (D.C.comp (Φ.map p2)
              (D.inl _ _)) a₀'
            = D.F.onHom (D.C.comp (Ψt.map q1)
              (D.inr _ _)) a₀' := by
            rw [h']
          rw [D.toGaloisCatData.fmap_comp, D.toGaloisCatData.fmap_comp] at h1
          exact D.fsum_disjoint _ _ h1
        | inr q2 =>
          have h' : D.C.comp (Ψt.map q1)
              (D.inr _ _)
            = D.C.comp (Ψt.map q2)
              (D.inr _ _) := h
          rw [hti q1 q2 (D.inr_mono _ _ h')]
    · intro u
      cases D.connected_factors hA.1 u with
      | inl hv =>
        obtain ⟨v, hv⟩ := hv
        obtain ⟨p, hp⟩ := hΦs v
        refine ⟨.inl p, ?_⟩
        show D.C.comp (Φ.map p)
            (D.inl _ _) = u
        rw [hp, hv]
      | inr hw =>
        obtain ⟨w, hw⟩ := hw
        obtain ⟨q, hq⟩ := hts w
        refine ⟨.inr q, ?_⟩
        show D.C.comp (Ψt.map q)
            (D.inr _ _) = u
        rw [hq, hw]

end SumData

/-- **定理 (M26-5): モデルは和完全性を満たす**（Sum 型の構成的性質）。 -/
noncomputable def gsetSumData (G : Grp) : SumData.{1} where
  toQuotientData := gsetQuotientData G
  fsum_inl_inj := fun _ _ h => Sum.inl.inj h
  fsum_inr_inj := fun _ _ h => Sum.inr.inj h
  fsum_cases := fun s => by
    cases s with
    | inl x => exact Or.inl ⟨x, rfl⟩
    | inr y => exact Or.inr ⟨y, rfl⟩
  fsum_disjoint := fun _ _ h => by injection h

/-- 和完全性込みの公理系の無矛盾性。 -/
theorem sumData_consistent : Nonempty SumData.{1} :=
  ⟨gsetSumData intGrp⟩

end IUT
