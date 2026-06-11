/-
  IUT/SGA1Object.lean — M23(SGA1 主定理・対象レベルの完成: 本質的全射性)

  M22 で比較関手 Hom(A,−) の充満忠実性(射レベル)を公理から完成した。
  本モジュールは残っていた**対象レベル**——本質的全射性——を完成する:

  * M23-1 `CatIso.idIso/symmIso/transIso` — 同型の恒等・逆・合成
    (autGrp の演算と定義的に一致する独立構成)
  * M23-2 `QuotientData` — **商公理**(SGA1 の G2 後半): ガロア対象を
    自己同型の族 P で割った商 Qt(A,P) の存在を公理データ化。
    商射の不変性・降下(普遍性)・**F の商完全性**(商のファイバー =
    ファイバーの商: 全射性と一段階の P-witness 抽出)
  * M23-3 `quotient_realizes_coset` — **本質的全射性(推移的の場合)**:
    任意の部分群 H ≤ Aut(A) に対し、剰余類作用 Aut(A)/H は
    Hom(A, Qt(A,H)) と同変全単射で結ばれる。
    [σ] ↦ σ∘q の well-defined 性(商射の H-不変性)・単射性
    (商完全性 + evaluation 単射性 + 群計算)・全射性(商の
    ファイバー全射性 + ガロア推移性 + evaluation 単射性)
  * M23-4 `sga1_essentially_surjective` — 対象レベルの組み立て:
    全ての剰余類作用が比較関手の像に実現される。M16-5(任意の
    G-集合の軌道は剰余類作用)と合成すれば、**推移的 Aut(A)-集合は
    すべて比較関手の像**——対象の分類が公理から完結する
  * M23-5 `gsetQuotientData` — モデル(G-Set 圏)は商公理を満たす
    (軌道関係による商の実構成。選択公理不要——商は Quot で
    作れるため、降下公理 M22-8 と違い choice なしで済むことの
    形式的対比)

  **位置づけ(正直な申告)**: これで SGA1 主定理は
  「忠実(M21/M22)・充満(M22)・本質的全射(M23、推移的対象 =
  連結被覆)」の三点が全て公理から導出された。残るのは非連結
  (= 有限和)対象への拡張(F の和完全性公理 + 連結成分分解)と、
  ガロア対象の十分性(pro-対象)のみであり、これらは機械的な
  和の簿記と帰納法である。
-/
import IUT.SGA1Completion

namespace IUT

universe u

/-- 恒等同型(M23-1a)。`autGrp` の単位元と定義的に一致。 -/
def CatIso.idIso (C : Cat.{u, 0}) (A : C.Obj) : CatIso C A A :=
  ⟨C.id A, C.id A, C.id_comp _, C.id_comp _⟩

/-- 逆同型(M23-1b)。`autGrp` の逆元と定義的に一致。 -/
def CatIso.symmIso {C : Cat.{u, 0}} {A : C.Obj} (σ : CatIso C A A) :
    CatIso C A A :=
  ⟨σ.inv, σ.hom, σ.inv_hom, σ.hom_inv⟩

/-- 合成同型(M23-1c)。`autGrp` の積と定義的に一致。 -/
def CatIso.transIso {C : Cat.{u, 0}} {A : C.Obj} (σ τ : CatIso C A A) :
    CatIso C A A :=
  ⟨C.comp σ.hom τ.hom, C.comp τ.inv σ.inv,
   by rw [C.assoc, ← C.assoc τ.hom τ.inv σ.inv, τ.hom_inv, C.id_comp, σ.hom_inv],
   by rw [C.assoc, ← C.assoc σ.inv σ.hom τ.hom, σ.inv_hom, C.id_comp, τ.inv_hom]⟩

/-- 群計算の補題: a·(a⁻¹·b) = b。 -/
theorem Grp.mul_inv_cancel_left (G : Grp) (a b : G.carrier) :
    G.mul a (G.mul (G.inv a) b) = b := by
  rw [← G.mul_assoc, G.mul_inv, G.one_mul]

/-- 群計算の補題: a⁻¹·(a·b) = b。 -/
theorem Grp.inv_mul_cancel_left (G : Grp) (a b : G.carrier) :
    G.mul (G.inv a) (G.mul a b) = b := by
  rw [← G.mul_assoc, G.inv_mul, G.one_mul]

/-! ## M23-2: 商公理(G2 後半) -/

/-- **商公理付き抽象 Galois 圏**: 対象 A を自己同型の族 P で割った
    商 Qt(A,P) の存在(SGA1 の G2 後半「有限自己同型群による商」)。
    商完全性(q_fiber_exact)は P が恒等・逆・合成で閉じている
    (= 部分群)場合にのみ要求する。 -/
structure QuotientData extends DescentData.{u} where
  Qt : (A : C.Obj) → (CatIso C A A → Prop) → C.Obj
  qmap : (A : C.Obj) → (P : CatIso C A A → Prop) → C.Hom A (Qt A P)
  /-- 商射は P-不変。 -/
  q_coeq : ∀ {A : C.Obj} (P : CatIso C A A → Prop) (σ : CatIso C A A),
    P σ → C.comp σ.hom (qmap A P) = qmap A P
  /-- 降下(商の普遍性): P-不変な射は商を経由する。 -/
  q_descend : {A W : C.Obj} → (P : CatIso C A A → Prop) →
    (g : C.Hom A W) → (∀ σ, P σ → C.comp σ.hom g = g) →
    C.Hom (Qt A P) W
  q_descend_comp : ∀ {A W : C.Obj} (P : CatIso C A A → Prop)
    (g : C.Hom A W) (h : ∀ σ, P σ → C.comp σ.hom g = g),
    C.comp (qmap A P) (q_descend P g h) = g
  /-- F の商完全性 1: 商のファイバーへ全射。 -/
  q_fiber_surj : ∀ {A : C.Obj} (P : CatIso C A A → Prop)
    (w : F.onObj (Qt A P)), ∃ a, F.onHom (qmap A P) a = w
  /-- F の商完全性 2: 同じ商値を持つ二点は一段の P-witness で
      移り合う(P が部分群的に閉じているとき)。 -/
  q_fiber_exact : ∀ {A : C.Obj} (P : CatIso C A A → Prop),
    P (CatIso.idIso C A) →
    (∀ σ, P σ → P (CatIso.symmIso σ)) →
    (∀ σ τ, P σ → P τ → P (CatIso.transIso σ τ)) →
    ∀ (a a' : F.onObj A),
      F.onHom (qmap A P) a = F.onHom (qmap A P) a' →
      ∃ σ, P σ ∧ F.onHom σ.hom a = a'

namespace QuotientData

variable (D : QuotientData.{u})

/-- **定理 (M23-3): 本質的全射性(推移的の場合)** — A ガロア・
    H ≤ Aut(A) に対し、剰余類作用 Aut(A)/H は比較関手の像
    Hom(A, Qt(A,H)) と**同変全単射**で結ばれる。
    SGA1 主定理・対象レベルの本体。 -/
theorem quotient_realizes_coset
    {A : D.C.Obj} (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A)
    (H : Subgroup (D.toGaloisCatData.autGrp A)) :
    ∃ Φ : ActHom (cosetAction (D.toGaloisCatData.autGrp A) H)
        (D.toGaloisCatData.homGAction A (D.Qt A H.mem)),
      (∀ p q, Φ.map p = Φ.map q → p = q) ∧
      (∀ u : D.C.Hom A (D.Qt A H.mem), ∃ p, Φ.map p = u) := by
  -- well-defined 性: cosetRel σ τ ⟹ σ∘q = τ∘q
  have hwd : ∀ σ τ : CatIso D.C A A,
      cosetRel (D.toGaloisCatData.autGrp A) H σ τ →
      D.C.comp σ.hom (D.qmap A H.mem) = D.C.comp τ.hom (D.qmap A H.mem) := by
    intro σ τ hrel
    -- h' := σ⁻¹τ ∈ H、τ = σ·h'
    have hτ : (D.toGaloisCatData.autGrp A).mul σ
        ((D.toGaloisCatData.autGrp A).mul
          ((D.toGaloisCatData.autGrp A).inv σ) τ) = τ :=
      (D.toGaloisCatData.autGrp A).mul_inv_cancel_left σ τ
    have hhom : D.C.comp σ.hom
        ((D.toGaloisCatData.autGrp A).mul
          ((D.toGaloisCatData.autGrp A).inv σ) τ).hom = τ.hom :=
      congrArg CatIso.hom hτ
    have hcoeq := D.q_coeq H.mem _ hrel
    calc D.C.comp σ.hom (D.qmap A H.mem)
        = D.C.comp σ.hom (D.C.comp
            ((D.toGaloisCatData.autGrp A).mul
              ((D.toGaloisCatData.autGrp A).inv σ) τ).hom
            (D.qmap A H.mem)) := by rw [hcoeq]
      _ = D.C.comp (D.C.comp σ.hom
            ((D.toGaloisCatData.autGrp A).mul
              ((D.toGaloisCatData.autGrp A).inv σ) τ).hom)
            (D.qmap A H.mem) := (D.C.assoc _ _ _).symm
      _ = D.C.comp τ.hom (D.qmap A H.mem) := by rw [hhom]
  refine ⟨⟨Quot.lift (fun σ => D.C.comp σ.hom (D.qmap A H.mem))
      (fun σ τ h => hwd σ τ h), ?_⟩, ?_, ?_⟩
  · -- 同変性: Φ(τ·[σ]) = τ∘Φ([σ])
    intro τ p
    induction p using Quot.ind; rename_i σ
    show D.C.comp ((D.toGaloisCatData.autGrp A).mul τ σ).hom (D.qmap A H.mem)
        = D.C.comp τ.hom (D.C.comp σ.hom (D.qmap A H.mem))
    exact D.C.assoc τ.hom σ.hom (D.qmap A H.mem)
  · -- 単射性
    intro p q h
    induction p using Quot.ind; rename_i σ
    induction q using Quot.ind; rename_i τ
    apply Quot.sound
    -- ファイバーで比較: q(σ·a₀) = q(τ·a₀) ⟹ ∃ h ∈ H, h·(σ·a₀) = τ·a₀
    have h' : D.C.comp σ.hom (D.qmap A H.mem)
        = D.C.comp τ.hom (D.qmap A H.mem) := h
    have hfib : D.F.onHom (D.qmap A H.mem) (D.F.onHom σ.hom a₀)
        = D.F.onHom (D.qmap A H.mem) (D.F.onHom τ.hom a₀) := by
      rw [← D.toGaloisCatData.fmap_comp, ← D.toGaloisCatData.fmap_comp, h']
    obtain ⟨ρ, hρH, hρ⟩ := D.q_fiber_exact H.mem
      H.one_mem (fun _ hσ => H.inv_mem hσ)
      (fun _ _ hσ hτ => H.mul_mem hσ hτ)
      _ _ hfib
    -- σ·ρ = τ(evaluation 単射性)
    have hmul : (D.toGaloisCatData.autGrp A).mul σ ρ = τ := by
      apply CatIso.ext
      apply D.toGaloisCatData.evaluation_injective hA.1 a₀
      show D.F.onHom (D.C.comp σ.hom ρ.hom) a₀ = D.F.onHom τ.hom a₀
      rw [D.toGaloisCatData.fmap_comp, hρ]
    -- ⟹ σ⁻¹τ = ρ ∈ H
    show H.mem ((D.toGaloisCatData.autGrp A).mul
      ((D.toGaloisCatData.autGrp A).inv σ) τ)
    rw [← hmul, (D.toGaloisCatData.autGrp A).inv_mul_cancel_left σ ρ]
    exact hρH
  · -- 全射性
    intro u
    obtain ⟨a, ha⟩ := D.q_fiber_surj H.mem (D.F.onHom u a₀)
    obtain ⟨σ, hσ⟩ := D.toGaloisCatData.galois_trans_iso hA a₀ a
    refine ⟨Quot.mk _ σ, ?_⟩
    show D.C.comp σ.hom (D.qmap A H.mem) = u
    apply D.toGaloisCatData.evaluation_injective hA.1 a₀
    rw [D.toGaloisCatData.fmap_comp, hσ, ha]

/-- **定理 (M23-4): SGA1 主定理・対象レベルの完成** — 任意の部分群
    H ≤ Aut(A) の剰余類作用は比較関手の像として実現される。
    M16-5(任意の G-集合の軌道は剰余類作用と同変全単射)と合成
    すれば、**全ての推移的 Aut(A)-集合(= 連結被覆のファイバー)が
    比較関手の像**になる。M21(忠実の核心)・M22(充満忠実)と
    併せて主定理の三点(忠実・充満・本質的全射)が公理から完結。 -/
theorem sga1_essentially_surjective
    {A : D.C.Obj} (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A)
    (H : Subgroup (D.toGaloisCatData.autGrp A)) :
    ∃ (X : D.C.Obj)
      (Φ : ActHom (cosetAction (D.toGaloisCatData.autGrp A) H)
        (D.toGaloisCatData.homGAction A X)),
      (∀ p q, Φ.map p = Φ.map q → p = q) ∧
      (∀ u : D.C.Hom A X, ∃ p, Φ.map p = u) := by
  obtain ⟨Φ, hinj, hsurj⟩ := D.quotient_realizes_coset hA a₀ H
  exact ⟨D.Qt A H.mem, Φ, hinj, hsurj⟩

end QuotientData

/-! ## M23-5: モデルの商公理充足 -/

/-- モデルの商の台: P-軌道関係による商。 -/
def gsetQuotRel (G : Grp) (A : GAction G) (P : CatIso (GSetCat G) A A → Prop)
    (a a' : A.carrier) : Prop :=
  ∃ σ : CatIso (GSetCat G) A A, P σ ∧ σ.hom.map a = a'

/-- **定理 (M23-5): モデルは商公理を満たす** — G-Set 圏で P-軌道
    関係の Quot として商を実構成する。降下射は Quot.lift で作れる
    ため **Classical.choice 不要**(M22-8 の降下公理との形式的対比:
    商は構成的、像への降下は選択的)。 -/
noncomputable def gsetQuotientData (G : Grp) : QuotientData.{1} where
  toDescentData := gsetDescentData G
  Qt := fun A P =>
    { carrier := Quot (gsetQuotRel G A P)
      act := fun g x => Quot.lift
        (fun a => Quot.mk (gsetQuotRel G A P) (A.act g a))
        (fun a a' ⟨σ, hP, hσ⟩ => Quot.sound
          ⟨σ, hP, by rw [σ.hom.equivariant, hσ]⟩) x
      act_one := by
        intro x
        induction x using Quot.ind; rename_i a
        show Quot.mk (gsetQuotRel G A P) (A.act G.one a) = Quot.mk _ a
        rw [A.act_one]
      act_mul := by
        intro g h x
        induction x using Quot.ind; rename_i a
        show Quot.mk (gsetQuotRel G A P) (A.act (G.mul g h) a)
            = Quot.mk _ (A.act g (A.act h a))
        rw [A.act_mul] }
  qmap := fun A P => ⟨fun a => Quot.mk (gsetQuotRel G A P) a, fun _ _ => rfl⟩
  q_coeq := fun {A} P σ hP => by
    apply ActHom.ext
    intro a
    show Quot.mk (gsetQuotRel G A P) (σ.hom.map a) = Quot.mk _ a
    exact (Quot.sound ⟨σ, hP, rfl⟩).symm
  q_descend := fun {A W} P g hg =>
    ⟨Quot.lift g.map (fun a a' ⟨σ, hP, hσ⟩ => by
      have h1 : g.map (σ.hom.map a) = g.map a :=
        congrFun (congrArg ActHom.map (hg σ hP)) a
      rw [← hσ, h1]),
     by
      intro τ x
      induction x using Quot.ind; rename_i a
      show g.map (A.act τ a) = W.act τ (g.map a)
      exact g.equivariant τ a⟩
  q_descend_comp := fun P g hg => ActHom.ext (fun _ => rfl)
  q_fiber_surj := fun P w => by
    induction w using Quot.ind; rename_i a
    exact ⟨a, rfl⟩
  q_fiber_exact := fun {A} P hid hsym htrans a a' h =>
    quot_exact_of_equiv (gsetQuotRel G A P)
      (fun a => ⟨CatIso.idIso (GSetCat G) A, hid, rfl⟩)
      (fun {a a'} ⟨σ, hP, hσ⟩ => ⟨CatIso.symmIso σ, hsym σ hP, by
        rw [← hσ]
        show σ.inv.map (σ.hom.map a) = a
        exact congrFun (congrArg ActHom.map σ.hom_inv) a⟩)
      (fun {a a' a''} ⟨σ, hPσ, hσ⟩ ⟨τ, hPτ, hτ⟩ =>
        ⟨CatIso.transIso σ τ, htrans σ τ hPσ hPτ, by
          show τ.hom.map (σ.hom.map a) = a''
          rw [hσ, hτ]⟩)
      h

/-- 商公理込みの公理系の無矛盾性。 -/
theorem quotientData_consistent : Nonempty QuotientData.{1} :=
  ⟨gsetQuotientData intGrp⟩

end IUT
