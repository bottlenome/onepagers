/-
  IUT/Topology.lean — M15（位相付き副有限群）の形式化

  M13 で代数的に構成した逆極限群（副有限群）に**位相構造**を与え、
  副有限群の位相的特徴のうち本計画で使う中核を完全証明する:

  §1 位相空間の自前建設（mathlib 非依存）
  * `Topology` — 開集合系の公理（全体・二項交叉・任意合併）
  * `GenOpen` / `genTopology` — 準開基から生成される位相
    （帰納的定義）と最小性 `genOpen_minimal`
  * `Continuous` と **M15-1 `continuous_into_gen`** — 生成位相への
    連続性は準開基で検査すれば十分（連続性検査の基本補題）
  * `prodTopology` — 直積位相

  §2 逆極限の位相（副有限位相）
  * `limitTopology` — 柱状集合（有限レベルの条件の引き戻し）を
    準開基とする極限位相。各レベルは離散
  * M15-2 `limitProj_continuous` — 射影は連続
  * M15-3 `limit_mul_continuous` / M15-4 `limit_inv_continuous` —
    **逆極限群は位相群**（積・逆元が連続）。副有限群の定義の
    位相的半分が、構成した実物の上で成立することの完全証明
  * M15-5 `projKernel_isOpen` ほか — 射影の核は**開部分群**
    （開・1 を含む・積と逆元で閉じる）
  * M15-6 `cylinder_nbhd_basis` — **近傍基定理**: 極限位相の任意の
    開集合は、各点で「あるレベル k での一致」柱状集合を含む。
    系 `projKernel_nbhd`: 射影核は単位元の開近傍基をなす——
    「副有限群の位相は有限商への射影で決まる」の形式的内容
  * M15-7 `zhat_proj_surjective` — ẑ → ℤ/n は全射（コンパクト性の
    帰結として通常使われる持ち上げが、ẑ では構成的に証明できる）

  **位置づけ（正直な申告）**: コンパクト性・Hausdorff 性の一般論は
  未形式化（有限集合論のインフラを要する）。ここで証明したのは
  副有限位相の使用部分——位相群性・開部分群・近傍基・有限レベル
  への全射——であり、SGA1 の連続作用条件（M16）の土台になる。
-/
import IUT.Profinite

namespace IUT

/-! ## §1 位相空間の自前建設 -/

/-- **位相**: 開集合系（集合 = 述語 α → Prop）。 -/
structure Topology (α : Type) where
  IsOpen : (α → Prop) → Prop
  isOpen_univ : IsOpen (fun _ => True)
  isOpen_inter : ∀ {U V}, IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)
  isOpen_sUnion : ∀ (S : (α → Prop) → Prop),
    (∀ U, S U → IsOpen U) → IsOpen (fun x => ∃ U, S U ∧ U x)

/-- 離散位相（全ての集合が開）。有限レベルの位相。 -/
def discreteTopology (α : Type) : Topology α where
  IsOpen := fun _ => True
  isOpen_univ := trivial
  isOpen_inter := fun _ _ => trivial
  isOpen_sUnion := fun _ _ => trivial

/-- 準開基 B から生成される開集合（帰納的定義）。 -/
inductive GenOpen {α : Type} (B : (α → Prop) → Prop) : (α → Prop) → Prop where
  | basic : ∀ U, B U → GenOpen B U
  | univ : GenOpen B (fun _ => True)
  | inter : ∀ U V, GenOpen B U → GenOpen B V → GenOpen B (fun x => U x ∧ V x)
  | sUnion : ∀ S : (α → Prop) → Prop,
      (∀ U, S U → GenOpen B U) → GenOpen B (fun x => ∃ U, S U ∧ U x)

/-- 生成位相。 -/
def genTopology {α : Type} (B : (α → Prop) → Prop) : Topology α where
  IsOpen := GenOpen B
  isOpen_univ := GenOpen.univ
  isOpen_inter := fun hU hV => GenOpen.inter _ _ hU hV
  isOpen_sUnion := fun S h => GenOpen.sUnion S h

/-- 生成位相の最小性: B を含む任意の位相は生成位相を含む。 -/
theorem genOpen_minimal {α : Type} (B : (α → Prop) → Prop) (T : Topology α)
    (hB : ∀ U, B U → T.IsOpen U) :
    ∀ U, GenOpen B U → T.IsOpen U := by
  intro U hU
  induction hU with
  | basic U hU => exact hB U hU
  | univ => exact T.isOpen_univ
  | inter U V _ _ ihU ihV => exact T.isOpen_inter ihU ihV
  | sUnion S _ ih => exact T.isOpen_sUnion S ih

/-- 連続写像: 開集合の引き戻しは開。 -/
def Continuous {α β : Type} (Tα : Topology α) (Tβ : Topology β)
    (f : α → β) : Prop :=
  ∀ V, Tβ.IsOpen V → Tα.IsOpen (fun x => V (f x))

/-- 連続写像の合成。 -/
theorem continuous_comp {α β γ : Type}
    {Tα : Topology α} {Tβ : Topology β} {Tγ : Topology γ}
    {f : α → β} {g : β → γ}
    (hf : Continuous Tα Tβ f) (hg : Continuous Tβ Tγ g) :
    Continuous Tα Tγ (fun x => g (f x)) :=
  fun V hV => hf _ (hg V hV)

/-- **定理 (M15-1): 連続性の準開基検査** — 生成位相への連続性は
    準開基の引き戻しが開であることを見れば十分。 -/
theorem continuous_into_gen {α β : Type} (Tα : Topology α)
    (B : (β → Prop) → Prop) (f : α → β)
    (hf : ∀ V, B V → Tα.IsOpen (fun x => V (f x))) :
    Continuous Tα (genTopology B) f := by
  intro V hV
  induction hV with
  | basic U hU => exact hf U hU
  | univ => exact Tα.isOpen_univ
  | inter U V _ _ ihU ihV => exact Tα.isOpen_inter ihU ihV
  | sUnion S _ ih =>
    have heq : (fun x => ∃ U, S U ∧ U (f x))
        = (fun x => ∃ W, (fun W => ∃ U, S U ∧ W = fun y => U (f y)) W ∧ W x) := by
      funext x
      apply propext
      constructor
      · intro ⟨U, hU, hUx⟩
        exact ⟨_, ⟨U, hU, rfl⟩, hUx⟩
      · intro ⟨W, ⟨U, hU, hW⟩, hWx⟩
        rw [hW] at hWx
        exact ⟨U, hU, hWx⟩
    rw [heq]
    exact Tα.isOpen_sUnion _ (fun W hW => by
      obtain ⟨U, hU, rfl⟩ := hW
      exact ih U hU)

/-- 直積位相（開長方形を準開基とする生成位相）。 -/
def prodTopology {α β : Type} (Tα : Topology α) (Tβ : Topology β) :
    Topology (α × β) :=
  genTopology (fun W => ∃ U V, Tα.IsOpen U ∧ Tβ.IsOpen V ∧
    W = fun p => U p.1 ∧ V p.2)

/-! ## §2 逆極限の位相（副有限位相） -/

/-- 柱状集合: レベル i の条件 A の引き戻し。 -/
def cylinder (S : InverseSystem) (i : S.Idx) (A : (S.G i).carrier → Prop) :
    (limitGrp S).carrier → Prop :=
  fun x => A (x.val i)

/-- 極限位相の準開基 = 柱状集合の全体。 -/
def limitSubbasis (S : InverseSystem) : ((limitGrp S).carrier → Prop) → Prop :=
  fun U => ∃ i A, U = cylinder S i A

/-- **極限位相（副有限位相）**: 柱状集合が生成する位相。 -/
def limitTopology (S : InverseSystem) : Topology (limitGrp S).carrier :=
  genTopology (limitSubbasis S)

/-- 柱状集合は開。 -/
theorem cylinder_isOpen (S : InverseSystem) (i : S.Idx)
    (A : (S.G i).carrier → Prop) :
    (limitTopology S).IsOpen (cylinder S i A) :=
  GenOpen.basic _ ⟨i, A, rfl⟩

/-- **定理 (M15-2): 射影は連続**（各レベルは離散位相）。 -/
theorem limitProj_continuous (S : InverseSystem) (i : S.Idx) :
    Continuous (limitTopology S) (discreteTopology (S.G i).carrier)
      (limitProj S i).map :=
  fun V _ => cylinder_isOpen S i V

/-- 単位元の逆元は単位元（補題）。 -/
theorem Grp.inv_one (G : Grp) : G.inv G.one = G.one := by
  have h := G.inv_mul G.one
  rw [G.mul_one] at h
  exact h

/-- **定理 (M15-3): 積は連続** — 逆極限群の積は直積位相に関して
    連続。証明: 柱状集合の引き戻しは「レベル i の値の組ごとの
    開長方形」の合併に分解される。 -/
theorem limit_mul_continuous (S : InverseSystem) :
    Continuous (prodTopology (limitTopology S) (limitTopology S))
      (limitTopology S)
      (fun p => (limitGrp S).mul p.1 p.2) := by
  apply continuous_into_gen
  intro V hV
  obtain ⟨i, A, rfl⟩ := hV
  have heq : (fun p : (limitGrp S).carrier × (limitGrp S).carrier =>
        cylinder S i A ((limitGrp S).mul p.1 p.2))
      = (fun p => ∃ W, (fun W => ∃ a b, A ((S.G i).mul a b) ∧
          W = fun q : (limitGrp S).carrier × (limitGrp S).carrier =>
            q.1.val i = a ∧ q.2.val i = b) W ∧ W p) := by
    funext p
    apply propext
    constructor
    · intro hp
      exact ⟨_, ⟨p.1.val i, p.2.val i, hp, rfl⟩, rfl, rfl⟩
    · intro ⟨W, ⟨a, b, hab, hW⟩, hWp⟩
      rw [hW] at hWp
      show A ((S.G i).mul (p.1.val i) (p.2.val i))
      rw [hWp.1, hWp.2]
      exact hab
  rw [heq]
  exact GenOpen.sUnion _ (fun W hW => by
    obtain ⟨a, b, _, rfl⟩ := hW
    exact GenOpen.basic _
      ⟨cylinder S i (fun c => c = a), cylinder S i (fun c => c = b),
        cylinder_isOpen S i _, cylinder_isOpen S i _, rfl⟩)

/-- **定理 (M15-4): 逆元は連続**。M15-3 と併せて、逆極限群は
    **位相群**である（副有限群の位相的半分の完成）。 -/
theorem limit_inv_continuous (S : InverseSystem) :
    Continuous (limitTopology S) (limitTopology S)
      (fun x => (limitGrp S).inv x) := by
  apply continuous_into_gen
  intro V hV
  obtain ⟨i, A, rfl⟩ := hV
  exact GenOpen.basic _ ⟨i, fun c => A ((S.G i).inv c), rfl⟩

/-- 射影の核（レベル i で単位元になる元の全体）。 -/
def projKernel (S : InverseSystem) (i : S.Idx) :
    (limitGrp S).carrier → Prop :=
  fun x => x.val i = (S.G i).one

/-- **定理 (M15-5a): 射影核は開**。 -/
theorem projKernel_isOpen (S : InverseSystem) (i : S.Idx) :
    (limitTopology S).IsOpen (projKernel S i) :=
  GenOpen.basic _ ⟨i, fun c => c = (S.G i).one, rfl⟩

/-- M15-5b: 射影核は単位元を含む。 -/
theorem projKernel_one (S : InverseSystem) (i : S.Idx) :
    projKernel S i (limitGrp S).one := rfl

/-- M15-5c: 射影核は積で閉じる。 -/
theorem projKernel_mul (S : InverseSystem) (i : S.Idx)
    {x y : (limitGrp S).carrier}
    (hx : projKernel S i x) (hy : projKernel S i y) :
    projKernel S i ((limitGrp S).mul x y) := by
  show (S.G i).mul (x.val i) (y.val i) = (S.G i).one
  rw [hx, hy, (S.G i).one_mul]

/-- M15-5d: 射影核は逆元で閉じる。以上で**射影核は開部分群**。 -/
theorem projKernel_inv (S : InverseSystem) (i : S.Idx)
    {x : (limitGrp S).carrier} (hx : projKernel S i x) :
    projKernel S i ((limitGrp S).inv x) := by
  show (S.G i).inv (x.val i) = (S.G i).one
  rw [hx, (S.G i).inv_one]

/-- **定理 (M15-6): 近傍基定理** — 極限位相の開集合 U と x ∈ U に
    対し、あるレベル k が存在して「レベル k で x と一致する元」は
    すべて U に入る。すなわち柱状集合が近傍基をなす。
    （有向性が二つのレベルを共通上界で束ねるところが核心。） -/
theorem cylinder_nbhd_basis (S : InverseSystem) (i₀ : S.Idx)
    (U : (limitGrp S).carrier → Prop)
    (hU : (limitTopology S).IsOpen U) (x : (limitGrp S).carrier) :
    U x → ∃ k, ∀ y : (limitGrp S).carrier, y.val k = x.val k → U y := by
  induction hU with
  | basic V hV =>
    obtain ⟨i, A, rfl⟩ := hV
    intro hx
    refine ⟨i, fun y hy => ?_⟩
    show A (y.val i)
    rw [hy]
    exact hx
  | univ =>
    intro _
    exact ⟨i₀, fun _ _ => trivial⟩
  | inter V W _ _ ihV ihW =>
    intro hx
    obtain ⟨kV, hkV⟩ := ihV hx.1
    obtain ⟨kW, hkW⟩ := ihW hx.2
    obtain ⟨k, hVk, hWk⟩ := S.directed kV kW
    refine ⟨k, fun y hy => ⟨hkV y ?_, hkW y ?_⟩⟩
    · rw [← y.property hVk, hy, x.property hVk]
    · rw [← y.property hWk, hy, x.property hWk]
  | sUnion T _ ih =>
    intro hx
    obtain ⟨V, hV, hVx⟩ := hx
    obtain ⟨k, hk⟩ := ih V hV hVx
    exact ⟨k, fun y hy => ⟨V, hV, hk y hy⟩⟩

/-- **系: 射影核は単位元の開近傍基** — 1 を含む任意の開集合は
    ある射影核を含む。「副有限群の位相は有限商で決まる」の
    形式的内容であり、SGA1 の連続作用条件（M16）の土台。 -/
theorem projKernel_nbhd (S : InverseSystem) (i₀ : S.Idx)
    (U : (limitGrp S).carrier → Prop)
    (hU : (limitTopology S).IsOpen U) (h1 : U (limitGrp S).one) :
    ∃ k, ∀ y, projKernel S k y → U y := by
  obtain ⟨k, hk⟩ := cylinder_nbhd_basis S i₀ U hU (limitGrp S).one h1
  exact ⟨k, fun y hy => hk y hy⟩

/-- **定理 (M15-7): ẑ → ℤ/n は全射** — 一般の副有限群では
    コンパクト性から従う有限レベルへの全射が、ẑ では完備化写像を
    経由して**構成的に**証明できる（選択公理不要）。 -/
theorem zhat_proj_surjective (n : Nat) (c : (zmod n).carrier) :
    ∃ z : zhat.carrier, (limitProj zmodSystem n).map z = c := by
  induction c using Quot.ind
  rename_i a
  exact ⟨toZhat.map a, rfl⟩

end IUT
