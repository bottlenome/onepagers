/-
  IUT/AbstractGalois.lean — M21（抽象 Galois 圏: 公理系からの一般形）の形式化

  M20 では Galois 圏の公理系 G1–G6 を具体的モデル（G-Set 圏）の上で
  検証した。本モジュールは逆向きに、**公理系そのものを抽象データ構造
  `GaloisCatData` として定式化し、公理だけから主定理の抽象的中核を
  導出する**（SGA1 V.4 の一般論の前半）:

  * `GaloisCatData` — 抽象 Galois 圏: 圏 C・ファイバー関手 F・
    G1（終対象・ファイバー積、選択されたデータとして）・
    G2（始対象・有限和）・G3（エピモノ分解）・
    G4（F は終対象とファイバー積を保つ）・G5（F は始対象を空にする）・
    G6（F は同型を反映する）
  * M21-1 `prodObj` / `pair` — **積はファイバー積から導出される**
    （終対象上のファイバー積。一般論の最初の構成）
  * M21-2 `eqObj` / `eq_mono` — **イコライザもファイバー積から導出**
    （⟨f,g⟩ と対角 Δ のファイバー積）され、モノである
  * M21-3 `feq_surj` — F はイコライザを保つ（ファイバーの計算）
  * M21-4 `fiber_faithful` — **ファイバー関手は忠実**。
    公理 G1+G4+G6 だけからの導出（イコライザのファイバーが全射に
    なることと G6 の同型反映の合成）——抽象主定理の第一の柱
  * M21-5 `mono_of_fiber_injective` — ファイバー単射ならモノ
  * M21-6 `evaluation_injective` — **連結対象からの射はファイバーの
    一点で決まる**: A 連結・a ∈ F(A) のとき Hom(A,X) → F(X),
    u ↦ F(u)(a) は単射。被覆理論の核心補題の公理からの導出
  * M21-7 `galois_evaluation_bijective` — **ガロア対象の自己射群 ≅
    ファイバー**: A がガロア（連結 + 自己同型がファイバーに推移的）
    なら evaluation は全単射。「π₁ の有限レベル = ガロア対象の
    自己同型群」の抽象形（M14/M20 の Aut(F) ≅ G の公理版）
  * M21-8 `gsetGaloisData` — **モデルの公理系充足**: G-Set 圏と
    忘却関手が `GaloisCatData` の全フィールドを満たす
    （M20 の G1–G6 検証の構造化。無矛盾性証明を兼ねる）

  **位置づけ（正直な申告）**: SGA1 の一般論の後半——十分多くの
  ガロア対象の存在（連結対象はガロア対象に支配される）と
  pro-表現対象の構成、それによる抽象圏同値——は未形式化。
  本モジュールで「公理 ⟹ 忠実性・evaluation 単射・ガロア対象の
  群復元」という主定理の論理的骨格が公理のみから導出された。
-/
import IUT.GaloisAxioms

namespace IUT

universe u v

/-- **抽象 Galois 圏**: 圏・ファイバー関手・公理系 G1–G6
    （極限・余極限は選択されたデータとして持つ）。 -/
structure GaloisCatData where
  C : Cat.{u, v}
  F : Functor C SetCat
  -- G1a: 終対象
  T : C.Obj
  toT : (X : C.Obj) → C.Hom X T
  toT_unique : ∀ {X : C.Obj} (f g : C.Hom X T), f = g
  -- G1b: ファイバー積
  PB : {X Y Z : C.Obj} → C.Hom X Z → C.Hom Y Z → C.Obj
  pb₁ : {X Y Z : C.Obj} → (f : C.Hom X Z) → (g : C.Hom Y Z) → C.Hom (PB f g) X
  pb₂ : {X Y Z : C.Obj} → (f : C.Hom X Z) → (g : C.Hom Y Z) → C.Hom (PB f g) Y
  pb_comm : ∀ {X Y Z : C.Obj} (f : C.Hom X Z) (g : C.Hom Y Z),
    C.comp (pb₁ f g) f = C.comp (pb₂ f g) g
  pbLift : {W X Y Z : C.Obj} → {f : C.Hom X Z} → {g : C.Hom Y Z} →
    (u : C.Hom W X) → (v : C.Hom W Y) → C.comp u f = C.comp v g →
    C.Hom W (PB f g)
  pbLift₁ : ∀ {W X Y Z : C.Obj} {f : C.Hom X Z} {g : C.Hom Y Z}
    (u : C.Hom W X) (v : C.Hom W Y) (h : C.comp u f = C.comp v g),
    C.comp (pbLift u v h) (pb₁ f g) = u
  pbLift₂ : ∀ {W X Y Z : C.Obj} {f : C.Hom X Z} {g : C.Hom Y Z}
    (u : C.Hom W X) (v : C.Hom W Y) (h : C.comp u f = C.comp v g),
    C.comp (pbLift u v h) (pb₂ f g) = v
  pb_ext : ∀ {W X Y Z : C.Obj} {f : C.Hom X Z} {g : C.Hom Y Z}
    (w w' : C.Hom W (PB f g)),
    C.comp w (pb₁ f g) = C.comp w' (pb₁ f g) →
    C.comp w (pb₂ f g) = C.comp w' (pb₂ f g) → w = w'
  -- G2: 始対象と二項和
  O : C.Obj
  fromO : (X : C.Obj) → C.Hom O X
  fromO_unique : ∀ {X : C.Obj} (f g : C.Hom O X), f = g
  Sm : C.Obj → C.Obj → C.Obj
  inl : (X Y : C.Obj) → C.Hom X (Sm X Y)
  inr : (X Y : C.Obj) → C.Hom Y (Sm X Y)
  copair : {X Y W : C.Obj} → C.Hom X W → C.Hom Y W → C.Hom (Sm X Y) W
  copair₁ : ∀ {X Y W : C.Obj} (f : C.Hom X W) (g : C.Hom Y W),
    C.comp (inl X Y) (copair f g) = f
  copair₂ : ∀ {X Y W : C.Obj} (f : C.Hom X W) (g : C.Hom Y W),
    C.comp (inr X Y) (copair f g) = g
  -- G3: エピモノ分解（像）
  Im : {X Y : C.Obj} → C.Hom X Y → C.Obj
  imE : {X Y : C.Obj} → (f : C.Hom X Y) → C.Hom X (Im f)
  imM : {X Y : C.Obj} → (f : C.Hom X Y) → C.Hom (Im f) Y
  im_comp : ∀ {X Y : C.Obj} (f : C.Hom X Y), C.comp (imE f) (imM f) = f
  imE_fiber_surj : ∀ {X Y : C.Obj} (f : C.Hom X Y) (w : F.onObj (Im f)),
    ∃ x, F.onHom (imE f) x = w
  imM_fiber_inj : ∀ {X Y : C.Obj} (f : C.Hom X Y) (a b : F.onObj (Im f)),
    F.onHom (imM f) a = F.onHom (imM f) b → a = b
  -- G4: F は終対象とファイバー積を保つ
  fT : F.onObj T
  fT_unique : ∀ x y : F.onObj T, x = y
  fpb_inj : ∀ {X Y Z : C.Obj} (f : C.Hom X Z) (g : C.Hom Y Z)
    (w w' : F.onObj (PB f g)),
    F.onHom (pb₁ f g) w = F.onHom (pb₁ f g) w' →
    F.onHom (pb₂ f g) w = F.onHom (pb₂ f g) w' → w = w'
  fpb_surj : ∀ {X Y Z : C.Obj} (f : C.Hom X Z) (g : C.Hom Y Z)
    (a : F.onObj X) (b : F.onObj Y), F.onHom f a = F.onHom g b →
    ∃ w, F.onHom (pb₁ f g) w = a ∧ F.onHom (pb₂ f g) w = b
  -- G5（の使用部分）: F は始対象を空に送る
  fO_empty : F.onObj O → False
  -- G6: F は同型を反映する
  reflect_iso : ∀ {X Y : C.Obj} (f : C.Hom X Y),
    (∀ a b, F.onHom f a = F.onHom f b → a = b) →
    (∀ b, ∃ a, F.onHom f a = b) →
    ∃ g : C.Hom Y X, C.comp f g = C.id X ∧ C.comp g f = C.id Y

namespace GaloisCatData

variable (D : GaloisCatData.{u, v})

/-- ファイバーでの合成の計算。 -/
theorem fmap_comp {X Y Z : D.C.Obj} (f : D.C.Hom X Y) (g : D.C.Hom Y Z)
    (x : D.F.onObj X) :
    D.F.onHom (D.C.comp f g) x = D.F.onHom g (D.F.onHom f x) :=
  congrFun (D.F.map_comp f g) x

/-- ファイバーでの恒等射の計算。 -/
theorem fmap_id {X : D.C.Obj} (x : D.F.onObj X) :
    D.F.onHom (D.C.id X) x = x :=
  congrFun (D.F.map_id X) x

/-! ## M21-1: 積の導出（終対象上のファイバー積） -/

/-- 積 X × Y := X ×_T Y。 -/
def prodObj (X Y : D.C.Obj) : D.C.Obj := D.PB (D.toT X) (D.toT Y)

def pr₁ (X Y : D.C.Obj) : D.C.Hom (D.prodObj X Y) X := D.pb₁ _ _
def pr₂ (X Y : D.C.Obj) : D.C.Hom (D.prodObj X Y) Y := D.pb₂ _ _

/-- 対 ⟨u, v⟩。 -/
def pair {W X Y : D.C.Obj} (u : D.C.Hom W X) (v : D.C.Hom W Y) :
    D.C.Hom W (D.prodObj X Y) :=
  D.pbLift u v (D.toT_unique _ _)

theorem pair₁ {W X Y : D.C.Obj} (u : D.C.Hom W X) (v : D.C.Hom W Y) :
    D.C.comp (D.pair u v) (D.pr₁ X Y) = u :=
  D.pbLift₁ u v _

theorem pair₂ {W X Y : D.C.Obj} (u : D.C.Hom W X) (v : D.C.Hom W Y) :
    D.C.comp (D.pair u v) (D.pr₂ X Y) = v :=
  D.pbLift₂ u v _

/-- 対角 Δ : X → X × X。 -/
def diag (X : D.C.Obj) : D.C.Hom X (D.prodObj X X) :=
  D.pair (D.C.id X) (D.C.id X)

theorem diag₁ (X : D.C.Obj) :
    D.C.comp (D.diag X) (D.pr₁ X X) = D.C.id X := D.pair₁ _ _

theorem diag₂ (X : D.C.Obj) :
    D.C.comp (D.diag X) (D.pr₂ X X) = D.C.id X := D.pair₂ _ _

/-! ## M21-2: イコライザの導出（⟨f,g⟩ と Δ のファイバー積） -/

/-- イコライザ Eq(f,g) := PB(⟨f,g⟩, Δ_Y)。 -/
def eqObj {X Y : D.C.Obj} (f g : D.C.Hom X Y) : D.C.Obj :=
  D.PB (D.pair f g) (D.diag Y)

/-- イコライザの包含射。 -/
def eqMap {X Y : D.C.Obj} (f g : D.C.Hom X Y) : D.C.Hom (D.eqObj f g) X :=
  D.pb₁ _ _

/-- 補助射: Eq(f,g) → Y。 -/
def eqAux {X Y : D.C.Obj} (f g : D.C.Hom X Y) : D.C.Hom (D.eqObj f g) Y :=
  D.pb₂ _ _

/-- e ∘ f = q（第一成分の計算）。 -/
theorem eq_comp_f {X Y : D.C.Obj} (f g : D.C.Hom X Y) :
    D.C.comp (D.eqMap f g) f = D.eqAux f g := by
  have h := D.pb_comm (D.pair f g) (D.diag Y)
  have h1 := congrArg (fun t => D.C.comp t (D.pr₁ Y Y)) h
  simp only [] at h1
  rw [D.C.assoc, D.C.assoc, D.pair₁, D.diag₁, D.C.comp_id] at h1
  exact h1

/-- e ∘ g = q（第二成分の計算）。よって e ∘ f = e ∘ g。 -/
theorem eq_comp_g {X Y : D.C.Obj} (f g : D.C.Hom X Y) :
    D.C.comp (D.eqMap f g) g = D.eqAux f g := by
  have h := D.pb_comm (D.pair f g) (D.diag Y)
  have h1 := congrArg (fun t => D.C.comp t (D.pr₂ Y Y)) h
  simp only [] at h1
  rw [D.C.assoc, D.C.assoc, D.pair₂, D.diag₂, D.C.comp_id] at h1
  exact h1

/-- イコライザの基本等式 e ∘ f = e ∘ g。 -/
theorem eq_comm {X Y : D.C.Obj} (f g : D.C.Hom X Y) :
    D.C.comp (D.eqMap f g) f = D.C.comp (D.eqMap f g) g := by
  rw [D.eq_comp_f, D.eq_comp_g]

/-- **定理 (M21-2): イコライザはモノ**。 -/
theorem eq_mono {X Y : D.C.Obj} (f g : D.C.Hom X Y)
    {W : D.C.Obj} (w w' : D.C.Hom W (D.eqObj f g))
    (h : D.C.comp w (D.eqMap f g) = D.C.comp w' (D.eqMap f g)) : w = w' := by
  apply D.pb_ext
  · exact h
  · -- pb₂ = eqAux = e ∘ f で書き換え
    show D.C.comp w (D.eqAux f g) = D.C.comp w' (D.eqAux f g)
    rw [← D.eq_comp_f, ← D.C.assoc, ← D.C.assoc, h]

/-! ## M21-3: F はイコライザを保つ -/

/-- F での積の成分計算: F⟨u,v⟩ の第一成分は F u。 -/
theorem fpair₁ {W X Y : D.C.Obj} (u : D.C.Hom W X) (v : D.C.Hom W Y)
    (w : D.F.onObj W) :
    D.F.onHom (D.pr₁ X Y) (D.F.onHom (D.pair u v) w) = D.F.onHom u w := by
  rw [← D.fmap_comp, D.pair₁]

theorem fpair₂ {W X Y : D.C.Obj} (u : D.C.Hom W X) (v : D.C.Hom W Y)
    (w : D.F.onObj W) :
    D.F.onHom (D.pr₂ X Y) (D.F.onHom (D.pair u v) w) = D.F.onHom v w := by
  rw [← D.fmap_comp, D.pair₂]

/-- **定理 (M21-3): F はイコライザを保つ** — F f x = F g x なる
    ファイバー点はイコライザのファイバーから来る。 -/
theorem feq_surj {X Y : D.C.Obj} (f g : D.C.Hom X Y) (x : D.F.onObj X)
    (h : D.F.onHom f x = D.F.onHom g x) :
    ∃ w : D.F.onObj (D.eqObj f g), D.F.onHom (D.eqMap f g) w = x := by
  -- ⟨f,g⟩(x) = Δ(F f x) を成分計算で示し、fpb_surj を適用
  have hcomp : D.F.onHom (D.pair f g) x = D.F.onHom (D.diag Y) (D.F.onHom f x) := by
    apply D.fpb_inj (D.toT Y) (D.toT Y)
    · show D.F.onHom (D.pr₁ Y Y) _ = D.F.onHom (D.pr₁ Y Y) _
      rw [D.fpair₁]
      show D.F.onHom f x = D.F.onHom (D.pr₁ Y Y) (D.F.onHom (D.diag Y) (D.F.onHom f x))
      rw [← D.fmap_comp, D.diag₁, D.fmap_id]
    · show D.F.onHom (D.pr₂ Y Y) _ = D.F.onHom (D.pr₂ Y Y) _
      rw [D.fpair₂]
      show D.F.onHom g x = D.F.onHom (D.pr₂ Y Y) (D.F.onHom (D.diag Y) (D.F.onHom f x))
      rw [← D.fmap_comp, D.diag₂, D.fmap_id]
      exact h.symm
  obtain ⟨w, hw1, _⟩ := D.fpb_surj (D.pair f g) (D.diag Y) x (D.F.onHom f x) hcomp
  exact ⟨w, hw1⟩

/-! ## M21-4: ファイバー関手の忠実性（公理からの導出） -/

/-- 分裂簡約補題: s ∘ e = id なら e の後の合成は簡約できる。 -/
theorem cancel_of_split {E X Y : D.C.Obj} (e : D.C.Hom E X) (s : D.C.Hom X E)
    (hs : D.C.comp s e = D.C.id X) (f g : D.C.Hom X Y)
    (h : D.C.comp e f = D.C.comp e g) : f = g := by
  calc f = D.C.comp (D.C.id X) f := (D.C.id_comp f).symm
    _ = D.C.comp (D.C.comp s e) f := by rw [hs]
    _ = D.C.comp s (D.C.comp e f) := D.C.assoc s e f
    _ = D.C.comp s (D.C.comp e g) := by rw [h]
    _ = D.C.comp (D.C.comp s e) g := (D.C.assoc s e g).symm
    _ = D.C.comp (D.C.id X) g := by rw [hs]
    _ = g := D.C.id_comp g

/-- **定理 (M21-4): ファイバー関手は忠実** — F f = F g（各点）なら
    f = g。証明: イコライザ Eq(f,g) → X はファイバー全単射になる
    （単射: モノ性のファイバー版、全射: M21-3）ので G6 により同型、
    分裂簡約で f = g。公理 G1+G4+G6 だけからの導出。 -/
theorem fiber_faithful {X Y : D.C.Obj} (f g : D.C.Hom X Y)
    (h : ∀ x, D.F.onHom f x = D.F.onHom g x) : f = g := by
  -- e := Eq(f,g) → X はファイバー単射
  have einj : ∀ w w', D.F.onHom (D.eqMap f g) w = D.F.onHom (D.eqMap f g) w' →
      w = w' := by
    intro w w' hww
    apply D.fpb_inj
    · exact hww
    · show D.F.onHom (D.eqAux f g) w = D.F.onHom (D.eqAux f g) w'
      rw [← D.eq_comp_f, D.fmap_comp, D.fmap_comp, hww]
  -- ファイバー全射（M21-3）
  have esurj : ∀ x, ∃ w, D.F.onHom (D.eqMap f g) w = x :=
    fun x => D.feq_surj f g x (h x)
  obtain ⟨s, _, hs2⟩ := D.reflect_iso (D.eqMap f g) einj esurj
  exact D.cancel_of_split (D.eqMap f g) s hs2 f g (D.eq_comm f g)

/-- モノ射。 -/
def Mono {E X : D.C.Obj} (m : D.C.Hom E X) : Prop :=
  ∀ {W : D.C.Obj} (u v : D.C.Hom W E),
    D.C.comp u m = D.C.comp v m → u = v

/-- 同型射。 -/
def IsIso {X Y : D.C.Obj} (f : D.C.Hom X Y) : Prop :=
  ∃ g : D.C.Hom Y X, D.C.comp f g = D.C.id X ∧ D.C.comp g f = D.C.id Y

/-- **定理 (M21-5): ファイバー単射ならモノ**（忠実性の系）。 -/
theorem mono_of_fiber_injective {E X : D.C.Obj} (m : D.C.Hom E X)
    (hm : ∀ a b, D.F.onHom m a = D.F.onHom m b → a = b) : D.Mono m := by
  intro W u v huv
  apply D.fiber_faithful
  intro w
  apply hm
  rw [← D.fmap_comp, ← D.fmap_comp, huv]

/-! ## M21-6/7: 連結対象・evaluation 単射・ガロア対象の群復元 -/

/-- **連結性**: ファイバーが空でなく、空でないファイバーを持つ
    モノ部分対象は同型に限る（固有の部分被覆を持たない）。 -/
def Connected (A : D.C.Obj) : Prop :=
  Nonempty (D.F.onObj A) ∧
  ∀ {E : D.C.Obj} (m : D.C.Hom E A), D.Mono m →
    Nonempty (D.F.onObj E) → D.IsIso m

/-- **定理 (M21-6): evaluation の単射性** — A が連結なら、射
    u : A → X はファイバーの一点での値 F(u)(a) で決まる。
    被覆理論の核心補題（「連結被覆の射は一点で決まる」）の
    公理 G1+G4+G6 からの導出。 -/
theorem evaluation_injective {A X : D.C.Obj} (hA : D.Connected A)
    (a : D.F.onObj A) (u v : D.C.Hom A X)
    (h : D.F.onHom u a = D.F.onHom v a) : u = v := by
  -- イコライザは a を含む ⟹ 非空 ⟹ 連結性で同型 ⟹ u = v
  obtain ⟨w, hw⟩ := D.feq_surj u v a h
  have hne : Nonempty (D.F.onObj (D.eqObj u v)) := ⟨w⟩
  have hm : D.Mono (D.eqMap u v) := fun p q => D.eq_mono u v p q
  obtain ⟨s, _, hs2⟩ := hA.2 (D.eqMap u v) hm hne
  exact D.cancel_of_split (D.eqMap u v) s hs2 u v (D.eq_comm u v)

/-- **ガロア対象**: 連結で、自己同型がファイバーに推移的に作用する。 -/
def IsGalois (A : D.C.Obj) : Prop :=
  D.Connected A ∧
  ∀ a b : D.F.onObj A, ∃ σ : D.C.Hom A A, D.IsIso σ ∧ D.F.onHom σ a = b

/-- **定理 (M21-7): ガロア対象の自己射群 ≅ ファイバー** —
    A がガロアなら evaluation σ ↦ F(σ)(a₀) は自己射とファイバーの
    間の全単射（単射 = M21-6、全射 = 推移性）。
    「π₁ の有限レベル = ガロア対象の自己同型群」の抽象形であり、
    M14/M20 で具体的に証明した Aut(F) ≅ G の公理版。 -/
theorem galois_evaluation_bijective {A : D.C.Obj} (hA : D.IsGalois A)
    (a₀ : D.F.onObj A) :
    (∀ σ τ : D.C.Hom A A, D.F.onHom σ a₀ = D.F.onHom τ a₀ → σ = τ) ∧
    (∀ b : D.F.onObj A, ∃ σ : D.C.Hom A A, D.F.onHom σ a₀ = b) := by
  constructor
  · intro σ τ h
    exact D.evaluation_injective hA.1 a₀ σ τ h
  · intro b
    obtain ⟨σ, _, hσ⟩ := hA.2 a₀ b
    exact ⟨σ, hσ⟩

end GaloisCatData

/-! ## M21-8: モデル（G-Set 圏）の公理系充足 -/

/-- 忘却関手（G-Set 圏のファイバー関手）。 -/
def forgetfulG (G : Grp) : Functor (GSetCat G) SetCat where
  onObj := fun X => X.carrier
  onHom := fun f => f.map
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- **定理 (M21-8): モデルの公理系充足** — G-Set 圏と忘却関手は
    抽象 Galois 圏の公理系 `GaloisCatData` を満たす（M20 の G1–G6
    検証の構造化、公理系の無矛盾性証明を兼ねる）。
    G6 フィールドのみ Classical.choice を使用（M20-5 と同じ）。 -/
def gsetGaloisData (G : Grp) : GaloisCatData where
  C := GSetCat G
  F := forgetfulG G
  T := unitAction G
  toT := fun _ => ⟨fun _ => PUnit.unit, fun _ _ => rfl⟩
  toT_unique := fun _ _ => ActHom.ext (fun _ => rfl)
  PB := fun f g => pullbackAction G f g
  pb₁ := fun f g => ⟨fun p => p.val.1, fun _ _ => rfl⟩
  pb₂ := fun f g => ⟨fun p => p.val.2, fun _ _ => rfl⟩
  pb_comm := fun f g => ActHom.ext (fun w => w.property)
  pbLift := fun {W X Y Z} {f g} u v h =>
    ⟨fun w => ⟨(u.map w, v.map w), congrFun (congrArg ActHom.map h) w⟩,
      fun σ w => by
        apply Subtype.ext
        show (u.map (W.act σ w), v.map (W.act σ w))
            = (X.act σ (u.map w), Y.act σ (v.map w))
        rw [u.equivariant, v.equivariant]⟩
  pbLift₁ := fun _ _ _ => ActHom.ext (fun _ => rfl)
  pbLift₂ := fun _ _ _ => ActHom.ext (fun _ => rfl)
  pb_ext := fun {W X Y Z} {f g} w w' h1 h2 => by
    apply ActHom.ext
    intro x
    apply Subtype.ext
    have e1 : (w.map x).val.1 = (w'.map x).val.1 :=
      congrFun (congrArg ActHom.map h1) x
    have e2 : (w.map x).val.2 = (w'.map x).val.2 :=
      congrFun (congrArg ActHom.map h2) x
    show (w.map x).val = (w'.map x).val
    rw [show (w'.map x).val = ((w'.map x).val.1, (w'.map x).val.2) from rfl,
      ← e1, ← e2]
  O := emptyAction G
  fromO := fun _ => ⟨fun e => (nomatch e), fun _ e => (nomatch e)⟩
  fromO_unique := fun _ _ => ActHom.ext (fun e => (nomatch e))
  Sm := sumAction G
  inl := fun _ _ => ⟨fun x => .inl x, fun _ _ => rfl⟩
  inr := fun _ _ => ⟨fun y => .inr y, fun _ _ => rfl⟩
  copair := fun {X Y W} f g =>
    ⟨fun s => match s with
      | .inl x => f.map x
      | .inr y => g.map y,
     fun σ s => by
      cases s with
      | inl x =>
        show f.map (X.act σ x) = W.act σ (f.map x)
        exact f.equivariant σ x
      | inr y =>
        show g.map (Y.act σ y) = W.act σ (g.map y)
        exact g.equivariant σ y⟩
  copair₁ := fun _ _ => ActHom.ext (fun _ => rfl)
  copair₂ := fun _ _ => ActHom.ext (fun _ => rfl)
  Im := fun f => imageAction G f
  imE := fun f =>
    ⟨fun x => ⟨f.map x, x, rfl⟩, fun σ x => Subtype.ext (f.equivariant σ x)⟩
  imM := fun f => ⟨fun y => y.val, fun _ _ => rfl⟩
  im_comp := fun _ => ActHom.ext (fun _ => rfl)
  imE_fiber_surj := fun f w => by
    obtain ⟨x, hx⟩ := w.property
    exact ⟨x, Subtype.ext hx⟩
  imM_fiber_inj := fun f a b h => Subtype.ext h
  fT := PUnit.unit
  fT_unique := fun _ _ => rfl
  fpb_inj := fun f g w w' h1 h2 => by
    have e1 : w.val.1 = w'.val.1 := h1
    have e2 : w.val.2 = w'.val.2 := h2
    apply Subtype.ext
    show w.val = w'.val
    rw [show w'.val = (w'.val.1, w'.val.2) from rfl, ← e1, ← e2]
  fpb_surj := fun f g a b h => ⟨⟨(a, b), h⟩, rfl, rfl⟩
  fO_empty := fun e => (nomatch e)
  reflect_iso := fun {X Y} f hinj hsurj => by
    obtain ⟨g, hgf, hfg⟩ := gsets_G6_reflects_iso G f hinj hsurj
    exact ⟨g, ActHom.ext hgf, ActHom.ext hfg⟩

/-- 公理系の無矛盾性（M21-8 の系）。 -/
theorem galoisCatData_consistent : Nonempty GaloisCatData.{1, 0} :=
  ⟨gsetGaloisData (fiberAut intGrp)⟩

end IUT
