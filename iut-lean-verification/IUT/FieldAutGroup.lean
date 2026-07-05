/-
  IUT/FieldAutGroup.lean — M271F: 体の自己同型群 Aut(K) と Galois 群 Gal(L/K)
  ── 柱A 実 Galois 群論の本物の先行建設（遠アーベル復元の中心対象）

  分類 **[実]**（本物の体の自己同型群・本物の Galois 群 Gal(L/K)=Aut_K(L)）。

  complete_pct 影響: **柱A 実 Galois 群 Gal(L/K) の本物の先行建設**。遠アーベル
  幾何・π₁^ét 復元は「基礎体 K の自己同型のなす群 Aut(K)」と「拡大 K⊆L の
  Galois 群 Gal(L/K)=Aut_K(L)」を中心対象とする。既存資産では
  * `Field.lean`（M264F）が本物の体 `IUTField`（ℚ 実例つき）、
  * `QuotientGroup.lean`（M267F）が本物の群論（正規部分群・商群・第一同型定理・
    部分群の群構造 `subgroupGrp`）、
  * `AbstractGalois.lean`（M21）が **抽象** Galois 圏のガロア対象の自己同型群
  を持つが、**体の実構造からの自己同型群 Aut(K)（環準同型 σ:K→K の全単射）** も、
  **体拡大 K⊆L からの実 Galois 群 Gal(L/K)** も無かった。本モジュールが本物で構成する。

  内容（本物・toy 群を主語にしない）:
  * M271F-1 `FieldAut`      — 体の自己同型（加法・乗法・1 を保つ全単射環準同型。
    全単射は明示逆写像 `invFun` + 両側逆の witness で保持し choice を回避）。
    `FieldAut.map_zero`（0 の保存を加法性から導出）・`FieldAut.ext`（外延性）。
  * M271F-2 `fieldAutId`/`fieldAutComp`/`fieldAutInv` — 恒等・合成・逆が自己同型。
    **逆写像が環準同型になる**（全単射環準同型の逆は環準同型）を本物に証明。
  * M271F-3 `fieldAutGroup` — **Aut(K) が群をなす**（Grp のインスタンス化）。
  * M271F-4 `FieldExtension`/`galoisSubgroup` — 拡大 K⊆L（環準同型埋め込み）と
    **Gal(L/K)=Aut_K(L) が Aut(L) の部分群**（各点固定 ⟹ 合成・逆も固定）。
  * M271F-5 `galoisGroupGrp` — Gal(L/K) に載る**群構造**（`subgroupGrp` で群として扱う）。
  * M271F-6 `trivialExtension`/`gal_trivialExtension_trivial` — 実例: 自明拡大 K⊆K
    では Gal(K/K)=自明群（固定条件から σ=id を本物に証明）。
  * M271F-7 capstone: `GaloisGroupData`/`galoisGroupData`/`galoisGroup_exists`/
    `fieldAutGroup_exists`。

  **正直な限定**（何が本物で何が未達か）:
  1. 自己同型の**全単射性は明示逆写像 `invFun` の両側逆 witness**として持つ
     （非構成的な「全射 ⟹ 逆写像」を choice で作らない本物の設計）。これは真の
     全単射条件であり弱化ではない。
  2. Gal(L/K) の**位数・有限性・基本定理（中間体との Galois 対応）**は未形式化
     （core に有限基数・分離拡大・正規拡大の機構が無いため）。本モジュールは
     Gal(L/K) を「Aut(L) の部分群（＝群）」として本物に建設するところまで。
  3. 「Gal が K-線形に作用する」等の作用論は未着手（本切片は群構造の建設に限定）。
  4. 非自明な Gal の実例（例: ℚ(√2)/ℚ）は、二次拡大体の実構成が別切片のため
     本モジュールでは自明拡大 Gal(K/K)=1 の完全証明に留める。

  **選択公理不使用**（新規 choice を証明本体に導入しない）: 逆写像は明示、全単射は
  仮説 witness。禁止タクティク不使用（simp/decide/ring 等なし）。
-/
import IUT.Field
import IUT.QuotientGroup

namespace IUT

/-! ## M271F-1: 体の自己同型 -/

/-- **M271F-1: 体の自己同型** — 体 `K` の自己同型は、加法・乗法・単位元 1 を保つ
    全単射環準同型 σ:K→K である。全単射性は**明示逆写像 `invFun` と両側逆の
    witness**（`left_inv`/`right_inv`）として持ち、選択公理を回避する。
    （0 の保存は加法性から従うので公理に置かず `map_zero` で導出する。） -/
structure FieldAut (K : IUTField) where
  /-- 自己同型の写像本体。 -/
  toFun : K.carrier → K.carrier
  /-- 明示逆写像（全単射性の構成的 witness）。 -/
  invFun : K.carrier → K.carrier
  /-- 加法の保存。 -/
  map_add : ∀ x y, toFun (K.add x y) = K.add (toFun x) (toFun y)
  /-- 乗法の保存。 -/
  map_mul : ∀ x y, toFun (K.mul x y) = K.mul (toFun x) (toFun y)
  /-- 単位元の保存。 -/
  map_one : toFun K.one = K.one
  /-- 逆写像は左逆。 -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- 逆写像は右逆。 -/
  right_inv : ∀ x, toFun (invFun x) = x

namespace FieldAut

/-- **0 の保存**（加法性から導出）: σ(0) = σ(0+0) = σ(0)+σ(0) より σ(0)=0。 -/
theorem map_zero {K : IUTField} (σ : FieldAut K) : σ.toFun K.zero = K.zero := by
  have h : σ.toFun K.zero = K.add (σ.toFun K.zero) (σ.toFun K.zero) := by
    have step : σ.toFun (K.add K.zero K.zero)
        = K.add (σ.toFun K.zero) (σ.toFun K.zero) := σ.map_add K.zero K.zero
    rw [K.zero_add] at step
    exact step
  have h2 : K.add (σ.toFun K.zero) K.zero
      = K.add (σ.toFun K.zero) (σ.toFun K.zero) := by
    rw [← h, K.add_comm, K.zero_add]
  have h3 := K.add_left_cancel h2
  exact h3.symm

/-- **外延性** — 写像本体と逆写像が一致すれば自己同型は等しい（Prop 場は
    証明無関係で一致）。 -/
theorem ext {K : IUTField} {σ τ : FieldAut K}
    (h1 : σ.toFun = τ.toFun) (h2 : σ.invFun = τ.invFun) : σ = τ := by
  cases σ
  cases τ
  subst h1
  subst h2
  rfl

end FieldAut

/-! ## M271F-2: 恒等・合成・逆が自己同型 -/

/-- **恒等自己同型** id : K→K。 -/
def fieldAutId (K : IUTField) : FieldAut K where
  toFun := fun x => x
  invFun := fun x => x
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_one := rfl
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- **合成** σ∘τ（先に τ、次に σ）。逆写像は τ⁻¹∘σ⁻¹。 -/
def fieldAutComp {K : IUTField} (σ τ : FieldAut K) : FieldAut K where
  toFun := fun x => σ.toFun (τ.toFun x)
  invFun := fun x => τ.invFun (σ.invFun x)
  map_add := fun x y => by
    show σ.toFun (τ.toFun (K.add x y))
        = K.add (σ.toFun (τ.toFun x)) (σ.toFun (τ.toFun y))
    rw [τ.map_add, σ.map_add]
  map_mul := fun x y => by
    show σ.toFun (τ.toFun (K.mul x y))
        = K.mul (σ.toFun (τ.toFun x)) (σ.toFun (τ.toFun y))
    rw [τ.map_mul, σ.map_mul]
  map_one := by
    show σ.toFun (τ.toFun K.one) = K.one
    rw [τ.map_one, σ.map_one]
  left_inv := fun x => by
    show τ.invFun (σ.invFun (σ.toFun (τ.toFun x))) = x
    rw [σ.left_inv, τ.left_inv]
  right_inv := fun x => by
    show σ.toFun (τ.toFun (τ.invFun (σ.invFun x))) = x
    rw [τ.right_inv, σ.right_inv]

/-- **逆自己同型** σ⁻¹。**逆写像が環準同型になる**ことが本物の内容:
    σ⁻¹(x+y)=σ⁻¹(x)+σ⁻¹(y) は σ の全射性（right_inv）と加法性・単射性
    （left_inv）から従う。 -/
def fieldAutInv {K : IUTField} (σ : FieldAut K) : FieldAut K where
  toFun := σ.invFun
  invFun := σ.toFun
  map_add := fun x y => by
    show σ.invFun (K.add x y) = K.add (σ.invFun x) (σ.invFun y)
    have key : σ.toFun (K.add (σ.invFun x) (σ.invFun y)) = K.add x y := by
      rw [σ.map_add, σ.right_inv, σ.right_inv]
    rw [← key, σ.left_inv]
  map_mul := fun x y => by
    show σ.invFun (K.mul x y) = K.mul (σ.invFun x) (σ.invFun y)
    have key : σ.toFun (K.mul (σ.invFun x) (σ.invFun y)) = K.mul x y := by
      rw [σ.map_mul, σ.right_inv, σ.right_inv]
    rw [← key, σ.left_inv]
  map_one := by
    show σ.invFun K.one = K.one
    have h : σ.invFun (σ.toFun K.one) = K.one := σ.left_inv K.one
    rw [σ.map_one] at h
    exact h
  left_inv := fun x => σ.right_inv x
  right_inv := fun x => σ.left_inv x

/-! ## M271F-3: Aut(K) が群をなす -/

/-- **M271F-3: 体の自己同型群 Aut(K)** — 合成を積、恒等を単位元、逆自己同型を
    逆元として **Grp のインスタンス**をなす（M267F の群 `Grp` として本物に構成）。
    結合律・左単位律は定義的合成の外延性、左逆律は σ⁻¹∘σ=id を `left_inv` から。 -/
def fieldAutGroup (K : IUTField) : Grp where
  carrier := FieldAut K
  mul := fun σ τ => fieldAutComp σ τ
  one := fieldAutId K
  inv := fun σ => fieldAutInv σ
  mul_assoc := fun _ _ _ => FieldAut.ext rfl rfl
  one_mul := fun _ => FieldAut.ext rfl rfl
  inv_mul := fun a => FieldAut.ext (funext a.left_inv) (funext a.left_inv)

/-! ## M271F-4: 体拡大と Galois 群 Gal(L/K)=Aut_K(L) -/

/-- **体拡大 K⊆L** — 基礎体 `base` から上体 `top` への環準同型埋め込み
    （加法・乗法・1 を保つ）。 -/
structure FieldExtension where
  /-- 基礎体 K。 -/
  base : IUTField
  /-- 上体 L。 -/
  top : IUTField
  /-- 埋め込み ι : K → L。 -/
  incl : base.carrier → top.carrier
  /-- 埋め込みは加法を保つ。 -/
  incl_add : ∀ x y, incl (base.add x y) = top.add (incl x) (incl y)
  /-- 埋め込みは乗法を保つ。 -/
  incl_mul : ∀ x y, incl (base.mul x y) = top.mul (incl x) (incl y)
  /-- 埋め込みは 1 を保つ。 -/
  incl_one : incl base.one = top.one

/-- **Gal(L/K)=Aut_K(L) は Aut(L) の部分群** — K を各点固定する L の自己同型全体。
    恒等は明らかに固定、合成 σ∘τ は τ(ιk)=ιk, σ(ιk)=ιk より固定、逆 σ⁻¹ は
    σ(ιk)=ιk に σ⁻¹ を施して固定。**各点固定が合成・逆で閉じる**という本物の内容。 -/
def galoisSubgroup (E : FieldExtension) : Subgroup (fieldAutGroup E.top) where
  mem := fun σ => ∀ k, σ.toFun (E.incl k) = E.incl k
  one_mem := fun _ => rfl
  mul_mem := fun {σ τ} hσ hτ => fun k => by
    show σ.toFun (τ.toFun (E.incl k)) = E.incl k
    rw [hτ k, hσ k]
  inv_mem := fun {σ} hσ => fun k => by
    show σ.invFun (E.incl k) = E.incl k
    have h : σ.invFun (σ.toFun (E.incl k)) = E.incl k := σ.left_inv (E.incl k)
    rw [hσ k] at h
    exact h

/-! ## M271F-5: Gal(L/K) に載る群構造 -/

/-- **M271F-5: Galois 群 Gal(L/K) を群として** — 部分群 `galoisSubgroup` に
    `subgroupGrp`（M267F-6）で群構造を載せ、Gal(L/K) を**独立した群**として扱う。 -/
def galoisGroupGrp (E : FieldExtension) : Grp :=
  subgroupGrp (galoisSubgroup E)

/-! ## M271F-6: 実例 — 自明拡大 K⊆K の Gal は自明群 -/

/-- **自明拡大 K⊆K**（埋め込みは恒等）。 -/
def trivialExtension (K : IUTField) : FieldExtension where
  base := K
  top := K
  incl := fun x => x
  incl_add := fun _ _ => rfl
  incl_mul := fun _ _ => rfl
  incl_one := rfl

/-- **M271F-6: Gal(K/K) は自明群** — 自明拡大では K を各点固定する自己同型は
    恒等のみ（σ.toFun = id、逆写像も id）。「Gal(K/K)=1」の本物の完全証明。 -/
theorem gal_trivialExtension_trivial (K : IUTField)
    (σ : FieldAut K) (hσ : (galoisSubgroup (trivialExtension K)).mem σ) :
    σ = fieldAutId K := by
  apply FieldAut.ext
  · funext x
    have hx : σ.toFun x = x := hσ x
    exact hx
  · funext x
    have hx : σ.toFun x = x := hσ x
    have h : σ.invFun (σ.toFun x) = x := σ.left_inv x
    rw [hx] at h
    exact h

/-! ## M271F-7: capstone -/

/-- **capstone データ** — 体拡大 E に対する Galois 群の全部品: 自己同型群 Aut(L)・
    Galois 部分群 Gal(L/K)⊆Aut(L)・Gal に載る群構造。 -/
structure GaloisGroupData (E : FieldExtension) where
  /-- 上体の自己同型群 Aut(L)。 -/
  autGroup : Grp
  /-- Galois 群 Gal(L/K) は Aut(L) の部分群。 -/
  gal : Subgroup autGroup
  /-- Gal(L/K) を独立した群として。 -/
  galGroup : Grp
  /-- Gal の群構造は部分群 gal の `subgroupGrp`。 -/
  galGroup_eq : galGroup = subgroupGrp gal

/-- **Gal の所属条件は K の各点固定**（部分群の membership の特徴づけ）。 -/
theorem galoisSubgroup_mem_iff (E : FieldExtension) (σ : FieldAut E.top) :
    (galoisSubgroup E).mem σ ↔ (∀ k, σ.toFun (E.incl k) = E.incl k) :=
  Iff.rfl

/-- **証人** — Aut(L)・Gal(L/K)・その群構造が全条件を満たす。 -/
def galoisGroupData (E : FieldExtension) : GaloisGroupData E where
  autGroup := fieldAutGroup E.top
  gal := galoisSubgroup E
  galGroup := galoisGroupGrp E
  galGroup_eq := rfl

/-- **M271F-7a: Galois 群 Gal(L/K) の存在**（Aut_K(L) が群をなす）。 -/
theorem galoisGroup_exists (E : FieldExtension) : Nonempty (GaloisGroupData E) :=
  ⟨galoisGroupData E⟩

/-- **M271F-7b: 自己同型群 Aut(K) の存在**（本物の体 ℚ 上の Aut(ℚ) が群をなす）。 -/
theorem fieldAutGroup_exists : Nonempty Grp :=
  ⟨fieldAutGroup ratIUTField⟩

end IUT
