/-
  IUT/QuotientGroup.lean — M267F: 商群と準同型定理（第一同型定理）
  ── 柱A 実 Galois 群論の本物の先行建設

  分類 **[実]**（本物の群論の先行建設）。

  **complete_pct 影響: 柱A 実 Galois 群論の本物の先行建設
  （正規部分群・商群・準同型定理）**。実 Galois 群 Gal(L/K) の本物の
  理論に必要な群論の土台 — 正規部分群 N ⊴ G の定義、剰余類 G/N が
  **群**をなすこと、群準同型 φ の核 ker φ（正規部分群）・像 im φ
  （部分群）、そして**第一同型定理 G/ker φ ≅ im φ**（全単射準同型の
  構成）を core Lean のみで完全証明する。

  既存資産との非重複（recon 済み）:
  * `Profinite.lean` は **合同関係 `GrpCong`** による商群 `quotGrp` を
    持つが、「**正規部分群から**合同関係が誘導される」橋（本物の内容）は
    無かった。本モジュールが `IsNormalSubgroup N → GrpCong`（`normalCong`）
    を与え、剰余類 `cosetSpace G N` に群構造を載せる。
  * `GaloisClosureModel.lean` は `core_normal`（core(H) が共役で閉じる）
    を持つが、**一般の正規部分群述語 `IsNormalSubgroup`**・**核/像の
    部分群性**・**準同型定理**は無かった。本モジュールが新設する。

  内容（本物・toy 群を主語にしない）:
  * M267F-1 `IsNormalSubgroup` — 正規部分群 gNg⁻¹ ⊆ N の述語。
    `core_isNormal` で `core_normal` がこの述語を充足することを接続。
  * M267F-2 `normalCong` — **正規性 ⟹ 剰余類同値が積と両立する合同**
    （mul_compat の証明が正規性を本質的に使う古典的内容）。
  * M267F-3 `quotientGroupN` / `quotientProjN` / `quotientProjN_ker`
    — **商群 G/N**（群公理は合同商 `quotGrp` から継承）・射影準同型
    （全射）・射影の核がちょうど N であること。
  * M267F-4 `kerMem` / `kerSubgroup` / `ker_isNormal` — 群準同型 φ の
    **核は正規部分群**。
  * M267F-5 `imMem` / `imSubgroup` — φ の**像は（H の）部分群**。
  * M267F-6 `subgroupGrp` — 部分群に載る**群構造**（像を群として扱う）。
  * M267F-7 `firstIsoHom` / `firstIso_injective` / `firstIso_surjective`
    — **第一同型定理 G/ker φ ≅ im φ**: 明示準同型 φ̄([a]) = φ(a) が
    well-defined（核の潰し）で、単射（核の分離）かつ全射（像の定義）。
    「少なくとも全単射準同型」を選択公理なしで構成。
  * M267F-8 `leftTranslate` / `leftTranslate_bijection` — **Lagrange の
    骨格**: 左移動 n ↦ g·n が部分群 N と剰余類 gN の**全単射**
    （明示逆写像 x ↦ g⁻¹x）。全剰余類が N と同数であることの核。
  * M267F-9 `QuotientGroupData` / `quotientGroupData` /
    `firstIsomorphism_exists` / `quotientGroupN_exists` — capstone。

  **正直な限定**:
  1. **Lagrange は骨格のみ**: 左移動が N と剰余類の全単射であること
     （= 全剰余類が同数）まで。有限群での位数の整除 |N| ∣ |G| という
     結論は core に有限基数機構が無いため未形式化。
  2. **同型は「全単射準同型」まで**: `firstIsoHom` は単射かつ全射な
     準同型として構成した。両側逆写像を明示的 `Hom` として取り出すには
     像元が担う存在証明（Prop）から代表元を選ぶ必要があり選択公理を
     要するため、本モジュールでは（choice 回避のため）採らない。
  3. 本モジュールは実 Galois 群 Gal(L/K) の**抽象群論の土台**であり、
     体拡大からの実 Galois 群の構成そのものは範囲外（柱A の別切片）。

  **選択公理不使用**（型継承も無し）: 全宣言の公理は
  [propext, Quot.sound] のみ（gsetGaloisData 等 choice 付き資産に
  一切言及しない）。禁止タクティク不使用。サブエージェント並行部品。
-/
import IUT.SGA1
import IUT.Profinite
import IUT.GaloisClosureModel

namespace IUT

/-! ## M267F-1: 正規部分群 -/

/-- **正規部分群**（M267F-1a）: gNg⁻¹ ⊆ N、すなわち任意の g と
    n ∈ N について gng⁻¹ ∈ N。実 Galois 群論で Gal(L/K) の正規部分群
    （中間体の正規性に対応）を扱う土台。 -/
def IsNormalSubgroup (G : Grp) (N : Subgroup G) : Prop :=
  ∀ g n, N.mem n → N.mem (G.mul (G.mul g n) (G.inv g))

/-- **系 (M267F-1b): core(H) は正規部分群** — `core_normal`
    （M148F）が新述語 `IsNormalSubgroup` をそのまま充足する。 -/
theorem core_isNormal (G : Grp) (H : Subgroup G) :
    IsNormalSubgroup G (coreSubgroup G H) :=
  core_normal G H

/-! ## M267F-2: 正規性 ⟹ 剰余類同値は合同（積と両立） -/

/-- **定理・構成 (M267F-2): 正規部分群は合同関係を誘導する** —
    剰余類同値 `cosetRel G N` は積と両立し `GrpCong G` になる。
    mul_compat の証明が正規性を本質的に使う（古典的内容）:
    (ab)⁻¹(a'b') = (b⁻¹·(a⁻¹a')·b)·(b⁻¹b') で、第一因子は正規性で
    N に属し、第二因子は b⁻¹b' ∈ N。 -/
def normalCong (G : Grp) (N : Subgroup G) (hN : IsNormalSubgroup G N) :
    GrpCong G where
  rel := cosetRel G N
  refl := cosetRel_refl G N
  symm := fun h => cosetRel_symm G N h
  trans := fun h1 h2 => cosetRel_trans G N h1 h2
  mul_compat := by
    intro a b a' b' ha hb
    -- ha : N.mem (a⁻¹ a'), hb : N.mem (b⁻¹ b')
    have hconj := hN (G.inv b) (G.mul (G.inv a) a') ha
    rw [G.inv_inv] at hconj
    -- hconj : N.mem ((b⁻¹ (a⁻¹ a')) b)
    have hmul := N.mul_mem hconj hb
    show N.mem (G.mul (G.inv (G.mul a b)) (G.mul a' b'))
    have key : G.mul (G.mul (G.mul (G.inv b) (G.mul (G.inv a) a')) b)
          (G.mul (G.inv b) b')
        = G.mul (G.inv (G.mul a b)) (G.mul a' b') := by
      rw [G.inv_mul_rev,
        G.mul_assoc (G.mul (G.inv b) (G.mul (G.inv a) a')) b (G.mul (G.inv b) b'),
        ← G.mul_assoc b (G.inv b) b', G.mul_inv, G.one_mul,
        G.mul_assoc (G.inv b) (G.mul (G.inv a) a') b',
        G.mul_assoc (G.inv a) a' b',
        ← G.mul_assoc (G.inv b) (G.inv a) (G.mul a' b')]
    rw [← key]
    exact hmul

/-! ## M267F-3: 商群 G/N -/

/-- **商群 G/N**（M267F-3a）: 正規部分群による剰余類の群。台は
    `cosetSpace G N`（= `Quot (cosetRel G N)`）で、群公理は合同商
    `quotGrp`（M13-2）から継承される — 既存の剰余類集合に群構造が載る。 -/
def quotientGroupN (G : Grp) (N : Subgroup G) (hN : IsNormalSubgroup G N) : Grp :=
  quotGrp G (normalCong G N hN)

/-- **射影準同型 G → G/N**（M267F-3b）。 -/
def quotientProjN (G : Grp) (N : Subgroup G) (hN : IsNormalSubgroup G N) :
    Hom G (quotientGroupN G N hN) :=
  quotProj G (normalCong G N hN)

/-- **射影は全射**（M267F-3c）。 -/
theorem quotientProjN_surjective (G : Grp) (N : Subgroup G)
    (hN : IsNormalSubgroup G N) :
    ∀ x, ∃ a, (quotientProjN G N hN).map a = x :=
  quotProj_surjective G (normalCong G N hN)

/-- **定理 (M267F-3d): 射影の核はちょうど N** —
    π(a) = 1_{G/N} ⟺ a ∈ N（普遍対象としての商群の特徴）。 -/
theorem quotientProjN_ker (G : Grp) (N : Subgroup G) (hN : IsNormalSubgroup G N)
    (a : G.carrier) :
    (quotientProjN G N hN).map a = (quotientGroupN G N hN).one ↔ N.mem a := by
  constructor
  · intro h
    have hr := quot_exact G (normalCong G N hN) h
    have hr2 : N.mem (G.mul (G.inv a) G.one) := hr
    rw [G.mul_one] at hr2
    have h3 := N.inv_mem hr2
    rw [G.inv_inv] at h3
    exact h3
  · intro h
    apply Quot.sound
    show N.mem (G.mul (G.inv a) G.one)
    rw [G.mul_one]
    exact N.inv_mem h

/-! ## M267F-4: 準同型の核は正規部分群 -/

/-- **核への所属**（M267F-4a）: φ(g) = 1。 -/
def kerMem {G H : Grp} (φ : Hom G H) (g : G.carrier) : Prop :=
  φ.map g = H.one

/-- **核 ker φ は部分群**（M267F-4b）。 -/
def kerSubgroup {G H : Grp} (φ : Hom G H) : Subgroup G where
  mem := kerMem φ
  one_mem := φ.map_one
  mul_mem := fun {a b} ha hb => by
    show φ.map (G.mul a b) = H.one
    rw [φ.map_mul]
    show H.mul (φ.map a) (φ.map b) = H.one
    rw [ha, hb, H.one_mul]
  inv_mem := fun {a} ha => by
    show φ.map (G.inv a) = H.one
    rw [φ.map_inv]
    show H.inv (φ.map a) = H.one
    rw [ha, ← H.mul_one (H.inv H.one), H.inv_mul]

/-- **定理 (M267F-4c): ker φ は正規部分群** —
    φ(gng⁻¹) = φ(g)·1·φ(g)⁻¹ = 1。 -/
theorem ker_isNormal {G H : Grp} (φ : Hom G H) :
    IsNormalSubgroup G (kerSubgroup φ) := by
  intro g n hn
  show φ.map (G.mul (G.mul g n) (G.inv g)) = H.one
  rw [φ.map_mul, φ.map_mul, φ.map_inv]
  show H.mul (H.mul (φ.map g) (φ.map n)) (H.inv (φ.map g)) = H.one
  rw [hn, H.mul_one, H.mul_inv]

/-! ## M267F-5: 準同型の像は部分群 -/

/-- **像への所属**（M267F-5a）: ∃a, φ(a) = h。 -/
def imMem {G H : Grp} (φ : Hom G H) (h : H.carrier) : Prop :=
  ∃ a, φ.map a = h

/-- **像 im φ は（H の）部分群**（M267F-5b）。 -/
def imSubgroup {G H : Grp} (φ : Hom G H) : Subgroup H where
  mem := imMem φ
  one_mem := ⟨G.one, φ.map_one⟩
  mul_mem := fun {x y} hx hy => by
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨G.mul a b, ?_⟩
    rw [φ.map_mul, ha, hb]
  inv_mem := fun {x} hx => by
    obtain ⟨a, ha⟩ := hx
    refine ⟨G.inv a, ?_⟩
    rw [φ.map_inv, ha]

/-! ## M267F-6: 部分群の群構造 -/

/-- **部分群に載る群構造**（M267F-6）: {x // K.mem x} を群として扱う
    （像 im φ を第一同型定理の右辺の群にするため）。 -/
def subgroupGrp {G : Grp} (K : Subgroup G) : Grp where
  carrier := { x : G.carrier // K.mem x }
  mul := fun x y => ⟨G.mul x.val y.val, K.mul_mem x.property y.property⟩
  one := ⟨G.one, K.one_mem⟩
  inv := fun x => ⟨G.inv x.val, K.inv_mem x.property⟩
  mul_assoc := fun a b c => Subtype.ext (G.mul_assoc a.val b.val c.val)
  one_mul := fun a => Subtype.ext (G.one_mul a.val)
  inv_mul := fun a => Subtype.ext (G.inv_mul a.val)

/-! ## M267F-7: 第一同型定理 G/ker φ ≅ im φ -/

/-- **同型写像 φ̄ (M267F-7a)**: G/ker φ → im φ、φ̄([a]) := φ(a)。
    well-defined（a ~ b（核 mod）⟹ φ(a) = φ(b)）で準同型。 -/
def firstIsoHom {G H : Grp} (φ : Hom G H) :
    Hom (quotientGroupN G (kerSubgroup φ) (ker_isNormal φ))
      (subgroupGrp (imSubgroup φ)) where
  map := Quot.lift
    (fun a => (⟨φ.map a, ⟨a, rfl⟩⟩ : { x : H.carrier // imMem φ x }))
    (fun a b hab => by
      apply Subtype.ext
      show φ.map a = φ.map b
      have hk : φ.map (G.mul (G.inv a) b) = H.one := hab
      rw [φ.map_mul, φ.map_inv] at hk
      have hstep := congrArg (H.mul (φ.map a)) hk
      rw [← H.mul_assoc, H.mul_inv, H.one_mul, H.mul_one] at hstep
      exact hstep.symm)
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    apply Subtype.ext
    show φ.map (G.mul a b) = H.mul (φ.map a) (φ.map b)
    exact φ.map_mul a b

/-- **定理 (M267F-7b): φ̄ は単射** — φ̄[a] = φ̄[b] ⟹ φ(a)=φ(b) ⟹
    φ(a⁻¹b)=1 ⟹ a⁻¹b ∈ ker ⟹ [a]=[b]。 -/
theorem firstIso_injective {G H : Grp} (φ : Hom G H) :
    Hom.Injective (firstIsoHom φ) := by
  intro x y hxy
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  have hval : φ.map a = φ.map b := congrArg Subtype.val hxy
  apply Quot.sound
  show φ.map (G.mul (G.inv a) b) = H.one
  rw [φ.map_mul, φ.map_inv, ← hval, H.inv_mul]

/-- **定理 (M267F-7c): φ̄ は全射** — 像の任意元 h = φ(a) は φ̄[a] の値。 -/
theorem firstIso_surjective {G H : Grp} (φ : Hom G H) :
    ∀ y, ∃ x, (firstIsoHom φ).map x = y := by
  intro y
  obtain ⟨h, hex⟩ := y
  obtain ⟨a, ha⟩ := hex
  refine ⟨Quot.mk _ a, ?_⟩
  exact Subtype.ext ha

/-! ## M267F-8: Lagrange の骨格（左移動による剰余類 ≅ 部分群） -/

/-- 左剰余類 gN を型として（{x // g ~ x}）。 -/
def leftCosetType (G : Grp) (N : Subgroup G) (g : G.carrier) : Type :=
  { x : G.carrier // cosetRel G N g x }

/-- 部分群 N の台の型。 -/
def subgroupCarrier (G : Grp) (N : Subgroup G) : Type :=
  { n : G.carrier // N.mem n }

/-- **左移動 (M267F-8a)**: n ↦ g·n、N → gN。 -/
def leftTranslate (G : Grp) (N : Subgroup G) (g : G.carrier) :
    subgroupCarrier G N → leftCosetType G N g :=
  fun n => ⟨G.mul g n.val, by
    show N.mem (G.mul (G.inv g) (G.mul g n.val))
    rw [← G.mul_assoc, G.inv_mul, G.one_mul]
    exact n.property⟩

/-- **逆写像 (M267F-8b)**: x ↦ g⁻¹·x、gN → N（gN の元は g⁻¹x ∈ N）。 -/
def leftTranslateInv (G : Grp) (N : Subgroup G) (g : G.carrier) :
    leftCosetType G N g → subgroupCarrier G N :=
  fun x => ⟨G.mul (G.inv g) x.val, x.property⟩

/-- **左逆 (M267F-8c)**: g⁻¹(g·n) = n。 -/
theorem leftTranslate_leftInv (G : Grp) (N : Subgroup G) (g : G.carrier)
    (n : subgroupCarrier G N) :
    leftTranslateInv G N g (leftTranslate G N g n) = n := by
  apply Subtype.ext
  show G.mul (G.inv g) (G.mul g n.val) = n.val
  rw [← G.mul_assoc, G.inv_mul, G.one_mul]

/-- **右逆 (M267F-8d)**: g(g⁻¹·x) = x。 -/
theorem leftTranslate_rightInv (G : Grp) (N : Subgroup G) (g : G.carrier)
    (x : leftCosetType G N g) :
    leftTranslate G N g (leftTranslateInv G N g x) = x := by
  apply Subtype.ext
  show G.mul g (G.mul (G.inv g) x.val) = x.val
  rw [← G.mul_assoc, G.mul_inv, G.one_mul]

/-- **定理 (M267F-8e): Lagrange の骨格** — 左移動は N と剰余類 gN の
    全単射（明示両側逆写像）。全ての左剰余類が N と同数であることの核。
    **限定**: 有限群での位数の整除 |N| ∣ |G| は core に基数機構が無く未達。 -/
theorem leftTranslate_bijection (G : Grp) (N : Subgroup G) (g : G.carrier) :
    (∀ n, leftTranslateInv G N g (leftTranslate G N g n) = n) ∧
    (∀ x, leftTranslate G N g (leftTranslateInv G N g x) = x) :=
  ⟨leftTranslate_leftInv G N g, leftTranslate_rightInv G N g⟩

/-! ## M267F-9: capstone -/

/-- **capstone データ (M267F-9a)**: 群準同型 φ に対する第一同型定理の
    全部品 — 商群 G/ker φ・全射射影・像の群・全単射準同型（同型）。 -/
structure QuotientGroupData {G H : Grp} (φ : Hom G H) where
  /-- 商群 G/ker φ。 -/
  Q : Grp
  /-- 射影準同型 G → G/ker φ。 -/
  proj : Hom G Q
  /-- 射影は全射。 -/
  proj_surjective : ∀ x, ∃ a, proj.map a = x
  /-- 像 im φ を群として。 -/
  Im : Grp
  /-- 同型 φ̄ : G/ker φ → im φ。 -/
  iso : Hom Q Im
  /-- φ̄ は単射。 -/
  iso_injective : Hom.Injective iso
  /-- φ̄ は全射。 -/
  iso_surjective : ∀ y, ∃ x, iso.map x = y

/-- **証人 (M267F-9b)**: 第一同型定理の全条件を満たす。 -/
def quotientGroupData {G H : Grp} (φ : Hom G H) : QuotientGroupData φ where
  Q := quotientGroupN G (kerSubgroup φ) (ker_isNormal φ)
  proj := quotientProjN G (kerSubgroup φ) (ker_isNormal φ)
  proj_surjective := quotientProjN_surjective G (kerSubgroup φ) (ker_isNormal φ)
  Im := subgroupGrp (imSubgroup φ)
  iso := firstIsoHom φ
  iso_injective := firstIso_injective φ
  iso_surjective := firstIso_surjective φ

/-- **定理 (M267F-9c): 第一同型定理の存在**（G/ker φ ≅ im φ が
    全単射準同型として実現される）。 -/
theorem firstIsomorphism_exists {G H : Grp} (φ : Hom G H) :
    Nonempty (QuotientGroupData φ) :=
  ⟨quotientGroupData φ⟩

/-- **定理 (M267F-9d): 商群の存在**（正規部分群からの商群・全射射影・
    射影核 = N）。 -/
theorem quotientGroupN_exists (G : Grp) (N : Subgroup G)
    (hN : IsNormalSubgroup G N) :
    ∃ Q : Grp, ∃ proj : Hom G Q,
      (∀ x, ∃ a, proj.map a = x) ∧ (∀ a, proj.map a = Q.one ↔ N.mem a) :=
  ⟨quotientGroupN G N hN, quotientProjN G N hN,
    quotientProjN_surjective G N hN, quotientProjN_ker G N hN⟩

end IUT
