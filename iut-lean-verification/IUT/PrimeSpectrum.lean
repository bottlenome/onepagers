/-
  IUT/PrimeSpectrum.lean — M289F: 素スペクトル Spec R と Zariski 位相
                          （柱A: 実スキーム論への本物の先行建設）

  ── 主要成果の分類: **[実]**（本物の可換環 `CRing` の上に、本物のイデアル・
     本物の素イデアル・本物の Zariski 閉/開集合・本物の Zariski 位相の基底を
     ゼロから実構成する。toy 主語なし——主語は既存 M38 `CRing`／M264F `IUTField`
     という**本物の代数対象**そのもの）。

  complete_pct 影響: **柱A の実 mono-anabelian／実スキーム論の最下層を前進させる**。
  遠アーベル幾何・π₁^ét 復元は基礎体・基礎スキームの**位相空間としての Spec** を
  最下層に要求するが、現状コードベースには可換環上の一般イデアル／素イデアル／
  Zariski 位相が無かった（M264F で体の代数構造まで、M164 で特定の膜 (λ^k) の
  イデアル性まで、だが「素スペクトル Spec R + Zariski 位相」という位相空間は 0）。
  本ファイルはその位相空間 Spec R を**本物**に建てる。既存 `CRing`（M38）を土台に、
  一般イデアル `primeSpecIdeal`・素イデアル `primeSpecPrime`・Zariski 閉集合
  `primeSpecV`・基本開集合 `primeSpecD`・Zariski 位相の基底 `primeSpecBasicOpen`
  を実構成し、位相公理の本物の部分（V(0)=全体・V(R)=∅・antitone・基本開の補集合
  性・**D(fg)=D(f)∩D(g) の完全証明**・D(1)=全体・D(0)=∅・基底が有限交叉で閉じる）
  を sorry 皆無・新規 choice 皆無で閉じる。体 K の Spec が 1 点（唯一の素イデアル
  (0)）であることも本物に確定する。

  * M289F-1 `primeSpecIdeal`         — イデアル（0∈I・加法閉・環倍吸収 R·I⊆I）
  * M289F-2 `primeSpecPrime`         — 素イデアル（真イデアル + 素条件の witness 形
                                        ¬a∈P → ¬b∈P → ¬(ab)∈P、排中律回避）
  * M289F-3 `PrimeSpectrum`          — 素スペクトル（素イデアルを点とする空間）
  * M289F-4 `primeSpecZero/Unit/Principal/Inter Ideal` — 具体イデアル 4 種
  * M289F-5 `primeSpecV` + 基本性質  — Zariski 閉集合 V(0)/V(R)/antitone/V(I)∪V(J)
  * M289F-6 `primeSpecD` + 基本性質  — 基本開集合 D(f) の補集合性・**D(fg)=D(f)∩D(g)**
                                        （完全）・D(1)=全体・D(0)=∅
  * M289F-7 `primeSpecOpen`/`primeSpecBasicOpen` — Zariski 位相の骨組み
                                        （∅・全体・基本開の開性、基底の有限交叉閉性）
  * M289F-8 `primeSpecFieldZeroPrime` + `primeSpec_field_*` — 体の Spec は 1 点
  * M289F-9 `PrimeSpectrumSpace` / `primeSpec_topology_axioms` / `primeSpec_exists`
                                        — capstone（位相公理の本物の束ね）

  正直な限定（何が本物で何が未達か）:
  - **本物（完全証明）**: イデアル・素イデアルの公理系、Zariski 閉集合 V の
    V(0)=Spec 全体・V(R)=∅・反変単調性・V(I)∪V(J)⊆V(I∩J)、基本開 D の補集合性・
    **D(fg)=D(f)∩D(g)（両包含とも完全、素イデアル性 prime_witness を本質的に使用）**・
    D(1)=Spec 全体・D(0)=∅、Zariski 位相の ∅/全体/基本開の開性、**基底が有限交叉で
    閉じること**（D(fg) 経由、完全）、そして「体 K の Spec は (0) が唯一の素イデアル」
    （零イデアルが素であること = 体の整域性 M264F mul_ne_zero、非零元は素イデアルに
    属さないこと = 逆元で 1 を作る）は完全証明。
  - **正直申告（未達）**:
    ・素イデアルの素条件は選言形 `ab∈P → a∈P ∨ b∈P` ではなく**対偶 witness 形**
      `¬a∈P → ¬b∈P → ¬(ab)∈P` で述べる（抽象環上で選言を出すには所属判定の
      排中律を要し、本規約が証明本体での Classical.choice を禁ずるため。witness 形が
      構成的な本物の素イデアル内容であり、選言は古典論理でのみ従う）。
    ・素イデアルの**存在**（Krull = Zorn）は非構成的なので**仮定しない**。Spec は
      「与えられた素イデアルの点」の空間として扱う。体の (0) は本物で存在するので
      `primeSpec_exists` は体に対して本物に成立。
    ・V(I∩J)=V(I)∪V(J) は**易しい包含 V(I)∪V(J)⊆V(I∩J) のみ本物**。逆包含
      V(I∩J)⊆V(I)∪V(J) は「I∩J⊆P（素）→ I⊆P ∨ J⊆P」という選言を要し非構成的
      なため対象外（D(fg)=D(f)∩D(g) は基本開レベルで完全に閉じているので、位相の
      有限交叉の本物の核はそちらで達成）。
    ・体の Spec の一意性は「零元は属す ∧ 非零元は属さない」の構成的形で述べる
      （所属の ↔ 完全等号は 0 判定の排中律を要し、M264F の整域性と同じ正直な限定）。
    ・一般スキーム（構造層付き局所環空間 (Spec R, O_Spec)）は後続。ここは
      **位相空間 Spec R と Zariski 位相の基底**まで。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
-/
import IUT.Field

namespace IUT

/-! ## M289F-1: イデアル -/

/-- **M289F-1: 可換環 `R` のイデアル** — 部分集合 `mem : R.carrier → Prop` で、
    0 を含み、加法で閉じ、任意の環元 `r` による倍で吸収する（R·I ⊆ I）。
    （負元閉性は環倍 r = -1 から従うが、本規約では最小公理 0/加法/環倍で定義する。） -/
structure primeSpecIdeal (R : CRing) where
  /-- 所属述語。 -/
  mem : R.carrier → Prop
  /-- 0 ∈ I。 -/
  zero_mem : mem R.zero
  /-- 加法閉性: x,y ∈ I ⟹ x+y ∈ I。 -/
  add_mem : ∀ x y, mem x → mem y → mem (R.add x y)
  /-- 環倍吸収: x ∈ I ⟹ r·x ∈ I（任意の r で）。 -/
  smul_mem : ∀ r x, mem x → mem (R.mul r x)

/-- 真イデアル（1 ∉ I）。 -/
def primeSpec_isProper {R : CRing} (I : primeSpecIdeal R) : Prop := ¬ I.mem R.one

/-- イデアルの包含 I ⊆ J。 -/
def primeSpecSubset {R : CRing} (I J : primeSpecIdeal R) : Prop :=
  ∀ x, I.mem x → J.mem x

/-! ## M289F-2: 素イデアル -/

/-- **M289F-2: 素イデアル** — 真イデアル（1 ∉ P）で、**素条件の対偶 witness 形**
    `a ∉ P → b ∉ P → a·b ∉ P` を満たすもの。選言形 `a·b ∈ P → a ∈ P ∨ b ∈ P`
    は抽象環上で排中律を要するため、構成的に等価内容を持つ witness 形で述べる。 -/
structure primeSpecPrime (R : CRing) extends primeSpecIdeal R where
  /-- 真イデアル: 1 ∉ P。 -/
  proper : ¬ mem R.one
  /-- 素条件（witness 形）: a ∉ P かつ b ∉ P ならば a·b ∉ P。 -/
  prime_witness : ∀ a b, ¬ mem a → ¬ mem b → ¬ mem (R.mul a b)

/-! ## M289F-3: 素スペクトル -/

/-- **M289F-3: 素スペクトル Spec R** — 素イデアルを点とする空間。
    素イデアルの**存在**は非構成的（Krull = Zorn）なので仮定せず、
    「与えられた素イデアル」を点として扱う。 -/
structure PrimeSpectrum (R : CRing) where
  /-- 点となる素イデアル。 -/
  toPrime : primeSpecPrime R

/-! ## M289F-4: 具体イデアル 4 種 -/

/-- **零イデアル (0)** = {0}。 -/
def primeSpecZeroIdeal (R : CRing) : primeSpecIdeal R where
  mem := fun x => x = R.zero
  zero_mem := rfl
  add_mem := fun x y hx hy => by
    show R.add x y = R.zero
    rw [hx, hy, R.zero_add]
  smul_mem := fun r x hx => by
    show R.mul r x = R.zero
    rw [hx, R.mul_zero r]

/-- **単位イデアル (1)** = R 全体。 -/
def primeSpecUnitIdeal (R : CRing) : primeSpecIdeal R where
  mem := fun _ => True
  zero_mem := True.intro
  add_mem := fun _ _ _ _ => True.intro
  smul_mem := fun _ _ _ => True.intro

/-- **主イデアル (f)** = {r·f | r ∈ R}。 -/
def primeSpecPrincipalIdeal {R : CRing} (f : R.carrier) : primeSpecIdeal R where
  mem := fun x => ∃ r, x = R.mul r f
  zero_mem := by
    refine ⟨R.zero, ?_⟩
    rw [R.mul_comm R.zero f, R.mul_zero f]
  add_mem := fun x y hx hy => by
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨R.add a b, ?_⟩
    rw [ha, hb, R.right_distrib a b f]
  smul_mem := fun r x hx => by
    obtain ⟨a, ha⟩ := hx
    refine ⟨R.mul r a, ?_⟩
    rw [ha, R.mul_assoc r a f]

/-- **交イデアル I ∩ J**。 -/
def primeSpecInterIdeal {R : CRing} (I J : primeSpecIdeal R) : primeSpecIdeal R where
  mem := fun x => I.mem x ∧ J.mem x
  zero_mem := ⟨I.zero_mem, J.zero_mem⟩
  add_mem := fun x y hx hy =>
    ⟨I.add_mem x y hx.1 hy.1, J.add_mem x y hx.2 hy.2⟩
  smul_mem := fun r x hx =>
    ⟨I.smul_mem r x hx.1, J.smul_mem r x hx.2⟩

/-! ## M289F-5: Zariski 閉集合 V(I) と基本性質 -/

/-- **M289F-5: Zariski 閉集合 V(I)** = {P ∈ Spec R | I ⊆ P}。 -/
def primeSpecV {R : CRing} (I : primeSpecIdeal R) (P : PrimeSpectrum R) : Prop :=
  ∀ x, I.mem x → P.toPrime.mem x

/-- **V(0) = Spec R 全体** — 全ての素イデアルは 0 を含む。 -/
theorem primeSpec_V_zero {R : CRing} (P : PrimeSpectrum R) :
    primeSpecV (primeSpecZeroIdeal R) P := by
  intro x hx
  show P.toPrime.mem x
  rw [hx]
  exact P.toPrime.zero_mem

/-- **V(R) = ∅** — 単位イデアルを含む素イデアルは無い（1 ∉ P）。 -/
theorem primeSpec_V_one {R : CRing} (P : PrimeSpectrum R) :
    ¬ primeSpecV (primeSpecUnitIdeal R) P := by
  intro h
  apply P.toPrime.proper
  exact h R.one True.intro

/-- **反変単調性** — I ⊆ J ならば V(J) ⊆ V(I)。 -/
theorem primeSpec_V_antitone {R : CRing} (I J : primeSpecIdeal R)
    (hIJ : primeSpecSubset I J) (P : PrimeSpectrum R)
    (hP : primeSpecV J P) : primeSpecV I P := by
  intro x hx
  exact hP x (hIJ x hx)

/-- **V(I)∪V(J) ⊆ V(I∩J)**（易しい包含・本物）。逆包含は非構成的なので対象外。 -/
theorem primeSpec_V_inter {R : CRing} (I J : primeSpecIdeal R) (P : PrimeSpectrum R)
    (h : primeSpecV I P ∨ primeSpecV J P) :
    primeSpecV (primeSpecInterIdeal I J) P := by
  intro x hx
  cases h with
  | inl hI => exact hI x hx.1
  | inr hJ => exact hJ x hx.2

/-- **V((f)) = {P | f ∈ P}** — 主イデアル (f) を含むことは f ∈ P と同値。 -/
theorem primeSpec_V_principal {R : CRing} (f : R.carrier) (P : PrimeSpectrum R) :
    primeSpecV (primeSpecPrincipalIdeal f) P ↔ P.toPrime.mem f := by
  refine ⟨?_, ?_⟩
  · intro h
    exact h f ⟨R.one, (R.one_mul f).symm⟩
  · intro hf x hx
    obtain ⟨r, hr⟩ := hx
    rw [hr]
    exact P.toPrime.smul_mem r f hf

/-! ## M289F-6: 基本開集合 D(f) と基本性質 -/

/-- **M289F-6: 基本開集合 D(f)** = {P ∈ Spec R | f ∉ P} = Spec R ∖ V((f))。 -/
def primeSpecD {R : CRing} (f : R.carrier) (P : PrimeSpectrum R) : Prop :=
  ¬ P.toPrime.mem f

/-- **D(f) = V((f)) の補集合** — f ∉ P ⟺ ¬(P ∈ V((f)))。 -/
theorem primeSpec_D_compl {R : CRing} (f : R.carrier) (P : PrimeSpectrum R) :
    primeSpecD f P ↔ ¬ primeSpecV (primeSpecPrincipalIdeal f) P := by
  refine ⟨?_, ?_⟩
  · intro h hV
    exact h ((primeSpec_V_principal f P).mp hV)
  · intro h hf
    exact h ((primeSpec_V_principal f P).mpr hf)

/-- **D(fg) = D(f) ∩ D(g)（完全証明）** — 逆向きに素イデアル性 prime_witness を
    本質的に使用する。 -/
theorem primeSpec_D_mul {R : CRing} (f g : R.carrier) (P : PrimeSpectrum R) :
    primeSpecD (R.mul f g) P ↔ (primeSpecD f P ∧ primeSpecD g P) := by
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro hf
      apply h
      have hgf : P.toPrime.mem (R.mul g f) := P.toPrime.smul_mem g f hf
      rw [R.mul_comm g f] at hgf
      exact hgf
    · intro hg
      apply h
      exact P.toPrime.smul_mem f g hg
  · intro hfg
    exact P.toPrime.prime_witness f g hfg.1 hfg.2

/-- **D(1) = Spec R 全体** — 1 ∉ P は真イデアル性そのもの。 -/
theorem primeSpec_D_one {R : CRing} (P : PrimeSpectrum R) :
    primeSpecD R.one P :=
  P.toPrime.proper

/-- **D(0) = ∅** — 0 ∈ P は常に成り立つので f = 0 では D は空。 -/
theorem primeSpec_D_zero {R : CRing} (P : PrimeSpectrum R) :
    ¬ primeSpecD R.zero P := by
  intro h
  exact h P.toPrime.zero_mem

/-! ## M289F-7: Zariski 位相の骨組み -/

/-- **開集合（閉集合 V(I) の補集合として）** — U が或るイデアル I について
    V(I) の補集合であること。 -/
def primeSpecOpen {R : CRing} (U : PrimeSpectrum R → Prop) : Prop :=
  ∃ I : primeSpecIdeal R, ∀ P, U P ↔ ¬ primeSpecV I P

/-- **∅ は開**（= V(0) = 全体 の補集合）。 -/
theorem primeSpec_open_empty {R : CRing} :
    primeSpecOpen (fun _ : PrimeSpectrum R => False) := by
  refine ⟨primeSpecZeroIdeal R, ?_⟩
  intro P
  refine ⟨?_, ?_⟩
  · intro h
    exact h.elim
  · intro h
    exact h (primeSpec_V_zero P)

/-- **全体 Spec R は開**（= V(R) = ∅ の補集合）。 -/
theorem primeSpec_open_univ {R : CRing} :
    primeSpecOpen (fun _ : PrimeSpectrum R => True) := by
  refine ⟨primeSpecUnitIdeal R, ?_⟩
  intro P
  refine ⟨?_, ?_⟩
  · intro _
    exact primeSpec_V_one P
  · intro _
    exact True.intro

/-- **基本開 D(f) は開**（= V((f)) の補集合）。 -/
theorem primeSpec_open_basic {R : CRing} (f : R.carrier) :
    primeSpecOpen (primeSpecD f) := by
  refine ⟨primeSpecPrincipalIdeal f, ?_⟩
  intro P
  exact primeSpec_D_compl f P

/-- **基底となる基本開集合** — U が或る f について D(f) に一致すること。 -/
def primeSpecBasicOpen {R : CRing} (U : PrimeSpectrum R → Prop) : Prop :=
  ∃ f, ∀ P, U P ↔ primeSpecD f P

/-- **基底公理 (1): 全空間は基本開の和** — 全体 Spec R は D(1)（基本開）。 -/
theorem primeSpec_basic_whole {R : CRing} :
    primeSpecBasicOpen (fun _ : PrimeSpectrum R => True) := by
  refine ⟨R.one, ?_⟩
  intro P
  refine ⟨?_, ?_⟩
  · intro _
    exact primeSpec_D_one P
  · intro _
    exact True.intro

/-- **基底公理 (2): 基本開は有限交叉で閉じる（完全）** — D(f) ∩ D(g) = D(fg)。
    Zariski 位相の有限交叉公理の本物の核を、D(fg)=D(f)∩D(g) の完全証明で達成する。 -/
theorem primeSpec_basic_inter {R : CRing} {U W : PrimeSpectrum R → Prop}
    (hU : primeSpecBasicOpen U) (hW : primeSpecBasicOpen W) :
    primeSpecBasicOpen (fun P => U P ∧ W P) := by
  obtain ⟨f, hf⟩ := hU
  obtain ⟨g, hg⟩ := hW
  refine ⟨R.mul f g, ?_⟩
  intro P
  refine ⟨?_, ?_⟩
  · intro h
    exact (primeSpec_D_mul f g P).mpr ⟨(hf P).mp h.1, (hg P).mp h.2⟩
  · intro h
    have hd := (primeSpec_D_mul f g P).mp h
    exact ⟨(hf P).mpr hd.1, (hg P).mpr hd.2⟩

/-! ## M289F-8: 体の Spec は 1 点（唯一の素イデアル (0)） -/

/-- **M289F-8: 体 F の零イデアル (0) は素イデアル** — 真イデアル性は 1 ≠ 0、
    素条件は体の整域性 mul_ne_zero（a ≠ 0 ∧ b ≠ 0 → ab ≠ 0）。 -/
def primeSpecFieldZeroPrime (F : IUTField) : primeSpecPrime F.toCRing where
  mem := fun x => x = F.zero
  zero_mem := rfl
  add_mem := fun x y hx hy => by
    show F.toCRing.add x y = F.zero
    rw [hx, hy, F.toCRing.zero_add]
  smul_mem := fun r x hx => by
    show F.toCRing.mul r x = F.zero
    rw [hx, F.toCRing.mul_zero r]
  proper := F.one_ne_zero
  prime_witness := fun a b ha hb => F.mul_ne_zero ha hb

/-- 体の Spec の点（零イデアル (0)）。 -/
def primeSpecFieldPoint (F : IUTField) : PrimeSpectrum F.toCRing where
  toPrime := primeSpecFieldZeroPrime F

/-- **零元は任意の素イデアルに属す**（イデアル公理）。 -/
theorem primeSpec_field_zero_mem (F : IUTField) (P : PrimeSpectrum F.toCRing) :
    P.toPrime.mem F.zero :=
  P.toPrime.zero_mem

/-- **体では非零元はどの素イデアルにも属さない** — 属せば逆元で 1 を作れて真イデアル
    性に反する。これが「体の唯一の素イデアルは (0)」の構成的核（M264F の整域性と
    同じ正直な限定で、所属の完全等号 ↔ は 0 判定の排中律を要するため出さない）。 -/
theorem primeSpec_field_nonzero_not_mem (F : IUTField)
    (P : PrimeSpectrum F.toCRing) {x : F.carrier} (hx : x ≠ F.zero) :
    ¬ P.toPrime.mem x := by
  intro hmem
  apply P.toPrime.proper
  have h1 : P.toPrime.mem (F.mul (F.inv x) x) := P.toPrime.smul_mem (F.inv x) x hmem
  rw [F.inv_mul_cancel hx] at h1
  exact h1

/-- **体の Spec は 1 点**（束ね: 零元は属す ∧ 非零元は属さない）。 -/
theorem primeSpec_field_point (F : IUTField) (P : PrimeSpectrum F.toCRing) :
    P.toPrime.mem F.zero ∧
      (∀ x : F.carrier, x ≠ F.zero → ¬ P.toPrime.mem x) :=
  ⟨primeSpec_field_zero_mem F P, fun _ hx => primeSpec_field_nonzero_not_mem F P hx⟩

/-! ## M289F-9: capstone -/

/-- **M289F-9a: 素スペクトルの位相空間データ** — Zariski 閉集合 V の基本性質と、
    基本開集合 D の基本性質（特に D(fg)=D(f)∩D(g)）を束ねる位相公理レコード。 -/
structure PrimeSpectrumSpace (R : CRing) where
  /-- V(0) = Spec R 全体。 -/
  V_zero : ∀ P : PrimeSpectrum R, primeSpecV (primeSpecZeroIdeal R) P
  /-- V(R) = ∅。 -/
  V_one : ∀ P : PrimeSpectrum R, ¬ primeSpecV (primeSpecUnitIdeal R) P
  /-- 反変単調性。 -/
  V_antitone : ∀ (I J : primeSpecIdeal R), primeSpecSubset I J →
      ∀ P : PrimeSpectrum R, primeSpecV J P → primeSpecV I P
  /-- V(I)∪V(J) ⊆ V(I∩J)。 -/
  V_inter : ∀ (I J : primeSpecIdeal R) (P : PrimeSpectrum R),
      (primeSpecV I P ∨ primeSpecV J P) → primeSpecV (primeSpecInterIdeal I J) P
  /-- D(f) は V((f)) の補集合。 -/
  D_compl : ∀ (f : R.carrier) (P : PrimeSpectrum R),
      primeSpecD f P ↔ ¬ primeSpecV (primeSpecPrincipalIdeal f) P
  /-- **D(fg) = D(f) ∩ D(g)（完全）**。 -/
  D_mul : ∀ (f g : R.carrier) (P : PrimeSpectrum R),
      primeSpecD (R.mul f g) P ↔ (primeSpecD f P ∧ primeSpecD g P)
  /-- D(1) = Spec R 全体。 -/
  D_one : ∀ P : PrimeSpectrum R, primeSpecD R.one P
  /-- D(0) = ∅。 -/
  D_zero : ∀ P : PrimeSpectrum R, ¬ primeSpecD R.zero P

/-- **M289F-9b: 任意の可換環 R の Zariski 位相公理（本物の部分）を束ねる**。 -/
def primeSpec_topology_axioms (R : CRing) : PrimeSpectrumSpace R where
  V_zero := primeSpec_V_zero
  V_one := primeSpec_V_one
  V_antitone := primeSpec_V_antitone
  V_inter := primeSpec_V_inter
  D_compl := primeSpec_D_compl
  D_mul := primeSpec_D_mul
  D_one := primeSpec_D_one
  D_zero := primeSpec_D_zero

/-- **M289F-9c: 体の Spec は空でない**（本物の点 (0) が存在）。素イデアルの一般存在
    （Krull=Zorn）は非構成的なので仮定しないが、体では (0) が本物の素点として存在。 -/
theorem primeSpec_exists (F : IUTField) : Nonempty (PrimeSpectrum F.toCRing) :=
  ⟨primeSpecFieldPoint F⟩

/-- **M289F-9d: Zariski 位相の基底公理（本物）を束ねる** — 全空間 = D(1)、
    有限交叉 D(f)∩D(g) = D(fg)。位相の有限交叉公理の本物の核。 -/
structure PrimeSpectrumBasis (R : CRing) where
  /-- 全空間は基本開 D(1)。 -/
  basis_whole : primeSpecBasicOpen (fun _ : PrimeSpectrum R => True)
  /-- 基本開は有限交叉で閉じる（D(fg)=D(f)∩D(g)）。 -/
  basis_inter : ∀ {U W : PrimeSpectrum R → Prop},
      primeSpecBasicOpen U → primeSpecBasicOpen W →
      primeSpecBasicOpen (fun P => U P ∧ W P)

/-- **M289F-9e: 任意の R の Zariski 基底公理を束ねる**。 -/
def primeSpec_basis_axioms (R : CRing) : PrimeSpectrumBasis R where
  basis_whole := primeSpec_basic_whole
  basis_inter := primeSpec_basic_inter

end IUT
