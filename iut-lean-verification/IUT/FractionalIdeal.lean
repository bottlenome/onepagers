/-
  IUT/FractionalIdeal.lean — M302F（柱 A 先行建設: 整域の分数イデアルと
                             その積・可逆性 — イデアル類群／Dedekind への土台）

  ── 主要成果の分類: **[実]**（本物の整域 `Domain`＝M266F の上に、本物の
     分数体 K=Frac(D)（M266F fracRing）の中の本物の D-部分加群として分数
     イデアルを実構成し、本物の積・本物の単項分数イデアルの可逆性を証明する。
     toy 主語なし——主語は M266F `Domain`／`fracRing` という**本物の代数対象**）。

  complete_pct 影響: **柱 A の実イデアル理論（イデアル類群 Cl(D)・Dedekind 整域
  への最下層）を前進させる**。現状コードベースには可換環の通常イデアル（M289F
  primeSpecIdeal）と分数体 Frac(D)（M266F）はあったが、両者を繋ぐ「Frac(D) の中の
  D-部分加群としての分数イデアル」と「その積・単項の可逆性」は 0 であった。本ファイル
  はそれを**本物**に建てる。とりわけ (1) 分数イデアルの積が再び分数イデアルであること
  （共通分母 dd' の実構成）と (2) 単項分数イデアル (a)（a∈K*）が可逆であること
  ((a)·(a⁻¹)=D、K の環法則から）を sorry 皆無・新規 choice 皆無で完全証明する。

  * M302F-1 `fracIdEmb`/`fracIdSmul`     — 埋め込み ι:D→K と D-スカラー作用、
                                           ι の 0/1/積/和 の保存補題
  * M302F-2 `fracIdFractional`           — 分数イデアル（D-部分加群 + 共通分母
                                           witness ∃d≠0, dI⊆ι(D) を Prop で）
  * M302F-3 `fracIdOfIntegral`/`fracIdZero`/`fracIdOne`
                                         — 整イデアル→分数イデアル（d=1）、
                                           零イデアル (0)、単位イデアル D=ι(D)
  * M302F-4 `fracIdPrincipal`            — 単項分数イデアル (a)=aD（a∈K）、
                                           分数性は Quot.ind で共通分母を抽出
  * M302F-5 `fracIdMulGen`/`fracIdMul`   — 積 I·J（有限和 Σxᵢyᵢ の生成する
                                           部分加群、帰納生成）。**積は分数
                                           イデアル**（共通分母 dd'、完全証明）
  * M302F-6 `fracId_mul_comm`/`fracId_one_mul`/`fracId_mul_congr_*`
                                         — 積の可換性・単位元 D·I=I（完全）、
                                           mem 同値での積の合同
  * M302F-7 `fracId_principal_mul`/`_assoc`/`_comm`/`_one_eq`
                                         — (a)·(b)=(ab)（完全）→ 単項分数
                                           イデアルは積で可換モノイド（K の環法則）
  * M302F-8 `fracIdInvertible`/`fracId_principal_invertible`/`_is_invertible`
                                         — 可逆分数イデアル、**単項 (a)（a∈K*）
                                           は可逆**（(a)(a⁻¹)=D、完全証明）
  * M302F-9 capstone `FractionalIdealData`/`fracId_exists`/`FracIdCartierGroup`/
                     `fracId_cartier_group`/`fracId_mul_monoid`
                                         — 分数イデアルデータの束ね、単項分数
                                           イデアル（Cartier 因子）の群構造の土台

  正直な限定（何が本物で何が未達か）:
  - **本物（完全証明）**:
    ・分数イデアルの D-部分加群公理・共通分母（分数性）witness。
    ・整イデアル→分数イデアル（d=1）、零/単位イデアル。
    ・単項分数イデアル (a)=aD（a∈K）とその分数性（a の代表分母を Quot.ind で抽出）。
    ・**積 I·J が再び分数イデアルであること（共通分母 dd' の実構成、帰納法で完全）**。
    ・積の可換性 fracId_mul_comm、単位元 fracId_one_mul（D·I=I、両包含とも完全）。
    ・**(a)·(b)=(ab)（両包含とも完全、K の環法則）** → 単項分数イデアルが積で
      可換モノイド（結合・可換・単位、全て K.mul の法則へ帰着）。
    ・**単項分数イデアル (a)（a∈K*）の可逆性 (a)(a⁻¹)=D（完全証明）**。
    ・単項イデアルは可逆（fracId_principal_is_invertible、完全）。
  - **正直申告（未達・骨組み・後続）**:
    ・分数性（共通分母）は選言でなく **∃ 分母 witness 形**の Prop で述べる。
    ・一般の積の**結合律**は「生成の完全性（有限和が張る部分加群）」の帰納的
      再結合を要し、本ファイルでは**単項分数イデアルに限り完全証明**（K の
      mul_assoc）。一般 I·(J·L)=(I·J)·L は骨組み（後続）。
    ・**可逆イデアルが群をなす完全証明**（Dedekind 整域で全非零イデアルが可逆）は
      Dedekind 性（Noether+整閉+次元1）を要すので**骨組み/後続**。本ファイルは
      「**単項分数イデアル（=principal Cartier 因子）が積で可換群をなす土台**」
      （FracIdCartierGroup）まで本物で建てる。
    ・イデアル類群 Cl(D)=分数イデアル/単項 は骨組み（後続）。
    ・「体上は全分数イデアルが (a) or 0」は D↔体の橋渡しを要すので、本ファイルでは
      「零・単位イデアルは単項」(fracId_field_principal) の本物の部分のみ
      （全分類は骨組み・後続）。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無。
-/
import IUT.FractionField
import IUT.PrimeSpectrum

namespace IUT

/-! ## M302F-1: 埋め込み ι:D→K と D-スカラー作用 -/

/-- **M302F-1a: 埋め込み** ι : D → K=Frac(D)（a ↦ a/1、M266F fracOfRing の map）。 -/
def fracIdEmb (D : Domain) (a : D.R.carrier) : (fracRing D).carrier :=
  (fracOfRing D).map a

/-- **M302F-1b: D-スカラー作用** d·x := ι(d)·x（K の乗法で D が K に作用）。 -/
def fracIdSmul (D : Domain) (d : D.R.carrier) (x : (fracRing D).carrier) :
    (fracRing D).carrier :=
  (fracRing D).mul (fracIdEmb D d) x

/-- ι(0) = 0（代表が一致し定義的に等しい）。 -/
theorem fracIdEmb_zero (D : Domain) : fracIdEmb D D.R.zero = (fracRing D).zero := rfl

/-- ι(1) = 1。 -/
theorem fracIdEmb_one (D : Domain) : fracIdEmb D D.R.one = (fracRing D).one :=
  (fracOfRing D).map_one

/-- ι(a+b) = ι(a)+ι(b)。 -/
theorem fracIdEmb_add (D : Domain) (a b : D.R.carrier) :
    fracIdEmb D (D.R.add a b) = (fracRing D).add (fracIdEmb D a) (fracIdEmb D b) :=
  (fracOfRing D).map_add a b

/-- ι(a·b) = ι(a)·ι(b)。 -/
theorem fracIdEmb_mul (D : Domain) (a b : D.R.carrier) :
    fracIdEmb D (D.R.mul a b) = (fracRing D).mul (fracIdEmb D a) (fracIdEmb D b) :=
  (fracOfRing D).map_mul a b

/-- **鍵補題**: ι(p.den)·[p] = ι(p.num)（代表 p=n/m に対し m·(n/m)=n）。
    単項イデアルの分数性の核。 -/
theorem fracIdEmb_den_mul_class (D : Domain) (p : PreFrac D) :
    (fracRing D).mul (fracIdEmb D p.den) (Quot.mk (fracRel D) p)
      = fracIdEmb D p.num := by
  show Quot.mk (fracRel D) (pfMul (pfOfElem p.den) p)
    = Quot.mk (fracRel D) (pfOfElem p.num)
  apply Quot.sound
  show D.R.mul (D.R.mul p.den p.num) D.R.one
    = D.R.mul p.num (D.R.mul D.R.one p.den)
  rw [cring_mul_one, D.R.one_mul, D.R.mul_comm p.den p.num]

/-! ## M302F-2: 分数イデアル -/

/-- **M302F-2: 分数イデアル** — K=Frac(D) の D-部分加群 I（0 を含み・加法閉・
    D-スカラー作用で閉じる）で、**共通分母**を持つもの: ∃ d≠0∈D, d·I ⊆ ι(D)
    （各 x∈I に対し d·x が ι(D) の像に入る）。`isFractional` を単一の存在命題
    （Prop）にすることで、a∈K の代表分母を Quot.ind で構成的に供給できる。 -/
structure fracIdFractional (D : Domain) where
  /-- 所属述語。 -/
  mem : (fracRing D).carrier → Prop
  /-- 0 ∈ I。 -/
  zero_mem : mem (fracRing D).zero
  /-- 加法閉性。 -/
  add_mem : ∀ x y, mem x → mem y → mem ((fracRing D).add x y)
  /-- D-スカラー作用で閉じる（d·x = ι(d)·x ∈ I）。 -/
  smul_mem : ∀ (d : D.R.carrier) x, mem x → mem (fracIdSmul D d x)
  /-- **分数性（共通分母 witness）**: ∃ d≠0, ∀ x∈I, d·x ∈ ι(D)。 -/
  isFractional : ∃ d : D.R.carrier, d ≠ D.R.zero ∧
    ∀ x, mem x → ∃ e : D.R.carrier,
      (fracRing D).mul (fracIdEmb D d) x = fracIdEmb D e

/-- 分数イデアルの包含。 -/
def fracIdSubset {D : Domain} (I J : fracIdFractional D) : Prop :=
  ∀ x, I.mem x → J.mem x

/-! ## M302F-3: 整イデアル→分数イデアル、零/単位イデアル -/

/-- 整イデアル = D の通常イデアル（M289F primeSpecIdeal の別名）。 -/
def fracIdIntegral (D : Domain) := primeSpecIdeal D.R

/-- **M302F-3a: 整イデアル I ⊆ D は分数イデアル**（像 ι(I)、共通分母 d=1）。
    整イデアルが分数イデアルであることの本物の witness。 -/
def fracIdOfIntegral (D : Domain) (I : primeSpecIdeal D.R) : fracIdFractional D where
  mem := fun x => ∃ a : D.R.carrier, I.mem a ∧ x = fracIdEmb D a
  zero_mem := ⟨D.R.zero, I.zero_mem, rfl⟩
  add_mem := fun x y hx hy => by
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    exact ⟨D.R.add a b, I.add_mem a b ha hb, by rw [hxa, hyb, ← fracIdEmb_add]⟩
  smul_mem := fun d x hx => by
    obtain ⟨a, ha, hxa⟩ := hx
    refine ⟨D.R.mul d a, I.smul_mem d a ha, ?_⟩
    show (fracRing D).mul (fracIdEmb D d) x = fracIdEmb D (D.R.mul d a)
    rw [hxa, ← fracIdEmb_mul]
  isFractional := ⟨D.R.one, D.one_ne_zero, fun x hx => by
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨a, by rw [hxa, fracIdEmb_one, (fracRing D).one_mul]⟩⟩

/-- **M302F-3b: 零イデアル (0)** = {0}。 -/
def fracIdZero (D : Domain) : fracIdFractional D where
  mem := fun x => x = (fracRing D).zero
  zero_mem := rfl
  add_mem := fun x y hx hy => by rw [hx, hy, (fracRing D).zero_add]
  smul_mem := fun d x hx => by
    show (fracRing D).mul (fracIdEmb D d) x = (fracRing D).zero
    rw [hx, CRing.mul_zero]
  isFractional := ⟨D.R.one, D.one_ne_zero, fun x hx =>
    ⟨D.R.zero, by
      show (fracRing D).mul (fracIdEmb D D.R.one) x = fracIdEmb D D.R.zero
      rw [hx, CRing.mul_zero, fracIdEmb_zero]⟩⟩

/-- **M302F-3c: 単位イデアル D** = ι(D)（積の単位元）。 -/
def fracIdOne (D : Domain) : fracIdFractional D where
  mem := fun x => ∃ e : D.R.carrier, x = fracIdEmb D e
  zero_mem := ⟨D.R.zero, rfl⟩
  add_mem := fun x y hx hy => by
    obtain ⟨ex, hxe⟩ := hx
    obtain ⟨ey, hye⟩ := hy
    exact ⟨D.R.add ex ey, by rw [hxe, hye, ← fracIdEmb_add]⟩
  smul_mem := fun d x hx => by
    obtain ⟨ex, hxe⟩ := hx
    refine ⟨D.R.mul d ex, ?_⟩
    show (fracRing D).mul (fracIdEmb D d) x = fracIdEmb D (D.R.mul d ex)
    rw [hxe, ← fracIdEmb_mul]
  isFractional := ⟨D.R.one, D.one_ne_zero, fun x hx => by
    obtain ⟨ex, hxe⟩ := hx
    exact ⟨ex, by rw [hxe, fracIdEmb_one, (fracRing D).one_mul]⟩⟩

/-! ## M302F-4: 単項分数イデアル (a) = aD -/

/-- **M302F-4: 単項分数イデアル (a) = aD**（a∈K で生成、a·ι(D)）。
    分数性は a の代表 p=n/m の分母 m が共通分母を与える（Quot.ind で抽出）。 -/
def fracIdPrincipal (D : Domain) (a : (fracRing D).carrier) : fracIdFractional D where
  mem := fun x => ∃ e : D.R.carrier, x = (fracRing D).mul a (fracIdEmb D e)
  zero_mem := ⟨D.R.zero, by rw [fracIdEmb_zero, CRing.mul_zero]⟩
  add_mem := fun x y hx hy => by
    obtain ⟨ex, hxe⟩ := hx
    obtain ⟨ey, hye⟩ := hy
    refine ⟨D.R.add ex ey, ?_⟩
    rw [hxe, hye, ← (fracRing D).left_distrib, ← fracIdEmb_add]
  smul_mem := fun d x hx => by
    obtain ⟨ex, hxe⟩ := hx
    refine ⟨D.R.mul d ex, ?_⟩
    show (fracRing D).mul (fracIdEmb D d) x
      = (fracRing D).mul a (fracIdEmb D (D.R.mul d ex))
    rw [hxe, ← (fracRing D).mul_assoc, (fracRing D).mul_comm (fracIdEmb D d) a,
      (fracRing D).mul_assoc, ← fracIdEmb_mul]
  isFractional := by
    induction a using Quot.ind
    rename_i p
    refine ⟨p.den, p.den_ne, ?_⟩
    intro x hx
    obtain ⟨ex, hxe⟩ := hx
    refine ⟨D.R.mul p.num ex, ?_⟩
    rw [hxe, ← (fracRing D).mul_assoc, fracIdEmb_den_mul_class, ← fracIdEmb_mul]

/-! ## M302F-5: 積 I·J -/

/-- **M302F-5a: 積の生成述語** — {Σ xᵢyᵢ | xᵢ∈I, yᵢ∈J} が生成する D-部分加群を
    帰納的に定義（基底 x·y、0、加法閉、D-スカラー閉）。 -/
inductive fracIdMulGen (D : Domain) (I J : fracIdFractional D) :
    (fracRing D).carrier → Prop where
  | base : ∀ x y, I.mem x → J.mem y → fracIdMulGen D I J ((fracRing D).mul x y)
  | zero : fracIdMulGen D I J (fracRing D).zero
  | add : ∀ a b, fracIdMulGen D I J a → fracIdMulGen D I J b →
      fracIdMulGen D I J ((fracRing D).add a b)
  | smul : ∀ (d : D.R.carrier) a, fracIdMulGen D I J a →
      fracIdMulGen D I J (fracIdSmul D d a)

/-- **M302F-5b: 積 I·J は分数イデアル**（共通分母 dd' の実構成、帰納法で完全）。 -/
def fracIdMul (D : Domain) (I J : fracIdFractional D) : fracIdFractional D where
  mem := fracIdMulGen D I J
  zero_mem := fracIdMulGen.zero
  add_mem := fun x y hx hy => fracIdMulGen.add x y hx hy
  smul_mem := fun d x hx => fracIdMulGen.smul d x hx
  isFractional := by
    obtain ⟨dI, hdI, hI⟩ := I.isFractional
    obtain ⟨dJ, hdJ, hJ⟩ := J.isFractional
    refine ⟨D.R.mul dI dJ, domain_mul_ne_zero D hdI hdJ, ?_⟩
    intro x hgen
    induction hgen with
    | base p q hp hq =>
      obtain ⟨eI, heI⟩ := hI p hp
      obtain ⟨eJ, heJ⟩ := hJ q hq
      refine ⟨D.R.mul eI eJ, ?_⟩
      show (fracRing D).mul (fracIdEmb D (D.R.mul dI dJ)) ((fracRing D).mul p q)
        = fracIdEmb D (D.R.mul eI eJ)
      rw [fracIdEmb_mul D dI dJ,
        cring_mul_mul_swap' (fracRing D) (fracIdEmb D dI) (fracIdEmb D dJ) p q,
        heI, heJ, ← fracIdEmb_mul D eI eJ]
    | zero => exact ⟨D.R.zero, by rw [CRing.mul_zero, fracIdEmb_zero]⟩
    | add p q _ _ ihp ihq =>
      obtain ⟨ep, hep⟩ := ihp
      obtain ⟨eq, heq⟩ := ihq
      refine ⟨D.R.add ep eq, ?_⟩
      rw [(fracRing D).left_distrib, hep, heq, ← fracIdEmb_add]
    | smul d p _ ih =>
      obtain ⟨ep, hep⟩ := ih
      refine ⟨D.R.mul d ep, ?_⟩
      show (fracRing D).mul (fracIdEmb D (D.R.mul dI dJ))
          ((fracRing D).mul (fracIdEmb D d) p)
        = fracIdEmb D (D.R.mul d ep)
      rw [← (fracRing D).mul_assoc,
        (fracRing D).mul_comm (fracIdEmb D (D.R.mul dI dJ)) (fracIdEmb D d),
        (fracRing D).mul_assoc, hep, ← fracIdEmb_mul]

/-- 積の分数性を外に取り出す（積が分数イデアルであることの明示）。 -/
theorem fracId_mul_isFractional (D : Domain) (I J : fracIdFractional D) :
    ∃ d : D.R.carrier, d ≠ D.R.zero ∧
      ∀ x, (fracIdMul D I J).mem x →
        ∃ e : D.R.carrier,
          (fracRing D).mul (fracIdEmb D d) x = fracIdEmb D e :=
  (fracIdMul D I J).isFractional

/-! ## M302F-6: 可換性・単位元・合同 -/

/-- 生成述語は I,J 交換で対応（可換性の核）。 -/
theorem fracIdMulGen_comm (D : Domain) {I J : fracIdFractional D}
    {x : (fracRing D).carrier} (h : fracIdMulGen D I J x) :
    fracIdMulGen D J I x := by
  induction h with
  | base p q hp hq =>
    rw [(fracRing D).mul_comm p q]
    exact fracIdMulGen.base q p hq hp
  | zero => exact fracIdMulGen.zero
  | add p q _ _ ihp ihq => exact fracIdMulGen.add p q ihp ihq
  | smul d p _ ih => exact fracIdMulGen.smul d p ih

/-- **M302F-6a: 積は可換** I·J = J·I（mem 同値、完全）。 -/
theorem fracId_mul_comm (D : Domain) (I J : fracIdFractional D)
    (x : (fracRing D).carrier) :
    (fracIdMul D I J).mem x ↔ (fracIdMul D J I).mem x :=
  ⟨fracIdMulGen_comm D, fracIdMulGen_comm D⟩

/-- 生成述語は左因子の mem 同値で合同。 -/
theorem fracIdMulGen_congr_left (D : Domain) {I I' J : fracIdFractional D}
    (h : ∀ y, I.mem y ↔ I'.mem y) {x : (fracRing D).carrier}
    (hx : fracIdMulGen D I J x) : fracIdMulGen D I' J x := by
  induction hx with
  | base p q hp hq => exact fracIdMulGen.base p q ((h p).mp hp) hq
  | zero => exact fracIdMulGen.zero
  | add p q _ _ ihp ihq => exact fracIdMulGen.add p q ihp ihq
  | smul d p _ ih => exact fracIdMulGen.smul d p ih

/-- 生成述語は右因子の mem 同値で合同。 -/
theorem fracIdMulGen_congr_right (D : Domain) {I J J' : fracIdFractional D}
    (h : ∀ y, J.mem y ↔ J'.mem y) {x : (fracRing D).carrier}
    (hx : fracIdMulGen D I J x) : fracIdMulGen D I J' x := by
  induction hx with
  | base p q hp hq => exact fracIdMulGen.base p q hp ((h q).mp hq)
  | zero => exact fracIdMulGen.zero
  | add p q _ _ ihp ihq => exact fracIdMulGen.add p q ihp ihq
  | smul d p _ ih => exact fracIdMulGen.smul d p ih

/-- **M302F-6b: 積は左因子の mem 同値で合同**。 -/
theorem fracId_mul_congr_left (D : Domain) {I I' : fracIdFractional D}
    (h : ∀ y, I.mem y ↔ I'.mem y) (J : fracIdFractional D)
    (x : (fracRing D).carrier) :
    (fracIdMul D I J).mem x ↔ (fracIdMul D I' J).mem x :=
  ⟨fracIdMulGen_congr_left D h, fracIdMulGen_congr_left D (fun y => (h y).symm)⟩

/-- **M302F-6c: 積は右因子の mem 同値で合同**。 -/
theorem fracId_mul_congr_right (D : Domain) {J J' : fracIdFractional D}
    (h : ∀ y, J.mem y ↔ J'.mem y) (I : fracIdFractional D)
    (x : (fracRing D).carrier) :
    (fracIdMul D I J).mem x ↔ (fracIdMul D I J').mem x :=
  ⟨fracIdMulGen_congr_right D h, fracIdMulGen_congr_right D (fun y => (h y).symm)⟩

/-- **M302F-6d: 単位元** D·I = I（両包含とも完全、smul_mem を本質使用）。 -/
theorem fracId_one_mul (D : Domain) (I : fracIdFractional D)
    (x : (fracRing D).carrier) :
    (fracIdMul D (fracIdOne D) I).mem x ↔ I.mem x := by
  refine ⟨?_, ?_⟩
  · intro hgen
    induction hgen with
    | base p q hp hq =>
      obtain ⟨e, he⟩ := hp
      rw [he]
      exact I.smul_mem e q hq
    | zero => exact I.zero_mem
    | add p q _ _ ihp ihq => exact I.add_mem p q ihp ihq
    | smul d p _ ih => exact I.smul_mem d p ih
  · intro hx
    have h := fracIdMulGen.base (D := D) (I := fracIdOne D) (J := I)
      (fracIdEmb D D.R.one) x ⟨D.R.one, rfl⟩ hx
    rw [fracIdEmb_one, (fracRing D).one_mul] at h
    exact h

/-! ## M302F-7: 単項分数イデアルの積 = 積の単項（(a)(b)=(ab)） -/

/-- **M302F-7a: (a)·(b) = (ab)**（両包含とも完全、K の環法則）。 -/
theorem fracId_principal_mul (D : Domain) (a b : (fracRing D).carrier)
    (x : (fracRing D).carrier) :
    (fracIdMul D (fracIdPrincipal D a) (fracIdPrincipal D b)).mem x ↔
      (fracIdPrincipal D ((fracRing D).mul a b)).mem x := by
  refine ⟨?_, ?_⟩
  · intro hgen
    induction hgen with
    | base p q hp hq =>
      obtain ⟨ep, hep⟩ := hp
      obtain ⟨eq, heq⟩ := hq
      refine ⟨D.R.mul ep eq, ?_⟩
      rw [hep, heq,
        cring_mul_mul_swap' (fracRing D) a (fracIdEmb D ep) b (fracIdEmb D eq),
        ← fracIdEmb_mul]
    | zero =>
      exact ⟨D.R.zero, by rw [fracIdEmb_zero, CRing.mul_zero]⟩
    | add p q _ _ ihp ihq =>
      obtain ⟨ep, hep⟩ := ihp
      obtain ⟨eq, heq⟩ := ihq
      refine ⟨D.R.add ep eq, ?_⟩
      rw [hep, heq, ← (fracRing D).left_distrib, ← fracIdEmb_add]
    | smul d p _ ih =>
      obtain ⟨ep, hep⟩ := ih
      refine ⟨D.R.mul d ep, ?_⟩
      show (fracRing D).mul (fracIdEmb D d) p
        = (fracRing D).mul ((fracRing D).mul a b) (fracIdEmb D (D.R.mul d ep))
      rw [hep, ← (fracRing D).mul_assoc,
        (fracRing D).mul_comm (fracIdEmb D d) ((fracRing D).mul a b),
        (fracRing D).mul_assoc, ← fracIdEmb_mul]
  · intro hx
    obtain ⟨e, he⟩ := hx
    rw [he]
    have h := fracIdMulGen.base (D := D)
      (I := fracIdPrincipal D a) (J := fracIdPrincipal D b)
      ((fracRing D).mul a (fracIdEmb D e))
      ((fracRing D).mul b (fracIdEmb D D.R.one)) ⟨e, rfl⟩ ⟨D.R.one, rfl⟩
    rw [fracIdEmb_one, cring_mul_one (fracRing D) b,
      cring_mul_right_swap (fracRing D) a (fracIdEmb D e) b] at h
    exact h

/-- **M302F-7b: (1) = D**（単項イデアル (1) は単位イデアル）。 -/
theorem fracId_principal_one_eq (D : Domain) (x : (fracRing D).carrier) :
    (fracIdPrincipal D (fracRing D).one).mem x ↔ (fracIdOne D).mem x := by
  refine ⟨?_, ?_⟩
  · intro hx
    obtain ⟨e, he⟩ := hx
    exact ⟨e, by rw [he, (fracRing D).one_mul]⟩
  · intro hx
    obtain ⟨e, he⟩ := hx
    exact ⟨e, by rw [he, (fracRing D).one_mul]⟩

/-- **M302F-7c: 単項分数イデアルの積は可換**（(a)(b)=(ab)=(ba)=(b)(a)）。 -/
theorem fracId_principal_mul_comm (D : Domain) (a b : (fracRing D).carrier)
    (x : (fracRing D).carrier) :
    (fracIdMul D (fracIdPrincipal D a) (fracIdPrincipal D b)).mem x ↔
      (fracIdMul D (fracIdPrincipal D b) (fracIdPrincipal D a)).mem x :=
  fracId_mul_comm D (fracIdPrincipal D a) (fracIdPrincipal D b) x

/-- **M302F-7d: 単項分数イデアルの積は結合的**（K の mul_assoc へ帰着、完全）。 -/
theorem fracId_principal_mul_assoc (D : Domain)
    (a b c : (fracRing D).carrier) (x : (fracRing D).carrier) :
    (fracIdMul D (fracIdMul D (fracIdPrincipal D a) (fracIdPrincipal D b))
        (fracIdPrincipal D c)).mem x ↔
      (fracIdMul D (fracIdPrincipal D a)
        (fracIdMul D (fracIdPrincipal D b) (fracIdPrincipal D c))).mem x := by
  have eL :
      (fracIdMul D (fracIdMul D (fracIdPrincipal D a) (fracIdPrincipal D b))
          (fracIdPrincipal D c)).mem x ↔
        (fracIdPrincipal D
          ((fracRing D).mul ((fracRing D).mul a b) c)).mem x := by
    apply Iff.trans
      (fracId_mul_congr_left D (fracId_principal_mul D a b)
        (fracIdPrincipal D c) x)
    exact fracId_principal_mul D ((fracRing D).mul a b) c x
  have eR :
      (fracIdMul D (fracIdPrincipal D a)
          (fracIdMul D (fracIdPrincipal D b) (fracIdPrincipal D c))).mem x ↔
        (fracIdPrincipal D
          ((fracRing D).mul a ((fracRing D).mul b c))).mem x := by
    apply Iff.trans
      (fracId_mul_congr_right D (fracId_principal_mul D b c)
        (fracIdPrincipal D a) x)
    exact fracId_principal_mul D a ((fracRing D).mul b c) x
  rw [(fracRing D).mul_assoc a b c] at eL
  exact Iff.trans eL eR.symm

/-! ## M302F-8: 可逆分数イデアルと単項の可逆性 -/

/-- **M302F-8a: 可逆分数イデアル** — ∃ J, I·J = D（単位イデアル）。 -/
def fracIdInvertible (D : Domain) (I : fracIdFractional D) : Prop :=
  ∃ J : fracIdFractional D,
    ∀ x, (fracIdMul D I J).mem x ↔ (fracIdOne D).mem x

/-- **M302F-8b: (a)·(b) = D（a·b=1 のとき）**（(a)(b)=(ab)=(1)=D、完全証明）。 -/
theorem fracId_principal_invertible (D : Domain) (a b : (fracRing D).carrier)
    (hab : (fracRing D).mul a b = (fracRing D).one)
    (x : (fracRing D).carrier) :
    (fracIdMul D (fracIdPrincipal D a) (fracIdPrincipal D b)).mem x ↔
      (fracIdOne D).mem x := by
  apply Iff.trans (fracId_principal_mul D a b x)
  rw [hab]
  exact fracId_principal_one_eq D x

/-- **M302F-8c: 単項分数イデアル (a)（a∈K*）は可逆**（逆は (a⁻¹)、完全）。 -/
theorem fracId_principal_is_invertible (D : Domain) (a : (fracRing D).carrier)
    (h : ∃ b : (fracRing D).carrier, (fracRing D).mul a b = (fracRing D).one) :
    fracIdInvertible D (fracIdPrincipal D a) := by
  obtain ⟨b, hab⟩ := h
  exact ⟨fracIdPrincipal D b, fracId_principal_invertible D a b hab⟩

/-! ## M302F-9: capstone -/

/-- **M302F-9a: 分数イデアルデータ** — 単位・積・可換性・単位元・単項イデアルと
    その積法則・単項の可逆性を束ねる（全フィールドが本モジュールの完全証明）。 -/
structure FractionalIdealData (D : Domain) where
  /-- 単位イデアル D。 -/
  one : fracIdFractional D
  /-- 積。 -/
  mul : fracIdFractional D → fracIdFractional D → fracIdFractional D
  /-- 積の可換性。 -/
  mul_comm : ∀ I J x, (mul I J).mem x ↔ (mul J I).mem x
  /-- 単位元 D·I = I。 -/
  one_mul : ∀ I x, (mul one I).mem x ↔ I.mem x
  /-- 単項イデアル (a)。 -/
  principal : (fracRing D).carrier → fracIdFractional D
  /-- (a)·(b) = (ab)。 -/
  principal_mul : ∀ a b x, (mul (principal a) (principal b)).mem x ↔
    (principal ((fracRing D).mul a b)).mem x
  /-- a·b=1 のとき (a)·(b) = D（単項の可逆性）。 -/
  principal_invertible : ∀ a b, (fracRing D).mul a b = (fracRing D).one →
    ∀ x, (mul (principal a) (principal b)).mem x ↔ one.mem x

/-- **M302F-9b: 分数イデアルデータの witness**（全て本物）。 -/
def fracIdData (D : Domain) : FractionalIdealData D where
  one := fracIdOne D
  mul := fracIdMul D
  mul_comm := fracId_mul_comm D
  one_mul := fracId_one_mul D
  principal := fracIdPrincipal D
  principal_mul := fracId_principal_mul D
  principal_invertible := fracId_principal_invertible D

/-- **M302F-9c: 見出し定理** — 任意の整域 D に分数イデアルデータが存在。 -/
theorem fracId_exists (D : Domain) : Nonempty (FractionalIdealData D) :=
  ⟨fracIdData D⟩

/-- **M302F-9d: 単項 Cartier 因子群の土台** — 単項分数イデアル (a)（a∈K*）が
    積で可換群をなすための本物の法則束（結合・可換・単位・逆）。可逆イデアル一般が
    群をなす完全証明（Dedekind）は骨組み/後続だが、単項（principal Cartier 因子）
    に限れば K の環法則から完全に成立する。 -/
structure FracIdCartierGroup (D : Domain) where
  /-- 積の可換性 (a)(b)=(b)(a)。 -/
  mul_comm : ∀ a b x, (fracIdMul D (fracIdPrincipal D a) (fracIdPrincipal D b)).mem x
    ↔ (fracIdMul D (fracIdPrincipal D b) (fracIdPrincipal D a)).mem x
  /-- 積の結合律。 -/
  mul_assoc : ∀ a b c x,
    (fracIdMul D (fracIdMul D (fracIdPrincipal D a) (fracIdPrincipal D b))
        (fracIdPrincipal D c)).mem x ↔
      (fracIdMul D (fracIdPrincipal D a)
        (fracIdMul D (fracIdPrincipal D b) (fracIdPrincipal D c))).mem x
  /-- 単位元 D·(a) = (a)。 -/
  one_mul : ∀ a x, (fracIdMul D (fracIdOne D) (fracIdPrincipal D a)).mem x
    ↔ (fracIdPrincipal D a).mem x
  /-- 逆元 a·b=1 のとき (a)·(b)=D。 -/
  inv : ∀ a b, (fracRing D).mul a b = (fracRing D).one →
    ∀ x, (fracIdMul D (fracIdPrincipal D a) (fracIdPrincipal D b)).mem x
      ↔ (fracIdOne D).mem x

/-- **M302F-9e: 単項 Cartier 因子群の witness**（全て本物・イデアル類群の土台）。 -/
def fracId_cartier_group (D : Domain) : FracIdCartierGroup D where
  mul_comm := fracId_principal_mul_comm D
  mul_assoc := fracId_principal_mul_assoc D
  one_mul := fun a => fracId_one_mul D (fracIdPrincipal D a)
  inv := fracId_principal_invertible D

/-- **M302F-9f: 単項分数イデアルは積で可換モノイド**（結合・可換・単位、
    全て K の環法則へ帰着、完全）。 -/
theorem fracId_mul_monoid (D : Domain) :
    (∀ a b x, (fracIdMul D (fracIdPrincipal D a) (fracIdPrincipal D b)).mem x
        ↔ (fracIdMul D (fracIdPrincipal D b) (fracIdPrincipal D a)).mem x) ∧
      (∀ a b c x,
        (fracIdMul D (fracIdMul D (fracIdPrincipal D a) (fracIdPrincipal D b))
            (fracIdPrincipal D c)).mem x ↔
          (fracIdMul D (fracIdPrincipal D a)
            (fracIdMul D (fracIdPrincipal D b) (fracIdPrincipal D c))).mem x) ∧
      (∀ a x, (fracIdMul D (fracIdOne D) (fracIdPrincipal D a)).mem x
        ↔ (fracIdPrincipal D a).mem x) :=
  ⟨fracId_principal_mul_comm D, fracId_principal_mul_assoc D,
    fun a => fracId_one_mul D (fracIdPrincipal D a)⟩

/-- **M302F-9g: 体上の分数イデアルの単項性（本物の部分）** — 零イデアルと単位
    イデアルは単項（(0) と (1)=D）。全分数イデアルが (a) or 0 という完全分類は
    D↔体の橋渡しを要すので骨組み/後続（正直申告）。 -/
theorem fracId_field_principal (D : Domain) :
    (∀ x, (fracIdZero D).mem x ↔ (fracIdPrincipal D (fracRing D).zero).mem x) ∧
      (∀ x, (fracIdOne D).mem x ↔ (fracIdPrincipal D (fracRing D).one).mem x) := by
  refine ⟨?_, ?_⟩
  · intro x
    refine ⟨?_, ?_⟩
    · intro hx
      exact ⟨D.R.zero, by rw [hx, fracIdEmb_zero, CRing.mul_zero]⟩
    · intro hx
      obtain ⟨e, he⟩ := hx
      show x = (fracRing D).zero
      rw [he, CRing.mul_comm, CRing.mul_zero]
  · intro x
    exact (fracId_principal_one_eq D x).symm

end IUT
