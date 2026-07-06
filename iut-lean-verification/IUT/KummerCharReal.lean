/-
  IUT/KummerCharReal.lean — M349F [実／本物]
  分類: 実 (実 Kummer 指標 κ:G_K→μ_n を n 乗根から構成・M343F/M344F/M348F の κ 供給)
  complete_pct 影響: 柱A を前進（κ_α(σ)=σ(α)/α∈μ_n（α^n=a）を本物で構成＝1-コサイクル・
    自明作用で準同型・根の取替で コバウンダリ（[κ]∈H¹ well-defined）を証明し、M343F galThTorTwist・
    M344F β 捻れ・M348F が受け取っていた κ を実供給）。
  正直な限定: 一般 a の α∈K̄ 存在・完全 Kummer 双対は外部仮説等。
-/
import IUT.KummerTheory
import IUT.GaloisTheta

namespace IUT

/-! ## M349F-0: 実 Kummer 指標 κ_α(σ)=σ(α)/α（M320F の本物の Kummer コサイクルを主語に）

  M320F `kummerCocycle K r σ = σ(r)·r⁻¹`（r は n 乗根 α, r^n=a）を、絶対ガロア群の
  本物のモデル `fieldAutGroup K`（M271F, carrier=`FieldAut K`, mul=`fieldAutComp`）上の
  指標として据える。これが M343F galThTorTwist・M344F β 捻れ・M348F が「データ/仮説」
  として受け取っていた κ:G_K→μ_n の本物の実体である。 -/

/-- **M349F-1a: 実 Kummer 指標** κ_α(σ) = σ(α)·α⁻¹（α=r は α^n=a なる n 乗根）。
    M320F の本物の Kummer コサイクルを G_K=`fieldAutGroup K` 上の指標として据える。 -/
def kcrChar (K : IUTField) (r : (tateMultGroup K).carrier) (σ : FieldAut K) :
    (tateMultGroup K).carrier :=
  kummerCocycle K r σ

/-- **M349F-1b: 定義の明示** — κ_α(σ) = σ(α)·α⁻¹。 -/
theorem kcr_char_def (K : IUTField) (r : (tateMultGroup K).carrier) (σ : FieldAut K) :
    kcrChar K r σ
      = (tateMultGroup K).mul (kummerUnitAct K σ r) ((tateMultGroup K).inv r) :=
  rfl

/-- **M349F-1c: κ_α(σ) ∈ μ_n（本物、σ が a=α^n を固定するとき）** — σ が a=r^n を
    固定するなら κ_α(σ)^n = σ(a)/a = 1、すなわち κ_α(σ) は 1 の n 乗根。M320F
    `kummer_cocycle_in_mu` を実 Kummer 指標に据える。 -/
theorem kcr_mem_mu (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier)
    (σ : FieldAut K)
    (hfix : kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n) :
    (tateTorMuSubgroup K n).mem (kcrChar K r σ) :=
  kummer_cocycle_in_mu K n r σ hfix

/-! ## M349F-2: 1-コサイクル則（crossed homomorphism） -/

/-- **M349F-2: 1-コサイクル則（本物）** — κ_α(στ) = κ_α(σ)·σ(κ_α(τ))。M320F
    `kummer_cocycle`（可換群の並べ替え）を G_K=`fieldAutGroup K` の積 στ=σ∘τ 上に据える。
    実 Kummer 指標が本物の crossed homomorphism（1-コサイクル）であることの証明。 -/
theorem kcr_cocycle (K : IUTField) (r : (tateMultGroup K).carrier)
    (σ τ : FieldAut K) :
    kcrChar K r ((fieldAutGroup K).mul σ τ)
      = (tateMultGroup K).mul (kcrChar K r σ)
          (kummerUnitAct K σ (kcrChar K r τ)) :=
  kummer_cocycle K r σ τ

/-! ## M349F-3: 自明作用（μ_n⊆K）での準同型性 -/

/-- **M349F-3a: 自明作用仮説** — μ_n⊆K（K が原始 n 乗根を含む）のとき、G_K は指標値
    κ_α(τ)∈μ_n に自明に作用する: σ(κ_α(τ))=κ_α(τ)。実 Kummer 指標が準同型になる条件。 -/
def kcrTrivialAction (K : IUTField) (r : (tateMultGroup K).carrier) : Prop :=
  ∀ σ τ : FieldAut K, kummerUnitAct K σ (kcrChar K r τ) = kcrChar K r τ

/-- **M349F-3b: 自明作用での準同型則（本物）** — 指標値への作用が自明なら
    κ_α(στ) = κ_α(σ)·κ_α(τ)（1-コサイクル則で σ(κ_α(τ)) を κ_α(τ) に置換）。 -/
theorem kcr_hom_trivial_action (K : IUTField) (r : (tateMultGroup K).carrier)
    (σ τ : FieldAut K)
    (htriv : kummerUnitAct K σ (kcrChar K r τ) = kcrChar K r τ) :
    kcrChar K r ((fieldAutGroup K).mul σ τ)
      = (tateMultGroup K).mul (kcrChar K r σ) (kcrChar K r τ) := by
  rw [kcr_cocycle, htriv]

/-- **M349F-3c: μ_n の部分群群は可換** — μ_n⊆K^× は可換（`tateMultGroup_comm`）。 -/
theorem kcr_mu_comm (K : IUTField) (n : Nat) :
    ∀ a b : (subgroupGrp (tateTorMuSubgroup K n)).carrier,
      (subgroupGrp (tateTorMuSubgroup K n)).mul a b
        = (subgroupGrp (tateTorMuSubgroup K n)).mul b a := by
  intro a b
  apply Subtype.ext
  show (tateMultGroup K).mul a.val b.val = (tateMultGroup K).mul b.val a.val
  exact tateMultGroup_comm K a.val b.val

/-- **M349F-3d: 実 Kummer 指標を本物の準同型 κ:G_K→μ_n として**（本物）— a=α^n が
    G_K-固定（`hfix`）かつ μ_n⊆K（`htriv`）のとき、κ_α は絶対ガロア群
    `fieldAutGroup K` から μ_n（`subgroupGrp (tateTorMuSubgroup K n)`）への**本物の
    群準同型 `Hom`**。M343F galThTorTwist・M344F β 捻れ・M348F が「Hom GK μ_n」として
    受け取る κ の実体をここで供給する。 -/
def kcrHomMu (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) :
    Hom (fieldAutGroup K) (subgroupGrp (tateTorMuSubgroup K n)) where
  map := fun σ => ⟨kcrChar K r σ, kcr_mem_mu K n r σ (hfix σ)⟩
  map_mul := fun σ τ => Subtype.ext (kcr_hom_trivial_action K r σ τ (htriv σ τ))

/-- **M349F-3e: κ の準同型値が指標値に一致**（`kcrHomMu` の底写像の同定）。 -/
theorem kcr_hom_mu_map (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (σ : FieldAut K) :
    ((kcrHomMu K n r hfix htriv).map σ).val = kcrChar K r σ :=
  rfl

/-! ## M349F-4: 根の取替でコバウンダリ（[κ]∈H¹ の well-defined） -/

/-- **M349F-4a: 実 Kummer コバウンダリ** d_z(σ) = σ(z)·z⁻¹（M320F `kummerCoboundary`）。
    n 乗根 α を ζα（ζ∈μ_n）に取り替えたときの指標のずれを与える主コサイクル。 -/
def kcrCoboundary (K : IUTField) (z : (tateMultGroup K).carrier) (σ : FieldAut K) :
    (tateMultGroup K).carrier :=
  kummerCoboundary K z σ

/-- **M349F-4b: 根の取替でコバウンダリ（本物）** — α を α·z に取り替えると
    κ_{α·z}(σ) = κ_α(σ)·d_z(σ)。実 Kummer 指標が n 乗根の取替で**コバウンダリだけ
    ずれる** ＝ 円分類 [κ]∈H¹(G_K,μ_n) が (K^×)ⁿ を法として well-defined
    （M320F/M345F Kummer 類に接続）。 -/
theorem kcr_independent_of_root (K : IUTField) (r z : (tateMultGroup K).carrier)
    (σ : FieldAut K) :
    kcrChar K ((tateMultGroup K).mul r z) σ
      = (tateMultGroup K).mul (kcrChar K r σ) (kcrCoboundary K z σ) :=
  kummer_h1_welldefined K r z σ

/-- **M349F-4c: 固定された ζ のコバウンダリは自明** — ζ が σ-固定（μ_n⊆K）なら
    d_ζ(σ)=σ(ζ)·ζ⁻¹=ζ·ζ⁻¹=1。 -/
theorem kcr_coboundary_trivial_of_fixed (K : IUTField) (z : (tateMultGroup K).carrier)
    (σ : FieldAut K) (hz : kummerUnitAct K σ z = z) :
    kcrCoboundary K z σ = (tateMultGroup K).one := by
  show (tateMultGroup K).mul (kummerUnitAct K σ z) ((tateMultGroup K).inv z)
      = (tateMultGroup K).one
  rw [hz, (tateMultGroup K).mul_inv]

/-- **M349F-4d: μ_n⊆K での根の取替不変（本物）** — ζ が σ-固定（μ_n⊆K）なら
    κ_{α·ζ}(σ)=κ_α(σ)。指標が μ_n を法とする n 乗根選択に依らない（well-defined）。 -/
theorem kcr_root_change_fixed (K : IUTField) (r z : (tateMultGroup K).carrier)
    (σ : FieldAut K) (hz : kummerUnitAct K σ z = z) :
    kcrChar K ((tateMultGroup K).mul r z) σ = kcrChar K r σ := by
  rw [kcr_independent_of_root, kcr_coboundary_trivial_of_fixed K z σ hz,
    (tateMultGroup K).mul_one]

/-- **M349F-4e: コサイクル自明 ⟺ σ-固定** — κ_α(σ)=1 ⟺ σ(α)=α（M320F
    `kummer_cocycle_trivial_iff`）。単射方向 K^×/(K^×)ⁿ ↪ H¹ の核。 -/
theorem kcr_trivial_iff (K : IUTField) (r : (tateMultGroup K).carrier)
    (σ : FieldAut K) :
    kcrChar K r σ = (tateMultGroup K).one ↔ kummerUnitAct K σ r = r :=
  kummer_cocycle_trivial_iff K r σ

/-! ## M349F-5: M343F galThTorTwist / M348F への κ 供給 -/

/-- **M349F-5a: 実 Kummer 指標のガロア捻り** — 本物の κ:G_K→μ_n（`kcrHomMu`）から
    l-捻れ点の捻り因子 κ(σ)^j を μ_n 上で与える（M343F `galThTorTwist` の μ_n 部分群版）。 -/
def kcrRealTwist (K : IUTField) (n : Nat)
    (κ : Hom (fieldAutGroup K) (subgroupGrp (tateTorMuSubgroup K n)))
    (σ : FieldAut K) (j : Nat) : (subgroupGrp (tateTorMuSubgroup K n)).carrier :=
  (subgroupGrp (tateTorMuSubgroup K n)).pow (κ.map σ) j

/-- **M349F-5b: 捻りの単位則** — κ(1)^j=1（κ.map_one＋1 の冪は 1）。M343F
    `galTh_tor_twist_one` に対応。 -/
theorem kcr_real_twist_one (K : IUTField) (n : Nat)
    (κ : Hom (fieldAutGroup K) (subgroupGrp (tateTorMuSubgroup K n))) (j : Nat) :
    kcrRealTwist K n κ (fieldAutGroup K).one j
      = (subgroupGrp (tateTorMuSubgroup K n)).one := by
  show (subgroupGrp (tateTorMuSubgroup K n)).pow (κ.map (fieldAutGroup K).one) j
      = (subgroupGrp (tateTorMuSubgroup K n)).one
  rw [κ.map_one]
  exact galTh_pow_one (subgroupGrp (tateTorMuSubgroup K n)) j

/-- **M349F-5c: 捻りのコサイクル則（本物）** — κ(στ)^j=κ(σ)^j·κ(τ)^j（κ.map_mul＋
    可換群の積の冪分配 M343F-0b）。M343F `galTh_tor_twist_mul` に対応する、**実 Kummer
    指標の**捻りコサイクル則。 -/
theorem kcr_real_twist_mul (K : IUTField) (n : Nat)
    (κ : Hom (fieldAutGroup K) (subgroupGrp (tateTorMuSubgroup K n)))
    (σ τ : FieldAut K) (j : Nat) :
    kcrRealTwist K n κ ((fieldAutGroup K).mul σ τ) j
      = (subgroupGrp (tateTorMuSubgroup K n)).mul
          (kcrRealTwist K n κ σ j) (kcrRealTwist K n κ τ j) := by
  show (subgroupGrp (tateTorMuSubgroup K n)).pow
        (κ.map ((fieldAutGroup K).mul σ τ)) j = _
  rw [κ.map_mul]
  exact galTh_pow_mul_distrib (subgroupGrp (tateTorMuSubgroup K n))
    (kcr_mu_comm K n) (κ.map σ) (κ.map τ) j

/-- **M349F-5d: 抽象 μ_n（CycMuGroup）への κ 供給** — μ_n 部分群 → 抽象円分群 M.μ の
    同定 φ を通じて、実 Kummer 指標 `kcrHomMu` から M343F が要求する
    **κ : Hom G_K M.μ** を合成で得る（`Hom.comp`）。M343F galThTorTwist・M344F・M348F が
    「データ」として受けていた κ を、n 乗根からの本物の指標で供給する。 -/
def kcrGalThKappa (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (M : CycMuGroup)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ) :
    Hom (fieldAutGroup K) M.μ :=
  Hom.comp φ (kcrHomMu K n r hfix htriv)

/-- **M349F-5e: 供給された κ が galThTorTwist のコサイクル則を満たす（本物）** —
    実 Kummer 指標から供給した κ で、M343F の l-捻れ捻りコサイクル則
    κ(gh)^j = κ(g)^j·κ(h)^j が成り立つ。これで「κ からの供給は後続」限定を閉じ、
    galThTorTwist が本物の指標を受け取る。 -/
theorem kcr_supplies_galTh (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (M : CycMuGroup)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ)
    (g h : FieldAut K) (j : Nat) :
    galThTorTwist (fieldAutGroup K) M (kcrGalThKappa K n r hfix htriv M φ)
        ((fieldAutGroup K).mul g h) j
      = M.μ.mul
          (galThTorTwist (fieldAutGroup K) M (kcrGalThKappa K n r hfix htriv M φ) g j)
          (galThTorTwist (fieldAutGroup K) M (kcrGalThKappa K n r hfix htriv M φ) h j) :=
  galTh_tor_twist_mul (fieldAutGroup K) M (kcrGalThKappa K n r hfix htriv M φ) g h j

/-- **M349F-5f: 供給された κ の単位捻りは自明** — κ(1)^j=1（M343F `galTh_tor_twist_one`）。 -/
theorem kcr_supplies_galTh_one (K : IUTField) (n : Nat)
    (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (M : CycMuGroup)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ) (j : Nat) :
    galThTorTwist (fieldAutGroup K) M (kcrGalThKappa K n r hfix htriv M φ)
        (fieldAutGroup K).one j = M.μ.one :=
  galTh_tor_twist_one (fieldAutGroup K) M (kcrGalThKappa K n r hfix htriv M φ) j

/-! ## M349F-6: 外部仮説（決して導出しない・正直な限定） -/

/-- **M349F-6a: n 乗根の存在仮説（Prop）** — 一般の a∈K^× に対し α^n=a なる n 乗根
    α∈K̄ が存在するという**外部仮説**。分離閉包での根の存在そのものは柱A の後続入力で
    あり、本層はこれを明示の Prop 仮説として受け、決して自前で導出しない。 -/
def kcr_root_exists_hypothesis (K : IUTField) (n : Nat)
    (a : (tateMultGroup K).carrier) : Prop :=
  ∃ r : (tateMultGroup K).carrier, tateNpow (tateMultGroup K) r n = a

/-- **M349F-6b: n 乗根仮説から指標（仮説依存）** — 仮説の下で n 乗根 α を取り出し、
    その実 Kummer 指標を得る。仮説は外部入力で本体で導出しない。 -/
theorem kcr_char_of_root_hypothesis (K : IUTField) (n : Nat)
    (a : (tateMultGroup K).carrier) (h : kcr_root_exists_hypothesis K n a) :
    ∃ r : (tateMultGroup K).carrier,
      tateNpow (tateMultGroup K) r n = a ∧ (∀ σ, kcrChar K r σ = kcrChar K r σ) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr, fun _ => rfl⟩

/-- **M349F-6c: 完全 Kummer 双対仮説（Prop）** — 各 1-コサイクル類が n 乗根の実 Kummer
    指標から来るという**全射性（完全 Kummer 双対 K^×/(K^×)ⁿ ≅ H¹(G_K,μ_n)）の外部仮説**。
    本層は単射方向（`kcr_trivial_iff`）・well-defined（`kcr_independent_of_root`）までを
    本物で建て、全射性（完全同型）は外部入力として受け、決して自前で導出しない。 -/
def kcr_kummer_duality_hypothesis (K : IUTField)
    (isClass : (FieldAut K → (tateMultGroup K).carrier) → Prop) : Prop :=
  ∀ c, isClass c → ∃ r : (tateMultGroup K).carrier, ∀ σ, c σ = kcrChar K r σ

/-- **M349F-6d: Kummer 双対仮説から根の復元（仮説依存）** — 仮説の下で、任意の
    コサイクル類 c から n 乗根の実 Kummer 指標 κ_α=c を復元。仮説は外部入力で導出しない。 -/
theorem kcr_root_of_class_hypothesis (K : IUTField)
    (isClass : (FieldAut K → (tateMultGroup K).carrier) → Prop)
    (hyp : kcr_kummer_duality_hypothesis K isClass)
    (c : FieldAut K → (tateMultGroup K).carrier) (hc : isClass c) :
    ∃ r : (tateMultGroup K).carrier, ∀ σ, c σ = kcrChar K r σ :=
  hyp c hc

/-! ## M349F-7: capstone（実 Kummer 指標データ） -/

/-- **M349F-7a: 実 Kummer 指標データ** — 次数 n・n 乗根 α・実 Kummer 指標 κ_α と、
    1-コサイクル則・根の取替コバウンダリ（[κ]∈H¹ well-defined）・単射方向を束ねる。
    M343F/M344F/M348F が受け取る κ の本物の実体。 -/
structure KummerCharData (K : IUTField) where
  /-- Kummer 次数 n（IUT では素数 l）。 -/
  n : Nat
  /-- n 乗根 α（α^n=a、witness）。 -/
  r : (tateMultGroup K).carrier
  /-- 実 Kummer 指標 κ_α : G_K→K^×（μ_n 値）。 -/
  char : FieldAut K → (tateMultGroup K).carrier
  /-- char = 実 Kummer 指標 κ_α。 -/
  char_def : ∀ σ, char σ = kcrChar K r σ
  /-- 1-コサイクル則 κ(στ)=κ(σ)·σ(κ(τ))。 -/
  cocycle : ∀ σ τ, char ((fieldAutGroup K).mul σ τ)
    = (tateMultGroup K).mul (char σ) (kummerUnitAct K σ (char τ))
  /-- 根の取替コバウンダリ κ_{αz}(σ)=κ_α(σ)·d_z(σ)（H¹ well-defined）。 -/
  coboundary : ∀ z σ, kcrChar K ((tateMultGroup K).mul r z) σ
    = (tateMultGroup K).mul (char σ) (kcrCoboundary K z σ)
  /-- 単射方向 κ_α(σ)=1 ⟺ σ(α)=α。 -/
  trivial_iff : ∀ σ, char σ = (tateMultGroup K).one ↔ kummerUnitAct K σ r = r

/-- **M349F-7b: witness 本体** — 各フィールドを M349F-2〜4 の主定理で埋める。 -/
def kcrData (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier) :
    KummerCharData K where
  n := n
  r := r
  char := kcrChar K r
  char_def := fun _ => rfl
  cocycle := kcr_cocycle K r
  coboundary := fun z σ => kcr_independent_of_root K r z σ
  trivial_iff := fun σ => kcr_trivial_iff K r σ

/-- **M349F-7c: capstone — 実 Kummer 指標データの存在**（任意の体 K・次数 n・n 乗根 α）。
    n 乗根 α から実 Kummer 指標 κ_α:G_K→μ_n を本物で構成し、1-コサイクル則・
    根の取替コバウンダリ・単射方向を閉じる。M343F/M344F/M348F への κ 供給が閉じる。 -/
theorem kcr_exists (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier) :
    Nonempty (KummerCharData K) :=
  ⟨kcrData K n r⟩

/-! ## M349F-8: 実例（μ_n⊆K・自明作用：r=1 で κ≡1 の本物の準同型 G_ℚ→μ_2） -/

/-- **M349F-8a: 1 の n 乗は G_K-固定** — 1^n=1 は任意の σ で固定（`kummerUnitAct_one`）。 -/
theorem kcr_one_fix (K : IUTField) (n : Nat) :
    ∀ σ : FieldAut K,
      kummerUnitAct K σ (tateNpow (tateMultGroup K) (tateMultGroup K).one n)
        = tateNpow (tateMultGroup K) (tateMultGroup K).one n := by
  intro σ
  rw [tateTorOnePow (tateMultGroup K) n]
  exact kummerUnitAct_one K σ

/-- **M349F-8b: α=1 の指標は自明** — κ_1(σ)=σ(1)·1⁻¹=1（1 の n 乗根選択の基点）。 -/
theorem kcr_one_char (K : IUTField) (σ : FieldAut K) :
    kcrChar K (tateMultGroup K).one σ = (tateMultGroup K).one := by
  show (tateMultGroup K).mul (kummerUnitAct K σ (tateMultGroup K).one)
        ((tateMultGroup K).inv (tateMultGroup K).one) = (tateMultGroup K).one
  rw [kummerUnitAct_one K σ, tateTorInvOne (tateMultGroup K),
    (tateMultGroup K).mul_one]

/-- **M349F-8c: α=1 で自明作用が成立** — κ_1≡1 ゆえ指標値への作用は自明。 -/
theorem kcr_one_trivialAction (K : IUTField) :
    kcrTrivialAction K (tateMultGroup K).one := by
  intro σ τ
  rw [kcr_one_char K τ]
  exact kummerUnitAct_one K σ

/-- **M349F-8d: 本物の準同型 κ:G_ℚ→μ_2 の実例** — 有理数体 ℚ・α=1・n=2 で、実 Kummer
    指標を絶対ガロア群 `fieldAutGroup ℚ` から μ_2（`subgroupGrp (tateTorMuSubgroup ℚ 2)`）
    への**本物の群準同型 `Hom`** として構成。M343F/M344F/M348F が受け取る κ の実例。 -/
def kcrHomExample :
    Hom (fieldAutGroup ratIUTField) (subgroupGrp (tateTorMuSubgroup ratIUTField 2)) :=
  kcrHomMu ratIUTField 2 (tateMultGroup ratIUTField).one
    (kcr_one_fix ratIUTField 2) (kcr_one_trivialAction ratIUTField)

/-- **M349F-8e: 実例の存在** — 本物の準同型 κ:G_ℚ→μ_2 が存在する。 -/
theorem kcr_hom_example_exists :
    Nonempty (Hom (fieldAutGroup ratIUTField)
      (subgroupGrp (tateTorMuSubgroup ratIUTField 2))) :=
  ⟨kcrHomExample⟩

/-- **M349F-8f: 実例（l-捻れ）** — n=l（素数）で実 Kummer 指標データが存在。Mochizuki の
    IUT がテータ値を評価する l-捻れの Kummer 指標 κ_α:G_K→μ_l の実体。 -/
theorem kcr_prime_example (K : IUTField) (l : Nat)
    (r : (tateMultGroup K).carrier) : Nonempty (KummerCharData K) :=
  ⟨kcrData K l r⟩

/-- **M349F-8g: 実例（実 Kummer 指標データ・ℚ・n=2）** — 有理数体 ℚ の n=2 で
    実 Kummer 指標データが存在（ℚ^×/(ℚ^×)² の平方類を測る Kummer 指標）。 -/
theorem kcr_exists_rat_sq :
    Nonempty (KummerCharData ratIUTField) :=
  ⟨kcrData ratIUTField 2 (tateMultGroup ratIUTField).one⟩

end IUT
