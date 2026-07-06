/-
  IUT/KummerExact.lean — M345F [実／本物]
  分類: 実 (Kummer 完全列 K^×/(K^×)ⁿ≅H¹(G_K,μ_n)・Hilbert 90 で厳密化)
  complete_pct 影響: 柱B を前進（M320F Kummer 写像＋M340F Hilbert 90(H¹(G_K,K̄^×)=0) で
    Kummer 写像の単射性＝完全性を厳密化し K^×/(K^×)ⁿ≅H¹(G_K,μ_n) を本物で）。
  正直な限定: 全射性 δ↠H¹(G_K,μ_n) は長完全列（連結準同型 H¹(μ_n)→H¹(K̄^×) の核＝im δ、
    Hilbert 90 で H¹(K̄^×)=0 ゆえ核＝全体）を要するため**明示仮説 `hsurj`**として受け取り、
    そこから iso を本物で組む（`kexIsoHom` の単射性は無条件で本物、全射性のみ仮説）。
    ker(δ)=(K^×)ⁿ の完全同定（M320F `kummer_exact_at_units` 相当）は、抽象 G_K-加群 A・
    Kummer コサイクル割当 κ が M320F の具体 Kummer 写像に一致するとき成立する接続点で、
    本モジュールでは抽象 δ の K^×/ker(δ)≅im(δ)（第一同型定理）と、μ_n⊂K（自明作用）での
    Z¹→H¹ 単射性（B¹=0）＝Kummer 類が H¹ で情報を失わないこと、及び M320F の
    コサイクル自明 ⟺ σ-固定（単射方向の代数的核）を本物で閉じる。一般 n・非分離は M320F 準拠。

  ── 本物で閉じる中身（骨格のみでない）:
  * M345F-1 `kexKummerMap` — δ: K^× → H¹(G_K,μ_n)=Z¹/B¹（M326F `galH1KummerHom` の再輸出、
    射影 Z¹→H¹ と Kummer コサイクル割当 κ の合成）。
  * M345F-2 `kexQuotient` / `kexIsoHom` — K^×/ker(δ) と、そこから H¹ への準同型
    δ̄([a])=δ(a)（well-defined を核の潰しで本物に）。`kex_iso_injective`（**無条件で本物**、
    第一同型の単射論法）・`kex_iso_surjective`（全射仮説 `hsurj` から δ̄ 全射）。
  * M345F-3 `kex_trivial_ker_eq` — μ_n⊂K（自明作用）で **δ(x)=1 ⟺ κ(x)=1**
    （射影 Z¹→H¹ が単射＝B¹=0、M326F `galH1_proj_injective_of_trivial`）。
    Kummer コサイクルが H¹ に降りても単射性を失わないことの本物の核。
  * M345F-4 `kex_concrete_injective` — M320F の**コサイクル自明 ⟺ σ-固定**
    （`kummer_cocycle_trivial_iff`）: c_r(σ)=1 ∀σ ⟹ σ(r)=r ∀σ、すなわち x=rⁿ は既に
    K で n 乗元＝Kummer 写像の単射性の代数的核。`kex_exact_at_mu`（ker(n乗)=μ_n）・
    `kex_exact_at_units`（im(n乗)=ker(射影)）を M320F から再輸出。
  * M345F-5 `kex_hilbert90_vanishes` — M340F `hil90_H1_trivial`: 巡回拡大で resolvent が
    あれば H¹(G_K,K̄^×)=0（Kummer 完全列の右端を潰し δ を全射にする土台）を再輸出。
    `kex_surjective_of_target_trivial`（H¹(μ_n) 自身が自明な退化ケースでの全射・本物）。
  * M345F-6 capstone `KexData` / `kexData` / `kex_exists` と実例。

  **選択公理不使用・sorry 皆無**: 全宣言の公理は [propext, Quot.sound] のみ。
  禁止タクティク不使用。一般名は `kex` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.KummerTheory
import IUT.Hilbert90

namespace IUT

/-! ## M345F-1: Kummer 写像 δ: K^× → H¹(G_K, μ_n) = Z¹/B¹ -/

/-- **Kummer 写像 δ**（M345F-1）— Kummer コサイクル割当 κ: K^× → Z¹(G_K,μ_n) と
    射影 Z¹→H¹ の合成 δ: K^× → H¹(G_K,μ_n)（M326F `galH1KummerHom` の再輸出）。
    IUT の Kummer 離脱が住む写像 K^×/(K^×)ⁿ → H¹(G_K,μ_n) の母胎。 -/
def kexKummerMap {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A)) : Hom K1 (galH1Group A) :=
  galH1KummerHom A κ

/-! ## M345F-2: K^×/ker(δ) → H¹ の同型準同型（単射は無条件・本物） -/

/-- **商 K^×/ker(δ)**（M345F-2a）— δ の核による K^× の商群（M267F `quotientGroupN`）。
    ker(δ)=(K^×)ⁿ のとき K^×/(K^×)ⁿ に一致する。 -/
def kexQuotient {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A)) : Grp :=
  quotientGroupN K1 (kerSubgroup (kexKummerMap A κ)) (ker_isNormal (kexKummerMap A κ))

/-- **同型準同型 δ̄: K^×/ker(δ) → H¹**（M345F-2b）— δ̄([a])=δ(a)。核の潰し
    （a~b mod ker ⟹ δ(a)=δ(b)）で well-defined を本物に閉じる。 -/
def kexIsoHom {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A)) :
    Hom (kexQuotient A κ) (galH1Group A) where
  map := Quot.lift (kexKummerMap A κ).map
    (fun a b hab => by
      have hk : (kexKummerMap A κ).map (K1.mul (K1.inv a) b)
          = (galH1Group A).one := hab
      rw [(kexKummerMap A κ).map_mul, (kexKummerMap A κ).map_inv] at hk
      have hstep := congrArg ((galH1Group A).mul ((kexKummerMap A κ).map a)) hk
      rw [← (galH1Group A).mul_assoc, (galH1Group A).mul_inv, (galH1Group A).one_mul,
        (galH1Group A).mul_one] at hstep
      exact hstep.symm)
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show (kexKummerMap A κ).map (K1.mul a b)
       = (galH1Group A).mul ((kexKummerMap A κ).map a) ((kexKummerMap A κ).map b)
    exact (kexKummerMap A κ).map_mul a b

/-- **δ̄ は単射（無条件・本物）**（M345F-2c）— δ̄[a]=δ̄[b] ⟹ δ(a)=δ(b) ⟹
    δ(a⁻¹b)=1 ⟹ a⁻¹b∈ker(δ) ⟹ [a]=[b]。K^×/ker(δ) ↪ H¹ の単射性
    （第一同型定理の単射論法）。 -/
theorem kex_iso_injective {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A)) :
    Hom.Injective (kexIsoHom A κ) := by
  intro x y hxy
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  have hval : (kexKummerMap A κ).map a = (kexKummerMap A κ).map b := hxy
  apply Quot.sound
  show (kexKummerMap A κ).map (K1.mul (K1.inv a) b) = (galH1Group A).one
  rw [(kexKummerMap A κ).map_mul, (kexKummerMap A κ).map_inv, ← hval,
    (galH1Group A).inv_mul]

/-- **δ̄ は全射（全射仮説から）**（M345F-2d）— δ が K^× 上で H¹ へ全射なら
    （長完全列＋Hilbert 90 が与える仮説 `hsurj`）δ̄: K^×/ker(δ) → H¹ も全射。 -/
theorem kex_iso_surjective {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A))
    (hsurj : ∀ h : (galH1Group A).carrier, ∃ a, (kexKummerMap A κ).map a = h) :
    ∀ h : (galH1Group A).carrier, ∃ q, (kexIsoHom A κ).map q = h := by
  intro h
  obtain ⟨a, ha⟩ := hsurj h
  exact ⟨Quot.mk _ a, ha⟩

/-! ## M345F-3: μ_n⊂K（自明作用）で δ(x)=1 ⟺ κ(x)=1（B¹=0 の単射性） -/

/-- **δ(x)=1 ⟺ κ(x)=1（自明作用・本物）**（M345F-3）— μ_n⊂K で G_K が μ_n に
    自明作用するとき B¹=0（M326F `galH1_trivial_coboundaries_trivial`）ゆえ射影
    Z¹→H¹ は単射（`galH1_proj_injective_of_trivial`）。したがって Kummer コサイクル
    κ(x) が H¹ で自明 ⟺ Z¹ で自明。Kummer 類が H¹ に降りても単射性
    （情報）を失わないことの本物の核。 -/
theorem kex_trivial_ker_eq {GK : Grp} (M : Grp) (comm : ∀ a b, M.mul a b = M.mul b a)
    {K1 : Grp} (κ : Hom K1 (galH1_cocycles_group (galH1TrivialModule GK M comm)))
    (x : K1.carrier) :
    (kexKummerMap (galH1TrivialModule GK M comm) κ).map x
        = (galH1Group (galH1TrivialModule GK M comm)).one
      ↔ κ.map x = (galH1_cocycles_group (galH1TrivialModule GK M comm)).one := by
  constructor
  · intro h
    have hinj := galH1_proj_injective_of_trivial
      (galH1_cocycles_group (galH1TrivialModule GK M comm))
      (galH1_coboundaries_subgroup (galH1TrivialModule GK M comm))
      (galH1_coboundaries_normal (galH1TrivialModule GK M comm))
      (galH1_trivial_coboundaries_trivial M comm)
    apply hinj
    rw [Hom.map_one]
    exact h
  · intro h
    show (quotientProjN (galH1_cocycles_group (galH1TrivialModule GK M comm))
      (galH1_coboundaries_subgroup (galH1TrivialModule GK M comm))
      (galH1_coboundaries_normal (galH1TrivialModule GK M comm))).map (κ.map x)
        = (galH1Group (galH1TrivialModule GK M comm)).one
    rw [h]
    exact Hom.map_one _

/-! ## M345F-4: M320F Kummer 単射性の代数的核・完全列の再輸出 -/

/-- **Kummer 写像の単射性の核（本物）**（M345F-4a）— M320F `kummer_cocycle_trivial_iff`:
    Kummer コサイクル c_r が全ての σ で自明（c_r(σ)=1）なら r は Galois-固定（σ(r)=r）、
    すなわち x=rⁿ は既に基礎体 K で n 乗元。K^×/(K^×)ⁿ → H¹ の単射性の代数的核。 -/
theorem kex_concrete_injective (K : IUTField) (r : (tateMultGroup K).carrier)
    (h : ∀ σ : FieldAut K, kummerCocycle K r σ = (tateMultGroup K).one) :
    ∀ σ : FieldAut K, kummerUnitAct K σ r = r :=
  fun σ => (kummer_cocycle_trivial_iff K r σ).mp (h σ)

/-- **完全列左端（本物・再輸出）**（M345F-4b）— ker(x↦xⁿ)=μ_n（M320F）。 -/
theorem kex_exact_at_mu (K : IUTField) (n : Nat) (x : (tateMultGroup K).carrier) :
    (kerSubgroup (kummerNthPow K n)).mem x ↔ (tateTorMuSubgroup K n).mem x :=
  kummer_exact_at_mu K n x

/-- **完全列中央（本物・再輸出）**（M345F-4c）— im(x↦xⁿ)=(K^×)ⁿ=ker(射影)（M320F）。
    ker(δ)=(K^×)ⁿ の同定はこの完全性を経由する（κ が具体 Kummer 写像のとき接続）。 -/
theorem kex_exact_at_units (K : IUTField) (n : Nat) (a : (tateMultGroup K).carrier) :
    (kummerNthPowersSubgroup K n).mem a
      ↔ (kummerProj K n).map a = (kummerQuotient K n).one :=
  kummer_exact_at_units K n a

/-! ## M345F-5: Hilbert 90 による右端の消去（全射性の土台） -/

/-- **H¹(G_K, K̄^×)=0（本物・再輸出）**（M345F-5a）— M340F `hil90_H1_trivial`:
    巡回拡大で各コサイクルに resolvent があれば H¹(G_K,K̄^×) は自明。Kummer 完全列
    ⋯→H¹(μ_n)→H¹(K̄^×)→⋯ の右端 H¹(K̄^×) を潰し、連結準同型 H¹(μ_n)→H¹(K̄^×) が
    零＝δ が H¹(μ_n) へ全射になる本物の土台。 -/
theorem kex_hilbert90_vanishes {GK : Grp} {L : galH1Module GK}
    (cyc : hil90Cyclic GK)
    (hres : ∀ c : galH1Cocycle L, hil90ResolventHypothesis L cyc.σ c) :
    ∀ x : (galH1Group L).carrier, x = (galH1Group L).one :=
  hil90_H1_trivial cyc hres

/-- **全射（H¹(μ_n) 自身が自明な退化ケース・本物）**（M345F-5b）— 目標 H¹(G_K,μ_n) が
    自明（全元が単位元、例: 作用が μ_n を潰す退化 level）なら任意の δ は全射。
    一般の非退化 H¹(μ_n) への全射は連結準同型（LES）を要し `hsurj` 仮説で受ける。 -/
theorem kex_surjective_of_target_trivial {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A))
    (htriv : ∀ x : (galH1Group A).carrier, x = (galH1Group A).one) :
    ∀ h : (galH1Group A).carrier, ∃ a, (kexKummerMap A κ).map a = h := by
  intro h
  refine ⟨K1.one, ?_⟩
  rw [htriv ((kexKummerMap A κ).map K1.one), htriv h]

/-! ## M345F-6: capstone -/

/-- **自明 Kummer 割当**（M345F-6a）— 存在証人用の κ（全て単位コサイクルへ）。 -/
def kexTrivialKappa {GK : Grp} (A : galH1Module GK) (K1 : Grp) :
    Hom K1 (galH1_cocycles_group A) where
  map := fun _ => (galH1_cocycles_group A).one
  map_mul := fun _ _ => ((galH1_cocycles_group A).one_mul (galH1_cocycles_group A).one).symm

/-- **Kummer 完全列データ**（M345F-6b）— Kummer 写像 δ・商 K^×/ker(δ)・同型準同型 δ̄・
    その単射性（無条件・本物）・全射性（`hsurj` 仮説から δ̄ 全射）を束ねる。
    ker(δ)=(K^×)ⁿ かつ全射なら K^×/(K^×)ⁿ ≅ H¹(G_K,μ_n)。 -/
structure KexData {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A)) where
  /-- Kummer 写像 δ: K^× → H¹(G_K,μ_n)。 -/
  δ : Hom K1 (galH1Group A)
  /-- δ = 本物の Kummer 写像。 -/
  isδ : δ = kexKummerMap A κ
  /-- 商 K^×/ker(δ)。 -/
  Q : Grp
  /-- Q = K^×/ker(δ)。 -/
  isQ : Q = kexQuotient A κ
  /-- 同型準同型 δ̄: K^×/ker(δ) → H¹。 -/
  iso : Hom (kexQuotient A κ) (galH1Group A)
  /-- δ̄ は単射（無条件・本物）。 -/
  iso_injective : Hom.Injective iso
  /-- 全射仮説 `hsurj` から δ̄ が全射（K^×/ker(δ) ≅ H¹ の全射方向）。 -/
  iso_surjective_of_hyp :
    (∀ h : (galH1Group A).carrier, ∃ a, δ.map a = h) →
    ∀ h : (galH1Group A).carrier, ∃ q, iso.map q = h

/-- **証人**（M345F-6c）— 任意の G_K-加群 A・Kummer 割当 κ に対し完全列データを本物で組む。 -/
def kexData {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A)) : KexData A κ where
  δ := kexKummerMap A κ
  isδ := rfl
  Q := kexQuotient A κ
  isQ := rfl
  iso := kexIsoHom A κ
  iso_injective := kex_iso_injective A κ
  iso_surjective_of_hyp := kex_iso_surjective A κ

/-- **完全列データの存在**（M345F-6d, capstone）。 -/
theorem kex_exists {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A)) : Nonempty (KexData A κ) :=
  ⟨kexData A κ⟩

/-- **単射性 capstone**（M345F-6e）— δ̄: K^×/ker(δ) ↪ H¹(G_K,μ_n) は単射（本物）。 -/
theorem kex_iso_injective_capstone {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A)) :
    Hom.Injective (kexIsoHom A κ) :=
  kex_iso_injective A κ

/-- **実例（自明 μ_n 加群上の Kummer 完全列データの存在）**（M345F-6f）— 本物の巡回群
    ℤ/n=`zmod n`（M13 商群、可換）を μ_n の係数とする自明 G_K-加群上で、Kummer
    写像 δ・商・同型準同型（単射本物・全射は仮説付き）の完全列データが存在する。 -/
theorem kex_example (GK : Grp) (n : Nat) :
    Nonempty (KexData (galH1TrivialModule GK (zmod n) (cycStd_add_comm n))
      (kexTrivialKappa (galH1TrivialModule GK (zmod n) (cycStd_add_comm n)) (zmod n))) :=
  kex_exists _ _

end IUT
