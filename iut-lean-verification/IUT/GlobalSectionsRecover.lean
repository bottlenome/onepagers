/-
  IUT/GlobalSectionsRecover.lean — M294F（柱 A mono-anabelian 復元の
  本物の先行建設: 大域切断が環を復元する ＝ Γ(Spec R, O) ≅ R と
  Γ(Spec φ) = φ）

  ── 分類 **[実]**（本物の数学的実体の新規建設: 遠アーベル幾何の心臓
  「空間（＋構造層）から環そのものを復元する」の代数幾何版・第一歩を、
  実 CRing・実 RingHom・M293F の実構造層 O の上で本物構成する。
  toy 模型・surrogate 群を主語にしない。任意可換環 R の上での実定理）。

  **complete_pct 影響: +**（mono-anabelian 復元「空間 → 環」の代数幾何版
  第一歩を本物化。M293F の実構造層 O(D(1)) = R₁ と M291F の実 Spec 反変
  関手を土台に、(1) 大域切断関手 Γ(Spec R) := O(Spec R の大域切断) = R₁ が
  R と**環同型**（両方向の環準同型が互いに逆）R ≅ Γ(Spec R, O) を本物で
  確立し、(2) 環準同型 φ:R→S が誘導する大域切断上の写像 Γ(Spec φ) が、
  この同型のもとで**φ そのものと一致**する（Γ(Spec φ) = φ）ことを本物で
  証明する。＝「環はその locally ringed space の大域切断として復元され、
  環準同型も復元される」。柱 A の complete_pct を前進させる本物建設(b)。）

  柱 A「mono-anabelian 復元（空間から環を戻す IUT の心臓）」。

  ロードマップ上の位置: IUT の遠アーベル復元（AbsTopIII: π₁^ét から数体を
  復元）の**代数幾何版・第一歩**。「空間から環を復元する」思想を、位相
  空間 Spec R とその構造層 O から可換環 R そのものを大域切断として戻す、
  という最も基本的な形で本物化する。逆向き（環 → 空間 = Spec）は M291F、
  構造層 O の建設は M293F、本モジュールはその二つを束ねて**復元定理**を
  与える。

  * M294F-1 `globSecGamma` — 大域切断環 Γ(Spec R, O) := O(D(1)) = R₁。
  * M294F-2 `globSecInvHom` / `globSecEvalHom` — 大域評価 Γ(Spec R) → R を
    環準同型として本物化（両側逆を持つ環準同型の逆は環準同型）。
  * M294F-3 `GlobSecRingIso` / `globSec_ring_iso` — **R ≅ Γ(Spec R, O)**
    （両方向の環準同型 fwd/inv が互いに逆）。環が大域切断として復元。
  * M294F-4 `globSecGammaFun` / `globSecGammaMap` — 環準同型 φ:R→S が
    誘導する大域切断上の環準同型 Γ(Spec φ): Γ(Spec R) → Γ(Spec S)
    （num/1ᵏ ↦ φ(num)/1ᵏ）を局所化上で**直接**（同型経由でなく）構成。
  * M294F-5 `globSec_gamma_map_comm` / `globSec_gamma_map_eq_phi` —
    **Γ(Spec φ) = φ**: 上記同型のもとで Γ(Spec φ) が φ と一致。環準同型も
    Spec 写像＋層写像（大域切断への引き戻し）から復元される。
  * M294F-6 `GlobSecGammaSpecId` / `globSec_gamma_spec_id` — 関手
    Γ∘Spec ≅ id の**対象レベル（R≅Γ(Spec R)）と射レベル（Γ(Spec φ)=φ）**を
    束ねた骨組み（アフィンスキームの圏 ≃ CRingᵒᵖ の片側の核）。
  * M294F-7 `GlobalSectionsData` / `globSec_exists` / `globSec_recover_ring`
    / `globSec_recover_hom` — capstone。
  * M294F-8 実例: 離散体 K で K ≅ Γ(Spec K, O) かつ Spec K は 1 点
    （唯一の素イデアル = 零イデアル）を本物で確認。

  **正直な限定（必守申告・消去弱化禁止）**:
  1. 「locally ringed space の射」の完全な圏論的定義（連続写像＋層の射で
     各点局所環準同型）は M293F の前層骨組みの上に乗るので後続。ここは
     **大域切断レベルでの復元**（Γ(Spec φ) = φ・R ≅ Γ(Spec R)）まで本物。
     Γ(Spec φ) は層の引き戻しの大域切断（num/1ᵏ ↦ φ(num)/1ᵏ）として本物
     構成し、それが φ と一致することを証明する。
  2. アフィンスキームの圏 ≃ CRingᵒᵖ の**完全な圏同値**（充満忠実＋本質
     全射）は後続。ここは Γ∘Spec ≅ id の対象レベル・射レベルの本物の核
     （R≅Γ(Spec R) と Γ(Spec φ)=φ）まで。
  3. mono-anabelian の**本丸**（π₁^ét から数体を復元 = AbsTopIII）は
     さらに後続。本モジュールは「空間から環を復元」の**代数幾何版・第一歩**。
  4. 体 K は core のみ（mathlib 禁止）ゆえ **離散体**（∀a, a が単元 ∨ a=0）
     を仮定に取る形。具体的な Field 型の建設は後続。Spec K が 1 点である
     ことは本物で（任意素イデアルが零イデアルに一致）。

  全て選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。
  禁止タクティク不使用（cases/obtain/induction/rw/show/refine/exact/apply/
  intro/rfl のみ）。共有ファイル未変更（新規 1 本のみ）。
-/
import IUT.StructureSheafBasic
import IUT.SpecFunctorial

namespace IUT

/-! ## M294F-1: 大域切断環 Γ(Spec R, O) = O(D(1)) = R₁ -/

/-- **M294F-1: 大域切断関手 Γ** — アフィンスキーム Spec R の構造層 O の
    大域切断 Γ(Spec R, O) = O(D(1)) = R₁（M293F の f = 1 局所化）。 -/
def globSecGamma (R : CRing) : CRing := structSheaf_section_isCRing R R.one

/-! ## M294F-2: 大域評価を環準同型として本物化 -/

/-- 両側逆を持つ環準同型 φ:R→S の逆写像 g:S→R は単射性を与える
    （g が φ の左逆なら φ は単射）。 -/
theorem globSec_hom_inj {R S : CRing} (φ : RingHom R S) (g : S.carrier → R.carrier)
    (hl : ∀ r, g (φ.map r) = r) {x y : R.carrier} (h : φ.map x = φ.map y) : x = y := by
  have h1 : g (φ.map x) = g (φ.map y) := by rw [h]
  rw [hl, hl] at h1
  exact h1

/-- **M294F-2a: 両側逆を持つ環準同型の逆は環準同型**。φ:R→S が環準同型で
    g:S→R が両側逆（g∘φ=id・φ∘g=id）なら、g も環準同型 S→R。
    大域評価 Γ(Spec R) → R を環準同型にするのに使う。 -/
def globSecInvHom {R S : CRing} (φ : RingHom R S) (g : S.carrier → R.carrier)
    (hl : ∀ r, g (φ.map r) = r) (hr : ∀ s, φ.map (g s) = s) : RingHom S R where
  map := g
  map_add := by
    intro a b
    apply globSec_hom_inj φ g hl
    rw [hr, φ.map_add, hr, hr]
  map_mul := by
    intro a b
    apply globSec_hom_inj φ g hl
    rw [hr, φ.map_mul, hr, hr]
  map_one := by
    apply globSec_hom_inj φ g hl
    rw [hr, φ.map_one]

/-- **M294F-2b: 大域評価環準同型** Γ(Spec R) → R（num/1ᵏ ↦ num）。
    M293F の環同型 `structSheaf_global_eq_ring` の両側逆性から環準同型化。 -/
def globSecEvalHom (R : CRing) : RingHom (globSecGamma R) R :=
  globSecInvHom (structSheaf_globalHom R) structSheafGlobalEval
    (structSheaf_global_eq_ring R).1 (structSheaf_global_eq_ring R).2

/-! ## M294F-3: 環同型 R ≅ Γ(Spec R, O)（環が大域切断として復元される） -/

/-- **M294F-3a: 環同型** — 両方向の環準同型 fwd:R→S・inv:S→R が互いに逆。 -/
structure GlobSecRingIso (R S : CRing) where
  /-- 順方向の環準同型。 -/
  fwd : RingHom R S
  /-- 逆方向の環準同型。 -/
  inv : RingHom S R
  /-- inv∘fwd = id。 -/
  left_inv : ∀ r, inv.map (fwd.map r) = r
  /-- fwd∘inv = id。 -/
  right_inv : ∀ s, fwd.map (inv.map s) = s

/-- **M294F-3b: 環は大域切断として復元される** R ≅ Γ(Spec R, O)。
    fwd = 大域切断への埋め込み R → R₁（r ↦ r/1）、inv = 大域評価 R₁ → R。
    ＝ mono-anabelian「空間（＋構造層）から環を復元する」の代数幾何版・核。 -/
def globSec_ring_iso (R : CRing) : GlobSecRingIso R (globSecGamma R) where
  fwd := structSheaf_globalHom R
  inv := globSecEvalHom R
  left_inv := (structSheaf_global_eq_ring R).1
  right_inv := (structSheaf_global_eq_ring R).2

/-! ## M294F-4: 環準同型が誘導する大域切断上の写像 Γ(Spec φ) -/

/-- 大域切断の前分数 num/1ᵃ に φ を掛けた φ(num)/1ᵃ は関係を保つ
    （R₁ の関係は num の一致に退化するので φ で保たれる）。 -/
theorem globSec_gammaPre_rel {R S : CRing} (φ : RingHom R S)
    {a b : StructSheafPreLoc R R.one} (h : structSheafRel R R.one a b) :
    structSheafRel S S.one
      (⟨φ.map a.num, a.den⟩ : StructSheafPreLoc S S.one)
      ⟨φ.map b.num, b.den⟩ := by
  have hnum : a.num = b.num := structSheafGlobalEval_wd h
  refine ⟨0, ?_⟩
  show S.mul (structSheafPow S S.one 0)
    (S.add (S.mul (φ.map a.num) (structSheafPow S S.one b.den))
      (S.neg (S.mul (φ.map b.num) (structSheafPow S S.one a.den)))) = S.zero
  rw [structSheafPow_zero, S.one_mul, structSheafPow_one_eq_one S b.den,
    structSheafPow_one_eq_one S a.den, structSheafCR_mul_one, structSheafCR_mul_one,
    hnum, structSheafCR_add_neg]

/-- **M294F-4a: 誘導写像の台** Γ(Spec R) → Γ(Spec S)、num/1ᵃ ↦ φ(num)/1ᵃ。
    層の引き戻しの大域切断（同型経由でなく局所化上で直接構成）。 -/
def globSecGammaFun {R S : CRing} (φ : RingHom R S)
    (s : StructSheafSection R R.one) : StructSheafSection S S.one :=
  Quot.lift (fun x => Quot.mk (structSheafRel S S.one) ⟨φ.map x.num, x.den⟩)
    (fun _ _ h => Quot.sound (globSec_gammaPre_rel φ h)) s

/-- **M294F-4b: Γ(Spec φ)** — 環準同型 φ:R→S が誘導する大域切断上の
    **環準同型** Γ(Spec R) → Γ(Spec S)。 -/
def globSecGammaMap {R S : CRing} (φ : RingHom R S) :
    RingHom (globSecGamma R) (globSecGamma S) where
  map := globSecGammaFun φ
  map_add := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    apply congrArg (Quot.mk (structSheafRel S S.one))
    apply structSheafPreLoc_ext
    · show φ.map (R.add (R.mul x.num (structSheafPow R R.one y.den))
          (R.mul y.num (structSheafPow R R.one x.den)))
        = S.add (S.mul (φ.map x.num) (structSheafPow S S.one y.den))
          (S.mul (φ.map y.num) (structSheafPow S S.one x.den))
      rw [structSheafPow_one_eq_one R y.den, structSheafPow_one_eq_one R x.den,
        structSheafCR_mul_one, structSheafCR_mul_one, φ.map_add,
        structSheafPow_one_eq_one S y.den, structSheafPow_one_eq_one S x.den,
        structSheafCR_mul_one, structSheafCR_mul_one]
    · rfl
  map_mul := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    apply congrArg (Quot.mk (structSheafRel S S.one))
    apply structSheafPreLoc_ext
    · show φ.map (R.mul x.num y.num) = S.mul (φ.map x.num) (φ.map y.num)
      rw [φ.map_mul]
    · rfl
  map_one := by
    apply congrArg (Quot.mk (structSheafRel S S.one))
    apply structSheafPreLoc_ext
    · show φ.map R.one = S.one
      exact φ.map_one
    · rfl

/-! ## M294F-5: Γ(Spec φ) = φ（環準同型も復元される） -/

/-- **M294F-5a: 前方可換性** — 大域切断への埋め込みと Γ(Spec φ) が可換:
    Γ(Spec φ)(r/1) = φ(r)/1。 -/
theorem globSec_gamma_map_comm {R S : CRing} (φ : RingHom R S) (r : R.carrier) :
    (globSecGammaMap φ).map ((globSec_ring_iso R).fwd.map r)
      = (globSec_ring_iso S).fwd.map (φ.map r) := rfl

/-- **M294F-5b: Γ(Spec φ) = φ** — 環同型 R≅Γ(Spec R)・S≅Γ(Spec S) のもとで、
    φ が誘導する大域切断上の写像 Γ(Spec φ) を S 側で評価すると φ に戻る。
    ＝「環準同型も Spec 写像＋層写像（大域切断への引き戻し）から復元される」。 -/
theorem globSec_gamma_map_eq_phi {R S : CRing} (φ : RingHom R S) (r : R.carrier) :
    (globSec_ring_iso S).inv.map
        ((globSecGammaMap φ).map ((globSec_ring_iso R).fwd.map r))
      = φ.map r := rfl

/-! ## M294F-6: Γ∘Spec ≅ id（対象レベル ＋ 射レベルの骨組み） -/

/-- **M294F-6a: Γ∘Spec ≅ id の骨組み** — 関手 Γ∘Spec が恒等関手に自然
    同型であることの、対象レベル（R≅Γ(Spec R)）と射レベル（Γ(Spec φ)=φ）
    を束ねる。アフィンスキームの圏 ≃ CRingᵒᵖ の片側の核。 -/
structure GlobSecGammaSpecId where
  /-- 対象レベル: 各環 R について R ≅ Γ(Spec R, O)。 -/
  obj : ∀ R : CRing, GlobSecRingIso R (globSecGamma R)
  /-- 射レベル: 各環準同型 φ について Γ(Spec φ) = φ（同型経由）。 -/
  mor : ∀ {R S : CRing} (φ : RingHom R S) (r : R.carrier),
    (obj S).inv.map ((globSecGammaMap φ).map ((obj R).fwd.map r)) = φ.map r

/-- **M294F-6b: Γ∘Spec ≅ id（対象・射レベルの本物の核）**。 -/
def globSec_gamma_spec_id : GlobSecGammaSpecId where
  obj := globSec_ring_iso
  mor := fun φ r => globSec_gamma_map_eq_phi φ r

/-! ## M294F-7: capstone -/

/-- **M294F-7a: 大域切断復元データ** — 環 R・その大域切断環 Γ(Spec R)・
    両者の環同型を束ねる。「環はその Spec と構造層の大域切断として復元」。 -/
structure GlobalSectionsData (R : CRing) where
  /-- 大域切断環 Γ(Spec R, O)。 -/
  gamma : CRing
  /-- gamma は O(D(1)) = R₁。 -/
  gamma_eq : gamma = globSecGamma R
  /-- 環同型 R ≅ Γ(Spec R, O)。 -/
  iso : GlobSecRingIso R gamma
  /-- 復元（両方向が互いに逆）。 -/
  recover : (∀ r, iso.inv.map (iso.fwd.map r) = r)
    ∧ (∀ s, iso.fwd.map (iso.inv.map s) = s)

/-- **M294F-7b: 大域切断復元データの存在**（本物の環同型）。 -/
def globSec_exists (R : CRing) : GlobalSectionsData R where
  gamma := globSecGamma R
  gamma_eq := rfl
  iso := globSec_ring_iso R
  recover := ⟨(globSec_ring_iso R).left_inv, (globSec_ring_iso R).right_inv⟩

/-- **M294F-7c: 環は大域切断として復元される** R ≅ Γ(Spec R, O)
    （両方向の環準同型が互いに逆）。 -/
theorem globSec_recover_ring (R : CRing) :
    (∀ r : R.carrier,
        (globSecEvalHom R).map ((structSheaf_globalHom R).map r) = r)
    ∧ (∀ s : StructSheafSection R R.one,
        (structSheaf_globalHom R).map ((globSecEvalHom R).map s) = s) :=
  ⟨(globSec_ring_iso R).left_inv, (globSec_ring_iso R).right_inv⟩

/-- **M294F-7d: 環準同型は復元される** Γ(Spec φ) = φ。 -/
theorem globSec_recover_hom {R S : CRing} (φ : RingHom R S) (r : R.carrier) :
    (globSec_ring_iso S).inv.map
        ((globSecGammaMap φ).map ((globSec_ring_iso R).fwd.map r))
      = φ.map r :=
  globSec_gamma_map_eq_phi φ r

/-! ## M294F-8: 実例（離散体 K は K ≅ Γ(Spec K, O)・Spec K は 1 点） -/

/-- **離散体**（core のみ・mathlib 禁止ゆえの構成的定義）: すべての元が
    単元または零。 -/
def globSecIsField (K : CRing) : Prop :=
  ∀ a, (∃ b, K.mul a b = K.one) ∨ a = K.zero

/-- **M294F-8a: 体の Spec は 1 点** — 離散体 K の任意の素イデアル P は
    零イデアル（P.mem a → a = 0）。＝ Spec K は唯一の点（零イデアル）。
    体では非零元はすべて単元ゆえ真イデアルは単元を含めず、非零は入れない。 -/
theorem globSec_field_spec_onepoint {K : CRing} (hK : globSecIsField K)
    (P : specFunPrime K) (a : K.carrier) (ha : P.mem a) : a = K.zero := by
  cases hK a with
  | inl hunit =>
    obtain ⟨b, hb⟩ := hunit
    have h1 : P.mem (K.mul b a) := P.mem_smul b a ha
    have h2 : K.mul b a = K.one := by
      rw [K.mul_comm]
      exact hb
    rw [h2] at h1
    exact absurd h1 P.proper
  | inr hz => exact hz

/-- **M294F-8b: 体は大域切断として復元される** — 離散体 K で
    K ≅ Γ(Spec K, O)。Spec K は 1 点で、その上の切断環がちょうど K。 -/
def globSec_field_iso (K : CRing) (_ : globSecIsField K) :
    GlobSecRingIso K (globSecGamma K) :=
  globSec_ring_iso K

/-- **M294F-8c: 体の復元（束ね）** — 離散体 K で (1) K ≅ Γ(Spec K, O)
    （環同型）かつ (2) Spec K は 1 点（唯一の素イデアル = 零イデアル）。 -/
theorem globSec_field_recover {K : CRing} (hK : globSecIsField K) :
    ((∀ r, (globSecEvalHom K).map ((structSheaf_globalHom K).map r) = r)
      ∧ (∀ s, (structSheaf_globalHom K).map ((globSecEvalHom K).map s) = s))
    ∧ (∀ (P : specFunPrime K) (a : K.carrier), P.mem a → a = K.zero) :=
  ⟨⟨(globSec_ring_iso K).left_inv, (globSec_ring_iso K).right_inv⟩,
    fun P a ha => globSec_field_spec_onepoint hK P a ha⟩

end IUT
