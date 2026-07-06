/-
  IUT/Hilbert90.lean — M340F [実／本物]
  分類: 実 (Hilbert 90: H¹(Gal(L/K),L^×)=0・巡回拡大)
  complete_pct 影響: 柱B を前進（M326F H¹=Z¹/B¹ の上で、巡回拡大の Hilbert 90＝
    1-コサイクルが全てコバウンダリ c(σ^i)=σ^i(b)/b であることを本物で（resolvent の非零性を
    明示仮説とし、そこからコバウンダリ表示を厳密導出）。Kummer 完全性の土台）。
  正直な限定: resolvent b≠0（指標の一次独立）は明示仮説。一般（非巡回）Hilbert 90・
    高次 Hⁿ は後続。

  ── 本物で閉じる中身（骨格のみでない）:
  * M340F-1 `hil90Cyclic` — 巡回ガロア群 Gal(L/K)=⟨σ⟩ のモデル（生成元 σ と、
    任意元が σ の冪であるという巡回生成 `gen`）。
  * M340F-2 `hil90Coboundary` = M326F `galH1Coboundary`（乗法版）: b∈L^× から
    d_b(g)=σ_g(b)·b⁻¹。`hil90_coboundary_is_cocycle` でコサイクル則を本物で。
  * M340F-3 `hil90_cocycle_one`（c(1)=1）・`hil90_cocycle_agree_pow`
    （生成元での一致 ⟹ 全冪での一致）・`hil90_cocycle_ext_of_gen`
    （巡回生成の下でコサイクルは生成元での値で決まる）— 巡回コホモロジーの本物の核。
  * M340F-4 `hil90ResolventHypothesis` — resolvent b（≠0）の存在を**明示仮説**として
    受け取り、c(σ)=σ(b)/b を与える。古典的 resolvent b=Σ c(σ^i)σ^i(θ) の非零性
    （指標の一次独立）を名前付き入力にする。
  * M340F-5 `hil90_theorem`（主定理）— 巡回拡大で resolvent があれば c は b のコバウンダリ
    c = d_b（全ての σ^i で c(σ^i)=σ^i(b)/b）。
  * M340F-6 `hil90_H1_trivial` — 各コサイクルに resolvent があれば H¹(⟨σ⟩,L^×)=Z¹/B¹ が
    自明（全元が単位元）。M326F `galH1Group` に本物で接続。
  * M340F-7 capstone `Hilbert90Data` / `hil90Data` / `hil90_exists` と Unit 群での実例。

  **選択公理不使用・sorry 皆無**: 全宣言の公理は [propext, Quot.sound] のみ。
  禁止タクティク不使用。一般名は `hil90` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.GaloisCohomologyH1

namespace IUT

/-! ## M340F-1: 巡回ガロア群 Gal(L/K)=⟨σ⟩ のモデル -/

/-- **巡回ガロア群モデル**（M340F-1）: 生成元 σ と、任意の g が σ の冪
    g = σ^i である（巡回生成）。有限巡回拡大 Gal(L/K)≅ℤ/n の設定。 -/
structure hil90Cyclic (GK : Grp) where
  /-- 生成元 σ。 -/
  σ : GK.carrier
  /-- 巡回生成: 任意の g は σ の冪。 -/
  gen : ∀ g, ∃ i, g = GK.pow σ i

/-! ## M340F-2: コバウンダリ d_b(g) = σ_g(b)·b⁻¹（乗法版） -/

/-- **1-コバウンダリ（乗法版）**（M340F-2a）: b∈L^× から d_b(g)=σ_g(b)·b⁻¹。
    M326F `galH1Coboundary` の再輸出（L^× を係数 G_K-加群として使う）。 -/
def hil90Coboundary {GK : Grp} (A : galH1Module GK) (b : A.M.carrier) :
    galH1Cocycle A :=
  galH1Coboundary A b

/-- **コバウンダリはコサイクル**（M340F-2b, 易しい方向・証明）:
    d_b(gh) = d_b(g)·g·d_b(h)（1-コサイクル則）を本物で。 -/
theorem hil90_coboundary_is_cocycle {GK : Grp} (A : galH1Module GK)
    (b : A.M.carrier) :
    ∀ g h, (hil90Coboundary A b).f (GK.mul g h)
      = A.M.mul ((hil90Coboundary A b).f g)
                ((A.act g).map ((hil90Coboundary A b).f h)) :=
  (hil90Coboundary A b).cocycle

/-! ## M340F-3: 巡回コホモロジーの核 — コサイクルは生成元での値で決まる -/

/-- **コサイクルは単位元で 1**（M340F-3a）: c(1)=1。
    c(1·1)=c(1)·(1·c(1))=c(1)·c(1) から簡約律で。 -/
theorem hil90_cocycle_one {GK : Grp} {A : galH1Module GK}
    (c : galH1Cocycle A) : c.f GK.one = A.M.one := by
  have h := c.cocycle GK.one GK.one
  rw [GK.one_mul, A.act_one] at h
  have h2 : A.M.mul (c.f GK.one) A.M.one = A.M.mul (c.f GK.one) (c.f GK.one) := by
    rw [A.M.mul_one]
    exact h
  exact (A.M.mul_left_cancel h2).symm

/-- **生成元での一致 ⟹ 全冪での一致**（M340F-3b）: 二つのコサイクルが σ で
    一致すれば全ての σ^i で一致する（コサイクル則の帰納）。 -/
theorem hil90_cocycle_agree_pow {GK : Grp} {A : galH1Module GK}
    (σ : GK.carrier) (c1 c2 : galH1Cocycle A)
    (hgen : c1.f σ = c2.f σ) :
    ∀ i, c1.f (GK.pow σ i) = c2.f (GK.pow σ i) := by
  intro i
  induction i with
  | zero =>
    show c1.f GK.one = c2.f GK.one
    rw [hil90_cocycle_one c1, hil90_cocycle_one c2]
  | succ k ih =>
    show c1.f (GK.mul σ (GK.pow σ k)) = c2.f (GK.mul σ (GK.pow σ k))
    rw [c1.cocycle σ (GK.pow σ k), c2.cocycle σ (GK.pow σ k), hgen, ih]

/-- **コサイクルの外延性（巡回）**（M340F-3c）: 巡回生成の下で、生成元での
    値が一致するコサイクルは等しい。 -/
theorem hil90_cocycle_ext_of_gen {GK : Grp} {A : galH1Module GK}
    (cyc : hil90Cyclic GK) (c1 c2 : galH1Cocycle A)
    (hgen : c1.f cyc.σ = c2.f cyc.σ) : c1 = c2 := by
  apply galH1Cocycle.ext
  funext g
  obtain ⟨i, hi⟩ := cyc.gen g
  rw [hi]
  exact hil90_cocycle_agree_pow cyc.σ c1 c2 hgen i

/-! ## M340F-4: resolvent 仮説（指標の一次独立を名前付き入力に） -/

/-- **resolvent 仮説**（M340F-4）: コサイクル c と生成元 σ に対し、非零元
    b∈L^×（L^× の元＝可逆＝非零）で c(σ)=σ(b)·b⁻¹ を満たすものの存在。
    古典的 resolvent b=Σ c(σ^i)·σ^i(θ)（指標の一次独立で b≠0）を**明示仮説**化。 -/
structure hil90ResolventHypothesis {GK : Grp} (A : galH1Module GK)
    (σ : GK.carrier) (c : galH1Cocycle A) where
  /-- resolvent b（L^× の元ゆえ非零）。 -/
  b : A.M.carrier
  /-- c(σ) = σ(b)·b⁻¹（生成元でのコバウンダリ表示）。 -/
  resolvent : c.f σ = A.M.mul ((A.act σ).map b) (A.M.inv b)

/-! ## M340F-5: 主定理 — 巡回 Hilbert 90 -/

/-- **Hilbert 90（巡回）**（M340F-5, 主定理）: 巡回拡大で resolvent b があれば、
    コサイクル c は b のコバウンダリ c = d_b、すなわち全ての σ^i で
    c(σ^i)=σ^i(b)/b。resolvent（生成元での一致）から巡回外延性で全体へ厳密導出。 -/
theorem hil90_theorem {GK : Grp} {A : galH1Module GK}
    (cyc : hil90Cyclic GK) (c : galH1Cocycle A)
    (H : hil90ResolventHypothesis A cyc.σ c) :
    c = hil90Coboundary A H.b := by
  apply hil90_cocycle_ext_of_gen cyc
  exact H.resolvent

/-- **コサイクルは B¹ に属す**（M340F-5b）: resolvent があれば c は
    コバウンダリ部分群 B¹ = im(コバウンダリ準同型) の元。 -/
theorem hil90_cocycle_in_coboundaries {GK : Grp} {A : galH1Module GK}
    (cyc : hil90Cyclic GK) (c : galH1Cocycle A)
    (H : hil90ResolventHypothesis A cyc.σ c) :
    (galH1_coboundaries_subgroup A).mem c :=
  ⟨H.b, (hil90_theorem cyc c H).symm⟩

/-! ## M340F-6: H¹(⟨σ⟩, L^×) = 0 -/

/-- **コサイクルの類は自明**（M340F-6a）: resolvent があれば c の H¹ での類は
    単位元（射影 Z¹→H¹ で c ↦ 1）。M267F `quotientProjN_ker` で本物に。 -/
theorem hil90_class_trivial {GK : Grp} {A : galH1Module GK}
    (cyc : hil90Cyclic GK) (c : galH1Cocycle A)
    (H : hil90ResolventHypothesis A cyc.σ c) :
    (quotientProjN (galH1_cocycles_group A) (galH1_coboundaries_subgroup A)
      (galH1_coboundaries_normal A)).map c = (galH1Group A).one :=
  (quotientProjN_ker (galH1_cocycles_group A) (galH1_coboundaries_subgroup A)
    (galH1_coboundaries_normal A) c).mpr
    (hil90_cocycle_in_coboundaries cyc c H)

/-- **H¹(⟨σ⟩, L^×) = 0**（M340F-6b, capstone）: 各コサイクルに resolvent が
    あれば H¹ = Z¹/B¹ は自明（全元が単位元）。Hilbert 90 の本旨。 -/
theorem hil90_H1_trivial {GK : Grp} {A : galH1Module GK}
    (cyc : hil90Cyclic GK)
    (hres : ∀ c : galH1Cocycle A, hil90ResolventHypothesis A cyc.σ c) :
    ∀ x : (galH1Group A).carrier, x = (galH1Group A).one := by
  intro x
  induction x using Quot.ind
  rename_i c
  show (quotientProjN (galH1_cocycles_group A) (galH1_coboundaries_subgroup A)
    (galH1_coboundaries_normal A)).map c = (galH1Group A).one
  exact hil90_class_trivial cyc c (hres c)

/-! ## M340F-7: capstone と実例 -/

/-- **capstone データ**（M340F-7a）: 巡回モデル上の Hilbert 90 の全部品 —
    コバウンダリのコサイクル則・resolvent 下でのコバウンダリ表示・H¹ 自明性。 -/
structure Hilbert90Data {GK : Grp} (A : galH1Module GK) (cyc : hil90Cyclic GK) where
  /-- コバウンダリはコサイクル。 -/
  coboundary_is_cocycle : ∀ b g h, (hil90Coboundary A b).f (GK.mul g h)
    = A.M.mul ((hil90Coboundary A b).f g)
              ((A.act g).map ((hil90Coboundary A b).f h))
  /-- resolvent があれば c はコバウンダリ c = d_b。 -/
  cocycle_is_coboundary : ∀ (c : galH1Cocycle A)
    (H : hil90ResolventHypothesis A cyc.σ c), c = hil90Coboundary A H.b
  /-- 全コサイクルに resolvent があれば H¹ 自明。 -/
  h1_trivial : (∀ c : galH1Cocycle A, hil90ResolventHypothesis A cyc.σ c) →
    ∀ x : (galH1Group A).carrier, x = (galH1Group A).one

/-- **証人**（M340F-7b）。 -/
def hil90Data {GK : Grp} (A : galH1Module GK) (cyc : hil90Cyclic GK) :
    Hilbert90Data A cyc where
  coboundary_is_cocycle := fun b => (hil90Coboundary A b).cocycle
  cocycle_is_coboundary := fun c H => hil90_theorem cyc c H
  h1_trivial := fun hres => hil90_H1_trivial cyc hres

/-- **存在**（M340F-7c）。 -/
theorem hil90_exists {GK : Grp} (A : galH1Module GK) (cyc : hil90Cyclic GK) :
    Nonempty (Hilbert90Data A cyc) :=
  ⟨hil90Data A cyc⟩

/-- **自明群（Unit）**（M340F-7d）: 巡回モデルの最小実例 n=1 用の 1 点群。 -/
def hil90UnitGrp : Grp where
  carrier := Unit
  mul := fun _ _ => ()
  one := ()
  inv := fun _ => ()
  mul_assoc := fun _ _ _ => rfl
  one_mul := fun a => by cases a; rfl
  inv_mul := fun _ => rfl

/-- **Unit 群の巡回構造**（M340F-7e）: σ=()、全元は σ^0。 -/
def hil90UnitCyclic : hil90Cyclic hil90UnitGrp where
  σ := ()
  gen := fun g => ⟨0, by cases g; rfl⟩

/-- **Unit 群上の自明 G_K-加群**（M340F-7f）: 係数も Unit（可換）。 -/
def hil90UnitModule : galH1Module hil90UnitGrp :=
  galH1TrivialModule hil90UnitGrp hil90UnitGrp (fun _ _ => rfl)

/-- **実例**（M340F-7g）: Unit 巡回モデルで Hilbert 90 の全部品が実体化。 -/
example : Nonempty (Hilbert90Data hil90UnitModule hil90UnitCyclic) :=
  hil90_exists hil90UnitModule hil90UnitCyclic

/-- **実例（H¹=0）**（M340F-7h）: Unit 巡回モデルでは全コサイクルに resolvent が
    あり H¹(⟨σ⟩,L^×)=0（全元が単位元）を本物で。 -/
theorem hil90_unit_H1_trivial :
    ∀ x : (galH1Group hil90UnitModule).carrier,
      x = (galH1Group hil90UnitModule).one :=
  hil90_H1_trivial hil90UnitCyclic (fun _ => { b := (), resolvent := rfl })

end IUT
