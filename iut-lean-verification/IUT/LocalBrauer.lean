/-
  IUT/LocalBrauer.lean — M360F [実／本物]
  分類: 実 (局所 Brauer 群 Br(K)=H²(G_K,K̄^×))
  complete_pct 影響: 柱B を前進（M350F カップ積の H² 機構で局所 Brauer 群 Br(K)=H²(G_K,K̄^×)
    をアーベル群として構成・巡回代数類 χ∪δ(a)∈Br(K)・分裂条件（コバウンダリ）・n-捻れ
    Br(K)[n] を本物で。中心単純代数の分類の土台）。
  正直な限定: 局所不変量 inv:Br(K)≅ℚ/ℤ・完全類体論は外部仮説/後続。

  ── 本物で閉じる中身（骨格のみでない）:
  * M360F-1 `brauGroup` — Br(K) = H²(G_K,K̄^×)。M350F `cupH2group` を K̄^× 加群
    （`galH1Module` として受け取る）で具体化。**本物のアーベル群**。
  * M360F-2 `brau_is_abelian` — Br(K) はアーベル（M350F `cupZ2_comm` から H² へ降下）。
  * M360F-3 `brau_pow_one`/`brau_pow_mul`/`brau_pow_inv` — アーベル群の冪の
    基本法則（1ⁿ=1・(xy)ⁿ=xⁿyⁿ・(x⁻¹)ⁿ=(xⁿ)⁻¹）を本物で。
  * M360F-4 `brauTorsionSub`/`brauNsub` — n-捻れ部分群 Br(K)[n]（アーベルゆえ部分群）。
  * M360F-5 `brauCyclicClass`/`brau_cyclic_from_cup` — 巡回代数類 χ∪δ(a)∈Br(K)
    （M350F `cupProduct`：指標 χ∈H¹(G_K,ℤ/n) と Kummer 類 δ(a)∈H¹(G_K,μ_n) の
    カップ積）。分裂条件 `brau_split_iff`（類が自明 ⟺ コサイクルが 2-コバウンダリ、
    M267F `quotientProjN_ker`）・`brau_trivial`（コバウンダリ指標由来の巡回類は分裂、
    M350F `cup_coboundary_mem`）。
  * M360F-6 capstone `BrauerData`/`brauData`/`brau_exists` と実例（ℤ/n 係数）。

  **正直な限定**（消去・弱化禁止）:
  1. 係数 K̄^× は G_K-加群 `galH1Module` として**受け取る**（M326F と同じ規約）。
     体の分離閉包からの実 G_K 作用の構成そのものは範囲外。
  2. **局所不変量 inv: Br(K) ≅ ℚ/ℤ** は `brau_inv_hypothesis`（未導出の Prop 仮説）。
  3. **n-捻れと H²(G_K,μ_n) の関係**（Kummer 完全列 M345F 経由の
     Br(K)[n]≅H²(G_K,μ_n)）は係数変換 μ_n⊂K̄^× を要し `brau_nsub_mu_hypothesis`
     （Prop 仮説）として明示。
  4. **局所類体論（全 Brauer 類が巡回代数）** は `brau_cyclic_generation_hypothesis`
     （Prop 仮説）。相互律・完全 CFT は後続。

  **選択公理不使用・sorry 皆無**: 全宣言の公理は [propext, Quot.sound] のみ。
  禁止タクティク不使用。一般名は `brau` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.CupProduct
import IUT.Hilbert90

namespace IUT

/-! ## M360F-1: 局所 Brauer 群 Br(K) = H²(G_K, K̄^×) -/

/-- **局所 Brauer 群**（M360F-1）: Br(K) = H²(G_K, K̄^×)。M350F の H² 機構
    `cupH2group` を K̄^× 加群（`galH1Module GK` として受け取る）で具体化した
    **本物のアーベル群**。中心単純代数 / 巡回代数の分類が住む群。 -/
def brauGroup {GK : Grp} (Kbar : galH1Module GK) : Grp :=
  cupH2group Kbar

/-! ## M360F-2: Br(K) はアーベル群 -/

/-- **Br(K) はアーベル群**（M360F-2）: H² = Z²/B² の積が Z² の（アーベルな）
    積から誘導される（M350F `cupZ2_comm`）。 -/
theorem brau_is_abelian {GK : Grp} (Kbar : galH1Module GK) :
    ∀ x y, (brauGroup Kbar).mul x y = (brauGroup Kbar).mul y x := by
  intro x y
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  show Quot.mk _ ((cupZ2group Kbar).mul a b) = Quot.mk _ ((cupZ2group Kbar).mul b a)
  rw [cupZ2_comm Kbar a b]

/-! ## M360F-3: アーベル群の冪の基本法則 -/

/-- **単位元の冪**（M360F-3a）: 1ⁿ = 1。 -/
theorem brau_pow_one (G : Grp) (n : Nat) : G.pow G.one n = G.one := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show G.mul G.one (G.pow G.one k) = G.one
    rw [G.one_mul, ih]

/-- **積の冪**（M360F-3b, アーベル）: (xy)ⁿ = xⁿ·yⁿ。
    M326F `galH1_mul4_swap`（中間入替則）を冪の帰納で使う。 -/
theorem brau_pow_mul (G : Grp) (comm : ∀ a b, G.mul a b = G.mul b a)
    (x y : G.carrier) (n : Nat) :
    G.pow (G.mul x y) n = G.mul (G.pow x n) (G.pow y n) := by
  induction n with
  | zero =>
    show G.one = G.mul G.one G.one
    rw [G.one_mul]
  | succ k ih =>
    show G.mul (G.mul x y) (G.pow (G.mul x y) k)
       = G.mul (G.mul x (G.pow x k)) (G.mul y (G.pow y k))
    rw [ih]
    exact galH1_mul4_swap G comm x y (G.pow x k) (G.pow y k)

/-- **逆元の冪**（M360F-3c, アーベル）: (x⁻¹)ⁿ = (xⁿ)⁻¹。
    M326F `galH1_inv_mul`（反元の分配則）を冪の帰納で使う。 -/
theorem brau_pow_inv (G : Grp) (comm : ∀ a b, G.mul a b = G.mul b a)
    (x : G.carrier) (n : Nat) :
    G.pow (G.inv x) n = G.inv (G.pow x n) := by
  induction n with
  | zero =>
    show G.one = G.inv G.one
    rw [cup_inv_one G]
  | succ k ih =>
    show G.mul (G.inv x) (G.pow (G.inv x) k) = G.inv (G.mul x (G.pow x k))
    rw [ih, galH1_inv_mul G comm x (G.pow x k)]

/-! ## M360F-4: n-捻れ部分群 Br(K)[n] -/

/-- **n-捻れ部分群**（M360F-4a）: アーベル群 G で {x | xⁿ = 1} は部分群。
    閉性は M360F-3 の冪法則（(xy)ⁿ=xⁿyⁿ・(x⁻¹)ⁿ=(xⁿ)⁻¹）。 -/
def brauTorsionSub (G : Grp) (comm : ∀ a b, G.mul a b = G.mul b a) (n : Nat) :
    Subgroup G where
  mem := fun x => G.pow x n = G.one
  one_mem := brau_pow_one G n
  mul_mem := fun {a b} ha hb => by
    show G.pow (G.mul a b) n = G.one
    rw [brau_pow_mul G comm a b n, ha, hb, G.one_mul]
  inv_mem := fun {a} ha => by
    show G.pow (G.inv a) n = G.one
    rw [brau_pow_inv G comm a n, ha, cup_inv_one G]

/-- **n-捻れ Br(K)[n]**（M360F-4b）: Br(K) の n-捻れ部分群
    {x∈Br(K) | n·x = 0}。中心単純代数の指数 (exponent) が n を割るクラス。 -/
def brauNsub {GK : Grp} (Kbar : galH1Module GK) (n : Nat) :
    Subgroup (brauGroup Kbar) :=
  brauTorsionSub (brauGroup Kbar) (brau_is_abelian Kbar) n

/-! ## M360F-5: 巡回代数類 χ∪δ(a) と分裂条件 -/

/-- **分裂条件**（M360F-5a）: 2-コサイクル z の Brauer 類が自明（分裂）
    ⟺ z が 2-コバウンダリ（B² に属す）。M267F `quotientProjN_ker` で本物。
    中心単純代数が行列環に分裂するための条件のコホモロジー版。 -/
theorem brau_split_iff {GK : Grp} (Kbar : galH1Module GK) (z : cupTwoCocycle Kbar) :
    (quotientProjN (cupZ2group Kbar) (cupB2sub Kbar) (cupB2_normal Kbar)).map z
      = (brauGroup Kbar).one ↔ (cupB2sub Kbar).mem z :=
  quotientProjN_ker (cupZ2group Kbar) (cupB2sub Kbar) (cupB2_normal Kbar) z

/-- **巡回代数類**（M360F-5b）: 指標 χ∈H¹(G_K,ℤ/n)（コサイクル）と Kummer 類
    δ(a)∈H¹(G_K,μ_n)（コサイクル g）から、テンソル対 P による カップ積
    χ∪δ(a) ∈ Br(K) = H²(G_K,K̄^×)。M350F `cupProduct`。巡回代数 (χ,a) の
    Brauer 類の具体構成。 -/
def brauCyclicClass {GK : Grp} {A B : galH1Module GK} (Kbar : galH1Module GK)
    (P : cupPairing A B Kbar) (χ : galH1Cocycle A) (g : galH1Cocycle B) :
    (brauGroup Kbar).carrier :=
  cupProduct P χ g

/-- **巡回類 = 指標とKummer類のカップ積**（M360F-5c）: brauCyclicClass は
    2-コサイクル χ∪g（`cupCocycleOf`）の H² への射影に等しい（定義展開）。 -/
theorem brau_cyclic_from_cup {GK : Grp} {A B : galH1Module GK}
    (Kbar : galH1Module GK) (P : cupPairing A B Kbar)
    (χ : galH1Cocycle A) (g : galH1Cocycle B) :
    brauCyclicClass Kbar P χ g
      = (quotientProjN (cupZ2group Kbar) (cupB2sub Kbar) (cupB2_normal Kbar)).map
          (cupCocycleOf P χ g) :=
  rfl

/-- **コバウンダリ指標の巡回類は分裂**（M360F-5d）: 指標が 1-コバウンダリ f_a
    のとき、その巡回代数類 χ∪g は Br(K) で自明（分裂）。M350F `cup_coboundary_mem`
    （cup(f_a,g)∈B²）＋分裂条件。 -/
theorem brau_trivial {GK : Grp} {A B : galH1Module GK} (Kbar : galH1Module GK)
    (P : cupPairing A B Kbar) (a : A.M.carrier) (g : galH1Cocycle B) :
    brauCyclicClass Kbar P (galH1Coboundary A a) g = (brauGroup Kbar).one := by
  rw [brau_cyclic_from_cup Kbar P (galH1Coboundary A a) g]
  exact (brau_split_iff Kbar (cupCocycleOf P (galH1Coboundary A a) g)).mpr
    (cup_coboundary_mem P a g)

/-! ## M360F-6: 外部仮説（未導出・honest hypothesis） -/

/-- **外部仮説（未導出）: n-捻れと H²(G_K,μ_n) の関係**（M360F-6a）: 係数変換
    μ_n ⊂ K̄^× による H²(G_K,μ_n) → Br(K) が n-捻れ Br(K)[n] に入る（Kummer
    完全列 M345F 経由の Br(K)[n]≅H²(G_K,μ_n) の骨組み）。係数変換写像の構成は
    範囲外ゆえ **Prop 仮説として明示**。 -/
def brau_nsub_mu_hypothesis {GK : Grp} (Kbar Mu : galH1Module GK) (n : Nat) : Prop :=
  ∃ ι : Hom (cupH2group Mu) (brauGroup Kbar),
    ∀ x, (brauNsub Kbar n).mem (ι.map x)

/-- **外部仮説（未導出）: 局所不変量 inv: Br(K) ≅ ℚ/ℤ**（M360F-6b）: 局所類体論の
    核心である不変量同型（Br(K) の元を ℚ/ℤ の元＝不変量へ）を、ℚ/ℤ を表す群 QZ への
    全単射準同型として **Prop 仮説化**。相互律・充満忠実は後続。 -/
def brau_inv_hypothesis {GK : Grp} (Kbar : galH1Module GK) (QZ : Grp) : Prop :=
  ∃ inv : Hom (brauGroup Kbar) QZ,
    Hom.Injective inv ∧ (∀ y, ∃ x, inv.map x = y)

/-- **外部仮説（未導出）: 全 Brauer 類は巡回代数**（M360F-6c）: 局所体上の
    全ての中心可除環は巡回代数である（局所 CFT の帰結）＝ Br(K) の全類が
    テンソル対 P による巡回類 χ∪g で表される、を **Prop 仮説化**。 -/
def brau_cyclic_generation_hypothesis {GK : Grp} {A B : galH1Module GK}
    (Kbar : galH1Module GK) (P : cupPairing A B Kbar) : Prop :=
  ∀ x : (brauGroup Kbar).carrier,
    ∃ (χ : galH1Cocycle A) (g : galH1Cocycle B), brauCyclicClass Kbar P χ g = x

/-! ## M360F-7: capstone -/

/-- **capstone データ**（M360F-7a）: K̄^× 加群 Kbar に対する Br(K) の全部品 —
    Br(K)=H²(G_K,K̄^×)・アーベル性・分裂条件・n-捻れ部分群。 -/
structure BrauerData {GK : Grp} (Kbar : galH1Module GK) where
  /-- 局所 Brauer 群 Br(K)。 -/
  Br : Grp
  /-- Br(K) = H²(G_K,K̄^×) の同定。 -/
  Br_is : Br = brauGroup Kbar
  /-- Br(K) はアーベル。 -/
  abelian : ∀ x y, (brauGroup Kbar).mul x y = (brauGroup Kbar).mul y x
  /-- 分裂条件: 類が自明 ⟺ コサイクルが 2-コバウンダリ。 -/
  split_iff : ∀ z : cupTwoCocycle Kbar,
    (quotientProjN (cupZ2group Kbar) (cupB2sub Kbar) (cupB2_normal Kbar)).map z
      = (brauGroup Kbar).one ↔ (cupB2sub Kbar).mem z
  /-- n-捻れ部分群 Br(K)[n]。 -/
  torsion : Nat → Subgroup (brauGroup Kbar)
  /-- torsion の同定。 -/
  torsion_is : ∀ n, torsion n = brauNsub Kbar n

/-- **証人**（M360F-7b）。 -/
def brauData {GK : Grp} (Kbar : galH1Module GK) : BrauerData Kbar where
  Br := brauGroup Kbar
  Br_is := rfl
  abelian := brau_is_abelian Kbar
  split_iff := brau_split_iff Kbar
  torsion := brauNsub Kbar
  torsion_is := fun _ => rfl

/-- **Br(K) 構造の存在**（M360F-7c）。 -/
theorem brau_exists {GK : Grp} (Kbar : galH1Module GK) :
    Nonempty (BrauerData Kbar) :=
  ⟨brauData Kbar⟩

/-- **Br(K) は（アーベル）群**（M360F-7d）。 -/
theorem brau_isGroup {GK : Grp} (Kbar : galH1Module GK) :
    ∀ x y, (brauGroup Kbar).mul x y = (brauGroup Kbar).mul y x :=
  brau_is_abelian Kbar

/-! ## M360F-8: 実例（自明作用 ℤ/n 係数 K̄^× 模型上の Br(K)） -/

/-- **実例**（M360F-8a）: Unit ガロア群・ℤ/n 係数（自明作用）の K̄^× 模型上で
    Br(K)=H²(G_K,ℤ/n) の全部品が実体化する。 -/
def brauZmodData (n : Nat) : BrauerData (cupZmodModule hil90UnitGrp n) :=
  brauData (cupZmodModule hil90UnitGrp n)

/-- **実例存在**（M360F-8b）: 局所 Brauer 群 Br(K)=H²(G_K,K̄^×) の証人が存在。 -/
theorem brau_zmod_exists (n : Nat) :
    Nonempty (BrauerData (cupZmodModule hil90UnitGrp n)) :=
  ⟨brauZmodData n⟩

/-- **実例（巡回類）**（M360F-8c）: ℤ/n 係数上のカップ積で巡回代数類
    χ∪g ∈ Br(K) が実体化する（`cupZmodPairing` を使う）。 -/
def brauZmodCyclicClass (n : Nat)
    (χ g : galH1Cocycle (cupZmodModule hil90UnitGrp n)) :
    (brauGroup (cupZmodModule hil90UnitGrp n)).carrier :=
  brauCyclicClass (cupZmodModule hil90UnitGrp n) (cupZmodPairing hil90UnitGrp n) χ g

end IUT
