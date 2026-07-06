/-
  IUT/ThetaCyclotomicRigidity.lean — M338F [実／本物]
  分類: 実 (mono-theta 環境の円分剛性＝三剛性の3つ目・完結)
  complete_pct 影響: 柱E を前進（三剛性の3つ目＝円分剛性：内部円分体（テータ群の中心/交換子
    ≅ ℤ/n）と外部 μ_n の同型が標準的で ℤ/n^× 捻れ不定性がないことを本物で構成し、
    M323F 定数倍剛性・M333F 離散剛性と合わせ三剛性を束ねる）。
  正直な限定: <外部仮説として残した部分・tempered π₁ 商本丸は骨組み等>
    - **内部円分体の主語は離散 Heisenberg テータ群 thetaGrp の中心 {(0,0,z)} と
      その mod-l 商 thetaGrpMod l の中心類**（M11/M98F）である。交換子
      [(1,0,0),(0,1,0)] = (0,0,1) が中心生成元を標準指定する（comm_xy/theta_comm_mod）
      ことは本物だが、この中心を **tempered π₁^ét の交換子（実の遠アーベル対象）
      として実現**することは骨組み（柱E/D 後続）。
    - **外部円分体 μ_l の生成元 ζ（1 の l 乗根・冪の相異性 hdist）は仮説として受ける**
      （実例では M121F mu_l_zp_exists の本物の μ_l(ℤ_p) から供給できる）。
    - **mono-theta 環境の自己準同型が「標準生成元を中心（テータ切断）捻れを除いて保つ」
      という性質は明示の Prop 仮説 `thCyc_section_twist_hypothesis` として受け、
      決して自前で導出しない**（tempered π₁ から来る自己同型がこの形を取ることは
      柱E/D 後続の外部入力）。そこから円分剛性（中心生成元の厳密固定）を本物に導出する。
    - 円分剛性の「本丸」——内部円分体 ↔ 外部 μ_l の同型が標準的で ℤ/l^× 捻れが
      生き残らないこと——は本物で構成する: (1) 同型 centerToMu が準同型・生成元 ↦ ζ・
      忠実（核 = lℤ, ℤ/l ↪ μ_l）、(2) 外部生成元 ζ に写る内部座標は z≡1 (mod l) に
      **一意**（`thCyc_external_pin`, 捻れ不定性の消去）、(3) 交換子構造が中心生成元を
      **section 捻れの下で厳密固定**（`thCyc_cyclotomic_rigidity`, M11-5 の商版）、
      (4) mark 付き円分体の同型の一意性（`thCyc_marked_iso_unique`, M11-4b：ẑ^× 不定性が
      mark で消える離散核）。
    - 三剛性の束ね（`thCyc_three_rigidities`）は M323F 定数倍剛性（Laurent 環上）・
      M333F 離散剛性（Tate 曲線上・無限位数仮説付き）の既存 capstone をそのまま field と
      して参照する（過大主張しない）。
  全て選択公理不使用（新規 Classical.choice なし；商 Quot.sound は継承）。一般名は
  `thCyc` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.CyclotomicSync
import IUT.ThetaGroupMod
import IUT.EtaleTheta
import IUT.MonoThetaRigidity
import IUT.DiscreteRigidity

namespace IUT

/-! ## M338F-1: 内部円分体（テータ群の中心/交換子 ≅ ℤ/n）

  mono-theta 環境の内部円分体は、テータ（Heisenberg 型）群の**中心 = 交換子群**
  {(0,0,z)} である。標準生成元の交換子 [(1,0,0),(0,1,0)] = (0,0,1) がその生成元を
  標準指定し（M11 comm_xy / M98F theta_comm_mod）、中心は加法群 ℤ の準同型像で、
  mod-l 商では ℤ/l に一致する。 -/

/-- **M338F-1a: 内部円分体の生成元** — mod-l テータ群の中心生成元
    (0,0,1) の類（= 交換子 [(1,0,0),(0,1,0)] の類）。内部円分体 ⟨(0,0,1)⟩ の生成元。 -/
def thCycInternalGen (l : Nat) : (thetaGrpMod l).carrier :=
  (thetaRed l).map ((0, 0, 1) : thetaGrp.carrier)

/-- **定理 (M338F-1b): 交換子が内部円分体の生成元を与える** —
    標準生成元の交換子 [(1,0,0),(0,1,0)] = 内部円分体の生成元 (0,0,1)（M98F theta_comm_mod）。
    内部円分体が「テータ群の非可換性のすべて（交換子）」から標準的に生成されることの
    本物の根拠。 -/
theorem thCyc_comm_is_gen (l : Nat) :
    (thetaGrpMod l).comm
        ((thetaRed l).map ((1, 0, 0) : thetaGrp.carrier))
        ((thetaRed l).map ((0, 1, 0) : thetaGrp.carrier))
      = thCycInternalGen l :=
  theta_comm_mod l

/-- **M338F-1c: 内部円分体の ℤ-パラメトライズ** — 加法群 ℤ → mod-l テータ群、
    z ↦ (0,0,z) の類。中心 {(0,0,z)} が ℤ の準同型像であることの本物の群準同型
    （中心の Heisenberg 積 (0,0,z)·(0,0,z') = (0,0,z+z') が加法則を与える、
    M124F theta_center_mul）。 -/
def thCycInternalHom (l : Nat) : Hom intGrp (thetaGrpMod l) where
  map := fun z => (thetaRed l).map ((0, 0, z) : thetaGrp.carrier)
  map_mul := fun a b => by
    show (thetaRed l).map ((0, 0, a + b) : thetaGrp.carrier)
      = (thetaGrpMod l).mul ((thetaRed l).map ((0, 0, a) : thetaGrp.carrier))
          ((thetaRed l).map ((0, 0, b) : thetaGrp.carrier))
    rw [← (thetaRed l).map_mul, theta_center_mul]

/-- 内部円分体準同型は生成元 1 を内部生成元 (0,0,1) に送る（定義の確認）。 -/
theorem thCyc_internalHom_gen (l : Nat) :
    (thCycInternalHom l).map (1 : Int) = thCycInternalGen l := rfl

/-! ## M338F-2: 円分剛性の同型（内部円分体 ≅ 外部 μ_l、標準的・一意）

  内部円分体（テータ群中心の座標 z）と外部円分体 μ_l（1 の l 乗根の群、生成元 ζ）の
  同型は `centerToMu p l ζ : z ↦ ζ^{z mod l}`（M124F）で与えられる。これが準同型・
  生成元 ↦ 生成元・忠実（核 = lℤ, ℤ/l ↪ μ_l）であることに加え、**外部生成元 ζ に
  写る内部座標が z≡1 (mod l) に一意**（ℤ/l^× 捻れの不定性が生き残らない）ことを本物で示す。 -/

/-- **M338F-2a: 円分剛性の同型** — 内部円分体の座標 z を外部 μ_l の元 ζ^{z mod l} に
    送る標準同型（M124F centerToMu）。IUT の cyclotomic rigidity の主対象。 -/
def thCycRigIso (p l : Nat) (ζ : (Zp p).carrier) (z : Int) : (Zp p).carrier :=
  centerToMu p l ζ z

/-- **定理 (M338F-2b): 同型の準同型性** — centerToMu(z+z') = centerToMu z · centerToMu z'
    （M124F centerToMu_add）。内部円分体の加法（中心の Heisenberg 積）を μ_l の積に送る。 -/
theorem thCyc_rigIso_hom (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) (z z' : Int) :
    thCycRigIso p l ζ (z + z')
      = zpMul p (thCycRigIso p l ζ z) (thCycRigIso p l ζ z') :=
  centerToMu_add p l hl ζ hζl z z'

/-- **定理 (M338F-2c: 標準性・生成元 ↦ 生成元)** — 内部円分体の生成元（座標 1、
    交換子 (0,0,1)）は外部 μ_l の生成元 ζ に写る（M124F centerToMu_one_gen）。
    同型が ζ^× 捻れなしに **mark（生成元）を保つ**ことの本物の核。 -/
theorem thCyc_rigIso_gen (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    thCycRigIso p l ζ 1 = ζ :=
  centerToMu_one_gen p l hl ζ

/-- **定理 (M338F-2d): 同型の忠実性** — centerToMu z = 1 なら l ∣ z（M124F centerToMu_faithful）。
    核がちょうど lℤ、すなわち内部円分体 ℤ/l が外部 μ_l に**単射に埋め込まれる**（同型）。 -/
theorem thCyc_rigIso_faithful (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (z : Int) (hz : thCycRigIso p l ζ z = zpOne p) :
    ((l : Nat) : Int) ∣ z :=
  centerToMu_faithful p l hl ζ hdist z hz

/-- **M338F-2e: μ_l 冪の指数単射性** — ζ^a = ζ^b（a,b < l）なら a = b。冪の相異性
    hdist（0..l−1 の冪が相異）の対偶を三分律で回す。円分剛性の外部捻れ消去の核。 -/
theorem thCyc_zpPow_inj (p l : Nat) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (a b : Nat) (ha : a < l) (hb : b < l)
    (h : zpPow p ζ a = zpPow p ζ b) : a = b := by
  cases Nat.lt_trichotomy a b with
  | inl hlt => exact absurd h (hdist a b hlt hb)
  | inr h2 =>
    cases h2 with
    | inl heq => exact heq
    | inr hgt => exact absurd h.symm (hdist b a hgt ha)

/-- **M338F-2f: ζ^1 = ζ** — 冪の 1 乗（zpPow_succ + zpPow_zero + 単位律）。 -/
theorem thCyc_zpPow_one (p : Nat) (ζ : (Zp p).carrier) : zpPow p ζ 1 = ζ := by
  show zpPow p ζ (0 + 1) = ζ
  rw [zpPow_succ p ζ 0, zpPow_zero p ζ]
  exact zpOne_mul p ζ

/-- **定理 (M338F-2g): 外部生成元への一意ピン（円分剛性の本丸・外部側）** —
    外部 μ_l の生成元 ζ に写る内部円分体の座標は z ≡ 1 (mod l) に**一意**、すなわち
    l ∣ z − 1。centerToMu z = ζ = centerToMu 1 で両辺を μ_l の冪に開き、指数単射性
    （M338F-2e）で余りを 1 に固定する。**内部円分体の生成元と外部 μ_l の生成元 ζ を
    貼り合わせる同型は ℤ/l^× の非自明な捻れを許さない**——これが cyclotomic rigidity が
    消去する「シクロトーム捻れ不定性」の本物の消去。 -/
theorem thCyc_external_pin (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (z : Int) (hz : thCycRigIso p l ζ z = ζ) :
    ((l : Nat) : Int) ∣ z - 1 := by
  have hb : (0 : Int) < ((l : Nat) : Int) := by omega
  have h0 : 0 ≤ z % ((l : Nat) : Int) := Int.emod_nonneg z (by omega)
  have hlt : z % ((l : Nat) : Int) < ((l : Nat) : Int) := Int.emod_lt_of_pos z hb
  have htn : ((z % ((l : Nat) : Int)).toNat : Int) = z % ((l : Nat) : Int) :=
    Int.toNat_of_nonneg h0
  -- centerToMu z = ζ^{(z%l).toNat} = ζ = ζ^1
  have heq : zpPow p ζ (z % ((l : Nat) : Int)).toNat = zpPow p ζ 1 := by
    show thCycRigIso p l ζ z = zpPow p ζ 1
    rw [hz]
    exact (thCyc_zpPow_one p ζ).symm
  have hetn : (z % ((l : Nat) : Int)).toNat < l := by omega
  have h1l : (1 : Nat) < l := by omega
  have hee : (z % ((l : Nat) : Int)).toNat = 1 :=
    thCyc_zpPow_inj p l ζ hdist (z % ((l : Nat) : Int)).toNat 1 hetn h1l heq
  have hz1 : z % ((l : Nat) : Int) = 1 := by omega
  refine ⟨z / ((l : Nat) : Int), ?_⟩
  have hdiv := Int.mul_ediv_add_emod z ((l : Nat) : Int)
  rw [hz1] at hdiv
  omega

/-! ## M338F-3: 交換子構造による中心生成元の剛性（section 捻れ不定性の消去） -/

/-- **M338F-3a: section 捻れ仮説（正直な外部入力）** — mono-theta 環境の自己準同型 σ が
    標準生成元 (1,0,0),(0,1,0) を**中心（テータ切断）捻れ z₁,z₂ を除いて保つ**という
    性質。tempered π₁^ét から来る自己同型がこの形を取ることは柱E/D 後続の外部入力であり、
    **本層はこれを明示の Prop 仮説として受け、決して自前で導出しない**。 -/
def thCyc_section_twist_hypothesis (l : Nat)
    (σ : Hom (thetaGrpMod l) (thetaGrpMod l)) : Prop :=
  ∃ z₁ z₂ : Int,
    σ.map ((thetaRed l).map ((1, 0, 0) : thetaGrp.carrier))
        = (thetaRed l).map ((1, 0, z₁) : thetaGrp.carrier)
    ∧ σ.map ((thetaRed l).map ((0, 1, 0) : thetaGrp.carrier))
        = (thetaRed l).map ((0, 1, z₂) : thetaGrp.carrier)

/-- **定理 (M338F-3b): 円分剛性（本丸・内部側）** — section 捻れ仮説の下で、σ は内部円分体の
    生成元 (0,0,1) を**厳密に固定**する。テータ切断の不定性 (z₁,z₂) は交換子を通過する際に
    完全に相殺し、内部円分体（シクロトーム）には到達しない（M11-5 / M98F の商版
    mono_theta_cyclotomic_rigidity_mod）。**mono-theta 環境が内部円分体を剛性化する**
    ことの本物の内容: 内部円分体の生成元は section 捻れに依らず標準的。 -/
theorem thCyc_cyclotomic_rigidity (l : Nat)
    (σ : Hom (thetaGrpMod l) (thetaGrpMod l))
    (htw : thCyc_section_twist_hypothesis l σ) :
    σ.map (thCycInternalGen l) = thCycInternalGen l := by
  obtain ⟨z₁, z₂, hx, hy⟩ := htw
  exact mono_theta_cyclotomic_rigidity_mod l σ z₁ z₂ hx hy

/-- **定理 (M338F-3c): mark 付き円分体の同型の一意性（ẑ^× 不定性の消去核）** —
    裸の（離散）円分体 ℤ の自己準同型は ±1 の不定性を持つ（M11-3）が、生成元（mark）を
    保つ二つの同型は**一致**する（M11-4b marked_iso_unique）。内部円分体を μ_l と貼り合わせる
    「標準生成元 ↦ ζ」の mark が付いた同型は一意——cyclotomic rigidity が消去する
    ẑ^×-捻れ不定性が、交換子が供給する mark（M338F-3b）の下で消える離散核。 -/
theorem thCyc_marked_iso_unique (f g : Hom intGrp intGrp)
    (hf : f.map 1 = 1) (hg : g.map 1 = 1) :
    ∀ n : Int, f.map n = g.map n :=
  marked_iso_unique f g hf hg

/-! ## M338F-4: 総括レコード（円分剛性データ）と存在 -/

/-- **M338F-4a: テータ円分剛性データ** — 内部円分体（交換子/中心の生成元）・外部 μ_l との
    標準同型 centerToMu（準同型・生成元 ↦ ζ・忠実）・外部生成元への一意ピン（ℤ/l^× 捻れの
    消去）・交換子による中心生成元の section 捻れ下での厳密固定を一括束ね。三剛性の 3 つ目
    ＝**円分剛性**の witness 形。主語は本物の（離散 Heisenberg）テータ群中心と本物の μ_l 冪。 -/
structure ThetaCyclotomicRigidityData (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) where
  /-- 内部円分体の生成元 (0,0,1)（= 交換子の類）。 -/
  internalGen : (thetaGrpMod l).carrier
  /-- 内部生成元は交換子 [(1,0,0),(0,1,0)] に一致。 -/
  comm_gen : (thetaGrpMod l).comm
      ((thetaRed l).map ((1, 0, 0) : thetaGrp.carrier))
      ((thetaRed l).map ((0, 1, 0) : thetaGrp.carrier)) = internalGen
  /-- 円分剛性の同型 内部座標 z ↦ 外部 μ_l の ζ^{z mod l}。 -/
  rigIso : Int → (Zp p).carrier
  /-- 同型は centerToMu。 -/
  rigIso_def : ∀ z, rigIso z = centerToMu p l ζ z
  /-- 準同型性: rigIso(z+z') = rigIso z · rigIso z'。 -/
  rigIso_hom : ∀ z z', rigIso (z + z') = zpMul p (rigIso z) (rigIso z')
  /-- 生成元 ↦ 生成元: rigIso 1 = ζ（mark を保つ）。 -/
  rigIso_gen : rigIso 1 = ζ
  /-- 忠実性: rigIso z = 1 なら l ∣ z（ℤ/l ↪ μ_l）。 -/
  rigIso_faithful : ∀ z, rigIso z = zpOne p → ((l : Nat) : Int) ∣ z
  /-- 外部生成元 ζ への一意ピン: rigIso z = ζ なら z ≡ 1 (mod l)（ℤ/l^× 捻れの消去）。 -/
  external_pin : ∀ z, rigIso z = ζ → ((l : Nat) : Int) ∣ z - 1
  /-- 交換子による中心生成元の剛性: section 捻れ仮説の下で σ は内部生成元を固定。 -/
  rigidity : ∀ (σ : Hom (thetaGrpMod l) (thetaGrpMod l)),
      thCyc_section_twist_hypothesis l σ → σ.map internalGen = internalGen

/-- **M338F-4b: witness 本体** — 各フィールドを M338F-1〜3 の主定理で埋める。 -/
def thetaCyclotomicRigidityData (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) :
    ThetaCyclotomicRigidityData p l hl ζ hζl hdist where
  internalGen := thCycInternalGen l
  comm_gen := thCyc_comm_is_gen l
  rigIso := thCycRigIso p l ζ
  rigIso_def := fun _ => rfl
  rigIso_hom := fun z z' => thCyc_rigIso_hom p l hl ζ hζl z z'
  rigIso_gen := thCyc_rigIso_gen p l hl ζ
  rigIso_faithful := fun z hz => thCyc_rigIso_faithful p l hl ζ hdist z hz
  external_pin := fun z hz => thCyc_external_pin p l hl ζ hdist z hz
  rigidity := fun σ htw => thCyc_cyclotomic_rigidity l σ htw

/-- **定理 (M338F-4c): テータ円分剛性データの存在（M338F 見出し）** — 外部 μ_l の生成元 ζ
    （ζ^l=1・冪の相異性）が与えられれば、内部円分体（テータ群の交換子/中心）と外部 μ_l の
    標準同型・外部生成元への一意ピン（ℤ/l^× 捻れの消去）・交換子による中心生成元の剛性を
    束ねた円分剛性データが存在する。mono-theta 環境の三剛性の 3 つ目「円分剛性」が本物で
    確立される。 -/
theorem thCyc_exists (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) :
    Nonempty (ThetaCyclotomicRigidityData p l hl ζ hζl hdist) :=
  ⟨thetaCyclotomicRigidityData p l hl ζ hζl hdist⟩

/-! ## M338F-5: 三剛性の束ね（capstone） -/

/-- **定理 (M338F-5: 三剛性の束ね)** — mono-theta 環境の**三剛性**を一括で確立する:
    (1) **定数倍剛性**（M323F, Laurent 環上のテータ値の比が定数倍不定性の下で一意）、
    (2) **離散剛性**（M333F, Tate 曲線の周期格子 q^ℤ ≅ ℤ の離散性・無限位数仮説付き）、
    (3) **円分剛性**（本層 M338F, 内部円分体 ≅ 外部 μ_l が標準的・ℤ/l^× 捻れなし）。
    三剛性が揃うことが [EtTh] のテータ値の Hodge 劇場間の比較（円分捻れ不定性なし）の核。
    (1)(2) は既存 capstone（mThRig_exists / discRig_exists）をそのまま参照する。 -/
theorem thCyc_three_rigidities
    (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) :
    Nonempty (MonoThetaRigidityData R)
    ∧ Nonempty (DiscreteRigidityData K)
    ∧ Nonempty (ThetaCyclotomicRigidityData p l hl ζ hζl hdist) :=
  ⟨mThRig_exists R, discRig_exists K q hInf, thCyc_exists p l hl ζ hζl hdist⟩

/-! ## M338F-6: 実例 -/

/-- 実例: 内部円分体の生成元は交換子 [(1,0,0),(0,1,0)] の類（標準生成元の交換子）。 -/
example (l : Nat) :
    (thetaGrpMod l).comm
        ((thetaRed l).map ((1, 0, 0) : thetaGrp.carrier))
        ((thetaRed l).map ((0, 1, 0) : thetaGrp.carrier))
      = thCycInternalGen l :=
  thCyc_comm_is_gen l

/-- 実例: 円分剛性の同型は内部生成元（座標 1）を外部 μ_l の生成元 ζ に送る。 -/
example (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    thCycRigIso p l ζ 1 = ζ :=
  thCyc_rigIso_gen p l hl ζ

/-- 実例: 外部生成元 ζ に写る内部座標は z ≡ 1 (mod l) に一意（ℤ/l^× 捻れの消去）。 -/
example (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (z : Int) (hz : thCycRigIso p l ζ z = ζ) :
    ((l : Nat) : Int) ∣ z - 1 :=
  thCyc_external_pin p l hl ζ hdist z hz

/-- 実例: 本物の μ_l(ℤ_p)（M121F）から円分剛性データが存在する（p 素数・l = 2L+1 ∣ p−1）。 -/
theorem thCyc_mu_l_exists (p l L : Nat) (hp : IsPrime p) (hl : 2 ≤ l)
    (hLodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) :
    ∃ (ζ : (Zp p).carrier) (hζl : zpPow p ζ l = zpOne p)
      (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j),
      Nonempty (ThetaCyclotomicRigidityData p l hl ζ hζl hdist) := by
  obtain ⟨ζ, hζl, hdist, _⟩ := mu_l_zp_exists p l hp (by omega) hdvd
  exact ⟨ζ, hζl, hdist, thCyc_exists p l hl ζ hζl hdist⟩

end IUT
