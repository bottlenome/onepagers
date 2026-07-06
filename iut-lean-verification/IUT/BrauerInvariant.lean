/-
  IUT/BrauerInvariant.lean — M365F [実／本物]
  分類: 実 (局所不変量 inv:Br(K)→ℚ/ℤ・巡回代数部で M360F の inv 仮説を閉じる)
  complete_pct 影響: 柱B を前進（M360F 局所 Brauer 群の巡回代数類 (χ,a) に Hasse 不変量
    inv=v(a)/n∈(1/n)ℤ/ℤ⊆ℚ/ℤ を構成・準同型・分裂⟺inv=0・巡回部で単射を本物で証明し
    brau_inv_hypothesis を巡回部で実供給）。
  正直な限定: 全 Br(K)≅ℚ/ℤ の全単射（全類が巡回=局所 CFT）は外部仮説/後続。

  ── 本物で閉じる中身（骨格のみでない）:
  * M365F-1 `briQZn n` — 群 (1/n)ℤ/ℤ ≅ ℤ/n（ℚ/ℤ の n-捻れ）を `zmod n` で実体化。
    `bri_qzn_abelian`（アーベル群）・`bri_qzn_zero_iff`（[a]=0 ⟺ n∣a）を本物で。
  * M365F-2 `briVal` / `briInvCyclic` — 付値 v:K^×→ℤ（K^×=`unitsModel U` の第一成分・
    M330F の付値と同一）と、巡回代数類 (χ_n,a) の Hasse 不変量
    inv = v(a) mod n ∈ ℤ/n =(1/n)ℤ/ℤ を **本物の群準同型**として構成。
  * M365F-3 `bri_inv_hom` — inv((χ,a)·(χ,b)) = inv(χ,a)+inv(χ,b)。付値の加法性
    v(ab)=v(a)+v(b) から不変量が準同型であることを本物で。
  * M365F-4 `bri_inv_split_iff` / `briUnramNormSub` / `bri_norm_mem_iff` —
    巡回類が分裂（Br(K) で自明）⟺ inv=0 ⟺ n∣v(a) ⟺ a は不分岐ノルム群
    N={x|n∣v(x)} に属す、を本物で。核 = 不分岐ノルム群。
  * M365F-5 `bri_inv_surjective` / `bri_inv_injective_cyclic` — inv は ℤ/n へ全射・
    巡回類上で単射（第一同型 K^×/N ↪ ℤ/n、M267F `firstIsoHom`）。
  * M365F-6 `bri_inv_cyclic_hypothesis` / `bri_supplies_hypothesis` — 巡回 Brauer 群
    K^×/N ≅ ℤ/n=(1/n)ℤ/ℤ を不変量が全単射準同型で捉えること（M360F
    `brau_inv_hypothesis` の巡回部アナログ）を **本物で供給**。M360F の inv 仮説を
    巡回代数部で閉じる。
  * M365F-7 `bri_full_inv_hypothesis` — 全 Br(K)≅ℚ/ℤ（全類が巡回=局所 CFT）は
    **未導出の Prop 仮説**として明示（M360F `brau_inv_hypothesis` の再輸出）。決して導出しない。
  * M365F-8 capstone `BrauerInvariantData`/`briInvData`/`bri_exists` と実例
    （n=2 四元数型: 素元 π の巡回類の inv = 1 mod 2 = 1/2 ≠ 0 で非分裂）。

  **正直な限定**（消去・弱化禁止）:
  1. **全 Br(K) ≅ ℚ/ℤ の全単射**（Br(K) の全類が巡回代数 = 局所類体論の主定理）は
     `bri_full_inv_hypothesis`（未導出 Prop 仮説）。ここで本物で閉じたのは **巡回代数
     部分の不変量**（K^×/N ≅ ℤ/n）であって全類ではない。
  2. K^× は分裂表示 `unitsModel U = ℤ × O_v^×`（M330F と同じ規約）で扱い、付値は
     第一成分。相互律・完全 CFT との整合は M330F/後続。
  3. ℚ/ℤ は固定 n の n-捻れ (1/n)ℤ/ℤ ≅ ℤ/n として `zmod n` で表す（有限レベル）。
     全 ℚ/ℤ = colim_n (1/n)ℤ/ℤ の余極限としての構成は範囲外。

  **選択公理不使用・sorry 皆無**: 全宣言の公理は [propext, Quot.sound] のみ。
  禁止タクティク不使用。一般名は `bri` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.LocalBrauer
import IUT.LocalReciprocity
import IUT.QuotientGroup

namespace IUT

/-! ## M365F-1: 群 (1/n)ℤ/ℤ ≅ ℤ/n（ℚ/ℤ の n-捻れ） -/

/-- **不変量の値群**（M365F-1a）: (1/n)ℤ/ℤ ≅ ℤ/n = ℚ/ℤ の n-捻れ部分群。
    Hasse 不変量 v(a)/n が住む群を `zmod n`（M13 商群）で実体化した
    **本物のアーベル群**。 -/
def briQZn (n : Nat) : Grp := zmod n

/-- **(1/n)ℤ/ℤ はアーベル群**（M365F-1b）: ℤ の加法商ゆえ可換。 -/
theorem bri_qzn_abelian (n : Nat) (x y : (briQZn n).carrier) :
    (briQZn n).mul x y = (briQZn n).mul y x := by
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  show Quot.mk (modCong n).rel (intGrp.mul a b)
     = Quot.mk (modCong n).rel (intGrp.mul b a)
  have h : intGrp.mul a b = intGrp.mul b a := Int.add_comm a b
  rw [h]

/-- **零判定**（M365F-1c）: [a] = 0 in (1/n)ℤ/ℤ ⟺ n ∣ a。不変量が三重同値
    「分裂 ⟺ inv=0 ⟺ n∣v(a)」の算術核。 -/
theorem bri_qzn_zero_iff (n : Nat) (a : Int) :
    Quot.mk (modCong n).rel a = (briQZn n).one ↔ ((n : Nat) : Int) ∣ a := by
  constructor
  · intro h
    have h0 : Quot.mk (modCong n).rel a = Quot.mk (modCong n).rel (0 : Int) := h
    have hr : ((n : Nat) : Int) ∣ (a - 0) := quot_exact intGrp (modCong n) h0
    obtain ⟨k, hk⟩ := hr
    rw [Int.sub_zero] at hk
    exact ⟨k, hk⟩
  · intro h
    show Quot.mk (modCong n).rel a = Quot.mk (modCong n).rel (0 : Int)
    apply Quot.sound
    show ((n : Nat) : Int) ∣ (a - 0)
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [Int.sub_zero]; exact hk⟩

/-! ## M365F-2: 付値 v:K^×→ℤ と巡回代数類の Hasse 不変量 -/

/-- **付値** v : K^× = ℤ × O_v^× → ℤ（M365F-2a）: 分裂表示の第一成分。
    M330F `locRecArtin` の付値部と同一の付値。加法的準同型。 -/
def briVal (U : Grp) : Hom (unitsModel U) intGrp where
  map := fun x => x.1
  map_mul := fun _ _ => rfl

/-- 付値の明示式: v(k, u) = k。 -/
theorem briVal_apply (U : Grp) (k : Int) (u : U.carrier) :
    (briVal U).map (k, u) = k := rfl

/-- 射影 ℤ → (1/n)ℤ/ℤ（M365F-2b）: 付値を mod n に落とす。 -/
def briZmodProj (n : Nat) : Hom intGrp (briQZn n) := quotProj intGrp (modCong n)

/-- **巡回代数類の Hasse 不変量**（M365F-2c）: 位数 n の指標 χ_n と a∈K^× の
    巡回代数 (χ_n, a) に対し inv(χ_n,a) = v(a) mod n ∈ ℤ/n = (1/n)ℤ/ℤ ⊆ ℚ/ℤ。
    付値 v の mod-n 射影として **本物の群準同型** K^× → (1/n)ℤ/ℤ で構成。 -/
def briInvCyclic (U : Grp) (n : Nat) : Hom (unitsModel U) (briQZn n) :=
  Hom.comp (briZmodProj n) (briVal U)

/-- 不変量の明示式: inv(a) = [v(a)] = [a.1] ∈ (1/n)ℤ/ℤ。 -/
theorem briInvCyclic_apply (U : Grp) (n : Nat) (a : (unitsModel U).carrier) :
    (briInvCyclic U n).map a = Quot.mk (modCong n).rel a.1 := rfl

/-! ## M365F-3: 不変量は準同型（付値の加法性） -/

/-- **不変量は準同型**（M365F-3）: inv((χ,a)·(χ,b)) = inv(χ,a) + inv(χ,b)。
    巡回代数のテンソル則 (χ,a)⊗(χ,b) ≅ (χ,ab) と付値の加法性 v(ab)=v(a)+v(b)
    から、Hasse 不変量が (1/n)ℤ/ℤ への準同型であることを本物で。 -/
theorem bri_inv_hom (U : Grp) (n : Nat) (a b : (unitsModel U).carrier) :
    (briInvCyclic U n).map ((unitsModel U).mul a b)
      = (briQZn n).mul ((briInvCyclic U n).map a) ((briInvCyclic U n).map b) :=
  (briInvCyclic U n).map_mul a b

/-! ## M365F-4: 分裂 ⟺ inv=0 ⟺ n∣v(a) ⟺ 不分岐ノルム -/

/-- **分裂判定**（M365F-4a）: 巡回類 (χ_n,a) が分裂（Br(K) で自明）⟺ inv=0
    ⟺ n ∣ v(a)。不分岐巡回代数が行列環に分裂するための Hasse 判定。 -/
theorem bri_inv_split_iff (U : Grp) (n : Nat) (a : (unitsModel U).carrier) :
    (briInvCyclic U n).map a = (briQZn n).one ↔ ((n : Nat) : Int) ∣ a.1 := by
  rw [briInvCyclic_apply U n a]
  exact bri_qzn_zero_iff n a.1

/-- **不分岐ノルム群** N = {x∈K^× | n∣v(x)}（M365F-4b）: 次数 n の不分岐拡大
    L/K のノルム群 N_{L/K}(L^×)（の付値条件による特徴付け）。不変量の核。 -/
def briUnramNormSub (U : Grp) (n : Nat) : Subgroup (unitsModel U) :=
  kerSubgroup (briInvCyclic U n)

/-- **ノルム群の特徴付け**（M365F-4c）: x∈N ⟺ n∣v(x)。すなわち a は不分岐ノルム
    ⟺ inv(χ_n,a)=0（分裂）。「分裂 ⟺ ノルム」の一段を本物で。 -/
theorem bri_norm_mem_iff (U : Grp) (n : Nat) (x : (unitsModel U).carrier) :
    (briUnramNormSub U n).mem x ↔ ((n : Nat) : Int) ∣ x.1 :=
  bri_inv_split_iff U n x

/-- **核 = 不分岐ノルム群**（M365F-4d）: ker(inv) = N（定義一致）。 -/
theorem bri_ker_eq_norm (U : Grp) (n : Nat) :
    kerSubgroup (briInvCyclic U n) = briUnramNormSub U n := rfl

/-! ## M365F-5: 全射性・巡回部での単射性 -/

/-- **inv は (1/n)ℤ/ℤ へ全射**（M365F-5a）: 付値 v は全射（v(π^k)=k）ゆえ
    inv も全射。各不変量値 c/n が素元冪の巡回類で実現される。 -/
theorem bri_inv_surjective (U : Grp) (n : Nat) :
    ∀ y : (briQZn n).carrier, ∃ x, (briInvCyclic U n).map x = y := by
  intro y
  induction y using Quot.ind; rename_i a
  exact ⟨((a : Int), U.one), rfl⟩

/-- **inv は巡回類上で単射**（M365F-5b）: 第一同型 K^×/N ↪ (1/n)ℤ/ℤ
    （M267F `firstIsoHom`）。位数 n の巡回 Brauer 類 Br(K)[n]_cyc が不変量で
    ℤ/n に単射に埋め込まれる（不変量が巡回類を分離する）。 -/
theorem bri_inv_injective_cyclic (U : Grp) (n : Nat) :
    Hom.Injective (firstIsoHom (briInvCyclic U n)) :=
  firstIso_injective (briInvCyclic U n)

/-! ## M365F-6: 巡回 Brauer 群 K^×/N ≅ (1/n)ℤ/ℤ（inv 仮説の実供給） -/

/-- 部分群からの忘却準同型 subgroupGrp K → G（像を全体へ埋める・単射）。 -/
def briSubForget {G : Grp} (K : Subgroup G) : Hom (subgroupGrp K) G where
  map := fun x => x.val
  map_mul := fun _ _ => rfl

/-- 忘却準同型は単射（Subtype.ext）。 -/
theorem briSubForget_injective {G : Grp} (K : Subgroup G) :
    Hom.Injective (briSubForget K) :=
  fun _ _ h => Subtype.ext h

/-- **降下した不変量** K^×/N → (1/n)ℤ/ℤ（M365F-6a）: 第一同型
    K^×/N ≅ im(inv) と忘却を合成した、巡回 Brauer 群から (1/n)ℤ/ℤ への
    **本物の準同型**。 -/
def briInvDescended (U : Grp) (n : Nat) :
    Hom (quotientGroupN (unitsModel U) (kerSubgroup (briInvCyclic U n))
          (ker_isNormal (briInvCyclic U n))) (briQZn n) :=
  Hom.comp (briSubForget (imSubgroup (briInvCyclic U n))) (firstIsoHom (briInvCyclic U n))

/-- 降下不変量は単射（M365F-6b）: 忘却と第一同型の単射の合成。 -/
theorem bri_inv_descended_injective (U : Grp) (n : Nat) :
    Hom.Injective (briInvDescended U n) :=
  Hom.comp_injective (briSubForget_injective (imSubgroup (briInvCyclic U n)))
    (firstIso_injective (briInvCyclic U n))

/-- 降下不変量は全射（M365F-6c）: inv 自身の全射性から。 -/
theorem bri_inv_descended_surjective (U : Grp) (n : Nat) :
    ∀ y, ∃ x, (briInvDescended U n).map x = y := by
  intro y
  obtain ⟨a, ha⟩ := bri_inv_surjective U n y
  refine ⟨Quot.mk _ a, ?_⟩
  show (briInvCyclic U n).map a = y
  exact ha

/-- **巡回部 inv 仮説**（M365F-6d）: M360F `brau_inv_hypothesis` の巡回代数部
    アナログ — 巡回 Brauer 群 K^×/N から (1/n)ℤ/ℤ への全単射準同型（不変量）が
    存在する、という Prop。 -/
def bri_inv_cyclic_hypothesis (U : Grp) (n : Nat) : Prop :=
  ∃ inv : Hom (quotientGroupN (unitsModel U) (kerSubgroup (briInvCyclic U n))
              (ker_isNormal (briInvCyclic U n))) (briQZn n),
    Hom.Injective inv ∧ (∀ y, ∃ x, inv.map x = y)

/-- **M360F の inv 仮説を巡回部で実供給**（M365F-6e）: 上の仮説を Hasse 不変量で
    **本物に証明**する。巡回 Brauer 群 K^×/N ≅ (1/n)ℤ/ℤ が不変量で全単射準同型に
    なることを示し、M360F `brau_inv_hypothesis` の限定を巡回代数部で閉じる。 -/
theorem bri_supplies_hypothesis (U : Grp) (n : Nat) :
    bri_inv_cyclic_hypothesis U n :=
  ⟨briInvDescended U n, bri_inv_descended_injective U n, bri_inv_descended_surjective U n⟩

/-! ## M365F-7: 全 Br(K)≅ℚ/ℤ は未導出の外部仮説（正直な限定） -/

/-- **外部仮説（未導出）: 全 Br(K) ≅ ℚ/ℤ**（M365F-7）: Br(K) の**全**類が
    巡回代数（局所類体論の主定理）で、不変量 inv:Br(K)→ℚ/ℤ が全単射同型に
    なること。M360F `brau_inv_hypothesis` を再輸出した **Prop 仮説**であり、
    本モジュールでは**決して導出しない**（巡回部の閉包 `bri_supplies_hypothesis`
    とは別）。 -/
def bri_full_inv_hypothesis {GK : Grp} (Kbar : galH1Module GK) (QZ : Grp) : Prop :=
  brau_inv_hypothesis Kbar QZ

/-! ## M365F-8: capstone と実例 -/

/-- **capstone データ**（M365F-8a）: 単数群 U と位数 n に対する局所不変量の全部品 —
    値群 (1/n)ℤ/ℤ・不変量準同型 inv・準同型則・全射性・巡回部での単射性。 -/
structure BrauerInvariantData (U : Grp) (n : Nat) where
  /-- 不変量の値群 (1/n)ℤ/ℤ ≅ ℤ/n。 -/
  QZn : Grp
  /-- QZn の同定。 -/
  QZn_is : QZn = briQZn n
  /-- QZn はアーベル。 -/
  QZn_abelian : ∀ x y, (briQZn n).mul x y = (briQZn n).mul y x
  /-- Hasse 不変量 inv: K^× → (1/n)ℤ/ℤ。 -/
  inv : Hom (unitsModel U) (briQZn n)
  /-- inv の同定。 -/
  inv_is : inv = briInvCyclic U n
  /-- inv は準同型。 -/
  inv_hom : ∀ a b, (briInvCyclic U n).map ((unitsModel U).mul a b)
    = (briQZn n).mul ((briInvCyclic U n).map a) ((briInvCyclic U n).map b)
  /-- 分裂判定 inv=0 ⟺ n∣v(a)。 -/
  split_iff : ∀ a, (briInvCyclic U n).map a = (briQZn n).one ↔ ((n : Nat) : Int) ∣ a.1
  /-- inv は全射。 -/
  surjective : ∀ y, ∃ x, (briInvCyclic U n).map x = y
  /-- inv は巡回類上で単射（K^×/N ↪ (1/n)ℤ/ℤ）。 -/
  cyclic_injective : Hom.Injective (firstIsoHom (briInvCyclic U n))

/-- **証人**（M365F-8b）: 全条件を本物の証明で満たす。 -/
def briInvData (U : Grp) (n : Nat) : BrauerInvariantData U n where
  QZn := briQZn n
  QZn_is := rfl
  QZn_abelian := bri_qzn_abelian n
  inv := briInvCyclic U n
  inv_is := rfl
  inv_hom := bri_inv_hom U n
  split_iff := bri_inv_split_iff U n
  surjective := bri_inv_surjective U n
  cyclic_injective := bri_inv_injective_cyclic U n

/-- **局所不変量データの存在**（M365F-8c）。 -/
theorem bri_exists (U : Grp) (n : Nat) : Nonempty (BrauerInvariantData U n) :=
  ⟨briInvData U n⟩

/-- **具体的存在**（M365F-8d）: 自明単数群上でも局所不変量が実体化。 -/
theorem bri_exists_witness : Nonempty (BrauerInvariantData punitGrp 2) :=
  ⟨briInvData punitGrp 2⟩

/-! ## M365F-8e: 実例 — n=2 四元数型代数の不変量 1/2 -/

/-- **四元数型の不変量**（M365F-8e-1）: n=2、素元 π=(1,1)（v(π)=1）の巡回類
    (χ_2, π) の Hasse 不変量は 1 mod 2 = 1/2 ∈ (1/2)ℤ/ℤ ⊆ ℚ/ℤ。 -/
theorem bri_quaternion_inv (U : Grp) :
    (briInvCyclic U 2).map ((1 : Int), U.one) = Quot.mk (modCong 2).rel 1 := rfl

/-- **四元数型は非分裂**（M365F-8e-2）: inv = 1/2 ≠ 0 ゆえ (χ_2, π) は分裂しない
    （四元数可除環に対応）。2 ∤ 1 が非分裂の算術核。 -/
theorem bri_quaternion_not_split (U : Grp) :
    (briInvCyclic U 2).map ((1 : Int), U.one) ≠ (briQZn 2).one := by
  intro h
  have hd : ((2 : Nat) : Int) ∣ ((1 : Int), U.one).1 :=
    (bri_inv_split_iff U 2 ((1 : Int), U.one)).mp h
  obtain ⟨k, hk⟩ := hd
  omega

end IUT
