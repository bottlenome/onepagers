-- M426F ArakelovClassDegree [実・本物・柱C]
-- complete_pct 影響: 柱C で Arakelov Picard 次数が類群に降りる（主因子不変性）・次数0類 Pic^0＝
--   コンパクト部を D̂ と Pic(D̂) の本物の部分群として建設・M406F Cl(K) の有限イデアル部が Pic^0 へ入る、を本物で。
-- 正直な限定: Pic^0 のコンパクト性（Minkowski 束・格子体積の有限性）・一般数体（K=ℚ 模型）は 後続。

/-
  IUT/ArakelovClassDegree.lean — M426F（柱C: Arakelov 類次数 / 次数0 類群 Pic^0）

  ── 主要成果の分類: **[実]**（本物の先行建設 (b) / 昇格 (a)）。M356F
     (`IUT/ArakelovDivisor.lean`, prefix `ard`) が Arakelov 因子群 D̂ = D_fin ⊕ D_∞・
     実次数 deg:D̂→ℝ（加法準同型）・主 Arakelov 因子の deg=0（`ard_principal_degree_zero`,
     `ard_deg_descends`）・Arakelov Picard 群 `ardPicard = D̂/im(div̂)` を建てた。本モジュールは
     その **次の本物の一手**——**Arakelov 類次数**（deg が Picard 類群 Pic(D̂) の上に降りること）と、
     **次数0 の Arakelov 類群 Pic^0**（コンパクト部）を、**D̂ の本物の部分群**・**Pic(D̂) の本物の
     部分群**として core Lean のみで完全証明する。toy 主語なし——主語は M356F の本物の Arakelov
     因子群 D̂・実次数 deg・実積公式による主因子 deg=0 である。

  complete_pct 影響: **柱C（Frobenioid／Arakelov 類群）の実 IUT 完全証明率を前進させる**。
  M356F は「deg が主因子で消える」ところまでだった。本ファイルは:
  (1) **次数0 Arakelov 因子部分群 D̂^0 ⊆ D̂**（`acdDegZeroSub`）——deg(D)≈0 の因子全体。
      one/mul/inv の閉性を M356F の deg 加法準同型・deg(0̂)=0 から本物で証明（deg の核）。
  (2) **deg は Picard 類群の上に降りる**（`acd_degZero_class_invariant`）——主因子を足しても
      次数0 性は不変（M356F `ard_deg_descends` を類群 well-defined 性へ昇格）。
  (3) **主因子は D̂^0 に入る**（`acd_principal_subset_degZero`）——im(div̂) ⊆ D̂^0
      （主 Arakelov 因子の deg=0、M356F `ard_principalRaw_degree_zero`）。これが Pic^0 ⊆ Pic の核。
  (4) **次数0 Arakelov 類群 Pic^0**（`acdPic0Sub`）——Arakelov Picard 群 `ardPicard` の
      **本物の部分群**として、剰余類関係 cosetRel の上へ次数0 述語を Quot.lift で降ろして建設
      （well-defined 性 `acd_degZero_coset_wd` は「同一類なら次数が realEq」の本物の証明）。
  (5) **Pic^0 の核特徴付け**（`acd_pic0_iff_deg_zero`）——類 [D]∈Pic^0 ⟺ deg(D)≈0
      （完全列 0→Pic^0→Pic(D̂)→ℝ の Pic^0＝ker(deg) 部分の実体）。
  (6) **M406F Cl(K) との接続**（`acd_icg_idealGroup_image_in_degZero`）——M406F の分数イデアル群
      I(K)=`icgIdealGroup` を div̂ で D̂ へ送ると像は D̂^0 に入る（有限イデアル部が Pic^0 の
      算術的部分を占める）。
  (7) capstone `ArakelovClassDegreeData` / `acd_exists` / 実例。

  ## 検証する中核（全て sorry なし・新規 Classical.choice なし）
  * M426F-1 `acdDegZeroPred` / `acdDegZeroPred_wd` / `acdDegZeroMem`
              — 次数0 述語と ardEq 不変性（因子群 D̂=Quot ardEq の上への Prop lift）
  * M426F-2 `acd_degZero_class_invariant`
              — 主因子シフトで次数0 性不変（deg が類群に降りる本物の内容）
  * M426F-3 `acdDegZeroSub`
              — **次数0 Arakelov 因子部分群 D̂^0**（deg の核、本物の部分群）
  * M426F-4 `acd_principal_subset_degZero` / `acd_div_image_in_degZero`
              — im(div̂) ⊆ D̂^0（主因子は次数0）
  * M426F-5 `acd_degZero_coset_wd` / `acdPic0Mem` / `acdPic0Sub`
              — **次数0 Arakelov 類群 Pic^0**（Arakelov Picard 群の本物の部分群）
  * M426F-6 `acd_pic0_iff_deg_zero` / `acd_pic0_class_iff`
              — Pic^0 = ker(deg)（完全列の Pic^0 部分の核特徴付け）
  * M426F-7 `acd_icg_idealGroup_image_in_degZero`
              — M406F Cl(K) の分数イデアル部が Pic^0 へ（有限部の接続）
  * M426F-8 capstone `ArakelovClassDegreeData` / `arakelovClassDegreeData` /
    `acd_exists` / 実例 `acd_example_*`

  ## 正直な限定（消去/弱化禁止・地図として保持）
  - **本物（完全証明）**: D̂^0＝deg の核が D̂ の**部分群**であること・deg が主因子シフトで
    不変（類群 well-defined）・im(div̂) ⊆ D̂^0・Pic^0 が Arakelov Picard 群の**部分群**である
    こと・Pic^0=ker(deg) の核特徴付け・M406F 分数イデアル像が D̂^0 に入ること。全て K=ℚ 模型上で本物。
  - **正直申告（未達・後続）**:
    ・**deg はℝへの literal な準同型として取り出さない**。ℝ は setoid（realEq）ゆえ M356F 同様、
      deg は代表レベルの実数値関数として保ち、well-defined 性は realEq で述べる。次数写像を
      ℝ/realEq の商への literal Hom にするのは後続（RReal の商型の建設が要る）。
    ・**Pic^0 のコンパクト性**（Arakelov 類群の次数0 部分が有限体積の compact torus であること）は
      **範囲外**。コンパクト性は Minkowski 束・格子点計数・アデール類群の体積（幾何学的数論）を
      要すので後続。本ファイルは Pic^0 を**部分群**として建てる（有限性・体積・compact 性は主張しない）。
    ・**一般数体（K≠ℚ）**は範囲外（M356F と同じ K=ℚ 模型）。∞ 部は唯一のアルキメデス素点の
      実重み。複数無限素点・実/複素の重み配分は後続。
    ・**完全列 0→Pic^0→Pic→ℝ の全射性（deg の像がℝ全体）** は主張しない。核 Pic^0=ker(deg) と
      降下（well-defined）までを本物にする。全射性は archimedean 部の自由度から従うが体積/連続性入力を要すので後続。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・[propext, Quot.sound]）・sorry 皆無。
-/
import IUT.ArakelovDivisor
import IUT.IdealClassGroup

namespace IUT

/-! ## M426F-1: 次数0 述語と D̂=Quot ardEq の上への Prop lift -/

/-- **M426F-1a: 次数0 述語**（代表レベル）— Arakelov 因子代表 D が deg(D)≈0。
    Arakelov 類次数の核（compact 部 Pic^0）の因子レベル判定。 -/
def acdDegZeroPred (logp : Nat → RReal) (D : ardRaw) : Prop :=
  realEq (ardDeg logp D) realZero

/-- **M426F-1b: 次数0 述語の ardEq 不変性** — 等価な代表（ardEq）は同じ次数0 判定。
    M356F `ardDeg_wd`（deg は ardEq で well-defined）から propext で Prop 等式に。
    これにより述語が因子群 D̂=Quot ardEq の上に Quot.lift できる。 -/
theorem acdDegZeroPred_wd (logp : Nat → RReal) {D E : ardRaw} (h : ardEq D E) :
    acdDegZeroPred logp D = acdDegZeroPred logp E := by
  apply propext
  constructor
  · intro hD; exact realEq_trans (realEq_symm (ardDeg_wd logp h)) hD
  · intro hE; exact realEq_trans (ardDeg_wd logp h) hE

/-- **M426F-1c: 次数0 所属**（因子群 D̂ の上）— D̂=Quot ardEq の上へ次数0 述語を
    Quot.lift で降ろした本物の集合（deg の核の因子群レベル）。 -/
def acdDegZeroMem (logp : Nat → RReal) : ardGroup.carrier → Prop :=
  Quot.lift (acdDegZeroPred logp) (fun _ _ h => acdDegZeroPred_wd logp h)

/-! ## M426F-2: deg が Picard 類群に降りる（主因子シフトで次数0 不変） -/

/-- **M426F-2: 次数0 性は主因子シフトで不変** — deg(D + div̂(f)) ≈ deg(D)（M356F
    `ard_deg_descends`）ゆえ「D が次数0」⟺「D+div̂(f) が次数0」。これは**次数写像が
    Arakelov Picard 類群の上に降りる**（類の代表に依らず次数0 性が定まる）ことの本物の核。 -/
theorem acd_degZero_class_invariant (logp : Nat → RReal) (D : ardRaw) (f : RawDiv) :
    acdDegZeroPred logp (ardAdd D (ardPrincipalRaw logp f)) = acdDegZeroPred logp D := by
  apply propext
  have hdesc := ard_deg_descends logp D f
  constructor
  · intro h; exact realEq_trans (realEq_symm hdesc) h
  · intro h; exact realEq_trans hdesc h

/-! ## M426F-3: 次数0 Arakelov 因子部分群 D̂^0 ⊆ D̂（deg の核） -/

/-- **M426F-3: 次数0 Arakelov 因子部分群 D̂^0** — deg(D)≈0 の Arakelov 因子全体のなす
    **D̂ の本物の部分群**（次数写像 deg:D̂→ℝ の核）。
    ・one: deg(0̂)=0（M356F `ard_example_zero`）。
    ・mul: deg(D+E)≈deg D+deg E≈0+0≈0（M356F `ard_deg_hom` の核性）。
    ・inv: deg(D)+deg(−D)≈deg(D+(−D))≈0 かつ deg(D)≈0 ⟹ deg(−D)≈0（加法群での消去）。 -/
def acdDegZeroSub (logp : Nat → RReal) : Subgroup ardGroup where
  mem := acdDegZeroMem logp
  one_mem := ard_example_zero logp
  mul_mem := by
    intro a b ha hb
    revert ha hb
    induction a using Quot.ind; rename_i A
    induction b using Quot.ind; rename_i B
    intro ha hb
    show realEq (ardDeg logp (ardAdd A B)) realZero
    refine realEq_trans (ard_deg_hom logp A B) ?_
    refine realEq_trans (realAdd_congr_left (ardDeg logp B) ha) ?_
    refine realEq_trans (realAdd_comm realZero (ardDeg logp B)) ?_
    exact realEq_trans (realAdd_zero (ardDeg logp B)) hb
  inv_mem := by
    intro a ha
    revert ha
    induction a using Quot.ind; rename_i A
    intro ha
    show realEq (ardDeg logp (ardNeg A)) realZero
    -- deg(A + (−A)) ≈ 0（有限部零係数 + アルキメデス部の realAdd_neg）
    have hlv : realEq (logVolGlobal logp (rawAdd A.fin (rawNeg A.fin))) realZero :=
      logVolGlobal_zero_coeff logp (fun k => by
        show A.fin.coeff k + -(A.fin.coeff k) = 0
        omega)
    have hsum0 : realEq (ardDeg logp (ardAdd A (ardNeg A))) realZero := by
      show realEq (realAdd (logVolGlobal logp (rawAdd A.fin (rawNeg A.fin)))
          (realAdd A.arch (realNeg A.arch))) realZero
      refine realEq_trans
        (realAdd_congr_left (realAdd A.arch (realNeg A.arch)) hlv) ?_
      refine realEq_trans (realAdd_comm realZero (realAdd A.arch (realNeg A.arch))) ?_
      refine realEq_trans (realAdd_zero (realAdd A.arch (realNeg A.arch))) ?_
      exact realAdd_neg A.arch
    -- deg(A)+deg(−A) ≈ deg(A+(−A)) ≈ 0
    have hz : realEq (realAdd (ardDeg logp A) (ardDeg logp (ardNeg A))) realZero :=
      realEq_trans (realEq_symm (ard_deg_hom logp A (ardNeg A))) hsum0
    -- deg(A)≈0 ⟹ deg(A)+deg(−A) ≈ deg(−A)
    have hcong : realEq (realAdd (ardDeg logp A) (ardDeg logp (ardNeg A)))
        (ardDeg logp (ardNeg A)) := by
      refine realEq_trans (realAdd_congr_left (ardDeg logp (ardNeg A)) ha) ?_
      refine realEq_trans (realAdd_comm realZero (ardDeg logp (ardNeg A))) ?_
      exact realAdd_zero (ardDeg logp (ardNeg A))
    exact realEq_trans (realEq_symm hcong) hz

/-! ## M426F-4: 主因子は D̂^0 に入る（im(div̂) ⊆ D̂^0） -/

/-- **M426F-4a: 主 Arakelov 因子部分群 ⊆ 次数0 部分群** — im(div̂) ⊆ D̂^0。
    任意の主 Arakelov 因子は deg=0（M356F `ard_principalRaw_degree_zero`＝実積公式）
    ゆえ次数0 部分群に入る。これが Pic^0 = D̂^0/im(div̂) ⊆ Pic(D̂) を可能にする核。 -/
theorem acd_principal_subset_degZero (logp : Nat → RReal) (x : ardGroup.carrier)
    (hx : (ardPrincipalSub logp).mem x) : (acdDegZeroSub logp).mem x := by
  obtain ⟨y, hy⟩ := hx
  revert hy
  induction y using Quot.ind; rename_i f
  intro hy
  rw [← hy]
  show realEq (ardDeg logp (ardPrincipalRaw logp f)) realZero
  exact ard_principalRaw_degree_zero logp f

/-- **M426F-4b: div̂ の像は D̂^0 に入る** — 分数イデアル群 Div の任意元の主 Arakelov 因子
    div̂(x) は次数0（有限因子部が生む Arakelov 直線束の次数は 0）。 -/
theorem acd_div_image_in_degZero (logp : Nat → RReal) (x : picDivGrp.carrier) :
    (acdDegZeroSub logp).mem ((ardPrincipalHom logp).map x) :=
  acd_principal_subset_degZero logp _ ⟨x, rfl⟩

/-! ## M426F-5: 次数0 Arakelov 類群 Pic^0（Arakelov Picard 群の部分群） -/

/-- **M426F-5a: 次数0 所属は剰余類で well-defined** — 同一 Picard 類（cosetRel、
    a⁻¹b が主因子）なら次数0 性が一致。証明: a⁻¹b = div̂(f) から
    b ≡ a + div̂(f)（群法則）、`acdDegZeroMem` は D̂=Quot ardEq 上の関数ゆえ両辺で一致、
    さらに `acd_degZero_class_invariant`（主因子シフト不変）で a と一致。 -/
theorem acd_degZero_coset_wd (logp : Nat → RReal) (a b : ardGroup.carrier)
    (h : cosetRel ardGroup (ardPrincipalSub logp) a b) :
    acdDegZeroMem logp a = acdDegZeroMem logp b := by
  obtain ⟨y, hy⟩ := h
  revert hy
  induction a using Quot.ind; rename_i A
  induction b using Quot.ind; rename_i B
  induction y using Quot.ind; rename_i f
  intro hy
  -- hy : div̂(f) = a⁻¹·b（D̂ の元として）
  have key : Quot.mk ardEq (ardAdd A (ardPrincipalRaw logp f)) = Quot.mk ardEq B := by
    have h1 := congrArg (ardGroup.mul (Quot.mk ardEq A)) hy
    rw [← ardGroup.mul_assoc, ardGroup.mul_inv, ardGroup.one_mul] at h1
    exact h1
  exact Eq.trans (acd_degZero_class_invariant logp A f).symm
    (congrArg (acdDegZeroMem logp) key)

/-- **M426F-5b: 次数0 所属（Arakelov Picard 類群の上）** — Arakelov Picard 群
    `ardPicard = D̂/im(div̂)` の剰余類の上へ、次数0 述語を well-defined に降ろした集合。
    Arakelov 類次数 deg:Pic(D̂)→ℝ の核 Pic^0 の実体。 -/
def acdPic0Mem (logp : Nat → RReal) : (ardPicard logp).carrier → Prop :=
  Quot.lift (acdDegZeroMem logp) (fun a b h => acd_degZero_coset_wd logp a b h)

/-- **M426F-5c: 次数0 Arakelov 類群 Pic^0** — Arakelov Picard 群 `ardPicard` の
    **本物の部分群**（次数0 の類全体＝コンパクト部）。one/mul/inv は D̂^0（`acdDegZeroSub`）
    の閉性を剰余類の上へ持ち上げて得る。完全列 0→Pic^0→Pic(D̂)→ℝ の Pic^0=ker(deg)。 -/
def acdPic0Sub (logp : Nat → RReal) : Subgroup (ardPicard logp) where
  mem := acdPic0Mem logp
  one_mem := (acdDegZeroSub logp).one_mem
  mul_mem := by
    intro x y hx hy
    revert hx hy
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    intro hx hy
    exact (acdDegZeroSub logp).mul_mem hx hy
  inv_mem := by
    intro x hx
    revert hx
    induction x using Quot.ind; rename_i a
    intro hx
    exact (acdDegZeroSub logp).inv_mem hx

/-! ## M426F-6: Pic^0 = ker(deg)（核特徴付け・完全列の Pic^0 部分） -/

/-- **M426F-6a: Pic^0 の核特徴付け** — 因子 D の Picard 類 [D] が Pic^0 に入る
    ⟺ D が次数0 部分群 D̂^0 に入る（⟺ deg(D)≈0）。射影核が次数0 判定を保つこと
    （完全列 0→Pic^0→Pic(D̂)→ℝ での Pic^0=ker(deg) の実体）。 -/
theorem acd_pic0_iff_deg_zero (logp : Nat → RReal) (D : ardGroup.carrier) :
    (acdPic0Sub logp).mem
        ((quotientProjN ardGroup (ardPrincipalSub logp) (ardPrincipalNormal logp)).map D)
      ↔ (acdDegZeroSub logp).mem D :=
  Iff.rfl

/-- **M426F-6b: Pic^0 の核特徴付け（代表レベル）** — [D] ∈ Pic^0 ⟺ deg(D)≈0。 -/
theorem acd_pic0_class_iff (logp : Nat → RReal) (D : ardRaw) :
    (acdPic0Sub logp).mem
        ((quotientProjN ardGroup (ardPrincipalSub logp) (ardPrincipalNormal logp)).map
          (Quot.mk ardEq D))
      ↔ realEq (ardDeg logp D) realZero :=
  Iff.rfl

/-! ## M426F-7: M406F Cl(K) との接続（有限イデアル部が Pic^0 へ） -/

/-- **M426F-7: M406F 分数イデアル群 I(K) の像は D̂^0 に入る** — M406F の
    `icgIdealGroup = picDivGrp`（分数イデアル群）を div̂ で Arakelov 因子群へ送ると、
    像は次数0 部分群 D̂^0 に入る。すなわち**有限イデアル類（Cl(K) の算術的部分）は
    Arakelov 次数0 類 Pic^0 の中に座す**（有限部と Pic^0 の接続）。K=ℚ 模型では
    M406F `icg_pid_example` により Cl(ℤ)=0 ゆえ Pic^0 の有限部は自明で、Pic^0 は
    純粋にアルキメデス（compact）部から成る——という正直な地図。 -/
theorem acd_icg_idealGroup_image_in_degZero (logp : Nat → RReal)
    (x : icgIdealGroup.carrier) :
    (acdDegZeroSub logp).mem ((ardPrincipalHom logp).map x) :=
  acd_principal_subset_degZero logp _ ⟨x, rfl⟩

/-! ## M426F-8: capstone -/

/-- **M426F-8a: Arakelov 類次数データ** — Arakelov Picard 群 Pic(D̂)・次数0 因子部分群 D̂^0・
    次数0 類群 Pic^0・次数の降下（主因子不変）・主因子 ⊆ D̂^0・Pic^0=ker(deg) の束ね。 -/
structure ArakelovClassDegreeData (logp : Nat → RReal) where
  /-- Arakelov Picard 群 Pic(D̂) = D̂/im(div̂)（M356F）。 -/
  pic : Grp
  /-- 次数0 Arakelov 因子部分群 D̂^0 ⊆ D̂（deg の核）。 -/
  degZeroSub : Subgroup ardGroup
  /-- 次数0 Arakelov 類群 Pic^0 ⊆ Pic(D̂)（compact 部）。 -/
  pic0 : Subgroup (ardPicard logp)
  /-- deg は Picard 類群に降りる（主因子シフトで次数0 性不変）。 -/
  deg_descends : ∀ (D : ardRaw) (f : RawDiv),
    acdDegZeroPred logp (ardAdd D (ardPrincipalRaw logp f)) = acdDegZeroPred logp D
  /-- 主 Arakelov 因子は D̂^0 に入る（im(div̂) ⊆ D̂^0）。 -/
  principal_in_degZero : ∀ x, (ardPrincipalSub logp).mem x → degZeroSub.mem x
  /-- Pic^0 = ker(deg)（類 [D] ∈ Pic^0 ⟺ D ∈ D̂^0）。 -/
  pic0_iff : ∀ D : ardGroup.carrier,
    pic0.mem
        ((quotientProjN ardGroup (ardPrincipalSub logp) (ardPrincipalNormal logp)).map D)
      ↔ degZeroSub.mem D

/-- **M426F-8b: Arakelov 類次数データの witness**（全て本物）。 -/
def arakelovClassDegreeData (logp : Nat → RReal) : ArakelovClassDegreeData logp where
  pic := ardPicard logp
  degZeroSub := acdDegZeroSub logp
  pic0 := acdPic0Sub logp
  deg_descends := acd_degZero_class_invariant logp
  principal_in_degZero := acd_principal_subset_degZero logp
  pic0_iff := acd_pic0_iff_deg_zero logp

/-- **M426F-8c: 存在** — Arakelov 類次数データは充足可能（K=ℚ）。 -/
theorem acd_exists (logp : Nat → RReal) : Nonempty (ArakelovClassDegreeData logp) :=
  ⟨arakelovClassDegreeData logp⟩

/-! ## M426F-9: 実例 -/

/-- **M426F-9a: 実例（零因子は Pic^0 の核）** — 0̂ ∈ D̂^0（deg(0̂)=0）。 -/
theorem acd_example_zero_in_degZero (logp : Nat → RReal) :
    (acdDegZeroSub logp).mem ardGroup.one :=
  (acdDegZeroSub logp).one_mem

/-- **M426F-9b: 実例（主 Arakelov 因子は D̂^0）** — 任意の有限因子 f の主 Arakelov 因子
    ardPrincipalRaw(f) は次数0 部分群 D̂^0 に入る（deg=0＝実積公式）。 -/
theorem acd_example_principalRaw_in_degZero (logp : Nat → RReal) (f : RawDiv) :
    (acdDegZeroSub logp).mem (Quot.mk ardEq (ardPrincipalRaw logp f)) :=
  ard_principalRaw_degree_zero logp f

/-- **M426F-9c: 実例（自明類は Pic^0）** — Arakelov Picard 群の単位類は Pic^0 に入る。 -/
theorem acd_example_trivial_class_in_pic0 (logp : Nat → RReal) :
    (acdPic0Sub logp).mem (ardPicard logp).one :=
  (acdPic0Sub logp).one_mem

/-- **M426F-9d: 実例（x=2 の主因子類は Pic^0）** — 主 Arakelov 因子 div̂(2) の
    Picard 類は次数0（deg=log2+(−log2)=0）ゆえ Pic^0 に入る。 -/
theorem acd_example_two_class_in_pic0 (logp : Nat → RReal) :
    (acdPic0Sub logp).mem
      ((quotientProjN ardGroup (ardPrincipalSub logp) (ardPrincipalNormal logp)).map
        (Quot.mk ardEq (ardPrincipalRaw logp (pfSinglePrime 0 1).fin))) :=
  (acd_pic0_class_iff logp (ardPrincipalRaw logp (pfSinglePrime 0 1).fin)).mpr
    (ard_principalRaw_degree_zero logp (pfSinglePrime 0 1).fin)

end IUT
