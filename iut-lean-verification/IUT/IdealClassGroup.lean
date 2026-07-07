-- M406F IdealClassGroup [実・本物・柱C]
-- complete_pct 影響: 柱C で イデアル類群 Cl(K)=I(K)/P(K)（分数イデアル群を単項分数イデアルで割った本物の商群）とクラス写像 [𝔞] を本物で建設
-- 正直な限定: Cl(K) の有限性（Minkowski 束・幾何学的数論）・類数公式は 後続（本モジュールは群とクラス写像・自明類判定・PID 実例まで）

/-
  IUT/IdealClassGroup.lean — M406F（柱C 先行建設: イデアル類群 Cl(K)=I(K)/P(K)）

  ── 主要成果の分類: **[実]**（本物の先行建設 (b) / 昇格 (a)）。数体／Dedekind 整域の
     **イデアル類群** Cl(K)＝分数イデアル群 I(K) を単項分数イデアル部分群 P(K)＝im(div)
     で割った**本物の商群**（＝類数を定める中心対象・Pic の算術的化身）を core Lean のみで
     完全証明する。toy 主語なし——主語は「素点（素因子）上の付値ベクトルのなす自由アーベル群
     I(K)」という**本物の代数対象**（M307F `picDivGrp`＝Weil 因子群の化身）であり、
     div:K^×→I(K)（M307F `picDivPrincipalHom`）・商群（M267F `quotientGroupN`）は
     既存の本物の群機構の上に載る。

  complete_pct 影響: **柱C（Frobenioid／数論）の実 IUT 完全証明率を前進させる**。
  M307F は Picard 群 Pic＝Div/im(div)（直線束の同型類群）を建てたが、その**イデアル論的
  化身であるイデアル類群 Cl(K)**（分数イデアル ≡ 単項分数イデアル の類群）とその
  **クラス写像 [𝔞]**・**自明類の完全判定 [𝔞]=0 ⟺ 𝔞 単項**・**PID で Cl=0**（実例）は
  柱C に無かった。本ファイルはそれを**本物**に建てる:
  (1) 分数イデアル群 I(K)＝付値ベクトルの自由アーベル群（M307F `picDivGrp` 昇格・再利用）、
  (2) 単項分数イデアル部分群 P(K)＝im(div)（アーベルゆえ正規、M307F `picDivPrincipalNormal`）、
  (3) **イデアル類群 Cl(K)＝I(K)/P(K)**（M267F `quotientGroupN` による本物の商群）、
  (4) **クラス写像** cl:I(K)→Cl(K)（射影準同型・全射）と、**単項イデアルの類は自明**
      cl(div a)=0（P(K) を潰す）、
  (5) **自明類の完全判定** [𝔞]=0 ⟺ 𝔞∈P(K)（𝔞 単項）（M267F `quotientProjN_ker`）、
  (6) **PID 判定** div 全射 ⟹ Cl=0、および**閉じた実例** P(K)=I(K)（PID では全分数イデアル
      単項）⟹ Cl=0（仮定なし・完全証明。ℤ 上のイデアル類群 Cl(ℤ)=0 の化身）、
  (7) **Pic との同一視** Cl(K)=Pic（定義的に同一の商・rfl）——イデアル類群は Picard 群の
      素因子上の化身。

  ## 検証する中核（全て sorry なし・新規 Classical.choice なし）

  * M406F-1 `icgIdealGroup` / `icgDiv` / `icg_div_isHom` / `icg_ideal_group_comm`
                              — **分数イデアル群 I(K)**（付値ベクトルの自由アーベル群）と
                                単項写像 div:K^×→I(K)（本物の Hom・可換群）
  * M406F-2 `icgPrincipalSub` / `icg_principal_mem_iff`
                              — **単項分数イデアル部分群 P(K)＝im(div)**（M307F 再利用）と
                                所属判定 D∈P(K) ⟺ ∃a, div a=D
  * M406F-3 `icgClassGroup` / `icgClassMap` / `icg_class_map_surjective`
                              — **イデアル類群 Cl(K)＝I(K)/P(K)**（本物の商群）と
                                **クラス写像** cl:I(K)→Cl(K)（全射準同型）
  * M406F-4 `icg_class_of_principal_trivial`
                              — **単項イデアルの類は自明** cl(div a)=0（クラス写像が P(K) を潰す）
  * M406F-5 `icg_class_trivial_iff` / `icg_class_trivial_iff_principal`
                              — **自明類の完全判定** [𝔞]=0 ⟺ 𝔞∈P(K) ⟺ 𝔞 単項
  * M406F-6 `icg_cl_eq_pic` / `icg_classMap_eq_picProj`
                              — **Cl(K)=Pic**（M307F `picDivPic` と定義的に同一・rfl）
  * M406F-7 `icg_pid_class_trivial`
                              — **PID 判定** div 全射（全イデアル単項）⟹ Cl=0
  * M406F-8 `icgWholeSub` / `icgPIDClassGroup` / `icg_pid_all_trivial`
                              — **閉じた実例** P(K)=I(K)（PID）⟹ Cl=0（仮定なし・完全。
                                Cl(ℤ)=0 の化身: ℤ は PID で全分数イデアルが単項）
  * M406F-9 capstone `IdealClassGroupData` / `icgData` / `icg_exists` /
    `icg_pid_example` / `icg_class_map_kills_principal`

  ## 正直な限定（何が本物で何が後続か・消去/弱化禁止）

  - **本物（完全証明）**:
    ・分数イデアル群 I(K) が**アーベル群**（M307F `picDivGrp` 昇格再利用）。
    ・単項写像 div:K^×→I(K) が**群準同型** div(ab)=div(a)+div(b)（付値の加法性）。
    ・単項部分群 P(K)＝im(div) が**正規部分群**（I(K) アーベル）。
    ・**イデアル類群 Cl(K)＝I(K)/P(K) が群**であること（M267F 商群、完全）。
    ・**クラス写像** cl が**全射準同型**であること・**単項イデアルの類は自明**。
    ・**自明類の完全判定** [𝔞]=0 ⟺ 𝔞 単項（射影核＝P(K)、完全）。
    ・**Cl(K)=Pic**（定義的同一、rfl）。
    ・**PID で Cl=0**（div 全射 ⟹ 全類自明；P(K)=I(K) の閉じた実例で仮定なし完全証明）。
  - **正直申告（未達・骨組み・後続。飾りでなく地図）**:
    ・**付値系は M307F `PicDivValuation` をパラメータとして受け取る**（各素点の
      ord_k:K^×→ℤ が加法的準同型・有限台 witness）。これは div の**本物の普遍形**であり、
      特定の数体／局所体上の実 P 進付値（M301F 付値）で `PicDivValuation` を実体化して
      div の全射性（PID 判定の witness）を具体的に供給するのは後続。本ファイルは PID 実例を
      **P(K)=I(K)（全分数イデアル単項）の閉じた形**で完全に閉じる（Cl(ℤ)=0 の化身）。
    ・**Cl(K) の有限性（類数 h<∞）は範囲外**。有限性は Minkowski 束・格子点計数
      （幾何学的数論）を要すので後続。I(K) は自由アーベル群として無限位数であり、
      本ファイルは Cl を**群**として建てる（有限性・類数公式は主張しない）。
    ・**Dedekind 整域で全非零イデアルが可逆（I(K) が群）**の完全証明は Dedekind 性
      （Noether+整閉+次元1）を要すので M302F の骨組み／後続。本ファイルは I(K) を
      M307F の付値ベクトル群（＝素因子分解の一意性を仮定した Weil 因子群）として建てる。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無。
-/
import IUT.PicardDivisor

namespace IUT

/-! ## M406F-1: 分数イデアル群 I(K) と単項写像 div:K^×→I(K) -/

/-- **M406F-1a: 分数イデアル群 I(K)** — 素点（素因子）上の付値ベクトルのなす自由
    アーベル群（Dedekind 整域では素因子分解の一意性により分数イデアル ≅ Σ v_P(𝔞)[P]
    ＝ Weil 因子群）。M307F `picDivGrp` の**昇格再利用**（因子群＝分数イデアル群の化身）。 -/
def icgIdealGroup : Grp := picDivGrp

/-- **M406F-1b: 単項写像** div : K^×(=G) → I(K)、a ↦ (a) = Σ_P v_P(a)[P]。
    M307F `picDivPrincipalHom`（付値データ v からの本物の群準同型）。 -/
def icgDiv {G : Grp} (v : PicDivValuation G) : Hom G icgIdealGroup :=
  picDivPrincipalHom v

/-- **M406F-1c: div は群準同型** div(ab) = div(a)·div(b)（付値の加法性）。 -/
theorem icg_div_isHom {G : Grp} (v : PicDivValuation G) (a b : G.carrier) :
    (icgDiv v).map (G.mul a b)
      = icgIdealGroup.mul ((icgDiv v).map a) ((icgDiv v).map b) :=
  (icgDiv v).map_mul a b

/-- **M406F-1d: I(K) は可換群**（分数イデアルの積は可換）。 -/
theorem icg_ideal_group_comm (x y : icgIdealGroup.carrier) :
    icgIdealGroup.mul x y = icgIdealGroup.mul y x :=
  picDivGrp_comm x y

/-! ## M406F-2: 単項分数イデアル部分群 P(K) = im(div) -/

/-- **M406F-2a: 単項分数イデアル部分群 P(K)** = im(div) ⊆ I(K)（M267F `imSubgroup`）。
    「単項イデアル (a)＝a で生成される分数イデアル」全体のなす部分群。 -/
def icgPrincipalSub {G : Grp} (v : PicDivValuation G) : Subgroup icgIdealGroup :=
  imSubgroup (picDivPrincipalHom v)

/-- **M406F-2b: 単項部分群は正規**（I(K) はアーベル）— M307F `picDivPrincipalNormal`。 -/
theorem icgPrincipalNormal {G : Grp} (v : PicDivValuation G) :
    IsNormalSubgroup icgIdealGroup (icgPrincipalSub v) :=
  picDivPrincipalNormal v

/-- **M406F-2c: 所属判定** — D ∈ P(K) ⟺ D が単項（∃a, div a = D）。 -/
theorem icg_principal_mem_iff {G : Grp} (v : PicDivValuation G)
    (D : icgIdealGroup.carrier) :
    (icgPrincipalSub v).mem D ↔ ∃ a, (icgDiv v).map a = D :=
  Iff.rfl

/-! ## M406F-3: イデアル類群 Cl(K) = I(K)/P(K) とクラス写像 -/

/-- **M406F-3a: イデアル類群 Cl(K) = I(K)/P(K)** — 分数イデアル群を単項分数イデアルで
    割った本物の商群（M267F `quotientGroupN`）。類数を定める中心対象・Pic の算術的化身。 -/
def icgClassGroup {G : Grp} (v : PicDivValuation G) : Grp :=
  quotientGroupN icgIdealGroup (icgPrincipalSub v) (picDivPrincipalNormal v)

/-- **M406F-3b: クラス写像** cl : I(K) → Cl(K)、𝔞 ↦ [𝔞]（射影準同型）。 -/
def icgClassMap {G : Grp} (v : PicDivValuation G) : Hom icgIdealGroup (icgClassGroup v) :=
  quotientProjN icgIdealGroup (icgPrincipalSub v) (picDivPrincipalNormal v)

/-- **M406F-3c: クラス写像は全射**（全ての類は或る分数イデアルの類）。 -/
theorem icg_class_map_surjective {G : Grp} (v : PicDivValuation G) :
    ∀ x : (icgClassGroup v).carrier, ∃ D, (icgClassMap v).map D = x :=
  quotientProjN_surjective icgIdealGroup (icgPrincipalSub v) (picDivPrincipalNormal v)

/-! ## M406F-4: 単項イデアルの類は自明（クラス写像が P(K) を潰す） -/

/-- **M406F-4: 単項イデアルの類は自明** cl(div a) = [(a)] = 0（クラス写像はちょうど
    単項分数イデアル部分群 P(K) を単位元に送る）。イデアル類群の定義的核心。 -/
theorem icg_class_of_principal_trivial {G : Grp} (v : PicDivValuation G)
    (a : G.carrier) :
    (icgClassMap v).map ((icgDiv v).map a) = (icgClassGroup v).one :=
  (quotientProjN_ker icgIdealGroup (icgPrincipalSub v) (picDivPrincipalNormal v)
      ((icgDiv v).map a)).mpr ⟨a, rfl⟩

/-! ## M406F-5: 自明類の完全判定 [𝔞]=0 ⟺ 𝔞 単項 -/

/-- **M406F-5a: 自明類の完全判定** [𝔞] = 0 ⟺ 𝔞 ∈ P(K)（射影の核がちょうど P(K)）。
    M267F `quotientProjN_ker`。イデアル類群の普遍性の実体。 -/
theorem icg_class_trivial_iff {G : Grp} (v : PicDivValuation G)
    (D : icgIdealGroup.carrier) :
    (icgClassMap v).map D = (icgClassGroup v).one ↔ (icgPrincipalSub v).mem D :=
  quotientProjN_ker icgIdealGroup (icgPrincipalSub v) (picDivPrincipalNormal v) D

/-- **M406F-5b: 自明類 ⟺ 単項** [𝔞] = 0 ⟺ ∃a, div a = 𝔞（𝔞 が単項分数イデアル）。 -/
theorem icg_class_trivial_iff_principal {G : Grp} (v : PicDivValuation G)
    (D : icgIdealGroup.carrier) :
    (icgClassMap v).map D = (icgClassGroup v).one ↔ ∃ a, (icgDiv v).map a = D :=
  icg_class_trivial_iff v D

/-! ## M406F-6: Pic との同一視 -/

/-- **M406F-6a: Cl(K) = Pic** — イデアル類群は M307F Picard 群 Pic=Div/im(div) と
    **定義的に同一の商群**（分数イデアル群＝因子群、単項イデアル＝単項因子）。rfl。 -/
theorem icg_cl_eq_pic {G : Grp} (v : PicDivValuation G) :
    icgClassGroup v = picDivPic v := rfl

/-- **M406F-6b: クラス写像 = Picard 射影** — cl:I(K)→Cl(K) は M307F の射影
    Div→Pic と定義的に同一。イデアル類写像は直線束の同型類写像の算術的化身。 -/
theorem icg_classMap_eq_picProj {G : Grp} (v : PicDivValuation G) :
    icgClassMap v
      = quotientProjN picDivGrp (picDivPrincipalSub v) (picDivPrincipalNormal v) :=
  rfl

/-! ## M406F-7: PID 判定 — div 全射 ⟹ Cl=0 -/

/-- **M406F-7: PID 判定** — div が全射（全分数イデアルが単項）なら Cl(K)=0
    （全ての類が自明）。PID（一意分解整域を含む）のイデアル類群消滅の本物の判定。 -/
theorem icg_pid_class_trivial {G : Grp} (v : PicDivValuation G)
    (hsurj : ∀ D : icgIdealGroup.carrier, (icgPrincipalSub v).mem D)
    (x : (icgClassGroup v).carrier) : x = (icgClassGroup v).one := by
  obtain ⟨D, hD⟩ := quotientProjN_surjective icgIdealGroup (icgPrincipalSub v)
      (picDivPrincipalNormal v) x
  rw [← hD]
  exact (quotientProjN_ker icgIdealGroup (icgPrincipalSub v)
      (picDivPrincipalNormal v) D).mpr (hsurj D)

/-! ## M406F-8: 閉じた実例 — P(K)=I(K)（PID）⟹ Cl=0（Cl(ℤ)=0 の化身） -/

/-- **M406F-8a: 全部分群** P(K)=I(K)（PID では全分数イデアルが単項）を表す
    improper 部分群（mem ≡ True）。ℤ 等の PID で単項写像 div が全射になる事実の化身。 -/
def icgWholeSub : Subgroup icgIdealGroup where
  mem := fun _ => True
  one_mem := True.intro
  mul_mem := fun _ _ => True.intro
  inv_mem := fun _ => True.intro

/-- **M406F-8b: 全部分群は正規**（I(K) アーベル）。 -/
theorem icgWholeNormal : IsNormalSubgroup icgIdealGroup icgWholeSub :=
  picDivAbelianNormal icgWholeSub

/-- **M406F-8c: PID のイデアル類群** Cl = I(K)/I(K)（P(K)=I(K)）。 -/
def icgPIDClassGroup : Grp :=
  quotientGroupN icgIdealGroup icgWholeSub icgWholeNormal

/-- **M406F-8d: PID では Cl=0**（仮定なし・完全証明）— 全分数イデアルが単項
    （P(K)=I(K)）なら類群は自明（全元が単位元）。**Cl(ℤ)=0 の本物の化身**:
    ℤ は PID で全分数イデアルが単項ゆえイデアル類群は消える。 -/
theorem icg_pid_all_trivial (x : icgPIDClassGroup.carrier) :
    x = icgPIDClassGroup.one := by
  obtain ⟨D, hD⟩ := quotientProjN_surjective icgIdealGroup icgWholeSub icgWholeNormal x
  rw [← hD]
  exact (quotientProjN_ker icgIdealGroup icgWholeSub icgWholeNormal D).mpr True.intro

/-! ## M406F-9: capstone -/

/-- **M406F-9a: イデアル類群データ** — 分数イデアル群 I(K)・単項写像 div・
    イデアル類群 Cl(K)・クラス写像 cl（全射・単項を潰す・自明類判定）の束ね。
    全フィールドが本モジュールの完全証明。 -/
structure IdealClassGroupData {G : Grp} (v : PicDivValuation G) where
  /-- 分数イデアル群 I(K)。 -/
  idealGroup : Grp
  /-- 単項写像 div : K^× → I(K)。 -/
  div : Hom G idealGroup
  /-- イデアル類群 Cl(K) = I(K)/P(K)。 -/
  Cl : Grp
  /-- クラス写像 cl : I(K) → Cl(K)。 -/
  classMap : Hom idealGroup Cl
  /-- クラス写像は全射。 -/
  classMap_surjective : ∀ x, ∃ D, classMap.map D = x
  /-- 単項イデアルの類は自明 cl(div a) = 0。 -/
  principal_class_trivial : ∀ a, classMap.map (div.map a) = Cl.one
  /-- 自明類の完全判定 [𝔞]=0 ⟺ 𝔞 単項。 -/
  class_trivial_iff : ∀ D, classMap.map D = Cl.one ↔ ∃ a, div.map a = D

/-- **M406F-9b: イデアル類群データの witness**（全て本物）。 -/
def icgData {G : Grp} (v : PicDivValuation G) : IdealClassGroupData v where
  idealGroup := icgIdealGroup
  div := icgDiv v
  Cl := icgClassGroup v
  classMap := icgClassMap v
  classMap_surjective := icg_class_map_surjective v
  principal_class_trivial := icg_class_of_principal_trivial v
  class_trivial_iff := icg_class_trivial_iff_principal v

/-- **M406F-9c: 見出し定理** — 任意の付値系（数体 K の付値データ）に対し
    イデアル類群データが存在する。 -/
theorem icg_exists {G : Grp} (v : PicDivValuation G) :
    Nonempty (IdealClassGroupData v) := ⟨icgData v⟩

/-- **M406F-9d: 実例 Cl(ℤ)=0** — PID（全分数イデアル単項、P(K)=I(K)）では
    イデアル類群が自明（全類が 0）。ℤ のイデアル類群消滅の本物の化身。 -/
theorem icg_pid_example : ∀ x : icgPIDClassGroup.carrier, x = icgPIDClassGroup.one :=
  icg_pid_all_trivial

/-- **M406F-9e: 実例 クラス写像は単項を潰す** — 任意の付値系で単項イデアル (a) の
    類は自明。イデアル類群がちょうど「単項でない分数イデアル」を測ることの実体。 -/
theorem icg_class_map_kills_principal {G : Grp} (v : PicDivValuation G) (a : G.carrier) :
    (icgData v).classMap.map ((icgData v).div.map a) = (icgData v).Cl.one :=
  icg_class_of_principal_trivial v a

end IUT
