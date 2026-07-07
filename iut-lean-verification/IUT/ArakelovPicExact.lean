-- M431F ArakelovPicExact [実・本物・柱C]
-- complete_pct 影響: 柱C で Arakelov Picard 完全列 0→Pic^0→Pic(D̂)→im(deg)→0 を本物で建設。
--   ℝ を加法群 (Quot realEq) へ昇格し、deg を Pic(D̂)→ℝ の literal 群準同型として取り出し、
--   ker(deg)=Pic^0（M426F）・inclusion 単射・deg の像への全射（SES 構造）を完全証明。
-- 正直な限定: im(deg) は本物の部分群として建てる。deg の像がℝ全体という「真の全射性」の
--   算術的内容（Dirichlet 単数格子・regulator・Minkowski／数の幾何）は 後続。本模型では ∞ 部を
--   自由実数とするため模型上は全射だが、それは模型の自由性であり真の算術的像の制約は主張しない。

/-
  IUT/ArakelovPicExact.lean — M431F（柱C: Arakelov Picard 完全列 / Frobenioid）

  ── 主要成果の分類: **[実]**（昇格 (a) + 本物の先行建設 (b)）。M356F
     (`IUT/ArakelovDivisor.lean`, prefix `ard`) が Arakelov 因子群 D̂・実次数 deg:D̂→ℝ
     （代表レベル・realEq well-defined）・Arakelov Picard 群 `ardPicard`・主因子 deg=0 を建て、
     M426F (`IUT/ArakelovClassDegree.lean`, prefix `acd`) が次数0 類群 Pic^0＝`acdPic0Sub`
     （Arakelov Picard 群の本物の部分群・Pic^0=ker(deg) の核特徴付け `acd_pic0_iff_deg_zero`）
     を建てた。本モジュールはその **次の本物の一手**——**Arakelov Picard 完全列**
     0 → Pic^0 → Pic(D̂) → im(deg) → 0 を core Lean のみで完全証明する。

  complete_pct 影響: **柱C（Frobenioid／Arakelov Picard 完全列）の実 IUT 完全証明率を前進**。
  M426F は deg を「代表レベルの実数値関数（realEq well-defined）」として保ち、literal な群準同型に
  していなかった（ℝ が setoid ゆえ・M426F の正直申告 #1）。本ファイルは:
  (1) **ℝ を加法群へ昇格**（`apeRealGrp` = Quot realEq 上の realAdd 加法群）——M426F が「後続」と
      した RReal の商型の建設をゼロから本物で（結合・単位・逆元を Quot.sound で完全証明）。
  (2) **deg を literal 群準同型 D̂→ℝ へ昇格**（`apeDegHat : Hom ardGroup apeRealGrp`）——
      well-defined 性（M356F `ardDeg_wd`）を商の単一射で、加法準同型（M356F `ard_deg_hom`）を
      Quot.sound で literal Hom に。
  (3) **deg が Picard 類群へ降りる literal Hom**（`apeDegPic : Hom (ardPicard) apeRealGrp`）——
      主因子は deg=0（M356F `ard_principalRaw_degree_zero`）ゆえ剰余類の上で well-defined。
  (4) **ker(deg)=Pic^0**（`ape_ker_degPic_iff`）——完全列の Pic での完全性（M426F の核特徴付けを
      literal Hom の核として再述、Quot 分離性 `quot_exact_of_equiv` を使用）。
  (5) **im(deg) は ℝ の部分群**（`apeDegImage = imSubgroup apeDegPic`）+ deg の像への corestriction
      `apeDegOnto` は全射（`ape_degOnto_surjective`）——完全列の im(deg) での完全性（tautological）。
  (6) **inclusion Pic^0 → Pic は単射**（`apeInclPic0` / `ape_inclPic0_injective`）——完全列の
      Pic^0 での完全性。
  (7) **Pic での完全性 ker(onto)=im(incl)**（`ape_exact_at_pic`）——SES の中央での完全性。
  (8) **アルキメデス実インスタンス**（`apeArchDivisor` / `ape_arch_deg` / `ape_arch_in_image`）——
      純アルキメデス因子 ⟨0,r⟩ は deg≈r（任意の実数 r）ゆえ im(deg) は真に実数値（ℤ でなく ℝ）。
  (9) capstone `ArakelovPicExactData` / `ape_exists` / 実例。

  ## 正直な限定（消去/弱化禁止・地図として保持）
  - **本物（完全証明）**: ℝ の加法群（`apeRealGrp`）・deg の literal 群準同型化（D̂→ℝ・Pic→ℝ）・
    ker(deg)=Pic^0・im(deg) が ℝ の部分群・inclusion 単射・onto 全射・Pic での完全性
    ker(onto)=im(incl)。全て K=ℚ 模型上で本物・sorry 皆無・新規 Classical.choice なし。
  - **正直申告（未達・後続）**:
    ・**deg の像がℝ全体という「真の全射性」の算術的内容は範囲外**。本模型は ∞ 部を自由実数
      RReal とするため、模型上は `apeArchDivisor r` により deg が任意の r を実現し（模型上全射
      `ape_deg_model_surjective`）、im(deg)=ℝ となる。しかしこれは**模型の自由性の産物**であって
      真の算術的な像の制約（Dirichlet 単数定理による ∞ 部の格子性・regulator・Minkowski／数の
      幾何による Pic^0 のコンパクト性）は捉えていない。真の Arakelov 状況では im(deg) と Pic^0 の
      関係は単数格子で制御される——これは 後続。本ファイルは SES を im(deg) の上で本物にし、
      im(deg) が真に実数値であることを示すに留める（真の算術的像は主張しない）。
    ・**Pic^0 のコンパクト性**（有限体積 compact torus）は M426F と同じく範囲外。
    ・**一般数体（K≠ℚ）**は範囲外（M356F/M426F と同じ K=ℚ 模型）。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・[propext, Quot.sound]）・
  sorry 皆無・禁止タクティク不使用。
-/
import IUT.ArakelovClassDegree

namespace IUT

/-! ## M431F-1: ℝ を加法群へ昇格（apeRealGrp = Quot realEq 上の realAdd 群）

    M426F の正直申告 #1「deg を literal Hom にするには RReal の商型が要る」を解消する。
    ℝ は setoid（realEq）ゆえ、商 Quot realEq の上に realAdd を Quot.lift で降ろし、
    群公理を realEq の下の加法群法則（M117F realAdd_assoc/comm/zero/neg）から Quot.sound で
    完全証明する。これが deg を literal 群準同型として取り出す土台。 -/

/-- **M431F-1a: 実数商上の加法** — realAdd を Quot realEq の上へ二重 Quot.lift。
    well-defined 性は M117F 加法の左右 congruence。 -/
def apeRealAdd (x y : Quot realEq) : Quot realEq :=
  Quot.lift
    (fun a => Quot.lift (fun b => Quot.mk realEq (realAdd a b))
      (fun _ _ hb => Quot.sound (realAdd_congr_right a hb)) y)
    (fun a a' ha => by
      induction y using Quot.ind; rename_i b
      exact Quot.sound (realAdd_congr_left b ha)) x

/-- **M431F-1b: 実数商上の反元** — realNeg を Quot realEq の上へ Quot.lift。 -/
def apeRealNeg (x : Quot realEq) : Quot realEq :=
  Quot.lift (fun a => Quot.mk realEq (realNeg a))
    (fun _ _ ha => Quot.sound (realNeg_congr ha)) x

/-- **M431F-1c: 実数の加法群 ℝ = Quot realEq**（本物のアーベル群）。
    M426F が「後続」とした RReal 商型の literal 群。群公理を M117F realAdd の
    群法則（realEq の下）から Quot.sound で完全証明。これにより deg が literal Hom になる。 -/
def apeRealGrp : Grp where
  carrier := Quot realEq
  mul := apeRealAdd
  one := Quot.mk realEq realZero
  inv := apeRealNeg
  mul_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    induction z using Quot.ind; rename_i c
    show Quot.mk realEq (realAdd (realAdd a b) c)
        = Quot.mk realEq (realAdd a (realAdd b c))
    exact Quot.sound (realAdd_assoc a b c)
  one_mul := by
    intro x
    induction x using Quot.ind; rename_i a
    show Quot.mk realEq (realAdd realZero a) = Quot.mk realEq a
    exact Quot.sound (realEq_trans (realAdd_comm realZero a) (realAdd_zero a))
  inv_mul := by
    intro x
    induction x using Quot.ind; rename_i a
    show Quot.mk realEq (realAdd (realNeg a) a) = Quot.mk realEq realZero
    exact Quot.sound (realEq_trans (realAdd_comm (realNeg a) a) (realAdd_neg a))

/-- **M431F-1d: ℝ の加法群は可換**（realAdd の可換性）。 -/
theorem apeRealGrp_comm (x y : apeRealGrp.carrier) :
    apeRealGrp.mul x y = apeRealGrp.mul y x := by
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  show Quot.mk realEq (realAdd a b) = Quot.mk realEq (realAdd b a)
  exact Quot.sound (realAdd_comm a b)

/-- **M431F-1e: 商の分離性（ℝ）** — Quot.mk realEq x = Quot.mk realEq y ⟹ realEq x y。
    M13-3 一般化 `quot_exact_of_equiv` を realEq に適用（realEq は同値関係）。 -/
theorem ape_realEq_of_quot {x y : RReal} (h : Quot.mk realEq x = Quot.mk realEq y) :
    realEq x y :=
  quot_exact_of_equiv realEq realEq_refl realEq_symm realEq_trans h

/-! ## M431F-2: deg を literal 群準同型 D̂ → ℝ へ昇格 -/

/-- **M431F-2a: Arakelov 次数の literal 群準同型 D̂ → ℝ**（`apeDegHat`）。
    map = deg を Quot realEq へ送る（well-defined は M356F `ardDeg_wd`）、
    map_mul は M356F 加法準同型 `ard_deg_hom` を Quot.sound で literal 等式に。
    M426F では代表レベルの realEq 関数だった deg を **本物の Hom** に昇格。 -/
def apeDegHat (logp : Nat → RReal) : Hom ardGroup apeRealGrp where
  map := Quot.lift (fun D => Quot.mk realEq (ardDeg logp D))
    (fun _ _ h => Quot.sound (ardDeg_wd logp h))
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i A
    induction y using Quot.ind; rename_i B
    show Quot.mk realEq (ardDeg logp (ardAdd A B))
        = apeRealAdd (Quot.mk realEq (ardDeg logp A)) (Quot.mk realEq (ardDeg logp B))
    exact Quot.sound (ard_deg_hom logp A B)

/-- **M431F-2b: 主因子の次数は ℝ の単位元**（`apeDegHat.map(div̂(y)) = 0`）。
    M356F `ard_principalRaw_degree_zero`（実積公式）を literal 等式に。deg が Pic へ
    降りることの核。 -/
theorem ape_degHat_principal_eq_one (logp : Nat → RReal) (y : picDivGrp.carrier) :
    (apeDegHat logp).map ((ardPrincipalHom logp).map y) = apeRealGrp.one := by
  induction y using Quot.ind; rename_i f
  show Quot.mk realEq (ardDeg logp (ardPrincipalRaw logp f)) = Quot.mk realEq realZero
  exact Quot.sound (ard_principalRaw_degree_zero logp f)

/-! ## M431F-3: deg が Arakelov Picard 類群へ降りる literal 群準同型 -/

/-- **M431F-3a: deg は剰余類で well-defined**（literal 等式版）。
    同一 Picard 類（cosetRel、a⁻¹b が主因子 div̂(y)）なら b=a·div̂(y)、
    apeDegHat は Hom ゆえ deg(b)=deg(a)·deg(div̂(y))=deg(a)·1=deg(a)（ℝ の literal 等式）。 -/
theorem ape_degPic_wd (logp : Nat → RReal) (a b : ardGroup.carrier)
    (h : cosetRel ardGroup (ardPrincipalSub logp) a b) :
    (apeDegHat logp).map a = (apeDegHat logp).map b := by
  obtain ⟨y, hy⟩ := h
  -- hy : (ardPrincipalHom logp).map y = ardGroup.mul (ardGroup.inv a) b
  have hb : b = ardGroup.mul a ((ardPrincipalHom logp).map y) := by
    rw [hy, ← ardGroup.mul_assoc, ardGroup.mul_inv, ardGroup.one_mul]
  rw [hb, (apeDegHat logp).map_mul, ape_degHat_principal_eq_one logp y,
    apeRealGrp.mul_one]

/-- **M431F-3b: deg の literal 群準同型 Pic(D̂) → ℝ**（`apeDegPic`）。
    Arakelov Picard 群 `ardPicard = D̂/im(div̂)` の剰余類の上へ deg を well-defined に
    降ろした **本物の Hom**。完全列 0→Pic^0→Pic(D̂)→im(deg)→0 の中央写像。 -/
def apeDegPic (logp : Nat → RReal) : Hom (ardPicard logp) apeRealGrp where
  map := Quot.lift (apeDegHat logp).map
    (fun a b h => ape_degPic_wd logp a b h)
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show (apeDegHat logp).map (ardGroup.mul a b)
        = apeRealGrp.mul ((apeDegHat logp).map a) ((apeDegHat logp).map b)
    exact (apeDegHat logp).map_mul a b

/-! ## M431F-4: 完全列の Pic での完全性 ker(deg)=Pic^0 -/

/-- **M431F-4: ker(deg)=Pic^0**（完全列の Pic での完全性）— literal Hom deg:Pic→ℝ の
    核（deg([D])=0_ℝ）が M426F の次数0 類群 Pic^0（`acdPic0Sub`）に一致。
    deg([D])=0_ℝ ⟺ Quot.mk realEq (ardDeg D) = Quot.mk realEq 0 ⟺ realEq(ardDeg D,0)
    ⟺ [D]∈Pic^0（M426F の核特徴付け）。→ は Quot 分離性、← は Quot.sound。 -/
theorem ape_ker_degPic_iff (logp : Nat → RReal) (x : (ardPicard logp).carrier) :
    (apeDegPic logp).map x = apeRealGrp.one ↔ (acdPic0Sub logp).mem x := by
  induction x using Quot.ind; rename_i a
  induction a using Quot.ind; rename_i D
  constructor
  · intro h
    exact ape_realEq_of_quot h
  · intro h
    exact Quot.sound h

/-! ## M431F-5: im(deg) は ℝ の部分群・deg の像への corestriction は全射 -/

/-- **M431F-5a: im(deg) ⊆ ℝ**（達成可能な Arakelov 次数のなす部分群）— M267F imSubgroup
    により deg:Pic→ℝ の像は ℝ の**本物の部分群**。完全列の右端 im(deg)。 -/
def apeDegImage (logp : Nat → RReal) : Subgroup apeRealGrp :=
  imSubgroup (apeDegPic logp)

/-- **M431F-5b: deg の像への corestriction**（`apeDegOnto : Pic → im(deg)`）。
    値を像の subtype に載せた Hom（第一同型定理 firstIsoHom と同型の corestriction 論法）。 -/
def apeDegOnto (logp : Nat → RReal) :
    Hom (ardPicard logp) (subgroupGrp (apeDegImage logp)) where
  map := fun x => ⟨(apeDegPic logp).map x, ⟨x, rfl⟩⟩
  map_mul := by
    intro x y
    apply Subtype.ext
    show (apeDegPic logp).map ((ardPicard logp).mul x y)
        = apeRealGrp.mul ((apeDegPic logp).map x) ((apeDegPic logp).map y)
    exact (apeDegPic logp).map_mul x y

/-- **M431F-5c: corestriction は全射**（完全列の im(deg) での完全性・tautological）—
    像の任意元 h=deg(a) は apeDegOnto(a) の値。 -/
theorem ape_degOnto_surjective (logp : Nat → RReal) :
    ∀ y, ∃ x, (apeDegOnto logp).map x = y := by
  intro y
  obtain ⟨h, hex⟩ := y
  obtain ⟨a, ha⟩ := hex
  exact ⟨a, Subtype.ext ha⟩

/-! ## M431F-6: inclusion Pic^0 → Pic は単射（完全列の Pic^0 での完全性） -/

/-- **M431F-6a: inclusion Pic^0 ↪ Pic(D̂)**（`apeInclPic0`）— 次数0 類群を Picard 群へ
    埋め込む Hom（subtype の値取り）。完全列の左端の写像。 -/
def apeInclPic0 (logp : Nat → RReal) :
    Hom (subgroupGrp (acdPic0Sub logp)) (ardPicard logp) where
  map := fun x => x.val
  map_mul := fun _ _ => rfl

/-- **M431F-6b: inclusion は単射**（完全列の Pic^0 での完全性）— subtype の外延性。 -/
theorem ape_inclPic0_injective (logp : Nat → RReal) :
    Hom.Injective (apeInclPic0 logp) := by
  intro x y h
  exact Subtype.ext h

/-! ## M431F-7: Pic での完全性 ker(onto)=im(incl)（SES の中央完全性） -/

/-- **M431F-7a: ker(onto)=Pic^0** — corestriction onto の核（onto([D])=1_{im}）が Pic^0。
    値の第一成分の比較 → ker(deg)=Pic^0（M431F-4）へ帰着。 -/
theorem ape_ker_onto_iff (logp : Nat → RReal) (x : (ardPicard logp).carrier) :
    (apeDegOnto logp).map x = (subgroupGrp (apeDegImage logp)).one
      ↔ (acdPic0Sub logp).mem x := by
  constructor
  · intro h
    have hv : (apeDegPic logp).map x = apeRealGrp.one := congrArg Subtype.val h
    exact (ape_ker_degPic_iff logp x).mp hv
  · intro h
    apply Subtype.ext
    show (apeDegPic logp).map x = apeRealGrp.one
    exact (ape_ker_degPic_iff logp x).mpr h

/-- **M431F-7b: im(incl)=Pic^0** — inclusion Pic^0↪Pic の像はちょうど Pic^0（subtype の
    property そのもの）。 -/
theorem ape_im_incl_iff (logp : Nat → RReal) (x : (ardPicard logp).carrier) :
    (imSubgroup (apeInclPic0 logp)).mem x ↔ (acdPic0Sub logp).mem x := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h
    rw [← hp]
    exact p.property
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

/-- **M431F-7c: Pic での完全性 ker(onto)=im(incl)**（SES の中央完全性）—
    完全列 0→Pic^0→Pic(D̂)→im(deg)→0 が Pic で完全。ker(onto)=Pic^0=im(incl)。 -/
theorem ape_exact_at_pic (logp : Nat → RReal) (x : (ardPicard logp).carrier) :
    (apeDegOnto logp).map x = (subgroupGrp (apeDegImage logp)).one
      ↔ (imSubgroup (apeInclPic0 logp)).mem x :=
  Iff.trans (ape_ker_onto_iff logp x) (ape_im_incl_iff logp x).symm

/-! ## M431F-8: アルキメデス実インスタンス（im(deg) は真に実数値） -/

/-- **M431F-8a: 純アルキメデス Arakelov 因子** ⟨0, r⟩（有限部 0・∞ 重み r）。 -/
def apeArchDivisor (r : RReal) : ardRaw where
  fin := rawZero
  arch := r

/-- **M431F-8b: 純アルキメデス因子の次数は r**（`deg(⟨0,r⟩)≈r`）— 有限部の次数は 0
    （M312F `logVolGlobal_zero`）ゆえ deg=0+r≈r。任意の実数 r が達成される。 -/
theorem ape_arch_deg (logp : Nat → RReal) (r : RReal) :
    realEq (ardDeg logp (apeArchDivisor r)) r := by
  show realEq (realAdd (logVolGlobal logp rawZero) r) r
  refine realEq_trans (realAdd_congr_left r (logVolGlobal_zero logp)) ?_
  exact realEq_trans (realAdd_comm realZero r) (realAdd_zero r)

/-- **M431F-8c: 任意の実数 r は im(deg) に入る**（im(deg) は真に実数値・ℤ でなく ℝ）—
    純アルキメデス因子 ⟨0,r⟩ の Picard 類は deg≈r。∞ 部の非離散自由度が im(deg) を
    実数値にする（M426F の「archimedean 部が real degrees を与える」の実体）。 -/
theorem ape_arch_in_image (logp : Nat → RReal) (r : RReal) :
    (apeDegImage logp).mem (Quot.mk realEq r) := by
  refine ⟨(quotientProjN ardGroup (ardPrincipalSub logp) (ardPrincipalNormal logp)).map
      (Quot.mk ardEq (apeArchDivisor r)), ?_⟩
  show Quot.mk realEq (ardDeg logp (apeArchDivisor r)) = Quot.mk realEq r
  exact Quot.sound (ape_arch_deg logp r)

/-- **M431F-8d: deg は模型上ℝへ全射**（正直な注記付き）— 任意の r∈ℝ に対し純アルキメデス
    因子の類が deg≈r を実現する。**ただしこれは ∞ 部を自由実数とする模型の産物**であって、
    真の算術的な像の制約（Dirichlet 単数格子・regulator・Minkowski）ではない（ヘッダの
    正直申告参照）。完全列は im(deg) の上で本物にし、真の全射性は主張しない。 -/
theorem ape_deg_model_surjective (logp : Nat → RReal) :
    ∀ z : apeRealGrp.carrier, ∃ x : (ardPicard logp).carrier,
      (apeDegPic logp).map x = z := by
  intro z
  induction z using Quot.ind; rename_i r
  refine ⟨(quotientProjN ardGroup (ardPrincipalSub logp) (ardPrincipalNormal logp)).map
      (Quot.mk ardEq (apeArchDivisor r)), ?_⟩
  show Quot.mk realEq (ardDeg logp (apeArchDivisor r)) = Quot.mk realEq r
  exact Quot.sound (ape_arch_deg logp r)

/-! ## M431F-9: capstone -/

/-- **M431F-9a: Arakelov Picard 完全列データ** — ℝ の加法群・Pic(D̂)・deg の literal Hom・
    Pic^0・im(deg)・inclusion・corestriction・単射性・全射性・ker(deg)=Pic^0・
    Pic での完全性を束ねた **SES 0→Pic^0→Pic(D̂)→im(deg)→0** の完全な実体。 -/
structure ArakelovPicExactData (logp : Nat → RReal) where
  /-- ℝ の加法群（Quot realEq）。 -/
  realGrp : Grp
  /-- Arakelov Picard 群 Pic(D̂)。 -/
  pic : Grp
  /-- deg の literal 群準同型 Pic(D̂) → ℝ。 -/
  deg : Hom pic realGrp
  /-- 次数0 類群 Pic^0 ⊆ Pic(D̂)。 -/
  pic0 : Subgroup pic
  /-- 達成可能次数の像 im(deg) ⊆ ℝ。 -/
  image : Subgroup realGrp
  /-- inclusion Pic^0 ↪ Pic(D̂)。 -/
  incl : Hom (subgroupGrp pic0) pic
  /-- deg の像への corestriction Pic(D̂) ↠ im(deg)。 -/
  onto : Hom pic (subgroupGrp image)
  /-- inclusion は単射（Pic^0 での完全性）。 -/
  incl_injective : Hom.Injective incl
  /-- corestriction は全射（im(deg) での完全性）。 -/
  onto_surjective : ∀ y, ∃ x, onto.map x = y
  /-- ker(deg)=Pic^0（Pic での核特徴付け）。 -/
  ker_eq_pic0 : ∀ x, deg.map x = realGrp.one ↔ pic0.mem x
  /-- Pic での完全性 ker(onto)=im(incl)。 -/
  exact_at_pic : ∀ x, (onto.map x = (subgroupGrp image).one)
    ↔ (imSubgroup incl).mem x

/-- **M431F-9b: Arakelov Picard 完全列データの witness**（全て本物）。 -/
def arakelovPicExactData (logp : Nat → RReal) : ArakelovPicExactData logp where
  realGrp := apeRealGrp
  pic := ardPicard logp
  deg := apeDegPic logp
  pic0 := acdPic0Sub logp
  image := apeDegImage logp
  incl := apeInclPic0 logp
  onto := apeDegOnto logp
  incl_injective := ape_inclPic0_injective logp
  onto_surjective := ape_degOnto_surjective logp
  ker_eq_pic0 := ape_ker_degPic_iff logp
  exact_at_pic := ape_exact_at_pic logp

/-- **M431F-9c: 存在** — Arakelov Picard 完全列は充足可能（K=ℚ）。 -/
theorem ape_exists (logp : Nat → RReal) : Nonempty (ArakelovPicExactData logp) :=
  ⟨arakelovPicExactData logp⟩

/-! ## M431F-10: 実例 -/

/-- **M431F-10a: 実例（自明類の次数0）** — deg(1_Pic)=0_ℝ（Hom は単位元を保つ）。 -/
theorem ape_example_one_deg (logp : Nat → RReal) :
    (apeDegPic logp).map (ardPicard logp).one = apeRealGrp.one :=
  (apeDegPic logp).map_one

/-- **M431F-10b: 実例（自明類は Pic^0）** — 単位類は ker(deg)=Pic^0 に入る。 -/
theorem ape_example_trivial_in_pic0 (logp : Nat → RReal) :
    (acdPic0Sub logp).mem (ardPicard logp).one :=
  (ape_ker_degPic_iff logp (ardPicard logp).one).mp (apeDegPic logp).map_one

/-- **M431F-10c: 実例（主因子 div̂(2) の類は ker(deg)）** — deg([div̂(2)])=0_ℝ
    （実積公式 deg=log2+(−log2)=0）。 -/
theorem ape_example_two_deg (logp : Nat → RReal) :
    (apeDegPic logp).map
        ((quotientProjN ardGroup (ardPrincipalSub logp) (ardPrincipalNormal logp)).map
          (Quot.mk ardEq (ardPrincipalRaw logp (pfSinglePrime 0 1).fin)))
      = apeRealGrp.one :=
  (ape_ker_degPic_iff logp _).mpr (acd_example_two_class_in_pic0 logp)

/-- **M431F-10d: 実例（零実数は im(deg)）** — 0_ℝ ∈ im(deg)（純アルキメデス因子 ⟨0,0⟩）。 -/
theorem ape_example_zero_in_image (logp : Nat → RReal) :
    (apeDegImage logp).mem (Quot.mk realEq realZero) :=
  ape_arch_in_image logp realZero

/-- **M431F-10e: 実例（im(deg) は真に実数値）** — 任意の r に対し r∈im(deg)
    （アルキメデス因子の非離散自由度）。 -/
theorem ape_example_arch_real (logp : Nat → RReal) (r : RReal) :
    (apeDegImage logp).mem (Quot.mk realEq r) :=
  ape_arch_in_image logp r

end IUT
