/-
  IUT/SzpiroReduction.lean — M352F [実／本物]
  分類: 実 (実 Cor 3.12 界 ⟹ Szpiro/高さ不等式・3.12⟹Szpiro 実還元)
  complete_pct 影響: 柱D を前進（M347F の 3.11⟹3.12 実還元の次段＝実 Cor 3.12 界 ⟹ Szpiro
    不等式（height≤C·conductor+O(1)）の還元を実 deg_ℝ で証明し、crux⟹Cor3.12⟹Szpiro の
    完全条件付き連鎖を合成。crux Dβ-ω は依然外部仮説）。
  正直な限定: crux Dβ-ω（＝多輻的アルゴリズム＝論争の係争点）は外部仮説のまま・全連鎖は
    条件付き。定数 C/ε は模型 witness。本層は還元（3.12⟹Szpiro）が実内容で crux 非証明。
-/

/-
  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  本層は M347F `CruxInequalityReal.lean`（実 Cor 3.12 界 `cruxRealCor312Bound`＝
  deg_ℝ(Σj²) ≤ deg_ℝ(Σ w(k)k²)）を**前件**として受け取り、その**次段の還元**——
  実 Cor 3.12 界 ⟹ Szpiro/高さ不等式（height ≤ C·conductor + O(1)）——を、M312F の
  本物の実 Arakelov 局所次数 deg_ℝ（`logVolLocal`）の上で本物にする。主語は M319F/M324F
  の実パイロット体積の閉形式であり、toy m202fVol を用いない。crux（Dβ-ω）は決して証明せず、
  全連鎖 crux ⟹ Cor 3.12 ⟹ Szpiro を**条件付き**で合成する。

  * M352F-1 `szpHeightDeg` / `szpConductorDeg` / `szpConductorDeg_nonneg`
      — 高さ deg_ℝ（＝deg(q)＝テータパイロット LHS 閉形式 deg_ℝ(Σj²)）と導手 deg_ℝ
        （＝radical＝ガウスパイロット RHS 閉形式 deg_ℝ(Σ w(k)k²)）を実対象で定義。
        非負重み log q_v ≥ 0 の下で導手 deg_ℝ ≥ 0（M312F `logVol_rmul_nonneg`）。
  * M352F-2 `szpSzpiroIneq`
      — Szpiro 不等式の Prop: height ≤ C·conductor + bounded（両辺実 deg_ℝ）。
  * M352F-3 `szp_cor312_implies_szpiro`
      — **本丸の還元**（3.12⟹Szpiro）: 実 Cor 3.12 界（M347F `cruxRealCor312Bound`）を
        前件に、C ≥ 1・bounded ≥ 0・conductor ≥ 0 の下で Szpiro 不等式が従う。証明は
        推移律 height ≤ conductor ≤ C·conductor ≤ C·conductor+bounded（本物）。crux は前件。
  * M352F-4 `szp_full_chain`
      — **完全連鎖**（crux ⟹ Cor 3.12 ⟹ Szpiro）: M347F `cruxR_implies_cor312` と本層
        `szp_cor312_implies_szpiro` を合成。crux（前件）は仮説であって証明されない。
  * M352F-5 `szp_abc_form` / `szpAbcIneq`
      — ABC 形（height ≤ (1+ε)·conductor + O_ε(1)）: C = 1+ε の特殊化。ε ≥ 0 で
        1 ≤ 1+ε ゆえ M352F-3 に還元。算術的帰結の形。
  * M352F-6 `szp_crux_still_external`
      — 全連鎖が crux（M347F `cruxRealIneq`）に条件付きであることの明示（Iff.rfl）。
        crux はちょうど M324F 受け取り仮説であって定理ではない——正直な境界。
  * M352F-7 capstone `SzpiroReductionData` / `szpiroReductionData` / `szp_exists`。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）

  - **本物（完全証明）**:
    ・還元 3.12⟹Szpiro（`szp_cor312_implies_szpiro`）は本物: 高さ・導手を実 deg_ℝ で
      構成し、Cor 3.12 界を前件に推移律で Szpiro 不等式を導く部分は完全証明（rmul 単調性・
      加法両立・realAdd_zero を core Lean のみで使用）。
    ・完全連鎖 crux⟹Cor3.12⟹Szpiro の合成（`szp_full_chain`）・ABC 形（`szp_abc_form`）も
      前件を仮説としたまま本物で閉じる。
  - **正直申告（未達・crux・後続。飾りでなく地図。過大主張の厳禁）**:
    ・**crux Dβ-ω（テータパイロット ≤ ガウスパイロット＝多輻的アルゴリズム＝IUT 論争の
      係争点）は恒久的に本層の範囲外**。全連鎖は crux（および Cor 3.12 界）を**前件**として
      受け取る条件付き定理であって、crux 自体を決して証明しない。`szp_crux_still_external`
      （Iff.rfl）が「連鎖は crux に条件付きである」ことを機械検証で明示する。
    ・**定数 C・ε・bounded は模型 witness**（RReal パラメータ）。Szpiro 定数 6（原型
      deg(q) ≤ 6·deg(conductor)+O(1)）や ABC の (1+ε) の**具体値・最適性**は本層の範囲外
      ——本層は「C ≥ 1・bounded ≥ 0 なら還元が成り立つ」形（還元の構造）を本物にする。
    ・log q_v（実重み `logq`）は M312F/M319F/M324F/M347F と同じく**実重み witness**。
      log q_v の超越性・具体値・高さ/導手の大域体上の実在は範囲外（柱A/柱C の後続）。
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ不等式は rLe で言明する（M347F 系と
      同じ正直な形）。
  全て新規 Classical.choice を証明本体に導入せず（M347F/M324F/M319F/M312F から継承、
  #print axioms は propext/Quot.sound 系のみ）。sorry 皆無・禁止タクティク不使用（core Lean
  のみ）。一般名は `szp` 接頭辞で衝突回避。
-/
import IUT.CruxInequalityReal

namespace IUT

/-! ## M352F-1: 高さ deg_ℝ・導手 deg_ℝ（実対象） -/

/-- **M352F-1a: 高さ deg_ℝ** — deg(q)（テータパイロット LHS の閉形式 deg_ℝ(Σ_{j=1}^{l} j²)）
    を実 Arakelov 局所次数で。M319F `thPilot_total_closed` の右辺と一致する実対象。 -/
def szpHeightDeg (logq : Nat → RReal) (v : Nat) (l : Nat) : RReal :=
  logVolLocal logq v ((sumSq l : Nat) : Int)

/-- **M352F-1b: 導手 deg_ℝ** — 導手（radical, Σ_{k≤l} w(k)k²＝ガウスパイロット RHS の閉形式
    deg_ℝ）を実 Arakelov 局所次数で。M324F `gPilot_total_wssq` の右辺と一致する実対象。 -/
def szpConductorDeg (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) : RReal :=
  logVolLocal logq v ((wssq w l : Nat) : Int)

/-- **定理 (M352F-1c): 導手 deg_ℝ の非負性** — 非負重み log q_v ≥ 0 の下で導手 deg_ℝ ≥ 0
    （導手係数 Σ w(k)k² は Nat ゆえ非負・M312F `logVol_rmul_nonneg`）。Szpiro 還元で
    conductor ≥ 0 を放電するのに使える。 -/
theorem szpConductorDeg_nonneg (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (hq : rLe realZero (logq v)) :
    rLe realZero (szpConductorDeg logq v w l) := by
  show rLe realZero (rmul (intToReal ((wssq w l : Nat) : Int)) (logq v))
  exact logVol_rmul_nonneg (intToReal_mono (by omega)) hq

/-! ## M352F-2: Szpiro 不等式（Prop・両辺実 deg_ℝ） -/

/-- **M352F-2: Szpiro 不等式** — height ≤ C·conductor + bounded（両辺実 deg_ℝ）。
    deg(q) ≤ C·deg(conductor) + O(1) の Szpiro/ABC 型高さ・導手不等式を、実 Arakelov
    次数の順序 rLe で述べたもの。C・bounded は模型 witness。 -/
def szpSzpiroIneq (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (C bounded : RReal) : Prop :=
  rLe (szpHeightDeg logq v l)
    (realAdd (rmul C (szpConductorDeg logq v w l)) bounded)

/-! ## M352F-3: 本丸の還元（実 Cor 3.12 界 ⟹ Szpiro 不等式） -/

/-- **定理 (M352F-3, 本丸): 3.12⟹Szpiro 実還元（前件は Cor 3.12 界）** — 実 Cor 3.12 界
    `cruxRealCor312Bound`（＝deg_ℝ(Σj²) ≤ deg_ℝ(Σ w(k)k²)＝height ≤ conductor）を**前件**に、
    C ≥ 1（`rLe (intToReal 1) C`）・bounded ≥ 0・conductor ≥ 0 の下で Szpiro 不等式
    height ≤ C·conductor + bounded が従う。証明は推移律による本物の還元:
    height ≤ conductor ≤ C·conductor ≤ C·conductor + bounded（1·conductor≈conductor の
    書き替え・rmul 右単調性・加法両立）。**crux 自体（前件の由来）は証明しない**。 -/
theorem szp_cor312_implies_szpiro (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (C bounded : RReal) (hC : rLe (intToReal 1) C) (hb : rLe realZero bounded)
    (hcond : rLe realZero (szpConductorDeg logq v w l))
    (cor312 : cruxRealCor312Bound logq v w l) :
    szpSzpiroIneq logq v w l C bounded := by
  show rLe (szpHeightDeg logq v l)
    (realAdd (rmul C (szpConductorDeg logq v w l)) bounded)
  -- height ≤ conductor（前件・Cor 3.12 界と defeq）
  have h1 : rLe (szpHeightDeg logq v l) (szpConductorDeg logq v w l) := cor312
  -- conductor ≈ 1·conductor ≤ C·conductor（rmul 右単調性 + 1·x≈x）
  have hmono : rLe (rmul (intToReal 1) (szpConductorDeg logq v w l))
      (rmul C (szpConductorDeg logq v w l)) := rmul_le_mul_right hC hcond
  have hone : realEq (rmul (intToReal 1) (szpConductorDeg logq v w l))
      (szpConductorDeg logq v w l) :=
    realEq_trans (rmul_comm (intToReal 1) (szpConductorDeg logq v w l))
      (rmul_one (szpConductorDeg logq v w l))
  have h2 : rLe (szpConductorDeg logq v w l) (rmul C (szpConductorDeg logq v w l)) :=
    rLe_congr hone (realEq_refl _) hmono
  -- C·conductor ≈ C·conductor + 0 ≤ C·conductor + bounded（加法両立 + realAdd_zero）
  have hpair : rLe (realAdd (rmul C (szpConductorDeg logq v w l)) realZero)
      (realAdd (rmul C (szpConductorDeg logq v w l)) bounded) :=
    rLe_add_pair (rLe_refl (rmul C (szpConductorDeg logq v w l))) hb
  have h3 : rLe (rmul C (szpConductorDeg logq v w l))
      (realAdd (rmul C (szpConductorDeg logq v w l)) bounded) :=
    rLe_congr (realAdd_zero (rmul C (szpConductorDeg logq v w l))) (realEq_refl _) hpair
  exact rLe_trans h1 (rLe_trans h2 h3)

/-! ## M352F-4: 完全連鎖（crux ⟹ Cor 3.12 ⟹ Szpiro） -/

/-- **定理 (M352F-4): 完全条件付き連鎖 crux ⟹ Cor 3.12 ⟹ Szpiro** — M347F
    `cruxR_implies_cor312`（crux ⟹ 実 Cor 3.12 界）と本層 `szp_cor312_implies_szpiro`
    （実 Cor 3.12 界 ⟹ Szpiro）を合成し、crux 仮説から直接 Szpiro 不等式へ降ろす。
    crux（`cruxRealIneq`）は前件の仮説であって、この連鎖のどの段でも証明されない。
    C ≥ 1・bounded ≥ 0・conductor ≥ 0 の下での条件付き定理。 -/
theorem szp_full_chain (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (C bounded : RReal) (hC : rLe (intToReal 1) C) (hb : rLe realZero bounded)
    (hcond : rLe realZero (szpConductorDeg logq v w l))
    (crux : cruxRealIneq logq v w l) :
    szpSzpiroIneq logq v w l C bounded :=
  szp_cor312_implies_szpiro logq v w l C bounded hC hb hcond
    (cruxR_implies_cor312 logq v w l crux)

/-! ## M352F-5: ABC 形（height ≤ (1+ε)·conductor + O_ε(1)） -/

/-- **M352F-5a: ABC 不等式** — height ≤ (1+ε)·conductor + bounded（両辺実 deg_ℝ）。
    ABC 予想型の高さ・導手不等式を C = 1+ε で特殊化した実対象。ε・bounded は模型 witness。 -/
def szpAbcIneq (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (eps bounded : RReal) : Prop :=
  rLe (szpHeightDeg logq v l)
    (realAdd (rmul (realAdd (intToReal 1) eps) (szpConductorDeg logq v w l)) bounded)

/-- **定理 (M352F-5b): 実 Cor 3.12 界 ⟹ ABC 形** — ε ≥ 0 なら 1 ≤ 1+ε ゆえ、実 Cor 3.12 界
    を前件に、bounded ≥ 0・conductor ≥ 0 の下で ABC 形不等式 height ≤ (1+ε)·conductor+O_ε(1)
    が従う。C = 1+ε として M352F-3 `szp_cor312_implies_szpiro` に還元する。crux は前件。 -/
theorem szp_abc_form (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (eps bounded : RReal) (heps : rLe realZero eps) (hb : rLe realZero bounded)
    (hcond : rLe realZero (szpConductorDeg logq v w l))
    (cor312 : cruxRealCor312Bound logq v w l) :
    szpAbcIneq logq v w l eps bounded := by
  -- 1 ≤ 1+ε（1 = 1+0 ≤ 1+ε・加法両立 + realAdd_zero）
  have hpair : rLe (realAdd (intToReal 1) realZero) (realAdd (intToReal 1) eps) :=
    rLe_add_pair (rLe_refl (intToReal 1)) heps
  have hC : rLe (intToReal 1) (realAdd (intToReal 1) eps) :=
    rLe_congr (realAdd_zero (intToReal 1)) (realEq_refl _) hpair
  exact szp_cor312_implies_szpiro logq v w l (realAdd (intToReal 1) eps) bounded
    hC hb hcond cor312

/-! ## M352F-6: 全連鎖は crux に条件付き（正直な境界） -/

/-- **定理 (M352F-6): 全連鎖は crux に条件付き（Iff.rfl・過大主張の厳禁）** — 本層の Szpiro/ABC
    連鎖の**最深の前件**である crux（`cruxRealIneq`）は、ちょうど M324F 受け取り仮説
    `GaussPilotCruxHyp`（実 deg_ℝ 不等式 thPilotTotalVol ≤ gPilotTotalVol）に一致する
    （それ以上でも以下でもない）。すなわち crux⟹Cor3.12⟹Szpiro の全連鎖は**この外部仮説に
    条件付き**であり、crux（Dβ-ω＝論争の係争点）は本層でも決して証明されない——正直な境界。 -/
theorem szp_crux_still_external (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    cruxRealIneq logq v w l ↔ GaussPilotCruxHyp logq v w l :=
  Iff.rfl

/-- **定理 (M352F-6b): 前件 Cor 3.12 界も crux と両側同値** — M347F `cruxR_mirror` の再輸出:
    Szpiro 還元の前件である実 Cor 3.12 界 `cruxRealCor312Bound` は crux `cruxRealIneq` に
    **両側同値**であり、前件を弱められない——連鎖は本質的に crux に条件付き（局在の鋭さ）。 -/
theorem szp_cor312_iff_crux (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    cruxRealIneq logq v w l ↔ cruxRealCor312Bound logq v w l :=
  cruxR_mirror logq v w l

/-! ## M352F-7: capstone -/

/-- **M352F-7a: Szpiro 還元データ** — 高さ deg_ℝ・導手 deg_ℝ を実対象で束ね、3.12⟹Szpiro
    還元・完全連鎖 crux⟹Szpiro・crux 外部性（条件付き境界）を備える。主語は M319F/M324F の
    実パイロット体積の閉形式であり toy m202fVol を用いない。crux（Dβ-ω）は前件であって
    証明されない。 -/
structure SzpiroReductionData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (C bounded : RReal) where
  /-- 高さ deg_ℝ（deg(q)・テータパイロット LHS 閉形式）。 -/
  height : Nat → RReal
  /-- 導手 deg_ℝ（radical・ガウスパイロット RHS 閉形式）。 -/
  conductor : Nat → RReal
  /-- 高さは szpHeightDeg に一致。 -/
  height_eq : ∀ l, height l = szpHeightDeg logq v l
  /-- 導手は szpConductorDeg に一致。 -/
  conductor_eq : ∀ l, conductor l = szpConductorDeg logq v w l
  /-- **3.12⟹Szpiro 還元**: C≥1・bounded≥0・conductor≥0 の下で実 Cor 3.12 界から Szpiro
      不等式が従う（前件は仮説）。 -/
  cor312_to_szpiro : ∀ l, rLe (intToReal 1) C → rLe realZero bounded →
    rLe realZero (szpConductorDeg logq v w l) →
    cruxRealCor312Bound logq v w l → szpSzpiroIneq logq v w l C bounded
  /-- **完全連鎖**: crux から直接 Szpiro 不等式へ（crux は前件・証明されない）。 -/
  full_chain : ∀ l, rLe (intToReal 1) C → rLe realZero bounded →
    rLe realZero (szpConductorDeg logq v w l) →
    cruxRealIneq logq v w l → szpSzpiroIneq logq v w l C bounded
  /-- **crux 外部性**: 全連鎖は crux（＝M324F 受け取り仮説）に条件付き（Iff.rfl）。 -/
  crux_external : ∀ l, cruxRealIneq logq v w l ↔ GaussPilotCruxHyp logq v w l

/-- **M352F-7b: 実データ** — 全フィールドを M352F-1〜6 の本物で充足。 -/
def szpiroReductionData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (C bounded : RReal) : SzpiroReductionData logq v w C bounded where
  height := szpHeightDeg logq v
  conductor := szpConductorDeg logq v w
  height_eq := fun _ => rfl
  conductor_eq := fun _ => rfl
  cor312_to_szpiro := fun l hC hb hcond cor312 =>
    szp_cor312_implies_szpiro logq v w l C bounded hC hb hcond cor312
  full_chain := fun l hC hb hcond crux =>
    szp_full_chain logq v w l C bounded hC hb hcond crux
  crux_external := fun l => szp_crux_still_external logq v w l

/-- **M352F-7c: 存在（M352F 見出し）** — 任意の実重み logq・素点 v・重み列 w・模型定数 C・
    bounded に対し、高さ・導手を実 deg_ℝ で束ね、3.12⟹Szpiro 還元と完全連鎖 crux⟹Szpiro を
    備えたデータが存在する。crux（Dβ-ω）は外部仮説として明示され、**決して証明されない**
    ——本層は還元（3.12⟹Szpiro）を実内容で本物にするのみ。 -/
theorem szp_exists (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (C bounded : RReal) :
    Nonempty (SzpiroReductionData logq v w C bounded) :=
  ⟨szpiroReductionData logq v w C bounded⟩

/-! ## 実例（l=5, 単位重み: height=deg_ℝ(55), conductor=deg_ℝ(55)・C=1・bounded=0 の退化点） -/

/-- 実例: l=5 の実 Cor 3.12 界から Szpiro 不等式（C=1・bounded=0）が従う（3.12⟹Szpiro 実還元・
    非負重みで conductor≥0 を放電）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (hq : rLe realZero (logq v))
    (cor312 : cruxRealCor312Bound logq v w 5) :
    szpSzpiroIneq logq v w 5 (intToReal 1) realZero :=
  szp_cor312_implies_szpiro logq v w 5 (intToReal 1) realZero
    (rLe_refl _) (rLe_refl _) (szpConductorDeg_nonneg logq v w 5 hq) cor312

/-- 実例: l=5 の crux から直接 Szpiro 不等式（完全連鎖 crux⟹Cor3.12⟹Szpiro・crux は前件）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (hq : rLe realZero (logq v))
    (crux : cruxRealIneq logq v w 5) :
    szpSzpiroIneq logq v w 5 (intToReal 1) realZero :=
  szp_full_chain logq v w 5 (intToReal 1) realZero
    (rLe_refl _) (rLe_refl _) (szpConductorDeg_nonneg logq v w 5 hq) crux

/-- 実例: l=5 の実 Cor 3.12 界から ABC 形 height ≤ (1+ε)·conductor + O_ε(1)（ε=0・退化点）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (hq : rLe realZero (logq v))
    (cor312 : cruxRealCor312Bound logq v w 5) :
    szpAbcIneq logq v w 5 realZero realZero :=
  szp_abc_form logq v w 5 realZero realZero
    (rLe_refl _) (rLe_refl _) (szpConductorDeg_nonneg logq v w 5 hq) cor312

/-- 実例: 全連鎖は crux に条件付き（crux ＝ M324F 受け取り仮説・Iff.rfl）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    cruxRealIneq logq v w 5 ↔ GaussPilotCruxHyp logq v w 5 :=
  szp_crux_still_external logq v w 5

end IUT
