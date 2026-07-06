/-
  IUT/CruxInequalityReal.lean — M347F [実／本物]
  分類: 実 (crux 不等式 deg(theta-pilot)≤deg(Gauss-pilot) を実 deg_ℝ で精密化・還元)
  complete_pct 影響: 柱D を前進（M249F 模型版 transportDeg_iff_cor312 を実 deg_ℝ（M319F/M324F
    実体積）へ持ち上げ、crux 不等式の形を実対象で精密化し 3.11⟹3.12 の実還元・不定性安定性を
    証明。crux Dβ-ω 自体は外部仮説として明示・決して証明しない）。
  正直な限定: crux Dβ-ω（＝多輻的アルゴリズム＝論争の係争点）は外部 Prop 仮説のみ・Iff.rfl で
    受け取る不等式そのものと明示。
-/

/-
  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  本層は crux 不等式（テータパイロット ≤ ガウスパイロット）の**形**を、M312F の本物の
  実 Arakelov 局所次数 deg_ℝ（`logVolLocal`）と M319F 実テータパイロット総体積
  （`thPilotTotalVol`）・M324F 実ガウスパイロット総体積（`gPilotTotalVol`）の上で**精密化**
  し、その**周り**の同値・還元・不定性安定性を証明する。crux（Dβ-ω）自体は決して証明せず、
  外部 Prop 仮説として受け取る（`cruxR_is_hypothesis` が Iff.rfl で明示）。

  * M347F-1 `cruxRealIneq`
      — **crux 不等式の実対象化**: rLe (実テータパイロット総体積) (実ガウスパイロット総体積)。
        両辺は M319F/M324F の本物の実 deg_ℝ。**定義するだけ・証明しない**。
  * M347F-2 `cruxR_is_hypothesis` / `cruxR_is_indF_hypothesis`
      — **crux は受け取る仮説そのもの**（Iff.rfl）: `cruxRealIneq` はちょうど M324F
        `GaussPilotCruxHyp`・M342F `indF_cruxHyp` に一致し、それ以上でも以下でもない。
        新しく証明した不等式ではなく、論争の係争点をそのまま受け取ったものと機械検証で明示。
  * M347F-3 `cruxRealCor312Bound` / `cruxR_implies_cor312`
      — **実レベルの 3.11⟹3.12 還元**: crux 仮説の下で、閉形式版の実 deg_ℝ 不等式
        deg_ℝ(Σj²) ≤ deg_ℝ(Σ w(k)k²)（Szpiro 型比較の実 Arakelov 次数の影）が従う。
        還元は本物（M319F/M324F 閉形式を rLe_congr で張り替え）・crux は前件。
  * M347F-4 `cruxR_mirror`
      — **両側鏡像**（局在の鋭さ）: `cruxRealIneq ↔ cruxRealCor312Bound`。crux は
        ちょうど閉形式版の係争不等式に**両側同値**であり、これ以上の還元は論争の裁定に等しい。
        M249F `transportDeg_iff_cor312`（模型・次数レベル両側同値）の実 deg_ℝ 版。
  * M347F-5 `cruxR_model_mirror` / `cruxR_degtransport_cor312`
      — **模型レベル鏡像への橋渡し（M249F 再輸出）**: 実 deg_ℝ 上の crux は次数レベル
        transport `ThetaLinkTransportDeg` の実対象への refine であり、模型の両側同値
        （次数 transport ⟺ Cor312）を再輸出して 3.11(deg)⟺3.12 の骨組みを接続する。
  * M347F-6 `cruxR_indeterminacy_stable` / `cruxR_indeterminacy_stable_base`
      — **crux 不等式の形は 3 不定性作用で安定**: (Ind1)∘(Ind2)∘(Ind3) 完全同時作用を
        施したテータパイロット LHS で述べた crux は、hull 代表（M342F `indF_hullVol`）で
        述べた crux に一致（置換代表非依存）。m=0（純 Ind1/Ind2）では元の `cruxRealIneq`
        に一致——不定性は crux の真偽を変えず平行移動するのみ。M342F と接続。
  * M347F-7 capstone `CruxRealData` / `cruxRealData` / `cruxR_exists`。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）

  - **本物（完全証明）**:
    ・crux 不等式の**形**（両辺実 deg_ℝ）・crux が受け取り仮説そのものであること
      （Iff.rfl）・crux 仮説下の閉形式還元（3.11⟹3.12 の実版）・crux ⟺ 閉形式係争
      不等式の両側鏡像・不定性作用下の安定性（置換非依存・m=0 で元と一致）は、全て
      M319F/M324F/M342F/M312F の本物の実 deg_ℝ の上で core Lean のみで完全証明。
  - **正直申告（未達・crux・後続。飾りでなく地図。過大主張の厳禁）**:
    ・**crux Dβ-ω（テータパイロット ≤ ガウスパイロット＝多輻的アルゴリズム＝IUT 論争の
      係争点）は恒久的に本層の範囲外**。本層は crux の**形を実対象で精密化**し、その周りの
      同値・還元・安定性を本物にするのみで、**crux 自体（Dβ-ω）を決して証明しない**。
      `cruxR_is_hypothesis`（Iff.rfl）が「crux はちょうど受け取る不等式であって定理ではない」
      ことを機械検証で明示する。
    ・本層の実 deg_ℝ 上の crux は**次数レベルの影**であり、原論文の crux（点毎輸送
      `ThetaLinkTransport`）は M249F `transport_strictly_stronger` の示す通り**次数 transport
      より真に強い**——真の crux（log-Kummer 輸送の点毎実現）はさらに範囲外。
    ・log q_v（実重み `logq : Nat → RReal`）は M312F/M319F/M324F/M342F と同じく**実重み
      witness**（係数扱い）。log q_v の超越性・具体値は範囲外（柱A/柱C の後続）。
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ閉形式・鏡像・安定性は realEq/rLe で
      言明する（M312F 系と同じ正直な形）。
  全て新規 Classical.choice を証明本体に導入せず（M342F/M324F/M319F/M312F/M249F から継承、
  #print axioms は propext/Quot.sound 系のみ）。sorry 皆無・禁止タクティク不使用（core Lean
  のみ）。一般名は `cruxR` 接頭辞で衝突回避。
-/
import IUT.IndeterminacyFull

namespace IUT

/-! ## M347F-1: crux 不等式の実対象化（定義のみ・決して証明しない） -/

/-- **M347F-1: crux 不等式の実 deg_ℝ 対象化** — テータパイロット総体積（M319F
    `thPilotTotalVol`, LHS）≤ ガウスパイロット総体積（M324F `gPilotTotalVol`, RHS）を、
    **両辺の本物の実 Arakelov 局所次数 deg_ℝ** の上で述べた crux 命題。これは定理3.11 の
    体積不等式（＝Dβ-ω＝多輻的アルゴリズム＝IUT 論争の係争点）であり、その証明は本層の
    **恒久的な範囲外**——本層は crux を仮説として受け取り、その**形を精密化**するのみで、
    **決して証明しない**（`cruxR_is_hypothesis` 参照）。 -/
def cruxRealIneq (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) : Prop :=
  rLe (thPilotTotalVol logq v l) (gPilotTotalVol logq v w (l + 1))

/-! ## M347F-2: crux は受け取る仮説そのもの（Iff.rfl・過大主張の厳禁） -/

/-- **定理 (M347F-2a): crux は M324F 受け取り仮説そのもの**（Iff.rfl）— `cruxRealIneq` は
    ちょうど M324F `GaussPilotCruxHyp`（実 deg_ℝ 不等式 thPilotTotalVol ≤ gPilotTotalVol）
    に一致し、それ以上でも以下でもない。本層は crux をこの仮説として受け取るのみで、
    新しく証明した不等式ではない（過大主張の厳禁の機械検証的明示）。 -/
theorem cruxR_is_hypothesis (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    cruxRealIneq logq v w l ↔ GaussPilotCruxHyp logq v w l :=
  Iff.rfl

/-- **定理 (M347F-2b): crux は M342F 不定性受け取り仮説そのもの**（Iff.rfl）— `cruxRealIneq`
    はちょうど M342F `indF_cruxHyp`（3 不定性層が外部から受ける crux）に一致する。本層の
    crux は不定性層の外部仮説と**同一の Prop** であり、独立に証明されるものではない。 -/
theorem cruxR_is_indF_hypothesis (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    cruxRealIneq logq v w l ↔ indF_cruxHyp logq v w l :=
  Iff.rfl

/-! ## M347F-3: 実レベルの 3.11⟹3.12 還元（crux は前件） -/

/-- **M347F-3a: 実レベルの Cor 3.12 型下界（閉形式）** — 定理3.11 の体積不等式を**両辺の
    実 deg_ℝ 閉形式**で述べた Szpiro 型比較の Arakelov 次数の影:
    deg_ℝ(Σ_{j=1}^{l} j²) ≤ deg_ℝ(Σ_{k≤l} w(k)k²)
    （= logVolLocal v (sumSq l) ≤ logVolLocal v (wssq w l)）。M319F LHS の Σj² 閉形式と
    M324F RHS の Σ w(k)k² 閉形式を突き合わせた実対象の Cor 3.12 型言明。 -/
def cruxRealCor312Bound (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) : Prop :=
  rLe (logVolLocal logq v ((sumSq l : Nat) : Int))
    (logVolLocal logq v ((wssq w l : Nat) : Int))

/-- **定理 (M347F-3b): 実レベルの 3.11⟹3.12 還元（本物・crux は前件）** — crux 仮説
    `cruxRealIneq`（構成した実体積 thPilotTotalVol ≤ gPilotTotalVol）の下で、閉形式版の
    実 Cor 3.12 型下界 `cruxRealCor312Bound`（両辺実 deg_ℝ）が従う。**還元は本物**:
    M319F `thPilot_total_closed`（LHS 閉形式）と M324F `gPilot_total_wssq`（RHS 閉形式）を
    `rLe_congr` で張り替えるだけ——**crux 自体（前件の中身＝Dβ-ω）は証明しない**。 -/
theorem cruxR_implies_cor312 (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (crux : cruxRealIneq logq v w l) :
    cruxRealCor312Bound logq v w l :=
  gPilot_theorem311_conditional logq v w l crux

/-! ## M347F-4: 両側鏡像（局在の鋭さ・crux ⟺ 閉形式係争不等式） -/

/-- **定理 (M347F-4, 本丸): crux の両側鏡像（実 deg_ℝ）** — `cruxRealIneq ↔
    cruxRealCor312Bound`。crux（構成した実総体積の不等式）はちょうど閉形式版の係争
    不等式 deg_ℝ(Σj²) ≤ deg_ℝ(Σ w(k)k²) に**両側同値**であり、これ以上の還元は論争の
    裁定（Dβ-ω）に等しい——局在の鋭さの実対象版。M249F `transportDeg_iff_cor312`（模型・
    次数レベルの両側同値）を実 deg_ℝ へ持ち上げたもの。両方向とも M319F/M324F の閉形式
    （`thPilot_total_closed`・`gPilot_total_wssq`）を `rLe_congr` で張り替えるだけ——
    **crux の真偽そのもの（不等式が成り立つか）は判定しない**。 -/
theorem cruxR_mirror (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    cruxRealIneq logq v w l ↔ cruxRealCor312Bound logq v w l := by
  refine ⟨fun crux => ?_, fun h => ?_⟩
  · exact gPilot_theorem311_conditional logq v w l crux
  · show rLe (thPilotTotalVol logq v l) (gPilotTotalVol logq v w (l + 1))
    exact rLe_congr (realEq_symm (thPilot_total_closed logq v l))
      (realEq_symm (gPilot_total_wssq logq v w l)) h

/-! ## M347F-5: 模型レベル鏡像への橋渡し（M249F 再輸出・骨組み接続） -/

/-- **定理 (M347F-5a): 模型レベル鏡像（M249F 再輸出）** — M249F `transportDeg_iff_cor312`:
    次数レベル transport `ThetaLinkTransportDeg` ⟺ 系3.12（`Cor312 (arithSkeleton …)`）。
    本層の実 deg_ℝ 上の crux `cruxRealCor312Bound` はこの次数レベル crux の**実対象への
    refine**であり、模型の両側同値（3.11(deg)⟺3.12）を再輸出して橋渡しする。両者を厳密に
    橋渡しするのは（真の crux と同じく）範囲外——ここでは既存の還元路を再輸出する。 -/
theorem cruxR_model_mirror (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0) :
    ThetaLinkTransportDeg w n l k₀ hw0 ↔ Cor312 (arithSkeleton w n l B hl hB) :=
  transportDeg_iff_cor312 w n l B k₀ hl hB hw0

/-- **定理 (M347F-5b): 次数レベル crux から系3.12 への還元** — 模型鏡像の順方向:
    次数レベル transport から系3.12 の結論形（Szpiro/ABC 帰結の骨格）へ降ろす。 -/
theorem cruxR_degtransport_cor312 (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0)
    (h : ThetaLinkTransportDeg w n l k₀ hw0) :
    Cor312 (arithSkeleton w n l B hl hB) :=
  (transportDeg_iff_cor312 w n l B k₀ hl hB hw0).mp h

/-! ## M347F-6: crux 不等式の形は 3 不定性作用で安定（M342F と接続） -/

/-- **定理 (M347F-6a): crux の形は完全同時作用で安定（置換代表非依存）** — テータパイロット
    LHS に (Ind1)∘(Ind2)∘(Ind3) 完全同時作用（M342F `indF_full`, 互換 a↔b・単数・膨張 m）を
    施した LHS で述べた crux は、hull 代表（M342F `indF_hullVol` = logVolLocal v (Σj²+m)）で
    述べた crux に**一致**する。Σj² 核が (Ind1)(Ind2) で不変ゆえ crux の形は置換代表 (a,b) に
    依らない。M342F `indF_simultaneous_real` を `rLe_congr` で張り替える。 -/
theorem cruxR_indeterminacy_stable (logq : Nat → RReal) (v : Nat) (a b l : Nat) (m : Int)
    (R : RReal) (hab : ¬ a = b) (ha : a < l) (hb : b < l) :
    rLe (indF_full logq v a b l m) R ↔ rLe (indF_hullVol logq v l m) R := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact rLe_congr (indF_simultaneous_real logq v a b l m hab ha hb) (realEq_refl R) h
  · exact rLe_congr (realEq_symm (indF_simultaneous_real logq v a b l m hab ha hb))
      (realEq_refl R) h

/-- **定理 (M347F-6b): 純 Ind1/Ind2（膨張なし m=0）では元の crux に一致** — 膨張を伴わない
    完全同時作用（置換 Ind1・単数 Ind2, m=0）を施したテータパイロット LHS で述べた crux は、
    ちょうど元の `cruxRealIneq` に一致する。不定性（膨張以外）は crux の真偽を**変えない**
    ——crux の形は不定性の下で安定（well-defined）。M342F の (Ind1)(Ind2) 保存の帰結。 -/
theorem cruxR_indeterminacy_stable_base (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (a b l : Nat) (hab : ¬ a = b) (ha : a < l) (hb : b < l) :
    rLe (indF_full logq v a b l 0) (gPilotTotalVol logq v w (l + 1))
      ↔ cruxRealIneq logq v w l := by
  have hbase : realEq (indF_full logq v a b l 0) (thPilotTotalVol logq v l) := by
    have h1 := indF_simultaneous_real logq v a b l 0 hab ha hb
    have h0 : ((sumSq l : Nat) : Int) + 0 = ((sumSq l : Nat) : Int) := by omega
    rw [h0] at h1
    exact realEq_trans h1 (realEq_symm (thPilot_total_closed logq v l))
  show rLe (indF_full logq v a b l 0) (gPilotTotalVol logq v w (l + 1))
      ↔ rLe (thPilotTotalVol logq v l) (gPilotTotalVol logq v w (l + 1))
  refine ⟨fun h => rLe_congr hbase (realEq_refl _) h,
    fun h => rLe_congr (realEq_symm hbase) (realEq_refl _) h⟩

/-! ## M347F-7: capstone -/

/-- **M347F-7a: crux 実対象データ** — crux 不等式の形を実 deg_ℝ で束ねる: crux が受け取り
    仮説そのものであること（Iff.rfl）・閉形式版係争不等式との両側鏡像・crux 仮説下の
    3.11⟹3.12 還元。主語は M319F/M324F の本物の実 deg_ℝ であり toy m202fVol を用いない。
    crux（Dβ-ω）は仮説であって証明されない。 -/
structure CruxRealData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) where
  /-- crux 不等式（実 deg_ℝ, レベル l ごと）。 -/
  crux : Nat → Prop
  /-- crux はちょうど M324F 受け取り仮説（Iff.rfl・新規証明ではない）。 -/
  crux_is_hyp : ∀ l, crux l ↔ GaussPilotCruxHyp logq v w l
  /-- 両側鏡像: crux ⟺ 閉形式版係争不等式（局在の鋭さ）。 -/
  crux_mirror : ∀ l, crux l ↔ cruxRealCor312Bound logq v w l
  /-- 3.11⟹3.12 実還元: crux 仮説の下で閉形式 Cor 3.12 型下界が従う（前件は仮説）。 -/
  crux_implies_312 : ∀ l, crux l → cruxRealCor312Bound logq v w l

/-- **M347F-7b: 実データ** — 全フィールドを M347F-2〜4 の本物で充足。crux は本層
    `cruxRealIneq`（受け取り仮説）で、同値・還元を実対象で埋める。 -/
def cruxRealData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    CruxRealData logq v w where
  crux := cruxRealIneq logq v w
  crux_is_hyp := fun l => cruxR_is_hypothesis logq v w l
  crux_mirror := fun l => cruxR_mirror logq v w l
  crux_implies_312 := fun l crux => cruxR_implies_cor312 logq v w l crux

/-- **M347F-7c: 存在（M347F 見出し）** — 任意の実重み logq・素点 v・重み列 w に対し、crux
    不等式の形を実 deg_ℝ で精密化し、受け取り仮説との同値・両側鏡像・3.11⟹3.12 還元を
    備えたデータが存在する。crux（Dβ-ω）は外部仮説として明示され、**決して証明されない**
    ——本層は crux の**形を実対象で精密化し、その周りの還元を本物にする**のみ。 -/
theorem cruxR_exists (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    Nonempty (CruxRealData logq v w) :=
  ⟨cruxRealData logq v w⟩

/-! ## 実例（l=5: Σ_{j=1}^{5} j²=55, 単位重み Σ_{k=0}^{5} 1·k²=55 で crux は等号退化点） -/

/-- 実例: crux は受け取り仮説そのもの（Iff.rfl）——新しく証明した不等式ではない。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    cruxRealIneq logq v w 5 ↔ GaussPilotCruxHyp logq v w 5 :=
  cruxR_is_hypothesis logq v w 5

/-- 実例: l=5 の両側鏡像——crux ⟺ 閉形式版係争不等式 deg_ℝ(55) ≤ deg_ℝ(Σ w(k)k²)。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    cruxRealIneq logq v w 5 ↔ cruxRealCor312Bound logq v w 5 :=
  cruxR_mirror logq v w 5

/-- 実例: l=5 の crux 仮説の下で実 Cor 3.12 型下界が従う（3.11⟹3.12 実還元・crux は前件）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (crux : cruxRealIneq logq v w 5) :
    rLe (logVolLocal logq v ((sumSq 5 : Nat) : Int))
      (logVolLocal logq v ((wssq w 5 : Nat) : Int)) :=
  cruxR_implies_cor312 logq v w 5 crux

/-- 実例: l=5（n=2）で完全同時作用（Ind1 互換 0↔1・Ind2・Ind3 膨張 m=1）の crux は
    hull 代表の crux に一致（置換代表非依存の安定性）。 -/
example (logq : Nat → RReal) (v : Nat) (R : RReal) :
    rLe (indF_full logq v 0 1 2 1) R ↔ rLe (indF_hullVol logq v 2 1) R :=
  cruxR_indeterminacy_stable logq v 0 1 2 1 R (by omega) (by omega) (by omega)

/-- 実例: l=5（n=2）で純 Ind1/Ind2（膨張なし）の crux は元の `cruxRealIneq` に一致。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    rLe (indF_full logq v 0 1 2 0) (gPilotTotalVol logq v w 3)
      ↔ cruxRealIneq logq v w 2 :=
  cruxR_indeterminacy_stable_base logq v w 0 1 2 (by omega) (by omega) (by omega)

end IUT
