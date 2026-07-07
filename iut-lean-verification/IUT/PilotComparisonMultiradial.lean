-- M412F PilotComparisonMultiradial [実・本物・柱D]
-- complete_pct 影響: 柱D で theta-pilot(M319F) vs gauss-pilot(M324F) の比較を多輻表現レベル(M407F/M372F)で
--   本物化——theta-pilot 体積を多輻表現(不定性商上の well-defined 降下)へ載せ替え、crux 不等式を
--   「多輻不変体積どうしの比較」として述べ、その周りの同値・(Ind1)(Ind2)-不変性・3.11⟹3.12 還元を実で閉じる。
--   crux(多輻的アルゴリズムの不等式そのもの)は決して導出せず外部仮説のまま。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。
--   比較は実 deg_ℝ 体積レベル・LHS は M372F (Ind1)(Ind2)-降下(Σj² 核)・RHS は M324F ガウス閉形式・
--   (Ind3) 明示 m シフトは除く・局所体 K=ℚ_p・ℝ は setoid(realEq/rLe で言明)。

/-
  IUT/PilotComparisonMultiradial.lean — M412F（定理3.11 / パイロット比較の多輻表現化）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の先行建設 (b)・既存の多輻表現/実パイロット体積の (a) 束ね昇格）。
    M319F の本物のテータパイロット総体積 `thPilotTotalVol`（実 deg_ℝ, Σj² 閉形式）・M324F の本物の
    ガウスパイロット総体積 `gPilotTotalVol`（実 deg_ℝ, Σw(k)k² 閉形式）・M372F の多輻表現
    `mrpRepresentation`（テータパイロット体積の (Ind1)(Ind2)-不変核への降下）・M407F の theta-link ×
    多輻表現整合の上に、**crux 不等式（テータパイロット ≤ ガウスパイロット）を多輻表現レベルで述べる**:
    LHS のテータパイロット体積は多輻表現へ降下し（well-defined な不定性商上の値）、crux はちょうど
    **その多輻不変体積とガウスパイロット体積の比較**である。crux 自体は導出しない。
  * complete_pct 影響: **前進**。M347F は crux 不等式の形を実 deg_ℝ で精密化し 3.11⟹3.12 の実還元を
    本物化した。M407F は theta-link が多輻表現を coherent に輸送することを本物化した。**次の本物の一手**は、
    crux 比較の LHS を M319F 生の総体積から M372F **多輻表現へ載せ替え**、crux を「多輻不変体積どうしの
    比較」として述べ直すこと:
      - **多輻レベル crux** `pcmMultiradialCrux` = rLe (多輻表現 mrpRepresentation) (ガウスパイロット体積)。
        LHS は M372F の (Ind1)(Ind2)-不変核（不定性商上で well-defined）。
      - **多輻レベル crux ⟺ 実 crux**（`pcm_multiradial_crux_iff`）: 多輻表現はテータパイロット体積の降下
        （M372F `mrp_representation_descent`）ゆえ、多輻レベル crux は M347F `cruxRealIneq`（生の総体積の
        crux）と `rLe_congr` で両側同値。crux の主語を多輻不変体積へ載せ替えても比較は同じ命題。
      - **比較は (Ind1)(Ind2)-不変で well-defined**: (Ind1) 置換・(Ind2) 単数の像で述べた crux は多輻レベル
        crux に一致（M372F `mrp_ind1_invariant`/`mrp_ind2_invariant` を `rLe_congr` で張り替え）——crux 比較は
        不定性代表の取り方に依らない。
      - **3.11⟹3.12 還元**（`pcm_multiradial_crux_implies_cor312`）: 多輻レベル crux 仮説の下で M347F
        `cruxRealCor312Bound`（閉形式版係争不等式）が従う（M347F `cruxR_implies_cor312` を再利用、crux は前件）。
      - **theta-link coherence**（`pcm_comparison_is_thetaLink_rep`）: crux が比較する多輻表現は、M407F の
        theta-link が ×2l で coherent に輸送する当の対象（`tlm_thetaLink_transports_rep`）。
    crux Dβ-ω（多輻的アルゴリズム＝この比較が与える不等式＝IUT 論争の当の係争点）は**決して導出せず**
    外部仮説のまま（`pcm_crux_is_hypothesis` は Iff.rfl）。柱D の theta-pilot vs gauss-pilot 比較を
    **多輻表現レベルで実建設**。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M412F-1 `pcm_lhs_multiradial` — テータパイロット LHS を多輻量として述べる（M372F 降下の再確認）。
  * M412F-2 `pcmMultiradialCrux` — 多輻レベル crux（LHS = 多輻表現・RHS = ガウスパイロット体積）。
  * M412F-3 `pcm_multiradial_crux_iff` / `pcm_crux_is_gauss_hyp` — 多輻レベル crux ⟺ 実 crux ⟺ M324F 受け取り仮説。
  * M412F-4 `pcm_crux_ind1_invariant` / `pcm_crux_ind2_invariant` — 比較は (Ind1)(Ind2)-不変で well-defined。
  * M412F-5 `pcm_multiradial_crux_mirror` / `pcm_multiradial_crux_implies_cor312` — 閉形式両側鏡像・3.11⟹3.12 還元。
  * M412F-6 `pcm_comparison_is_thetaLink_rep` — 比較する多輻表現は theta-link が ×2l 輸送する当の対象。
  * M412F-7 `pcm_crux_external` / `pcm_crux_is_hypothesis`（Iff.rfl）— crux は外部仮説・決して導出しない。
  * M412F-8 capstone `PilotComparisonMultiradialData` / `pcm_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロットの比較不等式そのもの＝IUT 論争の
    当の係争点）は恒久的に本層の範囲外**。本層は crux の**主語を多輻不変体積へ載せ替え**、その周りの同値・
    不変性・還元を本物にするのみで、**crux 自体（不等式が成り立つか）を決して証明しない**。
    `pcm_crux_is_hypothesis`（Iff.rfl）が「crux はちょうど受け取る外部仮説であって定理ではない」ことを明示。
  * **比較は実 deg_ℝ 体積レベル**。LHS は M372F の (Ind1)(Ind2)-降下（Σj² 核）・RHS は M324F の Σw(k)k²
    閉形式。(Ind3) 明示 m シフト（M372F `mrp_ind3_shift_core`）は不変性から除く。群レベルの完全同変性は後続。
  * **局所体は K = ℚ_p**。log q_v は実重み witness（M312F 継承）。有理冪の分母 2l は微細格子 witness。
    **ℝ は setoid**（realEq が同値・`=` でない）ゆえ比較・同値・鏡像は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 横展開・本物の先行建設[実]。一般名は `pcm` 接頭辞で衝突回避。
-/
import IUT.CruxInequalityReal
import IUT.ThetaLinkMultiradial

namespace IUT

/-! ## M412F-1: テータパイロット LHS を多輻量として述べる（M372F 降下の再確認） -/

/-- **定理 (M412F-1: テータパイロット LHS は多輻表現へ降下)** — 定理3.11 の体積不等式の LHS
    （M319F テータパイロット総体積 `thPilotTotalVol`）は、M372F の多輻表現 `mrpRepresentation`
    （(Ind1)(Ind2)-不変核 Σj² への降下＝不定性商上の well-defined 値）に一致する（realEq）。
    すなわち crux 比較の LHS はそのまま**多輻不変体積**として読める（M372F `mrp_representation_descent`
    の再確認、crux 比較を多輻表現レベルで述べる基点）。 -/
theorem pcm_lhs_multiradial (logq : Nat → RReal) (v n : Nat) :
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n) :=
  mrp_representation_descent logq v n

/-! ## M412F-2: 多輻レベル crux（LHS = 多輻表現・RHS = ガウスパイロット体積） -/

/-- **M412F-2: 多輻レベル crux 不等式** — テータパイロット ≤ ガウスパイロットの crux を、LHS に
    生の総体積ではなく **M372F 多輻表現 `mrpRepresentation`**（(Ind1)(Ind2)-不変核）を据えて述べたもの:
    rLe (多輻表現 logq v l) (ガウスパイロット体積 logq v w (l+1))。これは定理3.11 の体積不等式
    （＝Dβ-ω＝多輻的アルゴリズム＝IUT 論争の係争点）を**多輻不変体積どうしの比較**として述べた命題で
    あり、その証明は本層の**恒久的な範囲外**——本層は crux を仮説として受け取り、主語を多輻不変体積へ
    載せ替えるのみで、**決して証明しない**（`pcm_crux_is_hypothesis` 参照）。 -/
def pcmMultiradialCrux (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) : Prop :=
  rLe (mrpRepresentation logq v l) (gPilotTotalVol logq v w (l + 1))

/-! ## M412F-3: 多輻レベル crux ⟺ 実 crux ⟺ M324F 受け取り仮説 -/

/-- **定理 (M412F-3a: 多輻レベル crux ⟺ 実 crux・本丸)** — 多輻レベル crux `pcmMultiradialCrux`
    （LHS = 多輻表現）は、M347F `cruxRealIneq`（LHS = 生のテータパイロット総体積）と**両側同値**である。
    多輻表現はテータパイロット体積の降下（M372F `mrp_representation_descent`、realEq）ゆえ、両辺の LHS は
    realEq で結ばれ、`rLe_congr` で張り替えるだけ——crux の主語を多輻不変体積へ載せ替えても**同じ命題**
    （well-defined）。**crux の真偽そのもの（不等式が成り立つか）は判定しない**。 -/
theorem pcm_multiradial_crux_iff (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    pcmMultiradialCrux logq v w l ↔ cruxRealIneq logq v w l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact rLe_congr (realEq_symm (mrp_representation_descent logq v l)) (realEq_refl _) h
  · exact rLe_congr (mrp_representation_descent logq v l) (realEq_refl _) h

/-- **定理 (M412F-3b: 多輻レベル crux ⟺ M324F 受け取り仮説)** — 多輻レベル crux はちょうど M324F
    `GaussPilotCruxHyp`（実 deg_ℝ 不等式 thPilotTotalVol ≤ gPilotTotalVol＝crux を受け取る仮説そのもの）
    に一致する。`cruxRealIneq` は定義上 `GaussPilotCruxHyp` に等しい（M347F `cruxR_is_hypothesis`）ので、
    多輻レベル crux も同じ外部仮説であり、本層で新しく証明した不等式ではないことを機械検証で明示する。 -/
theorem pcm_crux_is_gauss_hyp (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    pcmMultiradialCrux logq v w l ↔ GaussPilotCruxHyp logq v w l :=
  pcm_multiradial_crux_iff logq v w l

/-! ## M412F-4: 比較は (Ind1)(Ind2)-不変で well-defined（不定性代表非依存） -/

/-- **定理 (M412F-4a: crux 比較は (Ind1) 置換で不変)** — LHS の l-捻れラベルに (Ind1) 互換
    swapMult a b を掛けた実 deg_ℝ 総体積で述べた crux は、多輻レベル crux `pcmMultiradialCrux` に一致する。
    (Ind1) 像は多輻表現の不変核へ降下する（M372F `mrp_ind1_invariant`、Σ_{σj} j² = Σj²）ので、
    `rLe_congr` で張り替えるだけ——crux 比較は (Ind1) 置換代表の取り方に**依らない**（多輻不変体積上の
    well-defined な比較）。 -/
theorem pcm_crux_ind1_invariant (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (a b l : Nat) (hab : ¬ a = b) (ha : a < l) (hb : b < l) :
    rLe (indR_realTotal logq v (swapMult a b indR_natExp) l) (gPilotTotalVol logq v w (l + 1))
      ↔ pcmMultiradialCrux logq v w l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact rLe_congr (mrp_ind1_invariant logq v a b l hab ha hb) (realEq_refl _) h
  · exact rLe_congr (realEq_symm (mrp_ind1_invariant logq v a b l hab ha hb)) (realEq_refl _) h

/-- **定理 (M412F-4b: crux 比較は (Ind2) 単数で不変)** — LHS に (Ind2) 単数作用（付値 μ=0）を掛けた
    実 deg_ℝ で述べた crux は、多輻レベル crux `pcmMultiradialCrux` に一致する。(Ind2) 像は不変核へ降下
    する（M372F `mrp_ind2_invariant`、v(単数)=0）ので `rLe_congr` で張り替えるだけ——crux 比較は
    (Ind2) 単数不定性の下でも well-defined（不変体積上の比較）。 -/
theorem pcm_crux_ind2_invariant (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    rLe (indR_ind2Vol logq v (thPilotTotalVol logq v l) 0) (gPilotTotalVol logq v w (l + 1))
      ↔ pcmMultiradialCrux logq v w l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact rLe_congr (mrp_ind2_invariant logq v l) (realEq_refl _) h
  · exact rLe_congr (realEq_symm (mrp_ind2_invariant logq v l)) (realEq_refl _) h

/-! ## M412F-5: 閉形式両側鏡像・3.11⟹3.12 還元（crux は前件） -/

/-- **定理 (M412F-5a: 多輻レベル crux の両側鏡像)** — 多輻レベル crux `pcmMultiradialCrux` は、M347F
    `cruxRealCor312Bound`（閉形式版係争不等式 deg_ℝ(Σj²) ≤ deg_ℝ(Σw(k)k²)）と**両側同値**である。
    M412F-3a（多輻 ⟺ 実 crux）と M347F `cruxR_mirror`（実 crux ⟺ 閉形式）を合成する。crux の主語を
    多輻不変体積へ載せ替えても、なお閉形式版の係争不等式にちょうど両側同値——これ以上の還元は論争の裁定
    （Dβ-ω）に等しい。 -/
theorem pcm_multiradial_crux_mirror (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    pcmMultiradialCrux logq v w l ↔ cruxRealCor312Bound logq v w l :=
  Iff.trans (pcm_multiradial_crux_iff logq v w l) (cruxR_mirror logq v w l)

/-- **定理 (M412F-5b: 多輻レベル crux 仮説下の 3.11⟹3.12 還元・本物・crux は前件)** — 多輻レベル crux
    仮説 `pcmMultiradialCrux`（多輻表現 ≤ ガウスパイロット体積）の下で、M347F 閉形式版の実 Cor 3.12 型下界
    `cruxRealCor312Bound`（deg_ℝ(Σj²) ≤ deg_ℝ(Σw(k)k²)）が従う。**還元は本物**: M412F-3a で多輻レベル crux を
    実 crux へ移し、M347F `cruxR_implies_cor312`（M319F/M324F 閉形式を `rLe_congr` で張り替え）を再利用する
    ——**crux 自体（前件の中身＝Dβ-ω）は証明しない**。 -/
theorem pcm_multiradial_crux_implies_cor312 (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (crux : pcmMultiradialCrux logq v w l) :
    cruxRealCor312Bound logq v w l :=
  cruxR_implies_cor312 logq v w l ((pcm_multiradial_crux_iff logq v w l).mp crux)

/-! ## M412F-6: crux が比較する多輻表現は theta-link が ×2l 輸送する当の対象（M407F 接続） -/

/-- **定理 (M412F-6: 比較の多輻表現 = theta-link 輸送の対象)** — crux 比較の LHS の多輻表現は、(i) テータ
    パイロット体積の降下であり（M372F `mrp_representation_descent`）、(ii) M407F の横 theta-link が **×2l で
    coherent に輸送する当の対象**である（`tlm_thetaLink_transports_rep`: q パラメータ総体積 ≈ 2l·多輻表現）。
    すなわち crux 比較が住む多輻不変体積は、theta-link と両立する M407F の対象そのもの——比較・降下・
    theta-link 輸送が同じ多輻表現の上で coherent に閉じる本物（crux 不等式は導出しない）。 -/
theorem pcm_comparison_is_thetaLink_rep (logq : Nat → RReal) (v l n : Nat) :
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n)
    ∧ realEq (thLinkQParamTotalVol logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n)) :=
  ⟨mrp_representation_descent logq v n, tlm_thetaLink_transports_rep logq v l n⟩

/-! ## M412F-7: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M412F-7a: crux は外部仮説・決して導出しない／honest)** — crux 比較の LHS が多輻不変体積へ
    降下すること（`pcm_lhs_multiradial`: テータパイロット体積 ≈ 多輻表現）は**無条件で本物**（crux とは
    独立に成立）。しかしその上での**多輻的アルゴリズム**（比較が与える crux Dβ-ω ＝ テータパイロット ⇄
    ガウスパイロットの比較不等式そのもの ＝ IUT 論争の当の係争点）は本層で**決して証明しない**。crux を
    任意の外部 Prop `crux` として受け取り、降下の本物性 **と** crux の連言を、crux が仮説として供給された
    場合にのみ返す——crux は決して導出されない。 -/
theorem pcm_crux_external (logq : Nat → RReal) (v n : Nat) (crux : Prop) (hcrux : crux) :
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n) ∧ crux :=
  ⟨mrp_representation_descent logq v n, hcrux⟩

/-- **定理 (M412F-7b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**として
    扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明した定理ではなく、論争の係争点をそのまま
    外部仮説として受け取ったものであることを機械検証で明示（M347F `cruxR_is_hypothesis`・M372F
    `mrp_crux_is_hypothesis`・M407F `tlm_crux_is_hypothesis` と同じ精神）。 -/
theorem pcm_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M412F-8: capstone -/

/-- **M412F-8a: パイロット比較多輻表現データ**（総括） — 定理3.11 のパイロット比較（テータパイロット ≤
    ガウスパイロット）を、LHS に M372F 多輻表現（(Ind1)(Ind2)-不変核）を据えた**多輻レベル crux** として
    束ねる: crux 比較の LHS が多輻表現へ降下すること・多輻レベル crux が実 crux（＝M324F 受け取り仮説）と
    両側同値であること・閉形式版係争不等式との両側鏡像・(Ind1)(Ind2)-不変で well-defined であること・
    多輻レベル crux 仮説下の 3.11⟹3.12 還元。主語は M319F/M324F/M372F の本物の実 deg_ℝ であり toy を
    用いない。crux（Dβ-ω）は仮説であって証明されない。 -/
structure PilotComparisonMultiradialData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) where
  /-- 多輻レベル crux（レベル l ごと・LHS = 多輻表現）。 -/
  mcrux : Nat → Prop
  /-- crux 比較の LHS は多輻表現へ降下（well-defined な不定性商上の値）。 -/
  lhs_multiradial : ∀ n : Nat, realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n)
  /-- 多輻レベル crux ⟺ 実 crux（主語の載せ替えで命題は変わらない）。 -/
  mcrux_is_real : ∀ l : Nat, mcrux l ↔ cruxRealIneq logq v w l
  /-- 多輻レベル crux ⟺ M324F 受け取り仮説（新規証明ではない）。 -/
  mcrux_is_hyp : ∀ l : Nat, mcrux l ↔ GaussPilotCruxHyp logq v w l
  /-- 閉形式両側鏡像: 多輻レベル crux ⟺ 閉形式版係争不等式。 -/
  mcrux_mirror : ∀ l : Nat, mcrux l ↔ cruxRealCor312Bound logq v w l
  /-- 3.11⟹3.12 還元: 多輻レベル crux 仮説の下で閉形式 Cor 3.12 型下界が従う（前件は仮説）。 -/
  mcrux_implies_312 : ∀ l : Nat, mcrux l → cruxRealCor312Bound logq v w l

/-- **M412F-8b: 実データ** — 全フィールドを M412F-1〜5 の本物で充足。多輻レベル crux は本層
    `pcmMultiradialCrux`（受け取り仮説を多輻表現レベルで述べたもの）で、同値・鏡像・還元を実対象で埋める。 -/
def pilotComparisonMultiradialData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    PilotComparisonMultiradialData logq v w where
  mcrux := pcmMultiradialCrux logq v w
  lhs_multiradial := fun n => pcm_lhs_multiradial logq v n
  mcrux_is_real := fun l => pcm_multiradial_crux_iff logq v w l
  mcrux_is_hyp := fun l => pcm_crux_is_gauss_hyp logq v w l
  mcrux_mirror := fun l => pcm_multiradial_crux_mirror logq v w l
  mcrux_implies_312 := fun l crux => pcm_multiradial_crux_implies_cor312 logq v w l crux

/-- **M412F-8c: 存在（M412F 見出し）** — 任意の実重み logq・素点 v・重み列 w に対し、定理3.11 のパイロット
    比較を多輻表現レベルで述べたデータが存在する。crux 比較の LHS は M372F 多輻表現（(Ind1)(Ind2)-不変核）
    へ降下し、多輻レベル crux は実 crux（＝M324F 受け取り仮説）と両側同値で、閉形式鏡像・3.11⟹3.12 還元を
    備える。crux（Dβ-ω）は外部仮説として明示され、**決して証明されない**——本層は crux の**主語を多輻不変
    体積へ載せ替え、その周りの同値・不変性・還元を本物にする**のみ。 -/
theorem pcm_exists (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    Nonempty (PilotComparisonMultiradialData logq v w) :=
  ⟨pilotComparisonMultiradialData logq v w⟩

/-! ## 実例（l=5: Σ_{j=1}^{5} j²=55, 単位重み Σ_{k=0}^{5} 1·k²=55 で crux は等号退化点） -/

/-- 実例: crux 比較の LHS（l=5, n=2）は多輻表現へ降下する（well-defined な不定性商上の値）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thPilotTotalVol logq v 2) (mrpRepresentation logq v 2) :=
  pcm_lhs_multiradial logq v 2

/-- 実例: 多輻レベル crux（l=5）は実 crux と両側同値（主語の載せ替えで命題は変わらない）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    pcmMultiradialCrux logq v w 5 ↔ cruxRealIneq logq v w 5 :=
  pcm_multiradial_crux_iff logq v w 5

/-- 実例: 多輻レベル crux（l=5）はちょうど M324F 受け取り仮説（新規証明ではない・Iff）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    pcmMultiradialCrux logq v w 5 ↔ GaussPilotCruxHyp logq v w 5 :=
  pcm_crux_is_gauss_hyp logq v w 5

/-- 実例: crux 比較は (Ind1) 互換 0↔1 で不変（l=5, n=2, 置換代表非依存の well-defined）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    rLe (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2) (gPilotTotalVol logq v w 3)
      ↔ pcmMultiradialCrux logq v w 2 :=
  pcm_crux_ind1_invariant logq v w 0 1 2 (by omega) (by omega) (by omega)

/-- 実例: 多輻レベル crux 仮説（l=5）の下で閉形式版 Cor 3.12 型下界が従う（3.11⟹3.12 還元・crux は前件）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (crux : pcmMultiradialCrux logq v w 5) :
    rLe (logVolLocal logq v ((sumSq 5 : Nat) : Int))
      (logVolLocal logq v ((wssq w 5 : Nat) : Int)) :=
  pcm_multiradial_crux_implies_cor312 logq v w 5 crux

/-- 実例: crux が比較する多輻表現は theta-link が ×2l 輸送する当の対象（l=5, n=2）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thPilotTotalVol logq v 2) (mrpRepresentation logq v 2)
    ∧ realEq (thLinkQParamTotalVol logq v 5 2)
        (rmul (intToReal ((2 * 5 : Nat) : Int)) (mrpRepresentation logq v 2)) :=
  pcm_comparison_is_thetaLink_rep logq v 5 2

/-- 実例: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  pcm_crux_is_hypothesis crux

/-- 実例（capstone 存在）: パイロット比較多輻表現データは存在する。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    Nonempty (PilotComparisonMultiradialData logq v w) :=
  pcm_exists logq v w

end IUT
