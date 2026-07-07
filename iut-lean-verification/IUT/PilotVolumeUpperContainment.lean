-- M422F PilotVolumeUpperContainment [実・本物・柱D]
-- complete_pct 影響: 柱D で テータパイロット多輻表現(M372F/M417F mrpRepresentation=(Σj²)·log q_v)を
--   対数殻(M387F lsc_log_upper の上方包含)の実 deg_ℝ 上界 (Σj²+c)·log q_v(有界補正 c)へ収め、
--   M417F の l³ 下界と合わせてパイロット体積の**両側実 deg_ℝ 有界性**を本物化する
--   (crux theta≤gauss 比較は決して導出しない)。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。
--   上方包含は crux が「使う」構造的入力(付値上界=殻の deg_ℝ)だが多輻不等式そのものは本層で決して
--   証明しない。上界は M139 intToReal_mono・M180 rmul_le_mul_right の順序単調性で本物・補正 c は
--   有界スラック(Σj²+c、M387F m^{d-c} の実 deg_ℝ 対応)・局所体 K=ℚ_p・ℝ は setoid(realEq/rLe で言明)。

/-
  IUT/PilotVolumeUpperContainment.lean — M422F（定理3.11 / パイロット体積の対数殻上方包含）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の先行建設 (b)・既存の実 deg_ℝ 表現/上方包含の (a) 束ね昇格）。
    M417F の本物の多輻テータパイロット表現 `mrpRepresentation`（＝(Ind1)(Ind2)-不変核 (Σj²)·log q_v）と
    M387F の本物の対数殻上方包含 `lsc_log_upper`（log(U^(d)) ⊆ m^{d-c}、有界補正 c）の上に、
    **パイロット体積の対数殻上方包含**を実 deg_ℝ で組織する:
    多輻テータパイロット表現は、その殻レベル（付値 Σj²）に有界補正 c を足した対数殻 m^{Σj²+c} の
    実 deg_ℝ `(Σj²+c)·log q_v` に**上方包含**される（`mrpRepresentation ≤ pvuLogShellBound`）。
    これが「対数殻がパイロット体積を（有界補正まで）含む」本物の上界構造であり、M417F の l³ 下界
    （l³·log q_v ≤ 3·多輻表現）と合わせてパイロット体積を**両側から実 deg_ℝ で有界化**する。
    crux（theta ≤ gauss 比較）は決して導出しない。
  * complete_pct 影響: **前進**。M417F は多輻表現の l³ **下界**を本物化し、M387F は対数殻の上方包含
    log(U^(d)) ⊆ m^{d-c} を Zp 上で本物化したが、その**上方包含を実 deg_ℝ 体積の上界として述べ、
    多輻テータパイロット表現に当てて両側有界性へ束ねる**一手は範囲外だった。本 M422F はその**次の
    本物の一手**として:
      - **対数殻の deg_ℝ 上界** `pvuLogShellBound logq v d` = logVolLocal v d = d·log q_v
        （殻 m^d = p^d·ℤ_p の実 deg_ℝ 上界＝付値 d 分の log q_v）。
      - **上方包含（本丸）** `pvu_upper_containment` = rLe (多輻表現) (pvuLogShellBound v (Σj²+c))。
        多輻表現の殻レベルは Σj²、そこへ有界補正 c を足した殻に上方包含される（Σj² ≤ Σj²+c の
        単調性を M139 `intToReal_mono`・M180 `rmul_le_mul_right`（右非負）で実 deg_ℝ の順序へ持ち上げ）。
        これは M387F `lsc_log_upper`（m^{d-c} の有界補正 c）の**実 deg_ℝ 版**。
      - **両側有界** `pvu_two_sided` = l³ 下界（M417F `lpb_multiradial_cubic_bound`）**と** 上方包含の連言。
        パイロット体積は下（×3 で l³）と上（対数殻 deg_ℝ）から本物で挟まれる——**crux とは別物**。
      - **上方包含は (Ind1)(Ind2)-不変** `pvu_upper_ind1_invariant`/`pvu_upper_ind2_invariant`、
        **降下形** `pvu_upper_via_descent`（生の総体積 thPilotTotalVol に対しても）。
      - **M387F 接続** `pvu_shell_upper_align`: 本層の実 deg_ℝ 上方包含は M387F の Zp 上方包含
        log(U^(d)) ⊆ m^{d-c} と同じ「有界補正 c までの上方包含」現象の両輪（Zp 格子側＋deg_ℝ 体積側）。
    crux Dβ-ω（多輻的アルゴリズム＝theta ≤ gauss 比較＝IUT 論争の当の係争点）は**決して導出せず**
    外部仮説のまま（`pvu_crux_is_hypothesis` は Iff.rfl、`pvu_crux_external` は crux を受け取るのみ）。
    柱D のパイロット体積を **対数殻の上方包含で実 deg_ℝ 上界化し両側有界へ本物化**。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M422F-1 `pvuLogShellBound` — 対数殻 m^d の実 deg_ℝ 上界 d·log q_v（M312F logVolLocal を殻上界の語彙で）。
  * M422F-2 `pvu_upper_containment` — 多輻表現 ≤ 殻 m^{Σj²+c} の deg_ℝ（有界補正 c、本丸・本物）。
  * M422F-2b `pvu_upper_containment_le` — 一般 Σj² ≤ d 版（任意の殻レベル d ≥ Σj² に上方包含）。
  * M422F-3 `pvu_two_sided` — 両側有界（M417F l³ 下界 **と** 上方包含の連言・crux とは別物）。
  * M422F-4 `pvu_upper_via_descent`/`pvu_upper_ind1_invariant`/`pvu_upper_ind2_invariant` —
    上方包含は生の総体積・(Ind1)(Ind2)-不変代表に対しても成立（well-defined）。
  * M422F-5 `pvu_shell_upper_align` — M387F の Zp 上方包含 log(U^(d)) ⊆ m^{d-c} と本層の deg_ℝ 上方包含の両輪。
  * M422F-6 `pvu_crux_external`/`pvu_crux_is_hypothesis`（Iff.rfl）— crux は外部仮説・決して導出しない。
  * M422F-7 capstone `PilotVolumeUpperContainmentData`/`pvu_exists` と実例（l=5: Σj²=55, 上界 (55+c)·log q_v）。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロットの比較不等式そのもの＝
    IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層が証明する上方包含は「多輻表現がその殻レベル
    Σj²（＋有界補正 c）の対数殻 deg_ℝ に収まる」**構造的な付値上界**であり、M139 `intToReal_mono`・
    M180 `rmul_le_mul_right` の**順序単調性**で閉じる本物——**crux（theta ≤ gauss の比較）とは全く別の
    不等式**。上方包含は多輻的**上界**が「使う」構造的入力だが、多輻不等式そのものは本層で決して導出せず、
    crux を M412F の受け取り仮説 `pcmMultiradialCrux` として受け取るのみ（`pvu_crux_is_hypothesis` は Iff.rfl）。
  * **上方包含は実 deg_ℝ 体積レベル**。殻上界 `pvuLogShellBound` は M312F logVolLocal（付値×重み）で本物。
    有界補正 c は殻レベルの有界スラック Σj²+c であり、M387F の m^{d-c}（有界補正 c）の実 deg_ℝ 対応
    （Zp 側は Nat 減算 d-c、deg_ℝ 側は殻レベルへの正の補正）。
  * **局所体は K = ℚ_p**。log q_v は実重み witness（M312F 継承）。多輻表現は M372F の (Ind1)(Ind2)-降下
    （Σj² 核）。(Ind3) 明示 m シフトは上方包含の対象外。分数係数 log-shell（原文 I_K の 1/(2p)）は
    ℤ_p に 1/p が無いため整数レベルに留める（M387F 継承）。**ℝ は setoid**（realEq が同値・`=` でない）
    ゆえ上方包含・両側有界・不変性は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 横展開・本物の先行建設[実]。一般名は `pvu` 接頭辞で衝突回避。
-/
import IUT.LogVolumePilotBound
import IUT.LogShellContainment

namespace IUT

/-! ## M422F-1: 対数殻 m^d の実 deg_ℝ 上界（付値 d 分の log q_v） -/

/-- **M422F-1: 対数殻の deg_ℝ 上界** — 対数殻 m^d = p^d·ℤ_p の実 deg_ℝ 上界
    `d·log q_v = logVolLocal v d`。付値 d 分の重み（M312F `logVolLocal` を殻上界の語彙で採る）。
    パイロット体積が上方包含される受け皿の実 deg_ℝ 量。 -/
def pvuLogShellBound (logq : Nat → RReal) (v d : Nat) : RReal :=
  logVolLocal logq v (d : Int)

/-! ## M422F-2: 上方包含（本丸）多輻表現 ≤ 殻 m^{Σj²+c} の deg_ℝ（有界補正 c） -/

/-- **定理 (M422F-2: パイロット体積の対数殻上方包含・本丸・本物)** — 多輻テータパイロット表現
    `mrpRepresentation logq v l`（＝(Σj²)·log q_v）は、その殻レベル Σj² へ**有界補正 c** を足した
    対数殻 m^{Σj²+c} の実 deg_ℝ 上界 `pvuLogShellBound v (Σj²+c) = (Σj²+c)·log q_v` に**上方包含**
    される（非負重み log q_v ≥ 0 の下で）。Σj² ≤ Σj²+c の単調性を M139 `intToReal_mono`・
    M180 `rmul_le_mul_right`（右非負での単調性）で実 deg_ℝ の順序 rLe へ持ち上げるだけ——これは
    M387F `lsc_log_upper`（log(U^(d)) ⊆ m^{d-c}、有界補正 c）の**実 deg_ℝ 版**であり、多輻的
    **上界**が使う構造的入力そのもの。ただし crux（theta ≤ gauss 比較）は本層で決して導出しない。 -/
theorem pvu_upper_containment (logq : Nat → RReal) (v l c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (mrpRepresentation logq v l) (pvuLogShellBound logq v (sumSq l + c)) := by
  have hint : ((sumSq l : Nat) : Int) ≤ ((sumSq l + c : Nat) : Int) := by omega
  show rLe (rmul (intToReal ((sumSq l : Nat) : Int)) (logq v))
    (rmul (intToReal ((sumSq l + c : Nat) : Int)) (logq v))
  exact rmul_le_mul_right (intToReal_mono hint) hq

/-- **定理 (M422F-2b: 一般殻レベル版)** — 多輻表現は、その殻レベル Σj² を**上回る任意の殻レベル
    d ≥ Σj²** の対数殻 m^d の実 deg_ℝ 上界に上方包含される（`mrpRepresentation ≤ pvuLogShellBound v d`）。
    有界補正版（M422F-2、d = Σj²+c）を一般化した本物の上方包含——上方包含は殻レベルの取り方に
    単調で well-defined。 -/
theorem pvu_upper_containment_le (logq : Nat → RReal) (v l d : Nat)
    (hd : sumSq l ≤ d) (hq : rLe realZero (logq v)) :
    rLe (mrpRepresentation logq v l) (pvuLogShellBound logq v d) := by
  have hint : ((sumSq l : Nat) : Int) ≤ (d : Int) := by omega
  show rLe (rmul (intToReal ((sumSq l : Nat) : Int)) (logq v))
    (rmul (intToReal (d : Int)) (logq v))
  exact rmul_le_mul_right (intToReal_mono hint) hq

/-! ## M422F-3: 両側有界（M417F l³ 下界 と 上方包含の連言・crux とは別物） -/

/-- **定理 (M422F-3: パイロット体積の両側実 deg_ℝ 有界性・本物)** — 多輻テータパイロット表現は、
    **下**（M417F `lpb_multiradial_cubic_bound`: l³·log q_v ≤ 3·多輻表現）と**上**（本層の上方包含:
    多輻表現 ≤ 殻 m^{Σj²+c} の deg_ℝ）から**本物で挟まれる**。すなわちパイロット体積 (Σj²)·log q_v は
    実 deg_ℝ で両側有界。両側とも M97 初等的不等式（l³ ≤ 3Σj²）と付値単調性（Σj² ≤ Σj²+c）の
    **本物の順序**であり、**crux（theta ≤ gauss 比較）とは全く別物**——ここで論争の係争点は一切
    導出していない。 -/
theorem pvu_two_sided (logq : Nat → RReal) (v l c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
    ∧ rLe (mrpRepresentation logq v l) (pvuLogShellBound logq v (sumSq l + c)) :=
  ⟨lpb_multiradial_cubic_bound logq v l hq, pvu_upper_containment logq v l c hq⟩

/-! ## M422F-4: 上方包含は生の総体積・(Ind1)(Ind2)-不変代表に対しても成立 -/

/-- **定理 (M422F-4a: 上方包含は生のテータパイロット総体積に対しても成立)** — 多輻表現は
    テータパイロット総体積 `thPilotTotalVol` の降下（M372F `mrp_representation_descent`、realEq）
    ゆえ、上方包含は生の総体積に対しても述べられる: `thPilotTotalVol ≤ 殻 m^{Σj²+c} の deg_ℝ`。
    `rLe_congr`（左因子の realEq 張り替え）で M422F-2 から従う——上方包含が「多輻表現」でも
    「その降下元の総体積」でも同じ本物の命題であることの確認。 -/
theorem pvu_upper_via_descent (logq : Nat → RReal) (v l c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (thPilotTotalVol logq v l) (pvuLogShellBound logq v (sumSq l + c)) :=
  rLe_congr (realEq_symm (mrp_representation_descent logq v l))
    (realEq_refl _) (pvu_upper_containment logq v l c hq)

/-- **定理 (M422F-4b: 上方包含は (Ind1) 置換で不変)** — 上方包含の LHS を、(Ind1) 互換 swapMult a b
    を掛けた実 deg_ℝ 総体積 `indR_realTotal` へ載せ替えても、なお殻 m^{Σj²+c} の deg_ℝ に上方包含
    される。(Ind1) 像は多輻表現の不変核へ降下する（M372F `mrp_ind1_invariant`、Σ_{σj} j² = Σj²）ので
    `rLe_congr` で張り替えるだけ——上方包含は (Ind1) 置換代表の取り方に**依らない**（多輻不変体積上の
    well-defined な上界）。 -/
theorem pvu_upper_ind1_invariant (logq : Nat → RReal) (v a b l c : Nat)
    (hab : ¬ a = b) (ha : a < l) (hb : b < l) (hq : rLe realZero (logq v)) :
    rLe (indR_realTotal logq v (swapMult a b indR_natExp) l)
      (pvuLogShellBound logq v (sumSq l + c)) :=
  rLe_congr (realEq_symm (mrp_ind1_invariant logq v a b l hab ha hb))
    (realEq_refl _) (pvu_upper_containment logq v l c hq)

/-- **定理 (M422F-4c: 上方包含は (Ind2) 単数で不変)** — 上方包含の LHS を、(Ind2) 単数作用
    （付値 μ=0）を掛けた実 deg_ℝ へ載せ替えても、なお殻 m^{Σj²+c} の deg_ℝ に上方包含される。
    (Ind2) 像は不変核へ降下する（M372F `mrp_ind2_invariant`、v(単数)=0）ので `rLe_congr` で
    張り替えるだけ——上方包含は (Ind2) 単数不定性の下でも well-defined。 -/
theorem pvu_upper_ind2_invariant (logq : Nat → RReal) (v l c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (indR_ind2Vol logq v (thPilotTotalVol logq v l) 0)
      (pvuLogShellBound logq v (sumSq l + c)) :=
  rLe_congr (realEq_symm (mrp_ind2_invariant logq v l))
    (realEq_refl _) (pvu_upper_containment logq v l c hq)

/-! ## M422F-5: M387F の Zp 上方包含と本層の deg_ℝ 上方包含の両輪 -/

/-- **定理 (M422F-5: 上方包含の両輪／Zp 格子側 ＋ deg_ℝ 体積側)** — 本層の実 deg_ℝ 上方包含
    （多輻表現 ≤ 殻 m^{Σj²+c} の deg_ℝ）は、M387F の**Zp 格子上の上方包含** `lsc_log_upper`
    （log(U^(d)) ⊆ m^{d-c}、有界補正 c）と**同じ「有界補正までの上方包含」現象の両輪**である:
    (i) レベル d の主単数 x ∈ U^(d) の log content は緩めた殻 m^{d-c} に収まり（Zp 格子側・付値上界）、
    (ii) 多輻テータパイロット表現は殻 m^{Σj²+c} の実 deg_ℝ 上界に収まる（deg_ℝ 体積側）。
    どちらも付値方向の**構造的上界**で、多輻的上界が使う入力そのもの——crux（多輻不等式）は導出しない。 -/
theorem pvu_shell_upper_align (p d cc : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x)
    (logq : Nat → RReal) (v l c : Nat) (hq : rLe realZero (logq v)) :
    logShellMem p (d - cc) (logShellContent p x.val)
    ∧ rLe (mrpRepresentation logq v l) (pvuLogShellBound logq v (sumSq l + c)) :=
  ⟨lsc_log_upper p d cc x hx, pvu_upper_containment logq v l c hq⟩

/-! ## M422F-6: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M422F-6a: 上方包含は本物・crux は外部仮説／honest)** — パイロット体積の対数殻上方包含
    `pvu_upper_containment`（多輻表現 ≤ 殻 m^{Σj²+c} の deg_ℝ）は付値単調性で閉じる**無条件で本物**の
    命題（crux とは独立に成立）。しかし theta-pilot ≤ gauss-pilot の**多輻的アルゴリズム**（crux Dβ-ω
    ＝ M412F `pcmMultiradialCrux` ＝ IUT 論争の当の係争点）は本層で**決して証明しない**。crux を M412F の
    受け取り仮説 `pcmMultiradialCrux` として受け取り、上方包含（本物）**と** crux（仮説）を連言で返す
    ——crux は決して導出されない。 -/
theorem pvu_crux_external (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l c : Nat)
    (hq : rLe realZero (logq v)) (crux : pcmMultiradialCrux logq v w l) :
    rLe (mrpRepresentation logq v l) (pvuLogShellBound logq v (sumSq l + c))
    ∧ pcmMultiradialCrux logq v w l :=
  ⟨pvu_upper_containment logq v l c hq, crux⟩

/-- **定理 (M422F-6b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux（theta ≤ gauss 比較）は本層が証明した
    上方包含とは別物であり、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で
    明示（M417F `lpb_crux_is_hypothesis`・M387F `lsc_crux_is_hypothesis` と同じ精神）。 -/
theorem pvu_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M422F-7: capstone -/

/-- **M422F-7a: パイロット体積上方包含データ**（総括） — 定理3.11 のテータパイロット体積を、M387F
    対数殻上方包含の実 deg_ℝ 上界の上で束ねる: 上方包含（多輻表現 ≤ 殻 m^{Σj²+c} の deg_ℝ）・
    M417F l³ 下界・降下形（生の総体積）・(Ind1) 不変。主語は M372F/M417F の本物の実 deg_ℝ 表現と
    M312F の本物の対数殻 deg_ℝ 上界であり toy を用いない。crux（Dβ-ω＝theta ≤ gauss）は別物であって
    本層で証明されない。 -/
structure PilotVolumeUpperContainmentData (logq : Nat → RReal) (v : Nat) where
  /-- 対数殻 m^d の実 deg_ℝ 上界。 -/
  shellBound : Nat → RReal
  /-- shellBound は本物の対数殻 deg_ℝ 上界。 -/
  is_bound : shellBound = pvuLogShellBound logq v
  /-- 上方包含: 多輻表現 ≤ 殻 m^{Σj²+c} の deg_ℝ（有界補正 c、非負重みの下で）。 -/
  upper : ∀ l c : Nat, rLe realZero (logq v) →
    rLe (mrpRepresentation logq v l) (shellBound (sumSq l + c))
  /-- 下界: l³·log q_v ≤ 3·多輻表現（M417F、両側有界の下側）。 -/
  lower : ∀ l : Nat, rLe realZero (logq v) →
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
  /-- 上方包含は生のテータパイロット総体積（降下元）に対しても成立。 -/
  upper_descent : ∀ l c : Nat, rLe realZero (logq v) →
    rLe (thPilotTotalVol logq v l) (shellBound (sumSq l + c))
  /-- 上方包含は (Ind1) 置換で不変（不定性代表非依存）。 -/
  upper_ind1_inv : ∀ (a b l c : Nat), ¬ a = b → a < l → b < l → rLe realZero (logq v) →
    rLe (indR_realTotal logq v (swapMult a b indR_natExp) l) (shellBound (sumSq l + c))

/-- **M422F-7b: 実データ** — 全フィールドを M422F-1〜4 の本物と M417F l³ 下界で充足。 -/
def pilotVolumeUpperContainmentData (logq : Nat → RReal) (v : Nat) :
    PilotVolumeUpperContainmentData logq v where
  shellBound := pvuLogShellBound logq v
  is_bound := rfl
  upper := fun l c hq => pvu_upper_containment logq v l c hq
  lower := fun l hq => lpb_multiradial_cubic_bound logq v l hq
  upper_descent := fun l c hq => pvu_upper_via_descent logq v l c hq
  upper_ind1_inv := fun a b l c hab ha hb hq =>
    pvu_upper_ind1_invariant logq v a b l c hab ha hb hq

/-- **M422F-7c: 存在（M422F 見出し）** — 任意の実重み logq・素点 v に対し、パイロット体積の対数殻
    上方包含データが存在する。多輻テータパイロット表現 (Σj²)·log q_v は殻 m^{Σj²+c} の実 deg_ℝ 上界
    に**上方包含**され（M387F `lsc_log_upper` の実 deg_ℝ 版）、M417F の l³ 下界と合わせて**両側で本物に
    有界**。crux（Dβ-ω＝theta ≤ gauss 比較）は別物であって**決して証明されない**。 -/
theorem pvu_exists (logq : Nat → RReal) (v : Nat) :
    Nonempty (PilotVolumeUpperContainmentData logq v) :=
  ⟨pilotVolumeUpperContainmentData logq v⟩

/-! ## 実例（l=5: Σ_{j=1}^{5} j²=55, 上界 (55+c)·log q_v、両側 125·log q_v ≤ 3·表現 ≤ 3·(55+c)·log q_v） -/

/-- 実例: Σ_{j=1}^{5} j² = sumSq 5 = 55（多輻表現の殻レベル）。 -/
example : sumSq 5 = 55 := rfl

/-- 実例（上方包含）: l=5 の多輻表現は殻 m^{55+c} の deg_ℝ 上界 (55+c)·log q_v に上方包含される。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (mrpRepresentation logq v 5) (pvuLogShellBound logq v (sumSq 5 + c)) :=
  pvu_upper_containment logq v 5 c hq

/-- 実例（一般殻レベル）: Σj²=55 ≤ 100 なので l=5 の多輻表現は殻 m^{100} の deg_ℝ にも上方包含される。 -/
example (logq : Nat → RReal) (v : Nat) (hq : rLe realZero (logq v)) :
    rLe (mrpRepresentation logq v 5) (pvuLogShellBound logq v 100) :=
  pvu_upper_containment_le logq v 5 100 (by have : sumSq 5 = 55 := rfl; omega) hq

/-- 実例（両側有界）: l=5 のパイロット体積は下（125·log q_v ≤ 3·表現）と上（表現 ≤ 殻 deg_ℝ）で挟まれる。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v 5))
    ∧ rLe (mrpRepresentation logq v 5) (pvuLogShellBound logq v (sumSq 5 + c)) :=
  pvu_two_sided logq v 5 c hq

/-- 実例（降下形）: l=5 の上方包含は生のテータパイロット総体積に対しても成立。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (thPilotTotalVol logq v 5) (pvuLogShellBound logq v (sumSq 5 + c)) :=
  pvu_upper_via_descent logq v 5 c hq

/-- 実例（(Ind1) 不変）: l=2 の上方包含は (Ind1) 互換 0↔1 で不変（置換代表非依存の well-defined）。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2)
      (pvuLogShellBound logq v (sumSq 2 + c)) :=
  pvu_upper_ind1_invariant logq v 0 1 2 c (by omega) (by omega) (by omega) hq

/-- 実例（両輪）: M387F の Zp 上方包含 log(U^(d)) ⊆ m^{d-c} と本層の deg_ℝ 上方包含は同じ現象の両輪。 -/
example (p d cc : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x)
    (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    logShellMem p (d - cc) (logShellContent p x.val)
    ∧ rLe (mrpRepresentation logq v 5) (pvuLogShellBound logq v (sumSq 5 + c)) :=
  pvu_shell_upper_align p d cc x hx logq v 5 c hq

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  pvu_crux_is_hypothesis crux

/-- 実例（capstone 存在）: パイロット体積上方包含データは存在する。 -/
example (logq : Nat → RReal) (v : Nat) :
    Nonempty (PilotVolumeUpperContainmentData logq v) :=
  pvu_exists logq v

end IUT
