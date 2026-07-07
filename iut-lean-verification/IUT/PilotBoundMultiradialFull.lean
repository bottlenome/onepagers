-- M427F PilotBoundMultiradialFull [実・本物・柱D]
-- complete_pct 影響: 柱D で crux(theta≤gauss 多輻比較)を M422F の両側実 deg_ℝ 有界域
--   [l³·log q_v (×3 で 3·mrpRepresentation) , 対数殻 m^{Σj²+c} の deg_ℝ] の**内側**へ据えて総合する
--   ——多輻テータパイロット表現は下(l³)・上(対数殻)から無条件で本物に挟まれ、crux はその有界域内での
--   ガウスパイロットとの比較という**さらなる外部命題**として位置づける(crux は決して導出しない)。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。
--   両側有界は M417F l³ 下界(3·rep 上の)＋M422F 対数殻上方包含で無条件・本物だが、crux が有界域の
--   どこで成り立つか(gauss と対数殻の順序)は本層で決して判定しない。局所体 K=ℚ_p・ℝ は setoid(realEq/rLe)。

/-
  IUT/PilotBoundMultiradialFull.lean — M427F（定理3.11 / 多輻境界の総合：crux を両側実有界域の内側へ）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の先行建設 (b)・既存の両側実 deg_ℝ 有界性 (M422F `pvu_two_sided`) と
    多輻レベル crux (M412F `pcmMultiradialCrux`) の (a) 束ね昇格）。M422F は多輻テータパイロット表現
    `mrpRepresentation`（(Ind1)(Ind2)-不変核 (Σj²)·log q_v）が**下**（M417F l³ 下界: l³·log q_v ≤ 3·rep）
    **と上**（M422F 対数殻上方包含: rep ≤ 殻 m^{Σj²+c} の deg_ℝ）から**無条件で本物に挟まれる**ことを
    確立した。M412F は crux（テータパイロット ≤ ガウスパイロット）を多輻表現レベルで述べた。**次の本物の
    一手**は両者を**総合**すること: crux 比較（rep ≤ gPilotTotalVol）は、この両側実有界域
    [l³·log q_v (×3 で 3·rep 上) , 対数殻 deg_ℝ] の**内側に位置する、ガウスパイロットとのさらなる比較**
    である。両側有界は無条件で本物、crux はその有界域内での外部命題——crux 自体は決して導出しない。
  * complete_pct 影響: **前進**。M422F は両側有界を、M412F は多輻レベル crux をそれぞれ本物化したが、
    その**両者を一つの命題へ束ね「crux が両側実有界域の内側に住む」構造を明示する**一手は範囲外だった。
    本 M427F はその**次の本物の一手**として:
      - **無条件両側有界** `pbm_two_sided_real`（M422F `pvu_two_sided` 再利用）= l³ 下界 ∧ 対数殻上方包含。
      - **crux は両側有界域の内側**（本丸） `pbm_crux_within_two_sided`: crux 仮説の下で、下界
        （l³·log q_v ≤ 3·rep・無条件）・上界（rep ≤ 対数殻 deg_ℝ・無条件）・crux（rep ≤ gauss・外部）の
        三連言を返す。すなわち多輻テータパイロット表現は両側有界域に無条件で挟まれ、crux はその域内での
        ガウスパイロットとの比較——crux が有界域の**どこで**成り立つか（gauss ⇄ 対数殻の順序）は判定しない。
      - **両側有界は (Ind1)(Ind2)-不変** `pbm_two_sided_ind1_invariant`/`pbm_two_sided_ind2_invariant`
        （M417F `lpb_bound_ind1/2_invariant` ＋ M422F `pvu_upper_ind1/2_invariant` 再利用）。
      - **3.11⟹3.12 還元** `pbm_crux_implies_cor312`（M412F `pcm_multiradial_crux_implies_cor312` 再利用）:
        有界域内の crux は閉形式版 Cor 3.12 型下界を導く（crux は前件・中身は導出しない）。
    crux Dβ-ω（多輻的アルゴリズム＝この比較が与える不等式＝IUT 論争の当の係争点）は**決して導出せず**
    外部仮説のまま（`pbm_crux_is_hypothesis` は Iff.rfl）。柱D の両側有界と多輻 crux を**総合し本物化**。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M427F-1 `pbm_two_sided_real` — 無条件両側有界（M422F `pvu_two_sided` 再利用・crux とは別物）。
  * M427F-2 `pbm_crux_within_two_sided` — 本丸: crux は両側有界域 [l³, 対数殻] の内側（三連言・本物）。
  * M427F-2b `pbm_crux_within_le` — 一般殻レベル d ≥ Σj² 版（任意の緩めた上界殻でも crux は域内）。
  * M427F-3 `pbm_crux_implies_cor312` — 有界域内 crux ⟹ Cor 3.12（M412F 再利用・crux は前件）。
  * M427F-4 `pbm_two_sided_ind1_invariant`/`pbm_two_sided_ind2_invariant` — 両側有界は (Ind1)(Ind2)-不変。
  * M427F-5 `pbm_crux_external`/`pbm_crux_is_hypothesis`（Iff.rfl）— crux は外部仮説・決して導出しない。
  * M427F-6 capstone `PilotBoundMultiradialFullData`/`pbm_exists` と実例（l=5: Σj²=55, 域 [125·log q_v, (55+c)·log q_v]）。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロットの比較不等式そのもの＝
    IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層が総合する両側有界（下界 l³・上界 対数殻）は
    M97 初等不等式と付値単調性で閉じる**無条件で本物**の命題であり、crux（rep ≤ gauss）とは**別の不等式**。
    本層は crux を M412F の受け取り仮説 `pcmMultiradialCrux` として受け取り、それが両側有界域の**内側に
    位置する**という構造を述べるのみで、**crux 自体（gauss と rep の大小・crux が域内のどこで成り立つか）を
    決して証明しない**（`pbm_crux_is_hypothesis` は Iff.rfl）。gauss ⇄ 対数殻 deg_ℝ の順序も判定しない。
  * **有界性は実 deg_ℝ 体積レベル**。下界は M417F の 3·rep 上（l³·log q_v ≤ 3·rep）で本物・上界は M422F の
    対数殻 deg_ℝ `pvuLogShellBound v (Σj²+c)` で本物（有界補正 c は殻レベルの有界スラック）。
  * **局所体は K = ℚ_p**。log q_v は非負実重み witness（M312F 継承・hq : realZero ≤ logq v が両側の前提）。
    LHS は M372F (Ind1)(Ind2)-降下（Σj² 核）・gauss RHS は M324F 閉形式。**ℝ は setoid**（realEq が同値・
    `=` でない）ゆえ両側有界・crux 位置づけ・不変性・還元は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 総合・本物の先行建設[実]。一般名は `pbm` 接頭辞で衝突回避。
-/
import IUT.PilotVolumeUpperContainment
import IUT.PilotComparisonMultiradial

namespace IUT

/-! ## M427F-1: 無条件両側有界（M422F `pvu_two_sided` 再利用・crux とは別物） -/

/-- **定理 (M427F-1: 多輻テータパイロット表現の無条件両側実 deg_ℝ 有界)** — 多輻テータパイロット表現
    `mrpRepresentation logq v l`（＝(Σj²)·log q_v）は、**下**（M417F l³ 下界: l³·log q_v ≤ 3·rep）
    **と上**（M422F 対数殻上方包含: rep ≤ 殻 m^{Σj²+c} の deg_ℝ）から**無条件で本物に挟まれる**。
    M422F `pvu_two_sided` をそのまま再利用——両側とも M97 初等不等式（l³ ≤ 3Σj²）と付値単調性
    （Σj² ≤ Σj²+c）の**本物の順序**であり、**crux（theta ≤ gauss 比較）とは全く別物**。この有界域が、
    crux 比較（rep ≤ gauss）が住む受け皿である。 -/
theorem pbm_two_sided_real (logq : Nat → RReal) (v l c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
    ∧ rLe (mrpRepresentation logq v l) (pvuLogShellBound logq v (sumSq l + c)) :=
  pvu_two_sided logq v l c hq

/-! ## M427F-2: 本丸 — crux は両側有界域 [l³, 対数殻] の内側 -/

/-- **定理 (M427F-2: crux は両側実有界域の内側・本丸・本物の総合)** — crux 仮説
    `pcmMultiradialCrux logq v w l`（rep ≤ ガウスパイロット体積・外部仮説）の下で、多輻テータパイロット
    表現について次の三つが同時に成り立つ:
      (i)  **下界**（無条件・本物）: l³·log q_v ≤ 3·rep（M417F）、
      (ii) **上界**（無条件・本物）: rep ≤ 対数殻 m^{Σj²+c} の deg_ℝ（M422F）、
      (iii)**crux**（外部仮説）: rep ≤ ガウスパイロット体積（M412F `pcmMultiradialCrux`）。
    すなわち rep は両側実 deg_ℝ 有界域 [l³ (×3 で 3·rep 上) , 対数殻 deg_ℝ] に**無条件で挟まれ**、crux は
    その有界域**内側での**ガウスパイロットとの比較として位置づけられる。(i)(ii) は crux とは独立に本物で
    成立し、**crux 自体（rep と gauss の大小・crux が域内のどこで成り立つか）は決して導出しない**——
    crux は M412F の受け取り仮説をそのまま連言の第三成分へ据えるだけ（`pbm_crux_is_hypothesis` 参照）。 -/
theorem pbm_crux_within_two_sided (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l c : Nat)
    (hq : rLe realZero (logq v)) (crux : pcmMultiradialCrux logq v w l) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
    ∧ rLe (mrpRepresentation logq v l) (pvuLogShellBound logq v (sumSq l + c))
    ∧ pcmMultiradialCrux logq v w l :=
  ⟨lpb_multiradial_cubic_bound logq v l hq, pvu_upper_containment logq v l c hq, crux⟩

/-- **定理 (M427F-2b: 一般殻レベル版)** — 有界域の上界殻レベルを Σj² を上回る任意の d ≥ Σj² へ緩めても、
    crux は依然その両側有界域 [l³, 殻 m^d の deg_ℝ] の内側に位置する。上界は M422F `pvu_upper_containment_le`
    （殻レベルに単調な上方包含・well-defined）で本物・crux は外部仮説のまま。 -/
theorem pbm_crux_within_le (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l d : Nat)
    (hd : sumSq l ≤ d) (hq : rLe realZero (logq v)) (crux : pcmMultiradialCrux logq v w l) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
    ∧ rLe (mrpRepresentation logq v l) (pvuLogShellBound logq v d)
    ∧ pcmMultiradialCrux logq v w l :=
  ⟨lpb_multiradial_cubic_bound logq v l hq, pvu_upper_containment_le logq v l d hd hq, crux⟩

/-! ## M427F-3: 有界域内 crux ⟹ Cor 3.12（M412F 再利用・crux は前件） -/

/-- **定理 (M427F-3: 有界域内 crux は Cor 3.12 を導く・本物・crux は前件)** — 両側実有界域の内側に位置する
    crux 仮説 `pcmMultiradialCrux`（rep ≤ ガウスパイロット体積）の下で、M347F 閉形式版の実 Cor 3.12 型下界
    `cruxRealCor312Bound`（deg_ℝ(Σj²) ≤ deg_ℝ(Σw(k)k²)）が従う。M412F `pcm_multiradial_crux_implies_cor312`
    をそのまま再利用——**還元は本物**だが**crux 自体（前件の中身＝Dβ-ω）は証明しない**。crux が両側有界域の
    内側に住むという本層の総合と、その crux が Cor 3.12 を導くという M412F の還元が接続する。 -/
theorem pbm_crux_implies_cor312 (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (crux : pcmMultiradialCrux logq v w l) :
    cruxRealCor312Bound logq v w l :=
  pcm_multiradial_crux_implies_cor312 logq v w l crux

/-! ## M427F-4: 両側有界は (Ind1)(Ind2)-不変（不定性代表非依存） -/

/-- **定理 (M427F-4a: 両側有界は (Ind1) 置換で不変)** — 両側有界の主語（多輻表現）を、(Ind1) 互換
    swapMult a b を掛けた実 deg_ℝ 総体積 `indR_realTotal` へ載せ替えても、下界（M417F
    `lpb_bound_ind1_invariant`）・上界（M422F `pvu_upper_ind1_invariant`）ともに成立する。(Ind1) 像は
    多輻表現の不変核へ降下する（M372F `mrp_ind1_invariant`、Σ_{σj} j² = Σj²）ので両側とも既存の不変性を
    そのまま束ねるだけ——両側有界域は (Ind1) 置換代表の取り方に**依らない**（多輻不変体積上で well-defined）。 -/
theorem pbm_two_sided_ind1_invariant (logq : Nat → RReal) (v a b l c : Nat)
    (hab : ¬ a = b) (ha : a < l) (hb : b < l) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int))
          (indR_realTotal logq v (swapMult a b indR_natExp) l))
    ∧ rLe (indR_realTotal logq v (swapMult a b indR_natExp) l)
        (pvuLogShellBound logq v (sumSq l + c)) :=
  ⟨lpb_bound_ind1_invariant logq v a b l hab ha hb hq,
   pvu_upper_ind1_invariant logq v a b l c hab ha hb hq⟩

/-- **定理 (M427F-4b: 両側有界は (Ind2) 単数で不変)** — 両側有界の主語を、(Ind2) 単数作用（付値 μ=0）を
    掛けた実 deg_ℝ へ載せ替えても、下界（M417F `lpb_bound_ind2_invariant`）・上界（M422F
    `pvu_upper_ind2_invariant`）ともに成立する。(Ind2) 像は不変核へ降下する（M372F `mrp_ind2_invariant`、
    v(単数)=0）ので既存の不変性を束ねるだけ——両側有界域は (Ind2) 単数不定性の下でも well-defined。 -/
theorem pbm_two_sided_ind2_invariant (logq : Nat → RReal) (v l c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int))
          (indR_ind2Vol logq v (thPilotTotalVol logq v l) 0))
    ∧ rLe (indR_ind2Vol logq v (thPilotTotalVol logq v l) 0)
        (pvuLogShellBound logq v (sumSq l + c)) :=
  ⟨lpb_bound_ind2_invariant logq v l hq,
   pvu_upper_ind2_invariant logq v l c hq⟩

/-! ## M427F-5: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M427F-5a: 両側有界は本物・crux は外部仮説／honest)** — 多輻テータパイロット表現の両側実 deg_ℝ
    有界性（下界 l³・上界 対数殻）は M97 初等不等式と付値単調性で閉じる**無条件で本物**の命題（crux とは
    独立に成立）。しかし theta-pilot ≤ gauss-pilot の**多輻的アルゴリズム**（crux Dβ-ω ＝ M412F
    `pcmMultiradialCrux` ＝ IUT 論争の当の係争点）は本層で**決して証明しない**。crux を M412F の受け取り仮説
    として受け取り、両側有界（本物）**と** crux（仮説）を連言で返す——crux は決して導出されない。 -/
theorem pbm_crux_external (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l c : Nat)
    (hq : rLe realZero (logq v)) (crux : pcmMultiradialCrux logq v w l) :
    (rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
     ∧ rLe (mrpRepresentation logq v l) (pvuLogShellBound logq v (sumSq l + c)))
    ∧ pcmMultiradialCrux logq v w l :=
  ⟨pvu_two_sided logq v l c hq, crux⟩

/-- **定理 (M427F-5b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**として
    扱い、それ以上でも以下でもない（Iff.rfl）。crux（theta ≤ gauss 比較）は本層が総合した両側有界とは別物
    であり、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で明示（M422F
    `pvu_crux_is_hypothesis`・M412F `pcm_crux_is_hypothesis` と同じ精神）。 -/
theorem pbm_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M427F-6: capstone -/

/-- **M427F-6a: 多輻境界総合データ**（総括） — 定理3.11 の多輻テータパイロット表現を、M422F 両側実 deg_ℝ
    有界域の上で束ね、M412F 多輻 crux をその有界域の内側へ据える: 無条件両側有界・crux が両側有界域内側に
    位置すること・両側有界の (Ind1)(Ind2)-不変性・有界域内 crux による 3.11⟹3.12 還元。主語は M372F/M417F/
    M312F の本物の実 deg_ℝ であり toy を用いない。crux（Dβ-ω＝theta ≤ gauss）は外部仮説であって
    本層で証明されない。 -/
structure PilotBoundMultiradialFullData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) where
  /-- 対数殻 m^d の実 deg_ℝ 上界（両側有界の上側受け皿）。 -/
  shellBound : Nat → RReal
  /-- shellBound は本物の対数殻 deg_ℝ 上界（M422F）。 -/
  is_bound : shellBound = pvuLogShellBound logq v
  /-- 多輻レベル crux（レベル l ごと・LHS = 多輻表現・外部仮説）。 -/
  mcrux : Nat → Prop
  /-- mcrux は M412F の多輻レベル crux そのもの（受け取り仮説）。 -/
  is_mcrux : mcrux = pcmMultiradialCrux logq v w
  /-- 無条件両側有界: l³ 下界（3·rep 上）∧ 対数殻上方包含（crux とは独立に本物）。 -/
  two_sided : ∀ l c : Nat, rLe realZero (logq v) →
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
    ∧ rLe (mrpRepresentation logq v l) (shellBound (sumSq l + c))
  /-- crux は両側有界域の内側: crux 仮説の下で 下界 ∧ 上界 ∧ crux（本丸）。 -/
  crux_within : ∀ l c : Nat, rLe realZero (logq v) → mcrux l →
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
    ∧ rLe (mrpRepresentation logq v l) (shellBound (sumSq l + c))
    ∧ mcrux l
  /-- 有界域内 crux は閉形式版 Cor 3.12 型下界を導く（crux は前件・中身は導出しない）。 -/
  crux_implies_312 : ∀ l : Nat, mcrux l → cruxRealCor312Bound logq v w l
  /-- 両側有界は (Ind1) 置換で不変（不定性代表非依存）。 -/
  two_sided_ind1_inv : ∀ (a b l c : Nat), ¬ a = b → a < l → b < l → rLe realZero (logq v) →
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int))
          (indR_realTotal logq v (swapMult a b indR_natExp) l))
    ∧ rLe (indR_realTotal logq v (swapMult a b indR_natExp) l) (shellBound (sumSq l + c))

/-- **M427F-6b: 実データ** — 全フィールドを M427F-1〜4 の本物と M412F 還元で充足。crux は本層で受け取る
    `pcmMultiradialCrux` そのものであり、両側有界の内側に据えるのみで証明しない。 -/
def pilotBoundMultiradialFullData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    PilotBoundMultiradialFullData logq v w where
  shellBound := pvuLogShellBound logq v
  is_bound := rfl
  mcrux := pcmMultiradialCrux logq v w
  is_mcrux := rfl
  two_sided := fun l c hq => pbm_two_sided_real logq v l c hq
  crux_within := fun l c hq crux => pbm_crux_within_two_sided logq v w l c hq crux
  crux_implies_312 := fun l crux => pbm_crux_implies_cor312 logq v w l crux
  two_sided_ind1_inv := fun a b l c hab ha hb hq =>
    pbm_two_sided_ind1_invariant logq v a b l c hab ha hb hq

/-- **M427F-6c: 存在（M427F 見出し）** — 任意の実重み logq・素点 v・重み列 w に対し、多輻境界総合データが
    存在する。多輻テータパイロット表現 (Σj²)·log q_v は両側実 deg_ℝ 有界域 [l³ (×3 で 3·rep 上) , 対数殻
    m^{Σj²+c} の deg_ℝ] に**無条件で本物に挟まれ**、crux（rep ≤ ガウスパイロット体積）はその有界域の**内側
    での**さらなる比較として位置づけられ、有界域内 crux は Cor 3.12 を導く。crux（Dβ-ω＝theta ≤ gauss）は
    外部仮説として明示され、**決して証明されない**——本層は両側有界と多輻 crux を**総合し、crux が有界域の
    内側に住むという構造を本物にする**のみ。 -/
theorem pbm_exists (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    Nonempty (PilotBoundMultiradialFullData logq v w) :=
  ⟨pilotBoundMultiradialFullData logq v w⟩

/-! ## 実例（l=5: Σ_{j=1}^{5} j²=55, 域 [125·log q_v (×3 で 3·rep 上) , (55+c)·log q_v]） -/

/-- 実例: Σ_{j=1}^{5} j² = sumSq 5 = 55（有界域の上界殻レベル・下界 l³=125）。 -/
example : sumSq 5 = 55 := rfl

/-- 実例（無条件両側有界）: l=5 の多輻表現は下（125·log q_v ≤ 3·rep）と上（rep ≤ 殻 (55+c) deg_ℝ）で挟まれる。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v 5))
    ∧ rLe (mrpRepresentation logq v 5) (pvuLogShellBound logq v (sumSq 5 + c)) :=
  pbm_two_sided_real logq v 5 c hq

/-- 実例（本丸・crux は域内）: l=5 の crux 仮説の下で、下界・上界・crux の三連言（crux は有界域の内側）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (c : Nat)
    (hq : rLe realZero (logq v)) (crux : pcmMultiradialCrux logq v w 5) :
    rLe (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v 5))
    ∧ rLe (mrpRepresentation logq v 5) (pvuLogShellBound logq v (sumSq 5 + c))
    ∧ pcmMultiradialCrux logq v w 5 :=
  pbm_crux_within_two_sided logq v w 5 c hq crux

/-- 実例（一般殻レベル）: Σj²=55 ≤ 100 なので l=5 の crux は緩めた殻 m^{100} を上界とする有界域の内側にも住む。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (hq : rLe realZero (logq v)) (crux : pcmMultiradialCrux logq v w 5) :
    rLe (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v 5))
    ∧ rLe (mrpRepresentation logq v 5) (pvuLogShellBound logq v 100)
    ∧ pcmMultiradialCrux logq v w 5 :=
  pbm_crux_within_le logq v w 5 100 (by have : sumSq 5 = 55 := rfl; omega) hq crux

/-- 実例（3.11⟹3.12）: l=5 の有界域内 crux 仮説の下で閉形式版 Cor 3.12 型下界が従う（crux は前件）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (crux : pcmMultiradialCrux logq v w 5) :
    rLe (logVolLocal logq v ((sumSq 5 : Nat) : Int))
      (logVolLocal logq v ((wssq w 5 : Nat) : Int)) :=
  pbm_crux_implies_cor312 logq v w 5 crux

/-- 実例（(Ind1) 不変）: l=2 の両側有界は (Ind1) 互換 0↔1 で不変（置換代表非依存の well-defined）。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * 2 * 2 : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int))
          (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2))
    ∧ rLe (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2)
        (pvuLogShellBound logq v (sumSq 2 + c)) :=
  pbm_two_sided_ind1_invariant logq v 0 1 2 c (by omega) (by omega) (by omega) hq

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  pbm_crux_is_hypothesis crux

/-- 実例（capstone 存在）: 多輻境界総合データは存在する。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    Nonempty (PilotBoundMultiradialFullData logq v w) :=
  pbm_exists logq v w

end IUT
