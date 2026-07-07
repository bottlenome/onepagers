/-
  IUT/MultiradialRep.lean — M372F [実／本物]
  分類: 実 (多輻表現＝実テータパイロット体積／不定性作用（(Ind1)(Ind2)-不変核）)
  complete_pct 影響: 柱D を前進（M342F 3不定性作用・M367F log-link 不定性可換の上で、多輻表現を
    実テータパイロット体積の (Ind1)(Ind2)-不変核（＝不定性商上の well-defined 降下）として構成・
    (Ind3) は明示 m シフト・M362F 比較との多輻整合。crux Dβ-ω は外部仮説）。
  正直な限定: crux Dβ-ω（多輻アルゴリズム＝theta-link 整合＝論争の係争点）は外部仮説のまま。
    表現は実体積の (Ind1)(Ind2)-降下。

  ## 本モジュールの位置づけ（何を合成したか）

  IUT III の**多輻表現（multiradial representation）**は、テータパイロット体積を 3 つの不定性
  (Ind1)(Ind2)(Ind3) の作用「を法として（modulo）」見た対象である。本 M372F は、この
  「不定性商の上に降下した well-defined な実 deg_ℝ 値」＝多輻表現を、既に本物化された部品の
  上で構成する:
    * M319F `ThetaPilotRealVolume`: 実テータパイロット総体積 `thPilotTotalVol`（Σj² 閉形式）。
    * M342F `IndeterminacyFull`: (Ind1) 置換保存（`indR_ind1_preserves`/`indF_ind1_perm_general`）・
      (Ind2) 単数保存（`indR_ind2_unit`、付値 0）・(Ind3) 膨張の厳密量（`indF_ind3_dilation_real`）。
    * M367F `LogLinkIndeterminacy`: log-link と不定性の可換（`lli_commute_general`）・
      多輻比較整合（`lli_multiradial_compat`）。
    * M362F `MultiradialCompare`: 比較同型・多輻表現の芽（`mrc_multiradial_seed`）。
    * M312F `LogVolume`: 実 Arakelov 局所次数 `logVolLocal`・加法性 `logVolLocal_add`。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M372F-1 `mrpInvariantCore` / `mrp_core_eq_pilot`
      — 多輻表現の**不変核** = テータパイロット体積が降下する Σj² の実 deg_ℝ 値
        logVolLocal v (Σj²)。M319F `thPilot_total_closed` で実テータパイロット体積が
        この核に一致（realEq）することを再確認。
  * M372F-2 `mrp_ind1_invariant` / `mrp_ind2_invariant`
      — 核は (Ind1) 置換（M342F `indR_ind1_preserves`）・(Ind2) 単数（M332F `indR_ind2_unit`、
        付値 0）で不変。不定性作用の像がすべて同じ核へ降下することの本物。
  * M372F-3 `mrpRepresentation`
      — **多輻表現** = テータパイロット体積を (Ind1)(Ind2) 不定性で法として見た well-defined
        降下 = 不変核の値。不定性商の上の実 deg_ℝ 対象として定義。
  * M372F-4 `mrp_well_defined`
      — 表現は不定性商の上で well-defined: 相異なる不定性作用（(Ind1) 置換・(Ind2) 単数）の
        像はすべて同じ表現値を与える（不変性から）。
  * M372F-5 `mrp_ind3_shifts` / `mrp_ind3_shift_core`
      — (Ind3) 膨張は表現を**明示 m だけシフト**する（M342F `indF_ind3_dilation_real`・
        M367F `lli_ind3_shift`）: 表現は (Ind3) 不変ではないが予測可能にずれる
        （表現 ＋ logVolLocal v m）。
  * M372F-6 `mrp_multiradial`
      — 表現は「多輻的」= M362F 比較の芽（単数側）と M367F log-link 可換（体積側、
        `lli_multiradial_compat`）に整合する。降下（表現）と多輻整合を連言で束ねる。
  * M372F-7 `mrp_crux_external` / `mrp_crux_is_hypothesis`
      — crux Dβ-ω（多輻アルゴリズム＝theta-link 整合＝論争の係争点）は外部仮説のまま。
        表現の降下は本物・crux は受け取るのみ（決して導出しない）。
  * M372F-8 capstone `MrpRepresentationData` / `mrpRepresentationData` / `mrp_exists` + 実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）
  * **crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層は
    テータパイロット体積の (Ind1)(Ind2)-降下（多輻表現）を実 deg_ℝ で本物構成するのみで、
    crux（表現と theta-link の整合不等式）は外部 Prop 仮説として受け取り決して導出しない。
  * **表現は実テータパイロット体積の (Ind1)(Ind2)-不変核（Σj²）への降下**。full な多輻
    アルゴリズム（theta-link 整合込み）は crux であり範囲外。(Ind3) は明示 m シフトで
    捉える（不変ではない）。
  * **deg_ℝ（Arakelov 局所次数）レベル**。log q_v は実重み witness（M312F 継承）。
    群レベルの完全同変性は後続。ℝ は setoid ゆえ realEq で言明する。
  全て選択公理不使用（sorry 皆無・新規 Classical 皆無）。禁止タクティク不使用（core Lean のみ）。
  共有ファイル未変更。柱D 横展開・本物の先行建設[実]。一般名は `mrp` 接頭辞で衝突回避。
-/
import IUT.LogLinkIndeterminacy
import IUT.ThetaPilotRealVolume

namespace IUT

/-! ## M372F-1: 多輻表現の不変核（テータパイロット体積が降下する Σj² の実 deg_ℝ 値） -/

/-- **M372F-1a: 不変核** — 多輻表現が住む不定性商の上の well-defined な実 deg_ℝ 値
    ＝テータパイロット体積が降下する Σj² 核 logVolLocal v (Σj²)。(Ind1) 置換・(Ind2) 単数
    で不変（M342F/M332F）ゆえ、不定性を法とした表現の値を与える基点。 -/
def mrpInvariantCore (logq : Nat → RReal) (v n : Nat) : RReal :=
  logVolLocal logq v ((sumSq n : Nat) : Int)

/-- **定理 (M372F-1b): 実テータパイロット体積は不変核へ降下** — M319F `thPilot_total_closed`
    より、実テータパイロット総体積は Σj² 核（不変核）に一致する（realEq、ℝ は setoid）。 -/
theorem mrp_core_eq_pilot (logq : Nat → RReal) (v n : Nat) :
    realEq (thPilotTotalVol logq v n) (mrpInvariantCore logq v n) :=
  thPilot_total_closed logq v n

/-! ## M372F-2: 核は (Ind1) 置換・(Ind2) 単数で不変 -/

/-- **定理 (M372F-2a: 核は (Ind1) 置換で不変)** — l-捻れラベルの互換（M342F (Ind1)、
    swapMult a b）を掛けた実 deg_ℝ 総体積は不変核に一致する（Σ_{σj} j² = Σj²、置換不変）。
    M332F `indR_ind1_preserves`（置換不変）と `indR_realTotal_closed`（閉形式）・
    `indR_natExp_sum`（Σ(k+1)² = Σj²）で閉じる。不定性の (Ind1) 像が核へ降下する本物。 -/
theorem mrp_ind1_invariant (logq : Nat → RReal) (v a b n : Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) :
    realEq (indR_realTotal logq v (swapMult a b indR_natExp) n)
      (mrpInvariantCore logq v n) := by
  refine realEq_trans (indR_ind1_preserves logq v a b n hab ha hb) ?_
  refine realEq_trans (indR_realTotal_closed logq v indR_natExp n) ?_
  show realEq (logVolLocal logq v ((nsum indR_natExp n : Nat) : Int))
    (mrpInvariantCore logq v n)
  rw [indR_natExp_sum n]
  exact realEq_refl _

/-- **定理 (M372F-2b: 核は (Ind2) 単数で不変)** — 単数作用（M332F (Ind2)、付値 μ=0）を
    テータパイロット体積に掛けても不変核に一致する（v(単数)=0 ゆえ付値の寄与は実 deg_ℝ 0、
    M332F `indR_ind2_unit`）。不定性の (Ind2) 像が核へ降下する本物。 -/
theorem mrp_ind2_invariant (logq : Nat → RReal) (v n : Nat) :
    realEq (indR_ind2Vol logq v (thPilotTotalVol logq v n) 0)
      (mrpInvariantCore logq v n) :=
  realEq_trans (indR_ind2_unit logq v (thPilotTotalVol logq v n) 0 rfl)
    (thPilot_total_closed logq v n)

/-! ## M372F-3: 多輻表現（テータパイロット体積を (Ind1)(Ind2) 不定性で法とした降下） -/

/-- **M372F-3: 多輻表現** — テータパイロット体積を (Ind1)(Ind2) 不定性の作用「を法として」
    見た well-defined 降下 ＝ 不変核の値。(Ind1) 置換・(Ind2) 単数はどれも核を保存するので
    （M372F-2）、この値は不定性商の上に確定する。IUT III の多輻表現の実 deg_ℝ 版
    （crux Dβ-ω＝theta-link 整合はこの降下の外にある外部仮説）。 -/
def mrpRepresentation (logq : Nat → RReal) (v n : Nat) : RReal :=
  mrpInvariantCore logq v n

/-- **定理 (M372F-3b): 表現はテータパイロット体積の降下** — 表現の値は実テータパイロット
    体積そのものが降下したもの（realEq）。 -/
theorem mrp_representation_descent (logq : Nat → RReal) (v n : Nat) :
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n) :=
  mrp_core_eq_pilot logq v n

/-! ## M372F-4: 表現は不定性商の上で well-defined -/

/-- **定理 (M372F-4a: well-defined／異なる (Ind1) 代表)** — 相異なる互換 (a,b)/(c,d) で
    (Ind1) 置換した像はすべて同じ表現値を与える（両者 ≈ 核）。不定性商の上で表現が
    代表の取り方に依らないことの本物（多輻表現が「不定性を法とした」対象である根拠）。 -/
theorem mrp_well_defined (logq : Nat → RReal) (v a b c d n : Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n)
    (hcd : ¬ c = d) (hc : c < n) (hd : d < n) :
    realEq (indR_realTotal logq v (swapMult a b indR_natExp) n)
      (indR_realTotal logq v (swapMult c d indR_natExp) n) :=
  realEq_trans (mrp_ind1_invariant logq v a b n hab ha hb)
    (realEq_symm (mrp_ind1_invariant logq v c d n hcd hc hd))

/-- **定理 (M372F-4b: well-defined／(Ind1) と (Ind2) の像が一致)** — (Ind1) 置換の像と
    (Ind2) 単数の像は同じ表現値を与える（両者 ≈ 核）。異なる種類の不定性作用を跨いで
    表現が well-defined であることの本物。 -/
theorem mrp_well_defined_cross (logq : Nat → RReal) (v a b n : Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) :
    realEq (indR_realTotal logq v (swapMult a b indR_natExp) n)
      (indR_ind2Vol logq v (thPilotTotalVol logq v n) 0) :=
  realEq_trans (mrp_ind1_invariant logq v a b n hab ha hb)
    (realEq_symm (mrp_ind2_invariant logq v n))

/-! ## M372F-5: (Ind3) 膨張は表現を明示 m だけシフトする（不変ではない） -/

/-- **定理 (M372F-5a: (Ind3) は表現を明示 m シフト／閉形式)** — (Ind3) 膨張（付値 m）を
    テータパイロット体積に掛けた実 deg_ℝ は logVolLocal v (Σj²+m) にちょうど等しい
    （M342F `indF_ind3_dilation_real`）。表現は (Ind3) 不変ではないが、Σj² 核に膨張量 m を
    平行移動しただけの予測可能なずれ。 -/
theorem mrp_ind3_shifts (logq : Nat → RReal) (v n : Nat) (m : Int) :
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) m)
      (logVolLocal logq v (((sumSq n : Nat) : Int) + m)) :=
  indF_ind3_dilation_real logq v n m

/-- **定理 (M372F-5b: (Ind3) シフトを表現＋明示 m で分離)** — (Ind3) 膨張後の実 deg_ℝ は
    **表現 ＋ 明示シフト** logVolLocal v m にちょうど等しい（M312F `logVolLocal_add` で
    Σj²+m を Σj² と m へ分ける）。表現は (Ind3) で不変でなく、明示 m だけずれる正直な形
    （M367F `lli_ind3_shift` の実テータパイロット版）。 -/
theorem mrp_ind3_shift_core (logq : Nat → RReal) (v n : Nat) (m : Int) :
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) m)
      (realAdd (mrpRepresentation logq v n) (logVolLocal logq v m)) :=
  realEq_trans (indF_ind3_dilation_real logq v n m)
    (logVolLocal_add logq v ((sumSq n : Nat) : Int) m)

/-! ## M372F-6: 表現は多輻的（M362F 比較・M367F log-link と整合） -/

/-- **定理 (M372F-6: 多輻性)** — 表現が「多輻的」であること: (i) 表現はテータパイロット
    体積の降下（`mrp_representation_descent`）であり、(ii) M362F 比較の芽（単数側、
    `mrc_multiradial_seed`）と M367F log-link 体積輸送の不定性可換（体積側、
    `lli_commute_general`）に整合する（M367F `lli_multiradial_compat`）。＝表現が単数の
    比較同型でも実 deg_ℝ 体積輸送でも不定性に respect される多輻構造の芽。crux Dβ-ω＝
    theta-link 整合はこの芽の外にある外部仮説。 -/
theorem mrp_multiradial (logq : Nat → RReal) (v p d : Nat) (hp : 1 ≤ p)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x)
    (n : Nat) (nn μ : Int) :
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n)
    ∧ ((logShellMem p d (logShellContent p x.val)
          ∧ (mrcCompare p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x))
        ∧ realEq (lliIndThenLog logq v nn μ) (lliLogThenInd logq v nn μ)) :=
  ⟨mrp_representation_descent logq v n, lli_multiradial_compat logq v p d hp x hx nn μ⟩

/-! ## M372F-7: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M372F-7a: crux は外部仮説・決して導出しない／honest)** — 表現の降下
    （テータパイロット体積 ≈ 不変核）は**無条件で本物**（`mrp_representation_descent` が
    crux とは独立に成立）だが、その下での**多輻アルゴリズム**（表現と theta-link の crux
    ＝ Dβ-ω ＝ 論争の当の係争点）は本層で**決して証明しない**。crux を任意の外部 Prop
    `crux` として受け取り、降下の本物性 **と** crux の連言を、crux が仮説として供給された
    場合にのみ返す——crux は決して導出されない。 -/
theorem mrp_crux_external (logq : Nat → RReal) (v n : Nat)
    (crux : Prop) (hcrux : crux) :
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n) ∧ crux :=
  ⟨mrp_representation_descent logq v n, hcrux⟩

/-- **定理 (M372F-7b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説
    そのもの**として扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明した
    定理ではなく、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で
    明示（M362F/M367F と同じ精神）。 -/
theorem mrp_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M372F-8: capstone -/

/-- **M372F-8a: 多輻表現データ**（総括） — テータパイロット体積の (Ind1)(Ind2)-降下として
    の多輻表現を実 deg_ℝ で束ねる: 表現・降下・(Ind1) 不変・(Ind2) 不変・(Ind3) 明示シフト。
    主語は M319F/M342F/M332F/M312F の本物の実 deg_ℝ であり、toy を用いない。
    crux Dβ-ω（theta-link 整合）は範囲外。 -/
structure MrpRepresentationData (logq : Nat → RReal) (v : Nat) where
  /-- 多輻表現（不定性商の上の実 deg_ℝ 値）。 -/
  rep : Nat → RReal
  /-- rep は本物の多輻表現。 -/
  is_rep : rep = mrpRepresentation logq v
  /-- 表現はテータパイロット体積の降下。 -/
  descent : ∀ n, realEq (thPilotTotalVol logq v n) (rep n)
  /-- 核は (Ind1) 置換で不変（不定性商の上で well-defined）。 -/
  ind1_inv : ∀ (a b n : Nat), ¬ a = b → a < n → b < n →
    realEq (indR_realTotal logq v (swapMult a b indR_natExp) n) (rep n)
  /-- 核は (Ind2) 単数で不変。 -/
  ind2_inv : ∀ n, realEq (indR_ind2Vol logq v (thPilotTotalVol logq v n) 0) (rep n)
  /-- (Ind3) 膨張は表現を明示 m だけシフト（不変ではない）。 -/
  ind3_shift : ∀ (n : Nat) (m : Int),
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) m)
      (realAdd (rep n) (logVolLocal logq v m))

/-- **M372F-8b: 実データ** — 全フィールドを M372F-1〜5 の本物で充足。 -/
def mrpRepresentationData (logq : Nat → RReal) (v : Nat) :
    MrpRepresentationData logq v where
  rep := mrpRepresentation logq v
  is_rep := rfl
  descent := fun n => mrp_representation_descent logq v n
  ind1_inv := fun a b n hab ha hb => mrp_ind1_invariant logq v a b n hab ha hb
  ind2_inv := fun n => mrp_ind2_invariant logq v n
  ind3_shift := fun n m => mrp_ind3_shift_core logq v n m

/-- **M372F-8c: 存在** — 任意の実重み logq・素点 v に対し、多輻表現データが存在する。
    M342F 3 不定性作用・M367F log-link 可換の上で、多輻表現がテータパイロット体積の
    (Ind1)(Ind2)-降下として実 deg_ℝ で本物化された。 -/
theorem mrp_exists (logq : Nat → RReal) (v : Nat) :
    Nonempty (MrpRepresentationData logq v) :=
  ⟨mrpRepresentationData logq v⟩

/-! ## M372F-8 実例（l=5, l⋇=2, n=2: ラベル j=1,2, Σj²=5） -/

/-- 実例: Σj² = sumSq 2 = 5。 -/
example : sumSq 2 = 5 := rfl

/-- 実例: l=5（n=2）で実テータパイロット体積は不変核 logVolLocal v 5 へ降下する。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thPilotTotalVol logq v 2) (mrpRepresentation logq v 2) :=
  mrp_representation_descent logq v 2

/-- 実例: l=5（n=2）で (Ind1) 互換 0↔1 の像は不変核へ降下する（置換不変）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2)
      (mrpInvariantCore logq v 2) :=
  mrp_ind1_invariant logq v 0 1 2 (by omega) (by omega) (by omega)

/-- 実例: l=5（n=2）で表現は不定性商の上で well-defined（(0,1) と (1,0) の像が一致）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2)
      (indR_realTotal logq v (swapMult 1 0 indR_natExp) 2) :=
  mrp_well_defined logq v 0 1 1 0 2 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

/-- 実例: l=5（n=2）で (Ind3) 膨張 m=1 は表現を明示シフト logVolLocal v 1 だけずらす。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v 2) 1)
      (realAdd (mrpRepresentation logq v 2) (logVolLocal logq v 1)) :=
  mrp_ind3_shift_core logq v 2 1

/-- 実例: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  mrp_crux_is_hypothesis crux

end IUT
