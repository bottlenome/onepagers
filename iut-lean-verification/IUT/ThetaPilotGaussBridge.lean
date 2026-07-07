-- M418F ThetaPilotGaussBridge [実・本物・柱E]
-- complete_pct 影響: 柱E で M413F の軌道側具体指数蓄積 topbConcreteExpSumNat
--   （Σj² 核）と M324F のガウスパイロット重み付き閉形式 wssq（Σw(k)k² 核）が
--   ともに本物の実 deg_ℝ 閉形式であることを一点で束ね、crux が「具体指数蓄積
--   による deg_ℝ ≤ 重み付き deg_ℝ」という一つの well-posed な実比較として
--   書けること（M324F の crux 命題と同値）を示す。
-- 正直な限定: crux Dβ-ω（theta≤gauss）は恒久的に外部仮説（Iff.rfl で明示するのみ）。
--   log q_v・分母 2l・重み w の実対数化・full 解析的テータ関数値は本層の範囲外。

/-
  IUT/ThetaPilotGaussBridge.lean — M418F [実／本物、柱E]

  ── 主要成果の分類: **[実]**。既存の二つの実橋、M413F（`ThetaOrbitVolumeBridge.lean`、
     `tovb` 接頭辞）と M324F（`GaussPilotRealVolume.lean`、`gPilot` 接頭辞）を
     接続し、これまで結ばれていなかった対を新たに繋ぐ。

  ## 背景（既存の二つの層、本層はこの間の隙間を埋める）

  * M413F は M408F の軌道側具体指数蓄積 `topbConcreteExpSumNat (l+1)`
    （E 側、Laurent 環側単一ラベル実指数の実際の和）が M319F の実テータパイロット
    体積の核 `sumSq l` に一致すること（`tovb_concrete_exp_eq_sumSq`）、および
    実テータパイロット総体積 `thPilotTotalVol` がその具体指数蓄積による
    `logVolLocal` に realEq で一致すること（`tovb_orbit_volume`）を証明した。
    **これは E 側の蓄積と D 側の体積（LHS のみ）を繋ぐ橋であり、ガウスパイロット
    （RHS）には一切触れていない。**
  * M324F は定理3.11 の RHS（ガウスパイロット）を実 deg_ℝ へ昇格し、閉形式
    `gPilot_total_wssq`（`gPilotTotalVol … (l+1) ≈ logVolLocal … (wssq w l)`）を
    証明した上で、crux 命題を `gPilot_crux_statement`（両辺 `sumSq l` /
    `wssq w l` の deg_ℝ 比較）として単離し、`GaussPilotCruxHyp` を明示的仮説
    として受け取る条件付き定理 `gPilot_theorem311_conditional` を閉じた。
    **この crux 命題は M319F の `sumSq` を直接使うのみで、M413F の
    より具体的な E 側オブジェクト `topbConcreteExpSumNat`（軌道積の蓄積指数
    そのもの）を一度も経由していない。**

  すなわち「M413F の軌道側具体指数蓄積 `topbConcreteExpSumNat` を核とする
  crux 命題」と「M324F の `sumSq` を核とする crux 命題」が **同一の実比較で
  あること**、および両核（`topbConcreteExpSumNat` と `wssq`）が **ともに
  本物の実 deg_ℝ 閉形式**であることは、M413F・M324F のいずれの範囲にも
  入っておらず、一度も定理として結ばれていなかった。本層 M418F はその隙間を
  埋める:

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M418F-1 `tpgb_theta_core_closed` — M413F 再輸出。軌道側具体指数蓄積
    `topbConcreteExpSumNat (l+1)` による局所 log-volume が実テータパイロット
    総体積 `thPilotTotalVol` に realEq で一致すること（`tovb_orbit_volume`）。
    E 側の核が本物の実 deg_ℝ 閉形式であることの確認。
  * M418F-2 `tpgb_gauss_core_closed` — M324F 再輸出。重み付き閉形式核
    `wssq w l` による局所 log-volume がガウスパイロット総体積 `gPilotTotalVol`
    に realEq で一致すること（`gPilot_total_wssq`）。RHS の核が本物の実 deg_ℝ
    閉形式であることの確認。
  * M418F-3 本丸 `tpgb_pilot_cores` — 両核を一つの命題に束ねる: 軌道側具体
    指数蓄積 `topbConcreteExpSumNat (l+1)`（E 側、M413F 経由で本物の
    Σj² 核）による deg_ℝ が `thPilotTotalVol` に realEq で一致し、かつ
    重み付き核 `wssq w l`（D 側、本物の Σw(k)k² 核）による deg_ℝ が
    `gPilotTotalVol` に realEq で一致する、という連言。**両者がともに
    real closed-form Σ-square 核であることの単一の witness**。
  * M418F-4 crux 外部仮説 `ThetaPilotGaussCruxHyp` — 軌道側具体指数蓄積を
    核とする deg_ℝ が重み付き核 `wssq w l` の deg_ℝ 以下であるという、
    crux の**明示的仮説**（Prop）。証明しない。
  * M418F-5 `tpgb_crux_iff_gPilot` — 本層の crux 仮説 `ThetaPilotGaussCruxHyp`
    が M324F の `gPilot_crux_statement`（`sumSq` を核とする crux 命題）と
    **外延的に同値**であること（`tovb_concrete_exp_eq_sumSq` による核の書換え
    のみで閉じる、Iff）。E 側の具体指数蓄積で述べた crux が、D 側の `sumSq`
    で述べた既存の crux とちょうど同じ実比較であることの本物の同定——
    crux 自体は証明しない。
  * M418F-6 `tpgb_crux_is_hypothesis` — `ThetaPilotGaussCruxHyp` が定義上
    ちょうどこの deg_ℝ 比較であること（Iff.rfl）。crux が仮説であって
    定理でないことの機械検証的明示。
  * M418F-7 capstone `ThetaPilotGaussBridgeData` / `thetaPilotGaussBridgeData` /
    `tpgb_exists` — 上記を一つの witness レコードに束ね、任意の logq・v・w・l
    に対する存在を示す。
  * M418F-8 実例（l=5: 両核の具体値・crux 仮説の同値性）。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）

  - **本物（完全証明）**: M413F の軌道側具体指数蓄積 `topbConcreteExpSumNat`
    による deg_ℝ 閉形式と、M324F の重み付き核 `wssq` による deg_ℝ 閉形式は、
    ともに本層で machine-checked に再確認される。両核を核とする crux 命題
    （本層の `ThetaPilotGaussCruxHyp` と M324F の `gPilot_crux_statement`）が
    外延的に同値であることも本物（`tovb_concrete_exp_eq_sumSq` の核書換えの
    みで閉じる、新規の数学的仮説は導入しない）。
  - **正直申告（未達・witness・後続。飾りでなく地図）**:
    ・**crux 不等式（Dβ-ω・多輻的アルゴリズム＝IUT 論争の係争点）は
      恒久的に本層の範囲外**——`ThetaPilotGaussCruxHyp` は仮説として
      受け取るのみで、本層はそれを証明しない（`tpgb_crux_is_hypothesis` が
      Iff.rfl でそのことを明示する）。
    ・log q_v（重み witness）・分母 2l（微細格子 u=q^{1/2l}）・重み関数 w の
      実対数化は M319F/M324F と同じく witness のまま——本層はそれらの
      実在・超越性には一切触れない。
    ・全ラベルの解析的エタールテータ関数値そのもの・p 進収束・tempered π₁^ét
      による軌道の実現は M368F/M373F/M398F/M403F/M408F/M413F と同様に
      外部仮説として継承し、本層は一切導出しない。
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ体積側の同定は realEq で
      言明する（M413F/M319F/M324F と同じ正直な形）。

  選択公理不使用（新規 Classical.choice なし；継承分の propext/Quot.sound のみ）。
  sorry 皆無・禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/
  positivity/conv/nth_rewrite/field_simp）不使用。許可タクティク（cases/obtain/
  induction/rw/show/refine/exact/apply/intro/generalize/funext/omega）のみ使用。
  共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
  一般名は `tpgb` 接頭辞で衝突回避。
-/
import IUT.ThetaOrbitVolumeBridge
import IUT.GaussPilotRealVolume

namespace IUT

/-! ## M418F-1: E 側の核（軌道側具体指数蓄積）は本物の実 deg_ℝ 閉形式（M413F 再輸出） -/

/-- **定理 (M418F-1: E 側核の deg_ℝ 閉形式、M413F 再輸出)** — 実テータ
    パイロット総体積 `thPilotTotalVol logq v l` は、M413F の軌道側具体指数
    蓄積 `topbConcreteExpSumNat (l+1)`（E 側、Laurent 環側単一ラベル実指数の
    実際の和）による局所 log-volume に realEq で一致する（`tovb_orbit_volume`
    の再輸出）。crux 比較の LHS 核が本物の実 deg_ℝ 閉形式であることの確認。 -/
theorem tpgb_theta_core_closed (logq : Nat → RReal) (v : Nat) (l : Nat) :
    realEq (thPilotTotalVol logq v l)
      (logVolLocal logq v ((topbConcreteExpSumNat (l + 1) : Nat) : Int)) :=
  tovb_orbit_volume logq v l

/-! ## M418F-2: D 側の核（ガウスパイロット重み付き閉形式）は本物の実 deg_ℝ 閉形式
    （M324F 再輸出） -/

/-- **定理 (M418F-2: D 側核の deg_ℝ 閉形式、M324F 再輸出)** — ガウスパイロット
    総体積 `gPilotTotalVol logq v w (l+1)` は、M324F の重み付き閉形式核
    `wssq w l`（Σ_{k≤l} w(k)·k²）による局所 log-volume に realEq で一致する
    （`gPilot_total_wssq` の再輸出）。crux 比較の RHS 核が本物の実 deg_ℝ
    閉形式であることの確認。 -/
theorem tpgb_gauss_core_closed (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (l : Nat) :
    realEq (gPilotTotalVol logq v w (l + 1))
      (logVolLocal logq v ((wssq w l : Nat) : Int)) :=
  gPilot_total_wssq logq v w l

/-! ## M418F-3: 本丸——両核を一つの命題に束ねる -/

/-- **定理 (M418F-3: 本丸——両 Σ-square 核の deg_ℝ 閉形式を束ねる)** —
    軌道側具体指数蓄積 `topbConcreteExpSumNat (l+1)`（E 側、M413F 経由で
    本物の Σj² 核）による局所 log-volume が実テータパイロット総体積に
    realEq で一致し、**かつ**重み付き核 `wssq w l`（D 側、本物の Σw(k)k² 核）
    による局所 log-volume がガウスパイロット総体積に realEq で一致する、
    という連言。両者がともに real closed-form Σ-square 核であることの
    単一の witness——crux（両核の deg_ℝ 比較）が well-posed な実比較で
    あることの本物の下地。crux 不等式そのものはここでは述べない。 -/
theorem tpgb_pilot_cores (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    realEq (thPilotTotalVol logq v l)
      (logVolLocal logq v ((topbConcreteExpSumNat (l + 1) : Nat) : Int))
    ∧ realEq (gPilotTotalVol logq v w (l + 1))
      (logVolLocal logq v ((wssq w l : Nat) : Int)) :=
  ⟨tpgb_theta_core_closed logq v l, tpgb_gauss_core_closed logq v w l⟩

/-! ## M418F-4/5/6: crux——外部仮説として明示・M324F の crux 命題との外延同値 -/

/-- **M418F-4: crux 外部仮説（明示的仮説・証明しない）** — 軌道側具体指数蓄積
    `topbConcreteExpSumNat (l+1)`（E 側、M413F の本物の核）による局所
    log-volume が、重み付き核 `wssq w l`（D 側、M324F の本物の核）による
    局所 log-volume 以下であるという crux 命題。これは定理3.11 の体積不等式
    （＝Dβ-ω＝多輻的アルゴリズム＝IUT 論争の係争点）を E 側の具体指数蓄積の
    言葉で述べたものであり、その証明は本タスクの**恒久的な範囲外**——本層は
    crux を仮説として受け取るのみ（`tpgb_crux_is_hypothesis` 参照）。 -/
def ThetaPilotGaussCruxHyp (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (l : Nat) : Prop :=
  rLe (logVolLocal logq v ((topbConcreteExpSumNat (l + 1) : Nat) : Int))
    (logVolLocal logq v ((wssq w l : Nat) : Int))

/-- **定理 (M418F-5: crux 仮説は M324F の crux 命題と外延的に同値)** —
    本層の crux 仮説 `ThetaPilotGaussCruxHyp`（E 側の具体指数蓄積
    `topbConcreteExpSumNat (l+1)` を核とする deg_ℝ 比較）は、M324F の
    `gPilot_crux_statement`（`sumSq l` を核とする deg_ℝ 比較）と**外延的に
    同値**である。M413F `tovb_concrete_exp_eq_sumSq`（`topbConcreteExpSumNat
    (l+1) = sumSq l`）による核の書換えのみで閉じる（新規の数学的仮説を
    一切導入しない）。E 側の具体指数蓄積で述べた crux が、D 側の `sumSq`
    で述べた既存の crux（M324F）とちょうど同じ実比較であることの本物の
    同定——crux 自体（不等式の真偽）は本定理の範囲外のまま。 -/
theorem tpgb_crux_iff_gPilot (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (l : Nat) :
    ThetaPilotGaussCruxHyp logq v w l ↔ gPilot_crux_statement logq v w l := by
  show rLe (logVolLocal logq v ((topbConcreteExpSumNat (l + 1) : Nat) : Int))
      (logVolLocal logq v ((wssq w l : Nat) : Int))
    ↔ rLe (logVolLocal logq v ((sumSq l : Nat) : Int))
      (logVolLocal logq v ((wssq w l : Nat) : Int))
  rw [tovb_concrete_exp_eq_sumSq l]

/-- **定理 (M418F-6: crux が仮説であることの明示)** — `ThetaPilotGaussCruxHyp`
    は定義上ちょうど実 deg_ℝ 不等式「(E 側具体指数蓄積の deg_ℝ) ≤
    (重み付き核 wssq の deg_ℝ)」であり、**それ以上でも以下でもない**
    （Iff.rfl）。本層は crux をこの仮説として受け取るのみで、**証明はしない**
    （過大主張の厳禁の機械検証的明示）。 -/
theorem tpgb_crux_is_hypothesis (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (l : Nat) :
    ThetaPilotGaussCruxHyp logq v w l
      ↔ rLe (logVolLocal logq v ((topbConcreteExpSumNat (l + 1) : Nat) : Int))
          (logVolLocal logq v ((wssq w l : Nat) : Int)) :=
  Iff.rfl

/-! ## M418F-7: capstone -/

/-- **M418F-7a: テータパイロット・ガウス橋データ** — 与えられた実重み logq・
    素点 v・重み関数 w・ラベル数 l に対し、(i) E 側核（軌道側具体指数蓄積）が
    本物の実 deg_ℝ 閉形式であること、(ii) D 側核（重み付き wssq）が本物の
    実 deg_ℝ 閉形式であること、(iii) 本層の crux 仮説が M324F の crux 命題と
    外延的に同値であること、を一括で束ねる。E 側（M413F）と D 側（M324F）が
    「両者ともに real closed-form Σ-square 核であり、crux はその一意な実
    比較である」という一点で出会うことの witness。 -/
structure ThetaPilotGaussBridgeData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (l : Nat) where
  /-- E 側核（軌道側具体指数蓄積）の deg_ℝ 閉形式。 -/
  theta_core_closed : realEq (thPilotTotalVol logq v l)
    (logVolLocal logq v ((topbConcreteExpSumNat (l + 1) : Nat) : Int))
  /-- D 側核（重み付き wssq）の deg_ℝ 閉形式。 -/
  gauss_core_closed : realEq (gPilotTotalVol logq v w (l + 1))
    (logVolLocal logq v ((wssq w l : Nat) : Int))
  /-- 本層の crux 仮説は M324F の crux 命題と外延的に同値。 -/
  crux_equiv : ThetaPilotGaussCruxHyp logq v w l ↔ gPilot_crux_statement logq v w l

/-- **M418F-7b: witness 本体** — 各フィールドを M418F-1〜5 の主定理で埋める。 -/
def thetaPilotGaussBridgeData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (l : Nat) : ThetaPilotGaussBridgeData logq v w l where
  theta_core_closed := tpgb_theta_core_closed logq v l
  gauss_core_closed := tpgb_gauss_core_closed logq v w l
  crux_equiv := tpgb_crux_iff_gPilot logq v w l

/-- **定理 (M418F-7c: capstone——テータパイロット・ガウス橋データの存在)** —
    任意の実重み logq・素点 v・重み関数 w・ラベル数 l に対し、M413F の
    E 側具体指数蓄積核と M324F の D 側重み付き核が、ともに本物の実 deg_ℝ
    閉形式として同一の橋データに束ねられ、crux（両核の deg_ℝ 比較）が
    well-posed な実比較として単一の仮説に単離される。E 側の蓄積された
    軌道指数と D 側のガウスパイロット体積を、M413F・M324F の実オブジェクトを
    経由して直接対峙させるという本モジュールの主張が閉じる。 -/
theorem tpgb_exists (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    Nonempty (ThetaPilotGaussBridgeData logq v w l) :=
  ⟨thetaPilotGaussBridgeData logq v w l⟩

/-! ## M418F-8: 実例（l=5: E 側核 topbConcreteExpSumNat 6 = sumSq 5 = 55、
    D 側核 wssq (単位重み) 5 = 55、crux 仮説の同値性） -/

/-- 実例: l=5 で E 側核（軌道側具体指数蓄積）`topbConcreteExpSumNat 6` は
    D 側の `sumSq 5 = 55` に一致する（M413F `tovb_concrete_exp_eq_sumSq`
    の再確認）。 -/
example : topbConcreteExpSumNat 6 = sumSq 5 := tovb_concrete_exp_eq_sumSq 5

example : topbConcreteExpSumNat 6 = 55 := tovb_concrete_exp_eq_sumSq 5

/-- 実例: 単位重み w≡1 のガウスパイロット D 側核 `wssq 5 = 55`
    （E 側核と一致——crux が等号で退化する正規化点）。 -/
example : wssq (fun _ => 1) 5 = 55 := rfl

/-- 実例: l=5 で E 側核による deg_ℝ が実テータパイロット総体積に一致する
    （`tpgb_theta_core_closed`）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thPilotTotalVol logq v 5)
      (logVolLocal logq v ((topbConcreteExpSumNat 6 : Nat) : Int)) :=
  tpgb_theta_core_closed logq v 5

/-- 実例: l=5・単位重みで D 側核による deg_ℝ がガウスパイロット総体積に
    一致する（`tpgb_gauss_core_closed`）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (gPilotTotalVol logq v (fun _ => 1) 6)
      (logVolLocal logq v ((wssq (fun _ => 1) 5 : Nat) : Int)) :=
  tpgb_gauss_core_closed logq v (fun _ => 1) 5

/-- 実例: l=5・単位重みで本層の crux 仮説は M324F の crux 命題と同値である
    （`tpgb_crux_iff_gPilot`）。 -/
example (logq : Nat → RReal) (v : Nat) :
    ThetaPilotGaussCruxHyp logq v (fun _ => 1) 5
      ↔ gPilot_crux_statement logq v (fun _ => 1) 5 :=
  tpgb_crux_iff_gPilot logq v (fun _ => 1) 5

/-- 実例: l=5・単位重みで橋データが本物で存在する（`tpgb_exists`）。 -/
example (logq : Nat → RReal) (v : Nat) :
    Nonempty (ThetaPilotGaussBridgeData logq v (fun _ => 1) 5) :=
  tpgb_exists logq v (fun _ => 1) 5

end IUT
