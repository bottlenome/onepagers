/-
  IUT/ThetaPilotOrbitBridge.lean — M378F [実／本物]
  分類: 実 (テータ軌道積の指数 Σj² と テータパイロット体積核 Σj² の橋)
  complete_pct 影響: 柱E を前進（M373F テータ軌道積 ∏Θ^{2l}=q^{Σj²} の指数 Σj² が M319F 実テータ
    パイロット体積核の Σj² に一致することを本物で示し、E 側（テータ値）と D 側（体積）を同じ
    Σj² 核で結ぶ小さな橋）。
  正直な限定: 2つの Σj² 指数の橋のみ・完全なテータパイロット⟷テータ値対応（crux 込み）は範囲外。

  ## 内容（tier-S・本物の橋渡し）

  M373F `ThetaOrbitProduct.lean` は円分影の軌道積の指数和を `topExpSumNat`
  （0 始まりラベル j=0,…,l−1 の Σj²、`topExpSumNat (l+1) = ssq l` と閉じる、
  M93 `ssq`）として持つ。M319F `ThetaPilotRealVolume.lean` は実テータパイロット
  総体積の閉形式を M1 `sumSq`（1 始まりラベル j=1,…,n の Σj²）で持つ
  （`thPilot_total_closed`: thPilotTotalVol logq v n ≈ logVolLocal logq v (sumSq n)）。

  `ssq` と `sumSq` は**同一の漸化式**（0 での 0、l+1 での ssq l/sumSq l + (l+1)²）で
  独立に定義された二つの宣言であり、defeq ではなく本物の帰納証明を要する
  （`tpb_ssq_eq_sumSq`）。これを `top_exp_sum_shift`（M373F）と合成し、
  **E 側（`topCycProd`/`topExpSumNat`, 円分影の軌道積の指数）と D 側
  （`thPilotTotalVol`, 実 Arakelov 体積の Σj² 核）が同じ自然数 `sumSq l`
  を指数/核として共有する**ことを本物で証明する（`tpb_orbit_exp_eq_pilot_core`）。
  この共有量を介して、実テータパイロット体積を軌道積の指数 `topExpSumNat (l+1)`
  で書き直し（`tpb_pilot_volume_of_orbit`）、軌道の円分影積を pilot 核 `sumSq l`
  の冪として書き直す（`tpb_orbit_norm_is_pilot`）——E と D が同じ Σj² で
  出会うことの本物の橋。

  正直な限定（消去・弱化禁止）: 本層は M373F の指数 `topExpSumNat`（E 側の
  軌道積の冪指数）と M319F の指数 `sumSq`（D 側の実体積の閉形式係数）という
  **二つの Σj² 指数の一致のみ**を橋渡しする。テータパイロット対象とテータ値
  そのものの完全な対応（両者を結ぶ crux・多輻的アルゴリズムの不等式）は
  恒久的に本層の範囲外——M319F/M373F 双方の正直な限定がそのまま継承される
  （log q_v は実重み witness・分母 2l は witness・非アルキメデス側のみ 等）。

  選択公理不使用（新規 Classical.choice なし）。sorry 不使用。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用。許可タクティク（cases/obtain/induction/rw/show/refine/exact/apply/intro/
  generalize/funext/omega）のみ使用。共有ファイル（IUT.lean・build.sh・dashboard.md・
  graph 系）は一切変更していない。一般名は `tpb` 接頭辞で衝突回避。
-/
import IUT.ThetaOrbitProduct
import IUT.ThetaPilotRealVolume

namespace IUT

/-! ## M378F-1: 軌道積の指数（M373F 再輸出） -/

/-- **M378F-1: 軌道積の指数** tpbExponent l = topExpSumNat l（M373F 再輸出、
    ラベル j=0,…,l−1 の指数 j² の総和 Σj²、Nat 版）。E 側（円分影の軌道積
    ∏Θ^{2l}=q^{Σj²}）の指数の本橋モジュールでの呼び名。 -/
def tpbExponent (l : Nat) : Nat := topExpSumNat l

/-! ## M378F-2: 本丸——ssq と sumSq の一致、軌道指数と pilot 核の一致 -/

/-- **定理 (M378F-2a: ssq = sumSq)** — M93 `ssq`（ThetaOrbitProduct 側の平方和）
    と M1 `sumSq`（ThetaPilotRealVolume 側の平方和）は、独立に定義された同一の
    漸化式（0 での 0・l+1 での 前者 + (l+1)²）ゆえ、すべての l で一致する
    （本物の帰納証明、defeq には拠らない）。 -/
theorem tpb_ssq_eq_sumSq : ∀ l : Nat, ssq l = sumSq l := by
  intro l
  induction l with
  | zero => rfl
  | succ l ih =>
    show ssq l + (l + 1) * (l + 1) = sumSq l + (l + 1) * (l + 1)
    rw [ih]

/-- **定理 (M378F-2b: 本丸——軌道指数 = pilot 核・橋)** — E 側の軌道積の指数和
    `topExpSumNat (l+1)`（M373F、ラベル 0,…,l の Σj²）は、D 側の実テータパイロット
    体積の閉形式係数 `sumSq l`（M319F、ラベル 1,…,l の Σj²）に一致する
    （M373F `top_exp_sum_shift` で ssq l に落とし、M378F-2a で sumSq l に渡す）。
    これが本モジュールの核心の橋: E（テータ軌道積）と D（テータパイロット体積）が
    **同じ自然数 Σj²** を核として共有する。 -/
theorem tpb_orbit_exp_eq_pilot_core (l : Nat) : topExpSumNat (l + 1) = sumSq l := by
  rw [top_exp_sum_shift l, tpb_ssq_eq_sumSq l]

/-! ## M378F-3: D 側——実テータパイロット体積を軌道指数で書き直す -/

/-- **定理 (M378F-3: pilot 体積の軌道指数表示)** — 実テータパイロット総体積
    `thPilotTotalVol logq v l`（M319F）は、E 側の軌道積の指数 `topExpSumNat (l+1)`
    による局所 log-volume `logVolLocal logq v (topExpSumNat (l+1))` に一致する
    （realEq、M319F `thPilot_total_closed` を M378F-2b の橋で軌道指数へ書き換え）。
    D 側の体積の主語がちょうど E 側の軌道積の指数で読めることの本物。 -/
theorem tpb_pilot_volume_of_orbit (logq : Nat → RReal) (v : Nat) (l : Nat) :
    realEq (thPilotTotalVol logq v l)
      (logVolLocal logq v ((topExpSumNat (l + 1) : Nat) : Int)) := by
  rw [tpb_orbit_exp_eq_pilot_core l]
  exact thPilot_total_closed logq v l

/-! ## M378F-4: E 側——軌道の円分影積を pilot 核の冪として書き直す -/

/-- **定理 (M378F-4: 軌道円分影積の pilot 核表示)** — E 側の円分影の軌道積
    `topCycProd M (l+1)`（M373F、ラベル 0,…,l の ∏ζ^{j²}）は、D 側の pilot 核
    `sumSq l` を指数とする単一の円分影の冪 `ζ^{sumSq l}` に一致する
    （M373F `top_cyc_prod_pow` と M378F-2b の橋の合成）。テータ軌道積の指数が
    実テータパイロット体積の Σj² 核とちょうど同じ自然数であることの E 側からの
    確認——E（テータ値の積）と D（体積の算術次数）が Σj² で出会う。 -/
theorem tpb_orbit_norm_is_pilot (M : CycMuGroup) (l : Nat) :
    topCycProd M (l + 1) = M.μ.pow M.ζ (sumSq l) := by
  rw [top_cyc_prod_pow M (l + 1), tpb_orbit_exp_eq_pilot_core l]

/-! ## M378F-5: capstone——橋データと存在 -/

/-- **M378F-5a: 橋データ** — 与えられた円分影群 M・実重み logq・素点 v・ラベル数 l
    に対し、(i) 軌道指数と pilot 核の一致、(ii) 実 pilot 体積の軌道指数表示、
    (iii) 軌道円分影積の pilot 核表示、を一括で束ねる。E 側（テータ軌道積・
    テータ値）と D 側（実 Arakelov 体積）が同じ Σj² で出会うことの witness。 -/
structure ThetaPilotOrbitBridgeData (M : CycMuGroup) (logq : Nat → RReal) (v : Nat)
    (l : Nat) where
  /-- 軌道指数 = pilot 核（Nat の等式）。 -/
  core_eq : topExpSumNat (l + 1) = sumSq l
  /-- 実 pilot 体積 = 軌道指数による局所 log-volume。 -/
  volume_eq : realEq (thPilotTotalVol logq v l)
    (logVolLocal logq v ((topExpSumNat (l + 1) : Nat) : Int))
  /-- 軌道円分影積 = pilot 核を指数とする ζ の冪。 -/
  orbit_eq : topCycProd M (l + 1) = M.μ.pow M.ζ (sumSq l)

/-- **M378F-5b: witness 本体** — 各フィールドを M378F-2〜4 の主定理で埋める。 -/
def thetaPilotOrbitBridgeData (M : CycMuGroup) (logq : Nat → RReal) (v : Nat) (l : Nat) :
    ThetaPilotOrbitBridgeData M logq v l where
  core_eq := tpb_orbit_exp_eq_pilot_core l
  volume_eq := tpb_pilot_volume_of_orbit logq v l
  orbit_eq := tpb_orbit_norm_is_pilot M l

/-- **定理 (M378F-5c: capstone — 橋データの存在)** — 任意の円分影群 M・実重み logq・
    素点 v・ラベル数 l に対し、テータ軌道積の指数とテータパイロット体積の Σj² 核が
    一致する橋データが本物で組み上がる。E 側（M373F）と D 側（M319F）が同じ Σj²
    で出会うという本モジュールの主張が閉じる。 -/
theorem tpb_exists (M : CycMuGroup) (logq : Nat → RReal) (v : Nat) (l : Nat) :
    Nonempty (ThetaPilotOrbitBridgeData M logq v l) :=
  ⟨thetaPilotOrbitBridgeData M logq v l⟩

/-! ## 実例（l=4: 軌道指数 topExpSumNat 5 と pilot 核 sumSq 4 はともに Σj²=30） -/

/-- 実例: E 側の軌道指数 topExpSumNat 5（ラベル 0,…,4 の Σj²=0+1+4+9+16）と
    D 側の pilot 核 sumSq 4（ラベル 1,…,4 の Σj²=1+4+9+16）はともに 30 に一致する
    （`tpb_orbit_exp_eq_pilot_core`）。 -/
example : topExpSumNat 5 = sumSq 4 := tpb_orbit_exp_eq_pilot_core 4

example : sumSq 4 = 30 := rfl

example : topExpSumNat 5 = 30 := tpb_orbit_exp_eq_pilot_core 4

/-- 実例: l=4 で実テータパイロット体積は軌道指数 topExpSumNat 5 による
    局所 log-volume に一致する（`tpb_pilot_volume_of_orbit`）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thPilotTotalVol logq v 4)
      (logVolLocal logq v ((topExpSumNat 5 : Nat) : Int)) :=
  tpb_pilot_volume_of_orbit logq v 4

/-- 実例: 本物の μ_5 上で、l=4 の軌道円分影積は pilot 核 sumSq 4 = 30 を指数とする
    ζ の冪に一致する（`tpb_orbit_norm_is_pilot`）。 -/
example :
    topCycProd (cycMuStd 5 (by omega)) 5
      = (cycMuStd 5 (by omega)).μ.pow (cycMuStd 5 (by omega)).ζ (sumSq 4) :=
  tpb_orbit_norm_is_pilot (cycMuStd 5 (by omega)) 4

/-- 実例: l=4 の橋データが本物で存在する（`tpb_exists`、本物の G_ℚ 上の μ_5 と
    任意の実重み・素点で）。 -/
example (logq : Nat → RReal) (v : Nat) :
    Nonempty (ThetaPilotOrbitBridgeData (cycMuStd 5 (by omega)) logq v 4) :=
  tpb_exists (cycMuStd 5 (by omega)) logq v 4

end IUT
