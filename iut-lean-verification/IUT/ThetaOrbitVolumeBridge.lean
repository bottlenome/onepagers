-- M413F ThetaOrbitVolumeBridge [実・本物・柱E]
-- complete_pct 影響: 柱E で M408F の具体指数和 topbConcreteExpSumNat（M403F/M398F
--   Laurent 環側単一ラベル指数 (thLtorExp j).toNat の実蓄積）が M319F 実テータパイロット
--   体積の Σj² 核 sumSq に本物で一致し、その体積そのものを軌道側の具体蓄積指数による
--   log-volume として書けることを示す（E 側の蓄積と D 側の体積が同じ核で出会う）。
-- 正直な限定: crux 不等式（Dβ-ω・多輻的アルゴリズム、ガウスパイロットとの突き合わせ）と
--   テータ値の解析的実体・log q_v の超越性は本層の範囲外のまま継承する。

/-
  IUT/ThetaOrbitVolumeBridge.lean — M413F [実／本物、柱E]

  ── 主要成果の分類: **[実]**。既存の二つの実橋、M408F（`ThetaOrbitProductBridge.lean`、
     `topb` 接頭辞）と M378F（`ThetaPilotOrbitBridge.lean`、`tpb` 接頭辞）を合成し、
     これまで結ばれていなかった対を新たに繋ぐ。

  ## 背景（既存の二つの橋、本層はこの間の隙間を埋める）

  * M408F は M403F/M398F の Laurent 環側単一ラベル具体指数 `(thLtorExp (j:Int)).toNat`
    （j=0,…,l−1）の有限和を `topbConcreteExpSumNat` として定義し、それが M373F の
    直書き総指数 `topExpSumNat` に一致すること（`topb_concrete_exp_sum_eq`）、
    ひいては `topbConcreteExpSumNat (l+1) = ssq l`（`topb_orbit_sum`、M93 `ssq`）を
    証明した。**これは E 側の「単一ラベル具体指数の蓄積」と「M373F の総指数」を
    繋ぐ橋であり、D 側（体積）にはまだ触れていない。**
  * M378F は M373F の `ssq` と M319F（`ThetaPilotRealVolume.lean`）の `sumSq`
    （実テータパイロット総体積 `thPilotTotalVol` の閉形式係数）が同一の漸化式ゆえ
    一致すること（`tpb_ssq_eq_sumSq`）を示し、`topExpSumNat (l+1) = sumSq l`
    （`tpb_orbit_exp_eq_pilot_core`）を経由して実体積を **M373F の直書き総指数**
    `topExpSumNat (l+1)` で書き直した（`tpb_pilot_volume_of_orbit`）。**この橋は
    M373F の総指数を経由するのみで、M408F の具体指数蓄積 `topbConcreteExpSumNat`
    そのものには触れていない。**

  すなわち「M408F の具体指数蓄積（単一ラベルの Laurent 環側実指数の和という、
  M373F の直書きより一段具体的な実オブジェクト）が、M319F の実 Arakelov 体積
  `thPilotTotalVol` の核そのものと一致し、その体積を具体指数蓄積による
  log-volume として書ける」ことは、M408F・M378F のいずれの範囲にも入っておらず、
  一度も定理として結ばれていなかった。本層 M413F はその隙間を埋める:

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M413F-1 `tovb_concrete_exp_eq_sumSq` — M408F の具体指数蓄積
    `topbConcreteExpSumNat (l+1)` が M319F の体積核 `sumSq l` に一致すること
    （M408F `topb_orbit_sum`: `topbConcreteExpSumNat (l+1) = ssq l` と M378F
    `tpb_ssq_eq_sumSq`: `ssq l = sumSq l` を合成した本物の推移律）。
  * M413F-2 本丸 `tovb_orbit_volume` — 実テータパイロット総体積
    `thPilotTotalVol logq v l`（M319F、D 側の実 Arakelov 局所次数）が、
    M408F の具体指数蓄積 `topbConcreteExpSumNat (l+1)`（E 側、単一ラベルの
    Laurent 環側実指数の実蓄積）による局所 log-volume に realEq で一致する
    ことを示す。M413F-1 の橋で `sumSq l` を `topbConcreteExpSumNat (l+1)` に
    書き換え、M319F `thPilot_total_closed` に渡す。**軌道積側の「具体的に
    蓄積された」指数 Σj² が、そのままテータパイロット実体積の核であること**
    の本物の同定——E 側の蓄積 (M408F) と D 側の体積 (M319F) が M413F-1 を
    介して出会う。
  * M413F-3 `tovb_orbit_cyc_via_concrete` — 円分影の有限積 `topCycProd M (l+1)`
    （M373F の実オブジェクト、μ_l の元）が、M408F `topb_cyc_prod_concrete_exp`
    により具体指数蓄積 `topbConcreteExpSumNat (l+1)` を指数とする ζ の冪に
    一致することの再輸出（capstone データの一部として、E 側の円分影積も
    同じ具体指数蓄積で読めることを束ねるために用いる）。
  * M413F-4 capstone `ThetaOrbitVolumeBridgeData`/`thetaOrbitVolumeBridgeData`/
    `tovb_exists` — 上記三つ（具体指数=体積核、実体積=具体指数の log-volume、
    円分影積=具体指数の冪）を一つの witness レコードに束ね、任意の M・logq・v・l
    に対する存在を示す。
  * M413F-5 実例（l=4: `topbConcreteExpSumNat 5 = sumSq 4 = 30`、対応する
    実体積の同定と円分影積の同定）。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）

  - **本物（完全証明）**: M408F の具体指数蓄積 `topbConcreteExpSumNat`（単一
    ラベルの Laurent 環側実指数 `thLtorExp` の toNat の実際の和）が M319F の
    実 Arakelov 体積 `thPilotTotalVol` の Σj² 核と一致し、体積そのものを
    その具体指数蓄積による `logVolLocal` として書けること、および円分影の
    有限積が同じ具体指数蓄積を指数とする冪として書けることは、本層で
    machine-checked に閉じる（M408F/M378F/M319F からの合成のみ・新規の
    数学的仮説は導入しない）。
  - **正直申告（未達・witness・後続。飾りでなく地図）**:
    ・log q_v（重み witness）・分母 2l（微細格子 u=q^{1/2l}）は M319F と同じく
      witness のまま——本層はそれらの実在・超越性には一切触れない。
    ・ガウスパイロット（定理3.11 RHS）との crux 不等式（Dβ-ω・多輻的
      アルゴリズム＝IUT 論争の係争点）は M319F/M378F と同様、恒久的に本層の
      範囲外。本層は E 側の具体指数蓄積と D 側の体積核の**同定**のみを行い、
      crux（LHS と RHS の突き合わせ）の証明ではない。
    ・全ラベルの解析的エタールテータ関数値そのもの・p 進収束・tempered π₁^ét
      による軌道の実現は M368F/M373F/M398F/M403F/M408F と同様に外部仮説として
      継承し、本層は一切導出しない。
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ体積側の同定は realEq で
      言明する（M319F/M378F と同じ正直な形）。

  選択公理不使用（新規 Classical.choice なし；継承分の propext/Quot.sound のみ）。
  sorry 皆無・禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/
  positivity/conv/nth_rewrite/field_simp）不使用。許可タクティク（cases/obtain/
  induction/rw/show/refine/exact/apply/intro/generalize/funext/omega）のみ使用。
  共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
  一般名は `tovb` 接頭辞で衝突回避。
-/
import IUT.ThetaOrbitProductBridge
import IUT.ThetaPilotOrbitBridge

namespace IUT

/-! ## M413F-1: M408F の具体指数蓄積は M319F の体積核 sumSq に一致 -/

/-- **定理 (M413F-1: 具体指数蓄積 = 体積核)** — M408F の具体指数蓄積
    `topbConcreteExpSumNat (l+1)`（M403F/M398F の Laurent 環側単一ラベル
    実指数 `(thLtorExp (j:Int)).toNat` の j=0,…,l にわたる実際の和）は、
    M319F の実テータパイロット体積の閉形式係数 `sumSq l` に一致する
    （M408F `topb_orbit_sum`: `topbConcreteExpSumNat (l+1) = ssq l` と
    M378F `tpb_ssq_eq_sumSq`: `ssq l = sumSq l` の推移律）。E 側の
    「具体的に蓄積された」指数が、D 側の体積核とちょうど同じ自然数で
    あることの本物の同定。 -/
theorem tovb_concrete_exp_eq_sumSq (l : Nat) :
    topbConcreteExpSumNat (l + 1) = sumSq l :=
  (topb_orbit_sum l).trans (tpb_ssq_eq_sumSq l)

/-! ## M413F-2: 本丸——実テータパイロット体積を具体指数蓄積の log-volume として書く -/

/-- **定理 (M413F-2: 本丸——実体積 = 具体指数蓄積による log-volume)** —
    実テータパイロット総体積 `thPilotTotalVol logq v l`（M319F、D 側の本物の
    実 Arakelov 局所次数）は、M408F の具体指数蓄積 `topbConcreteExpSumNat (l+1)`
    （E 側、単一ラベルの Laurent 環側実指数の実際の和）による局所 log-volume
    `logVolLocal logq v (topbConcreteExpSumNat (l+1))` に realEq で一致する。
    M413F-1 の橋（`sumSq l = topbConcreteExpSumNat (l+1)`）で M319F
    `thPilot_total_closed` の核を書き換えるだけで閉じる——軌道積側の
    「蓄積された」指数 Σj² がそのままテータパイロット実体積の核であることの
    本物の同定。E（M408F の具体指数蓄積）と D（M319F の実体積）がこの一点で
    出会う、本モジュールの中核の橋。 -/
theorem tovb_orbit_volume (logq : Nat → RReal) (v : Nat) (l : Nat) :
    realEq (thPilotTotalVol logq v l)
      (logVolLocal logq v ((topbConcreteExpSumNat (l + 1) : Nat) : Int)) := by
  rw [tovb_concrete_exp_eq_sumSq l]
  exact thPilot_total_closed logq v l

/-! ## M413F-3: E 側——円分影積も同じ具体指数蓄積で読める（M408F 再輸出） -/

/-- **定理 (M413F-3: 円分影の有限積は具体指数蓄積の冪、M408F 再輸出)** —
    円分影の有限積 `topCycProd M (l+1)`（M373F の実オブジェクト、μ_l の元）は、
    M408F `topb_cyc_prod_concrete_exp` により、具体指数蓄積
    `topbConcreteExpSumNat (l+1)` を指数とする単一の円分影に一致する。
    capstone データで、E 側の体積（M413F-2）と E 側の円分影積の双方が
    同じ具体指数蓄積を核として共有することを束ねるために用いる。 -/
theorem tovb_orbit_cyc_via_concrete (M : CycMuGroup) (l : Nat) :
    topCycProd M (l + 1) = M.μ.pow M.ζ (topbConcreteExpSumNat (l + 1)) :=
  topb_cyc_prod_concrete_exp M (l + 1)

/-! ## M413F-4: capstone——具体指数蓄積・実体積・円分影積を一つの witness に束ねる -/

/-- **M413F-4a: 軌道体積橋データ** — 与えられた円分影群 M・実重み logq・素点 v・
    ラベル数 l に対し、(i) M408F の具体指数蓄積が M319F の体積核 sumSq に一致
    すること、(ii) 実テータパイロット総体積がその具体指数蓄積による log-volume
    に一致すること、(iii) 円分影の有限積が同じ具体指数蓄積を指数とする冪に
    一致すること、を一括で束ねる。E 側（M408F の具体指数蓄積・円分影積）と
    D 側（M319F の実 Arakelov 体積）が同じ具体指数蓄積で出会うことの witness。 -/
structure ThetaOrbitVolumeBridgeData (M : CycMuGroup) (logq : Nat → RReal) (v : Nat)
    (l : Nat) where
  /-- 具体指数蓄積 = 体積核（Nat の等式）。 -/
  concrete_core_eq : topbConcreteExpSumNat (l + 1) = sumSq l
  /-- 実テータパイロット体積 = 具体指数蓄積による局所 log-volume。 -/
  volume_eq : realEq (thPilotTotalVol logq v l)
    (logVolLocal logq v ((topbConcreteExpSumNat (l + 1) : Nat) : Int))
  /-- 円分影の有限積 = 具体指数蓄積を指数とする ζ の冪。 -/
  cyc_eq : topCycProd M (l + 1) = M.μ.pow M.ζ (topbConcreteExpSumNat (l + 1))

/-- **M413F-4b: witness 本体** — 各フィールドを M413F-1〜3 の主定理で埋める。 -/
def thetaOrbitVolumeBridgeData (M : CycMuGroup) (logq : Nat → RReal) (v : Nat) (l : Nat) :
    ThetaOrbitVolumeBridgeData M logq v l where
  concrete_core_eq := tovb_concrete_exp_eq_sumSq l
  volume_eq := tovb_orbit_volume logq v l
  cyc_eq := tovb_orbit_cyc_via_concrete M l

/-- **定理 (M413F-4c: capstone——軌道体積橋データの存在)** — 任意の円分影群 M・
    実重み logq・素点 v・ラベル数 l に対し、M408F の具体指数蓄積・M319F の
    実テータパイロット体積・M373F の円分影積が同じ Σj² 核で本物に出会う
    橋データが組み上がる。E 側の蓄積された軌道指数と D 側の実体積を、
    M408F の実オブジェクトを経由して直接同定するという本モジュールの
    主張が閉じる。 -/
theorem tovb_exists (M : CycMuGroup) (logq : Nat → RReal) (v : Nat) (l : Nat) :
    Nonempty (ThetaOrbitVolumeBridgeData M logq v l) :=
  ⟨thetaOrbitVolumeBridgeData M logq v l⟩

/-! ## M413F-5: 実例（l=4: 具体指数蓄積 topbConcreteExpSumNat 5 と体積核 sumSq 4 は
    ともに Σj²=30） -/

/-- 実例: l=4 で M408F の具体指数蓄積 `topbConcreteExpSumNat 5`
    （ラベル 0,…,4 の単一ラベル実指数の和）は M319F の体積核 `sumSq 4` に一致する
    （`tovb_concrete_exp_eq_sumSq`）。 -/
example : topbConcreteExpSumNat 5 = sumSq 4 := tovb_concrete_exp_eq_sumSq 4

example : topbConcreteExpSumNat 5 = 30 := tovb_concrete_exp_eq_sumSq 4

/-- 実例: l=4 で実テータパイロット総体積は、M408F の具体指数蓄積
    `topbConcreteExpSumNat 5 = 30` による局所 log-volume に一致する
    （`tovb_orbit_volume`）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thPilotTotalVol logq v 4)
      (logVolLocal logq v ((topbConcreteExpSumNat 5 : Nat) : Int)) :=
  tovb_orbit_volume logq v 4

/-- 実例: 本物の μ_5 上で、l=4 の円分影の有限積は具体指数蓄積
    `topbConcreteExpSumNat 5 = 30` を指数とする ζ の冪に一致する
    （`tovb_orbit_cyc_via_concrete`）。 -/
example :
    topCycProd (cycMuStd 5 (by omega)) 5
      = (cycMuStd 5 (by omega)).μ.pow (cycMuStd 5 (by omega)).ζ (topbConcreteExpSumNat 5) :=
  tovb_orbit_cyc_via_concrete (cycMuStd 5 (by omega)) 4

/-- 実例: l=4 の軌道体積橋データが本物で存在する（`tovb_exists`、本物の G_ℚ 上の
    μ_5 と任意の実重み・素点で）。 -/
example (logq : Nat → RReal) (v : Nat) :
    Nonempty (ThetaOrbitVolumeBridgeData (cycMuStd 5 (by omega)) logq v 4) :=
  tovb_exists (cycMuStd 5 (by omega)) logq v 4

end IUT
