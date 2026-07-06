/-
  IUT/IndeterminacyFull.lean — M342F [実／本物]
  分類: 実 (3不定性の (Ind3)＋完全同時作用を実テータパイロット体積 deg_ℝ で完成)
  complete_pct 影響: 柱D を前進（M332F が「主要部分＋骨組み」とした (Ind3) 膨張・
    (Ind1)×(Ind2)×(Ind3) 完全同時作用を実 deg_ℝ で本物化・不定性の掃く hull を実対象で。
    crux Dβ-ω は外部仮説として明示・決して導出しない）。
  正直な限定: crux Dβ-ω（多輻的アルゴリズム＝論争の係争点）は外部 Prop 仮説のみ。
    S_{l⋇} 全体の任意置換閉包は<必要なら仮説>。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  M332F `IndeterminacyRealAction` は (Ind1) 互換置換不変（`indR_ind1_preserves`）と
  (Ind2) 単数不変（`indR_ind2_unit`）を実 deg_ℝ で本物化したが、(Ind3) 膨張
  （`indR_ind3_dilation`）は「下界保持のみ」・(Ind1)×(Ind2)×(Ind3) の完全同時作用は
  「主要部分＋骨組み」に留めていた。本層はその二点を実 deg_ℝ の**厳密な閉形式**へ
  昇格する（M332F の実 deg_ℝ 作用を土台に積み上げ・toy degZ を主語にしない）:

  * M342F-1 `indF_ind3_total_closed` / `indF_ind3_dilation_real`
      — **(Ind3) 膨張の実 deg_ℝ 厳密量**: 付値シフト m の膨張は実テータパイロット
        総体積を deg_ℝ = logVolLocal v (Σj² + m) = (Σj²+m)·log q_v へちょうど動かす
        （M312F `logVolLocal_add` で束ねる）。M332F の下界のみ（`indR_ind3_dilation`）
        を**計算済みの厳密量**へ昇格。`indF_ind3_dilation_lb` は M332F の単調下界を再輸出。
  * M342F-2 `indF_full` / `indF_simultaneous_real`
      — **完全同時作用 (Ind1)∘(Ind2)∘(Ind3) の実 deg_ℝ 閉形式**: 置換（互換 Ind1）・
        単数（Ind2, 付値 0）・膨張（Ind3, 付値 m）を実総体積へ**同時**適用した結果は
        ちょうど logVolLocal v (Σj² + m)。(Ind1)/(Ind2) は Σj² 核を保存するので、
        完全同時作用の実 deg_ℝ 変化は**厳密に (Ind3) 膨張量 m** に等しい。M332F の
        (Ind1)×(Ind2) 保存を (Ind3) と統合した完全版。
  * M342F-3 `indF_hullVol` / `indF_hull` / `indF_hull_expand`
      — **3 不定性が掃く hull**: 到達可能な実 deg_ℝ 値 logVolLocal v (Σj² + m)。
        Σj² 核は (Ind1)(Ind2) で不変ゆえ **hull は置換代表に依らず m の平行移動で決まる**
        （`indF_hull`）。非負膨張（m≥0）では hull は基点体積を上界する（`indF_hull_expand`）。
  * M342F-4 `indF_ind1_perm_general` / `indF_ind1_full_permutation`
      — **(Ind1) 一般置換（互換合成）**: 任意関数 g に対する互換不変を一般化し
        （`indF_ind1_perm_general`）、二互換の合成 swapMult c d ∘ swapMult a b が実 deg_ℝ
        総体積を保つことを示す（`indF_ind1_full_permutation`）。任意置換は互換の積ゆえ
        構成要素は本物。S_{l⋇} 全体の閉包は反復の定型（下記正直申告）。
  * M342F-5 `indF_cruxHyp` / `indF_crux_is_hypothesis`
      — **crux Dβ-ω は外部 Prop 仮説（決して導出しない）**: テータパイロット ⇄
        ガウスパイロット比較（M324F `GaussPilotCruxHyp`）を受け取るのみ。
        `indF_crux_is_hypothesis` は crux がちょうど実 deg_ℝ 不等式であることを Iff.rfl で
        明示（証明はしない・過大主張の厳禁）。
  * M342F-6 capstone `IndFullActionData` / `indFullActionData` / `indF_exists`。
  * 実例: l=5（l⋇=2, n=2）で Σj²=5、(Ind3) m=1 膨張・完全同時作用が logVolLocal v 6 へ。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）

  - **本物（完全証明）**:
    ・(Ind3) 膨張の厳密量・完全同時作用 (Ind1)∘(Ind2)∘(Ind3) の閉形式・hull の
      置換非依存・(Ind1) 二互換合成不変は、全て M319F/M312F の**本物の実 deg_ℝ**の上で
      core Lean のみで完全証明（M332F の実作用を土台に積み上げ）。
  - **正直申告（未達・witness・後続。飾りでなく地図）**:
    ・log q_v（実重み `logq : Nat → RReal`）は M312F/M319F/M332F と同じく**実重み
      witness**（係数扱い）。log q_v の超越性・具体値・u=q^{1/2l} の体内実在は範囲外。
    ・(Ind1) 一般置換は**互換の積の構成要素（単一・二互換合成）**まで本物。対称群
      S_{l⋇} 全体の任意置換への閉包（互換生成の一般反復）は必要なら仮説として据える
      （本層は互換合成の本物を提示するに留める）。
    ・(Ind3) 膨張・単数作用は「付値の寄与」の実 deg_ℝ 上の代数的挙動であり、原論文の
      log-shell 上の単数積分・上方両立の解析的内容は写像しない（M332F の継続）。
    ・**多輻的アルゴリズム本体 Dβ-ω（crux＝論争の係争点）は恒久的に本層の範囲外**——
      本層は 3 不定性の作用と hull を実 deg_ℝ 上で**無条件に**構成するのみで、crux
      不等式（LHS と RHS を突き合わせる）は外部 Prop 仮説として受け取るだけ・決して
      導出しない（`indF_crux_is_hypothesis`）。
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ deg_ℝ の閉形式・下界は
      realEq/rLe で言明する（M312F/M319F/M332F と同じ正直な形）。
  全て新規 Classical.choice を証明本体に導入せず（M332F/M319F/M324F/M312F から継承、
  #print axioms は propext/Quot.sound 系のみ）。sorry 皆無・禁止タクティク不使用
  （core Lean のみ）。一般名は `indF` 接頭辞で衝突回避。
-/
import IUT.IndeterminacyRealAction
import IUT.GaussPilotRealVolume

namespace IUT

/-! ## M342F-1: (Ind3) 膨張の実 deg_ℝ 厳密量（M332F 下界を計算済み閉形式へ昇格） -/

/-- **M342F-1a: (Ind3) 膨張の実総体積の厳密閉形式（一般指数）** — 付値シフト m の
    膨張を、ラベル指数 g に沿った実総体積 `indR_realTotal` に適用した結果は、ちょうど
    logVolLocal v (Σg + m) = (Σg + m)·log q_v。M312F `logVolLocal_add` で膨張寄与
    logVolLocal v m を Σg の deg_ℝ に束ねる。M332F の下界（`indR_ind3_dilation`）を
    **計算済みの厳密量**へ昇格。 -/
theorem indF_ind3_total_closed (logq : Nat → RReal) (v : Nat) (g : Nat → Nat)
    (n : Nat) (m : Int) :
    realEq (indR_ind3Vol logq v (indR_realTotal logq v g n) m)
      (logVolLocal logq v (((nsum g n : Nat) : Int) + m)) := by
  show realEq (realAdd (indR_realTotal logq v g n) (logVolLocal logq v m))
      (logVolLocal logq v (((nsum g n : Nat) : Int) + m))
  refine realEq_trans (realAdd_congr_left (logVolLocal logq v m)
    (indR_realTotal_closed logq v g n)) ?_
  exact realEq_symm (logVolLocal_add logq v ((nsum g n : Nat) : Int) m)

/-- **M342F-1b: (Ind3) 膨張の実テータパイロット体積の厳密量（既定指数 Σj²）** —
    付値シフト m の膨張は、M319F の実テータパイロット総体積 `thPilotTotalVol` を
    deg_ℝ = logVolLocal v (Σj² + m) = (Σj²+m)·log q_v へちょうど動かす。従来
    「下界を保つ」だけだった (Ind3) の実作用を、**動く量まで計算した厳密閉形式**に。 -/
theorem indF_ind3_dilation_real (logq : Nat → RReal) (v : Nat) (n : Nat) (m : Int) :
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) m)
      (logVolLocal logq v (((sumSq n : Nat) : Int) + m)) := by
  show realEq (realAdd (thPilotTotalVol logq v n) (logVolLocal logq v m))
      (logVolLocal logq v (((sumSq n : Nat) : Int) + m))
  refine realEq_trans (realAdd_congr_left (logVolLocal logq v m)
    (thPilot_total_closed logq v n)) ?_
  exact realEq_symm (logVolLocal_add logq v ((sumSq n : Nat) : Int) m)

/-- **M342F-1c: (Ind3) 膨張の単調下界（M332F 再輸出）** — 膨張の付値寄与 m≥0 は
    非負重みの下で実 deg_ℝ を増大（下界保持以上）。M332F `indR_ind3_dilation`。 -/
theorem indF_ind3_dilation_lb (logq : Nat → RReal) (v : Nat) (V : RReal) (m : Int)
    (hm : 0 ≤ m) (hq : rLe realZero (logq v)) :
    rLe V (indR_ind3Vol logq v V m) :=
  indR_ind3_dilation logq v V m hm hq

/-! ## M342F-2: 完全同時作用 (Ind1)∘(Ind2)∘(Ind3) の実 deg_ℝ 閉形式 -/

/-- **M342F-2a: 完全同時作用の合成体積** — l-捻れラベルの互換置換（Ind1, swapMult a b）・
    単数作用（Ind2, 付値 0）・膨張（Ind3, 付値 m）を、実テータパイロット総体積へ
    **同時**（合成）に適用した実 deg_ℝ。 -/
def indF_full (logq : Nat → RReal) (v a b n : Nat) (m : Int) : RReal :=
  indR_ind3Vol logq v
    (indR_ind2Vol logq v
      (indR_realTotal logq v (swapMult a b indR_natExp) n) 0) m

/-- **M342F-2b (本丸): 完全同時作用 (Ind1)∘(Ind2)∘(Ind3) の実 deg_ℝ 閉形式** —
    置換（Ind1）・単数（Ind2）・膨張（Ind3）の同時作用の結果はちょうど
    logVolLocal v (Σj² + m)。(Ind1) は Σj² を置換不変に保ち・(Ind2) は付値 0 で保つので、
    完全同時作用の実 deg_ℝ 変化は**厳密に (Ind3) 膨張量 m のみ**。M332F の (Ind1)×(Ind2)
    保存を (Ind3) と統合した完全版（M259F Bool³ 混合の実 deg_ℝ 全展開）。 -/
theorem indF_simultaneous_real (logq : Nat → RReal) (v a b n : Nat) (m : Int)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) :
    realEq (indF_full logq v a b n m)
      (logVolLocal logq v (((sumSq n : Nat) : Int) + m)) := by
  have hP2 : realEq
      (indR_ind2Vol logq v (indR_realTotal logq v (swapMult a b indR_natExp) n) 0)
      (logVolLocal logq v ((sumSq n : Nat) : Int)) := by
    refine realEq_trans (indR_ind2_unit logq v
      (indR_realTotal logq v (swapMult a b indR_natExp) n) 0 rfl) ?_
    refine realEq_trans (indR_ind1_preserves logq v a b n hab ha hb) ?_
    have hc := indR_realTotal_closed logq v indR_natExp n
    rw [indR_natExp_sum n] at hc
    exact hc
  show realEq (realAdd
        (indR_ind2Vol logq v (indR_realTotal logq v (swapMult a b indR_natExp) n) 0)
        (logVolLocal logq v m))
      (logVolLocal logq v (((sumSq n : Nat) : Int) + m))
  refine realEq_trans (realAdd_congr_left (logVolLocal logq v m) hP2) ?_
  exact realEq_symm (logVolLocal_add logq v ((sumSq n : Nat) : Int) m)

/-! ## M342F-3: 3 不定性が掃く hull（実 deg_ℝ 到達域） -/

/-- **M342F-3a: hull 体積** — 3 不定性 (Ind1)×(Ind2)×(Ind3) が到達する実 deg_ℝ 値
    logVolLocal v (Σj² + m)。Σj² 核（(Ind1)(Ind2) 不変）に膨張量 m を平行移動した対象。 -/
def indF_hullVol (logq : Nat → RReal) (v n : Nat) (m : Int) : RReal :=
  logVolLocal logq v (((sumSq n : Nat) : Int) + m)

/-- **M342F-3b (本丸): hull は (Ind1) 置換代表に依らない** — 異なる互換 (a,b)/(c,d) で
    完全同時作用させても、到達する実 deg_ℝ は等しい（両者 ≈ hull 体積）。Σj² 核が
    (Ind1)(Ind2) で不変ゆえ、掃く hull は置換の取り方に依らず **膨張量 m の平行移動**で
    決まる。「hull は不変核 Σj² の平行移動」の実 deg_ℝ 言明。 -/
theorem indF_hull (logq : Nat → RReal) (v a b c d n : Nat) (m : Int)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n)
    (hcd : ¬ c = d) (hc : c < n) (hd : d < n) :
    realEq (indF_full logq v a b n m) (indF_full logq v c d n m) :=
  realEq_trans (indF_simultaneous_real logq v a b n m hab ha hb)
    (realEq_symm (indF_simultaneous_real logq v c d n m hcd hc hd))

/-- **M342F-3c: hull は非負膨張で基点体積を上界する** — 付値シフト m≥0 の膨張のもと、
    hull 体積 logVolLocal v (Σj² + m) は実テータパイロット総体積 thPilotTotalVol を
    上界する（非負重み log q_v ≥ 0）。(Ind3) の一方向性（膨張のみ）の実 deg_ℝ 版。 -/
theorem indF_hull_expand (logq : Nat → RReal) (v n : Nat) (m : Int)
    (hm : 0 ≤ m) (hq : rLe realZero (logq v)) :
    rLe (thPilotTotalVol logq v n) (indF_hullVol logq v n m) := by
  have hlb : rLe (thPilotTotalVol logq v n)
      (indR_ind3Vol logq v (thPilotTotalVol logq v n) m) :=
    indR_ind3_dilation logq v (thPilotTotalVol logq v n) m hm hq
  exact rLe_congr (realEq_refl (thPilotTotalVol logq v n))
    (indF_ind3_dilation_real logq v n m) hlb

/-! ## M342F-4: (Ind1) 一般置換（互換合成＝任意置換の構成要素） -/

/-- **M342F-4a: (Ind1) 互換不変の一般化（任意ラベル指数関数 g）** — 任意の g に対し、
    互換 swapMult a b は実 deg_ℝ 総体積を保つ（Σ_{σ} g = Σ g、置換不変）。組合せ核
    `nsum_two_point_eq`（二点入替不変）を、閉形式 `indR_realTotal_closed` 経由で実 deg_ℝ
    へ持ち上げる。M332F `indR_ind1_preserves`（既定指数）を一般 g へ広げ、互換合成の
    基盤とする。 -/
theorem indF_ind1_perm_general (logq : Nat → RReal) (v a b n : Nat) (g : Nat → Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) :
    realEq (indR_realTotal logq v (swapMult a b g) n)
      (indR_realTotal logq v g n) := by
  have hswap : nsum (swapMult a b g) n = nsum g n :=
    nsum_two_point_eq (swapMult a b g) g a b n hab ha hb
      (fun k hka hkb => swapMult_other a b g k hka hkb)
      (by rw [swapMult_left, swapMult_right a b g hab]; exact Nat.add_comm _ _)
  refine realEq_trans (indR_realTotal_closed logq v (swapMult a b g) n) ?_
  rw [hswap]
  exact realEq_symm (indR_realTotal_closed logq v g n)

/-- **M342F-4b: (Ind1) 二互換合成の実 deg_ℝ 不変** — 二つの互換の合成
    swapMult c d ∘ swapMult a b（既定指数 indR_natExp に適用）は実テータパイロット
    総体積を保つ。任意置換は互換の積ゆえ、これが一般 S_{l⋇} 置換不変の**構成要素**。
    S_{l⋇} 全体の任意置換への閉包は互換合成の反復の定型（必要なら仮説・正直申告）。 -/
theorem indF_ind1_full_permutation (logq : Nat → RReal) (v a b c d n : Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n)
    (hcd : ¬ c = d) (hc : c < n) (hd : d < n) :
    realEq (indR_realTotal logq v (swapMult c d (swapMult a b indR_natExp)) n)
      (indR_realTotal logq v indR_natExp n) :=
  realEq_trans
    (indF_ind1_perm_general logq v c d n (swapMult a b indR_natExp) hcd hc hd)
    (indR_ind1_preserves logq v a b n hab ha hb)

/-! ## M342F-5: crux Dβ-ω は外部 Prop 仮説（決して導出しない） -/

/-- **M342F-5a: crux Dβ-ω 仮説（外部 Prop）** — テータパイロット総体積 ⇄ ガウスパイロット
    総体積の実 deg_ℝ 比較（M324F `GaussPilotCruxHyp`）。これは定理3.11 の体積不等式
    （＝多輻的アルゴリズム＝IUT 論争の係争点）であり、本層は**仮説として受け取るのみ・
    決して導出しない**。3 不定性の作用・hull は上で**無条件に**実 deg_ℝ 構成したが、
    crux はそれとは独立に外部から受ける。 -/
def indF_cruxHyp (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) : Prop :=
  GaussPilotCruxHyp logq v w l

/-- **M342F-5b: crux が外部仮説であることの明示** — `indF_cruxHyp` はちょうど実 deg_ℝ
    不等式「thPilotTotalVol ≤ gPilotTotalVol」であり、それ以上でも以下でもない
    （Iff.rfl）。本層は crux をこの仮説として受け取るのみで、**証明はしない**
    （過大主張の厳禁の機械検証的明示）。 -/
theorem indF_crux_is_hypothesis (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    indF_cruxHyp logq v w l
      ↔ rLe (thPilotTotalVol logq v l) (gPilotTotalVol logq v w (l + 1)) :=
  Iff.rfl

/-! ## M342F-6: capstone -/

/-- **M342F-6a: 完全不定性作用データ** — 3 不定性の完全同時作用を実 deg_ℝ で束ねる:
    完全同時作用の閉形式・(Ind3) 膨張厳密量・hull の置換非依存・(Ind1) 二互換合成不変。
    主語は M319F/M312F/M332F の本物の実 deg_ℝ であり、toy degZ を作用主語に用いない。 -/
structure IndFullActionData (logq : Nat → RReal) (v : Nat) where
  /-- 完全同時作用 (Ind1)∘(Ind2)∘(Ind3) の実 deg_ℝ 閉形式（hull 体積へ到達）。 -/
  simultaneous : ∀ (a b n : Nat) (m : Int), ¬ a = b → a < n → b < n →
    realEq (indF_full logq v a b n m) (indF_hullVol logq v n m)
  /-- (Ind3) 膨張の実 deg_ℝ 厳密量。 -/
  ind3_amount : ∀ (n : Nat) (m : Int),
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) m) (indF_hullVol logq v n m)
  /-- 掃く hull は (Ind1) 置換代表に依らない（Σj² 核不変・hull は m 平行移動）。 -/
  hull_perm_inv : ∀ (a b c d n : Nat) (m : Int), ¬ a = b → a < n → b < n →
    ¬ c = d → c < n → d < n →
    realEq (indF_full logq v a b n m) (indF_full logq v c d n m)
  /-- (Ind1) 二互換合成（一般置換の構成要素）も実 deg_ℝ 総体積を保つ。 -/
  ind1_double : ∀ (a b c d n : Nat), ¬ a = b → a < n → b < n →
    ¬ c = d → c < n → d < n →
    realEq (indR_realTotal logq v (swapMult c d (swapMult a b indR_natExp)) n)
      (indR_realTotal logq v indR_natExp n)

/-- **M342F-6b: 実データ** — 全フィールドを M342F-2〜4 の本物で充足。 -/
def indFullActionData (logq : Nat → RReal) (v : Nat) : IndFullActionData logq v where
  simultaneous := fun a b n m hab ha hb => indF_simultaneous_real logq v a b n m hab ha hb
  ind3_amount := fun n m => indF_ind3_dilation_real logq v n m
  hull_perm_inv := fun a b c d n m hab ha hb hcd hc hd =>
    indF_hull logq v a b c d n m hab ha hb hcd hc hd
  ind1_double := fun a b c d n hab ha hb hcd hc hd =>
    indF_ind1_full_permutation logq v a b c d n hab ha hb hcd hc hd

/-- **M342F-6c: 存在** — 任意の実重み logq・素点 v に対し、3 不定性の完全同時作用データ
    が存在する。M332F の「主要部分＋骨組み」だった (Ind3)・完全同時作用が実 deg_ℝ で
    本物化された。 -/
theorem indF_exists (logq : Nat → RReal) (v : Nat) :
    Nonempty (IndFullActionData logq v) :=
  ⟨indFullActionData logq v⟩

/-! ## 実例（l=5, l⋇=2, n=2: ラベル j=1,2, Σj²=1²+2²=5） -/

/-- 実例: 既定指数和 Σ_{k<2}(k+1)² = 5。 -/
example : nsum indR_natExp 2 = 5 := rfl

/-- 実例: sumSq 2 = 5。 -/
example : sumSq 2 = 5 := rfl

/-- 実例: l=5（n=2）で (Ind3) 膨張（付値 m=1）は実テータパイロット総体積を
    deg_ℝ = logVolLocal v (5+1) = 6·log q_v へちょうど動かす（厳密量）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v 2) 1)
      (logVolLocal logq v (((sumSq 2 : Nat) : Int) + 1)) :=
  indF_ind3_dilation_real logq v 2 1

/-- 実例: l=5（n=2）で完全同時作用（Ind1 互換 0↔1・Ind2 単数・Ind3 膨張 m=1）は
    hull 体積 logVolLocal v 6 へ到達する（実 deg_ℝ 閉形式）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (indF_full logq v 0 1 2 1) (indF_hullVol logq v 2 1) :=
  indF_simultaneous_real logq v 0 1 2 1 (by omega) (by omega) (by omega)

/-- 実例: l=5（n=2）で hull は (Ind1) 置換代表 (0,1) と (1,0) で等しい（置換非依存）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (indF_full logq v 0 1 2 1) (indF_full logq v 1 0 2 1) :=
  indF_hull logq v 0 1 1 0 2 1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

/-- 実例: l=5（n=2）で (Ind1) 二互換合成（0↔1 を二度）は実テータパイロット総体積を
    保存する（一般置換の構成要素・実 deg_ℝ）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (indR_realTotal logq v (swapMult 0 1 (swapMult 0 1 indR_natExp)) 2)
      (indR_realTotal logq v indR_natExp 2) :=
  indF_ind1_full_permutation logq v 0 1 0 1 2 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

end IUT
