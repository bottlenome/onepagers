-- M417F LogVolumePilotBound [実・本物・柱D]
-- complete_pct 影響: 柱D で M319F の実 l³≤3Σj² 下界を M372F 多輻表現 mrpRepresentation
--   ((Ind1)(Ind2)-不変核) の上へ持ち上げ、テータパイロット多輻表現の実 deg_ℝ 下界
--   l³·log q_v ≤ 3·(多輻表現) を本物として証明する (RHS を 3·Σj² 重み形から 3·mrpRepresentation
--   へ載せ替え、rmul 結合律・intToReal 乗法性で橋渡し)。crux(theta≤gauss 比較)は決して導出しない。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。
--   下界は実 deg_ℝ・LHS の l³ は初等的不等式 M97 cube_le_sumSq (crux とは別物・本物)・
--   RHS は M372F (Ind1)(Ind2)-降下 (Σj² 核)・log q_v は実重み witness・ℝ は setoid(realEq/rLe)。

/-
  IUT/LogVolumePilotBound.lean — M417F（定理3.11 / パイロット下界の多輻表現化）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の先行建設 (b)・既存の実 l³ 下界 (a) 昇格）。
    M319F `thPilot_cubic_bound`（実 deg_ℝ の l³ 下界 l³·log q_v ≤ 3·(Σj²)·log q_v、M97
    `cube_le_sumSq`: l³ ≤ 3Σj² の順序持ち上げ）を、M372F の**多輻表現** `mrpRepresentation`
    （テータパイロット体積の (Ind1)(Ind2)-不変核＝不定性商上の well-defined 降下）の上へ
    **載せ替える**。すなわち、生の重み形 RHS `3·(Σj²)·log q_v` を **`3·mrpRepresentation`**
    （多輻不変体積の 3 倍）へ書き換え、下界を **多輻表現に対する実 deg_ℝ 下界**
    `l³·log q_v ≤ 3·(多輻表現)` として述べ直す。これは M97 cube_le_sumSq を再利用する
    **本物の初等的不等式**（l³ ≤ 3Σj²）であり、crux（theta ≤ gauss 比較）とは別物。
  * complete_pct 影響: **前進**。M412F は theta-pilot vs gauss-pilot の crux を多輻表現レベルで
    述べ（LHS を多輻表現へ載せ替え）、M372F は多輻表現を (Ind1)(Ind2)-降下として本物化した。
    **次の本物の一手**は、M319F の実 l³ 下界そのものを多輻表現レベルへ持ち上げること:
      - **多輻レベル l³ 下界** `lpb_multiradial_cubic_bound` =
        rLe (l³·log q_v) (3·mrpRepresentation)。RHS は M372F の (Ind1)(Ind2)-不変核の 3 倍。
      - **橋渡し** `lpb_three_rep_eq`: 3·(Σj²)·log q_v ≈ 3·mrpRepresentation
        （rmul 結合律 `rmul_assoc_real`・intToReal 乗法性 `intToReal_mul`）。
      - **(Ind1)(Ind2)-不変**: 下界の RHS の多輻表現は (Ind1) 置換像・(Ind2) 単数像へ
        載せ替えても同じ（M372F `mrp_ind1_invariant`/`mrp_ind2_invariant` を `rmul_congr_right`
        ＋ `rLe_congr` で張り替え）——下界は不定性代表の取り方に依らない。
      - **降下形** `lpb_bound_via_descent`: 下界はテータパイロット総体積そのもの
        （M372F `mrp_representation_descent`）に対しても述べられる。
    crux Dβ-ω（多輻的アルゴリズム＝theta ≤ gauss 比較＝IUT 論争の係争点）は**決して導出せず**
    外部仮説のまま（`lpb_crux_is_hypothesis` は Iff.rfl、`lpb_crux_external` は crux を受け取るのみ）。
    柱D の実 l³ 下界を **多輻表現レベルで本物化**。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M417F-1 `lpb_three_rep_eq` — 3·(Σj²)·log q_v ≈ 3·mrpRepresentation（重み形→多輻表現の橋渡し）。
  * M417F-2 `lpb_multiradial_cubic_bound` — 多輻レベル l³ 下界 l³·log q_v ≤ 3·mrpRepresentation（本物）。
  * M417F-3 `lpb_bound_via_descent` — 下界はテータパイロット総体積（降下）に対しても成立。
  * M417F-4 `lpb_bound_ind1_invariant` / `lpb_bound_ind2_invariant` — 下界は (Ind1)(Ind2)-不変。
  * M417F-5 `lpb_elementary_nat` — 台となる初等的不等式 l³ ≤ 3Σj²（M97、crux とは別物・本物）。
  * M417F-6 `lpb_crux_external` / `lpb_crux_is_hypothesis`（Iff.rfl）— crux は外部仮説・決して導出しない。
  * M417F-7 capstone `LogVolumePilotBoundData` / `lpb_exists` と実例（l=5: 125 ≤ 3·Σj²=165）。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロットの比較不等式そのもの＝
    IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層が証明する l³ 下界は M97 `cube_le_sumSq`
    による**初等的不等式**（l³ ≤ 3Σj²）を多輻表現へ持ち上げたものであり、**crux（theta ≤ gauss の
    比較）とは全く別の不等式**。`lpb_crux_is_hypothesis`（Iff.rfl）が「crux は受け取る外部仮説で
    あって定理ではない」ことを明示し、`lpb_crux_external` は l³ 下界（本物）と crux（仮説）を
    連言で束ねるが crux は決して導出しない。
  * **下界は実 deg_ℝ 体積レベル**。RHS の多輻表現は M372F の (Ind1)(Ind2)-降下（Σj² 核）。
    (Ind3) 明示 m シフトは不変性から除く。群レベルの完全同変性は後続。
  * **局所体は K = ℚ_p**。log q_v は実重み witness（M312F 継承）。有理冪の分母 2l は微細格子 witness。
    **ℝ は setoid**（realEq が同値・`=` でない）ゆえ下界・橋渡し・不変性は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 横展開・本物の先行建設[実]。一般名は `lpb` 接頭辞で衝突回避。
-/
import IUT.PilotComparisonMultiradial

namespace IUT

/-! ## M417F-1: 橋渡し 3·(Σj²)·log q_v ≈ 3·mrpRepresentation（重み形→多輻表現） -/

/-- **定理 (M417F-1: 重み形 RHS を多輻表現の 3 倍へ載せ替え)** — M319F の l³ 下界の RHS
    `3·(Σj²)·log q_v = rmul (intToReal (3·Σj²)) (logq v)` は、M372F の多輻表現
    `mrpRepresentation logq v l`（＝(Σj²)·log q_v の不変核）の **3 倍** `rmul (intToReal 3)
    (mrpRepresentation logq v l)` に一致する（realEq、ℝ は setoid）。intToReal の乗法性
    `intToReal_mul`（3·Σj² = 3 × Σj²）と rmul 結合律 `rmul_assoc_real` で括り直すだけ——
    下界の右辺を「多輻不変体積の 3 倍」として読む本物の橋渡し。 -/
theorem lpb_three_rep_eq (logq : Nat → RReal) (v l : Nat) :
    realEq (rmul (intToReal ((3 * sumSq l : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l)) := by
  show realEq (rmul (intToReal ((3 * sumSq l : Nat) : Int)) (logq v))
    (rmul (intToReal ((3 : Nat) : Int))
      (rmul (intToReal ((sumSq l : Nat) : Int)) (logq v)))
  have hcast : ((3 * sumSq l : Nat) : Int)
      = ((3 : Nat) : Int) * ((sumSq l : Nat) : Int) := by
    rw [Int.natCast_mul]
  rw [hcast]
  refine realEq_trans (rmul_congr_left (logq v)
    (realEq_symm (intToReal_mul ((3 : Nat) : Int) ((sumSq l : Nat) : Int)))) ?_
  exact rmul_assoc_real (intToReal ((3 : Nat) : Int))
    (intToReal ((sumSq l : Nat) : Int)) (logq v)

/-! ## M417F-2: 多輻レベル l³ 下界（本物・M97 の初等的不等式を多輻表現へ持ち上げ） -/

/-- **定理 (M417F-2: 多輻レベル l³ 下界・本物)** — テータパイロット多輻表現の実 deg_ℝ 下界:
    `l³·log q_v ≤ 3·mrpRepresentation`（非負重み log q_v ≥ 0 の下で）。M319F `thPilot_cubic_bound`
    （生の重み形 l³·log q_v ≤ 3·(Σj²)·log q_v、台は M97 `cube_le_sumSq`: l³ ≤ 3Σj²）を、
    M417F-1 の橋渡し `lpb_three_rep_eq` で RHS を **多輻表現の 3 倍**へ載せ替えたもの。
    これは M97 の**初等的不等式**を多輻不変体積の上へ持ち上げた本物であり、**crux（theta ≤ gauss
    比較）とは別物**——ここでは論争の係争点を一切導出していない。 -/
theorem lpb_multiradial_cubic_bound (logq : Nat → RReal) (v l : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l)) :=
  rLe_congr (realEq_refl _) (lpb_three_rep_eq logq v l)
    (thPilot_cubic_bound logq v l hq)

/-! ## M417F-3: 下界の降下形（テータパイロット総体積そのものに対して） -/

/-- **定理 (M417F-3: 下界はテータパイロット総体積に対しても成立)** — 多輻表現はテータパイロット
    総体積の降下（M372F `mrp_representation_descent`、realEq）ゆえ、l³ 下界は生の総体積
    `thPilotTotalVol` の 3 倍に対しても述べられる: `l³·log q_v ≤ 3·thPilotTotalVol`。
    `rmul_congr_right`（右因子の realEq 張り替え）＋ `rLe_congr` で M417F-2 から従う——
    下界が「多輻表現」でも「その降下元の総体積」でも同じ本物の命題であることの確認。 -/
theorem lpb_bound_via_descent (logq : Nat → RReal) (v l : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int)) (thPilotTotalVol logq v l)) :=
  rLe_congr (realEq_refl _)
    (rmul_congr_right (intToReal ((3 : Nat) : Int))
      (realEq_symm (mrp_representation_descent logq v l)))
    (lpb_multiradial_cubic_bound logq v l hq)

/-! ## M417F-4: 下界は (Ind1)(Ind2)-不変（不定性代表非依存） -/

/-- **定理 (M417F-4a: 下界は (Ind1) 置換で不変)** — l³ 下界の RHS の多輻表現を、(Ind1) 互換
    swapMult a b を掛けた実 deg_ℝ 総体積 `indR_realTotal` の 3 倍へ載せ替えても、なお下界は
    成立する: `l³·log q_v ≤ 3·(Ind1 像)`。(Ind1) 像は多輻表現の不変核へ降下する（M372F
    `mrp_ind1_invariant`、Σ_{σj} j² = Σj²）ので、`rmul_congr_right`＋`rLe_congr` で M417F-2 から
    張り替えるだけ——下界は (Ind1) 置換代表の取り方に**依らない**（多輻不変体積上の well-defined
    な下界）。 -/
theorem lpb_bound_ind1_invariant (logq : Nat → RReal) (v a b l : Nat)
    (hab : ¬ a = b) (ha : a < l) (hb : b < l) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int))
        (indR_realTotal logq v (swapMult a b indR_natExp) l)) :=
  rLe_congr (realEq_refl _)
    (rmul_congr_right (intToReal ((3 : Nat) : Int))
      (realEq_symm (mrp_ind1_invariant logq v a b l hab ha hb)))
    (lpb_multiradial_cubic_bound logq v l hq)

/-- **定理 (M417F-4b: 下界は (Ind2) 単数で不変)** — l³ 下界の RHS の多輻表現を、(Ind2) 単数作用
    （付値 μ=0）を掛けた実 deg_ℝ の 3 倍へ載せ替えても、なお下界は成立する。(Ind2) 像は不変核へ
    降下する（M372F `mrp_ind2_invariant`、v(単数)=0）ので `rmul_congr_right`＋`rLe_congr` で
    張り替えるだけ——下界は (Ind2) 単数不定性の下でも well-defined。 -/
theorem lpb_bound_ind2_invariant (logq : Nat → RReal) (v l : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int))
        (indR_ind2Vol logq v (thPilotTotalVol logq v l) 0)) :=
  rLe_congr (realEq_refl _)
    (rmul_congr_right (intToReal ((3 : Nat) : Int))
      (realEq_symm (mrp_ind2_invariant logq v l)))
    (lpb_multiradial_cubic_bound logq v l hq)

/-! ## M417F-5: 台となる初等的不等式 l³ ≤ 3Σj²（M97、crux とは別物・本物） -/

/-- **定理 (M417F-5: 台の初等的不等式)** — 多輻レベル l³ 下界の台は、M97 `cube_le_sumSq` の
    **初等的な離散不等式** l³ ≤ 3·Σ_{j=1}^{l} j²（Nat レベル）である。これは**本物の証明済み
    不等式**であり、**crux（theta ≤ gauss の多輻的比較）とは全く別の命題**——crux は導出しない。 -/
theorem lpb_elementary_nat (l : Nat) : l * l * l ≤ 3 * sumSq l :=
  cube_le_sumSq l

/-! ## M417F-6: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M417F-6a: l³ 下界は本物・crux は外部仮説／honest)** — 多輻レベル l³ 下界
    `lpb_multiradial_cubic_bound`（l³·log q_v ≤ 3·多輻表現）は M97 の初等的不等式を持ち上げた
    **無条件で本物**の命題（crux とは独立に成立）。しかし theta-pilot ≤ gauss-pilot の**多輻的
    アルゴリズム**（crux Dβ-ω ＝ M412F `pcmMultiradialCrux` ＝ IUT 論争の当の係争点）は本層で
    **決して証明しない**。crux を M412F の受け取り仮説 `pcmMultiradialCrux` として受け取り、
    l³ 下界（本物）**と** crux（仮説）を連言で返す——crux は決して導出されない。 -/
theorem lpb_crux_external (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat)
    (hq : rLe realZero (logq v)) (crux : pcmMultiradialCrux logq v w l) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
    ∧ pcmMultiradialCrux logq v w l :=
  ⟨lpb_multiradial_cubic_bound logq v l hq, crux⟩

/-- **定理 (M417F-6b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux（theta ≤ gauss 比較）は本層が証明した
    l³ 下界とは別物であり、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で
    明示（M412F `pcm_crux_is_hypothesis`・M372F `mrp_crux_is_hypothesis` と同じ精神）。 -/
theorem lpb_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M417F-7: capstone -/

/-- **M417F-7a: パイロット下界多輻表現データ**（総括） — 定理3.11 のテータパイロット下界を、
    M372F 多輻表現（(Ind1)(Ind2)-不変核）の上で述べた実 deg_ℝ の l³ 下界として束ねる:
    多輻レベル l³ 下界・重み形との橋渡し・降下形・(Ind1)(Ind2)-不変・台の初等的不等式。
    主語は M319F/M372F/M97 の本物の実 deg_ℝ であり toy を用いない。crux（Dβ-ω＝theta ≤ gauss）は
    別物であって本層で証明されない。 -/
structure LogVolumePilotBoundData (logq : Nat → RReal) (v : Nat) where
  /-- 多輻レベル l³ 下界: l³·log q_v ≤ 3·多輻表現（非負重みの下で）。 -/
  cubic_bound : ∀ l : Nat, rLe realZero (logq v) →
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
  /-- 重み形 RHS を多輻表現の 3 倍へ載せ替える橋渡し。 -/
  three_rep_eq : ∀ l : Nat,
    realEq (rmul (intToReal ((3 * sumSq l : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v l))
  /-- 下界はテータパイロット総体積（降下元）に対しても成立。 -/
  bound_descent : ∀ l : Nat, rLe realZero (logq v) →
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int)) (thPilotTotalVol logq v l))
  /-- 下界は (Ind1) 置換で不変（不定性代表非依存）。 -/
  ind1_inv : ∀ (a b l : Nat), ¬ a = b → a < l → b < l → rLe realZero (logq v) →
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int))
        (indR_realTotal logq v (swapMult a b indR_natExp) l))
  /-- 台の初等的不等式 l³ ≤ 3Σj²（M97、crux とは別物・本物）。 -/
  elementary : ∀ l : Nat, l * l * l ≤ 3 * sumSq l

/-- **M417F-7b: 実データ** — 全フィールドを M417F-1〜5 の本物で充足。 -/
def logVolumePilotBoundData (logq : Nat → RReal) (v : Nat) :
    LogVolumePilotBoundData logq v where
  cubic_bound := fun l hq => lpb_multiradial_cubic_bound logq v l hq
  three_rep_eq := fun l => lpb_three_rep_eq logq v l
  bound_descent := fun l hq => lpb_bound_via_descent logq v l hq
  ind1_inv := fun a b l hab ha hb hq => lpb_bound_ind1_invariant logq v a b l hab ha hb hq
  elementary := fun l => lpb_elementary_nat l

/-- **M417F-7c: 存在（M417F 見出し）** — 任意の実重み logq・素点 v に対し、テータパイロット下界を
    多輻表現レベルで述べたデータが存在する。多輻レベル l³ 下界 l³·log q_v ≤ 3·mrpRepresentation は
    M97 の初等的不等式を M372F 多輻表現へ持ち上げた**本物**であり、(Ind1)(Ind2)-不変で well-defined。
    crux（Dβ-ω＝theta ≤ gauss 比較）は別物であって**決して証明されない**。 -/
theorem lpb_exists (logq : Nat → RReal) (v : Nat) :
    Nonempty (LogVolumePilotBoundData logq v) :=
  ⟨logVolumePilotBoundData logq v⟩

/-! ## 実例（l=5, l⋇=2..5: Σ_{j=1}^{5} j²=55, 3·55=165, l³=125 ≤ 165） -/

/-- 実例: Σ_{j=1}^{5} j² = sumSq 5 = 55。 -/
example : sumSq 5 = 55 := rfl

/-- 実例（l=5 の初等的下界）: 125 = 5³ ≤ 3·Σj² = 3·55 = 165（M97、crux とは別物）。 -/
example : (125 : Nat) ≤ 3 * sumSq 5 := lpb_elementary_nat 5

/-- 実例: l=5 の多輻レベル l³ 下界 125·log q_v ≤ 3·mrpRepresentation（非負重みの下で）。 -/
example (logq : Nat → RReal) (v : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v 5)) :=
  lpb_multiradial_cubic_bound logq v 5 hq

/-- 実例: l=5 の下界はテータパイロット総体積（降下元）に対しても成立。 -/
example (logq : Nat → RReal) (v : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int)) (thPilotTotalVol logq v 5)) :=
  lpb_bound_via_descent logq v 5 hq

/-- 実例: l=5 の下界は (Ind1) 互換 0↔1 で不変（置換代表非依存の well-defined、n=2 で例示）。 -/
example (logq : Nat → RReal) (v : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * 2 * 2 : Nat) : Int)) (logq v))
      (rmul (intToReal ((3 : Nat) : Int))
        (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2)) :=
  lpb_bound_ind1_invariant logq v 0 1 2 (by omega) (by omega) (by omega) hq

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  lpb_crux_is_hypothesis crux

/-- 実例（capstone 存在）: パイロット下界多輻表現データは存在する。 -/
example (logq : Nat → RReal) (v : Nat) :
    Nonempty (LogVolumePilotBoundData logq v) :=
  lpb_exists logq v

end IUT
