/-
  IUT/IndeterminacyRealAction.lean — M332F（柱D 本丸の横展開:
  **3 不定性 (Ind1)(Ind2)(Ind3) の作用を、実テータパイロット体積
  （M319F, 実 deg_ℝ = Arakelov 局所次数）へ昇格**）

  ── 主要成果の分類: **[実]**（既存 IndAction 系（M241F/M254F/M259F）の
     **toy/算術模型（QDiv・degZ・Bool³ 軌道）を実 deg_ℝ 体積へ置換 (a) 昇格**）。
     complete_pct 影響: **柱D（定理3.11・体積側の不定性作用）の実 IUT 完全
     証明率を前進させる**。従来、3 つの不定性の作用（(Ind1) ラベル置換・
     (Ind2) 単数トーソル・(Ind3) 膨張）は、有効因子モノイド QDiv の
     **整数次数 degZ**（`w : ℕ→ℕ` 自然数重み・重複度 ℕ 値）の上で
     `IndAction`/`PermIndAction`/`FullIndAction` として構成されていた
     （M241F は「単数は重み 0 のエタール座標に宿らせた degZ 不変軌道」、
     M254F は「等重み座標の置換 `degZ_swap` が degZ 保存」、M259F は
     「Bool³ 混合次数 = 等号 ⊕ 下界」）。本層はその作用主語を、M319F
     `thPilotTotalVol`（実テータパイロット総体積 Σ_{j=1}^n deg_ℝ(Θ(q,u_j))
     = (Σj²)·log q_v、本物の ℝ = RReal 上の実 deg_ℝ）と、M312F
     `logVolLocal`（実 Arakelov 局所次数 n·log q_v）の上へ載せ替える。
     すなわち 3 不定性が **実テータパイロット体積 Σj²·log q_v** にどう作用
     するかを実 deg_ℝ で本物構成する:

       (Ind1) 等重みラベル置換 → **Σj² は置換不変（deg_ℝ 厳密保存）**、
       (Ind2) 単数作用（v(単数)=0） → **付値 0 の寄与ゆえ deg_ℝ 保存**、
       (Ind3) 膨張（v ≥ 0 の寄与） → **deg_ℝ を増大（下界保持）**。

     toy 主語（degZ・QDiv・m202fVol）は本層では作用の**主語**として一切
     用いない——主語は M319F の実総体積と M312F の実 Arakelov 次数である。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M332F-0 `indR_natExp` / `indR_realTotal` / `indR_realTotal_closed`
      — **実テータパイロット体積の一般化**: ラベル指数関数 g:ℕ→ℕ に沿った
        実 deg_ℝ 総体積 Σ_{k<n} deg_ℝ(g k) = Σ_{k<n}(g k)·log q_v（全て
        同一素点 v の実重み logq v）と、その **閉形式** ≈ logVolLocal v (Σ g)
        （M312F `logVolLocal_add` で束ねる）。既定指数 `indR_natExp k=(k+1)²`
        （ラベル j=k+1 の指数 j²）。`indR_natExp_sum`: Σ = sumSq（M1 Σj²）。
  * M332F-1 `indR_ind1_preserves`（**(Ind1) 等重み置換の実作用**）
      — l-捻れラベル j の置換（互換 swapMult）が実 deg_ℝ 総体積を保つ
        （Σ_{σj} j² = Σj²、置換不変＝deg_ℝ 厳密保存）。M254F の degZ 置換
        不変を**実 deg_ℝ へ昇格**。組合せ核は既存の実 Nat 補題
        `nsum_two_point_eq`（二点入替不変、M254F）を再利用し、主語を実
        deg_ℝ 体積へ載せた（logVolLocal/logVolSum が主語）。
  * M332F-2 `indR_ind2_unit`（**(Ind2) 単数作用の実作用**）
      — 単数 O_v^× の作用はテータ値に単数倍を掛ける＝付値 0 の寄与
        （v(単数)=0）ゆえ実 deg_ℝ を保つ: deg_ℝ(unit·Θ)=deg_ℝ(Θ)+
        deg_ℝ(unit) かつ deg_ℝ(unit)=logVolLocal v 0 ≈ 0（M312F
        `logVolLocal_zero`）。M241F の重み 0 座標 degZ 不変の**実 deg_ℝ 版**
        （多輻性の芽）。
  * M332F-3 `indR_ind3_dilation`（**(Ind3) 膨張の実作用**）
      — 膨張は付値 ≥0 の寄与 logVolLocal v m（m≥0）を上乗せし、非負重み
        （log q_v ≥0）の下で実 deg_ℝ を**増大（下界保持以上）**:
        V ≤ V + logVolLocal v m。M259F の膨張の下界制約の**実 deg_ℝ 版**
        （M312F `logVol_rmul_nonneg` の非負性）。
  * M332F-4 `indR_simultaneous`（**(Ind1)×(Ind2) 同時作用**）
      — 置換 ⊕ 単数の同時作用が実総体積を保つ（deg_ℝ 混合挙動の実版、
        M259F Bool³ の実 deg_ℝ 部分版）。**crux（多輻的アルゴリズム本体
        Dβ-ω＝IUT 論争の係争点）は範囲外**。
  * M332F-5 capstone `IndRealActionData` / `indRealActionData` /
        `indR_exists` / `indR_ind1_invariant`（(Ind1) が実テータパイロット
        体積を保存）/ `indR_multiradial_seed`（多輻性の芽の実版）。
  * 実例: l=5（l⋇=2, n=2）で (Ind1) 置換不変（実 deg_ℝ）・(Ind2) 単数不変
        を具体確認。nsum indR_natExp 2 = sumSq 2 = 5。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）

  - **本物（完全証明）**:
    ・(Ind1) 置換の Σj² 不変（`indR_ind1_preserves`）は実 deg_ℝ 体積の上で
      本物: 組合せ核 `nsum_two_point_eq`（既存の実 Nat 二点入替不変）を、
      閉形式 `indR_realTotal_closed`（M312F logVolLocal_add）経由で実 deg_ℝ
      総体積へ持ち上げた。従来 degZ（QDiv 整数次数）だった主語が **本物の
      実 deg_ℝ = Arakelov 次数** へ昇格。
    ・(Ind2) 単数作用の deg_ℝ 不変（`indR_ind2_unit`）は本物: 単数の付値
      0 の寄与 logVolLocal v 0 ≈ 0（M312F logVolLocal_zero）で実 deg_ℝ を
      保つ。M241F の重み 0 座標次数不変の実 deg_ℝ 化。
    ・実テータパイロット体積 = M319F `thPilotTotalVol`（本物の実 deg_ℝ）で
      あり、その一般化 `indR_realTotal` の閉形式・(Ind1) 不変・(Ind2) 不変・
      (Ind3) 下界は core Lean のみで完全証明。`indR_ind1_invariant` は置換
      後の実総体積が **M319F の実テータパイロット総体積そのもの**に一致する
      ことを言明（実 deg_ℝ で閉じた本物）。
  - **正直申告（未達・witness・後続。飾りでなく地図）**:
    ・log q_v（実重み `logq : ℕ→RReal`）は M312F/M319F と同じく**実重み
      witness**（係数扱い）。log q_v の超越性・具体値・u=q^{1/2l} の体内
      実在は本層の範囲外（柱A/柱C の後続）。
    ・(Ind1) 置換は**互換（二点入替）**の実 deg_ℝ 不変で本物。一般の
      対称群 S_{l⋇} 全体の実作用（互換の合成による任意置換）は互換不変
      から従うが、本層は互換の単一適用を本物として据え、任意置換への
      閉包は据えない（互換生成の反復は後続の定型）。
    ・(Ind3) 膨張・(Ind1)×(Ind2) 同時作用は**主要部分＋骨組み**: 膨張は
      「付値 ≥0 の寄与を上乗せ」・同時作用は「置換 ⊕ 単数の deg_ℝ 保存の
      合成」を実 deg_ℝ で本物に据えるが、(Ind1)×(Ind2)×(Ind3) の完全同時
      作用（M259F Bool³ の実 deg_ℝ 全展開、等号 ⊕ 下界の混合）の実版は
      主要部分に留める。
    ・**多輻的アルゴリズム本体 Dβ-ω（crux＝論争の係争点）は恒久的に本層の
      範囲外**——本層は 3 不定性の作用を実 deg_ℝ 上で構成するのみで、
      crux（LHS と RHS を突き合わせる不等式）の証明ではない（過大主張禁止）。
    ・単数作用・膨張は「付値の寄与」の実 deg_ℝ 上の代数的挙動であり、原論文
      の log-shell 上の単数積分・上方両立の解析的内容は写像しない（M55F/
      M202F の正直申告の継続）。
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ deg_ℝ の保存・閉形式・
      下界は realEq/rLe で言明する（M312F/M319F と同じ正直な形）。
  全て新規 Classical.choice を証明本体に導入せず（M312F/M319F/M254F/M1 から
  継承、#print axioms は propext/Quot.sound 系のみ）。sorry 皆無・禁止
  タクティク不使用（core Lean のみ）。サブエージェント新規 1 本（共有
  ファイル未変更）。一般名は `indR` 接頭辞で衝突回避。
-/
import IUT.ThetaPilotRealVolume
import IUT.IndActionLabel

namespace IUT

/-! ## M332F-0: 実テータパイロット体積の一般化（ラベル指数関数に沿った実 deg_ℝ 総体積） -/

/-- **M332F-0a: 既定ラベル指数** — ラベル j=k+1 の l-捻れ点のテータ値の指数 j²。
    位置 k（0-based）はラベル j=k+1 に対応し、指数は (k+1)²。 -/
def indR_natExp (k : Nat) : Nat := (k + 1) * (k + 1)

/-- **M332F-0b: ラベル指数関数に沿った実 deg_ℝ 総体積** — Σ_{k<n} deg_ℝ(g k)
    = Σ_{k<n}(g k)·log q_v。全項が同一素点 v の実重み logq v を共有する
    （テータパイロットは単一素点の総体積）。M312F `logVolSum` に定数重み
    `fun _ => logq v` を与えたもの。既定 g=`indR_natExp` で M319F の
    `thPilotTotalVol` に一致する（`indR_thPilot_bridge`）。 -/
def indR_realTotal (logq : Nat → RReal) (v : Nat) (g : Nat → Nat) (n : Nat) : RReal :=
  logVolSum (fun k => ((g k : Nat) : Int)) (fun _ => logq v) n

/-- **M332F-0c: 実総体積の閉形式** — 実 deg_ℝ 総体積は整数和 Σ g の実 deg_ℝ
    に一致する（realEq、ℝ は setoid）: indR_realTotal g n ≈ logVolLocal v (Σ_{k<n} g k)。
    各項 (g k)·log q_v を M312F `logVolLocal_add` で束ね、整数和 `nsum g n`
    へ落とす（M319F `thPilot_total_closed` の一般指数版）。 -/
theorem indR_realTotal_closed (logq : Nat → RReal) (v : Nat) (g : Nat → Nat) :
    ∀ n, realEq (indR_realTotal logq v g n)
      (logVolLocal logq v ((nsum g n : Nat) : Int)) := by
  intro n
  induction n with
  | zero =>
    show realEq realZero (logVolLocal logq v 0)
    exact realEq_symm (logVolLocal_zero logq v)
  | succ p ih =>
    show realEq (realAdd (indR_realTotal logq v g p)
          (logVolLocal logq v ((g p : Nat) : Int)))
        (logVolLocal logq v ((nsum g (p + 1) : Nat) : Int))
    have hcoeff : ((nsum g (p + 1) : Nat) : Int)
        = ((nsum g p : Nat) : Int) + ((g p : Nat) : Int) := by
      have hs : nsum g (p + 1) = nsum g p + g p := rfl
      rw [hs, Int.natCast_add]
    rw [hcoeff]
    refine realEq_trans (realAdd_congr_left
      (logVolLocal logq v ((g p : Nat) : Int)) ih) ?_
    exact realEq_symm (logVolLocal_add logq v ((nsum g p : Nat) : Int) ((g p : Nat) : Int))

/-- **M332F-0d: 既定指数和 = Σj²（M1 sumSq）** — Σ_{k<n}(k+1)² = Σ_{j=1}^n j²。
    実テータパイロット体積の閉形式が M319F の sumSq（ガウス簿記 Σj²）に
    一致することを保証する橋。 -/
theorem indR_natExp_sum (n : Nat) : nsum indR_natExp n = sumSq n := by
  induction n with
  | zero => rfl
  | succ p ih =>
    show nsum indR_natExp p + (p + 1) * (p + 1) = sumSq (p + 1)
    rw [ih, sumSq_succ]

/-- **M332F-0e: M319F テータパイロット体積とのブリッジ** — 既定指数での実総体積は
    M319F の実テータパイロット総体積そのものに一致する（realEq）:
    thPilotTotalVol v n ≈ indR_realTotal indR_natExp n。両者の閉形式
    （M319F sumSq・本層 nsum indR_natExp）が `indR_natExp_sum` で一致するため。 -/
theorem indR_thPilot_bridge (logq : Nat → RReal) (v : Nat) (n : Nat) :
    realEq (thPilotTotalVol logq v n) (indR_realTotal logq v indR_natExp n) := by
  refine realEq_trans (thPilot_total_closed logq v n) ?_
  rw [← indR_natExp_sum n]
  exact realEq_symm (indR_realTotal_closed logq v indR_natExp n)

/-! ## M332F-1: (Ind1) 等重みラベル置換の実作用（Σj² 置換不変＝実 deg_ℝ 保存） -/

/-- **M332F-1 (本丸): (Ind1) 置換は実 deg_ℝ 総体積を保つ** — l-捻れラベルの
    互換（swapMult a b、位置 a,b < n の入替）は実テータパイロット体積を
    保存する（Σ_{σj} j² = Σj²、置換不変＝実 deg_ℝ 厳密保存）。
    組合せ核は既存の実 Nat 補題 `nsum_two_point_eq`（M254F の二点入替不変）を
    再利用し、閉形式 `indR_realTotal_closed`（M312F logVolLocal_add）経由で
    **実 deg_ℝ 総体積**へ持ち上げる（主語は degZ でなく logVolLocal）。
    M254F の degZ 置換不変を実 Arakelov 次数へ昇格したもの。 -/
theorem indR_ind1_preserves (logq : Nat → RReal) (v a b n : Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) :
    realEq (indR_realTotal logq v (swapMult a b indR_natExp) n)
      (indR_realTotal logq v indR_natExp n) := by
  have hswap : nsum (swapMult a b indR_natExp) n = nsum indR_natExp n :=
    nsum_two_point_eq (swapMult a b indR_natExp) indR_natExp a b n hab ha hb
      (fun k hka hkb => swapMult_other a b indR_natExp k hka hkb)
      (by rw [swapMult_left, swapMult_right a b indR_natExp hab]; exact Nat.add_comm _ _)
  refine realEq_trans (indR_realTotal_closed logq v (swapMult a b indR_natExp) n) ?_
  rw [hswap]
  exact realEq_symm (indR_realTotal_closed logq v indR_natExp n)

/-! ## M332F-2: (Ind2) 単数作用の実作用（付値 0 の寄与＝実 deg_ℝ 保存） -/

/-- **M332F-2a: (Ind2) 単数作用（実 deg_ℝ）** — 単数 O_v^× の作用はテータ値に
    単数倍を掛ける＝付値 μ の寄与 logVolLocal v μ を実体積に上乗せする。
    単数なら v(単数)=μ=0。 -/
def indR_ind2Vol (logq : Nat → RReal) (v : Nat) (V : RReal) (μ : Int) : RReal :=
  realAdd V (logVolLocal logq v μ)

/-- **M332F-2 (本丸): 単数作用は実 deg_ℝ を保つ** — 単数の付値 μ=0（v(単数)=0）
    ゆえ、単数作用は実テータパイロット体積を保存する:
    deg_ℝ(unit·Θ) = deg_ℝ(Θ) + logVolLocal v 0 ≈ deg_ℝ(Θ)
    （M312F `logVolLocal_zero`: 付値 0 の寄与は実 deg_ℝ 0）。M241F の
    「重み 0 座標は degZ に効かない」の**実 deg_ℝ = Arakelov 次数版**。 -/
theorem indR_ind2_unit (logq : Nat → RReal) (v : Nat) (V : RReal) (μ : Int)
    (hμ : μ = 0) : realEq (indR_ind2Vol logq v V μ) V := by
  show realEq (realAdd V (logVolLocal logq v μ)) V
  rw [hμ]
  refine realEq_trans (realAdd_congr_right V (logVolLocal_zero logq v)) ?_
  exact realAdd_zero V

/-! ## M332F-3: (Ind3) 膨張の実作用（付値 ≥0 の寄与＝実 deg_ℝ 増大／下界保持） -/

/-- **M332F-3a: (Ind3) 膨張作用（実 deg_ℝ）** — 膨張は付値 m の寄与
    logVolLocal v m を実体積に上乗せする。膨張は m≥0（体積の拡大方向）。 -/
def indR_ind3Vol (logq : Nat → RReal) (v : Nat) (V : RReal) (m : Int) : RReal :=
  realAdd V (logVolLocal logq v m)

/-- **M332F-3 (本丸): 膨張は実 deg_ℝ を増大（下界保持以上）** — 膨張の付値
    寄与 m≥0 は、非負重み（log q_v ≥0）の下で実テータパイロット体積を
    増大させる: V ≤ V + logVolLocal v m（M312F `logVol_rmul_nonneg`: 非負
    係数×非負重み＝非負寄与）。M259F の膨張の下界制約（degZ 単調増加）の
    **実 deg_ℝ 版**。 -/
theorem indR_ind3_dilation (logq : Nat → RReal) (v : Nat) (V : RReal) (m : Int)
    (hm : 0 ≤ m) (hq : rLe realZero (logq v)) :
    rLe V (indR_ind3Vol logq v V m) := by
  show rLe V (realAdd V (logVolLocal logq v m))
  have hterm : rLe realZero (logVolLocal logq v m) := by
    show rLe realZero (rmul (intToReal m) (logq v))
    exact logVol_rmul_nonneg (intToReal_mono hm) hq
  have hpair : rLe (realAdd V realZero) (realAdd V (logVolLocal logq v m)) :=
    rLe_add_pair (rLe_refl V) hterm
  exact rLe_congr (realAdd_zero V) (realEq_refl (realAdd V (logVolLocal logq v m))) hpair

/-! ## M332F-4: (Ind1)×(Ind2) 同時作用（置換 ⊕ 単数の実 deg_ℝ 保存） -/

/-- **M332F-4: (Ind1)×(Ind2) 同時作用は実 deg_ℝ を保つ** — l-捻れラベル置換
    （互換 swapMult a b）と単数作用（付値 0）を実テータパイロット体積に
    **同時**に作用させても実 deg_ℝ は保存される: 単数を掛けた置換後の実総体積が
    非置換の実総体積に一致する（realEq）。deg_ℝ 混合挙動の実版（M259F Bool³ の
    実 deg_ℝ 部分版）。**crux（多輻的アルゴリズム本体 Dβ-ω）は範囲外**——
    本層は置換 ⊕ 単数の deg_ℝ 保存の合成のみで、crux 不等式の証明ではない。 -/
theorem indR_simultaneous (logq : Nat → RReal) (v a b n : Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) :
    realEq
      (indR_ind2Vol logq v (indR_realTotal logq v (swapMult a b indR_natExp) n) 0)
      (indR_realTotal logq v indR_natExp n) :=
  realEq_trans
    (indR_ind2_unit logq v (indR_realTotal logq v (swapMult a b indR_natExp) n) 0 rfl)
    (indR_ind1_preserves logq v a b n hab ha hb)

/-! ## M332F-5: capstone -/

/-- **M332F-5a: 3 不定性の実作用データ** — 実テータパイロット体積（M319F）への
    3 つの不定性 (Ind1)(Ind2)(Ind3) の実 deg_ℝ 作用を束ねる: 実総体積・
    3 作用と、(Ind1) 置換不変（Σj² 保存）・(Ind2) 単数不変（付値 0）・
    (Ind3) 膨張下界。主語は M319F/M312F の本物の実 deg_ℝ であり、toy degZ を
    作用の主語に用いない。 -/
structure IndRealActionData (logq : Nat → RReal) (v : Nat) where
  /-- 実テータパイロット総体積（既定指数）Σj²·log q_v。 -/
  totalVol : Nat → RReal
  /-- (Ind1) ラベル指数関数に沿った実 deg_ℝ 総体積（置換で並べ替え可）。 -/
  ind1 : (Nat → Nat) → Nat → RReal
  /-- (Ind2) 単数作用（付値 μ の寄与を上乗せ）。 -/
  ind2 : RReal → Int → RReal
  /-- (Ind3) 膨張作用（付値 m の寄与を上乗せ）。 -/
  ind3 : RReal → Int → RReal
  /-- (Ind1) 互換は実 deg_ℝ 総体積を保つ（Σ_{σj} j² = Σj²、置換不変）。 -/
  ind1_preserves : ∀ (a b n : Nat), ¬ a = b → a < n → b < n →
    realEq (ind1 (swapMult a b indR_natExp) n) (ind1 indR_natExp n)
  /-- (Ind2) 単数作用（付値 0）は実 deg_ℝ を保つ。 -/
  ind2_unit : ∀ (V : RReal) (μ : Int), μ = 0 → realEq (ind2 V μ) V
  /-- (Ind3) 膨張（付値 m≥0）は非負重みの下で実 deg_ℝ を増大（下界保持）。 -/
  ind3_dilation : ∀ (V : RReal) (m : Int), 0 ≤ m → rLe realZero (logq v) →
    rLe V (ind3 V m)

/-- **M332F-5b: 実データ** — 全フィールドを M332F-0〜3 の本物で充足。
    実総体積・3 作用・(Ind1) 置換不変・(Ind2) 単数不変・(Ind3) 膨張下界を
    実 deg_ℝ 対象で埋める。 -/
def indRealActionData (logq : Nat → RReal) (v : Nat) : IndRealActionData logq v where
  totalVol := thPilotTotalVol logq v
  ind1 := indR_realTotal logq v
  ind2 := indR_ind2Vol logq v
  ind3 := indR_ind3Vol logq v
  ind1_preserves := fun a b n hab ha hb => indR_ind1_preserves logq v a b n hab ha hb
  ind2_unit := fun V μ hμ => indR_ind2_unit logq v V μ hμ
  ind3_dilation := fun V m hm hq => indR_ind3_dilation logq v V m hm hq

/-- **M332F-5c: 存在** — 任意の実重み logq・素点 v に対し、実テータパイロット
    体積への 3 不定性の実 deg_ℝ 作用データが存在する。従来 degZ（QDiv）だった
    作用主語が **本物の実 deg_ℝ = Arakelov 次数** へ昇格される。 -/
theorem indR_exists (logq : Nat → RReal) (v : Nat) :
    Nonempty (IndRealActionData logq v) :=
  ⟨indRealActionData logq v⟩

/-- **M332F-5d: (Ind1) は実テータパイロット体積を保存**（capstone・本丸再掲） —
    l-捻れラベルの互換 (Ind1) を適用した実総体積は、M319F の実テータパイロット
    総体積 `thPilotTotalVol`（本物の実 deg_ℝ）**そのもの**に一致する（realEq）。
    Σj² の置換不変性が実 Arakelov 次数の上で閉じたことの言明。 -/
theorem indR_ind1_invariant (logq : Nat → RReal) (v a b n : Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) :
    realEq (indR_realTotal logq v (swapMult a b indR_natExp) n)
      (thPilotTotalVol logq v n) :=
  realEq_trans (indR_ind1_preserves logq v a b n hab ha hb)
    (realEq_symm (indR_thPilot_bridge logq v n))

/-- **M332F-5e: 多輻性の芽（実版）** — 3 不定性の実 deg_ℝ 挙動を一つに束ねる:
    (1) (Ind1) 置換は実 deg_ℝ を保つ（Σj² 不変）、(2) (Ind2) 単数（付値 0）は
    実 deg_ℝ を保つ、(3) (Ind3) 膨張（付値 m≥0）は実 deg_ℝ を増大（下界保持）。
    軌道共変性（Ind1/Ind2 は等値・Ind3 は下界）の実 deg_ℝ 版＝多輻性の芽。
    **crux（多輻的アルゴリズム本体 Dβ-ω）は範囲外**（過大主張禁止）。 -/
theorem indR_multiradial_seed (logq : Nat → RReal) (v a b n : Nat) (V : RReal) (m : Int)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) (hm : 0 ≤ m)
    (hq : rLe realZero (logq v)) :
    realEq (indR_realTotal logq v (swapMult a b indR_natExp) n)
        (indR_realTotal logq v indR_natExp n)
      ∧ realEq (indR_ind2Vol logq v V 0) V
      ∧ rLe V (indR_ind3Vol logq v V m) :=
  ⟨indR_ind1_preserves logq v a b n hab ha hb,
   indR_ind2_unit logq v V 0 rfl,
   indR_ind3_dilation logq v V m hm hq⟩

/-! ## 実例（l=5, l⋇=2, n=2: ラベル j=1,2, Σj²=1²+2²=5） -/

/-- 実例: 既定指数和 Σ_{k<2}(k+1)² = sumSq 2 = 1²+2² = 5。 -/
example : nsum indR_natExp 2 = 5 := rfl

/-- 実例: sumSq 2 = 5（M319F 実テータパイロット体積の閉形式係数）。 -/
example : sumSq 2 = 5 := rfl

/-- 実例: l=5（n=2）で (Ind1) ラベル置換（位置 0,1＝ラベル j=1,2 の互換）は
    実テータパイロット体積を保存する（実 deg_ℝ の Σj² 置換不変）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2)
      (thPilotTotalVol logq v 2) :=
  indR_ind1_invariant logq v 0 1 2 (by omega) (by omega) (by omega)

/-- 実例: l=5（n=2）で (Ind2) 単数作用（付値 0）は実テータパイロット体積を
    保存する（実 deg_ℝ 単数不変）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (indR_ind2Vol logq v (thPilotTotalVol logq v 2) 0) (thPilotTotalVol logq v 2) :=
  indR_ind2_unit logq v (thPilotTotalVol logq v 2) 0 rfl

/-- 実例: l=5（n=2）で (Ind3) 膨張（付値 m=1）は非負重みの下で実テータ
    パイロット体積を増大させる（下界保持以上）。 -/
example (logq : Nat → RReal) (v : Nat) (hq : rLe realZero (logq v)) :
    rLe (thPilotTotalVol logq v 2)
      (indR_ind3Vol logq v (thPilotTotalVol logq v 2) 1) :=
  indR_ind3_dilation logq v (thPilotTotalVol logq v 2) 1 (by omega) hq

end IUT
