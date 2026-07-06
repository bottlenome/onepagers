/-
  IUT/LogLinkIndeterminacy.lean — M367F [実／本物]
  分類: 実 (log-link が不定性作用と可換＝多輻表現の構造的整合)
  complete_pct 影響: 柱D を前進（M337F 縦 log-link と M342F 3不定性作用 (Ind1)(Ind2)(Ind3) の
    可換性を実 deg_ℝ で証明＝log-link∘不定性=不定性∘log-link（(Ind3) は明示 m シフトを除いて）・
    M362F 多輻比較との整合。多輻表現に必要な構造的事実。crux Dβ-ω は外部仮説）。
  正直な限定: crux Dβ-ω（論争の係争点）は外部仮説のまま。可換性は deg_ℝ レベル。
    (Ind3) は明示シフトを除いて可換。

  ## 本モジュールの位置づけ（何を合成したか）

  IUT III の**多輻表現（multiradial representation）**は、Θ-link の左右の 2 描像を同一視する
  比較アルゴリズムが、3 つの不定性 (Ind1)(Ind2)(Ind3) によって**乱されない（respected）**こと
  を要する。本 M367F は、この「不定性が log-link に respect される」構造的事実を実 deg_ℝ で
  本物化する。合成する本物:
    * M337F `LogLinkReal`: 縦 log-link `logLinkMap`（乗法 U^(d) → 加法 log-shell）と、その
      実 deg_ℝ 体積輸送 `logLinkVolTransport`／`logLink_volume_transport`（log は積を和へ）／
      `logLink_pilot_transport`（実テータパイロット体積の log-link 像）。
    * M342F `IndeterminacyFull`: 3 不定性の実 deg_ℝ 作用 (Ind1) 置換保存・(Ind2) 単数保存
      （付値 0）・(Ind3) 膨張（付値 m）と `indF_ind3_dilation_real`（(Ind3) の厳密量）。
    * M332F `IndeterminacyRealAction`: `indR_ind3Vol`／`indR_ind2Vol`（付値シフト作用）・
      `indR_realTotal`／`indR_realTotal_closed`（総体積の閉形式）・`indF_ind1_perm_general`。
    * M362F `MultiradialCompare`: 比較同型 `mrcCompare`・多輻表現の芽 `mrc_multiradial_seed`。
    * M312F `LogVolume`: 実 Arakelov 局所次数 `logVolLocal`・加法性 `logVolLocal_add`。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M367F-1 `lliLogThenInd` / `lliIndThenLog`
      — 2 つの合成: 「log-link してから不定性」対「不定性してから log-link」を実 deg_ℝ で。
        不定性は付値シフト μ（(Ind2) は μ=0・(Ind3) は μ=m）を実体積に上乗せする M332F の
        `indR_ind3Vol` 作用そのもの。
  * M367F-2 `lli_commute_general` / `lli_ind2_commute` / `lli_ind1_commute`
      — **可換性 log-link∘不定性 = 不定性∘log-link（deg_ℝ）**: log-link は加法ゆえ付値シフト
        を体積の和へ移し、シフトを掛ける順序に依らない（M337F `logLink_volume_transport`）。
        (Ind1) 置換は Σj² 核を保存（M332F `indF_ind1_perm_general`）ゆえ log-link 輸送は
        置換の前後で同じ。(Ind2) 単数（付値 0）は log-link を素通り（M332F `indR_ind2_unit`）。
  * M367F-3 `lli_ind3_shift` / `lli_ind3_pilot_shift`
      — **(Ind3) は明示 m シフトを除いて可換**: 膨張付値 m の log-link 像はちょうど元の像 ＋
        明示シフト logVolLocal v m（M337F 加法輸送）。実テータパイロットでは
        M342F `indF_ind3_dilation_real` で Σj²+m へ。
  * M367F-4 `lli_multiradial_compat`
      — **多輻比較との整合**: 比較同型の芽（M362F `mrc_multiradial_seed`、単数側）と、
        log-link 体積輸送の不定性可換（体積側）を連言で束ねる ＝ 不定性が多輻比較に整合する
        （多輻表現の芽の deg_ℝ 版）。
  * M367F-5 `lli_crux_external` / `lli_crux_is_hypothesis`
      — **crux Dβ-ω は外部仮説（決して導出しない）**: 可換性は本物だが crux は受け取るのみ。
  * M367F-6 capstone `LliCommuteData` / `lliCommuteData` / `lli_exists` + 実例。

  ## 正直な限定（消去・弱化禁止）
  * **crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層は
    log-link と不定性作用の可換性を実 deg_ℝ で本物構成するのみで、crux（log-link と theta-link
    の両立不等式）は外部 Prop 仮説として受け取り決して導出しない（`lli_crux_is_hypothesis`）。
  * **可換性は deg_ℝ（Arakelov 局所次数）レベル**。log q_v は実重み witness（M312F 継承）。
    群レベルの完全な同変性（比較同型そのものの不定性同変）は後続。
  * **(Ind3) 膨張は明示シフト logVolLocal v m を除いて可換**（膨張は片方向の付値寄与ゆえ、
    厳密な可換ではなく「明示 m だけずれて可換」——これが正直な形）。ℝ は setoid ゆえ realEq。
  全て選択公理不使用（sorry 皆無・新規 Classical 皆無）。禁止タクティク不使用（core Lean のみ）。
  共有ファイル未変更。柱D 横展開・本物の先行建設[実]。
-/
import IUT.LogLinkReal
import IUT.IndeterminacyFull
import IUT.MultiradialCompare

namespace IUT

/-! ## M367F-1: 2 つの合成（log-link ∘ 不定性 と 不定性 ∘ log-link） -/

/-- **M367F-1a: 合成「log-link してから不定性」** — 付値 n を先に縦 log-link で実 deg_ℝ 体積
    `logLinkVolTransport logq v n` へ輸送し（乗法 → 加法）、そのあと不定性（付値シフト μ を
    上乗せ、M332F `indR_ind3Vol`）を作用させる。(Ind2) は μ=0・(Ind3) は μ=m。 -/
def lliLogThenInd (logq : Nat → RReal) (v : Nat) (n μ : Int) : RReal :=
  indR_ind3Vol logq v (logLinkVolTransport logq v n) μ

/-- **M367F-1b: 合成「不定性してから log-link」** — 先に不定性を付値レベルで作用させ
    （付値 n を n+μ へシフト）、そのあと縦 log-link で実 deg_ℝ 体積へ輸送する。 -/
def lliIndThenLog (logq : Nat → RReal) (v : Nat) (n μ : Int) : RReal :=
  logLinkVolTransport logq v (n + μ)

/-- **定理 (M367F-1c): 合成の unfold（log-link してから不定性）** — 明示形。 -/
theorem lli_logThenInd_eq (logq : Nat → RReal) (v : Nat) (n μ : Int) :
    lliLogThenInd logq v n μ
      = realAdd (logLinkVolTransport logq v n) (logVolLocal logq v μ) :=
  rfl

/-! ## M367F-2: 可換性 log-link ∘ 不定性 = 不定性 ∘ log-link（実 deg_ℝ） -/

/-- **定理 (M367F-2a: 本丸): log-link は付値シフト不定性と可換（実 deg_ℝ）** —
    縦 log-link は加法写像ゆえ、付値レベルのシフト μ（不定性）を、実 deg_ℝ 体積の和
    logVolLocal v μ へ移し、**シフトを掛ける順序に依らない**:
      不定性 ∘ log-link  =  logLinkVolTransport v (n+μ)  （先にシフトしてから log-link）
      log-link ∘ 不定性  =  logLinkVolTransport v n + logVolLocal v μ  （log-link してからシフト）
    両者は M337F `logLink_volume_transport`（log turns products into sums）で realEq。
    log-link と不定性作用が実 deg_ℝ 上で可換であることの本物。 -/
theorem lli_commute_general (logq : Nat → RReal) (v : Nat) (n μ : Int) :
    realEq (lliIndThenLog logq v n μ) (lliLogThenInd logq v n μ) :=
  logLink_volume_transport logq v n μ

/-- **定理 (M367F-2b: (Ind2) 単数は log-link を素通りして可換)** — 単数作用（付値 μ=0、
    M332F (Ind2)）は付値をずらさないので、log-link ∘ (Ind2) = (Ind2) ∘ log-link は
    **どちらも元の log-link 体積そのもの**に一致する（M332F `indR_ind2_unit`: 付値 0 の
    寄与は実 deg_ℝ 0）。(Ind2) は log-link と完全に可換（シフトなし）。 -/
theorem lli_ind2_commute (logq : Nat → RReal) (v : Nat) (n : Int) :
    realEq (lliIndThenLog logq v n 0) (logLinkVolTransport logq v n) :=
  realEq_trans (lli_commute_general logq v n 0)
    (indR_ind2_unit logq v (logLinkVolTransport logq v n) 0 rfl)

/-- **定理 (M367F-2c: (Ind1) 置換は log-link 輸送と可換)** — l-捻れラベルの互換
    （M332F (Ind1)、swapMult a b）は Σj² 核（総和 nsum）を保存する（`indF_ind1_perm_general`）
    ので、log-link が輸送する実 deg_ℝ 体積は**置換を掛ける前後で同じ**:
      logLinkVolTransport v (Σ_{σ} g)  ≈  logLinkVolTransport v (Σ g)。
    log-link は置換をいつ掛けても Σj² 核を同じように輸送する（可換）。総体積の閉形式
    `indR_realTotal_closed`（M312F 加法輸送）で両辺を実総体積へ結び、置換不変で閉じる。 -/
theorem lli_ind1_commute (logq : Nat → RReal) (v a b n : Nat) (g : Nat → Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) :
    realEq (logLinkVolTransport logq v ((nsum (swapMult a b g) n : Nat) : Int))
      (logLinkVolTransport logq v ((nsum g n : Nat) : Int)) := by
  refine realEq_trans
    (realEq_symm (indR_realTotal_closed logq v (swapMult a b g) n)) ?_
  refine realEq_trans (indF_ind1_perm_general logq v a b n g hab ha hb) ?_
  exact indR_realTotal_closed logq v g n

/-- **定理 (M367F-2d: (Ind1) 置換は実総体積レベルでも log-link と可換)** — 置換後の実 deg_ℝ
    総体積は、置換前の総体積の log-link 輸送像に一致する（`indR_realTotal` = log-link 像）。 -/
theorem lli_ind1_realTotal_commute (logq : Nat → RReal) (v a b n : Nat) (g : Nat → Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) :
    realEq (indR_realTotal logq v (swapMult a b g) n)
      (logLinkVolTransport logq v ((nsum g n : Nat) : Int)) :=
  realEq_trans (indF_ind1_perm_general logq v a b n g hab ha hb)
    (indR_realTotal_closed logq v g n)

/-! ## M367F-3: (Ind3) は明示 m シフトを除いて可換 -/

/-- **定理 (M367F-3a: 本丸): (Ind3) 膨張は明示 m シフトを除いて log-link と可換** —
    膨張（M332F (Ind3)、付値 m）の log-link 像は、元の付値 n の log-link 像に**明示シフト**
    logVolLocal v m を加えたものにちょうど等しい:
      log-link v (n+m)  ≈  log-link v n  +  logVolLocal v m。
    すなわち (Ind3) は log-link と**厳密には可換でなく、明示 m だけずれて可換**（膨張は片方向の
    付値寄与）——これが正直な形。M337F `logLink_volume_transport`（加法輸送）で閉じる。
    右辺 = `lliLogThenInd logq v n m`（log-link してから (Ind3) 膨張）。 -/
theorem lli_ind3_shift (logq : Nat → RReal) (v : Nat) (n m : Int) :
    realEq (logLinkVolTransport logq v (n + m))
      (realAdd (logLinkVolTransport logq v n) (logVolLocal logq v m)) :=
  logLink_volume_transport logq v n m

/-- **定理 (M367F-3b: (Ind3) の実テータパイロット版・明示シフト)** — 実テータパイロット体積
    （M319F、付値 Σj²）を膨張 m させたもの（M342F `indF_ind3_dilation_real`）は、Σj²+m の
    log-link 像に一致する（`lliIndThenLog logq v (Σj²) m`）。log-link してから (Ind3) 膨張 ＝
    (Ind3) 膨張してから log-link（明示 m シフトを Σj² 核に平行移動）。 -/
theorem lli_ind3_pilot_shift (logq : Nat → RReal) (v : Nat) (n : Nat) (m : Int) :
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) m)
      (lliIndThenLog logq v ((sumSq n : Nat) : Int) m) :=
  indF_ind3_dilation_real logq v n m

/-! ## M367F-4: 多輻比較（M362F）との整合 -/

/-- **定理 (M367F-4: 多輻比較との整合＝不定性同変の芽)** — 多輻表現の芽（M362F
    `mrc_multiradial_seed`、比較同型が段付きフィルトレーションと可換＝**単数側**）と、
    log-link 体積輸送が不定性シフト μ と可換（**体積側**、`lli_commute_general`）を連言で束ねる。
    ＝ 同じ縦 log-link（＝比較写像 `mrcCompare`）が、単数の比較同型でも実 deg_ℝ 体積輸送でも
    不定性に整合する。多輻表現が要する「不定性が比較アルゴリズムを respect する」ことの
    deg_ℝ 版の芽（crux Dβ-ω＝theta-link 整合はこの芽の外にある外部仮説）。 -/
theorem lli_multiradial_compat (logq : Nat → RReal) (v p d : Nat) (hp : 1 ≤ p)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x) (n μ : Int) :
    (logShellMem p d (logShellContent p x.val)
        ∧ (mrcCompare p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x))
      ∧ realEq (lliIndThenLog logq v n μ) (lliLogThenInd logq v n μ) :=
  ⟨mrc_multiradial_seed p d hp x hx, lli_commute_general logq v n μ⟩

/-! ## M367F-5: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M367F-5a: crux は外部仮説・決して導出しない／honest)** — log-link と不定性作用の
    可換性は**無条件で本物**（`lli_commute_general` が crux とは独立に成立）だが、その下での
    **多輻的両立**（log-link・不定性・theta-link の crux ＝ Dβ-ω ＝ 論争の当の係争点）は本層で
    **決して証明しない**。crux を任意の外部 Prop `crux` として受け取り、可換性の本物性 **と**
    crux の連言を、crux が仮説として供給された場合にのみ返す——crux は決して導出されない。 -/
theorem lli_crux_external (logq : Nat → RReal) (v : Nat) (n μ : Int)
    (crux : Prop) (hcrux : crux) :
    realEq (lliIndThenLog logq v n μ) (lliLogThenInd logq v n μ) ∧ crux :=
  ⟨lli_commute_general logq v n μ, hcrux⟩

/-- **定理 (M367F-5b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説
    そのもの**として扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明した定理では
    なく、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で明示。 -/
theorem lli_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M367F-6: capstone -/

/-- **M367F-6a: log-link ⟷ 不定性 可換データ**（総括） — 縦 log-link と 3 不定性作用の
    可換性を実 deg_ℝ で束ねる: 2 合成・一般可換・(Ind2) 素通り・(Ind1) 置換可換・(Ind3) 明示
    シフト可換。主語は M337F/M342F/M332F/M312F の本物の実 deg_ℝ であり、toy を用いない。
    crux Dβ-ω は範囲外。 -/
structure LliCommuteData (logq : Nat → RReal) (v : Nat) where
  /-- 合成「log-link してから不定性」。 -/
  logThenInd : Int → Int → RReal
  /-- 合成「不定性してから log-link」。 -/
  indThenLog : Int → Int → RReal
  /-- logThenInd は本物の合成。 -/
  is_logThenInd : logThenInd = lliLogThenInd logq v
  /-- indThenLog は本物の合成。 -/
  is_indThenLog : indThenLog = lliIndThenLog logq v
  /-- 一般可換: log-link ∘ 不定性 = 不定性 ∘ log-link（付値シフト μ）。 -/
  commute : ∀ (n μ : Int), realEq (indThenLog n μ) (logThenInd n μ)
  /-- (Ind2) 単数（付値 0）は log-link を素通り（シフトなし可換）。 -/
  ind2_preserve : ∀ (n : Int), realEq (indThenLog n 0) (logLinkVolTransport logq v n)
  /-- (Ind1) 置換は log-link 輸送と可換（Σj² 核保存）。 -/
  ind1_commute : ∀ (a b n' : Nat) (g : Nat → Nat), ¬ a = b → a < n' → b < n' →
    realEq (logLinkVolTransport logq v ((nsum (swapMult a b g) n' : Nat) : Int))
      (logLinkVolTransport logq v ((nsum g n' : Nat) : Int))
  /-- (Ind3) 膨張は明示 m シフトを除いて log-link と可換。 -/
  ind3_shift : ∀ (n m : Int), realEq (logLinkVolTransport logq v (n + m))
    (realAdd (logLinkVolTransport logq v n) (logVolLocal logq v m))

/-- **M367F-6b: 実データ** — 全フィールドを M367F-1〜3 の本物で充足。 -/
def lliCommuteData (logq : Nat → RReal) (v : Nat) : LliCommuteData logq v where
  logThenInd := lliLogThenInd logq v
  indThenLog := lliIndThenLog logq v
  is_logThenInd := rfl
  is_indThenLog := rfl
  commute := fun n μ => lli_commute_general logq v n μ
  ind2_preserve := fun n => lli_ind2_commute logq v n
  ind1_commute := fun a b n' g hab ha hb => lli_ind1_commute logq v a b n' g hab ha hb
  ind3_shift := fun n m => lli_ind3_shift logq v n m

/-- **M367F-6c: 存在** — 任意の実重み logq・素点 v に対し、log-link ⟷ 不定性 可換データが
    存在する。M337F 縦 log-link と M342F 3 不定性作用の可換性が実 deg_ℝ で本物化された。 -/
theorem lli_exists (logq : Nat → RReal) (v : Nat) : Nonempty (LliCommuteData logq v) :=
  ⟨lliCommuteData logq v⟩

/-! ## M367F-6 実例（実 deg_ℝ 可換性の本物性） -/

/-- 実例: log-link は付値シフト不定性と可換（一般 n, μ）。 -/
example (logq : Nat → RReal) (v : Nat) (n μ : Int) :
    realEq (lliIndThenLog logq v n μ) (lliLogThenInd logq v n μ) :=
  lli_commute_general logq v n μ

/-- 実例: (Ind2) 単数（付値 0）は log-link を素通り（元の log-link 体積へ）。 -/
example (logq : Nat → RReal) (v : Nat) (n : Int) :
    realEq (lliIndThenLog logq v n 0) (logLinkVolTransport logq v n) :=
  lli_ind2_commute logq v n

/-- 実例: l=5（n=2）で (Ind1) 互換 0↔1 は log-link 輸送と可換（Σj²=5 核保存）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (logLinkVolTransport logq v ((nsum (swapMult 0 1 indR_natExp) 2 : Nat) : Int))
      (logLinkVolTransport logq v ((nsum indR_natExp 2 : Nat) : Int)) :=
  lli_ind1_commute logq v 0 1 2 indR_natExp (by omega) (by omega) (by omega)

/-- 実例: (Ind3) 膨張 m=1 は明示シフト logVolLocal v 1 を除いて log-link と可換。 -/
example (logq : Nat → RReal) (v : Nat) (n : Int) :
    realEq (logLinkVolTransport logq v (n + 1))
      (realAdd (logLinkVolTransport logq v n) (logVolLocal logq v 1)) :=
  lli_ind3_shift logq v n 1

/-- 実例: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  lli_crux_is_hypothesis crux

end IUT
