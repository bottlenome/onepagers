/-
  IUT/GaussPilotRealVolume.lean — M324F（柱D 本丸の横展開:
  **ガウスパイロット log-volume の実対象化＝定理3.11 の体積 RHS を
  m202fVol toy から実 deg_ℝ（Arakelov 局所次数）へ昇格し、テータパイロット
  LHS（M319F）と対にして「crux 仮説の下で両辺実対象の定理3.11 体積不等式」を
  本物で閉じる**）

  ── 主要成果の分類: **[実]**（既存 toy 模型 m202fVol の **本物への置換
     (a) 昇格**）。complete_pct 影響: **柱D（定理3.11・体積側 RHS）の実 IUT
     完全証明率を前進させる**。M319F `ThetaPilotRealVolume.lean` は定理3.11 の
     体積 **LHS（テータパイロット）** を実 deg_ℝ（`logVolLocal`, Arakelov 局所
     次数）へ昇格させたが、**RHS（ガウスパイロット）** は依然として toy 模型
     `m202fVol`（Region=ℤ・vol=id・体積値そのものが領域）を主語とする充足デモ
     （GaussPilot311.lean M216F `gaussBase311Rep` / GaussPilotWeighted.lean
     M158F）に留まっていた——Θ-正則包の体積 `wssq w l` は「id 体積で読んだ整数」
     に過ぎなかった（各層のヘッダに「体積値そのものを領域とする充足デモ模型」と
     正直に明記されている）。本層はその **RHS の体積主語を、M312F の本物の実数値
     Arakelov 局所次数 `logVolLocal`（deg_ℝ: n·log q_v, 本物の ℝ = RReal 上）** へ
     載せ替え、テータパイロット LHS（M319F `thPilotTotalVol`）と **両辺実対象**で
     突き合わせる。そして定理3.11 の体積不等式（テータパイロット ≤ ガウス
     パイロット）を、**crux を明示的仮説として受け取る条件付き定理**として本物で
     閉じる（crux 自体は証明しない）。toy 主語 m202fVol は本層では一切用いない。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M324F-1 `gPilotValueDeg` / `gPilotValueDeg_eq`
      — **単一ガウス因子項の実 deg_ℝ**: deg_ℝ = w(k)·k²·log q_v。M135F
        `wssq`（Σ_{k≤l} w(k)·k²）の各項 w(k)·k² を M312F `logVolLocal`
        （n·log q_v）に接続。実数値で
        gPilotValueDeg logq v w k = rmul(intToReal(w k·(k·k)))(log q_v)。
  * M324F-2 `gPilotTotalVol` / `gPilot_total_closed` / `gPilot_total_wssq`
      — **ガウスパイロット総体積** Σ_{k=0}^{m-1} deg_ℝ(w(k)·k²) を実数値で。
        M312F `logVolLocal_add` で有限和を束ね、**Σ w(k)·k² の閉形式**
        （M135F `wssq` = nsum）へ落とす:
        gPilotTotalVol logq v w (l+1) ≈ logVolLocal logq v (wssq w l)。
        定理3.11 のガウスパイロット体積（RHS）を **実 deg_ℝ** で構成。
  * M324F-3 `gPilot_crux_statement` / `GaussPilotCruxHyp`
      — **crux 不等式の実対象ステートメント**（両辺実 deg_ℝ）:
        `gPilot_crux_statement` = deg_ℝ(Σj²) ≤ deg_ℝ(Σ w(k)·k²)（閉形式版・
        定理3.11 の体積不等式）。`GaussPilotCruxHyp` = crux を**仮説として
        受け取る Prop**（テータパイロット総体積 ≤ ガウスパイロット総体積、
        構成した実体積の上で）。
  * M324F-4 `gPilot_theorem311_conditional` / `gPilot_crux_is_hypothesis`
      — **条件付き定理**（本物で・crux は仮説・還元は本物）: crux 仮説
        `GaussPilotCruxHyp` の下で、閉形式版の定理3.11 体積不等式
        `gPilot_crux_statement`（両辺実 deg_ℝ）が従う。証明は M319F
        `thPilot_total_closed` と本層 `gPilot_total_wssq`（両辺の閉形式）を
        `rLe_congr` で張り替えるだけ——**crux 自体は証明しない**。
        `gPilot_crux_is_hypothesis` は crux が定義上ちょうどこの仮説である
        （それ以上でない）ことを Iff.rfl で明示する。
  * M324F-5 `gPilot_bound_compare` / `gPilot_gap_nonempty`
      — **l³ 下界と RHS の対比**: Nat 側の重み比較 sumSq l ≤ wssq w l を実
        deg_ℝ の順序 rLe へ持ち上げ（M312F `intToReal_mono` + M180
        `rmul_le_mul_right`、非負重み log q_v ≥ 0）。`gPilot_gap_nonempty` は
        M249F `transport_strictly_stronger`（点毎 ⊋ 次数 transport の
        具体 witness＝Dβ-ω が空でない）を再輸出し、両辺の隔たりが実在する
        ことを示す。
  * M324F-6 `gPilot_to_cor312`
      — **crux 仮説から系3.12 への還元（既存接続）**: M249F
        `transportDeg_iff_cor312`（鏡像定理・次数 transport ⟺ Cor312）を
        再利用し、次数レベルの crux から Szpiro/ABC 帰結（Cor312）への還元を
        骨組みで接続。
  * M324F-7 capstone `GaussPilotVolumeData` / `gaussPilotVolumeData` /
        `gPilot_exists` / `gPilot_conditional_theorem311`。
  * 実例: l=5（Σ_{j=1}^{5} j²=55, Σ_{k=0}^{5} 1·k²=55）で LHS・RHS の具体値と
        crux 不等式のステートメント・条件付き定理。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）

  - **本物（完全証明）**:
    ・RHS（ガウスパイロット総体積）の主語は M312F の**本物の実数値 Arakelov
      局所次数** `logVolLocal`（本物の ℝ = RReal 上の n·log q_v）であり、
      **toy 主語 m202fVol（vol=id・領域=ℤ）は用いない**——ここが「RHS の体積
      主語を toy から実へ昇格」の中身。
    ・ガウスパイロット総体積の deg_ℝ 加法性（`logVolLocal_add`）による Σ の
      束ね、および **Σ w(k)·k² 閉形式**（M135F `wssq`=nsum への一致）は完全証明。
    ・**条件付き定理**（crux 仮説 ⟹ 閉形式版の体積不等式）の**還元は本物**:
      両辺の閉形式（M319F LHS・本層 RHS）を `rLe_congr` で張り替える部分は
      完全証明。crux（仮説）を除いた足回りはすべて実対象で閉じている。
    ・l³ 下界の順序 rLe への持ち上げ（`intToReal_mono`・`rmul_le_mul_right`）
      は完全証明。
  - **正直申告（未達・crux・後続。飾りでなく地図。過大主張の厳禁）**:
    ・**crux 不等式（テータパイロット ≤ ガウスパイロット＝Dβ-ω＝多輻的
      アルゴリズム＝IUT 論争の当の係争点）は恒久的に本タスクの範囲外**。本層は
      両辺の体積を実 deg_ℝ で**構成**し、crux を **明示的仮説** `GaussPilotCruxHyp`
      として受け取る**条件付き定理**を本物にするのみで、**crux 自体を証明しない**。
      `gPilot_crux_is_hypothesis`（Iff.rfl）が「crux はちょうどこの仮説であって
      定理ではない」ことを機械検証で明示する。なお本層の実 deg_ℝ 上の crux は
      **次数レベルの影**であり、原論文の crux（点毎輸送 `ThetaLinkTransport`）は
      M249F `transport_strictly_stronger` の示す通り**次数 transport より真に
      強い**（`gPilot_gap_nonempty` で再確認）——真の crux はさらに範囲外。
    ・log q_v（重み `logq : Nat → RReal`）は M312F/M319F と同じく**実重み
      witness**（係数扱い）。RHS の重み構造 w(k)·k²（M135F `wssq`）を実 deg_ℝ
      文脈で再利用したもので、log q_v の超越性・具体値・重み w の実対数化は
      本層の範囲外（柱A/柱C の後続で本物化）。
    ・定理3.11 ⟹ 系3.12 の還元は既存 M5/M97/M249F のまま（`gPilot_to_cor312` は
      M249F `transportDeg_iff_cor312` の再輸出・骨組み接続）。本層は体積 RHS の
      実 deg_ℝ 化と両辺実対象の条件付き定理に限る。
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ総体積の閉形式・加法性は
      realEq で言明する（M312F/M319F と同じ正直な形）。
  全て新規 Classical.choice を証明本体に導入せず（M312F/M319F/M135F/M249F から
  継承、#print axioms は propext/Quot.sound 系のみ）。sorry 皆無・禁止タクティク
  不使用（core Lean のみ）。サブエージェント新規1本（共有ファイル未変更）。
  一般名は `gPilot` 接頭辞で衝突回避。
-/
import IUT.ThetaPilotRealVolume
import IUT.TransportMirror

namespace IUT

/-! ## M324F-1: 単一ガウス因子項の実 deg_ℝ -/

/-- **M324F-1a: ガウス因子第 k 項の実 Arakelov 局所次数** —
    deg_ℝ(w(k)·k²) = w(k)·k²·log q_v。M135F `wssq`（Σ_{k≤l} w(k)·k²）の各項
    w(k)·k² を M312F の局所 log-volume `logVolLocal`（n·log q_v）に投入する。
    従来 m202fVol の id 体積ではなく **本物の実数値 Arakelov 次数**。 -/
def gPilotValueDeg (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (k : Nat) : RReal :=
  logVolLocal logq v ((w k * (k * k) : Nat) : Int)

/-- **定理 (M324F-1b): ガウス項の実 deg_ℝ の係数抽出** —
    gPilotValueDeg logq v w k = w(k)·k²·log q_v = rmul(intToReal(w k·(k·k)))(log q_v)。 -/
theorem gPilotValueDeg_eq (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (k : Nat) :
    gPilotValueDeg logq v w k
      = rmul (intToReal ((w k * (k * k) : Nat) : Int)) (logq v) :=
  rfl

/-! ## M324F-2: ガウスパイロット総体積 Σ w(k)·k² と wssq 閉形式 -/

/-- **M324F-2a: ガウスパイロット総体積** — Σ_{k=0}^{m-1} deg_ℝ(w(k)·k²)
    = Σ_{k<m} w(k)·k²·log q_v。定理3.11 のガウスパイロット体積（RHS）を
    **実数値 deg_ℝ** で束ねたもの（M135F `wssq` の実 deg_ℝ 版・m=l+1 で
    Σ_{k=0}^{l}）。 -/
def gPilotTotalVol (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) : Nat → RReal
  | 0 => realZero
  | m + 1 => realAdd (gPilotTotalVol logq v w m) (gPilotValueDeg logq v w m)

/-- **定理 (M324F-2b): 総体積の Σ w(k)·k² 閉形式** — ガウスパイロット総体積は
    Σ_{k<m} w(k)·k² の重み付き実 deg_ℝ に一致する（realEq、ℝ は setoid）:
    gPilotTotalVol logq v w m ≈ logVolLocal logq v (Σ_{k<m} w(k)·k²)。M135F
    `wssq`（nsum）の各項の deg_ℝ を M312F `logVolLocal_add` で束ねる。ガウス
    パイロット体積の **本物の閉形式**。 -/
theorem gPilot_total_closed (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    ∀ m, realEq (gPilotTotalVol logq v w m)
      (logVolLocal logq v ((nsum (fun k => w k * (k * k)) m : Nat) : Int)) := by
  intro m
  induction m with
  | zero =>
    show realEq realZero (logVolLocal logq v 0)
    exact realEq_symm (logVolLocal_zero logq v)
  | succ m ih =>
    show realEq (realAdd (gPilotTotalVol logq v w m)
          (logVolLocal logq v ((w m * (m * m) : Nat) : Int)))
        (logVolLocal logq v ((nsum (fun k => w k * (k * k)) (m + 1) : Nat) : Int))
    have hcoeff : ((nsum (fun k => w k * (k * k)) (m + 1) : Nat) : Int)
        = ((nsum (fun k => w k * (k * k)) m : Nat) : Int)
          + ((w m * (m * m) : Nat) : Int) := by
      have hs : nsum (fun k => w k * (k * k)) (m + 1)
          = nsum (fun k => w k * (k * k)) m + w m * (m * m) := rfl
      rw [hs, Int.natCast_add]
    rw [hcoeff]
    refine realEq_trans (realAdd_congr_left
      (logVolLocal logq v ((w m * (m * m) : Nat) : Int)) ih) ?_
    exact realEq_symm (logVolLocal_add logq v
      ((nsum (fun k => w k * (k * k)) m : Nat) : Int)
      ((w m * (m * m) : Nat) : Int))

/-- **定理 (M324F-2c): 総体積 = wssq の実 deg_ℝ** — l+1 項の総体積が、ちょうど
    M135F `wssq w l`（Σ_{k≤l} w(k)·k²、= nsum … (l+1)）の実 deg_ℝ に一致する
    （realEq）。ガウスパイロット RHS の実 deg_ℝ 閉形式の確定形。 -/
theorem gPilot_total_wssq (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    realEq (gPilotTotalVol logq v w (l + 1))
      (logVolLocal logq v ((wssq w l : Nat) : Int)) :=
  gPilot_total_closed logq v w (l + 1)

/-! ## M324F-3: crux 不等式の実対象ステートメントと仮説 -/

/-- **M324F-3a: crux 不等式の実対象ステートメント（両辺実 deg_ℝ・閉形式版）** —
    定理3.11 の体積不等式「テータパイロット ≤ ガウスパイロット」を、**両辺の
    実 deg_ℝ 閉形式**で述べたもの: deg_ℝ(Σ_{j=1}^{l} j²) ≤ deg_ℝ(Σ_{k≤l} w(k)·k²)
    （= logVolLocal logq v (sumSq l) ≤ logVolLocal logq v (wssq w l)）。M319F LHS
    の Σj² 閉形式と本層 RHS の Σ w(k)·k² 閉形式を突き合わせた実対象の言明。 -/
def gPilot_crux_statement (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    Prop :=
  rLe (logVolLocal logq v ((sumSq l : Nat) : Int))
    (logVolLocal logq v ((wssq w l : Nat) : Int))

/-- **M324F-3b: crux 仮説（明示的 hypothesis）** — テータパイロット総体積
    （M319F `thPilotTotalVol`, LHS）≤ ガウスパイロット総体積（本層
    `gPilotTotalVol`, RHS）を、**構成した実体積の上で**述べた crux 命題。
    これは定理3.11 の体積不等式（＝Dβ-ω＝多輻的アルゴリズム＝IUT 論争の
    係争点）であり、その証明は本タスクの**恒久的な範囲外**——本層は crux を
    仮説として受け取るのみ（`gPilot_crux_is_hypothesis` 参照）。 -/
def GaussPilotCruxHyp (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) :
    Prop :=
  rLe (thPilotTotalVol logq v l) (gPilotTotalVol logq v w (l + 1))

/-! ## M324F-4: 条件付き定理（crux 仮説の下で両辺実対象の定理3.11 体積不等式） -/

/-- **定理 (M324F-4a): crux 仮説下の条件付き定理3.11（本物・crux は仮説）** —
    crux 仮説 `GaussPilotCruxHyp`（構成した実体積 thPilotTotalVol ≤
    gPilotTotalVol）の下で、閉形式版の定理3.11 体積不等式
    `gPilot_crux_statement`（両辺実 deg_ℝ: deg_ℝ(Σj²) ≤ deg_ℝ(Σ w(k)·k²)）が
    従う。**還元は本物**: M319F `thPilot_total_closed`（LHS 閉形式）と本層
    `gPilot_total_wssq`（RHS 閉形式）を `rLe_congr` で張り替えるだけ。
    **crux 自体（仮説の中身）は証明しない**——両辺の体積を実対象で構成し、
    crux を仮説として受けた条件付き定理を本物で閉じるのが本層の成果。 -/
theorem gPilot_theorem311_conditional (logq : Nat → RReal) (v : Nat)
    (w : Nat → Nat) (l : Nat) (crux : GaussPilotCruxHyp logq v w l) :
    gPilot_crux_statement logq v w l := by
  show rLe (logVolLocal logq v ((sumSq l : Nat) : Int))
    (logVolLocal logq v ((wssq w l : Nat) : Int))
  exact rLe_congr (thPilot_total_closed logq v l)
    (gPilot_total_wssq logq v w l) crux

/-- **定理 (M324F-4b): crux が仮説であることの明示** — `GaussPilotCruxHyp` は
    定義上ちょうど実 deg_ℝ 不等式「thPilotTotalVol ≤ gPilotTotalVol」であり、
    **それ以上でも以下でもない**（Iff.rfl）。本層は crux をこの仮説として
    受け取るのみで、**証明はしない**（過大主張の厳禁の機械検証的明示）。 -/
theorem gPilot_crux_is_hypothesis (logq : Nat → RReal) (v : Nat)
    (w : Nat → Nat) (l : Nat) :
    GaussPilotCruxHyp logq v w l
      ↔ rLe (thPilotTotalVol logq v l) (gPilotTotalVol logq v w (l + 1)) :=
  Iff.rfl

/-! ## M324F-5: l³ 下界と RHS の対比・両辺の隔たり -/

/-- **定理 (M324F-5a): LHS↔RHS 係数対比の実 deg_ℝ 版** — Nat 側の重み比較
    sumSq l ≤ wssq w l（例えば w ≥ 1 なら M135F `wssq_lower` から）を、実
    deg_ℝ の順序 rLe へ持ち上げる: deg_ℝ(sumSq l) ≤ deg_ℝ(wssq w l)（非負
    重み log q_v ≥ 0 の下で）。M312F `intToReal_mono`（順序埋め込み）＋ M180
    `rmul_le_mul_right`（右非負での単調性）。crux 不等式の閉形式版が、係数の
    大小からは（重み比較を仮定すれば）実対象で従う骨組み。 -/
theorem gPilot_bound_compare (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (l : Nat) (hq : rLe realZero (logq v)) (hcmp : sumSq l ≤ wssq w l) :
    rLe (logVolLocal logq v ((sumSq l : Nat) : Int))
      (logVolLocal logq v ((wssq w l : Nat) : Int)) := by
  show rLe (rmul (intToReal ((sumSq l : Nat) : Int)) (logq v))
    (rmul (intToReal ((wssq w l : Nat) : Int)) (logq v))
  have hint : ((sumSq l : Nat) : Int) ≤ ((wssq w l : Nat) : Int) := by omega
  exact rmul_le_mul_right (intToReal_mono hint) hq

/-- **定理 (M324F-5b): 両辺の隔たりは実在する（Dβ-ω が空でない）** — M249F
    `transport_strictly_stronger` の再輸出: 点毎輸送 `ThetaLinkTransport`
    （原論文の crux）は次数輸送 `ThetaLinkTransportDeg`（本層の実 deg_ℝ 上の
    crux の次数レベルの影）より**真に強い**具体 witness が存在する。すなわち
    LHS↔RHS の隔たり（crux＝Dβ-ω）は骨格からは決定されず**空でない**——crux を
    仮説として孤立させる意味の機械検証。 -/
theorem gPilot_gap_nonempty :
    ∃ (w : Nat → Nat) (n l B k₀ : Nat) (hw0 : w k₀ = 0),
      ThetaLinkTransportDeg w n l k₀ hw0
        ∧ ¬ ThetaLinkTransport w n l B k₀ hw0 :=
  transport_strictly_stronger

/-! ## M324F-6: crux 仮説から系3.12 への還元（既存 M249F 接続） -/

/-- **定理 (M324F-6): 次数レベル crux から系3.12 への還元（M249F 再利用）** —
    M249F 鏡像定理 `transportDeg_iff_cor312`（次数 transport ⟺ Cor312）を通して、
    次数レベルの crux（`ThetaLinkTransportDeg`）から系3.12 の結論形（Cor312、
    Szpiro/ABC 帰結の骨格）へ降ろす骨組み接続。本層の実 deg_ℝ 上の crux 仮説
    `GaussPilotCruxHyp` はこの次数レベル crux の実対象への refine であり、両者を
    厳密に橋渡しするのは（真の crux と同じく）範囲外——ここでは既存の還元路を
    再輸出する。 -/
theorem gPilot_to_cor312 (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0)
    (h : ThetaLinkTransportDeg w n l k₀ hw0) :
    Cor312 (arithSkeleton w n l B hl hB) :=
  (transportDeg_iff_cor312 w n l B k₀ hl hB hw0).mp h

/-! ## M324F-7: capstone -/

/-- **M324F-7a: ガウスパイロット実体積データ** — 定理3.11 の両辺を **実
    Arakelov 次数 deg_ℝ** で束ねる: LHS（テータパイロット総体積・M319F）、
    RHS（ガウスパイロット総体積・本層）、それぞれの閉形式（Σj²・Σ w(k)·k²）、
    および **crux 仮説の下で両辺実対象の定理3.11 体積不等式が従う条件付き
    定理**。主語は M312F の本物の実数値 log-volume であり、toy m202fVol を
    用いない。crux（conditional_311 の前件）は仮説であって証明しない。 -/
structure GaussPilotVolumeData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) where
  /-- テータパイロット総体積（LHS・M319F の実 deg_ℝ）。 -/
  lhsVol : Nat → RReal
  /-- ガウスパイロット総体積（RHS・本層の実 deg_ℝ）。 -/
  rhsVol : Nat → RReal
  /-- LHS の Σj² 閉形式: lhsVol n ≈ deg_ℝ(sumSq n)。 -/
  lhs_closed : ∀ n : Nat,
    realEq (lhsVol n) (logVolLocal logq v ((sumSq n : Nat) : Int))
  /-- RHS の Σ w(k)·k² 閉形式: rhsVol (l+1) ≈ deg_ℝ(wssq w l)。 -/
  rhs_closed : ∀ l : Nat,
    realEq (rhsVol (l + 1)) (logVolLocal logq v ((wssq w l : Nat) : Int))
  /-- **条件付き定理3.11**: crux 仮説（lhsVol l ≤ rhsVol (l+1)、両辺実対象）の
      下で、閉形式版の体積不等式 deg_ℝ(sumSq l) ≤ deg_ℝ(wssq w l) が従う。
      crux（前件）は仮説であって証明されない。 -/
  conditional_311 : ∀ l : Nat,
    rLe (lhsVol l) (rhsVol (l + 1)) →
      rLe (logVolLocal logq v ((sumSq l : Nat) : Int))
        (logVolLocal logq v ((wssq w l : Nat) : Int))

/-- **M324F-7b: 実データ** — 全フィールドを M324F-2〜4 の本物で充足。LHS は
    M319F `thPilotTotalVol`、RHS は本層 `gPilotTotalVol`、閉形式と条件付き定理を
    実対象で埋める。 -/
def gaussPilotVolumeData (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    GaussPilotVolumeData logq v w where
  lhsVol := thPilotTotalVol logq v
  rhsVol := gPilotTotalVol logq v w
  lhs_closed := thPilot_total_closed logq v
  rhs_closed := fun l => gPilot_total_wssq logq v w l
  conditional_311 := fun l crux => gPilot_theorem311_conditional logq v w l crux

/-- **M324F-7c: 存在（M324F 見出し）** — 任意の実重み logq・素点 v・重み列 w に
    対し、定理3.11 の両辺（LHS・RHS）を実 Arakelov 次数 deg_ℝ で束ね、crux 仮説
    下の条件付き体積不等式を備えたデータが存在する。従来 m202fVol toy だった
    RHS の体積主語が **本物の実数値 log-volume** へ昇格される。 -/
theorem gPilot_exists (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) :
    Nonempty (GaussPilotVolumeData logq v w) :=
  ⟨gaussPilotVolumeData logq v w⟩

/-- **M324F-7d: 条件付き定理3.11**（capstone 再掲）— crux 仮説の下で両辺実対象の
    定理3.11 体積不等式。 -/
theorem gPilot_conditional_theorem311 (logq : Nat → RReal) (v : Nat)
    (w : Nat → Nat) (l : Nat) (crux : GaussPilotCruxHyp logq v w l) :
    rLe (logVolLocal logq v ((sumSq l : Nat) : Int))
      (logVolLocal logq v ((wssq w l : Nat) : Int)) :=
  gPilot_theorem311_conditional logq v w l crux

/-! ## 実例（l=5: Σ_{j=1}^{5} j²=55, Σ_{k=0}^{5} 1·k²=55） -/

/-- 実例: テータパイロット LHS の平方和 Σ_{j=1}^{5} j² = 55。 -/
example : sumSq 5 = 55 := rfl

/-- 実例: 単位重み w≡1 のガウスパイロット RHS の重み付き平方和
    Σ_{k=0}^{5} 1·k² = 55（l=5, LHS と一致＝crux 不等式が等号で退化する正規化点）。 -/
example : wssq (fun _ => 1) 5 = 55 := rfl

/-- 実例: l=5（単位重み）のガウスパイロット総体積 ≈ logVolLocal v (wssq 5)。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (gPilotTotalVol logq v (fun _ => 1) 6)
      (logVolLocal logq v ((wssq (fun _ => 1) 5 : Nat) : Int)) :=
  gPilot_total_wssq logq v (fun _ => 1) 5

/-- 実例: l=5 の crux 仮説の下で、両辺実 deg_ℝ の定理3.11 体積不等式
    deg_ℝ(Σj²=55) ≤ deg_ℝ(Σ w(k)·k²) が従う（条件付き定理）。 -/
example (logq : Nat → RReal) (v : Nat) (w : Nat → Nat)
    (crux : GaussPilotCruxHyp logq v w 5) :
    rLe (logVolLocal logq v ((sumSq 5 : Nat) : Int))
      (logVolLocal logq v ((wssq w 5 : Nat) : Int)) :=
  gPilot_theorem311_conditional logq v w 5 crux

end IUT
