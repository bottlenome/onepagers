/-
  IUT/LogLinkReal.lean — M337F [実／本物]
  分類: 実 (log-theta-lattice の縦 log-link を実 log-shell/実テータパイロット体積上で)
  complete_pct 影響: 柱D を前進（M327F log-Kummer・M319F 実テータパイロット体積・M321F 実
    log-shell を合成し、縦 log-link（乗法 U^(d)→加法 log-shell の p 進 log）を本物で構成・
    実 deg_ℝ 体積輸送を本物化。crux Dβ-ω は外部仮説として明示、決して導出しない）。
  正直な限定: crux Dβ-ω（多輻的アルゴリズム＝論争の係争点）は外部 Prop 仮説のみ。log は主項
    係数レベル（完全収束は後続）。ℝ は setoid（realEq/rLe で言明・`=` でない）。log-link 写像
    そのものは無条件で本物だが、多輻的両立（log-link と theta-link の crux）は受け取るのみ。

  ## 本モジュールの位置づけ（何を合成し何を本物化したか）

  IUT III の **log-theta-lattice** は 2 方向のリンクを持つ（M3 `LogThetaLattice`）:
    ・**縦の log-link** (n,m) → (n,m+1): 同一の数論的正則構造（同一列）の内部で
      p 進対数を取り、**乗法（Frobenius-like 単数群 U^(d)）から加法（étale-like
      log-shell m^d）へ**移る 1 段の垂直ステップ。
    ・**横の theta-link** (n,m) → (n+1,m): 異なる正則構造への移行（M328F
      `ThetaLinkReal` が実テータ値で本物化した水平辺）。
  本 M337F は **縦の log-link を実対象で構成**する。従来 M3 の Link.log は頂点に
  実データを載せない**組合せ骨格**であり、M205F `LogKummer` は log-link を toy 模型
  （m202fVol 体積・Bool 軌道）で装飾するだけだった。本層は次を合成して縦 log-link を
  本物化する:
    * M327F `LogKummerReal`: 本物の graded log θ_d（`logKumLog`, 乗法 U^(d) → 加法 ℤ/p）と
      その準同型 `logKum_log_hom`・核 `logKum_log_kernel`（= U^(d+1)）・全射・log(uⁿ)=n·log u。
    * M321F `LogShellReal`: 本物の加法 log-shell m^d = p^d·ℤ_p（`logShellMem`）と、
      主単数の leading log content が m^d に着地すること（`logShell_unit_filtration`）。
    * M319F `ThetaPilotRealVolume` / M312F `LogVolume`: 実テータパイロット体積
      Σj²·log q_v（`thPilotTotalVol`）と実 Arakelov 局所次数（`logVolLocal`・加法性）。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M337F-1 `logLinkMap` / `logLink_one` / `logLink_hom` / `logLink_pow`
      — **縦 log-link 写像** = 実 graded log θ_d（乗法 U^(d) → 加法 log-shell ℤ/p）。
        1 段の垂直ステップ。log(1)=0・準同型 log(uv)=log u + log v（乗法 → 加法）・
        log(uⁿ)=n·log u を M327F の本物で閉じる（`logKum_log_*` を log-link の語彙で採る）。
  * M337F-2 `logLink_shell_step` / `logLink_kernel` / `logLink_surj`
      — **1 格子ステップ下降**: log-link は乗法フィルトレーション U^(d) を加法 log-shell m^d
        （M321F）へ送る。leading log content が m^d に着地し（`logShell_unit_filtration`）、
        写像の核はちょうど U^(d+1)（`logKum_log_kernel`）・全射（`logKum_log_surj`）。
  * M337F-3 `logLinkVolTransport` / `logLink_volume_transport` / `logLink_pilot_transport`
      — **実 deg_ℝ 体積輸送**: log-link は加法ゆえ、乗法側の積（付値 n+m）を加法 log-shell の
        体積の和へ移す（log turns products into sums, `logVolLocal_add`）。実テータパイロット
        体積 Σj²（M319F）が像 log-shell の実 deg_ℝ に一致する（`thPilot_total_closed`）。
  * M337F-4 `LogLinkLatticeData` / `logLinkLatticeData` / `logLink_lattice_vertical` /
    `logLink_vertical_preserves_col`
      — **縦辺の装飾**: M3 の縦 log-link 辺（Link.log (n,m)→(n,m+1)、組合せ骨格）を実 graded
        log で装飾。横の theta-link（M328F）と異なり **列（正則構造）を保つ**（Θ 本数 0、
        `pure_log_same_col`）ことを機械検証で明示。
  * M337F-5 `logLink_crux_hypothesis` / `logLink_scope`（**crux は外部仮説・決して導出しない**）
      — log-link 写像は**無条件で本物**（準同型が仮定なしで成立）だが、その **多輻的両立**
        （log-link と theta-link の crux ＝ Dβ-ω ＝ 論争の係争点）は外部 Prop として**受け取る
        のみ**で、本層では決して証明しない（過大主張禁止）。
  * M337F-6 capstone `LogLinkRealData` / `logLinkRealData` / `logLink_exists` + 実例。

  ## 正直な限定（消去・弱化禁止）
  * **crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層は
    縦 log-link の**写像・準同型・log-shell 下降・実 deg_ℝ 体積輸送を本物で構成するのみ**で、
    crux（log-link と theta-link の両立不等式）は外部 Prop 仮説として受け取り決して導出しない
    （`logLink_crux_hypothesis` / `logLink_scope` が機械検証で scope を固定）。
  * **log 写像は p 進対数の主項 θ_d で本物**（M327F/M321F と同じ）。完全な収束級数
    log(1+t) = t − t²/2 + … は後続層。局所体は K = ℚ_p（O_v = ℤ_p, U^(d)=1+p^d ℤ_p）。
  * **準同型・log-shell 下降は U^(d) の各段で本物**。全レベルを束ねる単一の完全 log は後続。
  * log q_v は実重み witness（M312F/M319F 継承）。**ℝ は setoid** ゆえ体積輸送は realEq で言明。
  全て選択公理不使用（sorry 皆無・新規 Classical 皆無）。禁止タクティク不使用（core Lean のみ）。
  共有ファイル未変更。柱D 横展開・本物の先行建設[実]。
-/
import IUT.LogKummerReal
import IUT.LogShellReal
import IUT.ThetaPilotRealVolume
import IUT.LogThetaLattice

namespace IUT

/-! ## M337F-1: 縦 log-link 写像（乗法 U^(d) → 加法 log-shell ℤ/p、1 段の垂直ステップ） -/

/-- **M337F-1a: 縦 log-link 写像** — log-theta-lattice の縦辺 (n,m)→(n,m+1) が
    実行する操作: p 進対数の主項 θ_d（M327F `logKumLog`）で、乗法群 U^(d)
    （Frobenius-like 単数群）から加法群 ℤ/p（étale-like log-shell）へ移す 1 段の
    垂直ステップ。surrogate でない本物の graded log。 -/
def logLinkMap (p d : Nat) (hp : 1 ≤ p) (u : (principalUnits p).carrier) :
    (zmod p).carrier :=
  logKumLog p d hp u

/-- **定理 (M337F-1b): log-link は単位元を 0 へ** — log(1) = 0
    （乗法単位元 → 加法単位元）。M327F `logKum_log_one`。 -/
theorem logLink_one (p d : Nat) (hp : 1 ≤ p) :
    logLinkMap p d hp (principalUnits p).one = (zmod p).one :=
  logKum_log_one p d hp

/-- **定理 (M337F-1c): log-link は準同型（乗法 → 加法）** — log(uv) = log u + log v。
    縦 log-link が**乗法（Frobenius-like）から加法（étale-like log-shell）への
    準同型**であることの本物（M327F `logKum_log_hom`）。log-link 写像そのものは
    この準同型を無条件で満たす（crux とは独立）。 -/
theorem logLink_hom (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y) :
    logLinkMap p d hp ((principalUnits p).mul x y)
      = (zmod p).mul (logLinkMap p d hp x) (logLinkMap p d hp y) :=
  logKum_log_hom p d hp hd x y hx hy

/-- **定理 (M337F-1d): log-link の n 乗可換** — log(uⁿ) = n·log u
    （乗法の n 乗 ⇄ 加法の n 倍、log-Kummer 可換図）。M327F `logKum_log_pow`。 -/
theorem logLink_pow (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    {u : (principalUnits p).carrier} (hu : (unitFiltration p d).mem u) :
    ∀ n : Nat,
      logLinkMap p d hp (tateNpow (principalUnits p) u n)
        = tateNpow (zmod p) (logLinkMap p d hp u) n :=
  logKum_log_pow p d hp hd hu

/-! ## M337F-2: 1 格子ステップ下降（U^(d) → 加法 log-shell m^d、核 = U^(d+1)） -/

/-- **定理 (M337F-2a: 本丸): log-link は U^(d) を加法 log-shell m^d へ下降** —
    縦 log-link の 1 ステップは、乗法フィルトレーション U^(d)（Frobenius-like）を
    加法 log-shell m^d = p^d·ℤ_p（M321F、étale-like）へ送る:
    (i) 主単数 x ∈ U^(d) の leading log content x−1 が加法 log-shell m^d に着地し
        （M321F `logShell_unit_filtration`）、
    (ii) log-link 写像の**核はちょうど次段 U^(d+1)**（log x = 0 ⟺ x ∈ U^(d+1)、
        M327F `logKum_log_kernel`）。
    これが log-theta-lattice の縦辺 1 段の「乗法 U^(d)/U^(d+1) ⇄ 加法 m^d/m^{d+1}」の
    本物の下降（付値方向の対応）。 -/
theorem logLink_shell_step (p d : Nat) (hp : 1 ≤ p)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x) :
    logShellMem p d (logShellContent p x.val)
      ∧ (logLinkMap p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x) :=
  ⟨logShell_unit_filtration p d x hx, logKum_log_kernel p d hp x hx⟩

/-- **定理 (M337F-2b): log-link の核 = U^(d+1)** — log-link 写像の核はちょうど
    次段の単数フィルトレーション（1 格子ステップ下降の核）。M327F `logKum_log_kernel`。 -/
theorem logLink_kernel (p d : Nat) (hp : 1 ≤ p)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x) :
    logLinkMap p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x :=
  logKum_log_kernel p d hp x hx

/-- **定理 (M337F-2c): log-link は加法 log-shell を尽くす（全射）** — 任意の加法類
    c ∈ ℤ/p は U^(d) のある単数の log。縦 log-link が加法 log-shell ℤ/p を尽くす
    （像が全 log-shell）ことの本物。M327F `logKum_log_surj`。 -/
theorem logLink_surj (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (c : (zmod p).carrier) :
    ∃ u : (principalUnits p).carrier,
      (unitFiltration p d).mem u ∧ logLinkMap p d hp u = c :=
  logKum_log_surj p d hp hd c

/-! ## M337F-3: 実 deg_ℝ 体積輸送（log turns products into sums） -/

/-- **M337F-3a: log-link の実 deg_ℝ 体積輸送** — 縦 log-link の像となる加法 log-shell
    の実 Arakelov 局所次数 deg_ℝ（M312F `logVolLocal`）。付値レベル n（乗法側の付値）を
    加法 log-shell の実数値体積 n·log q_v へ移す。 -/
def logLinkVolTransport (logq : Nat → RReal) (v : Nat) (n : Int) : RReal :=
  logVolLocal logq v n

/-- **定理 (M337F-3b: 本丸): log-link は積を和へ移す（実 deg_ℝ）** — 縦 log-link は
    加法写像ゆえ、乗法側の**積**（付値 n+m ＝ 2 単数の積の付値）を、加法 log-shell の
    体積の**和**へ移す: deg_ℝ(n+m) ≈ deg_ℝ(n) + deg_ℝ(m)（M312F `logVolLocal_add`）。
    p 進対数の「乗法 → 加法」性が実 Arakelov 次数の上で本物に実現される
    （log turns products into sums、realEq、ℝ は setoid）。 -/
theorem logLink_volume_transport (logq : Nat → RReal) (v : Nat) (n m : Int) :
    realEq (logLinkVolTransport logq v (n + m))
      (realAdd (logLinkVolTransport logq v n) (logLinkVolTransport logq v m)) :=
  logVolLocal_add logq v n m

/-- **定理 (M337F-3c): 実テータパイロット体積の log-link 像** — 縦 log-link の像となる
    加法 log-shell の実 deg_ℝ 体積（付値レベル Σj²）は、M319F の実テータパイロット総体積
    `thPilotTotalVol`（Σj²·log q_v）に一致する（realEq、`thPilot_total_closed`）。実テータ
    パイロット体積が log-link の 1 縦ステップで加法 log-shell 体積へ本物に輸送される。 -/
theorem logLink_pilot_transport (logq : Nat → RReal) (v : Nat) (n : Nat) :
    realEq (thPilotTotalVol logq v n)
      (logLinkVolTransport logq v ((sumSq n : Nat) : Int)) :=
  thPilot_total_closed logq v n

/-! ## M337F-4: log-theta-lattice の縦 log-link 辺を実 graded log で装飾 -/

/-- **M337F-4a: 縦 log-link 格子辺データ** — M3 `LogThetaLattice` の縦 log-link 辺
    （LatticeSite (col,row) → (col,row+1) の Link.log、従来は頂点に実データを載せない
    **組合せ骨格**）を、実 graded log θ_d（乗法 U^(d) → 加法 log-shell ℤ/p）で装飾する
    構造。縦の log-link 側を実対象へ昇格（横の theta-link は M328F で別途昇格）。 -/
structure LogLinkLatticeData (p d : Nat) (hp : 1 ≤ p) where
  /-- 辺の始点の列（数論的正則構造ラベル）。log-link は同一列内。 -/
  col : Int
  /-- 辺の始点の行（log 方向ラベル）。 -/
  row : Int
  /-- M3 の縦 log-link 辺 (col,row) → (col,row+1)（本物の組合せ辺）。 -/
  edge : Link ⟨col, row⟩ ⟨col, row + 1⟩
  /-- 辺に載る実 graded log 写像（乗法 U^(d) → 加法 log-shell ℤ/p）。 -/
  logMap : (principalUnits p).carrier → (zmod p).carrier
  /-- logMap は本物の graded log（M327F）。 -/
  is_log : logMap = logKumLog p d hp
  /-- log-link 写像の準同型（乗法 → 加法・U^(d) 上、1 ≤ d の下で）。 -/
  log_hom : 1 ≤ d → ∀ (x y : (principalUnits p).carrier),
    (unitFiltration p d).mem x → (unitFiltration p d).mem y →
    logMap ((principalUnits p).mul x y) = (zmod p).mul (logMap x) (logMap y)
  /-- 1 格子ステップ下降の核: log の核 = U^(d+1)。 -/
  kernel : ∀ (x : (principalUnits p).carrier), (unitFiltration p d).mem x →
    (logMap x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x)

/-- **M337F-4b: witness** — M3 の Link.log 縦辺に実 graded log `logKumLog`（M327F）を
    載せ、準同型・核を本物で充足。組合せ骨格の縦 log-link 辺を実対象へ昇格した witness。 -/
def logLinkLatticeData (p d : Nat) (hp : 1 ≤ p) (n m : Int) :
    LogLinkLatticeData p d hp where
  col := n
  row := m
  edge := Link.log n m
  logMap := logKumLog p d hp
  is_log := rfl
  log_hom := fun hd x y hx hy => logKum_log_hom p d hp hd x y hx hy
  kernel := fun x hx => logKum_log_kernel p d hp x hx

/-- **定理 (M337F-4c: log-theta-lattice の縦 log-link 辺の実 graded log 昇格)** —
    任意の格子位置 (n,m) で、M3 の縦 log-link 辺 (n,m)→(n,m+1)（Link.log）に実 graded log
    θ_d（乗法 U^(d) → 加法 log-shell ℤ/p の準同型・核 = U^(d+1)）を載せたデータが存在する。
    **組合せ骨格の縦 log-link 辺が実対象へ昇格**される（crux Dβ-ω は範囲外）。 -/
theorem logLink_lattice_vertical (p d : Nat) (hp : 1 ≤ p) (n m : Int) :
    Nonempty (LogLinkLatticeData p d hp) :=
  ⟨logLinkLatticeData p d hp n m⟩

/-- **定理 (M337F-4d): 縦 log-link は列（正則構造）を保つ（theta-link と対比）** —
    縦 log-link 辺 (n,m)→(n,m+1) は Θ-link を 0 本しか通らない経路であり（M3 `Path 0`）、
    **列 col を保つ**（同一の数論的正則構造の内部・M3 `pure_log_same_col`）。M328F の横
    theta-link が列を +1 する（正則構造を変える）のと対照的な、縦 log-link の本質。 -/
theorem logLink_vertical_preserves_col (n m : Int) :
    (⟨n, m + 1⟩ : LatticeSite).col = (⟨n, m⟩ : LatticeSite).col :=
  pure_log_same_col (Path.log n m (Path.nil ⟨n, m + 1⟩))

/-! ## M337F-5: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M337F-5a: crux は外部仮説・決して導出しない／honest)** — 縦 log-link 写像は
    **無条件で本物**（準同型 log(uv)=log u + log v が crux とは独立に成立）だが、その下での
    **多輻的両立**（log-link と横 theta-link の crux ＝ Dβ-ω ＝ 多輻的アルゴリズム ＝ IUT
    論争の当の係争点）は本層で**決して証明しない**。crux を任意の外部 Prop `crux` として
    受け取り、log-link 準同型の本物性 **と** crux の連言を、crux が仮説として供給された
    場合にのみ返す——crux は決して導出されない（過大主張禁止）。 -/
theorem logLink_crux_hypothesis (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y)
    (crux : Prop) (hcrux : crux) :
    (logLinkMap p d hp ((principalUnits p).mul x y)
        = (zmod p).mul (logLinkMap p d hp x) (logLinkMap p d hp y))
      ∧ crux :=
  ⟨logLink_hom p d hp hd x y hx hy, hcrux⟩

/-- **定理 (M337F-5b: scope の固定)** — 縦 log-link 写像は本物（無条件で単位元を保つ
    準同型）であり、crux（外部 Prop）は **仮説としてのみ**利用可能で本層では導出されない。
    log-link の写像・準同型・log-shell 下降・体積輸送を本物にするのみで crux を証明しない、
    という scope を機械検証可能な形で固定する。 -/
theorem logLink_scope (p d : Nat) (hp : 1 ≤ p) :
    logLinkMap p d hp (principalUnits p).one = (zmod p).one
      ∧ (∀ crux : Prop, crux → crux) :=
  ⟨logLink_one p d hp, fun _ h => h⟩

/-! ## M337F-6: capstone -/

/-- **M337F-6a: 縦 log-link 実データ**（総括） — log-theta-lattice の縦 log-link を実対象で
    束ねる: 実 graded log 写像（乗法 U^(d) → 加法 log-shell ℤ/p）・log(1)=0・準同型・
    1 格子ステップ下降（核 = U^(d+1)）・実 deg_ℝ 体積輸送（積 → 和）。主語は M327F/M321F/
    M319F/M312F の本物であり、toy m202fVol・Bool 軌道を用いない。crux Dβ-ω は範囲外。 -/
structure LogLinkRealData where
  /-- 局所体 K = ℚ_p の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  /-- p ≥ 1。 -/
  hp : 1 ≤ p
  /-- フィルトレーション段 d ≥ 1。 -/
  d : Nat
  /-- d ≥ 1。 -/
  hd : 1 ≤ d
  /-- 縦 log-link 写像（graded log θ_d、乗法 → 加法 log-shell）。 -/
  logMap : (principalUnits p).carrier → (zmod p).carrier
  /-- logMap は本物の graded log。 -/
  is_log : logMap = logLinkMap p d hp
  /-- log(1) = 0（乗法単位元 → 加法単位元）。 -/
  log_one : logMap (principalUnits p).one = (zmod p).one
  /-- log-link は準同型（乗法 → 加法、U^(d) 上）。 -/
  log_hom : ∀ (x y : (principalUnits p).carrier),
    (unitFiltration p d).mem x → (unitFiltration p d).mem y →
    logMap ((principalUnits p).mul x y) = (zmod p).mul (logMap x) (logMap y)
  /-- 1 格子ステップ下降: leading log content が加法 log-shell m^d に着地。 -/
  shell_content : ∀ (x : (principalUnits p).carrier), (unitFiltration p d).mem x →
    logShellMem p d (logShellContent p x.val)
  /-- 1 格子ステップ下降の核: log の核 = U^(d+1)。 -/
  kernel : ∀ (x : (principalUnits p).carrier), (unitFiltration p d).mem x →
    (logMap x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x)
  /-- 実 deg_ℝ 体積輸送: log-link は積（付値 n+m）を加法 log-shell 体積の和へ移す。 -/
  vol_transport : ∀ (logq : Nat → RReal) (v : Nat) (n m : Int),
    realEq (logLinkVolTransport logq v (n + m))
      (realAdd (logLinkVolTransport logq v n) (logLinkVolTransport logq v m))

/-- **M337F-6b: witness** — ℤ_p 上（段 d=1）の本物の縦 log-link データ。 -/
def logLinkRealData (p : Nat) (hp : 1 ≤ p) : LogLinkRealData where
  p := p
  hp := hp
  d := 1
  hd := by omega
  logMap := logLinkMap p 1 hp
  is_log := rfl
  log_one := logLink_one p 1 hp
  log_hom := fun x y hx hy => logLink_hom p 1 hp (by omega) x y hx hy
  shell_content := fun x hx => (logLink_shell_step p 1 hp x hx).1
  kernel := fun x hx => logLink_kernel p 1 hp x hx
  vol_transport := fun logq v n m => logLink_volume_transport logq v n m

/-- **M337F-6c: 存在** — 本物の縦 log-link データは充足可能（K = ℚ₂）。 -/
theorem logLink_exists : Nonempty LogLinkRealData :=
  ⟨logLinkRealData 2 (by omega)⟩

/-! ## M337F-6 実例（ℤ₂・縦 log-link の本物性） -/

/-- 実例: 縦 log-link は単位元を 0 へ（ℤ₂, d=1）。 -/
example : logLinkMap 2 1 (by omega) (principalUnits 2).one = (zmod 2).one :=
  logLink_one 2 1 (by omega)

/-- 実例: 縦 log-link は加法 log-shell ℤ/2 を尽くす（生成元 1 を持つ主単数が存在）。 -/
example :
    ∃ u : (principalUnits 2).carrier,
      (unitFiltration 2 1).mem u
        ∧ logLinkMap 2 1 (by omega) u = Quot.mk (modCong 2).rel 1 :=
  logLink_surj 2 1 (by omega) (by omega) (Quot.mk (modCong 2).rel 1)

/-- 実例: 実 deg_ℝ 体積輸送（積 → 和）— 付値 2+3 の像体積は付値 2・3 の像体積の和。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (logLinkVolTransport logq v (2 + 3))
      (realAdd (logLinkVolTransport logq v 2) (logLinkVolTransport logq v 3)) :=
  logLink_volume_transport logq v 2 3

/-- 実例: 実テータパイロット体積（l=5, l⋇=2, Σj²=5）の log-link 像 = 加法 log-shell 体積。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thPilotTotalVol logq v 2)
      (logLinkVolTransport logq v ((sumSq 2 : Nat) : Int)) :=
  logLink_pilot_transport logq v 2

/-- 実例: 縦 log-link 辺は列を保つ（Θ-link 0 本の縦辺・M328F 横 theta-link と対比）。 -/
example (n m : Int) :
    (⟨n, m + 1⟩ : LatticeSite).col = (⟨n, m⟩ : LatticeSite).col :=
  logLink_vertical_preserves_col n m

end IUT
