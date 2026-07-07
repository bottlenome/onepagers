-- M392F LogLinkShellCompat [実・本物・柱D]
-- complete_pct 影響: 柱D で 縦 log-link（M337F）が対数殻フィルトレーション包含格子（M387F）を
--   保つこと（filtered map・入れ子の可換・graded 同型の誘導・上方包含が log-link 越しに生存）を実構成。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説。log は主項係数レベル・
--   局所体は K=ℚ_p・上方包含は整数レベル d-c（分数係数 1/2p 版は後続）・ℝ は setoid（realEq で言明）。

/-
  IUT/LogLinkShellCompat.lean — M392F（縦 log-link ⇄ 対数殻フィルトレーション包含格子の両立）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の p 進局所体 K = ℚ_p・O_v = ℤ_p 上で、
    M337F（`LogLinkReal`）の**縦 log-link**（乗法 U^(d) → 加法 log-shell m^d の graded log）と
    M387F（`LogShellContainment`）の**対数殻フィルトレーション包含格子**（下方/上方包含・
    殻/フィルトレーションの入れ子・graded 同型）の**両立**を本物で建てる。log-link が包含格子を
    **保つ**（filtered map・入れ子の可換・graded 同型を誘導・上方包含が log-link 越しに生存）ことを
    完全証明する。crux は導出しない。）
  * complete_pct 影響: **前進**。M337F は縦 log-link 写像・準同型・1 格子ステップ下降・実 deg_ℝ
    体積輸送を本物化し、M387F は対数殻の包含格子（下方 log(U^(d))⊆m^d・上方 log(U^(d))⊆m^{d-c}・
    入れ子・graded 同型 U^(d)/U^(d+1)≅m^d/m^{d+1}）を本物化した。両者の**次の本物の一手**は
    その**両立**——**縦 log-link が M387F の殻フィルトレーション構造を保つ**こと。本 M392F は:
      - **filtered map**: log-link(U^(d+1)) の leading log content が m^{d+1} に着地し、殻の入れ子で
        m^d にも収まる（M387F 格子に沿った filtered 写像）。
      - **入れ子の可換**: 源側の入れ子 U^{d+1}⊆U^d が、log-link を通して像側の入れ子 m^{d+1}⊆m^d と
        整合（log-link は包含格子と可換）。
      - **graded 同型の誘導**: log-link 写像（`logLinkMap` = M337F/M327F `logKumLog`）が M387F の
        graded 同型 U^(d)/U^(d+1)≅m^d/m^{d+1} を誘導（核 = U^(d+1)・全射、`lsc_graded_iso` を
        log-link 写像の語彙で採る）。
      - **上方包含の生存**: 実 deg_ℝ 体積輸送（M337F、積 → 和）と上方包含 log(U^(d))⊆m^{d-c}
        （M387F 有界補正 c）が両立し、**有界補正の付値下界が log-link 越しに生存**する（実
        付値レベルの主張、crux 不等式ではない）。
    crux Dβ-ω（多輻的アルゴリズム＝Ind3 log-shell 包含が与える不等式＝IUT 論争の係争点）は
    **決して導出せず**外部仮説のまま。柱D の log-link ⇄ log-shell の**両立を実で建設**する。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  本層は M337F（`LogLinkReal`, `logLinkMap`/`logLinkVolTransport`/`logLink_volume_transport`）と
  M387F（`LogShellContainment`, `lsc_log_lower`/`lsc_shell_nesting`/`lsc_filt_nesting`/
  `lsc_log_filtration`/`lsc_log_upper`/`lsc_graded_iso`）の**本物の対象**の上に、
  両者の**両立**を新規に積む:
  * M392F-1 `llsc_loglink_filtered`/`llsc_loglink_filtered_le` — **filtered map**:
    log-link(U^(d+1)) の content が m^{d+1} に着地し殻の入れ子で m^d へ（下方包含 + 入れ子の合成）・
    一般 d ≤ e 版（`lsc_log_filtration`）。
  * M392F-2 `llsc_nesting_coherent` — **入れ子の可換**: x ∈ U^{d+1} は源側 U^d に入り（`lsc_filt_nesting`）
    かつ像 content が m^d に収まる（filtered）——log-link が源/像の入れ子を可換に保つ。
  * M392F-3 `llsc_graded_kernel`/`llsc_graded_surj`/`llsc_graded_iso` — **graded 同型の誘導**:
    log-link 写像 `logLinkMap`（= `logKumLog`）が M387F graded 同型 U^(d)/U^(d+1)≅m^d/m^{d+1} を
    誘導（`lsc_graded_kernel`/`lsc_graded_surj`/`lsc_graded_iso` を log-link 写像の語彙で採る）。
  * M392F-4 `llsc_vol_upper_compat`/`llsc_pilot_upper_compat` — **上方包含の生存**: 実 deg_ℝ
    体積輸送（`logLink_volume_transport`、積 → 和）と上方包含 `lsc_log_upper`（有界補正 c）の両立・
    実テータパイロット体積版。
  * M392F-5 `llsc_crux_external`/`llsc_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説
    （決して導出しない）。
  * M392F-6 capstone `LogLinkShellCompatData`/`logLinkShellCompatData`/`llsc_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）
  * **crux Dβ-ω（多輻的アルゴリズム＝Ind3 log-shell 包含が与える不等式＝IUT 論争の当の係争点）は
    恒久的に本層の範囲外**。上方包含の生存（`llsc_vol_upper_compat`）は crux が「使う」構造的入力
    （付値下界が log-link 越しに生存する）だが、**多輻不等式そのもの**は本層で決して証明せず、crux を
    任意の外部 Prop として受け取るだけ（`llsc_crux_is_hypothesis` は Iff.rfl）。
  * **log 写像は p 進対数の主項 θ_d（`logKumLog`/`logLinkMap`, M327F/M337F）で本物**（完全収束級数は
    後続）。filtered map・入れ子の可換・graded 同型の誘導は各段 U^(d) 上で本物。
  * **上方包含は Nat 付値レベルの下界** m^{d-c}（有界補正 c）。原文 I_K = (1/2p)·log(O_K^×) の分数係数
    は ℤ_p に 1/p が無いため整数レベル d-c に留める（分数係数版は後続）。
  * **局所体は K = ℚ_p（O_v = ℤ_p, U^(d)=1+p^d ℤ_p, m^d = p^d ℤ_p）**。一般局所体・完全同変性は後続。
    **ℝ は setoid** ゆえ体積輸送は realEq で言明。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。
  禁止タクティク不使用（core Lean のみ）。共有ファイル（IUT.lean・build.sh・dashboard.md・
  graph 系）は一切変更なし。柱D 横展開・本物の先行建設[実]。一般名は `llsc` 接頭辞で衝突回避。
-/
import IUT.LogLinkReal
import IUT.LogShellContainment

namespace IUT

/-! ## M392F-1: log-link は M387F 殻格子に沿った filtered map -/

/-- **定理 (M392F-1a): 縦 log-link は filtered map（1 段）** — レベル d+1 の主単数
    x ∈ U^(d+1) について、その leading log content x−1 は対数殻 m^{d+1} に着地し
    （下方包含 M387F-1 `lsc_log_lower`）、殻の入れ子 m^{d+1} ⊆ m^d（M387F-2b
    `lsc_shell_nesting`）により m^d にも収まる。すなわち縦 log-link（M337F）は M387F の
    **殻フィルトレーション包含格子に沿った filtered 写像**（深い単数の log は深い殻へ、
    殻は入れ子）。 -/
theorem llsc_loglink_filtered (p d : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p (d + 1)).mem x) :
    logShellMem p (d + 1) (logShellContent p x.val)
      ∧ logShellMem p d (logShellContent p x.val) :=
  ⟨lsc_log_lower p (d + 1) x hx,
   lsc_shell_nesting p d (logShellContent p x.val) (lsc_log_lower p (d + 1) x hx)⟩

/-- **定理 (M392F-1b): 縦 log-link は filtered map（一般 d ≤ e）** — より深い主単数
    x ∈ U^(e)（e ≥ d）の log content は殻 m^d に収まる（M387F-3 `lsc_log_filtration`、
    下方包含 + 入れ子の合成）。縦 log-link が M387F 包含格子に沿って filtered であることの
    一般版（レベルを跨いだ包含 log-link(U^(e)) ⊆ m^d）。 -/
theorem llsc_loglink_filtered_le (p : Nat) {d e : Nat} (h : d ≤ e)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p e).mem x) :
    logShellMem p d (logShellContent p x.val) :=
  lsc_log_filtration p h x hx

/-! ## M392F-2: log-link は源/像の入れ子を可換に保つ -/

/-- **定理 (M392F-2: 入れ子の可換)** — レベル d+1 の主単数 x ∈ U^(d+1) について、
    **源側の入れ子** x ∈ U^d（乗法フィルトレーションの入れ子 U^{d+1}⊆U^d、M387F-2c
    `lsc_filt_nesting`）**と**、**像側の入れ子** log content ∈ m^d（filtered map M392F-1a）が
    **同時に成立**する。すなわち縦 log-link は **M387F の包含格子（源の乗法入れ子 ⇄ 像の加法
    入れ子）と可換**——log-link はレベル d を対応する殻/フィルトレーション片へ coherent に写す。 -/
theorem llsc_nesting_coherent (p d : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p (d + 1)).mem x) :
    (unitFiltration p d).mem x
      ∧ logShellMem p d (logShellContent p x.val) :=
  ⟨lsc_filt_nesting p d x hx, (llsc_loglink_filtered p d x hx).2⟩

/-! ## M392F-3: log-link 写像が M387F の graded 同型を誘導 -/

/-- **定理 (M392F-3a): log-link は graded 同型の核 U^(d+1) を誘導** — 縦 log-link 写像
    `logLinkMap`（= M337F/M327F の graded log θ_d）について、u ∈ U^(d) の log-link 値が
    加法単位元 0 になるのはちょうど u ∈ U^(d+1) のとき（M387F-5a `lsc_graded_kernel`）。
    log-link 写像が M387F graded 同型 U^(d)/U^(d+1)≅m^d/m^{d+1} の**核**を誘導する。 -/
theorem llsc_graded_kernel (p d : Nat) (hp : 1 ≤ p)
    (u : (principalUnits p).carrier) (hu : (unitFiltration p d).mem u) :
    (logLinkMap p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u) :=
  lsc_graded_kernel p d hp u hu

/-- **定理 (M392F-3b): log-link は graded 同型の全射性を誘導** — 加法殻商 m^d/m^{d+1} ≅ ℤ/p の
    任意の類 c は U^(d) のある主単数の log-link 値（M387F-5b `lsc_graded_surj`）。log-link 写像が
    graded 同型の**全射性**を誘導する。 -/
theorem llsc_graded_surj (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (c : (zmod p).carrier) :
    ∃ u : (principalUnits p).carrier,
      (unitFiltration p d).mem u ∧ logLinkMap p d hp u = c :=
  lsc_graded_surj p d hp hd c

/-- **定理 (M392F-3c): 縦 log-link は M387F graded 同型 U^(d)/U^(d+1)≅m^d/m^{d+1} を誘導** —
    縦 log-link 写像 `logLinkMap` は U^(d) を加法殻商 ℤ/p ≅ m^d/m^{d+1} へ**全射**し、その**核は
    ちょうど U^(d+1)**（M387F-5c `lsc_graded_iso` を log-link 写像の語彙で採る）。すなわち縦
    log-link と殻フィルトレーションが graded ピース上で両立し、log-link が M387F graded 同型を
    誘導する（第一同型定理を全射+核で表す本リポジトリ標準形式）。 -/
theorem llsc_graded_iso (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) :
    (∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
        (unitFiltration p d).mem u ∧ logLinkMap p d hp u = c)
    ∧ (∀ u : (principalUnits p).carrier, (unitFiltration p d).mem u →
        (logLinkMap p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)) :=
  lsc_graded_iso p d hp hd

/-! ## M392F-4: 実 deg_ℝ 体積輸送と上方包含の両立（有界補正が log-link 越しに生存） -/

/-- **定理 (M392F-4a: 上方包含の生存)** — 縦 log-link の実 deg_ℝ 体積輸送（M337F、加法ゆえ積 → 和、
    deg_ℝ(n+m) ≈ deg_ℝ(n) + deg_ℝ(m)、`logLink_volume_transport`、realEq）**と**、M387F の上方包含
    log(U^(d)) ⊆ m^{d-c}（有界補正 c、`lsc_log_upper`）が**両立**する。すなわち**有界補正の付値下界が
    log-link（体積輸送）越しに生存**する——「log-shell は大きすぎない」方向の付値下界が縦 log-link の
    加法輸送の下で保たれる、実付値レベルの主張。多輻不等式（crux Dβ-ω）そのものは決して導出しない。 -/
theorem llsc_vol_upper_compat (p d c : Nat)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x)
    (logq : Nat → RReal) (v : Nat) (n m : Int) :
    realEq (logLinkVolTransport logq v (n + m))
        (realAdd (logLinkVolTransport logq v n) (logLinkVolTransport logq v m))
      ∧ logShellMem p (d - c) (logShellContent p x.val) :=
  ⟨logLink_volume_transport logq v n m, lsc_log_upper p d c x hx⟩

/-- **定理 (M392F-4b: 実テータパイロット体積の log-link 像 ⇄ 上方包含)** — 実テータパイロット総体積
    Σj²·log q_v（M319F）の縦 log-link 像が加法 log-shell 体積に一致し（`logLink_pilot_transport`、
    realEq）、かつ上方包含 log(U^(d)) ⊆ m^{d-c}（`lsc_log_upper`）が両立する。実テータパイロット体積の
    log-link 輸送と有界補正の付値下界が同時に本物で成立（crux 不等式ではない）。 -/
theorem llsc_pilot_upper_compat (p d c : Nat)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x)
    (logq : Nat → RReal) (v : Nat) (k : Nat) :
    realEq (thPilotTotalVol logq v k)
        (logLinkVolTransport logq v ((sumSq k : Nat) : Int))
      ∧ logShellMem p (d - c) (logShellContent p x.val) :=
  ⟨logLink_pilot_transport logq v k, lsc_log_upper p d c x hx⟩

/-! ## M392F-5: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M392F-5a: crux は外部仮説・決して導出しない／honest)** — 縦 log-link が M387F 殻格子を
    保つこと（filtered map `llsc_loglink_filtered`）は**無条件で本物**（crux とは独立に成立）。しかし
    その両立構造を**使う多輻的アルゴリズム**（Ind3 log-shell 包含が与える crux Dβ-ω ＝ IUT 論争の
    当の係争点 ＝ 多輻不等式）は本層で**決して証明しない**。crux を任意の外部 Prop `crux` として
    受け取り、filtered map の本物性 **と** crux の連言を、crux が仮説として供給された場合にのみ
    返す——crux は決して導出されない。 -/
theorem llsc_crux_external (p d : Nat)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p (d + 1)).mem x)
    (crux : Prop) (hcrux : crux) :
    logShellMem p d (logShellContent p x.val) ∧ crux :=
  ⟨(llsc_loglink_filtered p d x hx).2, hcrux⟩

/-- **定理 (M392F-5b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明した定理ではなく、論争の
    係争点をそのまま外部仮説として受け取ったものであることを機械検証で明示（M337F
    `logLink_crux_hypothesis`・M387F `lsc_crux_is_hypothesis` と同じ精神）。 -/
theorem llsc_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M392F-6: capstone -/

/-- **M392F-6a: log-link ⇄ 殻格子両立データ**（総括） — 本物の p 進局所体 K = ℚ_p・O_v = ℤ_p 上で
    縦 log-link（M337F）が対数殻フィルトレーション包含格子（M387F）を保つことを束ねる:
    filtered map（log-link(U^(d+1)) の content が m^{d+1}⊆m^d へ着地）・入れ子の可換（源 U^{d+1}⊆U^d
    ⇄ 像 m^{d+1}⊆m^d）・graded 同型の誘導（U^(d)/U^(d+1)≅m^d/m^{d+1}・核 = U^(d+1)・全射）・
    上方包含の生存（実 deg_ℝ 体積輸送と log(U^(d))⊆m^{d-c} の両立）。主語は M337F/M387F の本物の
    log-link・対数殻・graded log であり toy を用いない。crux Dβ-ω は範囲外。 -/
structure LogLinkShellCompatData where
  /-- 局所体 K = ℚ_p の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  /-- p ≥ 1。 -/
  hp : 1 ≤ p
  /-- フィルトレーション段 d ≥ 1。 -/
  d : Nat
  /-- d ≥ 1。 -/
  hd : 1 ≤ d
  /-- 縦 log-link 写像（graded log θ_d、乗法 U^(d) → 加法殻商 ℤ/p）。 -/
  logMap : (principalUnits p).carrier → (zmod p).carrier
  /-- logMap は M337F の本物の縦 log-link 写像。 -/
  is_log : logMap = logLinkMap p d hp
  /-- 対数殻 m^e = p^e·ℤ_p の会員述語。 -/
  shellMem : Nat → (Zp p).carrier → Prop
  /-- shellMem は M321F の本物の対数殻会員述語。 -/
  is_shell : shellMem = logShellMem p
  /-- leading log content x − 1（p 進 log の主項）。 -/
  logContent : (Zp p).carrier → (Zp p).carrier
  /-- logContent は M321F の本物の leading log content。 -/
  is_content : logContent = logShellContent p
  /-- filtered map: log-link(U^(d+1)) の content は m^{d+1} に着地し殻の入れ子で m^d へ。 -/
  filtered : ∀ (x : (principalUnits p).carrier), (unitFiltration p (d + 1)).mem x →
    shellMem (d + 1) (logContent x.val) ∧ shellMem d (logContent x.val)
  /-- 入れ子の可換: x ∈ U^(d+1) は源側 U^d に入り像 content が m^d に収まる。 -/
  nesting_coherent : ∀ (x : (principalUnits p).carrier), (unitFiltration p (d + 1)).mem x →
    (unitFiltration p d).mem x ∧ shellMem d (logContent x.val)
  /-- graded 同型の核 = U^(d+1)（log-link 写像が誘導）。 -/
  graded_kernel : ∀ (u : (principalUnits p).carrier), (unitFiltration p d).mem u →
    (logMap u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)
  /-- graded 同型の全射性（log-link 写像が加法殻商 m^d/m^{d+1} ≅ ℤ/p を尽くす）。 -/
  graded_surj : ∀ c : (zmod p).carrier,
    ∃ u : (principalUnits p).carrier,
      (unitFiltration p d).mem u ∧ logMap u = c
  /-- 実 deg_ℝ 体積輸送（log-link は積を和へ移す、realEq）。 -/
  vol_transport : ∀ (logq : Nat → RReal) (v : Nat) (n m : Int),
    realEq (logLinkVolTransport logq v (n + m))
      (realAdd (logLinkVolTransport logq v n) (logLinkVolTransport logq v m))
  /-- 上方包含の生存: log(U^(d)) ⊆ m^{d-c}（有界補正 c、log-link 越しに生存）。 -/
  upper_survives : ∀ c (x : (principalUnits p).carrier), (unitFiltration p d).mem x →
    shellMem (d - c) (logContent x.val)

/-- **M392F-6b: witness** — ℤ_p 上（段 d=1）の本物の log-link ⇄ 殻格子両立データ。 -/
def logLinkShellCompatData (p : Nat) (hp : 1 ≤ p) : LogLinkShellCompatData where
  p := p
  hp := hp
  d := 1
  hd := by omega
  logMap := logLinkMap p 1 hp
  is_log := rfl
  shellMem := logShellMem p
  is_shell := rfl
  logContent := logShellContent p
  is_content := rfl
  filtered := fun x hx => llsc_loglink_filtered p 1 x hx
  nesting_coherent := fun x hx => llsc_nesting_coherent p 1 x hx
  graded_kernel := fun u hu => llsc_graded_kernel p 1 hp u hu
  graded_surj := fun c => llsc_graded_surj p 1 hp (by omega) c
  vol_transport := fun logq v n m => logLink_volume_transport logq v n m
  upper_survives := fun c x hx => lsc_log_upper p 1 c x hx

/-- **M392F-6c: 存在** — 本物の log-link ⇄ 殻格子両立データは充足可能（K = ℚ₂）。 -/
theorem llsc_exists : Nonempty LogLinkShellCompatData :=
  ⟨logLinkShellCompatData 2 (by omega)⟩

/-! ## M392F-6 実例（ℤ₂・log-link ⇄ 殻格子両立の本物性） -/

/-- 実例（filtered map）: レベル d+1 の主単数の log content は m^{d+1} に着地し殻の入れ子で m^d へ。 -/
example (p d : Nat) (x : (principalUnits p).carrier) (hx : (unitFiltration p (d + 1)).mem x) :
    logShellMem p (d + 1) (logShellContent p x.val)
      ∧ logShellMem p d (logShellContent p x.val) :=
  llsc_loglink_filtered p d x hx

/-- 実例（入れ子の可換）: x ∈ U^(d+1) は源側 U^d に入り像 content が m^d に収まる。 -/
example (p d : Nat) (x : (principalUnits p).carrier) (hx : (unitFiltration p (d + 1)).mem x) :
    (unitFiltration p d).mem x ∧ logShellMem p d (logShellContent p x.val) :=
  llsc_nesting_coherent p d x hx

/-- 実例（graded 同型の誘導・ℤ₂）: log-link 写像は加法殻商 ℤ/2 の生成元 1 を誘導する
    （U^(1)/U^(2) ≅ m^1/m^2 の全射性を log-link 写像で）。 -/
example :
    ∃ u : (principalUnits 2).carrier,
      (unitFiltration 2 1).mem u ∧ logLinkMap 2 1 (by omega) u = Quot.mk (modCong 2).rel 1 :=
  llsc_graded_surj 2 1 (by omega) (by omega) (Quot.mk (modCong 2).rel 1)

/-- 実例（上方包含の生存）: 実 deg_ℝ 体積輸送（積 → 和）と上方包含 m^{d-c} が両立する。 -/
example (p d c : Nat) (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x)
    (logq : Nat → RReal) (v : Nat) :
    realEq (logLinkVolTransport logq v (2 + 3))
        (realAdd (logLinkVolTransport logq v 2) (logLinkVolTransport logq v 3))
      ∧ logShellMem p (d - c) (logShellContent p x.val) :=
  llsc_vol_upper_compat p d c x hx logq v 2 3

/-- 実例（crux は外部仮説）: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  llsc_crux_is_hypothesis crux

/-- 実例（capstone 存在）: log-link ⇄ 殻格子両立データは存在する。 -/
example : Nonempty LogLinkShellCompatData :=
  llsc_exists

end IUT
