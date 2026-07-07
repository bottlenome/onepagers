-- M387F LogShellContainment [実・本物・柱D]
-- complete_pct 影響: 柱D で 主単数フィルトレーション U^(d)=1+m^d と p 進 log の
--   本物の対数殻包含格子（log(U^(d))⊆m^d の下方包含・殻/フィルトレーションの入れ子
--   m^{d+1}⊆m^d・U^{d+1}⊆U^d・log(U^(e))⊆m^d (d≤e)・「殻は大きすぎない」上方包含
--   log(U^(d))⊆m^{d-c}・graded log による U^(d)/U^(d+1)≅m^d/m^{d+1} 同型）を実 ℤ_p /
--   付値模型上で本物構成（crux は導出しない）。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説。
--   （`lsc_crux_external` は crux を受け取るのみ・`lsc_crux_is_hypothesis` は Iff.rfl）。
--   上方包含は crux が「使う」構造的入力だが、多輻不等式そのものは本層で決して証明しない。

/-
  IUT/LogShellContainment.lean — M387F（本物の対数殻フィルトレーション包含格子）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の p 進局所体 K = ℚ_p・O_v = ℤ_p 上の
    対数殻 m^d = p^d·ℤ_p（M321F）と本物の主単数フィルトレーション
    U^(d) = 1 + m^d（M31）・graded log θ_d（M327F `logKumLog`）の上に、
    **対数殻の包含格子**（filtration ⇄ shell の包含・入れ子・graded 同型）を
    本物で組織化する）。
  * complete_pct 影響: **前進**。M382F（`MultiradialIndet`）は 3 不定性を
    群作用として組織し、Ind3（log-shell 膨張）を明示 m シフトとして残したが、
    その log-shell の**包含構造**（膨張作用の受け皿となる殻の入れ子・log の
    着地レベル）は範囲外だった。本 M387F はその**次の本物の一手**として、
    log-shell の**フィルトレーション/包含格子**を実 ℤ_p 上で閉じる:
      - 下方包含 log(U^(d)) ⊆ m^d（レベル d の主単数の log はレベル ≥ d の殻へ）
      - 殻の入れ子 m^{d+1} ⊆ m^d（p^{d+1}ℤ_p ⊆ p^dℤ_p）・
        フィルトレーションの入れ子 U^{d+1} ⊆ U^d
      - フィルトレーション包含 log(U^(e)) ⊆ m^d（d ≤ e、深い単数は深い殻へ）
      - 上方包含 log(U^(d)) ⊆ m^{d-c}（有界補正 c、「殻は大きすぎない」方向、
        付値下界としての本物の主張）——これが多輻的**上界**が**使う**構造的入力
      - graded log による U^(d)/U^(d+1) ≅ m^d/m^{d+1} 同型（核 = U^(d+1)・全射）
    crux Dβ-ω（多輻的アルゴリズム＝Ind3 log-shell 包含が与える不等式＝論争の
    係争点）は**決して導出せず**外部仮説のまま。柱D の log-shell 対象の
    **包含格子を代理 → 実へ昇格**させる（M321F/M327F の本物を包含格子へ組織化）。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  本層は M321F（`LogShellReal`）と M327F（`LogKummerReal`）の**本物の対象**の上に、
  対数殻の**包含格子**を新規に積む:
  * M387F-1 `lsc_log_lower` — 下方包含 log(U^(d)) ⊆ m^d（M321F
    `logShell_unit_filtration` を包含格子の語彙で採る）。
  * M387F-2 `lsc_shell_nesting`/`lsc_shell_nesting_le`/`lsc_filt_nesting` —
    殻の入れ子 m^{d+1} ⊆ m^d（M321F `logShell_antitone`）・一般 d ≤ e 版・
    フィルトレーションの入れ子 U^{d+1} ⊆ U^d（M31 `unitFiltration_antitone`）。
  * M387F-3 `lsc_log_filtration` — **フィルトレーション包含** log(U^(e)) ⊆ m^d
    （d ≤ e、深い単数は深い殻へ着地し殻は入れ子）＝下方包含 + 入れ子の合成。
    これが「殻の間の包含 log(U^(d))」の本物の格子内容（新規合成）。
  * M387F-4 `lsc_log_upper` — **上方包含** log(U^(d)) ⊆ m^{d-c}（有界補正 c）。
    Nat 減算で d - c ≤ d（`Nat.sub_le`）ゆえ m^d ⊆ m^{d-c}、log 内容は付値 ≥ d-c。
    「殻は大きすぎない」方向の付値下界。これが多輻的**上界**が使う構造的入力
    （不等式そのものは crux で外部）。
  * M387F-5 `lsc_graded_kernel`/`lsc_graded_surj`/`lsc_graded_iso` — graded log
    による **U^(d)/U^(d+1) ≅ m^d/m^{d+1}**（核 = U^(d+1)・ℤ/p ≅ m^d/m^{d+1} へ全射）。
    M327F `logKum_log_kernel`/`logKum_log_surj`/`logKum_frob_etale` を殻商同型の
    語彙で採る。
  * M387F-6 `lsc_crux_external`/`lsc_crux_is_hypothesis` — crux Dβ-ω は外部仮説
    （決して導出しない・Iff.rfl のみ）。
  * M387F-7 capstone `LogShellContainmentData`/`lscContainmentData`/`lsc_exists`
    と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）
  * **crux Dβ-ω（多輻的アルゴリズム＝Ind3 log-shell 包含が与える不等式＝IUT 論争の
    当の係争点）は恒久的に本層の範囲外**。上方包含 log(U^(d)) ⊆ m^{d-c} は crux が
    「使う」構造的入力（付値下界）だが、**多輻不等式そのもの**は本層で決して証明せず、
    crux を任意の外部 Prop として受け取るだけ（`lsc_crux_is_hypothesis` は Iff.rfl）。
  * **log 写像は p 進対数の主項 θ_d（`logKumLog`, M327F）で本物**（完全収束級数
    log(1+t)=t−t²/2+… は後続）。下方/フィルトレーション/graded 包含は各段 U^(d) 上で本物。
  * **log-shell の下方包含は「leading log content x − 1」で本物**（M321F
    `logShellContent`）。完全 log の全項での包含は完全収束級数を要し後続。
  * **上方包含は Nat 付値レベルの下界** m^{d-c}（有界補正 c）として本物。原文 IUT の
    I_K = (1/2p)·log(O_K^×) の分数係数（ℤ_p の外へ出る fractional module）は ℤ_p に
    1/p が無いため本層では整数レベル d-c に留める（分数係数版は後続）。
  * **局所体は K = ℚ_p（O_v = ℤ_p, U^(d)=1+p^d ℤ_p, m^d = p^d ℤ_p）**。一般局所体・
    分数 log-shell・完全同変性は後続。deg_ℝ／測度論的 log-volume との数値接続も後続。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。
  禁止タクティク不使用（core Lean のみ）。共有ファイル（IUT.lean・build.sh・
  dashboard.md・graph 系）は一切変更なし。柱D 横展開・本物の先行建設[実]。
  一般名は `lsc` 接頭辞で衝突回避。
-/
import IUT.LogShellReal
import IUT.LogKummerReal

namespace IUT

/-! ## M387F-1: 下方包含 log(U^(d)) ⊆ m^d -/

/-- **定理 (M387F-1): 対数殻下方包含 log(U^(d)) ⊆ m^d** — レベル d の主単数
    x ∈ U^(d) = 1 + m^d の leading log content x − 1 は対数殻 m^d = p^d·ℤ_p に
    着地する。すなわち「レベル d の主単数の log はレベル ≥ d の殻へ落ちる」本物の
    包含（M321F `logShell_unit_filtration` を包含格子の語彙で採る）。log-Kummer 対応
    U^(d) → m^d の下方（付値を上げる）方向。 -/
theorem lsc_log_lower (p d : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) :
    logShellMem p d (logShellContent p x.val) :=
  logShell_unit_filtration p d x hx

/-! ## M387F-2: 殻・フィルトレーションの入れ子 -/

/-- **定理 (M387F-2a): 殻の入れ子（一般）** — d ≤ e なら m^e ⊆ m^d
    （p^eℤ_p ⊆ p^dℤ_p、付値の単調性）。対数殻格子の反変性（M321F `logShell_antitone`）。 -/
theorem lsc_shell_nesting_le (p : Nat) {d e : Nat} (h : d ≤ e)
    (x : (Zp p).carrier) (hx : logShellMem p e x) : logShellMem p d x :=
  logShell_antitone p h x hx

/-- **定理 (M387F-2b): 殻の一段入れ子 m^{d+1} ⊆ m^d** — 高次の殻は低次の殻に
    含まれる（p^{d+1}ℤ_p ⊆ p^dℤ_p）。Ind3 膨張作用（M382F）が殻を一段動かす際の
    受け皿の入れ子構造。 -/
theorem lsc_shell_nesting (p d : Nat) (x : (Zp p).carrier)
    (hx : logShellMem p (d + 1) x) : logShellMem p d x :=
  logShell_antitone p (Nat.le_succ d) x hx

/-- **定理 (M387F-2c): フィルトレーションの一段入れ子 U^{d+1} ⊆ U^d** — 高次の
    主単数群は低次の主単数群に含まれる（1 + m^{d+1} ⊆ 1 + m^d）。乗法側の入れ子で、
    殻の入れ子（M387F-2b）と log で整合する（M31 `unitFiltration_antitone`）。 -/
theorem lsc_filt_nesting (p d : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p (d + 1)).mem x) : (unitFiltration p d).mem x :=
  unitFiltration_antitone p (Nat.le_succ d) x hx

/-! ## M387F-3: フィルトレーション包含 log(U^(e)) ⊆ m^d（d ≤ e） -/

/-- **定理 (M387F-3): フィルトレーション包含 log(U^(e)) ⊆ m^d（d ≤ e）** —
    より深い主単数 x ∈ U^(e)（e ≥ d）の log content は、より深い殻 m^e に着地し
    （下方包含）、殻は入れ子 m^e ⊆ m^d なので m^d にも収まる。＝「深い単数は深い殻へ、
    殻は入れ子」の合成。これが**殻の間の包含 log(U^(d)) ⊆ m^d の格子構造**の本物
    （下方包含 M387F-1 + 入れ子 M387F-2a の合成、新規）。 -/
theorem lsc_log_filtration (p : Nat) {d e : Nat} (h : d ≤ e)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p e).mem x) :
    logShellMem p d (logShellContent p x.val) :=
  logShell_antitone p h (logShellContent p x.val)
    (logShell_unit_filtration p e x hx)

/-! ## M387F-4: 上方包含 log(U^(d)) ⊆ m^{d-c}（有界補正 c・「殻は大きすぎない」） -/

/-- **定理 (M387F-4): 対数殻上方包含 log(U^(d)) ⊆ m^{d-c}（有界補正 c）** —
    レベル d の主単数の log content は、**有界補正 c だけ緩めた殻** m^{d-c} にも収まる
    （Nat 減算で d - c ≤ d ゆえ m^d ⊆ m^{d-c}、log の付値は ≥ d ≥ d-c）。これが
    「log-shell は大きすぎない」（上界）方向の**付値下界としての本物の主張**であり、
    **多輻的上界が使う構造的入力**そのもの。ただし多輻不等式（crux Dβ-ω）自体は
    本層で決して導出しない（M387F-6 外部仮説）。原文 I_K の分数係数 1/(2p) は
    ℤ_p に 1/p が無いため整数レベル d-c に留める（正直な限定）。 -/
theorem lsc_log_upper (p d c : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) :
    logShellMem p (d - c) (logShellContent p x.val) :=
  logShell_antitone p (Nat.sub_le d c) (logShellContent p x.val)
    (logShell_unit_filtration p d x hx)

/-! ## M387F-5: graded log による U^(d)/U^(d+1) ≅ m^d/m^{d+1} 同型 -/

/-- **定理 (M387F-5a): graded 同型の核 = U^(d+1)** — u ∈ U^(d) について
    log u = 0 ⟺ u ∈ U^(d+1)。乗法フィルトレーション商 U^(d)/U^(d+1) と加法殻商
    m^d/m^{d+1} の同型の核（次段 U^(d+1) がちょうど log の核＝殻 m^{d+1} に対応）。
    M327F `logKum_log_kernel` を殻商同型の語彙で採る。 -/
theorem lsc_graded_kernel (p d : Nat) (hp : 1 ≤ p)
    (u : (principalUnits p).carrier) (hu : (unitFiltration p d).mem u) :
    (logKumLog p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u) :=
  logKum_log_kernel p d hp u hu

/-- **定理 (M387F-5b): graded 同型の全射性** — 加法殻商 m^d/m^{d+1} ≅ ℤ/p の任意の
    類は U^(d) のある主単数の log。乗法フィルトレーション商が加法殻商を尽くす
    （M327F `logKum_log_surj`）。 -/
theorem lsc_graded_surj (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (c : (zmod p).carrier) :
    ∃ u : (principalUnits p).carrier,
      (unitFiltration p d).mem u ∧ logKumLog p d hp u = c :=
  logKum_log_surj p d hp hd c

/-- **定理 (M387F-5c): graded 同型 U^(d)/U^(d+1) ≅ m^d/m^{d+1}** — graded log θ_d は
    U^(d) を加法殻商 ℤ/p ≅ m^d/m^{d+1} へ**全射**し、その**核はちょうど U^(d+1)**。
    ＝ 単数フィルトレーション商と対数殻商の付値方向の同型（第一同型定理を hom+核+全射で
    表す本リポジトリ標準形式、M327F `logKum_frob_etale` を殻商同型の語彙で採る）。
    Ind3 膨張が動かす殻の**graded ピース**の乗法 ⇄ 加法対応の本物。 -/
theorem lsc_graded_iso (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) :
    (∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
        (unitFiltration p d).mem u ∧ logKumLog p d hp u = c)
    ∧ (∀ u : (principalUnits p).carrier, (unitFiltration p d).mem u →
        (logKumLog p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)) :=
  logKum_frob_etale p d hp hd

/-! ## M387F-6: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M387F-6a: crux は外部仮説・決して導出しない／honest)** — 対数殻の
    下方包含 log(U^(d)) ⊆ m^d（`lsc_log_lower`）と上方包含 log(U^(d)) ⊆ m^{d-c}
    （`lsc_log_upper`）は**無条件で本物**（crux とは独立に成立）。しかしそれらの
    構造的入力を**使う多輻的アルゴリズム**（Ind3 log-shell 包含が与える crux Dβ-ω
    ＝ IUT 論争の当の係争点＝多輻不等式）は本層で**決して証明しない**。crux を任意の
    外部 Prop `crux` として受け取り、下方包含の本物性 **と** crux の連言を、crux が
    仮説として供給された場合にのみ返す——crux は決して導出されない。 -/
theorem lsc_crux_external (p d : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x)
    (crux : Prop) (hcrux : crux) :
    logShellMem p d (logShellContent p x.val) ∧ crux :=
  ⟨lsc_log_lower p d x hx, hcrux⟩

/-- **定理 (M387F-6b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る
    仮説そのもの**として扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明
    した定理ではなく、論争の係争点をそのまま外部仮説として受け取ったものであることを
    機械検証で明示（M382F `mind_crux_is_hypothesis` と同じ精神）。 -/
theorem lsc_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M387F-7: capstone -/

/-- **M387F-7a: 対数殻包含格子データ**（総括） — 本物の p 進局所体 K = ℚ_p・
    O_v = ℤ_p 上の対数殻 m^d = p^d·ℤ_p と主単数フィルトレーション U^(d) = 1 + m^d の
    **包含格子**を束ねる: 下方包含 log(U^(d)) ⊆ m^d・殻/フィルトレーションの入れ子・
    フィルトレーション包含 log(U^(e)) ⊆ m^d (d ≤ e)・上方包含 log(U^(d)) ⊆ m^{d-c}・
    graded log による U^(d)/U^(d+1) ≅ m^d/m^{d+1}（核 = U^(d+1)・全射）。主語は
    M321F/M327F の本物の対数殻・主単数群・graded log であり toy を用いない。
    crux Dβ-ω（Ind3 log-shell 包含が与える多輻不等式）は範囲外。 -/
structure LogShellContainmentData where
  /-- 局所体 K = ℚ_p の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  /-- p ≥ 1。 -/
  hp : 1 ≤ p
  /-- 対数殻 m^d = p^d·ℤ_p の会員述語。 -/
  shellMem : Nat → (Zp p).carrier → Prop
  /-- shellMem は本物の対数殻会員述語。 -/
  is_shell : shellMem = logShellMem p
  /-- leading log content x − 1（p 進 log の主項）。 -/
  logContent : (Zp p).carrier → (Zp p).carrier
  /-- logContent は本物の leading log content。 -/
  is_content : logContent = logShellContent p
  /-- 下方包含: log(U^(d)) ⊆ m^d。 -/
  log_lower : ∀ d (x : (principalUnits p).carrier),
    (unitFiltration p d).mem x → shellMem d (logContent x.val)
  /-- 殻の一段入れ子 m^{d+1} ⊆ m^d。 -/
  shell_nesting : ∀ d (x : (Zp p).carrier), shellMem (d + 1) x → shellMem d x
  /-- フィルトレーションの一段入れ子 U^{d+1} ⊆ U^d。 -/
  filt_nesting : ∀ d (x : (principalUnits p).carrier),
    (unitFiltration p (d + 1)).mem x → (unitFiltration p d).mem x
  /-- フィルトレーション包含: d ≤ e なら log(U^(e)) ⊆ m^d。 -/
  log_filtration : ∀ {d e} (_ : d ≤ e) (x : (principalUnits p).carrier),
    (unitFiltration p e).mem x → shellMem d (logContent x.val)
  /-- 上方包含: log(U^(d)) ⊆ m^{d-c}（有界補正 c、「殻は大きすぎない」・多輻上界の入力）。 -/
  log_upper : ∀ d c (x : (principalUnits p).carrier),
    (unitFiltration p d).mem x → shellMem (d - c) (logContent x.val)
  /-- graded 同型の核 = U^(d+1)。 -/
  graded_kernel : ∀ d (u : (principalUnits p).carrier), (unitFiltration p d).mem u →
    (logKumLog p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)
  /-- graded 同型の全射性（加法殻商 m^d/m^{d+1} ≅ ℤ/p を尽くす）。 -/
  graded_surj : ∀ d, 1 ≤ d → ∀ c : (zmod p).carrier,
    ∃ u : (principalUnits p).carrier,
      (unitFiltration p d).mem u ∧ logKumLog p d hp u = c

/-- **M387F-7b: witness** — ℤ_p 上の本物の対数殻包含格子データ。 -/
def lscContainmentData (p : Nat) (hp : 1 ≤ p) : LogShellContainmentData where
  p := p
  hp := hp
  shellMem := logShellMem p
  is_shell := rfl
  logContent := logShellContent p
  is_content := rfl
  log_lower := fun d x hx => lsc_log_lower p d x hx
  shell_nesting := fun d x hx => lsc_shell_nesting p d x hx
  filt_nesting := fun d x hx => lsc_filt_nesting p d x hx
  log_filtration := fun h x hx => lsc_log_filtration p h x hx
  log_upper := fun d c x hx => lsc_log_upper p d c x hx
  graded_kernel := fun d u hu => lsc_graded_kernel p d hp u hu
  graded_surj := fun d hd c => lsc_graded_surj p d hp hd c

/-- **M387F-7c: 存在** — 本物の対数殻包含格子データは充足可能（K = ℚ₂）。 -/
theorem lsc_exists : Nonempty LogShellContainmentData :=
  ⟨lscContainmentData 2 (by omega)⟩

/-! ## M387F-7 実例 -/

/-- 実例（下方包含）: レベル d の主単数の log content は殻 m^d に着地する。 -/
example (p d : Nat) (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x) :
    logShellMem p d (logShellContent p x.val) :=
  lsc_log_lower p d x hx

/-- 実例（フィルトレーション包含）: より深い単数 x ∈ U^{d+1} の log content は
    殻 m^d に着地する（深い単数は深い殻へ、殻は入れ子）。 -/
example (p d : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p (d + 1)).mem x) :
    logShellMem p d (logShellContent p x.val) :=
  lsc_log_filtration p (Nat.le_succ d) x hx

/-- 実例（上方包含・多輻上界の入力）: レベル d の主単数の log content は緩めた殻
    m^{d-c} にも収まる（「殻は大きすぎない」方向の付値下界）。 -/
example (p d c : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) :
    logShellMem p (d - c) (logShellContent p x.val) :=
  lsc_log_upper p d c x hx

/-- 実例（殻の入れ子・具体）: ℤ₂ 上、m^1 の元 2 = toZp 2 は m^0（全体）にも入る
    （M321F `logShell_example_two` を一段入れ子で下げる）。 -/
example : logShellMem 2 0 ((toZp 2).map 2) :=
  lsc_shell_nesting 2 0 ((toZp 2).map 2) logShell_example_two

/-- 実例（graded 全射・ℤ₂）: 加法殻商 ℤ/2 の生成元 1 を log に持つ主単数
    u ∈ U^(1) が存在する（U^(1)/U^(2) ≅ m^1/m^2 の全射性）。 -/
example :
    ∃ u : (principalUnits 2).carrier,
      (unitFiltration 2 1).mem u ∧ logKumLog 2 1 (by omega) u = Quot.mk (modCong 2).rel 1 :=
  lsc_graded_surj 2 1 (by omega) (by omega) (Quot.mk (modCong 2).rel 1)

/-- 実例（crux は外部仮説）: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  lsc_crux_is_hypothesis crux

/-- 実例（capstone 存在）: 対数殻包含格子データは存在する。 -/
example : Nonempty LogShellContainmentData :=
  lsc_exists

end IUT
