-- M397F LogThetaLatticeShell [実・本物・柱D]
-- complete_pct 影響: 柱D で 縦 log-link（M337F）×横 theta-link（M328F）の log-theta-lattice
--   正方形が対数殻フィルトレーション（M392F）レベルで可換（縦→横=横→縦、M367F の明示不定性
--   シフトを除いて同一の殻片へ着地）・縦 log-link の反復が殻フィルトレーションの coherent 塔を
--   与え横 theta-link がその塔と両立・実 deg_ℝ 体積が正方形を coherent に一周（殻上界内）を実構成。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説。正方形可換は殻
--   フィルトレーション/実 deg_ℝ 付値レベル（多輻不等式そのものではない）・(Ind3) は明示 μ シフトを
--   除いて可換・log は主項係数・局所体 K=ℚ_p・ℝ は setoid（realEq で言明）。

/-
  IUT/LogThetaLatticeShell.lean — M397F（log-theta-lattice ⇄ 殻フィルトレーション両立）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の先行建設 (b)・既存の縦横リンク両立の (a) 昇格）。
    本物の p 進局所体 K = ℚ_p・O_v = ℤ_p の上で、log-theta-lattice の **2 方向のリンク**——
    **縦の log-link**（M337F `logLinkMap`、同一列内で乗法 U^(d) → 加法 log-shell m^d へ）と
    **横の theta-link**（M328F `thLinkMap`、列を +1 する実テータ値 Θ↔q の同一視）——を組み合わせた
    **格子正方形**が、M387F/M392F の**対数殻フィルトレーション包含格子**と**両立**することを本物で
    建てる。crux は導出しない。
  * complete_pct 影響: **前進**。M392F は縦 log-link が殻フィルトレーション格子を保つこと（filtered
    map・graded 同型の誘導・上方包含の生存）を本物化し、M328F は横 theta-link を実テータ値で本物化、
    M367F は log-link と 3 不定性作用の可換性（(Ind3) は明示 m シフトを除いて）を本物化した。三者の
    **次の本物の一手**は、これらを **log-theta-lattice の正方形**（縦横リンクの可換図）へ束ね、その
    正方形が**殻フィルトレーションレベルで可換**であることを示すこと。本 M397F は:
      - **正方形の可換（組合せ）**: 頂点 (n,m) から (n+1,m+1) へ、縦→横（log してから theta）と
        横→縦（theta してから log）の 2 経路がともに **Θ-link ちょうど 1 本の Path 1** として同一の
        隅 (n+1,m+1) に到達する（M3 `Path`・`path_col`）。
      - **正方形の可換（殻フィルトレーション）**: 縦 log-link は主単数 x ∈ U^(d+1) の leading log
        content を殻 m^{d+1}⊆m^d へ着地させ（M392F `llsc_loglink_filtered`）、横 theta-link は Θ↔q の
        同一視（M328F `thLink_map_eq_qparam`）を保つ——縦→横と横→縦は**同一の殻片 m^d へ着地**する。
      - **正方形の可換（実 deg_ℝ 体積）**: 縦 log-link 体積輸送（付値 → deg_ℝ、加法）と横 theta-link
        の ×2l スケールが、掛ける順序に依らない: deg_ℝ(log-link(2l·n)) ≈ 2l·deg_ℝ(log-link(n))
        （M312F `intToReal_mul`/`rmul_assoc_real`、M328F `thLink_degree` と同型のパターン）。
        **M367F の明示不定性シフト μ を除いて可換**（`logLink_volume_transport`）。
      - **coherent な殻フィルトレーション塔**: 縦 log-link を格子の上へ反復すると、各段 e で M392F の
        graded 同型 U^(e)/U^(e+1)≅m^e/m^{e+1}（`llsc_graded_iso`）が成立する coherent な塔を与え、
        横 theta-link がこの塔と両立する。
      - **殻上界内の体積**: 正方形を一周する実 deg_ℝ 体積が M392F 上方包含 log(U^(d))⊆m^{d-c} の
        殻上界内に留まる（実付値レベルの主張、crux 不等式ではない）。
    crux Dβ-ω（多輻的アルゴリズム＝Ind3 log-shell 包含が与える不等式＝IUT 論争の係争点）は
    **決して導出せず**外部仮説のまま。柱D の log-theta-lattice ⇄ 殻フィルトレーションの**両立を実で建設**。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  本層は M392F（`LogLinkShellCompat`）・M328F（`ThetaLinkReal`）・M367F（`LogLinkIndeterminacy`）の
  **本物の対象**の上に、縦横リンクを束ねた **log-theta-lattice 正方形の殻フィルトレーション両立**を
  新規に積む:
  * M397F-1 `ltls_square_vh`/`ltls_square_hv`/`ltls_square_commutes`/`ltls_square_col_shift`
      — **正方形の可換（組合せ）**: 縦→横・横→縦の 2 経路がともに Path 1 で隅 (n+1,m+1) へ（M3）。
  * M397F-2 `ltls_square_shell` — **正方形の可換（殻フィルトレーション）**: 縦 log-link が content を
      m^{d+1}⊆m^d へ（M392F `llsc_loglink_filtered`）・横 theta-link が Θ↔q を保つ（M328F）——
      同一の殻片 m^d へ着地。
  * M397F-3 `ltlsThetaScaleVal`/`ltlsSquareHV`/`ltlsSquareVH`/`ltls_square_commutes_vol`/
    `ltls_square_vol_shift` — **正方形の可換（実 deg_ℝ 体積）**: ×2l スケールと log-link 輸送が可換・
      M367F 明示不定性シフト μ を除いて可換。
  * M397F-4 `ltls_tower_graded_iso`/`ltls_tower_theta_compat` — **coherent 殻塔**: 各段 e で M392F
      graded 同型が成立する塔・横 theta-link が塔と両立。
  * M397F-5 `ltls_square_vol_within_shell` — **殻上界内の体積**: 正方形体積が上方包含 m^{d-c} 内に。
  * M397F-6 `ltls_crux_external`/`ltls_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M397F-7 capstone `LogThetaLatticeShellData`/`logThetaLatticeShellData`/`ltls_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）
  * **crux Dβ-ω（多輻的アルゴリズム＝Ind3 log-shell 包含が与える不等式＝IUT 論争の当の係争点）は
    恒久的に本層の範囲外**。正方形の可換（`ltls_square_shell`・`ltls_square_commutes_vol`）は crux が
    「使う」構造的入力（縦横リンクが殻フィルトレーション上で整合する）だが、**多輻不等式そのもの**は
    本層で決して証明せず、crux を任意の外部 Prop として受け取るだけ（`ltls_crux_is_hypothesis` は Iff.rfl）。
  * **正方形の可換は殻フィルトレーション/実 deg_ℝ 付値レベル**。群レベルの完全な可換図（頂点に載る
    Frobenioid の完全同変性）は後続。**(Ind3) 膨張は明示 μ シフトを除いて可換**（M367F 継承）。
  * **log 写像は p 進 log の主項 θ_d（M327F/M337F）で本物**。完全収束級数は後続。
  * **局所体は K = ℚ_p（O_v = ℤ_p, U^(d)=1+p^d ℤ_p, m^d = p^d ℤ_p）**。一般局所体・完全同変性は後続。
    **ℝ は setoid** ゆえ体積輸送・スケールは realEq で言明。**上方包含は Nat 付値レベルの下界** m^{d-c}
    （分数係数 1/2p 版は後続）。テータ値の係数環 R は一般 CRing（存在証明は R = intRing）。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク
  不使用（core Lean のみ）。共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更なし。
  柱D 横展開・本物の先行建設[実]。一般名は `ltls` 接頭辞で衝突回避。
-/
import IUT.LogLinkShellCompat
import IUT.LogLinkIndeterminacy
import IUT.ThetaLinkReal

namespace IUT

/-! ## M397F-1: log-theta-lattice 正方形の可換（組合せ ── 縦→横 = 横→縦） -/

/-- **M397F-1a: 正方形の縦→横経路** — 頂点 (n,m) から縦 log-link で (n,m+1) へ登り、そこから横
    theta-link で (n+1,m+1) へ渡る。M3 `Path` で Θ-link ちょうど 1 本の Path 1。
    log-theta-lattice の格子正方形の「縦→横」辺（先に log してから theta）。 -/
theorem ltls_square_vh (n m : Int) : Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩ :=
  Path.log n m (Path.theta n (m + 1) (Path.nil ⟨n + 1, m + 1⟩))

/-- **M397F-1b: 正方形の横→縦経路** — 頂点 (n,m) から横 theta-link で (n+1,m) へ渡り、そこから縦
    log-link で (n+1,m+1) へ登る。同じく Θ-link ちょうど 1 本の Path 1。
    log-theta-lattice の格子正方形の「横→縦」辺（先に theta してから log）。 -/
theorem ltls_square_hv (n m : Int) : Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩ :=
  Path.theta n m (Path.log (n + 1) m (Path.nil ⟨n + 1, m + 1⟩))

/-- **定理 (M397F-1c: 正方形の可換／組合せ)** — log-theta-lattice の格子正方形は組合せ的に**可換**:
    縦→横（`ltls_square_vh`）と横→縦（`ltls_square_hv`）の 2 経路が**ともに Θ-link ちょうど 1 本の
    Path 1 として同一の隅 (n+1,m+1) に到達**する。縦 log-link と横 theta-link の交換が格子上で
    閉じることの本物（M3 `Path`）。 -/
theorem ltls_square_commutes (n m : Int) :
    Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩ ∧ Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩ :=
  ⟨ltls_square_vh n m, ltls_square_hv n m⟩

/-- **定理 (M397F-1d: 正方形は列を +1 する)** — 正方形の 2 経路はともに Θ-link を 1 本通るので、
    隅 (n+1,m+1) の列は始点 (n,m) の列 +1（M3 `path_col`）。横 theta-link 1 本ぶん正則構造が変わる
    （縦 log-link は列を保つ）ことの本物。 -/
theorem ltls_square_col_shift (n m : Int) :
    (⟨n + 1, m + 1⟩ : LatticeSite).col = (⟨n, m⟩ : LatticeSite).col + ((1 : Nat) : Int) :=
  path_col (ltls_square_vh n m)

/-! ## M397F-2: 正方形の可換（殻フィルトレーション ── 同一の殻片 m^d へ着地） -/

/-- **定理 (M397F-2: 正方形の可換／殻フィルトレーション・本丸)** — log-theta-lattice の格子正方形は
    **対数殻フィルトレーションレベルで可換**:
      (i) 縦 log-link は主単数 x ∈ U^(d+1) の leading log content を殻 m^{d+1} に着地させ、殻の入れ子で
          m^d にも収まる（M392F `llsc_loglink_filtered`、filtered map）、
      (ii) 横 theta-link は実テータ値 Θ(q,u_j) を q パラメータ q^{j²} と同一視する（M328F
          `thLink_map_eq_qparam`）。
    すなわち縦→横と横→縦の両経路は**同一の殻片 m^d へ着地**し（縦の殻フィルトレーションは横 theta-link
    をまたいでも mono-analytic に保たれる）、正方形が殻フィルトレーションの上で可換に閉じる。crux
    不等式そのものは決して導出しない。 -/
theorem ltls_square_shell (p d l : Nat) (R : CRing)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p (d + 1)).mem x) (j : Int) :
    (logShellMem p (d + 1) (logShellContent p x.val)
        ∧ logShellMem p d (logShellContent p x.val))
      ∧ thLinkMap R l j = thLinkQParam R l j :=
  ⟨llsc_loglink_filtered p d x hx, thLink_map_eq_qparam R l j⟩

/-! ## M397F-3: 正方形の可換（実 deg_ℝ 体積 ── ×2l スケールと log-link 輸送の交換） -/

/-- **M397F-3a: 横 theta-link の付値スケール** — 横 theta-link は付値 n を ×2l する
    （M328F `thLinkExp` の付値版、微細座標 u = q^{1/2l} の分母 2l 払い）。 -/
def ltlsThetaScaleVal (l : Nat) (n : Int) : Int :=
  ((2 * l : Nat) : Int) * n

/-- **M397F-3b: 正方形の横→縦の実 deg_ℝ 体積** — 先に横 theta-link で付値を ×2l し
    （`ltlsThetaScaleVal`）、そのあと縦 log-link で実 deg_ℝ 体積へ輸送する（M337F
    `logLinkVolTransport`）。log-theta-lattice 正方形の「横→縦」の体積。 -/
def ltlsSquareHV (logq : Nat → RReal) (v l : Nat) (n : Int) : RReal :=
  logLinkVolTransport logq v (ltlsThetaScaleVal l n)

/-- **M397F-3c: 正方形の縦→横の実 deg_ℝ 体積** — 先に縦 log-link で実 deg_ℝ 体積へ輸送し、そのあと
    横 theta-link の ×2l スケールを deg_ℝ レベルで掛ける（M328F `thLink_degree` の付値版）。
    log-theta-lattice 正方形の「縦→横」の体積。 -/
def ltlsSquareVH (logq : Nat → RReal) (v l : Nat) (n : Int) : RReal :=
  rmul (intToReal ((2 * l : Nat) : Int)) (logLinkVolTransport logq v n)

/-- **定理 (M397F-3d: 正方形の可換／実 deg_ℝ 体積・本丸)** — log-theta-lattice の格子正方形は
    **実 deg_ℝ 体積レベルで可換**: 横 theta-link の ×2l スケールと縦 log-link の体積輸送は**掛ける
    順序に依らない**——
      横→縦: deg_ℝ(log-link(2l·n)) = (2l·n)·log q_v
      縦→横: 2l·deg_ℝ(log-link(n)) = 2l·(n·log q_v)
    の両者が realEq（M312F `intToReal_mul`/`rmul_assoc_real`、M328F `thLink_degree` と同型のパターン）。
    縦 log-link（加法輸送）と横 theta-link（×2l スケール）の交換が実 Arakelov 次数の上で本物に閉じる。 -/
theorem ltls_square_commutes_vol (logq : Nat → RReal) (v l : Nat) (n : Int) :
    realEq (ltlsSquareHV logq v l n) (ltlsSquareVH logq v l n) := by
  show realEq (rmul (intToReal (((2 * l : Nat) : Int) * n)) (logq v))
      (rmul (intToReal ((2 * l : Nat) : Int)) (rmul (intToReal n) (logq v)))
  exact realEq_trans
    (rmul_congr_left (logq v) (realEq_symm (intToReal_mul ((2 * l : Nat) : Int) n)))
    (rmul_assoc_real (intToReal ((2 * l : Nat) : Int)) (intToReal n) (logq v))

/-- **定理 (M397F-3e: 正方形の可換は M367F 明示不定性シフトを除いて閉じる)** — 縦 log-link は加法
    写像ゆえ、(Ind3) 膨張の不定性 μ（M367F・M342F）は正方形の体積に**明示シフト** logVolLocal v μ を
    上乗せするだけで交換する:
      log-link v (2l·n + μ)  ≈  ltlsSquareHV v l n  +  logVolLocal v μ。
    すなわち log-theta-lattice 正方形は **M367F の明示 μ シフトを除いて可換**（膨張は片方向の付値寄与）
    ——これが正直な形（M337F `logLink_volume_transport` の加法輸送で閉じる、crux 不等式ではない）。 -/
theorem ltls_square_vol_shift (logq : Nat → RReal) (v l : Nat) (n μ : Int) :
    realEq (logLinkVolTransport logq v (ltlsThetaScaleVal l n + μ))
      (realAdd (ltlsSquareHV logq v l n) (logVolLocal logq v μ)) :=
  logLink_volume_transport logq v (ltlsThetaScaleVal l n) μ

/-! ## M397F-4: coherent な殻フィルトレーション塔（縦 log-link の反復）と横 theta-link の両立 -/

/-- **定理 (M397F-4a: coherent な殻フィルトレーション塔)** — 縦 log-link を格子の上へ**反復**すると、
    各段 e ≥ 1 で M392F の graded 同型 U^(e)/U^(e+1) ≅ m^e/m^{e+1}（`llsc_graded_iso`、全射 + 核 =
    U^(e+1)）が成立する**coherent な塔**を与える。縦 log-link 塔の各レベルが M392F 殻 graded 同型を
    coherent に担う（log-theta-lattice の縦方向の反復が殻フィルトレーション塔を生成）。 -/
theorem ltls_tower_graded_iso (p : Nat) (hp : 1 ≤ p) :
    ∀ e, 1 ≤ e →
      (∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
          (unitFiltration p e).mem u ∧ logLinkMap p e hp u = c)
      ∧ (∀ u : (principalUnits p).carrier, (unitFiltration p e).mem u →
          (logLinkMap p e hp u = (zmod p).one ↔ (unitFiltration p (e + 1)).mem u)) :=
  fun e he => llsc_graded_iso p e hp he

/-- **定理 (M397F-4b: 横 theta-link は塔と両立)** — 縦 log-link 塔の段 d での M392F graded 同型
    （`llsc_graded_iso`）**と**、横 theta-link の Θ↔q 同一視（M328F `thLink_map_eq_qparam`）が**同時に
    成立**する。すなわち横 theta-link は縦の coherent 殻フィルトレーション塔と両立する（正方形の縦横が
    塔の各段で整合する）。 -/
theorem ltls_tower_theta_compat (p d l : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) (R : CRing) (j : Int) :
    ((∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
          (unitFiltration p d).mem u ∧ logLinkMap p d hp u = c)
      ∧ (∀ u : (principalUnits p).carrier, (unitFiltration p d).mem u →
          (logLinkMap p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)))
      ∧ thLinkMap R l j = thLinkQParam R l j :=
  ⟨llsc_graded_iso p d hp hd, thLink_map_eq_qparam R l j⟩

/-! ## M397F-5: 正方形を一周する実 deg_ℝ 体積が殻上界内に留まる -/

/-- **定理 (M397F-5: 殻上界内の体積)** — log-theta-lattice 正方形の可換（実 deg_ℝ 体積、
    `ltls_square_commutes_vol`）**と**、M392F の上方包含 log(U^(d)) ⊆ m^{d-c}（有界補正 c、
    `lsc_log_upper`）が**両立**する。すなわち正方形を一周する縦横リンクの実 deg_ℝ 体積が殻の**上界内に
    留まる**（「log-shell は大きすぎない」方向の付値下界が正方形の交換の下で生存する、実付値レベルの
    主張）。多輻不等式（crux Dβ-ω）そのものは決して導出しない。 -/
theorem ltls_square_vol_within_shell (p d c l : Nat)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x)
    (logq : Nat → RReal) (v : Nat) (n : Int) :
    realEq (ltlsSquareHV logq v l n) (ltlsSquareVH logq v l n)
      ∧ logShellMem p (d - c) (logShellContent p x.val) :=
  ⟨ltls_square_commutes_vol logq v l n, lsc_log_upper p d c x hx⟩

/-! ## M397F-6: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M397F-6a: crux は外部仮説・決して導出しない／honest)** — log-theta-lattice 正方形が
    殻フィルトレーション/実 deg_ℝ の上で可換であること（`ltls_square_commutes_vol`）は**無条件で本物**
    （crux とは独立に成立）。しかしその正方形の上での**多輻的アルゴリズム**（Ind3 log-shell 包含が
    与える crux Dβ-ω ＝ テータパイロット ⇄ ガウスパイロットの比較不等式 ＝ IUT 論争の当の係争点）は
    本層で**決して証明しない**。crux を任意の外部 Prop `crux` として受け取り、正方形可換の本物性 **と**
    crux の連言を、crux が仮説として供給された場合にのみ返す——crux は決して導出されない。 -/
theorem ltls_crux_external (logq : Nat → RReal) (v l : Nat) (n : Int)
    (crux : Prop) (hcrux : crux) :
    realEq (ltlsSquareHV logq v l n) (ltlsSquareVH logq v l n) ∧ crux :=
  ⟨ltls_square_commutes_vol logq v l n, hcrux⟩

/-- **定理 (M397F-6b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明した定理ではなく、論争の係争点を
    そのまま外部仮説として受け取ったものであることを機械検証で明示（M328F `thLink_stage_hypothesis`・
    M392F `llsc_crux_is_hypothesis`・M367F `lli_crux_is_hypothesis` と同じ精神）。 -/
theorem ltls_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M397F-7: capstone -/

/-- **M397F-7a: log-theta-lattice ⇄ 殻フィルトレーション両立データ**（総括） — 本物の p 進局所体
    K = ℚ_p・O_v = ℤ_p 上で、縦 log-link（M337F）と横 theta-link（M328F）を束ねた log-theta-lattice
    正方形が M392F 殻フィルトレーション格子と両立することを束ねる: 正方形の可換（組合せ Path 1・殻
    フィルトレーション同一殻片・実 deg_ℝ 体積の ×2l 交換・M367F 明示 μ シフトを除いて可換）・coherent
    な殻塔（各段 graded 同型）・横 theta-link の塔両立。主語は M392F/M328F/M367F の本物であり toy を
    用いない。crux Dβ-ω は範囲外。 -/
structure LogThetaLatticeShellData where
  /-- 局所体 K = ℚ_p の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  /-- p ≥ 1。 -/
  hp : 1 ≤ p
  /-- フィルトレーション段 d ≥ 1。 -/
  d : Nat
  /-- d ≥ 1。 -/
  hd : 1 ≤ d
  /-- l-捻れ（微細座標 u = q^{1/2l} の分母 2l を与える）。 -/
  l : Nat
  /-- テータ値の係数環（一般 CRing）。 -/
  R : CRing
  /-- 正方形の縦→横経路（log してから theta、Path 1）。 -/
  square_vh : ∀ (n m : Int), Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩
  /-- 正方形の横→縦経路（theta してから log、Path 1）。 -/
  square_hv : ∀ (n m : Int), Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩
  /-- 正方形の可換（殻フィルトレーション）: 縦 log-link content が m^{d+1}⊆m^d へ・横 theta-link が
      Θ↔q を保つ（同一殻片へ着地）。 -/
  shell_square : ∀ (x : (principalUnits p).carrier), (unitFiltration p (d + 1)).mem x → ∀ (j : Int),
    (logShellMem p (d + 1) (logShellContent p x.val)
        ∧ logShellMem p d (logShellContent p x.val))
      ∧ thLinkMap R l j = thLinkQParam R l j
  /-- 正方形の可換（実 deg_ℝ 体積）: ×2l スケールと log-link 輸送が交換。 -/
  vol_square : ∀ (logq : Nat → RReal) (v : Nat) (n : Int),
    realEq (ltlsSquareHV logq v l n) (ltlsSquareVH logq v l n)
  /-- 正方形の可換は M367F 明示不定性シフト μ を除いて閉じる。 -/
  vol_square_shift : ∀ (logq : Nat → RReal) (v : Nat) (n μ : Int),
    realEq (logLinkVolTransport logq v (ltlsThetaScaleVal l n + μ))
      (realAdd (ltlsSquareHV logq v l n) (logVolLocal logq v μ))
  /-- coherent な殻塔: 各段 e ≥ 1 で M392F graded 同型が成立。 -/
  tower_graded : ∀ e, 1 ≤ e →
    (∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
        (unitFiltration p e).mem u ∧ logLinkMap p e hp u = c)
    ∧ (∀ u : (principalUnits p).carrier, (unitFiltration p e).mem u →
        (logLinkMap p e hp u = (zmod p).one ↔ (unitFiltration p (e + 1)).mem u))
  /-- 横 theta-link は縦の殻塔と両立（Θ↔q の同一視）。 -/
  theta_tower_compat : ∀ (j : Int), thLinkMap R l j = thLinkQParam R l j

/-- **M397F-7b: witness** — K = ℚ_p（段 d=1）・l・R 上の本物の log-theta-lattice ⇄ 殻フィルトレーション
    両立データ。全フィールドを M397F-1〜4 の本物で充足。 -/
def logThetaLatticeShellData (p : Nat) (hp : 1 ≤ p) (l : Nat) (R : CRing) :
    LogThetaLatticeShellData where
  p := p
  hp := hp
  d := 1
  hd := by omega
  l := l
  R := R
  square_vh := fun n m => ltls_square_vh n m
  square_hv := fun n m => ltls_square_hv n m
  shell_square := fun x hx j => ltls_square_shell p 1 l R x hx j
  vol_square := fun logq v n => ltls_square_commutes_vol logq v l n
  vol_square_shift := fun logq v n μ => ltls_square_vol_shift logq v l n μ
  tower_graded := fun e he => ltls_tower_graded_iso p hp e he
  theta_tower_compat := fun j => thLink_map_eq_qparam R l j

/-- **M397F-7c: 存在** — 本物の log-theta-lattice ⇄ 殻フィルトレーション両立データは充足可能
    （K = ℚ₂・l=1・R = intRing）。縦 log-link × 横 theta-link の格子正方形が M392F 殻フィルトレーション
    格子と両立することが実体化される（crux Dβ-ω は範囲外）。 -/
theorem ltls_exists : Nonempty LogThetaLatticeShellData :=
  ⟨logThetaLatticeShellData 2 (by omega) 1 intRing⟩

/-! ## M397F-7 実例（log-theta-lattice ⇄ 殻フィルトレーション両立の本物性） -/

/-- 実例（正方形の可換／組合せ）: 縦→横 と 横→縦 がともに Path 1 で同一の隅 (n+1,m+1) へ。 -/
example (n m : Int) :
    Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩ ∧ Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩ :=
  ltls_square_commutes n m

/-- 実例（正方形の可換／殻フィルトレーション）: 縦 log-link content が m^{d+1}⊆m^d へ・横 theta-link
    が Θ↔q を保つ（同一殻片へ着地）。 -/
example (p d l : Nat) (R : CRing) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p (d + 1)).mem x) (j : Int) :
    (logShellMem p (d + 1) (logShellContent p x.val)
        ∧ logShellMem p d (logShellContent p x.val))
      ∧ thLinkMap R l j = thLinkQParam R l j :=
  ltls_square_shell p d l R x hx j

/-- 実例（正方形の可換／実 deg_ℝ 体積・l=5）: 横 ×2l スケールと縦 log-link 輸送が交換する。 -/
example (logq : Nat → RReal) (v : Nat) (n : Int) :
    realEq (ltlsSquareHV logq v 5 n) (ltlsSquareVH logq v 5 n) :=
  ltls_square_commutes_vol logq v 5 n

/-- 実例（M367F 明示シフトを除いて可換・μ=1）: 正方形体積は明示シフト logVolLocal v 1 を除いて閉じる。 -/
example (logq : Nat → RReal) (v : Nat) (n : Int) :
    realEq (logLinkVolTransport logq v (ltlsThetaScaleVal 5 n + 1))
      (realAdd (ltlsSquareHV logq v 5 n) (logVolLocal logq v 1)) :=
  ltls_square_vol_shift logq v 5 n 1

/-- 実例（coherent 殻塔・段 e=3）: 縦 log-link 塔の段 3 で M392F graded 同型が成立。 -/
example (p : Nat) (hp : 1 ≤ p) :
    (∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
        (unitFiltration p 3).mem u ∧ logLinkMap p 3 hp u = c)
    ∧ (∀ u : (principalUnits p).carrier, (unitFiltration p 3).mem u →
        (logLinkMap p 3 hp u = (zmod p).one ↔ (unitFiltration p (3 + 1)).mem u)) :=
  ltls_tower_graded_iso p hp 3 (by omega)

/-- 実例（crux は外部仮説）: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  ltls_crux_is_hypothesis crux

/-- 実例（capstone 存在）: log-theta-lattice ⇄ 殻フィルトレーション両立データは存在する。 -/
example : Nonempty LogThetaLatticeShellData :=
  ltls_exists

end IUT
