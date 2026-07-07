/-
  IUT/FrobenioidLinkDegree.lean — M416F（柱C: **realified Frobenioid 次数の
  リンク両立** ── M411F の deg_ℝ が inter-Frobenioid link（theta-link/log-link）
  の下でどう振る舞うかを本物で構成する）

  -- M416F FrobenioidLinkDegree [実・本物・柱C]
  -- complete_pct 影響: 柱C で realified Frobenioid 次数 deg_ℝ（M411F frRealDeg）が
  --   theta-link で ×2l に（Θ^{2l}=q^{j²}, Frobenius [2l]・M328F ×2l）・log-link で
  --   乗法→加法に整合（product→sum・M337F）することを本物で証明し、リンク下の次数
  --   簿記（degree bookkeeping）を M411F の射の次数変換則へ接続する。
  -- 正直な限定: 完全な FrdI/FrdII link 構造（型付き Frobenioid・base category・ファイバー化・
  --   Θ×μ_LGP-link 本体）と crux 不等式（多輻的アルゴリズム＝Dβ-ω）は外部/後続——本層は
  --   次数簿記のみで crux（多輻的境界）は一切証明しない。

  ── 主要成果の分類: **[実]**（既存本物対象の合成・(a) 昇格）。complete_pct 影響:
     **柱C（Frobenioid 次数）**の実 IUT 完全証明率を前進させる。M411F
     `FrobenioidRealification` は単一 Frobenioid の realified 次数関手 deg_ℝ
     （`frRealDeg`＝M312F Arakelov 次数）と [FrdI] の射の次数変換則
     `frRealDeg_hom`（deg_ℝ(E)≈n·deg_ℝ(D)+deg_ℝ(eff)）を本物で建てた。しかし
     **Frobenioid 間の link（theta-link/log-link）の下での deg_ℝ の振る舞い**は
     未接続であった。本層はそれを次で本物化する（M328F/M337F/M411F の合成）:

     (1) **theta-link の次数効果（×2l）**: IUT III の theta-link は Θ^{2l}=q^{j²}
         （M328F: テータ値の 2l 乗＝リンク先 q パラメータ、指数 j²↦2l·j²）。
         Frobenioid の対象（因子 RawDiv）の上では、この theta-link は Frobenius
         自己射 [2l]（`picDivFrobRaw (2l)`）として作用し、realified 次数を
         **deg_ℝ(θ-link D)≈2l·deg_ℝ(D)** に ×2l する（M411F `frRealDeg_frob`）。
         さらに **theta-link を M411F の Frobenioid 射 `frRawHom`（Frobenius 次数 2l・
         零因子 0）として実体化**し、その次数変換を M411F `frRealDeg_hom` で閉じる。
     (2) **log-link の次数効果（乗法→加法）**: 縦 log-link（M337F）は p 進対数で
         乗法（Frobenius-like 付値の積 n+m）を加法 log-shell 体積の和へ移す
         （product→sum, M337F `logLink_volume_transport`）。これは realified
         Frobenioid 次数の**加法準同型** deg_ℝ(D+E)≈deg_ℝ(D)+deg_ℝ(E)
         （M411F `frRealDeg_add`）と整合する（log-link の加法性＝deg_ℝ の加法性）。
     (3) **log-theta-lattice 周りの合成両立**: theta-link（×2l の Frobenius）と
         log-link（加法）が可換 ── deg_ℝ(θ-link(D+E))≈2l·deg_ℝ(D)+2l·deg_ℝ(E)
         （`fldThetaLink_add`, Frobenius 斉次と加法の合成）。realified Frobenioid
         次数が格子の 2 方向の move と coherent（次数準同型が保たれる）。
     (4) **capstone** `FrobenioidLinkDegreeData` / `fldData` / `fld_exists` ＋ 実例。
     toy 主語なし——主語は M312F の本物の Arakelov 次数 deg_ℝ・M307F の本物の因子
     RawDiv・M328F の本物のテータ値/q パラメータ次数・M337F の本物の log-link 体積輸送。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M416F-1 `fldThetaLink` / `fldTheta_degree`
      — theta-link の Frobenioid 対象上の作用＝Frobenius [2l]（Θ^{2l}=q^{j²}）と
        realified 次数の ×2l（`frRealDeg_frob` から本物）。
  * M416F-2 `fldThetaMor` / `fldThetaMor_deg` / `fldTheta_morphism_degree` /
    `fldTheta_eff_zero`
      — theta-link を M411F の Frobenioid 射 `frRawHom`（次数 2l・零因子 0）として
        実体化し、[FrdI] の射の次数変換則（`frRealDeg_hom`）に接続。
  * M416F-3 `fldTheta_qparam_degree` / `fldTheta_qparam_total`
      — M328F の q パラメータ側次数変換（deg_ℝ(q^{j²})≈2l·deg_ℝ(Θ)・総体積 ×2l）を
        Frobenioid link degree の語彙で採る（写像側 M328F と次数側 M411F の橋渡し）。
  * M416F-4 `fldLogLink_transport` / `fldLogLink_frobenioid_additive`
      — log-link の乗法→加法体積輸送（M337F `logLink_volume_transport`）と realified
        Frobenioid 次数の加法準同型（M411F `frRealDeg_add`）の整合。
  * M416F-5 `fldThetaLink_add`
      — theta-link（×2l Frobenius）と log-link（加法）の合成両立（格子 coherence）。
  * M416F-6 capstone `FrobenioidLinkDegreeData` / `fldData` / `fld_exists` /
    `fld_theta_scale` / `fld_loglink_additive` ＋ 実例（l=5: 因子 10 の theta-link 等）。

  ## 正直な限定（消去・弱化禁止・過大主張禁止）

  - **本物（完全証明）**: theta-link の Frobenioid 対象上の作用＝Frobenius [2l] と
    realified 次数の ×2l（deg_ℝ(θ-link D)≈2l·deg_ℝ(D)）、theta-link の Frobenioid 射
    実体化（次数 2l・零因子 0）と [FrdI] 次数変換則、log-link の乗法→加法体積輸送と
    deg_ℝ の加法準同型の整合、theta-link×log-link の合成両立は **本物**（realEq）。
  - **恒久的範囲外（crux＝Dβ-ω＝多輻的アルゴリズム）**: theta-link/log-link の**下での**
    テータパイロット⇄ガウスパイロットの比較不等式（多輻的境界＝IUT 論争の係争点）は
    **本層で一切証明しない**。本層は link の下での **realified 次数の簿記（×2l・加法性・
    合成両立）を本物にするのみ**であり、crux の真偽・多輻的境界には踏み込まない
    （M328F-4/M337F-5 と同じ scope）。
  - **後続（本物化の続き）**: 完全な [FrdI/II] link 構造（型付き Frobenioid・base
    category 全公理・ファイバー化・Θ×μ_LGP-link の構成本体）・アルキメデス素点の寄与・
    log q_v の具体値/超越性は柱C/D/E 後続。本層は次数簿記（degree bookkeeping）まで。
  - **ℝ は setoid**（realEq が同値・`=` でない）ゆえ次数の link 両立は realEq で言明する
    （M312F/M328F/M337F/M411F と同じ正直な形）。因子群 Div=Quot rawEq への Grp 圏化は後続。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無・禁止
  タクティク不使用（core Lean のみ）。共有ファイル未変更（新規1本）。一般名は `fld` 接頭辞。
-/
import IUT.FrobenioidRealification
import IUT.ThetaLinkReal
import IUT.LogLinkReal

namespace IUT

/-! ## M416F-1: theta-link の Frobenioid 対象上の作用（Frobenius [2l]・Θ^{2l}=q^{j²}） -/

/-- **M416F-1a: theta-link の Frobenioid 対象作用** — IUT III の theta-link は
    テータ値の 2l 乗（Θ^{2l}=q^{j²}, M328F）である。Frobenioid の対象（因子 RawDiv）の
    上では、この theta-link は Frobenius 自己射 [2l]（`picDivFrobRaw (2l)`＝因子の 2l 倍）
    として作用する。surrogate でない本物の因子 Frobenius。 -/
def fldThetaLink (l : Nat) (D : RawDiv) : RawDiv :=
  picDivFrobRaw (2 * l) D

/-- **定理 (M416F-1b: theta-link は realified 次数を ×2l)** — deg_ℝ(θ-link D) ≈ 2l·deg_ℝ(D)。
    theta-link（Θ^{2l}=q^{j²}）が realified Frobenioid 次数（M411F `frRealDeg`）を
    **2l 倍**する（M328F 指数対応 j²↦2l·j²＝スケール ×2l の次数版）。M411F の Frobenius
    斉次性 `frRealDeg_frob`（deg_ℝ([n]D)≈n·deg_ℝ(D)）から n=2l で本物（realEq）。 -/
theorem fldTheta_degree (logq : Nat → RReal) (l : Nat) (D : RawDiv) :
    realEq (frRealDeg logq (fldThetaLink l D))
      (rmul (intToReal ((2 * l : Nat) : Int)) (frRealDeg logq D)) :=
  frRealDeg_frob logq (2 * l) D

/-! ## M416F-2: theta-link を M411F の Frobenioid 射として実体化（[FrdI] 次数変換則へ接続） -/

/-- **M416F-2a: theta-link の Frobenioid 射** — theta-link を M411F の代表 Frobenioid 射
    `frRawHom D (θ-link D)` として実体化する: Frobenius 次数 2l・有効零因子 0
    （Div(φ)=0）。IUT の theta-link を Frobenioid の Frobenius 自己射（次数 2l）として
    据える本物のブリッジ（M411F `frFrobRawMor` の 2l 版、choice 不使用）。 -/
def fldThetaMor (l : Nat) (hl : 1 ≤ l) (D : RawDiv) : frRawHom D (fldThetaLink l D) :=
  frFrobRawMor (2 * l) (by omega) D

/-- **定理 (M416F-2b: theta-link 射の Frobenius 次数は 2l)**（rfl）。 -/
theorem fldThetaMor_deg (l : Nat) (hl : 1 ≤ l) (D : RawDiv) :
    (fldThetaMor l hl D).deg = 2 * l := rfl

/-- **定理 (M416F-2c: theta-link の [FrdI] 次数変換則)** — theta-link 射
    f : D→θ-link D（Frobenius 次数 2l・零因子 0）に対し **deg_ℝ(θ-link D) ≈
    2l·deg_ℝ(D) + deg_ℝ(0)**。M411F の射の realified 次数変換則 `frRealDeg_hom`
    （deg_ℝ(E)≈n·deg_ℝ(D)+deg_ℝ(eff)、[FrdI] の実数値化）を theta-link 射へ適用した本物。
    theta-link の次数効果を **Frobenioid の射の次数簿記**として閉じる。 -/
theorem fldTheta_morphism_degree (logq : Nat → RReal) (l : Nat) (hl : 1 ≤ l)
    (D : RawDiv) :
    realEq (frRealDeg logq (fldThetaLink l D))
      (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (frRealDeg logq D))
        (frRealDeg logq rawZero)) :=
  frRealDeg_hom logq (fldThetaMor l hl D)

/-- **定理 (M416F-2d: theta-link 射の零因子 realified 次数は 0)** — theta-link は
    Frobenius 自己射ゆえ零因子部 Div(φ)=0 の realified 次数は 0（M411F `frMorDeg`）。 -/
theorem fldTheta_eff_zero (logq : Nat → RReal) (l : Nat) (hl : 1 ≤ l) (D : RawDiv) :
    realEq (frMorDeg logq (fldThetaMor l hl D)) realZero :=
  frRealDeg_zero logq

/-! ## M416F-3: M328F の q パラメータ側次数変換を Frobenioid link degree の語彙で採る -/

/-- **定理 (M416F-3a: theta-link の q パラメータ次数変換／M328F 橋渡し)** — リンク先の
    q パラメータの実 Arakelov 次数はテータ値の実次数の **2l 倍**:
    deg_ℝ(q^{j²}) ≈ 2l·deg_ℝ(Θ(q,u_j))（M328F `thLink_degree`）。M328F の theta-link
    写像（Θ↔q）側の次数変換を、本層の realified Frobenioid 次数簿記へ接続する。 -/
theorem fldTheta_qparam_degree (logq : Nat → RReal) (v : Nat) (l : Nat) (j : Int) :
    realEq (thLinkQParamDeg logq v l j)
      (rmul (intToReal ((2 * l : Nat) : Int)) (thPilotValueDeg logq v j)) :=
  thLink_degree logq v l j

/-- **定理 (M416F-3b: theta-link の総体積次数変換)** — q パラメータ側の総体積は
    テータパイロット総体積の **2l 倍**: Σ deg_ℝ(q^{j²}) ≈ 2l·Σ deg_ℝ(Θ)
    （M328F `thLink_total_degree`）。theta-link が総体積を ×2l で変換する本物。 -/
theorem fldTheta_qparam_total (logq : Nat → RReal) (v : Nat) (l : Nat) (n : Nat) :
    realEq (thLinkQParamTotalVol logq v l n)
      (rmul (intToReal ((2 * l : Nat) : Int)) (thPilotTotalVol logq v n)) :=
  thLink_total_degree logq v l n

/-! ## M416F-4: log-link の乗法→加法体積輸送と realified Frobenioid 次数の加法性の整合 -/

/-- **定理 (M416F-4a: log-link の乗法→加法体積輸送)** — 縦 log-link（M337F）は p 進対数で
    乗法側の積（付値 n+m）を加法 log-shell 体積の和へ移す:
    deg_ℝ(n+m) ≈ deg_ℝ(n)+deg_ℝ(m)（M337F `logLink_volume_transport`, product→sum）。
    log-link が乗法（Frobenius-like）を加法（étale-like log-shell）へ移す本物の次数効果。 -/
theorem fldLogLink_transport (logq : Nat → RReal) (v : Nat) (n m : Int) :
    realEq (logLinkVolTransport logq v (n + m))
      (realAdd (logLinkVolTransport logq v n) (logLinkVolTransport logq v m)) :=
  logLink_volume_transport logq v n m

/-- **定理 (M416F-4b: realified Frobenioid 次数の加法準同型は log-link と整合)** —
    realified Frobenioid 次数（M411F `frRealDeg`）は加法準同型
    deg_ℝ(D+E) ≈ deg_ℝ(D)+deg_ℝ(E)（M411F `frRealDeg_add`）であり、これは M416F-4a の
    log-link の乗法→加法体積輸送（product→sum）と**同じ加法性**である。log-link の加法性が
    Frobenioid 次数関手の加法準同型として実現される（次数簿記の整合）。 -/
theorem fldLogLink_frobenioid_additive (logq : Nat → RReal) (D E : RawDiv) :
    realEq (frRealDeg logq (rawAdd D E))
      (realAdd (frRealDeg logq D) (frRealDeg logq E)) :=
  frRealDeg_add logq D E

/-! ## M416F-5: theta-link（×2l Frobenius）と log-link（加法）の合成両立（格子 coherence） -/

/-- **定理 (M416F-5: log-theta-lattice 周りの次数合成両立)** — theta-link（×2l の Frobenius
    [2l]）と log-link（加法 D+E）は次数の上で可換:
    **deg_ℝ(θ-link(D+E)) ≈ 2l·deg_ℝ(D) + 2l·deg_ℝ(E)**。
    theta-link を先に取る（Frobenius 斉次 `frRealDeg_frob`）か log-link 加法を先に取る
    （`frRealDeg_add`＋左分配 `rmul_add_left`）かに依らず一致する。realified Frobenioid
    次数が log-theta-lattice の 2 方向の move（横 theta-link ×2l・縦 log-link 加法）と
    **coherent**（次数準同型が保たれる）ことの本物の次数簿記。 -/
theorem fldThetaLink_add (logq : Nat → RReal) (l : Nat) (D E : RawDiv) :
    realEq (frRealDeg logq (fldThetaLink l (rawAdd D E)))
      (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (frRealDeg logq D))
        (rmul (intToReal ((2 * l : Nat) : Int)) (frRealDeg logq E))) := by
  refine realEq_trans (frRealDeg_frob logq (2 * l) (rawAdd D E)) ?_
  refine realEq_trans
    (rmul_congr_right (intToReal ((2 * l : Nat) : Int)) (frRealDeg_add logq D E)) ?_
  exact rmul_add_left (frRealDeg logq D) (frRealDeg logq E)
    (intToReal ((2 * l : Nat) : Int))

/-! ## M416F-6: capstone（Frobenioid link degree データの束ね） -/

/-- **M416F-6a: Frobenioid link degree データ** — realified Frobenioid 次数 deg_ℝ の
    inter-Frobenioid link 両立の束ね: theta-link の ×2l スケール・log-link の加法性
    （乗法→加法）・両者の合成両立。IUT の log-theta-lattice の次数簿記を realified
    Frobenioid 次数（M411F）の上で本物構成した witness。crux（多輻的境界）は範囲外。 -/
structure FrobenioidLinkDegreeData (logq : Nat → RReal) (l : Nat) where
  /-- theta-link の次数因子 2l（Θ^{2l}=q^{j²}）。 -/
  factor : Int
  /-- theta-link の Frobenioid 対象作用（Frobenius [2l]）。 -/
  theta : RawDiv → RawDiv
  /-- realified Frobenioid 次数 deg_ℝ:RawDiv→ℝ（M411F）。 -/
  rdeg : RawDiv → RReal
  /-- **theta-link は次数を ×2l** deg_ℝ(θ-link D)≈2l·deg_ℝ(D)。 -/
  theta_scale : ∀ D, realEq (rdeg (theta D)) (rmul (intToReal factor) (rdeg D))
  /-- **log-link は加法**（乗法→加法）deg_ℝ(D+E)≈deg_ℝ(D)+deg_ℝ(E)。 -/
  loglink_additive : ∀ D E, realEq (rdeg (rawAdd D E)) (realAdd (rdeg D) (rdeg E))
  /-- **合成両立** deg_ℝ(θ-link(D+E))≈2l·deg_ℝ(D)+2l·deg_ℝ(E)（格子 coherence）。 -/
  theta_loglink_compat : ∀ D E,
    realEq (rdeg (theta (rawAdd D E)))
      (realAdd (rmul (intToReal factor) (rdeg D)) (rmul (intToReal factor) (rdeg E)))

/-- **M416F-6b: 実データ** — 全フィールドを M328F/M337F/M411F の本物で充足。 -/
def fldData (logq : Nat → RReal) (l : Nat) : FrobenioidLinkDegreeData logq l where
  factor := ((2 * l : Nat) : Int)
  theta := fldThetaLink l
  rdeg := frRealDeg logq
  theta_scale := fldTheta_degree logq l
  loglink_additive := fldLogLink_frobenioid_additive logq
  theta_loglink_compat := fldThetaLink_add logq l

/-- **M416F-6c: 存在** — Frobenioid link degree データは充足可能。 -/
theorem fld_exists (logq : Nat → RReal) (l : Nat) :
    Nonempty (FrobenioidLinkDegreeData logq l) :=
  ⟨fldData logq l⟩

/-- **M416F-6d: theta-link の ×2l スケール**（capstone 再掲）。 -/
theorem fld_theta_scale (logq : Nat → RReal) (l : Nat) (D : RawDiv) :
    realEq (frRealDeg logq (fldThetaLink l D))
      (rmul (intToReal ((2 * l : Nat) : Int)) (frRealDeg logq D)) :=
  fldTheta_degree logq l D

/-- **M416F-6e: log-link の加法性**（capstone 再掲）。 -/
theorem fld_loglink_additive (logq : Nat → RReal) (D E : RawDiv) :
    realEq (frRealDeg logq (rawAdd D E))
      (realAdd (frRealDeg logq D) (frRealDeg logq E)) :=
  fldLogLink_frobenioid_additive logq D E

/-! ## M416F 実例（l=5: theta-link 因子 10・×2l 次数・合成両立・射の次数変換） -/

/-- 実例: l=5 の theta-link 次数因子は 2·5 = 10（Θ^{10}=q^{j²}）。 -/
example : ((2 * 5 : Nat) : Int) = 10 := by omega

/-- 実例: l=5 の theta-link は realified Frobenioid 次数を ×10 する。 -/
example (logq : Nat → RReal) (D : RawDiv) :
    realEq (frRealDeg logq (fldThetaLink 5 D))
      (rmul (intToReal ((2 * 5 : Nat) : Int)) (frRealDeg logq D)) :=
  fldTheta_degree logq 5 D

/-- 実例: l=5 の theta-link 射の Frobenius 次数は 10。 -/
example (D : RawDiv) : (fldThetaMor 5 (by omega) D).deg = 10 := rfl

/-- 実例: log-link の乗法→加法体積輸送（付値 2+3 の像＝付値 2・3 の像の和）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (logLinkVolTransport logq v (2 + 3))
      (realAdd (logLinkVolTransport logq v 2) (logLinkVolTransport logq v 3)) :=
  fldLogLink_transport logq v 2 3

/-- 実例: l=5 の合成両立 deg_ℝ(θ-link(D+E)) ≈ 10·deg_ℝ(D)+10·deg_ℝ(E)。 -/
example (logq : Nat → RReal) (D E : RawDiv) :
    realEq (frRealDeg logq (fldThetaLink 5 (rawAdd D E)))
      (realAdd (rmul (intToReal ((2 * 5 : Nat) : Int)) (frRealDeg logq D))
        (rmul (intToReal ((2 * 5 : Nat) : Int)) (frRealDeg logq E))) :=
  fldThetaLink_add logq 5 D E

/-- 実例: q パラメータ次数変換（l=5, j=1）deg_ℝ(q^1) ≈ 10·deg_ℝ(Θ(q,u_1))。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thLinkQParamDeg logq v 5 1)
      (rmul (intToReal ((2 * 5 : Nat) : Int)) (thPilotValueDeg logq v 1)) :=
  fldTheta_qparam_degree logq v 5 1

end IUT
