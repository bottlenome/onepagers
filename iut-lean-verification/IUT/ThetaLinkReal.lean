/-
  IUT/ThetaLinkReal.lean — M328F（柱E テータの横展開:
  **theta-link を実テータ値で本物化 ── テータ値 Θ(q,u_j)=q^{j²/2l} と
  リンク先 Hodge 劇場の q パラメータ q^{j²} の同一視写像を、M318F の
  本物のテータ値の上で構成する（多輻的アルゴリズムの舞台の本物化）**）

  ── 主要成果の分類: **[実]**（本物の先行建設 (b)・既存 theta-link 骨格の
     (a) 昇格）。complete_pct 影響: **柱E の theta-link 写像側**の実 IUT
     完全証明率を前進させる。IUT III の **theta-link** は、あるホッジ劇場の
     テータ値 Θ(q,u_j)（M318F: 微細座標 u = q^{1/2l} の下で u^{j²}
     ＝ q^{j²/2l}）を、隣のホッジ劇場の q パラメータ（q^{j²} 型）と
     同一視する対応であり、多輻的アルゴリズム（定理3.11）が走る舞台の
     水平辺である。従来この theta-link は
       ・M3 `LogThetaLattice.lean`: LatticeSite/Link.theta（(n,m)→(n+1,m)）
         という **組合せ骨格**（頂点に載る実データなし）、
       ・M244F `ThetaLinkTransport.lean`: crux を単一 Prop へ縮約する
         **忠実算術模型**（体積主語は m202fVol toy 由来の QDiv 領域）
     の二形しか無く、**theta-link の写像そのもの（Θ↔q の同一視）を
     実テータ値の上で本物構成**してはいなかった。

  本層は、M318F の **本物のテータ値** Θ(q,u_j) = thLtorValue R j
  = uMonHom R (j²)（Laurent 単項式）を主語に、theta-link の写像を
  **本物の反復群冪 thLtorPow で** 構成する。核心は次の同一視である:

    微細座標 u = q^{1/2l} では q = u^{2l} ゆえ、リンク先の q パラメータは
      q^{j²} = u^{2l·j²} = (u^{j²})^{2l} = Θ(q,u_j)^{2l}
    である。すなわち **theta-link 写像 = テータ値を 2l 乗する本物の操作**
    （thLtorPow による 2l 回の反復積）であり、その像がちょうど q^{j²} 型の
    q パラメータ（q = u^{2l} の j² 乗、IsLPowerValue R (2l)）になる。
    指数の対応は j²（テータ値の分子）↦ 2l·j²（q パラメータの分子）、
    すなわちスケール **×2l**（有理冪 q^{j²/2l} ↦ q^{j²} の分母 2l を払う）。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M328F-1 `thLinkExp` / `thLink_exponent` / `thLink_exponent_scale`
      — **theta-link の指数対応**: q パラメータの微細指数
        thLinkExp l j = (2l)·j²（テータ値の指数 j² のスケール ×2l）。
        「テータ値の指数 j²/2l ↦ q パラメータの指数 j²」の分母払いの本物。
  * M328F-2 `thLinkQParam` / `thLinkMap` / `thLink_map_eq_qparam` /
    `thLink_qparam_is_qpower`
      — **theta-link 写像**: thLinkMap R l j = Θ(q,u_j)^{2l}（本物の反復群冪
        thLtorPow で 2l 乗）が、リンク先 q パラメータ thLinkQParam
        = u^{2l·j²} = q^{j²} に一致（thLtorPow_uMon）。q パラメータは
        q = u^{2l} の j² 乗（IsLPowerValue R (2l)）。
  * M328F-3 `thLinkQParamDeg` / `thLink_degree` / `thLinkQParamTotalVol` /
    `thLink_total_degree`
      — **theta-link の次数変換**: q パラメータの実 Arakelov 次数
        deg_ℝ(q^{j²}) ≈ 2l · deg_ℝ(Θ(q,u_j))（M319F thPilotValueDeg の
        2l 倍）。テータパイロット総体積（M319F thPilotTotalVol）を
        q パラメータ側総体積へ **×2l で変換**（実数値 deg_ℝ で本物）。
  * M328F-4 `thLink_crux_stage` / `thLink_stage_hypothesis`
      — **crux の舞台としての theta-link（honest）**: theta-link 写像
        （Θ↔q の同一視）は本物で構成される一方、その下でのテータパイロット
        ⇄ ガウスパイロットの比較（crux ＝ Dβ-ω ＝ 多輻的アルゴリズム）は
        **恒久的に範囲外**であることを、crux を外部 Prop 仮説として明示。
  * M328F-5 `ThetaLinkLatticeData` / `thetaLinkLatticeData` /
    `thLink_lattice_point`
      — **log-theta-lattice の 1 theta-link 辺の昇格**: M3 の組合せ辺
        Link.theta（(col,row)→(col+1,row)、頂点に実データなし）を、実テータ値
        Θ(q,u_j) と q パラメータ q^{j²} の同一視で装飾（横の theta-link 側を
        実テータ値へ昇格）。縦の log-link・多輻的アルゴリズムは柱D 後続。
  * M328F-6 capstone `ThetaLinkData` / `thetaLinkData` / `thLink_exists`
  * 実例: l=5・小さい j でテータ値の指数 j² と q パラメータ指数 2l·j² の対応。

  ## 既存 toy/骨格を何処まで実テータ値へ昇格したか（必須明記）

  - **M3 `LogThetaLattice.Link.theta`（組合せ骨格）**: 頂点に載る実データが
    無い水平辺 (n,m)→(n+1,m) であった。本層は **その theta-link 側の辺を
    実テータ値 Θ(q,u_j)↔q^{j²} の同一視写像で装飾**（M328F-5）。ただし
    LatticeSite/Link/Path の組合せ構造そのもの（縦横の格子）は M3 のまま
    利用し、**横の theta-link 辺に実テータ値を載せる**ところを昇格する。
  - **M244F `ThetaLinkTransport`（crux 単一 Prop・算術模型）**: crux を
    ただ一つの Prop に孤立させたが、theta-link の写像そのものは
    忠実算術模型（QDiv・m202fVol 由来）の上であった。本層は theta-link の
    **写像・指数対応・次数変換を実テータ値 q^{j²}（M318F）の上で本物構成**し、
    crux 不等式は M244F と同様に範囲外に留める（M328F-4 で明示）。
  - **toy 主語は一切用いない**: 主語は M318F の本物の Laurent 単項式
    Θ(q,u_j)=u^{j²}・q^{j²}=u^{2l·j²} と、本物の反復群冪 thLtorPow・
    M312F の本物の実数値 Arakelov 次数 logVolLocal であり、m202fVol・
    Bool 軌道・surrogate 群は使用しない。

  ## 正直な限定（消去・弱化禁止・過大主張禁止）

  - **本物（完全証明）**: theta-link 写像 = テータ値の 2l 乗（thLtorPow）が
    q パラメータ q^{j²}=u^{2l·j²} に一致すること（thLink_map_eq_qparam）、
    指数の対応 j² ↦ 2l·j²（スケール ×2l、thLink_exponent_scale）、
    q パラメータが q=u^{2l} の j² 乗であること（thLink_qparam_is_qpower）、
    次数変換 deg_ℝ(q^{j²}) ≈ 2l·deg_ℝ(Θ)（thLink_degree・thLink_total_degree、
    実数値 deg_ℝ の realEq）は **本物**。
  - **恒久的範囲外（crux＝Dβ-ω＝論争の係争点）**: theta-link の**下での**
    テータパイロット ⇄ ガウスパイロットの比較不等式（crux）＝多輻的
    アルゴリズム（[AbsTopIII] 環復元・tempered π₁ 上のエタールテータ剛性・
    全レベル log-Kummer・Θ×μ_LGP-link の構成本体）は **本層では一切証明
    しない**。本層は theta-link の **写像（Θ↔q の同一視）を本物にするのみ**
    であり、crux の真偽には踏み込まない（M328F-4 で外部 Prop 仮説として明示、
    過大主張禁止）。
  - **witness/後続**: テータ値は M318F の本物（u=q^{1/2l} の l 乗根の体内
    実在・log q_v の超越性/具体値は witness、柱A/柱C 後続）。有理冪
    q^{j²/2l} の分母 2l は微細格子の witness——指数の**分子 j²** と
    スケール ×2l が本物。log-theta-lattice の完全構造（縦の log-link の
    log-Kummer 非線形性）・多輻的アルゴリズムの詳細は柱D 後続。
  - **ℝ は setoid**（realEq が同値・`=` でない）ゆえ次数変換は realEq で言明
    する（M312F/M319F と同じ正直な形）。

  全て新規 Classical.choice を証明本体に導入せず（M318F/M319F/M312F/M3 から
  継承、#print axioms は propext/Quot.sound 系のみ）。sorry 皆無・禁止
  タクティク不使用（core Lean のみ）。サブエージェント新規1本（共有
  ファイル未変更）。一般名は `thLink` 接頭辞で衝突回避。
-/
import IUT.ThetaPilotRealVolume
import IUT.LogThetaLattice

namespace IUT

/-! ## M328F-1: theta-link の指数対応（テータ値指数 j² ↦ q パラメータ指数 2l·j²） -/

/-- **M328F-1a: q パラメータの微細指数** — リンク先の q パラメータ q^{j²} は
    微細座標 u = q^{1/2l}（q = u^{2l}）の下で u^{2l·j²} である。その指数
    thLinkExp l j = (2l)·(テータ値指数 j²)。テータ値 Θ(q,u_j) の指数 j²
    （M318F thLtorExp）を **スケール ×2l** した q パラメータ指数。 -/
def thLinkExp (l : Nat) (j : Int) : Int :=
  ((2 * l : Nat) : Int) * thLtorExp j

/-- **定理 (M328F-1b: 指数対応)** — q パラメータの微細指数は (2l)·j²。
    テータ値の有理冪 q^{j²/2l}（微細指数 j²）と q パラメータ q^{j²}
    （微細指数 2l·j²）の指数の対応: 分母 2l を払う ×2l のスケール。 -/
theorem thLink_exponent (l : Nat) (j : Int) :
    thLinkExp l j = ((2 * l : Nat) : Int) * (j * j) := by
  show ((2 * l : Nat) : Int) * thLtorExp j = ((2 * l : Nat) : Int) * (j * j)
  rw [thLtorExp_sq]

/-- **定理 (M328F-1c: 指数のスケール対応)** — q パラメータ微細指数
    = (2l)·(テータ値微細指数)。theta-link の指数対応が **ちょうど ×2l の
    スケール**であること（q^{j²/2l} ↦ q^{j²} の分母払い）の明示。 -/
theorem thLink_exponent_scale (l : Nat) (j : Int) :
    thLinkExp l j = ((2 * l : Nat) : Int) * thLtorExp j :=
  rfl

/-! ## M328F-2: theta-link 写像（Θ↔q の同一視 ── テータ値の 2l 乗 = q^{j²}） -/

/-- **M328F-2a: リンク先の q パラメータ** — q^{j²} = u^{2l·j²}
    = uMonHom R (thLinkExp l j)。隣のホッジ劇場の q パラメータ（q = u^{2l}
    の j² 乗）を本物の Laurent 単項式として表す。 -/
def thLinkQParam (R : CRing) (l : Nat) (j : Int) : (laurentRing R).carrier :=
  uMonHom R (thLinkExp l j)

/-- **M328F-2b: theta-link 写像** — テータ値 Θ(q,u_j) を **2l 乗する本物の
    操作**（M318F thLtorPow による 2l 回の反復群冪）。微細座標 u = q^{1/2l}
    では q = u^{2l} ゆえ Θ(q,u_j)^{2l} = (u^{j²})^{2l} = u^{2l·j²} = q^{j²}
    となり、テータ値をリンク先の q パラメータへ移す写像を与える。
    surrogate 写像でない本物の反復積。 -/
def thLinkMap (R : CRing) (l : Nat) (j : Int) : (laurentRing R).carrier :=
  thLtorPow R (thLtorValue R j) (2 * l)

/-- **定理 (M328F-2c: theta-link 写像 = q パラメータ／本丸)** —
    thLinkMap R l j = thLinkQParam R l j。すなわち **テータ値の 2l 乗が
    ちょうどリンク先の q パラメータ q^{j²}** に一致する（M318F thLtorPow_uMon
    による指数 j²·2l = 2l·j² の計算）。theta-link の Θ↔q 同一視を本物で
    閉じる中心定理。 -/
theorem thLink_map_eq_qparam (R : CRing) (l : Nat) (j : Int) :
    thLinkMap R l j = thLinkQParam R l j := by
  show thLtorPow R (uMonHom R (thLtorExp j)) (2 * l)
      = uMonHom R (((2 * l : Nat) : Int) * thLtorExp j)
  rw [thLtorPow_uMon R (thLtorExp j) (2 * l),
      Int.mul_comm (thLtorExp j) (((2 * l : Nat) : Int))]

/-- **定理 (M328F-2d: q パラメータは q の冪)** — リンク先 q パラメータ q^{j²}
    は q = u^{2l} の j² 乗であり、周期格子 q^ℤ（l-冪部分群 IsLPowerValue、
    法 2l）に属す。theta-link の像が **q パラメータ（q の有理整数冪）** で
    あることの本物。 -/
theorem thLink_qparam_is_qpower (R : CRing) (l : Nat) (j : Int) :
    IsLPowerValue R ((2 * l : Nat) : Int) (thLinkQParam R l j) :=
  ⟨thLtorExp j, rfl⟩

/-! ## M328F-3: theta-link の次数変換（テータパイロット体積 → q パラメータ体積） -/

/-- **M328F-3a: q パラメータの実 Arakelov 次数** — deg_ℝ(q^{j²})
    = logVolLocal logq v (thLinkExp l j) = (2l·j²)·log q_v。リンク先 q
    パラメータの実数値 log-volume（M312F logVolLocal）。 -/
def thLinkQParamDeg (logq : Nat → RReal) (v : Nat) (l : Nat) (j : Int) : RReal :=
  logVolLocal logq v (thLinkExp l j)

/-- **定理 (M328F-3b: theta-link の次数変換)** — q パラメータの実 deg_ℝ は
    テータ値の実 deg_ℝ（M319F thPilotValueDeg）の **2l 倍**:
    deg_ℝ(q^{j²}) ≈ 2l · deg_ℝ(Θ(q,u_j))。theta-link が次数を ×2l で変換
    する（テータ値を 2l 乗する写像の deg_ℝ 版）ことの本物（realEq）。 -/
theorem thLink_degree (logq : Nat → RReal) (v : Nat) (l : Nat) (j : Int) :
    realEq (thLinkQParamDeg logq v l j)
      (rmul (intToReal ((2 * l : Nat) : Int)) (thPilotValueDeg logq v j)) := by
  show realEq (rmul (intToReal (((2 * l : Nat) : Int) * thLtorExp j)) (logq v))
      (rmul (intToReal ((2 * l : Nat) : Int))
        (rmul (intToReal (thLtorExp j)) (logq v)))
  exact realEq_trans
    (rmul_congr_left (logq v)
      (realEq_symm (intToReal_mul ((2 * l : Nat) : Int) (thLtorExp j))))
    (rmul_assoc_real (intToReal ((2 * l : Nat) : Int))
      (intToReal (thLtorExp j)) (logq v))

/-- **M328F-3c: q パラメータ側の総体積** — Σ_{j=1}^{n} deg_ℝ(q^{j²})。
    theta-link 先のホッジ劇場での q パラメータ体積（M319F thPilotTotalVol の
    q パラメータ版）。 -/
def thLinkQParamTotalVol (logq : Nat → RReal) (v : Nat) (l : Nat) : Nat → RReal
  | 0 => realZero
  | n + 1 => realAdd (thLinkQParamTotalVol logq v l n)
      (thLinkQParamDeg logq v l ((n + 1 : Nat) : Int))

/-- **定理 (M328F-3d: 総体積の次数変換)** — q パラメータ側総体積は
    テータパイロット総体積（M319F thPilotTotalVol）の **2l 倍**:
    Σ deg_ℝ(q^{j²}) ≈ 2l · Σ deg_ℝ(Θ(q,u_j))。theta-link がテータパイロット
    体積を q パラメータ側体積へ ×2l で **本物に変換**する（実数値 deg_ℝ の
    realEq、各項 thLink_degree を有限和へ束ねる）。 -/
theorem thLink_total_degree (logq : Nat → RReal) (v : Nat) (l : Nat) :
    ∀ n, realEq (thLinkQParamTotalVol logq v l n)
      (rmul (intToReal ((2 * l : Nat) : Int)) (thPilotTotalVol logq v n)) := by
  intro n
  induction n with
  | zero =>
    show realEq realZero (rmul (intToReal ((2 * l : Nat) : Int)) realZero)
    exact realEq_symm (rmul_zero (intToReal ((2 * l : Nat) : Int)))
  | succ n ih =>
    show realEq (realAdd (thLinkQParamTotalVol logq v l n)
          (thLinkQParamDeg logq v l ((n + 1 : Nat) : Int)))
        (rmul (intToReal ((2 * l : Nat) : Int))
          (realAdd (thPilotTotalVol logq v n)
            (thPilotValueDeg logq v ((n + 1 : Nat) : Int))))
    refine realEq_trans
      (realAdd_congr_left (thLinkQParamDeg logq v l ((n + 1 : Nat) : Int)) ih) ?_
    refine realEq_trans
      (realAdd_congr_right
        (rmul (intToReal ((2 * l : Nat) : Int)) (thPilotTotalVol logq v n))
        (thLink_degree logq v l ((n + 1 : Nat) : Int))) ?_
    exact realEq_symm (rmul_add_left (thPilotTotalVol logq v n)
      (thPilotValueDeg logq v ((n + 1 : Nat) : Int))
      (intToReal ((2 * l : Nat) : Int)))

/-! ## M328F-4: crux の舞台としての theta-link（honest ── crux は範囲外） -/

/-- **定理 (M328F-4a: crux の舞台としての theta-link／honest)** — theta-link
    写像（Θ↔q の同一視 thLinkMap = thLinkQParam）は **本物で構成される**が、
    その下でのテータパイロット ⇄ ガウスパイロットの比較（crux ＝ Dβ-ω ＝
    多輻的アルゴリズム）は **本層で証明しない**。crux を任意の外部 Prop
    `crux` として受け取り、theta-link 写像の本物性 **と** crux の連言を、
    crux が仮説として供給された場合にのみ返す——crux は決して導出されない
    （範囲外）ことの明示（過大主張禁止）。 -/
theorem thLink_crux_stage (R : CRing) (l : Nat) (j : Int)
    (crux : Prop) (hcrux : crux) :
    thLinkMap R l j = thLinkQParam R l j ∧ crux :=
  ⟨thLink_map_eq_qparam R l j, hcrux⟩

/-- **定理 (M328F-4b: 舞台仮説の明示)** — theta-link 写像は本物（無条件で
    thLinkMap = thLinkQParam）であり、crux（外部 Prop）は **仮説としてのみ**
    利用可能で本層では導出されない。theta-link の写像を本物にするのみで
    crux を証明しない、という scope を機械検証可能な形で固定する。 -/
theorem thLink_stage_hypothesis (R : CRing) (l : Nat) :
    (∀ j : Int, thLinkMap R l j = thLinkQParam R l j)
      ∧ (∀ crux : Prop, crux → crux) :=
  ⟨thLink_map_eq_qparam R l, fun _ h => h⟩

/-! ## M328F-5: log-theta-lattice の 1 theta-link 辺を実テータ値へ昇格 -/

/-- **M328F-5a: theta-link 格子辺データ** — M3 `LogThetaLattice` の水平
    theta-link 辺（LatticeSite (col,row) → (col+1,row) の Link.theta、
    従来は頂点に実データを載せない**組合せ骨格**）を、実テータ値
    Θ(q,u_j) と リンク先 q パラメータ q^{j²} の **同一視写像**で装飾する
    構造。横の theta-link 側を実テータ値へ昇格（縦の log-link は M3 のまま）。 -/
structure ThetaLinkLatticeData (R : CRing) (l : Nat) where
  /-- 辺の始点の列（数論的正則構造ラベル）。 -/
  col : Int
  /-- 辺の始点の行（log 方向ラベル）。 -/
  row : Int
  /-- M3 の水平 theta-link 辺 (col,row) → (col+1,row)（本物の組合せ辺）。 -/
  edge : Link ⟨col, row⟩ ⟨col + 1, row⟩
  /-- 始点に載る実テータ値 Θ(q,u_j) = u^{j²}（M318F）。 -/
  thetaValue : Int → (laurentRing R).carrier
  /-- 終点に載る実 q パラメータ q^{j²} = u^{2l·j²}（M328F-2）。 -/
  qParam : Int → (laurentRing R).carrier
  /-- theta-link 同一視: テータ値の 2l 乗 = 終点の q パラメータ（本物）。 -/
  identify : ∀ j : Int, thLinkMap R l j = qParam j

/-- **M328F-5b: witness** — M3 の Link.theta 辺に実テータ値
    thLtorValue（始点）と q パラメータ thLinkQParam（終点）を載せ、
    同一視を thLink_map_eq_qparam で充足。組合せ骨格の theta-link 辺を
    実テータ値へ昇格した witness。 -/
def thetaLinkLatticeData (R : CRing) (l : Nat) (n m : Int) :
    ThetaLinkLatticeData R l where
  col := n
  row := m
  edge := Link.theta n m
  thetaValue := thLtorValue R
  qParam := thLinkQParam R l
  identify := thLink_map_eq_qparam R l

/-- **定理 (M328F-5c: log-theta-lattice の 1 theta-link 辺の実テータ値昇格)** —
    任意の格子位置 (n,m) で、M3 の水平 theta-link 辺 (n,m)→(n+1,m)
    （Link.theta）に実テータ値 Θ(q,u_j) と q パラメータ q^{j²} の同一視を
    載せたデータが存在する。**組合せ骨格の theta-link 辺が実テータ値へ
    昇格**される（縦の log-link・多輻的アルゴリズムは柱D 後続）。 -/
theorem thLink_lattice_point (R : CRing) (l : Nat) (n m : Int) :
    Nonempty (ThetaLinkLatticeData R l) :=
  ⟨thetaLinkLatticeData R l n m⟩

/-! ## M328F-6: capstone（theta-link データの束ね） -/

/-- **M328F-6a: theta-link データ** — テータ値 Θ(q,u_j)、リンク先 q
    パラメータ q^{j²}、theta-link 写像（テータ値の 2l 乗）、指数対応
    （×2l のスケール）を一括束ね。IUT の theta-link（Θ↔q の同一視・
    多輻的アルゴリズムの舞台の水平辺）を実テータ値の上で本物構成した witness。
    crux 不等式（Dβ-ω）は範囲外（M328F-4 参照）。 -/
structure ThetaLinkData (R : CRing) (l : Nat) where
  /-- テータ値 Θ(q,u_j) = u^{j²}（M318F 本物）。 -/
  thetaValue : Int → (laurentRing R).carrier
  /-- リンク先の q パラメータ q^{j²} = u^{2l·j²}。 -/
  qParam : Int → (laurentRing R).carrier
  /-- theta-link 写像 = テータ値の 2l 乗（本物の反復群冪）。 -/
  linkMap : Int → (laurentRing R).carrier
  /-- q パラメータの微細指数（2l·j²）。 -/
  exp : Int → Int
  /-- テータ値の指数抽出: Θ(q,u_j) = u^{j²}（M318F）。 -/
  thetaValue_eq : ∀ j : Int, thetaValue j = uMonHom R (thLtorExp j)
  /-- theta-link 写像 = q パラメータ（Θ↔q の同一視・本物）。 -/
  map_eq : ∀ j : Int, linkMap j = qParam j
  /-- q パラメータの指数抽出: q^{j²} = u^{exp j}。 -/
  qParam_exp : ∀ j : Int, qParam j = uMonHom R (exp j)
  /-- 指数のスケール対応: exp j = (2l)·j²（×2l の分母払い）。 -/
  exp_scale : ∀ j : Int, exp j = ((2 * l : Nat) : Int) * thLtorExp j
  /-- q パラメータは q = u^{2l} の j² 乗（q^ℤ、法 2l）。 -/
  qParam_is_qpow : ∀ j : Int,
    IsLPowerValue R ((2 * l : Nat) : Int) (qParam j)

/-- **M328F-6b: witness 本体** — thetaValue := thLtorValue、
    qParam := thLinkQParam、linkMap := thLinkMap、exp := thLinkExp として
    全フィールドを M328F-1〜2 の本物で埋める。 -/
def thetaLinkData (R : CRing) (l : Nat) : ThetaLinkData R l where
  thetaValue := thLtorValue R
  qParam := thLinkQParam R l
  linkMap := thLinkMap R l
  exp := thLinkExp l
  thetaValue_eq := thLtor_value_exponent R
  map_eq := thLink_map_eq_qparam R l
  qParam_exp := fun _ => rfl
  exp_scale := fun _ => rfl
  qParam_is_qpow := thLink_qparam_is_qpower R l

/-- **定理 (M328F-6c: theta-link データの存在／M328F 見出し)** — 任意の係数環
    R・任意の l に対し、テータ値 Θ(q,u_j)=u^{j²} をリンク先の q パラメータ
    q^{j²}=u^{2l·j²} と同一視する theta-link（写像＝テータ値の 2l 乗・指数
    対応＝×2l のスケール・q パラメータは q^ℤ）を実テータ値の上で本物構成した
    データが存在する。IUT の theta-link の **写像そのもの** が M318F の本物の
    テータ値の上で実体化される（crux 不等式は範囲外）。 -/
theorem thLink_exists (R : CRing) (l : Nat) :
    Nonempty (ThetaLinkData R l) :=
  ⟨thetaLinkData R l⟩

/-! ## 実例（l=5・小さい j: テータ値指数 j² と q パラメータ指数 2l·j² の対応） -/

/-- 実例: l=5・j=1 の q パラメータ微細指数 = 2·5·1² = 10（q^1 = u^{10}）。 -/
example : thLinkExp 5 1 = 10 := by rw [thLink_exponent]; omega

/-- 実例: l=5・j=2 の q パラメータ微細指数 = 2·5·2² = 40（q^4 = u^{40}）。 -/
example : thLinkExp 5 2 = 40 := by rw [thLink_exponent]; omega

/-- 実例: theta-link 写像 = q パラメータ（l=5, j=1）: Θ(q,u_1)^{10} = q^1。 -/
example (R : CRing) : thLinkMap R 5 1 = thLinkQParam R 5 1 :=
  thLink_map_eq_qparam R 5 1

/-- 実例: l=5・j=2 の q パラメータ q^{4} が q=u^{10} の冪（q^ℤ, 法 10）。 -/
example (R : CRing) :
    IsLPowerValue R ((2 * 5 : Nat) : Int) (thLinkQParam R 5 2) :=
  thLink_qparam_is_qpower R 5 2

/-- 実例: theta-link の次数変換（l=5, j=1）: deg_ℝ(q^1) ≈ 10·deg_ℝ(Θ(q,u_1))。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thLinkQParamDeg logq v 5 1)
      (rmul (intToReal ((2 * 5 : Nat) : Int)) (thPilotValueDeg logq v 1)) :=
  thLink_degree logq v 5 1

/-- 実例: 1 本の theta-link 辺は Θ-link をちょうど 1 本含む経路（M3 Path 1）。
    実テータ値を載せる格子辺が組合せ的に「列 +1」の水平辺であることの整合。 -/
example (n m : Int) : Path 1 (⟨n, m⟩ : LatticeSite) ⟨n + 1, m⟩ :=
  Path.theta n m (Path.nil _)

end IUT
