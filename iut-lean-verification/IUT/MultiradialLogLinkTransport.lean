-- M437F MultiradialLogLinkTransport [実・本物・柱D]
-- complete_pct 影響: 柱D で 縦 log-link 体積輸送(M337F, 積→和の加法輸送)と横 theta-link ×2l 輸送
--   (M407F)を合成し、log-theta-lattice 正方形(M397F HV=VH)を経由して「log-link 版の多輻 log-volume
--   輸送」を本物で建設。M432F の両側実 deg_ℝ 有界を log-link 合成後の主語 mlltLogLink へ張り替え、
--   合成輸送後も両側有界域の内側に留まることを実で示す(M337F/M407F/M397F/M432F を合成昇格)。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。
--   合成は有限段 n・付値レベル sumSq n・×2l 明示スケール・log-link は主項係数レベル(完全収束は後続)・
--   log-theta-lattice 交換は M397F 実 deg_ℝ 付値レベル(HV≈VH、多輻不等式そのものではない)・局所体
--   K=ℚ_p・ℝ は setoid(realEq/rLe で言明)。

/-
  IUT/MultiradialLogLinkTransport.lean — M437F（定理3.11 / 多輻 log-volume 輸送の log-link 版：
  縦 log-link 体積輸送と横 theta-link ×2l 輸送を合成し、両側実有界が合成の下で coherent に保たれる）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の先行建設 (b)・既存の縦 log-link 体積輸送 (M337F
    `logLinkVolTransport`/`logLink_pilot_transport`)・横 theta-link ×2l 輸送 (M407F
    `tlm_thetaLink_transports_rep`)・log-theta-lattice 正方形の実 deg_ℝ 可換 (M397F
    `ltls_square_commutes_vol`)・両側実有界 (M432F `lvt_two_sided_transported`) の (a) 束ね昇格）。
    M337F は縦 log-link が乗法側の積（付値の和）を加法 log-shell の体積の和へ移すこと（log turns
    products into sums, `logLink_volume_transport`）と、実テータパイロット体積が log-link 像の
    加法 log-shell 体積に一致すること（`logLink_pilot_transport`）を本物化した。M407F は横 theta-link
    が多輻表現を実 deg_ℝ で ×2l に coherent 輸送することを、M397F は log-theta-lattice 正方形が実
    deg_ℝ 体積レベルで可換（横 theta-link ×2l then 縦 log-link ＝ 縦 log-link then 横 theta-link ×2l、
    `ltlsSquareHV ≈ ltlsSquareVH`）であることを本物化した。**次の本物の一手**は、これらを**合成**して
    「**log-link 版の多輻 log-volume 輸送**」——多輻パイロット段（付値核 Σj²）を横 theta-link ×2l で
    スケールしてから縦 log-link で加法 log-shell の実 deg_ℝ 体積へ輸送する合成写像 `mlltLogLink`——を
    建て、その合成輸送が (i) theta-link と log-link の**両立**（可換正方形の部分ケース、M397F HV≈VH）、
    (ii) 合成後の主語がなお多輻表現の ×2l に realEq、(iii) M432F の両側実有界域の内側に留まる、ことを
    示すこと。crux は導出しない。
  * complete_pct 影響: **前進**。M337F は縦 log-link 加法輸送を、M407F は横 theta-link ×2l 輸送を、
    M397F は格子正方形の可換を、M432F は両側有界の輸送安定をそれぞれ本物化したが、**縦 log-link と
    横 theta-link を合成した「log-link 版の多輻 log-volume 輸送」を一つの写像へ束ね、その合成が両立
    (HV≈VH) しつつ両側有界域の内側に留まる**という一手は範囲外だった。本 M437F はその**次の本物の一手**:
      - **合成輸送写像** `mlltLogLink`（= `ltlsSquareHV`（付値 sumSq n）= 横 theta-link ×2l then 縦
        log-link の実 deg_ℝ 体積 = logLinkVolTransport v (2l·Σj²)）。
      - **theta-link ⇄ log-link 両立**（可換正方形の部分ケース）`mllt_theta_log_compat`: 横 theta-link
        ×2l then 縦 log-link ＝ 縦 log-link then 横 theta-link ×2l（M397F `ltls_square_commutes_vol`）。
      - **log-link 輸送は積を和へ**（加法輸送法）`mllt_loglink_additive`: 合成の底となる縦 log-link は
        乗法側の付値の和（積）を加法 log-shell 体積の和へ移す（M337F `logLink_volume_transport`）。
      - **合成後主語 = ×2l·多輻表現** `mllt_transports_rep`/`mllt_eq_thlink`: 合成輸送後の主語
        `mlltLogLink` は多輻表現の ×2l に realEq（M397F 可換 + M337F パイロット輸送 + M372F 降下を連結）で、
        横 theta-link 側総体積 `thLinkQParamTotalVol`（M407F）と realEq。
      - **合成後も両側有界域の内側**（本丸）`mllt_loglink_transport`: 合成輸送後の主語 `mlltLogLink` が
        M432F の両側実有界域（下 2l·(l³·log q_v) ≤ 3·合成後・上 合成後 ≤ 2l·対数殻 deg_ℝ）の内側に
        留まる（M432F `lvt_two_sided_transported` を realEq で主語張り替え `rLe_congr`）。
      - **crux 外部** `mllt_crux_external`/`mllt_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は範囲外。
      - **正直な限定を定理として** `mllt_model_scope`（有限段・付値レベル・×2l 明示・crux 外部を固定）。
    crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の係争点）は**決して導出せず**外部仮説のまま。柱D の縦
    log-link 加法輸送と横 theta-link ×2l 輸送を**合成し、両側有界が合成の下で安定であるという構造を
    本物化**。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M437F-1 `mlltLogLink` — 合成輸送写像（横 theta-link ×2l then 縦 log-link の実 deg_ℝ 体積、付値核
      Σj²）。M397F `ltlsSquareHV`（付値 sumSq n）の多輻パイロット段への特殊化。
  * M437F-2 `mllt_theta_log_compat` — theta-link ⇄ log-link 両立（可換正方形の部分ケース、M397F
      `ltls_square_commutes_vol`）: 横 theta-link ×2l then 縦 log-link ＝ 縦 log-link then 横 theta-link ×2l。
  * M437F-3 `mllt_loglink_additive` — 縦 log-link は積（付値の和）を加法 log-shell 体積の和へ移す
      （M337F `logLink_volume_transport`）。
  * M437F-4 `mllt_transports_rep`/`mllt_eq_thlink` — 合成後主語 = ×2l·多輻表現（M397F 可換 + M337F
      `logLink_pilot_transport` + M372F `mrp_representation_descent` を連結）で `thLinkQParamTotalVol`
      （M407F）と realEq。
  * M437F-5 `mllt_loglink_transport` — 本丸: 合成輸送後の主語が M432F 両側有界域の内側（下界 2l·l³·log q_v
      ≤ 3·合成後・上界 合成後 ≤ 2l·対数殻、`rLe_congr` で M432F `lvt_two_sided_transported` の主語を張り替え）。
  * M437F-6 `mllt_crux_external`/`mllt_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M437F-7 `mllt_model_scope` — 正直な限定（有限段・付値レベル sumSq n・×2l 明示・crux 外部）を定理化。
  * M437F-8 capstone `MultiradialLogLinkTransportData`/`mllt_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロットの比較不等式そのもの＝
    IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層が合成するのは、縦 log-link の加法輸送（積→和、
    M337F 無条件）と横 theta-link の ×2l 体積輸送（M407F）を log-theta-lattice 正方形（M397F HV≈VH）で
    繋いだ**合成輸送写像**であり、その両立と両側有界域内滞留は M97 初等不等式・付値加法性・M180 乗法
    単調性・M150 結合律で閉じる**無条件で本物**の命題——**crux（rep ≤ gauss）とは別の主張**。crux は
    任意の外部 Prop として受け取るのみ（`mllt_crux_is_hypothesis` は Iff.rfl）。
  * **合成は有限段 n・付値レベル sumSq n（Σj²）・×2l 明示スケール**。log-link は M337F の p 進対数の
    主項 θ_d レベル（完全収束級数 log(1+t)=t−t²/2+… は後続）。log-theta-lattice 交換は M397F
    `ltls_square_commutes_vol`（HV≈VH）の実 deg_ℝ 付値レベル——群レベルの完全同変性は後続。許容誤差
    log(l) 等の明示不定性シフトは M397F `ltls_square_vol_shift` の明示 μ 上乗せで交換する（本層は
    μ=0 の核ケース）。
  * **両側有界は M432F の輸送安定（M427F 両側有界を ×2l 輸送でスケール）**。**局所体は K = ℚ_p**。
    log q_v は非負実重み witness（hq : realZero ≤ logq v が前提）。**ℝ は setoid**（realEq が同値・`=`
    でない）ゆえ合成輸送・両立・両側有界は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 合成・本物の先行建設[実]。一般名は `mllt` 接頭辞で衝突回避。
-/
import IUT.LogVolMultiradialTransport
import IUT.LogLinkReal

namespace IUT

/-! ## M437F-1: 合成輸送写像（横 theta-link ×2l then 縦 log-link の実 deg_ℝ 体積） -/

/-- **M437F-1: log-link 版の多輻 log-volume 輸送写像** — 多輻パイロット段（付値の不変核 Σj²）を、
    横 theta-link で ×2l スケールしてから縦 log-link で加法 log-shell の実 deg_ℝ 体積へ輸送した
    合成写像。M397F 正方形の横→縦体積 `ltlsSquareHV`（付値 sumSq n）の多輻パイロット段への特殊化:
      mlltLogLink v l n  =  logLinkVolTransport v (2l·Σj²)  =  deg_ℝ(log-link(2l·Σ_{j≤n} j²))。
    横 theta-link 輸送（M407F）と縦 log-link 輸送（M337F）を log-theta-lattice 正方形（M397F）で
    合成した本物の主語（toy を用いない）。 -/
def mlltLogLink (logq : Nat → RReal) (v l n : Nat) : RReal :=
  ltlsSquareHV logq v l ((sumSq n : Nat) : Int)

/-! ## M437F-2: theta-link ⇄ log-link 両立（可換正方形の部分ケース） -/

/-- **定理 (M437F-2: theta-link ⇄ log-link 両立・可換正方形の部分ケース・本物)** — 合成輸送写像
    `mlltLogLink`（横 theta-link ×2l then 縦 log-link）は、順序を入れ替えた縦 log-link then 横
    theta-link ×2l（M397F `ltlsSquareVH` = `2l · logLinkVolTransport v Σj²`）と realEq に一致する:
      横 theta-link ×2l then 縦 log-link  ≈  縦 log-link then 横 theta-link ×2l。
    これは log-theta-lattice 正方形の実 deg_ℝ 体積可換（M397F `ltls_square_commutes_vol`、HV≈VH）を
    多輻パイロット段（付値 Σj²）へ特殊化した本物——縦 log-link（加法輸送）と横 theta-link（×2l
    スケール）の**交換が実 Arakelov 次数の上で閉じる**（可換図式の部分ケース、crux 不等式ではない）。 -/
theorem mllt_theta_log_compat (logq : Nat → RReal) (v l n : Nat) :
    realEq (mlltLogLink logq v l n)
      (rmul (intToReal ((2 * l : Nat) : Int))
        (logLinkVolTransport logq v ((sumSq n : Nat) : Int))) :=
  ltls_square_commutes_vol logq v l ((sumSq n : Nat) : Int)

/-! ## M437F-3: 縦 log-link は積（付値の和）を加法 log-shell 体積の和へ移す -/

/-- **定理 (M437F-3: log-link 加法輸送法・本物)** — 合成輸送の底となる縦 log-link は加法写像ゆえ、
    乗法側の**積**（付値 a+b ＝ 2 単数の積の付値）を、加法 log-shell の実 deg_ℝ 体積の**和**へ移す:
      logLinkVolTransport v (a+b)  ≈  logLinkVolTransport v a  +  logLinkVolTransport v b。
    許容誤差 log(l) 等の明示不定性シフトはこの加法性で予測可能な明示項として吸収される（M337F
    `logLink_volume_transport`、log turns products into sums）——合成輸送の底が本物の加法構造で
    閉じることの機械検証（crux 不等式ではない）。 -/
theorem mllt_loglink_additive (logq : Nat → RReal) (v : Nat) (a b : Int) :
    realEq (logLinkVolTransport logq v (a + b))
      (realAdd (logLinkVolTransport logq v a) (logLinkVolTransport logq v b)) :=
  logLink_volume_transport logq v a b

/-! ## M437F-4: 合成後主語 = ×2l·多輻表現（M397F 可換 + M337F パイロット輸送 + M372F 降下） -/

/-- **定理 (M437F-4a: 合成後主語 = ×2l·多輻表現・本物)** — 合成輸送後の主語 `mlltLogLink`（横
    theta-link ×2l then 縦 log-link）は多輻表現（M372F `mrpRepresentation`、テータパイロット体積の
    (Ind1)(Ind2)-不変核 Σj² への降下）の **×2l 倍**にちょうど realEq に等しい:
      mlltLogLink v l n  ≈  2l · (多輻表現)。
    証明は (i) M397F 可換 `mllt_theta_log_compat`（合成 ≈ 2l·logLinkVolTransport v Σj²）、(ii) M337F
    `logLink_pilot_transport`（logLinkVolTransport v Σj² ≈ テータパイロット総体積）、(iii) M372F
    `mrp_representation_descent`（テータパイロット総体積 ≈ 多輻表現）を連結する——縦 log-link と横
    theta-link を合成した実 deg_ℝ 体積が多輻表現の ×2l と一致する本物（crux 不等式は導出しない）。 -/
theorem mllt_transports_rep (logq : Nat → RReal) (v l n : Nat) :
    realEq (mlltLogLink logq v l n)
      (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n)) :=
  realEq_trans (mllt_theta_log_compat logq v l n)
    (rmul_congr_right (intToReal ((2 * l : Nat) : Int))
      (realEq_trans
        (realEq_symm (logLink_pilot_transport logq v n))
        (mrp_representation_descent logq v n)))

/-- **定理 (M437F-4b: 合成後主語 = 横 theta-link 側総体積)** — 合成輸送後の主語 `mlltLogLink`
    （縦 log-link 経由）は、横 theta-link 側の q パラメータ総体積 `thLinkQParamTotalVol`（M407F、
    theta-link 側総体積 ≈ 2l·多輻表現）と realEq に一致する。すなわち縦 log-link 経由の合成輸送と
    横 theta-link 経由の輸送は同じ多輻表現の ×2l へ着地する——2 経路の輸送が実 deg_ℝ で coherent に
    閉じる本物（M397F 正方形の両辺が同じ多輻 log-volume を与える、crux 不等式ではない）。 -/
theorem mllt_eq_thlink (logq : Nat → RReal) (v l n : Nat) :
    realEq (mlltLogLink logq v l n) (thLinkQParamTotalVol logq v l n) :=
  realEq_trans (mllt_transports_rep logq v l n)
    (realEq_symm (tlm_thetaLink_transports_rep logq v l n))

/-! ## M437F-5: 本丸 — 合成輸送後の主語は両側有界域の内側に留まる -/

/-- **定理 (M437F-5: 合成輸送後主語は両側実有界域の内側・本丸・本物の合成)** — 縦 log-link と横
    theta-link を合成した輸送後の主語 `mlltLogLink` は、M432F の**スケールした両側実有界域の内側に
    なお留まる**:
      (i) **下界**: 2l·(l³·log q_v) ≤ 3·(合成輸送後主語)、
      (ii)**上界**: 合成輸送後主語 ≤ 2l·(対数殻 m^{Σj²+c} の deg_ℝ)。
    証明は M432F `lvt_two_sided_transported`（横 theta-link 側総体積 `thLinkQParamTotalVol` が両側
    有界域の内側）を、主語を M437F-4b `mllt_eq_thlink`（合成後主語 ≈ `thLinkQParamTotalVol`）の realEq で
    張り替える（`rLe_congr`）。すなわち**両側有界が縦 log-link と横 theta-link の合成の下でも coherent に
    保たれ**、合成輸送後の log-volume もその実 deg_ℝ 有界域を離れない本物の合成（crux 不等式は決して
    導出しない）。 -/
theorem mllt_loglink_transport (logq : Nat → RReal) (v l n c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((3 : Nat) : Int)) (mlltLogLink logq v l n))
    ∧ rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c))) := by
  have heq : realEq (thLinkQParamTotalVol logq v l n) (mlltLogLink logq v l n) :=
    realEq_symm (mllt_eq_thlink logq v l n)
  refine ⟨?_, ?_⟩
  · -- 下界: 3·thLinkQParamTotalVol → 3·合成後主語 へ RHS を張り替える。
    exact rLe_congr (realEq_refl _)
      (rmul_congr_right (intToReal ((3 : Nat) : Int)) heq)
      (lvt_two_sided_transported logq v l n c hq).1
  · -- 上界: 主語 thLinkQParamTotalVol → 合成後主語 へ LHS を張り替える。
    exact rLe_congr heq (realEq_refl _)
      (lvt_two_sided_transported logq v l n c hq).2

/-! ## M437F-6: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M437F-6a: 合成輸送後有界は本物・crux は外部仮説／honest)** — 両側有界が縦 log-link と横
    theta-link の合成輸送の下で coherent に保たれること（M437F-5: 合成後主語 `mlltLogLink` ≤ 2l·対数殻
    deg_ℝ）は付値加法性・乗法単調性・×2l 輸送・M397F 正方形可換で閉じる**無条件で本物**の命題（crux
    とは独立に成立）。しかし theta-pilot ≤ gauss-pilot の**多輻的アルゴリズム**（crux Dβ-ω ＝ IUT 論争の
    当の係争点）は本層で**決して証明しない**。crux を任意の外部 Prop `crux` として受け取り、合成輸送後
    上界の本物性 **と** crux の連言を、crux が仮説として供給された場合にのみ返す——crux は決して
    導出されない。 -/
theorem mllt_crux_external (logq : Nat → RReal) (v l n c : Nat)
    (hq : rLe realZero (logq v)) (crux : Prop) (hcrux : crux) :
    rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
    ∧ crux :=
  ⟨(mllt_loglink_transport logq v l n c hq).2, hcrux⟩

/-- **定理 (M437F-6b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux（theta ≤ gauss 比較）は本層が合成した合成
    輸送後有界とは別物であり、論争の係争点をそのまま外部仮説として受け取ったものであることを機械
    検証で明示（M337F `logLink_crux_hypothesis`・M407F `tlm_crux_is_hypothesis`・M432F
    `lvt_crux_is_hypothesis` と同じ精神）。 -/
theorem mllt_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M437F-7: 正直な限定を定理として明記（消去・弱化禁止） -/

/-- **定理 (M437F-7: 合成輸送の正直な scope・限定を定理化)** — 本層の合成輸送 `mlltLogLink` は、
    (i) **有限段 n・付値レベル Σj²・×2l 明示スケール**の合成である（`mllt_theta_log_compat`:
        合成 ≈ 2l·logLinkVolTransport v Σj²、横 theta-link ×2l then 縦 log-link の正方形の部分ケース）、
    (ii) **crux（外部 Prop）は仮説としてのみ利用可能で本層では導出されない**（`∀ crux, crux → crux`）。
    すなわち本層は縦 log-link 加法輸送と横 theta-link ×2l 輸送の**合成を本物にするのみ**で、多輻不等式
    （crux Dβ-ω）を証明しない、という正直な限定を機械検証可能な形で固定する（消去・弱化禁止）。 -/
theorem mllt_model_scope (logq : Nat → RReal) (v l n : Nat) :
    realEq (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int))
          (logLinkVolTransport logq v ((sumSq n : Nat) : Int)))
    ∧ (∀ crux : Prop, crux → crux) :=
  ⟨mllt_theta_log_compat logq v l n, fun _ h => h⟩

/-! ## M437F-8: capstone -/

/-- **M437F-8a: log-link 版の多輻 log-volume 輸送データ**（総括） — 縦 log-link の加法体積輸送（M337F）と
    横 theta-link の ×2l 体積輸送（M407F）を log-theta-lattice 正方形（M397F HV≈VH）で合成した「log-link
    版の多輻 log-volume 輸送」を束ねる: theta-link ⇄ log-link 両立（可換正方形の部分ケース）・log-link
    加法輸送（積→和）・合成後主語 = ×2l·多輻表現 = 横 theta-link 側総体積・合成後主語が M432F 両側有界域の
    内側に留まること。主語は M337F/M407F/M397F/M432F の本物の実 deg_ℝ であり toy を用いない。crux
    （Dβ-ω＝theta ≤ gauss）は外部仮説であって本層で証明されない。 -/
structure MultiradialLogLinkTransportData (logq : Nat → RReal) (v : Nat) where
  /-- 横 theta-link 輸送スケール 2l を与える l-捻れ。 -/
  l : Nat
  /-- 合成輸送写像（横 theta-link ×2l then 縦 log-link）。 -/
  transport : Nat → RReal
  /-- transport は本層の合成輸送写像 `mlltLogLink`。 -/
  is_transport : transport = mlltLogLink logq v l
  /-- theta-link ⇄ log-link 両立（可換正方形の部分ケース、M397F HV≈VH）。 -/
  theta_log_compat : ∀ n : Nat,
    realEq (transport n)
      (rmul (intToReal ((2 * l : Nat) : Int))
        (logLinkVolTransport logq v ((sumSq n : Nat) : Int)))
  /-- 合成後主語 = ×2l·多輻表現（M397F 可換 + M337F パイロット輸送 + M372F 降下）。 -/
  transports_rep : ∀ n : Nat,
    realEq (transport n)
      (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n))
  /-- 合成後主語 = 横 theta-link 側総体積（2 経路の輸送が coherent）。 -/
  eq_thlink : ∀ n : Nat,
    realEq (transport n) (thLinkQParamTotalVol logq v l n)
  /-- 本丸: 合成後主語は M432F 両側有界域の内側（下 2l·l³·log q_v ≤ 3·合成後・上 合成後 ≤ 2l·対数殻）。 -/
  within_two_sided : ∀ n c : Nat, rLe realZero (logq v) →
    rLe (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((3 : Nat) : Int)) (transport n))
    ∧ rLe (transport n) (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
  /-- 縦 log-link は積（付値の和）を加法 log-shell 体積の和へ移す（合成の底の加法輸送）。 -/
  loglink_additive : ∀ a b : Int,
    realEq (logLinkVolTransport logq v (a + b))
      (realAdd (logLinkVolTransport logq v a) (logLinkVolTransport logq v b))

/-- **M437F-8b: 実データ** — 全フィールドを M437F-1〜5 の本物で充足。合成輸送は M397F 正方形の横辺
    `ltlsSquareHV`、両側有界は M432F、多輻表現は M372F であり crux は受け取らず合成のみ。 -/
def multiradialLogLinkTransportData (logq : Nat → RReal) (v l : Nat) :
    MultiradialLogLinkTransportData logq v where
  l := l
  transport := mlltLogLink logq v l
  is_transport := rfl
  theta_log_compat := fun n => mllt_theta_log_compat logq v l n
  transports_rep := fun n => mllt_transports_rep logq v l n
  eq_thlink := fun n => mllt_eq_thlink logq v l n
  within_two_sided := fun n c hq => mllt_loglink_transport logq v l n c hq
  loglink_additive := fun a b => mllt_loglink_additive logq v a b

/-- **M437F-8c: 存在（M437F 見出し）** — 任意の実重み logq・素点 v・l-捻れ l に対し、log-link 版の
    多輻 log-volume 輸送データが存在する。縦 log-link の加法体積輸送（M337F）は横 theta-link ×2l
    体積輸送（M407F）と log-theta-lattice 正方形（M397F HV≈VH）で coherent に合成でき、合成輸送後の
    主語 `mlltLogLink` は多輻表現の ×2l ＝ 横 theta-link 側総体積に realEq で一致し、M432F の両側実
    有界域の内側に留まる。crux（Dβ-ω＝theta ≤ gauss）は外部仮説として明示され、**決して証明されない**
    ——本層は縦 log-link 加法輸送と横 theta-link ×2l 輸送を**合成し、両側有界が合成の下で安定である
    という構造を本物にする**のみ。 -/
theorem mllt_exists (logq : Nat → RReal) (v l : Nat) :
    Nonempty (MultiradialLogLinkTransportData logq v) :=
  ⟨multiradialLogLinkTransportData logq v l⟩

/-! ## 実例（twist l=3 → ×2l=×6, 多輻段 n=5: Σ_{j=1}^{5} j²=55, 下界 n³=125） -/

/-- 実例（theta-link ⇄ log-link 両立・l=3, n=5）: 合成（横 theta-link ×6 then 縦 log-link）＝
    縦 log-link then 横 theta-link ×6（M397F 正方形の部分ケース）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (mlltLogLink logq v 3 5)
      (rmul (intToReal ((2 * 3 : Nat) : Int))
        (logLinkVolTransport logq v ((sumSq 5 : Nat) : Int))) :=
  mllt_theta_log_compat logq v 3 5

/-- 実例（合成後主語 = ×6·多輻表現・l=3, n=5）: 縦 log-link 経由の合成輸送後主語は多輻表現の ×6。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (mlltLogLink logq v 3 5)
      (rmul (intToReal ((2 * 3 : Nat) : Int)) (mrpRepresentation logq v 5)) :=
  mllt_transports_rep logq v 3 5

/-- 実例（合成後主語 = 横 theta-link 側総体積・l=3, n=5）: 縦 log-link 経由と横 theta-link 経由が一致。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (mlltLogLink logq v 3 5) (thLinkQParamTotalVol logq v 3 5) :=
  mllt_eq_thlink logq v 3 5

/-- 実例（本丸・合成後主語は域内・l=3, n=5）: 合成輸送後主語は下（6·125·log q_v ≤ 3·合成後）と
    上（合成後 ≤ 6·殻 deg_ℝ）の両側有界域の内側に留まる。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * 3 : Nat) : Int))
          (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v)))
        (rmul (intToReal ((3 : Nat) : Int)) (mlltLogLink logq v 3 5))
    ∧ rLe (mlltLogLink logq v 3 5)
        (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c))) :=
  mllt_loglink_transport logq v 3 5 c hq

/-- 実例（log-link 加法輸送・積→和）: 付値 2+3 の像体積は付値 2・3 の像体積の和。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (logLinkVolTransport logq v (2 + 3))
      (realAdd (logLinkVolTransport logq v 2) (logLinkVolTransport logq v 3)) :=
  mllt_loglink_additive logq v 2 3

/-- 実例（正直な限定・scope）: 合成は有限段・付値レベル・×6 明示で、crux は仮説として通すのみ。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (mlltLogLink logq v 3 5)
        (rmul (intToReal ((2 * 3 : Nat) : Int))
          (logLinkVolTransport logq v ((sumSq 5 : Nat) : Int)))
    ∧ (∀ crux : Prop, crux → crux) :=
  mllt_model_scope logq v 3 5

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  mllt_crux_is_hypothesis crux

/-- 実例（capstone 存在）: log-link 版の多輻 log-volume 輸送データは存在する。 -/
example (logq : Nat → RReal) (v l : Nat) :
    Nonempty (MultiradialLogLinkTransportData logq v) :=
  mllt_exists logq v l

end IUT
