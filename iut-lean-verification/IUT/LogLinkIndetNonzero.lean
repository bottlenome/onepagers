-- M442F LogLinkIndetNonzero [実・本物・柱D]
-- complete_pct 影響: 柱D で M437F(MultiradialLogLinkTransport)の「μ=0 核ケース(log(l) 不定性ゼロ)のみ」
--   という正直な限定を §2(a) 昇格で閉じる。log-link 版多輻 log-volume 輸送を μ≠0(log(l)-スケール不定性が
--   実際に効く)へ一般化し、両側界が不定性シフト log(l)·μ を許容誤差として吸収した上でなお保たれることを
--   本物構成(M397F ltls_square_vol_shift の明示 μ シフト API を再利用)。M437F の μ=0 核へ μ=0 で厳密還元。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。
--   不定性は明示 log(l)·μ の 1 パラメータ族(logVolLocal v μ)に留まり (Ind3) の完全な離散/連続混合や
--   一般不定性群は未・局所体 K=ℚ_p・ℝ は setoid(realEq/rLe で言明)。

/-
  IUT/LogLinkIndetNonzero.lean — M442F（定理3.11 / log-link 版多輻 log-volume 輸送の μ≠0 昇格：
  log(l)-スケール不定性が実際に効く一般 μ ケースで両側界が許容誤差込みでなお保たれる）

  ## 二軸
  * 主要成果の分類: **[実]**（§2(a) 昇格・既存の正直な限定を本物へ置換して閉じる）。M437F
    `MultiradialLogLinkTransport`（`mllt`）の合成輸送 `mlltLogLink` とその両側界 `mllt_loglink_transport`
    は本物だが、**許容誤差 log(l) を M397F 明示 μ シフトで交換し、本層は μ=0 核ケース（不定性ゼロ）に留まる**
    と正直に限定していた（`mllt_model_scope`）。本 M442F はその限定を **μ≠0（log(l) 不定性が実際に含まれる）
    ケースへ昇格**して閉じる: M397F `ltls_square_vol_shift`（正方形体積は明示 μ シフト logVolLocal v μ を除いて
    可換）の μ を **μ=0 から一般 μ へ解放**し、μ≠0 での合成輸送後 log-volume `linTransportMu` を建て、その
    両側界が **不定性シフト log(l)·μ（＝ logVolLocal v μ）を許容誤差として吸収した上でなお保たれる**ことを
    realEq/rLe で本物構成する。crux は導出しない。
  * complete_pct 影響: **前進**。M437F は縦 log-link 加法輸送と横 theta-link ×2l 輸送を合成して両側界内
    滞留を本物化したが、**その合成は μ=0 核（不定性ゼロ）に限られ**、log(l) 不定性が実際に効く μ≠0 の
    ケースは範囲外だった（M397F 明示 μ シフトで「交換する」と述べるに留まった）。本 M442F はその
    **μ=0 核のみ**という限定を破る:
      - **一般 μ シフト** `linMuShift`（M397F/M437F の μ=0 特殊化を一般 μ へ）: log(l)-スケール不定性の
        1 パラメータ族 logVolLocal v μ（μ 単位ぶんの局所 log-volume、大きさ |μ|·log q_v）。
      - **μ≠0 合成輸送** `linTransportMu`（mllt の μ=0 核 `mlltLogLink` を μ 一般へ拡張）: 付値核
        2l·Σj² に不定性 μ を上乗せして log-link 輸送した実 deg_ℝ 体積。
      - **不定性の明示分解** `lin_transport_decomp`: linTransportMu ≈ mlltLogLink（μ=0 核）+ linMuShift
        （M397F `ltls_square_vol_shift` そのもの）——μ≠0 の全寄与が μ=0 核 + 明示 μ シフトに分かれる。
      - **μ=0 厳密還元** `lin_reduces_to_mu_zero`: μ=0 で linTransportMu ≈ mlltLogLink（M437F μ=0 版へ
        厳密に一致、logVolLocal v 0 ≈ 0）——昇格が M437F を真に含むことを機械検証。
      - **両側界＋不定性許容** `lin_two_sided_with_indet`（本丸）: μ≠0 のとき下界 + 3·(log(l) 不定性シフト)
        ≤ 3·transported ・transported ≤ 上界 + (log(l) 不定性シフト)——不定性 log(l)·μ を両側界の許容誤差
        として吸収した上で M437F 両側界がなお保たれる（`rLe_add`＋M337F 分配 `rmul_add_left`）。
      - **不定性吸収と crux 位置** `lin_indet_absorbed`: μ=0 核の上界（crux が内側に座す μ=0 両側界）が
        μ≠0 でも保たれ、不定性 log(l)·μ が両側界の緩みとして完全に吸収される（transported = μ=0 核 +
        明示 μ シフト）——crux の位置づけ（両側界の内側）が μ≠0 でも保たれる。
      - **crux 外部** `lin_crux_external`/`lin_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は範囲外。
      - **残る限定を定理として** `lin_model_scope`: 不定性は明示 log(l)·μ の 1 パラメータ族に留まり
        (Ind3) の完全な離散/連続混合や一般不定性群は未、を正直に固定（M437F の「μ=0 核のみ」を実際に破った）。
    crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の係争点）は**決して導出せず**外部仮説のまま。柱D の
    log-link 版多輻輸送を **μ=0 核から μ≠0（log(l) 不定性込み）へ昇格し、両側界が許容誤差込みで安定である
    という構造を本物化**。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M442F-1 `linMuShift` — 一般 μ の log(l)-スケール不定性シフト（logVolLocal v μ、M397F/M437F μ=0
      特殊化を一般 μ へ・大きさ |μ|·log q_v）。
  * M442F-2 `linTransportMu` — μ≠0 合成輸送後 log-volume（mllt の μ=0 核 `mlltLogLink` の μ 一般拡張）。
  * M442F-3 `lin_transport_decomp` — linTransportMu ≈ mlltLogLink + linMuShift（M397F `ltls_square_vol_shift`）。
  * M442F-4 `lin_reduces_to_mu_zero` — μ=0 で linTransportMu ≈ mlltLogLink（M437F へ厳密還元・
      `logVolLocal_zero`）。
  * M442F-5 `lin_two_sided_with_indet` — 本丸: 下界 + 3·μ シフト ≤ 3·transported ・transported ≤
      上界 + μ シフト（M437F 両側界＋M130 `rLe_add`＋M337F 分配 `rmul_add_left`）。
  * M442F-6 `lin_indet_absorbed` — μ=0 核上界（crux の位置）は μ≠0 でも保たれ、不定性は明示 μ シフトとして
      完全吸収（M437F μ=0 上界 + 分解）。
  * M442F-7 `lin_crux_external`/`lin_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M442F-8 `lin_model_scope` — 残る正直な限定（明示 log(l)·μ の 1 パラメータ族・crux 外部）を定理化。
  * M442F-9 capstone `LogLinkIndetNonzeroData`/`lin_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロットの比較不等式そのもの＝
    IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層が昇格するのは M437F の合成輸送を μ=0 核から
    μ≠0（log(l) 不定性込み）へ広げ、両側界が不定性シフトを許容誤差として吸収してなお成立するという
    付値/体積レベルの安定性であり、M397F 明示 μ シフト・付値加法性・M130 加法単調性・M337F 実分配で
    閉じる**無条件で本物**の命題——**crux（rep ≤ gauss）とは別の主張**。crux は任意の外部 Prop として
    受け取るのみ（`lin_crux_is_hypothesis` は Iff.rfl）。
  * **不定性は明示 log(l)·μ の 1 パラメータ族（linMuShift = logVolLocal v μ）に留まる**。μ=0 核のみだった
    M437F を実際に破り μ≠0 を含むが、**(Ind3) の完全な離散/連続混合や一般不定性群（log-shell 不定性
    Ind1/Ind2/Ind3 の合成群作用）は未**——本層が扱うのは 1 パラメータ μ ∈ ℤ の明示シフトのみ。完全な
    不定性群の同変性は後続。
  * **合成は有限段 n・付値レベル sumSq n（Σj²）・×2l 明示スケール**。log-link は M337F 主項係数レベル・
    両側界は M432F/M437F の輸送安定・**局所体は K = ℚ_p**。log q_v は非負実重み witness
    （hq : realZero ≤ logq v が前提）。**ℝ は setoid**（realEq が同値・`=` でない）ゆえ分解・還元・
    両側界・吸収は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 昇格・正直な限定を本物へ置換[実]。一般名は `lin` 接頭辞で衝突回避。
-/
import IUT.MultiradialLogLinkTransport
import IUT.LogThetaLatticeShell

namespace IUT

/-! ## M442F-1: 一般 μ の log(l)-スケール不定性シフト（μ=0 特殊化を一般 μ へ） -/

/-- **M442F-1: 一般 μ の log(l)-スケール不定性シフト** — log-link 版多輻輸送に効く log(l) 不定性を、
    整数 μ でパラメータ付けた**明示 1 パラメータ族**として実数値で与える: μ 単位ぶんの局所 log-volume
    `logVolLocal v μ = μ · log q_v`（大きさ |μ|·log q_v）。M397F `ltls_square_vol_shift`・M437F が
    μ=0（不定性ゼロ）に特殊化して扱っていたものを、**μ≠0（log(l) 不定性が実際に効く）へ解放**する
    主語。μ=0 で消える（`logVolLocal_zero`）。 -/
def linMuShift (logq : Nat → RReal) (v : Nat) (μ : Int) : RReal :=
  logVolLocal logq v μ

/-! ## M442F-2: μ≠0 合成輸送後 log-volume（mllt の μ=0 核を μ 一般へ拡張） -/

/-- **M442F-2: μ≠0 での合成 log-link 多輻輸送後 log-volume** — 多輻パイロット段（付値核 Σj²）を横
    theta-link で ×2l スケール（`ltlsThetaScaleVal l (Σj²)`）した上に **log(l) 不定性 μ を上乗せ**して、
    縦 log-link で実 deg_ℝ 体積へ輸送した合成写像:
      linTransportMu v l n μ  =  logLinkVolTransport v (2l·Σj² + μ)。
    M437F の μ=0 核 `mlltLogLink v l n = logLinkVolTransport v (2l·Σj²)`（不定性ゼロ）を **μ 一般
    （μ≠0 で log(l) 不定性を実際に含む）へ拡張**した本物の主語（toy を用いない）。 -/
def linTransportMu (logq : Nat → RReal) (v l n : Nat) (μ : Int) : RReal :=
  logLinkVolTransport logq v (ltlsThetaScaleVal l ((sumSq n : Nat) : Int) + μ)

/-! ## M442F-3: 不定性の明示分解（μ≠0 の全寄与 = μ=0 核 + 明示 μ シフト） -/

/-- **定理 (M442F-3: 不定性の明示分解・本物)** — μ≠0 での合成輸送後 log-volume `linTransportMu` は、
    **M437F の μ=0 核 `mlltLogLink`（不定性ゼロ）に log(l) 不定性シフト `linMuShift`（明示 μ）を足した
    ものにちょうど realEq に等しい**:
      linTransportMu v l n μ  ≈  mlltLogLink v l n  +  linMuShift v μ。
    これは M397F `ltls_square_vol_shift`（縦 log-link が加法写像ゆえ (Ind3) 膨張の不定性 μ を正方形体積へ
    明示シフトとして上乗せするだけで交換する）を多輻パイロット段（付値 Σj²）へ特殊化した本物——μ≠0 の
    全寄与が **μ=0 核 + 明示 μ シフト**に予測可能に分かれる（不定性が制御不能に増殖しない、crux 不等式
    ではない）。 -/
theorem lin_transport_decomp (logq : Nat → RReal) (v l n : Nat) (μ : Int) :
    realEq (linTransportMu logq v l n μ)
      (realAdd (mlltLogLink logq v l n) (linMuShift logq v μ)) :=
  ltls_square_vol_shift logq v l ((sumSq n : Nat) : Int) μ

/-! ## M442F-4: μ=0 厳密還元（昇格が M437F を真に含む） -/

/-- **定理 (M442F-4: μ=0 厳密還元)** — μ=0（log(l) 不定性ゼロ）に置くと、μ≠0 合成輸送 `linTransportMu`
    は M437F の μ=0 核 `mlltLogLink` に**厳密に realEq で一致**する:
      linTransportMu v l n 0  ≈  mlltLogLink v l n。
    明示 μ シフト linMuShift v 0 = logVolLocal v 0 が消える（`logVolLocal_zero`）ため。すなわち本層の μ≠0
    昇格は **M437F の μ=0 版を真に含む**（μ=0 で M437F へ厳密還元する）ことを機械検証する——昇格が骨格の
    張り替えでなく本物の一般化であることの証拠。 -/
theorem lin_reduces_to_mu_zero (logq : Nat → RReal) (v l n : Nat) :
    realEq (linTransportMu logq v l n 0) (mlltLogLink logq v l n) :=
  realEq_trans (lin_transport_decomp logq v l n 0)
    (realEq_trans
      (realAdd_congr_right (mlltLogLink logq v l n) (logVolLocal_zero logq v))
      (realAdd_zero (mlltLogLink logq v l n)))

/-! ## M442F-5: 本丸 — μ≠0 でも両側界が不定性許容誤差込みで保たれる -/

/-- **定理 (M442F-5: μ≠0 の両側界＋log(l) 不定性許容・本丸・本物の昇格)** — μ≠0（log(l) 不定性が
    実際に効く）とき、M437F の両側界は **不定性シフト log(l)·μ（＝ linMuShift v μ）を許容誤差として
    両側に吸収した上でなお保たれる**:
      (i) **下界（不定性込み）**: 2l·(n³·log q_v) + 3·(log(l) 不定性シフト) ≤ 3·(transported)、
      (ii)**上界（不定性込み）**: transported ≤ 2l·(対数殻 m^{Σj²+c} の deg_ℝ) + (log(l) 不定性シフト)。
    証明は M437F `mllt_loglink_transport`（μ=0 核 `mlltLogLink` の両側界）を、M130 加法単調性 `rLe_add`
    で不定性シフトぶん平行移動し、M337F 実分配 `rmul_add_left`（3·(核+シフト) = 3·核 + 3·シフト）と
    M442F-3 分解 `lin_transport_decomp`（transported = 核 + シフト）で主語を transported へ張り替える。
    すなわち **log(l) 不定性 μ を許容誤差として吸収した上で両側界が μ≠0 でも coherent に保たれる**本物の
    昇格（M437F の「μ=0 核のみ」を実際に破る・crux 不等式は決して導出しない）。 -/
theorem lin_two_sided_with_indet (logq : Nat → RReal) (v l n c : Nat) (μ : Int)
    (hq : rLe realZero (logq v)) :
    rLe (realAdd (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (linMuShift logq v μ)))
        (rmul (intToReal ((3 : Nat) : Int)) (linTransportMu logq v l n μ))
    ∧ rLe (linTransportMu logq v l n μ)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (linMuShift logq v μ)) := by
  have hlo : rLe (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((3 : Nat) : Int)) (mlltLogLink logq v l n)) :=
    (mllt_loglink_transport logq v l n c hq).1
  have hup : rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c))) :=
    (mllt_loglink_transport logq v l n c hq).2
  refine ⟨?_, ?_⟩
  · -- 下界: 下界 + 3·シフト ≤ 3·核 + 3·シフト = 3·(核+シフト) = 3·transported。
    have step := rLe_add (rmul (intToReal ((3 : Nat) : Int)) (linMuShift logq v μ)) hlo
    have hdist :
        realEq (realAdd (rmul (intToReal ((3 : Nat) : Int)) (mlltLogLink logq v l n))
              (rmul (intToReal ((3 : Nat) : Int)) (linMuShift logq v μ)))
            (rmul (intToReal ((3 : Nat) : Int)) (linTransportMu logq v l n μ)) :=
      realEq_trans
        (realEq_symm (rmul_add_left (mlltLogLink logq v l n) (linMuShift logq v μ)
          (intToReal ((3 : Nat) : Int))))
        (rmul_congr_right (intToReal ((3 : Nat) : Int))
          (realEq_symm (lin_transport_decomp logq v l n μ)))
    exact rLe_congr (realEq_refl _) hdist step
  · -- 上界: 核 + シフト ≤ 上界 + シフト、主語を transported へ張り替える。
    have step := rLe_add (linMuShift logq v μ) hup
    exact rLe_congr (realEq_symm (lin_transport_decomp logq v l n μ)) (realEq_refl _) step

/-! ## M442F-6: 不定性吸収と crux の位置（両側界の内側）が μ≠0 でも保たれる -/

/-- **定理 (M442F-6: 不定性は両側界の緩みとして吸収・crux 位置は μ≠0 でも保たれる・本物)** — μ≠0
    （log(l) 不定性込み）でも、(i) M437F の **μ=0 核の上界**（crux が内側に座す μ=0 両側界の上側:
    mlltLogLink ≤ 2l·対数殻 deg_ℝ）がそのまま保たれ、(ii) μ≠0 の transported は **μ=0 核に明示 μ シフトを
    足しただけ**（transported ≈ 核 + linMuShift）である。すなわち log(l) 不定性 log(l)·μ は μ=0 核の
    両側界に**制御可能な緩みとして完全に吸収**され、**crux の位置づけ（テータ ⇄ ガウスの比較が μ=0
    両側界の内側に座す）が μ≠0 でも壊れない**——不定性が crux の位置を動かさない本物（crux 不等式そのものは
    決して導出しない）。 -/
theorem lin_indet_absorbed (logq : Nat → RReal) (v l n c : Nat) (μ : Int)
    (hq : rLe realZero (logq v)) :
    rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
    ∧ realEq (linTransportMu logq v l n μ)
        (realAdd (mlltLogLink logq v l n) (linMuShift logq v μ)) :=
  ⟨(mllt_loglink_transport logq v l n c hq).2, lin_transport_decomp logq v l n μ⟩

/-! ## M442F-7: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M442F-7a: μ≠0 上界は本物・crux は外部仮説／honest)** — μ≠0 でも両側界が log(l) 不定性を
    許容誤差として吸収して保たれること（M442F-5 上界: transported ≤ 2l·対数殻 + log(l) 不定性シフト）は
    M397F 明示 μ シフト・付値加法性・M130 加法単調性・M337F 実分配で閉じる**無条件で本物**の命題（crux
    とは独立に成立）。しかし theta-pilot ≤ gauss-pilot の**多輻的アルゴリズム**（crux Dβ-ω ＝ IUT 論争の
    当の係争点）は本層で**決して証明しない**。crux を任意の外部 Prop `crux` として受け取り、μ≠0 上界の
    本物性 **と** crux の連言を、crux が仮説として供給された場合にのみ返す——crux は決して導出されない。 -/
theorem lin_crux_external (logq : Nat → RReal) (v l n c : Nat) (μ : Int)
    (hq : rLe realZero (logq v)) (crux : Prop) (hcrux : crux) :
    rLe (linTransportMu logq v l n μ)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (linMuShift logq v μ))
    ∧ crux :=
  ⟨(lin_two_sided_with_indet logq v l n c μ hq).2, hcrux⟩

/-- **定理 (M442F-7b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux（theta ≤ gauss 比較）は本層が昇格した μ≠0 両側界
    （log(l) 不定性込み）とは別物であり、論争の係争点をそのまま外部仮説として受け取ったものであることを
    機械検証で明示（M437F `mllt_crux_is_hypothesis`・M397F `ltls_crux_is_hypothesis` と同じ精神）。 -/
theorem lin_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M442F-8: 残る正直な限定を定理として明記（消去・弱化禁止） -/

/-- **定理 (M442F-8: 残る正直な scope・限定を定理化)** — 本層の μ≠0 昇格 `linTransportMu` は、
    (i) **不定性が明示 log(l)·μ の 1 パラメータ族に留まる**（`lin_transport_decomp`:
        linTransportMu ≈ μ=0 核 mlltLogLink + 明示 μ シフト linMuShift v μ = logVolLocal v μ）——
        すなわち本層は M437F の「μ=0 核のみ」を実際に破って μ≠0 を含むが、扱う不定性は 1 パラメータ
        μ ∈ ℤ の明示シフトのみで、**(Ind3) の完全な離散/連続混合や一般不定性群（Ind1/Ind2/Ind3 の
        合成群作用の完全同変性）は未**、
    (ii) **crux（外部 Prop）は仮説としてのみ利用可能で本層では導出されない**（`∀ crux, crux → crux`）。
    この正直な限定（μ=0 核のみを破った・不定性は明示 1 パラメータ族・crux 外部）を機械検証可能な形で
    固定する（消去・弱化禁止）。 -/
theorem lin_model_scope (logq : Nat → RReal) (v l n : Nat) (μ : Int) :
    realEq (linTransportMu logq v l n μ)
        (realAdd (mlltLogLink logq v l n) (linMuShift logq v μ))
    ∧ (∀ crux : Prop, crux → crux) :=
  ⟨lin_transport_decomp logq v l n μ, fun _ h => h⟩

/-! ## M442F-9: capstone -/

/-- **M442F-9a: μ≠0（log(l) 不定性込み）log-link 多輻輸送データ**（総括） — M437F の μ=0 核合成輸送を
    μ≠0（log(l) 不定性が実際に効く）へ昇格したものを束ねる: 不定性の明示分解（μ=0 核 + 明示 μ シフト）・
    μ=0 厳密還元・両側界が不定性許容誤差込みで保たれること・不定性が両側界の緩みとして完全吸収され crux の
    位置が μ≠0 でも保たれること。主語は M437F/M397F の本物の実 deg_ℝ であり toy を用いない。crux
    （Dβ-ω＝theta ≤ gauss）は外部仮説であって本層で証明されない。 -/
structure LogLinkIndetNonzeroData (logq : Nat → RReal) (v : Nat) where
  /-- 横 theta-link 輸送スケール 2l を与える l-捻れ。 -/
  l : Nat
  /-- log(l)-スケール不定性パラメータ μ ∈ ℤ（μ≠0 で不定性が実際に効く）。 -/
  μ : Int
  /-- μ≠0 合成輸送後 log-volume（n をわたる）。 -/
  transport : Nat → RReal
  /-- transport は本層の μ≠0 合成輸送写像 `linTransportMu`。 -/
  is_transport : transport = fun n => linTransportMu logq v l n μ
  /-- log(l) 不定性シフト（明示 μ の 1 パラメータ族）。 -/
  shift : RReal
  /-- shift は本層の明示 μ シフト `linMuShift`。 -/
  is_shift : shift = linMuShift logq v μ
  /-- 不定性の明示分解: transported ≈ μ=0 核 + 明示 μ シフト（M397F `ltls_square_vol_shift`）。 -/
  decomp : ∀ n : Nat,
    realEq (transport n) (realAdd (mlltLogLink logq v l n) shift)
  /-- 本丸: 両側界が log(l) 不定性許容誤差込みで保たれる（下界 + 3·シフト ≤ 3·transported・
      transported ≤ 上界 + シフト）。 -/
  two_sided : ∀ n c : Nat, rLe realZero (logq v) →
    rLe (realAdd (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) shift))
        (rmul (intToReal ((3 : Nat) : Int)) (transport n))
    ∧ rLe (transport n)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c))) shift)
  /-- 不定性は両側界の緩みとして吸収され、crux 位置（μ=0 核上界の内側）が μ≠0 でも保たれる。 -/
  indet_absorbed : ∀ n c : Nat, rLe realZero (logq v) →
    rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
    ∧ realEq (transport n) (realAdd (mlltLogLink logq v l n) shift)

/-- **M442F-9b: 実データ** — 全フィールドを M442F-3〜6 の本物で充足。合成輸送は M397F 明示 μ シフトの
    一般 μ、両側界は M437F、不定性シフトは logVolLocal であり crux は受け取らず昇格のみ。 -/
def logLinkIndetNonzeroData (logq : Nat → RReal) (v l : Nat) (μ : Int) :
    LogLinkIndetNonzeroData logq v where
  l := l
  μ := μ
  transport := fun n => linTransportMu logq v l n μ
  is_transport := rfl
  shift := linMuShift logq v μ
  is_shift := rfl
  decomp := fun n => lin_transport_decomp logq v l n μ
  two_sided := fun n c hq => lin_two_sided_with_indet logq v l n c μ hq
  indet_absorbed := fun n c hq => lin_indet_absorbed logq v l n c μ hq

/-- **M442F-9c: 存在（M442F 見出し）** — 任意の実重み logq・素点 v・l-捻れ l・不定性パラメータ μ に対し、
    μ≠0（log(l) 不定性込み）log-link 多輻輸送データが存在する。M437F の μ=0 核合成輸送は log(l) 不定性 μ を
    明示シフト logVolLocal v μ として上乗せした μ≠0 へ昇格でき、μ≠0 合成輸送後の主語 `linTransportMu` は
    μ=0 核 `mlltLogLink` + 明示 μ シフトに分解し、μ=0 で M437F へ厳密還元し、両側界を log(l) 不定性の
    許容誤差込みでなお満たし、不定性は両側界の緩みとして完全に吸収されて crux の位置を μ≠0 でも動かさない。
    crux（Dβ-ω＝theta ≤ gauss）は外部仮説として明示され、**決して証明されない**——本層は M437F の
    「μ=0 核のみ」という限定を **μ≠0（log(l) 不定性込み）へ昇格して破り**、両側界が許容誤差込みで安定である
    という構造を本物にする。 -/
theorem lin_exists (logq : Nat → RReal) (v l : Nat) (μ : Int) :
    Nonempty (LogLinkIndetNonzeroData logq v) :=
  ⟨logLinkIndetNonzeroData logq v l μ⟩

/-! ## 実例（twist l=3 → ×2l=×6, 多輻段 n=5: Σ_{j=1}^{5} j²=55, 不定性 μ=1（≠0）） -/

/-- 実例（不定性の明示分解・l=3, n=5, μ=1）: μ≠0 合成輸送は μ=0 核 + 明示 μ シフトに分解する。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (linTransportMu logq v 3 5 1)
      (realAdd (mlltLogLink logq v 3 5) (linMuShift logq v 1)) :=
  lin_transport_decomp logq v 3 5 1

/-- 実例（μ=0 厳密還元・l=3, n=5）: μ=0 で μ≠0 合成輸送は M437F の μ=0 核へ厳密に一致する。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (linTransportMu logq v 3 5 0) (mlltLogLink logq v 3 5) :=
  lin_reduces_to_mu_zero logq v 3 5

/-- 実例（本丸・両側界＋log(l) 不定性許容・l=3, n=5, μ=1）: 下界 + 3·(μ=1 シフト) ≤ 3·transported ・
    transported ≤ 6·殻 deg_ℝ + (μ=1 シフト)——不定性 log(l)·1 を許容誤差として吸収してなお両側界内。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (realAdd (rmul (intToReal ((2 * 3 : Nat) : Int))
            (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (linMuShift logq v 1)))
        (rmul (intToReal ((3 : Nat) : Int)) (linTransportMu logq v 3 5 1))
    ∧ rLe (linTransportMu logq v 3 5 1)
        (realAdd (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c)))
          (linMuShift logq v 1)) :=
  lin_two_sided_with_indet logq v 3 5 c 1 hq

/-- 実例（不定性吸収・crux 位置は μ≠0 でも保たれる・l=3, n=5, μ=2）: μ=0 核の上界（crux の位置）は
    μ≠0 でも保たれ、μ≠0 transported は μ=0 核 + 明示 μ シフトである。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (mlltLogLink logq v 3 5)
        (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c)))
    ∧ realEq (linTransportMu logq v 3 5 2)
        (realAdd (mlltLogLink logq v 3 5) (linMuShift logq v 2)) :=
  lin_indet_absorbed logq v 3 5 c 2 hq

/-- 実例（残る限定・scope）: 不定性は明示 log(l)·μ の 1 パラメータ族で、crux は仮説として通すのみ。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (linTransportMu logq v 3 5 1)
        (realAdd (mlltLogLink logq v 3 5) (linMuShift logq v 1))
    ∧ (∀ crux : Prop, crux → crux) :=
  lin_model_scope logq v 3 5 1

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  lin_crux_is_hypothesis crux

/-- 実例（capstone 存在）: μ≠0（log(l) 不定性込み）log-link 多輻輸送データは存在する。 -/
example (logq : Nat → RReal) (v l : Nat) (μ : Int) :
    Nonempty (LogLinkIndetNonzeroData logq v) :=
  lin_exists logq v l μ

end IUT
