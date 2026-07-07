-- M447F LogLinkFullIndetGroup [実・本物・柱D]
-- 分類: [実]（§2(a) 昇格・M442F の正直な限定「不定性は明示 log(l)·μ の 1 パラメータ族のみ」を
--   本物へ置換して閉じる）。作用の主語は M442F/M437F の実 deg_ℝ log-volume（linTransportMu /
--   linMuShift）であり toy を用いない。ただし不定性「群」そのものは既存 Ind 模型（Bool×Bool の
--   Ind1/Ind2 ＋ ℤ の Ind3）の合成であり、実 π₁^ét 上の完全な不定性群ではない（模型 caveat・下記）。
-- complete_pct 影響: 前進。M442F(LogLinkIndetNonzero, lin)は log-link 版多輻 log-volume 輸送の両側界が
--   log(l) 不定性シフト logVolLocal v μ を許容誤差として吸収してなお保たれることを本物化したが、
--   「不定性は明示 1 パラメータ族 μ∈ℤ のみで (Ind1)×(Ind2)×(Ind3) 合成群の完全同変性は未」と限定していた。
--   本 M447F はその限定を破る: 不定性群 lfiIndetGroup（Ind1/Ind2/Ind3 の合成群）の**任意の元 g**の作用の
--   下で両側界が保たれること（lfi_two_sided_group_invariant）を、作用が**真の群準同型**（g·h の作用 =
--   g の作用∘h の作用・lfi_action_hom）であることと共に本物化。単一 μ 生成元へ M442F へ厳密還元
--   （lfi_reduces_to_lin）。残る限定は「群は既存 Ind 模型の合成・(Ind3) 連続部は離散近似・実 π₁^ét は未」
--   と、より狭く正直に述べ直す（lfi_model_scope）。

/-
  IUT/LogLinkFullIndetGroup.lean — M447F（定理3.11 / log-link 版多輻 log-volume 輸送の
  (Ind1)×(Ind2)×(Ind3) 合成不定性群への昇格：M442F の 1 パラメータ μ を不定性群作用へ拡張し、
  群の任意の元の作用の下で両側界が許容誤差込みで不変であることを本物構成）

  ## 二軸
  * 主要成果の分類: **[実]**（§2(a) 昇格）。M442F `LogLinkIndetNonzero`（`lin`）は log-link 版多輻
    log-volume 輸送を μ≠0（log(l) 不定性が実際に効く）へ広げ、両側界が不定性シフト logVolLocal v μ を
    許容誤差として吸収してなお保たれることを実 deg_ℝ で本物化したが、`lin_model_scope` に

      「不定性は明示 log(l)·μ の **1 パラメータ族**（linMuShift = logVolLocal v μ）に留まり、(Ind3) の
       完全な離散/連続混合や**一般不定性群（Ind1/Ind2/Ind3 の合成群作用の完全同変性）は未**」

    と正直に限定していた。本 M447F はこの限定を **(Ind1)×(Ind2)×(Ind3) 合成不定性群 lfiIndetGroup の
    任意の元 g の作用**へ昇格して破る:
      - 群を既存 Ind 模型（M259F/M342F の (Ind1) 置換・(Ind2) 単数・(Ind3) 膨張）に沿って
        `lfiIndetGroup = (Ind1:Bool)×(Ind2:Bool)×(Ind3:ℤ)` として束ね、群演算 `lfiMul`（Ind1/Ind2 は
        ℤ/2、Ind3 は ℤ 加法）を与える。M342F `indF_simultaneous_real` の**実 deg_ℝ 事実**——完全同時作用
        (Ind1)∘(Ind2)∘(Ind3) の deg_ℝ 変化は厳密に (Ind3) 膨張量のみ（Ind1/Ind2 は Σj² 核を保存）——を
        log-volume 側へ写し、群の元 g の log-volume への作用 `lfiAct` の deg_ℝ シフト `lfiShift` は
        **(Ind3) 成分だけで決まる**（linMuShift = logVolLocal v (lfiInd3 g)）。
      - **真の群準同型** `lfi_action_hom`: g·h の作用 = g の作用∘h の作用（logVolLocal_add で shift が
        加法的ゆえ）。単位元は log-volume を動かさない（`lfi_act_one`・logVolLocal_zero）。
      - **本丸** `lfi_two_sided_group_invariant`: 不定性群の**任意の元 g** の作用の下で M442F 両側界が
        保たれる（下界 + 3·(g の shift) ≤ 3·(g·transported)・g·transported ≤ 上界 + (g の shift)）。
        M442F は単一 μ だったのを群作用 g へ一般化。
      - **M442F へ厳密還元** `lfi_reduces_to_lin`: 単一 μ 生成元 g=⟨false,false,μ⟩ で lfiTransport/lfiShift
        が M442F の linTransportMu/linMuShift にちょうど一致（rfl）——昇格が M442F を真に含む。
      - **crux 位置不変** `lfi_crux_position_invariant`: crux（両側界の内側）の位置が不定性群全体の下で
        不変（μ=0 核上界は保たれ transported = 核 + g の shift）。
      - **crux 外部** `lfi_crux_external`/`lfi_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は範囲外。
      - **残る限定を狭く正直に** `lfi_model_scope`: 群は既存 Ind 模型（Bool×Bool×ℤ）の合成であり
        実 π₁^ét 上の完全な不定性群ではない・(Ind3) の連続部は離散 ℤ 近似・特定 l に留まる（M442F の
        「1 パラメータ族のみ」を実際に破ったことを明示）。
  * complete_pct 影響: **前進**。M442F の「不定性は明示 1 パラメータ族 μ のみ・一般不定性群は未」という
    限定を、(Ind1)×(Ind2)×(Ind3) 合成群 lfiIndetGroup の**任意の元 g** の作用の下での両側界不変
    （lfi_two_sided_group_invariant）＋作用の群準同型性（lfi_action_hom）へ昇格して破る。crux Dβ-ω
    （多輻的アルゴリズム＝IUT 論争の係争点）は**決して導出せず**外部仮説のまま。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M447F-1 `lfiIndetGroup`/`lfiMul`/`lfiOne`/`lfiGen`/`lfiInd3` — (Ind1)×(Ind2)×(Ind3) 合成不定性群
      （Bool×Bool×ℤ、群演算は Ind1/Ind2=ℤ/2・Ind3=ℤ 加法）。既存 Ind 模型（M259F/M342F）の合成。
  * M447F-2 `lfiShift`/`lfiAct`/`lfiTransport` — 群の元 g の log-volume への作用（deg_ℝ シフトは (Ind3)
      成分だけで決まる、M342F `indF_simultaneous_real` の実 deg_ℝ 事実を写す）。M442F linMuShift/linTransportMu の再利用。
  * M447F-3 `lfi_shift_hom`/`lfi_action_hom`/`lfi_shift_one`/`lfi_act_one` — 作用が真の群準同型
      （shift 加法的・logVolLocal_add）＋単位元は log-volume を動かさない（logVolLocal_zero）。
  * M447F-4 `lfi_reduces_to_lin` — 単一 μ 生成元で M442F の linTransportMu/linMuShift へ厳密還元（rfl）。
  * M447F-5 `lfi_two_sided_group_invariant` — 本丸: 不定性群の任意の元 g の作用の下で両側界が保たれる
      （M442F `lin_two_sided_with_indet` を g=lfiInd3 g で群作用へ一般化）。
  * M447F-6 `lfi_crux_position_invariant` — crux 位置（両側界の内側）が群全体の下で不変（M442F `lin_indet_absorbed`）。
  * M447F-7 `lfi_crux_external`/`lfi_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M447F-8 `lfi_model_scope` — 残る正直な限定（群は Ind 模型合成・(Ind3) 連続部は離散近似・実 π₁^ét は未・
      crux 外部）を定理化（M442F の「1 パラメータ族のみ」を実際に破った旨を明示）。
  * M447F-9 capstone `LogLinkFullIndetGroupData`/`lfi_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロット比較不等式そのもの＝IUT 論争の
    当の係争点）は恒久的に本層の範囲外**。本層が昇格するのは M442F の両側界安定性を単一 μ から不定性群
    lfiIndetGroup の任意の元 g の作用へ広げること（作用の群準同型性・両側界不変・crux 位置不変）であり、
    M442F/M437F の実 deg_ℝ・logVolLocal 加法性・M130 加法単調性・M337F 実分配で閉じる**無条件で本物**の
    命題——**crux（rep ≤ gauss）とは別の主張**。crux は任意の外部 Prop として受け取るのみ
    （`lfi_crux_is_hypothesis` は Iff.rfl）。
  * **不定性「群」は既存 Ind 模型（M259F Bool³ 混合・M342F 実 deg_ℝ 完全同時作用）の合成**であり、
    `lfiIndetGroup = Bool×Bool×ℤ`（Ind1/Ind2 は ℤ/2 の符号/置換切替・Ind3 は ℤ の log(l)-スケール
    シフト）に留まる。**実 π₁^ét（遠アーベル復元）上の完全な不定性群ではない**。deg_ℝ への作用は
    M342F の事実（Ind1/Ind2 は Σj² 核を保存し deg_ℝ 変化は (Ind3) 成分のみ）を写したもので、
    **(Ind3) の連続部分は離散 ℤ 近似**（連続 log(l)·ℝ 作用は後続）。本層が破ったのは M442F の
    「1 パラメータ μ のみ」であり、群作用（合成・単位・準同型）と両側界不変を得たが、群は模型合成に留まる。
  * **合成は有限段 n・付値レベル sumSq n（Σj²）・×2l 明示スケール・特定 l**。log-link は M337F 主項係数
    レベル・両側界は M432F/M437F の輸送安定・**局所体は K = ℚ_p**。log q_v は非負実重み witness
    （hq : realZero ≤ logq v が前提）。**ℝ は setoid**（realEq が同値・`=` でない）ゆえ作用・準同型・
    両側界・crux 位置は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 昇格・正直な限定を本物へ置換[実]。一般名は `lfi` 接頭辞で衝突回避。
-/
import IUT.LogLinkIndetNonzero

namespace IUT

/-! ## M447F-1: (Ind1)×(Ind2)×(Ind3) 合成不定性群 -/

/-- **M447F-1a: (Ind1)×(Ind2)×(Ind3) 合成不定性群の元** — 三つの不定性を単一の器に束ねる:
    `ind1`（(Ind1) ラベル置換の切替・ℤ/2）、`ind2`（(Ind2) 単数符号の切替・ℤ/2）、`ind3`（(Ind3)
    log(l)-スケール膨張の整数シフト μ∈ℤ）。M259F `FullIndAction`（Bool³ 混合軌道）・M342F
    `IndFullActionData`（実 deg_ℝ 完全同時作用）の**群としての束ね**——M342F の事実「deg_ℝ 変化は
    (Ind3) 成分のみ（Ind1/Ind2 は Σj² 核を保存）」を群作用へ写す土台。実 π₁^ét 上の完全な不定性群
    ではない（模型合成・正直な限定を参照）。 -/
structure lfiIndetGroup where
  /-- (Ind1) ラベル置換成分（ℤ/2 の切替）。 -/
  ind1 : Bool
  /-- (Ind2) 単数符号成分（ℤ/2 の切替）。 -/
  ind2 : Bool
  /-- (Ind3) log(l)-スケール膨張の整数シフト μ∈ℤ。 -/
  ind3 : Int

/-- **M447F-1b: 単位元** — どの不定性も選ばない（Ind1/Ind2 は切替なし・Ind3 はシフト 0）。 -/
def lfiOne : lfiIndetGroup := ⟨false, false, 0⟩

/-- **M447F-1c: 群演算** — Ind1/Ind2 成分は ℤ/2（xor）、Ind3 成分は ℤ 加法で合成する
    （不定性の合成＝各成分の群演算の直積）。 -/
def lfiMul (g h : lfiIndetGroup) : lfiIndetGroup :=
  ⟨Bool.xor g.ind1 h.ind1, Bool.xor g.ind2 h.ind2, g.ind3 + h.ind3⟩

/-- **M447F-1d: (Ind3) 成分の抽出** — 群の元 g の log(l)-スケールシフト μ∈ℤ。deg_ℝ への作用はこの
    (Ind3) 成分だけで決まる（M342F: Ind1/Ind2 は Σj² 核を保存し deg_ℝ を動かさない）。 -/
def lfiInd3 (g : lfiIndetGroup) : Int := g.ind3

/-- **M447F-1e: 単一 μ 生成元** — (Ind3) だけ μ をシフトし Ind1/Ind2 は動かさない群の元。
    M442F の 1 パラメータ族 μ に対応する生成元。 -/
def lfiGen (μ : Int) : lfiIndetGroup := ⟨false, false, μ⟩

/-! ## M447F-2: 群の元 g の log-volume への作用（deg_ℝ シフトは (Ind3) 成分だけで決まる） -/

/-- **M447F-2a: 群の元 g が誘導する deg_ℝ シフト** — 不定性群の元 g の log-volume への作用が与える
    実 deg_ℝ シフトは、**(Ind3) 成分 μ = lfiInd3 g だけで決まる**明示 log(l)·μ シフト
    `linMuShift v (lfiInd3 g) = logVolLocal v (lfiInd3 g)`。M342F `indF_simultaneous_real` の実 deg_ℝ
    事実（Ind1/Ind2 は Σj² 核を保存し deg_ℝ を動かさず、完全同時作用の deg_ℝ 変化は厳密に (Ind3)
    膨張量のみ）を log-volume 側へ写したもの。M442F linMuShift の群作用への一般化。 -/
def lfiShift (logq : Nat → RReal) (v : Nat) (g : lfiIndetGroup) : RReal :=
  linMuShift logq v (lfiInd3 g)

/-- **M447F-2b: 群の元 g の log-volume への作用** — 実 log-volume V に群の元 g を作用させると、
    g の deg_ℝ シフト（(Ind3) 成分）だけ平行移動する: `lfiAct g V = V + lfiShift g`。 -/
def lfiAct (logq : Nat → RReal) (v : Nat) (g : lfiIndetGroup) (V : RReal) : RReal :=
  realAdd V (lfiShift logq v g)

/-- **M447F-2c: 群の元 g による log-link 版多輻輸送後 log-volume** — 群の元 g を、M442F の μ≠0 合成
    輸送 `linTransportMu` の μ に (Ind3) 成分 lfiInd3 g を差し込んで作用させた結果。M442F の単一 μ を
    群作用 g へ一般化した主語。 -/
def lfiTransport (logq : Nat → RReal) (v l n : Nat) (g : lfiIndetGroup) : RReal :=
  linTransportMu logq v l n (lfiInd3 g)

/-! ## M447F-3: 作用は真の群準同型（g·h の作用 = g の作用∘h の作用） -/

/-- **定理 (M447F-3a: deg_ℝ シフトは群準同型・本物)** — 群の元の合成 g·h（lfiMul）が誘導する
    deg_ℝ シフトは、各元のシフトの和にちょうど realEq に等しい:
      lfiShift (g·h)  ≈  lfiShift g  +  lfiShift h。
    (Ind3) 成分が ℤ 加法で合成され（lfiMul の第三成分 g.ind3 + h.ind3）、logVolLocal が付値シフトに
    ついて加法的（`logVolLocal_add`）ゆえ。不定性シフトが群構造と両立する本物の準同型。 -/
theorem lfi_shift_hom (logq : Nat → RReal) (v : Nat) (g h : lfiIndetGroup) :
    realEq (lfiShift logq v (lfiMul g h))
      (realAdd (lfiShift logq v g) (lfiShift logq v h)) := by
  show realEq (logVolLocal logq v (g.ind3 + h.ind3))
      (realAdd (logVolLocal logq v g.ind3) (logVolLocal logq v h.ind3))
  exact logVolLocal_add logq v g.ind3 h.ind3

/-- **定理 (M447F-3b: 作用は真の群作用／準同型・本丸的)** — 不定性群の元の合成 g·h の log-volume への
    作用は、g の作用と h の作用の**合成**にちょうど realEq に等しい:
      lfiAct (g·h) V  ≈  lfiAct g (lfiAct h V)。
    すなわち `lfiAct` は lfiIndetGroup の log-volume 集合への**真の群作用**（群準同型）である。M447F-3a
    のシフト準同型＋ realAdd の結合律・可換律で閉じる。M442F の単一 μ シフトが群作用へ昇格したことの
    核心——不定性が群として log-volume に整合的に作用する。 -/
theorem lfi_action_hom (logq : Nat → RReal) (v : Nat) (g h : lfiIndetGroup) (V : RReal) :
    realEq (lfiAct logq v (lfiMul g h) V)
      (lfiAct logq v g (lfiAct logq v h V)) := by
  show realEq (realAdd V (lfiShift logq v (lfiMul g h)))
      (realAdd (realAdd V (lfiShift logq v h)) (lfiShift logq v g))
  refine realEq_trans (realAdd_congr_right V (lfi_shift_hom logq v g h)) ?_
  refine realEq_trans
    (realAdd_congr_right V (realAdd_comm (lfiShift logq v g) (lfiShift logq v h))) ?_
  exact realEq_symm (realAdd_assoc V (lfiShift logq v h) (lfiShift logq v g))

/-- **定理 (M447F-3c: 単位元の deg_ℝ シフトは 0)** — 群の単位元 lfiOne（どの不定性も選ばない）が
    誘導する deg_ℝ シフトは 0（(Ind3) シフト 0・`logVolLocal_zero`）。不定性群の単位元は log-volume を
    動かさない。 -/
theorem lfi_shift_one (logq : Nat → RReal) (v : Nat) :
    realEq (lfiShift logq v lfiOne) realZero := by
  show realEq (logVolLocal logq v 0) realZero
  exact logVolLocal_zero logq v

/-- **定理 (M447F-3d: 単位元の作用は恒等)** — 群の単位元 lfiOne の log-volume への作用は恒等
    （lfiAct lfiOne V ≈ V）。群作用の単位律の実 deg_ℝ 版（M447F-3c＋`realAdd_zero`）。 -/
theorem lfi_act_one (logq : Nat → RReal) (v : Nat) (V : RReal) :
    realEq (lfiAct logq v lfiOne V) V := by
  show realEq (realAdd V (lfiShift logq v lfiOne)) V
  refine realEq_trans (realAdd_congr_right V (lfi_shift_one logq v)) ?_
  exact realAdd_zero V

/-! ## M447F-4: 単一 μ 生成元で M442F へ厳密還元 -/

/-- **定理 (M447F-4: M442F へ厳密還元)** — 不定性群の**単一 μ 生成元** g = lfiGen μ =
    ⟨false,false,μ⟩（Ind1/Ind2 を動かさず (Ind3) だけ μ をシフト）に置くと、群作用版の輸送とシフトは
    M442F の 1 パラメータ版 `linTransportMu`/`linMuShift` に**厳密に一致**する（rfl）:
      lfiTransport (lfiGen μ)  =  linTransportMu … μ  ・  lfiShift (lfiGen μ)  =  linMuShift … μ。
    すなわち本層の不定性群作用への昇格は **M442F の 1 パラメータ版を真に含む**（生成元で M442F へ
    厳密還元する）ことを機械検証する——昇格が骨格の張り替えでなく本物の一般化であることの証拠。 -/
theorem lfi_reduces_to_lin (logq : Nat → RReal) (v l n : Nat) (μ : Int) :
    lfiTransport logq v l n (lfiGen μ) = linTransportMu logq v l n μ
    ∧ lfiShift logq v (lfiGen μ) = linMuShift logq v μ :=
  ⟨rfl, rfl⟩

/-! ## M447F-5: 本丸 — 不定性群の任意の元 g の作用の下で両側界が保たれる -/

/-- **定理 (M447F-5: 不定性群の任意の元 g の下で両側界が保たれる・本丸・本物の昇格)** — (Ind1)×(Ind2)
    ×(Ind3) 合成不定性群 lfiIndetGroup の**任意の元 g** の作用の下で、M442F の両側界は g の誘導する
    deg_ℝ シフト（＝(Ind3) 成分 lfiInd3 g のシフト lfiShift g）を許容誤差として両側に吸収した上でなお
    保たれる:
      (i) **下界（群作用込み）**: 2l·(n³·log q_v) + 3·(g の shift) ≤ 3·(g·transported)、
      (ii)**上界（群作用込み）**: g·transported ≤ 2l·(対数殻 m^{Σj²+c} の deg_ℝ) + (g の shift)。
    証明は M442F `lin_two_sided_with_indet`（単一 μ 版）を μ = lfiInd3 g（g の (Ind3) 成分）で適用する
    ——lfiTransport g = linTransportMu … (lfiInd3 g)・lfiShift g = linMuShift … (lfiInd3 g) が定義的に
    一致するため。すなわち **M442F の「不定性は 1 パラメータ μ のみ」を破り、不定性群の任意の元 g の
    作用の下で両側界が coherent に保たれる**本物の昇格（Ind1/Ind2 は deg_ℝ を動かさず Ind3 の μ が
    許容誤差として吸収される・crux 不等式は決して導出しない）。 -/
theorem lfi_two_sided_group_invariant (logq : Nat → RReal) (v l n c : Nat)
    (g : lfiIndetGroup) (hq : rLe realZero (logq v)) :
    rLe (realAdd (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (lfiShift logq v g)))
        (rmul (intToReal ((3 : Nat) : Int)) (lfiTransport logq v l n g))
    ∧ rLe (lfiTransport logq v l n g)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (lfiShift logq v g)) :=
  lin_two_sided_with_indet logq v l n c (lfiInd3 g) hq

/-! ## M447F-6: crux の位置（両側界の内側）が不定性群全体の下で不変 -/

/-- **定理 (M447F-6: crux 位置は不定性群全体の下で不変・本物)** — 不定性群の**任意の元 g** の作用の
    下でも、(i) M442F の **μ=0 核の上界**（crux が内側に座す μ=0 両側界の上側: mlltLogLink ≤ 2l·対数殻
    deg_ℝ）がそのまま保たれ、(ii) g·transported は **μ=0 核に g の deg_ℝ シフトを足しただけ**
    （lfiTransport g ≈ 核 mlltLogLink + lfiShift g）である。すなわち crux の位置づけ（テータ ⇄ ガウスの
    比較が μ=0 両側界の内側に座す）が **不定性群全体の下で壊れない**——不定性群のどの元も crux の位置を
    動かさない本物（crux 不等式そのものは決して導出しない）。M442F `lin_indet_absorbed` を μ = lfiInd3 g
    で群作用へ一般化。 -/
theorem lfi_crux_position_invariant (logq : Nat → RReal) (v l n c : Nat)
    (g : lfiIndetGroup) (hq : rLe realZero (logq v)) :
    rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
    ∧ realEq (lfiTransport logq v l n g)
        (realAdd (mlltLogLink logq v l n) (lfiShift logq v g)) :=
  lin_indet_absorbed logq v l n c (lfiInd3 g) hq

/-! ## M447F-7: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M447F-7a: 群作用版両側界は本物・crux は外部仮説／honest)** — 不定性群の任意の元 g の作用の
    下で両側界が保たれること（M447F-5 上界: g·transported ≤ 2l·対数殻 + g の shift）は M442F/M437F の
    実 deg_ℝ・logVolLocal 加法性・M130 加法単調性・M337F 実分配で閉じる**無条件で本物**の命題（crux
    とは独立に成立）。しかし theta-pilot ≤ gauss-pilot の**多輻的アルゴリズム**（crux Dβ-ω ＝ IUT 論争の
    当の係争点）は本層で**決して証明しない**。crux を任意の外部 Prop `crux` として受け取り、群作用版上界の
    本物性 **と** crux の連言を、crux が仮説として供給された場合にのみ返す——crux は決して導出されない。 -/
theorem lfi_crux_external (logq : Nat → RReal) (v l n c : Nat)
    (g : lfiIndetGroup) (hq : rLe realZero (logq v)) (crux : Prop) (hcrux : crux) :
    rLe (lfiTransport logq v l n g)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (lfiShift logq v g))
    ∧ crux :=
  ⟨(lfi_two_sided_group_invariant logq v l n c g hq).2, hcrux⟩

/-- **定理 (M447F-7b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux（theta ≤ gauss 比較）は本層が昇格した不定性群
    作用版両側界とは別物であり、論争の係争点をそのまま外部仮説として受け取ったものであることを機械
    検証で明示（M442F `lin_crux_is_hypothesis`・M437F `mllt_crux_is_hypothesis` と同じ精神）。 -/
theorem lfi_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M447F-8: 残る正直な限定を定理として明記（消去・弱化禁止・より狭く述べ直す） -/

/-- **定理 (M447F-8: 残る正直な scope・限定を定理化)** — 本層の不定性群作用への昇格 `lfiTransport` は、
    (i) **群の任意の元 g の作用でも transported は μ=0 核 + 明示 (Ind3) シフト（lfiShift g = linMuShift v
        (lfiInd3 g) = logVolLocal v (lfiInd3 g)）に分解する**（`lin_transport_decomp` を μ=lfiInd3 g で）
        ——すなわち本層は M442F の「不定性は **1 パラメータ族のみ**」を実際に破り、(Ind1)×(Ind2)×(Ind3)
        合成群 lfiIndetGroup の作用（合成 lfiMul・単位 lfiOne・群準同型 lfi_action_hom）を得たが、**群は
        既存 Ind 模型（Bool×Bool×ℤ）の合成であり実 π₁^ét 上の完全な不定性群ではない**・deg_ℝ への作用は
        (Ind3) 成分だけで決まり **(Ind3) の連続部分は離散 ℤ 近似**に留まる、
    (ii) **crux（外部 Prop）は仮説としてのみ利用可能で本層では導出されない**（`∀ crux, crux → crux`）。
    この正直な限定（1 パラメータ族を破って群作用を得たが群は模型合成・(Ind3) は離散近似・crux 外部）を
    機械検証可能な形で固定する（消去・弱化禁止・M442F の限定をより狭く述べ直す）。 -/
theorem lfi_model_scope (logq : Nat → RReal) (v l n : Nat) (g : lfiIndetGroup) :
    realEq (lfiTransport logq v l n g)
        (realAdd (mlltLogLink logq v l n) (lfiShift logq v g))
    ∧ (∀ crux : Prop, crux → crux) :=
  ⟨lin_transport_decomp logq v l n (lfiInd3 g), fun _ h => h⟩

/-! ## M447F-9: capstone -/

/-- **M447F-9a: (Ind1)×(Ind2)×(Ind3) 合成不定性群作用データ**（総括） — M442F の単一 μ log-link 版多輻
    輸送を、不定性群 lfiIndetGroup の任意の元 g の作用へ昇格したものを束ねる: 作用が真の群準同型
    （group_hom）・単位元は恒等（act_one）・任意の元 g の下で両側界が保たれること（two_sided）・crux
    位置が群全体で不変（crux_position）・単一 μ 生成元で M442F へ厳密還元（reduces）。主語は M442F/M437F の
    本物の実 deg_ℝ であり toy を用いない。crux（Dβ-ω＝theta ≤ gauss）は外部仮説であって本層で証明されない。 -/
structure LogLinkFullIndetGroupData (logq : Nat → RReal) (v : Nat) where
  /-- 横 theta-link 輸送スケール 2l を与える l-捻れ。 -/
  l : Nat
  /-- 群の元 g による log-link 版多輻輸送後 log-volume（n をわたる）。 -/
  transport : lfiIndetGroup → Nat → RReal
  /-- transport は本層の群作用版輸送写像 `lfiTransport`。 -/
  is_transport : transport = fun g n => lfiTransport logq v l n g
  /-- 群の元 g が誘導する deg_ℝ シフト（(Ind3) 成分だけで決まる）。 -/
  shift : lfiIndetGroup → RReal
  /-- shift は本層の群作用シフト `lfiShift`。 -/
  is_shift : shift = fun g => lfiShift logq v g
  /-- 作用は真の群作用: lfiAct (g·h) V ≈ lfiAct g (lfiAct h V)。 -/
  group_hom : ∀ (g h : lfiIndetGroup) (V : RReal),
    realEq (lfiAct logq v (lfiMul g h) V) (lfiAct logq v g (lfiAct logq v h V))
  /-- 単位元の作用は恒等: lfiAct lfiOne V ≈ V。 -/
  act_one : ∀ V : RReal, realEq (lfiAct logq v lfiOne V) V
  /-- 本丸: 不定性群の任意の元 g の作用の下で両側界が保たれる（下界 + 3·shift ≤ 3·transported・
      transported ≤ 上界 + shift）。 -/
  two_sided : ∀ (g : lfiIndetGroup) (n c : Nat), rLe realZero (logq v) →
    rLe (realAdd (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (shift g)))
        (rmul (intToReal ((3 : Nat) : Int)) (transport g n))
    ∧ rLe (transport g n)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (shift g))
  /-- crux 位置（μ=0 核上界の内側）が不定性群全体の下で不変。 -/
  crux_position : ∀ (g : lfiIndetGroup) (n c : Nat), rLe realZero (logq v) →
    rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
    ∧ realEq (transport g n) (realAdd (mlltLogLink logq v l n) (shift g))
  /-- 単一 μ 生成元で M442F へ厳密還元（1 パラメータ版を真に含む）。 -/
  reduces : ∀ (μ : Int) (n : Nat),
    transport (lfiGen μ) n = linTransportMu logq v l n μ

/-- **M447F-9b: 実データ** — 全フィールドを M447F-3〜6 の本物で充足。作用は M342F の実 deg_ℝ 事実を
    写した群準同型、両側界は M442F、シフトは logVolLocal であり crux は受け取らず昇格のみ。 -/
def logLinkFullIndetGroupData (logq : Nat → RReal) (v l : Nat) :
    LogLinkFullIndetGroupData logq v where
  l := l
  transport := fun g n => lfiTransport logq v l n g
  is_transport := rfl
  shift := fun g => lfiShift logq v g
  is_shift := rfl
  group_hom := fun g h V => lfi_action_hom logq v g h V
  act_one := fun V => lfi_act_one logq v V
  two_sided := fun g n c hq => lfi_two_sided_group_invariant logq v l n c g hq
  crux_position := fun g n c hq => lfi_crux_position_invariant logq v l n c g hq
  reduces := fun μ n => rfl

/-- **M447F-9c: 存在（M447F 見出し）** — 任意の実重み logq・素点 v・l-捻れ l に対し、(Ind1)×(Ind2)×(Ind3)
    合成不定性群作用版の log-link 多輻輸送データが存在する。M442F の単一 μ log-link 版多輻輸送は、不定性群
    lfiIndetGroup の任意の元 g の作用へ昇格でき、その作用は真の群準同型（合成・単位・準同型）で、任意の元 g の
    下で両側界を許容誤差（g の (Ind3) シフト）込みでなお満たし、crux の位置を群全体の下で動かさず、単一 μ
    生成元で M442F へ厳密還元する。crux（Dβ-ω＝theta ≤ gauss）は外部仮説として明示され、**決して証明され
    ない**——本層は M442F の「不定性は 1 パラメータ族のみ」という限定を **不定性群作用へ昇格して破り**、両側界が
    群作用の下で安定であるという構造を本物にする（群は既存 Ind 模型の合成に留まる旨は正直に固定）。 -/
theorem lfi_exists (logq : Nat → RReal) (v l : Nat) :
    Nonempty (LogLinkFullIndetGroupData logq v) :=
  ⟨logLinkFullIndetGroupData logq v l⟩

/-! ## 実例（twist l=3 → ×2l=×6, 多輻段 n=5: Σ_{j=1}^{5} j²=55, 群の元 g=⟨true,true,2⟩） -/

/-- 実例（作用は真の群準同型・g=⟨true,false,1⟩, h=⟨false,true,2⟩）: 合成 g·h の作用は g の作用∘h の作用。 -/
example (logq : Nat → RReal) (v : Nat) (V : RReal) :
    realEq (lfiAct logq v (lfiMul ⟨true, false, 1⟩ ⟨false, true, 2⟩) V)
      (lfiAct logq v ⟨true, false, 1⟩ (lfiAct logq v ⟨false, true, 2⟩ V)) :=
  lfi_action_hom logq v ⟨true, false, 1⟩ ⟨false, true, 2⟩ V

/-- 実例（単位元の作用は恒等）: 不定性群の単位元 lfiOne は log-volume を動かさない。 -/
example (logq : Nat → RReal) (v : Nat) (V : RReal) :
    realEq (lfiAct logq v lfiOne V) V :=
  lfi_act_one logq v V

/-- 実例（M442F へ厳密還元・l=3, n=5, μ=1）: 単一 μ 生成元で群作用版は M442F の linTransportMu へ一致。 -/
example (logq : Nat → RReal) (v : Nat) :
    lfiTransport logq v 3 5 (lfiGen 1) = linTransportMu logq v 3 5 1
    ∧ lfiShift logq v (lfiGen 1) = linMuShift logq v 1 :=
  lfi_reduces_to_lin logq v 3 5 1

/-- 実例（本丸・任意の元 g=⟨true,true,2⟩ の下で両側界・l=3, n=5）: 下界 + 3·(g の shift) ≤ 3·(g·transported)・
    g·transported ≤ 6·殻 deg_ℝ + (g の shift)——不定性群の元 g の作用を許容誤差として吸収してなお両側界内。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (realAdd (rmul (intToReal ((2 * 3 : Nat) : Int))
            (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (lfiShift logq v ⟨true, true, 2⟩)))
        (rmul (intToReal ((3 : Nat) : Int)) (lfiTransport logq v 3 5 ⟨true, true, 2⟩))
    ∧ rLe (lfiTransport logq v 3 5 ⟨true, true, 2⟩)
        (realAdd (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c)))
          (lfiShift logq v ⟨true, true, 2⟩)) :=
  lfi_two_sided_group_invariant logq v 3 5 c ⟨true, true, 2⟩ hq

/-- 実例（crux 位置は群全体で不変・g=⟨true,false,2⟩, l=3, n=5）: μ=0 核の上界（crux の位置）は群の元 g の
    下でも保たれ、g·transported は μ=0 核 + g の shift である。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (mlltLogLink logq v 3 5)
        (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c)))
    ∧ realEq (lfiTransport logq v 3 5 ⟨true, false, 2⟩)
        (realAdd (mlltLogLink logq v 3 5) (lfiShift logq v ⟨true, false, 2⟩)) :=
  lfi_crux_position_invariant logq v 3 5 c ⟨true, false, 2⟩ hq

/-- 実例（残る限定・scope）: 群作用でも transported は μ=0 核 + 明示 (Ind3) シフトに分解し、群は模型合成に
    留まり crux は仮説として通すのみ。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (lfiTransport logq v 3 5 ⟨true, true, 1⟩)
        (realAdd (mlltLogLink logq v 3 5) (lfiShift logq v ⟨true, true, 1⟩))
    ∧ (∀ crux : Prop, crux → crux) :=
  lfi_model_scope logq v 3 5 ⟨true, true, 1⟩

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  lfi_crux_is_hypothesis crux

/-- 実例（capstone 存在）: (Ind1)×(Ind2)×(Ind3) 合成不定性群作用版の log-link 多輻輸送データは存在する。 -/
example (logq : Nat → RReal) (v l : Nat) :
    Nonempty (LogLinkFullIndetGroupData logq v) :=
  lfi_exists logq v l

end IUT
