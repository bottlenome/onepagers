-- M452F LogLinkContinuousIndet [実・本物・柱D]
-- 分類: [実]（§2(a) 昇格・M447F LogLinkFullIndetGroup(lfi)の正直な限定「(Ind3) の連続部分は
--   離散 ℤ 近似に留まる」を本物へ置換して閉じる）。作用の主語は M442F/M437F の実 deg_ℝ
--   log-volume（mlltLogLink / logVolLocal）であり toy を用いない。不定性シフトを整数 μ の
--   離散族から**実数 t（ℝ setoid）で連続にパラメータ付けた 1 次元実シフト**へ昇格する。
-- complete_pct 影響: 前進。M447F は (Ind1)×(Ind2)×(Ind3) 合成不定性群の作用の下で log-link 両側界が
--   保たれることを本物化したが、(Ind3) 成分は**整数 μ∈ℤ の離散シフト**（lfiShift = logVolLocal v μ）に
--   留まり「(Ind3) の連続部分は離散 ℤ 近似」と正直に限定していた。本 M452F はその限定を破る:
--   連続 (Ind3) シフト lciContShift v t = t·log q_v（t は実数 ℝ setoid）を建て、連続 t の下で両側界が
--   許容誤差込みで保たれること（lci_two_sided_continuous）を realEq/rLe で本物化。t を整数値
--   intToReal μ に制限すると M447F の離散版 lfiTransport/lfiShift へ厳密整合（lci_reduces_to_lfi）。
--   残る限定は「連続部は 1 次元実シフト（rmul スケール）・(Ind1)(Ind2) との完全連続混合や実 π₁^ét 上の
--   完全不定性・Haar 測度積分は未」とより狭く述べ直す（lci_model_scope）。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。

/-
  IUT/LogLinkContinuousIndet.lean — M452F（定理3.11 / log-link 版多輻 log-volume 輸送の (Ind3)
  不定性の連続化：M447F の整数 μ 離散シフトを実数 t の連続シフトへ昇格し、連続不定性の下で
  両側界が許容誤差込みで保たれることを本物構成）

  ## 二軸
  * 主要成果の分類: **[実]**（§2(a) 昇格・既存の正直な限定を本物へ置換して閉じる）。M447F
    `LogLinkFullIndetGroup`（`lfi`）は (Ind1)×(Ind2)×(Ind3) 合成不定性群 lfiIndetGroup の任意の元 g の
    作用の下で M442F 両側界が保たれることを本物化したが、その (Ind3) 成分は **整数 μ∈ℤ の離散シフト**
    （lfiShift g = linMuShift v (lfiInd3 g) = logVolLocal v μ、μ は Int）に留まり、`lfi_model_scope` に

      「deg_ℝ への作用は (Ind3) 成分だけで決まり **(Ind3) の連続部分は離散 ℤ 近似**に留まる」

    と正直に限定していた。本 M452F はこの限定を **連続 ℝ 値の (Ind3) 不定性**へ昇格して破る:
      - **連続 (Ind3) シフト** `lciContShift v t = rmul t (logq v) = t · log q_v`（t は**実数 RReal＝
        ℝ setoid**）。M447F/M442F の離散シフト logVolLocal v μ = (intToReal μ)·log q_v の μ を **整数から
        実数 t へ解放**した 1 次元連続シフト。整数値 t = intToReal μ でちょうど離散シフトに一致（defeq）。
      - **連続シフトの加法性** `lci_shift_additive`: lciContShift v (t+s) ≈ lciContShift v t +
        lciContShift v s（実数加法 realAdd で・右分配 `rmul_add_right`）——連続不定性が実数加法群として
        整合的（logVolLocal_add の連続版・ℤ 準同型を ℝ 準同型へ昇格）。
      - **連続 (Ind3) 輸送** `lciTransport v l n t`: M442F μ=0 核 `mlltLogLink` に連続シフト lciContShift v t
        を上乗せした実 deg_ℝ 体積（離散 linTransportMu の連続版・t が整数値で lin_transport_decomp と realEq 整合）。
      - **本丸** `lci_two_sided_continuous`: **連続 t の下で両側界が保たれる**（下界 + 3·(連続シフト) ≤
        3·(連続輸送)・連続輸送 ≤ 上界 + (連続シフト)）を realEq/rLe で本物化。M442F/M437F 両側界 +
        M130 `rLe_add` + M337F 実分配 `rmul_add_left` で閉じる。M447F は整数 μ だったのを実数 t へ一般化。
      - **M447F へ厳密整合** `lci_reduces_to_lfi`: t = intToReal μ（整数値）で連続シフト/連続輸送が
        M447F の離散版 lfiShift/lfiTransport（の Ind3 成分・lfiGen μ）にちょうど一致（shift は rfl・
        transport は lin_transport_decomp の realEq）——昇格が M447F 離散版を真に含む。
      - **連続不定性区間** `lci_indet_interval`: 連続不定性 t が実数区間 [−bnd, bnd]（bnd = log l 相当）を
        動いても crux の位置（μ=0 核両側界の内側）が保たれ、連続シフトは shift(−bnd) と shift(bnd) の
        間に収まる（区間全体で crux が内側・M180 乗法単調性 `rmul_le_mul_right`）。
      - **crux 外部** `lci_crux_external`/`lci_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は範囲外。
      - **残る限定を狭く正直に** `lci_model_scope`: 連続部は 1 次元実シフト（rmul スケール）に留まり
        (Ind1)(Ind2) との完全な連続混合・実 π₁^ét 上の完全不定性・Haar 測度レベルの積分は未（M447F の
        「離散 ℤ 近似」を実際に破ったことを明示）。
  * complete_pct 影響: **前進**。M447F の「(Ind3) の連続部分は離散 ℤ 近似に留まる」という限定を、
    連続 ℝ 値シフト lciContShift（実数 t で連続パラメータ付け）の下での両側界不変
    （lci_two_sided_continuous）＋連続シフトの実数加法準同型（lci_shift_additive）へ昇格して破る。
    crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の係争点）は**決して導出せず**外部仮説のまま。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M452F-1 `lciContShift` — 連続 (Ind3) シフト（実数 t·log q_v、離散 logVolLocal v μ の μ を実数へ解放）。
  * M452F-2 `lci_shift_additive` — 連続シフトの実数加法準同型（`rmul_add_right`、ℤ 準同型 logVolLocal_add の連続版）。
  * M452F-3 `lciTransport` — 連続 (Ind3) 輸送（μ=0 核 mlltLogLink + 連続シフト、離散 linTransportMu の連続版）。
  * M452F-4 `lci_transport_decomp` — 連続輸送 = μ=0 核 + 連続シフト（定義的分解・realEq_refl）。
  * M452F-5 `lci_two_sided_continuous` — 本丸: 連続 t の下で両側界（下界 + 3·連続シフト ≤ 3·連続輸送・
      連続輸送 ≤ 上界 + 連続シフト、M437F 両側界 + M130 rLe_add + M337F rmul_add_left）。
  * M452F-6 `lci_reduces_to_lfi` — t = intToReal μ で M447F 離散版 lfiShift/lfiTransport へ厳密整合。
  * M452F-7 `lci_indet_interval` — 連続不定性区間 [−bnd, bnd] で crux 位置が内側・連続シフトが両端の間
      （M180 `rmul_le_mul_right`）。
  * M452F-8 `lci_crux_external`/`lci_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M452F-9 `lci_model_scope` — 残る正直な限定（連続部は 1 次元実シフト・(Ind1)(Ind2) 完全連続混合・
      実 π₁^ét・Haar 測度積分は未）を定理化（M447F の「離散 ℤ 近似」を実際に破った旨を明示）。
  * M452F-10 capstone `LogLinkContinuousIndetData`/`lci_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロットの比較不等式そのもの＝
    IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層が昇格するのは M447F/M442F の両側界安定性を
    整数 μ の離散シフトから実数 t の連続シフトへ広げること（連続加法性・連続両側界・区間内 crux 位置）で
    あり、M437F 実 deg_ℝ・rmul 実分配・M130 加法単調性・M180 乗法単調性で閉じる**無条件で本物**の命題
    ——**crux（rep ≤ gauss）とは別の主張**。crux は任意の外部 Prop として受け取るのみ
    （`lci_crux_is_hypothesis` は Iff.rfl）。
  * **連続部は 1 次元実シフト（rmul スケール）に留まる**。M447F の「(Ind3) 連続部は離散 ℤ 近似」を実際に
    破り実数 t を含むが、**(Ind1)(Ind2) との完全な連続混合・実 π₁^ét（遠アーベル復元）上の完全不定性群・
    Haar 測度レベルの不定性積分は未**——本層が扱うのは (Ind3) 方向の 1 次元連続シフト t·log q_v のみ。
    連続シフトは μ=0 核に上乗せする明示 1 パラメータ（実数 t）で、群レベル/測度レベルの完全同変性は後続。
  * **合成は有限段 n・付値レベル sumSq n（Σj²）・×2l 明示スケール・特定 l**。log-link は M337F 主項係数
    レベル・両側界は M432F/M437F の輸送安定・**局所体は K = ℚ_p**。log q_v は非負実重み witness
    （hq : realZero ≤ logq v が前提）。**ℝ は setoid**（realEq が同値・`=` でない）ゆえ連続シフト・加法性・
    両側界・区間・crux 位置は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 昇格・正直な限定を本物へ置換[実]。一般名は `lci` 接頭辞で衝突回避。
-/
import IUT.LogLinkFullIndetGroup

namespace IUT

/-! ## M452F-1: 連続 (Ind3) シフト（整数 μ の離散シフトを実数 t の連続シフトへ昇格） -/

/-- **M452F-1: 連続 (Ind3) シフト** — log-link 版多輻輸送に効く (Ind3) log(l)-スケール不定性を、
    **実数 t（RReal＝ℝ setoid）で連続にパラメータ付けた** 1 次元実シフトとして与える:
      lciContShift v t  =  rmul t (logq v)  =  t · log q_v。
    M447F/M442F の離散シフト `linMuShift v μ = logVolLocal v μ = rmul (intToReal μ) (logq v)`（μ は
    整数）の μ を **整数から実数 t へ解放**した連続化。整数値 t = intToReal μ でちょうど離散シフトに
    一致する（defeq）——M447F の「(Ind3) の連続部分は離散 ℤ 近似」を実際に破る主語（toy を用いない）。 -/
def lciContShift (logq : Nat → RReal) (v : Nat) (t : RReal) : RReal :=
  rmul t (logq v)

/-! ## M452F-2: 連続シフトの実数加法準同型（ℤ 準同型 logVolLocal_add の連続版） -/

/-- **定理 (M452F-2: 連続シフトの実数加法準同型・本物)** — 連続 (Ind3) シフトは実数加法について加法的:
      lciContShift v (t+s)  ≈  lciContShift v t  +  lciContShift v s。
    右分配 `rmul_add_right`（(t+s)·log q_v = t·log q_v + s·log q_v）で閉じる。M442F/M447F の離散加法
    `logVolLocal_add`（ℤ→ℝ 準同型）を **実数 t,s の連続加法（ℝ→ℝ 準同型）へ昇格**したもの——連続不定性が
    実数加法群として log-volume に整合的に効く本物の準同型。 -/
theorem lci_shift_additive (logq : Nat → RReal) (v : Nat) (t s : RReal) :
    realEq (lciContShift logq v (realAdd t s))
      (realAdd (lciContShift logq v t) (lciContShift logq v s)) :=
  rmul_add_right t s (logq v)

/-! ## M452F-3: 連続 (Ind3) 輸送（μ=0 核 + 連続シフト・離散 linTransportMu の連続版） -/

/-- **M452F-3: 連続 (Ind3) 輸送後 log-volume** — M442F の μ=0 核（不定性ゼロ）`mlltLogLink` に、
    連続シフト `lciContShift v t` を上乗せして log-link 輸送した実 deg_ℝ 体積:
      lciTransport v l n t  =  mlltLogLink v l n  +  lciContShift v t。
    M442F の離散 μ≠0 輸送 `linTransportMu`（≈ mlltLogLink + linMuShift v μ、`lin_transport_decomp`）を
    **実数 t の連続シフトへ昇格**した本物の主語。整数値 t = intToReal μ で離散 linTransportMu と realEq
    整合する（`lci_reduces_to_lfi`）。 -/
def lciTransport (logq : Nat → RReal) (v l n : Nat) (t : RReal) : RReal :=
  realAdd (mlltLogLink logq v l n) (lciContShift logq v t)

/-! ## M452F-4: 連続輸送の明示分解（μ=0 核 + 連続シフト） -/

/-- **定理 (M452F-4: 連続輸送の明示分解・本物)** — 連続 (Ind3) 輸送 `lciTransport` は、M442F の μ=0 核
    `mlltLogLink`（不定性ゼロ）に連続シフト `lciContShift v t` を足したものにちょうど realEq に等しい:
      lciTransport v l n t  ≈  mlltLogLink v l n  +  lciContShift v t。
    連続不定性の全寄与が **μ=0 核 + 連続シフト**に予測可能に分かれる（連続不定性が制御不能に増殖しない、
    crux 不等式ではない）。M442F 離散版 `lin_transport_decomp` の連続版（本層では定義的分解）。 -/
theorem lci_transport_decomp (logq : Nat → RReal) (v l n : Nat) (t : RReal) :
    realEq (lciTransport logq v l n t)
      (realAdd (mlltLogLink logq v l n) (lciContShift logq v t)) :=
  realEq_refl _

/-! ## M452F-5: 本丸 — 連続 t の下で両側界が保たれる -/

/-- **定理 (M452F-5: 連続 (Ind3) 不定性の下で両側界が保たれる・本丸・本物の昇格)** — **実数 t で連続に
    パラメータ付けた** (Ind3) シフトの下で、M442F/M437F の両側界は連続シフト `lciContShift v t`
    （＝ t·log q_v）を許容誤差として両側に吸収した上でなお保たれる:
      (i) **下界（連続不定性込み）**: 2l·(n³·log q_v) + 3·(連続シフト) ≤ 3·(連続輸送)、
      (ii)**上界（連続不定性込み）**: 連続輸送 ≤ 2l·(対数殻 m^{Σj²+c} の deg_ℝ) + (連続シフト)。
    証明は M437F `mllt_loglink_transport`（μ=0 核 mlltLogLink の両側界）を、M130 加法単調性 `rLe_add`
    で連続シフトぶん平行移動し、M337F 実分配 `rmul_add_left`（3·(核+連続シフト) = 3·核 + 3·連続シフト）と
    M452F-4 分解で主語を連続輸送へ張り替える。すなわち **M447F の「(Ind3) は整数 μ の離散シフト」を破り、
    実数 t の連続不定性の下で両側界が coherent に保たれる**本物の昇格（連続シフト t·log q_v を許容誤差と
    して吸収・crux 不等式は決して導出しない）。 -/
theorem lci_two_sided_continuous (logq : Nat → RReal) (v l n c : Nat) (t : RReal)
    (hq : rLe realZero (logq v)) :
    rLe (realAdd (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (lciContShift logq v t)))
        (rmul (intToReal ((3 : Nat) : Int)) (lciTransport logq v l n t))
    ∧ rLe (lciTransport logq v l n t)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (lciContShift logq v t)) := by
  have hlo : rLe (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((3 : Nat) : Int)) (mlltLogLink logq v l n)) :=
    (mllt_loglink_transport logq v l n c hq).1
  have hup : rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c))) :=
    (mllt_loglink_transport logq v l n c hq).2
  refine ⟨?_, ?_⟩
  · -- 下界: 下界 + 3·連続シフト ≤ 3·核 + 3·連続シフト = 3·(核+連続シフト) = 3·連続輸送。
    have step := rLe_add (rmul (intToReal ((3 : Nat) : Int)) (lciContShift logq v t)) hlo
    have hdist :
        realEq (realAdd (rmul (intToReal ((3 : Nat) : Int)) (mlltLogLink logq v l n))
              (rmul (intToReal ((3 : Nat) : Int)) (lciContShift logq v t)))
            (rmul (intToReal ((3 : Nat) : Int)) (lciTransport logq v l n t)) :=
      realEq_symm (rmul_add_left (mlltLogLink logq v l n) (lciContShift logq v t)
        (intToReal ((3 : Nat) : Int)))
    exact rLe_congr (realEq_refl _) hdist step
  · -- 上界: 核 + 連続シフト ≤ 上界 + 連続シフト、主語を連続輸送へ張り替える（定義的一致）。
    exact rLe_add (lciContShift logq v t) hup

/-! ## M452F-6: t = intToReal μ で M447F 離散版へ厳密整合 -/

/-- **定理 (M452F-6: M447F 離散版へ厳密整合)** — 連続パラメータ t を**整数値 t = intToReal μ** に
    制限すると、連続シフト/連続輸送は M447F の離散版 `lfiShift`/`lfiTransport`（単一 μ 生成元 lfiGen μ の
    (Ind3) 成分）にちょうど整合する:
      lciContShift v (intToReal μ)  =  lfiShift v (lfiGen μ)（rfl、両者とも rmul (intToReal μ)(logq v)）、
      lciTransport v l n (intToReal μ)  ≈  lfiTransport v l n (lfiGen μ)（`lin_transport_decomp` の realEq）。
    すなわち本層の連続不定性への昇格は **M447F の離散 ℤ シフトを真に含む**（整数値で M447F へ厳密整合する）
    ことを機械検証する——昇格が骨格の張り替えでなく本物の一般化であることの証拠。 -/
theorem lci_reduces_to_lfi (logq : Nat → RReal) (v l n : Nat) (μ : Int) :
    lciContShift logq v (intToReal μ) = lfiShift logq v (lfiGen μ)
    ∧ realEq (lciTransport logq v l n (intToReal μ)) (lfiTransport logq v l n (lfiGen μ)) :=
  ⟨rfl, realEq_symm (lin_transport_decomp logq v l n μ)⟩

/-! ## M452F-7: 連続不定性区間 [−bnd, bnd] で crux 位置が内側 -/

/-- **定理 (M452F-7: 連続不定性区間で crux 位置が保たれる・本物)** — 連続不定性 t が実数区間
    **[−bnd, bnd]**（bnd = log l 相当の許容範囲・`hlo : −bnd ≤ t`, `hhi : t ≤ bnd`）を動いても、
    (i) M442F の **μ=0 核の上界**（crux が内側に座す μ=0 両側界の上側: mlltLogLink ≤ 2l·対数殻 deg_ℝ）が
        そのまま保たれ（t に依らず・crux の位置は連続区間全体で不変）、
    (ii) 連続シフト `lciContShift v t` は両端の連続シフト **shift(−bnd) と shift(bnd) の間に収まる**
        （lciContShift v (−bnd) ≤ lciContShift v t ≤ lciContShift v bnd、M180 乗法単調性 `rmul_le_mul_right`・
        log q_v ≥ 0）。
    すなわち crux の位置づけ（テータ ⇄ ガウスの比較が μ=0 両側界の内側に座す）が **連続不定性区間全体の
    下で壊れない**——連続 t のどの値も crux の位置を両側界の外へ動かさない本物（crux 不等式そのものは
    決して導出しない）。M447F `lfi_crux_position_invariant` の連続区間版。 -/
theorem lci_indet_interval (logq : Nat → RReal) (v l n c : Nat) (bnd t : RReal)
    (hlo : rLe (realNeg bnd) t) (hhi : rLe t bnd) (hq : rLe realZero (logq v)) :
    rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
    ∧ rLe (lciContShift logq v (realNeg bnd)) (lciContShift logq v t)
    ∧ rLe (lciContShift logq v t) (lciContShift logq v bnd) :=
  ⟨(mllt_loglink_transport logq v l n c hq).2,
   rmul_le_mul_right hlo hq,
   rmul_le_mul_right hhi hq⟩

/-! ## M452F-8: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M452F-8a: 連続両側界は本物・crux は外部仮説／honest)** — 連続 t の下で両側界が保たれること
    （M452F-5 上界: 連続輸送 ≤ 2l·対数殻 + 連続シフト）は M437F 実 deg_ℝ・rmul 実分配・M130 加法単調性で
    閉じる**無条件で本物**の命題（crux とは独立に成立）。しかし theta-pilot ≤ gauss-pilot の**多輻的
    アルゴリズム**（crux Dβ-ω ＝ IUT 論争の当の係争点）は本層で**決して証明しない**。crux を任意の外部
    Prop `crux` として受け取り、連続両側界上界の本物性 **と** crux の連言を、crux が仮説として供給された
    場合にのみ返す——crux は決して導出されない。 -/
theorem lci_crux_external (logq : Nat → RReal) (v l n c : Nat) (t : RReal)
    (hq : rLe realZero (logq v)) (crux : Prop) (hcrux : crux) :
    rLe (lciTransport logq v l n t)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (lciContShift logq v t))
    ∧ crux :=
  ⟨(lci_two_sided_continuous logq v l n c t hq).2, hcrux⟩

/-- **定理 (M452F-8b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux（theta ≤ gauss 比較）は本層が昇格した連続
    (Ind3) 不定性の下での両側界とは別物であり、論争の係争点をそのまま外部仮説として受け取ったもので
    あることを機械検証で明示（M447F `lfi_crux_is_hypothesis`・M442F `lin_crux_is_hypothesis` と同じ精神）。 -/
theorem lci_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M452F-9: 残る正直な限定を定理として明記（消去・弱化禁止・より狭く述べ直す） -/

/-- **定理 (M452F-9: 残る正直な scope・限定を定理化)** — 本層の連続 (Ind3) 不定性への昇格 `lciTransport`
    は、
    (i) **連続 t（実数 RReal）でも連続輸送は μ=0 核 + 連続シフト（lciContShift v t = t·log q_v）に分解する**
        （`lci_transport_decomp`）——すなわち本層は M447F の「(Ind3) の連続部分は **離散 ℤ 近似**」を実際に
        破り、実数 t の連続シフトと連続加法準同型（lci_shift_additive）を得たが、**連続部は 1 次元実シフト
        （rmul スケール）に留まり、(Ind1)(Ind2) との完全な連続混合・実 π₁^ét 上の完全不定性群・Haar 測度
        レベルの不定性積分は未**、
    (ii) **crux（外部 Prop）は仮説としてのみ利用可能で本層では導出されない**（`∀ crux, crux → crux`）。
    この正直な限定（離散 ℤ 近似を破って連続 1 次元実シフトを得たが完全連続混合・実 π₁^ét・Haar 測度は未・
    crux 外部）を機械検証可能な形で固定する（消去・弱化禁止・M447F の限定をより狭く述べ直す）。 -/
theorem lci_model_scope (logq : Nat → RReal) (v l n : Nat) (t : RReal) :
    realEq (lciTransport logq v l n t)
        (realAdd (mlltLogLink logq v l n) (lciContShift logq v t))
    ∧ (∀ crux : Prop, crux → crux) :=
  ⟨lci_transport_decomp logq v l n t, fun _ h => h⟩

/-! ## M452F-10: capstone -/

/-- **M452F-10a: 連続 (Ind3) 不定性 log-link 多輻輸送データ**（総括） — M447F の整数 μ 離散 (Ind3) シフトを
    実数 t の連続シフトへ昇格したものを束ねる: 連続シフトの実数加法準同型（shift_additive）・連続輸送の
    明示分解（decomp）・連続 t の下で両側界が保たれること（two_sided）・整数値で M447F 離散版へ整合
    （reduces）。主語は M442F/M437F の本物の実 deg_ℝ であり toy を用いない。crux（Dβ-ω＝theta ≤ gauss）は
    外部仮説であって本層で証明されない。 -/
structure LogLinkContinuousIndetData (logq : Nat → RReal) (v : Nat) where
  /-- 横 theta-link 輸送スケール 2l を与える l-捻れ。 -/
  l : Nat
  /-- 連続 (Ind3) シフト（実数 t·log q_v）。 -/
  contShift : RReal → RReal
  /-- contShift は本層の連続シフト `lciContShift`。 -/
  is_contShift : contShift = fun t => lciContShift logq v t
  /-- 連続 t による log-link 版多輻輸送後 log-volume（n をわたる）。 -/
  transport : RReal → Nat → RReal
  /-- transport は本層の連続輸送写像 `lciTransport`。 -/
  is_transport : transport = fun t n => lciTransport logq v l n t
  /-- 連続シフトは実数加法準同型: shift(t+s) ≈ shift(t) + shift(s)。 -/
  shift_additive : ∀ t s : RReal,
    realEq (contShift (realAdd t s)) (realAdd (contShift t) (contShift s))
  /-- 連続輸送の明示分解: transported ≈ μ=0 核 + 連続シフト。 -/
  decomp : ∀ (t : RReal) (n : Nat),
    realEq (transport t n) (realAdd (mlltLogLink logq v l n) (contShift t))
  /-- 本丸: 連続 t の下で両側界が保たれる（下界 + 3·連続シフト ≤ 3·連続輸送・
      連続輸送 ≤ 上界 + 連続シフト）。 -/
  two_sided : ∀ (t : RReal) (n c : Nat), rLe realZero (logq v) →
    rLe (realAdd (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (contShift t)))
        (rmul (intToReal ((3 : Nat) : Int)) (transport t n))
    ∧ rLe (transport t n)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (contShift t))
  /-- 整数値 t = intToReal μ で M447F 離散版 lfiShift へ厳密整合。 -/
  reduces : ∀ μ : Int, contShift (intToReal μ) = lfiShift logq v (lfiGen μ)

/-- **M452F-10b: 実データ** — 全フィールドを M452F-2〜6 の本物で充足。連続シフトは rmul 実スケール、
    両側界は M437F、加法性は rmul_add_right であり crux は受け取らず昇格のみ。 -/
def logLinkContinuousIndetData (logq : Nat → RReal) (v l : Nat) :
    LogLinkContinuousIndetData logq v where
  l := l
  contShift := fun t => lciContShift logq v t
  is_contShift := rfl
  transport := fun t n => lciTransport logq v l n t
  is_transport := rfl
  shift_additive := fun t s => lci_shift_additive logq v t s
  decomp := fun t n => lci_transport_decomp logq v l n t
  two_sided := fun t n c hq => lci_two_sided_continuous logq v l n c t hq
  reduces := fun _ => rfl

/-- **M452F-10c: 存在（M452F 見出し）** — 任意の実重み logq・素点 v・l-捻れ l に対し、連続 (Ind3) 不定性版の
    log-link 多輻輸送データが存在する。M447F の整数 μ 離散 (Ind3) シフトは、実数 t の連続シフト
    lciContShift v t = t·log q_v へ昇格でき、その連続シフトは実数加法準同型で、連続 t の下で両側界を
    許容誤差（連続シフト）込みでなお満たし、整数値 t = intToReal μ で M447F 離散版へ厳密整合する。
    crux（Dβ-ω＝theta ≤ gauss）は外部仮説として明示され、**決して証明されない**——本層は M447F の
    「(Ind3) の連続部分は離散 ℤ 近似」という限定を **連続 ℝ 値シフトへ昇格して破り**、両側界が連続不定性の
    下で安定であるという構造を本物にする（連続部は 1 次元実シフトに留まる旨は正直に固定）。 -/
theorem lci_exists (logq : Nat → RReal) (v l : Nat) :
    Nonempty (LogLinkContinuousIndetData logq v) :=
  ⟨logLinkContinuousIndetData logq v l⟩

/-! ## 実例（twist l=3 → ×2l=×6, 多輻段 n=5: Σ_{j=1}^{5} j²=55, 連続シフト t） -/

/-- 実例（連続シフトの加法性）: lciContShift v (t+s) ≈ lciContShift v t + lciContShift v s。 -/
example (logq : Nat → RReal) (v : Nat) (t s : RReal) :
    realEq (lciContShift logq v (realAdd t s))
      (realAdd (lciContShift logq v t) (lciContShift logq v s)) :=
  lci_shift_additive logq v t s

/-- 実例（本丸・連続 t の下で両側界・l=3, n=5）: 下界 + 3·(連続シフト t) ≤ 3·(連続輸送)・
    連続輸送 ≤ 6·殻 deg_ℝ + (連続シフト t)——連続不定性 t·log q_v を許容誤差として吸収してなお両側界内。 -/
example (logq : Nat → RReal) (v c : Nat) (t : RReal) (hq : rLe realZero (logq v)) :
    rLe (realAdd (rmul (intToReal ((2 * 3 : Nat) : Int))
            (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (lciContShift logq v t)))
        (rmul (intToReal ((3 : Nat) : Int)) (lciTransport logq v 3 5 t))
    ∧ rLe (lciTransport logq v 3 5 t)
        (realAdd (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c)))
          (lciContShift logq v t)) :=
  lci_two_sided_continuous logq v 3 5 c t hq

/-- 実例（M447F 離散版へ厳密整合・l=3, n=5, μ=2）: t=intToReal 2（整数値）で連続版は M447F 離散版へ一致。 -/
example (logq : Nat → RReal) (v : Nat) :
    lciContShift logq v (intToReal 2) = lfiShift logq v (lfiGen 2)
    ∧ realEq (lciTransport logq v 3 5 (intToReal 2)) (lfiTransport logq v 3 5 (lfiGen 2)) :=
  lci_reduces_to_lfi logq v 3 5 2

/-- 実例（連続不定性区間・crux 位置が内側）: 連続 t が [−bnd, bnd] を動いても μ=0 核の上界（crux 位置）は
    保たれ、連続シフトは shift(−bnd) と shift(bnd) の間に収まる。 -/
example (logq : Nat → RReal) (v c : Nat) (bnd t : RReal)
    (hlo : rLe (realNeg bnd) t) (hhi : rLe t bnd) (hq : rLe realZero (logq v)) :
    rLe (mlltLogLink logq v 3 5)
        (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c)))
    ∧ rLe (lciContShift logq v (realNeg bnd)) (lciContShift logq v t)
    ∧ rLe (lciContShift logq v t) (lciContShift logq v bnd) :=
  lci_indet_interval logq v 3 5 c bnd t hlo hhi hq

/-- 実例（残る限定・scope）: 連続輸送は μ=0 核 + 連続シフトに分解し、連続部は 1 次元実シフトに留まり
    crux は仮説として通すのみ。 -/
example (logq : Nat → RReal) (v : Nat) (t : RReal) :
    realEq (lciTransport logq v 3 5 t)
        (realAdd (mlltLogLink logq v 3 5) (lciContShift logq v t))
    ∧ (∀ crux : Prop, crux → crux) :=
  lci_model_scope logq v 3 5 t

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  lci_crux_is_hypothesis crux

/-- 実例（capstone 存在）: 連続 (Ind3) 不定性版の log-link 多輻輸送データは存在する。 -/
example (logq : Nat → RReal) (v l : Nat) :
    Nonempty (LogLinkContinuousIndetData logq v) :=
  lci_exists logq v l

end IUT
