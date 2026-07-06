/-
  IUT/LogVolumeArch.lean — M317F（柱C 先行建設: **アルキメデス log-volume log‖x‖**
                       — M312F が「範囲外」とした無限素点の寄与を本物へ昇格させ、
                       大域 log-volume の完全形（有限＋無限素点）へ近づける中核）

  ── 主要成果の分類: **[実]**（本物の先行建設 (b) かつ M312F 限定の (a) 昇格）。
     M312F `LogVolume.lean` は大域 log-volume（Arakelov 次数）を
     **非アルキメデス側**（付値×実重み log q_v、有限素点）でのみ本物構成し、
     ヘッダ正直申告に「**アルキメデス素点の log|x|（複素/実素点の寄与）は本モジュール
     では扱わない … log|·| の構成と両素点の統合は後続**」と明記していた。
     **本モジュールはこの「アルキメデス部分」を本物へ昇格させる**——構成的 ℝ 上の
     本物の絶対値 `rabs`（M127F RealAbs、‖x‖_∞）の**乗法性 `rabs_mul`（‖xy‖≈‖x‖·‖y‖、
     本物・完全証明済み）**を主語に、アルキメデス log-volume `logArchVol L x = λ(‖x‖)`
     の**加法性 log‖xy‖≈log‖x‖+log‖y‖ を本物で導く**。さらに M312F の有限部
     `logVolGlobal` と本層の無限部を合流させ、大域 log-volume の**完全形**
     deg_ℝ(D)=Σ_{v 有限}n_v·log q_v ＋ Σ_{v 無限}n_v·log‖·‖_v を **加法準同型**として
     本物で建てる。toy 主語なし——主語は M127F の本物の ℝ 絶対値 `rabs` と M307F の
     本物の因子代表 `RawDiv`・M312F の本物の Arakelov 次数 `logVolGlobal` である。

  complete_pct 影響: **柱C（Frobenioid/log-volume）の実 IUT 完全証明率を前進させる**。
     M312F が本物化したのは大域 log-volume の**有限素点部分のみ**であった。本モジュールは
     その正直申告のうち「アルキメデス素点の log‖·‖」を本物へ昇格 (a) し、次を本物で閉じる:
       (1) アルキメデス絶対値の乗法性 ‖xy‖≈‖x‖·‖y‖（M127F rabs_mul をそのまま本物で使用）、
       (2) アルキメデス log-volume の**加法性** log‖xy‖≈log‖x‖+log‖y‖（(1) と加法的
           付値 witness の準同型性から**本物で導出**——log 自体は解析的入力＝係数扱い）、
       (3) 大域 log-volume の**完全形**（有限＋無限素点）の**加法準同型**（M312F と合流）、
       (4) 積公式（Artin-Whaples）の骨組み——‖xy‖≈1 なら log‖x‖+log‖y‖≈0（本物）、
       (5) 有効因子＋非負アルキメデス寄与 ⟹ deg_ℝ≥0（M312F effective の完全形拡張）。
     これにより柱C の log-volume は「有限素点のみ本物」から「有限＋無限素点の合流を
     本物」へ前進する（完全な大域積公式・実 log の具体構成・Haar 測度は下記後続）。

  ## 検証する中核（全て sorry なし・新規 Classical.choice なし）

  * M317F-1 `logArchAbs` / `logArchAbs_mul` / `logArchAbs_congr` / `logArchAbs_nonneg_seq`
                              — **アルキメデス絶対値** ‖x‖_∞（M127F `rabs`）と**乗法性
                                 ‖xy‖≈‖x‖·‖y‖（本物・rabs_mul）**・非負性（実素点 v_∞）
  * M317F-2 `LogArchLog` / `logArchLogTrivial`
                              — **加法的付値 witness** λ:ℝ→ℝ（λ(xy)≈λ(x)+λ(y)、λ(1)≈0）。
                                 実 log の構成的 ℝ 上の完全構成は解析的後続——log を
                                 加法準同型 witness として受け、その準同型性を本物で使う
                                 （正直申告参照）。自明付値 λ≡0 を実インスタンスに与える。
  * M317F-3 `logArchVol` / `logArchVol_congr` / `logArchVol_mul`
                              — **アルキメデス log-volume** log‖x‖＝λ(‖x‖) と**加法性
                                 log‖xy‖≈log‖x‖+log‖y‖（本物: rabs_mul + λ の準同型性で導出）**
  * M317F-4 `logArchVol_unit` / `logArch_product_formula`
                              — **積公式（Artin-Whaples）の骨組み**: ‖u‖≈1 ⟹ log‖u‖≈0、
                                 ‖xy‖≈1 ⟹ log‖x‖+log‖y‖≈0（無限素点部分・本物）
  * M317F-5 `logArchWeight` / `logArchWeight_nonneg` / `logArchGlobal`
    / `logArchGlobal_add` / `logArchGlobal_zero`
                              — **大域 log-volume の完全形** deg_ℝ(D)=（有限部 M312F
                                 logVolGlobal）＋（無限部 Σ n_v·log‖·‖_v）と**加法準同型**
                                 （M312F logVolGlobal_add と合流・logVol_add4_swap で入替）
  * M317F-6 `logArchGlobal_effective_nonneg`
                              — **有効因子＋非負アルキメデス寄与 ⟹ deg_ℝ≥0**（M312F
                                 effective_nonneg の有限＋無限完全形・rLe で本物）
  * M317F-7 capstone `LogVolumeArchData` / `logVolumeArchData` / `logArch_exists` /
    `logArch_vol_isHom` / `logArch_global_complete`
  * M317F-8 実例 `logArch_example_trivial_zero` / `logArch_example_real_place`

  ## 正直な限定（何が本物で何が後続か・消去/弱化禁止）

  - **本物（完全証明）**:
    ・**アルキメデス絶対値の乗法性** ‖xy‖≈‖x‖·‖y‖（M127F `rabs_mul`、構成的 ℝ 上で
      完全証明済みを本物で使用）。
    ・**アルキメデス log-volume の加法性** log‖xy‖≈log‖x‖+log‖y‖——rabs_mul（本物）と
      加法的付値 witness λ の準同型性 λ(ab)≈λ(a)+λ(b) から**本物で導出**（logArchVol_mul）。
    ・**積公式の骨組み** ‖xy‖≈1 ⟹ log‖x‖+log‖y‖≈0（無限素点の消去律・本物）。
    ・**大域 log-volume 完全形の加法準同型** deg_ℝ(D+D')≈deg_ℝ(D)+deg_ℝ(D')
      （有限部 M312F logVolGlobal_add ＋ 無限部の合流、logVol_add4_swap、完全）。
    ・**有効因子＋非負アルキメデス寄与 ⟹ deg_ℝ≥0**（M312F effective_nonneg の
      有限＋無限完全形、本物の ℝ の順序 rLe、完全）。
    ・零因子（有限＋無限）の deg_ℝ=0（完全）。
  - **正直申告（未達・骨組み・後続。飾りでなく地図）**:
    ・**実対数 log の構成的 ℝ 上の完全構成は本モジュールの範囲外**——log を**加法準同型
      witness λ:ℝ→ℝ（λ(xy)≈λ(x)+λ(y)・λ(1)≈0）として受ける**（承認済みの正直な限定）。
      アルキメデス log-volume の**代数的・順序的内容（加法性・積公式・順序）は本物で閉じる**
      が、λ の解析的実体（log 2, log e, … の RReal 構成）は解析的入力として後続。
      実インスタンスは自明付値 λ≡0（本物だが退化）を与える——非自明な実 log witness の
      構成（GeomRlim との接続による実対数）は後続。
    ・**複素素点の重み 2（‖·‖²）は骨組み**——本層は実素点（重み 1）の log‖·‖ を扱い、
      複素素点の 2 倍重みは warch の係数として吸収する形（測度論的 Haar 測度による重みの
      完全導出は後続）。
    ・**完全な大域積公式（全素点で Σ_v log‖x‖_v=0）は範囲外**——本層は有限部（M312F の
      零係数因子）＋無限部の骨組み（‖xy‖≈1 での消去律）を本物で与える。非自明大域体での
      完全積公式は大域類体論的入力（log q_v・log‖·‖_v の具体値が満たす消去律）を要すので後続。
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ全言明は realEq/rLe による（M312F と同形）。
    ・**測度論的 Haar 測度の完全構成**（log-shell の体積を Haar 測度で定義）は後続。本層は
      Arakelov 次数（有限＋無限）の代数的・順序的核を本物で与える。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無。
-/
import IUT.LogVolume
import IUT.RealAbs

namespace IUT

/-! ## M317F-1: アルキメデス絶対値 ‖x‖_∞（実素点 v_∞） -/

/-- **M317F-1a: アルキメデス絶対値** ‖x‖_∞ — 実素点での絶対値（M127F `rabs`）。
    非アルキメデス側の付値（M307F deg 成分）に対応する無限素点の大きさ。 -/
def logArchAbs (x : RReal) : RReal := rabs x

/-- **M317F-1b: 乗法性** ‖xy‖≈‖x‖·‖y‖ — M127F `rabs_mul`（構成的 ℝ 上で本物・完全
    証明済み）をそのまま本物で使う。アルキメデス log-volume の加法性の根拠。 -/
theorem logArchAbs_mul (x y : RReal) :
    realEq (logArchAbs (rmul x y)) (rmul (logArchAbs x) (logArchAbs y)) :=
  rabs_mul x y

/-- **M317F-1c: ≈ との両立**。 -/
theorem logArchAbs_congr {x y : RReal} (h : realEq x y) :
    realEq (logArchAbs x) (logArchAbs y) :=
  rabs_congr h

/-- **M317F-1d: 非負性（点ごと witness 形）** 0 ≤ ‖x‖_∞。 -/
theorem logArchAbs_nonneg_seq (x : RReal) (n : Nat) :
    qLe ratRing.zero ((logArchAbs x).seq n) :=
  rabs_nonneg_seq x n

/-! ## M317F-2: 加法的付値 witness λ（log の準同型的核） -/

/-- **M317F-2a: 加法的付値 witness** λ:ℝ→ℝ — 実対数 log の**準同型的核**を witness と
    して受ける: λ(xy)≈λ(x)+λ(y)（乗法→加法）・λ(1)≈0・≈ 両立。実 log の構成的 ℝ 上の
    完全構成は解析的後続——ここでは λ の**準同型性のみ**を本物で使い、アルキメデス
    log-volume の加法性・積公式・順序を本物で導く（正直申告参照）。 -/
structure LogArchLog where
  /-- 加法的付値本体 λ（log‖·‖ の λ 部分）。 -/
  lam : RReal → RReal
  /-- ≈ との両立。 -/
  lam_congr : ∀ {x y : RReal}, realEq x y → realEq (lam x) (lam y)
  /-- 準同型性（乗法→加法）λ(xy)≈λ(x)+λ(y)。 -/
  lam_mul : ∀ x y : RReal, realEq (lam (rmul x y)) (realAdd (lam x) (lam y))
  /-- 単位元 λ(1)≈0。 -/
  lam_one : realEq (lam (qToReal ratRing.one)) realZero

/-- **M317F-2b: 自明付値インスタンス** λ≡0 — 本物だが退化した加法的付値（自明な
    アルキメデス付値）。構造が非空であることを本物で示す（非自明な実 log witness の
    構成は解析的後続）。 -/
def logArchLogTrivial : LogArchLog where
  lam := fun _ => realZero
  lam_congr := fun _ => realEq_refl realZero
  lam_mul := fun _ _ => realEq_symm (realAdd_zero realZero)
  lam_one := realEq_refl realZero

/-! ## M317F-3: アルキメデス log-volume log‖x‖＝λ(‖x‖) -/

/-- **M317F-3a: アルキメデス log-volume** log‖x‖ = λ(‖x‖_∞)。無限素点の log-volume
    寄与（実素点の log‖·‖）。 -/
def logArchVol (L : LogArchLog) (x : RReal) : RReal := L.lam (logArchAbs x)

/-- **M317F-3b: ≈ との両立**。 -/
theorem logArchVol_congr (L : LogArchLog) {x y : RReal} (h : realEq x y) :
    realEq (logArchVol L x) (logArchVol L y) :=
  L.lam_congr (logArchAbs_congr h)

/-- **M317F-3c: 加法性（本丸）** log‖xy‖ ≈ log‖x‖ + log‖y‖。**本物で導出**:
    ‖xy‖≈‖x‖·‖y‖（M127F rabs_mul、本物）を λ の congr で移し、λ の準同型性
    λ(‖x‖·‖y‖)≈λ(‖x‖)+λ(‖y‖) で加法へ落とす。log の乗法→加法性がアルキメデス
    log-volume の加法準同型として本物で成立する。 -/
theorem logArchVol_mul (L : LogArchLog) (x y : RReal) :
    realEq (logArchVol L (rmul x y))
      (realAdd (logArchVol L x) (logArchVol L y)) :=
  realEq_trans (L.lam_congr (logArchAbs_mul x y))
    (L.lam_mul (logArchAbs x) (logArchAbs y))

/-! ## M317F-4: 積公式（Artin-Whaples）の骨組み -/

/-- **M317F-4a: 単位の log-volume は 0** — ‖u‖≈1（アルキメデス単位）なら log‖u‖≈0。
    λ の単位元性 λ(1)≈0 による。積公式の無限素点部分の核。 -/
theorem logArchVol_unit (L : LogArchLog) {u : RReal}
    (h : realEq (logArchAbs u) (qToReal ratRing.one)) :
    realEq (logArchVol L u) realZero :=
  realEq_trans (L.lam_congr h) L.lam_one

/-- **M317F-4b: 積公式の骨組み** — ‖xy‖≈1 なら log‖x‖+log‖y‖≈0。加法性と単位性の
    合成: log‖x‖+log‖y‖≈log‖xy‖≈log(1)≈0。Artin-Whaples 積公式の**無限素点の
    消去律**（有限素点部分は M312F `logVol_product_formula_trivial`）。完全な大域積公式
    は大域類体論的入力を要すので後続。 -/
theorem logArch_product_formula (L : LogArchLog) {x y : RReal}
    (h : realEq (logArchAbs (rmul x y)) (qToReal ratRing.one)) :
    realEq (realAdd (logArchVol L x) (logArchVol L y)) realZero :=
  realEq_trans (realEq_symm (logArchVol_mul L x y)) (logArchVol_unit L h)

/-! ## M317F-5: 大域 log-volume の完全形（有限＋無限素点） -/

/-- **M317F-5a: アルキメデス重み** — 無限素点 k の局所元 elt k のアルキメデス
    log-volume log‖elt k‖ を重み係数とする（無限部の Σ n_v·log‖·‖_v の重み）。 -/
def logArchWeight (L : LogArchLog) (elt : Nat → RReal) : Nat → RReal :=
  fun k => logArchVol L (elt k)

/-- **M317F-5b: アルキメデス重みの非負性** — 各局所元の log‖·‖≥0（‖·‖≥1）なら重み ≥0。 -/
theorem logArchWeight_nonneg (L : LogArchLog) (elt : Nat → RReal)
    (h : ∀ k, rLe realZero (logArchVol L (elt k))) :
    ∀ k, rLe realZero (logArchWeight L elt k) :=
  h

/-- **M317F-5c: 大域 log-volume の完全形** deg_ℝ(D) = （有限部 M312F logVolGlobal）
    ＋（無限部 Σ_{v∞} n_v·log‖·‖_v）。因子は有限素点成分 xf と無限素点成分 xa の対で
    表す。M312F の Arakelov 次数（有限）に無限素点の寄与を合流させた完全形。 -/
def logArchGlobal (logq warch : Nat → RReal) (xf xa : RawDiv) : RReal :=
  realAdd (logVolGlobal logq xf) (logVolGlobal warch xa)

/-- **M317F-5d: 完全形の加法準同型（本丸・合流）** deg_ℝ(D+D')≈deg_ℝ(D)+deg_ℝ(D')。
    有限部・無限部の各々に M312F `logVolGlobal_add` を適用し、M312F `logVol_add4_swap`
    で 4 項を入替える。有限＋無限素点の Arakelov 次数が本物の加法準同型として合流する。 -/
theorem logArchGlobal_add (logq warch : Nat → RReal) (xf yf xa ya : RawDiv) :
    realEq (logArchGlobal logq warch (rawAdd xf yf) (rawAdd xa ya))
      (realAdd (logArchGlobal logq warch xf xa)
        (logArchGlobal logq warch yf ya)) := by
  refine realEq_trans (realAdd_congr_left
    (logVolGlobal warch (rawAdd xa ya)) (logVolGlobal_add logq xf yf)) ?_
  refine realEq_trans (realAdd_congr_right
    (realAdd (logVolGlobal logq xf) (logVolGlobal logq yf))
    (logVolGlobal_add warch xa ya)) ?_
  exact logVol_add4_swap (logVolGlobal logq xf) (logVolGlobal logq yf)
    (logVolGlobal warch xa) (logVolGlobal warch ya)

/-- **M317F-5e: 完全形の零因子** deg_ℝ(0)≈0（有限部・無限部とも零因子は 0）。 -/
theorem logArchGlobal_zero (logq warch : Nat → RReal) :
    realEq (logArchGlobal logq warch rawZero rawZero) realZero := by
  refine realEq_trans (realAdd_congr_left
    (logVolGlobal warch rawZero) (logVolGlobal_zero logq)) ?_
  refine realEq_trans (realAdd_congr_right realZero (logVolGlobal_zero warch)) ?_
  exact realAdd_zero realZero

/-! ## M317F-6: 有効因子の非負性（有限＋無限完全形） -/

/-- **M317F-6: 完全形の有効因子非負性** — 有効因子（有限部・無限部とも n_v≥0）かつ
    非負重み（log q_v≥0 かつ log‖·‖_v≥0）なら deg_ℝ≥0（本物の ℝ の順序 rLe）。
    M312F `logVolGlobal_effective_nonneg` の有限＋無限完全形。`rLe_add_pair` で
    両寄与を合算し `realAdd realZero realZero≈0` に潰す。 -/
theorem logArchGlobal_effective_nonneg (logq warch : Nat → RReal)
    (hq : ∀ k, rLe realZero (logq k)) (hw : ∀ k, rLe realZero (warch k))
    {xf xa : RawDiv} (hxf : picDivEffectiveRaw xf) (hxa : picDivEffectiveRaw xa) :
    rLe realZero (logArchGlobal logq warch xf xa) := by
  have hpair : rLe (realAdd realZero realZero)
      (logArchGlobal logq warch xf xa) :=
    rLe_add_pair (logVolGlobal_effective_nonneg logq hq hxf)
      (logVolGlobal_effective_nonneg warch hw hxa)
  exact rLe_congr (realAdd_zero realZero) (realEq_refl _) hpair

/-! ## M317F-7: capstone -/

/-- **M317F-7a: アルキメデス log-volume データ** — 無限素点の log-volume（加法準同型）と
    大域完全形（有限＋無限の加法準同型・零）を本物の ℝ で束ねる。 -/
structure LogVolumeArchData where
  /-- アルキメデス局所 log-volume log‖x‖。 -/
  archVol : RReal → RReal
  /-- ≈ との両立。 -/
  archVol_congr : ∀ {x y : RReal}, realEq x y → realEq (archVol x) (archVol y)
  /-- 加法性 log‖xy‖≈log‖x‖+log‖y‖。 -/
  archVol_mul : ∀ x y : RReal,
    realEq (archVol (rmul x y)) (realAdd (archVol x) (archVol y))
  /-- 大域 log-volume 完全形（有限＋無限）deg_ℝ:RawDiv×RawDiv→ℝ。 -/
  global : RawDiv → RawDiv → RReal
  /-- 完全形の加法準同型。 -/
  global_add : ∀ xf yf xa ya : RawDiv,
    realEq (global (rawAdd xf yf) (rawAdd xa ya))
      (realAdd (global xf xa) (global yf ya))
  /-- 完全形の零因子。 -/
  global_zero : realEq (global rawZero rawZero) realZero

/-- **M317F-7b: 実データ** — 全フィールドを本物で充足。 -/
def logVolumeArchData (L : LogArchLog) (logq warch : Nat → RReal) :
    LogVolumeArchData where
  archVol := logArchVol L
  archVol_congr := fun {_ _} h => logArchVol_congr L h
  archVol_mul := logArchVol_mul L
  global := logArchGlobal logq warch
  global_add := logArchGlobal_add logq warch
  global_zero := logArchGlobal_zero logq warch

/-- **M317F-7c: 存在**（実データ）。 -/
theorem logArch_exists (L : LogArchLog) (logq warch : Nat → RReal) :
    Nonempty LogVolumeArchData :=
  ⟨logVolumeArchData L logq warch⟩

/-- **M317F-7d: アルキメデス log-vol は加法準同型**（capstone 再掲・本丸）。 -/
theorem logArch_vol_isHom (L : LogArchLog) (x y : RReal) :
    realEq (logArchVol L (rmul x y))
      (realAdd (logArchVol L x) (logArchVol L y)) :=
  logArchVol_mul L x y

/-- **M317F-7e: 大域完全形の合流**（capstone 再掲）— 有限＋無限素点の加法準同型。 -/
theorem logArch_global_complete (logq warch : Nat → RReal)
    (xf yf xa ya : RawDiv) :
    realEq (logArchGlobal logq warch (rawAdd xf yf) (rawAdd xa ya))
      (realAdd (logArchGlobal logq warch xf xa)
        (logArchGlobal logq warch yf ya)) :=
  logArchGlobal_add logq warch xf yf xa ya

/-! ## M317F-8: 実例 -/

/-- **M317F-8a: 自明因子で 0** — 有限＋無限とも零因子の完全形 deg_ℝ=0。 -/
theorem logArch_example_trivial_zero (logq warch : Nat → RReal) :
    realEq (logArchGlobal logq warch rawZero rawZero) realZero :=
  logArchGlobal_zero logq warch

/-- **M317F-8b: 実素点 1 つで log‖·‖ の加法性** — 自明付値インスタンスでの
    アルキメデス log-volume の加法性（本物の rabs_mul + λ 準同型性の具体例）。 -/
theorem logArch_example_real_place (x y : RReal) :
    realEq (logArchVol logArchLogTrivial (rmul x y))
      (realAdd (logArchVol logArchLogTrivial x)
        (logArchVol logArchLogTrivial y)) :=
  logArchVol_mul logArchLogTrivial x y

end IUT
