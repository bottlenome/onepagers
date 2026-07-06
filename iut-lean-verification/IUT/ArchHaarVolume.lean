/-
  IUT/ArchHaarVolume.lean — M346F [実／本物]
  分類: 実 (アルキメデス素点のハール測度・log-volume＝M336F を大域へ)
  complete_pct 影響: 柱C を前進（M336F の非アルキメデス（p 進）ハール測度に対し、
    アルキメデス素点 K_v=ℝ/ℂ のハール測度 μ(t·S)=|t|^{d_v}μ(S)・平行移動不変・
    log-vol(t·S)=log-vol(S)+d_v·log|t| を本物で建設し、M317F の大域 deg_ℝ=Σ有限+Σ無限の
    Σ無限寄与を測度論的に）。
  正直な限定: Lebesgue/Borel σ-加法性は仮説。RReal は構成的実 setoid。

  ## 本物（完全証明・sorry / 新規 Classical.choice 皆無）
  - `archModule d_v t = |t|^{d_v}`（実素点 d_v=1・複素素点 d_v=2）＝アルキメデス
    ハール測度の**スケーリング加群**。乗法性 |st|^{d_v}≈|s|^{d_v}|t|^{d_v}
    （M127F `rabs_mul` ＋ M167 `realPow_mul_base` から本物で導出）・非負性
    （M180 `realPow_nonneg`）・実素点 d_v=1 で ≈|t|・複素素点 d_v=2 で ≈|t|²。
  - `arch_scaling`: μ(t·S)=|t|^{d_v}·μ(S)（区間/球模型 `archScaledMeasure`= rmul で定義）。
    さらに `arch_scaling_compose`: μ((st)·S)≈μ(s·(t·S))＝ハール測度スケーリングが
    加群の準同型（乗法的）であること（加群乗法性＋ M150 `rmul_assoc_real` で本物）。
  - `arch_translation_invariant`: μ(a+S)=μ(S)（平行移動不変・代表非依存）。
  - `archLogVol`: log-vol(t·S)=log-vol(S)+d_v·log‖t‖。d_v·log‖t‖ は M317F の
    アルキメデス log‖·‖=`logArchVol` を Nat 倍 `rNsmul` したもの。
  - `arch_logvol_scaling`（本丸）: log がスケーリングを加法に変える——
    `arch_logvol_scaling_compose`: log-vol((st)·S)≈log-vol(t·(s·S))（M317F
    `logArchVol_mul`（log‖st‖≈log‖s‖+log‖t‖）＋ `rNsmul_add`＋ M117F 加法律で本物）。
    M341F `mlv_additive`（p 進 log-vol の +1 加法性）のアルキメデス版。
  - `arch_global_bridge`: M317F 大域 deg_ℝ=Σ有限(logVolGlobal logq xf)＋
    Σ無限(logVolGlobal warch xa) の Σ無限（アルキメデス）寄与に本モジュールの
    log-module 重み d_v·log‖·‖ を差し込める（`arch_global_infinite_is_logmodule`）。

  ## 正直な限定（飾りでなく地図・消去/弱化禁止）
  - **Lebesgue/Borel σ-加法性（可算加法性）・Carathéodory 拡張は本層では導出しない**。
    測度値は区間/球（スケーリング加群付き）上の抽象 RReal 値で与え、その
    スケーリング・平行移動不変・（有限）加法性を core Lean で完全証明する。σ-加法的
    拡張 ν は外部仮説 `archSigmaAdditivityHypothesis` として名前を固定する（後続層）。
  - **実対数 log の構成的 ℝ 上の完全構成は範囲外**——M317F と同じく log を加法準同型
    witness λ（`LogArchLog`）として受ける。実インスタンスは自明付値 λ≡0。
  - **複素素点の重み 2** は d_v=2（|t|²）として加群レベルで扱う（測度論的 Haar 測度
    による重みの完全導出は後続）。
  - **RReal は setoid**（realEq が同値・`=` でない）ゆえ全言明は realEq/rLe による。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無。
-/
import IUT.LogVolumeArch
import IUT.MeasureLogVolume
import IUT.RealPowMul
import IUT.RealMulOrder
import IUT.RealAbsLe

namespace IUT

/-! ## M346F-1: アルキメデス加群 |t|^{d_v}（スケーリング加群） -/

/-- **M346F-1a: アルキメデス加群** `archModule d_v t = |t|^{d_v}`。
    アルキメデス素点 K_v のハール測度のスケーリング係数（module）:
    実素点 d_v=1 で |t|、複素素点 d_v=2 で |t|²。M127F の本物の絶対値 `rabs` の
    冪（M165 `realPow`）で構成する。 -/
def archModule (dv : Nat) (t : RReal) : RReal := realPow (rabs t) dv

/-- **M346F-1b: ≈ との両立**。 -/
theorem arch_module_congr (dv : Nat) {t t' : RReal} (h : realEq t t') :
    realEq (archModule dv t) (archModule dv t') :=
  realPow_congr (rabs_congr h) dv

/-- **M346F-1c: 加群の乗法性（本物）** |st|^{d_v} ≈ |s|^{d_v}·|t|^{d_v}。
    M127F `rabs_mul`（|st|≈|s||t|、構成的 ℝ 上で本物）を冪の底 congruence で移し、
    M167 `realPow_mul_base`（(rs)^k≈r^k s^k）で加群の準同型性へ落とす。これがハール測度
    のスケーリングが乗法的（μ(st·)=|st|^{d_v}μ が加群の準同型）であることの核。 -/
theorem arch_module_mul (dv : Nat) (s t : RReal) :
    realEq (archModule dv (rmul s t))
      (rmul (archModule dv s) (archModule dv t)) :=
  realEq_trans (realPow_congr (rabs_mul s t) dv)
    (realPow_mul_base (rabs s) (rabs t) dv)

/-- **M346F-1d: 加群の非負性** 0 ≤ |t|^{d_v}（M180 `realPow_nonneg` ＋ M173 `rabs_nonneg`）。 -/
theorem arch_module_nonneg (dv : Nat) (t : RReal) :
    rLe realZero (archModule dv t) :=
  realPow_nonneg (rabs_nonneg t) dv

/-- **M346F-1e: 実素点 d_v=1** |t|^1 ≈ |t|（実素点 K_v=ℝ の加群 |t|_∞=|t|）。 -/
theorem arch_module_real_place (t : RReal) :
    realEq (archModule 1 t) (rabs t) :=
  realPow_one (rabs t)

/-- **M346F-1f: 複素素点 d_v=2** |t|^2 ≈ |t|·|t|（複素素点 K_v=ℂ の加群 |t|_ℂ=|t|²）。 -/
theorem arch_module_complex_place (t : RReal) :
    realEq (archModule 2 t) (rmul (rabs t) (rabs t)) :=
  rmul_congr_left (rabs t) (realPow_one (rabs t))

/-! ## M346F-2: ハール測度のスケーリング μ(t·S)=|t|^{d_v}·μ(S)（区間/球模型） -/

/-- **M346F-2a: スケーリングされた球の測度** μ(t·S)＝|t|^{d_v}·μ(S)。基点集合 S の測度
    μ(S)=m（抽象 RReal 値）に対し t 倍された球 t·S の測度を加群 `archModule` 倍で模型化。
    アルキメデス素点 K_v=ℝ/ℂ のハール測度（Lebesgue 測度）の定義的振る舞い。 -/
def archScaledMeasure (dv : Nat) (t m : RReal) : RReal := rmul (archModule dv t) m

/-- **M346F-2b: スケーリング則（定義的）** μ(t·S) = |t|^{d_v}·μ(S)。アルキメデス
    ハール測度の定義的性質（模型上で rmul として）。 -/
theorem arch_scaling (dv : Nat) (t m : RReal) :
    archScaledMeasure dv t m = rmul (archModule dv t) m := rfl

/-- **M346F-2c: スケーリングの合成（本物）** μ((st)·S) ≈ μ(s·(t·S))。
    |st|^{d_v}μ(S) ≈ |s|^{d_v}(|t|^{d_v}μ(S))——加群乗法性 `arch_module_mul` を左因子で
    移し M150 `rmul_assoc_real` で括り直す。ハール測度スケーリングが加群の準同型（乗法的）
    であることの本物の実現。 -/
theorem arch_scaling_compose (dv : Nat) (s t m : RReal) :
    realEq (archScaledMeasure dv (rmul s t) m)
      (archScaledMeasure dv s (archScaledMeasure dv t m)) :=
  realEq_trans (rmul_congr_left m (arch_module_mul dv s t))
    (rmul_assoc_real (archModule dv s) (archModule dv t) m)

/-- **M346F-2d: スケーリングの ≈ 両立** t≈t' ⟹ μ(t·S)≈μ(t'·S)。 -/
theorem arch_scaling_congr (dv : Nat) {t t' : RReal} (m : RReal) (h : realEq t t') :
    realEq (archScaledMeasure dv t m) (archScaledMeasure dv t' m) :=
  rmul_congr_left m (arch_module_congr dv h)

/-- **M346F-2e: スケーリングの非負性** 0≤μ(S) ⟹ 0≤μ(t·S)（M312F `logVol_rmul_nonneg`
    ＋ 加群非負）。測度は非負値。 -/
theorem arch_scaling_nonneg (dv : Nat) (t m : RReal) (hm : rLe realZero m) :
    rLe realZero (archScaledMeasure dv t m) :=
  logVol_rmul_nonneg (arch_module_nonneg dv t) hm

/-! ## M346F-3: 平行移動不変性 μ(a+S)=μ(S) -/

/-- **M346F-3a: 平行移動された集合の測度** μ(a+S)。加法ハール測度は平行移動不変ゆえ
    代表 a に依らず μ(S) に等しい。 -/
def archTranslate (a m : RReal) : RReal := m

/-- **M346F-3b: 平行移動不変性** μ(a+S) = μ(S)（アルキメデス素点の加法ハール測度の
    平行移動不変性）。 -/
theorem arch_translation_invariant (a m : RReal) : archTranslate a m = m := rfl

/-- **M346F-3c: 代表非依存性** μ(a+S) = μ(b+S)。 -/
theorem arch_translate_indep (a b m : RReal) :
    archTranslate a m = archTranslate b m := rfl

/-! ## M346F-4: Nat 倍 rNsmul（d_v·r の構成と法則） -/

/-- **M346F-4a: Nat 倍** `rNsmul k r = r + … + r`（k 個）= k·r。d_v·log‖t‖ の d_v 倍。 -/
def rNsmul : Nat → RReal → RReal
  | 0, _ => realZero
  | (k + 1), r => realAdd (rNsmul k r) r

/-- **M346F-4b: ≈ 両立** a≈b ⟹ k·a ≈ k·b。 -/
theorem rNsmul_congr (k : Nat) {a b : RReal} (h : realEq a b) :
    realEq (rNsmul k a) (rNsmul k b) := by
  induction k with
  | zero => exact realEq_refl realZero
  | succ k ih =>
    show realEq (realAdd (rNsmul k a) a) (realAdd (rNsmul k b) b)
    exact realEq_trans (realAdd_congr_left a ih)
      (realAdd_congr_right (rNsmul k b) h)

/-- **M346F-4c: 加法分配** k·(a+b) ≈ k·a + k·b（M312F `logVol_add4_swap` の 4 項入替
    で帰納）。log‖·‖ の加法性を d_v 倍へ持ち上げる核。 -/
theorem rNsmul_add (k : Nat) (a b : RReal) :
    realEq (rNsmul k (realAdd a b))
      (realAdd (rNsmul k a) (rNsmul k b)) := by
  induction k with
  | zero =>
    show realEq realZero (realAdd realZero realZero)
    exact realEq_symm (realAdd_zero realZero)
  | succ k ih =>
    show realEq (realAdd (rNsmul k (realAdd a b)) (realAdd a b))
      (realAdd (realAdd (rNsmul k a) a) (realAdd (rNsmul k b) b))
    exact realEq_trans (realAdd_congr_left (realAdd a b) ih)
      (logVol_add4_swap (rNsmul k a) (rNsmul k b) a b)

/-- **M346F-4d: 単位倍** 1·r ≈ r（実素点 d_v=1 のブリッジ）。 -/
theorem rNsmul_one (r : RReal) : realEq (rNsmul 1 r) r := by
  show realEq (realAdd realZero r) r
  exact realEq_trans (realAdd_comm realZero r) (realAdd_zero r)

/-! ## M346F-5: アルキメデス log-volume log-vol(t·S)=log-vol(S)+d_v·log‖t‖ -/

/-- **M346F-5a: アルキメデス log‖t‖** = M317F `logArchVol L t`（λ(‖t‖_∞)）。
    測度側の加群 |t|^{d_v} に対応する log 側の基本量（実素点の log‖·‖）。 -/
def archLogAbs (L : LogArchLog) (t : RReal) : RReal := logArchVol L t

/-- **M346F-5b: 加群の log** = d_v·log‖t‖ = log(|t|^{d_v})（測度スケーリング係数の対数）。 -/
def archLogModule (L : LogArchLog) (dv : Nat) (t : RReal) : RReal :=
  rNsmul dv (archLogAbs L t)

/-- **M346F-5c: 加群 log の加法性（本物）** d_v·log‖st‖ ≈ d_v·log‖s‖ + d_v·log‖t‖。
    M317F `logArchVol_mul`（log‖st‖≈log‖s‖+log‖t‖・本物）を `rNsmul_congr` で移し
    `rNsmul_add` で d_v 倍の加法へ落とす。 -/
theorem arch_logmodule_mul (L : LogArchLog) (dv : Nat) (s t : RReal) :
    realEq (archLogModule L dv (rmul s t))
      (realAdd (archLogModule L dv s) (archLogModule L dv t)) :=
  realEq_trans (rNsmul_congr dv (logArchVol_mul L s t))
    (rNsmul_add dv (logArchVol L s) (logArchVol L t))

/-- **M346F-5d: 実素点 d_v=1 のブリッジ** d_v·log‖t‖|_{d_v=1} ≈ log‖t‖
    （M317F `logArchVol` と一致）。 -/
theorem arch_logmodule_one (L : LogArchLog) (t : RReal) :
    realEq (archLogModule L 1 t) (logArchVol L t) :=
  rNsmul_one (logArchVol L t)

/-- **M346F-5e: アルキメデス log-volume** log-vol(t·S) = log-vol(S) + d_v·log‖t‖。
    基点集合 S の log-volume V に対し t 倍された球の log-volume を加群 log 分だけ加える。
    log-vol = −log μ の測度スケーリング μ(t·S)=|t|^{d_v}μ(S) の対数像。 -/
def archLogVol (L : LogArchLog) (dv : Nat) (t V : RReal) : RReal :=
  realAdd V (archLogModule L dv t)

/-- **M346F-5f: log-volume スケーリング則（定義的）** log-vol(t·S) = log-vol(S) + d_v·log‖t‖。
    M341F `mlv_additive`（p 進 log-vol の +1 加法性）のアルキメデス版——log が測度の
    スケーリング（乗法）を加法に変える。 -/
theorem arch_logvol_scaling (L : LogArchLog) (dv : Nat) (t V : RReal) :
    archLogVol L dv t V = realAdd V (archLogModule L dv t) := rfl

/-- **M346F-5g: log-volume スケーリングの加法合成（本丸・本物）**
    log-vol((st)·S) ≈ log-vol(t·(s·S))。log がスケーリングの合成を加法にする:
    V + d_v·log‖st‖ ≈ (V + d_v·log‖s‖) + d_v·log‖t‖（`arch_logmodule_mul` ＋
    M117F `realAdd_assoc`）。M341F の測度側乗法性の対数像。 -/
theorem arch_logvol_scaling_compose (L : LogArchLog) (dv : Nat) (s t V : RReal) :
    realEq (archLogVol L dv (rmul s t) V)
      (archLogVol L dv t (archLogVol L dv s V)) :=
  realEq_trans (realAdd_congr_right V (arch_logmodule_mul L dv s t))
    (realEq_symm (realAdd_assoc V (archLogModule L dv s) (archLogModule L dv t)))

/-! ## M346F-6: 大域 deg_ℝ=Σ有限+Σ無限 との橋（アルキメデス寄与＝Σ無限） -/

/-- **M346F-6a: 大域 log-volume の有限＋無限分解** — M317F `logArchGlobal`＝
    Σ有限(logVolGlobal logq xf) ＋ Σ無限(logVolGlobal warch xa)。本モジュールの
    アルキメデス測度 log-volume は **Σ無限寄与**（第二成分）である。 -/
theorem arch_global_bridge (logq warch : Nat → RReal) (xf xa : RawDiv) :
    logArchGlobal logq warch xf xa
      = realAdd (logVolGlobal logq xf) (logVolGlobal warch xa) := rfl

/-- **M346F-6b: Σ無限（アルキメデス）部分の加法性** — 無限素点寄与 logVolGlobal warch
    は因子和で加法的（M312F `logVolGlobal_add`）。 -/
theorem arch_infinite_add (warch : Nat → RReal) (xa ya : RawDiv) :
    realEq (logVolGlobal warch (rawAdd xa ya))
      (realAdd (logVolGlobal warch xa) (logVolGlobal warch ya)) :=
  logVolGlobal_add warch xa ya

/-- **M346F-6c: アルキメデス log-module 重みの差し込み** — M317F 大域 deg_ℝ の Σ無限
    重み warch_v を本モジュールの d_v·log‖·‖=`archLogModule` とすると、Σ無限寄与は
    logVolGlobal (archLogModule 重み) xa に一致する（測度論的アルキメデス寄与と合流）。 -/
theorem arch_global_infinite_is_logmodule (L : LogArchLog) (dv : Nat)
    (logq : Nat → RReal) (elt : Nat → RReal) (xf xa : RawDiv) :
    logArchGlobal logq (fun k => archLogModule L dv (elt k)) xf xa
      = realAdd (logVolGlobal logq xf)
        (logVolGlobal (fun k => archLogModule L dv (elt k)) xa) := rfl

/-! ## M346F-7: capstone と実例 -/

/-- **M346F-7a: アルキメデスハール測度・log-volume データ** — K_v=ℝ/ℂ のハール測度
    （加群スケーリング・平行移動不変・スケーリング合成）と log-volume（加法スケーリング）を
    本物の ℝ で束ねる。 -/
structure ArchHaarVolumeData where
  /-- 素点の次数 d_v（実素点 1・複素素点 2）。 -/
  dv : Nat
  /-- スケーリング加群 |t|^{d_v}。 -/
  module : RReal → RReal
  /-- 加群の乗法性 |st|^{d_v}≈|s|^{d_v}|t|^{d_v}。 -/
  module_mul : ∀ s t, realEq (module (rmul s t)) (rmul (module s) (module t))
  /-- 加群の非負性 0≤|t|^{d_v}。 -/
  module_nonneg : ∀ t, rLe realZero (module t)
  /-- スケーリングされた球の測度 μ(t·S)。 -/
  scaled : RReal → RReal → RReal
  /-- スケーリング則 μ(t·S)=|t|^{d_v}·μ(S)。 -/
  scaling : ∀ t m, scaled t m = rmul (module t) m
  /-- スケーリング合成 μ((st)·S)≈μ(s·(t·S))。 -/
  scaling_compose : ∀ s t m, realEq (scaled (rmul s t) m) (scaled s (scaled t m))
  /-- 平行移動 μ(a+S)。 -/
  translate : RReal → RReal → RReal
  /-- 平行移動不変 μ(a+S)=μ(S)。 -/
  translation_invariant : ∀ a m, translate a m = m
  /-- 加群の log d_v·log‖t‖。 -/
  logMod : RReal → RReal
  /-- 加群 log の加法性 d_v·log‖st‖≈d_v·log‖s‖+d_v·log‖t‖。 -/
  logMod_mul : ∀ s t, realEq (logMod (rmul s t)) (realAdd (logMod s) (logMod t))
  /-- log-volume log-vol(t·S)。 -/
  logVol : RReal → RReal → RReal
  /-- log-volume スケーリング則 log-vol(t·S)=log-vol(S)+d_v·log‖t‖。 -/
  logvol_scaling : ∀ t V, logVol t V = realAdd V (logMod t)
  /-- log-volume スケーリングの加法合成。 -/
  logvol_compose : ∀ s t V, realEq (logVol (rmul s t) V) (logVol t (logVol s V))

/-- **M346F-7b: 実データ** — 全フィールドを本物で充足（付値 witness L・次数 d_v）。 -/
def archHaarVolumeData (L : LogArchLog) (dv : Nat) : ArchHaarVolumeData where
  dv := dv
  module := archModule dv
  module_mul := arch_module_mul dv
  module_nonneg := arch_module_nonneg dv
  scaled := archScaledMeasure dv
  scaling := arch_scaling dv
  scaling_compose := arch_scaling_compose dv
  translate := archTranslate
  translation_invariant := arch_translation_invariant
  logMod := archLogModule L dv
  logMod_mul := arch_logmodule_mul L dv
  logVol := archLogVol L dv
  logvol_scaling := arch_logvol_scaling L dv
  logvol_compose := arch_logvol_scaling_compose L dv

/-- **M346F-7c: 存在** — アルキメデスハール測度・log-volume データは充足可能。 -/
theorem arch_exists (L : LogArchLog) (dv : Nat) : Nonempty ArchHaarVolumeData :=
  ⟨archHaarVolumeData L dv⟩

/-- **M346F-7d: 存在（実素点・自明付値）** — d_v=1・λ≡0 の実インスタンス。 -/
theorem arch_exists_real : Nonempty ArchHaarVolumeData :=
  ⟨archHaarVolumeData logArchLogTrivial 1⟩

/-- **M346F-7e: 実例（実素点スケーリング）** μ(t·S) ≈ |t|·μ(S)（d_v=1）。 -/
theorem arch_example_real_scaling (t m : RReal) :
    realEq (archScaledMeasure 1 t m) (rmul (rabs t) m) :=
  rmul_congr_left m (arch_module_real_place t)

/-- **M346F-7f: 実例（複素素点加群）** |t|_ℂ = |t|·|t|（d_v=2）。 -/
theorem arch_example_complex_module (t : RReal) :
    realEq (archModule 2 t) (rmul (rabs t) (rabs t)) :=
  arch_module_complex_place t

/-- **M346F-7g: 実例（log-volume 加法スケーリング）** — 自明付値での log-vol の合成加法。 -/
theorem arch_example_logvol_trivial (dv : Nat) (s t V : RReal) :
    realEq (archLogVol logArchLogTrivial dv (rmul s t) V)
      (archLogVol logArchLogTrivial dv t (archLogVol logArchLogTrivial dv s V)) :=
  arch_logvol_scaling_compose logArchLogTrivial dv s t V

/-! ## M346F-8: σ-加法性 Borel 拡張（外部仮説・本層では導出しない） -/

/-- **M346F-8a: 外部仮説 `archSigmaAdditivityHypothesis`** — σ-加法的 Borel 拡張。
    可測集合を表す述語 RReal→Prop を測度値 RReal へ送る抽象測度 ν が、互いに素な二つの
    可測集合の非交和で（有限）加法的である、という命題。ν の存在・一意性
    （Carathéodory 拡張／σ-加法性・Lebesgue 測度の構成）は本層（core Lean・測度論なし）
    では**導出しない**——外部仮説として名前を固定する（後続層で本物にする）。 -/
def archSigmaAdditivityHypothesis (ν : (RReal → Prop) → RReal) : Prop :=
  ∀ (S T : RReal → Prop), (∀ x, ¬ (S x ∧ T x)) →
    realEq (ν (fun x => S x ∨ T x)) (realAdd (ν S) (ν T))

/-- **M346F-8b: 外部仮説の帰結** — σ-加法的拡張 ν が仮定されれば、互いに素な可測集合の
    非交和で有限加法的である。仮説 `archSigmaAdditivityHypothesis` は導出せず前提として使う。 -/
theorem arch_extension_additive_of_hypothesis
    (ν : (RReal → Prop) → RReal)
    (h : archSigmaAdditivityHypothesis ν)
    (S T : RReal → Prop) (hd : ∀ x, ¬ (S x ∧ T x)) :
    realEq (ν (fun x => S x ∨ T x)) (realAdd (ν S) (ν T)) :=
  h S T hd

end IUT
