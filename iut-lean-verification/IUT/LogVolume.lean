/-
  IUT/LogVolume.lean — M312F（柱C 先行建設: **実数値 log-volume ＝ Arakelov 次数**
                       — 因子の次数を本物の ℝ 上の順序準同型へ拡張する中核）

  ── 主要成果の分類: **[実]**（本物の先行建設 (b) かつ既存模型の (a) 昇格）。
     IUT の log-volume は「log-shell の体積」であり、各素点 v での寄与は
     非アルキメデス側では −v(x)·log(q_v)（付値×重み log q_v）、大域では
     それらの有限和 deg_ℝ(D)=Σ_v n_v·log(q_v)＝**Arakelov 次数**（実数値）である。
     本モジュールは、M307F `PicardDivisor` の**因子群 Div**（素点上の有限台
     ℤ-値関数の自由アーベル群）と、その**整数値次数** `picDivDegree`（Div→ℤ の
     本物の群 Hom）を、M115F〜M180 でスクラッチ構成した**本物の ℝ**（正則実数列
     `RReal`・`realAdd`/`rmul`/`rLe`/`realEq`）の上へ持ち上げ、**実重み**
     `logq : ℕ→ℝ`（各素点の log q_v を実係数 witness として受け取る）で重み付けた
     **実数値 log-volume** `logVolGlobal` を建てる。toy 主語なし——主語は M307F の
     本物の因子代表 `RawDiv` と本物の ℝ であり、加法性・Frobenius 斉次性・有効因子
     非負性・rawEq 不変性（ℝ は setoid ゆえ realEq で）を core Lean のみで完全証明する。

  complete_pct 影響: **柱C（Frobenioid/log-volume）の実 IUT 完全証明率を前進させる**。
  既存の柱C の log-volume は二段階の模型であった:
    ・M131F `rlogVol`（LogVolBridge）: **QDiv**（M51F の有効因子**モノイド**、素点重複度
      が **ℕ 値**、逆元なし）の次数 degZ を `qToReal∘ratOfInt` で ℝ に読むもの。
      重みは `w : ℕ→ℕ`（**自然数**重み）で degZ の内側に畳み込まれていた。
    ・M99F `intVolumeTheory`（VolumeModel）: Region=ℤ・vol=id の inhabitation 模型。
  本モジュールはこれを二方向で**本物へ昇格 (a)**する:
    (1) 台となる対象を「有効因子モノイド QDiv（ℕ 値・逆元なし）」から M307F の
        **因子群 Div（ℤ 値・逆元あり）の代表 RawDiv** へ——負係数（有効でない因子）も
        扱える大域体の因子群の上に log-volume を載せる。
    (2) 重みを「ℕ 値 w」から**実重み logq:ℕ→ℝ**（log q_v を本物の ℝ の元＝実係数
        witness として持つ）へ——次数を **ℤ から本物の ℝ の Arakelov 次数**へ拡張する。
  これにより「因子の次数＝log-volume の離散部分」（M307F deg into ℤ）は、
  **実重み付き実数値 Arakelov 次数** deg_ℝ:Div→ℝ（加法順序準同型）へと本物で昇格する。
  さらに **unit 重み（logq≡1）では logVolGlobal が intToReal∘picDivDegree に一致**する
  ことを realEq で証明し、M307F の commit 済み整数次数 Hom との**本物のブリッジ**を張る。

  ## 検証する中核（全て sorry なし・新規 Classical.choice なし）

  * M312F-0 `logVolSum` / `logVolSum_congr` / `logVolSum_add` / `logVolSum_ext_zero` /
    `logVolSum_stable` / `logVolSum_smul` / `logVolSum_zero_coeff`
                              — 実重み付き ℝ-値有限和のインフラ（加法性・台安定性・
                                 スカラー斉次性・零係数消滅、realEq/= で完全証明）
  * M312F-1 `logVolLocal` / `logVolLocal_add` / `logVolLocal_zero`
                              — **局所 log-volume** −v(x)·log q_v の加法順序準同型
                                 （ℤ→ℝ、logVolLocal(n+m)≈logVolLocal n+logVolLocal m）
  * M312F-2 `logVolGlobal` / `logVolGlobal_wd`
                              — **大域 log-volume（Arakelov 次数）** deg_ℝ(D)=Σ n_v log q_v
                                 と rawEq 不変性（ℝ は setoid ゆえ realEq で well-defined）
  * M312F-3 `logVolGlobal_add`  — **加法準同型** deg_ℝ(D+D')≈deg_ℝ(D)+deg_ℝ(D')
                                 （M307F picDivDegree.map_mul の実数値版・本丸）
  * M312F-4 `logVolGlobal_zero` / `logVolGlobal_zero_coeff` / `logVol_product_formula_trivial`
                              — 零因子・零係数因子は deg_ℝ=0（体/自明付値の単項因子は
                                 Arakelov 次数 0＝**積公式の有限部分**）
  * M312F-5 `logVol_rmul_nonneg` / `logVolSum_nonneg` / `logVolGlobal_effective_nonneg`
                              — **有効因子は logVol≥0**（n_v≥0 かつ log q_v≥0 ⟹ deg_ℝ≥0、
                                 M240F 有効順序単調性と概念整合、rLe で完全証明）
  * M312F-6 `logVolGlobal_frob` — **Frobenius 斉次性** deg_ℝ([n]D)≈n·deg_ℝ(D)
                                 （M307F picDiv_frob_degree の実数値版）
  * M312F-7 `logVolUnit` / `logVolSum_unweighted` / `logVolGlobal_unweighted_degree`
                              — **M307F 整数次数とのブリッジ**: unit 重みで
                                 deg_ℝ(D)≈intToReal(picDivDegree D)（committed Hom への接続）
  * M312F-8 capstone `LogVolumeData` / `logVolumeData` / `logVol_exists` /
    `logVol_degree_isHom` / `logVol_effective_nonneg`

  ## 正直な限定（何が本物で何が後続か・消去/弱化禁止）

  - **本物（完全証明）**:
    ・logVolGlobal が **rawEq 不変**（realEq、ℝ は setoid）＝因子群 Div の上に
      well-defined であること（台安定性 logVolSum_stable 経由、完全）。
    ・logVolGlobal が **加法準同型** deg_ℝ(D+D')≈deg_ℝ(D)+deg_ℝ(D')（実数の加法 realAdd、
      M307F picDivDegree.map_mul のℝ 化、完全）。
    ・logVolLocal（局所寄与 n·log q_v）が **ℤ→ℝ の加法準同型**（完全）。
    ・**有効因子（n_v≥0）かつ非負重み（log q_v≥0）なら logVol≥0**（本物の ℝ の順序 rLe、
      M307F picDivEffectiveRaw と接続、完全）。
    ・**Frobenius 斉次性** deg_ℝ([n]D)≈n·deg_ℝ(D)（rmul、完全）。
    ・**unit 重みで logVolGlobal≈intToReal∘picDivDegree**（M307F の commit 済み整数次数
      Hom への本物のブリッジ、完全）。
    ・零/零係数因子（体・自明付値の単項因子）は deg_ℝ=0（積公式の有限部分、完全）。
  - **正直申告（未達・骨組み・後続。飾りでなく地図）**:
    ・**実重み logq:ℕ→ℝ はパラメータ**として受け取る（各素点の log q_v を本物の ℝ の
      元＝実係数 witness として持つ形）。log q_v の**超越性・具体値**（log 2, log 3, …の
      構成）は本モジュールの範囲外——係数として扱えば log-volume の代数的・順序的内容は
      本物で閉じる。特定の局所体上で q_v から log q_v を実構成し `logq` を実体化するのは後続。
    ・**アルキメデス素点の log|x|**（複素/実素点の寄与）は本モジュールでは扱わない。
      非アルキメデス（付値＝M307F の deg 成分）×実重みの部分を本物で建てる。log|·| の
      構成（実対数の後続整備）と両素点の統合は後続。
    ・**積公式（Artin-Whaples）の完全証明**（大域体の全素点で Σ_v v(x)·log q_v=0）は
      範囲外。本モジュールは**有限部分**——零係数因子（体/自明付値 M307F picDivTrivialVal の
      単項因子）が deg_ℝ=0——を本物で与える。非自明大域体での完全積公式（log q_v の
      具体値が満たす消去律）は大域類体論的入力を要すので後続。
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ logVolGlobal を「Div→ℝ の Grp Hom」
      として `=` で言明せず、代表 RawDiv 上で **realEq による準同型性**として言明する
      （M131F rlogVol と同じ正直な形）。Grp 圏の ℝ 係数対象化（実数の商群化）は後続。
    ・**測度論的 Haar 測度の完全構成**（log-shell の体積を Haar 測度で定義）は後続。
      本モジュールは Arakelov 次数（測度論的 log-volume の代数的・順序的核）を本物で与える。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無。
-/
import IUT.IntRealBridge
import IUT.PicardDivisor
import IUT.RealRingLaws
import IUT.RealMulOrder
import IUT.GeomRlimComplete

namespace IUT

/-! ## M312F-0: 実重み付き ℝ-値有限和のインフラ -/

/-- **M312F-0a: 実数値 log-volume 和** logVolSum c logq n
    = Σ_{k<n} (c k)·(logq k)（各項 rmul(intToReal(c k))(logq k)＝n_k·log q_k）。
    非アルキメデス側の局所 log-volume の有限和（Arakelov 次数の本体）。 -/
def logVolSum (c : Nat → Int) (logq : Nat → RReal) : Nat → RReal
  | 0 => realZero
  | n + 1 => realAdd (logVolSum c logq n) (rmul (intToReal (c n)) (logq n))

/-- **M312F-0b: 合同性** — 係数が各点で等しければ和は等しい（`=`、項が literally 一致）。 -/
theorem logVolSum_congr {c c' : Nat → Int} (logq : Nat → RReal)
    (h : ∀ k, c k = c' k) : ∀ n, logVolSum c logq n = logVolSum c' logq n := by
  intro n
  induction n with
  | zero => rfl
  | succ p ih =>
    show realAdd (logVolSum c logq p) (rmul (intToReal (c p)) (logq p))
        = realAdd (logVolSum c' logq p) (rmul (intToReal (c' p)) (logq p))
    rw [ih, h p]

/-- 4 項の入れ替え補題 (a+b)+(c+d) ≈ (a+c)+(b+d)（加法の結合・可換で）。 -/
theorem logVol_add4_swap (a b c d : RReal) :
    realEq (realAdd (realAdd a b) (realAdd c d))
      (realAdd (realAdd a c) (realAdd b d)) := by
  refine realEq_trans (realAdd_assoc a b (realAdd c d)) ?_
  refine realEq_trans (realAdd_congr_right a (realEq_symm (realAdd_assoc b c d))) ?_
  refine realEq_trans (realAdd_congr_right a (realAdd_congr_left d (realAdd_comm b c))) ?_
  refine realEq_trans (realAdd_congr_right a (realAdd_assoc c b d)) ?_
  exact realEq_symm (realAdd_assoc a c (realAdd b d))

/-- **M312F-0c: 加法性** Σ(c+c') ≈ Σc + Σc'（realEq、Arakelov 次数の加法性の核）。 -/
theorem logVolSum_add (c c' : Nat → Int) (logq : Nat → RReal) :
    ∀ n, realEq (logVolSum (fun k => c k + c' k) logq n)
      (realAdd (logVolSum c logq n) (logVolSum c' logq n)) := by
  intro n
  induction n with
  | zero => exact realEq_symm (realAdd_zero realZero)
  | succ p ih =>
    have termEq : realEq (rmul (intToReal (c p + c' p)) (logq p))
        (realAdd (rmul (intToReal (c p)) (logq p))
          (rmul (intToReal (c' p)) (logq p))) :=
      realEq_trans (rmul_congr_left (logq p) (realEq_symm (intToReal_add (c p) (c' p))))
        (rmul_add_right (intToReal (c p)) (intToReal (c' p)) (logq p))
    show realEq (realAdd (logVolSum (fun k => c k + c' k) logq p)
          (rmul (intToReal (c p + c' p)) (logq p)))
        (realAdd (realAdd (logVolSum c logq p) (rmul (intToReal (c p)) (logq p)))
          (realAdd (logVolSum c' logq p) (rmul (intToReal (c' p)) (logq p))))
    refine realEq_trans (realAdd_congr_left
      (rmul (intToReal (c p + c' p)) (logq p)) ih) ?_
    refine realEq_trans (realAdd_congr_right
      (realAdd (logVolSum c logq p) (logVolSum c' logq p)) termEq) ?_
    exact logVol_add4_swap (logVolSum c logq p) (logVolSum c' logq p)
      (rmul (intToReal (c p)) (logq p)) (rmul (intToReal (c' p)) (logq p))

/-- ℤ=0 のスカラー項は 0（intToReal 0 = realZero の defeq + rmul_zero）。 -/
theorem logVol_scale_zero (r : RReal) :
    realEq (rmul (intToReal (0 : Int)) r) realZero :=
  realEq_trans (rmul_comm (intToReal (0 : Int)) r)
    (realEq_trans (rmul_congr_right r (realEq_refl realZero)) (rmul_zero r))

/-- 係数 0 の項は log-volume 0。 -/
theorem logVol_term_zero (logq : Nat → RReal) {c : Nat → Int} {k : Nat}
    (h : c k = 0) : realEq (rmul (intToReal (c k)) (logq k)) realZero := by
  rw [h]
  exact logVol_scale_zero (logq k)

/-- **M312F-0d: 台の外への延長** — m 以上で消える係数は m+j まで和が m と同じ（realEq）。 -/
theorem logVolSum_ext_zero (c : Nat → Int) (logq : Nat → RReal) (m : Nat)
    (hf : ∀ k, m ≤ k → c k = 0) :
    ∀ j, realEq (logVolSum c logq (m + j)) (logVolSum c logq m) := by
  intro j
  induction j with
  | zero => exact realEq_refl _
  | succ p ih =>
    show realEq (realAdd (logVolSum c logq (m + p))
          (rmul (intToReal (c (m + p))) (logq (m + p))))
        (logVolSum c logq m)
    have hterm : realEq (rmul (intToReal (c (m + p))) (logq (m + p))) realZero :=
      logVol_term_zero logq (hf (m + p) (Nat.le_add_right m p))
    refine realEq_trans (realAdd_congr_right (logVolSum c logq (m + p)) hterm) ?_
    refine realEq_trans (realAdd_zero (logVolSum c logq (m + p))) ?_
    exact ih

/-- **M312F-0e: 台安定性** — m 以上で消える係数は m ≤ n なら和が bound に依らない。 -/
theorem logVolSum_stable (c : Nat → Int) (logq : Nat → RReal) (m n : Nat)
    (hf : ∀ k, m ≤ k → c k = 0) (hmn : m ≤ n) :
    realEq (logVolSum c logq n) (logVolSum c logq m) := by
  obtain ⟨j, hj⟩ := Nat.le.dest hmn
  rw [← hj]
  exact logVolSum_ext_zero c logq m hf j

/-- **M312F-0f: スカラー斉次性** Σ(s·c) ≈ s·Σc（realEq、Frobenius 斉次性の核）。 -/
theorem logVolSum_smul (s : Int) (c : Nat → Int) (logq : Nat → RReal) :
    ∀ n, realEq (logVolSum (fun k => s * c k) logq n)
      (rmul (intToReal s) (logVolSum c logq n)) := by
  intro n
  induction n with
  | zero => exact realEq_symm (rmul_zero (intToReal s))
  | succ p ih =>
    have termEq : realEq (rmul (intToReal (s * c p)) (logq p))
        (rmul (intToReal s) (rmul (intToReal (c p)) (logq p))) :=
      realEq_trans (rmul_congr_left (logq p) (realEq_symm (intToReal_mul s (c p))))
        (rmul_assoc_real (intToReal s) (intToReal (c p)) (logq p))
    show realEq (realAdd (logVolSum (fun k => s * c k) logq p)
          (rmul (intToReal (s * c p)) (logq p)))
        (rmul (intToReal s)
          (realAdd (logVolSum c logq p) (rmul (intToReal (c p)) (logq p))))
    refine realEq_trans (realAdd_congr_left
      (rmul (intToReal (s * c p)) (logq p)) ih) ?_
    refine realEq_trans (realAdd_congr_right
      (rmul (intToReal s) (logVolSum c logq p)) termEq) ?_
    exact realEq_symm (rmul_add_left (logVolSum c logq p)
      (rmul (intToReal (c p)) (logq p)) (intToReal s))

/-- **M312F-0g: 零係数消滅** — 全係数 0 の和は 0（realEq）。 -/
theorem logVolSum_zero_coeff (c : Nat → Int) (logq : Nat → RReal)
    (h : ∀ k, c k = 0) : ∀ n, realEq (logVolSum c logq n) realZero := by
  intro n
  induction n with
  | zero => exact realEq_refl _
  | succ p ih =>
    show realEq (realAdd (logVolSum c logq p) (rmul (intToReal (c p)) (logq p)))
        realZero
    have ht := logVol_term_zero logq (h p)
    refine realEq_trans (realAdd_congr_right (logVolSum c logq p) ht) ?_
    refine realEq_trans (realAdd_zero (logVolSum c logq p)) ?_
    exact ih

/-! ## M312F-1: 局所 log-volume（各素点の寄与 n_v·log q_v） -/

/-- **M312F-1a: 局所 log-volume** — 素点 k での寄与 n·log q_k（= rmul(intToReal n)(logq k)）。
    非アルキメデス側の −v(x)·log q_v（付値×重み）の実体。 -/
def logVolLocal (logq : Nat → RReal) (k : Nat) (n : Int) : RReal :=
  rmul (intToReal n) (logq k)

/-- **M312F-1b: 局所 log-volume の加法性** — logVolLocal(n+m) ≈ logVolLocal n + logVolLocal m
    （ℤ→ℝ の加法準同型、付値の加法性 v(xy)=v(x)+v(y) の log-volume 版）。 -/
theorem logVolLocal_add (logq : Nat → RReal) (k : Nat) (n m : Int) :
    realEq (logVolLocal logq k (n + m))
      (realAdd (logVolLocal logq k n) (logVolLocal logq k m)) :=
  realEq_trans (rmul_congr_left (logq k) (realEq_symm (intToReal_add n m)))
    (rmul_add_right (intToReal n) (intToReal m) (logq k))

/-- **M312F-1c: 局所 log-volume の零** — logVolLocal 0 ≈ 0。 -/
theorem logVolLocal_zero (logq : Nat → RReal) (k : Nat) :
    realEq (logVolLocal logq k 0) realZero :=
  logVol_scale_zero (logq k)

/-! ## M312F-2: 大域 log-volume（Arakelov 次数）と rawEq 不変性 -/

/-- **M312F-2a: 大域 log-volume（Arakelov 次数）** — 因子 D（M307F RawDiv 代表）に対し
    deg_ℝ(D) = Σ_v n_v·log q_v（実数値）。M307F の整数次数 picDivDegree の実重み ℝ 化。 -/
def logVolGlobal (logq : Nat → RReal) (x : RawDiv) : RReal :=
  logVolSum x.coeff logq x.bound

/-- **M312F-2b: rawEq 不変性（well-definedness）** — 係数等価な因子代表は同じ Arakelov
    次数を持つ（realEq、ℝ は setoid）。台安定性で両者を max bound に揃え係数一致で閉じる。
    これにより logVolGlobal は因子群 Div=Quot rawEq の上に well-defined。 -/
theorem logVolGlobal_wd (logq : Nat → RReal) {x y : RawDiv} (h : rawEq x y) :
    realEq (logVolGlobal logq x) (logVolGlobal logq y) := by
  have hx : realEq (logVolSum x.coeff logq x.bound)
      (logVolSum x.coeff logq (Nat.max x.bound y.bound)) :=
    realEq_symm (logVolSum_stable x.coeff logq x.bound (Nat.max x.bound y.bound)
      x.vanish (Nat.le_max_left x.bound y.bound))
  have hy : realEq (logVolSum y.coeff logq (Nat.max x.bound y.bound))
      (logVolSum y.coeff logq y.bound) :=
    logVolSum_stable y.coeff logq y.bound (Nat.max x.bound y.bound)
      y.vanish (Nat.le_max_right x.bound y.bound)
  have hc : logVolSum x.coeff logq (Nat.max x.bound y.bound)
      = logVolSum y.coeff logq (Nat.max x.bound y.bound) :=
    logVolSum_congr logq h (Nat.max x.bound y.bound)
  refine realEq_trans hx ?_
  rw [hc]
  exact hy

/-! ## M312F-3: 加法準同型（本丸: deg_ℝ(D+D')≈deg_ℝ(D)+deg_ℝ(D')） -/

/-- **M312F-3: Arakelov 次数の加法準同型** — deg_ℝ(D+D') ≈ deg_ℝ(D)+deg_ℝ(D')。
    M307F `picDivDegree.map_mul`（deg into ℤ）の**実数値版**。次数関手の加法性が
    本物の実数の加法 realAdd として成立する。台安定性で各成分を自身の bound に揃える。 -/
theorem logVolGlobal_add (logq : Nat → RReal) (x y : RawDiv) :
    realEq (logVolGlobal logq (rawAdd x y))
      (realAdd (logVolGlobal logq x) (logVolGlobal logq y)) := by
  have s1 := logVolSum_add x.coeff y.coeff logq (Nat.max x.bound y.bound)
  have s2 : realEq (logVolSum x.coeff logq (Nat.max x.bound y.bound))
      (logVolSum x.coeff logq x.bound) :=
    logVolSum_stable x.coeff logq x.bound (Nat.max x.bound y.bound)
      x.vanish (Nat.le_max_left x.bound y.bound)
  have s3 : realEq (logVolSum y.coeff logq (Nat.max x.bound y.bound))
      (logVolSum y.coeff logq y.bound) :=
    logVolSum_stable y.coeff logq y.bound (Nat.max x.bound y.bound)
      y.vanish (Nat.le_max_right x.bound y.bound)
  refine realEq_trans s1 ?_
  refine realEq_trans (realAdd_congr_left
    (logVolSum y.coeff logq (Nat.max x.bound y.bound)) s2) ?_
  exact realAdd_congr_right (logVolSum x.coeff logq x.bound) s3

/-! ## M312F-4: 零因子・零係数因子（積公式の有限部分） -/

/-- **M312F-4a: 零因子の Arakelov 次数は 0**。 -/
theorem logVolGlobal_zero (logq : Nat → RReal) :
    realEq (logVolGlobal logq rawZero) realZero :=
  realEq_refl _

/-- **M312F-4b: 零係数因子の Arakelov 次数は 0**（realEq）。 -/
theorem logVolGlobal_zero_coeff (logq : Nat → RReal) {x : RawDiv}
    (h : ∀ k, x.coeff k = 0) : realEq (logVolGlobal logq x) realZero :=
  logVolSum_zero_coeff x.coeff logq h x.bound

/-- **M312F-4c: 積公式の有限部分** — 体/自明付値（M307F `picDivTrivialVal`）の
    **単項因子** div(a) は Arakelov 次数 0。全素点で v(a)=0（単項因子が零因子）ゆえ
    Σ_v v(a)·log q_v = 0＝Artin-Whaples 積公式の有限部分（体の場合）が本物で成立。
    非自明大域体での完全積公式（log q_v の具体値が満たす消去律）は大域類体論的入力を
    要すので後続。 -/
theorem logVol_product_formula_trivial {G : Grp} (logq : Nat → RReal) (a : G.carrier) :
    realEq (logVolGlobal logq (picDivPrincipalRaw (picDivTrivialVal G) a)) realZero :=
  logVolGlobal_zero_coeff logq (fun _ => rfl)

/-! ## M312F-5: 有効因子の非負性（log-shell 体積の効果性） -/

/-- **M312F-5a: 非負積** — 0≤a, 0≤b なら 0≤a·b（rmul の右単調性 + rmul_zero）。 -/
theorem logVol_rmul_nonneg {a b : RReal} (ha : rLe realZero a) (hb : rLe realZero b) :
    rLe realZero (rmul a b) := by
  have h := rmul_le_mul_right ha hb
  have hz : realEq (rmul realZero b) realZero :=
    realEq_trans (rmul_comm realZero b) (rmul_zero b)
  exact rLe_congr hz (realEq_refl (rmul a b)) h

/-- **M312F-5b: 有効係数の和の非負性** — 全係数 ≥0 かつ全重み ≥0 なら和 ≥0（rLe）。 -/
theorem logVolSum_nonneg (c : Nat → Int) (logq : Nat → RReal)
    (hc : ∀ k, 0 ≤ c k) (hq : ∀ k, rLe realZero (logq k)) :
    ∀ n, rLe realZero (logVolSum c logq n) := by
  intro n
  induction n with
  | zero => exact rLe_refl realZero
  | succ p ih =>
    show rLe realZero
      (realAdd (logVolSum c logq p) (rmul (intToReal (c p)) (logq p)))
    have ht : rLe realZero (rmul (intToReal (c p)) (logq p)) :=
      logVol_rmul_nonneg (intToReal_mono (hc p)) (hq p)
    have hpair : rLe (realAdd realZero realZero)
        (realAdd (logVolSum c logq p) (rmul (intToReal (c p)) (logq p))) :=
      rLe_add_pair ih ht
    exact rLe_congr (realAdd_zero realZero) (realEq_refl _) hpair

/-- **M312F-5c: 有効因子の非負性** — 有効因子（M307F `picDivEffectiveRaw`、n_v≥0）は
    非負重み（log q_v≥0）の下で Arakelov 次数 ≥0（本物の ℝ の順序 rLe）。M240F の
    有効順序単調性と概念整合する log-shell 体積の効果性。 -/
theorem logVolGlobal_effective_nonneg (logq : Nat → RReal)
    (hq : ∀ k, rLe realZero (logq k)) {x : RawDiv} (hx : picDivEffectiveRaw x) :
    rLe realZero (logVolGlobal logq x) :=
  logVolSum_nonneg x.coeff logq hx hq x.bound

/-! ## M312F-6: Frobenius 斉次性 -/

/-- **M312F-6: Arakelov 次数の Frobenius 斉次性** — deg_ℝ([n]D) ≈ n·deg_ℝ(D)。
    M307F `picDiv_frob_degree`（deg([n]D)=n·deg D into ℤ）の**実数値版**。
    Frobenius 作用 [n]（因子の n 倍）が本物の実数の乗法 rmul として次数を n 倍する。 -/
theorem logVolGlobal_frob (logq : Nat → RReal) (n : Nat) (x : RawDiv) :
    realEq (logVolGlobal logq (picDivFrobRaw n x))
      (rmul (intToReal (n : Int)) (logVolGlobal logq x)) :=
  logVolSum_smul (n : Int) x.coeff logq x.bound

/-! ## M312F-7: M307F 整数次数とのブリッジ（unit 重み） -/

/-- **M312F-7a: unit 重み** logq ≡ 1（全素点で重み 1）。 -/
def logVolUnit : Nat → RReal := fun _ => qToReal ratRing.one

/-- **M312F-7b: unit 重みの和は整数次数の ℝ 像** — logVolSum c 1 b ≈ intToReal(Σ c)。
    各項 c_k·1 ≈ c_k（rmul_one）＋加法性で M307F picDivSum の ℝ 像に一致（realEq）。 -/
theorem logVolSum_unweighted (c : Nat → Int) :
    ∀ b, realEq (logVolSum c logVolUnit b) (intToReal (picDivSum c b)) := by
  intro b
  induction b with
  | zero => exact realEq_refl _
  | succ p ih =>
    show realEq (realAdd (logVolSum c logVolUnit p)
          (rmul (intToReal (c p)) (qToReal ratRing.one)))
        (intToReal (picDivSum c p + c p))
    refine realEq_trans (realAdd_congr_right (logVolSum c logVolUnit p)
      (rmul_one (intToReal (c p)))) ?_
    refine realEq_trans (realAdd_congr_left (intToReal (c p)) ih) ?_
    exact intToReal_add (picDivSum c p) (c p)

/-- **M312F-7c: M307F 整数次数とのブリッジ（本物の接続）** — unit 重みでの Arakelov
    次数 deg_ℝ(D) は M307F の commit 済み整数次数 Hom `picDivDegree`（Div→ℤ）の ℝ 像に
    一致する: logVolGlobal 1 D ≈ intToReal(picDivDegree D)。柱C の「因子の次数＝
    log-volume の離散部分」を本物で言明する（picDivDegree.map(Quot.mk x) = picDivSum は
    Quot.lift の defeq）。 -/
theorem logVolGlobal_unweighted_degree (x : RawDiv) :
    realEq (logVolGlobal logVolUnit x)
      (intToReal (picDivDegree.map (Quot.mk rawEq x))) :=
  logVolSum_unweighted x.coeff x.bound

/-! ## M312F-8: capstone -/

/-- **M312F-8a: log-volume データ** — 実数値 log-volume（Arakelov 次数）の束ね。
    加法順序準同型・rawEq 不変・零・Frobenius 斉次を本物の ℝ で充足する。 -/
structure LogVolumeData (logq : Nat → RReal) where
  /-- 大域 log-volume（Arakelov 次数）deg_ℝ:RawDiv→ℝ。 -/
  vol : RawDiv → RReal
  /-- 加法準同型 deg_ℝ(D+D')≈deg_ℝ(D)+deg_ℝ(D')。 -/
  vol_add : ∀ x y, realEq (vol (rawAdd x y)) (realAdd (vol x) (vol y))
  /-- 零因子 deg_ℝ(0)≈0。 -/
  vol_zero : realEq (vol rawZero) realZero
  /-- rawEq 不変（Div の上に well-defined）。 -/
  vol_wd : ∀ {x y}, rawEq x y → realEq (vol x) (vol y)
  /-- Frobenius 斉次 deg_ℝ([n]D)≈n·deg_ℝ(D)。 -/
  vol_frob : ∀ (n : Nat) (x : RawDiv),
    realEq (vol (picDivFrobRaw n x)) (rmul (intToReal (n : Int)) (vol x))

/-- **M312F-8b: 実データ** — 全フィールドを本物で充足。 -/
def logVolumeData (logq : Nat → RReal) : LogVolumeData logq where
  vol := logVolGlobal logq
  vol_add := logVolGlobal_add logq
  vol_zero := logVolGlobal_zero logq
  vol_wd := logVolGlobal_wd logq
  vol_frob := logVolGlobal_frob logq

/-- **M312F-8c: 存在**（`Nonempty` でなく実データ）。 -/
theorem logVol_exists (logq : Nat → RReal) : Nonempty (LogVolumeData logq) :=
  ⟨logVolumeData logq⟩

/-- **M312F-8d: log-volume は加法準同型**（capstone 再掲）。 -/
theorem logVol_degree_isHom (logq : Nat → RReal) (x y : RawDiv) :
    realEq (logVolGlobal logq (rawAdd x y))
      (realAdd (logVolGlobal logq x) (logVolGlobal logq y)) :=
  logVolGlobal_add logq x y

/-- **M312F-8e: 有効因子は非負**（capstone 再掲）。 -/
theorem logVol_effective_nonneg (logq : Nat → RReal)
    (hq : ∀ k, rLe realZero (logq k)) {x : RawDiv} (hx : picDivEffectiveRaw x) :
    rLe realZero (logVolGlobal logq x) :=
  logVolGlobal_effective_nonneg logq hq hx

end IUT
