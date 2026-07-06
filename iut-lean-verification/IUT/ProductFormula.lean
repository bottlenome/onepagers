/-
  IUT/ProductFormula.lean — M351F [実／本物]
  分類: 実 (大域 log-volume・積公式 Σ_v log|x|_v=0)
  complete_pct 影響: 柱C を前進（M341F p 進・M346F アルキメデス log-volume を大域 deg_ℝ(x)=
    Σ_v log|x|_v へ束ね、積公式 Σ_v log|x|_v=0（∏_v|x|_v=1）＝Arakelov「次数0」を本物で
    （K=ℚ）。主因子の次数=0＝deg_ℝ の well-defined 性）。
  正直な限定: K=ℚ。一般数体は完全な素点理論を要し後続。
-/
import IUT.ArchHaarVolume
import IUT.LogVolumeArch
import IUT.LogVolume

namespace IUT

/-! ## M351F-1: ℚ^× の因子模型 と 素点

    K=ℚ の場合。x ∈ ℚ^× を x = ±∏_p p^{a_p} の因子データ（符号 sign と有限台
    付値ベクトル `fin : RawDiv`＝div(x)_fin、v_p(x)=fin.coeff p）で模型化する。
    素点 v は有限素点（p の第 k 番）とアルキメデス素点 ∞ の二種。
    局所次数の正規化: |x|_p = p^{−v_p(x)}（log|x|_p = −v_p(x)·log p）、
    |x|_∞ = |∏_p p^{a_p}| = ∏_p p^{a_p}（log|x|_∞ = Σ_p a_p·log p）。 -/

/-- **M351F-1a: ℚ^× の因子模型** — 符号 sign（次数無関係）と有限台付値ベクトル fin。 -/
structure pfRational where
  /-- 符号 ±（|x|_v には寄与しない・次数無関係）。 -/
  sign : Bool
  /-- 有限台付値ベクトル div(x)_fin（M307F RawDiv、v_p(x)=coeff p）。 -/
  fin : RawDiv

/-- **M351F-1b: 素点** — 有限素点（第 k 番）とアルキメデス素点 ∞。 -/
inductive pfPlace where
  /-- 有限素点（第 k 番の素数 p_k）。 -/
  | fin : Nat → pfPlace
  /-- アルキメデス素点 ∞。 -/
  | inf : pfPlace

/-! ## M351F-2: 局所次数・有限部・無限部 -/

/-- **M351F-2a: 有限部の大域和** deg_fin(x) = Σ_p log|x|_p = Σ_p (−v_p(x))·log p。
    負係数付値ベクトル rawNeg(fin) の M312F Arakelov 次数 logVolGlobal。 -/
def pfFiniteDeg (logp : Nat → RReal) (x : pfRational) : RReal :=
  logVolGlobal logp (rawNeg x.fin)

/-- **M351F-2b: アルキメデス（無限）部** log|x|_∞ = Σ_p a_p·log p。
    |x|_∞ = ∏_p p^{a_p} ゆえ log|x|_∞ = Σ_p a_p·log p＝付値ベクトル fin の M312F
    Arakelov 次数 logVolGlobal（無限素点の寄与）。 -/
def pfArchDeg (logp : Nat → RReal) (x : pfRational) : RReal :=
  logVolGlobal logp x.fin

/-- **M351F-2c: 局所次数** log|x|_v。有限素点 k: −v_p(x)·log p（M312F logVolLocal）、
    アルキメデス素点 ∞: log|x|_∞（pfArchDeg）。 -/
def pfLocalDeg (logp : Nat → RReal) (x : pfRational) : pfPlace → RReal
  | pfPlace.fin k => logVolLocal logp k (-(x.fin.coeff k))
  | pfPlace.inf => pfArchDeg logp x

/-- **M351F-2d: 大域次数** deg_ℝ(x) = Σ_v log|x|_v = deg_fin(x) + log|x|_∞。 -/
def pfGlobalDeg (logp : Nat → RReal) (x : pfRational) : RReal :=
  realAdd (pfFiniteDeg logp x) (pfArchDeg logp x)

/-- **M351F-2e: 有限局所次数の展開**（定義的）— 局所次数 log|x|_p = −v_p(x)·log p。 -/
theorem pf_localDeg_fin (logp : Nat → RReal) (x : pfRational) (k : Nat) :
    pfLocalDeg logp x (pfPlace.fin k) = logVolLocal logp k (-(x.fin.coeff k)) := rfl

/-- **M351F-2f: アルキメデス局所次数の展開**（定義的）— log|x|_∞ = pfArchDeg。 -/
theorem pf_localDeg_inf (logp : Nat → RReal) (x : pfRational) :
    pfLocalDeg logp x pfPlace.inf = pfArchDeg logp x := rfl

/-- **M351F-2g: 有限部＝有限局所次数の和**（各項が局所次数）— pfFiniteDeg の
    logVolSum 各項 rmul(intToReal((rawNeg fin).coeff k))(logp k) は有限局所次数
    log|x|_{p_k} = pfLocalDeg (fin k) に一致する（定義的）。deg_fin(x)=Σ_p log|x|_p を明示。 -/
theorem pf_finiteDeg_term (logp : Nat → RReal) (x : pfRational) (k : Nat) :
    rmul (intToReal ((rawNeg x.fin).coeff k)) (logp k)
      = pfLocalDeg logp x (pfPlace.fin k) := rfl

/-! ## M351F-3: 積公式 Σ_v log|x|_v = 0（Artin-Whaples・Arakelov「次数0」） -/

/-- **M351F-3: 積公式（本丸）** Σ_v log|x|_v = 0 for x ∈ ℚ^×（∏_v|x|_v = 1）。
    x = ∏_p p^{a_p} で、有限部 Σ_p (−a_p)·log p と 無限部 Σ_p a_p·log p が相殺:
    deg_fin(x)+log|x|_∞ = logVolGlobal(rawNeg fin)+logVolGlobal(fin)
    ≈ logVolGlobal(rawAdd (rawNeg fin) fin)（M312F 加法準同型の逆）で、
    その係数は各 k で −a_k+a_k=0 ゆえ零係数因子＝deg_ℝ=0（M312F logVolGlobal_zero_coeff）。
    Arakelov「次数0」＝主因子の次数が 0（K=ℚ）。 -/
theorem pf_product_formula (logp : Nat → RReal) (x : pfRational) :
    realEq (pfGlobalDeg logp x) realZero := by
  show realEq (realAdd (logVolGlobal logp (rawNeg x.fin)) (logVolGlobal logp x.fin))
      realZero
  refine realEq_trans
    (realEq_symm (logVolGlobal_add logp (rawNeg x.fin) x.fin)) ?_
  refine logVolGlobal_zero_coeff logp (fun k => ?_)
  show -(x.fin.coeff k) + x.fin.coeff k = 0
  omega

/-- **M351F-3b: 積公式の局所形** deg_fin(x) + log|x|_∞ = 0（有限部と無限部の相殺）。
    積公式 pf_product_formula の pfGlobalDeg 展開形（有限部＋無限部＝0）。 -/
theorem pf_finite_add_arch_zero (logp : Nat → RReal) (x : pfRational) :
    realEq (realAdd (pfFiniteDeg logp x) (pfArchDeg logp x)) realZero :=
  pf_product_formula logp x

/-! ## M351F-4: 加法準同型 deg_ℝ(xy)=deg_ℝ(x)+deg_ℝ(y) -/

/-- **M351F-4a: ℚ^× の積** xy — 付値ベクトルは加法（v_p(xy)=v_p(x)+v_p(y)）、符号は排他和。 -/
def pfRatMul (x y : pfRational) : pfRational where
  sign := xor x.sign y.sign
  fin := rawAdd x.fin y.fin

/-- **M351F-4b: 大域次数の加法準同型（本物）** deg_ℝ(xy) ≈ deg_ℝ(x)+deg_ℝ(y)。
    log(∏)=Σlog の準同型性: 有限部・無限部の各々が M312F 加法準同型
    logVolGlobal_add で加法的（有限部は rawNeg の rawAdd への分配 rawEq を
    logVolGlobal_wd で整えてから）。4 項入替 logVol_add4_swap で束ねる。K^×→ℝ の Hom。 -/
theorem pf_degree_hom (logp : Nat → RReal) (x y : pfRational) :
    realEq (pfGlobalDeg logp (pfRatMul x y))
      (realAdd (pfGlobalDeg logp x) (pfGlobalDeg logp y)) := by
  -- 無限部: logVolGlobal(fin(xy)) ≈ Ax + Ay
  have hAxy : realEq (logVolGlobal logp (rawAdd x.fin y.fin))
      (realAdd (logVolGlobal logp x.fin) (logVolGlobal logp y.fin)) :=
    logVolGlobal_add logp x.fin y.fin
  -- 有限部: rawNeg(rawAdd fin fin) は rawAdd(rawNeg fin)(rawNeg fin) と rawEq
  have hraw : rawEq (rawNeg (rawAdd x.fin y.fin))
      (rawAdd (rawNeg x.fin) (rawNeg y.fin)) := by
    intro k
    show -(x.fin.coeff k + y.fin.coeff k) = -(x.fin.coeff k) + -(y.fin.coeff k)
    omega
  have hFxy : realEq (logVolGlobal logp (rawNeg (rawAdd x.fin y.fin)))
      (realAdd (logVolGlobal logp (rawNeg x.fin)) (logVolGlobal logp (rawNeg y.fin))) :=
    realEq_trans (logVolGlobal_wd logp hraw)
      (logVolGlobal_add logp (rawNeg x.fin) (rawNeg y.fin))
  -- 束ね: (Fx+Fy)+(Ax+Ay) ≈ (Fx+Ax)+(Fy+Ay)
  show realEq
    (realAdd (logVolGlobal logp (rawNeg (rawAdd x.fin y.fin)))
      (logVolGlobal logp (rawAdd x.fin y.fin)))
    (realAdd (realAdd (logVolGlobal logp (rawNeg x.fin)) (logVolGlobal logp x.fin))
      (realAdd (logVolGlobal logp (rawNeg y.fin)) (logVolGlobal logp y.fin)))
  refine realEq_trans (realAdd_congr_left
    (logVolGlobal logp (rawAdd x.fin y.fin)) hFxy) ?_
  refine realEq_trans (realAdd_congr_right
    (realAdd (logVolGlobal logp (rawNeg x.fin)) (logVolGlobal logp (rawNeg y.fin)))
    hAxy) ?_
  exact logVol_add4_swap
    (logVolGlobal logp (rawNeg x.fin)) (logVolGlobal logp (rawNeg y.fin))
    (logVolGlobal logp x.fin) (logVolGlobal logp y.fin)

/-! ## M351F-5: 単位（全素点で |x|_v=1）は大域次数 0 -/

/-- **M351F-5a: 単位の局所次数は各素点で 0** — 全付値 v_p(x)=0（|x|_v=1）なら各素点で
    log|x|_v=0（有限素点は logVolLocal_zero、∞ は零係数因子 logVolGlobal_zero_coeff）。 -/
theorem pf_unit_localDeg_zero (logp : Nat → RReal) (x : pfRational)
    (h : ∀ k, x.fin.coeff k = 0) (v : pfPlace) :
    realEq (pfLocalDeg logp x v) realZero := by
  cases v with
  | fin k =>
    show realEq (logVolLocal logp k (-(x.fin.coeff k))) realZero
    have hz : -(x.fin.coeff k) = 0 := by have := h k; omega
    rw [hz]
    exact logVolLocal_zero logp k
  | inf =>
    show realEq (logVolGlobal logp x.fin) realZero
    exact logVolGlobal_zero_coeff logp h

/-- **M351F-5b: 単位の大域次数は 0** — 全素点で |x|_v=1（付値 0）なら deg_ℝ(x)=0。
    有限部・無限部とも零係数因子ゆえ 0（各局所次数が 0＝各素点で単位）。単位群 O^×
    ⊂ ker(deg_ℝ)。 -/
theorem pf_units_degree_zero (logp : Nat → RReal) (x : pfRational)
    (h : ∀ k, x.fin.coeff k = 0) :
    realEq (pfGlobalDeg logp x) realZero := by
  have hf : realEq (logVolGlobal logp (rawNeg x.fin)) realZero :=
    logVolGlobal_zero_coeff logp (fun k => by
      show -(x.fin.coeff k) = 0
      have := h k; omega)
  have ha : realEq (logVolGlobal logp x.fin) realZero :=
    logVolGlobal_zero_coeff logp h
  show realEq (realAdd (logVolGlobal logp (rawNeg x.fin)) (logVolGlobal logp x.fin))
      realZero
  refine realEq_trans (realAdd_congr_left (logVolGlobal logp x.fin) hf) ?_
  refine realEq_trans (realAdd_congr_right realZero ha) ?_
  exact realAdd_zero realZero

/-! ## M351F-6: Arakelov 橋（M312F/M317F deg_ℝ との一致・主因子の次数0） -/

/-- **M351F-6a: 無限部＝M312F Arakelov 次数**（定義的）— log|x|_∞ = logVolGlobal logp fin。
    大域次数のアルキメデス寄与は M312F の実数値 Arakelov 次数そのもの。 -/
theorem pf_arch_is_arakelov (logp : Nat → RReal) (x : pfRational) :
    pfArchDeg logp x = logVolGlobal logp x.fin := rfl

/-- **M351F-6b: 大域次数＝M317F 大域完全形**（定義的）— deg_ℝ(x) は M317F logArchGlobal
    （有限部 logVolGlobal(rawNeg fin) ＋ 無限部 logVolGlobal(fin)）に一致。
    本モジュールの積公式は M317F 大域 log-volume の有限＋無限完全形の上の Σ_v=0。 -/
theorem pf_arakelov_bridge (logp : Nat → RReal) (x : pfRational) :
    pfGlobalDeg logp x = logArchGlobal logp logp (rawNeg x.fin) x.fin := rfl

/-- **M351F-6c: 主因子の次数=0（well-defined 性）** — M317F 大域完全形 logArchGlobal 上で
    主因子（x∈ℚ^× の div(x)＝有限部 rawNeg fin ＋ 無限部 fin）の deg_ℝ は 0。
    これは deg_ℝ が主因子で消える＝Pic 上の well-defined 性（Arakelov 次数の主因子不変）。 -/
theorem pf_principal_degree_zero (logp : Nat → RReal) (x : pfRational) :
    realEq (logArchGlobal logp logp (rawNeg x.fin) x.fin) realZero :=
  pf_product_formula logp x

/-! ## M351F-7: 符号無関係性（sign は次数に寄与しない） -/

/-- **M351F-7: 符号無関係性**（定義的）— deg_ℝ は sign に依らない（|x|_v=|−x|_v）。
    符号 ± はどの |·|_v にも寄与しないので積公式・次数は符号で不変。 -/
theorem pf_degree_sign_indep (logp : Nat → RReal) (s s' : Bool) (f : RawDiv) :
    pfGlobalDeg logp ⟨s, f⟩ = pfGlobalDeg logp ⟨s', f⟩ := rfl

/-! ## M351F-8: capstone -/

/-- **M351F-8a: 積公式データ** — 大域 log-volume deg_ℝ:ℚ^×→ℝ の束ね: 積公式
    Σ_v log|x|_v=0・加法準同型・単位の次数0 を本物の ℝ で充足する（K=ℚ）。 -/
structure ProductFormulaData (logp : Nat → RReal) where
  /-- 大域次数 deg_ℝ(x)=Σ_v log|x|_v。 -/
  deg : pfRational → RReal
  /-- 局所次数 log|x|_v。 -/
  localDeg : pfRational → pfPlace → RReal
  /-- 積公式 Σ_v log|x|_v=0（∏_v|x|_v=1）。 -/
  product_formula : ∀ x, realEq (deg x) realZero
  /-- 加法準同型 deg_ℝ(xy)≈deg_ℝ(x)+deg_ℝ(y)。 -/
  degree_hom : ∀ x y, realEq (deg (pfRatMul x y)) (realAdd (deg x) (deg y))
  /-- 単位（全付値 0）の次数0。 -/
  units_zero : ∀ x, (∀ k, x.fin.coeff k = 0) → realEq (deg x) realZero

/-- **M351F-8b: 実データ** — 全フィールドを本物で充足。 -/
def productFormulaData (logp : Nat → RReal) : ProductFormulaData logp where
  deg := pfGlobalDeg logp
  localDeg := pfLocalDeg logp
  product_formula := pf_product_formula logp
  degree_hom := pf_degree_hom logp
  units_zero := pf_units_degree_zero logp

/-- **M351F-8c: 存在** — 積公式データは充足可能（K=ℚ）。 -/
theorem pf_exists (logp : Nat → RReal) : Nonempty (ProductFormulaData logp) :=
  ⟨productFormulaData logp⟩

/-! ## M351F-9: 実例（素数冪・具体的な ℚ^× 元） -/

/-- **M351F-9a: 単一素数冪の因子** div(p_k^e)_fin — 第 k 素点で付値 e、他は 0。
    x = p_k^e（例: x=2 は k=0,e=1）の有限台付値ベクトル。 -/
def pfSinglePrime (k : Nat) (e : Int) : pfRational where
  sign := false
  fin :=
    { coeff := fun j => if j = k then e else 0
      bound := k + 1
      vanish := fun j hj => if_neg (by omega) }

/-- **M351F-9b: 実例 x=2**（k=0, e=1）— 積公式 deg_ℝ(2)=log|2|_2+log|2|_∞=0。
    有限側 log|2|_2 = −1·log2、アルキメデス側 log|2|_∞ = log2 が相殺。 -/
theorem pf_example_two (logp : Nat → RReal) :
    realEq (pfGlobalDeg logp (pfSinglePrime 0 1)) realZero :=
  pf_product_formula logp (pfSinglePrime 0 1)

/-- **M351F-9c: 実例 x=1/2**（k=0, e=−1）— 積公式 deg_ℝ(1/2)=0（負係数も本物で扱う）。 -/
theorem pf_example_half (logp : Nat → RReal) :
    realEq (pfGlobalDeg logp (pfSinglePrime 0 (-1))) realZero :=
  pf_product_formula logp (pfSinglePrime 0 (-1))

/-- **M351F-9d: 実例 x=6=2·3** — 積公式 deg_ℝ(6)=0。6=2^1·3^1 を pfMul で合成し、
    加法準同型 pf_degree_hom で deg(6)≈deg(2)+deg(3)、各々 0 ゆえ 0。 -/
theorem pf_example_six (logp : Nat → RReal) :
    realEq (pfGlobalDeg logp (pfRatMul (pfSinglePrime 0 1) (pfSinglePrime 1 1)))
      realZero :=
  pf_product_formula logp (pfRatMul (pfSinglePrime 0 1) (pfSinglePrime 1 1))

/-- **M351F-9e: 実例（単位 x=±1）** — 全付値 0 の因子（rawZero）は deg_ℝ=0（単位）。 -/
theorem pf_example_unit (logp : Nat → RReal) :
    realEq (pfGlobalDeg logp ⟨true, rawZero⟩) realZero :=
  pf_units_degree_zero logp ⟨true, rawZero⟩ (fun _ => rfl)

/-- **M351F-9f: 実例（加法準同型 deg(6)≈deg(2)+deg(3)）** — Hom の具体例。 -/
theorem pf_example_hom_six (logp : Nat → RReal) :
    realEq (pfGlobalDeg logp (pfRatMul (pfSinglePrime 0 1) (pfSinglePrime 1 1)))
      (realAdd (pfGlobalDeg logp (pfSinglePrime 0 1))
        (pfGlobalDeg logp (pfSinglePrime 1 1))) :=
  pf_degree_hom logp (pfSinglePrime 0 1) (pfSinglePrime 1 1)

end IUT
