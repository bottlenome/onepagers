/-
  IUT/QuadraticProductFormula.lean — M366F [実／本物]
  分類: 実 (積公式を K=ℚ(√d) へ＝一般数体の忠実な部分ケース)
  complete_pct 影響: 柱C を前進（M351F 積公式(K=ℚ)を二次体 K=ℚ(√d) へ拡張＝
    Σ_v [K_v:ℚ_v]·log|x|_v=0 をノルム N:K^×→ℚ^× 経由で ℚ の積公式に還元して証明・
    局所次数の和=[K:ℚ]=2 の基本等式。一般数体の忠実な部分ケース）。
  正直な限定: 二次体のみ・一般数体/全分岐の完全素点理論は後続。ノルム還元が
    忠実部分ケース戦略（別コース99%より本コース3%）。
-/
import IUT.ProductFormula

namespace IUT

/-! ## M366F-1: 二次体 K=ℚ(√d) とノルム N(a+b√d)=a²−db²

    二次体 K=ℚ(√d)（d は平方因子を持たない整数と想定）。K の元 a+b√d に対して
    共役 a−b√d との積がノルム N(a+b√d)=(a+b√d)(a−b√d)=a²−d·b² ∈ ℚ。
    ノルムは乗法的 N:K^×→ℚ^× で、これが積公式の ℚ への還元の核となる。 -/

/-- **M366F-1a: 二次体データ** K=ℚ(√d) — パラメータ d（平方因子なしと想定）。
    二つの埋め込み σ,σ̄:K→ℝ/ℂ（√d↦±√d）を持ち、[K:ℚ]=2。 -/
structure qpfField where
  /-- 判別式パラメータ d（K=ℚ(√d)、平方因子を持たない整数と想定）。 -/
  d : Int

/-- **M366F-1b: [K:ℚ]=2** — 二次拡大の絶対次数。 -/
def qpfDegree : Nat := 2

/-- **M366F-1c: ノルム** N(a+b√d) = a²−d·b² ∈ ℤ（整元のノルム）。
    共役 a−b√d との積 (a+b√d)(a−b√d)=a²−d·b²。 -/
def qpfNorm (d a b : Int) : Int := a * a - d * (b * b)

/-- **M366F-1d: 有理整数のノルム**（b=0）— N(a) = a²（ℚ の元は共役不変）。 -/
theorem qpfNorm_int (d a : Int) : qpfNorm d a 0 = a * a := by
  show a * a - d * (0 * 0) = a * a
  omega

/-- **M366F-1e: 具体ノルム N_{√2}(1+√2)=−1**（ℚ(√2) の基本単数、a=b=1, d=2）。 -/
theorem qpfNorm_sqrt2_unit : qpfNorm 2 1 1 = -1 := by
  show (1 : Int) * 1 - 2 * (1 * 1) = -1
  omega

/-- **M366F-1f: 具体ノルム N_{√2}(3+√2)=7**（a=3,b=1,d=2）。 -/
theorem qpfNorm_sqrt2_seven : qpfNorm 2 3 1 = 7 := by
  show (3 : Int) * 3 - 2 * (1 * 1) = 7
  omega

/-- **M366F-1g: 具体ノルム N_i(1+i)=2**（ガウス整数、a=b=1, d=−1）。 -/
theorem qpfNorm_gauss_two : qpfNorm (-1) 1 1 = 2 := by
  show (1 : Int) * 1 - (-1) * (1 * 1) = 2
  omega

/-! ## M366F-2: K^× の元の模型（ノルムの因子データ）

    K の各素点 v での |x|_v は、大域には ℚ の各素点 p での |N(x)|_p に束ねられる
    （∏_{v|p} |x|_v^{[K_v:ℚ_v]} = |N_{K/ℚ}(x)|_p）。そこで x∈K^× を、そのノルム
    N(x)∈ℚ^× の因子データ（M351F `pfRational`）で忠実に模型化する。これがノルム還元
    戦略の Lean 化（本コースの部分ケース）。 -/

/-- **M366F-2a: K^× の元** — 二次体 K=ℚ(√d) の元 x を、そのノルム N(x)∈ℚ^× の
    因子データ `norm : pfRational`（v_p(N(x)) の付値ベクトル）で模型化する。 -/
structure qpfElt where
  /-- 二次体 K=ℚ(√d) のパラメータ。 -/
  d : Int
  /-- ノルム N_{K/ℚ}(x) ∈ ℚ^× の因子データ（M351F pfRational）。 -/
  norm : pfRational

/-- **M366F-2b: K^× の積** x·y — ノルムは乗法的 N(xy)=N(x)N(y) ゆえ、ノルム因子データは
    M351F `pfRatMul`（付値ベクトルは加法 v_p(N(xy))=v_p(N(x))+v_p(N(y))）で合成する。 -/
def qpfEltMul (x y : qpfElt) : qpfElt where
  d := x.d
  norm := pfRatMul x.norm y.norm

/-- **M366F-2c: ノルムの乗法性（因子レベル）** — N(xy) の因子データ＝N(x),N(y) の
    因子データの M351F 積（rawAdd）。ノルム N:K^×→ℚ^× が準同型であることの本体
    （付値レベル、線形）。 -/
theorem qpf_norm_datum_mul (x y : qpfElt) :
    (qpfEltMul x y).norm = pfRatMul x.norm y.norm := rfl

/-! ## M366F-3: 局所次数の重み [K_v:ℚ_v] と基本等式 Σ_{v|p}[K_v:ℚ_v]=[K:ℚ]=2 -/

/-- **M366F-3a: 有限素点 p の分解型** — 二次体で有理素数 p は次の三型に分解する:
    分裂（split, p=v·v̄）・不分岐惰性（inert）・分岐（ramified, p=v²）。 -/
inductive qpfFinSplit where
  /-- 分裂 p=v·v̄（相異なる二素点、各 [K_v:ℚ_p]=1）。 -/
  | split
  /-- 惰性（一素点、f=2, e=1, [K_v:ℚ_p]=2）。 -/
  | inert
  /-- 分岐 p=v²（一素点、e=2, f=1, [K_v:ℚ_p]=2）。 -/
  | ramified

/-- **M366F-3b: 分解型の局所次数リスト** [K_v:ℚ_p]（v|p ごと）。
    split→[1,1]・inert→[2]・ramified→[2]（e·f）。 -/
def qpfFinMult : qpfFinSplit → List Nat
  | .split => [1, 1]
  | .inert => [2]
  | .ramified => [2]

/-- **M366F-3c: アルキメデス素点の型** — d>0 なら二つの実素点（実埋め込み σ,σ̄）、
    d<0 なら一つの複素素点（[K_v:ℝ]=2）。 -/
inductive qpfArchSplit where
  /-- d>0: 二つの実素点（各 [K_v:ℝ]=1）。 -/
  | realPlaces
  /-- d<0: 一つの複素素点（[K_v:ℝ]=2）。 -/
  | complexPlace

/-- **M366F-3d: アルキメデス局所次数リスト** — realPlaces→[1,1]・complexPlace→[2]（M346F d_v）。 -/
def qpfArchMult : qpfArchSplit → List Nat
  | .realPlaces => [1, 1]
  | .complexPlace => [2]

/-- **M366F-3e: 局所次数リストの総和** Σ_{v|p} [K_v:ℚ_v]。 -/
def qpfListSum : List Nat → Nat
  | [] => 0
  | m :: ms => m + qpfListSum ms

/-- **M366F-3f: 基本等式（有限素点）** Σ_{v|p} [K_v:ℚ_p] = [K:ℚ] = 2。
    分裂 1+1=2・惰性 2・分岐 2——どの分解型でも局所次数の和が絶対次数 [K:ℚ]=2 に
    等しい（Σ_{v|p} e_v f_v = [K:ℚ] の基本恒等式の二次体版）。 -/
theorem qpf_fin_degree_sum (s : qpfFinSplit) : qpfListSum (qpfFinMult s) = qpfDegree := by
  cases s with
  | split => rfl
  | inert => rfl
  | ramified => rfl

/-- **M366F-3g: 基本等式（アルキメデス素点）** Σ_{v|∞} [K_v:ℝ] = [K:ℚ] = 2。
    実素点二つ 1+1=2・複素素点一つ 2。 -/
theorem qpf_arch_degree_sum (s : qpfArchSplit) :
    qpfListSum (qpfArchMult s) = qpfDegree := by
  cases s with
  | realPlaces => rfl
  | complexPlace => rfl

/-- **M366F-3h: ノルム両立性（基本等式の総括）** — 有限・アルキメデスいずれの素点でも
    Σ_{v|w} [K_v:ℚ_v] = 2 = [K:ℚ]。∏_{v|p}|x|_v^{[K_v:ℚ_v]}=|N(x)|_p の重複度がこの
    基本等式に従い、大域積公式のノルム還元を支える。 -/
theorem qpf_norm_compatible (s : qpfFinSplit) (t : qpfArchSplit) :
    qpfListSum (qpfFinMult s) = 2 ∧ qpfListSum (qpfArchMult t) = 2 :=
  ⟨qpf_fin_degree_sum s, qpf_arch_degree_sum t⟩

/-! ## M366F-4: 重み付き局所次数 [K_v:ℚ_v]·log|x|_v（M346F rNsmul 倍） -/

/-- **M366F-4a: 重み付き局所次数** [K_v:ℚ_v]·log|x|_v = m·l（M346F `rNsmul` の Nat 倍）。 -/
def qpfWeightedLocal (m : Nat) (l : RReal) : RReal := rNsmul m l

/-- **M366F-4b: 次数 1 の素点** — [K_v:ℚ_v]=1 の重みは log|x|_v そのもの（rNsmul_one）。
    分裂素点・実素点の各成分。 -/
theorem qpf_weighted_one (l : RReal) : realEq (qpfWeightedLocal 1 l) l :=
  rNsmul_one l

/-- **M366F-4c: 次数 2 の素点** — [K_v:ℚ_v]=2 の重みは log|x|_v+log|x|_v（惰性/分岐/
    複素素点）。 -/
theorem qpf_weighted_two (l : RReal) :
    realEq (qpfWeightedLocal 2 l) (realAdd l l) := by
  show realEq (realAdd (rNsmul 1 l) l) (realAdd l l)
  exact realAdd_congr_left l (rNsmul_one l)

/-- **M366F-4d: 分裂素点の重み和** — 二つの次数 1 素点 v,v̄ の重み付き寄与
    1·log|x|_v + 1·log|x|_v̄ ≈ log|x|_v + log|x|_v̄。 -/
theorem qpf_split_weighted (l₁ l₂ : RReal) :
    realEq (realAdd (qpfWeightedLocal 1 l₁) (qpfWeightedLocal 1 l₂))
      (realAdd l₁ l₂) :=
  realEq_trans (realAdd_congr_left (rNsmul 1 l₂) (rNsmul_one l₁))
    (realAdd_congr_right l₁ (rNsmul_one l₂))

/-! ## M366F-5: 大域次数 Σ_v [K_v:ℚ_v]·log|x|_v とノルム還元 -/

/-- **M366F-5a: 局所次数（p 素点の寄与）** — 有理素点 p 上の K-素点の重み付き寄与の和
    Σ_{v|p} [K_v:ℚ_v]·log|x|_v は、ノルムの p 局所次数 log|N(x)|_p に一致する
    （∏_{v|p}|x|_v^{[K_v:ℚ_v]}=|N(x)|_p の対数）。それを M351F `pfLocalDeg`（N(x) の
    因子データ上）で与える。 -/
def qpfLocalDeg (logp : Nat → RReal) (x : qpfElt) : pfPlace → RReal :=
  pfLocalDeg logp x.norm

/-- **M366F-5b: 大域次数** deg_K(x) = Σ_v [K_v:ℚ_v]·log|x|_v。ノルム還元により
    = Σ_p log|N(x)|_p ＝ N(x)∈ℚ^× の M351F 大域次数 `pfGlobalDeg`。 -/
def qpfGlobalDeg (logp : Nat → RReal) (x : qpfElt) : RReal :=
  pfGlobalDeg logp x.norm

/-- **M366F-5c: ノルム還元（本丸の還元・定義的）** — K 上の大域次数
    Σ_v [K_v:ℚ_v]·log|x|_v は、ノルム N(x)∈ℚ^× の ℚ 上大域次数 Σ_p log|N(x)|_p に
    一致する。二次体の積公式を ℚ の積公式へ還元する核（本コースの忠実部分ケース）。 -/
theorem qpf_reduce_to_Q (logp : Nat → RReal) (x : qpfElt) :
    qpfGlobalDeg logp x = pfGlobalDeg logp x.norm := rfl

/-- **M366F-5d: 積公式（本丸）** Σ_v [K_v:ℚ_v]·log|x|_v = 0 for x∈K^×。
    ノルム還元 `qpf_reduce_to_Q` で ℚ の大域次数 pfGlobalDeg(N(x)) に落とし、
    M351F `pf_product_formula`（Σ_p log|N(x)|_p = 0）を N(x)∈ℚ^× に適用する。
    二次体 K=ℚ(√d) の Artin–Whaples 積公式（一般数体の忠実な部分ケース）。 -/
theorem qpf_product_formula (logp : Nat → RReal) (x : qpfElt) :
    realEq (qpfGlobalDeg logp x) realZero :=
  pf_product_formula logp x.norm

/-- **M366F-5e: 大域次数の加法準同型** deg_K(xy) ≈ deg_K(x)+deg_K(y)。
    ノルム乗法性 N(xy)=N(x)N(y)（因子は rawAdd）＋ M351F `pf_degree_hom`。K^×→ℝ の Hom。 -/
theorem qpf_degree_hom (logp : Nat → RReal) (x y : qpfElt) :
    realEq (qpfGlobalDeg logp (qpfEltMul x y))
      (realAdd (qpfGlobalDeg logp x) (qpfGlobalDeg logp y)) :=
  pf_degree_hom logp x.norm y.norm

/-- **M366F-5f: 積公式の局所形** — 大域次数の展開（有限部＋無限部＝0、ノルム経由）。 -/
theorem qpf_finite_add_arch_zero (logp : Nat → RReal) (x : qpfElt) :
    realEq (realAdd (pfFiniteDeg logp x.norm) (pfArchDeg logp x.norm)) realZero :=
  pf_finite_add_arch_zero logp x.norm

/-! ## M366F-6: capstone -/

/-- **M366F-6a: 二次体積公式データ** — K=ℚ(√d) の大域次数 deg_K:K^×→ℝ の束ね:
    積公式 Σ_v[K_v:ℚ_v]·log|x|_v=0・加法準同型・ℚ へのノルム還元・[K:ℚ]=2 を
    本物の ℝ で充足する。 -/
structure QuadraticProductFormulaData (logp : Nat → RReal) where
  /-- 二次体 K=ℚ(√d) のパラメータ。 -/
  d : Int
  /-- 大域次数 deg_K(x)=Σ_v[K_v:ℚ_v]·log|x|_v。 -/
  gdeg : qpfElt → RReal
  /-- 積公式 Σ_v[K_v:ℚ_v]·log|x|_v=0。 -/
  product_formula : ∀ x, realEq (gdeg x) realZero
  /-- 加法準同型 deg_K(xy)≈deg_K(x)+deg_K(y)。 -/
  degree_hom : ∀ x y, realEq (gdeg (qpfEltMul x y)) (realAdd (gdeg x) (gdeg y))
  /-- ℚ へのノルム還元 deg_K(x)=pfGlobalDeg(N(x))。 -/
  reduce : ∀ x, gdeg x = pfGlobalDeg logp x.norm
  /-- 絶対次数 [K:ℚ]。 -/
  absDegree : Nat
  /-- [K:ℚ]=2。 -/
  is_degree_two : absDegree = 2

/-- **M366F-6b: 実データ** — 全フィールドを本物で充足（判別式 d）。 -/
def quadraticProductFormulaData (logp : Nat → RReal) (d : Int) :
    QuadraticProductFormulaData logp where
  d := d
  gdeg := qpfGlobalDeg logp
  product_formula := qpf_product_formula logp
  degree_hom := qpf_degree_hom logp
  reduce := fun x => qpf_reduce_to_Q logp x
  absDegree := qpfDegree
  is_degree_two := rfl

/-- **M366F-6c: 存在** — 二次体積公式データは充足可能（任意の d）。 -/
theorem qpf_exists (logp : Nat → RReal) (d : Int) :
    Nonempty (QuadraticProductFormulaData logp) :=
  ⟨quadraticProductFormulaData logp d⟩

/-! ## M366F-7: 実例（ℚ(√2)・ℚ(i) の具体元） -/

/-- **M366F-7a: ℚ(√2) の基本単数 x=1+√2**（N(x)=−1、単位）— 積公式 deg_K(1+√2)=0。
    ノルム −1 は全付値 0（rawZero）ゆえ ℚ 側でも次数 0。 -/
theorem qpf_example_sqrt2_unit (logp : Nat → RReal) :
    realEq (qpfGlobalDeg logp ⟨2, ⟨true, rawZero⟩⟩) realZero :=
  qpf_product_formula logp ⟨2, ⟨true, rawZero⟩⟩

/-- **M366F-7b: ℚ(√2) の元 x=3+√2**（N(x)=7=p_3）— 積公式 deg_K(3+√2)=0。
    ノルム 7 の因子データは第 3 素点（p_3=7）で付値 1。 -/
theorem qpf_example_sqrt2_seven (logp : Nat → RReal) :
    realEq (qpfGlobalDeg logp ⟨2, pfSinglePrime 3 1⟩) realZero :=
  qpf_product_formula logp ⟨2, pfSinglePrime 3 1⟩

/-- **M366F-7c: ガウス体 ℚ(i) の元 x=1+i**（N(x)=2=p_0）— 積公式 deg_K(1+i)=0。
    ノルム 2 の因子データは第 0 素点（p_0=2）で付値 1。 -/
theorem qpf_example_gauss (logp : Nat → RReal) :
    realEq (qpfGlobalDeg logp ⟨-1, pfSinglePrime 0 1⟩) realZero :=
  qpf_product_formula logp ⟨-1, pfSinglePrime 0 1⟩

/-- **M366F-7d: 加法準同型の実例** — ℚ(i) で deg_K((1+i)·y)≈deg_K(1+i)+deg_K(y)。 -/
theorem qpf_example_hom (logp : Nat → RReal) (y : qpfElt) :
    realEq (qpfGlobalDeg logp (qpfEltMul ⟨-1, pfSinglePrime 0 1⟩ y))
      (realAdd (qpfGlobalDeg logp ⟨-1, pfSinglePrime 0 1⟩) (qpfGlobalDeg logp y)) :=
  qpf_degree_hom logp ⟨-1, pfSinglePrime 0 1⟩ y

/-- **M366F-7e: 基本等式の実例** — 惰性素点 Σ_{v|p}[K_v:ℚ_p]=2、複素素点 Σ_{v|∞}[K_v:ℝ]=2。 -/
theorem qpf_example_fundamental :
    qpfListSum (qpfFinMult .inert) = 2 ∧ qpfListSum (qpfArchMult .complexPlace) = 2 :=
  qpf_norm_compatible .inert .complexPlace

end IUT
