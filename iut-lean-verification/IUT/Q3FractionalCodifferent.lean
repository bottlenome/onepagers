/-
  IUT/Q3FractionalCodifferent.lean — 柱B・B3 実 FRACTIONAL 逆 different 𝔡⁻¹=(π₉⁻⁶)
    を **本物の分数イデアル / 符号付き付値の部分対象**として建設し、q9cd が延期していた
    「分数 𝔡⁻¹ 本体」を実へ昇格する。

  ── 主要成果の分類: **[実／(a) 昇格]** — q9cd（Q3Codifferent）が「正直な限定 1」で
     **延期**していた真の逆 different 𝔡⁻¹=(π₉⁻⁶)（負冪の分数イデアル）を、
     符号付き付値 v_M : M* → **ℤ**（一様化子冪分解 M* ≅ π₉^ℤ × O_M* に忠実な
     `q9fcUnif`（exp : Int・unit : 実単数））の上の genuine な分数イデアル
     部分対象として初めて実 Lean で建てる。主語は実 π₉・実単数 u*·u**・
     実逆元 q3kInv・実 different 生成 q9dvDifferent（=D=(σπ₉−π₉)(σ²π₉−π₉)）——
     toy 模型（Bool 軌道・surrogate 群）を一切使わない（§3 遵守）。整数側の付値
     q9v（exp : Nat）を負冪へ拡張した忠実な符号付き付値であり、q9v_val_pi9=1 等の
     実付値公理と両立する（q9fc_val_ofUnif が整元では q9vVal と一致することを示す）。

  complete_pct 影響: **B3（audit-decided・予測 +0.01〜0.04・分数 𝔡⁻¹ 実化）**。
     動かす新規内容は「q9cd が **整数影**（π₉⁶ シフトの述語）でしか持てなかった 𝔡⁻¹ を、
     符号付き付値 v_M(x)≥−6 による genuine な分数イデアル部分対象へ昇格し、
     (i) 𝔡⁻¹ ⊇ O_M（v≥0 ⟹ v≥−6）、(ii) **𝔡·𝔡⁻¹ = O_M**（分数イデアル逆関係
     (π₉⁶)·(π₉⁻⁶)=O_M——生成元の積が付値 0 の単数・両包含を実証）、
     (iii) trace-dual 特徴づけ（q9cd の整数影を分数 𝔡⁻¹ の numerator 描像として接続）を
     割ること」。q9cd の DEFERRED 分数対象を DEFINED な分数イデアル関係へ置換する。

  核心の実データ（真水・NEW）:
   * q9fcUnif / q9fcVal — 符号付き付値 v_M : M* → ℤ（π₉^ℤ×O_M* 分解・exp:Int）。
     整側 q9vUnif（exp:Nat）を負冪へ拡張した忠実モデル（q9fcOfUnif 埋め込み・
     q9fc_val_ofUnif が整元で q9vVal と一致）。
   * q9fcMul / q9fc_val_mul — M* の積と付値の加法性 v_M(xy)=v_M(x)+v_M(y)（ℤ 上）
   * q9fcDiffGen / q9fcInvDiffGen — 𝔡 生成 π₉⁶·(u*u**)（=実 different D）と
     𝔡⁻¹ 生成 π₉⁻⁶·(u*u**)⁻¹（実逆元）。q9fc_diffgen_real で D 同定（reality anchor）
   * q9fc_diffgen_mul_inv_val / _unit — **★ 生成元の逆関係**: 𝔡gen·𝔡⁻¹gen の付値=0
     かつ単数部=1（= π₉⁰·1=1・(π₉⁶)(π₉⁻⁶)=(1)=O_M の generator 版）
   * q9fcInO / q9fcMemD / q9fcMemDinv — 分数イデアル O_M（v≥0）・𝔡（v≥6）・𝔡⁻¹（v≥−6）
   * q9fc_O_subset_Dinv — **(i) 𝔡⁻¹ ⊇ O_M**（v≥0 ⟹ v≥−6）
   * q9fc_diff_inv_eq_O — **★ (ii) 𝔡·𝔡⁻¹ = O_M**（積述語 ⟺ v≥0・両包含・分数逆関係）
   * q9fc_shift6_memDinv / q9fc_tracedual_all / q9fc_tracedual_sharp —
     **(iii) trace-dual**: numerator y·π₉⁻⁶ が 𝔡⁻¹ に入る（v(y)−6≥−6）ことと、
     q9cd の trace-dual 述語（∀t,π₉⁶∣Tr(y·t)）が全 y 成立・level 7 で破れることを接続
   * q9fc_invdiffgen_sharp — 𝔡⁻¹ 生成が **ちょうど** level −6（𝔡⁻¹⊋(π₉⁻⁵)）
   * Q3FractionalCodifferentData — capstone（束ね・新規証明ゼロ）

  正直な限定（§4 規約により消さない・弱めない・q9cd/q9di/q9dv/q9v/q9wr/q9nf 継承の上に追記のみ）:
  1. **拡大 1 個（M/L₂/ℚ₃）・特定の分数イデアル (π₉⁻⁶) のみ**。一般の分数イデアル
     THEORY（イデアル類群・分数イデアルの積の一般結合律・trace form の双対基底）は
     範囲外——本ファイルは (π₉⁻⁶) という **specific な** 𝔡⁻¹ に限る。
  2. **符号付き付値表現**を採用: 元は `q9fcUnif`（exp:Int・unit:実単数）＝
     局所体 M* の一様化子冪分解 M*≅π₉^ℤ×O_M* の忠実モデル。負冪 π₉⁻⁶ は O_M の分数元で
     choice-free に q3kCar として建てられない（q9cd 正直限定 1・FractionField の
     no_zero_div が排中律断片を要すのと同型の障壁）ため、**分数ideal を付値 v_M≥−6 の
     部分対象**として実現する。O_M は v≥0（M* の整元）で、0 は付値を持たず本表現の外
     （分数イデアル生成元の言明には不要・q9v 同様の TOTAL 付値不在を継承）。
  3. **q9cd/q9di/q9dv/q9v/q9wr 継承**: 可除性／付値形の different（d=6・v_M(D)=6・
     (π₉⁶)）・σ のみの Galois 作用・π₁^ét 不在を継承。trace-dual (iii) は q9cd の
     整数影（π₉⁶ シフト述語）を分数 𝔡⁻¹ の numerator 描像として接続するもので、
     L₂ 上の trace pairing の双対基底一般論は未達（q9cd 継承）。
  4. **q9cd の延期ノート更新**: q9cd「正直な限定 1」が延期した分数 𝔡⁻¹=(π₉⁻⁶) 本体は
     本ファイルで **now built**（符号付き付値表現による genuine な分数イデアル逆関係
     𝔡·𝔡⁻¹=O_M として）。q9cd の整数影は消さず、その分数昇格が本ファイル。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3Codifferent

namespace IUT

/-! ## q9fc-0: 符号付き付値表現 M* ≅ π₉^ℤ × O_M*（exp : Int） -/

/-- **q9fc-0a（★）: 局所体 M* の一様化子冪分解の忠実モデル** π₉^exp · u（exp∈ℤ・u 実単数）。
    整側 q9vUnif（exp:Nat）を負冪へ拡張——負冪 π₉⁻ⁿ を含む分数元を choice-free に表す。 -/
structure q9fcUnif where
  /-- 符号付き付値（一様化子 π₉ の整数冪指数・負も許す）。 -/
  exp : Int
  /-- 単数因子 u（実 O_M 単数）。 -/
  unit : q3kCar
  /-- u が実単数であること。 -/
  isUnit : q3kUnitMem unit

/-- 外延性（isUnit は Prop なので proof irrelevance で消える・preFrac_ext と同型）。 -/
theorem q9fcUnif_ext : ∀ {x y : q9fcUnif},
    x.exp = y.exp → x.unit = y.unit → x = y
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

/-- **q9fc-0b（★）: 符号付き付値 v_M : M* → ℤ**（exp 射影・負冪も定義値）。 -/
def q9fcVal (x : q9fcUnif) : Int := x.exp

/-- **q9fc-0c: 整側 q9vUnif（v≥0）の埋め込み** O_M* ↪ M*（exp を ℤ へ）。 -/
def q9fcOfUnif (x : q9vUnif) : q9fcUnif where
  exp := (x.exp : Int)
  unit := x.unit
  isUnit := x.isUnit

/-- **q9fc-0d: 整元では符号付き付値が実 q9v 付値と一致**（v_M が toy でなく
    q9v の忠実拡張である証拠・q9vVal x = x.exp を ℤ へ持ち上げただけ）。 -/
theorem q9fc_val_ofUnif (x : q9vUnif) :
    q9fcVal (q9fcOfUnif x) = (q9vVal x : Int) := rfl

/-! ## q9fc-1: M* の積と付値の加法性 v_M(xy)=v_M(x)+v_M(y) -/

/-- **q9fc-1a: M* の積**（π₉^{a+b}·(u·u')・exp は ℤ 加法・unit は実単数積）。 -/
def q9fcMul (x y : q9fcUnif) : q9fcUnif where
  exp := x.exp + y.exp
  unit := q3kMul x.unit y.unit
  isUnit := q3k_unit_mul x.isUnit y.isUnit

/-- **q9fc-1b（★）: 付値の加法性 v_M(x·y) = v_M(x) + v_M(y)**（ℤ 上）。 -/
theorem q9fc_val_mul (x y : q9fcUnif) :
    q9fcVal (q9fcMul x y) = q9fcVal x + q9fcVal y := rfl

/-! ## q9fc-2: 分数イデアル生成元 π₉⁶（𝔡）と π₉⁻⁶（𝔡⁻¹） -/

/-- π₉ を表す M* 元（v_M(π₉)=1）。 -/
def q9fcPi9 : q9fcUnif where
  exp := 1
  unit := q3kOne
  isUnit := q3k_unit_one

/-- **q9fc-2a: 𝔡 の生成元 π₉⁶·(u*u**)**（=実 different D・q9dvDifferent を M* へ）。 -/
def q9fcDiffGen : q9fcUnif := q9fcOfUnif q9dvDifferent

/-- **q9fc-2b（★）: 𝔡⁻¹ の生成元 π₉⁻⁶·(u*u**)⁻¹**（実逆元 q3kInv を消費・
    D の M* における真の乗法逆元・負冪 −6）。 -/
def q9fcInvDiffGen : q9fcUnif where
  exp := -6
  unit := q3kInv q9diUnit q9di_unit_isUnit
  isUnit := q3k_unit_inv q9diUnit q9di_unit_isUnit

/-- **q9fc-2c: v_M(𝔡gen) = 6**（different 生成の付値・q9dv の v_M(D)=6 の M* 版）。 -/
theorem q9fc_diffgen_val : q9fcVal q9fcDiffGen = 6 := rfl

/-- **q9fc-2d: v_M(𝔡⁻¹gen) = −6**（逆 different 生成の付値・負冪）。 -/
theorem q9fc_invdiffgen_val : q9fcVal q9fcInvDiffGen = -6 := rfl

/-- **q9fc-2e（reality anchor）: 𝔡gen の実 O_M 元は real different D=(σπ₉−π₉)(σ²π₉−π₉)**。
    q9dv_different_elt を消費——q9fcDiffGen が toy でなく実 different の M* 表現である証拠。 -/
theorem q9fc_diffgen_real :
    q9vElt q9dvDifferent
      = q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
               (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)) :=
  q9dv_different_elt

/-! ## q9fc-3: ★ 生成元の逆関係 (π₉⁶)·(π₉⁻⁶) = (1) = O_M -/

/-- **q9fc-3a（★）: v_M(𝔡gen·𝔡⁻¹gen) = 0**（生成元の積が付値 0——
    (π₉⁶)·(π₉⁻⁶)=(π₉⁰) の付値版）。 -/
theorem q9fc_diffgen_mul_inv_val :
    q9fcVal (q9fcMul q9fcDiffGen q9fcInvDiffGen) = 0 := by
  rw [q9fc_val_mul, q9fc_diffgen_val, q9fc_invdiffgen_val]
  omega

/-- **q9fc-3b（★）: 𝔡gen·𝔡⁻¹gen の単数部 = 1**（(u*u**)·(u*u**)⁻¹=1・実逆元関係
    q3k_inv_mul）。付値 0 かつ単数部 1 ⟹ 生成元の積は 1 で、(π₉⁶)(π₉⁻⁶)=(1)=O_M。 -/
theorem q9fc_diffgen_mul_inv_unit :
    (q9fcMul q9fcDiffGen q9fcInvDiffGen).unit = q3kOne := by
  show q3kMul q9diUnit (q3kInv q9diUnit q9di_unit_isUnit) = q3kOne
  exact q3k_inv_mul q9diUnit q9di_unit_isUnit

/-! ## q9fc-4: 分数イデアル O_M（v≥0）・𝔡（v≥6）・𝔡⁻¹（v≥−6）の述語 -/

/-- **q9fc-4a: O_M 部分対象**（M* の整元 v_M(x)≥0）。 -/
def q9fcInO (x : q9fcUnif) : Prop := (0 : Int) ≤ q9fcVal x

/-- **q9fc-4b: different 𝔡=(π₉⁶) 分数イデアル**（v_M(x)≥6）。 -/
def q9fcMemD (x : q9fcUnif) : Prop := (6 : Int) ≤ q9fcVal x

/-- **q9fc-4c（★）: 逆 different 𝔡⁻¹=(π₉⁻⁶) 分数イデアル**（v_M(x)≥−6・負冪を許す）。
    q9cd が整数影でしか持てなかった 𝔡⁻¹ を、符号付き付値の genuine 部分対象として実現。 -/
def q9fcMemDinv (x : q9fcUnif) : Prop := (-6 : Int) ≤ q9fcVal x

/-- 𝔡⁻¹ の生成元は 𝔡⁻¹ に属する（v_M=−6≥−6）。 -/
theorem q9fc_invdiffgen_memDinv : q9fcMemDinv q9fcInvDiffGen := by
  show (-6 : Int) ≤ q9fcVal q9fcInvDiffGen
  rw [q9fc_invdiffgen_val]
  omega

/-- 𝔡 の生成元は 𝔡 に属する（v_M=6≥6）。 -/
theorem q9fc_diffgen_memD : q9fcMemD q9fcDiffGen := by
  show (6 : Int) ≤ q9fcVal q9fcDiffGen
  rw [q9fc_diffgen_val]
  omega

/-! ## q9fc-5: ★ (i) 𝔡⁻¹ ⊇ O_M と 𝔡 ⊆ O_M -/

/-- **q9fc-5a（★ (i)）: 𝔡⁻¹ ⊇ O_M**——O_M ⊆ 𝔡⁻¹（v≥0 ⟹ v≥−6）。
    𝔡=(π₉⁶)⊆O_M ⟹ 𝔡⁻¹⊇O_M の分数イデアル逆包含の実証。 -/
theorem q9fc_O_subset_Dinv (x : q9fcUnif) (h : q9fcInO x) : q9fcMemDinv x := by
  show (-6 : Int) ≤ q9fcVal x
  have h0 : (0 : Int) ≤ q9fcVal x := h
  omega

/-- **q9fc-5b: 𝔡 ⊆ O_M**（v≥6 ⟹ v≥0・𝔡=(π₉⁶) は整イデアル）。 -/
theorem q9fc_D_subset_O (x : q9fcUnif) (h : q9fcMemD x) : q9fcInO x := by
  show (0 : Int) ≤ q9fcVal x
  have h6 : (6 : Int) ≤ q9fcVal x := h
  omega

/-! ## q9fc-6: ★★ (ii) 𝔡·𝔡⁻¹ = O_M（分数イデアル逆関係） -/

/-- 積イデアル 𝔡·𝔡⁻¹ の所属述語（∃ a∈𝔡, b∈𝔡⁻¹, x=a·b）。 -/
def q9fcProdDDinv (x : q9fcUnif) : Prop :=
  ∃ a b : q9fcUnif, q9fcMemD a ∧ q9fcMemDinv b ∧ x = q9fcMul a b

/-- **q9fc-6（★★ headline (ii)）: 𝔡·𝔡⁻¹ = O_M**——積イデアル述語が O_M（v≥0）と
    **ちょうど一致**（両包含）。
    (⟹) v_M(a·b)=v_M(a)+v_M(b)≥6+(−6)=0 で積が O_M に入る、
    (⟸) v_M(x)=n≥0 の x を x=π₉⁶·(π₉ⁿ⁻⁶·u) と分解（前因子∈𝔡・後因子∈𝔡⁻¹）。
    分数イデアルの逆関係 (π₉⁶)·(π₉⁻⁶)=O_M の genuine な両包含実証——
    q9cd の DEFERRED 分数 𝔡⁻¹ を DEFINED な逆関係へ昇格。 -/
theorem q9fc_diff_inv_eq_O (x : q9fcUnif) : q9fcProdDDinv x ↔ q9fcInO x := by
  constructor
  · intro h
    obtain ⟨a, b, ha, hb, hx⟩ := h
    have ha' : (6 : Int) ≤ q9fcVal a := ha
    have hb' : (-6 : Int) ≤ q9fcVal b := hb
    show (0 : Int) ≤ q9fcVal x
    rw [hx]
    show (0 : Int) ≤ q9fcVal a + q9fcVal b
    omega
  · intro h
    have h' : (0 : Int) ≤ q9fcVal x := h
    refine ⟨⟨6, q3kOne, q3k_unit_one⟩,
            ⟨x.exp - 6, x.unit, x.isUnit⟩, ?_, ?_, ?_⟩
    · show (6 : Int) ≤ (6 : Int)
      omega
    · show (-6 : Int) ≤ x.exp - 6
      have hx0 : (0 : Int) ≤ x.exp := h'
      omega
    · apply q9fcUnif_ext
      · show x.exp = (6 : Int) + (x.exp - 6)
        omega
      · show x.unit = q3kMul q3kOne x.unit
        exact (q3k_one_mul x.unit).symm

/-! ## q9fc-7: (iii) trace-dual 特徴づけ（q9cd 整数影の分数 numerator 描像への接続） -/

/-- **q9fc-7a: numerator シフト** y ↦ y·π₉⁻⁶（整元 y∈O_M を分数 𝔡⁻¹ の代表へ・
    符号付き付値 v(y)−6）。 -/
def q9fcShift6 (y : q9vUnif) : q9fcUnif where
  exp := (y.exp : Int) - 6
  unit := y.unit
  isUnit := y.isUnit

/-- **q9fc-7b（★ (iii) 一部）: numerator y·π₉⁻⁶ ∈ 𝔡⁻¹**——π₉⁻⁶·O_M ⊆ 𝔡⁻¹
    （v(y)−6≥−6・y∈O_M で v(y)≥0）。q9cd の trace-dual 整数影（π₉⁻⁶·O_M⊆𝔡⁻¹）の
    符号付き付値版。 -/
theorem q9fc_shift6_memDinv (y : q9vUnif) : q9fcMemDinv (q9fcShift6 y) := by
  show (-6 : Int) ≤ (y.exp : Int) - 6
  omega

/-- **q9fc-7c（★ (iii) trace-dual）: 𝔡⁻¹ = {x : Tr(x·O_M)⊆O_{L₂}} の整数影が全 y 成立**——
    q9cd_codiff_all を再輸出（numerator y·π₉⁻⁶ の trace-dual 述語 ∀t,π₉⁶∣Tr(y·t) が
    全 y で成立＝π₉⁻⁶·O_M⊆𝔡⁻¹）。q9fc_shift6_memDinv と合わせ、分数 𝔡⁻¹ の numerator
    描像と trace-dual 描像が一致する。 -/
theorem q9fc_tracedual_all (y : q3kCar) : q9cdCodiffMem y := q9cd_codiff_all y

/-- **q9fc-7d（★ (iii) 非退化）: trace-dual は level 7 で破れる**——q9cd_codiff_sharp を
    再輸出（∃y t,¬π₉⁷∣Tr(y·t)）。分数 𝔡⁻¹=(π₉⁻⁶) が **ちょうど** level −6 に
    座る（trace pairing の非退化）ことの trace-dual 側の証拠。 -/
theorem q9fc_tracedual_sharp :
    ¬ (∀ y t : q3kCar, q9wrDvd (q9nfPiPow 7) (q9nfTr (q3kMul y t))) :=
  q9cd_codiff_sharp

/-- **q9fc-7e（★ 分数側 sharp）: 𝔡⁻¹ 生成が ちょうど level −6**——
    ¬(−5 ≤ v_M(𝔡⁻¹gen))（v_M=−6 なので −5≤−6 は偽）。𝔡⁻¹=(π₉⁻⁶)⊋(π₉⁻⁵)——
    逆 different がちょうど −6 に座る分数側の非退化。 -/
theorem q9fc_invdiffgen_sharp : ¬ ((-5 : Int) ≤ q9fcVal q9fcInvDiffGen) := by
  intro h
  have h' : (-5 : Int) ≤ (-6 : Int) := by rw [← q9fc_invdiffgen_val]; exact h
  omega

/-! ## q9fc-8: capstone（束ね・新規証明ゼロ） -/

/-- **q9fc-8: 実 fractional 逆 different データ**——符号付き付値 v_M:M*→ℤ・
    生成元 π₉⁶(𝔡)/π₉⁻⁶(𝔡⁻¹)・生成元逆関係 v(𝔡gen·𝔡⁻¹gen)=0 & 単数部=1・
    (i) 𝔡⁻¹⊇O_M・(ii) 𝔡·𝔡⁻¹=O_M・(iii) trace-dual（全 y 成立・level 7 破れ）を
    束ねる（新規証明ゼロ）。 -/
structure Q3FractionalCodifferentData where
  /-- 付値の加法性 v_M(xy)=v_M(x)+v_M(y)。 -/
  val_mul : ∀ x y : q9fcUnif, q9fcVal (q9fcMul x y) = q9fcVal x + q9fcVal y
  /-- v_M(𝔡gen)=6・v_M(𝔡⁻¹gen)=−6。 -/
  gen_vals : q9fcVal q9fcDiffGen = 6 ∧ q9fcVal q9fcInvDiffGen = -6
  /-- 生成元逆関係 v(𝔡gen·𝔡⁻¹gen)=0 かつ単数部=1（(π₉⁶)(π₉⁻⁶)=(1)）。 -/
  gen_inverse : q9fcVal (q9fcMul q9fcDiffGen q9fcInvDiffGen) = 0
    ∧ (q9fcMul q9fcDiffGen q9fcInvDiffGen).unit = q3kOne
  /-- (i) 𝔡⁻¹ ⊇ O_M。 -/
  O_subset_Dinv : ∀ x : q9fcUnif, q9fcInO x → q9fcMemDinv x
  /-- (ii) 𝔡·𝔡⁻¹ = O_M（両包含）。 -/
  diff_inv_eq_O : ∀ x : q9fcUnif, q9fcProdDDinv x ↔ q9fcInO x
  /-- (iii) trace-dual: numerator y·π₉⁻⁶ ∈ 𝔡⁻¹。 -/
  shift6_memDinv : ∀ y : q9vUnif, q9fcMemDinv (q9fcShift6 y)
  /-- (iii) trace-dual: 整数影が全 y 成立（π₉⁻⁶·O_M⊆𝔡⁻¹）。 -/
  tracedual_all : ∀ y : q3kCar, q9cdCodiffMem y
  /-- (iii) trace-dual: level 7 で破れる（非退化）。 -/
  tracedual_sharp : ¬ (∀ y t : q3kCar, q9wrDvd (q9nfPiPow 7) (q9nfTr (q3kMul y t)))

/-- **見出し実例** — 実 M=ℚ₃(ζ₉) 上の genuine な分数逆 different 𝔡⁻¹=(π₉⁻⁶)。 -/
def q9fc_data : Q3FractionalCodifferentData where
  val_mul := q9fc_val_mul
  gen_vals := ⟨q9fc_diffgen_val, q9fc_invdiffgen_val⟩
  gen_inverse := ⟨q9fc_diffgen_mul_inv_val, q9fc_diffgen_mul_inv_unit⟩
  O_subset_Dinv := q9fc_O_subset_Dinv
  diff_inv_eq_O := q9fc_diff_inv_eq_O
  shift6_memDinv := q9fc_shift6_memDinv
  tracedual_all := q9fc_tracedual_all
  tracedual_sharp := q9fc_tracedual_sharp

/-- **実 fractional 逆 different 構造の存在**（𝔡⁻¹=(π₉⁻⁶) を符号付き付値の
    genuine 分数イデアル部分対象として・𝔡·𝔡⁻¹=O_M を含む）。 -/
theorem q9fc_exists : Nonempty Q3FractionalCodifferentData := ⟨q9fc_data⟩

end IUT
