/-
  IUT/Q3DifferentIdeal.lean — 柱B・B3 実 different の可除性形式 → 本物の DIFFERENT IDEAL
    OBJECT 𝔡_{M/L₂} = (π₉⁶)（v_M(D)=6・π₉⁶∣D∧¬π₉⁷∣D を、実 O_M 上の genuine な
    主イデアル対象として昇格）

  ── 主要成果の分類: **[実／(a) 昇格]** — q9tw/q9ac/q9dv が **可除性形式**
     （π₉⁶∣D ∧ ¬π₉⁷∣D）および q9dv の **付値値** v_M(D)=6 として持っていた実 different を、
     コードベースの **本物の環イデアル構造** `primeSpecIdeal`（0∈I・加法閉・環倍吸収
     R·I⊆I）の実 `q3kRing` インスタンスとして **genuine な IDEAL OBJECT** 𝔡_{M/L₂}=(π₉⁶)
     へ昇格する。所属述語 q9diMem x := π₉⁶∣x が真の O_M-イデアル公理（zero/add/smul）を
     割り、D∈𝔡・𝔡=(D)=(π₉⁶)（D=π₉⁶·単数 の associate 等式・実逆元 q3kInv 使用）・
     鋭さ ¬π₉⁷∣D を実で証明する。主語は実 π₉⁶・実 different D=(σπ₉−π₉)(σ²π₉−π₉)・
     実単数 u*·u**——toy 模型（Bool 軌道・surrogate 群）を一切使わない。

  complete_pct 影響: **B3 0.27→（独立監査次第・予測 +0.02〜0.05・different ideal object 化）**。
     動かす新規内容は「散在していた可除性下界／上界（π₉⁶∣D・¬π₉⁷∣D）と付値値 v_M(D)=6 を、
     単一の **本物のイデアル対象** 𝔡=(π₉⁶)∈`primeSpecIdeal q3kRing` に retire し、
     different がその生成元であること（𝔡=(D)、associate 等式で両包含を実証）を割る」こと。
     従来の scattered な divisibility 言明を genuine な ideal-object の言明へ置換する。

  核心の実データ（真水・NEW）:
   * q9diMem / q9diDifferentIdeal — 𝔡_{M/L₂}=(π₉⁶) を **本物の環イデアル**
     （`primeSpecIdeal q3kRing`・O_M-イデアル公理 zero/add/smul を実で充足）として実現
   * q9di_mem_iff_val — 𝔡 = 付値サブレベル: 付値域 q9vUnif 上で x∈𝔡 ⟺ 6 ≤ v_M(x)
     （q9v_dvd_iff ブリッジ・散在下界の genuine ideal 化）
   * q9di_different_mem — D ∈ 𝔡（different 生成元がイデアルに属する）
   * q9di_ideal_add / q9di_ideal_smul — 加法閉性・O_M-環倍吸収（イデアル公理の実証）
   * q9di_different_eq_pi6 — 𝔡 = (D) = (π₉⁶) **ちょうど**（D=π₉⁶·(u*u**)、u*u** 実単数の
     associate 等式で両包含・実逆元 q3kInv を消費）
   * q9di_different_sharp — ¬π₉⁷∣D（生成元がちょうど level 6・q9ac_different_sharp を付値冪橋
     q9dv_pipow7_eq 経由で ideal-object 言明へ）
   * Q3DifferentIdealData — capstone（束ね）

  正直な限定（§4 規約により消さない・弱めない・q9v/q9dv/q9wr/q9ac 継承の上に追記のみ）:
  1. **主イデアル (π₉⁶) のみ・拡大 1 個（M/L₂）**。一般 Dedekind different 理論・
     素イデアル分解・different の推移公式（d(M/ℚ₃)）は範囲外。
  2. **分数イデアル群・イデアル類群はゼロ**。逆 different 𝔡⁻¹=(π₉⁻⁶) は O_M の分数イデアル
     （負冪）を要し、本モジュールの整イデアル (π₉⁶)⊆O_M の枠外——codifferent の trace-dual
     characterization {y : Tr(y·O_M)⊆O_L₂} も L₂ 上の trace pairing を要するため未達
     （honest scope note・toy を作らない §3 遵守）。
  3. **付値サブレベル同定 q9di_mem_iff_val は付値部分モノイド q9vUnif 上のみ**——
     一般元 x∈O_M への拡張は q9v の TOTAL 付値不在（choice-free 障壁）を継承。
  4. 𝔡=(π₉⁶) の生成元 different D=π₉⁶·(u*u**) は q9wr_different を消費・鋭さ ¬π₉⁷∣D は
     q9ac_different_sharp を消費（新規なのは ideal-object 化と associate 等式による 𝔡=(D)）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3DifferentValuation
import IUT.PrimeSpectrum

namespace IUT

/-! ## q9di-0: different 生成元 D と単数因子 u*·u** -/

/-- 実 different 生成元 D = (σπ₉−π₉)(σ²π₉−π₉)（q9wr_different の主語）。 -/
def q9diD : q3kCar :=
  q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
         (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))

/-- different の単数因子 u*·u**（D = π₉⁶·(u*u**) の単数部分）。 -/
def q9diUnit : q3kCar := q3kMul q9wrUStar q9wrUStarStar

/-- u*·u** は実単数（q9wr の単数性を消費）。 -/
theorem q9di_unit_isUnit : q3kUnitMem q9diUnit :=
  q3k_unit_mul q9wr_ustar_unit q9wr_ustarstar_unit

/-- **D = π₉⁶·(u*u**)**（q9wr_different を D/q9diUnit 記法へ・defeq）。 -/
theorem q9di_different_factor : q9diD = q3kMul q9psPi6 q9diUnit := q9wr_different

/-! ## q9di-1: 所属述語 q9diMem と本物の環イデアル対象 𝔡=(π₉⁶) -/

/-- **q9di-1a（★）: 𝔡_{M/L₂} の所属述語** x ∈ 𝔡 = (π₉⁶) ⟺ π₉⁶ ∣ x（主イデアル）。 -/
def q9diMem (x : q3kCar) : Prop := q9wrDvd (q9nfPiPow 6) x

/-- 所属述語の定義的特徴づけ（可除性形式との橋渡し）。 -/
theorem q9di_mem_iff (x : q3kCar) : q9diMem x ↔ q9wrDvd (q9nfPiPow 6) x := Iff.rfl

/-- **q9di-1b: 加法閉性** x,y ∈ 𝔡 ⟹ x+y ∈ 𝔡（イデアル公理・q9nf_dvd_add 消費）。 -/
theorem q9di_ideal_add (x y : q3kCar) (hx : q9diMem x) (hy : q9diMem y) :
    q9diMem (q3kAdd x y) :=
  q9nf_dvd_add hx hy

/-- **q9di-1c（★）: O_M-環倍吸収** x ∈ 𝔡 ⟹ r·x ∈ 𝔡（任意 r∈O_M・イデアル公理の核）。 -/
theorem q9di_ideal_smul (r x : q3kCar) (hx : q9diMem x) : q9diMem (q3kMul r x) := by
  rw [q3k_mul_comm r x]
  exact q9nf_dvd_mul_right hx r

/-- 0 ∈ 𝔡（イデアル公理・q9nf_dvd_zero 消費）。 -/
theorem q9di_ideal_zero : q9diMem q3kZero := q9nf_dvd_zero (q9nfPiPow 6)

/-- **q9di-1d（★ IDEAL OBJECT）: 𝔡_{M/L₂}=(π₉⁶) を本物の環イデアルとして実現**——
    コードベースの genuine な `primeSpecIdeal q3kRing`（0∈I・加法閉・環倍吸収 R·I⊆I）の
    実インスタンス。所属 q9diMem が真の O_M-イデアル公理を充足する（可除性形式の散在言明を
    単一の ideal-object へ昇格）。 -/
def q9diDifferentIdeal : primeSpecIdeal q3kRing where
  mem := q9diMem
  zero_mem := q9di_ideal_zero
  add_mem := q9di_ideal_add
  smul_mem := q9di_ideal_smul

/-! ## q9di-2: 𝔡 = 付値サブレベル（付値部分モノイド上の genuine ideal 化） -/

/-- **q9di-2（★）: 𝔡 = 付値サブレベル**——付値域 q9vUnif 上で x ∈ 𝔡 ⟺ 6 ≤ v_M(x)。
    q9v_dvd_iff ブリッジにより、散在していた可除性下界（π₉⁶∣D）を **単一の付値サブレベル
    membership**（イデアル対象そのもの）へ retire する。 -/
theorem q9di_mem_iff_val (x : q9vUnif) : q9diMem (q9vElt x) ↔ 6 ≤ q9vVal x :=
  q9v_dvd_iff x 6

/-! ## q9di-3: different 生成元 D がイデアルに属する（D ∈ 𝔡） -/

/-- **q9di-3（★）: D ∈ 𝔡**——different 生成元 D=(σπ₉−π₉)(σ²π₉−π₉) が主イデアル (π₉⁶) に
    属する（D=π₉⁶·(u*u**)・q9wr_different 消費）。 -/
theorem q9di_different_mem : q9diMem q9diD := by
  refine ⟨q9diUnit, ?_⟩
  rw [q9nf_pipow6_eq]
  exact q9di_different_factor

/-! ## q9di-4: ★ 𝔡 = (D) = (π₉⁶) ちょうど（associate 等式・両包含） -/

/-- **q9di-4（★ headline）: 𝔡 = (D) = (π₉⁶) ちょうど**——different D で生成される
    イデアル (D)={x : D∣x} が主イデアル 𝔡=(π₉⁶) と **一致**する。D=π₉⁶·(u*u**) の
    u*u** が実単数（associate）であることから両包含を実証（⟸ 向きは実逆元 q3kInv を消費）。
    可除性下界／上界の散在言明を「different が 𝔡 の生成元」という genuine ideal-object 等式へ昇格。 -/
theorem q9di_different_eq_pi6 (x : q3kCar) : q9wrDvd q9diD x ↔ q9diMem x := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    refine ⟨q3kMul q9diUnit c, ?_⟩
    rw [q9nf_pipow6_eq, hc, q9di_different_factor, q3k_mul_assoc q9psPi6 q9diUnit c]
  · intro h
    obtain ⟨c, hc⟩ := h
    refine ⟨q3kMul (q3kInv q9diUnit q9di_unit_isUnit) c, ?_⟩
    rw [hc, q9nf_pipow6_eq, q9di_different_factor,
        q3k_mul_assoc q9psPi6 q9diUnit (q3kMul (q3kInv q9diUnit q9di_unit_isUnit) c),
        ← q3k_mul_assoc q9diUnit (q3kInv q9diUnit q9di_unit_isUnit) c,
        q3k_inv_mul q9diUnit q9di_unit_isUnit, q3k_one_mul c]

/-! ## q9di-5: ★ 生成元の鋭さ ¬π₉⁷∣D（𝔡 はちょうど level 6・≠(π₉⁷)） -/

/-- **q9di-5（★）: ¬π₉⁷ ∣ D**——𝔡=(D)=(π₉⁶) の生成元がちょうど level 6 に座る
    （𝔡 ⊋ (π₉⁷)）。q9ac_different_sharp（¬π₉⁶·π₉∣D）を付値冪橋 q9dv_pipow7_eq（π₉⁷=π₉⁶·π₉）
    経由で ideal-object 言明へ。 -/
theorem q9di_different_sharp : ¬ q9wrDvd (q9nfPiPow 7) q9diD := by
  rw [q9dv_pipow7_eq]
  exact q9ac_different_sharp

/-- **q9di-5b: D ∉ (π₉⁷) 即ち 𝔡=(D) は (π₉⁷) を真に含む**（sharp の ideal 版・
    q9di_different_mem と合わせ 𝔡 の level が **ちょうど 6**）。 -/
theorem q9di_different_level6 :
    q9diMem q9diD ∧ ¬ q9wrDvd (q9nfPiPow 7) q9diD :=
  ⟨q9di_different_mem, q9di_different_sharp⟩

/-! ## q9di-6: capstone（束ね・新規証明ゼロ）

  逆 different 𝔡⁻¹=(π₉⁻⁶) / codifferent の trace-dual characterization
  {y : Tr(y·O_M)⊆O_L₂} は O_M の分数イデアル（負冪）・L₂ 上の trace pairing を要し、
  本モジュールの整イデアル (π₉⁶)⊆O_M の枠外である（正直な限定 2・toy を作らず honest scope）。 -/

/-- **q9di-6: 実 different ideal データ**——本物の環イデアル対象 𝔡=(π₉⁶)・付値サブレベル
    同定・D∈𝔡・𝔡=(D)=(π₉⁶)・生成元の鋭さ ¬π₉⁷∣D を束ねる（新規証明ゼロ）。 -/
structure Q3DifferentIdealData where
  /-- 本物の環イデアル対象 𝔡_{M/L₂}=(π₉⁶)∈`primeSpecIdeal q3kRing`。 -/
  ideal : primeSpecIdeal q3kRing
  /-- 𝔡 = 付値サブレベル（付値域上で x∈𝔡 ⟺ 6≤v_M(x)）。 -/
  mem_iff_val : ∀ x : q9vUnif, q9diMem (q9vElt x) ↔ 6 ≤ q9vVal x
  /-- D ∈ 𝔡（different 生成元がイデアルに属する）。 -/
  different_mem : q9diMem q9diD
  /-- D = π₉⁶·(u*u**)（生成元の associate 分解）。 -/
  different_factor : q9diD = q3kMul q9psPi6 q9diUnit
  /-- 𝔡 = (D) = (π₉⁶) ちょうど（associate 両包含）。 -/
  eq_pi6 : ∀ x : q3kCar, q9wrDvd q9diD x ↔ q9diMem x
  /-- ¬π₉⁷∣D（生成元がちょうど level 6）。 -/
  sharp : ¬ q9wrDvd (q9nfPiPow 7) q9diD

/-- **見出し実例** — 実 M=ℚ₃(ζ₉) 上の genuine な different ideal object 𝔡=(π₉⁶)。 -/
def q9di_data : Q3DifferentIdealData where
  ideal := q9diDifferentIdeal
  mem_iff_val := q9di_mem_iff_val
  different_mem := q9di_different_mem
  different_factor := q9di_different_factor
  eq_pi6 := q9di_different_eq_pi6
  sharp := q9di_different_sharp

/-- **実 different ideal object の存在**（𝔡_{M/L₂}=(π₉⁶) を本物の環イデアルとして）。 -/
theorem q9di_exists : Nonempty Q3DifferentIdealData := ⟨q9di_data⟩

end IUT
