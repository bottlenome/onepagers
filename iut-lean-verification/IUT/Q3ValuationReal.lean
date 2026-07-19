/-
  IUT/Q3ValuationReal.lean — 柱B・B1/B3 実 v_M 付値関数の建設（一様化子冪部分モノイド版）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（複数の B 監査 B1 q9gl・B3 q9tw/q9tf が
     SAME missing machinery として名指しした「実 v_M 付値関数の建設」——現行の可除性形式
     `q9wrDvd (q9nfPiPow n) x`（∃c, x=π₉ⁿ·c）を、実際の**付値関数** v_M へ置換する）。
     本ラウンドは一様化子冪部分モノイド {π₉ⁿ·u : u 単数} 上の**忠実な完全付値関数**
     q9vVal : q9vUnif → Nat を実 Lean で建て、i_G(σ)=v_M(σπ₉−π₉) を初めて DEFINED
     な値（=3）として与える（従来の可除性下界ではなく厳密な付値値）。主語は実 π₉・実 σ・
     実単数 u*——toy 模型（m202fVol 型・Bool 軌道・surrogate 群）を一切使わない。

  complete_pct 影響: **B1/B3（audit-decided, forecast modest）**。可除性形式の付値
     ↔ 実付値関数のブリッジ q9v_dvd_iff（q9wrDvd (q9nfPiPow n) (q9vElt x) ↔ n ≤ q9vVal x）が、
     B1「generator-independence を equality inf として述べたい」・B3「abstract different ideal」の
     両監査が名指しした「実 v_M 不在」の正直限定を、部分モノイド上で**本物に retire** する。
     i_G(σ)=v_M(σπ₉−π₉)=3（q9v_sigmaPi_val）は break t=2 の実分岐 jump を初めて
     厳密な付値値として確定する。

  核心の実データ:
   * q9vUnif — 部分モノイド {π₉ⁿ·u}（exp・unit・isUnit を明示保持し choice-free に）
   * q9vVal / q9vElt — 実付値関数（exp 射影）と対応する実 q3kCar 元
   * q9v_val_pi9 : v_M(π₉)=1
   * q9v_val_unit : q3kUnitMem(q9vElt x) ⟹ v_M(x)=0
   * q9v_val_mul : v_M(x·y)=v_M(x)+v_M(y)（一様化子冪モノイドの加法性）
   * q9v_dvd_iff : q9wrDvd (q9nfPiPow n) (q9vElt x) ↔ n ≤ v_M(x)（★ ブリッジ・限定 retire）
   * q9v_wellDef : q9vElt x = q9vElt y ⟹ v_M(x)=v_M(y)（★ 付値の well-defined 性＝核心）
   * q9v_ultrametric : π₉^{min(v x, v y)} ∣ (q9vElt x + q9vElt y)（超距離）
   * q9v_pi9_not_dvd_unit : π₉ ∤ 単数（★ well-defined 性の crux・ノルム 3·s 非単数）
   * q9v_sigmaPi_val : v_M(σπ₉−π₉)=3 = i_G(σ)（★ break t=2 jump の厳密付値化）

  正直な限定（§4 規約により消さない・弱めない・q3k/q9ps/q9wr/q9nf 継承の上に追記のみ）:
  1. **TOTAL な付値関数 v_M : q3kCar → Nat は建てない**（choice-free に不可能）。
     total 化は v(0)=∞ の総関数化と非零判定（Π⁰₂ = Markov/排中律の断片）を要する——
     ℤ₃ 側 Zp3ValuationRing.lean（z3v）が同じ理由で付値を「関係」z3vGe で持つのと同型の障壁。
     本ファイルは一様化子冪部分モノイド {π₉ⁿ·u} 上に忠実な**関数**を建て、その上で
     完全な付値公理（v_pi9=1・v_unit=0・v_mul 加法性・dvd_iff ブリッジ・well-defined）を割る。
  2. **一様化子冪部分モノイドのみ**。一般元 x∈O_M（π₉ 冪単数でない元・0・非零因子でない）の
     付値は本ラウンド範囲外——それは z3v 型の関係付値 z3vGe の M 版（後続）を要する。
  3. **拡大 1 個（M/L₂）・下付き付値のみ**。上付き番号・Herbrand・実 Hasse–Arf は継承限定。
  4. dvd_iff ブリッジと well-defined 性は部分モノイド上で完全——B1/B3 が名指した限定を
     この部分モノイド上で本物に retire する（一般元への拡張が残る正直な差分）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3NormFiltrationSpike

namespace IUT

/-! ## q9v-0: π₉ ∤ 単数（well-defined 性の crux・ノルム 3·s 非単数） -/

/-- **q9v-0（★ crux）: π₉ は実単数を割らない**。もし π₉ ∣ u（u 単数）なら
    N(u)=N(π₉)·N(c)=(ζ₃−1)·N(c)、q3rqNorm を取ると 3·s の形になり ℤ₃ 単数でない
    （q9wr_three_mul_not_unit）——u が単数であることと矛盾。q9wr_G3_trivial の
    ノルム 2 段イディオムを「一様化子でない単数の π₉-可除性排除」へ抽出。 -/
theorem q9v_pi9_not_dvd_unit (u : q3kCar) (hu : q3kUnitMem u) :
    ¬ q9wrDvd q9psPi9 u := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hunit : IsZpUnit 3 (q3rqNorm (q3kNormBase u)) := hu
  have hnorm : q3kNormBase u = q3rqMul (q3kNormBase q9psPi9) (q3kNormBase c) := by
    rw [hc, q3k_normBase_mul q9psPi9 c]
  rw [hnorm, q9wr_normBase_pi9, q3rq_norm_mul, q9wr_qnorm_zeta_sub] at hunit
  exact q9wr_three_mul_not_unit (q3rqNorm (q3kNormBase c)) hunit

/-! ## q9v-1: 一様化子冪の一般相殺 π₉ⁿ·a = π₉ⁿ·b ⟹ a = b -/

/-- **q9v-1: π₉ⁿ の正則相殺**（q9wr_pi9_cancel の n 帰納一般化）。 -/
theorem q9v_pipow_cancel (n : Nat) {a b : q3kCar}
    (h : q3kMul (q9nfPiPow n) a = q3kMul (q9nfPiPow n) b) : a = b := by
  induction n with
  | zero =>
    have h' : q3kMul q3kOne a = q3kMul q3kOne b := h
    rw [q3k_one_mul a, q3k_one_mul b] at h'
    exact h'
  | succ n ih =>
    have h' : q3kMul (q3kMul q9psPi9 (q9nfPiPow n)) a
        = q3kMul (q3kMul q9psPi9 (q9nfPiPow n)) b := h
    rw [q3k_mul_assoc q9psPi9 (q9nfPiPow n) a,
        q3k_mul_assoc q9psPi9 (q9nfPiPow n) b] at h'
    exact ih (q9wr_pi9_cancel h')

/-! ## q9v-2: 一様化子冪部分モノイド q9vUnif と付値関数 q9vVal -/

/-- **q9v-2a: 一様化子冪部分モノイド {π₉ⁿ·u}**——付値 exp・単数 unit・その単数性を
    明示保持する（∃ からの exp 抽出を避け choice-free に）。 -/
structure q9vUnif where
  /-- 付値（一様化子 π₉ の冪指数）。 -/
  exp : Nat
  /-- 単数因子 u。 -/
  unit : q3kCar
  /-- u が実単数であること。 -/
  isUnit : q3kUnitMem unit

/-- **q9v-2b: 対応する実 O_M 元** π₉^exp · u。 -/
def q9vElt (x : q9vUnif) : q3kCar := q3kMul (q9nfPiPow x.exp) x.unit

/-- **q9v-2c（★）: 実付値関数 v_M**（一様化子冪指数）。 -/
def q9vVal (x : q9vUnif) : Nat := x.exp

/-! ## q9v-3: 付値のブリッジ q9wrDvd ↔ v_M（★ 可除性限定の retire） -/

/-- **q9v-3（★ ブリッジ）: q9wrDvd (π₉ⁿ) (q9vElt x) ↔ n ≤ v_M(x)**。
    可除性形式（q9wr/q9nf の主表現）と実付値関数の**厳密な同値**——
    B1/B3 監査が名指した「実 v_M 不在」の正直限定を部分モノイド上で retire する核心。
    (⟸) は指数単調性、(⟹) は π₉^{v+1}∣ ⟹ π₉ⁿ 相殺 ⟹ π₉∣単数 で矛盾。 -/
theorem q9v_dvd_iff (x : q9vUnif) (n : Nat) :
    q9wrDvd (q9nfPiPow n) (q9vElt x) ↔ n ≤ q9vVal x := by
  constructor
  · intro h
    have key : ¬ x.exp < n := by
      intro hlt
      have hle : x.exp + 1 ≤ n := hlt
      obtain ⟨c, hc⟩ := q9nf_dvd_of_le hle h
      have heq : q3kMul (q9nfPiPow x.exp) x.unit
          = q3kMul (q9nfPiPow (x.exp + 1)) c := hc
      rw [q9nf_pipow_add x.exp 1, q9nf_pipow1_eq,
          q3k_mul_assoc (q9nfPiPow x.exp) q9psPi9 c] at heq
      have hu : x.unit = q3kMul q9psPi9 c := q9v_pipow_cancel x.exp heq
      exact q9v_pi9_not_dvd_unit x.unit x.isUnit ⟨c, hu⟩
    show n ≤ x.exp
    omega
  · intro h
    exact q9nf_dvd_of_le h ⟨x.unit, rfl⟩

/-! ## q9v-4: 付値公理 v(π₉)=1・v(unit)=0・v(xy)=v(x)+v(y) -/

/-- π₉ を表す部分モノイド元（π₉ = π₉¹·1）。 -/
def q9vPi9 : q9vUnif where
  exp := 1
  unit := q3kOne
  isUnit := q3k_unit_one

/-- **q9v-4a: q9vPi9 の実元は π₉**。 -/
theorem q9v_pi9_elt : q9vElt q9vPi9 = q9psPi9 := by
  show q3kMul (q9nfPiPow 1) q3kOne = q9psPi9
  rw [q9nf_pipow1_eq, q3k_mul_comm q9psPi9 q3kOne, q3k_one_mul q9psPi9]

/-- **q9v-4b: v_M(π₉) = 1**。 -/
theorem q9v_val_pi9 : q9vVal q9vPi9 = 1 := rfl

/-- **q9v-4c: v_M(unit) = 0**——q9vElt x が実単数なら exp=0（さもなくば π₉∣単数）。 -/
theorem q9v_val_unit (x : q9vUnif) (hu : q3kUnitMem (q9vElt x)) : q9vVal x = 0 := by
  have hnot : ¬ 1 ≤ x.exp := by
    intro h1
    have hdvd : q9wrDvd (q9nfPiPow 1) (q9vElt x) := (q9v_dvd_iff x 1).mpr h1
    rw [q9nf_pipow1_eq] at hdvd
    exact q9v_pi9_not_dvd_unit (q9vElt x) hu hdvd
  show x.exp = 0
  omega

/-- **q9v-4d: 部分モノイドの積**（π₉^{a+b}·(u·u')）。 -/
def q9vMul (x y : q9vUnif) : q9vUnif where
  exp := x.exp + y.exp
  unit := q3kMul x.unit y.unit
  isUnit := q3k_unit_mul x.isUnit y.isUnit

/-- **q9v-4e: 積の実元は元の積**。 -/
theorem q9v_elt_mul (x y : q9vUnif) :
    q9vElt (q9vMul x y) = q3kMul (q9vElt x) (q9vElt y) := by
  show q3kMul (q9nfPiPow (x.exp + y.exp)) (q3kMul x.unit y.unit)
     = q3kMul (q3kMul (q9nfPiPow x.exp) x.unit) (q3kMul (q9nfPiPow y.exp) y.unit)
  rw [q9nf_pipow_add x.exp y.exp, q3k_kM_eq]
  exact (q3kRing.mul_mul_mul_comm (q9nfPiPow x.exp) x.unit (q9nfPiPow y.exp) y.unit).symm

/-- **q9v-4f（★）: 付値の加法性 v_M(x·y) = v_M(x) + v_M(y)**。 -/
theorem q9v_val_mul (x y : q9vUnif) :
    q9vVal (q9vMul x y) = q9vVal x + q9vVal y := rfl

/-! ## q9v-5: 付値の well-defined 性（★ 実元にのみ依存する）と超距離 -/

/-- **q9v-5（★ well-defined）: q9vElt x = q9vElt y ⟹ v_M(x) = v_M(y)**。
    一様化子冪分解の指数は実元にのみ依存する——付値が「関数」たりうる核心。
    ブリッジ q9v_dvd_iff の両向き適用で相互不等式を得て omega。 -/
theorem q9v_wellDef (x y : q9vUnif) (hxy : q9vElt x = q9vElt y) :
    q9vVal x = q9vVal y := by
  have hx_dvd_y : q9wrDvd (q9nfPiPow x.exp) (q9vElt y) := by
    rw [← hxy]; exact ⟨x.unit, rfl⟩
  have hy_dvd_x : q9wrDvd (q9nfPiPow y.exp) (q9vElt x) := by
    rw [hxy]; exact ⟨y.unit, rfl⟩
  have h1 : x.exp ≤ y.exp := (q9v_dvd_iff y x.exp).mp hx_dvd_y
  have h2 : y.exp ≤ x.exp := (q9v_dvd_iff x y.exp).mp hy_dvd_x
  show x.exp = y.exp
  omega

/-- **q9v-5b（超距離）: π₉^{min(v x, v y)} ∣ (q9vElt x + q9vElt y)**。
    実付値の非アルキメデス（超距離）不等式 v(x+y) ≥ min(v x, v y) の可除性実現。 -/
theorem q9v_ultrametric (x y : q9vUnif) :
    q9wrDvd (q9nfPiPow (Nat.min (q9vVal x) (q9vVal y)))
      (q3kAdd (q9vElt x) (q9vElt y)) := by
  refine q9nf_dvd_add ?_ ?_
  · exact q9nf_dvd_of_le (Nat.min_le_left x.exp y.exp) ⟨x.unit, rfl⟩
  · exact q9nf_dvd_of_le (Nat.min_le_right x.exp y.exp) ⟨y.unit, rfl⟩

/-! ## q9v-6: ★ payoff——i_G(σ) = v_M(σπ₉−π₉) = 3（break t=2 jump の厳密付値化） -/

/-- σπ₉−π₉ を表す部分モノイド元（= π₉³·u*・q9wr_ustar_unit）。 -/
def q9vSigmaPi : q9vUnif where
  exp := 3
  unit := q9wrUStar
  isUnit := q9wr_ustar_unit

/-- **q9v-6a: q9vSigmaPi の実元は σπ₉−π₉**。 -/
theorem q9v_sigmaPi_elt :
    q9vElt q9vSigmaPi = q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9) := by
  show q3kMul (q9nfPiPow 3) q9wrUStar = q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)
  have h3 : q9nfPiPow 3 = q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9 := q9nf_pipow3_eq
  rw [h3, q9wr_sigma_pi_eq]

/-- **q9v-6b（★ headline）: i_G(σ) = v_M(σπ₉−π₉) = 3**。
    break t=2 の実野性分岐 jump を、可除性下界ではなく**厳密な付値値**として初確定。
    B1 の i_G(σ)=v_M(σx−x) が DEFINED になる実例——σ の一様化子作用差の付値は正確に 3。 -/
theorem q9v_sigmaPi_val : q9vVal q9vSigmaPi = 3 := rfl

/-- **q9v-6c: 付値値 3 とブリッジの整合**——π₉³∣(σπ₉−π₉) かつ ¬π₉⁴∣(σπ₉−π₉) が
    v_M=3 から dvd_iff 経由で従う（q9wr_break の実付値関数版）。 -/
theorem q9v_sigmaPi_break :
    q9wrDvd (q9nfPiPow 3) (q9vElt q9vSigmaPi)
    ∧ ¬ q9wrDvd (q9nfPiPow 4) (q9vElt q9vSigmaPi) := by
  refine ⟨(q9v_dvd_iff q9vSigmaPi 3).mpr (Nat.le_refl 3), ?_⟩
  intro h4
  have : (4 : Nat) ≤ q9vVal q9vSigmaPi := (q9v_dvd_iff q9vSigmaPi 4).mp h4
  rw [q9v_sigmaPi_val] at this
  omega

/-! ## q9v-7: capstone（実 v_M 付値データの束ね） -/

/-- **q9v-7: 実 v_M 付値関数データ**（一様化子冪部分モノイド上の完全付値・
    新規証明ゼロ・束ねのみ）。 -/
structure Q3ValuationRealData where
  /-- v_M(π₉) = 1（一様化子の付値）。 -/
  val_pi9 : q9vVal q9vPi9 = 1
  /-- v_M(x·y) = v_M(x) + v_M(y)（加法性）。 -/
  val_mul : ∀ x y : q9vUnif, q9vVal (q9vMul x y) = q9vVal x + q9vVal y
  /-- ブリッジ q9wrDvd ↔ v_M（可除性限定の retire）。 -/
  dvd_iff : ∀ (x : q9vUnif) (n : Nat),
    q9wrDvd (q9nfPiPow n) (q9vElt x) ↔ n ≤ q9vVal x
  /-- 付値の well-defined 性（実元にのみ依存）。 -/
  wellDef : ∀ x y : q9vUnif, q9vElt x = q9vElt y → q9vVal x = q9vVal y
  /-- i_G(σ) = v_M(σπ₉−π₉) = 3（break t=2 jump の厳密付値化）。 -/
  sigmaPi_val : q9vVal q9vSigmaPi = 3

/-- **見出し実例** — 一様化子冪部分モノイド上の実 v_M 付値関数。 -/
def q9v_data : Q3ValuationRealData where
  val_pi9 := q9v_val_pi9
  val_mul := q9v_val_mul
  dvd_iff := q9v_dvd_iff
  wellDef := q9v_wellDef
  sigmaPi_val := q9v_sigmaPi_val

/-- **実 v_M 付値関数の存在**（部分モノイド {π₉ⁿ·u}・i_G(σ)=3 を含む）。 -/
theorem q9v_exists : Nonempty Q3ValuationRealData := ⟨q9v_data⟩

end IUT
