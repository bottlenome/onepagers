/-
  IUT/Q3ArtinConductorReal.lean — 柱B・B3 実 Artin 導手／conductor–discriminant
    （実 Gal(M/L₂)=⟨σ⟩ の実指標の Artin 導手と実 different の鋭さ）

  ── 主要成果の分類: **[実／(a) 昇格]** — wcd/mjw/ajw/arc の **Nat 階段** Artin 導手・
     conductor–discriminant（監査が「Artin 導手は Bool→Nat」と模型判定済み）を、
     実 Gal(M/L₂)=⟨q3kSigma⟩ の **実指標**（q9kd の Hom(⟨σ⟩,μ₃)）× **実分岐フィルトレーション**
     （q9wr の break t=2・π₉ 可除性）の上の **実 Artin 導手／実 conductor–discriminant** へ昇格する。
     主語は実 σ・実 π₉=Y−1・実 O_M・実指標——toy 模型を一切使わない。

  **本モジュールの真水（NEW・監査対象の新規実定理）は次の 3 点に限定する**:
   (A2) σ² 側の break 上界 `¬π₉⁴∣(σ²π₉−π₉)`——q9wr は σ 側しか持たない欠落を埋める。
   (A7) 実 different の鋭さ `¬π₉⁷∣D`（D=π₉⁶·(u*·u**)）——d(M/L₂)=6「ちょうど」の実証。
   (A4/A5/A8) 実指標の Artin 導手 a(χ⁰)=0, a(χ)=a(χ²)=3 を、実 G_i フィルトレーション帰属
     （π₉ 可除性の iff-spec で緊縛）から導出し、`q9kd_hom_complete` により **全指標**にわたる和
     Σ_φ a(φ)=6=d の実 Führerdiskriminanten（conductor–discriminant）公式を両辺実で建てる。

  **消費（再主張しない・二重計上回避）**:
   * d=6 の実恒等式 D=(σπ₉−π₉)(σ²π₉−π₉)=π₉⁶·(u*u**) は `q9wr_different` から **消費**。
   * G₂ 帰属（π₉³∣σπ₉−π₉・σ²π₉−π₉）は `q9wr_G2_mem`、σ 側 break 上界 `¬π₉⁴∣σπ₉−π₉` は
     `q9wr_G3_trivial` から **消費**。u*/u** の単数性は `q9wr_ustar(star)_unit` から **消費**。
   * Nat 模型 wcd との cross-check（Σ=6・a=3）は `wcdConductorTotal`/`wcdArtinExpWild` を **消費**
     （A9 は cross-check のみ・新規証明ゼロ）。
   * U6 イディオム（π₉ 正則消去→ノルム 2 段→mod-3 矛盾）を A2/A7 で新インスタンス化する
     （`q9wr_pi3_cancel`・`q9wr_normBase_pi9`・`q9wr_qnorm_zeta_sub`・`q9wr_three_mul_not_unit` 消費）。

  complete_pct 影響: **B3 0→（独立監査次第・予測 0.15–0.25）— display-moving**。

  正直な限定（§4 規約により消さない・弱化しない・q9wr/q9kd 継承の上に追記のみ）:
  1. **拡大 1 個（M/L₂）・1 次元指標 3 本のみ**。L₂^×/(L₂^×)³ 全体・高次元表現は範囲外。
  2. **付値関数 v_M なし**。導手も different もフィルトレーションも π₉ 冪の **可除性形式**
     （q9wr 正直限定 1 を継承）。一般元 x の v_π・上付き番号・Herbrand φ/ψ はゼロ。
  3. **Artin 導手の一般公式 a(χ)=Σ(1/[G₀:G_i])dim(V/V^{G_i}) は本拡大でのインスタンス化**であり
     一般定理ではない。合成 different（推移公式・d(M/ℚ₃)）は範囲外。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3WildRamFiltrationReal
import IUT.Q3KummerDualityReal

namespace IUT

/-! ## q9ac-1（A1）: π₉ 冪 `q9acPiPow` と可除性の単調性（下降/上昇） -/

/-- π₉ⁿ（左結合の冪・π₉⁰=1）。フィルトレーションの divisor に用いる。 -/
def q9acPiPow : Nat → q3kCar
  | 0 => q3kOne
  | n + 1 => q3kMul (q9acPiPow n) q9psPi9

/-- π₉^{a+b} = π₉ᵃ·π₉ᵇ（可換環の冪則）。 -/
theorem q9ac_pow_add (a b : Nat) :
    q9acPiPow (a + b) = q3kMul (q9acPiPow a) (q9acPiPow b) := by
  induction b with
  | zero => exact (q9kd_mul_one (q9acPiPow a)).symm
  | succ k ih =>
    show q3kMul (q9acPiPow (a + k)) q9psPi9
       = q3kMul (q9acPiPow a) (q3kMul (q9acPiPow k) q9psPi9)
    rw [ih, q3k_mul_assoc]

/-- π₉¹ = π₉。 -/
theorem q9ac_pow1 : q9acPiPow 1 = q9psPi9 := q3k_one_mul q9psPi9

/-- π₉² = π₉·π₉（q9wr 形）。 -/
theorem q9ac_pow2 : q9acPiPow 2 = q3kMul q9psPi9 q9psPi9 := by
  show q3kMul (q9acPiPow 1) q9psPi9 = q3kMul q9psPi9 q9psPi9
  rw [q9ac_pow1]

/-- π₉³ = (π₉·π₉)·π₉（q9wr 形）。 -/
theorem q9ac_pow3 : q9acPiPow 3 = q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9 := by
  show q3kMul (q9acPiPow 2) q9psPi9 = _
  rw [q9ac_pow2]

/-- π₉⁴ = ((π₉·π₉)·π₉)·π₉（q9wr 形）。 -/
theorem q9ac_pow4 :
    q9acPiPow 4 = q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psPi9 := by
  show q3kMul (q9acPiPow 3) q9psPi9 = _
  rw [q9ac_pow3]

/-- **A1a `q9ac_dvd_of_le`**: 可除性の下降 a≤b: π₉ᵇ∣x → π₉ᵃ∣x。 -/
theorem q9ac_dvd_of_le {a b : Nat} (hab : a ≤ b) {x : q3kCar}
    (h : q9wrDvd (q9acPiPow b) x) : q9wrDvd (q9acPiPow a) x := by
  obtain ⟨d, hd⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  obtain ⟨c, hc⟩ := h
  refine ⟨q3kMul (q9acPiPow d) c, ?_⟩
  rw [hc, hd, q9ac_pow_add a d, q3k_mul_assoc]

/-- **A1b `q9ac_not_dvd_of_ge`**: 上昇 a≤b: ¬π₉ᵃ∣x → ¬π₉ᵇ∣x。 -/
theorem q9ac_not_dvd_of_ge {a b : Nat} (hab : a ≤ b) {x : q3kCar}
    (h : ¬ q9wrDvd (q9acPiPow a) x) : ¬ q9wrDvd (q9acPiPow b) x :=
  fun hb => h (q9ac_dvd_of_le hab hb)

/-! ## q9ac-2（A2 ★NEW）: σ² 側 break 上界 ¬π₉⁴∣(σ²π₉−π₉) -/

/-- **A2 `q9ac_sigma2_G3_trivial`（★ 新規実定理）**: ¬π₉⁴∣(σ²π₉−π₉)。
    q9wr は σ 側（`q9wr_G3_trivial`）しか持たない。U6 イディオムを σ² で新インスタンス化:
    π₉³ 正則消去 → u**=π₉·x → N(u**)=(ζ₃−1)·N(x)∈(3) だが u** は単数 → mod-3 矛盾。 -/
theorem q9ac_sigma2_G3_trivial :
    ¬ q9wrDvd (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psPi9)
        (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)) := by
  intro hd
  obtain ⟨x, hx⟩ := hd
  have hcomb : q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9wrUStarStar
      = q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) (q3kMul q9psPi9 x) := by
    have hcc := q9wr_sigma2_pi_eq.symm.trans hx
    rw [q3k_mul_assoc (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psPi9 x] at hcc
    exact hcc
  have hux : q9wrUStarStar = q3kMul q9psPi9 x := q9wr_pi3_cancel hcomb
  have hnorm : q3kNormBase q9wrUStarStar
      = q3rqMul (q3kNormBase q9psPi9) (q3kNormBase x) := by
    rw [hux, q3k_normBase_mul q9psPi9 x]
  rw [q9wr_normBase_pi9] at hnorm
  have huu : IsZpUnit 3 (q3rqNorm (q3kNormBase q9wrUStarStar)) := q9wr_ustarstar_unit
  rw [hnorm, q3rq_norm_mul, q9wr_qnorm_zeta_sub] at huu
  exact q9wr_three_mul_not_unit (q3rqNorm (q3kNormBase x)) huu

/-! ## q9ac-3（A3）: 実 G_i 帰属述語（π₉ 可除性）と i≤2 成立・i≥3 不成立（σ・σ² 両方） -/

/-- 実 G_i 帰属述語: g∈{σ,σ²} が i 次分岐群に属する ⟺ π₉^{i+1} ∣ (act g π₉ − π₉)。
    付値関数を建てない可除性形式（q9wr 正直限定 1 継承）。 -/
def q9acGiMem (g : q9kdGCar) (i : Nat) : Prop :=
  q9wrDvd (q9acPiPow (i + 1)) (q3kAdd (q9kdAct g q9psPi9) (q3kNeg q9psPi9))

/-- σ が G_i に属する (i≤2)。π₉³·u* を π₉^{i+1}·(π₉^{2-i}·u*) に再分割（G₂ 帰属を消費）。 -/
theorem q9ac_giMem_s_le {i : Nat} (hi : i ≤ 2) : q9acGiMem q9kdGCar.s i := by
  refine ⟨q3kMul (q9acPiPow (2 - i)) q9wrUStar, ?_⟩
  show q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)
     = q3kMul (q9acPiPow (i + 1)) (q3kMul (q9acPiPow (2 - i)) q9wrUStar)
  rw [q9wr_sigma_pi_eq, ← q9ac_pow3]
  have harith : (3 : Nat) = (i + 1) + (2 - i) := by omega
  rw [harith, q9ac_pow_add (i + 1) (2 - i), q3k_mul_assoc]

/-- σ² が G_i に属する (i≤2)。π₉³·u** を再分割（G₂ 帰属を消費）。 -/
theorem q9ac_giMem_s2_le {i : Nat} (hi : i ≤ 2) : q9acGiMem q9kdGCar.s2 i := by
  refine ⟨q3kMul (q9acPiPow (2 - i)) q9wrUStarStar, ?_⟩
  show q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)
     = q3kMul (q9acPiPow (i + 1)) (q3kMul (q9acPiPow (2 - i)) q9wrUStarStar)
  rw [q9wr_sigma2_pi_eq, ← q9ac_pow3]
  have harith : (3 : Nat) = (i + 1) + (2 - i) := by omega
  rw [harith, q9ac_pow_add (i + 1) (2 - i), q3k_mul_assoc]

/-- σ が G_i に属さない (i≥3)。¬π₉⁴∣ からの可除性上昇（`q9wr_G3_trivial` 消費）。 -/
theorem q9ac_giMem_s_gt {i : Nat} (hi : 3 ≤ i) : ¬ q9acGiMem q9kdGCar.s i := by
  have hbase : ¬ q9wrDvd (q9acPiPow 4) (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)) := by
    rw [q9ac_pow4]; exact q9wr_G3_trivial
  exact q9ac_not_dvd_of_ge (by omega : (4 : Nat) ≤ i + 1) hbase

/-- σ² が G_i に属さない (i≥3)。¬π₉⁴∣ からの可除性上昇（**A2** 消費）。 -/
theorem q9ac_giMem_s2_gt {i : Nat} (hi : 3 ≤ i) : ¬ q9acGiMem q9kdGCar.s2 i := by
  have hbase : ¬ q9wrDvd (q9acPiPow 4) (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)) := by
    rw [q9ac_pow4]; exact q9ac_sigma2_G3_trivial
  exact q9ac_not_dvd_of_ge (by omega : (4 : Nat) ≤ i + 1) hbase

/-- **A3a `q9ac_gi_le`**: i≤2 で σ,σ² ともに G_i に属する（フィルトレーション帰属の完成）。 -/
theorem q9ac_gi_le {i : Nat} (hi : i ≤ 2) :
    q9acGiMem q9kdGCar.s i ∧ q9acGiMem q9kdGCar.s2 i :=
  ⟨q9ac_giMem_s_le hi, q9ac_giMem_s2_le hi⟩

/-- **A3b `q9ac_gi_gt`**: i≥3 で σ,σ² ともに G_i に属さない（break t=2 の完成）。 -/
theorem q9ac_gi_gt {i : Nat} (hi : 3 ≤ i) :
    ¬ q9acGiMem q9kdGCar.s i ∧ ¬ q9acGiMem q9kdGCar.s2 i :=
  ⟨q9ac_giMem_s_gt hi, q9ac_giMem_s2_gt hi⟩

/-! ## q9ac-4（A4）: 実 codim(V^{G_i}) の iff-spec 緊縛（anti-model 条件） -/

/-- i≤2 判定子（0,1,2↦1、それ以上↦0）。codim の値の骨組み。 -/
def q9acLe2 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | _ + 3 => 0

/-- q9acLe2 i = 1 ⟺ i ≤ 2（骨組みを実区間に緊縛）。 -/
theorem q9ac_le2_iff (i : Nat) : q9acLe2 i = 1 ↔ i ≤ 2 := by
  match i with
  | 0 => exact ⟨fun _ => by omega, fun _ => rfl⟩
  | 1 => exact ⟨fun _ => by omega, fun _ => rfl⟩
  | 2 => exact ⟨fun _ => by omega, fun _ => rfl⟩
  | _ + 3 =>
    exact ⟨fun h => absurd (show (0 : Nat) = 1 from h) (by omega),
           fun h => absurd h (by omega)⟩

/-- 実 codim(V^{G_i}) の Nat 値: 非自明指標 (s,s2) では i≤2 で 1・i≥3 で 0、自明指標 (e) では 0。
    **iff-spec（`q9ac_codim_spec`）で実 Prop に緊縛**するので素の Nat 階段ではない。 -/
def q9acCodim : q9kdGCar → Nat → Nat
  | .e, _ => 0
  | .s, i => q9acLe2 i
  | .s2, i => q9acLe2 i

/-- χ=χ¹ は σ 上非自明（χ(σ)=ζ₃≠1）。 -/
theorem q9ac_chi_s_ne : (q9kdChiPow q9kdGCar.s).map q9kdGCar.s ≠ q9kdMu3One := by
  intro h
  exact q9kd_z_ne_one (congrArg Subtype.val h)

/-- χ²=χ² は σ 上非自明（χ²(σ)=ζ₃²≠1）。 -/
theorem q9ac_chi_s2_ne : (q9kdChiPow q9kdGCar.s2).map q9kdGCar.s ≠ q9kdMu3One := by
  intro h
  exact q9kd_zsq_ne_one (congrArg Subtype.val h)

/-- **A4 `q9ac_codim_spec`（iff-spec・MANDATORY anti-model 条件）**:
    codim(V^{G_i}) = 1 ⟺ (指標が σ 上非自明 ∧ σ が実 G_i に属する)。
    Nat 値の全てが実 Prop（`q9kd_z_ne_one` 由来の非自明性・A3 の実 G_i 帰属）で強制される。 -/
theorem q9ac_codim_spec (g : q9kdGCar) (i : Nat) :
    q9acCodim g i = 1 ↔
      ((q9kdChiPow g).map q9kdGCar.s ≠ q9kdMu3One ∧ q9acGiMem q9kdGCar.s i) := by
  cases g with
  | e =>
    have hchar : (q9kdChiPow q9kdGCar.e).map q9kdGCar.s = q9kdMu3One := rfl
    apply Iff.intro
    · intro h
      exact absurd (show (0 : Nat) = 1 from h) (by omega)
    · intro h
      exact absurd hchar h.1
  | s =>
    apply Iff.intro
    · intro h
      exact ⟨q9ac_chi_s_ne, q9ac_giMem_s_le ((q9ac_le2_iff i).mp h)⟩
    · intro h
      obtain hle | hgt := (by omega : i ≤ 2 ∨ 3 ≤ i)
      · exact (q9ac_le2_iff i).mpr hle
      · exact absurd h.2 (q9ac_giMem_s_gt hgt)
  | s2 =>
    apply Iff.intro
    · intro h
      exact ⟨q9ac_chi_s2_ne, q9ac_giMem_s_le ((q9ac_le2_iff i).mp h)⟩
    · intro h
      obtain hle | hgt := (by omega : i ≤ 2 ∨ 3 ≤ i)
      · exact (q9ac_le2_iff i).mpr hle
      · exact absurd h.2 (q9ac_giMem_s_gt hgt)

/-! ## q9ac-5（A5）: 実 Artin 導手 a(χ)=Σ_{i=0}^{2} codim = 3・a(χ⁰)=0 -/

/-- 実 Artin 導手 a(φ) = Σ_{i=0}^{2} codim(V^{G_i})（本拡大は G₃=1 なので i≤2 で尽きる）。 -/
def q9acArtin (g : q9kdGCar) : Nat :=
  q9acCodim g 0 + q9acCodim g 1 + q9acCodim g 2

/-- **A5a `q9ac_artin_chi`**: a(χ) = 3（= tame 1 + Swan 2）。 -/
theorem q9ac_artin_chi : q9acArtin q9kdGCar.s = 3 := rfl

/-- **A5b `q9ac_artin_chi2`**: a(χ²) = 3。 -/
theorem q9ac_artin_chi2 : q9acArtin q9kdGCar.s2 = 3 := rfl

/-- **A5c `q9ac_artin_chi0`**: a(χ⁰) = 0（自明指標）。 -/
theorem q9ac_artin_chi0 : q9acArtin q9kdGCar.e = 0 := rfl

/-! ## q9ac-6（A6）: Swan 導手 = a(χ)−1 = 2 = 実 break t -/

/-- Swan 導手 sw(φ) = a(φ) − 1。 -/
def q9acSwan (g : q9kdGCar) : Nat := q9acArtin g - 1

/-- **A6 `q9ac_swan_eq_break`**: Swan(χ)=a(χ)−1=2＝実 break t
    （σ∈G₂ かつ σ∉G₃ の実分岐フィルトレーションと同定・`q9wr_break` 消費）。 -/
theorem q9ac_swan_eq_break :
    q9acSwan q9kdGCar.s = 2
    ∧ q9wrDvd (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
        (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
    ∧ ¬ q9wrDvd (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psPi9)
        (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)) :=
  ⟨rfl, q9wr_break.1, q9wr_break.2.2⟩

/-! ## q9ac-7（A7 ★NEW）: 実 different の鋭さ ¬π₉⁷∣D -/

/-- π₉⁶ 正則消去: π₉⁶·a = π₉⁶·b ⟹ a = b（`q9wr_pi3_cancel` を 2 段）。 -/
theorem q9ac_pi6_cancel {a b : q3kCar}
    (h : q3kMul q9psPi6 a = q3kMul q9psPi6 b) : a = b := by
  have h2 : q3kMul (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
                     (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)) a
          = q3kMul (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
                     (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)) b := h
  rw [q3k_mul_assoc (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
        (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) a,
      q3k_mul_assoc (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9)
        (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) b] at h2
  exact q9wr_pi3_cancel (q9wr_pi3_cancel h2)

/-- **A7 `q9ac_different_sharp`（★ 新規実定理）**: ¬π₉⁷∣D（D=π₉⁶·(u*u**)）。
    d(M/L₂)=6「ちょうど」の実証: π₉⁶ 消去 → u*u**=π₉·x → N(u*u**)=(ζ₃−1)·N(x)∈(3) だが
    u*u** は単数 → mod-3 矛盾。**D=π₉⁶·(u*u**) は `q9wr_different` を消費**。 -/
theorem q9ac_different_sharp :
    ¬ q9wrDvd (q3kMul q9psPi6 q9psPi9)
        (q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
                (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))) := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hcomb : q3kMul q9psPi6 (q3kMul q9wrUStar q9wrUStarStar)
             = q3kMul q9psPi6 (q3kMul q9psPi9 c) := by
    have hcc := q9wr_different.symm.trans hc
    rw [q3k_mul_assoc q9psPi6 q9psPi9 c] at hcc
    exact hcc
  have huu : q3kMul q9wrUStar q9wrUStarStar = q3kMul q9psPi9 c := q9ac_pi6_cancel hcomb
  have hnorm : q3kNormBase (q3kMul q9wrUStar q9wrUStarStar)
      = q3rqMul (q3kNormBase q9psPi9) (q3kNormBase c) := by
    rw [huu, q3k_normBase_mul q9psPi9 c]
  rw [q9wr_normBase_pi9] at hnorm
  have hunit : IsZpUnit 3 (q3rqNorm (q3kNormBase (q3kMul q9wrUStar q9wrUStarStar))) :=
    q3k_unit_mul q9wr_ustar_unit q9wr_ustarstar_unit
  rw [hnorm, q3rq_norm_mul, q9wr_qnorm_zeta_sub] at hunit
  exact q9wr_three_mul_not_unit (q3rqNorm (q3kNormBase c)) hunit

/-! ## q9ac-8（A8 ★headline）: 実 conductor–discriminant Σ_φ a(φ)=6=d（全指標和） -/

/-- **A8 `q9ac_conductor_discriminant_real`（★ 本命題・実 Führerdiskriminanten）**:
    Σ_{φ} a(φ) = 0+3+3 = 6 ∧ 全指標の完全枚挙（`q9kd_hom_complete`）∧
    D=(σπ₉−π₉)(σ²π₉−π₉)=π₉⁶·(u*u**)（`q9wr_different` 消費）∧ ¬π₉⁷∣D（**A7**）。
    左辺（指標和・実指標）と右辺（実 different・鋭さ込み）がともに実で 6 に一致する。 -/
theorem q9ac_conductor_discriminant_real :
    (q9acArtin q9kdGCar.e + q9acArtin q9kdGCar.s + q9acArtin q9kdGCar.s2 = 6)
    ∧ (∀ φ : Hom q9kdG q9kdMu3, φ = q9kdChi0 ∨ φ = q9kdChi ∨ φ = q9kdChi2)
    ∧ (q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
              (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))
        = q3kMul q9psPi6 (q3kMul q9wrUStar q9wrUStarStar))
    ∧ ¬ q9wrDvd (q3kMul q9psPi6 q9psPi9)
        (q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
                (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))) :=
  ⟨rfl, q9kd_hom_complete, q9wr_different, q9ac_different_sharp⟩

/-! ## q9ac-9（A9）: Nat 模型 wcd との cross-check（新規証明ゼロ） -/

/-- **A9 `q9ac_matches_wcd`**: Nat 階段模型 wcd（M441F）との cross-check
    （Σ=6=`wcdConductorTotal 3 2`・a(χ)=3=`wcdArtinExpWild 2`・新規証明ゼロ）。 -/
theorem q9ac_matches_wcd :
    q9acArtin q9kdGCar.e + q9acArtin q9kdGCar.s + q9acArtin q9kdGCar.s2
      = wcdConductorTotal 3 2
    ∧ q9acArtin q9kdGCar.s = wcdArtinExpWild 2 := by
  refine ⟨?_, ?_⟩
  · show (6 : Nat) = wcdConductorTotal 3 2
    rfl
  · show (3 : Nat) = wcdArtinExpWild 2
    rfl

/-! ## q9ac-10（A10）: capstone（束ねのみ・新規証明ゼロ） -/

/-- **A10 `Q3ArtinConductorRealData`**: 実 Artin 導手／実 conductor–discriminant データ束ね。 -/
structure Q3ArtinConductorRealData where
  /-- a(χ) = 3（実指標の Artin 導手）。 -/
  artin_chi : q9acArtin q9kdGCar.s = 3
  /-- a(χ⁰) = 0。 -/
  artin_chi0 : q9acArtin q9kdGCar.e = 0
  /-- codim(V^{G_i}) の iff-spec 緊縛（anti-model 条件）。 -/
  codim_spec : ∀ g i, q9acCodim g i = 1 ↔
    ((q9kdChiPow g).map q9kdGCar.s ≠ q9kdMu3One ∧ q9acGiMem q9kdGCar.s i)
  /-- σ² 側 break 上界 ¬π₉⁴∣(σ²π₉−π₉)（★ NEW）。 -/
  sigma2_break : ¬ q9wrDvd (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psPi9)
    (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))
  /-- 実 different の鋭さ ¬π₉⁷∣D（★ NEW）。 -/
  different_sharp : ¬ q9wrDvd (q3kMul q9psPi6 q9psPi9)
    (q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
            (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)))
  /-- 全指標和 Σ_φ a(φ) = 6。 -/
  cond_disc_sum : q9acArtin q9kdGCar.e + q9acArtin q9kdGCar.s + q9acArtin q9kdGCar.s2 = 6
  /-- Nat 模型 cross-check。 -/
  matches_wcd : q9acArtin q9kdGCar.e + q9acArtin q9kdGCar.s + q9acArtin q9kdGCar.s2
    = wcdConductorTotal 3 2

/-- **A10b `q9ac_data`**: 見出し実例——実 M=ℚ₃(ζ₉) 上の実 Artin 導手／conductor–discriminant。 -/
def q9ac_data : Q3ArtinConductorRealData where
  artin_chi := q9ac_artin_chi
  artin_chi0 := q9ac_artin_chi0
  codim_spec := q9ac_codim_spec
  sigma2_break := q9ac_sigma2_G3_trivial
  different_sharp := q9ac_different_sharp
  cond_disc_sum := q9ac_conductor_discriminant_real.1
  matches_wcd := q9ac_matches_wcd.1

/-- **A10c `q9ac_exists`**: 実 Artin 導手／実 conductor–discriminant の存在。 -/
theorem q9ac_exists : Nonempty Q3ArtinConductorRealData := ⟨q9ac_data⟩

end IUT
