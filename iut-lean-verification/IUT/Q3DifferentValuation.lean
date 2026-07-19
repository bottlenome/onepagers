/-
  IUT/Q3DifferentValuation.lean — 柱B・B3 実 different の付値値化 d(M/L₂)=v_M(D)=6
    （可除性形式 d=6（π₉⁶∣D ∧ ¬π₉⁷∣D）を、実 v_M 付値関数上の DEFINED 値 v_M(D)=6 へ昇格）

  ── 主要成果の分類: **[実／(a) 昇格]** — q9tw/q9ac が **可除性形式**（π₉⁶∣D ∧ ¬π₉⁷∣D）で
     持っていた実 different の指数 d(M/L₂)=6 を、`Q3ValuationReal` で建てた **実 v_M 付値関数**
     q9vVal（一様化子冪部分モノイド {π₉ⁿ·u} 上の忠実な付値）の上で **v_M(D)=6 という
     DEFINED な付値値** へ昇格する。q9v が名指した B3 hook（"the cheapest real B3 gain"）を実現し、
     q9v を「B3 の足場」から「genuine な小 B3 増分」へ変える。主語は実 different 生成元
     D=(σπ₉−π₉)(σ²π₉−π₉)（実 σ・実 π₉・実単数 u*·u**）——toy 模型を一切使わない。

  complete_pct 影響: **B3 0.27→（独立監査次第・予測 +0.01〜0.03・different を付値値化）**。
     動かす新規内容は「different D が付値部分モノイドの元であり、その v_M 値が **ちょうど 6**」
     という DEFINED value（q9dv_val_different）——従来の 2 本の可除性言明
     （π₉⁶∣D ∧ ¬π₉⁷∣D）を単一の付値等式 v_M(D)=6 に retire し、q9v_dvd_iff ブリッジ経由で
     両可除性を v_M(D)=6 から **導出**して見せる（q9dv_different_sharp_from_val が q9ac 形の
     ¬π₉⁷∣D を付値値から再導出）。

  核心の実データ:
   * q9dvDifferent — different 生成元 D を付値部分モノイド元 ⟨exp=6, unit=u*·u**⟩ として実現
   * q9dv_different_elt — その実元が実 different D=(σπ₉−π₉)(σ²π₉−π₉) と一致（q9wr_different 消費）
   * q9dv_val_different : v_M(D)=6（★ d(M/L₂) の DEFINED 付値値化）
   * q9dv_val_pinned — v_M は実元 D にのみ依存（q9v_wellDef 経由・vacuous rfl でない証拠）
   * q9dv_different_sharp_from_val — v_M(D)=6 ⟹ ¬π₉⁷∣D（q9ac_different_sharp を付値から再導出）
   * q9dv_different_defined — v(D)=6 ∧ 実元が real different（束ね）

  正直な限定（§4 規約により消さない・弱めない・q9v/q9wr/q9tw/q9ac 継承の上に追記のみ）:
  1. **これは唯一の different 生成元 D（部分モノイド元）上の d(M/L₂)=6 という値**。
     抽象 different イデアル論・一般 v_M（TOTAL な付値関数）は建てない——q9v 正直限定
     （一様化子冪部分モノイド {π₉ⁿ·u} 上の忠実な関数に限る・total 化は choice/排中律断片を要する）を継承。
  2. **拡大 1 個（M/L₂）・下付き付値のみ**。合成 different（推移公式・d(M/ℚ₃)=9）・
     上付き番号・Herbrand・実 Hasse–Arf は範囲外——q9wr/q9tw/q9ac の継承限定。
  3. v_M(D)=6 は **q9v の付値関数**（部分モノイド上）と **q9wr の実 different 恒等式**
     （D=π₉⁶·(u*·u**)）の合成であり、その双方の正直限定を継承する。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3ValuationReal
import IUT.Q3ArtinConductorReal

namespace IUT

/-! ## q9dv-1: different 生成元 D を付値部分モノイド元として実現 -/

/-- **q9dv-1（★）: 実 different 生成元 D の付値部分モノイド表現** ⟨exp=6, unit=u*·u**⟩。
    q9wr_different の D=π₉⁶·(u*·u**) を、q9v の一様化子冪部分モノイド {π₉ⁿ·u} の元として実現する
    （指数 6・単数因子 u*·u**・その単数性は q3k_unit_mul で確保）。 -/
def q9dvDifferent : q9vUnif where
  exp := 6
  unit := q3kMul q9wrUStar q9wrUStarStar
  isUnit := q3k_unit_mul q9wr_ustar_unit q9wr_ustarstar_unit

/-! ## q9dv-2: 付値部分モノイド元の実元が実 different D と一致 -/

/-- **q9dv-2（★）: q9dvDifferent の実元は real different D=(σπ₉−π₉)(σ²π₉−π₉)**。
    q9vElt ⟨6, u*·u**⟩ = π₉⁶·(u*·u**)（定義）で、q9nf_pipow6_eq（π₉⁶ の一様化子冪 = q9psPi6）を
    経て q9wr_different（D=π₉⁶·(u*·u**)）と一致する。付値の主語が toy でなく実 different である証拠。 -/
theorem q9dv_different_elt :
    q9vElt q9dvDifferent
      = q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
               (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)) := by
  show q3kMul (q9nfPiPow 6) (q3kMul q9wrUStar q9wrUStarStar)
     = q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
              (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))
  rw [q9nf_pipow6_eq]
  exact q9wr_different.symm

/-! ## q9dv-3: ★ d(M/L₂) = v_M(D) = 6（DEFINED な付値値） -/

/-- **q9dv-3（★ headline）: d(M/L₂) = v_M(D) = 6**。
    実 different 生成元 D の実 v_M 付値値が **ちょうど 6**——q9tw/q9ac の可除性形式
    d=6（π₉⁶∣D ∧ ¬π₉⁷∣D）を、付値関数上の単一の DEFINED value へ昇格する。
    exp 射影で rfl だが、q9dv_different_elt により実元が real different に緊縛されているので
    vacuous でない（下記 q9dv_val_pinned が well-defined 性で実元依存を明示）。 -/
theorem q9dv_val_different : q9vVal q9dvDifferent = 6 := rfl

/-- **q9dv-3b（★ well-defined 緊縛）: 実元 D で v_M=6 は分解に依らない**。
    q9vElt y = D なる任意の部分モノイド元 y の付値は 6——q9v_wellDef により付値は
    実元 D にのみ依存する。q9dv_val_different が「一つの分解の rfl」でなく
    「実 different D の付値値そのもの」であることの証拠（vacuous rfl でない）。 -/
theorem q9dv_val_pinned (y : q9vUnif)
    (hy : q9vElt y
        = q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
                 (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))) :
    q9vVal y = 6 := by
  have h : q9vElt y = q9vElt q9dvDifferent := by rw [hy, q9dv_different_elt]
  have hval : q9vVal y = q9vVal q9dvDifferent := q9v_wellDef y q9dvDifferent h
  rw [hval]
  exact q9dv_val_different

/-! ## q9dv-4: 付値値 6 から可除性形式（π₉⁶∣D ∧ ¬π₉⁷∣D）を再導出（★ 昇格の実証） -/

/-- π₉⁷ = π₉⁶·π₉ の一様化子冪橋渡し（q9nf_pipow_add 6 1 経由）。 -/
theorem q9dv_pipow7_eq : q9nfPiPow 7 = q3kMul q9psPi6 q9psPi9 := by
  have h : q9nfPiPow 7 = q3kMul (q9nfPiPow 6) (q9nfPiPow 1) := q9nf_pipow_add 6 1
  rw [q9nf_pipow6_eq, q9nf_pipow1_eq] at h
  exact h

/-- **q9dv-4a: v_M(D)=6 ⟹ π₉⁶ ∣ D**（下界を付値値から回収・q9v_dvd_iff ⟸）。 -/
theorem q9dv_pi6_dvd_different : q9wrDvd (q9nfPiPow 6) (q9vElt q9dvDifferent) :=
  (q9v_dvd_iff q9dvDifferent 6).mpr (Nat.le_refl 6)

/-- **q9dv-4b: v_M(D)=6 ⟹ ¬π₉⁷ ∣ D**（上界を付値値から回収・q9v_dvd_iff ⟹ + omega）。 -/
theorem q9dv_pi7_not_dvd_different : ¬ q9wrDvd (q9nfPiPow 7) (q9vElt q9dvDifferent) := by
  intro h7
  have hle : (7 : Nat) ≤ q9vVal q9dvDifferent := (q9v_dvd_iff q9dvDifferent 7).mp h7
  rw [q9dv_val_different] at hle
  omega

/-- **q9dv-4c（★ 昇格の実証）: v_M(D)=6 から q9ac 形の鋭さ ¬π₉⁷∣D を再導出**。
    q9ac_different_sharp（¬ q9wrDvd (π₉⁶·π₉) D）と **同一命題**を、独立した divisibility の
    ノルム計算からではなく **付値値 v_M(D)=6 から** 導く——d=6 の可除性 2 本が単一の付値値に
    retire され、そこから復元されることの実証（cross-check として q9ac_different_sharp と整合）。 -/
theorem q9dv_different_sharp_from_val :
    ¬ q9wrDvd (q3kMul q9psPi6 q9psPi9)
        (q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
                (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))) := by
  rw [← q9dv_pipow7_eq, ← q9dv_different_elt]
  exact q9dv_pi7_not_dvd_different

/-! ## q9dv-5: 束ね v(D)=6 ∧ 実元が real different -/

/-- **q9dv-5（★）: v_M(D)=6 ∧ 実元が real different**——q9tw/q9ac の可除性形式 d=6 の
    exact 付値値化を単一命題に束ねる（付値値 + 実元同定 + 可除性 2 本の付値からの復元）。 -/
theorem q9dv_different_defined :
    q9vVal q9dvDifferent = 6
    ∧ q9vElt q9dvDifferent
        = q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
                 (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))
    ∧ q9wrDvd (q9nfPiPow 6) (q9vElt q9dvDifferent)
    ∧ ¬ q9wrDvd (q9nfPiPow 7) (q9vElt q9dvDifferent) :=
  ⟨q9dv_val_different, q9dv_different_elt,
   q9dv_pi6_dvd_different, q9dv_pi7_not_dvd_different⟩

/-! ## q9dv-6: capstone（束ねのみ・新規証明ゼロ） -/

/-- **q9dv-6: 実 different 付値値データ**——d(M/L₂)=v_M(D)=6 の DEFINED 付値値・実元同定・
    可除性 2 本の付値からの復元・q9ac 形鋭さの付値からの再導出を束ねる（新規証明ゼロ）。 -/
structure Q3DifferentValuationData where
  /-- 実元が real different D=(σπ₉−π₉)(σ²π₉−π₉)。 -/
  different_elt : q9vElt q9dvDifferent
    = q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
             (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))
  /-- d(M/L₂) = v_M(D) = 6（★ DEFINED 付値値）。 -/
  val_different : q9vVal q9dvDifferent = 6
  /-- v_M は実元 D にのみ依存（well-defined 緊縛・vacuous rfl でない）。 -/
  val_pinned : ∀ y : q9vUnif,
    q9vElt y = q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
                      (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))
    → q9vVal y = 6
  /-- π₉⁶ ∣ D（下界を付値値から回収）。 -/
  pi6_dvd : q9wrDvd (q9nfPiPow 6) (q9vElt q9dvDifferent)
  /-- ¬π₉⁷ ∣ D（上界を付値値から回収）。 -/
  pi7_not_dvd : ¬ q9wrDvd (q9nfPiPow 7) (q9vElt q9dvDifferent)
  /-- q9ac 形の鋭さ ¬π₉⁷∣D を付値値から再導出（昇格の実証）。 -/
  sharp_from_val : ¬ q9wrDvd (q3kMul q9psPi6 q9psPi9)
    (q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
            (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)))

/-- **見出し実例** — 実 different D の DEFINED 付値値 d(M/L₂)=v_M(D)=6。 -/
def q9dv_data : Q3DifferentValuationData where
  different_elt := q9dv_different_elt
  val_different := q9dv_val_different
  val_pinned := q9dv_val_pinned
  pi6_dvd := q9dv_pi6_dvd_different
  pi7_not_dvd := q9dv_pi7_not_dvd_different
  sharp_from_val := q9dv_different_sharp_from_val

/-- **実 different 付値値データの存在**（d(M/L₂)=v_M(D)=6 を DEFINED value として）。 -/
theorem q9dv_exists : Nonempty Q3DifferentValuationData := ⟨q9dv_data⟩

end IUT
