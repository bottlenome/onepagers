/-
  IUT/Q3CubeQuotientReal.lean — 実局所体の立方剰余群 L₂^×/(L₂^×)³ の rank≥2 下界（B6）
    L₂^× = q3rqLx = ℤ×U₂ 上の部分群 ⟨[λ],[ζ₃]⟩ ≅ (ℤ/3)²（一様化子 λ ＋ 円分 ζ₃）

  ── 主要成果の分類: **[実／(a) 昇格]** — q9kd の単一クラス ⟨[ζ₃]⟩（rank≥1）を、
     実群提示 L₂^× = ℤ×U₂ 上の ⟨[λ],[ζ₃]⟩（rank≥2）へ昇格する。主対象は実
     q3rqLx = prodGrp intGrp q3rqU（付値部 ℤ × 単数群 U₂ = O_{L₂}^×）——toy 主語なし
     （m202fVol 型・Bool 軌道・surrogate 群を一切使わない）。NEW content は
     (1) 一様化子クラス [λ] の非立方性（付値論法・3∤1）と、
     (2) [λ] と [ζ₃] の 𝔽₃-独立性（8 個の非自明結合が全て非立方）。

  complete_pct 影響: **B6 0.15→（監査次第・予測 0.20 → 表示 26→27）**。named gap
  「L₂^×/(L₂^×)³ の全体構造は未計算（⟨[ζ₃]⟩ 部分のみ）」を rank≥1 → rank≥2
  （4 のうち 2 次元）へ部分前進させる。full rank 4 は未達（据置）。
  **消費（再主張しない）**:
   * ζ₃ の O_{L₂} 内 3 乗根非存在は `q9ci_no_cbrt_zeta`（柱A）から **消費**。
   * ζ₃² の 3 乗根非存在は `q9ci_no_cbrt_zetaSq`（柱A）から **消費**。
   * [ζ₃] 群提示上の非立方性は `q9kd_class_nontrivial`（B6・q9kd）から **消費**。
  本モジュールの真水（新規主張）は **付値方向 [λ] の非立方性 ＋ [λ]/[ζ₃] の
  𝔽₃-独立性の組み立てのみ**（非立方性の核は既存を消費）。

  内容（§3.1 q9cq-1..q9cq-9）:
   * q9cq-1 q9cq_cube_fst        — g³ の第1成分 = 3·g.1（prodGrp/intGrp 成分立方）
   * q9cq-2 q9cq_lambdaClass     — [λ] := (1, e_U)（一様化子クラス・付値 1）
   * q9cq-3 q9cq_lambda_nontrivial — ¬∃g, g³=[λ]（付値 3∤1・**新規**）
   * q9cq-4 q9cq_zetaClass       — [ζ₃] := (0, ⟨ζ₃,·⟩)（q9kd と同一クラス）
   * q9cq-5 q9cq_val_nontrivial  — i∉3ℤ で ¬∃g, g³=(i,u)（任意 u・付値・**新規**）
   * q9cq-6 q9cq_zeta_noncube / q9cq_zetaSq_noncube — (0,ζ₃),(0,ζ₃²) 非立方（q9kd/q9ci 消費）
   * q9cq-7 q9cq_lambda_zeta_indep — 8 個の (i,ζ₃^j)≠(0,e) が全非立方（**新規・組立**）
   * q9cq-8 q9cq_rank_ge_two     — ⟨[λ],[ζ₃]⟩ ≅ (ℤ/3)²（honest 下界形・capstone）
   * q9cq-9 Q3CubeQuotientData / q9cq_data / q9cq_exists — データ束ね

  named target（**定理化しない・コメントのみ**・§3.2 正直な限定 1）:
    L₂^×/(L₂^×)³ ≅ (ℤ/3)⁴（rank 4・|quotient|=81=3⁴）。分解 1(λ)+0(μ₂)+1(μ₃)+2(主単数 ℤ₃²)
    と局所体公式 [L₂^×:(L₂^×)³]=3·|μ₃|/|3|_{L₂}=3·3/(1/9)=81 が一致（audit §1.3）。
    残り 2 次元（主単数 1+m≅ℤ₃²）と上界 exhaustion（高々 rank 4）は主単数フィルトレーション
    U^(i)・v_M・graded 判別器を要す 2〜3 ラウンド案件（B2 監査 §1.3／q3rq 限定 4 継承）。

  正直な限定（§4 規約により消さない・弱化しない・q3rq/q9kd 継承の上に追記のみ）:
  1. **rank ≥ 2 下界のみ**。full rank 4（(ℤ/3)⁴）は未計算——主単数 1+m≅ℤ₃² の 2 次元と
     上界 exhaustion は未達（上記 named target 参照・据置）。
  2. **非立方性の核は消費**。ζ₃・ζ₃² の非3乗は q9ci、[ζ₃] 群提示非立方は q9kd を消費
     （本モジュール新規は付値方向 [λ] と独立性の組み立てのみ）。
  3. **商群オブジェクトは建てない**。「¬∃ g, g³=x」の非立方性述語形（q9kd 準拠）で下界を
     述べる。μ₂ 部分が自明（−1 は立方）である事実も定理化せず註記のみ。
  4. q3rq/q9kd の恒久限定（O_L と L^× のみ・体化なし・Galois σ 超えゼロ・実テータ/π₁ ゼロ・
     tmzLimit 橋なし・兄弟担体・n=3・体 L₂ 1 個）を継承。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3KummerDualityReal
import IUT.Q3KummerCubeIdent

namespace IUT

/-! ## q9cq-1: 群冪の第1成分（付値）— g³ の第1成分 = 3·g.1 -/

/-- **q9cq-1 `q9cq_cube_fst`**: g³ = q3rqLx.mul (q3rqLx.mul g g) g の第1成分は
    3·g.1（prodGrp/intGrp の成分ごと立方——第1成分は intGrp の加法で n+n+n=3n）。 -/
theorem q9cq_cube_fst (g : q3rqLx.carrier) :
    (q3rqLx.mul (q3rqLx.mul g g) g).1 = 3 * g.1 := by
  have key : ∀ n : Int, (n + n) + n = 3 * n := by intro n; omega
  exact key g.1

/-! ## q9cq-2: 一様化子クラス [λ] = (1, e_U) -/

/-- **q9cq-2 `q9cq_lambdaClass`**: [λ] := (1, e_U)。第1成分（λ-付値）1・単数部は
    U₂ の単位元 e_U = q3rqU.one。注意: q3rqLambda=(0,1) は単数でない（N=3∉ℤ₃^×）ので
    U₂ の元ではなく、L₂^× では付値 1 の元＝群提示第1成分 1 で表される。 -/
def q9cq_lambdaClass : q3rqLx.carrier := ((1 : Int), q3rqU.one)

/-! ## q9cq-3: [λ] の非立方性（付値 3∤1・新規） -/

/-- **q9cq-3 `q9cq_lambda_nontrivial`**: [λ] は非立方——¬∃g, g³=[λ]。
    g³ の第1成分 = 3·g.1 = 1 ⟹ 3∣1 ⟹ 矛盾（omega）。付値方向の**新規**内容
    （q9kd は付値方向を一切持たない）。 -/
theorem q9cq_lambda_nontrivial :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = q9cq_lambdaClass := by
  intro hex
  obtain ⟨g, hg⟩ := hex
  have h1 : (q3rqLx.mul (q3rqLx.mul g g) g).1 = q9cq_lambdaClass.1 := congrArg Prod.fst hg
  rw [q9cq_cube_fst g] at h1
  -- h1 : 3 * g.1 = 1（付値 3∤1）
  have key : ∀ n : Int, 3 * n = 1 → False := by intro n hn; omega
  exact key g.1 h1

/-! ## q9cq-4: 円分クラス [ζ₃] = (0, ⟨ζ₃,·⟩)（q9kd と同一） -/

/-- U₂ の元としての ζ₃。 -/
def q9cq_zetaUnit : q3rqU.carrier := ⟨q3rqZeta, q3rq_zeta_unit⟩

/-- ζ₃² は単数（ζ₃·ζ₃ が単数）。 -/
theorem q9cq_zetaSq_unit : q3rqUnitMem q3rqZetaSq :=
  q3rq_unit_mul q3rq_zeta_unit q3rq_zeta_unit

/-- U₂ の元としての ζ₃²。 -/
def q9cq_zetaSqUnit : q3rqU.carrier := ⟨q3rqZetaSq, q9cq_zetaSq_unit⟩

/-- **q9cq-4 `q9cq_zetaClass`**: [ζ₃] := (0, ⟨ζ₃,·⟩)（q9kd の Kummer 類と同一）。 -/
def q9cq_zetaClass : q3rqLx.carrier := ((0 : Int), q9cq_zetaUnit)

/-- [ζ₃²] := (0, ⟨ζ₃²,·⟩)。 -/
def q9cq_zetaSqClass : q3rqLx.carrier := ((0 : Int), q9cq_zetaSqUnit)

/-! ## q9cq-5: 付値非立方（i∉3ℤ で (i,u) は任意単数 u で非立方・新規） -/

/-- **q9cq-5 `q9cq_val_nontrivial`**: 3∤i なら ¬∃g, g³=(i,u)（任意 u : U₂）。
    第1成分 3·g.1 = i ⟹ 3∣i ⟹ 矛盾。付値方向の**新規**内容（第2成分 u に無関係）。 -/
theorem q9cq_val_nontrivial (i : Int) (hi : ¬ (3 : Int) ∣ i) (u : q3rqU.carrier) :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((i : Int), u) := by
  intro hex
  obtain ⟨g, hg⟩ := hex
  have h1 : (q3rqLx.mul (q3rqLx.mul g g) g).1 = i := congrArg Prod.fst hg
  rw [q9cq_cube_fst g] at h1
  -- h1 : 3 * g.1 = i ⟹ 3∣i、矛盾
  have key : ∀ n : Int, 3 * n = i → False := by
    intro n hn
    exact hi ⟨n, hn.symm⟩
  exact key g.1 h1

/-- i=1 の付値非立方（3∤1）。 -/
theorem q9cq_val1_noncube (u : q3rqU.carrier) :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((1 : Int), u) :=
  q9cq_val_nontrivial 1 (by omega) u

/-- i=2 の付値非立方（3∤2）。 -/
theorem q9cq_val2_noncube (u : q3rqU.carrier) :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((2 : Int), u) :=
  q9cq_val_nontrivial 2 (by omega) u

/-! ## q9cq-6: ζ₃・ζ₃² の非立方（q9kd/q9ci 消費・第2成分へ射影） -/

/-- **q9cq-6a `q9cq_zeta_noncube`**: (0,ζ₃) は非立方。**`q9kd_class_nontrivial`
    （B6・q9kd）を消費**——同一クラスの群提示非立方性を再証明しない。 -/
theorem q9cq_zeta_noncube :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = q9cq_zetaClass :=
  q9kd_class_nontrivial

/-- **q9cq-6b `q9cq_zetaSq_noncube`**: (0,ζ₃²) は非立方。第2成分（単数部）へ射影し
    **`q9ci_no_cbrt_zetaSq`（柱A）を消費**——第1成分 0=3·g.1 は制約せず、単数部
    u³=ζ₃² が q9ci に矛盾。 -/
theorem q9cq_zetaSq_noncube :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = q9cq_zetaSqClass := by
  intro hex
  obtain ⟨g, hg⟩ := hex
  have h2 : (q3rqLx.mul (q3rqLx.mul g g) g).2
      = (⟨q3rqZetaSq, q9cq_zetaSq_unit⟩ : q3rqU.carrier) := congrArg Prod.snd hg
  have hval : q3rqMul (q3rqMul g.2.val g.2.val) g.2.val = q3rqZetaSq :=
    congrArg Subtype.val h2
  exact q9ci_no_cbrt_zetaSq g.2.val hval

/-! ## q9cq-7: [λ]/[ζ₃] の 𝔽₃-独立性（8 個の非自明結合が全非立方・新規・組立） -/

/-- 8 個の非自明結合 [λ]^i·[ζ₃]^j = (i, ζ₃^j)（i,j∈{0,1,2}, (i,j)≠(0,0)）が
    全て非立方であることの命題（＝(ℤ/3)²↪立方剰余群 の単射性 ＝ rank≥2 下界）。 -/
def Q9cqIndep : Prop :=
  (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((1 : Int), q3rqU.one))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((2 : Int), q3rqU.one))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((0 : Int), q9cq_zetaUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((1 : Int), q9cq_zetaUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((2 : Int), q9cq_zetaUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((0 : Int), q9cq_zetaSqUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((1 : Int), q9cq_zetaSqUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((2 : Int), q9cq_zetaSqUnit))

/-- **q9cq-7 `q9cq_lambda_zeta_indep`**: [λ] と [ζ₃] は立方剰余群内で 𝔽₃-独立
    ——8 個の非自明結合 (i,ζ₃^j) が全て非立方。i≠0（j 任意）は付値 q9cq-5 で、
    i=0,j∈{1,2} は q9cq-6（q9kd/q9ci 消費）で処理する**新規の組み立て**。 -/
theorem q9cq_lambda_zeta_indep : Q9cqIndep :=
  ⟨q9cq_val1_noncube q3rqU.one,
   q9cq_val2_noncube q3rqU.one,
   q9cq_zeta_noncube,
   q9cq_val1_noncube q9cq_zetaUnit,
   q9cq_val2_noncube q9cq_zetaUnit,
   q9cq_zetaSq_noncube,
   q9cq_val1_noncube q9cq_zetaSqUnit,
   q9cq_val2_noncube q9cq_zetaSqUnit⟩

/-! ## q9cq-8: rank≥2 下界（⟨[λ],[ζ₃]⟩ ≅ (ℤ/3)²・honest 下界形・capstone） -/

/-- **q9cq-8 `q9cq_rank_ge_two`**: ⟨[λ],[ζ₃]⟩ ≅ (ℤ/3)² の honest 下界形。
    [λ] 単独の非立方性（q9cq-3）と 8 結合の 𝔽₃-独立性（q9cq-7）を束ね、
    (ℤ/3)² が実立方剰余群 L₂^×/(L₂^×)³ = q3rqLx/(q3rqLx)³ へ単射することを述べる。
    **full rank 4 は主張しない**（ヘッダ named target 参照）。 -/
theorem q9cq_rank_ge_two :
    (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = q9cq_lambdaClass)
    ∧ Q9cqIndep :=
  ⟨q9cq_lambda_nontrivial, q9cq_lambda_zeta_indep⟩

/-! ## q9cq-9: capstone（データ束ね・新規証明ゼロ） -/

/-- **q9cq-9 `Q3CubeQuotientData`**: 実立方剰余群 L₂^×/(L₂^×)³ の rank≥2 下界データ束ね。 -/
structure Q3CubeQuotientData where
  /-- [λ] は非立方（付値 3∤1・新規）。 -/
  lambda_noncube :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = q9cq_lambdaClass
  /-- [ζ₃] は非立方（q9kd 消費）。 -/
  zeta_noncube :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = q9cq_zetaClass
  /-- [ζ₃²] は非立方（q9ci 消費）。 -/
  zetaSq_noncube :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = q9cq_zetaSqClass
  /-- 8 個の非自明結合が全非立方（[λ]/[ζ₃] の 𝔽₃-独立性・rank≥2 下界）。 -/
  indep : Q9cqIndep

/-- **q9cq-9b `q9cq_data`**: 見出し実例——実 L₂=ℚ₃(√−3) の立方剰余群の rank≥2 下界。 -/
def q9cq_data : Q3CubeQuotientData where
  lambda_noncube := q9cq_lambda_nontrivial
  zeta_noncube := q9cq_zeta_noncube
  zetaSq_noncube := q9cq_zetaSq_noncube
  indep := q9cq_lambda_zeta_indep

/-- **q9cq-9c `q9cq_exists`**: 実立方剰余群の rank≥2 下界の存在。 -/
theorem q9cq_exists : Nonempty Q3CubeQuotientData := ⟨q9cq_data⟩

end IUT
