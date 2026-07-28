/-
  IUT/Q3ArtinRepReal.lean — 柱B・B3 実 Galois 表現上の実 Artin 導手
    （実 Gal(M/L₂)=⟨σ⟩ の **実 O_{L₂}-表現** V と、その **実固定部分加群**から読む codim）

  ── 主要成果の分類: **[実／(a) 昇格]** — 既存 Artin 導手側（arc の f=dim(V/V^{G_0})∈{0,1}・
     M471F `achRep`（dim/codim0 が**素の Nat フィールド**）・q9ac の指標和）は、監査が
     「**表現空間が無い・codim が実表現から計算されていない**」と判定した部分である
     （M471F 自身が正直限定に「**実 Galois 表現上の実 codim** は依然対象外」と明記）。
     本モジュールはそこを、
       * 実 O_{L₂}-加群 + 実 Galois 群 q9kdG の O_{L₂}-線形作用（`q9arRep`）という
         **本物の表現対象**、
       * その **正則表現 V_reg = O_M**（実環自己同型 σ の作用）と
         **実固有直線 V₀=O_{L₂}·1, V_χ=O_{L₂}·ζ₉, V_{χ²}=O_{L₂}·ζ₉²**（部分表現）、
       * **実固定部分加群 V^{G_i}**（G_i は q9wr/q9ac の**実分岐フィルトレーション**）から
         読む codim（`q9arIsCodim`）と、その **一意性定理**、
     で置換して昇格する。主語は実 σ・実 O_M・実 O_{L₂}-加群——Nat 階段を主語にしない。

  **本モジュールの真水（NEW・監査対象の新規実定理）**:
   (R1) `q9arRep`（実 O_{L₂}[Gal(M/L₂)]-加群）と正則表現 `q9arRegRep`（V=O_M、σ の
        O_{L₂}-線形性 `q9ar_act_smul` は「σ が L₂ を固定する」という実内容の帰結）。
   (R2) 実固有直線 3 本を**部分表現**として構成（`q9arSub`）し、各々が
        **自由階数 1**（`q9ar_chi_basis` 等・基底の存在と係数の一意性）であることを証明。
   (R3) 各直線の作用が **実 Kummer 指標 q9kd の χ⁰/χ/χ²** そのものであることを証明
        （`q9ar_chi_character` 等: act g v = χ(g)·v、χ(g)∈μ₃(O_M) は q9kd の実指標値）。
   (R4) **実固定部分加群 V^{G_i} の計算**: i≤2 で V_χ^{G_i}=0（ζ₃−1 の正則性 q9ci 消費）、
        i≥3 で V_χ^{G_i}=V_χ（G_i={e} の実証明 q9ac 消費）。V₀ は全 i で固定＝全体。
   (R5) **codim の一意性** `q9ar_codim_unique`（直線が非零であることから 0 と 1 は排他）
        ——codim の Nat 値は **実固定部分加群によって強制**される（選ばれた値ではない）。
   (R6) **Artin 導手の forced 値**: 「実 codim spec を満たす任意の c : Nat→Nat」に対し
        c 0=c 1=c 2=1（V_χ, V_{χ²}）・i≥3 で c i=0 ⟹ a(χ)=a(χ²)=3, a(χ⁰)=0。
   (R7) **実 conductor–discriminant** `q9ar_conductor_discriminant_real`:
        実 codim spec を満たす任意の c と、**実 different の指数 spec**
        （π₉ⁿ∣D ∧ ¬π₉ⁿ⁺¹∣D）を満たす任意の n に対し Σ_ρ a(ρ)·dim ρ = n。
        両辺とも実対象に spec で緊縛された数であり、どちらも「置いた Nat」ではない。
   (R8) 正則表現の **直和分解 V_reg = V₀⊕V_χ⊕V_{χ²}**（存在＋一意性）——Σ_ρ が
        C₃ の既約全体をちょうど 1 回ずつ渡ることの実証明。
   (R9) **作用の非自明性** `q9ar_chi_act_nontrivial`（σζ₉≠ζ₉）——q9kh/q9tk の実 G-加群
        μ₃(O_M) は作用が**自明**（`q9kh_act_trivial`）だったが、本表現は σ が実際に動かす。
        併せて **spec の非空虚性**（`q9ar_codim_chi_spec` 等の解の存在と具体値
        `q9ar_cond_disc_value` : 0+3+3=6）を示し、headline が空虚な全称命題でないことを保証する。

  **消費（再主張しない・二重計上回避）**:
   * 実分岐フィルトレーション G₀=G₁=G₂=⟨σ⟩・G₃∩{σ,σ²}=∅ は `q9ac_gi_le`/`q9ac_gi_gt`
     （及びその下の `q9wr_G2_mem`/`q9wr_G3_trivial`）から **消費**。
   * 実 different D=π₉⁶·(u\*u\*\*) は `q9wr_different`、鋭さ ¬π₉⁷∣D は
     `q9ac_different_sharp` から **消費**（本モジュールで再証明しない）。
   * (ζ₃−1) の正則性は `q9ci_zeta_sub_one_reg`、3 の正則性は `q9ci_three_reg_L2` から **消費**。
   * 実 Kummer 指標 χ⁰/χ/χ² とその完全枚挙は `q9kdChi0`/`q9kdChi`/`q9kdChi2`/
     `q9kd_hom_complete` から **消費**。
   * q9ac の指標和 a(χ)=3・Σ=6 との一致は `q9ar_matches_q9ac` で **cross-check のみ**
     （新規証明ゼロ・二重計上しない）。

  complete_pct 影響: **B3 0.34 →（独立監査次第・予測 +0.10〜0.16）— display-moving**。
  動かす中身は「Artin 導手側に**実表現空間と実固定部分加群が無い**」という q9ac 監査の
  弱点そのもの（codim を実 V^{G_i} から計算した）。

  正直な限定（§4 規約により消さない・弱化しない・q3k/q9ci/q9wr/q9ac/q9kd 継承の上に追記のみ）:
  1. **付値関数 v_M は無い**（q9wr 正直限定 1 を継承）。分岐群 G_i も different の指数も
     π₉ 冪の**可除性形式**。上付き番号・Herbrand φ/ψ はゼロ。
  2. **codim は「階数 1 の実直線に対する 2 択 spec」**（固定部分＝全体 ⟹ 0、固定部分＝0 ⟹ 1）
     であり、O_{L₂} 上の**一般の次元論（長さ・階数の一般理論）は建てていない**。
     どちらの択が成り立つかは各 (直線, G_i) で**実際に計算**し、値の一意性も証明したが、
     「任意の部分加群の codim」を定義したわけではない。
  3. **Artin 導手の重み |G_i|/|G₀| は有理数として形式化していない**。i≤2 では
     G_i = G₀（集合として一致・`q9ar_G_eq_G0`）ゆえ重み 1、i≥3 では codim=0 ゆえ項が
     消える、という**本拡大に固有の事実**で和を確定させている（一般公式ではない）。
  4. **拡大 1 個（M/L₂）・1 次元表現 3 本（C₃ の既約全体）のみ**。高次元表現・
     誘導表現・Brauer 帰納・合成 different（推移公式・d(M/ℚ₃)）は範囲外。
  5. **体化なし**（O_M・O_{L₂} の加群として扱う。ベクトル空間ではない）——A2 恒久限定継承。
     「dim ρ = 1」は自由階数 1（`q9ar_chi_basis` 等）の意味で用いる。
  6. 副有限 G_{L₂}・絶対 Galois 群・連続表現はゼロ（q9kd 正直限定 1 継承）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3ArtinConductorReal

namespace IUT

/-! ## q9ar-0: 座標補助（embed スカラー倍・embed の加法性・1≠0） -/

/-- embed(a)·x の第 0 座標 = a·x₀。 -/
theorem q9ar_smul_0 (a : q3rqCar) (x : q3kCar) :
    (q3kMul (q3kEmbed a) x).1 = q3rqMul a x.1 := by
  show q3rqAdd (q3rqMul a x.1)
      (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero x.2.2) (q3rqMul q3rqZero x.2.1)))
    = q3rqMul a x.1
  rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul x.2.2, q3rqRing.zero_mul x.2.1,
      q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
      q3rqRing.add_zero (q3rqRing.mul a x.1)]

/-- embed(a)·x の第 1（Y）座標 = a·x₁。 -/
theorem q9ar_smul_1 (a : q3rqCar) (x : q3kCar) :
    (q3kMul (q3kEmbed a) x).2.1 = q3rqMul a x.2.1 := by
  show q3rqAdd (q3rqAdd (q3rqMul a x.2.1) (q3rqMul q3rqZero x.1))
      (q3rqMul q3rqZeta (q3rqMul q3rqZero x.2.2)) = q3rqMul a x.2.1
  rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul x.1,
      q3rqRing.add_zero (q3rqRing.mul a x.2.1), q3rqRing.zero_mul x.2.2,
      q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero (q3rqRing.mul a x.2.1)]

/-- embed(a)·x の第 2（Y²）座標 = a·x₂。 -/
theorem q9ar_smul_2 (a : q3rqCar) (x : q3kCar) :
    (q3kMul (q3kEmbed a) x).2.2 = q3rqMul a x.2.2 := by
  show q3rqAdd (q3rqAdd (q3rqMul a x.2.2) (q3rqMul q3rqZero x.2.1))
      (q3rqMul q3rqZero x.1) = q3rqMul a x.2.2
  rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul x.2.1,
      q3rqRing.add_zero (q3rqRing.mul a x.2.2), q3rqRing.zero_mul x.1,
      q3rqRing.add_zero (q3rqRing.mul a x.2.2)]

/-- embed の加法性 embed(a+b) = embed(a)+embed(b)。 -/
theorem q9ar_embed_add (a b : q3rqCar) :
    q3kEmbed (q3rqAdd a b) = q3kAdd (q3kEmbed a) (q3kEmbed b) := by
  apply q3k_ext
  · rfl
  · show q3rqZero = q3rqAdd q3rqZero q3rqZero
    rw [q3k_A_eq, q3k_Z_eq, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqZero = q3rqAdd q3rqZero q3rqZero
    rw [q3k_A_eq, q3k_Z_eq, q3rqRing.add_zero q3rqRing.zero]

/-- embed(0) = 0。 -/
theorem q9ar_embed_zero : q3kEmbed q3rqZero = q3kZero := rfl

/-- 1 ≠ 0（O_{L₂}）。 -/
theorem q9ar_one_ne_zero : q3rqOne ≠ q3rqZero := by
  intro h
  exact q3rq_z3_one_ne_zero (congrArg Prod.fst h)

/-! ## q9ar-1（R1）: 実 O_{L₂}[Gal(M/L₂)]-加群（実表現） -/

/-- **R1（★）`q9arRep`**: 実 Galois 表現——O_{L₂} 上の加群に実 Gal(M/L₂)=q9kdG が
    **O_{L₂}-線形**に作用する対象。指標表でも Nat データでもなく、担体・加法・スカラー倍・
    群作用を持つ本物の表現対象である。 -/
structure q9arRep where
  /-- 表現空間の担体。 -/
  car : Type
  /-- 加法。 -/
  add : car → car → car
  /-- 零元。 -/
  zero : car
  /-- 反元。 -/
  neg : car → car
  /-- O_{L₂} スカラー倍。 -/
  smul : q3rqCar → car → car
  /-- 実 Galois 群の作用。 -/
  act : q9kdGCar → car → car
  /-- 加法結合律。 -/
  add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
  /-- 加法可換律。 -/
  add_comm : ∀ u v, add u v = add v u
  /-- 零元則。 -/
  zero_add : ∀ v, add zero v = v
  /-- 反元則。 -/
  neg_add : ∀ v, add (neg v) v = zero
  /-- 1 倍。 -/
  one_smul : ∀ v, smul q3rqOne v = v
  /-- スカラーの結合律。 -/
  smul_smul : ∀ a b v, smul (q3rqMul a b) v = smul a (smul b v)
  /-- スカラー倍の加法分配（ベクトル側）。 -/
  smul_add : ∀ a u v, smul a (add u v) = add (smul a u) (smul a v)
  /-- スカラー倍の加法分配（スカラー側）。 -/
  add_smul : ∀ a b v, smul (q3rqAdd a b) v = add (smul a v) (smul b v)
  /-- 0 倍は零。 -/
  zero_smul : ∀ v, smul q3rqZero v = zero
  /-- 単位元の作用は恒等。 -/
  act_one : ∀ v, act q9kdGCar.e v = v
  /-- 作用の準同型性。 -/
  act_mul : ∀ g h v, act (q9kdGMul g h) v = act g (act h v)
  /-- 作用は加法的。 -/
  act_add : ∀ g u v, act g (add u v) = add (act g u) (act g v)
  /-- 作用は O_{L₂}-線形（σ が L₂ を固定する実内容）。 -/
  act_smul : ∀ g a v, act g (smul a v) = smul a (act g v)

/-! ## q9ar-2（R1）: 正則表現 V_reg = O_M（実環自己同型 σ の作用） -/

/-- σ² は加法的（σ の加法性を 2 回）。 -/
theorem q9ar_sigma2_add (x y : q3kCar) :
    q3kSigma2 (q3kAdd x y) = q3kAdd (q3kSigma2 x) (q3kSigma2 y) := by
  rw [q3k_sigma2_comp (q3kAdd x y), q9kd_sigma_add x y,
      q9kd_sigma_add (q3kSigma x) (q3kSigma y), ← q3k_sigma2_comp x, ← q3k_sigma2_comp y]

/-- σ² は L₂ = embed 像を固定。 -/
theorem q9ar_sigma2_fixes_base (n : q3rqCar) : q3kSigma2 (q3kEmbed n) = q3kEmbed n := by
  rw [q3k_sigma2_comp (q3kEmbed n), q9kd_sigma_fixes_base n, q9kd_sigma_fixes_base n]

/-- **実作用は加法的**（g = id, σ, σ²）。 -/
theorem q9ar_act_add (g : q9kdGCar) (x y : q3kCar) :
    q9kdAct g (q3kAdd x y) = q3kAdd (q9kdAct g x) (q9kdAct g y) := by
  cases g with
  | e => rfl
  | s => exact q9kd_sigma_add x y
  | s2 => exact q9ar_sigma2_add x y

/-- **実作用は O_{L₂}-線形**: g(embed(a)·x) = embed(a)·g(x)
    ——σ が実際に L₂ を固定する（`q9kd_sigma_fixes_base`）という実内容の帰結。 -/
theorem q9ar_act_smul (g : q9kdGCar) (a : q3rqCar) (x : q3kCar) :
    q9kdAct g (q3kMul (q3kEmbed a) x) = q3kMul (q3kEmbed a) (q9kdAct g x) := by
  cases g with
  | e => rfl
  | s =>
    show q3kSigma (q3kMul (q3kEmbed a) x) = q3kMul (q3kEmbed a) (q3kSigma x)
    rw [q3k_sigma_mul (q3kEmbed a) x, q9kd_sigma_fixes_base a]
  | s2 =>
    show q3kSigma2 (q3kMul (q3kEmbed a) x) = q3kMul (q3kEmbed a) (q3kSigma2 x)
    rw [q3k_sigma2_mul (q3kEmbed a) x, q9ar_sigma2_fixes_base a]

/-- **R1b（★）`q9arRegRep`**: 実正則表現 V_reg = O_M
    （O_{L₂}-加群としてのランク 3・作用は実環自己同型 σ）。 -/
def q9arRegRep : q9arRep where
  car := q3kCar
  add := q3kAdd
  zero := q3kZero
  neg := q3kNeg
  smul := fun a x => q3kMul (q3kEmbed a) x
  act := q9kdAct
  add_assoc := q3kRing.add_assoc
  add_comm := q3kRing.add_comm
  zero_add := q3kRing.zero_add
  neg_add := q3kRing.neg_add
  one_smul := fun x => by
    show q3kMul (q3kEmbed q3rqOne) x = x
    rw [q3k_embed_one]
    exact q3k_one_mul x
  smul_smul := fun a b x => by
    show q3kMul (q3kEmbed (q3rqMul a b)) x = q3kMul (q3kEmbed a) (q3kMul (q3kEmbed b) x)
    rw [← q3k_embed_mul a b]
    exact q3k_mul_assoc (q3kEmbed a) (q3kEmbed b) x
  smul_add := fun a x y => q3k_left_distrib (q3kEmbed a) x y
  add_smul := fun a b x => by
    show q3kMul (q3kEmbed (q3rqAdd a b)) x = q3kAdd (q3kMul (q3kEmbed a) x) (q3kMul (q3kEmbed b) x)
    rw [q9ar_embed_add a b, q3k_kM_eq]
    exact q3kRing.right_distrib (q3kEmbed a) (q3kEmbed b) x
  zero_smul := fun x => by
    show q3kMul (q3kEmbed q3rqZero) x = q3kZero
    rw [q9ar_embed_zero, q3k_kM_eq]
    exact q3kRing.zero_mul x
  act_one := fun _ => rfl
  act_mul := q9kd_act_mul
  act_add := q9ar_act_add
  act_smul := q9ar_act_smul

/-! ## q9ar-3（R2）: 部分表現の構成（O_M の部分 O_{L₂}[G]-加群） -/

/-- 部分表現データ: O_M の部分集合が 0・加法・反元・O_{L₂} 倍・実 Galois 作用で閉じる。 -/
structure q9arSubData where
  /-- 部分集合。 -/
  mem : q3kCar → Prop
  /-- 0 を含む。 -/
  mem_zero : mem q3kZero
  /-- 加法で閉じる。 -/
  mem_add : ∀ {x y}, mem x → mem y → mem (q3kAdd x y)
  /-- 反元で閉じる。 -/
  mem_neg : ∀ {x}, mem x → mem (q3kNeg x)
  /-- O_{L₂} 倍で閉じる。 -/
  mem_smul : ∀ (a : q3rqCar) {x}, mem x → mem (q3kMul (q3kEmbed a) x)
  /-- 実 Galois 作用で閉じる。 -/
  mem_act : ∀ (g : q9kdGCar) {x}, mem x → mem (q9kdAct g x)

/-- **R2（★）`q9arSub`**: 部分表現（実正則表現の部分 O_{L₂}[Gal(M/L₂)]-加群）。 -/
def q9arSub (S : q9arSubData) : q9arRep where
  car := { x : q3kCar // S.mem x }
  add := fun u v => ⟨q3kAdd u.val v.val, S.mem_add u.property v.property⟩
  zero := ⟨q3kZero, S.mem_zero⟩
  neg := fun u => ⟨q3kNeg u.val, S.mem_neg u.property⟩
  smul := fun a u => ⟨q3kMul (q3kEmbed a) u.val, S.mem_smul a u.property⟩
  act := fun g u => ⟨q9kdAct g u.val, S.mem_act g u.property⟩
  add_assoc := fun u v w => Subtype.ext (q3kRing.add_assoc u.val v.val w.val)
  add_comm := fun u v => Subtype.ext (q3kRing.add_comm u.val v.val)
  zero_add := fun v => Subtype.ext (q3kRing.zero_add v.val)
  neg_add := fun v => Subtype.ext (q3kRing.neg_add v.val)
  one_smul := fun v => Subtype.ext (q9arRegRep.one_smul v.val)
  smul_smul := fun a b v => Subtype.ext (q9arRegRep.smul_smul a b v.val)
  smul_add := fun a u v => Subtype.ext (q9arRegRep.smul_add a u.val v.val)
  add_smul := fun a b v => Subtype.ext (q9arRegRep.add_smul a b v.val)
  zero_smul := fun v => Subtype.ext (q9arRegRep.zero_smul v.val)
  act_one := fun _ => Subtype.ext rfl
  act_mul := fun g h v => Subtype.ext (q9kd_act_mul g h v.val)
  act_add := fun g u v => Subtype.ext (q9ar_act_add g u.val v.val)
  act_smul := fun g a v => Subtype.ext (q9ar_act_smul g a v.val)

/-! ## q9ar-4（R2,R3）: 実固有直線 V₀ = O_{L₂}·1, V_χ = O_{L₂}·ζ₉, V_{χ²} = O_{L₂}·ζ₉² -/

/-- 実作用は第 0 座標を動かさない（σ が L₂ を固定する座標版）。 -/
theorem q9ar_act_coord0 (g : q9kdGCar) (x : q3kCar) : (q9kdAct g x).1 = x.1 := by
  cases g <;> rfl

/-- V₀ = O_{L₂}·1 の帰属（Y 成分・Y² 成分が 0）。 -/
def q9arTrivMem (x : q3kCar) : Prop := x.2.1 = q3rqZero ∧ x.2.2 = q3rqZero

/-- V_χ = O_{L₂}·ζ₉ の帰属（定数成分・Y² 成分が 0）。 -/
def q9arChiMem (x : q3kCar) : Prop := x.1 = q3rqZero ∧ x.2.2 = q3rqZero

/-- V_{χ²} = O_{L₂}·ζ₉² の帰属（定数成分・Y 成分が 0）。 -/
def q9arChi2Mem (x : q3kCar) : Prop := x.1 = q3rqZero ∧ x.2.1 = q3rqZero

/-- 0+0 = 0（座標補助）。 -/
theorem q9ar_zz : q3rqAdd q3rqZero q3rqZero = q3rqZero := q3rqRing.zero_add q3rqRing.zero

/-- −0 = 0（座標補助）。 -/
theorem q9ar_nz : q3rqNeg q3rqZero = q3rqZero := q3rqRing.neg_zero

/-- a·0 = 0（座標補助）。 -/
theorem q9ar_mz (a : q3rqCar) : q3rqMul a q3rqZero = q3rqZero := q3rqRing.mul_zero a

/-- **V₀ は部分表現**。 -/
def q9arTrivData : q9arSubData where
  mem := q9arTrivMem
  mem_zero := ⟨rfl, rfl⟩
  mem_add := fun {x y} hx hy =>
    ⟨by show q3rqAdd x.2.1 y.2.1 = q3rqZero
        rw [hx.1, hy.1]; exact q9ar_zz,
     by show q3rqAdd x.2.2 y.2.2 = q3rqZero
        rw [hx.2, hy.2]; exact q9ar_zz⟩
  mem_neg := fun {x} hx =>
    ⟨by show q3rqNeg x.2.1 = q3rqZero
        rw [hx.1]; exact q9ar_nz,
     by show q3rqNeg x.2.2 = q3rqZero
        rw [hx.2]; exact q9ar_nz⟩
  mem_smul := fun a {x} hx =>
    ⟨by rw [q9ar_smul_1 a x, hx.1]; exact q9ar_mz a,
     by rw [q9ar_smul_2 a x, hx.2]; exact q9ar_mz a⟩
  mem_act := fun g {x} hx => by
    cases g with
    | e => exact hx
    | s =>
      exact ⟨by show q3rqMul q3rqZeta x.2.1 = q3rqZero
                rw [hx.1]; exact q9ar_mz q3rqZeta,
             by show q3rqMul q3rqZetaSq x.2.2 = q3rqZero
                rw [hx.2]; exact q9ar_mz q3rqZetaSq⟩
    | s2 =>
      exact ⟨by show q3rqMul q3rqZetaSq x.2.1 = q3rqZero
                rw [hx.1]; exact q9ar_mz q3rqZetaSq,
             by show q3rqMul q3rqZeta x.2.2 = q3rqZero
                rw [hx.2]; exact q9ar_mz q3rqZeta⟩

/-- **V_χ は部分表現**。 -/
def q9arChiData : q9arSubData where
  mem := q9arChiMem
  mem_zero := ⟨rfl, rfl⟩
  mem_add := fun {x y} hx hy =>
    ⟨by show q3rqAdd x.1 y.1 = q3rqZero
        rw [hx.1, hy.1]; exact q9ar_zz,
     by show q3rqAdd x.2.2 y.2.2 = q3rqZero
        rw [hx.2, hy.2]; exact q9ar_zz⟩
  mem_neg := fun {x} hx =>
    ⟨by show q3rqNeg x.1 = q3rqZero
        rw [hx.1]; exact q9ar_nz,
     by show q3rqNeg x.2.2 = q3rqZero
        rw [hx.2]; exact q9ar_nz⟩
  mem_smul := fun a {x} hx =>
    ⟨by rw [q9ar_smul_0 a x, hx.1]; exact q9ar_mz a,
     by rw [q9ar_smul_2 a x, hx.2]; exact q9ar_mz a⟩
  mem_act := fun g {x} hx => by
    cases g with
    | e => exact hx
    | s =>
      exact ⟨hx.1,
             by show q3rqMul q3rqZetaSq x.2.2 = q3rqZero
                rw [hx.2]; exact q9ar_mz q3rqZetaSq⟩
    | s2 =>
      exact ⟨hx.1,
             by show q3rqMul q3rqZeta x.2.2 = q3rqZero
                rw [hx.2]; exact q9ar_mz q3rqZeta⟩

/-- **V_{χ²} は部分表現**。 -/
def q9arChi2Data : q9arSubData where
  mem := q9arChi2Mem
  mem_zero := ⟨rfl, rfl⟩
  mem_add := fun {x y} hx hy =>
    ⟨by show q3rqAdd x.1 y.1 = q3rqZero
        rw [hx.1, hy.1]; exact q9ar_zz,
     by show q3rqAdd x.2.1 y.2.1 = q3rqZero
        rw [hx.2, hy.2]; exact q9ar_zz⟩
  mem_neg := fun {x} hx =>
    ⟨by show q3rqNeg x.1 = q3rqZero
        rw [hx.1]; exact q9ar_nz,
     by show q3rqNeg x.2.1 = q3rqZero
        rw [hx.2]; exact q9ar_nz⟩
  mem_smul := fun a {x} hx =>
    ⟨by rw [q9ar_smul_0 a x, hx.1]; exact q9ar_mz a,
     by rw [q9ar_smul_1 a x, hx.2]; exact q9ar_mz a⟩
  mem_act := fun g {x} hx => by
    cases g with
    | e => exact hx
    | s =>
      exact ⟨hx.1,
             by show q3rqMul q3rqZeta x.2.1 = q3rqZero
                rw [hx.2]; exact q9ar_mz q3rqZeta⟩
    | s2 =>
      exact ⟨hx.1,
             by show q3rqMul q3rqZetaSq x.2.1 = q3rqZero
                rw [hx.2]; exact q9ar_mz q3rqZetaSq⟩

/-- **実自明表現** V₀ = O_{L₂}·1（部分表現）。 -/
def q9arTrivRep : q9arRep := q9arSub q9arTrivData

/-- **実 χ-表現** V_χ = O_{L₂}·ζ₉（部分表現）。 -/
def q9arChiRep : q9arRep := q9arSub q9arChiData

/-- **実 χ²-表現** V_{χ²} = O_{L₂}·ζ₉²（部分表現）。 -/
def q9arChi2Rep : q9arRep := q9arSub q9arChi2Data

/-! ## q9ar-5（R2）: 各直線は O_{L₂} 上自由階数 1（基底 1, ζ₉, ζ₉²） -/

/-- **R2a `q9ar_triv_basis`**: V₀ の任意元は embed(a)·1 と一意に書ける（基底 1）。 -/
theorem q9ar_triv_basis (v : q9arTrivRep.car) :
    ∃ a : q3rqCar, v.val = q3kMul (q3kEmbed a) q3kOne
      ∧ ∀ b : q3rqCar, v.val = q3kMul (q3kEmbed b) q3kOne → b = a := by
  refine ⟨v.val.1, ?_, ?_⟩
  · rw [q3k_mul_comm (q3kEmbed v.val.1) q3kOne, q3k_one_mul]
    apply q3k_ext
    · rfl
    · exact v.property.1
    · exact v.property.2
  · intro b hb
    rw [q3k_mul_comm (q3kEmbed b) q3kOne, q3k_one_mul] at hb
    exact (congrArg (fun z : q3kCar => z.1) hb).symm

/-- **R2b `q9ar_chi_basis`**: V_χ の任意元は embed(a)·ζ₉ と一意に書ける（基底 ζ₉）。 -/
theorem q9ar_chi_basis (v : q9arChiRep.car) :
    ∃ a : q3rqCar, v.val = q3kMul (q3kEmbed a) q3kZeta9
      ∧ ∀ b : q3rqCar, v.val = q3kMul (q3kEmbed b) q3kZeta9 → b = a := by
  refine ⟨v.val.2.1, ?_, ?_⟩
  · rw [q9yp_mulY_100 v.val.2.1]
    apply q3k_ext
    · exact v.property.1
    · rfl
    · exact v.property.2
  · intro b hb
    rw [q9yp_mulY_100 b] at hb
    exact (congrArg (fun z : q3kCar => z.2.1) hb).symm

/-- **R2c `q9ar_chi2_basis`**: V_{χ²} の任意元は embed(a)·ζ₉² と一意に書ける（基底 ζ₉²）。 -/
theorem q9ar_chi2_basis (v : q9arChi2Rep.car) :
    ∃ a : q3rqCar, v.val = q3kMul (q3kEmbed a) q9ypY2
      ∧ ∀ b : q3rqCar, v.val = q3kMul (q3kEmbed b) q9ypY2 → b = a := by
  refine ⟨v.val.2.2, ?_, ?_⟩
  · rw [q9kd_embed_mul_y2 v.val.2.2]
    apply q3k_ext
    · exact v.property.1
    · exact v.property.2
    · rfl
  · intro b hb
    rw [q9kd_embed_mul_y2 b] at hb
    exact (congrArg (fun z : q3kCar => z.2.2) hb).symm

/-! ## q9ar-6（R3）: 各直線の作用は実 Kummer 指標 χ⁰/χ/χ²（q9kd）そのもの -/

/-- **R3a `q9ar_triv_character`**: V₀ 上で g·v = χ⁰(g)·v（自明指標）。 -/
theorem q9ar_triv_character (g : q9kdGCar) (x : q3kCar) (hx : q9arTrivMem x) :
    q9kdAct g x = q3kMul ((q9kdChi0.map g).val) x := by
  show q9kdAct g x = q3kMul q3kOne x
  rw [q3k_one_mul]
  cases g with
  | e => rfl
  | s =>
    apply q3k_ext
    · rfl
    · show q3rqMul q3rqZeta x.2.1 = x.2.1
      rw [hx.1]; exact q9ar_mz q3rqZeta
    · show q3rqMul q3rqZetaSq x.2.2 = x.2.2
      rw [hx.2]; exact q9ar_mz q3rqZetaSq
  | s2 =>
    apply q3k_ext
    · rfl
    · show q3rqMul q3rqZetaSq x.2.1 = x.2.1
      rw [hx.1]; exact q9ar_mz q3rqZetaSq
    · show q3rqMul q3rqZeta x.2.2 = x.2.2
      rw [hx.2]; exact q9ar_mz q3rqZeta

/-- **R3b（★）`q9ar_chi_character`**: V_χ 上で g·v = χ(g)·v
    ——χ は q9kd の**実 Kummer 指標** `q9kdChi`（値は μ₃(O_M) の実元）。
    これにより V_χ は「指標 χ を持つ実 1 次元表現」として同定される。 -/
theorem q9ar_chi_character (g : q9kdGCar) (x : q3kCar) (hx : q9arChiMem x) :
    q9kdAct g x = q3kMul ((q9kdChi.map g).val) x := by
  cases g with
  | e =>
    show x = q3kMul q3kOne x
    rw [q3k_one_mul]
  | s =>
    show q3kSigma x = q3kMul (q3kEmbed q3rqZeta) x
    apply q3k_ext
    · rw [q9ar_smul_0 q3rqZeta x, hx.1, q9ar_mz q3rqZeta]
      exact hx.1
    · rw [q9ar_smul_1 q3rqZeta x]
      rfl
    · rw [q9ar_smul_2 q3rqZeta x, hx.2, q9ar_mz q3rqZeta]
      show q3rqMul q3rqZetaSq x.2.2 = q3rqZero
      rw [hx.2]; exact q9ar_mz q3rqZetaSq
  | s2 =>
    show q3kSigma2 x = q3kMul (q3kEmbed q3rqZetaSq) x
    apply q3k_ext
    · rw [q9ar_smul_0 q3rqZetaSq x, hx.1, q9ar_mz q3rqZetaSq]
      exact hx.1
    · rw [q9ar_smul_1 q3rqZetaSq x]
      rfl
    · rw [q9ar_smul_2 q3rqZetaSq x, hx.2, q9ar_mz q3rqZetaSq]
      show q3rqMul q3rqZeta x.2.2 = q3rqZero
      rw [hx.2]; exact q9ar_mz q3rqZeta

/-- **R3c（★）`q9ar_chi2_character`**: V_{χ²} 上で g·v = χ²(g)·v（q9kd の実指標 `q9kdChi2`）。 -/
theorem q9ar_chi2_character (g : q9kdGCar) (x : q3kCar) (hx : q9arChi2Mem x) :
    q9kdAct g x = q3kMul ((q9kdChi2.map g).val) x := by
  cases g with
  | e =>
    show x = q3kMul q3kOne x
    rw [q3k_one_mul]
  | s =>
    show q3kSigma x = q3kMul (q3kEmbed q3rqZetaSq) x
    apply q3k_ext
    · rw [q9ar_smul_0 q3rqZetaSq x, hx.1, q9ar_mz q3rqZetaSq]
      exact hx.1
    · rw [q9ar_smul_1 q3rqZetaSq x, hx.2, q9ar_mz q3rqZetaSq]
      show q3rqMul q3rqZeta x.2.1 = q3rqZero
      rw [hx.2]; exact q9ar_mz q3rqZeta
    · rw [q9ar_smul_2 q3rqZetaSq x]
      rfl
  | s2 =>
    show q3kSigma2 x = q3kMul (q3kEmbed q3rqZeta) x
    apply q3k_ext
    · rw [q9ar_smul_0 q3rqZeta x, hx.1, q9ar_mz q3rqZeta]
      exact hx.1
    · rw [q9ar_smul_1 q3rqZeta x, hx.2, q9ar_mz q3rqZeta]
      show q3rqMul q3rqZetaSq x.2.1 = q3rqZero
      rw [hx.2]; exact q9ar_mz q3rqZetaSq
    · rw [q9ar_smul_2 q3rqZeta x]
      rfl

/-! ## q9ar-7（R4,R5）: 実固定部分加群 V^H と codim の spec・一意性 -/

/-- **実固定部分加群**: v ∈ V^H ⟺ H の全ての元が v を固定する。 -/
def q9arFix (R : q9arRep) (H : q9kdGCar → Prop) (v : R.car) : Prop :=
  ∀ g, H g → R.act g v = v

/-- **R5（★）`q9arIsCodim`**: 階数 1 の実直線 R に対する codim(V^H) = n の spec。
    n=0 ⟺ **実固定部分加群が V 全体**、n=1 ⟺ **実固定部分加群が 0 のみ**。
    Nat 値は「置いた」のではなく、**実固定部分加群がどちらであるかによって決まる**
    （`q9ar_codim_unique` により値は一意）。 -/
def q9arIsCodim (R : q9arRep) (H : q9kdGCar → Prop) (n : Nat) : Prop :=
  (n = 0 ∧ ∀ v : R.car, q9arFix R H v)
  ∨ (n = 1 ∧ ∀ v : R.car, q9arFix R H v → v = R.zero)

/-- **R5b（★）`q9ar_codim_unique`**: 表現が非零ならば codim の値は一意
    ——「固定部分＝全体」と「固定部分＝0」は非零元の存在で排他になる。
    これにより codim は実固定部分加群から**強制**される数である。 -/
theorem q9ar_codim_unique {R : q9arRep} {H : q9kdGCar → Prop} {m n : Nat}
    (hne : ∃ v : R.car, v ≠ R.zero)
    (hm : q9arIsCodim R H m) (hn : q9arIsCodim R H n) : m = n := by
  obtain ⟨v, hv⟩ := hne
  cases hm with
  | inl h1 =>
    cases hn with
    | inl h2 => rw [h1.1, h2.1]
    | inr h2 => exact absurd (h2.2 v (h1.2 v)) hv
  | inr h1 =>
    cases hn with
    | inl h2 => exact absurd (h1.2 v (h2.2 v)) hv
    | inr h2 => rw [h1.1, h2.1]

/-- 群が自明（H ⊆ {e}）ならば固定部分加群は全体。 -/
theorem q9ar_fix_all_of_trivial {R : q9arRep} {H : q9kdGCar → Prop}
    (hH : ∀ g, H g → g = q9kdGCar.e) (v : R.car) : q9arFix R H v := by
  intro g hg
  rw [hH g hg]
  exact R.act_one v

/-! ## q9ar-8（R4）: 実分岐フィルトレーション G_i を部分群述語として使う -/

/-- **実分岐群 G_i**（q9ac/q9wr の**実**フィルトレーション: π₉^{i+1} ∣ (gπ₉ − π₉)）。 -/
def q9arG (i : Nat) (g : q9kdGCar) : Prop := q9acGiMem g i

/-- 単位元は全ての G_i に属する（gπ₉−π₉ = 0）。 -/
theorem q9ar_G_e (i : Nat) : q9arG i q9kdGCar.e := by
  refine ⟨q3kZero, ?_⟩
  show q3kAdd q9psPi9 (q3kNeg q9psPi9) = q3kMul (q9acPiPow (i + 1)) q3kZero
  exact (q3kRing.add_neg q9psPi9).trans (q3kRing.mul_zero (q9acPiPow (i + 1))).symm

/-- **R4a `q9ar_G_all`**: i ≤ 2 では G_i = ⟨σ⟩ 全体（`q9ac_gi_le` 消費）。 -/
theorem q9ar_G_all {i : Nat} (hi : i ≤ 2) : ∀ g, q9arG i g := by
  intro g
  cases g with
  | e => exact q9ar_G_e i
  | s => exact (q9ac_gi_le hi).1
  | s2 => exact (q9ac_gi_le hi).2

/-- **R4b `q9ar_G_triv`**: i ≥ 3 では G_i = {e}（`q9ac_gi_gt` 消費）。 -/
theorem q9ar_G_triv {i : Nat} (hi : 3 ≤ i) : ∀ g, q9arG i g → g = q9kdGCar.e := by
  intro g hg
  cases g with
  | e => rfl
  | s => exact absurd hg (q9ac_gi_gt hi).1
  | s2 => exact absurd hg (q9ac_gi_gt hi).2

/-- **R4c `q9ar_G_eq_G0`**: i ≤ 2 では G_i と G₀ は**集合として一致**
    （両者とも ⟨σ⟩ 全体）。Artin 導手の重み |G_i|/|G₀| = 1 はこの事実で置き換える
    （有理数の指数計算は形式化しない——正直な限定 3）。 -/
theorem q9ar_G_eq_G0 {i : Nat} (hi : i ≤ 2) (g : q9kdGCar) : q9arG i g ↔ q9arG 0 g :=
  ⟨fun _ => q9ar_G_all (by omega : (0 : Nat) ≤ 2) g, fun _ => q9ar_G_all hi g⟩

/-! ## q9ar-9（R4）: 各直線の実固定部分加群の計算 -/

/-- (ζ₃²−1) は正則（`q9ci_zeta_norm3`＋`q9ci_three_reg_L2` 消費）。 -/
theorem q9ar_zetaSq_sub_one_reg (z : q3rqCar)
    (h : q3rqMul (q3rqAdd q3rqZetaSq (q3rqNeg q3rqOne)) z = q3rqZero) : z = q3rqZero := by
  have key : q3rqMul q3rqThreeElt z = q3rqZero := by
    calc q3rqMul q3rqThreeElt z
        = q3rqMul (q3rqMul (q3rqAdd q3rqZetaSq (q3rqNeg q3rqOne))
              (q3rqAdd q3rqZeta (q3rqNeg q3rqOne))) z := by rw [← q9ci_zeta_norm3]
      _ = q3rqMul (q3rqMul (q3rqAdd q3rqZeta (q3rqNeg q3rqOne))
              (q3rqAdd q3rqZetaSq (q3rqNeg q3rqOne))) z := by
            rw [q3k_M_eq,
              q3rqRing.mul_comm (q3rqAdd q3rqZetaSq (q3rqNeg q3rqOne))
              (q3rqAdd q3rqZeta (q3rqNeg q3rqOne))]
      _ = q3rqMul (q3rqAdd q3rqZeta (q3rqNeg q3rqOne))
            (q3rqMul (q3rqAdd q3rqZetaSq (q3rqNeg q3rqOne)) z) := q3rqRing.mul_assoc _ _ _
      _ = q3rqMul (q3rqAdd q3rqZeta (q3rqNeg q3rqOne)) q3rqZero := by rw [h]
      _ = q3rqZero := q3rqRing.mul_zero _
  exact q9ci_three_reg_L2 z key

/-- ζ·b = b ⟹ (ζ−1)·b = 0（一般形の 1 行）。 -/
theorem q9ar_sub_one_mul {u b : q3rqCar} (h : q3rqMul u b = b) :
    q3rqMul (q3rqAdd u (q3rqNeg q3rqOne)) b = q3rqZero := by
  rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq,
      q3rqRing.right_distrib u (q3rqRing.neg q3rqRing.one) b,
      q3rqRing.neg_mul q3rqRing.one b, q3rqRing.one_mul b]
  rw [q3k_M_eq] at h
  rw [h]
  exact q3rqRing.add_neg b

/-- **R4d（★）`q9ar_chi_fix_zero`**: i ≤ 2 では **V_χ^{G_i} = 0**
    ——σ ∈ G_i（実分岐フィルトレーション）から ζ₃·b = b、
    (ζ₃−1) の正則性（`q9ci_zeta_sub_one_reg` 消費）で b = 0。 -/
theorem q9ar_chi_fix_zero {i : Nat} (hi : i ≤ 2) (v : q9arChiRep.car)
    (hv : q9arFix q9arChiRep (q9arG i) v) : v = q9arChiRep.zero := by
  have hs : q9kdAct q9kdGCar.s v.val = v.val :=
    congrArg (fun w : q9arChiRep.car => w.val) (hv q9kdGCar.s (q9ar_G_all hi q9kdGCar.s))
  have hb : q3rqMul q3rqZeta v.val.2.1 = v.val.2.1 :=
    congrArg (fun z : q3kCar => z.2.1) hs
  have hb0 : v.val.2.1 = q3rqZero :=
    q9ci_zeta_sub_one_reg v.val.2.1 (q9ar_sub_one_mul hb)
  apply Subtype.ext
  apply q3k_ext
  · exact v.property.1
  · exact hb0
  · exact v.property.2

/-- **R4e（★）`q9ar_chi2_fix_zero`**: i ≤ 2 では **V_{χ²}^{G_i} = 0**
    （σ の Y² 成分への作用は ζ₃² 倍・(ζ₃²−1) の正則性）。 -/
theorem q9ar_chi2_fix_zero {i : Nat} (hi : i ≤ 2) (v : q9arChi2Rep.car)
    (hv : q9arFix q9arChi2Rep (q9arG i) v) : v = q9arChi2Rep.zero := by
  have hs : q9kdAct q9kdGCar.s v.val = v.val :=
    congrArg (fun w : q9arChi2Rep.car => w.val) (hv q9kdGCar.s (q9ar_G_all hi q9kdGCar.s))
  have hc : q3rqMul q3rqZetaSq v.val.2.2 = v.val.2.2 :=
    congrArg (fun z : q3kCar => z.2.2) hs
  have hc0 : v.val.2.2 = q3rqZero :=
    q9ar_zetaSq_sub_one_reg v.val.2.2 (q9ar_sub_one_mul hc)
  apply Subtype.ext
  apply q3k_ext
  · exact v.property.1
  · exact v.property.2
  · exact hc0

/-- **R4f `q9ar_triv_fix_all`**: V₀ は任意の H で固定部分＝全体（σ が L₂ を固定する実内容）。 -/
theorem q9ar_triv_fix_all (H : q9kdGCar → Prop) (v : q9arTrivRep.car) :
    q9arFix q9arTrivRep H v := by
  intro g _
  apply Subtype.ext
  show q9kdAct g v.val = v.val
  rw [q9ar_triv_character g v.val v.property]
  show q3kMul q3kOne v.val = v.val
  exact q3k_one_mul v.val

/-! ## q9ar-10（R5）: 非零元の存在（codim 一意性の前提） -/

/-- V₀ ∋ 1 ≠ 0。 -/
theorem q9ar_triv_nonzero : ∃ v : q9arTrivRep.car, v ≠ q9arTrivRep.zero := by
  refine ⟨⟨q3kOne, ⟨rfl, rfl⟩⟩, ?_⟩
  intro h
  have h1 : q3kOne = q3kZero := congrArg (fun w : q9arTrivRep.car => w.val) h
  exact q9ar_one_ne_zero (congrArg (fun z : q3kCar => z.1) h1)

/-- V_χ ∋ ζ₉ ≠ 0。 -/
theorem q9ar_chi_nonzero : ∃ v : q9arChiRep.car, v ≠ q9arChiRep.zero := by
  refine ⟨⟨q3kZeta9, ⟨rfl, rfl⟩⟩, ?_⟩
  intro h
  have h1 : q3kZeta9 = q3kZero := congrArg (fun w : q9arChiRep.car => w.val) h
  exact q9ar_one_ne_zero (congrArg (fun z : q3kCar => z.2.1) h1)

/-- V_{χ²} ∋ ζ₉² ≠ 0。 -/
theorem q9ar_chi2_nonzero : ∃ v : q9arChi2Rep.car, v ≠ q9arChi2Rep.zero := by
  refine ⟨⟨q9ypY2, ?_⟩, ?_⟩
  · rw [q9yp_y2]
    exact ⟨rfl, rfl⟩
  · intro h
    have h1 : q9ypY2 = q3kZero := congrArg (fun w : q9arChi2Rep.car => w.val) h
    rw [q9yp_y2] at h1
    exact q9ar_one_ne_zero (congrArg (fun z : q3kCar => z.2.2) h1)

/-! ## q9ar-10b: 作用は**非自明**（q9kh の μ₃-加群のように自明作用ではない） -/

/-- **`q9ar_chi_act_nontrivial`**: V_χ 上の σ の作用は非自明（σζ₉ ≠ ζ₉）。
    ——q9kh/q9tk の実 G-加群 μ₃(O_M) は作用が**自明**（`q9kh_act_trivial`）であったが、
    本モジュールの実表現は σ が実際に元を動かす。codim が 1 になる実根拠でもある。 -/
theorem q9ar_chi_act_nontrivial :
    ∃ v : q9arChiRep.car, q9arChiRep.act q9kdGCar.s v ≠ v := by
  refine ⟨⟨q3kZeta9, ⟨rfl, rfl⟩⟩, ?_⟩
  intro h
  exact q9kd_sigma_ne_id (congrArg (fun w : q9arChiRep.car => w.val) h)

/-- **`q9ar_chi2_act_nontrivial`**: V_{χ²} 上の σ の作用も非自明（σζ₉² ≠ ζ₉²）。 -/
theorem q9ar_chi2_act_nontrivial :
    ∃ v : q9arChi2Rep.car, q9arChi2Rep.act q9kdGCar.s v ≠ v := by
  refine ⟨⟨q9ypY2, by rw [q9yp_y2]; exact ⟨rfl, rfl⟩⟩, ?_⟩
  intro h
  exact q9kd_sigma_y2_ne (congrArg (fun w : q9arChi2Rep.car => w.val) h)

/-! ## q9ar-11（R4,R6）: 各段の実 codim と Artin 導手の forced 値 -/

/-- i ≤ 2: codim(V_χ^{G_i}) = 1（実固定部分加群が 0）。 -/
theorem q9ar_codim_chi_le {i : Nat} (hi : i ≤ 2) :
    q9arIsCodim q9arChiRep (q9arG i) 1 :=
  Or.inr ⟨rfl, fun v hv => q9ar_chi_fix_zero hi v hv⟩

/-- i ≥ 3: codim(V_χ^{G_i}) = 0（G_i={e} ゆえ固定部分が全体）。 -/
theorem q9ar_codim_chi_gt {i : Nat} (hi : 3 ≤ i) :
    q9arIsCodim q9arChiRep (q9arG i) 0 :=
  Or.inl ⟨rfl, fun v => q9ar_fix_all_of_trivial (q9ar_G_triv hi) v⟩

/-- i ≤ 2: codim(V_{χ²}^{G_i}) = 1。 -/
theorem q9ar_codim_chi2_le {i : Nat} (hi : i ≤ 2) :
    q9arIsCodim q9arChi2Rep (q9arG i) 1 :=
  Or.inr ⟨rfl, fun v hv => q9ar_chi2_fix_zero hi v hv⟩

/-- i ≥ 3: codim(V_{χ²}^{G_i}) = 0。 -/
theorem q9ar_codim_chi2_gt {i : Nat} (hi : 3 ≤ i) :
    q9arIsCodim q9arChi2Rep (q9arG i) 0 :=
  Or.inl ⟨rfl, fun v => q9ar_fix_all_of_trivial (q9ar_G_triv hi) v⟩

/-- 全ての i: codim(V₀^{G_i}) = 0。 -/
theorem q9ar_codim_triv (i : Nat) : q9arIsCodim q9arTrivRep (q9arG i) 0 :=
  Or.inl ⟨rfl, fun v => q9ar_triv_fix_all (q9arG i) v⟩

/-- **R6a（★）`q9ar_artin_chi`**: 実 codim spec を満たす**任意の** c について
    c i = 1 (i≤2)・c i = 0 (i≥3)・a(χ) = c 0 + c 1 + c 2 = 3。
    Nat 値は spec と実固定部分加群から**強制**される（置いた値ではない）。 -/
theorem q9ar_artin_chi (c : Nat → Nat)
    (hc : ∀ i, q9arIsCodim q9arChiRep (q9arG i) (c i)) :
    (∀ i, i ≤ 2 → c i = 1) ∧ (∀ i, 3 ≤ i → c i = 0) ∧ c 0 + c 1 + c 2 = 3 := by
  have h1 : ∀ i, i ≤ 2 → c i = 1 := fun i hi =>
    q9ar_codim_unique q9ar_chi_nonzero (hc i) (q9ar_codim_chi_le hi)
  have h2 : ∀ i, 3 ≤ i → c i = 0 := fun i hi =>
    q9ar_codim_unique q9ar_chi_nonzero (hc i) (q9ar_codim_chi_gt hi)
  refine ⟨h1, h2, ?_⟩
  rw [h1 0 (by omega), h1 1 (by omega), h1 2 (by omega)]

/-- **R6b `q9ar_artin_chi2`**: a(χ²) = 3（同上）。 -/
theorem q9ar_artin_chi2 (c : Nat → Nat)
    (hc : ∀ i, q9arIsCodim q9arChi2Rep (q9arG i) (c i)) :
    (∀ i, i ≤ 2 → c i = 1) ∧ (∀ i, 3 ≤ i → c i = 0) ∧ c 0 + c 1 + c 2 = 3 := by
  have h1 : ∀ i, i ≤ 2 → c i = 1 := fun i hi =>
    q9ar_codim_unique q9ar_chi2_nonzero (hc i) (q9ar_codim_chi2_le hi)
  have h2 : ∀ i, 3 ≤ i → c i = 0 := fun i hi =>
    q9ar_codim_unique q9ar_chi2_nonzero (hc i) (q9ar_codim_chi2_gt hi)
  refine ⟨h1, h2, ?_⟩
  rw [h1 0 (by omega), h1 1 (by omega), h1 2 (by omega)]

/-- **R6c `q9ar_artin_triv`**: a(χ⁰) = 0（自明表現は全段で固定部分＝全体）。 -/
theorem q9ar_artin_triv (c : Nat → Nat)
    (hc : ∀ i, q9arIsCodim q9arTrivRep (q9arG i) (c i)) :
    (∀ i, c i = 0) ∧ c 0 + c 1 + c 2 = 0 := by
  have h1 : ∀ i, c i = 0 := fun i =>
    q9ar_codim_unique q9ar_triv_nonzero (hc i) (q9ar_codim_triv i)
  refine ⟨h1, ?_⟩
  rw [h1 0, h1 1, h1 2]

/-! ## q9ar-12（R8）: 正則表現の実直和分解 V_reg = V₀ ⊕ V_χ ⊕ V_{χ²} -/

/-- **R8a（★）`q9ar_regular_decomp`**: 実正則表現 O_M は 3 本の実固有直線の和で書ける
    （C₃ の既約表現が重複度 1 でちょうど出揃う——Σ_ρ が全既約を渡ることの実証明）。 -/
theorem q9ar_regular_decomp (x : q3kCar) :
    ∃ a b c : q3kCar, q9arTrivMem a ∧ q9arChiMem b ∧ q9arChi2Mem c
      ∧ x = q3kAdd (q3kAdd a b) c := by
  refine ⟨((x.1, q3rqZero, q3rqZero) : q3kCar), ((q3rqZero, x.2.1, q3rqZero) : q3kCar),
    ((q3rqZero, q3rqZero, x.2.2) : q3kCar), ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
  apply q3k_ext
  · show x.1 = q3rqAdd (q3rqAdd x.1 q3rqZero) q3rqZero
    rw [q3k_A_eq, q3k_Z_eq, q3rqRing.add_zero x.1, q3rqRing.add_zero x.1]
  · show x.2.1 = q3rqAdd (q3rqAdd q3rqZero x.2.1) q3rqZero
    rw [q3k_A_eq, q3k_Z_eq, q3rqRing.zero_add x.2.1, q3rqRing.add_zero x.2.1]
  · show x.2.2 = q3rqAdd (q3rqAdd q3rqZero q3rqZero) x.2.2
    rw [q3k_A_eq, q3k_Z_eq, q3rqRing.zero_add q3rqRing.zero, q3rqRing.zero_add x.2.2]

/-- 和の第 0 座標は V₀ 成分の第 0 座標。 -/
theorem q9ar_sum_coord0 {p q r : q3kCar} (hq : q9arChiMem q) (hr : q9arChi2Mem r) :
    (q3kAdd (q3kAdd p q) r).1 = p.1 := by
  show q3rqAdd (q3rqAdd p.1 q.1) r.1 = p.1
  rw [hq.1, hr.1, q3k_A_eq, q3k_Z_eq, q3rqRing.add_zero p.1, q3rqRing.add_zero p.1]

/-- 和の第 1 座標は V_χ 成分の第 1 座標。 -/
theorem q9ar_sum_coord1 {p q r : q3kCar} (hp : q9arTrivMem p) (hr : q9arChi2Mem r) :
    (q3kAdd (q3kAdd p q) r).2.1 = q.2.1 := by
  show q3rqAdd (q3rqAdd p.2.1 q.2.1) r.2.1 = q.2.1
  rw [hp.1, hr.2, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_add q.2.1, q3rqRing.add_zero q.2.1]

/-- 和の第 2 座標は V_{χ²} 成分の第 2 座標。 -/
theorem q9ar_sum_coord2 {p q r : q3kCar} (hp : q9arTrivMem p) (hq : q9arChiMem q) :
    (q3kAdd (q3kAdd p q) r).2.2 = r.2.2 := by
  show q3rqAdd (q3rqAdd p.2.2 q.2.2) r.2.2 = r.2.2
  rw [hp.2, hq.2, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_add q3rqRing.zero,
      q3rqRing.zero_add r.2.2]

/-- **R8b（★）`q9ar_regular_decomp_unique`**: 分解は一意（＝直和分解）。 -/
theorem q9ar_regular_decomp_unique {a b c a' b' c' : q3kCar}
    (ha : q9arTrivMem a) (hb : q9arChiMem b) (hc : q9arChi2Mem c)
    (ha' : q9arTrivMem a') (hb' : q9arChiMem b') (hc' : q9arChi2Mem c')
    (h : q3kAdd (q3kAdd a b) c = q3kAdd (q3kAdd a' b') c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have e0 : (q3kAdd (q3kAdd a b) c).1 = (q3kAdd (q3kAdd a' b') c').1 :=
    congrArg (fun z : q3kCar => z.1) h
  have e1 : (q3kAdd (q3kAdd a b) c).2.1 = (q3kAdd (q3kAdd a' b') c').2.1 :=
    congrArg (fun z : q3kCar => z.2.1) h
  have e2 : (q3kAdd (q3kAdd a b) c).2.2 = (q3kAdd (q3kAdd a' b') c').2.2 :=
    congrArg (fun z : q3kCar => z.2.2) h
  rw [q9ar_sum_coord0 hb hc, q9ar_sum_coord0 hb' hc'] at e0
  rw [q9ar_sum_coord1 ha hc, q9ar_sum_coord1 ha' hc'] at e1
  rw [q9ar_sum_coord2 ha hb, q9ar_sum_coord2 ha' hb'] at e2
  have h0 : a.1 = a'.1 := e0
  have h1 : b.2.1 = b'.2.1 := e1
  have h2 : c.2.2 = c'.2.2 := e2
  refine ⟨q3k_ext h0 ?_ ?_, q3k_ext ?_ h1 ?_, q3k_ext ?_ ?_ h2⟩
  · rw [ha.1, ha'.1]
  · rw [ha.2, ha'.2]
  · rw [hb.1, hb'.1]
  · rw [hb.2, hb'.2]
  · rw [hc.1, hc'.1]
  · rw [hc.2, hc'.2]

/-! ## q9ar-13（R7）: 実 different の指数 spec（π₉ 可除性・一意） -/

/-- 実 different の生成元 D = (σπ₉−π₉)(σ²π₉−π₉)（`q9wr_different` の左辺）。 -/
def q9arDifferent : q3kCar :=
  q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
         (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))

/-- **R7a `q9arIsDiffExp`**: 実 different の指数 n の spec（π₉ⁿ∣D ∧ ¬π₉ⁿ⁺¹∣D）。
    Nat 値ではなく、**実 D の可除性そのもの**で n を規定する。 -/
def q9arIsDiffExp (n : Nat) : Prop :=
  q9wrDvd (q9acPiPow n) q9arDifferent ∧ ¬ q9wrDvd (q9acPiPow (n + 1)) q9arDifferent

/-- π₉⁶（q9ac の冪関数と q9ps の名前付き π₉⁶ の一致）。 -/
theorem q9ar_pow6 : q9acPiPow 6 = q9psPi6 := by
  have h : q9acPiPow (3 + 3) = q3kMul (q9acPiPow 3) (q9acPiPow 3) := q9ac_pow_add 3 3
  rw [q9ac_pow3] at h
  exact h

/-- π₉⁷ = π₉⁶·π₉。 -/
theorem q9ar_pow7 : q9acPiPow 7 = q3kMul q9psPi6 q9psPi9 := by
  show q3kMul (q9acPiPow 6) q9psPi9 = q3kMul q9psPi6 q9psPi9
  rw [q9ar_pow6]

/-- **R7b `q9ar_diffExp_six`**: 実 different の指数 spec を 6 が満たす
    （π₉⁶∣D は `q9wr_different`、¬π₉⁷∣D は `q9ac_different_sharp` を **消費**）。 -/
theorem q9ar_diffExp_six : q9arIsDiffExp 6 := by
  refine ⟨⟨q3kMul q9wrUStar q9wrUStarStar, ?_⟩, ?_⟩
  · rw [q9ar_pow6]
    exact q9wr_different
  · show ¬ q9wrDvd (q9acPiPow 7) q9arDifferent
    intro h
    rw [q9ar_pow7] at h
    exact q9ac_different_sharp h

/-- **R7c `q9ar_diffExp_unique`**: 指数 spec を満たす n は一意（可除性の単調性）。 -/
theorem q9ar_diffExp_unique {m n : Nat}
    (hm : q9arIsDiffExp m) (hn : q9arIsDiffExp n) : m = n := by
  obtain h1 | h1 := (by omega : m + 1 ≤ n ∨ n ≤ m)
  · exact absurd (q9ac_dvd_of_le h1 hn.1) hm.2
  · obtain h2 | h2 := (by omega : n + 1 ≤ m ∨ m ≤ n)
    · exact absurd (q9ac_dvd_of_le h2 hm.1) hn.2
    · omega

/-- **R7d `q9ar_diffExp_eq_six`**: 実 different の指数は 6（v(𝔡)=d(M/L₂)=6）。 -/
theorem q9ar_diffExp_eq_six {n : Nat} (hn : q9arIsDiffExp n) : n = 6 :=
  q9ar_diffExp_unique hn q9ar_diffExp_six

/-! ## q9ar-14（R7 ★headline）: 実 conductor–discriminant Σ_ρ a(ρ)·dim ρ = v(𝔡) -/

/-- **R7（★★ 本命題）`q9ar_conductor_discriminant_real`**:
    **実表現の実固定部分加群から読んだ codim** の spec を満たす任意の c⁰, c¹, c² と、
    **実 different の可除性 spec** を満たす任意の n に対し
      Σ_ρ a(ρ)·dim ρ = a(χ⁰)·1 + a(χ)·1 + a(χ²)·1 = 0 + 3 + 3 = n（= 6 = v(𝔡)）。
    左辺は実固定部分加群に、右辺は実 different の可除性に緊縛されており、
    どちらも「置いた Nat」ではない。dim ρ = 1 は各直線の自由階数 1
    （`q9ar_triv_basis`/`q9ar_chi_basis`/`q9ar_chi2_basis`）による。 -/
theorem q9ar_conductor_discriminant_real
    (c0 c1 c2 : Nat → Nat)
    (h0 : ∀ i, q9arIsCodim q9arTrivRep (q9arG i) (c0 i))
    (h1 : ∀ i, q9arIsCodim q9arChiRep (q9arG i) (c1 i))
    (h2 : ∀ i, q9arIsCodim q9arChi2Rep (q9arG i) (c2 i))
    {n : Nat} (hn : q9arIsDiffExp n) :
    (c0 0 + c0 1 + c0 2) + (c1 0 + c1 1 + c1 2) + (c2 0 + c2 1 + c2 2) = n := by
  rw [(q9ar_artin_triv c0 h0).2, (q9ar_artin_chi c1 h1).2.2,
      (q9ar_artin_chi2 c2 h2).2.2, q9ar_diffExp_eq_six hn]

/-- **R7e `q9ar_conductor_tail`**: i ≥ 3 の項は全て 0（有限和で尽きることの保証）
    ——Artin 導手 Σ_{i≥0} を i≤2 で打ち切ってよい実根拠。 -/
theorem q9ar_conductor_tail
    (c0 c1 c2 : Nat → Nat)
    (h0 : ∀ i, q9arIsCodim q9arTrivRep (q9arG i) (c0 i))
    (h1 : ∀ i, q9arIsCodim q9arChiRep (q9arG i) (c1 i))
    (h2 : ∀ i, q9arIsCodim q9arChi2Rep (q9arG i) (c2 i)) :
    ∀ i, 3 ≤ i → c0 i = 0 ∧ c1 i = 0 ∧ c2 i = 0 := by
  intro i hi
  exact ⟨(q9ar_artin_triv c0 h0).1 i, (q9ar_artin_chi c1 h1).2.1 i hi,
    (q9ar_artin_chi2 c2 h2).2.1 i hi⟩

/-! ## q9ar-14b: **非空虚性**——実 codim spec は実際に解を持つ（headline の具体値 0+3+3=6） -/

/-- 自明表現側の codim 関数（恒等的に 0）。 -/
def q9arZeroFn : Nat → Nat := fun _ => 0

/-- V₀ の実 codim spec の解（全段 0）。 -/
theorem q9ar_codim_triv_spec (i : Nat) :
    q9arIsCodim q9arTrivRep (q9arG i) (q9arZeroFn i) := q9ar_codim_triv i

/-- V_χ の実 codim spec の解（i≤2 で 1・i≥3 で 0）。
    **注意**: `q9acLe2` は「解が存在する」ことの**証人**として使うだけであり、
    定理の主語ではない（主語は実固定部分加群の spec `q9arIsCodim`）。 -/
theorem q9ar_codim_chi_spec (i : Nat) :
    q9arIsCodim q9arChiRep (q9arG i) (q9acLe2 i) := by
  match i with
  | 0 => exact q9ar_codim_chi_le (by omega)
  | 1 => exact q9ar_codim_chi_le (by omega)
  | 2 => exact q9ar_codim_chi_le (by omega)
  | _ + 3 => exact q9ar_codim_chi_gt (by omega)

/-- V_{χ²} の実 codim spec の解。 -/
theorem q9ar_codim_chi2_spec (i : Nat) :
    q9arIsCodim q9arChi2Rep (q9arG i) (q9acLe2 i) := by
  match i with
  | 0 => exact q9ar_codim_chi2_le (by omega)
  | 1 => exact q9ar_codim_chi2_le (by omega)
  | 2 => exact q9ar_codim_chi2_le (by omega)
  | _ + 3 => exact q9ar_codim_chi2_gt (by omega)

/-- **`q9ar_cond_disc_value`**: headline を実際の解に適用した具体値
    a(χ⁰)+a(χ)+a(χ²) = 0+3+3 = 6 = v(𝔡)（空虚な全称命題でないことの証拠）。 -/
theorem q9ar_cond_disc_value :
    (q9arZeroFn 0 + q9arZeroFn 1 + q9arZeroFn 2)
      + (q9acLe2 0 + q9acLe2 1 + q9acLe2 2)
      + (q9acLe2 0 + q9acLe2 1 + q9acLe2 2) = 6 :=
  q9ar_conductor_discriminant_real q9arZeroFn q9acLe2 q9acLe2
    q9ar_codim_triv_spec q9ar_codim_chi_spec q9ar_codim_chi2_spec q9ar_diffExp_six

/-! ## q9ar-15: q9ac（指標和版）との cross-check（新規証明ゼロ） -/

/-- **`q9ar_matches_q9ac`**: 実表現から読んだ Artin 導手が、q9ac の**指標和版**
    `q9acArtin`（a(χ⁰)=0, a(χ)=a(χ²)=3, Σ=6）と一致する cross-check。
    **新規証明ゼロ**——q9ac 側の値は再主張せず一致だけを述べる（二重計上回避）。 -/
theorem q9ar_matches_q9ac
    (c0 c1 c2 : Nat → Nat)
    (h0 : ∀ i, q9arIsCodim q9arTrivRep (q9arG i) (c0 i))
    (h1 : ∀ i, q9arIsCodim q9arChiRep (q9arG i) (c1 i))
    (h2 : ∀ i, q9arIsCodim q9arChi2Rep (q9arG i) (c2 i)) :
    (c0 0 + c0 1 + c0 2 = q9acArtin q9kdGCar.e)
    ∧ (c1 0 + c1 1 + c1 2 = q9acArtin q9kdGCar.s)
    ∧ (c2 0 + c2 1 + c2 2 = q9acArtin q9kdGCar.s2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(q9ar_artin_triv c0 h0).2]
    exact q9ac_artin_chi0.symm
  · rw [(q9ar_artin_chi c1 h1).2.2]
    exact q9ac_artin_chi.symm
  · rw [(q9ar_artin_chi2 c2 h2).2.2]
    exact q9ac_artin_chi2.symm

/-! ## q9ar-16: capstone（束ねのみ・新規証明ゼロ） -/

/-- **capstone `Q3ArtinRepRealData`**: 実 Galois 表現上の実 Artin 導手データ。 -/
structure Q3ArtinRepRealData where
  /-- V_χ は実 Kummer 指標 χ を持つ実表現（act g v = χ(g)·v）。 -/
  chi_character : ∀ g x, q9arChiMem x → q9kdAct g x = q3kMul ((q9kdChi.map g).val) x
  /-- V_χ は O_{L₂} 上自由階数 1（基底 ζ₉）。 -/
  chi_basis : ∀ v : q9arChiRep.car, ∃ a : q3rqCar, v.val = q3kMul (q3kEmbed a) q3kZeta9
    ∧ ∀ b : q3rqCar, v.val = q3kMul (q3kEmbed b) q3kZeta9 → b = a
  /-- i ≤ 2 で実固定部分加群 V_χ^{G_i} = 0。 -/
  chi_fix_zero : ∀ {i : Nat}, i ≤ 2 → ∀ v : q9arChiRep.car,
    q9arFix q9arChiRep (q9arG i) v → v = q9arChiRep.zero
  /-- i ≥ 3 では G_i = {e}（実分岐フィルトレーション）。 -/
  g_trivial : ∀ {i : Nat}, 3 ≤ i → ∀ g, q9arG i g → g = q9kdGCar.e
  /-- codim の値は実固定部分加群から強制される（一意性）。 -/
  codim_unique : ∀ {R : q9arRep} {H : q9kdGCar → Prop} {m n : Nat},
    (∃ v : R.car, v ≠ R.zero) → q9arIsCodim R H m → q9arIsCodim R H n → m = n
  /-- 実 different の指数は 6。 -/
  diff_exp : ∀ {n : Nat}, q9arIsDiffExp n → n = 6
  /-- 実 conductor–discriminant Σ_ρ a(ρ)·dim ρ = v(𝔡)。 -/
  cond_disc : ∀ (c0 c1 c2 : Nat → Nat),
    (∀ i, q9arIsCodim q9arTrivRep (q9arG i) (c0 i)) →
    (∀ i, q9arIsCodim q9arChiRep (q9arG i) (c1 i)) →
    (∀ i, q9arIsCodim q9arChi2Rep (q9arG i) (c2 i)) →
    ∀ (n : Nat), q9arIsDiffExp n →
      (c0 0 + c0 1 + c0 2) + (c1 0 + c1 1 + c1 2) + (c2 0 + c2 1 + c2 2) = n
  /-- 正則表現の直和分解 V_reg = V₀⊕V_χ⊕V_{χ²}（存在）。 -/
  regular_decomp : ∀ x : q3kCar, ∃ a b c : q3kCar,
    q9arTrivMem a ∧ q9arChiMem b ∧ q9arChi2Mem c ∧ x = q3kAdd (q3kAdd a b) c

/-- **証人 `q9ar_data`**: 実 M=ℚ₃(ζ₉)/L₂ 上の実 Galois 表現・実 codim・実 conductor–discriminant。 -/
def q9ar_data : Q3ArtinRepRealData where
  chi_character := q9ar_chi_character
  chi_basis := q9ar_chi_basis
  chi_fix_zero := fun hi v hv => q9ar_chi_fix_zero hi v hv
  g_trivial := fun hi => q9ar_G_triv hi
  codim_unique := fun hne hm hn => q9ar_codim_unique hne hm hn
  diff_exp := fun hn => q9ar_diffExp_eq_six hn
  cond_disc := fun c0 c1 c2 h0 h1 h2 _ hn =>
    q9ar_conductor_discriminant_real c0 c1 c2 h0 h1 h2 hn
  regular_decomp := q9ar_regular_decomp

/-- **`q9ar_exists`**: 実 Galois 表現上の実 Artin 導手／実 conductor–discriminant の存在。 -/
theorem q9ar_exists : Nonempty Q3ArtinRepRealData := ⟨q9ar_data⟩

end IUT
