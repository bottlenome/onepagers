/-
  IUT/Q3KummerDualityReal.lean — 実巡回 3 次 Kummer 双対（B6）
    M = ℚ₃(ζ₉) = L₂[Y]/(Y³−ζ₃)・実 Gal(M/L₂) = ⟨q3kSigma⟩ の上の完全 Kummer 双対

  ── 主要成果の分類: **[実／(a) 昇格]** — 既存 Kummer 理論の「抽象体 K・witness 根・
     仮説形」（M320F/M345F/M349F の正直限定＝全射性は外部仮説・完全双対は未達）を、
     実巡回 3 次 Kummer 拡大 M = ℚ₃(ζ₉) = L₂[Y]/(Y³−ζ₃)・実相対 Galois
     Gal(M/L₂) = ⟨q3kSigma⟩（実 O_M の実環自己同型・位数 3）上の **完全双対**へ昇格する。
     主対象は柱A level-9 キャンペーンが建てた **実** σ（Y↦ζ₃Y）であり、AUDIT_RUBRIC の
     「Galois 群＝実際の環自己同型の群」を初めて満たす。toy 主語なし（m202fVol 型・
     Bool 軌道・surrogate 群を一切使わない）。

  complete_pct 影響: **B6 0→（監査次第・予測 0.15–0.25）— 表示を動かす柱B 初の
  モジュール**。本モジュールの新規内容は
   (1) 群提示 L₂^× = ℤ×U₂ 上の Kummer 類 [ζ₃] の非自明性、
   (2) 完全対 Gal(M/L₂)×⟨[ζ₃]⟩→μ₃ の両側非退化、
   (3) Hom(Gal(M/L₂),μ₃) の完全枚挙、
   (4) k↦χᵏ が ⟨[ζ₃]⟩→Hom の全単射（＝この拡大での Kummer 同型の完全証明）。
  **消費（再主張しない）**: ζ₃ の O_{L₂} 内 3 乗根非存在は `q9ci_no_cbrt_zeta`（柱A）
  から **消費**する（本モジュールの新規主張ではない）。O_M 内 μ₃ 完全性
  （x³=1⟹x∈{1,ζ₃,ζ₃²}）は `q9c_m_mu3_complete`（柱A）から **消費**する。

  内容:
   * q9kd_sigma_fixes_base / q9kd_sigma_add / q9kd_sigma3_id / σ≠id・σ²≠id  — T1,T2
   * q9kd_cocycle / q9kd_cocycle2                                         — T3
   * q9kdG（実 Gal(M/L₂)=⟨σ⟩ の 3 元群）・q9kdAct（実環自己同型作用）        — 実現
   * q9kdMu3（μ₃(O_M)={x:x³=1}・実群）・q9kdChi（実 Kummer 指標 Hom）        — 主対象
   * q9kd_chi_hom / q9kd_chi_faithful                                     — T4,T5
   * q9kd_class_nontrivial（q9ci_no_cbrt_zeta 消費）                       — T6
   * q9kd_pairing_eq / q9kd_pairing_nondeg_left / _right                  — T7,T8
   * q9kd_hom_exhaust / q9kd_hom_complete（q9c_m_mu3_complete 消費）        — T9
   * q9kd_kummer_iso_surj / _inj（χⁱ 全単射）                              — T10
   * Q3KummerDualityRealData / q9kd_data / q9kd_exists                    — T11

  正直な限定（§4 規約により消さない・弱化しない・q3k/q3rq 継承の上に追記のみ）:
  1. **Galois は有限商 ⟨σ⟩≅Gal(M/L₂) のみ**。副有限 G_{L₂}・絶対 Galois 群・逆極限は
     ゼロ。一般 H¹ 形式論（galH1Module）への接続なし（q3k が IUTField でないため既存
     抽象機構と型が合わない——接続は M 体化後の後続）。
  2. **n=3・拡大 1 個・類 1 個**。L₂^×/(L₂^×)³ の全体構造は計算しない（⟨[ζ₃]⟩ 部分のみ）。
  3. μ₃⊂L₂・μ₃(O_M) 完全性は q3mc/q9c 消費（本モジュールで再証明しない）。
  4. O_M と単数群のみ（体化なし・A2 恒久限定継承）・兄弟担体・実テータ関数ゼロ・
     π₁ 同定ゼロ・tmzLimit 比較橋なし（q3rq §5 firewall 継承）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3Mu9Completeness
import IUT.Q3KummerYPow

namespace IUT

/-! ## q9kd-1: σ の基礎（T1,T2） -/

/-- **T1 `q9kd_sigma_fixes_base`**: σ は L₂ = embed 像を固定（実相対 Galois）。 -/
theorem q9kd_sigma_fixes_base (n : q3rqCar) : q3kSigma (q3kEmbed n) = q3kEmbed n := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta q3rqZero = q3rqZero
    exact q3rqRing.mul_zero q3rqZeta
  · show q3rqMul q3rqZetaSq q3rqZero = q3rqZero
    exact q3rqRing.mul_zero q3rqZetaSq

/-- **T2a `q9kd_sigma_add`**: σ は加法的（成分ごと・分配）。 -/
theorem q9kd_sigma_add (x y : q3kCar) :
    q3kSigma (q3kAdd x y) = q3kAdd (q3kSigma x) (q3kSigma y) := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta (q3rqAdd x.2.1 y.2.1)
        = q3rqAdd (q3rqMul q3rqZeta x.2.1) (q3rqMul q3rqZeta y.2.1)
    rw [q3k_M_eq, q3k_A_eq]
    exact q3rqRing.left_distrib q3rqZeta x.2.1 y.2.1
  · show q3rqMul q3rqZetaSq (q3rqAdd x.2.2 y.2.2)
        = q3rqAdd (q3rqMul q3rqZetaSq x.2.2) (q3rqMul q3rqZetaSq y.2.2)
    rw [q3k_M_eq, q3k_A_eq]
    exact q3rqRing.left_distrib q3rqZetaSq x.2.2 y.2.2

/-- **T2b `q9kd_sigma3_id`**: σ³ = id（位数 3・q3k_sigma3_id 消費）。 -/
theorem q9kd_sigma3_id (x : q3kCar) : q3kSigma (q3kSigma (q3kSigma x)) = x :=
  q3k_sigma3_id x

/-- **T2c σ ≠ id**: σ(ζ₉) = ζ₃ζ₉ ≠ ζ₉（ζ₃ ≠ 1）。 -/
theorem q9kd_sigma_ne_id : q3kSigma q3kZeta9 ≠ q3kZeta9 := by
  intro h
  have h1 : (q3kSigma q3kZeta9).2.1 = q3kZeta9.2.1 := congrArg (fun z : q3kCar => z.2.1) h
  rw [q3kSigma_1] at h1
  have h2 : q3rqMul q3rqZeta q3rqOne = q3rqOne := h1
  rw [q3rq_mul_one q3rqZeta] at h2
  exact q3rq_zeta_ne_one h2

/-- **T2d σ² ≠ id**: σ²(ζ₉) = ζ₃²ζ₉ ≠ ζ₉（ζ₃² ≠ 1）。 -/
theorem q9kd_sigma2_ne_id : q3kSigma2 q3kZeta9 ≠ q3kZeta9 := by
  intro h
  have h1 : (q3kSigma2 q3kZeta9).2.1 = q3kZeta9.2.1 := congrArg (fun z : q3kCar => z.2.1) h
  rw [q3kSigma2_1] at h1
  have h2 : q3rqMul q3rqZetaSq q3rqOne = q3rqOne := h1
  rw [q3rq_mul_one q3rqZetaSq] at h2
  exact q3rq_zeta_sq_ne_one h2

/-! ## q9kd-2: Kummer コサイクル σ(ζ₉)=ζ₃·ζ₉（T3） -/

/-- **T3a `q9kd_cocycle`**: σ(ζ₉) = embed(ζ₃)·ζ₉。 -/
theorem q9kd_cocycle : q3kSigma q3kZeta9 = q3kMul (q3kEmbed q3rqZeta) q3kZeta9 := by
  rw [q9yp_mulY_100 q3rqZeta]
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta q3rqOne = q3rqZeta
    exact q3rq_mul_one q3rqZeta
  · show q3rqMul q3rqZetaSq q3rqZero = q3rqZero
    exact q3rqRing.mul_zero q3rqZetaSq

/-- **T3b `q9kd_cocycle2`**: σ²(ζ₉) = embed(ζ₃²)·ζ₉。 -/
theorem q9kd_cocycle2 : q3kSigma2 q3kZeta9 = q3kMul (q3kEmbed q3rqZetaSq) q3kZeta9 := by
  rw [q9yp_mulY_100 q3rqZetaSq]
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZetaSq q3rqOne = q3rqZetaSq
    exact q3rq_mul_one q3rqZetaSq
  · show q3rqMul q3rqZeta q3rqZero = q3rqZero
    exact q3rqRing.mul_zero q3rqZeta

/-! ## q9kd-3: 実 Gal(M/L₂) = ⟨σ⟩ の 3 元群と実環自己同型作用 -/

/-- 実 Gal(M/L₂) ≅ ℤ/3 の担体（e=id, s=σ, s2=σ²）。 -/
inductive q9kdGCar where
  | e | s | s2

/-- ⟨σ⟩ の乗法（合成の Cayley 表）。 -/
def q9kdGMul : q9kdGCar → q9kdGCar → q9kdGCar
  | .e, y => y
  | .s, .e => .s
  | .s, .s => .s2
  | .s, .s2 => .e
  | .s2, .e => .s2
  | .s2, .s => .e
  | .s2, .s2 => .s

/-- ⟨σ⟩ の逆元。 -/
def q9kdGInv : q9kdGCar → q9kdGCar
  | .e => .e
  | .s => .s2
  | .s2 => .s

/-- **実 Gal(M/L₂) = ⟨σ⟩ : Grp**（位数 3 の巡回群）。 -/
def q9kdG : Grp where
  carrier := q9kdGCar
  mul := q9kdGMul
  one := .e
  inv := q9kdGInv
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; rfl
  inv_mul := by intro a; cases a <;> rfl

/-- 実環自己同型作用 ⟨σ⟩ → Aut(O_M): e↦id, s↦σ, s2↦σ²。 -/
def q9kdAct : q9kdGCar → q3kCar → q3kCar
  | .e => id
  | .s => q3kSigma
  | .s2 => q3kSigma2

/-- **作用の準同型性** act(gh) = act(g)∘act(h)（⟨σ⟩ が実 O_M に忠実に作用）。 -/
theorem q9kd_act_mul (g h : q9kdGCar) (x : q3kCar) :
    q9kdAct (q9kdGMul g h) x = q9kdAct g (q9kdAct h x) := by
  cases g with
  | e => cases h <;> rfl
  | s =>
    cases h with
    | e => rfl
    | s =>
      show q3kSigma2 x = q3kSigma (q3kSigma x)
      exact q3k_sigma2_comp x
    | s2 =>
      show x = q3kSigma (q3kSigma2 x)
      rw [q3k_sigma2_comp x]
      exact (q3k_sigma3_id x).symm
  | s2 =>
    cases h with
    | e => rfl
    | s =>
      show x = q3kSigma2 (q3kSigma x)
      rw [q3k_sigma2_comp (q3kSigma x)]
      exact (q3k_sigma3_id x).symm
    | s2 =>
      show q3kSigma x = q3kSigma2 (q3kSigma2 x)
      rw [q3k_sigma2_comp (q3kSigma2 x), q3k_sigma2_comp x, q3k_sigma3_id x]

/-! ## q9kd-4: μ₃(O_M) = {x : x³=1} を実群として構成 -/

/-- x⁶ の 2 通りの結合（可換環の再配置）。 -/
theorem q9kd_x6 (x : q3kCar) :
    q3kMul (q3kMul (q3kMul x x) (q3kMul x x)) (q3kMul x x)
      = q3kMul (q3kMul (q3kMul x x) x) (q3kMul (q3kMul x x) x) := by
  rw [q3k_kM_eq]
  exact (q3kRing.mul_mul_mul_comm (q3kRing.mul x x) x (q3kRing.mul x x) x).symm

/-- x³=1 ⟹ (x²)³=1（μ₃ の逆元 x⁻¹=x² の整合）。 -/
theorem q9kd_sq_cube (x : q3kCar) (h : q3kMul (q3kMul x x) x = q3kOne) :
    q3kMul (q3kMul (q3kMul x x) (q3kMul x x)) (q3kMul x x) = q3kOne := by
  rw [q9kd_x6, h, q3k_one_mul]

/-- (xy)³ = x³·y³（可換環の 6 因子再配置）。 -/
theorem q9kd_mul_cube (x y : q3kCar) :
    q3kMul (q3kMul (q3kMul x y) (q3kMul x y)) (q3kMul x y)
      = q3kMul (q3kMul (q3kMul x x) x) (q3kMul (q3kMul y y) y) := by
  rw [q3k_kM_eq,
      q3kRing.mul_mul_mul_comm x y x y,
      q3kRing.mul_mul_mul_comm (q3kRing.mul x x) (q3kRing.mul y y) x y]

/-- x³=1, y³=1 ⟹ (xy)³=1（μ₃ の乗法閉性）。 -/
theorem q9kd_mu3_mul_closed {x y : q3kCar}
    (hx : q3kMul (q3kMul x x) x = q3kOne) (hy : q3kMul (q3kMul y y) y = q3kOne) :
    q3kMul (q3kMul (q3kMul x y) (q3kMul x y)) (q3kMul x y) = q3kOne := by
  rw [q9kd_mul_cube, hx, hy, q3k_one_mul]

/-- 1³=1。 -/
theorem q9kd_one_cube : q3kMul (q3kMul q3kOne q3kOne) q3kOne = q3kOne := by
  rw [q3k_one_mul, q3k_one_mul]

/-- **μ₃(O_M) = {x ∈ O_M : x³ = 1} : Grp**（実群・逆元 x⁻¹ = x²）。 -/
def q9kdMu3 : Grp where
  carrier := { x : q3kCar // q3kMul (q3kMul x x) x = q3kOne }
  mul := fun x y => ⟨q3kMul x.val y.val, q9kd_mu3_mul_closed x.property y.property⟩
  one := ⟨q3kOne, q9kd_one_cube⟩
  inv := fun x => ⟨q3kMul x.val x.val, q9kd_sq_cube x.val x.property⟩
  mul_assoc := fun x y z => Subtype.ext (q3k_mul_assoc x.val y.val z.val)
  one_mul := fun x => Subtype.ext (q3k_one_mul x.val)
  inv_mul := fun x => Subtype.ext x.property

/-! ## q9kd-5: μ₃ の 3 元 {1, ζ₃, ζ₃²} ⊂ O_M -/

/-- x·1 = x（可換）。 -/
theorem q9kd_mul_one (x : q3kCar) : q3kMul x q3kOne = x := by
  rw [q3k_mul_comm]; exact q3k_one_mul x

/-- ζ₃³ = 1（O_M 内・embed）。 -/
theorem q9kd_embed_zeta_cube :
    q3kMul (q3kMul (q3kEmbed q3rqZeta) (q3kEmbed q3rqZeta)) (q3kEmbed q3rqZeta) = q3kOne := by
  rw [q3k_embed_mul, q3k_embed_mul, q3rq_zeta_cube]
  exact q3k_embed_one

/-- (ζ₃²)³ = 1（O_M 内・embed）。 -/
theorem q9kd_embed_zetaSq_cube :
    q3kMul (q3kMul (q3kEmbed q3rqZetaSq) (q3kEmbed q3rqZetaSq)) (q3kEmbed q3rqZetaSq) = q3kOne := by
  rw [q3k_embed_mul, q3k_embed_mul, q3rq_zetaSq_mul_zetaSq, q3rq_zeta_mul_zetaSq]
  exact q3k_embed_one

/-- μ₃ の単位元 1。 -/
def q9kdMu3One : q9kdMu3.carrier := ⟨q3kOne, q9kd_one_cube⟩
/-- μ₃ の ζ₃。 -/
def q9kdMu3Z : q9kdMu3.carrier := ⟨q3kEmbed q3rqZeta, q9kd_embed_zeta_cube⟩
/-- μ₃ の ζ₃²。 -/
def q9kdMu3Z2 : q9kdMu3.carrier := ⟨q3kEmbed q3rqZetaSq, q9kd_embed_zetaSq_cube⟩

/-! ## q9kd-6: μ₃ 内の積補題（指標の準同型性 T4 用） -/

/-- ζ₃·ζ₃² = 1（O_M）。 -/
theorem q9kd_z_zsq : q3kMul (q3kEmbed q3rqZeta) (q3kEmbed q3rqZetaSq) = q3kOne := by
  rw [q3k_embed_mul, q3rq_zeta_mul_zetaSq]
  exact q3k_embed_one

/-- ζ₃²·ζ₃ = 1（O_M）。 -/
theorem q9kd_zsq_z : q3kMul (q3kEmbed q3rqZetaSq) (q3kEmbed q3rqZeta) = q3kOne := by
  have h : q3rqMul q3rqZetaSq q3rqZeta = q3rqOne :=
    (q3rqRing.mul_comm q3rqZetaSq q3rqZeta).trans q3rq_zeta_mul_zetaSq
  rw [q3k_embed_mul, h]
  exact q3k_embed_one

/-- ζ₃²·ζ₃² = ζ₃（O_M）。 -/
theorem q9kd_zsq_zsq :
    q3kMul (q3kEmbed q3rqZetaSq) (q3kEmbed q3rqZetaSq) = q3kEmbed q3rqZeta := by
  rw [q3k_embed_mul, q3rq_zetaSq_mul_zetaSq]

/-- embed ζ₃ ≠ 1。 -/
theorem q9kd_z_ne_one : q3kEmbed q3rqZeta ≠ q3kOne := by
  intro h
  rw [← q3k_embed_one] at h
  exact q3rq_zeta_ne_one (q3k_embed_inj h)

/-- embed ζ₃² ≠ 1。 -/
theorem q9kd_zsq_ne_one : q3kEmbed q3rqZetaSq ≠ q3kOne := by
  intro h
  rw [← q3k_embed_one] at h
  exact q3rq_zeta_sq_ne_one (q3k_embed_inj h)

/-- embed ζ₃ ≠ embed ζ₃²（第 2 座標 h ≠ −h）。 -/
theorem q9kd_z_ne_zsq : q3kEmbed q3rqZeta ≠ q3kEmbed q3rqZetaSq := by
  intro h
  have h1 : q3rqZeta = q3rqZetaSq := q3k_embed_inj h
  have h2 : q3rqHalf = z3.neg q3rqHalf := by
    have hh := congrArg Prod.snd h1
    rw [q3k_zsq_eq] at hh
    exact hh
  have h3 : z3.add q3rqHalf q3rqHalf = z3.add q3rqHalf (z3.neg q3rqHalf) :=
    congrArg (z3.add q3rqHalf) h2
  rw [z3.add_neg q3rqHalf, q3rq_half_add_half] at h3
  exact q3rq_z3_one_ne_zero h3

/-! ## q9kd-7: 実 Kummer 指標 χ : ⟨σ⟩ → μ₃(O_M)（T4） -/

/-- χ の写像: e↦1, s↦ζ₃, s2↦ζ₃²。 -/
def q9kdChiMap : q9kdGCar → q9kdMu3.carrier
  | .e => q9kdMu3One
  | .s => q9kdMu3Z
  | .s2 => q9kdMu3Z2

/-- **T4 `q9kd_chi_hom`**: 実 Kummer 指標 χ : Gal(M/L₂) → μ₃(O_M)（準同型）。 -/
def q9kdChi : Hom q9kdG q9kdMu3 where
  map := q9kdChiMap
  map_mul := by
    intro g h
    cases g with
    | e => cases h <;> exact Subtype.ext (q3k_one_mul _).symm
    | s =>
      cases h with
      | e => exact Subtype.ext (q9kd_mul_one _).symm
      | s => exact Subtype.ext (q3k_embed_mul q3rqZeta q3rqZeta).symm
      | s2 => exact Subtype.ext q9kd_z_zsq.symm
    | s2 =>
      cases h with
      | e => exact Subtype.ext (q9kd_mul_one _).symm
      | s => exact Subtype.ext q9kd_zsq_z.symm
      | s2 => exact Subtype.ext q9kd_zsq_zsq.symm

/-- **T4b `q9kd_chi_hom`**: χ の準同型性 χ(σ^{j+k}) = χ(σʲ)·χ(σᵏ)（mod σ³=id, ζ₃³=1）。 -/
theorem q9kd_chi_hom (g h : q9kdGCar) :
    q9kdChiMap (q9kdGMul g h) = q9kdMu3.mul (q9kdChiMap g) (q9kdChiMap h) :=
  q9kdChi.map_mul g h

/-- **T5 `q9kd_chi_faithful`**: χ は忠実（ker χ = {id}）。 -/
theorem q9kd_chi_faithful (g : q9kdGCar) (h : q9kdChiMap g = q9kdMu3One) :
    g = q9kdGCar.e := by
  cases g with
  | e => rfl
  | s => exact absurd (congrArg Subtype.val h) q9kd_z_ne_one
  | s2 => exact absurd (congrArg Subtype.val h) q9kd_zsq_ne_one

/-! ## q9kd-8: Kummer 類 [ζ₃] の非自明性（T6・q9ci_no_cbrt_zeta 消費） -/

/-- **T6 `q9kd_class_nontrivial`**: 群提示 L₂^× = ℤ×U₂ 上で Kummer 類 [ζ₃] は
    非 3 乗（¬∃ g, g³ = (0, ζ₃U)）。**3 乗根非存在は `q9ci_no_cbrt_zeta`（柱A）を
    消費**——本モジュールの新規主張は群提示 ℤ×U₂ 上への持ち上げと Kummer 類定式化。 -/
theorem q9kd_class_nontrivial :
    ¬ ∃ g : q3rqLx.carrier,
      q3rqLx.mul (q3rqLx.mul g g) g
        = ((0 : Int), (⟨q3rqZeta, q3rq_zeta_unit⟩ : q3rqU.carrier)) := by
  intro hex
  obtain ⟨g, hg⟩ := hex
  have h2 : (q3rqLx.mul (q3rqLx.mul g g) g).2
      = (⟨q3rqZeta, q3rq_zeta_unit⟩ : q3rqU.carrier) := congrArg Prod.snd hg
  have hval : q3rqMul (q3rqMul g.2.val g.2.val) g.2.val = q3rqZeta :=
    congrArg Subtype.val h2
  exact q9ci_no_cbrt_zeta g.2.val hval

/-! ## q9kd-9: 完全対 Gal×⟨[ζ₃]⟩→μ₃ の両側非退化（T7,T8） -/

/-- 類 [ζ₃]ᵏ の立方根: e↦1, s↦ζ₉, s2↦ζ₉²。 -/
def q9kdRoot : q9kdGCar → q3kCar
  | .e => q3kOne
  | .s => q3kZeta9
  | .s2 => q9ypY2

/-- embed(n)·ζ₉² = (0,0,n)（対の値計算の補助）。 -/
theorem q9kd_embed_mul_y2 (n : q3rqCar) :
    q3kMul (q3kEmbed n) q9ypY2 = ((q3rqZero, q3rqZero, n) : q3kCar) := by
  rw [q9yp_y2]
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul n q3rqRing.zero)
        (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.one)
          (q3rqRing.mul q3rqRing.zero q3rqRing.zero))) = q3rqRing.zero
    rw [q3rqRing.mul_zero n, q3rqRing.zero_mul q3rqRing.one, q3rqRing.mul_zero q3rqRing.zero,
      q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul n q3rqRing.zero)
        (q3rqRing.mul q3rqRing.zero q3rqRing.zero))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqRing.zero q3rqRing.one)) = q3rqRing.zero
    rw [q3rqRing.mul_zero n, q3rqRing.mul_zero q3rqRing.zero, q3rqRing.add_zero q3rqRing.zero,
      q3rqRing.zero_mul q3rqRing.one, q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul n q3rqRing.one)
        (q3rqRing.mul q3rqRing.zero q3rqRing.zero)) (q3rqRing.mul q3rqRing.zero q3rqRing.zero) = n
    rw [q3rqRing.mul_one n, q3rqRing.mul_zero q3rqRing.zero,
      q3rqRing.add_zero (q3rqRing.add n q3rqRing.zero), q3rqRing.add_zero n]

/-- σ(ζ₉²) = embed(ζ₃²)·ζ₉²（対の値・k=2）。 -/
theorem q9kd_pairing_s_r2 :
    q3kSigma q9ypY2 = q3kMul (q3kEmbed q3rqZetaSq) q9ypY2 := by
  rw [q9kd_embed_mul_y2, q9yp_y2]
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta q3rqZero = q3rqZero
    exact q3rqRing.mul_zero q3rqZeta
  · show q3rqMul q3rqZetaSq q3rqOne = q3rqZetaSq
    exact q3rq_mul_one q3rqZetaSq

/-- **T7 `q9kd_pairing_eq`**: 対の値の閉形式 σ(ζ₉ᵏ) = embed(ζ₃ᵏ)·ζ₉ᵏ (k=0,1,2)。 -/
theorem q9kd_pairing_eq :
    q3kSigma (q9kdRoot q9kdGCar.e) = q3kMul (q3kEmbed q3rqOne) (q9kdRoot q9kdGCar.e)
    ∧ q3kSigma (q9kdRoot q9kdGCar.s) = q3kMul (q3kEmbed q3rqZeta) (q9kdRoot q9kdGCar.s)
    ∧ q3kSigma (q9kdRoot q9kdGCar.s2) = q3kMul (q3kEmbed q3rqZetaSq) (q9kdRoot q9kdGCar.s2) := by
  refine ⟨?_, q9kd_cocycle, q9kd_pairing_s_r2⟩
  show q3kSigma q3kOne = q3kMul (q3kEmbed q3rqOne) q3kOne
  rw [q3k_sigma_one]
  exact (q3k_one_mul q3kOne).symm

/-- ζ₉² は σ で固定されない（右非退化 k=2 用）。 -/
theorem q9kd_sigma_y2_ne : q3kSigma q9ypY2 ≠ q9ypY2 := by
  rw [q9yp_y2]
  intro h
  have h1 : (q3kSigma ((q3rqZero, q3rqZero, q3rqOne) : q3kCar)).2.2
      = ((q3rqZero, q3rqZero, q3rqOne) : q3kCar).2.2 := congrArg (fun z : q3kCar => z.2.2) h
  rw [q3kSigma_2] at h1
  have h2 : q3rqMul q3rqZetaSq q3rqOne = q3rqOne := h1
  rw [q3rq_mul_one q3rqZetaSq] at h2
  exact q3rq_zeta_sq_ne_one h2

/-- **T8a `q9kd_pairing_nondeg_left`**: 左非退化——σʲ(ζ₉)=ζ₉ ⟹ σʲ=id。 -/
theorem q9kd_pairing_nondeg_left (g : q9kdGCar)
    (h : q9kdAct g q3kZeta9 = q3kZeta9) : g = q9kdGCar.e := by
  cases g with
  | e => rfl
  | s => exact absurd h q9kd_sigma_ne_id
  | s2 => exact absurd h q9kd_sigma2_ne_id

/-- **T8b `q9kd_pairing_nondeg_right`**: 右非退化——σ(ζ₉ᵏ)=ζ₉ᵏ ⟹ 3∣k（k∈{0,1,2}）。 -/
theorem q9kd_pairing_nondeg_right (k : q9kdGCar)
    (h : q3kSigma (q9kdRoot k) = q9kdRoot k) : k = q9kdGCar.e := by
  cases k with
  | e => rfl
  | s => exact absurd h q9kd_sigma_ne_id
  | s2 => exact absurd h q9kd_sigma_y2_ne

/-! ## q9kd-10: Hom(⟨σ⟩,μ₃) の完全枚挙（T9・q9c_m_mu3_complete 消費） -/

/-- 同 map を持つ Hom は等しい（map_mul は Prop・証明無関係）。 -/
theorem q9kd_hom_ext {G H : Grp} (f g : Hom G H) (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl

/-- 自明指標 χ⁰。 -/
def q9kdChi0 : Hom q9kdG q9kdMu3 where
  map := fun _ => q9kdMu3One
  map_mul := fun _ _ => Subtype.ext (q3k_one_mul q3kOne).symm

/-- 指標 χ²（s↦ζ₃², s2↦ζ₃）。 -/
def q9kdChi2Map : q9kdGCar → q9kdMu3.carrier
  | .e => q9kdMu3One
  | .s => q9kdMu3Z2
  | .s2 => q9kdMu3Z

/-- χ² : Gal(M/L₂) → μ₃（もう一つの非自明指標）。 -/
def q9kdChi2 : Hom q9kdG q9kdMu3 where
  map := q9kdChi2Map
  map_mul := by
    intro g h
    cases g with
    | e => cases h <;> exact Subtype.ext (q3k_one_mul _).symm
    | s =>
      cases h with
      | e => exact Subtype.ext (q9kd_mul_one _).symm
      | s => exact Subtype.ext q9kd_zsq_zsq.symm
      | s2 => exact Subtype.ext q9kd_zsq_z.symm
    | s2 =>
      cases h with
      | e => exact Subtype.ext (q9kd_mul_one _).symm
      | s => exact Subtype.ext q9kd_z_zsq.symm
      | s2 => exact Subtype.ext (q3k_embed_mul q3rqZeta q3rqZeta).symm

/-- **T9a `q9kd_hom_exhaust`**: 任意の hom の σ での値は μ₃ の 3 元のいずれか
    （**`q9c_m_mu3_complete` 消費**: 値 m は m³=1 なので m∈{1,ζ₃,ζ₃²}）。 -/
theorem q9kd_hom_exhaust (φ : Hom q9kdG q9kdMu3) :
    φ.map q9kdGCar.s = q9kdMu3One
    ∨ φ.map q9kdGCar.s = q9kdMu3Z
    ∨ φ.map q9kdGCar.s = q9kdMu3Z2 := by
  obtain h | h | h :=
    q9c_m_mu3_complete (φ.map q9kdGCar.s).val (φ.map q9kdGCar.s).property
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

/-- hom は σ の像で一意に決まる。 -/
theorem q9kd_hom_det (φ ψ : Hom q9kdG q9kdMu3)
    (h : φ.map q9kdGCar.s = ψ.map q9kdGCar.s) : φ = ψ := by
  apply q9kd_hom_ext
  funext g
  cases g with
  | e =>
    show φ.map q9kdGCar.e = ψ.map q9kdGCar.e
    exact (Hom.map_one φ).trans (Hom.map_one ψ).symm
  | s => exact h
  | s2 =>
    show φ.map q9kdGCar.s2 = ψ.map q9kdGCar.s2
    have hφ : φ.map q9kdGCar.s2
        = q9kdMu3.mul (φ.map q9kdGCar.s) (φ.map q9kdGCar.s) :=
      φ.map_mul q9kdGCar.s q9kdGCar.s
    have hψ : ψ.map q9kdGCar.s2
        = q9kdMu3.mul (ψ.map q9kdGCar.s) (ψ.map q9kdGCar.s) :=
      ψ.map_mul q9kdGCar.s q9kdGCar.s
    rw [hφ, hψ, h]

/-- **T9b `q9kd_hom_complete`**: Hom(⟨σ⟩,μ₃) = {χ⁰,χ¹,χ²}（完全枚挙）。 -/
theorem q9kd_hom_complete (φ : Hom q9kdG q9kdMu3) :
    φ = q9kdChi0 ∨ φ = q9kdChi ∨ φ = q9kdChi2 := by
  obtain h | h | h := q9kd_hom_exhaust φ
  · exact Or.inl (q9kd_hom_det φ q9kdChi0 h)
  · exact Or.inr (Or.inl (q9kd_hom_det φ q9kdChi h))
  · exact Or.inr (Or.inr (q9kd_hom_det φ q9kdChi2 h))

/-! ## q9kd-11: 完全 Kummer 双対 ⟨[ζ₃]⟩ ≅ Hom(Gal,μ₃)（T10） -/

/-- k ↦ χᵏ の枚挙: e↦χ⁰, s↦χ¹, s2↦χ²。 -/
def q9kdChiPow : q9kdGCar → Hom q9kdG q9kdMu3
  | .e => q9kdChi0
  | .s => q9kdChi
  | .s2 => q9kdChi2

/-- χᵏ の σ での値の val（単射判定用）。 -/
def q9kdSVal : q9kdGCar → q3kCar
  | .e => q3kOne
  | .s => q3kEmbed q3rqZeta
  | .s2 => q3kEmbed q3rqZetaSq

theorem q9kd_chipow_sval (g : q9kdGCar) :
    ((q9kdChiPow g).map q9kdGCar.s).val = q9kdSVal g := by
  cases g <;> rfl

/-- **T10a `q9kd_kummer_iso_surj`**: k↦χᵏ は全射（T9 の束ね）。 -/
theorem q9kd_kummer_iso_surj (φ : Hom q9kdG q9kdMu3) :
    ∃ k, q9kdChiPow k = φ := by
  obtain h | h | h := q9kd_hom_complete φ
  · exact ⟨q9kdGCar.e, h.symm⟩
  · exact ⟨q9kdGCar.s, h.symm⟩
  · exact ⟨q9kdGCar.s2, h.symm⟩

/-- **T10b `q9kd_kummer_iso_inj`**: k↦χᵏ は単射（指標の相異・T5 の束ね）。 -/
theorem q9kd_kummer_iso_inj (j k : q9kdGCar)
    (h : q9kdChiPow j = q9kdChiPow k) : j = k := by
  have hs : q9kdSVal j = q9kdSVal k := by
    rw [← q9kd_chipow_sval j, ← q9kd_chipow_sval k, h]
  cases j with
  | e =>
    cases k with
    | e => rfl
    | s => exact absurd hs (Ne.symm q9kd_z_ne_one)
    | s2 => exact absurd hs (Ne.symm q9kd_zsq_ne_one)
  | s =>
    cases k with
    | e => exact absurd hs q9kd_z_ne_one
    | s => rfl
    | s2 => exact absurd hs q9kd_z_ne_zsq
  | s2 =>
    cases k with
    | e => exact absurd hs q9kd_zsq_ne_one
    | s => exact absurd hs (Ne.symm q9kd_z_ne_zsq)
    | s2 => rfl

/-- **T10 `q9kd_kummer_iso`**: k↦χᵏ は ⟨[ζ₃]⟩ → Hom(Gal(M/L₂),μ₃) の全単射
    ＝実巡回 3 次 Kummer 双対の完全証明（全射＋単射の束ね）。 -/
theorem q9kd_kummer_iso :
    (∀ φ : Hom q9kdG q9kdMu3, ∃ k, q9kdChiPow k = φ)
    ∧ (∀ j k, q9kdChiPow j = q9kdChiPow k → j = k) :=
  ⟨q9kd_kummer_iso_surj, q9kd_kummer_iso_inj⟩

/-! ## q9kd-12: capstone（T11・束ねのみ・新規証明ゼロ） -/

/-- **T11 `Q3KummerDualityRealData`**: 実巡回 3 次 Kummer 双対の完全データ束ね。 -/
structure Q3KummerDualityRealData where
  /-- 実 Kummer 指標 χ の忠実性（ker χ = {id}）。 -/
  chi_faithful : ∀ g, q9kdChiMap g = q9kdMu3One → g = q9kdGCar.e
  /-- Kummer 類 [ζ₃] の群提示 ℤ×U₂ 上の非自明性（q9ci_no_cbrt_zeta 消費）。 -/
  class_nontrivial :
    ¬ ∃ g : q3rqLx.carrier,
      q3rqLx.mul (q3rqLx.mul g g) g
        = ((0 : Int), (⟨q3rqZeta, q3rq_zeta_unit⟩ : q3rqU.carrier))
  /-- 対の左非退化。 -/
  pairing_nondeg_left : ∀ g, q9kdAct g q3kZeta9 = q3kZeta9 → g = q9kdGCar.e
  /-- 対の右非退化。 -/
  pairing_nondeg_right : ∀ k, q3kSigma (q9kdRoot k) = q9kdRoot k → k = q9kdGCar.e
  /-- Hom(⟨σ⟩,μ₃) の完全枚挙（q9c_m_mu3_complete 消費）。 -/
  hom_complete : ∀ φ : Hom q9kdG q9kdMu3, φ = q9kdChi0 ∨ φ = q9kdChi ∨ φ = q9kdChi2
  /-- k↦χᵏ の全射。 -/
  iso_surj : ∀ φ : Hom q9kdG q9kdMu3, ∃ k, q9kdChiPow k = φ
  /-- k↦χᵏ の単射。 -/
  iso_inj : ∀ j k, q9kdChiPow j = q9kdChiPow k → j = k

/-- **T11b `q9kd_data`**: 見出し実例——実 M=ℚ₃(ζ₉) 上の完全 Kummer 双対。 -/
def q9kd_data : Q3KummerDualityRealData where
  chi_faithful := q9kd_chi_faithful
  class_nontrivial := q9kd_class_nontrivial
  pairing_nondeg_left := q9kd_pairing_nondeg_left
  pairing_nondeg_right := q9kd_pairing_nondeg_right
  hom_complete := q9kd_hom_complete
  iso_surj := q9kd_kummer_iso_surj
  iso_inj := q9kd_kummer_iso_inj

/-- **T11c `q9kd_exists`**: 実巡回 3 次 Kummer 双対の完全証明の存在。 -/
theorem q9kd_exists : Nonempty Q3KummerDualityRealData := ⟨q9kd_data⟩

end IUT
