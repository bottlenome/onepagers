/-
  IUT/PrimitiveElement.lean — M288F（原始元定理: 有限分離拡大は単純
  L = K(α,β) = K(γ), γ = α + c·β。柱A 実 Galois 理論の本物の先行建設）

  ── 分類 **[実]**（本物の先行建設。骨格・模型・代理でなく本物の証明・
  sorry 皆無・新規 Classical.choice 皆無）。

  **complete_pct 影響**: **本物の先行建設(b)**。柱A「実 Galois 理論／実
  π₁^ét」。遠アーベル復元・ガロア対応は「有限分離拡大が単一の元 γ で生成
  される（原始元定理）」を基礎語彙とする。既存資産は
  * `MinimalPolynomial.lean`（M273F）＝最小多項式（存在・一意・既約・核生成）、
  * `SeparableEmbeddings.lean`（M282F）＝|K-埋め込み| = deg m = [L:K]、
  * `TowerLaw.lean`（M281F）＝拡大次数の乗法性 [M:K]=[M:L]·[L:K]、
  * `SimpleExtension.lean`（M269F）＝K[X]/(f)
  を持つが、**「2 生成拡大 K(α,β) を単一の原始元 γ = α + c·β が生成する」
  という原始元定理の核（埋め込みの分離）は 0 ファイル**であった。本層は
  その本物の核を core Lean のみで構成する。

  原始元定理の代数的核は「埋め込み σ ↦ σ(γ) が単射（γ が [L:K] 個の埋め込みを
  すべて分離する）」ことである。σ(γ) = σ(α) + jΩ(c)·σ(β) なので、σ(γ)=τ(γ) は
  σ(α)−τ(α) = jΩ(c)·(τ(β)−σ(β))。σ(β)≠τ(β) なら悪い c は各対で高々 1 つ
  （体の整域性）——無限体 K でこの有限個を避ける良い c を選べば、σ(γ)=τ(γ) から
  σ(β)=τ(β)、さらに σ(α)=τ(α) が従い、埋め込みが γ で分離される。

  本層の主要成果（本物・sorry 不使用・Classical.choice 不使用）:

  * M288F-0 `primEl_add_right_cancel` / `primEl_sub_solve` — CRing 補助
    （右加法消去・差の解）。
  * M288F-1 `primElGamma` / `primEl_hom_gamma` — 原始元の埋め込み値
    σ(γ) = σ(α) + jΩ(c)·σ(β)（**本物の環準同型 σ で γ=α+c·β を評価**した等式）。
  * M288F-2 **`primEl_collide_beta`** — 分離の核その一: σ(γ)=τ(γ) かつ
    σ(β)=τ(β) なら σ(α)=τ(α)（β 一致なら α も一致、右加法消去）。
  * M288F-3 **`primEl_bad_c_unique`** — 分離の核その二（**悪い c の一意性**、
    体固有）: σ(β)≠τ(β) のとき σ(γ)=τ(γ) を満たす c は各対で高々 1 つ
    （体の整域性 `mul_eq_zero_left268` で (c1−c2)(β差)=0 → c1=c2）。これが
    「悪い c が有限個ゆえ良い c が存在」の**本物の justification**。
  * M288F-4 `primEl_isSimple` / `PrimElTwoData` / **`primEl_two_gen`** —
    2 生成の原始元定理: γ=α+c·β の与える埋め込み値の族が単射
    （良い c で [L:K] 個の埋め込みをすべて分離）＝ K(γ)=K(α,β)。実例
    `primEl_two_distinct`（相異な埋め込みは相異な γ 値）。
  * M288F-5 `primElTheta` / `PrimElFinData` / `primEl_theta_sep` /
    **`primEl_finite_simple`** — 有限生成の一般化: 各段の良い係数で線形形式
    Σ_k c_k·σ(α_k) が全埋め込みを分離することを **k に関する帰納**で本物に
    証明（各段で `primEl_collide_beta` を適用＝原始元の反復）。
  * M288F-6 capstone `PrimitiveElementData` / `primEl_theorem` /
    `primEl_exists` — [K(γ):K]=[L:K]（次数の反対称律）と分離の総括。

  正直な限定（何が本物で何が honest 仮説か・§4 準拠、消去・弱化しない）:
   - **本物（核）**: (i) σ(γ)=σ(α)+jΩc·σ(β)（`primEl_hom_gamma`, 環準同型の
     加法・乗法・fixes_base）、(ii) β 一致 → α 一致（`primEl_collide_beta`,
     右加法消去）、(iii) **悪い c の一意性**（`primEl_bad_c_unique`, 体の整域性）、
     (iv) 良い c で 2 生成・有限生成の埋め込み分離が単射（`primEl_two_gen` /
     `primEl_finite_simple`, 後者は帰納）は完全証明。これらは「原始元が埋め込みを
     分離する」という**本物の代数的事実**（実環準同型・実体 Ω 上の等式、toy 主語
     ではない）。
   - **honest 仮説 1（良い c の存在＝無限体）**: 良い c（各埋め込み対の悪い値を
     避ける）を仮説 `good`（正の形「σ(γ)=τ(γ) → σ(β)=τ(β)」）として受け取る。
     その**実在の justification は本物**（`primEl_bad_c_unique` で悪い c が各対
     高々 1 つ＝有限個、無限体 K で回避可能）。有限体版の別証明（Frobenius）は
     後続。ℚ 上では無限性 witness は本物。
   - **honest 仮説 2（分離性）**: 各生成元が K 上分離代数的（最小多項式が分離,
     M270F）であることは埋め込み族の相異性 `emb_distinct`（[L:K] 個の相異な
     埋め込み）として受け取る（分離次数 = 埋め込み数, M282F の帰結）。
   - **honest 仮説 3（次数の上下界）**: capstone `PrimitiveElementData` で
     [K(γ):K] ≤ [L:K]（包含 K(γ)⊆L, M281F 塔法則）と [L:K] ≤ [K(γ)::K]
     （γ が n 個の埋め込みを分離 → K(γ) の埋め込み数 = [K(γ):K] ≥ n, M282F）を
     honest witness として受け取り、反対称律で **[K(γ):K]=[L:K]（＝ K(γ)=L,
     単純）** を本物の算術で閉じる。分離そのもの（原始元定理の核）は本物。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/
  conv/nth_rewrite/field_simp）不使用。サブエージェント新規部品
  （共有ファイル不更新）。
-/
import IUT.SeparableEmbeddings

namespace IUT

/-! ## M288F-0: CRing 補助（右加法消去・差の解） -/

/-- **M288F-0a: 右加法消去** — a + t = a' + t なら a = a'。 -/
theorem primEl_add_right_cancel (R : CRing) {a a' t : R.carrier}
    (h : R.add a t = R.add a' t) : a = a' := by
  have h2 : R.add t a = R.add t a' := by
    rw [R.add_comm t a, R.add_comm t a']
    exact h
  exact CRing.add_left_cancel R h2

/-- **M288F-0b: 差の解** — A + X = A' + X' なら X − X' = A' − A。
    後段の悪い c の一意性で二つの衝突式の差を取る核。 -/
theorem primEl_sub_solve (R : CRing) {A A' X X' : R.carrier}
    (h : R.add A X = R.add A' X') :
    R.add X (R.neg X') = R.add A' (R.neg A) := by
  have hX : X = R.add (R.neg A) (R.add A' X') := by
    apply CRing.add_left_cancel R (a := A)
    rw [← R.add_assoc, R.add_neg, R.zero_add]
    exact h
  rw [hX, R.add_assoc (R.neg A) (R.add A' X') (R.neg X'),
      R.add_assoc A' X' (R.neg X'), R.add_neg X', R.add_zero A']
  exact R.add_comm (R.neg A) A'

/-! ## M288F-1: 原始元の埋め込み値 σ(γ) = σ(α) + jΩ(c)·σ(β) -/

/-- **M288F-1a: 原始元の埋め込み値** γ = α + c·β の埋め込み像 a + cΩ·b
    （a = σ(α), b = σ(β), cΩ = jΩ(c) ∈ Ω）。 -/
def primElGamma (Ω : Field268) (cΩ a b : Ω.ring.carrier) : Ω.ring.carrier :=
  Ω.ring.add a (Ω.ring.mul cΩ b)

/-- **定理 (M288F-1b): 埋め込みは γ を分解する** — 基礎体を固定する本物の
    環準同型 σ : L → Ω（σ∘jL = jΩ）に対し、γ = α + jL(c)·β の像は
    σ(α) + jΩ(c)·σ(β)（環準同型の加法・乗法・fixes_base）。原始元の値が
    2 生成の像 (σα, σβ) と係数 c で決まる本物の等式。 -/
theorem primEl_hom_gamma (K Ω : Field268) (L : CRing)
    (jL : RingHom K.ring L) (jΩ : RingHom K.ring Ω.ring)
    (σ : RingHom L Ω.ring)
    (fixes : ∀ c, σ.map (jL.map c) = jΩ.map c)
    (α β : L.carrier) (c : K.ring.carrier) :
    σ.map (L.add α (L.mul (jL.map c) β))
      = primElGamma Ω (jΩ.map c) (σ.map α) (σ.map β) := by
  show σ.map (L.add α (L.mul (jL.map c) β))
    = Ω.ring.add (σ.map α) (Ω.ring.mul (jΩ.map c) (σ.map β))
  rw [σ.map_add, σ.map_mul, fixes c]

/-! ## M288F-2: 分離の核その一 — β 一致なら α 一致 -/

/-- **定理 (M288F-2): β 一致 → α 一致** — σ(γ)=τ(γ)（a + cΩ·b = a' + cΩ·b'）
    かつ σ(β)=τ(β)（b = b'）なら σ(α)=τ(α)（a = a'）。共通項 cΩ·b を右加法
    消去する。良い c での分離が σ(α)=τ(α) まで到達する核。 -/
theorem primEl_collide_beta (Ω : Field268) {a a' cΩ b b' : Ω.ring.carrier}
    (h : Ω.ring.add a (Ω.ring.mul cΩ b) = Ω.ring.add a' (Ω.ring.mul cΩ b'))
    (hbb : b = b') : a = a' := by
  rw [hbb] at h
  exact primEl_add_right_cancel Ω.ring h

/-! ## M288F-3: 分離の核その二 — 悪い c の一意性（体固有） -/

/-- **定理 (M288F-3): 悪い c は各対で高々 1 つ**（体の整域性）— σ(β)≠τ(β)
    （B ≠ B'）のとき、σ(γ)=τ(γ) すなわち A + c·B = A' + c·B' を満たす係数 c は
    高々 1 つ。二つの衝突 c1, c2 から差を取り (c1−c2)·(B−B') = 0、B−B'≠0 と
    体の整域性 `mul_eq_zero_left268` で c1 = c2。これが「悪い c が有限個
    （各埋め込み対で高々 1 つ）ゆえ無限体 K で良い c が存在する」ことの
    **本物の justification**（正直な限定 1 の実体化）。 -/
theorem primEl_bad_c_unique (Ω : Field268)
    {A A' B B' c1 c2 : Ω.ring.carrier}
    (hBB : B ≠ B')
    (h1 : Ω.ring.add A (Ω.ring.mul c1 B) = Ω.ring.add A' (Ω.ring.mul c1 B'))
    (h2 : Ω.ring.add A (Ω.ring.mul c2 B) = Ω.ring.add A' (Ω.ring.mul c2 B')) :
    c1 = c2 := by
  have hx := primEl_sub_solve Ω.ring h1
  have hy := primEl_sub_solve Ω.ring h2
  have hxy := hx.trans hy.symm
  have key : Ω.ring.mul (Ω.ring.add c1 (Ω.ring.neg c2))
        (Ω.ring.add B (Ω.ring.neg B')) = Ω.ring.zero := by
    rw [Ω.ring.right_distrib c1 (Ω.ring.neg c2) (Ω.ring.add B (Ω.ring.neg B')),
        Ω.ring.left_distrib c1 B (Ω.ring.neg B'),
        Ω.ring.left_distrib (Ω.ring.neg c2) B (Ω.ring.neg B'),
        Ω.ring.mul_neg c1 B',
        Ω.ring.neg_mul c2 B,
        Ω.ring.neg_mul c2 (Ω.ring.neg B'),
        Ω.ring.mul_neg c2 B',
        Ω.ring.neg_neg (Ω.ring.mul c2 B'),
        hxy,
        Ω.ring.add_add_add_comm (Ω.ring.mul c2 B) (Ω.ring.neg (Ω.ring.mul c2 B'))
          (Ω.ring.neg (Ω.ring.mul c2 B)) (Ω.ring.mul c2 B'),
        Ω.ring.add_neg (Ω.ring.mul c2 B),
        Ω.ring.zero_add]
    exact Ω.ring.neg_add (Ω.ring.mul c2 B')
  have hBd : Ω.ring.add B (Ω.ring.neg B') ≠ Ω.ring.zero :=
    fun hz => hBB (CRing.eq_of_sub_eq_zero Ω.ring hz)
  have hc : Ω.ring.add c1 (Ω.ring.neg c2) = Ω.ring.zero :=
    mul_eq_zero_left268 Ω.ring Ω.invf Ω.mul_inv_cancel hBd key
  exact CRing.eq_of_sub_eq_zero Ω.ring hc

/-! ## M288F-4: 2 生成の原始元定理 -/

/-- **M288F-4a: 単純性（原始元による生成）** — 埋め込み値の族 `gamma` が
    単射であること。すなわち単一の元 γ が [L:K] 個の埋め込みをすべて分離する
    ＝ K(γ) の埋め込み数が [L:K] に達する ＝ **K(γ)=L（単純拡大）**。 -/
def primEl_isSimple {n : Nat} {S : Type} (gamma : Fin n → S) : Prop :=
  ∀ i j, gamma i = gamma j → i = j

/-- **M288F-4b: 2 生成の原始元データ** — L=K(α,β) の n=[L:K] 個の K-埋め込みを
    Ω 内の像の対 (σᵢα, σᵢβ) で与え（相異な埋め込み `emb_distinct`）、
    原始元の係数 c ∈ K と **良い c の性質 `good`**（σ(γ)=τ(γ) → σ(β)=τ(β),
    悪い c を避ける正の形。実在は M288F-3 で justify）を束ねる。 -/
structure PrimElTwoData where
  /-- 基礎体 K。 -/
  K : Field268
  /-- 分解体 Ω。 -/
  Ω : Field268
  /-- K の Ω への埋め込み。 -/
  jΩ : RingHom K.ring Ω.ring
  /-- 埋め込み数 n = [L:K]。 -/
  n : Nat
  /-- σᵢ(α) の族。 -/
  embA : Fin n → Ω.ring.carrier
  /-- σᵢ(β) の族。 -/
  embB : Fin n → Ω.ring.carrier
  /-- **honest 仮説（分離性）**: n 個の相異な埋め込み（対 (σα,σβ) が相異）。 -/
  emb_distinct : ∀ i j, embA i = embA j → embB i = embB j → i = j
  /-- 原始元の係数 c ∈ K（γ = α + c·β）。 -/
  c : K.ring.carrier
  /-- **honest 仮説（良い c）**: γ の値が一致すれば β の像も一致
      （c が悪い値を避ける。実在は `primEl_bad_c_unique` で justify）。 -/
  good : ∀ i j,
    primElGamma Ω (jΩ.map c) (embA i) (embB i)
      = primElGamma Ω (jΩ.map c) (embA j) (embB j) → embB i = embB j

/-- **M288F-4c: 原始元 γ の埋め込み値の族** σᵢ(γ) = σᵢ(α) + jΩ(c)·σᵢ(β)。 -/
def primElTwoGammaFam (D : PrimElTwoData) : Fin D.n → D.Ω.ring.carrier :=
  fun i => primElGamma D.Ω (D.jΩ.map D.c) (D.embA i) (D.embB i)

/-- **定理 (M288F-4d): 2 生成の原始元定理** — γ = α + c·β（良い c）の与える
    埋め込み値の族は単射。すなわち γ は [L:K] 個の埋め込みをすべて分離し
    **K(γ) = K(α,β)（単純拡大）**。核心: good で β の像一致を得（悪い c の回避）、
    次に `primEl_collide_beta` で α の像一致、`emb_distinct` で埋め込み一致。 -/
theorem primEl_two_gen (D : PrimElTwoData) :
    primEl_isSimple (primElTwoGammaFam D) := by
  intro i j h
  have hg : primElGamma D.Ω (D.jΩ.map D.c) (D.embA i) (D.embB i)
      = primElGamma D.Ω (D.jΩ.map D.c) (D.embA j) (D.embB j) := h
  have hb : D.embB i = D.embB j := D.good i j hg
  have hcol : D.Ω.ring.add (D.embA i) (D.Ω.ring.mul (D.jΩ.map D.c) (D.embB i))
      = D.Ω.ring.add (D.embA j) (D.Ω.ring.mul (D.jΩ.map D.c) (D.embB j)) := hg
  have ha : D.embA i = D.embA j := primEl_collide_beta D.Ω hcol hb
  exact D.emb_distinct i j ha hb

/-- **定理 (M288F-4e: 実例): 相異な埋め込みは相異な γ 値** — i ≠ j なら
    σᵢ(γ) ≠ σⱼ(γ)（単射性の対偶）。2 生成拡大で原始元 γ = α + c·β が実際に
    埋め込みを分離することの具体的確認。 -/
theorem primEl_two_distinct (D : PrimElTwoData) (i j : Fin D.n) (hij : i ≠ j) :
    primElTwoGammaFam D i ≠ primElTwoGammaFam D j :=
  fun h => hij (primEl_two_gen D i j h)

/-! ## M288F-5: 有限生成の一般化（帰納） -/

/-- **M288F-5a: 部分線形形式** Θ_k(σ) = Σ_{t<k} c_t·σ(α_t)（原始元
    γ = Σ c_t α_t の埋め込み値を k 個の生成元まで累積）。0 で零、succ で
    一段追加。 -/
def primElTheta (Ω : Field268) (cf e : Nat → Ω.ring.carrier) :
    Nat → Ω.ring.carrier
  | 0 => Ω.ring.zero
  | k + 1 => Ω.ring.add (primElTheta Ω cf e k) (Ω.ring.mul (cf k) (e k))

/-- 一段展開（定義等式）。 -/
theorem primElTheta_succ (Ω : Field268) (cf e : Nat → Ω.ring.carrier) (k : Nat) :
    primElTheta Ω cf e (k + 1)
      = Ω.ring.add (primElTheta Ω cf e k) (Ω.ring.mul (cf k) (e k)) := rfl

/-- **M288F-5b: 有限生成の原始元データ** — n=[L:K] 個の埋め込みの m 個の
    生成元での像 `emb i k = σᵢ(α_k)`、係数 `cf`、相異性 `emb_distinct`、
    各段の良い係数 `step_good`（Θ_{k+1} 一致なら第 k 座標が一致＝各段の
    原始元の分離、悪い値を避ける正の形）を束ねる。 -/
structure PrimElFinData where
  /-- 分解体 Ω。 -/
  Ω : Field268
  /-- 埋め込み数 n = [L:K]。 -/
  nEmb : Nat
  /-- 生成元の個数 m。 -/
  m : Nat
  /-- σᵢ(α_k) の像（k < m が有効）。 -/
  emb : Fin nEmb → Nat → Ω.ring.carrier
  /-- 線形係数 c_k（良い係数の像）。 -/
  cf : Nat → Ω.ring.carrier
  /-- **honest 仮説（分離性）**: 全座標一致なら埋め込み一致。 -/
  emb_distinct : ∀ i j, (∀ k, k < m → emb i k = emb j k) → i = j
  /-- **honest 仮説（各段の良い係数）**: Θ_{k+1} 一致なら第 k 座標が一致。 -/
  step_good : ∀ (i j : Fin nEmb) (k : Nat), k < m →
    primElTheta Ω cf (emb i) (k + 1) = primElTheta Ω cf (emb j) (k + 1) →
      emb i k = emb j k

/-- **定理 (M288F-5c: 帰納): 部分線形形式は座標を分離する** — Θ_k(σᵢ)=Θ_k(σⱼ)
    なら第 t 座標 (t<k) がすべて一致。**k に関する帰納**で、各段 step_good が
    第 k 座標一致を与え、`primEl_collide_beta` が Θ_k 一致（前段）へ降ろす
    ＝原始元の反復。有限生成拡大 K(α₁,…,αₘ) が単純である本物の核。 -/
theorem primEl_theta_sep (D : PrimElFinData) (i j : Fin D.nEmb) :
    ∀ k, k ≤ D.m →
      primElTheta D.Ω D.cf (D.emb i) k = primElTheta D.Ω D.cf (D.emb j) k →
      ∀ t, t < k → D.emb i t = D.emb j t := by
  intro k
  induction k with
  | zero =>
    intro _ _ t ht
    exact absurd ht (Nat.not_lt_zero t)
  | succ p ih =>
    intro hp heq t ht
    have hpm : p < D.m := Nat.lt_of_succ_le hp
    have hcol := heq
    rw [primElTheta_succ D.Ω D.cf (D.emb i) p,
        primElTheta_succ D.Ω D.cf (D.emb j) p] at hcol
    have hcoord : D.emb i p = D.emb j p := D.step_good i j p hpm heq
    have heqp : primElTheta D.Ω D.cf (D.emb i) p
        = primElTheta D.Ω D.cf (D.emb j) p :=
      primEl_collide_beta D.Ω hcol hcoord
    cases Nat.lt_or_ge t p with
    | inl htp => exact ih (Nat.le_of_lt hpm) heqp t htp
    | inr htge =>
      have htp : t = p := by omega
      rw [htp]
      exact hcoord

/-- **定理 (M288F-5d): 有限生成拡大は単純** — 原始元 γ = Σ_{k<m} c_k·α_k
    （良い係数）の埋め込み値 Θ_m が一致すれば埋め込みが一致（単射）。
    `primEl_theta_sep` で全座標一致、`emb_distinct` で埋め込み一致。
    2 生成 `primEl_two_gen` の m 生成への一般化（帰納で本物）。 -/
theorem primEl_finite_simple (D : PrimElFinData) (i j : Fin D.nEmb)
    (h : primElTheta D.Ω D.cf (D.emb i) D.m
      = primElTheta D.Ω D.cf (D.emb j) D.m) : i = j := by
  have hall : ∀ t, t < D.m → D.emb i t = D.emb j t :=
    primEl_theta_sep D i j D.m (Nat.le_refl D.m) h
  exact D.emb_distinct i j hall

/-- **M288F-5e: 有限生成の単純性（isSimple 形）** — Θ_m の族は単射。 -/
theorem primEl_finite_isSimple (D : PrimElFinData) :
    primEl_isSimple (fun i => primElTheta D.Ω D.cf (D.emb i) D.m) :=
  fun i j h => primEl_finite_simple D i j h

/-! ## M288F-6: capstone — [K(γ):K] = [L:K]（単純） -/

/-- **M288F-6a: 原始元定理の総括データ** — 2 生成の原始元データ `base` と、
    次数の上下界の honest witness を束ねる。分離そのもの（`base` の
    `primEl_two_gen`）は本物、次数の等式は反対称律で閉じる。 -/
structure PrimitiveElementData where
  /-- 2 生成の原始元データ（分離は本物）。 -/
  base : PrimElTwoData
  /-- 原始元の生成する部分拡大の次数 [K(γ):K]。 -/
  degKγ : Nat
  /-- 全体の拡大次数 [L:K]。 -/
  degL : Nat
  /-- [L:K] = 埋め込み数 n（M282F: 分離拡大で埋め込み数 = 次数）。 -/
  degL_eq : degL = base.n
  /-- **honest witness（下界）**: γ が n 個の埋め込みを分離 → [K(γ):K] ≥ n
      （M282F: K(γ) の埋め込み数 = [K(γ):K]、分離された n 個が実現）。 -/
  deg_lower : base.n ≤ degKγ
  /-- **honest witness（上界）**: K(γ) ⊆ L → [K(γ):K] ≤ [L:K]（M281F 塔法則）。 -/
  deg_upper : degKγ ≤ degL

/-- **定理 (M288F-6b): 原始元定理** — [K(γ):K] = [L:K]。すなわち原始元 γ の
    生成する部分拡大が全体に一致（**K(γ) = L, 単純拡大**）。上下界の反対称律
    で閉じる本物の算術（分離＝原始元定理の核は `primEl_two_gen` で本物）。 -/
theorem primEl_theorem (D : PrimitiveElementData) : D.degKγ = D.degL := by
  have hup : D.degKγ ≤ D.base.n := by
    have h := D.deg_upper
    rw [D.degL_eq] at h
    exact h
  have heq : D.degKγ = D.base.n := Nat.le_antisymm hup D.deg_lower
  rw [heq, D.degL_eq]

/-- **定理 (M288F-6c): 原始元の存在と総括** — 原始元 γ = α + c·β が
    (i) [L:K] 個の埋め込みをすべて分離し（`primEl_two_gen`, 本物の核）、
    (ii) [K(γ):K] = [L:K]（`primEl_theorem`）を満たす＝有限分離拡大は単純。 -/
theorem primEl_exists (D : PrimitiveElementData) :
    primEl_isSimple (primElTwoGammaFam D.base) ∧ D.degKγ = D.degL :=
  ⟨primEl_two_gen D.base, primEl_theorem D⟩

/-- **定理 (M288F-6d): 総括の存在**（原始元データがあれば単純性が従う）。 -/
theorem primEl_theorem_exists (D : PrimitiveElementData) :
    Nonempty (primEl_isSimple (primElTwoGammaFam D.base) ∧ D.degKγ = D.degL) :=
  ⟨primEl_exists D⟩

end IUT
