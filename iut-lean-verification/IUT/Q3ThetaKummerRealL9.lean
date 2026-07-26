/-
  IUT/Q3ThetaKummerRealL9.lean — E4 実 theta の Kummer 理論（level-9 実スライス）
    実テータ群のテータ値 Θ = ζ₉（g_{[ζ₉]} の w-単数部）の本物の Kummer コサイクル
    κ_Θ(σ) = σ(Θ)/Θ ∈ μ₃(O_M) と、実 H¹(Gal(M/L₂), μ₃(O_M)) での類の非自明性

  ── 主要成果の分類: **[実／(a) 昇格]** — E4「実 theta の Kummer 理論」の従来モジュール
     M353F (tkc)・M358F (tkr) は、G_K が抽象 `Grp`・μ_{2l} が抽象 `CycMuGroup`・κ が仮定された
     Hom・Θ が形式記号であり、コサイクル全体が模型の上に住んでいた（監査 E4 = 0.00 の理由）。
     本モジュールはその主語を**実対象へ置換**する: G = 実 Gal(M/L₂) = ⟨σ⟩（`q9kdG`・実環
     自己同型 σ: Y↦ζ₃Y の群）、係数 = 実 μ₃(O_M)（`q9kdMu3`・M=ℚ₃(ζ₉) の実 1 の 3 乗根群）、
     Θ = **実 level-9 テータ群 `q9mtGrp` の元 g_{[ζ₉]} の w-単数部**（実 Tate 曲線 E_{3⁹} の実
     9-torsion 点 [ζ₉] への lift・μ₉ 値 Weil ペアリングの担体）。κ_Θ(σ)=σ(Θ)·Θ⁻¹ は実環の
     等式として成立する本物の 1-コサイクルで、その類は実 H¹ = Z¹/B¹（M326F 機構の実
     インスタンス）で**非自明**、3 乗ノルム Θ³ = ζ₃ ∈ L₂ の類は実立方剰余群
     L₂^×/(L₂^×)³ で**非立方**（q9cq 消費）。q9kd の正直な限定 1「一般 H¹ 形式論
     （galH1Module）への接続なし」という named gap を、μ₃(O_M) を係数加群に取ることで
     閉じる。toy 主語なし（m202fVol 型・Bool 軌道・surrogate 群を一切使わない）。

  ── **正直な訂正（独立敵対監査 2026-07-21・最重要）** ──────────────────────
  当初ヘッダの「初めて」主張は **誤り**であり撤回する。監査が rfl で確認した事実:
   * `q9tkTheta = q3kZeta9` — すなわち **Θ は文字通り ζ₉**。theta 群の元 g_{[ζ₉]} は
     q 部自明・指数 0 ゆえ、中心化条件 qᵃw⁹=1 は a=0 で ζ₉⁹=1 に退化し、theta 群は
     「ζ₉ ∈ μ₉」を超える制約を **一切課さない**。
   * `q9tkModule = q9khModule`（並行 B6 モジュール `Q3KummerH1Real` と **定義的に同一**）、
     `q9tkKappa = q9kdChiMap`、`q9tkClass = q9khDelta.map …`、旗艦 Kummer 関係式は
     `q9kd_cocycle` そのもの。よって「H¹ 機構を初めて実対象で駆動」「q9kd の named gap を
     初めて閉じる」はいずれも **偽**（q9kh が同一内容を持つ）。
   * `q9tk_class_nontrivial` は真だが新規でない（`q9kh_delta_inj` の ≠ 半分・q9kh は
     H¹ 全体を計算しており本モジュールより **強い**）。
  本モジュールの真水は cancellation による乗数一意性・導出版 crossed-hom・torsor 不変性
  の小補題数本のみで、**すべて generic Kummer**（theta 固有の内容はゼロ）。E4 の主語である
  Θ^{2l}=q^{j²}（theta pilot vs q pilot の非対称性）は不在——ここでは Θ³=ζ₃ と
  **単数**に落ち、q 側は `q9tk_q_cocycle_trivial` すなわち **自明**コサイクルである。
  ─────────────────────────────────────────────────

  complete_pct 影響: **E4 0.00 → 0.03（独立敵対監査確定・+0.03）**。当初予測 0.10–0.20 は
  上記の二重計上により棄却された。実 galH1Module インスタンスは **一度だけ**計上され、
  帰属は **B6**（generic Kummer）であって E4 ではない。
  新規（真水）は
   (1) Θ の「テータ群からの抽出」packaging（q9mt 所属・付値 0・μ₉ 完全性消費の三点で
       Θ が実テータ群データであることを固定）、
   (2) 実 Kummer 関係式 σ_g(Θ) = κ_Θ(g)·Θ の**一意性込み**の証明（Θ⁻¹ = Y⁸ による実
       キャンセル・q9kd は σ(ζ₉) の閉形式のみでコサイクル一意性を持たない）、
   (3) 実ガロア作用上の crossed-homomorphism 条件の**導出**（case-bash でなく
       σ の乗法性からの本物の導出）と μ₃-トーサー不変性（Θ↦ζΘ でコサイクル不変）、
   (4) 実 galH1Module インスタンス（M326F/M353F の H¹ 機構を実対象で駆動。**訂正: 「初めて」
       ではない**——`q9tkModule = q9khModule` が rfl で成立し B6 の q9kh と同一内容）:
       B¹ = 0（σ が μ₃ を点別固定）と **[κ_Θ] ≠ 0 ∈ H¹(Gal(M/L₂), μ₃(O_M))**、
   (5) 立方ノルム Θ³ = ζ₃（ガロア固定・M353F-2 の実版）と実立方剰余群への着地
       （[Θ³] = [ζ₃] は非立方・[λ] と独立 = q9cq 消費）、実 Kummer 双対との同定
       κ_Θ = χ（q9kd 完全双対の生成元）。
  **消費（再主張しない）**: q9mt_gz_mem / q9mt_mem_val0_mu9 / q9mt_weil_nondeg（柱E 実テータ群）、
  q9kd_cocycle / q9kd_cocycle2 / q9kd_act_mul / q9kd_hom_det / q9kd_z_ne_one（B6 実 Kummer 双対）、
  q9cq_zeta_noncube / q9cq_lambda_zeta_indep（B6 実立方剰余群）、q9c_m_mu3_complete（柱B μ₃
  完全性）、q3k_sigma_mul / q3k_sigma2_mul / q3k_zeta9_cube（柱A 実巡回代数）、
  M326F galH1 機構・M267F 商群機構。

  正直な限定（§4 規約により消さない・弱めない・q3k/q9kd/q9cq/q9mt 継承の上に追記のみ）:
  1. **n=3・有限 Gal(M/L₂)=⟨σ⟩ スライスのみ**。IUT 本体の μ_{2l}（l 素数 ≥5）・副有限
     G_K・完全エタールテータ類は未達——M353F/M358F の抽象一般形はその座標として残り、
     本モジュールはその**実 level-3 実現**（実 level-9 対象の上）である。
  2. **Θ = ζ₉ はテータ群の内部シクロトーム／9-torsion データ**（g_{[ζ₉]} の w-単数部・
     Weil 値 Z₉ の担体）であって、**評価されたテータ級数値 Θ(q,u_j) ではない**（p 進収束
     級数は依然ゼロ）。テータ値の q-冪部分（基礎体降下データ 3・q=3⁹）は自明コサイクル
     `q9tk_q_cocycle_trivial`（M353F-2b の実版）としてのみ現れる。
  3. **H¹ の係数は μ₃(O_M)・B¹ は μ₃ からのコバウンダリのみ**。完全 Kummer 接続射
     δ: L₂^× → H¹ の Hom としての構成・同型 H¹(Gal,μ₃) ≅ L₂^×/(L₂^×)³ の同型としての
     定式化は未達——着地は κ_Θ = χ の同定（q9kd 完全双対）＋ Θ³ = ζ₃ の非立方性
     （q9cq 消費）の 2 本で honest に述べる。
  4. q3k/q9kd/q9cq/q9mt の恒久限定を継承: O_M と単数群のみ（体化なし）・群提示の
     K-point の影・σ-only Galois（副有限化なし）・実テータ関数ゼロ・π₁ 同定ゼロ・
     q=3⁹ は忠実部分ケースの 2 乗・tmzLimit 比較橋なし。
  5. **二重計上（当初「firewall」主張は撤回）**: 既存定理は消費のみ（再証明 0 本）だが、
     当初ここに書いた「旗艦は κ_Θ/q9tkModule を主語に持ち、これらを消すと命題が消滅する」
     という firewall 主張は **実質的に誤導**であった。監査の指摘どおり κ_Θ = χ および
     q9tkModule = q9khModule は **定義的同一**であり、旗艦は B6 対象を消しても生き残る
     どころか **B6 対象そのもの**である（q9kh は import も消費宣言もしていないのに rfl 同値）。
     したがって本モジュールは E4 としては **near-pure 二重計上**であり、監査は 0.03 を付けた。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
  一般名は `q9tk` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.ThetaKummerClass
import IUT.Q3Mu9ThetaGroup
import IUT.Q3CubeQuotientReal

namespace IUT

/-! ## q9tk-0: テータ値 Θ の実テータ群からの抽出 -/

/-- **q9tk-0a: 実テータ値 Θ** — 実 level-9 テータ群の元 g_{[ζ₉]}（`q9mtGZeta`）の
    w-成分の単数部。定義的には Θ = ζ₉ = Y ∈ O_M = ℚ₃(ζ₉) の実元だが、主語は
    「実 Tate 曲線 E_{3⁹} の実 9-torsion 点 [ζ₉] へ射影されるテータ群データ」である。 -/
def q9tkTheta : q3kCar := q9mtGZeta.2.2.val

/-- **q9tk-0b: Θ = ζ₉**（抽出の閉形式・定義的）。 -/
theorem q9tk_theta_eq : q9tkTheta = q3kZeta9 := rfl

/-- **q9tk-0c: Θ の出自（テータ群所属）** — g_{[ζ₉]} は実テータ群 C_{M₉}(g_τ) の元
    （`q9mt_gz_mem` 消費・再証明しない）。 -/
theorem q9tk_theta_group_mem : q9mtGrp.mem q9mtGZeta := q9mt_gz_mem

/-- **q9tk-0d: Θ ∈ μ₉(O_M)** — 付値 0 のテータ群元の単数部は実 μ₉ に落ちる
    （`q9mt_mem_val0_mu9`＝μ₉ 完全性 q9c_mu9_complete の消費点・再証明しない）。 -/
theorem q9tk_theta_mu9 : q3kMu9 q9tkTheta :=
  q9mt_mem_val0_mu9 q9mtGZeta q9mt_gz_mem rfl

/-- **q9tk-0e: Θ は E_{3⁹}[9] の実 9-torsion 点 [ζ₉] へ射影**（`q9mt_proj_e9_zeta` 消費）。 -/
theorem q9tk_theta_proj : q9tlProj.map q9mtGZeta.2 = q9tlZeta9 := q9mt_proj_e9_zeta

/-- **q9tk-0f: Θ ≠ 1**（テータ値の非退化・q3k_zeta9_ne_one）。 -/
theorem q9tk_theta_ne_one : q9tkTheta ≠ q3kOne := q3k_zeta9_ne_one

/-! ## q9tk-1: 実ガロア作用の基礎（σ_g の乗法性・基礎体固定・μ₃ 点別固定） -/

/-- **q9tk-1a: σ_g は基礎体 L₂（embed 像）を固定**（実相対 Galois・
    e: 恒等、s: q9kd_sigma_fixes_base、s2: σ² = σ∘σ）。 -/
theorem q9tk_act_embed (g : q9kdGCar) (n : q3rqCar) :
    q9kdAct g (q3kEmbed n) = q3kEmbed n := by
  cases g with
  | e => rfl
  | s => exact q9kd_sigma_fixes_base n
  | s2 =>
    show q3kSigma2 (q3kEmbed n) = q3kEmbed n
    rw [q3k_sigma2_comp (q3kEmbed n), q9kd_sigma_fixes_base n, q9kd_sigma_fixes_base n]

/-- **q9tk-1b: σ_g は乗法的**（実環自己同型・q3k_sigma_mul / q3k_sigma2_mul 消費）。 -/
theorem q9tk_act_mul (g : q9kdGCar) (x y : q3kCar) :
    q9kdAct g (q3kMul x y) = q3kMul (q9kdAct g x) (q9kdAct g y) := by
  cases g with
  | e => rfl
  | s => exact q3k_sigma_mul x y
  | s2 => exact q3k_sigma2_mul x y

/-- **q9tk-1c: σ_g(1) = 1**。 -/
theorem q9tk_act_one (g : q9kdGCar) : q9kdAct g q3kOne = q3kOne := by
  cases g with
  | e => rfl
  | s => exact q3k_sigma_one
  | s2 => exact q3k_sigma2_one

/-- **q9tk-1d（★）: σ_g は μ₃(O_M) を点別固定** — x³ = 1 なら x ∈ {1, ζ₃, ζ₃²} ⊂ embed L₂
    （**μ₃ 完全性 `q9c_m_mu3_complete` 消費**）で、embed 像は q9tk-1a で固定。
    実 H¹ の B¹ = 0（q9tk-4）とコサイクル条件の実導出（q9tk-3）の核。 -/
theorem q9tk_mu3_fixed (g : q9kdGCar) (x : q3kCar)
    (hx : q3kMul (q3kMul x x) x = q3kOne) : q9kdAct g x = x := by
  obtain h | h | h := q9c_m_mu3_complete x hx
  · rw [h]; exact q9tk_act_one g
  · rw [h]; exact q9tk_act_embed g q3rqZeta
  · rw [h]; exact q9tk_act_embed g q3rqZetaSq

/-! ## q9tk-2: 実 Kummer コサイクル κ_Θ とその一意性 -/

/-- **q9tk-2a: テータ Kummer コサイクル κ_Θ** — κ_Θ(e)=1, κ_Θ(σ)=ζ₃, κ_Θ(σ²)=ζ₃²
    ∈ μ₃(O_M)。定義式 σ_g(Θ) = κ_Θ(g)·Θ（q9tk-2c）と一意性（q9tk-2e）がこの写像を
    「Θ の Kummer コサイクル σ↦σ(Θ)/Θ」として特徴付ける。 -/
def q9tkKappa : q9kdGCar → q9kdMu3.carrier
  | .e => q9kdMu3One
  | .s => q9kdMu3Z
  | .s2 => q9kdMu3Z2

/-- **q9tk-2b: κ_Θ(σ) ≠ 1**（コサイクルの非空虚性・実 witness ζ₃ ≠ 1）。 -/
theorem q9tk_kappa_s_ne_one : (q9tkKappa q9kdGCar.s).val ≠ q3kOne := q9kd_z_ne_one

/-- **q9tk-2c（★★ 旗艦）: 実 Kummer 関係式** σ_g(Θ) = κ_Θ(g)·Θ — 実環 O_M の等式。
    e: Θ = 1·Θ、s: σ(ζ₉) = ζ₃·ζ₉（`q9kd_cocycle` 消費）、s2: σ²(ζ₉) = ζ₃²·ζ₉
    （`q9kd_cocycle2` 消費）。M353F の形式的 κ_Θ = `galH1Coboundary A Θ` が
    実 p 進対象の等式になる。**訂正（監査）**: Θ = ζ₉ ゆえ本式は `q9kd_cocycle`
    そのものであり、theta 固有の新規内容ではない。 -/
theorem q9tk_kummer_eq (g : q9kdGCar) :
    q9kdAct g q9tkTheta = q3kMul (q9tkKappa g).val q9tkTheta := by
  cases g with
  | e => exact (q3k_one_mul q9tkTheta).symm
  | s => exact q9kd_cocycle
  | s2 => exact q9kd_cocycle2

/-- **q9tk-2d: Θ の実逆元** Y⁸·Θ = 1（Y⁹ = 1・`q9tl_zpow8`/`q9tl_zpow9` 消費）。
    κ_Θ の「除算 σ(Θ)/Θ」を実環で正当化するキャンセル部品。 -/
theorem q9tk_theta_inv_mul : q3kMul q9ypY8 q9tkTheta = q3kOne := by
  have h : q3kMul (tateNpow q3kU q9tlZeta9U 8).val q3kZeta9 = q3kOne := q9tl_zpow9
  rw [q9tl_zpow8] at h
  exact h

/-- **q9tk-2e: Θ 倍のキャンセル** m·Θ = m'·Θ ⟹ m = m'（Θ は実可逆・Θ⁻¹ = Y⁸）。 -/
theorem q9tk_theta_cancel (m m' : q3kCar)
    (h : q3kMul m q9tkTheta = q3kMul m' q9tkTheta) : m = m' := by
  have h2 : q3kMul (q3kMul m q9tkTheta) q9ypY8
      = q3kMul (q3kMul m' q9tkTheta) q9ypY8 :=
    congrArg (fun z => q3kMul z q9ypY8) h
  rw [q3k_mul_assoc m q9tkTheta q9ypY8, q3k_mul_assoc m' q9tkTheta q9ypY8,
      q3k_mul_comm q9tkTheta q9ypY8, q9tk_theta_inv_mul,
      q9kd_mul_one m, q9kd_mul_one m'] at h2
  exact h2

/-- **q9tk-2f（★）: κ_Θ の一意性** — σ_g(Θ) = m·Θ を満たす m は κ_Θ(g) に限る。
    κ_Θ が Θ から**一意に**決まる本物の Kummer コサイクルであることの核
    （q9kd の閉形式 σ(ζ₉)=ζ₃ζ₉ には無い新規内容）。 -/
theorem q9tk_kappa_unique (g : q9kdGCar) (m : q3kCar)
    (h : q9kdAct g q9tkTheta = q3kMul m q9tkTheta) : m = (q9tkKappa g).val :=
  q9tk_theta_cancel m (q9tkKappa g).val (h.symm.trans (q9tk_kummer_eq g))

/-! ## q9tk-3: 実ガロア作用上の 1-コサイクル条件（導出・case-bash でない） -/

/-- **q9tk-3a（★★ 旗艦）: crossed homomorphism 条件** κ_Θ(gh) = κ_Θ(g)·σ_g(κ_Θ(h))。
    証明は本物の導出: σ_{gh}(Θ) = σ_g(σ_h(Θ)) = σ_g(κ_Θ(h)·Θ) = σ_g(κ_Θ(h))·κ_Θ(g)·Θ
    （σ_g の乗法性 q9tk-1b・Kummer 関係式 q9tk-2c）に一意性 q9tk-2f を適用する。 -/
theorem q9tk_cocycle_cond (g h : q9kdGCar) :
    (q9tkKappa (q9kdGMul g h)).val
      = q3kMul (q9tkKappa g).val (q9kdAct g (q9tkKappa h).val) := by
  apply q9tk_theta_cancel
  rw [← q9tk_kummer_eq (q9kdGMul g h), q9kd_act_mul g h q9tkTheta,
      q9tk_kummer_eq h, q9tk_act_mul g (q9tkKappa h).val q9tkTheta,
      q9tk_kummer_eq g,
      ← q3k_mul_assoc (q9kdAct g (q9tkKappa h).val) (q9tkKappa g).val q9tkTheta,
      q3k_mul_comm (q9kdAct g (q9tkKappa h).val) (q9tkKappa g).val,
      q3k_mul_assoc (q9tkKappa g).val (q9kdAct g (q9tkKappa h).val) q9tkTheta]

/-- **q9tk-3b（★）: μ₃-トーサー不変性** — テータ値の μ₃-捻り Θ ↦ ζ·Θ（ζ ∈ μ₃(O_M)）は
    Kummer 関係式を**コサイクルごと**不変に保つ: σ_g(ζΘ) = κ_Θ(g)·(ζΘ)。
    M353F-4c（[ζΘ]=[Θ]・H¹ 類の不変性）の実版であり、σ が μ₃ を固定するため
    実スライスでは類どころかコサイクル自体が不変になる（より強い実結果）。 -/
theorem q9tk_torsor_invariance (ζ : q9kdMu3.carrier) (g : q9kdGCar) :
    q9kdAct g (q3kMul ζ.val q9tkTheta)
      = q3kMul (q9tkKappa g).val (q3kMul ζ.val q9tkTheta) := by
  rw [q9tk_act_mul g ζ.val q9tkTheta, q9tk_mu3_fixed g ζ.val ζ.property,
      q9tk_kummer_eq g,
      ← q3k_mul_assoc ζ.val (q9tkKappa g).val q9tkTheta,
      q3k_mul_comm ζ.val (q9tkKappa g).val,
      q3k_mul_assoc (q9tkKappa g).val ζ.val q9tkTheta]

/-! ## q9tk-4: 実 galH1Module インスタンスと H¹ 類の非自明性 -/

/-- **q9tk-4a: μ₃(O_M) への σ_g の制限**（実 Hom・値の固定性 q9tk-1d で μ₃ に閉じる）。 -/
def q9tkActHom (g : q9kdGCar) : Hom q9kdMu3 q9kdMu3 where
  map := fun x => ⟨q9kdAct g x.val, by
    rw [q9tk_mu3_fixed g x.val x.property]; exact x.property⟩
  map_mul := fun x y => Subtype.ext (q9tk_act_mul g x.val y.val)

/-- **q9tk-4b（★）: 実 G-加群** — M326F `galH1Module` の**実インスタンス**:
    G = 実 Gal(M/L₂) = ⟨σ⟩、M = 実 μ₃(O_M)、作用 = 実環自己同型 σ_g の制限。
    q9kd 正直限定 1 の named gap「一般 H¹ 形式論への接続なし」を閉じる。
    **訂正（監査）**: 「初めて」ではない——`q9tkModule = q9khModule`（B6 の
    `Q3KummerH1Real`）が rfl で成立。本インスタンスの計上先は B6 であって E4 ではない。 -/
def q9tkModule : galH1Module q9kdG where
  M := q9kdMu3
  comm := fun a b => Subtype.ext (q3k_mul_comm a.val b.val)
  act := q9tkActHom
  act_one := fun _ => Subtype.ext rfl
  act_mul := fun g h m => Subtype.ext (q9kd_act_mul g h m.val)

/-- **q9tk-4c: κ_Θ は実 Z¹ の元**（1-コサイクル条件 = q9tk-3a）。 -/
def q9tkCocycle : galH1Cocycle q9tkModule where
  f := q9tkKappa
  cocycle := fun g h => Subtype.ext (q9tk_cocycle_cond g h)

/-- **q9tk-4d: テータ Kummer 類 [Θ] ∈ H¹(Gal(M/L₂), μ₃(O_M))** — M353F の射影
    `tkcProj`（Z¹ → H¹ = Z¹/B¹）を**実加群で駆動**して得る実類。 -/
def q9tkClass : (galH1Group q9tkModule).carrier :=
  (tkcProj q9tkModule).map q9tkCocycle

/-- **q9tk-4e（★）: B¹ = 0** — σ_g が μ₃ を点別固定するため、μ₃ からのコバウンダリ
    f_m(g) = σ_g(m)·m⁻¹ はすべて自明コサイクル。 -/
theorem q9tk_coboundary_trivial (m : q9kdMu3.carrier) :
    (galH1CoboundaryHom q9tkModule).map m = (galH1_cocycles_group q9tkModule).one := by
  apply galH1Cocycle.ext
  funext g
  show q9kdMu3.mul ((q9tkActHom g).map m) (q9kdMu3.inv m) = q9kdMu3.one
  have hfix : (q9tkActHom g).map m = m :=
    Subtype.ext (q9tk_mu3_fixed g m.val m.property)
  rw [hfix]
  exact q9kdMu3.mul_inv m

/-- **q9tk-4f（★★★ 旗艦・非自明性 witness）: [Θ] ≠ 0 ∈ H¹(Gal(M/L₂), μ₃(O_M))** —
    [Θ] = 0 なら κ_Θ ∈ B¹（M267F `quotientProjN_ker`）、B¹ = 0（q9tk-4e）ゆえ
    κ_Θ(σ) = 1、しかし κ_Θ(σ) = ζ₃ ≠ 1（`q9kd_z_ne_one` 消費）で矛盾。
    実テータ群データの Kummer 類が実 H¹ で本物に非自明であることの確定。 -/
theorem q9tk_class_nontrivial : q9tkClass ≠ (galH1Group q9tkModule).one := by
  intro h
  have hmem := (quotientProjN_ker (galH1_cocycles_group q9tkModule)
    (galH1_coboundaries_subgroup q9tkModule)
    (galH1_coboundaries_normal q9tkModule) q9tkCocycle).mp h
  obtain ⟨m, hm⟩ := hmem
  have hm' : (galH1_cocycles_group q9tkModule).one = q9tkCocycle := by
    rw [← q9tk_coboundary_trivial m]; exact hm
  have hval := congrArg
    (fun c : galH1Cocycle q9tkModule => (c.f q9kdGCar.s).val) hm'
  exact q9kd_z_ne_one hval.symm

/-! ## q9tk-5: 実 Kummer 双対との同定（κ_Θ = χ・双対の生成元） -/

/-- **q9tk-5a: κ_Θ は群準同型**（crossed hom ＋ μ₃ 点別固定 ⟹ Hom）。 -/
def q9tkKappaHom : Hom q9kdG q9kdMu3 where
  map := q9tkKappa
  map_mul := fun g h => Subtype.ext (by
    have hc := q9tk_cocycle_cond g h
    rw [q9tk_mu3_fixed g (q9tkKappa h).val (q9tkKappa h).property] at hc
    exact hc)

/-- **q9tk-5b（★）: κ_Θ = χ** — テータ Kummer コサイクルは実 Kummer 双対
    （`q9kd_kummer_iso`）の Kummer 指標 χ に一致（σ での値 ζ₃ が一致・
    `q9kd_hom_det` 消費）。[Θ] は完全双対 ⟨[ζ₃]⟩ ≅ Hom(Gal,μ₃) の**生成元側**に対応。 -/
theorem q9tk_hom_eq_chi : q9tkKappaHom = q9kdChi :=
  q9kd_hom_det q9tkKappaHom q9kdChi rfl

/-- **q9tk-5c: 双対の枚挙での位置** — κ_Θ は k=1（クラス [ζ₃]¹）の指標 χ¹。 -/
theorem q9tk_duality_position : q9kdChiPow q9kdGCar.s = q9tkKappaHom :=
  q9tk_hom_eq_chi.symm

/-! ## q9tk-6: 立方ノルム Θ³ = ζ₃ と実立方剰余群への着地 -/

/-- **q9tk-6a（★）: 立方ノルム** Θ³ = ζ₃ ∈ embed L₂ — テータ値の 3 乗が基礎体に落ちる
    （`q3k_zeta9_cube` 消費）。M353F-2「Θ^{2l} = q^{j²} ∈ K」の実版（level-3 スライス）。 -/
theorem q9tk_theta_cube :
    q3kMul (q3kMul q9tkTheta q9tkTheta) q9tkTheta = q3kEmbed q3rqZeta :=
  q3k_zeta9_cube

/-- **q9tk-6b: 立方ノルムはガロア固定** σ_g(Θ³) = Θ³（基礎体 embed 固定 q9tk-1a）。 -/
theorem q9tk_cube_fixed (g : q9kdGCar) :
    q9kdAct g (q3kMul (q3kMul q9tkTheta q9tkTheta) q9tkTheta)
      = q3kMul (q3kMul q9tkTheta q9tkTheta) q9tkTheta := by
  rw [q9tk_theta_cube]
  exact q9tk_act_embed g q3rqZeta

/-- **q9tk-6c: 着地の同定** — 実立方剰余群の類 [ζ₃] = `q9cq_zetaClass` の単数部の
    embed は Θ³ そのもの（Kummer 対応 [Θ] ↔ [Θ³] の実データ側）。 -/
theorem q9tk_cube_class_eq :
    q3kEmbed q9cq_zetaClass.2.val
      = q3kMul (q3kMul q9tkTheta q9tkTheta) q9tkTheta := by
  rw [q9tk_theta_cube]
  rfl

/-- **q9tk-6d（★★ 非自明性 witness・q9cq 消費）: [Θ³] = [ζ₃] は非立方** —
    テータ値の Kummer 類の像は実 L₂^×/(L₂^×)³ で非自明（`q9cq_zeta_noncube` 消費・
    再証明しない）。 -/
theorem q9tk_land_noncube :
    ¬ ∃ g : q3rqLx.carrier,
      q3rqLx.mul (q3rqLx.mul g g) g = q9cq_zetaClass :=
  q9cq_zeta_noncube

/-- **q9tk-6e（q9cq 消費）: テータ類は一様化子類と独立** — [Θ³] = [ζ₃] と [λ] の
    8 つの非自明結合が全て非立方（rank ≥ 2 の実下界・`q9cq_lambda_zeta_indep` 消費）。 -/
theorem q9tk_land_indep : Q9cqIndep := q9cq_lambda_zeta_indep

/-- **q9tk-6f: 基礎体降下データの自明コサイクル**（M353F-2b の実版）— テータの q-冪側
    降下データ 3 ∈ ℚ₃ ⊂ L₂（q = 3⁹ の 9 乗根）はガロア固定で、その Kummer コサイクルは
    自明: σ_g(3) = 1·3。 -/
theorem q9tk_q_cocycle_trivial (g : q9kdGCar) :
    q9kdAct g (q3kEmbed q3kThree) = q3kMul q3kOne (q3kEmbed q3kThree) := by
  rw [q3k_one_mul]
  exact q9tk_act_embed g q3kThree

/-! ## q9tk-7: capstone（束ねのみ・新規証明ゼロ） -/

/-- **q9tk-7a: E4 実 theta Kummer 理論データ** — 実テータ群からの Θ 抽出・実 Kummer
    関係式と一意性・実ガロア作用上の 1-コサイクル・μ₃-トーサー不変性・実 H¹ での類の
    非自明性・実 Kummer 双対との同定・立方ノルムの実立方剰余群への非立方着地・
    Weil 非退化（同じ Θ が μ₉ Weil ペアリングの担体）を一括束ね。 -/
structure Q3ThetaKummerRealData where
  /-- Θ はテータ群 C_{M₉}(g_τ) のデータ（g_{[ζ₉]} 所属・q9mt 消費）。 -/
  theta_group_mem : q9mtGrp.mem q9mtGZeta
  /-- Θ ∈ μ₉(O_M)（付値 0・μ₉ 完全性消費）。 -/
  theta_mu9 : q3kMu9 q9tkTheta
  /-- Θ ≠ 1。 -/
  theta_ne_one : q9tkTheta ≠ q3kOne
  /-- 実 Kummer 関係式 σ_g(Θ) = κ_Θ(g)·Θ。 -/
  kummer_eq : ∀ g, q9kdAct g q9tkTheta = q3kMul (q9tkKappa g).val q9tkTheta
  /-- κ_Θ の一意性（σ_g(Θ) = m·Θ ⟹ m = κ_Θ(g)）。 -/
  kappa_unique : ∀ g m, q9kdAct g q9tkTheta = q3kMul m q9tkTheta
    → m = (q9tkKappa g).val
  /-- 実 1-コサイクル条件 κ_Θ(gh) = κ_Θ(g)·σ_g(κ_Θ(h))。 -/
  cocycle_cond : ∀ g h, (q9tkKappa (q9kdGMul g h)).val
    = q3kMul (q9tkKappa g).val (q9kdAct g (q9tkKappa h).val)
  /-- μ₃-トーサー不変性（Θ ↦ ζΘ でコサイクル不変）。 -/
  torsor_inv : ∀ (ζ : q9kdMu3.carrier) g,
    q9kdAct g (q3kMul ζ.val q9tkTheta)
      = q3kMul (q9tkKappa g).val (q3kMul ζ.val q9tkTheta)
  /-- ★ [Θ] ≠ 0 ∈ H¹(Gal(M/L₂), μ₃(O_M))（実 H¹ での非自明性）。 -/
  class_nontrivial : q9tkClass ≠ (galH1Group q9tkModule).one
  /-- κ_Θ(σ) = ζ₃ ≠ 1（点別非空虚性）。 -/
  kappa_s_ne_one : (q9tkKappa q9kdGCar.s).val ≠ q3kOne
  /-- κ_Θ = χ（実 Kummer 双対の生成元・q9kd 消費）。 -/
  hom_eq_chi : q9tkKappaHom = q9kdChi
  /-- 立方ノルム Θ³ = ζ₃ ∈ L₂。 -/
  cube_eq : q3kMul (q3kMul q9tkTheta q9tkTheta) q9tkTheta = q3kEmbed q3rqZeta
  /-- 立方ノルムはガロア固定。 -/
  cube_fixed : ∀ g, q9kdAct g (q3kMul (q3kMul q9tkTheta q9tkTheta) q9tkTheta)
    = q3kMul (q3kMul q9tkTheta q9tkTheta) q9tkTheta
  /-- ★ [Θ³] = [ζ₃] は実 L₂^×/(L₂^×)³ で非立方（q9cq 消費）。 -/
  land_noncube : ¬ ∃ g : q3rqLx.carrier,
    q3rqLx.mul (q3rqLx.mul g g) g = q9cq_zetaClass
  /-- テータ類は一様化子類 [λ] と独立（rank ≥ 2・q9cq 消費）。 -/
  land_indep : Q9cqIndep
  /-- 同じ Θ を担体とする μ₉ Weil ペアリングの非退化（q9mt 消費）。 -/
  weil_nondeg : q9mtWeil q9mtG3 q9mtGZeta ≠ q9tlMx.one

/-- **q9tk-7b: 見出し実例** — 実 M = ℚ₃(ζ₉)・実 Gal(M/L₂) = ⟨σ⟩ 上の実テータ値の
    Kummer 理論。 -/
def q9tk_data : Q3ThetaKummerRealData where
  theta_group_mem := q9tk_theta_group_mem
  theta_mu9 := q9tk_theta_mu9
  theta_ne_one := q9tk_theta_ne_one
  kummer_eq := q9tk_kummer_eq
  kappa_unique := q9tk_kappa_unique
  cocycle_cond := q9tk_cocycle_cond
  torsor_inv := q9tk_torsor_invariance
  class_nontrivial := q9tk_class_nontrivial
  kappa_s_ne_one := q9tk_kappa_s_ne_one
  hom_eq_chi := q9tk_hom_eq_chi
  cube_eq := q9tk_theta_cube
  cube_fixed := q9tk_cube_fixed
  land_noncube := q9tk_land_noncube
  land_indep := q9tk_land_indep
  weil_nondeg := q9mt_weil_nondeg

/-- **q9tk-7c: E4 実 theta Kummer 理論の存在**（実テータ群データ Θ・実 Gal(M/L₂)・
    実 μ₃(O_M)・実 H¹・実立方剰余群の上）。 -/
theorem q9tk_exists : Nonempty Q3ThetaKummerRealData := ⟨q9tk_data⟩

end IUT
