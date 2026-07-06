/-
  IUT/KummerTheory.lean — M320F: Kummer 理論 K^×/(K^×)ⁿ と Kummer 写像
  ── 柱B（局所類体論）の横展開 — Kummer 離脱（Kummer-detachment）の代数的核

  ── 主要成果の分類: **[実]**（本物の体 K の乗法群 K^× の上に、**n 乗写像 x↦xⁿ を
  本物の群準同型**として建て、その像 (K^×)ⁿ を本物の部分群、**Kummer 商
  K^×/(K^×)ⁿ を本物のアーベル商群**として実構成する。さらに **Kummer 写像
  x ↦ (σ ↦ σ(x^{1/n})/x^{1/n}) の 1-コサイクル則を本物で完全証明**する）。

  complete_pct 影響: **柱B「Kummer 理論＝Kummer-detachment の代数的核」の本物の
  先行建設**。Mochizuki の IUT は Frobenius-like（値のモノイド）と étale-like
  （遠アーベル的 π₁）を **Kummer 理論 K^×/(K^×)ⁿ ≅ H¹(G_K, μ_n)** で貼り合わせ
  （Kummer 離脱）、テータ値の遠アーベル復元を行う。既存コードベースは
  * `Field.lean`(M264F) 本物の体 `IUTField`（ℚ 実例）、
  * `QuotientGroup.lean`(M267F) 正規部分群・商群・準同型の核/像・第一同型定理、
  * `TateCurve.lean`(M309F) K^×=`tateMultGroup`・群冪 `tateNpow`・整数冪部分群、
  * `TateTorsion.lean`(M314F) 群冪の乗法性 `tateTorMulPow`・μ_n `tateTorMuSubgroup`、
  * `FieldAutGroup.lean`(M271F) 体の自己同型 `FieldAut`・自己同型群
  を個別に持つが、**「n 乗写像 K^×→K^× の準同型性・その像 (K^×)ⁿ・商 K^×/(K^×)ⁿ・
  Kummer 写像の 1-コサイクル則」そのもの**は無かった。本ファイルがそれを本物で建てる。

  * M320F-1 `kummerNthPow`         — **n 乗写像 x↦xⁿ を本物の群準同型 `Hom K^× K^×`**
    （可換性から (xy)ⁿ=xⁿyⁿ、`tateTorMulPow`）。
  * M320F-2 `kummerNthPowersSubgroup` — **像 (K^×)ⁿ を本物の部分群**（`imSubgroup`）。
    可換ゆえ正規 `kummer_nthPowers_isNormal`。
  * M320F-3 `kummerQuotient` / `kummer_quotient_isAbelian` — **Kummer 商
    K^×/(K^×)ⁿ を本物のアーベル商群**（`quotientGroupN`）。
  * M320F-4 `kummerUnitAct` / `kummerUnitAct_mul` / `_inv` / `_npow` / `_comp` —
    体の自己同型 σ の K^× への**本物の作用**（σ が乗法・逆元・群冪・合成を保つ）。
  * M320F-5 `kummerCocycle` / **`kummer_cocycle`** — **Kummer 写像の 1-コサイクル則**
    c(στ)=c(σ)·σ(c(τ)) を本物で完全証明（可換群の並べ替え `kummerRearrange`）。
    `kummer_cocycle_in_mu`（σ が x=rⁿ を固定するとき c(σ)∈μ_n を本物で）。
  * M320F-6 `kummerCoboundary` / `kummer_cocycle_mul` / `kummer_h1_welldefined` —
    r↦c_r(σ) が r について準同型（c_{rz}=c_r·c_z）＝ **Kummer 類が (K^×)ⁿ を
    法として well-defined**（H¹ への降下の本物の核）。`kummer_cocycle_trivial_iff`
    （コサイクルが自明 ⟺ r が σ-固定）＝ **単射方向の本物の核**。
  * M320F-7 完全列 `kummer_exact_at_mu`（ker(x↦xⁿ)=μ_n）/ `kummer_exact_at_units`
    （im(x↦xⁿ)=(K^×)ⁿ=ker(射影)）/ `kummer_proj_surjective` —
    **1→μ_n→K^×→K^×→K^×/(K^×)ⁿ→1 の各点の核=像を本物で**。
  * M320F-8 capstone `KummerData` / `kummerData` / `kummer_exists` /
    `kummer_quotient_group` / `kummer_nthPow_hom` / 実例 ℚ^×/(ℚ^×)²・l 素数版。

  正直な限定（何が本物で何が骨組みか）:
  - **本物**: n 乗写像が本物の群準同型（(xy)ⁿ=xⁿyⁿ）、像 (K^×)ⁿ が本物の（正規）
    部分群、Kummer 商 K^×/(K^×)ⁿ が本物のアーベル商群、Kummer 写像の **1-コサイクル
    則 c(στ)=c(σ)·σ(c(τ)) が完全証明**、σ 固定下で c(σ)∈μ_n、r↦c_r が準同型
    （(K^×)ⁿ 法での well-defined）、コサイクル自明 ⟺ σ-固定、完全列の各点の
    核=像。すべて sorry 皆無・新規 choice 皆無。
  - **n 乗根 x^{1/n} は witness で受け取る**: c_r(σ)=σ(r)·r⁻¹ の r は rⁿ=x なる元
    （μ_n⊆K なら原始 n 乗根が K にある場合の n 乗根の存在）を witness として
    受け取る。分離閉包での n 乗根の存在そのものは柱A の後続。
  - **c(σ)∈μ_n は σ が x=rⁿ を固定するという仮説形**: Galois 群 Gal(L/K) が
    基礎体の元 x を固定するという本物の条件 `hfix` の下で c(σ)ⁿ=σ(x)/x=1 を証明する。
    「x が基礎体 K に属する」ことからの `hfix` の自動導出は `FieldExtension` 経由の
    後続（本ファイルは仮説形で本物の中身 c(σ)ⁿ=σ(x)/x を閉じる）。
  - **H¹(G_K,μ_n) の完全な群コホモロジー（コバウンダリ商 Z¹/B¹）は骨組み**:
    1-コサイクルの条件と well-defined（(K^×)ⁿ 法）・単射方向（自明 ⟺ 固定）までを
    本物で建て、Z¹/B¹ の商群構成と全同型 K^×/(K^×)ⁿ ≅ H¹ の完全性は後続。
  - **IUT の Kummer-detachment 本丸（Frobenius-like ⇄ étale-like）は柱D/C 後続**:
    ここは Kummer 理論の代数的核（n 乗写像・商・コサイクル）に専念する。
  - **標数 p｜n の非分離・一般 μ_n⊄K は後続**: μ_n⊆K（原始 n 乗根が K にある）の
    設定に限る。

  全て選択公理不使用（新規 choice を証明本体に導入しない）。禁止タクティク不使用
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp
  なし）。共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更なし。
-/
import IUT.TateTorsion
import IUT.FieldAutGroup

namespace IUT

/-! ## M320F-0: 可換群の並べ替え補題（コサイクル則・well-defined の核） -/

/-- **可換群の 4 元並べ替え** (a·b)·(c·d) = (a·c)·(b·d)。 -/
theorem kummerMulMulComm (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (a b c d : G.carrier) :
    G.mul (G.mul a b) (G.mul c d) = G.mul (G.mul a c) (G.mul b d) := by
  rw [G.mul_assoc a b (G.mul c d), ← G.mul_assoc b c d, hc b c, G.mul_assoc c b d,
    ← G.mul_assoc a c (G.mul b d)]

/-- **可換群の並べ替え** (a·b)·(c·a⁻¹) = c·b（コサイクル則の核）。 -/
theorem kummerRearrange (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (a b c : G.carrier) :
    G.mul (G.mul a b) (G.mul c (G.inv a)) = G.mul c b := by
  rw [G.mul_assoc a b (G.mul c (G.inv a)), hc c (G.inv a),
    ← G.mul_assoc b (G.inv a) c, hc b (G.inv a), G.mul_assoc (G.inv a) b c,
    ← G.mul_assoc a (G.inv a) (G.mul b c), G.mul_inv, G.one_mul, hc b c]

/-- **可換群の並べ替え** (a·b)·(c·d)⁻¹ = (a·c⁻¹)·(b·d⁻¹)（well-defined の核）。 -/
theorem kummerRearrange2 (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (a b c d : G.carrier) :
    G.mul (G.mul a b) (G.inv (G.mul c d))
      = G.mul (G.mul a (G.inv c)) (G.mul b (G.inv d)) := by
  rw [G.inv_mul_rev c d, hc (G.inv d) (G.inv c),
    kummerMulMulComm G hc a b (G.inv c) (G.inv d)]

/-! ## M320F-1: n 乗写像 x↦xⁿ は本物の群準同型 K^×→K^× -/

/-- **n 乗写像 x↦xⁿ**（M320F-1）— 体 K の乗法群 K^× 上の n 乗写像は、K^× が
    可換群（`tateMultGroup_comm`）ゆえ (xy)ⁿ=xⁿyⁿ を満たし、**本物の群準同型**
    `Hom K^× K^×` をなす（`tateTorMulPow`）。Kummer 理論の n 乗写像そのもの。 -/
def kummerNthPow (K : IUTField) (n : Nat) :
    Hom (tateMultGroup K) (tateMultGroup K) where
  map := fun x => tateNpow (tateMultGroup K) x n
  map_mul := fun a b => tateTorMulPow (tateMultGroup K) (tateMultGroup_comm K) a b n

/-- **n 乗写像は準同型（明示）** — (xy)ⁿ = xⁿ·yⁿ。 -/
theorem kummer_nthPow_isHom (K : IUTField) (n : Nat) (a b : (tateMultGroup K).carrier) :
    (kummerNthPow K n).map ((tateMultGroup K).mul a b)
      = (tateMultGroup K).mul ((kummerNthPow K n).map a) ((kummerNthPow K n).map b) :=
  (kummerNthPow K n).map_mul a b

/-! ## M320F-2: 像 (K^×)ⁿ を本物の部分群として -/

/-- **像 (K^×)ⁿ = n 乗元全体**（M320F-2）— n 乗写像の像 `imSubgroup`
    （= { y | ∃ x, xⁿ = y }）を**本物の部分群**として実構成。 -/
def kummerNthPowersSubgroup (K : IUTField) (n : Nat) : Subgroup (tateMultGroup K) :=
  imSubgroup (kummerNthPow K n)

/-- **(K^×)ⁿ は正規部分群**（K^× は可換なので任意部分群が正規）。 -/
theorem kummer_nthPowers_isNormal (K : IUTField) (n : Nat) :
    IsNormalSubgroup (tateMultGroup K) (kummerNthPowersSubgroup K n) := by
  intro x m hm
  have hconj :
      (tateMultGroup K).mul ((tateMultGroup K).mul x m) ((tateMultGroup K).inv x) = m := by
    rw [tateMultGroup_comm K x m, (tateMultGroup K).mul_assoc,
      (tateMultGroup K).mul_inv, (tateMultGroup K).mul_one]
  rw [hconj]
  exact hm

/-! ## M320F-3: Kummer 商 K^×/(K^×)ⁿ を本物のアーベル商群として -/

/-- **Kummer 商 K^×/(K^×)ⁿ**（M320F-3）— 乗法群 K^× を n 乗元部分群 (K^×)ⁿ で
    割った**本物の商群**（M267F `quotientGroupN`、(K^×)ⁿ は可換ゆえ正規）。
    IUT の Kummer-detachment が住む代数的対象。 -/
def kummerQuotient (K : IUTField) (n : Nat) : Grp :=
  quotientGroupN (tateMultGroup K) (kummerNthPowersSubgroup K n)
    (kummer_nthPowers_isNormal K n)

/-- **射影 K^× → K^×/(K^×)ⁿ**（全射準同型）。 -/
def kummerProj (K : IUTField) (n : Nat) :
    Hom (tateMultGroup K) (kummerQuotient K n) :=
  quotientProjN (tateMultGroup K) (kummerNthPowersSubgroup K n)
    (kummer_nthPowers_isNormal K n)

/-- **K^×/(K^×)ⁿ はアーベル群**（可換群 K^× の商）。 -/
theorem kummer_quotient_isAbelian (K : IUTField) (n : Nat) :
    ∀ x y : (kummerQuotient K n).carrier,
      (kummerQuotient K n).mul x y = (kummerQuotient K n).mul y x := by
  intro x y
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  show Quot.mk _ ((tateMultGroup K).mul a b) = Quot.mk _ ((tateMultGroup K).mul b a)
  rw [tateMultGroup_comm K a b]

/-! ## M320F-4: 体の自己同型 σ の K^× への作用 -/

/-- **σ の K^× への作用**（M320F-4）— 体の自己同型 σ:K→K は非零元を非零元に写す
    （σ は全単射で σ(0)=0、σ(u)=0 なら σ⁻¹ を施して u=0 と矛盾）ので、乗法群 K^×
    に**本物に作用**する。Kummer 写像 σ ↦ σ(r)/r の σ(r) を与える。 -/
def kummerUnitAct (K : IUTField) (σ : FieldAut K) (u : (tateMultGroup K).carrier) :
    (tateMultGroup K).carrier :=
  ⟨σ.toFun u.val, by
    intro h
    apply u.property
    have h2 : σ.invFun (σ.toFun u.val) = σ.invFun K.zero := congrArg σ.invFun h
    rw [σ.left_inv] at h2
    have hz : σ.invFun K.zero = K.zero := by
      have h3 : σ.invFun (σ.toFun K.zero) = K.zero := σ.left_inv K.zero
      rw [σ.map_zero] at h3
      exact h3
    rw [hz] at h2
    exact h2⟩

/-- **作用は乗法を保つ**: σ(uv) = σ(u)·σ(v)。 -/
theorem kummerUnitAct_mul (K : IUTField) (σ : FieldAut K)
    (u v : (tateMultGroup K).carrier) :
    kummerUnitAct K σ ((tateMultGroup K).mul u v)
      = (tateMultGroup K).mul (kummerUnitAct K σ u) (kummerUnitAct K σ v) := by
  apply Subtype.ext
  show σ.toFun (K.mul u.val v.val) = K.mul (σ.toFun u.val) (σ.toFun v.val)
  exact σ.map_mul u.val v.val

/-- **作用は単位元を保つ**: σ(1) = 1。 -/
theorem kummerUnitAct_one (K : IUTField) (σ : FieldAut K) :
    kummerUnitAct K σ (tateMultGroup K).one = (tateMultGroup K).one := by
  apply Subtype.ext
  show σ.toFun K.one = K.one
  exact σ.map_one

/-- **作用は逆元を保つ**: σ(u⁻¹) = σ(u)⁻¹（作用が準同型であることから）。 -/
theorem kummerUnitAct_inv (K : IUTField) (σ : FieldAut K)
    (u : (tateMultGroup K).carrier) :
    kummerUnitAct K σ ((tateMultGroup K).inv u)
      = (tateMultGroup K).inv (kummerUnitAct K σ u) := by
  apply (tateMultGroup K).inv_eq_of_mul_eq_one
  rw [← kummerUnitAct_mul, (tateMultGroup K).mul_inv]
  exact kummerUnitAct_one K σ

/-- **作用は群冪を保つ**: σ(uⁿ) = σ(u)ⁿ（乗法・単位の保存から帰納で）。 -/
theorem kummerUnitAct_npow (K : IUTField) (σ : FieldAut K)
    (u : (tateMultGroup K).carrier) : ∀ n : Nat,
    kummerUnitAct K σ (tateNpow (tateMultGroup K) u n)
      = tateNpow (tateMultGroup K) (kummerUnitAct K σ u) n := by
  intro n
  induction n with
  | zero => exact kummerUnitAct_one K σ
  | succ k ih =>
    show kummerUnitAct K σ ((tateMultGroup K).mul (tateNpow (tateMultGroup K) u k) u)
      = (tateMultGroup K).mul (tateNpow (tateMultGroup K) (kummerUnitAct K σ u) k)
          (kummerUnitAct K σ u)
    rw [kummerUnitAct_mul, ih]

/-- **作用は合成と両立**: (σ∘τ)(r) = σ(τ(r))。 -/
theorem kummerUnitAct_comp (K : IUTField) (σ τ : FieldAut K)
    (r : (tateMultGroup K).carrier) :
    kummerUnitAct K (fieldAutComp σ τ) r
      = kummerUnitAct K σ (kummerUnitAct K τ r) :=
  Subtype.ext rfl

/-! ## M320F-5: Kummer 写像 σ ↦ σ(r)/r と 1-コサイクル則 -/

/-- **Kummer コサイクル c_r(σ) = σ(r)·r⁻¹**（M320F-5）— rⁿ=x なる n 乗根 r
    （witness）に対し、σ ↦ σ(r)/r∈μ_n を与える。IUT の Kummer 写像の中身。 -/
def kummerCocycle (K : IUTField) (r : (tateMultGroup K).carrier) (σ : FieldAut K) :
    (tateMultGroup K).carrier :=
  (tateMultGroup K).mul (kummerUnitAct K σ r) ((tateMultGroup K).inv r)

/-- **Kummer 写像本体** — x=rⁿ の n 乗根 r に対し σ ↦ c_r(σ)=σ(r)/r。 -/
def kummerMap (K : IUTField) (r : (tateMultGroup K).carrier) :
    FieldAut K → (tateMultGroup K).carrier :=
  fun σ => kummerCocycle K r σ

/-- **1-コサイクル則（本物）** — c_r(στ) = c_r(σ)·σ(c_r(τ))。
    証明: σ(τ(r))·r⁻¹ = (σ(r)·r⁻¹)·(σ(τ(r))·σ(r)⁻¹) を可換群の並べ替え
    `kummerRearrange` で閉じる（作用の合成・乗法・逆元の保存を使う）。 -/
theorem kummer_cocycle (K : IUTField) (r : (tateMultGroup K).carrier)
    (σ τ : FieldAut K) :
    kummerCocycle K r (fieldAutComp σ τ)
      = (tateMultGroup K).mul (kummerCocycle K r σ)
          (kummerUnitAct K σ (kummerCocycle K r τ)) := by
  show (tateMultGroup K).mul (kummerUnitAct K (fieldAutComp σ τ) r)
        ((tateMultGroup K).inv r)
    = (tateMultGroup K).mul
        ((tateMultGroup K).mul (kummerUnitAct K σ r) ((tateMultGroup K).inv r))
        (kummerUnitAct K σ
          ((tateMultGroup K).mul (kummerUnitAct K τ r) ((tateMultGroup K).inv r)))
  rw [kummerUnitAct_comp, kummerUnitAct_mul, kummerUnitAct_inv]
  exact (kummerRearrange (tateMultGroup K) (tateMultGroup_comm K)
    (kummerUnitAct K σ r) ((tateMultGroup K).inv r)
    (kummerUnitAct K σ (kummerUnitAct K τ r))).symm

/-- **c_r(σ) ∈ μ_n（本物、σ 固定下）** — σ が x=rⁿ を固定するとき
    c_r(σ)ⁿ = σ(rⁿ)·(rⁿ)⁻¹ = σ(x)·x⁻¹ = 1、すなわち c_r(σ) は 1 の n 乗根。
    `hfix` は Gal(L/K) が基礎体の元 x=rⁿ を固定するという本物の条件。 -/
theorem kummer_cocycle_in_mu (K : IUTField) (n : Nat)
    (r : (tateMultGroup K).carrier) (σ : FieldAut K)
    (hfix : kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n) :
    (tateTorMuSubgroup K n).mem (kummerCocycle K r σ) := by
  show tateNpow (tateMultGroup K)
      ((tateMultGroup K).mul (kummerUnitAct K σ r) ((tateMultGroup K).inv r)) n
    = (tateMultGroup K).one
  rw [tateTorMulPow (tateMultGroup K) (tateMultGroup_comm K)
      (kummerUnitAct K σ r) ((tateMultGroup K).inv r) n,
    tateTorInvPow (tateMultGroup K) (tateMultGroup_comm K) r n,
    ← kummerUnitAct_npow, hfix, (tateMultGroup K).mul_inv]

/-! ## M320F-6: コバウンダリと well-defined（(K^×)ⁿ 法）・単射方向の核 -/

/-- **Kummer コバウンダリ d_z(σ) = σ(z)·z⁻¹**（M320F-6）— z∈K^× の主コサイクル。
    n 乗根 r → r·z の取り替えでコサイクルが d_z だけずれる（H¹ での類の well-defined）。 -/
def kummerCoboundary (K : IUTField) (z : (tateMultGroup K).carrier) (σ : FieldAut K) :
    (tateMultGroup K).carrier :=
  (tateMultGroup K).mul (kummerUnitAct K σ z) ((tateMultGroup K).inv z)

/-- **r について準同型（本物）** — c_{rz}(σ) = c_r(σ)·c_z(σ)。
    r↦c_r(σ) が乗法的 ＝ n 乗根の取り替え r→r·z でコサイクルがコバウンダリ
    d_z だけずれる（Kummer 類が (K^×)ⁿ を法として well-defined の核）。 -/
theorem kummer_cocycle_mul (K : IUTField) (r z : (tateMultGroup K).carrier)
    (σ : FieldAut K) :
    kummerCocycle K ((tateMultGroup K).mul r z) σ
      = (tateMultGroup K).mul (kummerCocycle K r σ) (kummerCocycle K z σ) := by
  show (tateMultGroup K).mul (kummerUnitAct K σ ((tateMultGroup K).mul r z))
        ((tateMultGroup K).inv ((tateMultGroup K).mul r z))
    = (tateMultGroup K).mul
        ((tateMultGroup K).mul (kummerUnitAct K σ r) ((tateMultGroup K).inv r))
        ((tateMultGroup K).mul (kummerUnitAct K σ z) ((tateMultGroup K).inv z))
  rw [kummerUnitAct_mul]
  exact kummerRearrange2 (tateMultGroup K) (tateMultGroup_comm K)
    (kummerUnitAct K σ r) (kummerUnitAct K σ z) r z

/-- **well-defined（(K^×)ⁿ 法、本物）** — n 乗根を r→r·z に取り替えると Kummer
    コサイクルはコバウンダリ d_z だけずれる: c_{rz}(σ) = c_r(σ)·d_z(σ)。
    H¹(G_K,μ_n) での Kummer 類が (K^×)ⁿ を法として矛盾なく定まることの本物の核。 -/
theorem kummer_h1_welldefined (K : IUTField) (r z : (tateMultGroup K).carrier)
    (σ : FieldAut K) :
    kummerCocycle K ((tateMultGroup K).mul r z) σ
      = (tateMultGroup K).mul (kummerCocycle K r σ) (kummerCoboundary K z σ) :=
  kummer_cocycle_mul K r z σ

/-- **コサイクル自明 ⟺ σ-固定（本物、単射方向の核）** — c_r(σ)=1 ⟺ σ(r)=r。
    Kummer コサイクルがすべての σ で自明なら r は Galois-固定（r∈基礎体）、
    すなわち x=rⁿ は基礎体で既に n 乗元 ＝ K^×/(K^×)ⁿ → H¹ の単射性の本物の核。 -/
theorem kummer_cocycle_trivial_iff (K : IUTField) (r : (tateMultGroup K).carrier)
    (σ : FieldAut K) :
    kummerCocycle K r σ = (tateMultGroup K).one ↔ kummerUnitAct K σ r = r := by
  constructor
  · intro h
    have hr : (tateMultGroup K).mul r ((tateMultGroup K).inv r) = (tateMultGroup K).one :=
      (tateMultGroup K).mul_inv r
    have h2 : (tateMultGroup K).mul (kummerUnitAct K σ r) ((tateMultGroup K).inv r)
            = (tateMultGroup K).mul r ((tateMultGroup K).inv r) := by
      rw [hr]
      exact h
    exact (tateMultGroup K).mul_right_cancel h2
  · intro h
    show (tateMultGroup K).mul (kummerUnitAct K σ r) ((tateMultGroup K).inv r)
      = (tateMultGroup K).one
    rw [h, (tateMultGroup K).mul_inv]

/-! ## M320F-7: Kummer 完全列 1→μ_n→K^×→K^×→K^×/(K^×)ⁿ→1 の各点 -/

/-- **完全列 μ_n の点（本物）** — n 乗写像の核はちょうど μ_n（xⁿ=1）。
    完全列 1→μ_n→K^×→(x↦xⁿ)→K^× の左端の完全性（ker(n 乗)=μ_n）。 -/
theorem kummer_exact_at_mu (K : IUTField) (n : Nat) (x : (tateMultGroup K).carrier) :
    (kerSubgroup (kummerNthPow K n)).mem x ↔ (tateTorMuSubgroup K n).mem x :=
  Iff.rfl

/-- **完全列 K^× の点（本物）** — n 乗写像の像 (K^×)ⁿ はちょうど射影 K^×→K^×/(K^×)ⁿ
    の核。完全列 K^×→(x↦xⁿ)→K^×→(射影)→K^×/(K^×)ⁿ の中央の完全性
    （im(n 乗)=ker(射影)）。 -/
theorem kummer_exact_at_units (K : IUTField) (n : Nat) (a : (tateMultGroup K).carrier) :
    (kummerNthPowersSubgroup K n).mem a
      ↔ (kummerProj K n).map a = (kummerQuotient K n).one :=
  (quotientProjN_ker (tateMultGroup K) (kummerNthPowersSubgroup K n)
    (kummer_nthPowers_isNormal K n) a).symm

/-- **完全列の右端（本物）** — 射影 K^×→K^×/(K^×)ⁿ は全射。 -/
theorem kummer_proj_surjective (K : IUTField) (n : Nat) :
    ∀ y, ∃ a, (kummerProj K n).map a = y :=
  quotientProjN_surjective (tateMultGroup K) (kummerNthPowersSubgroup K n)
    (kummer_nthPowers_isNormal K n)

/-! ## M320F-8: capstone -/

/-- **Kummer 理論の総括データ**（M320F-8）— 次数 n・n 乗写像（準同型）・像 (K^×)ⁿ・
    Kummer 商 K^×/(K^×)ⁿ・μ_n・完全列の核=像を束ねる。 -/
structure KummerData (K : IUTField) where
  /-- Kummer 次数 n（IUT では素数 l）。 -/
  n : Nat
  /-- n 乗写像 x↦xⁿ（本物の群準同型）。 -/
  nthPow : Hom (tateMultGroup K) (tateMultGroup K)
  /-- nthPow = 本物の n 乗写像。 -/
  isNthPow : nthPow = kummerNthPow K n
  /-- 像 (K^×)ⁿ（本物の部分群）。 -/
  nthPowers : Subgroup (tateMultGroup K)
  /-- nthPowers = (K^×)ⁿ。 -/
  isNthPowers : nthPowers = kummerNthPowersSubgroup K n
  /-- Kummer 商 K^×/(K^×)ⁿ（本物のアーベル商群）。 -/
  quotient : Grp
  /-- quotient = K^×/(K^×)ⁿ。 -/
  isQuotient : quotient = kummerQuotient K n
  /-- μ_n（1 の n 乗根）。 -/
  mu : Subgroup (tateMultGroup K)
  /-- mu = μ_n。 -/
  isMu : mu = tateTorMuSubgroup K n
  /-- 完全列左端: ker(n 乗) = μ_n。 -/
  kernel_eq_mu : ∀ x, (kerSubgroup nthPow).mem x ↔ mu.mem x
  /-- quotient はアーベル群。 -/
  quotient_abelian : ∀ x y, quotient.mul x y = quotient.mul y x

/-- **witness** — 任意の体 K・任意の次数 n に対し Kummer データが存在する
    （n 乗写像・像・商・μ_n を本物で与え、完全列の核=像を本物で示す）。 -/
def kummerData (K : IUTField) (n : Nat) : KummerData K where
  n := n
  nthPow := kummerNthPow K n
  isNthPow := rfl
  nthPowers := kummerNthPowersSubgroup K n
  isNthPowers := rfl
  quotient := kummerQuotient K n
  isQuotient := rfl
  mu := tateTorMuSubgroup K n
  isMu := rfl
  kernel_eq_mu := fun x => kummer_exact_at_mu K n x
  quotient_abelian := kummer_quotient_isAbelian K n

/-- **Kummer データの存在**（任意の体 K）。 -/
theorem kummer_exists (K : IUTField) (n : Nat) : Nonempty (KummerData K) :=
  ⟨kummerData K n⟩

/-- **K^×/(K^×)ⁿ が群（capstone）** — Kummer 商は本物の群（結合律）。 -/
theorem kummer_quotient_group (K : IUTField) (n : Nat) :
    ∀ x y z : (kummerQuotient K n).carrier,
      (kummerQuotient K n).mul ((kummerQuotient K n).mul x y) z
        = (kummerQuotient K n).mul x ((kummerQuotient K n).mul y z) :=
  (kummerQuotient K n).mul_assoc

/-- **n 乗写像が準同型（capstone）** — (xy)ⁿ = xⁿ·yⁿ。 -/
theorem kummer_nthPow_hom (K : IUTField) (n : Nat) :
    ∀ a b : (tateMultGroup K).carrier,
      (kummerNthPow K n).map ((tateMultGroup K).mul a b)
        = (tateMultGroup K).mul ((kummerNthPow K n).map a) ((kummerNthPow K n).map b) :=
  (kummerNthPow K n).map_mul

/-- **実例 ℚ^×/(ℚ^×)²（±符号）** — 有理数体 ℚ の n=2 の Kummer 商
    ℚ^×/(ℚ^×)²（平方類群、±符号と素因数の偶奇を測る）の Kummer データが存在。 -/
theorem kummer_exists_rat_sq : Nonempty (KummerData ratIUTField) :=
  ⟨kummerData ratIUTField 2⟩

/-- **実例（IUT の l-捻れ）** — n=l（素数）で K^×/(K^×)^l。Mochizuki の IUT が
    テータ値を評価する l-捻れの Kummer 理論（Kummer-detachment の代数的核）。 -/
theorem kummer_prime_example (K : IUTField) (l : Nat) : Nonempty (KummerData K) :=
  ⟨kummerData K l⟩

end IUT
