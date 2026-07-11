/-
  IUT/Q3ThetaGroup.lean — A8d（柱A A8/E 接続: 実 E₉(ℚ₃) 上の実 Mumford テータ群）

  ── 主要成果の分類: **[実／昇格(a)+本物建設(b)]**。
     昇格(a): q3cu 正直限定 1 が名指しした「Mumford テータ群 1→μ₂→G(L)→E[2]→1
     （柱E EtaleTheta の幾何的実現）」を実 E₉(ℚ₃)=q3tCurve 2 の上でゼロから建設し、
     A8「非自明惰性型交換子の実担体ゼロ」の**テータ群 half を discharge**する。
     本物建設(b): 実直線束 L²^× の実全空間（降下 Quot）・実単項式束自己同型群 M・
     実 Weil ペアリングをゼロから建設。テータ群を fiat でなく**降下元 g_τ の中心化群
     C_M(g_τ)** として導出（cocycle は可換性条件 qᵃw²=1 の解）。

  complete_pct 影響: **A8 のみ前進**（設計 audit/theta-heisenberg-real-cover-detail-2026-07-11.md
  §5 見込み A8 0.60→0.65・柱A 51→52・独立監査確定が条件）。A5/A7/E は今回主張しない。
  主要内容:
  (i)   実単項式束自己同型群 q3thM（台 (ℚ₃^××ℤ)×ℚ₃^×・積 (c,a,w)(c',a',w')=(cc'w'ᵃ,a+a',ww')・
        結合律は §2.4-1 の成分計算）、
  (ii)  忠実な実作用 q3thAct（ρ(c,a,w)(u,t)=(wu, c·uᵃ·t)）・準同型 q3th_act_hom・忠実性
        q3th_act_faithful、
  (iii) 実降下元 g_τ=(q⁻¹,−2,q)・冪の閉形式 g_τⁿ=(q^{−n²},−2n,qⁿ)（q3th_tau_pow）、
  (iv)  実 L²^× 全空間 q3thTotal（Quot of T by g_τ orbit）・射影 q3thProjE、
  (v)   交換子恒等式 [g,g_τ]=(qᵃw²,0,1)・**中心化群条件 qᵃw²=1**・テータ群 q3thGrp・
        q3th_mem_iff（⟺ a=−j ∧ u₀²=1・q3cu_mu2_complete 消費）、
  (vi)  射影像＝Klein=E₉[2]（q3cu_ker_eq_klein 消費・4 点 witness）・
        核＝ℚ₃^××q^ℤ 中心（q3th_ker_central）・スカラー c·q^{t²}（E2 二次指数の実現）、
  (vii) ★ 交換子＝実 Weil ペアリング ∈ 実 μ₂ ⊂ ℤ₃^×（q3th_comm_eq_weil）・lift 非依存・
        交代・非退化・**[g_{[3]},g_{[−1]}]=(0,q3tNegOne)≠1**（q3th_nonabelian・実曲線に
        接続された初の非可換対象）。

  正直な限定（§4 準拠・消去/弱化しない・既存 surrogate/正直申告は消さない）:
  1. **「直線束」は 𝔾_m-torsor 部分のみ**（L²^×）。零切断・ファイバーの加法構造（ℚ₃-直線）・
     切断の空間 Γ(L²) は無い。次数 2 は降下 cocycle q⁻¹u⁻² の簿記としてのみ実現。
  2. **実テータ関数はゼロのまま**。収束 p 進テータ級数・その切断としての実現・Galois 同変
     評価は外部/後続。q3thGrp は切断上の作用素でなく降下可換性で定義される（Mumford 定義と
     同値だがその同値性自体は主張しない）。
  3. **cuspidal 惰性 proper・cuspidalization 本体（π₁ 再構成）は依然 0**。q3thGrp の交換子は
     「惰性＝交換子」の CARRIER を与えるが、π₁(E∖{O}) の惰性部分群との同定（π₁-identification）
     は未達。q3cu 正直限定 1 は**部分 discharge**（テータ群 half のみ・スキーム分岐被覆 half 残存）。
  4. **G_{ℚ₃} 作用ゼロ**。q3thGrp への実ガロア作用・χ 捻りは後続（A7 の入口）。
  5. **単一切片**: p=3・q=9・レベル 2（μ₂）のみ。奇 l・μ_l（l≥5）・一般 q は後続。
  6. **二重計上の排除（§4-6・監査向け・明示）**:
     - vs M384F/M429F（ℤ³ thetaGrp 代理）: 本モジュールの台は (ℚ₃^××ℤ)×ℚ₃^×・所属方程式
       qᵃw²=1 は実 q3tGrp 内の等式・交換子値は実 ℤ₃^× 単数（抽象 ℤ でない）。
       **ℤ³ thetaGrp への比較準同型は今回作らない**（A5/A7 後続の仕事として意図的に残す）。
     - vs q3cu（A8c）: q3cu_ker_eq_klein/mu2_complete は**消費**（再証明しない）。
     - A5 status・E status は今回**主張しない**。A7 mono-theta 剛性も主張しない（setup のみ）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。
-/
import IUT.Q3TateCuspidalization
import IUT.TateCurve

namespace IUT

/-! ## q3th-helpers: 実 ℚ₃^×（可換群 q3tGrp）上の整数冪の補助則 -/

/-- 可換左移動: a·(b·c) = b·(a·c)（q3t_comm）。 -/
theorem q3th_lc (a b c : q3tGrp.carrier) :
    q3tGrp.mul a (q3tGrp.mul b c) = q3tGrp.mul b (q3tGrp.mul a c) := by
  rw [← q3tGrp.mul_assoc, q3t_comm a b, q3tGrp.mul_assoc]

/-- 可換右移動: (a·b)·c = (a·c)·b（q3t_comm）。 -/
theorem q3th_rc (a b c : q3tGrp.carrier) :
    q3tGrp.mul (q3tGrp.mul a b) c = q3tGrp.mul (q3tGrp.mul a c) b := by
  rw [q3tGrp.mul_assoc, q3t_comm b c, ← q3tGrp.mul_assoc]

/-- 可換群での逆元分配: (x·y)⁻¹ = x⁻¹·y⁻¹。 -/
theorem q3th_inv_dist (x y : q3tGrp.carrier) :
    q3tGrp.inv (q3tGrp.mul x y) = q3tGrp.mul (q3tGrp.inv x) (q3tGrp.inv y) := by
  rw [Grp.inv_mul_rev, q3t_comm]

/-- 自然数冪の積分配（可換）: (x·y)ⁿ = xⁿ·yⁿ。 -/
theorem q3th_npow_mul (x y : q3tGrp.carrier) : ∀ k : Nat,
    tateNpow q3tGrp (q3tGrp.mul x y) k
      = q3tGrp.mul (tateNpow q3tGrp x k) (tateNpow q3tGrp y k) := by
  intro k
  induction k with
  | zero =>
    show q3tGrp.one = q3tGrp.mul q3tGrp.one q3tGrp.one
    rw [q3tGrp.one_mul]
  | succ j ih =>
    show q3tGrp.mul (tateNpow q3tGrp (q3tGrp.mul x y) j) (q3tGrp.mul x y)
        = q3tGrp.mul (q3tGrp.mul (tateNpow q3tGrp x j) x)
            (q3tGrp.mul (tateNpow q3tGrp y j) y)
    rw [ih, q3tGrp.mul_assoc, q3th_lc (tateNpow q3tGrp y j) x y, ← q3tGrp.mul_assoc]

/-- 整数冪の積分配（可換）: (x·y)ⁿ = xⁿ·yⁿ（全整数 n）。 -/
theorem q3th_zpow_mul (x y : q3tGrp.carrier) (n : Int) :
    tateZpow q3tGrp (q3tGrp.mul x y) n
      = q3tGrp.mul (tateZpow q3tGrp x n) (tateZpow q3tGrp y n) := by
  cases n with
  | ofNat k =>
    show tateNpow q3tGrp (q3tGrp.mul x y) k
        = q3tGrp.mul (tateNpow q3tGrp x k) (tateNpow q3tGrp y k)
    exact q3th_npow_mul x y k
  | negSucc k =>
    show tateNpow q3tGrp (q3tGrp.inv (q3tGrp.mul x y)) (k + 1)
        = q3tGrp.mul (tateNpow q3tGrp (q3tGrp.inv x) (k + 1))
            (tateNpow q3tGrp (q3tGrp.inv y) (k + 1))
    rw [q3th_inv_dist, q3th_npow_mul]

/-- 逆底の整数冪＝負冪: (g⁻¹)ⁿ = g^{−n}（全整数 n）。 -/
theorem q3th_zpow_inv_eq (g : q3tGrp.carrier) : ∀ n : Int,
    tateZpow q3tGrp (q3tGrp.inv g) n = tateZpow q3tGrp g (-n) := by
  intro n
  cases n with
  | ofNat k =>
    show tateNpow q3tGrp (q3tGrp.inv g) k = tateZpow q3tGrp g (-((k : Nat) : Int))
    induction k with
    | zero => rfl
    | succ j ih =>
      show q3tGrp.mul (tateNpow q3tGrp (q3tGrp.inv g) j) (q3tGrp.inv g)
          = tateZpow q3tGrp g (-(((j + 1 : Nat) : Int)))
      rw [ih]
      have hidx : -(((j + 1 : Nat) : Int)) = -((j : Nat) : Int) + (-1) := by omega
      have h1 : tateZpow q3tGrp g (-1) = q3tGrp.inv g := tateZpow_negOne q3tGrp g
      rw [hidx, tateZpow_add, h1]
  | negSucc k =>
    show tateNpow q3tGrp (q3tGrp.inv (q3tGrp.inv g)) (k + 1)
        = tateZpow q3tGrp g (-(Int.negSucc k))
    rw [Grp.inv_inv]
    have hidx : -(Int.negSucc k) = ((k + 1 : Nat) : Int) := by omega
    rw [hidx]
    rfl

/-- 逆底の整数冪＝冪の逆: (g⁻¹)ⁿ = (gⁿ)⁻¹。 -/
theorem q3th_zpow_inv (g : q3tGrp.carrier) (n : Int) :
    tateZpow q3tGrp (q3tGrp.inv g) n = q3tGrp.inv (tateZpow q3tGrp g n) := by
  rw [q3th_zpow_inv_eq, tateZpow_neg]

/-- 単位の整数冪は単位: 1ⁿ = 1。 -/
theorem q3th_npow_one_id (k : Nat) :
    tateNpow q3tGrp q3tGrp.one k = q3tGrp.one := by
  induction k with
  | zero => rfl
  | succ j ih =>
    show q3tGrp.mul (tateNpow q3tGrp q3tGrp.one j) q3tGrp.one = q3tGrp.one
    rw [ih, q3tGrp.one_mul]

/-- 単位の整数冪は単位（全整数）。 -/
theorem q3th_zpow_one_id (n : Int) :
    tateZpow q3tGrp q3tGrp.one n = q3tGrp.one := by
  cases n with
  | ofNat k => exact q3th_npow_one_id k
  | negSucc k =>
    show tateNpow q3tGrp (q3tGrp.inv q3tGrp.one) (k + 1) = q3tGrp.one
    rw [Grp.inv_one]
    exact q3th_npow_one_id (k + 1)

/-! ## q3th-0: ★ 実単項式束自己同型群 M（台 (ℚ₃^××ℤ)×ℚ₃^×） -/

/-- M の台 = (ℚ₃^× × ℤ) × ℚ₃^×。元 (c,a,w)：c=スカラー因子・a=自己同型指数・w=平行移動。 -/
abbrev q3thCar : Type := (q3tGrp.carrier × Int) × q3tGrp.carrier

/-- M の積 (c,a,w)·(c',a',w') = (c·c'·w'ᵃ, a+a', w·w')。 -/
def q3thMul (g g' : q3thCar) : q3thCar :=
  ((q3tGrp.mul (q3tGrp.mul g.1.1 g'.1.1) (tateZpow q3tGrp g'.2 g.1.2), g.1.2 + g'.1.2),
   q3tGrp.mul g.2 g'.2)

/-- M の単位元 (1,0,1)。 -/
def q3thOne : q3thCar := ((q3tGrp.one, (0 : Int)), q3tGrp.one)

/-- M の逆元 (c,a,w)⁻¹ = (c⁻¹·wᵃ, −a, w⁻¹)。 -/
def q3thInv (g : q3thCar) : q3thCar :=
  ((q3tGrp.mul (q3tGrp.inv g.1.1) (tateZpow q3tGrp g.2 g.1.2), -g.1.2), q3tGrp.inv g.2)

/-- **q3th-0a: M の結合律**（§2.4-1 の成分計算）。第 1 成分は可換 ℚ₃^× 内で
    tateZpow_add・q3th_zpow_mul により両辺が
    c₁c₂c₃·w₂^{a₁}·w₃^{a₁}·w₃^{a₂} に正規化される。 -/
theorem q3thMul_assoc (a b c : q3thCar) :
    q3thMul (q3thMul a b) c = q3thMul a (q3thMul b c) := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := a
  obtain ⟨⟨c2, e2⟩, w2⟩ := b
  obtain ⟨⟨c3, e3⟩, w3⟩ := c
  show ((q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) (tateZpow q3tGrp w2 e1)) c3)
          (tateZpow q3tGrp w3 (e1 + e2)), (e1 + e2) + e3),
        q3tGrp.mul (q3tGrp.mul w1 w2) w3)
     = ((q3tGrp.mul (q3tGrp.mul c1
          (q3tGrp.mul (q3tGrp.mul c2 c3) (tateZpow q3tGrp w3 e2)))
          (tateZpow q3tGrp (q3tGrp.mul w2 w3) e1), e1 + (e2 + e3)),
        q3tGrp.mul w1 (q3tGrp.mul w2 w3))
  have hA : (e1 + e2) + e3 = e1 + (e2 + e3) := by omega
  have hW : q3tGrp.mul (q3tGrp.mul w1 w2) w3 = q3tGrp.mul w1 (q3tGrp.mul w2 w3) :=
    q3tGrp.mul_assoc w1 w2 w3
  have hC : q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) (tateZpow q3tGrp w2 e1)) c3)
          (tateZpow q3tGrp w3 (e1 + e2))
      = q3tGrp.mul (q3tGrp.mul c1
          (q3tGrp.mul (q3tGrp.mul c2 c3) (tateZpow q3tGrp w3 e2)))
          (tateZpow q3tGrp (q3tGrp.mul w2 w3) e1) := by
    rw [tateZpow_add q3tGrp w3 e1 e2, q3th_zpow_mul w2 w3 e1]
    generalize tateZpow q3tGrp w2 e1 = s
    generalize tateZpow q3tGrp w3 e1 = t
    generalize tateZpow q3tGrp w3 e2 = u
    -- LHS: ((((c1 c2) s) c3) (t u))   RHS: ((c1 ((c2 c3) u)) (s t))
    -- 両辺を N = (((((c1 c2) c3) s) t) u) へ
    have hL :
        q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) s) c3) (q3tGrp.mul t u)
        = q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) c3) s) t) u := by
      rw [← q3tGrp.mul_assoc (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) s) c3) t u,
          q3th_rc (q3tGrp.mul c1 c2) s c3]
    have hR :
        q3tGrp.mul (q3tGrp.mul c1 (q3tGrp.mul (q3tGrp.mul c2 c3) u)) (q3tGrp.mul s t)
        = q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) c3) s) t) u := by
      rw [← q3tGrp.mul_assoc c1 (q3tGrp.mul c2 c3) u,
          ← q3tGrp.mul_assoc c1 c2 c3,
          ← q3tGrp.mul_assoc (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) c3) u) s t,
          q3th_rc (q3tGrp.mul (q3tGrp.mul c1 c2) c3) u s,
          q3th_rc (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) c3) s) u t]
    rw [hL, hR]
  rw [hA, hW, hC]

/-- **q3th-0b: M の左単位律** 1·(c,a,w)=(c,a,w)。 -/
theorem q3thOne_mul (a : q3thCar) : q3thMul q3thOne a = a := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := a
  show ((q3tGrp.mul (q3tGrp.mul q3tGrp.one c1) (tateZpow q3tGrp w1 0), (0 : Int) + e1),
        q3tGrp.mul q3tGrp.one w1) = ((c1, e1), w1)
  have hC : q3tGrp.mul (q3tGrp.mul q3tGrp.one c1) (tateZpow q3tGrp w1 0) = c1 := by
    show q3tGrp.mul (q3tGrp.mul q3tGrp.one c1) q3tGrp.one = c1
    rw [q3tGrp.one_mul, q3tGrp.mul_one]
  have hA : (0 : Int) + e1 = e1 := by omega
  have hW : q3tGrp.mul q3tGrp.one w1 = w1 := q3tGrp.one_mul w1
  rw [hC, hA, hW]

/-- **q3th-0c: M の左逆律** (c,a,w)⁻¹·(c,a,w)=1。 -/
theorem q3thInv_mul (a : q3thCar) : q3thMul (q3thInv a) a = q3thOne := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := a
  show ((q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.inv c1) (tateZpow q3tGrp w1 e1)) c1)
          (tateZpow q3tGrp w1 (-e1)), (-e1) + e1), q3tGrp.mul (q3tGrp.inv w1) w1)
     = ((q3tGrp.one, (0 : Int)), q3tGrp.one)
  have hW : q3tGrp.mul (q3tGrp.inv w1) w1 = q3tGrp.one := q3tGrp.inv_mul w1
  have hA : (-e1) + e1 = (0 : Int) := by omega
  have hC : q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.inv c1) (tateZpow q3tGrp w1 e1)) c1)
          (tateZpow q3tGrp w1 (-e1)) = q3tGrp.one := by
    have hzneg : tateZpow q3tGrp w1 (-e1) = q3tGrp.inv (tateZpow q3tGrp w1 e1) :=
      tateZpow_neg q3tGrp w1 e1
    rw [hzneg]
    generalize tateZpow q3tGrp w1 e1 = z
    rw [q3th_rc (q3tGrp.inv c1) z c1, q3tGrp.inv_mul c1, q3tGrp.one_mul z, q3tGrp.mul_inv z]
  rw [hC, hA, hW]

/-- **q3th-0（★）: 実単項式束自己同型群 M**（実群・cocycle 積・§2.4 の実提示）。 -/
def q3thM : Grp where
  carrier := q3thCar
  mul := q3thMul
  one := q3thOne
  inv := q3thInv
  mul_assoc := q3thMul_assoc
  one_mul := q3thOne_mul
  inv_mul := q3thInv_mul

/-! ## q3th-1: ★ 実自明束 T への忠実な実作用 ρ -/

/-- 実自明束の台 T = ℚ₃^× × ℚ₃^×（底 u・ファイバー座標 t）。 -/
abbrev q3thT : Type := q3tGrp.carrier × q3tGrp.carrier

/-- **q3th-1a: 実作用** ρ(c,a,w)(u,t) = (w·u, c·uᵃ·t)。 -/
def q3thAct (g : q3thCar) (x : q3thT) : q3thT :=
  (q3tGrp.mul g.2 x.1,
   q3tGrp.mul (q3tGrp.mul g.1.1 (tateZpow q3tGrp x.1 g.1.2)) x.2)

/-- **q3th-1b（★）: ρ は準同型** ρ(g·g') = ρ(g)∘ρ(g')。第 2 成分は可換 ℚ₃^× 内で
    tateZpow_add（uᵃ⁺ᵃ'=uᵃuᵃ'）・q3th_zpow_mul（(w'u)ᵃ=w'ᵃuᵃ）で一致。 -/
theorem q3th_act_hom (g g' : q3thCar) (x : q3thT) :
    q3thAct (q3thMul g g') x = q3thAct g (q3thAct g' x) := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := g
  obtain ⟨⟨c2, e2⟩, w2⟩ := g'
  obtain ⟨u, t⟩ := x
  show (q3tGrp.mul (q3tGrp.mul w1 w2) u,
        q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) (tateZpow q3tGrp w2 e1))
          (tateZpow q3tGrp u (e1 + e2))) t)
     = (q3tGrp.mul w1 (q3tGrp.mul w2 u),
        q3tGrp.mul (q3tGrp.mul c1 (tateZpow q3tGrp (q3tGrp.mul w2 u) e1))
          (q3tGrp.mul (q3tGrp.mul c2 (tateZpow q3tGrp u e2)) t))
  have hfst : q3tGrp.mul (q3tGrp.mul w1 w2) u = q3tGrp.mul w1 (q3tGrp.mul w2 u) :=
    q3tGrp.mul_assoc w1 w2 u
  have hsnd :
      q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) (tateZpow q3tGrp w2 e1))
          (tateZpow q3tGrp u (e1 + e2))) t
      = q3tGrp.mul (q3tGrp.mul c1 (tateZpow q3tGrp (q3tGrp.mul w2 u) e1))
          (q3tGrp.mul (q3tGrp.mul c2 (tateZpow q3tGrp u e2)) t) := by
    rw [tateZpow_add q3tGrp u e1 e2, q3th_zpow_mul w2 u e1]
    generalize tateZpow q3tGrp w2 e1 = s
    generalize tateZpow q3tGrp u e1 = p
    generalize tateZpow q3tGrp u e2 = r
    -- LHS: ((((c1 c2) s) (p r)) t)   RHS: ((c1 (s p)) ((c2 r) t))
    have hL :
        q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) s) (q3tGrp.mul p r)) t
        = q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) s) p) r) t := by
      rw [← q3tGrp.mul_assoc (q3tGrp.mul (q3tGrp.mul c1 c2) s) p r]
    have hR :
        q3tGrp.mul (q3tGrp.mul c1 (q3tGrp.mul s p)) (q3tGrp.mul (q3tGrp.mul c2 r) t)
        = q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c1 c2) s) p) r) t := by
      rw [← q3tGrp.mul_assoc c1 s p,
          ← q3tGrp.mul_assoc (q3tGrp.mul (q3tGrp.mul c1 s) p) (q3tGrp.mul c2 r) t,
          ← q3tGrp.mul_assoc (q3tGrp.mul (q3tGrp.mul c1 s) p) c2 r,
          q3th_rc (q3tGrp.mul c1 s) p c2,
          q3th_rc c1 s c2]
    rw [hL, hR]
  rw [hfst, hsnd]

/-- q に対する uᵃ の付値: (q3tQ 2)ᵃ の第 1 成分＝2a（q3t_zpow_fst の再掲）。 -/
theorem q3th_q_zpow_fst (a : Int) :
    (tateZpow q3tGrp (q3tQ 2) a).1 = 2 * a := by
  have h := q3t_zpow_fst 2 a
  have hc : ((2 : Nat) : Int) = (2 : Int) := by omega
  rw [hc] at h
  exact h

/-- **q3th-1c（★）: ρ は忠実**（作用が等しければ元が等しい）。1=(1,1) で c・w を復元し、
    q=(q3tQ 2) の無限位数（第 1 成分 2a）で指数 a を復元する。 -/
theorem q3th_act_faithful (g g' : q3thCar)
    (h : ∀ x : q3thT, q3thAct g x = q3thAct g' x) : g = g' := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := g
  obtain ⟨⟨c2, e2⟩, w2⟩ := g'
  -- (1,1) で w と c を復元
  have h1 := h (q3tGrp.one, q3tGrp.one)
  have hw1 : q3tGrp.mul w1 q3tGrp.one = q3tGrp.mul w2 q3tGrp.one := congrArg Prod.fst h1
  have hw : w1 = w2 := by
    rw [q3tGrp.mul_one, q3tGrp.mul_one] at hw1; exact hw1
  have hc1 : q3tGrp.mul (q3tGrp.mul c1 (tateZpow q3tGrp q3tGrp.one e1)) q3tGrp.one
      = q3tGrp.mul (q3tGrp.mul c2 (tateZpow q3tGrp q3tGrp.one e2)) q3tGrp.one :=
    congrArg Prod.snd h1
  have hc : c1 = c2 := by
    rw [q3th_zpow_one_id e1, q3th_zpow_one_id e2, q3tGrp.mul_one, q3tGrp.mul_one,
        q3tGrp.mul_one, q3tGrp.mul_one] at hc1
    exact hc1
  -- (q,1) で指数 e を復元
  have hq := h (q3tQ 2, q3tGrp.one)
  have hqs : q3tGrp.mul (q3tGrp.mul c1 (tateZpow q3tGrp (q3tQ 2) e1)) q3tGrp.one
      = q3tGrp.mul (q3tGrp.mul c2 (tateZpow q3tGrp (q3tQ 2) e2)) q3tGrp.one :=
    congrArg Prod.snd hq
  have hqs2 : q3tGrp.mul c1 (tateZpow q3tGrp (q3tQ 2) e1)
      = q3tGrp.mul c2 (tateZpow q3tGrp (q3tQ 2) e2) := by
    rw [q3tGrp.mul_one, q3tGrp.mul_one] at hqs; exact hqs
  have hqs3 : tateZpow q3tGrp (q3tQ 2) e1 = tateZpow q3tGrp (q3tQ 2) e2 := by
    rw [hc] at hqs2
    exact q3tGrp.mul_left_cancel hqs2
  have he : e1 = e2 := by
    have hf : (tateZpow q3tGrp (q3tQ 2) e1).1 = (tateZpow q3tGrp (q3tQ 2) e2).1 :=
      congrArg Prod.fst hqs3
    rw [q3th_q_zpow_fst e1, q3th_q_zpow_fst e2] at hf
    exact Int.eq_of_mul_eq_mul_left (by omega) hf
  rw [hc, he, hw]

/-! ## q3th-2: ★ 実降下元 g_τ と冪の閉形式 g_τⁿ=(q^{−n²},−2n,qⁿ) -/

/-- **q3th-2a: 実降下元 g_τ = (q⁻¹, −2, q)**（q=q3tQ 2=9・実 Tate 降下）。 -/
def q3thTau : q3thCar := ((q3tGrp.inv (q3tQ 2), (-2 : Int)), q3tQ 2)

/-- g_τ の M-逆元の閉形式 g_τ⁻¹ = (q⁻¹, 2, q⁻¹)。 -/
def q3thTauInv : q3thCar := ((q3tGrp.inv (q3tQ 2), (2 : Int)), q3tGrp.inv (q3tQ 2))

/-- g² = g·g（整数冪 2）。 -/
theorem q3th_q_sq_gen (w : q3tGrp.carrier) :
    tateZpow q3tGrp w 2 = q3tGrp.mul w w := by
  have h : tateZpow q3tGrp w (1 + 1) = q3tGrp.mul (tateZpow q3tGrp w 1) w :=
    tateZpow_succ q3tGrp w 1
  rw [tateZpow_one] at h
  exact h

/-- q² = q·q。 -/
theorem q3th_q_sq : tateZpow q3tGrp (q3tQ 2) 2 = q3tGrp.mul (q3tQ 2) (q3tQ 2) :=
  q3th_q_sq_gen (q3tQ 2)

/-- **q3th-2b: g_τ の M-逆元** q3thInv g_τ = (q⁻¹, 2, q⁻¹)（inv_inv・q²=q·q の簿記）。 -/
theorem q3th_inv_tau : q3thInv q3thTau = q3thTauInv := by
  show ((q3tGrp.mul (q3tGrp.inv (q3tGrp.inv (q3tQ 2))) (tateZpow q3tGrp (q3tQ 2) (-2)),
        -(-2 : Int)), q3tGrp.inv (q3tQ 2))
     = ((q3tGrp.inv (q3tQ 2), (2 : Int)), q3tGrp.inv (q3tQ 2))
  have hA : -(-2 : Int) = (2 : Int) := by omega
  have hC : q3tGrp.mul (q3tGrp.inv (q3tGrp.inv (q3tQ 2))) (tateZpow q3tGrp (q3tQ 2) (-2))
      = q3tGrp.inv (q3tQ 2) := by
    rw [Grp.inv_inv, tateZpow_neg q3tGrp (q3tQ 2) 2, q3th_q_sq, q3th_inv_dist,
        ← q3tGrp.mul_assoc, q3tGrp.mul_inv, q3tGrp.one_mul]
  rw [hA, hC]

/-- **q3th-2c: g_τ の正冪** g_τᵏ=(q^{−k²},−2k,qᵏ)（k:Nat・後者則の帰納）。 -/
theorem q3th_tau_npow (k : Nat) :
    tateNpow q3thM q3thTau k
      = ((tateZpow q3tGrp (q3tQ 2) (-((k : Int) * (k : Int))), -2 * (k : Int)),
         tateZpow q3tGrp (q3tQ 2) (k : Int)) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    show q3thMul (tateNpow q3thM q3thTau j) q3thTau
        = ((tateZpow q3tGrp (q3tQ 2) (-(((j + 1 : Nat) : Int) * ((j + 1 : Nat) : Int))),
            -2 * ((j + 1 : Nat) : Int)), tateZpow q3tGrp (q3tQ 2) ((j + 1 : Nat) : Int))
    rw [ih]
    -- q3thMul (F_j) g_τ を成分展開
    show ((q3tGrp.mul (q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (-((j : Int) * (j : Int))))
            (q3tGrp.inv (q3tQ 2))) (tateZpow q3tGrp (q3tQ 2) (-2 * (j : Int))),
          (-2 * (j : Int)) + (-2)), q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (j : Int)) (q3tQ 2))
       = ((tateZpow q3tGrp (q3tQ 2) (-(((j + 1 : Nat) : Int) * ((j + 1 : Nat) : Int))),
           -2 * ((j + 1 : Nat) : Int)), tateZpow q3tGrp (q3tQ 2) ((j + 1 : Nat) : Int))
    have hcast : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
    have hq1 : q3tGrp.inv (q3tQ 2) = tateZpow q3tGrp (q3tQ 2) (-1) :=
      (tateZpow_negOne q3tGrp (q3tQ 2)).symm
    have hW : q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (j : Int)) (q3tQ 2)
        = tateZpow q3tGrp (q3tQ 2) ((j + 1 : Nat) : Int) := by
      rw [hcast]
      exact (tateZpow_succ q3tGrp (q3tQ 2) (j : Int)).symm
    have hA : (-2 * (j : Int)) + (-2) = -2 * ((j + 1 : Nat) : Int) := by
      rw [hcast]; omega
    have hC : q3tGrp.mul (q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (-((j : Int) * (j : Int))))
            (q3tGrp.inv (q3tQ 2))) (tateZpow q3tGrp (q3tQ 2) (-2 * (j : Int)))
        = tateZpow q3tGrp (q3tQ 2) (-(((j + 1 : Nat) : Int) * ((j + 1 : Nat) : Int))) := by
      rw [hq1, ← tateZpow_add, ← tateZpow_add]
      have hexp : (-((j : Int) * (j : Int)) + (-1)) + (-2 * (j : Int))
          = -(((j + 1 : Nat) : Int) * ((j + 1 : Nat) : Int)) := by
        rw [hcast]
        have hsq : ((j : Int) + 1) * ((j : Int) + 1) = (j : Int) * (j : Int) + 2 * (j : Int) + 1 :=
          sq_succ (j : Int)
        rw [hsq]
        generalize (j : Int) * (j : Int) = K
        omega
      rw [hexp]
    rw [hC, hA, hW]

/-- g_τ⁻¹ の正冪 (g_τ⁻¹)ᵏ=(q^{−k²},2k,q^{−k})（k:Nat・後者則の帰納）。 -/
theorem q3th_tauinv_npow (k : Nat) :
    tateNpow q3thM q3thTauInv k
      = ((tateZpow q3tGrp (q3tQ 2) (-((k : Int) * (k : Int))), 2 * (k : Int)),
         tateZpow q3tGrp (q3tQ 2) (-(k : Int))) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    show q3thMul (tateNpow q3thM q3thTauInv j) q3thTauInv
        = ((tateZpow q3tGrp (q3tQ 2) (-(((j + 1 : Nat) : Int) * ((j + 1 : Nat) : Int))),
            2 * ((j + 1 : Nat) : Int)), tateZpow q3tGrp (q3tQ 2) (-((j + 1 : Nat) : Int)))
    rw [ih]
    show ((q3tGrp.mul (q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (-((j : Int) * (j : Int))))
            (q3tGrp.inv (q3tQ 2))) (tateZpow q3tGrp (q3tGrp.inv (q3tQ 2)) (2 * (j : Int))),
          (2 * (j : Int)) + 2), q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (-(j : Int)))
            (q3tGrp.inv (q3tQ 2)))
       = ((tateZpow q3tGrp (q3tQ 2) (-(((j + 1 : Nat) : Int) * ((j + 1 : Nat) : Int))),
           2 * ((j + 1 : Nat) : Int)), tateZpow q3tGrp (q3tQ 2) (-((j + 1 : Nat) : Int)))
    have hcast : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
    have hq1 : q3tGrp.inv (q3tQ 2) = tateZpow q3tGrp (q3tQ 2) (-1) :=
      (tateZpow_negOne q3tGrp (q3tQ 2)).symm
    have hW : q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (-(j : Int))) (q3tGrp.inv (q3tQ 2))
        = tateZpow q3tGrp (q3tQ 2) (-((j + 1 : Nat) : Int)) := by
      rw [hq1, ← tateZpow_add, hcast]
      have : -(j : Int) + (-1) = -((j : Int) + 1) := by omega
      rw [this]
    have hA : (2 * (j : Int)) + 2 = 2 * ((j + 1 : Nat) : Int) := by rw [hcast]; omega
    have hC : q3tGrp.mul (q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (-((j : Int) * (j : Int))))
            (q3tGrp.inv (q3tQ 2))) (tateZpow q3tGrp (q3tGrp.inv (q3tQ 2)) (2 * (j : Int)))
        = tateZpow q3tGrp (q3tQ 2) (-(((j + 1 : Nat) : Int) * ((j + 1 : Nat) : Int))) := by
      rw [q3th_zpow_inv_eq (q3tQ 2) (2 * (j : Int)), hq1, ← tateZpow_add, ← tateZpow_add]
      have hexp : (-((j : Int) * (j : Int)) + (-1)) + (-(2 * (j : Int)))
          = -(((j + 1 : Nat) : Int) * ((j + 1 : Nat) : Int)) := by
        rw [hcast]
        have hsq : ((j : Int) + 1) * ((j : Int) + 1) = (j : Int) * (j : Int) + 2 * (j : Int) + 1 :=
          sq_succ (j : Int)
        rw [hsq]
        generalize (j : Int) * (j : Int) = K
        omega
      rw [hexp]
    rw [hC, hA, hW]

/-- **q3th-2d（★）: g_τ の冪の閉形式** g_τⁿ = (q^{−n²}, −2n, qⁿ)（全整数 n・
    §2.4-7・負冪側は g_τ⁻¹ の冪へ帰着して −(n+1)² の簿記を閉じる）。 -/
theorem q3th_tau_pow (n : Int) :
    tateZpow q3thM q3thTau n
      = ((tateZpow q3tGrp (q3tQ 2) (-(n * n)), -2 * n), tateZpow q3tGrp (q3tQ 2) n) := by
  cases n with
  | ofNat k =>
    show tateNpow q3thM q3thTau k
        = ((tateZpow q3tGrp (q3tQ 2) (-((Int.ofNat k) * (Int.ofNat k))), -2 * (Int.ofNat k)),
           tateZpow q3tGrp (q3tQ 2) (Int.ofNat k))
    exact q3th_tau_npow k
  | negSucc k =>
    show tateNpow q3thM (q3thInv q3thTau) (k + 1)
        = ((tateZpow q3tGrp (q3tQ 2) (-((Int.negSucc k) * (Int.negSucc k))),
            -2 * (Int.negSucc k)), tateZpow q3tGrp (q3tQ 2) (Int.negSucc k))
    rw [q3th_inv_tau, q3th_tauinv_npow (k + 1)]
    have hns : (Int.negSucc k) = -(((k + 1 : Nat) : Int)) := by omega
    have hsq : (Int.negSucc k) * (Int.negSucc k)
        = ((k + 1 : Nat) : Int) * ((k + 1 : Nat) : Int) := by
      rw [hns, Int.neg_mul_neg]
    have hA : 2 * ((k + 1 : Nat) : Int) = -2 * (Int.negSucc k) := by rw [hns]; omega
    have hW : tateZpow q3tGrp (q3tQ 2) (-((k + 1 : Nat) : Int))
        = tateZpow q3tGrp (q3tQ 2) (Int.negSucc k) := by rw [hns]
    rw [hsq, hA, hW]

/-! ## q3th-4: ★ 交換子恒等式・中心化群条件 qᵃw²=1・テータ群 q3thGrp -/

/-- M の交換子 [g,g'] = g·g'·g⁻¹·g'⁻¹。 -/
def q3thComm (g g' : q3thCar) : q3thCar :=
  q3thMul (q3thMul (q3thMul g g') (q3thInv g)) (q3thInv g')

/-- **中間積 (g·g')·g⁻¹ = (c'·w'ᵃ·w^{−a'}, a', w')**（§2.4-2 の第一段）。 -/
theorem q3th_P2 (g g' : q3thCar) :
    q3thMul (q3thMul g g') (q3thInv g)
      = ((q3tGrp.mul (q3tGrp.mul g'.1.1 (tateZpow q3tGrp g'.2 g.1.2))
            (tateZpow q3tGrp g.2 (-g'.1.2)), g'.1.2), g'.2) := by
  obtain ⟨⟨c, a⟩, w⟩ := g
  obtain ⟨⟨c', a'⟩, w'⟩ := g'
  show ((q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c c') (tateZpow q3tGrp w' a))
          (q3tGrp.mul (q3tGrp.inv c) (tateZpow q3tGrp w a)))
          (tateZpow q3tGrp (q3tGrp.inv w) (a + a')), (a + a') + (-a)),
        q3tGrp.mul (q3tGrp.mul w w') (q3tGrp.inv w))
     = ((q3tGrp.mul (q3tGrp.mul c' (tateZpow q3tGrp w' a)) (tateZpow q3tGrp w (-a')), a'), w')
  have hE : (a + a') + (-a) = a' := by omega
  have hW : q3tGrp.mul (q3tGrp.mul w w') (q3tGrp.inv w) = w' := by
    rw [q3th_rc w w' (q3tGrp.inv w), q3tGrp.mul_inv w, q3tGrp.one_mul]
  have hC : q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c c') (tateZpow q3tGrp w' a))
          (q3tGrp.mul (q3tGrp.inv c) (tateZpow q3tGrp w a)))
          (tateZpow q3tGrp (q3tGrp.inv w) (a + a'))
      = q3tGrp.mul (q3tGrp.mul c' (tateZpow q3tGrp w' a)) (tateZpow q3tGrp w (-a')) := by
    rw [q3th_zpow_inv_eq w (a + a')]
    have hTU : q3tGrp.mul (tateZpow q3tGrp w a) (tateZpow q3tGrp w (-(a + a')))
        = tateZpow q3tGrp w (-a') := by
      rw [← tateZpow_add]
      have hx : a + -(a + a') = -a' := by omega
      rw [hx]
    generalize hS : tateZpow q3tGrp w' a = S
    rw [← hTU]
    generalize tateZpow q3tGrp w a = T
    generalize tateZpow q3tGrp w (-(a + a')) = X
    rw [← q3tGrp.mul_assoc (q3tGrp.mul (q3tGrp.mul c c') S) (q3tGrp.inv c) T,
        q3th_rc (q3tGrp.mul c c') S (q3tGrp.inv c),
        q3th_rc c c' (q3tGrp.inv c),
        q3tGrp.mul_inv c, q3tGrp.one_mul c',
        ← q3tGrp.mul_assoc (q3tGrp.mul c' S) T X]
  rw [hC, hE, hW]

/-- **q3th-4a（★）: 交換子恒等式** [g,g'] = (w'ᵃ·w^{−a'}, 0, 1)（§2.4-2）。
    第 2（指数）成分は 0・平行移動成分は 1 で、非可換性はスカラー成分に宿る。 -/
theorem q3th_commutator (g g' : q3thCar) :
    q3thComm g g'
      = ((q3tGrp.mul (tateZpow q3tGrp g'.2 g.1.2) (tateZpow q3tGrp g.2 (-g'.1.2)),
          (0 : Int)), q3tGrp.one) := by
  show q3thMul (q3thMul (q3thMul g g') (q3thInv g)) (q3thInv g') = _
  rw [q3th_P2 g g']
  obtain ⟨⟨c, a⟩, w⟩ := g
  obtain ⟨⟨c', a'⟩, w'⟩ := g'
  show ((q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c' (tateZpow q3tGrp w' a))
            (tateZpow q3tGrp w (-a')))
          (q3tGrp.mul (q3tGrp.inv c') (tateZpow q3tGrp w' a')))
          (tateZpow q3tGrp (q3tGrp.inv w') a'), a' + (-a')), q3tGrp.mul w' (q3tGrp.inv w'))
     = ((q3tGrp.mul (tateZpow q3tGrp w' a) (tateZpow q3tGrp w (-a')), (0 : Int)), q3tGrp.one)
  have hE : a' + (-a') = (0 : Int) := by omega
  have hW : q3tGrp.mul w' (q3tGrp.inv w') = q3tGrp.one := q3tGrp.mul_inv w'
  have hC : q3tGrp.mul (q3tGrp.mul (q3tGrp.mul (q3tGrp.mul c' (tateZpow q3tGrp w' a))
            (tateZpow q3tGrp w (-a')))
          (q3tGrp.mul (q3tGrp.inv c') (tateZpow q3tGrp w' a')))
          (tateZpow q3tGrp (q3tGrp.inv w') a')
      = q3tGrp.mul (tateZpow q3tGrp w' a) (tateZpow q3tGrp w (-a')) := by
    rw [q3th_zpow_inv_eq w' a']
    have hPQ : q3tGrp.mul (tateZpow q3tGrp w' a') (tateZpow q3tGrp w' (-a')) = q3tGrp.one := by
      rw [← tateZpow_add]
      have hx : a' + -a' = (0 : Int) := by omega
      rw [hx]
      rfl
    generalize hS : tateZpow q3tGrp w' a = S
    generalize hV : tateZpow q3tGrp w (-a') = V
    -- goal: ((((c' S) V) (inv c' · P)) Q) = mul S V,  P·Q = 1
    rw [← q3tGrp.mul_assoc (q3tGrp.mul (q3tGrp.mul c' S) V) (q3tGrp.inv c')
          (tateZpow q3tGrp w' a'),
        q3th_rc (q3tGrp.mul c' S) V (q3tGrp.inv c'),
        q3th_rc c' S (q3tGrp.inv c'),
        q3tGrp.mul_inv c', q3tGrp.one_mul S,
        q3tGrp.mul_assoc (q3tGrp.mul S V) (tateZpow q3tGrp w' a') (tateZpow q3tGrp w' (-a')),
        hPQ, q3tGrp.mul_one]
  rw [hC, hE, hW]

/-- **q3th-4b: 中心化群条件** q3thMem g := qᵃ·w² = 1（実 q3tGrp 内の等式）。 -/
def q3thMem (g : q3thCar) : Prop :=
  q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) g.1.2) (q3tGrp.mul g.2 g.2) = q3tGrp.one

/-- q3thMem の成分値: qᵃ·w² = (2a+2j, u₀²)（q3th_q_zpow_fst・q3t_zpow_snd 消費）。 -/
theorem q3th_mem_val (a : Int) (j : Int) (u0 : (zpUnits 3 isPrime_three).carrier) :
    q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) a) (q3tGrp.mul (j, u0) (j, u0))
      = ((2 * a + (j + j)), (zpUnits 3 isPrime_three).mul u0 u0) := by
  show ((tateZpow q3tGrp (q3tQ 2) a).1 + (j + j),
        (zpUnits 3 isPrime_three).mul (tateZpow q3tGrp (q3tQ 2) a).2
          ((zpUnits 3 isPrime_three).mul u0 u0))
     = ((2 * a + (j + j)), (zpUnits 3 isPrime_three).mul u0 u0)
  rw [q3th_q_zpow_fst a, q3t_zpow_snd 2 a, (zpUnits 3 isPrime_three).one_mul]

/-- **q3th-4c（★）: 中心化群条件の成分解** qᵃw²=1 ⟺ a=−j ∧ u₀²=1、u₀²=1 は
    **q3cu_mu2_complete を消費**して u₀=±1 に確定（§2.4-3）。 -/
theorem q3th_mem_iff (g : q3thCar) :
    q3thMem g ↔ (g.1.2 = -(g.2.1) ∧
      (g.2.2 = (zpUnits 3 isPrime_three).one ∨ g.2.2 = q3tNegOne)) := by
  obtain ⟨⟨c, a⟩, j, u0⟩ := g
  show (q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) a) (q3tGrp.mul (j, u0) (j, u0)) = q3tGrp.one)
     ↔ (a = -j ∧ (u0 = (zpUnits 3 isPrime_three).one ∨ u0 = q3tNegOne))
  rw [q3th_mem_val a j u0]
  constructor
  · intro h
    have hfst : (2 * a + (j + j)) = (0 : Int) := congrArg Prod.fst h
    have hsnd : (zpUnits 3 isPrime_three).mul u0 u0 = (zpUnits 3 isPrime_three).one :=
      congrArg Prod.snd h
    exact ⟨by omega, q3cu_mu2_complete u0 hsnd⟩
  · intro h
    obtain ⟨ha, hu⟩ := h
    have hfst : (2 * a + (j + j)) = (0 : Int) := by omega
    have hsnd : (zpUnits 3 isPrime_three).mul u0 u0 = (zpUnits 3 isPrime_three).one := by
      obtain hu1 | hu2 := hu
      · rw [hu1]; exact (zpUnits 3 isPrime_three).one_mul _
      · rw [hu2]; exact q3tNegOne_sq
    show ((2 * a + (j + j)), (zpUnits 3 isPrime_three).mul u0 u0)
       = ((0 : Int), (zpUnits 3 isPrime_three).one)
    rw [hfst, hsnd]

/-- 単位元は中心化群条件を満たす。 -/
theorem q3th_mem_one : q3thMem q3thOne := by
  show q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) 0) (q3tGrp.mul q3tGrp.one q3tGrp.one) = q3tGrp.one
  rw [q3tGrp.one_mul q3tGrp.one]
  show q3tGrp.mul q3tGrp.one q3tGrp.one = q3tGrp.one
  rw [q3tGrp.one_mul]

/-- 中心化群は積で閉じる: qᵃw²=1 ∧ qᵃ'w'²=1 ⟹ q^{a+a'}(ww')²=1。 -/
theorem q3th_mem_mul (g g' : q3thCar) (hg : q3thMem g) (hg' : q3thMem g') :
    q3thMem (q3thMul g g') := by
  apply (q3th_mem_iff (q3thMul g g')).mpr
  obtain ⟨⟨c, a⟩, j, u0⟩ := g
  obtain ⟨⟨c', a'⟩, j', u0'⟩ := g'
  have ha : a = -j := ((q3th_mem_iff _).mp hg).1
  have hu : u0 = (zpUnits 3 isPrime_three).one ∨ u0 = q3tNegOne :=
    ((q3th_mem_iff _).mp hg).2
  have ha' : a' = -j' := ((q3th_mem_iff _).mp hg').1
  have hu' : u0' = (zpUnits 3 isPrime_three).one ∨ u0' = q3tNegOne :=
    ((q3th_mem_iff _).mp hg').2
  refine ⟨?_, ?_⟩
  · show a + a' = -(j + j')
    omega
  · show (zpUnits 3 isPrime_three).mul u0 u0' = (zpUnits 3 isPrime_three).one
      ∨ (zpUnits 3 isPrime_three).mul u0 u0' = q3tNegOne
    obtain hu1 | hu2 := hu
    · obtain hu1' | hu2' := hu'
      · left; rw [hu1, hu1']; exact (zpUnits 3 isPrime_three).one_mul _
      · right; rw [hu1, hu2']; exact (zpUnits 3 isPrime_three).one_mul _
    · obtain hu1' | hu2' := hu'
      · right; rw [hu2, hu1']; exact (zpUnits 3 isPrime_three).mul_one _
      · left; rw [hu2, hu2']; exact q3tNegOne_sq

/-- 中心化群は逆元で閉じる。 -/
theorem q3th_mem_inv (g : q3thCar) (hg : q3thMem g) : q3thMem (q3thInv g) := by
  apply (q3th_mem_iff (q3thInv g)).mpr
  obtain ⟨⟨c, a⟩, j, u0⟩ := g
  have ha : a = -j := ((q3th_mem_iff _).mp hg).1
  have hu : u0 = (zpUnits 3 isPrime_three).one ∨ u0 = q3tNegOne :=
    ((q3th_mem_iff _).mp hg).2
  refine ⟨?_, ?_⟩
  · show -a = -(-j)
    omega
  · show (zpUnits 3 isPrime_three).inv u0 = (zpUnits 3 isPrime_three).one
      ∨ (zpUnits 3 isPrime_three).inv u0 = q3tNegOne
    obtain hu1 | hu2 := hu
    · left; rw [hu1]; exact Grp.inv_one (zpUnits 3 isPrime_three)
    · right; rw [hu2]
      have h := q3tNegOne_sq
      exact (Grp.inv_eq_of_mul_eq_one (zpUnits 3 isPrime_three) h).symm

/-- **q3th-4d（★）: テータ群 q3thGrp = C_M(g_τ)**（中心化群条件 qᵃw²=1 の部分群）。 -/
def q3thGrp : Subgroup q3thM where
  mem := q3thMem
  one_mem := q3th_mem_one
  mul_mem := fun {a b} ha hb => q3th_mem_mul a b ha hb
  inv_mem := fun {a} ha => q3th_mem_inv a ha

/-- **q3th-4e: 中心化性** g∈q3thGrp ⟺ g が g_τ と可換（qᵃw²=1 の幾何的意味）。 -/
theorem q3th_mem_comm (g : q3thCar) :
    q3thMem g ↔ q3thMul g q3thTau = q3thMul q3thTau g := by
  obtain ⟨⟨c, a⟩, w⟩ := g
  -- g·g_τ = (c·q⁻¹·q^a, a-2, w·q), g_τ·g = (q⁻¹·c·w^{-2}, a-2, q·w)
  show (q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) a) (q3tGrp.mul w w) = q3tGrp.one)
     ↔ q3thMul ((c, a), w) q3thTau = q3thMul q3thTau ((c, a), w)
  constructor
  · intro h
    show ((q3tGrp.mul (q3tGrp.mul c (q3tGrp.inv (q3tQ 2))) (tateZpow q3tGrp (q3tQ 2) a),
           a + (-2)), q3tGrp.mul w (q3tQ 2))
       = ((q3tGrp.mul (q3tGrp.mul (q3tGrp.inv (q3tQ 2)) c) (tateZpow q3tGrp w (-2)),
           (-2) + a), q3tGrp.mul (q3tQ 2) w)
    have hA : a + (-2) = (-2) + a := by omega
    have hW : q3tGrp.mul w (q3tQ 2) = q3tGrp.mul (q3tQ 2) w := q3t_comm w (q3tQ 2)
    have hC : q3tGrp.mul (q3tGrp.mul c (q3tGrp.inv (q3tQ 2))) (tateZpow q3tGrp (q3tQ 2) a)
        = q3tGrp.mul (q3tGrp.mul (q3tGrp.inv (q3tQ 2)) c) (tateZpow q3tGrp w (-2)) := by
      -- from qᵃ·w²=1: q^a = (w²)⁻¹ = w^{-2}
      have hqa : tateZpow q3tGrp (q3tQ 2) a = tateZpow q3tGrp w (-2) := by
        have hw2 : q3tGrp.mul w w = tateZpow q3tGrp w 2 := (q3th_q_sq_gen w).symm
        have h2 : q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) a) (tateZpow q3tGrp w 2) = q3tGrp.one := by
          rw [← hw2]; exact h
        have h2' : q3tGrp.mul (tateZpow q3tGrp w 2) (tateZpow q3tGrp (q3tQ 2) a) = q3tGrp.one := by
          rw [q3t_comm (tateZpow q3tGrp w 2) (tateZpow q3tGrp (q3tQ 2) a)]; exact h2
        have h3 : tateZpow q3tGrp (q3tQ 2) a = q3tGrp.inv (tateZpow q3tGrp w 2) :=
          Grp.inv_eq_of_mul_eq_one q3tGrp h2'
        rw [h3]
        exact (tateZpow_neg q3tGrp w 2).symm
      rw [hqa, q3t_comm c (q3tGrp.inv (q3tQ 2))]
    rw [hA, hW, hC]
  · intro h
    -- 逆向き: 可換性の c 成分から qᵃ = w^{-2}、ゆえ qᵃw²=1
    have hc : q3tGrp.mul (q3tGrp.mul c (q3tGrp.inv (q3tQ 2))) (tateZpow q3tGrp (q3tQ 2) a)
        = q3tGrp.mul (q3tGrp.mul (q3tGrp.inv (q3tQ 2)) c) (tateZpow q3tGrp w (-2)) :=
      congrArg (fun z => z.1.1) h
    rw [q3t_comm (q3tGrp.inv (q3tQ 2)) c] at hc
    have hqa : tateZpow q3tGrp (q3tQ 2) a = tateZpow q3tGrp w (-2) :=
      q3tGrp.mul_left_cancel hc
    show q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) a) (q3tGrp.mul w w) = q3tGrp.one
    rw [hqa]
    have hw2 : q3tGrp.mul w w = tateZpow q3tGrp w 2 := (q3th_q_sq_gen w).symm
    rw [hw2, ← tateZpow_add]
    have : (-2 : Int) + 2 = 0 := by omega
    rw [this]
    rfl

/-! ## q3th-3: ★ 実 L²^× 全空間（降下 Quot）と射影・スカラーファイバー -/

/-- g_τ 軌道同値: x ~ y ⟺ ∃ n, ρ(g_τⁿ)(x)=y。 -/
def q3thOrbit (x y : q3thT) : Prop :=
  ∃ n : Int, q3thAct (tateZpow q3thM q3thTau n) x = y

/-- **q3th-3a（★）: 実直線束 L²^× の全空間** = T/⟨g_τ 軌道⟩（自明束の実降下 Quot・
    E₉=ℚ₃^×/q^ℤ と同じイディオム。零切断除去の 𝔾_m-torsor 部分のみ・§4-1）。 -/
def q3thTotal : Type := Quot q3thOrbit

/-- 全空間への標準射。 -/
def q3thTotalMk (x : q3thT) : q3thTotal := Quot.mk q3thOrbit x

/-- ρ(g_τⁿ)(u,t) の底成分 = qⁿ·u。 -/
theorem q3th_tau_act_base (n : Int) (x : q3thT) :
    (q3thAct (tateZpow q3thM q3thTau n) x).1
      = q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) n) x.1 := by
  rw [q3th_tau_pow n]
  rfl

/-- **q3th-3b（★）: 底への射影** [(u,t)] ↦ [u] ∈ E₉（well-def: 底が qⁿ 倍で不変）。 -/
def q3thProjE : q3thTotal → (q3tCurve 2).carrier :=
  Quot.lift (fun x => (q3tProj 2).map x.1)
    (fun x y h => by
      obtain ⟨n, hn⟩ := h
      have hy1 : y.1 = q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) n) x.1 := by
        rw [← hn, q3th_tau_act_base n x]
      show (q3tProj 2).map x.1 = (q3tProj 2).map y.1
      rw [hy1, (q3tProj 2).map_mul]
      have hs : (q3tProj 2).map (tateZpow q3tGrp (q3tQ 2) n) = (q3tCurve 2).one :=
        (quotientProjN_ker q3tGrp (q3tSubgroup 2) (q3t_normal (q3tSubgroup 2))
          (tateZpow q3tGrp (q3tQ 2) n)).mpr ⟨n, rfl⟩
      rw [hs, (q3tCurve 2).one_mul])

/-- スカラー元 s(c) = (c,0,1) ∈ M。 -/
def q3thScalar (c : q3tGrp.carrier) : q3thCar := ((c, (0 : Int)), q3tGrp.one)

/-- スカラーの作用 ρ(s(c))(u,t) = (u, c·t)。 -/
theorem q3th_scalar_act (c : q3tGrp.carrier) (x : q3thT) :
    q3thAct (q3thScalar c) x = (x.1, q3tGrp.mul c x.2) := by
  obtain ⟨u, t⟩ := x
  show (q3tGrp.mul q3tGrp.one u,
        q3tGrp.mul (q3tGrp.mul c (tateZpow q3tGrp u 0)) t) = (u, q3tGrp.mul c t)
  have h1 : q3tGrp.mul q3tGrp.one u = u := q3tGrp.one_mul u
  have h2 : q3tGrp.mul (q3tGrp.mul c (tateZpow q3tGrp u 0)) t = q3tGrp.mul c t := by
    show q3tGrp.mul (q3tGrp.mul c q3tGrp.one) t = q3tGrp.mul c t
    rw [q3tGrp.mul_one]
  rw [h1, h2]

/-- **q3th-3c（★）: スカラーのファイバー単純推移性** — 一意なスカラー c=t'·t⁻¹ が
    ファイバー座標 t を t' に移す（零切断除去の 𝔾_m-torsor の単純推移作用）。 -/
theorem q3th_fiber_scalar (u t t' : q3tGrp.carrier) :
    q3thAct (q3thScalar (q3tGrp.mul t' (q3tGrp.inv t))) (u, t) = (u, t') := by
  rw [q3th_scalar_act]
  show (u, q3tGrp.mul (q3tGrp.mul t' (q3tGrp.inv t)) t) = (u, t')
  rw [q3tGrp.mul_assoc, q3tGrp.inv_mul, q3tGrp.mul_one]

/-! ## q3th-可換冪補助（quotient 作用の well-def 用） -/

/-- 可換元の逆元も可換（一般 Grp 事実の q3thM 版）。 -/
theorem q3thM_comm_inv {g h : q3thCar} (hc : q3thM.mul g h = q3thM.mul h g) :
    q3thM.mul g (q3thM.inv h) = q3thM.mul (q3thM.inv h) g := by
  apply q3thM.mul_left_cancel (a := h)
  have hX : q3thM.mul h (q3thM.mul g (q3thM.inv h)) = g := by
    rw [← q3thM.mul_assoc h g (q3thM.inv h), ← hc,
        q3thM.mul_assoc g h (q3thM.inv h), q3thM.mul_inv, q3thM.mul_one]
  have hY : q3thM.mul h (q3thM.mul (q3thM.inv h) g) = g := by
    rw [← q3thM.mul_assoc h (q3thM.inv h) g, q3thM.mul_inv, q3thM.one_mul]
  rw [hX, hY]

/-- 可換なら自然数冪とも可換。 -/
theorem q3th_comm_npow (g h : q3thCar) (hc : q3thMul g h = q3thMul h g) (k : Nat) :
    q3thMul g (tateNpow q3thM h k) = q3thMul (tateNpow q3thM h k) g := by
  induction k with
  | zero =>
    show q3thMul g q3thOne = q3thMul q3thOne g
    rw [q3thOne_mul g]
    exact q3thM.mul_one g
  | succ j ih =>
    show q3thMul g (q3thMul (tateNpow q3thM h j) h)
        = q3thMul (q3thMul (tateNpow q3thM h j) h) g
    rw [← q3thMul_assoc g (tateNpow q3thM h j) h, ih,
        q3thMul_assoc (tateNpow q3thM h j) g h, hc,
        ← q3thMul_assoc (tateNpow q3thM h j) h g]

/-- 可換なら整数冪とも可換。 -/
theorem q3th_comm_zpow (g h : q3thCar) (hc : q3thMul g h = q3thMul h g) (n : Int) :
    q3thMul g (tateZpow q3thM h n) = q3thMul (tateZpow q3thM h n) g := by
  cases n with
  | ofNat k => exact q3th_comm_npow g h hc k
  | negSucc k =>
    have hci : q3thMul g (q3thInv h) = q3thMul (q3thInv h) g := q3thM_comm_inv hc
    show q3thMul g (tateNpow q3thM (q3thInv h) (k + 1))
        = q3thMul (tateNpow q3thM (q3thInv h) (k + 1)) g
    exact q3th_comm_npow g (q3thInv h) hci (k + 1)

/-! ## q3th-5: ★ 中心化群の Quot 作用・Klein=E₉[2] への全射 -/

/-- **q3th-5a（★）: 中心化群の q3thTotal への作用**（Quot.lift・well-def = 中心化性）。 -/
def q3thQuotAct (g : q3thCar) (hc : q3thMul g q3thTau = q3thMul q3thTau g) :
    q3thTotal → q3thTotal :=
  Quot.lift (fun x => Quot.mk q3thOrbit (q3thAct g x))
    (fun x y hxy => by
      obtain ⟨n, hn⟩ := hxy
      apply Quot.sound
      refine ⟨n, ?_⟩
      rw [← q3th_act_hom, ← hn, ← q3th_act_hom]
      have hcomm : q3thMul (tateZpow q3thM q3thTau n) g
          = q3thMul g (tateZpow q3thM q3thTau n) := (q3th_comm_zpow g q3thTau hc n).symm
      rw [hcomm])

/-- **q3th-5b（★）: π-同変性** pr(g·z) = [w]·pr(z)（中心拡大の射影が同変）。 -/
theorem q3th_over_klein (g : q3thCar) (hc : q3thMul g q3thTau = q3thMul q3thTau g)
    (z : q3thTotal) :
    q3thProjE (q3thQuotAct g hc z)
      = (q3tCurve 2).mul ((q3tProj 2).map g.2) (q3thProjE z) := by
  induction z using Quot.ind
  rename_i x
  show (q3tProj 2).map (q3tGrp.mul g.2 x.1)
     = (q3tCurve 2).mul ((q3tProj 2).map g.2) ((q3tProj 2).map x.1)
  rw [(q3tProj 2).map_mul]

/-- **q3th-5c: テータ群射影は Klein=E₉[2] に入る**（u₀=±1 消費）。 -/
theorem q3th_proj_klein_mem (g : q3thCar) (hg : q3thMem g) :
    q3ttKleinMem ((q3tProj 2).map g.2) := by
  obtain ⟨⟨c, a⟩, j, u0⟩ := g
  have hu : u0 = (zpUnits 3 isPrime_three).one ∨ u0 = q3tNegOne :=
    ((q3th_mem_iff _).mp hg).2
  exact ⟨j, u0, hu, rfl⟩

/-- **q3th-5d（★）: テータ群射影は Klein に全射** — 各 Klein 点は平行移動成分として
    テータ群の元に持ち上がる（q3cu_ker_eq_klein=E₉[2] と on the nose・§3）。
    witness g=((1,−k),(k,u)): a=−j=−k ∧ u₀=u∈{±1}。 -/
theorem q3th_proj_surj_klein (x : (q3tCurve 2).carrier) (hx : q3ttKleinMem x) :
    ∃ g : q3thCar, q3thMem g ∧ (q3tProj 2).map g.2 = x := by
  obtain ⟨k, u, hu, hxe⟩ := hx
  refine ⟨((q3tGrp.one, -k), (k, u)), ?_, ?_⟩
  · exact (q3th_mem_iff _).mpr ⟨rfl, hu⟩
  · exact hxe.symm

/-! ## q3th-6: ★ 中心核（ℚ₃^××q^ℤ・中心的）・スカラー c·q^{t²}（E2 二次指数） -/

/-- **q3th-6a（★）: スカラー中心性** — 純スカラー (c,0,1) は M の中心（全交換子が消える）。
    pr 核の ℚ₃^× 部分の中心性の実現。 -/
theorem q3th_ker_central (c : q3tGrp.carrier) (g' : q3thCar) :
    q3thComm (q3thScalar c) g' = q3thOne := by
  rw [q3th_commutator]
  show ((q3tGrp.mul (tateZpow q3tGrp g'.2 (0 : Int))
          (tateZpow q3tGrp q3tGrp.one (-g'.1.2)), (0 : Int)), q3tGrp.one)
     = ((q3tGrp.one, (0 : Int)), q3tGrp.one)
  have h1 : tateZpow q3tGrp g'.2 (0 : Int) = q3tGrp.one := tateZpow_zero q3tGrp g'.2
  have h2 : tateZpow q3tGrp q3tGrp.one (-g'.1.2) = q3tGrp.one := q3th_zpow_one_id (-g'.1.2)
  rw [h1, h2, q3tGrp.one_mul]

/-- **q3th-6b（★）: 核のスカラー作用 c·q^{t²}** — pr 核 (g_τ の冪)は L²^× のファイバーに
    スカラー q^{−n²} で作用する（**q^{n²} = 柱E E2 のテータ値二次指数の初の幾何的住処**・§2.3）。 -/
theorem q3th_ker_scalar (n : Int) (t : q3tGrp.carrier) :
    (q3thAct (tateZpow q3thM q3thTau n) (q3tGrp.one, t)).2
      = q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (-(n * n))) t := by
  rw [q3th_tau_pow n]
  show q3tGrp.mul (q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (-(n * n)))
        (tateZpow q3tGrp q3tGrp.one (-2 * n))) t
     = q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (-(n * n))) t
  rw [q3th_zpow_one_id (-2 * n), q3tGrp.mul_one]

/-! ## q3th-7: ★★ 交換子＝実 Weil ペアリング ∈ 実 μ₂ ⊂ ℤ₃^× -/

/-- **q3th-7a（★）: 実 Weil ペアリング** e(g,g') = w'ᵃ·w^{−a'}（交換子のスカラー成分）。 -/
def q3thWeil (g g' : q3thCar) : q3tGrp.carrier :=
  q3tGrp.mul (tateZpow q3tGrp g'.2 g.1.2) (tateZpow q3tGrp g.2 (-g'.1.2))

/-- **q3th-7b（★★）: 交換子＝Weil ペアリング** [g,g'] = (e(g,g'),0,1)（§2.4-4）。 -/
theorem q3th_comm_eq_weil (g g' : q3thCar) :
    q3thComm g g' = ((q3thWeil g g', (0 : Int)), q3tGrp.one) :=
  q3th_commutator g g'

/-- **q3th-7c（★）: lift 非依存（スカラー c 非依存）** — ペアリングは (a,w) のみに依存し
    スカラー成分 c に依らない（§2.4-5 の lift 非依存の核）。 -/
theorem q3th_weil_lift_indep (g1 g2 g' : q3thCar)
    (ha : g1.1.2 = g2.1.2) (hw : g1.2 = g2.2) :
    q3thWeil g1 g' = q3thWeil g2 g' := by
  show q3tGrp.mul (tateZpow q3tGrp g'.2 g1.1.2) (tateZpow q3tGrp g1.2 (-g'.1.2))
     = q3tGrp.mul (tateZpow q3tGrp g'.2 g2.1.2) (tateZpow q3tGrp g2.2 (-g'.1.2))
  rw [ha, hw]

/-- **q3th-7d（★）: 交代性** e(g,g)=1（任意の元は自分自身と可換）。 -/
theorem q3th_weil_alt (g : q3thCar) : q3thWeil g g = q3tGrp.one := by
  show q3tGrp.mul (tateZpow q3tGrp g.2 g.1.2) (tateZpow q3tGrp g.2 (-g.1.2)) = q3tGrp.one
  rw [← tateZpow_add]
  have hx : g.1.2 + -g.1.2 = (0 : Int) := by omega
  rw [hx]
  rfl

/-- **非可換 witness g_{[3]} = (1,−1,(1,1))**（∈ テータ群・[3]=[(1,1)] の lift）。 -/
def q3thG3 : q3thCar := ((q3tGrp.one, (-1 : Int)), ((1 : Int), (zpUnits 3 isPrime_three).one))

/-- **非可換 witness g_{[−1]} = (1,0,(0,−1))**（∈ テータ群・[−1]=[(0,−1)] の lift）。 -/
def q3thGm1 : q3thCar := ((q3tGrp.one, (0 : Int)), ((0 : Int), q3tNegOne))

/-- g_{[3]} ∈ テータ群。 -/
theorem q3th_g3_mem : q3thMem q3thG3 := (q3th_mem_iff _).mpr ⟨rfl, Or.inl rfl⟩

/-- g_{[−1]} ∈ テータ群。 -/
theorem q3th_gm1_mem : q3thMem q3thGm1 := (q3th_mem_iff _).mpr ⟨rfl, Or.inr rfl⟩

/-- **q3th-7e（★）: 実 Weil ペアリング値 e([3],[−1]) = −1** ∈ 実 μ₂ ⊂ ℤ₃^×。 -/
theorem q3th_weil_g3_gm1 :
    q3thWeil q3thG3 q3thGm1 = ((0 : Int), q3tNegOne) := by
  show q3tGrp.mul (tateZpow q3tGrp ((0 : Int), q3tNegOne) (-1))
        (tateZpow q3tGrp ((1 : Int), (zpUnits 3 isPrime_three).one) (-0))
     = ((0 : Int), q3tNegOne)
  have hz : tateZpow q3tGrp ((1 : Int), (zpUnits 3 isPrime_three).one) (-0) = q3tGrp.one := by
    show tateZpow q3tGrp ((1 : Int), (zpUnits 3 isPrime_three).one) 0 = q3tGrp.one
    exact tateZpow_zero q3tGrp _
  have hi : tateZpow q3tGrp ((0 : Int), q3tNegOne) (-1) = ((0 : Int), q3tNegOne) := by
    have e : tateZpow q3tGrp ((0 : Int), q3tNegOne) (-1)
        = q3tGrp.inv ((0 : Int), q3tNegOne) := tateZpow_negOne q3tGrp ((0 : Int), q3tNegOne)
    rw [e]
    show (intGrp.inv (0 : Int), (zpUnits 3 isPrime_three).inv q3tNegOne)
       = ((0 : Int), q3tNegOne)
    have h1 : intGrp.inv (0 : Int) = (0 : Int) := by show -(0 : Int) = 0; omega
    have h2 : (zpUnits 3 isPrime_three).inv q3tNegOne = q3tNegOne :=
      (Grp.inv_eq_of_mul_eq_one (zpUnits 3 isPrime_three) q3tNegOne_sq).symm
    rw [h1, h2]
  rw [hi, hz, q3tGrp.mul_one]

/-- **q3th-7f（★★）: 非退化性** e([3],[−1]) = −1 ≠ 1（実 Weil ペアリングが非自明値を取る）。 -/
theorem q3th_weil_nondeg : q3thWeil q3thG3 q3thGm1 ≠ q3tGrp.one := by
  rw [q3th_weil_g3_gm1]
  intro h
  exact q3t_negone_ne_one (congrArg Prod.snd h)

/-- **q3th-7g（★★★）: 実曲線に接続された初の非可換対象** —
    [g_{[3]},g_{[−1]}] = (0,q3tNegOne) ≠ 1（実 −1∈ℤ₃^×・q3t_negone_ne_one）。
    惰性型交換子（幾何的 lift の交換子が実 μ₂ に落ちる）の初の実担体。 -/
theorem q3th_nonabelian : q3thComm q3thG3 q3thGm1 ≠ q3thOne := by
  rw [q3th_comm_eq_weil, q3th_weil_g3_gm1]
  intro h
  have hc : ((0 : Int), q3tNegOne) = q3tGrp.one := congrArg (fun z => z.1.1) h
  exact q3t_negone_ne_one (congrArg Prod.snd hc)

/-! ## q3th-8: capstone -/

/-- **q3th-8a: 実 Mumford テータ群データ** — 中心化群としてのテータ群・交換子＝Weil
    ペアリング・Klein=E₉[2] 全射・交代性・**初の実非可換対象**を束ねる。 -/
structure Q3ThetaGroupData where
  /-- テータ群 = C_M(g_τ)（中心化群）。 -/
  grp : Subgroup q3thM
  /-- 中心化群としての特徴付け。 -/
  isCentralizer : ∀ g, grp.mem g ↔ q3thMul g q3thTau = q3thMul q3thTau g
  /-- 交換子＝実 Weil ペアリング（スカラー成分・指数 0・平行移動 1）。 -/
  commutator : ∀ g g', q3thComm g g' = ((q3thWeil g g', (0 : Int)), q3tGrp.one)
  /-- 射影像 ⊆ Klein=E₉[2]。 -/
  projKlein : ∀ g, grp.mem g → q3ttKleinMem ((q3tProj 2).map g.2)
  /-- 射影は Klein に全射（4 点全て hit）。 -/
  projSurj : ∀ x, q3ttKleinMem x → ∃ g, grp.mem g ∧ (q3tProj 2).map g.2 = x
  /-- Weil ペアリングは交代的。 -/
  weilAlt : ∀ g, q3thWeil g g = q3tGrp.one
  /-- 核のスカラー作用 q^{−n²}（E2 二次指数）。 -/
  kerScalar : ∀ n t, (q3thAct (tateZpow q3thM q3thTau n) (q3tGrp.one, t)).2
    = q3tGrp.mul (tateZpow q3tGrp (q3tQ 2) (-(n * n))) t
  /-- ★ 実曲線に接続された初の非可換対象。 -/
  nonabelian : q3thComm q3thG3 q3thGm1 ≠ q3thOne
  /-- ★ 実 Weil ペアリングの非退化値 e([3],[−1])=−1≠1。 -/
  weilNondeg : q3thWeil q3thG3 q3thGm1 ≠ q3tGrp.one

/-- **q3th-8b: 見出し実例** — 実 E₉(ℚ₃)=ℚ₃^×/9^ℤ 上の実 Mumford テータ群。 -/
def q3thData : Q3ThetaGroupData where
  grp := q3thGrp
  isCentralizer := q3th_mem_comm
  commutator := q3th_comm_eq_weil
  projKlein := q3th_proj_klein_mem
  projSurj := q3th_proj_surj_klein
  weilAlt := q3th_weil_alt
  kerScalar := q3th_ker_scalar
  nonabelian := q3th_nonabelian
  weilNondeg := q3th_weil_nondeg

/-- **q3th-8c: 実 Mumford テータ群の存在**（実 ℚ₃ 上・q=9・レベル 2・μ₂）。 -/
theorem q3thTheta_exists : Nonempty Q3ThetaGroupData := ⟨q3thData⟩

end IUT
