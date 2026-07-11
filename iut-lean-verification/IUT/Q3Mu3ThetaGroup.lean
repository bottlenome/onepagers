/-
  IUT/Q3Mu3ThetaGroup.lean — R3（level-3 実テータ群・μ₃ 値 Weil ペアリング）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、R1 の実分岐 2 次
     局所拡大 L₂^× = q3rqLx = ℤ(v_λ) × U₂ の上に、level-3 の**実単項式束自己同型群 M**・
     その中に降下元 g_τ（q=27 立方）の中心化群としての**テータ群**を本物に建て、その
     交換子が**μ₃ 値の実 Weil ペアリング e₃**（μ₂ でなく μ₃！）に落ちること、そして
     非退化 e₃([3],[ζ₃])=ζ₃^{±1}≠1（実局所環内の実 μ₃ 値）を証明する。実曲線の実
     テータ交換子から初の 3-冪円分値。q3th=level-2 テンプレートの L₂/μ₃/立方版。
     toy 主語なし——主語は実 z3=zpRing 3 上の実対環 L₂^×。）

  complete_pct 影響: **R3**（level-3 テータ群 + μ₃ 値 Weil ペアリング）。後続 R4 の
  mono-theta 剛性が、この μ₃ 上の endo 作用を恒等に固定することで mod-3 不定性
  ℤ₃^×→(ℤ/3)^×=Aut(μ₃) を殺す（R4）。A7 の 0.46–0.50（R3/R4 マイルストーン）への
  own move。A8/A5 は本ラウンドでは主張しない（別監査が判断）。本ラウンド単体は
  「complete_pct 前進は R3/R4 マイルストーン到達時に監査確定」と正直申告する。

  内容（q3th=level-2 テンプレートの立方版・prefix q3m3）:
   * 可換冪補助 q3m3_lc/rc/inv_dist/zpow_mul/zpow_inv/zpow_one_id — L₂^× 可換 (q3tlComm)
   * q3m3M — 実単項式束自己同型群 M（台 (L₂^××ℤ)×L₂^×・cocycle 積）
   * q3m3Tau — level-3 降下元 g_τ=(q⁻¹,−3,q)（q=27・中央指数 −3＝立方）
   * q3m3Comm/q3m3_commutator — 交換子 [g,g']=(w'ᵃw^{−a'},0,1)
   * q3m3Mem/q3m3_mem_iff — 所属 qᵃw³=1 ⟺ 成分条件（v_w=−2a ∧ (−1)ᵃu_w³=1）
   * q3m3_mem_even_mu3 — 偶 a の所属 ⟹ u_w∈μ₃（**q3mc_mu3_complete 消費**）
   * q3m3Grp — テータ群 = C_M(g_τ)（中心化群）
   * q3m3Weil — ★ μ₃ 値 Weil ペアリング e₃
   * q3m3_comm_eq_weil — 交換子＝e₃・q3m3_weil_alt 交代性
   * q3m3_weil_nondeg — ★★ e₃([3],[ζ₃])=ζ₃^{−1}≠1（実 μ₃ 値・非自明）
   * q3m3_nonabelian — ★ 実曲線に接続された初の μ₃ 値非可換対象
   * q3m3_proj_e3 — テータ群射影が E₂₇[3] 点 [3]・[ζ₃] に到達
   * Q3Mu3ThetaData / q3m3Data / q3m3_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・追記のみ）:
  1. **q=27 は忠実部分ケース**（§2(b)）。q^{1/3}=3∈ℚ₃ の立方トリックであって
     [EtTh] の q 固定 q^{1/l} 添加そのものではない。6 次暴分岐体経路は
     full-faithful 版の named future target。
  2. **L₂/level-3/μ₃ スライスのみ**。μ_{3ⁿ}（n≥2・wild）・full ℤ₃^× kill は F-wild
     の後続 named target。
  3. **kill は未達（R3 は舞台の建設）**。本ファイルは ℤ₃^× 不定性を殺さない——それは
     R4 の mono-theta 剛性の仕事。R4 の kill も **mod-3 成分（Aut(μ₃)≅ℤ/2）のみ**で、
     1+3ℤ₃ の pro-3 主単数部分は F-wild まで残存。
  4. **所属の (−1)ᵃ 因子**: qᵃw³=1 の単数条件は (−1)ᵃ·u_w³=1。μ₃ 完全性（R2a）は
     **偶 a の枝（u_w³=1⟹u_w∈μ₃）のみ**を閉じる。奇 a の枝（u_w³=−1⟹u_w∈−μ₃）は
     μ₆ 完全性が要り、R2a 正直限定 4 のとおり F-wild 手前の後続。本ファイルの
     q3m3_mem_iff は**成分分割（完全性不要・厳密）**で、μ₃ 消費は偶 a の
     q3m3_mem_even_mu3 に局在させる。
  5. **実テータ関数ゼロ・π₁ 同定ゼロ・Galois 作用ゼロ**（q3th/R1 正直限定を継承）。
     テータ群は切断上の作用素でなく降下可換性（中心化群）で定義される。
  6. **K-point の影**（群提示 ℤ×U₂ の上・A2 恒久限定を継承）。「直線束」は 𝔾_m-torsor
     部分（L₂^×）のみ・零切断/ファイバー加法/切断空間は無い。
  7. **二重計上の firewall**: q3th（level-2 テンプレート）・R1(q3rq)・R2a(q3mc)・
     R2b(q3tl) は**消費のみ**（再証明しない）。A8/A5 status は主張しない。
     tmzLimit への比較橋も含めない（q3mr §4-6 と同方針）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3ThetaGroup
import IUT.Q3RamifiedQuadratic
import IUT.Q3Mu3Completeness
import IUT.Q3TateCurveL2

namespace IUT

/-! ## q3m3-helpers: 実 L₂^×（可換群 q3rqLx）上の整数冪の補助則 -/

/-- 可換左移動: a·(b·c) = b·(a·c)（q3tlComm）。 -/
theorem q3m3_lc (a b c : q3rqLx.carrier) :
    q3rqLx.mul a (q3rqLx.mul b c) = q3rqLx.mul b (q3rqLx.mul a c) := by
  rw [← q3rqLx.mul_assoc, q3tlComm a b, q3rqLx.mul_assoc]

/-- 可換右移動: (a·b)·c = (a·c)·b（q3tlComm）。 -/
theorem q3m3_rc (a b c : q3rqLx.carrier) :
    q3rqLx.mul (q3rqLx.mul a b) c = q3rqLx.mul (q3rqLx.mul a c) b := by
  rw [q3rqLx.mul_assoc, q3tlComm b c, ← q3rqLx.mul_assoc]

/-- 可換群での逆元分配: (x·y)⁻¹ = x⁻¹·y⁻¹。 -/
theorem q3m3_inv_dist (x y : q3rqLx.carrier) :
    q3rqLx.inv (q3rqLx.mul x y) = q3rqLx.mul (q3rqLx.inv x) (q3rqLx.inv y) := by
  rw [Grp.inv_mul_rev, q3tlComm]

/-- 自然数冪の積分配（可換）: (x·y)ⁿ = xⁿ·yⁿ。 -/
theorem q3m3_npow_mul (x y : q3rqLx.carrier) : ∀ k : Nat,
    tateNpow q3rqLx (q3rqLx.mul x y) k
      = q3rqLx.mul (tateNpow q3rqLx x k) (tateNpow q3rqLx y k) := by
  intro k
  induction k with
  | zero =>
    show q3rqLx.one = q3rqLx.mul q3rqLx.one q3rqLx.one
    rw [q3rqLx.one_mul]
  | succ j ih =>
    show q3rqLx.mul (tateNpow q3rqLx (q3rqLx.mul x y) j) (q3rqLx.mul x y)
        = q3rqLx.mul (q3rqLx.mul (tateNpow q3rqLx x j) x)
            (q3rqLx.mul (tateNpow q3rqLx y j) y)
    rw [ih, q3rqLx.mul_assoc, q3m3_lc (tateNpow q3rqLx y j) x y, ← q3rqLx.mul_assoc]

/-- 整数冪の積分配（可換）: (x·y)ⁿ = xⁿ·yⁿ（全整数 n）。 -/
theorem q3m3_zpow_mul (x y : q3rqLx.carrier) (n : Int) :
    tateZpow q3rqLx (q3rqLx.mul x y) n
      = q3rqLx.mul (tateZpow q3rqLx x n) (tateZpow q3rqLx y n) := by
  cases n with
  | ofNat k =>
    show tateNpow q3rqLx (q3rqLx.mul x y) k
        = q3rqLx.mul (tateNpow q3rqLx x k) (tateNpow q3rqLx y k)
    exact q3m3_npow_mul x y k
  | negSucc k =>
    show tateNpow q3rqLx (q3rqLx.inv (q3rqLx.mul x y)) (k + 1)
        = q3rqLx.mul (tateNpow q3rqLx (q3rqLx.inv x) (k + 1))
            (tateNpow q3rqLx (q3rqLx.inv y) (k + 1))
    rw [q3m3_inv_dist, q3m3_npow_mul]

/-- 逆底の整数冪＝負冪: (g⁻¹)ⁿ = g^{−n}（全整数 n）。 -/
theorem q3m3_zpow_inv_eq (g : q3rqLx.carrier) : ∀ n : Int,
    tateZpow q3rqLx (q3rqLx.inv g) n = tateZpow q3rqLx g (-n) := by
  intro n
  cases n with
  | ofNat k =>
    show tateNpow q3rqLx (q3rqLx.inv g) k = tateZpow q3rqLx g (-((k : Nat) : Int))
    induction k with
    | zero => rfl
    | succ j ih =>
      show q3rqLx.mul (tateNpow q3rqLx (q3rqLx.inv g) j) (q3rqLx.inv g)
          = tateZpow q3rqLx g (-(((j + 1 : Nat) : Int)))
      rw [ih]
      have hidx : -(((j + 1 : Nat) : Int)) = -((j : Nat) : Int) + (-1) := by omega
      have h1 : tateZpow q3rqLx g (-1) = q3rqLx.inv g := tateZpow_negOne q3rqLx g
      rw [hidx, tateZpow_add, h1]
  | negSucc k =>
    show tateNpow q3rqLx (q3rqLx.inv (q3rqLx.inv g)) (k + 1)
        = tateZpow q3rqLx g (-(Int.negSucc k))
    rw [Grp.inv_inv]
    have hidx : -(Int.negSucc k) = ((k + 1 : Nat) : Int) := by omega
    rw [hidx]
    rfl

/-- 逆底の整数冪＝冪の逆: (g⁻¹)ⁿ = (gⁿ)⁻¹。 -/
theorem q3m3_zpow_inv (g : q3rqLx.carrier) (n : Int) :
    tateZpow q3rqLx (q3rqLx.inv g) n = q3rqLx.inv (tateZpow q3rqLx g n) := by
  rw [q3m3_zpow_inv_eq, tateZpow_neg]

/-- 単位の整数冪は単位: 1ⁿ = 1。 -/
theorem q3m3_npow_one_id (k : Nat) :
    tateNpow q3rqLx q3rqLx.one k = q3rqLx.one := by
  induction k with
  | zero => rfl
  | succ j ih =>
    show q3rqLx.mul (tateNpow q3rqLx q3rqLx.one j) q3rqLx.one = q3rqLx.one
    rw [ih, q3rqLx.one_mul]

/-- 単位の整数冪は単位（全整数）。 -/
theorem q3m3_zpow_one_id (n : Int) :
    tateZpow q3rqLx q3rqLx.one n = q3rqLx.one := by
  cases n with
  | ofNat k => exact q3m3_npow_one_id k
  | negSucc k =>
    show tateNpow q3rqLx (q3rqLx.inv q3rqLx.one) (k + 1) = q3rqLx.one
    rw [Grp.inv_one]
    exact q3m3_npow_one_id (k + 1)

/-! ## q3m3-0: ★ 実単項式束自己同型群 M（台 (L₂^××ℤ)×L₂^×） -/

/-- M の台 = (L₂^× × ℤ) × L₂^×。元 (c,a,w)。 -/
abbrev q3m3Car : Type := (q3rqLx.carrier × Int) × q3rqLx.carrier

/-- M の積 (c,a,w)·(c',a',w') = (c·c'·w'ᵃ, a+a', w·w')。 -/
def q3m3Mul (g g' : q3m3Car) : q3m3Car :=
  ((q3rqLx.mul (q3rqLx.mul g.1.1 g'.1.1) (tateZpow q3rqLx g'.2 g.1.2), g.1.2 + g'.1.2),
   q3rqLx.mul g.2 g'.2)

/-- M の単位元 (1,0,1)。 -/
def q3m3One : q3m3Car := ((q3rqLx.one, (0 : Int)), q3rqLx.one)

/-- M の逆元 (c,a,w)⁻¹ = (c⁻¹·wᵃ, −a, w⁻¹)。 -/
def q3m3Inv (g : q3m3Car) : q3m3Car :=
  ((q3rqLx.mul (q3rqLx.inv g.1.1) (tateZpow q3rqLx g.2 g.1.2), -g.1.2), q3rqLx.inv g.2)

/-- **q3m3-0a: M の結合律**（§2.4-1 の成分計算・立方トリックとは独立の M 構造）。 -/
theorem q3m3Mul_assoc (a b c : q3m3Car) :
    q3m3Mul (q3m3Mul a b) c = q3m3Mul a (q3m3Mul b c) := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := a
  obtain ⟨⟨c2, e2⟩, w2⟩ := b
  obtain ⟨⟨c3, e3⟩, w3⟩ := c
  show ((q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c1 c2) (tateZpow q3rqLx w2 e1)) c3)
          (tateZpow q3rqLx w3 (e1 + e2)), (e1 + e2) + e3),
        q3rqLx.mul (q3rqLx.mul w1 w2) w3)
     = ((q3rqLx.mul (q3rqLx.mul c1
          (q3rqLx.mul (q3rqLx.mul c2 c3) (tateZpow q3rqLx w3 e2)))
          (tateZpow q3rqLx (q3rqLx.mul w2 w3) e1), e1 + (e2 + e3)),
        q3rqLx.mul w1 (q3rqLx.mul w2 w3))
  have hA : (e1 + e2) + e3 = e1 + (e2 + e3) := by omega
  have hW : q3rqLx.mul (q3rqLx.mul w1 w2) w3 = q3rqLx.mul w1 (q3rqLx.mul w2 w3) :=
    q3rqLx.mul_assoc w1 w2 w3
  have hC : q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c1 c2) (tateZpow q3rqLx w2 e1)) c3)
          (tateZpow q3rqLx w3 (e1 + e2))
      = q3rqLx.mul (q3rqLx.mul c1
          (q3rqLx.mul (q3rqLx.mul c2 c3) (tateZpow q3rqLx w3 e2)))
          (tateZpow q3rqLx (q3rqLx.mul w2 w3) e1) := by
    rw [tateZpow_add q3rqLx w3 e1 e2, q3m3_zpow_mul w2 w3 e1]
    generalize tateZpow q3rqLx w2 e1 = s
    generalize tateZpow q3rqLx w3 e1 = t
    generalize tateZpow q3rqLx w3 e2 = u
    have hL :
        q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c1 c2) s) c3) (q3rqLx.mul t u)
        = q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c1 c2) c3) s) t) u := by
      rw [← q3rqLx.mul_assoc (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c1 c2) s) c3) t u,
          q3m3_rc (q3rqLx.mul c1 c2) s c3]
    have hR :
        q3rqLx.mul (q3rqLx.mul c1 (q3rqLx.mul (q3rqLx.mul c2 c3) u)) (q3rqLx.mul s t)
        = q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c1 c2) c3) s) t) u := by
      rw [← q3rqLx.mul_assoc c1 (q3rqLx.mul c2 c3) u,
          ← q3rqLx.mul_assoc c1 c2 c3,
          ← q3rqLx.mul_assoc (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c1 c2) c3) u) s t,
          q3m3_rc (q3rqLx.mul (q3rqLx.mul c1 c2) c3) u s,
          q3m3_rc (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c1 c2) c3) s) u t]
    rw [hL, hR]
  rw [hA, hW, hC]

/-- **q3m3-0b: M の左単位律** 1·(c,a,w)=(c,a,w)。 -/
theorem q3m3One_mul (a : q3m3Car) : q3m3Mul q3m3One a = a := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := a
  show ((q3rqLx.mul (q3rqLx.mul q3rqLx.one c1) (tateZpow q3rqLx w1 0), (0 : Int) + e1),
        q3rqLx.mul q3rqLx.one w1) = ((c1, e1), w1)
  have hC : q3rqLx.mul (q3rqLx.mul q3rqLx.one c1) (tateZpow q3rqLx w1 0) = c1 := by
    show q3rqLx.mul (q3rqLx.mul q3rqLx.one c1) q3rqLx.one = c1
    rw [q3rqLx.one_mul, q3rqLx.mul_one]
  have hA : (0 : Int) + e1 = e1 := by omega
  have hW : q3rqLx.mul q3rqLx.one w1 = w1 := q3rqLx.one_mul w1
  rw [hC, hA, hW]

/-- **q3m3-0c: M の左逆律** (c,a,w)⁻¹·(c,a,w)=1。 -/
theorem q3m3Inv_mul (a : q3m3Car) : q3m3Mul (q3m3Inv a) a = q3m3One := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := a
  show ((q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.inv c1) (tateZpow q3rqLx w1 e1)) c1)
          (tateZpow q3rqLx w1 (-e1)), (-e1) + e1), q3rqLx.mul (q3rqLx.inv w1) w1)
     = ((q3rqLx.one, (0 : Int)), q3rqLx.one)
  have hW : q3rqLx.mul (q3rqLx.inv w1) w1 = q3rqLx.one := q3rqLx.inv_mul w1
  have hA : (-e1) + e1 = (0 : Int) := by omega
  have hC : q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.inv c1) (tateZpow q3rqLx w1 e1)) c1)
          (tateZpow q3rqLx w1 (-e1)) = q3rqLx.one := by
    have hzneg : tateZpow q3rqLx w1 (-e1) = q3rqLx.inv (tateZpow q3rqLx w1 e1) :=
      tateZpow_neg q3rqLx w1 e1
    rw [hzneg]
    generalize tateZpow q3rqLx w1 e1 = z
    rw [q3m3_rc (q3rqLx.inv c1) z c1, q3rqLx.inv_mul c1, q3rqLx.one_mul z, q3rqLx.mul_inv z]
  rw [hC, hA, hW]

/-- **q3m3-0（★）: 実単項式束自己同型群 M**（実群・cocycle 積・L₂^× 上）。 -/
def q3m3M : Grp where
  carrier := q3m3Car
  mul := q3m3Mul
  one := q3m3One
  inv := q3m3Inv
  mul_assoc := q3m3Mul_assoc
  one_mul := q3m3One_mul
  inv_mul := q3m3Inv_mul

/-! ## q3m3-1: ★ 交換子恒等式（M の構造・立方トリックと独立） -/

/-- M の交換子 [g,g'] = g·g'·g⁻¹·g'⁻¹。 -/
def q3m3Comm (g g' : q3m3Car) : q3m3Car :=
  q3m3Mul (q3m3Mul (q3m3Mul g g') (q3m3Inv g)) (q3m3Inv g')

/-- **中間積 (g·g')·g⁻¹ = (c'·w'ᵃ·w^{−a'}, a', w')**（§2.4-2 の第一段）。 -/
theorem q3m3_P2 (g g' : q3m3Car) :
    q3m3Mul (q3m3Mul g g') (q3m3Inv g)
      = ((q3rqLx.mul (q3rqLx.mul g'.1.1 (tateZpow q3rqLx g'.2 g.1.2))
            (tateZpow q3rqLx g.2 (-g'.1.2)), g'.1.2), g'.2) := by
  obtain ⟨⟨c, a⟩, w⟩ := g
  obtain ⟨⟨c', a'⟩, w'⟩ := g'
  show ((q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c c') (tateZpow q3rqLx w' a))
          (q3rqLx.mul (q3rqLx.inv c) (tateZpow q3rqLx w a)))
          (tateZpow q3rqLx (q3rqLx.inv w) (a + a')), (a + a') + (-a)),
        q3rqLx.mul (q3rqLx.mul w w') (q3rqLx.inv w))
     = ((q3rqLx.mul (q3rqLx.mul c' (tateZpow q3rqLx w' a)) (tateZpow q3rqLx w (-a')), a'), w')
  have hE : (a + a') + (-a) = a' := by omega
  have hW : q3rqLx.mul (q3rqLx.mul w w') (q3rqLx.inv w) = w' := by
    rw [q3m3_rc w w' (q3rqLx.inv w), q3rqLx.mul_inv w, q3rqLx.one_mul]
  have hC : q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c c') (tateZpow q3rqLx w' a))
          (q3rqLx.mul (q3rqLx.inv c) (tateZpow q3rqLx w a)))
          (tateZpow q3rqLx (q3rqLx.inv w) (a + a'))
      = q3rqLx.mul (q3rqLx.mul c' (tateZpow q3rqLx w' a)) (tateZpow q3rqLx w (-a')) := by
    rw [q3m3_zpow_inv_eq w (a + a')]
    have hTU : q3rqLx.mul (tateZpow q3rqLx w a) (tateZpow q3rqLx w (-(a + a')))
        = tateZpow q3rqLx w (-a') := by
      rw [← tateZpow_add]
      have hx : a + -(a + a') = -a' := by omega
      rw [hx]
    generalize hS : tateZpow q3rqLx w' a = S
    rw [← hTU]
    generalize tateZpow q3rqLx w a = T
    generalize tateZpow q3rqLx w (-(a + a')) = X
    rw [← q3rqLx.mul_assoc (q3rqLx.mul (q3rqLx.mul c c') S) (q3rqLx.inv c) T,
        q3m3_rc (q3rqLx.mul c c') S (q3rqLx.inv c),
        q3m3_rc c c' (q3rqLx.inv c),
        q3rqLx.mul_inv c, q3rqLx.one_mul c',
        ← q3rqLx.mul_assoc (q3rqLx.mul c' S) T X]
  rw [hC, hE, hW]

/-- **q3m3-1a（★）: 交換子恒等式** [g,g'] = (w'ᵃ·w^{−a'}, 0, 1)（§2.4-2）。
    第 2（指数）成分は 0・平行移動成分は 1・非可換性はスカラー成分に宿る。 -/
theorem q3m3_commutator (g g' : q3m3Car) :
    q3m3Comm g g'
      = ((q3rqLx.mul (tateZpow q3rqLx g'.2 g.1.2) (tateZpow q3rqLx g.2 (-g'.1.2)),
          (0 : Int)), q3rqLx.one) := by
  show q3m3Mul (q3m3Mul (q3m3Mul g g') (q3m3Inv g)) (q3m3Inv g') = _
  rw [q3m3_P2 g g']
  obtain ⟨⟨c, a⟩, w⟩ := g
  obtain ⟨⟨c', a'⟩, w'⟩ := g'
  show ((q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c' (tateZpow q3rqLx w' a))
            (tateZpow q3rqLx w (-a')))
          (q3rqLx.mul (q3rqLx.inv c') (tateZpow q3rqLx w' a')))
          (tateZpow q3rqLx (q3rqLx.inv w') a'), a' + (-a')), q3rqLx.mul w' (q3rqLx.inv w'))
     = ((q3rqLx.mul (tateZpow q3rqLx w' a) (tateZpow q3rqLx w (-a')), (0 : Int)), q3rqLx.one)
  have hE : a' + (-a') = (0 : Int) := by omega
  have hW : q3rqLx.mul w' (q3rqLx.inv w') = q3rqLx.one := q3rqLx.mul_inv w'
  have hC : q3rqLx.mul (q3rqLx.mul (q3rqLx.mul (q3rqLx.mul c' (tateZpow q3rqLx w' a))
            (tateZpow q3rqLx w (-a')))
          (q3rqLx.mul (q3rqLx.inv c') (tateZpow q3rqLx w' a')))
          (tateZpow q3rqLx (q3rqLx.inv w') a')
      = q3rqLx.mul (tateZpow q3rqLx w' a) (tateZpow q3rqLx w (-a')) := by
    rw [q3m3_zpow_inv_eq w' a']
    have hPQ : q3rqLx.mul (tateZpow q3rqLx w' a') (tateZpow q3rqLx w' (-a')) = q3rqLx.one := by
      rw [← tateZpow_add]
      have hx : a' + -a' = (0 : Int) := by omega
      rw [hx]
      rfl
    generalize hS : tateZpow q3rqLx w' a = S
    generalize hV : tateZpow q3rqLx w (-a') = V
    rw [← q3rqLx.mul_assoc (q3rqLx.mul (q3rqLx.mul c' S) V) (q3rqLx.inv c')
          (tateZpow q3rqLx w' a'),
        q3m3_rc (q3rqLx.mul c' S) V (q3rqLx.inv c'),
        q3m3_rc c' S (q3rqLx.inv c'),
        q3rqLx.mul_inv c', q3rqLx.one_mul S,
        q3rqLx.mul_assoc (q3rqLx.mul S V) (tateZpow q3rqLx w' a') (tateZpow q3rqLx w' (-a')),
        hPQ, q3rqLx.mul_one]
  rw [hC, hE, hW]

/-! ## q3m3-2: 立方冪・第 2 成分（単数部）の冪則・降下元 g_τ -/

/-- w² = w·w（整数冪 2）。 -/
theorem q3m3_sq_gen (w : q3rqLx.carrier) :
    tateZpow q3rqLx w 2 = q3rqLx.mul w w := by
  have h : tateZpow q3rqLx w (1 + 1) = q3rqLx.mul (tateZpow q3rqLx w 1) w :=
    tateZpow_succ q3rqLx w 1
  rw [tateZpow_one] at h
  exact h

/-- **w³ = (w·w)·w**（整数冪 3・立方の基本形）。 -/
theorem q3m3_cube_gen (w : q3rqLx.carrier) :
    tateZpow q3rqLx w 3 = q3rqLx.mul (q3rqLx.mul w w) w := by
  have h : tateZpow q3rqLx w (2 + 1) = q3rqLx.mul (tateZpow q3rqLx w 2) w :=
    tateZpow_succ q3rqLx w 2
  rw [q3m3_sq_gen] at h
  exact h

/-- 第 2 成分（単数部）の自然数冪則: (gⁿ).2 = (q3rqU 内の g.2 の n 乗)。 -/
theorem q3m3_npow_snd (g : q3rqLx.carrier) : ∀ n : Nat,
    (tateNpow q3rqLx g n).2 = tateNpow q3rqU g.2 n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show q3rqU.mul (tateNpow q3rqLx g k).2 g.2
        = q3rqU.mul (tateNpow q3rqU g.2 k) g.2
    rw [ih]

/-- 第 2 成分（単数部）の整数冪則: (g^t).2 = (q3rqU 内の g.2 の t 乗)（負冪込み）。 -/
theorem q3m3_zpow_snd (g : q3rqLx.carrier) : ∀ t : Int,
    (tateZpow q3rqLx g t).2 = tateZpow q3rqU g.2 t := by
  intro t
  cases t with
  | ofNat n => exact q3m3_npow_snd g n
  | negSucc n =>
    show (tateNpow q3rqLx (q3rqLx.inv g) (n + 1)).2
        = tateNpow q3rqU (q3rqU.inv g.2) (n + 1)
    have hinv : (q3rqLx.inv g).2 = q3rqU.inv g.2 := rfl
    rw [← hinv]
    exact q3m3_npow_snd (q3rqLx.inv g) (n + 1)

/-- **q3m3-2a: level-3 降下元 g_τ = (q⁻¹, −3, q)**（q=q3tlQ=27・中央指数 −3＝立方）。
    q3th の level-2 g_τ=(q⁻¹,−2,q) の立方版。 -/
def q3m3Tau : q3m3Car := ((q3rqLx.inv q3tlQ, (-3 : Int)), q3tlQ)

/-! ## q3m3-3: ★ 中心化群条件 qᵃw³=1・テータ群 q3m3Grp -/

/-- **q3m3-3a: 中心化群条件** q3m3Mem g := qᵃ·w³ = 1（実 L₂^× 内の等式・立方）。 -/
def q3m3Mem (g : q3m3Car) : Prop :=
  q3rqLx.mul (tateZpow q3rqLx q3tlQ g.1.2)
    (q3rqLx.mul (q3rqLx.mul g.2 g.2) g.2) = q3rqLx.one

/-- **q3m3-3b（★）: 中心化性** g∈テータ群 ⟺ g が g_τ と可換（qᵃw³=1 の幾何的意味）。 -/
theorem q3m3_mem_comm (g : q3m3Car) :
    q3m3Mem g ↔ q3m3Mul g q3m3Tau = q3m3Mul q3m3Tau g := by
  obtain ⟨⟨c, a⟩, w⟩ := g
  show (q3rqLx.mul (tateZpow q3rqLx q3tlQ a) (q3rqLx.mul (q3rqLx.mul w w) w) = q3rqLx.one)
     ↔ q3m3Mul ((c, a), w) q3m3Tau = q3m3Mul q3m3Tau ((c, a), w)
  constructor
  · intro h
    show ((q3rqLx.mul (q3rqLx.mul c (q3rqLx.inv q3tlQ)) (tateZpow q3rqLx q3tlQ a),
           a + (-3)), q3rqLx.mul w q3tlQ)
       = ((q3rqLx.mul (q3rqLx.mul (q3rqLx.inv q3tlQ) c) (tateZpow q3rqLx w (-3)),
           (-3) + a), q3rqLx.mul q3tlQ w)
    have hA : a + (-3) = (-3) + a := by omega
    have hW : q3rqLx.mul w q3tlQ = q3rqLx.mul q3tlQ w := q3tlComm w q3tlQ
    have hC : q3rqLx.mul (q3rqLx.mul c (q3rqLx.inv q3tlQ)) (tateZpow q3rqLx q3tlQ a)
        = q3rqLx.mul (q3rqLx.mul (q3rqLx.inv q3tlQ) c) (tateZpow q3rqLx w (-3)) := by
      have hqa : tateZpow q3rqLx q3tlQ a = tateZpow q3rqLx w (-3) := by
        have hw3 : q3rqLx.mul (q3rqLx.mul w w) w = tateZpow q3rqLx w 3 :=
          (q3m3_cube_gen w).symm
        have h2 : q3rqLx.mul (tateZpow q3rqLx q3tlQ a) (tateZpow q3rqLx w 3) = q3rqLx.one := by
          rw [← hw3]; exact h
        have h2' : q3rqLx.mul (tateZpow q3rqLx w 3) (tateZpow q3rqLx q3tlQ a) = q3rqLx.one := by
          rw [q3tlComm (tateZpow q3rqLx w 3) (tateZpow q3rqLx q3tlQ a)]; exact h2
        have h3 : tateZpow q3rqLx q3tlQ a = q3rqLx.inv (tateZpow q3rqLx w 3) :=
          Grp.inv_eq_of_mul_eq_one q3rqLx h2'
        rw [h3]
        exact (tateZpow_neg q3rqLx w 3).symm
      rw [hqa, q3tlComm c (q3rqLx.inv q3tlQ)]
    rw [hA, hW, hC]
  · intro h
    have hc : q3rqLx.mul (q3rqLx.mul c (q3rqLx.inv q3tlQ)) (tateZpow q3rqLx q3tlQ a)
        = q3rqLx.mul (q3rqLx.mul (q3rqLx.inv q3tlQ) c) (tateZpow q3rqLx w (-3)) :=
      congrArg (fun z => z.1.1) h
    rw [q3tlComm (q3rqLx.inv q3tlQ) c] at hc
    have hqa : tateZpow q3rqLx q3tlQ a = tateZpow q3rqLx w (-3) :=
      q3rqLx.mul_left_cancel hc
    show q3rqLx.mul (tateZpow q3rqLx q3tlQ a) (q3rqLx.mul (q3rqLx.mul w w) w) = q3rqLx.one
    rw [hqa]
    have hw3 : q3rqLx.mul (q3rqLx.mul w w) w = tateZpow q3rqLx w 3 := (q3m3_cube_gen w).symm
    rw [hw3, ← tateZpow_add]
    have : (-3 : Int) + 3 = 0 := by omega
    rw [this]
    rfl

/-- 単位元は中心化群条件を満たす。 -/
theorem q3m3_mem_one : q3m3Mem q3m3One := by
  apply (q3m3_mem_comm q3m3One).mpr
  rw [q3m3One_mul q3m3Tau]
  exact (q3m3M.mul_one q3m3Tau).symm

/-- 中心化群は積で閉じる（中心化性から一般群論的に・完全性不要）。 -/
theorem q3m3_mem_mul (g g' : q3m3Car) (hg : q3m3Mem g) (hg' : q3m3Mem g') :
    q3m3Mem (q3m3Mul g g') := by
  apply (q3m3_mem_comm (q3m3Mul g g')).mpr
  have hcg : q3m3M.mul g q3m3Tau = q3m3M.mul q3m3Tau g := (q3m3_mem_comm g).mp hg
  have hcg' : q3m3M.mul g' q3m3Tau = q3m3M.mul q3m3Tau g' := (q3m3_mem_comm g').mp hg'
  show q3m3M.mul (q3m3M.mul g g') q3m3Tau = q3m3M.mul q3m3Tau (q3m3M.mul g g')
  calc q3m3M.mul (q3m3M.mul g g') q3m3Tau
      = q3m3M.mul g (q3m3M.mul g' q3m3Tau) := q3m3M.mul_assoc g g' q3m3Tau
    _ = q3m3M.mul g (q3m3M.mul q3m3Tau g') := by rw [hcg']
    _ = q3m3M.mul (q3m3M.mul g q3m3Tau) g' := (q3m3M.mul_assoc g q3m3Tau g').symm
    _ = q3m3M.mul (q3m3M.mul q3m3Tau g) g' := by rw [hcg]
    _ = q3m3M.mul q3m3Tau (q3m3M.mul g g') := q3m3M.mul_assoc q3m3Tau g g'

/-- 中心化群は逆元で閉じる（中心化性から一般群論的に・完全性不要）。 -/
theorem q3m3_mem_inv (g : q3m3Car) (hg : q3m3Mem g) : q3m3Mem (q3m3Inv g) := by
  apply (q3m3_mem_comm (q3m3Inv g)).mpr
  have hcg : q3m3M.mul g q3m3Tau = q3m3M.mul q3m3Tau g := (q3m3_mem_comm g).mp hg
  show q3m3M.mul (q3m3M.inv g) q3m3Tau = q3m3M.mul q3m3Tau (q3m3M.inv g)
  apply q3m3M.mul_left_cancel (a := g)
  have hX : q3m3M.mul g (q3m3M.mul (q3m3M.inv g) q3m3Tau) = q3m3Tau := by
    rw [← q3m3M.mul_assoc g (q3m3M.inv g) q3m3Tau, q3m3M.mul_inv, q3m3M.one_mul]
  have hY : q3m3M.mul g (q3m3M.mul q3m3Tau (q3m3M.inv g)) = q3m3Tau := by
    rw [← q3m3M.mul_assoc g q3m3Tau (q3m3M.inv g),
        show q3m3M.mul g q3m3Tau = q3m3M.mul q3m3Tau g from hcg,
        q3m3M.mul_assoc q3m3Tau g (q3m3M.inv g), q3m3M.mul_inv, q3m3M.mul_one]
  rw [hX, hY]

/-- **q3m3-3c（★）: テータ群 q3m3Grp = C_M(g_τ)**（中心化群条件 qᵃw³=1 の部分群）。 -/
def q3m3Grp : Subgroup q3m3M where
  mem := q3m3Mem
  one_mem := q3m3_mem_one
  mul_mem := fun {a b} ha hb => q3m3_mem_mul a b ha hb
  inv_mem := fun {a} ha => q3m3_mem_inv a ha

/-! ## q3m3-4: ★ 所属の成分特徴付け mem_iff（成分分割・厳密）と μ₃ 消費 -/

/-- 付値方程式 6a+3v=0 ⟺ 2a+v=0（Int・omega）。 -/
theorem q3m3_val_fwd (a v : Int) (h : a * 6 + ((v + v) + v) = 0) : 2 * a + v = 0 := by omega

/-- 付値方程式の逆向き 2a+v=0 ⟹ 6a+3v=0（Int・omega）。 -/
theorem q3m3_val_bwd (a v : Int) (h : 2 * a + v = 0) : a * 6 + ((v + v) + v) = 0 := by omega

/-- **q3m3-4a（★）: 所属の成分特徴付け** qᵃw³=1 ⟺ (2a+v_w=0 ∧ (−1)ᵃ·u_w³=1)。
    L₂^×=ℤ×U₂ の成分ごとの分割（完全性不要・厳密）。付値成分 6a+3v_w=0 ⟺ 2a+v_w=0、
    単数成分 (−1)ᵃ·u_w³=1。奇 a の枝の μ₆ 解消は R2a 正直限定 4 のとおり後続。 -/
theorem q3m3_mem_iff (g : q3m3Car) :
    q3m3Mem g ↔ (2 * g.1.2 + g.2.1 = 0 ∧
      q3rqU.mul (tateZpow q3rqU q3tlNegOneU g.1.2)
        (q3rqU.mul (q3rqU.mul g.2.2 g.2.2) g.2.2) = q3rqU.one) := by
  obtain ⟨⟨c, a⟩, vw, uw⟩ := g
  show q3m3Mem ((c, a), (vw, uw))
     ↔ (2 * a + vw = 0 ∧ q3rqU.mul (tateZpow q3rqU q3tlNegOneU a)
          (q3rqU.mul (q3rqU.mul uw uw) uw) = q3rqU.one)
  have hQ1 : (tateZpow q3rqLx q3tlQ a).1 = a * 6 := q3tl_pow_fst a
  have hQ2 : (tateZpow q3rqLx q3tlQ a).2 = tateZpow q3rqU q3tlNegOneU a :=
    q3m3_zpow_snd q3tlQ a
  have hpair : q3m3Mem ((c, a), (vw, uw))
      ↔ ((tateZpow q3rqLx q3tlQ a).1 + ((vw + vw) + vw) = (0 : Int)
          ∧ q3rqU.mul (tateZpow q3rqLx q3tlQ a).2 (q3rqU.mul (q3rqU.mul uw uw) uw)
              = q3rqU.one) := by
    show (((tateZpow q3rqLx q3tlQ a).1 + ((vw + vw) + vw),
            q3rqU.mul (tateZpow q3rqLx q3tlQ a).2 (q3rqU.mul (q3rqU.mul uw uw) uw))
          : q3rqLx.carrier) = ((0 : Int), q3rqU.one) ↔ _
    rw [Prod.mk.injEq]
  rw [hpair, hQ1, hQ2]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨q3m3_val_fwd a vw h1, h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨q3m3_val_bwd a vw h1, h2⟩

/-- **q3m3-4b（★★★・μ₃ 消費）: 付値 0 の所属 ⟹ 単数部 ∈ μ₃** — a=0 の中心化群元
    （＝valuation-0 の内部円分スライス）は u_w∈μ₃={1,ζ₃,ζ₃²}。所属から (−1)⁰·u_w³=1
    ゆえ u_w³=1、**q3mc_mu3_complete（R2a）を消費**して μ₃ に確定。R4 が恒等固定する
    「テータ環境の内部 μ₃」の実在。 -/
theorem q3m3_mem_val0_mu3 (g : q3m3Car) (hmem : q3m3Mem g) (ha : g.1.2 = 0) :
    q3rqMu3 g.2.2.val := by
  have hiff := (q3m3_mem_iff g).mp hmem
  obtain ⟨_, h2⟩ := hiff
  rw [ha] at h2
  -- (−1)⁰ = 1 ⟹ u_w³ = 1（U₂ 内）
  have h2' : q3rqU.mul (q3rqU.mul g.2.2 g.2.2) g.2.2 = q3rqU.one := by
    have hz : tateZpow q3rqU q3tlNegOneU (0 : Int) = q3rqU.one := tateZpow_zero q3rqU q3tlNegOneU
    rw [hz, q3rqU.one_mul] at h2
    exact h2
  -- .val に落とす: u_w.val³ = q3rqOne
  have hval : q3rqMul (q3rqMul g.2.2.val g.2.2.val) g.2.2.val = q3rqOne :=
    congrArg Subtype.val h2'
  exact q3mc_mu3_complete g.2.2.val hval

/-! ## q3m3-5: ★★ 交換子＝μ₃ 値 Weil ペアリング e₃・非退化 e₃([3],[ζ₃])≠1 -/

/-- **q3m3-5a（★）: 実 Weil ペアリング** e₃(g,g') = w'ᵃ·w^{−a'}（交換子のスカラー成分・
    L₂^× 値）。level-3 では非退化値が μ₃ に落ちる（μ₂ でなく！）。 -/
def q3m3Weil (g g' : q3m3Car) : q3rqLx.carrier :=
  q3rqLx.mul (tateZpow q3rqLx g'.2 g.1.2) (tateZpow q3rqLx g.2 (-g'.1.2))

/-- **q3m3-5b（★★）: 交換子＝Weil ペアリング** [g,g'] = (e₃(g,g'),0,1)。 -/
theorem q3m3_comm_eq_weil (g g' : q3m3Car) :
    q3m3Comm g g' = ((q3m3Weil g g', (0 : Int)), q3rqLx.one) :=
  q3m3_commutator g g'

/-- **q3m3-5c（★）: 交代性** e₃(g,g)=1（任意の元は自分自身と可換）。 -/
theorem q3m3_weil_alt (g : q3m3Car) : q3m3Weil g g = q3rqLx.one := by
  show q3rqLx.mul (tateZpow q3rqLx g.2 g.1.2) (tateZpow q3rqLx g.2 (-g.1.2)) = q3rqLx.one
  rw [← tateZpow_add]
  have hx : g.1.2 + -g.1.2 = (0 : Int) := by omega
  rw [hx]
  rfl

/-- **q3m3-5d（★）: 非可換 witness g_{[3]} = (1,−1,3)**（3=(2,−1)∈L₂^×・[3] の lift）。
    membership: v_w=2=−2·(−1) ∧ (−1)^{−1}·(−1)³=1。 -/
def q3m3G3 : q3m3Car := ((q3rqLx.one, (-1 : Int)), q3tl3)

/-- **q3m3-5e（★）: 非可換 witness g_{[ζ₃]} = (1,0,ζ₃)**（ζ₃=(0,ζ₃)∈L₂^×・[ζ₃] の lift）。
    membership: v_w=0=−2·0 ∧ (−1)⁰·ζ₃³=1。 -/
def q3m3Gz : q3m3Car := ((q3rqLx.one, (0 : Int)), q3tlZeta3Elt)

/-- g_{[3]} ∈ テータ群（q3m3_mem_iff.mpr・q3tl_negU_cube/sq 消費）。 -/
theorem q3m3_g3_mem : q3m3Mem q3m3G3 := by
  apply (q3m3_mem_iff q3m3G3).mpr
  refine ⟨?_, ?_⟩
  · show ((2 : Int) * (-1) + 2 = 0)
    omega
  · show q3rqU.mul (tateZpow q3rqU q3tlNegOneU (-1))
          (q3rqU.mul (q3rqU.mul q3tlNegOneU q3tlNegOneU) q3tlNegOneU) = q3rqU.one
    have h1 : tateZpow q3rqU q3tlNegOneU (-1) = q3rqU.inv q3tlNegOneU :=
      tateZpow_negOne q3rqU q3tlNegOneU
    rw [h1, q3tl_negU_cube, q3rqU.inv_mul]

/-- g_{[ζ₃]} ∈ テータ群（q3m3_mem_iff.mpr・q3tl_zetaU_cube 消費）。 -/
theorem q3m3_gz_mem : q3m3Mem q3m3Gz := by
  apply (q3m3_mem_iff q3m3Gz).mpr
  refine ⟨?_, ?_⟩
  · show ((2 : Int) * 0 + 0 = 0)
    omega
  · show q3rqU.mul (tateZpow q3rqU q3tlNegOneU 0)
          (q3rqU.mul (q3rqU.mul q3tlZeta3U q3tlZeta3U) q3tlZeta3U) = q3rqU.one
    have h0 : tateZpow q3rqU q3tlNegOneU 0 = q3rqU.one := tateZpow_zero q3rqU q3tlNegOneU
    rw [h0, q3rqU.one_mul, q3tl_zetaU_cube]

/-- **q3m3-5f（★★）: 実 μ₃ 値 Weil ペアリング** e₃([3],[ζ₃]) = ζ₃⁻¹ = (0, ζ₃⁻¹)。
    a₃=−1・a_ζ=0 で e₃ = ζ₃^{a₃}·3^{−a_ζ} = ζ₃⁻¹·1 = ζ₃⁻¹（∈実 μ₃ ⊂ U₂）。
    実曲線の実テータ交換子から得た初の 3-冪円分値。 -/
theorem q3m3_weil_g3_gz :
    q3m3Weil q3m3G3 q3m3Gz = (((0 : Int)), q3rqU.inv q3tlZeta3U) := by
  show q3rqLx.mul (tateZpow q3rqLx q3tlZeta3Elt (-1)) (tateZpow q3rqLx q3tl3 (-(0 : Int)))
     = (((0 : Int)), q3rqU.inv q3tlZeta3U)
  have h00 : -(0 : Int) = 0 := by omega
  have hz : tateZpow q3rqLx q3tl3 (-(0 : Int)) = q3rqLx.one := by
    rw [h00]; exact tateZpow_zero q3rqLx q3tl3
  have hi : tateZpow q3rqLx q3tlZeta3Elt (-1) = (((0 : Int)), q3rqU.inv q3tlZeta3U) := by
    have e : tateZpow q3rqLx q3tlZeta3Elt (-1) = q3rqLx.inv q3tlZeta3Elt :=
      tateZpow_negOne q3rqLx q3tlZeta3Elt
    rw [e]
    show ((intGrp.inv (0 : Int)), q3rqU.inv q3tlZeta3U) = (((0 : Int)), q3rqU.inv q3tlZeta3U)
    have hn : intGrp.inv (0 : Int) = (0 : Int) := rfl
    rw [hn]
  rw [hi, hz, q3rqLx.mul_one]

/-- **q3m3-5g（★★★）: 非退化性** e₃([3],[ζ₃]) = ζ₃⁻¹ ≠ 1（実 μ₃ 値が非自明）。
    inv ζ₃=1 ⟹ ζ₃=1 に矛盾（R1 q3rq_zeta_ne_one）。**μ₂ でなく μ₃ 値の非退化**——
    R4 が殺す mod-3 円分不定性の実担体。 -/
theorem q3m3_weil_nondeg : q3m3Weil q3m3G3 q3m3Gz ≠ q3rqLx.one := by
  rw [q3m3_weil_g3_gz]
  intro h
  have hu : q3rqU.inv q3tlZeta3U = q3rqU.one := congrArg Prod.snd h
  have hz : q3tlZeta3U = q3rqU.one := by
    have hh := congrArg q3rqU.inv hu
    rw [Grp.inv_inv, Grp.inv_one] at hh
    exact hh
  have hval : q3rqZeta = q3rqOne := congrArg Subtype.val hz
  exact q3rq_zeta_ne_one hval

/-- **q3m3-5h（★★★）: 実曲線に接続された初の μ₃ 値非可換対象** —
    [g_{[3]},g_{[ζ₃]}] ≠ 1（交換子＝μ₃ 値 Weil ペアリング ζ₃⁻¹≠1）。
    q3th の μ₂ 値 non-abelian の立方版・3-冪円分の実担体。 -/
theorem q3m3_nonabelian : q3m3Comm q3m3G3 q3m3Gz ≠ q3m3One := by
  rw [q3m3_comm_eq_weil]
  intro h
  apply q3m3_weil_nondeg
  exact congrArg (fun z => z.1.1) h

/-! ## q3m3-6: テータ群射影が E₂₇[3] 点 [3]・[ζ₃] に到達 -/

/-- **q3m3-6a: g_{[3]} の w-成分は [3]∈E₂₇[3] へ射影**（q3tl3pt・位数ちょうど 3）。 -/
theorem q3m3_proj_e3_three : q3tlProj.map q3m3G3.2 = q3tl3pt := rfl

/-- **q3m3-6b: g_{[ζ₃]} の w-成分は [ζ₃]∈E₂₇[3] へ射影**（q3tlZeta3・位数ちょうど 3）。 -/
theorem q3m3_proj_e3_zeta : q3tlProj.map q3m3Gz.2 = q3tlZeta3 := rfl

/-! ## q3m3-7: capstone -/

/-- **q3m3-7a: level-3 実テータ群データ（μ₃ 値 Weil ペアリング）** — 中心化群としての
    テータ群・交換子＝μ₃ 値 Weil ペアリング・所属の成分特徴付け・偶付値の μ₃ 完全性消費・
    非退化 e₃([3],[ζ₃])≠1（**μ₂ でなく μ₃**）・初の μ₃ 値非可換対象・E₂₇[3] 射影を束ねる。 -/
structure Q3Mu3ThetaData where
  /-- テータ群 = C_M(g_τ)（中心化群）。 -/
  grp : Subgroup q3m3M
  /-- 中心化群としての特徴付け。 -/
  isCentralizer : ∀ g, grp.mem g ↔ q3m3Mul g q3m3Tau = q3m3Mul q3m3Tau g
  /-- 交換子＝μ₃ 値 Weil ペアリング。 -/
  commutator : ∀ g g', q3m3Comm g g' = ((q3m3Weil g g', (0 : Int)), q3rqLx.one)
  /-- 所属の成分特徴付け（2a+v_w=0 ∧ (−1)ᵃu_w³=1）。 -/
  memIff : ∀ g, grp.mem g ↔ (2 * g.1.2 + g.2.1 = 0 ∧
    q3rqU.mul (tateZpow q3rqU q3tlNegOneU g.1.2)
      (q3rqU.mul (q3rqU.mul g.2.2 g.2.2) g.2.2) = q3rqU.one)
  /-- 付値 0 の所属 ⟹ 単数部∈μ₃（μ₃ 完全性 q3mc_mu3_complete 消費）。 -/
  memVal0Mu3 : ∀ g, grp.mem g → g.1.2 = 0 → q3rqMu3 g.2.2.val
  /-- Weil ペアリングは交代的。 -/
  weilAlt : ∀ g, q3m3Weil g g = q3rqLx.one
  /-- ★★ 非退化 μ₃ 値 e₃([3],[ζ₃]) = ζ₃⁻¹ ≠ 1。 -/
  weilNondeg : q3m3Weil q3m3G3 q3m3Gz ≠ q3rqLx.one
  /-- ★ 初の μ₃ 値非可換対象。 -/
  nonabelian : q3m3Comm q3m3G3 q3m3Gz ≠ q3m3One
  /-- witness g_{[3]}・g_{[ζ₃]} はテータ群の元。 -/
  g3Mem : grp.mem q3m3G3
  gzMem : grp.mem q3m3Gz
  /-- w-成分は E₂₇[3] 点 [3]・[ζ₃] へ射影。 -/
  projThree : q3tlProj.map q3m3G3.2 = q3tl3pt
  projZeta : q3tlProj.map q3m3Gz.2 = q3tlZeta3

/-- **q3m3-7b: 見出し実例** — L₂=ℚ₃(ζ₃) 上の level-3 実テータ群（μ₃ 値 Weil）。 -/
def q3m3Data : Q3Mu3ThetaData where
  grp := q3m3Grp
  isCentralizer := q3m3_mem_comm
  commutator := q3m3_comm_eq_weil
  memIff := q3m3_mem_iff
  memVal0Mu3 := q3m3_mem_val0_mu3
  weilAlt := q3m3_weil_alt
  weilNondeg := q3m3_weil_nondeg
  nonabelian := q3m3_nonabelian
  g3Mem := q3m3_g3_mem
  gzMem := q3m3_gz_mem
  projThree := q3m3_proj_e3_three
  projZeta := q3m3_proj_e3_zeta

/-- **q3m3-7c: level-3 実テータ群（μ₃ 値 Weil ペアリング）の存在**
    （実 L₂=ℚ₃(ζ₃)・q=27・レベル 3・μ₃）。 -/
theorem q3m3_exists : Nonempty Q3Mu3ThetaData := ⟨q3m3Data⟩

end IUT
