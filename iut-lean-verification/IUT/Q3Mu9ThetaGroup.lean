/-
  IUT/Q3Mu9ThetaGroup.lean — level-9 実テータ群（μ₉ 値 Weil ペアリング・q9c μ₉ 完全性の消費者）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**（骨格・模型・代理でなく、q9tl で建てた
     実 level-9 Tate 曲線 E_{3⁹} = M^×/q^ℤ（M^× = q9tlMx = ℤ(v_π)×U₃・q=3⁹・実 u₆）の上に、
     level-9 の**実単項式束自己同型群 M₉**・その中の降下元 g_τ=(q⁻¹,−9,q)（q=3⁹・中央指数
     −9＝9 乗）の中心化群としての**テータ群**を本物に建て、その交換子が**μ₉ 値の実 Weil
     ペアリング e₉** に落ちること、そして非退化 e₉(g₃,g_ζ)=ζ₉⁻¹≠1（実 M^× 内の**原始 9 乗根**
     ＝実テータ交換子から得た初の wild 円分値）を証明する。q3m3=level-3 テンプレートの
     U₃/μ₉/9 乗版。付値 0 の所属点 `q9mt_mem_val0_mu9` で **Module B の μ₉ 完全性
     `q9c_mu9_complete`（carrier レベル・単数仮定なし・9 重積形）を消費**する——これが
     level-9 kill キャンペーンが q9c を実際に消費する唯一の接続点。toy 主語なし
     ——主語は実 q3k 上の実対環 M^× = q9tlMx。）

  complete_pct 影響: **0 前進（foundation・q3m3 の忠実部分ケースの 2 乗）**。本モジュール単体は
  何も kill せず（テータ機構と μ₉ 値 Weil の建設のみ）。level-9 kill 本体は後続の剛性 q9mr
  ＋橋 q9mb が本モジュールのテータ機構を消費して達成する。「complete_pct 0 前進（骨格でなく
  本物基盤の先行建設・q9c 消費機構の設置）」と正直申告する。

  内容（audit/level9-theta-kill-detail-2026-07-11.md §2.4・q3m3 の level-9 写経・prefix q9mt）:
   * 可換冪補助 q9mt_lc/rc/inv_dist/zpow_mul/zpow_inv — M^× 可換 (q9tlComm)
   * q9mt_cube_gen/q9mt_ninth_gen — w³/w⁹ の tateZpow⇄9 重積変換（汎用 Grp）
   * q9mtM — 実単項式束自己同型群 M₉（台 (M^××ℤ)×M^×・cocycle 積）
   * q9mtTau — level-9 降下元 g_τ=(q⁻¹,−9,q)（q=3⁹・中央指数 −9＝9 乗）
   * q9mtComm/q9mt_commutator — 交換子 [g,g']=(w'ᵃw^{−a'},0,1)
   * q9mtMem/q9mt_mem_iff — 所属 qᵃw⁹=1 ⟺ 成分条件（6a+v_w=0 ∧ (u₆⁹)ᵃu_w⁹=1）
   * q9mt_mem_val0_mu9 — ★★★ 付値 0 の所属 ⟹ u_w∈μ₉（**q9c_mu9_complete 消費**）
   * q9mtGrp — テータ群 = C_{M₉}(g_τ)（中心化群）
   * q9mtWeil — ★ μ₉ 値 Weil ペアリング e₉
   * q9mt_comm_eq_weil — 交換子＝e₉・q9mt_weil_alt 交代性
   * q9mt_weil_nondeg — ★★ e₉(g₃,g_ζ)=ζ₉⁻¹≠1（実 M^× 内の原始 9 乗根・非自明）
   * q9mt_nonabelian — ★ 実曲線に接続された初の μ₉ 値非可換対象
   * q9mt_proj_e9_three/zeta — テータ群射影が E_{3⁹}[9] 点 [3]・[ζ₉] に到達
   * Q3Mu9ThetaGroupData / q9mt_data / q9mt_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・追記のみ）:
  1. **a≠0 枝の解の分類は閉じない・閉じる必要もない**（witness の所属は定義的に閉じ、kill は
     a=0 の内部 cyclotome しか使わない）。q3m3 正直限定 4（奇 a 枝の μ₆）と同格の正直限定。
  2. **q=3⁹ は忠実部分ケースの 2 乗**（q^{1/9}=3∈ℚ₃ の 9 乗トリック・[EtTh] の q 固定
     q^{1/l} 添加そのものではない）。full-faithful 版は named future target。
  3. **U₃/level-9/μ₉ スライスのみ**。full ℤ₃^× kill は後続 q9mr/q9mb・pro-3 bulk 残存。
  4. **kill は未達（本ファイルは舞台の建設）**。ℤ₃^× 不定性を殺すのは剛性 q9mr＋橋 q9mb。
  5. **実テータ関数ゼロ・π₁ 同定ゼロ・Galois 作用ゼロ**（q3m3/q9tl/q9c/q3k の正直限定を継承）。
     テータ群は切断上の作用素でなく降下可換性（中心化群）で定義される。
  6. **K-point の影**（群提示 ℤ×U₃ の上・A2 恒久限定を継承）。
  7. **二重計上の firewall**: q3m3（level-3 テンプレート）・q9tl・q9c・q9ps・q3k は**消費のみ**
     （再証明しない）。tmzLimit への比較橋も含めない（後続 q9mb の管轄）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3TateCurveL9
import IUT.Q3Mu9Completeness
import IUT.Q3KummerPiSplit
import IUT.Q3KummerYPow

namespace IUT

/-! ## q9mt-helpers: 実 M^×（可換群 q9tlMx）上の整数冪の補助則 -/

/-- 可換左移動: a·(b·c) = b·(a·c)（q9tlComm）。 -/
theorem q9mt_lc (a b c : q9tlMx.carrier) :
    q9tlMx.mul a (q9tlMx.mul b c) = q9tlMx.mul b (q9tlMx.mul a c) := by
  rw [← q9tlMx.mul_assoc, q9tlComm a b, q9tlMx.mul_assoc]

/-- 可換右移動: (a·b)·c = (a·c)·b（q9tlComm）。 -/
theorem q9mt_rc (a b c : q9tlMx.carrier) :
    q9tlMx.mul (q9tlMx.mul a b) c = q9tlMx.mul (q9tlMx.mul a c) b := by
  rw [q9tlMx.mul_assoc, q9tlComm b c, ← q9tlMx.mul_assoc]

/-- 可換群での逆元分配: (x·y)⁻¹ = x⁻¹·y⁻¹。 -/
theorem q9mt_inv_dist (x y : q9tlMx.carrier) :
    q9tlMx.inv (q9tlMx.mul x y) = q9tlMx.mul (q9tlMx.inv x) (q9tlMx.inv y) := by
  rw [Grp.inv_mul_rev, q9tlComm]

/-- 自然数冪の積分配（可換）: (x·y)ⁿ = xⁿ·yⁿ。 -/
theorem q9mt_npow_mul (x y : q9tlMx.carrier) : ∀ k : Nat,
    tateNpow q9tlMx (q9tlMx.mul x y) k
      = q9tlMx.mul (tateNpow q9tlMx x k) (tateNpow q9tlMx y k) := by
  intro k
  induction k with
  | zero =>
    show q9tlMx.one = q9tlMx.mul q9tlMx.one q9tlMx.one
    rw [q9tlMx.one_mul]
  | succ j ih =>
    show q9tlMx.mul (tateNpow q9tlMx (q9tlMx.mul x y) j) (q9tlMx.mul x y)
        = q9tlMx.mul (q9tlMx.mul (tateNpow q9tlMx x j) x)
            (q9tlMx.mul (tateNpow q9tlMx y j) y)
    rw [ih, q9tlMx.mul_assoc, q9mt_lc (tateNpow q9tlMx y j) x y, ← q9tlMx.mul_assoc]

/-- 整数冪の積分配（可換）: (x·y)ⁿ = xⁿ·yⁿ（全整数 n）。 -/
theorem q9mt_zpow_mul (x y : q9tlMx.carrier) (n : Int) :
    tateZpow q9tlMx (q9tlMx.mul x y) n
      = q9tlMx.mul (tateZpow q9tlMx x n) (tateZpow q9tlMx y n) := by
  cases n with
  | ofNat k =>
    show tateNpow q9tlMx (q9tlMx.mul x y) k
        = q9tlMx.mul (tateNpow q9tlMx x k) (tateNpow q9tlMx y k)
    exact q9mt_npow_mul x y k
  | negSucc k =>
    show tateNpow q9tlMx (q9tlMx.inv (q9tlMx.mul x y)) (k + 1)
        = q9tlMx.mul (tateNpow q9tlMx (q9tlMx.inv x) (k + 1))
            (tateNpow q9tlMx (q9tlMx.inv y) (k + 1))
    rw [q9mt_inv_dist, q9mt_npow_mul]

/-- 逆底の整数冪＝負冪: (g⁻¹)ⁿ = g^{−n}（全整数 n）。 -/
theorem q9mt_zpow_inv_eq (g : q9tlMx.carrier) : ∀ n : Int,
    tateZpow q9tlMx (q9tlMx.inv g) n = tateZpow q9tlMx g (-n) := by
  intro n
  cases n with
  | ofNat k =>
    show tateNpow q9tlMx (q9tlMx.inv g) k = tateZpow q9tlMx g (-((k : Nat) : Int))
    induction k with
    | zero => rfl
    | succ j ih =>
      show q9tlMx.mul (tateNpow q9tlMx (q9tlMx.inv g) j) (q9tlMx.inv g)
          = tateZpow q9tlMx g (-(((j + 1 : Nat) : Int)))
      rw [ih]
      have hidx : -(((j + 1 : Nat) : Int)) = -((j : Nat) : Int) + (-1) := by omega
      have h1 : tateZpow q9tlMx g (-1) = q9tlMx.inv g := tateZpow_negOne q9tlMx g
      rw [hidx, tateZpow_add, h1]
  | negSucc k =>
    show tateNpow q9tlMx (q9tlMx.inv (q9tlMx.inv g)) (k + 1)
        = tateZpow q9tlMx g (-(Int.negSucc k))
    rw [Grp.inv_inv]
    have hidx : -(Int.negSucc k) = ((k + 1 : Nat) : Int) := by omega
    rw [hidx]
    rfl

/-- 逆底の整数冪＝冪の逆: (g⁻¹)ⁿ = (gⁿ)⁻¹。 -/
theorem q9mt_zpow_inv (g : q9tlMx.carrier) (n : Int) :
    tateZpow q9tlMx (q9tlMx.inv g) n = q9tlMx.inv (tateZpow q9tlMx g n) := by
  rw [q9mt_zpow_inv_eq, tateZpow_neg]

/-! ## q9mt-cube/ninth: w³ = (w·w)·w・w⁹ = (w³·w³)·w³（汎用 Grp・q9c 消費形へ） -/

/-- w² = w·w（整数冪 2・汎用 Grp）。 -/
theorem q9mt_sq_gen (G : Grp) (w : G.carrier) :
    tateZpow G w 2 = G.mul w w := by
  have h : tateZpow G w (1 + 1) = G.mul (tateZpow G w 1) w := tateZpow_succ G w 1
  rw [tateZpow_one] at h
  exact h

/-- **w³ = (w·w)·w**（整数冪 3・汎用 Grp・立方の基本形）。 -/
theorem q9mt_cube_gen (G : Grp) (w : G.carrier) :
    tateZpow G w 3 = G.mul (G.mul w w) w := by
  have h : tateZpow G w (2 + 1) = G.mul (tateZpow G w 2) w := tateZpow_succ G w 2
  rw [q9mt_sq_gen] at h
  exact h

/-- **w⁹ = (w³·w³)·w³**（整数冪 9・汎用 Grp・q9c_mu9_complete の 9 重積形に一致）。
    塔分解 9 = 6+3・6 = 3+3 で tateZpow_add を 2 回、各立方を q9mt_cube_gen で開く。 -/
theorem q9mt_ninth_gen (G : Grp) (w : G.carrier) :
    tateZpow G w 9
      = G.mul (G.mul (G.mul (G.mul w w) w) (G.mul (G.mul w w) w)) (G.mul (G.mul w w) w) := by
  have hc : tateZpow G w 3 = G.mul (G.mul w w) w := q9mt_cube_gen G w
  have h6 : tateZpow G w 6 = G.mul (tateZpow G w 3) (tateZpow G w 3) := by
    have he : (6 : Int) = 3 + 3 := by omega
    rw [he]; exact tateZpow_add G w 3 3
  have h9 : tateZpow G w 9 = G.mul (tateZpow G w 6) (tateZpow G w 3) := by
    have he : (9 : Int) = 6 + 3 := by omega
    rw [he]; exact tateZpow_add G w 6 3
  rw [h9, h6, hc]

/-! ## q9mt-0: ★ 実単項式束自己同型群 M₉（台 (M^××ℤ)×M^×） -/

/-- M₉ の台 = (M^× × ℤ) × M^×。元 (c,a,w)。 -/
abbrev q9mtCar : Type := (q9tlMx.carrier × Int) × q9tlMx.carrier

/-- M₉ の積 (c,a,w)·(c',a',w') = (c·c'·w'ᵃ, a+a', w·w')。 -/
def q9mtMul (g g' : q9mtCar) : q9mtCar :=
  ((q9tlMx.mul (q9tlMx.mul g.1.1 g'.1.1) (tateZpow q9tlMx g'.2 g.1.2), g.1.2 + g'.1.2),
   q9tlMx.mul g.2 g'.2)

/-- M₉ の単位元 (1,0,1)。 -/
def q9mtOne : q9mtCar := ((q9tlMx.one, (0 : Int)), q9tlMx.one)

/-- M₉ の逆元 (c,a,w)⁻¹ = (c⁻¹·wᵃ, −a, w⁻¹)。 -/
def q9mtInv (g : q9mtCar) : q9mtCar :=
  ((q9tlMx.mul (q9tlMx.inv g.1.1) (tateZpow q9tlMx g.2 g.1.2), -g.1.2), q9tlMx.inv g.2)

/-- **q9mt-0a: M₉ の結合律**（§2.4-1 の成分計算・9 乗トリックとは独立の M 構造）。 -/
theorem q9mtMul_assoc (a b c : q9mtCar) :
    q9mtMul (q9mtMul a b) c = q9mtMul a (q9mtMul b c) := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := a
  obtain ⟨⟨c2, e2⟩, w2⟩ := b
  obtain ⟨⟨c3, e3⟩, w3⟩ := c
  show ((q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c1 c2) (tateZpow q9tlMx w2 e1)) c3)
          (tateZpow q9tlMx w3 (e1 + e2)), (e1 + e2) + e3),
        q9tlMx.mul (q9tlMx.mul w1 w2) w3)
     = ((q9tlMx.mul (q9tlMx.mul c1
          (q9tlMx.mul (q9tlMx.mul c2 c3) (tateZpow q9tlMx w3 e2)))
          (tateZpow q9tlMx (q9tlMx.mul w2 w3) e1), e1 + (e2 + e3)),
        q9tlMx.mul w1 (q9tlMx.mul w2 w3))
  have hA : (e1 + e2) + e3 = e1 + (e2 + e3) := by omega
  have hW : q9tlMx.mul (q9tlMx.mul w1 w2) w3 = q9tlMx.mul w1 (q9tlMx.mul w2 w3) :=
    q9tlMx.mul_assoc w1 w2 w3
  have hC : q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c1 c2) (tateZpow q9tlMx w2 e1)) c3)
          (tateZpow q9tlMx w3 (e1 + e2))
      = q9tlMx.mul (q9tlMx.mul c1
          (q9tlMx.mul (q9tlMx.mul c2 c3) (tateZpow q9tlMx w3 e2)))
          (tateZpow q9tlMx (q9tlMx.mul w2 w3) e1) := by
    rw [tateZpow_add q9tlMx w3 e1 e2, q9mt_zpow_mul w2 w3 e1]
    generalize tateZpow q9tlMx w2 e1 = s
    generalize tateZpow q9tlMx w3 e1 = t
    generalize tateZpow q9tlMx w3 e2 = u
    have hL :
        q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c1 c2) s) c3) (q9tlMx.mul t u)
        = q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c1 c2) c3) s) t) u := by
      rw [← q9tlMx.mul_assoc (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c1 c2) s) c3) t u,
          q9mt_rc (q9tlMx.mul c1 c2) s c3]
    have hR :
        q9tlMx.mul (q9tlMx.mul c1 (q9tlMx.mul (q9tlMx.mul c2 c3) u)) (q9tlMx.mul s t)
        = q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c1 c2) c3) s) t) u := by
      rw [← q9tlMx.mul_assoc c1 (q9tlMx.mul c2 c3) u,
          ← q9tlMx.mul_assoc c1 c2 c3,
          ← q9tlMx.mul_assoc (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c1 c2) c3) u) s t,
          q9mt_rc (q9tlMx.mul (q9tlMx.mul c1 c2) c3) u s,
          q9mt_rc (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c1 c2) c3) s) u t]
    rw [hL, hR]
  rw [hA, hW, hC]

/-- **q9mt-0b: M₉ の左単位律** 1·(c,a,w)=(c,a,w)。 -/
theorem q9mtOne_mul (a : q9mtCar) : q9mtMul q9mtOne a = a := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := a
  show ((q9tlMx.mul (q9tlMx.mul q9tlMx.one c1) (tateZpow q9tlMx w1 0), (0 : Int) + e1),
        q9tlMx.mul q9tlMx.one w1) = ((c1, e1), w1)
  have hC : q9tlMx.mul (q9tlMx.mul q9tlMx.one c1) (tateZpow q9tlMx w1 0) = c1 := by
    show q9tlMx.mul (q9tlMx.mul q9tlMx.one c1) q9tlMx.one = c1
    rw [q9tlMx.one_mul, q9tlMx.mul_one]
  have hA : (0 : Int) + e1 = e1 := by omega
  have hW : q9tlMx.mul q9tlMx.one w1 = w1 := q9tlMx.one_mul w1
  rw [hC, hA, hW]

/-- **q9mt-0c: M₉ の左逆律** (c,a,w)⁻¹·(c,a,w)=1。 -/
theorem q9mtInv_mul (a : q9mtCar) : q9mtMul (q9mtInv a) a = q9mtOne := by
  obtain ⟨⟨c1, e1⟩, w1⟩ := a
  show ((q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.inv c1) (tateZpow q9tlMx w1 e1)) c1)
          (tateZpow q9tlMx w1 (-e1)), (-e1) + e1), q9tlMx.mul (q9tlMx.inv w1) w1)
     = ((q9tlMx.one, (0 : Int)), q9tlMx.one)
  have hW : q9tlMx.mul (q9tlMx.inv w1) w1 = q9tlMx.one := q9tlMx.inv_mul w1
  have hA : (-e1) + e1 = (0 : Int) := by omega
  have hC : q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.inv c1) (tateZpow q9tlMx w1 e1)) c1)
          (tateZpow q9tlMx w1 (-e1)) = q9tlMx.one := by
    have hzneg : tateZpow q9tlMx w1 (-e1) = q9tlMx.inv (tateZpow q9tlMx w1 e1) :=
      tateZpow_neg q9tlMx w1 e1
    rw [hzneg]
    generalize tateZpow q9tlMx w1 e1 = z
    rw [q9mt_rc (q9tlMx.inv c1) z c1, q9tlMx.inv_mul c1, q9tlMx.one_mul z, q9tlMx.mul_inv z]
  rw [hC, hA, hW]

/-- **q9mt-0（★）: 実単項式束自己同型群 M₉**（実群・cocycle 積・M^× 上）。 -/
def q9mtM : Grp where
  carrier := q9mtCar
  mul := q9mtMul
  one := q9mtOne
  inv := q9mtInv
  mul_assoc := q9mtMul_assoc
  one_mul := q9mtOne_mul
  inv_mul := q9mtInv_mul

/-! ## q9mt-1: ★ 交換子恒等式（M₉ の構造・9 乗トリックと独立） -/

/-- M₉ の交換子 [g,g'] = g·g'·g⁻¹·g'⁻¹。 -/
def q9mtComm (g g' : q9mtCar) : q9mtCar :=
  q9mtMul (q9mtMul (q9mtMul g g') (q9mtInv g)) (q9mtInv g')

/-- **中間積 (g·g')·g⁻¹ = (c'·w'ᵃ·w^{−a'}, a', w')**（§2.4-2 の第一段）。 -/
theorem q9mt_P2 (g g' : q9mtCar) :
    q9mtMul (q9mtMul g g') (q9mtInv g)
      = ((q9tlMx.mul (q9tlMx.mul g'.1.1 (tateZpow q9tlMx g'.2 g.1.2))
            (tateZpow q9tlMx g.2 (-g'.1.2)), g'.1.2), g'.2) := by
  obtain ⟨⟨c, a⟩, w⟩ := g
  obtain ⟨⟨c', a'⟩, w'⟩ := g'
  show ((q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c c') (tateZpow q9tlMx w' a))
          (q9tlMx.mul (q9tlMx.inv c) (tateZpow q9tlMx w a)))
          (tateZpow q9tlMx (q9tlMx.inv w) (a + a')), (a + a') + (-a)),
        q9tlMx.mul (q9tlMx.mul w w') (q9tlMx.inv w))
     = ((q9tlMx.mul (q9tlMx.mul c' (tateZpow q9tlMx w' a)) (tateZpow q9tlMx w (-a')), a'), w')
  have hE : (a + a') + (-a) = a' := by omega
  have hW : q9tlMx.mul (q9tlMx.mul w w') (q9tlMx.inv w) = w' := by
    rw [q9mt_rc w w' (q9tlMx.inv w), q9tlMx.mul_inv w, q9tlMx.one_mul]
  have hC : q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c c') (tateZpow q9tlMx w' a))
          (q9tlMx.mul (q9tlMx.inv c) (tateZpow q9tlMx w a)))
          (tateZpow q9tlMx (q9tlMx.inv w) (a + a'))
      = q9tlMx.mul (q9tlMx.mul c' (tateZpow q9tlMx w' a)) (tateZpow q9tlMx w (-a')) := by
    rw [q9mt_zpow_inv_eq w (a + a')]
    have hTU : q9tlMx.mul (tateZpow q9tlMx w a) (tateZpow q9tlMx w (-(a + a')))
        = tateZpow q9tlMx w (-a') := by
      rw [← tateZpow_add]
      have hx : a + -(a + a') = -a' := by omega
      rw [hx]
    generalize hS : tateZpow q9tlMx w' a = S
    rw [← hTU]
    generalize tateZpow q9tlMx w a = T
    generalize tateZpow q9tlMx w (-(a + a')) = X
    rw [← q9tlMx.mul_assoc (q9tlMx.mul (q9tlMx.mul c c') S) (q9tlMx.inv c) T,
        q9mt_rc (q9tlMx.mul c c') S (q9tlMx.inv c),
        q9mt_rc c c' (q9tlMx.inv c),
        q9tlMx.mul_inv c, q9tlMx.one_mul c',
        ← q9tlMx.mul_assoc (q9tlMx.mul c' S) T X]
  rw [hC, hE, hW]

/-- **q9mt-1a（★）: 交換子恒等式** [g,g'] = (w'ᵃ·w^{−a'}, 0, 1)（§2.4-2）。
    第 2（指数）成分は 0・平行移動成分は 1・非可換性はスカラー成分に宿る。 -/
theorem q9mt_commutator (g g' : q9mtCar) :
    q9mtComm g g'
      = ((q9tlMx.mul (tateZpow q9tlMx g'.2 g.1.2) (tateZpow q9tlMx g.2 (-g'.1.2)),
          (0 : Int)), q9tlMx.one) := by
  show q9mtMul (q9mtMul (q9mtMul g g') (q9mtInv g)) (q9mtInv g') = _
  rw [q9mt_P2 g g']
  obtain ⟨⟨c, a⟩, w⟩ := g
  obtain ⟨⟨c', a'⟩, w'⟩ := g'
  show ((q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c' (tateZpow q9tlMx w' a))
            (tateZpow q9tlMx w (-a')))
          (q9tlMx.mul (q9tlMx.inv c') (tateZpow q9tlMx w' a')))
          (tateZpow q9tlMx (q9tlMx.inv w') a'), a' + (-a')), q9tlMx.mul w' (q9tlMx.inv w'))
     = ((q9tlMx.mul (tateZpow q9tlMx w' a) (tateZpow q9tlMx w (-a')), (0 : Int)), q9tlMx.one)
  have hE : a' + (-a') = (0 : Int) := by omega
  have hW : q9tlMx.mul w' (q9tlMx.inv w') = q9tlMx.one := q9tlMx.mul_inv w'
  have hC : q9tlMx.mul (q9tlMx.mul (q9tlMx.mul (q9tlMx.mul c' (tateZpow q9tlMx w' a))
            (tateZpow q9tlMx w (-a')))
          (q9tlMx.mul (q9tlMx.inv c') (tateZpow q9tlMx w' a')))
          (tateZpow q9tlMx (q9tlMx.inv w') a')
      = q9tlMx.mul (tateZpow q9tlMx w' a) (tateZpow q9tlMx w (-a')) := by
    rw [q9mt_zpow_inv_eq w' a']
    have hPQ : q9tlMx.mul (tateZpow q9tlMx w' a') (tateZpow q9tlMx w' (-a')) = q9tlMx.one := by
      rw [← tateZpow_add]
      have hx : a' + -a' = (0 : Int) := by omega
      rw [hx]
      rfl
    generalize hS : tateZpow q9tlMx w' a = S
    generalize hV : tateZpow q9tlMx w (-a') = V
    rw [← q9tlMx.mul_assoc (q9tlMx.mul (q9tlMx.mul c' S) V) (q9tlMx.inv c')
          (tateZpow q9tlMx w' a'),
        q9mt_rc (q9tlMx.mul c' S) V (q9tlMx.inv c'),
        q9mt_rc c' S (q9tlMx.inv c'),
        q9tlMx.mul_inv c', q9tlMx.one_mul S,
        q9tlMx.mul_assoc (q9tlMx.mul S V) (tateZpow q9tlMx w' a') (tateZpow q9tlMx w' (-a')),
        hPQ, q9tlMx.mul_one]
  rw [hC, hE, hW]

/-! ## q9mt-2: 単数部（第 2 成分）の冪則・降下元 g_τ -/

/-- 第 2 成分（単数部）の整数冪則: (g^t).2 = (U₃ 内の g.2 の t 乗)（負冪込み）。
    q9tl_npow_snd（自然数版）を負冪へ拡張。 -/
theorem q9mt_zpow_snd (g : q9tlMx.carrier) : ∀ t : Int,
    (tateZpow q9tlMx g t).2 = tateZpow q3kU g.2 t := by
  intro t
  cases t with
  | ofNat n => exact q9tl_npow_snd g n
  | negSucc n =>
    show (tateNpow q9tlMx (q9tlMx.inv g) (n + 1)).2
        = tateNpow q3kU (q3kU.inv g.2) (n + 1)
    have hinv : (q9tlMx.inv g).2 = q3kU.inv g.2 := rfl
    rw [← hinv]
    exact q9tl_npow_snd (q9tlMx.inv g) (n + 1)

/-- **q9mt-2a: level-9 降下元 g_τ = (q⁻¹, −9, q)**（q=q9tlQ=3⁹・中央指数 −9＝9 乗）。
    q3m3 の level-3 g_τ=(q⁻¹,−3,q) の 9 乗版。 -/
def q9mtTau : q9mtCar := ((q9tlMx.inv q9tlQ, (-9 : Int)), q9tlQ)

/-! ## q9mt-3: ★ 中心化群条件 qᵃw⁹=1・テータ群 q9mtGrp -/

/-- **q9mt-3a: 中心化群条件** q9mtMem g := qᵃ·w⁹ = 1（実 M^× 内の等式・9 乗）。 -/
def q9mtMem (g : q9mtCar) : Prop :=
  q9tlMx.mul (tateZpow q9tlMx q9tlQ g.1.2) (tateZpow q9tlMx g.2 9) = q9tlMx.one

/-- **q9mt-3b（★）: 中心化性** g∈テータ群 ⟺ g が g_τ と可換（qᵃw⁹=1 の幾何的意味）。 -/
theorem q9mt_mem_comm (g : q9mtCar) :
    q9mtMem g ↔ q9mtMul g q9mtTau = q9mtMul q9mtTau g := by
  obtain ⟨⟨c, a⟩, w⟩ := g
  show (q9tlMx.mul (tateZpow q9tlMx q9tlQ a) (tateZpow q9tlMx w 9) = q9tlMx.one)
     ↔ q9mtMul ((c, a), w) q9mtTau = q9mtMul q9mtTau ((c, a), w)
  constructor
  · intro h
    show ((q9tlMx.mul (q9tlMx.mul c (q9tlMx.inv q9tlQ)) (tateZpow q9tlMx q9tlQ a),
           a + (-9)), q9tlMx.mul w q9tlQ)
       = ((q9tlMx.mul (q9tlMx.mul (q9tlMx.inv q9tlQ) c) (tateZpow q9tlMx w (-9)),
           (-9) + a), q9tlMx.mul q9tlQ w)
    have hA : a + (-9) = (-9) + a := by omega
    have hW : q9tlMx.mul w q9tlQ = q9tlMx.mul q9tlQ w := q9tlComm w q9tlQ
    have hC : q9tlMx.mul (q9tlMx.mul c (q9tlMx.inv q9tlQ)) (tateZpow q9tlMx q9tlQ a)
        = q9tlMx.mul (q9tlMx.mul (q9tlMx.inv q9tlQ) c) (tateZpow q9tlMx w (-9)) := by
      have hqa : tateZpow q9tlMx q9tlQ a = tateZpow q9tlMx w (-9) := by
        have h2' : q9tlMx.mul (tateZpow q9tlMx w 9) (tateZpow q9tlMx q9tlQ a) = q9tlMx.one := by
          rw [q9tlComm (tateZpow q9tlMx w 9) (tateZpow q9tlMx q9tlQ a)]; exact h
        have h3 : tateZpow q9tlMx q9tlQ a = q9tlMx.inv (tateZpow q9tlMx w 9) :=
          Grp.inv_eq_of_mul_eq_one q9tlMx h2'
        rw [h3]
        exact (tateZpow_neg q9tlMx w 9).symm
      rw [hqa, q9tlComm c (q9tlMx.inv q9tlQ)]
    rw [hA, hW, hC]
  · intro h
    have hc : q9tlMx.mul (q9tlMx.mul c (q9tlMx.inv q9tlQ)) (tateZpow q9tlMx q9tlQ a)
        = q9tlMx.mul (q9tlMx.mul (q9tlMx.inv q9tlQ) c) (tateZpow q9tlMx w (-9)) :=
      congrArg (fun z => z.1.1) h
    rw [q9tlComm (q9tlMx.inv q9tlQ) c] at hc
    have hqa : tateZpow q9tlMx q9tlQ a = tateZpow q9tlMx w (-9) :=
      q9tlMx.mul_left_cancel hc
    show q9tlMx.mul (tateZpow q9tlMx q9tlQ a) (tateZpow q9tlMx w 9) = q9tlMx.one
    rw [hqa, ← tateZpow_add]
    have : (-9 : Int) + 9 = 0 := by omega
    rw [this]
    rfl

/-- 単位元は中心化群条件を満たす。 -/
theorem q9mt_mem_one : q9mtMem q9mtOne := by
  apply (q9mt_mem_comm q9mtOne).mpr
  rw [q9mtOne_mul q9mtTau]
  exact (q9mtM.mul_one q9mtTau).symm

/-- 中心化群は積で閉じる（中心化性から一般群論的に・完全性不要）。 -/
theorem q9mt_mem_mul (g g' : q9mtCar) (hg : q9mtMem g) (hg' : q9mtMem g') :
    q9mtMem (q9mtMul g g') := by
  apply (q9mt_mem_comm (q9mtMul g g')).mpr
  have hcg : q9mtM.mul g q9mtTau = q9mtM.mul q9mtTau g := (q9mt_mem_comm g).mp hg
  have hcg' : q9mtM.mul g' q9mtTau = q9mtM.mul q9mtTau g' := (q9mt_mem_comm g').mp hg'
  show q9mtM.mul (q9mtM.mul g g') q9mtTau = q9mtM.mul q9mtTau (q9mtM.mul g g')
  calc q9mtM.mul (q9mtM.mul g g') q9mtTau
      = q9mtM.mul g (q9mtM.mul g' q9mtTau) := q9mtM.mul_assoc g g' q9mtTau
    _ = q9mtM.mul g (q9mtM.mul q9mtTau g') := by rw [hcg']
    _ = q9mtM.mul (q9mtM.mul g q9mtTau) g' := (q9mtM.mul_assoc g q9mtTau g').symm
    _ = q9mtM.mul (q9mtM.mul q9mtTau g) g' := by rw [hcg]
    _ = q9mtM.mul q9mtTau (q9mtM.mul g g') := q9mtM.mul_assoc q9mtTau g g'

/-- 中心化群は逆元で閉じる（中心化性から一般群論的に・完全性不要）。 -/
theorem q9mt_mem_inv (g : q9mtCar) (hg : q9mtMem g) : q9mtMem (q9mtInv g) := by
  apply (q9mt_mem_comm (q9mtInv g)).mpr
  have hcg : q9mtM.mul g q9mtTau = q9mtM.mul q9mtTau g := (q9mt_mem_comm g).mp hg
  show q9mtM.mul (q9mtM.inv g) q9mtTau = q9mtM.mul q9mtTau (q9mtM.inv g)
  apply q9mtM.mul_left_cancel (a := g)
  have hX : q9mtM.mul g (q9mtM.mul (q9mtM.inv g) q9mtTau) = q9mtTau := by
    rw [← q9mtM.mul_assoc g (q9mtM.inv g) q9mtTau, q9mtM.mul_inv, q9mtM.one_mul]
  have hY : q9mtM.mul g (q9mtM.mul q9mtTau (q9mtM.inv g)) = q9mtTau := by
    rw [← q9mtM.mul_assoc g q9mtTau (q9mtM.inv g),
        show q9mtM.mul g q9mtTau = q9mtM.mul q9mtTau g from hcg,
        q9mtM.mul_assoc q9mtTau g (q9mtM.inv g), q9mtM.mul_inv, q9mtM.mul_one]
  rw [hX, hY]

/-- **q9mt-3c（★）: テータ群 q9mtGrp = C_{M₉}(g_τ)**（中心化群条件 qᵃw⁹=1 の部分群）。 -/
def q9mtGrp : Subgroup q9mtM where
  mem := q9mtMem
  one_mem := q9mt_mem_one
  mul_mem := fun {a b} ha hb => q9mt_mem_mul a b ha hb
  inv_mem := fun {a} ha => q9mt_mem_inv a ha

/-! ## q9mt-4: ★ 所属の成分特徴付け mem_iff（成分分割・厳密）と μ₉ 消費 -/

/-- 付値方程式 54a+9v=0 ⟹ 6a+v=0（Int・omega）。 -/
theorem q9mt_val_fwd (a v : Int) (h : a * 54 + 9 * v = 0) : 6 * a + v = 0 := by omega

/-- 付値方程式の逆向き 6a+v=0 ⟹ 54a+9v=0（Int・omega）。 -/
theorem q9mt_val_bwd (a v : Int) (h : 6 * a + v = 0) : a * 54 + 9 * v = 0 := by omega

/-- **q9mt-4a（★）: 所属の成分特徴付け** qᵃw⁹=1 ⟺ (6a+v_w=0 ∧ (u₆⁹)ᵃ·u_w⁹=1)。
    M^×=ℤ×U₃ の成分ごとの分割（完全性不要・厳密）。付値成分 54a+9v_w=0 ⟺ 6a+v_w=0、
    単数成分 (u₆⁹)ᵃ·u_w⁹=1（q9tlQ.2=u₆⁹）。a≠0 枝の μ₉₊ 解消は正直限定 1 のとおり非目標。 -/
theorem q9mt_mem_iff (g : q9mtCar) :
    q9mtMem g ↔ (6 * g.1.2 + g.2.1 = 0 ∧
      q3kU.mul (tateZpow q3kU q9tlQ.2 g.1.2)
        (tateZpow q3kU g.2.2 9) = q3kU.one) := by
  obtain ⟨⟨c, a⟩, vw, uw⟩ := g
  show q9mtMem ((c, a), (vw, uw))
     ↔ (6 * a + vw = 0 ∧ q3kU.mul (tateZpow q3kU q9tlQ.2 a)
          (tateZpow q3kU uw 9) = q3kU.one)
  have hQ1 : (tateZpow q9tlMx q9tlQ a).1 = a * 54 := q9tl_pow_fst a
  have hQ2 : (tateZpow q9tlMx q9tlQ a).2 = tateZpow q3kU q9tlQ.2 a :=
    q9mt_zpow_snd q9tlQ a
  have hW1 : (tateZpow q9tlMx ((vw, uw) : q9tlMx.carrier) 9).1 = 9 * vw := by
    rw [q9tl_zpow_fst ((vw, uw) : q9tlMx.carrier) 9, tateZpow_intGrp]
  have hW2 : (tateZpow q9tlMx ((vw, uw) : q9tlMx.carrier) 9).2 = tateZpow q3kU uw 9 :=
    q9mt_zpow_snd ((vw, uw) : q9tlMx.carrier) 9
  have hpair : q9mtMem ((c, a), (vw, uw))
      ↔ ((tateZpow q9tlMx q9tlQ a).1 + (tateZpow q9tlMx ((vw, uw) : q9tlMx.carrier) 9).1
            = (0 : Int)
          ∧ q3kU.mul (tateZpow q9tlMx q9tlQ a).2
              (tateZpow q9tlMx ((vw, uw) : q9tlMx.carrier) 9).2 = q3kU.one) := by
    show ((tateZpow q9tlMx q9tlQ a).1 + (tateZpow q9tlMx ((vw, uw) : q9tlMx.carrier) 9).1,
            q3kU.mul (tateZpow q9tlMx q9tlQ a).2
              (tateZpow q9tlMx ((vw, uw) : q9tlMx.carrier) 9).2)
          = ((0 : Int), q3kU.one) ↔ _
    rw [Prod.mk.injEq]
  rw [hpair, hQ1, hW1, hQ2, hW2]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨q9mt_val_fwd a vw h1, h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨q9mt_val_bwd a vw h1, h2⟩

/-- **q9mt-4b（★★★・μ₉ 消費）: 付値 0 の所属 ⟹ 単数部 ∈ μ₉** — a=0 の中心化群元
    （＝valuation-0 の内部円分スライス）は u_w∈μ₉。所属から (u₆⁹)⁰·u_w⁹=1 ゆえ u_w⁹=1、
    9 乗を 9 重積へ開き（q9mt_ninth_gen）、Subtype.val で carrier に落とし
    **`q9c_mu9_complete`（Module B）を消費**して μ₉ に確定。q3m3_mem_val0_mu3 の 9 乗版で、
    設計 §2.4 が確認した「9 重積 ⇄ tateZpow 変換 1 本で q9c 側に追加要求なし」を実現する。
    後続 q9mr が恒等固定する「テータ環境の内部 μ₉」の実在。 -/
theorem q9mt_mem_val0_mu9 (g : q9mtCar) (hmem : q9mtMem g) (ha : g.1.2 = 0) :
    q3kMu9 g.2.2.val := by
  have hiff := (q9mt_mem_iff g).mp hmem
  obtain ⟨_, h2⟩ := hiff
  rw [ha] at h2
  -- (u₆⁹)⁰ = 1 ⟹ u_w⁹ = 1（U₃ 内）
  have h2' : tateZpow q3kU g.2.2 9 = q3kU.one := by
    have hz : tateZpow q3kU q9tlQ.2 (0 : Int) = q3kU.one := tateZpow_zero q3kU q9tlQ.2
    rw [hz, q3kU.one_mul] at h2
    exact h2
  -- 9 乗を q9c の 9 重積形へ開く
  have h9 : q3kU.mul (q3kU.mul (q3kU.mul (q3kU.mul g.2.2 g.2.2) g.2.2)
              (q3kU.mul (q3kU.mul g.2.2 g.2.2) g.2.2))
              (q3kU.mul (q3kU.mul g.2.2 g.2.2) g.2.2) = q3kU.one := by
    rw [← q9mt_ninth_gen q3kU g.2.2]; exact h2'
  -- .val に落とす: u_w.val の 9 重積 = q3kOne（q9c 消費形へ一致）
  have hval : q3kMul (q3kMul (q3kMul (q3kMul g.2.2.val g.2.2.val) g.2.2.val)
              (q3kMul (q3kMul g.2.2.val g.2.2.val) g.2.2.val))
              (q3kMul (q3kMul g.2.2.val g.2.2.val) g.2.2.val) = q3kOne :=
    congrArg Subtype.val h9
  exact q9c_mu9_complete g.2.2.val hval

/-! ## q9mt-5: ★★ 交換子＝μ₉ 値 Weil ペアリング e₉・非退化 e₉(g₃,g_ζ)≠1 -/

/-- **q9mt-5a（★）: 実 Weil ペアリング** e₉(g,g') = w'ᵃ·w^{−a'}（交換子のスカラー成分・
    M^× 値）。level-9 では非退化値が μ₉ に落ちる（原始 9 乗根！）。 -/
def q9mtWeil (g g' : q9mtCar) : q9tlMx.carrier :=
  q9tlMx.mul (tateZpow q9tlMx g'.2 g.1.2) (tateZpow q9tlMx g.2 (-g'.1.2))

/-- **q9mt-5b（★★）: 交換子＝Weil ペアリング** [g,g'] = (e₉(g,g'),0,1)。 -/
theorem q9mt_comm_eq_weil (g g' : q9mtCar) :
    q9mtComm g g' = ((q9mtWeil g g', (0 : Int)), q9tlMx.one) :=
  q9mt_commutator g g'

/-- **q9mt-5c（★）: 交代性** e₉(g,g)=1（任意の元は自分自身と可換）。 -/
theorem q9mt_weil_alt (g : q9mtCar) : q9mtWeil g g = q9tlMx.one := by
  show q9tlMx.mul (tateZpow q9tlMx g.2 g.1.2) (tateZpow q9tlMx g.2 (-g.1.2)) = q9tlMx.one
  rw [← tateZpow_add]
  have hx : g.1.2 + -g.1.2 = (0 : Int) := by omega
  rw [hx]
  rfl

/-- **q9mt-5d（★）: 非可換 witness g_{[3]} = (1,−1,3)**（3=(6,u₆)∈M^×・[3] の lift）。
    membership: v_w=6=−6·(−1) ∧ (u₆⁹)^{−1}·(u₆)⁹=1（u_q=u₆⁹ で定義的に閉じる）。 -/
def q9mtG3 : q9mtCar := ((q9tlMx.one, (-1 : Int)), q9tl3)

/-- **q9mt-5e（★）: 非可換 witness g_{[ζ₉]} = (1,0,ζ₉)**（ζ₉=(0,Y)∈M^×・[ζ₉] の lift）。
    membership: v_w=0=−6·0 ∧ (u₆⁹)⁰·ζ₉⁹=1（Y⁹=1・q9tl_zpow9）。 -/
def q9mtGZeta : q9mtCar := ((q9tlMx.one, (0 : Int)), q9tlZeta9Elt)

/-- g_{[3]} ∈ テータ群（q9mt_mem_iff.mpr・u_q=u₆⁹ で定義的に閉じる）。 -/
theorem q9mt_g3_mem : q9mtMem q9mtG3 := by
  apply (q9mt_mem_iff q9mtG3).mpr
  refine ⟨?_, ?_⟩
  · show (6 : Int) * (-1) + 6 = 0
    omega
  · show q3kU.mul (tateZpow q3kU q9tlQ.2 (-1)) (tateZpow q3kU q9tl3.2 9) = q3kU.one
    have h1 : tateZpow q3kU q9tlQ.2 (-1) = q3kU.inv q9tlQ.2 :=
      tateZpow_negOne q3kU q9tlQ.2
    rw [h1]
    show q3kU.mul (q3kU.inv q9tlQ.2) (tateNpow q3kU q9tlU3 9) = q3kU.one
    exact q3kU.inv_mul q9tlQ.2

/-- g_{[ζ₉]} ∈ テータ群（q9mt_mem_iff.mpr・q9tl_zpow9 消費）。 -/
theorem q9mt_gz_mem : q9mtMem q9mtGZeta := by
  apply (q9mt_mem_iff q9mtGZeta).mpr
  refine ⟨?_, ?_⟩
  · show (6 : Int) * 0 + 0 = 0
    omega
  · show q3kU.mul (tateZpow q3kU q9tlQ.2 0) (tateZpow q3kU q9tlZeta9U 9) = q3kU.one
    rw [tateZpow_zero q3kU q9tlQ.2, q3kU.one_mul]
    show tateNpow q3kU q9tlZeta9U 9 = q3kU.one
    apply Subtype.ext
    exact q9tl_zpow9

/-- **q9mt-5f（★★）: 実 μ₉ 値 Weil ペアリング** e₉([3],[ζ₉]) = ζ₉⁻¹ = (0, ζ₉⁻¹)。
    a₃=−1・a_ζ=0 で e₉ = ζ₉^{a₃}·3^{−a_ζ} = ζ₉⁻¹·1 = ζ₉⁻¹（∈実 μ₉ ⊂ U₃）。
    実曲線の実テータ交換子から得た初の**原始 9 乗根**（wild 円分値）。 -/
theorem q9mt_weil_g3_gz :
    q9mtWeil q9mtG3 q9mtGZeta = (((0 : Int)), q3kU.inv q9tlZeta9U) := by
  show q9tlMx.mul (tateZpow q9tlMx q9tlZeta9Elt (-1)) (tateZpow q9tlMx q9tl3 (-(0 : Int)))
     = (((0 : Int)), q3kU.inv q9tlZeta9U)
  have h00 : -(0 : Int) = 0 := by omega
  have hz : tateZpow q9tlMx q9tl3 (-(0 : Int)) = q9tlMx.one := by
    rw [h00]; exact tateZpow_zero q9tlMx q9tl3
  have hi : tateZpow q9tlMx q9tlZeta9Elt (-1) = (((0 : Int)), q3kU.inv q9tlZeta9U) := by
    have e : tateZpow q9tlMx q9tlZeta9Elt (-1) = q9tlMx.inv q9tlZeta9Elt :=
      tateZpow_negOne q9tlMx q9tlZeta9Elt
    rw [e]
    show ((intGrp.inv (0 : Int)), q3kU.inv q9tlZeta9U) = (((0 : Int)), q3kU.inv q9tlZeta9U)
    have hn : intGrp.inv (0 : Int) = (0 : Int) := rfl
    rw [hn]
  rw [hi, hz, q9tlMx.mul_one]

/-- **q9mt-5g（★★★）: 非退化性** e₉([3],[ζ₉]) = ζ₉⁻¹ ≠ 1（実 μ₉ 値が非自明）。
    inv ζ₉=1 ⟹ ζ₉=1 に矛盾（q3k_zeta9_ne_one）。**μ₃ でなく原始 9 乗根**の非退化——
    後続 q9mr が殺す (1+3ℤ₃)/(1+9ℤ₃) 円分不定性の実担体（level-3 の ζ₃⁻¹ に対する質的新規）。 -/
theorem q9mt_weil_nondeg : q9mtWeil q9mtG3 q9mtGZeta ≠ q9tlMx.one := by
  rw [q9mt_weil_g3_gz]
  intro h
  have hu : q3kU.inv q9tlZeta9U = q3kU.one := congrArg Prod.snd h
  have hz : q9tlZeta9U = q3kU.one := by
    have hh := congrArg q3kU.inv hu
    rw [Grp.inv_inv, Grp.inv_one] at hh
    exact hh
  have hval : q3kZeta9 = q3kOne := congrArg Subtype.val hz
  exact q3k_zeta9_ne_one hval

/-- **q9mt-5h（★★★）: 実曲線に接続された初の μ₉ 値非可換対象** —
    [g_{[3]},g_{[ζ₉]}] ≠ 1（交換子＝μ₉ 値 Weil ペアリング ζ₉⁻¹≠1）。
    q3m3 の μ₃ 値 non-abelian の 9 乗版・原始 9 乗円分の実担体。 -/
theorem q9mt_nonabelian : q9mtComm q9mtG3 q9mtGZeta ≠ q9mtOne := by
  rw [q9mt_comm_eq_weil]
  intro h
  apply q9mt_weil_nondeg
  exact congrArg (fun z => z.1.1) h

/-! ## q9mt-6: テータ群射影が E_{3⁹}[9] 点 [3]・[ζ₉] に到達 -/

/-- **q9mt-6a: g_{[3]} の w-成分は [3]∈E_{3⁹}[9] へ射影**（q9tl3pt・位数ちょうど 9）。 -/
theorem q9mt_proj_e9_three : q9tlProj.map q9mtG3.2 = q9tl3pt := rfl

/-- **q9mt-6b: g_{[ζ₉]} の w-成分は [ζ₉]∈E_{3⁹}[9] へ射影**（q9tlZeta9・位数ちょうど 9）。 -/
theorem q9mt_proj_e9_zeta : q9tlProj.map q9mtGZeta.2 = q9tlZeta9 := rfl

/-! ## q9mt-7: capstone -/

/-- **q9mt-7a: level-9 実テータ群データ（μ₉ 値 Weil ペアリング）** — 中心化群としての
    テータ群・交換子＝μ₉ 値 Weil ペアリング・所属の成分特徴付け・付値 0 の μ₉ 完全性消費
    （q9c_mu9_complete）・非退化 e₉([3],[ζ₉])≠1（**原始 9 乗根**）・初の μ₉ 値非可換対象・
    E_{3⁹}[9] 射影を束ねる。 -/
structure Q3Mu9ThetaGroupData where
  /-- テータ群 = C_{M₉}(g_τ)（中心化群）。 -/
  grp : Subgroup q9mtM
  /-- 中心化群としての特徴付け。 -/
  isCentralizer : ∀ g, grp.mem g ↔ q9mtMul g q9mtTau = q9mtMul q9mtTau g
  /-- 交換子＝μ₉ 値 Weil ペアリング。 -/
  commutator : ∀ g g', q9mtComm g g' = ((q9mtWeil g g', (0 : Int)), q9tlMx.one)
  /-- 所属の成分特徴付け（6a+v_w=0 ∧ (u₆⁹)ᵃu_w⁹=1）。 -/
  memIff : ∀ g, grp.mem g ↔ (6 * g.1.2 + g.2.1 = 0 ∧
    q3kU.mul (tateZpow q3kU q9tlQ.2 g.1.2) (tateZpow q3kU g.2.2 9) = q3kU.one)
  /-- 付値 0 の所属 ⟹ 単数部∈μ₉（μ₉ 完全性 q9c_mu9_complete 消費）。 -/
  memVal0Mu9 : ∀ g, grp.mem g → g.1.2 = 0 → q3kMu9 g.2.2.val
  /-- Weil ペアリングは交代的。 -/
  weilAlt : ∀ g, q9mtWeil g g = q9tlMx.one
  /-- ★★ 非退化 μ₉ 値 e₉([3],[ζ₉]) = ζ₉⁻¹ ≠ 1（原始 9 乗根）。 -/
  weilNondeg : q9mtWeil q9mtG3 q9mtGZeta ≠ q9tlMx.one
  /-- ★ 初の μ₉ 値非可換対象。 -/
  nonabelian : q9mtComm q9mtG3 q9mtGZeta ≠ q9mtOne
  /-- witness g_{[3]}・g_{[ζ₉]} はテータ群の元。 -/
  g3Mem : grp.mem q9mtG3
  gzMem : grp.mem q9mtGZeta
  /-- w-成分は E_{3⁹}[9] 点 [3]・[ζ₉] へ射影。 -/
  projThree : q9tlProj.map q9mtG3.2 = q9tl3pt
  projZeta : q9tlProj.map q9mtGZeta.2 = q9tlZeta9

/-- **q9mt-7b: 見出し実例** — M = O_M 上の level-9 実テータ群（μ₉ 値 Weil）。 -/
def q9mt_data : Q3Mu9ThetaGroupData where
  grp := q9mtGrp
  isCentralizer := q9mt_mem_comm
  commutator := q9mt_comm_eq_weil
  memIff := q9mt_mem_iff
  memVal0Mu9 := q9mt_mem_val0_mu9
  weilAlt := q9mt_weil_alt
  weilNondeg := q9mt_weil_nondeg
  nonabelian := q9mt_nonabelian
  g3Mem := q9mt_g3_mem
  gzMem := q9mt_gz_mem
  projThree := q9mt_proj_e9_three
  projZeta := q9mt_proj_e9_zeta

/-- **q9mt-7c: level-9 実テータ群（μ₉ 値 Weil ペアリング）の存在**
    （実 M = O_M・q=3⁹・レベル 9・μ₉・q9c_mu9_complete 消費）。 -/
theorem q9mt_exists : Nonempty Q3Mu9ThetaGroupData := ⟨q9mt_data⟩

end IUT
