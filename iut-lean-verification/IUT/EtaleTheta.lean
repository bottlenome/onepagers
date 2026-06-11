/-
  IUT/EtaleTheta.lean — M11（エタールテータの cyclotomic rigidity [EtTh]）の形式化

  IUT II のガロア評価（M4 のテータ値 q^{j²}）の根拠は、[EtTh] の
  **mono-theta 環境の cyclotomic rigidity**（[EtTh] Cor 2.19）である:

    シクロトーム（ẑ(1) のコピー、離散版は ℤ）の同型は一般に
    ẑ×-torsor 分（離散版は ±1）の不定性を持つが、テータ群
    （theta group、Heisenberg 群）の交換子構造はシクロトームの
    **標準生成元**を切り出し、この不定性を消す（剛性 rigidity）。

  この二段構え——「裸のシクロトームは ±1 の不定性 / テータ構造付き
  なら剛性」——が [EtTh] の核心であり、ここでは離散モデル
  （テータ群 = 離散 Heisenberg 群 ℤ³、シクロトーム = 中心 ≅ ℤ）の上で
  その全論理を**公理化なしの完全証明**として形式化する。

  検証する定理（全て sorry なし・公理化ゼロ。具体群上の完全証明）:
  * M11-1 `theta_comm` — テータ群の交換子公式
    [(a,b,c), (a',b',c')] = (0, 0, ab'−a'b)。交換子が中心
    シクロトームに落ち、**シンプレクティック形式**になる
  * M11-2 `comm_xy` — 標準生成元の交換子 [x, y] = 中心の生成元 z。
    「テータ群の交換子構造がシクロトームの標準生成元を指定する」
    （[EtTh] の first Chern class = 交換子ペアリングの離散版）
  * M11-3 `cyclotome_indeterminacy` — **剛性なしの場合**: 裸の
    シクロトーム ℤ の（可逆）自己準同型は ±1 のみ。これが
    cyclotomic rigidity が消すべき不定性（ẑ× の離散版）の正体
  * M11-4 `marked_cyclotome_rigid` / `marked_iso_unique` — 生成元を
    指定（mark）されたシクロトームの自己同型は恒等のみ・同型は一意
  * M11-5 `mono_theta_cyclotomic_rigidity` — **[EtTh] Cor 2.19 の
    離散骨格**: テータ群の自己同型 σ が標準生成元 x, y を中心ズレ
    （= テータ切断の取り替え、(0,0,z) 倍）を除いて保つなら、σ は
    中心シクロトームの生成元を**厳密に固定**する。すなわち
    テータ切断の不定性は交換子を通じてシクロトームに到達しない
  * M11-6 `rigid_theta_values` — 剛性の帰結（M11 → M9/M4 接続）:
    mark を保つ同一視のもとでテータ指数簿記 j ↦ j²（M9-7 で一意性
    証明済み）は絶対的（単数倍の不定性なし）

  **形式化の範囲（正直な申告)**: ここで扱ったのは離散テータ群
  （l-等分前の Heisenberg 骨格）であり、p 進体上の実際の mono-theta
  環境（μ_l 係数、ガロア作用付き、tempered 基本群の商として実現）と
  「エタールテータ関数の関数等式がこの交換子構造を実現する」ことは
  未形式化。後者は M9 の `theta_exponent_unique`（自動形式性差分
  方程式）と本モジュールの剛性が接続する点に局在する。
-/
import IUT.FundamentalGroup

namespace IUT

/-! ## シクロトームの一般論: 不定性 ±1 と mark による剛性

シクロトーム（離散版 = 無限巡回群 ℤ = `intGrp`）の自己同型の分類。 -/

/-- ℤ の冪の一般公式: g^n = n·g（`intGrp_pow_one` の一般化）。 -/
theorem intGrp_pow_eq (g : Int) (n : Nat) : intGrp.pow g n = (n : Int) * g := by
  induction n with
  | zero =>
    show (0 : Int) = ((0 : Nat) : Int) * g
    have h0 : ((0 : Nat) : Int) = 0 := rfl
    rw [h0, Int.zero_mul]
  | succ k ih =>
    show g + intGrp.pow g k = ((k + 1 : Nat) : Int) * g
    rw [ih]
    have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [hc, Int.add_mul, Int.one_mul]
    exact Int.add_comm g _

/-- ℤ の自己準同型の自然数点での線型性（補題）。 -/
theorem hom_int_nat (f : Hom intGrp intGrp) (n : Nat) :
    f.map ((n : Nat) : Int) = ((n : Nat) : Int) * f.map 1 := by
  rw [← intGrp_pow_one n, f.map_pow, intGrp_pow_eq, intGrp_pow_eq, Int.mul_one]

/-- ℤ の自己準同型は線型: f(j) = j·f(1)。
    （シクロトームの準同型は 1 の行き先で決まる。） -/
theorem hom_int_linear (f : Hom intGrp intGrp) (j : Int) :
    f.map j = j * f.map 1 := by
  obtain h | h := Int.natAbs_eq j
  · rw [h]
    exact hom_int_nat f j.natAbs
  · have h2 : f.map (-(j.natAbs : Int)) = -(f.map ((j.natAbs : Nat) : Int)) :=
      f.map_inv _
    rw [h, h2, hom_int_nat f j.natAbs, Int.neg_mul]

/-- 整数の単数: a·b = 1 なら a = ±1（公理化なしの完全証明）。 -/
theorem int_unit {a b : Int} (h : a * b = 1) : a = 1 ∨ a = -1 := by
  have h1 : a.natAbs * b.natAbs = 1 := by
    rw [← Int.natAbs_mul, h]
    rfl
  have h2 : a.natAbs = 1 := by
    cases hA : a.natAbs with
    | zero =>
      rw [hA, Nat.zero_mul] at h1
      omega
    | succ k =>
      cases k with
      | zero => rfl
      | succ k' =>
        rw [hA] at h1
        cases hB : b.natAbs with
        | zero => rw [hB, Nat.mul_zero] at h1; omega
        | succ j =>
          rw [hB, Nat.mul_succ] at h1
          revert h1
          generalize (k' + 1 + 1) * j = T
          intro h1
          omega
  obtain h3 | h3 := Int.natAbs_eq a
  · left; rw [h3, h2]; rfl
  · right; rw [h3, h2]; rfl

/-- **定理 (M11-3): 裸のシクロトームの不定性** — 左逆を持つ
    （= 可逆性の弱い形の）自己準同型は恒等 (+1) か反転 (−1) のみ。
    これが cyclotomic rigidity が消去対象とする ẑ×-不定性の
    離散版（±1）である。 -/
theorem cyclotome_indeterminacy (f g : Hom intGrp intGrp)
    (hgf : ∀ n : Int, g.map (f.map n) = n) :
    (∀ n : Int, f.map n = n) ∨ (∀ n : Int, f.map n = -n) := by
  have h1 : f.map 1 * g.map 1 = 1 := by
    have h := hgf 1
    rw [hom_int_linear g (f.map 1)] at h
    exact h
  obtain h | h := int_unit h1
  · left
    intro n
    rw [hom_int_linear f n, h, Int.mul_one]
  · right
    intro n
    rw [hom_int_linear f n, h, Int.mul_neg, Int.mul_one]

/-- **定理 (M11-4a): marked シクロトームの剛性** — 生成元を保つ
    （f(1) = 1）自己準同型は恒等。mark があれば ±1 不定性は消える。 -/
theorem marked_cyclotome_rigid (f : Hom intGrp intGrp)
    (hmark : f.map 1 = 1) : ∀ n : Int, f.map n = n := by
  intro n
  rw [hom_int_linear f n, hmark, Int.mul_one]

/-- **定理 (M11-4b): marked 同型の一意性** — mark を保つ二つの
    準同型は一致する。「剛性 = 標準同型の一意存在」の一意性部分。 -/
theorem marked_iso_unique (f g : Hom intGrp intGrp)
    (hf : f.map 1 = 1) (hg : g.map 1 = 1) :
    ∀ n : Int, f.map n = g.map n := by
  intro n
  rw [marked_cyclotome_rigid f hf, marked_cyclotome_rigid g hg]

/-! ## テータ群（離散 Heisenberg 群）と交換子による剛性

[EtTh] の mono-theta 環境の核は theta group（Heisenberg 群）の
交換子構造である。離散モデル: 台 ℤ³、積
(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab')、中心 = {(0,0,*)} ≅ ℤ
（これがシクロトームの離散モデル）。 -/

/-- 3 成分の組の等値補題（モデル計算用）。 -/
theorem triple_ext {a₁ b₁ c₁ a₂ b₂ c₂ : Int}
    (h1 : a₁ = a₂) (h2 : b₁ = b₂) (h3 : c₁ = c₂) :
    ((a₁, b₁, c₁) : Int × Int × Int) = (a₂, b₂, c₂) := by
  rw [h1, h2, h3]

/-- **テータ群**（離散 Heisenberg 群）。 -/
@[reducible] def thetaGrp : Grp where
  carrier := Int × Int × Int
  mul := fun x y => (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2 + x.1 * y.2.1)
  one := (0, 0, 0)
  inv := fun x => (-x.1, -x.2.1, -x.2.2 + x.1 * x.2.1)
  mul_assoc := by
    intro x y z
    obtain ⟨a, b, c⟩ := x
    obtain ⟨a', b', c'⟩ := y
    obtain ⟨a'', b'', c''⟩ := z
    show (a + a' + a'', b + b' + b'',
        c + c' + a * b' + c'' + (a + a') * b'')
      = (a + (a' + a''), b + (b' + b''),
        c + (c' + c'' + a' * b'') + a * (b' + b''))
    refine triple_ext (by omega) (by omega) ?_
    rw [Int.add_mul, Int.mul_add]
    generalize a * b' = P
    generalize a * b'' = Q
    generalize a' * b'' = R
    omega
  one_mul := by
    intro x
    obtain ⟨a, b, c⟩ := x
    show ((0 : Int) + a, (0 : Int) + b, (0 : Int) + c + 0 * b) = (a, b, c)
    refine triple_ext (by omega) (by omega) (by omega)
  inv_mul := by
    intro x
    obtain ⟨a, b, c⟩ := x
    show (-a + a, -b + b, -c + a * b + c + -a * b) = ((0 : Int), 0, 0)
    refine triple_ext (by omega) (by omega) ?_
    rw [Int.neg_mul]
    generalize a * b = P
    omega

/-- 交換子 [x, y] = x·y·x⁻¹·y⁻¹。 -/
def Grp.comm (G : Grp) (x y : G.carrier) : G.carrier :=
  G.mul (G.mul x y) (G.mul (G.inv x) (G.inv y))

/-- 準同型は交換子を保つ。 -/
theorem Hom.map_grp_comm {G H : Grp} (f : Hom G H) (x y : G.carrier) :
    f.map (G.comm x y) = H.comm (f.map x) (f.map y) := by
  unfold Grp.comm
  rw [f.map_mul, f.map_mul, f.map_mul, f.map_inv, f.map_inv]

/-- **定理 (M11-1): テータ群の交換子公式** — 交換子は中心
    シクロトーム {(0,0,*)} に落ち、その値はシンプレクティック形式
    ab' − a'b である。テータ群の「非可換性のすべて」がシクロトーム
    一次元分に圧縮されることの機械検証。 -/
theorem theta_comm (a b c a' b' c' : Int) :
    thetaGrp.comm (a, b, c) (a', b', c') = (0, 0, a * b' - a' * b) := by
  unfold Grp.comm
  show (a + a' + (-a + -a'), b + b' + (-b + -b'),
      c + c' + a * b' + (-c + a * b + (-c' + a' * b') + -a * -b')
        + (a + a') * (-b + -b'))
    = ((0 : Int), (0 : Int), a * b' - a' * b)
  refine triple_ext (by omega) (by omega) ?_
  rw [Int.neg_mul_neg, Int.add_mul, Int.mul_add, Int.mul_add,
    Int.mul_neg, Int.mul_neg, Int.mul_neg, Int.mul_neg]
  generalize a * b' = P
  generalize a * b = Q
  generalize a' * b' = R
  generalize a' * b = S
  omega

/-- **定理 (M11-2): 交換子がシクロトームの標準生成元を指定する** —
    標準生成元 x = (1,0,0), y = (0,1,0) の交換子は中心の生成元
    z = (0,0,1) に一致する。[EtTh] における「テータ群の交換子
    ペアリング = first Chern class がシクロトームを標準化する」
    ことの離散版。 -/
theorem comm_xy : thetaGrp.comm (1, 0, 0) (0, 1, 0) = ((0, 0, 1) : Int × Int × Int) := by
  rw [theta_comm]
  rfl

/-- **定理 (M11-5): mono-theta cyclotomic rigidity**（[EtTh] Cor 2.19
    の離散骨格）— テータ群の自己準同型 σ が標準生成元 x, y を
    **中心ズレを除いて**保つ（σ(x) = (1,0,z₁)、σ(y) = (0,1,z₂)。
    中心ズレ (0,0,z) はテータ切断の取り替えに相当）なら、σ は中心
    シクロトームの生成元 (0,0,1) を厳密に固定する。

    すなわち: テータ切断の不定性（z₁, z₂ は任意）は交換子を通過する
    際に**完全に相殺**され、シクロトームには到達しない。これが
    「mono-theta 環境はシクロトームを剛性化する」の形式的内容であり、
    M11-3 の ±1 不定性が消える機構である。 -/
theorem mono_theta_cyclotomic_rigidity (σ : Hom thetaGrp thetaGrp) (z₁ z₂ : Int)
    (hx : σ.map (1, 0, 0) = (1, 0, z₁))
    (hy : σ.map (0, 1, 0) = (0, 1, z₂)) :
    σ.map (0, 0, 1) = ((0, 0, 1) : Int × Int × Int) := by
  have h1 : σ.map (thetaGrp.comm (1, 0, 0) (0, 1, 0))
      = thetaGrp.comm (1, 0, z₁) (0, 1, z₂) := by
    rw [Hom.map_grp_comm, hx, hy]
  rw [comm_xy] at h1
  rw [h1, theta_comm]
  rfl

/-- **定理 (M11-6): 剛性のもとでのテータ値の絶対性**（M11 → M9/M4
    接続）— mark を保つシクロトーム同一視のもとで、テータ指数簿記
    j ↦ j²（M9-7 `theta_exponent_unique` で一意性証明済み、M4 の
    テータ値 q^{j²} の指数）は単数倍の不定性なしに転送される。
    cyclotomic rigidity がガロア評価（M4）の値の well-defined 性を
    支える経路の形式化。 -/
theorem rigid_theta_values (f : Hom intGrp intGrp)
    (hmark : f.map 1 = 1) (j : Int) :
    f.map (j * j) = j * j :=
  marked_cyclotome_rigid f hmark (j * j)

end IUT
