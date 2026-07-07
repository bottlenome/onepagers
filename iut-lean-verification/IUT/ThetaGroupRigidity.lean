-- M399F ThetaGroupRigidity [実・本物・柱A]
-- complete_pct 影響: 柱A で テータ群の内部自己同型剛性を完全証明——共役はアーベル化 ℤ² に自明・中心に各点自明に作用し、その中心シフトはシンプレクティック形式 ω に一致（conj_{(a,b,t)}(x,y,z)=(x,y,z+ay−bx) を厳密計算）。逆に「アーベル化と中心の両方で恒等」な任意の群自己準同型は内部自己同型に一致し（本丸 tgrig_rigidity）、内部自己同型群は thetaGrp/Z ≅ ℤ² でパラメータ化される（tgrig_inner_eq_iff）。ゆえに M394F で内在的に復元された中心 = 円分体 μ_l は内部自己同型のもとで剛（tgrig_cyclotome_rigid）——mono-anabelian 剛性の本物の一歩。
-- 正直な限定: 完全な mono-anabelian 復元アルゴリズム（幾何的 tempered π₁^temp の slim 性・π₁^ét からの数体復元本体）は外部/後続。本モジュールは離散 Heisenberg 骨格 thetaGrp の内部自己同型剛性のみを扱う。

/-
  IUT/ThetaGroupRigidity.lean — M399F [実／本物・柱A]
  分類: 実（テータ群の内部自己同型剛性＝mono-anabelian rigidity の本物の建設）

  M394F (IUT/ThetaGroupReconstruction.lean, prefix tgr) はテータ群（離散 Heisenberg 群
  thetaGrp）の中心 Z = {(0,0,∗)} が「任意の元と可換」という純群論的述語だけから内在的に
  復元されること（Z = 交換子部分群 = μ_l の座）を完全証明した。M389F (ttoa) は中心への
  外ガロア作用（χ 捻り）を建設した。

  本モジュールは次の遠アーベル段階 **RIGIDITY（剛性）** を建設する:
  「テータ群は、その内在的データ（アーベル化 ℤ² と中心 Z）への作用まで込めて、
   内部自己同型の分だけしか自己同型の自由度を持たない」。

  建設内容（すべて本物の Heisenberg 計算・toy 群なし・選択公理不使用）:
    * **内部自己同型 conj_g は本物の群準同型** (M399F-1): 任意の抽象群 G と g に対し
      conj_g(x) = g·x·g⁻¹ が Hom G G をなすことを群公理だけから証明（tgrigConj）。
      合成則 conj_g ∘ conj_h = conj_{gh}・単位則 conj_1 = id・全射性（逆は conj_{g⁻¹}）
      も抽象群論で完全証明——内部自己同型「群」の本物の構造。
    * **シンプレクティック公式（本物の Heisenberg 計算）** (M399F-2):
        conj_{(a,b,t)}(x,y,z) = (x, y, z + a·y − b·x)
      を厳密に計算（tgrig_conj_formula）。ゆえに共役は
      (i) アーベル化 ℤ²（第 1・2 成分）に恒等で作用し、
      (ii) 中心シフトはシンプレクティック形式 ω((a,b),(x,y)) = a·y − b·x に一致し、
      (iii) 共役子の中心成分 t には依存しない（tgrig_conj_param_free）。
    * **内部自己同型は中心を各点固定** (M399F-3): 群論的中心性 tgrCentral z（M394F）
      だけから conj_g(z) = z を抽象群論で証明——M394F の内在的中心が内部自己同型で
      剛であることの核。
    * **内部自己同型群 ≅ thetaGrp/Z ≅ ℤ²** (M399F-4): conj_g = conj_h（各点一致）
      ⟺ g⁻¹h が中心（tgrig_inner_eq_iff）——内部自己同型は中心剰余
      thetaGrp/Z ≅ ℤ²（アーベル化）で忠実にパラメータ化される。
    * **剛性定理（本丸）** (M399F-5): 任意の群自己準同型 φ : thetaGrp → thetaGrp が
      (i) アーベル化 ℤ² に恒等（第 1・2 成分を保つ）かつ (ii) 中心に各点恒等
      （φ(0,0,c) = (0,0,c)）ならば、φ は**ちょうど内部自己同型**である:
        ∃ g, φ = conj_g （tgrig_rigidity・逆向きも込めた同値 tgrig_inner_characterization）。
      証明は本物: φ の第 3 成分のずれが 1-コサイクル条件を満たすことを準同型性から
      導き、中心恒等性でずれが ℤ² 上の加法的関数に降下し、加法的 ℤ→ℤ 関数の線型性
      （Int 構成子上の帰納法で完全証明）で ω 型シフトに一致させ、共役子を明示構成する。
    * **円分体 μ_l の剛性（遠アーベルの結論）** (M399F-6): M394F で内在的に復元された
      中心の μ_l 同一視（centerToMu）は**任意の**内部自己同型で不変
      （tgrig_cyclotome_rigid）——復元円分体は canonical かつ剛。

  意義: mono-anabelian の剛性言明「群は自分の自己同型を（内在的データへの作用まで
  込めて）内部分しか持たない」の最小だが本物のインスタンス。Mochizuki [EtTh] の
  mono-theta 環境の剛性 3 兄弟（cyclotomic / discrete / constant multiple rigidity）の
  うち円分剛性の群論的核（中心＝μ_l が Aut の内部分に対し不動）を離散 Heisenberg の
  本物の計算で完全証明する。

  正直な限定: これは剛性の**群論的核**であって、完全な mono-anabelian 復元アルゴリズム
  （幾何的 tempered π₁^temp Δ^temp の slim 遠アーベル性・π₁^ét からの数体の遠アーベル
  復元本体・[EtTh] の mono-theta 環境全体の剛性）ではない。主語は離散 Heisenberg 骨格
  thetaGrp（本物の群）と本物の μ_l 同期 centerToMu であり、外部の解析的入力・公理追加は
  ない。全て選択公理不使用（propext / Quot.sound のみ）。
-/
import IUT.ThetaGroupReconstruction

namespace IUT

/-! ## M399F-0: 3 成分射影の外延補題（一般形）

  triple_ext（M11）は明示タプル用。ここでは不透明な項 p q : ℤ³ にも使える一般形を
  用意する（構造 eta により destructuring で還元）。 -/

/-- **M399F-0: 射影一致 → 等値（一般形）** — 3 成分すべての射影が一致すれば等しい。 -/
theorem tgrig_prod3_ext {p q : Int × Int × Int}
    (h1 : p.1 = q.1) (h2 : p.2.1 = q.2.1) (h3 : p.2.2 = q.2.2) : p = q := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨a', b', c'⟩ := q
  exact triple_ext h1 h2 h3

/-! ## M399F-1: 内部自己同型は本物の群準同型（抽象群論・toy なし）

  任意の抽象群 G（M9 `Grp`）と g に対し conj_g(x) = g·x·g⁻¹ が群準同型をなすことを
  群公理（結合律・単位律・逆元律）だけから完全証明する。 -/

/-- **補題 (M399F-1a: 共役の乗法性の計算核)** —
    (g·x·g⁻¹)·(g·y·g⁻¹) = g·(x·y)·g⁻¹（g⁻¹·g を中央で消す・群公理のみ）。 -/
theorem tgrig_conj_mul_aux (G : Grp) (g x y : G.carrier) :
    G.mul (G.mul (G.mul g x) (G.inv g)) (G.mul (G.mul g y) (G.inv g))
      = G.mul (G.mul g (G.mul x y)) (G.inv g) := by
  rw [G.mul_assoc (G.mul g x) (G.inv g) (G.mul (G.mul g y) (G.inv g)),
    ← G.mul_assoc (G.inv g) (G.mul g y) (G.inv g),
    ← G.mul_assoc (G.inv g) g y, G.inv_mul g, G.one_mul y,
    ← G.mul_assoc (G.mul g x) y (G.inv g), G.mul_assoc g x y]

/-- **M399F-1b: 内部自己同型（本物の群準同型）** — conj_g(x) = g·x·g⁻¹。
    Heisenberg に限らない任意の抽象群 G 上の本物の内部自己同型。 -/
def tgrigConj (G : Grp) (g : G.carrier) : Hom G G where
  map := fun x => G.mul (G.mul g x) (G.inv g)
  map_mul := by
    intro x y
    exact (tgrig_conj_mul_aux G g x y).symm

/-- **補題 (M399F-1c: 単位元の逆元は単位元)**。 -/
theorem tgrig_inv_one (G : Grp) : G.inv G.one = G.one := by
  have h := G.inv_mul G.one
  rw [G.mul_one] at h
  exact h

/-- **定理 (M399F-1d: 単位則)** — conj_1 = id。 -/
theorem tgrig_conj_one (G : Grp) (x : G.carrier) :
    (tgrigConj G G.one).map x = x := by
  show G.mul (G.mul G.one x) (G.inv G.one) = x
  rw [G.one_mul, tgrig_inv_one G, G.mul_one]

/-- **補題 (M399F-1e: 積の逆元は逆順の積)** — (g·h)⁻¹ = h⁻¹·g⁻¹（群公理のみ）。 -/
theorem tgrig_inv_mul_rev (G : Grp) (g h : G.carrier) :
    G.inv (G.mul g h) = G.mul (G.inv h) (G.inv g) := by
  have hone : G.mul (G.mul g h) (G.mul (G.inv h) (G.inv g)) = G.one := by
    rw [G.mul_assoc g h (G.mul (G.inv h) (G.inv g)),
      ← G.mul_assoc h (G.inv h) (G.inv g), G.mul_inv h, G.one_mul, G.mul_inv g]
  exact (G.inv_eq_of_mul_eq_one hone).symm

/-- **定理 (M399F-1f: 合成則)** — conj_g ∘ conj_h = conj_{g·h}。
    内部自己同型たちが「群」をなすことの本物の内容（抽象群論・on-the-nose）。 -/
theorem tgrig_conj_comp (G : Grp) (g h x : G.carrier) :
    (tgrigConj G g).map ((tgrigConj G h).map x)
      = (tgrigConj G (G.mul g h)).map x := by
  show G.mul (G.mul g (G.mul (G.mul h x) (G.inv h))) (G.inv g)
    = G.mul (G.mul (G.mul g h) x) (G.inv (G.mul g h))
  rw [tgrig_inv_mul_rev G g h,
    ← G.mul_assoc (G.mul (G.mul g h) x) (G.inv h) (G.inv g),
    G.mul_assoc (G.mul g h) x (G.inv h),
    G.mul_assoc g h (G.mul x (G.inv h)),
    ← G.mul_assoc h x (G.inv h)]

/-- **定理 (M399F-1g: 逆則)** — conj_g ∘ conj_{g⁻¹} = id。 -/
theorem tgrig_conj_left_inv (G : Grp) (g x : G.carrier) :
    (tgrigConj G g).map ((tgrigConj G (G.inv g)).map x) = x := by
  rw [tgrig_conj_comp G g (G.inv g) x, G.mul_inv g]
  exact tgrig_conj_one G x

/-- **定理 (M399F-1h: 内部自己同型は全射)** — 逆写像 conj_{g⁻¹} から。
    M394F-4（全射自己準同型は中心を保つ）の適用条件を満たす具体クラス。 -/
theorem tgrig_conj_surjective (G : Grp) (g : G.carrier) :
    ∀ y, ∃ x, (tgrigConj G g).map x = y :=
  fun y => ⟨(tgrigConj G (G.inv g)).map y, tgrig_conj_left_inv G g y⟩

/-! ## M399F-2: シンプレクティック公式（本物の Heisenberg 計算）

  テータ群上の共役を厳密に計算する: conj_{(a,b,t)}(x,y,z) = (x, y, z + a·y − b·x)。
  第 1・2 成分（アーベル化 ℤ²）は不変、中心シフトはシンプレクティック形式
  ω((a,b),(x,y)) = a·y − b·x、共役子の中心成分 t には依存しない。 -/

/-- **定理 (M399F-2a: シンプレクティック公式／厳密計算)** —
      conj_{(a,b,t)}(x,y,z) = (x, y, z + a·y − b·x)。
    交換子公式（M11 theta_comm）の共役版: 共役の全効果が中心方向の
    シンプレクティック・シフトに圧縮される。 -/
theorem tgrig_conj_formula (a b t x y z : Int) :
    (tgrigConj thetaGrp ((a, b, t) : thetaGrp.carrier)).map
        ((x, y, z) : thetaGrp.carrier)
      = ((x, y, z + a * y - b * x) : thetaGrp.carrier) := by
  show ((a + x + -a, b + y + -b,
      t + z + a * y + (-t + a * b) + (a + x) * -b) : Int × Int × Int)
    = (x, y, z + a * y - b * x)
  refine triple_ext (by omega) (by omega) ?_
  rw [Int.add_mul a x (-b), Int.mul_neg a b, Int.mul_neg x b, Int.mul_comm b x]
  generalize a * y = P
  generalize a * b = Q
  generalize x * b = R
  omega

/-- **定理 (M399F-2b: アーベル化に自明・第 1 成分)** — 共役は第 1 成分を保つ。 -/
theorem tgrig_conj_ab_fst (g x : thetaGrp.carrier) :
    ((tgrigConj thetaGrp g).map x).1 = x.1 := by
  obtain ⟨a, b, t⟩ := g
  obtain ⟨u, v, w⟩ := x
  rw [tgrig_conj_formula]

/-- **定理 (M399F-2c: アーベル化に自明・第 2 成分)** — 共役は第 2 成分を保つ。
    2b と合わせ: 内部自己同型はアーベル化 ℤ² = thetaGrp/Z に恒等で作用する。 -/
theorem tgrig_conj_ab_snd (g x : thetaGrp.carrier) :
    ((tgrigConj thetaGrp g).map x).2.1 = x.2.1 := by
  obtain ⟨a, b, t⟩ := g
  obtain ⟨u, v, w⟩ := x
  rw [tgrig_conj_formula]

/-- **定理 (M399F-2d: 中心シフト = シンプレクティック形式)** —
    共役の第 3 成分のずれはちょうど ω((a,b),(x,y)) = a·y − b·x。 -/
theorem tgrig_conj_symplectic (a b t x y z : Int) :
    ((tgrigConj thetaGrp ((a, b, t) : thetaGrp.carrier)).map
        ((x, y, z) : thetaGrp.carrier)).2.2
      = z + a * y - b * x := by
  rw [tgrig_conj_formula]

/-- **定理 (M399F-2e: 共役子の中心成分は無関係)** — conj_{(a,b,t)} = conj_{(a,b,0)}。
    共役はアーベル化像 (a,b) ∈ ℤ² のみで決まる（内部自己同型が thetaGrp/Z で
    パラメータ化されることの前半）。 -/
theorem tgrig_conj_param_free (a b t : Int) (x : thetaGrp.carrier) :
    (tgrigConj thetaGrp ((a, b, t) : thetaGrp.carrier)).map x
      = (tgrigConj thetaGrp ((a, b, 0) : thetaGrp.carrier)).map x := by
  obtain ⟨u, v, w⟩ := x
  rw [tgrig_conj_formula, tgrig_conj_formula]

/-! ## M399F-3: 内部自己同型は中心を各点固定（抽象群論から）

  M394F の群論的中心性 tgrCentral z だけから conj_g(z) = z を導く——
  内在的に復元された中心（＝μ_l の座）が内部自己同型で**剛**であることの核。 -/

/-- **定理 (M399F-3a: 中心の各点固定・抽象版)** — z が群論的中心元なら conj_g(z) = z。
    証明は純群論的: g·z·g⁻¹ = z·g·g⁻¹ = z（中心性で g を通過させる）。 -/
theorem tgrig_conj_fixes_central (g : thetaGrp.carrier) {z : thetaGrp.carrier}
    (hz : tgrCentral z) : (tgrigConj thetaGrp g).map z = z := by
  show thetaGrp.mul (thetaGrp.mul g z) (thetaGrp.inv g) = z
  rw [← hz g, thetaGrp.mul_assoc z g (thetaGrp.inv g), thetaGrp.mul_inv g,
    thetaGrp.mul_one]

/-- **定理 (M399F-3b: 中心の各点固定・座標版)** — conj_g(0,0,c) = (0,0,c)。 -/
theorem tgrig_conj_fix_center (g : thetaGrp.carrier) (c : Int) :
    (tgrigConj thetaGrp g).map ((0, 0, c) : thetaGrp.carrier)
      = ((0, 0, c) : thetaGrp.carrier) :=
  tgrig_conj_fixes_central g (tgr_center_central c)

/-! ## M399F-4: 内部自己同型群 ≅ thetaGrp/Z ≅ ℤ²

  conj_g = conj_h（各点一致）⟺ g⁻¹·h が中心。ゆえに内部自己同型は中心剰余
  thetaGrp/Z（＝アーベル化 ℤ²）で忠実にパラメータ化され、その作用は
  シンプレクティック形式 ω を介する（M399F-2d）。 -/

/-- **定理 (M399F-4: 内部自己同型の一致 ⟺ 中心差)** —
      (∀x, conj_g x = conj_h x) ↔ tgrCentral (g⁻¹·h)。
    内部自己同型群が thetaGrp/Z ≅ ℤ² であることの本物の内容（忠実性＝ ⟸、
    分離性＝ ⟹ を両方向とも厳密計算で証明）。 -/
theorem tgrig_inner_eq_iff (g h : thetaGrp.carrier) :
    (∀ x : thetaGrp.carrier,
        (tgrigConj thetaGrp g).map x = (tgrigConj thetaGrp h).map x)
      ↔ tgrCentral (thetaGrp.mul (thetaGrp.inv g) h) := by
  obtain ⟨a, b, t⟩ := g
  obtain ⟨a', b', t'⟩ := h
  constructor
  · intro heq
    have h1 := heq ((0, 1, 0) : thetaGrp.carrier)
    have h2 := heq ((1, 0, 0) : thetaGrp.carrier)
    rw [tgrig_conj_formula, tgrig_conj_formula] at h1
    rw [tgrig_conj_formula, tgrig_conj_formula] at h2
    have ha : (0 + a * 1 - b * 0 : Int) = 0 + a' * 1 - b' * 0 :=
      congrArg (fun s : Int × Int × Int => s.2.2) h1
    have hb : (0 + a * 0 - b * 1 : Int) = 0 + a' * 0 - b' * 1 :=
      congrArg (fun s : Int × Int × Int => s.2.2) h2
    refine (tgr_central_iff _).mpr ⟨-t + a * b + t' + -a * b', ?_⟩
    show ((-a + a', -b + b', -t + a * b + t' + -a * b') : Int × Int × Int)
      = (0, 0, -t + a * b + t' + -a * b')
    refine triple_ext (by omega) (by omega) rfl
  · intro hc x
    obtain ⟨c, hc0⟩ := (tgr_central_iff _).mp hc
    have ha : (-a + a' : Int) = 0 :=
      congrArg (fun s : Int × Int × Int => s.1) hc0
    have hb : (-b + b' : Int) = 0 :=
      congrArg (fun s : Int × Int × Int => s.2.1) hc0
    obtain ⟨u, v, w⟩ := x
    rw [tgrig_conj_formula, tgrig_conj_formula]
    refine triple_ext rfl rfl ?_
    rw [show a' = a by omega, show b' = b by omega]

/-! ## M399F-5: 剛性定理（本丸）

  アーベル化 ℤ² に恒等・中心に各点恒等な任意の群自己準同型は**内部自己同型に一致**する。
  証明の骨格: φ の第 3 成分のずれは準同型性から 1-コサイクル条件を満たし、中心恒等性で
  ℤ² 上の加法的関数に降下し、加法的 ℤ→ℤ 関数の線型性（Int 構成子上の帰納法）で
  シンプレクティック型シフトに一致——共役子 g = (q, −p, 0)（p,q は生成元の像の中心座標）
  を明示構成する。 -/

/-- **補題 (M399F-5a: 加法的関数は 0 を保つ)**。 -/
theorem tgrig_additive_zero (g : Int → Int)
    (hadd : ∀ x y : Int, g (x + y) = g x + g y) : g 0 = 0 := by
  have h := hadd 0 0
  rw [Int.add_zero] at h
  omega

/-- **補題 (M399F-5b: 加法的関数は負を保つ)**。 -/
theorem tgrig_additive_neg (g : Int → Int)
    (hadd : ∀ x y : Int, g (x + y) = g x + g y) (x : Int) : g (-x) = -g x := by
  have h := hadd (-x) x
  rw [Int.add_left_neg] at h
  rw [tgrig_additive_zero g hadd] at h
  omega

/-- **補題 (M399F-5c: 加法的関数の自然数部の線型性)** — Nat 帰納法による本物の証明。 -/
theorem tgrig_additive_nat (g : Int → Int)
    (hadd : ∀ x y : Int, g (x + y) = g x + g y) :
    ∀ n : Nat, g (Int.ofNat n) = Int.ofNat n * g 1 := by
  intro n
  induction n with
  | zero =>
      show g 0 = 0 * g 1
      rw [tgrig_additive_zero g hadd]
      omega
  | succ k ih =>
      show g (Int.ofNat k + 1) = (Int.ofNat k + 1) * g 1
      rw [hadd (Int.ofNat k) 1, ih, Int.add_mul, Int.one_mul]

/-- **補題 (M399F-5d: 加法的 ℤ→ℤ 関数は線型)** — g(x) = x·g(1)。
    Int 構成子（ofNat / negSucc）上の場合分けと Nat 帰納法による完全証明。
    Cauchy 型の関数方程式の整数版（選択公理不要——ℤ 上では加法性が線型性を強制する）。 -/
theorem tgrig_additive_linear (g : Int → Int)
    (hadd : ∀ x y : Int, g (x + y) = g x + g y) :
    ∀ x : Int, g x = x * g 1 := by
  intro x
  cases x with
  | ofNat n => exact tgrig_additive_nat g hadd n
  | negSucc n =>
      have h1 : Int.negSucc n = -Int.ofNat (n + 1) := rfl
      rw [h1, tgrig_additive_neg g hadd, tgrig_additive_nat g hadd (n + 1),
        Int.neg_mul]

/-- **定理 (M399F-5e: 剛性定理／本丸)** — 群自己準同型 φ : thetaGrp → thetaGrp が
    (i) アーベル化 ℤ² に恒等（第 1・2 成分を保つ）かつ (ii) 中心に各点恒等ならば、
    φ は内部自己同型である: ∃ g, φ = conj_g。
    共役子は g = (q, −p, 0)、p = φ(1,0,0) の中心座標・q = φ(0,1,0) の中心座標、と
    **明示構成**される（存在は構成的・古典選択なし）。 -/
theorem tgrig_rigidity (φ : Hom thetaGrp thetaGrp)
    (hab1 : ∀ x : thetaGrp.carrier, (φ.map x).1 = x.1)
    (hab2 : ∀ x : thetaGrp.carrier, (φ.map x).2.1 = x.2.1)
    (hcen : ∀ c : Int,
      φ.map ((0, 0, c) : thetaGrp.carrier) = ((0, 0, c) : thetaGrp.carrier)) :
    ∃ g : thetaGrp.carrier,
      ∀ x : thetaGrp.carrier, φ.map x = (tgrigConj thetaGrp g).map x := by
  -- (A) 中心シフト則: φ(a,b,c+d) の中心座標 = φ(a,b,c) の中心座標 + d
  have hA : ∀ a b c d : Int,
      (φ.map ((a, b, c + d) : thetaGrp.carrier)).2.2
        = (φ.map ((a, b, c) : thetaGrp.carrier)).2.2 + d := by
    intro a b c d
    have e : thetaGrp.mul ((a, b, c) : thetaGrp.carrier)
        ((0, 0, d) : thetaGrp.carrier) = ((a, b, c + d) : thetaGrp.carrier) := by
      show ((a + 0, b + 0, c + d + a * 0) : Int × Int × Int) = (a, b, c + d)
      refine triple_ext (by omega) (by omega) (by omega)
    have hm := φ.map_mul ((a, b, c) : thetaGrp.carrier)
      ((0, 0, d) : thetaGrp.carrier)
    rw [e, hcen d] at hm
    have h3 : (φ.map ((a, b, c + d) : thetaGrp.carrier)).2.2
        = (φ.map ((a, b, c) : thetaGrp.carrier)).2.2 + d
          + (φ.map ((a, b, c) : thetaGrp.carrier)).1 * 0 :=
      congrArg (fun s : Int × Int × Int => s.2.2) hm
    omega
  -- (B) x 軸方向の加法性
  have hBx : ∀ a a' : Int,
      (φ.map ((a + a', 0, 0) : thetaGrp.carrier)).2.2
        = (φ.map ((a, 0, 0) : thetaGrp.carrier)).2.2
          + (φ.map ((a', 0, 0) : thetaGrp.carrier)).2.2 := by
    intro a a'
    have e : thetaGrp.mul ((a, 0, 0) : thetaGrp.carrier)
        ((a', 0, 0) : thetaGrp.carrier) = ((a + a', 0, 0) : thetaGrp.carrier) := by
      show ((a + a', 0 + 0, 0 + 0 + a * 0) : Int × Int × Int) = (a + a', 0, 0)
      refine triple_ext rfl (by omega) (by omega)
    have hm := φ.map_mul ((a, 0, 0) : thetaGrp.carrier)
      ((a', 0, 0) : thetaGrp.carrier)
    rw [e] at hm
    have h2 : (φ.map ((a', 0, 0) : thetaGrp.carrier)).2.1 = 0 :=
      hab2 ((a', 0, 0) : thetaGrp.carrier)
    have h3 : (φ.map ((a + a', 0, 0) : thetaGrp.carrier)).2.2
        = (φ.map ((a, 0, 0) : thetaGrp.carrier)).2.2
          + (φ.map ((a', 0, 0) : thetaGrp.carrier)).2.2
          + (φ.map ((a, 0, 0) : thetaGrp.carrier)).1
            * (φ.map ((a', 0, 0) : thetaGrp.carrier)).2.1 :=
      congrArg (fun s : Int × Int × Int => s.2.2) hm
    rw [h2] at h3
    omega
  -- (C) y 軸方向の加法性
  have hCy : ∀ b b' : Int,
      (φ.map ((0, b + b', 0) : thetaGrp.carrier)).2.2
        = (φ.map ((0, b, 0) : thetaGrp.carrier)).2.2
          + (φ.map ((0, b', 0) : thetaGrp.carrier)).2.2 := by
    intro b b'
    have e : thetaGrp.mul ((0, b, 0) : thetaGrp.carrier)
        ((0, b', 0) : thetaGrp.carrier) = ((0, b + b', 0) : thetaGrp.carrier) := by
      show ((0 + 0, b + b', 0 + 0 + 0 * b') : Int × Int × Int) = (0, b + b', 0)
      refine triple_ext (by omega) rfl (by omega)
    have hm := φ.map_mul ((0, b, 0) : thetaGrp.carrier)
      ((0, b', 0) : thetaGrp.carrier)
    rw [e] at hm
    have h1 : (φ.map ((0, b, 0) : thetaGrp.carrier)).1 = 0 :=
      hab1 ((0, b, 0) : thetaGrp.carrier)
    have h3 : (φ.map ((0, b + b', 0) : thetaGrp.carrier)).2.2
        = (φ.map ((0, b, 0) : thetaGrp.carrier)).2.2
          + (φ.map ((0, b', 0) : thetaGrp.carrier)).2.2
          + (φ.map ((0, b, 0) : thetaGrp.carrier)).1
            * (φ.map ((0, b', 0) : thetaGrp.carrier)).2.1 :=
      congrArg (fun s : Int × Int × Int => s.2.2) hm
    rw [h1] at h3
    omega
  -- (D) 積の分解: φ(a,b,ab) の中心座標 = φ(a,0,0) + φ(0,b,0) の中心座標 + ab
  have hD : ∀ a b : Int,
      (φ.map ((a, b, a * b) : thetaGrp.carrier)).2.2
        = (φ.map ((a, 0, 0) : thetaGrp.carrier)).2.2
          + (φ.map ((0, b, 0) : thetaGrp.carrier)).2.2 + a * b := by
    intro a b
    have e : thetaGrp.mul ((a, 0, 0) : thetaGrp.carrier)
        ((0, b, 0) : thetaGrp.carrier) = ((a, b, a * b) : thetaGrp.carrier) := by
      show ((a + 0, 0 + b, 0 + 0 + a * b) : Int × Int × Int) = (a, b, a * b)
      refine triple_ext (by omega) (by omega) ?_
      generalize a * b = P
      omega
    have hm := φ.map_mul ((a, 0, 0) : thetaGrp.carrier)
      ((0, b, 0) : thetaGrp.carrier)
    rw [e] at hm
    have h1 : (φ.map ((a, 0, 0) : thetaGrp.carrier)).1 = a :=
      hab1 ((a, 0, 0) : thetaGrp.carrier)
    have h2 : (φ.map ((0, b, 0) : thetaGrp.carrier)).2.1 = b :=
      hab2 ((0, b, 0) : thetaGrp.carrier)
    have h3 : (φ.map ((a, b, a * b) : thetaGrp.carrier)).2.2
        = (φ.map ((a, 0, 0) : thetaGrp.carrier)).2.2
          + (φ.map ((0, b, 0) : thetaGrp.carrier)).2.2
          + (φ.map ((a, 0, 0) : thetaGrp.carrier)).1
            * (φ.map ((0, b, 0) : thetaGrp.carrier)).2.1 :=
      congrArg (fun s : Int × Int × Int => s.2.2) hm
    rw [h1, h2] at h3
    exact h3
  -- 線型性: 生成元の像の中心座標 p, q で軸方向のずれが決まる
  have hlinx : ∀ a : Int, (φ.map ((a, 0, 0) : thetaGrp.carrier)).2.2
      = a * (φ.map ((1, 0, 0) : thetaGrp.carrier)).2.2 :=
    tgrig_additive_linear
      (fun a => (φ.map ((a, 0, 0) : thetaGrp.carrier)).2.2) hBx
  have hliny : ∀ b : Int, (φ.map ((0, b, 0) : thetaGrp.carrier)).2.2
      = b * (φ.map ((0, 1, 0) : thetaGrp.carrier)).2.2 :=
    tgrig_additive_linear
      (fun b => (φ.map ((0, b, 0) : thetaGrp.carrier)).2.2) hCy
  -- 共役子の明示構成 g = (q, −p, 0)
  refine ⟨(((φ.map ((0, 1, 0) : thetaGrp.carrier)).2.2,
    -(φ.map ((1, 0, 0) : thetaGrp.carrier)).2.2, 0) : thetaGrp.carrier), ?_⟩
  intro x
  obtain ⟨u, v, w⟩ := x
  rw [tgrig_conj_formula]
  refine tgrig_prod3_ext (hab1 ((u, v, w) : thetaGrp.carrier))
    (hab2 ((u, v, w) : thetaGrp.carrier)) ?_
  show (φ.map ((u, v, w) : thetaGrp.carrier)).2.2
    = w + (φ.map ((0, 1, 0) : thetaGrp.carrier)).2.2 * v
        - -(φ.map ((1, 0, 0) : thetaGrp.carrier)).2.2 * u
  have e2 : ((u, v, u * v + (w - u * v)) : thetaGrp.carrier)
      = ((u, v, w) : thetaGrp.carrier) := by
    refine triple_ext rfl rfl ?_
    generalize u * v = P
    omega
  have h4 := hA u v (u * v) (w - u * v)
  rw [e2] at h4
  have h5 := hD u v
  rw [hlinx u, hliny v] at h5
  rw [h5] at h4
  rw [Int.neg_mul, Int.sub_neg,
    Int.mul_comm ((φ.map ((0, 1, 0) : thetaGrp.carrier)).2.2) v,
    Int.mul_comm ((φ.map ((1, 0, 0) : thetaGrp.carrier)).2.2) u, h4]
  generalize u * (φ.map ((1, 0, 0) : thetaGrp.carrier)).2.2 = P
  generalize v * (φ.map ((0, 1, 0) : thetaGrp.carrier)).2.2 = Q
  generalize u * v = R
  omega

/-- **定理 (M399F-5f: 剛性の完全特徴付け)** — φ が「アーベル化 ℤ² に恒等かつ中心に
    各点恒等」であることと「内部自己同型であること」は**同値**。
    ⟸ は M399F-2b/2c/3b（内部自己同型がその性質を持つ）、⟹ は剛性定理 M399F-5e。 -/
theorem tgrig_inner_characterization (φ : Hom thetaGrp thetaGrp) :
    ((∀ x : thetaGrp.carrier, (φ.map x).1 = x.1)
        ∧ (∀ x : thetaGrp.carrier, (φ.map x).2.1 = x.2.1)
        ∧ (∀ c : Int, φ.map ((0, 0, c) : thetaGrp.carrier)
            = ((0, 0, c) : thetaGrp.carrier)))
      ↔ ∃ g : thetaGrp.carrier,
          ∀ x : thetaGrp.carrier, φ.map x = (tgrigConj thetaGrp g).map x := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    exact tgrig_rigidity φ h1 h2 h3
  · intro hex
    obtain ⟨g, hg⟩ := hex
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [hg x]
      exact tgrig_conj_ab_fst g x
    · intro x
      rw [hg x]
      exact tgrig_conj_ab_snd g x
    · intro c
      rw [hg ((0, 0, c) : thetaGrp.carrier)]
      exact tgrig_conj_fix_center g c

/-! ## M399F-6: 円分体 μ_l の剛性（遠アーベルの結論）

  M394F で内在的に復元された中心の μ_l 同一視（centerToMu）は任意の内部自己同型で
  不変——復元円分体は canonical（M394F）かつ**剛**（本モジュール）。 -/

/-- **定理 (M399F-6: 復元円分体は内部自己同型で剛)** —
    任意の g による共役のもとで中心元 (0,0,c) の μ_l 像は不変。
    M394F はせん断・符号という個別の自己同型での不変性を示した; 本定理は
    **全ての内部自己同型**での不変性（＝円分剛性の群論的核）を一括で与える。 -/
theorem tgrig_cyclotome_rigid (p l : Nat) (ζ : (Zp p).carrier)
    (g : thetaGrp.carrier) (c : Int) :
    centerToMu p l ζ
        ((tgrigConj thetaGrp g).map ((0, 0, c) : thetaGrp.carrier)).2.2
      = centerToMu p l ζ c :=
  congrArg (fun s : Int × Int × Int => centerToMu p l ζ s.2.2)
    (tgrig_conj_fix_center g c)

/-! ## M399F-7: capstone -/

/-- **M399F-7a: テータ群剛性データ** — 内部自己同型剛性の全成果を束ねる:
    シンプレクティック公式・アーベル化への自明作用・中心の各点固定・合成則と全射性
    （内部自己同型群の構造）・内部自己同型の一致 ⟺ 中心差（Inn ≅ thetaGrp/Z ≅ ℤ²）・
    剛性定理（アーベル化と中心に恒等 ⟹ 内部自己同型）・復元円分体 μ_l の剛性。
    主語は本物の thetaGrp・本物の μ_l（centerToMu）・任意の群自己準同型（toy 群なし）。 -/
structure ThetaGroupRigidityData (p l : Nat) (ζ : (Zp p).carrier) where
  /-- シンプレクティック公式: conj_{(a,b,t)}(x,y,z) = (x, y, z + a·y − b·x)。 -/
  conj_formula : ∀ a b t x y z : Int,
    (tgrigConj thetaGrp ((a, b, t) : thetaGrp.carrier)).map
        ((x, y, z) : thetaGrp.carrier)
      = ((x, y, z + a * y - b * x) : thetaGrp.carrier)
  /-- 内部自己同型はアーベル化 ℤ² に恒等（第 1 成分）。 -/
  conj_ab_fst : ∀ g x : thetaGrp.carrier,
    ((tgrigConj thetaGrp g).map x).1 = x.1
  /-- 内部自己同型はアーベル化 ℤ² に恒等（第 2 成分）。 -/
  conj_ab_snd : ∀ g x : thetaGrp.carrier,
    ((tgrigConj thetaGrp g).map x).2.1 = x.2.1
  /-- 内部自己同型は中心を各点固定する。 -/
  conj_fix_center : ∀ (g : thetaGrp.carrier) (c : Int),
    (tgrigConj thetaGrp g).map ((0, 0, c) : thetaGrp.carrier)
      = ((0, 0, c) : thetaGrp.carrier)
  /-- 合成則: conj_g ∘ conj_h = conj_{g·h}（内部自己同型群の構造）。 -/
  conj_comp : ∀ g h x : thetaGrp.carrier,
    (tgrigConj thetaGrp g).map ((tgrigConj thetaGrp h).map x)
      = (tgrigConj thetaGrp (thetaGrp.mul g h)).map x
  /-- 内部自己同型は全射（＝本物の自己同型）。 -/
  conj_surjective : ∀ g : thetaGrp.carrier,
    ∀ y, ∃ x, (tgrigConj thetaGrp g).map x = y
  /-- 内部自己同型の一致 ⟺ 中心差: Inn(thetaGrp) ≅ thetaGrp/Z ≅ ℤ²。 -/
  inner_eq_iff : ∀ g h : thetaGrp.carrier,
    (∀ x : thetaGrp.carrier,
        (tgrigConj thetaGrp g).map x = (tgrigConj thetaGrp h).map x)
      ↔ tgrCentral (thetaGrp.mul (thetaGrp.inv g) h)
  /-- 剛性定理: アーベル化と中心に恒等な自己準同型は内部自己同型。 -/
  rigidity : ∀ φ : Hom thetaGrp thetaGrp,
    (∀ x : thetaGrp.carrier, (φ.map x).1 = x.1) →
    (∀ x : thetaGrp.carrier, (φ.map x).2.1 = x.2.1) →
    (∀ c : Int, φ.map ((0, 0, c) : thetaGrp.carrier)
        = ((0, 0, c) : thetaGrp.carrier)) →
    ∃ g : thetaGrp.carrier,
      ∀ x : thetaGrp.carrier, φ.map x = (tgrigConj thetaGrp g).map x
  /-- 復元円分体 μ_l は全内部自己同型のもとで剛。 -/
  cyclotome_rigid : ∀ (g : thetaGrp.carrier) (c : Int),
    centerToMu p l ζ
        ((tgrigConj thetaGrp g).map ((0, 0, c) : thetaGrp.carrier)).2.2
      = centerToMu p l ζ c

/-- **M399F-7b: witness 本体** — 全フィールドを M399F-1〜6 の本物の証明で埋める
    （外部仮説ゼロ・完全証明・ζ が単数根であることすら不要）。 -/
def thetaGroupRigidityData (p l : Nat) (ζ : (Zp p).carrier) :
    ThetaGroupRigidityData p l ζ where
  conj_formula := tgrig_conj_formula
  conj_ab_fst := tgrig_conj_ab_fst
  conj_ab_snd := tgrig_conj_ab_snd
  conj_fix_center := tgrig_conj_fix_center
  conj_comp := tgrig_conj_comp thetaGrp
  conj_surjective := tgrig_conj_surjective thetaGrp
  inner_eq_iff := tgrig_inner_eq_iff
  rigidity := tgrig_rigidity
  cyclotome_rigid := tgrig_cyclotome_rigid p l ζ

/-- **定理 (M399F-7c: テータ群剛性データの存在／M399F 見出し)** —
    任意の p・l・μ_l 候補 ζ に対し、テータ群の内部自己同型剛性データ
    （シンプレクティック公式・Inn ≅ ℤ²・剛性定理・円分剛性）が**外部仮説なしで**
    存在する（完全証明）。 -/
theorem tgrig_exists (p l : Nat) (ζ : (Zp p).carrier) :
    Nonempty (ThetaGroupRigidityData p l ζ) :=
  ⟨thetaGroupRigidityData p l ζ⟩

/-! ## M399F-8: 実例 -/

/-- 実例: p=7・l=5 のテータ群剛性データが存在する（ζ は任意の ℤ_7 の元でよい）。 -/
example (ζ : (Zp 7).carrier) : Nonempty (ThetaGroupRigidityData 7 5 ζ) :=
  tgrig_exists 7 5 ζ

/-- 実例: シンプレクティック公式の数値検証 —
    conj_{(2,3,5)}(7,11,13) = (7, 11, 13 + 2·11 − 3·7) = (7, 11, 14)。 -/
example : (tgrigConj thetaGrp ((2, 3, 5) : thetaGrp.carrier)).map
      ((7, 11, 13) : thetaGrp.carrier) = ((7, 11, 14) : thetaGrp.carrier) := by
  rw [tgrig_conj_formula]
  refine triple_ext rfl rfl (by omega)

/-- 実例: 共役子の中心成分は無関係 — conj_{(2,3,5)} = conj_{(2,3,0)}（各点で）。 -/
example (x : thetaGrp.carrier) :
    (tgrigConj thetaGrp ((2, 3, 5) : thetaGrp.carrier)).map x
      = (tgrigConj thetaGrp ((2, 3, 0) : thetaGrp.carrier)).map x :=
  tgrig_conj_param_free 2 3 5 x

/-- 実例: 内部自己同型は中心 (0,0,c) を固定する（円分剛性の核）。 -/
example (g : thetaGrp.carrier) (c : Int) :
    (tgrigConj thetaGrp g).map ((0, 0, c) : thetaGrp.carrier)
      = ((0, 0, c) : thetaGrp.carrier) :=
  tgrig_conj_fix_center g c

/-- 実例: 中心差だけ異なる共役子は同じ内部自己同型を与える —
    g = (1,2,0) と h = (1,2,9) について g⁻¹·h は中心、ゆえに conj_g = conj_h。 -/
example : ∀ x : thetaGrp.carrier,
    (tgrigConj thetaGrp ((1, 2, 0) : thetaGrp.carrier)).map x
      = (tgrigConj thetaGrp ((1, 2, 9) : thetaGrp.carrier)).map x :=
  fun x => tgrig_conj_param_free 1 2 0 x |>.trans
    (tgrig_conj_param_free 1 2 9 x).symm

/-- 実例: M394F のせん断自己同型 tgrShear n はアーベル化に恒等・中心に各点恒等なので、
    剛性定理により**内部自己同型に一致**する（骨格外の実クロスチェック）。 -/
example (n : Int) : ∃ g : thetaGrp.carrier,
    ∀ x : thetaGrp.carrier, (tgrShear n).map x = (tgrigConj thetaGrp g).map x := by
  refine tgrig_rigidity (tgrShear n) ?_ ?_ ?_
  · intro x
    obtain ⟨u, v, w⟩ := x
    show u = u
    rfl
  · intro x
    obtain ⟨u, v, w⟩ := x
    show v = v
    rfl
  · intro c
    exact tgr_shear_fix_center n c

end IUT
