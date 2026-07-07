-- M394F ThetaGroupReconstruction [実・本物・柱A]
-- complete_pct 影響: 柱A で テータ群（離散 Heisenberg 群 thetaGrp）の中心 Z を「∀h で可換な元」という群論的述語だけから内在的に復元し（Z = {(0,0,c)} = 交換子部分群 [G,G] = μ_l の離散モデル）、任意の全射自己準同型（＝自己同型）がその中心を保つ関手性を完全証明——mono-anabelian「群から構造を復元する」方向の本物の SEED（中心 = μ_l は内在＝canonical）。
-- 正直な限定: 完全な mono-anabelian π₁^ét → 数体 の復元アルゴリズム（幾何的 tempered π₁^temp の slim 遠アーベル性・遠アーベル復元本体）は外部/後続。本モジュールは離散 Heisenberg 骨格 thetaGrp の中心の群論的特徴付けと自己同型不変性・μ_l 同期のみを扱う。

/-
  IUT/ThetaGroupReconstruction.lean — M394F [実／本物・柱A]
  分類: 実（テータ群の中心の群論的（内在的）復元＝mono-anabelian SEED）

  M384F (IUT/TemperedThetaCommutator.lean, prefix ttc) は離散 Heisenberg 群
  （テータ群 thetaGrp）の交換子 [g,h] が中心 {(0,0,∗)} に落ち、その中心座標が
  シンプレクティック形式 ω(g,h)=a·b′−a′·b に一致することを完全証明した。
  M389F (IUT/TemperedThetaOuterAction.lean, prefix ttoa) はその中心＝内部円分体 μ_l
  への G_K の外ガロア作用（円分指標 χ による捻り、スケール作用 ttoaScale）を本物で建設した。

  本モジュールは **mono-anabelian（遠アーベル）方向の実 SEED** を建設する:
  「群 + そのガロア作用から構造を内在的に復元する」。復元する対象は **中心 Z(thetaGrp)**。

  建設内容（すべて本物の Heisenberg 計算・toy 群なし）:
    * **中心の群論的（内在的）特徴付け（本丸）**: 群の中心を「任意の元と可換」という
      純群論的述語 `tgrCentral g := ∀ h, g·h = h·g` だけで定義し、
        tgrCentral g ↔ ∃ c, g = (0,0,c)
      を完全証明（M394F-2）。中心座標 (0,0,c) の軸が、群構造だけから内在的に
      復元される（幾何座標 (a,b) への言及なし）。
    * **中心 = 交換子部分群（両方 (0,0,∗) 軸）**: 交換子はすべて中心に属し（M394F-3a）、
      逆に任意の中心元 (0,0,c) は交換子 [(c,0,0),(0,1,0)] として実現される（M394F-3b）ので、
        tgrCentral g ↔ ∃ x y, g = [x,y]（M394F-3c）
      ——中心と交換子部分群が群論的に同一（ともに内在的に復元される）。
    * **自己同型は中心を保つ（関手性・canonical 性の核）**: 任意の全射自己準同型
      （＝自己同型）φ は中心を中心へ写す φ(Z) ⊆ Z（M394F-4）。ゆえに中心は
      群の自己同型のもとで canonical な不変量である。
    * **具体的自己同型の本物の建設**: せん断 `tgrShear n`(a,b,c)=(a,b,c+n·a)（M394F-5）と
      符号 `tgrNeg`(a,b,c)=(−a,−b,c)（M394F-6）は本物の群自己同型（準同型・全射・
      逆写像あり）であり、中心を **各点固定** する。これらが M394F-4 の全射条件を
      満たす具体クラス。
    * **復元中心 ≅ μ_l は canonical**: 中心座標の M124F/M384F 同期写像 centerToMu 像は
      自己同型（せん断・符号）で不変（M394F-7）——内在的に復元された中心の μ_l 同一視が
      自己同型に依らず canonical であることの本物の内容。
    * **外ガロア作用は復元中心に降下（canonical）**: M389F の外ガロア作用（スケール
      作用 ttoaScale e）は復元中心 {(0,0,∗)} を中心へ写し、中心座標を e 倍する
      （M394F-8）——復元された中心の上で M389F の χ 捻りが well-defined。

  意義: mono-anabelian の核心「群論的データだけから構造を取り出す」の**最小だが本物の
  一歩**。中心（＝内部円分体 μ_l の座）は補助的な座標選択ではなく、群の可換性という
  純群論的性質だけから内在的に復元され（tgr_central_iff）、自己同型のもとで canonical
  （tgr_surjEndo_preserves_central）であることを完全証明する。

  正直な限定: これは復元の **SEED**（中心が内在的）であって、完全な mono-anabelian
  アルゴリズム（幾何的 tempered π₁^temp Δ^temp の slim 遠アーベル性・π₁^ét からの数体
  の遠アーベル復元本体・Mochizuki の復元アルゴリズム全体）ではない。本モジュールは
  離散 Heisenberg 骨格 thetaGrp の中心の群論的特徴付け・自己同型不変性・μ_l 同期のみを
  扱う。中心が μ_l と同一視される点は M124F centerToMu を経由する（外部の解析的入力なし）。
  全て選択公理不使用（propext / Quot.sound のみ）。
-/
import IUT.TemperedThetaOuterAction

namespace IUT

/-! ## M394F-1: 中心の群論的（内在的）述語

  中心を「任意の元と可換」という純群論的性質だけで定義する。幾何座標 (a,b) や
  シンプレクティック形式には一切言及しない——群構造そのものからの内在的定義。 -/

/-- **M394F-1a: 中心性の群論的述語** — g が任意の h と可換: g·h = h·g。
    群の演算だけを使う内在的定義（mono-anabelian の主語）。 -/
def tgrCentral (g : thetaGrp.carrier) : Prop :=
  ∀ h : thetaGrp.carrier, thetaGrp.mul g h = thetaGrp.mul h g

/-- **定理 (M394F-1b: 中心座標は真に中心)** — (0,0,c) は任意の元と可換。
    Heisenberg 群の第 3 成分軸が中心をなすことの本物の整数証明。 -/
theorem tgr_center_central (c : Int) : tgrCentral ((0, 0, c) : thetaGrp.carrier) := by
  intro g
  obtain ⟨a, b, c'⟩ := g
  show ((0 + a, 0 + b, c + c' + 0 * b) : Int × Int × Int)
    = (a + 0, b + 0, c' + c + a * 0)
  refine triple_ext (by omega) (by omega) (by omega)

/-! ## M394F-2: 中心の群論的特徴付け（本丸）

  中心元は必ず (0,0,c) の形をとる: 群論的中心性 → 幾何座標が 0。逆と合わせ
  Z = {(0,0,∗)} が群構造だけから内在的に復元される。 -/

/-- **定理 (M394F-2a: 中心性 → 幾何座標が 0)** — g=(a,b,c) が中心なら a=0 かつ b=0。
    証明は標準生成元 (1,0,0),(0,1,0) との可換性を第 3 成分で読む: 可換条件の
    第 3 成分の差がちょうど b（生成元 x との）と a（生成元 y との）を強制する。 -/
theorem tgr_central_forward (a b c : Int)
    (h : tgrCentral ((a, b, c) : thetaGrp.carrier)) : a = 0 ∧ b = 0 := by
  have h1 := h (1, 0, 0)
  have h2 := h (0, 1, 0)
  have hb : (c + 0 + a * 0 : Int) = 0 + c + 1 * b :=
    congrArg (fun t : Int × Int × Int => t.2.2) h1
  have ha : (c + 0 + a * 1 : Int) = 0 + c + 0 * b :=
    congrArg (fun t : Int × Int × Int => t.2.2) h2
  exact ⟨by omega, by omega⟩

/-- **定理 (M394F-2b: 中心の内在的特徴付け／本丸)** — 群論的中心性は (0,0,∗) 軸に等しい:
      tgrCentral g ↔ ∃ c, g = (0,0,c)。
    「任意の元と可換」という純群論的性質だけから、中心座標軸（内部円分体 μ_l の座）が
    内在的に復元される。mono-anabelian「群から構造を取り出す」方向の本物の核。 -/
theorem tgr_central_iff (g : thetaGrp.carrier) :
    tgrCentral g ↔ ∃ c : Int, g = ((0, 0, c) : thetaGrp.carrier) := by
  constructor
  · intro hc
    obtain ⟨a, b, c⟩ := g
    obtain ⟨ha, hb⟩ := tgr_central_forward a b c hc
    exact ⟨c, by rw [ha, hb]⟩
  · intro hex
    obtain ⟨c, hc⟩ := hex
    rw [hc]
    exact tgr_center_central c

/-! ## M394F-3: 中心 = 交換子部分群（両方 (0,0,∗) 軸）

  交換子はすべて中心に属し、逆に任意の中心元は交換子として実現される。ゆえに
  中心と交換子部分群は群論的に同一——ともに内在的に復元される。 -/

/-- **定理 (M394F-3a: 交換子は中心に属す)** — [g,h] は群論的中心元。
    M384F/M11 theta_comm で交換子が (0,0,ω) に落ちる。 -/
theorem tgr_commutator_central (g h : thetaGrp.carrier) :
    tgrCentral (thetaGrp.comm g h) := by
  obtain ⟨a, b, c⟩ := g
  obtain ⟨a', b', c'⟩ := h
  rw [theta_comm]
  exact tgr_center_central (a * b' - a' * b)

/-- **定理 (M394F-3b: 中心元は交換子として実現される)** — (0,0,c) = [(c,0,0),(0,1,0)]。
    シンプレクティック形式 c·1−0·0 = c ゆえ、中心座標軸のすべての点が交換子の像。 -/
theorem tgr_central_is_commutator (c : Int) :
    ((0, 0, c) : thetaGrp.carrier)
      = thetaGrp.comm ((c, 0, 0) : Int × Int × Int) (0, 1, 0) := by
  rw [theta_comm]
  refine triple_ext rfl rfl (by omega)

/-- **定理 (M394F-3c: 中心 = 交換子部分群)** — 群論的中心性は交換子であることに等しい:
      tgrCentral g ↔ ∃ x y, g = [x,y]。
    中心（M394F-2b で内在的に復元）と交換子部分群がともに (0,0,∗) 軸で一致する
    ことの群論的完全証明——両者が同一の内在的対象であることの本物の内容。 -/
theorem tgr_central_iff_commutator (g : thetaGrp.carrier) :
    tgrCentral g ↔ ∃ x y : thetaGrp.carrier, g = thetaGrp.comm x y := by
  constructor
  · intro hc
    obtain ⟨c, hc0⟩ := (tgr_central_iff g).mp hc
    refine ⟨(c, 0, 0), (0, 1, 0), ?_⟩
    rw [hc0]
    exact tgr_central_is_commutator c
  · intro hex
    obtain ⟨x, y, hxy⟩ := hex
    rw [hxy]
    exact tgr_commutator_central x y

/-! ## M394F-4: 自己同型は中心を保つ（関手性・canonical 性の核）

  任意の全射自己準同型（＝自己同型）は中心を中心へ写す。ゆえに中心は群の自己同型の
  もとで canonical な不変量である（mono-anabelian の関手性）。 -/

/-- **定理 (M394F-4: 全射自己準同型は中心を保つ／関手性)** — φ が全射準同型なら
    中心元 z の像 φ(z) も中心: φ(Z) ⊆ Z。
    証明は純群論的: 任意の k = φ(h)（全射）に対し φ(z)·k = φ(z·h) = φ(h·z) = k·φ(z)。
    中心が「群から構造を復元する」際に自己同型のもとで canonical であることの核。 -/
theorem tgr_surjEndo_preserves_central (f : Hom thetaGrp thetaGrp)
    (hsurj : ∀ y, ∃ x, f.map x = y) {z : thetaGrp.carrier}
    (hz : tgrCentral z) : tgrCentral (f.map z) := by
  intro k
  obtain ⟨h, hh⟩ := hsurj k
  rw [← hh, ← f.map_mul, ← f.map_mul, hz h]

/-! ## M394F-5: 具体的自己同型（せん断）の本物の建設

  せん断 tgrShear n (a,b,c)=(a,b,c+n·a) は本物の群自己同型（準同型・逆写像 tgrShear(−n)
  あり）で、中心を各点固定する。M394F-4 の全射条件を満たす具体クラス。 -/

/-- **M394F-5a: せん断準同型** tgrShear n (a,b,c) = (a,b,c+n·a)。中心方向へのせん断
    （幾何座標 (a,b) を保ち、中心座標を n·a だけずらす）。本物の群準同型。 -/
def tgrShear (n : Int) : Hom thetaGrp thetaGrp where
  map := fun x => (x.1, x.2.1, x.2.2 + n * x.1)
  map_mul := by
    intro x y
    obtain ⟨a, b, c⟩ := x
    obtain ⟨a', b', c'⟩ := y
    show ((a + a', b + b', c + c' + a * b' + n * (a + a')) : Int × Int × Int)
      = (a + a', b + b', (c + n * a) + (c' + n * a') + a * b')
    refine triple_ext rfl rfl ?_
    rw [Int.mul_add]
    generalize a * b' = P
    generalize n * a = Q
    generalize n * a' = R
    omega

/-- **定理 (M394F-5b: せん断の左逆)** — tgrShear(−n) ∘ tgrShear n = id。 -/
theorem tgr_shear_left_inv (n : Int) (x : thetaGrp.carrier) :
    (tgrShear (-n)).map ((tgrShear n).map x) = x := by
  obtain ⟨a, b, c⟩ := x
  show ((a, b, (c + n * a) + (-n) * a) : Int × Int × Int) = (a, b, c)
  refine triple_ext rfl rfl ?_
  rw [Int.neg_mul]
  generalize n * a = P
  omega

/-- **定理 (M394F-5c: せん断は全射)** — 逆写像 tgrShear(−n) から。M394F-4 の適用条件。 -/
theorem tgr_shear_surjective (n : Int) :
    ∀ y, ∃ x, (tgrShear n).map x = y := by
  intro y
  refine ⟨(tgrShear (-n)).map y, ?_⟩
  obtain ⟨a, b, c⟩ := y
  show ((a, b, (c + (-n) * a) + n * a) : Int × Int × Int) = (a, b, c)
  refine triple_ext rfl rfl ?_
  rw [Int.neg_mul]
  generalize n * a = P
  omega

/-- **定理 (M394F-5d: せん断は中心を各点固定)** — tgrShear n (0,0,c) = (0,0,c)。
    a=0 ゆえ n·a=0。復元中心が具体自己同型で不変であることの本物の内容。 -/
theorem tgr_shear_fix_center (n c : Int) :
    (tgrShear n).map ((0, 0, c) : thetaGrp.carrier) = ((0, 0, c) : thetaGrp.carrier) := by
  show ((0, 0, c + n * 0) : Int × Int × Int) = (0, 0, c)
  refine triple_ext rfl rfl (by omega)

/-- **定理 (M394F-5e: せん断は中心を保つ／M394F-4 の具体化)** — せん断は中心を中心へ写す。 -/
theorem tgr_shear_preserves_central (n : Int) {z : thetaGrp.carrier}
    (hz : tgrCentral z) : tgrCentral ((tgrShear n).map z) :=
  tgr_surjEndo_preserves_central (tgrShear n) (tgr_shear_surjective n) hz

/-! ## M394F-6: 具体的自己同型（符号）の本物の建設

  符号 tgrNeg (a,b,c)=(−a,−b,c) は本物の群自己同型（involution）で中心を各点固定する。 -/

/-- **M394F-6a: 符号準同型** tgrNeg (a,b,c) = (−a,−b,c)。幾何座標を反転し中心を保つ。
    シンプレクティック形式 (−a)(−b′)=ab′ ゆえ準同型。 -/
def tgrNeg : Hom thetaGrp thetaGrp where
  map := fun x => (-x.1, -x.2.1, x.2.2)
  map_mul := by
    intro x y
    obtain ⟨a, b, c⟩ := x
    obtain ⟨a', b', c'⟩ := y
    show ((-(a + a'), -(b + b'), c + c' + a * b') : Int × Int × Int)
      = (-a + -a', -b + -b', c + c' + (-a) * (-b'))
    refine triple_ext (by omega) (by omega) ?_
    rw [Int.neg_mul_neg]

/-- **定理 (M394F-6b: 符号は involution)** — tgrNeg ∘ tgrNeg = id。 -/
theorem tgr_neg_involution (x : thetaGrp.carrier) :
    tgrNeg.map (tgrNeg.map x) = x := by
  obtain ⟨a, b, c⟩ := x
  show ((-(-a), -(-b), c) : Int × Int × Int) = (a, b, c)
  refine triple_ext (by omega) (by omega) rfl

/-- **定理 (M394F-6c: 符号は全射)** — involution ゆえ。 -/
theorem tgr_neg_surjective : ∀ y, ∃ x, tgrNeg.map x = y :=
  fun y => ⟨tgrNeg.map y, tgr_neg_involution y⟩

/-- **定理 (M394F-6d: 符号は中心を各点固定)** — tgrNeg (0,0,c) = (0,0,c)。 -/
theorem tgr_neg_fix_center (c : Int) :
    tgrNeg.map ((0, 0, c) : thetaGrp.carrier) = ((0, 0, c) : thetaGrp.carrier) := by
  show ((-0, -0, c) : Int × Int × Int) = (0, 0, c)
  refine triple_ext (by omega) (by omega) rfl

/-- **定理 (M394F-6e: 符号は中心を保つ／M394F-4 の具体化)**。 -/
theorem tgr_neg_preserves_central {z : thetaGrp.carrier}
    (hz : tgrCentral z) : tgrCentral (tgrNeg.map z) :=
  tgr_surjEndo_preserves_central tgrNeg tgr_neg_surjective hz

/-! ## M394F-7: 復元中心 ≅ μ_l は canonical（centerToMu が自己同型不変）

  内在的に復元された中心の μ_l 同一視（M124F/M384F centerToMu）は具体自己同型で不変。 -/

/-- **定理 (M394F-7a: せん断のもとで μ_l 像が不変)** —
    centerToMu(せん断した中心元の中心座標) = centerToMu(元の中心座標)。
    復元中心 ≅ μ_l がせん断自己同型に依らず canonical であることの本物の内容。 -/
theorem tgr_shear_centerToMu_invariant (p l : Nat) (ζ : (Zp p).carrier)
    (n c : Int) :
    centerToMu p l ζ ((tgrShear n).map ((0, 0, c) : thetaGrp.carrier)).2.2
      = centerToMu p l ζ c := by
  rw [tgr_shear_fix_center]

/-- **定理 (M394F-7b: 符号のもとで μ_l 像が不変)** — 同上（符号自己同型版）。 -/
theorem tgr_neg_centerToMu_invariant (p l : Nat) (ζ : (Zp p).carrier) (c : Int) :
    centerToMu p l ζ (tgrNeg.map ((0, 0, c) : thetaGrp.carrier)).2.2
      = centerToMu p l ζ c := by
  rw [tgr_neg_fix_center]

/-! ## M394F-8: 外ガロア作用は復元中心に降下（canonical）

  M389F の外ガロア作用（スケール作用 ttoaScale e）は復元中心 {(0,0,∗)} を中心へ写し、
  中心座標を e 倍する。復元された中心の上で M389F の χ 捻りが well-defined。 -/

/-- **定理 (M394F-8: 外ガロア（スケール）作用は復元中心に降下)** —
    ttoaScale e (0,0,c) は再び群論的中心元であり、その中心座標は e·c。
    M389F の χ 捻り（外ガロア作用）が、群論的に復元された中心の上で canonical に
    作用することの本物の内容（中心が内在的ゆえ χ 捻りも well-defined）。 -/
theorem tgr_outer_action_on_center (e c : Int) :
    tgrCentral (ttoaScale e ((0, 0, c) : thetaGrp.carrier))
      ∧ (ttoaScale e ((0, 0, c) : thetaGrp.carrier)).2.2 = e * c := by
  refine ⟨?_, rfl⟩
  show tgrCentral ((0, 0, e * c) : thetaGrp.carrier)
  exact tgr_center_central (e * c)

/-! ## M394F-9: capstone -/

/-- **M394F-9a: テータ群中心復元データ** — 離散 Heisenberg 群 thetaGrp の中心を群論的
    （内在的）に復元する mono-anabelian SEED を束ねる:
    中心の群論的特徴付け（tgrCentral g ↔ ∃c, g=(0,0,c)）・中心 = 交換子部分群
    （tgrCentral g ↔ ∃x y, g=[x,y]）・全射自己準同型が中心を保つ関手性・
    具体自己同型（せん断・符号）が中心を各点固定・復元中心の μ_l 同一視（centerToMu）が
    自己同型不変・外ガロア（スケール）作用が復元中心に降下。
    主語は本物の thetaGrp・本物の μ_l（centerToMu）・本物の自己同型（toy 群なし）。 -/
structure ThetaGroupReconstructionData (p l : Nat) (ζ : (Zp p).carrier) where
  /-- 中心座標は真に中心。 -/
  center_central : ∀ c : Int, tgrCentral ((0, 0, c) : thetaGrp.carrier)
  /-- 中心の内在的特徴付け: 群論的中心性 = (0,0,∗) 軸。 -/
  central_iff : ∀ g : thetaGrp.carrier,
    tgrCentral g ↔ ∃ c : Int, g = ((0, 0, c) : thetaGrp.carrier)
  /-- 交換子は中心に属す。 -/
  commutator_central : ∀ g h : thetaGrp.carrier, tgrCentral (thetaGrp.comm g h)
  /-- 中心元は交換子として実現される。 -/
  central_is_commutator : ∀ c : Int,
    ((0, 0, c) : thetaGrp.carrier)
      = thetaGrp.comm ((c, 0, 0) : Int × Int × Int) (0, 1, 0)
  /-- 中心 = 交換子部分群（群論的同一）。 -/
  central_iff_commutator : ∀ g : thetaGrp.carrier,
    tgrCentral g ↔ ∃ x y : thetaGrp.carrier, g = thetaGrp.comm x y
  /-- 全射自己準同型は中心を保つ（関手性）。 -/
  surjEndo_preserves : ∀ (f : Hom thetaGrp thetaGrp),
    (∀ y, ∃ x, f.map x = y) → ∀ z : thetaGrp.carrier,
      tgrCentral z → tgrCentral (f.map z)
  /-- せん断自己同型は全射。 -/
  shear_surjective : ∀ (n : Int), ∀ y, ∃ x, (tgrShear n).map x = y
  /-- せん断自己同型は中心を各点固定。 -/
  shear_fix_center : ∀ (n c : Int),
    (tgrShear n).map ((0, 0, c) : thetaGrp.carrier) = ((0, 0, c) : thetaGrp.carrier)
  /-- 符号自己同型は involution（全射）。 -/
  neg_involution : ∀ x : thetaGrp.carrier, tgrNeg.map (tgrNeg.map x) = x
  /-- 符号自己同型は中心を各点固定。 -/
  neg_fix_center : ∀ c : Int,
    tgrNeg.map ((0, 0, c) : thetaGrp.carrier) = ((0, 0, c) : thetaGrp.carrier)
  /-- 復元中心の μ_l 同一視はせん断で不変（canonical）。 -/
  shear_mu_invariant : ∀ (n c : Int),
    centerToMu p l ζ ((tgrShear n).map ((0, 0, c) : thetaGrp.carrier)).2.2
      = centerToMu p l ζ c
  /-- 復元中心の μ_l 同一視は符号で不変（canonical）。 -/
  neg_mu_invariant : ∀ c : Int,
    centerToMu p l ζ (tgrNeg.map ((0, 0, c) : thetaGrp.carrier)).2.2
      = centerToMu p l ζ c
  /-- 外ガロア（スケール）作用は復元中心に降下し中心座標を e 倍。 -/
  outer_action_on_center : ∀ e c : Int,
    tgrCentral (ttoaScale e ((0, 0, c) : thetaGrp.carrier))
      ∧ (ttoaScale e ((0, 0, c) : thetaGrp.carrier)).2.2 = e * c

/-- **M394F-9b: witness 本体** — 全フィールドを M394F-1〜8 の本物の証明で埋める
    （外部仮説ゼロ・完全証明・ζ が単数根であることすら不要）。 -/
def thetaGroupReconstructionData (p l : Nat) (ζ : (Zp p).carrier) :
    ThetaGroupReconstructionData p l ζ where
  center_central := tgr_center_central
  central_iff := tgr_central_iff
  commutator_central := tgr_commutator_central
  central_is_commutator := tgr_central_is_commutator
  central_iff_commutator := tgr_central_iff_commutator
  surjEndo_preserves := fun f hsurj z hz =>
    tgr_surjEndo_preserves_central f hsurj hz
  shear_surjective := tgr_shear_surjective
  shear_fix_center := tgr_shear_fix_center
  neg_involution := tgr_neg_involution
  neg_fix_center := tgr_neg_fix_center
  shear_mu_invariant := tgr_shear_centerToMu_invariant p l ζ
  neg_mu_invariant := tgr_neg_centerToMu_invariant p l ζ
  outer_action_on_center := tgr_outer_action_on_center

/-- **定理 (M394F-9c: テータ群中心復元データの存在／M394F 見出し)** —
    任意の p・l・μ_l 候補 ζ が与えられれば、離散 Heisenberg 群 thetaGrp の中心を
    群論的（内在的）に復元する mono-anabelian SEED データが**外部仮説なしで**存在する
    （完全証明）。中心の群論的特徴付け・中心 = 交換子部分群・自己同型不変性・μ_l 同期を束ねる。 -/
theorem tgr_exists (p l : Nat) (ζ : (Zp p).carrier) :
    Nonempty (ThetaGroupReconstructionData p l ζ) :=
  ⟨thetaGroupReconstructionData p l ζ⟩

/-! ## M394F-10: 実例 -/

/-- 実例: p=7・l=5 のテータ群中心復元データが存在する（ζ は任意の ℤ_7 の元でよい）。 -/
example (ζ : (Zp 7).carrier) : Nonempty (ThetaGroupReconstructionData 7 5 ζ) :=
  tgr_exists 7 5 ζ

/-- 実例: 中心の内在的特徴付け — g が「任意の元と可換」なのは g が (0,0,c) の形のときに限る。 -/
example (g : thetaGrp.carrier) :
    tgrCentral g ↔ ∃ c : Int, g = ((0, 0, c) : thetaGrp.carrier) :=
  tgr_central_iff g

/-- 実例: 中心 = 交換子部分群 — 中心元であることと交換子であることは同値。 -/
example (g : thetaGrp.carrier) :
    tgrCentral g ↔ ∃ x y : thetaGrp.carrier, g = thetaGrp.comm x y :=
  tgr_central_iff_commutator g

/-- 実例: 具体的中心元 (0,0,3) = 交換子 [(3,0,0),(0,1,0)]。 -/
example : ((0, 0, 3) : thetaGrp.carrier)
    = thetaGrp.comm ((3, 0, 0) : Int × Int × Int) (0, 1, 0) :=
  tgr_central_is_commutator 3

/-- 実例: せん断自己同型 tgrShear 5 は中心を保つ（関手性の具体化）。 -/
example {z : thetaGrp.carrier} (hz : tgrCentral z) :
    tgrCentral ((tgrShear 5).map z) :=
  tgr_shear_preserves_central 5 hz

/-- 実例: 符号自己同型 tgrNeg は中心 (0,0,c) を固定（復元中心の canonical 性）。 -/
example (c : Int) :
    tgrNeg.map ((0, 0, c) : thetaGrp.carrier) = ((0, 0, c) : thetaGrp.carrier) :=
  tgr_neg_fix_center c

/-- 実例: 外ガロア作用（e=3）は復元中心 (0,0,c) を中心へ写し中心座標を 3 倍する。 -/
example (c : Int) :
    tgrCentral (ttoaScale 3 ((0, 0, c) : thetaGrp.carrier))
      ∧ (ttoaScale 3 ((0, 0, c) : thetaGrp.carrier)).2.2 = 3 * c :=
  tgr_outer_action_on_center 3 c

end IUT
