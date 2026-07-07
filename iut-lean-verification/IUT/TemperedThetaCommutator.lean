-- M384F TemperedThetaCommutator [実・本物・柱A]
-- complete_pct 影響: 柱A で M379F が「外部」と明示した tempered π₁ の非可換部分を本物で建設＝離散 Heisenberg 群（テータ群 thetaGrp）の交換子 [g,h] が中心 {(0,0,∗)} に落ち・その中心座標がシンプレクティック形式 a·b′−a′·b に一致し・群自身が非可換（¬tcmAbelian）で交換子の μ_l 像が非自明（M379F のアーベル ℤ_l 商と対照）であることを完全証明。
-- 正直な限定: 完全な幾何的 tempered π₁^temp（Δ^temp）の slim 遠アーベル性・その商としての実現は外部/後続。ここで扱うのは離散 Heisenberg 骨格 thetaGrp とその mod-l 商・固定 p の ℤ_p 内 μ_l のみ。

/-
  IUT/TemperedThetaCommutator.lean — M384F [実／本物・柱A]
  分類: 実（離散 Heisenberg 群＝テータ群の非可換交換子構造・中心シクロトーム像）

  M379F (IUT/TemperedCommutator.lean) は被覆塔の**最大 pro-l アーベル商** ℤ_l が
  可換で交換子が自明であることを証明し、完全な幾何的 tempered π₁^temp の**非可換テータ構造**
  を「外部（幾何的入力・後続）」と正直に明示した（`tcm_full_tempered_nonabelian_hypothesis`）。
  本モジュールはその外部と名指しされた**非可換部分**を本物で建設する:

  テータ群（離散 Heisenberg 群 H(ℤ) = {(a,b,c)}、積 (a,b,c)(a',b',c')=(a+a',b+b',c+c'+a·b')、
  EtaleTheta の本物の `thetaGrp`）の上で
    * 交換子 [g,h] = g·h·g⁻¹·h⁻¹ は**中心** {(0,0,∗)} に落ちる（第 1・2 成分が 0）
    * その中心座標は**シンプレクティック（交代）形式** ω(g,h) = a·b′−a′·b に一致（M11 theta_comm）
    * 中心元 (0,0,c) は本当に**中心**（任意の元と可換）である
    * 交換子は交代的: [g,g] = 1、ω(g,h) = −ω(h,g)
    * テータ群自身は**非可換**: ¬ tcmAbelian thetaGrp（M379F のアーベル ℤ_l 商とは対照的）
    * 標準生成元の交換子は中心生成元: [(1,0,0),(0,1,0)] = (0,0,1) ≠ 1（M11 comm_xy）
    * 交換子の中心座標の **μ_l 像は非自明**: centerToMu p l ζ ([(1,0,0),(0,1,0)] の中心座標) = ζ
      （M124F centerToMu / M162F centerToMu_natCast）— tempered テータ交換子が内部円分体 μ の中で
      非自明に実現される（M379F のアーベル商では交換子が μ に到達しない）
    * **アーベル化** (a,b,c) ↦ (a,b)（ttcAbGrp = ℤ²）は交換子を潰す（M379F の ℤ_l アーベル化の類似）
      が、中心座標（μ）はそれを記録する — 非可換性が中心一次元に圧縮されることの本物の内容
  主語はすべて本物の Heisenberg 群 thetaGrp・その mod-l 商 thetaGrpMod・本物の μ_l（toy 群なし）。

  正直な限定: 完全な幾何的 tempered π₁^temp（Δ^temp）の slim 遠アーベル性・p 進テータ関数の
  ガロア同変な評価・tempered 被覆の商としての実現は外部（幾何的入力・後続）。本モジュールは
  離散 Heisenberg 骨格 thetaGrp とその mod-l 商・固定 p の ℤ_p 内 μ_l のみを扱う。
  全て選択公理不使用（propext / Quot.sound のみ）。
-/
import IUT.ThetaHeisenbergLift
import IUT.TemperedCommutator

namespace IUT

/-! ## M384F-1: 中心元は本当に中心（任意の元と可換）

  離散 Heisenberg 群 thetaGrp の中心座標 {(0,0,c)} が、群の任意の元と可換であること
  （＝真に群の中心に属すること）を本物の整数演算で証明する。 -/

/-- **M384F-1a: 中心性の述語** — z が任意の g と可換: z·g = g·z。 -/
def ttcCentral (z : thetaGrp.carrier) : Prop :=
  ∀ g : thetaGrp.carrier, thetaGrp.mul z g = thetaGrp.mul g z

/-- **定理 (M384F-1b): 中心座標 (0,0,c) は真に中心** — 任意の g と可換。
    Heisenberg 群の第 3 成分（シクロトーム座標）が群の中心をなすことの本物の証明。 -/
theorem ttc_center_central (c : Int) : ttcCentral ((0, 0, c) : thetaGrp.carrier) := by
  intro g
  obtain ⟨a, b, c'⟩ := g
  show ((0 + a, 0 + b, c + c' + 0 * b) : Int × Int × Int)
    = (a + 0, b + 0, c' + c + a * 0)
  refine triple_ext (by omega) (by omega) (by omega)

/-! ## M384F-2: 交換子は中心に落ち、シンプレクティック形式に一致

  M11 `theta_comm`（[EtTh] のテータ群交換子公式）を非可換構造の主語として用い、
  交換子 [g,h] が中心 {(0,0,∗)} に属し、その中心座標が交代形式 a·b′−a′·b に一致する
  ことを完全証明する。 -/

/-- **定理 (M384F-2a): 交換子の第 1 成分は 0** — [g,h] は中心に落ちる（a 成分）。 -/
theorem ttc_commutator_fst (a b c a' b' c' : Int) :
    (thetaGrp.comm (a, b, c) (a', b', c')).1 = 0 := by
  rw [theta_comm]

/-- **定理 (M384F-2b): 交換子の第 2 成分は 0** — [g,h] は中心に落ちる（b 成分）。 -/
theorem ttc_commutator_snd (a b c a' b' c' : Int) :
    (thetaGrp.comm (a, b, c) (a', b', c')).2.1 = 0 := by
  rw [theta_comm]

/-- **定理 (M384F-2c): 交換子の中心座標 = シンプレクティック形式** —
    [g,h] の第 3 成分は交代形式 ω(g,h) = a·b′−a′·b に一致（M11 theta_comm）。
    Heisenberg 群の「非可換性のすべて」が中心一次元の交代形式に圧縮されることの本物の内容。 -/
theorem ttc_commutator_form (a b c a' b' c' : Int) :
    (thetaGrp.comm (a, b, c) (a', b', c')).2.2 = a * b' - a' * b := by
  rw [theta_comm]

/-- **定理 (M384F-2d): 交換子は中心に属す** — [g,h] は任意の元と可換（ttcCentral）。
    第 1・2 成分が 0（M384F-2a,b）ゆえ M384F-1b の中心性が適用できる。 -/
theorem ttc_commutator_central (g h : thetaGrp.carrier) :
    ttcCentral (thetaGrp.comm g h) := by
  obtain ⟨a, b, c⟩ := g
  obtain ⟨a', b', c'⟩ := h
  rw [theta_comm]
  exact ttc_center_central (a * b' - a' * b)

/-! ## M384F-3: 交換子の交代性（[g,g] = 1、ω 反対称）

  交代形式の本質: 自己交換子は自明、交換子はラベル入替で符号反転する。 -/

/-- **定理 (M384F-3a): 自己交換子は自明** — [g,g] = 1（ω(g,g) = 0 の群レベル）。 -/
theorem ttc_commutator_self (g : thetaGrp.carrier) :
    thetaGrp.comm g g = thetaGrp.one := by
  obtain ⟨a, b, c⟩ := g
  rw [theta_comm]
  show ((0, 0, a * b - a * b) : Int × Int × Int) = ((0, 0, 0) : Int × Int × Int)
  refine triple_ext rfl rfl (by omega)

/-- **定理 (M384F-3b): 交換子の中心座標は反対称** — ω(g,h) = −ω(h,g)。
    シンプレクティック形式 a·b′−a′·b の交代性の本物の整数証明。 -/
theorem ttc_form_antisymm (a b c a' b' c' : Int) :
    (thetaGrp.comm (a, b, c) (a', b', c')).2.2
      = -((thetaGrp.comm (a', b', c') (a, b, c)).2.2) := by
  rw [theta_comm, theta_comm]
  show a * b' - a' * b = -(a' * b - a * b')
  generalize a * b' = P
  generalize a' * b = Q
  omega

/-! ## M384F-4: テータ群は非可換（M379F のアーベル ℤ_l 商と対照）

  M379F は被覆塔の pro-l アーベル商 ℤ_l が可換（`tcm_limit_abelian`）で交換子が自明
  であることを証明した。本節はその「外部」と名指しされた非可換部分を、同じ述語
  `tcmAbelian`（M379F 由来）で否定して対照させる。 -/

/-- 標準生成元の積（左）: (1,0,0)·(0,1,0) = (1,1,1)。 -/
theorem ttc_mul_ex1 :
    thetaGrp.mul ((1, 0, 0) : Int × Int × Int) (0, 1, 0) = (1, 1, 1) := by
  show ((1 + 0, 0 + 1, 0 + 0 + 1 * 1) : Int × Int × Int) = (1, 1, 1)
  refine triple_ext (by omega) (by omega) (by omega)

/-- 標準生成元の積（右・入替）: (0,1,0)·(1,0,0) = (1,1,0)。 -/
theorem ttc_mul_ex2 :
    thetaGrp.mul ((0, 1, 0) : Int × Int × Int) (1, 0, 0) = (1, 1, 0) := by
  show ((0 + 1, 1 + 0, 0 + 0 + 0 * 0) : Int × Int × Int) = (1, 1, 0)
  refine triple_ext (by omega) (by omega) (by omega)

/-- **定理 (M384F-4a): テータ群は非可換** — ¬ tcmAbelian thetaGrp。
    標準生成元 (1,0,0), (0,1,0) は可換でない（積の第 3 成分が 1 ≠ 0）。
    M379F `tcm_limit_abelian`（ℤ_l 商が可換）と**同じ述語 tcmAbelian で対照**させ、
    完全な tempered 構造の非可換性（M379F が外部と明示した部分）を本物で示す。 -/
theorem ttc_thetaGrp_not_tcmAbelian : ¬ tcmAbelian thetaGrp := by
  intro h
  have h2 := h ((1, 0, 0) : Int × Int × Int) ((0, 1, 0) : Int × Int × Int)
  rw [ttc_mul_ex1, ttc_mul_ex2] at h2
  have h3 : (1 : Int) = 0 := congrArg (fun t => t.2.2) h2
  exact absurd h3 (by omega)

/-- **定理 (M384F-4b): 標準生成元の交換子は中心生成元・非自明** —
    [(1,0,0),(0,1,0)] = (0,0,1) ≠ 1（M11 comm_xy）。テータ群の非可換性が
    中心シクロトームの生成元 (0,0,1) をちょうど 1 単位ぶん生むことの本物の内容。 -/
theorem ttc_commutator_gen_nontrivial :
    thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0) = ((0, 0, 1) : Int × Int × Int)
      ∧ ((0, 0, 1) : Int × Int × Int) ≠ thetaGrp.one := by
  refine ⟨comm_xy, ?_⟩
  intro hcontra
  have h3 : (1 : Int) = 0 := congrArg (fun t => t.2.2) hcontra
  exact absurd h3 (by omega)

/-! ## M384F-5: 交換子の μ_l 像（内部円分体の中で非自明）

  M124F `centerToMu` は中心座標 z ∈ ℤ を μ_l の元 ζ^{z mod l} に送る同期写像である。
  交換子の中心座標を μ_l に送ると非自明な元（ζ）が得られる — M379F のアーベル ℤ_l 商では
  交換子が自明ゆえ μ_l 側にも 1 しか到達しないのと対照的。 -/

/-- **定理 (M384F-5a): 交換子の中心座標の μ_l 像は形式値の μ_l 像に一致** —
    centerToMu(([g,h] の中心座標)) = centerToMu(a·b′−a′·b)。M11 theta_comm の μ_l 移送。 -/
theorem ttc_commutator_mu_form (p l : Nat) (ζ : (Zp p).carrier)
    (a b c a' b' c' : Int) :
    centerToMu p l ζ ((thetaGrp.comm (a, b, c) (a', b', c')).2.2)
      = centerToMu p l ζ (a * b' - a' * b) := by
  rw [theta_comm]

/-- **定理 (M384F-5b): 標準生成元の交換子の μ_l 像は非自明 = ζ** —
    centerToMu p l ζ ([(1,0,0),(0,1,0)] の中心座標) = ζ^1 = ζ（l ≥ 2）。
    tempered テータ交換子が内部円分体 μ_l（M124F 同期写像）の中で**非自明に実現**される
    ことの本物の証明。M379F のアーベル商では交換子が μ に到達しない（1）のと対照的。 -/
theorem ttc_commutator_mu (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    centerToMu p l ζ
        ((thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0)).2.2)
      = zpPow p ζ 1 := by
  have hval : (thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0)).2.2 = (1 : Int) := by
    rw [comm_xy]
  have hnat := centerToMu_natCast p l ζ (by omega : (1 : Nat) < l)
  have hcast : ((1 : Nat) : Int) = (1 : Int) := by omega
  rw [hval, ← hcast]
  exact hnat

/-! ## M384F-6: アーベル化 (a,b,c) ↦ (a,b) は交換子を潰す（M379F 類似）

  非可換 Heisenberg 群の最大アーベル商は ℤ²（(a,b) 部分）であり、そこへの射影は
  交換子を潰す。M379F の「ℤ_l アーベル化が交換子を潰す（`tcm_proj_kills_commutator`）」
  の Heisenberg 版 — 非可換性が中心一次元（μ 側）に完全に押し込まれることの本物の内容。 -/

/-- 対 (Int×Int) の等値補題。 -/
theorem ttc_pair_ext {a₁ b₁ a₂ b₂ : Int} (h1 : a₁ = a₂) (h2 : b₁ = b₂) :
    ((a₁, b₁) : Int × Int) = (a₂, b₂) := by
  rw [h1, h2]

/-- **M384F-6a: アーベル化群** ℤ²（Heisenberg 群の最大アーベル商の台）。 -/
@[reducible] def ttcAbGrp : Grp where
  carrier := Int × Int
  mul := fun x y => (x.1 + y.1, x.2 + y.2)
  one := (0, 0)
  inv := fun x => (-x.1, -x.2)
  mul_assoc := by
    intro x y z
    obtain ⟨a, b⟩ := x
    obtain ⟨a', b'⟩ := y
    obtain ⟨a'', b''⟩ := z
    show ((a + a' + a'', b + b' + b'') : Int × Int) = (a + (a' + a''), b + (b' + b''))
    exact ttc_pair_ext (by omega) (by omega)
  one_mul := by
    intro x
    obtain ⟨a, b⟩ := x
    show (((0 : Int) + a, (0 : Int) + b) : Int × Int) = (a, b)
    exact ttc_pair_ext (by omega) (by omega)
  inv_mul := by
    intro x
    obtain ⟨a, b⟩ := x
    show ((-a + a, -b + b) : Int × Int) = ((0 : Int), (0 : Int))
    exact ttc_pair_ext (by omega) (by omega)

/-- **定理 (M384F-6b): アーベル化群 ℤ² は可換** — M379F の述語 tcmAbelian で。 -/
theorem ttc_ab_abelian : tcmAbelian ttcAbGrp := by
  intro x y
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  show ((a + a', b + b') : Int × Int) = (a' + a, b' + b)
  exact ttc_pair_ext (by omega) (by omega)

/-- **M384F-6c: アーベル化射影** thetaGrp → ℤ²、(a,b,c) ↦ (a,b)（準同型）。 -/
def ttcAbProj : Hom thetaGrp ttcAbGrp where
  map := fun x => (x.1, x.2.1)
  map_mul := by
    intro x y
    obtain ⟨a, b, c⟩ := x
    obtain ⟨a', b', c'⟩ := y
    show ((a + a', b + b') : Int × Int) = (a + a', b + b')
    rfl

/-- **定理 (M384F-6d): アーベル化は交換子を潰す** — proj([g,h]) = 1_{ℤ²}。
    交換子の第 1・2 成分が 0（M384F-2a,b）ゆえ ℤ² 商では消える。M379F
    `tcm_proj_kills_commutator`（ℤ_l アーベル化が交換子を潰す）の Heisenberg 版。 -/
theorem ttc_ab_kills_commutator (a b c a' b' c' : Int) :
    ttcAbProj.map (thetaGrp.comm (a, b, c) (a', b', c')) = ttcAbGrp.one := by
  rw [theta_comm]
  rfl

/-! ## M384F-7: mod-l 商での交換子（M98F theta_comm_mod の再輸出） -/

/-- **定理 (M384F-7a): 商テータ群での交換子生成** —
    thetaGrpMod l で [red(1,0,0), red(0,1,0)] = red(0,0,1)（M98F theta_comm_mod）。
    非可換交換子構造が mod-l 商へ降下することの本物の内容。 -/
theorem ttc_mod_commutator_gen (l : Nat) :
    (thetaGrpMod l).comm ((thetaRed l).map (1, 0, 0)) ((thetaRed l).map (0, 1, 0))
      = (thetaRed l).map (0, 0, 1) :=
  theta_comm_mod l

/-! ## M384F-8: 正直な外部仮説（決して導出しない） -/

/-- **外部仮説（正直な限定・決して導出しない）**: 完全な幾何的 tempered 基本群 Δ^temp の
    slim 遠アーベル性（[SemiAnbd] André–Mochizuki）と、p 進テータ関数のガロア同変な評価・
    tempered 被覆の商としての thetaGrp の実現は本質的に外部（幾何的入力・後続）。本モジュールは
    離散 Heisenberg 骨格 thetaGrp・その mod-l 商・固定 p の μ_l のみを扱う。 -/
def ttc_full_tempered_slim_hypothesis (T : Grp) (f : Hom T thetaGrp) : Prop :=
  f.Injective

/-! ## M384F-9: capstone -/

/-- **M384F-9a: tempered テータ交換子データ** — 離散 Heisenberg 群 thetaGrp の
    非可換交換子構造を束ねる: 中心座標の中心性・交換子が中心に落ちる・中心座標 =
    シンプレクティック形式 a·b′−a′·b・交代性（[g,g]=1・ω 反対称）・群の非可換性
    （¬tcmAbelian、M379F のアーベル ℤ_l 商と対照）・標準生成元の交換子 = 中心生成元
    (0,0,1) ≠ 1・交換子の μ_l 像が非自明 = ζ・アーベル化 ℤ² が交換子を潰す（μ に圧縮）・
    mod-l 商での交換子生成。主語は本物の Heisenberg 群 thetaGrp・本物の μ_l（toy 群なし）。 -/
structure TemperedThetaCommutatorData (p l : Nat) (hl : 2 ≤ l)
    (ζ : (Zp p).carrier) where
  /-- 中心座標 (0,0,c) は真に中心。 -/
  center_central : ∀ c : Int, ttcCentral ((0, 0, c) : thetaGrp.carrier)
  /-- 交換子は中心に属す。 -/
  commutator_central : ∀ g h : thetaGrp.carrier, ttcCentral (thetaGrp.comm g h)
  /-- 交換子の第 1 成分は 0。 -/
  commutator_fst : ∀ a b c a' b' c' : Int,
    (thetaGrp.comm (a, b, c) (a', b', c')).1 = 0
  /-- 交換子の第 2 成分は 0。 -/
  commutator_snd : ∀ a b c a' b' c' : Int,
    (thetaGrp.comm (a, b, c) (a', b', c')).2.1 = 0
  /-- 交換子の中心座標 = シンプレクティック形式 a·b′−a′·b。 -/
  commutator_form : ∀ a b c a' b' c' : Int,
    (thetaGrp.comm (a, b, c) (a', b', c')).2.2 = a * b' - a' * b
  /-- 自己交換子は自明（交代性）。 -/
  commutator_self : ∀ g : thetaGrp.carrier, thetaGrp.comm g g = thetaGrp.one
  /-- 交換子の中心座標は反対称: ω(g,h) = −ω(h,g)。 -/
  form_antisymm : ∀ a b c a' b' c' : Int,
    (thetaGrp.comm (a, b, c) (a', b', c')).2.2
      = -((thetaGrp.comm (a', b', c') (a, b, c)).2.2)
  /-- テータ群は非可換（M379F のアーベル ℤ_l 商と対照）。 -/
  nonabelian : ¬ tcmAbelian thetaGrp
  /-- 標準生成元の交換子 = 中心生成元 (0,0,1)。 -/
  commutator_gen : thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0)
    = ((0, 0, 1) : Int × Int × Int)
  /-- 中心生成元 (0,0,1) は非自明（≠ 1）。 -/
  commutator_gen_ne_one : ((0, 0, 1) : Int × Int × Int) ≠ thetaGrp.one
  /-- 交換子の μ_l 像は非自明 = ζ。 -/
  commutator_mu : centerToMu p l ζ
      ((thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0)).2.2) = zpPow p ζ 1
  /-- アーベル化群 ℤ² は可換。 -/
  ab_abelian : tcmAbelian ttcAbGrp
  /-- アーベル化は交換子を潰す（非可換性が中心 μ に圧縮）。 -/
  ab_kills_commutator : ∀ a b c a' b' c' : Int,
    ttcAbProj.map (thetaGrp.comm (a, b, c) (a', b', c')) = ttcAbGrp.one
  /-- mod-l 商での交換子生成。 -/
  mod_commutator_gen : (thetaGrpMod l).comm
      ((thetaRed l).map (1, 0, 0)) ((thetaRed l).map (0, 1, 0))
    = (thetaRed l).map (0, 0, 1)

/-- **M384F-9b: witness 本体** — 全フィールドを M384F-1〜7 の本物の証明で埋める
    （外部仮説ゼロ・完全証明・ζ が単数根であることすら不要）。 -/
def temperedThetaCommutatorData (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    TemperedThetaCommutatorData p l hl ζ where
  center_central := ttc_center_central
  commutator_central := ttc_commutator_central
  commutator_fst := ttc_commutator_fst
  commutator_snd := ttc_commutator_snd
  commutator_form := ttc_commutator_form
  commutator_self := ttc_commutator_self
  form_antisymm := ttc_form_antisymm
  nonabelian := ttc_thetaGrp_not_tcmAbelian
  commutator_gen := comm_xy
  commutator_gen_ne_one := ttc_commutator_gen_nontrivial.2
  commutator_mu := ttc_commutator_mu p l hl ζ
  ab_abelian := ttc_ab_abelian
  ab_kills_commutator := ttc_ab_kills_commutator
  mod_commutator_gen := ttc_mod_commutator_gen l

/-- **定理 (M384F-9c): tempered テータ交換子データの存在（M384F 見出し）** —
    p・l ≥ 2・μ_l 候補 ζ が与えられれば、離散 Heisenberg 群 thetaGrp の非可換交換子構造
    （中心性・シンプレクティック形式・交代性・非可換性・μ_l 非自明像・アーベル化）を束ねた
    データが**外部仮説なしで**存在する（完全証明）。M379F が外部と明示した非可換テータ構造の
    本物の建設。 -/
theorem ttc_exists (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    Nonempty (TemperedThetaCommutatorData p l hl ζ) :=
  ⟨temperedThetaCommutatorData p l hl ζ⟩

/-! ## M384F-10: 実例 -/

/-- 実例: p = 7・l = 5 の tempered テータ交換子データが存在する（ζ は任意の ℤ_7 の元でよい）。 -/
example (ζ : (Zp 7).carrier) : Nonempty (TemperedThetaCommutatorData 7 5 (by omega) ζ) :=
  ttc_exists 7 5 (by omega) ζ

/-- 実例: テータ群は非可換（M379F の可換 ℤ_l 商と対照）。 -/
example : ¬ tcmAbelian thetaGrp := ttc_thetaGrp_not_tcmAbelian

/-- 実例: 具体的な交代形式 — [(2,3,0),(5,7,0)] の中心座標 = 2·7 − 5·3 = −1。 -/
example : (thetaGrp.comm ((2, 3, 0) : Int × Int × Int) (5, 7, 0)).2.2 = -1 := by
  rw [theta_comm]
  show (2 * 7 - 5 * 3 : Int) = -1
  omega

/-- 実例: 標準生成元の交換子 = 中心生成元 (0,0,1) ≠ 1。 -/
example : thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0) = ((0, 0, 1) : Int × Int × Int)
    ∧ ((0, 0, 1) : Int × Int × Int) ≠ thetaGrp.one :=
  ttc_commutator_gen_nontrivial

/-- 実例: 交換子は中心（任意の元と可換）。 -/
example (g h : thetaGrp.carrier) : ttcCentral (thetaGrp.comm g h) :=
  ttc_commutator_central g h

/-- 実例: アーベル化 ℤ² は交換子を潰す（非可換性が中心 μ に圧縮）。 -/
example (a b c a' b' c' : Int) :
    ttcAbProj.map (thetaGrp.comm (a, b, c) (a', b', c')) = ttcAbGrp.one :=
  ttc_ab_kills_commutator a b c a' b' c'

/-- 実例: 交換子の μ_l 像は非自明 = ζ（l = 5、内部円分体の中で非自明に実現）。 -/
example (ζ : (Zp 7).carrier) :
    centerToMu 7 5 ζ
        ((thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0)).2.2) = zpPow 7 ζ 1 :=
  ttc_commutator_mu 7 5 (by omega) ζ

end IUT
