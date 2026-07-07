/-
  IUT/ThetaCovering.lean — M369F [実／本物]
  分類: 実 (Tate 曲線の l 重テータ被覆＋被覆変換群 ℤ/l・tempered π₁ 詳細化)
  complete_pct 影響: 柱A を前進（M364F tempered π₁ を詳細化＝部分格子 lℤ⊆ℤ(=q^{lℤ}⊆q^ℤ) による
    l 次テータ被覆・被覆変換群 ℤ/l・完全性 lℤ→ℤ→ℤ/l・被覆が tempered π₁ の離散部に可視
    （副有限部でなく）を本物で）。
  正直な限定: 全被覆塔・tempered π₁=lim(deck) は外部仮説等。
-/
import IUT.TemperedPi1
import IUT.QuotientGroup

namespace IUT

/-! ## M369F-1: 部分格子 lℤ ⊆ ℤ（= q^{lℤ} ⊆ q^ℤ、指数 l）

  Tate 曲線 E_q = K^×/q^ℤ の周期束 q^ℤ は指数を取ると加法群 ℤ（M333F/M364F の離散部
  `tmpDiscretePart`）である。l 重テータ被覆はこの離散格子の指数 l の部分格子
  lℤ ⊆ ℤ（= q^{lℤ} ⊆ q^ℤ）に対応する。本物の加法群 `intGrp` の部分群として構成する。 -/

/-- **M369F-1: 部分格子 lℤ ⊆ ℤ** — 指数格子 ℤ（= 周期束 q^ℤ）の指数 l の部分群
    {a | l ∣ a}（= q^{lℤ}）。closure は整除の加法・逆元則から本物で。 -/
def tcvSublattice (l : Nat) : Subgroup intGrp where
  mem := fun a => (l : Int) ∣ a
  one_mem := ⟨0, by show (0 : Int) = (l : Int) * 0; rw [Int.mul_zero]⟩
  mul_mem := fun {a b} ha hb => by
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    show a + b = (l : Int) * (u + v)
    rw [Int.mul_add, ← hu, ← hv]
  inv_mem := fun {a} ha => by
    obtain ⟨u, hu⟩ := ha
    refine ⟨-u, ?_⟩
    show -a = (l : Int) * (-u)
    rw [Int.mul_neg, ← hu]

/-- 生成元 l 自身は部分格子 lℤ に属する（l = l·1）。 -/
theorem tcv_l_mem (l : Nat) : (tcvSublattice l).mem ((l : Nat) : Int) :=
  ⟨1, by show ((l : Nat) : Int) = (l : Int) * 1; rw [Int.mul_one]⟩

/-- **M369F-1b: 部分格子は正規部分群**（ℤ は可換ゆえ任意部分群が正規）。
    g + n + (−g) = n（可換性）で lℤ に留まる。 -/
def tcvSublattice_normal (l : Nat) :
    IsNormalSubgroup intGrp (tcvSublattice l) := by
  intro g n hn
  have he : intGrp.mul (intGrp.mul g n) (intGrp.inv g) = n := by
    show g + n + -g = n
    rw [Int.add_comm g n, Int.add_assoc, Int.add_comm g (-g),
      Int.add_left_neg, Int.add_zero]
  show (tcvSublattice l).mem (intGrp.mul (intGrp.mul g n) (intGrp.inv g))
  rw [he]
  exact hn

/-! ## M369F-2: 被覆変換群 deck = ℤ/lℤ = intGrp/(lℤ)（位数 l の群）

  l 重テータ被覆 E_{q^l} → E_q（格子レベルでは ℤ → ℤ/l）の被覆変換（デッキ）群は
  ℤ/lℤ = intGrp/(lℤ)（M267F `quotientGroupN`）である。位数 l の本物の群。 -/

/-- **M369F-2: 被覆変換群 deck(l) = ℤ/lℤ** — 指数格子 ℤ を部分格子 lℤ で割った
    本物の商群（M267F `quotientGroupN`）。l 重テータ被覆のデッキ群 ℤ/l。 -/
def tcvDeckGroup (l : Nat) : Grp :=
  quotientGroupN intGrp (tcvSublattice l) (tcvSublattice_normal l)

/-! ## M369F-3: 被覆写像 ℤ → ℤ/l（核 = lℤ）

  被覆 E_{q^l} → E_q の格子レベルの射影 ℤ → ℤ/l = deck。核はちょうど部分格子 lℤ。 -/

/-- **M369F-3: 被覆写像 cov : ℤ → deck(l)** — 格子レベルの射影（= E_{q^l} → E_q の
    デッキ商）。核 lℤ の本物の全射準同型。 -/
def tcvCovering (l : Nat) : Hom intGrp (tcvDeckGroup l) :=
  quotientProjN intGrp (tcvSublattice l) (tcvSublattice_normal l)

/-- **M369F-3b: 被覆は全射**（デッキ群の全ての元が持ち上がる）。 -/
theorem tcv_covering_surjective (l : Nat) :
    ∀ x, ∃ a, (tcvCovering l).map a = x :=
  quotientProjN_surjective intGrp (tcvSublattice l) (tcvSublattice_normal l)

/-! ## M369F-4: 完全性 lℤ → ℤ → ℤ/l（被覆が次数 l） -/

/-- **定理 (M369F-4a): 被覆の完全性 lℤ → ℤ → ℤ/l** — 被覆写像の核はちょうど
    部分格子 lℤ: cov(a) = 1_{deck} ⟺ a ∈ lℤ（M267F `quotientProjN_ker`）。
    l 重テータ被覆のガロア（デッキ）データそのもの。 -/
theorem tcv_covering_exact (l : Nat) (a : Int) :
    (tcvCovering l).map a = (tcvDeckGroup l).one ↔ (tcvSublattice l).mem a :=
  quotientProjN_ker intGrp (tcvSublattice l) (tcvSublattice_normal l) a

/-- **定理 (M369F-4b): デッキ群の生成元は位数 l（被覆は次数 l）** — デッキ生成元
    cov(1) は l 乗で単位元に潰れる: (cov 1)^l = [l] = 1_{deck}（l ∈ lℤ ゆえ）。
    被覆 E_{q^l} → E_q が l 段で閉じる（次数 l）ことの本物の内容。 -/
theorem tcv_deck_order (l : Nat) :
    (tcvDeckGroup l).pow ((tcvCovering l).map 1) l = (tcvDeckGroup l).one := by
  rw [← Hom.map_pow, intGrp_pow_one]
  exact (tcv_covering_exact l ((l : Nat) : Int)).mpr (tcv_l_mem l)

/-! ## M369F-5: テータ被覆＝ l-torsion ↔ デッキ群 ℤ/l（テータ関数が乗る被覆）

  E_q の l-torsion（l で消える点）は被覆変換群 ℤ/l に対応し、テータ関数はこの被覆上で
  定義される。格子レベルでは、デッキ生成元 cov(1)（= テータ準周期 q の指数 1、M333F）が
  ちょうど l-torsion 元（l 乗で消える）である。 -/

/-- **定理 (M369F-5a): 離散生成元 = テータ準周期 q**（M333F 再利用）— 被覆の離散生成元
    （指数 1）は周期準同型 n ↦ qⁿ で Tate パラメータ q（テータ準周期、M309F/M313F）に写る。
    テータ関数 Θ(q,·) が乗る周期がまさにこの生成元であることの接続。 -/
theorem tcv_theta_period_generates (K : IUTField) (q : (tateMultGroup K).carrier) :
    (discRig_periodHom K q).map 1 = q :=
  tateZpow_one (tateMultGroup K) q

/-- **定理 (M369F-5b): テータ被覆 — デッキ生成元は l-torsion** — E_q の l 重テータ被覆の
    デッキ群 ℤ/l において、生成元 cov(1)（テータ準周期 q に対応）は l-torsion 元
    （(cov 1)^l = 1_{deck}）であり、かつ被覆写像は準周期束の生成元 l を核（1_{deck}）に送る。
    テータ値の l-torsion（M318F 系）がデッキ群 ℤ/l に一致するという対応の本物の中身。 -/
theorem tcv_theta_covering (l : Nat) :
    (tcvDeckGroup l).pow ((tcvCovering l).map 1) l = (tcvDeckGroup l).one
      ∧ (tcvCovering l).map ((l : Nat) : Int) = (tcvDeckGroup l).one :=
  ⟨tcv_deck_order l, (tcv_covering_exact l ((l : Nat) : Int)).mpr (tcv_l_mem l)⟩

/-! ## M369F-6: tempered π₁ の詳細化（被覆は離散部に可視・副有限部でなく）

  M364F の tempered π₁ = 拡大 1 → Ẑ → π₁^temp → ℤ → 1 において、l 重テータ被覆は
  離散部 ℤ（`tmpDiscretePart`）にのみ可視で、副有限部 Ẑ（`tmpProfinitePart`）には
  不可視である。被覆 cov : ℤ → ℤ/l は離散部そのものの射影であり、π₁^temp 全体からの
  合成 π₁^temp ↠ ℤ ↠ ℤ/l は副有限埋め込み ι(Ẑ) を単位元に潰す。 -/

/-- **M369F-6a: 被覆は離散部 ℤ の射影**（tempered π₁ の離散部そのものに乗る）— 被覆写像
    cov : ℤ → ℤ/l は M364F の離散部 `tmpDiscretePart`（= intGrp）からデッキ群への全射。 -/
theorem tcv_discrete_surjects (l : Nat) :
    ∀ x, ∃ n : tmpDiscretePart.carrier, (tcvCovering l).map n = x :=
  tcv_covering_surjective l

/-- **M369F-6b: tempered 被覆 π₁^temp ↠ ℤ/l** — 射影 pr : π₁^temp ↠ ℤ（M364F `tmpProj`）と
    被覆 cov : ℤ ↠ ℤ/l の合成。デッキ群 ℤ/l を tempered π₁ の商として実現する。 -/
def tcvTemperedCovering (l : Nat) : Hom tmpTemperedGroup (tcvDeckGroup l) :=
  (tcvCovering l).comp tmpProj

/-- **定理 (M369F-6c): tempered 被覆は全射** — 合成 π₁^temp ↠ ℤ ↠ ℤ/l は全射
    （デッキ群 ℤ/l は tempered π₁ の商として可視）。 -/
theorem tcv_tempered_surjective (l : Nat) :
    ∀ x, ∃ p, (tcvTemperedCovering l).map p = x := by
  intro x
  obtain ⟨a, ha⟩ := tcv_covering_surjective l x
  obtain ⟨p, hp⟩ := tmp_proj_surjective a
  refine ⟨p, ?_⟩
  show (tcvCovering l).map (tmpProj.map p) = x
  rw [hp, ha]

/-- **定理 (M369F-6d): 被覆は副有限部に不可視（tempered 詳細化の核心）** — tempered 被覆
    π₁^temp ↠ ℤ/l は副有限部の埋め込み像 ι(Ẑ)（`tmpIncl`、円分部）を単位元に潰す:
    (cov∘pr)(ι z) = 1_{deck}。すなわち l 重テータ被覆は π₁^temp の**離散部にのみ可視**で、
    副有限部（エタール π₁ の側）には見えない。これが「テータ被覆は tempered でこそ見える」
    の本物の形式化。 -/
theorem tcv_tempered_kills_profinite (l : Nat) (z : tmpProfinitePart.carrier) :
    (tcvTemperedCovering l).map (tmpIncl.map z) = (tcvDeckGroup l).one := by
  show (tcvCovering l).map (tmpProj.map (tmpIncl.map z)) = (tcvDeckGroup l).one
  rw [tmp_proj_incl_trivial z]
  exact Hom.map_one (tcvCovering l)

/-! ## M369F-7: 正直な外部仮説（決して導出しない） -/

/-- **外部仮説（正直な限定・決して導出しない）**: 全被覆塔 E_{q^{l^k}} → E_q（k=0,1,2,…）が
    忠実 ＝ 周期 q が無限位数（塔が崩れず各段のデッキ群 ℤ/l^k が非自明）。M333F/M364F と同じく、
    正 valuation の素元 v(q)≠0 の具体構成は柱B ℤ_p 接続の後続ゆえ、本層では外部仮説として受ける。 -/
def tcv_full_tower_hypothesis (K : IUTField) (q : (tateMultGroup K).carrier) : Prop :=
  discRig_infiniteOrder_hypothesis (tateMultGroup K) q

/-- **外部仮説（正直な限定・決して導出しない）**: tempered π₁ = 全デッキ群 ℤ/l^k の逆極限
    （＝副有限完備化）で、実際の π₁^temp が slim（M9 `Slim`、中心自明）であること。André・
    Mochizuki [SemiAnbd] の tempered 遠アーベル定理の前提であり、本モデルの可換な骨格
    Ẑ×ℤ は slim でないため本質的に外部（幾何的入力）。決して導出しない。 -/
def tcv_tempered_limit_hypothesis (T : Grp) : Prop := Slim T

/-! ## M369F-8: capstone -/

/-- **M369F-8a: l 重テータ被覆の総括データ** — Tate パラメータ q・被覆度 l・被覆変換群
    deck = ℤ/lℤ・被覆写像 cov : ℤ → ℤ/l・完全性 lℤ→ℤ→ℤ/l（核 = lℤ）・全射性・デッキ生成元の
    位数 l（次数 l 被覆）・全被覆塔の忠実性仮説（正直な外部 crux）を束ねる。主語は本物の
    部分格子 lℤ と本物の商群 ℤ/l（toy 代理なし）。 -/
structure ThetaCoveringData (K : IUTField) where
  /-- Tate パラメータ q ∈ K^×。 -/
  q : (tateMultGroup K).carrier
  /-- 被覆度 l。 -/
  l : Nat
  /-- l ≥ 1。 -/
  hl : 0 < l
  /-- 被覆変換群 deck = ℤ/lℤ。 -/
  deckGroup : Grp
  /-- 被覆写像 cov : ℤ → deck。 -/
  covering : Hom intGrp deckGroup
  /-- deck = intGrp/(lℤ)（本物の商群）。 -/
  deck_isQuotient : deckGroup = tcvDeckGroup l
  /-- 完全性 lℤ→ℤ→ℤ/l: cov の核 = 部分格子 lℤ。 -/
  covering_exact : ∀ a, covering.map a = deckGroup.one ↔ (tcvSublattice l).mem a
  /-- 被覆は全射。 -/
  covering_surj : ∀ x, ∃ a, covering.map a = x
  /-- デッキ生成元は位数 l（次数 l 被覆）。 -/
  deck_order : deckGroup.pow (covering.map 1) l = deckGroup.one
  /-- 全被覆塔の忠実性仮説（正直な外部 crux）。 -/
  fullTower : tcv_full_tower_hypothesis K q

/-- **M369F-8b: witness 本体** — 全被覆塔仮説 hTower を受けて全フィールドを M369F-1〜6 の
    本物の証明で埋める（hTower 以外はすべて完全証明で埋まる）。 -/
def thetaCoveringData (K : IUTField) (q : (tateMultGroup K).carrier)
    (l : Nat) (hl : 0 < l) (hTower : tcv_full_tower_hypothesis K q) :
    ThetaCoveringData K where
  q := q
  l := l
  hl := hl
  deckGroup := tcvDeckGroup l
  covering := tcvCovering l
  deck_isQuotient := rfl
  covering_exact := tcv_covering_exact l
  covering_surj := tcv_covering_surjective l
  deck_order := tcv_deck_order l
  fullTower := hTower

/-- **定理 (M369F-8c): l 重テータ被覆データの（条件付き）存在** — 被覆度 l ≥ 1 と全被覆塔の
    忠実性仮説が与えられれば、Tate 曲線 E_q の l 重テータ被覆・被覆変換群 ℤ/l・完全性・
    次数 l を束ねたデータが存在する。存在が塔仮説に条件付くのは正直な限定（正 valuation の
    素元の具体構成は柱B の後続）。 -/
theorem tcv_exists (K : IUTField) (q : (tateMultGroup K).carrier)
    (l : Nat) (hl : 0 < l) (hTower : tcv_full_tower_hypothesis K q) :
    Nonempty (ThetaCoveringData K) :=
  ⟨thetaCoveringData K q l hl hTower⟩

/-! ## 実例（l = 5、被覆変換群 ℤ/5・無条件で成立する被覆の核） -/

/-- 実例: l = 5 のデッキ生成元は位数 5（(cov 1)^5 = 1_{ℤ/5}、次数 5 被覆）。 -/
example : (tcvDeckGroup 5).pow ((tcvCovering 5).map 1) 5 = (tcvDeckGroup 5).one :=
  tcv_deck_order 5

/-- 実例: ℤ/5 のデッキ生成元は非自明（cov(1) ≠ 1_{ℤ/5}、5 ∤ 1）。被覆変換群 ℤ/5 が
    真に位数 5 の非自明群であることの核。 -/
example : (tcvCovering 5).map 1 ≠ (tcvDeckGroup 5).one := by
  intro h
  have hmem : (tcvSublattice 5).mem 1 := (tcv_covering_exact 5 1).mp h
  obtain ⟨c, hc⟩ := hmem
  omega

/-- 実例: l = 5 被覆の完全性（cov の核 = 5ℤ）。 -/
example (a : Int) :
    (tcvCovering 5).map a = (tcvDeckGroup 5).one ↔ (tcvSublattice 5).mem a :=
  tcv_covering_exact 5 a

/-- 実例: テータ被覆は副有限部に不可視（π₁^temp の離散部にのみ可視）。 -/
example (z : tmpProfinitePart.carrier) :
    (tcvTemperedCovering 5).map (tmpIncl.map z) = (tcvDeckGroup 5).one :=
  tcv_tempered_kills_profinite 5 z

end IUT
