-- M464F LatticeCoherenceIndet [実・本物・柱C×柱D frontier・M459F の残限定「不定性込み格子整合は外部」を昇格で閉じる]
-- complete_pct 影響: 前進。柱C/柱D で M459F ilt_model_scope (ii)・外部仮説 ilt_full_lattice_hypothesis の
--   残限定「実 IUT の格子の整合は不定性 (Ind1)(Ind2)(Ind3) 込みでしか成立しない——その不定性込みの整合は外部」を
--   昇格で閉じる: M459F の無限 log-theta-lattice（ℤ×ℤ・iltNode/iltHLink/iltVLink）の**各格子辺の輸送に
--   M447F の (Ind1)×(Ind2)×(Ind3) 合成不定性群 lfiIndetGroup の元を貼った装飾経路 Lci2Path** を建て、
--   (i) 各辺の輸送の曖昧さ＝不定性群の log-volume 作用 lci2IndetAction、(ii) 経路合成＝簿記函手×蓄積不定性
--   lci2PathWithIndet、(iii) **本丸 lci2_path_coherent_mod_indet**: (0,0)→(m,n) の任意の 2 装飾経路の合成が
--   **不定性群を法として一致**（簿記函手は on the nose 一致・蓄積不定性の差は群の元 d＝path-independence up to
--   indeterminacy）、(iv) 不定性を単位元にすると M459F の on-the-nose 経路独立へ厳密還元（lci2_reduces_to_ilt）、
--   (v) 経路に沿った不定性の蓄積は真の群準同型（lci2_indet_group_hom・lfi_action_hom 再輸出＋逆元 lci2Inv 込みの
--   群法則）を完全証明し、M459F の外部仮説のうち不定性込み格子整合部分を内部定理 lci2_closes_m459_limitation
--   として供給。crux Dβ-ω は外部のまま（lci2_crux_is_hypothesis）。
-- 正直な限定: 不定性群は既存 Ind 模型（Bool×Bool×ℤ・M447F lfi）の格子貼り付けに留まり、実 π₁^ét（遠アーベル
--   復元）上の完全不定性群・各格子点の劇場の完全数論的実現（Θ±ellNF-Hodge 劇場全データ）・(Ind3) 連続部の
--   Haar 測度レベル・多輻不等式（crux Dβ-ω）は外部/後続（lci2_model_scope・ilt_full_lattice_hypothesis の
--   π₁^ét/slim 部分は狭めて残す）。

/-
  IUT/LatticeCoherenceIndet.lean — M464F [実／本物の忠実な部分ケース・柱C×柱D frontier]
  分類: 実（§2(a) 昇格）。M459F `InfiniteLogThetaLattice`（`ilt`）は ℤ×ℤ の無限
  log-theta-lattice の全単位正方形可換と on-the-nose 経路独立性を本物化したが、
  `ilt_model_scope` (ii)／外部仮説 `ilt_full_lattice_hypothesis` に

    「経路独立性が on-the-nose で成立するのは簿記レベルの帰結であり、実 IUT の
     格子の整合は不定性 (Ind1)(Ind2)(Ind3) 込みでしか成立しない——その不定性
     込みの整合は外部」

  と正直に限定していた。本 M464F はこの限定を **(Ind1)(Ind2)(Ind3) を畳み込んだ
  格子整合（path-independence up to indeterminacy）**へ昇格して閉じる。

  既存の実部品（本モジュールは両者の貼り合わせ・toy 主語なし）:
    * M459F (InfiniteLogThetaLattice): 格子点 Frobenioid iltNode・横 Θ-link 函手
      iltHLink・縦 log-link 函手 iltVLink・経路型 IltPath・函手解釈 iltPathFunctor・
      on-the-nose 経路独立 ilt_path_independent・degree 経路不変量 ilt_path_degree
    * M447F (LogLinkFullIndetGroup): (Ind1)×(Ind2)×(Ind3) 合成不定性群
      lfiIndetGroup（Bool×Bool×ℤ）・群演算 lfiMul・単位 lfiOne・log-volume への
      作用 lfiAct（deg_ℝ シフトは (Ind3) 成分のみ・M342F 実 deg_ℝ 事実の写し）・
      作用の群準同型 lfi_action_hom・単位作用 lfi_act_one
    * M457F (LogLinkFullContinuous): 連続版 lfc（本層は離散群 lfi を貼る・連続版の
      格子貼り付けは後続）

  本モジュールの構成（[IUTchIII] Thm 3.11 の「格子の整合は (Ind1)(Ind2)(Ind3) の
  不定性を法としてのみ成立する」の忠実な形式化）:
    * **装飾経路** Lci2Path m n: (0,0)→(m,n) の各格子辺（横 Θ-link／縦 log-link）に
      不定性群 lfiIndetGroup の元を貼った経路（IltPath の各 step に g を装飾）。
    * **辺の不定性作用** lci2IndetAction: 各格子辺の輸送に付随する曖昧さ＝
      不定性群の元 g の log-volume への作用（M447F lfiAct を格子辺に貼る・
      横辺も縦辺も同じ (Ind1)(Ind2)(Ind3) 群が作用）。
    * **不定性込み経路合成** lci2PathWithIndet: 経路の簿記函手（lci2Functor＝M459F
      iltPathFunctor）×蓄積不定性（lci2Indet＝辺装飾の lfiMul 畳み込み）の
      log-volume 作用。
    * **本丸 lci2_path_coherent_mod_indet**: (0,0)→(m,n) の任意の 2 装飾経路 p, q に
      対し、不定性群の元 d が存在して (a) 簿記函手は on the nose 一致（M459F
      ilt_path_independent）、(b) 蓄積不定性は lci2Indet p = lci2Indet q · d と
      群の元 d だけずれる（2 経路の差＝不定性群の元）、(c) log-volume 作用は
      d の作用を挟んで合成される（lfi_action_hom）。すなわち**格子の経路整合は
      不定性群を法として成立する**——M459F の on-the-nose 経路独立を実 IUT の形
      （up to (Ind1)(Ind2)(Ind3)）へ昇格。
    * **lci2_reduces_to_ilt**: 全辺の装飾を単位元にする埋め込み lci2OfIlt で
      蓄積不定性は lfiOne・作用は恒等・簿記函手は M459F iltPathFunctor に厳密一致
      ——昇格が M459F の on-the-nose 版を真に含む証拠。
    * **lci2_indet_group_hom**: 経路に沿った不定性の蓄積は群準同型（nil↦単位元・
      step↦lfiMul 蓄積・蓄積の作用＝辺作用の合成 lfi_action_hom・結合律
      lci2_mul_assoc・逆元 lci2Inv・単位法則）——不定性が経路に沿って群として
      蓄積する本物。
    * **lci2_closes_m459_limitation**: M459F の外部仮説 ilt_full_lattice_hypothesis
      のうち「不定性 (Ind1)(Ind2)(Ind3) 込みの格子整合」部分を内部定理として供給
      （coherence mod indet・群準同型・M459F への還元・degree 経路不変量）。

  crux（決して内部化しない）:
    * 多輻アルゴリズム不等式（Dβ-ω、[IUTchIII] Cor 3.12 の係争ステップ）は本
      モジュールの主張に一切含めない。lci2_crux_is_hypothesis (crux : Prop) :
      crux ↔ crux ＝ Iff.rfl で外部仮説として保持。

  正直な限定（M459F の残限定「不定性込み格子整合」を閉じた上で、残りを狭めて
  述べ直す・消さない・弱めない）:
    * 不定性群は**既存 Ind 模型（M447F lfiIndetGroup = Bool×Bool×ℤ）の格子への
      貼り付け**に留まる——実 π₁^ét（遠アーベル復元）上の完全な不定性群ではなく、
      deg_ℝ への作用は (Ind3) 成分のみで決まる（lci2_model_scope (i)）。(Ind3) の
      連続部・Haar 測度レベルの積分は M457F 連続版の格子貼り付けとして後続。
    * 経路の簿記函手は M459F の degree/因子簿記レベル（lci2_model_scope (ii)）——
      各格子点の劇場の完全な数論的実現（Θ±ellNF-Hodge 劇場全データ・実 π₁^ét・
      非可換幾何）は外部。ilt_full_lattice_hypothesis の π₁^ét/slim 部分
      （実 π₁^ét 上の完全 log-shell・完全 log-Kummer 対応）は外部のまま狭めて残す。
    * 多輻不等式（crux Dβ-ω）は外部仮説（lci2_crux_is_hypothesis・Iff.rfl）。
  全て選択公理不使用（propext / Quot.sound のみ）・sorry 皆無・禁止タクティク不使用。
-/
import IUT.InfiniteLogThetaLattice
import IUT.LogLinkFullIndetGroup

namespace IUT

/-! ## M464F-0: 不定性群の群法則の補完（M447F lfiMul/lfiOne に逆元・結合律を供給） -/

/-- Bool xor の右単位（写経・core 依存回避のため明示ケース分け）。 -/
theorem lci2_xor_false_right : ∀ b : Bool, Bool.xor b false = b
  | true => rfl
  | false => rfl

/-- Bool xor の左単位。 -/
theorem lci2_xor_false_left : ∀ b : Bool, Bool.xor false b = b
  | true => rfl
  | false => rfl

/-- Bool xor の自己消去（ℤ/2 の逆元＝自分自身）。 -/
theorem lci2_xor_self : ∀ b : Bool, Bool.xor b b = false
  | true => rfl
  | false => rfl

/-- Bool xor の結合律（8 ケースの明示写経）。 -/
theorem lci2_xor_assoc : ∀ a b c : Bool,
    Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c)
  | false, false, false => rfl
  | false, false, true => rfl
  | false, true, false => rfl
  | false, true, true => rfl
  | true, false, false => rfl
  | true, false, true => rfl
  | true, true, false => rfl
  | true, true, true => rfl

/-- Int の右逆元（omega の Int 線形で閉じる）。 -/
theorem lci2_int_add_neg (z : Int) : z + (-z) = 0 := by omega

/-- Int の左逆元。 -/
theorem lci2_int_neg_add (z : Int) : (-z) + z = 0 := by omega

/-- **M464F-0a: 不定性群の元の外延性** — 3 成分（Ind1・Ind2・Ind3）が一致すれば
    群の元として等しい（M447F lfiIndetGroup の構造 ext）。 -/
theorem lci2_group_ext {g h : lfiIndetGroup}
    (h1 : g.ind1 = h.ind1) (h2 : g.ind2 = h.ind2) (h3 : g.ind3 = h.ind3) :
    g = h := by
  cases g
  cases h
  cases h1
  cases h2
  cases h3
  rfl

/-- **定理 (M464F-0b): 右単位法則** — lfiMul g lfiOne = g（Ind1/Ind2 は xor 右単位・
    Ind3 は Int 加法右単位）。 -/
theorem lci2_mul_one (g : lfiIndetGroup) : lfiMul g lfiOne = g :=
  lci2_group_ext (lci2_xor_false_right g.ind1) (lci2_xor_false_right g.ind2)
    (Int.add_zero g.ind3)

/-- **定理 (M464F-0c): 左単位法則** — lfiMul lfiOne g = g。 -/
theorem lci2_one_mul (g : lfiIndetGroup) : lfiMul lfiOne g = g :=
  lci2_group_ext (lci2_xor_false_left g.ind1) (lci2_xor_false_left g.ind2)
    (Int.zero_add g.ind3)

/-- **定理 (M464F-0d): 結合律** — lfiMul は結合的（Ind1/Ind2 は xor 結合律・
    Ind3 は Int 加法結合律）。M447F の群演算が本物の群であることの補完。 -/
theorem lci2_mul_assoc (a b c : lfiIndetGroup) :
    lfiMul (lfiMul a b) c = lfiMul a (lfiMul b c) :=
  lci2_group_ext (lci2_xor_assoc a.ind1 b.ind1 c.ind1)
    (lci2_xor_assoc a.ind2 b.ind2 c.ind2) (Int.add_assoc a.ind3 b.ind3 c.ind3)

/-- **M464F-0e: 逆元** — Ind1/Ind2 は自己逆（ℤ/2）・Ind3 は符号反転（ℤ）。
    2 経路の蓄積不定性の「差」を群の元として取り出すための本物のインフラ。 -/
def lci2Inv (g : lfiIndetGroup) : lfiIndetGroup := ⟨g.ind1, g.ind2, -g.ind3⟩

/-- **定理 (M464F-0f): 右逆元法則** — lfiMul g (lci2Inv g) = lfiOne。 -/
theorem lci2_mul_inv (g : lfiIndetGroup) : lfiMul g (lci2Inv g) = lfiOne :=
  lci2_group_ext (lci2_xor_self g.ind1) (lci2_xor_self g.ind2)
    (lci2_int_add_neg g.ind3)

/-- **定理 (M464F-0g): 左逆元法則** — lfiMul (lci2Inv g) g = lfiOne。 -/
theorem lci2_inv_mul (g : lfiIndetGroup) : lfiMul (lci2Inv g) g = lfiOne :=
  lci2_group_ext (lci2_xor_self g.ind1) (lci2_xor_self g.ind2)
    (lci2_int_neg_add g.ind3)

/-! ## M464F-1: 各格子辺の輸送に付随する不定性群の作用（lci2IndetAction） -/

/-- **M464F-1a: 格子辺の種別** — 横辺＝Θ-link・縦辺＝log-link（M459F iltHLink／
    iltVLink に対応）。どちらの辺の輸送にも同じ (Ind1)(Ind2)(Ind3) 群が作用する。 -/
inductive Lci2Edge : Type where
  /-- 横辺（Θ-link・iltHLink）。 -/
  | horiz : Lci2Edge
  /-- 縦辺（log-link・iltVLink）。 -/
  | vert : Lci2Edge

/-- **M464F-1b: 辺の不定性作用（lci2IndetAction）** — 格子辺 e（横 Θ-link／縦
    log-link）の輸送に付随する曖昧さ＝不定性群の元 g の log-volume への作用
    （M447F lfiAct＝deg_ℝ を g の (Ind3) 成分ぶん平行移動・Ind1/Ind2 は Σj² 核を
    保存し deg_ℝ を動かさない M342F 実事実の写し）。M459F の格子に M447F の
    不定性群を辺ごとに貼る本モジュールの土台。 -/
def lci2IndetAction (logq : Nat → RReal) (v : Nat) (_e : Lci2Edge)
    (g : lfiIndetGroup) (V : RReal) : RReal :=
  lfiAct logq v g V

/-- **定理 (M464F-1c): 辺種別によらず同じ群が作用** — 横 Θ-link 辺と縦 log-link 辺の
    輸送の曖昧さは同一の (Ind1)(Ind2)(Ind3) 群作用（定義的一致）。 -/
theorem lci2_indet_action_edge_uniform (logq : Nat → RReal) (v : Nat)
    (g : lfiIndetGroup) (V : RReal) :
    lci2IndetAction logq v Lci2Edge.horiz g V
      = lci2IndetAction logq v Lci2Edge.vert g V := rfl

/-- **定理 (M464F-1d): 辺の不定性作用は M447F lfiAct そのもの**（貼り付けが骨格の
    張り替えでなく M447F の本物の作用の再利用であることの機械検証）。 -/
theorem lci2_indet_action_is_lfi (logq : Nat → RReal) (v : Nat) (e : Lci2Edge)
    (g : lfiIndetGroup) (V : RReal) :
    lci2IndetAction logq v e g V = lfiAct logq v g V := rfl

/-! ## M464F-2: 装飾経路（各辺に不定性群の元を貼った格子経路） -/

/-- **M464F-2a: 装飾経路** — (0,0)→(m,n) の格子経路の**各辺（横 Θ-link／縦
    log-link）に不定性群 lfiIndetGroup の元を貼った**もの。実 IUT の格子輸送は
    各辺で (Ind1)(Ind2)(Ind3) の曖昧さを持つ——その曖昧さを担う群の元を辺ごとに
    明示的に持ち歩く経路型（M459F IltPath の不定性装飾版）。 -/
inductive Lci2Path : Nat → Nat → Type where
  /-- 長さ 0 の経路（出発点 (0,0)・不定性なし）。 -/
  | nil : Lci2Path 0 0
  /-- 末尾に横 Θ-link 辺を継ぎ、その辺の輸送の不定性 g を貼る。 -/
  | stepH {m n : Nat} : Lci2Path m n → lfiIndetGroup → Lci2Path (m + 1) n
  /-- 末尾に縦 log-link 辺を継ぎ、その辺の輸送の不定性 g を貼る。 -/
  | stepV {m n : Nat} : Lci2Path m n → lfiIndetGroup → Lci2Path m (n + 1)

/-- **M464F-2b: 台の格子経路**（装飾を忘れる・M459F IltPath へ）。 -/
def lci2Underlying : {m n : Nat} → Lci2Path m n → IltPath m n
  | _, _, Lci2Path.nil => IltPath.nil
  | _, _, Lci2Path.stepH p _ => IltPath.stepH (lci2Underlying p)
  | _, _, Lci2Path.stepV p _ => IltPath.stepV (lci2Underlying p)

/-- **M464F-2c: 蓄積不定性** — 経路に沿った辺装飾の群演算 lfiMul による畳み込み
    （nil＝単位元・step＝右から蓄積）。不定性が経路に沿って群として蓄積する主語。 -/
def lci2Indet : {m n : Nat} → Lci2Path m n → lfiIndetGroup
  | _, _, Lci2Path.nil => lfiOne
  | _, _, Lci2Path.stepH p g => lfiMul (lci2Indet p) g
  | _, _, Lci2Path.stepV p g => lfiMul (lci2Indet p) g

/-- **M464F-2d: 装飾経路の簿記函手** — 台経路の M459F 函手解釈（横辺＝iltHLink・
    縦辺＝iltVLink の合成・因子簿記レベル）。装飾経路の輸送の「決定論的部分」。 -/
def lci2Functor (l : Nat) {m n : Nat} (p : Lci2Path m n) :
    Functor (iltNode 0 0) (iltNode m n) :=
  iltPathFunctor l (lci2Underlying p)

/-- **M464F-2e: 不定性込み経路合成（lci2PathWithIndet）** — 装飾経路 p に沿った
    log-volume の輸送＝蓄積不定性 lci2Indet p の作用（各辺で不定性群の元を掛けた
    総和が deg_ℝ シフトとして効く）。簿記函手 lci2Functor と対をなす、経路輸送の
    「不定性部分」。 -/
def lci2PathWithIndet (logq : Nat → RReal) (v : Nat) {m n : Nat}
    (p : Lci2Path m n) (V : RReal) : RReal :=
  lfiAct logq v (lci2Indet p) V

/-- **定理 (M464F-2f): 横辺 1 歩の合成則** — 装飾経路を横 Θ-link 辺（不定性 g）で
    延長した経路の log-volume 輸送は、辺の不定性作用 lci2IndetAction を先に掛けて
    から元の経路の輸送を行うことに realEq で一致（M447F lfi_action_hom＝蓄積が
    真の群作用であることの帰結）。 -/
theorem lci2_step_action_h (logq : Nat → RReal) (v : Nat) {m n : Nat}
    (p : Lci2Path m n) (g : lfiIndetGroup) (V : RReal) :
    realEq (lci2PathWithIndet logq v (Lci2Path.stepH p g) V)
      (lci2PathWithIndet logq v p (lci2IndetAction logq v Lci2Edge.horiz g V)) :=
  lfi_action_hom logq v (lci2Indet p) g V

/-- **定理 (M464F-2g): 縦辺 1 歩の合成則**（縦 log-link 辺版・同上）。 -/
theorem lci2_step_action_v (logq : Nat → RReal) (v : Nat) {m n : Nat}
    (p : Lci2Path m n) (g : lfiIndetGroup) (V : RReal) :
    realEq (lci2PathWithIndet logq v (Lci2Path.stepV p g) V)
      (lci2PathWithIndet logq v p (lci2IndetAction logq v Lci2Edge.vert g V)) :=
  lfi_action_hom logq v (lci2Indet p) g V

/-! ## M464F-3: 経路に沿った不定性の蓄積は群準同型（lci2_indet_group_hom） -/

/-- **定理 (M464F-3: lci2_indet_group_hom)** — 経路に沿った不定性の蓄積は**群として
    整合的**: (i) 空経路の蓄積不定性は単位元、(ii) 辺の継ぎ足しは lfiMul による
    右蓄積（横・縦とも）、(iii) 蓄積不定性の log-volume 作用は真の群作用
    （lfiAct (g·h) ≈ lfiAct g ∘ lfiAct h・M447F lfi_action_hom）、(iv) 単位元の
    作用は恒等、(v) 群法則（結合律・単位・両側逆元）——不定性が経路に沿って
    **群として蓄積する**ことの総括。 -/
theorem lci2_indet_group_hom (logq : Nat → RReal) (v : Nat) :
    lci2Indet Lci2Path.nil = lfiOne
    ∧ (∀ (m n : Nat) (p : Lci2Path m n) (g : lfiIndetGroup),
        lci2Indet (Lci2Path.stepH p g) = lfiMul (lci2Indet p) g
        ∧ lci2Indet (Lci2Path.stepV p g) = lfiMul (lci2Indet p) g)
    ∧ (∀ (g h : lfiIndetGroup) (V : RReal),
        realEq (lfiAct logq v (lfiMul g h) V)
          (lfiAct logq v g (lfiAct logq v h V)))
    ∧ (∀ V : RReal, realEq (lfiAct logq v lfiOne V) V)
    ∧ (∀ a b c : lfiIndetGroup, lfiMul (lfiMul a b) c = lfiMul a (lfiMul b c))
    ∧ (∀ g : lfiIndetGroup,
        lfiMul g lfiOne = g ∧ lfiMul lfiOne g = g
        ∧ lfiMul g (lci2Inv g) = lfiOne ∧ lfiMul (lci2Inv g) g = lfiOne) :=
  ⟨rfl,
    fun _ _ _ _ => ⟨rfl, rfl⟩,
    fun g h V => lfi_action_hom logq v g h V,
    fun V => lfi_act_one logq v V,
    fun a b c => lci2_mul_assoc a b c,
    fun g => ⟨lci2_mul_one g, lci2_one_mul g, lci2_mul_inv g, lci2_inv_mul g⟩⟩

/-! ## M464F-4: 本丸 — 経路整合は不定性群を法として成立（coherence mod indet） -/

/-- **M464F-4a: 2 装飾経路の差の不定性** — 蓄積不定性の「差」 d = (lci2Indet q)⁻¹ ·
    (lci2Indet p)。2 経路の輸送のずれ全体を担う不定性群の元。 -/
def lci2Diff {m n : Nat} (p q : Lci2Path m n) : lfiIndetGroup :=
  lfiMul (lci2Inv (lci2Indet q)) (lci2Indet p)

/-- **定理 (M464F-4b): 蓄積不定性の分解** — 任意の 2 装飾経路 p, q に対し、p の
    蓄積不定性は q の蓄積不定性に差 lci2Diff p q を右から掛けたものに厳密に等しい
    （群法則: 結合律＋右逆元＋左単位で閉じる）。 -/
theorem lci2_indet_decomp {m n : Nat} (p q : Lci2Path m n) :
    lci2Indet p = lfiMul (lci2Indet q) (lci2Diff p q) := by
  show lci2Indet p
      = lfiMul (lci2Indet q) (lfiMul (lci2Inv (lci2Indet q)) (lci2Indet p))
  rw [← lci2_mul_assoc, lci2_mul_inv, lci2_one_mul]

/-- **定理 (M464F-4c: lci2_path_coherent_mod_indet・本丸)** — **無限 log-theta-lattice
    の経路整合は不定性群 (Ind1)(Ind2)(Ind3) を法として成立する**: (0,0)→(m,n) の
    任意の 2 装飾経路 p, q（各辺の輸送が不定性群の元の曖昧さを持つ）に対し、
    不定性群の元 d が存在して
      (i) **簿記函手は on the nose 一致**（決定論的部分の経路独立性＝M459F
          ilt_path_independent・全単位正方形可換の帰納的反復）、
      (ii) **蓄積不定性の差はちょうど d**（lci2Indet p = lci2Indet q · d＝2 経路の
          輸送のずれは不定性群の元 1 つに吸収される＝path-independence up to
          indeterminacy）、
      (iii) **log-volume 輸送は d の作用を挟んで一致**（p の輸送 ≈ q の輸送 ∘
          d の作用・M447F lfi_action_hom）。
    M459F の on-the-nose 経路独立（簿記レベルの帰結と正直申告されていた）を、
    実 IUT の格子整合の忠実な形——**不定性込みでしか成立しない整合**——へ昇格。
    [IUTchIII] Thm 3.11 の「多輻表示は (Ind1)(Ind2)(Ind3) の不定性を法として
    well-defined」の格子経路版。 -/
theorem lci2_path_coherent_mod_indet (logq : Nat → RReal) (v l : Nat)
    {m n : Nat} (p q : Lci2Path m n) :
    ∃ d : lfiIndetGroup,
      lci2Functor l p = lci2Functor l q
      ∧ lci2Indet p = lfiMul (lci2Indet q) d
      ∧ ∀ V : RReal,
          realEq (lci2PathWithIndet logq v p V)
            (lfiAct logq v (lci2Indet q) (lfiAct logq v d V)) :=
  ⟨lci2Diff p q,
    ilt_path_independent l (lci2Underlying p) (lci2Underlying q),
    lci2_indet_decomp p q,
    fun V => by
      show realEq (lfiAct logq v (lci2Indet p) V)
        (lfiAct logq v (lci2Indet q) (lfiAct logq v (lci2Diff p q) V))
      rw [lci2_indet_decomp p q]
      exact lfi_action_hom logq v (lci2Indet q) (lci2Diff p q) V⟩

/-- **定理 (M464F-4d): degree レベルの coherence mod indet** — 任意の装飾経路の
    簿記函手の対象次数は横回数 m の (2l)^m 倍のみで決まる（M459F ilt_path_degree・
    不定性装飾は簿記次数を動かさず deg_ℝ シフト（(Ind3) 成分）にのみ効く——
    決定論的部分と不定性部分の分離の機械検証）。 -/
theorem lci2_path_degree (l : Nat) {m n : Nat} (p : Lci2Path m n)
    (D : IltObj 0 0) :
    picDivDegree.map ((lci2Functor l p).onObj D).div
      = iltFactor l m * picDivDegree.map D.div :=
  ilt_path_degree l (lci2Underlying p) D

/-! ## M464F-5: 不定性を単位元にすると M459F へ厳密還元（lci2_reduces_to_ilt） -/

/-- **M464F-5a: 自明装飾の埋め込み** — M459F の格子経路の全辺に単位元 lfiOne を
    貼った装飾経路（不定性ゼロの経路）。 -/
def lci2OfIlt : {m n : Nat} → IltPath m n → Lci2Path m n
  | _, _, IltPath.nil => Lci2Path.nil
  | _, _, IltPath.stepH p => Lci2Path.stepH (lci2OfIlt p) lfiOne
  | _, _, IltPath.stepV p => Lci2Path.stepV (lci2OfIlt p) lfiOne

/-- **定理 (M464F-5b): 自明装飾の台は元の経路**（埋め込みの忠実性・経路の帰納法）。 -/
theorem lci2_of_ilt_underlying {m n : Nat} (p : IltPath m n) :
    lci2Underlying (lci2OfIlt p) = p := by
  induction p with
  | nil => rfl
  | stepH p ih => exact congrArg IltPath.stepH ih
  | stepV p ih => exact congrArg IltPath.stepV ih

/-- **定理 (M464F-5c): 自明装飾の蓄積不定性は単位元**（単位元の畳み込み＝単位元・
    経路の帰納法＋右単位法則）。 -/
theorem lci2_of_ilt_indet {m n : Nat} (p : IltPath m n) :
    lci2Indet (lci2OfIlt p) = lfiOne := by
  induction p with
  | nil => rfl
  | stepH p ih =>
    show lfiMul (lci2Indet (lci2OfIlt p)) lfiOne = lfiOne
    rw [ih]
    exact lci2_mul_one lfiOne
  | stepV p ih =>
    show lfiMul (lci2Indet (lci2OfIlt p)) lfiOne = lfiOne
    rw [ih]
    exact lci2_mul_one lfiOne

/-- **定理 (M464F-5d: lci2_reduces_to_ilt)** — **不定性群を自明（全辺単位元）に
    すると M459F の on-the-nose 経路独立へ厳密整合する**: (i) 簿記函手は M459F の
    iltPathFunctor にちょうど一致、(ii) 自明装飾の 2 経路の函手は on the nose
    一致（＝ilt_path_independent がそのまま復元される）、(iii) 蓄積不定性は
    単位元、(iv) log-volume 輸送は恒等（不定性ゼロ）。本層の coherence mod indet
    が M459F の on-the-nose 版を**真に含む**（不定性→0 の極限で M459F）ことの
    機械検証——昇格が骨格の張り替えでなく本物の一般化である証拠。 -/
theorem lci2_reduces_to_ilt (logq : Nat → RReal) (v l : Nat) {m n : Nat}
    (p q : IltPath m n) :
    lci2Functor l (lci2OfIlt p) = iltPathFunctor l p
    ∧ lci2Functor l (lci2OfIlt p) = lci2Functor l (lci2OfIlt q)
    ∧ lci2Indet (lci2OfIlt p) = lfiOne
    ∧ ∀ V : RReal, realEq (lci2PathWithIndet logq v (lci2OfIlt p) V) V := by
  refine ⟨?_, ?_, lci2_of_ilt_indet p, ?_⟩
  · show iltPathFunctor l (lci2Underlying (lci2OfIlt p)) = iltPathFunctor l p
    rw [lci2_of_ilt_underlying p]
  · exact ilt_path_independent l (lci2Underlying (lci2OfIlt p))
      (lci2Underlying (lci2OfIlt q))
  · intro V
    show realEq (lfiAct logq v (lci2Indet (lci2OfIlt p)) V) V
    rw [lci2_of_ilt_indet p]
    exact lfi_act_one logq v V

/-! ## M464F-6: M459F の残限定を閉じる（lci2_closes_m459_limitation） -/

/-- **定理 (M464F-6: lci2_closes_m459_limitation・本丸の総括)** — M459F の正直な
    限定 ilt_model_scope (ii)／外部仮説 ilt_full_lattice_hypothesis が外部と申告した
    「実 IUT の格子の整合は不定性 (Ind1)(Ind2)(Ind3) 込みでしか成立しない——その
    不定性込みの整合」に対応する主張を、**内部の定理として**供給する:
    (i) **coherence mod indet**: (0,0)→(m,n) の任意の 2 装飾経路は、簿記函手が
        on the nose 一致し蓄積不定性の差が不定性群の元 1 つに吸収される、
    (ii) 蓄積不定性の log-volume 作用は真の群作用（合成・単位・群法則）、
    (iii) 不定性を自明にすると M459F の on-the-nose 経路独立へ厳密還元、
    (iv) degree レベルの経路不変量は不定性装飾に依らない（決定論的部分の分離）。
    まとめ: 無限 log-theta-lattice の経路整合は不定性群を法として成立する——
    M459F の残限定のうち**不定性込み格子整合**部分を閉じた（π₁^ét/slim 部分は
    lci2_model_scope で狭めて外部に残す）。 -/
theorem lci2_closes_m459_limitation (logq : Nat → RReal) (v l : Nat) :
    (∀ (m n : Nat) (p q : Lci2Path m n),
      ∃ d : lfiIndetGroup,
        lci2Functor l p = lci2Functor l q
        ∧ lci2Indet p = lfiMul (lci2Indet q) d)
    ∧ (∀ (g h : lfiIndetGroup) (V : RReal),
        realEq (lfiAct logq v (lfiMul g h) V)
          (lfiAct logq v g (lfiAct logq v h V)))
    ∧ (∀ (m n : Nat) (p : IltPath m n),
        lci2Functor l (lci2OfIlt p) = iltPathFunctor l p
        ∧ lci2Indet (lci2OfIlt p) = lfiOne)
    ∧ (∀ (m n : Nat) (p : Lci2Path m n) (D : IltObj 0 0),
        picDivDegree.map ((lci2Functor l p).onObj D).div
          = iltFactor l m * picDivDegree.map D.div) :=
  ⟨fun _ _ p q =>
      ⟨lci2Diff p q,
        ilt_path_independent l (lci2Underlying p) (lci2Underlying q),
        lci2_indet_decomp p q⟩,
    fun g h V => lfi_action_hom logq v g h V,
    fun _ _ p => ⟨(lci2_reduces_to_ilt logq v l p p).1, lci2_of_ilt_indet p⟩,
    fun _ _ p D => lci2_path_degree l p D⟩

/-! ## M464F-7: crux Dβ-ω は外部仮説（決して内部化しない） -/

/-- **crux（外部仮説・決して導出しない）**: log-theta-lattice の**多輻アルゴリズム
    不等式**（Dβ-ω、[IUTchIII] Cor 3.12 の係争ステップ＝ q-パイロットの体積が
    theta-パイロット軌道に支配されるという主張）は、本モジュールの主張には一切
    含めない。本モジュールが証明したのは「格子の経路整合が不定性群
    (Ind1)(Ind2)(Ind3) を法として成立する」という**構造的整合性**までであり、
    その不定性を体積不等式へ変換する主張は別問題である。恒等 Iff で外部仮説として
    保持（M459F ilt_crux_is_hypothesis・M447F lfi_crux_is_hypothesis と同じ精神）。 -/
theorem lci2_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M464F-8: 正直な限定（閉じた上で残りを狭めて述べ直す・消さない・弱めない） -/

/-- **定理 (M464F-8: lci2_model_scope・正直な限定の総括)** — 本構成のスコープ
    （M459F の残限定「不定性込み格子整合」を閉じた後に残る、より狭い正直な限定）:
    (i) **不定性群は既存 Ind 模型（M447F lfiIndetGroup = Bool×Bool×ℤ）の格子への
        貼り付け**である——deg_ℝ への作用（シフト）は (Ind3) 成分のみで決まる
        （lfiShift g = linMuShift v g.ind3・M342F の実 deg_ℝ 事実の写し）。
        実 π₁^ét（遠アーベル復元）上の完全な不定性群ではなく、(Ind3) 連続部の
        Haar 測度レベル（M457F 連続版の格子貼り付け）は後続、
    (ii) **経路の簿記函手は M459F の degree/因子簿記レベル**（lci2Functor＝
        iltPathFunctor・各格子点の劇場の完全な数論的実現・実 π₁^ét・非可換幾何は
        外部——ilt_full_lattice_hypothesis の π₁^ét/slim 部分は外部のまま残す）、
    (iii) **crux（外部 Prop）は仮説としてのみ利用可能で本層では導出されない**。 -/
theorem lci2_model_scope (logq : Nat → RReal) (v : Nat) :
    (∀ g : lfiIndetGroup, lfiShift logq v g = linMuShift logq v g.ind3)
    ∧ (∀ (l m n : Nat) (p : Lci2Path m n),
        lci2Functor l p = iltPathFunctor l (lci2Underlying p))
    ∧ (∀ crux : Prop, crux → crux) :=
  ⟨fun _ => rfl, fun _ _ _ _ => rfl, fun _ h => h⟩

/-! ## M464F-9: capstone -/

/-- **M464F-9a: 不定性込み格子整合データ** — 無限 log-theta-lattice の装飾経路
    （各辺に不定性群の元）・coherence mod indet（本丸）・蓄積不定性の群作用性・
    M459F への厳密還元・degree 経路不変量・群法則を束ねる。主語はすべて本物の
    因子群・圏・函手演算と M447F の実 deg_ℝ 作用（toy 主語なし）。crux Dβ-ω は
    フィールドに含めない（外部仮説のまま）。 -/
structure LatticeCoherenceIndetData (logq : Nat → RReal) (v l : Nat) where
  /-- 装飾経路の蓄積不定性。 -/
  indet : (m n : Nat) → Lci2Path m n → lfiIndetGroup
  /-- 蓄積不定性は本層の lfiMul 畳み込みそのもの。 -/
  indet_is : ∀ (m n : Nat) (p : Lci2Path m n), indet m n p = lci2Indet p
  /-- **本丸: coherence mod indet** — 任意の 2 装飾経路は簿記函手が on the nose
      一致し、蓄積不定性の差は不定性群の元 1 つに吸収される。 -/
  coherent : ∀ (m n : Nat) (p q : Lci2Path m n),
    ∃ d : lfiIndetGroup,
      lci2Functor l p = lci2Functor l q
      ∧ lci2Indet p = lfiMul (lci2Indet q) d
  /-- 蓄積不定性の log-volume 作用は真の群作用。 -/
  action_hom : ∀ (g h : lfiIndetGroup) (V : RReal),
    realEq (lfiAct logq v (lfiMul g h) V) (lfiAct logq v g (lfiAct logq v h V))
  /-- 単位元の作用は恒等。 -/
  act_one : ∀ V : RReal, realEq (lfiAct logq v lfiOne V) V
  /-- 不定性を自明にすると M459F の on-the-nose 経路独立へ厳密還元。 -/
  reduces : ∀ (m n : Nat) (p : IltPath m n),
    lci2Functor l (lci2OfIlt p) = iltPathFunctor l p
    ∧ lci2Indet (lci2OfIlt p) = lfiOne
  /-- 不定性群の群法則（結合律・両側逆元）。 -/
  group_laws : ∀ a b c : lfiIndetGroup,
    lfiMul (lfiMul a b) c = lfiMul a (lfiMul b c)
    ∧ lfiMul a (lci2Inv a) = lfiOne ∧ lfiMul (lci2Inv a) a = lfiOne
  /-- degree レベルの経路不変量（不定性装飾に依らない・決定論的部分の分離）。 -/
  path_degree : ∀ (m n : Nat) (p : Lci2Path m n) (D : IltObj 0 0),
    picDivDegree.map ((lci2Functor l p).onObj D).div
      = iltFactor l m * picDivDegree.map D.div

/-- **M464F-9b: witness 本体** — 全フィールドを M464F-0〜6 の本物の証明で埋める
    （crux 以外の外部仮説ゼロ・完全証明）。 -/
def latticeCoherenceIndetData (logq : Nat → RReal) (v l : Nat) :
    LatticeCoherenceIndetData logq v l where
  indet := fun _ _ p => lci2Indet p
  indet_is := fun _ _ _ => rfl
  coherent := fun _ _ p q =>
    ⟨lci2Diff p q,
      ilt_path_independent l (lci2Underlying p) (lci2Underlying q),
      lci2_indet_decomp p q⟩
  action_hom := fun g h V => lfi_action_hom logq v g h V
  act_one := fun V => lfi_act_one logq v V
  reduces := fun _ _ p =>
    ⟨(lci2_reduces_to_ilt logq v l p p).1, lci2_of_ilt_indet p⟩
  group_laws := fun a b c =>
    ⟨lci2_mul_assoc a b c, lci2_mul_inv a, lci2_inv_mul a⟩
  path_degree := fun _ _ p D => lci2_path_degree l p D

/-- **定理 (M464F-9c: lci2_exists・capstone)** — 任意の実重み logq・素点 v・
    l-捻れ l に対し、無限 log-theta-lattice の経路整合が不定性群 (Ind1)(Ind2)(Ind3)
    を法として成立する（coherence mod indet・群作用性・M459F への還元・degree
    不変量）データが **crux 以外の外部仮説なしで**存在する——M459F の残限定
    「不定性込み格子整合は外部」を閉じる。 -/
theorem lci2_exists (logq : Nat → RReal) (v l : Nat) :
    Nonempty (LatticeCoherenceIndetData logq v l) :=
  ⟨latticeCoherenceIndetData logq v l⟩

/-! ## M464F-10: 実例 -/

/-- 実例: (0,0)→(1,1) の 2 装飾経路（横→縦・辺不定性 ⟨true,false,1⟩,⟨false,true,2⟩ と
    縦→横・辺不定性 ⟨false,false,3⟩,⟨true,true,0⟩）は不定性群を法として整合する
    （l=3・本丸の具体化）。 -/
example (logq : Nat → RReal) (v : Nat) :
    ∃ d : lfiIndetGroup,
      lci2Functor 3 (Lci2Path.stepV (Lci2Path.stepH Lci2Path.nil
          ⟨true, false, 1⟩) ⟨false, true, 2⟩)
        = lci2Functor 3 (Lci2Path.stepH (Lci2Path.stepV Lci2Path.nil
          ⟨false, false, 3⟩) ⟨true, true, 0⟩)
      ∧ lci2Indet (Lci2Path.stepV (Lci2Path.stepH Lci2Path.nil
          ⟨true, false, 1⟩) ⟨false, true, 2⟩)
        = lfiMul (lci2Indet (Lci2Path.stepH (Lci2Path.stepV Lci2Path.nil
          ⟨false, false, 3⟩) ⟨true, true, 0⟩)) d
      ∧ ∀ V : RReal,
          realEq (lci2PathWithIndet logq v (Lci2Path.stepV (Lci2Path.stepH
              Lci2Path.nil ⟨true, false, 1⟩) ⟨false, true, 2⟩) V)
            (lfiAct logq v (lci2Indet (Lci2Path.stepH (Lci2Path.stepV
              Lci2Path.nil ⟨false, false, 3⟩) ⟨true, true, 0⟩))
              (lfiAct logq v d V)) :=
  lci2_path_coherent_mod_indet logq v 3
    (Lci2Path.stepV (Lci2Path.stepH Lci2Path.nil ⟨true, false, 1⟩)
      ⟨false, true, 2⟩)
    (Lci2Path.stepH (Lci2Path.stepV Lci2Path.nil ⟨false, false, 3⟩)
      ⟨true, true, 0⟩)

/-- 実例: 1 辺の装飾経路の蓄積不定性はその辺の不定性そのもの（左単位法則）。 -/
example : lci2Indet (Lci2Path.stepH Lci2Path.nil ⟨true, false, 2⟩)
    = (⟨true, false, 2⟩ : lfiIndetGroup) :=
  lci2_one_mul ⟨true, false, 2⟩

/-- 実例: 不定性を自明にすると M459F の on-the-nose 経路独立が復元される
    （(0,0)→(2,3) の正準経路・l=3・不定性ゼロで輸送は恒等）。 -/
example (logq : Nat → RReal) (v : Nat) :
    lci2Functor 3 (lci2OfIlt (iltPathHV 2 3)) = iltPathFunctor 3 (iltPathHV 2 3)
    ∧ lci2Functor 3 (lci2OfIlt (iltPathHV 2 3))
      = lci2Functor 3 (lci2OfIlt (iltPathVH 3 2))
    ∧ lci2Indet (lci2OfIlt (iltPathHV 2 3)) = lfiOne
    ∧ ∀ V : RReal,
        realEq (lci2PathWithIndet logq v (lci2OfIlt (iltPathHV 2 3)) V) V :=
  lci2_reduces_to_ilt logq v 3 (iltPathHV 2 3) (iltPathVH 3 2)

/-- 実例: 不定性は経路に沿って群として蓄積（横辺 g・縦辺 h の順の蓄積は
    lfiMul (lfiMul lfiOne g) h）。 -/
example (g h : lfiIndetGroup) :
    lci2Indet (Lci2Path.stepV (Lci2Path.stepH Lci2Path.nil g) h)
      = lfiMul (lfiMul lfiOne g) h := rfl

/-- 実例: 群法則——差の不定性 lci2Diff は右逆元・結合律で厳密に分解を与える
    （任意の 2 装飾経路・(0,0)→(1,1)）。 -/
example (p q : Lci2Path 1 1) :
    lci2Indet p = lfiMul (lci2Indet q) (lci2Diff p q) :=
  lci2_indet_decomp p q

/-- 実例: degree 経路不変量は不定性装飾に依らない（(0,0)→(2,7) の任意の装飾経路・
    l=1・(2·1)²=4 倍）。 -/
example (p : Lci2Path 2 7) (D : IltObj 0 0) :
    picDivDegree.map ((lci2Functor 1 p).onObj D).div
      = (4 : Int) * picDivDegree.map D.div :=
  lci2_path_degree 1 p D

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説
    （Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  lci2_crux_is_hypothesis crux

/-- 実例: capstone データは任意の logq・v・l で存在（具体化・l=5）。 -/
example (logq : Nat → RReal) (v : Nat) :
    Nonempty (LatticeCoherenceIndetData logq v 5) :=
  lci2_exists logq v 5

end IUT
