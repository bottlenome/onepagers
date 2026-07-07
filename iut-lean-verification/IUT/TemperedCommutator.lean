-- M379F TemperedCommutator [実・本物・柱A]
-- complete_pct 影響: 柱A で M374F の本物の被覆塔（deck 群 ℤ/l^n の逆系・逆極限 ℤ_l）の
--   交換子/アーベル化構造を本物で建設＝各段 ℤ/l^n と極限 ℤ_l が可換（交換子自明）・各段
--   射影が交換子を潰す（アーベル化を経由）・deck 共役作用が自明かつ遷移射と同変であることを完全証明。
-- 正直な限定: 完全な幾何的 tempered π₁^temp（Δ^temp）は非可換・slim であり、ここで扱うのは
--   その最大 pro-l アーベル商 = ℤ_l 塔のみ。非可換テータ構造・slim 遠アーベル性は外部（幾何的入力・後続）。

/-
  IUT/TemperedCommutator.lean — M379F [実／本物]
  分類: 実 (tempered 被覆塔 deck 群 ℤ/l^n・逆極限 ℤ_l の交換子/アーベル化・共役作用)

  M374F (IUT/TemperedTower.lean) が構成した本物の被覆塔＝deck 群 ℤ/l^n の逆系（遷移 mod l^n
  還元）とその逆極限 ℤ_l = lim ℤ/l^n の上で、Galois/deck **作用**とその**交換子構造**を次段として
  建設する。各段 ℤ/l^n は下部の整数表現の加法 Int.add_comm により可換であり、塔全体が可換
  ⇒ 極限 ℤ_l も可換。ゆえに:
    * deck 群 ℤ/l^n の交換子 [x,y] = x y x⁻¹ y⁻¹ は自明（本物・Int.add_comm から）
    * 極限 ℤ_l の交換子も自明（成分ごとの可換性から）
    * 極限から各段への射影 ℤ_l ↠ ℤ/l^n は交換子を潰す（アーベル化を経由する）
    * deck 共役作用 conj_g は自明（内部作用が消える＝塔が可換）で、塔の遷移射と同変
    * 射影の錐は遷移射と整合（ℤ_l 作用が遷移と可換）
  主語はすべて本物の商群 ℤ/l^n・本物の逆極限 ℤ_l（toy 代理・toy 群なし）。
-/
import IUT.TemperedTower

namespace IUT

/-! ## M379F-1: 可換性と交換子の一般的枠組み（本物の群 ℤ/l^n・ℤ_l に適用する道具）

  交換子 [x,y] = x·y·x⁻¹·y⁻¹ と共役 conj_g(x) = g·x·g⁻¹ を M9 の `Grp` 上で定義し、
  可換群では両者がそれぞれ自明・恒等になることを群公理のみから証明する。以降これを本物の
  deck 群 ℤ/l^n と逆極限 ℤ_l に適用する（代理群を主語にしない）。 -/

/-- **M379F-1a: 交換子** [x,y] = x·y·x⁻¹·y⁻¹（M9 `Grp` 上）。 -/
def tcmCommutator (G : Grp) (x y : G.carrier) : G.carrier :=
  G.mul (G.mul (G.mul x y) (G.inv x)) (G.inv y)

/-- **M379F-1b: 共役** conj_g(x) = g·x·g⁻¹（deck 作用の内部自己同型）。 -/
def tcmConj (G : Grp) (g x : G.carrier) : G.carrier :=
  G.mul (G.mul g x) (G.inv g)

/-- **M379F-1c: 可換群の述語** ∀ x y, x·y = y·x。 -/
def tcmAbelian (G : Grp) : Prop :=
  ∀ x y : G.carrier, G.mul x y = G.mul y x

/-- **定理 (M379F-1d): 可換 ⇒ 交換子自明** [x,y] = 1（群公理のみ）。 -/
theorem tcm_commutator_trivial_of_abelian (G : Grp) (h : tcmAbelian G)
    (x y : G.carrier) : tcmCommutator G x y = G.one := by
  show G.mul (G.mul (G.mul x y) (G.inv x)) (G.inv y) = G.one
  rw [h x y, G.mul_assoc y x (G.inv x), G.mul_inv, G.mul_one, G.mul_inv]

/-- **定理 (M379F-1e): 可換 ⇒ 共役自明** conj_g(x) = x（内部作用が消える）。 -/
theorem tcm_conj_trivial_of_abelian (G : Grp) (h : tcmAbelian G)
    (g x : G.carrier) : tcmConj G g x = x := by
  show G.mul (G.mul g x) (G.inv g) = x
  rw [h g x, G.mul_assoc, G.mul_inv, G.mul_one]

/-! ## M379F-2: 各段の deck 群 ℤ/l^n は可換（本物・Int.add_comm から）

  塔の第 n 段 deck 群 `ttwDeckTower l n = zmod (l^n)` は、下部の整数代表元の加法の可換性
  （Int.add_comm）から可換群である。塔が本当にアーベル被覆塔であることの本物の内容。 -/

/-- **定理 (M379F-2a): ℤ/n は可換**（代表元の加法 Int.add_comm から本物で）。 -/
theorem tcm_zmod_abelian (n : Nat) : tcmAbelian (zmod n) := by
  intro x y
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  show Quot.mk (modCong n).rel (a + b) = Quot.mk (modCong n).rel (b + a)
  rw [Int.add_comm]

/-- **定理 (M379F-2b): 塔の各段 deck 群 ℤ/l^n は可換**。 -/
theorem tcm_deck_abelian (l n : Nat) : tcmAbelian (ttwDeckTower l n) :=
  tcm_zmod_abelian (l ^ n)

/-- **定理 (M379F-2c): 塔の deck 群の交換子は自明** [x,y] = 1_{ℤ/l^n}。
    被覆塔が各段でアーベルである（テータ被覆塔の deck 群 ℤ/l^n が可換）ことの本物の証明。 -/
theorem tcm_deck_commutator_trivial (l n : Nat) (x y : (ttwDeckTower l n).carrier) :
    tcmCommutator (ttwDeckTower l n) x y = (ttwDeckTower l n).one :=
  tcm_commutator_trivial_of_abelian (ttwDeckTower l n) (tcm_deck_abelian l n) x y

/-- **定理 (M379F-2d): 塔の deck 共役作用は自明** conj_g(x) = x（内部 deck 作用が消える）。 -/
theorem tcm_deck_conj_trivial (l n : Nat) (g x : (ttwDeckTower l n).carrier) :
    tcmConj (ttwDeckTower l n) g x = x :=
  tcm_conj_trivial_of_abelian (ttwDeckTower l n) (tcm_deck_abelian l n) g x

/-! ## M379F-3: 逆極限 ℤ_l も可換（成分ごとの可換性から）

  可換群の逆系の逆極限は可換。ℤ_l = lim ℤ/l^n は各成分 ℤ/l^n が可換ゆえ可換群であり、
  その交換子・共役作用も自明である。塔の極限が可換であることの本物の内容。 -/

/-- **定理 (M379F-3a): 逆極限 ℤ_l は可換**（成分 ℤ/l^n の可換性を成分ごとに束ねる）。 -/
theorem tcm_limit_abelian (l : Nat) : tcmAbelian (ttwInverseLimit l) := by
  intro x y
  apply Subtype.ext
  funext n
  exact tcm_zmod_abelian (l ^ n) (x.val n) (y.val n)

/-- **定理 (M379F-3b): 逆極限 ℤ_l の交換子は自明** [x,y] = 1_{ℤ_l}。 -/
theorem tcm_limit_commutator_trivial (l : Nat) (x y : (ttwInverseLimit l).carrier) :
    tcmCommutator (ttwInverseLimit l) x y = (ttwInverseLimit l).one :=
  tcm_commutator_trivial_of_abelian (ttwInverseLimit l) (tcm_limit_abelian l) x y

/-- **定理 (M379F-3c): 逆極限 ℤ_l の共役作用は自明** conj_a(x) = x（ℤ_l の内部作用が消える）。 -/
theorem tcm_limit_conj_trivial (l : Nat) (a x : (ttwInverseLimit l).carrier) :
    tcmConj (ttwInverseLimit l) a x = x :=
  tcm_conj_trivial_of_abelian (ttwInverseLimit l) (tcm_limit_abelian l) a x

/-! ## M379F-4: 極限の各段への射影は交換子を潰す（アーベル化を経由）

  射影 ℤ_l ↠ ℤ/l^n（M374F `ttwLimitProj`）は準同型で、極限が可換ゆえ交換子を単位元へ送る。
  これは「ℤ_l 上の deck 作用がアーベル商を経由して各段に降りる」ことの本物の内容。 -/

/-- **定理 (M379F-4a): 射影は交換子を潰す** proj_n([x,y]) = 1_{ℤ/l^n}。
    極限の交換子が自明ゆえ、各段への射影はアーベル化を経由する（可換商への降下）。 -/
theorem tcm_proj_kills_commutator (l n : Nat) (x y : (ttwInverseLimit l).carrier) :
    (ttwLimitProj l n).map (tcmCommutator (ttwInverseLimit l) x y) = (ttwDeckTower l n).one := by
  rw [tcm_limit_commutator_trivial]
  exact (ttwLimitProj l n).map_one

/-! ## M379F-5: deck 共役作用は塔の遷移射と同変（equivariance）

  遷移射 t_n : ℤ/l^{n+1} → ℤ/l^n は準同型ゆえ共役作用と同変する:
  t_n(conj_g(x)) = conj_{t_n g}(t_n x)。これは deck 作用が塔全体で整合する
  （塔の各段の被覆変換が遷移と両立する）本物の内容。 -/

/-- **定理 (M379F-5a): 共役作用は遷移射と同変** t_n(g·x·g⁻¹) = (t_n g)·(t_n x)·(t_n g)⁻¹。 -/
theorem tcm_transition_conj (l n : Nat) (g x : (ttwDeckTower l (n + 1)).carrier) :
    (ttwTransition l n).map (tcmConj (ttwDeckTower l (n + 1)) g x)
      = tcmConj (ttwDeckTower l n) ((ttwTransition l n).map g) ((ttwTransition l n).map x) := by
  show (ttwTransition l n).map
        ((ttwDeckTower l (n + 1)).mul
          ((ttwDeckTower l (n + 1)).mul g x) ((ttwDeckTower l (n + 1)).inv g))
      = (ttwDeckTower l n).mul
          ((ttwDeckTower l n).mul ((ttwTransition l n).map g) ((ttwTransition l n).map x))
          ((ttwDeckTower l n).inv ((ttwTransition l n).map g))
  rw [(ttwTransition l n).map_mul, (ttwTransition l n).map_mul, (ttwTransition l n).map_inv]

/-- **定理 (M379F-5b): ℤ_l 作用は遷移射と整合**（射影の錐＝ℤ_l の各段作用が遷移と可換）。
    M374F `ttw_limit_proj_compat` の作用としての読み替え。 -/
theorem tcm_action_commutes (l : Nat) {i j : Nat} (h : i ≤ j)
    (x : (ttwInverseLimit l).carrier) :
    (zmodTrans (pow_dvd_mono l h)).map ((ttwLimitProj l j).map x) = (ttwLimitProj l i).map x :=
  ttw_limit_proj_compat l h x

/-! ## M379F-6: 正直な外部仮説（決して導出しない） -/

/-- **外部仮説（正直な限定・決して導出しない）**: 完全な幾何的 tempered 基本群 Δ^temp は
    **非可換**（テータ被覆に付随する非可換 pro-Σ 構造）であり、本モジュールで扱う可換な ℤ_l 塔は
    その**最大 pro-l アーベル商**にすぎない。Δ^temp の非可換性・slim 遠アーベル性
    （[SemiAnbd] André–Mochizuki）は本質的に外部（幾何的入力・後続）。 -/
def tcm_full_tempered_nonabelian_hypothesis (T : Grp) : Prop := ¬ tcmAbelian T

/-! ## M379F-7: capstone -/

/-- **M379F-7a: tempered 被覆塔の交換子/アーベル化データ** — 被覆度 l・各段 deck 群 ℤ/l^n の
    可換性と交換子自明・逆極限 ℤ_l の可換性と交換子自明・各段射影が交換子を潰す（アーベル化経由）・
    deck 共役作用の自明性（ℤ_l 内部作用が消える）・共役作用の遷移同変性・射影の遷移整合を束ねる。
    主語は本物の商群 ℤ/l^n・本物の逆極限 ℤ_l（toy 代理・toy 群なし）。 -/
structure TemperedCommutatorData (l : Nat) where
  /-- 被覆度 l ≥ 2。 -/
  hl : 2 ≤ l
  /-- 逆極限が本物の ℤ_l。 -/
  limit_isLadic : ttwInverseLimit l = Zp l
  /-- 各段 deck 群 ℤ/l^n は可換。 -/
  deck_abelian : ∀ n, tcmAbelian (ttwDeckTower l n)
  /-- 各段 deck 群の交換子は自明。 -/
  deck_commutator_trivial : ∀ (n : Nat) (x y : (ttwDeckTower l n).carrier),
    tcmCommutator (ttwDeckTower l n) x y = (ttwDeckTower l n).one
  /-- 逆極限 ℤ_l は可換。 -/
  limit_abelian : tcmAbelian (ttwInverseLimit l)
  /-- 逆極限 ℤ_l の交換子は自明。 -/
  limit_commutator_trivial : ∀ (x y : (ttwInverseLimit l).carrier),
    tcmCommutator (ttwInverseLimit l) x y = (ttwInverseLimit l).one
  /-- 各段への射影は交換子を潰す（アーベル化を経由）。 -/
  proj_kills_commutator : ∀ (n : Nat) (x y : (ttwInverseLimit l).carrier),
    (ttwLimitProj l n).map (tcmCommutator (ttwInverseLimit l) x y) = (ttwDeckTower l n).one
  /-- deck 共役作用は自明（ℤ_l 内部作用が消える）。 -/
  conj_trivial : ∀ (a x : (ttwInverseLimit l).carrier), tcmConj (ttwInverseLimit l) a x = x
  /-- 共役作用は塔の遷移射と同変。 -/
  transition_equivariant : ∀ (n : Nat) (g x : (ttwDeckTower l (n + 1)).carrier),
    (ttwTransition l n).map (tcmConj (ttwDeckTower l (n + 1)) g x)
      = tcmConj (ttwDeckTower l n) ((ttwTransition l n).map g) ((ttwTransition l n).map x)
  /-- 射影の錐は遷移射と整合（ℤ_l 作用が遷移と可換）。 -/
  proj_compat : ∀ {i j : Nat} (h : i ≤ j) (x : (ttwInverseLimit l).carrier),
    (zmodTrans (pow_dvd_mono l h)).map ((ttwLimitProj l j).map x) = (ttwLimitProj l i).map x

/-- **M379F-7b: witness 本体** — 全フィールドを M379F-1〜5 の本物の証明で埋める
    （外部仮説ゼロ・完全証明）。 -/
def temperedCommutatorData (l : Nat) (hl : 2 ≤ l) : TemperedCommutatorData l where
  hl := hl
  limit_isLadic := rfl
  deck_abelian := fun n => tcm_deck_abelian l n
  deck_commutator_trivial := fun n => tcm_deck_commutator_trivial l n
  limit_abelian := tcm_limit_abelian l
  limit_commutator_trivial := fun x y => tcm_limit_commutator_trivial l x y
  proj_kills_commutator := fun n => tcm_proj_kills_commutator l n
  conj_trivial := fun a => tcm_limit_conj_trivial l a
  transition_equivariant := fun n => tcm_transition_conj l n
  proj_compat := fun h => tcm_action_commutes l h

/-- **定理 (M379F-7c): tempered 被覆塔の交換子/アーベル化データの存在** — 被覆度 l ≥ 2 が
    与えられれば、各段 ℤ/l^n・逆極限 ℤ_l の可換性・交換子自明・射影がアーベル化を経由・deck
    共役作用の自明性と遷移同変性を束ねたデータが**外部仮説なしで**存在する（完全証明）。 -/
theorem tcm_exists (l : Nat) (hl : 2 ≤ l) : Nonempty (TemperedCommutatorData l) :=
  ⟨temperedCommutatorData l hl⟩

/-! ## 実例（l = 5、塔 ℤ/5 → ℤ/25 → ℤ/125 → …、逆極限 ℤ_5） -/

/-- 実例: 被覆度 5 の交換子/アーベル化データが存在する。 -/
example : Nonempty (TemperedCommutatorData 5) := tcm_exists 5 (by omega)

/-- 実例: 第 2 段 deck 群 ℤ/25 は可換（Int.add_comm から本物で）。 -/
example : tcmAbelian (ttwDeckTower 5 2) := tcm_deck_abelian 5 2

/-- 実例: 逆極限 ℤ_5 の交換子は自明。 -/
example (x y : (ttwInverseLimit 5).carrier) :
    tcmCommutator (ttwInverseLimit 5) x y = (ttwInverseLimit 5).one :=
  tcm_limit_commutator_trivial 5 x y

/-- 実例: ℤ_5 の各段 ℤ/5^n への射影は交換子を潰す（アーベル化を経由）。 -/
example (n : Nat) (x y : (ttwInverseLimit 5).carrier) :
    (ttwLimitProj 5 n).map (tcmCommutator (ttwInverseLimit 5) x y) = (ttwDeckTower 5 n).one :=
  tcm_proj_kills_commutator 5 n x y

/-- 実例: deck 共役作用は遷移 ℤ/25 → ℤ/5 と同変（塔の被覆変換が遷移と両立）。 -/
example (g x : (ttwDeckTower 5 2).carrier) :
    (ttwTransition 5 1).map (tcmConj (ttwDeckTower 5 2) g x)
      = tcmConj (ttwDeckTower 5 1) ((ttwTransition 5 1).map g) ((ttwTransition 5 1).map x) :=
  tcm_transition_conj 5 1 g x

/-- 実例: ℤ_5 作用は遷移射と整合（射影の錐が遷移と可換）。 -/
example (x : (ttwInverseLimit 5).carrier) :
    (zmodTrans (pow_dvd_mono 5 (Nat.le_succ 1))).map ((ttwLimitProj 5 2).map x)
      = (ttwLimitProj 5 1).map x :=
  tcm_action_commutes 5 (Nat.le_succ 1) x

end IUT
