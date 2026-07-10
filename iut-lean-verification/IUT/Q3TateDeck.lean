/-
  IUT/Q3TateDeck.lean — A5a（柱A A5: 実 tempered π₁ の離散デッキ群 ℤ）

  ── 主要成果の分類: **[実／昇格(a)]**。M364F `TemperedPi1.lean` の離散部
     `tmpDiscretePart = intGrp`（裸の ℤ・どの実曲線・実被覆にも未接続）と、
     M333F `DiscreteRigidity.lean` の外部仮説 `discRig_infiniteOrder_hypothesis`
     （「本層では決して自前で導出しない」と明記した仮説）を、**実 Tate 被覆
     ℚ₃^× → E_q(ℚ₃) のデッキ群 q^ℤ ≅ ℤ として本物化・定理化する**。被覆側の
     全部品（q3tProj 全射・quotientProjN_ker で核＝ちょうど q^ℤ・tateZpow 加法則）は
     A8a Q3TateCurve で既に本物なのでそのまま消費し、離散 ℤ 商を実主語（実 q=3^m・
     実 ℚ₃^× 群提示）の上のデッキ作用として実現する。toy 主語なし——主語は実 q3tGrp・
     実 q3tQ m・実射影 q3tProj m。

  complete_pct 影響: **A5 0→0.1（見込み・独立監査確定が条件）・柱A 47→48**。内容:
  (i)   zpow 第1成分公式 v(qᵗ)=m·t（q3td_zpow_fst・全整数 t）、
  (ii)  実周期準同型 ℤ → ℚ₃^×（q3tdPeriodHom）とその単射性 q^ℤ ≅ ℤ（q3td_period_inj・
        m≥1・外部仮説なし）——M333F discRig_periodHom の実 Grp 版、
  (iii) 実 Tate 被覆の完全列 ker(q3tProj)=im(q3tdPeriodHom)（q3td_ker・iff 形）、
  (iv)  **旗艦**: 外部仮説 `discRig_infiniteOrder_hypothesis` を実主語 q3tQ m の上で
        無条件に定理化（q3td_infinite_order）——M333F/M364F の名指し外部 crux の discharge、
  (v)   デッキ作用 t·x=qᵗ·x（q3tdDeck: GAction intGrp）・被覆変換性（q3td_deck_over_proj）・
        自由性（q3td_deck_free）・ファイバー推移性（q3td_deck_transitive）・
        ファイバー＝軌道（q3td_fiber_orbit）、
  (vi)  束ね Q3TateDeckData / q3tdData（q=3 見出し実例）/ q3tdDeck_exists。

  正直な限定（§3.6 準拠・消去/弱化しない・既存 surrogate は消さない）:
  (1) 位相・解析構造なし——tempered π₁ の定義（Berkovich/rigid 被覆理論）そのもの
      ではなく、K-点の群論的・算術的な影（格子商）である。
  (2) 実現されるのは離散**商** ℤ のみ——tempered 群本体・profinite 部分との拡大は A5b、
      punctured 曲線の非可換 θ 構造は範囲外。
  (3) 担体は群提示 3^ℤ×ℤ₃^×（A2/A8 恒久限定の継承・文字通りの {x:ℚ₃//x≠0} 商ではない）。
  (4) p = 3 固定・q ∈ 3^ℤ（q = 3^m）固定。
  (5) 一般 m の指数抽出逆写像は ∃ 形（q3td_image）で主張する。明示双方向逆写像
      （m=1 の x.1 による指数抽出）は Int 変数除算補題を要するため本ファイルでは採らない
      （単射＋∃形像で q^ℤ≅ℤ を主張する）。
  (6) 既存 M333F/M364F の仮説付き機構（discRig_infiniteOrder_hypothesis・
      temperedPi1Data 等）は消さず併設する（§2(a) 昇格の規約）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3TateCurve
import IUT.TateCurve
import IUT.DiscreteRigidity
import IUT.GaloisCategory

namespace IUT

/-! ## q3td-1: zpow の第1成分公式（q3t_npow_fst の Int 拡張） -/

/-- 一般元 g の npow 第1成分（q3t_npow_fst の g 一般化・帰納）。
    (gⁿ).1 = g.1 · n（intGrp 加法・Int.mul_add）。 -/
theorem q3td_npow_fst (g : q3tGrp.carrier) : ∀ n : Nat,
    (tateNpow q3tGrp g n).1 = g.1 * (n : Int) := by
  intro n
  induction n with
  | zero =>
    show (0 : Int) = g.1 * ((0 : Nat) : Int)
    omega
  | succ k ih =>
    show (tateNpow q3tGrp g k).1 + g.1 = g.1 * ((k + 1 : Nat) : Int)
    rw [ih]
    have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [hcast, Int.mul_add, Int.mul_one]

/-- **q3td-1（★）: zpow 第1成分公式** (qᵗ).1 = m·t（全整数 t）。
    ofNat は q3td_npow_fst（g=q3tQ m・g.1=(m:Int)）、negSucc は
    g=q3tGrp.inv(q3tQ m)（g.1=-(m:Int)）を経由し符号整理。 -/
theorem q3td_zpow_fst (m : Nat) (t : Int) :
    (tateZpow q3tGrp (q3tQ m) t).1 = (m : Int) * t := by
  cases t with
  | ofNat n =>
    show (tateNpow q3tGrp (q3tQ m) n).1 = (m : Int) * (Int.ofNat n)
    exact q3td_npow_fst (q3tQ m) n
  | negSucc n =>
    show (tateNpow q3tGrp (q3tGrp.inv (q3tQ m)) (n + 1)).1 = (m : Int) * (Int.negSucc n)
    rw [q3td_npow_fst (q3tGrp.inv (q3tQ m)) (n + 1)]
    show -(m : Int) * (((n + 1 : Nat)) : Int) = (m : Int) * (Int.negSucc n)
    have hns : Int.negSucc n = -(((n + 1 : Nat)) : Int) := by omega
    rw [hns, Int.mul_neg, Int.neg_mul]

/-! ## q3td-2: 周期準同型 ℤ → ℚ₃^× とその単射性（q^ℤ ≅ ℤ の実体） -/

/-- **q3td-2a: 実周期準同型** t ↦ qᵗ（M333F discRig_periodHom の実 Grp 版）。 -/
def q3tdPeriodHom (m : Nat) : Hom intGrp q3tGrp where
  map := tateZpow q3tGrp (q3tQ m)
  map_mul := fun a b => tateZpow_add q3tGrp (q3tQ m) a b

/-- **q3td-2b（★）: 単射性＝ q^ℤ ≅ ℤ（実同型・外部仮説なし）**。
    第1成分 m·a = m·b から m≥1 の左簡約（Int.eq_of_mul_eq_mul_left）で a=b。 -/
theorem q3td_period_inj (m : Nat) (hm : 1 ≤ m) :
    (q3tdPeriodHom m).Injective := by
  intro a b h
  have h1 : (tateZpow q3tGrp (q3tQ m) a).1 = (tateZpow q3tGrp (q3tQ m) b).1 :=
    congrArg Prod.fst h
  rw [q3td_zpow_fst m a, q3td_zpow_fst m b] at h1
  exact Int.eq_of_mul_eq_mul_left (by omega) h1

/-- **q3td-2c: 像＝ちょうど q^ℤ**（tateQPowersSubgroup の mem は定義的に ∃t, qᵗ=x）。 -/
theorem q3td_image (m : Nat) (x : q3tGrp.carrier) :
    (q3tSubgroup m).mem x ↔ ∃ t : Int, (q3tdPeriodHom m).map t = x := Iff.rfl

/-! ## q3td-3: 核＝ちょうど q^ℤ（被覆の完全列 1→q^ℤ→ℚ₃^×→E_q→1） -/

/-- **q3td-3（★）: 実 Tate 被覆の完全列** — ker(q3tProj)=im(q3tdPeriodHom)（iff 形）。
    quotientProjN_ker（核＝q^ℤ）と q3td_image（像＝q^ℤ）の合成。 -/
theorem q3td_ker (m : Nat) (x : q3tGrp.carrier) :
    (q3tProj m).map x = (q3tCurve m).one ↔ ∃ t, (q3tdPeriodHom m).map t = x :=
  (quotientProjN_ker q3tGrp (q3tSubgroup m) (q3t_normal (q3tSubgroup m)) x).trans
    (q3td_image m x)

/-! ## q3td-4: 外部仮説の定理化（本ラウンドの旗艦 discharge） -/

/-- **q3td-4（★★）: M333F/M364F の外部仮説を実主語上の定理として discharge** —
    discRig_infiniteOrder_hypothesis q3tGrp (q3tQ m)（∀ t, qᵗ=1 → t=0）。
    第1成分 m·t=0（q3tGrp.one.1=0）と m≥1 の左簡約で t=0。外部付値仮定ゼロ。 -/
theorem q3td_infinite_order (m : Nat) (hm : 1 ≤ m) :
    discRig_infiniteOrder_hypothesis q3tGrp (q3tQ m) := by
  intro t ht
  have h1 : (tateZpow q3tGrp (q3tQ m) t).1 = q3tGrp.one.1 := congrArg Prod.fst ht
  rw [q3td_zpow_fst m t] at h1
  have h0 : q3tGrp.one.1 = (0 : Int) := rfl
  rw [h0] at h1
  have hmt : (m : Int) * t = (m : Int) * 0 := by rw [Int.mul_zero]; exact h1
  exact Int.eq_of_mul_eq_mul_left (by omega) hmt

/-! ## q3td-5: デッキ作用（自由・推移的・被覆変換） -/

/-- **q3td-5a: デッキ作用** t·x = qᵗ·x（ℤ が実 ℚ₃^× に作用）。 -/
def q3tdDeck (m : Nat) : GAction intGrp where
  carrier := q3tGrp.carrier
  act := fun t x => q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) x
  act_one := fun x => by
    show q3tGrp.mul (tateZpow q3tGrp (q3tQ m) (0 : Int)) x = x
    rw [tateZpow_zero, q3tGrp.one_mul]
  act_mul := fun g h x => by
    show q3tGrp.mul (tateZpow q3tGrp (q3tQ m) (g + h)) x
        = q3tGrp.mul (tateZpow q3tGrp (q3tQ m) g) (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) h) x)
    rw [tateZpow_add, q3tGrp.mul_assoc]

/-- **q3td-5b（★）: デッキ変換は被覆変換**（射影を保つ＝id_{E_q} を覆う）。
    (qᵗx)⁻¹·x = q^{-t} ∈ q^ℤ（可換整理・tateZpow_neg）を Quot.sound で。 -/
theorem q3td_deck_over_proj (m : Nat) (t : Int) (x : q3tGrp.carrier) :
    (q3tProj m).map ((q3tdDeck m).act t x) = (q3tProj m).map x := by
  apply Quot.sound
  show (q3tSubgroup m).mem
      (q3tGrp.mul (q3tGrp.inv (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) x)) x)
  have heq : q3tGrp.mul (q3tGrp.inv (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) x)) x
      = q3tGrp.inv (tateZpow q3tGrp (q3tQ m) t) := by
    rw [q3tGrp.inv_mul_rev, q3tGrp.mul_assoc,
      q3t_comm (q3tGrp.inv (tateZpow q3tGrp (q3tQ m) t)) x,
      ← q3tGrp.mul_assoc, q3tGrp.inv_mul, q3tGrp.one_mul]
  rw [heq]
  exact ⟨-t, tateZpow_neg q3tGrp (q3tQ m) t⟩

/-- **q3td-5c（★）: 自由性** qᵗ·x = x → t = 0（m≥1・第1成分算術のみ）。 -/
theorem q3td_deck_free (m : Nat) (hm : 1 ≤ m) (t : Int) (x : q3tGrp.carrier) :
    (q3tdDeck m).act t x = x → t = 0 := by
  intro h
  have h1 : q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) x = x := h
  have hq : tateZpow q3tGrp (q3tQ m) t = q3tGrp.one := by
    have h2 : q3tGrp.mul (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) x) (q3tGrp.inv x)
        = q3tGrp.mul x (q3tGrp.inv x) :=
      congrArg (fun z => q3tGrp.mul z (q3tGrp.inv x)) h1
    rw [q3tGrp.mul_assoc, q3tGrp.mul_inv, q3tGrp.mul_one] at h2
    exact h2
  exact q3td_infinite_order m hm t hq

/-- **q3td-5d（★）: ファイバー推移性** proj x = proj y → ∃ t, qᵗ·x = y。
    quot_exact で mem(x⁻¹y) を得て ⟨t, ht⟩、qᵗ·x=(x⁻¹y)·x=y（可換整理）。 -/
theorem q3td_deck_transitive (m : Nat) (x y : q3tGrp.carrier)
    (h : (q3tProj m).map x = (q3tProj m).map y) :
    ∃ t, (q3tdDeck m).act t x = y := by
  have hrel : (q3tSubgroup m).mem (q3tGrp.mul (q3tGrp.inv x) y) :=
    quot_exact q3tGrp (normalCong q3tGrp (q3tSubgroup m) (q3t_normal (q3tSubgroup m))) h
  obtain ⟨t, ht⟩ := hrel
  refine ⟨t, ?_⟩
  show q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) x = y
  rw [ht, q3tGrp.mul_assoc, q3t_comm y x, ← q3tGrp.mul_assoc, q3tGrp.inv_mul, q3tGrp.one_mul]

/-- **q3td-5e: ファイバー＝軌道**（5b+5d の iff 束ね）— Galois 被覆の核心。 -/
theorem q3td_fiber_orbit (m : Nat) (x y : q3tGrp.carrier) :
    (q3tProj m).map x = (q3tProj m).map y ↔ ∃ t, (q3tdDeck m).act t x = y := by
  constructor
  · intro h
    exact q3td_deck_transitive m x y h
  · intro h
    obtain ⟨t, ht⟩ := h
    rw [← ht]
    exact (q3td_deck_over_proj m t x).symm

/-! ## q3td-6: capstone -/

/-- **q3td-6: 実 Tate 被覆デッキデータ** — 実被覆 ℚ₃^×→E_q(ℚ₃)（全射・核＝q^ℤ）・
    デッキ群 ℤ（周期準同型の単射・∃形像）・自由推移的被覆変換作用・無限位数定理
    （外部仮説 discharge）を束ねる。tempered π₁ の離散部分の初の非退化実実現。 -/
structure Q3TateDeckData where
  /-- Tate パラメータの指数 m（q = 3^m）。 -/
  m : Nat
  /-- m ≥ 1（真の退化パラメータ）。 -/
  hm : 1 ≤ m
  /-- 射影 ℚ₃^× → E_q は全射。 -/
  proj_surj : ∀ x, ∃ a, (q3tProj m).map a = x
  /-- 完全列: ker(q3tProj)=im(q3tdPeriodHom)。 -/
  ker_eq : ∀ x, (q3tProj m).map x = (q3tCurve m).one ↔ ∃ t, (q3tdPeriodHom m).map t = x
  /-- q^ℤ ≅ ℤ（周期準同型の単射性）。 -/
  deck_inj : (q3tdPeriodHom m).Injective
  /-- デッキ変換は被覆変換（射影を保つ）。 -/
  deck_over : ∀ t x, (q3tProj m).map ((q3tdDeck m).act t x) = (q3tProj m).map x
  /-- 自由性: qᵗ·x=x → t=0。 -/
  deck_free : ∀ t x, (q3tdDeck m).act t x = x → t = 0
  /-- ファイバー＝軌道。 -/
  fiber_orbit : ∀ x y, (q3tProj m).map x = (q3tProj m).map y ↔ ∃ t, (q3tdDeck m).act t x = y
  /-- 無限位数（外部仮説の実 discharge）。 -/
  infinite_order : discRig_infiniteOrder_hypothesis q3tGrp (q3tQ m)

/-- **q3td-6b: 見出し実例 q = 3**（m=1）— 実 Tate 被覆 ℚ₃^×→E₃(ℚ₃) のデッキ群 ℤ。 -/
def q3tdData : Q3TateDeckData where
  m := 1
  hm := Nat.le_refl 1
  proj_surj := q3tProj_surjective 1
  ker_eq := q3td_ker 1
  deck_inj := q3td_period_inj 1 (Nat.le_refl 1)
  deck_over := q3td_deck_over_proj 1
  deck_free := q3td_deck_free 1 (Nat.le_refl 1)
  fiber_orbit := q3td_fiber_orbit 1
  infinite_order := q3td_infinite_order 1 (Nat.le_refl 1)

/-- **q3td-6c: 実 Tate 被覆デッキデータの存在**（実 ℚ₃^×・実 q=3^m・m≥1）。 -/
theorem q3tdDeck_exists : Nonempty Q3TateDeckData := ⟨q3tdData⟩

end IUT
