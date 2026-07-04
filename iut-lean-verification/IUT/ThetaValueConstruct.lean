/-
  IUT/ThetaValueConstruct.lean — M223F: テータ値 q^{j²} の構成と評価写像
  （柱E・並行部品）

  柱E 残課題 E-1（#39）の「テータ値の **指数簿記** から **値そのもの**
  への昇格」切片。M209F（ThetaValueEval.lean）はテータ値の q-指数が
  `thetaValExp j = j²` であること・その差分方程式 F(j+1) = F(j) + 2j + 1,
  F(0) = 0 からの強制・± / orbitRep 軌道ラベルの上での mod l
  well-defined 性までを、M212F（ThetaLabelInjective.lean）はその逆向き
  ——**相異なるラベルが相異なるテータ値を与える（mod l）単射性**——を
  Euclid 補題（M32、素数性）で閉じていた。ただし両者が扱うのは値の
  **指数（整数 j²）** のみで、テータ値 q^{j²} を**一つの環の元**として
  構成してはいなかった。

  本モジュールは、M88F（LaurentMonomial.lean）の単項式機械
  （`uMon R m` = 単項式 u^m、`laurent_uMon_mul` = 指数法則
  u^a·u^b = u^{a+b}、`laurent_uMon_zero` = u^0 = 1）を用いて、テータ値
  q^{j²} を **Laurent 環 laurentRing R の元** `thetaValMonomial R j`
  （= 指数 thetaValExp j = j² の単項式）として構成し、指数簿記
  （M209F/M212F）を値レベルへ持ち上げる。核心は

    (A) 値の構成: thetaValMonomial R j := q^{j²}（指数 j² の単項式）、
        その指数抽出が M209F の thetaValExp j = j² に一致（値↔指数の橋）;
    (B) 乗法的漸化式: q^{(j+1)²} = q^{j²}·q^{2j+1}（単項式積 +
        M9-8 sq_succ 由来の M209F thetaValExp_rec）、基点 q^{0²} = 1;
    (C) 反転（値レベル）: q^{(l−j)²} = q^{j²}·q^{l·k}（M4-7/M209F
        thetaValExp_pm_mod の値単項式版、M190F funeqTwist の値側）;
    (D) 値レベル評価写像の単射性: R が非自明（1 ≠ 0）で l 素数なら、
        ラベル {1,…,l⋇} 上でテータ値単項式は相異なる（単項式の係数
        一致 ⟹ 指数一致 ⟹ M212F theta_label_injective で j = j'）

    を機械検証する。

  * M223F-1 `thetaValMonomial` / `thetaValMonomial_exp` — テータ値 q^{j²}
    の単項式構成と指数抽出（= M209F thetaValExp）
  * M223F-2 `thetaValMonomial_zero` / `thetaValMonomial_rec` — 基点
    q^{0²} = 1 と乗法的漸化式 q^{(j+1)²} = q^{j²}·q^{2j+1}
  * M223F-3 `thetaValMonomial_pm` — 反転 q^{(l−j)²} = q^{j²}·q^{l·k}
  * M223F-4 `uMon_coeff_inj` / `thetaEval_injective` — 単項式の係数
    単射性と、それによる値レベル評価写像 j ↦ q^{j²} の単射性（本丸）
  * M223F-5 総括レコード `ThetaValueConstructData` / `…` / `…_exists`

  意義: M209F/M212F の**指数簿記**（整数 j²）を、M88F 単項式機械で
  **テータ値 q^{j²} そのもの（Laurent 環の元）**へ昇格させる。テータ値の
  基点・乗法的漸化式・反転・および評価写像 j ↦ q^{j²} の単射性を値レベルで
  確立し、指数簿記から評価同型へ一歩進める——M209F の thetaValExp は
  「値の q-指数」だったが、本層は「値そのもの」を一つの対象として構成し、
  その単射評価 {1,…,l⋇} ↪ {テータ値単項式} を与える。

  正直な限定（スライス A+B+C+D）: 扱うのはテータ値の **q-指数を単項式の
  指数として実現した Laurent 環の元** q^{j²} と、その基点・乗法的漸化式・
  反転・評価写像の単射性のみ。q の付値・q-展開の収束・エタールテータ
  関数値そのものの構成、ガロア同変な p 進テータ値、tempered π₁ の商と
  しての実現は M209F/M212F 同様 E-1 残として未形式化。単項式の係数
  単射性は係数環 R の非自明性 `R.one ≠ R.zero` を仮定として受け
  （退化環では u^a = u^b が指数を潰すため）、値レベルの単射性は l の
  素数性（M212F 経由）と併せて用いる。全て選択公理不使用
  （M209F/M212F/M88F から継承、新規 Classical なし）。サブエージェント
  並行部品。
-/
import IUT.ThetaLabelInjective
import IUT.LaurentMonomial

namespace IUT

/-! ## M223F-1: テータ値 q^{j²} の単項式構成 -/

/-- **M223F-1a: テータ値 q^{j²} の単項式構成** — ラベル j のテータ値
    q^{j²}（IUT III p.161 の表示 {q^{j²}}）を、Laurent 環 laurentRing R の
    単項式 u^{thetaValExp j}（指数は M209F の値指数 thetaValExp j = j²）
    として構成する。指数簿記（整数 j²）から値（環の元）への昇格。 -/
def thetaValMonomial (R : CRing) (j : Int) : (laurentRing R).carrier :=
  Quot.mk (laurentRel R) (uMon R (thetaValExp j))

/-- **定理 (M223F-1b): 指数抽出 = M209F の値指数** — テータ値単項式
    q^{j²} の単項式指数はちょうど thetaValExp j = j²（M209F）。値↔指数の
    橋（定義的一致）。 -/
theorem thetaValMonomial_exp (R : CRing) (j : Int) :
    thetaValMonomial R j = Quot.mk (laurentRel R) (uMon R (j * j)) :=
  rfl

/-! ## M223F-2: 基点と乗法的漸化式 -/

/-- **定理 (M223F-2a): 基点** — q^{0²} = q^0 = 1（Laurent 環の単位）。
    M209F thetaValExp_zero（F(0) = 0）と M88F laurent_uMon_zero（u^0 = 1）
    による。 -/
theorem thetaValMonomial_zero (R : CRing) :
    thetaValMonomial R 0 = (laurentRing R).one := by
  show Quot.mk (laurentRel R) (uMon R (thetaValExp 0)) = (laurentRing R).one
  rw [thetaValExp_zero]
  exact laurent_uMon_zero R

/-- **定理 (M223F-2b): 乗法的漸化式** — q^{(j+1)²} = q^{j²}·q^{2j+1}。
    テータ値の自動形式性の差分方程式 F(j+1) = F(j) + 2j + 1（M209F
    thetaValExp_rec、M9-8 sq_succ 由来）を、単項式積の指数法則
    u^a·u^b = u^{a+b}（M88F laurent_uMon_mul）で**値レベルの積**へ持ち
    上げた形。指数簿記の漸化式が値そのものの乗法的漸化式になる。 -/
theorem thetaValMonomial_rec (R : CRing) (j : Int) :
    thetaValMonomial R (j + 1)
      = (laurentRing R).mul (thetaValMonomial R j)
          (Quot.mk (laurentRel R) (uMon R (2 * j + 1))) := by
  have hrec : thetaValExp (j + 1) = thetaValExp j + (2 * j + 1) := by
    have h := thetaValExp_rec j
    omega
  show Quot.mk (laurentRel R) (uMon R (thetaValExp (j + 1)))
    = (laurentRing R).mul (Quot.mk (laurentRel R) (uMon R (thetaValExp j)))
        (Quot.mk (laurentRel R) (uMon R (2 * j + 1)))
  rw [laurent_uMon_mul R (thetaValExp j) (2 * j + 1), hrec]

/-! ## M223F-3: 反転（値レベル） -/

/-- **定理 (M223F-3): 反転 q^{(l−j)²} = q^{j²}·q^{l·k}（値レベル）** —
    ±1 反転 j ↦ l−j の下でテータ値 q^{(l−j)²} は q^{j²} と q^l の冪
    （q^{l·k}）だけ異なる。M4-7/M209F thetaValExp_pm_mod（(l−j)² = j² + l·k）
    の値単項式版で、M190F funeqTwist の中心捻れ ≡ j (mod l) の値側。
    テータ値が {±1} 反転の下で（q^l を法に）不変であることの値論的表現。 -/
theorem thetaValMonomial_pm (R : CRing) (l j : Int) :
    ∃ k : Int, thetaValMonomial R (l - j)
      = (laurentRing R).mul (thetaValMonomial R j)
          (Quot.mk (laurentRel R) (uMon R (l * k))) := by
  obtain ⟨k, hk⟩ := thetaValExp_pm_mod l j
  refine ⟨k, ?_⟩
  show Quot.mk (laurentRel R) (uMon R (thetaValExp (l - j)))
    = (laurentRing R).mul (Quot.mk (laurentRel R) (uMon R (thetaValExp j)))
        (Quot.mk (laurentRel R) (uMon R (l * k)))
  rw [laurent_uMon_mul R (thetaValExp j) (l * k), hk]

/-! ## M223F-4: 値レベル評価写像の単射性 -/

/-- **補題 (M223F-4a): 単項式の係数単射性** — 係数環 R が非自明
    （R.one ≠ R.zero）なら、単項式 u^a と u^b の係数関数が一致すれば
    指数が一致する（a = b）。u^a の係数を a で評価すると one、u^b の
    係数を a で評価すると a = b のとき one・そうでなければ zero。退化環
    （1 = 0）を排すことで指数抽出が単射になる。 -/
theorem uMon_coeff_inj (R : CRing) (hne : R.one ≠ R.zero) (a b : Int)
    (h : (uMon R a).coeff = (uMon R b).coeff) : a = b := by
  have hpt : (if (a : Int) = a then R.one else R.zero)
      = (if (a : Int) = b then R.one else R.zero) := congrFun h a
  rw [if_pos rfl] at hpt
  cases Int.decEq a b with
  | isTrue heq => exact heq
  | isFalse hne' =>
    rw [if_neg hne'] at hpt
    exact absurd hpt hne

/-- **定理 (M223F-4b): 値レベル評価写像 j ↦ q^{j²} の単射性（本丸）** —
    係数環 R が非自明で l = 2l⋇+1 が素数なら、ラベル {1,…,l⋇} 上で
    テータ値単項式は相異なる: 1 ≤ j, j' ≤ l⋇ で q^{j²} と q^{j'²} の
    係数が一致すれば j = j'。単項式の係数単射性（M223F-4a、指数一致
    j² = j'²）を M212F theta_label_injective（j² ≡ j'² mod l ⟹ j = j'、
    Euclid・素数性）に接続する。M209F/M212F の**指数簿記の単射性**を
    **値そのものの評価写像の単射性**へ昇格させ、単射評価
    {1,…,l⋇} ↪ {テータ値単項式} を確立する。 -/
theorem thetaEval_injective (R : CRing) (hne : R.one ≠ R.zero)
    (l L : Nat) (hodd : l = 2 * L + 1) (hp : IsPrime l)
    (j j' : Nat) (hj : 1 ≤ j) (hjL : j ≤ L) (hj' : 1 ≤ j') (hj'L : j' ≤ L)
    (h : (uMon R (thetaValExp (j : Int))).coeff
        = (uMon R (thetaValExp (j' : Int))).coeff) :
    j = j' := by
  have hexp : thetaValExp (j : Int) = thetaValExp (j' : Int) :=
    uMon_coeff_inj R hne (thetaValExp (j : Int)) (thetaValExp (j' : Int)) h
  have hcong : ∃ k : Int,
      thetaValExp (j' : Int) = thetaValExp (j : Int) + (l : Int) * k := by
    refine ⟨0, ?_⟩
    show thetaValExp (j' : Int) = thetaValExp (j : Int) + (l : Int) * 0
    rw [Int.mul_zero, Int.add_zero, hexp]
  exact theta_label_injective l L hodd hp j j' hj hjL hj' hj'L hcong

/-! ## M223F-5: 総括レコード -/

/-- **M223F-5a: テータ値構成データ** — テータ値 q^{j²} の単項式構成の
    指数抽出（= M209F thetaValExp）、基点 q^{0²} = 1、乗法的漸化式
    q^{(j+1)²} = q^{j²}·q^{2j+1}、反転 q^{(l−j)²} = q^{j²}·q^{l·k}、および
    値レベル評価写像の単射性（1 ≤ j, j' ≤ l⋇ かつ係数一致 ⟹ j = j'）の
    一括束ね。E-1 の指数簿記 → 値構成側 witness。 -/
structure ThetaValueConstructData (R : CRing) (hne : R.one ≠ R.zero)
    (l L : Nat) (hodd : l = 2 * L + 1) (hp : IsPrime l) where
  /-- 指数抽出: q^{j²} の単項式指数 = thetaValExp j = j²（M209F）。 -/
  val_exp : ∀ j : Int,
    thetaValMonomial R j = Quot.mk (laurentRel R) (uMon R (j * j))
  /-- 基点: q^{0²} = 1。 -/
  val_zero : thetaValMonomial R 0 = (laurentRing R).one
  /-- 乗法的漸化式: q^{(j+1)²} = q^{j²}·q^{2j+1}。 -/
  val_rec : ∀ j : Int, thetaValMonomial R (j + 1)
    = (laurentRing R).mul (thetaValMonomial R j)
        (Quot.mk (laurentRel R) (uMon R (2 * j + 1)))
  /-- 反転（値レベル）: q^{(l−j)²} = q^{j²}·q^{l·k}。 -/
  val_pm : ∀ j : Int, ∃ k : Int, thetaValMonomial R ((l : Int) - j)
    = (laurentRing R).mul (thetaValMonomial R j)
        (Quot.mk (laurentRel R) (uMon R ((l : Int) * k)))
  /-- 値レベル評価写像の単射性: 1 ≤ j, j' ≤ l⋇ かつ係数一致 ⟹ j = j'。 -/
  val_inj : ∀ j j' : Nat, 1 ≤ j → j ≤ L → 1 ≤ j' → j' ≤ L →
    (uMon R (thetaValExp (j : Int))).coeff
        = (uMon R (thetaValExp (j' : Int))).coeff →
    j = j'

/-- **M223F-5b: witness 本体** — 全フィールドを M223F-1〜4 で埋める。 -/
def thetaValueConstructData (R : CRing) (hne : R.one ≠ R.zero)
    (l L : Nat) (hodd : l = 2 * L + 1) (hp : IsPrime l) :
    ThetaValueConstructData R hne l L hodd hp where
  val_exp := thetaValMonomial_exp R
  val_zero := thetaValMonomial_zero R
  val_rec := thetaValMonomial_rec R
  val_pm := fun j => thetaValMonomial_pm R (l : Int) j
  val_inj := fun j j' hj hjL hj' hj'L h =>
    thetaEval_injective R hne l L hodd hp j j' hj hjL hj' hj'L h

/-- **定理 (M223F-5c): テータ値構成データの存在（M223F 見出し）** —
    係数環 R が非自明で l = 2l⋇+1 が素数なら、テータ値 q^{j²} の構成
    データが存在する。M209F/M212F の指数簿記（整数 j²）が Laurent 環の
    元 q^{j²} として実体化し、基点・乗法的漸化式・反転・単射評価を
    値レベルで満たす。 -/
theorem thetaValueConstruct_exists (R : CRing) (hne : R.one ≠ R.zero)
    (l L : Nat) (hodd : l = 2 * L + 1) (hp : IsPrime l) :
    Nonempty (ThetaValueConstructData R hne l L hodd hp) :=
  ⟨thetaValueConstructData R hne l L hodd hp⟩

end IUT
