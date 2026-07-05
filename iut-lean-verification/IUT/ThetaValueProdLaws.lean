/-
  IUT/ThetaValueProdLaws.lean — M242F: テータ値の有限多ラベル積の追加代数則
  （連接則・逆順不変・転置不変・連続ラベル範囲の指数和閉形式接続・柱E E-1 並行部品）

  柱E 残課題 E-1（#39）の「値の代数構造」切片の続き。M237F
  （ThetaValueSubgroup.lean）はテータ値 q^{j²} が Laurent 環 laurentRing R の
  単元群の**部分群**をなすこと（IsMonomialValue の単位・積・逆元閉性）と、
  ラベル列 js に沿った**有限多ラベル積** thetaValProd R js = u^{Σ_{j∈js} j²}
  = uMonHom R (thetaExpSum js) の指数和合成則（二テータ値 → 任意有限個）、
  単項/対の整合を確立していた。ただし M237F は多ラベル積を**一本のラベル列**
  に対して閉じるにとどまり、複数ラベル列の**連接（結合則）**・列の**並べ替え
  不変性**（逆順・先頭転置）や、**連続ラベル範囲 [0,1,…,n]** に沿った積の
  指数和が平方和 Σj² の**閉形式** l(l+1)(2l+1)/6（M93 ssq_closed）へ落ちる
  という接続は与えていなかった。

  本モジュールは M237F の thetaExpSum / thetaValProd / thetaValProd_eq_uMonHom
  と M232F uMonHom_add・M93 ssq / ssq_closed を土台に、

    (A) **指数和の連接加法性**: thetaExpSum (js ++ ks)
        = thetaExpSum js + thetaExpSum ks（リスト連接での指数簿記の加法性）;
    (B) **多ラベル積の連接則（結合則の一般形・新規）**:
        thetaValProd R (js ++ ks)
          = (thetaValProd R js)·(thetaValProd R ks)。M237F の二テータ値合成則
        を**二つの有限積の連接**へ一般化した結合的合成則;
    (C) **並べ替え不変性（新規）**: 指数和・多ラベル積は列の**逆順**
        （thetaExpSum_reverse / thetaValProd_reverse）と**先頭二要素の転置**
        （thetaValProd_swap）の下で不変（積が可換モノイド値であることの帰結）;
    (D) **連続ラベル範囲の指数和閉形式接続（新規）**: ラベル範囲
        labelUpto n = [0,1,…,n−1] に沿った積の指数
        thetaExpSum (labelUpto (n+1)) = Σ_{k≤n} k² = ssq n（M93）、および
        その積本体 thetaValProd R (labelUpto (n+1)) = u^{ssq n}、閉形式
        6·ssq n = n(n+1)(2n+1)（M93 ssq_closed）。テータ値の連続ラベル積の
        総指数がガウス因子（M133 gaussDiv・M93 平方和）の閉形式に一致する

    を機械検証し、多ラベル積の代数則（連接・並べ替え・範囲和閉形式）を
    一つのデータへ束ねる。

  * M242F-1 `thetaExpSum_append` / `thetaExpSum_singleton` — 指数和の連接
    加法性と単項指数
  * M242F-2 `thetaValProd_append` — 多ラベル積の連接則（結合則の一般形・新規）
  * M242F-3 `thetaExpSum_reverse` / `thetaValProd_reverse` /
    `thetaValProd_swap` — 逆順・先頭転置の不変性（新規）
  * M242F-4 `labelUpto` / `sqSumBelow` / `sqSumBelow_succ` /
    `thetaExpSum_labelUpto` / `thetaValProd_labelUpto` /
    `thetaExpSum_labelUpto_closed` — 連続ラベル範囲の指数和と閉形式接続（新規）
  * M242F-5 総括レコード `ThetaValueProdLawData` / `thetaValueProdLawData`
    / `thetaValueProdLaw_exists` — capstone

  意義: M237F の**一本の多ラベル積**の指数和合成を、複数ラベル列の
  **連接（結合則）**・列の**並べ替え不変性**（逆順・転置）へ精緻化し、
  さらに**連続ラベル範囲**に沿った積の総指数が平方和 Σj² の閉形式
  l(l+1)(2l+1)/6（M93）へ落ちることを接続する。テータ値の多ラベル積を
  可換モノイド上の畳み込みとして代数化し、その連続範囲積をガウス簿記
  （M93/M133）へ橋渡しする E-1 の値代数側 witness。

  正直な限定（スライス A+B+C+D）: 扱うのはテータ値 q^{j²} が住む
  Laurent 環単元群の**有限多ラベル積の代数則**（連接＝結合則・逆順/転置
  不変・連続範囲の指数和 = ssq とその閉形式）のみ。ここで「連接則」「並べ替え
  不変」とは (laurentRing R, ×, 1) の可換モノイド構造の下で有限積が
  指数和 uMonHom R (thetaExpSum ·) を経由することの帰結であり、テータ値が
  ラベル上でなす**環準同型**や**ガロア同変な p 進テータ値**・
  **tempered π₁ の商としての実現**・**エタールテータ関数値そのものの構成**は
  M223F/M232F/M237F 同様 E-1 残として範囲外（本モジュールでは一切主張しない）。
  「並べ替え不変」も逆順・先頭転置という具体インスタンスに限り、
  一般の対称群作用（List.Perm 全体）の不変性は扱わない（指数和が加法的
  可換であることから任意の並べ替えで不変だが、その一般形は List.Perm の
  帰納で別途。ここでは代表二インスタンスのみ）。連続ラベル範囲の閉形式は
  M93 ssq_closed（6·Σj²=l(l+1)(2l+1)）の値指数側への言い換えであり、q の
  付値・q-展開の収束は扱わない。全て選択公理を証明本体で新規導入せず
  （M237F/M232F/M223F/M93 から継承、新規 Classical・新規 Classical.choice
  なし。商 laurentRing / laurentRel / Quot レベルの主張は Quot.sound を使う
  —— 商構成に内在、選択公理ではない）。#print axioms により継承分のみで
  あることを確認済み。サブエージェント並行部品。
-/
import IUT.ThetaValueSubgroup
import IUT.GaussianVolume

namespace IUT

/-! ## M242F-1: 指数和の連接加法性と単項指数 -/

/-- **定理 (M242F-1a): 指数和の連接加法性** — ラベル列の連接 js ++ ks に
    沿った指数和は各々の和: thetaExpSum (js ++ ks)
    = thetaExpSum js + thetaExpSum ks。多ラベル積の指数簿記が連接で加法的。 -/
theorem thetaExpSum_append (js ks : List Int) :
    thetaExpSum (js ++ ks) = thetaExpSum js + thetaExpSum ks := by
  induction js with
  | nil =>
    show thetaExpSum ks = 0 + thetaExpSum ks
    rw [Int.zero_add]
  | cons j js ih =>
    show thetaValExp j + thetaExpSum (js ++ ks)
      = (thetaValExp j + thetaExpSum js) + thetaExpSum ks
    rw [ih, Int.add_assoc]

/-- **定理 (M242F-1b): 単項指数** — 一ラベル列 [j] の指数和 = thetaValExp j
    = j²（末尾の空和 0 を吸収）。連接則で単項を扱うための整合。 -/
theorem thetaExpSum_singleton (j : Int) :
    thetaExpSum [j] = thetaValExp j := by
  show thetaValExp j + 0 = thetaValExp j
  rw [Int.add_zero]

/-! ## M242F-2: 多ラベル積の連接則（結合則の一般形） -/

/-- **定理 (M242F-2): 多ラベル積の連接則（結合則の一般形・新規）** —
    連接ラベル列に沿った有限積は各々の積の積:
    ∏_{j∈js++ks} q^{j²} = (∏_{j∈js} q^{j²})·(∏_{j∈ks} q^{j²})。M237F の
    二テータ値合成則 q^{j²}·q^{j'²}=u^{j²+j'²} を**二つの有限積の連接**へ
    一般化した結合的合成則（M237F thetaValProd_eq_uMonHom + M242F-1a
    thetaExpSum_append + M232F uMonHom_add で指数和へ落として貼り合わせ）。 -/
theorem thetaValProd_append (R : CRing) (js ks : List Int) :
    thetaValProd R (js ++ ks)
      = (laurentRing R).mul (thetaValProd R js) (thetaValProd R ks) := by
  rw [thetaValProd_eq_uMonHom R (js ++ ks), thetaExpSum_append,
    uMonHom_add, thetaValProd_eq_uMonHom R js, thetaValProd_eq_uMonHom R ks]

/-! ## M242F-3: 逆順・先頭転置の不変性 -/

/-- **定理 (M242F-3a): 指数和の逆順不変** — thetaExpSum (reverse js)
    = thetaExpSum js。指数和が加法的可換であることの帰結（reverse_cons +
    連接加法性 + Int.add_comm）。 -/
theorem thetaExpSum_reverse (js : List Int) :
    thetaExpSum (List.reverse js) = thetaExpSum js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    rw [List.reverse_cons, thetaExpSum_append, thetaExpSum_singleton, ih]
    show thetaExpSum js + thetaValExp j = thetaValExp j + thetaExpSum js
    rw [Int.add_comm]

/-- **定理 (M242F-3b): 多ラベル積の逆順不変（新規）** — ラベル列を逆順に
    しても有限積は不変: ∏_{reverse js} q^{j²} = ∏_{js} q^{j²}。積が指数和
    uMonHom (thetaExpSum ·) を経由し、指数和が逆順不変（M242F-3a）である
    ことの帰結。テータ値積が可換モノイド値であることの離散核。 -/
theorem thetaValProd_reverse (R : CRing) (js : List Int) :
    thetaValProd R (List.reverse js) = thetaValProd R js := by
  rw [thetaValProd_eq_uMonHom R (List.reverse js), thetaExpSum_reverse,
    thetaValProd_eq_uMonHom R js]

/-- **定理 (M242F-3c): 多ラベル積の先頭転置不変（新規）** — 先頭二ラベルを
    入れ替えても有限積は不変: ∏_{j::j'::js} q^{j²} = ∏_{j'::j::js} q^{j²}。
    指数和 thetaValExp j + (thetaValExp j' + …) の左可換（Int.add_left_comm）
    の値側言い換え。並べ替え不変性の代表インスタンス。 -/
theorem thetaValProd_swap (R : CRing) (j j' : Int) (js : List Int) :
    thetaValProd R (j :: j' :: js) = thetaValProd R (j' :: j :: js) := by
  rw [thetaValProd_eq_uMonHom R (j :: j' :: js),
    thetaValProd_eq_uMonHom R (j' :: j :: js)]
  show uMonHom R (thetaValExp j + (thetaValExp j' + thetaExpSum js))
    = uMonHom R (thetaValExp j' + (thetaValExp j + thetaExpSum js))
  rw [Int.add_left_comm]

/-! ## M242F-4: 連続ラベル範囲の指数和と閉形式接続 -/

/-- **M242F-4a: 連続ラベル範囲** — labelUpto n = [0,1,…,n−1]（末尾追加で
    構成）。テータ値の連続ラベル積の指数を平方和 ssq へ接続するためのラベル列。 -/
def labelUpto : Nat → List Int
  | 0 => []
  | n + 1 => labelUpto n ++ [(n : Int)]

/-- **M242F-4b: 下方平方和** — sqSumBelow n = 0²+1²+…+(n−1)²（Nat 上）。
    連続ラベル指数和の Nat 値対応物。 -/
def sqSumBelow : Nat → Nat
  | 0 => 0
  | n + 1 => sqSumBelow n + n * n

/-- **定理 (M242F-4c): 下方平方和と M93 平方和の一致** — sqSumBelow (n+1)
    = ssq n。0²+…+n² は 1²+…+n²（ssq n、0² は消える）に一致。M93 ssq への橋。 -/
theorem sqSumBelow_succ (n : Nat) : sqSumBelow (n + 1) = ssq n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show sqSumBelow (n + 1) + (n + 1) * (n + 1) = ssq n + (n + 1) * (n + 1)
    rw [ih]

/-- **定理 (M242F-4d): 連続ラベル範囲の指数和 = 下方平方和** —
    thetaExpSum (labelUpto n) = sqSumBelow n（Int へ cast）。連続ラベル
    [0,…,n−1] の指数和が平方和に一致（連接加法性 + 単項指数 + Nat/Int cast）。 -/
theorem thetaExpSum_labelUpto (n : Nat) :
    thetaExpSum (labelUpto n) = ((sqSumBelow n : Nat) : Int) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show thetaExpSum (labelUpto n ++ [(n : Int)])
      = ((sqSumBelow n + n * n : Nat) : Int)
    rw [thetaExpSum_append, thetaExpSum_singleton, ih,
      Int.natCast_add, Int.natCast_mul]
    show ((sqSumBelow n : Nat) : Int) + (n : Int) * (n : Int)
      = ((sqSumBelow n : Nat) : Int) + (n : Int) * (n : Int)
    rfl

/-- **定理 (M242F-4e): 連続ラベル範囲の指数和 = ssq（M93）** —
    thetaExpSum (labelUpto (n+1)) = ssq n。連続ラベル [0,…,n] の総指数が
    平方和 Σ_{k≤n} k² = ssq n に一致（M242F-4d + M242F-4c）。 -/
theorem thetaExpSum_labelUpto_ssq (n : Nat) :
    thetaExpSum (labelUpto (n + 1)) = ((ssq n : Nat) : Int) := by
  rw [thetaExpSum_labelUpto, sqSumBelow_succ]

/-- **定理 (M242F-4f): 連続ラベル範囲の多ラベル積 = 平方和単項式（新規）** —
    ∏_{j∈[0,…,n]} q^{j²} = u^{ssq n} = uMonHom R (ssq n)。テータ値の連続
    ラベル積の本体が平方和 Σj² を指数とする単項式（M237F
    thetaValProd_eq_uMonHom + M242F-4e）。ガウス因子（M133）の値指数側。 -/
theorem thetaValProd_labelUpto (R : CRing) (n : Nat) :
    thetaValProd R (labelUpto (n + 1)) = uMonHom R ((ssq n : Nat) : Int) := by
  rw [thetaValProd_eq_uMonHom R (labelUpto (n + 1)), thetaExpSum_labelUpto_ssq]

/-- **定理 (M242F-4g): 連続ラベル範囲の指数和の閉形式接続（新規）** —
    連続ラベル積の総指数 ssq n は閉形式 6·ssq n = n(n+1)(2n+1)（M93
    ssq_closed）を満たす。テータ値の連続ラベル積の総指数がガウス簿記
    （M93 平方和・M133 gaussDiv）の閉形式に一致。 -/
theorem thetaExpSum_labelUpto_closed (n : Nat) :
    6 * ssq n = n * (n + 1) * (2 * n + 1) :=
  ssq_closed n

/-! ## M242F-5: 総括レコード（多ラベル積の追加代数則） -/

/-- **M242F-5a: テータ値多ラベル積代数則データ** — テータ値 q^{j²} の有限
    多ラベル積 thetaValProd の追加代数則を一括束ね: 指数和の連接加法性、
    多ラベル積の連接則（結合則の一般形）、逆順・先頭転置の並べ替え不変性、
    連続ラベル範囲の指数和 = ssq とその閉形式、連続ラベル積 = 平方和単項式。
    M237F の一本の多ラベル積を連接・並べ替え・範囲和閉形式へ精緻化した
    E-1 の値代数側 witness。 -/
structure ThetaValueProdLawData (R : CRing) where
  /-- 多ラベル積写像 js ↦ ∏ q^{j²}。 -/
  prod : List Int → (laurentRing R).carrier
  /-- 指数簿記 js ↦ Σ j²。 -/
  expSum : List Int → Int
  /-- 積は指数和単項式: ∏ q^{j²} = u^{Σj²}。 -/
  prod_eq : ∀ js : List Int, prod js = uMonHom R (expSum js)
  /-- 指数和の連接加法性: Σ_{js++ks} = Σ_{js} + Σ_{ks}。 -/
  expSum_append : ∀ js ks : List Int,
    expSum (js ++ ks) = expSum js + expSum ks
  /-- 多ラベル積の連接則: ∏_{js++ks} = (∏_{js})·(∏_{ks})。 -/
  prod_append : ∀ js ks : List Int,
    prod (js ++ ks) = (laurentRing R).mul (prod js) (prod ks)
  /-- 逆順不変: ∏_{reverse js} = ∏_{js}。 -/
  prod_reverse : ∀ js : List Int,
    prod (List.reverse js) = prod js
  /-- 先頭転置不変: ∏_{j::j'::js} = ∏_{j'::j::js}。 -/
  prod_swap : ∀ (j j' : Int) (js : List Int),
    prod (j :: j' :: js) = prod (j' :: j :: js)
  /-- 連続ラベル範囲の積 = 平方和単項式: ∏_{[0,…,n]} q^{j²} = u^{ssq n}。 -/
  prod_range : ∀ n : Nat,
    prod (labelUpto (n + 1)) = uMonHom R ((ssq n : Nat) : Int)
  /-- 連続ラベル範囲の指数和の閉形式: 6·ssq n = n(n+1)(2n+1)。 -/
  range_closed : ∀ n : Nat, 6 * ssq n = n * (n + 1) * (2 * n + 1)

/-- **M242F-5b: witness 本体** — prod := thetaValProd R、expSum := thetaExpSum
    として全フィールドを M242F-1〜4 で埋める。 -/
def thetaValueProdLawData (R : CRing) : ThetaValueProdLawData R where
  prod := thetaValProd R
  expSum := thetaExpSum
  prod_eq := thetaValProd_eq_uMonHom R
  expSum_append := thetaExpSum_append
  prod_append := thetaValProd_append R
  prod_reverse := thetaValProd_reverse R
  prod_swap := thetaValProd_swap R
  prod_range := thetaValProd_labelUpto R
  range_closed := thetaExpSum_labelUpto_closed

/-- **定理 (M242F-5c): テータ値多ラベル積代数則データの存在（M242F 見出し）** —
    任意の係数環 R に対し、テータ値 q^{j²} の有限多ラベル積の追加代数則
    （連接＝結合則・逆順/転置の並べ替え不変・連続ラベル範囲の指数和 = ssq
    とその閉形式 l(l+1)(2l+1)/6）を束ねたデータが存在する。M237F の一本の
    多ラベル積が連接・並べ替え・範囲和閉形式へ精緻化される。 -/
theorem thetaValueProdLaw_exists (R : CRing) :
    Nonempty (ThetaValueProdLawData R) :=
  ⟨thetaValueProdLawData R⟩

end IUT
