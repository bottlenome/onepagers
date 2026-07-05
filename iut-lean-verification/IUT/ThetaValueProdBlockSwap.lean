/-
  IUT/ThetaValueProdBlockSwap.lean — M258F: テータ値多ラベル積のブロック入替・
  n 回左回転不変（block-swap / left-rotation invariance・柱E E-1 並行部品）

  柱E 残課題 E-1（#39）の「値の代数構造」切片の続き。M242F
  （ThetaValueProdLaws.lean）は多ラベル積 thetaValProd の並べ替え不変性を
  **列の逆順**と**先頭二要素の転置**（位置 0,1 のみ）に限って確立し、M253F
  （ThetaValueProdSwapAt.lean）はそれを「列中の**任意位置**にある**隣接二
  要素**」の転置不変へ一般化していた。ただし M253F まではいずれも「長さ 1
  の隣接対」の転置に限られており、**任意の長さを持つ二つの連続ブロック**を
  丸ごと入れ替える不変性や、それを反復して得られる**n 回の左回転**不変性は
  与えていなかった。

  本モジュールは M242F の thetaValProd_append（連接則）・thetaExpSum_append
  （指数和の連接加法性）と M232F/laurentRing の可換性 mul_comm を土台に、

    (A) **ブロック入替不変（新規）**: 列を xs ++ ys（xs, ys は任意長）に
        分解したとき、指数和・多ラベル積はブロックの前後を入れ替えても
        不変 thetaExpSum (xs ++ ys) = thetaExpSum (ys ++ xs) /
        thetaValProd R (xs ++ ys) = thetaValProd R (ys ++ xs)。連接則で
        両側を積へ落とし、Laurent 環の乗法可換性 mul_comm で入れ替える。
        M253F の「長さ 1 の隣接対の入替」を**任意長のブロック**の入替へ
        一般化する；
    (B) **単一ステップ左回転不変（新規）**: 先頭要素を末尾へ回す変換
        j :: js ↦ js ++ [j] の下で多ラベル積は不変（xs := [j], ys := js
        への (A) の特殊化）；
    (C) **n 回左回転不変（新規・本丸）**: 反復左回転 rotateLeft n js
        （n 回、先頭要素を末尾へ回す操作を n 回反復）の下で多ラベル積は
        不変 thetaValProd R (rotateLeft n js) = thetaValProd R js。(B) を
        n に関する帰納で反復し、任意回数の巡回置換で不変であることを
        機械検証する

    を機械検証し、M253F の隣接転置不変性を「ブロック入替」「n 回巡回
    置換」という具体的かつ広いインスタンス族へ前進させる。

  * M258F-1 `thetaExpSum_block_swap` / `thetaValProd_block_swap` —
    ブロック入替不変（新規）
  * M258F-2 `thetaValProd_rotate_left` — 単一ステップ左回転不変（新規）
  * M258F-3 `rotateLeft` / `thetaValProd_rotateLeft` — n 回左回転と
    その不変性（新規・本丸）
  * M258F-4 総括レコード `ThetaValueProdBlockSwapData` /
    `thetaValueProdBlockSwapData` / `thetaValueProdBlockSwap_exists` —
    capstone

  意義: M253F の「列中の任意位置にある長さ 1 の隣接対」の転置不変性を、
  「任意長の連続ブロックの入替」「n 回の巡回置換（左回転）」という、実務上
  よく使われる二つの具体的な並べ替えクラスへ広げる。証明は M242F の連接則
  と Laurent 環の乗法可換性のみから直接従い、新規の帰納は n 回反復（C）の
  一段のみ。

  正直な限定（スライス A+B+C）: 扱うのはテータ値 q^{j²} が住む Laurent 環
  単元群の**有限多ラベル積**について、(1) 列を xs++ys に分解したときの
  ブロック入替不変、(2) 先頭要素を末尾へ回す左回転の反復不変のみ。これは
  「列全体の**任意の並べ替え**」（List.Perm・対称群作用全体）の不変性の
  一般形ではなく、ブロック入替と左回転という**具体的な二つの並べ替えの
  族**に限る（M242F/M253F 同様、一般の List.Perm 不変性は範囲外）。右回転
  や任意の巡回シフト量の閉形式（rotateLeft n js が js の長さを法として
  周期的であること等）も本モジュールでは扱わない。テータ値がラベル上で
  なす**環準同型**や**ガロア同変な p 進テータ値**・**tempered π₁ の商と
  しての実現**・**エタールテータ関数値そのものの構成**は
  M223F/M232F/M237F/M242F/M253F 同様 E-1 残として範囲外（本モジュールでは
  一切主張しない）。q の付値・q-展開の収束も扱わない。全て選択公理を
  証明本体で新規導入せず（M253F/M242F/M237F/M232F/M223F から継承、新規
  Classical・新規 Classical.choice なし。商 laurentRing / laurentRel /
  Quot レベルの主張は Quot.sound を使う —— 商構成に内在、選択公理では
  ない）。#print axioms により継承分のみであることを確認済み。
  サブエージェント並行部品。
-/
import IUT.ThetaValueProdSwapAt

namespace IUT

/-! ## M258F-1: ブロック入替不変 -/

/-- **定理 (M258F-1a): 指数和のブロック入替不変（新規）** — 列を xs ++ ys
    （xs, ys は任意長）に分解したとき、指数和はブロックの前後を入れ替えても
    不変: thetaExpSum (xs ++ ys) = thetaExpSum (ys ++ xs)。M242F-1a 連接
    加法性で両側を分けたのち Int.add_comm で入れ替える。M253F-1（長さ 1 の
    隣接対の入替）を任意長のブロックへ一般化した指数簿記側。 -/
theorem thetaExpSum_block_swap (xs ys : List Int) :
    thetaExpSum (xs ++ ys) = thetaExpSum (ys ++ xs) := by
  rw [thetaExpSum_append, thetaExpSum_append, Int.add_comm]

/-- **定理 (M258F-1b): 多ラベル積のブロック入替不変（新規・本丸）** — 列を
    xs ++ ys に分解したとき、多ラベル積はブロックの前後を入れ替えても不変:
    thetaValProd R (xs ++ ys) = thetaValProd R (ys ++ xs)。連接則
    （M242F-2 thetaValProd_append）で両側を積へ落とし、Laurent 環の乗法
    可換性 mul_comm で入れ替える。M253F-2（長さ 1 の隣接対の入替）を任意長
    のブロックの入替へ一般化する本モジュールの本丸。 -/
theorem thetaValProd_block_swap (R : CRing) (xs ys : List Int) :
    thetaValProd R (xs ++ ys) = thetaValProd R (ys ++ xs) := by
  rw [thetaValProd_append R xs ys, thetaValProd_append R ys xs,
    (laurentRing R).mul_comm]

/-! ## M258F-2: 単一ステップ左回転不変 -/

/-- **定理 (M258F-2): 単一ステップ左回転不変（新規）** — 先頭要素を末尾へ
    回す変換 j :: js ↦ js ++ [j] の下で多ラベル積は不変:
    thetaValProd R (j :: js) = thetaValProd R (js ++ [j])。xs := [j],
    ys := js への M258F-1b の特殊化（[j] ++ js は j :: js に定義的に一致）。 -/
theorem thetaValProd_rotate_left (R : CRing) (j : Int) (js : List Int) :
    thetaValProd R (j :: js) = thetaValProd R (js ++ [j]) := by
  show thetaValProd R ([j] ++ js) = thetaValProd R (js ++ [j])
  exact thetaValProd_block_swap R [j] js

/-! ## M258F-3: n 回左回転とその不変性 -/

/-- **M258F-3a: n 回左回転 rotateLeft n js** — 先頭要素を末尾へ回す操作
    j :: js ↦ js ++ [j] を n 回反復する。空列では恒等（回転先が無い）。 -/
def rotateLeft : Nat → List Int → List Int
  | 0, js => js
  | _ + 1, [] => []
  | n + 1, j :: js => rotateLeft n (js ++ [j])

/-- **定理 (M258F-3b): n 回左回転不変（新規・本丸）** — 任意の回数 n の
    左回転の下で多ラベル積は不変: thetaValProd R (rotateLeft n js)
    = thetaValProd R js。n に関する帰納: 0 回は恒等、n+1 回は空列で自明、
    非空列では M258F-2（単一ステップ左回転不変）を一段適用してから帰納
    法の仮定を js ++ [j] に適用する。 -/
theorem thetaValProd_rotateLeft (R : CRing) (n : Nat) :
    ∀ js : List Int, thetaValProd R (rotateLeft n js) = thetaValProd R js := by
  induction n with
  | zero =>
    intro js
    rfl
  | succ n ih =>
    intro js
    cases js with
    | nil => rfl
    | cons j js =>
      show thetaValProd R (rotateLeft n (js ++ [j])) = thetaValProd R (j :: js)
      rw [ih (js ++ [j])]
      exact (thetaValProd_rotate_left R j js).symm

/-! ## M258F-4: 総括レコード（ブロック入替・n 回左回転不変） -/

/-- **M258F-4a: テータ値多ラベル積ブロック入替・左回転不変データ** — M242F
    の多ラベル積 thetaValProd（連接則 prod_append・指数和単項式 prod_eq）と、
    それに加えてブロック入替不変（prod_block_swap・expSum_block_swap）・
    単一ステップ左回転不変（rotate_left）・n 回左回転不変
    （rotateLeft_invariant）を一括束ねる。M253F（長さ 1 の隣接対の入替）を
    任意長ブロックと反復巡回置換へ一般化した E-1 の値代数側 witness。 -/
structure ThetaValueProdBlockSwapData (R : CRing) where
  /-- 多ラベル積写像 js ↦ ∏ q^{j²}。 -/
  prod : List Int → (laurentRing R).carrier
  /-- 指数簿記 js ↦ Σ j²。 -/
  expSum : List Int → Int
  /-- 積は指数和単項式: ∏ q^{j²} = u^{Σj²}。 -/
  prod_eq : ∀ js : List Int, prod js = uMonHom R (expSum js)
  /-- ブロック入替不変（指数簿記側）: Σ_{xs++ys} = Σ_{ys++xs}。 -/
  expSum_block_swap : ∀ xs ys : List Int, expSum (xs ++ ys) = expSum (ys ++ xs)
  /-- ブロック入替不変: ∏_{xs++ys} = ∏_{ys++xs}。 -/
  prod_block_swap : ∀ xs ys : List Int, prod (xs ++ ys) = prod (ys ++ xs)
  /-- 単一ステップ左回転不変: ∏_{j::js} = ∏_{js++[j]}。 -/
  rotate_left : ∀ (j : Int) (js : List Int), prod (j :: js) = prod (js ++ [j])
  /-- n 回左回転不変: ∏_{rotateLeft n js} = ∏_{js}。 -/
  rotateLeft_invariant : ∀ (n : Nat) (js : List Int),
    prod (rotateLeft n js) = prod js

/-- **M258F-4b: witness 本体** — prod := thetaValProd R、expSum := thetaExpSum
    として全フィールドを M258F-1〜3 で埋める。 -/
def thetaValueProdBlockSwapData (R : CRing) : ThetaValueProdBlockSwapData R where
  prod := thetaValProd R
  expSum := thetaExpSum
  prod_eq := thetaValProd_eq_uMonHom R
  expSum_block_swap := thetaExpSum_block_swap
  prod_block_swap := thetaValProd_block_swap R
  rotate_left := thetaValProd_rotate_left R
  rotateLeft_invariant := thetaValProd_rotateLeft R

/-- **定理 (M258F-4c): テータ値多ラベル積ブロック入替・左回転不変データの
    存在（M258F 見出し）** — 任意の係数環 R に対し、テータ値 q^{j²} の
    有限多ラベル積が、任意長ブロックの入替と n 回の左回転（巡回置換）の
    下で不変であることを束ねたデータが存在する。M253F の長さ 1 の隣接対
    転置不変が、ブロック入替と反復巡回置換へ一般化される。 -/
theorem thetaValueProdBlockSwap_exists (R : CRing) :
    Nonempty (ThetaValueProdBlockSwapData R) :=
  ⟨thetaValueProdBlockSwapData R⟩

end IUT
