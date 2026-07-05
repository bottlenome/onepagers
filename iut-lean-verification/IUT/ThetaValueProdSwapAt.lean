/-
  IUT/ThetaValueProdSwapAt.lean — M253F: テータ値多ラベル積の任意位置隣接転置不変
  （swap-at-position invariance・柱E E-1 並行部品）

  柱E 残課題 E-1（#39）の「値の代数構造」切片の続き。M242F
  （ThetaValueProdLaws.lean）はテータ値の有限多ラベル積 thetaValProd の
  並べ替え不変性を、**列の逆順**（thetaValProd_reverse）と**先頭二要素の
  転置**（thetaValProd_swap、位置 0,1 のみ）という二つの代表インスタンスに
  限って確立していた（M242F ヘッダの正直な限定に明記の通り、一般の対称群
  作用 List.Perm 全体は範囲外）。ただし先頭転置は「列の**先頭**」という
  特殊位置に限られており、列の**任意の位置**にある隣接二要素の転置に
  ついては M242F では扱っていなかった。

  本モジュールは M242F の thetaValProd_append（連接則）と thetaValProd_swap
  （先頭転置不変）を土台に、

    (A) **任意位置の指数和隣接転置不変（新規）**: 列を pre ++ [j,j'] ++ post
        （前置 pre・後置 post は任意）と分解したとき、指数和は j, j' の順序に
        依らない thetaExpSum (pre ++ j::j'::post)
        = thetaExpSum (pre ++ j'::j::post)（M242F-1a 連接加法性 +
        Int.add_left_comm）;
    (B) **任意位置の多ラベル積隣接転置不変（新規・本丸）**: 同じ分解の下で
        多ラベル積そのものも不変 thetaValProd R (pre ++ j::j'::post)
        = thetaValProd R (pre ++ j'::j::post)。列を pre と (j::j'::post) の
        連接として厚み分解し（M242F-2 thetaValProd_append）、後半部分にのみ
        M242F-3c の先頭転置不変（thetaValProd_swap）を適用してから連接則で
        貼り戻す、という「連接則 + 先頭転置」の合成で先頭以外の任意位置へ
        一般化する;
    (C) **M242F-3c との整合（新規）**: pre := [] に特殊化すると
        thetaValProd_swap_at は M242F-3c thetaValProd_swap と一致する
        （先頭転置が任意位置転置の特殊例であることの確認）

    を機械検証し、隣接転置不変性を「列の先頭」から「列の任意の位置」へ
    厳密に一般化する。

  * M253F-1 `thetaExpSum_swap_at` — 任意位置の指数和隣接転置不変（新規）
  * M253F-2 `thetaValProd_swap_at` — 任意位置の多ラベル積隣接転置不変
    （新規・本丸）
  * M253F-3 `thetaValProd_swap_at_nil` — pre=[] 特殊化と M242F-3c との整合
    （新規）
  * M253F-4 総括レコード `ThetaValueProdSwapAtData` / `thetaValueProdSwapAtData`
    / `thetaValueProdSwapAt_exists` — capstone

  意義: M242F の「先頭二要素の転置不変」という代表インスタンスを、
  「列中の**任意の隣接対**の転置不変」へ厳密に一般化する。これは列を
  pre ++ [j,j'] ++ post という形へ分解できるあらゆる隣接対（＝列中の
  あらゆる隣接位置）を尽くしており、「隣接転置不変性」という性質そのもの
  としては完結した結果である。テータ値の多ラベル積を可換モノイド上の
  畳み込みとして代数化する E-1 の値代数側 witness を、M242F の連接則と
  先頭転置不変の合成のみで前進させる。

  正直な限定（スライス A+B+C）: 扱うのはテータ値 q^{j²} が住む Laurent
  環単元群の**有限多ラベル積**について、列中の**任意位置にある隣接二要素**
  の転置の下での不変性のみ。ここで「任意位置」とは列を
  pre ++ [j,j'] ++ post の形に分解できる任意の前置・後置 pre, post を指す
  （＝隣接対の位置が列のどこにあってもよいという意味）。これは列の
  **隣接互換のみ**による不変性であり、列全体の**任意の並べ替え**
  （List.Perm・対称群作用全体）の不変性はここでも扱わない（M242F と同様
  範囲外。ただし対称群は隣接互換で生成されるため、本モジュールの結果は
  そのための構成要素の一つに過ぎず、任意並べ替え不変性そのものの証明は
  含まない）。テータ値がラベル上でなす**環準同型**や**ガロア同変な p 進
  テータ値**・**tempered π₁ の商としての実現**・**エタールテータ関数値
  そのものの構成**は M223F/M232F/M237F/M242F 同様 E-1 残として範囲外
  （本モジュールでは一切主張しない）。q の付値・q-展開の収束も扱わない。
  全て選択公理を証明本体で新規導入せず（M242F/M237F/M232F/M223F から
  継承、新規 Classical・新規 Classical.choice なし。商 laurentRing /
  laurentRel / Quot レベルの主張は Quot.sound を使う —— 商構成に内在、
  選択公理ではない）。#print axioms により継承分のみであることを確認済み。
  サブエージェント並行部品。
-/
import IUT.ThetaValueProdLaws

namespace IUT

/-! ## M253F-1: 任意位置の指数和隣接転置不変 -/

/-- **定理 (M253F-1): 任意位置の指数和隣接転置不変（新規）** — 列を
    pre ++ [j,j'] ++ post に分解したとき、指数和は j, j' の順序に依らない:
    thetaExpSum (pre ++ j::j'::post) = thetaExpSum (pre ++ j'::j::post)。
    M242F-1a 連接加法性で pre 側と (j::j'::post) 側へ分けたのち、後半の
    先頭二項を Int.add_left_comm で入れ替える。M242F-3a（逆順不変）と並ぶ
    「先頭以外の位置」への隣接転置不変性の指数簿記側。 -/
theorem thetaExpSum_swap_at (pre : List Int) (j j' : Int) (post : List Int) :
    thetaExpSum (pre ++ j :: j' :: post) = thetaExpSum (pre ++ j' :: j :: post) := by
  rw [thetaExpSum_append, thetaExpSum_append]
  show thetaExpSum pre + (thetaValExp j + (thetaValExp j' + thetaExpSum post))
    = thetaExpSum pre + (thetaValExp j' + (thetaValExp j + thetaExpSum post))
  rw [Int.add_left_comm (thetaValExp j) (thetaValExp j') (thetaExpSum post)]

/-! ## M253F-2: 任意位置の多ラベル積隣接転置不変（本丸） -/

/-- **定理 (M253F-2): 任意位置の多ラベル積隣接転置不変（新規・本丸）** —
    列を pre ++ [j,j'] ++ post に分解したとき、多ラベル積は j, j' の順序に
    依らない: thetaValProd R (pre ++ j::j'::post)
    = thetaValProd R (pre ++ j'::j::post)。列を pre と (j::j'::post) の
    連接として分解し（M242F-2 thetaValProd_append を両辺に適用）、後半
    部分にのみ M242F-3c の先頭転置不変（thetaValProd_swap）を適用してから
    連接則で貼り戻す。M242F-3c（列の**先頭**のみの転置不変）を、列の
    **任意の位置**の隣接転置不変へ一般化する本モジュールの本丸。 -/
theorem thetaValProd_swap_at (R : CRing) (pre : List Int) (j j' : Int)
    (post : List Int) :
    thetaValProd R (pre ++ j :: j' :: post)
      = thetaValProd R (pre ++ j' :: j :: post) := by
  rw [thetaValProd_append R pre (j :: j' :: post),
    thetaValProd_append R pre (j' :: j :: post),
    thetaValProd_swap R j j' post]

/-! ## M253F-3: pre=[] 特殊化と M242F-3c との整合 -/

/-- **定理 (M253F-3): pre=[] 特殊化と M242F-3c との整合（新規）** —
    M253F-2 thetaValProd_swap_at を pre := [] に特殊化すると、M242F-3c
    thetaValProd_swap（先頭転置不変）にちょうど一致する。先頭転置が
    「任意位置」隣接転置の特殊例であることの確認。 -/
theorem thetaValProd_swap_at_nil (R : CRing) (j j' : Int) (post : List Int) :
    thetaValProd R (j :: j' :: post) = thetaValProd R (j' :: j :: post) :=
  thetaValProd_swap_at R [] j j' post

/-! ## M253F-4: 総括レコード（任意位置隣接転置不変） -/

/-- **M253F-4a: テータ値多ラベル積任意位置転置不変データ** — M242F の
    多ラベル積 thetaValProd（連接則 prod_append・指数和単項式 prod_eq）と、
    それに加えて列中の**任意位置**の隣接転置不変（swap_at）・その指数簿記
    側（expSum_swap_at）を一括束ねる。M242F-3c（先頭転置のみ）を任意位置へ
    一般化した E-1 の値代数側 witness。 -/
structure ThetaValueProdSwapAtData (R : CRing) where
  /-- 多ラベル積写像 js ↦ ∏ q^{j²}。 -/
  prod : List Int → (laurentRing R).carrier
  /-- 指数簿記 js ↦ Σ j²。 -/
  expSum : List Int → Int
  /-- 積は指数和単項式: ∏ q^{j²} = u^{Σj²}。 -/
  prod_eq : ∀ js : List Int, prod js = uMonHom R (expSum js)
  /-- 多ラベル積の連接則: ∏_{js++ks} = (∏_{js})·(∏_{ks})。 -/
  prod_append : ∀ js ks : List Int,
    prod (js ++ ks) = (laurentRing R).mul (prod js) (prod ks)
  /-- 任意位置の指数和隣接転置不変: Σ_{pre++j::j'::post} = Σ_{pre++j'::j::post}。 -/
  expSum_swap_at : ∀ (pre : List Int) (j j' : Int) (post : List Int),
    expSum (pre ++ j :: j' :: post) = expSum (pre ++ j' :: j :: post)
  /-- 任意位置の多ラベル積隣接転置不変: ∏_{pre++j::j'::post}
      = ∏_{pre++j'::j::post}。 -/
  prod_swap_at : ∀ (pre : List Int) (j j' : Int) (post : List Int),
    prod (pre ++ j :: j' :: post) = prod (pre ++ j' :: j :: post)

/-- **M253F-4b: witness 本体** — prod := thetaValProd R、expSum := thetaExpSum
    として全フィールドを M242F・M253F-1〜2 で埋める。 -/
def thetaValueProdSwapAtData (R : CRing) : ThetaValueProdSwapAtData R where
  prod := thetaValProd R
  expSum := thetaExpSum
  prod_eq := thetaValProd_eq_uMonHom R
  prod_append := thetaValProd_append R
  expSum_swap_at := thetaExpSum_swap_at
  prod_swap_at := thetaValProd_swap_at R

/-- **定理 (M253F-4c): テータ値多ラベル積任意位置転置不変データの存在
    （M253F 見出し）** — 任意の係数環 R に対し、テータ値 q^{j²} の有限
    多ラベル積が、列中の**任意位置**にある隣接二要素の転置の下で不変で
    あることを束ねたデータが存在する。M242F-3c の先頭転置不変が列の
    任意位置へ一般化される。 -/
theorem thetaValueProdSwapAt_exists (R : CRing) :
    Nonempty (ThetaValueProdSwapAtData R) :=
  ⟨thetaValueProdSwapAtData R⟩

end IUT
