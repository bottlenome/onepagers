/-
  IUT/ThetaValueProdPerm.lean — M256F: テータ値多ラベル積の任意並べ替え不変
  （full symmetric-group / List.Perm invariance・柱E E-1 並行部品）

  ── 二軸ヘッダ（CLAUDE.md §1）─────────────────────────────────
  主要成果の分類: [実／(a)昇格]。M242F/M253F が「正直な限定」として
    **明示的に範囲外**と申告していた「一般の対称群作用（List.Perm 全体）の
    不変性」を、Lean 4 core の `List.Perm`（4 構成子 nil/cons/swap/trans）
    上の帰納で**本物に閉じる**。テータ値 q^{j²} の有限多ラベル積
    thetaValProd が、ラベル列の**任意の並べ替え**の下で不変であること
    ＝積がラベルの**多重集合（multiset）のみに依存する**（列順序に依らない）
    ことを機械検証し、E2 テータ値代数の「値の並べ替え不変性」を
    隣接互換の代表インスタンスから対称群全体へ昇格させる。
  complete_pct 影響: E 0.42→0.42（+ε・真水）。本モジュールは E2 テータ値
    代数（q^{j²} の Laurent 単項式実体化）の**既申告の honest-limitation を
    一つ実際に閉じる**真水前進であり、骨格追加でも capstone 束ねでもない
    （M242F/M253F が「List.Perm 全体は扱わない」と明記していた当の主張を
    新規に証明する）。ただし増分は小さく、E-1 残（q-展開収束・ガロア同変
    p 進テータ値・tempered π₁）は依然未形式化のため complete_pct の
    表示値は 42 を据え置き、内訳注記に「E2 の並べ替え不変が対称群全体へ
    昇格（多重集合 well-defined）」を追記する水準の前進。
  正直な限定（弱めない）: 扱うのはテータ値 q^{j²} が住む Laurent 環単元群の
    **有限多ラベル積の対称群不変性**（＝多重集合 well-defined 性）のみ。
    これはテータ値の積が可換モノイド (laurentRing R, ×, 1) 上の畳み込みで
    あり指数和 uMonHom R (thetaExpSum ·) を経由することの帰結である。
    テータ値がラベル上でなす**環準同型**や**ガロア同変な p 進テータ値**・
    **tempered π₁ の商としての実現**・**エタールテータ関数値そのものの
    構成**・**q の付値・q-展開の収束**は M223F/M232F/M237F/M242F/M253F
    同様 E-1 残として範囲外（本モジュールでは一切主張しない）。
  ────────────────────────────────────────────────────────────

  柱E 残課題 E-1（#39）の「値の代数構造」切片の続き。M242F
  （ThetaValueProdLaws.lean）はテータ値の有限多ラベル積 thetaValProd の
  並べ替え不変性を**逆順**（thetaValProd_reverse）と**先頭転置**
  （thetaValProd_swap）に限って、M253F（ThetaValueProdSwapAt.lean）は
  **列中の任意位置の隣接転置**（thetaValProd_swap_at）まで確立していた。
  だが両モジュールとも「正直な限定」に **「一般の対称群作用（List.Perm
  全体）の不変性は扱わない（隣接互換が対称群を生成するとはいえ、その
  一般形は List.Perm の帰納で別途）」** と明記していた。本モジュールは
  まさにその **List.Perm 全体の帰納**を実行してこの限定を閉じる。

  土台は (1) M242F-1a thetaExpSum_append（指数和の連接加法性）— は使わず、
  Lean core の List.Perm の 4 構成子（nil/cons/swap/trans）に沿った直接
  帰納、(2) M237F-4c thetaValProd_eq_uMonHom（積 = 指数和単項式）、
  (3) Int.add_left_comm（swap 構成子の可換律）。

    (A) **指数和の対称群不変（新規）** thetaExpSum_perm:
        js.Perm ks → thetaExpSum js = thetaExpSum ks。List.Perm の帰納で
        nil（rfl）・cons（先頭固定＋帰納法）・swap（Int.add_left_comm）・
        trans（Eq.trans）の 4 ケースを閉じる。指数簿記が多重集合のみに依存;
    (B) **多ラベル積の対称群不変（新規・本丸）** thetaValProd_perm:
        js.Perm ks → thetaValProd R js = thetaValProd R ks。積が指数和
        単項式 uMonHom R (thetaExpSum ·) を経由し（M237F-4c）、指数和が
        対称群不変（A）であることの帰結。テータ値の有限積が**ラベルの
        多重集合のみに依存する**（列順序に依らず well-defined）;
    (C) **既存インスタンスの対称群不変からの再導出（統合・整合）**:
        逆順 thetaValProd_reverse（core List.reverse_perm）・連接可換
        thetaValProd_append_comm（core List.perm_append_comm）・任意位置
        隣接転置 thetaValProd_swap_at（core List.Perm.append + swap）が
        すべて (B) の**特殊例**として再導出でき、M242F-3a/3b/3c・M253F-2 を
        対称群不変が厳密に**包摂**することを確認する。

  * M256F-1 `thetaExpSum_perm` — 指数和の対称群不変（List.Perm 帰納・新規）
  * M256F-2 `thetaValProd_perm` — 多ラベル積の対称群不変（新規・本丸）
  * M256F-3 `thetaValProd_reverse_of_perm` / `thetaValProd_append_comm` /
    `thetaValProd_swap_at_of_perm` — 既存インスタンスの再導出（包摂の確認）
  * M256F-4 総括レコード `ThetaValueProdPermData` / `thetaValueProdPermData`
    / `thetaValueProdPerm_exists` — capstone

  全て選択公理を証明本体で新規導入せず（List.Perm は core inductive、
  Int.add_left_comm は core、M237F-4c から継承。新規 Classical・新規
  Classical.choice なし。商 laurentRing / laurentRel / Quot レベルの主張は
  Quot.sound を使う —— 商構成に内在、選択公理ではない）。#print axioms に
  より [propext, Quot.sound]（指数和のみの M256F-1 は [propext]）で
  あることを確認済み。サブエージェント並行部品。
-/
import IUT.ThetaValueProdSwapAt

namespace IUT

/-! ## M256F-1: 指数和の対称群不変（List.Perm 帰納） -/

/-- **定理 (M256F-1): 指数和の対称群不変（新規）** — ラベル列 js が ks の
    並べ替え（js.Perm ks）であれば、指数和は等しい:
    thetaExpSum js = thetaExpSum ks。Lean core `List.Perm` の 4 構成子
    （nil/cons/swap/trans）に沿った帰納で閉じる。swap ケースが
    Int.add_left_comm（thetaValExp の可換律）、cons ケースが先頭固定＋
    帰納法。M242F-3a（逆順不変）を対称群全体へ拡げた指数簿記側であり、
    テータ値の指数和が**ラベルの多重集合のみに依存する**ことを示す。 -/
theorem thetaExpSum_perm {js ks : List Int} (h : js.Perm ks) :
    thetaExpSum js = thetaExpSum ks := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    show thetaValExp x + thetaExpSum _ = thetaValExp x + thetaExpSum _
    rw [ih]
  | swap x y l =>
    show thetaValExp y + (thetaValExp x + thetaExpSum l)
      = thetaValExp x + (thetaValExp y + thetaExpSum l)
    rw [Int.add_left_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-! ## M256F-2: 多ラベル積の対称群不変（本丸） -/

/-- **定理 (M256F-2): 多ラベル積の対称群不変（新規・本丸）** — ラベル列 js が
    ks の並べ替え（js.Perm ks）であれば、テータ値の有限多ラベル積は等しい:
    thetaValProd R js = thetaValProd R ks。積が指数和単項式
    uMonHom R (thetaExpSum ·) を経由し（M237F-4c thetaValProd_eq_uMonHom）、
    指数和が対称群不変（M256F-1）であることの帰結。これは**テータ値 q^{j²}
    の有限積がラベルの多重集合のみに依存する**（列順序に依らず well-defined
    な多重集合上の関数として定まる）ことの機械検証であり、M242F/M253F が
    「List.Perm 全体は扱わない」と明記していた honest-limitation を閉じる。 -/
theorem thetaValProd_perm (R : CRing) {js ks : List Int} (h : js.Perm ks) :
    thetaValProd R js = thetaValProd R ks := by
  rw [thetaValProd_eq_uMonHom R js, thetaValProd_eq_uMonHom R ks,
    thetaExpSum_perm h]

/-! ## M256F-3: 既存インスタンスの再導出（対称群不変が包摂することの確認） -/

/-- **定理 (M256F-3a): 逆順不変の対称群不変からの再導出** — M242F-3b
    thetaValProd_reverse（逆順不変）は、core `List.reverse_perm`
    （js.reverse.Perm js）と M256F-2 の合成で再導出できる。逆順が並べ替えの
    一種であることの確認（M242F-3b を対称群不変が包摂する）。 -/
theorem thetaValProd_reverse_of_perm (R : CRing) (js : List Int) :
    thetaValProd R (List.reverse js) = thetaValProd R js :=
  thetaValProd_perm R (List.reverse_perm js)

/-- **定理 (M256F-3b): 連接可換（新規・対称群不変の系）** — テータ値多ラベル
    積は連接の順序に依らない: thetaValProd R (js ++ ks)
    = thetaValProd R (ks ++ js)。core `List.perm_append_comm`
    ((js++ks).Perm (ks++js)) と M256F-2 の合成。M242F-2 の連接則
    （∏_{js++ks}=(∏js)·(∏ks)）に**連接の可換性**を加える系であり、積の
    多重集合依存性の直接の帰結。 -/
theorem thetaValProd_append_comm (R : CRing) (js ks : List Int) :
    thetaValProd R (js ++ ks) = thetaValProd R (ks ++ js) :=
  thetaValProd_perm R List.perm_append_comm

/-- **定理 (M256F-3c): 任意位置隣接転置不変の対称群不変からの再導出** —
    M253F-2 thetaValProd_swap_at（列中の任意位置 pre++[j,j']++post の隣接
    転置不変）は、core `List.Perm.append`（pre の refl と swap 構成子の連接）
    と M256F-2 の合成で再導出できる。M253F-2 を対称群不変が包摂することの
    確認（swap 構成子 (j::j'::post).Perm (j'::j::post) を pre に append）。 -/
theorem thetaValProd_swap_at_of_perm (R : CRing) (pre : List Int) (j j' : Int)
    (post : List Int) :
    thetaValProd R (pre ++ j :: j' :: post)
      = thetaValProd R (pre ++ j' :: j :: post) :=
  thetaValProd_perm R ((List.Perm.refl pre).append (List.Perm.swap j' j post))

/-! ## M256F-4: 総括レコード（対称群不変 = 多重集合 well-defined 性） -/

/-- **M256F-4a: テータ値多ラベル積対称群不変データ** — テータ値 q^{j²} の
    有限多ラベル積 thetaValProd と指数和 thetaExpSum が、ラベル列の
    **任意の並べ替え**（List.Perm）の下で不変であることを束ねる。すなわち
    両者はラベルの**多重集合のみに依存する** well-defined な関数である。
    さらに逆順・連接可換・任意位置隣接転置が対称群不変の特殊例として
    従うことを併せて保持する。M242F-3/M253F-2 の隣接互換代表インスタンスを
    対称群全体へ昇格した E-1 の値代数側 witness。 -/
structure ThetaValueProdPermData (R : CRing) where
  /-- 多ラベル積写像 js ↦ ∏ q^{j²}。 -/
  prod : List Int → (laurentRing R).carrier
  /-- 指数簿記 js ↦ Σ j²。 -/
  expSum : List Int → Int
  /-- 積は指数和単項式: ∏ q^{j²} = u^{Σj²}。 -/
  prod_eq : ∀ js : List Int, prod js = uMonHom R (expSum js)
  /-- 指数和の対称群不変: js.Perm ks → Σ_{js} = Σ_{ks}。 -/
  expSum_perm : ∀ {js ks : List Int}, js.Perm ks → expSum js = expSum ks
  /-- 多ラベル積の対称群不変（本丸）: js.Perm ks → ∏_{js} = ∏_{ks}。
      積がラベルの多重集合のみに依存する（列順序に依らない）。 -/
  prod_perm : ∀ {js ks : List Int}, js.Perm ks → prod js = prod ks
  /-- 逆順不変（対称群不変の系）: ∏_{reverse js} = ∏_{js}。 -/
  prod_reverse : ∀ js : List Int, prod (List.reverse js) = prod js
  /-- 連接可換（対称群不変の系）: ∏_{js++ks} = ∏_{ks++js}。 -/
  prod_append_comm : ∀ js ks : List Int, prod (js ++ ks) = prod (ks ++ js)
  /-- 任意位置隣接転置不変（対称群不変の系）: ∏_{pre++j::j'::post}
      = ∏_{pre++j'::j::post}。 -/
  prod_swap_at : ∀ (pre : List Int) (j j' : Int) (post : List Int),
    prod (pre ++ j :: j' :: post) = prod (pre ++ j' :: j :: post)

/-- **M256F-4b: witness 本体** — prod := thetaValProd R、expSum := thetaExpSum
    として全フィールドを M256F-1〜3・M237F-4c で埋める。 -/
def thetaValueProdPermData (R : CRing) : ThetaValueProdPermData R where
  prod := thetaValProd R
  expSum := thetaExpSum
  prod_eq := thetaValProd_eq_uMonHom R
  expSum_perm := thetaExpSum_perm
  prod_perm := thetaValProd_perm R
  prod_reverse := thetaValProd_reverse_of_perm R
  prod_append_comm := thetaValProd_append_comm R
  prod_swap_at := thetaValProd_swap_at_of_perm R

/-- **定理 (M256F-4c): テータ値多ラベル積対称群不変データの存在（M256F 見出し）**
    — 任意の係数環 R に対し、テータ値 q^{j²} の有限多ラベル積が、ラベル列の
    **任意の並べ替え**（List.Perm 全体）の下で不変である（＝ラベルの多重集合
    のみに依存する well-defined な関数である）ことを、逆順・連接可換・任意
    位置隣接転置の系とともに束ねたデータが存在する。M242F/M253F が honest-
    limitation として明示的に範囲外としていた「List.Perm 全体の不変性」を
    実際に閉じ、E2 テータ値代数の並べ替え不変性を対称群全体へ昇格する。 -/
theorem thetaValueProdPerm_exists (R : CRing) :
    Nonempty (ThetaValueProdPermData R) :=
  ⟨thetaValueProdPermData R⟩

end IUT
