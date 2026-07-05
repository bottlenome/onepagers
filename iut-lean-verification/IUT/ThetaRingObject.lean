/-
  IUT/ThetaRingObject.lean — M232F: テータ値の環写像対象
  （ring-structure map object・柱E E-1 並行部品）

  柱E 残課題 E-1（#39）の「環写像対象」切片。M223F
  （ThetaValueConstruct.lean）はテータ値 q^{j²} を Laurent 環
  laurentRing R の単項式 `thetaValMonomial R j`（= 指数 thetaValExp j
  = j² の単項式）として実体化し、基点 q^{0²}=1・乗法的漸化式
  q^{(j+1)²}=q^{j²}·q^{2j+1}・反転 q^{(l−j)²}=q^{j²}·q^{l·k}・評価写像
  j↦q^{j²} の単射性を値レベルで確立していた。ただし M223F は各テータ値を
  **個別の環の元**として扱うにとどまり、テータ値がその上に住む
  **環構造への写像対象**（指数モノイド (ℤ,+) から乗法モノイド
  (laurentRing R, ×, 1) への準同型）を対象として束ねてはいなかった。

  本モジュールは M88F（LaurentMonomial.lean）の単項式機械
  （`laurent_uMon_mul` = 指数法則 u^a·u^b = u^{a+b}、`laurent_uMon_zero`
  = u^0 = 1、`laurent_uMon_unit` = u^c は単元 u^c·u^{−c}=1）を土台に、

    (A) **指数モノイド準同型 uMonHom**: 単項式指数写像
        m ↦ u^m : (ℤ,+) → (laurentRing R, ×, 1) を対象として構成し、
        単位（u^0=1）・加法性（u^{a+b}=u^a·u^b、加法→乗法）・単元性
        （u^c·u^{−c}=1）を束ねる —— これがテータ値が住む**環写像対象**;
    (B) **テータ値の写像対象経由の実現**: thetaValMonomial R j
        = uMonHom R (thetaValExp j)（テータ値 q^{j²} は指数 j² における
        写像対象の像）;
    (C) **テータ値の乗法的合成則（新規）**: q^{j²}·q^{j'²}
        = u^{j²+j'²} = uMonHom R (thetaValExp j + thetaValExp j')。
        二つのテータ値の積が指数の和の単項式になる —— M223F には無い
        乗法的合成の環論的表現;
    (D) **テータ値の単元性/可逆性（新規）**: q^{j²}·u^{−j²} = 1。
        テータ値は Laurent 環の**単元群**に住み、逆元 u^{−j²} を持つ ——
        M223F には無い環構造（可逆性）の内容

    を機械検証し、これらを一つの**環写像対象データ**へ束ねる。

  * M232F-1 `uMonHom` / `uMonHom_zero` / `uMonHom_add` / `uMonHom_unit`
    — 指数モノイド準同型 m ↦ u^m とその単位・加法性・単元性
  * M232F-2 `thetaValMonomial_eq_uMonHom` / `thetaValMonomial_mul` /
    `thetaValMonomial_unit` — テータ値の写像対象経由の実現・乗法的
    合成則（新規）・単元性（新規）
  * M232F-3 `LaurentMonomialHom` / `uMonomialRingHom` — 環写像対象
    （指数モノイド準同型）を構造として束ねる本体
  * M232F-4 総括レコード `ThetaRingObjectData` / `thetaRingObjectData` /
    `thetaRingObject_exists` — テータ値を環写像対象経由で束ねる capstone

  意義: M223F の**個別テータ値**（Laurent 環の元 q^{j²}）を、それらが
  住む**環構造への写像対象**（指数モノイド準同型 (ℤ,+)→(laurentRing R,×)）
  として対象化し、テータ値の乗法的合成則 q^{j²}·q^{j'²}=q^{j²+j'²} と
  単元性 q^{j²}·q^{−j²}=1 を新たに与える。指数簿記から値構成（M223F）へ
  進んだ E-1 を、値の**環写像対象**（写像の対象化・乗法合成・可逆性）へ
  一歩進める。

  正直な限定（スライス A+B+C+D）: 扱うのはテータ値 q^{j²} が住む
  **Laurent 環の乗法モノイドへの指数写像対象**（単位・加法性・単元性）と、
  テータ値の写像対象経由の実現・乗法的合成則・単元性のみ。ここで
  「環写像対象」とは指数モノイド (ℤ,+) から乗法モノイド
  (laurentRing R, ×, 1) への準同型の意味であり、テータ値がラベル j 上で
  なす**環そのものの準同型**（テータ環→係数環の環準同型・ガロア同変な
  評価環写像）ではない。実際テータ値写像 j↦q^{j²} は指数 j↦j² が非加法的
  なためラベル上のモノイド準同型ではなく、環写像対象は**指数側**（すでに
  加法的な (ℤ,+)）でのみモノイド準同型になる。q の付値・q-展開の収束・
  エタールテータ関数値そのものの構成、**ガロア同変な p 進テータ値**、
  **tempered π₁ の商としての実現**は M223F/M209F/M212F 同様 E-1 残として
  範囲外（本モジュールでは一切主張しない）。全て選択公理不使用
  （M223F/M88F から継承、新規 Classical・新規 Classical.choice なし。
  商 laurentRing / laurentRel / Quot レベルの主張は Quot.sound を使う —
  商構成に内在、選択公理ではない）。サブエージェント並行部品。
-/
import IUT.ThetaValueConstruct

namespace IUT

/-! ## M232F-1: 指数モノイド準同型 uMonHom -/

/-- **M232F-1a: 指数モノイド準同型 uMonHom** — 単項式指数写像
    m ↦ u^m を Laurent 環 laurentRing R の元として与える写像対象。
    テータ値 q^{j²} が住む環構造への写像の主役（指数 m を Laurent 環の
    単項式 u^m に送る）。 -/
def uMonHom (R : CRing) (m : Int) : (laurentRing R).carrier :=
  Quot.mk (laurentRel R) (uMon R m)

/-- **定理 (M232F-1b): 単位** — u^0 = 1（M88F laurent_uMon_zero）。
    写像対象の単位律（加法単位 0 ↦ 乗法単位 1）。 -/
theorem uMonHom_zero (R : CRing) : uMonHom R 0 = (laurentRing R).one :=
  laurent_uMon_zero R

/-- **定理 (M232F-1c): 加法性（加法→乗法）** — u^{a+b} = u^a·u^b
    （M88F laurent_uMon_mul）。指数モノイド (ℤ,+) から乗法モノイド
    (laurentRing R, ×) への準同型性。 -/
theorem uMonHom_add (R : CRing) (a b : Int) :
    uMonHom R (a + b)
      = (laurentRing R).mul (uMonHom R a) (uMonHom R b) :=
  (laurent_uMon_mul R a b).symm

/-- **定理 (M232F-1d): 単元性** — u^c·u^{−c} = 1（M88F laurent_uMon_unit）。
    写像対象の像は Laurent 環の**単元群**に住む（負冪の可逆性）。 -/
theorem uMonHom_unit (R : CRing) (c : Int) :
    (laurentRing R).mul (uMonHom R c) (uMonHom R (-c))
      = (laurentRing R).one :=
  laurent_uMon_unit R c

/-! ## M232F-2: テータ値の写像対象経由の実現・乗法合成・単元性 -/

/-- **定理 (M232F-2a): テータ値 = 写像対象の像** — thetaValMonomial R j
    = uMonHom R (thetaValExp j)。テータ値 q^{j²} は指数 j²（M209F
    thetaValExp）における環写像対象の像（定義的一致）。 -/
theorem thetaValMonomial_eq_uMonHom (R : CRing) (j : Int) :
    thetaValMonomial R j = uMonHom R (thetaValExp j) :=
  rfl

/-- **定理 (M232F-2b): テータ値の乗法的合成則（新規）** —
    q^{j²}·q^{j'²} = u^{j²+j'²} = uMonHom R (thetaValExp j + thetaValExp j')。
    二つのテータ値の積が指数の和の単項式になる（M88F laurent_uMon_mul）。
    M223F の一段漸化式を任意の二テータ値の積へ一般化した環論的合成則。 -/
theorem thetaValMonomial_mul (R : CRing) (j j' : Int) :
    (laurentRing R).mul (thetaValMonomial R j) (thetaValMonomial R j')
      = uMonHom R (thetaValExp j + thetaValExp j') := by
  show (laurentRing R).mul (Quot.mk (laurentRel R) (uMon R (thetaValExp j)))
      (Quot.mk (laurentRel R) (uMon R (thetaValExp j')))
    = Quot.mk (laurentRel R) (uMon R (thetaValExp j + thetaValExp j'))
  exact laurent_uMon_mul R (thetaValExp j) (thetaValExp j')

/-- **定理 (M232F-2c): テータ値の単元性/可逆性（新規）** —
    q^{j²}·u^{−j²} = 1。テータ値は Laurent 環の**単元群**に住み、逆元
    u^{−j²} を持つ（M88F laurent_uMon_unit）。M223F には無い環構造
    （可逆性）の内容。 -/
theorem thetaValMonomial_unit (R : CRing) (j : Int) :
    (laurentRing R).mul (thetaValMonomial R j)
        (uMonHom R (-(thetaValExp j)))
      = (laurentRing R).one :=
  laurent_uMon_unit R (thetaValExp j)

/-! ## M232F-3: 環写像対象（指数モノイド準同型） -/

/-- **M232F-3a: Laurent 単項式写像対象** — 指数モノイド (ℤ,+) から
    Laurent 環 laurentRing R の乗法モノイド (×, 1) への準同型を束ねる
    構造。テータ値がその上に住む環構造への写像対象。単位（map_zero）・
    加法性（map_add、加法→乗法）・単元性（map_unit、像は単元群）を持つ。 -/
structure LaurentMonomialHom (R : CRing) where
  /-- 写像本体: 指数 m ↦ Laurent 環の元。 -/
  toRing : Int → (laurentRing R).carrier
  /-- 単位律: 加法単位 0 ↦ 乗法単位 1。 -/
  map_zero : toRing 0 = (laurentRing R).one
  /-- 加法性: u^{a+b} = u^a·u^b（加法モノイド → 乗法モノイド）。 -/
  map_add : ∀ a b : Int,
    toRing (a + b) = (laurentRing R).mul (toRing a) (toRing b)
  /-- 単元性: 像は Laurent 環の単元群に住む（u^c·u^{−c} = 1）。 -/
  map_unit : ∀ c : Int,
    (laurentRing R).mul (toRing c) (toRing (-c)) = (laurentRing R).one

/-- **M232F-3b: 環写像対象の witness** — uMonHom を写像対象として束ねる。 -/
def uMonomialRingHom (R : CRing) : LaurentMonomialHom R where
  toRing := uMonHom R
  map_zero := uMonHom_zero R
  map_add := uMonHom_add R
  map_unit := uMonHom_unit R

/-! ## M232F-4: 総括レコード（テータ値の環写像対象） -/

/-- **M232F-4a: テータ値環写像対象データ** — テータ値 q^{j²} を、それらが
    住む環写像対象（指数モノイド準同型 hom）経由で束ねる総括レコード。
    写像対象 hom、テータ値写像 thetaVal、写像対象経由の実現
    (via_hom)、基点 q^{0²}=1、乗法的漸化式 q^{(j+1)²}=q^{j²}·q^{2j+1}
    （M223F）、反転 q^{(l−j)²}=q^{j²}·q^{l·k}（M223F）、乗法的合成則
    q^{j²}·q^{j'²}=u^{j²+j'²}（新規）、単元性 q^{j²}·u^{−j²}=1（新規）を
    一括束ね。E-1 の指数簿記 → 値構成 → 環写像対象 の witness。 -/
structure ThetaRingObjectData (R : CRing) where
  /-- 環写像対象: 指数モノイド (ℤ,+) → 乗法モノイド (laurentRing R,×,1)。 -/
  hom : LaurentMonomialHom R
  /-- テータ値写像: j ↦ q^{j²}。 -/
  thetaVal : Int → (laurentRing R).carrier
  /-- 写像対象経由の実現: q^{j²} = hom(j²)。 -/
  via_hom : ∀ j : Int, thetaVal j = hom.toRing (thetaValExp j)
  /-- 基点: q^{0²} = 1。 -/
  base : thetaVal 0 = (laurentRing R).one
  /-- 乗法的漸化式: q^{(j+1)²} = q^{j²}·q^{2j+1}（M223F）。 -/
  val_rec : ∀ j : Int, thetaVal (j + 1)
    = (laurentRing R).mul (thetaVal j) (hom.toRing (2 * j + 1))
  /-- 反転: q^{(l−j)²} = q^{j²}·q^{l·k}（M223F）。 -/
  pm : ∀ l j : Int, ∃ k : Int, thetaVal (l - j)
    = (laurentRing R).mul (thetaVal j) (hom.toRing (l * k))
  /-- 乗法的合成則（新規）: q^{j²}·q^{j'²} = hom(j²+j'²)。 -/
  mul : ∀ j j' : Int,
    (laurentRing R).mul (thetaVal j) (thetaVal j')
      = hom.toRing (thetaValExp j + thetaValExp j')
  /-- 単元性（新規）: q^{j²}·hom(−j²) = 1。 -/
  unit : ∀ j : Int,
    (laurentRing R).mul (thetaVal j) (hom.toRing (-(thetaValExp j)))
      = (laurentRing R).one

/-- **M232F-4b: witness 本体** — hom は uMonomialRingHom、thetaVal は
    thetaValMonomial として全フィールドを M232F-1〜2 と M223F で埋める。 -/
def thetaRingObjectData (R : CRing) : ThetaRingObjectData R where
  hom := uMonomialRingHom R
  thetaVal := thetaValMonomial R
  via_hom := fun _ => rfl
  base := thetaValMonomial_zero R
  val_rec := thetaValMonomial_rec R
  pm := thetaValMonomial_pm R
  mul := thetaValMonomial_mul R
  unit := thetaValMonomial_unit R

/-- **定理 (M232F-4c): テータ値環写像対象データの存在（M232F 見出し）** —
    任意の係数環 R に対し、テータ値 q^{j²} をそれらが住む環写像対象
    （指数モノイド準同型 (ℤ,+)→(laurentRing R,×,1)）経由で束ねたデータが
    存在する。M223F の個別テータ値が、乗法的合成則 q^{j²}·q^{j'²}=q^{j²+j'²}
    と単元性 q^{j²}·q^{−j²}=1 を伴う環写像対象として対象化される。 -/
theorem thetaRingObject_exists (R : CRing) :
    Nonempty (ThetaRingObjectData R) :=
  ⟨thetaRingObjectData R⟩

end IUT
