/-
  IUT/ThetaValueSubgroup.lean — M237F: テータ値のなす部分群と多ラベル積
  （theta-value unit subgroup / multi-label product・柱E E-1 並行部品）

  柱E 残課題 E-1（#39）の「環写像対象（M232F）を**値の集合の代数構造**へ
  精緻化する」切片。M223F（ThetaValueConstruct.lean）はテータ値 q^{j²} を
  Laurent 環 laurentRing R の単項式（指数 thetaValExp j = j²）として個別に
  実体化し、M232F（ThetaRingObject.lean）はそれらが住む**指数モノイド準同型**
  uMonHom : (ℤ,+) → (laurentRing R, ×, 1)（単位 u^0=1・加法性 u^{a+b}=u^a·u^b・
  単元性 u^c·u^{−c}=1）と、テータ値の乗法合成則 q^{j²}·q^{j'²}=u^{j²+j'²}・
  単元性 q^{j²}·u^{−j²}=1 を確立していた。ただし M232F は準同型を**写像対象**
  として束ねるにとどまり、テータ値（＝ uMonHom の像 u^m）が Laurent 環の
  単元群のなかで**部分群/部分モノイドを構成する**という集合レベルの代数
  構造や、**任意有限個のラベルの積**の合成則は与えていなかった。

  本モジュールは M232F の uMonHom（と M88F の単項式機械）を土台に、

    (A) **テータ値の像述語 IsMonomialValue**: x が指数写像の像
        （∃ m, x = u^m）であることを述語化し、その集合が
        (a1) 単位 1 を含む（m=0）、(a2) 積で閉じる（u^a·u^b=u^{a+b}）、
        (a3) 逆元を持つ（各 u^a に逆 u^{−a} が像の中に在り u^a·u^{−a}=1）
        —— すなわち Laurent 環の**単元群の部分群**をなすことを機械検証し、
        テータ値 q^{j²} がその部分群の元であること（isMonomialValue_thetaVal）
        を与える;
    (B) **単元部分群データ LaurentUnitSubgroup**: 単位・積閉性・逆元閉性を
        束ねる構造とその witness monomialValueSubgroup;
    (C) **l-冪部分群と反射のコセット（新規）**: IsLPowerValue R l x
        （∃ k, x = u^{l·k}）を述語化し、それが部分モノイド（1 を含み積で
        閉じる）をなすこと、および反射 j ↦ l−j がテータ値を **q^l 部分群
        （l-冪値）のコセットの中で動かす**こと
        q^{(l−j)²} = q^{j²}·w（w は l-冪値）—— M223F thetaValMonomial_pm
        の部分群論的言い換え;
    (D) **有限多ラベル積の合成則（新規）**: ラベル列 js に沿ったテータ値の
        有限積 thetaValProd R js が指数和の単項式に一致
        thetaValProd R js = u^{Σ thetaValExp j}（thetaExpSum js）。M232F の
        二テータ値の合成則 q^{j²}·q^{j'²}=u^{j²+j'²} を**任意有限個**へ一般化
        し、積が像述語を満たす（部分群に閉じる）ことと、単項/対の整合
        （[j] は q^{j²}、[j,j'] は二項積）を与える

    を機械検証し、テータ値の部分群構造＋多ラベル積を一つのデータへ束ねる。

  * M237F-1 `IsMonomialValue` / `isMonomialValue_one` / `_mul` / `_inv` /
    `_thetaVal` — 像述語と単位・積・逆元の閉性、テータ値の所属
  * M237F-2 `LaurentUnitSubgroup` / `monomialValueSubgroup` — 単元部分群
    データと witness
  * M237F-3 `IsLPowerValue` / `isLPowerValue_one` / `_mul` /
    `thetaVal_reflection_coset` — l-冪部分モノイドと反射のコセット（新規）
  * M237F-4 `thetaExpSum` / `thetaValProd` / `thetaValProd_eq_uMonHom` /
    `_isMonomialValue` / `_singleton` / `_pair` — 有限多ラベル積の合成則
    （新規）と閉性・整合
  * M237F-5 総括レコード `ThetaValueSubgroupData` / `thetaValueSubgroupData`
    / `thetaValueSubgroup_exists` — capstone

  意義: M232F の**写像対象**（準同型 uMonHom）を、テータ値のなす
  **単元部分群**（集合レベルの代数構造: 1・積・逆元の閉性）と
  **有限多ラベル積の合成則**（二テータ値 → 任意有限個）へ精緻化する。
  反射 j↦l−j を q^l 部分群のコセットとして読み、テータ値の積構造を
  部分群・コセット・有限積の言葉で対象化する E-1 の値代数側 witness。

  正直な限定（スライス A+B+C+D）: 扱うのはテータ値 q^{j²} が住む
  **Laurent 環の単元群の部分群**（指数写像 uMonHom の像がなす部分モノイド
  ＋逆元）と、l-冪値のコセット・有限多ラベル積の指数和合成のみ。ここで
  「部分群」とは (laurentRing R, ×, 1) の単元群の部分集合が単位・積・逆元で
  閉じることの意味であり、テータ値がラベル上でなす**環準同型**や
  **ガロア同変な p 進テータ値**・**tempered π₁ の商としての実現**・
  **エタールテータ関数値そのものの構成**は M223F/M209F/M212F/M232F 同様
  E-1 残として範囲外（本モジュールでは一切主張しない）。反射のコセットは
  M223F thetaValMonomial_pm（指数の合同 (l−j)²≡j² mod l）の値単項式版を
  部分群語で言い直したものであり、q の付値・q-展開の収束は扱わない。
  全て選択公理を証明本体で新規導入せず（M232F/M223F/M88F から継承、
  新規 Classical・新規 Classical.choice なし。商 laurentRing / laurentRel /
  Quot レベルの主張は Quot.sound を使う —— 商構成に内在、選択公理では
  ない）。#print axioms により継承分のみであることを確認済み。
  サブエージェント並行部品。
-/
import IUT.ThetaRingObject

namespace IUT

/-! ## M237F-1: テータ値の像述語 IsMonomialValue と部分群の閉性 -/

/-- **M237F-1a: 像述語 IsMonomialValue** — x が指数写像対象 uMonHom の像
    （∃ m, x = u^m）であること。テータ値 q^{j²} が住む Laurent 環の単元群の
    「単項式値」の集合を切り出す述語。 -/
def IsMonomialValue (R : CRing) (x : (laurentRing R).carrier) : Prop :=
  ∃ m : Int, x = uMonHom R m

/-- **定理 (M237F-1b): 単位の所属** — 乗法単位 1 = u^0 は像述語を満たす
    （M232F uMonHom_zero）。部分群の単位元条件。 -/
theorem isMonomialValue_one (R : CRing) :
    IsMonomialValue R (laurentRing R).one :=
  ⟨0, (uMonHom_zero R).symm⟩

/-- **定理 (M237F-1c): 積での閉性** — 像述語を満たす x=u^a, y=u^b の積
    x·y=u^{a+b} も像述語を満たす（M232F uMonHom_add）。部分群の積閉性。 -/
theorem isMonomialValue_mul (R : CRing) (x y : (laurentRing R).carrier)
    (hx : IsMonomialValue R x) (hy : IsMonomialValue R y) :
    IsMonomialValue R ((laurentRing R).mul x y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [ha, hb, uMonHom_add]

/-- **定理 (M237F-1d): 逆元での閉性** — 像述語を満たす x=u^a には、像述語を
    満たす逆元 y=u^{−a} が在り x·y=1（M232F uMonHom_unit）。テータ値が
    Laurent 環の**単元群の部分群**をなすことの逆元条件。 -/
theorem isMonomialValue_inv (R : CRing) (x : (laurentRing R).carrier)
    (hx : IsMonomialValue R x) :
    ∃ y : (laurentRing R).carrier, IsMonomialValue R y ∧
      (laurentRing R).mul x y = (laurentRing R).one := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨uMonHom R (-a), ⟨-a, rfl⟩, ?_⟩
  rw [ha]
  exact uMonHom_unit R a

/-- **定理 (M237F-1e): テータ値は像述語を満たす** — thetaValMonomial R j
    = q^{j²} = u^{j²}（M232F thetaValMonomial_eq_uMonHom）。テータ値は
    単元部分群の元。 -/
theorem isMonomialValue_thetaVal (R : CRing) (j : Int) :
    IsMonomialValue R (thetaValMonomial R j) :=
  ⟨thetaValExp j, thetaValMonomial_eq_uMonHom R j⟩

/-! ## M237F-2: 単元部分群データ -/

/-- **M237F-2a: Laurent 単元部分群データ** — Laurent 環 laurentRing R の
    単元群の部分群を、所属述語 mem と単位（one_mem）・積閉性（mul_mem）・
    逆元閉性（inv_mem、各元に逆元が部分群内に在り積が 1）で束ねる構造。
    テータ値 q^{j²} がその上に住む単元部分群。 -/
structure LaurentUnitSubgroup (R : CRing) where
  /-- 所属述語: x が部分群の元か。 -/
  mem : (laurentRing R).carrier → Prop
  /-- 単位元条件: 乗法単位 1 は部分群に属す。 -/
  one_mem : mem (laurentRing R).one
  /-- 積閉性: 部分群の二元の積は部分群に属す。 -/
  mul_mem : ∀ x y, mem x → mem y →
    mem ((laurentRing R).mul x y)
  /-- 逆元閉性: 各元 x に逆元 y が部分群内に在り x·y = 1。 -/
  inv_mem : ∀ x, mem x →
    ∃ y, mem y ∧ (laurentRing R).mul x y = (laurentRing R).one

/-- **M237F-2b: witness** — 像述語 IsMonomialValue を所属とする単元部分群。
    テータ値のなす部分群を M237F-1 の閉性で束ねる。 -/
def monomialValueSubgroup (R : CRing) : LaurentUnitSubgroup R where
  mem := IsMonomialValue R
  one_mem := isMonomialValue_one R
  mul_mem := isMonomialValue_mul R
  inv_mem := isMonomialValue_inv R

/-! ## M237F-3: l-冪部分モノイドと反射のコセット -/

/-- **M237F-3a: l-冪値述語 IsLPowerValue** — x が q^l の冪 u^{l·k}
    （∃ k, x = u^{l·k}）であること。反射 j↦l−j がテータ値を動かす
    「q^l 部分群」（l-冪値の集合）を切り出す述語。 -/
def IsLPowerValue (R : CRing) (l : Int) (x : (laurentRing R).carrier) : Prop :=
  ∃ k : Int, x = uMonHom R (l * k)

/-- **定理 (M237F-3b): l-冪部分モノイドの単位** — 1 = u^{l·0} は l-冪値
    （k=0）。 -/
theorem isLPowerValue_one (R : CRing) (l : Int) :
    IsLPowerValue R l (laurentRing R).one := by
  refine ⟨0, ?_⟩
  rw [Int.mul_zero]
  exact (uMonHom_zero R).symm

/-- **定理 (M237F-3c): l-冪部分モノイドの積閉性** — u^{l·a}·u^{l·b}
    = u^{l·(a+b)} も l-冪値（M232F uMonHom_add）。q^l 部分群が積で閉じる。 -/
theorem isLPowerValue_mul (R : CRing) (l : Int) (x y : (laurentRing R).carrier)
    (hx : IsLPowerValue R l x) (hy : IsLPowerValue R l y) :
    IsLPowerValue R l ((laurentRing R).mul x y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  have hexp : l * (a + b) = l * a + l * b := by rw [Int.mul_add]
  rw [ha, hb, hexp, uMonHom_add]

/-- **定理 (M237F-3d): 反射のコセット（新規）** — 反射 j ↦ l−j はテータ値を
    q^l 部分群のコセットの中で動かす: q^{(l−j)²} = q^{j²}·w（w は l-冪値
    u^{l·k}）。M223F thetaValMonomial_pm（値レベル反転 (l−j)²=j²+l·k）を
    l-冪部分群 IsLPowerValue の言葉で言い直したもの。テータ値の反射不変性
    （q^l を法とする不変）の部分群論的表現。 -/
theorem thetaVal_reflection_coset (R : CRing) (l j : Int) :
    ∃ w : (laurentRing R).carrier, IsLPowerValue R l w ∧
      thetaValMonomial R (l - j)
        = (laurentRing R).mul (thetaValMonomial R j) w := by
  obtain ⟨k, hk⟩ := thetaValMonomial_pm R l j
  exact ⟨uMonHom R (l * k), ⟨k, rfl⟩, hk⟩

/-! ## M237F-4: 有限多ラベル積の合成則 -/

/-- **M237F-4a: ラベル列の指数和** — ラベル列 js に沿ったテータ値指数
    thetaValExp j = j² の総和 Σ thetaValExp j。多ラベル積の指数簿記。 -/
def thetaExpSum : List Int → Int
  | [] => 0
  | j :: js => thetaValExp j + thetaExpSum js

/-- **M237F-4b: 有限多ラベル積** — ラベル列 js に沿ったテータ値
    q^{j²} の有限積 ∏ q^{j²}（Laurent 環の乗法での畳み込み、基点 1）。 -/
def thetaValProd (R : CRing) : List Int → (laurentRing R).carrier
  | [] => (laurentRing R).one
  | j :: js => (laurentRing R).mul (thetaValMonomial R j) (thetaValProd R js)

/-- **定理 (M237F-4c): 多ラベル積の指数和合成則（新規・本丸）** —
    有限個のテータ値の積は指数和の単項式に一致:
    ∏_{j∈js} q^{j²} = u^{Σ_{j∈js} j²} = uMonHom R (thetaExpSum js)。
    M232F の二テータ値合成則 q^{j²}·q^{j'²}=u^{j²+j'²} を**任意有限個**の
    ラベルへ一般化した環論的合成則（M232F uMonHom_zero/uMonHom_add で
    リスト帰納）。 -/
theorem thetaValProd_eq_uMonHom (R : CRing) (js : List Int) :
    thetaValProd R js = uMonHom R (thetaExpSum js) := by
  induction js with
  | nil =>
    show (laurentRing R).one = uMonHom R 0
    exact (uMonHom_zero R).symm
  | cons j js ih =>
    show (laurentRing R).mul (thetaValMonomial R j) (thetaValProd R js)
      = uMonHom R (thetaValExp j + thetaExpSum js)
    rw [ih, thetaValMonomial_eq_uMonHom, uMonHom_add]

/-- **定理 (M237F-4d): 多ラベル積は単元部分群に閉じる** — 有限積
    ∏ q^{j²} = u^{Σj²} は像述語 IsMonomialValue を満たす（M237F-4c）。
    テータ値の有限積も単元部分群（M237F-2）の元。 -/
theorem thetaValProd_isMonomialValue (R : CRing) (js : List Int) :
    IsMonomialValue R (thetaValProd R js) :=
  ⟨thetaExpSum js, thetaValProd_eq_uMonHom R js⟩

/-- **定理 (M237F-4e): 単項ラベルの整合** — 一ラベルの積 [j] は個別テータ値
    q^{j²}（M223F thetaValMonomial）に一致（1 との積の吸収）。多ラベル積が
    単一テータ値の一般化であることの整合。 -/
theorem thetaValProd_singleton (R : CRing) (j : Int) :
    thetaValProd R [j] = thetaValMonomial R j := by
  show (laurentRing R).mul (thetaValMonomial R j) (laurentRing R).one
    = thetaValMonomial R j
  rw [(laurentRing R).mul_comm, (laurentRing R).one_mul]

/-- **定理 (M237F-4f): 二ラベルの整合** — 二ラベルの積 [j,j'] は二テータ値の
    二項積 q^{j²}·q^{j'²}（M232F thetaValMonomial_mul の左辺）に一致。多ラベル
    積が M232F の二テータ値合成則の一般化であることの整合。 -/
theorem thetaValProd_pair (R : CRing) (j j' : Int) :
    thetaValProd R [j, j']
      = (laurentRing R).mul (thetaValMonomial R j) (thetaValMonomial R j') := by
  show (laurentRing R).mul (thetaValMonomial R j)
      ((laurentRing R).mul (thetaValMonomial R j') (laurentRing R).one)
    = (laurentRing R).mul (thetaValMonomial R j) (thetaValMonomial R j')
  rw [(laurentRing R).mul_comm (thetaValMonomial R j') (laurentRing R).one,
    (laurentRing R).one_mul]

/-! ## M237F-5: 総括レコード（テータ値部分群 + 多ラベル積） -/

/-- **M237F-5a: テータ値部分群データ** — テータ値 q^{j²} のなす Laurent 環
    単元部分群（所属・単位・積・逆元）、テータ値の所属、反射のコセット
    （q^l 部分群）、有限多ラベル積の閉性・指数和合成を一括束ね。M232F の
    写像対象を値の代数構造（部分群・コセット・有限積）へ精緻化した
    E-1 の値代数側 witness。 -/
structure ThetaValueSubgroupData (R : CRing) where
  /-- テータ値のなす単元部分群。 -/
  subgroup : LaurentUnitSubgroup R
  /-- テータ値写像 j ↦ q^{j²}。 -/
  thetaVal : Int → (laurentRing R).carrier
  /-- テータ値は部分群の元。 -/
  thetaVal_mem : ∀ j : Int, subgroup.mem (thetaVal j)
  /-- 部分群の単位元条件。 -/
  one_mem : subgroup.mem (laurentRing R).one
  /-- 部分群の積閉性。 -/
  mul_mem : ∀ x y, subgroup.mem x → subgroup.mem y →
    subgroup.mem ((laurentRing R).mul x y)
  /-- 部分群の逆元閉性。 -/
  inv_mem : ∀ x, subgroup.mem x →
    ∃ y, subgroup.mem y ∧ (laurentRing R).mul x y = (laurentRing R).one
  /-- 反射のコセット（新規）: q^{(l−j)²} = q^{j²}·w（w は l-冪値）。 -/
  reflection : ∀ l j : Int, ∃ w : (laurentRing R).carrier,
    IsLPowerValue R l w ∧
      thetaVal (l - j) = (laurentRing R).mul (thetaVal j) w
  /-- 多ラベル積の閉性: ∏ q^{j²} は部分群に属す。 -/
  prodClose : ∀ js : List Int, subgroup.mem (thetaValProd R js)
  /-- 多ラベル積の指数和合成（新規）: ∏ q^{j²} = u^{Σj²}。 -/
  prodExp : ∀ js : List Int, thetaValProd R js = uMonHom R (thetaExpSum js)

/-- **M237F-5b: witness 本体** — subgroup は monomialValueSubgroup、thetaVal は
    thetaValMonomial として全フィールドを M237F-1〜4 で埋める。 -/
def thetaValueSubgroupData (R : CRing) : ThetaValueSubgroupData R where
  subgroup := monomialValueSubgroup R
  thetaVal := thetaValMonomial R
  thetaVal_mem := isMonomialValue_thetaVal R
  one_mem := isMonomialValue_one R
  mul_mem := isMonomialValue_mul R
  inv_mem := isMonomialValue_inv R
  reflection := thetaVal_reflection_coset R
  prodClose := thetaValProd_isMonomialValue R
  prodExp := thetaValProd_eq_uMonHom R

/-- **定理 (M237F-5c): テータ値部分群データの存在（M237F 見出し）** —
    任意の係数環 R に対し、テータ値 q^{j²} を Laurent 環単元群の部分群
    （単位・積・逆元の閉性）として束ね、反射を q^l 部分群のコセットとして
    読み、有限多ラベル積 ∏ q^{j²}=u^{Σj²} の合成則を伴うデータが存在する。
    M232F の写像対象が値の**代数構造**（部分群・コセット・有限積）へ
    精緻化される。 -/
theorem thetaValueSubgroup_exists (R : CRing) :
    Nonempty (ThetaValueSubgroupData R) :=
  ⟨thetaValueSubgroupData R⟩

end IUT
