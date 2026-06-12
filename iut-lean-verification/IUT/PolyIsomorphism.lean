/-
  IUT/PolyIsomorphism.lean — M53F（poly-isomorphism と剛性: Frobenius-like /
  étale-like 二分法の圏論的核）の形式化

  ## 動機

  望月 IUT の基本語彙 **poly-isomorphism**（[IUTchI] §0）は「二対象間の
  同型**全体の集合**を一つの射として扱う」装置である。その存在理由は
  [FrdI] 以来の二分法にある:

  * **Frobenius-like 構造**（因子・次数の簿記、Frobenioid 側）は**剛的**——
    対象間の同型は高々一つしかなく、poly-isomorphism は単集合に潰れる。
    リンクの両側で「どの同型で貼ったか」に曖昧さが生じない。
  * **étale-like 構造**（Galois 群・基本群側）は**剛的でない**——
    一つの対象の自己同型が群 G をなし、poly-isomorphism は G-トーソル
    （G の単一軌道）になる。どの同型で貼ったかを忘れることが
    (Ind1)（procession の自己同型による不定性、[IUTchIII] 定理3.11 (i)）
    の発生源であり、M5（IUT/Multiradial.lean）の `MultiradialRep.Ind` が
    抽象化した「不定性の選択肢の型」の正体である。

  本モジュールはこの二分法を、既存の実物（M48F の `elementaryFrobenioid`、
  M51F の `divisorFrobenioid`、M9 の `Grp`）の上で機械検証する。

  ## 検証する定理（全て sorry なし・選択公理なし）

  * M53F-1 `IsGaunt` / `IsoUnique` / `isoUnique_subsingleton` —
    剛性述語の定義: gaunt（同型 ⟹ 対象の等号）と同型の一意性
    （hom 成分の一意性。逆成分の一意性は M22-1a `CatIso.ext` が既に
    供給するので、hom の一意性から CatIso 全体の等号が従う）
  * M53F-2 `divisorFrobenioid_gaunt` — 因子 Frobenioid は gaunt
    （M51F-10 `divisor_iso_objects_eq` の述語への梱包）
  * M53F-3 `divisor_iso_d_one` / `divisor_iso_c_zero` /
    `divisor_iso_is_id` / `divisorFrobenioid_iso_unique` /
    `divisorFrobenioid_rigid` — 因子 Frobenioid の任意の同型は
    成分 (d, c) = (1, 0)、すなわち恒等射と同成分。したがって同型は
    一意であり、**poly-isomorphism は常に単集合 = Frobenius-like 剛性**
  * M53F-4 `elementaryFrobenioid_gaunt` / `elementary_iso_unique` /
    `elementaryFrobenioid_rigid` — 次数レベル（M48F）でも同様
    （`iso_deg_one`・`iso_c_zero` の再利用）
  * M53F-5 `deloopCat` — 群 G の一点圏 BG（対象 = 一点、射 = G、
    合成 = 積、恒等 = 単位元）の圏公理の完全証明。Galois 圏の
    「自己同型の巣」としての骨格モデル
  * M53F-6 `deloopHomIso` / `deloop_every_hom_iso` — BG では
    **全ての射が同型**（逆 = G.inv。左公理系から導出済みの
    `Grp.mul_inv` を右逆に使う）。Frobenioid 側（次数 ≥ 2 の射は
    決して可逆にならない、M48F-4）との第一の対比
  * M53F-7 `autToCarrier` / `carrierToAut` / `deloop_aut_torsor` —
    BG の同型全体（= poly-isomorphism）と G.carrier の明示的全単射
    （往復写像が両向きとも恒等）。**poly-isomorphism が G-トーソル
    全体になる = (Ind1) 型不定性の在処**の機械検証
  * M53F-8 `deloop_gaunt` / `deloop_not_iso_unique` / `gaunt_dichotomy` —
    二分法の総括。注意: BG は対象が一点なので gaunt は**自明に成立**
    する（gaunt は剛性を捉え損なう）。剛性を分離するのは `IsoUnique`
    であり、G が非自明なら BG は IsoUnique を**満たさない**。
    `gaunt_dichotomy`: 任意の非自明群 G に対し
    「divisorFrobenioid は IsoUnique ∧ BG は ¬IsoUnique」。
    `deloop_intGrp_not_iso_unique` は具体的証人（テータ被覆のデッキ群
    ℤ、M9 の `intGrp`）での発動
  * M53F-9 `deloopInd` / `deloopInd0` / `deloopInd_nontrivial` —
    M5 (Ind1) との接続: BG の自己同型型は `MultiradialRep` の
    `Ind`/`ind0` フィールド（不定性の選択肢の型と基点）が要求する
    形のデータ（型 + 基点 = 恒等同型）を供給し、G が非自明なら
    基点以外の選択肢が実在する（= 不定性が真に非自明）

  ## 正直な申告（モデルと本物の差）

  * **BG は Galois 圏そのものではない**: 本物の étale-like 側は
    連結被覆の圏（M20–M22 の Galois 圏）であり、BG はその「一つの
    ガロア対象の自己同型の巣」だけを切り出した一点 base の骨格である。
    G への位相（副有限性、M13）も本モジュールでは見ていない。
    ただし「自己同型群 = G が同型の一意性を破る」という (Ind1) の
    発生機構は BG で過不足なく現れる（M22-1b `autGrp` がガロア対象の
    自己同型を群化する経路と整合）。
  * **poly-isomorphism の「集合として扱う」演算**（合成・full poly-iso
    の関手性）は未形式化。ここで検証したのはその基数の二分法
    （単集合 vs G-トーソル）であり、これが (Ind1)(Ind2) が étale-like
    部分にのみ宿ることの圏論的核である。
  * **(Ind1) との接続は型レベル**: M53F-9 は `MultiradialRep.Ind` が
    要求する「点付き型」を BG の poly-isomorphism が供給できる形に
    なっていることまでを形式化した。実際の定理3.11 の構成で Ind が
    本当に procession の自己同型群から来ること（解析的内容）は
    M5 のインターフェース宣言に留まる（dashboard の M5 行参照）。
  * 選択公理・追加公理は不使用（全定理 propext/Quot.sound 以下）。
-/
import IUT.FrobenioidCat
import IUT.FrobenioidModel
import IUT.SGA1Completion

namespace IUT

universe u v

/-! ## M53F-1: 剛性述語 — gaunt と同型の一意性

    poly-isomorphism「X から Y への同型全体」の基数を測る二つの述語。
    `IsGaunt` は同型の**存在**が対象を同一視させること、`IsoUnique` は
    同型が存在しても**高々一つ**であること（poly-isomorphism が常に
    単集合に潰れる = 剛性）。逆成分の一意性は M22-1a `CatIso.ext`
    （逆は hom で決まる）が既に供給しているため、hom 成分の一意性だけで
    CatIso 全体の等号が従う（`isoUnique_subsingleton`）。 -/

/-- **gaunt 圏**: 任意の同型が対象の等号を強制する
    （同型で結ばれた対象は文字通り同一）。 -/
def IsGaunt (C : Cat.{u, v}) : Prop :=
  ∀ (X Y : C.Obj), CatIso C X Y → X = Y

/-- **同型の一意性**: 任意の二対象間の同型は hom 成分が一意
    （poly-isomorphism が常に単集合以下に潰れる = 剛性）。 -/
def IsoUnique (C : Cat.{u, v}) : Prop :=
  ∀ (X Y : C.Obj) (i j : CatIso C X Y), i.hom = j.hom

/-- **定理 (M53F-1): 剛性 ⟹ poly-isomorphism は単集合** —
    hom 成分の一意性から CatIso 全体の等号が従う（逆成分の一意性は
    M22-1a `CatIso.ext`: inv = inv∘hom∘inv' の標準論法）。 -/
theorem isoUnique_subsingleton {C : Cat.{u, 0}} (h : IsoUnique C)
    {X Y : C.Obj} (i j : CatIso C X Y) : i = j :=
  CatIso.ext (h X Y i j)

/-! ## M53F-2/3: Frobenioid 側の剛性（因子レベル、M51F の圏） -/

/-- **定理 (M53F-2): divisorFrobenioid は gaunt** —
    因子レベルの Frobenioid の同型は因子を動かせない
    （M51F-10 `divisor_iso_objects_eq` の述語への梱包）。 -/
theorem divisorFrobenioid_gaunt : IsGaunt divisorFrobenioid :=
  fun _ _ i => divisor_iso_objects_eq i

/-- **定理 (M53F-3a): 同型の Frobenius 次数は 1** —
    divisorFrobenioid の任意の同型の hom 成分は d = 1
    （d の積 = 1 ⟹ d = 1。M48F の `frob_mul_eq_one_left` を再利用）。 -/
theorem divisor_iso_d_one {x y : QDiv}
    (i : CatIso divisorFrobenioid x y) : i.hom.d = 1 :=
  frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos
    (congrArg DivHom.d i.hom_inv)

/-- **定理 (M53F-3b): 同型の因子部分は自明** —
    divisorFrobenioid の任意の同型の hom 成分は c = 0
    （有効因子の和 = 0 ⟹ max 上界 = 0 ⟹ 自明因子）。 -/
theorem divisor_iso_c_zero {x y : QDiv}
    (i : CatIso divisorFrobenioid x y) : i.hom.c = qzero := by
  -- 合成 = 恒等の c 成分: φ_{inv.d}(hom.c) + inv.c = 0
  have hc : qadd (qfrob i.inv.d i.hom.c) i.inv.c = qzero :=
    congrArg DivHom.c i.hom_inv
  -- 上界成分: max hom.c.bound inv.c.bound = 0
  have hb : max i.hom.c.bound i.inv.c.bound = 0 :=
    congrArg QDiv.bound hc
  have hb0 : i.hom.c.bound = 0 := nat_max_eq_zero_left hb
  -- 上界 0 の有効因子は自明因子
  exact QDiv.ext
    (funext fun k => i.hom.c.vanish k (by rw [hb0]; exact Nat.zero_le k))
    hb0

/-- **定理 (M53F-3c): 同型は恒等射と同成分** — divisorFrobenioid の
    任意の同型 i : x ≅ y の hom 成分は (d, c) = (1, 0)、すなわち
    恒等射 (1, 0) と同じデータ。Frobenius-like の簿記には
    「貼り方の選択肢」が存在しない。 -/
theorem divisor_iso_is_id {x y : QDiv}
    (i : CatIso divisorFrobenioid x y) :
    i.hom.d = 1 ∧ i.hom.c = qzero :=
  ⟨divisor_iso_d_one i, divisor_iso_c_zero i⟩

/-- **定理 (M53F-3d): 因子 Frobenioid の剛性** —
    divisorFrobenioid は IsoUnique を満たす:
    **poly-isomorphism は常に単集合以下**（両成分が (1, 0) に固定）。 -/
theorem divisorFrobenioid_iso_unique : IsoUnique divisorFrobenioid :=
  fun _ _ i j =>
    DivHom.ext ((divisor_iso_d_one i).trans (divisor_iso_d_one j).symm)
      ((divisor_iso_c_zero i).trans (divisor_iso_c_zero j).symm)

/-- **系 (M53F-3e): CatIso 全体としての一意性** —
    divisorFrobenioid の同型は（hom だけでなく逆込みのデータとして）
    一意。 -/
theorem divisorFrobenioid_rigid {x y : QDiv}
    (i j : CatIso divisorFrobenioid x y) : i = j :=
  isoUnique_subsingleton divisorFrobenioid_iso_unique i j

/-! ## M53F-4: Frobenioid 側の剛性（次数レベル、M48F の圏） -/

/-- **定理 (M53F-4a): elementaryFrobenioid は gaunt** —
    次数レベルでも同型は対象を動かせない（M48F-4d の述語への梱包）。 -/
theorem elementaryFrobenioid_gaunt : IsGaunt elementaryFrobenioid :=
  fun _ _ i => iso_objects_eq i

/-- **定理 (M53F-4b): 次数 Frobenioid の剛性** —
    elementaryFrobenioid は IsoUnique を満たす（同型の成分は
    M48F-4b/4c により (d, c) = (1, 0) に固定）。 -/
theorem elementary_iso_unique : IsoUnique elementaryFrobenioid :=
  fun _ _ i j =>
    FrobHom.ext ((iso_deg_one i).trans (iso_deg_one j).symm)
      ((iso_c_zero i).trans (iso_c_zero j).symm)

/-- **系 (M53F-4c): CatIso 全体としての一意性**（次数レベル）。 -/
theorem elementaryFrobenioid_rigid {n m : Int}
    (i j : CatIso elementaryFrobenioid n m) : i = j :=
  isoUnique_subsingleton elementary_iso_unique i j

/-! ## M53F-5/6: étale 側のモデル — 群の一点圏 BG

    Galois/étale-like 側の骨格: 一つの対象とその自己同型群 G。
    M22-1b `autGrp`（ガロア対象の自己同型の群化）の逆向きの構成で、
    「群 G を自己同型の巣として実現する最小の圏」である。 -/

/-- **定理 (M53F-5): 群の一点圏 BG** — 対象 = 一点、射 = G の元、
    合成 = 群の積（図式順）、恒等 = 単位元。圏公理は群公理そのもの
    （右単位則 `Grp.mul_one` は左公理系からの導出定理、M9）。 -/
def deloopCat (G : Grp) : Cat where
  Obj := Unit
  Hom := fun _ _ => G.carrier
  id := fun _ => G.one
  comp := fun f g => G.mul f g
  id_comp := fun f => G.one_mul f
  comp_id := fun f => G.mul_one f
  assoc := fun f g h => G.mul_assoc f g h

/-- **定理 (M53F-6a): BG の射は全て同型** — 任意の射 g に対し
    逆射 = G.inv g（右逆 `Grp.mul_inv` は左公理系からの導出定理、
    左逆 `Grp.inv_mul` は公理）。 -/
def deloopHomIso (G : Grp) {X Y : (deloopCat G).Obj}
    (f : (deloopCat G).Hom X Y) : CatIso (deloopCat G) X Y where
  hom := f
  inv := G.inv f
  hom_inv := G.mul_inv f
  inv_hom := G.inv_mul f

/-- **定理 (M53F-6b): 全射性の命題形** — BG の任意の射は
    ある同型の hom 成分である。Frobenioid 側（M48F-4a: 次数 ≥ 2 の
    射はどんな射とも合成して恒等にならない）との第一の対比。 -/
theorem deloop_every_hom_iso (G : Grp) (X Y : (deloopCat G).Obj)
    (f : (deloopCat G).Hom X Y) :
    ∃ i : CatIso (deloopCat G) X Y, i.hom = f :=
  ⟨deloopHomIso G f, rfl⟩

/-! ## M53F-7: BG の poly-isomorphism は G-トーソル -/

/-- 同型から群の元への読み出し（hom 成分）。 -/
def autToCarrier (G : Grp) {X Y : (deloopCat G).Obj}
    (i : CatIso (deloopCat G) X Y) : G.carrier :=
  i.hom

/-- 群の元から同型への持ち上げ（逆 = G.inv）。 -/
def carrierToAut (G : Grp) (X Y : (deloopCat G).Obj)
    (g : G.carrier) : CatIso (deloopCat G) X Y :=
  deloopHomIso G g

/-- 往復 (carrier → iso → carrier) は恒等。 -/
theorem carrier_aut_carrier (G : Grp) (X Y : (deloopCat G).Obj)
    (g : G.carrier) : autToCarrier G (carrierToAut G X Y g) = g :=
  rfl

/-- 往復 (iso → carrier → iso) は恒等（逆成分の一意性
    M22-1a `CatIso.ext` を使用: 同じ hom を持つ逆は等しい）。 -/
theorem aut_carrier_aut (G : Grp) {X Y : (deloopCat G).Obj}
    (i : CatIso (deloopCat G) X Y) :
    carrierToAut G X Y (autToCarrier G i) = i :=
  CatIso.ext rfl

/-- **定理 (M53F-7): BG の poly-isomorphism は G 全体** —
    任意の二対象間の同型全体（= poly-isomorphism）は G.carrier と
    明示的全単射（往復写像が両向きとも恒等）。étale-like 側では
    「どの同型で貼るか」の選択肢が群 G の元の個数だけあり、これが
    (Ind1) 型不定性（[IUTchIII] 定理3.11 (i)、M5 の `Ind`）の在処
    である。 -/
theorem deloop_aut_torsor (G : Grp) (X Y : (deloopCat G).Obj) :
    (∀ i : CatIso (deloopCat G) X Y,
        carrierToAut G X Y (autToCarrier G i) = i)
      ∧ (∀ g : G.carrier, autToCarrier G (carrierToAut G X Y g) = g) :=
  ⟨fun i => aut_carrier_aut G i, fun _ => rfl⟩

/-! ## M53F-8: 二分法の総括

    注意（gaunt の罠）: BG は対象が一点なので gaunt は**自明に成立**
    してしまう（`deloop_gaunt`）。剛的/非剛的を分離するのは対象の
    等号でなく**同型の一意性**であり、二分法は IsoUnique で測る:

        Frobenioid 側:  IsoUnique 成立（poly-isomorphism = 単集合）
        étale 側 (BG):  G 非自明なら IsoUnique 不成立
                        （poly-isomorphism = G-トーソル、|G| 個の選択肢） -/

/-- BG は自明に gaunt（対象が一点だから。剛性とは無関係であることに
    注意 — gaunt 性は二分法を見分けられない）。 -/
theorem deloop_gaunt (G : Grp) : IsGaunt (deloopCat G) :=
  fun X Y _ => by cases X; cases Y; rfl

/-- **定理 (M53F-8a): 非自明群の BG は剛的でない** —
    G に単位元以外の元があれば、BG は IsoUnique を満たさない
    （g と 1 がどちらも同型の hom 成分になるから）。 -/
theorem deloop_not_iso_unique (G : Grp) (h : ∃ g, g ≠ G.one) :
    ¬ IsoUnique (deloopCat G) := by
  intro hu
  obtain ⟨g, hg⟩ := h
  exact hg (hu Unit.unit Unit.unit
    (carrierToAut G Unit.unit Unit.unit g)
    (carrierToAut G Unit.unit Unit.unit G.one))

/-- **定理 (M53F-8b): 二分法** — 任意の非自明群 G に対し、
    Frobenius-like 側（divisorFrobenioid）は剛的（IsoUnique 成立 =
    poly-isomorphism は単集合）、étale-like 側（BG）は剛的でない
    （poly-isomorphism は G-トーソル）。(Ind1)(Ind2) 型の不定性が
    étale-like 部分に**のみ**宿り、因子・次数の簿記には宿らないこと
    の圏論的核。 -/
theorem gaunt_dichotomy (G : Grp) (h : ∃ g, g ≠ G.one) :
    IsoUnique divisorFrobenioid ∧ ¬ IsoUnique (deloopCat G) :=
  ⟨divisorFrobenioid_iso_unique, deloop_not_iso_unique G h⟩

/-- **定理 (M53F-8c): 具体的証人** — テータ被覆のデッキ群 ℤ
    （M9 の `intGrp`）の BG は剛的でない（1 ≠ 0 を証人に発動）。 -/
theorem deloop_intGrp_not_iso_unique : ¬ IsoUnique (deloopCat intGrp) :=
  deloop_not_iso_unique intGrp ⟨1, show (1 : Int) ≠ 0 by omega⟩

/-! ## M53F-9: M5 (Ind1) との接続

    M5（IUT/Multiradial.lean）の `MultiradialRep` は不定性を
    「選択肢の型 `Ind` と基点 `ind0 : Ind`」として公理化している。
    BG の poly-isomorphism はまさにこの形のデータを供給する:
    型 = 同型全体（M53F-7 により G-トーソル）、基点 = 恒等同型。
    G が非自明なら基点以外の選択肢が実在し（`deloopInd_nontrivial`）、
    不定性が真に非自明であることまで機械検証できる。
    実際の定理3.11 で Ind が procession の自己同型群から来るという
    解析的内容は M5 のインターフェース宣言に留まる（正直な申告）。 -/

/-- (Ind1) 型不定性の選択肢の型: BG の一点上の poly-isomorphism。
    `MultiradialRep.Ind` フィールドに供給できる形。 -/
def deloopInd (G : Grp) : Type :=
  CatIso (deloopCat G) Unit.unit Unit.unit

/-- 不定性の基点（恒等同型 = 「不定性を選ばない」選択肢）。
    `MultiradialRep.ind0` フィールドに供給できる形。 -/
def deloopInd0 (G : Grp) : deloopInd G :=
  carrierToAut G Unit.unit Unit.unit G.one

/-- **定理 (M53F-9): 不定性の非自明性** — G が非自明なら、
    基点（恒等同型）以外の選択肢が実在する。(Ind1) が「空回りの
    形式」でなく真の選択肢を持つことの BG モデルでの検証。 -/
theorem deloopInd_nontrivial (G : Grp) (h : ∃ g, g ≠ G.one) :
    ∃ i : deloopInd G, i ≠ deloopInd0 G := by
  obtain ⟨g, hg⟩ := h
  refine ⟨carrierToAut G Unit.unit Unit.unit g, fun heq => hg ?_⟩
  exact congrArg CatIso.hom heq

end IUT
