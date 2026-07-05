/-
  # M231F: 柱C 形式群の点集合 F(pℤ_p) の群法則総括 capstone（柱C・並行部品）

  Lubin–Tate 形式群 F = lt2Sol p hp の点集合 F(pℤ_p) が備える群法則——
  **単位（M81-2）・可換（M81-3）・逆元（M81-4）・ℤ_p-作用の加法性
  （M81-5）・結合（M85-5）**——を一つの証明記録に束ねる。本モジュールは
  新規の数学的主張を持たない（**新規証明ゼロ**）。全フィールドは既存
  定理 `lt_point_unit` / `lt_point_comm` / `lt_point_inverse` /
  `lt_point_module_add` / `lt_point_assoc` をそのまま代入するだけで
  埋まる。

  これは M224F（Lubin–Tate コア capstone）が正直な限定 (2) で
  「点群 `FormalGroupPoints*.lean` はここでは束ねない」と明記した箇所を、
  点群側の合流点として別レコードに束ねて閉じるものである
  （M224F とはスコープが重複しない）。

  * M231F-1 `pointUnit` — 単位法則の点版 F(x, 0) = x（M81-2）
  * M231F-2 `pointComm` — 可換性の点版 F(x, y) = F(y, x)（M81-3）
  * M231F-3 `pointInverse` — 逆元の点版 F(x, ι(x)) = 0（M81-4）
  * M231F-4 `pointModuleAdd` — [a]-加群則の点版
    F([a](x), [b](x)) = [a+b](x)（M81-5）
  * M231F-5 `pointAssoc` — 結合則の点版 F(F(x,y), z) = F(x, F(y,z))
    （M85-5）
  * M231F-6 `formalGroupPointLawsData` / `formalGroupPointLaws_exists` —
    witness 本体と存在定理

  **意義**: F(pℤ_p) が単位・可換・逆元・結合・ℤ_p-作用を備えた可換群
  （形式 ℤ_p-加群の点集合）であることを、共通パラメータ
  (p : Nat) (hp : IsPrime p) の下で一つの型 `FormalGroupPointLawsData`
  に固定し、new proof を一切追加せずに 2 モジュール（M81・M85）の
  合流点として閉じる。

  **正直な限定**: (1) 本 capstone は五法則を同一パラメータ (p, hp) の
  下で**並べて**束ねるのみで、これらから「点集合が Group / CommGroup の
  型クラスインスタンスをなす」という束縛（Mathlib 型クラスへの橋渡し）は
  与えない——各法則は個別の等式として証明済みだが、点集合を担う単一の
  台型（subtype）を定義し群公理を型クラスとして充足させる作業は
  範囲外。(2) 逆元・加群則の各フィールドは witness 引数
  （zpEval_closed / zpDivP による明示 witness）を M81/M85 の元の定理と
  同一の形で保持しており、witness の正規化（点集合上での一意表現への
  正規化）は行わない。(3) 各フィールドは既存定理の直接引用であり、
  本モジュールでの新規証明はない。

  全て選択公理不使用（型継承除く）。可能なら [propext, Quot.sound] のみ。
  サブエージェント並行部品。
-/
import IUT.FormalGroupPointsLaw
import IUT.FormalGroupPointsAssoc

namespace IUT

/-! ## M231F-6: 柱C 形式群の点集合の群法則総括データ -/

/-- **形式群の点群法則データ（M231F-6）**: 素数 p・`hp : IsPrime p`
    に対し、Lubin–Tate 形式群 F = lt2Sol p hp の点集合 F(pℤ_p) が備える
    五法則——単位・可換・逆元・ℤ_p-作用の加法性・結合——を一つの証明
    記録に束ねる。「柱C 点群: 単位・可換・逆元・加群則・結合」の単一
    証人。 -/
structure FormalGroupPointLawsData (p : Nat) (hp : IsPrime p) where
  /-- M231F-1（M81-2）: 単位法則の点版——F(x, 0) = x。 -/
  pointUnit : ∀ (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval2 p (lt2Sol p hp) x e ((zpRing p).zero) ((zpRing p).zero)
      hx (zero_point_witness p) = x
  /-- M231F-2（M81-3）: 可換性の点版——F(x, y) = F(y, x)。 -/
  pointComm : ∀ (x ex y ey : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey),
    zpEval2 p (lt2Sol p hp) x ex y ey hx hy
      = zpEval2 p (lt2Sol p hp) y ey x ex hy hx
  /-- M231F-3（M81-4）: 逆元の点版——F(x, ι(x)) = 0。 -/
  pointInverse : ∀ (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval2 p (lt2Sol p hp) x e
      (zpEval p (ltInv p hp) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltInv p hp)) x e hx))
      hx (zpEval_closed p hp.1 (ltInv p hp) rfl x e hx)
    = (zpRing p).zero
  /-- M231F-4（M81-5）: [a]-加群則の点版——
      F([a](x), [b](x)) = [a+b](x)。 -/
  pointModuleAdd : ∀ (a b x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval2 p (lt2Sol p hp)
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval p (ltSol p hp b) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp b)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
      (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
    = zpEval p (ltSol p hp ((zpRing p).add a b)) x e hx
  /-- M231F-5（M85-5）: 結合則の点版——
      F(F(x,y), z) = F(x, F(y,z))。 -/
  pointAssoc : ∀ (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez),
    zpEval2 p (lt2Sol p hp)
      (zpEval2 p (lt2Sol p hp) x ex y ey hx hy)
      (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) x ex y ey hx hy))
      z ez
      (zpEval2_closed' p hp.1 (lt2Sol p hp)
        (lt2Sol_is_formal_group p hp).1 x ex y ey hx hy)
      hz
    = zpEval2 p (lt2Sol p hp) x ex
        (zpEval2 p (lt2Sol p hp) y ey z ez hy hz)
        (zpDivP p hp.1 (zpEval2 p (lt2Sol p hp) y ey z ez hy hz))
        hx
        (zpEval2_closed' p hp.1 (lt2Sol p hp)
          (lt2Sol_is_formal_group p hp).1 y ey z ez hy hz)

/-- **証人（M231F-6）**: 本モジュールが柱C 形式群の点群法則の五段
    （M81-2/3/4/5・M85-5）を実際に一つのデータへ束ねる。全フィールドは
    既存定理の代入のみ（新規証明ゼロ）。 -/
def formalGroupPointLawsData (p : Nat) (hp : IsPrime p) :
    FormalGroupPointLawsData p hp where
  pointUnit := lt_point_unit p hp
  pointComm := lt_point_comm p hp
  pointInverse := lt_point_inverse p hp
  pointModuleAdd := lt_point_module_add p hp
  pointAssoc := lt_point_assoc p hp

/-- **定理 (M231F-6): 形式群の点群法則データの存在** — 柱C
    形式群 F = lt2Sol p hp の点集合 F(pℤ_p) が備える五法則（単位・
    可換・逆元・ℤ_p-作用の加法性・結合）が無矛盾に存在する（完成した
    点群プログラムの単一証明記録としての締めくくり）。 -/
theorem formalGroupPointLaws_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (FormalGroupPointLawsData p hp) :=
  ⟨formalGroupPointLawsData p hp⟩

end IUT
