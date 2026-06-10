/-
  IUT/Skeleton.lean

  IUT III 系3.12 をめぐる論争の「形式骨格」。

  ここで形式化するのは、望月・Scholze–Stix の両陣営が
  **合意している** 数値データのみである:

  * l ≥ 5 は素数、l⋇ = (l−1)/2 ≥ 2
  * |log(q)| > 0 : q-パイロット対象の procession 正規化対数体積
    （IUT III 系3.12 の仮定。楕円曲線 E_F の q-パラメータから計算される）
  * |log(Θ)| : 多輻的表現（IUT III 定理3.11）の中で、不定性
    (Ind1), (Ind2), (Ind3) を込めて測った Θ-パイロット対象の
    「可能な像の合併の正則包」の対数体積

  系3.12 の主張は −|log(Θ)| ≥ −|log(q)| である
  （teichmuller/pdf/IUT_III_Canonical_Splittings.pdf p.174）。

  論争の核心は「Θ-リンクの両側のコピーを同一視してよいか」であり、
  本形式化ではそれを `RCEval`（redundant-copies 評価）という
  追加公理として分離する。これにより両陣営の読みを同一の骨格上で
  比較できる。
-/
import IUT.Arithmetic

namespace IUT

/-- **形式骨格**: 系3.12 に現れる数値データ。
    両陣営が認める構成要素のみからなる。

    対数体積は `Int`（適当な共通分母で正規化した値）で表す。
    実数を避けるのは mathlib 非依存を保つためであり、
    以下の議論はすべて順序環の不等式論法なので一般性を失わない。 -/
structure Skeleton where
  /-- l⋇ = (l−1)/2。テータ値 q^{1²}, …, q^{l⋇²} のラベル数。 -/
  lstar : Nat
  /-- l ≥ 5（IUT の仮定）より l⋇ ≥ 2。 -/
  hl : lstar ≥ 2
  /-- |log(q)|: q-パイロットの対数体積。 -/
  logq : Int
  /-- 系3.12 の仮定: |log(q)| > 0。 -/
  hq : logq > 0
  /-- |log(Θ)|: 多輻的表現の中で不定性込みで測った
      Θ-パイロットの可能な像の対数体積。 -/
  logTheta : Int

/-- **系3.12 の主張** (IUT III, p.174):
    −|log(Θ)| ≥ −|log(q)|（同値変形すれば |log(Θ)| ≤ |log(q)|）。 -/
def Cor312 (s : Skeleton) : Prop := -s.logTheta ≥ -s.logq

/-- **RC 評価**（Scholze–Stix の同一視のもとで成立する評価式）:

    Θ-リンクの両側の環構造・ラベルを同一視（"redundant copies"）すると、
    Θ-パイロットは文字通り { q^{j²} } _{j=1,…,l⋇} となり、その
    procession 正規化対数体積は j² の平均 × |log(q)| 以上になる:

        l⋇ · |log(Θ)| ≥ (Σ_{j=1}^{l⋇} j²) · |log(q)|

    これは Scholze–Stix [Why abc is still a conjecture, 2018] の
    「同一視すれば Θ-リンクは q ↦ q^{j²} のリスケーリングに過ぎず、
    体積は j² 倍で増える」という指摘の形式化である。

    望月側はこの同一視自体を拒否する（Essential Logical Structure of
    IUT, 2024, "redundant copies" 節）。したがってこれは骨格の
    公理ではなく **追加仮定** として分離してある。 -/
def RCEval (s : Skeleton) : Prop :=
  (s.lstar : Int) * s.logTheta ≥ (sumSq s.lstar : Int) * s.logq

end IUT
