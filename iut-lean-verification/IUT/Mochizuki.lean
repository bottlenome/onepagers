/-
  IUT/Mochizuki.lean

  **定理（Lean 検証済み）**: RC 同一視を仮定しなければ、
  系3.12 は形式骨格から **独立** である。

  望月の読み（Essential Logical Structure of IUT, 2024）では、
  Θ-リンクの両側は「異なるラベルを持つ別個の数学的対象」であり、
  同一視は許されない。このとき RC 評価は公理から外れ、
  |log(Θ)| と |log(q)| を結ぶのは定理3.11 の多輻的アルゴリズム
  だけになる。

  ここで示すのは:
  1. RC 評価なしの骨格において系3.12 が成り立つモデルが存在する
     （= 望月の読みは形式骨格のレベルでは無矛盾。
        Scholze–Stix 型の矛盾は同一視なしでは再現できない）
  2. 系3.12 が成り立たないモデルも存在する
     （= 系3.12 は骨格だけからは導出できない。
        その成立は形式化されていない定理3.11 の多輻性の
        実質的内容に全面的に依存する）

  この 2 つを合わせると、系3.12 は形式骨格から独立な命題である。
-/
import IUT.Skeleton

namespace IUT

/-- 系3.12 が成り立つモデル: l⋇ = 2, |log(q)| = 1, |log(Θ)| = 1。
    −1 ≥ −1 で系3.12 が成立する。

    したがって「骨格 + 系3.12」は無矛盾であり、同一視を拒否する限り
    Scholze–Stix 型の矛盾は導出されない。これは望月側の主張
    「同一視こそが誤解の根源」の形式的内容に相当する。 -/
def modelHolds : Skeleton :=
  { lstar := 2, hl := by omega, logq := 1, hq := by omega, logTheta := 1 }

theorem cor312_consistent : ∃ s : Skeleton, Cor312 s :=
  ⟨modelHolds, show (-1 : Int) ≥ (-1 : Int) by omega⟩

/-- 系3.12 が成り立たないモデル: |log(Θ)| = 2 > 1 = |log(q)|。
    したがって系3.12 は骨格の公理だけからは証明できない。 -/
def modelFails : Skeleton :=
  { lstar := 2, hl := by omega, logq := 1, hq := by omega, logTheta := 2 }

theorem cor312_not_derivable : ∃ s : Skeleton, ¬Cor312 s :=
  ⟨modelFails, show ¬((-2 : Int) ≥ (-1 : Int)) by omega⟩

/-- **独立性定理**: 系3.12 は形式骨格から独立である。
    すなわち骨格は系3.12 を証明も反証もしない。

    数学的含意: 系3.12 の成否は、本形式化の範囲外にある
    定理3.11（多輻的表現アルゴリズム）の実質的内容
    —— すなわち「不定性 (Ind1)–(Ind3) を込めた Θ-パイロットの像が
    本当に q-パイロットの体積以下に収まるか」——
    のみによって決まる。これが論争の真の係争点である。 -/
theorem cor312_independent :
    (∃ s : Skeleton, Cor312 s) ∧ (∃ s : Skeleton, ¬Cor312 s) :=
  ⟨cor312_consistent, cor312_not_derivable⟩

end IUT
