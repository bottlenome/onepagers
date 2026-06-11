/-
  IUT/ScholzeStix.lean

  **定理（Lean 検証済み）**: RC 同一視のもとでは系3.12 は矛盾する。

  これは Scholze–Stix「Why abc is still a conjecture」(2018) の
  中心的論法の形式化である: Θ-リンクの両側のコピーを同一視すると、
  Θ-パイロットの体積は q-パイロットの体積の（j² の平均）倍、
  すなわち真に大きくなる。一方系3.12 は |log(Θ)| ≤ |log(q)| を
  主張するので、|log(q)| > 0 と合わせて矛盾が生じる。

  Scholze–Stix の原論文ではこの結論は「したがって系3.12 の証明は
  このままでは成立しない」と表現される。形式的には:
  「骨格 + RC評価 + 系3.12」という公理系は不整合（inconsistent）。
-/
import IUT.Skeleton

namespace IUT

/-- **Scholze–Stix の退化定理**:
    形式骨格の任意のインスタンスについて、RC 評価と系3.12 を
    同時に仮定すると矛盾が導かれる。

    証明の構造:
    1. 系3.12 より |log(Θ)| ≤ |log(q)|
    2. 両辺に l⋇ ≥ 0 を掛けて l⋇·|log(Θ)| ≤ l⋇·|log(q)|
    3. RC 評価より (Σj²)·|log(q)| ≤ l⋇·|log(Θ)|
    4. 合わせて (Σj²)·|log(q)| ≤ l⋇·|log(q)|
    5. しかし Σj² > l⋇（`sumSq_gt`）かつ |log(q)| > 0 なので
       l⋇·|log(q)| < (Σj²)·|log(q)|。矛盾。 -/
theorem ss_incompatible (s : Skeleton) (hrc : RCEval s) (hcor : Cor312 s) : False := by
  -- 1. 系3.12 を |log(Θ)| ≤ |log(q)| に変形
  have h1 : s.logTheta ≤ s.logq := by
    have := hcor
    unfold Cor312 at this
    omega
  -- 2. l⋇ ≥ 0 を掛ける
  have h2 : (s.lstar : Int) * s.logTheta ≤ (s.lstar : Int) * s.logq :=
    Int.mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg s.lstar)
  -- 3.–4. RC 評価と連結
  have h4 : (sumSq s.lstar : Int) * s.logq ≤ (s.lstar : Int) * s.logq :=
    Int.le_trans hrc h2
  -- 5. Σj² > l⋇ と |log(q)| > 0 から逆向きの真の不等式
  have h5 : (s.lstar : Int) * s.logq < (sumSq s.lstar : Int) * s.logq :=
    Int.mul_lt_mul_of_pos_right (sumSq_gt_int s.lstar s.hl) s.hq
  exact absurd h4 (Int.not_le.mpr h5)

/-- 言い換え: RC 同一視を認める読みのもとでは、系3.12 は
    すべてのインスタンスで **偽** である。 -/
theorem cor312_false_under_rc (s : Skeleton) (hrc : RCEval s) : ¬Cor312 s :=
  fun hcor => ss_incompatible s hrc hcor

end IUT
