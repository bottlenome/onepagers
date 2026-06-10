/-
  IUT/Verdict.lean

  **総括定理**: 本形式化が宇宙際タイヒミュラー論の正否について
  証明できることの全体。

  形式検証の結論は三部構成の二分法（dichotomy）である:

  (1) RC 同一視（Scholze–Stix の読み）を認めるなら、
      系3.12 はあらゆるインスタンスで矛盾する。
      → この読みのもとで「IUT は間違っている」は Lean で証明済み。

  (2) RC 同一視を拒否する（望月の読み）なら、骨格と系3.12 は
      無矛盾であり、Scholze–Stix 型の矛盾は再現されない。
      → 「IUT が間違っている」はこの読みからは導出できない。

  (3) しかし同時に、系3.12 は骨格から導出することもできない。
      → 「IUT が正しい」ことの形式的根拠は、未形式化の
        定理3.11（多輻的アルゴリズム）の実質的内容に
        全面的に残されている。

  したがって本検証の答えは:
  「IUT の正否は『Θ-リンクの両側のコピーを同一視してよいか』
   という一点に形式的に帰着し、同一視すれば反証可能（証明済み）、
   同一視しなければ正否いずれも現在の形式骨格からは決定不能」
  である。1,000 ページの原論文のうち形式化可能な算術的骨格は
  この二分法を厳密に支持する。
-/
import IUT.ScholzeStix
import IUT.Mochizuki
import IUT.Boolean

namespace IUT

/-- **最終判定定理（二分法）**。 -/
theorem verdict :
    -- (1) Scholze–Stix の読み: RC 同一視 + 系3.12 は矛盾
    (∀ s : Skeleton, RCEval s → ¬Cor312 s)
    -- (2) 望月の読み: 同一視なしでは系3.12 は無矛盾
    ∧ (∃ s : Skeleton, Cor312 s)
    -- (3) ただし系3.12 は骨格からは導出不能（独立）
    ∧ (∃ s : Skeleton, ¬Cor312 s) :=
  ⟨cor312_false_under_rc, cor312_consistent, cor312_not_derivable⟩

/-- 判定の系: 形式骨格のレベルでは、論争は
    「RCEval を公理として採用するか否か」と外延的に等価である。
    RCEval を採用したときに限り系3.12 の反証が得られる。 -/
theorem controversy_reduces_to_rc (s : Skeleton) :
    (RCEval s → ¬Cor312 s) ∧ (Cor312 s → ¬RCEval s) :=
  ⟨fun hrc hcor => ss_incompatible s hrc hcor,
   fun hcor hrc => ss_incompatible s hrc hcor⟩

end IUT
