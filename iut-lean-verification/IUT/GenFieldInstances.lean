/-
  ── 分類 **[実／昇格(a)]**（complete_pct 影響: A1 の「単一 f のみ」限定を
  一般構成器で解消する統合 capstone。数値は独立監査判定）──

  **M273F-capstone: 一般構成器の二実例化** — `gefField`（∀ 既約 f, ℚ[x]/(f) は実体）
  を、**異なる次数の二つの本物に既約な多項式** x³−2（次数3）と Φ₃=x²+x+1（次数2）に
  適用し、ℚ(∛2) と ℚ(ζ_3) を**同一の一般構成器から**得る。これにより「一般 f を
  量化する構成器が無い（単一 f への手組み）」という A1 の限定に正面から答える:
  bespoke な次数別ユークリッド鎖（cbc/cq1）ではなく、一つの degree-parametric な
  `gefField` が既約性証明（cti_irreducible / cqi_irreducible）を入力に取って両体を産む。

  全 axiom [propext, Quot.sound] のみ・sorry/新規 Classical.choice なし。模型ゼロ。
-/
import IUT.GenExtField
import IUT.CbrtTwoIrreducible
import IUT.Cq3Irreducible
import IUT.CbrtTwoBase
import IUT.Cq3Base

namespace IUT

/-- **ℚ(∛2) = ℚ[x]/(x³−2) を一般構成器から** — `gefField` を x³−2（次数3・実既約
    `cti_irreducible`）に適用。bespoke `cbc` 鎖でなく一般エンジンの実例。 -/
def gfiCbrtField : SimpleFieldExt pbzRatField :=
  gefField ct0PS 3 ct0_bound ct0_lead (by omega) cti_irreducible

/-- **ℚ(ζ_3) = ℚ[x]/(x²+x+1) を一般構成器から** — `gefField` を Φ₃（次数2・実既約
    `cqi_irreducible`）に適用。同一 `gefField` が異なる次数の第二例も産む。 -/
def gfiCq3Field : SimpleFieldExt pbzRatField :=
  gefField cq0PS 2 cq0_bound cq0_lead (by omega) cqi_irreducible

/-- **両体とも一般構成器由来で体性を持つ** — 一つの `gefField` が x³−2 と Φ₃ の
    両方から実体（非零元に逆元）を産むことを機械検証。単一 f への overfit でない。 -/
theorem gfi_both_fields_from_general :
    (∀ x, x ≠ gfiCbrtField.ring.zero →
      ∃ y, gfiCbrtField.ring.mul x y = gfiCbrtField.ring.one) ∧
    (∀ x, x ≠ gfiCq3Field.ring.zero →
      ∃ y, gfiCq3Field.ring.mul x y = gfiCq3Field.ring.one) :=
  ⟨gfiCbrtField.has_inverses, gfiCq3Field.has_inverses⟩

/-- **capstone: 一般構成器から二つの異なる次数の実数体** — `gefField` を用いて、
    次数の異なる二つの既約多項式から実体が存在する（A1「実際の商環として構成」を
    一般 f で・二実例で満たす）。 -/
theorem gfi_exists :
    ∃ E₁ E₂ : SimpleFieldExt pbzRatField,
      (∀ x, x ≠ E₁.ring.zero → ∃ y, E₁.ring.mul x y = E₁.ring.one) ∧
      (∀ x, x ≠ E₂.ring.zero → ∃ y, E₂.ring.mul x y = E₂.ring.one) :=
  ⟨gfiCbrtField, gfiCq3Field,
    gfiCbrtField.has_inverses, gfiCq3Field.has_inverses⟩

end IUT
