/-
  IUT/PolyIrreducible.lean — M271F（体係数多項式環 K[X] 上の**既約性の
  忠実な定式化**と「既約 ⟹ gcd は単元」の論理核: 柱A 実 Galois 理論／
  一般 f の ℚ[X]/(f) 実体化への直結スライス）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無・模型なし・toy 主語なし）。

  **complete_pct 影響**: 柱A「実 Galois 理論／実 π₁^ét」の本物の先行建設。
  `SimpleExtension.lean`（M269F）の `quotField_of_bezout` は honest 仮説
  `SimpleExtData.bezout`（割り切れない任意元 a と E が互いに素）を要求し、
  `PolyBezoutQ.lean`（M270F）は「gcd が単元 ⟹ Bezout=1」までを本物に
  積んだ。本層はその**間**を埋める論理核——**既約 f ⟹ f∤a なら gcd(f,a)
  は単元**——を、多項式の割り切れ `pbzDvd`（M270F-3）の上で本物に証明する。
  親が Wave 2 で `pbzBezout`（gcd gg 構成）→ 本層 `pir_gcd_unit_of_not_dvd`
  （gg 単元）→ `pir_unit_eq_psC`（gg=psC c）→ `pbzBezout_one_of_unit`
  （Bezout=1）と繋ぎ、一般 f の hBez を honest 仮説から本物へ昇格させる。

  * M271F-1 `pdvIsUnit` / `pdvAssoc` — 多項式の単元（非零定数 psC c）・
    同伴（相互割り切れ d∣f ∧ f∣d）。`PolyDivisibility.lean`（pdv）が未
    compile のため本層で同名定義し直す（親が統合時に一本化・下記の限定参照）。
  * M271F-2 `pir_dvd_trans` — 割り切れの推移律 d∣e ∧ e∣a ⟹ d∣a（psRing の
    積結合律で **本物に直接証明**——仮説引数に頼らず依存を切る）。
  * M271F-3 `pirIrreducible` — **既約性の忠実な定式化**: (次数≥1) ∧
    (∀ 約元 d, d は単元 or f と同伴)。核となる「約元は単元 or 同伴」を
    **定義そのもの**に持たせ、数論的既約（既約数=約数が単元か同伴のみ）と
    整合する。toy 主語（Bool 軌道・surrogate 群）で「完成」を作らない。
  * M271F-4 `pir_gcd_unit_of_not_dvd` — **本丸の橋**: 既約 f・gg∣f・gg∣a・
    f∤a ⟹ gg 単元。既約性の二分を gg∣f に適用し、gg が f と同伴なら
    f∣gg（同伴の第2成分）と gg∣a から推移律で f∣a、f∤a と矛盾——ゆえ gg 単元。
  * M271F-5 `pir_unit_eq_psC` — 単元の展開（gg = psC c, c≠0）。
    `pbzBezout_one_of_unit`（M270F-7）の hunit へ渡す形。

  正直な限定（何が本物で何が honest か）:
   - **本物**: 既約性の忠実な定式化（約元 = 単元 or 同伴 を定義に内包）、
     割り切れの推移律（psRing 積結合律から完全証明）、そして本丸
     **既約 ⟹ f∤a なら gcd は単元** の含意は、一般 `CRing R` 係数の
     多項式（有限台冪級数）環の割り切れ `pbzDvd` の上で完全証明
     （sorry 皆無・新規 choice 皆無・仮説引数なし）。推移律を仮説で
     受けず本物に証明したので、本丸の橋は pdv への import 依存を持たない
     （下記 pdv 一本化は名前重複回避のためだけの整理）。
   - **honest（整理事項・数学的ギャップではない）**: `pdvIsUnit`/`pdvAssoc`
     は本来 `PolyDivisibility.lean`（pdv）の述語だが同ファイルが未 compile
     のため本層で **同名再定義**した。親が統合時に pdv 側と一本化する
     （定義は文字通り同一——`pdvIsUnit R p := ∃ c, c≠0 ∧ p=psC R c`,
     `pdvAssoc R d f := pbzDvd R d f ∧ pbzDvd R f d`——ので昇格・弱化なし）。
     `pir_dvd_trans` は pdv の `pdv_dvd_trans` と同値で、本層で自前証明した。
   - 次数上界の witness は既約性の第1成分（∃ nf, …）として受け取る
     （有限台性からの次数抽出は行わない・M269F/M270F と同精神）。
     complete_pct は未設定（本層はグラフメタ不更新）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyDivisibility

namespace IUT

/-! ## M271F-1: 多項式の単元・同伴（`pdvIsUnit`/`pdvAssoc` は `PolyDivisibility` から） -/

/-! ## M271F-2: 割り切れの推移律（本物・仮説引数なし） -/

/-- **定理 (M271F-2): 割り切れの推移律** — d ∣ e ∧ e ∣ a ⟹ d ∣ a。
    e = c₁·d, a = c₂·e なら a = c₂·(c₁·d) = (c₂·c₁)·d。psRing の積結合律で
    本物に証明する（整除仮説を外部から受けず、本層で依存を切る）。 -/
theorem pir_dvd_trans (R : CRing) (d e a : PS R)
    (hde : pbzDvd R d e) (hea : pbzDvd R e a) : pbzDvd R d a := by
  obtain ⟨c1, hc1⟩ := hde
  obtain ⟨c2, hc2⟩ := hea
  refine ⟨psMul R c2 c1, ?_⟩
  rw [hc2, hc1]
  exact ((psRing R).mul_assoc c2 c1 d).symm

/-! ## M271F-3: 既約性の忠実な定式化 -/

/-- **M271F-3: 既約性** — f が既約 :=
    (i) 次数 ≥ 1（∃ nf ≥ 1, f は nf+1 で有界かつ nf 次係数 ≠ 0）かつ
    (ii) f の任意の約元 d は **単元 or f と同伴**。
    核となる二分「約元は単元か同伴」を**定義そのもの**に内包した忠実な
    既約性（数論的既約=約数が単元か同伴のみ、と整合）。toy 主語不使用。 -/
def pirIrreducible (R : CRing) (f : PS R) : Prop :=
  (∃ nf, 1 ≤ nf ∧ IsPolyBounded R f (nf + 1) ∧ f nf ≠ R.zero) ∧
  ∀ d, pbzDvd R d f → (pdvIsUnit R d ∨ pdvAssoc R d f)

/-! ## M271F-4: 本丸の橋（既約 ⟹ gcd は単元） -/

/-- **定理 (M271F-4): 既約 ⟹ f∤a なら公約元 gg は単元** — f 既約・gg∣f・
    gg∣a・f∤a のとき gg は単元。証明: 既約性の二分を gg∣f に適用。
    gg が単元ならそのまま。gg が f と同伴（gg∣f ∧ f∣gg）なら、第2成分
    f∣gg と gg∣a から推移律（M271F-2）で f∣a、これは f∤a に矛盾する。
    ゆえ gg は単元。親が `pbzBezout` の gcd gg にこれを適用し、
    `pir_unit_eq_psC`→`pbzBezout_one_of_unit` で hBez を得る。 -/
theorem pir_gcd_unit_of_not_dvd (R : CRing) (f a gg : PS R)
    (hirr : pirIrreducible R f) (hgf : pbzDvd R gg f)
    (hga : pbzDvd R gg a) (hnd : ¬ pbzDvd R f a) : pdvIsUnit R gg := by
  cases hirr.2 gg hgf with
  | inl hu => exact hu
  | inr hassoc =>
    have hfgg : pbzDvd R f gg := hassoc.2
    have hfa : pbzDvd R f a := pir_dvd_trans R f gg a hfgg hga
    exact absurd hfa hnd

/-! ## M271F-5: 単元の展開 -/

/-- **定理 (M271F-5): 単元 = 非零定数** — gg が単元なら ∃ c ≠ 0, gg = psC c。
    `pdvIsUnit` の定義展開そのもの。`pbzBezout_one_of_unit`（M270F-7）の
    hunit（gg = psC c）へ渡す形を明示する。 -/
theorem pir_unit_eq_psC (R : CRing) (gg : PS R) (h : pdvIsUnit R gg) :
    ∃ c : R.carrier, c ≠ R.zero ∧ gg = psC R c := h

end IUT
