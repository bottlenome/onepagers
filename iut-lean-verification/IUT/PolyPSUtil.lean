/-
  IUT/PolyPSUtil.lean — Wave 0 / N3（ℚ[x]/(x³−2) 実体建設の PS/多項式
  汎用小補題: 柱A 実 Galois 理論／実数体建設の下ごしらえ）

  ── 分類 **[実／承認済み足場(c)]**（骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無・模型なし）。

  **complete_pct 影響**: 0 前進（足場整備のみ・complete_pct 未設定）。
  本層は `audit/A1-real-numberfield-plan.md` §4 N3 の**名前付き実ターゲット**
  「実三次数体 ℚ(∛2) = ℚ[x]/(x³−2) を本物の商環として構成（G3/G4）」への
  必要足場である。Wave 1（`cbrt_linear_factor_root`・`BezB`/`bez_const`/
  `bez_descend`）と Wave 2（`cbrtTwo_bezout` の組み立て・Poly 梱包）が
  import して使う純代数の汎用補題を、一般 `CRing R` で書けるものは一般に
  提供する。後続計画: 本補題群を土台に N1/N2/N4〜N9 を実装し、
  `cbrtTwoData : SimpleExtData ratField268` を実 ℚ・実 f=x³−2 で充填する。

  * ppu_bounded_mono   — 有界上界の単調性（N ≤ M で伝播）
  * ppu_bound_drop     — 頂点係数 0 での上界一段降下
  * ppu_const_eq_psC   — 1 有界（定数）多項式は psC (h 0) に一致
  * ppu_psC_mul_left   — 定数の左積の係数（既存 `psC_mul_coeff` の再輸出）
  * ppu_poly_ext       — Poly の点ごと等式 → 等式（Subtype.ext 梱包）
  * ppu_psZero_of_coeffs — 上界 + 下位係数 0 ⟹ psZero（r=0 分岐用）

  正直な限定: いずれも一般 `CRing` 上の純代数の小補題であり、実 IUT の
  本丸（Bezout 極大性）そのものではない。本丸 `cbrtTwo_bezout` は後続
  Wave で本補題群を組み合わせて実証する（§4 N7）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.SimpleExtension
import IUT.Freshman

namespace IUT

/-! ## N3-1: 有界上界の単調性 -/

/-- **N3-1: 有界上界の単調性** — p が N で有界（多項式）で N ≤ M なら
    p は M でも有界（上界を緩めても消える）。 -/
theorem ppu_bounded_mono (R : CRing) {p : PS R} {N M : Nat} (h : N ≤ M)
    (hp : IsPolyBounded R p N) : IsPolyBounded R p M := by
  intro i hi
  exact hp i (by omega)

/-! ## N3-2: 頂点係数 0 での上界降下 -/

/-- **N3-2: 上界一段降下** — p が n+1 で有界かつ n 次係数が 0 なら、
    p は n で有界。i > n は元の有界性、i = n は係数 0 の仮定で消える。 -/
theorem ppu_bound_drop (R : CRing) {p : PS R} {n : Nat}
    (hb : IsPolyBounded R p (n + 1)) (hn : p n = R.zero) :
    IsPolyBounded R p n := by
  intro i hi
  cases Nat.lt_or_ge i (n + 1) with
  | inl hlt =>
    rw [show i = n from by omega]
    exact hn
  | inr hge => exact hb i hge

/-! ## N3-3: 定数多項式は psC (h 0) -/

/-- **N3-3: 1 有界（定数）多項式の正規形** — h が 1 で有界（次数 0）なら
    h = psC (h 0)。i = 0 は psC の定数項（if_pos rfl）、i ≥ 1 は有界性で
    h i = 0 と psC の非定数項 0 が一致。 -/
theorem ppu_const_eq_psC (R : CRing) {h : PS R}
    (hb : IsPolyBounded R h 1) : h = psC R (h 0) := by
  funext i
  show h i = (if i = 0 then h 0 else R.zero)
  cases Nat.lt_or_ge i 1 with
  | inl hlt =>
    rw [show i = 0 from by omega, if_pos rfl]
  | inr hge =>
    rw [hb i hge, if_neg (show ¬ i = 0 from by omega)]

/-! ## N3-4: 定数の左積の係数（既存補題の再輸出） -/

/-- **N3-4: 定数の左積の係数** — (psC c · h)_j = c · h_j。既存
    `psC_mul_coeff`（M45-4b）の再輸出（左版）。設計 §2.2 の `bez_const`
    で psC(c⁻¹)·y = psC(c⁻¹·c) の展開に使う。 -/
theorem ppu_psC_mul_left (R : CRing) (c : R.carrier) (h : PS R) :
    ∀ j, psMul R (psC R c) h j = R.mul c (h j) :=
  fun j => psC_mul_coeff R c h j

/-! ## N3-5: Poly の点ごと等式 -/

/-- **N3-5: Poly の外延性** — 台部分型 `Poly R` の 2 元は、係数列が
    点ごとに一致すれば等しい。funext で係数列の等式に上げ、`IsPoly`
    が Prop なので Subtype.ext で proof irrelevance を経て梱包する。 -/
theorem ppu_poly_ext (R : CRing) {p q : Poly R}
    (h : ∀ j, p.val j = q.val j) : p = q := by
  apply Subtype.ext
  funext j
  exact h j

/-! ## N3-6: 上界 + 下位係数 0 ⟹ psZero -/

/-- **N3-6: 全係数消滅 ⟹ 零級数** — p が n で有界（i ≥ n で 0）かつ
    下位（i < n）係数も全て 0 なら p = psZero。設計 §2.2 の r = 0 分岐
    （余り全消滅 ⟹ a = q·f3）で使う。 -/
theorem ppu_psZero_of_coeffs (R : CRing) {p : PS R} {n : Nat}
    (hb : IsPolyBounded R p n) (hlow : ∀ i, i < n → p i = R.zero) :
    p = psZero R := by
  funext i
  show p i = R.zero
  cases Nat.lt_or_ge i n with
  | inl hlt => exact hlow i hlt
  | inr hge => exact hb i hge

end IUT
