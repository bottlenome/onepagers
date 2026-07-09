/-
  IUT/CbrtTwoBase.lean — CT0（A1 実数体 ℚ(∛2) = ℚ[x]/(x³−2) の
  基礎データ層・Wave 0 / N1）

  ── 分類 **[実／承認済み足場(c)]**（本物の先行建設への足場。骨格でなく
  実 ℚ・実 f = x³−2 の本物のデータ・sorry 皆無・新規 Classical.choice 皆無・
  模型ゼロ）。名前付き実ターゲット: A1「実数体 K = ℚ[x]/(f) を実際の商環
  として構成」の最初の本物のインスタンス **実三次数体 ℚ(∛2)**（設計書
  `audit/A1-real-numberfield-plan.md` §1 の G0–G1）。本層はその
  `SimpleExtData` の bezout 以外の全 field（modulus/deg/bound/lead/deg_pos/
  base_nontrivial）に渡せるデータを本物で確定する。後続:
   - Wave 1（N4–N6）: `cbrt_linear_factor_root`・`BezB`/`bez_const`/
     `bez_descend`・頂点係数論法（本層のデータを import）。
   - Wave 2（N7）: `cbrtTwo_bezout`（f のイデアル極大性 = 本丸）。
   - Wave 3（N8–N9）: `SimpleExtData.build` 充填で ℚ(∛2) を体化、α = ∛2。
  本層で bezout・build は作らない（Wave 2/3 の主語）。

  **complete_pct 影響**: 本層単体では **complete_pct 未設定（0 前進）**。
  A1 の complete_pct はイデアル極大性（Wave 2）と体化（Wave 3）が本物で
  揃った時に動かす。本層はその「本コース」への足場であり、水増しの束ねでは
  なく、以後の全 Wave が import する A1 基盤データを実 ℚ・実 f で確定する。

  内容（設計 §1 N1）:
   * `ct0Field` — 実 ℚ の `Field268`（既存 `pbzRatField`（M270F-8a）の再利用。
     ring = ratIUTField.toCRing ≡ ratRing）。
   * `ct0Two` — 有理数 2、`ct0PS` — x³ − 2 の係数列（既存 `cbpF3val`（CBP-2a）を
     そのまま再利用。psAdd (X³) (psC (−2)) 形）。
   * `ct0PS_coeff0..3` — 係数確定（既存 `cbpF3_coeff*`（CBP-3）を再輸出）。
   * `ct0_bound` — deg ≤ 3（既存 `cbpF3val_bound`（CBP-4a）を再輸出）。
   * `ct0_lead` — 先頭係数 ≠ 0（既存 `cbpF3_lead_ne_zero`（CBP-4b）を再輸出）。
   * `ct0Modulus` — `simpleExtModulus ct0Field ct0PS 3 ct0_bound`（Poly ratRing。
     後続 Wave の hBez・build の主語となる法多項式 f = x³ − 2）。
   * `ct0_base_nontrivial` — 基礎体 ℚ の非自明性 1 ≠ 0。

  正直な限定（本層に含めないもの・§4 規約により消さない）:
   - **bezout（f のイデアル極大性）は本層に無い**（Wave 2 = N7 の主語）。
     従って本層だけでは ℚ(∛2) は体化されない。
   - **単一 f = x³−2 のみ**。一般既約 f への Bezout は未達（A1 満点は一般 f・
     複数実例を要する。設計 §5 の名前付き後続）。
   - 逆元は後続でも ∃ 形（全域 inv 付き IUTField 昇格は別スライス）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.CubicPolyQ
import IUT.PolyBezoutQ

namespace IUT

/-! ## CT0-1: 実 ℚ の Field268 -/

/-- **CT0-1: 基礎体 K = 実 ℚ**（`Field268`）。既存 `pbzRatField`（M270F-8a）の
    再利用: `ring = ratIUTField.toCRing`（≡ `ratRing`）、`invf = ratIUTField.inv`
    （≡ `qInv`）、`mul_inv_cancel = ratIUTField.mul_inv_cancel`。本物の体 ℚ を
    そのまま A1 の基礎体に据える（模型なし）。 -/
def ct0Field : Field268 := pbzRatField

/-! ## CT0-2: 法多項式 f = x³ − 2 の係数列 -/

/-- **CT0-2a: 有理数 2**（= 2/1、実 ℚ の元）。x³ − 2 の定数項 −2 の素。 -/
def ct0Two : QRat := ratOfInt.map (2 : Int)

/-- **CT0-2b: f = x³ − 2 の係数列** — 既存 `cbpF3val`（CBP-2a、= X³ と定数
    埋め込み −2 の `psAdd`）をそのまま再利用。実 ℚ[X] の実元。 -/
def ct0PS : PS ratRing := cbpF3val

/-! ## CT0-3: 係数確定（既存 CBP-3 の再輸出） -/

/-- **CT0-3a: 定数項 = −2**（`cbpNegTwo = ratOfInt.map (-2)`）。 -/
theorem ct0PS_coeff0 : ct0PS 0 = cbpNegTwo := cbpF3_coeff0

/-- **CT0-3b: 一次係数 = 0**。 -/
theorem ct0PS_coeff1 : ct0PS 1 = ratRing.zero := cbpF3_coeff1

/-- **CT0-3c: 二次係数 = 0**。 -/
theorem ct0PS_coeff2 : ct0PS 2 = ratRing.zero := cbpF3_coeff2

/-- **CT0-3d: 三次係数 = 1**（最高次係数）。 -/
theorem ct0PS_coeff3 : ct0PS 3 = ratRing.one := cbpF3_coeff3

/-! ## CT0-4: 有界性・先頭係数（SimpleExtData の bound / lead） -/

/-- **CT0-4a: f の有界性（deg ≤ 3）** — i ≥ 4 で X³ 項も定数項も台の外で 0。
    既存 `cbpF3val_bound`（CBP-4a）を再輸出。`SimpleExtData.bound`。 -/
theorem ct0_bound : IsPolyBounded ratRing ct0PS 4 := cbpF3val_bound

/-- **CT0-4b: 先頭係数 ≠ 0** — ct0PS 3 = 1 ≠ 0。既存 `cbpF3_lead_ne_zero`
    （CBP-4b、`cbp_one_ne_zero` 経由）を再輸出。`SimpleExtData.lead`。 -/
theorem ct0_lead : ct0PS 3 ≠ ratRing.zero := cbpF3_lead_ne_zero

/-! ## CT0-5: 法多項式 f（Poly ratRing の元） -/

/-- **CT0-5: 法多項式 f = x³ − 2**（`Poly ratRing` の元）— `simpleExtModulus`
    で ct0PS（deg 3・bound 4）を多項式に梱包。後続 Wave の Bezout（イデアル
    極大性）・`SimpleExtData.build`（体化）の**主語**となる法多項式。
    `deg = 3`（`deg_pos : 1 ≤ 3` は後続で `by omega`）。 -/
def ct0Modulus : Poly ratRing := simpleExtModulus ct0Field ct0PS 3 ct0_bound

/-! ## CT0-6: 基礎体の非自明性（SimpleExtData の base_nontrivial） -/

/-- **CT0-6: 基礎体 ℚ は非自明**（1 ≠ 0）— `ratIUTField.one_ne_zero`（M264F）。
    `SimpleExtData.base_nontrivial`（deg f ≥ 1 と併せ K[X]/(f) の非自明性を
    供給する素地）。 -/
theorem ct0_base_nontrivial : ct0Field.ring.one ≠ ct0Field.ring.zero :=
  ratIUTField.one_ne_zero

end IUT
