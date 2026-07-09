/-
  IUT/Cq3Base.lean — CQ0（A1 実数体 ℚ(ζ₃) = ℚ[x]/(x²+x+1) の基礎データ層 +
  円分多項式 Φ₃ = x²+x+1 の有理根なし＝既約性の基礎）

  ── 分類 **[実／承認済み足場(c)]**（本物の先行建設への足場。骨格でなく
  実 ℚ・実 f = x²+x+1 の本物のデータ・sorry 皆無・新規 Classical.choice
  皆無・模型ゼロ）。名前付き実ターゲット: A1「実数体 K = ℚ[x]/(f) を実際の
  商環として構成」の第二の本物のインスタンス **実二次数体 ℚ(ζ₃)**（ℚ(∛2)
  建設 `CbrtTwoBase`（CT0）の次数2版アナロジー）。本層はその `SimpleExtData`
  の bezout 以外の全 field（modulus/deg/bound/lead/deg_pos/base_nontrivial）に
  渡せるデータを本物で確定し、さらに **Φ₃ の有理根なし**（本丸）を実 ℚ の
  順序で完全証明する。後続:
   - Bezout（f のイデアル極大性）は本層に無い（別スライスの主語）。
   - 有理根なし ⟹ 一次因子なし ⟹ 二次多項式の既約性、の橋渡しは後続。

  **complete_pct 影響**: 本層単体では **complete_pct 未設定（0 前進）**。
  A1 の complete_pct はイデアル極大性・体化が本物で揃った時に動かす。本層は
  「本コース」への足場であり、Φ₃ 既約性の要（有理根の非存在）を実 ℚ 上で
  本物に証明する。

  内容:
   * `cq0Field` — 実 ℚ の `Field268`（既存 `pbzRatField`（M270F-8a）の再利用）。
   * `cq0PS` — x²+x+1 の係数列（単項式 x²・x と定数 1 の psAdd。実 ℚ[X] の実元）。
   * `cq0PS_coeff0..2` — 係数確定（0,1,2 次すべて係数 1）。
   * `cq0_bound` — deg ≤ 2（3 以上の係数は 0）。
   * `cq0_lead` — 先頭係数（2 次）≠ 0。
   * `cq0Modulus` — `simpleExtModulus cq0Field cq0PS 2 cq0_bound`（法多項式 f）。
   * `cq0_base_nontrivial` — 基礎体 ℚ の非自明性 1 ≠ 0。
   * `cq0_quad_pos` — **0 < n² + nd + d²**（d > 0）: 判別式 < 0 の完全平方
     `4(n²+nd+d²) = (2n+d)² + 3d²` を符号場合分けで（choice なし）。
   * `cq0_no_rat_root` — **本丸**: ∀ r∈ℚ, r²+r+1 ≠ 0。代表 (n/d) に落とし、
     交差積で n²d + nd² + d³ = 0 を得、d(n²+nd+d²) の正値性と矛盾させる。
     実 ℚ 上の本物の証明（模型なし）。

  正直な限定（§4 規約により消さない）:
   - **bezout（f のイデアル極大性）は本層に無い**（別スライス）。従って本層
     だけでは ℚ(ζ₃) は体化されない。
   - 有理根なし ⟹ 既約性 の完全な橋渡し（一次因子論法・因子分解の一意性）は
     本層に含めない後続。本層は「有理根が無い」までを本物で確定する。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.CbrtTwoBase
import IUT.Rationals

namespace IUT

/-! ## CQ0-1: 実 ℚ の Field268 -/

/-- **CQ0-1: 基礎体 K = 実 ℚ**（`Field268`）。既存 `pbzRatField`（M270F-8a）の
    再利用。本物の体 ℚ をそのまま A1 の基礎体に据える（模型なし）。 -/
def cq0Field : Field268 := pbzRatField

/-! ## CQ0-2: 法多項式 f = x²+x+1 の係数列 -/

/-- **CQ0-2: f = x²+x+1 の係数列** — 単項式 x²（`psSingle _ 1 2`）・x
    （`psSingle _ 1 1`）と定数 1（`psC _ 1`）の `psAdd`。実 ℚ[X] の実元。
    円分多項式 Φ₃（1 の原始 3 乗根 ζ₃ の最小多項式）。 -/
def cq0PS : PS ratRing :=
  psAdd ratRing
    (psAdd ratRing (psSingle ratRing ratRing.one 2) (psSingle ratRing ratRing.one 1))
    (psC ratRing ratRing.one)

/-! ## CQ0-3: 係数確定（x²+x+1 の係数関数の具体値） -/

/-- **CQ0-3a: 定数項 = 1**。 -/
theorem cq0PS_coeff0 : cq0PS 0 = ratRing.one := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 2 0)
      (psSingle ratRing ratRing.one 1 0)) (psC ratRing ratRing.one 0) = ratRing.one
  rw [show psSingle ratRing ratRing.one 2 0 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 1 0 = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one 0 = ratRing.one from if_pos rfl,
    ratRing.zero_add, ratRing.zero_add]

/-- **CQ0-3b: 一次係数 = 1**。 -/
theorem cq0PS_coeff1 : cq0PS 1 = ratRing.one := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 2 1)
      (psSingle ratRing ratRing.one 1 1)) (psC ratRing ratRing.one 1) = ratRing.one
  rw [show psSingle ratRing ratRing.one 2 1 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 1 1 = ratRing.one from if_pos rfl,
    show psC ratRing ratRing.one 1 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add, CRing.add_zero ratRing ratRing.one]

/-- **CQ0-3c: 二次係数 = 1**（最高次係数）。 -/
theorem cq0PS_coeff2 : cq0PS 2 = ratRing.one := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 2 2)
      (psSingle ratRing ratRing.one 1 2)) (psC ratRing ratRing.one 2) = ratRing.one
  rw [show psSingle ratRing ratRing.one 2 2 = ratRing.one from if_pos rfl,
    show psSingle ratRing ratRing.one 1 2 = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one 2 = ratRing.zero from if_neg (by omega),
    CRing.add_zero ratRing ratRing.one, CRing.add_zero ratRing ratRing.one]

/-! ## CQ0-4: 有界性・先頭係数 -/

/-- **CQ0-4a: f の有界性（deg ≤ 2）** — j ≥ 3 では x²・x 項も定数項も 0。
    `SimpleExtData.bound`（bound = deg+1 = 3）。 -/
theorem cq0_bound : IsPolyBounded ratRing cq0PS 3 := by
  intro j hj
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 2 j)
      (psSingle ratRing ratRing.one 1 j)) (psC ratRing ratRing.one j) = ratRing.zero
  rw [show psSingle ratRing ratRing.one 2 j = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 1 j = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one j = ratRing.zero from if_neg (by omega),
    ratRing.zero_add, ratRing.zero_add]

/-- **CQ0-4b: 先頭係数 ≠ 0** — cq0PS 2 = 1 ≠ 0。`SimpleExtData.lead`。 -/
theorem cq0_lead : cq0PS 2 ≠ ratRing.zero := by
  rw [cq0PS_coeff2]
  exact cbp_one_ne_zero

/-! ## CQ0-5: 法多項式 f（Poly ratRing の元） -/

/-- **CQ0-5: 法多項式 f = x²+x+1**（`Poly ratRing` の元）— `simpleExtModulus`
    で cq0PS（deg 2・bound 3）を多項式に梱包。後続の Bezout（イデアル極大性）・
    体化の**主語**となる法多項式。`deg = 2`（`deg_pos : 1 ≤ 2`）。 -/
def cq0Modulus : Poly ratRing := simpleExtModulus cq0Field cq0PS 2 cq0_bound

/-! ## CQ0-6: 基礎体の非自明性 -/

/-- **CQ0-6: 基礎体 ℚ は非自明**（1 ≠ 0）— `ratIUTField.one_ne_zero`。
    `SimpleExtData.base_nontrivial`。 -/
theorem cq0_base_nontrivial : cq0Field.ring.one ≠ cq0Field.ring.zero :=
  ratIUTField.one_ne_zero

/-! ## CQ0-7: 二次形式の正値性（判別式 < 0 の完全平方） -/

/-- **CQ0-7: 0 < n² + nd + d²**（d > 0）— 4(n²+nd+d²) = (2n+d)² + 3d² より
    n²+nd+d² > 0。完全平方の非負性を n の符号場合分けで（Int.mul_pos_of_neg_of_neg・
    Int.mul_nonneg・omega、choice なし）示す。Φ₃ の判別式 −3 < 0 の反映。 -/
theorem cq0_quad_pos (n d : Int) (hd : 0 < d) :
    0 < n * n + n * d + d * d := by
  have hdd : 0 < d * d := Int.mul_pos hd hd
  cases Int.lt_or_le n 0 with
  | inr hn =>
    have h1 : 0 ≤ n * n := Int.mul_nonneg hn hn
    have h2 : 0 ≤ n * d := Int.mul_nonneg hn (Int.le_of_lt hd)
    omega
  | inl hn =>
    cases Int.lt_or_le n (-d) with
    | inl hlt =>
      have hnp : 0 < n * (n + d) := Int.mul_pos_of_neg_of_neg hn (by omega)
      have hexp : n * (n + d) = n * n + n * d := Int.mul_add n n d
      omega
    | inr hge =>
      have hnn : 0 < n * n := Int.mul_pos_of_neg_of_neg hn hn
      have hdn : 0 ≤ d * (d + n) := Int.mul_nonneg (Int.le_of_lt hd) (by omega)
      have hexp : d * (d + n) = d * d + d * n := Int.mul_add d d n
      have hcomm : d * n = n * d := Int.mul_comm d n
      omega

/-! ## CQ0-8: 本丸 — Φ₃ の有理根なし（既約性の基礎） -/

/-- **CQ0-8: Φ₃ = x²+x+1 は有理根を持たない** — ∀ r ∈ ℚ, r²+r+1 ≠ 0。
    r を代表 n/d（d > 0）に落とすと、環演算は分子分母の交差積に還元され、
    r²+r+1 = 0 は交差積 `n²d + nd² + d³ = 0` を与える。これは
    `d·(n²+nd+d²)` に等しく、d > 0 かつ `cq0_quad_pos` により n²+nd+d² > 0
    なので正、0 と矛盾。実 ℚ の順序による本物の証明（模型なし）で、Φ₃ が ℚ 上
    一次因子を持たない＝**既約性の要**を確定する。 -/
theorem cq0_no_rat_root : ∀ r : QRat,
    ratRing.add (ratRing.add (ratRing.mul r r) r) ratRing.one ≠ ratRing.zero := by
  intro r
  induction r using Quot.ind
  rename_i x
  intro h
  -- 環演算を代表の交差積へ還元
  have h' : Quot.mk ratRel (prAdd (prAdd (prMul x x) x) prOne)
      = Quot.mk ratRel prZero := h
  have hr : ratRel (prAdd (prAdd (prMul x x) x) prOne) prZero := quot_exact_rat h'
  have hr' : (((x.num * x.num) * x.den + x.num * (x.den * x.den)) * 1
      + 1 * ((x.den * x.den) * x.den)) * 1
      = 0 * ((x.den * x.den) * x.den * 1) := hr
  -- 交差積を整理して三次式 = 0 を取り出す
  have hE : (x.num * x.num) * x.den + x.num * (x.den * x.den)
      + (x.den * x.den) * x.den = 0 := by omega
  -- 三次式 = (n²+nd+d²)·d、それは正なので矛盾
  have hq := cq0_quad_pos x.num x.den x.den_pos
  have hid : (x.num * x.num) * x.den + x.num * (x.den * x.den) + (x.den * x.den) * x.den
      = (x.num * x.num + x.num * x.den + x.den * x.den) * x.den := by
    rw [Int.add_mul, Int.add_mul, Int.mul_assoc x.num x.den x.den]
  have hpos : 0 < (x.num * x.num + x.num * x.den + x.den * x.den) * x.den :=
    Int.mul_pos hq x.den_pos
  rw [← hid] at hpos
  omega

end IUT
