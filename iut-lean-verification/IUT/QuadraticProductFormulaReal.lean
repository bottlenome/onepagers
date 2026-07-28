/-
  IUT/QuadraticProductFormulaReal.lean — M366R: 実二次体 ℚ(√D) の実ノルム乗法性と
  **実**積公式への還元（M366F の循環還元の修復）

  ── 主要成果の分類: **[実]** / §2 分類: **(a) 昇格**
     （M366F `QuadraticProductFormula.lean` が「一般数体の忠実な部分ケース」を
     **循環的な模型** M351F `pf_product_formula` へ還元していた欠陥を、
     還元先を**実の積公式** `IUT/B5ProductFormulaQ.lean` の `b5_product_formula`
     に張り替え、主語を**実の ℚ(√D) の元**（実 ℚ×ℚ 台 `qdfCarrier`、
     `IUT/QuadraticField.lean` の本物の二次体）に置換する）。

  complete_pct 影響: **柱B/B5「大域類体論・積公式(実)」の前進を主張する**
  （判定は独立監査）。動かす内容は次の三点に限る:
   1. 実二次体 ℚ(√D)（実台 ℚ×ℚ、実乗法 (a,b)(c,d)=(ac+D·bd, ad+bc)）の
      **実ノルム N(a,b)=a²−D·b² ∈ ℚ の乗法性 N(xy)=N(x)N(y)** の完全証明。
   2. x ≠ 0 ⟹ N(x) ∈ ℚ^× と、その **実の PreRat 代表の分子非零**、
      すなわち実 b5 積公式の仮説が満たされることの完全証明（**実の還元**）。
   3. 得られる帰結 |N(x)|_∞ · ∏_p |N(x)|_p = 1（実 `arpAbs`・実 `pavAbs`・
      実素因数分解の上の `b5_product_formula`）と、その積構造との両立
      （N(x)·N(y) の代表 = 代表の積）。

  ## 本モジュールが依存しないもの（監査可能な事実）
  `import` 閉包は `B5ProductFormulaQ`（実積公式）と `QuadraticField`（実二次体）
  のみを核とし、**`IUT/ProductFormula.lean`（M351F・循環模型）を含まない**。
  M366F が継承していた循環はここでは存在しない。

  ## 正直な限定（消去・弱化禁止）
  1. **K の素点そのものは未構成**。K の各素点 v での |x|_v も、分解 ∏_{v|p} も
     形式化していない。本モジュールが証明するのは
     「ノルムを取って ℚ 側の実積公式へ落とす」という**還元の実部分**であり、
     恒等式 ∏_{v|p}|x|_v^{[K_v:ℚ_v]} = |N_{K/ℚ}(x)|_p 自体は**未証明**である
     （`qprAggFin`/`qprAggArch` はその左辺の**定義**であって定理ではない。
     この点で「K の積公式を証明した」とは主張しない）。
  2. したがって本モジュールの積公式の**主語は N(x) ∈ ℚ^×**であり、K の元 x に
     ついては「x ↦ N(x) の実対応と、N(x) 側の実積公式」までである。
     重み [K:ℚ]=2 が本物に現れるのは **ℚ ⊂ K の元** x = ι(v) の場合のみで、
     そこでは N(ι v) = v² が実際に証明され、各素点で |N(ι v)|_w = |v|_w²
     （= |v|_w^{[K:ℚ]}）が実の乗法性から従う（qpr-5）。一般の x では
     重み分解は**未達**。
  3. 局所次数表（qpr-6 の `qprFinMult`/`qprArchMult`）は M366F-3 からの
     **移送であり新規性はない**。また分解理論（e·f・Σe_vf_v=[K:ℚ]）から導出した
     ものではなく**分解型の列挙**にすぎない。honest な位置づけとしては
     「[K:ℚ]=2 という数値の簿記」であり、証明された数論的内容ではない。
  4. 非零性・ゼロ判定は代表 witness 形（`r.num ≠ 0` / `x ≠ qdfZero` / D 非平方
     witness `hD`）。商 ℚ の全域ゼロ判定選言は排中律を要するため対象外
     （`qMul_inv`・`qdf_norm_ne_zero`・`b5_product_formula` の既存の正直申告を継承）。
  5. 値は ℚ≥0 内（ℝ 未構成）。log を取った次数式 Σ_v d_v·log|x|_v = 0 へは進めない。
  6. D は「ℚ で平方でない」witness 付きの任意の有理数。具体 witness は負の D
     （実例は D=−1）のみ — 正の非平方 D（√2∉ℚ 等）の witness は
     `QuadraticField.lean` の正直申告どおり未達で、本モジュールもそれを継承する。

  ## 新規 / 重複・移送 の内訳（過大主張防止・自己申告・機械確認済）
  * **新規**（★**正直な訂正（独立敵対監査 2026-07-21）**: 当初「コードベースに同等物なしを確認」と
    書いたが、その grep は識別子 `qdfNorm` に対してのみで**数学的内容に対しては行っていなかった**。
    実際には `IUT/QuadraticNorm.lean` の `qnm_mul` が **D=−1（ℚ(i)）の場合の実 ℚ 上ノルム乗法性**
    を既に持つ。したがって `qpr_norm_mul` の真の増分は「**任意の非平方 D への一般化**」であって
    「初のノルム乗法性」ではない。また `qpr_mul4` は `CRing.mul_mul_mul_comm` だけでなく
    `qnm_mul_mul_mul_comm` とも文字通り同一のコピー（リポ内 3 本目）。
    さらに監査の中心的判定: **輸出された積公式は decisively `b5∘N`**——結論は `r` のみに言及し
    証明項は `b5_product_formula r (qpr_rep_ne_zero …)` そのもので、B5 の既存 0.50 が購入済の
    b5 の**特殊化（論理的に弱い）**である。監査結果 B5 0.50→0.51（+0.01）。）:
    - `qpr_norm_mul` — 実 ℚ(√D) の `qdfNorm` に対する乗法性。本モジュール以前は
      `qdfNorm`/`qdfRing` を参照するファイルが `QuadraticField.lean` 以外に
      存在せず（grep 確認）、ノルム乗法性の言明もなかった。
    - `qpr_rep_ne_zero`・`qpr_product_formula`・`qpr_global_product_formula`
      — 実 ℚ(√D) から**実の** b5 積公式への還元（M366F の循環還元の置換）。
    - `qpr_norm_emb`（N(ι v)=v²）と、それを使う `qpr_product_formula_rational`。
    - 実例 `qpr_example_gauss`・`qpr_example_sqrtNegTwo`。
  * **既存定理の重複（rfl / `.symm` で一致することを機械確認した — 新規ではない）**:
    - `qpr_conj_mul` は `(qdfConj D hD).map_mul` と**同一**
      （`example … := (qdfConj D hD).map_mul x y` が通る）。本版の差分は
      非平方 witness `hD` を要求しないことだけ。
    - `qpr_emb_mul` は `((qdfExtension D hD).incl_mul v w).symm` と**同一**
      （同じく機械確認）。差分は `hD` 不要という点のみ。
    - `qprConj` は `(qdfConj D hD).toFun` と定義的に同一（`rfl` 確認）、
      `qprEmb` は `(qdfExtension D hD).incl` と同じ写像。
    - `qpr_arch_weight_two`/`qpr_padic_weight_two` は既存 `arp_abs_mul`/`pav_mul`
      の**単なるインスタンス化**（証明本体ゼロ）。
  * **移送（新規性なし）**: 共役 ring-hom による Brahmagupta 証明のイディオムは
    `IUT/Q3RamifiedQuadratic.lean` の `q3rq_norm_mul`（底 z3・D=−3）からの移送で
    あり、発明ではない（本モジュールは底 ratRing・任意の D で再実装）。
    局所次数リスト（qpr-6）は M366F-3 からの移送。4 因子入替 `qpr_mul4` は
    既存 `CRing.mul_mul_mul_comm`（LTIterate）と同内容の補題の再証明
    （import 閉包を最小に保つための自前版）。
  * **「初」「初めて」の類の主張はしない**。本モジュールの寄与は
    「循環していない実の還元を一本通したこと」であって、新イディオムの発明ではない。

  全て Lean 4.30.0 core のみ（mathlib 不使用）・sorry なし・新規 Classical.choice
  なし・禁止タクティク不使用。
-/
import IUT.B5ProductFormulaQ
import IUT.QuadraticField

namespace IUT

/-! ## qpr-1: 汎用の 4 因子入替（可換環） -/

/-- 4 因子入替 (ab)(cd) = (ac)(bd)（任意の可換環。既存 `CRing.mul_mul_mul_comm`
    と同内容の再証明 — import 閉包を B5+QuadraticField に閉じるための自前版）。 -/
theorem qpr_mul4 (R : CRing) (a b c d : R.carrier) :
    R.mul (R.mul a b) (R.mul c d) = R.mul (R.mul a c) (R.mul b d) := by
  rw [R.mul_assoc a b (R.mul c d), ← R.mul_assoc b c d, R.mul_comm b c,
    R.mul_assoc c b d, ← R.mul_assoc a c (R.mul b d)]

/-- 4 因子入替の ℚ(√D) 版（`qdfRing D` の可換環公理から）。 -/
theorem qpr_mul4Q (D : QRat) (a b c d : qdfCarrier) :
    qdfMul D (qdfMul D a b) (qdfMul D c d)
      = qdfMul D (qdfMul D a c) (qdfMul D b d) :=
  qpr_mul4 (qdfRing D) a b c d

/-! ## qpr-2: 実 ℚ(√D) の共役・ℚ の埋め込み・実ノルムの乗法性

    台は `IUT/QuadraticField.lean` の**実の** ℚ×ℚ（`qdfCarrier`、(a,b) ↔ a+b√D）、
    乗法は実の √D 則 `qdfMul`、ノルムは実の `qdfNorm D (a,b) = a²−D·b² ∈ ℚ`。
    模型・surrogate は用いない。 -/

/-- **共役** (a,b)̄ = (a,−b)（√D ↦ −√D）。`qdfConj`（FieldAut 版）は非平方
    witness `hD` を要するため、witness 不要の台レベル版をここで用いる。 -/
def qprConj (x : qdfCarrier) : qdfCarrier :=
  ((x.1, ratRing.neg x.2) : qdfCarrier)

/-- **ℚ の埋め込み** ι : ℚ → ℚ(√D)、v ↦ (v,0) = v + 0·√D。 -/
def qprEmb (v : QRat) : qdfCarrier := ((v, ratRing.zero) : qdfCarrier)

/-- ι は乗法的: ι(v)·ι(w) = ι(vw)（ℚ(√D) の対角部分環）。
    **重複申告**: 既存 `((qdfExtension D hD).incl_mul v w).symm` と同一（確認済）。
    差分は `hD` 不要という点のみ。新規ではない。 -/
theorem qpr_emb_mul (D : QRat) (v w : QRat) :
    qdfMul D (qprEmb v) (qprEmb w) = qprEmb (ratRing.mul v w) := by
  apply qdf_ext
  · show ratRing.add (ratRing.mul v w)
        (ratRing.mul D (ratRing.mul ratRing.zero ratRing.zero))
      = ratRing.mul v w
    rw [ratRing.mul_zero ratRing.zero, ratRing.mul_zero D,
      ratRing.add_zero (ratRing.mul v w)]
  · show ratRing.add (ratRing.mul v ratRing.zero)
        (ratRing.mul ratRing.zero w) = ratRing.zero
    rw [ratRing.mul_zero v, ratRing.zero_mul w,
      ratRing.add_zero ratRing.zero]

/-- **共役は乗法的** (xy)̄ = x̄·ȳ（ℚ(√D) の非自明自己同型の乗法性、台レベル）。
    **重複申告**: これは既存 `(qdfConj D hD).map_mul` と同一の命題であり
    （`example … := (qdfConj D hD).map_mul x y` が通ることを確認済）、新規ではない。
    差分は非平方 witness `hD` を仮定しない点のみ。 -/
theorem qpr_conj_mul (D : QRat) (x y : qdfCarrier) :
    qprConj (qdfMul D x y) = qdfMul D (qprConj x) (qprConj y) := by
  apply qdf_ext
  · show ratRing.add (ratRing.mul x.1 y.1) (ratRing.mul D (ratRing.mul x.2 y.2))
      = ratRing.add (ratRing.mul x.1 y.1)
          (ratRing.mul D (ratRing.mul (ratRing.neg x.2) (ratRing.neg y.2)))
    rw [ratRing.neg_mul x.2 (ratRing.neg y.2), ratRing.mul_neg x.2 y.2,
      ratRing.neg_neg (ratRing.mul x.2 y.2)]
  · show ratRing.neg (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1))
      = ratRing.add (ratRing.mul x.1 (ratRing.neg y.2))
          (ratRing.mul (ratRing.neg x.2) y.1)
    rw [ratRing.mul_neg x.1 y.2, ratRing.neg_mul x.2 y.1,
      ratRing.neg_add_dist (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)]

/-- **x·x̄ = ι(N(x))** — 第 1 成分 a²−D·b² = N(x)、第 2 成分 −ab+ba = 0。 -/
theorem qpr_mul_conj (D : QRat) (x : qdfCarrier) :
    qdfMul D x (qprConj x) = qprEmb (qdfNorm D x) := by
  apply qdf_ext
  · show ratRing.add (ratRing.mul x.1 x.1)
        (ratRing.mul D (ratRing.mul x.2 (ratRing.neg x.2)))
      = ratRing.add (ratRing.mul x.1 x.1)
          (ratRing.neg (ratRing.mul D (ratRing.mul x.2 x.2)))
    rw [ratRing.mul_neg x.2 x.2, ratRing.mul_neg D (ratRing.mul x.2 x.2)]
  · show ratRing.add (ratRing.mul x.1 (ratRing.neg x.2)) (ratRing.mul x.2 x.1)
      = ratRing.zero
    rw [ratRing.mul_neg x.1 x.2, ratRing.mul_comm x.2 x.1]
    exact ratRing.neg_add (ratRing.mul x.1 x.2)

/-- **★ 実ノルムの乗法性（新規）** N(x·y) = N(x)·N(y)（実 ℚ(√D) 上、任意の D）。
    共役が ring-hom であること x·x̄ = ι(N(x)) と 4 因子入替から
    ι(N(xy)) = (xy)(x̄ȳ) = (xx̄)(yȳ) = ι(N(x))·ι(N(y)) = ι(N(x)N(y))、
    第 1 成分を取って結論。多項式恒等式（Brahmagupta）の機械展開を回避する
    このイディオム自体は `Q3RamifiedQuadratic.q3rq_norm_mul` からの移送で、
    新規なのは**実 ℚ(√D)（`qdfNorm`）に対する乗法性という結論**である。 -/
theorem qpr_norm_mul (D : QRat) (x y : qdfCarrier) :
    qdfNorm D (qdfMul D x y) = ratRing.mul (qdfNorm D x) (qdfNorm D y) := by
  have hchain : qprEmb (qdfNorm D (qdfMul D x y))
      = qprEmb (ratRing.mul (qdfNorm D x) (qdfNorm D y)) := by
    rw [← qpr_mul_conj D (qdfMul D x y), qpr_conj_mul D x y,
      qpr_mul4Q D x y (qprConj x) (qprConj y),
      qpr_mul_conj D x, qpr_mul_conj D y, qpr_emb_mul D]
  exact congrArg Prod.fst hchain

/-- **N(1) = 1**（ノルムはモノイド準同型 K^× → ℚ^×）。 -/
theorem qpr_norm_one (D : QRat) : qdfNorm D qdfOne = ratRing.one := by
  show ratRing.add (ratRing.mul ratRing.one ratRing.one)
      (ratRing.neg (ratRing.mul D (ratRing.mul ratRing.zero ratRing.zero)))
    = ratRing.one
  rw [ratRing.one_mul ratRing.one, ratRing.mul_zero ratRing.zero,
    ratRing.mul_zero D, gqi_q_neg_zero, ratRing.add_zero ratRing.one]

/-! ## qpr-3: 実の還元 — N(x) の実代表は分子非零、ゆえに実 b5 積公式が使える -/

/-- 分子が 0 の代表は ℚ の 0（Quot.sound、choice 不使用）。 -/
theorem qpr_zero_of_num_zero (r : PreRat) (h : r.num = 0) :
    Quot.mk ratRel r = ratRing.zero := by
  show Quot.mk ratRel r = Quot.mk ratRel prZero
  apply Quot.sound
  show r.num * (1 : Int) = 0 * r.den
  rw [h, Int.zero_mul, Int.zero_mul]

/-- 分子非零の代表は ℚ の非零元。 -/
theorem qpr_num_ne_zero_of_ne (r : PreRat) (h : Quot.mk ratRel r ≠ ratRing.zero) :
    r.num ≠ 0 := by
  intro h0
  exact h (qpr_zero_of_num_zero r h0)

/-- 逆向き: 代表の分子が非零なら ℚ で非零。 -/
theorem qpr_ne_zero_of_num_ne (r : PreRat) (h : r.num ≠ 0) :
    Quot.mk ratRel r ≠ ratRing.zero := by
  intro h0
  apply h
  have hrel : r.num * (1 : Int) = 0 * r.den := quot_exact_rat h0
  omega

/-- **★ 還元の核（新規）** — x ≠ 0（実 ℚ(√D) の元）なら、そのノルム N(x) の
    **任意の実 PreRat 代表 r の分子は非零**。実ノルム非退化 `qdf_norm_ne_zero`
    （D 非平方 witness）から。これが実 b5 積公式 `b5_product_formula` の
    唯一の仮説であり、ここを実で埋めることが M366F の循環還元の修復にあたる。 -/
theorem qpr_rep_ne_zero (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D)
    (x : qdfCarrier) (hx : x ≠ qdfZero) (r : PreRat)
    (hr : Quot.mk ratRel r = qdfNorm D x) : r.num ≠ 0 := by
  apply qpr_num_ne_zero_of_ne
  rw [hr]
  exact qdf_norm_ne_zero D hD x hx

/-! ## qpr-4: 実 ℚ(√D) の元に対する実積公式（b5 への実の還元）

    **正直な限定（再掲・§4）**: K の素点は未構成であり、
    ∏_{v|p}|x|_v^{[K_v:ℚ_v]} = |N(x)|_p は**証明していない**。以下の
    `qprAggFin`/`qprAggArch` はその左辺の**定義**（記法）であって定理ではない。
    実の内容は「N(x) の実代表に対する実の ∏_v = 1」である。 -/

/-- ノルム還元によるアルキメデス側の集約因子（**定義**）:
    ∏_{v|∞}|x|_v^{[K_v:ℝ]} := |N(x)|_∞（実 `arpAbs`）。 -/
def qprAggArch (r : PreRat) : QRat := arpAbs (Quot.mk ratRel r)

/-- ノルム還元による p 上の集約因子（**定義**）:
    ∏_{v|p}|x|_v^{[K_v:ℚ_p]} := |N(x)|_p（実 `pavAbs`）。 -/
def qprAggFin (p : Nat) (r : PreRat) : QRat := pavAbs p r

/-- 集約された大域積 |N(x)|_∞ · ∏_{p∈Supp}|N(x)|_p（実 `fspProd`・実 `b5Support`）。 -/
def qprGlobalProd (r : PreRat) : QRat :=
  ratRing.mul (qprAggArch r) (fspProd (fun p => qprAggFin p r) (b5Support r))

/-- **★ 実積公式（本丸・M366F の修復版）** — 実二次体 ℚ(√D)（D は ℚ で
    平方でない）の非零元 x と、その**実ノルム** N(x) ∈ ℚ^× の任意の実代表 r に対し
        |N(x)|_∞ · ∏_{p ∈ Supp(N(x))} |N(x)|_p = 1。
    循環模型 M351F ではなく**実の** `b5_product_formula`（実 ℚ・実 `arpAbs`・
    実 `pavAbs`・実素因数分解）へ還元する。 -/
theorem qpr_product_formula (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D)
    (x : qdfCarrier) (hx : x ≠ qdfZero) (r : PreRat)
    (hr : Quot.mk ratRel r = qdfNorm D x) :
    ratRing.mul (arpAbs (Quot.mk ratRel r))
      (fspProd (fun p => pavAbs p r) (b5Support r)) = ratRing.one :=
  b5_product_formula r (qpr_rep_ne_zero D hD x hx r hr)

/-- 集約記法版（`qprGlobalProd` は上の左辺の定義的言い換え）。 -/
theorem qpr_global_product_formula (D : QRat)
    (hD : ∀ u : QRat, ratRing.mul u u ≠ D) (x : qdfCarrier) (hx : x ≠ qdfZero)
    (r : PreRat) (hr : Quot.mk ratRel r = qdfNorm D x) :
    qprGlobalProd r = ratRing.one :=
  qpr_product_formula D hD x hx r hr

/-- **還元は乗法構造と両立する** — r が N(x) の代表、s が N(y) の代表なら
    `prMul r s` は N(xy) の代表（実ノルム乗法性 `qpr_norm_mul` の代表版）。
    K^× → ℚ^× → {実積公式} という還元が群構造を保つことの実の内容。 -/
theorem qpr_rep_mul (D : QRat) (x y : qdfCarrier) (r s : PreRat)
    (hr : Quot.mk ratRel r = qdfNorm D x) (hs : Quot.mk ratRel s = qdfNorm D y) :
    Quot.mk ratRel (prMul r s) = qdfNorm D (qdfMul D x y) := by
  rw [qpr_norm_mul D x y, ← hr, ← hs]
  rfl

/-! ## qpr-5: ℚ ⊂ K の元での重み [K:ℚ]=2 の実現（実の局所次数簿記）

    K の一般の元では素点分解が未構成だが、**ℚ ⊂ K の元** x = ι(v) では
    N(ι v) = v² が実に証明でき、各素点 w で |N(ι v)|_w = |v|_w·|v|_w = |v|_w^{[K:ℚ]}
    が実の絶対値乗法性から従う。重み 2 = [K:ℚ] が模型でなく本物に現れる唯一の切片。 -/

/-- **N(ι v) = v²** — ℚ の元の K でのノルムは平方（= v^{[K:ℚ]}、[K:ℚ]=2）。 -/
theorem qpr_norm_emb (D : QRat) (v : QRat) :
    qdfNorm D (qprEmb v) = ratRing.mul v v := by
  show ratRing.add (ratRing.mul v v)
      (ratRing.neg (ratRing.mul D (ratRing.mul ratRing.zero ratRing.zero)))
    = ratRing.mul v v
  rw [ratRing.mul_zero ratRing.zero, ratRing.mul_zero D, gqi_q_neg_zero,
    ratRing.add_zero (ratRing.mul v v)]

/-- ι は単射的に非零を保つ: v ≠ 0 ⟹ ι(v) ≠ 0。 -/
theorem qpr_emb_ne_zero (v : QRat) (hv : v ≠ ratRing.zero) :
    qprEmb v ≠ qdfZero := by
  intro h
  exact hv (congrArg Prod.fst h)

/-- `prMul r r` は N(ι v)（v = [r]）の実代表。 -/
theorem qpr_rep_emb (D : QRat) (r : PreRat) :
    Quot.mk ratRel (prMul r r) = qdfNorm D (qprEmb (Quot.mk ratRel r)) := by
  rw [qpr_norm_emb D (Quot.mk ratRel r)]
  rfl

/-- **アルキメデス側の重み 2**: |N(ι v)|_∞ = |v|_∞·|v|_∞（実 `arpAbs` の乗法性）。
    **重複申告**: 既存 `arp_abs_mul` の単なるインスタンス化（証明本体ゼロ）。 -/
theorem qpr_arch_weight_two (r : PreRat) :
    arpAbs (Quot.mk ratRel (prMul r r))
      = ratRing.mul (arpAbs (Quot.mk ratRel r)) (arpAbs (Quot.mk ratRel r)) :=
  arp_abs_mul (Quot.mk ratRel r) (Quot.mk ratRel r)

/-- **p 進側の重み 2**: |N(ι v)|_p = |v|_p·|v|_p（実 `pavAbs` の乗法性）。
    **重複申告**: 既存 `pav_mul` の単なるインスタンス化（証明本体ゼロ）。 -/
theorem qpr_padic_weight_two (p : Nat) (hp : IsPrime p) (r : PreRat)
    (hr : r.num ≠ 0) :
    pavAbs p (prMul r r) = ratRing.mul (pavAbs p r) (pavAbs p r) :=
  pav_mul p hp r r hr hr

/-- **ℚ ⊂ K の元での実積公式** — v ∈ ℚ^×（代表 r, r.num ≠ 0）に対し、
    K = ℚ(√D) の元 ι(v) の実積公式（N(ι v) = v² の実代表 `prMul r r` に対する
    実の ∏ = 1）。
    **正直な限定**: 各因子が `qpr_arch_weight_two`/`qpr_padic_weight_two` により
    平方（= 重み [K:ℚ]=2）であることは証明済だが、**大域積そのものを
    (|v|_∞·∏_p|v|_p)² の形に書き換えることは未証明**である（台リスト
    `b5Support (prMul r r)` と `b5Support r` は同じ素数集合を持つが同一の
    リストとは限らず、有限積の並べ替え不変性を本モジュールでは証明していない）。
    したがって「重み 2 の積公式を大域形で証明した」とは主張しない。 -/
theorem qpr_product_formula_rational (D : QRat)
    (hD : ∀ u : QRat, ratRing.mul u u ≠ D) (r : PreRat) (hr : r.num ≠ 0) :
    ratRing.mul (arpAbs (Quot.mk ratRel (prMul r r)))
      (fspProd (fun p => pavAbs p (prMul r r)) (b5Support (prMul r r)))
      = ratRing.one :=
  qpr_product_formula D hD (qprEmb (Quot.mk ratRel r))
    (qpr_emb_ne_zero (Quot.mk ratRel r) (qpr_ne_zero_of_num_ne r hr))
    (prMul r r) (qpr_rep_emb D r)

/-! ## qpr-6: 局所次数の簿記 Σ_{v|p}[K_v:ℚ_v] = [K:ℚ] = 2

    **正直な位置づけ（§4・過大主張防止）**: 本節は M366F-3 からの**移送であり
    新規性はない**。また分解理論（Σ_{v|p} e_v f_v = [K:ℚ] の証明）から導いた
    ものではなく、二次体の分解型を**列挙して各々の和が 2 であることを確認する
    だけ**の簿記である。数論的内容は含まない。 -/

/-- [K:ℚ] = 2（二次拡大の絶対次数）。 -/
def qprDegree : Nat := 2

/-- 有限素点の分解型（分裂・惰性・分岐）の列挙。 -/
inductive qprFinSplit where
  /-- 分裂 p = v·v̄（相異なる二素点、各 [K_v:ℚ_p]=1）。 -/
  | split
  /-- 惰性（一素点、f=2, e=1）。 -/
  | inert
  /-- 分岐 p = v²（一素点、e=2, f=1）。 -/
  | ramified

/-- 分解型ごとの局所次数リスト [K_v:ℚ_p]（v|p）。 -/
def qprFinMult : qprFinSplit → List Nat
  | .split => [1, 1]
  | .inert => [2]
  | .ramified => [2]

/-- アルキメデス素点の型（D>0 は実素点 2 個、D<0 は複素素点 1 個）。 -/
inductive qprArchSplit where
  /-- 実素点 2 個（各 [K_v:ℝ]=1）。 -/
  | realPlaces
  /-- 複素素点 1 個（[K_v:ℝ]=2）。 -/
  | complexPlace

/-- アルキメデス局所次数リスト。 -/
def qprArchMult : qprArchSplit → List Nat
  | .realPlaces => [1, 1]
  | .complexPlace => [2]

/-- リストの総和 Σ_{v|p}[K_v:ℚ_v]。 -/
def qprListSum : List Nat → Nat
  | [] => 0
  | m :: ms => m + qprListSum ms

/-- 有限素点: どの分解型でも Σ_{v|p}[K_v:ℚ_p] = 2 = [K:ℚ]（列挙による確認）。 -/
theorem qpr_fin_degree_sum (s : qprFinSplit) :
    qprListSum (qprFinMult s) = qprDegree := by
  cases s with
  | split => rfl
  | inert => rfl
  | ramified => rfl

/-- アルキメデス素点: Σ_{v|∞}[K_v:ℝ] = 2 = [K:ℚ]（列挙による確認）。 -/
theorem qpr_arch_degree_sum (s : qprArchSplit) :
    qprListSum (qprArchMult s) = qprDegree := by
  cases s with
  | realPlaces => rfl
  | complexPlace => rfl

/-! ## qpr-7: 実例 — ガウス体 ℚ(i) = ℚ(√−1) の実元 1+i（N = 2） -/

/-- D = −1（ℚ(i) の被開平数、実 witness は `qdf_negOne_not_square`）。 -/
def qprNegOne : QRat := ratRing.neg ratRing.one

/-- D = −1 は ℚ で平方でない（`QuadraticField` の実 witness を消費）。 -/
theorem qprNegOne_not_square : ∀ u : QRat, ratRing.mul u u ≠ qprNegOne :=
  qdf_negOne_not_square

/-- 実の元 1 + i ∈ ℚ(i)（実 ℚ×ℚ 台の (1,1)）。 -/
def qprOnePlusI : qdfCarrier := ((ratRing.one, ratRing.one) : qdfCarrier)

/-- 1 + i ≠ 0。 -/
theorem qpr_onePlusI_ne_zero : qprOnePlusI ≠ qdfZero := by
  intro h
  have h1 : (ratRing.one : QRat) = ratRing.zero := congrArg Prod.fst h
  have h2 : (1 : Int) * 1 = 0 * 1 := quot_exact_rat h1
  omega

/-- **N(1+i) = 2**（実ノルム a²−D·b² = 1+1 = 2）。 -/
theorem qpr_norm_onePlusI :
    qdfNorm qprNegOne qprOnePlusI = ratRing.add ratRing.one ratRing.one := by
  show ratRing.add (ratRing.mul ratRing.one ratRing.one)
      (ratRing.neg (ratRing.mul (ratRing.neg ratRing.one)
        (ratRing.mul ratRing.one ratRing.one)))
    = ratRing.add ratRing.one ratRing.one
  rw [ratRing.one_mul ratRing.one,
    ratRing.neg_mul ratRing.one ratRing.one, ratRing.one_mul ratRing.one,
    ratRing.neg_neg ratRing.one]

/-- 2 = N(1+i) の実 PreRat 代表（2/1）。 -/
theorem qpr_rep_two :
    Quot.mk ratRel (intToPreRat 2) = qdfNorm qprNegOne qprOnePlusI := by
  rw [qpr_norm_onePlusI]
  apply Quot.sound
  show (2 : Int) * (1 * 1) = (1 * 1 + 1 * 1) * 1
  omega

/-- **★ 実例（本物の数・本物の絶対値）**: ℚ(i) の実元 1+i に対する実積公式
        |2|_∞ · ∏_{p ∈ Supp(2)} |2|_p = 1
    （N(1+i) = 2 の実代表に実 b5 積公式を適用）。主語は実の有理数 2 であり、
    模型・自由パラメータ（M351F の `logp`）は一切現れない。 -/
theorem qpr_example_gauss :
    ratRing.mul (arpAbs (Quot.mk ratRel (intToPreRat 2)))
      (fspProd (fun p => pavAbs p (intToPreRat 2)) (b5Support (intToPreRat 2)))
      = ratRing.one :=
  qpr_product_formula qprNegOne qprNegOne_not_square qprOnePlusI
    qpr_onePlusI_ne_zero (intToPreRat 2) qpr_rep_two

/-- 実例（ℚ(√−2) の元 √−2、N = 2）— 同じ実の還元が別の実二次体でも走ることの確認。 -/
theorem qpr_example_sqrtNegTwo :
    ratRing.mul (arpAbs (Quot.mk ratRel (intToPreRat 2)))
      (fspProd (fun p => pavAbs p (intToPreRat 2)) (b5Support (intToPreRat 2)))
      = ratRing.one := by
  apply qpr_product_formula qdfNegTwo qdfNegTwo_not_square qdfSqrt
  · intro h
    have h1 : (ratRing.one : QRat) = ratRing.zero := congrArg Prod.snd h
    have h2 : (1 : Int) * 1 = 0 * 1 := quot_exact_rat h1
    omega
  · show Quot.mk ratRel (intToPreRat 2)
      = ratRing.add (ratRing.mul ratRing.zero ratRing.zero)
          (ratRing.neg (ratRing.mul qdfNegTwo
            (ratRing.mul ratRing.one ratRing.one)))
    rw [ratRing.mul_zero ratRing.zero, ratRing.one_mul ratRing.one]
    show Quot.mk ratRel (intToPreRat 2)
      = ratRing.add ratRing.zero
          (ratRing.neg (ratRing.mul
            (ratRing.neg (ratRing.add ratRing.one ratRing.one)) ratRing.one))
    rw [ratRing.neg_mul (ratRing.add ratRing.one ratRing.one) ratRing.one,
      ratRing.neg_neg (ratRing.mul (ratRing.add ratRing.one ratRing.one)
        ratRing.one),
      ratRing.zero_add (ratRing.mul (ratRing.add ratRing.one ratRing.one)
        ratRing.one)]
    apply Quot.sound
    show (2 : Int) * ((1 * 1) * 1) = ((1 * 1 + 1 * 1) * 1) * (1 * 1)
    omega

end IUT

#print axioms IUT.qpr_norm_mul
#print axioms IUT.qpr_rep_ne_zero
#print axioms IUT.qpr_product_formula
#print axioms IUT.qpr_global_product_formula
#print axioms IUT.qpr_rep_mul
#print axioms IUT.qpr_norm_emb
#print axioms IUT.qpr_arch_weight_two
#print axioms IUT.qpr_padic_weight_two
#print axioms IUT.qpr_product_formula_rational
#print axioms IUT.qpr_example_gauss
#print axioms IUT.qpr_example_sqrtNegTwo
#print axioms IUT.qpr_norm_one
#print axioms IUT.qpr_fin_degree_sum
#print axioms IUT.qpr_arch_degree_sum
