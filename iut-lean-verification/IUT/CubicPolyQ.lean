/-
  IUT/CubicPolyQ.lean — CBP（実 ℚ[X] 上の具体多項式 x³ − 2 とその
  次数/モニック性の実補題）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無・模型ゼロ）。

  **complete_pct 影響**: 柱A「実 Galois 理論／実代数体」の本物の先行
  建設の一枚。親が `quotCRing (polyCRing ratRing) cbpF3` で実代数体
  **ℚ[X]/(x³−2)**（＝ ℚ(∛2)）を作り `quotField_of_bezout` で体化する、
  その多項式側の土台を **本物の多項式環 `polyCRing ratRing`（＝ 実 ℚ[X]）**
  の上に固める。x³ − 2 は toy 模型でなく、実有理数体 `ratRing`（M115F）
  の係数を持つ **`polyCRing ratRing` の実元**であり、単項式 X³
  （`psSingle ratRing ratRing.one 3`）と定数埋め込み `polyC` による −2 の
  和として、環演算 `polyAdd` で構成する（`cbpF3_as_ring`）。

  本スライスが固めるのは「cbpF3 が本物の非自明多項式であること」:
   * `cbpF3_coeff0/1/2/3` — 係数関数の具体値（定数項 −2・x³ 係数 1・
     中間 0）。`psSingle`/`psC` の if 分岐を if_pos/if_neg で確定。
   * `cbpF3_bound` — deg ≤ 3（4 以上の係数は 0）。
   * `cbpF3_monic` — 最高次係数 = 1、かつ 3 より上は 0（degree = 3 の
     tight な特徴づけ；本リポジトリに一般 degree 函数は無いため、
     係数の実補題で degree を確定する）。
   * `cbpF3_lead_ne_zero` — 先頭係数 ≠ 0（親の `SimpleExtData.lead`）。
   * `cbpNegTwo_ne_zero` — 定数項 −2 ≠ 0（x が因子でない素地・f(0) ≠ 0）。
   * `cbpF3_ne_zero` / `cbpF3_ne_one` — cbpF3 は 0 でも 1 でもない
     `polyCRing ratRing` の元（体拡大が非自明である素地）。
   * `cbpConstEmb_injective` — 定数埋め込み ℚ ↪ ℚ[X] が単射（数体の
     基礎体埋め込みが忠実）。

  正直な限定（何を本スライスに含めないか）:
   - 一般の `degree` 函数は本リポジトリに無い（M268F/M269F は次数を明示
     上界パラメータで扱う）。よって degree は「係数 3 = 1（≠0）かつ
     4 以上 0」という実補題群として tight に確定するに留める（parent の
     `SimpleExtData` は deg・bound・lead をこの形で受け取る）。
   - **既約性 / Bezout（x³−2 が ℚ 上既約 ⟹ 極大イデアル ⟹ 体）** は
     本スライスに含めない別スライス（`SimpleExtData.bezout` を親が
     honest 仮説として持ち回るか、拡張ユークリッド互除法で構成する）。
   - x³ を `polyMul cbpX cbpX cbpX` の Cauchy 積として展開する係数計算は
     行わず、単項式 `psSingle _ 1 3` として与える（同じ `polyCRing`
     の実元・より軽い忠実構成）。cbpX 自体は不定元として提供する。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.SimpleExtension
import IUT.FrobeniusCharP
import IUT.Rationals

namespace IUT

/-! ## CBP-0: 有理係数 ℚ の非自明性ユーティリティ -/

/-- **CBP-0a: ℚ は非自明**（1 ≠ 0）— 代表の交差積 1·1 = 0·1 は偽。 -/
theorem cbp_one_ne_zero : ratRing.one ≠ ratRing.zero := by
  intro h
  have h2 : (1 : Int) * 1 = 0 * 1 := quot_exact_rat h
  omega

/-- 定数項に使う有理数 −2 = (−2)/1（実 ℚ の元）。 -/
def cbpNegTwo : ratRing.carrier := ratOfInt.map (-2 : Int)

/-- **CBP-0b: −2 ≠ 0**（実 ℚ 上）— 代表の交差積 (−2)·1 = 0·1 は偽。
    x³ − 2 の定数項が非零、すなわち x が因子でない（f(0) ≠ 0）素地。 -/
theorem cbpNegTwo_ne_zero : cbpNegTwo ≠ ratRing.zero := by
  intro h
  have h2 : (-2 : Int) * 1 = 0 * 1 := quot_exact_rat h
  omega

/-! ## CBP-1: 不定元 x と単項式 x³（polyCRing ratRing の実元） -/

/-- 不定元 x の係数列 = X = (0, 1, 0, …)（単項式 1·X¹）。 -/
def cbpXval : PS ratRing := psSingle ratRing ratRing.one 1

/-- x の有界性（deg ≤ 1）。 -/
theorem cbpXval_bound : IsPolyBounded ratRing cbpXval 2 := by
  intro j hj
  show psSingle ratRing ratRing.one 1 j = ratRing.zero
  exact if_neg (by omega)

/-- **CBP-1a: 不定元 x**（実 ℚ[X] = `polyCRing ratRing` の元）。 -/
def cbpX : Poly ratRing := ⟨cbpXval, ⟨2, cbpXval_bound⟩⟩

/-- x の係数: 定数項 0。 -/
theorem cbpX_coeff0 : cbpX.val 0 = ratRing.zero := by
  show psSingle ratRing ratRing.one 1 0 = ratRing.zero
  exact if_neg (by omega)

/-- x の係数: 一次項 1。 -/
theorem cbpX_coeff1 : cbpX.val 1 = ratRing.one := by
  show psSingle ratRing ratRing.one 1 1 = ratRing.one
  exact if_pos rfl

/-- 単項式 x³ の係数列 = X³ = (0,0,0,1,0,…)。 -/
def cbpMonX3val : PS ratRing := psSingle ratRing ratRing.one 3

/-- x³ の有界性（deg ≤ 3）。 -/
theorem cbpMonX3val_bound : IsPolyBounded ratRing cbpMonX3val 4 := by
  intro j hj
  show psSingle ratRing ratRing.one 3 j = ratRing.zero
  exact if_neg (by omega)

/-- **CBP-1b: 単項式 x³**（実 ℚ[X] の元）。 -/
def cbpMonX3 : Poly ratRing := ⟨cbpMonX3val, ⟨4, cbpMonX3val_bound⟩⟩

/-! ## CBP-2: 具体多項式 f = x³ − 2 -/

/-- f = x³ − 2 の係数列 = X³ + (−2)（単項式 X³ と定数埋め込み −2 の和）。 -/
def cbpF3val : PS ratRing :=
  psAdd ratRing cbpMonX3val (psC ratRing cbpNegTwo)

/-- f の有界性（deg ≤ 3）: j ≥ 4 では X³ 項も定数項も台の外で 0。 -/
theorem cbpF3val_bound : IsPolyBounded ratRing cbpF3val 4 := by
  intro j hj
  show ratRing.add (psSingle ratRing ratRing.one 3 j) (psC ratRing cbpNegTwo j)
      = ratRing.zero
  rw [show psSingle ratRing ratRing.one 3 j = ratRing.zero from if_neg (by omega),
    show psC ratRing cbpNegTwo j = ratRing.zero from if_neg (by omega),
    ratRing.zero_add]

/-- **CBP-2a: 具体多項式 f = x³ − 2**（実 ℚ[X] = `polyCRing ratRing` の元）。 -/
def cbpF3 : Poly ratRing := ⟨cbpF3val, ⟨4, cbpF3val_bound⟩⟩

/-- **CBP-2b: f は環演算で構成される** — f = (単項式 x³) + (定数埋め込み
    `polyC` による −2)。cbpF3 が toy でなく `polyCRing ratRing` の環和
    として本物に建つことを示す（proof irrelevance で val 一致）。 -/
theorem cbpF3_as_ring :
    cbpF3 = polyAdd ratRing cbpMonX3 ((polyC ratRing).map cbpNegTwo) := rfl

/-! ## CBP-3: 係数の実補題（x³ − 2 の係数関数の具体値） -/

/-- **CBP-3a: 定数項 = −2**。 -/
theorem cbpF3_coeff0 : cbpF3.val 0 = cbpNegTwo := by
  show ratRing.add (psSingle ratRing ratRing.one 3 0) (psC ratRing cbpNegTwo 0)
      = cbpNegTwo
  rw [show psSingle ratRing ratRing.one 3 0 = ratRing.zero from if_neg (by omega),
    show psC ratRing cbpNegTwo 0 = cbpNegTwo from if_pos rfl,
    ratRing.zero_add]

/-- **CBP-3b: 一次係数 = 0**。 -/
theorem cbpF3_coeff1 : cbpF3.val 1 = ratRing.zero := by
  show ratRing.add (psSingle ratRing ratRing.one 3 1) (psC ratRing cbpNegTwo 1)
      = ratRing.zero
  rw [show psSingle ratRing ratRing.one 3 1 = ratRing.zero from if_neg (by omega),
    show psC ratRing cbpNegTwo 1 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add]

/-- **CBP-3c: 二次係数 = 0**。 -/
theorem cbpF3_coeff2 : cbpF3.val 2 = ratRing.zero := by
  show ratRing.add (psSingle ratRing ratRing.one 3 2) (psC ratRing cbpNegTwo 2)
      = ratRing.zero
  rw [show psSingle ratRing ratRing.one 3 2 = ratRing.zero from if_neg (by omega),
    show psC ratRing cbpNegTwo 2 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add]

/-- **CBP-3d: 三次係数 = 1**（最高次係数）。 -/
theorem cbpF3_coeff3 : cbpF3.val 3 = ratRing.one := by
  show ratRing.add (psSingle ratRing ratRing.one 3 3) (psC ratRing cbpNegTwo 3)
      = ratRing.one
  rw [show psSingle ratRing ratRing.one 3 3 = ratRing.one from if_pos rfl,
    show psC ratRing cbpNegTwo 3 = ratRing.zero from if_neg (by omega)]
  exact CRing.add_zero ratRing ratRing.one

/-! ## CBP-4: 次数 3・モニック性（degree の tight な特徴づけ） -/

/-- **CBP-4a: f の有界性（deg ≤ 3）** — parent の `SimpleExtData.bound`
    （bound = deg+1 = 4）。 -/
theorem cbpF3_bound : IsPolyBounded ratRing cbpF3.val 4 := cbpF3val_bound

/-- **CBP-4b: 先頭係数 ≠ 0** — parent の `SimpleExtData.lead`。 -/
theorem cbpF3_lead_ne_zero : cbpF3.val 3 ≠ ratRing.zero := by
  rw [cbpF3_coeff3]
  exact cbp_one_ne_zero

/-- **CBP-4c: モニック & degree = 3** — 最高次（3 次）係数 = 1 で、かつ
    3 より上の係数は全て 0。一般 degree 函数を持たない本リポジトリで、
    「deg f = 3 でモニック」を係数の実補題として tight に確定する。 -/
theorem cbpF3_monic :
    cbpF3.val 3 = ratRing.one ∧ ∀ j, 3 < j → cbpF3.val j = ratRing.zero := by
  refine ⟨cbpF3_coeff3, ?_⟩
  intro j hj
  exact cbpF3val_bound j (by omega)

/-! ## CBP-5: 非自明性（0 でも 1 でもない多項式） -/

/-- **CBP-5a: f ≠ 0** — 三次係数が 1 ≠ 0 なので零多項式ではない
    （`polyCRing ratRing` の零元 `polyZero` と分離）。 -/
theorem cbpF3_ne_zero : cbpF3 ≠ (polyCRing ratRing).zero := by
  intro h
  have hv : cbpF3.val = (polyCRing ratRing).zero.val :=
    congrArg (fun t : Poly ratRing => t.val) h
  have h3 : cbpF3.val 3 = psZero ratRing 3 := congrFun hv 3
  rw [cbpF3_coeff3] at h3
  exact cbp_one_ne_zero h3

/-- **CBP-5b: f ≠ 1** — 三次係数が 1 だが単位多項式 `polyOne` の三次係数は
    0（`psOne` は定数項のみ）なので、f は単位元でもない。 -/
theorem cbpF3_ne_one : cbpF3 ≠ (polyCRing ratRing).one := by
  intro h
  have hv : cbpF3.val = (polyCRing ratRing).one.val :=
    congrArg (fun t : Poly ratRing => t.val) h
  have h3 : cbpF3.val 3 = psOne ratRing 3 := congrFun hv 3
  rw [cbpF3_coeff3, show psOne ratRing 3 = ratRing.zero from if_neg (by omega)] at h3
  exact cbp_one_ne_zero h3

/-! ## CBP-6: 定数埋め込み ℚ ↪ ℚ[X] の単射性（基礎体埋め込みの忠実性） -/

/-- **CBP-6: 定数埋め込み `polyC` は単射** — [c] = [d]（定数多項式として
    等しい）なら 0 次係数を読んで c = d。数体 ℚ(∛2) の基礎体 ℚ の
    埋め込みが忠実であることの多項式環側の実証。 -/
theorem cbpConstEmb_injective {c d : ratRing.carrier}
    (h : (polyC ratRing).map c = (polyC ratRing).map d) : c = d := by
  have hv : psC ratRing c = psC ratRing d :=
    congrArg (fun t : Poly ratRing => t.val) h
  have h0 : psC ratRing c 0 = psC ratRing d 0 := congrFun hv 0
  rw [show psC ratRing c 0 = c from if_pos rfl,
    show psC ratRing d 0 = d from if_pos rfl] at h0
  exact h0

end IUT
