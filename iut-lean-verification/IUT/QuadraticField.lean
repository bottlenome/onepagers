/-
  IUT/QuadraticField.lean — M2xxG: 二次体 ℚ(√D) と Galois 群の位数ちょうど 2
  柱A 実 Galois 塔の第二段 — ℚ(i)（M2xxF）の一般化と「位数 2」ギャップの閉鎖
  （§2(b) 本物建設）

  ── 主要成果の分類: **[実]**（本物の二次体 ℚ(√D)（D は「ℚ で平方でない」witness
  付きの任意の有理数）と、その Galois 群 Gal(ℚ(√D)/ℚ) の**位数ちょうど 2** の
  完全証明）。

  complete_pct 影響: **柱A 実 Galois 群論の前進**。M2xxF（ℚ(i)）が正直申告で
  残した「Gal の位数がちょうど 2（= 非自明元は共役のみ）」の未達を、
  一般の非平方 D 上で**本物に閉じる**。
  * 台は**実際の ℚ×ℚ**（(a,b) ↔ a + b√D。Bool/Fin/ラベルの身代わりなし）、
    乗法 (a,b)(c,d) = (ac + D·bd, ad + bc) は √D² = D の実現。
  * 逆元は**実ノルム** N(a,b) = a² − D·b² による本物の構成
    (a,b)⁻¹ = (a·N⁻¹, (−b)·N⁻¹)。体公理 `mul_inv_cancel` は
    「D は ℚ で平方でない」witness `hD` から **N の非退化**（(a,b)≠0 ⟹ N≠0）を
    本物に証明して完全証明（b ≠ 0 なら (a/b)² = D で hD と矛盾、の構成的裏返し）。
  * **本丸 `qdf_galois_order_two`**: ℚ を各点固定する自己同型 σ は
    σ(√D)² = σ(D) = D を満たし、2·σ(√D)₁·σ(√D)₂ = 0 と D 非平方から
    σ(√D) = √D または σ(√D) = −√D の**選言を構成的に**得（Int.mul_eq_zero を
    商 ℚ に持ち上げる）、σ は σ(√D) で決まる（x = a + b√D 分解）から
    **σ = id ∨ σ = conj** — Gal(ℚ(√D)/ℚ) の位数はちょうど 2。
  * 実 witness: 負の有理数は ℚ で平方でない（平方非負 + 反対称律）から、
    D = −1・D = −2 で本物の体・本物の位数 2 Galois 群を実例化
    （`qdf_exists` は ℚ(√−2)、M2xxF の ℚ(i) を超える新しい実二次体）。

  * qdf-0 ℚ 側簿記 — mul_left_comm / mul_mul_mul_comm / **積零の選言**
    `qdf_q_mul_eq_zero`（Quot 代表 + Int.mul_eq_zero、choice なし）/
    左簡約 / 2 ≠ 0 / e² = 1 ⟹ e = ±1 / **負数は平方でない** `qdf_neg_not_square`
  * qdf-1 `qdfCarrier`/`qdfAdd`/`qdfMul D`/… — 台は実 ℚ×ℚ、√D 演算
  * qdf-2 `qdfRing D` — ℚ(√D) は可換環（全公理を ℚ の環公理から明示計算）
  * qdf-3 `qdf_norm_ne_zero` — ノルム非退化（hD: D 非平方 ⟹ (a,b)≠0 で N≠0）
  * qdf-4 `qdfField D hD : IUTField` — ℚ(√D) は本物の体
  * qdf-5 `qdfExtension`/`qdfSqrt`/`qdf_sqrt_sq` — 拡大 ℚ ⊂ ℚ(√D) と √D² = D
  * qdf-6 `qdfConj` — 共役 (a,b) ↦ (a,−b)（√D ↦ −√D の体自己同型・ℚ 固定）
  * qdf-7 `qdf_conj_ne_id`/`qdf_galois_nontrivial` — Gal ≠ 1
  * qdf-8 分解補題 `qdf_decompose`/`qdf_apply` — x = a + b√D と σ の決定性
  * qdf-9 **本丸** `qdf_galois_order_two`/`qdf_galoisGroup_order_two`
    — **σ = id ∨ σ = conj（位数ちょうど 2）の完全証明**
  * qdf-10 実例 D = −1, −2 と capstone `qdf_exists`

  正直な限定（何が本物で何が未達か）:
  - **本物**: 台は実際の ℚ×ℚ。逆元は実ノルム逆元。体公理・環公理・拡大・共役・
    Gal 非自明性・**位数ちょうど 2** の全証明は sorry 皆無・新規 Classical.choice
    皆無。σ(√D) = ±√D の選言も、商 ℚ の積零選言を代表の Int.mul_eq_zero から
    構成的に得ており排中律を使わない。
  - **未達（正直申告）**: (1) 正の非平方 D（例 D = 2, 3）の witness `hD` は
    未実例化 — √2∉ℚ 等は整数の無限降下（num² = 2·den² の不可能性）が別切片。
    本モジュールの実例は負の D（−1, −2、一般に任意の負の有理数
    `qdf_neg_not_square`）に限る。一般階梯（qdf-1〜qdf-9）自体は任意の
    非平方 D で成立するので、降下補題が入り次第 D = 2 も同じ定理で閉じる。
    (2) M2xxF の `gaussQField` は乗法を (ac − bd, …) と綴っており、本モジュールの
    `qdfField (−1)` とは定義的に別の（同型な）コピー — 同型による定理輸送は
    未形式化のため、ℚ(i) の位数 2 は本モジュール版 `qdfField (−1)` に対して成立。
    (3) 分離性・正規性・Galois 対応など拡大の一般論は未形式化（位数 2 の主張は
    自己同型の全数え上げとして直接証明）。

  選択公理不使用（新規 choice なし）。禁止タクティク（simp/decide/ring/rcases/
  by_cases/field_simp 等）不使用。
-/
import IUT.GaussianRationalField

namespace IUT

/-! ## qdf-0: ℚ 側の簿記（積の入れ替え・積零選言・左簡約・2≠0・平方根 ±1） -/

/-- 積の左入れ替え a(bc) = b(ac)。 -/
theorem qdf_q_mul_left_comm (a b c : QRat) :
    ratRing.mul a (ratRing.mul b c) = ratRing.mul b (ratRing.mul a c) := by
  rw [← ratRing.mul_assoc a b c, ratRing.mul_comm a b, ratRing.mul_assoc b a c]

/-- 4 因子の入れ替え (ab)(cd) = (ac)(bd)（ratRing 語彙版）。 -/
theorem qdf_q_mul_mul_mul_comm (a b c d : QRat) :
    ratRing.mul (ratRing.mul a b) (ratRing.mul c d)
      = ratRing.mul (ratRing.mul a c) (ratRing.mul b d) := by
  rw [ratRing.mul_assoc a b (ratRing.mul c d), ← ratRing.mul_assoc b c d,
    ratRing.mul_comm b c, ratRing.mul_assoc c b d,
    ← ratRing.mul_assoc a c (ratRing.mul b d)]

/-- **積零の選言（ℚ、構成的）** — uv = 0 ⟹ u = 0 ∨ v = 0。商の代表に降りて
    分子の積零 `Int.mul_eq_zero` の選言を `Quot.sound` で持ち上げる。
    排中律・choice 不使用（Int の選言は決定可能な整数論から）。 -/
theorem qdf_q_mul_eq_zero (u v : QRat) :
    ratRing.mul u v = ratRing.zero → u = ratRing.zero ∨ v = ratRing.zero := by
  induction u using Quot.ind
  rename_i r
  induction v using Quot.ind
  rename_i s
  intro h
  have h2 : Quot.mk ratRel (prMul r s) = Quot.mk ratRel prZero := h
  have h4 : r.num * s.num * 1 = 0 * (r.den * s.den) := quot_exact_rat h2
  rw [Int.mul_one, Int.zero_mul] at h4
  cases Int.mul_eq_zero.mp h4 with
  | inl h6 =>
    apply Or.inl
    show Quot.mk ratRel r = Quot.mk ratRel prZero
    apply Quot.sound
    show r.num * (1 : Int) = 0 * r.den
    rw [h6, Int.zero_mul, Int.zero_mul]
  | inr h6 =>
    apply Or.inr
    show Quot.mk ratRel s = Quot.mk ratRel prZero
    apply Quot.sound
    show s.num * (1 : Int) = 0 * s.den
    rw [h6, Int.zero_mul, Int.zero_mul]

/-- **左簡約** — a ≠ 0 かつ au = av なら u = v（a⁻¹ を左から掛ける）。 -/
theorem qdf_q_mul_left_cancel {a u v : QRat} (ha : a ≠ ratRing.zero)
    (h : ratRing.mul a u = ratRing.mul a v) : u = v := by
  have hinv : ratRing.mul (qInv a) a = ratRing.one :=
    ratIUTField.inv_mul_cancel ha
  have h1 : ratRing.mul (ratRing.mul (qInv a) a) u
      = ratRing.mul (ratRing.mul (qInv a) a) v := by
    rw [ratRing.mul_assoc (qInv a) a u, h, ← ratRing.mul_assoc (qInv a) a v]
  rw [hinv, ratRing.one_mul u, ratRing.one_mul v] at h1
  exact h1

/-- **2 ≠ 0（ℚ）** — 代表の交差積を `quot_exact_rat` で分離し Int に帰着。 -/
theorem qdf_q_two_ne_zero :
    ratRing.add ratRing.one ratRing.one ≠ ratRing.zero := by
  intro h
  have h2 : Quot.mk ratRel (prAdd prOne prOne) = Quot.mk ratRel prZero := h
  have h3 : ((1 : Int) * 1 + 1 * 1) * 1 = 0 * (1 * 1) := quot_exact_rat h2
  omega

/-- 0 ≤ 1（ℚ、代表の Int 不等式）。 -/
theorem qdf_q_zero_le_one : qLe ratRing.zero ratRing.one := by
  show (0 : Int) * 1 ≤ 1 * 1
  omega

/-- 0 ≤ 2（ℚ、代表の Int 不等式）。 -/
theorem qdf_q_zero_le_two :
    qLe ratRing.zero (ratRing.add ratRing.one ratRing.one) := by
  show (0 : Int) * (1 * 1) ≤ ((1 : Int) * 1 + 1 * 1) * 1
  omega

/-- **e² = 1 ⟹ e = 1 ∨ e = −1（ℚ、構成的）** — (e−1)(e+1) = e²−1 = 0 と
    積零選言から。X² = 1 の根の全数え上げ（位数 2 の算術的核心）。 -/
theorem qdf_q_sq_one (e : QRat) (h : ratRing.mul e e = ratRing.one) :
    e = ratRing.one ∨ e = ratRing.neg ratRing.one := by
  have hfactor : ratRing.mul (ratRing.add e (ratRing.neg ratRing.one))
      (ratRing.add e ratRing.one) = ratRing.zero := by
    rw [ratRing.right_distrib e (ratRing.neg ratRing.one)
        (ratRing.add e ratRing.one),
      ratRing.left_distrib e e ratRing.one,
      ratRing.neg_mul ratRing.one (ratRing.add e ratRing.one),
      ratRing.one_mul (ratRing.add e ratRing.one), h,
      ratRing.mul_comm e ratRing.one, ratRing.one_mul e,
      ratRing.add_comm ratRing.one e]
    exact ratRing.add_neg (ratRing.add e ratRing.one)
  cases qdf_q_mul_eq_zero (ratRing.add e (ratRing.neg ratRing.one))
      (ratRing.add e ratRing.one) hfactor with
  | inl h1 =>
    apply Or.inl
    have h2 : ratRing.add (ratRing.add e (ratRing.neg ratRing.one)) ratRing.one
        = ratRing.add ratRing.zero ratRing.one := by rw [h1]
    rw [ratRing.add_assoc e (ratRing.neg ratRing.one) ratRing.one,
      ratRing.neg_add ratRing.one, ratRing.add_zero e,
      ratRing.zero_add ratRing.one] at h2
    exact h2
  | inr h1 =>
    apply Or.inr
    have h2 : ratRing.add (ratRing.add e ratRing.one)
        (ratRing.neg ratRing.one)
        = ratRing.add ratRing.zero (ratRing.neg ratRing.one) := by rw [h1]
    rw [ratRing.add_assoc e ratRing.one (ratRing.neg ratRing.one),
      ratRing.add_neg ratRing.one, ratRing.add_zero e,
      ratRing.zero_add (ratRing.neg ratRing.one)] at h2
    exact h2

/-- **負の有理数は ℚ で平方でない** — 0 ≤ m, m ≠ 0 なら ∀u, u² ≠ −m
    （u² = −m なら平方非負から 0 ≤ −m、両辺に m を足して m ≤ 0、
    反対称律で m = 0 と矛盾）。具体 D = −1, −2, … の witness の源。 -/
theorem qdf_neg_not_square (m : QRat) (hm0 : qLe ratRing.zero m)
    (hmne : m ≠ ratRing.zero) :
    ∀ u : QRat, ratRing.mul u u ≠ ratRing.neg m := by
  intro u h
  have h1 : qLe ratRing.zero (ratRing.mul u u) := gqi_q_sq_nonneg u
  rw [h] at h1
  have h2 : qLe (ratRing.add ratRing.zero m)
      (ratRing.add (ratRing.neg m) m) := gqi_q_le_add m h1
  rw [ratRing.zero_add m, ratRing.neg_add m] at h2
  exact hmne (qLe_antisym m ratRing.zero h2 hm0)

/-! ## qdf-1: 台と √D 演算 — 実 ℚ×ℚ（(a,b) は a + b√D） -/

/-- **qdf-1a: ℚ(√D) の台** — 実際の ℚ×ℚ（第 1 成分 = 有理部、第 2 成分 =
    √D 係数。Bool/Fin/ラベル等の身代わりではない）。 -/
def qdfCarrier : Type := ratIUTField.carrier × ratIUTField.carrier

/-- 対の外延性（成分ごとの等式から）。 -/
theorem qdf_ext : ∀ {x y : qdfCarrier}, x.1 = y.1 → x.2 = y.2 → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

/-- 加法 (a,b)+(c,d) = (a+c, b+d)。 -/
def qdfAdd (x y : qdfCarrier) : qdfCarrier :=
  ((ratRing.add x.1 y.1, ratRing.add x.2 y.2) : qdfCarrier)

/-- 反元 −(a,b) = (−a,−b)。 -/
def qdfNeg (x : qdfCarrier) : qdfCarrier :=
  ((ratRing.neg x.1, ratRing.neg x.2) : qdfCarrier)

/-- 0 = (0,0)。 -/
def qdfZero : qdfCarrier := ((ratRing.zero, ratRing.zero) : qdfCarrier)

/-- 1 = (1,0)。 -/
def qdfOne : qdfCarrier := ((ratRing.one, ratRing.zero) : qdfCarrier)

/-- 平方根 √D = (0,1)。 -/
def qdfSqrt : qdfCarrier := ((ratRing.zero, ratRing.one) : qdfCarrier)

/-- **√D 乗法** (a,b)·(c,d) = (ac + D·bd, ad + bc)（√D² = D の実現）。 -/
def qdfMul (D : QRat) (x y : qdfCarrier) : qdfCarrier :=
  ((ratRing.add (ratRing.mul x.1 y.1) (ratRing.mul D (ratRing.mul x.2 y.2)),
    ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)) : qdfCarrier)

/-- **ノルム** N(a,b) = a² − D·b²（ℚ に値を取る実ノルム）。 -/
def qdfNorm (D : QRat) (x : qdfCarrier) : QRat :=
  ratRing.add (ratRing.mul x.1 x.1)
    (ratRing.neg (ratRing.mul D (ratRing.mul x.2 x.2)))

/-- **実ノルム逆元** (a,b)⁻¹ = (a·N⁻¹, (−b)·N⁻¹)（N⁻¹ は M115F の本物の
    ℚ 逆元 `qInv`。N = 0 のときは qInv 0 = 0 の規約で全域化）。 -/
def qdfInv (D : QRat) (x : qdfCarrier) : qdfCarrier :=
  ((ratRing.mul x.1 (qInv (qdfNorm D x)),
    ratRing.mul (ratRing.neg x.2) (qInv (qdfNorm D x))) : qdfCarrier)

/-! ## qdf-2: ℚ(√D) は可換環（全公理を ℚ の環公理から本物に証明） -/

/-- **qdf-2: ℚ(√D) の可換環構造** — 加法は成分ごと、乗法は √D 則。
    結合・可換・分配は ℚ の環公理（M115F）からの明示計算。 -/
def qdfRing (D : QRat) : CRing where
  carrier := qdfCarrier
  add := qdfAdd
  zero := qdfZero
  neg := qdfNeg
  mul := qdfMul D
  one := qdfOne
  add_assoc := fun x y z =>
    qdf_ext (ratRing.add_assoc x.1 y.1 z.1) (ratRing.add_assoc x.2 y.2 z.2)
  zero_add := fun x =>
    qdf_ext (ratRing.zero_add x.1) (ratRing.zero_add x.2)
  neg_add := fun x =>
    qdf_ext (ratRing.neg_add x.1) (ratRing.neg_add x.2)
  add_comm := fun x y =>
    qdf_ext (ratRing.add_comm x.1 y.1) (ratRing.add_comm x.2 y.2)
  mul_assoc := by
    intro x y z
    apply qdf_ext
    · show ratRing.add
          (ratRing.mul
            (ratRing.add (ratRing.mul x.1 y.1)
              (ratRing.mul D (ratRing.mul x.2 y.2))) z.1)
          (ratRing.mul D
            (ratRing.mul
              (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)) z.2))
        = ratRing.add
          (ratRing.mul x.1
            (ratRing.add (ratRing.mul y.1 z.1)
              (ratRing.mul D (ratRing.mul y.2 z.2))))
          (ratRing.mul D
            (ratRing.mul x.2
              (ratRing.add (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1))))
      rw [ratRing.right_distrib (ratRing.mul x.1 y.1)
          (ratRing.mul D (ratRing.mul x.2 y.2)) z.1,
        ratRing.right_distrib (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1) z.2,
        ratRing.left_distrib D (ratRing.mul (ratRing.mul x.1 y.2) z.2)
          (ratRing.mul (ratRing.mul x.2 y.1) z.2),
        ratRing.left_distrib x.1 (ratRing.mul y.1 z.1)
          (ratRing.mul D (ratRing.mul y.2 z.2)),
        ratRing.left_distrib x.2 (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1),
        ratRing.left_distrib D (ratRing.mul x.2 (ratRing.mul y.1 z.2))
          (ratRing.mul x.2 (ratRing.mul y.2 z.1)),
        ratRing.mul_assoc x.1 y.1 z.1,
        ratRing.mul_assoc D (ratRing.mul x.2 y.2) z.1,
        ratRing.mul_assoc x.2 y.2 z.1,
        ratRing.mul_assoc x.1 y.2 z.2,
        qdf_q_mul_left_comm D x.1 (ratRing.mul y.2 z.2),
        ratRing.mul_assoc x.2 y.1 z.2,
        ratRing.add_add_add_comm (ratRing.mul x.1 (ratRing.mul y.1 z.1))
          (ratRing.mul D (ratRing.mul x.2 (ratRing.mul y.2 z.1)))
          (ratRing.mul x.1 (ratRing.mul D (ratRing.mul y.2 z.2)))
          (ratRing.mul D (ratRing.mul x.2 (ratRing.mul y.1 z.2))),
        ratRing.add_comm (ratRing.mul D (ratRing.mul x.2 (ratRing.mul y.2 z.1)))
          (ratRing.mul D (ratRing.mul x.2 (ratRing.mul y.1 z.2)))]
    · show ratRing.add
          (ratRing.mul
            (ratRing.add (ratRing.mul x.1 y.1)
              (ratRing.mul D (ratRing.mul x.2 y.2))) z.2)
          (ratRing.mul
            (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)) z.1)
        = ratRing.add
          (ratRing.mul x.1
            (ratRing.add (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1)))
          (ratRing.mul x.2
            (ratRing.add (ratRing.mul y.1 z.1)
              (ratRing.mul D (ratRing.mul y.2 z.2))))
      rw [ratRing.right_distrib (ratRing.mul x.1 y.1)
          (ratRing.mul D (ratRing.mul x.2 y.2)) z.2,
        ratRing.right_distrib (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1) z.1,
        ratRing.left_distrib x.1 (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1),
        ratRing.left_distrib x.2 (ratRing.mul y.1 z.1)
          (ratRing.mul D (ratRing.mul y.2 z.2)),
        ratRing.mul_assoc x.1 y.1 z.2,
        ratRing.mul_assoc D (ratRing.mul x.2 y.2) z.2,
        ratRing.mul_assoc x.2 y.2 z.2,
        qdf_q_mul_left_comm D x.2 (ratRing.mul y.2 z.2),
        ratRing.mul_assoc x.1 y.2 z.1,
        ratRing.mul_assoc x.2 y.1 z.1,
        ratRing.add_add_add_comm (ratRing.mul x.1 (ratRing.mul y.1 z.2))
          (ratRing.mul x.2 (ratRing.mul D (ratRing.mul y.2 z.2)))
          (ratRing.mul x.1 (ratRing.mul y.2 z.1))
          (ratRing.mul x.2 (ratRing.mul y.1 z.1)),
        ratRing.add_comm (ratRing.mul x.2 (ratRing.mul D (ratRing.mul y.2 z.2)))
          (ratRing.mul x.2 (ratRing.mul y.1 z.1))]
  one_mul := by
    intro x
    apply qdf_ext
    · show ratRing.add (ratRing.mul ratRing.one x.1)
          (ratRing.mul D (ratRing.mul ratRing.zero x.2)) = x.1
      rw [ratRing.one_mul x.1, ratRing.zero_mul x.2, ratRing.mul_zero D,
        ratRing.add_zero x.1]
    · show ratRing.add (ratRing.mul ratRing.one x.2)
          (ratRing.mul ratRing.zero x.1) = x.2
      rw [ratRing.one_mul x.2, ratRing.zero_mul x.1, ratRing.add_zero x.2]
  mul_comm := by
    intro x y
    apply qdf_ext
    · show ratRing.add (ratRing.mul x.1 y.1)
          (ratRing.mul D (ratRing.mul x.2 y.2))
        = ratRing.add (ratRing.mul y.1 x.1)
          (ratRing.mul D (ratRing.mul y.2 x.2))
      rw [ratRing.mul_comm x.1 y.1, ratRing.mul_comm x.2 y.2]
    · show ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)
        = ratRing.add (ratRing.mul y.1 x.2) (ratRing.mul y.2 x.1)
      rw [ratRing.mul_comm x.1 y.2, ratRing.mul_comm x.2 y.1,
        ratRing.add_comm (ratRing.mul y.2 x.1) (ratRing.mul y.1 x.2)]
  left_distrib := by
    intro x y z
    apply qdf_ext
    · show ratRing.add (ratRing.mul x.1 (ratRing.add y.1 z.1))
          (ratRing.mul D (ratRing.mul x.2 (ratRing.add y.2 z.2)))
        = ratRing.add
          (ratRing.add (ratRing.mul x.1 y.1)
            (ratRing.mul D (ratRing.mul x.2 y.2)))
          (ratRing.add (ratRing.mul x.1 z.1)
            (ratRing.mul D (ratRing.mul x.2 z.2)))
      rw [ratRing.left_distrib x.1 y.1 z.1, ratRing.left_distrib x.2 y.2 z.2,
        ratRing.left_distrib D (ratRing.mul x.2 y.2) (ratRing.mul x.2 z.2),
        ratRing.add_add_add_comm (ratRing.mul x.1 y.1) (ratRing.mul x.1 z.1)
          (ratRing.mul D (ratRing.mul x.2 y.2))
          (ratRing.mul D (ratRing.mul x.2 z.2))]
    · show ratRing.add (ratRing.mul x.1 (ratRing.add y.2 z.2))
          (ratRing.mul x.2 (ratRing.add y.1 z.1))
        = ratRing.add
          (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1))
          (ratRing.add (ratRing.mul x.1 z.2) (ratRing.mul x.2 z.1))
      rw [ratRing.left_distrib x.1 y.2 z.2, ratRing.left_distrib x.2 y.1 z.1,
        ratRing.add_add_add_comm (ratRing.mul x.1 y.2) (ratRing.mul x.1 z.2)
          (ratRing.mul x.2 y.1) (ratRing.mul x.2 z.1)]

/-! ## qdf-3: ノルム非退化 — D 非平方 ⟹ ((a,b) ≠ 0 ⟹ N ≠ 0) -/

/-- **qdf-3: ノルムの非退化性** — D が ℚ で平方でなければ、(a,b) ≠ (0,0) で
    N = a² − D·b² ≠ 0。証明: N = 0 なら a² = D·b²。b ≠ 0 と仮定すると
    (a·b⁻¹)² = D で hD と矛盾 — ゆえ ¬(b ≠ 0)。その二重否定を目標 False に
    向けて構成的に剥がすと b = 0、従って a² = 0、整域性で ¬(a ≠ 0)、
    再び剥がして (a,b) = (0,0) となり仮定と矛盾。choice 不使用。 -/
theorem qdf_norm_ne_zero (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D)
    (x : qdfCarrier) (hx : x ≠ qdfZero) : qdfNorm D x ≠ ratRing.zero := by
  intro hN
  have hN' : ratRing.add (ratRing.mul x.1 x.1)
      (ratRing.neg (ratRing.mul D (ratRing.mul x.2 x.2))) = ratRing.zero := hN
  have hab : ratRing.mul x.1 x.1 = ratRing.mul D (ratRing.mul x.2 x.2) :=
    ratRing.eq_of_sub_eq_zero hN'
  have hb2 : ¬ x.2 ≠ ratRing.zero := by
    intro hb
    have hbc : ratRing.mul x.2 (qInv x.2) = ratRing.one :=
      ratIUTField.mul_inv_cancel x.2 hb
    apply hD (ratRing.mul x.1 (qInv x.2))
    show ratRing.mul (ratRing.mul x.1 (qInv x.2))
        (ratRing.mul x.1 (qInv x.2)) = D
    rw [qdf_q_mul_mul_mul_comm x.1 (qInv x.2) x.1 (qInv x.2), hab,
      ratRing.mul_assoc D (ratRing.mul x.2 x.2)
        (ratRing.mul (qInv x.2) (qInv x.2)),
      qdf_q_mul_mul_mul_comm x.2 x.2 (qInv x.2) (qInv x.2), hbc,
      ratRing.one_mul ratRing.one, ratRing.mul_comm D ratRing.one,
      ratRing.one_mul D]
  apply hb2
  intro hb0
  rw [hb0, ratRing.zero_mul ratRing.zero, ratRing.mul_zero D] at hab
  have ha2 : ¬ x.1 ≠ ratRing.zero := gqi_q_not_ne_of_sq_zero hab
  apply ha2
  intro ha0
  apply hx
  exact qdf_ext ha0 hb0

/-! ## qdf-4: ℚ(√D) は本物の体 -/

/-- **体公理の本体** — x ≠ 0 なら x·x⁻¹ = 1。第 1 成分は
    a·(aN⁻¹) + D·(b·(−bN⁻¹)) = (a² − D·b²)·N⁻¹ = N·N⁻¹ = 1（N ≠ 0 は qdf-3、
    N·N⁻¹ = 1 は M264F の本物の ℚ 体公理）。第 2 成分は
    a·(−bN⁻¹) + b·(aN⁻¹) = −(abN⁻¹) + abN⁻¹ = 0。 -/
theorem qdf_mul_inv_cancel (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D)
    (x : qdfCarrier) (hx : x ≠ qdfZero) :
    qdfMul D x (qdfInv D x) = qdfOne := by
  have hN : qdfNorm D x ≠ ratRing.zero := qdf_norm_ne_zero D hD x hx
  have hcancel : ratRing.mul (qdfNorm D x) (qInv (qdfNorm D x)) = ratRing.one :=
    ratIUTField.mul_inv_cancel (qdfNorm D x) hN
  apply qdf_ext
  · show ratRing.add
        (ratRing.mul x.1 (ratRing.mul x.1 (qInv (qdfNorm D x))))
        (ratRing.mul D
          (ratRing.mul x.2
            (ratRing.mul (ratRing.neg x.2) (qInv (qdfNorm D x)))))
      = ratRing.one
    rw [← ratRing.mul_assoc x.1 x.1 (qInv (qdfNorm D x)),
      ← ratRing.mul_assoc x.2 (ratRing.neg x.2) (qInv (qdfNorm D x)),
      ratRing.mul_neg x.2 x.2,
      ratRing.neg_mul (ratRing.mul x.2 x.2) (qInv (qdfNorm D x)),
      ratRing.mul_neg D (ratRing.mul (ratRing.mul x.2 x.2) (qInv (qdfNorm D x))),
      ← ratRing.mul_assoc D (ratRing.mul x.2 x.2) (qInv (qdfNorm D x)),
      ← ratRing.neg_mul (ratRing.mul D (ratRing.mul x.2 x.2))
        (qInv (qdfNorm D x)),
      ← ratRing.right_distrib (ratRing.mul x.1 x.1)
        (ratRing.neg (ratRing.mul D (ratRing.mul x.2 x.2)))
        (qInv (qdfNorm D x))]
    exact hcancel
  · show ratRing.add
        (ratRing.mul x.1 (ratRing.mul (ratRing.neg x.2) (qInv (qdfNorm D x))))
        (ratRing.mul x.2 (ratRing.mul x.1 (qInv (qdfNorm D x))))
      = ratRing.zero
    rw [← ratRing.mul_assoc x.1 (ratRing.neg x.2) (qInv (qdfNorm D x)),
      ratRing.mul_neg x.1 x.2,
      ratRing.neg_mul (ratRing.mul x.1 x.2) (qInv (qdfNorm D x)),
      ← ratRing.mul_assoc x.2 x.1 (qInv (qdfNorm D x)),
      ratRing.mul_comm x.2 x.1]
    exact ratRing.neg_add (ratRing.mul (ratRing.mul x.1 x.2)
      (qInv (qdfNorm D x)))

/-- 0⁻¹ = 0（成分ごとに 0·_ = 0）。 -/
theorem qdf_inv_zero (D : QRat) : qdfInv D qdfZero = qdfZero := by
  apply qdf_ext
  · show ratRing.mul ratRing.zero (qInv (qdfNorm D qdfZero)) = ratRing.zero
    exact ratRing.zero_mul (qInv (qdfNorm D qdfZero))
  · show ratRing.mul (ratRing.neg ratRing.zero) (qInv (qdfNorm D qdfZero))
      = ratRing.zero
    rw [gqi_q_neg_zero]
    exact ratRing.zero_mul (qInv (qdfNorm D qdfZero))

/-- (0,0) ≠ (1,0)（第 1 成分で ℚ の 0 ≠ 1 に帰着）。 -/
theorem qdf_zero_ne_one : qdfZero ≠ qdfOne := by
  intro h
  have h1 : ratRing.zero = ratRing.one :=
    congrArg (fun p : qdfCarrier => p.1) h
  exact ratIUTField.zero_ne_one h1

/-- **qdf-4: ℚ(√D) は本物の体** — 台は実 ℚ×ℚ、逆元は実ノルム逆元、
    体公理は D 非平方 witness から完全証明。 -/
def qdfField (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D) : IUTField where
  toCRing := qdfRing D
  inv := qdfInv D
  mul_inv_cancel := qdf_mul_inv_cancel D hD
  inv_zero := qdf_inv_zero D
  zero_ne_one := qdf_zero_ne_one

/-! ## qdf-5: 非自明拡大 ℚ ⊂ ℚ(√D) と √D² = D -/

/-- **qdf-5a: 体拡大 ℚ ⊂ ℚ(√D)** — 埋め込み a ↦ (a,0) は環準同型。 -/
def qdfExtension (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D) :
    FieldExtension where
  base := ratIUTField
  top := qdfField D hD
  incl := fun a => ((a, ratRing.zero) : qdfCarrier)
  incl_add := fun a b => by
    apply qdf_ext
    · exact rfl
    · show ratRing.zero = ratRing.add ratRing.zero ratRing.zero
      exact (ratRing.zero_add ratRing.zero).symm
  incl_mul := fun a b => by
    apply qdf_ext
    · show ratRing.mul a b
        = ratRing.add (ratRing.mul a b)
          (ratRing.mul D (ratRing.mul ratRing.zero ratRing.zero))
      rw [ratRing.zero_mul ratRing.zero, ratRing.mul_zero D,
        ratRing.add_zero (ratRing.mul a b)]
    · show ratRing.zero
        = ratRing.add (ratRing.mul a ratRing.zero) (ratRing.mul ratRing.zero b)
      rw [ratRing.mul_zero a, ratRing.zero_mul b,
        ratRing.zero_add ratRing.zero]
  incl_one := rfl

/-- **qdf-5b: √D² = D** — (0,1)·(0,1) = (D,0) = incl D（√D は本物に D の
    平方根）。σ(√D) の 2 択の出発点。 -/
theorem qdf_sqrt_sq (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D) :
    (qdfField D hD).mul qdfSqrt qdfSqrt = (qdfExtension D hD).incl D := by
  apply qdf_ext
  · show ratRing.add (ratRing.mul ratRing.zero ratRing.zero)
        (ratRing.mul D (ratRing.mul ratRing.one ratRing.one)) = D
    rw [ratRing.zero_mul ratRing.zero, ratRing.one_mul ratRing.one,
      ratRing.mul_comm D ratRing.one, ratRing.one_mul D, ratRing.zero_add D]
  · show ratRing.add (ratRing.mul ratRing.zero ratRing.one)
        (ratRing.mul ratRing.one ratRing.zero) = ratRing.zero
    rw [ratRing.zero_mul ratRing.one, ratRing.one_mul ratRing.zero,
      ratRing.zero_add ratRing.zero]

/-! ## qdf-6: 共役 √D ↦ −√D は ℚ(√D) の体自己同型で ℚ を各点固定 -/

/-- **qdf-6: 共役** σ(a,b) = (a,−b) — ℚ(√D) の本物の体自己同型
    （加法・乗法・1 を保ち、自身が明示逆写像の対合）。乗法の保存は
    (−b)(−d) = bd（√D² = D と整合する本物の内容）。 -/
def qdfConj (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D) :
    FieldAut (qdfField D hD) where
  toFun := fun x => ((x.1, ratRing.neg x.2) : qdfCarrier)
  invFun := fun x => ((x.1, ratRing.neg x.2) : qdfCarrier)
  map_add := fun x y => by
    apply qdf_ext
    · exact rfl
    · show ratRing.neg (ratRing.add x.2 y.2)
        = ratRing.add (ratRing.neg x.2) (ratRing.neg y.2)
      exact ratRing.neg_add_dist x.2 y.2
  map_mul := fun x y => by
    apply qdf_ext
    · show ratRing.add (ratRing.mul x.1 y.1)
          (ratRing.mul D (ratRing.mul x.2 y.2))
        = ratRing.add (ratRing.mul x.1 y.1)
          (ratRing.mul D (ratRing.mul (ratRing.neg x.2) (ratRing.neg y.2)))
      rw [ratRing.neg_mul x.2 (ratRing.neg y.2), ratRing.mul_neg x.2 y.2,
        ratRing.neg_neg (ratRing.mul x.2 y.2)]
    · show ratRing.neg (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1))
        = ratRing.add (ratRing.mul x.1 (ratRing.neg y.2))
          (ratRing.mul (ratRing.neg x.2) y.1)
      rw [ratRing.neg_add_dist (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1),
        ratRing.mul_neg x.1 y.2, ratRing.neg_mul x.2 y.1]
  map_one := by
    apply qdf_ext
    · exact rfl
    · show ratRing.neg ratRing.zero = ratRing.zero
      exact gqi_q_neg_zero
  left_inv := fun x => by
    apply qdf_ext
    · exact rfl
    · show ratRing.neg (ratRing.neg x.2) = x.2
      exact ratRing.neg_neg x.2
  right_inv := fun x => by
    apply qdf_ext
    · exact rfl
    · show ratRing.neg (ratRing.neg x.2) = x.2
      exact ratRing.neg_neg x.2

/-- **共役は ℚ を各点固定** — conj(a,0) = (a,−0) = (a,0)。 -/
theorem qdf_conj_fixes_base (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D)
    (k : QRat) :
    (qdfConj D hD).toFun ((qdfExtension D hD).incl k)
      = (qdfExtension D hD).incl k := by
  apply qdf_ext
  · exact rfl
  · show ratRing.neg ratRing.zero = ratRing.zero
    exact gqi_q_neg_zero

/-- **conj ∈ Gal(ℚ(√D)/ℚ)**（M271F-4 の Galois 部分群の membership）。 -/
theorem qdf_conj_mem_galois (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D) :
    (galoisSubgroup (qdfExtension D hD)).mem (qdfConj D hD) := by
  intro k
  exact qdf_conj_fixes_base D hD k

/-! ## qdf-7: Gal(ℚ(√D)/ℚ) は非自明 -/

/-- **qdf-7a: conj ≠ id** — conj(√D) = (0,−1) ≠ (0,1) = √D（第 2 成分で
    ℚ の −1 ≠ 1 に帰着）。 -/
theorem qdf_conj_ne_id (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D) :
    qdfConj D hD ≠ fieldAutId (qdfField D hD) := by
  intro h
  have h1 : (qdfConj D hD).toFun qdfSqrt
      = (fieldAutId (qdfField D hD)).toFun qdfSqrt := by rw [h]
  have h2 : ratRing.neg ratRing.one = ratRing.one :=
    congrArg (fun p : qdfCarrier => p.2) h1
  exact gqi_q_neg_one_ne_one h2

/-- **qdf-7b: Gal(ℚ(√D)/ℚ) は非自明**。 -/
theorem qdf_galois_nontrivial (D : QRat)
    (hD : ∀ u : QRat, ratRing.mul u u ≠ D) :
    ∃ σ : FieldAut (qdfField D hD),
      (galoisSubgroup (qdfExtension D hD)).mem σ
        ∧ σ ≠ fieldAutId (qdfField D hD) :=
  ⟨qdfConj D hD, qdf_conj_mem_galois D hD, qdf_conj_ne_id D hD⟩

/-! ## qdf-8: 分解補題 — x = a + b√D と「σ は σ(√D) で決まる」 -/

/-- **qdf-8a: 分解** (a,b) = incl a + incl b · √D（ℚ(√D) は ℚ 上 {1, √D}
    で張られる — 2 次拡大の実体）。 -/
theorem qdf_decompose (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D)
    (a b : QRat) :
    ((a, b) : qdfCarrier)
      = (qdfField D hD).add ((qdfExtension D hD).incl a)
        ((qdfField D hD).mul ((qdfExtension D hD).incl b) qdfSqrt) := by
  apply qdf_ext
  · show a = ratRing.add a (ratRing.add (ratRing.mul b ratRing.zero)
        (ratRing.mul D (ratRing.mul ratRing.zero ratRing.one)))
    rw [ratRing.mul_zero b, ratRing.zero_mul ratRing.one, ratRing.mul_zero D,
      ratRing.zero_add ratRing.zero, ratRing.add_zero a]
  · show b = ratRing.add ratRing.zero
        (ratRing.add (ratRing.mul b ratRing.one)
          (ratRing.mul ratRing.zero ratRing.zero))
    rw [ratRing.mul_comm b ratRing.one, ratRing.one_mul b,
      ratRing.zero_mul ratRing.zero, ratRing.add_zero b, ratRing.zero_add b]

/-- **qdf-8b: 共役側の分解** incl a + incl b · (0,−1) = (a,−b)
    （σ(√D) = −√D のとき σ = conj を出す計算核）。 -/
theorem qdf_decompose_conj (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D)
    (a b : QRat) :
    (qdfField D hD).add ((qdfExtension D hD).incl a)
      ((qdfField D hD).mul ((qdfExtension D hD).incl b)
        ((ratRing.zero, ratRing.neg ratRing.one) : qdfCarrier))
      = ((a, ratRing.neg b) : qdfCarrier) := by
  apply qdf_ext
  · show ratRing.add a (ratRing.add (ratRing.mul b ratRing.zero)
        (ratRing.mul D (ratRing.mul ratRing.zero (ratRing.neg ratRing.one))))
      = a
    rw [ratRing.mul_zero b, ratRing.zero_mul (ratRing.neg ratRing.one),
      ratRing.mul_zero D, ratRing.zero_add ratRing.zero, ratRing.add_zero a]
  · show ratRing.add ratRing.zero
        (ratRing.add (ratRing.mul b (ratRing.neg ratRing.one))
          (ratRing.mul ratRing.zero ratRing.zero))
      = ratRing.neg b
    rw [ratRing.mul_neg b ratRing.one, ratRing.mul_comm b ratRing.one,
      ratRing.one_mul b, ratRing.zero_mul ratRing.zero,
      ratRing.add_zero (ratRing.neg b), ratRing.zero_add (ratRing.neg b)]

/-- **qdf-8c: σ は σ(√D) で決まる** — ℚ を各点固定する σ に対し
    σ(a,b) = incl a + incl b · σ(√D)（加法性・乗法性・基底固定から）。 -/
theorem qdf_apply (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D)
    (σ : FieldAut (qdfField D hD))
    (hσ : (galoisSubgroup (qdfExtension D hD)).mem σ) (a b : QRat) :
    σ.toFun ((a, b) : qdfCarrier)
      = (qdfField D hD).add ((qdfExtension D hD).incl a)
        ((qdfField D hD).mul ((qdfExtension D hD).incl b)
          (σ.toFun qdfSqrt)) := by
  rw [qdf_decompose D hD a b,
    σ.map_add ((qdfExtension D hD).incl a)
      ((qdfField D hD).mul ((qdfExtension D hD).incl b) qdfSqrt),
    σ.map_mul ((qdfExtension D hD).incl b) qdfSqrt, hσ a, hσ b]

/-! ## qdf-9: 本丸 — Gal(ℚ(√D)/ℚ) の位数はちょうど 2 -/

/-- **qdf-9a（本丸）: Gal(ℚ(√D)/ℚ) は id と conj のみ** — ℚ を各点固定する
    自己同型 σ は σ = id または σ = conj。証明: t := σ(√D) は t² = σ(D) = D を
    満たす。成分計算で t₁² + D·t₂² = D かつ 2·t₁t₂ = 0。2 ≠ 0 と整域性から
    t₁t₂ = 0、積零選言（構成的）で t₁ = 0 か t₂ = 0。t₂ = 0 なら t₁² = D で
    D 非平方に矛盾。t₁ = 0 なら D·t₂² = D、D ≠ 0（D 非平方ゆえ）で左簡約して
    t₂² = 1、根の数え上げで t₂ = ±1、すなわち t = ±√D。t = √D なら分解補題で
    σ = id、t = −√D なら σ = conj。**M2xxF（ℚ(i)）が正直申告で残した
    「位数ちょうど 2」を一般 D で閉じる**。 -/
theorem qdf_galois_order_two (D : QRat) (hD : ∀ u : QRat, ratRing.mul u u ≠ D)
    (σ : FieldAut (qdfField D hD))
    (hσ : (galoisSubgroup (qdfExtension D hD)).mem σ) :
    σ = fieldAutId (qdfField D hD) ∨ σ = qdfConj D hD := by
  have hsq : (qdfField D hD).mul (σ.toFun qdfSqrt) (σ.toFun qdfSqrt)
      = (qdfExtension D hD).incl D := by
    rw [← σ.map_mul qdfSqrt qdfSqrt, qdf_sqrt_sq D hD, hσ D]
  have c1 : ratRing.add
      (ratRing.mul (σ.toFun qdfSqrt).1 (σ.toFun qdfSqrt).1)
      (ratRing.mul D
        (ratRing.mul (σ.toFun qdfSqrt).2 (σ.toFun qdfSqrt).2)) = D :=
    congrArg (fun p : qdfCarrier => p.1) hsq
  have c2 : ratRing.add
      (ratRing.mul (σ.toFun qdfSqrt).1 (σ.toFun qdfSqrt).2)
      (ratRing.mul (σ.toFun qdfSqrt).2 (σ.toFun qdfSqrt).1) = ratRing.zero :=
    congrArg (fun p : qdfCarrier => p.2) hsq
  rw [ratRing.mul_comm (σ.toFun qdfSqrt).2 (σ.toFun qdfSqrt).1] at c2
  have c2' : ratRing.mul (ratRing.add ratRing.one ratRing.one)
      (ratRing.mul (σ.toFun qdfSqrt).1 (σ.toFun qdfSqrt).2) = ratRing.zero := by
    rw [ratRing.right_distrib ratRing.one ratRing.one
        (ratRing.mul (σ.toFun qdfSqrt).1 (σ.toFun qdfSqrt).2),
      ratRing.one_mul (ratRing.mul (σ.toFun qdfSqrt).1 (σ.toFun qdfSqrt).2)]
    exact c2
  have ht12 : ratRing.mul (σ.toFun qdfSqrt).1 (σ.toFun qdfSqrt).2
      = ratRing.zero :=
    ratIUTField.eq_zero_of_mul_eq_zero_left c2' qdf_q_two_ne_zero
  cases qdf_q_mul_eq_zero (σ.toFun qdfSqrt).1 (σ.toFun qdfSqrt).2 ht12 with
  | inr ht2 =>
    rw [ht2, ratRing.zero_mul ratRing.zero, ratRing.mul_zero D,
      ratRing.add_zero (ratRing.mul (σ.toFun qdfSqrt).1 (σ.toFun qdfSqrt).1)]
      at c1
    exact absurd c1 (hD (σ.toFun qdfSqrt).1)
  | inl ht1 =>
    rw [ht1, ratRing.zero_mul ratRing.zero,
      ratRing.zero_add (ratRing.mul D
        (ratRing.mul (σ.toFun qdfSqrt).2 (σ.toFun qdfSqrt).2))] at c1
    have hDne : D ≠ ratRing.zero := by
      intro hD0
      apply hD ratRing.zero
      rw [ratRing.zero_mul ratRing.zero]
      exact hD0.symm
    have c1' : ratRing.mul D
        (ratRing.mul (σ.toFun qdfSqrt).2 (σ.toFun qdfSqrt).2)
        = ratRing.mul D ratRing.one := by
      rw [ratRing.mul_comm D ratRing.one, ratRing.one_mul D]
      exact c1
    have ht2sq : ratRing.mul (σ.toFun qdfSqrt).2 (σ.toFun qdfSqrt).2
        = ratRing.one := qdf_q_mul_left_cancel hDne c1'
    cases qdf_q_sq_one (σ.toFun qdfSqrt).2 ht2sq with
    | inl ht2 =>
      apply Or.inl
      have hts : σ.toFun qdfSqrt = qdfSqrt := qdf_ext ht1 ht2
      have htofun : ∀ x : qdfCarrier, σ.toFun x = x := by
        intro x
        have h1 := qdf_apply D hD σ hσ x.1 x.2
        rw [hts, ← qdf_decompose D hD x.1 x.2] at h1
        exact h1
      apply FieldAut.ext
      · funext x
        exact htofun x
      · funext x
        have h := σ.left_inv x
        rw [htofun x] at h
        exact h
    | inr ht2 =>
      apply Or.inr
      have hts : σ.toFun qdfSqrt
          = ((ratRing.zero, ratRing.neg ratRing.one) : qdfCarrier) :=
        qdf_ext ht1 ht2
      have htofun : ∀ x : qdfCarrier,
          σ.toFun x = ((x.1, ratRing.neg x.2) : qdfCarrier) := by
        intro x
        have h1 := qdf_apply D hD σ hσ x.1 x.2
        rw [hts, qdf_decompose_conj D hD x.1 x.2] at h1
        exact h1
      apply FieldAut.ext
      · funext x
        exact htofun x
      · funext x
        have h2 := htofun ((x.1, ratRing.neg x.2) : qdfCarrier)
        have h3 : σ.toFun ((x.1, ratRing.neg x.2) : qdfCarrier)
            = ((x.1, x.2) : qdfCarrier) := by
          rw [h2]
          apply qdf_ext
          · exact rfl
          · show ratRing.neg (ratRing.neg x.2) = x.2
            exact ratRing.neg_neg x.2
        have h4 := σ.left_inv ((x.1, ratRing.neg x.2) : qdfCarrier)
        rw [h3] at h4
        exact h4

/-- **qdf-9b: 群としての位数ちょうど 2** — Gal(ℚ(√D)/ℚ) を M271F-5 の群
    `galoisGroupGrp` として見たとき、単位元と異なる元 g（共役）が存在し、
    **すべての元は単位元か g** — 位数 2 の群の完全な特徴づけ。 -/
theorem qdf_galoisGroup_order_two (D : QRat)
    (hD : ∀ u : QRat, ratRing.mul u u ≠ D) :
    ∃ g : (galoisGroupGrp (qdfExtension D hD)).carrier,
      g ≠ (galoisGroupGrp (qdfExtension D hD)).one ∧
      ∀ h : (galoisGroupGrp (qdfExtension D hD)).carrier,
        h = (galoisGroupGrp (qdfExtension D hD)).one ∨ h = g := by
  refine ⟨⟨qdfConj D hD, qdf_conj_mem_galois D hD⟩, ?_, ?_⟩
  · intro h
    have h1 : qdfConj D hD = fieldAutId (qdfField D hD) :=
      congrArg Subtype.val h
    exact qdf_conj_ne_id D hD h1
  · intro g
    cases qdf_galois_order_two D hD g.val g.property with
    | inl h1 =>
      apply Or.inl
      apply Subtype.ext
      exact h1
    | inr h1 =>
      apply Or.inr
      apply Subtype.ext
      exact h1

/-! ## qdf-10: 実 witness（D = −1, −2）と capstone -/

/-- **D = −1 は ℚ で平方でない**（負数非平方の実例 1 — 本モジュール版 ℚ(i) の
    witness。M2xxF の gaussQField とは乗法の綴りが異なる同型コピー — 正直申告）。 -/
theorem qdf_negOne_not_square :
    ∀ u : QRat, ratRing.mul u u ≠ ratRing.neg ratRing.one :=
  qdf_neg_not_square ratRing.one qdf_q_zero_le_one ratIUTField.one_ne_zero

/-- −2（√−2 の被開平数）。 -/
def qdfNegTwo : QRat := ratRing.neg (ratRing.add ratRing.one ratRing.one)

/-- **D = −2 は ℚ で平方でない**（実例 2 — ℚ(i) を超える新しい二次体
    ℚ(√−2) の witness）。 -/
theorem qdfNegTwo_not_square : ∀ u : QRat, ratRing.mul u u ≠ qdfNegTwo :=
  qdf_neg_not_square (ratRing.add ratRing.one ratRing.one)
    qdf_q_zero_le_two qdf_q_two_ne_zero

/-- **本物の二次体 ℚ(√−2)**（実台 ℚ×ℚ・実ノルム逆元・体公理完全証明）。 -/
def qdfFieldNegTwo : IUTField := qdfField qdfNegTwo qdfNegTwo_not_square

/-- **本物の拡大 ℚ ⊂ ℚ(√−2)**。 -/
def qdfExtensionNegTwo : FieldExtension :=
  qdfExtension qdfNegTwo qdfNegTwo_not_square

/-- **ℚ(√−2)/ℚ の Galois 群は位数ちょうど 2**（qdf-9a の実例化）。 -/
theorem qdfNegTwo_galois_order_two
    (σ : FieldAut (qdfField qdfNegTwo qdfNegTwo_not_square))
    (hσ : (galoisSubgroup (qdfExtension qdfNegTwo qdfNegTwo_not_square)).mem σ) :
    σ = fieldAutId (qdfField qdfNegTwo qdfNegTwo_not_square)
      ∨ σ = qdfConj qdfNegTwo qdfNegTwo_not_square :=
  qdf_galois_order_two qdfNegTwo qdfNegTwo_not_square σ hσ

/-- **本モジュール版 ℚ(i) = ℚ(√−1) の Galois 群も位数ちょうど 2**
    （M2xxF が未達と申告した点の、qdfField (−1) 版での閉鎖）。 -/
theorem qdfNegOne_galois_order_two
    (σ : FieldAut (qdfField (ratRing.neg ratRing.one) qdf_negOne_not_square))
    (hσ : (galoisSubgroup
      (qdfExtension (ratRing.neg ratRing.one) qdf_negOne_not_square)).mem σ) :
    σ = fieldAutId (qdfField (ratRing.neg ratRing.one) qdf_negOne_not_square)
      ∨ σ = qdfConj (ratRing.neg ratRing.one) qdf_negOne_not_square :=
  qdf_galois_order_two (ratRing.neg ratRing.one) qdf_negOne_not_square σ hσ

/-- **qdf-10 capstone: 位数ちょうど 2 の Galois 群を持つ本物の体拡大が存在**
    — witness は ℚ ⊂ ℚ(√−2) と共役 σ: 非自明（σ ≠ id）で、ℚ を固定する
    自己同型は id と σ で全部。 -/
theorem qdf_exists :
    ∃ E : FieldExtension, ∃ σ : FieldAut E.top,
      (galoisSubgroup E).mem σ ∧ σ ≠ fieldAutId E.top ∧
      ∀ τ : FieldAut E.top, (galoisSubgroup E).mem τ →
        τ = fieldAutId E.top ∨ τ = σ :=
  ⟨qdfExtension qdfNegTwo qdfNegTwo_not_square,
   qdfConj qdfNegTwo qdfNegTwo_not_square,
   qdf_conj_mem_galois qdfNegTwo qdfNegTwo_not_square,
   qdf_conj_ne_id qdfNegTwo qdfNegTwo_not_square,
   fun τ hτ => qdf_galois_order_two qdfNegTwo qdfNegTwo_not_square τ hτ⟩

end IUT
