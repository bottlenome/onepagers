/-
  IUT/GaussianRationalField.lean — M2xxF: ガウス有理数体 ℚ(i) と非自明 Galois 群
  Gal(ℚ(i)/ℚ) ∋ 複素共役 — 柱A 実 Galois 塔の根元（§2(b) 本物建設）

  ── 主要成果の分類: **[実]**（本物の非自明有限次拡大 ℚ ⊂ ℚ(i) と、その上の
  本物の非自明 Galois 群の実例）。

  complete_pct 影響: **柱A 実 Galois 群論の根元欠落（監査名指し）を埋める本物建設**。
  これまでコードベースの全 Galois 塔は `trivialExtension`（Gal = 1）詰めで、
  「非自明有限体拡大 + 実 Galois 群」が 1 つも存在しなかった。本モジュールは
  **本物の体 ℚ(i)** を実台 ℚ×ℚ（(a,b) ↔ a+bi）上に構成し、
  * 逆元は**実ガウス逆元** (a,b)⁻¹ = (a·N⁻¹, (−b)·N⁻¹), N = a²+b²、
  * 体公理 `mul_inv_cancel` は **ℚ の順序（形式的実性: a²+b²=0 ⟹ a=b=0）**から
    本物に証明、
  * 非自明拡大 `gqiExtension : ℚ ⊂ ℚ(i)`（a ↦ (a,0) は環準同型埋め込み）、
  * 複素共役 `gqiConj : (a,b) ↦ (a,−b)` が ℚ(i) の体自己同型で ℚ を各点固定、
  * **本丸**: `gqi_conj_ne_id`（conj(i) = −i ≠ i、∵ ℚ で −1 ≠ 1）と
    `gqi_galois_nontrivial`（**Gal(ℚ(i)/ℚ) は非自明**: ∃σ∈Gal, σ≠id）
  を完全証明する。既存の実 Galois 機構（M271F `FieldAut`/`FieldExtension`/
  `galoisSubgroup`）の上に、初の非自明実例を建てる。

  * gqi-1 `gqiCarrier`/`gqiAdd`/`gqiMul`/… — 台は実 ℚ×ℚ、ガウス演算
  * gqi-2 `gqiRing` — ℚ(i) は可換環（結合・可換・分配を ℚ の環公理から）
  * gqi-3 `gqi_normsq_ne_zero` — 形式的実性 (a,b)≠(0,0) ⟹ a²+b²≠0
    （ℚ の順序 M115F-5: 平方非負 + 反対称律 + 整域性から）
  * gqi-4 `gaussQField : IUTField` — ℚ(i) は本物の体（実ガウス逆元で
    mul_inv_cancel を本物証明・inv_zero・zero_ne_one）
  * gqi-5 `gqiExtension : FieldExtension` — 非自明拡大 ℚ ⊂ ℚ(i)
  * gqi-6 `gqiConj : FieldAut gaussQField` — 複素共役（環準同型・対合）と
    `gqi_conj_mem_galois`（ℚ を各点固定 ⟹ conj ∈ Gal(ℚ(i)/ℚ)）
  * gqi-7 `gqi_conj_ne_id`/`gqi_galois_nontrivial`/`gqi_galoisGroup_nontrivial`
    — **Gal(ℚ(i)/ℚ) ≠ 1 の完全証明**
  * gqi-8 capstone `gqi_exists`

  正直な限定（何が本物で何が未達か）:
  - **本物**: 台 ℚ×ℚ は実際の有理数対（Bool/Fin/ラベルの身代わりなし）。
    逆元は実ガウス逆元で、体公理・環公理・拡大・共役・Gal 非自明性の全証明は
    sorry 皆無・新規 Classical.choice 皆無（propext/Quot.sound のみ）。
  - **未達（正直申告）**: (1) Gal(ℚ(i)/ℚ) ≅ ℤ/2（位数がちょうど 2、すなわち
    「id と conj で全部」）は未証明 — σ(i)² = −1 から σ(i) = ±i を導く因数分解
    論法（X²+1 の根の分類）が別切片。本モジュールは「非自明元の存在」まで。
    (2) 分離性・正規性など Galois 拡大の性質論は未形式化。
    (3) 商 ℚ 上のゼロ判定選言は排中律を要するため、非零性は常に仮説形/否定形で扱う
    （形式的実性補題は「N=0 と (a,b)≠0 の矛盾」として二重否定経由で構成的に証明）。

  選択公理不使用（新規 choice なし）。禁止タクティク（simp/decide/ring 等）不使用。
-/
import IUT.FieldAutGroup
import IUT.LubinTateZp

namespace IUT

/-! ## gqi-0: ℚ 側の簿記（順序と符号、全て既存 M115F API から） -/

/-- −0 = 0（ℚ、`CRing.add_neg` と `zero_add` から）。 -/
theorem gqi_q_neg_zero : ratRing.neg ratRing.zero = ratRing.zero := by
  have h := CRing.add_neg ratRing ratRing.zero
  rw [ratRing.zero_add] at h
  exact h

/-- ℚ の順序と加法の両立（`qLe_add` の ratRing 語彙版）。 -/
theorem gqi_q_le_add {a b : QRat} (c : QRat) (h : qLe a b) :
    qLe (ratRing.add a c) (ratRing.add b c) :=
  qLe_add a b c h

/-- ℚ の非負積閉性（`qLe_mul_nonneg` の ratRing 語彙版）。 -/
theorem gqi_q_mul_nonneg (a b : QRat) (ha : qLe ratRing.zero a)
    (hb : qLe ratRing.zero b) : qLe ratRing.zero (ratRing.mul a b) :=
  qLe_mul_nonneg a b ha hb

/-- **平方非負** 0 ≤ a²（全順序 `qLe_total` の Or 場合分け: a ≥ 0 なら積閉性、
    a ≤ 0 なら 0 ≤ −a と (−a)² = a²）。 -/
theorem gqi_q_sq_nonneg (a : QRat) : qLe ratRing.zero (ratRing.mul a a) := by
  cases qLe_total ratRing.zero a with
  | inl h => exact gqi_q_mul_nonneg a a h h
  | inr h =>
    have h1 : qLe (ratRing.add a (ratRing.neg a))
        (ratRing.add ratRing.zero (ratRing.neg a)) :=
      gqi_q_le_add (ratRing.neg a) h
    rw [ratRing.add_neg a, ratRing.zero_add (ratRing.neg a)] at h1
    have h2 : qLe ratRing.zero (ratRing.mul (ratRing.neg a) (ratRing.neg a)) :=
      gqi_q_mul_nonneg (ratRing.neg a) (ratRing.neg a) h1 h1
    rw [ratRing.neg_mul a (ratRing.neg a), ratRing.mul_neg a a,
      ratRing.neg_neg (ratRing.mul a a)] at h2
    exact h2

/-- **形式的実性（左）** a²+b² = 0 ⟹ a² = 0（a² は 0 と a²+b² に挟まれ、
    反対称律で 0）。 -/
theorem gqi_q_sq_eq_zero_left {a b : QRat}
    (h : ratRing.add (ratRing.mul a a) (ratRing.mul b b) = ratRing.zero) :
    ratRing.mul a a = ratRing.zero := by
  have h1 := gqi_q_sq_nonneg a
  have h2 := gqi_q_sq_nonneg b
  have h3 : qLe (ratRing.add ratRing.zero (ratRing.mul a a))
      (ratRing.add (ratRing.mul b b) (ratRing.mul a a)) :=
    gqi_q_le_add (ratRing.mul a a) h2
  rw [ratRing.zero_add (ratRing.mul a a),
    ratRing.add_comm (ratRing.mul b b) (ratRing.mul a a), h] at h3
  exact qLe_antisym (ratRing.mul a a) ratRing.zero h3 h1

/-- **形式的実性（右）** a²+b² = 0 ⟹ b² = 0。 -/
theorem gqi_q_sq_eq_zero_right {a b : QRat}
    (h : ratRing.add (ratRing.mul a a) (ratRing.mul b b) = ratRing.zero) :
    ratRing.mul b b = ratRing.zero := by
  rw [ratRing.add_comm (ratRing.mul a a) (ratRing.mul b b)] at h
  exact gqi_q_sq_eq_zero_left h

/-- a² = 0 ⟹ ¬(a ≠ 0)（ℚ の整域性 M264F-3。商 ℚ のゼロ判定選言は排中律を
    要するため、構成的に到達できる二重否定形で述べる — 正直申告）。 -/
theorem gqi_q_not_ne_of_sq_zero {a : QRat}
    (h : ratRing.mul a a = ratRing.zero) : ¬ a ≠ ratRing.zero := by
  intro hne
  exact hne (ratIUTField.eq_zero_of_mul_eq_zero_left h hne)

/-- **−1 ≠ 1（ℚ）** — 代表の交差積を `quot_exact_rat` で分離し Int の
    −1 ≠ 1 に帰着。conj ≠ id の算術的核心。 -/
theorem gqi_q_neg_one_ne_one : ratRing.neg ratRing.one ≠ ratRing.one := by
  intro h
  have h2 : Quot.mk ratRel (prNeg prOne) = Quot.mk ratRel prOne := h
  have h3 : (-1 : Int) * 1 = 1 * 1 := quot_exact_rat h2
  omega

/-! ## gqi-1: 台とガウス演算 — 実 ℚ×ℚ（(a,b) は a+bi） -/

/-- **gqi-1a: ℚ(i) の台** — 実際の ℚ×ℚ（第 1 成分 = 実部、第 2 成分 = 虚部。
    Bool/Fin/ラベル等の身代わりではない）。 -/
def gqiCarrier : Type := ratIUTField.carrier × ratIUTField.carrier

/-- 対の外延性（成分ごとの等式から）。 -/
theorem gqi_ext : ∀ {x y : gqiCarrier}, x.1 = y.1 → x.2 = y.2 → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

/-- 加法 (a,b)+(c,d) = (a+c, b+d)。 -/
def gqiAdd (x y : gqiCarrier) : gqiCarrier :=
  ((ratRing.add x.1 y.1, ratRing.add x.2 y.2) : gqiCarrier)

/-- 反元 −(a,b) = (−a,−b)。 -/
def gqiNeg (x : gqiCarrier) : gqiCarrier :=
  ((ratRing.neg x.1, ratRing.neg x.2) : gqiCarrier)

/-- 0 = (0,0)。 -/
def gqiZero : gqiCarrier := ((ratRing.zero, ratRing.zero) : gqiCarrier)

/-- 1 = (1,0)。 -/
def gqiOne : gqiCarrier := ((ratRing.one, ratRing.zero) : gqiCarrier)

/-- 虚数単位 i = (0,1)。 -/
def gqiI : gqiCarrier := ((ratRing.zero, ratRing.one) : gqiCarrier)

/-- **ガウス乗法** (a,b)·(c,d) = (ac−bd, ad+bc)（i² = −1 の実現）。 -/
def gqiMul (x y : gqiCarrier) : gqiCarrier :=
  ((ratRing.add (ratRing.mul x.1 y.1) (ratRing.neg (ratRing.mul x.2 y.2)),
    ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)) : gqiCarrier)

/-- **ノルム** N(a,b) = a²+b²（ℚ に値を取る実ノルム）。 -/
def gqiNorm (x : gqiCarrier) : QRat :=
  ratRing.add (ratRing.mul x.1 x.1) (ratRing.mul x.2 x.2)

/-- **実ガウス逆元** (a,b)⁻¹ = (a·N⁻¹, (−b)·N⁻¹)（N⁻¹ は M115F の本物の
    ℚ 逆元 `qInv`。N = 0 のときは qInv 0 = 0 の規約で全域化）。 -/
def gqiInv (x : gqiCarrier) : gqiCarrier :=
  ((ratRing.mul x.1 (qInv (gqiNorm x)),
    ratRing.mul (ratRing.neg x.2) (qInv (gqiNorm x))) : gqiCarrier)

/-! ## gqi-2: ℚ(i) は可換環（全公理を ℚ の環公理から本物に証明） -/

/-- **gqi-2: ℚ(i) の可換環構造** — 加法は成分ごと、乗法はガウス則。
    結合・可換・分配は ℚ の環公理（M115F）からの明示計算。 -/
def gqiRing : CRing where
  carrier := gqiCarrier
  add := gqiAdd
  zero := gqiZero
  neg := gqiNeg
  mul := gqiMul
  one := gqiOne
  add_assoc := fun x y z =>
    gqi_ext (ratRing.add_assoc x.1 y.1 z.1) (ratRing.add_assoc x.2 y.2 z.2)
  zero_add := fun x =>
    gqi_ext (ratRing.zero_add x.1) (ratRing.zero_add x.2)
  neg_add := fun x =>
    gqi_ext (ratRing.neg_add x.1) (ratRing.neg_add x.2)
  add_comm := fun x y =>
    gqi_ext (ratRing.add_comm x.1 y.1) (ratRing.add_comm x.2 y.2)
  mul_assoc := by
    intro x y z
    apply gqi_ext
    · show ratRing.add
          (ratRing.mul
            (ratRing.add (ratRing.mul x.1 y.1)
              (ratRing.neg (ratRing.mul x.2 y.2))) z.1)
          (ratRing.neg
            (ratRing.mul
              (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)) z.2))
        = ratRing.add
          (ratRing.mul x.1
            (ratRing.add (ratRing.mul y.1 z.1)
              (ratRing.neg (ratRing.mul y.2 z.2))))
          (ratRing.neg
            (ratRing.mul x.2
              (ratRing.add (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1))))
      rw [ratRing.right_distrib (ratRing.mul x.1 y.1)
          (ratRing.neg (ratRing.mul x.2 y.2)) z.1,
        ratRing.right_distrib (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1) z.2,
        ratRing.left_distrib x.1 (ratRing.mul y.1 z.1)
          (ratRing.neg (ratRing.mul y.2 z.2)),
        ratRing.left_distrib x.2 (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1),
        ratRing.neg_mul (ratRing.mul x.2 y.2) z.1,
        ratRing.neg_add_dist (ratRing.mul (ratRing.mul x.1 y.2) z.2)
          (ratRing.mul (ratRing.mul x.2 y.1) z.2),
        ratRing.mul_neg x.1 (ratRing.mul y.2 z.2),
        ratRing.neg_add_dist (ratRing.mul x.2 (ratRing.mul y.1 z.2))
          (ratRing.mul x.2 (ratRing.mul y.2 z.1)),
        ← ratRing.mul_assoc x.1 y.1 z.1,
        ← ratRing.mul_assoc x.1 y.2 z.2,
        ← ratRing.mul_assoc x.2 y.1 z.2,
        ← ratRing.mul_assoc x.2 y.2 z.1,
        ratRing.add_add_add_comm (ratRing.mul (ratRing.mul x.1 y.1) z.1)
          (ratRing.neg (ratRing.mul (ratRing.mul x.2 y.2) z.1))
          (ratRing.neg (ratRing.mul (ratRing.mul x.1 y.2) z.2))
          (ratRing.neg (ratRing.mul (ratRing.mul x.2 y.1) z.2)),
        ratRing.add_comm (ratRing.neg (ratRing.mul (ratRing.mul x.2 y.2) z.1))
          (ratRing.neg (ratRing.mul (ratRing.mul x.2 y.1) z.2))]
    · show ratRing.add
          (ratRing.mul
            (ratRing.add (ratRing.mul x.1 y.1)
              (ratRing.neg (ratRing.mul x.2 y.2))) z.2)
          (ratRing.mul
            (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)) z.1)
        = ratRing.add
          (ratRing.mul x.1
            (ratRing.add (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1)))
          (ratRing.mul x.2
            (ratRing.add (ratRing.mul y.1 z.1)
              (ratRing.neg (ratRing.mul y.2 z.2))))
      rw [ratRing.right_distrib (ratRing.mul x.1 y.1)
          (ratRing.neg (ratRing.mul x.2 y.2)) z.2,
        ratRing.right_distrib (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1) z.1,
        ratRing.left_distrib x.1 (ratRing.mul y.1 z.2) (ratRing.mul y.2 z.1),
        ratRing.left_distrib x.2 (ratRing.mul y.1 z.1)
          (ratRing.neg (ratRing.mul y.2 z.2)),
        ratRing.neg_mul (ratRing.mul x.2 y.2) z.2,
        ratRing.mul_neg x.2 (ratRing.mul y.2 z.2),
        ← ratRing.mul_assoc x.1 y.1 z.2,
        ← ratRing.mul_assoc x.1 y.2 z.1,
        ← ratRing.mul_assoc x.2 y.1 z.1,
        ← ratRing.mul_assoc x.2 y.2 z.2,
        ratRing.add_add_add_comm (ratRing.mul (ratRing.mul x.1 y.1) z.2)
          (ratRing.neg (ratRing.mul (ratRing.mul x.2 y.2) z.2))
          (ratRing.mul (ratRing.mul x.1 y.2) z.1)
          (ratRing.mul (ratRing.mul x.2 y.1) z.1),
        ratRing.add_comm (ratRing.neg (ratRing.mul (ratRing.mul x.2 y.2) z.2))
          (ratRing.mul (ratRing.mul x.2 y.1) z.1)]
  one_mul := by
    intro x
    apply gqi_ext
    · show ratRing.add (ratRing.mul ratRing.one x.1)
          (ratRing.neg (ratRing.mul ratRing.zero x.2)) = x.1
      rw [ratRing.one_mul x.1, ratRing.zero_mul x.2, gqi_q_neg_zero,
        ratRing.add_zero x.1]
    · show ratRing.add (ratRing.mul ratRing.one x.2)
          (ratRing.mul ratRing.zero x.1) = x.2
      rw [ratRing.one_mul x.2, ratRing.zero_mul x.1, ratRing.add_zero x.2]
  mul_comm := by
    intro x y
    apply gqi_ext
    · show ratRing.add (ratRing.mul x.1 y.1)
          (ratRing.neg (ratRing.mul x.2 y.2))
        = ratRing.add (ratRing.mul y.1 x.1)
          (ratRing.neg (ratRing.mul y.2 x.2))
      rw [ratRing.mul_comm x.1 y.1, ratRing.mul_comm x.2 y.2]
    · show ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1)
        = ratRing.add (ratRing.mul y.1 x.2) (ratRing.mul y.2 x.1)
      rw [ratRing.mul_comm x.1 y.2, ratRing.mul_comm x.2 y.1,
        ratRing.add_comm (ratRing.mul y.2 x.1) (ratRing.mul y.1 x.2)]
  left_distrib := by
    intro x y z
    apply gqi_ext
    · show ratRing.add (ratRing.mul x.1 (ratRing.add y.1 z.1))
          (ratRing.neg (ratRing.mul x.2 (ratRing.add y.2 z.2)))
        = ratRing.add
          (ratRing.add (ratRing.mul x.1 y.1)
            (ratRing.neg (ratRing.mul x.2 y.2)))
          (ratRing.add (ratRing.mul x.1 z.1)
            (ratRing.neg (ratRing.mul x.2 z.2)))
      rw [ratRing.left_distrib x.1 y.1 z.1, ratRing.left_distrib x.2 y.2 z.2,
        ratRing.neg_add_dist (ratRing.mul x.2 y.2) (ratRing.mul x.2 z.2),
        ratRing.add_add_add_comm (ratRing.mul x.1 y.1) (ratRing.mul x.1 z.1)
          (ratRing.neg (ratRing.mul x.2 y.2))
          (ratRing.neg (ratRing.mul x.2 z.2))]
    · show ratRing.add (ratRing.mul x.1 (ratRing.add y.2 z.2))
          (ratRing.mul x.2 (ratRing.add y.1 z.1))
        = ratRing.add
          (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1))
          (ratRing.add (ratRing.mul x.1 z.2) (ratRing.mul x.2 z.1))
      rw [ratRing.left_distrib x.1 y.2 z.2, ratRing.left_distrib x.2 y.1 z.1,
        ratRing.add_add_add_comm (ratRing.mul x.1 y.2) (ratRing.mul x.1 z.2)
          (ratRing.mul x.2 y.1) (ratRing.mul x.2 z.1)]

/-! ## gqi-3: 形式的実性 — (a,b) ≠ (0,0) ⟹ N = a²+b² ≠ 0 -/

/-- **gqi-3: ノルムの非退化性（ℚ の形式的実性）** — (a,b) ≠ (0,0) なら
    a²+b² ≠ 0。証明: a²+b² = 0 と仮定すると平方非負と反対称律から a² = 0 かつ
    b² = 0、整域性から ¬(a≠0)・¬(b≠0)。目標が False（否定）なので二重否定を
    構成的に剥がして (a,b) = (0,0) を得、仮定と矛盾。choice 不使用。 -/
theorem gqi_normsq_ne_zero (x : gqiCarrier) (hx : x ≠ gqiZero) :
    gqiNorm x ≠ ratRing.zero := by
  intro hN
  have hN' : ratRing.add (ratRing.mul x.1 x.1) (ratRing.mul x.2 x.2)
      = ratRing.zero := hN
  have ha : ratRing.mul x.1 x.1 = ratRing.zero := gqi_q_sq_eq_zero_left hN'
  have hb : ratRing.mul x.2 x.2 = ratRing.zero := gqi_q_sq_eq_zero_right hN'
  apply gqi_q_not_ne_of_sq_zero ha
  intro h1
  apply gqi_q_not_ne_of_sq_zero hb
  intro h2
  apply hx
  exact gqi_ext h1 h2

/-! ## gqi-4: ℚ(i) は本物の体 -/

/-- **体公理の本体** — x ≠ 0 なら x·x⁻¹ = 1。第 1 成分は
    a·(aN⁻¹) − b·(−bN⁻¹) = (a²+b²)·N⁻¹ = N·N⁻¹ = 1（N ≠ 0 は gqi-3、
    N·N⁻¹ = 1 は M264F の本物の ℚ 体公理）。第 2 成分は
    a·(−bN⁻¹) + b·(aN⁻¹) = −(abN⁻¹) + abN⁻¹ = 0。 -/
theorem gqi_mul_inv_cancel (x : gqiCarrier) (hx : x ≠ gqiZero) :
    gqiMul x (gqiInv x) = gqiOne := by
  have hN : gqiNorm x ≠ ratRing.zero := gqi_normsq_ne_zero x hx
  have hcancel : ratRing.mul (gqiNorm x) (qInv (gqiNorm x)) = ratRing.one :=
    ratIUTField.mul_inv_cancel (gqiNorm x) hN
  apply gqi_ext
  · show ratRing.add
        (ratRing.mul x.1 (ratRing.mul x.1 (qInv (gqiNorm x))))
        (ratRing.neg
          (ratRing.mul x.2
            (ratRing.mul (ratRing.neg x.2) (qInv (gqiNorm x)))))
      = ratRing.one
    rw [← ratRing.mul_assoc x.1 x.1 (qInv (gqiNorm x)),
      ← ratRing.mul_assoc x.2 (ratRing.neg x.2) (qInv (gqiNorm x)),
      ratRing.mul_neg x.2 x.2,
      ratRing.neg_mul (ratRing.mul x.2 x.2) (qInv (gqiNorm x)),
      ratRing.neg_neg (ratRing.mul (ratRing.mul x.2 x.2) (qInv (gqiNorm x))),
      ← ratRing.right_distrib (ratRing.mul x.1 x.1) (ratRing.mul x.2 x.2)
        (qInv (gqiNorm x))]
    exact hcancel
  · show ratRing.add
        (ratRing.mul x.1 (ratRing.mul (ratRing.neg x.2) (qInv (gqiNorm x))))
        (ratRing.mul x.2 (ratRing.mul x.1 (qInv (gqiNorm x))))
      = ratRing.zero
    rw [← ratRing.mul_assoc x.1 (ratRing.neg x.2) (qInv (gqiNorm x)),
      ratRing.mul_neg x.1 x.2,
      ratRing.neg_mul (ratRing.mul x.1 x.2) (qInv (gqiNorm x)),
      ← ratRing.mul_assoc x.2 x.1 (qInv (gqiNorm x)),
      ratRing.mul_comm x.2 x.1]
    exact ratRing.neg_add (ratRing.mul (ratRing.mul x.1 x.2) (qInv (gqiNorm x)))

/-- 0⁻¹ = 0（成分ごとに 0·_ = 0）。 -/
theorem gqi_inv_zero : gqiInv gqiZero = gqiZero := by
  apply gqi_ext
  · show ratRing.mul ratRing.zero (qInv (gqiNorm gqiZero)) = ratRing.zero
    exact ratRing.zero_mul (qInv (gqiNorm gqiZero))
  · show ratRing.mul (ratRing.neg ratRing.zero) (qInv (gqiNorm gqiZero))
      = ratRing.zero
    rw [gqi_q_neg_zero]
    exact ratRing.zero_mul (qInv (gqiNorm gqiZero))

/-- (0,0) ≠ (1,0)（第 1 成分で ℚ の 0 ≠ 1 に帰着）。 -/
theorem gqi_zero_ne_one : gqiZero ≠ gqiOne := by
  intro h
  have h1 : ratRing.zero = ratRing.one :=
    congrArg (fun p : gqiCarrier => p.1) h
  exact ratIUTField.zero_ne_one h1

/-- **gqi-4: ℚ(i) は本物の体** — 台は実 ℚ×ℚ、逆元は実ガウス逆元、
    体公理は形式的実性から完全証明。 -/
def gaussQField : IUTField where
  toCRing := gqiRing
  inv := gqiInv
  mul_inv_cancel := gqi_mul_inv_cancel
  inv_zero := gqi_inv_zero
  zero_ne_one := gqi_zero_ne_one

/-! ## gqi-5: 非自明拡大 ℚ ⊂ ℚ(i) -/

/-- **gqi-5: 体拡大 ℚ ⊂ ℚ(i)** — 埋め込み a ↦ (a,0) は環準同型
    （加法・乗法・1 を保つ）。コードベース初の非自明有限次拡大。 -/
def gqiExtension : FieldExtension where
  base := ratIUTField
  top := gaussQField
  incl := fun a => ((a, ratRing.zero) : gqiCarrier)
  incl_add := fun a b => by
    apply gqi_ext
    · exact rfl
    · show ratRing.zero = ratRing.add ratRing.zero ratRing.zero
      exact (ratRing.zero_add ratRing.zero).symm
  incl_mul := fun a b => by
    apply gqi_ext
    · show ratRing.mul a b
        = ratRing.add (ratRing.mul a b)
          (ratRing.neg (ratRing.mul ratRing.zero ratRing.zero))
      rw [ratRing.zero_mul ratRing.zero, gqi_q_neg_zero,
        ratRing.add_zero (ratRing.mul a b)]
    · show ratRing.zero
        = ratRing.add (ratRing.mul a ratRing.zero) (ratRing.mul ratRing.zero b)
      rw [ratRing.mul_zero a, ratRing.zero_mul b,
        ratRing.zero_add ratRing.zero]
  incl_one := rfl

/-! ## gqi-6: 複素共役は ℚ(i) の体自己同型で ℚ を各点固定 -/

/-- **gqi-6: 複素共役** σ(a,b) = (a,−b) — ℚ(i) の本物の体自己同型
    （加法・乗法・1 を保ち、自身が明示逆写像の対合）。乗法の保存が
    i² = −1 と整合する本物の内容（(−b)(−d) = bd）。 -/
def gqiConj : FieldAut gaussQField where
  toFun := fun x => ((x.1, ratRing.neg x.2) : gqiCarrier)
  invFun := fun x => ((x.1, ratRing.neg x.2) : gqiCarrier)
  map_add := fun x y => by
    apply gqi_ext
    · exact rfl
    · show ratRing.neg (ratRing.add x.2 y.2)
        = ratRing.add (ratRing.neg x.2) (ratRing.neg y.2)
      exact ratRing.neg_add_dist x.2 y.2
  map_mul := fun x y => by
    apply gqi_ext
    · show ratRing.add (ratRing.mul x.1 y.1)
          (ratRing.neg (ratRing.mul x.2 y.2))
        = ratRing.add (ratRing.mul x.1 y.1)
          (ratRing.neg (ratRing.mul (ratRing.neg x.2) (ratRing.neg y.2)))
      rw [ratRing.neg_mul x.2 (ratRing.neg y.2), ratRing.mul_neg x.2 y.2,
        ratRing.neg_neg (ratRing.mul x.2 y.2)]
    · show ratRing.neg (ratRing.add (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1))
        = ratRing.add (ratRing.mul x.1 (ratRing.neg y.2))
          (ratRing.mul (ratRing.neg x.2) y.1)
      rw [ratRing.neg_add_dist (ratRing.mul x.1 y.2) (ratRing.mul x.2 y.1),
        ratRing.mul_neg x.1 y.2, ratRing.neg_mul x.2 y.1]
  map_one := by
    apply gqi_ext
    · exact rfl
    · show ratRing.neg ratRing.zero = ratRing.zero
      exact gqi_q_neg_zero
  left_inv := fun x => by
    apply gqi_ext
    · exact rfl
    · show ratRing.neg (ratRing.neg x.2) = x.2
      exact ratRing.neg_neg x.2
  right_inv := fun x => by
    apply gqi_ext
    · exact rfl
    · show ratRing.neg (ratRing.neg x.2) = x.2
      exact ratRing.neg_neg x.2

/-- **共役は ℚ を各点固定** — conj(a,0) = (a,−0) = (a,0)。 -/
theorem gqi_conj_fixes_base (k : QRat) :
    gqiConj.toFun (gqiExtension.incl k) = gqiExtension.incl k := by
  apply gqi_ext
  · exact rfl
  · show ratRing.neg ratRing.zero = ratRing.zero
    exact gqi_q_neg_zero

/-- **conj ∈ Gal(ℚ(i)/ℚ)**（M271F-4 の Galois 部分群の membership）。 -/
theorem gqi_conj_mem_galois : (galoisSubgroup gqiExtension).mem gqiConj := by
  intro k
  exact gqi_conj_fixes_base k

/-! ## gqi-7: 本丸 — Gal(ℚ(i)/ℚ) は非自明 -/

/-- **gqi-7a: conj ≠ id** — conj(i) = (0,−1) ≠ (0,1) = i（第 2 成分で
    ℚ の −1 ≠ 1 に帰着）。 -/
theorem gqi_conj_ne_id : gqiConj ≠ fieldAutId gaussQField := by
  intro h
  have h1 : gqiConj.toFun gqiI = (fieldAutId gaussQField).toFun gqiI := by
    rw [h]
  have h2 : ratRing.neg ratRing.one = ratRing.one :=
    congrArg (fun p : gqiCarrier => p.2) h1
  exact gqi_q_neg_one_ne_one h2

/-- **gqi-7b: Gal(ℚ(i)/ℚ) は非自明** — ℚ を各点固定する自己同型で恒等でない
    もの（複素共役）が存在する。コードベース初の非自明実 Galois 群の実例。 -/
theorem gqi_galois_nontrivial :
    ∃ σ : FieldAut gaussQField,
      (galoisSubgroup gqiExtension).mem σ ∧ σ ≠ fieldAutId gaussQField :=
  ⟨gqiConj, gqi_conj_mem_galois, gqi_conj_ne_id⟩

/-- **gqi-7c: 群としての非自明性** — Gal(ℚ(i)/ℚ) を M271F-5 の群
    `galoisGroupGrp` として見たとき、単位元と異なる元が存在する。 -/
theorem gqi_galoisGroup_nontrivial :
    ∃ g : (galoisGroupGrp gqiExtension).carrier,
      g ≠ (galoisGroupGrp gqiExtension).one := by
  refine ⟨⟨gqiConj, gqi_conj_mem_galois⟩, ?_⟩
  intro h
  have h1 : gqiConj = fieldAutId gaussQField := congrArg Subtype.val h
  exact gqi_conj_ne_id h1

/-! ## gqi-8: capstone -/

/-- **gqi-8: capstone** — 非自明 Galois 群を持つ本物の体拡大が存在する
    （witness: ℚ ⊂ ℚ(i) と複素共役）。 -/
theorem gqi_exists :
    ∃ E : FieldExtension, ∃ σ : FieldAut E.top,
      (galoisSubgroup E).mem σ ∧ σ ≠ fieldAutId E.top :=
  ⟨gqiExtension, gqiConj, gqi_conj_mem_galois, gqi_conj_ne_id⟩

end IUT
