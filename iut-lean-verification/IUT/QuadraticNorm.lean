/-
  IUT/QuadraticNorm.lean — QNM: 二次拡大 ℚ(i)/ℚ の実ノルム写像 N と乗法性
  — 実局所類体論のノルム群の実対象の種（§2(b) 本物建設）

  ── 主要成果の分類: **[実]**（本物の体 ℚ(i)（`gaussQField`）の上に、実際の
  ℚ 値ノルム N(a,b) = a²+b² を構成し、その乗法性 N(z·w) = N(z)·N(w) を
  ℚ の環公理から完全証明する）。

  complete_pct 影響: **柱A の実ノルム写像／ノルム群の本物建設**。既存の本物の
  体拡大 ℚ ⊂ ℚ(i)（`GaussianRationalField.lean`）の上に、局所類体論で
  中心となる**ノルム写像 N: ℚ(i)^× → ℚ^×** の実例を積む。乗法性は
  **ガウス恒等式 (a²+b²)(c²+d²) = (ac−bd)² + (ad+bc)²** を ℚ の可換環公理
  （結合・可換・分配・負元則）から明示計算で証明。身代わり群・Bool 軌道・
  toy 模型は一切用いない。ノルム 1 の元の集合が乗法・逆元・単位で閉じる
  （**ノルム 1 部分群 = ker(N) の本物**）ことも完全証明する。

  * qnm-0 `qnm_mul_mul_mul_comm` / `qnm_add_cancel` — CRing の可換簿記
    （4 因子入替と、交差項 ±K の相殺）
  * qnm-1 `qnm_gauss` — **ガウス恒等式**（一般 CRing 上、a,b,c,d の多項式等式を
    分配・可換・負元則の明示 rw で証明。ring/nlinarith 不使用）
  * qnm-2 `qnmNorm` — 実ノルム N(a,b) = a²+b²（既存 `gqiNorm` を再利用、ℚ 値）
  * qnm-3 `qnm_mul` — **本丸: N(z·w) = N(z)·N(w)**（gqiMul と qnm_gauss を接続）
  * qnm-4 `qnm_norm_one` / `qnm_norm_zero` / `qnm_norm_ne_zero` — N(1)=1・N(0)=0・
    z≠0 ⟹ N(z)≠0（形式的実性 `gqi_normsq_ne_zero` 再利用）
  * qnm-5 `qnmNormOne` / `qnm_norm_one_{mul,inv}_closed` / `qnm_norm_one_ne_zero`
    — ノルム 1 の元が乗法・逆元で閉じ、非零である（ノルム群の本物）
  * qnm-6 `QnmNormOneSubgroup` / `qnmNormOneSet` — ノルム 1 部分群の総括
  * qnm-7 capstone `qnm_exists` — 乗法的かつ単位を保つ実ノルム写像の存在

  正直な限定（何が本物で何が未達か）:
  - **本物**: N は実際の ℚ の値 a²+b²（`gqiNorm` = ratRing.add (mul a a)(mul b b)）。
    乗法性 `qnm_mul` はガウス恒等式を ℚ の環公理から完全証明（sorry 皆無・
    新規 Classical.choice 皆無・禁止タクティク不使用）。ノルム 1 部分群の
    乗法閉性・逆元閉性・単位・非零は完全証明。
  - **未達（正直申告）**: (1) N の像（ノルム群 N(ℚ(i)^×) ⊆ ℚ^×）が ℚ^× の
    どの部分群かの決定（= 平方和で書ける正の有理数の特徴づけ）は未着手。
    (2) 局所体上のノルム剰余記号・相互律との接続は上位層の後続。
    本モジュールは「実ノルム写像の乗法性 + ノルム 1 群の閉性」まで。

  全て選択公理不使用（新規 choice を証明本体に導入しない）。
  禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。
-/
import IUT.GaussianRationalField

namespace IUT

/-! ## qnm-0: CRing の可換簿記 -/

/-- **4 因子入替** (a·b)·(c·d) = (a·c)·(b·d)（結合・可換から）。 -/
theorem qnm_mul_mul_mul_comm (R : CRing) (a b c d : R.carrier) :
    R.mul (R.mul a b) (R.mul c d) = R.mul (R.mul a c) (R.mul b d) := by
  rw [R.mul_assoc a b (R.mul c d), ← R.mul_assoc b c d, R.mul_comm b c,
    R.mul_assoc c b d, ← R.mul_assoc a c (R.mul b d)]

/-- **交差項の相殺** — 二乗展開に現れる ±k の 4 項が相殺し、平方項だけ残る形。
    ((w−k)+(−k+x)) + ((y+k)+(k+z)) = (w+y)+(z+x)。純加法アーベル群の恒等式。 -/
theorem qnm_add_cancel (R : CRing) (w x y z k : R.carrier) :
    R.add (R.add (R.add w (R.neg k)) (R.add (R.neg k) x))
        (R.add (R.add y k) (R.add k z))
      = R.add (R.add w y) (R.add z x) := by
  rw [R.add_add_add_comm (R.add w (R.neg k)) (R.add (R.neg k) x)
      (R.add y k) (R.add k z),
    R.add_add_add_comm w (R.neg k) y k,
    R.add_add_add_comm (R.neg k) x k z,
    R.neg_add k, R.add_zero (R.add w y),
    R.zero_add (R.add x z),
    R.add_comm x z]

/-! ## qnm-1: ガウス恒等式 -/

/-- **qnm-1: ガウス恒等式** — (a²+b²)(c²+d²) = (ac−bd)² + (ad+bc)²。
    一般可換環上の多項式等式を、左右分配・可換・負元則の明示 rw で証明
    （ring/nlinarith を使わない）。左辺を平方項の和 NF に展開し、右辺の二乗を
    展開して交差項 ±(ab)(cd) を相殺、同じ NF に帰着させる。 -/
theorem qnm_gauss (R : CRing) (a b c d : R.carrier) :
    R.mul (R.add (R.mul a a) (R.mul b b)) (R.add (R.mul c c) (R.mul d d))
      = R.add
          (R.mul (R.add (R.mul a c) (R.neg (R.mul b d)))
                 (R.add (R.mul a c) (R.neg (R.mul b d))))
          (R.mul (R.add (R.mul a d) (R.mul b c))
                 (R.add (R.mul a d) (R.mul b c))) := by
  have e2 : R.mul (R.mul b d) (R.mul a c) = R.mul (R.mul a b) (R.mul c d) := by
    rw [qnm_mul_mul_mul_comm R b d a c, R.mul_comm b a, R.mul_comm d c]
  have e3 : R.mul (R.mul a d) (R.mul b c) = R.mul (R.mul a b) (R.mul c d) := by
    rw [qnm_mul_mul_mul_comm R a d b c, R.mul_comm d c]
  have e4 : R.mul (R.mul b c) (R.mul a d) = R.mul (R.mul a b) (R.mul c d) := by
    rw [qnm_mul_mul_mul_comm R b c a d, R.mul_comm b a]
  rw [R.right_distrib (R.mul a a) (R.mul b b) (R.add (R.mul c c) (R.mul d d)),
    R.left_distrib (R.mul a a) (R.mul c c) (R.mul d d),
    R.left_distrib (R.mul b b) (R.mul c c) (R.mul d d),
    R.right_distrib (R.mul a c) (R.neg (R.mul b d))
      (R.add (R.mul a c) (R.neg (R.mul b d))),
    R.left_distrib (R.mul a c) (R.mul a c) (R.neg (R.mul b d)),
    R.left_distrib (R.neg (R.mul b d)) (R.mul a c) (R.neg (R.mul b d)),
    R.right_distrib (R.mul a d) (R.mul b c) (R.add (R.mul a d) (R.mul b c)),
    R.left_distrib (R.mul a d) (R.mul a d) (R.mul b c),
    R.left_distrib (R.mul b c) (R.mul a d) (R.mul b c),
    R.mul_neg (R.mul a c) (R.mul b d),
    R.neg_mul (R.mul b d) (R.mul a c),
    R.neg_mul (R.mul b d) (R.neg (R.mul b d)),
    R.mul_neg (R.mul b d) (R.mul b d),
    R.neg_neg (R.mul (R.mul b d) (R.mul b d)),
    qnm_mul_mul_mul_comm R a c a c,
    qnm_mul_mul_mul_comm R a c b d,
    e2,
    qnm_mul_mul_mul_comm R b d b d,
    qnm_mul_mul_mul_comm R a d a d,
    e3,
    e4,
    qnm_mul_mul_mul_comm R b c b c,
    qnm_add_cancel R (R.mul (R.mul a a) (R.mul c c))
      (R.mul (R.mul b b) (R.mul d d)) (R.mul (R.mul a a) (R.mul d d))
      (R.mul (R.mul b b) (R.mul c c)) (R.mul (R.mul a b) (R.mul c d))]

/-! ## qnm-2: 実ノルム N(a,b) = a²+b² -/

/-- **qnm-2: 実ノルム** N(a,b) = a²+b²（既存の本物の `gqiNorm` を再利用、
    ℚ に値を取る）。身代わりではなく実際の有理数の平方和。 -/
def qnmNorm (z : gqiCarrier) : ratIUTField.carrier := gqiNorm z

/-! ## qnm-3: 本丸 — ノルムの乗法性 -/

/-- **qnm-3: 本丸 N(z·w) = N(z)·N(w)** — ガウス積 `gqiMul` の第 1・第 2 成分が
    ガウス恒等式の (ac−bd), (ad+bc) に一致することから、`qnm_gauss` を
    そのまま接続。乗法性は ℚ の環公理からの本物証明。 -/
theorem qnm_mul (z w : gqiCarrier) :
    qnmNorm (gqiMul z w) = ratRing.mul (qnmNorm z) (qnmNorm w) := by
  show ratRing.add
        (ratRing.mul
          (ratRing.add (ratRing.mul z.1 w.1)
            (ratRing.neg (ratRing.mul z.2 w.2)))
          (ratRing.add (ratRing.mul z.1 w.1)
            (ratRing.neg (ratRing.mul z.2 w.2))))
        (ratRing.mul
          (ratRing.add (ratRing.mul z.1 w.2) (ratRing.mul z.2 w.1))
          (ratRing.add (ratRing.mul z.1 w.2) (ratRing.mul z.2 w.1)))
      = ratRing.mul
          (ratRing.add (ratRing.mul z.1 z.1) (ratRing.mul z.2 z.2))
          (ratRing.add (ratRing.mul w.1 w.1) (ratRing.mul w.2 w.2))
  exact (qnm_gauss ratRing z.1 z.2 w.1 w.2).symm

/-! ## qnm-4: 単位・零・非退化 -/

/-- **qnm-4a: N(1) = 1**（(1,0) のノルム = 1·1 + 0·0 = 1）。 -/
theorem qnm_norm_one : qnmNorm gqiOne = ratRing.one := by
  show ratRing.add (ratRing.mul ratRing.one ratRing.one)
        (ratRing.mul ratRing.zero ratRing.zero) = ratRing.one
  rw [ratRing.one_mul ratRing.one, ratRing.zero_mul ratRing.zero,
    ratRing.add_zero ratRing.one]

/-- **qnm-4b: N(0) = 0**（(0,0) のノルム = 0·0 + 0·0 = 0）。 -/
theorem qnm_norm_zero : qnmNorm gqiZero = ratRing.zero := by
  show ratRing.add (ratRing.mul ratRing.zero ratRing.zero)
        (ratRing.mul ratRing.zero ratRing.zero) = ratRing.zero
  rw [ratRing.zero_mul ratRing.zero, ratRing.add_zero ratRing.zero]

/-- **qnm-4c: z ≠ 0 ⟹ N(z) ≠ 0**（形式的実性 `gqi_normsq_ne_zero` 再利用）。 -/
theorem qnm_norm_ne_zero (z : gqiCarrier) (hz : z ≠ gqiZero) :
    qnmNorm z ≠ ratRing.zero :=
  gqi_normsq_ne_zero z hz

/-! ## qnm-5: ノルム 1 の元（ノルム群の本物） -/

/-- **qnm-5: ノルム 1 の述語** N(z) = 1（ノルム群 ker(N) の元）。 -/
def qnmNormOne (z : gqiCarrier) : Prop := qnmNorm z = ratRing.one

/-- **qnm-5a: 乗法閉性** — N(z)=1 かつ N(w)=1 なら N(z·w)=1
    （乗法性 `qnm_mul` と 1·1=1）。 -/
theorem qnm_norm_one_mul_closed {z w : gqiCarrier}
    (hz : qnmNormOne z) (hw : qnmNormOne w) : qnmNormOne (gqiMul z w) := by
  have hz' : qnmNorm z = ratRing.one := hz
  have hw' : qnmNorm w = ratRing.one := hw
  show qnmNorm (gqiMul z w) = ratRing.one
  rw [qnm_mul z w, hz', hw', ratRing.one_mul ratRing.one]

/-- **qnm-5b: ノルム 1 なら非零** — N(z)=1 かつ z=0 なら N(0)=0=1 で矛盾。 -/
theorem qnm_norm_one_ne_zero {z : gqiCarrier} (hz : qnmNormOne z) :
    z ≠ gqiZero := by
  have hz' : qnmNorm z = ratRing.one := hz
  intro h
  have hz0 : qnmNorm z = ratRing.zero := by
    rw [h]; exact qnm_norm_zero
  have hne : ratRing.one = ratRing.zero := by
    rw [← hz']; exact hz0
  exact ratIUTField.one_ne_zero hne

/-- **qnm-5c: 逆元閉性** — N(z)=1 なら N(z⁻¹)=1（z≠0 より z·z⁻¹=1、
    乗法性から 1 = N(z)·N(z⁻¹) = N(z⁻¹)）。 -/
theorem qnm_norm_one_inv_closed {z : gqiCarrier} (hz : qnmNormOne z) :
    qnmNormOne (gqiInv z) := by
  have hz' : qnmNorm z = ratRing.one := hz
  have hne : z ≠ gqiZero := qnm_norm_one_ne_zero hz
  have hcancel : gqiMul z (gqiInv z) = gqiOne := gqi_mul_inv_cancel z hne
  have hmul : qnmNorm (gqiMul z (gqiInv z))
      = ratRing.mul (qnmNorm z) (qnmNorm (gqiInv z)) := qnm_mul z (gqiInv z)
  rw [hcancel, qnm_norm_one, hz', ratRing.one_mul (qnmNorm (gqiInv z))] at hmul
  show qnmNorm (gqiInv z) = ratRing.one
  exact hmul.symm

/-! ## qnm-6: ノルム 1 部分群の総括 -/

/-- **qnm-6a: ノルム 1 部分群の枠** — 乗法・逆元で閉じ、単位を含む部分群。 -/
structure QnmNormOneSubgroup where
  /-- 元であること（述語）。 -/
  mem : gqiCarrier → Prop
  /-- 単位 1 は元。 -/
  one_mem : mem gqiOne
  /-- 乗法で閉じる。 -/
  mul_mem : ∀ {z w : gqiCarrier}, mem z → mem w → mem (gqiMul z w)
  /-- 逆元で閉じる。 -/
  inv_mem : ∀ {z : gqiCarrier}, mem z → mem (gqiInv z)

/-- **qnm-6b: N(z)=1 の元は本物のノルム 1 部分群をなす**。 -/
def qnmNormOneSet : QnmNormOneSubgroup where
  mem := qnmNormOne
  one_mem := qnm_norm_one
  mul_mem := fun {_ _} hz hw => qnm_norm_one_mul_closed hz hw
  inv_mem := fun {_} hz => qnm_norm_one_inv_closed hz

/-! ## qnm-7: capstone -/

/-- **qnm-7: capstone** — ℚ(i) 上に、乗法的かつ単位を保つ実 ℚ 値ノルム写像が
    存在する（witness: N(a,b) = a²+b²）。 -/
theorem qnm_exists :
    ∃ N : gqiCarrier → ratIUTField.carrier,
      (∀ z w, N (gqiMul z w) = ratRing.mul (N z) (N w)) ∧
      N gqiOne = ratRing.one :=
  ⟨qnmNorm, qnm_mul, qnm_norm_one⟩

end IUT
