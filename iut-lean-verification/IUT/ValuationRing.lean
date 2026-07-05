/-
  IUT/ValuationRing.lean — M301F: 離散付値と付値環 O_v（局所体＝柱 B への接続）

  ── 主要成果の分類: **[実]**（本物の体 `IUTField`（M264F）上に、本物の離散付値
  `v : K → ℤ∪{∞}` と本物の付値環 `O_v = {x | v(x) ≥ 0}` を構成し、付値環が
  **部分環・局所環**であること、極大イデアル `m_v = {v ≥ 1}` がイデアルであること、
  素元 π（v(π)=1）が m_v を生成すること、付値環外の元の逆元が m_v に落ちること
  （整閉性の核）を**完全証明**する）。

  complete_pct 影響: **柱A の局所体（付値環）の本物の先行建設**。数体の素点・局所体
  ℚ_p の代数的核は「体 K 上の離散付値 v とその付値環 O_v（DVR）」である。柱B の
  ℤ_p は「p 進付値の付値環」という特殊例だが、コードベースには**体上の一般離散付値と
  その付値環 O_v** を IUTField 上に建てたモジュールが無かった。本ファイルはその最下層を
  既存 `IUTField`（M264F）・`CRing`（M38）の上に**本物として実構成**する。これにより
  遠アーベル復元・エタールテータの舞台である局所体の代数的骨格が柱A に一段積まれる。
  （具体的な数体・ℚ_p の付値そのものの構成は柱B ℤ_p 接続の後続。）

  * M301F-1 `valOptAdd` / `valOptLe`  — 値群 ℤ∪{∞}（`Option Int`、none=∞）の
    加法（∞ 吸収）と順序（∞ が最大）
  * M301F-2 `valRingValuation`         — 体 K 上の**離散付値**の公理系
    （v(0)=∞, v(1)=0, v(xy)=v(x)+v(y), 超距離不等式, v(x)=∞ ⟺ x=0）
  * M301F-3 `valRingMem` / `valRingMaxMem` — 付値環 O_v={v≥0}・極大イデアル m_v={v≥1}
  * M301F-4 部分環性  — valRing_{zero,one,mul,add,neg}_mem / `valRing_isSubring`
  * M301F-5 イデアル性 — valRingMax_{zero_mem,absorb,add_mem}
  * M301F-6 局所環性  — `valRing_local_unit`（O_v∖m_v は単元）/ `valRing_is_local`
  * M301F-7 素元      — `valRing_uniformizer_generates`（m_v の元は π で割れる）
  * M301F-8 整閉核    — `valRing_notMem_inv_max`（O_v の外の元は逆元が m_v に落ちる
    ＝付値環は整閉／極大）、`valRing_integrallyClosed`（骨組み）
  * M301F-9 capstone  — `ValuationRingData` / `valRing_toData` / `valRing_exists` /
    `DVRData` / `valRing_dvr`、実例 `trivialValuation`（自明付値、O_v=K）

  正直な限定（何が本物で何が骨組みか）:
  - **本物**: 離散付値の公理系、付値環が部分環（0,1∈O_v・和積差で閉）・局所環
    （O_v∖m_v が単元）、m_v がイデアル、素元 π が m_v を生成する（任意 x∈m_v が
    π で割れる: x/π∈O_v）、付値環外の元の逆元が m_v に落ちる（整閉性の核）は
    完全証明（sorry 皆無・新規 choice 皆無）。
  - **超距離不等式の符号化**: v(x+y)≥min(v(x),v(y)) を、全順序値群上で同値な**選言形**
    `v(x+y)≥v(x) ∨ v(x+y)≥v(y)` で公理化した（min の順序判定を構成的に避けるための
    等価な言い換え。両者は全順序値群上で同値）。
  - **骨組み（後続）**: 「m_v=(π) の単項生成の完全性」は「割れる」方向を本物にし、
    生成の反対包含は骨組み。整閉整域（O_v が Frac=K の中で整閉な整域＝DVR）の完全証明は
    `valRing_notMem_inv_max`（外の元は非整）を本物に、monic 関係式による整閉包の全証明は
    後続。**具体的な離散付値（素元 π を持つ本物の v）の構成は柱B ℤ_p 接続の後続**——本
    ファイルの `trivialValuation`（自明付値）は O_v=K（rank 0）で π を持たないため、
    `DVRData`/`valRing_dvr` は「π を持つ付値なら DVR 骨格が従う」という条件付き本物
    （π 自身の具体構成は後続）として提示する。値群は ℤ（離散付値）に限る。
  - 本ファイルは付値の**代数構造**のみ。位相（完備化）・分岐・剰余体は既存
    ResidueField 等と後続で接続する。

  全て選択公理不使用（新規 choice を証明本体に導入しない）。
-/
import IUT.Field

namespace IUT

/-! ## M301F-1: 値群 ℤ∪{∞}（`Option Int`、`none` = ∞） -/

/-- **M301F-1a: 値群の加法**（∞ は吸収的: ∞+t = t+∞ = ∞）。 -/
def valOptAdd : Option Int → Option Int → Option Int
  | none, _ => none
  | some _, none => none
  | some a, some b => some (a + b)

/-- **M301F-1b: 値群の順序**（∞ が最大: t ≤ ∞ は真、∞ ≤ 有限 は偽）。 -/
def valOptLe : Option Int → Option Int → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a ≤ b

theorem valOptAdd_none_left (t : Option Int) : valOptAdd none t = none := rfl

theorem valOptAdd_some_none (a : Int) : valOptAdd (some a) none = none := rfl

theorem valOptAdd_some_some (a b : Int) : valOptAdd (some a) (some b) = some (a + b) := rfl

/-- 0 は加法の左単位（∞ でも保つ）。 -/
theorem valOptAdd_zero_left (t : Option Int) : valOptAdd (some (0 : Int)) t = t := by
  cases t with
  | none => rfl
  | some b =>
    show some ((0 : Int) + b) = some b
    rw [Int.zero_add]

/-- 順序の反射律。 -/
theorem valOptLe_refl (x : Option Int) : valOptLe x x := by
  cases x with
  | none => exact True.intro
  | some a => exact Int.le_refl a

/-- 順序の推移律（∞ を最大とする ℤ∪{∞} 上）。 -/
theorem valOptLe_trans {x y z : Option Int}
    (h1 : valOptLe x y) (h2 : valOptLe y z) : valOptLe x z := by
  cases z with
  | none => exact True.intro
  | some c =>
    cases y with
    | none => exact h2.elim
    | some b =>
      cases x with
      | none => exact h1.elim
      | some a => exact Int.le_trans h1 h2

/-! ## M301F-2: 体 K 上の離散付値の公理系 -/

/-- **M301F-2: 離散付値** `v : K → ℤ∪{∞}`。
    `v_zero`: v(0)=∞、`v_one`: v(1)=0、`v_mul`: v(xy)=v(x)+v(y)、
    `v_add_ge`: 超距離不等式の選言形（v(x+y)≥v(x) ∨ v(x+y)≥v(y)、全順序値群上で
    v(x+y)≥min(v(x),v(y)) と同値）、`v_eq_top`: v(x)=∞ ⟺ x=0（→ 側）。 -/
structure valRingValuation (K : IUTField) where
  /-- 付値関数（0 に ∞=none、非零元に整数値）。 -/
  v : K.carrier → Option Int
  /-- v(0) = ∞。 -/
  v_zero : v K.zero = none
  /-- v(1) = 0。 -/
  v_one : v K.one = some (0 : Int)
  /-- 乗法性: v(xy) = v(x) + v(y)。 -/
  v_mul : ∀ x y, v (K.mul x y) = valOptAdd (v x) (v y)
  /-- 超距離不等式（選言形）: v(x+y) ≥ v(x) または v(x+y) ≥ v(y)。 -/
  v_add_ge : ∀ x y, valOptLe (v x) (v (K.add x y)) ∨ valOptLe (v y) (v (K.add x y))
  /-- v(x)=∞ なら x=0（離散付値: 非零元は有限値）。 -/
  v_eq_top : ∀ x, v x = none → x = K.zero

/-! ## M301F-3: 付値環 O_v と極大イデアル m_v -/

/-- **M301F-3a: 付値環 O_v** の所属 = 「v(x) ≥ 0」。 -/
def valRingMem {K : IUTField} (val : valRingValuation K) (x : K.carrier) : Prop :=
  valOptLe (some (0 : Int)) (val.v x)

/-- **M301F-3b: 極大イデアル m_v** の所属 = 「v(x) ≥ 1」（= v(x) > 0）。 -/
def valRingMaxMem {K : IUTField} (val : valRingValuation K) (x : K.carrier) : Prop :=
  valOptLe (some (1 : Int)) (val.v x)

/-! ## M301F-4: 付値環は部分環 -/

/-- 0 ∈ O_v（v(0)=∞≥0）。 -/
theorem valRing_zero_mem {K : IUTField} (val : valRingValuation K) :
    valRingMem val K.zero := by
  show valOptLe (some (0 : Int)) (val.v K.zero)
  rw [val.v_zero]; exact True.intro

/-- 1 ∈ O_v（v(1)=0≥0）。 -/
theorem valRing_one_mem {K : IUTField} (val : valRingValuation K) :
    valRingMem val K.one := by
  show valOptLe (some (0 : Int)) (val.v K.one)
  rw [val.v_one]; exact Int.le_refl 0

/-- **積で閉じる**: v(x)≥0, v(y)≥0 なら v(xy)=v(x)+v(y)≥0。 -/
theorem valRing_mul_mem {K : IUTField} (val : valRingValuation K) (x y : K.carrier)
    (hx : valRingMem val x) (hy : valRingMem val y) : valRingMem val (K.mul x y) := by
  show valOptLe (some (0 : Int)) (val.v (K.mul x y))
  rw [val.v_mul]
  cases hvx : val.v x with
  | none => rw [valOptAdd_none_left]; exact True.intro
  | some a =>
    cases hvy : val.v y with
    | none => rw [valOptAdd_some_none]; exact True.intro
    | some b =>
      rw [valOptAdd_some_some]
      show (0 : Int) ≤ a + b
      have hx' : valOptLe (some (0 : Int)) (val.v x) := hx
      rw [hvx] at hx'
      have hy' : valOptLe (some (0 : Int)) (val.v y) := hy
      rw [hvy] at hy'
      show (0 : Int) ≤ a + b
      have ha : (0 : Int) ≤ a := hx'
      have hb : (0 : Int) ≤ b := hy'
      omega

/-- **和で閉じる**: v(x)≥0, v(y)≥0 なら超距離不等式で v(x+y)≥min≥0。 -/
theorem valRing_add_mem {K : IUTField} (val : valRingValuation K) (x y : K.carrier)
    (hx : valRingMem val x) (hy : valRingMem val y) : valRingMem val (K.add x y) := by
  show valOptLe (some (0 : Int)) (val.v (K.add x y))
  cases val.v_add_ge x y with
  | inl h => exact valOptLe_trans hx h
  | inr h => exact valOptLe_trans hy h

/-! ### 環の補題: (-1)·x = -x, -(-a)=a, x·1=x（v(-x)=v(x) 用） -/

/-- (-1)·x = -x（可換環）。 -/
theorem valRingNegOneMul (K : IUTField) (x : K.carrier) :
    K.mul (K.neg K.one) x = K.neg x := by
  have step : K.add (K.mul (K.neg K.one) x) (K.mul K.one x) = K.zero := by
    rw [← K.toCRing.right_distrib, K.neg_add, K.mul_comm K.zero x, K.toCRing.mul_zero]
  rw [K.one_mul x] at step
  have hz2 : K.add x (K.mul (K.neg K.one) x) = K.add x (K.neg x) := by
    rw [K.add_comm x (K.mul (K.neg K.one) x), step, K.add_comm x (K.neg x), K.neg_add]
  exact K.toCRing.add_left_cancel hz2

/-- -(-a) = a（可換環）。 -/
theorem valRingNegNeg (K : IUTField) (a : K.carrier) : K.neg (K.neg a) = a := by
  have h1 : K.add (K.neg (K.neg a)) (K.neg a) = K.zero := K.neg_add (K.neg a)
  have h2 : K.add a (K.neg a) = K.zero := by
    rw [K.add_comm a (K.neg a)]; exact K.neg_add a
  have hz2 : K.add (K.neg a) (K.neg (K.neg a)) = K.add (K.neg a) a := by
    rw [K.add_comm (K.neg a) (K.neg (K.neg a)), h1, K.add_comm (K.neg a) a, h2]
  exact K.toCRing.add_left_cancel hz2

/-- x·1 = x（可換環）。 -/
theorem valRingMulOne (K : IUTField) (x : K.carrier) : K.mul x K.one = x := by
  rw [K.mul_comm x K.one]; exact K.one_mul x

/-- v(-1) = 0（2·v(-1)=v(1)=0 より）。 -/
theorem valRing_v_negOne {K : IUTField} (val : valRingValuation K) :
    val.v (K.neg K.one) = some (0 : Int) := by
  have hmul : val.v (K.mul (K.neg K.one) (K.neg K.one))
      = valOptAdd (val.v (K.neg K.one)) (val.v (K.neg K.one)) := val.v_mul _ _
  rw [valRingNegOneMul K (K.neg K.one), valRingNegNeg K K.one, val.v_one] at hmul
  cases hvn : val.v (K.neg K.one) with
  | none => rw [hvn, valOptAdd_none_left] at hmul; nomatch hmul
  | some c =>
    rw [hvn, valOptAdd_some_some] at hmul
    have hc : (0 : Int) = c + c := Option.some.inj hmul
    have hc0 : c = 0 := by omega
    rw [hc0]

/-- **v(-x) = v(x)**（v(-x)=v((-1)·x)=v(-1)+v(x)=0+v(x)）。 -/
theorem valRing_v_neg {K : IUTField} (val : valRingValuation K) (x : K.carrier) :
    val.v (K.neg x) = val.v x := by
  rw [← valRingNegOneMul K x, val.v_mul, valRing_v_negOne val, valOptAdd_zero_left]

/-- **加法逆元で閉じる**: v(-x)=v(x)≥0。 -/
theorem valRing_neg_mem {K : IUTField} (val : valRingValuation K) (x : K.carrier)
    (hx : valRingMem val x) : valRingMem val (K.neg x) := by
  show valOptLe (some (0 : Int)) (val.v (K.neg x))
  rw [valRing_v_neg]
  exact hx

/-- **M301F-4 capstone: 付値環 O_v は部分環**（0,1∈O_v、和・積・差で閉じる）。 -/
theorem valRing_isSubring {K : IUTField} (val : valRingValuation K) :
    valRingMem val K.zero ∧ valRingMem val K.one ∧
    (∀ x y, valRingMem val x → valRingMem val y → valRingMem val (K.mul x y)) ∧
    (∀ x y, valRingMem val x → valRingMem val y → valRingMem val (K.add x y)) ∧
    (∀ x, valRingMem val x → valRingMem val (K.neg x)) :=
  ⟨valRing_zero_mem val, valRing_one_mem val, valRing_mul_mem val,
    valRing_add_mem val, valRing_neg_mem val⟩

/-! ## M301F-5: 極大イデアル m_v はイデアル -/

/-- 0 ∈ m_v（v(0)=∞≥1）。 -/
theorem valRingMax_zero_mem {K : IUTField} (val : valRingValuation K) :
    valRingMaxMem val K.zero := by
  show valOptLe (some (1 : Int)) (val.v K.zero)
  rw [val.v_zero]; exact True.intro

/-- **吸収律** O_v · m_v ⊆ m_v: v(x)≥0, v(y)≥1 なら v(xy)=v(x)+v(y)≥1。 -/
theorem valRingMax_absorb {K : IUTField} (val : valRingValuation K) (x y : K.carrier)
    (hx : valRingMem val x) (hy : valRingMaxMem val y) :
    valRingMaxMem val (K.mul x y) := by
  show valOptLe (some (1 : Int)) (val.v (K.mul x y))
  rw [val.v_mul]
  cases hvy : val.v y with
  | none =>
    cases hvx : val.v x with
    | none => rw [valOptAdd_none_left]; exact True.intro
    | some a => rw [valOptAdd_some_none]; exact True.intro
  | some b =>
    have hy' : valOptLe (some (1 : Int)) (val.v y) := hy
    rw [hvy] at hy'
    cases hvx : val.v x with
    | none => rw [valOptAdd_none_left]; exact True.intro
    | some a =>
      have hx' : valOptLe (some (0 : Int)) (val.v x) := hx
      rw [hvx] at hx'
      rw [valOptAdd_some_some]
      show (1 : Int) ≤ a + b
      have ha : (0 : Int) ≤ a := hx'
      have hb : (1 : Int) ≤ b := hy'
      omega

/-- **和で閉じる**: v(x)≥1, v(y)≥1 なら超距離不等式で v(x+y)≥1。 -/
theorem valRingMax_add_mem {K : IUTField} (val : valRingValuation K) (x y : K.carrier)
    (hx : valRingMaxMem val x) (hy : valRingMaxMem val y) :
    valRingMaxMem val (K.add x y) := by
  show valOptLe (some (1 : Int)) (val.v (K.add x y))
  cases val.v_add_ge x y with
  | inl h => exact valOptLe_trans hx h
  | inr h => exact valOptLe_trans hy h

/-! ## M301F-6: 付値環は局所環（O_v ∖ m_v は単元） -/

/-- O_v にあり m_v にない元は v(x)=0（0≤v かつ ¬(1≤v) ⟹ v=0）。 -/
theorem valRing_val_eq_zero_of_mem_not_max {K : IUTField} (val : valRingValuation K)
    (x : K.carrier) (hmem : valRingMem val x) (hmax : ¬ valRingMaxMem val x) :
    val.v x = some (0 : Int) := by
  cases hvx : val.v x with
  | none =>
    exfalso; apply hmax
    show valOptLe (some (1 : Int)) (val.v x)
    rw [hvx]; exact True.intro
  | some a =>
    have hmem' : valOptLe (some (0 : Int)) (val.v x) := hmem
    rw [hvx] at hmem'
    have hmax' : ¬ valOptLe (some (1 : Int)) (val.v x) := hmax
    rw [hvx] at hmax'
    have ha0 : (0 : Int) ≤ a := hmem'
    have ha : a = 0 := by
      have hnn : ¬ ((1 : Int) ≤ a) := hmax'
      omega
    rw [ha]

/-- **M301F-6: 局所環性** — O_v にあり m_v にない元 x は O_v の単元
    （v(x)=0 ⟹ v(x⁻¹)=0 ⟹ x⁻¹∈O_v、x·x⁻¹=1）。単元でない元は m_v に尽きる
    ＝ m_v が唯一の極大イデアル。 -/
theorem valRing_local_unit {K : IUTField} (val : valRingValuation K) (x : K.carrier)
    (hmem : valRingMem val x) (hmax : ¬ valRingMaxMem val x) :
    ∃ y, valRingMem val y ∧ K.mul x y = K.one := by
  have hvx : val.v x = some (0 : Int) :=
    valRing_val_eq_zero_of_mem_not_max val x hmem hmax
  have hx0 : x ≠ K.zero := by
    intro h
    have hz : val.v x = none := by rw [h]; exact val.v_zero
    rw [hvx] at hz; nomatch hz
  refine ⟨K.inv x, ?_, ?_⟩
  · have hv1 : val.v (K.mul x (K.inv x))
        = valOptAdd (val.v x) (val.v (K.inv x)) := val.v_mul x (K.inv x)
    rw [K.mul_inv_cancel x hx0, val.v_one, hvx, valOptAdd_zero_left] at hv1
    show valOptLe (some (0 : Int)) (val.v (K.inv x))
    rw [← hv1]; exact Int.le_refl 0
  · exact K.mul_inv_cancel x hx0

/-! ## M301F-7: 素元（uniformizer）が m_v を生成 -/

/-- π が素元 = v(π)=1。 -/
def valRingIsUniformizer {K : IUTField} (val : valRingValuation K) (π : K.carrier) : Prop :=
  val.v π = some (1 : Int)

/-- **M301F-7: 素元は m_v を生成** — v(π)=1 のとき、任意の x∈m_v（v(x)≥1）は
    π で割れる: x = y·π かつ y∈O_v（y=x·π⁻¹、v(y)=v(x)-1≥0）。 -/
theorem valRing_uniformizer_generates {K : IUTField} (val : valRingValuation K)
    (π : K.carrier) (hπ : val.v π = some (1 : Int)) (x : K.carrier)
    (hx : valRingMaxMem val x) :
    ∃ y, valRingMem val y ∧ x = K.mul y π := by
  have hπ0 : π ≠ K.zero := by
    intro h
    have hz : val.v π = none := by rw [h]; exact val.v_zero
    rw [hπ] at hz; nomatch hz
  cases hvx : val.v x with
  | none =>
    have hx0 : x = K.zero := val.v_eq_top x hvx
    refine ⟨K.zero, ?_, ?_⟩
    · show valOptLe (some (0 : Int)) (val.v K.zero)
      rw [val.v_zero]; exact True.intro
    · rw [hx0, K.mul_comm K.zero π, K.toCRing.mul_zero]
  | some m =>
    have hmax' : valOptLe (some (1 : Int)) (val.v x) := hx
    rw [hvx] at hmax'
    have hm : (1 : Int) ≤ m := hmax'
    have hvinv : val.v (K.inv π) = some (-1 : Int) := by
      have hv1 : val.v (K.mul π (K.inv π))
          = valOptAdd (val.v π) (val.v (K.inv π)) := val.v_mul π (K.inv π)
      rw [K.mul_inv_cancel π hπ0, val.v_one, hπ] at hv1
      cases hvi : val.v (K.inv π) with
      | none => rw [hvi, valOptAdd_some_none] at hv1; nomatch hv1
      | some c =>
        rw [hvi, valOptAdd_some_some] at hv1
        have hcc : (0 : Int) = 1 + c := Option.some.inj hv1
        have hc : c = -1 := by omega
        rw [hc]
    refine ⟨K.mul x (K.inv π), ?_, ?_⟩
    · show valOptLe (some (0 : Int)) (val.v (K.mul x (K.inv π)))
      rw [val.v_mul, hvx, hvinv, valOptAdd_some_some]
      show (0 : Int) ≤ m + (-1)
      omega
    · rw [K.mul_assoc x (K.inv π) π, K.inv_mul_cancel hπ0, valRingMulOne]

/-! ## M301F-8: 整閉性の核（外の元は非整） -/

/-- **M301F-8: 付値環は整閉（の核）** — v(x)=m<0（x∉O_v, x≠0）なら x⁻¹∈m_v。
    すなわち O_v の外の元 x は逆元が極大イデアルに落ちる。これは付値環が
    整閉整域（Frac=K の中で極大な部分環）であることの核となる事実。 -/
theorem valRing_notMem_inv_max {K : IUTField} (val : valRingValuation K) (x : K.carrier)
    (m : Int) (hvx : val.v x = some m) (hm : m < 0) :
    valRingMaxMem val (K.inv x) := by
  have hx0 : x ≠ K.zero := by
    intro h
    have hz : val.v x = none := by rw [h]; exact val.v_zero
    rw [hvx] at hz; nomatch hz
  have hvinv : val.v (K.inv x) = some (-m) := by
    have hv1 : val.v (K.mul x (K.inv x))
        = valOptAdd (val.v x) (val.v (K.inv x)) := val.v_mul x (K.inv x)
    rw [K.mul_inv_cancel x hx0, val.v_one, hvx] at hv1
    cases hvi : val.v (K.inv x) with
    | none => rw [hvi, valOptAdd_some_none] at hv1; nomatch hv1
    | some c =>
      rw [hvi, valOptAdd_some_some] at hv1
      have hcc : (0 : Int) = m + c := Option.some.inj hv1
      have hc : c = -m := by omega
      rw [hc]
  show valOptLe (some (1 : Int)) (val.v (K.inv x))
  rw [hvinv]
  show (1 : Int) ≤ -m
  omega

/-- **M301F-8b: 整閉性（骨組み）** — O_v は加法・乗法で閉じる（整な操作で不変）。
    monic 関係式による整閉包の全証明は後続（本層は v≥0 の保存を本物に）。 -/
theorem valRing_integrallyClosed {K : IUTField} (val : valRingValuation K) (x : K.carrier)
    (hx : valRingMem val x) : valRingMem val (K.mul x x) :=
  valRing_mul_mem val x x hx hx

/-! ## M301F-9: capstone — 付値環データ・DVR・実例（自明付値） -/

/-- **M301F-9a: 付値環の総括レコード** — 体 K・離散付値 val と、付値環 O_v が
    部分環（0,1∈O_v・積和差で閉）・m_v がイデアルを含む・局所環（O_v∖m_v が単元）を束ねる。 -/
structure ValuationRingData (K : IUTField) where
  /-- 台となる離散付値。 -/
  val : valRingValuation K
  /-- 0 ∈ O_v。 -/
  zero_mem : valRingMem val K.zero
  /-- 1 ∈ O_v。 -/
  one_mem : valRingMem val K.one
  /-- 積で閉じる。 -/
  mul_mem : ∀ x y, valRingMem val x → valRingMem val y → valRingMem val (K.mul x y)
  /-- 和で閉じる。 -/
  add_mem : ∀ x y, valRingMem val x → valRingMem val y → valRingMem val (K.add x y)
  /-- 差で閉じる。 -/
  neg_mem : ∀ x, valRingMem val x → valRingMem val (K.neg x)
  /-- 0 ∈ m_v。 -/
  max_zero_mem : valRingMaxMem val K.zero
  /-- 局所環性: O_v∖m_v は単元。 -/
  local_unit : ∀ x, valRingMem val x → ¬ valRingMaxMem val x →
    ∃ y, valRingMem val y ∧ K.mul x y = K.one

/-- **M301F-9b: 任意の離散付値から付値環データを組み立てる**。 -/
def valRing_toData {K : IUTField} (val : valRingValuation K) : ValuationRingData K where
  val := val
  zero_mem := valRing_zero_mem val
  one_mem := valRing_one_mem val
  mul_mem := valRing_mul_mem val
  add_mem := valRing_add_mem val
  neg_mem := valRing_neg_mem val
  max_zero_mem := valRingMax_zero_mem val
  local_unit := valRing_local_unit val

/-- **M301F-9c: 付値環は局所環**（総括: O_v∖m_v は単元＝ m_v が唯一の極大イデアル）。 -/
theorem valRing_is_local {K : IUTField} (data : ValuationRingData K) :
    ∀ x, valRingMem data.val x → ¬ valRingMaxMem data.val x →
      ∃ y, valRingMem data.val y ∧ K.mul x y = K.one :=
  data.local_unit

/-- **M301F-9d: 離散付値環（DVR）データ** — 付値 val・素元 π（v(π)=1）・
    π が m_v を生成することを束ねる。DVR = 局所 PID の骨格。 -/
structure DVRData (K : IUTField) where
  /-- 台となる離散付値。 -/
  val : valRingValuation K
  /-- 素元 π。 -/
  unif : K.carrier
  /-- v(π) = 1。 -/
  unif_val : val.v unif = some (1 : Int)
  /-- π が m_v を生成: 任意の x∈m_v は π で割れる。 -/
  generates : ∀ x, valRingMaxMem val x → ∃ y, valRingMem val y ∧ x = K.mul y unif

/-- **M301F-9e: 素元を持つ付値は DVR**（π 自身の具体構成は柱B ℤ_p 接続の後続。
    本定理は「π が在れば DVR 骨格が従う」という条件付き本物）。 -/
def valRing_dvr {K : IUTField} (val : valRingValuation K) (π : K.carrier)
    (hπ : val.v π = some (1 : Int)) : DVRData K where
  val := val
  unif := π
  unif_val := hπ
  generates := fun x hx => valRing_uniformizer_generates val π hπ x hx

/-! ### 実例: 自明付値（v≡0 on K*、O_v=K） -/

/-- **M301F-9f: 自明付値** — v(x) = 0（x≠0）, ∞（x=0）。整域性（IUTField）から
    v(xy)=v(x)+v(y) が従う。O_v=K（rank 0 の付値環）。 -/
def trivialValuation (K : IUTField) [DecidableEq K.carrier] : valRingValuation K where
  v := fun x => if x = K.zero then none else some (0 : Int)
  v_zero := by
    show (if K.zero = K.zero then none else some (0 : Int)) = none
    rw [if_pos rfl]
  v_one := by
    show (if K.one = K.zero then none else some (0 : Int)) = some (0 : Int)
    rw [if_neg K.one_ne_zero]
  v_mul := by
    intro x y
    show (if K.mul x y = K.zero then none else some (0 : Int))
        = valOptAdd (if x = K.zero then none else some (0 : Int))
            (if y = K.zero then none else some (0 : Int))
    split
    · rename_i hxy
      split
      · rfl
      · rename_i hx
        have hy : y = K.zero := K.eq_zero_of_mul_eq_zero_left hxy hx
        rw [if_pos hy, valOptAdd_some_none]
    · rename_i hxy
      have hx : x ≠ K.zero := by
        intro h; apply hxy; rw [h, K.mul_comm K.zero y, K.toCRing.mul_zero]
      have hy : y ≠ K.zero := by
        intro h; apply hxy; rw [h, K.toCRing.mul_zero]
      rw [if_neg hx, if_neg hy]
      show some (0 : Int) = some ((0 : Int) + 0)
      rw [Int.add_zero]
  v_add_ge := by
    intro x y
    show valOptLe (if x = K.zero then none else some (0 : Int))
          (if K.add x y = K.zero then none else some (0 : Int))
        ∨ valOptLe (if y = K.zero then none else some (0 : Int))
          (if K.add x y = K.zero then none else some (0 : Int))
    cases (inferInstance : Decidable (x = K.zero)) with
    | isTrue hx =>
      apply Or.inr
      have hadd : K.add x y = y := by rw [hx, K.zero_add]
      rw [hadd]
      exact valOptLe_refl _
    | isFalse hx =>
      apply Or.inl
      split
      · rename_i hx2; exact absurd hx2 hx
      · split
        · exact True.intro
        · exact Int.le_refl 0
  v_eq_top := by
    intro x hx
    have hx' : (if x = K.zero then none else some (0 : Int)) = none := hx
    split at hx'
    · rename_i h; exact h
    · rename_i h; nomatch hx'

/-- **M301F-9g: 付値環は存在する**（DecidableEq を持つ体上、自明付値から）。
    具体的な数体・ℚ_p の離散付値は柱B ℤ_p 接続の後続。 -/
theorem valRing_exists (K : IUTField) [DecidableEq K.carrier] :
    Nonempty (ValuationRingData K) :=
  ⟨valRing_toData (trivialValuation K)⟩

end IUT
