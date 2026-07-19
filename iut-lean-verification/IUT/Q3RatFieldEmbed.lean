/-
  IUT/Q3RatFieldEmbed.lean — A2c-4（柱A2: 実 p 進局所体 — ℚ↪ℚ₃ は体準同型）

  ── 主要成果の分類: **[実／(a) 昇格]**。既存の実環準同型 q3reMap : ratRing → q3Ring
     （A2c-3 Q3RatEmbed）と、実 ℚ の choice-free 逆元 qInv・体公理 qMul_inv
     （M115F-6・DecidableEq による全域化逆元）の上に、埋め込み ℚ↪ℚ₃ が
     **体準同型である**——非零有理数の像が ℚ₃ で可逆で、その逆元は有理逆元の像
     q3reMap(x⁻¹) に一致する——ことを本物 discharge する。toy 主語なし。
     主語は実 ratRing・実 q3Ring・実 qInv。

  complete_pct 影響: **A2 の named 恒久限定「∃逆元 CRing で体写像でない」を昇格**。
     A2c-3 は「∃-inverse を持つ CRing q3Ring への環準同型であって体射でない」と正直申告
     していた。本モジュールは ℚ-像に限れば真に体射であることを証明する:
     (i) q3re_map_inv — q3reMap(x)·q3reMap(x⁻¹)=1（非零有理数の逆元は像側で明示・
     ℚ 逆元の像に一致・choice-free）、(ii) q3reMap_unit — 非零有理数の像は ℚ₃ の単元、
     (iii) q3re_map_neg — 加法逆元保存、(iv) q3re_ker_trivial / q3reMap_injective —
     **核自明＝全単射（q3reMap は単射）**。これで ℚ-像は ℚ₃ の部分体（逆元で閉じた体）で
     あり、ℚ↪ℚ₃ は体埋め込みとして確立する。設計予測 A2 0.67→(監査確定・+ε)。

  * q3re_map_neg      — 加法逆元保存 q3reMap(−a)=−q3reMap(a)（add_left_cancel）
  * q3re_map_inv      — **★体準同型: q3reMap(x)·q3reMap(x⁻¹)=1（qMul_inv 消費）**
  * q3reMap_unit      — 非零有理数の像は ℚ₃ の単元（∃-inverse・逆元は ℚ-像内）
  * q3re_ker_trivial  — 核自明（表現子形: 像=0 ⟹ x=0）
  * q3re_ker_trivial' — 核自明（担体形）
  * q3reMap_injective — **★q3reMap の全単射（環準同型＋核自明＝単射）**
  * Q3RatFieldEmbedData — 総括レコード

  正直な限定（§3 準拠・消去/弱化しない）:
  - **q3Ring 全体はなお total-inverse IUTField ではない**（A2 恒久限定を継承）。
    体射性は **ℚ-像に限った** 命題であり、ℚ₃ の任意元の逆元計算は依然 witness 抽出
    （Markov）を要し choice-free に不能。本モジュールは「ℚ-像が ℚ₃ の部分体」までを
    主張し、ℚ₃ 全体の体構造は主張しない（この限定は消さない）。
  - **逆元は有理逆元の像**として明示: q3reMap(x⁻¹)。ℚ₃ 固有の（ℚ-像外の）元の逆元は
    範囲外。単射性は環準同型＋核自明の帰結で、全射性（ℚ₃ の全域被覆）は主張しない
    （ℚ₃ ⊋ ℚ の像）。
  - **p = 3 固定**・基礎体 ℚ のみ。ℚ₃ 上の位相・G_{ℚ₃}・分岐は範囲外（後続）。
  - 実 q3reMap・実 qInv・qMul_inv は既存（新設せず消費）。既存 surrogate は消さない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。
-/
import IUT.Q3RatEmbed

namespace IUT

/-! ## A2c-4-0: 加法逆元保存 -/

/-- **A2c-4-0: 加法逆元保存** q3reMap(−a) = −q3reMap(a)（環準同型の加法群部分）。 -/
theorem q3re_map_neg (a : ratRing.carrier) :
    q3reMap (ratRing.neg a) = q3Ring.neg (q3reMap a) := by
  apply q3Ring.add_left_cancel (a := q3reMap a)
  have hL : q3Ring.add (q3reMap a) (q3reMap (ratRing.neg a)) = q3Ring.zero := by
    rw [← q3re_map_add a (ratRing.neg a),
      ratRing.add_comm a (ratRing.neg a), ratRing.neg_add a, q3re_map_zero]
  have hR : q3Ring.add (q3reMap a) (q3Ring.neg (q3reMap a)) = q3Ring.zero := by
    rw [q3Ring.add_comm (q3reMap a) (q3Ring.neg (q3reMap a)), q3Ring.neg_add]
  rw [hL, hR]

/-! ## A2c-4-1: 体準同型 — 逆元保存 -/

/-- **A2c-4-1（★）: 体準同型（逆元保存）** — 非零有理数 x に対し
    q3reMap(x)·q3reMap(x⁻¹) = 1。逆元は有理逆元 qInv の像として明示（choice-free）。
    実 ℚ の体公理 qMul_inv と実環準同型 q3re_map_mul/q3re_map_one を消費する。
    これが A2c-3 の恒久限定「∃逆元 CRing で体写像でない」の ℚ-像上の昇格。 -/
theorem q3re_map_inv (x : PreRat) (hx : x.num ≠ 0) :
    q3Ring.mul (q3reMap (Quot.mk ratRel x)) (q3reMap (qInv (Quot.mk ratRel x)))
      = q3Ring.one := by
  have hstep : ratRing.mul (Quot.mk ratRel x) (qInv (Quot.mk ratRel x))
      = ratRing.one := qMul_inv x hx
  rw [← q3re_map_mul, hstep, q3re_map_one]

/-- **A2c-4-1b: 非零有理数の像は ℚ₃ の単元** — ∃ 形。逆元は ℚ-像内（q3reMap(x⁻¹)）。 -/
theorem q3reMap_unit (x : PreRat) (hx : x.num ≠ 0) :
    ∃ y : q3Ring.carrier, q3Ring.mul (q3reMap (Quot.mk ratRel x)) y = q3Ring.one :=
  ⟨q3reMap (qInv (Quot.mk ratRel x)), q3re_map_inv x hx⟩

/-! ## A2c-4-2: 核自明と単射性 -/

/-- **A2c-4-2a: 核自明（表現子形）** — 像が 0 なら有理数は 0。
    非零分子の像は非零（q3re_map_inj）の対偶。 -/
theorem q3re_ker_trivial (z : PreRat)
    (h : q3reMap (Quot.mk ratRel z) = q3Ring.zero) :
    Quot.mk ratRel z = ratRing.zero := by
  cases Decidable.em (z.num = 0) with
  | inl hz =>
    show Quot.mk ratRel z = Quot.mk ratRel prZero
    apply Quot.sound
    show z.num * prZero.den = prZero.num * z.den
    show z.num * 1 = 0 * z.den
    rw [hz, Int.zero_mul, Int.zero_mul]
  | inr hz => exact absurd h (q3re_map_inj z hz)

/-- **A2c-4-2b: 核自明（担体形）**。 -/
theorem q3re_ker_trivial' (c : ratRing.carrier)
    (h : q3reMap c = q3Ring.zero) : c = ratRing.zero := by
  revert h
  induction c using Quot.ind
  rename_i z
  intro h
  exact q3re_ker_trivial z h

/-- **A2c-4-2c（★）: q3reMap の単射性** — 環準同型＋核自明の帰結（体埋め込み）。
    a − b の像 = 0（q3re_map_add/q3re_map_neg・仮定 h）⟹ a − b = 0（核自明）⟹ a = b。 -/
theorem q3reMap_injective {a b : ratRing.carrier}
    (h : q3reMap a = q3reMap b) : a = b := by
  apply cring_eq_of_sub_zero ratRing
  refine q3re_ker_trivial' (ratRing.add a (ratRing.neg b)) ?_
  rw [q3re_map_add, q3re_map_neg, h,
    q3Ring.add_comm (q3reMap b) (q3Ring.neg (q3reMap b)), q3Ring.neg_add]

/-! ## A2c-4-3: 総括レコード -/

/-- **A2c-4-3a: 総括** — ℚ↪ℚ₃ は体埋め込み（逆元保存・単元性・加法逆元保存・
    核自明・単射）。ℚ-像が ℚ₃ の部分体であることの witness 束。 -/
structure Q3RatFieldEmbedData where
  /-- 環準同型 ratRing → q3Ring（A2c-3）。 -/
  map : ratRing.carrier → q3Ring.carrier
  /-- 体準同型: 非零有理数の逆元保存 map(x)·map(x⁻¹)=1。 -/
  map_inv : ∀ x : PreRat, x.num ≠ 0 →
    q3Ring.mul (map (Quot.mk ratRel x)) (map (qInv (Quot.mk ratRel x))) = q3Ring.one
  /-- 非零有理数の像は ℚ₃ の単元。 -/
  unit : ∀ x : PreRat, x.num ≠ 0 →
    ∃ y : q3Ring.carrier, q3Ring.mul (map (Quot.mk ratRel x)) y = q3Ring.one
  /-- 加法逆元保存。 -/
  map_neg : ∀ a, map (ratRing.neg a) = q3Ring.neg (map a)
  /-- 単射性（体埋め込み）。 -/
  inj : ∀ {a b : ratRing.carrier}, map a = map b → a = b

/-- **A2c-4-3b: witness**。 -/
noncomputable def q3reField_data : Q3RatFieldEmbedData where
  map := q3reMap
  map_inv := q3re_map_inv
  unit := q3reMap_unit
  map_neg := q3re_map_neg
  inj := q3reMap_injective

/-- **A2c-4-3c: 存在**。 -/
theorem q3reField_exists : Nonempty Q3RatFieldEmbedData := ⟨q3reField_data⟩

end IUT
