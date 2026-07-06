/-
  IUT/AbsTopMultMonoid.lean — M359F [実／本物]
  分類: 実 (AbsTopII 乗法モノイド O_v^▷ の復元＝(モノイド,付値,単数群))
  complete_pct 影響: 柱A を前進（AbsTop 系列の AbsTopII＝乗法モノイド O_v^▷=(O_v∖{0},×) と
    付値 v:O_v^▷→ℕ が本物のモノイド準同型・単数群 O_v^×=ker(v)・付値フィルトレーション、を
    本物で構成し M329F 体復元の乗法側を補完）。
  正直な限定: π₁ 位相からのモノイド復元・完全 AbsTopII アルゴリズムは外部仮説等。

  ── 位置づけ（AbsTop 系列）:
  * M325F `AbsTopMultAdd`     — 乗法群 K^× ＋付値 v から加法 x+y=x(1+x⁻¹y) を復元（核）
  * M329F `AbsTopFieldRecover`— 復元加法が体加法に一致し復元環＝元の体（体復元の完成）
  * M334F `CyclotomeRecovery` — χ から円分体 μ̂ を復元（円分剛性同型）
  * **M359F 本ファイル AbsTopII** — 乗法モノイド O_v^▷=(O_v∖{0},×,1) を本物のモノイドとして
    復元し、付値 v:O_v^▷→ℕ が本物のモノイド準同型（v(xy)=v(x)+v(y), v(1)=0）、
    単数群 O_v^×=ker(v)={v=0} が本物の群（可逆元＝degree 0）、付値フィルトレーション
    O_v^▷=⊔_d{v=d}（乗法は次数を加える）を core Lean のみで完全証明する。
    これは AbsTopI と AbsTopIII の間に座る「乗法モノイド＋付値」の復元であり、M329F の
    体復元が使う乗法構造 K.mul そのものを O_v^▷ 上のモノイド積として本物化する（乗法側の補完）。

  主要デクル:
  * M359F-1 `atmCarrier`/`atmMul`/`atmOne`/`atmCarrier_ext`
      — 乗法モノイド O_v^▷ の台（O_v の非零元）と積・単位・外延性
  * M359F-2 `atmCommMonoid`/`atmMonoid`（`atm_mul_assoc`/`atm_one_mul`/`atm_mul_one`/
      `atm_mul_comm`）— O_v^▷ が本物の可換モノイド（結合・単位・可換）
  * M359F-3 `atmValZ`/`atmValN`/`atmValZ_mul`/`atmValZ_one`/`atmValN_mul`/`atmValN_one`
      /`atmValMonoidHom` — 付値 v:O_v^▷→ℕ が本物のモノイド準同型（v(xy)=v(x)+v(y), v(1)=0）
  * M359F-4 `atmUnits`/`atm_units_one`/`atm_units_mul`/`atmUnitInv`/`atm_unit_mul_inv`
      /`atm_unit_iff`/`atm_units_is_group` — 単数群 O_v^×=ker(v)={v=0}（degree 0＝可逆元）
  * M359F-5 `atmMonoidFiltration`/`atm_grade_mul` — 付値フィルトレーション（乗法は次数を加える）
  * M359F-6 `AbsTopIIData`/`atm_toAbsTopIIData`/`atm_absTopII`/`atm_absTopII_mult_compat`
      — AbsTopII 復元 capstone（(モノイド,付値,単数群) を束ね、M329F 体復元の乗法側と整合）
  * M359F-7 `atmPi1ReconHypothesis`/`atm_pi1_reconstruction_hypothesis`
      — 外部仮説（π₁^ét からのモノイド復元・決して導出しない）
  * M359F-8 `atm_exists`/`atm_trivial_unit` + example

  正直な限定（消去・弱化禁止）:
  - **本物（完全証明・sorry 皆無・新規 Classical.choice 皆無）**: O_v^▷=(O_v∖{0},×,1) が
    本物の可換モノイド（結合・単位・可換）、付値 v:O_v^▷→ℕ が本物のモノイド準同型
    （v(xy)=v(x)+v(y), v(1)=0）、単数群 O_v^×={v=0}=ker(v) が可逆元とちょうど一致し
    （x 可逆 ⟺ v(x)=0）本物の群をなす（単位・積・逆元で閉じる）、付値フィルトレーション
    （乗法が次数を加える）、AbsTopII 復元データ、及び復元モノイド積が M329F の復元環の
    乗法 K.mul と一致すること（乗法側の整合）。
  - **正直申告（骨組み・後続・消さない）**:
    ・**π₁^ét 位相群からの乗法モノイド O_v^▷ の復元アルゴリズム**は骨組み。本モジュールは
      それを外部仮説 `atmPi1ReconHypothesis`（復元写像＋乗法保存）として**明示的に受け取り、
      決して導出しない**。実 π₁^ét からの抽出は柱A/E 後続。
    ・**完全 AbsTopII アルゴリズム**（mono-anabelian に O_v^▷ を位相群データのみから再構成する
      全体）は膨大ゆえ骨組み。ここは「O_v^▷ が本物のモノイド・付値準同型・単数群・
      フィルトレーションをなす代数的核」を本物で閉じる。
    ・具体的な数体・局所体の離散付値上での実例は柱B ℤ_p 接続の後続（本ファイルの実例は
      DecidableEq を持つ体上の自明付値 O_v=K で全非零元が単数となることを確認）。

  禁止タクティク不使用（cases/obtain/induction/rw/show/refine/exact/apply/intro/omega と
  if_neg のみ使用）。共有ファイル未変更（新規 1 本のみ・一般名は `atm` 接頭辞で衝突回避）。
-/
import IUT.AbsTopFieldRecover

namespace IUT

/-! ## M359F-1: 乗法モノイド O_v^▷ の台（O_v の非零元）・積・単位・外延性 -/

/-- **M359F-1a: 乗法モノイド O_v^▷ の台** — 付値環 O_v の**非零**元
    （elem∈O_v かつ elem≠0）。乗法モノイド O_v^▷=(O_v∖{0},×) の元。 -/
structure atmCarrier {K : IUTField} (val : valRingValuation K) where
  /-- 台となる体の元。 -/
  elem : K.carrier
  /-- O_v に属す（v(elem)≥0）。 -/
  mem : valRingMem val elem
  /-- 非零（O^▷ = O∖{0}）。 -/
  ne_zero : elem ≠ K.zero

/-- **M359F-1b: 外延性** — elem が等しければ O_v^▷ の元として等しい
    （mem・ne_zero は Prop ゆえ証明無関係）。 -/
theorem atmCarrier_ext {K : IUTField} {val : valRingValuation K} {x y : atmCarrier val}
    (h : x.elem = y.elem) : x = y := by
  cases x with
  | mk e1 m1 n1 =>
    cases y with
    | mk e2 m2 n2 =>
      cases h
      rfl

/-- **M359F-1c: モノイド積** — O_v^▷ の乗法（体の乗法 K.mul の制限）。
    O_v は積で閉じ（`valRing_mul_mem`）、非零の積は非零（整域性 `mul_ne_zero`）。 -/
def atmMul {K : IUTField} (val : valRingValuation K) (x y : atmCarrier val) : atmCarrier val where
  elem := K.mul x.elem y.elem
  mem := valRing_mul_mem val x.elem y.elem x.mem y.mem
  ne_zero := K.mul_ne_zero x.ne_zero y.ne_zero

/-- **M359F-1d: モノイド単位** — 1∈O_v^▷（v(1)=0≥0, 1≠0）。 -/
def atmOne {K : IUTField} (val : valRingValuation K) : atmCarrier val where
  elem := K.one
  mem := valRing_one_mem val
  ne_zero := K.one_ne_zero

/-! ## M359F-2: O_v^▷ は本物の可換モノイド -/

/-- **M359F-2a: 結合律** — (x·y)·z = x·(y·z)（体の乗法結合律から）。 -/
theorem atm_mul_assoc {K : IUTField} (val : valRingValuation K) (x y z : atmCarrier val) :
    atmMul val (atmMul val x y) z = atmMul val x (atmMul val y z) :=
  atmCarrier_ext (K.mul_assoc x.elem y.elem z.elem)

/-- **M359F-2b: 左単位律** — 1·x = x。 -/
theorem atm_one_mul {K : IUTField} (val : valRingValuation K) (x : atmCarrier val) :
    atmMul val (atmOne val) x = x :=
  atmCarrier_ext (K.one_mul x.elem)

/-- **M359F-2c: 右単位律** — x·1 = x。 -/
theorem atm_mul_one {K : IUTField} (val : valRingValuation K) (x : atmCarrier val) :
    atmMul val x (atmOne val) = x :=
  atmCarrier_ext (valRingMulOne K x.elem)

/-- **M359F-2d: 可換律** — x·y = y·x。 -/
theorem atm_mul_comm {K : IUTField} (val : valRingValuation K) (x y : atmCarrier val) :
    atmMul val x y = atmMul val y x :=
  atmCarrier_ext (K.mul_comm x.elem y.elem)

/-- **M359F-2e: 可換モノイドの公理束** — 台・積・単位と結合・単位・可換律。 -/
structure atmCommMonoid where
  /-- 台。 -/
  carrier : Type
  /-- 積。 -/
  mul : carrier → carrier → carrier
  /-- 単位。 -/
  one : carrier
  /-- 結合律。 -/
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  /-- 左単位律。 -/
  one_mul : ∀ a, mul one a = a
  /-- 右単位律。 -/
  mul_one : ∀ a, mul a one = a
  /-- 可換律。 -/
  mul_comm : ∀ a b, mul a b = mul b a

/-- **M359F-2f: 乗法モノイド O_v^▷** — O_v の非零元がなす**本物の可換モノイド**。
    AbsTopII の主対象。 -/
def atmMonoid {K : IUTField} (val : valRingValuation K) : atmCommMonoid where
  carrier := atmCarrier val
  mul := atmMul val
  one := atmOne val
  mul_assoc := atm_mul_assoc val
  one_mul := atm_one_mul val
  mul_one := atm_mul_one val
  mul_comm := atm_mul_comm val

/-! ## M359F-3: 付値 v:O_v^▷→ℕ は本物のモノイド準同型 -/

/-- **M359F-3a: 非零元の付値は有限かつ非負** — elem∈O_v∖{0} なら v(elem)=some a, a≥0。 -/
theorem atm_v_some {K : IUTField} (val : valRingValuation K) (x : K.carrier)
    (hmem : valRingMem val x) (hne : x ≠ K.zero) :
    ∃ a : Int, val.v x = some a ∧ (0 : Int) ≤ a := by
  cases hvx : val.v x with
  | none => exact absurd (val.v_eq_top x hvx) hne
  | some a =>
    refine ⟨a, rfl, ?_⟩
    have hmem' : valOptLe (some (0 : Int)) (val.v x) := hmem
    rw [hvx] at hmem'
    exact hmem'

/-- **M359F-3b: 整数値付値** v:O_v^▷→ℤ（非零元の有限値）。 -/
def atmValZ {K : IUTField} (val : valRingValuation K) (x : atmCarrier val) : Int :=
  Option.getD (val.v x.elem) 0

/-- **M359F-3c: 付値の some 形** — v(elem) = some (atmValZ x)。 -/
theorem atmValZ_eq {K : IUTField} (val : valRingValuation K) (x : atmCarrier val) :
    val.v x.elem = some (atmValZ val x) := by
  obtain ⟨a, ha, _⟩ := atm_v_some val x.elem x.mem x.ne_zero
  show val.v x.elem = some (Option.getD (val.v x.elem) 0)
  rw [ha]
  rfl

/-- **M359F-3d: 付値の非負性** — atmValZ x ≥ 0（O_v の元）。 -/
theorem atmValZ_nonneg {K : IUTField} (val : valRingValuation K) (x : atmCarrier val) :
    (0 : Int) ≤ atmValZ val x := by
  obtain ⟨a, ha, hn⟩ := atm_v_some val x.elem x.mem x.ne_zero
  show (0 : Int) ≤ Option.getD (val.v x.elem) 0
  rw [ha]
  exact hn

/-- **M359F-3e: 乗法性（ℤ）** — atmValZ(x·y) = atmValZ x + atmValZ y。付値公理 v_mul から。 -/
theorem atmValZ_mul {K : IUTField} (val : valRingValuation K) (x y : atmCarrier val) :
    atmValZ val (atmMul val x y) = atmValZ val x + atmValZ val y := by
  obtain ⟨a, ha, _⟩ := atm_v_some val x.elem x.mem x.ne_zero
  obtain ⟨b, hb, _⟩ := atm_v_some val y.elem y.mem y.ne_zero
  have hxa : atmValZ val x = a := by
    show Option.getD (val.v x.elem) 0 = a
    rw [ha]
    rfl
  have hyb : atmValZ val y = b := by
    show Option.getD (val.v y.elem) 0 = b
    rw [hb]
    rfl
  show Option.getD (val.v (K.mul x.elem y.elem)) 0 = atmValZ val x + atmValZ val y
  rw [hxa, hyb, val.v_mul, ha, hb, valOptAdd_some_some]
  rfl

/-- **M359F-3f: 単位の付値（ℤ）** — atmValZ 1 = 0（v(1)=0）。 -/
theorem atmValZ_one {K : IUTField} (val : valRingValuation K) :
    atmValZ val (atmOne val) = 0 := by
  show Option.getD (val.v K.one) 0 = 0
  rw [val.v_one]
  rfl

/-- **M359F-3g: 自然数値付値** v:O_v^▷→ℕ（degree, 非負値の toNat）。 -/
def atmValN {K : IUTField} (val : valRingValuation K) (x : atmCarrier val) : Nat :=
  (atmValZ val x).toNat

/-- **M359F-3h: 乗法性（ℕ）** — v(x·y) = v(x)+v(y)（ℕ の加法）。 -/
theorem atmValN_mul {K : IUTField} (val : valRingValuation K) (x y : atmCarrier val) :
    atmValN val (atmMul val x y) = atmValN val x + atmValN val y := by
  have hx := atmValZ_nonneg val x
  have hy := atmValZ_nonneg val y
  have hmul := atmValZ_mul val x y
  show (atmValZ val (atmMul val x y)).toNat = (atmValZ val x).toNat + (atmValZ val y).toNat
  rw [hmul]
  omega

/-- **M359F-3i: 単位の付値（ℕ）** — v(1) = 0。 -/
theorem atmValN_one {K : IUTField} (val : valRingValuation K) :
    atmValN val (atmOne val) = 0 := by
  show (atmValZ val (atmOne val)).toNat = 0
  rw [atmValZ_one]
  rfl

/-- **M359F-3j: 付値モノイド準同型データ** — v:O_v^▷→(ℕ,+,0)。 -/
structure atmValMonoidHomData {K : IUTField} (val : valRingValuation K) where
  /-- 付値関数 O_v^▷ → ℕ。 -/
  toFun : atmCarrier val → Nat
  /-- 乗法性: v(x·y)=v(x)+v(y)。 -/
  map_mul : ∀ x y, toFun (atmMul val x y) = toFun x + toFun y
  /-- 単位: v(1)=0。 -/
  map_one : toFun (atmOne val) = 0

/-- **M359F-3k: 付値モノイド準同型** — v:O_v^▷→ℕ は本物のモノイド準同型。 -/
def atmValMonoidHom {K : IUTField} (val : valRingValuation K) : atmValMonoidHomData val where
  toFun := atmValN val
  map_mul := atmValN_mul val
  map_one := atmValN_one val

/-! ## M359F-4: 単数群 O_v^× = ker(v) = {v=0}（degree 0＝可逆元） -/

/-- **M359F-4a: 単数（degree 0）** — O_v^× = {x∈O_v^▷ | v(x)=0} = ker(v)。 -/
def atmUnits {K : IUTField} (val : valRingValuation K) (x : atmCarrier val) : Prop :=
  atmValN val x = 0

/-- **M359F-4b: 単位は単数** — v(1)=0。 -/
theorem atm_units_one {K : IUTField} (val : valRingValuation K) :
    atmUnits val (atmOne val) :=
  atmValN_one val

/-- **M359F-4c: 単数は積で閉じる** — v(x)=v(y)=0 ⟹ v(x·y)=0（部分モノイド）。 -/
theorem atm_units_mul {K : IUTField} (val : valRingValuation K) (x y : atmCarrier val)
    (hx : atmUnits val x) (hy : atmUnits val y) : atmUnits val (atmMul val x y) := by
  have hx' : atmValN val x = 0 := hx
  have hy' : atmValN val y = 0 := hy
  show atmValN val (atmMul val x y) = 0
  rw [atmValN_mul, hx', hy']

/-- **M359F-4d: 付値 0 なら逆元の付値も 0** — v(x)=0 ⟹ v(x⁻¹)=0（M325F v(x⁻¹)=-v(x)）。 -/
theorem atm_v_inv_zero {K : IUTField} (val : valRingValuation K) (x : K.carrier)
    (hv : val.v x = some (0 : Int)) : val.v (K.inv x) = some (0 : Int) := by
  have h := absTop_v_inv val x 0 hv
  have e : (-(0 : Int)) = 0 := by omega
  rw [e] at h
  exact h

/-- **M359F-4e: 単数の逆元** — v(x)=0 の x に対し体逆元 x⁻¹ も O_v^▷ の元（v(x⁻¹)=0）。 -/
def atmUnitInv {K : IUTField} (val : valRingValuation K) (x : atmCarrier val)
    (hz : atmValZ val x = 0) : atmCarrier val where
  elem := K.inv x.elem
  mem := by
    have hv : val.v x.elem = some 0 := by
      have he := atmValZ_eq val x
      rw [hz] at he
      exact he
    show valOptLe (some (0 : Int)) (val.v (K.inv x.elem))
    rw [atm_v_inv_zero val x.elem hv]
    exact Int.le_refl 0
  ne_zero := K.inv_ne_zero x.ne_zero

/-- **M359F-4f: 逆元の積は単位** — x·x⁻¹ = 1（体の逆元公理）。 -/
theorem atm_unit_mul_inv {K : IUTField} (val : valRingValuation K) (x : atmCarrier val)
    (hz : atmValZ val x = 0) : atmMul val x (atmUnitInv val x hz) = atmOne val := by
  apply atmCarrier_ext
  show K.mul x.elem (K.inv x.elem) = K.one
  exact K.mul_inv_cancel x.elem x.ne_zero

/-- **M359F-4g: 逆元も単数** — v(x⁻¹)=0（degree 0 は逆元で閉じる）。 -/
theorem atmValZ_unitInv {K : IUTField} (val : valRingValuation K) (x : atmCarrier val)
    (hz : atmValZ val x = 0) : atmValZ val (atmUnitInv val x hz) = 0 := by
  have hv : val.v x.elem = some 0 := by
    have he := atmValZ_eq val x
    rw [hz] at he
    exact he
  show Option.getD (val.v (K.inv x.elem)) 0 = 0
  rw [atm_v_inv_zero val x.elem hv]
  rfl

/-- **M359F-4h: 逆元は単数** — atmUnitInv は再び単数（O_v^× は逆元で閉じる）。 -/
theorem atm_unitInv_is_unit {K : IUTField} (val : valRingValuation K) (x : atmCarrier val)
    (hz : atmValZ val x = 0) : atmUnits val (atmUnitInv val x hz) := by
  show (atmValZ val (atmUnitInv val x hz)).toNat = 0
  rw [atmValZ_unitInv]
  rfl

/-- **M359F-4i: 単数 ⟹ atmValZ=0** — degree 0（ℕ）から ℤ 値 0 を取り出す。 -/
theorem atm_valZ_eq_zero_of_unit {K : IUTField} (val : valRingValuation K) (x : atmCarrier val)
    (h : atmUnits val x) : atmValZ val x = 0 := by
  have hn := atmValZ_nonneg val x
  have h' : (atmValZ val x).toNat = 0 := h
  omega

/-- **M359F-4j: 単数 ⟺ 可逆** — x∈O_v^× ⟺ x はモノイド O_v^▷ の可逆元
    （∃y, x·y=1）。「単数群＝可逆元群」を本物に閉じる。 -/
theorem atm_unit_iff {K : IUTField} (val : valRingValuation K) (x : atmCarrier val) :
    atmUnits val x ↔ ∃ y, atmMul val x y = atmOne val := by
  apply Iff.intro
  · intro h
    have hz : atmValZ val x = 0 := atm_valZ_eq_zero_of_unit val x h
    exact ⟨atmUnitInv val x hz, atm_unit_mul_inv val x hz⟩
  · intro h
    obtain ⟨y, hy⟩ := h
    have h1 : atmValZ val (atmMul val x y) = atmValZ val (atmOne val) :=
      congrArg (atmValZ val) hy
    rw [atmValZ_mul, atmValZ_one] at h1
    have hx := atmValZ_nonneg val x
    have hy2 := atmValZ_nonneg val y
    show (atmValZ val x).toNat = 0
    omega

/-- **M359F-4k: 単数群データ** — O_v^× が単位を含み・積で閉じ・各元が単数な逆元を持つ
    （本物の群構造）。 -/
structure atmUnitGroupData {K : IUTField} (val : valRingValuation K) where
  /-- 単位は単数。 -/
  one_unit : atmUnits val (atmOne val)
  /-- 単数は積で閉じる。 -/
  mul_unit : ∀ x y, atmUnits val x → atmUnits val y → atmUnits val (atmMul val x y)
  /-- 各単数の逆元。 -/
  inv : ∀ x, atmUnits val x → atmCarrier val
  /-- 逆元も単数。 -/
  inv_unit : ∀ x (h : atmUnits val x), atmUnits val (inv x h)
  /-- 逆元の積は単位。 -/
  mul_inv : ∀ x (h : atmUnits val x), atmMul val x (inv x h) = atmOne val

/-- **M359F-4l: 単数群の構成** — O_v^× は本物の群をなす。 -/
def atm_units_group {K : IUTField} (val : valRingValuation K) : atmUnitGroupData val where
  one_unit := atm_units_one val
  mul_unit := atm_units_mul val
  inv := fun x h => atmUnitInv val x (atm_valZ_eq_zero_of_unit val x h)
  inv_unit := fun x h => atm_unitInv_is_unit val x (atm_valZ_eq_zero_of_unit val x h)
  mul_inv := fun x h => atm_unit_mul_inv val x (atm_valZ_eq_zero_of_unit val x h)

/-- **M359F-4m: 単数群は存在する**（本物の群）。 -/
theorem atm_units_is_group {K : IUTField} (val : valRingValuation K) :
    Nonempty (atmUnitGroupData val) :=
  ⟨atm_units_group val⟩

/-! ## M359F-5: 付値フィルトレーション O_v^▷ = ⊔_d {v=d}（乗法は次数を加える） -/

/-- **M359F-5a: 次数付き乗法** — v(x)=d, v(y)=e ⟹ v(x·y)=d+e（乗法は degree を加える）。 -/
theorem atm_grade_mul {K : IUTField} (val : valRingValuation K) (x y : atmCarrier val)
    (d e : Nat) (hx : atmValN val x = d) (hy : atmValN val y = e) :
    atmValN val (atmMul val x y) = d + e := by
  rw [atmValN_mul, hx, hy]

/-- **M359F-5b: 付値フィルトレーションデータ** — degree = v、全域被覆（各 x は degree x に属す）、
    次数付き乗法、単数=degree 0。 -/
structure atmFiltrationData {K : IUTField} (val : valRingValuation K) where
  /-- 次数関数 = 付値。 -/
  degree : atmCarrier val → Nat
  /-- degree は付値 v。 -/
  degree_is : degree = atmValN val
  /-- 全域被覆: 各元は自身の次数に属す（O_v^▷=⊔_d{v=d}）。 -/
  cover : ∀ x, ∃ d, degree x = d
  /-- 乗法は次数を加える。 -/
  graded_mul : ∀ x y d e, degree x = d → degree y = e → degree (atmMul val x y) = d + e
  /-- 単数 = degree 0 部分。 -/
  units_are_deg0 : ∀ x, atmUnits val x ↔ degree x = 0

/-- **M359F-5c: 付値フィルトレーションの構成**。 -/
def atmMonoidFiltration {K : IUTField} (val : valRingValuation K) : atmFiltrationData val where
  degree := atmValN val
  degree_is := rfl
  cover := fun x => ⟨atmValN val x, rfl⟩
  graded_mul := fun x y d e hx hy => atm_grade_mul val x y d e hx hy
  units_are_deg0 := fun _ => Iff.rfl

/-! ## M359F-6: AbsTopII 復元 capstone — (モノイド, 付値, 単数群) -/

/-- **M359F-6a: AbsTopII 復元データ** — 乗法モノイド O_v^▷・付値モノイド準同型 v:O_v^▷→ℕ・
    単数群 O_v^×=ker(v) を束ねた mono-anabelian AbsTopII の復元対象。 -/
structure AbsTopIIData {K : IUTField} (val : valRingValuation K) where
  /-- 復元した乗法モノイド O_v^▷。 -/
  mon : atmCommMonoid
  /-- モノイドは atmMonoid（O_v の非零元の本物のモノイド）に一致。 -/
  mon_is : mon = atmMonoid val
  /-- 付値モノイド準同型 v:O_v^▷→ℕ。 -/
  valHom : atmValMonoidHomData val
  /-- 付値準同型は atmValN。 -/
  valHom_is : valHom.toFun = atmValN val
  /-- 単数（degree 0）述語。 -/
  unit : atmCarrier val → Prop
  /-- 単数 = ker(v)（{v=0}）。 -/
  unit_ker : ∀ x, unit x ↔ atmValN val x = 0
  /-- 単数 = 可逆元。 -/
  unit_iff_inv : ∀ x, unit x ↔ ∃ y, atmMul val x y = atmOne val

/-- **M359F-6b: AbsTopII 復元データの構成** — 任意の離散付値から (モノイド,付値,単数群) を復元。 -/
def atm_toAbsTopIIData {K : IUTField} (val : valRingValuation K) : AbsTopIIData val where
  mon := atmMonoid val
  mon_is := rfl
  valHom := atmValMonoidHom val
  valHom_is := rfl
  unit := atmUnits val
  unit_ker := fun _ => Iff.rfl
  unit_iff_inv := fun x => atm_unit_iff val x

/-- **M359F-6c: AbsTopII 復元定理（capstone）** — 離散付値 val から乗法モノイド O_v^▷ を
    本物のモノイドとして復元し、付値 v:O_v^▷→ℕ が本物のモノイド準同型、単数群 O_v^×=ker(v)
    がちょうど可逆元と一致することを束ねる。AbsTopI と AbsTopIII の間の「乗法モノイド＋付値」の
    復元（π₁^ét からの復元アルゴリズムは外部仮説・ヘッダの正直な限定参照）。 -/
theorem atm_absTopII {K : IUTField} (val : valRingValuation K) :
    ∃ D : AbsTopIIData val,
      D.mon = atmMonoid val ∧
      D.valHom.toFun = atmValN val ∧
      (∀ x, D.unit x ↔ ∃ y, atmMul val x y = atmOne val) :=
  ⟨atm_toAbsTopIIData val, rfl, rfl, atm_unit_iff val⟩

/-- **M359F-6d: M329F 体復元との乗法整合** — 復元モノイド O_v^▷ の積は、M329F の復元環
    `absFRecoveredRing`（＝元の体 K）の乗法 K.mul そのものである。すなわち本 AbsTopII で
    復元した乗法モノイドは体復元の**乗法側**を与える（乗法側の補完）。 -/
theorem atm_absTopII_mult_compat {K : IUTField} [DecidableEq K.carrier]
    (val : valRingValuation K) (x y : atmCarrier val) :
    (absFRecoveredRing K).mul x.elem y.elem = (atmMul val x y).elem :=
  rfl

/-! ## M359F-7: 外部仮説（π₁^ét からのモノイド復元・決して導出しない） -/

/-- **M359F-7a: π₁^ét モノイド復元仮説** — π₁^ét 位相群 G から乗法モノイド O_v^▷ への
    復元写像（乗法を保存）。実 π₁^ét からの抽出アルゴリズムは本モジュール外＝**外部仮説**
    として受け取り、決して導出しない（正直な限定）。 -/
structure atmPi1ReconHypothesis {K : IUTField} (val : valRingValuation K) (G : Grp) where
  /-- π₁^ét の元から O_v^▷ の元への復元写像（外部アルゴリズム）。 -/
  recon : G.carrier → atmCarrier val
  /-- 復元は乗法を保存する（外部仮説・本モジュールでは導出しない）。 -/
  recon_mul : ∀ g h, recon (G.mul g h) = atmMul val (recon g) (recon h)

/-- **M359F-7b: 復元像の付値は加法的（仮説からの帰結）** — π₁^ét 復元仮説を**受け取れば**、
    復元像の付値が G の積で加法的になる（v(recon(gh))=v(recon g)+v(recon h)）。仮説は
    決して導出せず、その帰結のみを本物で示す。 -/
theorem atm_pi1_reconstruction_hypothesis {K : IUTField} (val : valRingValuation K) (G : Grp)
    (hyp : atmPi1ReconHypothesis val G) (g h : G.carrier) :
    atmValN val (hyp.recon (G.mul g h))
      = atmValN val (hyp.recon g) + atmValN val (hyp.recon h) := by
  rw [hyp.recon_mul, atmValN_mul]

/-! ## M359F-8: 実例・存在 -/

/-- **M359F-8a: 自明付値では全非零元が単数** — O_v=K（rank 0 付値）では v≡0 なので
    O_v^▷ の全元が単数 O_v^×（degree 0）。実例（DecidableEq を持つ体上）。 -/
theorem atm_trivial_unit {K : IUTField} [DecidableEq K.carrier]
    (x : atmCarrier (trivialValuation K)) : atmUnits (trivialValuation K) x := by
  have hv : (trivialValuation K).v x.elem = some (0 : Int) := by
    show (if x.elem = K.zero then none else some (0 : Int)) = some 0
    rw [if_neg x.ne_zero]
  have hz : atmValZ (trivialValuation K) x = 0 := by
    show Option.getD ((trivialValuation K).v x.elem) 0 = 0
    rw [hv]
    rfl
  show (atmValZ (trivialValuation K) x).toNat = 0
  rw [hz]
  rfl

/-- **M359F-8b: AbsTopII 復元データは存在する**（DecidableEq を持つ体上、自明付値から）。
    具体的な数体・局所体の離散付値上での復元は柱B ℤ_p 接続の後続。 -/
theorem atm_exists (K : IUTField) [DecidableEq K.carrier] :
    Nonempty (AbsTopIIData (trivialValuation K)) :=
  ⟨atm_toAbsTopIIData (trivialValuation K)⟩

/-- **M359F-8c: 実例** — 乗法モノイド O_v^▷ の単位 1 は単数（degree 0）。 -/
example {K : IUTField} (val : valRingValuation K) : atmUnits val (atmOne val) :=
  atm_units_one val

end IUT
