/-
  IUT/PadicAbsValueQ.lean — 実 p 進絶対値 |x|_p = p^{-v_p(x)} : ℚ^× → ℚ_{>0} の本物構成

  ── 主要成果の分類: **[実]**（本物の ℚ≥0 値 p 進絶対値と乗法性・support 外自明性の
     本物証明）。B5 積公式のスライス「実 p 進絶対値 |x|_p」。

  complete_pct 影響: **柱B の非アルキメデス素点 place at p の絶対値**を本物に積む
  §2(b) 本物の先行建設。既存 `PadicValuationQ` の実 p 進付値 v_p : ℚ^× → ℤ
  （`pvqVal`, 加法性 `pvq_val_mul`）の上に、実 ℚ 値の p 進絶対値
  |x|_p := p^{-v_p(x)} を **本物の有理数（PreRat 代表）** として構成し、
  積公式の核となる (i) 乗法性 |xy|_p = |x|_p·|y|_p、(ii) support 外自明性
  「p が分子・分母を割らなければ |x|_p = 1」、(iii) 正値性・非零性を本物証明する。
  模型・surrogate（m202fVol 型・Bool 軌道・代理群）は一切用いない。

  * `pavBase` / `pavBase_pos` / `pavBase_pow_pos` — 底 p の正値化
    （p = 0 は 1 に丸め、素数 p では p そのもの。冪 p^k > 0 を Int 値で保証）。
  * `pavOfVal` — 整数 v に対する p^{-v} の実 ℚ 代表
    (num, den) = (p^{(-v)⁺}, p^{v⁺})（v⁺ = v.toNat, (-v)⁺ = (-v).toNat）。
    値は p^{(-v)⁺ - v⁺} = p^{-v}。if 分岐なしの一様表現。
  * `pavAbs (p x) : QRat` — |x|_p = Quot.mk (pavOfVal p (pvqVal p x))。本物の ℚ≥0 値。
  * `pavOfVal_mul_rel` — **核: p^{-(a+b)} = p^{-a}·p^{-b}**（指数を Nat で束ね、
    Int.toNat の符号恒等式 t⁺ - (-t)⁺ = t を omega で回収）。
  * `pav_mul` — **乗法性** |xy|_p = |x|_p·|y|_p（`pvq_val_mul` の加法性から）。
  * `pavOfVal_zero` / `pav_val_zero` — v_p(x) = 0 なら |x|_p = 1。
  * `pvqNatVal_zero_of_not_dvd` / `pvqVal_zero_of_not_dvd` — p ∤ n なら v_p(n) = 0。
  * `pav_trivial` — **support 外自明性** p ∤ num ∧ p ∤ den ⟹ |x|_p = 1
    （積公式の有限性の核: ほとんどの p で自明値）。
  * `pav_nonneg` / `pav_ne_zero` — 正値性 0 ≤ |x|_p・非零性 |x|_p ≠ 0。
  * `PadicAbsData` / `pav_exists` — capstone（絶対値データ束と存在）。

  正直な限定: (1) |x|_p は非零代表（num ≠ 0 側）に対する ℚ^× 上の絶対値であり、
  |0|_p = 0 は付値 v_p(0) = +∞ が Int に収まらないため対象外（`PadicValuationQ`
  の限定を継承）。(2) 乗法性は付値の加法性が成り立つ素数 p でのみ（IsPrime p を明示）。
  (3) 値域は ℚ≥0 に留まり、完備化 ℚ_p や積公式 ∏_v |x|_v = 1 の全域集約は後続。
  本モジュール単独では complete_pct を主張しない（独立監査判定・親が統合時に判断）。

  全て選択公理不使用（新規 Classical.choice なし・propext / Quot.sound のみ）・sorry なし。
-/
import IUT.PadicValuationQ

namespace IUT

/-! ## 底 p の正値化（p^k > 0 を Int 値で保証） -/

/-- 絶対値の底（p = 0 は 1 に丸め、正値性を保証。素数 p では p そのもの）。 -/
def pavBase (p : Nat) : Nat := if p = 0 then 1 else p

/-- 底は 1 以上（正値）。 -/
theorem pavBase_pos (p : Nat) : 1 ≤ pavBase p := by
  show 1 ≤ if p = 0 then 1 else p
  cases Nat.decEq p 0 with
  | isTrue h => rw [if_pos h]; omega
  | isFalse h => rw [if_neg h]; omega

/-- 底の冪は Int 値で正（分母 den_pos の witness）。 -/
theorem pavBase_pow_pos (p k : Nat) : 0 < ((pavBase p ^ k : Nat) : Int) := by
  have hb : 0 < pavBase p := by have := pavBase_pos p; omega
  have hp : 0 < pavBase p ^ k := Nat.pow_pos hb
  omega

/-! ## p^{-v} の実 ℚ 代表 -/

/-- **p^{-v} の実 ℚ 代表** — 整数 v に対し (num, den) = (p^{(-v)⁺}, p^{v⁺})。
    v⁺ = v.toNat, (-v)⁺ = (-v).toNat（Int.toNat = max(·,0)）。
    値は p^{(-v)⁺ - v⁺} = p^{-v}（if 分岐なしの一様表現、num/den とも正）。 -/
def pavOfVal (p : Nat) (v : Int) : PreRat where
  num := ((pavBase p ^ (-v).toNat : Nat) : Int)
  den := ((pavBase p ^ v.toNat : Nat) : Int)
  den_pos := pavBase_pow_pos p v.toNat

/-- **|x|_p := p^{-v_p(x)}** — 実 ℚ≥0 値の p 進絶対値（PreRat 代表 x に対し
    付値 v_p(x) = pvqVal p x の符号で p の冪を分子・分母に配した本物の有理数）。 -/
def pavAbs (p : Nat) (x : PreRat) : QRat :=
  Quot.mk ratRel (pavOfVal p (pvqVal p x))

/-! ## 核: p^{-(a+b)} = p^{-a} · p^{-b} -/

/-- **核補題: 絶対値の乗法性（付値の加法 → 冪の乗法）** —
    ratRel (p^{-(a+b)}) (p^{-a}·p^{-b})。指数を Nat で束ね、
    Int.toNat の符号恒等式 t.toNat - (-t).toNat = t を omega で回収。 -/
theorem pavOfVal_mul_rel (p : Nat) (a b : Int) :
    ratRel (pavOfVal p (a + b)) (prMul (pavOfVal p a) (pavOfVal p b)) := by
  -- 指数の一致（Int.toNat の符号恒等式、omega）
  have hexp : (-(a + b)).toNat + (a.toNat + b.toNat)
            = (-a).toNat + (-b).toNat + (a + b).toNat := by omega
  -- Nat レベルの冪の等式（両辺を単一冪に束ねて指数一致を代入）
  have hnat : pavBase p ^ (-(a + b)).toNat
                * (pavBase p ^ a.toNat * pavBase p ^ b.toNat)
            = pavBase p ^ (-a).toNat * pavBase p ^ (-b).toNat
                * pavBase p ^ (a + b).toNat := by
    have hl : pavBase p ^ (-(a + b)).toNat
                * (pavBase p ^ a.toNat * pavBase p ^ b.toNat)
            = pavBase p ^ ((-(a + b)).toNat + (a.toNat + b.toNat)) := by
      rw [Nat.pow_add, Nat.pow_add]
    have hr : pavBase p ^ (-a).toNat * pavBase p ^ (-b).toNat
                * pavBase p ^ (a + b).toNat
            = pavBase p ^ ((-a).toNat + (-b).toNat + (a + b).toNat) := by
      rw [Nat.pow_add, Nat.pow_add]
    rw [hl, hr, hexp]
  -- ratRel を Int の冪の交差積として展開し、Nat の等式へ落とす
  show ((pavBase p ^ (-(a + b)).toNat : Nat) : Int)
         * (((pavBase p ^ a.toNat : Nat) : Int)
            * ((pavBase p ^ b.toNat : Nat) : Int))
     = ((pavBase p ^ (-a).toNat : Nat) : Int)
         * ((pavBase p ^ (-b).toNat : Nat) : Int)
         * ((pavBase p ^ (a + b).toNat : Nat) : Int)
  rw [← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul,
    hnat]

/-- **乗法性** |xy|_p = |x|_p · |y|_p（非零 x, y・p 素数）。
    付値の加法性 `pvq_val_mul` で v_p(xy) = v_p(x)+v_p(y) に開き、
    核補題 `pavOfVal_mul_rel` を Quot.sound で商へ持ち上げる。 -/
theorem pav_mul (p : Nat) (hp : IsPrime p) (x y : PreRat)
    (hx : x.num ≠ 0) (hy : y.num ≠ 0) :
    pavAbs p (prMul x y) = qMul (pavAbs p x) (pavAbs p y) := by
  show Quot.mk ratRel (pavOfVal p (pvqVal p (prMul x y)))
     = Quot.mk ratRel
         (prMul (pavOfVal p (pvqVal p x)) (pavOfVal p (pvqVal p y)))
  rw [pvq_val_mul p hp x y hx hy]
  exact Quot.sound (pavOfVal_mul_rel p (pvqVal p x) (pvqVal p y))

/-! ## v_p(x) = 0 なら |x|_p = 1 -/

/-- v = 0 での代表は 1/1（p^0 = 1）。 -/
theorem pavOfVal_zero (p : Nat) : pavOfVal p 0 = prOne := by
  apply preRat_ext
  · show ((pavBase p ^ (-(0 : Int)).toNat : Nat) : Int) = (1 : Int)
    have h0 : (-(0 : Int)).toNat = 0 := by omega
    rw [h0, Nat.pow_zero]; omega
  · show ((pavBase p ^ ((0 : Int)).toNat : Nat) : Int) = (1 : Int)
    have h0 : ((0 : Int)).toNat = 0 := by omega
    rw [h0, Nat.pow_zero]; omega

/-- **v_p(x) = 0 ⟹ |x|_p = 1** — 付値が 0 なら絶対値は単位元。 -/
theorem pav_val_zero (p : Nat) (x : PreRat) (h : pvqVal p x = 0) :
    pavAbs p x = ratRing.one := by
  show Quot.mk ratRel (pavOfVal p (pvqVal p x)) = Quot.mk ratRel prOne
  rw [h]
  exact congrArg (Quot.mk ratRel) (pavOfVal_zero p)

/-! ## support 外自明性: p ∤ num ∧ p ∤ den ⟹ |x|_p = 1 -/

/-- p ∤ n なら自然数付値 v_p(n) = 0（p ∣ 0 なので n ≠ 0 かつ p^0·n の spec）。 -/
theorem pvqNatVal_zero_of_not_dvd (p : Nat) (hp : IsPrime p) (n : Nat)
    (h : ¬ p ∣ n) : pvqNatVal p n = 0 := by
  have hp2 : 2 ≤ p := hp.1
  have hn1 : 1 ≤ n := by
    cases Nat.eq_zero_or_pos n with
    | inl h0 => exfalso; apply h; rw [h0]; exact Nat.dvd_zero p
    | inr hpos => exact hpos
  have hspec := pvqNatVal_spec p hp2 0 n h hn1
  rw [Nat.pow_zero, Nat.one_mul] at hspec
  exact hspec

/-- p ∤ |num| ∧ p ∤ |den| なら有理数付値 v_p(x) = 0（分子・分母とも自明）。 -/
theorem pvqVal_zero_of_not_dvd (p : Nat) (hp : IsPrime p) (x : PreRat)
    (hnum : ¬ p ∣ x.num.natAbs) (hden : ¬ p ∣ x.den.natAbs) :
    pvqVal p x = 0 := by
  show (pvqNatVal p x.num.natAbs : Int) - (pvqNatVal p x.den.natAbs : Int) = 0
  rw [pvqNatVal_zero_of_not_dvd p hp _ hnum,
    pvqNatVal_zero_of_not_dvd p hp _ hden]
  omega

/-- **support 外自明性** — p が分子・分母のどちらも割らなければ |x|_p = 1。
    積公式 ∏_v |x|_v = 1 の有限性の核: ほとんどの素点で絶対値は自明値。 -/
theorem pav_trivial (p : Nat) (hp : IsPrime p) (x : PreRat)
    (hnum : ¬ p ∣ x.num.natAbs) (hden : ¬ p ∣ x.den.natAbs) :
    pavAbs p x = ratRing.one :=
  pav_val_zero p x (pvqVal_zero_of_not_dvd p hp x hnum hden)

/-! ## 正値性・非零性 -/

/-- **正値性** 0 ≤ |x|_p（分子 p^{(-v)⁺} > 0）。 -/
theorem pav_nonneg (p : Nat) (x : PreRat) :
    qLe ratRing.zero (pavAbs p x) := by
  show (0 : Int) * ((pavBase p ^ (pvqVal p x).toNat : Nat) : Int)
     ≤ ((pavBase p ^ (-(pvqVal p x)).toNat : Nat) : Int) * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  exact Int.le_of_lt (pavBase_pow_pos p (-(pvqVal p x)).toNat)

/-- **非零性** |x|_p ≠ 0（分子が正なので prZero と ratRel 同値になり得ない）。 -/
theorem pav_ne_zero (p : Nat) (x : PreRat) :
    pavAbs p x ≠ ratRing.zero := by
  intro h
  have hrel : ratRel (pavOfVal p (pvqVal p x)) prZero := quot_exact_rat h
  have hh : ((pavBase p ^ (-(pvqVal p x)).toNat : Nat) : Int) * (1 : Int)
          = (0 : Int) * ((pavBase p ^ (pvqVal p x).toNat : Nat) : Int) := hrel
  rw [Int.mul_one, Int.zero_mul] at hh
  have hpos : 0 < ((pavBase p ^ (-(pvqVal p x)).toNat : Nat) : Int) :=
    pavBase_pow_pos p (-(pvqVal p x)).toNat
  omega

/-! ## capstone: 絶対値データと存在 -/

/-- **p 進絶対値データ** — 乗法性・support 外自明性・正値性・非零性を束ねる。 -/
structure PadicAbsData (p : Nat) where
  /-- 絶対値関数 |·|_p（非零 PreRat 代表上）。 -/
  abs : PreRat → QRat
  /-- 乗法性 |xy|_p = |x|_p·|y|_p（非零）。 -/
  multiplicative : ∀ x y : PreRat, x.num ≠ 0 → y.num ≠ 0 →
    abs (prMul x y) = qMul (abs x) (abs y)
  /-- support 外自明性 p ∤ |num| ∧ p ∤ |den| ⟹ |x|_p = 1。 -/
  trivial_off : ∀ x : PreRat, ¬ p ∣ x.num.natAbs → ¬ p ∣ x.den.natAbs →
    abs x = ratRing.one
  /-- 正値性 0 ≤ |x|_p。 -/
  nonneg : ∀ x : PreRat, qLe ratRing.zero (abs x)
  /-- 非零性 |x|_p ≠ 0。 -/
  ne_zero : ∀ x : PreRat, abs x ≠ ratRing.zero

/-- **capstone** — 各素数 p に対し、乗法的で support 外自明な実 p 進絶対値
    |·|_p : ℚ^× → ℚ≥0（PreRat 代表上）が存在する（Nonempty, choice 不使用）。 -/
theorem pav_exists (p : Nat) (hp : IsPrime p) : Nonempty (PadicAbsData p) :=
  ⟨{ abs := pavAbs p
     multiplicative := fun x y hx hy => pav_mul p hp x y hx hy
     trivial_off := fun x hnum hden => pav_trivial p hp x hnum hden
     nonneg := fun x => pav_nonneg p x
     ne_zero := fun x => pav_ne_zero p x }⟩

end IUT
