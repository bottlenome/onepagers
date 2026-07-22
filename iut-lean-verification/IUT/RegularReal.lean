/-
# M117F: Bishop 流正則実数列 — ℝ 骨格・加法群構造

柱C（issue #37）「ℝ の自前構成」の第二段（第一段 = M115F の ℚ）。
Bishop の**正則列** |x_m − x_n| ≤ 1/(m+1) + 1/(n+1) による実数の骨格。
正則列は収束の modulus が添字に固定されているため modulus 抽出
（= 選択公理の使用点）が不要になる、choice-free ℝ 構成の標準法。

  * M117F-1 `qFrac`/`qUnitFrac` — 基本分数 c/(m+1) と線形比較
    `qFrac_le`・合併 `qFrac_add`（全ての有理数簿記をこの 2 本に還元）
  * M117F-2 `int_eps_cancel`/`qLe_of_forall_add_frac` — **ε-消去**:
    ∀m, a ≤ b + c/(m+1) ⟹ a ≤ b（アルキメデス性の使用点。
    m = c·分母積 の明示 witness で排中律なしに閉じる）
  * M117F-3 `IsRegular`/`RReal`/`qToReal` — 正則列と定数列埋め込み
  * M117F-4 `realEq` — 同値関係（|xₙ−yₙ| ≤ 2/(n+1)）。推移律は
    4 項三角分割 + ε-消去（c = 6）が本丸
  * M117F-5 `realAdd`/`realNeg` — 加法（添字 2n+1 倍速化で正則性維持）
    と反元、`realEq` との両立（congruence）
  * M117F-6 加法群法則（≈ の下で）: 可換・結合・零・反元、
    埋め込みの加法性
  * M117F-7 `RegularRealData` — 総括

正直申告: 乗法（標準上界による添字加速）・順序 (x < y の witness 形)・
完備性（柱C-1 の本丸）は次層。realEq による商型化（Quot 化）も
次層 — 本層は setoid レベルの群法則まで。

全て選択公理不使用。
-/
import IUT.Rationals

namespace IUT

/-! ## M117F-1: 基本分数 c/(m+1) -/

/-- **M117F-1a: 基本分数** c/(m+1)（分母は正なので PreRat 直書き）。 -/
def qFrac (c m : Nat) : QRat :=
  Quot.mk ratRel ⟨(c : Int), (m : Int) + 1, by omega⟩

/-- **M117F-1b: 単位分数** 1/(m+1)。 -/
def qUnitFrac (m : Nat) : QRat := qFrac 1 m

/-- **M117F-1c: 分数の線形比較** — c/(m+1) ≤ c'/(m'+1) ⟺
    c(m'+1) ≤ c'(m+1)。係数が数値リテラルなら使用側は omega 一発。 -/
theorem qFrac_le {c m c' m' : Nat}
    (h : (c : Int) * ((m' : Int) + 1) ≤ (c' : Int) * ((m : Int) + 1)) :
    qLe (qFrac c m) (qFrac c' m') := by
  show (c : Int) * ((m' : Int) + 1) ≤ (c' : Int) * ((m : Int) + 1)
  exact h

/-- **M117F-1d: 分数の非負性**。 -/
theorem qFrac_nonneg (c m : Nat) : qLe ratRing.zero (qFrac c m) := by
  show (0 : Int) * ((m : Int) + 1) ≤ (c : Int) * 1
  omega

/-- **M117F-1e: 同分母の合併** c/(m+1) + d/(m+1) ≤ (c+d)/(m+1)
    （実は等号だが ≤ で十分）。 -/
theorem qFrac_add (c d m : Nat) :
    qLe (qAdd (qFrac c m) (qFrac d m)) (qFrac (c + d) m) := by
  show ((c : Int) * ((m : Int) + 1) + (d : Int) * ((m : Int) + 1))
      * ((m : Int) + 1)
    ≤ ((c + d : Nat) : Int) * (((m : Int) + 1) * ((m : Int) + 1))
  have e0 : ((c + d : Nat) : Int) = (c : Int) + (d : Int) := by omega
  rw [e0, ← Int.add_mul, Int.mul_assoc]
  exact Int.le_refl _

/-! ## qAdd/qNeg の環法則ラッパー（ratRing の法則を構文一致する形で再輸出） -/

/-- 加法の結合則（ラッパー）。 -/
theorem qAdd_assoc (a b c : QRat) :
    qAdd (qAdd a b) c = qAdd a (qAdd b c) := ratRing.add_assoc a b c

/-- 加法の可換則（ラッパー）。 -/
theorem qAdd_comm (a b : QRat) : qAdd a b = qAdd b a := ratRing.add_comm a b

/-- 左零元（ラッパー）。 -/
theorem qAdd_zero_left (a : QRat) : qAdd ratRing.zero a = a :=
  ratRing.zero_add a

/-- 右零元（可換 + 左零元から導出）。 -/
theorem qAdd_zero (a : QRat) : qAdd a ratRing.zero = a := by
  rw [qAdd_comm]
  exact ratRing.zero_add a

/-- 左反元（ラッパー）。 -/
theorem qNeg_add_self (a : QRat) : qAdd (qNeg a) a = ratRing.zero :=
  ratRing.neg_add a

/-- 右反元（ラッパー）。 -/
theorem qAdd_neg_self (a : QRat) : qAdd a (qNeg a) = ratRing.zero := by
  rw [qAdd_comm]
  exact ratRing.neg_add a

/-- 中央交換 (a+b)+(c+d) = (a+c)+(b+d)（結合・可換から導出）。 -/
theorem qAdd_swap_mid (a b c d : QRat) :
    qAdd (qAdd a b) (qAdd c d) = qAdd (qAdd a c) (qAdd b d) := by
  rw [qAdd_assoc a b (qAdd c d), ← qAdd_assoc b c d, qAdd_comm b c,
    qAdd_assoc c b d, ← qAdd_assoc a c (qAdd b d)]

/-- 反元の一意性: u + v = 0 なら v = −u。 -/
theorem qNeg_unique {u v : QRat} (h : qAdd u v = ratRing.zero) :
    v = qNeg u := by
  have h2 : qAdd (qNeg u) (qAdd u v) = qAdd (qNeg u) ratRing.zero := by
    rw [h]
  rw [← qAdd_assoc, qNeg_add_self u, qAdd_zero_left, qAdd_zero] at h2
  exact h2

/-- 反元の加法分配（一意性から導出）。 -/
theorem qNeg_add_dist (a b : QRat) :
    qNeg (qAdd a b) = qAdd (qNeg a) (qNeg b) := by
  have h0 : qAdd (qAdd a b) (qAdd (qNeg a) (qNeg b)) = ratRing.zero := by
    rw [qAdd_swap_mid a b (qNeg a) (qNeg b), qAdd_neg_self a,
      qAdd_neg_self b, qAdd_zero_left]
  exact (qNeg_unique h0).symm

/-- 二重反元（一意性から導出）。 -/
theorem qNeg_neg (a : QRat) : qNeg (qNeg a) = a :=
  (qNeg_unique (qNeg_add_self a)).symm

/-- 等式からの ≤。 -/
theorem qLe_of_eq {a b : QRat} (h : a = b) : qLe a b := h ▸ qLe_refl a

/-- **両側単調性**（qLe_add + 可換の合成、本層の主力）。 -/
theorem qLe_add_two {a b a' b' : QRat} (h1 : qLe a a') (h2 : qLe b b') :
    qLe (qAdd a b) (qAdd a' b') := by
  have s1 : qLe (qAdd a b) (qAdd a' b) := qLe_add a a' b h1
  have s2 : qLe (qAdd b a') (qAdd b' a') := qLe_add b b' a' h2
  rw [qAdd_comm b a', qAdd_comm b' a'] at s2
  exact qLe_trans _ _ _ s1 s2

/-! ## 絶対値の補足 -/

/-- |−t| の代表補題: intAbs (−n) = intAbs n。 -/
theorem intAbs_neg (n : Int) : intAbs (-n) = intAbs n := by
  cases Int.le_total n 0 with
  | inl h =>
    rw [intAbs_of_nonneg (show (0 : Int) ≤ -n by omega),
      intAbs_of_nonpos h]
  | inr h =>
    rw [intAbs_of_nonpos (show -n ≤ (0 : Int) by omega),
      intAbs_of_nonneg h, Int.neg_neg]

/-- **|−a| = |a|**（商上）。 -/
theorem qAbs_neg (a : QRat) : qAbs (qNeg a) = qAbs a := by
  induction a using Quot.ind; rename_i x
  exact congrArg (Quot.mk ratRel) (preRat_ext (intAbs_neg x.num) rfl)

/-- **|0| = 0**。 -/
theorem qAbs_zero : qAbs ratRing.zero = ratRing.zero :=
  congrArg (Quot.mk ratRel)
    (preRat_ext (intAbs_of_nonneg (Int.le_refl 0)) rfl)

/-- **|q − q| = 0**。 -/
theorem qAbs_self_sub (q : QRat) :
    qAbs (qAdd q (qNeg q)) = ratRing.zero := by
  rw [qAdd_neg_self q]
  exact qAbs_zero

/-- 0 ≤ 分数の和。 -/
theorem qFrac_add_nonneg (c m d n : Nat) :
    qLe ratRing.zero (qAdd (qFrac c m) (qFrac d n)) := by
  have h := qLe_add_two (qFrac_nonneg c m) (qFrac_nonneg d n)
  rw [qAdd_zero_left] at h
  exact h

/-- a − c = (a − b) + (b − c)（中点挿入）。 -/
theorem qSub_split (a b c : QRat) :
    qAdd a (qNeg c) = qAdd (qAdd a (qNeg b)) (qAdd b (qNeg c)) := by
  rw [qAdd_assoc a (qNeg b) (qAdd b (qNeg c)),
    ← qAdd_assoc (qNeg b) b (qNeg c), qNeg_add_self b, qAdd_zero_left]

/-- **中点挿入つき三角不等式** |a − c| ≤ |a − b| + |b − c|。 -/
theorem qAbs_sub_split (a b c : QRat) :
    qLe (qAbs (qAdd a (qNeg c)))
      (qAdd (qAbs (qAdd a (qNeg b))) (qAbs (qAdd b (qNeg c)))) := by
  rw [qSub_split a b c]
  exact qAbs_add_le (qAdd a (qNeg b)) (qAdd b (qNeg c))

/-- (a+b) − (c+d) = (a−c) + (b−d)（対の差）。 -/
theorem qAdd_sub_pair (a b c d : QRat) :
    qAdd (qAdd a b) (qNeg (qAdd c d))
      = qAdd (qAdd a (qNeg c)) (qAdd b (qNeg d)) := by
  rw [qNeg_add_dist c d, qAdd_swap_mid a b (qNeg c) (qNeg d)]

/-! ## M117F-2: ε-消去（アルキメデス性の使用点） -/

/-- **M117F-2a: 整数の ε-消去核** — A(D+1) ≤ B(D+1) + D（D ≥ 0）なら
    A ≤ B。(A−B)(D+1) ≤ D < D+1 だから A−B < 1。
    非線形は `Int.mul_le_mul_of_nonneg_right` の一手だけで、
    残りは積を不透明原子として omega が閉じる。 -/
theorem int_eps_cancel (A B D : Int) (hD : 0 ≤ D)
    (h : A * (D + 1) ≤ B * (D + 1) + D) : A ≤ B := by
  cases Int.lt_or_le B A with
  | inr hAB => exact hAB
  | inl hBA =>
    have hg1 : 1 ≤ A - B := by omega
    have hmul : 1 * (D + 1) ≤ (A - B) * (D + 1) :=
      Int.mul_le_mul_of_nonneg_right hg1 (by omega)
    have hdist : (A - B) * (D + 1) = A * (D + 1) - B * (D + 1) :=
      Int.sub_mul A B (D + 1)
    omega

/-- **定理 (M117F-2b): ε-消去** — ∀m, a ≤ b + c/(m+1) なら a ≤ b。
    witness m = c·(分母積) の明示構成で排中律なしに閉じる
    （代表レベルの Int 消去に還元）。 -/
theorem qLe_of_forall_add_frac (c : Nat) {a b : QRat}
    (h : ∀ m : Nat, qLe a (qAdd b (qFrac c m))) : qLe a b := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  have hD : (0 : Int) ≤ (c : Int) * y.den * x.den :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (Int.le_of_lt y.den_pos))
      (Int.le_of_lt x.den_pos)
  have key : x.num * (y.den * ((((c : Int) * y.den * x.den).toNat : Int) + 1))
      ≤ (y.num * ((((c : Int) * y.den * x.den).toNat : Int) + 1)
          + (c : Int) * y.den) * x.den :=
    h (((c : Int) * y.den * x.den).toNat)
  rw [Int.toNat_of_nonneg hD] at key
  have e1 : x.num * (y.den * ((c : Int) * y.den * x.den + 1))
      = x.num * y.den * ((c : Int) * y.den * x.den + 1) :=
    (Int.mul_assoc _ _ _).symm
  have e2 : (y.num * ((c : Int) * y.den * x.den + 1) + (c : Int) * y.den)
        * x.den
      = y.num * x.den * ((c : Int) * y.den * x.den + 1)
        + (c : Int) * y.den * x.den := by
    rw [Int.add_mul,
      int_mul_right_swap y.num ((c : Int) * y.den * x.den + 1) x.den]
  rw [e1, e2] at key
  show x.num * y.den ≤ y.num * x.den
  exact int_eps_cancel (x.num * y.den) (y.num * x.den)
    ((c : Int) * y.den * x.den) hD key

/-! ## M117F-3: 正則列と実数 -/

/-- **M117F-3a: 正則性** — |f m − f n| ≤ 1/(m+1) + 1/(n+1)。 -/
def IsRegular (f : Nat → QRat) : Prop :=
  ∀ m n, qLe (qAbs (qAdd (f m) (qNeg (f n))))
    (qAdd (qUnitFrac m) (qUnitFrac n))

/-- **M117F-3b: 正則実数** — 正則列そのもの（modulus 不要）。 -/
structure RReal where
  /-- 近似列（第 n 項は誤差 1/(n+1) 以内）。 -/
  seq : Nat → QRat
  /-- 正則性。 -/
  reg : IsRegular seq

/-- **M117F-3c: 定数列の埋め込み** ℚ → ℝ。 -/
def qToReal (q : QRat) : RReal where
  seq := fun _ => q
  reg := by
    intro m n
    rw [qAbs_self_sub]
    exact qFrac_add_nonneg 1 m 1 n

/-- 実数の零（定数列 0）。 -/
def realZero : RReal := qToReal ratRing.zero

/-! ## M117F-4: 同値関係 -/

/-- **M117F-4a: 実数の等値** — ∀n, |xₙ − yₙ| ≤ 2/(n+1)。 -/
def realEq (x y : RReal) : Prop :=
  ∀ n, qLe (qAbs (qAdd (x.seq n) (qNeg (y.seq n))))
    (qAdd (qUnitFrac n) (qUnitFrac n))

/-- **M117F-4b: 反射律**。 -/
theorem realEq_refl (x : RReal) : realEq x x := by
  intro n
  rw [qAbs_self_sub]
  exact qFrac_add_nonneg 1 n 1 n

/-- −(a − b) = b − a。 -/
theorem qNeg_sub (a b : QRat) :
    qNeg (qAdd a (qNeg b)) = qAdd b (qNeg a) := by
  rw [qNeg_add_dist a (qNeg b), qNeg_neg b, qAdd_comm (qNeg a) b]

/-- **M117F-4c: 対称律**（|b−a| = |−(a−b)| = |a−b|）。 -/
theorem realEq_symm {x y : RReal} (h : realEq x y) : realEq y x := by
  intro n
  have e : qAbs (qAdd (y.seq n) (qNeg (x.seq n)))
      = qAbs (qAdd (x.seq n) (qNeg (y.seq n))) := by
    rw [← qNeg_sub (x.seq n) (y.seq n), qAbs_neg]
  rw [e]
  exact h n

/-- 列が等しければ realEq。 -/
theorem realEq_of_seq_eq {x y : RReal} (h : ∀ n, x.seq n = y.seq n) :
    realEq x y := by
  intro n
  rw [h n, qAbs_self_sub]
  exact qFrac_add_nonneg 1 n 1 n

/-- **定理 (M117F-4d): 推移律（本丸）** — 4 項三角分割
    |xₙ−zₙ| ≤ |xₙ−xₘ| + |xₘ−yₘ| + |yₘ−zₘ| + |zₘ−zₙ|
    ≤ 2/(n+1) + 6/(m+1)（∀m）→ ε-消去（c = 6）。 -/
theorem realEq_trans {x y z : RReal} (hxy : realEq x y)
    (hyz : realEq y z) : realEq x z := by
  intro n
  apply qLe_of_forall_add_frac 6
  intro m
  have t2 : qLe (qAbs (qAdd (x.seq n) (qNeg (y.seq m))))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
        (qAdd (qUnitFrac m) (qUnitFrac m))) :=
    qLe_trans _ _ _ (qAbs_sub_split (x.seq n) (x.seq m) (y.seq m))
      (qLe_add_two (x.reg n m) (hxy m))
  have t3 : qLe (qAbs (qAdd (y.seq m) (qNeg (z.seq n))))
      (qAdd (qAdd (qUnitFrac m) (qUnitFrac m))
        (qAdd (qUnitFrac m) (qUnitFrac n))) :=
    qLe_trans _ _ _ (qAbs_sub_split (y.seq m) (z.seq m) (z.seq n))
      (qLe_add_two (hyz m) (z.reg m n))
  have total := qLe_trans _ _ _
    (qAbs_sub_split (x.seq n) (y.seq m) (z.seq n))
    (qLe_add_two t2 t3)
  apply qLe_trans _ _ _ total
  -- 折り畳み: ((uₙ+uₘ)+(uₘ+uₘ)) + ((uₘ+uₘ)+(uₘ+uₙ)) ≤ (uₙ+uₙ) + 6/(m+1)
  have inner3 : qLe (qAdd (qUnitFrac m) (qAdd (qUnitFrac m) (qUnitFrac m)))
      (qFrac 3 m) :=
    qLe_trans _ _ _ (qLe_add_two (qLe_refl _) (qFrac_add 1 1 m))
      (qFrac_add 1 2 m)
  have lb : qLe (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
        (qAdd (qUnitFrac m) (qUnitFrac m)))
      (qAdd (qUnitFrac n) (qFrac 3 m)) :=
    qLe_trans _ _ _ (qLe_of_eq (qAdd_assoc _ _ _))
      (qLe_add_two (qLe_refl _) inner3)
  have rb : qLe (qAdd (qAdd (qUnitFrac m) (qUnitFrac m))
        (qAdd (qUnitFrac m) (qUnitFrac n)))
      (qAdd (qUnitFrac n) (qFrac 3 m)) := by
    have e : qAdd (qAdd (qUnitFrac m) (qUnitFrac m))
          (qAdd (qUnitFrac m) (qUnitFrac n))
        = qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
          (qAdd (qUnitFrac m) (qUnitFrac m)) := by
      rw [qAdd_comm (qAdd (qUnitFrac m) (qUnitFrac m))
          (qAdd (qUnitFrac m) (qUnitFrac n)),
        qAdd_comm (qUnitFrac m) (qUnitFrac n)]
    exact qLe_trans _ _ _ (qLe_of_eq e) lb
  have fold := qLe_add_two lb rb
  have mid : qAdd (qAdd (qUnitFrac n) (qFrac 3 m))
        (qAdd (qUnitFrac n) (qFrac 3 m))
      = qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
        (qAdd (qFrac 3 m) (qFrac 3 m)) :=
    qAdd_swap_mid _ _ _ _
  exact qLe_trans _ _ _ fold (qLe_trans _ _ _ (qLe_of_eq mid)
    (qLe_add_two (qLe_refl _) (qFrac_add 3 3 m)))

/-! ## M117F-5: 加法と反元 -/

/-- **M117F-5a: 加法** — 添字を 2n+1 に倍速化して正則性を維持
    （1/(2m+2) + 1/(2n+2) が二組で 1/(m+1) + 1/(n+1) に収まる）。 -/
def realAdd (x y : RReal) : RReal where
  seq := fun n => qAdd (x.seq (2 * n + 1)) (y.seq (2 * n + 1))
  reg := by
    intro m n
    show qLe (qAbs (qAdd (qAdd (x.seq (2 * m + 1)) (y.seq (2 * m + 1)))
        (qNeg (qAdd (x.seq (2 * n + 1)) (y.seq (2 * n + 1))))))
      (qAdd (qUnitFrac m) (qUnitFrac n))
    rw [qAdd_sub_pair]
    have h1 := qLe_trans _ _ _ (qAbs_add_le _ _)
      (qLe_add_two (x.reg (2 * m + 1) (2 * n + 1))
        (y.reg (2 * m + 1) (2 * n + 1)))
    apply qLe_trans _ _ _ h1
    have mid : qAdd (qAdd (qUnitFrac (2 * m + 1)) (qUnitFrac (2 * n + 1)))
          (qAdd (qUnitFrac (2 * m + 1)) (qUnitFrac (2 * n + 1)))
        = qAdd (qAdd (qUnitFrac (2 * m + 1)) (qUnitFrac (2 * m + 1)))
          (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1))) :=
      qAdd_swap_mid _ _ _ _
    apply qLe_trans _ _ _ (qLe_of_eq mid)
    exact qLe_add_two
      (qLe_trans _ _ _ (qFrac_add 1 1 (2 * m + 1)) (qFrac_le (by omega)))
      (qLe_trans _ _ _ (qFrac_add 1 1 (2 * n + 1)) (qFrac_le (by omega)))

/-- **M117F-5b: 反元**（点ごと、正則性は |−t| = |t|）。 -/
def realNeg (x : RReal) : RReal where
  seq := fun n => qNeg (x.seq n)
  reg := by
    intro m n
    have e : qAdd (qNeg (x.seq m)) (qNeg (qNeg (x.seq n)))
        = qNeg (qAdd (x.seq m) (qNeg (x.seq n))) := by
      rw [qNeg_add_dist]
    show qLe (qAbs (qAdd (qNeg (x.seq m)) (qNeg (qNeg (x.seq n)))))
      (qAdd (qUnitFrac m) (qUnitFrac n))
    rw [e, qAbs_neg]
    exact x.reg m n

/-- **定理 (M117F-5c): 加法の左 congruence** — x ≈ x' なら
    x + y ≈ x' + y（ε-消去不要: 添字 2n+1 の評価がそのまま効く）。 -/
theorem realAdd_congr_left {x x' : RReal} (y : RReal) (h : realEq x x') :
    realEq (realAdd x y) (realAdd x' y) := by
  intro n
  show qLe (qAbs (qAdd (qAdd (x.seq (2 * n + 1)) (y.seq (2 * n + 1)))
      (qNeg (qAdd (x'.seq (2 * n + 1)) (y.seq (2 * n + 1))))))
    (qAdd (qUnitFrac n) (qUnitFrac n))
  rw [qAdd_sub_pair]
  apply qLe_trans _ _ _ (qAbs_add_le _ _)
  rw [qAbs_self_sub, qAdd_zero]
  exact qLe_trans _ _ _ (h (2 * n + 1))
    (qLe_add_two (qFrac_le (by omega)) (qFrac_le (by omega)))

/-- **M117F-5d: 加法の可換律**（列レベルで等しい）。 -/
theorem realAdd_comm (x y : RReal) : realEq (realAdd x y) (realAdd y x) :=
  realEq_of_seq_eq (fun _ => qAdd_comm _ _)

/-- **M117F-5e: 加法の右 congruence**（可換 + 左 congruence）。 -/
theorem realAdd_congr_right (x : RReal) {y y' : RReal} (h : realEq y y') :
    realEq (realAdd x y) (realAdd x y') :=
  realEq_trans (realAdd_comm x y)
    (realEq_trans (realAdd_congr_left x h) (realAdd_comm y' x))

/-! ## M117F-6: 加法群法則（≈ の下で） -/

/-- **定理 (M117F-6a): 右零元** x + 0 ≈ x（添字ズレ x_{2n+1} vs x_n は
    正則性そのもの）。 -/
theorem realAdd_zero (x : RReal) : realEq (realAdd x realZero) x := by
  intro n
  show qLe (qAbs (qAdd (qAdd (x.seq (2 * n + 1)) ratRing.zero)
      (qNeg (x.seq n))))
    (qAdd (qUnitFrac n) (qUnitFrac n))
  rw [qAdd_zero]
  exact qLe_trans _ _ _ (x.reg (2 * n + 1) n)
    (qLe_add_two (qFrac_le (by omega)) (qLe_refl _))

/-- **定理 (M117F-6b): 反元法則** x + (−x) ≈ 0（列レベルで 0）。 -/
theorem realAdd_neg (x : RReal) : realEq (realAdd x (realNeg x)) realZero :=
  realEq_of_seq_eq (fun _ => qAdd_neg_self _)

/-- ((p+q)+r) − (s+(q+t)) = (p−s) + (r−t)（結合律の差の整理）。 -/
theorem qAssoc_diff (p q r s t : QRat) :
    qAdd (qAdd (qAdd p q) r) (qNeg (qAdd s (qAdd q t)))
      = qAdd (qAdd p (qNeg s)) (qAdd r (qNeg t)) := by
  rw [qAdd_assoc p q r, qNeg_add_dist s (qAdd q t), qNeg_add_dist q t,
    qAdd_swap_mid p (qAdd q r) (qNeg s) (qAdd (qNeg q) (qNeg t)),
    qAdd_swap_mid q r (qNeg q) (qNeg t), qAdd_neg_self q, qAdd_zero_left]

/-- **定理 (M117F-6c): 結合律** (x+y)+z ≈ x+(y+z) — y の添字は両辺
    4n+3 で一致し、x・z の添字ズレ (4n+3 vs 2n+1) を正則性が吸収。 -/
theorem realAdd_assoc (x y z : RReal) :
    realEq (realAdd (realAdd x y) z) (realAdd x (realAdd y z)) := by
  intro n
  show qLe (qAbs (qAdd
      (qAdd (qAdd (x.seq (2 * (2 * n + 1) + 1)) (y.seq (2 * (2 * n + 1) + 1)))
        (z.seq (2 * n + 1)))
      (qNeg (qAdd (x.seq (2 * n + 1))
        (qAdd (y.seq (2 * (2 * n + 1) + 1)) (z.seq (2 * (2 * n + 1) + 1)))))))
    (qAdd (qUnitFrac n) (qUnitFrac n))
  rw [qAssoc_diff]
  apply qLe_trans _ _ _ (qAbs_add_le _ _)
  have hx := x.reg (2 * (2 * n + 1) + 1) (2 * n + 1)
  have hz := z.reg (2 * n + 1) (2 * (2 * n + 1) + 1)
  apply qLe_trans _ _ _ (qLe_add_two hx hz)
  exact qLe_add_two
    (qLe_trans _ _ _
      (qLe_add_two (qFrac_le (by omega)) (qLe_refl _))
      (qLe_trans _ _ _ (qFrac_add 1 1 (2 * n + 1)) (qFrac_le (by omega))))
    (qLe_trans _ _ _
      (qLe_add_two (qLe_refl _) (qFrac_le (by omega)))
      (qLe_trans _ _ _ (qFrac_add 1 1 (2 * n + 1)) (qFrac_le (by omega))))

/-- **定理 (M117F-6d): 埋め込みの加法性**（定数列は添字に依らない）。 -/
theorem qToReal_add (a b : QRat) :
    realEq (realAdd (qToReal a) (qToReal b)) (qToReal (qAdd a b)) :=
  realEq_of_seq_eq (fun _ => rfl)

/-! ## M117F-7: 総括 -/

/-- **M117F-7a: 総括** — 正則実数の同値関係 + 加法群構造（≈ の下）。 -/
structure RegularRealData where
  /-- 反射律。 -/
  eqv_refl : ∀ x, realEq x x
  /-- 対称律。 -/
  eqv_symm : ∀ {x y}, realEq x y → realEq y x
  /-- 推移律（ε-消去）。 -/
  eqv_trans : ∀ {x y z}, realEq x y → realEq y z → realEq x z
  /-- 加法の左 congruence。 -/
  add_congr_left : ∀ {x x'} (y), realEq x x' → realEq (realAdd x y) (realAdd x' y)
  /-- 加法の右 congruence。 -/
  add_congr_right : ∀ (x) {y y'}, realEq y y' → realEq (realAdd x y) (realAdd x y')
  /-- 可換律。 -/
  add_comm : ∀ x y, realEq (realAdd x y) (realAdd y x)
  /-- 結合律。 -/
  add_assoc : ∀ x y z, realEq (realAdd (realAdd x y) z) (realAdd x (realAdd y z))
  /-- 零元。 -/
  add_zero : ∀ x, realEq (realAdd x realZero) x
  /-- 反元。 -/
  add_neg : ∀ x, realEq (realAdd x (realNeg x)) realZero
  /-- 埋め込みの加法性。 -/
  embed_add : ∀ a b, realEq (realAdd (qToReal a) (qToReal b)) (qToReal (qAdd a b))

/-- **M117F-7b: witness**。 -/
def regularRealData : RegularRealData where
  eqv_refl := realEq_refl
  eqv_symm := realEq_symm
  eqv_trans := realEq_trans
  add_congr_left := realAdd_congr_left
  add_congr_right := realAdd_congr_right
  add_comm := realAdd_comm
  add_assoc := realAdd_assoc
  add_zero := realAdd_zero
  add_neg := realAdd_neg
  embed_add := qToReal_add

/-- **M117F-7c: 存在**。 -/
theorem regularReal_exists : Nonempty RegularRealData :=
  ⟨regularRealData⟩

end IUT
