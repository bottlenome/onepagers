/-
# M120F: 有理数の床関数と正則列の標準上界 — 商から Nat を取り出す

柱C（issue #37）「ℝ の自前構成」第三段（乗法）の準備。次層の実数乗法は
Bishop 流に添字を標準上界でスケールするため、正則列から Nat 上界を
choice なしで抽出する装置が必須になる。床関数は有理数の**値のみ**に
依存する（代表の取り方に依らない）ため、Quot.lift で商から Int/Nat を
選択公理なしに取り出せる稀有な関数である点が本層の要。

  * M120F-1 `int_ediv_unique` / `int_lt_cancel_right` — Int の Euclid 除算の
    一意性（q·b ≤ a < (q+1)·b なら a / b = q）。core の
    `Int.mul_ediv_add_emod`・`Int.emod_nonneg`・`Int.emod_lt_of_pos` を
    ∀ d r 形の補助命題に隔離して omega の変数除算制限を回避
  * M120F-2 `prFloor` / `prFloor_spec` / `ratRel_floor` / `qFloor` —
    床関数の代表定義・特徴付け・well-definedness（交差積で商の特徴付けを
    移送して一意性で閉じる）と商上の `qFloor`、上下界 `qFloor_le`/`qFloor_lt`
  * M120F-3 `qFloorNat` / `qFloorNat_upper` — 非負有理数の床の Nat 化と
    床+1 上界（0 ≤ q なら q ≤ floor(q)+1、`Int.toNat_of_nonneg` は
    omega 内蔵の toNat 対応で処理）
  * M120F-4 `qAbs_le_add_sub` — |a| ≤ |b| + |a−b|（a = b + (a−b) の
    群等式 + 三角不等式）
  * M120F-5 `rBound` / `rBound_spec` — **正則列の標準 Nat 上界**:
    ∀n, |xₙ| ≤ floorNat(|x₀|) + 3（|xₙ| ≤ |x₀| + 1/(n+1) + 1/1
    ≤ (floor+1) + 2）。Bishop 乗法の添字スケールを供給する本丸
  * M120F-6 `RatFloorData` — 総括レコードと witness

意義: 柱C（#37）ℝ 第三段（乗法）の準備。floor は有理数の値のみに
依存するため Quot.lift で choice なしに商から Int/Nat を抽出できる
稀有な装置。正則列の一様上界 rBound が Bishop 乗法の添字スケールを供給。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RegularReal

namespace IUT

/-! ## M120F-1: Int の Euclid 除算の一意性 -/

/-- **順序の強消去補題**: 正の d で右から割っても < は保存
    （`int_le_cancel_right` の < 版、対偶 + 単調性）。 -/
theorem int_lt_cancel_right {a b : Int} (d : Int) (hd : 0 < d)
    (h : a * d < b * d) : a < b := by
  cases Int.lt_or_le a b with
  | inl h1 => exact h1
  | inr h1 =>
    have h2 : b * d ≤ a * d :=
      Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hd)
    omega

/-- **M120F-1a: Euclid 除算の一意性** — q·b ≤ a < (q+1)·b なら a / b = q。
    証明は ∀ d r 形の補助命題（b·d + r = a, 0 ≤ r < b なら d = q）に
    隔離し、`Int.mul_ediv_add_emod` 等で instantiate（omega が変数除数の
    / % を扱えないため、除算項を変数 d r に押し込める）。積原子は
    b·q に正規化して omega へ。 -/
theorem int_ediv_unique (a b q : Int) (hb : 0 < b) (h1 : q * b ≤ a)
    (h2 : a < (q + 1) * b) : a / b = q := by
  have key : ∀ d r : Int, b * d + r = a → 0 ≤ r → r < b → d = q := by
    intro d r hdm hr0 hrb
    cases Int.lt_or_le d q with
    | inl hlt =>
      have hm : b * d ≤ b * (q - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hb)
      have e : b * (q - 1) = b * q - b := by rw [Int.mul_sub, Int.mul_one]
      have e2 : q * b = b * q := Int.mul_comm q b
      omega
    | inr hge =>
      cases Int.lt_or_le q d with
      | inl hlt2 =>
        have hm : b * (q + 1) ≤ b * d :=
          Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hb)
        have e : b * (q + 1) = b * q + b := by rw [Int.mul_add, Int.mul_one]
        have e2 : (q + 1) * b = q * b + b := by rw [Int.add_mul, Int.one_mul]
        have e3 : q * b = b * q := Int.mul_comm q b
        omega
      | inr hge2 => omega
  exact key (a / b) (a % b) (Int.mul_ediv_add_emod a b)
    (Int.emod_nonneg a (by omega)) (Int.emod_lt_of_pos a hb)

/-! ## M120F-2: 床関数 -/

/-- **M120F-2a: 床関数の代表** — num / den（Euclid 除算、分母正）。 -/
def prFloor (x : PreRat) : Int := x.num / x.den

/-- **M120F-2b: 床の特徴付け** floor·den ≤ num < (floor+1)·den
    （除算項を ∀ d r 形に隔離して omega）。 -/
theorem prFloor_spec (x : PreRat) :
    prFloor x * x.den ≤ x.num ∧ x.num < (prFloor x + 1) * x.den := by
  have hd := x.den_pos
  have key : ∀ d r : Int, x.den * d + r = x.num → 0 ≤ r → r < x.den →
      d * x.den ≤ x.num ∧ x.num < (d + 1) * x.den := by
    intro d r hdm hr0 hrb
    have e1 : d * x.den = x.den * d := Int.mul_comm d x.den
    have e2 : (d + 1) * x.den = x.den * d + x.den := by
      rw [Int.add_mul, Int.one_mul, Int.mul_comm d x.den]
    exact ⟨by omega, by omega⟩
  exact key (x.num / x.den) (x.num % x.den) (Int.mul_ediv_add_emod x.num x.den)
    (Int.emod_nonneg x.num (by omega)) (Int.emod_lt_of_pos x.num x.den_pos)

/-- **定理 (M120F-2c): 床の well-definedness** — 交差積関係の下で
    prFloor x が y の商の特徴付けを満たすことを示し
    `int_ediv_unique` で閉じる（床は有理数の値のみに依存）。 -/
theorem ratRel_floor {x y : PreRat} (h : ratRel x y) :
    prFloor x = prFloor y := by
  have h' : x.num * y.den = y.num * x.den := h
  have hs := prFloor_spec x
  have low : prFloor x * y.den ≤ y.num := by
    have h1 : prFloor x * x.den * y.den ≤ x.num * y.den :=
      Int.mul_le_mul_of_nonneg_right hs.1 (Int.le_of_lt y.den_pos)
    rw [int_mul_right_swap (prFloor x) x.den y.den, h'] at h1
    exact int_le_cancel_right x.den x.den_pos h1
  have up : y.num < (prFloor x + 1) * y.den := by
    have h3 : x.num * y.den < (prFloor x + 1) * x.den * y.den :=
      Int.mul_lt_mul_of_pos_right hs.2 y.den_pos
    rw [h', int_mul_right_swap (prFloor x + 1) x.den y.den] at h3
    exact int_lt_cancel_right x.den x.den_pos h3
  exact (int_ediv_unique y.num y.den (prFloor x) y.den_pos low up).symm

/-- **M120F-2d: 商上の床関数** — 値のみに依存するため Quot.lift で
    choice なしに商から Int を抽出できる。 -/
def qFloor (q : QRat) : Int :=
  Quot.lift prFloor (fun _ _ h => ratRel_floor h) q

/-- **定理 (M120F-2e): 床は下界** floor(q) ≤ q。 -/
theorem qFloor_le (q : QRat) : qLe (ratOfInt.map (qFloor q)) q := by
  induction q using Quot.ind; rename_i x
  show prFloor x * x.den ≤ x.num * 1
  rw [Int.mul_one]
  exact (prFloor_spec x).1

/-- **定理 (M120F-2f): 床+1 は上界** q ≤ floor(q) + 1。 -/
theorem qFloor_lt (q : QRat) : qLe q (ratOfInt.map (qFloor q + 1)) := by
  induction q using Quot.ind; rename_i x
  show x.num * 1 ≤ (prFloor x + 1) * x.den
  rw [Int.mul_one]
  exact Int.le_of_lt (prFloor_spec x).2

/-! ## M120F-3: 非負床の Nat 化 -/

/-- 床の非負性の核: 0 ≤ num, num < (f+1)·den, 0 < den なら 0 ≤ f
    （f を変数に取り除算項を omega から隠す）。 -/
theorem int_floor_nonneg {f den num : Int} (hden : 0 < den) (hnum : 0 ≤ num)
    (hup : num < (f + 1) * den) : 0 ≤ f := by
  cases Int.lt_or_le f 0 with
  | inl hneg =>
    have h1 : (f + 1) * den ≤ 0 * den :=
      Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hden)
    rw [Int.zero_mul] at h1
    omega
  | inr h => exact h

/-- toNat キャストの橋: 0 ≤ f なら ((f.toNat + 1 : Nat) : Int) = f + 1
    （omega の toNat / cast 内蔵対応、f は変数なので安全）。 -/
theorem int_toNat_cast_add_one {f : Int} (hf : 0 ≤ f) :
    ((f.toNat + 1 : Nat) : Int) = f + 1 := by omega

/-- **M120F-3a: 床の Nat 化**（負の床は 0 に切り上げ）。 -/
def qFloorNat (q : QRat) : Nat := (qFloor q).toNat

/-- **定理 (M120F-3b): 床+1 の Nat 上界** — 0 ≤ q なら
    q ≤ floorNat(q) + 1（非負なら toNat が忠実）。 -/
theorem qFloorNat_upper (q : QRat) (hq : qLe ratRing.zero q) :
    qLe q (ratOfInt.map ((qFloorNat q + 1 : Nat) : Int)) := by
  induction q using Quot.ind; rename_i x
  have hq' : (0 : Int) * x.den ≤ x.num * 1 := hq
  have hnum : 0 ≤ x.num := by omega
  have hf : 0 ≤ prFloor x :=
    int_floor_nonneg x.den_pos hnum (prFloor_spec x).2
  show x.num * 1 ≤ (((prFloor x).toNat + 1 : Nat) : Int) * x.den
  rw [int_toNat_cast_add_one hf, Int.mul_one]
  exact Int.le_of_lt (prFloor_spec x).2

/-! ## M120F-4: 絶対値の逆三角形 -/

/-- **|q| の非負性** 0 ≤ |a|（代表レベルで intAbs の非負性から）。 -/
theorem qAbs_nonneg (a : QRat) : qLe ratRing.zero (qAbs a) := by
  induction a using Quot.ind; rename_i x
  show (0 : Int) * x.den ≤ intAbs x.num * 1
  rw [Int.zero_mul, Int.mul_one]
  exact intAbs_nonneg x.num

/-- **定理 (M120F-4a): |a| ≤ |b| + |a−b|** — a = b + (a−b) の群等式を
    作って三角不等式 `qAbs_add_le` に流す。 -/
theorem qAbs_le_add_sub (a b : QRat) :
    qLe (qAbs a) (qAdd (qAbs b) (qAbs (qAdd a (qNeg b)))) := by
  have e : qAdd b (qAdd a (qNeg b)) = a := by
    rw [qAdd_comm a (qNeg b), ← qAdd_assoc, qAdd_neg_self b, qAdd_zero_left]
  have h := qAbs_add_le b (qAdd a (qNeg b))
  rw [e] at h
  exact h

/-! ## M120F-5: 正則列の標準 Nat 上界（本丸） -/

/-- **M120F-5a: 標準上界** — floorNat(|x₀|) + 3。次層の Bishop 乗法で
    添字スケールに使う一様上界。 -/
def rBound (x : RReal) : Nat := qFloorNat (qAbs (x.seq 0)) + 3

/-- **定理 (M120F-5b): 上界の正当性** — ∀n, |xₙ| ≤ rBound x。
    |xₙ| ≤ |x₀| + |xₙ−x₀| ≤ |x₀| + (1/(n+1) + 1/1)
    ≤ (floorNat(|x₀|)+1) + 2 = floorNat(|x₀|) + 3。 -/
theorem rBound_spec (x : RReal) (n : Nat) :
    qLe (qAbs (x.seq n)) (ratOfInt.map ((rBound x : Nat) : Int)) := by
  have h1 := qAbs_le_add_sub (x.seq n) (x.seq 0)
  have h2 := x.reg n 0
  have h3 := qLe_trans _ _ _ h1
    (qLe_add_two (qLe_refl (qAbs (x.seq 0))) h2)
  have h4 : qLe (qAdd (qUnitFrac n) (qUnitFrac 0)) (qFrac 2 0) :=
    qLe_trans _ _ _ (qLe_add_two (qFrac_le (by omega)) (qLe_refl (qFrac 1 0)))
      (qFrac_add 1 1 0)
  have h5 := qFloorNat_upper (qAbs (x.seq 0)) (qAbs_nonneg (x.seq 0))
  have h6 := qLe_trans _ _ _ h3 (qLe_add_two h5 h4)
  have hB : qLe
      (qAdd (ratOfInt.map ((qFloorNat (qAbs (x.seq 0)) + 1 : Nat) : Int))
        (qFrac 2 0))
      (ratOfInt.map ((qFloorNat (qAbs (x.seq 0)) + 3 : Nat) : Int)) := by
    show (((qFloorNat (qAbs (x.seq 0)) + 1 : Nat) : Int)
          * (((0 : Nat) : Int) + 1) + 2 * 1) * 1
      ≤ ((qFloorNat (qAbs (x.seq 0)) + 3 : Nat) : Int)
          * (1 * (((0 : Nat) : Int) + 1))
    omega
  exact qLe_trans _ _ _ h6 hB

/-! ## M120F-6: 総括 -/

/-- **M120F-6a: 総括** — 床関数の上下界・非負床の Nat 上界・
    正則列の一様上界。 -/
structure RatFloorData where
  /-- 床は下界: floor(q) ≤ q。 -/
  floor_le : ∀ q : QRat, qLe (ratOfInt.map (qFloor q)) q
  /-- 床+1 は上界: q ≤ floor(q) + 1。 -/
  floor_lt : ∀ q : QRat, qLe q (ratOfInt.map (qFloor q + 1))
  /-- 非負床の Nat 上界: 0 ≤ q なら q ≤ floorNat(q) + 1。 -/
  floorNat_upper : ∀ q : QRat, qLe ratRing.zero q →
    qLe q (ratOfInt.map ((qFloorNat q + 1 : Nat) : Int))
  /-- 正則列の一様上界: ∀n, |xₙ| ≤ rBound x。 -/
  abs_bound : ∀ (x : RReal) (n : Nat),
    qLe (qAbs (x.seq n)) (ratOfInt.map ((rBound x : Nat) : Int))

/-- **M120F-6b: witness**。 -/
def ratFloorData : RatFloorData where
  floor_le := qFloor_le
  floor_lt := qFloor_lt
  floorNat_upper := qFloorNat_upper
  abs_bound := rBound_spec

/-- **M120F-6c: 存在**。 -/
theorem ratFloor_exists : Nonempty RatFloorData := ⟨ratFloorData⟩

end IUT
