/-
# M142F: 整数・実数橋の環準同型性 — intToReal の加法・乗法・負元と忠実性

柱C C-1。M139 で導入した `intToReal : ℤ → ℝ`（M132 の natToReal の
Int 版、定数列埋め込み qToReal ∘ ratOfInt）は順序埋め込み
（intToReal_mono / intToReal_reflect）としてのみ整備されていた。
本層はこれを**環準同型**（加法・乗法・負元・減法との realEq 両立）に
格上げし、natToReal・rlogVol との整合を固める:

  * M142F-1 `intToReal_natCast` — ℕ 経由の可換三角形
    intToReal ∘ (ℕ → ℤ) = natToReal（定義的等式 rfl）
  * M142F-2 `intToReal_add` — 加法性
    intToReal a + intToReal b ≈ intToReal (a + b)
    （qToReal_add + ratOfInt.map_add。natToReal_add のパターンから
    Nat→Int キャスト調整を抜いた形）
  * M142F-3 `intToReal_mul` — 乗法性（qToReal_mul + ratOfInt.map_mul）
  * M142F-4 `qNeg_ratOfInt` — 代表レベルの負元両立
    qNeg (ι a) = ι (−a)（分子 −a・分母 1 の代表がそのまま一致）
  * M142F-5 `intToReal_neg` — 負元両立
    −intToReal a ≈ intToReal (−a)（realNeg は点ごと qNeg なので
    M142F-4 から列が一致 → realEq_of_seq_eq）
  * M142F-6 `intToReal_sub` — 減法両立（M142F-2 + M142F-5 の合成、
    realAdd_congr_right + realEq_trans）
  * M142F-7 `rlogVol_eq_intToReal` — **実数値 log-volume は整数次数の
    intToReal 像そのもの**: rlogVol w x = intToReal (degZ w x)
    （M131F の橋 qToReal ∘ ratOfInt ∘ degZ の最短表示、定義的等式）
  * M142F-8 `natToReal_reflect` — **natToReal の順序埋め込みの忠実性**:
    実数の不等式 natToReal a ≤ natToReal b から a ≤ b へ降下
    （intToReal_reflect + M142F-1 + omega）
  * M142F-9 `IntRealBridgeData` — 総括

## 意義

M139 の intToReal を順序埋め込みから**環準同型 + 順序忠実**に格上げ。
柱D の実数値体積理論の整数橋が全演算と両立し、Int 値の体積簿記
（次数・log-volume）の加減乗が実数の土俵でそのまま計算できる。
rlogVol = intToReal ∘ degZ の同定（M142F-7）により、M131F の実数値
log-volume の全法則が intToReal の環準同型性の系として読み直せる。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealVolumeTheory

namespace IUT

/-! ## M142F-1: ℕ 経由の可換三角形 -/

/-- **M142F-1: natCast 整合** — intToReal ∘ (ℕ → ℤ) = natToReal
    （両辺とも qToReal (ratOfInt.map ((a : Nat) : Int))、定義的等式）。 -/
theorem intToReal_natCast (a : Nat) :
    intToReal ((a : Nat) : Int) = natToReal a := rfl

/-! ## M142F-2: 加法性 -/

/-- **定理 (M142F-2): 加法性** — intToReal a + intToReal b ≈
    intToReal (a + b)（qToReal_add + ratOfInt.map_add。
    natToReal_add のパターンからキャスト調整を抜いた形）。 -/
theorem intToReal_add (a b : Int) :
    realEq (realAdd (intToReal a) (intToReal b)) (intToReal (a + b)) := by
  have e : qAdd (ratOfInt.map a) (ratOfInt.map b) = ratOfInt.map (a + b) :=
    (ratOfInt.map_add a b).symm
  have h1 := qToReal_add (ratOfInt.map a) (ratOfInt.map b)
  rw [e] at h1
  exact h1

/-! ## M142F-3: 乗法性 -/

/-- **定理 (M142F-3): 乗法性** — intToReal a · intToReal b ≈
    intToReal (a · b)（qToReal_mul + ratOfInt.map_mul）。 -/
theorem intToReal_mul (a b : Int) :
    realEq (rmul (intToReal a) (intToReal b)) (intToReal (a * b)) := by
  have e : qMul (ratOfInt.map a) (ratOfInt.map b) = ratOfInt.map (a * b) :=
    (ratOfInt.map_mul a b).symm
  have h1 := qToReal_mul (ratOfInt.map a) (ratOfInt.map b)
  rw [e] at h1
  exact h1

/-! ## M142F-4: 代表レベルの負元両立 -/

/-- **M142F-4: 負元の代表計算** — qNeg (ι a) = ι (−a)
    （prNeg ⟨a, 1⟩ = ⟨−a, 1⟩ = intToPreRat (−a)、定義的等式）。 -/
theorem qNeg_ratOfInt (a : Int) :
    qNeg (ratOfInt.map a) = ratOfInt.map (-a) := rfl

/-! ## M142F-5: 負元両立 -/

/-- **定理 (M142F-5): 負元両立** — −intToReal a ≈ intToReal (−a)
    （realNeg は点ごと qNeg なので M142F-4 から列が一致）。 -/
theorem intToReal_neg (a : Int) :
    realEq (realNeg (intToReal a)) (intToReal (-a)) :=
  realEq_of_seq_eq (fun _ => qNeg_ratOfInt a)

/-! ## M142F-6: 減法両立 -/

/-- **定理 (M142F-6): 減法両立** — intToReal a − intToReal b ≈
    intToReal (a − b)（加法性 + 負元両立の合成）。 -/
theorem intToReal_sub (a b : Int) :
    realEq (realAdd (intToReal a) (realNeg (intToReal b)))
      (intToReal (a - b)) := by
  have h1 : realEq (realAdd (intToReal a) (realNeg (intToReal b)))
      (realAdd (intToReal a) (intToReal (-b))) :=
    realAdd_congr_right (intToReal a) (intToReal_neg b)
  have h2 := intToReal_add a (-b)
  have e : a + (-b) = a - b := by omega
  rw [e] at h2
  exact realEq_trans h1 h2

/-! ## M142F-7: rlogVol との整合（M131F の橋の最短表示） -/

/-- **定理 (M142F-7): 実数値 log-volume は整数次数の intToReal 像
    そのもの** — rlogVol w x = intToReal (degZ w x)
    （qToReal ∘ ratOfInt ∘ degZ の合成が定義的に一致）。 -/
theorem rlogVol_eq_intToReal (w : Nat → Nat) (x : QDiv) :
    rlogVol w x = intToReal (degZ w x) := rfl

/-! ## M142F-8: natToReal の順序忠実性 -/

/-- **定理 (M142F-8): natToReal の順序埋め込みの忠実性** —
    実数の不等式 natToReal a ≤ natToReal b から自然数の a ≤ b へ降下
    （intToReal_reflect の ε-消去 + natCast 整合 + omega）。 -/
theorem natToReal_reflect {a b : Nat}
    (h : rLe (natToReal a) (natToReal b)) : a ≤ b := by
  have h' : rLe (intToReal ((a : Nat) : Int)) (intToReal ((b : Nat) : Int)) := by
    rw [intToReal_natCast, intToReal_natCast]
    exact h
  have h2 : ((a : Nat) : Int) ≤ ((b : Nat) : Int) := intToReal_reflect h'
  omega

/-! ## M142F-9: 総括 -/

/-- **M142F-9a: 総括** — 整数・実数橋の環準同型性データ。 -/
structure IntRealBridgeData where
  /-- 加法性。 -/
  add : ∀ a b : Int,
    realEq (realAdd (intToReal a) (intToReal b)) (intToReal (a + b))
  /-- 乗法性。 -/
  mul : ∀ a b : Int,
    realEq (rmul (intToReal a) (intToReal b)) (intToReal (a * b))
  /-- 負元両立。 -/
  neg : ∀ a : Int, realEq (realNeg (intToReal a)) (intToReal (-a))
  /-- 減法両立。 -/
  sub : ∀ a b : Int,
    realEq (realAdd (intToReal a) (realNeg (intToReal b)))
      (intToReal (a - b))
  /-- natCast 整合: intToReal ∘ (ℕ → ℤ) = natToReal。 -/
  natCast : ∀ a : Nat, intToReal ((a : Nat) : Int) = natToReal a
  /-- rlogVol の表示: 実数値 log-volume = 整数次数の intToReal 像。 -/
  rlogvol : ∀ (w : Nat → Nat) (x : QDiv),
    rlogVol w x = intToReal (degZ w x)
  /-- intToReal の順序忠実性（M139 の反映）。 -/
  int_reflect : ∀ {a b : Int},
    rLe (intToReal a) (intToReal b) → a ≤ b
  /-- natToReal の順序忠実性。 -/
  nat_reflect : ∀ {a b : Nat},
    rLe (natToReal a) (natToReal b) → a ≤ b

/-- **M142F-9b: witness**。 -/
def intRealBridgeData : IntRealBridgeData where
  add := intToReal_add
  mul := intToReal_mul
  neg := intToReal_neg
  sub := intToReal_sub
  natCast := intToReal_natCast
  rlogvol := rlogVol_eq_intToReal
  int_reflect := intToReal_reflect
  nat_reflect := natToReal_reflect

/-- **M142F-9c: 存在**。 -/
theorem intRealBridge_exists : Nonempty IntRealBridgeData :=
  ⟨intRealBridgeData⟩

end IUT
