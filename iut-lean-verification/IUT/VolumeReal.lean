/-
# M132: ガウス体積簿記の ℝ 化 — 系3.12 不等式の実数形（E-2）

柱E E-2（issue #39）の橋部分。M93（柱E E-8: 離散ガウス体積簿記）の
閉形式と下界を、M131F の橋（C-1）を通して**本物の実数 ℝ**
（M115F〜M130）の言葉に持ち上げる。[IUTchIV] の log-volume 計算が
実数の等式・不等式として機械検証の土俵に乗る。

  * M132-1 `natToReal` — ℕ → ℝ 埋め込みと単調・加法・乗法
  * M132-2 `ssq_closed_real` / `stri_closed_real` — 閉形式の実数化
    6·Σj² = l(l+1)(2l+1)・6·Σtri = l(l+1)(l+2)（realEq）
  * M132-3 `ssq_stri_real` — 指数橋 Σj² + Σj = 2Σtri の実数化
  * M132-4 **`cube_le_ssq_real`（本丸）** — 体積下界 l³ ≤ 3Σj² が
    rLe として成立（テータパイロット総 q-次数の実数下界 =
    系3.12 の体積側の実数形）
  * M132-5 `VolumeRealData` — 総括

正直な限定: rlogVol（M131F）との合流（ガウス因子の QDiv 実装と
その次数 = ssq の同定）は M12 側の因子構成を要し次層。実数の
除算（l³/3 形の言い直し）は逆元理論の整備後。

全て選択公理不使用。
-/
import IUT.LogVolBridge
import IUT.GaussianVolume

namespace IUT

/-! ## M132-1: ℕ → ℝ 埋め込み -/

/-- **M132-1a: 埋め込み** ℕ → ℝ（定数列）。 -/
def natToReal (a : Nat) : RReal :=
  qToReal (ratOfInt.map ((a : Nat) : Int))

/-- **M132-1b: 単調性**。 -/
theorem natToReal_mono {a b : Nat} (h : a ≤ b) :
    rLe (natToReal a) (natToReal b) :=
  qToReal_mono (ratOfInt_le (by omega))

/-- **M132-1c: 加法性**。 -/
theorem natToReal_add (a b : Nat) :
    realEq (realAdd (natToReal a) (natToReal b)) (natToReal (a + b)) := by
  have e : qAdd (ratOfInt.map ((a : Nat) : Int))
      (ratOfInt.map ((b : Nat) : Int))
      = ratOfInt.map (((a + b : Nat) : Nat) : Int) := by
    have e2 : (((a + b : Nat) : Nat) : Int)
        = ((a : Nat) : Int) + ((b : Nat) : Int) := by omega
    rw [e2]
    exact (ratOfInt.map_add _ _).symm
  have h1 := qToReal_add (ratOfInt.map ((a : Nat) : Int))
    (ratOfInt.map ((b : Nat) : Int))
  rw [e] at h1
  exact h1

/-- **M132-1d: 乗法性**。 -/
theorem natToReal_mul (a b : Nat) :
    realEq (rmul (natToReal a) (natToReal b)) (natToReal (a * b)) := by
  have e : qMul (ratOfInt.map ((a : Nat) : Int))
      (ratOfInt.map ((b : Nat) : Int))
      = ratOfInt.map (((a * b : Nat) : Nat) : Int) := by
    have e2 : (((a * b : Nat) : Nat) : Int)
        = ((a : Nat) : Int) * ((b : Nat) : Int) := by
      rw [Int.natCast_mul]
    rw [e2]
    exact (ratOfInt.map_mul _ _).symm
  have h1 := qToReal_mul (ratOfInt.map ((a : Nat) : Int))
    (ratOfInt.map ((b : Nat) : Int))
  rw [e] at h1
  exact h1

/-! ## M132-2: 閉形式の実数化 -/

/-- **定理 (M132-2a): 平方和閉形式の実数形** —
    6·Σj² = l(l+1)(2l+1)（realEq）。 -/
theorem ssq_closed_real (l : Nat) :
    realEq (rmul (natToReal 6) (natToReal (ssq l)))
      (natToReal (l * (l + 1) * (2 * l + 1))) := by
  have h := natToReal_mul 6 (ssq l)
  rw [ssq_closed l] at h
  exact h

/-- **定理 (M132-2b): 四面体数閉形式の実数形** —
    6·Σtri = l(l+1)(l+2)（realEq）。 -/
theorem stri_closed_real (l : Nat) :
    realEq (rmul (natToReal 6) (natToReal (stri l)))
      (natToReal (l * (l + 1) * (l + 2))) := by
  have h := natToReal_mul 6 (stri l)
  rw [stri_closed l] at h
  exact h

/-! ## M132-3: 指数橋の実数化 -/

/-- **定理 (M132-3): 指数橋の実数形** — Σj² + Σj = 2Σtri（realEq、
    [IUTchI] の q^{j²} 正規化と q^{tri j} 座席の換算の実数版）。 -/
theorem ssq_stri_real (l : Nat) :
    realEq (realAdd (natToReal (ssq l)) (natToReal (tri l)))
      (rmul (natToReal 2) (natToReal (stri l))) := by
  have h1 := natToReal_add (ssq l) (tri l)
  have h2 := natToReal_mul 2 (stri l)
  rw [ssq_stri l] at h1
  exact realEq_trans h1 (realEq_symm h2)

/-! ## M132-4: 体積下界（本丸） -/

/-- **定理 (M132-4): ガウス体積下界の実数形（本丸）** —
    l³ ≤ 3·Σj² が rLe として成立。テータパイロットの総 q-次数の
    実数下界 = 系3.12 の体積側ステートメントの実数形。 -/
theorem cube_le_ssq_real (l : Nat) :
    rLe (natToReal (l * l * l))
      (rmul (natToReal 3) (natToReal (ssq l))) :=
  rLe_trans (natToReal_mono (cube_le_ssq l))
    (rLe_of_realEq (realEq_symm (natToReal_mul 3 (ssq l))))

/-! ## M132-5: 総括 -/

/-- **M132-5a: 総括** — 体積簿記の実数形データ。 -/
structure VolumeRealData where
  /-- 埋め込みの単調性。 -/
  mono : ∀ {a b : Nat}, a ≤ b → rLe (natToReal a) (natToReal b)
  /-- 埋め込みの加法性。 -/
  add : ∀ a b, realEq (realAdd (natToReal a) (natToReal b))
    (natToReal (a + b))
  /-- 埋め込みの乗法性。 -/
  mul : ∀ a b, realEq (rmul (natToReal a) (natToReal b))
    (natToReal (a * b))
  /-- 平方和閉形式（実数形）。 -/
  ssq_closed : ∀ l, realEq (rmul (natToReal 6) (natToReal (ssq l)))
    (natToReal (l * (l + 1) * (2 * l + 1)))
  /-- 四面体数閉形式（実数形）。 -/
  stri_closed : ∀ l, realEq (rmul (natToReal 6) (natToReal (stri l)))
    (natToReal (l * (l + 1) * (l + 2)))
  /-- 指数橋（実数形）。 -/
  exp_bridge : ∀ l, realEq
    (realAdd (natToReal (ssq l)) (natToReal (tri l)))
    (rmul (natToReal 2) (natToReal (stri l)))
  /-- 体積下界（実数形、本丸）。 -/
  cube_bound : ∀ l, rLe (natToReal (l * l * l))
    (rmul (natToReal 3) (natToReal (ssq l)))

/-- **M132-5b: witness**。 -/
def volumeRealData : VolumeRealData where
  mono := natToReal_mono
  add := natToReal_add
  mul := natToReal_mul
  ssq_closed := ssq_closed_real
  stri_closed := stri_closed_real
  exp_bridge := ssq_stri_real
  cube_bound := cube_le_ssq_real

/-- **M132-5c: 存在**。 -/
theorem volumeReal_exists : Nonempty VolumeRealData :=
  ⟨volumeRealData⟩

end IUT
