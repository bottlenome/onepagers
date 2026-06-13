/-
  IUT/GaussianVolume.lean — M93（ガウス体積簿記 vol_q: 柱E・E8）

  IUT の「テータ関数 ↔ ガウス積分」類比の離散簿記を機械検証する。
  テータパイロットの q-冪は j = 1, …, l にわたる q^{j²} 系であり、
  その**総 log-volume（q-次数の総和）の閉形式と下界**が系3.12 の
  不等式側の入力になる。本層は分母を払った Nat 恒等式として:

  (1) **平方和の閉形式** 6·Σj² = l(l+1)(2l+1)（ssq_closed）;
  (2) **三角数和（四面体数）の閉形式** 6·Σ tri j = l(l+1)(l+2)
      （stri_closed — M92 のテータ対角次数 tri j の総和）;
  (3) **指数橋** j² + j = 2·tri j — [IUTchI] の q^{j²} 正規化と
      本系列の q^{tri j}（M90/M92 のガウス値の座席）の換算式;
  (4) **総和橋** Σj² + tri l = 2·Σtri（(3) の総和形）;
  (5) **ガウス積分の離散下界** l³ ≤ 3·Σj²（Σx² ~ ∫x² = l³/3 の
      離散版 — テータパイロット次数の体積下界）;
  (6) 総括 GaussianVolumeData: (1)–(5) + M92 の仮定なしガウス値
      （T^j(Θ) の q^{tri j} u^j 係数 = 1）を束ねた E8 witness。

  非線形恒等式は全て「展開補題で単項式原子 {l, l², l³} の線形式に
  落として omega」の定型で処理（gauss_bridge 方式の Nat 版）。

  * M93-1 `ssq` / `cube_expand` / `ssq_closed` — 平方和の閉形式
  * M93-2 `stri` / `stri_closed` — 四面体数の閉形式
  * M93-3 `sq_exponent` / `ssq_stri` — q^{j²} ↔ q^{tri j} の指数橋
  * M93-4 `cube_le_ssq` — **ガウス積分の離散下界（本丸）**
  * M93-5 `GaussianVolumeData` / `gaussianVolume` /
    `gaussian_volume_exists` — **E8 総括 witness**

  実数 log-volume（ℝ 化 = Realification 系との接続）・系3.12 の
  不等式本体（柱D）は未形式化。全て選択公理不使用。
-/
import IUT.MonoThetaWitness

namespace IUT

/-! ## 平方和の閉形式 -/

/-- **M93-1a: 平方和** ssq l = 1² + 2² + … + l²。 -/
def ssq : Nat → Nat
  | 0 => 0
  | l + 1 => ssq l + (l + 1) * (l + 1)

/-- **M93-1b: 三次の展開補題** x(x+1)(2x+1) = 2x³ + 3x² + x。 -/
theorem cube_expand (x : Nat) :
    x * (x + 1) * (2 * x + 1) = 2 * (x * x * x) + 3 * (x * x) + x := by
  have c1 : x * (x + 1) = x * x + x := Nat.mul_succ x x
  rw [c1, Nat.add_mul]
  have c2 : (x * x) * (2 * x + 1) = (x * x) * (2 * x) + x * x :=
    Nat.mul_succ (x * x) (2 * x)
  have c3 : x * (2 * x + 1) = x * (2 * x) + x := Nat.mul_succ x (2 * x)
  have d1 : (x * x) * (2 * x) = 2 * (x * x * x) := by
    rw [← Nat.mul_assoc (x * x) 2 x, Nat.mul_comm (x * x) 2,
      Nat.mul_assoc 2 (x * x) x]
  have d2 : x * (2 * x) = 2 * (x * x) := by
    rw [← Nat.mul_assoc x 2 x, Nat.mul_comm x 2, Nat.mul_assoc 2 x x]
  omega

/-- 二次の展開補題 (x+1)² = x² + 2x + 1。 -/
theorem sq_expand (x : Nat) : (x + 1) * (x + 1) = x * x + 2 * x + 1 := by
  rw [Nat.add_mul, Nat.one_mul]
  have c1 : x * (x + 1) = x * x + x := Nat.mul_succ x x
  omega

/-- 三乗の展開補題 (x+1)³ = x³ + 3x² + 3x + 1。 -/
theorem cube_succ_expand (x : Nat) :
    (x + 1) * (x + 1) * (x + 1) = x * x * x + 3 * (x * x) + 3 * x + 1 := by
  rw [sq_expand, Nat.add_mul, Nat.add_mul]
  have c1 : (x * x) * (x + 1) = (x * x) * x + x * x := Nat.mul_succ (x * x) x
  have c2 : (2 * x) * (x + 1) = (2 * x) * x + 2 * x := Nat.mul_succ (2 * x) x
  have c3 : (2 * x) * x = 2 * (x * x) := Nat.mul_assoc 2 x x
  have c4 : 1 * (x + 1) = x + 1 := Nat.one_mul (x + 1)
  omega

/-- **定理 (M93-1c): 平方和の閉形式** 6·Σj² = l(l+1)(2l+1)。 -/
theorem ssq_closed : ∀ l, 6 * ssq l = l * (l + 1) * (2 * l + 1) := by
  intro l
  induction l with
  | zero => rfl
  | succ l ih =>
    have hs : ssq (l + 1) = ssq l + (l + 1) * (l + 1) := rfl
    have e1 := cube_expand (l + 1)
    have e2 := cube_expand l
    have e3 := sq_expand l
    have e4 := cube_succ_expand l
    omega

/-! ## 四面体数（テータ対角次数の総和）の閉形式 -/

/-- **M93-2a: 三角数の総和（四面体数）** stri l = tri 1 + … + tri l —
    テータパイロットの対角 q-次数（M92）の総和。 -/
def stri : Nat → Nat
  | 0 => 0
  | l + 1 => stri l + tri (l + 1)

/-- **定理 (M93-2b): 四面体数の閉形式** 6·Σtri = l(l+1)(l+2)。 -/
theorem stri_closed : ∀ l, 6 * stri l = l * (l + 1) * (l + 2) := by
  intro l
  induction l with
  | zero => rfl
  | succ l ih =>
    show 6 * stri (l + 1) = (l + 1) * (l + 2) * (l + 3)
    have hs : stri (l + 1) = stri l + tri (l + 1) := rfl
    -- 6·tri(l+1) = 3·(l+1)(l+2)（原子を (l+2) 形に正規化）
    have htri : 2 * tri (l + 1) = (l + 1) * (l + 2) := tri_nat (l + 1)
    -- 展開: 両辺を {l³, l², l} の線形式へ
    have e1 : l * (l + 1) = l * l + l := Nat.mul_succ l l
    have e2 : l * (l + 1) * (l + 2)
        = (l * l) * (l + 2) + l * (l + 2) := by
      rw [e1, Nat.add_mul]
    have e3 : (l * l) * (l + 2) = (l * l) * l + 2 * (l * l) := by
      have h1 : (l * l) * (l + 2) = (l * l) * (l + 1) + l * l :=
        Nat.mul_succ (l * l) (l + 1)
      have h2 : (l * l) * (l + 1) = (l * l) * l + l * l :=
        Nat.mul_succ (l * l) l
      omega
    have e4 : l * (l + 2) = l * l + 2 * l := by
      have h1 : l * (l + 2) = l * (l + 1) + l := Nat.mul_succ l (l + 1)
      omega
    have e5 : (l + 1) * (l + 2) = l * l + 3 * l + 2 := by
      have h1 : (l + 1) * (l + 2) = (l + 1) * (l + 1) + (l + 1) :=
        Nat.mul_succ (l + 1) (l + 1)
      have h2 := sq_expand l
      omega
    have e6 : (l + 1) * (l + 2) * (l + 3)
        = l * l * l + 6 * (l * l) + 11 * l + 6 := by
      rw [e5, Nat.add_mul, Nat.add_mul]
      have h1 : (l * l) * (l + 3) = (l * l) * l + 3 * (l * l) := by
        have g1 : (l * l) * (l + 3) = (l * l) * (l + 2) + l * l :=
          Nat.mul_succ (l * l) (l + 2)
        omega
      have h2 : (3 * l) * (l + 3) = 3 * (l * l) + 9 * l := by
        have g1 : (3 * l) * (l + 3) = (3 * l) * (l + 2) + 3 * l :=
          Nat.mul_succ (3 * l) (l + 2)
        have g2 : (3 * l) * (l + 2) = (3 * l) * (l + 1) + 3 * l :=
          Nat.mul_succ (3 * l) (l + 1)
        have g3 : (3 * l) * (l + 1) = (3 * l) * l + 3 * l :=
          Nat.mul_succ (3 * l) l
        have g4 : (3 * l) * l = 3 * (l * l) := Nat.mul_assoc 3 l l
        omega
      omega
    omega

/-! ## 指数橋: q^{j²} 正規化 ↔ q^{tri j} 座席 -/

/-- **定理 (M93-3a): 指数橋** j² + j = 2·tri j — [IUTchI] の
    テータ値 q^{j²} と本系列の対角座席 q^{tri j}（M90/M92）の換算。 -/
theorem sq_exponent (j : Nat) : j * j + j = 2 * tri j := by
  have h := tri_nat j
  have e : j * (j + 1) = j * j + j := Nat.mul_succ j j
  omega

/-- **定理 (M93-3b): 総和橋** Σj² + tri l = 2·Σtri（指数橋の総和形 —
    Σj = tri l を込めて）。 -/
theorem ssq_stri : ∀ l, ssq l + tri l = 2 * stri l := by
  intro l
  induction l with
  | zero => rfl
  | succ l ih =>
    have h1 : ssq (l + 1) = ssq l + (l + 1) * (l + 1) := rfl
    have h2 : tri (l + 1) = tri l + (l + 1) := rfl
    have h3 : stri (l + 1) = stri l + tri (l + 1) := rfl
    have h4 := sq_exponent (l + 1)
    omega

/-! ## ガウス積分の離散下界（本丸） -/

/-- **定理 (M93-4): ガウス積分の離散下界** l³ ≤ 3·Σj²
    （Σx² ~ ∫₀^l x² dx = l³/3 の離散版 — テータパイロットの
    総 q-次数（log-volume）の体積下界）。 -/
theorem cube_le_ssq (l : Nat) : l * l * l ≤ 3 * ssq l := by
  have h := ssq_closed l
  have hc := cube_expand l
  omega

/-! ## E8 総括 witness -/

/-- **M93-5a: ガウス体積簿記の総括**（E8）— 閉形式・指数橋・
    体積下界・M92 の仮定なしガウス値を束ねる。 -/
structure GaussianVolumeData where
  /-- 平方和の閉形式 6·Σj² = l(l+1)(2l+1)。 -/
  ssq_formula : ∀ l, 6 * ssq l = l * (l + 1) * (2 * l + 1)
  /-- 四面体数の閉形式 6·Σtri = l(l+1)(l+2)。 -/
  stri_formula : ∀ l, 6 * stri l = l * (l + 1) * (l + 2)
  /-- 指数橋 j² + j = 2·tri j。 -/
  exponent_bridge : ∀ j, j * j + j = 2 * tri j
  /-- 総和橋 Σj² + tri l = 2·Σtri。 -/
  total_bridge : ∀ l, ssq l + tri l = 2 * stri l
  /-- ガウス積分の離散下界 l³ ≤ 3·Σj²。 -/
  volume_lower : ∀ l, l * l * l ≤ 3 * ssq l
  /-- 解析側の座席: T^j(Θ) の q^{tri j} u^j 係数 = 1（M92）。 -/
  values : ∀ (R : CRing) (j : Nat), tCoeff R j (tri j) ((j : Int)) = R.one

/-- **M93-5b: witness 本体**。 -/
def gaussianVolume : GaussianVolumeData where
  ssq_formula := ssq_closed
  stri_formula := stri_closed
  exponent_bridge := sq_exponent
  total_bridge := ssq_stri
  volume_lower := cube_le_ssq
  values := theta_gauss_tri

/-- **定理 (M93-5c): ガウス体積簿記の存在（E8 見出し）**。 -/
theorem gaussian_volume_exists : Nonempty GaussianVolumeData :=
  ⟨gaussianVolume⟩

end IUT
