/-
  IUT/PowerSeries2.lean — M50（二変数冪級数の基盤: 形式群法則への第一層）

  Lubin–Tate 形式群法則 F_f(X,Y) は二変数冪級数。本モジュールは
  **PS2 R := PS(psRing R)（反復構成 R[[X]][[Y]]）** を採用し、
  環構造を M39 からタダで得る。新規に必要なのは**総次数**の概念のみ:

  * M50-1 `PS2` / `ps2X` / `ps2Y` — 反復構成と座標級数
    （X = 定数項埋め込み psC(psX)、Y = psX(psRing R)。係数事実は rfl）
  * M50-2 `rsum_psRing_coeff` — psRing 値の有限和の係数交換
    （(Σ g_b) i = Σ (g_b i)）
  * M50-3 `ps2Pow_tcoeff_zero` — **総次数 truncation**:
    F₀₀ = 0 なら i + j < k で (F^k)_{i,j} = 0。二重和の各項が
    「総次数 < k の冪は帰納法・対角は F₀₀ = 0」で消える
    （M40 の一変数 truncation の二変数版、形式群代入の有限性の根拠）
  * M50-4 `ps2Comp1` — **1変数→2変数代入** (f∘F)_{i,j} =
    Σ_{k≤i+j} f_k·(F^k)_{i,j}（総次数で打ち切る有限和）
  * M50-5 代入の基本性質 — 加法性・1∘F = 1・**X∘F = F**
  * M50-6 `ps2Lin` — 線形部 X + Y とその係数
    （(X+Y)₀₀ = 0・(X+Y)₁₀ = (X+Y)₀₁ = 1 = 形式群法則の一次条件）

  ロードマップ: M50 基盤 → M51 二変数代入 F(P,Q) と f∘F = F∘(f,f) の
  定式化 → M52+ 形式群法則の存在（係数帰納の総次数版）。
  全て選択公理不使用。
-/
import IUT.LubinTateExists

namespace IUT

/-! ## 反復構成と座標 -/

/-- 二変数冪級数 R[[X]][[Y]]（外側が Y、内側が X）。
    係数アクセス: F j i = X^i Y^j の係数。 -/
def PS2 (R : CRing) : Type := PS (psRing R)

/-- 座標 X（Y について定数、X について一次）。 -/
def ps2X (R : CRing) : PS2 R := psC (psRing R) (psX R)

/-- 座標 Y（Y について一次、X について定数）。 -/
def ps2Y (R : CRing) : PS2 R := psX (psRing R)

/-- X の係数: X₀₀ = 0。 -/
theorem ps2X_00 (R : CRing) : ps2X R 0 0 = R.zero := rfl

/-- X の係数: X₁₀ = 1（X^1 Y^0）。 -/
theorem ps2X_10 (R : CRing) : ps2X R 0 1 = R.one := rfl

/-- Y の係数: Y₀₀ = 0。 -/
theorem ps2Y_00 (R : CRing) : ps2Y R 0 0 = R.zero := rfl

/-- Y の係数: Y₀₁ = 1（X^0 Y^1）。 -/
theorem ps2Y_01 (R : CRing) : ps2Y R 1 0 = R.one := rfl

/-! ## 有限和の係数交換 -/

/-- **M50-2**: psRing 値の有限和の係数交換 (Σ_b g_b) i = Σ_b (g_b i)。 -/
theorem rsum_psRing_coeff (R : CRing) (g : Nat → PS R) (i : Nat) : ∀ m,
    rsum (psRing R) g m i = rsum R (fun b => g b i) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    show R.add (rsum (psRing R) g m i) (g m i)
      = R.add (rsum R (fun b => g b i) m) (g m i)
    rw [ih]

/-! ## 総次数 truncation -/

/-- **定理 (M50-3): 総次数 truncation** — F₀₀ = 0 なら
    i + j < k で (F^k)_{i,j} = 0。各項は「総次数 < k の冪は帰納法、
    境界 (a,b) = (i,j) では F₀₀ = 0」で消える。形式群への代入が
    係数ごとに有限和で済む根拠。 -/
theorem ps2Pow_tcoeff_zero (R : CRing) (F : PS2 R) (hF : F 0 0 = R.zero) :
    ∀ k i j, i + j < k → psPow (psRing R) F k j i = R.zero := by
  intro k
  induction k with
  | zero => intro i j h; exact absurd h (by omega)
  | succ k ih =>
    intro i j h
    show (rsum (psRing R) (fun b => (psRing R).mul (psPow (psRing R) F k b)
        (F (j - b))) (j + 1)) i = R.zero
    have h1 : (rsum (psRing R) (fun b => (psRing R).mul (psPow (psRing R) F k b)
          (F (j - b))) (j + 1)) i
        = rsum R (fun b => ((psRing R).mul (psPow (psRing R) F k b)
            (F (j - b))) i) (j + 1) :=
      rsum_psRing_coeff R _ i (j + 1)
    rw [h1]
    have hc : rsum R (fun b => ((psRing R).mul (psPow (psRing R) F k b)
          (F (j - b))) i) (j + 1)
        = rsum R (fun _ => R.zero) (j + 1) :=
      rsum_congr R (j + 1) (fun b hb => by
        show rsum R (fun a => R.mul (psPow (psRing R) F k b a)
            (F (j - b) (i - a))) (i + 1) = R.zero
        have hcc : rsum R (fun a => R.mul (psPow (psRing R) F k b a)
              (F (j - b) (i - a))) (i + 1)
            = rsum R (fun _ => R.zero) (i + 1) :=
          rsum_congr R (i + 1) (fun a ha => by
            cases Nat.lt_or_ge (a + b) k with
            | inl hlt =>
              rw [ih a b hlt]
              exact R.zero_mul _
            | inr hge =>
              have hai : a = i := by omega
              have hbj : b = j := by omega
              rw [hai, hbj, show j - j = 0 by omega, show i - i = 0 by omega,
                hF]
              exact R.mul_zero _)
        rw [hcc]
        exact rsum_const_zero R (i + 1))
    rw [hc]
    exact rsum_const_zero R (j + 1)

/-! ## 1変数→2変数代入 -/

/-- **M50-4: 代入** (f∘F)_{i,j} = Σ_{k≤i+j} f_k·(F^k)_{i,j}
    （F₀₀ = 0 のとき総次数 truncation により真の代入と一致）。 -/
def ps2Comp1 (R : CRing) (f : PS R) (F : PS2 R) : PS2 R :=
  fun j => fun i =>
    rsum R (fun k => R.mul (f k) (psPow (psRing R) F k j i)) (i + j + 1)

/-- 代入の f-加法性。 -/
theorem ps2Comp1_add (R : CRing) (f g : PS R) (F : PS2 R) :
    ps2Comp1 R (psAdd R f g) F
      = psAdd (psRing R) (ps2Comp1 R f F) (ps2Comp1 R g F) := by
  funext j i
  show rsum R (fun k => R.mul (R.add (f k) (g k))
      (psPow (psRing R) F k j i)) (i + j + 1)
    = R.add (rsum R (fun k => R.mul (f k) (psPow (psRing R) F k j i)) (i + j + 1))
        (rsum R (fun k => R.mul (g k) (psPow (psRing R) F k j i)) (i + j + 1))
  have hc : rsum R (fun k => R.mul (R.add (f k) (g k))
        (psPow (psRing R) F k j i)) (i + j + 1)
      = rsum R (fun k => R.add (R.mul (f k) (psPow (psRing R) F k j i))
          (R.mul (g k) (psPow (psRing R) F k j i))) (i + j + 1) :=
    rsum_congr R (i + j + 1) (fun k _ => R.right_distrib _ _ _)
  rw [hc]
  exact rsum_add R _ _ (i + j + 1)

/-- 1∘F = 1。 -/
theorem ps2Comp1_one (R : CRing) (F : PS2 R) :
    ps2Comp1 R (psOne R) F = psOne (psRing R) := by
  funext j i
  show rsum R (fun k => R.mul (psOne R k) (psPow (psRing R) F k j i)) (i + j + 1)
    = psOne (psRing R) j i
  have hs : rsum R (fun k => R.mul (psOne R k)
        (psPow (psRing R) F k j i)) (i + j + 1)
      = R.mul (psOne R 0) (psPow (psRing R) F 0 j i) :=
    rsum_single R _ 0 (i + j + 1) (by omega) (fun l _ hl => by
      rw [show psOne R l = R.zero from if_neg hl]
      exact R.zero_mul _)
  rw [hs]
  show R.mul R.one (psOne (psRing R) j i) = psOne (psRing R) j i
  exact R.one_mul _

/-- **定理 (M50-5): 恒等代入** X∘F = F（F₀₀ = 0）。 -/
theorem ps2Comp1_X (R : CRing) (F : PS2 R) (hF : F 0 0 = R.zero) :
    ps2Comp1 R (psX R) F = F := by
  funext j i
  show rsum R (fun k => R.mul (psX R k) (psPow (psRing R) F k j i)) (i + j + 1)
    = F j i
  cases Nat.decEq (i + j) 0 with
  | isTrue h0 =>
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi
    subst hj
    show R.add R.zero (R.mul (psX R 0) (psPow (psRing R) F 0 0 0)) = F 0 0
    rw [show psX R 0 = R.zero from if_neg (by omega), R.zero_mul, R.zero_add,
      hF]
  | isFalse h0 =>
    have hs : rsum R (fun k => R.mul (psX R k)
          (psPow (psRing R) F k j i)) (i + j + 1)
        = R.mul (psX R 1) (psPow (psRing R) F 1 j i) :=
      rsum_single R _ 1 (i + j + 1) (by omega) (fun l _ hl => by
        rw [show psX R l = R.zero from if_neg hl]
        exact R.zero_mul _)
    rw [hs, show psX R 1 = R.one from if_pos rfl, R.one_mul,
      show psPow (psRing R) F 1 = F from (psRing (psRing R)).one_mul F]

/-! ## 線形部 X + Y -/

/-- 形式群法則の線形部 X + Y。 -/
def ps2Lin (R : CRing) : PS2 R := psAdd (psRing R) (ps2X R) (ps2Y R)

/-- (X+Y)₀₀ = 0。 -/
theorem ps2Lin_00 (R : CRing) : ps2Lin R 0 0 = R.zero := by
  show R.add (ps2X R 0 0) (ps2Y R 0 0) = R.zero
  rw [ps2X_00, ps2Y_00, R.zero_add]

/-- (X+Y)₁₀ = 1。 -/
theorem ps2Lin_10 (R : CRing) : ps2Lin R 0 1 = R.one := by
  show R.add (ps2X R 0 1) (ps2Y R 0 1) = R.one
  rw [ps2X_10, show ps2Y R 0 1 = R.zero from rfl, R.add_zero]

/-- (X+Y)₀₁ = 1。 -/
theorem ps2Lin_01 (R : CRing) : ps2Lin R 1 0 = R.one := by
  show R.add (ps2X R 1 0) (ps2Y R 1 0) = R.one
  rw [ps2Y_01, show ps2X R 1 0 = R.zero from rfl, R.zero_add]

end IUT
