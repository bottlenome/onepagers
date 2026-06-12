/-
  IUT/FormalGroupCongr.lean — M57（二変数冪の係数合同補題: 形式群第七層）

  LT 形式群法則の存在を総次数の係数再帰で構成するための**礎石**:

    k ≥ 2 のとき (F^k)_{j,i} は F の総次数 ≤ i+j−1 の係数のみで決まる

  （M41 の一変数 psPow_coeff_congr の二変数版）。これにより
  方程式の総次数 n の部分 F_{j,i}·(pⁿ − p) = (低次データ) において
  右辺が既決定の係数だけに依存することが保証され、再帰が回る。

  証明の核は **積の係数合同**（M57-2）: A·B の (j,i) 係数は二重
  Cauchy 和 Σ_{k≤j} Σ_{l≤i} A_{k,l}·B_{j−k,i−l} で、定数項消滅
  （A₀₀ = B₀₀ = 0）のもと各項は
  (1) 因子1が (0,0) → 両辺 0、(2) 因子2が (0,0) → 両辺 0、
  (3) 双方総次数 ≥ 1 → 双方総次数 ≤ n−1 で合同仮定が適用、
  の三分で処理される。冪は k についての帰納（因子1 = F^{k+2} の
  定数項消滅は M50 の総次数 truncation）。

  * M57-1 `ps2Mul_coeff` / `ps2Pow_one` — 積の二重 Cauchy 係数公式
    （M50 の rsum_psRing_coeff で外側の級数和を係数和に変換）と F¹ = F
  * M57-2 `ps2Mul_coeff_congr` — **積の係数合同**（三分処理）
  * M57-3 `ps2Pow_coeff_congr` / `ps2Pow_coeff_congr'` —
    **冪の係数合同**: F₀₀ = F'₀₀ = 0 かつ総次数 < n で F = F' なら、
    q ≥ 2 で総次数 ≤ n の (F^q) = (F'^q)

  ロードマップ: 次層で方程式の総次数分解（f∘F の k ∈ {1, p} 集中・
  F(fX, fY) の対角先頭項 pⁿ·F_{j,i}）→ 係数再帰による存在。
  全て選択公理不使用。
-/
import IUT.FormalGroupErr

namespace IUT

/-! ## 積の係数公式 -/

/-- **M57-1a: 二変数積の二重 Cauchy 係数公式** —
    (A·B)_{j,i} = Σ_{k≤j} Σ_{l≤i} A_{k,l}·B_{j−k,i−l}
    （外側の psRing 値 rsum を M50 の rsum_psRing_coeff で係数化、
    内側は psMul の定義透過）。 -/
theorem ps2Mul_coeff (R : CRing) (A B : PS2 R) (j i : Nat) :
    psMul (psRing R) A B j i
      = rsum R (fun k => rsum R
          (fun l => R.mul (A k l) (B (j - k) (i - l))) (i + 1)) (j + 1) :=
  rsum_psRing_coeff R (fun k => (psRing R).mul (A k) (B (j - k))) i (j + 1)

/-- **M57-1b**: F¹ = F。 -/
theorem ps2Pow_one (R : CRing) (F : PS2 R) : psPow (psRing R) F 1 = F :=
  (psRing (psRing R)).one_mul F

/-! ## 積の係数合同 -/

/-- **定理 (M57-2): 積の係数合同** — A₀₀ = A'₀₀ = B₀₀ = B'₀₀ = 0 かつ
    総次数 < n で A = A'・B = B' なら、総次数 ≤ n で A·B = A'·B'。
    （三分処理: 因子1 = (0,0) → 0、因子2 = (0,0) → 0、双方 ≥ 1 →
    双方 ≤ n−1 で合同仮定。） -/
theorem ps2Mul_coeff_congr (R : CRing) {A A' B B' : PS2 R} (n : Nat)
    (hA00 : A 0 0 = R.zero) (hA00' : A' 0 0 = R.zero)
    (hB00 : B 0 0 = R.zero) (hB00' : B' 0 0 = R.zero)
    (hA : ∀ j i, i + j < n → A j i = A' j i)
    (hB : ∀ j i, i + j < n → B j i = B' j i) :
    ∀ j i, i + j ≤ n →
      psMul (psRing R) A B j i = psMul (psRing R) A' B' j i := by
  intro j i hij
  rw [ps2Mul_coeff R A B j i, ps2Mul_coeff R A' B' j i]
  exact rsum_congr R (j + 1) (fun k hk =>
    rsum_congr R (i + 1) (fun l hl => by
      cases Nat.decEq (k + l) 0 with
      | isTrue h0 =>
        have hk0 : k = 0 := by omega
        have hl0 : l = 0 := by omega
        subst hk0
        subst hl0
        rw [hA00, hA00', R.zero_mul, R.zero_mul]
      | isFalse h0 =>
        cases Nat.decEq ((j - k) + (i - l)) 0 with
        | isTrue h1 =>
          have hjk : j - k = 0 := by omega
          have hil : i - l = 0 := by omega
          rw [hjk, hil, hB00, hB00', R.mul_zero, R.mul_zero]
        | isFalse h1 =>
          rw [hA k l (by omega), hB (j - k) (i - l) (by omega)]))

/-! ## 冪の係数合同 -/

/-- **定理 (M57-3a): 冪の係数合同（k+2 形）** — F₀₀ = F'₀₀ = 0 かつ
    総次数 < n で F = F' なら、総次数 ≤ n で (F^{k+2}) = (F'^{k+2})。
    帰納の因子1（F^{m+2}）の定数項消滅は M50 の総次数 truncation。 -/
theorem ps2Pow_coeff_congr (R : CRing) {F F' : PS2 R} (n : Nat)
    (hF : F 0 0 = R.zero) (hF' : F' 0 0 = R.zero)
    (h : ∀ j i, i + j < n → F j i = F' j i) :
    ∀ k j i, i + j ≤ n →
      psPow (psRing R) F (k + 2) j i = psPow (psRing R) F' (k + 2) j i := by
  intro k
  induction k with
  | zero =>
    intro j i hij
    show psMul (psRing R) (psPow (psRing R) F 1) F j i
        = psMul (psRing R) (psPow (psRing R) F' 1) F' j i
    rw [ps2Pow_one R F, ps2Pow_one R F']
    exact ps2Mul_coeff_congr R n hF hF' hF hF' h h j i hij
  | succ m ih =>
    intro j i hij
    show psMul (psRing R) (psPow (psRing R) F (m + 2)) F j i
        = psMul (psRing R) (psPow (psRing R) F' (m + 2)) F' j i
    exact ps2Mul_coeff_congr R n
      (ps2Pow_tcoeff_zero R F hF (m + 2) 0 0 (by omega))
      (ps2Pow_tcoeff_zero R F' hF' (m + 2) 0 0 (by omega))
      hF hF'
      (fun j' i' hij' => ih j' i' (by omega))
      h j i hij

/-- **定理 (M57-3b): 冪の係数合同（q ≥ 2 形）** — M49 の
    psPow_coeff_congr' に対応する使い勝手版。 -/
theorem ps2Pow_coeff_congr' (R : CRing) {F F' : PS2 R} (n : Nat)
    (hF : F 0 0 = R.zero) (hF' : F' 0 0 = R.zero)
    (h : ∀ j i, i + j < n → F j i = F' j i)
    (q : Nat) (hq : 2 ≤ q) :
    ∀ j i, i + j ≤ n →
      psPow (psRing R) F q j i = psPow (psRing R) F' q j i := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  subst hk
  exact ps2Pow_coeff_congr R n hF hF' h k

end IUT
