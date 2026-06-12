/-
  IUT/FormalGroup3Congr.lean — M64（三変数冪の係数合同: 結合則キャンペーン第二層）

  M57（二変数の係数合同）の三変数版:

    q ≥ 2 のとき (G^q)_{j,k,i} は G の総次数 ≤ i+k+j−1 の係数のみで決まる。

  三変数一意性（M61 のスキーマの三変数版・次層以降）の礎石。証明構造は
  M57 と同一で、三重 Cauchy 公式（M63）上の**三分処理**:
  (1) 因子1が (0,0,0) → 両辺 0、(2) 因子2が (0,0,0) → 両辺 0、
  (3) 双方総次数 ≥ 1 → 双方 ≤ n−1 で合同仮定。

  * M64-1 `ps3Pow_one` — G¹ = G
  * M64-2 `ps3Mul_coeff_congr` — **積の係数合同**（三分処理）
  * M64-3 `ps3Pow_coeff_congr` / `ps3Pow_coeff_congr'` —
    **冪の係数合同**（k 帰納、帰納因子の定数項消滅は M63 の
    総次数 truncation）

  全て選択公理不使用。
-/
import IUT.PowerSeries3

namespace IUT

/-- **M64-1**: G¹ = G。 -/
theorem ps3Pow_one (R : CRing) (G : PS3 R) :
    psPow (psRing (psRing R)) G 1 = G :=
  (psRing (psRing (psRing R))).one_mul G

/-- **定理 (M64-2): 積の係数合同（三変数）** — 定数項消滅のもと、
    総次数 < n で A = A'・B = B' なら総次数 ≤ n で A·B = A'·B'。 -/
theorem ps3Mul_coeff_congr (R : CRing) {A A' B B' : PS3 R} (n : Nat)
    (hA00 : A 0 0 0 = R.zero) (hA00' : A' 0 0 0 = R.zero)
    (hB00 : B 0 0 0 = R.zero) (hB00' : B' 0 0 0 = R.zero)
    (hA : ∀ j k i, i + k + j < n → A j k i = A' j k i)
    (hB : ∀ j k i, i + k + j < n → B j k i = B' j k i) :
    ∀ j k i, i + k + j ≤ n →
      psMul (psRing (psRing R)) A B j k i
        = psMul (psRing (psRing R)) A' B' j k i := by
  intro j k i hijk
  rw [ps3Mul_coeff R A B j k i, ps3Mul_coeff R A' B' j k i]
  exact rsum_congr R (j + 1) (fun c hc =>
    rsum_congr R (k + 1) (fun b hb =>
      rsum_congr R (i + 1) (fun a ha => by
        cases Nat.decEq (c + b + a) 0 with
        | isTrue h0 =>
          have hc0 : c = 0 := by omega
          have hb0 : b = 0 := by omega
          have ha0 : a = 0 := by omega
          subst hc0
          subst hb0
          subst ha0
          rw [hA00, hA00', R.zero_mul, R.zero_mul]
        | isFalse h0 =>
          cases Nat.decEq ((j - c) + (k - b) + (i - a)) 0 with
          | isTrue h1 =>
            have hjc : j - c = 0 := by omega
            have hkb : k - b = 0 := by omega
            have hia : i - a = 0 := by omega
            rw [hjc, hkb, hia, hB00, hB00', R.mul_zero, R.mul_zero]
          | isFalse h1 =>
            rw [hA c b a (by omega),
              hB (j - c) (k - b) (i - a) (by omega)])))

/-- **定理 (M64-3a): 冪の係数合同（q = m+2 形）**。 -/
theorem ps3Pow_coeff_congr (R : CRing) {G G' : PS3 R} (n : Nat)
    (hG : G 0 0 0 = R.zero) (hG' : G' 0 0 0 = R.zero)
    (h : ∀ j k i, i + k + j < n → G j k i = G' j k i) :
    ∀ m j k i, i + k + j ≤ n →
      psPow (psRing (psRing R)) G (m + 2) j k i
        = psPow (psRing (psRing R)) G' (m + 2) j k i := by
  intro m
  induction m with
  | zero =>
    intro j k i hijk
    show psMul (psRing (psRing R)) (psPow (psRing (psRing R)) G 1) G j k i
        = psMul (psRing (psRing R)) (psPow (psRing (psRing R)) G' 1) G'
            j k i
    rw [ps3Pow_one R G, ps3Pow_one R G']
    exact ps3Mul_coeff_congr R n hG hG' hG hG' h h j k i hijk
  | succ m ih =>
    intro j k i hijk
    show psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) G (m + 2)) G j k i
        = psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) G' (m + 2)) G' j k i
    exact ps3Mul_coeff_congr R n
      (ps3Pow_tcoeff_zero R G hG (m + 2) 0 0 0 (by omega))
      (ps3Pow_tcoeff_zero R G' hG' (m + 2) 0 0 0 (by omega))
      hG hG'
      (fun j' k' i' h' => ih j' k' i' (by omega))
      h j k i hijk

/-- **定理 (M64-3b): 冪の係数合同（q ≥ 2 形）** — 使い勝手版。 -/
theorem ps3Pow_coeff_congr' (R : CRing) {G G' : PS3 R} (n : Nat)
    (hG : G 0 0 0 = R.zero) (hG' : G' 0 0 0 = R.zero)
    (h : ∀ j k i, i + k + j < n → G j k i = G' j k i)
    (q : Nat) (hq : 2 ≤ q) :
    ∀ j k i, i + k + j ≤ n →
      psPow (psRing (psRing R)) G q j k i
        = psPow (psRing (psRing R)) G' q j k i := by
  obtain ⟨m, hm⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  subst hm
  exact ps3Pow_coeff_congr R n hG hG' h m

end IUT
