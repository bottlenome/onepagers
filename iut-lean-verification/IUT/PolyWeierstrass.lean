/-
  # M147F: 多項式 Weierstrass 一意性 — 塔一段多項式のモニック正則性
  （Oₙ 座標系の第一切片）

  塔の一段多項式 g = towerStepPoly p R piR lamR = πY + Y^p − λ は
  **Y^p がモニック**（g_p = 1、台は {0, 1, p} のみ）。これだけで
  「有限台（多項式）レベルでは g との積は次数を落とせない」=
  **g の多項式正則性**と、**次数 < p の剰余の一意性**が任意の可換環 R で
  選択公理なしに閉じる。

  * M147F-1 `IsPolyBounded` — 有限台の上界述語
  * M147F-2 `towerStepPoly_coeff_top` / `towerStepPoly_coeff_other` —
    係数確定: g_p = 1・g_j = 0 (j ∉ {0, 1, p})
    （M111-1 towerStepPoly_coeff_zero・M119-2 _coeff_one の補完）
  * M147F-3 `rsum_single_middle` — 中央 1 項だけ残る有限和
    （M144-1 rsum_tail_single の中央版）
  * M147F-4 `psMul_g_top_coeff` — 頂点係数の抽出:
    w が M+1 で有界なら (w·g)_{M+p} = w_M（モニック性の核）
  * M147F-5 **`poly_mul_g_bounded_zero`（本丸）** — 有界な w に対し
    (w·g)_j = 0 (∀ j ≥ p) ⟹ w = 0（g の多項式正則性、
    上界 N の下向き帰納）
  * M147F-6 `poly_division_unique` — 次数 < p 剰余の一意性:
    q·g + r = q'·g + r'（q, q' 有界・r, r' は p で有界）⟹
    q = q' かつ r = r'
  * M147F-7 `PolyWeierstrassData` / `polyWeierstrass_exists` — 総括

  意義: M122 の座標忠実性（π-adic 収束）の塔版への入口。
  g = πY + Y^p − λ のモニック性だけで、多項式部分の座標
  （次数 < p 剰余）の一意性が任意の可換環で閉じる。存在
  （割り算アルゴリズム）と冪級数全体への拡張（λ-adic 収束）は次層。

  正直な限定: 本層が扱うのは有限台（多項式）の切片のみで、
  冪級数全体での Weierstrass 除法（π-adic / λ-adic 完備性が必要）は
  含まない。また「有界性の witness N」は仮定として受け取る
  （有限台性の存在命題からの抽出は行わない）。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.LambdaPropagation

namespace IUT

/-! ## M147F-1: 有限台の上界 -/

/-- **M147F-1: 多項式的有界性** — 係数列 f が N 以上で消える。 -/
def IsPolyBounded (R : CRing) (f : PS R) (N : Nat) : Prop :=
  ∀ i, N ≤ i → f i = R.zero

/-! ## M147F-2: 一段多項式の係数確定 -/

/-- **M147F-2a: 頂点係数はモニック** — (πY + Y^p − λ)_p = 1
    （p ≥ 2 で Y の項も定数項も p 次に寄与しない）。 -/
theorem towerStepPoly_coeff_top (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) :
    towerStepPoly p R piR lamR p = R.one := by
  show R.add (R.add (psSingle R piR 1 p) (psMono R p p))
      (R.neg (psC R lamR p)) = R.one
  rw [show psSingle R piR 1 p = R.zero from if_neg (by omega),
    show psMono R p p = R.one from if_pos rfl,
    show psC R lamR p = R.zero from if_neg (by omega),
    CRing.neg_zero R, CRing.add_zero R, R.zero_add]

/-- **M147F-2b: 台の外は零** — j ∉ {0, 1, p} なら
    (πY + Y^p − λ)_j = 0（台は {0, 1, p} のみ）。 -/
theorem towerStepPoly_coeff_other (p : Nat) (_hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ p →
    towerStepPoly p R piR lamR j = R.zero := by
  intro j h0 h1 hpj
  show R.add (R.add (psSingle R piR 1 j) (psMono R p j))
      (R.neg (psC R lamR j)) = R.zero
  rw [show psSingle R piR 1 j = R.zero from if_neg h1,
    show psMono R p j = R.zero from if_neg hpj,
    show psC R lamR j = R.zero from if_neg h0,
    CRing.neg_zero R, R.zero_add, R.zero_add]

/-! ## M147F-3: 中央 1 項だけ残る有限和 -/

/-- **M147F-3: 中央単項和** — m 番目以外が消える有限和は f m のみ
    （M144-1 rsum_tail_single の中央版、n の帰納）。 -/
theorem rsum_single_middle (R : CRing) (f : Nat → R.carrier) (m : Nat) :
    ∀ n, (∀ k, k < n → k ≠ m → f k = R.zero) → m < n →
    rsum R f n = f m := by
  intro n
  induction n with
  | zero =>
    intro _ hm
    exact absurd hm (Nat.not_lt_zero m)
  | succ n ih =>
    intro h hm
    show R.add (rsum R f n) (f n) = f m
    cases Nat.lt_or_ge m n with
    | inl hlt =>
      rw [h n (by omega) (by omega), CRing.add_zero R]
      exact ih (fun k hk hkm => h k (by omega) hkm) hlt
    | inr hge =>
      have hmn : n = m := by omega
      subst hmn
      have hz : rsum R f n = rsum R (fun _ => R.zero) n :=
        rsum_congr R n (fun k hk => h k (by omega) (by omega))
      rw [hz, rsum_const_zero R n, R.zero_add]

/-! ## M147F-4: 頂点係数の抽出 -/

/-- **M147F-4: モニック性の核** — w が M+1 で有界なら
    (w·g)_{M+p} = w_M。Cauchy 和のうち i > M は w の有界性で、
    i < M は g の添字が p+1 以上になり台の外で消え、i = M の項
    w_M · g_p = w_M · 1 だけが残る。 -/
theorem psMul_g_top_coeff (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (w : PS R) (M : Nat)
    (hw : ∀ i, M + 1 ≤ i → w i = R.zero) :
    psMul R w (towerStepPoly p R piR lamR) (M + p) = w M := by
  show rsum R (fun i => R.mul (w i) (towerStepPoly p R piR lamR (M + p - i)))
    (M + p + 1) = w M
  have hmid : rsum R
      (fun i => R.mul (w i) (towerStepPoly p R piR lamR (M + p - i)))
      (M + p + 1)
      = R.mul (w M) (towerStepPoly p R piR lamR (M + p - M)) :=
    rsum_single_middle R
      (fun i => R.mul (w i) (towerStepPoly p R piR lamR (M + p - i)))
      M (M + p + 1)
      (fun k hk hkm => by
        show R.mul (w k) (towerStepPoly p R piR lamR (M + p - k)) = R.zero
        cases Nat.lt_or_ge k M with
        | inl hlt =>
          rw [towerStepPoly_coeff_other p hp R piR lamR (M + p - k)
            (by omega) (by omega) (by omega)]
          exact CRing.mul_zero R (w k)
        | inr hge =>
          rw [hw k (by omega)]
          exact CRing.zero_mul R (towerStepPoly p R piR lamR (M + p - k)))
      (by omega)
  rw [hmid, show M + p - M = p from by omega,
    towerStepPoly_coeff_top p hp R piR lamR,
    R.mul_comm (w M) R.one, R.one_mul]

/-! ## M147F-5: 本丸 — g の多項式正則性 -/

/-- **定理 (M147F-5): g の多項式正則性** — 有界な w に対し、積 w·g の
    次数 ≥ p 部分が全部 0 なら w = 0。上界 N の下向き帰納:
    最高次係数 w_{N−1} = (w·g)_{N−1+p} = 0 から上界を一つ下げる。 -/
theorem poly_mul_g_bounded_zero (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (w : PS R) (N : Nat)
    (hw : IsPolyBounded R w N)
    (hlow : ∀ j, p ≤ j → psMul R w (towerStepPoly p R piR lamR) j = R.zero) :
    ∀ i, w i = R.zero := by
  revert hw
  induction N with
  | zero =>
    intro hw i
    exact hw i (Nat.zero_le i)
  | succ M ih =>
    intro hw
    have hM : w M = R.zero := by
      have h1 : psMul R w (towerStepPoly p R piR lamR) (M + p) = w M :=
        psMul_g_top_coeff p hp R piR lamR w M (fun i hi => hw i hi)
      rw [← h1]
      exact hlow (M + p) (by omega)
    apply ih
    intro i hi
    cases Nat.lt_or_ge i (M + 1) with
    | inl hlt =>
      rw [show i = M from by omega]
      exact hM
    | inr hge => exact hw i hge

/-! ## M147F-6: 次数 < p 剰余の一意性 -/

/-- **定理 (M147F-6): 剰余の一意性** — q·g + r = q'·g + r'
    （q, q' 有界・r, r' は次数 < p）なら q = q' かつ r = r'。
    差 w = q − q' に M147F-5 を適用: (w·g)_j (j ≥ p) は r' − r の
    係数で、r, r' が p で有界だから 0。 -/
theorem poly_division_unique (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (q q' r r' : PS R) (Nq Nq' : Nat)
    (hq : IsPolyBounded R q Nq) (hq' : IsPolyBounded R q' Nq')
    (hr : IsPolyBounded R r p) (hr' : IsPolyBounded R r' p)
    (heq : ∀ j, psAdd R (psMul R q (towerStepPoly p R piR lamR)) r j
      = psAdd R (psMul R q' (towerStepPoly p R piR lamR)) r' j) :
    (∀ i, q i = q' i) ∧ (∀ i, r i = r' i) := by
  -- w = q − q' は Nq + Nq' で有界
  have hwb : IsPolyBounded R (psAdd R q (psNeg R q')) (Nq + Nq') := by
    intro i hi
    show R.add (q i) (R.neg (q' i)) = R.zero
    rw [hq i (by omega), hq' i (by omega), CRing.neg_zero R, R.zero_add]
  -- (w·g)_j + (q'·g)_j = (q·g)_j（項ごとの右分配）
  have hsum : ∀ j,
      R.add (psMul R (psAdd R q (psNeg R q')) (towerStepPoly p R piR lamR) j)
        (psMul R q' (towerStepPoly p R piR lamR) j)
      = psMul R q (towerStepPoly p R piR lamR) j := by
    intro j
    show R.add (rsum R (fun k => R.mul (psAdd R q (psNeg R q') k)
        (towerStepPoly p R piR lamR (j - k))) (j + 1))
      (rsum R (fun k => R.mul (q' k)
        (towerStepPoly p R piR lamR (j - k))) (j + 1))
      = rsum R (fun k => R.mul (q k)
        (towerStepPoly p R piR lamR (j - k))) (j + 1)
    rw [← rsum_add R _ _ (j + 1)]
    exact rsum_congr R (j + 1) (fun k _ => by
      show R.add
          (R.mul (psAdd R q (psNeg R q') k) (towerStepPoly p R piR lamR (j - k)))
          (R.mul (q' k) (towerStepPoly p R piR lamR (j - k)))
        = R.mul (q k) (towerStepPoly p R piR lamR (j - k))
      rw [← CRing.right_distrib R]
      have hkey : R.add (psAdd R q (psNeg R q') k) (q' k) = q k := by
        show R.add (R.add (q k) (R.neg (q' k))) (q' k) = q k
        rw [R.add_assoc, R.neg_add, CRing.add_zero R]
      rw [hkey])
  -- j ≥ p では (q·g)_j = (q'·g)_j（r, r' が消えるので）
  have hwlow : ∀ j, p ≤ j →
      psMul R (psAdd R q (psNeg R q')) (towerStepPoly p R piR lamR) j
        = R.zero := by
    intro j hj
    have hqg : psMul R q (towerStepPoly p R piR lamR) j
        = psMul R q' (towerStepPoly p R piR lamR) j := by
      have h2 : R.add (psMul R q (towerStepPoly p R piR lamR) j) (r j)
          = R.add (psMul R q' (towerStepPoly p R piR lamR) j) (r' j) := heq j
      rw [hr j hj, hr' j hj, CRing.add_zero R, CRing.add_zero R] at h2
      exact h2
    have h3 : R.add (psMul R q' (towerStepPoly p R piR lamR) j)
        (psMul R (psAdd R q (psNeg R q')) (towerStepPoly p R piR lamR) j)
        = R.add (psMul R q' (towerStepPoly p R piR lamR) j) R.zero := by
      rw [CRing.add_zero R,
        R.add_comm (psMul R q' (towerStepPoly p R piR lamR) j)
          (psMul R (psAdd R q (psNeg R q')) (towerStepPoly p R piR lamR) j),
        hsum j]
      exact hqg
    exact CRing.add_left_cancel R h3
  -- 本丸を適用して w = 0、すなわち q = q'
  have hw0 : ∀ i, psAdd R q (psNeg R q') i = R.zero :=
    poly_mul_g_bounded_zero p hp R piR lamR (psAdd R q (psNeg R q'))
      (Nq + Nq') hwb hwlow
  have hqq : ∀ i, q i = q' i := by
    intro i
    have h' : R.add (q i) (R.neg (q' i)) = R.zero := hw0 i
    exact CRing.eq_of_sub_eq_zero R h'
  -- q = q' から q·g = q'·g、加法簡約で r = r'
  have hmul : ∀ j, psMul R q (towerStepPoly p R piR lamR) j
      = psMul R q' (towerStepPoly p R piR lamR) j := by
    intro j
    show rsum R (fun k => R.mul (q k) (towerStepPoly p R piR lamR (j - k))) (j + 1)
      = rsum R (fun k => R.mul (q' k) (towerStepPoly p R piR lamR (j - k))) (j + 1)
    exact rsum_congr R (j + 1) (fun k _ => by rw [hqq k])
  refine ⟨hqq, ?_⟩
  intro j
  have h2 : R.add (psMul R q (towerStepPoly p R piR lamR) j) (r j)
      = R.add (psMul R q' (towerStepPoly p R piR lamR) j) (r' j) := heq j
  rw [hmul j] at h2
  exact CRing.add_left_cancel R h2

/-! ## M147F-7: 総括 -/

/-- **M147F-7: 多項式 Weierstrass データ** — g のモニック正則性
    （bounded_zero）と次数 < p 剰余の一意性（uniqueness）を
    任意の可換環で束ねる。 -/
structure PolyWeierstrassData (p : Nat) (hp : 2 ≤ p) where
  bounded_zero : ∀ (R : CRing) (piR lamR : R.carrier) (w : PS R) (N : Nat),
    IsPolyBounded R w N →
    (∀ j, p ≤ j → psMul R w (towerStepPoly p R piR lamR) j = R.zero) →
    ∀ i, w i = R.zero
  uniqueness : ∀ (R : CRing) (piR lamR : R.carrier)
    (q q' r r' : PS R) (Nq Nq' : Nat),
    IsPolyBounded R q Nq → IsPolyBounded R q' Nq' →
    IsPolyBounded R r p → IsPolyBounded R r' p →
    (∀ j, psAdd R (psMul R q (towerStepPoly p R piR lamR)) r j
      = psAdd R (psMul R q' (towerStepPoly p R piR lamR)) r' j) →
    (∀ i, q i = q' i) ∧ (∀ i, r i = r' i)

/-- 証人: M147F-5・M147F-6 をそのまま束ねる。 -/
def polyWeierstrassWitness (p : Nat) (hp : 2 ≤ p) :
    PolyWeierstrassData p hp where
  bounded_zero := fun R piR lamR w N hw hlow =>
    poly_mul_g_bounded_zero p hp R piR lamR w N hw hlow
  uniqueness := fun R piR lamR q q' r r' Nq Nq' hq hq' hr hr' heq =>
    poly_division_unique p hp R piR lamR q q' r r' Nq Nq' hq hq' hr hr' heq

/-- **見出し (M147F): 多項式 Weierstrass データの存在**。 -/
theorem polyWeierstrass_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (PolyWeierstrassData p hp) :=
  ⟨polyWeierstrassWitness p hp⟩

end IUT
