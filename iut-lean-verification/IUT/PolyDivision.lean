/-
  # M152F: 多項式割り算の存在 — モニック g による剰余構成
  （多項式 Weierstrass 準備の完結）

  塔の一段多項式 g = towerStepPoly p R piR lamR = πY + Y^p − λ は
  **Y^p モニック**（g_p = 1、台は {0, 1, p} のみ）。有限台（多項式）の
  w に対して w = q·g + r（deg r < p）を**上界 N の帰納で明示構成**する:
  頂点係数 w_{N+p} を単項式 w_{N+p}·Y^N と g の積で削り、上界を一段
  下げて帰納仮定に渡す。∃ の witness は各段で明示構成するので
  選択公理は不要。

  * M152F-1 `psMul_single_g_coeff` — 単項式 × g の係数公式:
    (c·Y^k · g)_j = c·g_{j−k}（j ≥ k）、= 0（j < k）
    （Cauchy 和は M147F-3 rsum_single_middle で中央 1 項に潰れる）
  * M152F-2 `sub_top_bounded` — 頂点消去: w が N+p+1 で有界なら
    w − (w_{N+p}·Y^N)·g は N+p で有界（頂点は g_p = 1 で打ち消し、
    上側は g の台の外）
  * M152F-3 **`poly_division_exists`（本丸）** — 割り算の存在:
    w が N+p で有界なら q（N+1 有界）と r（p 有界）が存在して
    w = q·g + r（N の帰納、商は q = q' + w_{N+p}·Y^N と積み上げ、
    psMul の左分配は rsum_add + right_distrib の項ごと計算）
  * M152F-4 `poly_weierstrass_complete` — **完結の見出し**: 存在
    （M152F-3）+ 一意性（M147F-6 poly_division_unique）を一本に束ね、
    q・r の両方の一意性まで込みで多項式 Weierstrass 準備が閉じる
  * M152F-5 `PolyDivisionData` / `polyDivisionWitness` /
    `polyDivision_exists_thm` — 総括

  意義: M147F（一意性）の対。O' = R[[Y]]/(g) の多項式部分に
  R^p 座標（次数 < p 剰余）が存在・一意の両輪で立つ。冪級数全体への
  拡張（λ-adic 収束）= M122 の塔版本体は次層。

  正直な限定: 本層が扱うのは有限台（多項式）の切片のみで、冪級数
  全体での Weierstrass 除法（π-adic / λ-adic 完備性が必要）は含まない。
  有界性の witness N は仮定として受け取る（有限台性の存在命題からの
  抽出は行わない）。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.PolyWeierstrass

namespace IUT

/-! ## M152F-1: 単項式 × g の係数公式 -/

/-- **M152F-1: 単項式 × g の係数** — (c·Y^k · g)_j は j ≥ k なら
    c·g_{j−k}、j < k なら 0。Cauchy 和のうち i = k の項だけが
    psSingle の台で生き残る（M147F-3 rsum_single_middle）。 -/
theorem psMul_single_g_coeff (p : Nat) (_hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (c : R.carrier) (k : Nat) :
    ∀ j, psMul R (psSingle R c k) (towerStepPoly p R piR lamR) j
      = if k ≤ j then R.mul c (towerStepPoly p R piR lamR (j - k))
        else R.zero := by
  intro j
  show rsum R
      (fun i => R.mul (psSingle R c k i) (towerStepPoly p R piR lamR (j - i)))
      (j + 1)
    = if k ≤ j then R.mul c (towerStepPoly p R piR lamR (j - k)) else R.zero
  cases Nat.lt_or_ge j k with
  | inl hlt =>
    -- j < k: 全項で psSingle の添字が k に届かず 0
    rw [if_neg (by omega)]
    have hz : rsum R
        (fun i => R.mul (psSingle R c k i) (towerStepPoly p R piR lamR (j - i)))
        (j + 1)
        = rsum R (fun _ => R.zero) (j + 1) :=
      rsum_congr R (j + 1) (fun i hi => by
        show R.mul (psSingle R c k i) (towerStepPoly p R piR lamR (j - i))
          = R.zero
        rw [show psSingle R c k i = R.zero from if_neg (by omega)]
        exact CRing.zero_mul R _)
    rw [hz]
    exact rsum_const_zero R (j + 1)
  | inr hge =>
    -- j ≥ k: i = k の中央 1 項だけが残る
    rw [if_pos hge]
    have hmid : rsum R
        (fun i => R.mul (psSingle R c k i) (towerStepPoly p R piR lamR (j - i)))
        (j + 1)
        = R.mul (psSingle R c k k) (towerStepPoly p R piR lamR (j - k)) :=
      rsum_single_middle R
        (fun i => R.mul (psSingle R c k i) (towerStepPoly p R piR lamR (j - i)))
        k (j + 1)
        (fun i _ hik => by
          show R.mul (psSingle R c k i) (towerStepPoly p R piR lamR (j - i))
            = R.zero
          rw [show psSingle R c k i = R.zero from if_neg hik]
          exact CRing.zero_mul R _)
        (by omega)
    rw [hmid, show psSingle R c k k = c from if_pos rfl]

/-! ## M152F-2: 頂点消去 -/

/-- **M152F-2: 頂点消去** — w が N+p+1 で有界なら、先頭項
    w_{N+p}·Y^N·g を引いた w − (w_{N+p}·Y^N)·g は N+p で有界。
    j = N+p では g_p = 1 による打ち消し、j > N+p では w も
    単項式積も消える（g の台の外）。 -/
theorem sub_top_bounded (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (w : PS R) (N : Nat)
    (hw : IsPolyBounded R w (N + p + 1)) :
    IsPolyBounded R
      (psAdd R w (psNeg R (psMul R (psSingle R (w (N + p)) N)
        (towerStepPoly p R piR lamR)))) (N + p) := by
  intro j hj
  show R.add (w j) (R.neg (psMul R (psSingle R (w (N + p)) N)
      (towerStepPoly p R piR lamR) j)) = R.zero
  rw [psMul_single_g_coeff p hp R piR lamR (w (N + p)) N j]
  cases Nat.lt_or_ge j (N + p + 1) with
  | inl hlt =>
    -- j = N + p: w_{N+p} − w_{N+p}·g_p = w_{N+p} − w_{N+p}·1 = 0
    have hje : j = N + p := by omega
    subst hje
    rw [if_pos (Nat.le_add_right N p),
      show N + p - N = p from by omega,
      towerStepPoly_coeff_top p hp R piR lamR,
      R.mul_comm (w (N + p)) R.one, R.one_mul, R.add_comm]
    exact R.neg_add (w (N + p))
  | inr hge =>
    -- j > N + p: w j = 0 かつ g_{j−N} は台 {0,1,p} の外で 0
    rw [hw j hge, if_pos (show N ≤ j from by omega),
      towerStepPoly_coeff_other p hp R piR lamR (j - N)
        (by omega) (by omega) (by omega),
      CRing.mul_zero R (w (N + p)), CRing.neg_zero R, R.zero_add]

/-! ## M152F-3: 本丸 — 割り算の存在 -/

/-- **定理 (M152F-3): 多項式割り算の存在** — w が N+p で有界なら
    q（N+1 有界）と r（p 有界）が存在して w = q·g + r。上界 N の
    帰納: N = 0 は q = 0・r = w、N+1 は頂点消去（M152F-2）で上界を
    下げ、商を q = q' + w_{N+p}·Y^N と積み上げる（witness は各段で
    明示構成、選択公理不要）。 -/
theorem poly_division_exists (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) : ∀ (N : Nat) (w : PS R),
    IsPolyBounded R w (N + p) →
    ∃ (q r : PS R), IsPolyBounded R q (N + 1) ∧ IsPolyBounded R r p ∧
      ∀ j, w j = psAdd R (psMul R q (towerStepPoly p R piR lamR)) r j := by
  intro N
  induction N with
  | zero =>
    -- w は p で有界: q = 0、r = w
    intro w hw
    refine ⟨psZero R, w, ?_, ?_, ?_⟩
    · intro i _
      rfl
    · intro i hi
      exact hw i (by omega)
    · intro j
      show w j = R.add (psMul R (psZero R) (towerStepPoly p R piR lamR) j) (w j)
      have hz : psMul R (psZero R) (towerStepPoly p R piR lamR) j = R.zero := by
        show rsum R
            (fun i => R.mul (psZero R i) (towerStepPoly p R piR lamR (j - i)))
            (j + 1) = R.zero
        have hc : rsum R
            (fun i => R.mul (psZero R i) (towerStepPoly p R piR lamR (j - i)))
            (j + 1)
            = rsum R (fun _ => R.zero) (j + 1) :=
          rsum_congr R (j + 1) (fun i _ => CRing.zero_mul R _)
        rw [hc]
        exact rsum_const_zero R (j + 1)
      rw [hz, R.zero_add]
  | succ N ih =>
    intro w hw
    -- 頂点消去で上界を一段下げる
    have hw' : IsPolyBounded R w (N + p + 1) := by
      intro i hi
      exact hw i (by omega)
    have hsub := sub_top_bounded p hp R piR lamR w N hw'
    obtain ⟨q', r', hq', hr', heq'⟩ := ih _ hsub
    refine ⟨psAdd R q' (psSingle R (w (N + p)) N), r', ?_, hr', ?_⟩
    · -- 商の有界性: q' は N+1 有界、単項式は N 番目のみ
      intro i hi
      show R.add (q' i) (psSingle R (w (N + p)) N i) = R.zero
      rw [hq' i (by omega),
        show psSingle R (w (N + p)) N i = R.zero from if_neg (by omega),
        R.zero_add]
    · -- 等式: w = w' + (single·g) = (q'·g + r') + single·g = (q'+single)·g + r'
      intro j
      show w j = R.add
        (psMul R (psAdd R q' (psSingle R (w (N + p)) N))
          (towerStepPoly p R piR lamR) j) (r' j)
      -- 帰納段の等式を係数の形で受ける
      have h1 : R.add (w j)
          (R.neg (psMul R (psSingle R (w (N + p)) N)
            (towerStepPoly p R piR lamR) j))
          = R.add (psMul R q' (towerStepPoly p R piR lamR) j) (r' j) := heq' j
      -- psMul の左分配（係数ごと: rsum_add + right_distrib）
      have hdist : psMul R (psAdd R q' (psSingle R (w (N + p)) N))
          (towerStepPoly p R piR lamR) j
          = R.add (psMul R q' (towerStepPoly p R piR lamR) j)
            (psMul R (psSingle R (w (N + p)) N)
              (towerStepPoly p R piR lamR) j) := by
        show rsum R (fun i => R.mul
            (R.add (q' i) (psSingle R (w (N + p)) N i))
            (towerStepPoly p R piR lamR (j - i))) (j + 1)
          = R.add
            (rsum R (fun i => R.mul (q' i)
              (towerStepPoly p R piR lamR (j - i))) (j + 1))
            (rsum R (fun i => R.mul (psSingle R (w (N + p)) N i)
              (towerStepPoly p R piR lamR (j - i))) (j + 1))
        rw [← rsum_add R _ _ (j + 1)]
        exact rsum_congr R (j + 1) (fun i _ =>
          CRing.right_distrib R (q' i) (psSingle R (w (N + p)) N i)
            (towerStepPoly p R piR lamR (j - i)))
      calc w j
          = R.add (R.add (w j)
              (R.neg (psMul R (psSingle R (w (N + p)) N)
                (towerStepPoly p R piR lamR) j)))
              (psMul R (psSingle R (w (N + p)) N)
                (towerStepPoly p R piR lamR) j) := by
            rw [R.add_assoc, R.neg_add, CRing.add_zero R]
        _ = R.add (R.add (psMul R q' (towerStepPoly p R piR lamR) j) (r' j))
              (psMul R (psSingle R (w (N + p)) N)
                (towerStepPoly p R piR lamR) j) := by
            rw [h1]
        _ = R.add (R.add (psMul R q' (towerStepPoly p R piR lamR) j)
              (psMul R (psSingle R (w (N + p)) N)
                (towerStepPoly p R piR lamR) j)) (r' j) := by
            rw [R.add_assoc, R.add_comm (r' j)
              (psMul R (psSingle R (w (N + p)) N)
                (towerStepPoly p R piR lamR) j), ← R.add_assoc]
        _ = R.add (psMul R (psAdd R q' (psSingle R (w (N + p)) N))
              (towerStepPoly p R piR lamR) j) (r' j) := by
            rw [hdist]

/-! ## M152F-4: 完結の見出し — 存在 + 一意性 -/

/-- **見出し (M152F-4): 多項式 Weierstrass 準備の完結** — 存在
    （M152F-3）と一意性（M147F-6 poly_division_unique）を一本化:
    w が N+p で有界なら q（N+1 有界）・r（p 有界）が存在して
    w = q·g + r、しかも同じ分解を与える任意の (q₂, r₂) は q・r と
    係数ごとに一致する。O' = R[[Y]]/(g) の多項式部分の R^p 座標
    （次数 < p 剰余）が存在・一意の両輪で立つ。 -/
theorem poly_weierstrass_complete (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (N : Nat) (w : PS R)
    (hw : IsPolyBounded R w (N + p)) :
    ∃ (q r : PS R), IsPolyBounded R q (N + 1) ∧ IsPolyBounded R r p ∧
      (∀ j, w j = psAdd R (psMul R q (towerStepPoly p R piR lamR)) r j) ∧
      (∀ (q₂ r₂ : PS R) (Nq₂ : Nat), IsPolyBounded R q₂ Nq₂ →
        IsPolyBounded R r₂ p →
        (∀ j, w j = psAdd R (psMul R q₂ (towerStepPoly p R piR lamR)) r₂ j) →
        (∀ i, q i = q₂ i) ∧ (∀ i, r i = r₂ i)) := by
  obtain ⟨q, r, hq, hr, heq⟩ := poly_division_exists p hp R piR lamR N w hw
  refine ⟨q, r, hq, hr, heq, ?_⟩
  intro q₂ r₂ Nq₂ hq₂ hr₂ heq₂
  exact poly_division_unique p hp R piR lamR q q₂ r r₂ (N + 1) Nq₂
    hq hq₂ hr hr₂ (fun j => (heq j).symm.trans (heq₂ j))

/-! ## M152F-5: 総括 -/

/-- **M152F-5: 多項式割り算データ** — 存在（existence）と
    存在 + 一意性の完結形（complete）を任意の可換環で束ねる。 -/
structure PolyDivisionData (p : Nat) (hp : 2 ≤ p) where
  existence : ∀ (R : CRing) (piR lamR : R.carrier) (N : Nat) (w : PS R),
    IsPolyBounded R w (N + p) →
    ∃ (q r : PS R), IsPolyBounded R q (N + 1) ∧ IsPolyBounded R r p ∧
      ∀ j, w j = psAdd R (psMul R q (towerStepPoly p R piR lamR)) r j
  complete : ∀ (R : CRing) (piR lamR : R.carrier) (N : Nat) (w : PS R),
    IsPolyBounded R w (N + p) →
    ∃ (q r : PS R), IsPolyBounded R q (N + 1) ∧ IsPolyBounded R r p ∧
      (∀ j, w j = psAdd R (psMul R q (towerStepPoly p R piR lamR)) r j) ∧
      (∀ (q₂ r₂ : PS R) (Nq₂ : Nat), IsPolyBounded R q₂ Nq₂ →
        IsPolyBounded R r₂ p →
        (∀ j, w j = psAdd R (psMul R q₂ (towerStepPoly p R piR lamR)) r₂ j) →
        (∀ i, q i = q₂ i) ∧ (∀ i, r i = r₂ i))

/-- 証人: M152F-3・M152F-4 をそのまま束ねる。 -/
def polyDivisionWitness (p : Nat) (hp : 2 ≤ p) : PolyDivisionData p hp where
  existence := fun R piR lamR N w hw =>
    poly_division_exists p hp R piR lamR N w hw
  complete := fun R piR lamR N w hw =>
    poly_weierstrass_complete p hp R piR lamR N w hw

/-- **見出し (M152F): 多項式割り算データの存在**。 -/
theorem polyDivision_exists_thm (p : Nat) (hp : 2 ≤ p) :
    Nonempty (PolyDivisionData p hp) :=
  ⟨polyDivisionWitness p hp⟩

end IUT
