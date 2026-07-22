/-
# M155: (λ,π)-adic 分離性への局在 — 塔座標の一般忠実性の正確な条件（柱B 本線）

M147F/M152F は塔一段商 O' = R[[Y]]/(g)（g = πY + Y^p − λ）の多項式部分に
R^p 座標が立つことを「**多項式 witness**」の範囲で閉じた。本層は
**witness が任意の冪級数**でも座標が単射である条件を正確に切り出す:

  h·g が多項式（次数 < p）なら、係数の再帰
    w_j = λ·w_{j+p} − π·w_{j+p−1}
  により w の全係数は (λ,π) 冪イデアルの**無限深度**に沈む（深度補題 —
  分離性なしで構成的に成立）。従って **(λ,π)-adic 分離性**
  （∩ₖ (λ,π)^k = 0）の下で w = 0、すなわち**次数 < p 剰余の一般忠実性**。

  * M155-1 `IsIn2Pow` — (λ,π)^k 所属の ∃-述語と neg 閉性・
    生成元一致時の主冪 collapse
  * M155-2 `psMul_g_coeff_three` — 3 点台の係数公式
    (w·g)_{j+p} = (w_j·1 + w_{j+p−1}·π) + w_{j+p}·(−λ)
  * M155-3 **`depth_of_bounded_image`（深度補題）** — w·g の次数 ≥ p
    部分が消えるなら ∀k j, w_j ∈ (λ,π)^k
  * M155-4 `IsSeparated2` / **`sep_poly_faithful`（局在の本丸）** —
    分離性 ⟹ 任意 witness に対する次数 < p 剰余の単射性
  * M155-5 **`zp_separated`** — ℤ_p は (p,p)-adic 分離的（レベル別
    簿記 val_p_mul の反復で x = π^k c の第 k 成分が消える）
  * M155-6 `zp_step_faithful` — 台での instance:
    ℤ_p[[Y]]/(pY + Y^p − p) の次数 < p 剰余は任意 witness で一意
  * M155-7 `TowerSeparationData` — 総括

正直な限定: 実際の塔レベル（R = eisRing・towerLevel）の分離性は
各レベルの座標理論（M122 の塔版）を要し次層 — 本層はその成立条件を
「分離性」という単一のインターフェースに**正確に局在**させ、塔の台
ℤ_p でインターフェースが実際に inhabit されることを実証する。

全て選択公理不使用。
-/
import IUT.PolyWeierstrass

namespace IUT

/-! ## M155-1: (λ,π) 冪イデアルの ∃-述語 -/

/-- **M155-1a: (λ,π)^k 所属** — k 重の 2 項分解の入れ子。 -/
def IsIn2Pow (R : CRing) (lam piR : R.carrier) : Nat → R.carrier → Prop
  | 0, _ => True
  | k + 1, x => ∃ a b, IsIn2Pow R lam piR k a ∧ IsIn2Pow R lam piR k b ∧
      x = R.add (R.mul lam a) (R.mul piR b)

/-- **M155-1b: neg 閉性**。 -/
theorem isIn2Pow_neg (R : CRing) (lam piR : R.carrier) : ∀ (k : Nat)
    (x : R.carrier), IsIn2Pow R lam piR k x →
    IsIn2Pow R lam piR k (R.neg x) := by
  intro k
  induction k with
  | zero => intro x _; exact trivial
  | succ k ih =>
    intro x hx
    obtain ⟨a, b, ha, hb, hx⟩ := hx
    refine ⟨R.neg a, R.neg b, ih a ha, ih b hb, ?_⟩
    rw [hx, CRing.neg_add_dist R, CRing.mul_neg R lam a,
      CRing.mul_neg R piR b]

/-- **M155-1c: 生成元一致の collapse** — λ = π のとき
    (π,π)^k 所属は主冪 π^k の倍元。 -/
theorem isIn2Pow_collapse (R : CRing) (piR : R.carrier) : ∀ (k : Nat)
    (x : R.carrier), IsIn2Pow R piR piR k x →
    ∃ c, x = R.mul (rpow R piR k) c := by
  intro k
  induction k with
  | zero =>
    intro x _
    refine ⟨x, ?_⟩
    rw [show rpow R piR 0 = R.one from rfl, R.one_mul]
  | succ k ih =>
    intro x hx
    obtain ⟨a, b, ha, hb, hx⟩ := hx
    obtain ⟨ca, hca⟩ := ih a ha
    obtain ⟨cb, hcb⟩ := ih b hb
    refine ⟨R.add ca cb, ?_⟩
    rw [hx, hca, hcb, ← R.left_distrib piR,
      ← R.left_distrib (rpow R piR k) ca cb]
    rw [show rpow R piR (k + 1) = R.mul (rpow R piR k) piR from rfl,
      ← R.mul_assoc piR (rpow R piR k) (R.add ca cb),
      R.mul_comm piR (rpow R piR k), R.mul_assoc]

/-! ## M155-2: 3 点台の係数公式 -/

/-- rsum の一段剥がし（記法固定用）。 -/
theorem rsum_peel (R : CRing) (f : Nat → R.carrier) (m : Nat) :
    rsum R f (m + 1) = R.add (rsum R f m) (f m) := rfl

/-- **定理 (M155-2): 3 点台の係数公式** — g の台 {0,1,p} に対応して
    (w·g)_{j+p} = (w_j·1 + w_{j+p−1}·π) + w_{j+p}·(−λ)。 -/
theorem psMul_g_coeff_three (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (w : PS R) (j : Nat) :
    psMul R w (towerStepPoly p R piR lamR) (j + p)
      = R.add (R.add (R.mul (w j) R.one) (R.mul (w (j + p - 1)) piR))
          (R.mul (w (j + p)) (R.neg lamR)) := by
  show rsum R
      (fun i => R.mul (w i) (towerStepPoly p R piR lamR (j + p - i)))
      (j + p + 1)
    = R.add (R.add (R.mul (w j) R.one) (R.mul (w (j + p - 1)) piR))
        (R.mul (w (j + p)) (R.neg lamR))
  rw [rsum_peel R _ (j + p)]
  have e2 : rsum R
      (fun i => R.mul (w i) (towerStepPoly p R piR lamR (j + p - i)))
      (j + p)
      = R.add (rsum R
          (fun i => R.mul (w i) (towerStepPoly p R piR lamR (j + p - i)))
          (j + p - 1))
        (R.mul (w (j + p - 1))
          (towerStepPoly p R piR lamR (j + p - (j + p - 1)))) := by
    rw [show j + p = j + p - 1 + 1 from by omega]
    rfl
  rw [e2,
    rsum_single_middle R
      (fun i => R.mul (w i) (towerStepPoly p R piR lamR (j + p - i)))
      j (j + p - 1)
      (fun k hk hkj => by
        show R.mul (w k) (towerStepPoly p R piR lamR (j + p - k)) = R.zero
        rw [towerStepPoly_coeff_other p hp R piR lamR (j + p - k)
            (by omega) (by omega) (by omega),
          R.mul_comm (w k) R.zero, CRing.zero_mul R])
      (by omega),
    show j + p - j = p from by omega,
    towerStepPoly_coeff_top p hp R piR lamR,
    show j + p - (j + p - 1) = 1 from by omega,
    towerStepPoly_coeff_one p hp R piR lamR,
    show j + p - (j + p) = 0 from by omega,
    towerStepPoly_coeff_zero p (by omega) R piR lamR]

/-! ## M155-3: 深度補題 -/

/-- **定理 (M155-3): 深度補題（分離性なしで成立）** — w·g の次数 ≥ p
    部分が全て 0 なら、係数再帰 w_j = λ·w_{j+p} − π·w_{j+p−1} により
    w の全係数は (λ,π)^k の全深度に沈む。 -/
theorem depth_of_bounded_image (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (w : PS R)
    (hlow : ∀ i, p ≤ i →
      psMul R w (towerStepPoly p R piR lamR) i = R.zero) :
    ∀ k j, IsIn2Pow R lamR piR k (w j) := by
  intro k
  induction k with
  | zero => intro j; exact trivial
  | succ k ih =>
    intro j
    -- 係数再帰の抽出
    have E : R.add (R.add (R.mul (w j) R.one) (R.mul (w (j + p - 1)) piR))
        (R.mul (w (j + p)) (R.neg lamR)) = R.zero := by
      rw [← psMul_g_coeff_three p hp R piR lamR w j]
      exact hlow (j + p) (by omega)
    have hsolve : w j = R.add (R.mul lamR (w (j + p)))
        (R.mul piR (R.neg (w (j + p - 1)))) := by
      apply CRing.eq_of_sub_eq_zero R
      -- w_j − T = E の並べ替え
      rw [CRing.neg_add_dist R, CRing.mul_neg R piR (w (j + p - 1)),
        CRing.neg_neg R]
      -- 目標: w_j + (−(λ·w_{j+p}) + π·w_{j+p−1}) = 0
      rw [R.mul_comm (w j) R.one, R.one_mul] at E
      rw [R.mul_comm (w (j + p - 1)) piR] at E
      have e3 : R.mul (w (j + p)) (R.neg lamR)
          = R.neg (R.mul lamR (w (j + p))) := by
        rw [CRing.mul_neg R (w (j + p)) lamR,
          R.mul_comm (w (j + p)) lamR]
      rw [e3] at E
      -- E : (w_j + π·w') + (−(λ·w'')) = 0 → 並べ替え
      rw [R.add_assoc (w j) (R.mul piR (w (j + p - 1)))
          (R.neg (R.mul lamR (w (j + p)))),
        R.add_comm (R.mul piR (w (j + p - 1)))
          (R.neg (R.mul lamR (w (j + p))))] at E
      exact E
    exact ⟨w (j + p), R.neg (w (j + p - 1)), ih (j + p),
      isIn2Pow_neg R lamR piR k _ (ih (j + p - 1)), hsolve⟩

/-! ## M155-4: 分離性への局在（本丸） -/

/-- **M155-4a: (λ,π)-adic 分離性** — ∩ₖ (λ,π)^k = 0。 -/
def IsSeparated2 (R : CRing) (lam piR : R.carrier) : Prop :=
  ∀ x, (∀ k, IsIn2Pow R lam piR k x) → x = R.zero

/-- **定理 (M155-4b): 局在の本丸** — 分離性の下で、次数 < p 剰余は
    **任意の冪級数 witness** に対して単射（M147F の多項式 witness
    限定を撤廃する正確な条件）。 -/
theorem sep_poly_faithful (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (hsep : IsSeparated2 R lamR piR)
    {r r' : PS R} (hr : IsPolyBounded R r p) (hr' : IsPolyBounded R r' p)
    (h : Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR)) r
       = Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR)) r') :
    ∀ i, r i = r' i := by
  obtain ⟨w, hw⟩ :=
    quot_exact_ideal (psRing R) (towerStepPoly p R piR lamR) h
  have hco : ∀ i, R.add (r i) (R.neg (r' i))
      = psMul R w (towerStepPoly p R piR lamR) i := fun i => congrFun hw i
  have hlow : ∀ i, p ≤ i →
      psMul R w (towerStepPoly p R piR lamR) i = R.zero := by
    intro i hi
    rw [← hco i, hr i hi, hr' i hi, CRing.neg_zero R, CRing.add_zero R]
  have hwz : ∀ j, w j = R.zero := fun j =>
    hsep (w j) (fun k => depth_of_bounded_image p hp R piR lamR w hlow k j)
  intro i
  apply CRing.eq_of_sub_eq_zero R
  rw [hco i]
  show rsum R
      (fun k => R.mul (w k) (towerStepPoly p R piR lamR (i - k))) (i + 1)
    = R.zero
  rw [rsum_congr R (i + 1) (fun k _ => by
      show R.mul (w k) (towerStepPoly p R piR lamR (i - k)) = R.zero
      rw [hwz k, CRing.zero_mul R]),
    rsum_const_zero R (i + 1)]

/-! ## M155-5: ℤ_p の分離性（台の instance） -/

/-- π^k 倍のレベル別簿記（val_p_mul の反復）。 -/
theorem zp_pow_mul_val_rep (p : Nat) : ∀ (k : Nat) (y : (Zp p).carrier)
    (n : Nat) (c : Int), Quot.mk (modCong (p ^ n)).rel c = y.val n →
    ((zpRing p).mul (rpow (zpRing p) (zpPi p) k) y).val n
      = Quot.mk (modCong (p ^ n)).rel (((p ^ k : Nat) : Int) * c) := by
  intro k
  induction k with
  | zero =>
    intro y n c hc
    rw [show rpow (zpRing p) (zpPi p) 0 = (zpRing p).one from rfl,
      (zpRing p).one_mul y, ← hc]
    apply congrArg
    have e : ((p ^ 0 : Nat) : Int) = 1 := by
      rw [Nat.pow_zero]
      rfl
    rw [e, Int.one_mul]
  | succ k ih =>
    intro y n c hc
    -- π^{k+1}·y = π^k·(π·y)（結合 + 可換）
    have e1 : (zpRing p).mul (rpow (zpRing p) (zpPi p) (k + 1)) y
        = (zpRing p).mul (rpow (zpRing p) (zpPi p) k)
            ((zpRing p).mul (zpPi p) y) := by
      rw [show rpow (zpRing p) (zpPi p) (k + 1)
          = (zpRing p).mul (rpow (zpRing p) (zpPi p) k) (zpPi p) from rfl,
        (zpRing p).mul_assoc]
    rw [e1]
    -- (π·y).val n = mk (p·c)
    have hstep : Quot.mk (modCong (p ^ n)).rel (((p : Nat) : Int) * c)
        = ((zpRing p).mul (zpPi p) y).val n :=
      (val_p_mul p y n c hc).symm
    rw [ih ((zpRing p).mul (zpPi p) y) n (((p : Nat) : Int) * c) hstep]
    apply congrArg
    rw [← Int.mul_assoc]
    apply congrArg (· * c)
    rw [show p ^ (k + 1) = p ^ k * p from Nat.pow_succ p k,
      Int.natCast_mul]

/-- **定理 (M155-5): ℤ_p の (p,p)-adic 分離性** — 全深度に沈む元は
    各レベル k で π^k 倍 = 第 k 成分が 0、よって 0。 -/
theorem zp_separated (p : Nat) (_hp : 2 ≤ p) :
    IsSeparated2 (zpRing p) (zpPi p) (zpPi p) := by
  intro x hall
  apply Subtype.ext
  funext n
  show x.val n = Quot.mk (modCong (p ^ n)).rel 0
  obtain ⟨c, hc⟩ := isIn2Pow_collapse (zpRing p) (zpPi p) n x (hall n)
  obtain ⟨crep, hcrep⟩ := Quot.exists_rep (c.val n)
  have hval := zp_pow_mul_val_rep p n c n crep hcrep
  rw [hc, hval]
  apply Quot.sound
  show ((p ^ n : Nat) : Int) ∣ ((p ^ n : Nat) : Int) * crep - 0
  exact ⟨crep, by omega⟩

/-! ## M155-6: 台での instance -/

/-- **定理 (M155-6): 台の一般忠実性** — ℤ_p[[Y]]/(pY + Y^p − p) の
    次数 < p 剰余は任意の冪級数 witness に対して一意（分離性
    インターフェースが実際に inhabit されることの実証）。 -/
theorem zp_step_faithful (p : Nat) (hp : 2 ≤ p) {r r' : PS (zpRing p)}
    (hr : IsPolyBounded (zpRing p) r p)
    (hr' : IsPolyBounded (zpRing p) r' p)
    (h : Quot.mk (idealRel (psRing (zpRing p))
          (towerStepPoly p (zpRing p) (zpPi p) (zpPi p))) r
       = Quot.mk (idealRel (psRing (zpRing p))
          (towerStepPoly p (zpRing p) (zpPi p) (zpPi p))) r') :
    ∀ i, r i = r' i :=
  sep_poly_faithful p hp (zpRing p) (zpPi p) (zpPi p)
    (zp_separated p hp) hr hr' h

/-! ## M155-7: 総括 -/

/-- **M155-7a: 総括** — 分離性局在のデータ。 -/
structure TowerSeparationData (p : Nat) (hp : 2 ≤ p) where
  /-- 深度補題（分離性なしで成立）。 -/
  depth : ∀ (R : CRing) (piR lamR : R.carrier) (w : PS R),
    (∀ i, p ≤ i → psMul R w (towerStepPoly p R piR lamR) i = R.zero) →
    ∀ k j, IsIn2Pow R lamR piR k (w j)
  /-- 局在: 分離性 ⟹ 一般忠実性。 -/
  faithful_of_sep : ∀ (R : CRing) (piR lamR : R.carrier),
    IsSeparated2 R lamR piR →
    ∀ {r r' : PS R}, IsPolyBounded R r p → IsPolyBounded R r' p →
    Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR)) r
      = Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR)) r' →
    ∀ i, r i = r' i
  /-- ℤ_p の分離性。 -/
  zp_sep : IsSeparated2 (zpRing p) (zpPi p) (zpPi p)

/-- **M155-7b: witness**。 -/
def towerSeparationData (p : Nat) (hp : 2 ≤ p) :
    TowerSeparationData p hp where
  depth := fun R piR lamR w hlow =>
    depth_of_bounded_image p hp R piR lamR w hlow
  faithful_of_sep := fun R piR lamR hsep =>
    sep_poly_faithful p hp R piR lamR hsep
  zp_sep := zp_separated p hp

/-- **M155-7c: 存在**。 -/
theorem towerSeparation_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (TowerSeparationData p hp) :=
  ⟨towerSeparationData p hp⟩

end IUT
