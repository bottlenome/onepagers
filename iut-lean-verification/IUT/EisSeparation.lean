/-
# M160: eisRing の (λ,π)-adic 分離性（柱B）

M155 は塔一段商の次数 < p 剰余の一般忠実性（任意冪級数 witness）を
「(λ,π)-adic 分離性 ∩ₖ (λ,π)^k = 0」という単一条件に正確に局在させ、
塔の台 ℤ_p でこれを実証した。本層はその**レベル 1 版**: 分岐環
O = eisRing p = ℤ_p[[X]]/(X^{p−1} + π) 自身が (λ, π)-adic に分離的で
あることを証明し、M155 の `sep_poly_faithful` を O₂ = eisRing p で
instantiate する。鍵は M122 の安定化被約係数 c_i（Weierstrass 座標）の
ℤ_p 値化と、その (λ,π) 冪イデアル下の**深度簿記**である:

  π 倍は各座標を π 倍し（psC 定数積の係数公式）、λ 倍は座標を
  シフトし（域内 c_{i+1}(λx) = c_i(x)、巻き戻り c_0(λx) = −π·c_{p−2}(x)
  — M93F-2a/2b）、どちらの経路でも p−1 ステップごとに全座標が
  π 冪を 1 つ獲得する。従って x ∈ (λ,π)^{(p−1)d} なら全座標が
  (π)^d に沈み（弱形の深度補題 — ⌊k/(p−1)⌋ 深度で十分）、
  ℤ_p の分離性（M155-5 zp_separated）で座標 = 0、座標忠実性
  （M122-5 eisCoeff_faithful）で x = 0。

  * M160-1 `isIn2Pow_zero` / `isIn2Pow_add` / `isIn2Pow_of_le` /
    `isIn2Pow_pi_mul` — (λ,π) 冪イデアル述語の閉性簿記
    （0 所属・加法閉・深度単調・π 倍の深度 +1）
  * M160-2 `eisCoeffStab_sound` / `eisCoordStab` / `eisCoordStab_val` /
    `eisCoordStab_add` — 安定化被約係数の **O 上 ℤ_p 値化**
    （Quot.lift、well-definedness は M93F-1c の全レベル束）と加法性
  * M160-3 `eisCoeffZp_const_mul` / `eisCoordStab_pi_mul` /
    `eisCoordStab_lambda` / `negPi_mul_trunc_stable` /
    `eisCoeffStab_X_wrap` / `eisCoordStab_lambda_wrap` — 座標簿記:
    π 倍 = 座標の π 倍、λ 倍 = 域内シフト / 巻き戻り −π 倍
    （打ち切りレベル差は (−π)^{n+1} の p 進消滅で吸収）
  * M160-4 **`eis_coord_depth`（深度補題・技術的本丸）** —
    x ∈ (λ,π)^{(p−1)d} ⟹ 全座標 c_i(x) ∈ (π)^d
    （外側 d・内側 λ 予算 j ≤ p−1 の二重帰納）
  * M160-5 **`eis_separated`（本丸）** — IsSeparated2 (eisRing p) λ π
  * M160-6 `eis_step_faithful` — M155 `sep_poly_faithful` の
    O₂ = eisRing p での instance: eisRing[[Y]]/(πY + Y^p − λ) の
    次数 < p 剰余は**任意の冪級数 witness** に対して一意
  * M160-7 `EisSeparationData` — 総括

意義: M155 が「分離性」に局在させた塔座標の一般忠実性が、塔の
第 1 レベル（分岐拡大 O = ℤ_p[λ]）で実際に inhabit されることの実証。
これで一般座標忠実性は台 ℤ_p（M155-6）とレベル 1（本層）の両方で
閉じ、λ₂ の座標理論（M122 の塔版）への橋が架かる。

正直な限定: (1) 深度は弱形 ⌊k/(p−1)⌋ の粗い簿記（(p−1)d ステップで
深度 d）であり、正確な付値 ⌊k/(p−1)⌋ の最良性・λ 単独冪の深度は
追求しない（分離性にはこれで十分）。(2) instantiate は一般の
(piR, lamR) = (eisPi, eisLambda) での sep_poly_faithful 適用であり、
towerLevel p 1 の構造定数との同一視（塔の第 2 段の座標理論）は次層。
全て選択公理不使用。
-/
import IUT.TowerSeparation
import IUT.EisFaithful
import IUT.FormalGroupPoints

namespace IUT

/-! ## M160-1: (λ,π) 冪イデアル述語の閉性簿記 -/

/-- **M160-1a: 0 は全深度に沈む**。 -/
theorem isIn2Pow_zero (R : CRing) (lam piR : R.carrier) : ∀ k : Nat,
    IsIn2Pow R lam piR k R.zero := by
  intro k
  induction k with
  | zero => exact trivial
  | succ k ih =>
    refine ⟨R.zero, R.zero, ih, ih, ?_⟩
    rw [CRing.mul_zero R lam, CRing.mul_zero R piR, R.zero_add]

/-- **M160-1b: 加法閉性** — 深度 k 同士の和は深度 k。 -/
theorem isIn2Pow_add (R : CRing) (lam piR : R.carrier) : ∀ (k : Nat)
    (x y : R.carrier), IsIn2Pow R lam piR k x → IsIn2Pow R lam piR k y →
    IsIn2Pow R lam piR k (R.add x y) := by
  intro k
  induction k with
  | zero => intro x y _ _; exact trivial
  | succ k ih =>
    intro x y hx hy
    obtain ⟨a1, b1, ha1, hb1, hx1⟩ := hx
    obtain ⟨a2, b2, ha2, hb2, hy1⟩ := hy
    refine ⟨R.add a1 a2, R.add b1 b2, ih a1 a2 ha1 ha2,
      ih b1 b2 hb1 hb2, ?_⟩
    rw [hx1, hy1, R.left_distrib lam a1 a2, R.left_distrib piR b1 b2]
    exact CRing.add_add_add_comm R (R.mul lam a1) (R.mul piR b1)
      (R.mul lam a2) (R.mul piR b2)

/-- **M160-1c: 深度単調性** — 深度 k 所属は任意の j ≤ k 深度所属。 -/
theorem isIn2Pow_of_le (R : CRing) (lam piR : R.carrier) : ∀ (k j : Nat),
    j ≤ k → ∀ x : R.carrier,
    IsIn2Pow R lam piR k x → IsIn2Pow R lam piR j x := by
  intro k
  induction k with
  | zero =>
    intro j hj x hx
    have hj0 : j = 0 := by omega
    rw [hj0]
    exact trivial
  | succ k ih =>
    intro j hj x hx
    cases j with
    | zero => exact trivial
    | succ j =>
      obtain ⟨a, b, ha, hb, hxe⟩ := hx
      exact ⟨a, b, ih j (by omega) a ha, ih j (by omega) b hb, hxe⟩

/-- **M160-1d: π 倍の深度 +1** — y ∈ (λ,π)^k なら π·y ∈ (λ,π)^{k+1}
    （witness は a = 0, b = y）。 -/
theorem isIn2Pow_pi_mul (R : CRing) (lam piR : R.carrier) (k : Nat)
    (y : R.carrier) (hy : IsIn2Pow R lam piR k y) :
    IsIn2Pow R lam piR (k + 1) (R.mul piR y) := by
  refine ⟨R.zero, y, isIn2Pow_zero R lam piR k, hy, ?_⟩
  rw [CRing.mul_zero R lam, R.zero_add]

/-! ## M160-2: 安定化被約係数の O 上 ℤ_p 値化 -/

/-- **M160-2a: 安定化係数の well-definedness（ℤ_p 値）** —
    f ≡ g mod (E) なら c_i(f) = c_i(g) in ℤ_p
    （M93F-1c の eisCoeff_sound の全レベル束）。 -/
theorem eisCoeffStab_sound (p : Nat) (i : Nat) (hi : i < p - 1)
    (f g : PS (zpRing p)) (hfg : eisRel p f g) :
    eisCoeffStab p f i = eisCoeffStab p g i := by
  apply Subtype.ext
  funext n
  show (eisCoeffZp p f i n).val n = (eisCoeffZp p g i n).val n
  exact eisCoeff_sound p i n hi f g hfg

/-- **M160-2b: O の ℤ_p 値座標** c_i : O → ℤ_p（i < p−1、Quot.lift）。
    M93F-1c のレベル別座標 eisCoeff の全レベル束ね上げ。 -/
def eisCoordStab (p : Nat) (i : Nat) (hi : i < p - 1)
    (x : EisCarrier p) : (Zp p).carrier :=
  Quot.lift (fun f => eisCoeffStab p f i)
    (fun f g hfg => eisCoeffStab_sound p i hi f g hfg) x

/-- **M160-2c: レベル n 成分は eisCoeff**（定義一致）。 -/
theorem eisCoordStab_val (p : Nat) (i n : Nat) (hi : i < p - 1)
    (x : EisCarrier p) :
    (eisCoordStab p i hi x).val n = eisCoeff p i n hi x := by
  induction x using Quot.ind; rename_i f
  rfl

/-- 代表元上の加法性（M93F-1b の加法性の ℤ_p 値版）。 -/
theorem eisCoeffStab_psAdd (p : Nat) (f g : PS (zpRing p)) (i : Nat) :
    eisCoeffStab p (psAdd (zpRing p) f g) i
      = (zpRing p).add (eisCoeffStab p f i) (eisCoeffStab p g i) := by
  apply Subtype.ext
  funext n
  show (eisCoeffZp p (psAdd (zpRing p) f g) i n).val n
    = ((zpRing p).add (eisCoeffStab p f i) (eisCoeffStab p g i)).val n
  rw [eisCoeffZp_add p f g i n]
  rfl

/-- **M160-2d: 座標の加法性**（商上）。 -/
theorem eisCoordStab_add (p : Nat) (i : Nat) (hi : i < p - 1)
    (x y : EisCarrier p) :
    eisCoordStab p i hi ((eisRing p).add x y)
      = (zpRing p).add (eisCoordStab p i hi x) (eisCoordStab p i hi y) := by
  induction x using Quot.ind; rename_i f
  induction y using Quot.ind; rename_i g
  exact eisCoeffStab_psAdd p f g i

/-! ## M160-3: 座標簿記 — π 倍と λ 倍 -/

/-- O の π（構造射による p の像）。 -/
def eisPi (p : Nat) : (eisRing p).carrier := (eisOf p).map (zpPi p)

/-- **M160-3a: 定数倍の被約係数**（代表元上・全打ち切り） —
    c_i(a·f) = a·c_i(f)（psC 定数積の係数公式 + 左スカラー倍）。 -/
theorem eisCoeffZp_const_mul (p : Nat) (a : (Zp p).carrier)
    (f : PS (zpRing p)) (i n : Nat) :
    eisCoeffZp p (psMul (zpRing p) (psC (zpRing p) a) f) i n
      = (zpRing p).mul a (eisCoeffZp p f i n) := by
  have hcong : ∀ j, j < n →
      (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
        (psMul (zpRing p) (psC (zpRing p) a) f (i + j * (p - 1)))
      = (zpRing p).mul a
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
            (f (i + j * (p - 1)))) := by
    intro j _
    rw [psC_mul_coeff (zpRing p) a f (i + j * (p - 1)),
      ← (zpRing p).mul_assoc (rpow (zpRing p) (zpNegPi p) j) a
        (f (i + j * (p - 1))),
      (zpRing p).mul_comm (rpow (zpRing p) (zpNegPi p) j) a,
      (zpRing p).mul_assoc a (rpow (zpRing p) (zpNegPi p) j)
        (f (i + j * (p - 1)))]
  show rsum (zpRing p)
      (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
        (psMul (zpRing p) (psC (zpRing p) a) f (i + j * (p - 1)))) n
    = (zpRing p).mul a (eisCoeffZp p f i n)
  rw [rsum_congr (zpRing p) n hcong]
  exact (rsum_mul_left (zpRing p)
    (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
      (f (i + j * (p - 1)))) a n).symm

/-- **M160-3b: π 倍の座標簿記** — c_i(π·x) = π·c_i(x) in ℤ_p。 -/
theorem eisCoordStab_pi_mul (p : Nat) (x : EisCarrier p) (i : Nat)
    (hi : i < p - 1) :
    eisCoordStab p i hi ((eisRing p).mul (eisPi p) x)
      = (zpRing p).mul (zpPi p) (eisCoordStab p i hi x) := by
  induction x using Quot.ind; rename_i f
  apply Subtype.ext
  funext n
  show (eisCoeffZp p (psMul (zpRing p) (psC (zpRing p) (zpPi p)) f) i n).val n
    = ((zpRing p).mul (zpPi p) (eisCoeffStab p f i)).val n
  rw [eisCoeffZp_const_mul p (zpPi p) f i n]
  rfl

/-- **M160-3c: λ 倍の域内シフト（ℤ_p 値版）** —
    c_{i+1}(λ·x) = c_i(x)（M93F-2a の全レベル束）。 -/
theorem eisCoordStab_lambda (p : Nat) (x : EisCarrier p) (i : Nat)
    (hi1 : i + 1 < p - 1) :
    eisCoordStab p (i + 1) hi1 ((eisRing p).mul (eisLambda p) x)
      = eisCoordStab p i (Nat.lt_of_succ_lt hi1) x := by
  apply Subtype.ext
  funext n
  rw [eisCoordStab_val p (i + 1) n hi1,
    eisCoordStab_val p i n (Nat.lt_of_succ_lt hi1)]
  exact eisCoeff_lambda_mul p x i n hi1

/-- 打ち切りレベル差の吸収: −π 倍の後ではレベル n+1 成分は
    n 打ち切りと n+1 打ち切りで一致（差の項 (−π)^{n+1}·f は
    M93F-0c で消滅）。 -/
theorem negPi_mul_trunc_stable (p : Nat) (f : PS (zpRing p)) (k n : Nat) :
    ((zpRing p).mul (zpNegPi p) (eisCoeffZp p f k (n + 1))).val (n + 1)
      = ((zpRing p).mul (zpNegPi p) (eisCoeffZp p f k n)).val (n + 1) := by
  have hd : eisCoeffZp p f k (n + 1)
      = (zpRing p).add (eisCoeffZp p f k n)
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n)
            (f (k + n * (p - 1)))) := rfl
  have hpow : (zpRing p).mul (zpNegPi p)
      ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n) (f (k + n * (p - 1))))
      = (zpRing p).mul (rpow (zpRing p) (zpNegPi p) (n + 1))
          (f (k + n * (p - 1))) := by
    show (zpRing p).mul (zpNegPi p)
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n) (f (k + n * (p - 1))))
      = (zpRing p).mul
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n) (zpNegPi p))
          (f (k + n * (p - 1)))
    rw [(zpRing p).mul_comm (rpow (zpRing p) (zpNegPi p) n) (zpNegPi p),
      (zpRing p).mul_assoc (zpNegPi p) (rpow (zpRing p) (zpNegPi p) n)
        (f (k + n * (p - 1)))]
  have hsplit : (zpRing p).mul (zpNegPi p) (eisCoeffZp p f k (n + 1))
      = (zpRing p).add
          ((zpRing p).mul (zpNegPi p) (eisCoeffZp p f k n))
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) (n + 1))
            (f (k + n * (p - 1)))) := by
    rw [hd, (zpRing p).left_distrib, hpow]
  rw [hsplit]
  show (zmodRing (p ^ (n + 1))).add
      (((zpRing p).mul (zpNegPi p) (eisCoeffZp p f k n)).val (n + 1))
      (((zpRing p).mul (rpow (zpRing p) (zpNegPi p) (n + 1))
        (f (k + n * (p - 1)))).val (n + 1))
    = ((zpRing p).mul (zpNegPi p) (eisCoeffZp p f k n)).val (n + 1)
  rw [val_negPiPow_mul p (Nat.le_refl (n + 1)) (f (k + n * (p - 1)))]
  show (zmodRing (p ^ (n + 1))).add
      (((zpRing p).mul (zpNegPi p) (eisCoeffZp p f k n)).val (n + 1))
      ((zmodRing (p ^ (n + 1))).zero)
    = ((zpRing p).mul (zpNegPi p) (eisCoeffZp p f k n)).val (n + 1)
  exact CRing.add_zero (zmodRing (p ^ (n + 1)))
    (((zpRing p).mul (zpNegPi p) (eisCoeffZp p f k n)).val (n + 1))

/-- **M160-3d: λ 倍の巻き戻り（代表元・ℤ_p 値版）** —
    c_0(X·f) = −π·c_{p−2}(f) in ℤ_p（M93F-2b の全レベル束、
    レベル差は negPi_mul_trunc_stable で吸収）。 -/
theorem eisCoeffStab_X_wrap (p : Nat) (hp : 2 ≤ p) (f : PS (zpRing p)) :
    eisCoeffStab p (psMul (zpRing p) (psX (zpRing p)) f) 0
      = (zpRing p).mul (zpNegPi p) (eisCoeffStab p f (p - 2)) := by
  apply Subtype.ext
  funext n
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ n =>
    show (eisCoeffZp p (psMul (zpRing p) (psX (zpRing p)) f) 0 (n + 1)).val
        (n + 1)
      = ((zpRing p).mul (zpNegPi p) (eisCoeffStab p f (p - 2))).val (n + 1)
    rw [eisCoeffZp_X_wrap p hp f n]
    show ((zpRing p).mul (zpNegPi p) (eisCoeffZp p f (p - 2) n)).val (n + 1)
      = ((zpRing p).mul (zpNegPi p) (eisCoeffZp p f (p - 2) (n + 1))).val
          (n + 1)
    exact (negPi_mul_trunc_stable p f (p - 2) n).symm

/-- **M160-3e: λ 倍の巻き戻り（商上）** — c_0(λ·x) = −π·c_{p−2}(x)。 -/
theorem eisCoordStab_lambda_wrap (p : Nat) (hp : 2 ≤ p)
    (x : EisCarrier p) (h0 : 0 < p - 1) (hpw : p - 2 < p - 1) :
    eisCoordStab p 0 h0 ((eisRing p).mul (eisLambda p) x)
      = (zpRing p).mul (zpNegPi p) (eisCoordStab p (p - 2) hpw x) := by
  induction x using Quot.ind; rename_i f
  exact eisCoeffStab_X_wrap p hp f

/-! ## M160-4: 深度補題（技術的本丸） -/

/-- **定理 (M160-4): 座標深度補題（弱形）** — x ∈ (λ,π)^{(p−1)d} なら
    全座標 c_i(x) ∈ (π)^d in ℤ_p。外側 d の帰納の中で、λ 予算
    j ≤ p−1 の内側帰納: 深度 (p−1)d + j の元は添字 i < j の座標が
    既に深度 d+1（λ の巻き戻り・π 倍はどちらも π 冪を供給し、
    域内シフトは予算を 1 消費して添字を下げる）。 -/
theorem eis_coord_depth (p : Nat) (hp : 2 ≤ p) : ∀ (d : Nat)
    (x : EisCarrier p),
    IsIn2Pow (eisRing p) (eisLambda p) (eisPi p) ((p - 1) * d) x →
    ∀ (i : Nat) (hi : i < p - 1),
    IsIn2Pow (zpRing p) (zpPi p) (zpPi p) d (eisCoordStab p i hi x) := by
  intro d
  induction d with
  | zero => intro x _ i hi; exact trivial
  | succ d ih =>
    have inner : ∀ (j : Nat), j ≤ p - 1 → ∀ (x : EisCarrier p),
        IsIn2Pow (eisRing p) (eisLambda p) (eisPi p) ((p - 1) * d + j) x →
        ∀ (i : Nat) (hi : i < p - 1), i < j →
        IsIn2Pow (zpRing p) (zpPi p) (zpPi p) (d + 1)
          (eisCoordStab p i hi x) := by
      intro j
      induction j with
      | zero =>
        intro _ x _ i hi hij
        exact absurd hij (Nat.not_lt_zero i)
      | succ j ihj =>
        intro hj1 x hx i hi hij
        obtain ⟨a, b, ha, hb, hxe⟩ := hx
        -- b の座標は深度 d（外側 IH + 深度単調性）
        have hb' : IsIn2Pow (zpRing p) (zpPi p) (zpPi p) d
            (eisCoordStab p i hi b) :=
          ih b (isIn2Pow_of_le (eisRing p) (eisLambda p) (eisPi p)
            ((p - 1) * d + j) ((p - 1) * d)
            (Nat.le_add_right ((p - 1) * d) j) b hb) i hi
        rw [hxe, eisCoordStab_add p i hi ((eisRing p).mul (eisLambda p) a)
            ((eisRing p).mul (eisPi p) b),
          eisCoordStab_pi_mul p b i hi]
        refine isIn2Pow_add (zpRing p) (zpPi p) (zpPi p) (d + 1) _ _ ?_
          (isIn2Pow_pi_mul (zpRing p) (zpPi p) (zpPi p) d
            (eisCoordStab p i hi b) hb')
        cases i with
        | zero =>
          -- 巻き戻り: c_0(λa) = −π·c_{p−2}(a) ∈ (π)^{d+1}
          have hpw : p - 2 < p - 1 := by omega
          have hca : IsIn2Pow (zpRing p) (zpPi p) (zpPi p) d
              (eisCoordStab p (p - 2) hpw a) :=
            ih a (isIn2Pow_of_le (eisRing p) (eisLambda p) (eisPi p)
              ((p - 1) * d + j) ((p - 1) * d)
              (Nat.le_add_right ((p - 1) * d) j) a ha) (p - 2) hpw
          have hpi2 : IsIn2Pow (zpRing p) (zpPi p) (zpPi p) (d + 1)
              ((zpRing p).mul (zpPi p) (eisCoordStab p (p - 2) hpw a)) :=
            isIn2Pow_pi_mul (zpRing p) (zpPi p) (zpPi p) d
              (eisCoordStab p (p - 2) hpw a) hca
          have hneg : IsIn2Pow (zpRing p) (zpPi p) (zpPi p) (d + 1)
              ((zpRing p).neg ((zpRing p).mul (zpPi p)
                (eisCoordStab p (p - 2) hpw a))) :=
            isIn2Pow_neg (zpRing p) (zpPi p) (zpPi p) (d + 1)
              ((zpRing p).mul (zpPi p) (eisCoordStab p (p - 2) hpw a)) hpi2
          have hnm : (zpRing p).mul (zpNegPi p)
              (eisCoordStab p (p - 2) hpw a)
              = (zpRing p).neg ((zpRing p).mul (zpPi p)
                  (eisCoordStab p (p - 2) hpw a)) :=
            CRing.neg_mul (zpRing p) (zpPi p) (eisCoordStab p (p - 2) hpw a)
          rw [eisCoordStab_lambda_wrap p hp a hi hpw, hnm]
          exact hneg
        | succ i' =>
          -- 域内シフト: c_{i'+1}(λa) = c_{i'}(a)、予算 j に帰着
          rw [eisCoordStab_lambda p a i' hi]
          exact ihj (by omega) a ha i' (Nat.lt_of_succ_lt hi) (by omega)
    intro x hx i hi
    have hx' : IsIn2Pow (eisRing p) (eisLambda p) (eisPi p)
        ((p - 1) * d + (p - 1)) x := by
      have he : (p - 1) * (d + 1) = (p - 1) * d + (p - 1) :=
        Nat.mul_succ (p - 1) d
      rw [← he]
      exact hx
    exact inner (p - 1) (Nat.le_refl (p - 1)) x hx' i hi hi

/-! ## M160-5: eisRing の (λ,π)-adic 分離性（本丸） -/

/-- **定理 (M160-5): eisRing の分離性** — ∩ₖ (λ,π)^k = 0 in O。
    深度補題（M160-4）で全座標を全深度に沈め、ℤ_p の分離性
    （M155-5）で座標 = 0、座標忠実性（M122-5）で x = 0。 -/
theorem eis_separated (p : Nat) (hp : 2 ≤ p) :
    IsSeparated2 (eisRing p) (eisLambda p) (eisPi p) := by
  intro x hall
  apply eisCoeff_faithful p hp x
  intro i n hi
  have hc : eisCoordStab p i hi x = (zpRing p).zero := by
    apply zp_separated p hp
    intro k
    exact eis_coord_depth p hp k x (hall ((p - 1) * k)) i hi
  rw [← eisCoordStab_val p i n hi x, hc]
  rfl

/-! ## M160-6: M155 の instance — レベル 1 の一般座標忠実性 -/

/-- **定理 (M160-6): レベル 1 の一般忠実性** —
    eisRing[[Y]]/(πY + Y^p − λ) の次数 < p 剰余は**任意の冪級数
    witness** に対して一意（M155 sep_poly_faithful の O₂ = eisRing p
    での instantiate。M147F の多項式 witness 限定の撤廃がレベル 1 で
    成立）。 -/
theorem eis_step_faithful (p : Nat) (hp : 2 ≤ p) {r r' : PS (eisRing p)}
    (hr : IsPolyBounded (eisRing p) r p)
    (hr' : IsPolyBounded (eisRing p) r' p)
    (h : Quot.mk (idealRel (psRing (eisRing p))
          (towerStepPoly p (eisRing p) (eisPi p) (eisLambda p))) r
       = Quot.mk (idealRel (psRing (eisRing p))
          (towerStepPoly p (eisRing p) (eisPi p) (eisLambda p))) r') :
    ∀ i, r i = r' i :=
  sep_poly_faithful p hp (eisRing p) (eisPi p) (eisLambda p)
    (eis_separated p hp) hr hr' h

/-! ## M160-7: 総括 -/

/-- **M160-7a: 総括** — eisRing の分離性データ。 -/
structure EisSeparationData (p : Nat) (hp : 2 ≤ p) where
  /-- 座標深度補題（弱形）。 -/
  coord_depth : ∀ (d : Nat) (x : EisCarrier p),
    IsIn2Pow (eisRing p) (eisLambda p) (eisPi p) ((p - 1) * d) x →
    ∀ (i : Nat) (hi : i < p - 1),
    IsIn2Pow (zpRing p) (zpPi p) (zpPi p) d (eisCoordStab p i hi x)
  /-- eisRing の (λ,π)-adic 分離性。 -/
  separated : IsSeparated2 (eisRing p) (eisLambda p) (eisPi p)
  /-- レベル 1 の一般座標忠実性（M155 instance）。 -/
  step_faithful : ∀ {r r' : PS (eisRing p)},
    IsPolyBounded (eisRing p) r p → IsPolyBounded (eisRing p) r' p →
    Quot.mk (idealRel (psRing (eisRing p))
        (towerStepPoly p (eisRing p) (eisPi p) (eisLambda p))) r
      = Quot.mk (idealRel (psRing (eisRing p))
        (towerStepPoly p (eisRing p) (eisPi p) (eisLambda p))) r' →
    ∀ i, r i = r' i

/-- **M160-7b: witness**。 -/
def eisSeparationData (p : Nat) (hp : 2 ≤ p) : EisSeparationData p hp where
  coord_depth := eis_coord_depth p hp
  separated := eis_separated p hp
  step_faithful := fun hr hr' h => eis_step_faithful p hp hr hr' h

/-- **M160-7c: 存在**。 -/
theorem eisSeparation_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (EisSeparationData p hp) :=
  ⟨eisSeparationData p hp⟩

end IUT
