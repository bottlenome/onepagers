/-
# M111: 剰余塔と非自明性 — ρₙ : Oₙ → ℤ/p と Oₙ ≠ 0

分岐拡大の塔 O₁ ⊆ O₂ ⊆ …（M109 EisTowerRings）の各レベルから
剰余体 ℤ/p への環準同型（剰余射）ρₙ を構成し、その存在から塔の
**非自明性**（1 ≠ 0、λₙ・πₙ が単元でない）を導く。

  * M111-1 `towerStepPoly_coeff_zero` — 一段多項式の定数項は −λ
  * M111-2 `eisResFun_congr` / `eisRes` — 基底剰余射
    O = ℤ_p[[X]]/(E) → ℤ/p（定数項 → mod p。well-defined 性は
    (h·E)₀ = h₀·π と proj_p_zero）
  * M111-3 `eisRes_pi` / `eisRes_lambda` — ρ₁(π) = 0・ρ₁(λ) = 0
  * M111-4 `towerResFun_congr` / `towerResStep` — 一般降下:
    ρ(λ) = 0 なる ρ : R → ℤ/p は R[[Y]]/(πY + Y^p − λ) を通る
    （イデアル生成元の定数項が −λ で ρ に消えるため）
  * M111-5 `towerResStep_pi` / `towerResStep_lam` — π'・λ' も消える
  * M111-6 `TowerRes` / `towerRes` — 全レベルの剰余射の再帰構成
  * M111-7 `towerRes_compat` — 剰余射は塔の推移射と両立（rfl!）
  * M111-8 `tower_one_ne_zero` / `tower_lam_not_unit` /
    `tower_pi_not_unit` — 非自明性: Oₙ ≠ 0 かつ λₙ, πₙ ∉ Oₙ^×
  * M111-9 `ResidueTowerData` — 総括

正直な限定: ρₙ の存在は「Oₙ ≠ 0」と「λₙ が非単元」を与えるが、
「λₙ ≠ 0」自体は与えない（それには各レベルの整域性が必要で、
レベルごとの Eisenstein 係数論法として今後の課題）。

全て選択公理不使用。
-/
import IUT.EisTowerRings
import IUT.EisDomain
import IUT.LTErrorDivisible
import IUT.FormalGroupExists

namespace IUT

/-! ## 一段多項式の定数項 -/

/-- **M111-1: 一段多項式の定数項** (πY + Y^p − λ)₀ = −λ
    （p ≥ 1 で Y^p の定数項は 0）。 -/
theorem towerStepPoly_coeff_zero (p : Nat) (hp : 1 ≤ p) (R : CRing)
    (piR lamR : R.carrier) :
    towerStepPoly p R piR lamR 0 = R.neg lamR := by
  show R.add (R.add (psSingle R piR 1 0) (psMono R p 0))
      (R.neg (psC R lamR 0)) = R.neg lamR
  rw [show psSingle R piR 1 0 = R.zero from if_neg (by omega),
    show psMono R p 0 = R.zero from if_neg (by omega),
    show psC R lamR 0 = lamR from if_pos rfl,
    R.zero_add, R.zero_add]

/-! ## 基底剰余射 O → ℤ/p -/

/-- 基底剰余の代表写像: 定数項の mod p 像。 -/
def eisResFun (p : Nat) (f : PS (zpRing p)) : (zmodRing (p ^ 1)).carrier :=
  (projRing p 1).map (f 0)

/-- **定理 (M111-2a): well-defined 性** — f ≡ g (mod E) なら定数項の
    mod p 像は一致（(h·E)₀ = h₀·π が proj_p_zero で消える）。 -/
theorem eisResFun_congr (p : Nat) (hp : 2 ≤ p) {f g : PS (zpRing p)}
    (h : eisRel p f g) : eisResFun p f = eisResFun p g := by
  obtain ⟨w, hw⟩ := h
  have h0 : (zpRing p).add (f 0) ((zpRing p).neg (g 0))
      = (zpRing p).mul (w 0) (eisPoly p 0) :=
    (congrFun hw 0).trans (psMul_coeff_zero (zpRing p) w (eisPoly p))
  have h1 : (projRing p 1).map
      ((zpRing p).add (f 0) ((zpRing p).neg (g 0)))
      = (zmodRing (p ^ 1)).zero := by
    rw [h0, eisPoly_coeff_zero p hp, (projRing p 1).map_mul,
      proj_p_zero p, CRing.mul_zero (zmodRing (p ^ 1))]
  have h2 : (zmodRing (p ^ 1)).add ((projRing p 1).map (f 0))
      ((zmodRing (p ^ 1)).neg ((projRing p 1).map (g 0)))
      = (zmodRing (p ^ 1)).zero := by
    rw [← RingHom.map_neg (projRing p 1) (g 0), ← (projRing p 1).map_add]
    exact h1
  exact CRing.eq_of_sub_eq_zero (zmodRing (p ^ 1)) h2

/-- **M111-2b: 基底剰余射** ρ₁ : O → ℤ/p（環準同型）。 -/
def eisRes (p : Nat) (hp : 2 ≤ p) :
    RingHom (eisRing p) (zmodRing (p ^ 1)) where
  map := Quot.lift (eisResFun p) (fun _ _ h => eisResFun_congr p hp h)
  map_add := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    exact (projRing p 1).map_add (f 0) (g 0)
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    show (projRing p 1).map (psMul (zpRing p) f g 0)
      = (zmodRing (p ^ 1)).mul ((projRing p 1).map (f 0))
        ((projRing p 1).map (g 0))
    rw [psMul_coeff_zero (zpRing p) f g]
    exact (projRing p 1).map_mul (f 0) (g 0)
  map_one := rfl

/-- **M111-3a: ρ₁(π) = 0**（π の定数項は π で mod p 消滅）。 -/
theorem eisRes_pi (p : Nat) (hp : 2 ≤ p) :
    (eisRes p hp).map ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
      = (zmodRing (p ^ 1)).zero := by
  show (projRing p 1).map ((toZp p).map ((p : Nat) : Int))
    = (zmodRing (p ^ 1)).zero
  exact proj_p_zero p

/-- **M111-3b: ρ₁(λ) = 0**（X の定数項は 0）。 -/
theorem eisRes_lambda (p : Nat) (hp : 2 ≤ p) :
    (eisRes p hp).map (eisLambda p) = (zmodRing (p ^ 1)).zero := by
  show (projRing p 1).map ((zpRing p).zero) = (zmodRing (p ^ 1)).zero
  exact RingHom.map_zero (projRing p 1)

/-! ## 一般降下: ρ は一段昇りを通る -/

/-- 一段昇りの剰余代表写像: 定数項の ρ 像。 -/
def towerResFun (p : Nat) {R : CRing}
    (ρ : RingHom R (zmodRing (p ^ 1))) (f : PS R) :
    (zmodRing (p ^ 1)).carrier :=
  ρ.map (f 0)

/-- **定理 (M111-4a): well-defined 性** — 生成元の定数項は −λ で
    ρ(λ) = 0 だから ρ∘(定数項) はイデアルを消す。 -/
theorem towerResFun_congr (p : Nat) (hp : 1 ≤ p) {R : CRing}
    (piR lamR : R.carrier) (ρ : RingHom R (zmodRing (p ^ 1)))
    (hlam : ρ.map lamR = (zmodRing (p ^ 1)).zero)
    {f g : PS R}
    (h : idealRel (psRing R) (towerStepPoly p R piR lamR) f g) :
    towerResFun p ρ f = towerResFun p ρ g := by
  obtain ⟨w, hw⟩ := h
  have h0 : R.add (f 0) (R.neg (g 0))
      = R.mul (w 0) (towerStepPoly p R piR lamR 0) :=
    (congrFun hw 0).trans
      (psMul_coeff_zero R w (towerStepPoly p R piR lamR))
  have h1 : ρ.map (R.add (f 0) (R.neg (g 0)))
      = (zmodRing (p ^ 1)).zero := by
    rw [h0, towerStepPoly_coeff_zero p hp R piR lamR, ρ.map_mul,
      RingHom.map_neg ρ lamR, hlam, CRing.neg_zero (zmodRing (p ^ 1)),
      CRing.mul_zero (zmodRing (p ^ 1))]
  have h2 : (zmodRing (p ^ 1)).add (ρ.map (f 0))
      ((zmodRing (p ^ 1)).neg (ρ.map (g 0)))
      = (zmodRing (p ^ 1)).zero := by
    rw [← RingHom.map_neg ρ (g 0), ← ρ.map_add]
    exact h1
  exact CRing.eq_of_sub_eq_zero (zmodRing (p ^ 1)) h2

/-- **M111-4b: 一般降下** — ρ : R → ℤ/p、ρ(λ) = 0 なら
    ρ' : R[[Y]]/(πY + Y^p − λ) → ℤ/p（定数項 → ρ 像）。 -/
def towerResStep (p : Nat) (hp : 1 ≤ p) {R : CRing}
    (piR lamR : R.carrier) (ρ : RingHom R (zmodRing (p ^ 1)))
    (hlam : ρ.map lamR = (zmodRing (p ^ 1)).zero) :
    RingHom (towerStep p R piR lamR) (zmodRing (p ^ 1)) where
  map := Quot.lift (towerResFun p ρ)
    (fun _ _ h => towerResFun_congr p hp piR lamR ρ hlam h)
  map_add := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    exact ρ.map_add (f 0) (g 0)
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    show ρ.map (psMul R f g 0)
      = (zmodRing (p ^ 1)).mul (ρ.map (f 0)) (ρ.map (g 0))
    rw [psMul_coeff_zero R f g]
    exact ρ.map_mul (f 0) (g 0)
  map_one := ρ.map_one

/-- **M111-5a: ρ'(ι π) = ρ(π)**（定数の像は定数項の像）— 特に
    ρ(π) = 0 なら ρ'(π') = 0。 -/
theorem towerResStep_pi (p : Nat) (hp : 1 ≤ p) {R : CRing}
    (piR lamR : R.carrier) (ρ : RingHom R (zmodRing (p ^ 1)))
    (hlam : ρ.map lamR = (zmodRing (p ^ 1)).zero)
    (hpi : ρ.map piR = (zmodRing (p ^ 1)).zero) :
    (towerResStep p hp piR lamR ρ hlam).map
      ((towerStepOf p R piR lamR).map piR)
      = (zmodRing (p ^ 1)).zero := by
  show ρ.map piR = (zmodRing (p ^ 1)).zero
  exact hpi

/-- **M111-5b: ρ'(λ') = 0**（Y の定数項は 0）。 -/
theorem towerResStep_lam (p : Nat) (hp : 1 ≤ p) {R : CRing}
    (piR lamR : R.carrier) (ρ : RingHom R (zmodRing (p ^ 1)))
    (hlam : ρ.map lamR = (zmodRing (p ^ 1)).zero) :
    (towerResStep p hp piR lamR ρ hlam).map (towerLam p R piR lamR)
      = (zmodRing (p ^ 1)).zero := by
  show ρ.map R.zero = (zmodRing (p ^ 1)).zero
  exact RingHom.map_zero ρ

/-! ## 全レベルの剰余射 -/

/-- **M111-6a: 一段の剰余データ** — 剰余射と π・λ の消滅。 -/
structure TowerRes (p : Nat) (L : TowerLevel p) where
  /-- 剰余射 ρ : Oₙ → ℤ/p。 -/
  res : RingHom L.ring (zmodRing (p ^ 1))
  /-- ρ(πₙ) = 0。 -/
  res_pi : res.map L.pi = (zmodRing (p ^ 1)).zero
  /-- ρ(λₙ) = 0。 -/
  res_lam : res.map L.lam = (zmodRing (p ^ 1)).zero

/-- **定理 (M111-6b): 剰余射の再帰構成** — 全レベル n に
    ρₙ : Oₙ₊₁ → ℤ/p が存在（基底は eisRes、一段は towerResStep）。 -/
def towerRes (p : Nat) (hp : 2 ≤ p) :
    (n : Nat) → TowerRes p (towerLevel p n)
  | 0 => ⟨eisRes p hp, eisRes_pi p hp, eisRes_lambda p hp⟩
  | n + 1 =>
    ⟨towerResStep p (Nat.le_of_succ_le hp) (towerLevel p n).pi
        (towerLevel p n).lam (towerRes p hp n).res
        (towerRes p hp n).res_lam,
      towerResStep_pi p (Nat.le_of_succ_le hp) (towerLevel p n).pi
        (towerLevel p n).lam (towerRes p hp n).res
        (towerRes p hp n).res_lam (towerRes p hp n).res_pi,
      towerResStep_lam p (Nat.le_of_succ_le hp) (towerLevel p n).pi
        (towerLevel p n).lam (towerRes p hp n).res
        (towerRes p hp n).res_lam⟩

/-- **定理 (M111-7): 剰余射は塔と両立** — ρₙ₊₁ ∘ ι = ρₙ
    （定数の定数項はそれ自身なので定義から rfl）。 -/
theorem towerRes_compat (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (a : (towerLevel p n).ring.carrier) :
    (towerRes p hp (n + 1)).res.map ((towerHom p n).map a)
      = (towerRes p hp n).res.map a := rfl

/-! ## 非自明性 -/

/-- **定理 (M111-8a): Oₙ ≠ 0** — 全レベルで 1 ≠ 0
    （剰余射で ℤ/p に落とすと 1 ≠ 0 に矛盾）。 -/
theorem tower_one_ne_zero (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    (towerLevel p n).ring.one ≠ (towerLevel p n).ring.zero := by
  intro h
  have h1 : (towerRes p hp n).res.map (towerLevel p n).ring.one
      = (towerRes p hp n).res.map (towerLevel p n).ring.zero :=
    congrArg (towerRes p hp n).res.map h
  rw [(towerRes p hp n).res.map_one,
    RingHom.map_zero (towerRes p hp n).res] at h1
  exact zmod_one_ne_zero (p ^ 1) (two_le_pow p hp 1 (Nat.le_refl 1)) h1

/-- **定理 (M111-8b): λₙ は単元でない** — λₙ·v = 1 なら剰余射で
    0 = 1 in ℤ/p となり矛盾。 -/
theorem tower_lam_not_unit (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (v : (towerLevel p n).ring.carrier) :
    (towerLevel p n).ring.mul (towerLevel p n).lam v
      ≠ (towerLevel p n).ring.one := by
  intro h
  have h1 := congrArg (towerRes p hp n).res.map h
  rw [(towerRes p hp n).res.map_mul, (towerRes p hp n).res_lam,
    CRing.zero_mul (zmodRing (p ^ 1)),
    (towerRes p hp n).res.map_one] at h1
  exact zmod_one_ne_zero (p ^ 1) (two_le_pow p hp 1 (Nat.le_refl 1))
    h1.symm

/-- **定理 (M111-8c): πₙ は単元でない**（λₙ と同じ論法）。 -/
theorem tower_pi_not_unit (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (v : (towerLevel p n).ring.carrier) :
    (towerLevel p n).ring.mul (towerLevel p n).pi v
      ≠ (towerLevel p n).ring.one := by
  intro h
  have h1 := congrArg (towerRes p hp n).res.map h
  rw [(towerRes p hp n).res.map_mul, (towerRes p hp n).res_pi,
    CRing.zero_mul (zmodRing (p ^ 1)),
    (towerRes p hp n).res.map_one] at h1
  exact zmod_one_ne_zero (p ^ 1) (two_le_pow p hp 1 (Nat.le_refl 1))
    h1.symm

/-! ## 総括 -/

/-- **M111-9a: 総括** — 剰余塔データ: 全レベルの剰余射・塔両立・
    非自明性（1 ≠ 0、λ・π 非単元）。 -/
structure ResidueTowerData (p : Nat) (hp : 2 ≤ p) where
  /-- 各レベルの剰余射（π・λ 消滅つき）。 -/
  res : (n : Nat) → TowerRes p (towerLevel p n)
  /-- 剰余射は塔の推移射と両立。 -/
  compat : ∀ (n : Nat) (a : (towerLevel p n).ring.carrier),
    (res (n + 1)).res.map ((towerHom p n).map a) = (res n).res.map a
  /-- 全レベルで 1 ≠ 0。 -/
  one_ne_zero : ∀ n,
    (towerLevel p n).ring.one ≠ (towerLevel p n).ring.zero
  /-- λₙ は単元でない。 -/
  lam_not_unit : ∀ n v,
    (towerLevel p n).ring.mul (towerLevel p n).lam v
      ≠ (towerLevel p n).ring.one
  /-- πₙ は単元でない。 -/
  pi_not_unit : ∀ n v,
    (towerLevel p n).ring.mul (towerLevel p n).pi v
      ≠ (towerLevel p n).ring.one

/-- **M111-9b: witness**。 -/
def residueTowerData (p : Nat) (hp : 2 ≤ p) : ResidueTowerData p hp where
  res := towerRes p hp
  compat := towerRes_compat p hp
  one_ne_zero := tower_one_ne_zero p hp
  lam_not_unit := tower_lam_not_unit p hp
  pi_not_unit := tower_pi_not_unit p hp

/-- **M111-9c: 存在**。 -/
theorem residueTower_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (ResidueTowerData p hp) :=
  ⟨residueTowerData p hp⟩

end IUT
