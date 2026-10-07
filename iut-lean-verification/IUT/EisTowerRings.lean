/-
  IUT/EisTowerRings.lean — M109（柱B B-1: Λₙ 塔の環骨格を全レベルで構成）

  B-1/B-2 の最後の壁だった **Λₙ(n ≥ 2) の生成元の住処**——次数
  p^{n−1}(p−1) の分岐拡大の塔 O = O₁ ⊆ O₂ ⊆ …——を、
  **一般単項イデアル商環**（M82F の Eisenstein 構成の完全一般化）と
  **一段昇り towerStep** の再帰で全レベル一気に構成する:

    O_{n+1} := O_n[[Y]]/(f_πₙ(Y) − λₙ)、λ_{n+1} := Y mod (…)

  各レベルで **f(λ_{n+1}) = λₙ**（塔の関係式）が witness 1 の即物的な
  イデアル計算で成り立ち、帰納法で **[π^{n+1}]λ_{n+1} = 0**（λ_{n+1} は
  π^{n+1}-捻れ点）が従う。M89F の「塔の生成元 λₙ は未形式化」申告の
  構成部分を全レベルで解消する。

  * M109-1 `QuotIdeal` / `qiAdd` / `qiNeg` / `qiMul` / `quotCRing` —
    **一般単項イデアル商環** S/(E)（M82F の idealRel 両立補題で
    Quot.lift、環法則は代表の法則 + congrArg。全て一般環）
  * M109-2 `quotOf` / `quot_exact_ideal` / `quot_rpow_mk` — 構造射
    S → S/(E)（環準同型）・分離性・冪の交換
  * M109-3 `psSmul_psX` / `rpow_psX` — 小部品（c·X = single c 1・
    X^k = psMono k の一般環版）
  * M109-4 `towerStepPoly` / `towerStep` / `towerStepOf` / `towerLam` —
    **一段昇り**: R ↦ R[[Y]]/(π_R·Y + Y^p − λ_R)
  * M109-5 `ringF` / `ringF_hom` / `towerStep_shape` — 選ばれた π に
    関する LT 多項式作用 f_π(t) = π t + t^p、その環準同型との交換、
    **塔の関係式 f(λ') = ι(λ)**（witness 1 のイデアル計算、無条件）
  * M109-6 `TowerLevel` / `towerLevel` / `towerHom` / `tower_shape` —
    **塔の再帰構成**（towerLevel p n = O_{n+1}、基底 = M82F の O）
  * M109-7 `ringFIter` / `ringFIter_hom` / `tower_torsion` —
    **[π^{n+1}]λ_{n+1} = 0**（基底 = M82F-7 の πλ + λ^p = 0、
    帰納段 = 関係式 + 準同型交換）
  * M109-8 `EisTowerData` — 総括レコードと witness

  未形式化（正直申告）: 塔の各レベルの**非自明性**（O_n ≠ 0・λₙ ≠ 0・
  ι の単射性）は towerStepPoly の Eisenstein 性による係数論法（M83F-6 の
  レベル n 版）が要り次層。[c]-作用・Galois 作用・相互法則の塔への
  持ち上げも次層（M105〜M107 の機構の O_n 版）。
  全て選択公理不使用。
-/
import IUT.RamifiedReciprocity

namespace IUT

/-! ## 一般単項イデアル商環 S/(E) -/

/-- **M109-1a: 商の台**。 -/
def QuotIdeal (S : CRing) (E : S.carrier) := Quot (idealRel S E)

/-- **M109-1b: 加法**（両側の well-definedness は idealRel_add_*）。 -/
def qiAdd (S : CRing) (E : S.carrier) (x y : QuotIdeal S E) : QuotIdeal S E :=
  Quot.lift
    (fun f => Quot.lift
      (fun g => Quot.mk (idealRel S E) (S.add f g))
      (fun _ _ hg => Quot.sound (idealRel_add_left S E f hg)) y)
    (fun _ _ hf => by
      induction y using Quot.ind
      rename_i g
      exact Quot.sound (idealRel_add_right S E g hf)) x

/-- **M109-1c: 反元**。 -/
def qiNeg (S : CRing) (E : S.carrier) (x : QuotIdeal S E) : QuotIdeal S E :=
  Quot.lift (fun f => Quot.mk (idealRel S E) (S.neg f))
    (fun _ _ hf => Quot.sound (idealRel_neg S E hf)) x

/-- **M109-1d: 乗法**。 -/
def qiMul (S : CRing) (E : S.carrier) (x y : QuotIdeal S E) : QuotIdeal S E :=
  Quot.lift
    (fun f => Quot.lift
      (fun g => Quot.mk (idealRel S E) (S.mul f g))
      (fun _ _ hg => Quot.sound (idealRel_mul_left S E f hg)) y)
    (fun _ _ hf => by
      induction y using Quot.ind
      rename_i g
      exact Quot.sound (idealRel_mul_right S E g hf)) x

/-- **定理 (M109-1e): 一般商環** S/(E) は可換環（法則は代表の法則 +
    congrArg、Quot.sound 不要）。 -/
def quotCRing (S : CRing) (E : S.carrier) : CRing where
  carrier := QuotIdeal S E
  add := qiAdd S E
  zero := Quot.mk (idealRel S E) S.zero
  neg := qiNeg S E
  mul := qiMul S E
  one := Quot.mk (idealRel S E) S.one
  add_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    induction z using Quot.ind; rename_i k
    exact congrArg (Quot.mk (idealRel S E)) (S.add_assoc f g k)
  zero_add := by
    intro x
    induction x using Quot.ind; rename_i f
    exact congrArg (Quot.mk (idealRel S E)) (S.zero_add f)
  neg_add := by
    intro x
    induction x using Quot.ind; rename_i f
    exact congrArg (Quot.mk (idealRel S E)) (S.neg_add f)
  add_comm := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    exact congrArg (Quot.mk (idealRel S E)) (S.add_comm f g)
  mul_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    induction z using Quot.ind; rename_i k
    exact congrArg (Quot.mk (idealRel S E)) (S.mul_assoc f g k)
  one_mul := by
    intro x
    induction x using Quot.ind; rename_i f
    exact congrArg (Quot.mk (idealRel S E)) (S.one_mul f)
  mul_comm := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    exact congrArg (Quot.mk (idealRel S E)) (S.mul_comm f g)
  left_distrib := by
    intro x y z
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    induction z using Quot.ind; rename_i k
    exact congrArg (Quot.mk (idealRel S E)) (S.left_distrib f g k)

/-- **M109-2a: 構造射** S → S/(E)（環準同型、成分は Quot.mk）。 -/
def quotOf (S : CRing) (E : S.carrier) : RingHom S (quotCRing S E) where
  map := fun a => Quot.mk (idealRel S E) a
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- **定理 (M109-2b): 分離性** — mk f = mk g なら f ≡ g (mod E)
    （eis_exact の一般化、Prop への Quot.lift）。 -/
theorem quot_exact_ideal (S : CRing) (E : S.carrier) {f g : S.carrier}
    (h : Quot.mk (idealRel S E) f = Quot.mk (idealRel S E) g) :
    idealRel S E f g := by
  have hf : Quot.lift (idealRel S E f)
      (fun _ _ hxy => propext
        ⟨fun hfx => idealRel_trans S E hfx hxy,
         fun hfy => idealRel_trans S E hfy (idealRel_symm S E hxy)⟩)
      (Quot.mk (idealRel S E) f) := idealRel_refl S E f
  rw [h] at hf
  exact hf

/-- **M109-2c: 冪の交換** — 商での冪は代表の冪。 -/
theorem quot_rpow_mk (S : CRing) (E : S.carrier) (f : S.carrier) : ∀ k,
    rpow (quotCRing S E) (Quot.mk (idealRel S E) f) k
      = Quot.mk (idealRel S E) (rpow S f k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (quotCRing S E).mul
        (rpow (quotCRing S E) (Quot.mk (idealRel S E) f) k)
        (Quot.mk (idealRel S E) f)
      = Quot.mk (idealRel S E) (S.mul (rpow S f k) f)
    rw [ih]
    rfl

/-! ## 小部品 -/

/-- **M109-3a**: c·X = single c 1（一般環版）。 -/
theorem psSmul_psX (R : CRing) (c : R.carrier) :
    psSmul R c (psX R) = psSingle R c 1 := by
  funext n
  cases Nat.decEq n 1 with
  | isTrue h =>
    show R.mul c (psX R n) = psSingle R c 1 n
    rw [show psX R n = R.one from if_pos h,
      show psSingle R c 1 n = c from if_pos h]
    exact CRing.mul_one R c
  | isFalse h =>
    show R.mul c (psX R n) = psSingle R c 1 n
    rw [show psX R n = R.zero from if_neg h,
      show psSingle R c 1 n = R.zero from if_neg h]
    exact CRing.mul_zero R c

/-- **M109-3b**: X^k = psMono k（一般環版、eis_rpow_X の一般化）。 -/
theorem rpow_psX (R : CRing) (k : Nat) :
    rpow (psRing R) (psX R) k = psMono R k := by
  rw [← psPow_eq_rpow R (psX R) k,
    show psPow R (psX R) k = psMono R (1 * k) from psMono_pow R 1 k,
    show 1 * k = k from Nat.one_mul k]

/-! ## 一段昇り -/

/-- **M109-4a: 一段の Eisenstein 型多項式** f_π(Y) − λ = π·Y + Y^p − λ。 -/
def towerStepPoly (p : Nat) (R : CRing) (piR lamR : R.carrier) : PS R :=
  psAdd R (psAdd R (psSingle R piR 1) (psMono R p))
    (psNeg R (psC R lamR))

/-- **M109-4b: 一段昇りの環** R[[Y]]/(f_π(Y) − λ)。 -/
def towerStep (p : Nat) (R : CRing) (piR lamR : R.carrier) : CRing :=
  quotCRing (psRing R) (towerStepPoly p R piR lamR)

/-- **M109-4c: 一段昇りの構造射** R → R[[Y]]/(…)（定数注入の商像）。 -/
def towerStepOf (p : Nat) (R : CRing) (piR lamR : R.carrier) :
    RingHom R (towerStep p R piR lamR) :=
  RingHom.comp (psConstHom R) (quotOf (psRing R) (towerStepPoly p R piR lamR))

/-- **M109-4d: 一段昇りの一意化元** λ' = Y mod (…)。 -/
def towerLam (p : Nat) (R : CRing) (piR lamR : R.carrier) :
    (towerStep p R piR lamR).carrier :=
  Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR)) (psX R)

/-! ## LT 多項式作用と塔の関係式 -/

/-- **M109-5a: 選ばれた π に関する LT 作用** f_π(t) = π·t + t^p
    （eisF の一般環版）。 -/
def ringF (p : Nat) (R : CRing) (piR : R.carrier) (t : R.carrier) :
    R.carrier :=
  R.add (R.mul piR t) (rpow R t p)

/-- **M109-5b: f_π は環準同型と交換**（π も運ぶ）。 -/
theorem ringF_hom (p : Nat) {R S : CRing} (φ : RingHom R S)
    (piR : R.carrier) (t : R.carrier) :
    φ.map (ringF p R piR t) = ringF p S (φ.map piR) (φ.map t) := by
  show φ.map (R.add (R.mul piR t) (rpow R t p))
    = S.add (S.mul (φ.map piR) (φ.map t)) (rpow S (φ.map t) p)
  rw [φ.map_add, φ.map_mul, ringHom_rpow φ t p]

/-- **定理 (M109-5c): 塔の関係式** — f_π'(λ') = ι(λ)（π' = ι(π)）。
    witness 1 のイデアル計算: (π·Y + Y^p) − C(λ) = 1·(f_π(Y) − λ)。
    無条件（p にも R にも制約なし）。 -/
theorem towerStep_shape (p : Nat) (R : CRing) (piR lamR : R.carrier) :
    ringF p (towerStep p R piR lamR)
      ((towerStepOf p R piR lamR).map piR)
      (towerLam p R piR lamR)
      = (towerStepOf p R piR lamR).map lamR := by
  -- 冪部分: λ'^p = mk (X^p) = mk (mono p)
  have hpow : rpow (towerStep p R piR lamR) (towerLam p R piR lamR) p
      = Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR))
        (psMono R p) := by
    show rpow (quotCRing (psRing R) (towerStepPoly p R piR lamR))
        (Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR)) (psX R)) p
      = Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR))
        (psMono R p)
    rw [quot_rpow_mk (psRing R) (towerStepPoly p R piR lamR) (psX R) p,
      rpow_psX R p]
  -- 積部分: ι(π)·λ' = mk (C(π)·X) = mk (single π 1)
  have hmul : (towerStep p R piR lamR).mul
      ((towerStepOf p R piR lamR).map piR) (towerLam p R piR lamR)
      = Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR))
        (psSingle R piR 1) := by
    show Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR))
        (psMul R (psC R piR) (psX R))
      = Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR))
        (psSingle R piR 1)
    have h1 : psMul R (psC R piR) (psX R) = psSingle R piR 1 :=
      (psSmul_eq_psC_mul R piR (psX R)).symm.trans (psSmul_psX R piR)
    rw [h1]
  show (towerStep p R piR lamR).add
      ((towerStep p R piR lamR).mul
        ((towerStepOf p R piR lamR).map piR) (towerLam p R piR lamR))
      (rpow (towerStep p R piR lamR) (towerLam p R piR lamR) p)
    = (towerStepOf p R piR lamR).map lamR
  rw [hmul, hpow]
  -- mk (single + mono) = mk (C λ): 差はちょうど towerStepPoly、証人 1
  show Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR))
      (psAdd R (psSingle R piR 1) (psMono R p))
    = Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR))
      (psC R lamR)
  apply Quot.sound
  refine ⟨psOne R, ?_⟩
  have hone : psMul R (psOne R) (towerStepPoly p R piR lamR)
      = towerStepPoly p R piR lamR :=
    (psRing R).one_mul (towerStepPoly p R piR lamR)
  show psAdd R (psAdd R (psSingle R piR 1) (psMono R p))
      (psNeg R (psC R lamR))
    = psMul R (psOne R) (towerStepPoly p R piR lamR)
  rw [hone]
  rfl

/-! ## 塔の再帰構成 -/

/-- **M109-6a: 塔の一段のデータ**（環・π の像・一意化元）。 -/
structure TowerLevel (p : Nat) where
  /-- レベルの環 O_{n+1}。 -/
  ring : CRing
  /-- π の像。 -/
  pi : ring.carrier
  /-- 一意化元 λ_{n+1}。 -/
  lam : ring.carrier

/-- **定理 (M109-6b): 塔の再帰構成** — towerLevel p n = O_{n+1}。
    基底は M82F の O = ℤ_p[[X]]/(X^{p−1} + π)、一段は towerStep。 -/
def towerLevel (p : Nat) : Nat → TowerLevel p
  | 0 =>
    ⟨eisRing p, (eisOf p).map ((toZp p).map ((p : Nat) : Int)), eisLambda p⟩
  | n + 1 =>
    ⟨towerStep p (towerLevel p n).ring (towerLevel p n).pi
        (towerLevel p n).lam,
      (towerStepOf p (towerLevel p n).ring (towerLevel p n).pi
        (towerLevel p n).lam).map (towerLevel p n).pi,
      towerLam p (towerLevel p n).ring (towerLevel p n).pi
        (towerLevel p n).lam⟩

/-- **M109-6c: 塔の推移射** O_{n+1} → O_{n+2}。 -/
def towerHom (p : Nat) (n : Nat) :
    RingHom (towerLevel p n).ring (towerLevel p (n + 1)).ring :=
  towerStepOf p (towerLevel p n).ring (towerLevel p n).pi
    (towerLevel p n).lam

/-- **定理 (M109-6d): 全レベルの塔の関係式** —
    f(λ_{n+2}) = ι(λ_{n+1})（towerStep_shape の instance）。 -/
theorem tower_shape (p : Nat) (n : Nat) :
    ringF p (towerLevel p (n + 1)).ring (towerLevel p (n + 1)).pi
      (towerLevel p (n + 1)).lam
      = (towerHom p n).map (towerLevel p n).lam :=
  towerStep_shape p (towerLevel p n).ring (towerLevel p n).pi
    (towerLevel p n).lam

/-! ## 塔の捻れ関係 -/

/-- **M109-7a: f_π の反復**（内側剥がし、eisIter の一般環版）。 -/
def ringFIter (p : Nat) (R : CRing) (piR : R.carrier) :
    Nat → R.carrier → R.carrier
  | 0, t => t
  | k + 1, t => ringFIter p R piR k (ringF p R piR t)

/-- **M109-7b: 反復は環準同型と交換**。 -/
theorem ringFIter_hom (p : Nat) {R S : CRing} (φ : RingHom R S)
    (piR : R.carrier) : ∀ (k : Nat) (t : R.carrier),
    φ.map (ringFIter p R piR k t)
      = ringFIter p S (φ.map piR) k (φ.map t) := by
  intro k
  induction k with
  | zero => intro t; rfl
  | succ k ih =>
    intro t
    show φ.map (ringFIter p R piR k (ringF p R piR t))
      = ringFIter p S (φ.map piR) k (ringF p S (φ.map piR) (φ.map t))
    rw [ih (ringF p R piR t), ringF_hom p φ piR t]

/-- **基底: f(λ) = 0 in O**（M82F-7 の ringF 形）。 -/
theorem tower_base_torsion (p : Nat) (hp : 2 ≤ p) :
    ringF p (towerLevel p 0).ring (towerLevel p 0).pi (towerLevel p 0).lam
      = (towerLevel p 0).ring.zero :=
  eisOf_lambda_torsion_shape p hp

/-- **定理 (M109-7c): 塔の捻れ関係（本丸）** —
    [π^{n+1}]λ_{n+1} = 0（towerLevel p n の λ は f_π の n+1 回反復で
    消える）。基底 = M82F-7、帰納段 = 塔の関係式 + 準同型交換。 -/
theorem tower_torsion (p : Nat) (hp : 2 ≤ p) : ∀ n,
    ringFIter p (towerLevel p n).ring (towerLevel p n).pi (n + 1)
      (towerLevel p n).lam
      = (towerLevel p n).ring.zero := by
  intro n
  induction n with
  | zero =>
    show ringFIter p (towerLevel p 0).ring (towerLevel p 0).pi 0
        (ringF p (towerLevel p 0).ring (towerLevel p 0).pi
          (towerLevel p 0).lam)
      = (towerLevel p 0).ring.zero
    rw [tower_base_torsion p hp]
    rfl
  | succ n ih =>
    show ringFIter p (towerLevel p (n + 1)).ring (towerLevel p (n + 1)).pi
        (n + 1)
        (ringF p (towerLevel p (n + 1)).ring (towerLevel p (n + 1)).pi
          (towerLevel p (n + 1)).lam)
      = (towerLevel p (n + 1)).ring.zero
    rw [tower_shape p n]
    have h1 : ringFIter p (towerLevel p (n + 1)).ring
        (towerLevel p (n + 1)).pi (n + 1)
        ((towerHom p n).map (towerLevel p n).lam)
        = (towerHom p n).map
          (ringFIter p (towerLevel p n).ring (towerLevel p n).pi (n + 1)
            (towerLevel p n).lam) :=
      (ringFIter_hom p (towerHom p n) (towerLevel p n).pi (n + 1)
        (towerLevel p n).lam).symm
    rw [h1, ih]
    exact RingHom.map_zero (towerHom p n)

/-! ## 総括レコード -/

/-- **M109-8a: 総括** — Λₙ 塔の環骨格。 -/
structure EisTowerData (p : Nat) (hp : 2 ≤ p) where
  /-- 各レベルのデータ（level n = O_{n+1}）。 -/
  level : Nat → TowerLevel p
  /-- 推移射。 -/
  hom : ∀ n, RingHom (level n).ring (level (n + 1)).ring
  /-- 基底は M82F の O。 -/
  base_ring : (level 0).ring = eisRing p
  /-- 塔の関係式 f(λ_{n+2}) = ι(λ_{n+1})。 -/
  shape : ∀ n, ringF p (level (n + 1)).ring (level (n + 1)).pi
    (level (n + 1)).lam = (hom n).map (level n).lam
  /-- 捻れ関係 [π^{n+1}]λ_{n+1} = 0。 -/
  torsion : ∀ n, ringFIter p (level n).ring (level n).pi (n + 1)
    (level n).lam = (level n).ring.zero

/-- **M109-8b: witness**。 -/
def eisTowerData (p : Nat) (hp : 2 ≤ p) : EisTowerData p hp where
  level := towerLevel p
  hom := towerHom p
  base_ring := rfl
  shape := tower_shape p
  torsion := tower_torsion p hp

/-- **M109-8c: 存在**。 -/
theorem eisTower_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (EisTowerData p hp) :=
  ⟨eisTowerData p hp⟩

end IUT
