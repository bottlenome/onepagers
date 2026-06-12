/-
  IUT/LTErrorDivisible.lean — M48（Lubin–Tate 誤差項の p-整除性: 第十一層）

  LT 多項式 f = pX + X^p に対し、**任意の** F で誤差項

    E(F) := (p·F + F^p) − F∘f   （f∘F の展開形と合成形の差）

  の全係数が p で割れることを完全証明する。証明は mod-p 還元
  Φ := psMap (projRing p 1) : PS(ℤ_p) → PS(ℤ/p) による一撃:

    Φ(p·F) = 0（標数）、Φ(F^p) = Φ(F)^p、Φ(F∘f) = Φ(F)∘X^p（f̄ = X^p）

  であり、**M47 の Frobenius 定理 Φ(F)^p = Φ(F)∘X^p がちょうど両者の
  一致を与える**。係数の p-整除性は M43 の level-1 判定で witness 付き
  （zpDivP）に具体化される。

  * M48-1 `RingHom.map_neg` / psMap の neg・single・mono・smul 保存
  * M48-2 `ltPoly` — **LT 多項式 f = p·X + X^p** とその係数
    （f₀ = 0・f₁ = p、M49 の方程式インターフェース用）
  * M48-3 `proj_p_zero` / `ltPoly_reduction` — **mod p で f ≡ X^p**
  * M48-4 `ltError_reduction` — **Φ(E(F)) = 0**（Frobenius 定理の適用）
  * M48-5 `ltError_divisible` — **各係数の p-整除性**（∃ witness、
    構成的には zpDivP）

  残り: 係数の再帰構成（存在定理）。全て選択公理不使用。
-/
import IUT.FrobeniusCharP

namespace IUT

/-! ## psMap の追加保存則 -/

/-- 環準同型は負元を保つ。 -/
theorem RingHom.map_neg {R S : CRing} (φ : RingHom R S) (x : R.carrier) :
    φ.map (R.neg x) = S.neg (φ.map x) := by
  have h : S.add (φ.map x) (φ.map (R.neg x)) = S.zero := by
    rw [← φ.map_add, CRing.add_neg R x, φ.map_zero]
  exact (S.neg_eq_of_add_eq_zero h).symm

/-- psMap は負元を保つ。 -/
theorem psMap_neg {R S : CRing} (φ : RingHom R S) (P : PS R) :
    psMap φ (psNeg R P) = psNeg S (psMap φ P) := by
  funext n
  exact φ.map_neg (P n)

/-- psMap は単項式 c·X^m を保つ。 -/
theorem psMap_single {R S : CRing} (φ : RingHom R S) (c : R.carrier) (m : Nat) :
    psMap φ (psSingle R c m) = psSingle S (φ.map c) m := by
  funext n
  show φ.map (psSingle R c m n) = psSingle S (φ.map c) m n
  cases Nat.decEq n m with
  | isTrue he =>
    rw [show psSingle R c m n = c from if_pos he,
      show psSingle S (φ.map c) m n = φ.map c from if_pos he]
  | isFalse he =>
    rw [show psSingle R c m n = R.zero from if_neg he,
      show psSingle S (φ.map c) m n = S.zero from if_neg he]
    exact φ.map_zero

/-- psMap は X^m を保つ。 -/
theorem psMap_mono {R S : CRing} (φ : RingHom R S) (m : Nat) :
    psMap φ (psMono R m) = psMono S m := by
  funext n
  show φ.map (psMono R m n) = psMono S m n
  cases Nat.decEq n m with
  | isTrue he =>
    rw [show psMono R m n = R.one from if_pos he,
      show psMono S m n = S.one from if_pos he]
    exact φ.map_one
  | isFalse he =>
    rw [show psMono R m n = R.zero from if_neg he,
      show psMono S m n = S.zero from if_neg he]
    exact φ.map_zero

/-- psMap はスカラー倍を保つ。 -/
theorem psMap_smul {R S : CRing} (φ : RingHom R S) (c : R.carrier) (F : PS R) :
    psMap φ (psSmul R c F) = psSmul S (φ.map c) (psMap φ F) := by
  funext n
  exact φ.map_mul c (F n)

/-- 係数 0 の単項式は零級数。 -/
theorem psSingle_zero_coeff (R : CRing) (m : Nat) :
    psSingle R R.zero m = psZero R := by
  funext n
  cases Nat.decEq n m with
  | isTrue he => exact if_pos he
  | isFalse he => exact if_neg he

/-- 0 によるスカラー倍は零級数。 -/
theorem psSmul_zero (R : CRing) (G : PS R) : psSmul R R.zero G = psZero R := by
  funext n
  exact R.zero_mul (G n)

/-- 零級数は加法単位元（左）。 -/
theorem psAdd_zero_left (R : CRing) (Q : PS R) : psAdd R (psZero R) Q = Q := by
  funext n
  exact R.zero_add (Q n)

/-! ## LT 多項式とその mod-p 還元 -/

/-- **M48-2: Lubin–Tate 多項式** f = p·X + X^p。 -/
def ltPoly (p : Nat) : PS (zpRing p) :=
  psAdd (zpRing p) (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1)
    (psMono (zpRing p) p)

/-- f の定数項は 0。 -/
theorem ltPoly_coeff_zero (p : Nat) (hp : 2 ≤ p) :
    ltPoly p 0 = (zpRing p).zero := by
  show (zpRing p).add (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1 0)
      (psMono (zpRing p) p 0) = (zpRing p).zero
  rw [show psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1 0
      = (zpRing p).zero from if_neg (by omega),
    show psMono (zpRing p) p 0 = (zpRing p).zero from if_neg (by omega),
    (zpRing p).zero_add]

/-- f の一次係数は p。 -/
theorem ltPoly_coeff_one (p : Nat) (hp : 2 ≤ p) :
    ltPoly p 1 = (toZp p).map ((p : Nat) : Int) := by
  show (zpRing p).add (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1 1)
      (psMono (zpRing p) p 1) = (toZp p).map ((p : Nat) : Int)
  rw [show psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1 1
      = (toZp p).map ((p : Nat) : Int) from if_pos rfl,
    show psMono (zpRing p) p 1 = (zpRing p).zero from if_neg (by omega),
    (zpRing p).add_zero]

/-- **M48-3a**: p の mod-p 像は 0（レベル 1 射影）。 -/
theorem proj_p_zero (p : Nat) :
    (projRing p 1).map ((toZp p).map ((p : Nat) : Int))
      = (zmodRing (p ^ 1)).zero := by
  show Quot.mk (modCong (p ^ 1)).rel ((p : Nat) : Int)
    = Quot.mk (modCong (p ^ 1)).rel 0
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ ((p : Nat) : Int) - 0
  rw [Nat.pow_one]
  exact ⟨1, by omega⟩

/-- **定理 (M48-3b): mod p で f ≡ X^p** — LT 多項式の還元。 -/
theorem ltPoly_reduction (p : Nat) :
    psMap (projRing p 1) (ltPoly p) = psMono (zmodRing (p ^ 1)) p := by
  show psMap (projRing p 1)
      (psAdd (zpRing p) (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1)
        (psMono (zpRing p) p)) = psMono (zmodRing (p ^ 1)) p
  rw [psMap_add (projRing p 1) _ _,
    psMap_single (projRing p 1) ((toZp p).map ((p : Nat) : Int)) 1,
    psMap_mono (projRing p 1) p, proj_p_zero p, psSingle_zero_coeff,
    psAdd_zero_left]

/-! ## 誤差項の消滅と p-整除性 -/

/-- **定理 (M48-4): 誤差項の mod-p 消滅** —
    Φ((p·F + F^p) − F∘f) = 0。Φ(p·F) = 0（標数）、Φ(F^p) = Φ(F)^p、
    Φ(F∘f) = Φ(F)∘X^p で、**M47 の Frobenius 定理**が両者を同一視する。 -/
theorem ltError_reduction (p : Nat) (hp : IsPrime p) (F : PS (zpRing p)) :
    psMap (projRing p 1)
      (psAdd (zpRing p)
        (psAdd (zpRing p)
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F)
          (psPow (zpRing p) F p))
        (psNeg (zpRing p) (psComp (zpRing p) F (ltPoly p))))
      = psZero (zmodRing (p ^ 1)) := by
  rw [psMap_add (projRing p 1)
      (psAdd (zpRing p)
        (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F)
        (psPow (zpRing p) F p))
      (psNeg (zpRing p) (psComp (zpRing p) F (ltPoly p))),
    psMap_add (projRing p 1)
      (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F)
      (psPow (zpRing p) F p),
    psMap_neg (projRing p 1) (psComp (zpRing p) F (ltPoly p)),
    psMap_smul (projRing p 1) ((toZp p).map ((p : Nat) : Int)) F,
    psMap_pow (projRing p 1) F p,
    psMap_comp (projRing p 1) F (ltPoly p),
    proj_p_zero p, psSmul_zero, ltPoly_reduction p,
    frobenius_charp p hp (psMap (projRing p 1) F),
    psAdd_zero_left]
  exact CRing.add_neg (psRing (zmodRing (p ^ 1))) _

/-- **定理 (M48-5): LT 誤差項の p-整除性** — 任意の F・任意の係数 n で
    ((p·F + F^p) − F∘f)_n は p で割れる（witness は構成的には
    M43 の zpDivP）。LT 存在定理の係数構成を可能にする鍵。 -/
theorem ltError_divisible (p : Nat) (hp : IsPrime p) (F : PS (zpRing p))
    (n : Nat) :
    ∃ e, psAdd (zpRing p)
        (psAdd (zpRing p)
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F)
          (psPow (zpRing p) F p))
        (psNeg (zpRing p) (psComp (zpRing p) F (ltPoly p))) n
      = zpMul p ((toZp p).map ((p : Nat) : Int)) e := by
  apply (zp_dvd_p_iff p hp.1 _).mpr
  exact congrFun (ltError_reduction p hp F) n

end IUT
