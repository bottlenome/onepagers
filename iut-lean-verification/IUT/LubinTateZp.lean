/-
  IUT/LubinTateZp.lean — M42（ℤ_p は Lubin–Tate 消去仮説を満たす）

  M41 の一意性スキーマの消去仮説（(g_1)^n − c の正則性）を係数環
  ℤ_p・c = g_1 = p で**完全証明**し、ℤ_p 上の Lubin–Tate 方程式
  F∘g = p·F + F^q の解の一意性を具体形で確立する。鍵となる分解:

    p^n − p = p · (p^{n−1} − 1)、  p^{n−1} − 1 は単数（≡ −1 mod p）

  により、正則性 = **p-捻れなし性**（成分計算: p·c ≡ 0 mod p^{m+1} ⟹
  c ≡ 0 mod p^m）× **単元の正則性**（M36 の逆元で消去）に帰着する。

  * M42-1 CRing 負元ツールキット — add_neg・neg_eq_of_add_eq_zero・
    mul_neg・neg_mul・neg_neg・neg_add_dist・eq_of_sub_eq_zero（公理ゼロ）
  * M42-2 `CRing.cancel_to_annihilate` — 消去式 a·G + c·b = b·G + c·a
    から **(G − c)·(a − b) = 0** への一般変形
  * M42-3 `rpow_toZp` / `toZp_sub` — toZp と冪・差の両立
  * M42-4 `zp_p_regular` — **ℤ_p の p-捻れなし性**: p·d = 0 ⟹ d = 0
  * M42-5 `zp_unit_regular` — 単数は正則（M36 の明示逆元で消去）
  * M42-6 `zp_lt_cancel` — **ℤ_p は消去仮説を満たす**（n ≥ 2 で
    p^n − p は正則）
  * M42-7 `lubin_tate_unique_zp` — **ℤ_p 上の LT 一意性**（具体形）

  存在側（係数の再帰構成、誤差項の p-整除性）は次段。
  全て選択公理不使用。
-/
import IUT.LubinTateUnique

namespace IUT

/-! ## CRing 負元ツールキット -/

/-- a + (−a) = 0。 -/
theorem CRing.add_neg (R : CRing) (a : R.carrier) :
    R.add a (R.neg a) = R.zero := by
  rw [R.add_comm]
  exact R.neg_add a

/-- a + b = 0 なら −a = b。 -/
theorem CRing.neg_eq_of_add_eq_zero (R : CRing) {a b : R.carrier}
    (h : R.add a b = R.zero) : R.neg a = b := by
  have h1 : R.add (R.neg a) (R.add a b) = R.add (R.neg a) R.zero := by rw [h]
  rw [← R.add_assoc, R.neg_add, R.zero_add, R.add_zero] at h1
  exact h1.symm

/-- x·(−y) = −(x·y)。 -/
theorem CRing.mul_neg (R : CRing) (x y : R.carrier) :
    R.mul x (R.neg y) = R.neg (R.mul x y) := by
  have h : R.add (R.mul x y) (R.mul x (R.neg y)) = R.zero := by
    rw [← R.left_distrib, R.add_neg, R.mul_zero]
  exact (R.neg_eq_of_add_eq_zero h).symm

/-- (−x)·y = −(x·y)。 -/
theorem CRing.neg_mul (R : CRing) (x y : R.carrier) :
    R.mul (R.neg x) y = R.neg (R.mul x y) := by
  rw [R.mul_comm, R.mul_neg, R.mul_comm]

/-- −(−a) = a。 -/
theorem CRing.neg_neg (R : CRing) (a : R.carrier) : R.neg (R.neg a) = a :=
  R.neg_eq_of_add_eq_zero (R.neg_add a)

/-- −(x+y) = (−x) + (−y)。 -/
theorem CRing.neg_add_dist (R : CRing) (x y : R.carrier) :
    R.neg (R.add x y) = R.add (R.neg x) (R.neg y) := by
  apply R.neg_eq_of_add_eq_zero
  rw [R.add_add_add_comm, R.add_neg, R.add_neg, R.zero_add]

/-- a − b = 0 なら a = b。 -/
theorem CRing.eq_of_sub_eq_zero (R : CRing) {a b : R.carrier}
    (h : R.add a (R.neg b) = R.zero) : a = b := by
  have h1 : R.add (R.neg b) a = R.zero := by
    rw [R.add_comm]
    exact h
  have h2 := R.neg_eq_of_add_eq_zero h1
  rw [R.neg_neg] at h2
  exact h2.symm

/-- **定理 (M42-2): 消去式から零化へ** — a·G + c·b = b·G + c·a なら
    (G − c)·(a − b) = 0。 -/
theorem CRing.cancel_to_annihilate (R : CRing) {G c a b : R.carrier}
    (h : R.add (R.mul a G) (R.mul c b) = R.add (R.mul b G) (R.mul c a)) :
    R.mul (R.add G (R.neg c)) (R.add a (R.neg b)) = R.zero := by
  rw [R.right_distrib, R.left_distrib G a (R.neg b),
    R.left_distrib (R.neg c) a (R.neg b),
    R.mul_neg G b, R.neg_mul c a, R.neg_mul c (R.neg b), R.mul_neg c b,
    R.neg_neg, R.mul_comm G a, R.mul_comm G b,
    R.add_comm (R.neg (R.mul c a)) (R.mul c b),
    R.add_add_add_comm (R.mul a G) (R.neg (R.mul b G)) (R.mul c b)
      (R.neg (R.mul c a)),
    ← R.neg_add_dist (R.mul b G) (R.mul c a), h]
  exact R.add_neg _

/-! ## toZp と冪・差の両立 -/

/-- rpow と toZp の両立: (toZp x)^n = toZp (x^n)。 -/
theorem rpow_toZp (p : Nat) (x : Int) : ∀ n,
    rpow (zpRing p) ((toZp p).map x) n = (toZp p).map (ipow x n) := by
  intro n
  induction n with
  | zero => exact ((toZpRing p).map_one).symm
  | succ n ih =>
    show (zpRing p).mul (rpow (zpRing p) ((toZp p).map x) n) ((toZp p).map x)
      = (toZp p).map (ipow x n * x)
    have hmm : (zpRing p).mul ((toZp p).map (ipow x n)) ((toZp p).map x)
        = (toZp p).map (ipow x n * x) :=
      ((toZpRing p).map_mul (ipow x n) x).symm
    rw [ih]
    exact hmm

/-- toZp と差の両立。 -/
theorem toZp_sub (p : Nat) (A B : Int) :
    (zpRing p).add ((toZp p).map A) ((zpRing p).neg ((toZp p).map B))
      = (toZp p).map (A - B) := by
  show (Zp p).mul ((toZp p).map A) ((Zp p).inv ((toZp p).map B))
    = (toZp p).map (A - B)
  rw [← Hom.map_inv (toZp p) B, ← (toZp p).map_mul]
  rfl

/-! ## ℤ_p の正則性 -/

/-- **定理 (M42-4): ℤ_p の p-捻れなし性** — p·d = 0 ⟹ d = 0
    （成分計算: p·c ≡ 0 mod p^{m+1} ⟹ c ≡ 0 mod p^m）。 -/
theorem zp_p_regular (p : Nat) (hp : 2 ≤ p) {d : (Zp p).carrier}
    (h : zpMul p ((toZp p).map ((p : Nat) : Int)) d = (Zp p).one) :
    d = (Zp p).one := by
  apply Subtype.ext
  funext m
  have hm : zmodMul (p ^ (m + 1))
      (Quot.mk (modCong (p ^ (m + 1))).rel ((p : Nat) : Int)) (d.val (m + 1))
      = Quot.mk (modCong (p ^ (m + 1))).rel 0 :=
    congrFun (congrArg Subtype.val h) (m + 1)
  obtain ⟨c, hc⟩ := Quot.exists_rep (d.val (m + 1))
  rw [← hc] at hm
  have hQ : Quot.mk (modCong (p ^ (m + 1))).rel (((p : Nat) : Int) * c)
      = Quot.mk (modCong (p ^ (m + 1))).rel 0 := hm
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (p ^ (m + 1))) hQ
  have hk' : ((p : Nat) : Int) * c = ((p ^ (m + 1) : Nat) : Int) * k := by
    revert hk
    generalize ((p ^ (m + 1) : Nat) : Int) * k = W
    generalize ((p : Nat) : Int) * c = V
    intro hk
    omega
  have he : ((p ^ (m + 1) : Nat) : Int) * k
      = ((p : Nat) : Int) * (((p ^ m : Nat) : Int) * k) := by
    rw [cast_pow_succ, Int.mul_comm ((p ^ m : Nat) : Int) ((p : Nat) : Int),
      Int.mul_assoc]
  rw [he] at hk'
  have hpc : c = ((p ^ m : Nat) : Int) * k :=
    Int.eq_of_mul_eq_mul_left (by omega) hk'
  have hcomp : (zmodTrans (pow_dvd_mono p (Nat.le_succ m))).map (d.val (m + 1))
      = d.val m := d.property (Nat.le_succ m)
  rw [← hc] at hcomp
  rw [← hcomp]
  show Quot.mk (modCong (p ^ m)).rel c = Quot.mk (modCong (p ^ m)).rel 0
  apply Quot.sound
  refine ⟨k, ?_⟩
  rw [hpc]
  generalize ((p ^ m : Nat) : Int) * k = W
  omega

/-- **定理 (M42-5): 単数の正則性** — u 単数、u·d = 0 ⟹ d = 0
    （M36 の明示逆元で消去）。 -/
theorem zp_unit_regular (p : Nat) (hp : IsPrime p) {u d : (Zp p).carrier}
    (hu : IsZpUnit p u) (h : zpMul p u d = (Zp p).one) : d = (Zp p).one := by
  have h1 : zpMul p (zpUnitInv p hp u hu) (zpMul p u d)
      = zpMul p (zpUnitInv p hp u hu) ((Zp p).one) := by rw [h]
  rw [← zpMul_assoc, zpUnitInv_mul p hp u hu, zpOne_mul] at h1
  rw [h1]
  exact CRing.mul_zero (zpRing p) (zpUnitInv p hp u hu)

/-- **定理 (M42-6): ℤ_p は LT 消去仮説を満たす** — n ≥ 2 で
    p^n − p = p·(p^{n−1} − 1) は正則（p-捻れなし × 単数正則）。 -/
theorem zp_lt_cancel (p : Nat) (hp : IsPrime p) : ∀ n a b, 2 ≤ n →
    (zpRing p).add
        ((zpRing p).mul a (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n))
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) b)
      = (zpRing p).add
        ((zpRing p).mul b (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n))
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) a)
    → a = b := by
  intro n a b hn h
  have hann := CRing.cancel_to_annihilate (zpRing p) h
  rw [rpow_toZp p ((p : Nat) : Int) n,
    toZp_sub p (ipow ((p : Nat) : Int) n) ((p : Nat) : Int)] at hann
  obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  subst hm
  have hfac : ipow ((p : Nat) : Int) (m + 2) - ((p : Nat) : Int)
      = ((p : Nat) : Int) * (ipow ((p : Nat) : Int) (m + 1) - 1) := by
    rw [Int.mul_sub, Int.mul_one]
    have he : ((p : Nat) : Int) * ipow ((p : Nat) : Int) (m + 1)
        = ipow ((p : Nat) : Int) (m + 2) := by
      show ((p : Nat) : Int) * ipow ((p : Nat) : Int) (m + 1)
        = ipow ((p : Nat) : Int) (m + 1) * ((p : Nat) : Int)
      exact Int.mul_comm _ _
    rw [he]
  have hmul : (toZp p).map (((p : Nat) : Int) * (ipow ((p : Nat) : Int) (m + 1) - 1))
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1)) :=
    (toZpRing p).map_mul ((p : Nat) : Int) (ipow ((p : Nat) : Int) (m + 1) - 1)
  rw [hfac, hmul, (zpRing p).mul_assoc] at hann
  have h1 : zpMul p ((toZp p).map (ipow ((p : Nat) : Int) (m + 1) - 1))
      ((zpRing p).add a ((zpRing p).neg b)) = (Zp p).one :=
    zp_p_regular p hp.1 hann
  have hU : ¬ ((p : Nat) : Int) ∣ (ipow ((p : Nat) : Int) (m + 1) - 1) := by
    intro hd
    apply not_dvd_one p hp.1
    have hdp : ((p : Nat) : Int) ∣ ipow ((p : Nat) : Int) (m + 1) :=
      ⟨ipow ((p : Nat) : Int) m, by
        show ipow ((p : Nat) : Int) m * ((p : Nat) : Int)
          = ((p : Nat) : Int) * ipow ((p : Nat) : Int) m
        exact Int.mul_comm _ _⟩
    obtain ⟨x, hx⟩ := hdp
    obtain ⟨y, hy⟩ := hd
    refine ⟨x - y, ?_⟩
    rw [Int.mul_sub, ← hx, ← hy]
    generalize ipow ((p : Nat) : Int) (m + 1) = W
    omega
  have h2 : (zpRing p).add a ((zpRing p).neg b) = (Zp p).one :=
    zp_unit_regular p hp ⟨ipow ((p : Nat) : Int) (m + 1) - 1, rfl, hU⟩ h1
  exact CRing.eq_of_sub_eq_zero (zpRing p) h2

/-- **定理 (M42-7): ℤ_p 上の Lubin–Tate 一意性**（具体形）—
    g(0) = 0、g(1) = p、方程式 F∘g = p·F + F^q（q ≥ 2）の解は
    定数項 0 と一次係数で一意。 -/
theorem lubin_tate_unique_zp (p : Nat) (hp : IsPrime p)
    (g : PS (zpRing p)) (hg0 : g 0 = (zpRing p).zero)
    (hg1 : g 1 = (toZp p).map ((p : Nat) : Int))
    (q : Nat) (hq : 2 ≤ q) (F F' : PS (zpRing p))
    (hF0 : F 0 = (zpRing p).zero) (hF'0 : F' 0 = (zpRing p).zero)
    (hF1 : F 1 = F' 1)
    (eF : psComp (zpRing p) F g
      = (psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F)
          (psPow (zpRing p) F q))
    (eF' : psComp (zpRing p) F' g
      = (psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F')
          (psPow (zpRing p) F' q)) :
    F = F' := by
  apply lubin_tate_unique (zpRing p) g hg0 ((toZp p).map ((p : Nat) : Int))
    q hq ?_ F F' hF0 hF'0 hF1 eF eF'
  intro n c d hn h
  rw [hg1] at h
  exact zp_lt_cancel p hp n c d hn h

end IUT
