/-
  IUT/PrincipalUnits.lean — M29（主単数: ℤ_p の乗法構造と幾何級数可逆性）

  局所類体論の分岐側の第一歩。単数群 O^× の構造論は「主単数
  1 + m が（乗法で）群をなし、filtration 1+m ⊃ 1+m² ⊃ … を持つ」
  ことから始まる。その核心を完全証明する:

  * M29-1 `dvd_sub_mul` — 乗法の合同両立（mod N で積が well-defined）
  * M29-2 `zmodMul` / `zpMul` — **ℤ/p^n と ℤ_p の乗法構造**
    （商上の積と、遷移と両立する極限上の成分ごとの積。可換性込み）
  * M29-3 `geom_identity` — 幾何級数恒等式 (1−t)·Σ_{k<n} t^k = 1 − t^n
  * M29-4 `dvd_ipow` — p ∣ t ⟹ p^n ∣ t^n
  * M29-5 `zmod_principal_unit_invertible` — **主単数の可逆性**:
    a ≡ 1 (mod p) なら a は ℤ/p^n で可逆（逆元 = 幾何級数 Σ(1−a)^k）。
    「1 + pℤ_p が乗法群をなす」ことの各有限レベルでの完全証明であり、
    O^× = μ × (1+m) の構造論と LCFT 分岐部の出発点。

  全て選択公理不使用。
-/
import IUT.LocalCFT

namespace IUT

/-- **M29-1: 乗法の合同両立** — N ∣ A−A'、N ∣ B−B' なら
    N ∣ AB−A'B'。 -/
theorem dvd_sub_mul {N A A' B B' : Int} (h1 : N ∣ A - A') (h2 : N ∣ B - B') :
    N ∣ A * B - A' * B' := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  refine ⟨A * l + k * B', ?_⟩
  have e1 : N * (A * l) = A * (B - B') := by
    rw [hl, ← Int.mul_assoc, Int.mul_comm N A, Int.mul_assoc]
  have e2 : N * (k * B') = (A - A') * B' := by
    rw [hk, ← Int.mul_assoc]
  rw [Int.mul_add, e1, e2, Int.mul_sub, Int.sub_mul]
  generalize A * B = P
  generalize A * B' = Q
  generalize A' * B' = R
  omega

/-- **M29-2a: ℤ/n の乗法**（商上の積、well-defined 性込み）。 -/
def zmodMul (n : Nat) (x y : (zmod n).carrier) : (zmod n).carrier :=
  Quot.lift
    (fun a => Quot.lift (fun b => Quot.mk (modCong n).rel (a * b))
      (fun _ _ hb => Quot.sound (dvd_sub_mul (dvd_sub_refl _ a) hb)) y)
    (fun a a' ha => by
      induction y using Quot.ind
      rename_i b
      exact Quot.sound (dvd_sub_mul ha (dvd_sub_refl _ b))) x

/-- ℤ/n の乗法は可換。 -/
theorem zmodMul_comm (n : Nat) (x y : (zmod n).carrier) :
    zmodMul n x y = zmodMul n y x := by
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  show Quot.mk (modCong n).rel (a * b) = Quot.mk (modCong n).rel (b * a)
  rw [Int.mul_comm]

/-- **M29-2b: ℤ_p の乗法**（遷移と両立する成分ごとの積）。
    これにより ℤ_p は（加法群に加えて）乗法構造を持つ。 -/
def zpMul (p : Nat) (x y : (Zp p).carrier) : (Zp p).carrier :=
  ⟨fun n => zmodMul (p ^ n) (x.val n) (y.val n), by
    intro i j h
    have hmul : ∀ (a b : (zmod (p ^ j)).carrier),
        (zmodTrans (pow_dvd_mono p h)).map (zmodMul (p ^ j) a b)
        = zmodMul (p ^ i) ((zmodTrans (pow_dvd_mono p h)).map a)
          ((zmodTrans (pow_dvd_mono p h)).map b) := by
      intro a b
      induction a using Quot.ind; rename_i a'
      induction b using Quot.ind; rename_i b'
      rfl
    show (zmodTrans (pow_dvd_mono p h)).map
        (zmodMul (p ^ j) (x.val j) (y.val j))
      = zmodMul (p ^ i) (x.val i) (y.val i)
    have hx : (zmodTrans (pow_dvd_mono p h)).map (x.val j) = x.val i :=
      x.property h
    have hy : (zmodTrans (pow_dvd_mono p h)).map (y.val j) = y.val i :=
      y.property h
    rw [hmul, hx, hy]⟩

/-- ℤ_p の乗法は可換。 -/
theorem zpMul_comm (p : Nat) (x y : (Zp p).carrier) :
    zpMul p x y = zpMul p y x := by
  apply Subtype.ext
  funext n
  exact zmodMul_comm (p ^ n) (x.val n) (y.val n)

/-! ## 幾何級数による主単数の可逆性 -/

/-- 冪（自前定義、defeq 制御のため）。 -/
def ipow (a : Int) : Nat → Int
  | 0 => 1
  | n + 1 => ipow a n * a

/-- 幾何級数 Σ_{k<n} a^k。 -/
def geomSum (a : Int) : Nat → Int
  | 0 => 0
  | n + 1 => geomSum a n + ipow a n

/-- **M29-3: 幾何級数恒等式** (1−a)·Σ_{k<n} a^k = 1 − a^n。 -/
theorem geom_identity (a : Int) : ∀ n, (1 - a) * geomSum a n = 1 - ipow a n := by
  intro n
  induction n with
  | zero =>
    show (1 - a) * 0 = 1 - 1
    rw [Int.mul_zero]
    omega
  | succ n ih =>
    show (1 - a) * (geomSum a n + ipow a n) = 1 - ipow a n * a
    rw [Int.mul_add, ih, Int.sub_mul, Int.one_mul,
      Int.mul_comm a (ipow a n)]
    generalize ipow a n = T
    generalize T * a = S
    omega

/-- **M29-4**: p ∣ a ⟹ p^n ∣ a^n。 -/
theorem dvd_ipow (p a : Int) (h : p ∣ a) : ∀ n, ipow p n ∣ ipow a n := by
  intro n
  induction n with
  | zero => exact ⟨1, by show (1 : Int) = 1 * 1; omega⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨m, hm⟩ := h
    refine ⟨k * m, ?_⟩
    show ipow a n * a = ipow p n * p * (k * m)
    rw [hk, hm, Int.mul_assoc, ← Int.mul_assoc k p m, Int.mul_comm k p,
      Int.mul_assoc p k m, ← Int.mul_assoc (ipow p n) p (k * m)]

/-- Nat 冪のキャストは ipow に一致。 -/
theorem cast_pow_ipow (p : Nat) : ∀ n, ((p ^ n : Nat) : Int) = ipow ((p : Nat) : Int) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((p ^ n * p : Nat) : Int) = ipow ((p : Nat) : Int) n * ((p : Nat) : Int)
    rw [Int.natCast_mul, ih]

/-- **定理 (M29-5): 主単数の可逆性**（幾何級数）— a ≡ 1 (mod p) なら
    a は ℤ/p^n で可逆（逆元 = Σ_{k<n} (1−a)^k）。「1 + pℤ_p が
    乗法群をなす」ことの各有限レベルでの完全証明。O^× = μ × (1+m)
    構造論と LCFT 分岐部分の出発点。 -/
theorem zmod_principal_unit_invertible (p : Nat) (n : Nat) (a : Int)
    (h : ((p : Nat) : Int) ∣ (1 - a)) :
    ∃ v, zmodMul (p ^ n) (Quot.mk (modCong (p ^ n)).rel a) v
      = Quot.mk (modCong (p ^ n)).rel 1 := by
  refine ⟨Quot.mk (modCong (p ^ n)).rel (geomSum (1 - a) n), ?_⟩
  show Quot.mk (modCong (p ^ n)).rel (a * geomSum (1 - a) n)
      = Quot.mk (modCong (p ^ n)).rel 1
  apply Quot.sound
  -- a·Σ(1−a)^k = 1 − (1−a)^n（恒等式）、p^n ∣ (1−a)^n
  have hid := geom_identity (1 - a) n
  have ha : (1 : Int) - (1 - a) = a := by omega
  rw [ha] at hid
  -- hid : a * geomSum (1−a) n = 1 − ipow (1−a) n
  obtain ⟨c, hc⟩ := dvd_ipow ((p : Nat) : Int) (1 - a) h n
  show ((p ^ n : Nat) : Int) ∣ (a * geomSum (1 - a) n - 1)
  refine ⟨-c, ?_⟩
  rw [cast_pow_ipow, Int.mul_neg, ← hc, hid]
  generalize ipow (1 - a) n = T
  omega

end IUT
