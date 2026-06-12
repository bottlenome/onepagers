/-
  IUT/PrincipalUnitGroup.lean — M30（主単数群: (1 + pℤ_p, ×) の Grp 構成）

  M29 で各有限レベル ℤ/p^n の主単数の可逆性を示した。本モジュールは
  それを逆極限に持ち上げ、**主単数のなす乗法群を実際の `Grp` として
  構成**する。局所類体論の分岐部 O^× = μ × (1+m) の「(1+m)」が
  群であることの完全証明:

  * M30-1 `dvd_sub_ipow` / `dvd_sub_geomSum` — 冪・幾何級数の合同両立
    （逆元写像が商上 well-defined であることの核）
  * M30-2 `geomSum_levels` — **レベル間整合性**: p ∣ t、i ≤ j なら
    p^i ∣ Σ_{k<j} t^k − Σ_{k<i} t^k（ずれは Σ_{i≤k<j} t^k で各項が
    p^i の倍数）。レベルごとの逆元が逆極限の整合族をなす理由
  * M30-3 `IsPrincipalUnit` / `zpOne` — 主単数性（各レベルの代表が
    1 + p·* の形）と ℤ_p の乗法単位元
  * M30-4 `isPrincipalUnit_mul` — 主単数は積で閉じる
    （1 − ab = (1−a) + a(1−b)）
  * M30-5 `zpGeomInv` — **主単数の ℤ_p 逆元**（幾何級数逆元の整合束、
    構成的・選択公理不使用）と、逆元が再び主単数であること
  * M30-6 `principalUnits` — **主単数群 (1 + pℤ_p, ×) : Grp**。
    乗法は zpMul（M29）の制限、群公理は成分ごとの Int 恒等式に還元
  * M30-7 `principal_unit_invertible` — 主単数は ℤ_p の単元
    （zpMul の意味で乗法逆元を持つ）
  * M30-8 `toZp_one_add_principal` — 1 + p·k 型整数の像は主単数
    （「1 + pℤ_p」という名の正当化）

  正直な申告: ここでの「主単数群」は ℤ_p の乗法 zpMul に関する群で
  あり、一般の局所体 O_K^× ではなく K = ℚ_p の場合の構成である。
  全て選択公理不使用。
-/
import IUT.PrincipalUnits

namespace IUT

/-- **M30-1a: 冪の合同両立** — N ∣ A−A' なら N ∣ A^k − A'^k。 -/
theorem dvd_sub_ipow {N A A' : Int} (h : N ∣ A - A') :
    ∀ k, N ∣ ipow A k - ipow A' k := by
  intro k
  induction k with
  | zero => exact dvd_sub_refl _ _
  | succ k ih => exact dvd_sub_mul ih h

/-- **M30-1b: 幾何級数の合同両立** — N ∣ A−A' なら
    N ∣ Σ_{k<n} A^k − Σ_{k<n} A'^k。逆元写像の well-defined 性の核。 -/
theorem dvd_sub_geomSum {N A A' : Int} (h : N ∣ A - A') :
    ∀ k, N ∣ geomSum A k - geomSum A' k := by
  intro k
  induction k with
  | zero => exact dvd_sub_refl _ _
  | succ k ih => exact dvd_sub_add ih (dvd_sub_ipow h k)

/-- 補題: N ∣ A−A' なら N ∣ (1−A) − (1−A')。 -/
theorem dvd_sub_one_sub {N A A' : Int} (h : N ∣ A - A') :
    N ∣ (1 - A) - (1 - A') := by
  obtain ⟨k, hk⟩ := h
  exact ⟨-k, by rw [Int.mul_neg, ← hk]; omega⟩

/-- 補題: P ∣ t なら P ∣ c·t。 -/
theorem dvd_mul_of_dvd {P t : Int} (h : P ∣ t) (c : Int) : P ∣ c * t := by
  obtain ⟨m, hm⟩ := h
  exact ⟨c * m, by rw [hm, ← Int.mul_assoc, Int.mul_comm c P, Int.mul_assoc]⟩

/-- **定理 (M30-2): レベル間整合性** — p ∣ t、i ≤ j なら
    p^i ∣ geomSum t j − geomSum t i。ずれ Σ_{i≤k<j} t^k の各項
    t^k は p^k の倍数で p^i ∣ p^k。逆元の遷移整合性の核。 -/
theorem geomSum_levels (p : Nat) (t : Int) (ht : ((p : Nat) : Int) ∣ t)
    {i j : Nat} (h : i ≤ j) :
    ((p ^ i : Nat) : Int) ∣ geomSum t j - geomSum t i := by
  induction h with
  | refl => exact dvd_sub_refl _ _
  | @step m h' ih =>
    have h1 : ((p ^ i : Nat) : Int) ∣ ipow t m := by
      have hc : ((p ^ i : Nat) : Int) ∣ ((p ^ m : Nat) : Int) :=
        Int.ofNat_dvd.mpr (pow_dvd_mono p h')
      have hd : ((p ^ m : Nat) : Int) ∣ ipow t m := by
        rw [cast_pow_ipow]
        exact dvd_ipow _ t ht m
      exact Int.dvd_trans hc hd
    obtain ⟨k, hk⟩ := ih
    obtain ⟨l, hl⟩ := h1
    refine ⟨k + l, ?_⟩
    show geomSum t m + ipow t m - geomSum t i = ((p ^ i : Nat) : Int) * (k + l)
    rw [Int.mul_add, ← hk, ← hl]
    omega

/-! ## 主単数性と乗法単位元 -/

/-- **M30-3a: 主単数性** — 各レベルの代表が 1 + p·* の形
    （すなわち x ≡ 1 mod p）。 -/
def IsPrincipalUnit (p : Nat) (x : (Zp p).carrier) : Prop :=
  ∀ n, ∃ a : Int, x.val n = Quot.mk (modCong (p ^ n)).rel a ∧
    ((p : Nat) : Int) ∣ (1 - a)

/-- **M30-3b: ℤ_p の乗法単位元** 1（全レベルで Quot.mk 1）。 -/
def zpOne (p : Nat) : (Zp p).carrier :=
  ⟨fun n => Quot.mk (modCong (p ^ n)).rel 1, fun {_ _} _ => rfl⟩

/-- 1 は主単数。 -/
theorem isPrincipalUnit_one (p : Nat) : IsPrincipalUnit p (zpOne p) :=
  fun _ => ⟨1, rfl, ⟨0, by omega⟩⟩

/-- **定理 (M30-4): 主単数は積で閉じる** —
    1 − ab = (1−a) + a(1−b)。 -/
theorem isPrincipalUnit_mul (p : Nat) {x y : (Zp p).carrier}
    (hx : IsPrincipalUnit p x) (hy : IsPrincipalUnit p y) :
    IsPrincipalUnit p (zpMul p x y) := by
  intro n
  obtain ⟨a, ha, hpa⟩ := hx n
  obtain ⟨b, hb, hpb⟩ := hy n
  refine ⟨a * b, ?_, ?_⟩
  · show zmodMul (p ^ n) (x.val n) (y.val n)
      = Quot.mk (modCong (p ^ n)).rel (a * b)
    rw [ha, hb]
    rfl
  · obtain ⟨k, hk⟩ := hpa
    obtain ⟨l, hl⟩ := hpb
    refine ⟨k + a * l, ?_⟩
    rw [Int.mul_add, ← hk]
    have hpal : ((p : Nat) : Int) * (a * l) = a * (1 - b) := by
      rw [hl, ← Int.mul_assoc, Int.mul_comm ((p : Nat) : Int) a, Int.mul_assoc]
    rw [hpal, Int.mul_sub, Int.mul_one]
    generalize a * b = Q
    omega

/-! ## 幾何級数逆元の整合束 -/

/-- **M30-5a: レベルごとの幾何級数逆元写像**（商上 well-defined）。 -/
def zmodGeomInv (p n : Nat) :
    (zmod (p ^ n)).carrier → (zmod (p ^ n)).carrier :=
  Quot.lift (fun a => Quot.mk (modCong (p ^ n)).rel (geomSum (1 - a) n))
    (fun _ _ h => Quot.sound (dvd_sub_geomSum (dvd_sub_one_sub h) n))

/-- **M30-5b: 主単数の ℤ_p 逆元** — レベルごとの幾何級数逆元の整合束。
    遷移整合性は `geomSum_levels`（レベル間のずれが p^i で消える）に
    よる。構成的（選択公理不使用）。 -/
def zpGeomInv (p : Nat) (x : (Zp p).carrier) (hx : IsPrincipalUnit p x) :
    (Zp p).carrier :=
  ⟨fun n => zmodGeomInv p n (x.val n), by
    intro i j h
    obtain ⟨a, ha, hpa⟩ := hx j
    have hcomp : (zmodTrans (pow_dvd_mono p h)).map (x.val j) = x.val i :=
      x.property h
    rw [ha] at hcomp
    show (zmodTrans (pow_dvd_mono p h)).map (zmodGeomInv p j (x.val j))
      = zmodGeomInv p i (x.val i)
    rw [ha, ← hcomp]
    exact Quot.sound (geomSum_levels p (1 - a) hpa h)⟩

/-- P ∣ t なら n ≥ 1 で P ∣ 1 − geomSum t n
    （geomSum t n = 1 + t·(…) なので）。 -/
theorem dvd_one_sub_geomSum {P t : Int} (h : P ∣ t) :
    ∀ n, P ∣ 1 - geomSum t (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨0, by show (1 : Int) - (0 + 1) = P * 0; omega⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨l, hl⟩ := dvd_mul_of_dvd h (ipow t n)
    have hT : P * l = ipow t (n + 1) := hl.symm
    refine ⟨k - l, ?_⟩
    show 1 - (geomSum t (n + 1) + ipow t (n + 1)) = P * (k - l)
    rw [Int.mul_sub, ← hk, hT]
    generalize geomSum t (n + 1) = S
    generalize ipow t (n + 1) = T
    omega

/-- **M30-5c: 逆元は再び主単数** — レベル n ≥ 1 では
    geomSum (1−a) n ≡ 1 (mod p)、レベル 0 は自明群。 -/
theorem isPrincipalUnit_geomInv (p : Nat) (x : (Zp p).carrier)
    (hx : IsPrincipalUnit p x) : IsPrincipalUnit p (zpGeomInv p x hx) := by
  intro n
  cases n with
  | zero =>
    refine ⟨1, ?_, ⟨0, by omega⟩⟩
    show zmodGeomInv p 0 (x.val 0) = Quot.mk (modCong (p ^ 0)).rel 1
    induction x.val 0 using Quot.ind
    rename_i b
    apply Quot.sound
    show ((p ^ 0 : Nat) : Int) ∣ geomSum (1 - b) 0 - 1
    rw [Nat.pow_zero]
    exact Int.one_dvd _
  | succ m =>
    obtain ⟨a, ha, hpa⟩ := hx (m + 1)
    refine ⟨geomSum (1 - a) (m + 1), ?_, dvd_one_sub_geomSum hpa m⟩
    show zmodGeomInv p (m + 1) (x.val (m + 1))
      = Quot.mk (modCong (p ^ (m + 1))).rel (geomSum (1 - a) (m + 1))
    rw [ha]
    rfl

/-! ## 主単数群 -/

/-- **定理 (M30-6): 主単数群** (1 + pℤ_p, ×) — ℤ_p の乗法 zpMul に
    関する群。群公理は成分ごとの Int 恒等式（結合則・単位元）と
    幾何級数恒等式（逆元、M29-5 の計算）に還元される。 -/
def principalUnits (p : Nat) : Grp where
  carrier := { x : (Zp p).carrier // IsPrincipalUnit p x }
  mul := fun x y =>
    ⟨zpMul p x.val y.val, isPrincipalUnit_mul p x.property y.property⟩
  one := ⟨zpOne p, isPrincipalUnit_one p⟩
  inv := fun x =>
    ⟨zpGeomInv p x.val x.property, isPrincipalUnit_geomInv p x.val x.property⟩
  mul_assoc := by
    intro x y z
    apply Subtype.ext
    apply Subtype.ext
    funext n
    show zmodMul (p ^ n)
        (zmodMul (p ^ n) (x.val.val n) (y.val.val n)) (z.val.val n)
      = zmodMul (p ^ n) (x.val.val n)
        (zmodMul (p ^ n) (y.val.val n) (z.val.val n))
    induction x.val.val n using Quot.ind; rename_i a
    induction y.val.val n using Quot.ind; rename_i b
    induction z.val.val n using Quot.ind; rename_i c
    show Quot.mk (modCong (p ^ n)).rel (a * b * c)
      = Quot.mk (modCong (p ^ n)).rel (a * (b * c))
    rw [Int.mul_assoc]
  one_mul := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    funext n
    show zmodMul (p ^ n) (Quot.mk (modCong (p ^ n)).rel 1) (x.val.val n)
      = x.val.val n
    induction x.val.val n using Quot.ind; rename_i a
    show Quot.mk (modCong (p ^ n)).rel (1 * a)
      = Quot.mk (modCong (p ^ n)).rel a
    rw [Int.one_mul]
  inv_mul := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    funext n
    obtain ⟨a, ha, hpa⟩ := x.property n
    show zmodMul (p ^ n) (zmodGeomInv p n (x.val.val n)) (x.val.val n)
      = Quot.mk (modCong (p ^ n)).rel 1
    rw [ha]
    show Quot.mk (modCong (p ^ n)).rel (geomSum (1 - a) n * a)
      = Quot.mk (modCong (p ^ n)).rel 1
    apply Quot.sound
    have hid := geom_identity (1 - a) n
    have ha' : (1 : Int) - (1 - a) = a := by omega
    rw [ha'] at hid
    obtain ⟨c, hc⟩ := dvd_ipow ((p : Nat) : Int) (1 - a) hpa n
    refine ⟨-c, ?_⟩
    show geomSum (1 - a) n * a - 1 = ((p ^ n : Nat) : Int) * (-c)
    rw [Int.mul_comm (geomSum (1 - a) n) a, cast_pow_ipow, Int.mul_neg,
      ← hc, hid]
    generalize ipow (1 - a) n = T
    omega

/-- 主単数群はアーベル群（zpMul の可換性の制限）。 -/
theorem principalUnits_comm (p : Nat) (x y : (principalUnits p).carrier) :
    (principalUnits p).mul x y = (principalUnits p).mul y x := by
  apply Subtype.ext
  exact zpMul_comm p x.val y.val

/-- **定理 (M30-7): 主単数は ℤ_p の単元** — IsPrincipalUnit x なら
    zpMul の意味で乗法逆元を持つ（逆元 = 幾何級数の整合束、構成的）。
    M29-5 の極限への持ち上げ。 -/
theorem principal_unit_invertible (p : Nat) (x : (Zp p).carrier)
    (hx : IsPrincipalUnit p x) :
    ∃ y, zpMul p y x = zpOne p :=
  ⟨zpGeomInv p x hx,
    congrArg Subtype.val ((principalUnits p).inv_mul ⟨x, hx⟩)⟩

/-- **M30-8**: 1 + p·k 型の整数の像は主単数
    （「1 + pℤ_p」という名の正当化）。 -/
theorem toZp_one_add_principal (p : Nat) (k : Int) :
    IsPrincipalUnit p ((toZp p).map (1 + ((p : Nat) : Int) * k)) :=
  fun _ => ⟨1 + ((p : Nat) : Int) * k, rfl,
    ⟨-k, by
      rw [Int.mul_neg]
      generalize ((p : Nat) : Int) * k = q
      omega⟩⟩

end IUT
