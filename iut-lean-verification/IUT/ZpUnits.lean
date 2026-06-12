/-
  IUT/ZpUnits.lean — M36（単数群 ℤ_p^× の Grp 構成）

  局所体 ℚ_p の単数群 O^× = ℤ_p^× を**実際の `Grp` として構成**する。
  ℚ_p^× = p^ℤ × ℤ_p^×（M27 の unitsModel の実体化）と分岐相互法則の
  土台。逆元の構成が核心で、

    x^{−1} = x^{p−2} · (x^{p−1})^{−1}

  と取る: x^{p−1} は古典形 Fermat（M34）によりレベル 1 で ≡ 1、
  よって M35 のレベル 1 判定で**主単数**となり、M30 の幾何級数逆元
  zpGeomInv が適用できる。代表元の抽出（= 選択公理）を完全に回避した
  構成である。

  * M36-1 `IsZpUnit` / `not_dvd_one` / `not_dvd_ipow` — 単数性
    （レベル 1 の剰余が p と素）と基本補題
  * M36-2 `isZpUnit_mul` / `isZpUnit_teich` / `isZpUnit_of_principal` —
    積閉性（Euclid の補題）・Teichmüller 代表は単数・主単数は単数
  * M36-3 `unit_pow_principal` — **x^{p−1} は主単数**（古典形 Fermat +
    レベル 1 判定）。逆元構成の鍵
  * M36-4 `zpUnitInv` / `zpUnitInv_mul` — **逆元の明示構成**
    x^{p−2}·(x^{p−1})^{−1} とその左逆元性
  * M36-5 `zpUnits` — **単数群 ℤ_p^× : Grp**（アーベル群、
    群法則は全て M35 までの既証明に帰着）
  * M36-6 `zpUnits_decomposition` — 単数群の元の **μ × U^(1) 分解**
    （M35 の存在定理のパッケージング）

  未形式化: ℚ_p^× = p^ℤ × ℤ_p^× の明示同型・Lubin–Tate・分岐相互法則。
  全て選択公理不使用。
-/
import IUT.UnitDecomposition

namespace IUT

/-! ## 単数性と基本補題 -/

/-- **M36-1a: ℤ_p の単数性** — レベル 1 の剰余が p と素。 -/
def IsZpUnit (p : Nat) (x : (Zp p).carrier) : Prop :=
  ∃ a : Int, x.val 1 = Quot.mk (modCong (p ^ 1)).rel a ∧
    ¬ ((p : Nat) : Int) ∣ a

/-- p ≥ 2 は 1 を割らない（Int 版）。 -/
theorem not_dvd_one (p : Nat) (hp : 2 ≤ p) : ¬ ((p : Nat) : Int) ∣ (1 : Int) := by
  intro h
  have h1 : ((p : Nat) : Int).natAbs ∣ ((1 : Int)).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_natCast] at h1
  have h2 : p ∣ 1 := h1
  have := Nat.le_of_dvd (by omega) h2
  omega

/-- p ∤ a なら p ∤ a^k（Euclid の補題の反復）。 -/
theorem not_dvd_ipow (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) : ∀ k, ¬ ((p : Nat) : Int) ∣ ipow a k := by
  intro k
  induction k with
  | zero =>
    intro h
    have h' : ((p : Nat) : Int) ∣ (1 : Int) := h
    exact not_dvd_one p hp.1 h'
  | succ k ih =>
    intro h
    exact ha (euclid_int p hp h ih)

/-! ## 単数性の閉性 -/

/-- **M36-2a: 単数は積で閉じる**（Euclid の補題）。 -/
theorem isZpUnit_mul (p : Nat) (hp : IsPrime p) {x y : (Zp p).carrier}
    (hx : IsZpUnit p x) (hy : IsZpUnit p y) : IsZpUnit p (zpMul p x y) := by
  obtain ⟨a, ha, hpa⟩ := hx
  obtain ⟨b, hb, hpb⟩ := hy
  refine ⟨a * b, ?_, ?_⟩
  · show zmodMul (p ^ 1) (x.val 1) (y.val 1)
      = Quot.mk (modCong (p ^ 1)).rel (a * b)
    rw [ha, hb]
    rfl
  · intro hab
    exact hpb (euclid_int p hp hab hpa)

/-- **M36-2b: Teichmüller 代表は単数**（剰余の復元 M33-7 から即座）。 -/
theorem isZpUnit_teich (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) : IsZpUnit p (teich p hp a) :=
  ⟨a, teich_reduction p hp a, ha⟩

/-- **M36-2c: 主単数は単数**（c ≡ 1 mod p なら p ∤ c）。 -/
theorem isZpUnit_of_principal (p : Nat) (hp : IsPrime p) {x : (Zp p).carrier}
    (hx : IsPrincipalUnit p x) : IsZpUnit p x := by
  obtain ⟨c, hc, hpc⟩ := hx 1
  refine ⟨c, hc, ?_⟩
  intro hdc
  apply not_dvd_one p hp.1
  obtain ⟨u, hu⟩ := hpc
  obtain ⟨v, hv⟩ := hdc
  refine ⟨u + v, ?_⟩
  rw [Int.mul_add, ← hu, ← hv]
  omega

/-! ## 逆元の明示構成 -/

/-- **定理 (M36-3): x^{p−1} は主単数** — 古典形 Fermat（M34-3）と
    レベル 1 判定（M35-2）から。逆元構成の鍵。 -/
theorem unit_pow_principal (p : Nat) (hp : IsPrime p) (x : (Zp p).carrier)
    (hx : IsZpUnit p x) : IsPrincipalUnit p (zpPow p x (p - 1)) := by
  apply isPrincipalUnit_of_level_one
  obtain ⟨a, ha, hpa⟩ := hx
  show zmodPow (p ^ 1) (x.val 1) (p - 1) = Quot.mk (modCong (p ^ 1)).rel 1
  rw [ha]
  show Quot.mk (modCong (p ^ 1)).rel (ipow a (p - 1))
    = Quot.mk (modCong (p ^ 1)).rel 1
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ ipow a (p - 1) - 1
  rw [Nat.pow_one]
  exact flt_unit p hp hpa

/-- **M36-4a: 単数の逆元** x^{−1} = x^{p−2}·(x^{p−1})^{−1} —
    幾何級数逆元（M30）の適用。代表元の抽出なし（選択公理回避）。 -/
def zpUnitInv (p : Nat) (hp : IsPrime p) (x : (Zp p).carrier)
    (hx : IsZpUnit p x) : (Zp p).carrier :=
  zpMul p (zpPow p x (p - 2))
    (zpGeomInv p (zpPow p x (p - 1)) (unit_pow_principal p hp x hx))

/-- **定理 (M36-4b): 左逆元性** — x^{−1}·x = 1
    （x^{p−2}·g·x = g·x^{p−1} = 1、g = (x^{p−1})^{−1}）。 -/
theorem zpUnitInv_mul (p : Nat) (hp : IsPrime p) (x : (Zp p).carrier)
    (hx : IsZpUnit p x) : zpMul p (zpUnitInv p hp x hx) x = zpOne p := by
  show zpMul p (zpMul p (zpPow p x (p - 2))
      (zpGeomInv p (zpPow p x (p - 1)) (unit_pow_principal p hp x hx))) x
    = zpOne p
  rw [zpMul_comm p (zpPow p x (p - 2))
      (zpGeomInv p (zpPow p x (p - 1)) (unit_pow_principal p hp x hx)),
    zpMul_assoc, ← zpPow_succ]
  have h2 : p - 2 + 1 = p - 1 := by have := hp.1; omega
  rw [h2]
  exact congrArg Subtype.val
    ((principalUnits p).inv_mul ⟨zpPow p x (p - 1), unit_pow_principal p hp x hx⟩)

/-- 逆元は単数（レベル 1 の代表 = a^{p−2}·(幾何級数) で
    幾何級数部はレベル 1 で値 1）。 -/
theorem isZpUnit_inv (p : Nat) (hp : IsPrime p) (x : (Zp p).carrier)
    (hx : IsZpUnit p x) : IsZpUnit p (zpUnitInv p hp x hx) := by
  obtain ⟨a, ha, hpa⟩ := hx
  refine ⟨ipow a (p - 2), ?_, not_dvd_ipow p hp hpa (p - 2)⟩
  show zmodMul (p ^ 1) (zmodPow (p ^ 1) (x.val 1) (p - 2))
      (zmodGeomInv p 1 (zmodPow (p ^ 1) (x.val 1) (p - 1)))
    = Quot.mk (modCong (p ^ 1)).rel (ipow a (p - 2))
  rw [ha]
  show Quot.mk (modCong (p ^ 1)).rel
      (ipow a (p - 2) * geomSum (1 - ipow a (p - 1)) 1)
    = Quot.mk (modCong (p ^ 1)).rel (ipow a (p - 2))
  have hg : geomSum (1 - ipow a (p - 1)) 1 = 1 := by
    show (0 : Int) + 1 = 1
    omega
  rw [hg, Int.mul_one]

/-! ## 単数群 ℤ_p^× -/

/-- **定理 (M36-5): 単数群 ℤ_p^× : Grp** — 群法則は全て M35 までの
    既証明（結合則・単位元・Euler/Fermat 系逆元）に帰着する。 -/
def zpUnits (p : Nat) (hp : IsPrime p) : Grp where
  carrier := { x : (Zp p).carrier // IsZpUnit p x }
  mul := fun x y => ⟨zpMul p x.val y.val, isZpUnit_mul p hp x.property y.property⟩
  one := ⟨zpOne p, ⟨1, rfl, not_dvd_one p hp.1⟩⟩
  inv := fun x => ⟨zpUnitInv p hp x.val x.property, isZpUnit_inv p hp x.val x.property⟩
  mul_assoc := by
    intro x y z
    apply Subtype.ext
    exact zpMul_assoc p x.val y.val z.val
  one_mul := by
    intro x
    apply Subtype.ext
    exact zpOne_mul p x.val
  inv_mul := by
    intro x
    apply Subtype.ext
    exact zpUnitInv_mul p hp x.val x.property

/-- ℤ_p^× はアーベル群。 -/
theorem zpUnits_comm (p : Nat) (hp : IsPrime p) (x y : (zpUnits p hp).carrier) :
    (zpUnits p hp).mul x y = (zpUnits p hp).mul y x := by
  apply Subtype.ext
  exact zpMul_comm p x.val y.val

/-- **定理 (M36-6): 単数群の μ × U^(1) 分解** — ℤ_p^× の任意の元は
    Teichmüller 代表と主単数の積（M35 の存在定理のパッケージング、
    一意性は M35-5）。 -/
theorem zpUnits_decomposition (p : Nat) (hp : IsPrime p)
    (x : (zpUnits p hp).carrier) :
    ∃ (a : Int) (u : (Zp p).carrier), ¬ ((p : Nat) : Int) ∣ a ∧
      IsPrincipalUnit p u ∧ x.val = zpMul p (teich p hp a) u := by
  obtain ⟨a, ha, hpa⟩ := x.property
  obtain ⟨u, hu, hxu⟩ := unit_decomposition p hp x.val hpa ha
  exact ⟨a, u, hpa, hu, hxu⟩

end IUT
