/-
  IUT/LaurentMonomial.lean — M88F（Laurent 単項式計算: 柱E・E4 関数等式の準備部品）

  Laurent 環における **u^c 倍 = 添字シフト** を計算可能な形で確立する。
  テータ級数の関数等式（E4）は u^c 倍を添字の平行移動として読む操作に
  帰着するため、その部品を係数レベル → Quot レベルの順で整備する。

  * M88F-1 `uMon_mul_coeff` — **u^c 倍 = 添字シフト**: 窓 [−|c|, |c|] の
    畳み込み和を一点 i = c に退化させる（rsum_single + toNat 添字計算）
  * M88F-2 `uMon_mul_uMon` — 単項式の指数法則 u^a · u^b = u^{a+b}
    （係数レベル、if 条件の omega 同値変形）
  * M88F-3 `laurent_uMon_mul` / `laurent_uMon_zero` — Quot レベルの
    指数法則と u^0 = 1（mul-on-mk の定義的簡約 + Quot.sound 一発）
  * M88F-4 `uShift` — 添字シフトを原始演算として定義し、
    `uShift_eq_uMon_mul` で u^c 倍と係数一致
  * M88F-5 `uShift_add` / `laurent_uMon_unit` — シフトの加法性と
    **u^c は単元**（Laurent 環の本質: 負冪の可逆性）

  テータ級数の関数等式そのもの・q 方向のシフトは次層。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.LaurentRing

namespace IUT

/-! ## u^c 倍 = 添字シフト（係数レベル） -/

/-- **定理 (M88F-1): u^c 倍 = 添字シフト** — 窓 [−|c|, |c|] の畳み込み和は
    一点 i = c だけが生き残る。 -/
theorem uMon_mul_coeff (R : CRing) (c : Int) (f : LRep R) :
    (lMul R (uMon R c) f).coeff = fun k => f.coeff (k - c) := by
  funext k
  -- 一点窓の添字 t₀: -(|c|) + t₀ = c
  obtain ⟨t₀, ht₀⟩ : ∃ t : Nat, (t : Int) = c + (c.natAbs : Int) :=
    ⟨(c + (c.natAbs : Int)).toNat, Int.toNat_of_nonneg (by omega)⟩
  show rsum R (fun t => R.mul
      (if (-(c.natAbs : Int) + (t : Int)) = c then R.one else R.zero)
      (f.coeff (k - (-(c.natAbs : Int) + (t : Int)))))
      (2 * c.natAbs + 1)
    = f.coeff (k - c)
  refine Eq.trans (rsum_single R (fun t => R.mul
      (if (-(c.natAbs : Int) + (t : Int)) = c then R.one else R.zero)
      (f.coeff (k - (-(c.natAbs : Int) + (t : Int))))) t₀
      (2 * c.natAbs + 1) (by omega)
      (fun j _ hne => by
        show R.mul
            (if (-(c.natAbs : Int) + (j : Int)) = c then R.one else R.zero)
            (f.coeff (k - (-(c.natAbs : Int) + (j : Int)))) = R.zero
        rw [if_neg (show (-(c.natAbs : Int) + (j : Int)) ≠ c by omega)]
        exact R.zero_mul
          (f.coeff (k - (-(c.natAbs : Int) + (j : Int)))))) ?_
  show R.mul
      (if (-(c.natAbs : Int) + (t₀ : Int)) = c then R.one else R.zero)
      (f.coeff (k - (-(c.natAbs : Int) + (t₀ : Int)))) = f.coeff (k - c)
  rw [if_pos (show (-(c.natAbs : Int) + (t₀ : Int)) = c by omega),
    R.one_mul,
    show k - (-(c.natAbs : Int) + (t₀ : Int)) = k - c by omega]

/-- **定理 (M88F-2): 単項式の指数法則**（係数レベル） u^a · u^b = u^{a+b}。 -/
theorem uMon_mul_uMon (R : CRing) (a b : Int) :
    (lMul R (uMon R a) (uMon R b)).coeff = (uMon R (a + b)).coeff := by
  rw [uMon_mul_coeff R a (uMon R b)]
  funext k
  show (if k - a = b then R.one else R.zero)
    = (if k = a + b then R.one else R.zero)
  cases Int.decEq (k - a) b with
  | isTrue h => rw [if_pos h, if_pos (show k = a + b by omega)]
  | isFalse h => rw [if_neg h, if_neg (show k ≠ a + b by omega)]

/-! ## Quot レベルの指数法則 -/

/-- **M88F-3: Quot レベルの指数法則**（mul-on-mk は定義的に簡約）。 -/
theorem laurent_uMon_mul (R : CRing) (a b : Int) :
    (laurentRing R).mul (Quot.mk (laurentRel R) (uMon R a))
        (Quot.mk (laurentRel R) (uMon R b))
      = Quot.mk (laurentRel R) (uMon R (a + b)) :=
  Quot.sound (uMon_mul_uMon R a b)

/-- u^0 = 1（係数は構文的に一致）。 -/
theorem laurent_uMon_zero (R : CRing) :
    Quot.mk (laurentRel R) (uMon R 0) = (laurentRing R).one :=
  Quot.sound (show (uMon R 0).coeff = (lOne R).coeff from rfl)

/-! ## シフトの原始演算化 -/

/-- **M88F-4: 添字シフト**を原始演算として（台の有界性込みで）定義。 -/
def uShift (R : CRing) (c : Int) (f : LRep R) : LRep R where
  coeff := fun k => f.coeff (k - c)
  bnd := f.bnd + c.natAbs
  supp := fun k hk => f.supp (k - c) (by omega)

/-- シフトは u^c 倍と係数一致。 -/
theorem uShift_eq_uMon_mul (R : CRing) (c : Int) (f : LRep R) :
    (uShift R c f).coeff = (lMul R (uMon R c) f).coeff :=
  (uMon_mul_coeff R c f).symm

/-- **M88F-5: シフトの加法性**。 -/
theorem uShift_add (R : CRing) (c d : Int) (f : LRep R) :
    (uShift R c (uShift R d f)).coeff = (uShift R (c + d) f).coeff := by
  funext k
  show f.coeff ((k - c) - d) = f.coeff (k - (c + d))
  rw [show (k - c) - d = k - (c + d) by omega]

/-- **u^c は単元**（Laurent 環の本質: u^c · u^{−c} = 1）。 -/
theorem laurent_uMon_unit (R : CRing) (c : Int) :
    (laurentRing R).mul (Quot.mk (laurentRel R) (uMon R c))
        (Quot.mk (laurentRel R) (uMon R (-c)))
      = (laurentRing R).one :=
  Eq.trans (laurent_uMon_mul R c (-c))
    (Eq.trans
      (congrArg (fun e => Quot.mk (laurentRel R) (uMon R e))
        (show c + -c = 0 by omega))
      (laurent_uMon_zero R))

end IUT
