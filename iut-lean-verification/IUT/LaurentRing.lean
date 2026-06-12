/-
  IUT/LaurentRing.lean — M87（Laurent 環の完成: 柱E 第一層後半）

  M86 の係数代数を完成させ、**Laurent 多項式環 laurentRing R : CRing**
  を係数一致による Quot 商で建設する。

  * M87-1 `wsum_mul_left/right` / `wsum_shift` — 窓和のスカラーと
    平行移動（添字付け替えの装置）
  * M87-2 `lMul_coeff_assoc` — **畳み込みの結合則（本丸）**:
    余裕つき共通窓 B = f+g+h+|k|+1 への拡大・h-因子の押し込み・
    s↔i 交換・f-因子の括り出し・|i| > f.bnd は両辺 0・
    |i| ≤ f.bnd は平行移動 + 窓非依存性で (g·h)-係数の定義窓に着地
  * M87-3 `lMul_coeff_one` — 単位法則（一点窓の評価）
  * M87-4 `lMul_coeff_congr_left/right` — 係数一致は積で保たれる
    （Quot の well-definedness 用、左は共通窓化）
  * M87-5 `laurentRing R : CRing` — **Quot 環化**: 演算は二重
    Quot.lift、**環公理は全て Quot.sound（係数恒等式）一発**

  q-級数環 L[[q]] = psRing (laurentRing R)（E2 — 既存 PS 理論の
  無償取得）とテータ級数（E3）は次層。全て選択公理不使用。
-/
import IUT.LaurentCoeff

namespace IUT

/-! ## 窓和のスカラーと平行移動 -/

theorem wsum_mul_left (R : CRing) (φ : Int → R.carrier) (c : R.carrier)
    (lo : Int) (len : Nat) :
    R.mul c (wsum R φ lo len) = wsum R (fun k => R.mul c (φ k)) lo len :=
  rsum_mul_left R (fun t => φ (lo + (t : Int))) c len

theorem wsum_mul_right (R : CRing) (φ : Int → R.carrier) (c : R.carrier)
    (lo : Int) (len : Nat) :
    R.mul (wsum R φ lo len) c = wsum R (fun k => R.mul (φ k) c) lo len :=
  rsum_mul_right R (fun t => φ (lo + (t : Int))) c len

/-- **M87-1: 平行移動** — 窓を c だけずらす。 -/
theorem wsum_shift (R : CRing) (φ : Int → R.carrier) (lo : Int)
    (len : Nat) (c : Int) :
    wsum R φ lo len = wsum R (fun k => φ (k + c)) (lo - c) len :=
  rsum_congr R len (fun t _ => by
    show φ (lo + (t : Int)) = φ ((lo - c + (t : Int)) + c)
    rw [show (lo - c + (t : Int)) + c = lo + (t : Int) by omega])

/-! ## 結合則 -/

/-- **定理 (M87-2): 畳み込みの結合則（本丸）**。 -/
theorem lMul_coeff_assoc (R : CRing) (f g h : LRep R) :
    (lMul R (lMul R f g) h).coeff = (lMul R f (lMul R g h)).coeff := by
  funext k
  obtain ⟨B, hB⟩ : ∃ B : Nat, B = f.bnd + g.bnd + h.bnd + k.natAbs + 1 :=
    ⟨_, rfl⟩
  rw [lMul_coeff_window R (lMul R f g) h k (-(B : Int)) (2 * B + 1)
      (show (-(B : Int)) ≤ -(((f.bnd + g.bnd : Nat)) : Int) by omega)
      (show (((f.bnd + g.bnd : Nat)) : Int)
        < -(B : Int) + ((2 * B + 1 : Nat) : Int) by omega),
    lMul_coeff_window R f (lMul R g h) k (-(B : Int)) (2 * B + 1)
      (show (-(B : Int)) ≤ -((f.bnd : Nat) : Int) by omega)
      (show ((f.bnd : Nat) : Int)
        < -(B : Int) + ((2 * B + 1 : Nat) : Int) by omega)]
  -- 左辺: 内側展開 + h の押し込み
  have hexp : wsum R (fun s =>
      R.mul ((lMul R f g).coeff s) (h.coeff (k - s)))
      (-(B : Int)) (2 * B + 1)
      = wsum R (fun s => wsum R (fun i =>
          R.mul (f.coeff i) (R.mul (g.coeff (s - i)) (h.coeff (k - s))))
          (-(B : Int)) (2 * B + 1)) (-(B : Int)) (2 * B + 1) :=
    wsum_congr R (-(B : Int)) (2 * B + 1) (fun s _ _ => by
      rw [lMul_coeff_window R f g s (-(B : Int)) (2 * B + 1)
          (show (-(B : Int)) ≤ -((f.bnd : Nat) : Int) by omega)
          (show ((f.bnd : Nat) : Int)
            < -(B : Int) + ((2 * B + 1 : Nat) : Int) by omega),
        wsum_mul_right R (fun i => R.mul (f.coeff i) (g.coeff (s - i)))
          (h.coeff (k - s)) (-(B : Int)) (2 * B + 1)]
      exact wsum_congr R (-(B : Int)) (2 * B + 1) (fun i _ _ => by
        show R.mul (R.mul (f.coeff i) (g.coeff (s - i)))
            (h.coeff (k - s))
          = R.mul (f.coeff i) (R.mul (g.coeff (s - i)) (h.coeff (k - s)))
        exact R.mul_assoc (f.coeff i) (g.coeff (s - i))
          (h.coeff (k - s))))
  rw [hexp]
  -- s ↔ i 交換
  have hx : wsum R (fun s => wsum R (fun i =>
        R.mul (f.coeff i) (R.mul (g.coeff (s - i)) (h.coeff (k - s))))
        (-(B : Int)) (2 * B + 1)) (-(B : Int)) (2 * B + 1)
      = wsum R (fun i => wsum R (fun s =>
          R.mul (f.coeff i) (R.mul (g.coeff (s - i)) (h.coeff (k - s))))
          (-(B : Int)) (2 * B + 1)) (-(B : Int)) (2 * B + 1) :=
    rsum_exchange R (fun t₁ t₂ =>
      R.mul (f.coeff (-(B : Int) + (t₂ : Int)))
        (R.mul (g.coeff ((-(B : Int) + (t₁ : Int))
            - (-(B : Int) + (t₂ : Int))))
          (h.coeff (k - (-(B : Int) + (t₁ : Int))))))
      (2 * B + 1) (2 * B + 1)
  rw [hx]
  -- 各 i: f を括り出して場合分け
  refine wsum_congr R (-(B : Int)) (2 * B + 1) (fun i _ _ => ?_)
  refine Eq.trans ((wsum_mul_left R (fun s =>
      R.mul (g.coeff (s - i)) (h.coeff (k - s)))
      (f.coeff i) (-(B : Int)) (2 * B + 1)).symm) ?_
  show R.mul (f.coeff i) (wsum R (fun s =>
      R.mul (g.coeff (s - i)) (h.coeff (k - s)))
      (-(B : Int)) (2 * B + 1))
    = R.mul (f.coeff i) ((lMul R g h).coeff (k - i))
  cases Nat.lt_or_ge f.bnd i.natAbs with
  | inl hbig =>
    rw [f.supp i hbig, R.zero_mul, R.zero_mul]
  | inr hsmall =>
    refine congrArg (R.mul (f.coeff i)) ?_
    refine Eq.trans (wsum_shift R (fun s =>
      R.mul (g.coeff (s - i)) (h.coeff (k - s)))
      (-(B : Int)) (2 * B + 1) i) ?_
    refine Eq.trans (wsum_congr R (-(B : Int) - i) (2 * B + 1)
      (fun t _ _ => by
        show R.mul (g.coeff ((t + i) - i)) (h.coeff (k - (t + i)))
          = R.mul (g.coeff t) (h.coeff ((k - i) - t))
        rw [show (t + i) - i = t by omega,
          show k - (t + i) = (k - i) - t by omega])) ?_
    exact (wsum_supported R (fun t =>
        R.mul (g.coeff t) (h.coeff ((k - i) - t))) g.bnd
      (fun t ht => by
        show R.mul (g.coeff t) (h.coeff ((k - i) - t)) = R.zero
        rw [g.supp t ht]
        exact R.zero_mul _)
      (-(B : Int) - i) (2 * B + 1) (by omega) (by omega))

/-! ## 単位法則と係数一致の保存 -/

/-- **M87-3: 単位法則**（一点窓の評価）。 -/
theorem lMul_coeff_one (R : CRing) (f : LRep R) :
    (lMul R (lOne R) f).coeff = f.coeff := by
  funext k
  show R.add R.zero
      (R.mul R.one (f.coeff (k - (-((0 : Nat) : Int) + ((0 : Nat) : Int)))))
    = f.coeff k
  rw [R.zero_add, R.one_mul,
    show k - (-((0 : Nat) : Int) + ((0 : Nat) : Int)) = k by omega]

theorem lMul_coeff_congr_right (R : CRing) (f g g' : LRep R)
    (hg : g.coeff = g'.coeff) :
    (lMul R f g).coeff = (lMul R f g').coeff := by
  funext k
  show wsum R (fun i => R.mul (f.coeff i) (g.coeff (k - i)))
      (-(f.bnd : Int)) (2 * f.bnd + 1)
    = wsum R (fun i => R.mul (f.coeff i) (g'.coeff (k - i)))
        (-(f.bnd : Int)) (2 * f.bnd + 1)
  exact wsum_congr R (-(f.bnd : Int)) (2 * f.bnd + 1) (fun i _ _ => by
    show R.mul (f.coeff i) (g.coeff (k - i))
      = R.mul (f.coeff i) (g'.coeff (k - i))
    rw [hg])

theorem lMul_coeff_congr_left (R : CRing) (f f' g : LRep R)
    (hf : f.coeff = f'.coeff) :
    (lMul R f g).coeff = (lMul R f' g).coeff := by
  funext k
  obtain ⟨M, hM⟩ : ∃ M : Nat, M = f.bnd + f'.bnd + 1 := ⟨_, rfl⟩
  rw [lMul_coeff_window R f g k (-(M : Int)) (2 * M + 1)
      (show (-(M : Int)) ≤ -((f.bnd : Nat) : Int) by omega)
      (show ((f.bnd : Nat) : Int)
        < -(M : Int) + ((2 * M + 1 : Nat) : Int) by omega),
    lMul_coeff_window R f' g k (-(M : Int)) (2 * M + 1)
      (show (-(M : Int)) ≤ -((f'.bnd : Nat) : Int) by omega)
      (show ((f'.bnd : Nat) : Int)
        < -(M : Int) + ((2 * M + 1 : Nat) : Int) by omega)]
  exact wsum_congr R (-(M : Int)) (2 * M + 1) (fun i _ _ => by
    show R.mul (f.coeff i) (g.coeff (k - i))
      = R.mul (f'.coeff i) (g.coeff (k - i))
    rw [hf])

/-! ## Quot 環化 -/

def laurentRel (R : CRing) (f g : LRep R) : Prop := f.coeff = g.coeff

def lauAdd (R : CRing) :
    Quot (laurentRel R) → Quot (laurentRel R) → Quot (laurentRel R) :=
  Quot.lift (fun f => Quot.lift
      (fun g => Quot.mk (laurentRel R) (lAdd R f g))
      (fun g g' hg => Quot.sound (show (lAdd R f g).coeff
          = (lAdd R f g').coeff by
        funext k
        show R.add (f.coeff k) (g.coeff k)
          = R.add (f.coeff k) (g'.coeff k)
        rw [hg])))
    (fun f f' hf => by
      funext q
      induction q using Quot.ind
      rename_i g
      exact Quot.sound (show (lAdd R f g).coeff = (lAdd R f' g).coeff by
        funext k
        show R.add (f.coeff k) (g.coeff k)
          = R.add (f'.coeff k) (g.coeff k)
        rw [hf]))

def lauNeg (R : CRing) : Quot (laurentRel R) → Quot (laurentRel R) :=
  Quot.lift (fun f => Quot.mk (laurentRel R) (lNeg R f))
    (fun f f' hf => Quot.sound (show (lNeg R f).coeff
        = (lNeg R f').coeff by
      funext k
      show R.neg (f.coeff k) = R.neg (f'.coeff k)
      rw [hf]))

def lauMul (R : CRing) :
    Quot (laurentRel R) → Quot (laurentRel R) → Quot (laurentRel R) :=
  Quot.lift (fun f => Quot.lift
      (fun g => Quot.mk (laurentRel R) (lMul R f g))
      (fun g g' hg =>
        Quot.sound (lMul_coeff_congr_right R f g g' hg)))
    (fun f f' hf => by
      funext q
      induction q using Quot.ind
      rename_i g
      exact Quot.sound (lMul_coeff_congr_left R f f' g hf))

/-- **定理 (M87-5): Laurent 多項式環**（環公理は全て Quot.sound 一発）。 -/
def laurentRing (R : CRing) : CRing where
  carrier := Quot (laurentRel R)
  add := lauAdd R
  zero := Quot.mk (laurentRel R) (lZero R)
  neg := lauNeg R
  mul := lauMul R
  one := Quot.mk (laurentRel R) (lOne R)
  add_assoc := by
    intro a b c
    induction a using Quot.ind
    induction b using Quot.ind
    induction c using Quot.ind
    exact Quot.sound (lAdd_coeff_assoc R _ _ _)
  zero_add := by
    intro a
    induction a using Quot.ind
    exact Quot.sound (lAdd_coeff_zero R _)
  neg_add := by
    intro a
    induction a using Quot.ind
    exact Quot.sound (lAdd_coeff_neg R _)
  add_comm := by
    intro a b
    induction a using Quot.ind
    induction b using Quot.ind
    exact Quot.sound (lAdd_coeff_comm R _ _)
  mul_assoc := by
    intro a b c
    induction a using Quot.ind
    induction b using Quot.ind
    induction c using Quot.ind
    exact Quot.sound (lMul_coeff_assoc R _ _ _)
  one_mul := by
    intro a
    induction a using Quot.ind
    exact Quot.sound (lMul_coeff_one R _)
  mul_comm := by
    intro a b
    induction a using Quot.ind
    induction b using Quot.ind
    exact Quot.sound (lMul_coeff_comm R _ _)
  left_distrib := by
    intro a b c
    induction a using Quot.ind
    induction b using Quot.ind
    induction c using Quot.ind
    exact Quot.sound (lMul_coeff_distrib R _ _ _)

/-- 構造射 R → R[u^{±1}]（定数の埋め込み、環準同型）。 -/
def laurentOf (R : CRing) : RingHom R (laurentRing R) where
  map := fun c => Quot.mk (laurentRel R) (lConst R c)
  map_add := fun a b => Quot.sound (show (lConst R (R.add a b)).coeff
      = (lAdd R (lConst R a) (lConst R b)).coeff by
    funext k
    show (if k = 0 then R.add a b else R.zero)
      = R.add (if k = 0 then a else R.zero)
          (if k = 0 then b else R.zero)
    cases Nat.decEq k.natAbs 0 with
    | isTrue hk =>
      rw [if_pos (show k = 0 by omega), if_pos (show k = 0 by omega),
        if_pos (show k = 0 by omega)]
    | isFalse hk =>
      rw [if_neg (show k ≠ 0 by omega), if_neg (show k ≠ 0 by omega),
        if_neg (show k ≠ 0 by omega)]
      exact (R.zero_add R.zero).symm)
  map_mul := fun a b => Quot.sound (show (lConst R (R.mul a b)).coeff
      = (lMul R (lConst R a) (lConst R b)).coeff by
    funext k
    show (if k = 0 then R.mul a b else R.zero)
      = R.add R.zero
          (R.mul (if ((-((0 : Nat) : Int) + ((0 : Nat) : Int)) = 0)
            then a else R.zero)
            (if (k - (-((0 : Nat) : Int) + ((0 : Nat) : Int))) = 0
              then b else R.zero))
    rw [R.zero_add,
      if_pos (show (-((0 : Nat) : Int) + ((0 : Nat) : Int)) = 0 by omega),
      show k - (-((0 : Nat) : Int) + ((0 : Nat) : Int)) = k by omega]
    cases Nat.decEq k.natAbs 0 with
    | isTrue hk =>
      rw [if_pos (show k = 0 by omega), if_pos (show k = 0 by omega)]
    | isFalse hk =>
      rw [if_neg (show k ≠ 0 by omega), if_neg (show k ≠ 0 by omega)]
      exact (R.mul_zero a).symm)
  map_one := Quot.sound (show (lConst R R.one).coeff
      = (lOne R).coeff from rfl)

end IUT
