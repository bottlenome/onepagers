/-
  IUT/LaurentCoeff.lean — M86（Laurent 係数代数: 柱E 第一層・前半）

  柱E（幾何層: テータ関数・Tate 曲線）の土台となる **Laurent 多項式環
  ℤ[u^{±1}]**（一般の可換環 R 上）の係数レベル代数。choice 回避のため
  台の有界性を**データ（bnd : Nat）として持つ**表現 LRep を採り
  （M67F の QDiv 方式）、環としての完成（係数一致による Quot 商 +
  CRing 公理、結合則込み）は次層 M87。

  * M86-1 `wsum` — **窓和** Σ_{t<len} φ(lo + t)（Int 添字の有限和を
    既存 rsum に翻訳する装置）と congr・加法・スカラー
  * M86-2 `wsum_supported` — **窓非依存性**: 台が [−S, S] に収まる
    関数の窓和は、台を覆う任意の窓で一致（右トリム = rsum_pad・
    左トリム = rsum_split + 添字平行移動）
  * M86-3 `LRep` — 有界台表現と演算（加法・反元・1・単項式 u^m・
    定数・**畳み込み積**）の台評価
  * M86-4 `lMul_coeff_window` — 積係数の窓非依存形
  * M86-5 加法系の法則と分配則（係数レベル・窓共有で点ごと）
  * M86-6 `lMul_coeff_comm` — **可換則**（共通窓への拡大 +
    rsum_reflect による反転）

  結合則（共通窓 + 平行移動）・Quot 環化・ℤ 係数の実体化は M87。
  全て選択公理不使用。
-/
import IUT.RamifiedEntrance

namespace IUT

/-! ## 窓和 -/

/-- **M86-1: 窓和** Σ_{t<len} φ(lo + t)。 -/
def wsum (R : CRing) (φ : Int → R.carrier) (lo : Int) (len : Nat) :
    R.carrier :=
  rsum R (fun t => φ (lo + (t : Int))) len

theorem wsum_congr (R : CRing) {φ ψ : Int → R.carrier} (lo : Int)
    (len : Nat) (h : ∀ k : Int, lo ≤ k → k < lo + (len : Int) → φ k = ψ k) :
    wsum R φ lo len = wsum R ψ lo len :=
  rsum_congr R len (fun t ht => h (lo + (t : Int)) (by omega) (by omega))

theorem wsum_zero (R : CRing) (lo : Int) (len : Nat) :
    wsum R (fun _ => R.zero) lo len = R.zero :=
  rsum_const_zero R len

theorem wsum_add (R : CRing) (φ ψ : Int → R.carrier) (lo : Int)
    (len : Nat) :
    wsum R (fun k => R.add (φ k) (ψ k)) lo len
      = R.add (wsum R φ lo len) (wsum R ψ lo len) :=
  rsum_add R (fun t => φ (lo + (t : Int))) (fun t => ψ (lo + (t : Int)))
    len

/-- **定理 (M86-2): 窓非依存性** — 台が [−S, S] に収まるなら、
    それを覆う任意の窓での和は正準窓 [−S, S] での和に一致。 -/
theorem wsum_supported (R : CRing) (φ : Int → R.carrier) (S : Nat)
    (hφ : ∀ k : Int, S < k.natAbs → φ k = R.zero)
    (lo : Int) (len : Nat)
    (hlo : lo ≤ -(S : Int)) (hhi : (S : Int) < lo + (len : Int)) :
    wsum R φ lo len = wsum R φ (-(S : Int)) (2 * S + 1) := by
  -- 左トリム量 d と右の正味長 2S+1
  obtain ⟨d, hd⟩ : ∃ d : Nat, (d : Int) = -(S : Int) - lo :=
    ⟨(-(S : Int) - lo).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hlen : len = d + (2 * S + 1) + (len - d - (2 * S + 1)) := by omega
  -- 右トリム: 長さを d + (2S+1) に
  have htrimR : wsum R φ lo len = wsum R φ lo (d + (2 * S + 1)) :=
    rsum_pad R (fun t => φ (lo + (t : Int))) (by omega)
      (fun m hm => by
        show φ (lo + (m : Int)) = R.zero
        exact hφ (lo + (m : Int)) (by omega))
  -- 左トリム: 先頭 d 項は台の左外
  have hsplit := rsum_split R (fun t => φ (lo + (t : Int))) d (2 * S + 1)
  have hzero : rsum R (fun t => φ (lo + (t : Int))) d = R.zero := by
    have hz : rsum R (fun t => φ (lo + (t : Int))) d
        = rsum R (fun _ => R.zero) d :=
      rsum_congr R d (fun t ht => hφ (lo + (t : Int)) (by omega))
    rw [hz]
    exact rsum_const_zero R d
  have hshift : rsum R (fun t => φ (lo + ((d + t : Nat) : Int)))
      (2 * S + 1)
      = wsum R φ (-(S : Int)) (2 * S + 1) :=
    rsum_congr R (2 * S + 1) (fun t _ => by
      show φ (lo + ((d + t : Nat) : Int)) = φ (-(S : Int) + (t : Int))
      rw [show lo + ((d + t : Nat) : Int) = -(S : Int) + (t : Int) from by
        rw [Int.natCast_add]
        omega])
  rw [htrimR]
  show rsum R (fun t => φ (lo + (t : Int))) (d + (2 * S + 1))
    = wsum R φ (-(S : Int)) (2 * S + 1)
  rw [hsplit, hzero, R.zero_add]
  exact hshift

/-! ## 有界台表現と演算 -/

/-- **M86-3: 有界台 Laurent 表現**（台の有界性をデータで持つ =
    choice 回避、M67F 方式）。 -/
structure LRep (R : CRing) where
  coeff : Int → R.carrier
  bnd : Nat
  supp : ∀ k : Int, bnd < k.natAbs → coeff k = R.zero

def lAdd (R : CRing) (f g : LRep R) : LRep R where
  coeff := fun k => R.add (f.coeff k) (g.coeff k)
  bnd := max f.bnd g.bnd
  supp := fun k hk => by
    rw [f.supp k (by omega), g.supp k (by omega)]
    exact R.zero_add R.zero

def lNeg (R : CRing) (f : LRep R) : LRep R where
  coeff := fun k => R.neg (f.coeff k)
  bnd := f.bnd
  supp := fun k hk => by
    rw [f.supp k hk]
    exact (CRing.add_zero R (R.neg R.zero)).symm.trans (R.neg_add R.zero)

def lZero (R : CRing) : LRep R where
  coeff := fun _ => R.zero
  bnd := 0
  supp := fun _ _ => rfl

def lOne (R : CRing) : LRep R where
  coeff := fun k => if k = 0 then R.one else R.zero
  bnd := 0
  supp := fun k hk => if_neg (show k ≠ 0 by omega)

/-- 単項式 u^m（m : Int — 負冪も込み）。 -/
def uMon (R : CRing) (m : Int) : LRep R where
  coeff := fun k => if k = m then R.one else R.zero
  bnd := m.natAbs
  supp := fun k hk => if_neg (show k ≠ m by omega)

/-- 定数の埋め込み。 -/
def lConst (R : CRing) (c : R.carrier) : LRep R where
  coeff := fun k => if k = 0 then c else R.zero
  bnd := 0
  supp := fun k hk => if_neg (show k ≠ 0 by omega)

/-- **畳み込み積**（窓 = 左因子の台）。 -/
def lMul (R : CRing) (f g : LRep R) : LRep R where
  coeff := fun k => wsum R (fun i => R.mul (f.coeff i) (g.coeff (k - i)))
    (-(f.bnd : Int)) (2 * f.bnd + 1)
  bnd := f.bnd + g.bnd
  supp := fun k hk => by
    show wsum R (fun i => R.mul (f.coeff i) (g.coeff (k - i)))
      (-(f.bnd : Int)) (2 * f.bnd + 1) = R.zero
    have hz : wsum R (fun i => R.mul (f.coeff i) (g.coeff (k - i)))
        (-(f.bnd : Int)) (2 * f.bnd + 1)
        = wsum R (fun _ => R.zero) (-(f.bnd : Int)) (2 * f.bnd + 1) :=
      wsum_congr R (-(f.bnd : Int)) (2 * f.bnd + 1) (fun i hi₁ hi₂ => by
        rw [g.supp (k - i) (by omega)]
        exact R.mul_zero (f.coeff i))
    rw [hz]
    exact wsum_zero R (-(f.bnd : Int)) (2 * f.bnd + 1)

/-- **M86-4: 積係数の窓非依存形** — 左因子の台を覆う任意の窓でよい。 -/
theorem lMul_coeff_window (R : CRing) (f g : LRep R) (k : Int)
    (lo : Int) (len : Nat)
    (hlo : lo ≤ -((f.bnd : Nat) : Int))
    (hhi : ((f.bnd : Nat) : Int) < lo + (len : Int)) :
    (lMul R f g).coeff k
      = wsum R (fun i => R.mul (f.coeff i) (g.coeff (k - i))) lo len := by
  show wsum R (fun i => R.mul (f.coeff i) (g.coeff (k - i)))
      (-(f.bnd : Int)) (2 * f.bnd + 1) = _
  exact (wsum_supported R (fun i => R.mul (f.coeff i) (g.coeff (k - i)))
    f.bnd
    (fun i hi => by
      show R.mul (f.coeff i) (g.coeff (k - i)) = R.zero
      rw [f.supp i hi]
      exact R.zero_mul (g.coeff (k - i)))
    lo len hlo hhi).symm

/-! ## 加法系の法則と分配則（係数レベル） -/

theorem lAdd_coeff_assoc (R : CRing) (f g h : LRep R) :
    (lAdd R (lAdd R f g) h).coeff = (lAdd R f (lAdd R g h)).coeff := by
  funext k
  exact R.add_assoc (f.coeff k) (g.coeff k) (h.coeff k)

theorem lAdd_coeff_comm (R : CRing) (f g : LRep R) :
    (lAdd R f g).coeff = (lAdd R g f).coeff := by
  funext k
  exact R.add_comm (f.coeff k) (g.coeff k)

theorem lAdd_coeff_zero (R : CRing) (f : LRep R) :
    (lAdd R (lZero R) f).coeff = f.coeff := by
  funext k
  exact R.zero_add (f.coeff k)

theorem lAdd_coeff_neg (R : CRing) (f : LRep R) :
    (lAdd R (lNeg R f) f).coeff = (lZero R).coeff := by
  funext k
  exact R.neg_add (f.coeff k)

/-- **M86-5: 分配則**（左因子の窓を共有するので点ごと）。 -/
theorem lMul_coeff_distrib (R : CRing) (f g h : LRep R) :
    (lMul R f (lAdd R g h)).coeff
      = (lAdd R (lMul R f g) (lMul R f h)).coeff := by
  funext k
  show wsum R (fun i => R.mul (f.coeff i)
      (R.add (g.coeff (k - i)) (h.coeff (k - i))))
      (-(f.bnd : Int)) (2 * f.bnd + 1)
    = R.add
        (wsum R (fun i => R.mul (f.coeff i) (g.coeff (k - i)))
          (-(f.bnd : Int)) (2 * f.bnd + 1))
        (wsum R (fun i => R.mul (f.coeff i) (h.coeff (k - i)))
          (-(f.bnd : Int)) (2 * f.bnd + 1))
  have hc : wsum R (fun i => R.mul (f.coeff i)
      (R.add (g.coeff (k - i)) (h.coeff (k - i))))
      (-(f.bnd : Int)) (2 * f.bnd + 1)
      = wsum R (fun i => R.add
          (R.mul (f.coeff i) (g.coeff (k - i)))
          (R.mul (f.coeff i) (h.coeff (k - i))))
          (-(f.bnd : Int)) (2 * f.bnd + 1) :=
    wsum_congr R (-(f.bnd : Int)) (2 * f.bnd + 1) (fun i _ _ =>
      R.left_distrib (f.coeff i) (g.coeff (k - i)) (h.coeff (k - i)))
  rw [hc]
  exact wsum_add R (fun i => R.mul (f.coeff i) (g.coeff (k - i)))
    (fun i => R.mul (f.coeff i) (h.coeff (k - i)))
    (-(f.bnd : Int)) (2 * f.bnd + 1)

/-! ## 可換則 -/

/-- **定理 (M86-6): 畳み込みの可換則**（係数レベル） — 共通窓
    B = f.bnd + g.bnd + |k| + 1 への拡大と rsum_reflect の反転。 -/
theorem lMul_coeff_comm (R : CRing) (f g : LRep R) :
    (lMul R f g).coeff = (lMul R g f).coeff := by
  funext k
  -- 共通の余裕つき窓
  have hL := lMul_coeff_window R f g k
    (-(((f.bnd + g.bnd + k.natAbs + 1 : Nat)) : Int))
    (2 * (f.bnd + g.bnd + k.natAbs + 1) + 1)
    (by omega) (by omega)
  have hR := lMul_coeff_window R g f k
    (k - ((f.bnd + g.bnd + k.natAbs + 1 : Nat) : Int))
    (2 * (f.bnd + g.bnd + k.natAbs + 1) + 1)
    (by omega) (by omega)
  rw [hL, hR]
  -- 反転 t ↦ 2B − t（rsum_reflect）で両窓が一致
  show rsum R (fun t =>
      R.mul (f.coeff (-(((f.bnd + g.bnd + k.natAbs + 1 : Nat)) : Int)
          + (t : Int)))
        (g.coeff (k - (-(((f.bnd + g.bnd + k.natAbs + 1 : Nat)) : Int)
          + (t : Int)))))
      (2 * (f.bnd + g.bnd + k.natAbs + 1) + 1)
    = rsum R (fun t =>
        R.mul (g.coeff (k - ((f.bnd + g.bnd + k.natAbs + 1 : Nat) : Int)
            + (t : Int)))
          (f.coeff (k - (k - ((f.bnd + g.bnd + k.natAbs + 1 : Nat) : Int)
            + (t : Int)))))
      (2 * (f.bnd + g.bnd + k.natAbs + 1) + 1)
  rw [rsum_reflect R (2 * (f.bnd + g.bnd + k.natAbs + 1)) (fun t =>
    R.mul (f.coeff (-(((f.bnd + g.bnd + k.natAbs + 1 : Nat)) : Int)
        + (t : Int)))
      (g.coeff (k - (-(((f.bnd + g.bnd + k.natAbs + 1 : Nat)) : Int)
        + (t : Int)))))]
  refine rsum_congr R (2 * (f.bnd + g.bnd + k.natAbs + 1) + 1)
    (fun t ht => ?_)
  show R.mul
      (f.coeff (-(((f.bnd + g.bnd + k.natAbs + 1 : Nat)) : Int)
        + ((2 * (f.bnd + g.bnd + k.natAbs + 1) - t : Nat) : Int)))
      (g.coeff (k - (-(((f.bnd + g.bnd + k.natAbs + 1 : Nat)) : Int)
        + ((2 * (f.bnd + g.bnd + k.natAbs + 1) - t : Nat) : Int))))
    = R.mul
        (g.coeff (k - ((f.bnd + g.bnd + k.natAbs + 1 : Nat) : Int)
          + (t : Int)))
        (f.coeff (k - (k - ((f.bnd + g.bnd + k.natAbs + 1 : Nat) : Int)
          + (t : Int))))
  rw [show (-(((f.bnd + g.bnd + k.natAbs + 1 : Nat)) : Int)
        + ((2 * (f.bnd + g.bnd + k.natAbs + 1) - t : Nat) : Int))
      = k - (k - ((f.bnd + g.bnd + k.natAbs + 1 : Nat) : Int)
          + (t : Int)) from by omega]
  rw [show k - (k - (k - ((f.bnd + g.bnd + k.natAbs + 1 : Nat) : Int)
        + (t : Int)))
      = k - ((f.bnd + g.bnd + k.natAbs + 1 : Nat) : Int) + (t : Int)
      from by omega]
  exact R.mul_comm _ _

end IUT
