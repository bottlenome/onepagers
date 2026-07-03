/-
# M168: 実数幾何級数の漸化式と残差恒等式（柱E→C 橋）

M165（実数幾何級数の閉形式 (1 ⊖ r)·s_k ≈ 1 ⊖ r^k）の続き。幾何級数の
標準的な二つの補助恒等式——左漸化式と残差形——を realEq 下で閉じ、
ℝ 上の幾何級数 API を完成させる。

  * M168-1 **`real_geom_rec_left`** — 左漸化式 s_{k+1} ≈ 1 ⊕ r·s_k
    （s_{k+1} = 1 + r + … + r^k = 1 + r·(1 + … + r^{k-1})）
  * M168-2 **`real_geom_residual`** — 残差恒等式
    (1 ⊖ r)·s_k ⊕ r^k ≈ 1（閉形式 M165 の移項形: 部分和に欠けている
    のはちょうど末尾 r^k だけ）
  * M168-3 `RealGeomRecData` — 総括

意義: 左漸化式は幾何級数の帰納的性格を、残差恒等式は「(1⊖r)·s_k が
1 に r^k だけ足りない」ことを明示する。後者は |r| < 1 での収束
s_k → (1 ⊖ r)⁻¹ において**残差が r^k で支配される**ことを述べる直前の
一歩（次層の rate-bound 評価の代数的下地）。

正直な限定: 収束そのもの（r^k → 0 と極限の同定）は次層。本層は
有限 k での realEq 恒等式のみ。

全て選択公理不使用。
-/
import IUT.RealGeom

namespace IUT

/-! ## M168-1: 左漸化式 -/

/-- **定理 (M168-1): 左漸化式** — s_{k+1} ≈ 1 ⊕ r·s_k。
    k の帰納。両辺を共通の中点 1 ⊕ (r·s_k ⊕ r^{k+1}) に寄せる:
    左辺は IH（s_{k+1} ≈ 1 ⊕ r·s_k）の左 congruence + 結合、
    右辺は s_{k+1} の展開 + 実左分配 + rmul_comm。 -/
theorem real_geom_rec_left (r : RReal) (k : Nat) :
    realEq (realGeomSum r (k + 1))
      (realAdd (qToReal ratRing.one) (rmul r (realGeomSum r k))) := by
  induction k with
  | zero =>
    show realEq (realAdd realZero (qToReal ratRing.one))
        (realAdd (qToReal ratRing.one) (rmul r realZero))
    refine realEq_trans
      (realEq_trans (realAdd_comm realZero (qToReal ratRing.one))
        (realAdd_zero (qToReal ratRing.one))) ?_
    exact realEq_symm (realEq_trans
      (realAdd_congr_right (qToReal ratRing.one) (rmul_zero r))
      (realAdd_zero (qToReal ratRing.one)))
  | succ k ih =>
    show realEq (realAdd (realGeomSum r (k + 1)) (realPow r (k + 1)))
        (realAdd (qToReal ratRing.one) (rmul r (realGeomSum r (k + 1))))
    have hL : realEq (realAdd (realGeomSum r (k + 1)) (realPow r (k + 1)))
        (realAdd (qToReal ratRing.one)
          (realAdd (rmul r (realGeomSum r k)) (realPow r (k + 1)))) :=
      realEq_trans (realAdd_congr_left (realPow r (k + 1)) ih)
        (realAdd_assoc (qToReal ratRing.one) (rmul r (realGeomSum r k))
          (realPow r (k + 1)))
    have hR : realEq
        (realAdd (qToReal ratRing.one) (rmul r (realGeomSum r (k + 1))))
        (realAdd (qToReal ratRing.one)
          (realAdd (rmul r (realGeomSum r k)) (realPow r (k + 1)))) :=
      realAdd_congr_right (qToReal ratRing.one)
        (realEq_trans (rmul_add_left (realGeomSum r k) (realPow r k) r)
          (realAdd_congr_right (rmul r (realGeomSum r k))
            (rmul_comm r (realPow r k))))
    exact realEq_trans hL (realEq_symm hR)

/-! ## M168-2: 残差恒等式 -/

/-- **定理 (M168-2): 残差恒等式** — (1 ⊖ r)·s_k ⊕ r^k ≈ 1。
    閉形式 M165（(1 ⊖ r)·s_k ≈ 1 ⊖ r^k）の左 congruence + 結合 +
    (⊖r^k) ⊕ r^k ≈ 0 で 1 ⊕ 0 ≈ 1 に畳む。「部分和に欠けているのは
    末尾 r^k だけ」。 -/
theorem real_geom_residual (r : RReal) (k : Nat) :
    realEq (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realPow r k)) (qToReal ratRing.one) :=
  realEq_trans (realAdd_congr_left (realPow r k) (real_geom_closed r k))
    (realEq_trans
      (realAdd_assoc (qToReal ratRing.one) (realNeg (realPow r k))
        (realPow r k))
      (realEq_trans
        (realAdd_congr_right (qToReal ratRing.one)
          (realEq_trans (realAdd_comm (realNeg (realPow r k)) (realPow r k))
            (realAdd_neg (realPow r k))))
        (realAdd_zero (qToReal ratRing.one))))

/-! ## M168-3: 総括 -/

/-- **M168-3a: 総括** — 実数幾何級数の漸化式・残差データ。 -/
structure RealGeomRecData where
  /-- 左漸化式 s_{k+1} ≈ 1 ⊕ r·s_k。 -/
  rec_left : ∀ (r : RReal) (k : Nat),
    realEq (realGeomSum r (k + 1))
      (realAdd (qToReal ratRing.one) (rmul r (realGeomSum r k)))
  /-- 残差恒等式 (1 ⊖ r)·s_k ⊕ r^k ≈ 1。 -/
  residual : ∀ (r : RReal) (k : Nat),
    realEq (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realPow r k)) (qToReal ratRing.one)

/-- **M168-3b: witness**。 -/
def realGeomRecData : RealGeomRecData where
  rec_left := real_geom_rec_left
  residual := real_geom_residual

/-- **M168-3c: 存在**。 -/
theorem realGeomRec_exists : Nonempty RealGeomRecData := ⟨realGeomRecData⟩

end IUT
