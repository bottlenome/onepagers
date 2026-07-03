/-
# M165: 幾何級数の実数版 — realEq 下での閉形式（柱E→C 橋）

M163（任意可換環での幾何級数の閉形式 (1−r)·s_k = 1−r^k）を**自前 ℝ の
土俵へ移設**する。RReal は CRing ではなく realEq 商上の構造なので、
閉形式は「厳密な等式」ではなく **realEq 下の等式**として、実数乗法代数
（M123F 可換・M150 結合分配・M153F 負号引き出し）の congruence 連鎖で
閉じる。

  * M165-1 `realPow` / `realGeomSum` — 実数の冪と部分和の再帰定義
  * M165-2 `real_add_cancel_middle` — realEq 版相殺補題
    (a ⊕ (⊖b)) ⊕ (b ⊕ d) ≈ a ⊕ d
  * M165-3 **`real_geom_closed`（本丸）** — realEq 下の閉形式
    (1 ⊖ r)·s_k ≈ 1 ⊖ r^k。k の帰納 + 実分配 + 相殺
  * M165-4 `RealGeomData` — 総括

意義: M163 の代数核が実数の realEq 構造でも成立することを確認し、
**幾何級数の閉形式が ℝ の土俵に乗った**。これは |r| < 1 での収束
s_k → (1 ⊖ r)⁻¹（残差 (⊖r^k)·(1 ⊖ r)⁻¹）を論じる直前の一歩であり、
テータ級数・log-volume の収束論の実数側入口。

正直な限定: 本層は**有限部分和の realEq 恒等式のみ**。極限 s_k の
Cauchy 性と (1 ⊖ r)⁻¹ への収束（rate-bound master + |r| < 1 =
IsPos(1 ⊖ rabs r) 前提）は次層。M163 と同じく「収束」ではなく
「閉形式」までである点を過大主張しない。

全て選択公理不使用。
-/
import IUT.RealRingLaws
import IUT.ApartInv
import IUT.RealOrder

namespace IUT

/-! ## M165-1: 実数の冪と部分和 -/

/-- **M165-1a: 実数の冪** — r^k を rmul の反復で（r^0 = 1、
    r^{k+1} = r^k · r）。 -/
def realPow (r : RReal) : Nat → RReal
  | 0 => qToReal ratRing.one
  | k + 1 => rmul (realPow r k) r

/-- **M165-1b: 実数の幾何部分和** — s_k = Σ_{i<k} r^i
    （s_0 = 0、s_{k+1} = s_k ⊕ r^k）。 -/
def realGeomSum (r : RReal) : Nat → RReal
  | 0 => realZero
  | k + 1 => realAdd (realGeomSum r k) (realPow r k)

/-! ## M165-2: realEq 版相殺補題 -/

/-- **補題 (M165-2): realEq 相殺** — (a ⊕ (⊖b)) ⊕ (b ⊕ d) ≈ a ⊕ d。
    結合 + (⊖b) ⊕ b ≈ 0 + 0 ⊕ d ≈ d の congruence 連鎖。 -/
theorem real_add_cancel_middle (a b d : RReal) :
    realEq (realAdd (realAdd a (realNeg b)) (realAdd b d)) (realAdd a d) :=
  realEq_trans (realAdd_assoc a (realNeg b) (realAdd b d))
    (realEq_trans
      (realAdd_congr_right a (realEq_symm (realAdd_assoc (realNeg b) b d)))
      (realEq_trans
        (realAdd_congr_right a (realAdd_congr_left d
          (realEq_trans (realAdd_comm (realNeg b) b) (realAdd_neg b))))
        (realAdd_congr_right a
          (realEq_trans (realAdd_comm realZero d) (realAdd_zero d)))))

/-! ## M165-3: 本丸 — realEq 下の閉形式 -/

/-- **定理 (M165-3, 本丸): 実数幾何級数の閉形式** —
    (1 ⊖ r)·s_k ≈ 1 ⊖ r^k（realEq 下）。k = 0 は両辺 ≈ 0
    （rmul_zero・realAdd_neg）。k+1 は実分配 rmul_add_left で
    (1⊖r)·(s_k ⊕ r^k) を分け、IH で第一項、補助 hCp で第二項
    (1⊖r)·r^k ≈ r^k ⊕ (⊖r^{k+1}) を出し、M165-2 で畳む。 -/
theorem real_geom_closed (r : RReal) (k : Nat) :
    realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) (realGeomSum r k))
      (realAdd (qToReal ratRing.one) (realNeg (realPow r k))) := by
  induction k with
  | zero =>
    show realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) realZero)
        (realAdd (qToReal ratRing.one) (realNeg (qToReal ratRing.one)))
    exact realEq_trans (rmul_zero _)
      (realEq_symm (realAdd_neg (qToReal ratRing.one)))
  | succ k ih =>
    show realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r))
          (realAdd (realGeomSum r k) (realPow r k)))
        (realAdd (qToReal ratRing.one) (realNeg (rmul (realPow r k) r)))
    -- 補助: (1 ⊖ r)·r^k ≈ r^k ⊕ (⊖(r^k·r))
    have hCp : realEq
        (rmul (realAdd (qToReal ratRing.one) (realNeg r)) (realPow r k))
        (realAdd (realPow r k) (realNeg (rmul (realPow r k) r))) :=
      realEq_trans
        (rmul_add_right (qToReal ratRing.one) (realNeg r) (realPow r k))
        (realEq_trans
          (realAdd_congr_right _ (rmul_neg_left r (realPow r k)))
          (realEq_trans
            (realAdd_congr_right _ (realNeg_congr (rmul_comm r (realPow r k))))
            (realAdd_congr_left _
              (realEq_trans (rmul_comm (qToReal ratRing.one) (realPow r k))
                (rmul_one (realPow r k))))))
    exact realEq_trans
      (rmul_add_left (realGeomSum r k) (realPow r k)
        (realAdd (qToReal ratRing.one) (realNeg r)))
      (realEq_trans
        (realAdd_congr_left
          (rmul (realAdd (qToReal ratRing.one) (realNeg r)) (realPow r k)) ih)
        (realEq_trans
          (realAdd_congr_right
            (realAdd (qToReal ratRing.one) (realNeg (realPow r k))) hCp)
          (real_add_cancel_middle (qToReal ratRing.one) (realPow r k)
            (realNeg (rmul (realPow r k) r)))))

/-! ## M165-4: 総括 -/

/-- **M165-4a: 総括** — 実数幾何級数の realEq 閉形式データ。 -/
structure RealGeomData where
  /-- 部分和の一段展開 s_{k+1} = s_k ⊕ r^k。 -/
  succ : ∀ (r : RReal) (k : Nat),
    realGeomSum r (k + 1) = realAdd (realGeomSum r k) (realPow r k)
  /-- realEq 下の閉形式 (1 ⊖ r)·s_k ≈ 1 ⊖ r^k。 -/
  closed : ∀ (r : RReal) (k : Nat),
    realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) (realGeomSum r k))
      (realAdd (qToReal ratRing.one) (realNeg (realPow r k)))

/-- **M165-4b: witness**。 -/
def realGeomData : RealGeomData where
  succ := fun _ _ => rfl
  closed := real_geom_closed

/-- **M165-4c: 存在**。 -/
theorem realGeom_exists : Nonempty RealGeomData := ⟨realGeomData⟩

end IUT
