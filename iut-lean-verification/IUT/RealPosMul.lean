/-
# M129F: 正値の乗法閉性 — pos·pos = pos

柱C（issue #37）ℝ 構成の順序×乗法の橋。M125 の正直申告
「正値と乗法の両立（pos·pos → pos）は次層」の解消。

  * M129F-1 `qFrac_mul` — 分数の積 (c/(k+1))·(d/(k'+1)) =
    cd/((k+1)(k'+1))（代表の Quot.sound、Nat 減算の −1+1 は
    1 ≤ (k+1)(k'+1) で復元、キャストは Int.natCast_mul）
  * M129F-2 `isPos_lower`/`isPos_lower_weak` — witness n から任意の
    添字 j ≥ 2n+1 での一様下界 x_j ≥ 1/(2n+2)
    （isPos_spread + qLe_cancel_right の消去、witness の弱め n ≤ n' つき）
  * M129F-3 本丸 `isPos_mul` — IsPos x → IsPos y → IsPos (x·y)。
    N = n₁+n₂、E = (2N+2)² を単一原子とし witness M = 2(E−1)+1。
    加速添字 s = mulIdx K M ≥ M ≥ 2N+1 で両因子の下界 1/(2N+2) を
    確保し、正×正の単調性 qLe_mul_two で積の下界 1/E = 2/(M+1) に着地
  * M129F-4 系 `rLt_mul_pos` — 0 < x, 0 < y → 0 < x·y
    （x − 0 ≈ x の橋 `realSub_zero` ×3 で isPos_mul に還元）
  * M129F-5 `RealPosMulData` — 総括

意義: M125 の正直申告の解消。順序体の最後の公理側部品。積の下界は
分数の積 qFrac_mul で J = (2N+2)²−1 に着地し、witness M = 2J+1 で
線形化（非線形は (2N+2)*(2N+2) を単一原子として omega が扱う）。

正直申告: rLt の乗法両立は 0 < x, 0 < y → 0 < x·y の形（一般形
x < y → x·z < y·z は乗法の分配律 — M123F の正直申告の次層 — 待ち）。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealOrder
import IUT.RealAbs

namespace IUT

/-! ## M129F-1: 分数の積 -/

/-- **M129F-1a: 分数の積** (c/(k+1))·(d/(k'+1)) = cd/((k+1)(k'+1))。
    分母は Nat 減算で ((k+1)(k'+1) − 1) + 1 に戻す（1 ≤ 積が要る）。 -/
theorem qFrac_mul (c k d k' : Nat) :
    qMul (qFrac c k) (qFrac d k')
      = qFrac (c * d) ((k + 1) * (k' + 1) - 1) := by
  have h1 : 1 ≤ (k + 1) * (k' + 1) := Nat.mul_pos (by omega) (by omega)
  refine Quot.sound ?_
  show (c : Int) * (d : Int) * ((((k + 1) * (k' + 1) - 1 : Nat) : Int) + 1)
    = ((c * d : Nat) : Int) * (((k : Int) + 1) * ((k' : Int) + 1))
  have e1 : (((k + 1) * (k' + 1) - 1 : Nat) : Int) + 1
      = (((k + 1) * (k' + 1) : Nat) : Int) := by omega
  have e2 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
  have e3 : ((k' + 1 : Nat) : Int) = (k' : Int) + 1 := by omega
  rw [e1, Int.natCast_mul, Int.natCast_mul, e2, e3]

/-! ## M129F-2: 正値 witness の一様下界 -/

/-- **M129F-2a: 一様下界** — witness n（2/(n+1) ≤ x_n）から任意の
    j ≥ 2n+1 で x_j ≥ 1/(2n+2)。isPos_spread の
    2/(n+1) ≤ (u_n + u_j) + x_j に対し 1/(2n+2) + (u_n + u_j) ≤ 2/(n+1)
    を具体計算（u_j ≤ 1/(2n+2)、1/(2n+2)+1/(2n+2) ≤ 1/(n+1)）で示し、
    qLe_cancel_right で x_j を残す（isPos_congr の消去パターン）。 -/
theorem isPos_lower {x : RReal} {n : Nat}
    (hn : qLe (qFrac 2 n) (x.seq n)) {j : Nat} (hj : 2 * n + 1 ≤ j) :
    qLe (qFrac 1 (2 * n + 1)) (x.seq j) := by
  have hspread := isPos_spread hn j
  have hj' : qLe (qUnitFrac j) (qFrac 1 (2 * n + 1)) := qFrac_le (by omega)
  have hfold : qLe (qAdd (qFrac 1 (2 * n + 1)) (qUnitFrac j)) (qFrac 1 n) :=
    qLe_trans _ _ _ (qLe_add_two (qLe_refl (qFrac 1 (2 * n + 1))) hj')
      (qLe_trans _ _ _ (qFrac_add 1 1 (2 * n + 1)) (qFrac_le (by omega)))
  have e : qAdd (qFrac 1 (2 * n + 1)) (qAdd (qUnitFrac n) (qUnitFrac j))
      = qAdd (qUnitFrac n) (qAdd (qFrac 1 (2 * n + 1)) (qUnitFrac j)) := by
    rw [← qAdd_assoc (qFrac 1 (2 * n + 1)) (qUnitFrac n) (qUnitFrac j),
      qAdd_comm (qFrac 1 (2 * n + 1)) (qUnitFrac n),
      qAdd_assoc (qUnitFrac n) (qFrac 1 (2 * n + 1)) (qUnitFrac j)]
  have hC : qLe (qAdd (qFrac 1 (2 * n + 1))
      (qAdd (qUnitFrac n) (qUnitFrac j))) (qFrac 2 n) :=
    qLe_trans _ _ _ (qLe_of_eq e)
      (qLe_trans _ _ _ (qLe_add_two (qLe_refl (qUnitFrac n)) hfold)
        (qFrac_add 1 1 n))
  refine qLe_cancel_right (c := qAdd (qUnitFrac n) (qUnitFrac j)) ?_
  exact qLe_trans _ _ _ (qLe_trans _ _ _ hC hspread)
    (qLe_of_eq (qAdd_comm (qAdd (qUnitFrac n) (qUnitFrac j)) (x.seq j)))

/-- **M129F-2b: 弱め付き一様下界** — n ≤ n'、j ≥ 2n'+1 なら
    x_j ≥ 1/(2n'+2)（下界の分母を共通の 2n'+1 に揃える）。 -/
theorem isPos_lower_weak {x : RReal} {n n' : Nat}
    (hn : qLe (qFrac 2 n) (x.seq n)) (hnn' : n ≤ n') {j : Nat}
    (hj : 2 * n' + 1 ≤ j) : qLe (qFrac 1 (2 * n' + 1)) (x.seq j) :=
  qLe_trans _ _ _ (qFrac_le (by omega)) (isPos_lower hn (by omega))

/-! ## M129F-3: 本丸 — 正値の乗法閉性 -/

/-- **定理 (M129F-3): 正値の乗法閉性** — witness n₁, n₂ から N = n₁+n₂、
    E = (2N+2)·(2N+2) を単一原子として witness M = 2(E−1)+1 を取る。
    加速添字 s = mulIdx K M ≥ M ≥ 2N+1 で x_s, y_s ≥ 1/(2N+2)、
    正×正の単調性と qFrac_mul で x_s·y_s ≥ 1/E = 2/(M+1)。 -/
theorem isPos_mul {x y : RReal} (hx : IsPos x) (hy : IsPos y) :
    IsPos (rmul x y) := by
  obtain ⟨n1, h1⟩ := hx
  obtain ⟨n2, h2⟩ := hy
  refine ⟨2 * ((2 * (n1 + n2) + 1 + 1) * (2 * (n1 + n2) + 1 + 1) - 1) + 1, ?_⟩
  have hK : 1 ≤ rBound x + rBound y := rBound_pair_pos x y
  have hE : (2 * (n1 + n2) + 1 + 1) * 1
      ≤ (2 * (n1 + n2) + 1 + 1) * (2 * (n1 + n2) + 1 + 1) :=
    Nat.mul_le_mul (Nat.le_refl (2 * (n1 + n2) + 1 + 1)) (by omega)
  have hM : 2 * (n1 + n2) + 1
      ≤ 2 * ((2 * (n1 + n2) + 1 + 1) * (2 * (n1 + n2) + 1 + 1) - 1) + 1 := by
    omega
  have hs := mulIdx_ge (rBound x + rBound y)
    (2 * ((2 * (n1 + n2) + 1 + 1) * (2 * (n1 + n2) + 1 + 1) - 1) + 1) hK
  have hxlow := isPos_lower_weak h1 (Nat.le_add_right n1 n2)
    (Nat.le_trans hM hs)
  have hylow := isPos_lower_weak h2 (Nat.le_add_left n2 n1)
    (Nat.le_trans hM hs)
  have h0 : qLe ratRing.zero (qFrac 1 (2 * (n1 + n2) + 1)) :=
    qFrac_nonneg 1 (2 * (n1 + n2) + 1)
  have hmul := qLe_mul_two hxlow hylow h0 (qLe_trans _ _ _ h0 hxlow)
  have hlow : qLe
      (qFrac 2
        (2 * ((2 * (n1 + n2) + 1 + 1) * (2 * (n1 + n2) + 1 + 1) - 1) + 1))
      (qMul (qFrac 1 (2 * (n1 + n2) + 1)) (qFrac 1 (2 * (n1 + n2) + 1))) := by
    rw [qFrac_mul 1 (2 * (n1 + n2) + 1) 1 (2 * (n1 + n2) + 1)]
    exact qFrac_le (by omega)
  exact qLe_trans _ _ _ hlow hmul

/-! ## M129F-4: 系 — rLt の乗法両立 -/

/-- **M129F-4a: −0 = 0**（代表計算）。 -/
theorem qNeg_zero : qNeg ratRing.zero = ratRing.zero :=
  congrArg (Quot.mk ratRel) (preRat_ext Int.neg_zero rfl)

/-- **M129F-4b: −0 ≈ 0**（点ごと qNeg_zero）。 -/
theorem realNeg_zero : realEq (realNeg realZero) realZero :=
  realEq_of_seq_eq (fun _ => qNeg_zero)

/-- **M129F-4c: x − 0 ≈ x**（realNeg_zero + realAdd_zero の橋）。 -/
theorem realSub_zero (x : RReal) :
    realEq (realAdd x (realNeg realZero)) x :=
  realEq_trans (realAdd_congr_right x realNeg_zero) (realAdd_zero x)

/-- **定理 (M129F-4d): rLt の乗法両立** — 0 < x, 0 < y → 0 < x·y
    （realSub_zero の橋 ×3 で isPos_mul に還元）。 -/
theorem rLt_mul_pos {x y : RReal} (hx : rLt realZero x)
    (hy : rLt realZero y) : rLt realZero (rmul x y) :=
  isPos_congr (realEq_symm (realSub_zero (rmul x y)))
    (isPos_mul (isPos_congr (realSub_zero x) hx)
      (isPos_congr (realSub_zero y) hy))

/-! ## M129F-5: 総括 -/

/-- **M129F-5a: 総括** — 正値の乗法閉性のデータ。 -/
structure RealPosMulData where
  /-- 正値の乗法閉性。 -/
  pos_mul : ∀ {x y}, IsPos x → IsPos y → IsPos (rmul x y)
  /-- rLt の乗法両立（0 < x, 0 < y → 0 < x·y）。 -/
  lt_mul : ∀ {x y}, rLt realZero x → rLt realZero y →
    rLt realZero (rmul x y)

/-- **M129F-5b: witness**。 -/
def realPosMulData : RealPosMulData where
  pos_mul := isPos_mul
  lt_mul := rLt_mul_pos

/-- **M129F-5c: 存在**。 -/
theorem realPosMul_exists : Nonempty RealPosMulData :=
  ⟨realPosMulData⟩

end IUT
