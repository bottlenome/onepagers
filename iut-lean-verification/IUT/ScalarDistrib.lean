/-
# M138F: 有理スカラーの分配律 — (x+y)·c ≈ x·c + y·c

柱C（issue #37）。M123F の正直申告（分配律は次層）の有理スカラー
特殊化。log-volume の線形性（rlogVol の qToReal 係数の分配）など
E-2/C-1 の実用形。一般分配律の三重添字ズレを、右因子を定数列
qToReal c に固定して一因子ズレに落とす。

数学設計: z = qToReal c は定数列なので rBound z =: C が |c| の
Nat 上界（rBound_spec z 0 がそのまま qLe (qAbs c) (ratOfInt C)）。
LHS_n = (x_a + y_a)·c（a = 2·mulIdx K₁ n + 1、K₁ = rBound(x+y)+C）、
RHS_n = x_b·c + y_{b'}·c（b = mulIdx K₂ (2n+1)、b' = mulIdx K₃ (2n+1)）。
qMul の右因子が共通 c なので分配は有理数側で厳密に効き、差は
qMul (x_a − x_b) c + qMul (y_a − y_{b'}) c。三つの添字はいずれも
「添字+1 = 4K(n+1)（K ≥ C）」の形なので C/(添字+1) ≤ 1/(4n+4) が
単調性一段（Int.mul_le_mul_of_nonneg_right）で閉じ、4 項の合計が
4/(4n+4) = u_n に収まる — ε-消去不要。

  * M138F-1 右分配ラッパー — `qAdd_mul`/`qSub_mul`
    （qMul_add + qMul_comm/qMul_neg_left の再輸出）
  * M138F-2 添字キャスト橋 — `scalar_addIdx_cast`:
    (2·mulIdx K n + 1) + 1 = 2·(2K(n+1))、`scalar_mulIdx_cast`:
    mulIdx K (2n+1) + 1 = 2·(2K(n+1))（mulIdx_cast の M123F 定型）
  * M138F-3 スカラー分数押さえ — `qFrac_scalar_bound`:
    C ≤ K・j+1 = 4K(n+1) なら C/(j+1) ≤ 1/(4n+4)
    （C(n+1)・K(n+1) の非線形は単調性一段に隔離、残りは同一綴り
    原子で omega）
  * M138F-4 核 — `scalar_distrib_core`: 3 添字 + |c| ≤ C を仮定した
    QRat レベルの 4 項評価
  * M138F-5 本丸 — `rmul_scalar_distrib` と Nat キャスト系
    `rmul_scalar_distrib_nat`（natToReal = qToReal ∘ ratOfInt の defeq）
  * M138F-6 `ScalarDistribData` — 総括

正直申告: 一般の実数×実数分配律・結合律は依然次層（添字スケールが
三重にズレるため 4 点比較の一般化が要る）。本層は右因子が定数列の
特殊形のみ。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealLe
import IUT.VolumeReal

namespace IUT

/-! ## M138F-1: 右分配ラッパー -/

/-- **M138F-1a: 右分配** (a+b)·c = a·c + b·c（qMul_comm + qMul_add）。 -/
theorem qAdd_mul (a b c : QRat) :
    qMul (qAdd a b) c = qAdd (qMul a c) (qMul b c) := by
  rw [qMul_comm (qAdd a b) c, qMul_add c a b, qMul_comm c a, qMul_comm c b]

/-- **M138F-1b: 差の右分配** (a−b)·c = a·c − b·c（qMul_neg_left）。 -/
theorem qSub_mul (a b c : QRat) :
    qMul (qAdd a (qNeg b)) c = qAdd (qMul a c) (qNeg (qMul b c)) := by
  rw [qAdd_mul a (qNeg b) c, qMul_neg_left b c]

/-! ## M138F-2: 添字キャスト橋（M123F の mulIdx_cast 定型） -/

/-- **M138F-2a: LHS 側の橋** — a = 2·mulIdx K n + 1 に対し
    (a : Int) + 1 = 2·(2K(n+1))（mulIdx_cast + 同一綴り原子 omega）。 -/
theorem scalar_addIdx_cast (K n : Nat) (hK : 1 ≤ K) :
    ((2 * mulIdx K n + 1 : Nat) : Int) + 1
      = 2 * (2 * (K : Int) * ((n : Int) + 1)) := by
  have hM := mulIdx_cast K n hK
  omega

/-- **M138F-2b: RHS 側の橋** — b = mulIdx K (2n+1) に対し
    (b : Int) + 1 = 2·(2K(n+1))（2K(2(n+1)) = 2(2K(n+1)) の並べ替えは
    Int.mul_assoc/comm の非線形隔離定型）。 -/
theorem scalar_mulIdx_cast (K n : Nat) (hK : 1 ≤ K) :
    ((mulIdx K (2 * n + 1) : Nat) : Int) + 1
      = 2 * (2 * (K : Int) * ((n : Int) + 1)) := by
  have hM := mulIdx_cast K (2 * n + 1) hK
  have e1 : ((2 * n + 1 : Nat) : Int) + 1 = 2 * ((n : Int) + 1) := by omega
  rw [e1] at hM
  have e2 : 2 * (K : Int) * (2 * ((n : Int) + 1))
      = 2 * (2 * (K : Int) * ((n : Int) + 1)) := by
    rw [← Int.mul_assoc (2 * (K : Int)) 2 ((n : Int) + 1),
      Int.mul_comm (2 * (K : Int)) 2,
      Int.mul_assoc 2 (2 * (K : Int)) ((n : Int) + 1)]
  rw [e2] at hM
  exact hM

/-! ## M138F-3: スカラー分数押さえ -/

/-- **定理 (M138F-3): スカラー分数押さえ（核）** — C ≤ K かつ
    j + 1 = 4K(n+1)（Int 形）なら C/(j+1) ≤ 1/(4n+4)。
    非線形 C(n+1) ≤ K(n+1) は `Int.mul_le_mul_of_nonneg_right` 一段に
    隔離し、K·4(n+1) = 2·(2K(n+1)) は mul_assoc/comm、残りは
    同一綴り原子の omega。 -/
theorem qFrac_scalar_bound (C K n j : Nat) (hCK : C ≤ K)
    (hj : ((j : Nat) : Int) + 1 = 2 * (2 * (K : Int) * ((n : Int) + 1))) :
    qLe (qFrac C j) (qUnitFrac (4 * n + 3)) := by
  apply qFrac_le
  have ecast : ((4 * n + 3 : Nat) : Int) + 1 = 4 * ((n : Int) + 1) := by omega
  rw [ecast]
  have hCK' : (C : Int) ≤ (K : Int) := by omega
  have h1 : (C : Int) * (4 * ((n : Int) + 1))
      ≤ (K : Int) * (4 * ((n : Int) + 1)) :=
    Int.mul_le_mul_of_nonneg_right hCK' (by omega)
  have h22 : (4 : Int) = 2 * 2 := by omega
  have h2 : (K : Int) * (4 * ((n : Int) + 1))
      = 2 * (2 * (K : Int) * ((n : Int) + 1)) := by
    rw [← Int.mul_assoc (K : Int) 4 ((n : Int) + 1), Int.mul_comm (K : Int) 4,
      h22, Int.mul_assoc 2 2 (K : Int),
      Int.mul_assoc 2 (2 * (K : Int)) ((n : Int) + 1)]
  omega

/-! ## M138F-4: 核 — QRat レベルの 4 項評価 -/

/-- **定理 (M138F-4): 分配差の核** — |c| ≤ C と 3 添字の押さえ
    C/(a+1), C/(b+1), C/(b'+1) ≤ 1/(4n+4) から
    |(x_a + y_a)·c − (x_b·c + y_{b'}·c)|
    = |(x_a − x_b)·c + (y_a − y_{b'})·c|
    ≤ (u_a + u_b)·C + (u_a + u_{b'})·C
    = (C/(a+1) + C/(b+1)) + (C/(a+1) + C/(b'+1))
    ≤ 2/(4n+4) + 2/(4n+4) ≤ u_n + u_n。ε-消去不要で閉じる。 -/
theorem scalar_distrib_core (x y : RReal) (c : QRat) (C a b b' n : Nat)
    (hc : qLe (qAbs c) (ratOfInt.map ((C : Nat) : Int)))
    (ha : qLe (qFrac C a) (qUnitFrac (4 * n + 3)))
    (hb : qLe (qFrac C b) (qUnitFrac (4 * n + 3)))
    (hb' : qLe (qFrac C b') (qUnitFrac (4 * n + 3))) :
    qLe (qAbs (qAdd (qMul (qAdd (x.seq a) (y.seq a)) c)
        (qNeg (qAdd (qMul (x.seq b) c) (qMul (y.seq b') c)))))
      (qAdd (qUnitFrac n) (qUnitFrac n)) := by
  -- 分配（有理数側は厳密）と対の差への整理
  rw [qAdd_mul (x.seq a) (y.seq a) c, qAdd_sub_pair,
    ← qSub_mul (x.seq a) (x.seq b) c, ← qSub_mul (y.seq a) (y.seq b') c]
  apply qLe_trans _ _ _ (qAbs_add_le _ _)
  rw [qAbs_mul (qAdd (x.seq a) (qNeg (x.seq b))) c,
    qAbs_mul (qAdd (y.seq a) (qNeg (y.seq b'))) c]
  -- (u_a + u_b)·C の qFrac 化
  have e1 : qMul (qAdd (qUnitFrac a) (qUnitFrac b))
        (ratOfInt.map ((C : Nat) : Int))
      = qAdd (qFrac C a) (qFrac C b) := by
    rw [qMul_comm, qMul_add, ratOfInt_mul_unitFrac, ratOfInt_mul_unitFrac]
  have e2 : qMul (qAdd (qUnitFrac a) (qUnitFrac b'))
        (ratOfInt.map ((C : Nat) : Int))
      = qAdd (qFrac C a) (qFrac C b') := by
    rw [qMul_comm, qMul_add, ratOfInt_mul_unitFrac, ratOfInt_mul_unitFrac]
  -- 各半分: |x_a − x_b|·|c| ≤ C/(a+1) + C/(b+1)
  have t1 : qLe (qMul (qAbs (qAdd (x.seq a) (qNeg (x.seq b)))) (qAbs c))
      (qAdd (qFrac C a) (qFrac C b)) := by
    have h := qLe_mul_two (x.reg a b) hc (qAbs_nonneg c)
      (qFrac_add_nonneg 1 a 1 b)
    rw [e1] at h
    exact h
  have t2 : qLe (qMul (qAbs (qAdd (y.seq a) (qNeg (y.seq b')))) (qAbs c))
      (qAdd (qFrac C a) (qFrac C b')) := by
    have h := qLe_mul_two (y.reg a b') hc (qAbs_nonneg c)
      (qFrac_add_nonneg 1 a 1 b')
    rw [e2] at h
    exact h
  -- 折り畳み: C/(a+1) + C/(b+1) ≤ 2/(4n+4) ≤ 1/(n+1)
  have f1 : qLe (qAdd (qFrac C a) (qFrac C b)) (qUnitFrac n) :=
    qLe_trans _ _ _ (qLe_add_two ha hb)
      (qLe_trans _ _ _ (qFrac_add 1 1 (4 * n + 3)) (qFrac_le (by omega)))
  have f2 : qLe (qAdd (qFrac C a) (qFrac C b')) (qUnitFrac n) :=
    qLe_trans _ _ _ (qLe_add_two ha hb')
      (qLe_trans _ _ _ (qFrac_add 1 1 (4 * n + 3)) (qFrac_le (by omega)))
  exact qLe_add_two (qLe_trans _ _ _ t1 f1) (qLe_trans _ _ _ t2 f2)

/-! ## M138F-5: 本丸 -/

/-- **定理 (M138F-5a): 有理スカラーの分配律（本丸）** —
    (x + y)·c ≈ x·c + y·c（c : QRat、右因子は定数列 qToReal c）。
    |c| の押さえは rBound_spec (qToReal c) 0、三つの加速添字は
    いずれも +1 = 4K(n+1)（K ≥ rBound (qToReal c)）の形なので
    `qFrac_scalar_bound` が一様に効く。 -/
theorem rmul_scalar_distrib (x y : RReal) (c : QRat) :
    realEq (rmul (realAdd x y) (qToReal c))
      (realAdd (rmul x (qToReal c)) (rmul y (qToReal c))) := by
  intro n
  have hc : qLe (qAbs c)
      (ratOfInt.map ((rBound (qToReal c) : Nat) : Int)) :=
    rBound_spec (qToReal c) 0
  have hK1 : 1 ≤ rBound (realAdd x y) + rBound (qToReal c) :=
    rBound_pair_pos (realAdd x y) (qToReal c)
  have hK2 : 1 ≤ rBound x + rBound (qToReal c) :=
    rBound_pair_pos x (qToReal c)
  have hK3 : 1 ≤ rBound y + rBound (qToReal c) :=
    rBound_pair_pos y (qToReal c)
  have ha : qLe (qFrac (rBound (qToReal c))
        (2 * mulIdx (rBound (realAdd x y) + rBound (qToReal c)) n + 1))
      (qUnitFrac (4 * n + 3)) :=
    qFrac_scalar_bound (rBound (qToReal c))
      (rBound (realAdd x y) + rBound (qToReal c)) n
      (2 * mulIdx (rBound (realAdd x y) + rBound (qToReal c)) n + 1)
      (Nat.le_add_left _ _)
      (scalar_addIdx_cast (rBound (realAdd x y) + rBound (qToReal c)) n hK1)
  have hb : qLe (qFrac (rBound (qToReal c))
        (mulIdx (rBound x + rBound (qToReal c)) (2 * n + 1)))
      (qUnitFrac (4 * n + 3)) :=
    qFrac_scalar_bound (rBound (qToReal c)) (rBound x + rBound (qToReal c)) n
      (mulIdx (rBound x + rBound (qToReal c)) (2 * n + 1))
      (Nat.le_add_left _ _)
      (scalar_mulIdx_cast (rBound x + rBound (qToReal c)) n hK2)
  have hb' : qLe (qFrac (rBound (qToReal c))
        (mulIdx (rBound y + rBound (qToReal c)) (2 * n + 1)))
      (qUnitFrac (4 * n + 3)) :=
    qFrac_scalar_bound (rBound (qToReal c)) (rBound y + rBound (qToReal c)) n
      (mulIdx (rBound y + rBound (qToReal c)) (2 * n + 1))
      (Nat.le_add_left _ _)
      (scalar_mulIdx_cast (rBound y + rBound (qToReal c)) n hK3)
  show qLe (qAbs (qAdd
      (qMul (qAdd
        (x.seq (2 * mulIdx (rBound (realAdd x y) + rBound (qToReal c)) n + 1))
        (y.seq (2 * mulIdx (rBound (realAdd x y) + rBound (qToReal c)) n + 1)))
        c)
      (qNeg (qAdd
        (qMul (x.seq (mulIdx (rBound x + rBound (qToReal c)) (2 * n + 1))) c)
        (qMul (y.seq (mulIdx (rBound y + rBound (qToReal c)) (2 * n + 1)))
          c)))))
    (qAdd (qUnitFrac n) (qUnitFrac n))
  exact scalar_distrib_core x y c (rBound (qToReal c))
    (2 * mulIdx (rBound (realAdd x y) + rBound (qToReal c)) n + 1)
    (mulIdx (rBound x + rBound (qToReal c)) (2 * n + 1))
    (mulIdx (rBound y + rBound (qToReal c)) (2 * n + 1))
    n hc ha hb hb'

/-- **定理 (M138F-5b): Nat キャスト系** — (x + y)·k ≈ x·k + y·k
    （natToReal k = qToReal (ratOfInt.map k) の defeq 合わせ）。 -/
theorem rmul_scalar_distrib_nat (x y : RReal) (k : Nat) :
    realEq (rmul (realAdd x y) (natToReal k))
      (realAdd (rmul x (natToReal k)) (rmul y (natToReal k))) :=
  rmul_scalar_distrib x y (ratOfInt.map ((k : Nat) : Int))

/-! ## M138F-6: 総括 -/

/-- **M138F-6a: 総括** — 有理スカラー分配律のデータ。 -/
structure ScalarDistribData where
  /-- 有理スカラーの分配律。 -/
  scalar_distrib : ∀ (x y : RReal) (c : QRat),
    realEq (rmul (realAdd x y) (qToReal c))
      (realAdd (rmul x (qToReal c)) (rmul y (qToReal c)))
  /-- Nat キャスト系。 -/
  scalar_distrib_nat : ∀ (x y : RReal) (k : Nat),
    realEq (rmul (realAdd x y) (natToReal k))
      (realAdd (rmul x (natToReal k)) (rmul y (natToReal k)))

/-- **M138F-6b: witness**。 -/
def scalarDistribData : ScalarDistribData where
  scalar_distrib := rmul_scalar_distrib
  scalar_distrib_nat := rmul_scalar_distrib_nat

/-- **M138F-6c: 存在**。 -/
theorem scalarDistrib_exists : Nonempty ScalarDistribData :=
  ⟨scalarDistribData⟩

end IUT
