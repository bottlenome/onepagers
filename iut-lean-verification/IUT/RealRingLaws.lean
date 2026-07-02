/-
# M150: ℝ の環法則の完成 — 一般 rate-bound 補題による分配律・結合律（柱C 本線）

第90弾で特定され第96弾（M138F スカラー版）でも回避されてきた
**bound-chain 係数問題**（rmul の添字スケジュール K が相手の評価定数を
知らない）を全面解決する。鍵は M145 のミニ極限補題の**二変数一般化**:

  **realEq_of_rate_bound** — 速度 C の点ごと近似
  |w_n − w'_n| ≤ C/(n+1) は realEq w w' を与える
  （3 項望遠鏡 w_n − w'_n = (w_n − w_m) + (w_m − w'_m) + (w'_m − w'_n)
    + ε-消去 c = C+2）

これにより「積の列同士の差を C·uₙ で押さえる」だけでよくなり、
C に rBound の積・和がいくら入っても構わない — 添字スケジュールの
不一致が無害化される。

  * M150-1 `rLe_of_rate_bound` / **`realEq_of_rate_bound`（master）**
  * M150-2 補助 — ratOfInt の非負性・積の定数化
  * M150-3 **`rmul_add_right` / `rmul_add_left`（分配律、realEq）**
    — C = rBound x·2 + rBound z·2 + (rBound y·2 + rBound z·2)
  * M150-4 **`rmul_assoc_real`（結合律、realEq）**
    — C = rBound x·rBound y·2 + rBound z·(rBound x·2 + rBound y·2)
  * M150-5 `RealRingLawsData` — 総括

これで自前 ℝ は加法群（M117F）・乗法可換モノイド（M123F）・
**結合律・分配律（本層）**・順序（M125/M130/M136F）・絶対値（M127F）・
完備性（M128）・正値/apart 逆元（M129F/M145）を備えた
**構成的順序体の全景**に到達する（realEq を等号とする商の意味で）。

正直な限定: realEq 商上の「環構造」の一括レコード化（setoid 環）は
総括層で。rmul の単位元法則 rmul 1 x ≈ x は M123F 済み。

全て選択公理不使用。
-/
import IUT.RealInv

namespace IUT

/-! ## M150-1: 一般 rate-bound 補題（master） -/

/-- **M150-1a: 片側 rate-bound** — |w_k − w'_k| ≤ C/(k+1)（∀k）なら
    rLe w w'。3 項望遠鏡 + ε-消去 c = C+2。 -/
theorem rLe_of_rate_bound (w w' : RReal) (C : Nat)
    (h : ∀ k, qLe (qAbs (qAdd (w.seq k) (qNeg (w'.seq k)))) (qFrac C k)) :
    rLe w w' := by
  intro n
  show qLe (w.seq n) (qAdd (w'.seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))
  apply qLe_of_forall_add_frac (C + 2)
  intro m
  have t1 : qLe (w.seq n)
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac m)) (w.seq m)) :=
    qLe_abs_move (w.reg n m)
  have t2 : qLe (w.seq m) (qAdd (qFrac C m) (w'.seq m)) :=
    qLe_abs_move (h m)
  have t3 : qLe (w'.seq m)
      (qAdd (qAdd (qUnitFrac m) (qUnitFrac n)) (w'.seq n)) :=
    qLe_abs_move (w'.reg m n)
  have hc : qLe (w.seq n)
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
        (qAdd (qFrac C m)
          (qAdd (qAdd (qUnitFrac m) (qUnitFrac n)) (w'.seq n)))) :=
    qLe_trans _ _ _ t1 (qLe_add_two (qLe_refl _)
      (qLe_trans _ _ _ t2 (qLe_add_two (qLe_refl _) t3)))
  refine qLe_trans _ _ _ hc ?_
  -- (u_n+u_m) + (Cu_m + ((u_m+u_n) + w'_n))
  --   = ((u_n+u_m) + (Cu_m + (u_m+u_n))) + w'_n を経て濃縮
  rw [← qAdd_assoc (qFrac C m) (qAdd (qUnitFrac m) (qUnitFrac n))
      (w'.seq n),
    ← qAdd_assoc (qAdd (qUnitFrac n) (qUnitFrac m))
      (qAdd (qFrac C m) (qAdd (qUnitFrac m) (qUnitFrac n))) (w'.seq n)]
  -- 純分数部分: (u_n+u_m) + (Cu_m + (u_m+u_n)) ≤ (u_n+u_n) + F(C+2)m
  have hfold : qLe (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
      (qAdd (qFrac C m) (qAdd (qUnitFrac m) (qUnitFrac n))))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac (C + 2) m)) := by
    rw [qAdd_swap_mid (qUnitFrac n) (qUnitFrac m) (qFrac C m)
        (qAdd (qUnitFrac m) (qUnitFrac n)),
      ← qAdd_assoc (qUnitFrac m) (qUnitFrac m) (qUnitFrac n),
      qAdd_comm (qAdd (qUnitFrac m) (qUnitFrac m)) (qUnitFrac n),
      qAdd_swap_mid (qUnitFrac n) (qFrac C m) (qUnitFrac n)
        (qAdd (qUnitFrac m) (qUnitFrac m))]
    apply qLe_add_two (qLe_refl _)
    exact qLe_trans _ _ _
      (qLe_add_two (qLe_refl _) (qFrac_add 1 1 m)) (qFrac_add C 2 m)
  refine qLe_trans _ _ _ (qLe_add _ _ (w'.seq n) hfold) (qLe_of_eq ?_)
  rw [qAdd_comm (qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
      (qFrac (C + 2) m)) (w'.seq n),
    ← qAdd_assoc (w'.seq n) (qAdd (qUnitFrac n) (qUnitFrac n))
      (qFrac (C + 2) m)]

/-- **定理 (M150-1b): 一般 rate-bound（master）** — 速度 C の点ごと
    近似は realEq。bound-chain 問題の全面解決装置。 -/
theorem realEq_of_rate_bound (w w' : RReal) (C : Nat)
    (h : ∀ k, qLe (qAbs (qAdd (w.seq k) (qNeg (w'.seq k)))) (qFrac C k)) :
    realEq w w' :=
  rLe_antisym (rLe_of_rate_bound w w' C h)
    (rLe_of_rate_bound w' w C (fun k => by
      rw [qAbs_sub_comm (w'.seq k) (w.seq k)]
      exact h k))

/-! ## M150-2: 補助 -/

/-- ratOfInt の Nat キャスト像は非負。 -/
theorem ratOfInt_natCast_nonneg (k : Nat) :
    qLe ratRing.zero (ratOfInt.map ((k : Nat) : Int)) := by
  show (0 : Int) * 1 ≤ ((k : Nat) : Int) * 1
  omega

/-- ratOfInt は Nat 積を保つ（qMul 側から見た形）。 -/
theorem ratOfInt_natCast_mul (a b : Nat) :
    qMul (ratOfInt.map ((a : Nat) : Int)) (ratOfInt.map ((b : Nat) : Int))
      = ratOfInt.map (((a * b : Nat) : Nat) : Int) := by
  have e : (((a * b : Nat) : Nat) : Int)
      = ((a : Nat) : Int) * ((b : Nat) : Int) := Int.natCast_mul a b
  rw [e]
  exact (ratOfInt.map_mul _ _).symm

/-! ## M150-3: 分配律 -/

/-- **定理 (M150-3a): 右分配律（realEq、本丸1）** —
    (x + y)·z ≈ x·z + y·z。積列の差を 4 つの rBound 定数で
    C·uₙ に押さえ、master で回収。 -/
theorem rmul_add_right (x y z : RReal) :
    realEq (rmul (realAdd x y) z) (realAdd (rmul x z) (rmul y z)) := by
  apply realEq_of_rate_bound _ _
    (rBound x * 2 + rBound z * 2 + (rBound y * 2 + rBound z * 2))
  intro n
  show qLe (qAbs (qAdd
      (qMul (qAdd
          (x.seq (2 * mulIdx (rBound (realAdd x y) + rBound z) n + 1))
          (y.seq (2 * mulIdx (rBound (realAdd x y) + rBound z) n + 1)))
        (z.seq (mulIdx (rBound (realAdd x y) + rBound z) n)))
      (qNeg (qAdd
        (qMul (x.seq (mulIdx (rBound x + rBound z) (2 * n + 1)))
          (z.seq (mulIdx (rBound x + rBound z) (2 * n + 1))))
        (qMul (y.seq (mulIdx (rBound y + rBound z) (2 * n + 1)))
          (z.seq (mulIdx (rBound y + rBound z) (2 * n + 1))))))))
    (qFrac (rBound x * 2 + rBound z * 2 + (rBound y * 2 + rBound z * 2)) n)
  have hK1 := rBound_pair_pos (realAdd x y) z
  have hK2 := rBound_pair_pos x z
  have hK3 := rBound_pair_pos y z
  have hA := mulIdx_succ (rBound (realAdd x y) + rBound z) n hK1
  have hB := mulIdx_succ (rBound x + rBound z) (2 * n + 1) hK2
  have hC := mulIdx_succ (rBound y + rBound z) (2 * n + 1) hK3
  generalize ha : mulIdx (rBound (realAdd x y) + rBound z) n = A at *
  generalize hb : mulIdx (rBound x + rBound z) (2 * n + 1) = B at *
  generalize hc : mulIdx (rBound y + rBound z) (2 * n + 1) = Cc at *
  -- 添字下界: n ≤ A, 2A+1, B, Cc
  have hAn : n ≤ A := by
    have h2 : 1 * (n + 1)
        ≤ 2 * (rBound (realAdd x y) + rBound z) * (n + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hBn : n ≤ B := by
    have h2 : 1 * (2 * n + 1 + 1)
        ≤ 2 * (rBound x + rBound z) * (2 * n + 1 + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hCn : n ≤ Cc := by
    have h2 : 1 * (2 * n + 1 + 1)
        ≤ 2 * (rBound y + rBound z) * (2 * n + 1 + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  -- 差の 2 分割
  rw [qAdd_mul (x.seq (2 * A + 1)) (y.seq (2 * A + 1)) (z.seq A),
    qNeg_add_dist (qMul (x.seq B) (z.seq B)) (qMul (y.seq Cc) (z.seq Cc)),
    qAdd_swap_mid (qMul (x.seq (2 * A + 1)) (z.seq A))
      (qMul (y.seq (2 * A + 1)) (z.seq A))
      (qNeg (qMul (x.seq B) (z.seq B)))
      (qNeg (qMul (y.seq Cc) (z.seq Cc)))]
  refine qLe_trans _ _ _ (qAbs_add_le _ _) ?_
  -- 項 1: |x'z_A − x_B z_B| ≤ Bx·2uₙ + Bz·2uₙ
  have hb1 : qLe (qAbs (qAdd (qMul (x.seq (2 * A + 1)) (z.seq A))
      (qNeg (qMul (x.seq B) (z.seq B)))))
      (qFrac (rBound x * 2 + rBound z * 2) n) := by
    refine qLe_trans _ _ _
      (qAbs_mul_sub (x.seq (2 * A + 1)) (z.seq A) (x.seq B) (z.seq B)) ?_
    have s1 : qLe (qMul (qAbs (x.seq (2 * A + 1)))
        (qAbs (qAdd (z.seq A) (qNeg (z.seq B)))))
        (qFrac (rBound x * 2) n) := by
      have hzz : qLe (qAbs (qAdd (z.seq A) (qNeg (z.seq B)))) (qFrac 2 n) :=
        qLe_trans _ _ _ (z.reg A B)
          (qLe_trans _ _ _ (qLe_add_two (qFrac_le (by omega))
            (qFrac_le (by omega))) (qFrac_add 1 1 n))
      have := qLe_mul_two (rBound_spec x (2 * A + 1)) hzz
        (qAbs_nonneg _) (ratOfInt_natCast_nonneg _)
      rw [ratOfInt_mul_qFrac (rBound x) 2 n] at this
      exact this
    have s2 : qLe (qMul (qAbs (z.seq B))
        (qAbs (qAdd (x.seq (2 * A + 1)) (qNeg (x.seq B)))))
        (qFrac (rBound z * 2) n) := by
      have hxx : qLe (qAbs (qAdd (x.seq (2 * A + 1)) (qNeg (x.seq B))))
          (qFrac 2 n) :=
        qLe_trans _ _ _ (x.reg (2 * A + 1) B)
          (qLe_trans _ _ _ (qLe_add_two (qFrac_le (by omega))
            (qFrac_le (by omega))) (qFrac_add 1 1 n))
      have := qLe_mul_two (rBound_spec z B) hxx
        (qAbs_nonneg _) (ratOfInt_natCast_nonneg _)
      rw [ratOfInt_mul_qFrac (rBound z) 2 n] at this
      exact this
    exact qLe_trans _ _ _ (qLe_add_two s1 s2)
      (qFrac_add (rBound x * 2) (rBound z * 2) n)
  -- 項 2（対称）
  have hb2 : qLe (qAbs (qAdd (qMul (y.seq (2 * A + 1)) (z.seq A))
      (qNeg (qMul (y.seq Cc) (z.seq Cc)))))
      (qFrac (rBound y * 2 + rBound z * 2) n) := by
    refine qLe_trans _ _ _
      (qAbs_mul_sub (y.seq (2 * A + 1)) (z.seq A) (y.seq Cc) (z.seq Cc)) ?_
    have s1 : qLe (qMul (qAbs (y.seq (2 * A + 1)))
        (qAbs (qAdd (z.seq A) (qNeg (z.seq Cc)))))
        (qFrac (rBound y * 2) n) := by
      have hzz : qLe (qAbs (qAdd (z.seq A) (qNeg (z.seq Cc)))) (qFrac 2 n) :=
        qLe_trans _ _ _ (z.reg A Cc)
          (qLe_trans _ _ _ (qLe_add_two (qFrac_le (by omega))
            (qFrac_le (by omega))) (qFrac_add 1 1 n))
      have := qLe_mul_two (rBound_spec y (2 * A + 1)) hzz
        (qAbs_nonneg _) (ratOfInt_natCast_nonneg _)
      rw [ratOfInt_mul_qFrac (rBound y) 2 n] at this
      exact this
    have s2 : qLe (qMul (qAbs (z.seq Cc))
        (qAbs (qAdd (y.seq (2 * A + 1)) (qNeg (y.seq Cc)))))
        (qFrac (rBound z * 2) n) := by
      have hyy : qLe (qAbs (qAdd (y.seq (2 * A + 1)) (qNeg (y.seq Cc))))
          (qFrac 2 n) :=
        qLe_trans _ _ _ (y.reg (2 * A + 1) Cc)
          (qLe_trans _ _ _ (qLe_add_two (qFrac_le (by omega))
            (qFrac_le (by omega))) (qFrac_add 1 1 n))
      have := qLe_mul_two (rBound_spec z Cc) hyy
        (qAbs_nonneg _) (ratOfInt_natCast_nonneg _)
      rw [ratOfInt_mul_qFrac (rBound z) 2 n] at this
      exact this
    exact qLe_trans _ _ _ (qLe_add_two s1 s2)
      (qFrac_add (rBound y * 2) (rBound z * 2) n)
  exact qLe_trans _ _ _ (qLe_add_two hb1 hb2)
    (qFrac_add (rBound x * 2 + rBound z * 2)
      (rBound y * 2 + rBound z * 2) n)

/-- **M150-3b: 左分配律** — z·(x + y) ≈ z·x + z·y（可換 + congruence）。 -/
theorem rmul_add_left (x y z : RReal) :
    realEq (rmul z (realAdd x y)) (realAdd (rmul z x) (rmul z y)) := by
  refine realEq_trans (rmul_comm z (realAdd x y)) ?_
  refine realEq_trans (rmul_add_right x y z) ?_
  refine realEq_trans (realAdd_congr_left (rmul y z) (rmul_comm x z)) ?_
  exact realAdd_congr_right (rmul z x) (rmul_comm y z)

/-! ## M150-4: 結合律 -/

/-- **定理 (M150-4): 結合律（realEq、本丸2）** — (x·y)·z ≈ x·(y·z)。
    三重積の差を rBound の積の定数で C·uₙ に押さえ、master で回収。 -/
theorem rmul_assoc_real (x y z : RReal) :
    realEq (rmul (rmul x y) z) (rmul x (rmul y z)) := by
  apply realEq_of_rate_bound _ _
    (rBound x * rBound y * 2
      + rBound z * (rBound x * 2 + rBound y * 2))
  intro n
  show qLe (qAbs (qAdd
      (qMul (qMul
          (x.seq (mulIdx (rBound x + rBound y)
            (mulIdx (rBound (rmul x y) + rBound z) n)))
          (y.seq (mulIdx (rBound x + rBound y)
            (mulIdx (rBound (rmul x y) + rBound z) n))))
        (z.seq (mulIdx (rBound (rmul x y) + rBound z) n)))
      (qNeg (qMul
        (x.seq (mulIdx (rBound x + rBound (rmul y z)) n))
        (qMul
          (y.seq (mulIdx (rBound y + rBound z)
            (mulIdx (rBound x + rBound (rmul y z)) n)))
          (z.seq (mulIdx (rBound y + rBound z)
            (mulIdx (rBound x + rBound (rmul y z)) n))))))))
    (qFrac (rBound x * rBound y * 2
      + rBound z * (rBound x * 2 + rBound y * 2)) n)
  have hK1 := rBound_pair_pos (rmul x y) z
  have hK2 := rBound_pair_pos x y
  have hK3 := rBound_pair_pos x (rmul y z)
  have hK4 := rBound_pair_pos y z
  have hA := mulIdx_succ (rBound (rmul x y) + rBound z) n hK1
  generalize ha : mulIdx (rBound (rmul x y) + rBound z) n = A at *
  have hA' := mulIdx_succ (rBound x + rBound y) A hK2
  generalize ha' : mulIdx (rBound x + rBound y) A = A' at *
  have hB := mulIdx_succ (rBound x + rBound (rmul y z)) n hK3
  generalize hb : mulIdx (rBound x + rBound (rmul y z)) n = B at *
  have hB' := mulIdx_succ (rBound y + rBound z) B hK4
  generalize hb' : mulIdx (rBound y + rBound z) B = B' at *
  -- 添字下界
  have hAn : n ≤ A := by
    have h2 : 1 * (n + 1) ≤ 2 * (rBound (rmul x y) + rBound z) * (n + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hA'n : A ≤ A' := by
    have h2 : 1 * (A + 1) ≤ 2 * (rBound x + rBound y) * (A + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hBn : n ≤ B := by
    have h2 : 1 * (n + 1)
        ≤ 2 * (rBound x + rBound (rmul y z)) * (n + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hB'n : B ≤ B' := by
    have h2 : 1 * (B + 1) ≤ 2 * (rBound y + rBound z) * (B + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  -- RHS 三重積を左結合形へ
  rw [← qMul_assoc (x.seq B) (y.seq B') (z.seq B')]
  refine qLe_trans _ _ _ (qAbs_mul_sub
    (qMul (x.seq A') (y.seq A')) (z.seq A)
    (qMul (x.seq B) (y.seq B')) (z.seq B')) ?_
  -- 項 1: |x_{A'}y_{A'}|·|z_A − z_{B'}| ≤ (BxBy)·2uₙ
  have s1 : qLe (qMul (qAbs (qMul (x.seq A') (y.seq A')))
      (qAbs (qAdd (z.seq A) (qNeg (z.seq B')))))
      (qFrac (rBound x * rBound y * 2) n) := by
    have hxy : qLe (qAbs (qMul (x.seq A') (y.seq A')))
        (ratOfInt.map (((rBound x * rBound y : Nat) : Nat) : Int)) := by
      rw [qAbs_mul, ← ratOfInt_natCast_mul (rBound x) (rBound y)]
      exact qLe_mul_two (rBound_spec x A') (rBound_spec y A')
        (qAbs_nonneg _) (ratOfInt_natCast_nonneg _)
    have hzz : qLe (qAbs (qAdd (z.seq A) (qNeg (z.seq B')))) (qFrac 2 n) :=
      qLe_trans _ _ _ (z.reg A B')
        (qLe_trans _ _ _ (qLe_add_two (qFrac_le (by omega))
          (qFrac_le (by omega))) (qFrac_add 1 1 n))
    have := qLe_mul_two hxy hzz (qAbs_nonneg _) (ratOfInt_natCast_nonneg _)
    rw [ratOfInt_mul_qFrac (rBound x * rBound y) 2 n] at this
    exact this
  -- 項 2: |z_{B'}|·|x_{A'}y_{A'} − x_B y_{B'}| ≤ Bz·(Bx·2 + By·2)uₙ
  have s2 : qLe (qMul (qAbs (z.seq B'))
      (qAbs (qAdd (qMul (x.seq A') (y.seq A'))
        (qNeg (qMul (x.seq B) (y.seq B'))))))
      (qFrac (rBound z * (rBound x * 2 + rBound y * 2)) n) := by
    have hinner : qLe (qAbs (qAdd (qMul (x.seq A') (y.seq A'))
        (qNeg (qMul (x.seq B) (y.seq B')))))
        (qFrac (rBound x * 2 + rBound y * 2) n) := by
      refine qLe_trans _ _ _
        (qAbs_mul_sub (x.seq A') (y.seq A') (x.seq B) (y.seq B')) ?_
      have u1 : qLe (qMul (qAbs (x.seq A'))
          (qAbs (qAdd (y.seq A') (qNeg (y.seq B')))))
          (qFrac (rBound x * 2) n) := by
        have hyy : qLe (qAbs (qAdd (y.seq A') (qNeg (y.seq B'))))
            (qFrac 2 n) :=
          qLe_trans _ _ _ (y.reg A' B')
            (qLe_trans _ _ _ (qLe_add_two (qFrac_le (by omega))
              (qFrac_le (by omega))) (qFrac_add 1 1 n))
        have := qLe_mul_two (rBound_spec x A') hyy
          (qAbs_nonneg _) (ratOfInt_natCast_nonneg _)
        rw [ratOfInt_mul_qFrac (rBound x) 2 n] at this
        exact this
      have u2 : qLe (qMul (qAbs (y.seq B'))
          (qAbs (qAdd (x.seq A') (qNeg (x.seq B)))))
          (qFrac (rBound y * 2) n) := by
        have hxx : qLe (qAbs (qAdd (x.seq A') (qNeg (x.seq B))))
            (qFrac 2 n) :=
          qLe_trans _ _ _ (x.reg A' B)
            (qLe_trans _ _ _ (qLe_add_two (qFrac_le (by omega))
              (qFrac_le (by omega))) (qFrac_add 1 1 n))
        have := qLe_mul_two (rBound_spec y B') hxx
          (qAbs_nonneg _) (ratOfInt_natCast_nonneg _)
        rw [ratOfInt_mul_qFrac (rBound y) 2 n] at this
        exact this
      exact qLe_trans _ _ _ (qLe_add_two u1 u2)
        (qFrac_add (rBound x * 2) (rBound y * 2) n)
    have := qLe_mul_two (rBound_spec z B') hinner
      (qAbs_nonneg _) (ratOfInt_natCast_nonneg _)
    rw [ratOfInt_mul_qFrac (rBound z) (rBound x * 2 + rBound y * 2) n]
      at this
    exact this
  exact qLe_trans _ _ _ (qLe_add_two s1 s2)
    (qFrac_add (rBound x * rBound y * 2)
      (rBound z * (rBound x * 2 + rBound y * 2)) n)

/-! ## M150-5: 総括 -/

/-- **M150-5a: 総括** — ℝ の環法則データ。 -/
structure RealRingLawsData where
  /-- 一般 rate-bound（master）。 -/
  rate_bound : ∀ (w w' : RReal) (C : Nat),
    (∀ k, qLe (qAbs (qAdd (w.seq k) (qNeg (w'.seq k)))) (qFrac C k)) →
    realEq w w'
  /-- 右分配律。 -/
  right_distrib : ∀ x y z,
    realEq (rmul (realAdd x y) z) (realAdd (rmul x z) (rmul y z))
  /-- 左分配律。 -/
  left_distrib : ∀ x y z,
    realEq (rmul z (realAdd x y)) (realAdd (rmul z x) (rmul z y))
  /-- 結合律。 -/
  assoc : ∀ x y z, realEq (rmul (rmul x y) z) (rmul x (rmul y z))

/-- **M150-5b: witness**。 -/
def realRingLawsData : RealRingLawsData where
  rate_bound := realEq_of_rate_bound
  right_distrib := rmul_add_right
  left_distrib := rmul_add_left
  assoc := rmul_assoc_real

/-- **M150-5c: 存在**。 -/
theorem realRingLaws_exists : Nonempty RealRingLawsData :=
  ⟨realRingLawsData⟩

end IUT
