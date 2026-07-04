/-
# M180: 実数乗法の順序単調性 — rLe の右乗法単調性（柱C）

M130 の非厳密順序 `rLe` と M123F の乗法 `rmul` の橋渡し。
rmul x z と rmul y z は添字加速定数 K₁ = rBound x + rBound z と
K₂ = rBound y + rBound z が異なる（bound-chain 問題）ため点ごと
直接比較は破綻するが、M123F-7e（mul_seq_congr）の 4 点比較を
片側不等式に読み替えた望遠鏡
x_{s₁}z_{s₁} → x_j z_j → y_j z_j → y_{s₂}z_{s₂}（∀j）で
ε-消去に持ち込む。中央ギャップは z_j が僅かに負になり得る
（rLe realZero z は z_j ≥ −2u_j までしか言わない）ため、
(x_j − y_j)·z_j = (x_j − y_j)(z_j + 2u_j) − (x_j − y_j)·2u_j と
分解し、非負因子 z_j + 2u_j への右単調性（qLe_mul_right）と
rBound による大きさ押さえで j-項に濃縮するのが核。

  * M180-1 `mul_idx_gap` — 加速添字と比較点 j の積ギャップ
    |x_s z_s − x_j z_j| ≤ u_n + (K+K)/(j+1)
    （mul_seq_congr の Gap1 の単独補題化）
  * M180-2 `rmul_mid_gap` — 中央ギャップ
    x_j z_j − y_j z_j ≤ (2·rBound z + 4 + 2(rBound x + rBound y))/(j+1)
    （非負シフト z_j + 2u_j 経由の片側評価）
  * M180-3 `rmul_le_seq` — 点ごと核: 望遠鏡 + ε-消去
  * M180-4 **本丸 `rmul_le_mul_right`** — x ≤ y, 0 ≤ z なら
    x·z ≤ y·z（rLe）。左版 `rmul_le_mul_left` は可換 + congruence
  * M180-5 `realPow_nonneg` / **`realPow_le`** — 冪の非負性と
    冪の単調性 0 ≤ a ≤ b ⟹ a^k ≤ b^k（k の帰納で M180-4 を二度）
  * M180-6 `RealMulOrderData` — 総括 + witness + 存在

## 意義

幾何級数の収束論（柱C）のブロッカーの解消。比 r の冪 r^k を
比較級数で押さえる rate-bound 論法は「≤ を非負実数倍しても保たれる」
こと（本モジュールの M180-4）に帰着する。M159F は非負**整数**定数倍
に限定していたが、本モジュールで一般の非負実数 z に拡張され、
realPow_le により冪の項別比較が可能になる。

正直な限定: 狭義順序 rLt 版の乗法単調性、および両側同時
（x ≤ x', z ≤ z' ⟹ xz ≤ x'z'）版は次層。z の非負性は
rLe realZero z（witness 揺らぎ込み）で仮定しており、
これは点ごとには z_j ≥ −2/(j+1) しか与えないが、
本証明の非負シフト分解はこの弱い形で十分に閉じている。

全て選択公理不使用。
-/
import IUT.RealAbsPow
import IUT.RealLe

namespace IUT

/-! ## M180-1: 加速添字と比較点の積ギャップ -/

/-- **M180-1: 積ギャップ補題** — K を x・z の一様上界（K ≥ 1）とすると
    s = mulIdx K n に対し |x_s z_s − x_j z_j| ≤ u_n + (K+K)/(j+1)。
    mul_seq_congr（M123F-7e）の Gap1 を単独補題化したもの:
    |x_s z_s − x_j z_j| ≤ |x_s||z_s − z_j| + |z_j||x_s − x_j|
    ≤ K(u_s + u_j) + K(u_s + u_j) → s-項は相殺補題で u_n へ。 -/
theorem mul_idx_gap (x z : RReal) (K : Nat) (hK : 1 ≤ K)
    (hxK : ∀ i, qLe (qAbs (x.seq i)) (ratOfInt.map (K : Int)))
    (hzK : ∀ i, qLe (qAbs (z.seq i)) (ratOfInt.map (K : Int)))
    (n j : Nat) :
    qLe (qAbs (qAdd (qMul (x.seq (mulIdx K n)) (z.seq (mulIdx K n)))
        (qNeg (qMul (x.seq j) (z.seq j)))))
      (qAdd (qUnitFrac n) (qFrac (K + K) j)) := by
  have hKnn : qLe ratRing.zero (ratOfInt.map (K : Int)) :=
    qLe_trans _ _ _ (qAbs_nonneg (z.seq j)) (hzK j)
  have b := qAbs_mul_sub (x.seq (mulIdx K n)) (z.seq (mulIdx K n))
    (x.seq j) (z.seq j)
  have t1 := qLe_mul_two (hxK (mulIdx K n)) (z.reg (mulIdx K n) j)
    (qAbs_nonneg _) hKnn
  have t2 := qLe_mul_two (hzK j) (x.reg (mulIdx K n) j)
    (qAbs_nonneg _) hKnn
  have b2 := qLe_trans _ _ _ b (qLe_add_two t1 t2)
  have eT : qMul (ratOfInt.map (K : Int))
        (qAdd (qUnitFrac (mulIdx K n)) (qUnitFrac j))
      = qAdd (qFrac K (mulIdx K n)) (qFrac K j) := by
    rw [qMul_add, ratOfInt_mul_unitFrac, ratOfInt_mul_unitFrac]
  rw [eT] at b2
  have swap : qAdd (qAdd (qFrac K (mulIdx K n)) (qFrac K j))
        (qAdd (qFrac K (mulIdx K n)) (qFrac K j))
      = qAdd (qAdd (qFrac K (mulIdx K n)) (qFrac K (mulIdx K n)))
        (qAdd (qFrac K j) (qFrac K j)) :=
    qAdd_swap_mid _ _ _ _
  have fold1 : qLe (qAdd (qFrac K (mulIdx K n)) (qFrac K (mulIdx K n)))
      (qUnitFrac n) :=
    qLe_trans _ _ _ (qFrac_add K K (mulIdx K n)) (qFrac_two_bound K n hK)
  exact qLe_trans _ _ _ b2 (qLe_trans _ _ _ (qLe_of_eq swap)
    (qLe_add_two fold1 (qFrac_add K K j)))

/-! ## M180-2: 中央ギャップ（rLe と z ≥ 0 の使用点） -/

/-- **定理 (M180-2): 中央ギャップ** — x ≤ y（rLe）、0 ≤ z（rLe）のとき
    x_j z_j − y_j z_j ≤ (2·rBound z + 4 + 2(rBound x + rBound y))/(j+1)。

    核: d := x_j − y_j ≤ 2u_j に対し z_j は僅かに負になり得るので、
    d·z_j = d·(z_j + 2u_j) + (−d)·(2u_j) と分解する。
    第一項は 0 ≤ z_j + 2u_j（rLe realZero z の点ごと読み）への
    右単調性で 2u_j·(z_j + 2u_j) ≤ (2·rBound z)/(j+1) + 4/(j+1)、
    第二項は −d ≤ |x_j| + |y_j| ≤ rBound x + rBound y の大きさ押さえで
    2(rBound x + rBound y)/(j+1)。全て j-項なので ε-消去で消える。 -/
theorem rmul_mid_gap {x y z : RReal} (hxy : rLe x y) (hz : rLe realZero z)
    (j : Nat) :
    qLe (qAdd (qMul (x.seq j) (z.seq j)) (qNeg (qMul (y.seq j) (z.seq j))))
      (qFrac (rBound z * 2 + 4
        + (rBound y + rBound y + (rBound x + rBound x))) j) := by
  -- d = x_j − y_j ≤ 2/(j+1)
  have hd : qLe (qAdd (x.seq j) (qNeg (y.seq j))) (qFrac 2 j) :=
    qLe_trans _ _ _ (qSub_le_of_le (hxy j)) (qFrac_add 1 1 j)
  -- 非負シフト 0 ≤ z_j + 2u_j（rLe realZero z の点ごと読み）
  have hw : qLe ratRing.zero
      (qAdd (z.seq j) (qAdd (qUnitFrac j) (qUnitFrac j))) := hz j
  have hu2nn : qLe ratRing.zero (qAdd (qUnitFrac j) (qUnitFrac j)) :=
    qFrac_add_nonneg 1 j 1 j
  -- Step A: d·(z_j + 2u_j) ≤ F2j·(z_j + 2u_j)
  have hstepA : qLe
      (qMul (qAdd (x.seq j) (qNeg (y.seq j)))
        (qAdd (z.seq j) (qAdd (qUnitFrac j) (qUnitFrac j))))
      (qMul (qFrac 2 j)
        (qAdd (z.seq j) (qAdd (qUnitFrac j) (qUnitFrac j)))) :=
    qLe_mul_right hd hw
  -- F2j·(z_j + 2u_j) = F2j·z_j + F2j·2u_j
  have edist : qMul (qFrac 2 j)
        (qAdd (z.seq j) (qAdd (qUnitFrac j) (qUnitFrac j)))
      = qAdd (qMul (qFrac 2 j) (z.seq j))
        (qMul (qFrac 2 j) (qAdd (qUnitFrac j) (qUnitFrac j))) :=
    qMul_add (qFrac 2 j) (z.seq j) (qAdd (qUnitFrac j) (qUnitFrac j))
  -- term1: F2j·z_j ≤ (rBound z · 2)/(j+1)
  have hzB : qLe (z.seq j) (ratOfInt.map ((rBound z : Nat) : Int)) :=
    qLe_trans _ _ _ (qLe_self_abs (z.seq j)) (rBound_spec z j)
  have term1 : qLe (qMul (qFrac 2 j) (z.seq j))
      (qFrac (rBound z * 2) j) := by
    rw [qMul_comm (qFrac 2 j) (z.seq j)]
    exact qLe_trans _ _ _ (qLe_mul_right hzB (qFrac_nonneg 2 j))
      (qLe_of_eq (ratOfInt_mul_qFrac (rBound z) 2 j))
  -- term2: F2j·2u_j ≤ 4/(j+1)
  have hu2b : qLe (qFrac 2 j) (ratOfInt.map ((2 : Nat) : Int)) := by
    show ((2 : Nat) : Int) * 1 ≤ ((2 : Nat) : Int) * ((j : Int) + 1)
    omega
  have hu2 : qLe (qAdd (qUnitFrac j) (qUnitFrac j))
      (ratOfInt.map ((2 : Nat) : Int)) :=
    qLe_trans _ _ _ (qFrac_add 1 1 j) hu2b
  have term2 : qLe (qMul (qFrac 2 j) (qAdd (qUnitFrac j) (qUnitFrac j)))
      (qFrac 4 j) := by
    rw [qMul_comm (qFrac 2 j) (qAdd (qUnitFrac j) (qUnitFrac j))]
    exact qLe_trans _ _ _ (qLe_mul_right hu2 (qFrac_nonneg 2 j))
      (qLe_of_eq (ratOfInt_mul_qFrac 2 2 j))
  -- term3: (−d)·2u_j ≤ 2(rBound x + rBound y)/(j+1)
  have hnd : qLe (qNeg (qAdd (x.seq j) (qNeg (y.seq j))))
      (qAdd (ratOfInt.map ((rBound y : Nat) : Int))
        (ratOfInt.map ((rBound x : Nat) : Int))) := by
    rw [qNeg_sub (x.seq j) (y.seq j)]
    have h2 := qAbs_add_le (y.seq j) (qNeg (x.seq j))
    rw [qAbs_neg (x.seq j)] at h2
    exact qLe_trans _ _ _ (qLe_self_abs (qAdd (y.seq j) (qNeg (x.seq j))))
      (qLe_trans _ _ _ h2
        (qLe_add_two (rBound_spec y j) (rBound_spec x j)))
  have hByu : qLe (qMul (ratOfInt.map ((rBound y : Nat) : Int))
        (qAdd (qUnitFrac j) (qUnitFrac j)))
      (qFrac (rBound y + rBound y) j) := by
    rw [qMul_add (ratOfInt.map ((rBound y : Nat) : Int))
        (qUnitFrac j) (qUnitFrac j),
      ratOfInt_mul_unitFrac (rBound y) j]
    exact qFrac_add (rBound y) (rBound y) j
  have hBxu : qLe (qMul (ratOfInt.map ((rBound x : Nat) : Int))
        (qAdd (qUnitFrac j) (qUnitFrac j)))
      (qFrac (rBound x + rBound x) j) := by
    rw [qMul_add (ratOfInt.map ((rBound x : Nat) : Int))
        (qUnitFrac j) (qUnitFrac j),
      ratOfInt_mul_unitFrac (rBound x) j]
    exact qFrac_add (rBound x) (rBound x) j
  have edist3 : qMul (qAdd (ratOfInt.map ((rBound y : Nat) : Int))
        (ratOfInt.map ((rBound x : Nat) : Int)))
        (qAdd (qUnitFrac j) (qUnitFrac j))
      = qAdd (qMul (ratOfInt.map ((rBound y : Nat) : Int))
          (qAdd (qUnitFrac j) (qUnitFrac j)))
        (qMul (ratOfInt.map ((rBound x : Nat) : Int))
          (qAdd (qUnitFrac j) (qUnitFrac j))) := by
    rw [qMul_comm (qAdd (ratOfInt.map ((rBound y : Nat) : Int))
        (ratOfInt.map ((rBound x : Nat) : Int)))
        (qAdd (qUnitFrac j) (qUnitFrac j)),
      qMul_add (qAdd (qUnitFrac j) (qUnitFrac j))
        (ratOfInt.map ((rBound y : Nat) : Int))
        (ratOfInt.map ((rBound x : Nat) : Int)),
      qMul_comm (qAdd (qUnitFrac j) (qUnitFrac j))
        (ratOfInt.map ((rBound y : Nat) : Int)),
      qMul_comm (qAdd (qUnitFrac j) (qUnitFrac j))
        (ratOfInt.map ((rBound x : Nat) : Int))]
  have term3 : qLe (qMul (qNeg (qAdd (x.seq j) (qNeg (y.seq j))))
        (qAdd (qUnitFrac j) (qUnitFrac j)))
      (qFrac (rBound y + rBound y + (rBound x + rBound x)) j) :=
    qLe_trans _ _ _ (qLe_mul_right hnd hu2nn)
      (qLe_trans _ _ _ (qLe_of_eq edist3)
        (qLe_trans _ _ _ (qLe_add_two hByu hBxu)
          (qFrac_add (rBound y + rBound y) (rBound x + rBound x) j)))
  -- Step A の右辺濃縮: d·(z_j + 2u_j) ≤ F(Bz·2)j + F4j
  have hA : qLe (qMul (qAdd (x.seq j) (qNeg (y.seq j)))
        (qAdd (z.seq j) (qAdd (qUnitFrac j) (qUnitFrac j))))
      (qAdd (qFrac (rBound z * 2) j) (qFrac 4 j)) :=
    qLe_trans _ _ _ hstepA (qLe_trans _ _ _ (qLe_of_eq edist)
      (qLe_add_two term1 term2))
  -- 分解恒等式: d·(z_j + 2u_j) + (−d)·2u_j = d·z_j
  have efac2 : qAdd (qMul (qAdd (x.seq j) (qNeg (y.seq j)))
        (qAdd (z.seq j) (qAdd (qUnitFrac j) (qUnitFrac j))))
      (qMul (qNeg (qAdd (x.seq j) (qNeg (y.seq j))))
        (qAdd (qUnitFrac j) (qUnitFrac j)))
      = qMul (qAdd (x.seq j) (qNeg (y.seq j))) (z.seq j) := by
    rw [qMul_add (qAdd (x.seq j) (qNeg (y.seq j))) (z.seq j)
        (qAdd (qUnitFrac j) (qUnitFrac j)),
      qMul_neg_left (qAdd (x.seq j) (qNeg (y.seq j)))
        (qAdd (qUnitFrac j) (qUnitFrac j)),
      qAdd_assoc (qMul (qAdd (x.seq j) (qNeg (y.seq j))) (z.seq j))
        (qMul (qAdd (x.seq j) (qNeg (y.seq j)))
          (qAdd (qUnitFrac j) (qUnitFrac j)))
        (qNeg (qMul (qAdd (x.seq j) (qNeg (y.seq j)))
          (qAdd (qUnitFrac j) (qUnitFrac j)))),
      qAdd_neg_self (qMul (qAdd (x.seq j) (qNeg (y.seq j)))
        (qAdd (qUnitFrac j) (qUnitFrac j))),
      qAdd_zero (qMul (qAdd (x.seq j) (qNeg (y.seq j))) (z.seq j))]
  -- 合成: d·z_j ≤ (F(Bz·2)j + F4j) + F(2(Bx+By))j
  have hmid0 : qLe (qMul (qAdd (x.seq j) (qNeg (y.seq j))) (z.seq j))
      (qAdd (qAdd (qFrac (rBound z * 2) j) (qFrac 4 j))
        (qFrac (rBound y + rBound y + (rBound x + rBound x)) j)) :=
    qLe_trans _ _ _ (qLe_of_eq efac2.symm) (qLe_add_two hA term3)
  -- j-項の合併
  have hfold : qLe (qAdd (qAdd (qFrac (rBound z * 2) j) (qFrac 4 j))
        (qFrac (rBound y + rBound y + (rBound x + rBound x)) j))
      (qFrac (rBound z * 2 + 4
        + (rBound y + rBound y + (rBound x + rBound x))) j) :=
    qLe_trans _ _ _
      (qLe_add_two (qFrac_add (rBound z * 2) 4 j) (qLe_refl _))
      (qFrac_add (rBound z * 2 + 4)
        (rBound y + rBound y + (rBound x + rBound x)) j)
  -- (x_j − y_j)·z_j = x_j z_j − y_j z_j に張り替えて着地
  have efac1 : qMul (qAdd (x.seq j) (qNeg (y.seq j))) (z.seq j)
      = qAdd (qMul (x.seq j) (z.seq j))
        (qNeg (qMul (y.seq j) (z.seq j))) := by
    rw [qMul_comm (qAdd (x.seq j) (qNeg (y.seq j))) (z.seq j),
      qMul_add (z.seq j) (x.seq j) (qNeg (y.seq j)),
      qMul_neg_right (z.seq j) (y.seq j),
      qMul_comm (z.seq j) (x.seq j), qMul_comm (z.seq j) (y.seq j)]
  exact qLe_trans _ _ _ (qLe_of_eq efac1.symm)
    (qLe_trans _ _ _ hmid0 hfold)

/-! ## M180-3: 点ごと核（望遠鏡 + ε-消去） -/

/-- **定理 (M180-3): 右乗法単調性の点ごと核** — x ≤ y（rLe）、
    0 ≤ z（rLe）のとき、左右で異なる添字加速 s₁ = mulIdx K₁ n・
    s₂ = mulIdx K₂ n を持つ積列の間の rLe 型不等式。

    証明: ε-消去 c = (K₁+K₁) + (中央定数 + (K₂+K₂))。任意の比較点 j で
    望遠鏡 x_{s₁}z_{s₁} → x_j z_j → y_j z_j → y_{s₂}z_{s₂} を組み、
    両外側は M180-1（片側読み）、中央は M180-2。s-項は相殺補題で
    u_n に、j-項は c/(j+1) に濃縮する。 -/
theorem rmul_le_seq (x y z : RReal) (hxy : rLe x y) (hz : rLe realZero z)
    (K₁ K₂ : Nat) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂)
    (hxK₁ : ∀ i, qLe (qAbs (x.seq i)) (ratOfInt.map (K₁ : Int)))
    (hzK₁ : ∀ i, qLe (qAbs (z.seq i)) (ratOfInt.map (K₁ : Int)))
    (hyK₂ : ∀ i, qLe (qAbs (y.seq i)) (ratOfInt.map (K₂ : Int)))
    (hzK₂ : ∀ i, qLe (qAbs (z.seq i)) (ratOfInt.map (K₂ : Int)))
    (n : Nat) :
    qLe (qMul (x.seq (mulIdx K₁ n)) (z.seq (mulIdx K₁ n)))
      (qAdd (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))
        (qAdd (qUnitFrac n) (qUnitFrac n))) := by
  apply qLe_of_forall_add_frac (K₁ + K₁ + (rBound z * 2 + 4
    + (rBound y + rBound y + (rBound x + rBound x)) + (K₂ + K₂)))
  intro j
  -- 外側ギャップ 1（片側読み）: x_{s₁}z_{s₁} − x_j z_j
  have t1 : qLe (qAdd (qMul (x.seq (mulIdx K₁ n)) (z.seq (mulIdx K₁ n)))
        (qNeg (qMul (x.seq j) (z.seq j))))
      (qAdd (qUnitFrac n) (qFrac (K₁ + K₁) j)) :=
    qLe_trans _ _ _ (qLe_self_abs _)
      (mul_idx_gap x z K₁ hK₁ hxK₁ hzK₁ n j)
  -- 中央ギャップ: x_j z_j − y_j z_j
  have t2 : qLe (qAdd (qMul (x.seq j) (z.seq j))
        (qNeg (qMul (y.seq j) (z.seq j))))
      (qFrac (rBound z * 2 + 4
        + (rBound y + rBound y + (rBound x + rBound x))) j) :=
    rmul_mid_gap hxy hz j
  -- 外側ギャップ 2（向きを反転して片側読み）: y_j z_j − y_{s₂}z_{s₂}
  have t3 : qLe (qAdd (qMul (y.seq j) (z.seq j))
        (qNeg (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))))
      (qAdd (qUnitFrac n) (qFrac (K₂ + K₂) j)) := by
    have e : qAbs (qAdd (qMul (y.seq j) (z.seq j))
          (qNeg (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))))
        = qAbs (qAdd (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))
          (qNeg (qMul (y.seq j) (z.seq j)))) := by
      rw [← qNeg_sub (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))
          (qMul (y.seq j) (z.seq j)),
        qAbs_neg]
    exact qLe_trans _ _ _ (qLe_self_abs _)
      (qLe_trans _ _ _ (qLe_of_eq e)
        (mul_idx_gap y z K₂ hK₂ hyK₂ hzK₂ n j))
  -- 望遠鏡分解
  have esplit : qAdd (qMul (x.seq (mulIdx K₁ n)) (z.seq (mulIdx K₁ n)))
        (qNeg (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n))))
      = qAdd (qAdd (qMul (x.seq (mulIdx K₁ n)) (z.seq (mulIdx K₁ n)))
          (qNeg (qMul (x.seq j) (z.seq j))))
        (qAdd (qAdd (qMul (x.seq j) (z.seq j))
            (qNeg (qMul (y.seq j) (z.seq j))))
          (qAdd (qMul (y.seq j) (z.seq j))
            (qNeg (qMul (y.seq (mulIdx K₂ n))
              (z.seq (mulIdx K₂ n)))))) := by
    rw [← qSub_split (qMul (x.seq j) (z.seq j))
        (qMul (y.seq j) (z.seq j))
        (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n))),
      ← qSub_split (qMul (x.seq (mulIdx K₁ n)) (z.seq (mulIdx K₁ n)))
        (qMul (x.seq j) (z.seq j))
        (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))]
  have total : qLe (qAdd (qMul (x.seq (mulIdx K₁ n)) (z.seq (mulIdx K₁ n)))
        (qNeg (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))))
      (qAdd (qAdd (qUnitFrac n) (qFrac (K₁ + K₁) j))
        (qAdd (qFrac (rBound z * 2 + 4
            + (rBound y + rBound y + (rBound x + rBound x))) j)
          (qAdd (qUnitFrac n) (qFrac (K₂ + K₂) j)))) :=
    qLe_trans _ _ _ (qLe_of_eq esplit)
      (qLe_add_two t1 (qLe_add_two t2 t3))
  -- 総和の組み替え (u_n + A) + (B + (u_n + C)) = (u_n + u_n) + (A + (B + C))
  have easm := qAdd_assemble (qUnitFrac n) (qFrac (K₁ + K₁) j)
    (qFrac (rBound z * 2 + 4
      + (rBound y + rBound y + (rBound x + rBound x))) j)
    (qFrac (K₂ + K₂) j)
  -- j-項の合併
  have hfold : qLe (qAdd (qFrac (K₁ + K₁) j)
        (qAdd (qFrac (rBound z * 2 + 4
            + (rBound y + rBound y + (rBound x + rBound x))) j)
          (qFrac (K₂ + K₂) j)))
      (qFrac (K₁ + K₁ + (rBound z * 2 + 4
        + (rBound y + rBound y + (rBound x + rBound x)) + (K₂ + K₂))) j) :=
    qLe_trans _ _ _
      (qLe_add_two (qLe_refl (qFrac (K₁ + K₁) j))
        (qFrac_add (rBound z * 2 + 4
          + (rBound y + rBound y + (rBound x + rBound x))) (K₂ + K₂) j))
      (qFrac_add (K₁ + K₁) (rBound z * 2 + 4
        + (rBound y + rBound y + (rBound x + rBound x)) + (K₂ + K₂)) j)
  have htotal : qLe (qAdd (qMul (x.seq (mulIdx K₁ n)) (z.seq (mulIdx K₁ n)))
        (qNeg (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
        (qFrac (K₁ + K₁ + (rBound z * 2 + 4
          + (rBound y + rBound y + (rBound x + rBound x))
          + (K₂ + K₂))) j)) :=
    qLe_trans _ _ _ total (qLe_trans _ _ _ (qLe_of_eq easm)
      (qLe_add_two (qLe_refl (qAdd (qUnitFrac n) (qUnitFrac n))) hfold))
  -- 移項して着地
  have hx := qLe_sub_move htotal
  have e5 : qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
        (qFrac (K₁ + K₁ + (rBound z * 2 + 4
          + (rBound y + rBound y + (rBound x + rBound x))
          + (K₂ + K₂))) j))
      (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))
      = qAdd (qAdd (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))
          (qAdd (qUnitFrac n) (qUnitFrac n)))
        (qFrac (K₁ + K₁ + (rBound z * 2 + 4
          + (rBound y + rBound y + (rBound x + rBound x))
          + (K₂ + K₂))) j) := by
    rw [qAdd_comm (qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
        (qFrac (K₁ + K₁ + (rBound z * 2 + 4
          + (rBound y + rBound y + (rBound x + rBound x))
          + (K₂ + K₂))) j))
        (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n))),
      ← qAdd_assoc (qMul (y.seq (mulIdx K₂ n)) (z.seq (mulIdx K₂ n)))
        (qAdd (qUnitFrac n) (qUnitFrac n))
        (qFrac (K₁ + K₁ + (rBound z * 2 + 4
          + (rBound y + rBound y + (rBound x + rBound x))
          + (K₂ + K₂))) j)]
  exact qLe_trans _ _ _ hx (qLe_of_eq e5)

/-! ## M180-4: 本丸 — rLe の乗法単調性 -/

/-- **定理 (M180-4a): 右乗法単調性（本丸）** — x ≤ y、0 ≤ z なら
    x·z ≤ y·z（rLe）。rmul の添字加速定数 K₁ = rBound x + rBound z と
    K₂ = rBound y + rBound z のズレは M180-3 の ε-消去が吸収する。 -/
theorem rmul_le_mul_right {x y z : RReal} (hxy : rLe x y)
    (hz : rLe realZero z) : rLe (rmul x z) (rmul y z) := by
  intro n
  exact rmul_le_seq x y z hxy hz
    (rBound x + rBound z) (rBound y + rBound z)
    (rBound_pair_pos x z) (rBound_pair_pos y z)
    (fun i => qLe_trans _ _ _ (rBound_spec x i) (ratOfInt_le (by omega)))
    (fun i => qLe_trans _ _ _ (rBound_spec z i) (ratOfInt_le (by omega)))
    (fun i => qLe_trans _ _ _ (rBound_spec y i) (ratOfInt_le (by omega)))
    (fun i => qLe_trans _ _ _ (rBound_spec z i) (ratOfInt_le (by omega)))
    n

/-- **定理 (M180-4b): 左乗法単調性** — x ≤ y、0 ≤ z なら z·x ≤ z·y
    （可換 rmul_comm と rLe_congr で右版に還元）。 -/
theorem rmul_le_mul_left {x y : RReal} (z : RReal) (hxy : rLe x y)
    (hz : rLe realZero z) : rLe (rmul z x) (rmul z y) :=
  rLe_congr (rmul_comm x z) (rmul_comm y z) (rmul_le_mul_right hxy hz)

/-! ## M180-5: 冪の単調性 -/

/-- **定理 (M180-5a): 冪の非負性** — 0 ≤ a なら 0 ≤ a^k。
    k = 0 は 0 ≤ 1、k+1 は 0 ≈ 0·a ≤ a^k·a（M180-4a + rmul_zero）。 -/
theorem realPow_nonneg {a : RReal} (ha : rLe realZero a) :
    ∀ k, rLe realZero (realPow a k) := by
  intro k
  induction k with
  | zero =>
    intro n
    have h1 : qLe ratRing.zero ratRing.one := by
      show (0 : Int) * 1 ≤ (1 : Int) * 1
      omega
    have h2 := qLe_add_two h1 (qFrac_add_nonneg 1 n 1 n)
    rw [qAdd_zero_left] at h2
    exact h2
  | succ k ih =>
    have hstep : rLe (rmul realZero a) (rmul (realPow a k) a) :=
      rmul_le_mul_right ih ha
    have hz0 : realEq (rmul realZero a) realZero :=
      realEq_trans (rmul_comm realZero a) (rmul_zero a)
    exact rLe_congr hz0 (realEq_refl (rmul (realPow a k) a)) hstep

/-- **定理 (M180-5b): 冪の単調性** — 0 ≤ a、a ≤ b なら a^k ≤ b^k。
    k の帰納で a^k·a ≤ b^k·a ≤ b^k·b（M180-4a を二度、後者は
    可換 congruence 経由で底の比較に M180-5a の非負性を使う）。 -/
theorem realPow_le {a b : RReal} (ha : rLe realZero a) (hab : rLe a b) :
    ∀ k, rLe (realPow a k) (realPow b k) := by
  intro k
  induction k with
  | zero => exact rLe_refl (qToReal ratRing.one)
  | succ k ih =>
    have hb : rLe realZero b := rLe_trans ha hab
    have h1 : rLe (rmul (realPow a k) a) (rmul (realPow b k) a) :=
      rmul_le_mul_right ih ha
    have h2 : rLe (rmul a (realPow b k)) (rmul b (realPow b k)) :=
      rmul_le_mul_right hab (realPow_nonneg hb k)
    have h3 : rLe (rmul (realPow b k) a) (rmul (realPow b k) b) :=
      rLe_congr (rmul_comm a (realPow b k)) (rmul_comm b (realPow b k)) h2
    exact rLe_trans h1 h3

/-! ## M180-6: 総括 -/

/-- **M180-6a: 総括** — 実数乗法の順序単調性データ。 -/
structure RealMulOrderData where
  /-- 右乗法単調性（本丸）。 -/
  mul_le_right : ∀ {x y z : RReal}, rLe x y → rLe realZero z →
    rLe (rmul x z) (rmul y z)
  /-- 左乗法単調性。 -/
  mul_le_left : ∀ {x y : RReal} (z : RReal), rLe x y → rLe realZero z →
    rLe (rmul z x) (rmul z y)
  /-- 冪の非負性。 -/
  pow_nonneg : ∀ {a : RReal}, rLe realZero a →
    ∀ k, rLe realZero (realPow a k)
  /-- 冪の単調性。 -/
  pow_le : ∀ {a b : RReal}, rLe realZero a → rLe a b →
    ∀ k, rLe (realPow a k) (realPow b k)

/-- **M180-6b: witness**。 -/
def realMulOrderData : RealMulOrderData where
  mul_le_right := rmul_le_mul_right
  mul_le_left := rmul_le_mul_left
  pow_nonneg := realPow_nonneg
  pow_le := realPow_le

/-- **M180-6c: 存在**。 -/
theorem realMulOrder_exists : Nonempty RealMulOrderData :=
  ⟨realMulOrderData⟩

end IUT
