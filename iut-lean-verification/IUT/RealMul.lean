/-
# M123F: 実数の乗法 — Bishop 流添字スケーリング

柱C（issue #37）「ℝ の自前構成」の第四段（M115F ℚ → M117F 正則列 →
M120F 床関数・標準上界に続く）。標準上界 K = rBound x + rBound y による
添字加速 s n = 2K(n+1) − 1 で積の正則性を維持する Bishop 流の実数乗法。
|ab − cd| ≤ |a||b−d| + |d||a−c| の分解と
K·(1/(2K(m+1))) = 1/(2(m+1)) の相殺が核。

  * M123F-1 乗法ラッパー — `qMul_comm`/`qMul_assoc`/`qMul_one`/
    `qMul_zero`/`qMul_add`/`qMul_neg_left`/`qMul_neg_right`
    （ratRing の法則を qMul 構文で再輸出）
  * M123F-2 乗法の単調性 — 加法の橋 `qLe_sub_nonneg`/`qLe_of_sub_nonneg`
    経由で `qLe_mul_right`・両側版 `qLe_mul_two`
  * M123F-3 積の差の分解 — `qAbs_mul_sub`:
    |ab − cd| ≤ |a||b−d| + |d||a−c|（等式 ab − cd = a(b−d) + d(a−c)）
  * M123F-4 添字スケール — `mulIdx K n = 2K(n+1) − 1` と
    キャスト橋 `mulIdx_cast`・下界 `mulIdx_ge`
  * M123F-5 スカラー×分数 — `ratOfInt_mul_qFrac`: k·(c/(m+1)) = kc/(m+1)
    と相殺補題 `qFrac_two_bound`: (K+K)/(mulIdx K t + 1) ≤ 1/(t+1)
  * M123F-6 本丸 `rmul` — z_n := x_{s n}·y_{s n}（s n = mulIdx K n、
    K = rBound x + rBound y）の正則性 `mul_seq_reg`
  * M123F-7 法則 — 可換・congruence（4 点比較 + ε-消去）・単位元・
    零元・埋め込みの乗法性
  * M123F-8 `RealMulData` — 総括

正直申告: 乗法の結合律・加法との分配律は次層（添字スケールが三重に
ズレるため 4 点比較の一般化が要る）。congruence は ε-消去
（c = 4K + 2K'）で本層に収めた。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RatFloor

namespace IUT

/-! ## M123F-1: 乗法ラッパー（ratRing の法則を qMul 構文で再輸出） -/

/-- 乗法の可換則（ラッパー）。 -/
theorem qMul_comm (a b : QRat) : qMul a b = qMul b a := ratRing.mul_comm a b

/-- 乗法の結合則（ラッパー）。 -/
theorem qMul_assoc (a b c : QRat) :
    qMul (qMul a b) c = qMul a (qMul b c) := ratRing.mul_assoc a b c

/-- 右単位元（one_mul + 可換から導出）。 -/
theorem qMul_one (a : QRat) : qMul a ratRing.one = a := by
  rw [qMul_comm]
  exact ratRing.one_mul a

/-- 右零元 a·0 = 0（CRing.mul_zero のラッパー）。 -/
theorem qMul_zero (a : QRat) : qMul a ratRing.zero = ratRing.zero :=
  ratRing.mul_zero a

/-- 左分配（ラッパー）。 -/
theorem qMul_add (a b c : QRat) :
    qMul a (qAdd b c) = qAdd (qMul a b) (qMul a c) :=
  ratRing.left_distrib a b c

/-- 反元の左乗法分配 (−a)·c = −(ac)（反元の一意性から導出）。 -/
theorem qMul_neg_left (a c : QRat) : qMul (qNeg a) c = qNeg (qMul a c) := by
  have h0 : qAdd (qMul a c) (qMul (qNeg a) c) = ratRing.zero := by
    rw [qMul_comm a c, qMul_comm (qNeg a) c, ← qMul_add, qAdd_neg_self,
      qMul_zero]
  exact qNeg_unique h0

/-- 反元の右乗法分配 a·(−d) = −(ad)（可換 + 左版）。 -/
theorem qMul_neg_right (a d : QRat) : qMul a (qNeg d) = qNeg (qMul a d) := by
  rw [qMul_comm a (qNeg d), qMul_neg_left, qMul_comm d a]

/-! ## M123F-2: 乗法の単調性 -/

/-- qLe と加法の橋（順方向）: a ≤ b なら 0 ≤ b − a。 -/
theorem qLe_sub_nonneg {a b : QRat} (h : qLe a b) :
    qLe ratRing.zero (qAdd b (qNeg a)) := by
  have h1 := qLe_add a b (qNeg a) h
  rw [qAdd_neg_self a] at h1
  exact h1

/-- qLe と加法の橋（逆方向）: 0 ≤ b − a なら a ≤ b。 -/
theorem qLe_of_sub_nonneg {a b : QRat}
    (h : qLe ratRing.zero (qAdd b (qNeg a))) : qLe a b := by
  have h1 := qLe_add ratRing.zero (qAdd b (qNeg a)) a h
  rw [qAdd_zero_left, qAdd_assoc, qNeg_add_self a, qAdd_zero] at h1
  exact h1

/-- **定理 (M123F-2a): 乗法の右単調性** — a ≤ b, 0 ≤ c なら ac ≤ bc
    （0 ≤ (b−a)c に還元して非負積閉性 `qLe_mul_nonneg` で閉じる）。 -/
theorem qLe_mul_right {a b c : QRat} (h : qLe a b)
    (hc : qLe ratRing.zero c) : qLe (qMul a c) (qMul b c) := by
  have h1 : qLe ratRing.zero (qAdd b (qNeg a)) := qLe_sub_nonneg h
  have h2 : qLe ratRing.zero (qMul (qAdd b (qNeg a)) c) :=
    qLe_mul_nonneg _ _ h1 hc
  have e : qMul (qAdd b (qNeg a)) c = qAdd (qMul b c) (qNeg (qMul a c)) := by
    rw [qMul_comm (qAdd b (qNeg a)) c, qMul_add c b (qNeg a),
      qMul_comm c b, qMul_comm c (qNeg a), qMul_neg_left a c]
  rw [e] at h2
  exact qLe_of_sub_nonneg h2

/-- **乗法の両側単調性** — a ≤ a', b ≤ b', 0 ≤ b, 0 ≤ a' なら ab ≤ a'b'
    （右単調性 2 回 + 可換）。 -/
theorem qLe_mul_two {a a' b b' : QRat} (ha : qLe a a') (hb : qLe b b')
    (hb0 : qLe ratRing.zero b) (ha'0 : qLe ratRing.zero a') :
    qLe (qMul a b) (qMul a' b') := by
  have h1 : qLe (qMul a b) (qMul a' b) := qLe_mul_right ha hb0
  have h2 : qLe (qMul b a') (qMul b' a') := qLe_mul_right hb ha'0
  rw [qMul_comm b a', qMul_comm b' a'] at h2
  exact qLe_trans _ _ _ h1 h2

/-! ## M123F-3: 積の差の分解 -/

/-- 積の差の恒等式 ab − cd = a(b−d) + d(a−c)（rw 連鎖）。 -/
theorem qMul_sub_expand (a b c d : QRat) :
    qAdd (qMul a b) (qNeg (qMul c d))
      = qAdd (qMul a (qAdd b (qNeg d))) (qMul d (qAdd a (qNeg c))) := by
  rw [qMul_add a b (qNeg d), qMul_add d a (qNeg c),
    qMul_neg_right a d, qMul_neg_right d c,
    qMul_comm d a, qMul_comm d c,
    ← qSub_split (qMul a b) (qMul a d) (qMul c d)]

/-- **定理 (M123F-3a): 積の差の分解** —
    |ab − cd| ≤ |a||b−d| + |d||a−c|（恒等式 + 三角不等式 + |xy|=|x||y|）。 -/
theorem qAbs_mul_sub (a b c d : QRat) :
    qLe (qAbs (qAdd (qMul a b) (qNeg (qMul c d))))
      (qAdd (qMul (qAbs a) (qAbs (qAdd b (qNeg d))))
        (qMul (qAbs d) (qAbs (qAdd a (qNeg c))))) := by
  rw [qMul_sub_expand a b c d]
  have h := qAbs_add_le (qMul a (qAdd b (qNeg d))) (qMul d (qAdd a (qNeg c)))
  rw [qAbs_mul a (qAdd b (qNeg d)), qAbs_mul d (qAdd a (qNeg c))] at h
  exact h

/-- 4 項組み替え (u+A)+(B+(u+C)) = (u+u)+(A+(B+C))
    （congruence の総和整理用）。 -/
theorem qAdd_assemble (u A B C : QRat) :
    qAdd (qAdd u A) (qAdd B (qAdd u C))
      = qAdd (qAdd u u) (qAdd A (qAdd B C)) := by
  rw [qAdd_swap_mid u A B (qAdd u C), qAdd_comm A (qAdd u C),
    qAdd_assoc u C A, qAdd_swap_mid u B u (qAdd C A), qAdd_comm C A,
    ← qAdd_assoc B A C, qAdd_comm B A, qAdd_assoc A B C]

/-! ## M123F-4: 添字スケール -/

/-- **M123F-4a: 添字スケール** s n = 2K(n+1) − 1（K ≥ 1 で全単調）。 -/
def mulIdx (K n : Nat) : Nat := 2 * K * (n + 1) - 1

/-- s n + 1 = 2K(n+1)（K ≥ 1 で切り捨てが起きない）。 -/
theorem mulIdx_succ (K n : Nat) (hK : 1 ≤ K) :
    mulIdx K n + 1 = 2 * K * (n + 1) := by
  have h1 : 0 < 2 * K * (n + 1) := Nat.mul_pos (by omega) (Nat.succ_pos n)
  show 2 * K * (n + 1) - 1 + 1 = 2 * K * (n + 1)
  omega

/-- **M123F-4b: キャスト橋** ((s n : Nat) : Int) + 1 = 2K(n+1)
    （↑(a·b) と ↑a·↑b の橋渡しは `Int.natCast_mul`）。 -/
theorem mulIdx_cast (K n : Nat) (hK : 1 ≤ K) :
    ((mulIdx K n : Nat) : Int) + 1 = 2 * (K : Int) * ((n : Int) + 1) := by
  have h : ((mulIdx K n + 1 : Nat) : Int) = ((2 * K * (n + 1) : Nat) : Int) := by
    rw [mulIdx_succ K n hK]
  rw [Int.natCast_mul, Int.natCast_mul] at h
  have e1 : ((mulIdx K n + 1 : Nat) : Int)
      = ((mulIdx K n : Nat) : Int) + 1 := by omega
  have e2 : (((2 : Nat)) : Int) = (2 : Int) := rfl
  have e3 : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
  rw [e1, e2, e3] at h
  exact h

/-- **M123F-4c: 添字の下界** n ≤ s n（2K(n+1) ≥ 2(n+1) から）。 -/
theorem mulIdx_ge (K n : Nat) (hK : 1 ≤ K) : n ≤ mulIdx K n := by
  have h1 : 2 * 1 * (n + 1) ≤ 2 * K * (n + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 2) hK) (Nat.le_refl (n + 1))
  have h2 := mulIdx_succ K n hK
  omega

/-! ## M123F-5: スカラー×分数と相殺補題 -/

/-- ratOfInt の ≤ 橋: a ≤ b なら (a : ℚ) ≤ (b : ℚ)（代表計算）。 -/
theorem ratOfInt_le {a b : Int} (h : a ≤ b) :
    qLe (ratOfInt.map a) (ratOfInt.map b) := by
  show a * 1 ≤ b * 1
  omega

/-- **M123F-5a: スカラー×分数** k·(c/(m+1)) = kc/(m+1)
    （Quot.sound の交差積 + `Int.natCast_mul`）。 -/
theorem ratOfInt_mul_qFrac (k c m : Nat) :
    qMul (ratOfInt.map ((k : Nat) : Int)) (qFrac c m) = qFrac (k * c) m := by
  apply Quot.sound
  show (k : Int) * (c : Int) * ((m : Int) + 1)
    = ((k * c : Nat) : Int) * (1 * ((m : Int) + 1))
  rw [Int.natCast_mul, Int.one_mul]

/-- スカラー×単位分数 k·(1/(s+1)) = k/(s+1)。 -/
theorem ratOfInt_mul_unitFrac (k s : Nat) :
    qMul (ratOfInt.map ((k : Nat) : Int)) (qUnitFrac s) = qFrac k s := by
  have h := ratOfInt_mul_qFrac k 1 s
  rw [Nat.mul_one] at h
  exact h

/-- **定理 (M123F-5b): 相殺補題（核）** —
    (K+K)/(mulIdx K t + 1) = 2K/(2K(t+1)) = 1/(t+1)。 -/
theorem qFrac_two_bound (K t : Nat) (hK : 1 ≤ K) :
    qLe (qFrac (K + K) (mulIdx K t)) (qUnitFrac t) := by
  apply qFrac_le
  apply Int.le_of_eq
  rw [mulIdx_cast K t hK]
  have e1 : ((K + K : Nat) : Int) = 2 * (K : Int) := by omega
  have e2 : ((1 : Nat) : Int) = (1 : Int) := rfl
  rw [e1, e2, Int.one_mul]

/-! ## M123F-6: 本丸 — 乗法の定義と正則性 -/

/-- 標準上界の対和は正（rBound = floorNat + 3 ≥ 3）。 -/
theorem rBound_pair_pos (x y : RReal) : 1 ≤ rBound x + rBound y := by
  show 1 ≤ qFloorNat (qAbs (x.seq 0)) + 3 + (qFloorNat (qAbs (y.seq 0)) + 3)
  omega

/-- **定理 (M123F-6a): 加速積列の正則性（一般形）** — K を両列の一様上界
    （K ≥ 1）とすると z_n = x_{s n}·y_{s n}（s = mulIdx K）は正則:
    |z_m − z_n| ≤ |x_{sm}||y_{sm} − y_{sn}| + |y_{sn}||x_{sm} − x_{sn}|
    ≤ K(u_{sm}+u_{sn}) + K(u_{sm}+u_{sn}) ≤ (K+K)/(sm+1) + (K+K)/(sn+1)
    = u_m + u_n（相殺補題）。 -/
theorem mul_seq_reg (x y : RReal) (K : Nat) (hK : 1 ≤ K)
    (hxK : ∀ i, qLe (qAbs (x.seq i)) (ratOfInt.map (K : Int)))
    (hyK : ∀ i, qLe (qAbs (y.seq i)) (ratOfInt.map (K : Int)))
    (m n : Nat) :
    qLe (qAbs (qAdd (qMul (x.seq (mulIdx K m)) (y.seq (mulIdx K m)))
        (qNeg (qMul (x.seq (mulIdx K n)) (y.seq (mulIdx K n))))))
      (qAdd (qUnitFrac m) (qUnitFrac n)) := by
  -- b1: 積差の分解
  have b1 := qAbs_mul_sub (x.seq (mulIdx K m)) (y.seq (mulIdx K m))
    (x.seq (mulIdx K n)) (y.seq (mulIdx K n))
  -- b2: 各項を K·(u_{sm}+u_{sn}) で押さえる
  have hKnn : qLe ratRing.zero (ratOfInt.map (K : Int)) :=
    qLe_trans _ _ _ (qAbs_nonneg (x.seq (mulIdx K m))) (hxK (mulIdx K m))
  have t1 : qLe (qMul (qAbs (x.seq (mulIdx K m)))
        (qAbs (qAdd (y.seq (mulIdx K m)) (qNeg (y.seq (mulIdx K n))))))
      (qMul (ratOfInt.map (K : Int))
        (qAdd (qUnitFrac (mulIdx K m)) (qUnitFrac (mulIdx K n)))) :=
    qLe_mul_two (hxK (mulIdx K m)) (y.reg (mulIdx K m) (mulIdx K n))
      (qAbs_nonneg _) hKnn
  have t2 : qLe (qMul (qAbs (y.seq (mulIdx K n)))
        (qAbs (qAdd (x.seq (mulIdx K m)) (qNeg (x.seq (mulIdx K n))))))
      (qMul (ratOfInt.map (K : Int))
        (qAdd (qUnitFrac (mulIdx K m)) (qUnitFrac (mulIdx K n)))) :=
    qLe_mul_two (hyK (mulIdx K n)) (x.reg (mulIdx K m) (mulIdx K n))
      (qAbs_nonneg _) hKnn
  have b2 := qLe_trans _ _ _ b1 (qLe_add_two t1 t2)
  -- b3: qFrac 化 K·(u_{sm}+u_{sn}) = qFrac K sm + qFrac K sn
  have eT : qMul (ratOfInt.map (K : Int))
        (qAdd (qUnitFrac (mulIdx K m)) (qUnitFrac (mulIdx K n)))
      = qAdd (qFrac K (mulIdx K m)) (qFrac K (mulIdx K n)) := by
    rw [qMul_add, ratOfInt_mul_unitFrac, ratOfInt_mul_unitFrac]
  rw [eT] at b2
  -- b4: 並べ替え → 同分母合併 → 相殺補題で u_m + u_n へ
  have swap : qAdd (qAdd (qFrac K (mulIdx K m)) (qFrac K (mulIdx K n)))
        (qAdd (qFrac K (mulIdx K m)) (qFrac K (mulIdx K n)))
      = qAdd (qAdd (qFrac K (mulIdx K m)) (qFrac K (mulIdx K m)))
        (qAdd (qFrac K (mulIdx K n)) (qFrac K (mulIdx K n))) :=
    qAdd_swap_mid _ _ _ _
  have fold_m : qLe (qAdd (qFrac K (mulIdx K m)) (qFrac K (mulIdx K m)))
      (qUnitFrac m) :=
    qLe_trans _ _ _ (qFrac_add K K (mulIdx K m)) (qFrac_two_bound K m hK)
  have fold_n : qLe (qAdd (qFrac K (mulIdx K n)) (qFrac K (mulIdx K n)))
      (qUnitFrac n) :=
    qLe_trans _ _ _ (qFrac_add K K (mulIdx K n)) (qFrac_two_bound K n hK)
  exact qLe_trans _ _ _ b2 (qLe_trans _ _ _ (qLe_of_eq swap)
    (qLe_add_two fold_m fold_n))

/-- **M123F-6b: 実数の乗法** — K = rBound x + rBound y で添字を加速した
    積列。正則性は `mul_seq_reg`（上界は `rBound_spec` から）。 -/
def rmul (x y : RReal) : RReal where
  seq := fun n => qMul (x.seq (mulIdx (rBound x + rBound y) n))
    (y.seq (mulIdx (rBound x + rBound y) n))
  reg := by
    intro m n
    exact mul_seq_reg x y (rBound x + rBound y) (rBound_pair_pos x y)
      (fun i => qLe_trans _ _ _ (rBound_spec x i) (ratOfInt_le (by omega)))
      (fun i => qLe_trans _ _ _ (rBound_spec y i) (ratOfInt_le (by omega)))
      m n

/-! ## M123F-7: 法則 -/

/-- **定理 (M123F-7a): 可換律** — K = rBound x + rBound y と
    rBound y + rBound x の一致は Nat.add_comm で列の等式に落とす。 -/
theorem rmul_comm (x y : RReal) : realEq (rmul x y) (rmul y x) := by
  apply realEq_of_seq_eq
  intro n
  show qMul (x.seq (mulIdx (rBound x + rBound y) n))
      (y.seq (mulIdx (rBound x + rBound y) n))
    = qMul (y.seq (mulIdx (rBound y + rBound x) n))
      (x.seq (mulIdx (rBound y + rBound x) n))
  rw [Nat.add_comm (rBound y) (rBound x), qMul_comm]

/-- **定理 (M123F-7b): 右単位元** x·1 ≈ x — 添字ズレ x_{s n} vs x_n は
    正則性 + s n ≥ n（`mulIdx_ge`）で吸収。 -/
theorem rmul_one (x : RReal) : realEq (rmul x (qToReal ratRing.one)) x := by
  intro n
  have hK : 1 ≤ rBound x + rBound (qToReal ratRing.one) :=
    rBound_pair_pos x (qToReal ratRing.one)
  have hge : n ≤ mulIdx (rBound x + rBound (qToReal ratRing.one)) n :=
    mulIdx_ge (rBound x + rBound (qToReal ratRing.one)) n hK
  show qLe (qAbs (qAdd
      (qMul (x.seq (mulIdx (rBound x + rBound (qToReal ratRing.one)) n))
        ratRing.one)
      (qNeg (x.seq n))))
    (qAdd (qUnitFrac n) (qUnitFrac n))
  rw [qMul_one]
  exact qLe_trans _ _ _
    (x.reg (mulIdx (rBound x + rBound (qToReal ratRing.one)) n) n)
    (qLe_add_two (qFrac_le (by omega)) (qLe_refl (qUnitFrac n)))

/-- **定理 (M123F-7c): 零元** x·0 ≈ 0（点ごと qMul_zero）。 -/
theorem rmul_zero (x : RReal) : realEq (rmul x realZero) realZero := by
  apply realEq_of_seq_eq
  intro n
  show qMul (x.seq (mulIdx (rBound x + rBound realZero) n)) ratRing.zero
    = ratRing.zero
  exact qMul_zero _

/-- **定理 (M123F-7d): 埋め込みの乗法性**（定数列は添字に依らない）。 -/
theorem qToReal_mul (a b : QRat) :
    realEq (rmul (qToReal a) (qToReal b)) (qToReal (qMul a b)) :=
  realEq_of_seq_eq (fun _ => rfl)

/-- **定理 (M123F-7e): congruence の核（一般形）** — x ≈ x' のとき
    加速添字 s = mulIdx K n・s' = mulIdx K' n が K ≠ K' でズレても、
    4 点比較 x_s y_s → x_j y_j → x'_j y_j → x'_{s'} y_{s'}（∀j）で
    |z_n − z'_n| ≤ 2/(n+1) + (4K+2K')/(j+1) を作り ε-消去で閉じる。 -/
theorem mul_seq_congr (x x' y : RReal) (K K' : Nat)
    (hK : 1 ≤ K) (hK' : 1 ≤ K')
    (hxK : ∀ i, qLe (qAbs (x.seq i)) (ratOfInt.map (K : Int)))
    (hyK : ∀ i, qLe (qAbs (y.seq i)) (ratOfInt.map (K : Int)))
    (hx'K : ∀ i, qLe (qAbs (x'.seq i)) (ratOfInt.map (K' : Int)))
    (hyK' : ∀ i, qLe (qAbs (y.seq i)) (ratOfInt.map (K' : Int)))
    (h : realEq x x') (n : Nat) :
    qLe (qAbs (qAdd (qMul (x.seq (mulIdx K n)) (y.seq (mulIdx K n)))
        (qNeg (qMul (x'.seq (mulIdx K' n)) (y.seq (mulIdx K' n))))))
      (qAdd (qUnitFrac n) (qUnitFrac n)) := by
  apply qLe_of_forall_add_frac (K + K + (K + K + (K' + K')))
  intro j
  have hKnn : qLe ratRing.zero (ratOfInt.map (K : Int)) :=
    qLe_trans _ _ _ (qAbs_nonneg (y.seq j)) (hyK j)
  have hK'nn : qLe ratRing.zero (ratOfInt.map (K' : Int)) :=
    qLe_trans _ _ _ (qAbs_nonneg (y.seq j)) (hyK' j)
  -- 4 点分割: P → Q1 → Q2 → R
  have split1 := qAbs_sub_split
    (qMul (x.seq (mulIdx K n)) (y.seq (mulIdx K n)))
    (qMul (x.seq j) (y.seq j))
    (qMul (x'.seq (mulIdx K' n)) (y.seq (mulIdx K' n)))
  have split2 := qAbs_sub_split
    (qMul (x.seq j) (y.seq j))
    (qMul (x'.seq j) (y.seq j))
    (qMul (x'.seq (mulIdx K' n)) (y.seq (mulIdx K' n)))
  -- Gap1: |x_s y_s − x_j y_j| ≤ u_n + (K+K)/(j+1)
  have hg1 : qLe (qAbs (qAdd
        (qMul (x.seq (mulIdx K n)) (y.seq (mulIdx K n)))
        (qNeg (qMul (x.seq j) (y.seq j)))))
      (qAdd (qUnitFrac n) (qFrac (K + K) j)) := by
    have b := qAbs_mul_sub (x.seq (mulIdx K n)) (y.seq (mulIdx K n))
      (x.seq j) (y.seq j)
    have t1 := qLe_mul_two (hxK (mulIdx K n)) (y.reg (mulIdx K n) j)
      (qAbs_nonneg _) hKnn
    have t2 := qLe_mul_two (hyK j) (x.reg (mulIdx K n) j)
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
  -- Gap2: |x_j y_j − x'_j y_j| ≤ (K+K)/(j+1)（realEq の使用点）
  have hg2 : qLe (qAbs (qAdd (qMul (x.seq j) (y.seq j))
        (qNeg (qMul (x'.seq j) (y.seq j)))))
      (qFrac (K + K) j) := by
    have b := qAbs_mul_sub (x.seq j) (y.seq j) (x'.seq j) (y.seq j)
    rw [qAbs_self_sub (y.seq j), qMul_zero, qAdd_zero_left] at b
    have t := qLe_mul_two (hyK j) (h j) (qAbs_nonneg _) hKnn
    have eT : qMul (ratOfInt.map (K : Int))
          (qAdd (qUnitFrac j) (qUnitFrac j))
        = qAdd (qFrac K j) (qFrac K j) := by
      rw [qMul_add, ratOfInt_mul_unitFrac]
    rw [eT] at t
    exact qLe_trans _ _ _ b (qLe_trans _ _ _ t (qFrac_add K K j))
  -- Gap3: |x'_j y_j − x'_{s'} y_{s'}| ≤ u_n + (K'+K')/(j+1)
  have hg3 : qLe (qAbs (qAdd (qMul (x'.seq j) (y.seq j))
        (qNeg (qMul (x'.seq (mulIdx K' n)) (y.seq (mulIdx K' n))))))
      (qAdd (qUnitFrac n) (qFrac (K' + K') j)) := by
    have b := qAbs_mul_sub (x'.seq j) (y.seq j)
      (x'.seq (mulIdx K' n)) (y.seq (mulIdx K' n))
    have t1 := qLe_mul_two (hx'K j) (y.reg j (mulIdx K' n))
      (qAbs_nonneg _) hK'nn
    have t2 := qLe_mul_two (hyK' (mulIdx K' n)) (x'.reg j (mulIdx K' n))
      (qAbs_nonneg _) hK'nn
    have b2 := qLe_trans _ _ _ b (qLe_add_two t1 t2)
    have eT : qMul (ratOfInt.map (K' : Int))
          (qAdd (qUnitFrac j) (qUnitFrac (mulIdx K' n)))
        = qAdd (qFrac K' j) (qFrac K' (mulIdx K' n)) := by
      rw [qMul_add, ratOfInt_mul_unitFrac, ratOfInt_mul_unitFrac]
    rw [eT] at b2
    have swap2 : qAdd (qAdd (qFrac K' j) (qFrac K' (mulIdx K' n)))
          (qAdd (qFrac K' j) (qFrac K' (mulIdx K' n)))
        = qAdd (qAdd (qFrac K' (mulIdx K' n)) (qFrac K' (mulIdx K' n)))
          (qAdd (qFrac K' j) (qFrac K' j)) := by
      rw [qAdd_swap_mid (qFrac K' j) (qFrac K' (mulIdx K' n))
          (qFrac K' j) (qFrac K' (mulIdx K' n)),
        qAdd_comm (qAdd (qFrac K' j) (qFrac K' j))
          (qAdd (qFrac K' (mulIdx K' n)) (qFrac K' (mulIdx K' n)))]
    have fold1 : qLe (qAdd (qFrac K' (mulIdx K' n)) (qFrac K' (mulIdx K' n)))
        (qUnitFrac n) :=
      qLe_trans _ _ _ (qFrac_add K' K' (mulIdx K' n)) (qFrac_two_bound K' n hK')
    exact qLe_trans _ _ _ b2 (qLe_trans _ _ _ (qLe_of_eq swap2)
      (qLe_add_two fold1 (qFrac_add K' K' j)))
  -- 総和の組み替えと分数の合併
  have total := qLe_trans _ _ _ split1
    (qLe_add_two hg1 (qLe_trans _ _ _ split2 (qLe_add_two hg2 hg3)))
  have easm := qAdd_assemble (qUnitFrac n) (qFrac (K + K) j)
    (qFrac (K + K) j) (qFrac (K' + K') j)
  have hfold : qLe (qAdd (qFrac (K + K) j)
        (qAdd (qFrac (K + K) j) (qFrac (K' + K') j)))
      (qFrac (K + K + (K + K + (K' + K'))) j) :=
    qLe_trans _ _ _
      (qLe_add_two (qLe_refl (qFrac (K + K) j)) (qFrac_add (K + K) (K' + K') j))
      (qFrac_add (K + K) (K + K + (K' + K')) j)
  exact qLe_trans _ _ _ total (qLe_trans _ _ _ (qLe_of_eq easm)
    (qLe_add_two (qLe_refl (qAdd (qUnitFrac n) (qUnitFrac n))) hfold))

/-- **定理 (M123F-7f): 左 congruence** — x ≈ x' なら x·y ≈ x'·y
    （K = rBound x + rBound y と K' = rBound x' + rBound y が異なっても
    `mul_seq_congr` の ε-消去が吸収）。 -/
theorem rmul_congr_left {x x' : RReal} (y : RReal) (h : realEq x x') :
    realEq (rmul x y) (rmul x' y) := by
  intro n
  exact mul_seq_congr x x' y (rBound x + rBound y) (rBound x' + rBound y)
    (rBound_pair_pos x y) (rBound_pair_pos x' y)
    (fun i => qLe_trans _ _ _ (rBound_spec x i) (ratOfInt_le (by omega)))
    (fun i => qLe_trans _ _ _ (rBound_spec y i) (ratOfInt_le (by omega)))
    (fun i => qLe_trans _ _ _ (rBound_spec x' i) (ratOfInt_le (by omega)))
    (fun i => qLe_trans _ _ _ (rBound_spec y i) (ratOfInt_le (by omega)))
    h n

/-- **定理 (M123F-7g): 右 congruence**（可換 + 左 congruence）。 -/
theorem rmul_congr_right (x : RReal) {y y' : RReal} (h : realEq y y') :
    realEq (rmul x y) (rmul x y') :=
  realEq_trans (rmul_comm x y)
    (realEq_trans (rmul_congr_left x h) (rmul_comm y' x))

/-! ## M123F-8: 総括 -/

/-- **M123F-8a: 総括** — 実数乗法の法則束（≈ の下）。 -/
structure RealMulData where
  /-- 可換律。 -/
  mul_comm : ∀ x y, realEq (rmul x y) (rmul y x)
  /-- 左 congruence。 -/
  mul_congr_left : ∀ {x x'} (y), realEq x x' →
    realEq (rmul x y) (rmul x' y)
  /-- 右 congruence。 -/
  mul_congr_right : ∀ (x) {y y'}, realEq y y' →
    realEq (rmul x y) (rmul x y')
  /-- 単位元。 -/
  mul_one : ∀ x, realEq (rmul x (qToReal ratRing.one)) x
  /-- 零元。 -/
  mul_zero : ∀ x, realEq (rmul x realZero) realZero
  /-- 埋め込みの乗法性。 -/
  embed_mul : ∀ a b, realEq (rmul (qToReal a) (qToReal b))
    (qToReal (qMul a b))

/-- **M123F-8b: witness**。 -/
def realMulData : RealMulData where
  mul_comm := rmul_comm
  mul_congr_left := rmul_congr_left
  mul_congr_right := rmul_congr_right
  mul_one := rmul_one
  mul_zero := rmul_zero
  embed_mul := qToReal_mul

/-- **M123F-8c: 存在**。 -/
theorem realMul_exists : Nonempty RealMulData :=
  ⟨realMulData⟩

end IUT
