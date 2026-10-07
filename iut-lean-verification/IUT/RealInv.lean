/-
# M145: 正値実数の逆元 — ℝ の乗法逆元の構成（柱C 本線）

M115F の正直申告「逆元の体公理は代表 witness 形」を実数まで持ち上げ、
**正値実数（IsPos）の乗法逆元を選択公理なしに構成**する。

設計の鍵は二つ:
  (1) **添字シフト rshift** — IsPos の witness N から尾部一様下界
      1/(2N+2) ≤ x'_m（∀m）を持つ realEq-同値な実数を作る
  (2) **ミニ極限補題 realEq_qconst_of_bound** — 速度 C の定数近似
      |w_n − y| ≤ C/(n+1) は realEq w (qToReal y) を与える
      （望遠鏡 + ε-消去 c = C+1。rmul の添字スケジュール K が
      逆元の modulus N を知らないという bound-chain 問題を、
      積列の C·uₙ 評価に緩めてから極限で回収して回避する）

  * M145-1 `rshift` / `rshift_eq` — 添字シフトと realEq 不変性
  * M145-2 ℚ 逆元ツールキット — 下界 1/(N+1) ≤ a のもとでの
    a·a⁻¹ = 1（関数形）・|a⁻¹| ≤ N+1・差の展開
    a⁻¹ − b⁻¹ = (b−a)·a⁻¹b⁻¹・Lipschitz |a⁻¹−b⁻¹| ≤ (N+1)²|a−b|
  * M145-3 `realEq_qconst_of_bound` — ミニ極限補題
  * M145-4 `rinvPos` — 逆元の実数（加速添字 (N+1)²(n+1)−1、
    正則性は Lipschitz + qFrac_mul の添字算術）
  * M145-5 **`rinvPos_mul_self`（本丸）** — x · x⁻¹ ≈ 1
  * M145-6 **`pos_inv_exists`（見出し）** — IsPos x なら
    ∃ y, x·y ≈ 1（∃ から ∃ なので witness 抽出不要 = choice なし）
  * M145-7 `RealInvData` — 総括

正直な限定: 負の実数・apart（IsPos |x|）一般の逆元は符号分岐を
経由して次層。逆元の一意性・除算の代数法則も次層。

全て選択公理不使用。
-/
import IUT.RealPosMul
import IUT.RealComplete
import IUT.ScalarDistrib

namespace IUT

/-! ## M145-1: 添字シフト -/

/-- **M145-1a: 添字シフト** — 正則性は添字単調性で保存。 -/
def rshift (k : Nat) (x : RReal) : RReal where
  seq := fun n => x.seq (n + k)
  reg := by
    intro m n
    show qLe (qAbs (qAdd (x.seq (m + k)) (qNeg (x.seq (n + k)))))
      (qAdd (qUnitFrac m) (qUnitFrac n))
    exact qLe_trans _ _ _ (x.reg (m + k) (n + k))
      (qLe_add_two (qFrac_le (by omega)) (qFrac_le (by omega)))

/-- **M145-1b: シフト不変性** — rshift k x ≈ x。 -/
theorem rshift_eq (k : Nat) (x : RReal) : realEq (rshift k x) x := by
  intro n
  show qLe (qAbs (qAdd (x.seq (n + k)) (qNeg (x.seq n))))
    (qAdd (qUnitFrac n) (qUnitFrac n))
  exact qLe_trans _ _ _ (x.reg (n + k) n)
    (qLe_add_two (qFrac_le (by omega)) (qLe_refl _))

/-! ## M145-2: ℚ 逆元ツールキット -/

/-- 下界 1/(N+1) ≤ a は代表の分子の正値性を与える。 -/
theorem qlb_num_pos {N : Nat} {x : PreRat}
    (h : qLe (qFrac 1 N) (Quot.mk ratRel x)) : 1 ≤ x.num := by
  have h' : (1 : Int) * x.den ≤ x.num * ((N : Int) + 1) := h
  have hd := x.den_pos
  cases Int.lt_or_le x.num 1 with
  | inr hge => exact hge
  | inl hlt =>
    have hn0 : x.num ≤ 0 := by omega
    have h2 : x.num * ((N : Int) + 1) ≤ 0 * ((N : Int) + 1) :=
      Int.mul_le_mul_of_nonneg_right hn0 (by omega)
    rw [Int.zero_mul] at h2
    omega

/-- **M145-2a: 体の公理の関数形（下界 witness）** — 1/(N+1) ≤ a なら
    a · a⁻¹ = 1（M115F-6d の代表 witness を qLe 仮定に置換）。 -/
theorem qInv_mul_self {N : Nat} : ∀ {a : QRat},
    qLe (qFrac 1 N) a → qMul a (qInv a) = ratRing.one := by
  intro a
  induction a using Quot.ind
  rename_i x
  intro h
  have hnum := qlb_num_pos h
  exact qMul_inv x (by omega)

/-- **M145-2b: 逆元の上界** — 1/(N+1) ≤ a なら |a⁻¹| ≤ N+1。 -/
theorem qAbs_qInv_le {N : Nat} : ∀ {a : QRat},
    qLe (qFrac 1 N) a → qLe (qAbs (qInv a)) (qFrac (N + 1) 0) := by
  intro a
  induction a using Quot.ind
  rename_i x
  intro h
  have hnum := qlb_num_pos h
  have h' : (1 : Int) * x.den ≤ x.num * ((N : Int) + 1) := h
  have hd := x.den_pos
  show intAbs (prInv x).num * ((0 : Int) + 1)
    ≤ ((N + 1 : Nat) : Int) * (prInv x).den
  rw [prInv_of_ne (by omega : x.num ≠ 0)]
  show intAbs (prInvNum x) * ((0 : Int) + 1)
    ≤ ((N + 1 : Nat) : Int) * prInvDen x
  rw [show prInvNum x = x.den from if_pos (by omega),
    intAbs_of_nonneg (Int.le_of_lt hd),
    show prInvDen x = x.num from Int.natAbs_of_nonneg (by omega),
    show ((N + 1 : Nat) : Int) = (N : Int) + 1 from by omega,
    Int.mul_comm ((N : Int) + 1) x.num]
  omega

/-- **M145-2c: 差の展開** — a⁻¹ − b⁻¹ = (b − a)·a⁻¹·b⁻¹
    （体の公理 2 回 + 環算）。 -/
theorem qInv_sub_expand {N : Nat} {a b : QRat}
    (ha : qLe (qFrac 1 N) a) (hb : qLe (qFrac 1 N) b) :
    qAdd (qInv a) (qNeg (qInv b))
      = qMul (qAdd b (qNeg a)) (qMul (qInv a) (qInv b)) := by
  have h1 := qInv_mul_self ha
  have h2 := qInv_mul_self hb
  have e1 : qMul b (qMul (qInv a) (qInv b)) = qInv a := by
    rw [qMul_comm (qInv a) (qInv b), ← qMul_assoc b (qInv b) (qInv a),
      h2, qMul_comm ratRing.one (qInv a), qMul_one]
  have e2 : qMul a (qMul (qInv a) (qInv b)) = qInv b := by
    rw [← qMul_assoc a (qInv a) (qInv b), h1,
      qMul_comm ratRing.one (qInv b), qMul_one]
  rw [qAdd_mul b (qNeg a) (qMul (qInv a) (qInv b)),
    qMul_neg_left a (qMul (qInv a) (qInv b)), e1, e2]

/-- **M145-2d: Lipschitz 評価** — |a⁻¹ − b⁻¹| ≤ (N+1)²·|b − a|。 -/
theorem qInv_diff_le {N : Nat} {a b : QRat}
    (ha : qLe (qFrac 1 N) a) (hb : qLe (qFrac 1 N) b) :
    qLe (qAbs (qAdd (qInv a) (qNeg (qInv b))))
      (qMul (qFrac ((N + 1) * (N + 1)) 0) (qAbs (qAdd b (qNeg a)))) := by
  rw [qInv_sub_expand ha hb, qAbs_mul, qAbs_mul]
  have h2 : qLe (qMul (qAbs (qInv a)) (qAbs (qInv b)))
      (qMul (qFrac (N + 1) 0) (qFrac (N + 1) 0)) :=
    qLe_mul_two (qAbs_qInv_le ha) (qAbs_qInv_le hb)
      (qAbs_nonneg _) (qFrac_nonneg _ _)
  rw [qFrac_mul (N + 1) 0 (N + 1) 0] at h2
  rw [qMul_comm (qAbs (qAdd b (qNeg a)))
    (qMul (qAbs (qInv a)) (qAbs (qInv b)))]
  exact qLe_mul_right h2 (qAbs_nonneg _)

/-! ## M145-3: ミニ極限補題 -/

/-- padding: v ≤ v + u（u は非負分数）。 -/
theorem qLe_pad_frac (v : QRat) (c m : Nat) :
    qLe v (qAdd v (qFrac c m)) := by
  have h0 : qLe (qAdd v ratRing.zero) (qAdd v (qFrac c m)) :=
    qLe_add_two (qLe_refl v) (qFrac_nonneg c m)
  rw [qAdd_zero] at h0
  exact h0

/-- **定理 (M145-3): ミニ極限補題** — 速度 C の定数近似は realEq:
    |w_k − y| ≤ C/(k+1)（∀k）なら w ≈ qToReal y。
    望遠鏡 w_n − y = (w_n − w_m) + (w_m − y) と ε-消去 c = 1+C。 -/
theorem realEq_qconst_of_bound (w : RReal) (y : QRat) (C : Nat)
    (h : ∀ k, qLe (qAbs (qAdd (w.seq k) (qNeg y))) (qFrac C k)) :
    realEq w (qToReal y) := by
  apply rLe_antisym
  · intro n
    show qLe (w.seq n) (qAdd y (qAdd (qUnitFrac n) (qUnitFrac n)))
    apply qLe_of_forall_add_frac (1 + C)
    intro m
    have t1 : qLe (w.seq n)
        (qAdd (qAdd (qUnitFrac n) (qUnitFrac m)) (w.seq m)) :=
      qLe_abs_move (w.reg n m)
    have t2 : qLe (w.seq m) (qAdd (qFrac C m) y) := qLe_abs_move (h m)
    have t3 : qLe (w.seq n)
        (qAdd (qAdd (qUnitFrac n) (qUnitFrac m)) (qAdd (qFrac C m) y)) :=
      qLe_trans _ _ _ t1 (qLe_add_two (qLe_refl _) t2)
    refine qLe_trans _ _ _ t3 ?_
    -- (u_n + u_m) + (Cu_m + y) = (u_n + Cu_m·側) を並べ替えて濃縮
    have e1 : qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
        (qAdd (qFrac C m) y)
        = qAdd (qAdd (qUnitFrac n) (qFrac C m))
          (qAdd (qUnitFrac m) y) :=
      qAdd_swap_mid (qUnitFrac n) (qUnitFrac m) (qFrac C m) y
    rw [e1]
    -- 目標: … ≤ (y + (u_n + u_n)) + F(1+C) m
    -- 左 ≤ (u_n + F(1+C)m 相当) + (u_n + y) 経由で押さえる
    have s1 : qLe (qAdd (qUnitFrac n) (qFrac C m))
        (qAdd (qUnitFrac n) (qFrac C m)) := qLe_refl _
    have s2 : qLe (qAdd (qUnitFrac m) y) (qAdd (qUnitFrac m) y) :=
      qLe_refl _
    -- まとめ替え: (u_n + Cu_m) + (u_m + y)
    --   = (u_n + u_m 側を y へ寄せる) — swap でもう一度
    have e2 : qAdd (qAdd (qUnitFrac n) (qFrac C m))
        (qAdd (qUnitFrac m) y)
        = qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
          (qAdd (qFrac C m) y) := e1.symm
    rw [e2, ← qAdd_assoc (qAdd (qUnitFrac n) (qUnitFrac m))
      (qFrac C m) y]
    -- 目標: ((u_n + u_m) + Cu_m) + y ≤ (y + 2u_n) + F(1+C)m
    have s3 : qLe (qAdd (qAdd (qUnitFrac n) (qUnitFrac m)) (qFrac C m))
        (qAdd (qUnitFrac n) (qFrac (1 + C) m)) := by
      rw [qAdd_assoc (qUnitFrac n) (qUnitFrac m) (qFrac C m)]
      exact qLe_add_two (qLe_refl _) (qFrac_add 1 C m)
    have s4 : qLe (qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
        (qFrac C m)) y)
        (qAdd (qAdd (qUnitFrac n) (qFrac (1 + C) m)) y) :=
      qLe_add _ _ y s3
    refine qLe_trans _ _ _ s4 ?_
    -- (u_n + F) + y ≤ (y + (u_n + u_n)) + F
    have e3 : qAdd (qAdd (qUnitFrac n) (qFrac (1 + C) m)) y
        = qAdd (qAdd (qUnitFrac n) y) (qFrac (1 + C) m) := by
      rw [qAdd_assoc (qUnitFrac n) (qFrac (1 + C) m) y,
        qAdd_comm (qFrac (1 + C) m) y,
        ← qAdd_assoc (qUnitFrac n) y (qFrac (1 + C) m)]
    rw [e3]
    apply qLe_add
    -- u_n + y ≤ y + (u_n + u_n)
    have s5 : qLe (qAdd (qUnitFrac n) y)
        (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) y) :=
      qLe_add _ _ y (qLe_pad_frac (qUnitFrac n) 1 n)
    refine qLe_trans _ _ _ s5 (qLe_of_eq ?_)
    exact qAdd_comm (qAdd (qUnitFrac n) (qUnitFrac n)) y
  · intro n
    show qLe y (qAdd (w.seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))
    apply qLe_of_forall_add_frac (1 + C)
    intro m
    -- y ≤ Cu_m + w_m ≤ Cu_m + ((u_m + u_n) + w_n)
    have habs : qLe (qAbs (qAdd y (qNeg (w.seq m)))) (qFrac C m) := by
      rw [qAbs_sub_comm y (w.seq m)]
      exact h m
    have t2 : qLe y (qAdd (qFrac C m) (w.seq m)) := qLe_abs_move habs
    have t1 : qLe (w.seq m)
        (qAdd (qAdd (qUnitFrac m) (qUnitFrac n)) (w.seq n)) :=
      qLe_abs_move (w.reg m n)
    have t3 : qLe y (qAdd (qFrac C m)
        (qAdd (qAdd (qUnitFrac m) (qUnitFrac n)) (w.seq n))) :=
      qLe_trans _ _ _ t2 (qLe_add_two (qLe_refl _) t1)
    refine qLe_trans _ _ _ t3 ?_
    -- Cu_m + ((u_m + u_n) + w_n) ≤ (w_n + 2u_n) + F(1+C)m
    have e1 : qAdd (qFrac C m)
        (qAdd (qAdd (qUnitFrac m) (qUnitFrac n)) (w.seq n))
        = qAdd (qAdd (qAdd (qFrac C m) (qUnitFrac m)) (qUnitFrac n))
          (w.seq n) := by
      rw [← qAdd_assoc (qFrac C m)
        (qAdd (qUnitFrac m) (qUnitFrac n)) (w.seq n),
        ← qAdd_assoc (qFrac C m) (qUnitFrac m) (qUnitFrac n)]
    rw [e1]
    have s3 : qLe (qAdd (qFrac C m) (qUnitFrac m)) (qFrac (1 + C) m) := by
      refine qLe_trans _ _ _ (qLe_of_eq (qAdd_comm (qFrac C m)
        (qUnitFrac m))) (qFrac_add 1 C m)
    have s4 : qLe (qAdd (qAdd (qAdd (qFrac C m) (qUnitFrac m))
        (qUnitFrac n)) (w.seq n))
        (qAdd (qAdd (qFrac (1 + C) m) (qUnitFrac n)) (w.seq n)) :=
      qLe_add _ _ (w.seq n) (qLe_add _ _ (qUnitFrac n) s3)
    refine qLe_trans _ _ _ s4 ?_
    -- (F + u_n) + w_n ≤ (w_n + 2u_n) + F
    have s5 : qLe (qAdd (qUnitFrac n) (w.seq n))
        (qAdd (w.seq n) (qAdd (qUnitFrac n) (qUnitFrac n))) := by
      refine qLe_trans _ _ _ (qLe_add _ _ (w.seq n) (qLe_pad_frac (qUnitFrac n) 1 n)) (qLe_of_eq ?_)
      exact qAdd_comm (qAdd (qUnitFrac n) (qUnitFrac n)) (w.seq n)
    have e2 : qAdd (qAdd (qFrac (1 + C) m) (qUnitFrac n)) (w.seq n)
        = qAdd (qFrac (1 + C) m) (qAdd (qUnitFrac n) (w.seq n)) :=
      qAdd_assoc (qFrac (1 + C) m) (qUnitFrac n) (w.seq n)
    rw [e2]
    have s6 : qLe (qAdd (qFrac (1 + C) m)
        (qAdd (qUnitFrac n) (w.seq n)))
        (qAdd (qFrac (1 + C) m)
          (qAdd (w.seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))) :=
      qLe_add_two (qLe_refl _) s5
    refine qLe_trans _ _ _ s6 (qLe_of_eq ?_)
    exact qAdd_comm (qFrac (1 + C) m)
      (qAdd (w.seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))

/-! ## M145-4: 逆元の実数 -/

/-- 加速添字 (N+1)²(n+1) − 1。 -/
def rinvIdx (N n : Nat) : Nat := (N + 1) * (N + 1) * (n + 1) - 1

/-- 添字算術: rinvIdx + 1 = (N+1)²(n+1)。 -/
theorem rinvIdx_succ (N n : Nat) :
    rinvIdx N n + 1 = (N + 1) * (N + 1) * (n + 1) := by
  show (N + 1) * (N + 1) * (n + 1) - 1 + 1 = (N + 1) * (N + 1) * (n + 1)
  have h2 : 1 * 1 ≤ (N + 1) * (N + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : (N + 1) * (N + 1) * 1 ≤ (N + 1) * (N + 1) * (n + 1) :=
    Nat.mul_le_mul_left ((N + 1) * (N + 1)) (by omega)
  omega

/-- 添字押さえ: (N+1)²·u_{rinvIdx N n} ≤ u_n（qFrac_mul の着地）。 -/
theorem qFrac_sq_bound (N n : Nat) :
    qLe (qMul (qFrac ((N + 1) * (N + 1)) 0) (qFrac 1 (rinvIdx N n)))
      (qFrac 1 n) := by
  rw [qFrac_mul ((N + 1) * (N + 1)) 0 1 (rinvIdx N n),
    Nat.mul_one ((N + 1) * (N + 1)), Nat.one_mul (rinvIdx N n + 1),
    Nat.add_sub_cancel]
  apply qFrac_le
  have e1 : ((rinvIdx N n : Nat) : Int) + 1
      = (((N + 1) * (N + 1) * (n + 1) : Nat) : Int) := by
    have h := rinvIdx_succ N n
    omega
  rw [e1, Int.natCast_mul ((N + 1) * (N + 1)) (n + 1),
    show ((n + 1 : Nat) : Int) = (n : Int) + 1 from by omega]
  omega

/-- **M145-4: 正値実数の逆元** — 一様下界 1/(N+1) ≤ x_m（∀m）を
    持つ実数の逆元。正則性は Lipschitz (N+1)² と加速添字の相殺。 -/
def rinvPos (x : RReal) (N : Nat)
    (hx : ∀ m, qLe (qFrac 1 N) (x.seq m)) : RReal where
  seq := fun n => qInv (x.seq (rinvIdx N n))
  reg := by
    intro m n
    show qLe (qAbs (qAdd (qInv (x.seq (rinvIdx N m)))
        (qNeg (qInv (x.seq (rinvIdx N n))))))
      (qAdd (qUnitFrac m) (qUnitFrac n))
    have hlip := qInv_diff_le (hx (rinvIdx N m)) (hx (rinvIdx N n))
    refine qLe_trans _ _ _ hlip ?_
    -- (N+1)²·|x_jn − x_jm| ≤ (N+1)²·(u_jn + u_jm) ≤ u_n + u_m ≤ u_m + u_n
    have hreg := x.reg (rinvIdx N n) (rinvIdx N m)
    have h1 : qLe (qMul (qAbs (qAdd (x.seq (rinvIdx N n))
        (qNeg (x.seq (rinvIdx N m)))))
        (qFrac ((N + 1) * (N + 1)) 0))
        (qMul (qAdd (qUnitFrac (rinvIdx N n))
          (qUnitFrac (rinvIdx N m)))
          (qFrac ((N + 1) * (N + 1)) 0)) :=
      qLe_mul_right hreg (qFrac_nonneg _ _)
    rw [qMul_comm (qFrac ((N + 1) * (N + 1)) 0)
      (qAbs (qAdd (x.seq (rinvIdx N n)) (qNeg (x.seq (rinvIdx N m)))))]
    refine qLe_trans _ _ _ h1 ?_
    rw [qMul_comm (qAdd (qUnitFrac (rinvIdx N n))
      (qUnitFrac (rinvIdx N m))) (qFrac ((N + 1) * (N + 1)) 0),
      qMul_add (qFrac ((N + 1) * (N + 1)) 0)
        (qUnitFrac (rinvIdx N n)) (qUnitFrac (rinvIdx N m))]
    refine qLe_trans _ _ _
      (qLe_add_two (qFrac_sq_bound N n) (qFrac_sq_bound N m))
      (qLe_of_eq (qAdd_comm (qFrac 1 n) (qFrac 1 m)))

/-! ## M145-5: 本丸 x·x⁻¹ ≈ 1 -/

/-- **定理 (M145-5): 逆元の乗法公理（本丸）** — x · rinvPos x ≈ 1。
    積列の第 n 項は x_a·(x_b)⁻¹（a = mulIdx K n、b = rinvIdx N a）で、
    |x_a·(x_b)⁻¹ − 1| = |x_a − x_b|·|(x_b)⁻¹| ≤ 2u_a·(N+1)
    ≤ (2N+2)/(n+1)。ミニ極限補題 C = 2(N+1) で realEq に到達。 -/
theorem rinvPos_mul_self (x : RReal) (N : Nat)
    (hx : ∀ m, qLe (qFrac 1 N) (x.seq m)) :
    realEq (rmul x (rinvPos x N hx)) (qToReal ratRing.one) := by
  apply realEq_qconst_of_bound _ _ (2 * (N + 1))
  intro n
  have hK : 1 ≤ rBound x + rBound (rinvPos x N hx) :=
    rBound_pair_pos x (rinvPos x N hx)
  -- 記号: a = mulIdx K n、b = rinvIdx N a（show で defeq 固定後に一般化）
  show qLe (qAbs (qAdd (qMul
      (x.seq (mulIdx (rBound x + rBound (rinvPos x N hx)) n))
      (qInv (x.seq (rinvIdx N
        (mulIdx (rBound x + rBound (rinvPos x N hx)) n)))))
      (qNeg ratRing.one))) (qFrac (2 * (N + 1)) n)
  generalize ha : mulIdx (rBound x + rBound (rinvPos x N hx)) n = a
  -- a ≥ n（mulIdx_succ + K ≥ 1）
  have han : n ≤ a := by
    have h := mulIdx_succ (rBound x + rBound (rinvPos x N hx)) n hK
    rw [ha] at h
    have h2 : 1 * (n + 1) ≤ 2 * (rBound x + rBound (rinvPos x N hx))
        * (n + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  -- 差の積化: x_a·inv − 1 = (x_a − x_b)·inv
  have hone := qInv_mul_self (hx (rinvIdx N a))
  have e1 : qAdd (qMul (x.seq a) (qInv (x.seq (rinvIdx N a))))
      (qNeg ratRing.one)
      = qMul (qAdd (x.seq a) (qNeg (x.seq (rinvIdx N a))))
        (qInv (x.seq (rinvIdx N a))) := by
    rw [qAdd_mul (x.seq a) (qNeg (x.seq (rinvIdx N a)))
        (qInv (x.seq (rinvIdx N a))),
      qMul_neg_left (x.seq (rinvIdx N a)) (qInv (x.seq (rinvIdx N a))),
      hone]
  rw [e1, qAbs_mul]
  -- |x_a − x_b| ≤ u_a + u_b ≤ 2u_a（b ≥ a）
  have hba : a ≤ rinvIdx N a := by
    have h := rinvIdx_succ N a
    have h2 : 1 * 1 * (a + 1) ≤ (N + 1) * (N + 1) * (a + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    omega
  have hdiff : qLe (qAbs (qAdd (x.seq a) (qNeg (x.seq (rinvIdx N a)))))
      (qFrac 2 a) := by
    refine qLe_trans _ _ _ (x.reg a (rinvIdx N a)) ?_
    refine qLe_trans _ _ _
      (qLe_add_two (qLe_refl (qUnitFrac a)) (qFrac_le (by omega)))
      (qFrac_add 1 1 a)
  -- 積の押さえ: |Δ|·|inv| ≤ 2u_a·(N+1) = (2N+2)/(a+1) ≤ (2N+2)/(n+1)
  have hprod : qLe (qMul (qAbs (qAdd (x.seq a)
      (qNeg (x.seq (rinvIdx N a)))))
      (qAbs (qInv (x.seq (rinvIdx N a)))))
      (qMul (qFrac 2 a) (qFrac (N + 1) 0)) :=
    qLe_mul_two hdiff (qAbs_qInv_le (hx (rinvIdx N a)))
      (qAbs_nonneg _) (qFrac_nonneg _ _)
  refine qLe_trans _ _ _ hprod ?_
  rw [qFrac_mul 2 a (N + 1) 0]
  -- qFrac (2(N+1)) ((a+1)·1 − 1) ≤ qFrac (2N+2) n
  rw [Nat.mul_one (a + 1), Nat.add_sub_cancel]
  apply qFrac_le
  have h2 : ((2 * (N + 1) : Nat) : Int) * ((n : Int) + 1)
      ≤ ((2 * (N + 1) : Nat) : Int) * ((a : Int) + 1) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  omega

/-! ## M145-6: 見出し — IsPos からの逆元存在 -/

/-- IsPos の witness からシフト後の一様下界。 -/
theorem isPos_shift_lb {x : RReal} {n : Nat}
    (hn : qLe (qFrac 2 n) (x.seq n)) :
    ∀ m, qLe (qFrac 1 (2 * n + 1)) ((rshift (2 * n + 1) x).seq m) := by
  intro m
  show qLe (qFrac 1 (2 * n + 1)) (x.seq (m + (2 * n + 1)))
  exact isPos_lower hn (by omega)

/-- **定理 (M145-6): 正値実数の逆元存在（見出し）** — IsPos x なら
    ∃ y, x·y ≈ 1。∃ から ∃ への写像なので witness 抽出（choice）は
    不要。y は rshift + rinvPos の明示構成。 -/
theorem pos_inv_exists (x : RReal) (hx : IsPos x) :
    ∃ y : RReal, realEq (rmul x y) (qToReal ratRing.one) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨rinvPos (rshift (2 * n + 1) x) (2 * n + 1)
    (isPos_shift_lb hn), ?_⟩
  refine realEq_trans (rmul_congr_left _ (realEq_symm
    (rshift_eq (2 * n + 1) x))) ?_
  exact rinvPos_mul_self (rshift (2 * n + 1) x) (2 * n + 1)
    (isPos_shift_lb hn)

/-! ## M145-7: 総括 -/

/-- **M145-7a: 総括** — 実数逆元のデータ。 -/
structure RealInvData where
  /-- シフト不変性。 -/
  shift_eq : ∀ k x, realEq (rshift k x) x
  /-- ミニ極限補題。 -/
  const_of_bound : ∀ (w : RReal) (y : QRat) (C : Nat),
    (∀ k, qLe (qAbs (qAdd (w.seq k) (qNeg y))) (qFrac C k)) →
    realEq w (qToReal y)
  /-- 一様下界つき逆元の乗法公理。 -/
  inv_mul : ∀ (x : RReal) (N : Nat)
    (hx : ∀ m, qLe (qFrac 1 N) (x.seq m)),
    realEq (rmul x (rinvPos x N hx)) (qToReal ratRing.one)
  /-- 正値実数の逆元存在。 -/
  pos_inv : ∀ x, IsPos x →
    ∃ y : RReal, realEq (rmul x y) (qToReal ratRing.one)

/-- **M145-7b: witness**。 -/
def realInvData : RealInvData where
  shift_eq := rshift_eq
  const_of_bound := realEq_qconst_of_bound
  inv_mul := rinvPos_mul_self
  pos_inv := pos_inv_exists

/-- **M145-7c: 存在**。 -/
theorem realInv_exists : Nonempty RealInvData :=
  ⟨realInvData⟩

end IUT
