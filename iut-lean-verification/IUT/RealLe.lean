/-
# M130: 実数の非厳密順序 ≤ — witness 形と反対称律

柱C（issue #37）。M125 の正直申告（≤ との整合）の解消。
構成的 ≤ は「各添字で固有の揺らぎを許した比較」:

  rLe x y := ∀ n, x_n ≤ y_n + 2/(n+1)

設計の鍵: 推移律などの合成は **望遠鏡分解**
a − c = (a − b) + (b − c)（qSub_split）で片側差に割り、
定数側だけを qFrac の折り畳みで濃縮して ε-消去する
（M125 で苦しんだ大域並べ替えを完全回避する定型）。

  * M130-1 片側差の移項補題（qLe_sub_move / qSub_le_of_le）
  * M130-2 `rLe`・`rLe_of_realEq`・反射
  * M130-3 **推移律**（望遠鏡 + ε-消去 c = 6）
  * M130-4 **反対称律（本丸）** — rLe x y → rLe y x → x ≈ y
  * M130-5 congruence（rLe_of_realEq + 推移律で無償）・加法両立
  * M130-6 rLt との整合 — rLt → rLe（spread + ε c = 2)・
    rLt y x → ¬ rLe x y（強排反）
  * M130-7 `RealLeData` — 総括

正直な限定: 線形性（rLe x y ∨ rLe y x）は排中律相当のため対象外
（共推移性 M125 が構成的代替)。¬rLt → rLe の向きは代表抽出の
δ-論法を要するため次層。

全て選択公理不使用。
-/
import IUT.RealOrder

namespace IUT

/-! ## M130-1: 片側差の移項 -/

/-- 移項: a − c ≤ B なら a ≤ B + c。 -/
theorem qLe_sub_move {a c B : QRat}
    (h : qLe (qAdd a (qNeg c)) B) : qLe a (qAdd B c) := by
  have e : a = qAdd (qAdd a (qNeg c)) c := by
    rw [qAdd_assoc a (qNeg c) c, qNeg_add_self c, qAdd_zero]
  exact qLe_trans _ _ _ (qLe_of_eq e) (qLe_add (qAdd a (qNeg c)) B c h)

/-- 移項: a ≤ b + B なら a − b ≤ B。 -/
theorem qSub_le_of_le {a b B : QRat}
    (h : qLe a (qAdd b B)) : qLe (qAdd a (qNeg b)) B := by
  have h2 := qLe_add a (qAdd b B) (qNeg b) h
  have e : qAdd (qAdd b B) (qNeg b) = B := by
    rw [qAdd_comm b B, qAdd_assoc B b (qNeg b), qAdd_neg_self b, qAdd_zero]
  rw [e] at h2
  exact h2

/-- 正則性の片側差: x_n − x_m ≤ u_n + u_m。 -/
theorem reg_sub_le (x : RReal) (n m : Nat) :
    qLe (qAdd (x.seq n) (qNeg (x.seq m)))
      (qAdd (qUnitFrac n) (qUnitFrac m)) :=
  qLe_trans _ _ _ (qLe_self_abs _) (x.reg n m)

/-! ## M130-2: 定義と基本 -/

/-- **M130-2a: 非厳密順序**（witness 形）。 -/
def rLe (x y : RReal) : Prop :=
  ∀ n, qLe (x.seq n)
    (qAdd (y.seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))

/-- **M130-2b: ≈ から ≤**（|x_n − y_n| ≤ 2u_n の片側読み）。 -/
theorem rLe_of_realEq {x y : RReal} (h : realEq x y) : rLe x y := by
  intro n
  exact qLe_trans _ _ _ (qLe_abs_move (h n)) (qLe_of_eq (qAdd_comm _ _))

/-- **M130-2c: 反射律**。 -/
theorem rLe_refl (x : RReal) : rLe x x :=
  rLe_of_realEq (realEq_refl x)

/-! ## M130-3: 推移律 -/

/-- **定理 (M130-3): 推移律** — 望遠鏡分解
    x_n − z_n = (x_n − x_m) + ((x_m − y_m) + ((y_m − z_m) + (z_m − z_n)))
    と定数側の折り畳み（≤ 2u_n + 6/(m+1)）、ε-消去 c = 6。 -/
theorem rLe_trans {x y z : RReal} (h1 : rLe x y) (h2 : rLe y z) :
    rLe x z := by
  intro n
  apply qLe_of_forall_add_frac 6
  intro m
  -- 片側差の 4 部品
  have t1 := reg_sub_le x n m
  have t2 : qLe (qAdd (x.seq m) (qNeg (y.seq m)))
      (qFrac 2 m) :=
    qLe_trans _ _ _ (qSub_le_of_le (h1 m)) (qFrac_add 1 1 m)
  have t3 : qLe (qAdd (y.seq m) (qNeg (z.seq m)))
      (qFrac 2 m) :=
    qLe_trans _ _ _ (qSub_le_of_le (h2 m)) (qFrac_add 1 1 m)
  have t4 := reg_sub_le z m n
  -- 望遠鏡: x_n − z_n = t1 + (t2 + (t3 + t4))
  have esplit : qAdd (x.seq n) (qNeg (z.seq n))
      = qAdd (qAdd (x.seq n) (qNeg (x.seq m)))
        (qAdd (qAdd (x.seq m) (qNeg (y.seq m)))
          (qAdd (qAdd (y.seq m) (qNeg (z.seq m)))
            (qAdd (z.seq m) (qNeg (z.seq n))))) := by
    rw [← qSub_split (y.seq m) (z.seq m) (z.seq n),
      ← qSub_split (x.seq m) (y.seq m) (z.seq n),
      ← qSub_split (x.seq n) (x.seq m) (z.seq n)]
  have total : qLe (qAdd (x.seq n) (qNeg (z.seq n)))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
        (qAdd (qFrac 2 m)
          (qAdd (qFrac 2 m) (qAdd (qUnitFrac m) (qUnitFrac n))))) :=
    qLe_trans _ _ _ (qLe_of_eq esplit)
      (qLe_add_two t1 (qLe_add_two t2 (qLe_add_two t3 t4)))
  -- 定数側の濃縮: … ≤ (u_n + u_n) + F6m
  have hfold : qLe (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
      (qAdd (qFrac 2 m)
        (qAdd (qFrac 2 m) (qAdd (qUnitFrac m) (qUnitFrac n)))))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 6 m)) := by
    -- 内側: F2m + (u_m + u_n) → (F2m + u_m) + u_n ≤ F3m + u_n
    have i1 : qLe (qAdd (qFrac 2 m) (qAdd (qUnitFrac m) (qUnitFrac n)))
        (qAdd (qFrac 3 m) (qUnitFrac n)) :=
      qLe_trans _ _ _ (qLe_of_eq (qAdd_assoc _ _ _).symm)
        (qLe_add_two (qFrac_add 2 1 m) (qLe_refl _))
    -- 中間: F2m + (F3m + u_n) → (F2m + F3m) + u_n ≤ F5m + u_n
    have i2 : qLe (qAdd (qFrac 2 m)
        (qAdd (qFrac 2 m) (qAdd (qUnitFrac m) (qUnitFrac n))))
        (qAdd (qFrac 5 m) (qUnitFrac n)) :=
      qLe_trans _ _ _ (qLe_add_two (qLe_refl _) i1)
        (qLe_trans _ _ _ (qLe_of_eq (qAdd_assoc _ _ _).symm)
          (qLe_add_two (qFrac_add 2 3 m) (qLe_refl _)))
    -- 外側: (u_n + u_m) + (F5m + u_n) → comm → swap_mid →
    --   (u_n + u_n) + (u_m + F5m) ≤ (u_n + u_n) + F6m
    have i3 : qLe (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
        (qAdd (qFrac 2 m)
          (qAdd (qFrac 2 m) (qAdd (qUnitFrac m) (qUnitFrac n)))))
        (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
          (qAdd (qUnitFrac n) (qFrac 5 m))) :=
      qLe_add_two (qLe_refl _)
        (qLe_trans _ _ _ i2 (qLe_of_eq (qAdd_comm _ _)))
    have e4 : qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
        (qAdd (qUnitFrac n) (qFrac 5 m))
        = qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
          (qAdd (qUnitFrac m) (qFrac 5 m)) :=
      qAdd_swap_mid _ _ _ _
    exact qLe_trans _ _ _ i3 (qLe_trans _ _ _ (qLe_of_eq e4)
      (qLe_add_two (qLe_refl _) (qFrac_add 1 5 m)))
  -- 移項して着地
  have hD := qLe_trans _ _ _ total hfold
  have hx := qLe_sub_move hD
  -- ((u_n+u_n) + F6m) + z_n = (z_n + (u_n+u_n)) + F6m
  have e5 : qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 6 m))
      (z.seq n)
      = qAdd (qAdd (z.seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))
        (qFrac 6 m) := by
    rw [qAdd_comm (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 6 m))
        (z.seq n),
      ← qAdd_assoc (z.seq n) (qAdd (qUnitFrac n) (qUnitFrac n))
        (qFrac 6 m)]
  exact qLe_trans _ _ _ hx (qLe_of_eq e5)

/-! ## M130-4: 反対称律 -/

/-- |t| ≤ M ⟸ t ≤ M かつ −t ≤ M（代表レベルの符号場合分け）。 -/
theorem qAbs_le_both {t M : QRat} (h1 : qLe t M) (h2 : qLe (qNeg t) M) :
    qLe (qAbs t) M := by
  induction t using Quot.ind; rename_i a
  induction M using Quot.ind; rename_i b
  have h1' : a.num * b.den ≤ b.num * a.den := h1
  have h2' : -a.num * b.den ≤ b.num * a.den := h2
  show intAbs a.num * b.den ≤ b.num * a.den
  cases Int.le_total a.num 0 with
  | inl hneg =>
    rw [intAbs_of_nonpos hneg]
    rw [Int.neg_mul] at h2'
    rw [Int.neg_mul]
    exact h2'
  | inr hpos =>
    rw [intAbs_of_nonneg hpos]
    exact h1'

/-- **定理 (M130-4): 反対称律（本丸）** — 両側の ≤ がそのまま
    |x_n − y_n| ≤ 2u_n を与える。 -/
theorem rLe_antisym {x y : RReal} (h1 : rLe x y) (h2 : rLe y x) :
    realEq x y := by
  intro n
  apply qAbs_le_both
  · exact qSub_le_of_le (h1 n)
  · have e : qNeg (qAdd (x.seq n) (qNeg (y.seq n)))
        = qAdd (y.seq n) (qNeg (x.seq n)) := qNeg_sub _ _
    rw [e]
    exact qSub_le_of_le (h2 n)

/-! ## M130-5: congruence と加法両立 -/

/-- **M130-5a: congruence**（rLe_of_realEq + 推移律で無償）。 -/
theorem rLe_congr {x x' y y' : RReal} (hx : realEq x x')
    (hy : realEq y y') (h : rLe x y) : rLe x' y' :=
  rLe_trans (rLe_of_realEq (realEq_symm hx)) (rLe_trans h (rLe_of_realEq hy))

/-- **M130-5b: 加法両立** — x ≤ y なら x + z ≤ y + z
    （添字 2n+1 の揺らぎ 2u_{2n+1} = u_n が余裕で収まる）。 -/
theorem rLe_add {x y : RReal} (z : RReal) (h : rLe x y) :
    rLe (realAdd x z) (realAdd y z) := by
  intro n
  show qLe (qAdd (x.seq (2 * n + 1)) (z.seq (2 * n + 1)))
    (qAdd (qAdd (y.seq (2 * n + 1)) (z.seq (2 * n + 1)))
      (qAdd (qUnitFrac n) (qUnitFrac n)))
  have hs := h (2 * n + 1)
  have step : qLe (qAdd (x.seq (2 * n + 1)) (z.seq (2 * n + 1)))
      (qAdd (qAdd (y.seq (2 * n + 1))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1))))
        (z.seq (2 * n + 1))) :=
    qLe_add _ _ (z.seq (2 * n + 1)) hs
  apply qLe_trans _ _ _ step
  have e : qAdd (qAdd (y.seq (2 * n + 1))
      (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1))))
      (z.seq (2 * n + 1))
      = qAdd (qAdd (y.seq (2 * n + 1)) (z.seq (2 * n + 1)))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1))) := by
    rw [qAdd_assoc (y.seq (2 * n + 1))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1)))
        (z.seq (2 * n + 1)),
      qAdd_comm (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1)))
        (z.seq (2 * n + 1)),
      ← qAdd_assoc (y.seq (2 * n + 1)) (z.seq (2 * n + 1))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1)))]
  apply qLe_trans _ _ _ (qLe_of_eq e)
  exact qLe_add_two (qLe_refl _)
    (qLe_trans _ _ _ (qFrac_add 1 1 (2 * n + 1))
      (qLe_trans _ _ _ (qFrac_le (by omega)) (qFrac_split 1 1 n)))

/-! ## M130-6: rLt との整合 -/

/-- **定理 (M130-6a): 狭義から非厳密へ** — spread の片側読みと
    ε-消去 c = 2（2u_{2w+1} = u_w の相殺）。 -/
theorem rLt_le {x y : RReal} (h : rLt x y) : rLe x y := by
  obtain ⟨n, hn⟩ := h
  intro k
  apply qLe_of_forall_add_frac 2
  intro w
  -- spread: F2n ≤ (u_n + u_w) + (y_{2w+1} − x_{2w+1})
  have hs := isPos_spread hn w
  -- u_n の消去で x_{2w+1} ≤ u_w + y_{2w+1}
  have hcanc : qLe (x.seq (2 * w + 1))
      (qAdd (qUnitFrac w) (y.seq (2 * w + 1))) := by
    -- u_n + x_s ≤ F2n + x_s ≤ (u_n + u_w) + (y_s − x_s) + x_s
    --   = u_n + (u_w + y_s) → cancel-left u_n
    have hu : qLe (qAdd (qUnitFrac n) (x.seq (2 * w + 1)))
        (qAdd (qFrac 2 n) (x.seq (2 * w + 1))) :=
      qLe_add_two (qFrac_le (by omega)) (qLe_refl _)
    have hmv : qLe (qAdd (qFrac 2 n) (x.seq (2 * w + 1)))
        (qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac w))
          ((realAdd y (realNeg x)).seq w)) (x.seq (2 * w + 1))) :=
      qLe_add _ _ _ hs
    -- (y − x)_w + x_s = y_s（群法則）
    have egrp : qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac w))
        ((realAdd y (realNeg x)).seq w)) (x.seq (2 * w + 1))
        = qAdd (qUnitFrac n)
          (qAdd (qUnitFrac w) (y.seq (2 * w + 1))) := by
      show qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac w))
          (qAdd (y.seq (2 * w + 1)) (qNeg (x.seq (2 * w + 1)))))
          (x.seq (2 * w + 1))
        = qAdd (qUnitFrac n)
          (qAdd (qUnitFrac w) (y.seq (2 * w + 1)))
      rw [qAdd_assoc (qAdd (qUnitFrac n) (qUnitFrac w))
          (qAdd (y.seq (2 * w + 1)) (qNeg (x.seq (2 * w + 1))))
          (x.seq (2 * w + 1)),
        qAdd_assoc (y.seq (2 * w + 1)) (qNeg (x.seq (2 * w + 1)))
          (x.seq (2 * w + 1)),
        qNeg_add_self (x.seq (2 * w + 1)),
        qAdd_zero (y.seq (2 * w + 1)),
        qAdd_assoc (qUnitFrac n) (qUnitFrac w) (y.seq (2 * w + 1))]
    have hchain := qLe_trans _ _ _ hu (qLe_trans _ _ _ hmv
      (qLe_of_eq egrp))
    -- cancel-left u_n
    have hcomm : qLe (qAdd (x.seq (2 * w + 1)) (qUnitFrac n))
        (qAdd (qAdd (qUnitFrac w) (y.seq (2 * w + 1))) (qUnitFrac n)) := by
      apply qLe_trans _ _ _ (qLe_of_eq (qAdd_comm _ _))
      exact qLe_trans _ _ _ hchain (qLe_of_eq (qAdd_comm _ _))
    exact qLe_cancel_right hcomm
  -- x_k − y_k の望遠鏡: (x_k − x_s) + ((x_s − y_s) + (y_s − y_k))
  have t1 := reg_sub_le x k (2 * w + 1)
  have t2 : qLe (qAdd (x.seq (2 * w + 1)) (qNeg (y.seq (2 * w + 1))))
      (qUnitFrac w) := by
    apply qSub_le_of_le
    exact qLe_trans _ _ _ hcanc (qLe_of_eq (qAdd_comm _ _))
  have t3 := reg_sub_le y (2 * w + 1) k
  have esplit : qAdd (x.seq k) (qNeg (y.seq k))
      = qAdd (qAdd (x.seq k) (qNeg (x.seq (2 * w + 1))))
        (qAdd (qAdd (x.seq (2 * w + 1)) (qNeg (y.seq (2 * w + 1))))
          (qAdd (y.seq (2 * w + 1)) (qNeg (y.seq k)))) := by
    rw [← qSub_split (x.seq (2 * w + 1)) (y.seq (2 * w + 1)) (y.seq k),
      ← qSub_split (x.seq k) (x.seq (2 * w + 1)) (y.seq k)]
  have total : qLe (qAdd (x.seq k) (qNeg (y.seq k)))
      (qAdd (qAdd (qUnitFrac k) (qUnitFrac (2 * w + 1)))
        (qAdd (qUnitFrac w)
          (qAdd (qUnitFrac (2 * w + 1)) (qUnitFrac k)))) :=
    qLe_trans _ _ _ (qLe_of_eq esplit)
      (qLe_add_two t1 (qLe_add_two t2 t3))
  -- 濃縮: ≤ (u_k + u_k) + F2w（u_{2w+1} + u_{2w+1} = u_w、u_w + u_w = F2w）
  have hfold : qLe (qAdd (qAdd (qUnitFrac k) (qUnitFrac (2 * w + 1)))
      (qAdd (qUnitFrac w)
        (qAdd (qUnitFrac (2 * w + 1)) (qUnitFrac k))))
      (qAdd (qAdd (qUnitFrac k) (qUnitFrac k)) (qFrac 2 w)) := by
    -- swap_mid: (u_k + u_{s}) + (u_w + (u_{s} + u_k))
    --   = (u_k + u_w) + (u_s + (u_s + u_k))  [swap_mid]
    have e1 : qAdd (qAdd (qUnitFrac k) (qUnitFrac (2 * w + 1)))
        (qAdd (qUnitFrac w)
          (qAdd (qUnitFrac (2 * w + 1)) (qUnitFrac k)))
        = qAdd (qAdd (qUnitFrac k) (qUnitFrac w))
          (qAdd (qUnitFrac (2 * w + 1))
            (qAdd (qUnitFrac (2 * w + 1)) (qUnitFrac k))) :=
      qAdd_swap_mid _ _ _ _
    -- 内側: u_s + (u_s + u_k) = (u_s + u_s) + u_k ≤ u_w + u_k
    have i1 : qLe (qAdd (qUnitFrac (2 * w + 1))
        (qAdd (qUnitFrac (2 * w + 1)) (qUnitFrac k)))
        (qAdd (qUnitFrac w) (qUnitFrac k)) :=
      qLe_trans _ _ _ (qLe_of_eq (qAdd_assoc _ _ _).symm)
        (qLe_add_two
          (qLe_trans _ _ _ (qFrac_add 1 1 (2 * w + 1))
            (qFrac_le (by omega)))
          (qLe_refl _))
    -- (u_k + u_w) + (u_w + u_k) = (u_k + u_k) + (u_w + u_w) ≤ … + F2w
    have e2 : qAdd (qAdd (qUnitFrac k) (qUnitFrac w))
        (qAdd (qUnitFrac w) (qUnitFrac k))
        = qAdd (qAdd (qUnitFrac k) (qUnitFrac k))
          (qAdd (qUnitFrac w) (qUnitFrac w)) := by
      rw [qAdd_comm (qUnitFrac w) (qUnitFrac k)]
      exact qAdd_swap_mid _ _ _ _
    exact qLe_trans _ _ _ (qLe_of_eq e1)
      (qLe_trans _ _ _ (qLe_add_two (qLe_refl _) i1)
        (qLe_trans _ _ _ (qLe_of_eq e2)
          (qLe_add_two (qLe_refl _) (qFrac_add 1 1 w))))
  have hD := qLe_trans _ _ _ total hfold
  have hx := qLe_sub_move hD
  have e5 : qAdd (qAdd (qAdd (qUnitFrac k) (qUnitFrac k)) (qFrac 2 w))
      (y.seq k)
      = qAdd (qAdd (y.seq k) (qAdd (qUnitFrac k) (qUnitFrac k)))
        (qFrac 2 w) := by
    rw [qAdd_comm (qAdd (qAdd (qUnitFrac k) (qUnitFrac k)) (qFrac 2 w))
        (y.seq k),
      ← qAdd_assoc (y.seq k) (qAdd (qUnitFrac k) (qUnitFrac k))
        (qFrac 2 w)]
  exact qLe_trans _ _ _ hx (qLe_of_eq e5)

/-- **定理 (M130-6b): 強排反** — y < x なら ¬(x ≤ y)
    （witness 添字での 2/(n+1) ≤ 1/(n+1) の矛盾）。 -/
theorem rLt_not_le {x y : RReal} (h : rLt y x) : ¬ rLe x y := by
  intro hle
  obtain ⟨n, hn⟩ := h
  -- hn : F2n ≤ x_s − y_s（s = 2n+1）、hle s : x_s ≤ y_s + 2u_s
  have h1 : qLe (qAdd (qFrac 2 n) (y.seq (2 * n + 1)))
      (x.seq (2 * n + 1)) := by
    have := qLe_add _ _ (y.seq (2 * n + 1)) hn
    have egrp : qAdd ((realAdd x (realNeg y)).seq n) (y.seq (2 * n + 1))
        = x.seq (2 * n + 1) := by
      show qAdd (qAdd (x.seq (2 * n + 1)) (qNeg (y.seq (2 * n + 1))))
          (y.seq (2 * n + 1)) = x.seq (2 * n + 1)
      rw [qAdd_assoc (x.seq (2 * n + 1)) (qNeg (y.seq (2 * n + 1)))
          (y.seq (2 * n + 1)),
        qNeg_add_self (y.seq (2 * n + 1)), qAdd_zero]
    rw [egrp] at this
    exact this
  have h2 := hle (2 * n + 1)
  -- 連鎖: F2n + y_s ≤ x_s ≤ y_s + 2u_s → cancel y_s → F2n ≤ 2u_s
  have h3 : qLe (qAdd (qFrac 2 n) (y.seq (2 * n + 1)))
      (qAdd (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1)))
        (y.seq (2 * n + 1))) := by
    apply qLe_trans _ _ _ (qLe_trans _ _ _ h1 h2)
    exact qLe_of_eq (qAdd_comm _ _)
  have h4 : qLe (qFrac 2 n)
      (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1))) := by
    apply qLe_cancel_right (c := y.seq (2 * n + 1))
    exact h3
  have h5 : qLe (qFrac 2 n) (qFrac 2 (2 * n + 1)) :=
    qLe_trans _ _ _ h4 (qFrac_add 1 1 (2 * n + 1))
  -- 具体矛盾: 2(2n+2) ≤ 2(n+1) は偽
  have h6 : (2 : Int) * ((2 * n + 1 : Int) + 1)
      ≤ 2 * ((n : Int) + 1) := h5
  omega

/-! ## M130-7: 総括 -/

/-- **M130-7a: 総括** — 非厳密順序のデータ。 -/
structure RealLeData where
  /-- ≈ から ≤。 -/
  of_eqv : ∀ {x y}, realEq x y → rLe x y
  /-- 反射律。 -/
  le_refl : ∀ x, rLe x x
  /-- 推移律。 -/
  le_trans : ∀ {x y z}, rLe x y → rLe y z → rLe x z
  /-- 反対称律（realEq が返る）。 -/
  le_antisym : ∀ {x y}, rLe x y → rLe y x → realEq x y
  /-- congruence。 -/
  le_congr : ∀ {x x' y y'}, realEq x x' → realEq y y' →
    rLe x y → rLe x' y'
  /-- 加法両立。 -/
  le_add : ∀ {x y} (z), rLe x y → rLe (realAdd x z) (realAdd y z)
  /-- 狭義 → 非厳密。 -/
  lt_le : ∀ {x y}, rLt x y → rLe x y
  /-- 強排反。 -/
  lt_not_le : ∀ {x y}, rLt y x → ¬ rLe x y

/-- **M130-7b: witness**。 -/
def realLeData : RealLeData where
  of_eqv := rLe_of_realEq
  le_refl := rLe_refl
  le_trans := rLe_trans
  le_antisym := rLe_antisym
  le_congr := rLe_congr
  le_add := rLe_add
  lt_le := rLt_le
  lt_not_le := rLt_not_le

/-- **M130-7c: 存在**。 -/
theorem realLe_exists : Nonempty RealLeData :=
  ⟨realLeData⟩

end IUT
