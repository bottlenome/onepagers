/-
# M125: 実数の順序 — witness 形正値性と共推移性

柱C（issue #37）ℝ 構成の第五段。Bishop 流の**構成的順序**:
IsPos x := ∃n, 2/(n+1) ≤ x_n（witness 形 — margin 2 が正則性の
揺らぎ 1/(n+1) を吸収して全添字に伝播する）。

  * M125-1 補助 — a ≤ |a|・neg 反転・加法消去・「|a−b| ≤ B なら
    a ≤ B + b」の移項
  * M125-2 `IsPos` と伝播 `isPos_spread`（witness は任意添字の
    下界を与える）
  * M125-3 `isPos_congr` — ≈ 不変性（添字 5n+4 の margin 計算）
  * M125-4 `isPos_zero_false`・`isPos_add`（添字 3N+2 の合流）
  * M125-5 `rLt x y := IsPos (y − x)` と congruence・非反射律
  * M125-6 `rLt_trans`（(z−x) ≈ (z−y)+(y−x) の代数 + isPos_add）
  * M125-7 **共推移性 `rLt_cotrans`（本丸）** — x < y なら任意の z
    に対し x < z ∨ z < y。qLe_total（有理数の全順序）による構成的
    場合分け — 排中律なしの三分律の代替（Bishop の順序の核心）
  * M125-8 `RealOrderData` — 総括

正直な限定: 正値と乗法の両立（pos·pos → pos）・≤（非厳密順序、
¬(y < x) 形）との整合は次層。

全て選択公理不使用。
-/
import IUT.RealMul

namespace IUT

/-! ## M125-1: 補助補題 -/

/-- a ≤ |a|。 -/
theorem qLe_self_abs (a : QRat) : qLe a (qAbs a) := by
  induction a using Quot.ind; rename_i x
  show x.num * x.den ≤ intAbs x.num * x.den
  exact Int.mul_le_mul_of_nonneg_right (int_le_intAbs x.num)
    (Int.le_of_lt x.den_pos)

/-- neg は順序を反転。 -/
theorem qLe_neg_flip {a b : QRat} (h : qLe a b) : qLe (qNeg b) (qNeg a) := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  have h' : x.num * y.den ≤ y.num * x.den := h
  show -y.num * x.den ≤ -x.num * y.den
  rw [Int.neg_mul, Int.neg_mul]
  omega

/-- 右加法の消去。 -/
theorem qLe_cancel_right {a b c : QRat}
    (h : qLe (qAdd a c) (qAdd b c)) : qLe a b := by
  have h2 := qLe_add (qAdd a c) (qAdd b c) (qNeg c) h
  rw [qAdd_assoc a c (qNeg c), qAdd_neg_self c, qAdd_zero,
    qAdd_assoc b c (qNeg c), qAdd_neg_self c, qAdd_zero] at h2
  exact h2

/-- **移項**: |a − b| ≤ B なら a ≤ B + b。 -/
theorem qLe_abs_move {a b B : QRat}
    (h : qLe (qAbs (qAdd a (qNeg b))) B) : qLe a (qAdd B b) := by
  have e : a = qAdd (qAdd a (qNeg b)) b := by
    rw [qAdd_assoc a (qNeg b) b, qNeg_add_self b, qAdd_zero]
  have h2 : qLe (qAdd (qAdd a (qNeg b)) b) (qAdd B b) :=
    qLe_add (qAdd a (qNeg b)) B b
      (qLe_trans _ _ _ (qLe_self_abs (qAdd a (qNeg b))) h)
  exact qLe_trans _ _ _ (qLe_of_eq e) h2

/-- 分数の分割（qFrac_add の逆向き、等号なので ≤ 双方向）。 -/
theorem qFrac_split (c d m : Nat) :
    qLe (qFrac (c + d) m) (qAdd (qFrac c m) (qFrac d m)) := by
  show ((c + d : Nat) : Int) * (((m : Int) + 1) * ((m : Int) + 1))
    ≤ ((c : Int) * ((m : Int) + 1) + (d : Int) * ((m : Int) + 1))
      * ((m : Int) + 1)
  have e0 : ((c + d : Nat) : Int) = (c : Int) + (d : Int) := by omega
  rw [e0, ← Int.add_mul, Int.mul_assoc]
  exact Int.le_refl _

/-! ## M125-2: 正値性 -/

/-- **M125-2a: witness 形正値性** — ある添字で 2/(n+1) 以上
    （margin 2 が正則性の揺らぎを吸収する）。 -/
def IsPos (x : RReal) : Prop :=
  ∃ n : Nat, qLe (qFrac 2 n) (x.seq n)

/-- **M125-2b: 伝播** — witness n から任意添字 m の押さえ
    2/(n+1) ≤ (1/(n+1) + 1/(m+1)) + x_m。 -/
theorem isPos_spread {x : RReal} {n : Nat}
    (hn : qLe (qFrac 2 n) (x.seq n)) (m : Nat) :
    qLe (qFrac 2 n)
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac m)) (x.seq m)) :=
  qLe_trans _ _ _ hn (qLe_abs_move (x.reg n m))

/-! ## M125-3: ≈ 不変性 -/

/-- **定理 (M125-3): 正値性は realEq 不変** — witness n から
    添字 m = 5n+4 で margin 計算（5/(m+1) = 1/(n+1) がちょうど相殺）。 -/
theorem isPos_congr {x y : RReal} (hxy : realEq x y) (h : IsPos x) :
    IsPos y := by
  obtain ⟨n, hn⟩ := h
  refine ⟨5 * n + 4, ?_⟩
  -- x_m ≥ 2/(n+1) − (u_n + u_m)、y_m ≥ x_m − 2u_m
  have h1 : qLe (qFrac 2 n)
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac (5 * n + 4)))
        (x.seq (5 * n + 4))) := isPos_spread hn (5 * n + 4)
  have h2 : qLe (x.seq (5 * n + 4))
      (qAdd (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4)))
        (y.seq (5 * n + 4))) :=
    qLe_abs_move (hxy (5 * n + 4))
  -- 合成: F2n ≤ (u_n + u_m) + ((u_m + u_m) + y_m) = C + y_m
  have h3 : qLe (qFrac 2 n)
      (qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac (5 * n + 4)))
          (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4))))
        (y.seq (5 * n + 4))) := by
    have h4 := qLe_trans _ _ _ h1
      (qLe_add_two (qLe_refl (qAdd (qUnitFrac n) (qUnitFrac (5 * n + 4)))) h2)
    exact qLe_trans _ _ _ h4 (qLe_of_eq
      ((qAdd_assoc (qAdd (qUnitFrac n) (qUnitFrac (5 * n + 4)))
        (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4)))
        (y.seq (5 * n + 4))).symm))
  -- 濃縮: F2m + C ≤ F2n（C = u_n + 3u_m、5u_m = u_n）
  have hC : qLe (qAdd (qFrac 2 (5 * n + 4))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac (5 * n + 4)))
        (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4)))))
      (qFrac 2 n) := by
    -- u_m + (u_m + u_m) ≤ F3m、F2m + F3m ≤ F5m = u_n、u_n + u_n ≤ F2n
    have hm3 : qLe (qAdd (qUnitFrac (5 * n + 4))
        (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4))))
        (qFrac 3 (5 * n + 4)) :=
      qLe_trans _ _ _
        (qLe_add_two (qLe_refl _) (qFrac_add 1 1 (5 * n + 4)))
        (qFrac_add 1 2 (5 * n + 4))
    -- 並べ替え: F2m + ((u_n + u_m) + (u_m+u_m)) = (F2m + (u_m + (u_m+u_m))) + u_n
    have e1 : qAdd (qFrac 2 (5 * n + 4))
        (qAdd (qAdd (qUnitFrac n) (qUnitFrac (5 * n + 4)))
          (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4))))
        = qAdd (qAdd (qFrac 2 (5 * n + 4))
            (qAdd (qUnitFrac (5 * n + 4))
              (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4)))))
          (qUnitFrac n) := by
      rw [qAdd_assoc (qUnitFrac n) (qUnitFrac (5 * n + 4))
          (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4))),
        qAdd_comm (qUnitFrac n)
          (qAdd (qUnitFrac (5 * n + 4))
            (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4)))),
        ← qAdd_assoc (qFrac 2 (5 * n + 4))
          (qAdd (qUnitFrac (5 * n + 4))
            (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4))))
          (qUnitFrac n)]
    have h5 : qLe (qAdd (qFrac 2 (5 * n + 4))
        (qAdd (qUnitFrac (5 * n + 4))
          (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4)))))
        (qFrac 5 (5 * n + 4)) :=
      qLe_trans _ _ _ (qLe_add_two (qLe_refl _) hm3)
        (qFrac_add 2 3 (5 * n + 4))
    have h6 : qLe (qFrac 5 (5 * n + 4)) (qUnitFrac n) :=
      qFrac_le (by omega)
    have h7 : qLe (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 2 n) :=
      qFrac_add 1 1 n
    exact qLe_trans _ _ _ (qLe_of_eq e1)
      (qLe_trans _ _ _
        (qLe_add_two (qLe_trans _ _ _ h5 h6) (qLe_refl (qUnitFrac n)))
        h7)
  -- 消去: F2m + C ≤ F2n ≤ C + y_m → F2m ≤ y_m
  apply qLe_cancel_right (c := qAdd (qAdd (qUnitFrac n) (qUnitFrac (5 * n + 4)))
    (qAdd (qUnitFrac (5 * n + 4)) (qUnitFrac (5 * n + 4))))
  have h8 := qLe_trans _ _ _ hC h3
  exact qLe_trans _ _ _ h8 (qLe_of_eq (qAdd_comm _ _))

/-! ## M125-4: 零の非正値性と加法閉性 -/

/-- **M125-4a: 0 は正でない**。 -/
theorem isPos_zero_false : ¬ IsPos realZero := by
  intro h
  obtain ⟨n, hn⟩ := h
  have h' : (2 : Int) * 1 ≤ 0 * ((n : Int) + 1) := hn
  omega

/-- **定理 (M125-4b): 正値の加法閉性** — witness n₁, n₂ から
    N = max、添字 m = 3N+2 で合流（u_m + u_{2m+1} = u_N/2）。 -/
theorem isPos_add {x y : RReal} (hx : IsPos x) (hy : IsPos y) :
    IsPos (realAdd x y) := by
  obtain ⟨n1, h1⟩ := hx
  obtain ⟨n2, h2⟩ := hy
  -- N := n1 + n2 で両 witness を弱める（u_{n1}, u_{n2} ≥ u_N）
  refine ⟨3 * (n1 + n2) + 2, ?_⟩
  show qLe (qFrac 2 (3 * (n1 + n2) + 2))
    (qAdd (x.seq (2 * (3 * (n1 + n2) + 2) + 1))
      (y.seq (2 * (3 * (n1 + n2) + 2) + 1)))
  have hs1 := isPos_spread h1 (2 * (3 * (n1 + n2) + 2) + 1)
  have hs2 := isPos_spread h2 (2 * (3 * (n1 + n2) + 2) + 1)
  -- F2n1 + F2n2 ≤ (u_{n1}+u_s + x_s) + (u_{n2}+u_s + y_s)
  have hsum := qLe_add_two hs1 hs2
  -- 並べ替え: RHS = ((u_{n1}+u_s)+(u_{n2}+u_s)) + (x_s + y_s)
  have e1 : qAdd
      (qAdd (qAdd (qUnitFrac n1) (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1)))
        (x.seq (2 * (3 * (n1 + n2) + 2) + 1)))
      (qAdd (qAdd (qUnitFrac n2) (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1)))
        (y.seq (2 * (3 * (n1 + n2) + 2) + 1)))
      = qAdd
        (qAdd (qAdd (qUnitFrac n1) (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1)))
          (qAdd (qUnitFrac n2) (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1))))
        (qAdd (x.seq (2 * (3 * (n1 + n2) + 2) + 1))
          (y.seq (2 * (3 * (n1 + n2) + 2) + 1))) :=
    qAdd_swap_mid _ _ _ _
  -- 濃縮: F2m + ((u_{n1}+u_s)+(u_{n2}+u_s)) ≤ F2n1 + F2n2 は重いので
  -- 消去方式: F2m + C ≤ F4N 系で比較。C ≤ u_N + u_N + 2u_s、
  -- u_{ni} ≤ u_N は N = n1+n2 で qFrac_le。
  have hC : qLe (qAdd (qFrac 2 (3 * (n1 + n2) + 2))
      (qAdd (qAdd (qUnitFrac n1) (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1)))
        (qAdd (qUnitFrac n2) (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1)))))
      (qAdd (qFrac 2 n1) (qFrac 2 n2)) := by
    -- u_s ≤ u_m/2 = qFrac 1 (2m+1)、まとめて評価:
    -- F2m + u_{n1} + u_s + u_{n2} + u_s ≤ (u_{n1} + F2m/2 + …) …
    -- 直接: F2m + 2u_s ≤ F3m' ≤ u_{n1} … は添字混在なので、
    -- 片側ずつ: (F2m + u_s + u_s) ≤ F1n1 + F1n2 型に分ける。
    -- F2m + u_s + u_s = F2m + F2s-fold ≤ F2m + F1m = F3m ≤ ?
    -- 3/(3N+3) = 1/(N+1) ≤ u_{n1} … 分割: F3m ≤ F1N ≤ F1n1。
    -- 残り u_{n1} + u_{n2} ≤ F1n1 + F1n2。合計 ≤ F2n1 + F2n2
    -- （F1n1 + F1n1 ≤ F2n1 等で回収）。
    have hss : qLe (qAdd (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1))
        (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1)))
        (qFrac 1 (3 * (n1 + n2) + 2)) :=
      qLe_trans _ _ _ (qFrac_add 1 1 (2 * (3 * (n1 + n2) + 2) + 1))
        (qFrac_le (by omega))
    have hfold : qLe (qAdd (qFrac 2 (3 * (n1 + n2) + 2))
        (qFrac 1 (3 * (n1 + n2) + 2)))
        (qFrac 3 (3 * (n1 + n2) + 2)) := qFrac_add 2 1 _
    have h3N : qLe (qFrac 3 (3 * (n1 + n2) + 2)) (qFrac 1 n1) :=
      qFrac_le (by omega)
    -- 組み立て: LHS = F2m + ((u_{n1}+u_s)+(u_{n2}+u_s))
    --   = (F2m + (u_s+u_s)) + (u_{n1}+u_{n2})   [swap_mid + comm]
    have e2 : qAdd (qAdd (qUnitFrac n1)
          (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1)))
        (qAdd (qUnitFrac n2) (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1)))
        = qAdd (qAdd (qUnitFrac n1) (qUnitFrac n2))
          (qAdd (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1))
            (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1))) :=
      qAdd_swap_mid _ _ _ _
    have e3 : qAdd (qFrac 2 (3 * (n1 + n2) + 2))
        (qAdd (qAdd (qUnitFrac n1) (qUnitFrac n2))
          (qAdd (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1))
            (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1))))
        = qAdd (qAdd (qUnitFrac n1) (qUnitFrac n2))
          (qAdd (qFrac 2 (3 * (n1 + n2) + 2))
            (qAdd (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1))
              (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1)))) := by
      rw [← qAdd_assoc, qAdd_comm (qFrac 2 (3 * (n1 + n2) + 2))
          (qAdd (qUnitFrac n1) (qUnitFrac n2)), qAdd_assoc]
    have h9 : qLe (qAdd (qFrac 2 (3 * (n1 + n2) + 2))
        (qAdd (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1))
          (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1))))
        (qFrac 1 n1) :=
      qLe_trans _ _ _ (qLe_add_two (qLe_refl _) hss)
        (qLe_trans _ _ _ hfold h3N)
    -- 合計: (u_{n1}+u_{n2}) + F1n1 ≤ F2n1 + F2n2
    --   （u_{n1}+F1n1 ≤ F2n1、u_{n2} ≤ F2n2）
    have h10 : qLe (qAdd (qAdd (qUnitFrac n1) (qUnitFrac n2)) (qFrac 1 n1))
        (qAdd (qFrac 2 n1) (qFrac 2 n2)) := by
      have e4 : qAdd (qAdd (qUnitFrac n1) (qUnitFrac n2)) (qFrac 1 n1)
          = qAdd (qAdd (qUnitFrac n1) (qFrac 1 n1)) (qUnitFrac n2) := by
        rw [qAdd_assoc (qUnitFrac n1) (qUnitFrac n2) (qFrac 1 n1),
          qAdd_comm (qUnitFrac n2) (qFrac 1 n1),
          ← qAdd_assoc (qUnitFrac n1) (qFrac 1 n1) (qUnitFrac n2)]
      exact qLe_trans _ _ _ (qLe_of_eq e4)
        (qLe_add_two (qFrac_add 1 1 n1) (qFrac_le (by omega)))
    exact qLe_trans _ _ _
      (qLe_of_eq (by rw [e2]; exact e3))
      (qLe_trans _ _ _
        (qLe_add_two (qLe_refl (qAdd (qUnitFrac n1) (qUnitFrac n2))) h9)
        h10)
  -- 消去
  have hchain := qLe_trans _ _ _ hC
    (qLe_trans _ _ _ hsum (qLe_of_eq e1))
  apply qLe_cancel_right
    (c := qAdd (qAdd (qUnitFrac n1) (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1)))
      (qAdd (qUnitFrac n2) (qUnitFrac (2 * (3 * (n1 + n2) + 2) + 1))))
  exact qLe_trans _ _ _ hchain (qLe_of_eq (qAdd_comm _ _))


/-! ## M125-5: 狭義順序 rLt -/

/-- 移項: a + c ≤ b なら a ≤ b − c。 -/
theorem qLe_move_right {a b c : QRat} (h : qLe (qAdd a c) b) :
    qLe a (qAdd b (qNeg c)) := by
  have h2 := qLe_add (qAdd a c) b (qNeg c) h
  rw [qAdd_assoc a c (qNeg c), qAdd_neg_self c, qAdd_zero] at h2
  exact h2

/-- 移項: a ≤ b − c なら a + c ≤ b。 -/
theorem qLe_move_left {a b c : QRat} (h : qLe a (qAdd b (qNeg c))) :
    qLe (qAdd a c) b := by
  have h2 := qLe_add a (qAdd b (qNeg c)) c h
  rw [qAdd_assoc b (qNeg c) c, qNeg_add_self c, qAdd_zero] at h2
  exact h2

/-- **M125-5a: 狭義順序** x < y ⟺ y − x が正。 -/
def rLt (x y : RReal) : Prop := IsPos (realAdd y (realNeg x))

/-- realNeg の congruence（M117F の補完）。 -/
theorem realNeg_congr {x x' : RReal} (h : realEq x x') :
    realEq (realNeg x) (realNeg x') := by
  intro n
  have e : qAdd (qNeg (x.seq n)) (qNeg (qNeg (x'.seq n)))
      = qNeg (qAdd (x.seq n) (qNeg (x'.seq n))) := by
    rw [qNeg_add_dist]
  show qLe (qAbs (qAdd (qNeg (x.seq n)) (qNeg (qNeg (x'.seq n)))))
    (qAdd (qUnitFrac n) (qUnitFrac n))
  rw [e, qAbs_neg]
  exact h n

/-- **M125-5b: rLt の congruence**。 -/
theorem rLt_congr {x x' y y' : RReal} (hx : realEq x x')
    (hy : realEq y y') (h : rLt x y) : rLt x' y' :=
  isPos_congr
    (realEq_trans (realAdd_congr_left (realNeg x) hy)
      (realAdd_congr_right y' (realNeg_congr hx))) h

/-- **M125-5c: 非反射律**。 -/
theorem rLt_irrefl (x : RReal) : ¬ rLt x x := by
  intro h
  exact isPos_zero_false (isPos_congr (realAdd_neg x) h)

/-! ## M125-6: 推移律 -/

/-- (z − y) + (y − x) ≈ z − x（群法則の連鎖）。 -/
theorem rSub_chain (x y z : RReal) :
    realEq (realAdd (realAdd z (realNeg y)) (realAdd y (realNeg x)))
      (realAdd z (realNeg x)) := by
  -- ((z + −y) + (y + −x)) ≈ z + (−y + (y + −x)) ≈ z + ((−y + y) + −x)
  --   ≈ z + (0 + −x) ≈ z + (−x + 0) ≈ z + −x
  have s1 : realEq (realAdd (realAdd z (realNeg y)) (realAdd y (realNeg x)))
      (realAdd z (realAdd (realNeg y) (realAdd y (realNeg x)))) :=
    realAdd_assoc z (realNeg y) (realAdd y (realNeg x))
  have s2 : realEq (realAdd (realNeg y) (realAdd y (realNeg x)))
      (realAdd (realAdd (realNeg y) y) (realNeg x)) :=
    realEq_symm (realAdd_assoc (realNeg y) y (realNeg x))
  have s3 : realEq (realAdd (realNeg y) y) realZero :=
    realEq_trans (realAdd_comm (realNeg y) y) (realAdd_neg y)
  have s4 : realEq (realAdd (realAdd (realNeg y) y) (realNeg x))
      (realAdd realZero (realNeg x)) :=
    realAdd_congr_left (realNeg x) s3
  have s5 : realEq (realAdd realZero (realNeg x)) (realNeg x) :=
    realEq_trans (realAdd_comm realZero (realNeg x))
      (realAdd_zero (realNeg x))
  have s6 : realEq (realAdd (realNeg y) (realAdd y (realNeg x))) (realNeg x) :=
    realEq_trans s2 (realEq_trans s4 s5)
  exact realEq_trans s1 (realAdd_congr_right z s6)

/-- **定理 (M125-6): 推移律** — 正値の加法閉性と差の連鎖。 -/
theorem rLt_trans {x y z : RReal} (h1 : rLt x y) (h2 : rLt y z) :
    rLt x z :=
  isPos_congr (rSub_chain x y z) (isPos_add h2 h1)

/-! ## M125-7: 共推移性（本丸） -/

/-- **定理 (M125-7): 共推移性** — x < y なら任意の z に対して
    x < z か z < y（構成的三分律の代替）。有理数の全順序
    `qLe_total` による z の高精度比較で分岐し、margin 計算
    （u_n − u_s − u_t = 7/16·u_n ≥ 2u_m）で witness を構成。 -/
theorem rLt_cotrans {x y : RReal} (h : rLt x y) (z : RReal) :
    rLt x z ∨ rLt z y := by
  obtain ⟨n, hn⟩ := h
  -- hn : F2n ≤ y_s + (−x_s)、s := 2n+1
  -- 比較点: t := 2(8n+7)+1、比較値: x_s + 1/(n+1)
  cases qLe_total (qAdd (x.seq (2 * n + 1)) (qFrac 1 n))
      (z.seq (2 * (8 * n + 7) + 1)) with
  | inl hA =>
    -- z が上半分: x < z、witness m := 8n+7
    refine Or.inl ⟨8 * n + 7, ?_⟩
    show qLe (qFrac 2 (8 * n + 7))
      (qAdd (z.seq (2 * (8 * n + 7) + 1))
        (qNeg (x.seq (2 * (8 * n + 7) + 1))))
    apply qLe_move_right
    -- F2m + x_t ≤ z_t: x_t ≤ (u_t + u_s) + x_s、F2m + u_t + u_s ≤ F1n
    have hxt : qLe (x.seq (2 * (8 * n + 7) + 1))
        (qAdd (qAdd (qUnitFrac (2 * (8 * n + 7) + 1))
          (qUnitFrac (2 * n + 1))) (x.seq (2 * n + 1))) :=
      qLe_abs_move (x.reg (2 * (8 * n + 7) + 1) (2 * n + 1))
    have hcon : qLe (qAdd (qFrac 2 (8 * n + 7))
        (qAdd (qUnitFrac (2 * (8 * n + 7) + 1)) (qUnitFrac (2 * n + 1))))
        (qFrac 1 n) := by
      have f1 : qLe (qFrac 2 (8 * n + 7)) (qFrac 4 (2 * (8 * n + 7) + 1)) :=
        qFrac_le (by omega)
      have f2 : qLe (qUnitFrac (2 * n + 1)) (qFrac 8 (2 * (8 * n + 7) + 1)) :=
        qFrac_le (by omega)
      have f3 := qLe_add_two f1
        (qLe_add_two (qLe_refl (qUnitFrac (2 * (8 * n + 7) + 1))) f2)
      have f4 : qLe (qAdd (qFrac 4 (2 * (8 * n + 7) + 1))
          (qAdd (qFrac 1 (2 * (8 * n + 7) + 1))
            (qFrac 8 (2 * (8 * n + 7) + 1))))
          (qFrac 13 (2 * (8 * n + 7) + 1)) :=
        qLe_trans _ _ _
          (qLe_add_two (qLe_refl _) (qFrac_add 1 8 (2 * (8 * n + 7) + 1)))
          (qFrac_add 4 9 (2 * (8 * n + 7) + 1))
      have f5 : qLe (qFrac 13 (2 * (8 * n + 7) + 1)) (qFrac 1 n) :=
        qFrac_le (by omega)
      exact qLe_trans _ _ _ f3 (qLe_trans _ _ _ f4 f5)
    have step : qLe (qAdd (qFrac 2 (8 * n + 7))
        (x.seq (2 * (8 * n + 7) + 1)))
        (qAdd (qFrac 1 n) (x.seq (2 * n + 1))) := by
      have g1 := qLe_add_two (qLe_refl (qFrac 2 (8 * n + 7))) hxt
      have e : qAdd (qFrac 2 (8 * n + 7))
          (qAdd (qAdd (qUnitFrac (2 * (8 * n + 7) + 1))
            (qUnitFrac (2 * n + 1))) (x.seq (2 * n + 1)))
          = qAdd (qAdd (qFrac 2 (8 * n + 7))
              (qAdd (qUnitFrac (2 * (8 * n + 7) + 1))
                (qUnitFrac (2 * n + 1)))) (x.seq (2 * n + 1)) :=
        (qAdd_assoc _ _ _).symm
      exact qLe_trans _ _ _ g1 (qLe_trans _ _ _ (qLe_of_eq e)
        (qLe_add_two hcon (qLe_refl (x.seq (2 * n + 1)))))
    exact qLe_trans _ _ _ step
      (qLe_trans _ _ _ (qLe_of_eq (qAdd_comm _ _)) hA)
  | inr hB =>
    -- z が下半分: z < y、witness m := 8n+7
    refine Or.inr ⟨8 * n + 7, ?_⟩
    show qLe (qFrac 2 (8 * n + 7))
      (qAdd (y.seq (2 * (8 * n + 7) + 1))
        (qNeg (z.seq (2 * (8 * n + 7) + 1))))
    apply qLe_move_right
    -- F2m + z_t ≤ y_t: cancel (u_s + u_t) 方式
    apply qLe_cancel_right (c := qAdd (qUnitFrac (2 * n + 1))
      (qUnitFrac (2 * (8 * n + 7) + 1)))
    -- 左辺: (F2m + z_t) + (u_s + u_t) ≤ ((F2m + F1n) + (u_s+u_t)) + x_s
    have g1 : qLe (qAdd (qFrac 2 (8 * n + 7))
        (z.seq (2 * (8 * n + 7) + 1)))
        (qAdd (qFrac 2 (8 * n + 7))
          (qAdd (x.seq (2 * n + 1)) (qFrac 1 n))) :=
      qLe_add_two (qLe_refl _) hB
    -- 濃縮: F2m + F1n + (u_s + u_t) ≤ F2n
    have hcon2 : qLe (qAdd (qAdd (qFrac 2 (8 * n + 7)) (qFrac 1 n))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1))))
        (qFrac 2 n) := by
      have f1 : qLe (qFrac 2 (8 * n + 7)) (qFrac 4 (2 * (8 * n + 7) + 1)) :=
        qFrac_le (by omega)
      have f2 : qLe (qFrac 1 n) (qFrac 16 (2 * (8 * n + 7) + 1)) :=
        qFrac_le (by omega)
      have f3 : qLe (qUnitFrac (2 * n + 1)) (qFrac 8 (2 * (8 * n + 7) + 1)) :=
        qFrac_le (by omega)
      have f4 := qLe_add_two (qLe_add_two f1 f2)
        (qLe_add_two f3 (qLe_refl (qUnitFrac (2 * (8 * n + 7) + 1))))
      have f5 : qLe (qAdd (qAdd (qFrac 4 (2 * (8 * n + 7) + 1))
            (qFrac 16 (2 * (8 * n + 7) + 1)))
          (qAdd (qFrac 8 (2 * (8 * n + 7) + 1))
            (qFrac 1 (2 * (8 * n + 7) + 1))))
          (qFrac 29 (2 * (8 * n + 7) + 1)) :=
        qLe_trans _ _ _
          (qLe_add_two (qFrac_add 4 16 (2 * (8 * n + 7) + 1))
            (qFrac_add 8 1 (2 * (8 * n + 7) + 1)))
          (qFrac_add 20 9 (2 * (8 * n + 7) + 1))
      have f6 : qLe (qFrac 29 (2 * (8 * n + 7) + 1)) (qFrac 2 n) :=
        qFrac_le (by omega)
      exact qLe_trans _ _ _ f4 (qLe_trans _ _ _ f5 f6)
    -- 右辺への鎖: F2n + x_s ≤ y_s ≤ (u_s + u_t) + y_t
    have hys : qLe (qAdd (qFrac 2 n) (x.seq (2 * n + 1)))
        (y.seq (2 * n + 1)) := by
      apply qLe_move_left
      exact hn
    have hyt : qLe (y.seq (2 * n + 1))
        (qAdd (qAdd (qUnitFrac (2 * n + 1))
          (qUnitFrac (2 * (8 * n + 7) + 1)))
          (y.seq (2 * (8 * n + 7) + 1))) :=
      qLe_abs_move (y.reg (2 * n + 1) (2 * (8 * n + 7) + 1))
    -- 組み立て
    have e1 : qAdd (qAdd (qFrac 2 (8 * n + 7))
        (z.seq (2 * (8 * n + 7) + 1)))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1)))
        = qAdd (qAdd (qFrac 2 (8 * n + 7))
            (qAdd (qUnitFrac (2 * n + 1))
              (qUnitFrac (2 * (8 * n + 7) + 1))))
          (z.seq (2 * (8 * n + 7) + 1)) := by
      rw [qAdd_assoc (qFrac 2 (8 * n + 7)) (z.seq (2 * (8 * n + 7) + 1))
          (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1))),
        qAdd_comm (z.seq (2 * (8 * n + 7) + 1))
          (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1))),
        ← qAdd_assoc (qFrac 2 (8 * n + 7))
          (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1)))
          (z.seq (2 * (8 * n + 7) + 1))]
    have g2 : qLe (qAdd (qAdd (qFrac 2 (8 * n + 7))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1))))
        (z.seq (2 * (8 * n + 7) + 1)))
        (qAdd (qAdd (qFrac 2 (8 * n + 7))
          (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1))))
          (qAdd (x.seq (2 * n + 1)) (qFrac 1 n))) :=
      qLe_add_two (qLe_refl _) hB
    -- (F2m + (u_s+u_t)) + (x_s + F1n) = ((F2m + F1n) + (u_s+u_t)) + x_s
    have e2 : qAdd (qAdd (qFrac 2 (8 * n + 7))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1))))
        (qAdd (x.seq (2 * n + 1)) (qFrac 1 n))
        = qAdd (qAdd (qAdd (qFrac 2 (8 * n + 7)) (qFrac 1 n))
            (qAdd (qUnitFrac (2 * n + 1))
              (qUnitFrac (2 * (8 * n + 7) + 1))))
          (x.seq (2 * n + 1)) := by
      rw [qAdd_comm (x.seq (2 * n + 1)) (qFrac 1 n),
        qAdd_swap_mid (qFrac 2 (8 * n + 7))
          (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1)))
          (qFrac 1 n) (x.seq (2 * n + 1)),
        ← qAdd_assoc (qAdd (qFrac 2 (8 * n + 7)) (qFrac 1 n))
          (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1)))
          (x.seq (2 * n + 1))]
    have g3 : qLe (qAdd (qAdd (qAdd (qFrac 2 (8 * n + 7)) (qFrac 1 n))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * (8 * n + 7) + 1))))
        (x.seq (2 * n + 1)))
        (qAdd (qFrac 2 n) (x.seq (2 * n + 1))) :=
      qLe_add_two hcon2 (qLe_refl _)
    have g4 : qLe (qAdd (qFrac 2 n) (x.seq (2 * n + 1)))
        (qAdd (qAdd (qUnitFrac (2 * n + 1))
          (qUnitFrac (2 * (8 * n + 7) + 1)))
          (y.seq (2 * (8 * n + 7) + 1))) :=
      qLe_trans _ _ _ hys hyt
    exact qLe_trans _ _ _ (qLe_of_eq e1)
      (qLe_trans _ _ _ g2 (qLe_trans _ _ _ (qLe_of_eq e2)
        (qLe_trans _ _ _ g3 (qLe_trans _ _ _ g4
          (qLe_of_eq (qAdd_comm _ _))))))

/-! ## M125-8: 総括 -/

/-- **M125-8a: 総括** — 構成的順序のデータ。 -/
structure RealOrderData where
  /-- 正値性の ≈ 不変性。 -/
  pos_congr : ∀ {x y}, realEq x y → IsPos x → IsPos y
  /-- 0 は正でない。 -/
  pos_zero : ¬ IsPos realZero
  /-- 正値の加法閉性。 -/
  pos_add : ∀ {x y}, IsPos x → IsPos y → IsPos (realAdd x y)
  /-- rLt の congruence。 -/
  lt_congr : ∀ {x x' y y'}, realEq x x' → realEq y y' →
    rLt x y → rLt x' y'
  /-- 非反射律。 -/
  lt_irrefl : ∀ x, ¬ rLt x x
  /-- 推移律。 -/
  lt_trans : ∀ {x y z}, rLt x y → rLt y z → rLt x z
  /-- 共推移性。 -/
  lt_cotrans : ∀ {x y}, rLt x y → ∀ z, rLt x z ∨ rLt z y

/-- **M125-8b: witness**。 -/
def realOrderData : RealOrderData where
  pos_congr := isPos_congr
  pos_zero := isPos_zero_false
  pos_add := isPos_add
  lt_congr := rLt_congr
  lt_irrefl := rLt_irrefl
  lt_trans := rLt_trans
  lt_cotrans := rLt_cotrans

/-- **M125-8c: 存在**。 -/
theorem realOrder_exists : Nonempty RealOrderData :=
  ⟨realOrderData⟩

end IUT
