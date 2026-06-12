/-
  IUT/PowerSeries.lean — M39（形式冪級数環 R[[X]]: Lubin–Tate 第二層）

  Lubin–Tate 形式群法則が住む形式冪級数環を自前で構成する。係数列
  Nat → R として実装し、積は Cauchy 畳み込み (PQ)_n = Σ_{k≤n} P_k Q_{n−k}。
  山場は**畳み込みの結合則**で、三角和の交換

    Σ_{j≤n} Σ_{k≤j} g(k, j−k) = Σ_{k≤n} Σ_{l≤n−k} g(k, l)

  を直接帰納で証明して両辺を共通形 Σ_{k+l≤n} P_k Q_l S_{n−k−l} に
  帰着させる（矩形化・指示関数を使わない）。

  * M39-1 一般有限和 `rsum` — congr・加法・head 分解・定数 0・
    スカラー倍（左右）・**反転** Σf(k) = Σf(m−k)
  * M39-2 `rsum_triangle` — **三角和の交換**（結合則の核、直接帰納）
  * M39-3 `PS` / `psAdd` / `psMul` / `psOne` — 係数列・点ごとの加法・
    Cauchy 積・単位元 (1, 0, 0, …)
  * M39-4 `psRing` — **R[[X]] は可換環**: 可換性は反転補題、
    結合則は三角交換、分配は項ごとの分配 + 和の加法性
  * M39-5 `psC` / `psConstHom` / `psX` — 定数項埋め込みの環準同型性と
    変数 X（M40 の合成・Lubin–Tate 補題への入口）

  全て選択公理不使用（ite の判定は Nat.decEq）。
-/
import IUT.Ring

namespace IUT

/-! ## CRing の追加簿記 -/

/-- 0·a = 0。 -/
theorem CRing.zero_mul (R : CRing) (a : R.carrier) :
    R.mul R.zero a = R.zero := by
  rw [R.mul_comm]
  exact R.mul_zero a

/-- a + 0 = a。 -/
theorem CRing.add_zero (R : CRing) (a : R.carrier) : R.add a R.zero = a := by
  rw [R.add_comm]
  exact R.zero_add a

/-- (a+b)+(c+d) = (a+c)+(b+d)。 -/
theorem CRing.add_add_add_comm (R : CRing) (a b c d : R.carrier) :
    R.add (R.add a b) (R.add c d) = R.add (R.add a c) (R.add b d) := by
  rw [R.add_assoc a b (R.add c d), ← R.add_assoc b c d, R.add_comm b c,
    R.add_assoc c b d, ← R.add_assoc a c (R.add b d)]

/-! ## 一般有限和 -/

/-- 一般可換環上の有限和 Σ_{k<n} f k。 -/
def rsum (R : CRing) (f : Nat → R.carrier) : Nat → R.carrier
  | 0 => R.zero
  | n + 1 => R.add (rsum R f n) (f n)

/-- 有限和は範囲内の値だけで決まる。 -/
theorem rsum_congr (R : CRing) {f g : Nat → R.carrier} : ∀ n,
    (∀ k, k < n → f k = g k) → rsum R f n = rsum R g n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    show R.add (rsum R f n) (f n) = R.add (rsum R g n) (g n)
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

/-- 有限和の加法性。 -/
theorem rsum_add (R : CRing) (f g : Nat → R.carrier) : ∀ n,
    rsum R (fun k => R.add (f k) (g k)) n = R.add (rsum R f n) (rsum R g n) := by
  intro n
  induction n with
  | zero =>
    show R.zero = R.add R.zero R.zero
    rw [R.zero_add]
  | succ n ih =>
    show R.add (rsum R (fun k => R.add (f k) (g k)) n) (R.add (f n) (g n))
      = R.add (R.add (rsum R f n) (f n)) (R.add (rsum R g n) (g n))
    rw [ih]
    exact R.add_add_add_comm _ _ _ _

/-- 有限和の頭出し。 -/
theorem rsum_head (R : CRing) (f : Nat → R.carrier) : ∀ n,
    rsum R f (n + 1) = R.add (f 0) (rsum R (fun k => f (k + 1)) n) := by
  intro n
  induction n with
  | zero =>
    show R.add R.zero (f 0) = R.add (f 0) R.zero
    exact R.add_comm _ _
  | succ n ih =>
    show R.add (rsum R f (n + 1)) (f (n + 1))
      = R.add (f 0) (R.add (rsum R (fun k => f (k + 1)) n) (f (n + 1)))
    rw [ih, R.add_assoc]

/-- 定数 0 の和は 0。 -/
theorem rsum_const_zero (R : CRing) : ∀ n,
    rsum R (fun _ => R.zero) n = R.zero := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show R.add (rsum R (fun _ => R.zero) n) R.zero = R.zero
    rw [ih, R.zero_add]

/-- 左スカラー倍: c·Σf = Σ c·f。 -/
theorem rsum_mul_left (R : CRing) (f : Nat → R.carrier) (c : R.carrier) : ∀ n,
    R.mul c (rsum R f n) = rsum R (fun k => R.mul c (f k)) n := by
  intro n
  induction n with
  | zero =>
    show R.mul c R.zero = R.zero
    exact R.mul_zero c
  | succ n ih =>
    show R.mul c (R.add (rsum R f n) (f n))
      = R.add (rsum R (fun k => R.mul c (f k)) n) (R.mul c (f n))
    rw [R.left_distrib, ih]

/-- 右スカラー倍: (Σf)·c = Σ f·c。 -/
theorem rsum_mul_right (R : CRing) (f : Nat → R.carrier) (c : R.carrier) : ∀ n,
    R.mul (rsum R f n) c = rsum R (fun k => R.mul (f k) c) n := by
  intro n
  rw [R.mul_comm, rsum_mul_left]
  exact rsum_congr R n (fun k _ => R.mul_comm c (f k))

/-- **M39-1: 和の反転** — Σ_{k<m+1} f k = Σ_{k<m+1} f (m−k)。 -/
theorem rsum_reflect (R : CRing) : ∀ (m : Nat) (f : Nat → R.carrier),
    rsum R f (m + 1) = rsum R (fun k => f (m - k)) (m + 1) := by
  intro m
  induction m with
  | zero => intro f; rfl
  | succ m ih =>
    intro f
    show R.add (rsum R f (m + 1)) (f (m + 1))
      = rsum R (fun k => f (m + 1 - k)) (m + 2)
    have hhead : rsum R (fun k => f (m + 1 - k)) (m + 2)
        = R.add (f (m + 1)) (rsum R (fun k => f (m + 1 - (k + 1))) (m + 1)) :=
      rsum_head R _ (m + 1)
    rw [hhead]
    have hidx : rsum R (fun k => f (m + 1 - (k + 1))) (m + 1)
        = rsum R (fun k => f (m - k)) (m + 1) :=
      rsum_congr R (m + 1) (fun k _ => by
        rw [show m + 1 - (k + 1) = m - k by omega])
    rw [hidx, ← ih f]
    exact R.add_comm _ _

/-- **定理 (M39-2): 三角和の交換** —
    Σ_{j≤n} Σ_{k≤j} g(k, j−k) = Σ_{k≤n} Σ_{l≤n−k} g(k, l)。
    畳み込み結合則の核（直接帰納による）。 -/
theorem rsum_triangle (R : CRing) (g : Nat → Nat → R.carrier) : ∀ n,
    rsum R (fun j => rsum R (fun k => g k (j - k)) (j + 1)) (n + 1)
      = rsum R (fun k => rsum R (fun l => g k l) (n + 1 - k)) (n + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show R.add (rsum R (fun j => rsum R (fun k => g k (j - k)) (j + 1)) (n + 1))
        (rsum R (fun k => g k (n + 1 - k)) (n + 2))
      = rsum R (fun k => rsum R (fun l => g k l) (n + 2 - k)) (n + 2)
    rw [ih]
    have hA : rsum R (fun k => g k (n + 1 - k)) (n + 2)
        = R.add (rsum R (fun k => g k (n + 1 - k)) (n + 1)) (g (n + 1) 0) := by
      show R.add (rsum R (fun k => g k (n + 1 - k)) (n + 1)) (g (n + 1) (n + 1 - (n + 1)))
        = R.add (rsum R (fun k => g k (n + 1 - k)) (n + 1)) (g (n + 1) 0)
      rw [show n + 1 - (n + 1) = 0 by omega]
    rw [hA]
    have hR : rsum R (fun k => rsum R (fun l => g k l) (n + 2 - k)) (n + 2)
        = R.add (rsum R (fun k => rsum R (fun l => g k l) (n + 2 - k)) (n + 1))
            (R.add R.zero (g (n + 1) 0)) := by
      show R.add (rsum R (fun k => rsum R (fun l => g k l) (n + 2 - k)) (n + 1))
          (rsum R (fun l => g (n + 1) l) (n + 2 - (n + 1)))
        = _
      rw [show n + 2 - (n + 1) = 1 by omega]
      rfl
    rw [hR]
    have hsplit : rsum R (fun k => rsum R (fun l => g k l) (n + 2 - k)) (n + 1)
        = rsum R (fun k => R.add (rsum R (fun l => g k l) (n + 1 - k))
            (g k (n + 1 - k))) (n + 1) :=
      rsum_congr R (n + 1) (fun k hk => by
        have hb : n + 2 - k = (n + 1 - k) + 1 := by omega
        rw [hb]
        rfl)
    rw [hsplit]
    have hadd : rsum R (fun k => R.add (rsum R (fun l => g k l) (n + 1 - k))
          (g k (n + 1 - k))) (n + 1)
        = R.add (rsum R (fun k => rsum R (fun l => g k l) (n + 1 - k)) (n + 1))
            (rsum R (fun k => g k (n + 1 - k)) (n + 1)) :=
      rsum_add R _ _ (n + 1)
    rw [hadd, R.zero_add, ← R.add_assoc]

/-! ## 形式冪級数 -/

/-- **M39-3: 形式冪級数**（係数列）。 -/
def PS (R : CRing) : Type := Nat → R.carrier

/-- 点ごとの加法。 -/
def psAdd (R : CRing) (P Q : PS R) : PS R := fun n => R.add (P n) (Q n)

/-- 零級数。 -/
def psZero (R : CRing) : PS R := fun _ => R.zero

/-- 点ごとの符号反転。 -/
def psNeg (R : CRing) (P : PS R) : PS R := fun n => R.neg (P n)

/-- **Cauchy 積** (PQ)_n = Σ_{k≤n} P_k Q_{n−k}。 -/
def psMul (R : CRing) (P Q : PS R) : PS R :=
  fun n => rsum R (fun k => R.mul (P k) (Q (n - k))) (n + 1)

/-- 単位級数 (1, 0, 0, …)。 -/
def psOne (R : CRing) : PS R := fun n => if n = 0 then R.one else R.zero

/-- **定理 (M39-4): R[[X]] は可換環** — 可換性は反転、結合則は
    三角交換、分配は項ごとの分配と和の加法性。 -/
def psRing (R : CRing) : CRing where
  carrier := PS R
  add := psAdd R
  zero := psZero R
  neg := psNeg R
  mul := psMul R
  one := psOne R
  add_assoc := by
    intro P Q S
    funext n
    exact R.add_assoc _ _ _
  zero_add := by
    intro P
    funext n
    exact R.zero_add _
  neg_add := by
    intro P
    funext n
    exact R.neg_add _
  add_comm := by
    intro P Q
    funext n
    exact R.add_comm _ _
  mul_assoc := by
    intro P Q S
    funext n
    show rsum R (fun j => R.mul (rsum R (fun k => R.mul (P k) (Q (j - k))) (j + 1))
        (S (n - j))) (n + 1)
      = rsum R (fun k => R.mul (P k)
          (rsum R (fun l => R.mul (Q l) (S (n - k - l))) (n - k + 1))) (n + 1)
    have h1 : rsum R (fun j => R.mul (rsum R (fun k => R.mul (P k) (Q (j - k))) (j + 1))
          (S (n - j))) (n + 1)
        = rsum R (fun j => rsum R (fun k => R.mul (R.mul (P k) (Q (j - k)))
            (S (n - j))) (j + 1)) (n + 1) :=
      rsum_congr R (n + 1) (fun j _ => rsum_mul_right R _ (S (n - j)) (j + 1))
    have h2 : rsum R (fun j => rsum R (fun k => R.mul (R.mul (P k) (Q (j - k)))
          (S (n - j))) (j + 1)) (n + 1)
        = rsum R (fun j => rsum R (fun k => R.mul (R.mul (P k) (Q (j - k)))
            (S (n - (k + (j - k))))) (j + 1)) (n + 1) :=
      rsum_congr R (n + 1) (fun j _ =>
        rsum_congr R (j + 1) (fun k hk => by
          rw [show k + (j - k) = j by omega]))
    have h3 : rsum R (fun j => rsum R (fun k => R.mul (R.mul (P k) (Q (j - k)))
          (S (n - (k + (j - k))))) (j + 1)) (n + 1)
        = rsum R (fun k => rsum R (fun l => R.mul (R.mul (P k) (Q l))
            (S (n - (k + l)))) (n + 1 - k)) (n + 1) :=
      rsum_triangle R (fun k l => R.mul (R.mul (P k) (Q l)) (S (n - (k + l)))) n
    have h4 : rsum R (fun k => rsum R (fun l => R.mul (R.mul (P k) (Q l))
          (S (n - (k + l)))) (n + 1 - k)) (n + 1)
        = rsum R (fun k => R.mul (P k)
            (rsum R (fun l => R.mul (Q l) (S (n - k - l))) (n - k + 1))) (n + 1) :=
      rsum_congr R (n + 1) (fun k hk => by
        have hb : n + 1 - k = n - k + 1 := by omega
        rw [hb]
        have h5 : rsum R (fun l => R.mul (R.mul (P k) (Q l)) (S (n - (k + l))))
              (n - k + 1)
            = rsum R (fun l => R.mul (P k) (R.mul (Q l) (S (n - k - l))))
              (n - k + 1) :=
          rsum_congr R (n - k + 1) (fun l _ => by
            rw [show n - (k + l) = n - k - l by omega, R.mul_assoc])
        rw [h5]
        exact (rsum_mul_left R (fun l => R.mul (Q l) (S (n - k - l)))
          (P k) (n - k + 1)).symm)
    rw [h1, h2, h3, h4]
  one_mul := by
    intro P
    funext n
    show rsum R (fun k => R.mul (psOne R k) (P (n - k))) (n + 1) = P n
    have hhead : rsum R (fun k => R.mul (psOne R k) (P (n - k))) (n + 1)
        = R.add (R.mul (psOne R 0) (P (n - 0)))
            (rsum R (fun k => R.mul (psOne R (k + 1)) (P (n - (k + 1)))) n) :=
      rsum_head R _ n
    rw [hhead]
    have hz : rsum R (fun k => R.mul (psOne R (k + 1)) (P (n - (k + 1)))) n
        = R.zero := by
      have hc : rsum R (fun k => R.mul (psOne R (k + 1)) (P (n - (k + 1)))) n
          = rsum R (fun _ => R.zero) n :=
        rsum_congr R n (fun k _ => by
          show R.mul R.zero (P (n - (k + 1))) = R.zero
          exact R.zero_mul _)
      rw [hc]
      exact rsum_const_zero R n
    rw [hz]
    show R.add (R.mul R.one (P n)) R.zero = P n
    rw [R.one_mul, R.add_zero]
  mul_comm := by
    intro P Q
    funext n
    show rsum R (fun k => R.mul (P k) (Q (n - k))) (n + 1)
      = rsum R (fun k => R.mul (Q k) (P (n - k))) (n + 1)
    have hrefl : rsum R (fun k => R.mul (P k) (Q (n - k))) (n + 1)
        = rsum R (fun k => R.mul (P (n - k)) (Q (n - (n - k)))) (n + 1) :=
      rsum_reflect R n (fun k => R.mul (P k) (Q (n - k)))
    rw [hrefl]
    exact rsum_congr R (n + 1) (fun k hk => by
      rw [show n - (n - k) = k by omega]
      exact R.mul_comm _ _)
  left_distrib := by
    intro P Q S
    funext n
    show rsum R (fun k => R.mul (P k) (R.add (Q (n - k)) (S (n - k)))) (n + 1)
      = R.add (rsum R (fun k => R.mul (P k) (Q (n - k))) (n + 1))
          (rsum R (fun k => R.mul (P k) (S (n - k))) (n + 1))
    have hc : rsum R (fun k => R.mul (P k) (R.add (Q (n - k)) (S (n - k)))) (n + 1)
        = rsum R (fun k => R.add (R.mul (P k) (Q (n - k)))
            (R.mul (P k) (S (n - k)))) (n + 1) :=
      rsum_congr R (n + 1) (fun k _ => R.left_distrib _ _ _)
    rw [hc]
    exact rsum_add R _ _ (n + 1)

/-! ## 定数と変数 -/

/-- 定数項埋め込み。 -/
def psC (R : CRing) (r : R.carrier) : PS R := fun n => if n = 0 then r else R.zero

/-- 変数 X = (0, 1, 0, 0, …)。 -/
def psX (R : CRing) : PS R := fun n => if n = 1 then R.one else R.zero

/-- **定理 (M39-5): 定数項埋め込みは環準同型** R → R[[X]]。 -/
def psConstHom (R : CRing) : RingHom R (psRing R) where
  map := psC R
  map_add := fun r s => by
    funext n
    cases n with
    | zero => rfl
    | succ m =>
      show R.zero = R.add R.zero R.zero
      rw [R.zero_add]
  map_mul := fun r s => by
    funext n
    cases n with
    | zero =>
      show R.mul r s = R.add R.zero (R.mul r s)
      rw [R.zero_add]
    | succ m =>
      show R.zero = rsum R (fun k => R.mul (psC R r k) (psC R s (m + 1 - k))) (m + 2)
      have hc : rsum R (fun k => R.mul (psC R r k) (psC R s (m + 1 - k))) (m + 2)
          = rsum R (fun _ => R.zero) (m + 2) :=
        rsum_congr R (m + 2) (fun k _ => by
          cases k with
          | zero =>
            show R.mul r (psC R s (m + 1)) = R.zero
            show R.mul r R.zero = R.zero
            exact R.mul_zero r
          | succ j =>
            show R.mul R.zero (psC R s (m + 1 - (j + 1))) = R.zero
            exact R.zero_mul _)
      rw [hc, rsum_const_zero]
  map_one := rfl

end IUT
