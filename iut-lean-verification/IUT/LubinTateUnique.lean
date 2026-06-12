/-
  IUT/LubinTateUnique.lean — M41（Lubin–Tate 補題: 一意性側）

  Lubin–Tate 型方程式 F∘g = c·F + F^q（f = cX + X^q を f∘F = c·F + F^q
  と環演算で展開した形）に対する解の**一意性**を、抽象可換環上の
  スキーマとして完全証明する:

    F(0) = F'(0) = 0、F(1) = F'(1)、双方が方程式を満たす ⟹ F = F'。

  証明は係数の強帰納法。係数 n ≥ 2 の方程式は

    L + F_n·(g_1)^n = c·F_n + T

  の形に分解され（L = 低次和、T = (F^q)_n は F_{<n} のみに依存）、
  2 解の差に消去仮説 hcancel（(g_1)^n − c の正則性の減算なし定式化:
  a·G + c·b = b·G + c·a ⟹ a = b）を適用する。

  * M41-1 `CRing.add_quad_swap` — 加法簿記 (a+t)+(t+b) = (b+t)+(t+a)
  * M41-2 `rpow` / `psSmul` — 環の冪・級数のスカラー倍
  * M41-3 `psPow_congr` — (Q^k)_m は Q_0..Q_m のみに依存
  * M41-4 `psPow_coeff_diag` — **対角係数** (g^k)_k = (g_1)^k
    （leading term の同定。g(0) = 0 で下三角 + 対角のみ生存）
  * M41-5 `psPow_coeff_congr` — **F_n 非依存性**: F(0) = 0 なら
    (F^{k+2})_n は F_{<n} のみで決まる（境界項は truncation と
    F(0) = 0 で消える）
  * M41-6 `lubin_tate_unique` — **一意性定理**（スキーマ）

  ℤ_p での消去仮説の充足（p^n − p = p(p^{n−1} − 1) の正則性 =
  捻れなし性 × 主単数の可逆性）と存在側（係数の再帰構成）は次段 M42。
  全て選択公理不使用。
-/
import IUT.Composition

namespace IUT

/-- **M41-1: 加法簿記** (a+t)+(t+b) = (b+t)+(t+a)。 -/
theorem CRing.add_quad_swap (R : CRing) (a b t : R.carrier) :
    R.add (R.add a t) (R.add t b) = R.add (R.add b t) (R.add t a) := by
  rw [R.add_assoc a t (R.add t b), ← R.add_assoc t t b,
    R.add_comm (R.add t t) b, ← R.add_assoc a b (R.add t t),
    R.add_assoc b t (R.add t a), ← R.add_assoc t t a,
    R.add_comm (R.add t t) a, ← R.add_assoc b a (R.add t t),
    R.add_comm b a]

/-- 環の冪。 -/
def rpow (R : CRing) (a : R.carrier) : Nat → R.carrier
  | 0 => R.one
  | k + 1 => R.mul (rpow R a k) a

/-- 級数のスカラー倍 (c·F)_n = c·F_n。 -/
def psSmul (R : CRing) (c : R.carrier) (F : PS R) : PS R :=
  fun n => R.mul c (F n)

/-- **M41-3**: (Q^k)_m は Q_0..Q_m のみに依存。 -/
theorem psPow_congr (R : CRing) (F F' : PS R) (b : Nat)
    (h : ∀ i, i ≤ b → F i = F' i) : ∀ k m, m ≤ b →
    psPow R F k m = psPow R F' k m := by
  intro k
  induction k with
  | zero => intro m _; rfl
  | succ k ih =>
    intro m hm
    show rsum R (fun j => R.mul (psPow R F k j) (F (m - j))) (m + 1)
      = rsum R (fun j => R.mul (psPow R F' k j) (F' (m - j))) (m + 1)
    exact rsum_congr R (m + 1) (fun j hj => by
      rw [ih j (by omega), h (m - j) (by omega)])

/-- **定理 (M41-4): 対角係数** — g(0) = 0 なら (g^k)_k = (g_1)^k。
    合成の leading term の同定。 -/
theorem psPow_coeff_diag (R : CRing) (g : PS R) (hg : g 0 = R.zero) :
    ∀ k, psPow R g k k = rpow R (g 1) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show rsum R (fun j => R.mul (psPow R g k j) (g (k + 1 - j))) (k + 2)
      = R.mul (rpow R (g 1) k) (g 1)
    have hs : rsum R (fun j => R.mul (psPow R g k j) (g (k + 1 - j))) (k + 2)
        = R.mul (psPow R g k k) (g (k + 1 - k)) :=
      rsum_single R _ k (k + 2) (by omega) (fun j hj hne => by
        cases Nat.lt_or_ge j k with
        | inl hlt =>
          rw [psPow_coeff_zero R g hg k j hlt]
          exact R.zero_mul _
        | inr hge =>
          have hj1 : j = k + 1 := by omega
          subst hj1
          rw [show k + 1 - (k + 1) = 0 by omega, hg]
          exact R.mul_zero _)
    rw [hs, show k + 1 - k = 1 by omega, ih]

/-- **定理 (M41-5): F_n 非依存性** — F(0) = F'(0) = 0 で F, F' が
    n 未満で一致すれば (F^{k+2})_n = (F'^{k+2})_n（境界項 j = 0 は
    truncation、j = n は F(0) = 0 で消える）。 -/
theorem psPow_coeff_congr (R : CRing) (F F' : PS R) (n : Nat)
    (hF : F 0 = R.zero) (hF' : F' 0 = R.zero)
    (hagree : ∀ j, j < n → F j = F' j) (k : Nat) :
    psPow R F (k + 2) n = psPow R F' (k + 2) n := by
  show rsum R (fun j => R.mul (psPow R F (k + 1) j) (F (n - j))) (n + 1)
    = rsum R (fun j => R.mul (psPow R F' (k + 1) j) (F' (n - j))) (n + 1)
  exact rsum_congr R (n + 1) (fun j hj => by
    cases Nat.decEq j 0 with
    | isTrue h0 =>
      subst h0
      rw [psPow_coeff_zero R F hF (k + 1) 0 (by omega),
        psPow_coeff_zero R F' hF' (k + 1) 0 (by omega),
        R.zero_mul, R.zero_mul]
    | isFalse h0 =>
      cases Nat.decEq j n with
      | isTrue hn =>
        rw [hn, show n - n = 0 by omega, hF, hF', R.mul_zero, R.mul_zero]
      | isFalse hn =>
        have h1 : psPow R F (k + 1) j = psPow R F' (k + 1) j :=
          psPow_congr R F F' j (fun i hi => hagree i (by omega)) (k + 1) j
            (Nat.le_refl j)
        have h2 : F (n - j) = F' (n - j) := hagree (n - j) (by omega)
        rw [h1, h2])

/-- **定理 (M41-6): Lubin–Tate 一意性**（スキーマ）—
    方程式 F∘g = c·F + F^q（g(0) = 0、q ≥ 2）の解は定数項 0 と
    一次係数で一意。消去仮説 hcancel は (g_1)^n − c（n ≥ 2）の
    正則性の減算なし定式化。 -/
theorem lubin_tate_unique (R : CRing) (g : PS R) (hg : g 0 = R.zero)
    (c : R.carrier) (q : Nat) (hq : 2 ≤ q)
    (hcancel : ∀ n a b, 2 ≤ n →
      R.add (R.mul a (rpow R (g 1) n)) (R.mul c b)
        = R.add (R.mul b (rpow R (g 1) n)) (R.mul c a) → a = b)
    (F F' : PS R)
    (hF0 : F 0 = R.zero) (hF'0 : F' 0 = R.zero) (hF1 : F 1 = F' 1)
    (eF : psComp R F g = (psRing R).add (psSmul R c F) (psPow R F q))
    (eF' : psComp R F' g = (psRing R).add (psSmul R c F') (psPow R F' q)) :
    F = F' := by
  obtain ⟨q', hq'⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  subst hq'
  have key : ∀ n, (∀ j, j < n → F j = F' j) → F n = F' n := by
    intro n hbelow
    cases n with
    | zero => exact hF0.trans hF'0.symm
    | succ m =>
      cases m with
      | zero => exact hF1
      | succ m =>
        have h1 : R.add
              (rsum R (fun k => R.mul (F k) (psPow R g k (m + 2))) (m + 2))
              (R.mul (F (m + 2)) (psPow R g (m + 2) (m + 2)))
            = R.add (R.mul c (F (m + 2))) (psPow R F (q' + 2) (m + 2)) :=
          congrFun eF (m + 2)
        have h2 : R.add
              (rsum R (fun k => R.mul (F' k) (psPow R g k (m + 2))) (m + 2))
              (R.mul (F' (m + 2)) (psPow R g (m + 2) (m + 2)))
            = R.add (R.mul c (F' (m + 2))) (psPow R F' (q' + 2) (m + 2)) :=
          congrFun eF' (m + 2)
        rw [psPow_coeff_diag R g hg (m + 2)] at h1 h2
        have hL : rsum R (fun k => R.mul (F' k) (psPow R g k (m + 2))) (m + 2)
            = rsum R (fun k => R.mul (F k) (psPow R g k (m + 2))) (m + 2) :=
          rsum_congr R (m + 2) (fun k hk => by rw [hbelow k (by omega)])
        have hT : psPow R F' (q' + 2) (m + 2) = psPow R F (q' + 2) (m + 2) :=
          (psPow_coeff_congr R F F' (m + 2) hF0 hF'0 hbelow q').symm
        rw [hL, hT] at h2
        have hX : R.add
            (R.add (rsum R (fun k => R.mul (F k) (psPow R g k (m + 2))) (m + 2))
              (psPow R F (q' + 2) (m + 2)))
            (R.add (R.mul (F (m + 2)) (rpow R (g 1) (m + 2)))
              (R.mul c (F' (m + 2))))
          = R.add
            (R.add (rsum R (fun k => R.mul (F k) (psPow R g k (m + 2))) (m + 2))
              (psPow R F (q' + 2) (m + 2)))
            (R.add (R.mul (F' (m + 2)) (rpow R (g 1) (m + 2)))
              (R.mul c (F (m + 2)))) := by
          rw [R.add_add_add_comm
              (rsum R (fun k => R.mul (F k) (psPow R g k (m + 2))) (m + 2))
              (psPow R F (q' + 2) (m + 2))
              (R.mul (F (m + 2)) (rpow R (g 1) (m + 2)))
              (R.mul c (F' (m + 2))),
            R.add_add_add_comm
              (rsum R (fun k => R.mul (F k) (psPow R g k (m + 2))) (m + 2))
              (psPow R F (q' + 2) (m + 2))
              (R.mul (F' (m + 2)) (rpow R (g 1) (m + 2)))
              (R.mul c (F (m + 2))),
            h1, h2]
          exact R.add_quad_swap (R.mul c (F (m + 2))) (R.mul c (F' (m + 2)))
            (psPow R F (q' + 2) (m + 2))
        have hAB := R.add_left_cancel hX
        exact hcancel (m + 2) (F (m + 2)) (F' (m + 2)) (by omega) hAB
  have all : ∀ n, ∀ j, j ≤ n → F j = F' j := by
    intro n
    induction n with
    | zero =>
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      exact key 0 (fun i hi => absurd hi (by omega))
    | succ n ih =>
      intro j hj
      cases Nat.lt_or_ge j (n + 1) with
      | inl h => exact ih j (by omega)
      | inr h =>
        have hj1 : j = n + 1 := by omega
        subst hj1
        exact key (n + 1) (fun i hi => ih i (by omega))
  funext n
  exact all n n (Nat.le_refl n)

end IUT
