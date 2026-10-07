/-
  IUT/CyclicUnits.lean — M104（B-3 完全終結: 被覆定理と μ_{p−1} への移送）

  M103 で原始根 g（ord g = p−1）の存在を示した。本モジュールは
  **被覆**（全ての単数が g の冪であること）を機械検証し、M101 の
  同型 teichBar で **μ_{p−1} が巡回群であること**へ移送する。
  これで issue #36 B-3「μ_{p−1} ≅ (ℤ/p)^× の巡回性同定」が
  statement・証明とも完全に閉じる。

  被覆の論法: c が g^0, …, g^{p−2} のどれとも異なると仮定すると、
  これら p−1 個の相異なる冪（M102-8）と c を合わせた p 個の相異なる
  元が全て X^{p−1} − 1 の根（Fermat）となり roots_bound（M96）に
  矛盾。∃ への変換は **有界探索の決定可能性**（M17 の
  decidableBoundedExists）+ ℤ/n の等値 Bool 判定で構成的に行う
  （選択公理回避）。

  * M104-1 `zmodEqb` / `zmodEqb_true` / `zmodEqb_false` — ℤ/n の
    等値 Bool 判定（差の零判定 = M91F zmodIsZero の再利用）
  * M104-2 `zpPow_zero` / `teichBar_pow` — teichBar は冪と交換
    （ω̄(c^k) = ω̄(c)^k、M101 乗法性の反復）
  * M104-3 `generator_covers` — **被覆**: ord g = p−1 なら任意の単数
    c に対し ∃ k ≤ p−2, g^k = c（有界探索 + roots_bound の背理）
  * M104-4 `zmodUnits_cyclic` — **(ℤ/p)^× は巡回群**（原始根の存在
    M103 と被覆のパッケージ）
  * M104-5 `mu_powers_distinct` / `mu_cyclic` — **μ_{p−1} は巡回群**:
    ω̄(g) の冪が μ_{p−1} を枚挙する（teichBar_pow + 全射性 M101-6 の
    合流。B-3 の最終形）

  これで柱B の B-3 は残件ゼロ。B-1（Λₙ 塔の生成元）・B-2（分岐 rec
  の全射性）が柱B の残りタスク。
  全て選択公理不使用。
-/
import IUT.PrimitiveRoot
import IUT.Finiteness
import IUT.ZpDomain

namespace IUT

/-! ## ℤ/n の等値 Bool 判定 -/

/-- **M104-1a: 等値判定** — 差（加法群の演算）の零判定。 -/
def zmodEqb (n : Nat) (c d : (zmod n).carrier) : Bool :=
  zmodIsZero n ((zmod n).mul c ((zmod n).inv d))

/-- **M104-1b**: 判定が true なら等しい。 -/
theorem zmodEqb_true {n : Nat} {c d : (zmod n).carrier}
    (h : zmodEqb n c d = true) : c = d := by
  have h1 : (zmod n).mul c ((zmod n).inv d) = (zmod n).one :=
    zmodIsZero_true n _ h
  have h3 : (zmod n).mul ((zmod n).mul c ((zmod n).inv d)) d
      = (zmod n).mul (zmod n).one d :=
    congrArg (fun w => (zmod n).mul w d) h1
  rw [(zmod n).mul_assoc, (zmod n).inv_mul, (zmod n).one_mul,
    Grp.mul_one] at h3
  exact h3

/-- **M104-1c**: 判定が false なら異なる。 -/
theorem zmodEqb_false {n : Nat} {c d : (zmod n).carrier}
    (h : zmodEqb n c d = false) : c ≠ d := by
  intro heq
  rw [heq] at h
  have h1 : (zmod n).mul d ((zmod n).inv d) = (zmod n).one :=
    Grp.mul_inv (zmod n) d
  have h2 : zmodEqb n d d = true := by
    show zmodIsZero n ((zmod n).mul d ((zmod n).inv d)) = true
    rw [h1]
    exact zmodIsZero_zero n
  rw [h2] at h
  exact Bool.noConfusion h

/-! ## teichBar は冪と交換 -/

/-- **M104-2a**: x^0 = 1（ℤ_p 冪の基底）。 -/
theorem zpPow_zero (p : Nat) (x : (Zp p).carrier) : zpPow p x 0 = zpOne p := by
  apply Subtype.ext
  funext n
  show zmodPow (p ^ n) (x.val n) 0 = Quot.mk (modCong (p ^ n)).rel 1
  induction x.val n using Quot.ind; rename_i a
  rfl

/-- **M104-2b: teichBar は冪と交換** — ω̄(c^k) = ω̄(c)^k
    （M101 乗法性の反復）。 -/
theorem teichBar_pow (p : Nat) (hp : IsPrime p) (c : (zmod (p ^ 1)).carrier) :
    ∀ k, teichBar p hp (zmodPow (p ^ 1) c k)
      = zpPow p (teichBar p hp c) k := by
  intro k
  induction k with
  | zero =>
    rw [zpPow_zero]
    induction c using Quot.ind; rename_i a
    show teich p hp 1 = zpOne p
    exact teich_one p hp
  | succ k ih =>
    rw [zmodPow_succ, teichBar_mul, ih, ← zpPow_succ]

/-! ## 被覆定理 -/

/-- **定理 (M104-3): 被覆** — ord g = p−1 なら任意の単数 c は g の冪
    g^k（k ≤ p−2）。有界探索（M17 の決定可能性）で witness を構成的に
    取り、見つからない場合は g^0, …, g^{p−2}, c の p 個の相異なる元が
    全て X^{p−1} − 1 の根（Fermat）となって roots_bound（M96）に矛盾。 -/
theorem generator_covers (p : Nat) (hp : IsPrime p)
    {g : (zmod (p ^ 1)).carrier} (hg : IsZmodUnit p g)
    (hord : zmodOrd p g = p - 1) :
    ∀ c, IsZmodUnit p c →
      ∃ k, k ≤ p - 2 ∧ zmodPow (p ^ 1) g k = c := by
  intro c hc
  have hp2 := hp.1
  cases decidableBoundedExists
      (fun k => zmodEqb (p ^ 1) (zmodPow (p ^ 1) g k) c = true) (p - 2) with
  | isTrue h =>
    obtain ⟨k, hk, hP⟩ := h
    exact ⟨k, hk, zmodEqb_true hP⟩
  | isFalse h =>
    exfalso
    have hne : ∀ k, k ≤ p - 2 → zmodPow (p ^ 1) g k ≠ c := by
      intro k hk
      cases htest : zmodEqb (p ^ 1) (zmodPow (p ^ 1) g k) c with
      | true => exact absurd ⟨k, hk, htest⟩ h
      | false => exact zmodEqb_false htest
    have hdist : ∀ i j, i < j → j ≤ p - 2 + 1 →
        (fun i => if i ≤ p - 2 then zmodPow (p ^ 1) g i else c) i
          ≠ (fun i => if i ≤ p - 2 then zmodPow (p ^ 1) g i else c) j := by
      intro i j hij hj heq
      have heq' : (if i ≤ p - 2 then zmodPow (p ^ 1) g i else c)
          = (if j ≤ p - 2 then zmodPow (p ^ 1) g j else c) := heq
      cases Nat.lt_or_ge (p - 2) j with
      | inr hjle =>
        -- j ≤ p−2: 両方 g の冪
        have hi' : i ≤ p - 2 := by omega
        rw [if_pos hi', if_pos hjle] at heq'
        exact zmodOrd_powers_distinct p hp hg i j hij
          (by rw [hord]; omega) heq'
      | inl hjgt =>
        -- j = p−1: r j = c、r i = g^i
        have hi' : i ≤ p - 2 := by omega
        rw [if_pos hi', if_neg (by omega : ¬ j ≤ p - 2)] at heq'
        exact hne i hi' heq'
    have hroots : ∀ i, i ≤ p - 2 + 1 →
        rpow (zmodRing (p ^ 1))
          ((fun i => if i ≤ p - 2 then zmodPow (p ^ 1) g i else c) i)
          (p - 2 + 1)
        = (zmodRing (p ^ 1)).one := by
      intro i hi
      have hu : IsZmodUnit p
          ((fun i => if i ≤ p - 2 then zmodPow (p ^ 1) g i else c) i) := by
        cases Nat.lt_or_ge (p - 2) i with
        | inr hile =>
          show IsZmodUnit p (if i ≤ p - 2 then zmodPow (p ^ 1) g i else c)
          rw [if_pos hile]
          exact isZmodUnit_pow p hp hg i
        | inl higt =>
          show IsZmodUnit p (if i ≤ p - 2 then zmodPow (p ^ 1) g i else c)
          rw [if_neg (by omega : ¬ i ≤ p - 2)]
          exact hc
      show rpow (zmodRing (p ^ 1))
          (if i ≤ p - 2 then zmodPow (p ^ 1) g i else c) (p - 2 + 1)
        = (zmodRing (p ^ 1)).one
      rw [← zmodPow_eq_rpow]
      have hcong : zmodPow (p ^ 1)
          (if i ≤ p - 2 then zmodPow (p ^ 1) g i else c) (p - 2 + 1)
          = zmodPow (p ^ 1)
            (if i ≤ p - 2 then zmodPow (p ^ 1) g i else c) (p - 1) :=
        congrArg (zmodPow (p ^ 1) _) (by omega)
      exact hcong.trans (zmodUnit_pow_card p hp hu)
    exact bin_roots_bound (zmodRing (p ^ 1)) (zmod_no_zero_div p hp)
      (zmodRing_one_ne_zero p hp) (zmodRing (p ^ 1)).one (p - 2)
      (fun i => if i ≤ p - 2 then zmodPow (p ^ 1) g i else c)
      hdist hroots

/-! ## (ℤ/p)^× は巡回群（総括） -/

/-- **定理 (M104-4): (ℤ/p)^× は巡回群** — 原始根 g が存在し、任意の
    単数は g^k（k ≤ p−2）。M103 と被覆のパッケージ。 -/
theorem zmodUnits_cyclic (p : Nat) (hp : IsPrime p) :
    ∃ g, IsZmodUnit p g ∧ zmodOrd p g = p - 1 ∧
      ∀ c, IsZmodUnit p c → ∃ k, k ≤ p - 2 ∧ zmodPow (p ^ 1) g k = c := by
  obtain ⟨g, hg, hord⟩ := primitive_root_exists p hp
  exact ⟨g, hg, hord, generator_covers p hp hg hord⟩

/-! ## μ_{p−1} への移送（B-3 の最終形） -/

/-- **M104-5a: μ 側の冪の相異性** — ω̄(g) の冪 i < j < ord g は
    相異なる（teichBar の単射性 M101-7 で ℤ/p 側に降ろす）。 -/
theorem mu_powers_distinct (p : Nat) (hp : IsPrime p)
    {g : (zmod (p ^ 1)).carrier} (hg : IsZmodUnit p g) {i j : Nat}
    (hij : i < j) (hj : j < zmodOrd p g) :
    zpPow p (teichBar p hp g) i ≠ zpPow p (teichBar p hp g) j := by
  intro heq
  have h1 : teichBar p hp (zmodPow (p ^ 1) g i)
      = teichBar p hp (zmodPow (p ^ 1) g j) := by
    rw [teichBar_pow, teichBar_pow, heq]
  have h2 := teichBar_inj p hp h1
  exact zmodOrd_powers_distinct p hp hg i j hij hj h2

/-- **定理 (M104-5b): μ_{p−1} は巡回群** — ω̄(g)（g 原始根）の冪が
    μ_{p−1} の全ての元を枚挙する。被覆をレベル 1 に適用し、全射性の
    核心（M101-6: y = ω̄(y mod p)）で持ち上げる。**B-3 の最終形**。 -/
theorem mu_cyclic (p : Nat) (hp : IsPrime p) :
    ∃ x, IsMuRoot p x ∧ ∀ y, IsMuRoot p y →
      ∃ k, k ≤ p - 2 ∧ zpPow p x k = y := by
  obtain ⟨g, hg, hord⟩ := primitive_root_exists p hp
  refine ⟨teichBar p hp g, isMuRoot_teichBar p hp hg, ?_⟩
  intro y hy
  have hyu : IsZmodUnit p (y.val 1) := isZmodUnit_of_muRoot p hp hy
  obtain ⟨k, hk, hgk⟩ := generator_covers p hp hg hord (y.val 1) hyu
  refine ⟨k, hk, ?_⟩
  rw [← teichBar_pow, hgk]
  exact teichBar_of_muRoot p hp hy

end IUT
