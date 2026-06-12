/-
  IUT/FrobeniusGen.lean — M54（一般化 Frobenius 定理: F^p = (Frob F)∘X^p）

  M47 の Frobenius 定理 F^p = F∘X^p は係数環 ℤ/p に特化していた
  （係数 FLT c^p = c で係数側の Frobenius が消える）。二変数版
  （形式群第五層）では係数環が S = (ℤ/p)[[X]] になり、係数側の
  Frobenius c ↦ c^p が**消えずに残る**ため、一般化が必要になる:

    標数 p の任意の可換環 S（rofNat S p = 0）で
      F^p = (psMap (frobHom S) F) ∘ X^p
    （frobHom : c ↦ c^p は環準同型 — 正確な新入生の夢が map_add）

  証明は M47 と同じ truncation 帰納で、単項式の冪 (c·X^N)^p =
  c^p·X^{Np} の係数 c^p を FLT で c に戻す代わりに frobHom の像として
  そのまま運ぶ。ℤ/p では frobHom = 恒等（FLT）なので M47 を回復する
  （サニティアンカー `frobenius_gen_recovers`）。

  * M54-1 `rpow_one_base` / `freshman_exact_ring` — 1^k = 1 と
    **標数 p の環レベル正確な新入生の夢** (x+y)^p = x^p + y^p
  * M54-2 `frobHom` — **Frobenius 環準同型** c ↦ c^p（map_add =
    新入生の夢・map_mul = 冪の積分配・map_one = 1^p = 1）
  * M54-3 `freshman_exact_gen` / `psMap_trunc` — 級数レベルの正確な
    新入生の夢（標数 p の任意の環）と psMap の打ち切り交換
  * M54-4 `frobenius_trunc_gen` / `frobenius_charp_gen` —
    **一般化 Frobenius 定理** F^p = (Frob F)∘X^p（truncation 帰納）
  * M54-5 `frobHom_zmod_id` / `frobenius_gen_recovers` — ℤ/p では
    frobHom = 恒等で M47 の F^p = F∘X^p を回復（整合性アンカー）
  * M54-6 `psRing_char` — **標数 p は冪級数環に遺伝**（二変数版で
    S = (ℤ/p)[[X]] に適用するための入口）

  ロードマップ: 次層（M55）で外側変数（Y）に本定理・内側変数（X）に
  M47 を適用し、二変数 Frobenius G^p = G(X^p, Y^p) を組み上げる。
  全て選択公理不使用。
-/
import IUT.FormalGroupMap

namespace IUT

/-! ## 標数 p の環レベルの道具 -/

/-- **M54-1a: 1^k = 1**。 -/
theorem rpow_one_base (R : CRing) : ∀ k, rpow R R.one k = R.one := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show R.mul (rpow R R.one k) R.one = R.one
    rw [CRing.mul_one R _, ih]

/-- **定理 (M54-1b): 標数 p の正確な新入生の夢（環レベル）** —
    rofNat R p = 0 なら (x+y)^p = x^p + y^p（M45 の p·C 項が消滅）。 -/
theorem freshman_exact_ring (R : CRing) (p : Nat) (hp : IsPrime p)
    (hchar : rofNat R p = R.zero) (x y : R.carrier) :
    rpow R (R.add x y) p = R.add (rpow R x p) (rpow R y p) := by
  obtain ⟨c, hc⟩ := freshman_ring R p hp x y
  rw [hc, hchar, CRing.zero_mul R c]
  exact CRing.add_zero R _

/-- **M54-2: Frobenius 環準同型** c ↦ c^p（標数 p の環）。 -/
def frobHom (R : CRing) (p : Nat) (hp : IsPrime p)
    (hchar : rofNat R p = R.zero) : RingHom R R where
  map := fun c => rpow R c p
  map_add := freshman_exact_ring R p hp hchar
  map_mul := fun a b => rpow_mul_dist R a b p
  map_one := rpow_one_base R p

/-! ## 級数レベルの道具 -/

/-- **定理 (M54-3a): 級数レベルの正確な新入生の夢（標数 p の任意の環）**
    — M47 の freshman_exact から ℤ/p 特化を外した形。 -/
theorem freshman_exact_gen (R : CRing) (p : Nat) (hp : IsPrime p)
    (hchar : rofNat R p = R.zero) (A B : PS R) :
    psPow R (psAdd R A B) p
      = (psRing R).add (psPow R A p) (psPow R B p) := by
  obtain ⟨C, hC⟩ := freshman_ps R p hp A B
  rw [hC, rofNat_ps_eq_psC R p, hchar, psC_zero,
    show (psRing R).mul (psZero R) C = (psRing R).zero from
      CRing.zero_mul (psRing R) C]
  exact CRing.add_zero (psRing R) _

/-- **M54-3b: psMap は打ち切りと交換**。 -/
theorem psMap_trunc {R S : CRing} (φ : RingHom R S) (F : PS R) (N : Nat) :
    psMap φ (psTrunc R F N) = psTrunc S (psMap φ F) N := by
  funext n
  show φ.map (if n < N then F n else R.zero)
      = (if n < N then φ.map (F n) else S.zero)
  cases Nat.decLt n N with
  | isTrue h => rw [if_pos h, if_pos h]
  | isFalse h =>
    rw [if_neg h, if_neg h]
    exact φ.map_zero

/-! ## 一般化 Frobenius 定理 -/

/-- **M54-4a: 打ち切りの一般化 Frobenius** —
    (trunc F N)^p = (trunc (Frob F) N)∘X^p（truncation 帰納）。 -/
theorem frobenius_trunc_gen (R : CRing) (p : Nat) (hp : IsPrime p)
    (hchar : rofNat R p = R.zero) (F : PS R) : ∀ N,
    psPow R (psTrunc R F N) p
      = psComp R (psTrunc R (psMap (frobHom R p hp hchar) F) N)
          (psMono R p) := by
  intro N
  induction N with
  | zero =>
    rw [psTrunc_zero, psTrunc_zero, psComp_zero_left]
    obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.1; omega⟩
    rw [hm]
    exact psPow_zero_base _ m
  | succ N ih =>
    rw [psTrunc_succ R F N,
      freshman_exact_gen R p hp hchar (psTrunc R F N)
        (psSingle R (F N) N),
      ih, psSingle_pow R (F N) N p,
      psTrunc_succ R (psMap (frobHom R p hp hchar) F) N]
    have hca : psComp R (psAdd R
          (psTrunc R (psMap (frobHom R p hp hchar) F) N)
          (psSingle R ((psMap (frobHom R p hp hchar) F) N) N))
          (psMono R p)
        = (psRing R).add
            (psComp R (psTrunc R (psMap (frobHom R p hp hchar) F) N)
              (psMono R p))
            (psComp R (psSingle R ((psMap (frobHom R p hp hchar) F) N) N)
              (psMono R p)) :=
      psComp_add R _ _ _
    rw [hca,
      psComp_single R ((psMap (frobHom R p hp hchar) F) N) N p
        (by have := hp.1; omega),
      show N * p = p * N from Nat.mul_comm N p]
    rfl

/-- **定理 (M54-4b): 一般化 Frobenius 定理（標数 p）** —
    F^p = (Frob F)∘X^p。係数 n は trunc (n+1) に一致させて
    打ち切り版に帰着（M41 psPow_congr + 合成の左係数依存性）。 -/
theorem frobenius_charp_gen (R : CRing) (p : Nat) (hp : IsPrime p)
    (hchar : rofNat R p = R.zero) (F : PS R) :
    psPow R F p
      = psComp R (psMap (frobHom R p hp hchar) F) (psMono R p) := by
  funext n
  have h1 : psPow R F p n = psPow R (psTrunc R F (n + 1)) p n :=
    psPow_congr R F (psTrunc R F (n + 1)) n
      (fun i hi => (psTrunc_agree R F (n + 1) (by omega)).symm)
      p n (Nat.le_refl n)
  have h2 : psComp R (psMap (frobHom R p hp hchar) F) (psMono R p) n
      = psComp R (psTrunc R (psMap (frobHom R p hp hchar) F) (n + 1))
          (psMono R p) n :=
    psComp_congr_left R (psMono R p) n
      (fun k hk =>
        (psTrunc_agree R (psMap (frobHom R p hp hchar) F) (n + 1)
          (by omega)).symm)
  rw [h1, h2]
  exact congrFun (frobenius_trunc_gen R p hp hchar F (n + 1)) n

/-! ## 整合性アンカーと遺伝 -/

/-- **M54-5a: ℤ/p では Frobenius 準同型は恒等**（係数 FLT）。 -/
theorem frobHom_zmod_id (p : Nat) (hp : IsPrime p)
    (F : PS (zmodRing (p ^ 1))) :
    psMap (frobHom (zmodRing (p ^ 1)) p hp (zmod_char p)) F = F := by
  funext n
  exact zmod_flt p hp (F n)

/-- **定理 (M54-5b): M47 の回復（整合性アンカー）** — ℤ/p では
    一般化 Frobenius 定理が F^p = F∘X^p に退化する。 -/
theorem frobenius_gen_recovers (p : Nat) (hp : IsPrime p)
    (F : PS (zmodRing (p ^ 1))) :
    psPow (zmodRing (p ^ 1)) F p
      = psComp (zmodRing (p ^ 1)) F (psMono (zmodRing (p ^ 1)) p) := by
  have h := frobenius_charp_gen (zmodRing (p ^ 1)) p hp (zmod_char p) F
  rw [frobHom_zmod_id p hp F] at h
  exact h

/-- **定理 (M54-6): 標数 p は冪級数環に遺伝** — rofNat R p = 0 なら
    rofNat R[[X]] p = 0（二変数版で S = (ℤ/p)[[X]] に M54-4 を適用する
    ための入口）。 -/
theorem psRing_char (R : CRing) (p : Nat) (hchar : rofNat R p = R.zero) :
    rofNat (psRing R) p = (psRing R).zero := by
  rw [rofNat_ps_eq_psC R p, hchar]
  exact psC_zero R

end IUT
