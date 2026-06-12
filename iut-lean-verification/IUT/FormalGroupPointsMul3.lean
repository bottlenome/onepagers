/-
  IUT/FormalGroupPointsMul3.lean — M84（3 変数評価の乗法性:
  点の群キャンペーン第八層・結合則輸送の第三段）

  3 変数評価の乗法性 (A·B)(x,y,z) = A(x,y,z)·B(x,y,z) を完全証明する。
  設計: M78 の「三角形 vs 矩形・はみ出しは冪が殺す」論法を
  **任意の可換環の抽象補題 nilpotent_cauchy_mul**（u^N 以上の冪が
  消えるなら打ち切り Cauchy 積 = 積の打ち切り）に昇格させ、
  レベル m+1 射影先 ℤ/p^{m+1} で z̄ に適用する。行方向（PS2 成分）は
  M83 の 2 変数乗法性が成分ごとに供給する——入れ子設計（M82）の続き。

  * M84-1 `zpEval2Seg_zero` / `zpEval2Seg_psAdd` / `zpEval2Seg_rsum` —
    2 変数部分和の加法性（PS2 環の有限和と交換）
  * M84-2 `nilpotent_cauchy_mul` — **抽象冪零 Cauchy 補題**
    （M78 の論法の抽象化、任意の可換環）
  * M84-3 `zpEval3_mul` — **乗法性（本丸）**: 行 = M83・列 = 抽象補題
  * M84-4 `zpEval3_one` / `zpEval3_pow` — 1 と冪の評価

  代入連鎖律・liftYZ/ps3X の評価・結合則の点輸送は次層（最終層）。
  全て選択公理不使用。
-/
import IUT.FormalGroupPointsMul2

namespace IUT

/-! ## 2 変数部分和の加法性 -/

/-- **M84-1a: 0 級数の 2 変数部分和** = 0。 -/
theorem zpEval2Seg_zero (p : Nat) (x y : (Zp p).carrier) (N : Nat) :
    zpEval2Seg p ((psRing (psRing (zpRing p))).zero) x y N
      = (zpRing p).zero := by
  show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
      (zpRing p).mul ((psRing (psRing (zpRing p))).zero b a)
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      N) N = (zpRing p).zero
  have hz : rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul ((psRing (psRing (zpRing p))).zero b a)
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        N) N
      = rsum (zpRing p) (fun _ => (zpRing p).zero) N :=
    rsum_congr (zpRing p) N (fun b _ => by
      have hz2 : rsum (zpRing p) (fun a =>
            (zpRing p).mul ((psRing (psRing (zpRing p))).zero b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b))) N
          = rsum (zpRing p) (fun _ => (zpRing p).zero) N :=
        rsum_congr (zpRing p) N (fun a _ => (zpRing p).zero_mul _)
      show rsum (zpRing p) (fun a =>
          (zpRing p).mul ((psRing (psRing (zpRing p))).zero b a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y b))) N = (zpRing p).zero
      rw [hz2]
      exact rsum_const_zero (zpRing p) N)
  rw [hz]
  exact rsum_const_zero (zpRing p) N

/-- **M84-1b: 2 変数部分和の加法性**。 -/
theorem zpEval2Seg_psAdd (p : Nat) (A B : PS2 (zpRing p))
    (x y : (Zp p).carrier) (N : Nat) :
    zpEval2Seg p (psAdd (psRing (zpRing p)) A B) x y N
      = (zpRing p).add (zpEval2Seg p A x y N) (zpEval2Seg p B x y N) := by
  show rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
      (zpRing p).mul ((zpRing p).add (A b a) (B b a))
        ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
      N) N = _
  have hc : ∀ b, b < N →
      rsum (zpRing p) (fun a =>
        (zpRing p).mul ((zpRing p).add (A b a) (B b a))
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        N
      = (zpRing p).add
          (rsum (zpRing p) (fun a => (zpRing p).mul (A b a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y b))) N)
          (rsum (zpRing p) (fun a => (zpRing p).mul (B b a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y b))) N) := by
    intro b _
    have h1 : rsum (zpRing p) (fun a =>
          (zpRing p).mul ((zpRing p).add (A b a) (B b a))
            ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
          N
        = rsum (zpRing p) (fun a => (zpRing p).add
            ((zpRing p).mul (A b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b)))
            ((zpRing p).mul (B b a)
              ((zpRing p).mul (rpow (zpRing p) x a)
                (rpow (zpRing p) y b)))) N :=
      rsum_congr (zpRing p) N (fun a _ =>
        (zpRing p).right_distrib (A b a) (B b a) _)
    rw [h1]
    exact rsum_add (zpRing p) _ _ N
  have h2 : rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul ((zpRing p).add (A b a) (B b a))
          ((zpRing p).mul (rpow (zpRing p) x a) (rpow (zpRing p) y b)))
        N) N
      = rsum (zpRing p) (fun b => (zpRing p).add
          (rsum (zpRing p) (fun a => (zpRing p).mul (A b a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y b))) N)
          (rsum (zpRing p) (fun a => (zpRing p).mul (B b a)
            ((zpRing p).mul (rpow (zpRing p) x a)
              (rpow (zpRing p) y b))) N)) N :=
    rsum_congr (zpRing p) N hc
  rw [h2]
  exact rsum_add (zpRing p) _ _ N

/-- **M84-1c: PS2 環の有限和との交換**。 -/
theorem zpEval2Seg_rsum (p : Nat) (v : Nat → PS2 (zpRing p))
    (x y : (Zp p).carrier) (N : Nat) :
    ∀ K, zpEval2Seg p (rsum (psRing (psRing (zpRing p))) v K) x y N
      = rsum (zpRing p) (fun k => zpEval2Seg p (v k) x y N) K := by
  intro K
  induction K with
  | zero => exact zpEval2Seg_zero p x y N
  | succ K ih =>
    show zpEval2Seg p (psAdd (psRing (zpRing p))
        (rsum (psRing (psRing (zpRing p))) v K) (v K)) x y N
      = (zpRing p).add
          (rsum (zpRing p) (fun k => zpEval2Seg p (v k) x y N) K)
          (zpEval2Seg p (v K) x y N)
    rw [zpEval2Seg_psAdd p (rsum (psRing (psRing (zpRing p))) v K) (v K)
        x y N, ih]

/-! ## 抽象冪零 Cauchy 補題 -/

/-- **定理 (M84-2): 冪零 Cauchy 補題**（M78 の三角形論法の抽象化） —
    u の N 乗以上が消えるとき、打ち切り Cauchy 積 = 打ち切り積。 -/
theorem nilpotent_cauchy_mul (S : CRing) (u : S.carrier)
    (f g : Nat → S.carrier) (N : Nat)
    (hu : ∀ k, N ≤ k → rpow S u k = S.zero) :
    rsum S (fun c => S.mul
      (rsum S (fun k => S.mul (f k) (g (c - k))) (c + 1))
      (rpow S u c)) N
    = S.mul (rsum S (fun c => S.mul (f c) (rpow S u c)) N)
        (rsum S (fun c => S.mul (g c) (rpow S u c)) N) := by
  cases N with
  | zero =>
    show S.zero = S.mul S.zero S.zero
    exact (CRing.zero_mul S S.zero).symm
  | succ m =>
    have hA : rsum S (fun c => S.mul
          (rsum S (fun k => S.mul (f k) (g (c - k))) (c + 1))
          (rpow S u c)) (m + 1)
        = rsum S (fun c => rsum S (fun k =>
            S.mul (S.mul (f k) (g (c - k))) (rpow S u c)) (c + 1))
            (m + 1) :=
      rsum_congr S (m + 1) (fun c _ =>
        rsum_mul_right S (fun k => S.mul (f k) (g (c - k)))
          (rpow S u c) (c + 1))
    have hB : rsum S (fun c => rsum S (fun k =>
          S.mul (S.mul (f k) (g (c - k))) (rpow S u c)) (c + 1)) (m + 1)
        = rsum S (fun j => rsum S (fun l =>
            S.mul (S.mul (f j) (g l)) (rpow S u (j + l))) (m + 1 - j))
            (m + 1) :=
      (rsum_congr S (m + 1) (fun c _ =>
        rsum_congr S (c + 1) (fun k hk => by
          rw [show k + (c - k) = c by omega]))).symm.trans
        (rsum_triangle S (fun j l =>
          S.mul (S.mul (f j) (g l)) (rpow S u (j + l))) m)
    have hC : S.mul (rsum S (fun c => S.mul (f c) (rpow S u c)) (m + 1))
        (rsum S (fun c => S.mul (g c) (rpow S u c)) (m + 1))
        = rsum S (fun j => rsum S (fun l =>
            S.mul (S.mul (f j) (g l)) (rpow S u (j + l))) (m + 1))
            (m + 1) := by
      rw [rsum_mul_right S (fun j => S.mul (f j) (rpow S u j))
          (rsum S (fun c => S.mul (g c) (rpow S u c)) (m + 1)) (m + 1)]
      refine rsum_congr S (m + 1) (fun j _ => ?_)
      show S.mul (S.mul (f j) (rpow S u j))
          (rsum S (fun l => S.mul (g l) (rpow S u l)) (m + 1)) = _
      rw [rsum_mul_left S (fun l => S.mul (g l) (rpow S u l))
          (S.mul (f j) (rpow S u j)) (m + 1)]
      refine rsum_congr S (m + 1) (fun l _ => ?_)
      show S.mul (S.mul (f j) (rpow S u j)) (S.mul (g l) (rpow S u l))
        = S.mul (S.mul (f j) (g l)) (rpow S u (j + l))
      rw [rpow_add S u j l]
      exact CRing.mul_mul_comm S (f j) (rpow S u j) (g l) (rpow S u l)
    -- 矩形 = 三角形 + u^{m+1}·(はみ出し)
    have hj : ∀ j, j < m + 1 →
        rsum S (fun l => S.mul (S.mul (f j) (g l)) (rpow S u (j + l)))
          (m + 1)
        = S.add
            (rsum S (fun l =>
              S.mul (S.mul (f j) (g l)) (rpow S u (j + l))) (m + 1 - j))
            (S.mul (rpow S u (m + 1))
              (rsum S (fun k =>
                S.mul (S.mul (f j) (g (m + 1 - j + k))) (rpow S u k))
                j)) := by
      intro j hjlt
      have hsplit := rsum_split S (fun l =>
        S.mul (S.mul (f j) (g l)) (rpow S u (j + l))) (m + 1 - j) j
      rw [show m + 1 - j + j = m + 1 by omega] at hsplit
      rw [hsplit]
      have htailterm : ∀ k, k < j →
          S.mul (S.mul (f j) (g (m + 1 - j + k)))
            (rpow S u (j + (m + 1 - j + k)))
          = S.mul (rpow S u (m + 1))
              (S.mul (S.mul (f j) (g (m + 1 - j + k))) (rpow S u k)) := by
        intro k _
        rw [show j + (m + 1 - j + k) = (m + 1) + k by omega,
          rpow_add S u (m + 1) k]
        exact CRing.mul_left_comm S (S.mul (f j) (g (m + 1 - j + k)))
          (rpow S u (m + 1)) (rpow S u k)
      have htail : rsum S (fun k =>
            S.mul (S.mul (f j) (g (m + 1 - j + k)))
              (rpow S u (j + (m + 1 - j + k)))) j
          = S.mul (rpow S u (m + 1))
              (rsum S (fun k =>
                S.mul (S.mul (f j) (g (m + 1 - j + k))) (rpow S u k))
                j) :=
        (rsum_congr S j htailterm).trans
          ((rsum_mul_left S (fun k =>
              S.mul (S.mul (f j) (g (m + 1 - j + k))) (rpow S u k))
            (rpow S u (m + 1)) j).symm)
      rw [htail]
    have hcongr : rsum S (fun j => rsum S (fun l =>
          S.mul (S.mul (f j) (g l)) (rpow S u (j + l))) (m + 1)) (m + 1)
        = rsum S (fun j => S.add
            (rsum S (fun l =>
              S.mul (S.mul (f j) (g l)) (rpow S u (j + l))) (m + 1 - j))
            (S.mul (rpow S u (m + 1))
              (rsum S (fun k =>
                S.mul (S.mul (f j) (g (m + 1 - j + k))) (rpow S u k))
                j))) (m + 1) :=
      rsum_congr S (m + 1) hj
    have hE : rsum S (fun j => rsum S (fun l =>
          S.mul (S.mul (f j) (g l)) (rpow S u (j + l))) (m + 1)) (m + 1)
        = S.add
            (rsum S (fun j => rsum S (fun l =>
              S.mul (S.mul (f j) (g l)) (rpow S u (j + l))) (m + 1 - j))
              (m + 1))
            (S.mul (rpow S u (m + 1))
              (rsum S (fun j => rsum S (fun k =>
                S.mul (S.mul (f j) (g (m + 1 - j + k))) (rpow S u k)) j)
                (m + 1))) := by
      rw [hcongr,
        rsum_add S (fun j => rsum S (fun l =>
          S.mul (S.mul (f j) (g l)) (rpow S u (j + l))) (m + 1 - j))
          (fun j => S.mul (rpow S u (m + 1))
            (rsum S (fun k =>
              S.mul (S.mul (f j) (g (m + 1 - j + k))) (rpow S u k)) j))
          (m + 1),
        rsum_mul_left S (fun j => rsum S (fun k =>
          S.mul (S.mul (f j) (g (m + 1 - j + k))) (rpow S u k)) j)
          (rpow S u (m + 1)) (m + 1)]
    rw [hA, hB, hC, hE, hu (m + 1) (Nat.le_refl (m + 1)),
      CRing.zero_mul S, CRing.add_zero S]

/-! ## 3 変数の乗法性 -/

/-- **定理 (M84-3): 3 変数評価の乗法性（本丸）** —
    (A·B)(x,y,z) = A(x,y,z)·B(x,y,z)。行方向は M83、列方向は
    冪零 Cauchy 補題（u := z̄ in ℤ/p^{m+1}）。 -/
theorem zpEval3_mul (p : Nat) (A B : PS3 (zpRing p))
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez) :
    zpEval3 p (psMul (psRing (psRing (zpRing p))) A B)
      x ex y ey z ez hx hy hz
      = (zpRing p).mul (zpEval3 p A x ex y ey z ez hx hy hz)
          (zpEval3 p B x ex y ey z ez hx hy hz) := by
  apply Subtype.ext
  funext n
  show (zpEval3Seg p (psMul (psRing (psRing (zpRing p))) A B)
      x y z n).val n
    = ((zpRing p).mul (zpEval3Seg p A x y z n)
        (zpEval3Seg p B x y z n)).val n
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ m =>
    -- 左辺: 行を M83 で分解して冪零 Cauchy 形へ
    have hL : (projRing p (m + 1)).map
        (zpEval3Seg p (psMul (psRing (psRing (zpRing p))) A B)
          x y z (m + 1))
        = rsum (zmodRing (p ^ (m + 1))) (fun c =>
            (zmodRing (p ^ (m + 1))).mul
              (rsum (zmodRing (p ^ (m + 1))) (fun k =>
                (zmodRing (p ^ (m + 1))).mul
                  ((projRing p (m + 1)).map
                    (zpEval2Seg p (A k) x y (m + 1)))
                  ((projRing p (m + 1)).map
                    (zpEval2Seg p (B (c - k)) x y (m + 1)))) (c + 1))
              (rpow (zmodRing (p ^ (m + 1)))
                ((projRing p (m + 1)).map z) c)) (m + 1) := by
      show (projRing p (m + 1)).map (rsum (zpRing p) (fun c =>
          (zpRing p).mul
            (zpEval2Seg p ((psMul (psRing (psRing (zpRing p))) A B) c)
              x y (m + 1))
            (rpow (zpRing p) z c)) (m + 1)) = _
      rw [ringHom_rsum (projRing p (m + 1)) _ (m + 1)]
      refine rsum_congr (zmodRing (p ^ (m + 1))) (m + 1) (fun c _ => ?_)
      show (projRing p (m + 1)).map ((zpRing p).mul
          (zpEval2Seg p ((psMul (psRing (psRing (zpRing p))) A B) c)
            x y (m + 1))
          (rpow (zpRing p) z c)) = _
      rw [(projRing p (m + 1)).map_mul,
        ringHom_rpow (projRing p (m + 1)) z c,
        show zpEval2Seg p ((psMul (psRing (psRing (zpRing p))) A B) c)
            x y (m + 1)
          = zpEval2Seg p (rsum (psRing (psRing (zpRing p))) (fun k =>
              (psRing (psRing (zpRing p))).mul (A k) (B (c - k)))
              (c + 1)) x y (m + 1) from rfl,
        zpEval2Seg_rsum p (fun k =>
          (psRing (psRing (zpRing p))).mul (A k) (B (c - k))) x y
          (m + 1) (c + 1),
        ringHom_rsum (projRing p (m + 1)) _ (c + 1)]
      refine congrArg (fun w => (zmodRing (p ^ (m + 1))).mul w
        (rpow (zmodRing (p ^ (m + 1)))
          ((projRing p (m + 1)).map z) c)) ?_
      refine rsum_congr (zmodRing (p ^ (m + 1))) (c + 1) (fun k _ => ?_)
      have hmulk : (zpEval2Seg p ((psRing (psRing (zpRing p))).mul
            (A k) (B (c - k))) x y (m + 1)).val (m + 1)
          = (((zpRing p).mul (zpEval2Seg p (A k) x y (m + 1))
              (zpEval2Seg p (B (c - k)) x y (m + 1)))).val (m + 1) :=
        congrFun (congrArg Subtype.val
          (zpEval2_mul p (A k) (B (c - k)) x ex y ey hx hy)) (m + 1)
      show (projRing p (m + 1)).map
          (zpEval2Seg p ((psRing (psRing (zpRing p))).mul (A k)
            (B (c - k))) x y (m + 1)) = _
      rw [show (projRing p (m + 1)).map
          (zpEval2Seg p ((psRing (psRing (zpRing p))).mul (A k)
            (B (c - k))) x y (m + 1))
          = (projRing p (m + 1)).map
              ((zpRing p).mul (zpEval2Seg p (A k) x y (m + 1))
                (zpEval2Seg p (B (c - k)) x y (m + 1))) from hmulk,
        (projRing p (m + 1)).map_mul]
    -- 右辺: 射影して冪零 Cauchy 補題の積形へ
    have hR : (projRing p (m + 1)).map
        ((zpRing p).mul (zpEval3Seg p A x y z (m + 1))
          (zpEval3Seg p B x y z (m + 1)))
        = (zmodRing (p ^ (m + 1))).mul
            (rsum (zmodRing (p ^ (m + 1))) (fun c =>
              (zmodRing (p ^ (m + 1))).mul
                ((projRing p (m + 1)).map
                  (zpEval2Seg p (A c) x y (m + 1)))
                (rpow (zmodRing (p ^ (m + 1)))
                  ((projRing p (m + 1)).map z) c)) (m + 1))
            (rsum (zmodRing (p ^ (m + 1))) (fun c =>
              (zmodRing (p ^ (m + 1))).mul
                ((projRing p (m + 1)).map
                  (zpEval2Seg p (B c) x y (m + 1)))
                (rpow (zmodRing (p ^ (m + 1)))
                  ((projRing p (m + 1)).map z) c)) (m + 1)) := by
      rw [(projRing p (m + 1)).map_mul]
      show (zmodRing (p ^ (m + 1))).mul
          ((projRing p (m + 1)).map (rsum (zpRing p) (fun c =>
            (zpRing p).mul (zpEval2Seg p (A c) x y (m + 1))
              (rpow (zpRing p) z c)) (m + 1)))
          ((projRing p (m + 1)).map (rsum (zpRing p) (fun c =>
            (zpRing p).mul (zpEval2Seg p (B c) x y (m + 1))
              (rpow (zpRing p) z c)) (m + 1))) = _
      rw [ringHom_rsum (projRing p (m + 1)) _ (m + 1),
        ringHom_rsum (projRing p (m + 1)) _ (m + 1)]
      have hone : ∀ W : PS3 (zpRing p),
          rsum (zmodRing (p ^ (m + 1))) (fun c =>
            (projRing p (m + 1)).map ((zpRing p).mul
              (zpEval2Seg p (W c) x y (m + 1)) (rpow (zpRing p) z c)))
            (m + 1)
          = rsum (zmodRing (p ^ (m + 1))) (fun c =>
              (zmodRing (p ^ (m + 1))).mul
                ((projRing p (m + 1)).map
                  (zpEval2Seg p (W c) x y (m + 1)))
                (rpow (zmodRing (p ^ (m + 1)))
                  ((projRing p (m + 1)).map z) c)) (m + 1) :=
        fun W => rsum_congr (zmodRing (p ^ (m + 1))) (m + 1)
          (fun c _ => by
            show (projRing p (m + 1)).map ((zpRing p).mul
                (zpEval2Seg p (W c) x y (m + 1))
                (rpow (zpRing p) z c)) = _
            rw [(projRing p (m + 1)).map_mul,
              ringHom_rpow (projRing p (m + 1)) z c])
      rw [hone A, hone B]
    show (projRing p (m + 1)).map
        (zpEval3Seg p (psMul (psRing (psRing (zpRing p))) A B)
          x y z (m + 1))
      = (projRing p (m + 1)).map
          ((zpRing p).mul (zpEval3Seg p A x y z (m + 1))
            (zpEval3Seg p B x y z (m + 1)))
    rw [hL, hR]
    exact nilpotent_cauchy_mul (zmodRing (p ^ (m + 1)))
      ((projRing p (m + 1)).map z)
      (fun k => (projRing p (m + 1)).map
        (zpEval2Seg p (A k) x y (m + 1)))
      (fun k => (projRing p (m + 1)).map
        (zpEval2Seg p (B k) x y (m + 1)))
      (m + 1)
      (fun k hk => proj_rpow_point_low p z ez hz hk)

/-! ## 1 と冪の評価 -/

/-- **M84-4a: 1 の評価** — 1(x,y,z) = 1（c = 0 集中 + M82 の 2 変数
    1 部分和）。 -/
theorem zpEval3_one (p : Nat) (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez) :
    zpEval3 p ((psRing (psRing (psRing (zpRing p)))).one)
      x ex y ey z ez hx hy hz = (zpRing p).one := by
  apply Subtype.ext
  funext n
  show (zpEval3Seg p (psOne (psRing (psRing (zpRing p)))) x y z n).val n
    = ((zpRing p).one).val n
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ m =>
    have hseg : zpEval3Seg p (psOne (psRing (psRing (zpRing p))))
        x y z (m + 1) = (zpRing p).one := by
      show rsum (zpRing p) (fun c => (zpRing p).mul
          (zpEval2Seg p (psOne (psRing (psRing (zpRing p))) c)
            x y (m + 1))
          (rpow (zpRing p) z c)) (m + 1) = (zpRing p).one
      have hs : rsum (zpRing p) (fun c => (zpRing p).mul
            (zpEval2Seg p (psOne (psRing (psRing (zpRing p))) c)
              x y (m + 1))
            (rpow (zpRing p) z c)) (m + 1)
          = (zpRing p).mul
              (zpEval2Seg p (psOne (psRing (psRing (zpRing p))) 0)
                x y (m + 1))
              (rpow (zpRing p) z 0) :=
        rsum_single (zpRing p) (fun c => (zpRing p).mul
            (zpEval2Seg p (psOne (psRing (psRing (zpRing p))) c)
              x y (m + 1))
            (rpow (zpRing p) z c)) 0 (m + 1) (by omega)
          (fun c _ hc => by
            show (zpRing p).mul
                (zpEval2Seg p (psOne (psRing (psRing (zpRing p))) c)
                  x y (m + 1))
                (rpow (zpRing p) z c) = (zpRing p).zero
            rw [show psOne (psRing (psRing (zpRing p))) c
                = (psRing (psRing (zpRing p))).zero from if_neg hc,
              zpEval2Seg_zero p x y (m + 1)]
            exact (zpRing p).zero_mul _)
      rw [hs,
        show zpEval2Seg p (psOne (psRing (psRing (zpRing p))) 0)
            x y (m + 1) = (zpRing p).one from zpEval2Seg_one p x y m]
      show (zpRing p).mul ((zpRing p).one) ((zpRing p).one)
        = (zpRing p).one
      exact (zpRing p).one_mul _
    rw [hseg]

/-- **M84-4b: 冪の評価** — (G^k)(x,y,z) = G(x,y,z)^k。 -/
theorem zpEval3_pow (p : Nat) (G : PS3 (zpRing p))
    (x ex y ey z ez : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ex)
    (hy : y = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ey)
    (hz : z = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) ez) :
    ∀ k, zpEval3 p (psPow (psRing (psRing (zpRing p))) G k)
        x ex y ey z ez hx hy hz
      = rpow (zpRing p) (zpEval3 p G x ex y ey z ez hx hy hz) k := by
  intro k
  induction k with
  | zero => exact zpEval3_one p x ex y ey z ez hx hy hz
  | succ k ih =>
    show zpEval3 p (psMul (psRing (psRing (zpRing p)))
        (psPow (psRing (psRing (zpRing p))) G k) G)
        x ex y ey z ez hx hy hz
      = (zpRing p).mul
          (rpow (zpRing p) (zpEval3 p G x ex y ey z ez hx hy hz) k)
          (zpEval3 p G x ex y ey z ez hx hy hz)
    rw [zpEval3_mul p (psPow (psRing (psRing (zpRing p))) G k) G
        x ex y ey z ez hx hy hz, ih]

end IUT
