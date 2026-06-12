/-
  IUT/PointValues.lean — M78F（点での具体値: 点の群キャンペーン並行部品）

  M77 の評価 zpEval の**具体値**を拡充する。witness 非依存性・
  スカラー倍・負元・単項式・c·X、そして頂点として
  **Lubin–Tate 多項式の点での値 f(x) = πx + x^p** を ℤ_p の等式
  として確立する（[π]-倍写像の実体。その反復の核 = 等分点 =
  分岐 LCFT の入力）。

  * M78F-1 `zpEval_witness_irrel` — 評価は可除性 witness e の取り方に
    依らない（成分は e に言及しない）
  * M78F-2 `psShift` / `ps_eq_X_mul_shift` — 定数項 0 の級数の
    X-因数分解 G = X·(shift G)（後段の閉性 G(x) ∈ pℤ_p の部品）
  * M78F-3 `zpEval_smul` — (c·F)(x) = c·F(x)
  * M78F-4 `zpEval_neg` — (−F)(x) = −F(x)（−a = (−1)·a 経由で
    M78F-3 に還元）
  * M78F-5 `proj_rpow_x_low` — x ∈ pℤ_p なら n ≤ m で
    proj_n(x^m) = 0（指数の分割 + p^n のレベル n 消滅）
  * M78F-6 `zpEval_mono` — (X^m)(x) = x^m（m < n は一点集中、
    n ≤ m は両辺消滅）
  * M78F-7 `zpEval_single_one` — (c·X)(x) = c·x
  * M78F-8 `zpEval_ltPoly` — **f(x) = πx + x^p**（M78F-6/7 +
    M77 の加法性で ltPoly の定義を成分分解）

  評価の乗法性・合成両立・点の群の群法則は並行開発中/次層。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.FormalGroupPoints

namespace IUT

/-! ## witness 非依存性 -/

/-- **M78F-1: 評価の witness 非依存性** — zpEval の成分
    `fun n => (zpEvalSeg p F x n).val n` は e に言及しないので、
    可除性 witness の取り替えで値は変わらない。 -/
theorem zpEval_witness_irrel (p : Nat) (F : PS (zpRing p))
    (x e e' : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    (hx' : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e') :
    zpEval p F x e hx = zpEval p F x e' hx' :=
  Subtype.ext rfl

/-! ## X-因数分解 -/

/-- **M78F-2a: 係数のシフト** (shift G)_n = G_{n+1}。 -/
def psShift (R : CRing) (G : PS R) : PS R := fun n => G (n + 1)

/-- **M78F-2b: 定数項 0 の級数の X-因数分解** G = X·(shift G)。 -/
theorem ps_eq_X_mul_shift (R : CRing) (G : PS R) (hG : G 0 = R.zero) :
    G = psMul R (psX R) (psShift R G) := by
  funext n
  cases n with
  | zero =>
    show G 0 = R.add R.zero (R.mul (psX R 0) (psShift R G (0 - 0)))
    rw [show psX R 0 = R.zero from rfl, R.zero_mul, R.zero_add]
    exact hG
  | succ m =>
    have hs : rsum R (fun k =>
          R.mul (psX R k) (psShift R G (m + 1 - k))) (m + 2)
        = R.mul (psX R 1) (psShift R G (m + 1 - 1)) :=
      rsum_single R (fun k =>
          R.mul (psX R k) (psShift R G (m + 1 - k))) 1 (m + 2) (by omega)
        (fun k _ hk => by
          show R.mul (psX R k) (psShift R G (m + 1 - k)) = R.zero
          rw [show psX R k = R.zero from if_neg hk]
          exact R.zero_mul _)
    show G (m + 1)
      = rsum R (fun k => R.mul (psX R k) (psShift R G (m + 1 - k))) (m + 2)
    rw [hs, show psX R 1 = R.one from rfl, R.one_mul]
    rfl

/-! ## スカラー倍と負元 -/

/-- **M78F-3: スカラー倍の評価** (c·F)(x) = c·F(x)。 -/
theorem zpEval_smul (p : Nat) (c : (Zp p).carrier) (F : PS (zpRing p))
    (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (psSmul (zpRing p) c F) x e hx
      = (zpRing p).mul c (zpEval p F x e hx) := by
  apply Subtype.ext
  funext n
  have hseg : zpEvalSeg p (psSmul (zpRing p) c F) x n
      = (zpRing p).mul c (zpEvalSeg p F x n) := by
    show rsum (zpRing p) (fun k =>
        (zpRing p).mul ((zpRing p).mul c (F k)) (rpow (zpRing p) x k)) n
      = (zpRing p).mul c (zpEvalSeg p F x n)
    have hc : rsum (zpRing p) (fun k =>
          (zpRing p).mul ((zpRing p).mul c (F k)) (rpow (zpRing p) x k)) n
        = rsum (zpRing p) (fun k =>
            (zpRing p).mul c
              ((zpRing p).mul (F k) (rpow (zpRing p) x k))) n :=
      rsum_congr (zpRing p) n (fun k _ =>
        (zpRing p).mul_assoc c (F k) (rpow (zpRing p) x k))
    rw [hc]
    exact (rsum_mul_left (zpRing p) (fun k =>
      (zpRing p).mul (F k) (rpow (zpRing p) x k)) c n).symm
  show (projRing p n).map (zpEvalSeg p (psSmul (zpRing p) c F) x n)
    = (zmodRing (p ^ n)).mul (c.val n)
        ((projRing p n).map (zpEvalSeg p F x n))
  rw [hseg]
  exact (projRing p n).map_mul _ _

/-- −a = (−1)·a（M42 の負元ツールキットの帰結）。 -/
theorem CRing.neg_eq_neg_one_mul (R : CRing) (a : R.carrier) :
    R.neg a = R.mul (R.neg R.one) a := by
  rw [CRing.neg_mul R R.one a, R.one_mul]

/-- **M78F-4: 負元の評価** (−F)(x) = −F(x)（−F = (−1)·F として
    M78F-3 に還元）。 -/
theorem zpEval_neg (p : Nat) (F : PS (zpRing p)) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (psNeg (zpRing p) F) x e hx
      = (zpRing p).neg (zpEval p F x e hx) := by
  have hps : psNeg (zpRing p) F
      = psSmul (zpRing p) ((zpRing p).neg (zpRing p).one) F := by
    funext k
    exact CRing.neg_eq_neg_one_mul (zpRing p) (F k)
  rw [hps, zpEval_smul]
  exact (CRing.neg_eq_neg_one_mul (zpRing p) (zpEval p F x e hx)).symm

/-! ## 高次冪の低レベル消滅 -/

/-- **M78F-5: x ∈ pℤ_p の冪の低レベル消滅** — n ≤ m なら
    レベル n で x^m = 0（x^m = p^n·(p^{m−n}·e^m) で p^n が殺す）。 -/
theorem proj_rpow_x_low (p : Nat) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    {n m : Nat} (h : n ≤ m) :
    (projRing p n).map (rpow (zpRing p) x m) = (zmodRing (p ^ n)).zero := by
  obtain ⟨d, hd⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  subst hd
  rw [hx, rpow_mul_dist (zpRing p) ((toZp p).map ((p : Nat) : Int)) e (n + d),
    rpow_add (zpRing p) ((toZp p).map ((p : Nat) : Int)) n d,
    (projRing p n).map_mul, (projRing p n).map_mul,
    proj_rpow_p_zero p n,
    CRing.zero_mul (zmodRing (p ^ n)), CRing.zero_mul (zmodRing (p ^ n))]

/-! ## 単項式の評価 -/

/-- **M78F-6: 単項式の評価** (X^m)(x) = x^m（m < n は k = m への
    一点集中、n ≤ m は部分和の全項消滅 + M78F-5 で両辺 0）。 -/
theorem zpEval_mono (p : Nat) (m : Nat) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (psMono (zpRing p) m) x e hx = rpow (zpRing p) x m := by
  apply Subtype.ext
  funext n
  show (zpEvalSeg p (psMono (zpRing p) m) x n).val n
    = (rpow (zpRing p) x m).val n
  cases Nat.lt_or_ge m n with
  | inl hmn =>
    have hseg : zpEvalSeg p (psMono (zpRing p) m) x n
        = rpow (zpRing p) x m := by
      have hs : rsum (zpRing p) (fun k =>
            (zpRing p).mul (psMono (zpRing p) m k) (rpow (zpRing p) x k)) n
          = (zpRing p).mul (psMono (zpRing p) m m) (rpow (zpRing p) x m) :=
        rsum_single (zpRing p) (fun k =>
            (zpRing p).mul (psMono (zpRing p) m k) (rpow (zpRing p) x k))
          m n hmn
          (fun k _ hk => by
            show (zpRing p).mul (psMono (zpRing p) m k)
                (rpow (zpRing p) x k) = (zpRing p).zero
            rw [show psMono (zpRing p) m k = (zpRing p).zero from if_neg hk]
            exact (zpRing p).zero_mul _)
      show rsum (zpRing p) (fun k =>
          (zpRing p).mul (psMono (zpRing p) m k) (rpow (zpRing p) x k)) n
        = rpow (zpRing p) x m
      rw [hs, show psMono (zpRing p) m m = (zpRing p).one from if_pos rfl,
        (zpRing p).one_mul]
    rw [hseg]
  | inr hnm =>
    have hseg : zpEvalSeg p (psMono (zpRing p) m) x n = (zpRing p).zero := by
      show rsum (zpRing p) (fun k =>
          (zpRing p).mul (psMono (zpRing p) m k) (rpow (zpRing p) x k)) n
        = (zpRing p).zero
      have hc : rsum (zpRing p) (fun k =>
            (zpRing p).mul (psMono (zpRing p) m k) (rpow (zpRing p) x k)) n
          = rsum (zpRing p) (fun _ => (zpRing p).zero) n :=
        rsum_congr (zpRing p) n (fun k hk => by
          show (zpRing p).mul (psMono (zpRing p) m k)
              (rpow (zpRing p) x k) = (zpRing p).zero
          rw [show psMono (zpRing p) m k = (zpRing p).zero from
            if_neg (by omega)]
          exact (zpRing p).zero_mul _)
      rw [hc]
      exact rsum_const_zero (zpRing p) n
    rw [hseg]
    exact (proj_rpow_x_low p x e hx hnm).symm

/-! ## c·X の評価 -/

/-- **M78F-7: 一次単項式の評価** (c·X)(x) = c·x（レベル 1 では
    部分和 0 と (c·x) の成分 0 が一致 — x ∈ pℤ_p が効く）。 -/
theorem zpEval_single_one (p : Nat) (hp : 2 ≤ p) (c : (Zp p).carrier)
    (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (psSingle (zpRing p) c 1) x e hx = (zpRing p).mul c x := by
  apply Subtype.ext
  funext n
  show (zpEvalSeg p (psSingle (zpRing p) c 1) x n).val n
    = ((zpRing p).mul c x).val n
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ m =>
    cases m with
    | zero =>
      have h1 : zpEvalSeg p (psSingle (zpRing p) c 1) x 1
          = (zpRing p).zero := by
        show (zpRing p).add (zpRing p).zero
            ((zpRing p).mul (psSingle (zpRing p) c 1 0) (rpow (zpRing p) x 0))
          = (zpRing p).zero
        rw [show psSingle (zpRing p) c 1 0 = (zpRing p).zero from rfl,
          (zpRing p).zero_mul, (zpRing p).zero_add]
      have hx1 : x.val 1 = Quot.mk (modCong (p ^ 1)).rel 0 :=
        (zp_dvd_p_iff p hp x).mp ⟨e, hx⟩
      rw [h1]
      show ((zpRing p).zero).val 1 = zmodMul (p ^ 1) (c.val 1) (x.val 1)
      rw [hx1]
      obtain ⟨a, ha⟩ := Quot.exists_rep (c.val 1)
      rw [← ha]
      show Quot.mk (modCong (p ^ 1)).rel 0
        = Quot.mk (modCong (p ^ 1)).rel (a * 0)
      apply Quot.sound
      show ((p ^ 1 : Nat) : Int) ∣ 0 - a * 0
      refine ⟨0, ?_⟩
      rw [Int.mul_zero, Int.mul_zero]
      omega
    | succ m' =>
      have hseg : zpEvalSeg p (psSingle (zpRing p) c 1) x (m' + 2)
          = (zpRing p).mul c x := by
        have hs : rsum (zpRing p) (fun k =>
              (zpRing p).mul (psSingle (zpRing p) c 1 k)
                (rpow (zpRing p) x k)) (m' + 2)
            = (zpRing p).mul (psSingle (zpRing p) c 1 1)
                (rpow (zpRing p) x 1) :=
          rsum_single (zpRing p) (fun k =>
              (zpRing p).mul (psSingle (zpRing p) c 1 k)
                (rpow (zpRing p) x k)) 1 (m' + 2) (by omega)
            (fun k _ hk => by
              show (zpRing p).mul (psSingle (zpRing p) c 1 k)
                  (rpow (zpRing p) x k) = (zpRing p).zero
              rw [show psSingle (zpRing p) c 1 k = (zpRing p).zero from
                if_neg hk]
              exact (zpRing p).zero_mul _)
        show rsum (zpRing p) (fun k =>
            (zpRing p).mul (psSingle (zpRing p) c 1 k)
              (rpow (zpRing p) x k)) (m' + 2)
          = (zpRing p).mul c x
        rw [hs, show psSingle (zpRing p) c 1 1 = c from if_pos rfl]
        show (zpRing p).mul c ((zpRing p).mul (rpow (zpRing p) x 0) x)
          = (zpRing p).mul c x
        rw [show rpow (zpRing p) x 0 = (zpRing p).one from rfl,
          (zpRing p).one_mul]
      rw [hseg]

/-! ## Lubin–Tate 多項式の点での値 -/

/-- **M78F-8（頂点）: f(x) = πx + x^p** — Lubin–Tate 多項式
    f = p·X + X^p の点 x ∈ pℤ_p での値の ℤ_p 等式。[π]-倍写像の
    実体であり、その反復の核（等分点）= 分岐 LCFT の入力。 -/
theorem zpEval_ltPoly (p : Nat) (hp : 2 ≤ p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltPoly p) x e hx
      = (zpRing p).add
          ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) x)
          (rpow (zpRing p) x p) := by
  show zpEval p (psAdd (zpRing p)
      (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1)
      (psMono (zpRing p) p)) x e hx = _
  rw [zpEval_add, zpEval_single_one p hp, zpEval_mono]

end IUT
