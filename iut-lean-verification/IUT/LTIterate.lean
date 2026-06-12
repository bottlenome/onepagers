/-
  IUT/LTIterate.lean — M72F（逆元キャンペーンのサブエージェント並行部品:
  合成の乗法性パッケージと Lubin–Tate 多項式の反復）

  1 変数合成 P ↦ P∘Q を「打ち切り環準同型」として完成させ
  （加法性・単位元保存は M40 で済み、ここで乗法性・冪・結合則を追加）、
  その応用として LT 多項式 f = pX + X^p の反復 f^{∘n}（[p^n] 系列）を
  構成する。p^n 等分点（分岐つき局所類体論 LCFT への入口）に向けた
  第一歩。

  * M72F-1 `CRing.mul_mul_mul_comm` — 乗法簿記 (a·b)·(c·d) = (a·c)·(b·d)
  * M72F-2 `psComp_mul` — **合成の乗法性** (P₁·P₂)∘Q = (P₁∘Q)·(P₂∘Q)
    （Q(0) = 0。M69b の 2 変数版 ps23Comp_mul の 1 変数の影:
    左辺は psPow_add で冪を分解 + 三角和交換 + psPowPow_low padding、
    右辺は Cauchy 積を rsum_mul_left/right で展開して添字交換）
  * M72F-3 `psComp_pow` — 冪の合成 (P^m)∘Q = (P∘Q)^m（m 帰納）
  * M72F-4 `psComp_assoc` — **1 変数連鎖律** (P∘Q)∘W = P∘(Q∘W)
    （Q(0) = W(0) = 0。両辺を共通形 Σ_k P_k·Σ_m (Q^k)_m (W^m)_n に帰着）
  * M72F-5 `ltIter` / `ltIter_coeff_zero` / `ltIter_coeff_one` /
    `ltIter_comm` — **f^{∘n} の構成**と定数項 0・一次係数 π^n・
    可換性 f^{∘n}∘f = f∘f^{∘n}
  * M72F-6 `psComp_single_one` / `psComp_mono` / `psComp_ltPoly_left` —
    **f∘G = π·G + G^p**（G(0) = 0。f の係数は k = 1, p のみ生存）
  * M72F-7 `ltIter_eq_ltSol` — **f^{∘n} = [π^n] 系列**: ltIter p n は
    M49 の Lubin–Tate 補題の一意解 ltSol p hp (π^n) に一致

  全て選択公理不使用。
-/
import IUT.FormalGroupEval

namespace IUT

/-! ## 乗法簿記 -/

/-- **M72F-1: 乗法簿記** (a·b)·(c·d) = (a·c)·(b·d)。 -/
theorem CRing.mul_mul_mul_comm (R : CRing) (a b c d : R.carrier) :
    R.mul (R.mul a b) (R.mul c d) = R.mul (R.mul a c) (R.mul b d) := by
  rw [R.mul_assoc a b (R.mul c d), ← R.mul_assoc b c d, R.mul_comm b c,
    R.mul_assoc c b d, ← R.mul_assoc a c (R.mul b d)]

/-! ## 合成の乗法性 -/

/-- **定理 (M72F-2): 合成の乗法性** — (P₁·P₂)∘Q = (P₁∘Q)·(P₂∘Q)
    （Q(0) = 0）。係数 n で両辺を共通形
    Σ_{a≤n} Σ_{b≤n} (P₁_a·P₂_b)·(Q^a·Q^b)_n に帰着する。 -/
theorem psComp_mul (R : CRing) (P₁ P₂ Q : PS R) (hQ : Q 0 = R.zero) :
    psComp R (psMul R P₁ P₂) Q
      = psMul R (psComp R P₁ Q) (psComp R P₂ Q) := by
  funext n
  -- 左辺 → 共通形
  have hLHS : psComp R (psMul R P₁ P₂) Q n
      = rsum R (fun a => rsum R (fun b =>
          R.mul (R.mul (P₁ a) (P₂ b))
            (psMul R (psPow R Q a) (psPow R Q b) n)) (n + 1)) (n + 1) := by
    show rsum R (fun k => R.mul (psMul R P₁ P₂ k) (psPow R Q k n)) (n + 1) = _
    -- Cauchy 係数を配り、冪を psPow_add で分解
    have h1 : rsum R (fun k => R.mul (psMul R P₁ P₂ k) (psPow R Q k n)) (n + 1)
        = rsum R (fun k => rsum R (fun l =>
            R.mul (R.mul (P₁ l) (P₂ (k - l)))
              (psMul R (psPow R Q l) (psPow R Q (k - l)) n)) (k + 1)) (n + 1) :=
      rsum_congr R (n + 1) (fun k _ => by
        show R.mul (rsum R (fun l => R.mul (P₁ l) (P₂ (k - l))) (k + 1))
            (psPow R Q k n)
          = rsum R (fun l =>
              R.mul (R.mul (P₁ l) (P₂ (k - l)))
                (psMul R (psPow R Q l) (psPow R Q (k - l)) n)) (k + 1)
        rw [rsum_mul_right R (fun l => R.mul (P₁ l) (P₂ (k - l)))
          (psPow R Q k n) (k + 1)]
        exact rsum_congr R (k + 1) (fun l hl => by
          have hsplit : psPow R Q k
              = psMul R (psPow R Q l) (psPow R Q (k - l)) := by
            have h := psPow_add R Q l (k - l)
            rw [show l + (k - l) = k by omega] at h
            exact h
          rw [hsplit]))
    -- 三角和の矩形化
    have h2 : rsum R (fun k => rsum R (fun l =>
          R.mul (R.mul (P₁ l) (P₂ (k - l)))
            (psMul R (psPow R Q l) (psPow R Q (k - l)) n)) (k + 1)) (n + 1)
        = rsum R (fun a => rsum R (fun b =>
            R.mul (R.mul (P₁ a) (P₂ b))
              (psMul R (psPow R Q a) (psPow R Q b) n)) (n + 1 - a)) (n + 1) :=
      rsum_triangle R (fun a b =>
        R.mul (R.mul (P₁ a) (P₂ b))
          (psMul R (psPow R Q a) (psPow R Q b) n)) n
    -- 内側境界を n+1 へ padding（はみ出しは psPowPow_low で消滅）
    have h3 : rsum R (fun a => rsum R (fun b =>
          R.mul (R.mul (P₁ a) (P₂ b))
            (psMul R (psPow R Q a) (psPow R Q b) n)) (n + 1 - a)) (n + 1)
        = rsum R (fun a => rsum R (fun b =>
            R.mul (R.mul (P₁ a) (P₂ b))
              (psMul R (psPow R Q a) (psPow R Q b) n)) (n + 1)) (n + 1) :=
      rsum_congr R (n + 1) (fun a ha =>
        (rsum_pad R (fun b => R.mul (R.mul (P₁ a) (P₂ b))
            (psMul R (psPow R Q a) (psPow R Q b) n))
          (show n + 1 - a ≤ n + 1 by omega)
          (fun b hb => by
            show R.mul (R.mul (P₁ a) (P₂ b))
                (psMul R (psPow R Q a) (psPow R Q b) n) = R.zero
            rw [psPowPow_low R Q Q hQ hQ a b n (by omega)]
            exact R.mul_zero _)).symm)
    rw [h1, h2, h3]
  -- 右辺 → 共通形
  have hRHS : psMul R (psComp R P₁ Q) (psComp R P₂ Q) n
      = rsum R (fun a => rsum R (fun b =>
          R.mul (R.mul (P₁ a) (P₂ b))
            (psMul R (psPow R Q a) (psPow R Q b) n)) (n + 1)) (n + 1) := by
    show rsum R (fun m =>
        R.mul (psComp R P₁ Q m) (psComp R P₂ Q (n - m))) (n + 1) = _
    -- 両因子の内側境界を n+1 へ padding し、積を二重和に展開
    have r1 : rsum R (fun m =>
          R.mul (psComp R P₁ Q m) (psComp R P₂ Q (n - m))) (n + 1)
        = rsum R (fun m => rsum R (fun a => rsum R (fun b =>
            R.mul (R.mul (P₁ a) (P₂ b))
              (R.mul (psPow R Q a m) (psPow R Q b (n - m)))) (n + 1)) (n + 1))
            (n + 1) :=
      rsum_congr R (n + 1) (fun m hm => by
        have hA : psComp R P₁ Q m
            = rsum R (fun a => R.mul (P₁ a) (psPow R Q a m)) (n + 1) := by
          show rsum R (fun a => R.mul (P₁ a) (psPow R Q a m)) (m + 1) = _
          exact (rsum_pad R (fun a => R.mul (P₁ a) (psPow R Q a m))
            (show m + 1 ≤ n + 1 by omega)
            (fun a ha => by
              show R.mul (P₁ a) (psPow R Q a m) = R.zero
              rw [psPow_coeff_zero R Q hQ a m (by omega)]
              exact R.mul_zero _)).symm
        have hB : psComp R P₂ Q (n - m)
            = rsum R (fun b => R.mul (P₂ b) (psPow R Q b (n - m))) (n + 1) := by
          show rsum R (fun b =>
              R.mul (P₂ b) (psPow R Q b (n - m))) (n - m + 1) = _
          exact (rsum_pad R (fun b => R.mul (P₂ b) (psPow R Q b (n - m)))
            (show n - m + 1 ≤ n + 1 by omega)
            (fun b hb => by
              show R.mul (P₂ b) (psPow R Q b (n - m)) = R.zero
              rw [psPow_coeff_zero R Q hQ b (n - m) (by omega)]
              exact R.mul_zero _)).symm
        rw [hA, hB,
          rsum_mul_right R (fun a => R.mul (P₁ a) (psPow R Q a m))
            (rsum R (fun b => R.mul (P₂ b) (psPow R Q b (n - m))) (n + 1))
            (n + 1)]
        refine rsum_congr R (n + 1) (fun a _ => ?_)
        rw [rsum_mul_left R (fun b => R.mul (P₂ b) (psPow R Q b (n - m)))
          (R.mul (P₁ a) (psPow R Q a m)) (n + 1)]
        exact rsum_congr R (n + 1) (fun b _ =>
          R.mul_mul_mul_comm (P₁ a) (psPow R Q a m) (P₂ b)
            (psPow R Q b (n - m))))
    -- 添字交換 (m,a,b) → (a,b,m)
    have r2 : rsum R (fun m => rsum R (fun a => rsum R (fun b =>
          R.mul (R.mul (P₁ a) (P₂ b))
            (R.mul (psPow R Q a m) (psPow R Q b (n - m)))) (n + 1)) (n + 1))
          (n + 1)
        = rsum R (fun a => rsum R (fun m => rsum R (fun b =>
            R.mul (R.mul (P₁ a) (P₂ b))
              (R.mul (psPow R Q a m) (psPow R Q b (n - m)))) (n + 1)) (n + 1))
            (n + 1) :=
      rsum_exchange R (fun m a => rsum R (fun b =>
        R.mul (R.mul (P₁ a) (P₂ b))
          (R.mul (psPow R Q a m) (psPow R Q b (n - m)))) (n + 1)) (n + 1)
        (n + 1)
    have r3 : rsum R (fun a => rsum R (fun m => rsum R (fun b =>
          R.mul (R.mul (P₁ a) (P₂ b))
            (R.mul (psPow R Q a m) (psPow R Q b (n - m)))) (n + 1)) (n + 1))
          (n + 1)
        = rsum R (fun a => rsum R (fun b => rsum R (fun m =>
            R.mul (R.mul (P₁ a) (P₂ b))
              (R.mul (psPow R Q a m) (psPow R Q b (n - m)))) (n + 1)) (n + 1))
            (n + 1) :=
      rsum_congr R (n + 1) (fun a _ =>
        rsum_exchange R (fun m b =>
          R.mul (R.mul (P₁ a) (P₂ b))
            (R.mul (psPow R Q a m) (psPow R Q b (n - m)))) (n + 1) (n + 1))
    -- 内側の m 和を Cauchy 積 (Q^a·Q^b)_n に畳む（定義的）
    have r4 : rsum R (fun a => rsum R (fun b => rsum R (fun m =>
          R.mul (R.mul (P₁ a) (P₂ b))
            (R.mul (psPow R Q a m) (psPow R Q b (n - m)))) (n + 1)) (n + 1))
          (n + 1)
        = rsum R (fun a => rsum R (fun b =>
            R.mul (R.mul (P₁ a) (P₂ b))
              (psMul R (psPow R Q a) (psPow R Q b) n)) (n + 1)) (n + 1) :=
      rsum_congr R (n + 1) (fun a _ => rsum_congr R (n + 1) (fun b _ =>
        (rsum_mul_left R
          (fun m => R.mul (psPow R Q a m) (psPow R Q b (n - m)))
          (R.mul (P₁ a) (P₂ b)) (n + 1)).symm))
    rw [r1, r2, r3, r4]
  rw [hLHS, hRHS]

/-! ## 冪の合成 -/

/-- **定理 (M72F-3): 冪の合成** — (P^m)∘Q = (P∘Q)^m（Q(0) = 0、m 帰納:
    底は psComp_one、段は psComp_mul）。 -/
theorem psComp_pow (R : CRing) (P Q : PS R) (hQ : Q 0 = R.zero) :
    ∀ m, psComp R (psPow R P m) Q = psPow R (psComp R P Q) m := by
  intro m
  induction m with
  | zero => exact psComp_one R Q
  | succ m ih =>
    show psComp R (psMul R (psPow R P m) P) Q
      = psMul R (psPow R (psComp R P Q) m) (psComp R P Q)
    rw [psComp_mul R (psPow R P m) P Q hQ, ih]

/-! ## 1 変数連鎖律 -/

/-- **定理 (M72F-4): 1 変数連鎖律** — (P∘Q)∘W = P∘(Q∘W)
    （Q(0) = W(0) = 0）。両辺を共通形
    Σ_{k≤n} P_k · Σ_{m≤n} (Q^k)_m (W^m)_n に帰着する。 -/
theorem psComp_assoc (R : CRing) (P Q W : PS R)
    (hQ : Q 0 = R.zero) (hW : W 0 = R.zero) :
    psComp R (psComp R P Q) W = psComp R P (psComp R Q W) := by
  funext n
  -- 左辺 → 共通形
  have hLHS : psComp R (psComp R P Q) W n
      = rsum R (fun k => R.mul (P k)
          (rsum R (fun m => R.mul (psPow R Q k m) (psPow R W m n)) (n + 1)))
          (n + 1) := by
    show rsum R (fun m => R.mul (psComp R P Q m) (psPow R W m n)) (n + 1) = _
    -- 内側境界を n+1 へ padding し、(W^m)_n を中へ配る
    have h1 : rsum R (fun m =>
          R.mul (psComp R P Q m) (psPow R W m n)) (n + 1)
        = rsum R (fun m => rsum R (fun k =>
            R.mul (P k) (R.mul (psPow R Q k m) (psPow R W m n))) (n + 1))
            (n + 1) :=
      rsum_congr R (n + 1) (fun m hm => by
        have hpad : psComp R P Q m
            = rsum R (fun k => R.mul (P k) (psPow R Q k m)) (n + 1) := by
          show rsum R (fun k => R.mul (P k) (psPow R Q k m)) (m + 1) = _
          exact (rsum_pad R (fun k => R.mul (P k) (psPow R Q k m))
            (show m + 1 ≤ n + 1 by omega)
            (fun k hk => by
              show R.mul (P k) (psPow R Q k m) = R.zero
              rw [psPow_coeff_zero R Q hQ k m (by omega)]
              exact R.mul_zero _)).symm
        rw [hpad, rsum_mul_right R (fun k => R.mul (P k) (psPow R Q k m))
          (psPow R W m n) (n + 1)]
        exact rsum_congr R (n + 1) (fun k _ =>
          R.mul_assoc (P k) (psPow R Q k m) (psPow R W m n)))
    -- 添字交換 (m,k) → (k,m)
    have h2 : rsum R (fun m => rsum R (fun k =>
          R.mul (P k) (R.mul (psPow R Q k m) (psPow R W m n))) (n + 1)) (n + 1)
        = rsum R (fun k => rsum R (fun m =>
            R.mul (P k) (R.mul (psPow R Q k m) (psPow R W m n))) (n + 1))
            (n + 1) :=
      rsum_exchange R (fun m k =>
        R.mul (P k) (R.mul (psPow R Q k m) (psPow R W m n))) (n + 1) (n + 1)
    -- P_k を外へ
    have h3 : rsum R (fun k => rsum R (fun m =>
          R.mul (P k) (R.mul (psPow R Q k m) (psPow R W m n))) (n + 1)) (n + 1)
        = rsum R (fun k => R.mul (P k)
            (rsum R (fun m => R.mul (psPow R Q k m) (psPow R W m n)) (n + 1)))
            (n + 1) :=
      rsum_congr R (n + 1) (fun k _ =>
        (rsum_mul_left R (fun m => R.mul (psPow R Q k m) (psPow R W m n))
          (P k) (n + 1)).symm)
    rw [h1, h2, h3]
  -- 右辺 → 共通形（(Q∘W)^k = (Q^k)∘W は M72F-3）
  have hRHS : psComp R P (psComp R Q W) n
      = rsum R (fun k => R.mul (P k)
          (rsum R (fun m => R.mul (psPow R Q k m) (psPow R W m n)) (n + 1)))
          (n + 1) := by
    show rsum R (fun k =>
        R.mul (P k) (psPow R (psComp R Q W) k n)) (n + 1) = _
    refine rsum_congr R (n + 1) (fun k _ => ?_)
    rw [← psComp_pow R Q W hW k]
    rfl
  rw [hLHS, hRHS]

/-! ## Lubin–Tate 多項式の反復 -/

/-- **M72F-5a: f^{∘n}** — LT 多項式 f = pX + X^p の n 回反復
    （[p^n] 系列の本体）。 -/
def ltIter (p : Nat) : Nat → PS (zpRing p)
  | 0 => psX (zpRing p)
  | n + 1 => psComp (zpRing p) (ltIter p n) (ltPoly p)

/-- **M72F-5b: 定数項** f^{∘n}(0) = 0。 -/
theorem ltIter_coeff_zero (p : Nat) (hp : 2 ≤ p) :
    ∀ n, ltIter p n 0 = (zpRing p).zero := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show psComp (zpRing p) (ltIter p n) (ltPoly p) 0 = (zpRing p).zero
    rw [psComp_coeff_zero (zpRing p) (ltIter p n) (ltPoly p)]
    exact ih

/-- **M72F-5c: 一次係数** (f^{∘n})_1 = π^n（π = p の像）。 -/
theorem ltIter_coeff_one (p : Nat) (hp : 2 ≤ p) :
    ∀ n, ltIter p n 1
      = rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show psComp (zpRing p) (ltIter p n) (ltPoly p) 1 = _
    rw [psComp_coeff_one (zpRing p) (ltIter p n) (ltPoly p), ih,
      ltPoly_coeff_one p hp]
    rfl

/-- **定理 (M72F-5d): 反復の可換性** f^{∘n}∘f = f∘f^{∘n}
    （n 帰納 + 連鎖律 M72F-4）。 -/
theorem ltIter_comm (p : Nat) (hp : 2 ≤ p) :
    ∀ n, psComp (zpRing p) (ltIter p n) (ltPoly p)
      = psComp (zpRing p) (ltPoly p) (ltIter p n) := by
  intro n
  induction n with
  | zero =>
    rw [show ltIter p 0 = psX (zpRing p) from rfl,
      psComp_X (zpRing p) (ltPoly p) (ltPoly_coeff_zero p hp),
      psComp_X_right (zpRing p) (ltPoly p)]
  | succ n ih =>
    show psComp (zpRing p)
        (psComp (zpRing p) (ltIter p n) (ltPoly p)) (ltPoly p)
      = psComp (zpRing p) (ltPoly p)
          (psComp (zpRing p) (ltIter p n) (ltPoly p))
    calc psComp (zpRing p)
          (psComp (zpRing p) (ltIter p n) (ltPoly p)) (ltPoly p)
        = psComp (zpRing p)
            (psComp (zpRing p) (ltPoly p) (ltIter p n)) (ltPoly p) := by
          rw [ih]
      _ = psComp (zpRing p) (ltPoly p)
            (psComp (zpRing p) (ltIter p n) (ltPoly p)) :=
          psComp_assoc (zpRing p) (ltPoly p) (ltIter p n) (ltPoly p)
            (ltIter_coeff_zero p hp n) (ltPoly_coeff_zero p hp)

/-! ## f∘G の明示形 -/

/-- **M72F-6a: 一次単項式の合成** (c·X)∘G = c·G（G(0) = 0）。 -/
theorem psComp_single_one (R : CRing) (c : R.carrier) (G : PS R)
    (hG : G 0 = R.zero) :
    psComp R (psSingle R c 1) G = psSmul R c G := by
  funext n
  show rsum R (fun k => R.mul (psSingle R c 1 k) (psPow R G k n)) (n + 1)
    = R.mul c (G n)
  cases n with
  | zero =>
    show R.add R.zero (R.mul (psSingle R c 1 0) (psPow R G 0 0))
      = R.mul c (G 0)
    rw [show psSingle R c 1 0 = R.zero from if_neg (show ¬0 = 1 by omega),
      R.zero_mul, hG, R.mul_zero]
    exact R.add_zero _
  | succ m =>
    have hs : rsum R (fun k =>
          R.mul (psSingle R c 1 k) (psPow R G k (m + 1))) (m + 2)
        = R.mul (psSingle R c 1 1) (psPow R G 1 (m + 1)) :=
      rsum_single R _ 1 (m + 2) (by omega) (fun j _ hj => by
        rw [show psSingle R c 1 j = R.zero from if_neg hj]
        exact R.zero_mul _)
    rw [hs, show psSingle R c 1 1 = c from if_pos rfl, psPow_one R G]

/-- **M72F-6b: 単項式の合成** X^m∘G = G^m（G(0) = 0。n < m の側は
    truncation psPow_coeff_zero）。 -/
theorem psComp_mono (R : CRing) (G : PS R) (hG : G 0 = R.zero) (m : Nat) :
    psComp R (psMono R m) G = psPow R G m := by
  funext n
  show rsum R (fun k => R.mul (psMono R m k) (psPow R G k n)) (n + 1)
    = psPow R G m n
  cases Nat.lt_or_ge n m with
  | inl hlt =>
    have hz : rsum R (fun k => R.mul (psMono R m k) (psPow R G k n)) (n + 1)
        = rsum R (fun _ => R.zero) (n + 1) :=
      rsum_congr R (n + 1) (fun k hk => by
        rw [show psMono R m k = R.zero from if_neg (show ¬k = m by omega)]
        exact R.zero_mul _)
    rw [hz, rsum_const_zero R (n + 1),
      psPow_coeff_zero R G hG m n hlt]
  | inr hge =>
    have hs : rsum R (fun k => R.mul (psMono R m k) (psPow R G k n)) (n + 1)
        = R.mul (psMono R m m) (psPow R G m n) :=
      rsum_single R _ m (n + 1) (by omega) (fun j _ hj => by
        rw [show psMono R m j = R.zero from if_neg hj]
        exact R.zero_mul _)
    rw [hs, show psMono R m m = R.one from if_pos rfl]
    exact R.one_mul _

/-- **定理 (M72F-6c): f∘G = π·G + G^p**（G(0) = 0。f = πX + X^p の
    係数は k = 1, p のみ生存し、合成の加法性で分解）。 -/
theorem psComp_ltPoly_left (p : Nat) (hp : 2 ≤ p) (G : PS (zpRing p))
    (hG : G 0 = (zpRing p).zero) :
    psComp (zpRing p) (ltPoly p) G
      = (psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) G)
          (psPow (zpRing p) G p) := by
  show psComp (zpRing p)
      ((psRing (zpRing p)).add
        (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1)
        (psMono (zpRing p) p)) G = _
  rw [psComp_add (zpRing p)
      (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1)
      (psMono (zpRing p) p) G,
    psComp_single_one (zpRing p) ((toZp p).map ((p : Nat) : Int)) G hG,
    psComp_mono (zpRing p) G hG p]

/-! ## [p^n] 系列の同定 -/

/-- **定理 (M72F-7): f^{∘n} = ltSol(π^n)** — 反復は Lubin–Tate 補題
    （M49）の一意解 [π^n] 系列に一致する（F(0) = 0・F(1) = π^n・
    方程式 F∘f = π·F + F^p を ltIter_comm + psComp_ltPoly_left で検証）。
    p^n 等分点（LCFT 分岐部）への入口。 -/
theorem ltIter_eq_ltSol (p : Nat) (hp : IsPrime p) :
    ∀ n, ltIter p n
      = ltSol p hp (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n) := by
  intro n
  obtain ⟨_, _, huniq⟩ :=
    lubin_tate p hp (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n)
  exact huniq (ltIter p n) (ltIter_coeff_zero p hp.1 n)
    (ltIter_coeff_one p hp.1 n)
    (by
      rw [ltIter_comm p hp.1 n]
      exact psComp_ltPoly_left p hp.1 (ltIter p n)
        (ltIter_coeff_zero p hp.1 n))

end IUT
