/-
  IUT/FormalGroupFam.lean — M69a（乗法性のための代数基盤: 結合則キャンペーン第七層）

  結合則の最難所 — ps23Comp の乗法性 (F·G)∘(P,Q) = (F∘(P,Q))·(G∘(P,Q)) —
  を「PS3 環の中の有限族和の代数」に持ち上げるための基盤層。
  鍵となる発想: 係数ごとの打ち切り和 rsum を **族和 ps3Fam_sum**
  （fun j k i => Σ_{t<N} v t j k i）として固定境界 N で扱うと、
  族和と積の分配・スカラーの抽出・添字交換が全て**環レベルの恒等式**
  になり、係数掘りが消える。打ち切り境界の差は **rsum_pad**（高位消滅
  での詰め替え）と冪積の下方消滅（M68）で吸収する。

  * M69a-1 `rsum_pad` — 高位で消える和の境界詰め替え
  * M69a-2 `ps3Const` / `ps3_const_mul` / `ps3Smul` / `ps3Smul_eq` —
    三重定数とスカラー倍（smul = 定数との積、三重一点集中和）
  * M69a-3 `ps3Fam_sum` と代数則 — **族和は積と分配**
    （Fam v N · W = Fam (v · W) N、W · Fam も同様）・congr・
    スカラー和の抽出 ps3Smul_rsum
  * M69a-4 `ps3Mul_congr_le` — 総次数 ≤ n の一致から積の総次数 n の
    係数一致（無条件版 — M64 と違い定数項消滅不要）
  * M69a-5 `ps3PowPow_mul` — 冪積の結合 (P^{a₁}Q^{b₁})·(P^{a₂}Q^{b₂})
    = P^{a₁+a₂}Q^{b₁+b₂}（可換環の冪指数法則）
  * M69a-6 `ps23Comp_eq_fam` — **打ち切り安定性**: 総次数 < N の係数で
    ps23Comp は境界 N の族和に一致

  次層（M69b）でこれらを合流させ乗法性 → 連鎖律 → 結合則。
  全て選択公理不使用。
-/
import IUT.FormalGroupChain

namespace IUT

/-! ## 境界詰め替え -/

/-- **M69a-1: 高位消滅での境界詰め替え** — g が M 以降で消えるなら
    Σ_{<N} g = Σ_{<M} g（M ≤ N）。 -/
theorem rsum_pad (R : CRing) (g : Nat → R.carrier) {M N : Nat}
    (hMN : M ≤ N) (h : ∀ m, M ≤ m → g m = R.zero) :
    rsum R g N = rsum R g M := by
  induction hMN with
  | refl => rfl
  | @step N' h' ih =>
    show R.add (rsum R g N') (g N') = rsum R g M
    have hM : M ≤ N' := h'
    rw [h N' hM, CRing.add_zero R _, ih]

/-! ## 三重定数とスカラー倍 -/

/-- 三重定数（(0,0,0) に集中）。 -/
def ps3Const (R : CRing) (c : R.carrier) : PS3 R :=
  psC (psRing (psRing R)) (psC (psRing R) (psC R c))

/-- **M69a-2a: 定数との積の係数** — (const c · A)_{j,k,i} = c·A_{j,k,i}
    （三重一点集中和、(c,b,a) = (0,0,0) にスパイク）。 -/
theorem ps3_const_mul (R : CRing) (c : R.carrier) (A : PS3 R)
    (j k i : Nat) :
    psMul (psRing (psRing R)) (ps3Const R c) A j k i
      = R.mul c (A j k i) := by
  rw [ps3Mul_coeff R (ps3Const R c) A j k i]
  have houter : rsum R (fun c' => rsum R (fun b => rsum R (fun a =>
        R.mul (ps3Const R c c' b a) (A (j - c') (k - b) (i - a)))
        (i + 1)) (k + 1)) (j + 1)
      = rsum R (fun b => rsum R (fun a =>
          R.mul (ps3Const R c 0 b a) (A j (k - b) (i - a))) (i + 1))
          (k + 1) :=
    rsum_single R (fun c' => rsum R (fun b => rsum R (fun a =>
        R.mul (ps3Const R c c' b a) (A (j - c') (k - b) (i - a)))
        (i + 1)) (k + 1)) 0 (j + 1) (by omega)
      (fun c' _ hc' => by
        have hz2 : ∀ b, b < k + 1 → rsum R (fun a =>
            R.mul (ps3Const R c c' b a)
              (A (j - c') (k - b) (i - a))) (i + 1) = R.zero :=
          fun b _ => by
            have hz3 : ∀ a, a < i + 1 →
                R.mul (ps3Const R c c' b a)
                  (A (j - c') (k - b) (i - a)) = R.zero :=
              fun a _ => by
                rw [show ps3Const R c c'
                    = (psRing (psRing R)).zero from if_neg hc']
                exact R.zero_mul _
            have hc1 : rsum R (fun a =>
                R.mul (ps3Const R c c' b a)
                  (A (j - c') (k - b) (i - a))) (i + 1)
                = rsum R (fun _ => R.zero) (i + 1) :=
              rsum_congr R (i + 1) hz3
            rw [hc1]
            exact rsum_const_zero R (i + 1)
        have hc2 : rsum R (fun b => rsum R (fun a =>
              R.mul (ps3Const R c c' b a)
                (A (j - c') (k - b) (i - a))) (i + 1)) (k + 1)
            = rsum R (fun _ => R.zero) (k + 1) :=
          rsum_congr R (k + 1) hz2
        show rsum R (fun b => rsum R (fun a =>
            R.mul (ps3Const R c c' b a)
              (A (j - c') (k - b) (i - a))) (i + 1)) (k + 1) = R.zero
        rw [hc2]
        exact rsum_const_zero R (k + 1))
  rw [houter]
  have hmid : rsum R (fun b => rsum R (fun a =>
        R.mul (ps3Const R c 0 b a) (A j (k - b) (i - a))) (i + 1))
        (k + 1)
      = rsum R (fun a =>
          R.mul (ps3Const R c 0 0 a) (A j k (i - a))) (i + 1) :=
    rsum_single R (fun b => rsum R (fun a =>
        R.mul (ps3Const R c 0 b a) (A j (k - b) (i - a))) (i + 1))
      0 (k + 1) (by omega)
      (fun b _ hb => by
        have hz3 : ∀ a, a < i + 1 →
            R.mul (ps3Const R c 0 b a) (A j (k - b) (i - a)) = R.zero :=
          fun a _ => by
            rw [show ps3Const R c 0 b a = R.zero from by
              show (if b = 0 then psC R c else (psRing R).zero) a = R.zero
              rw [if_neg hb]
              rfl]
            exact R.zero_mul _
        have hc1 : rsum R (fun a =>
            R.mul (ps3Const R c 0 b a) (A j (k - b) (i - a))) (i + 1)
            = rsum R (fun _ => R.zero) (i + 1) :=
          rsum_congr R (i + 1) hz3
        show rsum R (fun a =>
            R.mul (ps3Const R c 0 b a) (A j (k - b) (i - a))) (i + 1)
          = R.zero
        rw [hc1]
        exact rsum_const_zero R (i + 1))
  rw [hmid]
  have hinner : rsum R (fun a =>
        R.mul (ps3Const R c 0 0 a) (A j k (i - a))) (i + 1)
      = R.mul (ps3Const R c 0 0 0) (A j k (i - 0)) :=
    rsum_single R (fun a =>
        R.mul (ps3Const R c 0 0 a) (A j k (i - a))) 0 (i + 1)
      (by omega)
      (fun a _ ha => by
        show R.mul (ps3Const R c 0 0 a) (A j k (i - a)) = R.zero
        rw [show ps3Const R c 0 0 a = R.zero from by
          show (if a = 0 then c else R.zero) = R.zero
          rw [if_neg ha]]
        exact R.zero_mul _)
  rw [hinner]
  rfl

/-- スカラー倍（係数ごとの c 倍）。 -/
def ps3Smul (R : CRing) (c : R.carrier) (A : PS3 R) : PS3 R :=
  fun j k i => R.mul c (A j k i)

/-- **M69a-2b**: スカラー倍 = 三重定数との積。 -/
theorem ps3Smul_eq (R : CRing) (c : R.carrier) (A : PS3 R) :
    ps3Smul R c A = psMul (psRing (psRing R)) (ps3Const R c) A := by
  funext j k i
  exact (ps3_const_mul R c A j k i).symm

/-! ## 族和の代数 -/

/-- **M69a-3a: 族和** — (Fam v N)_{j,k,i} = Σ_{t<N} (v t)_{j,k,i}
    （固定境界の係数ごとの和。t についての和が PS3 環の有限和に
    一致するのは succ ケースの定義的等式 Fam v (N+1) ≡
    add₃ (Fam v N) (v N) から）。 -/
def ps3Fam_sum (R : CRing) (v : Nat → PS3 R) (N : Nat) : PS3 R :=
  fun j k i => rsum R (fun t => v t j k i) N

/-- 族和の項別書き換え。 -/
theorem ps3Fam_congr (R : CRing) {v w : Nat → PS3 R} (N : Nat)
    (h : ∀ t, t < N → v t = w t) :
    ps3Fam_sum R v N = ps3Fam_sum R w N := by
  funext j k i
  exact rsum_congr R N (fun t ht => by rw [h t ht])

/-- **定理 (M69a-3b): 族和は右からの積と分配** —
    (Fam v N)·W = Fam (fun t => (v t)·W) N（環レベルの帰納:
    succ は右分配則、zero は 0·W = 0）。 -/
theorem ps3Fam_mul_right (R : CRing) (v : Nat → PS3 R) (W : PS3 R) :
    ∀ N, psMul (psRing (psRing R)) (ps3Fam_sum R v N) W
      = ps3Fam_sum R (fun t => psMul (psRing (psRing R)) (v t) W) N := by
  intro N
  induction N with
  | zero =>
    show psMul (psRing (psRing R)) (ps3Fam_sum R v 0) W = _
    have h0 : ps3Fam_sum R v 0
        = (psRing (psRing (psRing R))).zero := rfl
    rw [h0]
    exact CRing.zero_mul (psRing (psRing (psRing R))) W
  | succ N ih =>
    show (psRing (psRing (psRing R))).mul
        ((psRing (psRing (psRing R))).add (ps3Fam_sum R v N) (v N)) W
      = (psRing (psRing (psRing R))).add
          (ps3Fam_sum R (fun t => psMul (psRing (psRing R)) (v t) W) N)
          ((psRing (psRing (psRing R))).mul (v N) W)
    have ih' : (psRing (psRing (psRing R))).mul (ps3Fam_sum R v N) W
        = ps3Fam_sum R (fun t => psMul (psRing (psRing R)) (v t) W) N :=
      ih
    rw [(psRing (psRing (psRing R))).right_distrib (ps3Fam_sum R v N)
      (v N) W, ih']

/-- **定理 (M69a-3c): 族和は左からの積と分配** —
    W·(Fam v N) = Fam (fun t => W·(v t)) N（左分配則）。 -/
theorem ps3Fam_mul_left (R : CRing) (v : Nat → PS3 R) (W : PS3 R) :
    ∀ N, psMul (psRing (psRing R)) W (ps3Fam_sum R v N)
      = ps3Fam_sum R (fun t => psMul (psRing (psRing R)) W (v t)) N := by
  intro N
  induction N with
  | zero =>
    show psMul (psRing (psRing R)) W (ps3Fam_sum R v 0) = _
    have h0 : ps3Fam_sum R v 0
        = (psRing (psRing (psRing R))).zero := rfl
    rw [h0]
    exact CRing.mul_zero (psRing (psRing (psRing R))) W
  | succ N ih =>
    show (psRing (psRing (psRing R))).mul W
        ((psRing (psRing (psRing R))).add (ps3Fam_sum R v N) (v N))
      = (psRing (psRing (psRing R))).add
          (ps3Fam_sum R (fun t => psMul (psRing (psRing R)) W (v t)) N)
          ((psRing (psRing (psRing R))).mul W (v N))
    have ih' : (psRing (psRing (psRing R))).mul W (ps3Fam_sum R v N)
        = ps3Fam_sum R (fun t => psMul (psRing (psRing R)) W (v t)) N :=
      ih
    rw [(psRing (psRing (psRing R))).left_distrib W (ps3Fam_sum R v N)
      (v N), ih']

/-- **M69a-3d: スカラー和の抽出** —
    ps3Smul (Σ_{t<N} f t) A = Fam (fun t => ps3Smul (f t) A) N。 -/
theorem ps3Smul_rsum (R : CRing) (f : Nat → R.carrier) (A : PS3 R) :
    ∀ N, ps3Smul R (rsum R f N) A
      = ps3Fam_sum R (fun t => ps3Smul R (f t) A) N := by
  intro N
  induction N with
  | zero =>
    funext j k i
    exact R.zero_mul (A j k i)
  | succ N ih =>
    funext j k i
    show R.mul (R.add (rsum R f N) (f N)) (A j k i)
      = R.add (ps3Fam_sum R (fun t => ps3Smul R (f t) A) N j k i)
          (R.mul (f N) (A j k i))
    rw [R.right_distrib (rsum R f N) (f N) (A j k i)]
    have hih : R.mul (rsum R f N) (A j k i)
        = ps3Fam_sum R (fun t => ps3Smul R (f t) A) N j k i :=
      congrFun (congrFun (congrFun ih j) k) i
    rw [hih]

/-! ## 積の係数一致と冪積の結合 -/

/-- **定理 (M69a-4): 積の係数一致（無条件版）** — A と A'・B と B' が
    総次数 ≤ n で一致するなら、積の総次数 = n の係数は一致する
    （各分割の両因子の総次数が ≤ n に収まるため。M64 と違い
    定数項消滅は不要）。 -/
theorem ps3Mul_congr_le (R : CRing) {A A' B B' : PS3 R} (n : Nat)
    (hA : ∀ c b a, a + b + c ≤ n → A c b a = A' c b a)
    (hB : ∀ c b a, a + b + c ≤ n → B c b a = B' c b a)
    (j k i : Nat) (hdeg : i + k + j ≤ n) :
    psMul (psRing (psRing R)) A B j k i
      = psMul (psRing (psRing R)) A' B' j k i := by
  rw [ps3Mul_coeff R A B j k i, ps3Mul_coeff R A' B' j k i]
  exact rsum_congr R (j + 1) (fun c hc =>
    rsum_congr R (k + 1) (fun b hb =>
      rsum_congr R (i + 1) (fun a ha => by
        rw [hA c b a (by omega), hB (j - c) (k - b) (i - a) (by omega)])))

/-- 可換環の interchange 法則 (A·B)·(C·D) = (A·C)·(B·D)。 -/
theorem CRing.mul_mul_comm (R : CRing) (A B C D : R.carrier) :
    R.mul (R.mul A B) (R.mul C D) = R.mul (R.mul A C) (R.mul B D) := by
  rw [R.mul_assoc A B (R.mul C D), ← R.mul_assoc B C D,
    R.mul_comm B C, R.mul_assoc C B D, ← R.mul_assoc A C (R.mul B D)]

/-- **定理 (M69a-5): 冪積の結合** —
    (P^{a₁}Q^{b₁})·(P^{a₂}Q^{b₂}) = P^{a₁+a₂}Q^{b₁+b₂}
    （可換環の冪指数法則 rpow_add + 並べ替え）。 -/
theorem ps3PowPow_mul (R : CRing) (P Q : PS3 R) (a₁ b₁ a₂ b₂ : Nat) :
    psMul (psRing (psRing R))
      (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
        (psPow (psRing (psRing R)) Q b₁))
      (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₂)
        (psPow (psRing (psRing R)) Q b₂))
    = psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P (a₁ + a₂))
        (psPow (psRing (psRing R)) Q (b₁ + b₂)) := by
  have hP : psPow (psRing (psRing R)) P (a₁ + a₂)
      = psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a₁)
          (psPow (psRing (psRing R)) P a₂) := by
    rw [psPow_eq_rpow (psRing (psRing R)) P (a₁ + a₂),
      rpow_add (psRing (psRing (psRing R))) P a₁ a₂,
      ← psPow_eq_rpow (psRing (psRing R)) P a₁,
      ← psPow_eq_rpow (psRing (psRing R)) P a₂]
    rfl
  have hQ : psPow (psRing (psRing R)) Q (b₁ + b₂)
      = psMul (psRing (psRing R)) (psPow (psRing (psRing R)) Q b₁)
          (psPow (psRing (psRing R)) Q b₂) := by
    rw [psPow_eq_rpow (psRing (psRing R)) Q (b₁ + b₂),
      rpow_add (psRing (psRing (psRing R))) Q b₁ b₂,
      ← psPow_eq_rpow (psRing (psRing R)) Q b₁,
      ← psPow_eq_rpow (psRing (psRing R)) Q b₂]
    rfl
  rw [hP, hQ]
  exact CRing.mul_mul_comm (psRing (psRing (psRing R)))
    (psPow (psRing (psRing R)) P a₁) (psPow (psRing (psRing R)) Q b₁)
    (psPow (psRing (psRing R)) P a₂) (psPow (psRing (psRing R)) Q b₂)

/-- 三重定数は乗法的（psC = psConstHom の map の三段重ね）。 -/
theorem ps3Const_mul (R : CRing) (c d : R.carrier) :
    psMul (psRing (psRing R)) (ps3Const R c) (ps3Const R d)
      = ps3Const R (R.mul c d) := by
  show psMul (psRing (psRing R))
      (psC (psRing (psRing R)) (psC (psRing R) (psC R c)))
      (psC (psRing (psRing R)) (psC (psRing R) (psC R d)))
    = psC (psRing (psRing R)) (psC (psRing R) (psC R (R.mul c d)))
  rw [show psC R (R.mul c d)
      = psMul R (psC R c) (psC R d) from (psConstHom R).map_mul c d,
    show psC (psRing R) (psMul R (psC R c) (psC R d))
      = psMul (psRing R) (psC (psRing R) (psC R c))
          (psC (psRing R) (psC R d)) from
      (psConstHom (psRing R)).map_mul (psC R c) (psC R d),
    show psC (psRing (psRing R))
        (psMul (psRing R) (psC (psRing R) (psC R c))
          (psC (psRing R) (psC R d)))
      = psMul (psRing (psRing R))
          (psC (psRing (psRing R)) (psC (psRing R) (psC R c)))
          (psC (psRing (psRing R)) (psC (psRing R) (psC R d))) from
      (psConstHom (psRing (psRing R))).map_mul
        (psC (psRing R) (psC R c)) (psC (psRing R) (psC R d))]

/-- **スカラー積の合成則** — (c•A)·(d•B) = (c·d)•(A·B)
    （定数積表示 + interchange）。 -/
theorem ps3Smul_mul_smul (R : CRing) (c d : R.carrier) (A B : PS3 R) :
    psMul (psRing (psRing R)) (ps3Smul R c A) (ps3Smul R d B)
      = ps3Smul R (R.mul c d) (psMul (psRing (psRing R)) A B) := by
  rw [ps3Smul_eq R c A, ps3Smul_eq R d B,
    ps3Smul_eq R (R.mul c d) (psMul (psRing (psRing R)) A B),
    ← ps3Const_mul R c d]
  exact CRing.mul_mul_comm (psRing (psRing (psRing R)))
    (ps3Const R c) A (ps3Const R d) B

/-! ## 打ち切り安定性 -/

/-- **定理 (M69a-6): ps23Comp の族和表示（打ち切り安定性）** —
    総次数 i+k+j < N の係数で、ps23Comp F P Q は境界 N の二重族和
    Fam_b Fam_a smul(F_{b,a}) (P^aQ^b) に一致する
    （P₀₀₀ = Q₀₀₀ = 0。境界の差は冪積の下方消滅 M68 で吸収）。 -/
theorem ps23Comp_eq_fam (R : CRing) (F : PS2 R) (P Q : PS3 R)
    (hP : P 0 0 0 = R.zero) (hQ : Q 0 0 0 = R.zero)
    (N j k i : Nat) (hN : i + k + j < N) :
    ps23Comp R F P Q j k i
      = ps3Fam_sum R (fun b => ps3Fam_sum R (fun a =>
          ps3Smul R (F b a)
            (psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b))) N) N j k i := by
  show rsum R (fun b => rsum R (fun a => R.mul (F b a)
      ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
        (psPow (psRing (psRing R)) Q b)) j k i)) (i + k + j + 1))
      (i + k + j + 1)
    = rsum R (fun b => rsum R (fun a => R.mul (F b a)
        ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i)) N) N
  -- 内側の境界を i+k+j+1 → N に詰め替え（a ≥ i+k+j+1 の項は冪積消滅）
  have hinner : ∀ b, rsum R (fun a => R.mul (F b a)
        ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i)) N
      = rsum R (fun a => R.mul (F b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)) (i + k + j + 1) :=
    fun b => rsum_pad R _ (by omega) (fun a ha => by
      rw [ps3PowPow_low R P Q hP hQ a b j k i (by omega)]
      exact R.mul_zero _)
  -- 外側の境界を詰め替え（b ≥ i+k+j+1 では内側の全項が消滅）
  have houter : rsum R (fun b => rsum R (fun a => R.mul (F b a)
        ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i)) N) N
      = rsum R (fun b => rsum R (fun a => R.mul (F b a)
          ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b)) j k i)) N) (i + k + j + 1) :=
    rsum_pad R _ (by omega) (fun b hb => by
      have hz : rsum R (fun a => R.mul (F b a)
            ((psMul (psRing (psRing R)) (psPow (psRing (psRing R)) P a)
              (psPow (psRing (psRing R)) Q b)) j k i)) N
          = rsum R (fun _ => R.zero) N :=
        rsum_congr R N (fun a _ => by
          rw [ps3PowPow_low R P Q hP hQ a b j k i (by omega)]
          exact R.mul_zero _)
      rw [hz]
      exact rsum_const_zero R N)
  rw [houter]
  exact rsum_congr R (i + k + j + 1) (fun b _ => (hinner b).symm)

end IUT
