/-
  IUT/FormalGroup3Decomp.lean — M65（三変数方程式の分解: 結合則キャンペーン第三層）

  M58（二変数の総次数分解）の三変数版。三変数 LT 方程式
  f∘G = G(f(X), f(Y), f(Z)) の両辺を係数分解し、一意性（次層）の
  入力となる形に落とす。

  * M65-1 `ps3Comp1_add` / `ps3Comp1_single_one` / `ps3Comp1_mono` —
    代入の f-加法性・線形項 (c·X)∘G = c·G・単項式 X^m∘G = G^m
    （総次数 truncation M63 で打ち切り正当化）
  * M65-2 `lt3_lhs_decomp` — **左辺の分解** (f∘G)_{j,k,i}
    = π·G_{j,k,i} + (G^p)_{j,k,i}（f = pX + X^p の k ∈ {1, p} 集中）
  * M65-3 `in3X_pow` / `in3Y_pow` / `in3Z_pow` — **注入は冪と交換**
    (in_• f)^a = in_•(f^a)（psPow_psC・ringHom_rpow・psMap_pow の合流）
  * M65-4 `in3X_mul_in3Y` / `ps3_constV_mul_inZ` — **注入積の構造**:
    in3X·in3Y は二変数の注入積の定数持ち上げ（psConstHom.map_mul で
    一行）、(psC V)·in3Z w の係数 = V_{k,i}·w_j（三重一点集中和）
  * M65-5 `lt3_rhs_coeff` — **右辺の一変数化**
    G(f(X), f(Y), f(Z))_{j,k,i} = Σ_{c,b,a} G_{c,b,a}·(f^a)_i·(f^b)_k·(f^c)_j
    （係数因子が一変数 ltPoly の冪に落ち、M49/M59 の一変数機構
    （対角 π^a・対角下消滅）が直接適用可能に）

  全て選択公理不使用。
-/
import IUT.FormalGroup3Congr

namespace IUT

/-! ## 代入の基本性質 -/

/-- **M65-1a: 代入の f-加法性**。 -/
theorem ps3Comp1_add (R : CRing) (f g : PS R) (G : PS3 R) :
    ps3Comp1 R (psAdd R f g) G
      = psAdd (psRing (psRing R)) (ps3Comp1 R f G) (ps3Comp1 R g G) := by
  funext j k i
  show rsum R (fun m => R.mul (R.add (f m) (g m))
      (psPow (psRing (psRing R)) G m j k i)) (i + k + j + 1)
    = R.add
        (rsum R (fun m => R.mul (f m)
          (psPow (psRing (psRing R)) G m j k i)) (i + k + j + 1))
        (rsum R (fun m => R.mul (g m)
          (psPow (psRing (psRing R)) G m j k i)) (i + k + j + 1))
  rw [← rsum_add R _ _ (i + k + j + 1)]
  exact rsum_congr R (i + k + j + 1) (fun m _ =>
    R.right_distrib (f m) (g m) (psPow (psRing (psRing R)) G m j k i))

/-- **M65-1b: 線形項の代入** — (c·X)∘G の係数 = c·G_{j,k,i}
    （G₀₀₀ = 0）。 -/
theorem ps3Comp1_single_one (R : CRing) (c : R.carrier) (G : PS3 R)
    (hG : G 0 0 0 = R.zero) :
    ∀ j k i, ps3Comp1 R (psSingle R c 1) G j k i = R.mul c (G j k i) := by
  intro j k i
  show rsum R (fun m => R.mul (psSingle R c 1 m)
      (psPow (psRing (psRing R)) G m j k i)) (i + k + j + 1)
    = R.mul c (G j k i)
  cases Nat.decEq (i + k + j) 0 with
  | isTrue h0 =>
    have hi : i = 0 := by omega
    have hk : k = 0 := by omega
    have hj : j = 0 := by omega
    subst hi
    subst hk
    subst hj
    show R.add R.zero (R.mul (psSingle R c 1 0)
        (psPow (psRing (psRing R)) G 0 0 0 0)) = R.mul c (G 0 0 0)
    rw [show psSingle R c 1 0 = R.zero from if_neg (by omega),
      R.zero_mul, hG, R.mul_zero]
    exact R.zero_add R.zero
  | isFalse h0 =>
    have hs : rsum R (fun m => R.mul (psSingle R c 1 m)
          (psPow (psRing (psRing R)) G m j k i)) (i + k + j + 1)
        = R.mul (psSingle R c 1 1) (psPow (psRing (psRing R)) G 1 j k i) :=
      rsum_single R _ 1 (i + k + j + 1) (by omega) (fun m _ hm => by
        rw [show psSingle R c 1 m = R.zero from if_neg hm]
        exact R.zero_mul _)
    rw [hs, show psSingle R c 1 1 = c from if_pos rfl, ps3Pow_one R G]

/-- **M65-1c: 単項式の代入は冪** — X^m∘G = G^m（G₀₀₀ = 0）。 -/
theorem ps3Comp1_mono (R : CRing) (m : Nat) (G : PS3 R)
    (hG : G 0 0 0 = R.zero) :
    ps3Comp1 R (psMono R m) G = psPow (psRing (psRing R)) G m := by
  funext j k i
  show rsum R (fun q => R.mul (psMono R m q)
      (psPow (psRing (psRing R)) G q j k i)) (i + k + j + 1)
    = psPow (psRing (psRing R)) G m j k i
  cases Nat.lt_or_ge (i + k + j) m with
  | inl h =>
    have hz : rsum R (fun q => R.mul (psMono R m q)
          (psPow (psRing (psRing R)) G q j k i)) (i + k + j + 1)
        = rsum R (fun _ => R.zero) (i + k + j + 1) :=
      rsum_congr R (i + k + j + 1) (fun q hq => by
        rw [show psMono R m q = R.zero from if_neg (by omega)]
        exact R.zero_mul _)
    rw [hz, rsum_const_zero, ps3Pow_tcoeff_zero R G hG m i k j h]
  | inr h =>
    have hs : rsum R (fun q => R.mul (psMono R m q)
          (psPow (psRing (psRing R)) G q j k i)) (i + k + j + 1)
        = R.mul (psMono R m m) (psPow (psRing (psRing R)) G m j k i) :=
      rsum_single R _ m (i + k + j + 1) (by omega) (fun q _ hq => by
        rw [show psMono R m q = R.zero from if_neg hq]
        exact R.zero_mul _)
    rw [hs, show psMono R m m = R.one from if_pos rfl]
    exact R.one_mul _

/-! ## 左辺の分解 -/

/-- **定理 (M65-2): 左辺の分解** — (f∘G)_{j,k,i} = π·G_{j,k,i}
    + (G^p)_{j,k,i}（f = pX + X^p、G₀₀₀ = 0。第二項は M64 により
    低次係数のみに依存）。 -/
theorem lt3_lhs_decomp (p : Nat) (G : PS3 (zpRing p))
    (hG : G 0 0 0 = (zpRing p).zero) (j k i : Nat) :
    ps3Comp1 (zpRing p) (ltPoly p) G j k i
      = (zpRing p).add
          ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) (G j k i))
          (psPow (psRing (psRing (zpRing p))) G p j k i) := by
  have h1 : ps3Comp1 (zpRing p) (ltPoly p) G j k i
      = (zpRing p).add
          (ps3Comp1 (zpRing p)
            (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1) G
            j k i)
          (ps3Comp1 (zpRing p) (psMono (zpRing p) p) G j k i) :=
    congrFun (congrFun (congrFun (ps3Comp1_add (zpRing p)
      (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1)
      (psMono (zpRing p) p) G) j) k) i
  rw [h1, ps3Comp1_single_one (zpRing p) _ G hG j k i,
    ps3Comp1_mono (zpRing p) p G hG]

/-! ## 注入は冪と交換 -/

/-- **M65-3a**: (in3X f)^a = in3X(f^a)。 -/
theorem in3X_pow (R : CRing) (f : PS R) (a : Nat) :
    psPow (psRing (psRing R)) (in3X R f) a = in3X R (psPow R f a) := by
  show psPow (psRing (psRing R))
      (psC (psRing (psRing R)) (psC (psRing R) f)) a = _
  rw [psPow_psC (psRing (psRing R)) (psC (psRing R) f) a,
    show rpow (psRing (psRing R)) (psC (psRing R) f) a
        = psC (psRing R) (rpow (psRing R) f a) from
      (ringHom_rpow (psConstHom (psRing R)) f a).symm,
    ← psPow_eq_rpow R f a]
  rfl

/-- **M65-3b**: (in3Y f)^b = in3Y(f^b)。 -/
theorem in3Y_pow (R : CRing) (f : PS R) (b : Nat) :
    psPow (psRing (psRing R)) (in3Y R f) b = in3Y R (psPow R f b) := by
  show psPow (psRing (psRing R))
      (psC (psRing (psRing R)) (psMap (psConstHom R) f)) b = _
  rw [psPow_psC (psRing (psRing R)) (psMap (psConstHom R) f) b,
    ← psPow_eq_rpow (psRing R) (psMap (psConstHom R) f) b,
    ← psMap_pow (psConstHom R) f b]
  rfl

/-- **M65-3c**: (in3Z f)^c = in3Z(f^c)。 -/
theorem in3Z_pow (R : CRing) (f : PS R) (c : Nat) :
    psPow (psRing (psRing R)) (in3Z R f) c = in3Z R (psPow R f c) :=
  (psMap_pow (RingHom.comp (psConstHom R) (psConstHom (psRing R))) f c).symm

/-! ## 注入積の構造 -/

/-- **M65-4a**: in3X g · in3Y h = （二変数の注入積 inX₂g·inY₂h の
    定数持ち上げ）— psConstHom の map_mul で一行。 -/
theorem in3X_mul_in3Y (R : CRing) (g h : PS R) :
    psMul (psRing (psRing R)) (in3X R g) (in3Y R h)
      = psC (psRing (psRing R))
          (psMul (psRing R) (psC (psRing R) g)
            (psMap (psConstHom R) h)) :=
  ((psConstHom (psRing (psRing R))).map_mul (psC (psRing R) g)
    (psMap (psConstHom R) h)).symm

/-- **定理 (M65-4b): 定数持ち上げ × Z 注入の係数公式** —
    ((psC V)·in3Z w)_{j,k,i} = V_{k,i}·w_j（三重一点集中和:
    c = 0・b = k・a = i にスパイク）。 -/
theorem ps3_constV_mul_inZ (R : CRing) (V : PS2 R) (w : PS R)
    (j k i : Nat) :
    psMul (psRing (psRing R)) (psC (psRing (psRing R)) V) (in3Z R w)
        j k i
      = R.mul (V k i) (w j) := by
  rw [ps3Mul_coeff R (psC (psRing (psRing R)) V) (in3Z R w) j k i]
  have houter : rsum R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul ((psC (psRing (psRing R)) V) c b a)
          (in3Z R w (j - c) (k - b) (i - a))) (i + 1)) (k + 1)) (j + 1)
      = rsum R (fun b => rsum R (fun a =>
          R.mul ((psC (psRing (psRing R)) V) 0 b a)
            (in3Z R w j (k - b) (i - a))) (i + 1)) (k + 1) :=
    rsum_single R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul ((psC (psRing (psRing R)) V) c b a)
          (in3Z R w (j - c) (k - b) (i - a))) (i + 1)) (k + 1))
      0 (j + 1) (by omega)
      (fun c _ hc => by
        have hz2 : ∀ b, b < k + 1 → rsum R (fun a =>
            R.mul ((psC (psRing (psRing R)) V) c b a)
              (in3Z R w (j - c) (k - b) (i - a))) (i + 1) = R.zero :=
          fun b _ => by
            have hz3 : ∀ a, a < i + 1 →
                R.mul ((psC (psRing (psRing R)) V) c b a)
                  (in3Z R w (j - c) (k - b) (i - a)) = R.zero :=
              fun a _ => by
                rw [show (psC (psRing (psRing R)) V) c
                    = (psRing (psRing R)).zero from if_neg hc]
                exact R.zero_mul _
            have hcz : rsum R (fun a =>
                R.mul ((psC (psRing (psRing R)) V) c b a)
                  (in3Z R w (j - c) (k - b) (i - a))) (i + 1)
                = rsum R (fun _ => R.zero) (i + 1) :=
              rsum_congr R (i + 1) hz3
            rw [hcz]
            exact rsum_const_zero R (i + 1)
        have hcz2 : rsum R (fun b => rsum R (fun a =>
              R.mul ((psC (psRing (psRing R)) V) c b a)
                (in3Z R w (j - c) (k - b) (i - a))) (i + 1)) (k + 1)
            = rsum R (fun _ => R.zero) (k + 1) :=
          rsum_congr R (k + 1) hz2
        show rsum R (fun b => rsum R (fun a =>
            R.mul ((psC (psRing (psRing R)) V) c b a)
              (in3Z R w (j - c) (k - b) (i - a))) (i + 1)) (k + 1)
          = R.zero
        rw [hcz2]
        exact rsum_const_zero R (k + 1))
  rw [houter]
  have hmid : rsum R (fun b => rsum R (fun a =>
        R.mul ((psC (psRing (psRing R)) V) 0 b a)
          (in3Z R w j (k - b) (i - a))) (i + 1)) (k + 1)
      = rsum R (fun a =>
          R.mul ((psC (psRing (psRing R)) V) 0 k a)
            (in3Z R w j (k - k) (i - a))) (i + 1) :=
    rsum_single R (fun b => rsum R (fun a =>
        R.mul ((psC (psRing (psRing R)) V) 0 b a)
          (in3Z R w j (k - b) (i - a))) (i + 1))
      k (k + 1) (by omega)
      (fun b hb hbk => by
        have hz3 : ∀ a, a < i + 1 →
            R.mul ((psC (psRing (psRing R)) V) 0 b a)
              (in3Z R w j (k - b) (i - a)) = R.zero :=
          fun a _ => by
            rw [show in3Z R w j (k - b) (i - a) = R.zero from by
              show (if k - b = 0 then psC R (w j) else (psRing R).zero)
                  (i - a) = R.zero
              rw [if_neg (show ¬ k - b = 0 by omega)]
              rfl]
            exact R.mul_zero _
        have hcz : rsum R (fun a =>
            R.mul ((psC (psRing (psRing R)) V) 0 b a)
              (in3Z R w j (k - b) (i - a))) (i + 1)
            = rsum R (fun _ => R.zero) (i + 1) :=
          rsum_congr R (i + 1) hz3
        show rsum R (fun a =>
            R.mul ((psC (psRing (psRing R)) V) 0 b a)
              (in3Z R w j (k - b) (i - a))) (i + 1) = R.zero
        rw [hcz]
        exact rsum_const_zero R (i + 1))
  rw [hmid]
  have hinner : rsum R (fun a =>
        R.mul ((psC (psRing (psRing R)) V) 0 k a)
          (in3Z R w j (k - k) (i - a))) (i + 1)
      = R.mul ((psC (psRing (psRing R)) V) 0 k i)
          (in3Z R w j (k - k) (i - i)) :=
    rsum_single R (fun a =>
        R.mul ((psC (psRing (psRing R)) V) 0 k a)
          (in3Z R w j (k - k) (i - a)))
      i (i + 1) (by omega)
      (fun a _ hai => by
        show R.mul ((psC (psRing (psRing R)) V) 0 k a)
            (in3Z R w j (k - k) (i - a)) = R.zero
        rw [show in3Z R w j (k - k) (i - a) = R.zero from by
          show (if k - k = 0 then psC R (w j) else (psRing R).zero)
              (i - a) = R.zero
          rw [if_pos (Nat.sub_self k)]
          show (if i - a = 0 then w j else R.zero) = R.zero
          rw [if_neg (show ¬ i - a = 0 by omega)]]
        exact R.mul_zero _)
  rw [hinner,
    show (psC (psRing (psRing R)) V) 0 k i = V k i from
      congrFun (congrFun (if_pos rfl) k) i,
    show in3Z R w j (k - k) (i - i) = w j from by
      show (if k - k = 0 then psC R (w j) else (psRing R).zero)
          (i - i) = w j
      rw [if_pos (Nat.sub_self k)]
      exact if_pos (Nat.sub_self i)]

/-! ## 右辺の一変数化 -/

/-- **定理 (M65-5): 右辺の一変数化** — G(f(X), f(Y), f(Z))_{j,k,i}
    = Σ_{c,b,a} G_{c,b,a}·((f^a)_i·(f^b)_k)·(f^c)_j。係数因子が
    一変数 f の冪に落ち、M49/M59 の一変数機構（対角 π^a・対角下消滅）
    が直接適用できる。 -/
theorem lt3_rhs_coeff (R : CRing) (f : PS R) (G : PS3 R) (j k i : Nat) :
    ps3Comp3 R G (in3X R f) (in3Y R f) (in3Z R f) j k i
      = rsum R (fun c => rsum R (fun b => rsum R (fun a =>
          R.mul (G c b a)
            (R.mul (R.mul (psPow R f a i) (psPow R f b k))
              (psPow R f c j)))
          (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) := by
  show rsum R (fun c => rsum R (fun b => rsum R (fun a =>
      R.mul (G c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) (in3X R f) a)
            (psPow (psRing (psRing R)) (in3Y R f) b))
          (psPow (psRing (psRing R)) (in3Z R f) c)) j k i))
      (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1) = _
  exact rsum_congr R (i + k + j + 1) (fun c _ =>
    rsum_congr R (i + k + j + 1) (fun b _ =>
      rsum_congr R (i + k + j + 1) (fun a _ => by
        rw [in3X_pow R f a, in3Y_pow R f b, in3Z_pow R f c,
          in3X_mul_in3Y R (psPow R f a) (psPow R f b),
          ps3_constV_mul_inZ R
            (psMul (psRing R) (psC (psRing R) (psPow R f a))
              (psMap (psConstHom R) (psPow R f b)))
            (psPow R f c) j k i,
          inX_mul_inY R (psPow R f a) (psPow R f b) k i])))

end IUT
