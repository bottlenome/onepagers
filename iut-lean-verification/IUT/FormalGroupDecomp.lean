/-
  IUT/FormalGroupDecomp.lean — M58（形式群方程式の総次数分解: 形式群第八層）

  存在再帰の方程式 F_{j,i}·(pⁿ − p) = (既決定データ) を立てるための
  両辺の係数分解。

  * M58-1 `ps2Comp1_single_one` — **線形項の代入** (c·X)∘F = c·F
    （係数ごと、F₀₀ = 0。k = 1 への一点集中和）
  * M58-2 `lt2_lhs_decomp` — **左辺の分解** (f∘F)_{j,i} = π·F_{j,i}
    + (F^p)_{j,i}（f = pX + X^p の係数が k ∈ {1, p} に集中。
    第二項は M57 により総次数 ≤ i+j−1 の係数のみに依存）
  * M58-3 `inX_mul_inY` — **注入積の係数公式** (inX g · inY h)_{j,i}
    = g_i·h_j（二重 Cauchy 和が (k,l) = (0,i) に一点集中 —
    X 方向注入は第 0 行・Y 方向注入は第 0 列のみ非零）
  * M58-4 `lt2_rhs_coeff` — **右辺の一変数化** F(f(X), f(Y))_{j,i}
    = Σ_{b,a ≤ i+j} F_{b,a}·(f^a)_i·(f^b)_j（(fX)^a = inX(f^a)・
    (fY)^b = inY(f^b) と M58-3 の合流。係数因子 (f^a)_i は
    **一変数** ltPoly の冪 — M49 で建てた一変数機構（対角 π^a・
    下方消滅）がそのまま適用可能になる）

  ロードマップ: 次層で対角項 (a,b) = (i,j) の分離（係数 π^{i+j}）と
  総次数の係数再帰による存在。全て選択公理不使用。
-/
import IUT.FormalGroupCongr

namespace IUT

/-! ## 左辺の分解 -/

/-- **定理 (M58-1): 線形項の代入** — (c·X)∘F の係数 = c·F_{j,i}
    （F₀₀ = 0）。 -/
theorem ps2Comp1_single_one (R : CRing) (c : R.carrier) (F : PS2 R)
    (hF : F 0 0 = R.zero) :
    ∀ j i, ps2Comp1 R (psSingle R c 1) F j i = R.mul c (F j i) := by
  intro j i
  show rsum R (fun k => R.mul (psSingle R c 1 k)
      (psPow (psRing R) F k j i)) (i + j + 1) = R.mul c (F j i)
  cases Nat.decEq (i + j) 0 with
  | isTrue h0 =>
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi
    subst hj
    show R.add R.zero (R.mul (psSingle R c 1 0)
        (psPow (psRing R) F 0 0 0)) = R.mul c (F 0 0)
    rw [show psSingle R c 1 0 = R.zero from if_neg (by omega),
      R.zero_mul, hF, R.mul_zero]
    exact R.zero_add R.zero
  | isFalse h0 =>
    have hs : rsum R (fun k => R.mul (psSingle R c 1 k)
          (psPow (psRing R) F k j i)) (i + j + 1)
        = R.mul (psSingle R c 1 1) (psPow (psRing R) F 1 j i) :=
      rsum_single R _ 1 (i + j + 1) (by omega) (fun k _ hk => by
        rw [show psSingle R c 1 k = R.zero from if_neg hk]
        exact R.zero_mul _)
    rw [hs, show psSingle R c 1 1 = c from if_pos rfl, ps2Pow_one R F]

/-- **定理 (M58-2): 左辺の分解** — (f∘F)_{j,i} = π·F_{j,i} + (F^p)_{j,i}
    （f = pX + X^p、F₀₀ = 0。第二項は M57 により低次係数のみに依存）。 -/
theorem lt2_lhs_decomp (p : Nat) (F : PS2 (zpRing p))
    (hF : F 0 0 = (zpRing p).zero) (j i : Nat) :
    ps2Comp1 (zpRing p) (ltPoly p) F j i
      = (zpRing p).add
          ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) (F j i))
          (psPow (psRing (zpRing p)) F p j i) := by
  have h1 : ps2Comp1 (zpRing p) (ltPoly p) F j i
      = (zpRing p).add
          (ps2Comp1 (zpRing p)
            (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1) F j i)
          (ps2Comp1 (zpRing p) (psMono (zpRing p) p) F j i) :=
    congrFun (congrFun (ps2Comp1_add (zpRing p)
      (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1)
      (psMono (zpRing p) p) F) j) i
  rw [h1, ps2Comp1_single_one (zpRing p) _ F hF j i,
    ps2Comp1_mono (zpRing p) p F hF]

/-! ## 右辺の一変数化 -/

/-- **定理 (M58-3): 注入積の係数公式** — (inX g · inY h)_{j,i} = g_i·h_j
    （二重 Cauchy 和が (k,l) = (0,i) に一点集中）。 -/
theorem inX_mul_inY (R : CRing) (g h : PS R) (j i : Nat) :
    psMul (psRing R) (psC (psRing R) g) (psMap (psConstHom R) h) j i
      = R.mul (g i) (h j) := by
  rw [ps2Mul_coeff R (psC (psRing R) g) (psMap (psConstHom R) h) j i]
  have houter : rsum R (fun k => rsum R (fun l =>
        R.mul ((psC (psRing R) g) k l)
          ((psMap (psConstHom R) h) (j - k) (i - l))) (i + 1)) (j + 1)
      = rsum R (fun l => R.mul ((psC (psRing R) g) 0 l)
          ((psMap (psConstHom R) h) j (i - l))) (i + 1) :=
    rsum_single R _ 0 (j + 1) (by omega) (fun k _ hk => by
      have hz : ∀ l, l < i + 1 →
          R.mul ((psC (psRing R) g) k l)
            ((psMap (psConstHom R) h) (j - k) (i - l)) = R.zero :=
        fun l _ => by
          rw [show (psC (psRing R) g) k = (psRing R).zero from if_neg hk]
          exact R.zero_mul _
      have hc : rsum R (fun l => R.mul ((psC (psRing R) g) k l)
            ((psMap (psConstHom R) h) (j - k) (i - l))) (i + 1)
          = rsum R (fun _ => R.zero) (i + 1) :=
        rsum_congr R (i + 1) hz
      rw [hc]
      exact rsum_const_zero R (i + 1))
  rw [houter]
  have hinner : rsum R (fun l => R.mul ((psC (psRing R) g) 0 l)
        ((psMap (psConstHom R) h) j (i - l))) (i + 1)
      = R.mul ((psC (psRing R) g) 0 i) ((psMap (psConstHom R) h) j (i - i)) :=
    rsum_single R (fun l => R.mul ((psC (psRing R) g) 0 l)
        ((psMap (psConstHom R) h) j (i - l))) i (i + 1) (by omega)
      (fun l hl hne => by
        show R.mul ((psC (psRing R) g) 0 l)
            ((psMap (psConstHom R) h) j (i - l)) = R.zero
        rw [show (psMap (psConstHom R) h) j (i - l) = R.zero from
          if_neg (show ¬ i - l = 0 by omega)]
        exact R.mul_zero _)
  rw [hinner,
    show (psC (psRing R) g) 0 i = g i from congrFun (if_pos rfl) i,
    show (psMap (psConstHom R) h) j (i - i) = h j from
      if_pos (Nat.sub_self i)]

/-- **定理 (M58-4): 右辺の一変数化** — F(f(X), f(Y))_{j,i}
    = Σ_{b,a ≤ i+j} F_{b,a}·(f^a)_i·(f^b)_j。係数因子は一変数 f の冪
    なので、M49 の一変数機構（対角・下方消滅）が直接適用できる。 -/
theorem lt2_rhs_coeff (R : CRing) (f : PS R) (F : PS2 R) (j i : Nat) :
    ps2Comp2 R F (psC (psRing R) f) (psMap (psConstHom R) f) j i
      = rsum R (fun b => rsum R (fun a =>
          R.mul (F b a) (R.mul (psPow R f a i) (psPow R f b j)))
          (i + j + 1)) (i + j + 1) := by
  show rsum R (fun b => rsum R (fun a => R.mul (F b a)
      ((psMul (psRing R) (psPow (psRing R) (psC (psRing R) f) a)
        (psPow (psRing R) (psMap (psConstHom R) f) b)) j i))
      (i + j + 1)) (i + j + 1) = _
  exact rsum_congr R (i + j + 1) (fun b _ =>
    rsum_congr R (i + j + 1) (fun a _ => by
      have hP : psPow (psRing R) (psC (psRing R) f) a
          = psC (psRing R) (psPow R f a) := by
        rw [psPow_psC (psRing R) f a, ← psPow_eq_rpow R f a]
      have hQ : psPow (psRing R) (psMap (psConstHom R) f) b
          = psMap (psConstHom R) (psPow R f b) :=
        (psMap_pow (psConstHom R) f b).symm
      rw [hP, hQ, inX_mul_inY R (psPow R f a) (psPow R f b) j i]))

end IUT
