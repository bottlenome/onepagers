/-
  IUT/Frobenius2.lean — M55（二変数 Frobenius と LT 誤差の mod-p 消滅: 形式群第五層）

  標数 p の二変数 Frobenius 定理

    G^p = G(X^p, Y^p)   in (ℤ/p)[[X, Y]]

  を完全証明し、形式群方程式の **mod-p での自動成立**（= 誤差項の
  mod-p 消滅）を導く。これは M49 の一変数存在証明の心臓部
  （ltError_reduction）の二変数版であり、次層の係数再帰構成で
  「誤差を p で割る」ことを可能にする。

  証明の構造（一変数理論の二段重ね）:
  G ∈ PS2 R = PS(R[[X]]) を外側変数 Y の級数と見ると、係数環
  S = R[[X]] は標数 p（M54-6 遺伝）なので **M54 の一般化 Frobenius**
  G^p = (Frob_S G)∘Y^p が効き、係数側 Frobenius c ↦ c^p には
  **M47 の一変数 Frobenius**（ℤ/p 上）c^p = c∘X^p が効く。
  両者の合成で (G^p)_{pb, pa} = G_{b,a}・p 非整除指数では 0 が出る。

  * M55-1 `nat_le_mul_self` / `nat_not_dvd_of_div` — Nat 簿記
  * M55-2 `ps2Comp1_mono` — **X^m∘G = G^m**（G₀₀ = 0、総次数
    truncation M50 で打ち切りが正当化される）
  * M55-3 `ps2_powXY` — 座標冪の積 (X^m)^a·(Y^m)^b = X^{ma}Y^{mb}
    （M51 の psPow_psC・psMono_pow・ps2MonoXY の合流）
  * M55-4 `ps2Comp2_powXY_hit` / `_missX` / `_missY` —
    **G(X^m, Y^m) の係数公式**（(mb, ma) 係数 = G_{b,a}、
    m 非整除指数では 0。二重一点集中和）
  * M55-5 `ps2Pow_frob_hit` / `_missX` / `_missY` — **G^p の係数公式**
    （M54 外側 + M47 内側の二段適用）
  * M55-6 `frobenius2_charp` — **二変数 Frobenius 定理**:
    G₀₀ = 0 なる任意の G ∈ PS2(ℤ/p) は還元方程式
    X^p∘G = G(X^p, Y^p) を満たす（M53-6 が LT 形式群の還元に
    強制する方程式が、実は無条件に成立することの機械検証）
  * M55-7 `lt_error_vanishes_modp` — **LT 誤差の mod-p 消滅**:
    任意の F ∈ PS2(ℤ_p)（F₀₀ = 0）で形式群方程式の両辺は
    mod p で一致する（M53 の移送 + ltPoly_reduction + M55-6）。
    係数ごとの p-整除性（次層で zp_dvd_p_iff に接続）の源泉

  ロードマップ: 次層で誤差の係数 p-整除性 → 総次数の係数再帰による
  LT 形式群法則の存在。全て選択公理不使用。
-/
import IUT.FrobeniusGen

namespace IUT

/-! ## Nat 簿記 -/

/-- **M55-1a**: b ≤ m·b（m ≥ 1）。 -/
theorem nat_le_mul_self (m b : Nat) (hm : 1 ≤ m) : b ≤ m * b := by
  have h : 1 * b ≤ m * b := Nat.mul_le_mul_right b hm
  rw [Nat.one_mul] at h
  exact h

/-- **M55-1b**: p·(j/p) ≠ j なら p ∤ j（整除判定の決定手続き）。 -/
theorem nat_not_dvd_of_div (p j : Nat) (h : p * (j / p) ≠ j) : ¬ p ∣ j :=
  fun hd => h (Nat.mul_div_cancel' hd)

/-! ## X^m∘G = G^m -/

/-- **定理 (M55-2): 単項式の 1→2 変数代入は冪** — X^m∘G = G^m
    （G₀₀ = 0 のとき。m > i+j の係数は両辺とも総次数 truncation
    （M50-3）で消滅）。 -/
theorem ps2Comp1_mono (R : CRing) (m : Nat)
    (G : PS2 R) (hG : G 0 0 = R.zero) :
    ps2Comp1 R (psMono R m) G = psPow (psRing R) G m := by
  funext j i
  show rsum R (fun k => R.mul (psMono R m k) (psPow (psRing R) G k j i))
      (i + j + 1) = psPow (psRing R) G m j i
  cases Nat.lt_or_ge (i + j) m with
  | inl h =>
    have hz : rsum R (fun k => R.mul (psMono R m k)
          (psPow (psRing R) G k j i)) (i + j + 1)
        = rsum R (fun _ => R.zero) (i + j + 1) :=
      rsum_congr R (i + j + 1) (fun k hk => by
        rw [show psMono R m k = R.zero from if_neg (by omega)]
        exact R.zero_mul _)
    rw [hz, rsum_const_zero, ps2Pow_tcoeff_zero R G hG m i j h]
  | inr h =>
    have hs : rsum R (fun k => R.mul (psMono R m k)
          (psPow (psRing R) G k j i)) (i + j + 1)
        = R.mul (psMono R m m) (psPow (psRing R) G m j i) :=
      rsum_single R _ m (i + j + 1) (by omega) (fun k _ hk => by
        rw [show psMono R m k = R.zero from if_neg hk]
        exact R.zero_mul _)
    rw [hs, show psMono R m m = R.one from if_pos rfl]
    exact R.one_mul _

/-! ## 座標冪の積と G(X^m, Y^m) の係数公式 -/

/-- **M55-3: 座標冪の積** (X^m)^a·(Y^m)^b = X^{ma}·Y^{mb}
    （二変数単項式 δ）。 -/
theorem ps2_powXY (R : CRing) (m a b : Nat) :
    psMul (psRing R)
      (psPow (psRing R) (psC (psRing R) (psMono R m)) a)
      (psPow (psRing R) (psMono (psRing R) m) b)
    = ps2Mono R (m * a) (m * b) := by
  have hP : psPow (psRing R) (psC (psRing R) (psMono R m)) a
      = psC (psRing R) (psMono R (m * a)) := by
    rw [psPow_psC (psRing R) (psMono R m) a,
      ← psPow_eq_rpow R (psMono R m) a, psMono_pow R m a]
  have hQ : psPow (psRing R) (psMono (psRing R) m) b
      = psMono (psRing R) (m * b) := psMono_pow (psRing R) m b
  rw [hP, hQ, ← ps2X_pow R (m * a), ← ps2Y_pow R (m * b)]
  exact ps2MonoXY R (m * a) (m * b)

/-- **定理 (M55-4a): G(X^m, Y^m) の対角係数** —
    (m·b, m·a) 係数 = G_{b,a}（二重一点集中和、m ≥ 1）。 -/
theorem ps2Comp2_powXY_hit (R : CRing) (m : Nat) (hm : 1 ≤ m)
    (G : PS2 R) (b a : Nat) :
    ps2Comp2 R G (psC (psRing R) (psMono R m)) (psMono (psRing R) m)
      (m * b) (m * a) = G b a := by
  have hm0 : 0 < m := hm
  have hterm : ∀ b' a',
      (psMul (psRing R)
        (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
        (psPow (psRing R) (psMono (psRing R) m) b')) (m * b) (m * a)
      = ps2Mono R (m * a') (m * b') (m * b) (m * a) :=
    fun b' a' => congrFun (congrFun (ps2_powXY R m a' b') (m * b)) (m * a)
  show rsum R (fun b' => rsum R (fun a' => R.mul (G b' a')
      ((psMul (psRing R)
        (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
        (psPow (psRing R) (psMono (psRing R) m) b')) (m * b) (m * a)))
      (m * a + m * b + 1)) (m * a + m * b + 1) = G b a
  have hb : b < m * a + m * b + 1 :=
    Nat.lt_succ_of_le (Nat.le_trans (nat_le_mul_self m b hm)
      (Nat.le_add_left (m * b) (m * a)))
  have ha : a < m * a + m * b + 1 :=
    Nat.lt_succ_of_le (Nat.le_trans (nat_le_mul_self m a hm)
      (Nat.le_add_right (m * a) (m * b)))
  have houter : rsum R (fun b' => rsum R (fun a' => R.mul (G b' a')
      ((psMul (psRing R)
        (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
        (psPow (psRing R) (psMono (psRing R) m) b')) (m * b) (m * a)))
      (m * a + m * b + 1)) (m * a + m * b + 1)
      = rsum R (fun a' => R.mul (G b a')
          ((psMul (psRing R)
            (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
            (psPow (psRing R) (psMono (psRing R) m) b)) (m * b) (m * a)))
          (m * a + m * b + 1) :=
    rsum_single R _ b (m * a + m * b + 1) hb (fun b' _ hb' => by
      have hz : ∀ a', a' < m * a + m * b + 1 →
          R.mul (G b' a')
            ((psMul (psRing R)
              (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
              (psPow (psRing R) (psMono (psRing R) m) b')) (m * b) (m * a))
          = R.zero := fun a' _ => by
        rw [hterm b' a',
          show ps2Mono R (m * a') (m * b') (m * b) (m * a) = R.zero from
            if_neg (fun h => hb' (Nat.eq_of_mul_eq_mul_left hm0 h).symm)]
        exact R.mul_zero _
      have hc : rsum R (fun a' => R.mul (G b' a')
            ((psMul (psRing R)
              (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
              (psPow (psRing R) (psMono (psRing R) m) b')) (m * b) (m * a)))
            (m * a + m * b + 1)
          = rsum R (fun _ => R.zero) (m * a + m * b + 1) :=
        rsum_congr R (m * a + m * b + 1) hz
      rw [hc]
      exact rsum_const_zero R (m * a + m * b + 1))
  have hinner : rsum R (fun a' => R.mul (G b a')
        ((psMul (psRing R)
          (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
          (psPow (psRing R) (psMono (psRing R) m) b)) (m * b) (m * a)))
        (m * a + m * b + 1)
      = R.mul (G b a)
          ((psMul (psRing R)
            (psPow (psRing R) (psC (psRing R) (psMono R m)) a)
            (psPow (psRing R) (psMono (psRing R) m) b)) (m * b) (m * a)) :=
    rsum_single R _ a (m * a + m * b + 1) ha (fun a' _ ha' => by
      rw [hterm b a',
        show ps2Mono R (m * a') (m * b) (m * b) (m * a) = R.zero from by
          show (if m * b = m * b
              then (if m * a = m * a' then R.one else R.zero)
              else R.zero) = R.zero
          rw [if_pos rfl]
          exact if_neg (fun h => ha' (Nat.eq_of_mul_eq_mul_left hm0 h).symm)]
      exact R.mul_zero _)
  rw [houter, hinner, hterm b a,
    show ps2Mono R (m * a) (m * b) (m * b) (m * a) = R.one from by
      show (if m * b = m * b
          then (if m * a = m * a then R.one else R.zero)
          else R.zero) = R.one
      rw [if_pos rfl, if_pos rfl]]
  exact CRing.mul_one R (G b a)

/-- **定理 (M55-4b): Y 指数が m 非整除なら 0**。 -/
theorem ps2Comp2_powXY_missY (R : CRing) (m : Nat) (G : PS2 R)
    (j i : Nat) (hj : ∀ b', j ≠ m * b') :
    ps2Comp2 R G (psC (psRing R) (psMono R m)) (psMono (psRing R) m)
      j i = R.zero := by
  show rsum R (fun b' => rsum R (fun a' => R.mul (G b' a')
      ((psMul (psRing R)
        (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
        (psPow (psRing R) (psMono (psRing R) m) b')) j i))
      (i + j + 1)) (i + j + 1) = R.zero
  have hz : ∀ b', b' < i + j + 1 →
      rsum R (fun a' => R.mul (G b' a')
        ((psMul (psRing R)
          (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
          (psPow (psRing R) (psMono (psRing R) m) b')) j i))
        (i + j + 1) = R.zero := fun b' _ => by
    have hz2 : ∀ a', a' < i + j + 1 →
        R.mul (G b' a')
          ((psMul (psRing R)
            (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
            (psPow (psRing R) (psMono (psRing R) m) b')) j i)
        = R.zero := fun a' _ => by
      rw [congrFun (congrFun (ps2_powXY R m a' b') j) i]
      show R.mul (G b' a')
          (if j = m * b'
            then (if i = m * a' then R.one else R.zero)
            else R.zero) = R.zero
      rw [if_neg (hj b')]
      exact R.mul_zero _
    have hc : rsum R (fun a' => R.mul (G b' a')
          ((psMul (psRing R)
            (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
            (psPow (psRing R) (psMono (psRing R) m) b')) j i))
          (i + j + 1)
        = rsum R (fun _ => R.zero) (i + j + 1) :=
      rsum_congr R (i + j + 1) hz2
    rw [hc]
    exact rsum_const_zero R (i + j + 1)
  have hc2 : rsum R (fun b' => rsum R (fun a' => R.mul (G b' a')
        ((psMul (psRing R)
          (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
          (psPow (psRing R) (psMono (psRing R) m) b')) j i))
        (i + j + 1)) (i + j + 1)
      = rsum R (fun _ => R.zero) (i + j + 1) :=
    rsum_congr R (i + j + 1) hz
  rw [hc2]
  exact rsum_const_zero R (i + j + 1)

/-- **定理 (M55-4c): X 指数が m 非整除なら 0**。 -/
theorem ps2Comp2_powXY_missX (R : CRing) (m : Nat) (G : PS2 R)
    (j i : Nat) (hi : ∀ a', i ≠ m * a') :
    ps2Comp2 R G (psC (psRing R) (psMono R m)) (psMono (psRing R) m)
      j i = R.zero := by
  show rsum R (fun b' => rsum R (fun a' => R.mul (G b' a')
      ((psMul (psRing R)
        (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
        (psPow (psRing R) (psMono (psRing R) m) b')) j i))
      (i + j + 1)) (i + j + 1) = R.zero
  have hz : ∀ b', b' < i + j + 1 →
      rsum R (fun a' => R.mul (G b' a')
        ((psMul (psRing R)
          (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
          (psPow (psRing R) (psMono (psRing R) m) b')) j i))
        (i + j + 1) = R.zero := fun b' _ => by
    have hz2 : ∀ a', a' < i + j + 1 →
        R.mul (G b' a')
          ((psMul (psRing R)
            (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
            (psPow (psRing R) (psMono (psRing R) m) b')) j i)
        = R.zero := fun a' _ => by
      rw [congrFun (congrFun (ps2_powXY R m a' b') j) i]
      show R.mul (G b' a')
          (if j = m * b'
            then (if i = m * a' then R.one else R.zero)
            else R.zero) = R.zero
      cases Nat.decEq j (m * b') with
      | isTrue h =>
        rw [if_pos h, if_neg (hi a')]
        exact R.mul_zero _
      | isFalse h =>
        rw [if_neg h]
        exact R.mul_zero _
    have hc : rsum R (fun a' => R.mul (G b' a')
          ((psMul (psRing R)
            (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
            (psPow (psRing R) (psMono (psRing R) m) b')) j i))
          (i + j + 1)
        = rsum R (fun _ => R.zero) (i + j + 1) :=
      rsum_congr R (i + j + 1) hz2
    rw [hc]
    exact rsum_const_zero R (i + j + 1)
  have hc2 : rsum R (fun b' => rsum R (fun a' => R.mul (G b' a')
        ((psMul (psRing R)
          (psPow (psRing R) (psC (psRing R) (psMono R m)) a')
          (psPow (psRing R) (psMono (psRing R) m) b')) j i))
        (i + j + 1)) (i + j + 1)
      = rsum R (fun _ => R.zero) (i + j + 1) :=
    rsum_congr R (i + j + 1) hz
  rw [hc2]
  exact rsum_const_zero R (i + j + 1)

/-! ## G^p の係数公式（M54 外側 + M47 内側の二段適用） -/

/-- **定理 (M55-5a): G^p の対角係数** — (G^p)_{pb, pa} = G_{b,a}
    in PS2(ℤ/p)。外側（Y）は M54 の一般化 Frobenius、内側（X）は
    M47 の Frobenius。 -/
theorem ps2Pow_frob_hit (p : Nat) (hp : IsPrime p)
    (G : PS2 (zmodRing (p ^ 1))) (b a : Nat) :
    psPow (psRing (zmodRing (p ^ 1))) G p (p * b) (p * a) = G b a := by
  have hp1 : 1 ≤ p := by have := hp.1; omega
  have hchar : rofNat (psRing (zmodRing (p ^ 1))) p
      = (psRing (zmodRing (p ^ 1))).zero :=
    psRing_char (zmodRing (p ^ 1)) p (zmod_char p)
  have h1 := frobenius_charp_gen (psRing (zmodRing (p ^ 1))) p hp hchar G
  have h3 : psPow (psRing (zmodRing (p ^ 1))) G p (p * b)
      = rpow (psRing (zmodRing (p ^ 1))) (G b) p :=
    (congrFun h1 (p * b)).trans
      (psComp_mono_coeff (psRing (zmodRing (p ^ 1)))
        (psMap (frobHom (psRing (zmodRing (p ^ 1))) p hp hchar) G) p b hp1)
  have h4 : psPow (psRing (zmodRing (p ^ 1))) G p (p * b) (p * a)
      = rpow (psRing (zmodRing (p ^ 1))) (G b) p (p * a) :=
    congrFun h3 (p * a)
  rw [h4, ← psPow_eq_rpow (zmodRing (p ^ 1)) (G b) p,
    frobenius_charp p hp (G b)]
  exact psComp_mono_coeff (zmodRing (p ^ 1)) (G b) p a hp1

/-- **定理 (M55-5b): Y 指数が p 非整除なら 0**。 -/
theorem ps2Pow_frob_missY (p : Nat) (hp : IsPrime p)
    (G : PS2 (zmodRing (p ^ 1))) (j i : Nat) (hj : ¬ p ∣ j) :
    psPow (psRing (zmodRing (p ^ 1))) G p j i
      = (zmodRing (p ^ 1)).zero := by
  have hchar : rofNat (psRing (zmodRing (p ^ 1))) p
      = (psRing (zmodRing (p ^ 1))).zero :=
    psRing_char (zmodRing (p ^ 1)) p (zmod_char p)
  have h1 := frobenius_charp_gen (psRing (zmodRing (p ^ 1))) p hp hchar G
  have h3 : psPow (psRing (zmodRing (p ^ 1))) G p j
      = psZero (zmodRing (p ^ 1)) :=
    (congrFun h1 j).trans
      (psComp_mono_coeff_zero (psRing (zmodRing (p ^ 1)))
        (psMap (frobHom (psRing (zmodRing (p ^ 1))) p hp hchar) G) p j hj)
  exact congrFun h3 i

/-- **定理 (M55-5c): X 指数が p 非整除なら 0**。 -/
theorem ps2Pow_frob_missX (p : Nat) (hp : IsPrime p)
    (G : PS2 (zmodRing (p ^ 1))) (b i : Nat) (hi : ¬ p ∣ i) :
    psPow (psRing (zmodRing (p ^ 1))) G p (p * b) i
      = (zmodRing (p ^ 1)).zero := by
  have hp1 : 1 ≤ p := by have := hp.1; omega
  have hchar : rofNat (psRing (zmodRing (p ^ 1))) p
      = (psRing (zmodRing (p ^ 1))).zero :=
    psRing_char (zmodRing (p ^ 1)) p (zmod_char p)
  have h1 := frobenius_charp_gen (psRing (zmodRing (p ^ 1))) p hp hchar G
  have h3 : psPow (psRing (zmodRing (p ^ 1))) G p (p * b)
      = rpow (psRing (zmodRing (p ^ 1))) (G b) p :=
    (congrFun h1 (p * b)).trans
      (psComp_mono_coeff (psRing (zmodRing (p ^ 1)))
        (psMap (frobHom (psRing (zmodRing (p ^ 1))) p hp hchar) G) p b hp1)
  have h4 : psPow (psRing (zmodRing (p ^ 1))) G p (p * b) i
      = rpow (psRing (zmodRing (p ^ 1))) (G b) p i :=
    congrFun h3 i
  rw [h4, ← psPow_eq_rpow (zmodRing (p ^ 1)) (G b) p,
    frobenius_charp p hp (G b)]
  exact psComp_mono_coeff_zero (zmodRing (p ^ 1)) (G b) p i hi

/-! ## 二変数 Frobenius 定理 -/

/-- **定理 (M55-6): 二変数 Frobenius 定理（標数 p）** —
    G₀₀ = 0 なる任意の G ∈ PS2(ℤ/p) は X^p∘G = G(X^p, Y^p) を満たす。
    すなわち M53-6 が LT 形式群の mod-p 還元に強制する方程式は、
    標数 p では**無条件に**成立する（誤差の消滅の源泉）。 -/
theorem frobenius2_charp (p : Nat) (hp : IsPrime p)
    (G : PS2 (zmodRing (p ^ 1)))
    (hG : G 0 0 = (zmodRing (p ^ 1)).zero) :
    ps2Comp1 (zmodRing (p ^ 1)) (psMono (zmodRing (p ^ 1)) p) G
      = ps2Comp2 (zmodRing (p ^ 1)) G
          (psC (psRing (zmodRing (p ^ 1))) (psMono (zmodRing (p ^ 1)) p))
          (psMap (psConstHom (zmodRing (p ^ 1)))
            (psMono (zmodRing (p ^ 1)) p)) := by
  have hp1 : 1 ≤ p := by have := hp.1; omega
  rw [ps2Comp1_mono (zmodRing (p ^ 1)) p G hG,
    psMap_mono (psConstHom (zmodRing (p ^ 1))) p]
  funext j i
  cases Nat.decEq (p * (j / p)) j with
  | isTrue hjd =>
    cases Nat.decEq (p * (i / p)) i with
    | isTrue hid =>
      rw [← hjd, ← hid]
      exact (ps2Pow_frob_hit p hp G (j / p) (i / p)).trans
        (ps2Comp2_powXY_hit (zmodRing (p ^ 1)) p hp1 G (j / p) (i / p)).symm
    | isFalse hid =>
      have hi : ¬ p ∣ i := nat_not_dvd_of_div p i hid
      rw [← hjd, ps2Pow_frob_missX p hp G (j / p) i hi,
        ps2Comp2_powXY_missX (zmodRing (p ^ 1)) p G (p * (j / p)) i
          (fun a' h => hi ⟨a', h⟩)]
  | isFalse hjd =>
    have hj : ¬ p ∣ j := nat_not_dvd_of_div p j hjd
    rw [ps2Pow_frob_missY p hp G j i hj,
      ps2Comp2_powXY_missY (zmodRing (p ^ 1)) p G j i
        (fun b' h => hj ⟨b', h⟩)]

/-! ## LT 誤差の mod-p 消滅 -/

/-- **定理 (M55-7a): LT 誤差の mod-p 消滅** — 任意の F ∈ PS2(ℤ_p)
    （F̄₀₀ = 0）で形式群方程式 f∘F = F(f(X), f(Y))（f = pX + X^p）の
    両辺は mod p で一致する（M53 の移送 + M48 の f̄ = X^p + M55-6）。
    次層の係数 p-整除性（誤差/p の構成）の源泉。 -/
theorem lt_error_vanishes_modp (p : Nat) (hp : IsPrime p)
    (F : PS2 (zpRing p))
    (hF : ps2Map (projRing p 1) F 0 0 = (zmodRing (p ^ 1)).zero) :
    ps2Map (projRing p 1) (ps2Comp1 (zpRing p) (ltPoly p) F)
      = ps2Map (projRing p 1) (ps2Comp2 (zpRing p) F
          (psC (psRing (zpRing p)) (ltPoly p))
          (psMap (psConstHom (zpRing p)) (ltPoly p))) := by
  rw [ps2Map_comp1 (projRing p 1) (ltPoly p) F,
    ps2Map_comp2 (projRing p 1) F _ _,
    ps2Map_psC (projRing p 1) (ltPoly p),
    ps2Map_inY (projRing p 1) (ltPoly p),
    ltPoly_reduction p]
  exact frobenius2_charp p hp (ps2Map (projRing p 1) F) hF

/-- **定理 (M55-7b): F₀₀ = 0（ℤ_p レベル）からの導出形**。 -/
theorem lt_error_vanishes_modp' (p : Nat) (hp : IsPrime p)
    (F : PS2 (zpRing p)) (hF0 : F 0 0 = (zpRing p).zero) :
    ps2Map (projRing p 1) (ps2Comp1 (zpRing p) (ltPoly p) F)
      = ps2Map (projRing p 1) (ps2Comp2 (zpRing p) F
          (psC (psRing (zpRing p)) (ltPoly p))
          (psMap (psConstHom (zpRing p)) (ltPoly p))) :=
  lt_error_vanishes_modp p hp F (by
    show (projRing p 1).map (F 0 0) = (zmodRing (p ^ 1)).zero
    rw [hF0]
    exact RingHom.map_zero (projRing p 1))

end IUT
