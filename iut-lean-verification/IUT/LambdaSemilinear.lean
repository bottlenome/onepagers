/-
  IUT/LambdaSemilinear.lean — M106（柱B B-1 第二段: [c]-作用の半線形性と
  Galois 同変性）

  M105 で λ 上の [c]-倍作用 [c]λ = ltSol(c) mod E を構成した。本モジュールは
  **[c] 級数の dilation 恒等式**

    [c](zX) = z·[c](X)  （z^{p−1} = 1）

  を Lubin–Tate 補題（M49）の一意性だけで機械検証し、その帰結として

    σ_ζ([c]λ) = ζ·[c]λ  （Galois 作用 M86F は [c]-作用と可換 = 同変）
    [c](ω(a)λ) = ω(a)·[c]λ  （共役族 M84F 上の半線形性）

  を得る。M89F-6 は「f の半線形性」止まりだったが、これで **ℤ_p-作用
  全体が μ_{p−1}-同変**になり、Λ₁ = {0} ∪ {ω(a)λ}（M97F）の全点で
  [c]-作用が確定する（Λ₁ の ℤ_p[Gal]-加群構造の完成）。

  証明の設計（係数の台の性質を経由しない）: W := [c]∘(zX) と
  W' := z·[c] の両方が LT 方程式 F∘f = πF + F^p を満たし
  F(0) = 0・F(1) = zc を共有することを示し、一意性で W = W'。
  W 側は (zX)∘f = z·f = f∘(zX)（z^p = z による f の dilation 恒等式）で
  f を通り抜けさせ、W' 側は smul の簿記のみ。

  * M106-1 `psSingle_mul_single` / `psSingleOne_pow` — 単項式の積・冪
    （一点集中 Cauchy 和）
  * M106-2 `psScale_eq_comp` — **psScale = 右合成**: S∘(zX) = scale_z S
    （M86F の Galois 作用の実体が dilation 合成であることの同定）
  * M106-3 `psComp_smul_left` / `psSmul_add` / `psSmul_swap` /
    `psPow_smul` — smul の簿記（合成・加法・交換・冪との分配）
  * M106-4 `ltPoly_dilate` — **f∘(zX) = z·f**（z^p = z。f の dilation
    恒等式、M84F eisF_semilinear の級数版）
  * M106-5 `rpow_fixed_of_root` — z^{p−1} = 1 ⟹ z^p = z
  * M106-6 `ltSol_dilate` — **本丸: [c]∘(zX) = z·[c]**（一意性）
  * M106-7 `psScale_ltSol` / `psSmul_eq_psC_mul` — psScale 形への
    読み替えと psC 積形への橋
  * M106-8 `eisAut_eisBr` — **Galois 同変性**: σ_ζ([c]λ) = ζ·[c]λ
  * M106-9 `eisBr_conj_scale` / `zpPow_eq_rpow_zp` /
    `eisAut_teich_eisBr` — **共役族での半線形性**: [c](ω(a)λ) =
    ω(a)·[c]λ（teich の 1 の冪根性 M34-5 を rpow に橋渡しして適用）

  未形式化（正直申告）: [c]-作用の O の一般点への拡張（O の完備性 =
  p 進級数和）・Λₙ(n ≥ 2) の塔の環構成は次層以降（B-1 残り）。
  全て選択公理不使用。
-/
import IUT.LambdaModule
import IUT.EisensteinGalois
import IUT.CyclicUnits

namespace IUT

/-! ## 単項式の積・冪 -/

/-- **M106-1a: 単項式の積** — single(a,i)·single(b,j) = single(ab, i+j)
    （Cauchy 和の一点集中）。 -/
theorem psSingle_mul_single (R : CRing) (a b : R.carrier) (i j : Nat) :
    psMul R (psSingle R a i) (psSingle R b j)
      = psSingle R (R.mul a b) (i + j) := by
  funext n
  show rsum R (fun k => R.mul (psSingle R a i k) (psSingle R b j (n - k)))
      (n + 1)
    = psSingle R (R.mul a b) (i + j) n
  cases Nat.decEq n (i + j) with
  | isTrue h =>
    have hs : rsum R (fun k =>
          R.mul (psSingle R a i k) (psSingle R b j (n - k))) (n + 1)
        = R.mul (psSingle R a i i) (psSingle R b j (n - i)) :=
      rsum_single R _ i (n + 1) (by omega) (fun k _ hk => by
        rw [show psSingle R a i k = R.zero from if_neg hk]
        exact R.zero_mul _)
    rw [hs, show psSingle R a i i = a from if_pos rfl,
      show psSingle R b j (n - i) = b from if_pos (by omega),
      show psSingle R (R.mul a b) (i + j) n = R.mul a b from if_pos h]
  | isFalse h =>
    have hz : rsum R (fun k =>
          R.mul (psSingle R a i k) (psSingle R b j (n - k))) (n + 1)
        = rsum R (fun _ => R.zero) (n + 1) := by
      apply rsum_congr
      intro k hk
      cases Nat.decEq k i with
      | isTrue hki =>
        rw [show psSingle R b j (n - k) = R.zero from if_neg (by omega)]
        exact CRing.mul_zero R _
      | isFalse hki =>
        rw [show psSingle R a i k = R.zero from if_neg hki]
        exact R.zero_mul _
    rw [hz, rsum_const_zero R (n + 1),
      show psSingle R (R.mul a b) (i + j) n = R.zero from if_neg h]

/-- **M106-1b: 一次単項式の冪** — (zX)^k = z^k·X^k（single 形）。 -/
theorem psSingleOne_pow (R : CRing) (z : R.carrier) : ∀ k,
    psPow R (psSingle R z 1) k = psSingle R (rpow R z k) k := by
  intro k
  induction k with
  | zero =>
    funext n
    rfl
  | succ k ih =>
    show psMul R (psPow R (psSingle R z 1) k) (psSingle R z 1)
      = psSingle R (rpow R z (k + 1)) (k + 1)
    rw [ih, psSingle_mul_single R (rpow R z k) z k 1]
    rfl

/-! ## psScale = 右合成 -/

/-- **定理 (M106-2): psScale = 右合成** — S∘(zX) = scale_z S
    （M86F の Galois 作用の実体が dilation 合成であることの同定。
    S の条件なし）。 -/
theorem psScale_eq_comp (R : CRing) (S : PS R) (z : R.carrier) :
    psComp R S (psSingle R z 1) = psScale R z S := by
  funext n
  show rsum R (fun k => R.mul (S k) (psPow R (psSingle R z 1) k n)) (n + 1)
    = R.mul (rpow R z n) (S n)
  have hc : rsum R (fun k =>
        R.mul (S k) (psPow R (psSingle R z 1) k n)) (n + 1)
      = rsum R (fun k => R.mul (S k) (psSingle R (rpow R z k) k n)) (n + 1) :=
    rsum_congr R (n + 1) (fun k _ => by rw [psSingleOne_pow R z k])
  rw [hc]
  have hs : rsum R (fun k =>
        R.mul (S k) (psSingle R (rpow R z k) k n)) (n + 1)
      = R.mul (S n) (psSingle R (rpow R z n) n n) :=
    rsum_single R _ n (n + 1) (by omega) (fun k _ hk => by
      rw [show psSingle R (rpow R z k) k n = R.zero from if_neg
        (fun hnk => hk hnk.symm)]
      exact CRing.mul_zero R _)
  rw [hs, show psSingle R (rpow R z n) n n = rpow R z n from if_pos rfl]
  exact R.mul_comm _ _

/-! ## smul の簿記 -/

/-- **M106-3a: smul は左合成と可換** — (c·P)∘Q = c·(P∘Q)。 -/
theorem psComp_smul_left (R : CRing) (c : R.carrier) (P Q : PS R) :
    psComp R (psSmul R c P) Q = psSmul R c (psComp R P Q) := by
  funext n
  show rsum R (fun k => R.mul (R.mul c (P k)) (psPow R Q k n)) (n + 1)
    = R.mul c (rsum R (fun k => R.mul (P k) (psPow R Q k n)) (n + 1))
  have hc : rsum R (fun k =>
        R.mul (R.mul c (P k)) (psPow R Q k n)) (n + 1)
      = rsum R (fun k => R.mul c (R.mul (P k) (psPow R Q k n))) (n + 1) :=
    rsum_congr R (n + 1) (fun k _ => R.mul_assoc c (P k) _)
  rw [hc]
  exact (rsum_mul_left R _ c (n + 1)).symm

/-- **M106-3b**: smul は加法と分配。 -/
theorem psSmul_add (R : CRing) (c : R.carrier) (F G : PS R) :
    psSmul R c (psAdd R F G) = psAdd R (psSmul R c F) (psSmul R c G) := by
  funext n
  exact R.left_distrib c (F n) (G n)

/-- **M106-3c**: smul どうしは交換。 -/
theorem psSmul_swap (R : CRing) (c d : R.carrier) (F : PS R) :
    psSmul R c (psSmul R d F) = psSmul R d (psSmul R c F) := by
  funext n
  show R.mul c (R.mul d (F n)) = R.mul d (R.mul c (F n))
  rw [← R.mul_assoc, R.mul_comm c d, R.mul_assoc]

/-- **M106-3d: smul と冪** — (c·F)^k = c^k·F^k。 -/
theorem psPow_smul (R : CRing) (c : R.carrier) (F : PS R) : ∀ k,
    psPow R (psSmul R c F) k = psSmul R (rpow R c k) (psPow R F k) := by
  intro k
  induction k with
  | zero =>
    funext n
    show psOne R n = R.mul (R.one) (psOne R n)
    rw [R.one_mul]
  | succ k ih =>
    show psMul R (psPow R (psSmul R c F) k) (psSmul R c F)
      = psSmul R (rpow R c (k + 1)) (psPow R F (k + 1))
    rw [ih]
    funext n
    show rsum R (fun j => R.mul (R.mul (rpow R c k) (psPow R F k j))
        (R.mul c (F (n - j)))) (n + 1)
      = R.mul (R.mul (rpow R c k) c)
          (rsum R (fun j => R.mul (psPow R F k j) (F (n - j))) (n + 1))
    have hc : rsum R (fun j => R.mul (R.mul (rpow R c k) (psPow R F k j))
          (R.mul c (F (n - j)))) (n + 1)
        = rsum R (fun j => R.mul (R.mul (rpow R c k) c)
            (R.mul (psPow R F k j) (F (n - j)))) (n + 1) :=
      rsum_congr R (n + 1) (fun j _ =>
        CRing.mul_mul_mul_comm R (rpow R c k) (psPow R F k j) c (F (n - j)))
    rw [hc]
    exact (rsum_mul_left R _ (R.mul (rpow R c k) c) (n + 1)).symm

/-! ## f の dilation 恒等式 -/

/-- **M106-5: 冪根の固定性** — z^{p−1} = 1 なら z^p = z。 -/
theorem rpow_fixed_of_root (p : Nat) (hp : 2 ≤ p) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) :
    rpow (zpRing p) z p = z := by
  have he : rpow (zpRing p) z p = rpow (zpRing p) z (p - 1 + 1) :=
    congrArg (rpow (zpRing p) z) (by omega)
  rw [he]
  show (zpRing p).mul (rpow (zpRing p) z (p - 1)) z = z
  rw [hz]
  exact (zpRing p).one_mul z

/-- **定理 (M106-4): f の dilation 恒等式** — f∘(zX) = z·f（z^p = z。
    f(zx) = πzx + z^p x^p = z·f(x) の級数形、M84F eisF_semilinear の
    級数版）。 -/
theorem ltPoly_dilate (p : Nat) (hp : 2 ≤ p) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z p = z) :
    psComp (zpRing p) (ltPoly p) (psSingle (zpRing p) z 1)
      = psSmul (zpRing p) z (ltPoly p) := by
  have h0 : psSingle (zpRing p) z 1 0 = (zpRing p).zero :=
    if_neg (by omega)
  rw [psComp_ltPoly_left p hp (psSingle (zpRing p) z 1) h0,
    psSingleOne_pow (zpRing p) z p, hz]
  funext n
  show (zpRing p).add
      ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
        (psSingle (zpRing p) z 1 n))
      (psSingle (zpRing p) z p n)
    = (zpRing p).mul z
      ((zpRing p).add
        (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1 n)
        (psMono (zpRing p) p n))
  cases Nat.decEq n 1 with
  | isTrue h1 =>
    rw [show psSingle (zpRing p) z 1 n = z from if_pos h1,
      show psSingle (zpRing p) z p n = (zpRing p).zero from if_neg (by omega),
      show psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1 n
        = (toZp p).map ((p : Nat) : Int) from if_pos h1,
      show psMono (zpRing p) p n = (zpRing p).zero from if_neg (by omega),
      CRing.add_zero (zpRing p), CRing.add_zero (zpRing p)]
    exact (zpRing p).mul_comm _ z
  | isFalse h1 =>
    cases Nat.decEq n p with
    | isTrue hpn =>
      rw [show psSingle (zpRing p) z 1 n = (zpRing p).zero from if_neg h1,
        show psSingle (zpRing p) z p n = z from if_pos hpn,
        show psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1 n
          = (zpRing p).zero from if_neg h1,
        show psMono (zpRing p) p n = (zpRing p).one from if_pos hpn,
        CRing.mul_zero (zpRing p), (zpRing p).zero_add,
        (zpRing p).zero_add, CRing.mul_one (zpRing p)]
    | isFalse hpn =>
      rw [show psSingle (zpRing p) z 1 n = (zpRing p).zero from if_neg h1,
        show psSingle (zpRing p) z p n = (zpRing p).zero from if_neg hpn,
        show psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1 n
          = (zpRing p).zero from if_neg h1,
        show psMono (zpRing p) p n = (zpRing p).zero from if_neg hpn,
        CRing.mul_zero (zpRing p), (zpRing p).zero_add,
        CRing.mul_zero (zpRing p)]

/-! ## 本丸: [c] の dilation 恒等式 -/

/-- **定理 (M106-6): [c]∘(zX) = z·[c]**（z^{p−1} = 1）— 両辺とも
    LT 方程式の解で F(0) = 0・F(1) = zc を共有するため、M49 の
    一意性で一致する。係数の台の性質（deg ≡ 1 mod p−1）を経由しない。 -/
theorem ltSol_dilate (p : Nat) (hp : IsPrime p) (z c : (Zp p).carrier)
    (hz1 : rpow (zpRing p) z (p - 1) = (zpRing p).one) :
    psComp (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1)
      = psSmul (zpRing p) z (ltSol p hp c) := by
  have hz : rpow (zpRing p) z p = z := rpow_fixed_of_root p hp.1 z hz1
  have hzX0 : psSingle (zpRing p) z 1 0 = (zpRing p).zero := if_neg (by omega)
  have hf0 : ltPoly p 0 = (zpRing p).zero := ltPoly_coeff_zero p hp.1
  -- W := [c]∘(zX) の LT 方程式
  have hWeq : psComp (zpRing p)
      (psComp (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1)) (ltPoly p)
      = (psRing (zpRing p)).add
        (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
          (psComp (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1)))
        (psPow (zpRing p)
          (psComp (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1)) p) := by
    have e1 : psComp (zpRing p)
        (psComp (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1))
        (ltPoly p)
        = psComp (zpRing p) (ltSol p hp c)
          (psComp (zpRing p) (psSingle (zpRing p) z 1) (ltPoly p)) :=
      psComp_assoc (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1)
        (ltPoly p) hzX0 hf0
    have e2 : psComp (zpRing p) (psSingle (zpRing p) z 1) (ltPoly p)
        = psSmul (zpRing p) z (ltPoly p) :=
      psComp_single_one (zpRing p) z (ltPoly p) hf0
    have e3 : psSmul (zpRing p) z (ltPoly p)
        = psComp (zpRing p) (ltPoly p) (psSingle (zpRing p) z 1) :=
      (ltPoly_dilate p hp.1 z hz).symm
    have e4 : psComp (zpRing p) (ltSol p hp c)
        (psComp (zpRing p) (ltPoly p) (psSingle (zpRing p) z 1))
        = psComp (zpRing p)
          (psComp (zpRing p) (ltSol p hp c) (ltPoly p))
          (psSingle (zpRing p) z 1) :=
      (psComp_assoc (zpRing p) (ltSol p hp c) (ltPoly p)
        (psSingle (zpRing p) z 1) hf0 hzX0).symm
    have e5 : psComp (zpRing p)
        (psComp (zpRing p) (ltSol p hp c) (ltPoly p)) (psSingle (zpRing p) z 1)
        = psComp (zpRing p)
          ((psRing (zpRing p)).add
            (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) (ltSol p hp c))
            (psPow (zpRing p) (ltSol p hp c) p))
          (psSingle (zpRing p) z 1) :=
      congrArg (fun W => psComp (zpRing p) W (psSingle (zpRing p) z 1))
        (ltSol_equation p hp c)
    have e6 : psComp (zpRing p)
        ((psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) (ltSol p hp c))
          (psPow (zpRing p) (ltSol p hp c) p))
        (psSingle (zpRing p) z 1)
        = (psRing (zpRing p)).add
          (psComp (zpRing p)
            (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) (ltSol p hp c))
            (psSingle (zpRing p) z 1))
          (psComp (zpRing p) (psPow (zpRing p) (ltSol p hp c) p)
            (psSingle (zpRing p) z 1)) :=
      psComp_add (zpRing p) _ _ _
    have e7 : psComp (zpRing p)
        (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) (ltSol p hp c))
        (psSingle (zpRing p) z 1)
        = psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
          (psComp (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1)) :=
      psComp_smul_left (zpRing p) _ _ _
    have e8 : psComp (zpRing p) (psPow (zpRing p) (ltSol p hp c) p)
        (psSingle (zpRing p) z 1)
        = psPow (zpRing p)
          (psComp (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1)) p :=
      psComp_pow (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1) hzX0 p
    rw [e1, e2, e3, e4, e5, e6, e7, e8]
  -- W' := z·[c] の LT 方程式
  have hW'eq : psComp (zpRing p) (psSmul (zpRing p) z (ltSol p hp c))
      (ltPoly p)
      = (psRing (zpRing p)).add
        (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
          (psSmul (zpRing p) z (ltSol p hp c)))
        (psPow (zpRing p) (psSmul (zpRing p) z (ltSol p hp c)) p) := by
    have e1 : psComp (zpRing p) (psSmul (zpRing p) z (ltSol p hp c))
        (ltPoly p)
        = psSmul (zpRing p) z (psComp (zpRing p) (ltSol p hp c) (ltPoly p)) :=
      psComp_smul_left (zpRing p) z _ _
    have e2 : psSmul (zpRing p) z
        (psComp (zpRing p) (ltSol p hp c) (ltPoly p))
        = psSmul (zpRing p) z
          ((psRing (zpRing p)).add
            (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) (ltSol p hp c))
            (psPow (zpRing p) (ltSol p hp c) p)) :=
      congrArg (psSmul (zpRing p) z) (ltSol_equation p hp c)
    have e3 : psSmul (zpRing p) z
        ((psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) (ltSol p hp c))
          (psPow (zpRing p) (ltSol p hp c) p))
        = psAdd (zpRing p)
          (psSmul (zpRing p) z
            (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) (ltSol p hp c)))
          (psSmul (zpRing p) z (psPow (zpRing p) (ltSol p hp c) p)) :=
      psSmul_add (zpRing p) z _ _
    have e4 : psSmul (zpRing p) z
        (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) (ltSol p hp c))
        = psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
          (psSmul (zpRing p) z (ltSol p hp c)) :=
      psSmul_swap (zpRing p) z _ _
    have e5 : psPow (zpRing p) (psSmul (zpRing p) z (ltSol p hp c)) p
        = psSmul (zpRing p) (rpow (zpRing p) z p)
          (psPow (zpRing p) (ltSol p hp c) p) :=
      psPow_smul (zpRing p) z (ltSol p hp c) p
    have e6 : psSmul (zpRing p) (rpow (zpRing p) z p)
        (psPow (zpRing p) (ltSol p hp c) p)
        = psSmul (zpRing p) z (psPow (zpRing p) (ltSol p hp c) p) :=
      congrArg (fun w => psSmul (zpRing p) w
        (psPow (zpRing p) (ltSol p hp c) p)) hz
    rw [e1, e2, e3, e4, ← e6, ← e5]
    rfl
  -- 一意性で合流
  obtain ⟨V, _, huniq⟩ := lubin_tate p hp ((zpRing p).mul z c)
  have hW := huniq
    (psComp (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1))
    ((psComp_coeff_zero (zpRing p) _ _).trans rfl)
    ((psComp_coeff_one (zpRing p) _ _).trans
      (by
        show (zpRing p).mul (ltSol p hp c 1) (psSingle (zpRing p) z 1 1)
          = (zpRing p).mul z c
        rw [show psSingle (zpRing p) z 1 1 = z from if_pos rfl]
        exact (zpRing p).mul_comm c z))
    hWeq
  have hW' := huniq (psSmul (zpRing p) z (ltSol p hp c))
    (by
      show (zpRing p).mul z (ltSol p hp c 0) = (zpRing p).zero
      exact CRing.mul_zero (zpRing p) z)
    rfl
    hW'eq
  exact hW.trans hW'.symm

/-! ## psScale 形と psC 積形への橋 -/

/-- **M106-7a: psScale での読み** — scale_z [c] = z·[c]。 -/
theorem psScale_ltSol (p : Nat) (hp : IsPrime p) (z c : (Zp p).carrier)
    (hz1 : rpow (zpRing p) z (p - 1) = (zpRing p).one) :
    psScale (zpRing p) z (ltSol p hp c)
      = psSmul (zpRing p) z (ltSol p hp c) :=
  (psScale_eq_comp (zpRing p) (ltSol p hp c) z).symm.trans
    (ltSol_dilate p hp z c hz1)

/-- **M106-7b: smul = psC 積**。 -/
theorem psSmul_eq_psC_mul (R : CRing) (c : R.carrier) (F : PS R) :
    psSmul R c F = psMul R (psC R c) F := by
  funext n
  exact (psC_mul_coeff R c F n).symm

/-! ## Galois 同変性と共役族での半線形性 -/

/-- **定理 (M106-8): Galois 同変性** — σ_ζ([c]λ) = ζ·[c]λ。
    Galois 作用（M86F、dilation）が ℤ_p-作用全体と可換であること。
    M89F-5 の eisIter 可換性の [c] 一般化。 -/
theorem eisAut_eisBr (p : Nat) (hp : IsPrime p) (z : (Zp p).carrier)
    (hz1 : rpow (zpRing p) z (p - 1) = (zpRing p).one) (hp2 : 2 ≤ p)
    (c : (Zp p).carrier) :
    (eisAut p z hz1 hp2).map (eisBr p hp c)
      = (eisRing p).mul ((eisOf p).map z) (eisBr p hp c) :=
  congrArg (Quot.mk (eisRel p))
    ((psScale_ltSol p hp z c hz1).trans
      (psSmul_eq_psC_mul (zpRing p) z (ltSol p hp c)))

/-- **M106-9a: 共役点での評価** — [c] の zλ での値（代表 [c]∘(zX)）は
    z·[c]λ（半線形性の O-言明）。 -/
theorem eisBr_conj_scale (p : Nat) (hp : IsPrime p) (z c : (Zp p).carrier)
    (hz1 : rpow (zpRing p) z (p - 1) = (zpRing p).one) :
    Quot.mk (eisRel p)
      (psComp (zpRing p) (ltSol p hp c) (psSingle (zpRing p) z 1))
      = (eisRing p).mul ((eisOf p).map z) (eisBr p hp c) :=
  congrArg (Quot.mk (eisRel p))
    ((ltSol_dilate p hp z c hz1).trans
      (psSmul_eq_psC_mul (zpRing p) z (ltSol p hp c)))

/-- **M106-9b: zpPow = rpow の橋**（M34 の冪根性を rpow 形で使う）。 -/
theorem zpPow_eq_rpow_zp (p : Nat) (x : (Zp p).carrier) : ∀ k,
    zpPow p x k = rpow (zpRing p) x k := by
  intro k
  induction k with
  | zero => exact zpPow_zero p x
  | succ k ih =>
    rw [zpPow_succ p x k, ih]
    rfl

/-- **定理 (M106-9c): Teichmüller 共役での Galois 同変性** —
    σ_{ω(a)}([c]λ) = ω(a)·[c]λ（p ∤ a。M34-5 の ω(a)^{p−1} = 1 を
    橋渡しして M106-8 を instantiate。M84F の共役族 {ω(a)λ} 上で
    [c]-作用が確定する）。 -/
theorem eisAut_teich_eisBr (p : Nat) (hp : IsPrime p) (hp2 : 2 ≤ p)
    {a : Int} (ha : ¬ ((p : Nat) : Int) ∣ a) (c : (Zp p).carrier) :
    (eisAut p (teich p hp a)
        ((zpPow_eq_rpow_zp p (teich p hp a) (p - 1)).symm.trans
          (teich_root_of_unity p hp ha)) hp2).map (eisBr p hp c)
      = (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisBr p hp c) :=
  eisAut_eisBr p hp (teich p hp a) _ hp2 c

end IUT
