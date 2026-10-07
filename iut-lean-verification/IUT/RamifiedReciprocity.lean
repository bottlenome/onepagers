/-
  IUT/RamifiedReciprocity.lean — M107（柱B B-2 の心臓部:
  レベル 1 分岐相互法則 [u]λ = ω(ū)·λ）

  M105/M106 で構成した λ 上の [c]-倍作用について、**単数 u ∈ ℤ_p^× の
  作用が剰余 ū = u mod p だけで決まる**こと——分岐局所類体論の
  レベル 1 の実体——を完全証明する:

    [u]λ = ω(u mod p)·λ    （u = ω(a)·v、v 主単数、と分解して
                              [v]λ = λ・[ω(a)]λ = ω(a)λ）

  M87F の RecRamified はこの法則を「witness 付きインターフェース」として
  持っていたが、本モジュールで **本物の Lubin–Tate 作用がそれを満たす**
  ことが機械検証される。鍵は三つ:

  (1) **[ζ] = ζX の厳密同定**（ltSol_teich）: ζ^{p−1} = 1 なら [ζ] 級数は
      文字どおり一次式 ζX（M106 の f∘(ζX) = ζf と M49 一意性）。
  (2) **形式群の行分解と吸収**（ps21Comp_split / eisRel_FG_absorb）:
      F = C(row₀) + Y·(shift F) の頭出しで F(S,T) = row₀∘S + T·(…)、
      **row₀(F) = X**（F(X,0) = X を CR1/CR2 の (X,0) 特殊化 + 一意性で）
      から **E ∣ T なら F(S,T) ≡ S (mod E)** — 主単数の作用が λ を
      動かさない理由。
  (3) **主単数の分解**: v = 1 + πd（M43 level-1 判定）と M76 加法則で
      [v] = F([1],[πd])、[πd] ∈ (E)（M105）を (2) が吸収。

  * M107-1 `psMul_psX_coeff_zero` / `psMul_psX_coeff` / `psX_shift_split`
    — X 倍 = 添字シフトの一般環版（M93F の p 特化版の一般化）
  * M107-2 `psC_zero` / `psZero_mul` / `psComp_psZero_right` /
    `psMap_constHom_psX` — 小部品（psC 0 = 0・0·G = 0・P∘0 = C(P₀)・
    inY 座標の同定）
  * M107-3 `ps21Comp_add` / `ps21Comp_Y` — 代入の F-加法性と
    Y 座標の代入 = Q
  * M107-4 `ps21Comp_split` — **行分解**: F(P,Q) = Q·(shift F)(P,Q)
    + row₀∘P
  * M107-5 `lt2Sol_row_zero` — **F(X,0) = X**: row₀(lt2Sol) = X
    （CR1/CR2 の (X,0) 特殊化で f∘row₀ = row₀∘f、一意性で [1] = X）
  * M107-6 `eisRel_FG_absorb` — **吸収**: E ∣ T なら F(S,T) ≡ S (mod E)
  * M107-7 `ltSol_teich` — **[ζ] = ζX**（厳密な級数の等式）
  * M107-8 `eisBr_principal` — **主単数は λ を固定**: [v]λ = λ
  * M107-9 `eisBr_reciprocity` — **レベル 1 分岐相互法則**:
    u ≡ a (mod p)、p ∤ a なら [u]λ = ω(a)·λ
  * M107-10 `RamifiedReciprocityData` — 総括レコードと witness

  未形式化（正直申告）: Λₙ(n ≥ 2) での相互法則（塔の環構成が先）・
  rec 全体（K^× = p^ℤ × ℤ_p^×）との貼り合わせの O-レベル実証は次層。
  全て選択公理不使用。
-/
import IUT.LambdaSemilinear

namespace IUT

/-! ## X 倍 = 添字シフト（一般環版） -/

/-- **M107-1a**: (X·g)₀ = 0（一般環版）。 -/
theorem psMul_psX_coeff_zero (R : CRing) (g : PS R) :
    psMul R (psX R) g 0 = R.zero := by
  show R.add R.zero (R.mul (psX R 0) (g (0 - 0))) = R.zero
  rw [(show psX R 0 = R.zero from if_neg (by omega)), R.zero_mul, R.zero_add]

/-- **M107-1b**: (X·g)_{m+1} = g_m（一般環版）。 -/
theorem psMul_psX_coeff (R : CRing) (g : PS R) (m : Nat) :
    psMul R (psX R) g (m + 1) = g m := by
  show rsum R (fun k => R.mul (psX R k) (g (m + 1 - k))) (m + 2) = g m
  have hs : rsum R (fun k => R.mul (psX R k) (g (m + 1 - k))) (m + 2)
      = R.mul (psX R 1) (g (m + 1 - 1)) :=
    rsum_single R _ 1 (m + 2) (by omega) (fun j _ hj => by
      rw [show psX R j = R.zero from if_neg hj]
      exact R.zero_mul _)
  rw [hs, show psX R 1 = R.one from if_pos rfl, R.one_mul]
  exact congrArg g (by omega)

/-- **M107-1c: 頭出し分解（一般環版）** — f = X·shift(f) + C(f₀)。 -/
theorem psX_shift_split (R : CRing) (f : PS R) :
    f = psAdd R (psMul R (psX R) (psShift R f)) (psC R (f 0)) := by
  funext m
  cases m with
  | zero =>
    show f 0 = R.add (psMul R (psX R) (psShift R f) 0) (f 0)
    rw [psMul_psX_coeff_zero R (psShift R f), R.zero_add]
  | succ m =>
    show f (m + 1) = R.add (psMul R (psX R) (psShift R f) (m + 1)) R.zero
    rw [psMul_psX_coeff R (psShift R f) m, CRing.add_zero R]
    rfl

/-! ## 小部品 -/

/-- **M107-2b**: 0·G = 0。 -/
theorem psZero_mul (R : CRing) (G : PS R) :
    psMul R (psZero R) G = psZero R := by
  funext n
  show rsum R (fun k => R.mul (psZero R k) (G (n - k))) (n + 1) = R.zero
  have hc : rsum R (fun k => R.mul (psZero R k) (G (n - k))) (n + 1)
      = rsum R (fun _ => R.zero) (n + 1) :=
    rsum_congr R (n + 1) (fun k _ => R.zero_mul _)
  rw [hc]
  exact rsum_const_zero R (n + 1)

/-- **M107-2c**: P∘0 = C(P₀)。 -/
theorem psComp_psZero_right (R : CRing) (P : PS R) :
    psComp R P (psZero R) = psC R (P 0) := by
  have hpow : ∀ k, 1 ≤ k → psPow R (psZero R) k = psZero R := by
    intro k hk
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    subst hm
    show psMul R (psPow R (psZero R) m) (psZero R) = psZero R
    have hcomm : psMul R (psPow R (psZero R) m) (psZero R)
        = psMul R (psZero R) (psPow R (psZero R) m) :=
      (psRing R).mul_comm _ _
    rw [hcomm]
    exact psZero_mul R (psPow R (psZero R) m)
  funext n
  show rsum R (fun k => R.mul (P k) (psPow R (psZero R) k n)) (n + 1)
    = psC R (P 0) n
  have hs : rsum R (fun k => R.mul (P k) (psPow R (psZero R) k n)) (n + 1)
      = R.mul (P 0) (psPow R (psZero R) 0 n) :=
    rsum_single R _ 0 (n + 1) (by omega) (fun j _ hj => by
      rw [hpow j (by omega)]
      show R.mul (P j) R.zero = R.zero
      exact CRing.mul_zero R _)
  rw [hs]
  show R.mul (P 0) (psOne R n) = psC R (P 0) n
  cases Nat.decEq n 0 with
  | isTrue h =>
    rw [show psOne R n = R.one from if_pos h,
      show psC R (P 0) n = P 0 from if_pos h]
    exact CRing.mul_one R _
  | isFalse h =>
    rw [show psOne R n = R.zero from if_neg h,
      show psC R (P 0) n = R.zero from if_neg h]
    exact CRing.mul_zero R _

/-! ## 代入の F-加法性と Y 座標 -/

/-- **M107-3a: 代入の F-加法性** — (F + G)(P,Q) = F(P,Q) + G(P,Q)。 -/
theorem ps21Comp_add (R : CRing) (F G : PS2 R) (P Q : PS R) :
    ps21Comp R (psAdd (psRing R) F G) P Q
      = psAdd R (ps21Comp R F P Q) (ps21Comp R G P Q) := by
  funext n
  show rsum R (fun b => rsum R (fun a =>
      R.mul (R.add (F b a) (G b a))
        (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1)
    = R.add (ps21Comp R F P Q n) (ps21Comp R G P Q n)
  have hinner : ∀ b, rsum R (fun a =>
      R.mul (R.add (F b a) (G b a))
        (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)
      = R.add
        (rsum R (fun a => R.mul (F b a)
          (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1))
        (rsum R (fun a => R.mul (G b a)
          (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) := by
    intro b
    have hc : rsum R (fun a =>
        R.mul (R.add (F b a) (G b a))
          (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)
        = rsum R (fun a => R.add
          (R.mul (F b a) (psMul R (psPow R P a) (psPow R Q b) n))
          (R.mul (G b a) (psMul R (psPow R P a) (psPow R Q b) n))) (n + 1) :=
      rsum_congr R (n + 1) (fun a _ => R.right_distrib _ _ _)
    rw [hc]
    exact rsum_add R _ _ (n + 1)
  have houter : rsum R (fun b => rsum R (fun a =>
      R.mul (R.add (F b a) (G b a))
        (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1)) (n + 1)
      = rsum R (fun b => R.add
        (rsum R (fun a => R.mul (F b a)
          (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1))
        (rsum R (fun a => R.mul (G b a)
          (psMul R (psPow R P a) (psPow R Q b) n)) (n + 1))) (n + 1) :=
    rsum_congr R (n + 1) (fun b _ => hinner b)
  rw [houter]
  exact rsum_add R _ _ (n + 1)

/-- **M107-3b: Y 座標の代入** — Y(P,Q) = Q。 -/
theorem ps21Comp_Y (R : CRing) (P Q : PS R) (hQ : Q 0 = R.zero) :
    ps21Comp R (psX (psRing R)) P Q = Q := by
  show ps21Comp R (ps2Y R) P Q = Q
  rw [← psMap_constHom_psX R, ps21Comp_inY R (psX R) P Q]
  exact psComp_X R Q hQ

/-! ## 行分解 -/

/-- **定理 (M107-4): 行分解** — F(P,Q) = Q·(shift F)(P,Q) + row₀∘P
    （F = Y·shift F + C(row₀) の頭出しを代入で押し出す）。 -/
theorem ps21Comp_split (R : CRing) (F : PS2 R) (P Q : PS R)
    (hP : P 0 = R.zero) (hQ : Q 0 = R.zero) :
    ps21Comp R F P Q
      = psAdd R
        (psMul R Q (ps21Comp R (psShift (psRing R) F) P Q))
        (psComp R (F 0) P) := by
  have hd := psX_shift_split (psRing R) F
  have h1 : ps21Comp R F P Q
      = ps21Comp R (psAdd (psRing R)
          (psMul (psRing R) (psX (psRing R)) (psShift (psRing R) F))
          (psC (psRing R) (F 0))) P Q :=
    congrArg (fun W => ps21Comp R W P Q) hd
  have h2 := ps21Comp_add R
    (psMul (psRing R) (psX (psRing R)) (psShift (psRing R) F))
    (psC (psRing R) (F 0)) P Q
  have h3 := ps21Comp_mul R (psX (psRing R)) (psShift (psRing R) F) P Q hP hQ
  have h4 := ps21Comp_Y R P Q hQ
  have h5 := ps21Comp_inX R (F 0) P Q
  rw [h1, h2, h3, h4, h5]

/-! ## row₀(lt2Sol) = X -/

/-- **定理 (M107-5): F(X,0) = X** — LT 形式群法則の 0 行は X。
    (X,0) 特殊化: f∘row₀ = row₀∘f（CR1・方程式・CR2・座標の代入の
    合流）、row₀(0) = 0・row₀(1) = 1 から M49 一意性で [1] = X。 -/
theorem lt2Sol_row_zero (p : Nat) (hp : IsPrime p) :
    lt2Sol p hp 0 = psX (zpRing p) := by
  have hF := lt2Sol_is_formal_group p hp
  have hf0 : ltPoly p 0 = (zpRing p).zero := ltPoly_coeff_zero p hp.1
  have hX0 : psX (zpRing p) 0 = (zpRing p).zero := if_neg (by omega)
  have hZ0 : psZero (zpRing p) 0 = (zpRing p).zero := rfl
  -- 特殊化 F(X,0) = row₀（行分解 + 0 の因子消し + row₀∘X = row₀）
  have hspec : ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p))
      (psZero (zpRing p)) = lt2Sol p hp 0 := by
    rw [ps21Comp_split (zpRing p) (lt2Sol p hp) (psX (zpRing p))
        (psZero (zpRing p)) hX0 hZ0,
      psZero_mul (zpRing p), psComp_X_right (zpRing p) (lt2Sol p hp 0)]
    exact CRing.zero_add (psRing (zpRing p)) _
  -- f∘row₀ = row₀∘f
  have hcomm : psComp (zpRing p) (ltPoly p) (lt2Sol p hp 0)
      = psComp (zpRing p) (lt2Sol p hp 0) (ltPoly p) := by
    have c2 : psComp (zpRing p) (ltPoly p) (lt2Sol p hp 0)
        = psComp (zpRing p) (ltPoly p)
          (ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p))
            (psZero (zpRing p))) :=
      congrArg (psComp (zpRing p) (ltPoly p)) hspec.symm
    have c3 := ps21Comp_comp1 (zpRing p) (ltPoly p) (lt2Sol p hp)
      (psX (zpRing p)) (psZero (zpRing p)) hF.1 hX0 hZ0
    have c4 : ps21Comp (zpRing p) (ps2Comp1 (zpRing p) (ltPoly p) (lt2Sol p hp))
        (psX (zpRing p)) (psZero (zpRing p))
        = ps21Comp (zpRing p)
          (ps2Comp2 (zpRing p) (lt2Sol p hp)
            (psC (psRing (zpRing p)) (ltPoly p))
            (psMap (psConstHom (zpRing p)) (ltPoly p)))
          (psX (zpRing p)) (psZero (zpRing p)) :=
      congrArg (fun W => ps21Comp (zpRing p) W (psX (zpRing p))
        (psZero (zpRing p))) hF.2.2.2
    have hU00 : psC (psRing (zpRing p)) (ltPoly p) 0 0 = (zpRing p).zero := by
      show ltPoly p 0 = (zpRing p).zero
      exact hf0
    have hV00 : psMap (psConstHom (zpRing p)) (ltPoly p) 0 0
        = (zpRing p).zero := by
      show psC (zpRing p) (ltPoly p 0) 0 = (zpRing p).zero
      rw [show psC (zpRing p) (ltPoly p 0) 0 = ltPoly p 0 from if_pos rfl]
      exact hf0
    have c5 := ps21Comp_comp2 (zpRing p) (lt2Sol p hp)
      (psC (psRing (zpRing p)) (ltPoly p))
      (psMap (psConstHom (zpRing p)) (ltPoly p))
      (psX (zpRing p)) (psZero (zpRing p)) hU00 hV00 hX0 hZ0
    have c6 : ps21Comp (zpRing p) (psC (psRing (zpRing p)) (ltPoly p))
        (psX (zpRing p)) (psZero (zpRing p)) = ltPoly p := by
      rw [ps21Comp_inX (zpRing p) (ltPoly p) (psX (zpRing p))
        (psZero (zpRing p))]
      exact psComp_X_right (zpRing p) (ltPoly p)
    have c7 : ps21Comp (zpRing p) (psMap (psConstHom (zpRing p)) (ltPoly p))
        (psX (zpRing p)) (psZero (zpRing p)) = psZero (zpRing p) := by
      rw [ps21Comp_inY (zpRing p) (ltPoly p) (psX (zpRing p))
        (psZero (zpRing p)), psComp_psZero_right (zpRing p) (ltPoly p), hf0]
      exact psC_zero (zpRing p)
    have c8 : ps21Comp (zpRing p) (lt2Sol p hp)
        (ps21Comp (zpRing p) (psC (psRing (zpRing p)) (ltPoly p))
          (psX (zpRing p)) (psZero (zpRing p)))
        (ps21Comp (zpRing p) (psMap (psConstHom (zpRing p)) (ltPoly p))
          (psX (zpRing p)) (psZero (zpRing p)))
        = ps21Comp (zpRing p) (lt2Sol p hp) (ltPoly p)
          (psZero (zpRing p)) := by
      rw [c6, c7]
    have c9 : ps21Comp (zpRing p) (lt2Sol p hp) (ltPoly p) (psZero (zpRing p))
        = psComp (zpRing p) (lt2Sol p hp 0) (ltPoly p) := by
      rw [ps21Comp_split (zpRing p) (lt2Sol p hp) (ltPoly p)
          (psZero (zpRing p)) hf0 hZ0, psZero_mul (zpRing p)]
      exact CRing.zero_add (psRing (zpRing p)) _
    rw [c2, c3, c4, c5, c8, c9]
  -- 一意性: row₀ は a = 1 の解
  have hrow0 : lt2Sol p hp 0 0 = (zpRing p).zero := hF.1
  have hrow1 : lt2Sol p hp 0 1 = (zpRing p).one := hF.2.1
  have heq : psComp (zpRing p) (lt2Sol p hp 0) (ltPoly p)
      = (psRing (zpRing p)).add
        (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) (lt2Sol p hp 0))
        (psPow (zpRing p) (lt2Sol p hp 0) p) :=
    hcomm.symm.trans (psComp_ltPoly_left p hp.1 (lt2Sol p hp 0) hrow0)
  obtain ⟨V, _, huniq⟩ := lubin_tate p hp ((zpRing p).one)
  have h1 := huniq (lt2Sol p hp 0) hrow0 hrow1 heq
  have h2 := huniq (psX (zpRing p)) (if_neg (by omega)) (if_pos rfl) (by
    rw [psComp_X (zpRing p) (ltPoly p) hf0]
    have h3 := psComp_ltPoly_left p hp.1 (psX (zpRing p)) (if_neg (by omega))
    have h4 : psComp (zpRing p) (ltPoly p) (psX (zpRing p)) = ltPoly p :=
      psComp_X_right (zpRing p) (ltPoly p)
    rw [← h4]
    exact h3)
  exact h1.trans h2.symm

/-! ## 吸収補題 -/

/-- **定理 (M107-6): 吸収** — S(0) = 0・T(0) = 0・T = w·E なら
    F(S,T) ≡ S (mod E)（行分解 + row₀ = X）。主単数の作用が λ を
    動かさない理由の級数形。 -/
theorem eisRel_FG_absorb (p : Nat) (hp : IsPrime p) (S T : PS (zpRing p))
    (hS : S 0 = (zpRing p).zero) (hT0 : T 0 = (zpRing p).zero)
    (w : PS (zpRing p)) (hT : T = psMul (zpRing p) w (eisPoly p)) :
    eisRel p (ps21Comp (zpRing p) (lt2Sol p hp) S T) S := by
  have hsplit := ps21Comp_split (zpRing p) (lt2Sol p hp) S T hS hT0
  rw [lt2Sol_row_zero p hp, psComp_X (zpRing p) S hS] at hsplit
  -- hsplit : F(S,T) = T·G + S、G := (shift F)(S,T)
  refine ⟨psMul (zpRing p) w
    (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T), ?_⟩
  have hcancel : psAdd (zpRing p)
      (psAdd (zpRing p)
        (psMul (zpRing p) T
          (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T))
        S)
      (psNeg (zpRing p) S)
      = psMul (zpRing p) T
        (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T) := by
    show (psRing (zpRing p)).add
        ((psRing (zpRing p)).add
          (psMul (zpRing p) T
            (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T))
          S)
        ((psRing (zpRing p)).neg S)
      = psMul (zpRing p) T
        (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T)
    rw [(psRing (zpRing p)).add_assoc,
      CRing.add_neg (psRing (zpRing p)) S,
      CRing.add_zero (psRing (zpRing p))]
  have hout : psMul (zpRing p) T
      (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T)
      = psMul (zpRing p)
        (psMul (zpRing p) w
          (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T))
        (eisPoly p) := by
    have h1 : psMul (zpRing p) T
        (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T)
        = psMul (zpRing p) (psMul (zpRing p) w (eisPoly p))
          (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T) :=
      congrArg (fun W => psMul (zpRing p) W
        (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T)) hT
    have h2 : (psRing (zpRing p)).mul
        ((psRing (zpRing p)).mul w (eisPoly p))
        (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T)
        = (psRing (zpRing p)).mul
          ((psRing (zpRing p)).mul w
            (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T))
          (eisPoly p) := by
      rw [(psRing (zpRing p)).mul_assoc, (psRing (zpRing p)).mul_assoc,
        (psRing (zpRing p)).mul_comm (eisPoly p)
          (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T)]
    exact h1.trans h2
  show psAdd (zpRing p) (ps21Comp (zpRing p) (lt2Sol p hp) S T)
      (psNeg (zpRing p) S)
    = psMul (zpRing p)
      (psMul (zpRing p) w
        (ps21Comp (zpRing p) (psShift (psRing (zpRing p)) (lt2Sol p hp)) S T))
      (eisPoly p)
  rw [hsplit, hcancel, hout]

/-! ## [ζ] = ζX の厳密同定 -/

/-- **定理 (M107-7): [ζ] = ζX** — ζ^{p−1} = 1 なら [ζ] 級数は
    文字どおり一次単項式 ζX（M106 の f∘(ζX) = ζf・(ζX)∘f = ζf と
    M49 一意性の合流。Teichmüller 代表の作用は正確にスカラー倍）。 -/
theorem ltSol_teich (p : Nat) (hp : IsPrime p) (z : (Zp p).carrier)
    (hz1 : rpow (zpRing p) z (p - 1) = (zpRing p).one) :
    ltSol p hp z = psSingle (zpRing p) z 1 := by
  have hz : rpow (zpRing p) z p = z := rpow_fixed_of_root p hp.1 z hz1
  have hf0 : ltPoly p 0 = (zpRing p).zero := ltPoly_coeff_zero p hp.1
  have hW0 : psSingle (zpRing p) z 1 0 = (zpRing p).zero := if_neg (by omega)
  have hWeq : psComp (zpRing p) (psSingle (zpRing p) z 1) (ltPoly p)
      = (psRing (zpRing p)).add
        (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
          (psSingle (zpRing p) z 1))
        (psPow (zpRing p) (psSingle (zpRing p) z 1) p) := by
    have e1 : psComp (zpRing p) (psSingle (zpRing p) z 1) (ltPoly p)
        = psSmul (zpRing p) z (ltPoly p) :=
      psComp_single_one (zpRing p) z (ltPoly p) hf0
    have e2 : psSmul (zpRing p) z (ltPoly p)
        = psComp (zpRing p) (ltPoly p) (psSingle (zpRing p) z 1) :=
      (ltPoly_dilate p hp.1 z hz).symm
    have e3 := psComp_ltPoly_left p hp.1 (psSingle (zpRing p) z 1) hW0
    exact (e1.trans e2).trans e3
  obtain ⟨V, _, huniq⟩ := lubin_tate p hp z
  have h1 := huniq (ltSol p hp z) rfl rfl (ltSol_equation p hp z)
  have h2 := huniq (psSingle (zpRing p) z 1) hW0 (if_pos rfl) hWeq
  exact h1.trans h2.symm

/-! ## 主単数は λ を固定 -/

/-- **定理 (M107-8): 主単数の自明作用** — v が主単数なら [v]λ = λ。
    v = 1 + πd（M43）、[v] = F([1],[πd])（M76）、[πd] ∈ (E)（M105）を
    吸収補題が飲み込む。 -/
theorem eisBr_principal (p : Nat) (hp : IsPrime p) (v : (Zp p).carrier)
    (hv : IsPrincipalUnit p v) :
    eisBr p hp v = eisLambda p := by
  -- v − 1 は π の倍数
  have hw1 : ((zpRing p).add v ((zpRing p).neg ((zpRing p).one))).val 1
      = Quot.mk (modCong (p ^ 1)).rel 0 := by
    obtain ⟨c, hc, hpc⟩ := hv 1
    have key : ∀ (C : Int), ((p : Nat) : Int) ∣ 1 - C →
        ((p ^ 1 : Nat) : Int) ∣ (C + -1) - 0 := by
      intro C hC
      obtain ⟨k, hk⟩ := hC
      rw [Nat.pow_one]
      exact ⟨-k, by rw [Int.mul_neg, ← hk]; omega⟩
    show (zmod (p ^ 1)).mul (v.val 1)
        ((zmod (p ^ 1)).inv (Quot.mk (modCong (p ^ 1)).rel 1))
      = Quot.mk (modCong (p ^ 1)).rel 0
    rw [hc]
    exact Quot.sound (key c hpc)
  obtain ⟨d, hd⟩ := (zp_dvd_p_iff p hp.1
    ((zpRing p).add v ((zpRing p).neg ((zpRing p).one)))).mpr hw1
  -- v = 1 + πd
  have hv_split : v = (zpRing p).add ((zpRing p).one)
      (zpMul p ((toZp p).map ((p : Nat) : Int)) d) := by
    rw [← hd]
    show v = (zpRing p).add ((zpRing p).one)
      ((zpRing p).add v ((zpRing p).neg ((zpRing p).one)))
    rw [(zpRing p).add_comm v ((zpRing p).neg ((zpRing p).one)),
      ← (zpRing p).add_assoc]
    have h1 : (zpRing p).add ((zpRing p).one)
        ((zpRing p).neg ((zpRing p).one)) = (zpRing p).zero :=
      CRing.add_neg (zpRing p) ((zpRing p).one)
    rw [h1, (zpRing p).zero_add]
  -- [v] = F(X, [πd])
  have hbr : ltSol p hp v
      = ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p))
        (ltSol p hp (zpMul p ((toZp p).map ((p : Nat) : Int)) d)) := by
    have h1 : ltSol p hp v = ltSol p hp ((zpRing p).add ((zpRing p).one)
        (zpMul p ((toZp p).map ((p : Nat) : Int)) d)) :=
      congrArg (ltSol p hp) hv_split
    have h2 := lt_module_add p hp ((zpRing p).one)
      (zpMul p ((toZp p).map ((p : Nat) : Int)) d)
    rw [h1, ← h2, ltSol_one p hp]
  -- [πd] = h·E
  have hpid : eisRel p
      (ltSol p hp (zpMul p ((toZp p).map ((p : Nat) : Int)) d))
      (psZero (zpRing p)) := by
    have h0 := eisBr_pi_mul p hp d
    exact eis_exact p h0
  obtain ⟨h, hh⟩ := hpid
  have hneg : psNeg (zpRing p) (psZero (zpRing p)) = psZero (zpRing p) :=
    CRing.neg_zero (psRing (zpRing p))
  have hadd : psAdd (zpRing p)
      (ltSol p hp (zpMul p ((toZp p).map ((p : Nat) : Int)) d))
      (psZero (zpRing p))
      = ltSol p hp (zpMul p ((toZp p).map ((p : Nat) : Int)) d) :=
    CRing.add_zero (psRing (zpRing p)) _
  rw [hneg, hadd] at hh
  -- 吸収
  have habs := eisRel_FG_absorb p hp (psX (zpRing p))
    (ltSol p hp (zpMul p ((toZp p).map ((p : Nat) : Int)) d))
    (if_neg (by omega)) rfl h hh
  show Quot.mk (eisRel p) (ltSol p hp v) = eisLambda p
  rw [hbr]
  exact Quot.sound habs

/-! ## レベル 1 分岐相互法則 -/

/-- **定理 (M107-9): レベル 1 分岐相互法則** — u ≡ a (mod p)、p ∤ a
    なら **[u]λ = ω(a)·λ**。単数分解 u = ω(a)·v（M35）で
    [u] = [v]∘[ω(a)] = [v]∘(ω(a)X) = scale_{ω(a)}([v]) = σ_{ω(a)}([v]λ の代表)、
    主単数の自明作用（M107-8）と σ(λ) = ω(a)λ（M86F）の合流。
    「単数の作用は剰余だけで決まる」= 分岐 LCFT のレベル 1 の実体。 -/
theorem eisBr_reciprocity (p : Nat) (hp : IsPrime p) (u : (Zp p).carrier)
    {a : Int} (ha : ¬ ((p : Nat) : Int) ∣ a)
    (hu : u.val 1 = Quot.mk (modCong (p ^ 1)).rel a) :
    eisBr p hp u
      = (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p) := by
  obtain ⟨v, hv, huv⟩ := unit_decomposition p hp u ha hu
  have hz1 : rpow (zpRing p) (teich p hp a) (p - 1) = (zpRing p).one :=
    (zpPow_eq_rpow_zp p (teich p hp a) (p - 1)).symm.trans
      (teich_root_of_unity p hp ha)
  -- [u] = scale_{ω(a)}([v])
  have h1 : ltSol p hp u
      = psComp (zpRing p) (ltSol p hp v) (ltSol p hp (teich p hp a)) := by
    have e1 : ltSol p hp u
        = ltSol p hp ((zpRing p).mul v (teich p hp a)) := by
      have e2 : (zpRing p).mul v (teich p hp a)
          = zpMul p (teich p hp a) v := zpMul_comm p v (teich p hp a)
      rw [e2, ← huv]
    rw [e1, ← lt_module_mul p hp v (teich p hp a)]
  have h2 : psComp (zpRing p) (ltSol p hp v) (ltSol p hp (teich p hp a))
      = psScale (zpRing p) (teich p hp a) (ltSol p hp v) := by
    rw [ltSol_teich p hp (teich p hp a) hz1]
    exact psScale_eq_comp (zpRing p) (ltSol p hp v) (teich p hp a)
  -- scale = eisAut、主単数 + σ(λ) = ω(a)λ
  have h3 : Quot.mk (eisRel p)
      (psScale (zpRing p) (teich p hp a) (ltSol p hp v))
      = (eisAut p (teich p hp a) hz1 hp.1).map (eisBr p hp v) := rfl
  show Quot.mk (eisRel p) (ltSol p hp u)
    = (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p)
  rw [h1, h2, h3, eisBr_principal p hp v hv]
  exact eisAut_lambda p (teich p hp a) hz1 hp.1

/-! ## 総括レコード -/

/-- **M107-10a: 総括** — レベル 1 分岐相互法則のデータ。 -/
structure RamifiedReciprocityData (p : Nat) (hp : IsPrime p) where
  /-- [c]-倍作用（M105）。 -/
  bracket : (Zp p).carrier → (eisRing p).carrier
  /-- 主単数は λ を固定する。 -/
  principal_fix : ∀ v, IsPrincipalUnit p v → bracket v = eisLambda p
  /-- 単数の作用は剰余で決まる: u ≡ a (mod p)、p ∤ a なら
      [u]λ = ω(a)·λ。 -/
  reciprocity : ∀ (u : (Zp p).carrier) (a : Int),
    ¬ ((p : Nat) : Int) ∣ a →
    u.val 1 = Quot.mk (modCong (p ^ 1)).rel a →
    bracket u = (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p)
  /-- π の倍数は λ を殺す（M105 との整合）。 -/
  pi_kill : ∀ c, bracket (zpMul p ((toZp p).map ((p : Nat) : Int)) c)
    = (eisRing p).zero

/-- **M107-10b: witness**。 -/
def ramifiedReciprocityData (p : Nat) (hp : IsPrime p) :
    RamifiedReciprocityData p hp where
  bracket := eisBr p hp
  principal_fix := eisBr_principal p hp
  reciprocity := fun u _ ha hu => eisBr_reciprocity p hp u ha hu
  pi_kill := eisBr_pi_mul p hp

/-- **M107-10c: 存在**。 -/
theorem ramifiedReciprocity_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (RamifiedReciprocityData p hp) :=
  ⟨ramifiedReciprocityData p hp⟩

end IUT
