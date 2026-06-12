/-
  IUT/FormalGroupInverse.lean — M75（形式群の逆元 [-1] 級数:
  逆元キャンペーン最終層・完結）

  Lubin–Tate 形式群法則 F = lt2Sol の**逆元**を完全証明する:

    **F(X, ι(X)) = 0**   （ι = ltSol p hp (−1)、[-1] 級数）

  戦略: H := F(X, ι(X)) と置き、
  * 後合成連鎖律（本層）: H∘f = F(X∘f, ι∘f) = F(f, f∘ι)
    （ι は f と可換 — ι の LT 方程式と f∘G = πG + G^p の崩落 M72F）
  * f∘H = (f∘₂F)(X,ι) = F(f(X),f(Y)) の代入（**F 自身の方程式 M62**）
    = F(f∘X, f∘ι) = F(f, f∘ι)（CR1/CR2/橋渡し M74）
  の両輪で H が LT 方程式 H∘f = π·H + H^p を満たすことを示し、
  H(0) = 0・H(1) = 1 + (−1) = 0（M72 の一次係数 master 補題）から
  **一意性（M49）で H = 0 級数 = ltSol p hp 0** と同定する。

  * M75-1 `psComp_ps21Comp` — **後合成連鎖律**
    (F(P,Q))∘g = F(P∘g, Q∘g)（psComp の乗法性・冪 M72F と合流）
  * M75-2 `zero_lt_equation` — 0 級数は LT 方程式の解（a = 0）
  * M75-3 `ltInv` — **[-1] 級数** ι = ltSol p hp (−1) と読み出し
  * M75-4 `lt_formal_group_inverse` — **逆元 F(X, ι(X)) = 0（本丸）**
  * M75-5 `lt_formal_group_has_inverse` — 存在形のパッケージ

  これで lt2Sol は単位・可換・結合（M62/M71）に加え**逆元**を備えた
  完全な 1 次元形式群（群法則の全公理）であることが機械検証された。
  左逆元 F(ι(X), X) = 0 は可換性から従う（明示の機械検証は未形式化、
  正直申告）。全て選択公理不使用。
-/
import IUT.FormalGroupEvalComp
import IUT.LTIterate

namespace IUT

/-! ## 後合成連鎖律 -/

/-- **定理 (M75-1): 後合成連鎖律** — (F(P,Q))∘g = F(P∘g, Q∘g)
    （P(0) = Q(0) = g(0) = 0。M70e の ps3Comp3_comp23 の 1 変数版、
    psComp の乗法性・冪の代入（M72F）と合流）。 -/
theorem psComp_ps21Comp (R : CRing) (F : PS2 R) (P Q g : PS R)
    (hP : P 0 = R.zero) (hQ : Q 0 = R.zero) (hg : g 0 = R.zero) :
    psComp R (ps21Comp R F P Q) g
      = ps21Comp R F (psComp R P g) (psComp R Q g) := by
  funext n
  -- 左辺: ps21Comp の係数を pad + 右抽出で三重和へ
  have hL : psComp R (ps21Comp R F P Q) g n
      = rsum R (fun m => rsum R (fun b₁ => rsum R (fun a₁ =>
          R.mul (F b₁ a₁)
            (R.mul (psMul R (psPow R P a₁) (psPow R Q b₁) m)
              (psPow R g m n))) (n + 1)) (n + 1)) (n + 1) := by
    show rsum R (fun m => R.mul (ps21Comp R F P Q m)
        (psPow R g m n)) (n + 1) = _
    refine rsum_congr R (n + 1) (fun m hm => ?_)
    rw [ps21Comp_pad R F P Q hP hQ (n + 1) m (by omega),
      rsum_mul_right R _ (psPow R g m n) (n + 1)]
    refine rsum_congr R (n + 1) (fun b₁ _ => ?_)
    rw [rsum_mul_right R _ (psPow R g m n) (n + 1)]
    exact rsum_congr R (n + 1) (fun a₁ _ =>
      R.mul_assoc (F b₁ a₁) _ _)
  -- 右辺: 冪の代入 + 乗法性で (P^{a₁}Q^{b₁})∘g に融合して三重和へ
  have hR : ps21Comp R F (psComp R P g) (psComp R Q g) n
      = rsum R (fun b₁ => rsum R (fun a₁ => rsum R (fun m =>
          R.mul (F b₁ a₁)
            (R.mul (psMul R (psPow R P a₁) (psPow R Q b₁) m)
              (psPow R g m n))) (n + 1)) (n + 1)) (n + 1) := by
    show rsum R (fun b₁ => rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          (psMul R (psPow R (psComp R P g) a₁)
            (psPow R (psComp R Q g) b₁) n)) (n + 1)) (n + 1) = _
    refine rsum_congr R (n + 1) (fun b₁ _ => ?_)
    refine rsum_congr R (n + 1) (fun a₁ _ => ?_)
    rw [← psComp_pow R P g hg a₁, ← psComp_pow R Q g hg b₁,
      ← psComp_mul R (psPow R P a₁) (psPow R Q b₁) g hg]
    show R.mul (F b₁ a₁) (rsum R (fun m =>
        R.mul (psMul R (psPow R P a₁) (psPow R Q b₁) m)
          (psPow R g m n)) (n + 1)) = _
    rw [rsum_mul_left R _ (F b₁ a₁) (n + 1)]
  rw [hL, hR]
  -- (m, b₁, a₁) → (b₁, a₁, m)
  have hx1 : rsum R (fun m => rsum R (fun b₁ => rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          (R.mul (psMul R (psPow R P a₁) (psPow R Q b₁) m)
            (psPow R g m n))) (n + 1)) (n + 1)) (n + 1)
      = rsum R (fun b₁ => rsum R (fun m => rsum R (fun a₁ =>
          R.mul (F b₁ a₁)
            (R.mul (psMul R (psPow R P a₁) (psPow R Q b₁) m)
              (psPow R g m n))) (n + 1)) (n + 1)) (n + 1) :=
    rsum_exchange R (fun m b₁ => rsum R (fun a₁ =>
        R.mul (F b₁ a₁)
          (R.mul (psMul R (psPow R P a₁) (psPow R Q b₁) m)
            (psPow R g m n))) (n + 1)) (n + 1) (n + 1)
  rw [hx1]
  refine rsum_congr R (n + 1) (fun b₁ _ => ?_)
  exact rsum_exchange R (fun m a₁ =>
      R.mul (F b₁ a₁)
        (R.mul (psMul R (psPow R P a₁) (psPow R Q b₁) m)
          (psPow R g m n))) (n + 1) (n + 1)

/-! ## 0 級数は LT 方程式の解 -/

/-- **M75-2: 0 級数の LT 方程式** — 0∘f = π·0 + 0^p（a = 0 の解）。 -/
theorem zero_lt_equation (p : Nat) (hp : IsPrime p) :
    psComp (zpRing p) (psZero (zpRing p)) (ltPoly p)
      = (psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
            (psZero (zpRing p)))
          (psPow (zpRing p) (psZero (zpRing p)) p) := by
  have h1 : psComp (zpRing p) (psZero (zpRing p)) (ltPoly p)
      = psZero (zpRing p) := by
    funext n
    show rsum (zpRing p) (fun k => (zpRing p).mul (psZero (zpRing p) k)
        (psPow (zpRing p) (ltPoly p) k n)) (n + 1) = (zpRing p).zero
    have hz : rsum (zpRing p) (fun k => (zpRing p).mul (psZero (zpRing p) k)
          (psPow (zpRing p) (ltPoly p) k n)) (n + 1)
        = rsum (zpRing p) (fun _ => (zpRing p).zero) (n + 1) :=
      rsum_congr (zpRing p) (n + 1) (fun k _ =>
        (zpRing p).zero_mul (psPow (zpRing p) (ltPoly p) k n))
    rw [hz]
    exact rsum_const_zero (zpRing p) (n + 1)
  have h2 : psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
      (psZero (zpRing p)) = psZero (zpRing p) := by
    funext n
    exact (zpRing p).mul_zero _
  have h3 : psPow (zpRing p) (psZero (zpRing p)) p = psZero (zpRing p) := by
    have hp2 : 2 ≤ p := hp.1
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    subst hp'
    funext n
    show rsum (zpRing (p' + 1)) (fun m => (zpRing (p' + 1)).mul
        (psPow (zpRing (p' + 1)) (psZero (zpRing (p' + 1))) p' m)
        (psZero (zpRing (p' + 1)) (n - m))) (n + 1)
      = (zpRing (p' + 1)).zero
    have hz : rsum (zpRing (p' + 1)) (fun m => (zpRing (p' + 1)).mul
          (psPow (zpRing (p' + 1)) (psZero (zpRing (p' + 1))) p' m)
          (psZero (zpRing (p' + 1)) (n - m))) (n + 1)
        = rsum (zpRing (p' + 1)) (fun _ => (zpRing (p' + 1)).zero)
            (n + 1) :=
      rsum_congr (zpRing (p' + 1)) (n + 1) (fun m _ =>
        (zpRing (p' + 1)).mul_zero _)
    rw [hz]
    exact rsum_const_zero (zpRing (p' + 1)) (n + 1)
  rw [h1, h2, h3]
  funext n
  exact ((zpRing p).zero_add _).symm

/-! ## [-1] 級数と逆元 -/

/-- **M75-3: [-1] 級数** — 線形部 −X で f と可換な唯一の級数
    （M49 の Lubin–Tate 補題の a = −1 への適用）。 -/
def ltInv (p : Nat) (hp : IsPrime p) : PS (zpRing p) :=
  ltSol p hp ((zpRing p).neg ((zpRing p).one))

theorem ltInv_zero (p : Nat) (hp : IsPrime p) :
    ltInv p hp 0 = (zpRing p).zero := rfl

theorem ltInv_one (p : Nat) (hp : IsPrime p) :
    ltInv p hp 1 = (zpRing p).neg ((zpRing p).one) := rfl

/-- **定理 (M75-4): Lubin–Tate 形式群の逆元（本丸）** —
    F(X, ι(X)) = 0。H := F(X, ι(X)) が LT 方程式を満たし
    （H∘f は後合成連鎖律・f∘H は F の方程式 + CR1/CR2/橋渡しで
    共通形 F(f, f∘ι) に合流）、H(0) = H(1) = 0 から一意性で
    0 級数と同定される。 -/
theorem lt_formal_group_inverse (p : Nat) (hp : IsPrime p) :
    ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p)) (ltInv p hp)
      = psZero (zpRing p) := by
  have hF := lt2Sol_is_formal_group p hp
  have hf0 : ltPoly p 0 = (zpRing p).zero := ltPoly_coeff_zero p hp.1
  have hX0 : psX (zpRing p) 0 = (zpRing p).zero := rfl
  have hι0 : ltInv p hp 0 = (zpRing p).zero := rfl
  -- H の定数項と一次係数
  have hH0 : ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p))
      (ltInv p hp) 0 = (zpRing p).zero := by
    rw [ps21Comp_zero_coeff]
    exact hF.1
  have hH1 : ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p))
      (ltInv p hp) 1 = (zpRing p).zero := by
    rw [ps21Comp_lin (zpRing p) (lt2Sol p hp) (psX (zpRing p))
        (ltInv p hp) hX0 hι0,
      hF.2.1, hF.2.2.1,
      show psX (zpRing p) 1 = (zpRing p).one from rfl,
      show ltInv p hp 1 = (zpRing p).neg ((zpRing p).one) from rfl,
      (zpRing p).one_mul, (zpRing p).one_mul, (zpRing p).add_comm]
    exact (zpRing p).neg_add ((zpRing p).one)
  -- ι∘f = f∘ι（ι の LT 方程式 + f∘G の崩落）
  have hcomm : psComp (zpRing p) (ltInv p hp) (ltPoly p)
      = psComp (zpRing p) (ltPoly p) (ltInv p hp) :=
    (ltSol_equation p hp ((zpRing p).neg ((zpRing p).one))).trans
      (psComp_ltPoly_left p hp.1 (ltInv p hp) rfl).symm
  -- 注入の定数項（係数読み出しは定義的に f₀）
  have hU00 : psC (psRing (zpRing p)) (ltPoly p) 0 0
      = (zpRing p).zero := hf0
  have hV00 : psMap (psConstHom (zpRing p)) (ltPoly p) 0 0
      = (zpRing p).zero := hf0
  -- H∘f → 共通形 F(f, f∘ι)
  have hL : psComp (zpRing p)
      (ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p)) (ltInv p hp))
      (ltPoly p)
      = ps21Comp (zpRing p) (lt2Sol p hp) (ltPoly p)
          (psComp (zpRing p) (ltPoly p) (ltInv p hp)) := by
    rw [psComp_ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p))
        (ltInv p hp) (ltPoly p) hX0 hι0 hf0,
      psComp_X (zpRing p) (ltPoly p) hf0, hcomm]
  -- f∘H → 同じ共通形（CR1 → F の方程式 → CR2 → 橋渡し）
  have hR : psComp (zpRing p) (ltPoly p)
      (ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p)) (ltInv p hp))
      = ps21Comp (zpRing p) (lt2Sol p hp) (ltPoly p)
          (psComp (zpRing p) (ltPoly p) (ltInv p hp)) := by
    rw [ps21Comp_comp1 (zpRing p) (ltPoly p) (lt2Sol p hp)
        (psX (zpRing p)) (ltInv p hp) hF.1 hX0 hι0,
      hF.2.2.2,
      ps21Comp_comp2 (zpRing p) (lt2Sol p hp)
        (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p))
        (psX (zpRing p)) (ltInv p hp) hU00 hV00 hX0 hι0,
      ps21Comp_inX (zpRing p) (ltPoly p) (psX (zpRing p)) (ltInv p hp),
      ps21Comp_inY (zpRing p) (ltPoly p) (psX (zpRing p)) (ltInv p hp),
      psComp_X_right (zpRing p) (ltPoly p)]
  -- H は LT 方程式（a = 0）を満たす
  have heqH : psComp (zpRing p)
      (ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p)) (ltInv p hp))
      (ltPoly p)
      = (psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
            (ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p))
              (ltInv p hp)))
          (psPow (zpRing p)
            (ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p))
              (ltInv p hp)) p) := by
    rw [hL, ← hR]
    exact psComp_ltPoly_left p hp.1 _ hH0
  -- 一意性: H も 0 級数も ltSol p hp 0
  obtain ⟨W, _, huniq⟩ := lubin_tate p hp ((zpRing p).zero)
  have h1 := huniq _ hH0 hH1 heqH
  have h2 := huniq (psZero (zpRing p)) rfl rfl (zero_lt_equation p hp)
  exact h1.trans h2.symm

/-- **M75-5: 逆元の存在形** — lt2Sol は逆元を持つ
    （witness は [-1] 級数の明示構成、choice なし）。 -/
theorem lt_formal_group_has_inverse (p : Nat) (hp : IsPrime p) :
    ∃ ι : PS (zpRing p), ι 0 = (zpRing p).zero ∧
      ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p)) ι
        = psZero (zpRing p) :=
  ⟨ltInv p hp, rfl, lt_formal_group_inverse p hp⟩

end IUT
