/-
  IUT/FormalGroupInvLeft.lean — M75F（形式群の左逆元:
  M75 の左右対称化・サブエージェント並行部品）

  Lubin–Tate 形式群法則 F = lt2Sol の**左逆元**を完全証明する:

    **F(ι(X), X) = 0**   （ι = ltInv p hp = ltSol p hp (−1)）

  M75 の右逆元 F(X, ι(X)) = 0（lt_formal_group_inverse）の証明を
  代入スロットを入れ替えて精密に鏡映する。H' := F(ι(X), X) と置き、
  * 後合成連鎖律（M75-1）: H'∘f = F(ι∘f, X∘f) = F(f∘ι, f)
    （ι は f と可換 — ι の LT 方程式と f∘G = πG + G^p の崩落 M72F）
  * f∘H' = (f∘₂F)(ι,X) = F(f(X),f(Y)) の代入（**F 自身の方程式 M62**）
    = F(f∘ι, f∘X) = F(f∘ι, f)（CR1/CR2/橋渡し M74）
  の両輪で H' が LT 方程式 H'∘f = π·H' + H'^p を満たすことを示し、
  H'(0) = 0・H'(1) = (−1) + 1 = 0（M72 の一次係数 master 補題）から
  **一意性（M49）で H' = 0 級数 = ltSol p hp 0** と同定する。

  * M75F-1 `lt_formal_group_inverse_left` — **左逆元 F(ι(X), X) = 0（本丸）**
  * M75F-2 `lt_formal_group_inverse_both` — 左右両側の逆元のパッケージ
    （witness は [-1] 級数の明示構成、M75 の右逆元と本層の左逆元を束ねる）

  これで lt2Sol の逆元は左右両側で機械検証され、M75 で正直申告した
  「左逆元は未形式化」の穴が埋まる。全て選択公理不使用。
-/
import IUT.FormalGroupInverse

namespace IUT

/-- **定理 (M75F-1): Lubin–Tate 形式群の左逆元（本丸）** —
    F(ι(X), X) = 0。M75-4 の証明の代入スロットを入れ替えた鏡映:
    H' := F(ι(X), X) が LT 方程式を満たし
    （H'∘f は後合成連鎖律・f∘H' は F の方程式 + CR1/CR2/橋渡しで
    共通形 F(f∘ι, f) に合流）、H'(0) = H'(1) = 0 から一意性で
    0 級数と同定される。 -/
theorem lt_formal_group_inverse_left (p : Nat) (hp : IsPrime p) :
    ps21Comp (zpRing p) (lt2Sol p hp) (ltInv p hp) (psX (zpRing p))
      = psZero (zpRing p) := by
  have hF := lt2Sol_is_formal_group p hp
  have hf0 : ltPoly p 0 = (zpRing p).zero := ltPoly_coeff_zero p hp.1
  have hX0 : psX (zpRing p) 0 = (zpRing p).zero := rfl
  have hι0 : ltInv p hp 0 = (zpRing p).zero := rfl
  -- H' の定数項と一次係数
  have hH'0 : ps21Comp (zpRing p) (lt2Sol p hp) (ltInv p hp)
      (psX (zpRing p)) 0 = (zpRing p).zero := by
    rw [ps21Comp_zero_coeff]
    exact hF.1
  have hH'1 : ps21Comp (zpRing p) (lt2Sol p hp) (ltInv p hp)
      (psX (zpRing p)) 1 = (zpRing p).zero := by
    rw [ps21Comp_lin (zpRing p) (lt2Sol p hp) (ltInv p hp)
        (psX (zpRing p)) hι0 hX0,
      hF.2.1, hF.2.2.1,
      show ltInv p hp 1 = (zpRing p).neg ((zpRing p).one) from rfl,
      show psX (zpRing p) 1 = (zpRing p).one from rfl,
      (zpRing p).one_mul, (zpRing p).one_mul]
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
  -- H'∘f → 共通形 F(f∘ι, f)
  have hL : psComp (zpRing p)
      (ps21Comp (zpRing p) (lt2Sol p hp) (ltInv p hp) (psX (zpRing p)))
      (ltPoly p)
      = ps21Comp (zpRing p) (lt2Sol p hp)
          (psComp (zpRing p) (ltPoly p) (ltInv p hp)) (ltPoly p) := by
    rw [psComp_ps21Comp (zpRing p) (lt2Sol p hp) (ltInv p hp)
        (psX (zpRing p)) (ltPoly p) hι0 hX0 hf0,
      psComp_X (zpRing p) (ltPoly p) hf0, hcomm]
  -- f∘H' → 同じ共通形（CR1 → F の方程式 → CR2 → 橋渡し）
  have hR : psComp (zpRing p) (ltPoly p)
      (ps21Comp (zpRing p) (lt2Sol p hp) (ltInv p hp) (psX (zpRing p)))
      = ps21Comp (zpRing p) (lt2Sol p hp)
          (psComp (zpRing p) (ltPoly p) (ltInv p hp)) (ltPoly p) := by
    rw [ps21Comp_comp1 (zpRing p) (ltPoly p) (lt2Sol p hp)
        (ltInv p hp) (psX (zpRing p)) hF.1 hι0 hX0,
      hF.2.2.2,
      ps21Comp_comp2 (zpRing p) (lt2Sol p hp)
        (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p))
        (ltInv p hp) (psX (zpRing p)) hU00 hV00 hι0 hX0,
      ps21Comp_inX (zpRing p) (ltPoly p) (ltInv p hp) (psX (zpRing p)),
      ps21Comp_inY (zpRing p) (ltPoly p) (ltInv p hp) (psX (zpRing p)),
      psComp_X_right (zpRing p) (ltPoly p)]
  -- H' は LT 方程式（a = 0）を満たす
  have heqH' : psComp (zpRing p)
      (ps21Comp (zpRing p) (lt2Sol p hp) (ltInv p hp) (psX (zpRing p)))
      (ltPoly p)
      = (psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
            (ps21Comp (zpRing p) (lt2Sol p hp) (ltInv p hp)
              (psX (zpRing p))))
          (psPow (zpRing p)
            (ps21Comp (zpRing p) (lt2Sol p hp) (ltInv p hp)
              (psX (zpRing p))) p) := by
    rw [hL, ← hR]
    exact psComp_ltPoly_left p hp.1 _ hH'0
  -- 一意性: H' も 0 級数も ltSol p hp 0
  obtain ⟨W, _, huniq⟩ := lubin_tate p hp ((zpRing p).zero)
  exact (huniq _ hH'0 hH'1 heqH').trans
    (huniq (psZero (zpRing p)) rfl rfl (zero_lt_equation p hp)).symm

/-- **M75F-2: 左右両側の逆元のパッケージ** — lt2Sol は左右両側の
    逆元を持つ（witness は [-1] 級数の明示構成、choice なし。
    右は M75-4、左は本層 M75F-1）。 -/
theorem lt_formal_group_inverse_both (p : Nat) (hp : IsPrime p) :
    ∃ ι : PS (zpRing p), ι 0 = (zpRing p).zero ∧
      ps21Comp (zpRing p) (lt2Sol p hp) (psX (zpRing p)) ι
        = psZero (zpRing p) ∧
      ps21Comp (zpRing p) (lt2Sol p hp) ι (psX (zpRing p))
        = psZero (zpRing p) :=
  ⟨ltInv p hp, rfl, lt_formal_group_inverse p hp,
    lt_formal_group_inverse_left p hp⟩

end IUT
