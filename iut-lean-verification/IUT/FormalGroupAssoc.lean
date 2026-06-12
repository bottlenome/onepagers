/-
  IUT/FormalGroupAssoc.lean — M71（結合則: 結合則キャンペーン最終層）

  **Lubin–Tate 形式群法則の結合則**

    F(F(X,Y), Z) = F(X, F(Y,Z))

  を完全証明する。M63–M70e で構築した全装置の合流点:
  * 両辺 assocL/assocR の構成と一次条件 8 本（M67）
  * 方程式成分: 三本の連鎖律 CR1（M70a）・CR2（M70b）・CR3（M70e）+
    注入の橋渡し（M70c）+ lift の代入互換（M70d）+
    ps3Comp3 の乗法性パッケージ（M70F）で、両候補が
    IsLTFormalGroup3 の方程式 f∘₃A = A(f(X), f(Y), f(Z)) を満たす
    ことを示す。鍵は F 自身の方程式（lt2Sol_is_formal_group、M62）
    f∘₂F = F(f(X), f(Y)) を二回（外側の F と内側の F）に適用し、
    両辺を共通形 F(F(f(X), f(Y)), f(Z))（assocL 側）/
    F(f(X), F(f(Y), f(Z)))（assocR 側）へ落とすこと
  * 三変数一意性 lt3_unique（M66）で assocL = assocR

  これで lt2Sol は定数項 0・一次係数 1・f との交換・可換性（M62）・
  結合性を全て備えた真の 1 次元可換形式群法則であることが機械検証された。
  選択公理不使用。
-/
import IUT.FormalGroupComp3
import IUT.FormalGroupLift

namespace IUT

/-! ## assocL の方程式成分 -/

/-- **M71-1: assocL は LT 方程式を満たす** —
    f∘₃(F(F(X,Y),Z)) = (F(F(X,Y),Z))(f(X), f(Y), f(Z))。
    左辺は CR1 → F の方程式 → CR2 → 橋渡しで、右辺は CR3 → lift の
    崩落で、共通形 F(F(f(X),f(Y)), f(Z)) に合流する。 -/
theorem assocL_equation (p : Nat) (hp : IsPrime p) :
    ps3Comp1 (zpRing p) (ltPoly p) (assocL p hp)
      = ps3Comp3 (zpRing p) (assocL p hp)
          (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p))
          (in3Z (zpRing p) (ltPoly p)) := by
  have hF := lt2Sol_is_formal_group p hp
  have hf0 : ltPoly p 0 = (zpRing p).zero := ltPoly_coeff_zero p hp.1
  have hP000 : liftXY (zpRing p) (lt2Sol p hp) 0 0 0 = (zpRing p).zero :=
    hF.1
  have hZ000 : ps3Z (zpRing p) 0 0 0 = (zpRing p).zero := rfl
  have hU00 : psC (psRing (zpRing p)) (ltPoly p) 0 0 = (zpRing p).zero :=
    hf0
  have hV00 : psMap (psConstHom (zpRing p)) (ltPoly p) 0 0
      = (zpRing p).zero := hf0
  have hW₁ : in3X (zpRing p) (ltPoly p) 0 0 0 = (zpRing p).zero := hf0
  have hW₂ : in3Y (zpRing p) (ltPoly p) 0 0 0 = (zpRing p).zero := hf0
  have hW₃ : in3Z (zpRing p) (ltPoly p) 0 0 0 = (zpRing p).zero := hf0
  -- 左辺 → 共通形 F(F(f(X),f(Y)), f(Z))
  have hL : ps3Comp1 (zpRing p) (ltPoly p) (assocL p hp)
      = ps23Comp (zpRing p) (lt2Sol p hp)
          (ps23Comp (zpRing p) (lt2Sol p hp)
            (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p)))
          (in3Z (zpRing p) (ltPoly p)) := by
    show ps3Comp1 (zpRing p) (ltPoly p)
        (ps23Comp (zpRing p) (lt2Sol p hp)
          (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p))) = _
    rw [ps23Comp_comp1 (zpRing p) (ltPoly p) (lt2Sol p hp)
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p))
        hF.1 hP000 hZ000,
      hF.2.2.2,
      ps23Comp_comp2 (zpRing p) (lt2Sol p hp)
        (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p))
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p))
        hU00 hV00 hP000 hZ000,
      ps23Comp_inX (zpRing p) (ltPoly p)
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p)),
      ps23Comp_inY (zpRing p) (ltPoly p)
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p)),
      liftXY_comp1 (zpRing p) (ltPoly p) (lt2Sol p hp),
      ps3Comp1_ps3Z (zpRing p) (ltPoly p),
      hF.2.2.2,
      liftXY_comp2 (zpRing p) (lt2Sol p hp)
        (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p)),
      liftXY_in2X (zpRing p) (ltPoly p), liftXY_in2Y (zpRing p) (ltPoly p)]
  -- 右辺 → 同じ共通形
  have hR : ps3Comp3 (zpRing p) (assocL p hp)
        (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p))
        (in3Z (zpRing p) (ltPoly p))
      = ps23Comp (zpRing p) (lt2Sol p hp)
          (ps23Comp (zpRing p) (lt2Sol p hp)
            (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p)))
          (in3Z (zpRing p) (ltPoly p)) := by
    show ps3Comp3 (zpRing p)
        (ps23Comp (zpRing p) (lt2Sol p hp)
          (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p)))
        (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p))
        (in3Z (zpRing p) (ltPoly p)) = _
    rw [ps3Comp3_comp23 (zpRing p) (lt2Sol p hp)
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p))
        (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p))
        (in3Z (zpRing p) (ltPoly p)) hP000 hZ000 hW₁ hW₂ hW₃,
      ps3Comp3_liftXY (zpRing p) (lt2Sol p hp)
        (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p))
        (in3Z (zpRing p) (ltPoly p)),
      ps3Comp3_ps3Z (zpRing p) (in3X (zpRing p) (ltPoly p))
        (in3Y (zpRing p) (ltPoly p)) (in3Z (zpRing p) (ltPoly p)) hW₃]
  rw [hL, hR]

/-! ## assocR の方程式成分 -/

/-- **M71-2: assocR は LT 方程式を満たす** —
    共通形は F(f(X), F(f(Y), f(Z)))。 -/
theorem assocR_equation (p : Nat) (hp : IsPrime p) :
    ps3Comp1 (zpRing p) (ltPoly p) (assocR p hp)
      = ps3Comp3 (zpRing p) (assocR p hp)
          (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p))
          (in3Z (zpRing p) (ltPoly p)) := by
  have hF := lt2Sol_is_formal_group p hp
  have hf0 : ltPoly p 0 = (zpRing p).zero := ltPoly_coeff_zero p hp.1
  have hX000 : ps3X (zpRing p) 0 0 0 = (zpRing p).zero := rfl
  have hQ000 : liftYZ (zpRing p) (lt2Sol p hp) 0 0 0 = (zpRing p).zero :=
    hF.1
  have hU00 : psC (psRing (zpRing p)) (ltPoly p) 0 0 = (zpRing p).zero :=
    hf0
  have hV00 : psMap (psConstHom (zpRing p)) (ltPoly p) 0 0
      = (zpRing p).zero := hf0
  have hW₁ : in3X (zpRing p) (ltPoly p) 0 0 0 = (zpRing p).zero := hf0
  have hW₂ : in3Y (zpRing p) (ltPoly p) 0 0 0 = (zpRing p).zero := hf0
  have hW₃ : in3Z (zpRing p) (ltPoly p) 0 0 0 = (zpRing p).zero := hf0
  -- 左辺 → 共通形 F(f(X), F(f(Y),f(Z)))
  have hL : ps3Comp1 (zpRing p) (ltPoly p) (assocR p hp)
      = ps23Comp (zpRing p) (lt2Sol p hp)
          (in3X (zpRing p) (ltPoly p))
          (ps23Comp (zpRing p) (lt2Sol p hp)
            (in3Y (zpRing p) (ltPoly p)) (in3Z (zpRing p) (ltPoly p))) := by
    show ps3Comp1 (zpRing p) (ltPoly p)
        (ps23Comp (zpRing p) (lt2Sol p hp)
          (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp))) = _
    rw [ps23Comp_comp1 (zpRing p) (ltPoly p) (lt2Sol p hp)
        (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp))
        hF.1 hX000 hQ000,
      hF.2.2.2,
      ps23Comp_comp2 (zpRing p) (lt2Sol p hp)
        (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p))
        (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp))
        hU00 hV00 hX000 hQ000,
      ps23Comp_inX (zpRing p) (ltPoly p)
        (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp)),
      ps23Comp_inY (zpRing p) (ltPoly p)
        (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp)),
      ps3Comp1_ps3X (zpRing p) (ltPoly p),
      liftYZ_comp1 (zpRing p) (ltPoly p) (lt2Sol p hp),
      hF.2.2.2,
      liftYZ_comp2 (zpRing p) (lt2Sol p hp)
        (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p)),
      liftYZ_in2X (zpRing p) (ltPoly p), liftYZ_in2Y (zpRing p) (ltPoly p)]
  -- 右辺 → 同じ共通形
  have hR : ps3Comp3 (zpRing p) (assocR p hp)
        (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p))
        (in3Z (zpRing p) (ltPoly p))
      = ps23Comp (zpRing p) (lt2Sol p hp)
          (in3X (zpRing p) (ltPoly p))
          (ps23Comp (zpRing p) (lt2Sol p hp)
            (in3Y (zpRing p) (ltPoly p)) (in3Z (zpRing p) (ltPoly p))) := by
    show ps3Comp3 (zpRing p)
        (ps23Comp (zpRing p) (lt2Sol p hp)
          (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp)))
        (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p))
        (in3Z (zpRing p) (ltPoly p)) = _
    rw [ps3Comp3_comp23 (zpRing p) (lt2Sol p hp)
        (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp))
        (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p))
        (in3Z (zpRing p) (ltPoly p)) hX000 hQ000 hW₁ hW₂ hW₃,
      ps3Comp3_ps3X (zpRing p) (in3X (zpRing p) (ltPoly p))
        (in3Y (zpRing p) (ltPoly p)) (in3Z (zpRing p) (ltPoly p)) hW₁,
      ps3Comp3_liftYZ (zpRing p) (lt2Sol p hp)
        (in3X (zpRing p) (ltPoly p)) (in3Y (zpRing p) (ltPoly p))
        (in3Z (zpRing p) (ltPoly p))]
  rw [hL, hR]

/-! ## IsLTFormalGroup3 の充足と結合則 -/

/-- **M71-3a: assocL は IsLTFormalGroup3 を満たす**。 -/
theorem assocL_is_lt3 (p : Nat) (hp : IsPrime p) :
    IsLTFormalGroup3 p (assocL p hp) :=
  ⟨assocL_000 p hp, (assocL_linear p hp).1, (assocL_linear p hp).2.1,
    (assocL_linear p hp).2.2, assocL_equation p hp⟩

/-- **M71-3b: assocR は IsLTFormalGroup3 を満たす**。 -/
theorem assocR_is_lt3 (p : Nat) (hp : IsPrime p) :
    IsLTFormalGroup3 p (assocR p hp) :=
  ⟨assocR_000 p hp, (assocR_linear p hp).1, (assocR_linear p hp).2.1,
    (assocR_linear p hp).2.2, assocR_equation p hp⟩

/-- **定理 (M71-4): Lubin–Tate 形式群法則の結合則** —
    F(F(X,Y), Z) = F(X, F(Y,Z))（三変数一意性 M66 による）。 -/
theorem lt_formal_group_assoc (p : Nat) (hp : IsPrime p) :
    assocL p hp = assocR p hp :=
  lt3_unique p hp (assocL p hp) (assocR p hp)
    (assocL_is_lt3 p hp) (assocR_is_lt3 p hp)

/-- **M71-4 の展開形**: ps23Comp で書いた結合則。 -/
theorem lt2Sol_assoc (p : Nat) (hp : IsPrime p) :
    ps23Comp (zpRing p) (lt2Sol p hp)
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p))
      = ps23Comp (zpRing p) (lt2Sol p hp)
          (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp)) :=
  lt_formal_group_assoc p hp

end IUT
