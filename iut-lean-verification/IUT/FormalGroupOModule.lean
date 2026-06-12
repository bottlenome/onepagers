/-
  IUT/FormalGroupOModule.lean — M76（[a] 級数の O-加群構造:
  形式 ℤ_p-加群キャンペーン第一層）

  Lubin–Tate 補題（M49）の [a] := ltSol p hp a 級数族が
  **形式群 F = lt2Sol 上の ℤ_p-加群構造（環準同型 ℤ_p → End(F)）**
  をなすことを完全証明する。M75 の逆元証明スキーマ（両連鎖律で
  共通形に合流 → 一意性）が a, b を任意にしてそのまま一般化する。

  * M76-1 `ltSol_comm` — [a] は f と可換（[a] の LT 方程式 +
    f∘G = πG + G^p の崩落 M72F、M75 の hcomm の一般化）
  * M76-2 `ltSol_zero` / `ltSol_one` — **[0] = 0 級数・[1] = X**
    （一意性による正規化。[1] = X は psComp_X / psComp_X_right の合流）
  * M76-3 `lt_module_add` — **加法 F([a]X, [b]X) = [a+b]X（本丸）**:
    H := F([a],[b]) が H(0) = 0・H(1) = a + b・LT 方程式
    （H∘f は後合成連鎖律 M75-1、f∘H は CR1 → F の方程式 → CR2 →
    橋渡し M74 — 共通形 F(f∘[a], f∘[b])）を満たし一意性で [a+b]
  * M76-4 `lt_module_mul` — **乗法 [a]∘[b] = [ab]**:
    psComp_assoc（M72F の 1 変数連鎖律）×3 と f との可換性だけで
    G := [a]∘[b] が f と可換 → 一意性で [ab]
  * M76-5 `lt_module_add_neg` / `ltInv_eq_ltSol_neg_one` —
    **一般の逆元 F([a]X, [−a]X) = 0** と [-1] 級数の同定

  これで a ↦ [a] は加法・乗法・単位を保つ = lt2Sol は
  **形式 ℤ_p-加群**（Lubin–Tate 理論の心臓部）。End(F) 側の
  環構造の圏論的パッケージングは未形式化（正直申告）。
  全て選択公理不使用。
-/
import IUT.FormalGroupInverse

namespace IUT

/-! ## [a] と f の可換性・正規化 -/

/-- **M76-1: [a] は f と可換** — [a]∘f = f∘[a]
    （[a] の LT 方程式と f∘G の崩落（M72F）の合流、
    M75 の hcomm の一般化）。 -/
theorem ltSol_comm (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) :
    psComp (zpRing p) (ltSol p hp a) (ltPoly p)
      = psComp (zpRing p) (ltPoly p) (ltSol p hp a) :=
  (ltSol_equation p hp a).trans
    (psComp_ltPoly_left p hp.1 (ltSol p hp a) rfl).symm

/-- **M76-2a: [0] = 0 級数**（0 級数も a = 0 の解 → 一意性）。 -/
theorem ltSol_zero (p : Nat) (hp : IsPrime p) :
    ltSol p hp ((zpRing p).zero) = psZero (zpRing p) := by
  obtain ⟨W, _, huniq⟩ := lubin_tate p hp ((zpRing p).zero)
  exact (huniq (psZero (zpRing p)) rfl rfl (zero_lt_equation p hp)).symm

/-- **M76-2b: [1] = X**（X も a = 1 の解: X∘f = f = f∘X = π·X + X^p
    — psComp_X・psComp_X_right・f∘G の崩落の合流 → 一意性）。 -/
theorem ltSol_one (p : Nat) (hp : IsPrime p) :
    ltSol p hp ((zpRing p).one) = psX (zpRing p) := by
  obtain ⟨W, _, huniq⟩ := lubin_tate p hp ((zpRing p).one)
  refine (huniq (psX (zpRing p)) rfl rfl ?_).symm
  rw [psComp_X (zpRing p) (ltPoly p) (ltPoly_coeff_zero p hp.1),
    ← psComp_ltPoly_left p hp.1 (psX (zpRing p)) rfl]
  exact (psComp_X_right (zpRing p) (ltPoly p)).symm

/-! ## 加法構造 -/

/-- **定理 (M76-3): O-加群の加法（本丸）** — F([a]X, [b]X) = [a+b]X。
    M75 の逆元証明スキーマの一般化: H := F([a],[b]) が LT 方程式を
    満たし（両連鎖律で共通形 F(f∘[a], f∘[b]) に合流）、
    H(0) = 0・H(1) = a + b から一意性で [a+b] と同定。 -/
theorem lt_module_add (p : Nat) (hp : IsPrime p)
    (a b : (Zp p).carrier) :
    ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a) (ltSol p hp b)
      = ltSol p hp ((zpRing p).add a b) := by
  have hF := lt2Sol_is_formal_group p hp
  have hf0 : ltPoly p 0 = (zpRing p).zero := ltPoly_coeff_zero p hp.1
  have ha0 : ltSol p hp a 0 = (zpRing p).zero := rfl
  have hb0 : ltSol p hp b 0 = (zpRing p).zero := rfl
  -- H の定数項と一次係数
  have hH0 : ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a)
      (ltSol p hp b) 0 = (zpRing p).zero := by
    rw [ps21Comp_zero_coeff]
    exact hF.1
  have hH1 : ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a)
      (ltSol p hp b) 1 = (zpRing p).add a b := by
    rw [ps21Comp_lin (zpRing p) (lt2Sol p hp) (ltSol p hp a)
        (ltSol p hp b) ha0 hb0,
      hF.2.1, hF.2.2.1,
      show ltSol p hp a 1 = a from rfl,
      show ltSol p hp b 1 = b from rfl,
      (zpRing p).one_mul, (zpRing p).one_mul]
  -- 注入の定数項
  have hU00 : psC (psRing (zpRing p)) (ltPoly p) 0 0
      = (zpRing p).zero := hf0
  have hV00 : psMap (psConstHom (zpRing p)) (ltPoly p) 0 0
      = (zpRing p).zero := hf0
  -- H∘f → 共通形 F(f∘[a], f∘[b])
  have hL : psComp (zpRing p)
      (ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a) (ltSol p hp b))
      (ltPoly p)
      = ps21Comp (zpRing p) (lt2Sol p hp)
          (psComp (zpRing p) (ltPoly p) (ltSol p hp a))
          (psComp (zpRing p) (ltPoly p) (ltSol p hp b)) := by
    rw [psComp_ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a)
        (ltSol p hp b) (ltPoly p) ha0 hb0 hf0,
      ltSol_comm p hp a, ltSol_comm p hp b]
  -- f∘H → 同じ共通形（CR1 → F の方程式 → CR2 → 橋渡し）
  have hR : psComp (zpRing p) (ltPoly p)
      (ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a) (ltSol p hp b))
      = ps21Comp (zpRing p) (lt2Sol p hp)
          (psComp (zpRing p) (ltPoly p) (ltSol p hp a))
          (psComp (zpRing p) (ltPoly p) (ltSol p hp b)) := by
    rw [ps21Comp_comp1 (zpRing p) (ltPoly p) (lt2Sol p hp)
        (ltSol p hp a) (ltSol p hp b) hF.1 ha0 hb0,
      hF.2.2.2,
      ps21Comp_comp2 (zpRing p) (lt2Sol p hp)
        (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p))
        (ltSol p hp a) (ltSol p hp b) hU00 hV00 ha0 hb0,
      ps21Comp_inX (zpRing p) (ltPoly p) (ltSol p hp a) (ltSol p hp b),
      ps21Comp_inY (zpRing p) (ltPoly p) (ltSol p hp a) (ltSol p hp b)]
  -- H は LT 方程式（一次係数 a + b）を満たす
  have heqH : psComp (zpRing p)
      (ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a) (ltSol p hp b))
      (ltPoly p)
      = (psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
            (ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a)
              (ltSol p hp b)))
          (psPow (zpRing p)
            (ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a)
              (ltSol p hp b)) p) := by
    rw [hL, ← hR]
    exact psComp_ltPoly_left p hp.1 _ hH0
  -- 一意性
  obtain ⟨W, _, huniq⟩ := lubin_tate p hp ((zpRing p).add a b)
  exact huniq _ hH0 hH1 heqH

/-! ## 乗法構造 -/

/-- **定理 (M76-4): O-加群の乗法（合成則）** — [a]∘[b] = [ab]。
    psComp_assoc（M72F）×3 と f との可換性で G := [a]∘[b] が
    f と可換 → 一意性で [ab] と同定。 -/
theorem lt_module_mul (p : Nat) (hp : IsPrime p)
    (a b : (Zp p).carrier) :
    psComp (zpRing p) (ltSol p hp a) (ltSol p hp b)
      = ltSol p hp ((zpRing p).mul a b) := by
  have hf0 : ltPoly p 0 = (zpRing p).zero := ltPoly_coeff_zero p hp.1
  have ha0 : ltSol p hp a 0 = (zpRing p).zero := rfl
  have hb0 : ltSol p hp b 0 = (zpRing p).zero := rfl
  have hG0 : psComp (zpRing p) (ltSol p hp a) (ltSol p hp b) 0
      = (zpRing p).zero :=
    (psComp_coeff_zero (zpRing p) (ltSol p hp a) (ltSol p hp b)).trans ha0
  have hG1 : psComp (zpRing p) (ltSol p hp a) (ltSol p hp b) 1
      = (zpRing p).mul a b := by
    rw [psComp_coeff_one (zpRing p) (ltSol p hp a) (ltSol p hp b),
      show ltSol p hp a 1 = a from rfl,
      show ltSol p hp b 1 = b from rfl]
  -- G∘f = f∘G（結合則 ×3 と可換性の往復）
  have heq : psComp (zpRing p)
      (psComp (zpRing p) (ltSol p hp a) (ltSol p hp b)) (ltPoly p)
      = (psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
            (psComp (zpRing p) (ltSol p hp a) (ltSol p hp b)))
          (psPow (zpRing p)
            (psComp (zpRing p) (ltSol p hp a) (ltSol p hp b)) p) := by
    rw [psComp_assoc (zpRing p) (ltSol p hp a) (ltSol p hp b)
        (ltPoly p) hb0 hf0,
      ltSol_comm p hp b,
      ← psComp_assoc (zpRing p) (ltSol p hp a) (ltPoly p)
        (ltSol p hp b) hf0 hb0,
      ltSol_comm p hp a,
      psComp_assoc (zpRing p) (ltPoly p) (ltSol p hp a)
        (ltSol p hp b) ha0 hb0]
    exact psComp_ltPoly_left p hp.1 _ hG0
  obtain ⟨W, _, huniq⟩ := lubin_tate p hp ((zpRing p).mul a b)
  exact huniq _ hG0 hG1 heq

/-! ## 一般の逆元と [-1] の同定 -/

/-- **M76-5a: 一般の逆元** — F([a]X, [−a]X) = [0]X = 0
    （加法 + [0] の正規化。M75 の逆元は a = 1 の場合に相当）。 -/
theorem lt_module_add_neg (p : Nat) (hp : IsPrime p)
    (a : (Zp p).carrier) :
    ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a)
      (ltSol p hp ((zpRing p).neg a)) = psZero (zpRing p) := by
  rw [lt_module_add p hp a ((zpRing p).neg a),
    show (zpRing p).add a ((zpRing p).neg a) = (zpRing p).zero from by
      rw [(zpRing p).add_comm]
      exact (zpRing p).neg_add a]
  exact ltSol_zero p hp

/-- **M76-5b: [-1] 級数の同定**（M75 の ltInv は定義から [−1]）。 -/
theorem ltInv_eq_ltSol_neg_one (p : Nat) (hp : IsPrime p) :
    ltInv p hp = ltSol p hp ((zpRing p).neg ((zpRing p).one)) := rfl

end IUT
