/-
  IUT/FormalGroupEq.lean — M52（形式群方程式の定式化: 形式群第三層）

  Lubin–Tate 形式群法則の方程式

    f∘F = F(f(X), f(Y))   （f = pX + X^p、F ≡ X + Y mod 総次数 2）

  を機械可読な形に定式化する。f(X)・f(Y) は **1 変数級数の二方向注入**
  inX f := psC(psRing R) f（Y について定数）、inY f := psMap(psC) f
  （X について定数）であり、M50 の代入 ps2Comp1 がこの注入と整合する
  こと（f∘X-座標 = inX f・f∘Y-座標 = inY f）を完全証明する。

  サニティアンカーとして **f = X（恒等）のとき方程式が任意の F
  （F₀₀ = 0）で成立する**ことを示す — M50–M52 の全機構（ps2Comp1・
  ps2Comp2・座標・注入）が一周して噛み合うことの機械的検証。

  * M52-1 `ps2Comp1_coordX` — **f∘X = inX f**（X 座標への代入は
    X 方向注入。j = 0 で k = i にスパイク、j ≥ 1 で消滅）
  * M52-2 `ps2Comp1_coordY` — **f∘Y = inY f**（同、Y 方向）
  * M52-3 `psMap_constHom_psX` — inY X = Y（注入は座標を座標へ）
  * M52-4 `fgl_equation_identity` — **恒等 f = X での方程式成立**
    （左辺 = F は M50、右辺 = F(X,Y) = F は M51 の恒等代入）
  * M52-5 `IsLTFormalGroup` — **LT 形式群法則の述語**（一次条件
    F₀₀ = 0・F₁₀ = F₀₁ = 1 と方程式）と注入の定数項消滅
    （代入の truncation 妥当性）

  ロードマップ: 次層で存在（総次数の係数帰納 — M49 のスキーマの
  二変数版）と一意性。全て選択公理不使用。
-/
import IUT.FormalGroupSub

namespace IUT

/-! ## 座標への代入 = 注入 -/

/-- **定理 (M52-1): f∘X = inX f** — X 座標への代入は X 方向注入
    psC(psRing R) f に一致。 -/
theorem ps2Comp1_coordX (R : CRing) (f : PS R) :
    ps2Comp1 R f (ps2X R) = psC (psRing R) f := by
  funext j i
  show rsum R (fun k => R.mul (f k) (psPow (psRing R) (ps2X R) k j i))
      (i + j + 1) = psC (psRing R) f j i
  have hterm : ∀ k, psPow (psRing R) (ps2X R) k j i
      = (if j = 0 then (if i = k then R.one else R.zero) else R.zero) := by
    intro k
    rw [ps2X_pow R k]
    show (if j = 0 then psMono R k else (psRing R).zero) i = _
    cases Nat.decEq j 0 with
    | isTrue hj =>
      rw [if_pos hj, if_pos hj]
      rfl
    | isFalse hj =>
      rw [if_neg hj, if_neg hj]
      rfl
  cases Nat.decEq j 0 with
  | isTrue hj =>
    have hc : rsum R (fun k => R.mul (f k)
          (psPow (psRing R) (ps2X R) k j i)) (i + j + 1)
        = R.mul (f i) (psPow (psRing R) (ps2X R) i j i) :=
      rsum_single R _ i (i + j + 1) (by omega) (fun k _ hk => by
        rw [hterm k, if_pos hj, if_neg (fun h => hk h.symm)]
        exact R.mul_zero _)
    rw [hc, hterm i, if_pos hj, if_pos rfl, CRing.mul_one R (f i)]
    show f i = (if j = 0 then f else (psRing R).zero) i
    rw [if_pos hj]
  | isFalse hj =>
    have hc : rsum R (fun k => R.mul (f k)
          (psPow (psRing R) (ps2X R) k j i)) (i + j + 1)
        = rsum R (fun _ => R.zero) (i + j + 1) :=
      rsum_congr R (i + j + 1) (fun k _ => by
        rw [hterm k, if_neg hj]
        exact R.mul_zero _)
    rw [hc, rsum_const_zero]
    show R.zero = (if j = 0 then f else (psRing R).zero) i
    rw [if_neg hj]
    rfl

/-- **定理 (M52-2): f∘Y = inY f** — Y 座標への代入は Y 方向注入
    psMap (psConstHom R) f に一致。 -/
theorem ps2Comp1_coordY (R : CRing) (f : PS R) :
    ps2Comp1 R f (ps2Y R) = psMap (psConstHom R) f := by
  funext j i
  show rsum R (fun k => R.mul (f k) (psPow (psRing R) (ps2Y R) k j i))
      (i + j + 1) = psC R (f j) i
  have hterm : ∀ k, psPow (psRing R) (ps2Y R) k j i
      = (if j = k then (if i = 0 then R.one else R.zero) else R.zero) := by
    intro k
    rw [ps2Y_pow R k]
    show (if j = k then (psRing R).one else (psRing R).zero) i = _
    cases Nat.decEq j k with
    | isTrue hj =>
      rw [if_pos hj, if_pos hj]
      rfl
    | isFalse hj =>
      rw [if_neg hj, if_neg hj]
      rfl
  cases Nat.decEq i 0 with
  | isTrue hi =>
    have hc : rsum R (fun k => R.mul (f k)
          (psPow (psRing R) (ps2Y R) k j i)) (i + j + 1)
        = R.mul (f j) (psPow (psRing R) (ps2Y R) j j i) :=
      rsum_single R _ j (i + j + 1) (by omega) (fun k _ hk => by
        rw [hterm k, if_neg (fun h => hk h.symm)]
        exact R.mul_zero _)
    rw [hc, hterm j, if_pos rfl, if_pos hi, CRing.mul_one R (f j),
      show psC R (f j) i = f j from by
        show (if i = 0 then f j else R.zero) = f j
        rw [if_pos hi]]
  | isFalse hi =>
    have hc : rsum R (fun k => R.mul (f k)
          (psPow (psRing R) (ps2Y R) k j i)) (i + j + 1)
        = rsum R (fun _ => R.zero) (i + j + 1) :=
      rsum_congr R (i + j + 1) (fun k _ => by
        rw [hterm k]
        cases Nat.decEq j k with
        | isTrue hj =>
          rw [if_pos hj, if_neg hi]
          exact R.mul_zero _
        | isFalse hj =>
          rw [if_neg hj]
          exact R.mul_zero _)
    rw [hc, rsum_const_zero,
      show psC R (f j) i = R.zero from by
        show (if i = 0 then f j else R.zero) = R.zero
        rw [if_neg hi]]

/-- **M52-3**: Y 方向注入は X 座標を Y 座標に送る（inY X = Y）。 -/
theorem psMap_constHom_psX (R : CRing) :
    psMap (psConstHom R) (psX R) = ps2Y R := by
  funext j i
  show psC R (psX R j) i = ps2Y R j i
  cases Nat.decEq j 1 with
  | isTrue hj =>
    rw [show psX R j = R.one from if_pos hj,
      show ps2Y R j = (psRing R).one from if_pos hj]
    rfl
  | isFalse hj =>
    rw [show psX R j = R.zero from if_neg hj,
      show ps2Y R j = (psRing R).zero from if_neg hj]
    show psC R R.zero i = psZero R i
    rw [psC_zero R]

/-! ## サニティアンカー: 恒等 f = X での方程式成立 -/

/-- **定理 (M52-4): 恒等での形式群方程式** — f = X のとき任意の F
    （F₀₀ = 0）で X∘F = F(X∘X座標, X∘Y座標) が成立。M50–M52 の
    全機構が一周して噛み合うことの機械検証。 -/
theorem fgl_equation_identity (R : CRing) (F : PS2 R) (hF : F 0 0 = R.zero) :
    ps2Comp1 R (psX R) F
      = ps2Comp2 R F (ps2Comp1 R (psX R) (ps2X R))
          (ps2Comp1 R (psX R) (ps2Y R)) := by
  rw [ps2Comp1_X R F hF, ps2Comp1_coordX R (psX R),
    ps2Comp1_coordY R (psX R), psMap_constHom_psX R]
  exact (ps2Comp2_coords R F).symm

/-! ## LT 形式群法則の述語 -/

/-- **M52-5: Lubin–Tate 形式群法則の述語** — 一次条件
    （F₀₀ = 0・F₁₀ = F₀₁ = 1）と方程式 f∘F = F(f(X), f(Y))
    （f = pX + X^p、f(X)・f(Y) は二方向注入）。 -/
def IsLTFormalGroup (p : Nat) (F : PS2 (zpRing p)) : Prop :=
  F 0 0 = (zpRing p).zero ∧
  F 0 1 = (zpRing p).one ∧
  F 1 0 = (zpRing p).one ∧
  ps2Comp1 (zpRing p) (ltPoly p) F
    = ps2Comp2 (zpRing p) F (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p))

/-- 注入 f(X) の定数項は 0（代入の truncation 妥当性）。 -/
theorem inX_ltPoly_00 (p : Nat) (hp : 2 ≤ p) :
    psC (psRing (zpRing p)) (ltPoly p) 0 0 = (zpRing p).zero := by
  show ltPoly p 0 = (zpRing p).zero
  exact ltPoly_coeff_zero p hp

/-- 注入 f(Y) の定数項は 0。 -/
theorem inY_ltPoly_00 (p : Nat) (hp : 2 ≤ p) :
    psMap (psConstHom (zpRing p)) (ltPoly p) 0 0 = (zpRing p).zero := by
  show ltPoly p 0 = (zpRing p).zero
  exact ltPoly_coeff_zero p hp

end IUT
