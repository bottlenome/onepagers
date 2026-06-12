/-
  IUT/FormalGroupErr.lean — M56（LT 誤差の係数 p-整除性と誤差/p の構成: 形式群第六層）

  M55 の「形式群方程式の両辺は mod p で一致する」を、係数ごとの
  **p-整除性**と choice-free な**除算 E/p の実構成**に変換する。
  これは M48（一変数誤差の整除性）→ M49（係数再帰）のパイプラインの
  二変数版の前半であり、次層の総次数帰納で「誤差を p で割って
  次の係数を決める」操作を供給する。

  * M56-1 `lt2Err` — **二変数 LT 誤差** E(F) := f∘F − F(f(X), f(Y))
    （f = pX + X^p。PS2 の環構造 = psRing(psRing ℤ_p) の加法と反元）
    と係数透過補題・**方程式との同値** E = 0 ⟺ IsLTFormalGroup の
    方程式成立
  * M56-2 `ps2Map_zero_cond` — F₀₀ = 0（ℤ_p）⟹ F̄₀₀ = 0（mod p）
  * M56-3 `lt2Err_reduction` — **誤差の mod-p 消滅（級数形）**
    Φ(E) = 0（M55-7 の両辺一致を x − x = 0 に変換）
  * M56-4 `lt2Err_divisible` — **全係数の p-整除性**
    ∃ e, E_{j,i} = p·e（M43 の zp_dvd_p_iff: 整除 ⟺ レベル1で消滅）
  * M56-5 `lt2Div` / `lt2Div_cancel` — **誤差/p の実構成**（M43 の
    zpDivP による choice-free な全係数一斉除算）と除算恒等式
    p·(E/p)_{j,i} = E_{j,i}

  ロードマップ: 次層で ps2Comp1 の対角先頭項分解（係数 F_{b,a} の
  方程式 F_{b,a}·(p^{a+b} − p) = E' 型）→ 総次数の係数再帰による
  LT 形式群法則の存在。全て選択公理不使用。
-/
import IUT.Frobenius2

namespace IUT

/-! ## 二変数 LT 誤差 -/

/-- **M56-1a: 二変数 LT 誤差** E(F) := f∘F − F(f(X), f(Y))
    （f = pX + X^p）。 -/
def lt2Err (p : Nat) (F : PS2 (zpRing p)) : PS2 (zpRing p) :=
  psAdd (psRing (zpRing p))
    (ps2Comp1 (zpRing p) (ltPoly p) F)
    (psNeg (psRing (zpRing p))
      (ps2Comp2 (zpRing p) F (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p))))

/-- 係数透過補題: E_{j,i} = (f∘F)_{j,i} − F(f(X), f(Y))_{j,i}。 -/
theorem lt2Err_coeff (p : Nat) (F : PS2 (zpRing p)) (j i : Nat) :
    lt2Err p F j i
      = (zpRing p).add (ps2Comp1 (zpRing p) (ltPoly p) F j i)
          ((zpRing p).neg (ps2Comp2 (zpRing p) F
            (psC (psRing (zpRing p)) (ltPoly p))
            (psMap (psConstHom (zpRing p)) (ltPoly p)) j i)) := rfl

/-- **定理 (M56-1b): 誤差消滅 ⟺ 方程式成立** — E(F) = 0 は
    IsLTFormalGroup の方程式成分と同値（次層の再帰構成の終着点）。 -/
theorem lt2Err_zero_iff_equation (p : Nat) (F : PS2 (zpRing p)) :
    lt2Err p F = (psRing (psRing (zpRing p))).zero
      ↔ ps2Comp1 (zpRing p) (ltPoly p) F
        = ps2Comp2 (zpRing p) F (psC (psRing (zpRing p)) (ltPoly p))
            (psMap (psConstHom (zpRing p)) (ltPoly p)) := by
  constructor
  · intro h
    funext j i
    exact CRing.eq_of_sub_eq_zero (zpRing p)
      (congrFun (congrFun h j) i)
  · intro h
    funext j i
    show (zpRing p).add (ps2Comp1 (zpRing p) (ltPoly p) F j i)
        ((zpRing p).neg (ps2Comp2 (zpRing p) F
          (psC (psRing (zpRing p)) (ltPoly p))
          (psMap (psConstHom (zpRing p)) (ltPoly p)) j i))
      = (zpRing p).zero
    rw [h]
    exact CRing.add_neg (zpRing p) _

/-! ## mod-p 消滅から係数整除性へ -/

/-- **M56-2: 定数項条件の還元** — F₀₀ = 0（ℤ_p）なら F̄₀₀ = 0（mod p）。 -/
theorem ps2Map_zero_cond (p : Nat) (F : PS2 (zpRing p))
    (hF0 : F 0 0 = (zpRing p).zero) :
    ps2Map (projRing p 1) F 0 0 = (zmodRing (p ^ 1)).zero := by
  show (projRing p 1).map (F 0 0) = (zmodRing (p ^ 1)).zero
  rw [hF0]
  exact RingHom.map_zero (projRing p 1)

/-- **定理 (M56-3): 誤差の mod-p 消滅（級数形）** — Φ(E(F)) = 0
    （M55-7 の両辺一致を psMap の加法・反元保存で x − x = 0 に変換）。 -/
theorem lt2Err_reduction (p : Nat) (hp : IsPrime p) (F : PS2 (zpRing p))
    (hF : ps2Map (projRing p 1) F 0 0 = (zmodRing (p ^ 1)).zero) :
    ps2Map (projRing p 1) (lt2Err p F)
      = (psRing (psRing (zmodRing (p ^ 1)))).zero := by
  show psMap (psRingHom (projRing p 1))
      (psAdd (psRing (zpRing p))
        (ps2Comp1 (zpRing p) (ltPoly p) F)
        (psNeg (psRing (zpRing p))
          (ps2Comp2 (zpRing p) F (psC (psRing (zpRing p)) (ltPoly p))
            (psMap (psConstHom (zpRing p)) (ltPoly p)))))
    = (psRing (psRing (zmodRing (p ^ 1)))).zero
  rw [psMap_add (psRingHom (projRing p 1)) _ _,
    psMap_neg (psRingHom (projRing p 1)) _]
  have heq : psMap (psRingHom (projRing p 1))
        (ps2Comp1 (zpRing p) (ltPoly p) F)
      = psMap (psRingHom (projRing p 1))
          (ps2Comp2 (zpRing p) F (psC (psRing (zpRing p)) (ltPoly p))
            (psMap (psConstHom (zpRing p)) (ltPoly p))) :=
    lt_error_vanishes_modp p hp F hF
  rw [heq]
  exact CRing.add_neg (psRing (psRing (zmodRing (p ^ 1)))) _

/-- **定理 (M56-4): 全係数の p-整除性** — ∃ e, E_{j,i} = p·e
    （M43 の zp_dvd_p_iff: 整除 ⟺ レベル 1 で消滅）。 -/
theorem lt2Err_divisible (p : Nat) (hp : IsPrime p) (F : PS2 (zpRing p))
    (hF0 : F 0 0 = (zpRing p).zero) (j i : Nat) :
    ∃ e, lt2Err p F j i
      = zpMul p ((toZp p).map ((p : Nat) : Int)) e := by
  apply (zp_dvd_p_iff p hp.1 _).mpr
  exact congrFun (congrFun
    (lt2Err_reduction p hp F (ps2Map_zero_cond p F hF0)) j) i

/-! ## 誤差/p の実構成 -/

/-- **M56-5a: 誤差/p** — M43 の zpDivP による choice-free な
    全係数一斉除算。 -/
def lt2Div (p : Nat) (hp : 2 ≤ p) (F : PS2 (zpRing p)) : PS2 (zpRing p) :=
  fun j i => zpDivP p hp (lt2Err p F j i)

/-- **定理 (M56-5b): 除算恒等式** — p·(E/p)_{j,i} = E_{j,i}
    （F₀₀ = 0 のとき。次層の係数再帰で「誤差を p で割って次の係数を
    決める」操作の正当化）。 -/
theorem lt2Div_cancel (p : Nat) (hp : IsPrime p) (F : PS2 (zpRing p))
    (hF0 : F 0 0 = (zpRing p).zero) (j i : Nat) :
    zpMul p ((toZp p).map ((p : Nat) : Int)) (lt2Div p hp.1 F j i)
      = lt2Err p F j i :=
  zpDivP_mul_cancel p hp.1 (lt2Err p F j i)
    (congrFun (congrFun
      (lt2Err_reduction p hp F (ps2Map_zero_cond p F hF0)) j) i)

end IUT
