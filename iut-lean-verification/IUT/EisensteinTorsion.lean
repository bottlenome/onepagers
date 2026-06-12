/-
  IUT/EisensteinTorsion.lean — M83F（非自明な π-捻れ点 λ の完全認定）

  M81F は奇素数 p で pℤ_p 内の捻れ点が自明（x = 0）であることを示し、
  M82F は分岐拡大の骨格 O = ℤ_p[[X]]/(X^{p−1} + π) と一意化元 λ を
  構成して π·λ + λ^p = 0 を確かめた。本ファイルはその対を完結させ、
  **λ ∈ O は Lubin–Tate 形式群の非自明な π-捻れ点である**ことを
  機械検証する: (i) O 上の f-作用 [πⁿ] を定義し、(ii) λ が全ての
  反復 [πⁿ]（n ≥ 1）で消えること、(iii) λ ≠ 0、(iv) この O-作用が
  pℤ_p の点評価（M78F/M79F）と構造射 eisOf で両立することを示す。

  * M83F-1 `eisF` — O 上の Lubin–Tate 多項式 f(T) = πT + T^p
    （f は二項多項式なので級数評価なしの正直な関数）
  * M83F-2 `eisIter` — [πⁿ]-作用 f^{∘n}（n に関する再帰）
  * M83F-3 `eisF_zero` / `eisIter_zero` — f(0) = 0、よって [πⁿ](0) = 0
  * M83F-4 `eisF_lambda` — **f(λ) = 0**（M82F-7 の言い換え）
  * M83F-5 `lambda_all_torsion` — **[πⁿ]λ = 0（∀ n ≥ 1）**:
    λ は全ての反復で消える捻れ点
  * M83F-6 `eisPoly_coeff_one` / `eis_lambda_ne_zero` — **λ ≠ 0 in O**
    （X ≡ 0 mod (E) なら一次係数で 1 = w₁·π、レベル 1 射影
    proj_p_zero で p ∣ 1 の矛盾、not_dvd_one — eis_one_ne_zero と
    同じ抽出パターン）
  * M83F-7 `eisOf_compat_f` — **基底作用との両立**
    eisOf(f(x)) = eisF(eisOf(x))：構造射 ℤ_p → O は点レベルの f
    （M78F の zpEval_ltPoly）と O 上の eisF を絡み合わせる
  * M83F-8 `eisIter_compat` — **[πⁿ]-作用の完全両立**
    eisOf([πⁿ](x)) = eisIterⁿ(eisOf(x))（n の帰納 + M79F-5 の
    漸化式 + M83F-7、witness は zpEval_closed の明示証人）

  以上で「非自明な捻れ点 λ の完全認定」
  （λ ≠ 0 ∧ [πⁿ]λ = 0 ∧ 基底作用との両立）が揃う。
  Λ₁ の完全な記述（位数 p の群であること・全 p−1 個の共役根）・
  O の整域性・Galois 作用は未形式化。p = 2 を除外するのは λ ≠ 0 の
  係数比較が E₁ = 1 で破綻するため（M81F と同じ正直申告）。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.EisensteinRing

namespace IUT

/-! ## O 上の Lubin–Tate 多項式と [πⁿ]-作用 -/

/-- **M83F-1: O 上の LT 多項式** f(T) = πT + T^p（π = p の eisOf 像）。
    f は二項多項式なので級数評価なしの正直な関数として定義できる。 -/
def eisF (p : Nat) (t : (eisRing p).carrier) : (eisRing p).carrier :=
  (eisRing p).add
    ((eisRing p).mul ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) t)
    (rpow (eisRing p) t p)

/-- **M83F-2: [πⁿ]-作用** — f の n 回反復（O の点への作用）。 -/
def eisIter (p : Nat) : Nat → (eisRing p).carrier → (eisRing p).carrier
  | 0, t => t
  | n + 1, t => eisIter p n (eisF p t)

/-! ## 0 と λ での f の値 -/

/-- **M83F-3a: f(0) = 0** — π·0 + 0^p = 0。 -/
theorem eisF_zero (p : Nat) (hp : 2 ≤ p) :
    eisF p ((eisRing p).zero) = (eisRing p).zero := by
  show (eisRing p).add
      ((eisRing p).mul ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
        ((eisRing p).zero))
      (rpow (eisRing p) ((eisRing p).zero) p)
    = (eisRing p).zero
  rw [CRing.mul_zero (eisRing p)
      ((eisOf p).map ((toZp p).map ((p : Nat) : Int))),
    rpow_zero_pos (eisRing p) p (by omega)]
  exact (eisRing p).zero_add (eisRing p).zero

/-- **M83F-4: f(λ) = 0** — λ は f の文字通りの根（M82F-7 の言い換え、
    定義一致）。 -/
theorem eisF_lambda (p : Nat) (hp : 2 ≤ p) :
    eisF p (eisLambda p) = (eisRing p).zero :=
  eisOf_lambda_torsion_shape p hp

/-- **M83F-3b: [πⁿ](0) = 0** — 0 は全ての反復で固定（n の帰納 +
    M83F-3a）。 -/
theorem eisIter_zero (p : Nat) (hp : 2 ≤ p) : ∀ n,
    eisIter p n ((eisRing p).zero) = (eisRing p).zero := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show eisIter p n (eisF p ((eisRing p).zero)) = (eisRing p).zero
    rw [eisF_zero p hp]
    exact ih

/-! ## λ は全ての [πⁿ]（n ≥ 1）で消える -/

/-- **定理 (M83F-5): [πⁿ]λ = 0（∀ n ≥ 1）** — λ は全ての正の反復で
    消える捻れ点: [πⁿ⁺¹]λ = [πⁿ](f(λ)) = [πⁿ](0) = 0。 -/
theorem lambda_all_torsion (p : Nat) (hp : 2 ≤ p) : ∀ n, 1 ≤ n →
    eisIter p n (eisLambda p) = (eisRing p).zero := by
  intro n hn
  cases n with
  | zero => exact absurd hn (by omega)
  | succ m =>
    show eisIter p m (eisF p (eisLambda p)) = (eisRing p).zero
    rw [eisF_lambda p hp]
    exact eisIter_zero p hp m

/-! ## λ ≠ 0（捻れの非自明性） -/

/-- E の一次係数は 0（p ≥ 3 で X^{p−1} は次数 ≥ 2、定数項 π は
    次数 0）。p = 2 では E₁ = 1 となりこの補題が破綻する。 -/
theorem eisPoly_coeff_one (p : Nat) (hodd : 3 ≤ p) :
    eisPoly p 1 = (zpRing p).zero := by
  show (zpRing p).add (psMono (zpRing p) (p - 1) 1)
      (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1)
    = (zpRing p).zero
  rw [show psMono (zpRing p) (p - 1) 1 = (zpRing p).zero from
      if_neg (by omega),
    show psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1 = (zpRing p).zero
      from if_neg (by omega),
    (zpRing p).zero_add]

/-- **定理 (M83F-6): λ ≠ 0 in O** — 捻れは非自明。X ≡ 0 mod (E) なら
    X − 0 = w·E の一次係数で 1 = w₀·E₁ + w₁·E₀ = w₁·π（E₁ = 0 は
    p ≥ 3）、レベル 1 射影で 0 = 1 in ℤ/p、すなわち p ∣ 1 の矛盾。 -/
theorem eis_lambda_ne_zero (p : Nat) (hodd : 3 ≤ p) :
    eisLambda p ≠ (eisRing p).zero := by
  intro h
  have h' : Quot.mk (eisRel p) (psX (zpRing p))
      = Quot.mk (eisRel p) (psZero (zpRing p)) := h
  obtain ⟨w, hh⟩ := eis_exact p h'
  -- 一次係数の読み取り: 1 + (−0) = (0 + w₀·E₁) + w₁·E₀
  have h1 : (zpRing p).add (zpRing p).one ((zpRing p).neg (zpRing p).zero)
      = (zpRing p).add
          ((zpRing p).add (zpRing p).zero
            ((zpRing p).mul (w 0) (eisPoly p 1)))
          ((zpRing p).mul (w 1) (eisPoly p 0)) := congrFun hh 1
  rw [CRing.neg_zero (zpRing p), CRing.add_zero (zpRing p) (zpRing p).one,
    eisPoly_coeff_one p hodd, CRing.mul_zero (zpRing p) (w 0),
    (zpRing p).zero_add, (zpRing p).zero_add,
    eisPoly_coeff_zero p (by omega)] at h1
  -- h1 : 1 = w₁·π。レベル 1 へ射影して p ∣ 1 を導く
  have hproj := congrArg (projRing p 1).map h1
  rw [(projRing p 1).map_one,
    (projRing p 1).map_mul (w 1) ((toZp p).map ((p : Nat) : Int)),
    proj_p_zero p, CRing.mul_zero (zmodRing (p ^ 1))] at hproj
  have hq : Quot.mk (modCong (p ^ 1)).rel 1
      = Quot.mk (modCong (p ^ 1)).rel 0 := hproj
  have hdvd : ((p ^ 1 : Nat) : Int) ∣ (1 - 0 : Int) :=
    quot_exact intGrp (modCong (p ^ 1)) hq
  rw [Nat.pow_one] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  refine not_dvd_one p (by omega) ⟨k, ?_⟩
  generalize hW : ((p : Nat) : Int) * k = W
  rw [hW] at hk
  omega

/-! ## 基底作用との両立 -/

/-- **定理 (M83F-7): 構造射は f を絡み合わせる** —
    eisOf(f(x)) = eisF(eisOf(x))（x ∈ pℤ_p）。点レベルの
    f(x) = πx + x^p（M78F-8）を環準同型 eisOf で運ぶだけ:
    **分岐側の作用は基底側の作用の延長**。 -/
theorem eisOf_compat_f (p : Nat) (hp : 2 ≤ p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    (eisOf p).map (zpEval p (ltPoly p) x e hx)
      = eisF p ((eisOf p).map x) := by
  rw [zpEval_ltPoly p hp x e hx, (eisOf p).map_add, (eisOf p).map_mul,
    ringHom_rpow (eisOf p) x p]
  rfl

/-- **定理 (M83F-8): [πⁿ]-作用の完全両立** —
    eisOf([πⁿ](x)) = eisIterⁿ(eisOf(x))（∀ n、x ∈ pℤ_p）。
    n の帰納: n = 0 は X(x) = x（M77-6c）、n+1 は点レベルの漸化式
    [πⁿ⁺¹](x) = [πⁿ](f(x))（M79F-5、witness は zpEval_closed の
    明示証人）に IH を f(x) で適用し M83F-7 で締める。 -/
theorem eisIter_compat (p : Nat) (hp : 2 ≤ p) : ∀ n (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    (eisOf p).map (zpEval p (ltIter p n) x e hx)
      = eisIter p n ((eisOf p).map x) := by
  intro n
  induction n with
  | zero =>
    intro x e hx
    exact congrArg (eisOf p).map (zpEval_X p hp x e hx)
  | succ n ih =>
    intro x e hx
    rw [zpEval_ltIter_succ p hp n x e hx,
      ih (zpEval p (ltPoly p) x e hx)
        ((zpRing p).mul e (zpEval p (psShift (zpRing p) (ltPoly p)) x e hx))
        (zpEval_closed p hp (ltPoly p) (ltPoly_coeff_zero p hp) x e hx),
      eisOf_compat_f p hp x e hx]
    rfl

end IUT
