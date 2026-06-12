/-
  IUT/EisensteinRing.lean — M82F（Eisenstein 拡大環
  O = ℤ_p[[X]]/(X^{p−1} + π) の自前構成）

  M81F は奇素数 p で Lubin–Tate 形式群の π-捻れ点が pℤ_p の中では
  自明（x = 0）であることを示した。非自明な捻れ点は
  π + λ^{p−1} = 0 の根 λ として**分岐拡大**にのみ住む。本ファイルは
  その住処の骨格 — Eisenstein 多項式 E = X^{p−1} + π による剰余環
  **O := ℤ_p[[X]]/(E)** — を Quot で一から構成し、一意化元
  λ := X mod E が **λ^{p−1} = −π**、さらに **π·λ + λ^p = 0**
  （λ は LT 多項式 f(T) = πT + T^p の文字通りの根）を満たすことを
  機械検証する。

  * M82F-1 `eisPoly` / `eisRel` / `idealRel_*` — Eisenstein 多項式
    E = X^{p−1} + π と単項イデアル (E) による合同（一般可換環での
    refl・symm・trans・add/neg/mul 両立を M42 負元簿記で証明）
  * M82F-2 `EisCarrier` / `eisAdd` / `eisNeg` / `eisMul` — 商の演算
    （Quot.lift の二重持ち上げ、well-definedness は
    (a+c)−(b+c) = a−b・(ac)−(bc) = (a−b)c = (hc)·E 等の明示証人）
  * M82F-3 `eisRing` — **O は可換環**（各法則は代表元の psRing 法則 +
    congrArg (Quot.mk)、Quot.sound 不要）
  * M82F-4 `eisOf` / `eisLambda` — 構造射 ℤ_p → O（psConstHom の像の
    Quot.mk、環準同型）と一意化元 λ = X mod E
  * M82F-5 `eis_rpow_mk` / `eis_rpow_X` / `eis_lambda_pow` —
    **λ^{p−1} = −π in O**（X^{p−1} − (−π) = 1·E、証人は 1。
    X^{p−1} = psMono (p−1) は psMono_pow）
  * M82F-6 `eis_exact` / `eis_one_ne_zero` — **O ≠ 0**（1 ≡ 0 なら
    1 = h₀·π を定数項で読み取り、レベル 1 射影 proj_p_zero で
    p ∣ 1 の矛盾、not_dvd_one）
  * M82F-7 `eisOf_lambda_torsion_shape` — **π·λ + λ^p = 0 in O**:
    λ は f(T) = πT + T^p の根、すなわち分岐拡大に住む最初の
    非自明捻れ点の骨格（指数分割 p = (p−1)+1 + M82F-5 + add_neg）

  λ での形式群の点の群 F(m_O)・O の整域性/完備性・Galois 作用は
  未形式化。これは全分岐拡大 ℚ_p(λ)/ℚ_p（次数 p−1）の環骨格。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.TorsionTrivial
import IUT.FormalGroupExists

namespace IUT

/-! ## Eisenstein 多項式と (E)-合同 -/

/-- **M82F-1a: Eisenstein 多項式** E = X^{p−1} + π（π = p ∈ ℤ_p）。 -/
def eisPoly (p : Nat) : PS (zpRing p) :=
  psAdd (zpRing p) (psMono (zpRing p) (p - 1))
    (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)))

/-- **M82F-1b: (E)-合同** — f ≡ g iff f − g ∈ (E)。 -/
def eisRel (p : Nat) (f g : PS (zpRing p)) : Prop :=
  ∃ h : PS (zpRing p),
    psAdd (zpRing p) f (psNeg (zpRing p) g) = psMul (zpRing p) h (eisPoly p)

/-- 一般可換環での単項イデアル合同（eisRel の一般形、定義一致）。 -/
def idealRel (S : CRing) (E f g : S.carrier) : Prop :=
  ∃ h : S.carrier, S.add f (S.neg g) = S.mul h E

/-- 反射律: f − f = 0 = 0·E。 -/
theorem idealRel_refl (S : CRing) (E f : S.carrier) : idealRel S E f f := by
  refine ⟨S.zero, ?_⟩
  rw [CRing.add_neg S f, CRing.zero_mul S E]

/-- 対称律: g − f = −(f − g) = (−h)·E。 -/
theorem idealRel_symm (S : CRing) (E : S.carrier) {f g : S.carrier}
    (h : idealRel S E f g) : idealRel S E g f := by
  obtain ⟨w, hw⟩ := h
  refine ⟨S.neg w, ?_⟩
  rw [CRing.neg_mul S w E, ← hw, CRing.neg_add_dist S f (S.neg g),
    CRing.neg_neg S g]
  exact S.add_comm g (S.neg f)

/-- 推移律: f − k = (f − g) + (g − k) = (h₁ + h₂)·E。 -/
theorem idealRel_trans (S : CRing) (E : S.carrier) {f g k : S.carrier}
    (h1 : idealRel S E f g) (h2 : idealRel S E g k) : idealRel S E f k := by
  obtain ⟨w1, hw1⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  refine ⟨S.add w1 w2, ?_⟩
  have key : S.add (S.add f (S.neg g)) (S.add g (S.neg k))
      = S.add f (S.neg k) := by
    rw [S.add_assoc f (S.neg g) (S.add g (S.neg k)),
      ← S.add_assoc (S.neg g) g (S.neg k), S.neg_add g, S.zero_add]
  rw [← key, hw1, hw2, ← CRing.right_distrib S w1 w2 E]

/-- 右加法両立: (a+c) − (b+c) = a − b（証人は同じ h）。 -/
theorem idealRel_add_right (S : CRing) (E c : S.carrier) {a b : S.carrier}
    (h : idealRel S E a b) : idealRel S E (S.add a c) (S.add b c) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  rw [CRing.neg_add_dist S b c, CRing.add_add_add_comm S a c (S.neg b) (S.neg c),
    CRing.add_neg S c, CRing.add_zero S (S.add a (S.neg b))]
  exact hw

/-- 左加法両立（可換性で右に帰着）。 -/
theorem idealRel_add_left (S : CRing) (E c : S.carrier) {a b : S.carrier}
    (h : idealRel S E a b) : idealRel S E (S.add c a) (S.add c b) := by
  rw [S.add_comm c a, S.add_comm c b]
  exact idealRel_add_right S E c h

/-- 右乗法両立: ac − bc = (a − b)c = (hc)·E（証人 h·c）。 -/
theorem idealRel_mul_right (S : CRing) (E c : S.carrier) {a b : S.carrier}
    (h : idealRel S E a b) : idealRel S E (S.mul a c) (S.mul b c) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨S.mul w c, ?_⟩
  rw [← CRing.neg_mul S b c, ← CRing.right_distrib S a (S.neg b) c, hw,
    S.mul_assoc w E c, S.mul_comm E c, ← S.mul_assoc w c E]

/-- 左乗法両立（可換性で右に帰着）。 -/
theorem idealRel_mul_left (S : CRing) (E c : S.carrier) {a b : S.carrier}
    (h : idealRel S E a b) : idealRel S E (S.mul c a) (S.mul c b) := by
  rw [S.mul_comm c a, S.mul_comm c b]
  exact idealRel_mul_right S E c h

/-- 負元両立: (−a) − (−b) = −(a − b) = (−h)·E。 -/
theorem idealRel_neg (S : CRing) (E : S.carrier) {a b : S.carrier}
    (h : idealRel S E a b) : idealRel S E (S.neg a) (S.neg b) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨S.neg w, ?_⟩
  rw [CRing.neg_mul S w E, ← hw, CRing.neg_add_dist S a (S.neg b)]

/-! ## 商の台と演算 -/

/-- **M82F-2a: 商の台** O = ℤ_p[[X]]/(E)。 -/
def EisCarrier (p : Nat) := Quot (eisRel p)

/-- **M82F-2b: 商の加法**（Quot.lift の二重持ち上げ）。 -/
def eisAdd (p : Nat) (x y : EisCarrier p) : EisCarrier p :=
  Quot.lift
    (fun f => Quot.lift
      (fun g => Quot.mk (eisRel p) (psAdd (zpRing p) f g))
      (fun _ _ hg => Quot.sound
        (idealRel_add_left (psRing (zpRing p)) (eisPoly p) f hg)) y)
    (fun _ _ hf => by
      induction y using Quot.ind
      rename_i g
      exact Quot.sound
        (idealRel_add_right (psRing (zpRing p)) (eisPoly p) g hf)) x

/-- **M82F-2c: 商の負元**。 -/
def eisNeg (p : Nat) (x : EisCarrier p) : EisCarrier p :=
  Quot.lift
    (fun f => Quot.mk (eisRel p) (psNeg (zpRing p) f))
    (fun _ _ hf => Quot.sound
      (idealRel_neg (psRing (zpRing p)) (eisPoly p) hf)) x

/-- **M82F-2d: 商の乗法**（Quot.lift の二重持ち上げ）。 -/
def eisMul (p : Nat) (x y : EisCarrier p) : EisCarrier p :=
  Quot.lift
    (fun f => Quot.lift
      (fun g => Quot.mk (eisRel p) (psMul (zpRing p) f g))
      (fun _ _ hg => Quot.sound
        (idealRel_mul_left (psRing (zpRing p)) (eisPoly p) f hg)) y)
    (fun _ _ hf => by
      induction y using Quot.ind
      rename_i g
      exact Quot.sound
        (idealRel_mul_right (psRing (zpRing p)) (eisPoly p) g hf)) x

/-! ## O は可換環 -/

/-- **M82F-3: Eisenstein 環** O = ℤ_p[[X]]/(X^{p−1} + π) は可換環
    （各法則は代表元の psRing 法則 + congrArg (Quot.mk)）。 -/
def eisRing (p : Nat) : CRing where
  carrier := EisCarrier p
  add := eisAdd p
  zero := Quot.mk (eisRel p) (psZero (zpRing p))
  neg := eisNeg p
  mul := eisMul p
  one := Quot.mk (eisRel p) (psOne (zpRing p))
  add_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    induction z using Quot.ind; rename_i k
    exact congrArg (Quot.mk (eisRel p)) ((psRing (zpRing p)).add_assoc f g k)
  zero_add := by
    intro x
    induction x using Quot.ind; rename_i f
    exact congrArg (Quot.mk (eisRel p)) ((psRing (zpRing p)).zero_add f)
  neg_add := by
    intro x
    induction x using Quot.ind; rename_i f
    exact congrArg (Quot.mk (eisRel p)) ((psRing (zpRing p)).neg_add f)
  add_comm := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    exact congrArg (Quot.mk (eisRel p)) ((psRing (zpRing p)).add_comm f g)
  mul_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    induction z using Quot.ind; rename_i k
    exact congrArg (Quot.mk (eisRel p)) ((psRing (zpRing p)).mul_assoc f g k)
  one_mul := by
    intro x
    induction x using Quot.ind; rename_i f
    exact congrArg (Quot.mk (eisRel p)) ((psRing (zpRing p)).one_mul f)
  mul_comm := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    exact congrArg (Quot.mk (eisRel p)) ((psRing (zpRing p)).mul_comm f g)
  left_distrib := by
    intro x y z
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    induction z using Quot.ind; rename_i k
    exact congrArg (Quot.mk (eisRel p))
      ((psRing (zpRing p)).left_distrib f g k)

/-! ## 構造射と一意化元 -/

/-- **M82F-4a: 構造射** ℤ_p → O、a ↦ (a mod E)（psConstHom の合成）。 -/
def eisOf (p : Nat) : RingHom (zpRing p) (eisRing p) where
  map := fun a => Quot.mk (eisRel p) (psC (zpRing p) a)
  map_add := fun a b =>
    congrArg (Quot.mk (eisRel p)) ((psConstHom (zpRing p)).map_add a b)
  map_mul := fun a b =>
    congrArg (Quot.mk (eisRel p)) ((psConstHom (zpRing p)).map_mul a b)
  map_one := congrArg (Quot.mk (eisRel p)) ((psConstHom (zpRing p)).map_one)

/-- **M82F-4b: 一意化元** λ = X mod E。 -/
def eisLambda (p : Nat) : (eisRing p).carrier :=
  Quot.mk (eisRel p) (psX (zpRing p))

/-! ## λ^{p−1} = −π -/

/-- **M82F-5a: 環冪と Quot.mk の交換** — O での冪は代表元の psRing 冪。 -/
theorem eis_rpow_mk (p : Nat) (f : PS (zpRing p)) : ∀ k,
    rpow (eisRing p) (Quot.mk (eisRel p) f) k
      = Quot.mk (eisRel p) (rpow (psRing (zpRing p)) f k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (eisRing p).mul
        (rpow (eisRing p) (Quot.mk (eisRel p) f) k) (Quot.mk (eisRel p) f)
      = Quot.mk (eisRel p)
          ((psRing (zpRing p)).mul (rpow (psRing (zpRing p)) f k) f)
    rw [ih]
    rfl

/-- **M82F-5b: X の冪は単項式** — X^k = psMono k（psX = psMono 1 は
    定義一致、psMono_pow + 1·k = k）。 -/
theorem eis_rpow_X (p : Nat) (k : Nat) :
    rpow (psRing (zpRing p)) (psX (zpRing p)) k = psMono (zpRing p) k := by
  rw [← psPow_eq_rpow (zpRing p) (psX (zpRing p)) k,
    show psPow (zpRing p) (psX (zpRing p)) k = psMono (zpRing p) (1 * k) from
      psMono_pow (zpRing p) 1 k]
  exact congrArg (psMono (zpRing p)) (Nat.one_mul k)

/-- **定理 (M82F-5c): λ^{p−1} = −π in O** — 一意化元の鍵恒等式。
    X^{p−1} − (−π) = X^{p−1} + π = 1·E（証人は 1）。 -/
theorem eis_lambda_pow (p : Nat) (hp : 2 ≤ p) :
    rpow (eisRing p) (eisLambda p) (p - 1)
      = (eisRing p).neg ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) := by
  have h1 : rpow (eisRing p) (eisLambda p) (p - 1)
      = Quot.mk (eisRel p)
          (rpow (psRing (zpRing p)) (psX (zpRing p)) (p - 1)) :=
    eis_rpow_mk p (psX (zpRing p)) (p - 1)
  rw [h1, eis_rpow_X p (p - 1)]
  show Quot.mk (eisRel p) (psMono (zpRing p) (p - 1))
    = Quot.mk (eisRel p)
        (psNeg (zpRing p) (psC (zpRing p) ((toZp p).map ((p : Nat) : Int))))
  apply Quot.sound
  refine ⟨(psRing (zpRing p)).one, ?_⟩
  show (psRing (zpRing p)).add (psMono (zpRing p) (p - 1))
      ((psRing (zpRing p)).neg ((psRing (zpRing p)).neg
        (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)))))
    = (psRing (zpRing p)).mul (psRing (zpRing p)).one (eisPoly p)
  rw [CRing.neg_neg (psRing (zpRing p))
      (psC (zpRing p) ((toZp p).map ((p : Nat) : Int))),
    (psRing (zpRing p)).one_mul (eisPoly p)]
  rfl

/-! ## O ≠ 0 -/

/-- **M82F-6a: 商の分離性** — mk f = mk g なら f ≡ g mod (E)
    （quot_exact の eisRel 版: Prop への Quot.lift）。 -/
theorem eis_exact (p : Nat) {f g : PS (zpRing p)}
    (h : Quot.mk (eisRel p) f = Quot.mk (eisRel p) g) : eisRel p f g := by
  have hf : Quot.lift (eisRel p f)
      (fun _ _ hxy => propext
        ⟨fun hfx => idealRel_trans (psRing (zpRing p)) (eisPoly p) hfx hxy,
         fun hfy => idealRel_trans (psRing (zpRing p)) (eisPoly p) hfy
           (idealRel_symm (psRing (zpRing p)) (eisPoly p) hxy)⟩)
      (Quot.mk (eisRel p) f) := idealRel_refl (psRing (zpRing p)) (eisPoly p) f
  rw [h] at hf
  exact hf

/-- E の定数項は π（X^{p−1} は p ≥ 2 で次数 ≥ 1）。 -/
theorem eisPoly_coeff_zero (p : Nat) (hp : 2 ≤ p) :
    eisPoly p 0 = (toZp p).map ((p : Nat) : Int) := by
  show (zpRing p).add (psMono (zpRing p) (p - 1) 0)
      (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) 0)
    = (toZp p).map ((p : Nat) : Int)
  rw [show psMono (zpRing p) (p - 1) 0 = (zpRing p).zero from
      if_neg (by omega),
    (zpRing p).zero_add]
  rfl

/-- **定理 (M82F-6b): O ≠ 0** — 1 ≡ 0 mod (E) なら定数項で
    1 = h₀·π、レベル 1 射影で 0 = 1 in ℤ/p、すなわち p ∣ 1 の矛盾。 -/
theorem eis_one_ne_zero (p : Nat) (hp : 2 ≤ p) :
    (eisRing p).one ≠ (eisRing p).zero := by
  intro h
  have h' : Quot.mk (eisRel p) (psOne (zpRing p))
      = Quot.mk (eisRel p) (psZero (zpRing p)) := h
  have hrel : ∃ w : PS (zpRing p),
      psAdd (zpRing p) (psOne (zpRing p)) (psNeg (zpRing p) (psZero (zpRing p)))
        = psMul (zpRing p) w (eisPoly p) := eis_exact p h'
  obtain ⟨h₀, hh⟩ := hrel
  -- 定数項の読み取り: 1 + (−0) = 0 + h₀(0)·E(0)
  have h0 : (zpRing p).add (zpRing p).one ((zpRing p).neg (zpRing p).zero)
      = (zpRing p).add (zpRing p).zero
          ((zpRing p).mul (h₀ 0) (eisPoly p 0)) := congrFun hh 0
  rw [CRing.neg_zero (zpRing p), CRing.add_zero (zpRing p) (zpRing p).one,
    (zpRing p).zero_add, eisPoly_coeff_zero p hp] at h0
  -- h0 : 1 = h₀(0)·π。レベル 1 へ射影して p ∣ 1 を導く
  have hproj := congrArg (projRing p 1).map h0
  rw [(projRing p 1).map_one,
    (projRing p 1).map_mul (h₀ 0) ((toZp p).map ((p : Nat) : Int)),
    proj_p_zero p, CRing.mul_zero (zmodRing (p ^ 1))] at hproj
  have hq : Quot.mk (modCong (p ^ 1)).rel 1
      = Quot.mk (modCong (p ^ 1)).rel 0 := hproj
  have hdvd : ((p ^ 1 : Nat) : Int) ∣ (1 - 0 : Int) :=
    quot_exact intGrp (modCong (p ^ 1)) hq
  rw [Nat.pow_one] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  refine not_dvd_one p hp ⟨k, ?_⟩
  generalize hW : ((p : Nat) : Int) * k = W
  rw [hW] at hk
  omega

/-! ## λ は LT 多項式の根 -/

/-- **定理 (M82F-7): π·λ + λ^p = 0 in O** — 一意化元 λ は Lubin–Tate
    多項式 f(T) = πT + T^p の文字通りの根。M81F（pℤ_p 内の自明性）の
    相方として、**分岐拡大に住む最初の非自明捻れ点の骨格**を与える。
    λ^p = λ^{p−1}·λ = (−π)·λ（M82F-5c + 指数分割 p = (p−1)+1）、
    π·λ + (−π)·λ = 0（neg_mul + add_neg）。 -/
theorem eisOf_lambda_torsion_shape (p : Nat) (hp : 2 ≤ p) :
    (eisRing p).add
      ((eisRing p).mul ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
        (eisLambda p))
      (rpow (eisRing p) (eisLambda p) p)
    = (eisRing p).zero := by
  have hpow : rpow (eisRing p) (eisLambda p) p
      = (eisRing p).mul (rpow (eisRing p) (eisLambda p) (p - 1))
          (eisLambda p) :=
    congrArg (rpow (eisRing p) (eisLambda p)) (show p = (p - 1) + 1 by omega)
  rw [hpow, eis_lambda_pow p hp,
    CRing.neg_mul (eisRing p)
      ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) (eisLambda p)]
  exact CRing.add_neg (eisRing p)
    ((eisRing p).mul ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
      (eisLambda p))

end IUT
