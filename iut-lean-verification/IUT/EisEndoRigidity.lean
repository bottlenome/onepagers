/-
  IUT/EisEndoRigidity.lean — M95（自己同型の上界骨格: 柱B）

  柱B の残段「構成した σ_ζ 族が Galois 群の**全て**であること」
  （自己同型の分類）の第一段。M86F〜M89F は σ_ζ を**構成**した
  （下界 = 存在側）。本層はその対をなす**上界側の骨格**:
  **ℤ_p を固定する任意の環自己準同型 σ は λ を Λ₁ に送る**ことを
  仮定なしで証明し、整域性（M90F の NoZeroDiv、M93F が witness 版を
  整備中）の下で「σ(λ) = 0 または σ(λ) は Eisenstein 根」の分類に
  落とす。鍵は **σ と f(t) = πt + t^p の可換性**（π = eisOf(p) が
  固定されることと環準同型性だけから従う — Galois 性は不要）。

  これにより「O の ℤ_p-自己準同型は λ の行き先で測られ、行き先は
  円分体 Λ₁ の中に剛性的に拘束される」という mono-anabelian 的
  上界が機械検証される。残るギャップは「Eisenstein 根は共役
  ω(a)λ で尽くされる」（根の個数 ≤ p−1 = 因数定理）のみ。

  * M95-1 `endo_eisF_comm` — **σ ∘ f = f ∘ σ**（ℤ_p 固定のみから）
  * M95-2 `endo_eisIter_comm` / `endo_preserves_torsion` —
    反復可換と捻れ塔の保存（任意の ℤ_p-固定自己準同型へ一般化）
  * M95-3 `endo_lambda_torsion` — **σ(λ) ∈ Λ₁（本丸・無条件）**
  * M95-4 `endo_lambda_classify` / `endo_lambda_root` — NoZeroDiv の
    下での分類: σ(λ) = 0 ∨ σ(λ)^{p−1} = −π
  * M95-5 `EisEndoRigidityData` / `eisEndoRigidity` /
    `eisEndoRigidity_exists` — 総括

  根の個数 ≤ p−1（因数定理）→ σ(λ) = ω(a)λ の完全分類・
  単射性からの σ(λ) ≠ 0 の導出は次層。全て選択公理不使用。
-/
import IUT.EisensteinTower
import IUT.EisensteinUpper

namespace IUT

/-! ## σ と f の可換性（ℤ_p 固定のみから） -/

/-- **定理 (M95-1): σ ∘ f = f ∘ σ** — ℤ_p の像を固定する任意の
    環自己準同型は f(t) = πt + t^p と可換（map_add・map_mul・
    ringHom_rpow + π の固定のみ。Galois 性は不要）。 -/
theorem endo_eisF_comm (p : Nat) (σ : RingHom (eisRing p) (eisRing p))
    (hfix : ∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z) :
    ∀ t, σ.map (eisF p t) = eisF p (σ.map t) := by
  intro t
  show σ.map ((eisRing p).add
      ((eisRing p).mul ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) t)
      (rpow (eisRing p) t p))
    = (eisRing p).add
      ((eisRing p).mul ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
        (σ.map t))
      (rpow (eisRing p) (σ.map t) p)
  rw [σ.map_add, σ.map_mul, ringHom_rpow σ t p,
    hfix ((toZp p).map ((p : Nat) : Int))]

/-- **定理 (M95-2a): 反復との可換** σ ∘ [πⁿ] = [πⁿ] ∘ σ。 -/
theorem endo_eisIter_comm (p : Nat) (σ : RingHom (eisRing p) (eisRing p))
    (hfix : ∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z) :
    ∀ n t, σ.map (eisIter p n t) = eisIter p n (σ.map t) := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
    intro t
    show σ.map (eisIter p n (eisF p t)) = eisIter p n (eisF p (σ.map t))
    rw [ih (eisF p t), endo_eisF_comm p σ hfix t]

/-- **定理 (M95-2b): 捻れ塔の保存** — 任意の ℤ_p-固定自己準同型は
    各 Λₙ を保つ（M89F の eisAut_preserves_torsion の一般化）。 -/
theorem endo_preserves_torsion (p : Nat)
    (σ : RingHom (eisRing p) (eisRing p))
    (hfix : ∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z)
    {n : Nat} {t : (eisRing p).carrier} (ht : IsEisTorsion p n t) :
    IsEisTorsion p n (σ.map t) := by
  show eisIter p n (σ.map t) = (eisRing p).zero
  rw [← endo_eisIter_comm p σ hfix n t, ht]
  exact RingHom.map_zero σ

/-! ## λ の行き先の剛性（本丸） -/

/-- **定理 (M95-3): σ(λ) ∈ Λ₁（無条件）** — λ の行き先は円分体
    Λ₁ の中に拘束される。 -/
theorem endo_lambda_torsion (p : Nat) (hp : 2 ≤ p)
    (σ : RingHom (eisRing p) (eisRing p))
    (hfix : ∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z) :
    IsEisTorsion p 1 (σ.map (eisLambda p)) :=
  endo_preserves_torsion p σ hfix
    (eisTorsion_lambda p hp 1 (Nat.le_refl 1))

/-- **定理 (M95-4a): 分類（NoZeroDiv の下）** —
    σ(λ) = 0 ∨ σ(λ)^{p−1} = −π（M90F の分類のインスタンス）。 -/
theorem endo_lambda_classify (p : Nat) (hp : 2 ≤ p)
    (hD : NoZeroDiv (eisRing p))
    (σ : RingHom (eisRing p) (eisRing p))
    (hfix : ∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z) :
    σ.map (eisLambda p) = (eisRing p).zero
      ∨ rpow (eisRing p) (σ.map (eisLambda p)) (p - 1)
          = (eisRing p).neg
              ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) :=
  eisTorsion_one_classify p hp hD (endo_lambda_torsion p hp σ hfix)

/-- **定理 (M95-4b): 非退化なら Eisenstein 根** — σ(λ) ≠ 0 なら
    σ(λ) は Eisenstein 方程式 t^{p−1} = −π の根。 -/
theorem endo_lambda_root (p : Nat) (hp : 2 ≤ p)
    (hD : NoZeroDiv (eisRing p))
    (σ : RingHom (eisRing p) (eisRing p))
    (hfix : ∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z)
    (hne : σ.map (eisLambda p) ≠ (eisRing p).zero) :
    rpow (eisRing p) (σ.map (eisLambda p)) (p - 1)
      = (eisRing p).neg
          ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) := by
  cases endo_lambda_classify p hp hD σ hfix with
  | inl h0 => exact absurd h0 hne
  | inr hroot => exact hroot

/-! ## 総括 -/

/-- **M95-5a: 自己同型上界骨格の総括** — ℤ_p-固定自己準同型の
    f-可換性・捻れ塔保存・λ の Λ₁ 拘束・Eisenstein 根への分類。 -/
structure EisEndoRigidityData (p : Nat) (hp : IsPrime p)
    (hD : NoZeroDiv (eisRing p)) where
  /-- σ ∘ f = f ∘ σ（ℤ_p 固定のみから）。 -/
  comm : ∀ (σ : RingHom (eisRing p) (eisRing p)),
    (∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z) →
    ∀ t, σ.map (eisF p t) = eisF p (σ.map t)
  /-- 捻れ塔の保存。 -/
  torsion : ∀ (σ : RingHom (eisRing p) (eisRing p)),
    (∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z) →
    ∀ {n : Nat} {t : (eisRing p).carrier}, IsEisTorsion p n t →
    IsEisTorsion p n (σ.map t)
  /-- σ(λ) ∈ Λ₁（無条件）。 -/
  lambda_torsion : ∀ (σ : RingHom (eisRing p) (eisRing p)),
    (∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z) →
    IsEisTorsion p 1 (σ.map (eisLambda p))
  /-- 非退化なら Eisenstein 根。 -/
  lambda_root : ∀ (σ : RingHom (eisRing p) (eisRing p)),
    (∀ z, σ.map ((eisOf p).map z) = (eisOf p).map z) →
    σ.map (eisLambda p) ≠ (eisRing p).zero →
    rpow (eisRing p) (σ.map (eisLambda p)) (p - 1)
      = (eisRing p).neg
          ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))

/-- **M95-5b: witness 本体**。 -/
def eisEndoRigidity (p : Nat) (hp : IsPrime p)
    (hD : NoZeroDiv (eisRing p)) : EisEndoRigidityData p hp hD where
  comm := fun σ hfix => endo_eisF_comm p σ hfix
  torsion := fun σ hfix => endo_preserves_torsion p σ hfix
  lambda_torsion := fun σ hfix => endo_lambda_torsion p hp.1 σ hfix
  lambda_root := fun σ hfix hne => endo_lambda_root p hp.1 hD σ hfix hne

/-- **定理 (M95-5c): 上界骨格の存在（見出し）**。 -/
theorem eisEndoRigidity_exists (p : Nat) (hp : IsPrime p)
    (hD : NoZeroDiv (eisRing p)) :
    Nonempty (EisEndoRigidityData p hp hD) :=
  ⟨eisEndoRigidity p hp hD⟩

end IUT
