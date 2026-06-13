/-
  IUT/EisensteinUpper.lean — M90F（柱B 上界・第一段: Λ₁ の
  Eisenstein 方程式への還元）

  M84F は Λ₁ = ker(f) ⊆ O = ℤ_p[[X]]/(X^{p−1} + π) が 0 と p−1 個の
  相異なる共役点 ω(a)·λ を含むこと（下界 ≥ p 点）を、M89F は捻れ塔
  Λₙ の Galois 加群構造を示した。完全な上界 |Λ₁| ≤ p には O が整域で
  あることが要る（未形式化 — 困難）。本ファイルはその**条件付き還元**
  を機械検証する: 零因子なし（NoZeroDiv）を仮定すれば、Λ₁ の元は
  0 か Eisenstein 方程式 t^{p−1} = −π の根に限る。

  * M90F-1 `eisF_factor` — **因数分解** f(t) = t·(π + t^{p−1})
    （指数分割 p = (p−1)+1 + 乗法可換 + 左分配）
  * M90F-2 `NoZeroDiv` — 零因子なしの述語（整域性の乗法部分、
    一般の可換環で定義）
  * M90F-3 `eisTorsion_one_classify` — **本丸（条件付き分類）**:
    NoZeroDiv (eisRing p) のもとで t ∈ Λ₁ なら t = 0 または
    t^{p−1} = −π。Λ₁ ⟺ f(t) = 0（eisIter の 1 段は defeq）を
    M90F-1 で因数分解し、零因子なしで場合分け、第二枝は
    π + t^{p−1} = 0 を neg_eq_of_add_eq_zero で読み替える
  * M90F-4 `lambda_eis_equation` — λ^{p−1} = −π を M90F-3 の分類から
    再導出（λ ∈ Λ₁（M89F-4c）+ λ ≠ 0（M83F-6）で第二枝に落ちる。
    無条件版は M82F-5c eis_lambda_pow — 分類が λ で正しい枝を選ぶ
    ことの照合）
  * M90F-5 `conj_eis_equation` — **共役点も方程式を満たす（無条件）**:
    (ω(a)λ)^{p−1} = ω(a)^{p−1}·λ^{p−1} = 1·(−π) = −π
    （rpow_mul_dist + ringHom_rpow + M84F-7a + M82F-5c、hD 不要）
  * M90F-6 `EisUpperData` / `eisUpper` / `eisUpper_exists` — **総括**:
    Λ₁ の分類（条件付き）・λ と共役族 ω(a)λ（1 ≤ a < p）が
    Eisenstein 根であること・族の非零性（M84F-7c）と相異性
    （M84F-8b）を束ねた純レコードと witness・存在定理

  O（あるいは ℤ_p）の整域性そのもの（NoZeroDiv (eisRing p) の証明）・
  |Λ₁| ≤ p の点の数え上げ（t^{p−1} = −π の根が高々 p−1 個である
  こと）は未形式化 — NoZeroDiv は仮定として受け取る条件付き還元。
  非零元の最初の非零レベル成分の抽出（付値証人）は ℤ/pⁿ の商型での
  等値判定を要し、選択公理なしの範囲で短く書けないため見送り。
  p = 2 の除外（hodd : 3 ≤ p、M90F-4 以降）は λ ≠ 0 が M83F-6 の
  係数比較に依存するため（同じ正直申告）。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.EisensteinTower

namespace IUT

/-! ## f の因数分解 f(t) = t·(π + t^{p−1}) -/

/-- **定理 (M90F-1): 因数分解** — f(t) = πt + t^p = t·(π + t^{p−1})。
    指数分割 p = (p−1)+1 で t^p = t^{p−1}·t、乗法可換で両項の t を
    左に揃え、左分配で括り出す。 -/
theorem eisF_factor (p : Nat) (hp : 2 ≤ p) (t : (eisRing p).carrier) :
    eisF p t
      = (eisRing p).mul t
          ((eisRing p).add ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
            (rpow (eisRing p) t (p - 1))) := by
  have hsplit : rpow (eisRing p) t p
      = (eisRing p).mul (rpow (eisRing p) t (p - 1)) t :=
    congrArg (rpow (eisRing p) t) (show p = (p - 1) + 1 by omega)
  show (eisRing p).add
      ((eisRing p).mul ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) t)
      (rpow (eisRing p) t p)
    = (eisRing p).mul t
        ((eisRing p).add ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
          (rpow (eisRing p) t (p - 1)))
  rw [hsplit,
    (eisRing p).mul_comm ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) t,
    (eisRing p).mul_comm (rpow (eisRing p) t (p - 1)) t,
    (eisRing p).left_distrib t
      ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
      (rpow (eisRing p) t (p - 1))]

/-! ## 零因子なしの述語 -/

/-- **M90F-2: 零因子なし** — ab = 0 なら a = 0 または b = 0
    （整域性の乗法部分。eisRing p での成立は未形式化、以下では
    仮定として受け取る）。 -/
def NoZeroDiv (R : CRing) : Prop :=
  ∀ a b : R.carrier, R.mul a b = R.zero → a = R.zero ∨ b = R.zero

/-! ## 条件付き分類: Λ₁ の元は 0 か Eisenstein 根 -/

/-- **定理 (M90F-3): Λ₁ の条件付き分類（本丸）** — O に零因子が
    なければ、t ∈ Λ₁ は t = 0 または **t^{p−1} = −π**（Eisenstein
    方程式）。t ∈ Λ₁ ⟺ f(t) = 0（eisIter の 1 段は defeq）、
    f(t) = t·(π + t^{p−1})（M90F-1）に NoZeroDiv を当て、第二枝は
    π + t^{p−1} = 0 から neg_eq_of_add_eq_zero で読み替える。
    **Λ₁ の上界 |Λ₁| ≤ p は Eisenstein 方程式の根の数え上げに還元**。 -/
theorem eisTorsion_one_classify (p : Nat) (hp : 2 ≤ p)
    (hD : NoZeroDiv (eisRing p)) {t : (eisRing p).carrier}
    (ht : IsEisTorsion p 1 t) :
    t = (eisRing p).zero
      ∨ rpow (eisRing p) t (p - 1)
          = (eisRing p).neg
              ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) := by
  have hF : eisF p t = (eisRing p).zero := ht
  rw [eisF_factor p hp t] at hF
  cases hD t
      ((eisRing p).add ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
        (rpow (eisRing p) t (p - 1))) hF with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr ((eisRing p).neg_eq_of_add_eq_zero h).symm

/-! ## λ と共役点は Eisenstein 根 -/

/-- **定理 (M90F-4): λ は分類の第二枝に落ちる** — λ ∈ Λ₁（M89F-4c）
    かつ λ ≠ 0（M83F-6）なので、NoZeroDiv のもとで M90F-3 から
    λ^{p−1} = −π。無条件版 M82F-5c eis_lambda_pow と同じ結論であり、
    **分類が λ で正しい枝を選ぶことの照合**になっている。 -/
theorem lambda_eis_equation (p : Nat) (hodd : 3 ≤ p)
    (hD : NoZeroDiv (eisRing p)) :
    rpow (eisRing p) (eisLambda p) (p - 1)
      = (eisRing p).neg
          ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) := by
  cases eisTorsion_one_classify p (by omega) hD
      (eisTorsion_lambda p (by omega) 1 (Nat.le_refl 1)) with
  | inl h => exact absurd h (eis_lambda_ne_zero p hodd)
  | inr h => exact h

/-- **定理 (M90F-5): 共役点も Eisenstein 根（無条件）** —
    (ω(a)λ)^{p−1} = ω(a)^{p−1}·λ^{p−1} = 1·(−π) = −π（p ∤ a）。
    冪の積分配（rpow_mul_dist）+ 環準同型の冪保存（ringHom_rpow）+
    ω(a)^{p−1} = 1（M84F-7a）+ λ^{p−1} = −π（M82F-5c）。
    こちらは NoZeroDiv 不要 — **共役族全体が文字通り同じ Eisenstein
    方程式を満たす**。 -/
theorem conj_eis_equation (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    rpow (eisRing p)
        ((eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p))
        (p - 1)
      = (eisRing p).neg
          ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) := by
  rw [rpow_mul_dist (eisRing p) ((eisOf p).map (teich p hp a))
      (eisLambda p) (p - 1),
    ← ringHom_rpow (eisOf p) (teich p hp a) (p - 1),
    teich_pow_rpow_one p hp ha, (eisOf p).map_one,
    (eisRing p).one_mul (rpow (eisRing p) (eisLambda p) (p - 1)),
    eis_lambda_pow p hp.1]

/-! ## 総括: 条件付き上界データ -/

/-- **M90F-6a: 条件付き上界データ** — NoZeroDiv (eisRing p) を仮定
    したときの Λ₁ の記述の全簿記: 分類（0 か Eisenstein 根）・λ が
    Eisenstein 根・共役族 ω(a)λ（1 ≤ a < p）が Eisenstein 根・族の
    非零性・相異性。M84F の下界 ≥ p と合わせ、上界は「t^{p−1} = −π の
    根は高々 p−1 個」（未形式化）だけを残す。 -/
structure EisUpperData (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    (hD : NoZeroDiv (eisRing p)) where
  /-- 分類: t ∈ Λ₁ なら t = 0 または t^{p−1} = −π。 -/
  classify : ∀ t : (eisRing p).carrier, IsEisTorsion p 1 t →
    t = (eisRing p).zero
      ∨ rpow (eisRing p) t (p - 1)
          = (eisRing p).neg
              ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
  /-- λ は Eisenstein 根: λ^{p−1} = −π。 -/
  lambda_root : rpow (eisRing p) (eisLambda p) (p - 1)
    = (eisRing p).neg ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
  /-- 共役族は Eisenstein 根: (ω(a)λ)^{p−1} = −π（1 ≤ a < p）。 -/
  conj_root : ∀ a : Nat, 1 ≤ a → a < p →
    rpow (eisRing p)
        ((eisRing p).mul ((eisOf p).map (teich p hp (a : Int)))
          (eisLambda p)) (p - 1)
      = (eisRing p).neg ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
  /-- 族の非零性: ω(a)λ ≠ 0（1 ≤ a < p）。 -/
  family_ne_zero : ∀ a : Nat, 1 ≤ a → a < p →
    (eisRing p).mul ((eisOf p).map (teich p hp (a : Int))) (eisLambda p)
      ≠ (eisRing p).zero
  /-- 族の相異性: ω(a)λ ≠ ω(b)λ（1 ≤ a < b < p）。 -/
  family_distinct : ∀ a b : Nat, 1 ≤ a → a < b → b < p →
    (eisRing p).mul ((eisOf p).map (teich p hp (a : Int))) (eisLambda p)
      ≠ (eisRing p).mul ((eisOf p).map (teich p hp (b : Int)))
          (eisLambda p)

/-- **定理 (M90F-6b): witness** — M90F-3/4/5 + M84F-7c/8b が条件付き
    上界データを成す（純レコード、選択公理不使用）。 -/
def eisUpper (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    (hD : NoZeroDiv (eisRing p)) : EisUpperData p hp hodd hD where
  classify := fun _ ht => eisTorsion_one_classify p hp.1 hD ht
  lambda_root := lambda_eis_equation p hodd hD
  conj_root := fun a h1 h2 =>
    conj_eis_equation p hp (nat_lt_not_dvd_int p a h1 h2)
  family_ne_zero := fun a h1 h2 =>
    teich_conj_ne_zero p hp hodd (nat_lt_not_dvd_int p a h1 h2)
  family_distinct := fun a b h1 h2 h3 =>
    lambda_one_family_distinct p hp hodd a b h1 h2 h3

/-- **M90F-6c: 存在定理（ヘッドライン）** — O に零因子がなければ、
    Λ₁ は 0 と Eisenstein 方程式 t^{p−1} = −π の根のみからなり、
    その中に p−1 個の相異なる共役根 ω(a)λ が実在する。柱B 上界の
    第一段（方程式への還元）完了。 -/
theorem eisUpper_exists (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    (hD : NoZeroDiv (eisRing p)) :
    Nonempty (EisUpperData p hp hodd hD) :=
  ⟨eisUpper p hp hodd hD⟩

end IUT
