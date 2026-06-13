/-
  IUT/EisensteinTower.lean — M89F（柱B 第3段後半の部品: O の捻れ塔と
  Galois 加群構造）

  M83F は O = ℤ_p[[X]]/(X^{p−1} + π) 上の [πⁿ]-作用 eisIter と非自明
  捻れ点 λ を、M86F は Galois 骨格 σ_ζ と可換性 σ_ζ ∘ f = f ∘ σ_ζ を、
  M87F は分岐 rec のレベル 1 データを構成した。本ファイルはその上に
  **捻れ塔 Λₙ := ker([πⁿ]) ⊆ O** を述語として立て、**Galois 作用が
  各捻れ層を保つ**こと — 相互写像が捻れ点に作用できる理由そのもの —
  を機械検証する。

  * M89F-1 `eisIter_succ_comm` — **外側剥がし**: [πⁿ⁺¹] = f ∘ [πⁿ]
    （定義は内側剥がし [πⁿ⁺¹] = [πⁿ] ∘ f なので、n の帰納で外側にも
    剥がせることを示す）
  * M89F-2 `eisIter_add` — **合成則**: [π^{m+n}] = [πᵐ] ∘ [πⁿ]
    （n の帰納、m + (n+1) = (m+n)+1 の定義簿記で defeq が揃う向き）
  * M89F-3 `IsEisTorsion` — **捻れ層の述語**: t ∈ Λₙ ⟺ [πⁿ]t = 0
  * M89F-4 `eisTorsion_zero` / `eisTorsion_mono` / `eisTorsion_lambda` /
    `eisTorsion_step` — 基本事実: 0 ∈ Λₙ（M83F-3b）、Λₙ ⊆ Λₙ₊₁
    （M89F-1 + f(0) = 0）、λ ∈ Λₙ（n ≥ 1、M83F-5 の言い換え）、
    t ∈ Λₙ₊₁ なら f(t) ∈ Λₙ（定義そのもの）
  * M89F-5 `eisAut_eisIter` / `eisAut_preserves_torsion` —
    **Galois 加群構造（本丸）**: σ_ζ は [πⁿ] と可換（n の帰納 +
    M86F-9 eisAut_eisF）、よって **σ_ζ(Λₙ) ⊆ Λₙ**:
    [πⁿ](σt) = σ([πⁿ]t) = σ(0) = 0（RingHom.map_zero）
  * M89F-6 `eisIter_semilinear` / `eisTorsion_conj_scale` —
    **1 の (p−1) 乗根倍は捻れ層を保つ**: ζ^{p−1} = 1 なら
    [πⁿ](ζt) = ζ·[πⁿ]t（n の帰納 + M84F-3 eisF_semilinear）、
    よって ζ·Λₙ ⊆ Λₙ。**注意**: f(T) = πT + T^p は線形でない
    （(ct)^p = c^p t^p）ので一般の c では成り立たない —
    一般の [c]-倍作用は形式群加法経由で、ここでは主張しない
  * M89F-7 `EisTorsionTowerData` / `eisTorsionTower` /
    `eisTorsionTower_exists` — **総括**: 述語・0 の所属・単調性・
    λ の所属（n ≥ 1）・非自明性（λ ≠ 0、M83F-6）・Galois 保存
    （Teichmüller 族 σ_a 全体）・共役族の所属（ω(a)λ ∈ Λ₁、M84F-8a）
    を束ねた純レコードと witness・存在定理
  * M89F-8 `eisTorsion_galois_orbit` — ストレッチ: **λ の Galois 軌道は
    Λ₁ ∖ {0} に留まる**（M89F-5 + M86F-5b eisAut_lambda +
    M84F-7c teich_conj_ne_zero）

  一般の [c]-倍作用（形式群加法経由）は**点の側 pℤ_p では M101
  （TorsionModule, ltAct_preserves_torsion）で決着**した（一般 a ∈ ℤ_p の
  [a]-作用が各 πⁿ-捻れ点を保つ）。残るのは分岐側 O = eisRing の捻れ塔
  Λₙ ⊆ O への移植（O 上の級数評価が要る）・Λₙ の位数・塔の生成元 λₙ
  で、これらは未形式化。p = 2 の除外（hodd : 3 ≤ p、総括とストレッチ
  のみ）は λ ≠ 0 が M83F-6 の係数比較に依存するため（同じ正直申告）。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RecRamified

namespace IUT

/-! ## 反復の外側剥がしと合成則 -/

/-- **定理 (M89F-1): 外側剥がし** — [πⁿ⁺¹] = f ∘ [πⁿ]。定義は
    内側剥がし eisIter (n+1) t = eisIter n (f t) なので、n の帰納で
    f を外側からも剥がせることを示す（基底は f^{∘1} = f の defeq、
    帰納段は IH を f(t) に適用）。 -/
theorem eisIter_succ_comm (p : Nat) : ∀ n t,
    eisIter p (n + 1) t = eisF p (eisIter p n t) := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
    intro t
    show eisIter p (n + 1) (eisF p t) = eisF p (eisIter p n (eisF p t))
    exact ih (eisF p t)

/-- **定理 (M89F-2): 合成則** — [π^{m+n}] = [πᵐ] ∘ [πⁿ]。n の帰納:
    m + (n+1) = (m+n)+1 の定義簿記で両辺が eisIter p (m+n) (f t) と
    eisIter p m (eisIter p n (f t)) に揃い、IH を f(t) に適用。 -/
theorem eisIter_add (p : Nat) : ∀ m n t,
    eisIter p (m + n) t = eisIter p m (eisIter p n t) := by
  intro m n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
    intro t
    show eisIter p (m + n) (eisF p t)
      = eisIter p m (eisIter p n (eisF p t))
    exact ih (eisF p t)

/-! ## 捻れ層 Λₙ の述語 -/

/-- **M89F-3: 捻れ層の述語** — t ∈ Λₙ ⟺ [πⁿ]t = 0。
    Λₙ := ker([πⁿ]) ⊆ O の点ごとの読み。 -/
def IsEisTorsion (p : Nat) (n : Nat) (t : (eisRing p).carrier) : Prop :=
  eisIter p n t = (eisRing p).zero

/-! ## 基本事実: 0・単調性・λ・一段降下 -/

/-- **M89F-4a: 0 ∈ Λₙ（∀ n）** — M83F-3b eisIter_zero の言い換え。 -/
theorem eisTorsion_zero (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    IsEisTorsion p n ((eisRing p).zero) :=
  eisIter_zero p hp n

/-- **定理 (M89F-4b): 単調性 Λₙ ⊆ Λₙ₊₁** — 外側剥がし（M89F-1）で
    [πⁿ⁺¹]t = f([πⁿ]t) = f(0) = 0（f(0) = 0 は M83F-3a、hp が要る）。
    捻れ層は本当に「塔」を成す。 -/
theorem eisTorsion_mono (p : Nat) (hp : 2 ≤ p) {n : Nat}
    {t : (eisRing p).carrier} (ht : IsEisTorsion p n t) :
    IsEisTorsion p (n + 1) t := by
  show eisIter p (n + 1) t = (eisRing p).zero
  rw [eisIter_succ_comm p n t, ht]
  exact eisF_zero p hp

/-- **M89F-4c: λ ∈ Λₙ（∀ n ≥ 1）** — M83F-5 lambda_all_torsion の
    述語形での言い換え。 -/
theorem eisTorsion_lambda (p : Nat) (hp : 2 ≤ p) (n : Nat) (hn : 1 ≤ n) :
    IsEisTorsion p n (eisLambda p) :=
  lambda_all_torsion p hp n hn

/-- **M89F-4d: 一段降下** — t ∈ Λₙ₊₁ なら f(t) ∈ Λₙ
    （eisIter の内側剥がしの定義そのもの、defeq）。 -/
theorem eisTorsion_step (p : Nat) {n : Nat} {t : (eisRing p).carrier}
    (ht : IsEisTorsion p (n + 1) t) : IsEisTorsion p n (eisF p t) :=
  ht

/-! ## Galois 加群構造: σ_ζ は各捻れ層を保つ -/

/-- **定理 (M89F-5a): σ_ζ は [πⁿ]-作用と可換** —
    σ_ζ([πⁿ]t) = [πⁿ](σ_ζ t)（∀ n, t）。n の帰納で一段の可換性
    M86F-9 eisAut_eisF を積み上げる。**Galois 作用は Lubin–Tate
    塔全体と両立**。 -/
theorem eisAut_eisIter (p : Nat) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) (hp : 2 ≤ p) :
    ∀ n t, (eisAut p z hz hp).map (eisIter p n t)
      = eisIter p n ((eisAut p z hz hp).map t) := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
    intro t
    show (eisAut p z hz hp).map (eisIter p n (eisF p t))
      = eisIter p n (eisF p ((eisAut p z hz hp).map t))
    rw [ih (eisF p t), eisAut_eisF p z hz hp t]

/-- **定理 (M89F-5b): Galois 作用は捻れ層を保つ（本丸）** —
    t ∈ Λₙ なら σ_ζ(t) ∈ Λₙ: [πⁿ](σt) = σ([πⁿ]t) = σ(0) = 0
    （M89F-5a + RingHom.map_zero）。**各 Λₙ は Galois 加群** —
    相互写像が捻れ点に作用できる理由そのもの。 -/
theorem eisAut_preserves_torsion (p : Nat) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) (hp : 2 ≤ p)
    (n : Nat) (t : (eisRing p).carrier) (ht : IsEisTorsion p n t) :
    IsEisTorsion p n ((eisAut p z hz hp).map t) := by
  show eisIter p n ((eisAut p z hz hp).map t) = (eisRing p).zero
  rw [← eisAut_eisIter p z hz hp n t, ht]
  exact RingHom.map_zero (eisAut p z hz hp)

/-! ## 1 の冪根倍は捻れ層を保つ（半線形性の反復） -/

/-- **定理 (M89F-6a): 半線形性の反復** — ζ^{p−1} = 1 なら
    [πⁿ](ζt) = ζ·[πⁿ]t（∀ n, t）。n の帰納で一段の半線形性
    M84F-3 eisF_semilinear を積み上げる。f(T) = πT + T^p は線形で
    ない（(ct)^p = c^p t^p）ので、ζ^p = ζ となる 1 の冪根に限る。 -/
theorem eisIter_semilinear (p : Nat) (hp : 2 ≤ p) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) :
    ∀ n t, eisIter p n ((eisRing p).mul ((eisOf p).map z) t)
      = (eisRing p).mul ((eisOf p).map z) (eisIter p n t) := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
    intro t
    show eisIter p n (eisF p ((eisRing p).mul ((eisOf p).map z) t))
      = (eisRing p).mul ((eisOf p).map z) (eisIter p n (eisF p t))
    rw [eisF_semilinear p hp z hz t]
    exact ih (eisF p t)

/-- **定理 (M89F-6b): 1 の冪根倍は捻れ層を保つ** — ζ^{p−1} = 1、
    t ∈ Λₙ なら ζt ∈ Λₙ: [πⁿ](ζt) = ζ·[πⁿ]t = ζ·0 = 0
    （M89F-6a + mul_zero）。**注意**: 一般の c ∈ ℤ_p の [c]-倍作用が
    Λₙ を保つことは形式群加法を経由する主張であり、ここでは主張
    しない（未形式化）。 -/
theorem eisTorsion_conj_scale (p : Nat) (hp : 2 ≤ p) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) {n : Nat}
    {t : (eisRing p).carrier} (ht : IsEisTorsion p n t) :
    IsEisTorsion p n ((eisRing p).mul ((eisOf p).map z) t) := by
  show eisIter p n ((eisRing p).mul ((eisOf p).map z) t) = (eisRing p).zero
  rw [eisIter_semilinear p hp z hz n t, ht]
  exact CRing.mul_zero (eisRing p) ((eisOf p).map z)

/-! ## 総括: 捻れ塔の Galois 加群データ -/

/-- **M89F-7a: 捻れ塔データ** — 捻れ塔 Λₙ とその Galois 加群構造の
    全簿記: 述語・0 の所属・単調性（塔であること）・λ の所属
    （n ≥ 1）・非自明性（λ ≠ 0）・Galois 保存（Teichmüller 族
    σ_a 全体が各層を保つ）・共役族の所属（ω(a)λ ∈ Λ₁）。 -/
structure EisTorsionTowerData (p : Nat) (hp : IsPrime p)
    (hodd : 3 ≤ p) where
  /-- 捻れ層の述語: t ∈ Λₙ。 -/
  torsion : Nat → (eisRing p).carrier → Prop
  /-- 0 ∈ Λₙ（∀ n）。 -/
  torsion_zero : ∀ n, torsion n (eisRing p).zero
  /-- 単調性: Λₙ ⊆ Λₙ₊₁（塔であること）。 -/
  torsion_mono : ∀ {n : Nat} {t : (eisRing p).carrier},
    torsion n t → torsion (n + 1) t
  /-- λ ∈ Λₙ（∀ n ≥ 1）。 -/
  torsion_lambda : ∀ n, 1 ≤ n → torsion n (eisLambda p)
  /-- 非自明性: λ ≠ 0。 -/
  lambda_ne_zero : eisLambda p ≠ (eisRing p).zero
  /-- Galois 保存: 各 σ_a（p ∤ a）は各 Λₙ を保つ — Λₙ は Galois 加群。 -/
  galois_preserves : ∀ (a : Int) (ha : ¬ ((p : Nat) : Int) ∣ a)
    (n : Nat) (t : (eisRing p).carrier),
    torsion n t → torsion n ((eisGal p hp a ha).map t)
  /-- 共役族の所属: ω(a)λ ∈ Λ₁（1 ≤ a < p）。 -/
  conj_member : ∀ a : Nat, 1 ≤ a → a < p →
    torsion 1 ((eisRing p).mul ((eisOf p).map (teich p hp (a : Int)))
      (eisLambda p))

/-- **定理 (M89F-7b): witness** — IsEisTorsion が捻れ塔データを成す
    （M89F-4 + M83F-6 + M89F-5b（σ_a = σ_{ω(a)} は defeq で充填）+
    M84F-8a、純レコード、選択公理不使用）。 -/
def eisTorsionTower (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    EisTorsionTowerData p hp hodd where
  torsion := IsEisTorsion p
  torsion_zero := fun n => eisTorsion_zero p hp.1 n
  torsion_mono := fun ht => eisTorsion_mono p hp.1 ht
  torsion_lambda := fun n hn => eisTorsion_lambda p hp.1 n hn
  lambda_ne_zero := eis_lambda_ne_zero p hodd
  galois_preserves := fun a ha n t ht =>
    eisAut_preserves_torsion p (teich p hp a)
      (teich_pow_rpow_one p hp ha) hp.1 n t ht
  conj_member := fun a h1 h2 =>
    (lambda_one_torsion_family p hp hodd a h1 h2).1

/-- **M89F-7c: 存在定理（ヘッドライン）** — O の捻れ塔は Galois
    加群構造を持つ。柱B 第3段後半（rec の捻れ層への作用）の土台。 -/
theorem eisTorsionTower_exists (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    Nonempty (EisTorsionTowerData p hp hodd) :=
  ⟨eisTorsionTower p hp hodd⟩

/-! ## ストレッチ: λ の Galois 軌道は Λ₁ ∖ {0} に留まる -/

/-- **定理 (M89F-8): Galois 軌道の所在** — 各 σ_a（p ∤ a）について
    σ_a(λ) ∈ Λ₁ かつ σ_a(λ) ≠ 0: 所属は M89F-5b（λ ∈ Λ₁ は
    M89F-4c）、非零は σ_a(λ) = ω(a)λ（M86F-5b）と M84F-7c。
    **λ の Galois 軌道は非自明捻れ点の中で閉じる**。 -/
theorem eisTorsion_galois_orbit (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    {a : Int} (ha : ¬ ((p : Nat) : Int) ∣ a) :
    IsEisTorsion p 1 ((eisGal p hp a ha).map (eisLambda p))
      ∧ (eisGal p hp a ha).map (eisLambda p) ≠ (eisRing p).zero := by
  constructor
  · exact eisAut_preserves_torsion p (teich p hp a)
      (teich_pow_rpow_one p hp ha) hp.1 1 (eisLambda p)
      (eisTorsion_lambda p hp.1 1 (Nat.le_refl 1))
  · rw [show (eisGal p hp a ha).map (eisLambda p)
        = (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p) from
        eisAut_lambda p (teich p hp a) (teich_pow_rpow_one p hp ha) hp.1]
    exact teich_conj_ne_zero p hp hodd ha

end IUT
