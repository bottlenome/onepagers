/-
  IUT/EisensteinGalois.lean — M86F（柱B 第2段: Galois 作用の骨格）

  M84F は Teichmüller 共役族 {ω(a)·λ} が p−1 個の相異なる非自明
  捻れ点であることを示した。本ファイルはその裏にある**環の対称性**を
  構成する: 1 の (p−1) 乗根 ζ（ζ^{p−1} = 1、特に ζ = ω(a)）ごとに
  **倍率写像 σ_ζ : λ ↦ ζλ は O = ℤ_p[[X]]/(X^{p−1} + π) の
  ℤ_p-固定環自己準同型**であり、合成則 σ_ζ ∘ σ_ξ = σ_{ζξ}・単位律
  σ_1 = id・λ での相異性を満たす — すなわち
  Gal(ℚ_p(λ)/ℚ_p) ≅ (ℤ/p)^× の骨格（下界 p−1 個の自己準同型）。

  * M86F-1 `psScale` / `psScale_add` / `psScale_neg` / `psScale_one` /
    `psScale_mul` — **係数倍率写像** (psScale z f)_n = z^n·f_n は
    任意の z で環演算を保つ（乗法は Cauchy 和内の指数分割
    z^n = z^k·z^{n−k}、congrArg を指数だけに当てる）
  * M86F-2 `psScale_psC` / `psScale_psX` / `psScale_comp` /
    `psScale_one_base` — 定数は固定・X は z·X・合成は積・1 倍は恒等
  * M86F-3 `psScale_eisPoly` / `psScale_eisRel` — **ζ^{p−1} = 1 なら
    E = X^{p−1} + π は固定**（係数 p−1 で仮定、係数 0 で z^0 = 1）、
    よって psScale は (E)-合同を保ち商に降りる
  * M86F-4 `eisAut` — **σ_ζ : O → O は環準同型**（Quot.lift、法則は
    代表元の psScale 法則 + congrArg (Quot.mk)、eisRing と同じ家風）
  * M86F-5 `eisAut_const` / `eisAut_lambda` — **ℤ_p 固定・λ ↦ ζλ**
  * M86F-6 `rpow_one_mul_closed` / `eisAut_comp` / `eisAut_one` /
    `eisAut_congr` — **合成則 σ_ζ ∘ σ_ξ = σ_{ζξ}・単位律 σ_1 = id**
    （1 の冪根は積で閉じる、合成は係数レベルの rpow_mul_dist）
  * M86F-7 `eisGal` / `eisGal_comp` / `eisGal_mul` — **Teichmüller
    実装 σ_a := σ_{ω(a)}**（p ∤ a）と乗法性 σ_a ∘ σ_b = σ_{ab}
    （M33-8a teich_mul: ω(ab) = ω(a)ω(b)）
  * M86F-8 `eisGal_distinct` — **相異性**: p ∤ (a−b) なら
    σ_a(λ) ≠ σ_b(λ)（M84F-7d teich_conj_distinct）—
    **p−1 個の相異なる自己準同型 = Gal ≅ (ℤ/p)^× の下界**
  * M86F-9 `eisAut_eisF` — ストレッチ: **σ_ζ は Lubin–Tate 作用
    f(T) = πT + T^p と可換**（π は固定 + 環準同型簿記）—
    Galois 作用と [π]-作用の両立、rec 接続（柱B 第3段）への布石

  全自己同型の分類（これで全部であること）・固定環がちょうど ℤ_p で
  あること・逆写像（σ_{a^{-1}}）の明示・rec との接続は未形式化。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RamifiedEntrance

namespace IUT

/-! ## 係数倍率写像 psScale -/

/-- **M86F-1a: 係数倍率写像** — (psScale z f)_n = z^n·f_n。
    形式変数の置換 X ↦ zX を係数列のレベルで実装したもの。 -/
def psScale (R : CRing) (z : R.carrier) (f : PS R) : PS R :=
  fun n => R.mul (rpow R z n) (f n)

/-- **M86F-1b: 加法の保存**（左分配、z に条件なし）。 -/
theorem psScale_add (R : CRing) (z : R.carrier) (f g : PS R) :
    psScale R z (psAdd R f g) = psAdd R (psScale R z f) (psScale R z g) := by
  funext n
  exact R.left_distrib (rpow R z n) (f n) (g n)

/-- **M86F-1c: 負元の保存**（z^n·(−f_n) = −(z^n·f_n)）。 -/
theorem psScale_neg (R : CRing) (z : R.carrier) (f : PS R) :
    psScale R z (psNeg R f) = psNeg R (psScale R z f) := by
  funext n
  exact CRing.mul_neg R (rpow R z n) (f n)

/-- **M86F-1d: 単位級数の固定** — 係数 0 で z^0·1 = 1、他は z^n·0 = 0。 -/
theorem psScale_one (R : CRing) (z : R.carrier) :
    psScale R z (psOne R) = psOne R := by
  funext n
  cases n with
  | zero =>
    show R.mul R.one R.one = R.one
    exact R.one_mul R.one
  | succ m =>
    show R.mul (rpow R z (m + 1)) R.zero = R.zero
    exact CRing.mul_zero R _

/-- **定理 (M86F-1e): 乗法の保存** — Cauchy 和の各項で指数を
    n = k + (n−k) に分割（congrArg は指数のみに当てる）:
    z^n·(f_k·g_{n−k}) = (z^k·f_k)·(z^{n−k}·g_{n−k})。 -/
theorem psScale_mul (R : CRing) (z : R.carrier) (f g : PS R) :
    psScale R z (psMul R f g) = psMul R (psScale R z f) (psScale R z g) := by
  funext n
  show R.mul (rpow R z n) (rsum R (fun k => R.mul (f k) (g (n - k))) (n + 1))
    = rsum R (fun k => R.mul (R.mul (rpow R z k) (f k))
        (R.mul (rpow R z (n - k)) (g (n - k)))) (n + 1)
  rw [rsum_mul_left R (fun k => R.mul (f k) (g (n - k))) (rpow R z n) (n + 1)]
  refine rsum_congr R (n + 1) (fun k hk => ?_)
  show R.mul (rpow R z n) (R.mul (f k) (g (n - k)))
    = R.mul (R.mul (rpow R z k) (f k)) (R.mul (rpow R z (n - k)) (g (n - k)))
  have hsplit : rpow R z n = R.mul (rpow R z k) (rpow R z (n - k)) :=
    (congrArg (rpow R z) (show n = k + (n - k) by omega)).trans
      (rpow_add R z k (n - k))
  rw [hsplit,
    R.mul_assoc (rpow R z k) (rpow R z (n - k)) (R.mul (f k) (g (n - k))),
    ← R.mul_assoc (rpow R z (n - k)) (f k) (g (n - k)),
    R.mul_comm (rpow R z (n - k)) (f k),
    R.mul_assoc (f k) (rpow R z (n - k)) (g (n - k)),
    ← R.mul_assoc (rpow R z k) (f k)
      (R.mul (rpow R z (n - k)) (g (n - k)))]

/-! ## 定数・X・合成・恒等 -/

/-- **M86F-2a: 定数級数の固定** — 係数 0 で z^0·c = c、他は 0。
    σ_ζ が ℤ_p を固定することの代表元レベル。 -/
theorem psScale_psC (R : CRing) (z c : R.carrier) :
    psScale R z (psC R c) = psC R c := by
  funext n
  cases n with
  | zero =>
    show R.mul R.one c = c
    exact R.one_mul c
  | succ m =>
    show R.mul (rpow R z (m + 1)) R.zero = R.zero
    exact CRing.mul_zero R _

/-- **M86F-2b: X の像は z·X** — psScale z X = (psC z)·X
    （係数 1 で z^1·1 = z、他は両辺 0）。σ_ζ(λ) = ζλ の代表元レベル。 -/
theorem psScale_psX (R : CRing) (z : R.carrier) :
    psScale R z (psX R) = psMul R (psC R z) (psX R) := by
  funext n
  match n with
  | 0 =>
    show R.mul R.one R.zero = R.add R.zero (R.mul z R.zero)
    rw [R.one_mul, CRing.mul_zero R z, R.zero_add]
  | 1 =>
    show R.mul (R.mul R.one z) R.one
      = R.add (R.add R.zero (R.mul z R.one)) (R.mul R.zero R.zero)
    rw [R.one_mul z, CRing.mul_one R z, CRing.mul_zero R R.zero,
      R.zero_add z, CRing.add_zero R z]
  | (m + 2) =>
    show R.mul (rpow R z (m + 2)) R.zero
      = rsum R (fun k => R.mul (psC R z k) (psX R (m + 2 - k))) (m + 3)
    rw [CRing.mul_zero R (rpow R z (m + 2))]
    have hc : rsum R (fun k => R.mul (psC R z k) (psX R (m + 2 - k))) (m + 3)
        = rsum R (fun _ => R.zero) (m + 3) :=
      rsum_congr R (m + 3) (fun k hk => by
        cases Nat.decEq k 0 with
        | isTrue he =>
          subst he
          show R.mul (psC R z 0) (psX R (m + 2 - 0)) = R.zero
          rw [show psX R (m + 2 - 0) = R.zero from if_neg (by omega)]
          exact CRing.mul_zero R _
        | isFalse hne =>
          show R.mul (psC R z k) (psX R (m + 2 - k)) = R.zero
          rw [show psC R z k = R.zero from if_neg hne]
          exact CRing.zero_mul R _)
    rw [hc, rsum_const_zero R (m + 3)]

/-- **M86F-2c: 合成は係数の積** — psScale z ∘ psScale w = psScale (zw)
    （係数レベルの (zw)^n = z^n·w^n、rpow_mul_dist）。 -/
theorem psScale_comp (R : CRing) (z w : R.carrier) (f : PS R) :
    psScale R z (psScale R w f) = psScale R (R.mul z w) f := by
  funext n
  show R.mul (rpow R z n) (R.mul (rpow R w n) (f n))
    = R.mul (rpow R (R.mul z w) n) (f n)
  rw [rpow_mul_dist R z w n, R.mul_assoc]

/-- **M86F-2d: 1 倍は恒等** — 1^n·f_n = f_n（M54-1a rpow_one_base）。 -/
theorem psScale_one_base (R : CRing) (f : PS R) :
    psScale R R.one f = f := by
  funext n
  show R.mul (rpow R R.one n) (f n) = f n
  rw [rpow_one_base R n]
  exact R.one_mul (f n)

/-! ## Eisenstein 多項式の固定と (E)-合同の保存 -/

/-- **定理 (M86F-3a): ζ^{p−1} = 1 なら E は固定** —
    係数 p−1 で z^{p−1}·1 = 1（仮定）、係数 0 で z^0·π = π、
    他は両辺 0。E = X^{p−1} + π が σ_ζ の固定点であること。 -/
theorem psScale_eisPoly (p : Nat) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) (hp : 2 ≤ p) :
    psScale (zpRing p) z (eisPoly p) = eisPoly p := by
  funext n
  cases Nat.decEq n 0 with
  | isTrue he =>
    subst he
    show (zpRing p).mul (zpRing p).one (eisPoly p 0) = eisPoly p 0
    exact (zpRing p).one_mul _
  | isFalse hn0 =>
    cases Nat.decEq n (p - 1) with
    | isTrue he =>
      subst he
      show (zpRing p).mul (rpow (zpRing p) z (p - 1)) (eisPoly p (p - 1))
        = eisPoly p (p - 1)
      rw [hz]
      exact (zpRing p).one_mul _
    | isFalse hne =>
      show (zpRing p).mul (rpow (zpRing p) z n) (eisPoly p n) = eisPoly p n
      have h0 : eisPoly p n = (zpRing p).zero := by
        show (zpRing p).add (psMono (zpRing p) (p - 1) n)
            (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) n)
          = (zpRing p).zero
        rw [show psMono (zpRing p) (p - 1) n = (zpRing p).zero from
            if_neg hne,
          show psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) n
            = (zpRing p).zero from if_neg hn0,
          (zpRing p).zero_add]
      rw [h0]
      exact CRing.mul_zero (zpRing p) _

/-- **M86F-3b: (E)-合同の保存** — f − g = h·E なら
    psScale f − psScale g = (psScale h)·E（加法・負元・乗法の保存 +
    E の固定。証人は psScale h）。psScale は商 O に降りる。 -/
theorem psScale_eisRel (p : Nat) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) (hp : 2 ≤ p)
    {f g : PS (zpRing p)} (hfg : eisRel p f g) :
    eisRel p (psScale (zpRing p) z f) (psScale (zpRing p) z g) := by
  obtain ⟨h, hw⟩ := hfg
  refine ⟨psScale (zpRing p) z h, ?_⟩
  rw [← psScale_neg, ← psScale_add, hw, psScale_mul,
    psScale_eisPoly p z hz hp]

/-! ## σ_ζ : O → O は環準同型 -/

/-- **定理 (M86F-4): Galois 自己準同型の骨格** —
    ζ^{p−1} = 1 なる ζ = eisOf z ごとに σ_ζ : O → O、
    (f mod E) ↦ (psScale z f mod E) は環準同型
    （Quot.lift、法則は代表元の psScale 法則 + congrArg (Quot.mk)）。 -/
def eisAut (p : Nat) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) (hp : 2 ≤ p) :
    RingHom (eisRing p) (eisRing p) where
  map := Quot.lift
    (fun f => Quot.mk (eisRel p) (psScale (zpRing p) z f))
    (fun _ _ hfg => Quot.sound (psScale_eisRel p z hz hp hfg))
  map_add := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    exact congrArg (Quot.mk (eisRel p)) (psScale_add (zpRing p) z f g)
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    exact congrArg (Quot.mk (eisRel p)) (psScale_mul (zpRing p) z f g)
  map_one := congrArg (Quot.mk (eisRel p)) (psScale_one (zpRing p) z)

/-! ## 作用の事実: ℤ_p 固定と λ ↦ ζλ -/

/-- **定理 (M86F-5a): σ_ζ は ℤ_p を固定** — σ_ζ(eisOf c) = eisOf c
    （代表元 psC c の固定、M86F-2a）。Galois 群が基礎体を動かさない
    ことの骨格。 -/
theorem eisAut_const (p : Nat) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) (hp : 2 ≤ p)
    (c : (Zp p).carrier) :
    (eisAut p z hz hp).map ((eisOf p).map c) = (eisOf p).map c :=
  congrArg (Quot.mk (eisRel p)) (psScale_psC (zpRing p) z c)

/-- **定理 (M86F-5b): σ_ζ(λ) = ζλ** — 一意化元は ζ 倍に写る
    （代表元 X ↦ z·X、M86F-2b）。共役 λ ↦ ζλ の自己準同型としての実現。 -/
theorem eisAut_lambda (p : Nat) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) (hp : 2 ≤ p) :
    (eisAut p z hz hp).map (eisLambda p)
      = (eisRing p).mul ((eisOf p).map z) (eisLambda p) :=
  congrArg (Quot.mk (eisRel p)) (psScale_psX (zpRing p) z)

/-! ## 群構造: 合成則と単位律 -/

/-- **M86F-6a: 1 の k 乗根は積で閉じる** — z^k = 1、w^k = 1 なら
    (zw)^k = z^k·w^k = 1（rpow_mul_dist）。 -/
theorem rpow_one_mul_closed (R : CRing) {z w : R.carrier} (k : Nat)
    (hz : rpow R z k = R.one) (hw : rpow R w k = R.one) :
    rpow R (R.mul z w) k = R.one := by
  rw [rpow_mul_dist R z w k, hz, hw]
  exact R.one_mul R.one

/-- **定理 (M86F-6b): 合成則** — σ_ζ ∘ σ_ξ = σ_{ζξ}
    （代表元レベルの psScale_comp、係数の (zw)^n = z^n·w^n）。 -/
theorem eisAut_comp (p : Nat) (z w : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one)
    (hw : rpow (zpRing p) w (p - 1) = (zpRing p).one)
    (hzw : rpow (zpRing p) ((zpRing p).mul z w) (p - 1) = (zpRing p).one)
    (hp : 2 ≤ p) : ∀ t,
    (eisAut p z hz hp).map ((eisAut p w hw hp).map t)
      = (eisAut p ((zpRing p).mul z w) hzw hp).map t := by
  intro t
  induction t using Quot.ind; rename_i f
  exact congrArg (Quot.mk (eisRel p)) (psScale_comp (zpRing p) z w f)

/-- **定理 (M86F-6c): 単位律** — σ_1 = id（h1 は rpow_one_base で
    供給できる。代表元レベルの psScale_one_base）。 -/
theorem eisAut_one (p : Nat)
    (h1 : rpow (zpRing p) (zpRing p).one (p - 1) = (zpRing p).one)
    (hp : 2 ≤ p) : ∀ t, (eisAut p (zpRing p).one h1 hp).map t = t := by
  intro t
  induction t using Quot.ind; rename_i f
  exact congrArg (Quot.mk (eisRel p)) (psScale_one_base (zpRing p) f)

/-- **M86F-6d: σ は ζ のみに依存** — z = z' なら σ_z = σ_{z'}
    （証明項は無関係: subst 後は証明無関係性で rfl）。 -/
theorem eisAut_congr (p : Nat) {z z' : (Zp p).carrier} (hzz : z = z')
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one)
    (hz' : rpow (zpRing p) z' (p - 1) = (zpRing p).one)
    (hp : 2 ≤ p) : ∀ t,
    (eisAut p z hz hp).map t = (eisAut p z' hz' hp).map t := by
  subst hzz
  intro t
  rfl

/-! ## Teichmüller 実装: Galois 群の骨格 -/

/-- **M86F-7a: Teichmüller Galois 元** — σ_a := σ_{ω(a)}（p ∤ a、
    ω(a)^{p−1} = 1 は M84F-7a teich_pow_rpow_one）。
    a ∈ (ℤ/p)^× ごとの O の自己準同型。 -/
def eisGal (p : Nat) (hp : IsPrime p) (a : Int)
    (ha : ¬ ((p : Nat) : Int) ∣ a) : RingHom (eisRing p) (eisRing p) :=
  eisAut p (teich p hp a) (teich_pow_rpow_one p hp ha) hp.1

/-- **M86F-7b: 合成の ω 側の表示** — σ_a ∘ σ_b = σ_{ω(a)·ω(b)}
    （M86F-6b の実装、1 の冪根性は M86F-6a で閉じる）。 -/
theorem eisGal_comp (p : Nat) (hp : IsPrime p) {a b : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) (hb : ¬ ((p : Nat) : Int) ∣ b) : ∀ t,
    (eisGal p hp a ha).map ((eisGal p hp b hb).map t)
      = (eisAut p ((zpRing p).mul (teich p hp a) (teich p hp b))
          (rpow_one_mul_closed (zpRing p) (p - 1)
            (teich_pow_rpow_one p hp ha) (teich_pow_rpow_one p hp hb))
          hp.1).map t :=
  eisAut_comp p (teich p hp a) (teich p hp b)
    (teich_pow_rpow_one p hp ha) (teich_pow_rpow_one p hp hb)
    (rpow_one_mul_closed (zpRing p) (p - 1)
      (teich_pow_rpow_one p hp ha) (teich_pow_rpow_one p hp hb)) hp.1

/-- **定理 (M86F-7c): 乗法性** — σ_a ∘ σ_b = σ_{ab}
    （M33-8a teich_mul: ω(ab) = ω(a)·ω(b) + M86F-6d）。
    a ↦ σ_a は (ℤ/p)^× の乗法を O の自己準同型の合成に運ぶ。 -/
theorem eisGal_mul (p : Nat) (hp : IsPrime p) {a b : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) (hb : ¬ ((p : Nat) : Int) ∣ b)
    (hab : ¬ ((p : Nat) : Int) ∣ (a * b)) : ∀ t,
    (eisGal p hp a ha).map ((eisGal p hp b hb).map t)
      = (eisGal p hp (a * b) hab).map t := by
  intro t
  rw [eisGal_comp p hp ha hb t]
  exact eisAut_congr p (teich_mul p hp a b).symm
    (rpow_one_mul_closed (zpRing p) (p - 1)
      (teich_pow_rpow_one p hp ha) (teich_pow_rpow_one p hp hb))
    (teich_pow_rpow_one p hp hab) hp.1 t

/-- **定理 (M86F-8): 相異性 — Gal ≅ (ℤ/p)^× の下界** —
    p ∤ (a − b) なら σ_a(λ) ≠ σ_b(λ)、特に σ_a ≠ σ_b:
    1 ≤ a < b < p の代表で **p−1 個の相異なる自己準同型**が立つ
    （M86F-5b で λ の像を ω(a)λ に読み、M84F-7d teich_conj_distinct）。 -/
theorem eisGal_distinct (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    {a b : Int} (ha : ¬ ((p : Nat) : Int) ∣ a)
    (hb : ¬ ((p : Nat) : Int) ∣ b)
    (hab : ¬ ((p : Nat) : Int) ∣ (a - b)) :
    (eisGal p hp a ha).map (eisLambda p)
      ≠ (eisGal p hp b hb).map (eisLambda p) := by
  rw [show (eisGal p hp a ha).map (eisLambda p)
      = (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p) from
      eisAut_lambda p (teich p hp a) (teich_pow_rpow_one p hp ha) hp.1,
    show (eisGal p hp b hb).map (eisLambda p)
      = (eisRing p).mul ((eisOf p).map (teich p hp b)) (eisLambda p) from
      eisAut_lambda p (teich p hp b) (teich_pow_rpow_one p hp hb) hp.1]
  exact teich_conj_distinct p hp hodd hab

/-! ## ストレッチ: Galois 作用と Lubin–Tate 作用の可換性 -/

/-- **定理 (M86F-9): σ_ζ は [π]-作用と可換** —
    σ_ζ(f(t)) = f(σ_ζ(t))（f(T) = πT + T^p）: π は固定（M86F-5a）、
    積と冪は環準同型簿記（map_mul + ringHom_rpow）。
    **Galois 作用は Lubin–Tate 作用と両立** — rec 接続への布石。 -/
theorem eisAut_eisF (p : Nat) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) (hp : 2 ≤ p)
    (t : (eisRing p).carrier) :
    (eisAut p z hz hp).map (eisF p t)
      = eisF p ((eisAut p z hz hp).map t) := by
  show (eisAut p z hz hp).map
      ((eisRing p).add
        ((eisRing p).mul ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) t)
        (rpow (eisRing p) t p))
    = eisF p ((eisAut p z hz hp).map t)
  rw [(eisAut p z hz hp).map_add, (eisAut p z hz hp).map_mul,
    eisAut_const p z hz hp ((toZp p).map ((p : Nat) : Int)),
    ringHom_rpow (eisAut p z hz hp) t p]
  rfl

end IUT
