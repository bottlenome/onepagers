/-
  IUT/EisensteinConjugates.lean — M84F（共役捻れ点族 {ω(a)·λ} の構成と
  相異性）

  M83F は λ ∈ O = ℤ_p[[X]]/(X^{p−1} + π) が非自明な π-捻れ点であることを
  完全認定した。古典的には Λ₁ \ {0} = {ζλ : ζ^{p−1} = 1} は p−1 個の
  共役点からなる。本ファイルはその **Teichmüller 倍の族 {ω(a)·λ}**
  （p ∤ a）を構成し、(i) 各 ω(a)·λ が全ての [πⁿ]（n ≥ 1）で消える
  捻れ点であること、(ii) ω(a)·λ ≠ 0、(iii) p ∤ (a − b) なら
  **ω(a)·λ ≠ ω(b)·λ**（相異性）を機械検証する。これにより Λ₁ は
  0 と p−1 個の相異なる非自明点を含む（**下界 ≥ p 点**）。

  * M84F-1 `zpPow_eq_rpow` — 冪の橋渡し: M34 の zpPow と環冪 rpow の
    一致（n の帰納、レベルごとの Quot.ind）
  * M84F-2 `ringHom_map_neg` — 環準同型は負元を保つ（map_add +
    加法逆元の一意性 neg_eq_of_add_eq_zero、RingHom に neg 場は無い）
  * M84F-3 `eisF_semilinear` — **f(ζt) = ζ·f(t)**（ζ^{p−1} = 1）:
    π(ζt) = ζ(πt)（mul_left_comm）、(ζt)^p = ζ^p t^p = ζ t^p
    （rpow_mul_dist + 指数分割 p = (p−1)+1 + ringHom_rpow + 仮定）
  * M84F-4 `conj_is_torsion` — **[πⁿ](ζλ) = 0（∀ n ≥ 1）**:
    f(ζλ) = ζ·f(λ) = ζ·0 = 0、以降は eisIter_zero（M83F-5 と同型）
  * M84F-5 `conj_ne_zero` — **ζλ ≠ 0**（ζ が単元なら）:
    ζλ = 0 なら λ = v(ζλ) = 0 で eis_lambda_ne_zero（M83F-6）に矛盾
  * M84F-6 `conj_distinct` — **相異性**: z − w が単元なら
    zλ ≠ wλ（差を取ると (z−w)λ = 0、M84F-5 の論法で矛盾）
  * M84F-7 `teich_pow_rpow_one` / `teich_conj_torsion` /
    `teich_conj_ne_zero` / `teich_conj_distinct` — **Teichmüller 実装**:
    ω(a)^{p−1} = 1（M34-5 を rpow 形に橋渡し）、逆元は M36 の
    zpUnitInv、相異性は ω(a) − ω(b) ≡ a − b (mod p)（M33-7
    teich_reduction）で差がレベル 1 単数（M36-1 IsZpUnit）
  * M84F-8 `lambda_one_torsion_family` / `lambda_one_family_distinct` —
    **族のパッケージ**: 1 ≤ a < p で ω(a)λ は [π]-捻れかつ ≠ 0、
    1 ≤ a < b < p で ω(a)λ ≠ ω(b)λ（p−1 個の相異なる非自明捻れ点）

  これは Λ₁ の下界（0 と p−1 個の共役点で ≥ p 点）。上界（Λ₁ が
  ちょうど p 点 = 位数 p の巡回 ℤ/p-加群であること）・O の整域性・
  Galois 軌道としての記述は未形式化。p = 2 の除外（hodd : 3 ≤ p）は
  λ ≠ 0 が M83F-6 の係数比較に依存するため（同じ正直申告）。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.EisensteinTorsion

namespace IUT

/-! ## 冪の橋渡しと負元の保存 -/

/-- **M84F-1: zpPow = rpow** — M34 のレベルごとの冪 zpPow は
    環冪 rpow (zpRing p) と一致する（n の帰納、基底はレベルごとの
    Quot.ind で ipow a 0 = 1、帰納段は zpPow_succ）。 -/
theorem zpPow_eq_rpow (p : Nat) (x : (Zp p).carrier) : ∀ k,
    zpPow p x k = rpow (zpRing p) x k := by
  intro k
  induction k with
  | zero =>
    apply Subtype.ext
    funext n
    show zmodPow (p ^ n) (x.val n) 0 = Quot.mk (modCong (p ^ n)).rel 1
    induction x.val n using Quot.ind
    rfl
  | succ k ih =>
    rw [zpPow_succ p x k, ih]
    rfl

/-- **M84F-2: 環準同型は負元を保つ** — RingHom に neg 場は無いが、
    map(a) + map(−a) = map(a + (−a)) = map(0) = 0 と加法逆元の一意性
    （M42 の neg_eq_of_add_eq_zero）から導出できる。 -/
theorem ringHom_map_neg {R S : CRing} (φ : RingHom R S) (a : R.carrier) :
    φ.map (R.neg a) = S.neg (φ.map a) := by
  refine (CRing.neg_eq_of_add_eq_zero S ?_).symm
  rw [← φ.map_add a (R.neg a), CRing.add_neg R a, φ.map_zero]

/-! ## f の半線形性 f(ζt) = ζ·f(t) -/

/-- **定理 (M84F-3): f は 1 の (p−1) 乗根倍と可換** —
    ζ^{p−1} = 1 なら f(ζt) = ζ·f(t)。π(ζt) = ζ(πt) は左交換、
    (ζt)^p = ζ^p·t^p（rpow_mul_dist）と ζ^p = ζ^{p−1}·ζ = ζ
    （指数分割 p = (p−1)+1 は congrArg、ζ^{p−1} = (eisOf z^{p−1})
    = eisOf(1) = 1 は ringHom_rpow + 仮定 + map_one）、最後に分配。 -/
theorem eisF_semilinear (p : Nat) (hp : 2 ≤ p) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one)
    (t : (eisRing p).carrier) :
    eisF p ((eisRing p).mul ((eisOf p).map z) t)
      = (eisRing p).mul ((eisOf p).map z) (eisF p t) := by
  have hzeta : rpow (eisRing p) ((eisOf p).map z) p = (eisOf p).map z := by
    have hsplit : rpow (eisRing p) ((eisOf p).map z) p
        = (eisRing p).mul (rpow (eisRing p) ((eisOf p).map z) (p - 1))
            ((eisOf p).map z) :=
      congrArg (rpow (eisRing p) ((eisOf p).map z))
        (show p = (p - 1) + 1 by omega)
    rw [hsplit, ← ringHom_rpow (eisOf p) z (p - 1), hz, (eisOf p).map_one,
      (eisRing p).one_mul]
  show (eisRing p).add
      ((eisRing p).mul ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
        ((eisRing p).mul ((eisOf p).map z) t))
      (rpow (eisRing p) ((eisRing p).mul ((eisOf p).map z) t) p)
    = (eisRing p).mul ((eisOf p).map z) (eisF p t)
  rw [CRing.mul_left_comm (eisRing p)
      ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) ((eisOf p).map z) t,
    rpow_mul_dist (eisRing p) ((eisOf p).map z) t p, hzeta,
    ← (eisRing p).left_distrib ((eisOf p).map z)
      ((eisRing p).mul ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) t)
      (rpow (eisRing p) t p)]
  rfl

/-! ## 共役点 ζλ は捻れ点 -/

/-- **定理 (M84F-4): [πⁿ](ζλ) = 0（∀ n ≥ 1）** — ζ^{p−1} = 1 なら
    ζλ も全ての正の反復で消える: f(ζλ) = ζ·f(λ) = ζ·0 = 0
    （M84F-3 + M83F-4 + mul_zero）、以降は M83F-3b の降下。 -/
theorem conj_is_torsion (p : Nat) (hp : 2 ≤ p) (z : (Zp p).carrier)
    (hz : rpow (zpRing p) z (p - 1) = (zpRing p).one) : ∀ n, 1 ≤ n →
    eisIter p n ((eisRing p).mul ((eisOf p).map z) (eisLambda p))
      = (eisRing p).zero := by
  intro n hn
  cases n with
  | zero => exact absurd hn (by omega)
  | succ m =>
    show eisIter p m
        (eisF p ((eisRing p).mul ((eisOf p).map z) (eisLambda p)))
      = (eisRing p).zero
    rw [eisF_semilinear p hp z hz (eisLambda p), eisF_lambda p hp,
      CRing.mul_zero (eisRing p) ((eisOf p).map z)]
    exact eisIter_zero p hp m

/-! ## 共役点の非自明性と相異性 -/

/-- **定理 (M84F-5): ζλ ≠ 0**（ζ = eisOf z、z は明示逆元 v を持つ）—
    ζλ = 0 なら λ = (vz)λ = v(ζλ) = v·0 = 0 で M83F-6 に矛盾。 -/
theorem conj_ne_zero (p : Nat) (hodd : 3 ≤ p) (z v : (Zp p).carrier)
    (hzv : (zpRing p).mul z v = (zpRing p).one) :
    (eisRing p).mul ((eisOf p).map z) (eisLambda p) ≠ (eisRing p).zero := by
  intro h
  apply eis_lambda_ne_zero p hodd
  have h1 : eisLambda p
      = (eisRing p).mul ((eisOf p).map v)
          ((eisRing p).mul ((eisOf p).map z) (eisLambda p)) := by
    rw [← (eisRing p).mul_assoc ((eisOf p).map v) ((eisOf p).map z)
        (eisLambda p),
      ← (eisOf p).map_mul v z, (zpRing p).mul_comm v z, hzv,
      (eisOf p).map_one, (eisRing p).one_mul]
  rw [h1, h]
  exact CRing.mul_zero (eisRing p) ((eisOf p).map v)

/-- **定理 (M84F-6): 相異性** — z − w が明示逆元 v を持つ単元なら
    zλ ≠ wλ。等しいとすると (z−w)λ = zλ − wλ = 0（map_add +
    ringHom_map_neg + 右分配 + neg_mul + add_neg）で M84F-5 に矛盾。 -/
theorem conj_distinct (p : Nat) (hodd : 3 ≤ p) (z w v : (Zp p).carrier)
    (hunit : (zpRing p).mul ((zpRing p).add z ((zpRing p).neg w)) v
      = (zpRing p).one) :
    (eisRing p).mul ((eisOf p).map z) (eisLambda p)
      ≠ (eisRing p).mul ((eisOf p).map w) (eisLambda p) := by
  intro h
  apply conj_ne_zero p hodd ((zpRing p).add z ((zpRing p).neg w)) v hunit
  rw [(eisOf p).map_add z ((zpRing p).neg w), ringHom_map_neg (eisOf p) w,
    CRing.right_distrib (eisRing p) ((eisOf p).map z)
      ((eisRing p).neg ((eisOf p).map w)) (eisLambda p),
    CRing.neg_mul (eisRing p) ((eisOf p).map w) (eisLambda p), h]
  exact CRing.add_neg (eisRing p)
    ((eisRing p).mul ((eisOf p).map w) (eisLambda p))

/-! ## Teichmüller 実装: ω(a)·λ の族 -/

/-- **M84F-7a: ω(a)^{p−1} = 1（rpow 形）** — M34-5 の
    teich_root_of_unity（zpPow 形）を M84F-1 の橋で環冪に運ぶ。 -/
theorem teich_pow_rpow_one (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) :
    rpow (zpRing p) (teich p hp a) (p - 1) = (zpRing p).one := by
  rw [← zpPow_eq_rpow p (teich p hp a) (p - 1)]
  exact teich_root_of_unity p hp ha

/-- **定理 (M84F-7b): ω(a)·λ は捻れ点** — [πⁿ](ω(a)λ) = 0（∀ n ≥ 1、
    p ∤ a）。M84F-4 の ζ := ω(a) への実装。 -/
theorem teich_conj_torsion (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) : ∀ n, 1 ≤ n →
    eisIter p n ((eisRing p).mul ((eisOf p).map (teich p hp a))
      (eisLambda p)) = (eisRing p).zero :=
  conj_is_torsion p hp.1 (teich p hp a) (teich_pow_rpow_one p hp ha)

/-- **定理 (M84F-7c): ω(a)·λ ≠ 0**（p ∤ a、p ≥ 3）— 逆元は M36 の
    明示構成 zpUnitInv（単数性は isZpUnit_teich、選択公理不使用）。 -/
theorem teich_conj_ne_zero (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    {a : Int} (ha : ¬ ((p : Nat) : Int) ∣ a) :
    (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p)
      ≠ (eisRing p).zero := by
  refine conj_ne_zero p hodd (teich p hp a)
    (zpUnitInv p hp (teich p hp a) (isZpUnit_teich p hp ha)) ?_
  rw [(zpRing p).mul_comm]
  exact zpUnitInv_mul p hp (teich p hp a) (isZpUnit_teich p hp ha)

/-- **定理 (M84F-7d): 共役点の相異性** — p ∤ (a − b) なら
    ω(a)λ ≠ ω(b)λ。ω(a) − ω(b) はレベル 1 で a − b に合同
    （M33-7 teich_reduction）なので M36 の単数判定 IsZpUnit を満たし、
    明示逆元 zpUnitInv で M84F-6 に渡せる。 -/
theorem teich_conj_distinct (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    {a b : Int} (hab : ¬ ((p : Nat) : Int) ∣ (a - b)) :
    (eisRing p).mul ((eisOf p).map (teich p hp a)) (eisLambda p)
      ≠ (eisRing p).mul ((eisOf p).map (teich p hp b)) (eisLambda p) := by
  have hd : IsZpUnit p
      ((zpRing p).add (teich p hp a) ((zpRing p).neg (teich p hp b))) := by
    refine ⟨a - b, ?_, hab⟩
    show (zmod (p ^ 1)).mul ((teich p hp a).val 1)
        ((zmod (p ^ 1)).inv ((teich p hp b).val 1))
      = Quot.mk (modCong (p ^ 1)).rel (a - b)
    rw [teich_reduction p hp a, teich_reduction p hp b]
    rfl
  refine conj_distinct p hodd (teich p hp a) (teich p hp b)
    (zpUnitInv p hp _ hd) ?_
  rw [(zpRing p).mul_comm]
  exact zpUnitInv_mul p hp _ hd

/-! ## 族のパッケージ: p−1 個の相異なる非自明捻れ点 -/

/-- 1 ≤ a < p なら p ∤ a（Int 版、Nat の割り切りに落として大小比較）。 -/
theorem nat_lt_not_dvd_int (p a : Nat) (h1 : 1 ≤ a) (h2 : a < p) :
    ¬ ((p : Nat) : Int) ∣ ((a : Nat) : Int) := by
  intro hd
  have hn : p ∣ a := Int.ofNat_dvd.mp hd
  have := Nat.le_of_dvd (by omega) hn
  omega

/-- **定理 (M84F-8a): [π]-捻れ点の族** — 各 1 ≤ a < p について
    ω(a)·λ は [π] で消える非自明な捻れ点（p ∤ a は大小比較から）。
    0 と合わせて Λ₁ は少なくとも p 点を含む（下界）。 -/
theorem lambda_one_torsion_family (p : Nat) (hp : IsPrime p)
    (hodd : 3 ≤ p) : ∀ a : Nat, 1 ≤ a → a < p →
    (eisIter p 1 ((eisRing p).mul ((eisOf p).map (teich p hp (a : Int)))
        (eisLambda p)) = (eisRing p).zero)
    ∧ ((eisRing p).mul ((eisOf p).map (teich p hp (a : Int))) (eisLambda p)
        ≠ (eisRing p).zero) := by
  intro a h1 h2
  have ha := nat_lt_not_dvd_int p a h1 h2
  exact ⟨teich_conj_torsion p hp ha 1 (by omega),
    teich_conj_ne_zero p hp hodd ha⟩

/-- **定理 (M84F-8b): 族の相異性** — 1 ≤ a < b < p なら
    ω(a)λ ≠ ω(b)λ（p ∣ a − b なら natAbs に落として
    0 < |a − b| < p の約数矛盾）。族は本当に p−1 個ある。 -/
theorem lambda_one_family_distinct (p : Nat) (hp : IsPrime p)
    (hodd : 3 ≤ p) : ∀ a b : Nat, 1 ≤ a → a < b → b < p →
    (eisRing p).mul ((eisOf p).map (teich p hp (a : Int))) (eisLambda p)
      ≠ (eisRing p).mul ((eisOf p).map (teich p hp (b : Int)))
          (eisLambda p) := by
  intro a b h1 h2 h3
  apply teich_conj_distinct p hp hodd
  intro hd
  have hn : p ∣ (((a : Nat) : Int) - ((b : Nat) : Int)).natAbs := by
    have h4 := Int.natAbs_dvd_natAbs.mpr hd
    rwa [Int.natAbs_natCast] at h4
  have hpos : 0 < (((a : Nat) : Int) - ((b : Nat) : Int)).natAbs := by omega
  have := Nat.le_of_dvd hpos hn
  omega

end IUT
