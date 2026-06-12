/-
  IUT/UnitDecomposition.lean — M35（単数分解 O^× = μ_{p−1} × U^(1)）

  局所体 ℚ_p の単数群の標準分解。レベル 1 で p と素な剰余 a を持つ
  任意の x : ℤ_p は **x = ω(a)·u（u は主単数）と一意に分解**する。
  μ 部（M33–M34 の Teichmüller 代表）と U^(1) 部（M30 の主単数群）が
  ここで結合し、LCFT の単数側の構造論が完成する。

  * M35-1 `zpMul_assoc` / `zpOne_mul` — ℤ_p 乗法の結合則・単位元
    （成分ごとの Int 恒等式）
  * M35-2 `isPrincipalUnit_of_level_one` — **主単数性のレベル 1 判定**:
    x ≡ 1 (mod p) なら全レベルで ≡ 1（整合性 + 商の exactness）
  * M35-3 `teich_pow_congr` / `teich_congr` — **ω は剰余のみに依存**:
    a ≡ b (mod p) ⟹ ω(a) = ω(b)（持ち上げ補題の反復で
    p^n ∣ a^{p^n} − b^{p^n}）。分解の一意性の核
  * M35-4 `unit_decomposition` — **存在**: x ≡ a (mod p)、p ∤ a なら
    x = ω(a)·u となる主単数 u が存在（u = ω(a)^{p−2}·x の明示構成。
    主単数性は恒等式 p(p−2) + 1 = (p−1)² と古典形 Fermat から）
  * M35-5 `decomposition_unique` — **一意性**: ω(a)·u = ω(b)·u'
    （u, u' 主単数）なら ω(a) = ω(b) かつ u = u'
    （レベル 1 の合同の望遠鏡和 + ω(a)^{p−2} による消去）

  未形式化: Lubin–Tate 形式群・分岐相互法則の Galois 側との同定。
  全て選択公理不使用。
-/
import IUT.RootsOfUnity

namespace IUT

/-! ## ℤ_p 乗法の結合則と単位元 -/

/-- ℤ_p の乗法は結合的。 -/
theorem zpMul_assoc (p : Nat) (x y z : (Zp p).carrier) :
    zpMul p (zpMul p x y) z = zpMul p x (zpMul p y z) := by
  apply Subtype.ext
  funext n
  show zmodMul (p ^ n) (zmodMul (p ^ n) (x.val n) (y.val n)) (z.val n)
    = zmodMul (p ^ n) (x.val n) (zmodMul (p ^ n) (y.val n) (z.val n))
  induction x.val n using Quot.ind; rename_i a
  induction y.val n using Quot.ind; rename_i b
  induction z.val n using Quot.ind; rename_i c
  show Quot.mk (modCong (p ^ n)).rel (a * b * c)
    = Quot.mk (modCong (p ^ n)).rel (a * (b * c))
  rw [Int.mul_assoc]

/-- 1 は ℤ_p 乗法の左単位元。 -/
theorem zpOne_mul (p : Nat) (x : (Zp p).carrier) : zpMul p (zpOne p) x = x := by
  apply Subtype.ext
  funext n
  show zmodMul (p ^ n) (Quot.mk (modCong (p ^ n)).rel 1) (x.val n) = x.val n
  induction x.val n using Quot.ind; rename_i a
  show Quot.mk (modCong (p ^ n)).rel (1 * a) = Quot.mk (modCong (p ^ n)).rel a
  rw [Int.one_mul]

/-! ## 主単数性のレベル 1 判定 -/

/-- **定理 (M35-2): 主単数性のレベル 1 判定** — x ≡ 1 (mod p) なら
    x は主単数（高レベルの代表は整合性により自動的に ≡ 1 mod p）。 -/
theorem isPrincipalUnit_of_level_one (p : Nat) (x : (Zp p).carrier)
    (hx : x.val 1 = Quot.mk (modCong (p ^ 1)).rel 1) :
    IsPrincipalUnit p x := by
  intro n
  cases n with
  | zero =>
    refine ⟨1, ?_, ⟨0, by omega⟩⟩
    induction x.val 0 using Quot.ind
    rename_i b
    apply Quot.sound
    show ((p ^ 0 : Nat) : Int) ∣ b - 1
    rw [Nat.pow_zero]
    exact Int.one_dvd _
  | succ m =>
    obtain ⟨c, hc⟩ := Quot.exists_rep (x.val (m + 1))
    have hcomp : (zmodTrans (pow_dvd_mono p (show 1 ≤ m + 1 by omega))).map
        (x.val (m + 1)) = x.val 1 := x.property (show 1 ≤ m + 1 by omega)
    rw [← hc, hx] at hcomp
    have hQ : Quot.mk (modCong (p ^ 1)).rel c
        = Quot.mk (modCong (p ^ 1)).rel 1 := hcomp
    have hrel := quot_exact intGrp (modCong (p ^ 1)) hQ
    refine ⟨c, hc.symm, ?_⟩
    apply dvd_sub_symm
    show ((p : Nat) : Int) ∣ c - 1
    have h1 : ((p ^ 1 : Nat) : Int) ∣ c - 1 := hrel
    rw [Nat.pow_one] at h1
    exact h1

/-! ## ω は剰余のみに依存（一意性の核） -/

/-- **M35-3a**: a ≡ b (mod p) なら p^n ∣ a^{p^n} − b^{p^n}
    （持ち上げ補題の反復）。 -/
theorem teich_pow_congr (p : Nat) (hp : IsPrime p) {a b : Int}
    (h : ((p : Nat) : Int) ∣ a - b) : ∀ n,
    ((p ^ n : Nat) : Int) ∣ ipow a (p ^ n) - ipow b (p ^ n) := by
  intro n
  cases n with
  | zero =>
    show ((p ^ 0 : Nat) : Int) ∣ ipow a (p ^ 0) - ipow b (p ^ 0)
    rw [Nat.pow_zero]
    exact Int.one_dvd _
  | succ m =>
    induction m with
    | zero =>
      show ((p ^ 1 : Nat) : Int) ∣ ipow a (p ^ 1) - ipow b (p ^ 1)
      rw [Nat.pow_one]
      exact dvd_sub_ipow h p
    | succ m ihm =>
      have hl := pow_lift p hp ihm (by omega)
      rw [← ipow_mul, ← ipow_mul, ← Nat.pow_succ] at hl
      exact hl

/-- **定理 (M35-3b): ω は剰余のみに依存** — a ≡ b (mod p) なら
    ω(a) = ω(b)。Teichmüller 代表が剰余類の標準持ち上げである理由。 -/
theorem teich_congr (p : Nat) (hp : IsPrime p) {a b : Int}
    (h : ((p : Nat) : Int) ∣ a - b) : teich p hp a = teich p hp b := by
  apply Subtype.ext
  funext n
  show Quot.mk (modCong (p ^ n)).rel (ipow a (p ^ n))
    = Quot.mk (modCong (p ^ n)).rel (ipow b (p ^ n))
  exact Quot.sound (teich_pow_congr p hp h n)

/-! ## 単数分解 -/

/-- **定理 (M35-4): 単数分解の存在** — x ≡ a (mod p)、p ∤ a なら
    x = ω(a)·u となる主単数 u が存在する（u = ω(a)^{p−2}·x の明示
    構成）。主単数性は p(p−2) + 1 = (p−1)² と古典形 Fermat による
    レベル 1 計算に帰着。 -/
theorem unit_decomposition (p : Nat) (hp : IsPrime p) (x : (Zp p).carrier)
    {a : Int} (ha : ¬ ((p : Nat) : Int) ∣ a)
    (hx : x.val 1 = Quot.mk (modCong (p ^ 1)).rel a) :
    ∃ u, IsPrincipalUnit p u ∧ x = zpMul p (teich p hp a) u := by
  refine ⟨zpMul p (zpPow p (teich p hp a) (p - 2)) x, ?_, ?_⟩
  · apply isPrincipalUnit_of_level_one
    show zmodMul (p ^ 1) (zmodPow (p ^ 1) ((teich p hp a).val 1) (p - 2)) (x.val 1)
      = Quot.mk (modCong (p ^ 1)).rel 1
    rw [hx]
    show Quot.mk (modCong (p ^ 1)).rel (ipow (ipow a (p ^ 1)) (p - 2) * a)
      = Quot.mk (modCong (p ^ 1)).rel 1
    apply Quot.sound
    show ((p ^ 1 : Nat) : Int) ∣ ipow (ipow a (p ^ 1)) (p - 2) * a - 1
    rw [Nat.pow_one, ← ipow_mul]
    obtain ⟨q, hq⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.1; omega⟩
    subst hq
    have he2 : q + 2 - 2 = q := by omega
    rw [he2]
    have hsq : (q + 2) * q + 1 = (q + 1) * (q + 1) := by
      rw [Nat.add_mul q 2 q, Nat.add_mul q 1 (q + 1), Nat.mul_add q q 1]
      generalize q * q = Q
      omega
    have hE : ipow (ipow a (q + 1)) (q + 1) = ipow a ((q + 2) * q) * a := by
      rw [← ipow_mul, ← hsq, ipow_add]
      show ipow a ((q + 2) * q) * ((1 : Int) * a) = ipow a ((q + 2) * q) * a
      rw [Int.one_mul]
    rw [← hE]
    have hF := flt_unit (q + 2) hp ha
    have hq1 : q + 2 - 1 = q + 1 := by omega
    rw [hq1] at hF
    have hpow := dvd_sub_ipow hF (q + 1)
    rw [one_ipow] at hpow
    exact hpow
  · rw [← zpMul_assoc]
    have hv : zpMul p (teich p hp a) (zpPow p (teich p hp a) (p - 2)) = zpOne p := by
      rw [zpMul_comm, ← zpPow_succ]
      have hpp : p - 2 + 1 = p - 1 := by have := hp.1; omega
      rw [hpp]
      exact teich_root_of_unity p hp ha
    rw [hv, zpOne_mul]

/-- **定理 (M35-5): 単数分解の一意性** — ω(a)·u = ω(b)·u'（u, u'
    主単数）なら ω(a) = ω(b) かつ u = u'。レベル 1 の合同の望遠鏡和
    （FLT 2 回 + 主単数性 2 回）と ω(a)^{p−2} による消去。 -/
theorem decomposition_unique (p : Nat) (hp : IsPrime p) {a b : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) {u u' : (Zp p).carrier}
    (hu : IsPrincipalUnit p u) (hu' : IsPrincipalUnit p u')
    (heq : zpMul p (teich p hp a) u = zpMul p (teich p hp b) u') :
    teich p hp a = teich p hp b ∧ u = u' := by
  obtain ⟨c, hc, hpc⟩ := hu 1
  obtain ⟨c', hc', hpc'⟩ := hu' 1
  have h1 : zmodMul (p ^ 1) ((teich p hp a).val 1) (u.val 1)
      = zmodMul (p ^ 1) ((teich p hp b).val 1) (u'.val 1) :=
    congrArg (fun w => w.val 1) heq
  rw [hc, hc'] at h1
  have h1' : Quot.mk (modCong (p ^ 1)).rel (ipow a (p ^ 1) * c)
      = Quot.mk (modCong (p ^ 1)).rel (ipow b (p ^ 1) * c') := h1
  have hrel := quot_exact intGrp (modCong (p ^ 1)) h1'
  have hrel' : ((p ^ 1 : Nat) : Int) ∣ ipow a (p ^ 1) * c - ipow b (p ^ 1) * c' :=
    hrel
  rw [Nat.pow_one] at hrel'
  have e1 : ((p : Nat) : Int) ∣ a - ipow a p :=
    dvd_sub_symm (fermat_little p hp a)
  have e2 : ((p : Nat) : Int) ∣ ipow a p - ipow a p * c := by
    obtain ⟨w, hw⟩ := dvd_mul_of_dvd hpc (ipow a p)
    refine ⟨w, ?_⟩
    rw [← hw, Int.mul_sub, Int.mul_one]
  have e4 : ((p : Nat) : Int) ∣ ipow b p * c' - ipow b p := by
    obtain ⟨w, hw⟩ := dvd_mul_of_dvd (dvd_sub_symm hpc') (ipow b p)
    refine ⟨w, ?_⟩
    rw [← hw, Int.mul_sub, Int.mul_one]
  have e5 := fermat_little p hp b
  have hab : ((p : Nat) : Int) ∣ a - b :=
    dvd_sub_trans (dvd_sub_trans (dvd_sub_trans (dvd_sub_trans e1 e2) hrel') e4) e5
  have hteich := teich_congr p hp hab
  refine ⟨hteich, ?_⟩
  rw [← hteich] at heq
  have h2 : zpMul p (zpPow p (teich p hp a) (p - 2)) (zpMul p (teich p hp a) u)
      = zpMul p (zpPow p (teich p hp a) (p - 2)) (zpMul p (teich p hp a) u') :=
    congrArg (fun w => zpMul p (zpPow p (teich p hp a) (p - 2)) w) heq
  rw [← zpMul_assoc, ← zpMul_assoc] at h2
  have hv : zpMul p (zpPow p (teich p hp a) (p - 2)) (teich p hp a) = zpOne p := by
    rw [← zpPow_succ]
    have hpp : p - 2 + 1 = p - 1 := by have := hp.1; omega
    rw [hpp]
    exact teich_root_of_unity p hp ha
  rw [hv, zpOne_mul, zpOne_mul] at h2
  exact h2

end IUT
