/-
  IUT/PadicDivision.lean — M43（p-進除算と Frobenius 合同: 存在側の除算インフラ）

  Lubin–Tate 存在側の係数構成 F_n = E_n/(p^n − p) に必要な
  **p での除算**を ℤ_p 上に構成する。除算 zpDivP を

    (zpDivP x)_m := （x のレベル m+1 の代表 c）/ p   （Int の ediv）

  と定義すると、well-defined 性と遷移整合性が ediv の加法公式
  (c + T·p)/p = c/p + T から**無条件に**従う（代表元抽出も場合分けも
  不要 = choice-free・全域）。p ∣ x のとき真の除算になる。

  * M43-1 `int_div_shift` / `int_sub_to_add` — ediv の簿記（Int 束縛）
  * M43-2 `zmodDivP` / `zpDivP` — レベル写像 ℤ/p^{m+1} → ℤ/p^m と
    その整合束 ℤ_p → ℤ_p
  * M43-3 `zpDivP_mul_cancel` — **p·(x/p) = x**（x ≡ 0 mod p のとき。
    p ∣ 代表 が level-1 条件から全レベルで出る）
  * M43-4 `zpDivP_cancel` — **(p·e)/p = e**（無条件）
  * M43-5 `zp_dvd_p_iff` — **可除性の level-1 判定**:
    ∃e, x = p·e ⟺ x のレベル 1 射影 = 0
  * M43-6 `zp_flt` — **ℤ_p の Frobenius 合同**: x^p ≡ x (mod p)
    （レベル 1 で一致。M32 の FLT の成分適用）
  * M43-7 `zp_frobenius_divisible` — **x^p − x は p で割れる**
    （M43-5 + M43-6。LT 誤差項の p-整除性の原型）

  残り: PS(ℤ_p) 上の新入生の夢 → 誤差項の p-整除性 → 係数の再帰構成。
  全て選択公理不使用。
-/
import IUT.LubinTateZp

namespace IUT

/-! ## ediv の簿記 -/

/-- 簿記: C − C' = W なら C = C' + W。 -/
theorem int_sub_to_add (C C' W : Int) (h : C - C' = W) : C = C' + W := by
  omega

/-- 簿記: C − 0 = P·k なら P ∣ C（Int 束縛）。 -/
theorem int_dvd_of_sub_zero (P C k : Int) (h : C - 0 = P * k) : P ∣ C := by
  refine ⟨k, ?_⟩
  revert h
  generalize P * k = W
  intro h
  omega

/-- **M43-1: ediv のシフト** — C = C' + T·P なら C/P − C'/P = T。 -/
theorem int_div_shift (P C C' T : Int) (hP : P ≠ 0) (h : C = C' + T * P) :
    C / P - C' / P = T := by
  rw [h, Int.add_mul_ediv_right C' T hP]
  generalize C' / P = Q
  omega

/-! ## p-進除算 -/

/-- **M43-2a: レベルごとの p-除算** ℤ/p^{m+1} → ℤ/p^m
    （代表の ediv。well-defined 性は ediv の加法公式から無条件）。 -/
def zmodDivP (p m : Nat) (hp : 2 ≤ p) :
    (zmod (p ^ (m + 1))).carrier → (zmod (p ^ m)).carrier :=
  Quot.lift (fun c => Quot.mk (modCong (p ^ m)).rel (c / ((p : Nat) : Int)))
    (fun c c' h => Quot.sound (by
      obtain ⟨k, hk⟩ := h
      have he : ((p ^ (m + 1) : Nat) : Int) * k
          = (((p ^ m : Nat) : Int) * k) * ((p : Nat) : Int) := by
        rw [cast_pow_succ, Int.mul_assoc ((p ^ m : Nat) : Int) ((p : Nat) : Int) k,
          Int.mul_comm ((p : Nat) : Int) k,
          ← Int.mul_assoc ((p ^ m : Nat) : Int) k ((p : Nat) : Int)]
      rw [he] at hk
      have hc : c = c' + (((p ^ m : Nat) : Int) * k) * ((p : Nat) : Int) :=
        int_sub_to_add c c' _ hk
      exact ⟨k, int_div_shift ((p : Nat) : Int) c c'
        (((p ^ m : Nat) : Int) * k) (by omega) hc⟩))

/-- **M43-2b: p-進除算** ℤ_p → ℤ_p（レベルを 1 つ消費する整合束。
    遷移整合性は「同じ代表の同じ ediv」で rfl）。 -/
def zpDivP (p : Nat) (hp : 2 ≤ p) (x : (Zp p).carrier) : (Zp p).carrier :=
  ⟨fun m => zmodDivP p m hp (x.val (m + 1)), by
    intro i j h
    have hcomp : (zmodTrans (pow_dvd_mono p (Nat.succ_le_succ h))).map
        (x.val (j + 1)) = x.val (i + 1) := x.property (Nat.succ_le_succ h)
    show (zmodTrans (pow_dvd_mono p h)).map (zmodDivP p j hp (x.val (j + 1)))
      = zmodDivP p i hp (x.val (i + 1))
    rw [← hcomp]
    induction x.val (j + 1) using Quot.ind
    rfl⟩

/-- **定理 (M43-3): p·(x/p) = x**（x ≡ 0 mod p のとき）— level-1 条件
    から全レベルの代表の p-整除性が整合性で出る。 -/
theorem zpDivP_mul_cancel (p : Nat) (hp : 2 ≤ p) (x : (Zp p).carrier)
    (hx : x.val 1 = Quot.mk (modCong (p ^ 1)).rel 0) :
    zpMul p ((toZp p).map ((p : Nat) : Int)) (zpDivP p hp x) = x := by
  apply Subtype.ext
  funext m
  obtain ⟨c, hc⟩ := Quot.exists_rep (x.val (m + 1))
  have hcomp1 : (zmodTrans (pow_dvd_mono p (Nat.succ_le_succ (Nat.zero_le m)))).map
      (x.val (m + 1)) = x.val 1 := x.property (Nat.succ_le_succ (Nat.zero_le m))
  rw [← hc, hx] at hcomp1
  have hQ : Quot.mk (modCong (p ^ 1)).rel c
      = Quot.mk (modCong (p ^ 1)).rel 0 := hcomp1
  have hdvd : ((p : Nat) : Int) ∣ c := by
    obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (p ^ 1)) hQ
    have hk' : c - 0 = ((p ^ 1 : Nat) : Int) * k := hk
    rw [Nat.pow_one] at hk'
    exact int_dvd_of_sub_zero ((p : Nat) : Int) c k hk'
  show zmodMul (p ^ m) (Quot.mk (modCong (p ^ m)).rel ((p : Nat) : Int))
      (zmodDivP p m hp (x.val (m + 1))) = x.val m
  have hcm : (zmodTrans (pow_dvd_mono p (Nat.le_succ m))).map (x.val (m + 1))
      = x.val m := x.property (Nat.le_succ m)
  rw [← hc] at hcm
  rw [← hc, ← hcm]
  show Quot.mk (modCong (p ^ m)).rel (((p : Nat) : Int) * (c / ((p : Nat) : Int)))
    = Quot.mk (modCong (p ^ m)).rel c
  have he : ((p : Nat) : Int) * (c / ((p : Nat) : Int)) = c := by
    obtain ⟨e, he'⟩ := hdvd
    rw [he', Int.mul_ediv_cancel_left e (by omega)]
  rw [he]

/-- **定理 (M43-4): (p·e)/p = e**（無条件）。 -/
theorem zpDivP_cancel (p : Nat) (hp : 2 ≤ p) (e : (Zp p).carrier) :
    zpDivP p hp (zpMul p ((toZp p).map ((p : Nat) : Int)) e) = e := by
  apply Subtype.ext
  funext m
  obtain ⟨c, hc⟩ := Quot.exists_rep (e.val (m + 1))
  show zmodDivP p m hp (zmodMul (p ^ (m + 1))
      (Quot.mk (modCong (p ^ (m + 1))).rel ((p : Nat) : Int)) (e.val (m + 1)))
    = e.val m
  have hcm : (zmodTrans (pow_dvd_mono p (Nat.le_succ m))).map (e.val (m + 1))
      = e.val m := e.property (Nat.le_succ m)
  rw [← hc] at hcm
  rw [← hc, ← hcm]
  show Quot.mk (modCong (p ^ m)).rel
      ((((p : Nat) : Int) * c) / ((p : Nat) : Int))
    = Quot.mk (modCong (p ^ m)).rel c
  rw [Int.mul_ediv_cancel_left c (by omega)]

/-- **定理 (M43-5): 可除性の level-1 判定** —
    ∃e, x = p·e ⟺ x のレベル 1 射影が 0。 -/
theorem zp_dvd_p_iff (p : Nat) (hp : 2 ≤ p) (x : (Zp p).carrier) :
    (∃ e, x = zpMul p ((toZp p).map ((p : Nat) : Int)) e)
      ↔ x.val 1 = Quot.mk (modCong (p ^ 1)).rel 0 := by
  constructor
  · intro ⟨e, he⟩
    subst he
    obtain ⟨c, hc⟩ := Quot.exists_rep (e.val 1)
    show zmodMul (p ^ 1) (Quot.mk (modCong (p ^ 1)).rel ((p : Nat) : Int))
        (e.val 1) = Quot.mk (modCong (p ^ 1)).rel 0
    rw [← hc]
    apply Quot.sound
    show ((p ^ 1 : Nat) : Int) ∣ ((p : Nat) : Int) * c - 0
    rw [Nat.pow_one]
    refine ⟨c, ?_⟩
    generalize ((p : Nat) : Int) * c = W
    omega
  · intro hx
    exact ⟨zpDivP p hp x, (zpDivP_mul_cancel p hp x hx).symm⟩

/-! ## Frobenius 合同 -/

/-- 簿記: (A + (−A)) − 0 = N·0。 -/
theorem int_add_neg_zero (N A : Int) : A + (-A) - 0 = N * 0 := by omega

/-- **定理 (M43-6): ℤ_p の Frobenius 合同** — x^p ≡ x (mod p)
    （レベル 1 射影の一致。M32 の Fermat の小定理の成分適用）。 -/
theorem zp_flt (p : Nat) (hp : IsPrime p) (x : (Zp p).carrier) :
    (zpPow p x p).val 1 = x.val 1 := by
  obtain ⟨a, ha⟩ := Quot.exists_rep (x.val 1)
  show zmodPow (p ^ 1) (x.val 1) p = x.val 1
  rw [← ha]
  show Quot.mk (modCong (p ^ 1)).rel (ipow a p)
    = Quot.mk (modCong (p ^ 1)).rel a
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ ipow a p - a
  rw [Nat.pow_one]
  exact fermat_little p hp a

/-- **定理 (M43-7): x^p − x は p で割れる**（ℤ_p、構成的 witness =
    zpDivP）。Lubin–Tate 誤差項の p-整除性の原型。 -/
theorem zp_frobenius_divisible (p : Nat) (hp : IsPrime p) (x : (Zp p).carrier) :
    ∃ e, (zpRing p).add (zpPow p x p) ((zpRing p).neg x)
      = zpMul p ((toZp p).map ((p : Nat) : Int)) e := by
  apply (zp_dvd_p_iff p hp.1 _).mpr
  show (zmod (p ^ 1)).mul ((zpPow p x p).val 1) ((zmod (p ^ 1)).inv (x.val 1))
    = Quot.mk (modCong (p ^ 1)).rel 0
  rw [zp_flt p hp x]
  induction x.val 1 using Quot.ind
  rename_i a
  apply Quot.sound
  exact ⟨0, int_add_neg_zero ((p ^ 1 : Nat) : Int) a⟩

end IUT
