/-
  IUT/TorsionTrivial.lean — M81F（ℤ_p 内の πⁿ-捻れ点の自明性:
  非自明な捻れ点には分岐拡大が必要）

  M79F の逆向きの帳簿: 奇素数 p では Lubin–Tate 形式群の
  πⁿ-捻れ点は pℤ_p の中に自明なもの（x = 0）しかない。
  f(x) = x·(π + x^{p−1}) と点で因数分解し、補因子を
  π + x^{p−1} = π·(1 + π^{p−2}·e^{p−1}) と分解（x = πe）、
  単数部分 1 + π·w を主単数機械（M29/M30/M35/M36, M42）で消去し、
  p-正則性（M42-4）で x = 0 に至る。ゆえに非自明な等分点は
  分岐拡大にのみ住む — 分岐 LCFT が体拡大を要する理由の機械検証。

  * M81F-1 `ltIter_one` — [π¹] = f（ltIter p 1 = ltPoly p、psComp_X）
  * M81F-2 `lt_point_factor` — **点での因数分解**
    f(x) = x·(π + x^{p−1})（x^p = x·x^{p−1} の指数分割 + 分配律）
  * M81F-3 `cofactor_decomp` — **補因子の分解**（奇素数）:
    π + x^{p−1} = π·(1 + π^{p−2}·e^{p−1})（rpow_mul_dist + 指数分割）
  * M81F-4 `one_add_p_mul_unit` / `one_add_p_mul_regular` —
    **1 + π·w は単数ゆえ正則**（レベル 1 で 1 + pc、p ∤ 1 + pc。
    M36 の IsZpUnit + M42-5 zp_unit_regular で消去）
  * M81F-5 `torsion_one_trivial` — **π-捻れの自明性**（奇素数）:
    [π](x) = 0 ⟹ x = 0（x·(π·u) = π·(x·u) → p-正則性 M42-4 →
    単数正則性で x = 0）
  * M81F-6 `torsion_trivial` — **πⁿ-捻れの自明性**（n の帰納:
    漸化式 M79F-5 で f(x) に降下し、底は M79F-7b、段は M81F-5）

  p = 2 では −2 が非自明な 2-捻れ点（x(2+x) = 0）なので奇素数に
  限る（正直申告）。分岐拡大での非自明捻れ点の構成は未形式化。
  全て選択公理不使用。サブエージェント並行部品・
  「非自明な捻れ点には分岐拡大が必要」の機械検証。
-/
import IUT.TorsionPoints
import IUT.LubinTateZp

namespace IUT

/-! ## [π¹] = f -/

/-- **M81F-1: [π¹] = f** — ltIter p 1 = psComp X f = f（X は合成の
    左単位元、psComp_X）。 -/
theorem ltIter_one (p : Nat) (hp : 2 ≤ p) : ltIter p 1 = ltPoly p :=
  psComp_X (zpRing p) (ltPoly p) (ltPoly_coeff_zero p hp)

/-! ## 点での因数分解 -/

/-- **M81F-2: 点での因数分解** — f(x) = πx + x^p = x·(π + x^{p−1})。
    x^p = x·x^{p−1}（指数 p = (p−1)+1 の分割、p には触れず指数だけ
    congrArg で書き換え）+ 左分配律。 -/
theorem lt_point_factor (p : Nat) (hp : 2 ≤ p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltPoly p) x e hx
      = (zpRing p).mul x
          ((zpRing p).add ((toZp p).map ((p : Nat) : Int))
            (rpow (zpRing p) x (p - 1))) := by
  have h1 : rpow (zpRing p) x p = rpow (zpRing p) x ((p - 1) + 1) :=
    congrArg (rpow (zpRing p) x) (by omega)
  have hpow : rpow (zpRing p) x p
      = (zpRing p).mul x (rpow (zpRing p) x (p - 1)) := by
    rw [h1]
    exact (zpRing p).mul_comm (rpow (zpRing p) x (p - 1)) x
  rw [zpEval_ltPoly p hp x e hx, hpow,
    (zpRing p).mul_comm ((toZp p).map ((p : Nat) : Int)) x,
    ← (zpRing p).left_distrib x ((toZp p).map ((p : Nat) : Int))
      (rpow (zpRing p) x (p - 1))]

/-! ## 補因子の分解 -/

/-- **M81F-3: 補因子の分解**（奇素数）—
    π + x^{p−1} = π·(1 + π^{p−2}·e^{p−1})。x = πe から
    x^{p−1} = π^{p−1}·e^{p−1}（rpow_mul_dist）、
    π^{p−1} = π·π^{p−2}（指数 p−1 = (p−2)+1 の分割、p ≥ 3）、
    最後に左分配律で π をくくり出す。 -/
theorem cofactor_decomp (p : Nat) (hodd : 3 ≤ p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    (zpRing p).add ((toZp p).map ((p : Nat) : Int)) (rpow (zpRing p) x (p - 1))
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          ((zpRing p).add (zpRing p).one
            ((zpRing p).mul
              (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 2))
              (rpow (zpRing p) e (p - 1)))) := by
  have hx1 : rpow (zpRing p) x (p - 1)
      = (zpRing p).mul
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 1))
          (rpow (zpRing p) e (p - 1)) := by
    rw [hx]
    exact rpow_mul_dist (zpRing p) ((toZp p).map ((p : Nat) : Int)) e (p - 1)
  have h1 : rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 1)
      = rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) ((p - 2) + 1) :=
    congrArg (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))) (by omega)
  have hsplit : rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 1)
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 2)) := by
    rw [h1]
    exact (zpRing p).mul_comm
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 2))
      ((toZp p).map ((p : Nat) : Int))
  have hone : (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) (zpRing p).one
      = (toZp p).map ((p : Nat) : Int) := by
    rw [(zpRing p).mul_comm]
    exact (zpRing p).one_mul ((toZp p).map ((p : Nat) : Int))
  rw [hx1, hsplit,
    (zpRing p).mul_assoc ((toZp p).map ((p : Nat) : Int))
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 2))
      (rpow (zpRing p) e (p - 1)),
    (zpRing p).left_distrib ((toZp p).map ((p : Nat) : Int)) (zpRing p).one
      ((zpRing p).mul
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 2))
        (rpow (zpRing p) e (p - 1))),
    hone]

/-! ## 補因子の単数性と正則性 -/

/-- **M81F-4a: 1 + π·w は単数** — レベル 1 の成分は 1 + pc で、
    p ∤ 1 + pc（さもなくば p ∣ 1）。M36 の IsZpUnit の witness を
    明示構成（代表元は Quot.exists_rep、選択公理不使用）。 -/
theorem one_add_p_mul_unit (p : Nat) (hp : IsPrime p) (w : (Zp p).carrier) :
    IsZpUnit p ((zpRing p).add (zpRing p).one
      ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) w)) := by
  obtain ⟨c, hc⟩ := Quot.exists_rep (w.val 1)
  refine ⟨1 + ((p : Nat) : Int) * c, ?_, ?_⟩
  · show (zmod (p ^ 1)).mul (Quot.mk (modCong (p ^ 1)).rel 1)
        (zmodMul (p ^ 1) (Quot.mk (modCong (p ^ 1)).rel ((p : Nat) : Int))
          (w.val 1))
      = Quot.mk (modCong (p ^ 1)).rel (1 + ((p : Nat) : Int) * c)
    rw [← hc]
    rfl
  · intro hd
    obtain ⟨k, hk⟩ := hd
    apply not_dvd_one p hp.1
    refine ⟨k - c, ?_⟩
    rw [Int.mul_sub, ← hk]
    generalize ((p : Nat) : Int) * c = W
    omega

/-- **M81F-4b: 1 + π·w は正則** — (1 + π·w)·z = 0 ⟹ z = 0
    （M81F-4a + M42-5 zp_unit_regular の明示逆元消去）。 -/
theorem one_add_p_mul_regular (p : Nat) (hp : IsPrime p)
    (w z : (Zp p).carrier)
    (h : (zpRing p).mul
        ((zpRing p).add (zpRing p).one
          ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) w)) z
      = (zpRing p).zero) :
    z = (zpRing p).zero :=
  zp_unit_regular p hp (one_add_p_mul_unit p hp w) h

/-! ## π-捻れの自明性 -/

/-- **定理 (M81F-5): π-捻れの自明性**（奇素数）—
    x ∈ pℤ_p が [π](x) = f(x) = 0 を満たすなら x = 0。
    f(x) = x·(π + x^{p−1}) = x·(π·u) = π·(x·u)（u = 1 + π^{p−2}e^{p−1}
    は単数）なので、p-正則性（M42-4）で x·u = 0、単数正則性
    （M81F-4b）で x = 0。 -/
theorem torsion_one_trivial (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    (ht : IsTorsionPoint p 1 x e hx) : x = (zpRing p).zero := by
  have h0 : zpEval p (ltPoly p) x e hx = (zpRing p).zero :=
    (congrArg (fun H => zpEval p H x e hx) (ltIter_one p hp.1)).symm.trans ht
  have h1 : (zpRing p).mul x
      ((zpRing p).add ((toZp p).map ((p : Nat) : Int))
        (rpow (zpRing p) x (p - 1))) = (zpRing p).zero :=
    (lt_point_factor p hp.1 x e hx).symm.trans h0
  rw [cofactor_decomp p hodd x e hx] at h1
  have h2 : rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 2)
      = rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) ((p - 3) + 1) :=
    congrArg (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))) (by omega)
  have h3 : rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 2)
      = (zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 3)) := by
    rw [h2]
    exact (zpRing p).mul_comm
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 3))
      ((toZp p).map ((p : Nat) : Int))
  rw [h3,
    (zpRing p).mul_assoc ((toZp p).map ((p : Nat) : Int))
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 3))
      (rpow (zpRing p) e (p - 1)),
    CRing.mul_left_comm (zpRing p) x ((toZp p).map ((p : Nat) : Int))
      ((zpRing p).add (zpRing p).one
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          ((zpRing p).mul
            (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 3))
            (rpow (zpRing p) e (p - 1)))))] at h1
  have h4 : (zpRing p).mul x
      ((zpRing p).add (zpRing p).one
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          ((zpRing p).mul
            (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 3))
            (rpow (zpRing p) e (p - 1)))))
      = (zpRing p).zero := zp_p_regular p hp.1 h1
  have h5 : (zpRing p).mul
      ((zpRing p).add (zpRing p).one
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
          ((zpRing p).mul
            (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 3))
            (rpow (zpRing p) e (p - 1))))) x
      = (zpRing p).zero :=
    ((zpRing p).mul_comm _ x).trans h4
  exact one_add_p_mul_regular p hp
    ((zpRing p).mul
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 3))
      (rpow (zpRing p) e (p - 1))) x h5

/-! ## πⁿ-捻れの自明性 -/

/-- **定理 (M81F-6): πⁿ-捻れの自明性**（奇素数）—
    ℤ_p の中では Λ_n = ker [πⁿ] は自明: 任意の n で
    IsTorsionPoint p n x e hx ⟹ x = 0。n の帰納で、底は
    [π⁰] = X（M79F-7b）、段は漸化式 [πⁿ⁺¹](x) = [πⁿ](f(x))
    （M79F-5）で f(x) の n-捻れに降下 → f(x) = 0 → M81F-5。
    非自明な等分点は分岐拡大にのみ存在する。 -/
theorem torsion_trivial (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    ∀ (n : Nat) (x e : (Zp p).carrier)
      (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
      IsTorsionPoint p n x e hx → x = (zpRing p).zero := by
  intro n
  induction n with
  | zero =>
    intro x e hx ht
    exact (torsion_zero_iff p hp.1 x e hx).mp ht
  | succ n ih =>
    intro x e hx ht
    have hy0 : zpEval p (ltPoly p) x e hx = (zpRing p).zero :=
      ih (zpEval p (ltPoly p) x e hx)
        ((zpRing p).mul e (zpEval p (psShift (zpRing p) (ltPoly p)) x e hx))
        (zpEval_closed p hp.1 (ltPoly p) (ltPoly_coeff_zero p hp.1) x e hx)
        ((zpEval_ltIter_succ p hp.1 n x e hx).symm.trans ht)
    exact torsion_one_trivial p hp hodd x e hx
      ((congrArg (fun H => zpEval p H x e hx) (ltIter_one p hp.1)).trans hy0)

end IUT
