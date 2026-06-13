/-
  IUT/EisDomain.lean — M93F（柱B: 整域性 witness 版の O = ℤ_p[π] への
  移送・第一段 — 係数簿記・λ シフト・λ 割り算・剰余体乗法性）

  M91F は ℤ_p 上で witness 付き零因子なし（NeZeroAt による構成的
  非零性）を確立した。本モジュールはその理論を M82F の Eisenstein 環
  O = ℤ_p[[X]]/(E)（E = X^{p−1} + π）へ移送する第一段である。O の
  元は冪級数の (E)-合同類であり係数が直接見えないため、鍵は
  **被約係数写像**: λ^{p−1} = −π による簡約 cᵢ(f) = Σ_j (−π)^j
  f_{i+j(p−1)} のレベル n 打ち切りが、望遠鏡和 cᵢ(hE) =
  (−π)^{n−1}·π·h_{…} ≡ 0 (mod p^n) により商 O 上 well-defined に
  なることである（i < p−1）。

  * M93F-0 `negp_pow_decomp` / `zmod_rpow_mk` / `val_negPiPow_pi_mul`
    — 簿記: (−p)^n = p^n·(±1)、ℤ/N での冪と代表元の交換、
    レベル n+1 での (−π)^n·π·y の消滅
  * M93F-1a `psMul_eisPoly_low` / `psMul_eisPoly_high` — h·E の係数
    公式: (hE)_m = h_m·π（m < p−1）、(hE)_m = h_{m−(p−1)} + h_m·π
    （m ≥ p−1）
  * M93F-1b `eisCoeffZp` / `eisCoeffZp_add` / `eisCoeffZp_mulE_succ`
    — 被約係数（代表元上）とその加法性、(E) 倍の**望遠鏡和**
    （帰納による完全計算）
  * M93F-1c `eisCoeff` / `EisNeZeroAt` / `eisNeZeroAt_ne_zero` —
    **被約係数のレベル n 射影は O 上 well-defined**（Quot.lift、
    本モジュールの本丸その一）。witness 付き非零性 EisNeZeroAt と
    x ≠ 0 の含意
  * M93F-1d `eisCoeff_eisOf` / `eisOf_injective` / `eisOf_neZeroAt`
    — 構造射 ℤ_p → O との両立: c₀(eisOf a) = a のレベル n 成分。
    系として **eisOf は単射**（O は ℤ_p を忠実に含む）と witness の
    移送 NeZeroAt p a n → EisNeZeroAt (eisOf a) 0 n
  * M93F-2 `eisCoeff_lambda_mul` / `eisNeZeroAt_lambda_mul` /
    `eisNeZeroAt_lambda_wrap` / `eis_lambda_mul_ne_zero` — **λ 倍の
    係数簿記**: 域内では cᵢ₊₁(λx) = cᵢ(x)（witness は添字シフト）、
    巻き戻り（i = p−2 → 0）では c₀(λx) = −π·c_{p−2}(x)（witness は
    レベル +1 シフト、M91F の p キャンセル簿記で抽出）。系:
    **witness を持つ x について λ·x ≠ 0**
  * M93F-3 `eis_lambda_division` — **witness 付き λ 割り算**: 代表元
    f の定数項が f₀ = π·e なら mk f = λ·x′、x′ = shift(f) −
    X^{p−2}·e は明示構成（証人 psC e: f − X·x′ = C(e)·E）
  * M93F-4 `eisCoeffZp_one` / `eisCoeff_mul_one` / `eis_residue_mul`
    / `eis_unit_mul_ne_zero` — **剰余体乗法性（部分的本丸）**:
    c₀ のレベル 1 射影（剰余体 𝔽_p への写像）は乗法的、ℤ/p の
    零因子なし（M32 Bézout 経由）により**単数剰余の積は非零**
  * M93F-5 `EisDomainData` / `eisDomainData` / `eisDomain_nonempty`
    — 完成部分の束（係数の零性・非零含意・eisOf 単射と移送・
    λ シフト・λ 割り算・剰余乗法性・単数剰余積の非零）と witness、
    見出し定理

  **位置づけ（正直な申告）**: 一般の λ 進付値分解 x = λ^k·u
  （u 単数剰余）の強帰納法による構成と、それによる一般の積の
  witness 付き非零性 eis_mul_ne_zero（M90F の NoZeroDiv 仮定の
  無条件解消）は次層の課題である。本モジュールはその土台
  （well-defined な係数簿記・λ シフト両方向・λ 割り算・剰余
  乗法性）を完全証明で供給する。全て選択公理不使用。
  サブエージェント並行部品。
-/
import IUT.ZpDomain
import IUT.EisensteinRing

namespace IUT

/-! ## §0 簿記: π・−π とその冪 -/

/-- π = p の ℤ_p 像（略記）。 -/
def zpPi (p : Nat) : (Zp p).carrier := (toZp p).map ((p : Nat) : Int)

/-- −π（被約簡約の乗数 λ^{p−1} = −π）。 -/
def zpNegPi (p : Nat) : (Zp p).carrier := (zpRing p).neg (zpPi p)

/-- Int 上の素朴な冪（rpow intRing の Int 値版。`*` 記法の型クラス
    解決を構造体 carrier に阻まれないための自前再帰）。 -/
def intPow (c : Int) : Nat → Int
  | 0 => 1
  | k + 1 => intPow c k * c

/-- **M93F-0a**: (−p)^n = p^n·w となる witness w（= ±1）の存在
    （n の帰納、cast_pow_succ で桁送り）。 -/
theorem negp_pow_decomp (p : Nat) : ∀ n : Nat,
    ∃ w : Int, intPow (-((p : Nat) : Int)) n = ((p ^ n : Nat) : Int) * w := by
  intro n
  induction n with
  | zero =>
    refine ⟨1, ?_⟩
    show (1 : Int) = ((p ^ 0 : Nat) : Int) * 1
    rw [Nat.pow_zero]
    omega
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨-w, ?_⟩
    show intPow (-((p : Nat) : Int)) n * (-((p : Nat) : Int))
      = ((p ^ (n + 1) : Nat) : Int) * (-w)
    rw [hw, cast_pow_succ p n, Int.mul_assoc, Int.mul_assoc]
    have h2 : w * (-((p : Nat) : Int)) = ((p : Nat) : Int) * (-w) := by
      rw [Int.mul_neg, Int.mul_neg, Int.mul_comm w ((p : Nat) : Int)]
    rw [h2]

/-- **M93F-0b**: ℤ/N での冪は代表元の Int 冪。 -/
theorem zmod_rpow_mk (N : Nat) (c : Int) : ∀ k,
    rpow (zmodRing N) (Quot.mk (modCong N).rel c) k
      = Quot.mk (modCong N).rel (intPow c k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show zmodMul N (rpow (zmodRing N) (Quot.mk (modCong N).rel c) k)
        (Quot.mk (modCong N).rel c)
      = Quot.mk (modCong N).rel (intPow c k * c)
    rw [ih]
    rfl

/-- **M93F-0c**: レベル n では (−π)^k·y（n ≤ k）は消える。 -/
theorem val_negPiPow_mul (p : Nat) {n k : Nat} (hnk : n ≤ k)
    (y : (Zp p).carrier) :
    ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) k) y).val n
      = Quot.mk (modCong (p ^ n)).rel 0 := by
  obtain ⟨c, hc⟩ := Quot.exists_rep (y.val n)
  obtain ⟨w, hw⟩ := negp_pow_decomp p k
  have hcomp : (rpow (zpRing p) (zpNegPi p) k).val n
      = Quot.mk (modCong (p ^ n)).rel (intPow (-((p : Nat) : Int)) k) := by
    have h1 : (projRing p n).map (rpow (zpRing p) (zpNegPi p) k)
        = rpow (zmodRing (p ^ n)) ((projRing p n).map (zpNegPi p)) k :=
      ringHom_rpow (projRing p n) (zpNegPi p) k
    have h2 : (projRing p n).map (zpNegPi p)
        = Quot.mk (modCong (p ^ n)).rel (-((p : Nat) : Int)) := rfl
    rw [h2] at h1
    have h3 : (rpow (zpRing p) (zpNegPi p) k).val n
        = (projRing p n).map (rpow (zpRing p) (zpNegPi p) k) := rfl
    rw [h3, h1]
    exact zmod_rpow_mk (p ^ n) (-((p : Nat) : Int)) k
  show zmodMul (p ^ n) ((rpow (zpRing p) (zpNegPi p) k).val n) (y.val n)
    = Quot.mk (modCong (p ^ n)).rel 0
  rw [hcomp, ← hc]
  show Quot.mk (modCong (p ^ n)).rel (intPow (-((p : Nat) : Int)) k * c)
    = Quot.mk (modCong (p ^ n)).rel 0
  apply Quot.sound
  show ((p ^ n : Nat) : Int) ∣ intPow (-((p : Nat) : Int)) k * c - 0
  obtain ⟨d, hd⟩ := pow_dvd_mono p hnk
  refine ⟨((d : Nat) : Int) * (w * c), ?_⟩
  apply int_sub_zero_of_eq
  have hcast : ((p ^ k : Nat) : Int)
      = ((p ^ n : Nat) : Int) * ((d : Nat) : Int) := by
    rw [← Int.natCast_mul, hd]
  rw [hw, hcast, Int.mul_assoc ((p ^ n : Nat) : Int) ((d : Nat) : Int) w,
    Int.mul_assoc ((p ^ n : Nat) : Int) (((d : Nat) : Int) * w) c,
    Int.mul_assoc ((d : Nat) : Int) w c]

/-- **M93F-0d**: レベル n+1 では (−π)^n·(π·y) は消える
    （望遠鏡和の境界項の消滅）。 -/
theorem val_negPiPow_pi_mul (p : Nat) (n : Nat) (y : (Zp p).carrier) :
    ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n)
      ((zpRing p).mul (zpPi p) y)).val (n + 1)
      = Quot.mk (modCong (p ^ (n + 1))).rel 0 := by
  obtain ⟨c, hc⟩ := Quot.exists_rep (y.val (n + 1))
  obtain ⟨w, hw⟩ := negp_pow_decomp p n
  have hcomp : (rpow (zpRing p) (zpNegPi p) n).val (n + 1)
      = Quot.mk (modCong (p ^ (n + 1))).rel
          (intPow (-((p : Nat) : Int)) n) := by
    have h1 : (projRing p (n + 1)).map (rpow (zpRing p) (zpNegPi p) n)
        = rpow (zmodRing (p ^ (n + 1)))
            ((projRing p (n + 1)).map (zpNegPi p)) n :=
      ringHom_rpow (projRing p (n + 1)) (zpNegPi p) n
    have h2 : (projRing p (n + 1)).map (zpNegPi p)
        = Quot.mk (modCong (p ^ (n + 1))).rel (-((p : Nat) : Int)) := rfl
    rw [h2] at h1
    have h3 : (rpow (zpRing p) (zpNegPi p) n).val (n + 1)
        = (projRing p (n + 1)).map (rpow (zpRing p) (zpNegPi p) n) := rfl
    rw [h3, h1]
    exact zmod_rpow_mk (p ^ (n + 1)) (-((p : Nat) : Int)) n
  show zmodMul (p ^ (n + 1)) ((rpow (zpRing p) (zpNegPi p) n).val (n + 1))
      (zmodMul (p ^ (n + 1)) ((zpPi p).val (n + 1)) (y.val (n + 1)))
    = Quot.mk (modCong (p ^ (n + 1))).rel 0
  rw [hcomp, ← hc]
  show Quot.mk (modCong (p ^ (n + 1))).rel
      (intPow (-((p : Nat) : Int)) n * (((p : Nat) : Int) * c))
    = Quot.mk (modCong (p ^ (n + 1))).rel 0
  apply Quot.sound
  show ((p ^ (n + 1) : Nat) : Int)
    ∣ intPow (-((p : Nat) : Int)) n * (((p : Nat) : Int) * c) - 0
  refine ⟨w * c, ?_⟩
  apply int_sub_zero_of_eq
  have h4 : w * (((p : Nat) : Int) * c) = ((p : Nat) : Int) * (w * c) := by
    rw [← Int.mul_assoc w ((p : Nat) : Int) c,
      Int.mul_comm w ((p : Nat) : Int), Int.mul_assoc ((p : Nat) : Int) w c]
  rw [hw, cast_pow_succ p n, Int.mul_assoc ((p ^ n : Nat) : Int) w
      (((p : Nat) : Int) * c), h4,
    ← Int.mul_assoc ((p ^ n : Nat) : Int) ((p : Nat) : Int) (w * c)]

/-! ## §1a M93F-1a: h·E の係数公式 -/

/-- **M93F-1a (低域)**: m < p−1 で (h·E)_m = h_m·π（E の台は
    {0, p−1}、低域では定数項 π だけが効く）。 -/
theorem psMul_eisPoly_low (p : Nat) (h : PS (zpRing p)) (m : Nat)
    (hm : m < p - 1) :
    psMul (zpRing p) h (eisPoly p) m = (zpRing p).mul (h m) (zpPi p) := by
  show rsum (zpRing p)
      (fun k => (zpRing p).mul (h k) (eisPoly p (m - k))) (m + 1)
    = (zpRing p).mul (h m) (zpPi p)
  have hs : rsum (zpRing p)
      (fun k => (zpRing p).mul (h k) (eisPoly p (m - k))) (m + 1)
      = (zpRing p).mul (h m) (eisPoly p (m - m)) := by
    refine rsum_single (zpRing p) _ m (m + 1) (by omega) (fun j hj hne => ?_)
    show (zpRing p).mul (h j) (eisPoly p (m - j)) = (zpRing p).zero
    have hE : eisPoly p (m - j) = (zpRing p).zero := by
      show (zpRing p).add (psMono (zpRing p) (p - 1) (m - j))
          (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m - j))
        = (zpRing p).zero
      rw [show psMono (zpRing p) (p - 1) (m - j) = (zpRing p).zero from
          if_neg (by omega),
        show psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m - j)
            = (zpRing p).zero from if_neg (by omega),
        (zpRing p).zero_add]
    rw [hE]
    exact CRing.mul_zero (zpRing p) (h j)
  rw [hs, show m - m = 0 from by omega,
    eisPoly_coeff_zero p (by omega)]
  rfl

/-- **M93F-1a (高域)**: p−1 ≤ m で (h·E)_m = h_{m−(p−1)} + h_m·π
    （単項式 X^{p−1} の寄与が加わる）。 -/
theorem psMul_eisPoly_high (p : Nat) (_hp : 2 ≤ p) (h : PS (zpRing p))
    (m : Nat) (hm : p - 1 ≤ m) :
    psMul (zpRing p) h (eisPoly p) m
      = (zpRing p).add (h (m - (p - 1)))
          ((zpRing p).mul (h m) (zpPi p)) := by
  have hsplit : psMul (zpRing p) h (eisPoly p)
      = psAdd (zpRing p)
          (psMul (zpRing p) h (psMono (zpRing p) (p - 1)))
          (psMul (zpRing p) h
            (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)))) :=
    (psRing (zpRing p)).left_distrib h (psMono (zpRing p) (p - 1))
      (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)))
  rw [hsplit]
  show (zpRing p).add (psMul (zpRing p) h (psMono (zpRing p) (p - 1)) m)
      (psMul (zpRing p) h
        (psC (zpRing p) ((toZp p).map ((p : Nat) : Int))) m)
    = (zpRing p).add (h (m - (p - 1)))
        ((zpRing p).mul (h m) (zpPi p))
  have hmono : psMul (zpRing p) h (psMono (zpRing p) (p - 1)) m
      = h (m - (p - 1)) := by
    show rsum (zpRing p)
        (fun k => (zpRing p).mul (h k) (psMono (zpRing p) (p - 1) (m - k)))
        (m + 1)
      = h (m - (p - 1))
    have hs : rsum (zpRing p)
        (fun k => (zpRing p).mul (h k) (psMono (zpRing p) (p - 1) (m - k)))
        (m + 1)
        = (zpRing p).mul (h (m - (p - 1)))
            (psMono (zpRing p) (p - 1) (m - (m - (p - 1)))) := by
      refine rsum_single (zpRing p) _ (m - (p - 1)) (m + 1) (by omega)
        (fun j hj hne => ?_)
      show (zpRing p).mul (h j) (psMono (zpRing p) (p - 1) (m - j))
        = (zpRing p).zero
      rw [show psMono (zpRing p) (p - 1) (m - j) = (zpRing p).zero from
          if_neg (by omega)]
      exact CRing.mul_zero (zpRing p) (h j)
    rw [hs, show m - (m - (p - 1)) = p - 1 from by omega,
      show psMono (zpRing p) (p - 1) (p - 1) = (zpRing p).one from
        if_pos rfl]
    exact CRing.mul_one (zpRing p) (h (m - (p - 1)))
  have hconst : psMul (zpRing p) h
      (psC (zpRing p) ((toZp p).map ((p : Nat) : Int))) m
      = (zpRing p).mul (h m) (zpPi p) := by
    show rsum (zpRing p)
        (fun k => (zpRing p).mul (h k)
          (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m - k)))
        (m + 1)
      = (zpRing p).mul (h m) (zpPi p)
    have hs : rsum (zpRing p)
        (fun k => (zpRing p).mul (h k)
          (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m - k)))
        (m + 1)
        = (zpRing p).mul (h m)
            (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m - m)) := by
      refine rsum_single (zpRing p) _ m (m + 1) (by omega) (fun j hj hne => ?_)
      show (zpRing p).mul (h j)
          (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m - j))
        = (zpRing p).zero
      rw [show psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m - j)
          = (zpRing p).zero from if_neg (by omega)]
      exact CRing.mul_zero (zpRing p) (h j)
    rw [hs, show m - m = 0 from by omega]
    rfl
  rw [hmono, hconst]

/-! ## §1b M93F-1b: 被約係数（代表元上）と望遠鏡和 -/

/-- **M93F-1b: 被約係数** — λ^{p−1} = −π による簡約
    cᵢ(f) = Σ_{j<n} (−π)^j·f_{i+j(p−1)}（レベル n 打ち切り）。 -/
def eisCoeffZp (p : Nat) (f : PS (zpRing p)) (i n : Nat) : (Zp p).carrier :=
  rsum (zpRing p)
    (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
      (f (i + j * (p - 1)))) n

/-- 被約係数の加法性（rsum_add + 左分配）。 -/
theorem eisCoeffZp_add (p : Nat) (f g : PS (zpRing p)) (i n : Nat) :
    eisCoeffZp p (psAdd (zpRing p) f g) i n
      = (zpRing p).add (eisCoeffZp p f i n) (eisCoeffZp p g i n) := by
  show rsum (zpRing p)
      (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
        ((zpRing p).add (f (i + j * (p - 1))) (g (i + j * (p - 1))))) n
    = (zpRing p).add (eisCoeffZp p f i n) (eisCoeffZp p g i n)
  have h1 : rsum (zpRing p)
      (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
        ((zpRing p).add (f (i + j * (p - 1))) (g (i + j * (p - 1))))) n
      = rsum (zpRing p)
        (fun j => (zpRing p).add
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) j) (f (i + j * (p - 1))))
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) j) (g (i + j * (p - 1)))))
        n :=
    rsum_congr (zpRing p) n (fun j _ => (zpRing p).left_distrib _ _ _)
  rw [h1]
  exact rsum_add (zpRing p) _ _ n

/-- **M93F-1b (望遠鏡和)**: cᵢ(h·E) のレベル m+1 打ち切りは境界項
    (−π)^m·π·h_{i+m(p−1)} に完全に潰れる（隣接項のキャンセル
    π + (−π) = 0 を m の帰納で実行）。 -/
theorem eisCoeffZp_mulE_succ (p : Nat) (h : PS (zpRing p)) (i : Nat)
    (hi : i < p - 1) : ∀ m : Nat,
    eisCoeffZp p (psMul (zpRing p) h (eisPoly p)) i (m + 1)
      = (zpRing p).mul (rpow (zpRing p) (zpNegPi p) m)
          ((zpRing p).mul (zpPi p) (h (i + m * (p - 1)))) := by
  intro m
  induction m with
  | zero =>
    show (zpRing p).add (zpRing p).zero
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) 0)
          (psMul (zpRing p) h (eisPoly p) (i + 0 * (p - 1))))
      = (zpRing p).mul (rpow (zpRing p) (zpNegPi p) 0)
          ((zpRing p).mul (zpPi p) (h (i + 0 * (p - 1))))
    have hidx : i + 0 * (p - 1) = i := by omega
    rw [(zpRing p).zero_add, hidx, psMul_eisPoly_low p h i hi,
      (zpRing p).mul_comm (h i) (zpPi p)]
  | succ m ih =>
    show (zpRing p).add
        (eisCoeffZp p (psMul (zpRing p) h (eisPoly p)) i (m + 1))
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) (m + 1))
          (psMul (zpRing p) h (eisPoly p) (i + (m + 1) * (p - 1))))
      = (zpRing p).mul (rpow (zpRing p) (zpNegPi p) (m + 1))
          ((zpRing p).mul (zpPi p) (h (i + (m + 1) * (p - 1))))
    have hsm : (m + 1) * (p - 1) = m * (p - 1) + (p - 1) :=
      Nat.succ_mul m (p - 1)
    have hidx : i + (m + 1) * (p - 1) = i + m * (p - 1) + (p - 1) := by
      omega
    rw [ih, hidx, psMul_eisPoly_high p (by omega) h
        (i + m * (p - 1) + (p - 1)) (by omega),
      show i + m * (p - 1) + (p - 1) - (p - 1) = i + m * (p - 1) from
        by omega]
    -- 記号: ν^m := rpow ν m、A := h (i+m(p−1))、B := h (i+m(p−1)+(p−1))
    -- 目標: ν^m·(π·A) + ν^{m+1}·(A + B·π) = ν^{m+1}·(π·B)
    rw [(zpRing p).left_distrib (rpow (zpRing p) (zpNegPi p) (m + 1))
        (h (i + m * (p - 1)))
        ((zpRing p).mul (h (i + m * (p - 1) + (p - 1))) (zpPi p))]
    -- ν^{m+1} = ν^m·ν（定義一致）で第一項とキャンセル
    have hstep : (zpRing p).mul (rpow (zpRing p) (zpNegPi p) (m + 1))
        (h (i + m * (p - 1)))
        = (zpRing p).mul (rpow (zpRing p) (zpNegPi p) m)
          ((zpRing p).mul (zpNegPi p) (h (i + m * (p - 1)))) := by
      show (zpRing p).mul
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) m) (zpNegPi p))
          (h (i + m * (p - 1)))
        = (zpRing p).mul (rpow (zpRing p) (zpNegPi p) m)
          ((zpRing p).mul (zpNegPi p) (h (i + m * (p - 1))))
      exact (zpRing p).mul_assoc _ _ _
    rw [hstep, ← (zpRing p).add_assoc, ← (zpRing p).left_distrib
        (rpow (zpRing p) (zpNegPi p) m)
        ((zpRing p).mul (zpPi p) (h (i + m * (p - 1))))
        ((zpRing p).mul (zpNegPi p) (h (i + m * (p - 1))))]
    have hcancel : (zpRing p).add
        ((zpRing p).mul (zpPi p) (h (i + m * (p - 1))))
        ((zpRing p).mul (zpNegPi p) (h (i + m * (p - 1))))
        = (zpRing p).zero := by
      rw [show (zpRing p).mul (zpNegPi p) (h (i + m * (p - 1)))
          = (zpRing p).neg ((zpRing p).mul (zpPi p) (h (i + m * (p - 1))))
          from CRing.neg_mul (zpRing p) (zpPi p) (h (i + m * (p - 1)))]
      exact CRing.add_neg (zpRing p) _
    rw [hcancel, CRing.mul_zero (zpRing p) (rpow (zpRing p) (zpNegPi p) m),
      (zpRing p).zero_add,
      (zpRing p).mul_comm (h (i + m * (p - 1) + (p - 1))) (zpPi p)]

/-- **M93F-1b (消滅)**: cᵢ(h·E) のレベル n 射影は 0（n = 0 は自明、
    n = m+1 は望遠鏡和 + M93F-0d）。 -/
theorem eisCoeff_mulE (p : Nat) (h : PS (zpRing p)) (i n : Nat)
    (hi : i < p - 1) :
    (eisCoeffZp p (psMul (zpRing p) h (eisPoly p)) i n).val n
      = Quot.mk (modCong (p ^ n)).rel 0 := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [eisCoeffZp_mulE_succ p h i hi m]
    exact val_negPiPow_pi_mul p m (h (i + m * (p - 1)))

/-! ## §1c M93F-1c: 被約係数は O 上 well-defined -/

/-- eisRel の分解形: f ≡ g なら f = g + w·E（明示証人）。 -/
theorem eisRel_decomp (p : Nat) {f g : PS (zpRing p)}
    (hfg : eisRel p f g) :
    ∃ w : PS (zpRing p),
      f = psAdd (zpRing p) g (psMul (zpRing p) w (eisPoly p)) := by
  obtain ⟨w, hw⟩ := hfg
  refine ⟨w, ?_⟩
  rw [← hw]
  show f = (psRing (zpRing p)).add g
      ((psRing (zpRing p)).add f ((psRing (zpRing p)).neg g))
  rw [(psRing (zpRing p)).add_comm g
      ((psRing (zpRing p)).add f ((psRing (zpRing p)).neg g)),
    (psRing (zpRing p)).add_assoc f ((psRing (zpRing p)).neg g) g,
    (psRing (zpRing p)).neg_add g,
    CRing.add_zero (psRing (zpRing p)) f]

/-- **M93F-1c (well-definedness)**: f ≡ g mod (E) なら被約係数の
    レベル n 射影は一致（加法性 + 望遠鏡消滅）。 -/
theorem eisCoeff_sound (p : Nat) (i n : Nat) (hi : i < p - 1)
    (f g : PS (zpRing p)) (hfg : eisRel p f g) :
    (eisCoeffZp p f i n).val n = (eisCoeffZp p g i n).val n := by
  obtain ⟨w, hw⟩ := eisRel_decomp p hfg
  rw [hw, eisCoeffZp_add p g (psMul (zpRing p) w (eisPoly p)) i n]
  show (zmodRing (p ^ n)).add ((eisCoeffZp p g i n).val n)
      ((eisCoeffZp p (psMul (zpRing p) w (eisPoly p)) i n).val n)
    = (eisCoeffZp p g i n).val n
  rw [eisCoeff_mulE p w i n hi]
  exact CRing.add_zero (zmodRing (p ^ n)) ((eisCoeffZp p g i n).val n)

/-- **M93F-1c: O の被約係数写像**（i < p−1、レベル n）— 商上の
    Quot.lift。本モジュールの本丸その一。 -/
def eisCoeff (p : Nat) (i n : Nat) (hi : i < p - 1)
    (x : EisCarrier p) : (zmod (p ^ n)).carrier :=
  Quot.lift (fun f => (eisCoeffZp p f i n).val n)
    (fun f g hfg => eisCoeff_sound p i n hi f g hfg) x

/-- **M93F-1c: witness 付き非零性** — 被約係数 cᵢ のレベル n 射影が
    0 でない（M91F の NeZeroAt の Eisenstein 版）。 -/
def EisNeZeroAt (p : Nat) (x : EisCarrier p) (i n : Nat)
    (hi : i < p - 1) : Prop :=
  eisCoeff p i n hi x ≠ Quot.mk (modCong (p ^ n)).rel 0

/-- 0 ∈ O の被約係数は全て 0。 -/
theorem eisCoeff_zero (p : Nat) (i n : Nat) (hi : i < p - 1) :
    eisCoeff p i n hi ((eisRing p).zero)
      = Quot.mk (modCong (p ^ n)).rel 0 := by
  show (eisCoeffZp p (psZero (zpRing p)) i n).val n
    = Quot.mk (modCong (p ^ n)).rel 0
  have h1 : eisCoeffZp p (psZero (zpRing p)) i n = (zpRing p).zero := by
    show rsum (zpRing p)
        (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
          ((zpRing p).zero)) n
      = (zpRing p).zero
    have h2 : rsum (zpRing p)
        (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
          ((zpRing p).zero)) n
        = rsum (zpRing p) (fun _ => (zpRing p).zero) n :=
      rsum_congr (zpRing p) n
        (fun j _ => CRing.mul_zero (zpRing p) (rpow (zpRing p) (zpNegPi p) j))
    rw [h2]
    exact rsum_const_zero (zpRing p) n
  rw [h1]
  rfl

/-- **M93F-1c**: witness があれば x ≠ 0 in O。 -/
theorem eisNeZeroAt_ne_zero (p : Nat) (x : EisCarrier p) {i n : Nat}
    (hi : i < p - 1) (hx : EisNeZeroAt p x i n hi) :
    x ≠ (eisRing p).zero := by
  intro h0
  apply hx
  rw [h0]
  exact eisCoeff_zero p i n hi

/-! ## §1d M93F-1d: 構造射 ℤ_p → O との両立 -/

/-- 定数級数の 0 番被約係数（代表元上）: c₀(psC a) = a
    （j = 0 項のみ、j ≥ 1 では psC が消える）。 -/
theorem eisCoeffZp_psC (p : Nat) (h0 : 0 < p - 1) (a : (Zp p).carrier) :
    ∀ n : Nat, eisCoeffZp p (psC (zpRing p) a) 0 (n + 1) = a := by
  intro n
  induction n with
  | zero =>
    show (zpRing p).add (zpRing p).zero
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) 0)
          (psC (zpRing p) a (0 + 0 * (p - 1))))
      = a
    have hidx : 0 + 0 * (p - 1) = 0 := by omega
    rw [(zpRing p).zero_add, hidx,
      show psC (zpRing p) a 0 = a from if_pos rfl]
    exact (zpRing p).one_mul a
  | succ n ih =>
    show (zpRing p).add (eisCoeffZp p (psC (zpRing p) a) 0 (n + 1))
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) (n + 1))
          (psC (zpRing p) a (0 + (n + 1) * (p - 1))))
      = a
    have hsm : (n + 1) * (p - 1) = n * (p - 1) + (p - 1) :=
      Nat.succ_mul n (p - 1)
    rw [ih, show psC (zpRing p) a (0 + (n + 1) * (p - 1)) = (zpRing p).zero
        from if_neg (by omega),
      CRing.mul_zero (zpRing p) (rpow (zpRing p) (zpNegPi p) (n + 1))]
    exact CRing.add_zero (zpRing p) a

/-- **M93F-1d**: c₀(eisOf a) のレベル n 射影は a のレベル n 成分
    （n = 0 は ℤ/1 の自明性、n ≥ 1 は eisCoeffZp_psC）。 -/
theorem eisCoeff_eisOf (p : Nat) (h0 : 0 < p - 1) (a : (Zp p).carrier)
    (n : Nat) :
    eisCoeff p 0 n h0 ((eisOf p).map a) = a.val n := by
  cases n with
  | zero =>
    show (eisCoeffZp p (psC (zpRing p) a) 0 0).val 0 = a.val 0
    obtain ⟨c, hc⟩ := Quot.exists_rep (a.val 0)
    rw [← hc]
    show Quot.mk (modCong (p ^ 0)).rel 0 = Quot.mk (modCong (p ^ 0)).rel c
    apply Quot.sound
    show ((p ^ 0 : Nat) : Int) ∣ 0 - c
    exact ⟨0 - c, (Int.one_mul (0 - c)).symm⟩
  | succ n =>
    show (eisCoeffZp p (psC (zpRing p) a) 0 (n + 1)).val (n + 1)
      = a.val (n + 1)
    rw [eisCoeffZp_psC p h0 a n]

/-- **系 (M93F-1d): eisOf は単射** — O は ℤ_p を忠実に含む
    （全レベルの係数比較 + Subtype.ext）。 -/
theorem eisOf_injective (p : Nat) (hp : 2 ≤ p) {a b : (Zp p).carrier}
    (h : (eisOf p).map a = (eisOf p).map b) : a = b := by
  have h0 : 0 < p - 1 := by omega
  apply Subtype.ext
  funext n
  have hn := congrArg (eisCoeff p 0 n h0) h
  rw [eisCoeff_eisOf p h0 a n, eisCoeff_eisOf p h0 b n] at hn
  exact hn

/-- **系 (M93F-1d): witness の移送** — NeZeroAt p a n なら
    eisOf a は係数 0・レベル n の witness を持つ。 -/
theorem eisOf_neZeroAt (p : Nat) (a : (Zp p).carrier) {n : Nat}
    (h0 : 0 < p - 1) (ha : NeZeroAt p a n) :
    EisNeZeroAt p ((eisOf p).map a) 0 n h0 := by
  show eisCoeff p 0 n h0 ((eisOf p).map a)
    ≠ Quot.mk (modCong (p ^ n)).rel 0
  rw [eisCoeff_eisOf p h0 a n]
  exact ha

/-! ## §2 M93F-2: λ 倍の係数簿記と witness シフト -/

/-- X·f の係数（正指数）: (X·f)_{m+1} = f_m。 -/
theorem psMul_X_coeff (p : Nat) (f : PS (zpRing p)) (m : Nat) :
    psMul (zpRing p) (psX (zpRing p)) f (m + 1) = f m := by
  show rsum (zpRing p)
      (fun k => (zpRing p).mul (psX (zpRing p) k) (f (m + 1 - k))) (m + 2)
    = f m
  have hs : rsum (zpRing p)
      (fun k => (zpRing p).mul (psX (zpRing p) k) (f (m + 1 - k))) (m + 2)
      = (zpRing p).mul (psX (zpRing p) 1) (f (m + 1 - 1)) := by
    refine rsum_single (zpRing p) _ 1 (m + 2) (by omega)
      (fun j hj hne => ?_)
    show (zpRing p).mul (psX (zpRing p) j) (f (m + 1 - j)) = (zpRing p).zero
    rw [show psX (zpRing p) j = (zpRing p).zero from if_neg hne]
    exact CRing.zero_mul (zpRing p) (f (m + 1 - j))
  rw [hs, show psX (zpRing p) 1 = (zpRing p).one from if_pos rfl,
    (zpRing p).one_mul, show m + 1 - 1 = m from by omega]

/-- X·f の係数（定数項）: (X·f)_0 = 0。 -/
theorem psMul_X_coeff_zero (p : Nat) (f : PS (zpRing p)) :
    psMul (zpRing p) (psX (zpRing p)) f 0 = (zpRing p).zero := by
  show (zpRing p).add (zpRing p).zero
      ((zpRing p).mul (psX (zpRing p) 0) (f (0 - 0)))
    = (zpRing p).zero
  rw [(zpRing p).zero_add,
    show psX (zpRing p) 0 = (zpRing p).zero from if_neg (by omega)]
  exact CRing.zero_mul (zpRing p) (f (0 - 0))

/-- **M93F-2a (域内シフト)**: cᵢ₊₁(λ·x) = cᵢ(x)（i+1 < p−1 のとき。
    被約添字がずれるだけで簡約は起きない）。 -/
theorem eisCoeff_lambda_mul (p : Nat) (x : EisCarrier p) (i n : Nat)
    (hi1 : i + 1 < p - 1) :
    eisCoeff p (i + 1) n hi1 ((eisRing p).mul (eisLambda p) x)
      = eisCoeff p i n (by omega) x := by
  induction x using Quot.ind
  rename_i f
  show (eisCoeffZp p (psMul (zpRing p) (psX (zpRing p)) f) (i + 1) n).val n
    = (eisCoeffZp p f i n).val n
  have h1 : eisCoeffZp p (psMul (zpRing p) (psX (zpRing p)) f) (i + 1) n
      = eisCoeffZp p f i n := by
    show rsum (zpRing p)
        (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
          (psMul (zpRing p) (psX (zpRing p)) f (i + 1 + j * (p - 1)))) n
      = rsum (zpRing p)
        (fun j => (zpRing p).mul (rpow (zpRing p) (zpNegPi p) j)
          (f (i + j * (p - 1)))) n
    refine rsum_congr (zpRing p) n (fun j _ => ?_)
    have hidx : i + 1 + j * (p - 1) = (i + j * (p - 1)) + 1 := by omega
    rw [hidx, psMul_X_coeff p f (i + j * (p - 1))]
  rw [h1]

/-- **M93F-2a (witness 版)**: x が (i, n)-witness を持てば λ·x は
    (i+1, n)-witness を持つ。 -/
theorem eisNeZeroAt_lambda_mul (p : Nat) (x : EisCarrier p) {i n : Nat}
    (hi1 : i + 1 < p - 1) (hx : EisNeZeroAt p x i n (by omega)) :
    EisNeZeroAt p ((eisRing p).mul (eisLambda p) x) (i + 1) n hi1 := by
  show eisCoeff p (i + 1) n hi1 ((eisRing p).mul (eisLambda p) x)
    ≠ Quot.mk (modCong (p ^ n)).rel 0
  rw [eisCoeff_lambda_mul p x i n hi1]
  exact hx

/-- **M93F-2b (巻き戻り)**: c₀(λ·x) = −π·c_{p−2}(x)（代表元上・
    レベル n+1 打ち切り。最高被約添字 p−2 が λ 倍で 0 番へ巻き戻り、
    簡約 λ^{p−1} = −π の乗数を拾う）。 -/
theorem eisCoeffZp_X_wrap (p : Nat) (hp : 2 ≤ p) (f : PS (zpRing p)) :
    ∀ n : Nat,
    eisCoeffZp p (psMul (zpRing p) (psX (zpRing p)) f) 0 (n + 1)
      = (zpRing p).mul (zpNegPi p) (eisCoeffZp p f (p - 2) n) := by
  intro n
  induction n with
  | zero =>
    show (zpRing p).add (zpRing p).zero
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) 0)
          (psMul (zpRing p) (psX (zpRing p)) f (0 + 0 * (p - 1))))
      = (zpRing p).mul (zpNegPi p) (zpRing p).zero
    have hidx : 0 + 0 * (p - 1) = 0 := by omega
    rw [(zpRing p).zero_add, hidx, psMul_X_coeff_zero p f,
      CRing.mul_zero (zpRing p) (rpow (zpRing p) (zpNegPi p) 0),
      CRing.mul_zero (zpRing p) (zpNegPi p)]
  | succ n ih =>
    show (zpRing p).add
        (eisCoeffZp p (psMul (zpRing p) (psX (zpRing p)) f) 0 (n + 1))
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) (n + 1))
          (psMul (zpRing p) (psX (zpRing p)) f (0 + (n + 1) * (p - 1))))
      = (zpRing p).mul (zpNegPi p)
          ((zpRing p).add (eisCoeffZp p f (p - 2) n)
            ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n)
              (f (p - 2 + n * (p - 1)))))
    have hsm : (n + 1) * (p - 1) = n * (p - 1) + (p - 1) :=
      Nat.succ_mul n (p - 1)
    have hidx : 0 + (n + 1) * (p - 1) = (p - 2 + n * (p - 1)) + 1 := by
      omega
    rw [ih, hidx, psMul_X_coeff p f (p - 2 + n * (p - 1)),
      (zpRing p).left_distrib (zpNegPi p) (eisCoeffZp p f (p - 2) n)
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n)
          (f (p - 2 + n * (p - 1))))]
    -- 残るは ν^{n+1}·A = ν·(ν^n·A) の付け替え
    have hpow : (zpRing p).mul (rpow (zpRing p) (zpNegPi p) (n + 1))
        (f (p - 2 + n * (p - 1)))
        = (zpRing p).mul (zpNegPi p)
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n)
            (f (p - 2 + n * (p - 1)))) := by
      show (zpRing p).mul
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n) (zpNegPi p))
          (f (p - 2 + n * (p - 1)))
        = (zpRing p).mul (zpNegPi p)
          ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) n)
            (f (p - 2 + n * (p - 1))))
      rw [(zpRing p).mul_comm (rpow (zpRing p) (zpNegPi p) n) (zpNegPi p),
        (zpRing p).mul_assoc (zpNegPi p) (rpow (zpRing p) (zpNegPi p) n)
          (f (p - 2 + n * (p - 1)))]
    rw [hpow]

/-- **M93F-2b (witness 版・巻き戻り)**: x が (p−2, n)-witness を
    持てば λ·x は (0, n+1)-witness を持つ（−π 倍はレベルをちょうど
    1 つ持ち上げる: M91F の p キャンセル簿記 p_mul_val_zero）。 -/
theorem eisNeZeroAt_lambda_wrap (p : Nat) (hp : 2 ≤ p)
    (x : EisCarrier p) {n : Nat} (hpw : p - 2 < p - 1) (h0 : 0 < p - 1)
    (hx : EisNeZeroAt p x (p - 2) n hpw) :
    EisNeZeroAt p ((eisRing p).mul (eisLambda p) x) 0 (n + 1) h0 := by
  induction x using Quot.ind
  rename_i f
  intro h0val
  apply hx
  show (eisCoeffZp p f (p - 2) n).val n = Quot.mk (modCong (p ^ n)).rel 0
  -- h0val を −π·S（S = c_{p−2}(f) のレベル n 打ち切り）の消滅に読み替え
  have h1 : ((zpRing p).mul (zpNegPi p)
      (eisCoeffZp p f (p - 2) n)).val (n + 1)
      = Quot.mk (modCong (p ^ (n + 1))).rel 0 := by
    rw [← eisCoeffZp_X_wrap p hp f n]
    exact h0val
  have h2 : ((zpRing p).neg ((zpRing p).mul (zpPi p)
      (eisCoeffZp p f (p - 2) n))).val (n + 1)
      = Quot.mk (modCong (p ^ (n + 1))).rel 0 := by
    rw [← CRing.neg_mul (zpRing p) (zpPi p) (eisCoeffZp p f (p - 2) n)]
    exact h1
  -- 負号を外す: −W ≡ 0 なら W ≡ 0
  obtain ⟨c, hc⟩ := Quot.exists_rep
    (((zpRing p).mul (zpPi p) (eisCoeffZp p f (p - 2) n)).val (n + 1))
  have h3 : (zmod (p ^ (n + 1))).inv
      (((zpRing p).mul (zpPi p) (eisCoeffZp p f (p - 2) n)).val (n + 1))
      = Quot.mk (modCong (p ^ (n + 1))).rel 0 := h2
  rw [← hc] at h3
  have h4 : Quot.mk (modCong (p ^ (n + 1))).rel (-c)
      = Quot.mk (modCong (p ^ (n + 1))).rel 0 := h3
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (p ^ (n + 1))) h4
  have hW : ((zpRing p).mul (zpPi p)
      (eisCoeffZp p f (p - 2) n)).val (n + 1)
      = Quot.mk (modCong (p ^ (n + 1))).rel 0 := by
    rw [← hc]
    apply Quot.sound
    show ((p ^ (n + 1) : Nat) : Int) ∣ c - 0
    refine ⟨-k, ?_⟩
    rw [Int.mul_neg]
    omega
  exact p_mul_val_zero p hp (eisCoeffZp p f (p - 2) n) n hW

/-- **系 (M93F-2c): witness を持つ x について λ·x ≠ 0**（域内なら
    添字シフト、最高添字なら巻き戻り — どちらの場合も witness が
    明示的に構成される）。 -/
theorem eis_lambda_mul_ne_zero (p : Nat) (hp : 2 ≤ p)
    (x : EisCarrier p) {i n : Nat} (hi : i < p - 1)
    (hx : EisNeZeroAt p x i n hi) :
    (eisRing p).mul (eisLambda p) x ≠ (eisRing p).zero := by
  cases Nat.decLt (i + 1) (p - 1) with
  | isTrue h =>
    exact eisNeZeroAt_ne_zero p ((eisRing p).mul (eisLambda p) x) h
      (eisNeZeroAt_lambda_mul p x h hx)
  | isFalse h =>
    have hieq : i = p - 2 := by omega
    subst hieq
    exact eisNeZeroAt_ne_zero p ((eisRing p).mul (eisLambda p) x)
      (show 0 < p - 1 by omega)
      (eisNeZeroAt_lambda_wrap p hp x hi (by omega) hx)

/-! ## §2' λ 自身の witness -/

/-- 1 は ℤ/N で 0 でない（2 ≤ N、not_dvd_one）。 -/
theorem zmod_one_ne_zero (N : Nat) (hN : 2 ≤ N) :
    Quot.mk (modCong N).rel 1 ≠ Quot.mk (modCong N).rel 0 := by
  intro h
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong N) h
  refine not_dvd_one N hN ⟨k, ?_⟩
  omega

/-- 2 ≤ p、1 ≤ n なら 2 ≤ p^n。 -/
theorem two_le_pow (p : Nat) (hp : 2 ≤ p) : ∀ n, 1 ≤ n → 2 ≤ p ^ n := by
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
    have h1 : 0 < p ^ m := pow_pos' p (by omega) m
    have h2 : 1 * p ≤ p ^ m * p := Nat.mul_le_mul h1 (Nat.le_refl p)
    rw [Nat.pow_succ]
    omega

/-- λ = X mod E の被約係数: c₁(λ) = 1（レベル n+1 打ち切り、p ≥ 3）。 -/
theorem eisCoeffZp_psX (p : Nat) (hodd : 3 ≤ p) : ∀ n : Nat,
    eisCoeffZp p (psX (zpRing p)) 1 (n + 1) = (zpRing p).one := by
  intro n
  induction n with
  | zero =>
    show (zpRing p).add (zpRing p).zero
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) 0)
          (psX (zpRing p) (1 + 0 * (p - 1))))
      = (zpRing p).one
    have hidx : 1 + 0 * (p - 1) = 1 := by omega
    rw [(zpRing p).zero_add, hidx,
      show psX (zpRing p) 1 = (zpRing p).one from if_pos rfl]
    exact (zpRing p).one_mul (zpRing p).one
  | succ n ih =>
    show (zpRing p).add (eisCoeffZp p (psX (zpRing p)) 1 (n + 1))
        ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) (n + 1))
          (psX (zpRing p) (1 + (n + 1) * (p - 1))))
      = (zpRing p).one
    have hsm : (n + 1) * (p - 1) = n * (p - 1) + (p - 1) :=
      Nat.succ_mul n (p - 1)
    rw [ih, show psX (zpRing p) (1 + (n + 1) * (p - 1)) = (zpRing p).zero
        from if_neg (by omega),
      CRing.mul_zero (zpRing p) (rpow (zpRing p) (zpNegPi p) (n + 1))]
    exact CRing.add_zero (zpRing p) (zpRing p).one

/-- **M93F-2d: λ は witness を持つ** — EisNeZeroAt λ 1 (n+1)
    （M83F-6 の λ ≠ 0 の witness 強化版、p ≥ 3）。 -/
theorem eisNeZeroAt_lambda (p : Nat) (hodd : 3 ≤ p) (n : Nat)
    (h1 : 1 < p - 1) : EisNeZeroAt p (eisLambda p) 1 (n + 1) h1 := by
  show (eisCoeffZp p (psX (zpRing p)) 1 (n + 1)).val (n + 1)
    ≠ Quot.mk (modCong (p ^ (n + 1))).rel 0
  rw [eisCoeffZp_psX p hodd n]
  show Quot.mk (modCong (p ^ (n + 1))).rel 1
    ≠ Quot.mk (modCong (p ^ (n + 1))).rel 0
  exact zmod_one_ne_zero (p ^ (n + 1))
    (two_le_pow p (by omega) (n + 1) (by omega))

/-! ## §3 M93F-3: witness 付き λ 割り算 -/

/-- 級数の頭出し分解: f = X·shift(f) + C(f₀)
    （psC_mul_coeff は M47 Freshman の既証明を再利用）。 -/
theorem psX_shift_decomp (p : Nat) (f : PS (zpRing p)) :
    f = psAdd (zpRing p)
      (psMul (zpRing p) (psX (zpRing p)) (psShift (zpRing p) f))
      (psC (zpRing p) (f 0)) := by
  funext m
  cases m with
  | zero =>
    show f 0 = (zpRing p).add
        (psMul (zpRing p) (psX (zpRing p)) (psShift (zpRing p) f) 0) (f 0)
    rw [psMul_X_coeff_zero p (psShift (zpRing p) f), (zpRing p).zero_add]
  | succ m =>
    show f (m + 1) = (zpRing p).add
        (psMul (zpRing p) (psX (zpRing p)) (psShift (zpRing p) f) (m + 1))
        ((zpRing p).zero)
    rw [psMul_X_coeff p (psShift (zpRing p) f) m,
      CRing.add_zero (zpRing p) (psShift (zpRing p) f m)]
    rfl

/-- **定理 (M93F-3): witness 付き λ 割り算** — 代表元 f の定数項が
    π で割れる（f₀ = π·e、witness e 明示）なら
    mk f = λ·mk x′、x′ = shift(f) − X^{p−2}·e は明示構成。
    (E)-合同の証人は psC e: f − X·x′ = C(e)·E（係数ごとの照合。
    定数項は f₀ = πe = e·π = e·E₀、正指数は X^{p−2} の巻き上げが
    E の単項式項 X^{p−1} を生む）。 -/
theorem eis_lambda_division (p : Nat) (hp : 2 ≤ p) (f : PS (zpRing p))
    (e : (Zp p).carrier)
    (he : f 0 = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    Quot.mk (eisRel p) f
      = (eisRing p).mul (eisLambda p)
          (Quot.mk (eisRel p)
            (psAdd (zpRing p) (psShift (zpRing p) f)
              (psNeg (zpRing p)
                (psMul (zpRing p) (psMono (zpRing p) (p - 2))
                  (psC (zpRing p) e))))) := by
  show Quot.mk (eisRel p) f
    = Quot.mk (eisRel p)
        (psMul (zpRing p) (psX (zpRing p))
          (psAdd (zpRing p) (psShift (zpRing p) f)
            (psNeg (zpRing p)
              (psMul (zpRing p) (psMono (zpRing p) (p - 2))
                (psC (zpRing p) e)))))
  apply Quot.sound
  refine ⟨psC (zpRing p) e, ?_⟩
  funext m
  cases m with
  | zero =>
    show (zpRing p).add (f 0)
        ((zpRing p).neg
          (psMul (zpRing p) (psX (zpRing p))
            (psAdd (zpRing p) (psShift (zpRing p) f)
              (psNeg (zpRing p)
                (psMul (zpRing p) (psMono (zpRing p) (p - 2))
                  (psC (zpRing p) e)))) 0))
      = psMul (zpRing p) (psC (zpRing p) e) (eisPoly p) 0
    rw [psMul_X_coeff_zero p
        (psAdd (zpRing p) (psShift (zpRing p) f)
          (psNeg (zpRing p)
            (psMul (zpRing p) (psMono (zpRing p) (p - 2))
              (psC (zpRing p) e)))),
      CRing.neg_zero (zpRing p), CRing.add_zero (zpRing p) (f 0),
      psC_mul_coeff (zpRing p) e (eisPoly p) 0, eisPoly_coeff_zero p hp,
      he]
    exact (zpRing p).mul_comm ((toZp p).map ((p : Nat) : Int)) e
  | succ m =>
    show (zpRing p).add (f (m + 1))
        ((zpRing p).neg
          (psMul (zpRing p) (psX (zpRing p))
            (psAdd (zpRing p) (psShift (zpRing p) f)
              (psNeg (zpRing p)
                (psMul (zpRing p) (psMono (zpRing p) (p - 2))
                  (psC (zpRing p) e)))) (m + 1)))
      = psMul (zpRing p) (psC (zpRing p) e) (eisPoly p) (m + 1)
    rw [psMul_X_coeff p
        (psAdd (zpRing p) (psShift (zpRing p) f)
          (psNeg (zpRing p)
            (psMul (zpRing p) (psMono (zpRing p) (p - 2))
              (psC (zpRing p) e)))) m]
    show (zpRing p).add (f (m + 1))
        ((zpRing p).neg ((zpRing p).add (f (m + 1))
          ((zpRing p).neg
            (psMul (zpRing p) (psMono (zpRing p) (p - 2))
              (psC (zpRing p) e) m))))
      = psMul (zpRing p) (psC (zpRing p) e) (eisPoly p) (m + 1)
    have hD : psMul (zpRing p) (psMono (zpRing p) (p - 2))
        (psC (zpRing p) e) m
        = (zpRing p).mul e (psMono (zpRing p) (p - 2) m) := by
      have hcomm : psMul (zpRing p) (psMono (zpRing p) (p - 2))
          (psC (zpRing p) e)
          = psMul (zpRing p) (psC (zpRing p) e)
            (psMono (zpRing p) (p - 2)) :=
        (psRing (zpRing p)).mul_comm (psMono (zpRing p) (p - 2))
          (psC (zpRing p) e)
      rw [congrFun hcomm m]
      exact psC_mul_coeff (zpRing p) e (psMono (zpRing p) (p - 2)) m
    rw [hD, psC_mul_coeff (zpRing p) e (eisPoly p) (m + 1),
      CRing.neg_add_dist (zpRing p) (f (m + 1))
        ((zpRing p).neg ((zpRing p).mul e (psMono (zpRing p) (p - 2) m))),
      CRing.neg_neg (zpRing p)
        ((zpRing p).mul e (psMono (zpRing p) (p - 2) m)),
      ← (zpRing p).add_assoc (f (m + 1)) ((zpRing p).neg (f (m + 1)))
        ((zpRing p).mul e (psMono (zpRing p) (p - 2) m)),
      CRing.add_neg (zpRing p) (f (m + 1)), (zpRing p).zero_add]
    have hE : psMono (zpRing p) (p - 2) m = eisPoly p (m + 1) := by
      cases Nat.decEq m (p - 2) with
      | isTrue hmeq =>
        subst hmeq
        rw [show psMono (zpRing p) (p - 2) (p - 2) = (zpRing p).one from
            if_pos rfl]
        show (zpRing p).one
          = (zpRing p).add (psMono (zpRing p) (p - 1) (p - 2 + 1))
              (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 2 + 1))
        rw [show psMono (zpRing p) (p - 1) (p - 2 + 1) = (zpRing p).one
            from if_pos (by omega),
          show psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (p - 2 + 1)
              = (zpRing p).zero from if_neg (by omega),
          CRing.add_zero (zpRing p) (zpRing p).one]
      | isFalse hmne =>
        rw [show psMono (zpRing p) (p - 2) m = (zpRing p).zero from
            if_neg hmne]
        show (zpRing p).zero
          = (zpRing p).add (psMono (zpRing p) (p - 1) (m + 1))
              (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 1))
        rw [show psMono (zpRing p) (p - 1) (m + 1) = (zpRing p).zero from
            if_neg (by omega),
          show psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 1)
              = (zpRing p).zero from if_neg (by omega),
          (zpRing p).zero_add]
    rw [hE]

/-- **系 (M93F-3): λ 割り算の ∃ 版**（商の元として: 明示構成なので
    choice-free）。 -/
theorem eis_lambda_division_exists (p : Nat) (hp : 2 ≤ p)
    (f : PS (zpRing p)) (e : (Zp p).carrier)
    (he : f 0 = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    ∃ x' : EisCarrier p,
      Quot.mk (eisRel p) f = (eisRing p).mul (eisLambda p) x' :=
  ⟨Quot.mk (eisRel p)
    (psAdd (zpRing p) (psShift (zpRing p) f)
      (psNeg (zpRing p)
        (psMul (zpRing p) (psMono (zpRing p) (p - 2)) (psC (zpRing p) e)))),
    eis_lambda_division p hp f e he⟩

/-! ## §4 M93F-4: 剰余体乗法性（部分的本丸） -/

/-- 積級数の定数項: (f·g)₀ = f₀·g₀。 -/
theorem psMul_coeff_zero (R : CRing) (f g : PS R) :
    psMul R f g 0 = R.mul (f 0) (g 0) := by
  show R.add R.zero (R.mul (f 0) (g 0)) = R.mul (f 0) (g 0)
  rw [R.zero_add]

/-- レベル 1 打ち切りの被約係数は定数項そのもの: c₀(f)|₁ = f₀。 -/
theorem eisCoeffZp_one (p : Nat) (f : PS (zpRing p)) :
    eisCoeffZp p f 0 1 = f 0 := by
  show (zpRing p).add (zpRing p).zero
      ((zpRing p).mul (rpow (zpRing p) (zpNegPi p) 0)
        (f (0 + 0 * (p - 1))))
    = f 0
  have hidx : 0 + 0 * (p - 1) = 0 := by omega
  rw [(zpRing p).zero_add, hidx]
  exact (zpRing p).one_mul (f 0)

/-- **M93F-4a: 剰余写像は乗法的** — c₀(x·y) のレベル 1 射影は
    c₀(x)·c₀(y) のレベル 1 射影の積（剰余体 O/λ = 𝔽_p への
    全射の乗法性）。 -/
theorem eisCoeff_mul_one (p : Nat) (h0 : 0 < p - 1) (x y : EisCarrier p) :
    eisCoeff p 0 1 h0 ((eisRing p).mul x y)
      = zmodMul (p ^ 1) (eisCoeff p 0 1 h0 x) (eisCoeff p 0 1 h0 y) := by
  induction x using Quot.ind
  rename_i f
  induction y using Quot.ind
  rename_i g
  show (eisCoeffZp p (psMul (zpRing p) f g) 0 1).val 1
    = zmodMul (p ^ 1) ((eisCoeffZp p f 0 1).val 1)
        ((eisCoeffZp p g 0 1).val 1)
  rw [eisCoeffZp_one p (psMul (zpRing p) f g), eisCoeffZp_one p f,
    eisCoeffZp_one p g, psMul_coeff_zero (zpRing p) f g]
  rfl

/-- **M93F-4b: ℤ/p の零因子なし**（M91F-3 の核を zmod レベルで抽出。
    Euclid の補題 Int 版 = M34-2、実体は M32 の Bézout）。 -/
theorem zmod_p_mul_nonzero (p : Nat) (hp : IsPrime p)
    (u v : (zmod (p ^ 1)).carrier)
    (hu : u ≠ Quot.mk (modCong (p ^ 1)).rel 0)
    (hv : v ≠ Quot.mk (modCong (p ^ 1)).rel 0) :
    zmodMul (p ^ 1) u v ≠ Quot.mk (modCong (p ^ 1)).rel 0 := by
  intro h0
  obtain ⟨a, ha⟩ := Quot.exists_rep u
  obtain ⟨b, hb⟩ := Quot.exists_rep v
  rw [← ha, ← hb] at h0
  have hab : Quot.mk (modCong (p ^ 1)).rel (a * b)
      = Quot.mk (modCong (p ^ 1)).rel 0 := h0
  obtain ⟨t, ht⟩ := quot_exact intGrp (modCong (p ^ 1)) hab
  rw [Nat.pow_one] at ht
  have hdvd : ((p : Nat) : Int) ∣ a * b := ⟨t, int_eq_of_sub_zero ht⟩
  have hpa : ¬ ((p : Nat) : Int) ∣ a := by
    intro hda
    apply hu
    rw [← ha]
    obtain ⟨s, hs⟩ := hda
    apply Quot.sound
    show ((p ^ 1 : Nat) : Int) ∣ a - 0
    rw [Nat.pow_one]
    exact ⟨s, int_sub_zero_of_eq hs⟩
  have hpb : ((p : Nat) : Int) ∣ b := euclid_int p hp hdvd hpa
  apply hv
  rw [← hb]
  obtain ⟨s, hs⟩ := hpb
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ b - 0
  rw [Nat.pow_one]
  exact ⟨s, int_sub_zero_of_eq hs⟩

/-- **定理 (M93F-4c): 単数剰余の乗法性** — x, y が単数剰余
    （c₀ レベル 1 witness）を持てば x·y も持つ。 -/
theorem eis_residue_mul (p : Nat) (hp : IsPrime p) (h0 : 0 < p - 1)
    (x y : EisCarrier p) (hx : EisNeZeroAt p x 0 1 h0)
    (hy : EisNeZeroAt p y 0 1 h0) :
    EisNeZeroAt p ((eisRing p).mul x y) 0 1 h0 := by
  show eisCoeff p 0 1 h0 ((eisRing p).mul x y)
    ≠ Quot.mk (modCong (p ^ 1)).rel 0
  rw [eisCoeff_mul_one p h0 x y]
  exact zmod_p_mul_nonzero p hp (eisCoeff p 0 1 h0 x)
    (eisCoeff p 0 1 h0 y) hx hy

/-- **系 (M93F-4d): 単数剰余元の積は 0 でない** — O の零因子なしの
    単数剰余部分（一般の積への拡張は λ 進付値分解を要し次層）。 -/
theorem eis_unit_mul_ne_zero (p : Nat) (hp : IsPrime p) (h0 : 0 < p - 1)
    (x y : EisCarrier p) (hx : EisNeZeroAt p x 0 1 h0)
    (hy : EisNeZeroAt p y 0 1 h0) :
    (eisRing p).mul x y ≠ (eisRing p).zero :=
  eisNeZeroAt_ne_zero p ((eisRing p).mul x y) h0
    (eis_residue_mul p hp h0 x y hx hy)

/-! ## §5 M93F-5 まとめの束 -/

/-- **M93F-5a: O の整域性データ（第一段）** — well-defined な被約
    係数簿記から得られた完成部分の束: 零の係数・witness の非零含意・
    eisOf の単射性と witness 移送・λ シフト（域内/巻き戻り/非零）・
    λ 割り算（witness 付き）・剰余乗法性・単数剰余積の非零。 -/
structure EisDomainData (p : Nat) (hp : IsPrime p) where
  coeff_zero : ∀ (i n : Nat) (hi : i < p - 1),
    eisCoeff p i n hi ((eisRing p).zero)
      = Quot.mk (modCong (p ^ n)).rel 0
  ne_zero : ∀ (x : EisCarrier p) (i n : Nat) (hi : i < p - 1),
    EisNeZeroAt p x i n hi → x ≠ (eisRing p).zero
  of_injective : ∀ {a b : (Zp p).carrier},
    (eisOf p).map a = (eisOf p).map b → a = b
  of_witness : ∀ (a : (Zp p).carrier) (n : Nat) (h0 : 0 < p - 1),
    NeZeroAt p a n → EisNeZeroAt p ((eisOf p).map a) 0 n h0
  lambda_shift : ∀ (x : EisCarrier p) (i n : Nat) (hi1 : i + 1 < p - 1)
    (hi : i < p - 1), EisNeZeroAt p x i n hi →
    EisNeZeroAt p ((eisRing p).mul (eisLambda p) x) (i + 1) n hi1
  lambda_wrap : ∀ (x : EisCarrier p) (n : Nat) (hpw : p - 2 < p - 1)
    (h0 : 0 < p - 1), EisNeZeroAt p x (p - 2) n hpw →
    EisNeZeroAt p ((eisRing p).mul (eisLambda p) x) 0 (n + 1) h0
  lambda_mul_ne_zero : ∀ (x : EisCarrier p) (i n : Nat) (hi : i < p - 1),
    EisNeZeroAt p x i n hi →
    (eisRing p).mul (eisLambda p) x ≠ (eisRing p).zero
  lambda_div : ∀ (f : PS (zpRing p)) (e : (Zp p).carrier),
    f 0 = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e →
    ∃ x' : EisCarrier p,
      Quot.mk (eisRel p) f = (eisRing p).mul (eisLambda p) x'
  residue_mul : ∀ (x y : EisCarrier p) (h0 : 0 < p - 1),
    EisNeZeroAt p x 0 1 h0 → EisNeZeroAt p y 0 1 h0 →
    EisNeZeroAt p ((eisRing p).mul x y) 0 1 h0
  unit_mul_ne_zero : ∀ (x y : EisCarrier p) (h0 : 0 < p - 1),
    EisNeZeroAt p x 0 1 h0 → EisNeZeroAt p y 0 1 h0 →
    (eisRing p).mul x y ≠ (eisRing p).zero

/-- **M93F-5b: witness**（全フィールドが本モジュールの完全証明）。 -/
def eisDomainData (p : Nat) (hp : IsPrime p) : EisDomainData p hp where
  coeff_zero := fun i n hi => eisCoeff_zero p i n hi
  ne_zero := fun x _i _n hi hx => eisNeZeroAt_ne_zero p x hi hx
  of_injective := fun {_ _} h => eisOf_injective p hp.1 h
  of_witness := fun a _n h0 ha => eisOf_neZeroAt p a h0 ha
  lambda_shift := fun x _i _n hi1 _ hx => eisNeZeroAt_lambda_mul p x hi1 hx
  lambda_wrap := fun x _n hpw h0 hx =>
    eisNeZeroAt_lambda_wrap p hp.1 x hpw h0 hx
  lambda_mul_ne_zero := fun x _i _n hi hx =>
    eis_lambda_mul_ne_zero p hp.1 x hi hx
  lambda_div := fun f e he => eis_lambda_division_exists p hp.1 f e he
  residue_mul := fun x y h0 hx hy => eis_residue_mul p hp h0 x y hx hy
  unit_mul_ne_zero := fun x y h0 hx hy =>
    eis_unit_mul_ne_zero p hp h0 x y hx hy

/-- **見出し定理 (M93F-5c)**: O = ℤ_p[π] の witness 付き整域性
    データ（第一段）は任意の素数 p で存在する。 -/
theorem eisDomain_nonempty (p : Nat) (hp : IsPrime p) :
    Nonempty (EisDomainData p hp) := ⟨eisDomainData p hp⟩

end IUT
