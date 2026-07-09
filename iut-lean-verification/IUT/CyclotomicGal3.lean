/-
  IUT/CyclotomicGal3.lean — A3/W-A2（CG3: Gal(ℚ(ζ₃)/ℚ) の位数ちょうど 2 の
  完全決定）

  ── 主要成果の分類: **[実／本物建設(b)]**。gefNF 担体（ζ_9・一般 n に
     スケールする唯一の担体）上で、非自明 Galois 群 Gal(ℚ(ζ₃)/ℚ) を
     **位数ちょうど 2**（元は id と共役 σ₁ : x̄ ↦ −1−x̄ のみ）と完全決定する。
     honest 仮説 0 本。これが A3 の「非自明有限体拡大が 1 つも構成されていない」
     欠落の初 discharge。

  complete_pct 影響: A3（実 π₁^ét / G_K）への本物前進候補——非自明 Galois 群
  Gal(ℚ(ζ₃)/ℚ) の完全決定を、ζ_9・一般 n にスケールする gefNF 担体上で初めて
  本物化（監査確定待ち・本ファイル単体では complete_pct 未設定）。既存
  `qdf_galois_order_two`（ℚ×ℚ 直積担体・2 次固定）の再演でなく、剰余簡約越しの
  環準同型性（G2 map_mul）と n 項分解（G3 決定補題）を初めて閉じる R3 系の初出。

  段分解:
   * (G1) 生成元 α = x̄・β = −1−x̄ と NF 積の係数公式 `cg3_mul_coeffs`
     （pfdRed_char で x̄² = −1−x̄ を本物化）・`cg3_alpha_sq`/`cg3_beta_sq`。
   * (G2) 共役 σ₁ `cg3ConjFun`・加法性 `cg3ConjFun_add`・**乗法性
     `cg3ConjFun_mul`**（係数公式 + QRat 恒等 `cg3q_conj0/1`）・対合。
   * (G3) 分解 `cg3_decompose`・決定補題 `cg3_aut_ext`（σ は σ(α) で決まる）。
   * (G4) Φ₃ の根 α, β・`cg3_sigma_alpha_root`（σα は根）・`cg3_root_dichotomy`
     （根は α か β・R1 `prc_roots_le_degree` の初適用）。
   * (G5) capstone `cg3_galois_order_two`（位数ちょうど 2）。

  正直な限定（§4 規約により消さない・追記のみ）:
   (i)   p = 3・ℚ 上・1 段のみの忠実な部分ケース（ζ_9・一般 n は後段）。
   (ii)  res（制限準同型）は未構成（M1 前）。本ファイルは Gal(ℚ(ζ₃)/ℚ) の
         完全決定まで。全射性・分離性・正規性の一般論も未形式化。
   (iii) K₁ = ℚ(ζ₃) は既存 `cq3Field`/`qdfField (−3)`/`gfiCq3Field` と同型な
         第 4 の担体（gefNF 表示）であり、同型による定理輸送は対象外。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。数値は QRat 明示計算。新規ファイルのみ（共有ファイル不更新）。
-/
import IUT.CyclotomicField3
import IUT.PolyRootCount
import IUT.RatZeroDecide

namespace IUT

/-! ## CG3-Q: QRat 明示計算の補助 -/

/-- x + ((−x) + y) = y（剰余簡約差の相殺の核）。 -/
theorem qsub_cancel_left (x y : QRat) :
    ratRing.add x (ratRing.add (ratRing.neg x) y) = y := by
  rw [← ratRing.add_assoc x (ratRing.neg x) y, ratRing.add_neg x, ratRing.zero_add y]

/-- (−x)(−y) = xy。 -/
theorem cg3q_negmul (x y : QRat) :
    ratRing.mul (ratRing.neg x) (ratRing.neg y) = ratRing.mul x y := by
  rw [ratRing.neg_mul x (ratRing.neg y), ratRing.mul_neg x y,
    ratRing.neg_neg (ratRing.mul x y)]

/-- 差の積の展開 (x0−x1)(y0−y1) = ((x0y0 − x0y1) − x1y0) + x1y1。 -/
theorem cg3q_expand_sub (x0 x1 y0 y1 : QRat) :
    ratRing.mul (ratRing.add x0 (ratRing.neg x1)) (ratRing.add y0 (ratRing.neg y1))
      = ratRing.add (ratRing.add (ratRing.add (ratRing.mul x0 y0)
          (ratRing.neg (ratRing.mul x0 y1))) (ratRing.neg (ratRing.mul x1 y0)))
          (ratRing.mul x1 y1) := by
  rw [ratRing.left_distrib (ratRing.add x0 (ratRing.neg x1)) y0 (ratRing.neg y1),
    CRing.right_distrib ratRing x0 (ratRing.neg x1) y0,
    CRing.right_distrib ratRing x0 (ratRing.neg x1) (ratRing.neg y1),
    ratRing.neg_mul x1 y0, ratRing.mul_neg x0 y1, cg3q_negmul x1 y1,
    CRing.add_add_add_comm ratRing (ratRing.mul x0 y0) (ratRing.neg (ratRing.mul x1 y0))
      (ratRing.neg (ratRing.mul x0 y1)) (ratRing.mul x1 y1),
    ← ratRing.add_assoc (ratRing.add (ratRing.mul x0 y0) (ratRing.neg (ratRing.mul x0 y1)))
      (ratRing.neg (ratRing.mul x1 y0)) (ratRing.mul x1 y1)]

/-- −1 ≠ 1（ℚ）— 代表の交差積 (−1)·1 = 1·1 に omega。 -/
theorem cg3q_neg_one_ne_one : ratRing.neg ratRing.one ≠ ratRing.one := by
  intro h
  have h2 : Quot.mk ratRel (prNeg prOne) = Quot.mk ratRel prOne := h
  have h3 : (-1 : Int) * 1 = 1 * 1 := quot_exact_rat h2
  omega

/-- ℚ の等値判定（構成的・rzd 経由）: p = q ∨ p ≠ q。 -/
theorem cg3q_eq_dec (p q : QRat) : p = q ∨ p ≠ q := by
  cases rzd_zero_or_ne (ratRing.add p (ratRing.neg q)) with
  | inl h => exact Or.inl (ratRing.eq_of_sub_eq_zero h)
  | inr h =>
    apply Or.inr
    intro he
    apply h
    rw [he, ratRing.add_neg q]

/-! ## CG3-0: 担体の外延性（係数 2 本で決まる） -/

/-- 担体 `GefNF cq0PS 2` の元は 0 次・1 次係数で決まる（2 次以上は 0）。 -/
theorem cg3_carrier_ext (x y : GefNF cq0PS 2)
    (h0 : x.val 0 = y.val 0) (h1 : x.val 1 = y.val 1) : x = y := by
  apply Subtype.ext
  funext j
  cases j with
  | zero => exact h0
  | succ j1 =>
    cases j1 with
    | zero => exact h1
    | succ j2 =>
      show x.val (j2 + 2) = y.val (j2 + 2)
      rw [x.property (j2 + 2) (by omega), y.property (j2 + 2) (by omega)]

/-! ## CG3-1: NF 積の係数公式（x̄² = −1−x̄ の本物化） -/

/-- NF 積の正規形係数（deg ≤ 1 の担体元の積を Φ₃ で簡約したもの）:
    0 次 = a₀b₀ − a₁b₁、1 次 = (a₀b₁ + a₁b₀) − a₁b₁。 -/
def cg3prodCoeff (a b : GefNF cq0PS 2) : PS ratRing := fun j =>
  if j = 0 then
    ratRing.add (ratRing.mul (a.val 0) (b.val 0))
      (ratRing.neg (ratRing.mul (a.val 1) (b.val 1)))
  else if j = 1 then
    ratRing.add (ratRing.add (ratRing.mul (a.val 0) (b.val 1))
      (ratRing.mul (a.val 1) (b.val 0)))
      (ratRing.neg (ratRing.mul (a.val 1) (b.val 1)))
  else ratRing.zero

theorem cg3prodCoeff_0 (a b : GefNF cq0PS 2) :
    cg3prodCoeff a b 0 = ratRing.add (ratRing.mul (a.val 0) (b.val 0))
      (ratRing.neg (ratRing.mul (a.val 1) (b.val 1))) := if_pos rfl

theorem cg3prodCoeff_1 (a b : GefNF cq0PS 2) :
    cg3prodCoeff a b 1 = ratRing.add (ratRing.add (ratRing.mul (a.val 0) (b.val 1))
      (ratRing.mul (a.val 1) (b.val 0)))
      (ratRing.neg (ratRing.mul (a.val 1) (b.val 1))) := by
  show (if (1:Nat) = 0 then _ else if (1:Nat) = 1 then _ else ratRing.zero) = _
  rw [if_neg (by omega : ¬(1:Nat) = 0), if_pos rfl]

theorem cg3prodCoeff_ge2 (a b : GefNF cq0PS 2) (j : Nat) (hj : 2 ≤ j) :
    cg3prodCoeff a b j = ratRing.zero := by
  show (if j = 0 then _ else if j = 1 then _ else ratRing.zero) = ratRing.zero
  rw [if_neg (by omega), if_neg (by omega)]

/-! ## CG3-1b: 低次 Cauchy 積の係数（rsum 展開） -/

theorem cg3_psmul0 (a b : GefNF cq0PS 2) :
    psMul ratRing a.val b.val 0 = ratRing.mul (a.val 0) (b.val 0) := by
  show ratRing.add ratRing.zero (ratRing.mul (a.val 0) (b.val 0))
    = ratRing.mul (a.val 0) (b.val 0)
  exact ratRing.zero_add _

theorem cg3_psmul1 (a b : GefNF cq0PS 2) :
    psMul ratRing a.val b.val 1
      = ratRing.add (ratRing.mul (a.val 0) (b.val 1)) (ratRing.mul (a.val 1) (b.val 0)) := by
  show ratRing.add (ratRing.add ratRing.zero (ratRing.mul (a.val 0) (b.val 1)))
      (ratRing.mul (a.val 1) (b.val 0))
    = ratRing.add (ratRing.mul (a.val 0) (b.val 1)) (ratRing.mul (a.val 1) (b.val 0))
  rw [ratRing.zero_add]

theorem cg3_psmul2 (a b : GefNF cq0PS 2) :
    psMul ratRing a.val b.val 2 = ratRing.mul (a.val 1) (b.val 1) := by
  show ratRing.add (ratRing.add (ratRing.add ratRing.zero
      (ratRing.mul (a.val 0) (b.val 2))) (ratRing.mul (a.val 1) (b.val 1)))
      (ratRing.mul (a.val 2) (b.val 0))
    = ratRing.mul (a.val 1) (b.val 1)
  rw [show b.val 2 = ratRing.zero from b.property 2 (by omega),
    show a.val 2 = ratRing.zero from a.property 2 (by omega),
    ratRing.mul_zero (a.val 0), CRing.zero_mul ratRing (b.val 0),
    ratRing.zero_add, ratRing.zero_add, CRing.add_zero ratRing]

theorem cg3_psmul_ge3 (a b : GefNF cq0PS 2) (j : Nat) (hj : 3 ≤ j) :
    psMul ratRing a.val b.val j = ratRing.zero := by
  show rsum ratRing (fun k => ratRing.mul (a.val k) (b.val (j - k))) (j + 1) = ratRing.zero
  have hc : rsum ratRing (fun k => ratRing.mul (a.val k) (b.val (j - k))) (j + 1)
      = rsum ratRing (fun _ => ratRing.zero) (j + 1) :=
    rsum_congr ratRing (j + 1) (fun k _ => by
      cases Nat.lt_or_ge k 2 with
      | inr hge => rw [a.property k hge, CRing.zero_mul ratRing (b.val (j - k))]
      | inl hlt => rw [b.property (j - k) (by omega), ratRing.mul_zero (a.val k)])
  rw [hc]
  exact rsum_const_zero ratRing (j + 1)

/-! ## CG3-1c: 係数公式（本丸・pfdRed_char） -/

/-- **NF 積の係数公式** — 担体元 a, b（deg ≤ 1）に対し、K₁ = ℚ(ζ₃) の積
    `cnfPhi3Field.mul a b` の各係数は `cg3prodCoeff a b`。証明は剰余の一意
    特徴付け `pfdRed_char`: a·b（deg ≤ 2）と正規形 v の差が psC(a₁b₁)·Φ₃
    （x̄² ≡ −1−x̄ の実現）に等しいことを全次数で確認する。 -/
theorem cg3_mul_coeffs (a b : GefNF cq0PS 2) :
    ∀ j, (cnfPhi3Field.mul a b).val j = cg3prodCoeff a b j := by
  have hw : IsPolyBounded ratRing (psMul ratRing a.val b.val) (2 + 2) := by
    intro i hi
    exact cg3_psmul_ge3 a b i (by omega)
  have hv : IsPolyBounded ratRing (cg3prodCoeff a b) 2 := by
    intro i hi
    exact cg3prodCoeff_ge2 a b i hi
  have hcong : ∃ (h : PS ratRing) (Nh : Nat), IsPolyBounded ratRing h Nh ∧
      ∀ j, psAdd ratRing (psMul ratRing a.val b.val)
        (psNeg ratRing (cg3prodCoeff a b)) j
        = psMul ratRing h cq0PS j := by
    refine ⟨psC ratRing (ratRing.mul (a.val 1) (b.val 1)), 1, ?_, ?_⟩
    · intro i hi
      show psC ratRing (ratRing.mul (a.val 1) (b.val 1)) i = ratRing.zero
      exact if_neg (by omega)
    · intro j
      cases j with
      | zero =>
        show ratRing.add (psMul ratRing a.val b.val 0)
            (ratRing.neg (cg3prodCoeff a b 0))
          = psMul ratRing (psC ratRing (ratRing.mul (a.val 1) (b.val 1))) cq0PS 0
        rw [cg3_psmul0 a b, cg3prodCoeff_0 a b,
          gefSmulCoeff (ratRing.mul (a.val 1) (b.val 1)) cq0PS 0, cq0PS_coeff0,
          CRing.mul_one ratRing,
          ratRing.neg_add_dist (ratRing.mul (a.val 0) (b.val 0))
            (ratRing.neg (ratRing.mul (a.val 1) (b.val 1))),
          ratRing.neg_neg (ratRing.mul (a.val 1) (b.val 1))]
        exact qsub_cancel_left (ratRing.mul (a.val 0) (b.val 0))
          (ratRing.mul (a.val 1) (b.val 1))
      | succ j1 =>
        cases j1 with
        | zero =>
          show ratRing.add (psMul ratRing a.val b.val 1)
              (ratRing.neg (cg3prodCoeff a b 1))
            = psMul ratRing (psC ratRing (ratRing.mul (a.val 1) (b.val 1))) cq0PS 1
          rw [cg3_psmul1 a b, cg3prodCoeff_1 a b,
            gefSmulCoeff (ratRing.mul (a.val 1) (b.val 1)) cq0PS 1, cq0PS_coeff1,
            CRing.mul_one ratRing,
            ratRing.neg_add_dist (ratRing.add (ratRing.mul (a.val 0) (b.val 1))
              (ratRing.mul (a.val 1) (b.val 0)))
              (ratRing.neg (ratRing.mul (a.val 1) (b.val 1))),
            ratRing.neg_neg (ratRing.mul (a.val 1) (b.val 1))]
          exact qsub_cancel_left (ratRing.add (ratRing.mul (a.val 0) (b.val 1))
            (ratRing.mul (a.val 1) (b.val 0))) (ratRing.mul (a.val 1) (b.val 1))
        | succ j2 =>
          cases j2 with
          | zero =>
            show ratRing.add (psMul ratRing a.val b.val 2)
                (ratRing.neg (cg3prodCoeff a b 2))
              = psMul ratRing (psC ratRing (ratRing.mul (a.val 1) (b.val 1))) cq0PS 2
            rw [cg3_psmul2 a b, cg3prodCoeff_ge2 a b 2 (by omega),
              gefSmulCoeff (ratRing.mul (a.val 1) (b.val 1)) cq0PS 2, cq0PS_coeff2,
              CRing.mul_one ratRing, CRing.neg_zero ratRing, CRing.add_zero ratRing]
          | succ j3 =>
            show ratRing.add (psMul ratRing a.val b.val (j3 + 3))
                (ratRing.neg (cg3prodCoeff a b (j3 + 3)))
              = psMul ratRing (psC ratRing (ratRing.mul (a.val 1) (b.val 1))) cq0PS (j3 + 3)
            rw [cg3_psmul_ge3 a b (j3 + 3) (by omega),
              cg3prodCoeff_ge2 a b (j3 + 3) (by omega),
              gefSmulCoeff (ratRing.mul (a.val 1) (b.val 1)) cq0PS (j3 + 3),
              show cq0PS (j3 + 3) = ratRing.zero from cq0_bound (j3 + 3) (by omega),
              CRing.neg_zero ratRing, ratRing.zero_add, ratRing.mul_zero]
  intro j
  show pfdRed cq0PS 2 2 (psMul ratRing a.val b.val) j = cg3prodCoeff a b j
  exact pfdRed_char cq0PS 2 cq0_bound cq0_lead 2 (psMul ratRing a.val b.val)
    (cg3prodCoeff a b) hw hv hcong j

/-- NF 積の 0 次係数。 -/
theorem cg3_mul_val0 (a b : GefNF cq0PS 2) :
    (cnfPhi3Field.mul a b).val 0
      = ratRing.add (ratRing.mul (a.val 0) (b.val 0))
        (ratRing.neg (ratRing.mul (a.val 1) (b.val 1))) := by
  rw [cg3_mul_coeffs a b 0, cg3prodCoeff_0 a b]

/-- NF 積の 1 次係数。 -/
theorem cg3_mul_val1 (a b : GefNF cq0PS 2) :
    (cnfPhi3Field.mul a b).val 1
      = ratRing.add (ratRing.add (ratRing.mul (a.val 0) (b.val 1))
        (ratRing.mul (a.val 1) (b.val 0)))
        (ratRing.neg (ratRing.mul (a.val 1) (b.val 1))) := by
  rw [cg3_mul_coeffs a b 1, cg3prodCoeff_1 a b]

/-! ## CG3-Q2: 共役の乗法性の QRat 恒等（σ₁(ab) = σ₁(a)σ₁(b) の係数） -/

/-- 0 次係数の恒等（共役の乗法性）。両辺は
    (x0y0 − x0y1) − x1y0 に正規化される。 -/
theorem cg3q_conj0 (x0 x1 y0 y1 : QRat) :
    ratRing.add (ratRing.add (ratRing.mul x0 y0) (ratRing.neg (ratRing.mul x1 y1)))
      (ratRing.neg (ratRing.add (ratRing.add (ratRing.mul x0 y1) (ratRing.mul x1 y0))
        (ratRing.neg (ratRing.mul x1 y1))))
    = ratRing.add (ratRing.mul (ratRing.add x0 (ratRing.neg x1))
          (ratRing.add y0 (ratRing.neg y1)))
        (ratRing.neg (ratRing.mul (ratRing.neg x1) (ratRing.neg y1))) := by
  have hL : ratRing.add (ratRing.add (ratRing.mul x0 y0) (ratRing.neg (ratRing.mul x1 y1)))
      (ratRing.neg (ratRing.add (ratRing.add (ratRing.mul x0 y1) (ratRing.mul x1 y0))
        (ratRing.neg (ratRing.mul x1 y1))))
    = ratRing.add (ratRing.add (ratRing.mul x0 y0) (ratRing.neg (ratRing.mul x0 y1)))
        (ratRing.neg (ratRing.mul x1 y0)) := by
    rw [ratRing.neg_add_dist (ratRing.add (ratRing.mul x0 y1) (ratRing.mul x1 y0))
        (ratRing.neg (ratRing.mul x1 y1)),
      ratRing.neg_add_dist (ratRing.mul x0 y1) (ratRing.mul x1 y0),
      ratRing.neg_neg (ratRing.mul x1 y1),
      CRing.add_add_add_comm ratRing (ratRing.mul x0 y0) (ratRing.neg (ratRing.mul x1 y1))
        (ratRing.add (ratRing.neg (ratRing.mul x0 y1)) (ratRing.neg (ratRing.mul x1 y0)))
        (ratRing.mul x1 y1),
      ratRing.neg_add (ratRing.mul x1 y1), CRing.add_zero ratRing,
      ← ratRing.add_assoc (ratRing.mul x0 y0) (ratRing.neg (ratRing.mul x0 y1))
        (ratRing.neg (ratRing.mul x1 y0))]
  have hR : ratRing.add (ratRing.mul (ratRing.add x0 (ratRing.neg x1))
          (ratRing.add y0 (ratRing.neg y1)))
        (ratRing.neg (ratRing.mul (ratRing.neg x1) (ratRing.neg y1)))
    = ratRing.add (ratRing.add (ratRing.mul x0 y0) (ratRing.neg (ratRing.mul x0 y1)))
        (ratRing.neg (ratRing.mul x1 y0)) := by
    rw [cg3q_expand_sub x0 x1 y0 y1, cg3q_negmul x1 y1,
      ratRing.add_assoc (ratRing.add (ratRing.add (ratRing.mul x0 y0)
          (ratRing.neg (ratRing.mul x0 y1))) (ratRing.neg (ratRing.mul x1 y0)))
        (ratRing.mul x1 y1) (ratRing.neg (ratRing.mul x1 y1)),
      ratRing.add_neg (ratRing.mul x1 y1), CRing.add_zero ratRing]
  exact hL.trans hR.symm

/-- 1 次係数の恒等（共役の乗法性）。両辺は
    (−x0y1 − x1y0) + x1y1 に正規化される。 -/
theorem cg3q_conj1 (x0 x1 y0 y1 : QRat) :
    ratRing.neg (ratRing.add (ratRing.add (ratRing.mul x0 y1) (ratRing.mul x1 y0))
      (ratRing.neg (ratRing.mul x1 y1)))
    = ratRing.add (ratRing.add
        (ratRing.mul (ratRing.add x0 (ratRing.neg x1)) (ratRing.neg y1))
        (ratRing.mul (ratRing.neg x1) (ratRing.add y0 (ratRing.neg y1))))
        (ratRing.neg (ratRing.mul (ratRing.neg x1) (ratRing.neg y1))) := by
  have hL : ratRing.neg (ratRing.add (ratRing.add (ratRing.mul x0 y1) (ratRing.mul x1 y0))
        (ratRing.neg (ratRing.mul x1 y1)))
    = ratRing.add (ratRing.add (ratRing.neg (ratRing.mul x0 y1))
        (ratRing.neg (ratRing.mul x1 y0))) (ratRing.mul x1 y1) := by
    rw [ratRing.neg_add_dist (ratRing.add (ratRing.mul x0 y1) (ratRing.mul x1 y0))
        (ratRing.neg (ratRing.mul x1 y1)),
      ratRing.neg_add_dist (ratRing.mul x0 y1) (ratRing.mul x1 y0),
      ratRing.neg_neg (ratRing.mul x1 y1)]
  have hR : ratRing.add (ratRing.add
        (ratRing.mul (ratRing.add x0 (ratRing.neg x1)) (ratRing.neg y1))
        (ratRing.mul (ratRing.neg x1) (ratRing.add y0 (ratRing.neg y1))))
        (ratRing.neg (ratRing.mul (ratRing.neg x1) (ratRing.neg y1)))
    = ratRing.add (ratRing.add (ratRing.neg (ratRing.mul x0 y1))
        (ratRing.neg (ratRing.mul x1 y0))) (ratRing.mul x1 y1) := by
    rw [CRing.right_distrib ratRing x0 (ratRing.neg x1) (ratRing.neg y1),
      ratRing.left_distrib (ratRing.neg x1) y0 (ratRing.neg y1),
      ratRing.mul_neg x0 y1, ratRing.neg_mul x1 y0, cg3q_negmul x1 y1,
      CRing.add_add_add_comm ratRing (ratRing.neg (ratRing.mul x0 y1)) (ratRing.mul x1 y1)
        (ratRing.neg (ratRing.mul x1 y0)) (ratRing.mul x1 y1),
      ratRing.add_assoc (ratRing.add (ratRing.neg (ratRing.mul x0 y1))
          (ratRing.neg (ratRing.mul x1 y0))) (ratRing.add (ratRing.mul x1 y1)
          (ratRing.mul x1 y1)) (ratRing.neg (ratRing.mul x1 y1)),
      ratRing.add_assoc (ratRing.mul x1 y1) (ratRing.mul x1 y1)
        (ratRing.neg (ratRing.mul x1 y1)),
      ratRing.add_neg (ratRing.mul x1 y1), CRing.add_zero ratRing]
  exact hL.trans hR.symm

/-! ## CG3-2: 担体の小補題（add・one・zero・incl の係数） -/

theorem cg3_add_val (x y : GefNF cq0PS 2) (j : Nat) :
    (cnfPhi3Field.add x y).val j = ratRing.add (x.val j) (y.val j) := rfl

theorem cg3_zero_val (j : Nat) : cnfPhi3Field.zero.val j = ratRing.zero := rfl

theorem cg3_one_val0 : cnfPhi3Field.one.val 0 = ratRing.one := by
  show (if (0:Nat) = 0 then ratRing.one else ratRing.zero) = ratRing.one
  exact if_pos rfl

theorem cg3_one_val1 : cnfPhi3Field.one.val 1 = ratRing.zero := by
  show (if (1:Nat) = 0 then ratRing.one else ratRing.zero) = ratRing.zero
  exact if_neg (by omega)

theorem cnf_incl_val0 (c : QRat) : (cnfExt3.incl c).val 0 = c := by
  show psC ratRing c 0 = c
  exact if_pos rfl

theorem cnf_incl_val1 (c : QRat) : (cnfExt3.incl c).val 1 = ratRing.zero := by
  show psC ratRing c 1 = ratRing.zero
  exact if_neg (by omega)

/-! ## CG3-3(G1): 生成元 α = x̄ と β = −1−x̄ -/

/-- 生成元 α = x̄（NF 単項式 X^1）。 -/
def cg3Alpha : GefNF cq0PS 2 := gefNFMon cq0PS 2 1 (by omega)

theorem cg3Alpha_val0 : cg3Alpha.val 0 = ratRing.zero := by
  show psSingle ratRing ratRing.one 1 0 = ratRing.zero
  exact if_neg (by omega)

theorem cg3Alpha_val1 : cg3Alpha.val 1 = ratRing.one := by
  show psSingle ratRing ratRing.one 1 1 = ratRing.one
  exact if_pos rfl

/-- 共役元 β = −1−x̄（係数 (−1, −1)）。 -/
def cg3Beta : GefNF cq0PS 2 :=
  ⟨fun j => if j = 0 then ratRing.neg ratRing.one
            else if j = 1 then ratRing.neg ratRing.one else ratRing.zero,
   fun j hj => by
     show (if j = 0 then ratRing.neg ratRing.one
       else if j = 1 then ratRing.neg ratRing.one else ratRing.zero) = ratRing.zero
     rw [if_neg (by omega), if_neg (by omega)]⟩

theorem cg3Beta_val0 : cg3Beta.val 0 = ratRing.neg ratRing.one := by
  show (if (0:Nat) = 0 then ratRing.neg ratRing.one
    else if (0:Nat) = 1 then ratRing.neg ratRing.one else ratRing.zero)
    = ratRing.neg ratRing.one
  exact if_pos rfl

theorem cg3Beta_val1 : cg3Beta.val 1 = ratRing.neg ratRing.one := by
  show (if (1:Nat) = 0 then ratRing.neg ratRing.one
    else if (1:Nat) = 1 then ratRing.neg ratRing.one else ratRing.zero)
    = ratRing.neg ratRing.one
  rw [if_neg (by omega : ¬(1:Nat) = 0), if_pos rfl]

/-- α ≠ β（1 次係数 1 ≠ −1）。 -/
theorem cg3Alpha_ne_beta : cg3Alpha ≠ cg3Beta := by
  intro h
  have h1 : cg3Alpha.val 1 = cg3Beta.val 1 :=
    congrArg (fun z : GefNF cq0PS 2 => z.val 1) h
  rw [cg3Alpha_val1, cg3Beta_val1] at h1
  exact cg3q_neg_one_ne_one h1.symm

/-! ## CG3-4(G2): 共役自己同型 σ₁ : y₀ + y₁x̄ ↦ (y₀−y₁) + (−y₁)x̄ -/

/-- 共役の担体写像 σ₁。 -/
def cg3ConjFun (y : GefNF cq0PS 2) : GefNF cq0PS 2 :=
  ⟨fun j => if j = 0 then ratRing.add (y.val 0) (ratRing.neg (y.val 1))
            else if j = 1 then ratRing.neg (y.val 1) else ratRing.zero,
   fun j hj => by
     show (if j = 0 then ratRing.add (y.val 0) (ratRing.neg (y.val 1))
       else if j = 1 then ratRing.neg (y.val 1) else ratRing.zero) = ratRing.zero
     rw [if_neg (by omega), if_neg (by omega)]⟩

theorem cg3ConjFun_val0 (y : GefNF cq0PS 2) :
    (cg3ConjFun y).val 0 = ratRing.add (y.val 0) (ratRing.neg (y.val 1)) := by
  show (if (0:Nat) = 0 then ratRing.add (y.val 0) (ratRing.neg (y.val 1))
    else if (0:Nat) = 1 then ratRing.neg (y.val 1) else ratRing.zero)
    = ratRing.add (y.val 0) (ratRing.neg (y.val 1))
  exact if_pos rfl

theorem cg3ConjFun_val1 (y : GefNF cq0PS 2) :
    (cg3ConjFun y).val 1 = ratRing.neg (y.val 1) := by
  show (if (1:Nat) = 0 then ratRing.add (y.val 0) (ratRing.neg (y.val 1))
    else if (1:Nat) = 1 then ratRing.neg (y.val 1) else ratRing.zero)
    = ratRing.neg (y.val 1)
  rw [if_neg (by omega : ¬(1:Nat) = 0), if_pos rfl]

/-- **G2 加法性** σ₁(x+y) = σ₁(x)+σ₁(y)（成分ごと線形）。 -/
theorem cg3ConjFun_add (x y : GefNF cq0PS 2) :
    cg3ConjFun (cnfPhi3Field.add x y)
      = cnfPhi3Field.add (cg3ConjFun x) (cg3ConjFun y) := by
  apply cg3_carrier_ext
  · rw [cg3ConjFun_val0 (cnfPhi3Field.add x y), cg3_add_val x y 0, cg3_add_val x y 1,
      cg3_add_val (cg3ConjFun x) (cg3ConjFun y) 0, cg3ConjFun_val0 x, cg3ConjFun_val0 y,
      ratRing.neg_add_dist (x.val 1) (y.val 1),
      CRing.add_add_add_comm ratRing (x.val 0) (y.val 0)
        (ratRing.neg (x.val 1)) (ratRing.neg (y.val 1))]
  · rw [cg3ConjFun_val1 (cnfPhi3Field.add x y), cg3_add_val x y 1,
      cg3_add_val (cg3ConjFun x) (cg3ConjFun y) 1, cg3ConjFun_val1 x, cg3ConjFun_val1 y,
      ratRing.neg_add_dist (x.val 1) (y.val 1)]

/-- **G2 乗法性（山場）** σ₁(xy) = σ₁(x)σ₁(y)。剰余簡約越しの環準同型性を
    係数公式 `cg3_mul_val0/1` と QRat 恒等 `cg3q_conj0/1` で本物に閉じる。 -/
theorem cg3ConjFun_mul (x y : GefNF cq0PS 2) :
    cg3ConjFun (cnfPhi3Field.mul x y)
      = cnfPhi3Field.mul (cg3ConjFun x) (cg3ConjFun y) := by
  apply cg3_carrier_ext
  · rw [cg3ConjFun_val0 (cnfPhi3Field.mul x y), cg3_mul_val0 x y, cg3_mul_val1 x y,
      cg3_mul_val0 (cg3ConjFun x) (cg3ConjFun y), cg3ConjFun_val0 x, cg3ConjFun_val1 x,
      cg3ConjFun_val0 y, cg3ConjFun_val1 y]
    exact cg3q_conj0 (x.val 0) (x.val 1) (y.val 0) (y.val 1)
  · rw [cg3ConjFun_val1 (cnfPhi3Field.mul x y), cg3_mul_val1 x y,
      cg3_mul_val1 (cg3ConjFun x) (cg3ConjFun y), cg3ConjFun_val0 x, cg3ConjFun_val1 x,
      cg3ConjFun_val0 y, cg3ConjFun_val1 y]
    exact cg3q_conj1 (x.val 0) (x.val 1) (y.val 0) (y.val 1)

/-- σ₁(1) = 1。 -/
theorem cg3ConjFun_one : cg3ConjFun cnfPhi3Field.one = cnfPhi3Field.one := by
  apply cg3_carrier_ext
  · rw [cg3ConjFun_val0 cnfPhi3Field.one, cg3_one_val0, cg3_one_val1,
      CRing.neg_zero ratRing, CRing.add_zero ratRing]
  · rw [cg3ConjFun_val1 cnfPhi3Field.one, cg3_one_val1, CRing.neg_zero ratRing]

/-- σ₁ は対合（σ₁² = id）。 -/
theorem cg3ConjFun_invol (y : GefNF cq0PS 2) : cg3ConjFun (cg3ConjFun y) = y := by
  apply cg3_carrier_ext
  · rw [cg3ConjFun_val0 (cg3ConjFun y), cg3ConjFun_val0 y, cg3ConjFun_val1 y,
      ratRing.neg_neg (y.val 1),
      ratRing.add_assoc (y.val 0) (ratRing.neg (y.val 1)) (y.val 1),
      ratRing.neg_add (y.val 1), CRing.add_zero ratRing]
  · rw [cg3ConjFun_val1 (cg3ConjFun y), cg3ConjFun_val1 y, ratRing.neg_neg (y.val 1)]

/-- σ₁(α) = β。 -/
theorem cg3_conj_alpha : cg3ConjFun cg3Alpha = cg3Beta := by
  apply cg3_carrier_ext
  · rw [cg3ConjFun_val0 cg3Alpha, cg3Alpha_val0, cg3Alpha_val1, cg3Beta_val0,
      ratRing.zero_add]
  · rw [cg3ConjFun_val1 cg3Alpha, cg3Alpha_val1, cg3Beta_val1]

/-- **G2: 共役 σ₁ は ℚ(ζ₃) の体自己同型**（明示逆写像 = 自身の対合）。 -/
def cg3Conj : FieldAut cnfPhi3Field where
  toFun := cg3ConjFun
  invFun := cg3ConjFun
  map_add := cg3ConjFun_add
  map_mul := cg3ConjFun_mul
  map_one := cg3ConjFun_one
  left_inv := cg3ConjFun_invol
  right_inv := cg3ConjFun_invol

/-- σ₁ は ℚ を各点固定（Gal(ℚ(ζ₃)/ℚ) の元）。 -/
theorem cg3Conj_mem : (galoisSubgroup cnfExt3).mem cg3Conj := by
  intro k
  show cg3ConjFun (cnfExt3.incl k) = cnfExt3.incl k
  apply cg3_carrier_ext
  · rw [cg3ConjFun_val0 (cnfExt3.incl k), cnf_incl_val1 k, CRing.neg_zero ratRing,
      CRing.add_zero ratRing]
  · rw [cg3ConjFun_val1 (cnfExt3.incl k), cnf_incl_val1 k, CRing.neg_zero ratRing]

/-- σ₁ ≠ id（σ₁(α) = β ≠ α）。 -/
theorem cg3Conj_ne_id : cg3Conj ≠ fieldAutId cnfPhi3Field := by
  intro h
  have h1 : cg3Conj.toFun cg3Alpha = (fieldAutId cnfPhi3Field).toFun cg3Alpha :=
    congrArg (fun σ : FieldAut cnfPhi3Field => σ.toFun cg3Alpha) h
  have h2 : cg3Beta = cg3Alpha := by
    rw [← cg3_conj_alpha]; exact h1
  have h3 : cg3Beta.val 1 = cg3Alpha.val 1 :=
    congrArg (fun z : GefNF cq0PS 2 => z.val 1) h2
  rw [cg3Beta_val1, cg3Alpha_val1] at h3
  exact cg3q_neg_one_ne_one h3

/-! ## CG3-5(G1): α² = β・β² = α（x̄² = −1−x̄ の帰結） -/

/-- **α² = β**（x̄·x̄ = x̄² 簡約 = −1−x̄）。 -/
theorem cg3_alpha_sq : cnfPhi3Field.mul cg3Alpha cg3Alpha = cg3Beta := by
  apply cg3_carrier_ext
  · rw [cg3_mul_val0 cg3Alpha cg3Alpha, cg3Alpha_val0, cg3Alpha_val1,
      CRing.zero_mul ratRing ratRing.zero, ratRing.one_mul ratRing.one, cg3Beta_val0,
      ratRing.zero_add]
  · rw [cg3_mul_val1 cg3Alpha cg3Alpha, cg3Alpha_val0, cg3Alpha_val1,
      CRing.zero_mul ratRing ratRing.one, ratRing.mul_zero ratRing.one,
      ratRing.one_mul ratRing.one, cg3Beta_val1, ratRing.zero_add, ratRing.zero_add]

/-- **β² = α**（ζ⁴ = ζ）。 -/
theorem cg3_beta_sq : cnfPhi3Field.mul cg3Beta cg3Beta = cg3Alpha := by
  apply cg3_carrier_ext
  · rw [cg3_mul_val0 cg3Beta cg3Beta, cg3Beta_val0, cg3Beta_val1,
      cg3q_negmul ratRing.one ratRing.one, ratRing.one_mul ratRing.one, cg3Alpha_val0,
      ratRing.add_neg ratRing.one]
  · rw [cg3_mul_val1 cg3Beta cg3Beta, cg3Beta_val0, cg3Beta_val1,
      cg3q_negmul ratRing.one ratRing.one, ratRing.one_mul ratRing.one, cg3Alpha_val1,
      ratRing.add_assoc ratRing.one ratRing.one (ratRing.neg ratRing.one),
      ratRing.add_neg ratRing.one, CRing.add_zero ratRing]

/-! ## CG3-6(G3): 分解 y = ι(y₀) + ι(y₁)·α と決定補題 -/

theorem cg3_inclMulAlpha_val0 (c : QRat) :
    (cnfPhi3Field.mul (cnfExt3.incl c) cg3Alpha).val 0 = ratRing.zero := by
  rw [cg3_mul_val0 (cnfExt3.incl c) cg3Alpha, cnf_incl_val0 c, cnf_incl_val1 c,
    cg3Alpha_val0, cg3Alpha_val1, ratRing.mul_zero c, CRing.zero_mul ratRing ratRing.one,
    CRing.neg_zero ratRing, ratRing.zero_add]

theorem cg3_inclMulAlpha_val1 (c : QRat) :
    (cnfPhi3Field.mul (cnfExt3.incl c) cg3Alpha).val 1 = c := by
  rw [cg3_mul_val1 (cnfExt3.incl c) cg3Alpha, cnf_incl_val0 c, cnf_incl_val1 c,
    cg3Alpha_val0, cg3Alpha_val1, CRing.mul_one ratRing c,
    CRing.zero_mul ratRing ratRing.zero, CRing.zero_mul ratRing ratRing.one,
    CRing.neg_zero ratRing, CRing.add_zero ratRing (ratRing.add c ratRing.zero),
    CRing.add_zero ratRing c]

/-- **G3 分解** — 任意の担体元は ℚ 上 {1, α} の一次結合 y = ι(y₀) + ι(y₁)·α。 -/
theorem cg3_decompose (y : GefNF cq0PS 2) :
    y = cnfPhi3Field.add (cnfExt3.incl (y.val 0))
      (cnfPhi3Field.mul (cnfExt3.incl (y.val 1)) cg3Alpha) := by
  apply cg3_carrier_ext
  · rw [cg3_add_val (cnfExt3.incl (y.val 0))
        (cnfPhi3Field.mul (cnfExt3.incl (y.val 1)) cg3Alpha) 0,
      cnf_incl_val0 (y.val 0), cg3_inclMulAlpha_val0 (y.val 1), CRing.add_zero ratRing]
  · rw [cg3_add_val (cnfExt3.incl (y.val 0))
        (cnfPhi3Field.mul (cnfExt3.incl (y.val 1)) cg3Alpha) 1,
      cnf_incl_val1 (y.val 0), cg3_inclMulAlpha_val1 (y.val 1), ratRing.zero_add]

/-- **G3 決定補題** — ℚ を固定する自己同型 σ, τ が α で一致すれば σ = τ
    （生成元の像で自己同型が決まる）。 -/
theorem cg3_aut_ext (σ τ : FieldAut cnfPhi3Field)
    (hσ : (galoisSubgroup cnfExt3).mem σ) (hτ : (galoisSubgroup cnfExt3).mem τ)
    (h : σ.toFun cg3Alpha = τ.toFun cg3Alpha) : σ = τ := by
  have htofun : ∀ y, σ.toFun y = τ.toFun y := by
    intro y
    rw [cg3_decompose y, σ.map_add, σ.map_mul, τ.map_add, τ.map_mul,
      hσ (y.val 0), hσ (y.val 1), hτ (y.val 0), hτ (y.val 1), h]
  apply FieldAut.ext
  · funext y; exact htofun y
  · funext x
    have h1 : σ.toFun (σ.invFun x) = x := σ.right_inv x
    have h2 : τ.toFun (σ.invFun x) = x := by rw [← htofun (σ.invFun x)]; exact h1
    have h3 : τ.invFun (τ.toFun (σ.invFun x)) = σ.invFun x := τ.left_inv (σ.invFun x)
    rw [h2] at h3
    exact h3.symm

/-! ## CG3-7(G4): Φ₃ の根 α, β と根の二分法（R1 の初適用） -/

/-- Φ₃ を K₁ = ℚ(ζ₃) の係数へ持ち上げた多項式（係数は全て 1_K）。 -/
def cg3PhiTop : PS cnfPhi3F268.ring := fun j =>
  if j = 0 then cnfPhi3F268.ring.one
  else if j = 1 then cnfPhi3F268.ring.one
  else if j = 2 then cnfPhi3F268.ring.one
  else cnfPhi3F268.ring.zero

theorem cg3PhiTop_0 : cg3PhiTop 0 = cnfPhi3F268.ring.one := if_pos rfl

theorem cg3PhiTop_1 : cg3PhiTop 1 = cnfPhi3F268.ring.one := by
  show (if (1:Nat) = 0 then _ else if (1:Nat) = 1 then cnfPhi3F268.ring.one else _)
    = cnfPhi3F268.ring.one
  rw [if_neg (by omega : ¬(1:Nat) = 0), if_pos rfl]

theorem cg3PhiTop_2 : cg3PhiTop 2 = cnfPhi3F268.ring.one := by
  show (if (2:Nat) = 0 then _ else if (2:Nat) = 1 then _
    else if (2:Nat) = 2 then cnfPhi3F268.ring.one else _) = cnfPhi3F268.ring.one
  rw [if_neg (by omega : ¬(2:Nat) = 0), if_neg (by omega : ¬(2:Nat) = 1), if_pos rfl]

theorem cg3PhiTop_bound : IsPolyBounded cnfPhi3F268.ring cg3PhiTop 3 := by
  intro j hj
  show (if j = 0 then _ else if j = 1 then _ else if j = 2 then _
    else cnfPhi3F268.ring.zero) = cnfPhi3F268.ring.zero
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **根の一般補題** — t²+t+1 = 0（K₁ 内）なら t は cg3PhiTop の根。
    評価 ev_t(Φ₃)|₃ = 1 + t + t² を t²+t+1 = 0 と可換環の並べ替えで潰す。 -/
theorem cg3_root_of_phi (t : GefNF cq0PS 2)
    (ht : cnfPhi3Field.add (cnfPhi3Field.add (cnfPhi3Field.mul t t) t) cnfPhi3Field.one
      = cnfPhi3Field.zero) :
    prcIsRoot cnfPhi3F268 cg3PhiTop t := by
  apply prc_root_of_eval cnfPhi3F268 cg3PhiTop t 3 cg3PhiTop_bound
  rw [evalSum_id]
  have hT0 : cnfPhi3F268.ring.mul (cg3PhiTop 0) (rpow cnfPhi3F268.ring t 0)
      = cnfPhi3F268.ring.one := by
    rw [cg3PhiTop_0]
    show cnfPhi3F268.ring.mul cnfPhi3F268.ring.one cnfPhi3F268.ring.one
      = cnfPhi3F268.ring.one
    exact cnfPhi3F268.ring.one_mul cnfPhi3F268.ring.one
  have hT1 : cnfPhi3F268.ring.mul (cg3PhiTop 1) (rpow cnfPhi3F268.ring t 1) = t := by
    rw [cg3PhiTop_1]
    show cnfPhi3F268.ring.mul cnfPhi3F268.ring.one
      (cnfPhi3F268.ring.mul cnfPhi3F268.ring.one t) = t
    rw [cnfPhi3F268.ring.one_mul, cnfPhi3F268.ring.one_mul]
  have hT2 : cnfPhi3F268.ring.mul (cg3PhiTop 2) (rpow cnfPhi3F268.ring t 2)
      = cnfPhi3F268.ring.mul t t := by
    rw [cg3PhiTop_2]
    show cnfPhi3F268.ring.mul cnfPhi3F268.ring.one
      (cnfPhi3F268.ring.mul (cnfPhi3F268.ring.mul cnfPhi3F268.ring.one t) t)
      = cnfPhi3F268.ring.mul t t
    rw [cnfPhi3F268.ring.one_mul, cnfPhi3F268.ring.one_mul]
  show cnfPhi3F268.ring.add (cnfPhi3F268.ring.add (cnfPhi3F268.ring.add
        cnfPhi3F268.ring.zero (cnfPhi3F268.ring.mul (cg3PhiTop 0) (rpow cnfPhi3F268.ring t 0)))
        (cnfPhi3F268.ring.mul (cg3PhiTop 1) (rpow cnfPhi3F268.ring t 1)))
        (cnfPhi3F268.ring.mul (cg3PhiTop 2) (rpow cnfPhi3F268.ring t 2))
    = cnfPhi3F268.ring.zero
  rw [hT0, hT1, hT2, cnfPhi3F268.ring.zero_add,
    cnfPhi3F268.ring.add_comm (cnfPhi3F268.ring.add cnfPhi3F268.ring.one t)
      (cnfPhi3F268.ring.mul t t),
    cnfPhi3F268.ring.add_comm cnfPhi3F268.ring.one t,
    ← cnfPhi3F268.ring.add_assoc (cnfPhi3F268.ring.mul t t) t cnfPhi3F268.ring.one]
  exact ht

/-- **α は Φ₃ の根**（α²+α+1 = β+α+1 = 0）。 -/
theorem cg3_alpha_root :
    cnfPhi3Field.add (cnfPhi3Field.add (cnfPhi3Field.mul cg3Alpha cg3Alpha) cg3Alpha)
      cnfPhi3Field.one = cnfPhi3Field.zero := by
  rw [cg3_alpha_sq]
  apply cg3_carrier_ext
  · rw [cg3_add_val (cnfPhi3Field.add cg3Beta cg3Alpha) cnfPhi3Field.one 0,
      cg3_add_val cg3Beta cg3Alpha 0, cg3Beta_val0, cg3Alpha_val0, cg3_one_val0,
      cg3_zero_val 0, CRing.add_zero ratRing, ratRing.neg_add ratRing.one]
  · rw [cg3_add_val (cnfPhi3Field.add cg3Beta cg3Alpha) cnfPhi3Field.one 1,
      cg3_add_val cg3Beta cg3Alpha 1, cg3Beta_val1, cg3Alpha_val1, cg3_one_val1,
      cg3_zero_val 1, ratRing.neg_add ratRing.one, ratRing.zero_add]

/-- **β は Φ₃ の根**（β²+β+1 = α+β+1 = 0）。 -/
theorem cg3_beta_root :
    cnfPhi3Field.add (cnfPhi3Field.add (cnfPhi3Field.mul cg3Beta cg3Beta) cg3Beta)
      cnfPhi3Field.one = cnfPhi3Field.zero := by
  rw [cg3_beta_sq]
  apply cg3_carrier_ext
  · rw [cg3_add_val (cnfPhi3Field.add cg3Alpha cg3Beta) cnfPhi3Field.one 0,
      cg3_add_val cg3Alpha cg3Beta 0, cg3Alpha_val0, cg3Beta_val0, cg3_one_val0,
      cg3_zero_val 0, ratRing.zero_add, ratRing.neg_add ratRing.one]
  · rw [cg3_add_val (cnfPhi3Field.add cg3Alpha cg3Beta) cnfPhi3Field.one 1,
      cg3_add_val cg3Alpha cg3Beta 1, cg3Alpha_val1, cg3Beta_val1, cg3_one_val1,
      cg3_zero_val 1, ratRing.add_neg ratRing.one, ratRing.zero_add]

/-- α は cg3PhiTop の根。 -/
theorem cg3_alpha_is_root : prcIsRoot cnfPhi3F268 cg3PhiTop cg3Alpha :=
  cg3_root_of_phi cg3Alpha cg3_alpha_root

/-- β は cg3PhiTop の根。 -/
theorem cg3_beta_is_root : prcIsRoot cnfPhi3F268 cg3PhiTop cg3Beta :=
  cg3_root_of_phi cg3Beta cg3_beta_root

/-- **σ(α) は Φ₃ の根**（Φ₃(σα) = σ(Φ₃(α)) = σ(0) = 0）。 -/
theorem cg3_sigma_alpha_root (σ : FieldAut cnfPhi3Field)
    (hσ : (galoisSubgroup cnfExt3).mem σ) :
    prcIsRoot cnfPhi3F268 cg3PhiTop (σ.toFun cg3Alpha) := by
  apply cg3_root_of_phi (σ.toFun cg3Alpha)
  have key : σ.toFun (cnfPhi3Field.add (cnfPhi3Field.add
      (cnfPhi3Field.mul cg3Alpha cg3Alpha) cg3Alpha) cnfPhi3Field.one)
      = σ.toFun cnfPhi3Field.zero := congrArg σ.toFun cg3_alpha_root
  rw [σ.map_add, σ.map_add, σ.map_mul, σ.map_one, FieldAut.map_zero σ] at key
  exact key

/-- 担体の等値判定（構成的）。 -/
theorem cg3_carrier_dec (x y : GefNF cq0PS 2) : x = y ∨ x ≠ y := by
  cases cg3q_eq_dec (x.val 0) (y.val 0) with
  | inr h0 => exact Or.inr (fun he => h0 (congrArg (fun z : GefNF cq0PS 2 => z.val 0) he))
  | inl h0 =>
    cases cg3q_eq_dec (x.val 1) (y.val 1) with
    | inl h1 => exact Or.inl (cg3_carrier_ext x y h0 h1)
    | inr h1 => exact Or.inr (fun he => h1 (congrArg (fun z : GefNF cq0PS 2 => z.val 1) he))

/-- **G4 根の二分法** — cg3PhiTop（deg 2）の根は α か β のみ。r ≠ α ∧ r ≠ β なら
    [r, α, β] は相異なる 3 根で `prc_roots_le_degree`（≤ 2）に矛盾。 -/
theorem cg3_root_dichotomy (r : GefNF cq0PS 2)
    (hr : prcIsRoot cnfPhi3F268 cg3PhiTop r) : r = cg3Alpha ∨ r = cg3Beta := by
  cases cg3_carrier_dec r cg3Alpha with
  | inl hα => exact Or.inl hα
  | inr hα =>
    cases cg3_carrier_dec r cg3Beta with
    | inl hβ => exact Or.inr hβ
    | inr hβ =>
      exfalso
      have hroots : ∀ z ∈ [r, cg3Alpha, cg3Beta], prcIsRoot cnfPhi3F268 cg3PhiTop z := by
        intro z hz
        cases hz with
        | head => exact hr
        | tail _ hz2 =>
          cases hz2 with
          | head => exact cg3_alpha_is_root
          | tail _ hz3 =>
            cases hz3 with
            | head => exact cg3_beta_is_root
            | tail _ hz4 => cases hz4
      have hdistinct : prcDistinct [r, cg3Alpha, cg3Beta] := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro x hx
          cases hx with
          | head => exact fun he => hα he.symm
          | tail _ hx2 =>
            cases hx2 with
            | head => exact fun he => hβ he.symm
            | tail _ hx3 => cases hx3
        · intro x hx
          cases hx with
          | head => exact fun he => cg3Alpha_ne_beta he.symm
          | tail _ hx2 => cases hx2
        · intro x hx; cases hx
        · exact True.intro
      have hlen : ([r, cg3Alpha, cg3Beta]).length ≤ 2 :=
        prc_roots_le_degree cnfPhi3F268 2 cg3PhiTop cg3PhiTop_bound
          (by rw [cg3PhiTop_2]
              exact gnf_zero_ne_one cq0PS 2 cq0_bound cq0_lead cnf_one_le_two)
          [r, cg3Alpha, cg3Beta] hroots hdistinct
      have h3le : (3 : Nat) ≤ 2 := hlen
      omega

/-! ## CG3-8(G5): capstone — Gal(ℚ(ζ₃)/ℚ) は位数ちょうど 2 -/

/-- **G5（本丸）: Gal(ℚ(ζ₃)/ℚ) は位数ちょうど 2** — 単位元と異なる元 g（共役 σ₁）が
    存在し、すべての元は単位元か g。σ の像 σ(α) は Φ₃ の根（α か β）で、決定補題
    `cg3_aut_ext` により σ は id か σ₁ に確定する。honest 仮説 0 本。 -/
theorem cg3_galois_order_two :
    ∃ g : (galoisGroupGrp cnfExt3).carrier,
      g ≠ (galoisGroupGrp cnfExt3).one ∧
      ∀ h : (galoisGroupGrp cnfExt3).carrier,
        h = (galoisGroupGrp cnfExt3).one ∨ h = g := by
  refine ⟨⟨cg3Conj, cg3Conj_mem⟩, ?_, ?_⟩
  · intro hg
    have h1 : cg3Conj = fieldAutId cnfPhi3Field := congrArg Subtype.val hg
    exact cg3Conj_ne_id h1
  · intro g'
    have hσroot : prcIsRoot cnfPhi3F268 cg3PhiTop (g'.val.toFun cg3Alpha) :=
      cg3_sigma_alpha_root g'.val g'.property
    cases cg3_root_dichotomy (g'.val.toFun cg3Alpha) hσroot with
    | inl hα =>
      apply Or.inl
      apply Subtype.ext
      apply cg3_aut_ext g'.val (fieldAutId cnfPhi3Field) g'.property
        (galoisSubgroup cnfExt3).one_mem
      show g'.val.toFun cg3Alpha = (fieldAutId cnfPhi3Field).toFun cg3Alpha
      exact hα
    | inr hβ =>
      apply Or.inr
      apply Subtype.ext
      apply cg3_aut_ext g'.val cg3Conj g'.property cg3Conj_mem
      show g'.val.toFun cg3Alpha = cg3Conj.toFun cg3Alpha
      rw [show cg3Conj.toFun cg3Alpha = cg3ConjFun cg3Alpha from rfl, cg3_conj_alpha]
      exact hβ

end IUT
