/-
  IUT/CyclotomicGal9.lean — A3/CG9（Gal(ℚ(ζ₉)/ℚ) の位数ちょうど 6 の完全決定・
  CG3 の degree-6 スケールアップ）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・
     実円分体 ℚ(ζ₉) = ℚ[x]/(Φ_9)（gefNF 担体・degree 6）の上で、非自明 Galois
     群 Gal(ℚ(ζ₉)/ℚ) を **位数ちょうど 6**——冪代入自己同型 σ_a: x̄₉ ↦ x̄₉^a,
     a ∈ (ℤ/9)^× = {1,2,4,5,7,8}——と完全決定する。honest 仮説 0 本・sorry 皆無・
     新規 Classical.choice 皆無（全主要 def/thm の #print axioms = [propext,
     Quot.sound]）。CG3 の位数 2 を degree 6 に写経・拡張したもの）。

  complete_pct 影響: A3（円分塔 Gal の完全決定・res₁ 全射性の前提）——
  Gal(ℚ(ζ₉)/ℚ) の 6 元を本物に構成・列挙し、2 段塔の上位 Gal を確定する。
  従来 CR39（res: Gal(ℚ(ζ₉)/ℚ)→Gal(ℚ(ζ₃)/ℚ)）は上位 Gal の「元が実際に存在
  すること」を σ_a として持たず res の domain を仮に扱っていたが、本ファイルで
  上位 Gal の 6 元を本物の体自己同型として構成し、res の全射性議論の domain を
  discharge する。本ファイル単体では complete_pct 未設定（res 全射性まで束ねた
  時点で独立監査に諮る）。

  段分解:
   * (S1) Φ_9(x̄₉)=0 の本物化 `cg9_rel1/rel2`（1+x̄₉³+x̄₉⁶=0・x̄₉⁶ の reduced 値
     `cg9_pow6_val`）と根事実 `cg9_root`（3∤a で Φ_9(x̄₉^a)=0・`cg9_evalPhi`）。
   * (S2) 冪代入自己同型 σ_a `cg9Subst`（評価準同型 evalSum で構成）・環準同型性
     `cg9Subst_add`/`cg9Subst_one`/**`cg9Subst_mul`（★山場・根での簡約消去
     `cg9_eval_hphi` ＋ evalHom_mul）**・両側逆 `cg9_subst_left_inv`（分解
     `cg9_decompose` ＋ 冪保存 `cg9_subst_pow` ＋ 指数逆元 `cg9_pow_inv_exp`）で
     本物の体自己同型 `cg9Aut` へ・ℚ 各点固定 `cg9Aut_mem`。
   * (S3) 決定補題 `cg9_aut_ext`（σ は σ(x̄₉) で決まる・n 項分解の写経）。
   * (S4) capstone `cg9_galois_order_six`（Gal の元は ちょうど 6 個・列挙リストに
     全て属し相異・任意 g は cr39Char g で σ_a に確定）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・ℚ 上・円分塔 2 段目（ℚ(ζ₉)）のみの忠実な部分ケース。
   (ii)  **群同型 Gal(ℚ(ζ₉)/ℚ) ≅ (ℤ/9)^× は未証明**。本ファイルは「位数ちょうど
         6」・6 元の本物構成・列挙・相異まで（cg9Aut の合成が (ℤ/9)^× の積に
         対応することは未形式化）。無限塔・逆極限 G_K は未達。
   (iii) `cg9Aut a a'` は **逆元 a'（a·a'≡1 mod 9）を明示 witness として受け取る**
         設計（core FieldAut は明示 invFun を要するため）。逆元の存在自体は
         (ℤ/9)^× の群性で自明だが、その群論を本ファイルには含めない。
   (iv)  res 全射性・分離性・正規性の一般論は未形式化（M4 以降）。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/
  dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.CyclotomicRes39
import IUT.CyclotomicEmbed39

namespace IUT

/-- constant embedding RingHom ℚ → K = ℚ(ζ_9). -/
def cg9Iota : RingHom ratRing cm9R where
  map := gefIncl cpdPhi9 6 (by omega)
  map_add := fun x y => Subtype.ext ((psConstHom ratRing).map_add x y)
  map_mul := fun x y => by
    apply Subtype.ext
    show psC ratRing (ratRing.mul x y)
        = pfdRed cpdPhi9 6 6 (psMul ratRing (psC ratRing x) (psC ratRing y))
    have hmm : psMul ratRing (psC ratRing x) (psC ratRing y)
        = psC ratRing (ratRing.mul x y) := ((psConstHom ratRing).map_mul x y).symm
    rw [hmm]
    have hbc : IsPolyBounded ratRing (psC ratRing (ratRing.mul x y)) 6 := by
      intro j hj
      show (if j = 0 then ratRing.mul x y else ratRing.zero) = ratRing.zero
      exact if_neg (by omega)
    funext j
    exact (pfdRed_of_bounded cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead 6
      (psC ratRing (ratRing.mul x y)) hbc j).symm
  map_one := Subtype.ext (psConstHom ratRing).map_one

/-- substitution map σ_a : y ↦ ev_{x̄₉^a}(y). -/
def cg9Subst (a : Nat) (y : GefNF cpdPhi9 6) : GefNF cpdPhi9 6 :=
  evalSum cg9Iota (cm9Pow a) y.val 6

/-! ## additivity / unit -/

/-- **additivity** σ_a(y+z) = σ_a(y)+σ_a(z). -/
theorem cg9Subst_add (a : Nat) (y z : GefNF cpdPhi9 6) :
    cg9Subst a (cm9R.add y z) = cm9R.add (cg9Subst a y) (cg9Subst a z) :=
  evalHom_add cg9Iota (cm9Pow a) y.val z.val 6

/-- **unit** σ_a(1) = 1. -/
theorem cg9Subst_one (a : Nat) : cg9Subst a cm9R.one = cm9R.one := by
  show evalSum cg9Iota (cm9Pow a) (psOne ratRing) 6 = cm9R.one
  rw [evalHom_stable cg9Iota (cm9Pow a) (psOne ratRing) 1
    (fun j hj => if_neg (by omega)) 6 (by omega)]
  exact evalHom_one cg9Iota (cm9Pow a)

/-! ## Φ_9(x̄₉)=0 relation: 1 + x̄₉³ + x̄₉⁶ = 0 -/

/-- reduced value of x̄₉⁶ = −1 − x̄₉³ (deg < 6). -/
def cg9V6 : PS ratRing :=
  fun j => if j = 0 then ratRing.neg ratRing.one
           else if j = 3 then ratRing.neg ratRing.one else ratRing.zero

theorem cg9V6_bound : IsPolyBounded ratRing cg9V6 6 := by
  intro j hj
  show (if j = 0 then ratRing.neg ratRing.one
        else if j = 3 then ratRing.neg ratRing.one else ratRing.zero) = ratRing.zero
  rw [if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 3 by omega)]

/-- X⁶ ≡ cg9V6 (mod Φ_9): X⁶ − (−1−X³) = X⁶+X³+1 = Φ_9 = 1·Φ_9. -/
theorem cg9_x6_cong : gnfCong cpdPhi9 (psSingle ratRing ratRing.one 6) cg9V6 := by
  refine ⟨psOne ratRing, ⟨1, fun j hj => if_neg (by omega)⟩, ?_⟩
  funext j
  show ratRing.add (psSingle ratRing ratRing.one 6 j) (ratRing.neg (cg9V6 j))
    = psMul ratRing (psOne ratRing) cpdPhi9 j
  rw [show psMul ratRing (psOne ratRing) cpdPhi9 j = cpdPhi9 j
      from congrFun ((psRing ratRing).one_mul cpdPhi9) j]
  cases Nat.decEq j 0 with
  | isTrue h0 =>
    rw [show psSingle ratRing ratRing.one 6 j = ratRing.zero from if_neg (by omega),
      show cg9V6 j = ratRing.neg ratRing.one from if_pos h0,
      CRing.neg_neg ratRing ratRing.one, ratRing.zero_add, h0, cpdPhi9_0]
  | isFalse h0 =>
    cases Nat.decEq j 3 with
    | isTrue h3 =>
      rw [show psSingle ratRing ratRing.one 6 j = ratRing.zero from if_neg (by omega),
        show cg9V6 j = ratRing.neg ratRing.one
          from (if_neg h0).trans (if_pos h3),
        CRing.neg_neg ratRing ratRing.one, ratRing.zero_add, h3, cpdPhi9_3]
    | isFalse h3 =>
      cases Nat.decEq j 6 with
      | isTrue h6 =>
        rw [show psSingle ratRing ratRing.one 6 j = ratRing.one from if_pos h6,
          show cg9V6 j = ratRing.zero from (if_neg h0).trans (if_neg h3),
          CRing.neg_zero ratRing, CRing.add_zero ratRing, h6, cpdPhi9_6]
      | isFalse h6 =>
        rw [show psSingle ratRing ratRing.one 6 j = ratRing.zero from if_neg h6,
          show cg9V6 j = ratRing.zero from (if_neg h0).trans (if_neg h3),
          CRing.neg_zero ratRing, CRing.add_zero ratRing, cpdPhi9_other j h0 h3 h6]

/-- x̄₉⁶ の reduced value. -/
theorem cg9_pow6_val : (cm9Pow 6).val = cg9V6 :=
  cm9_nf_unique (cm9Pow 6).val cg9V6 (cm9Pow 6).property cg9V6_bound
    (gnfCong_trans cpdPhi9 (cm9_pow_cong 6) cg9_x6_cong)

/-- **fundamental relation 1**: 1 + x̄₉³ + x̄₉⁶ = 0. -/
theorem cg9_rel1 : cm9R.add (cm9R.add cm9R.one (cm9Pow 3)) (cm9Pow 6) = cm9R.zero := by
  apply Subtype.ext
  show psAdd ratRing (psAdd ratRing (psOne ratRing) (cm9Pow 3).val) (cm9Pow 6).val
    = psZero ratRing
  rw [cm9_pow_small 3 (by omega), cg9_pow6_val]
  funext j
  show ratRing.add (ratRing.add (psOne ratRing j) (psSingle ratRing ratRing.one 3 j)) (cg9V6 j)
    = ratRing.zero
  cases Nat.decEq j 0 with
  | isTrue h0 =>
    rw [show psOne ratRing j = ratRing.one from if_pos h0,
      show psSingle ratRing ratRing.one 3 j = ratRing.zero from if_neg (by omega),
      show cg9V6 j = ratRing.neg ratRing.one from if_pos h0,
      CRing.add_zero ratRing, ratRing.add_neg ratRing.one]
  | isFalse h0 =>
    cases Nat.decEq j 3 with
    | isTrue h3 =>
      rw [show psOne ratRing j = ratRing.zero from if_neg h0,
        show psSingle ratRing ratRing.one 3 j = ratRing.one from if_pos h3,
        show cg9V6 j = ratRing.neg ratRing.one from (if_neg h0).trans (if_pos h3),
        ratRing.zero_add, ratRing.add_neg ratRing.one]
    | isFalse h3 =>
      rw [show psOne ratRing j = ratRing.zero from if_neg h0,
        show psSingle ratRing ratRing.one 3 j = ratRing.zero from if_neg h3,
        show cg9V6 j = ratRing.zero from (if_neg h0).trans (if_neg h3),
        ratRing.zero_add, ratRing.zero_add]

/-- **fundamental relation 2** (reordered). -/
theorem cg9_rel2 : cm9R.add (cm9R.add cm9R.one (cm9Pow 6)) (cm9Pow 3) = cm9R.zero := by
  rw [cm9R.add_assoc cm9R.one (cm9Pow 6) (cm9Pow 3),
      cm9R.add_comm (cm9Pow 6) (cm9Pow 3),
      ← cm9R.add_assoc cm9R.one (cm9Pow 3) (cm9Pow 6)]
  exact cg9_rel1

/-! ## Φ_9(x̄₉^a) = 0 for 3∤a (root fact for map_mul) -/

/-- evaluation of Φ_9 at x̄₉^a: = 1 + x̄₉^{3a} + x̄₉^{6a}. -/
theorem cg9_evalPhi (a : Nat) :
    evalSum cg9Iota (cm9Pow a) cpdPhi9 7
      = cm9R.add (cm9R.add cm9R.one (cm9Pow (a * 3))) (cm9Pow (a * 6)) := by
  have hz : ∀ i, cpdPhi9 i = ratRing.zero →
      cm9R.mul (cg9Iota.map (cpdPhi9 i)) (rpow cm9R (cm9Pow a) i) = cm9R.zero := by
    intro i hi
    rw [hi, RingHom.map_zero cg9Iota, CRing.zero_mul cm9R]
  have g0 : cm9R.mul (cg9Iota.map (cpdPhi9 0)) (rpow cm9R (cm9Pow a) 0) = cm9R.one := by
    rw [cpdPhi9_0, cg9Iota.map_one]
    show cm9R.mul cm9R.one cm9R.one = cm9R.one
    exact cm9R.one_mul cm9R.one
  have g1 := hz 1 (cpdPhi9_other 1 (by omega) (by omega) (by omega))
  have g2 := hz 2 (cpdPhi9_other 2 (by omega) (by omega) (by omega))
  have g4 := hz 4 (cpdPhi9_other 4 (by omega) (by omega) (by omega))
  have g5 := hz 5 (cpdPhi9_other 5 (by omega) (by omega) (by omega))
  have g3 : cm9R.mul (cg9Iota.map (cpdPhi9 3)) (rpow cm9R (cm9Pow a) 3) = cm9Pow (a * 3) := by
    rw [cpdPhi9_3, cg9Iota.map_one, cm9R.one_mul]
    exact cm9r_rpow_cm9Pow a 3
  have g6 : cm9R.mul (cg9Iota.map (cpdPhi9 6)) (rpow cm9R (cm9Pow a) 6) = cm9Pow (a * 6) := by
    rw [cpdPhi9_6, cg9Iota.map_one, cm9R.one_mul]
    exact cm9r_rpow_cm9Pow a 6
  show cm9R.add (cm9R.add (cm9R.add (cm9R.add (cm9R.add (cm9R.add (cm9R.add cm9R.zero
      (cm9R.mul (cg9Iota.map (cpdPhi9 0)) (rpow cm9R (cm9Pow a) 0)))
      (cm9R.mul (cg9Iota.map (cpdPhi9 1)) (rpow cm9R (cm9Pow a) 1)))
      (cm9R.mul (cg9Iota.map (cpdPhi9 2)) (rpow cm9R (cm9Pow a) 2)))
      (cm9R.mul (cg9Iota.map (cpdPhi9 3)) (rpow cm9R (cm9Pow a) 3)))
      (cm9R.mul (cg9Iota.map (cpdPhi9 4)) (rpow cm9R (cm9Pow a) 4)))
      (cm9R.mul (cg9Iota.map (cpdPhi9 5)) (rpow cm9R (cm9Pow a) 5)))
      (cm9R.mul (cg9Iota.map (cpdPhi9 6)) (rpow cm9R (cm9Pow a) 6))
    = cm9R.add (cm9R.add cm9R.one (cm9Pow (a * 3))) (cm9Pow (a * 6))
  rw [g0, g1, g2, g3, g4, g5, g6, cm9R.zero_add,
    CRing.add_zero cm9R, CRing.add_zero cm9R, CRing.add_zero cm9R, CRing.add_zero cm9R]

/-- **root fact**: Φ_9(x̄₉^a) = 0 when 3∤a. -/
theorem cg9_root (a : Nat) (h3 : ¬ 3 ∣ a) :
    evalSum cg9Iota (cm9Pow a) cpdPhi9 7 = cm9R.zero := by
  rw [cg9_evalPhi a]
  have hmod : a % 3 = 1 ∨ a % 3 = 2 := by omega
  cases hmod with
  | inl h1 =>
    rw [show a * 3 = (a / 3) * 9 + 3 by omega, cm9_pow_period (a / 3) 3,
      show a * 6 = (2 * (a / 3)) * 9 + 6 by omega, cm9_pow_period (2 * (a / 3)) 6]
    exact cg9_rel1
  | inr h2 =>
    rw [show a * 3 = (a / 3) * 9 + 6 by omega, cm9_pow_period (a / 3) 6,
      show a * 6 = (2 * (a / 3) + 1) * 9 + 3 by omega, cm9_pow_period (2 * (a / 3) + 1) 3]
    exact cg9_rel2

/-- evaluation of a multiple of Φ_9 at the root x̄₉^a vanishes (3∤a). -/
theorem cg9_eval_hphi (a : Nat) (ha : ¬ 3 ∣ a) (h : PS ratRing) (Nh : Nat)
    (hhb : IsPolyBounded ratRing h Nh) (M : Nat) (hM : Nh + 7 + 1 ≤ M) :
    evalSum cg9Iota (cm9Pow a) (psMul ratRing h cpdPhi9) M = cm9R.zero := by
  have hb : IsPolyBounded ratRing (psMul ratRing h cpdPhi9) (Nh + 7) :=
    simpleExt_mul_bounded ratRing hhb cpdPhi9_bound
  have e1 : evalSum cg9Iota (cm9Pow a) (psMul ratRing h cpdPhi9) M
      = evalSum cg9Iota (cm9Pow a) (psMul ratRing h cpdPhi9) (Nh + 7) :=
    evalHom_stable cg9Iota (cm9Pow a) (psMul ratRing h cpdPhi9) (Nh + 7) hb M (by omega)
  have e2 : evalSum cg9Iota (cm9Pow a) (psMul ratRing h cpdPhi9) (Nh + 7 + 1)
      = evalSum cg9Iota (cm9Pow a) (psMul ratRing h cpdPhi9) (Nh + 7) :=
    evalHom_stable cg9Iota (cm9Pow a) (psMul ratRing h cpdPhi9) (Nh + 7) hb (Nh + 7 + 1) (by omega)
  have hmul := evalHom_mul cg9Iota (cm9Pow a) h cpdPhi9 Nh 7 hhb cpdPhi9_bound
  rw [e1, ← e2, hmul, cg9_root a ha, CRing.mul_zero cm9R]

/-! ## multiplicativity (★ the crux) -/

/-- **multiplicativity** σ_a(y·z) = σ_a(y)·σ_a(z) for 3∤a. Evaluation at the root
    x̄₉^a kills the Φ_9-reduction of the product; `evalHom_mul` closes the rest. -/
theorem cg9Subst_mul (a : Nat) (ha : ¬ 3 ∣ a) (y z : GefNF cpdPhi9 6) :
    cg9Subst a (cm9R.mul y z) = cm9R.mul (cg9Subst a y) (cg9Subst a z) := by
  have hwb : IsPolyBounded ratRing (psMul ratRing y.val z.val) (6 + 6) :=
    simpleExt_mul_bounded ratRing y.property z.property
  obtain ⟨h, ⟨Nh, hhb⟩, he⟩ :=
    gnfCong_red cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead 6 (psMul ratRing y.val z.val) hwb
  have heq2 : pfdRed cpdPhi9 6 6 (psMul ratRing y.val z.val)
      = psAdd ratRing (psMul ratRing y.val z.val) (psMul ratRing h cpdPhi9) := by
    funext j
    have hej : ratRing.add (pfdRed cpdPhi9 6 6 (psMul ratRing y.val z.val) j)
        (ratRing.neg (psMul ratRing y.val z.val j)) = psMul ratRing h cpdPhi9 j :=
      congrFun he j
    show pfdRed cpdPhi9 6 6 (psMul ratRing y.val z.val) j
      = ratRing.add (psMul ratRing y.val z.val j) (psMul ratRing h cpdPhi9 j)
    have key : ratRing.add (psMul ratRing y.val z.val j) (psMul ratRing h cpdPhi9 j)
        = pfdRed cpdPhi9 6 6 (psMul ratRing y.val z.val) j := by
      rw [← hej, ratRing.add_comm (pfdRed cpdPhi9 6 6 (psMul ratRing y.val z.val) j)
          (ratRing.neg (psMul ratRing y.val z.val j)),
        ← ratRing.add_assoc (psMul ratRing y.val z.val j)
          (ratRing.neg (psMul ratRing y.val z.val j))
          (pfdRed cpdPhi9 6 6 (psMul ratRing y.val z.val) j),
        ratRing.add_neg (psMul ratRing y.val z.val j), ratRing.zero_add]
    exact key.symm
  have hRHS : cm9R.mul (cg9Subst a y) (cg9Subst a z)
      = evalSum cg9Iota (cm9Pow a) (psMul ratRing y.val z.val) (6 + 6 + 1) :=
    (evalHom_mul cg9Iota (cm9Pow a) y.val z.val 6 6 y.property z.property).symm
  have hpf6 : IsPolyBounded ratRing
      (pfdRed cpdPhi9 6 6 (psMul ratRing y.val z.val)) 6 :=
    pfdRed_bound cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead 6 (psMul ratRing y.val z.val) hwb
  show evalSum cg9Iota (cm9Pow a)
      (pfdRed cpdPhi9 6 6 (psMul ratRing y.val z.val)) 6
    = cm9R.mul (cg9Subst a y) (cg9Subst a z)
  rw [hRHS,
    (evalHom_stable cg9Iota (cm9Pow a)
      (pfdRed cpdPhi9 6 6 (psMul ratRing y.val z.val)) 6 hpf6 (Nh + 20) (by omega)).symm,
    heq2,
    evalHom_add cg9Iota (cm9Pow a) (psMul ratRing y.val z.val)
      (psMul ratRing h cpdPhi9) (Nh + 20),
    cg9_eval_hphi a ha h Nh hhb (Nh + 20) (by omega), CRing.add_zero cm9R,
    evalHom_stable cg9Iota (cm9Pow a) (psMul ratRing y.val z.val) (6 + 6) hwb (Nh + 20) (by omega)]
  exact (evalHom_stable cg9Iota (cm9Pow a) (psMul ratRing y.val z.val) (6 + 6) hwb
    (6 + 6 + 1) (by omega)).symm

/-! ## zero / rsum distribution / ℚ fixed -/

/-- σ_a(0) = 0. -/
theorem cg9_subst_zero (a : Nat) : cg9Subst a cm9R.zero = cm9R.zero :=
  evalHom_zero cg9Iota (cm9Pow a) 6

/-- σ_a distributes over finite sums. -/
theorem cg9_subst_rsum (a : Nat) (g : Nat → cm9R.carrier) :
    ∀ n, cg9Subst a (rsum cm9R g n) = rsum cm9R (fun i => cg9Subst a (g i)) n := by
  intro n
  induction n with
  | zero => exact cg9_subst_zero a
  | succ n ih =>
    show cg9Subst a (cm9R.add (rsum cm9R g n) (g n))
      = cm9R.add (rsum cm9R (fun i => cg9Subst a (g i)) n) (cg9Subst a (g n))
    rw [cg9Subst_add a (rsum cm9R g n) (g n), ih]

/-- σ_a fixes ℚ (the constant embedding). -/
theorem cg9_subst_incl (a : Nat) (c : QRat) :
    cg9Subst a (cg9Iota.map c) = cg9Iota.map c := by
  show evalSum cg9Iota (cm9Pow a) (psC ratRing c) 6 = cg9Iota.map c
  rw [evalHom_stable cg9Iota (cm9Pow a) (psC ratRing c) 1
    (fun j hj => if_neg (by omega)) 6 (by omega)]
  exact evalHom_C cg9Iota (cm9Pow a) c

/-! ## decompose y = Σ_{i<6} incl(y.val i)·x̄₉^i -/

/-- coefficient of a basis term. -/
theorem cg9_inclPow_val (c : QRat) (i : Nat) (hi : i < 6) :
    (cm9R.mul (cg9Iota.map c) (cm9Pow i)).val = psSingle ratRing c i := by
  show pfdRed cpdPhi9 6 6 (psMul ratRing (psC ratRing c) (cm9Pow i).val) = psSingle ratRing c i
  rw [cm9_pow_small i hi]
  have hps : psMul ratRing (psC ratRing c) (psSingle ratRing ratRing.one i)
      = psSingle ratRing c i := by
    funext k
    rw [gefSmulCoeff c (psSingle ratRing ratRing.one i) k]
    show ratRing.mul c (psSingle ratRing ratRing.one i k) = psSingle ratRing c i k
    cases Nat.decEq k i with
    | isTrue hk =>
      rw [show psSingle ratRing ratRing.one i k = ratRing.one from if_pos hk,
        show psSingle ratRing c i k = c from if_pos hk, CRing.mul_one ratRing]
    | isFalse hk =>
      rw [show psSingle ratRing ratRing.one i k = ratRing.zero from if_neg hk,
        show psSingle ratRing c i k = ratRing.zero from if_neg hk, CRing.mul_zero ratRing]
  rw [hps]
  funext k
  exact pfdRed_of_bounded cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead 6 (psSingle ratRing c i)
    (fun m hm => if_neg (by omega)) k

/-- coefficientwise value of a ring sum (add is pointwise). -/
theorem cg9_rsum_val (g : Nat → cm9R.carrier) (j : Nat) :
    ∀ n, (rsum cm9R g n).val j = rsum ratRing (fun i => (g i).val j) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (cm9R.add (rsum cm9R g n) (g n)).val j
      = ratRing.add (rsum ratRing (fun i => (g i).val j) n) ((g n).val j)
    show ratRing.add ((rsum cm9R g n).val j) ((g n).val j)
      = ratRing.add (rsum ratRing (fun i => (g i).val j) n) ((g n).val j)
    rw [ih]

/-- **decompose**: y = Σ_{i<6} incl(y.val i)·x̄₉^i. -/
theorem cg9_decompose (y : GefNF cpdPhi9 6) :
    rsum cm9R (fun i => cm9R.mul (cg9Iota.map (y.val i)) (cm9Pow i)) 6 = y := by
  apply Subtype.ext
  funext j
  rw [cg9_rsum_val (fun i => cm9R.mul (cg9Iota.map (y.val i)) (cm9Pow i)) j 6,
    rsum_congr ratRing 6 (fun i hi =>
      congrFun (cg9_inclPow_val (y.val i) i hi) j)]
  cases Nat.lt_or_ge j 6 with
  | inl hj =>
    rw [rsum_single ratRing (fun i => psSingle ratRing (y.val i) i j) j 6 hj
      (fun i hi hij => by
        show psSingle ratRing (y.val i) i j = ratRing.zero
        exact if_neg (fun hh => hij hh.symm))]
    show psSingle ratRing (y.val j) j j = y.val j
    exact if_pos rfl
  | inr hj =>
    rw [rsum_congr ratRing 6 (fun i hi => by
      show psSingle ratRing (y.val i) i j = ratRing.zero
      exact if_neg (by omega)), rsum_const_zero ratRing 6]
    exact (y.property j hj).symm

/-- rpow over cm9R agrees with cm9Pow multiplication. -/
theorem cg9_rpow_pow (a i : Nat) : rpow cm9R (cm9Pow a) i = cm9Pow (a * i) :=
  cm9r_rpow_cm9Pow a i

/-! ## generator power: σ_a(x̄₉^i) = x̄₉^{a·i} -/

/-- σ_a(x̄₉) = x̄₉^a. -/
theorem cg9_subst_zeta (a : Nat) : cg9Subst a cm9Zeta = cm9Pow a := by
  show rsum cm9R (fun k => cm9R.mul (cg9Iota.map (psSingle ratRing ratRing.one 1 k))
      (rpow cm9R (cm9Pow a) k)) 6 = cm9Pow a
  rw [rsum_single cm9R _ 1 6 (by omega) (fun j hj hjne => by
    show cm9R.mul (cg9Iota.map (psSingle ratRing ratRing.one 1 j)) (rpow cm9R (cm9Pow a) j)
      = cm9R.zero
    rw [show psSingle ratRing ratRing.one 1 j = ratRing.zero from if_neg hjne,
      RingHom.map_zero cg9Iota, CRing.zero_mul cm9R])]
  show cm9R.mul (cg9Iota.map (psSingle ratRing ratRing.one 1 1)) (rpow cm9R (cm9Pow a) 1) = cm9Pow a
  rw [show psSingle ratRing ratRing.one 1 1 = ratRing.one from if_pos rfl, cg9Iota.map_one,
    cm9R.one_mul]
  show cm9R.mul cm9R.one (cm9Pow a) = cm9Pow a
  exact cm9R.one_mul (cm9Pow a)

/-- σ_a(x̄₉^i) = x̄₉^{a·i} for all i. -/
theorem cg9_subst_pow (a : Nat) (ha : ¬ 3 ∣ a) :
    ∀ i, cg9Subst a (cm9Pow i) = cm9Pow (a * i) := by
  intro i
  induction i with
  | zero =>
    show cg9Subst a cm9R.one = cm9Pow (a * 0)
    rw [cg9Subst_one, Nat.mul_zero]
    rfl
  | succ i ih =>
    show cg9Subst a (cm9R.mul (cm9Pow i) cm9Zeta) = cm9Pow (a * (i + 1))
    rw [cg9Subst_mul a ha (cm9Pow i) cm9Zeta, ih, cg9_subst_zeta a,
      Nat.mul_succ a i, cm9Pow_add (a * i) a]

/-! ## periodicity and inverse exponent -/

/-- x̄₉^n depends only on n mod 9. -/
theorem cg9_pow_mod (n : Nat) : cm9Pow n = cm9Pow (n % 9) := by
  have h : cm9Pow ((n / 9) * 9 + n % 9) = cm9Pow (n % 9) := cm9_pow_period (n / 9) (n % 9)
  rw [show (n / 9) * 9 + n % 9 = n from by omega] at h
  exact h

/-- a·a' ≡ 1 (mod 9) ⟹ x̄₉^{a'·(a·i)} = x̄₉^i. -/
theorem cg9_pow_inv_exp (a a' i : Nat) (haa' : a * a' % 9 = 1) :
    cm9Pow (a' * (a * i)) = cm9Pow i := by
  have h1 : a' * (a * i) = a * a' * i := by rw [← Nat.mul_assoc, Nat.mul_comm a' a]
  rw [h1]
  have hmod : (a * a' * i) % 9 = i % 9 := by
    rw [Nat.mul_mod (a * a') i, haa', Nat.one_mul]
    omega
  rw [cg9_pow_mod (a * a' * i), hmod, ← cg9_pow_mod i]

/-! ## two-sided inverse -/

/-- **left inverse**: σ_{a'}(σ_a(y)) = y when a·a' ≡ 1 (mod 9). -/
theorem cg9_subst_left_inv (a a' : Nat) (_ha : ¬ 3 ∣ a) (ha' : ¬ 3 ∣ a')
    (haa' : a * a' % 9 = 1) (y : GefNF cpdPhi9 6) :
    cg9Subst a' (cg9Subst a y) = y := by
  show cg9Subst a' (rsum cm9R
      (fun i => cm9R.mul (cg9Iota.map (y.val i)) (rpow cm9R (cm9Pow a) i)) 6) = y
  rw [cg9_subst_rsum a'
      (fun i => cm9R.mul (cg9Iota.map (y.val i)) (rpow cm9R (cm9Pow a) i)) 6,
    rsum_congr cm9R 6 (fun i hi => by
      show cg9Subst a' (cm9R.mul (cg9Iota.map (y.val i)) (rpow cm9R (cm9Pow a) i))
        = cm9R.mul (cg9Iota.map (y.val i)) (cm9Pow i)
      rw [cg9_rpow_pow a i,
        cg9Subst_mul a' ha' (cg9Iota.map (y.val i)) (cm9Pow (a * i)),
        cg9_subst_incl a' (y.val i), cg9_subst_pow a' ha' (a * i),
        cg9_pow_inv_exp a a' i haa'])]
  exact cg9_decompose y

/-! ## the automorphism σ_a and its Galois membership -/

/-- **σ_a is a field automorphism** of ℚ(ζ_9) (explicit inverse a' with a·a'≡1 mod 9). -/
def cg9Aut (a a' : Nat) (ha : ¬ 3 ∣ a) (ha' : ¬ 3 ∣ a') (haa' : a * a' % 9 = 1) :
    FieldAut p9iPhi9Field where
  toFun := cg9Subst a
  invFun := cg9Subst a'
  map_add := cg9Subst_add a
  map_mul := cg9Subst_mul a ha
  map_one := cg9Subst_one a
  left_inv := cg9_subst_left_inv a a' ha ha' haa'
  right_inv := cg9_subst_left_inv a' a ha' ha (by rw [Nat.mul_comm]; exact haa')

/-- **σ_a fixes ℚ**: cg9Aut a ∈ Gal(ℚ(ζ_9)/ℚ). -/
theorem cg9Aut_mem (a a' : Nat) (ha : ¬ 3 ∣ a) (ha' : ¬ 3 ∣ a') (haa' : a * a' % 9 = 1) :
    (galoisSubgroup p9iExt9).mem (cg9Aut a a' ha ha' haa') :=
  fun k => cg9_subst_incl a k

/-! ## S3: determination lemma (σ is fixed by its value on x̄₉) -/

/-- constant embedding of ℚ agrees with the extension inclusion. -/
theorem cg9_map_eq_incl (c : QRat) : cg9Iota.map c = p9iExt9.incl c := rfl

/-- a Galois automorphism distributes over finite sums. -/
theorem faut_rsum (σ : FieldAut p9iPhi9Field) (g : Nat → cm9R.carrier) :
    ∀ n, σ.toFun (rsum cm9R g n) = rsum cm9R (fun i => σ.toFun (g i)) n := by
  intro n
  induction n with
  | zero => exact FieldAut.map_zero σ
  | succ n ih =>
    show σ.toFun (p9iPhi9Field.add (rsum cm9R g n) (g n))
      = cm9R.add (rsum cm9R (fun i => σ.toFun (g i)) n) (σ.toFun (g n))
    rw [σ.map_add (rsum cm9R g n) (g n), ih]
    rfl

/-- **determination**: two ℚ-fixing automorphisms agreeing on x̄₉ are equal. -/
theorem cg9_aut_ext (σ τ : FieldAut p9iPhi9Field)
    (hσ : (galoisSubgroup p9iExt9).mem σ) (hτ : (galoisSubgroup p9iExt9).mem τ)
    (h : σ.toFun cm9Zeta = τ.toFun cm9Zeta) : σ = τ := by
  have htofun : ∀ y, σ.toFun y = τ.toFun y := by
    intro y
    rw [← cg9_decompose y, faut_rsum σ _ 6, faut_rsum τ _ 6]
    apply rsum_congr cm9R 6
    intro i hi
    show σ.toFun (p9iPhi9Field.mul (cg9Iota.map (y.val i)) (cm9Pow i))
      = τ.toFun (p9iPhi9Field.mul (cg9Iota.map (y.val i)) (cm9Pow i))
    rw [σ.map_mul, τ.map_mul, cg9_map_eq_incl (y.val i), hσ (y.val i), hτ (y.val i),
      ← cr39_rpow_zeta i, ← cr39_rpow_hom σ cm9Zeta i, ← cr39_rpow_hom τ cm9Zeta i, h]
  apply FieldAut.ext
  · funext y; exact htofun y
  · funext x
    have h1 : σ.toFun (σ.invFun x) = x := σ.right_inv x
    have h2 : τ.toFun (σ.invFun x) = x := by rw [← htofun (σ.invFun x)]; exact h1
    have h3 : τ.invFun (τ.toFun (σ.invFun x)) = σ.invFun x := τ.left_inv (σ.invFun x)
    rw [h2] at h3
    exact h3.symm

/-! ## S4: Gal(ℚ(ζ_9)/ℚ) has exactly 6 elements -/

/-- ¬3∣n facts. -/
theorem cg9nd1 : ¬ (3 : Nat) ∣ 1 := by intro h; obtain ⟨k, hk⟩ := h; omega
theorem cg9nd2 : ¬ (3 : Nat) ∣ 2 := by intro h; obtain ⟨k, hk⟩ := h; omega
theorem cg9nd4 : ¬ (3 : Nat) ∣ 4 := by intro h; obtain ⟨k, hk⟩ := h; omega
theorem cg9nd5 : ¬ (3 : Nat) ∣ 5 := by intro h; obtain ⟨k, hk⟩ := h; omega
theorem cg9nd7 : ¬ (3 : Nat) ∣ 7 := by intro h; obtain ⟨k, hk⟩ := h; omega
theorem cg9nd8 : ¬ (3 : Nat) ∣ 8 := by intro h; obtain ⟨k, hk⟩ := h; omega

/-- a Galois-group element from σ_a. -/
def cg9Elt (a a' : Nat) (ha : ¬ 3 ∣ a) (ha' : ¬ 3 ∣ a') (haa' : a * a' % 9 = 1) :
    (galoisGroupGrp p9iExt9).carrier :=
  ⟨cg9Aut a a' ha ha' haa', cg9Aut_mem a a' ha ha' haa'⟩

/-- distinct exponents give distinct automorphisms. -/
theorem cg9Elt_ne {a a' b b' : Nat} {ha : ¬ 3 ∣ a} {ha' : ¬ 3 ∣ a'} {haa' : a * a' % 9 = 1}
    {hb : ¬ 3 ∣ b} {hb' : ¬ 3 ∣ b'} {hbb' : b * b' % 9 = 1}
    (ha9 : a < 9) (hb9 : b < 9) (hab : a ≠ b) :
    cg9Elt a a' ha ha' haa' ≠ cg9Elt b b' hb hb' hbb' := by
  intro he
  have hval : cg9Aut a a' ha ha' haa' = cg9Aut b b' hb hb' hbb' := congrArg Subtype.val he
  have hv : cg9Subst a cm9Zeta = cg9Subst b cm9Zeta :=
    congrArg (fun σ : FieldAut p9iPhi9Field => σ.toFun cm9Zeta) hval
  rw [cg9_subst_zeta a, cg9_subst_zeta b] at hv
  exact cm9_powers_distinct a b ha9 hb9 hab hv

/-- every g ∈ Gal equals σ_a for a = cr39Char(g). -/
theorem cg9_eq_aut (g : (galoisGroupGrp p9iExt9).carrier) (a a' : Nat)
    (ha : ¬ 3 ∣ a) (ha' : ¬ 3 ∣ a') (haa' : a * a' % 9 = 1)
    (hb : cr39Char g.val = a) :
    g = cg9Elt a a' ha ha' haa' := by
  apply Subtype.ext
  apply cg9_aut_ext g.val (cg9Aut a a' ha ha' haa') g.property (cg9Aut_mem a a' ha ha' haa')
  show g.val.toFun cm9Zeta = cg9Subst a cm9Zeta
  rw [cr39_char_spec g.val, hb, cg9_subst_zeta a]

/-- **capstone (S4)**: Gal(ℚ(ζ_9)/ℚ) is exactly the 6 automorphisms σ_a, a ∈ {1,2,4,5,7,8}:
    a list of length 6, pairwise distinct, containing every element of the group. -/
theorem cg9_galois_order_six :
    ∃ L : List (galoisGroupGrp p9iExt9).carrier,
      L.length = 6 ∧ prcDistinct L ∧
      ∀ g : (galoisGroupGrp p9iExt9).carrier, g ∈ L := by
  refine ⟨[cg9Elt 1 1 cg9nd1 cg9nd1 rfl, cg9Elt 2 5 cg9nd2 cg9nd5 rfl,
    cg9Elt 4 7 cg9nd4 cg9nd7 rfl, cg9Elt 5 2 cg9nd5 cg9nd2 rfl,
    cg9Elt 7 4 cg9nd7 cg9nd4 rfl, cg9Elt 8 8 cg9nd8 cg9nd8 rfl], rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      cases List.mem_cons.mp hx with
      | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
      | inr h1 => cases List.mem_cons.mp h1 with
        | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
        | inr h2 => cases List.mem_cons.mp h2 with
          | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
          | inr h3 => cases List.mem_cons.mp h3 with
            | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
            | inr h4 => cases List.mem_cons.mp h4 with
              | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
              | inr h5 => exact absurd h5 List.not_mem_nil
    · intro x hx
      cases List.mem_cons.mp hx with
      | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
      | inr h1 => cases List.mem_cons.mp h1 with
        | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
        | inr h2 => cases List.mem_cons.mp h2 with
          | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
          | inr h3 => cases List.mem_cons.mp h3 with
            | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
            | inr h4 => exact absurd h4 List.not_mem_nil
    · intro x hx
      cases List.mem_cons.mp hx with
      | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
      | inr h1 => cases List.mem_cons.mp h1 with
        | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
        | inr h2 => cases List.mem_cons.mp h2 with
          | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
          | inr h3 => exact absurd h3 List.not_mem_nil
    · intro x hx
      cases List.mem_cons.mp hx with
      | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
      | inr h1 => cases List.mem_cons.mp h1 with
        | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
        | inr h2 => exact absurd h2 List.not_mem_nil
    · intro x hx
      cases List.mem_cons.mp hx with
      | inl h => rw [h]; exact cg9Elt_ne (by omega) (by omega) (by omega)
      | inr h1 => exact absurd h1 List.not_mem_nil
    · exact ⟨fun x hx => absurd hx List.not_mem_nil, True.intro⟩
  · intro g
    have hlt : cr39Char g.val < 9 := cr39_char_lt g.val
    have hnd : ¬ 3 ∣ cr39Char g.val := cr39_char_not_dvd3 g.val
    have hcase : cr39Char g.val = 1 ∨ cr39Char g.val = 2 ∨ cr39Char g.val = 4 ∨
        cr39Char g.val = 5 ∨ cr39Char g.val = 7 ∨ cr39Char g.val = 8 := by omega
    cases hcase with
    | inl h => rw [cg9_eq_aut g 1 1 cg9nd1 cg9nd1 rfl h]; exact List.Mem.head _
    | inr h1 => cases h1 with
      | inl h => rw [cg9_eq_aut g 2 5 cg9nd2 cg9nd5 rfl h]
                 exact List.Mem.tail _ (List.Mem.head _)
      | inr h2 => cases h2 with
        | inl h => rw [cg9_eq_aut g 4 7 cg9nd4 cg9nd7 rfl h]
                   exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
        | inr h3 => cases h3 with
          | inl h => rw [cg9_eq_aut g 5 2 cg9nd5 cg9nd2 rfl h]
                     exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
          | inr h4 => cases h4 with
            | inl h => rw [cg9_eq_aut g 7 4 cg9nd7 cg9nd4 rfl h]
                       exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
                         (List.Mem.tail _ (List.Mem.head _))))
            | inr h => rw [cg9_eq_aut g 8 8 cg9nd8 cg9nd8 rfl h]
                       exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
                         (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))


end IUT
