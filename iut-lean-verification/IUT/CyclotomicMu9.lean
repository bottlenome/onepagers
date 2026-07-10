/-
  IUT/CyclotomicMu9.lean — W-C/CM9（設計 audit/A3-cyclotomic-tower-detail-2026-07-09.md
  §2.2 CM9）: ℚ(ζ_9) = ℚ[x]/(Φ_9) の 9 乗根群 μ_9(K₂) = ⟨x̄₉⟩（位数 9 の巡回群）

  ── 分類 **[実／本物建設(b)]**（本物の先行建設。実 NF 担体 `GefNF cpdPhi9 6`
     ＝ ℚ(ζ_9) の第二表示の上で、生成元 x̄₉ = X̄ が 1 の原始 9 乗根であること
     ——x̄₉⁹ = 1・x̄₉³ ≠ 1・位数ちょうど 9・冪 9 個相異——を core Lean のみで
     choice-free に本物に証明する。骨格・模型・代理・toy 主語なし）。

  **complete_pct 影響**: A3（円分塔 res₁ = CR39）への承認済み足場(c)。
  μ_9(ℚ(ζ_9)) = ⟨x̄₉⟩（位数 9 の巡回群）を本物に確立し、制限準同型 res の
  指標 a（σ(x̄₉) = x̄₉^a）抽出の土台を与える。本ファイル単体では
  complete_pct 未設定（W-C 完了＝CR39 で反映・独立監査確定）。

  内容（設計 §2.2 CM9）:
   * `cm9Zeta`             — x̄₉ = 単項式 X̄ の NF 担体元（gefNFMon）。
   * `cm9_factor`          — **x⁹ − 1 = Φ_9·(x³ − 1)**（具体 10 係数の Cauchy 照合・
     一般 ctp_pow_sub_one の代替）。商で x̄₉⁹ = 1 の核。
   * `cm9_pow_cong`        — x̄₉^k ≡ X^k (mod Φ_9)（合同代数 gnfCong の k 帰納）。
   * `cm9_nf_unique`       — NF 代表の一意性（合同 + 6 有界 ⟹ 等値）。
   * `cm9_zeta_pow9`       — **x̄₉⁹ = 1**（cm9_factor の商 + NF 一意性）。
   * `cm9_zeta_pow3_ne_one`— **x̄₉³ ≠ 1**（deg 3 < 6 で簡約不要・X³ ≠ 1）。
   * `cm9Pow_add`          — 冪の準同型 x̄₉^{a+b} = x̄₉^a · x̄₉^b（b 帰納・mul_assoc）。
   * `cm9_pow_sub`         — x̄₉^a = 1 ∧ x̄₉^c = 1 ⟹ x̄₉^{c−a} = 1（one_mul）。
   * `cm9_order`           — **位数ちょうど 9**（x̄₉⁹ = 1 かつ 0 < k < 9 で x̄₉^k ≠ 1）。
   * `cm9_powers_distinct` — x̄₉^0,…,x̄₉^8 は相異（準同型 + 位数 9）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   - **本物**: 全定理は実 NF 担体 `GefNF cpdPhi9 6`（= p9iPhi9Field.carrier）上の
     本物の等式・不等式。模型・代理なし。cm9_factor は実 ℚ[X] の 10 係数一致。
   - **部分ケースであること（消さない）**: p = 3・円分塔 2 段目（ℚ(ζ_9)）の
     9 乗根群のみ。制限準同型 res の指標抽出本体（σ(x̄₉) = x̄₉^a の a・3∤a・
     compat・群準同型性）は CR39（W-C 本体）の射程であり本ファイルに含めない。
   - **未達（正直申告）**: `cm9_root_in_powers`（y⁹ = 1 ⟹ y ∈ 冪・prc_roots_le_degree
     の 10 根矛盾）と構成的抽出 `cm9Find`（a < 9 走査・rzd 等値判定）は本
     ラウンドの予算内で未完（多項式根の評価準同型接続と Bool 零判定器が泥）。
     骨格・sorry で塞がず、到達範囲（cm9_factor + x̄₉⁹=1 + 位数 9 + 冪相異）を
     成果とし、root_in_powers/cm9Find は「未達」と正直に報告する（親が引き継ぐ）。
   - x̄₉ が単元であること・逆元 x̄₉^{9−i} は cm9_zeta_pow9 の帰結で暗に使う
     （明示の逆元関数は gefNFInv・F6 にあり本ファイルでは冪の準同型で回避）。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/
  dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.Phi9Irreducible
import IUT.PolyRootCount
import IUT.GenExtBasisAlpha
import IUT.GenExtFieldInv

namespace IUT

/-! ## CM9-0: 法多項式 x³−1・x⁹−1 と有界性 -/

/-- **CM9-0a: x³ − 1** — 単項式 X³ と定数 −1 の和（Φ_9 の相棒因子）。 -/
def cm9X3m1 : PS ratRing :=
  psAdd ratRing (psSingle ratRing ratRing.one 3) (psC ratRing (ratRing.neg ratRing.one))

/-- **CM9-0b: x⁹ − 1** — 9 乗根の消去多項式。 -/
def cm9X9m1 : PS ratRing :=
  psAdd ratRing (psSingle ratRing ratRing.one 9) (psC ratRing (ratRing.neg ratRing.one))

/-- x³ − 1 は 4 有界（deg 3）。 -/
theorem cm9X3m1_bound : IsPolyBounded ratRing cm9X3m1 4 := by
  intro j hj
  show ratRing.add (psSingle ratRing ratRing.one 3 j)
      (psC ratRing (ratRing.neg ratRing.one) j) = ratRing.zero
  rw [show psSingle ratRing ratRing.one 3 j = ratRing.zero from if_neg (by omega),
    show psC ratRing (ratRing.neg ratRing.one) j = ratRing.zero from if_neg (by omega),
    ratRing.zero_add]

/-! ## CM9-1: Φ_9 の係数（nested-if 特徴付け・cm9_factor / 値計算の共通部品） -/

/-- **CM9-1: Φ_9 = x⁶+x³+1 の係数** — j = 0,3,6 で 1・他で 0。 -/
theorem cm9_phi9_val (j : Nat) :
    cpdPhi9 j = if j = 0 then ratRing.one
      else if j = 3 then ratRing.one
      else if j = 6 then ratRing.one else ratRing.zero := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 j)
      (psSingle ratRing ratRing.one 3 j)) (psC ratRing ratRing.one j) = _
  cases Nat.decEq j 0 with
  | isTrue h0 =>
    subst h0
    rw [show psSingle ratRing ratRing.one 6 0 = ratRing.zero from if_neg (by omega),
      show psSingle ratRing ratRing.one 3 0 = ratRing.zero from if_neg (by omega),
      show psC ratRing ratRing.one 0 = ratRing.one from if_pos rfl,
      ratRing.zero_add, ratRing.zero_add, if_pos (rfl : (0 : Nat) = 0)]
  | isFalse h0 =>
    cases Nat.decEq j 3 with
    | isTrue h3 =>
      subst h3
      rw [show psSingle ratRing ratRing.one 6 3 = ratRing.zero from if_neg (by omega),
        show psSingle ratRing ratRing.one 3 3 = ratRing.one from if_pos rfl,
        show psC ratRing ratRing.one 3 = ratRing.zero from if_neg (by omega),
        ratRing.zero_add, CRing.add_zero ratRing,
        if_neg (show ¬ (3 : Nat) = 0 by omega), if_pos (rfl : (3 : Nat) = 3)]
    | isFalse h3 =>
      cases Nat.decEq j 6 with
      | isTrue h6 =>
        subst h6
        rw [show psSingle ratRing ratRing.one 6 6 = ratRing.one from if_pos rfl,
          show psSingle ratRing ratRing.one 3 6 = ratRing.zero from if_neg (by omega),
          show psC ratRing ratRing.one 6 = ratRing.zero from if_neg (by omega),
          CRing.add_zero ratRing, CRing.add_zero ratRing,
          if_neg (show ¬ (6 : Nat) = 0 by omega), if_neg (show ¬ (6 : Nat) = 3 by omega),
          if_pos (rfl : (6 : Nat) = 6)]
      | isFalse h6 =>
        rw [show psSingle ratRing ratRing.one 6 j = ratRing.zero from if_neg (by omega),
          show psSingle ratRing ratRing.one 3 j = ratRing.zero from if_neg (by omega),
          show psC ratRing ratRing.one j = ratRing.zero from if_neg (by omega),
          ratRing.zero_add, ratRing.zero_add,
          if_neg h0, if_neg h3, if_neg h6]

/-! ## CM9-2: cm9_factor — x⁹ − 1 = Φ_9·(x³ − 1)（10 係数 Cauchy 照合） -/

/-- 畳み込み補題 L1: (Φ_9 · X³)_j = if 3 ≤ j then Φ_9(j−3) else 0。 -/
theorem cm9_L1 (j : Nat) :
    psMul ratRing cpdPhi9 (psSingle ratRing ratRing.one 3) j
      = if 3 ≤ j then cpdPhi9 (j - 3) else ratRing.zero := by
  have hc : psMul ratRing cpdPhi9 (psSingle ratRing ratRing.one 3)
      = psMul ratRing (psSingle ratRing ratRing.one 3) cpdPhi9 :=
    (psRing ratRing).mul_comm cpdPhi9 (psSingle ratRing ratRing.one 3)
  rw [congrFun hc j, psMul_single_coeff268 ratRing ratRing.one 3 cpdPhi9 j]
  cases Nat.lt_or_ge j 3 with
  | inl h => rw [if_neg (by omega), if_neg (by omega)]
  | inr h => rw [if_pos (by omega), if_pos (by omega), ratRing.one_mul (cpdPhi9 (j - 3))]

/-- 畳み込み補題 L2: (Φ_9 · (−1))_j = −Φ_9(j)。 -/
theorem cm9_L2 (j : Nat) :
    psMul ratRing cpdPhi9 (psC ratRing (ratRing.neg ratRing.one)) j
      = ratRing.neg (cpdPhi9 j) := by
  have hc : psMul ratRing cpdPhi9 (psC ratRing (ratRing.neg ratRing.one))
      = psMul ratRing (psC ratRing (ratRing.neg ratRing.one)) cpdPhi9 :=
    (psRing ratRing).mul_comm cpdPhi9 (psC ratRing (ratRing.neg ratRing.one))
  rw [congrFun hc j,
    psC_mul_coeff ratRing (ratRing.neg ratRing.one) cpdPhi9 j,
    CRing.neg_mul ratRing ratRing.one (cpdPhi9 j), ratRing.one_mul (cpdPhi9 j)]

/-- **CM9-2（本丸）: x⁹ − 1 = Φ_9·(x³ − 1)** — 具体 10 係数の Cauchy 照合。
    左分配で (Φ_9·X³) + (Φ_9·(−1)) に分け、L1・L2 と Φ_9 係数（cm9_phi9_val）で
    各 j 次を潰す（一般 ctp_pow_sub_one の代替・本コース最短）。 -/
theorem cm9_factor : cm9X9m1 = psMul ratRing cpdPhi9 cm9X3m1 := by
  funext j
  have hdist : psMul ratRing cpdPhi9 cm9X3m1 j
      = ratRing.add (psMul ratRing cpdPhi9 (psSingle ratRing ratRing.one 3) j)
          (psMul ratRing cpdPhi9 (psC ratRing (ratRing.neg ratRing.one)) j) :=
    congrFun ((psRing ratRing).left_distrib cpdPhi9
      (psSingle ratRing ratRing.one 3) (psC ratRing (ratRing.neg ratRing.one))) j
  rw [hdist, cm9_L1 j, cm9_L2 j]
  show ratRing.add (psSingle ratRing ratRing.one 9 j)
      (psC ratRing (ratRing.neg ratRing.one) j)
    = ratRing.add (if 3 ≤ j then cpdPhi9 (j - 3) else ratRing.zero)
        (ratRing.neg (cpdPhi9 j))
  cases Nat.decEq j 0 with
  | isTrue h0 =>
    subst h0
    rw [show psSingle ratRing ratRing.one 9 0 = ratRing.zero from if_neg (by omega),
      show psC ratRing (ratRing.neg ratRing.one) 0 = ratRing.neg ratRing.one from if_pos rfl,
      if_neg (show ¬ (3 ≤ 0) by omega), cm9_phi9_val 0, if_pos (rfl : (0 : Nat) = 0)]
  | isFalse h0 =>
    cases Nat.decEq j 3 with
    | isTrue h3 =>
      subst h3
      rw [show psSingle ratRing ratRing.one 9 3 = ratRing.zero from if_neg (by omega),
        show psC ratRing (ratRing.neg ratRing.one) 3 = ratRing.zero from if_neg (by omega),
        if_pos (show 3 ≤ 3 by omega), cm9_phi9_val 0, cm9_phi9_val 3,
        if_pos (rfl : (0 : Nat) = 0), if_neg (show ¬ (3 : Nat) = 0 by omega),
        if_pos (rfl : (3 : Nat) = 3)]
      show ratRing.add ratRing.zero ratRing.zero
        = ratRing.add ratRing.one (ratRing.neg ratRing.one)
      rw [ratRing.zero_add, CRing.add_neg ratRing]
    | isFalse h3 =>
      cases Nat.decEq j 6 with
      | isTrue h6 =>
        subst h6
        rw [show psSingle ratRing ratRing.one 9 6 = ratRing.zero from if_neg (by omega),
          show psC ratRing (ratRing.neg ratRing.one) 6 = ratRing.zero from if_neg (by omega),
          if_pos (show 3 ≤ 6 by omega), cm9_phi9_val 3, cm9_phi9_val 6,
          if_neg (show ¬ (3 : Nat) = 0 by omega), if_pos (rfl : (3 : Nat) = 3),
          if_neg (show ¬ (6 : Nat) = 0 by omega), if_neg (show ¬ (6 : Nat) = 3 by omega),
          if_pos (rfl : (6 : Nat) = 6)]
        show ratRing.add ratRing.zero ratRing.zero
          = ratRing.add ratRing.one (ratRing.neg ratRing.one)
        rw [ratRing.zero_add, CRing.add_neg ratRing]
      | isFalse h6 =>
        cases Nat.decEq j 9 with
        | isTrue h9 =>
          subst h9
          rw [show psSingle ratRing ratRing.one 9 9 = ratRing.one from if_pos rfl,
            show psC ratRing (ratRing.neg ratRing.one) 9 = ratRing.zero from if_neg (by omega),
            if_pos (show 3 ≤ 9 by omega), cm9_phi9_val 6, cm9_phi9_val 9,
            if_neg (show ¬ (6 : Nat) = 0 by omega), if_neg (show ¬ (6 : Nat) = 3 by omega),
            if_pos (rfl : (6 : Nat) = 6),
            if_neg (show ¬ (9 : Nat) = 0 by omega), if_neg (show ¬ (9 : Nat) = 3 by omega),
            if_neg (show ¬ (9 : Nat) = 6 by omega)]
          show ratRing.add ratRing.one ratRing.zero
            = ratRing.add ratRing.one (ratRing.neg ratRing.zero)
          rw [CRing.add_zero ratRing, CRing.neg_zero ratRing, CRing.add_zero ratRing]
        | isFalse h9 =>
          rw [show psSingle ratRing ratRing.one 9 j = ratRing.zero from if_neg (by omega),
            show psC ratRing (ratRing.neg ratRing.one) j = ratRing.zero from if_neg (by omega),
            cm9_phi9_val j, if_neg h0, if_neg h3, if_neg h6]
          cases Nat.lt_or_ge j 3 with
          | inl hlt =>
            rw [if_neg (show ¬ (3 ≤ j) by omega)]
            show ratRing.add ratRing.zero ratRing.zero
              = ratRing.add ratRing.zero (ratRing.neg ratRing.zero)
            rw [CRing.neg_zero ratRing]
          | inr hge =>
            rw [if_pos hge, cm9_phi9_val (j - 3),
              if_neg (show ¬ (j - 3 = 0) by omega),
              if_neg (show ¬ (j - 3 = 3) by omega),
              if_neg (show ¬ (j - 3 = 6) by omega)]
            show ratRing.add ratRing.zero ratRing.zero
              = ratRing.add ratRing.zero (ratRing.neg ratRing.zero)
            rw [CRing.neg_zero ratRing]

/-! ## CM9-3: 生成元 x̄₉・その冪・NF 環 -/

/-- NF 環 ℚ[x]/(Φ_9)（= p9iPhi9Field の担体環）。 -/
def cm9R : CRing := gefNFRing cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead (by omega)

/-- **CM9-3a: 生成元 x̄₉ = X̄** — 単項式 X の NF 担体元（deg 1 < 6 で簡約不要）。 -/
def cm9Zeta : GefNF cpdPhi9 6 := gefNFMon cpdPhi9 6 1 (by omega)

/-- **CM9-3b: x̄₉ の冪** x̄₉^k（NF 環の乗法の反復）。 -/
def cm9Pow (k : Nat) : GefNF cpdPhi9 6 :=
  gefNFPow cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead (by omega) cm9Zeta k

/-! ## CM9-4: x̄₉^k ≡ X^k (mod Φ_9)（合同代数の k 帰納） -/

/-- **CM9-4: 冪の合同** — x̄₉^k ≡ X^k (mod Φ_9)。k 帰納:
    x̄₉^{k+1} = pfdRed(x̄₉^k · X̄) ≡ x̄₉^k · X ≡ X^k · X = X^{k+1}（gnfCong の伝播）。 -/
theorem cm9_pow_cong (k : Nat) :
    gnfCong cpdPhi9 (cm9Pow k).val (psSingle ratRing ratRing.one k) := by
  induction k with
  | zero => exact gnfCong_of_eq cpdPhi9 (cm9Pow 0).val (psSingle ratRing ratRing.one 0) rfl
  | succ k ih =>
    show gnfCong cpdPhi9
      (pfdRed cpdPhi9 6 6 (psMul ratRing (cm9Pow k).val cm9Zeta.val))
      (psSingle ratRing ratRing.one (k + 1))
    have hred : gnfCong cpdPhi9
        (pfdRed cpdPhi9 6 6 (psMul ratRing (cm9Pow k).val cm9Zeta.val))
        (psMul ratRing (cm9Pow k).val cm9Zeta.val) :=
      gnfCong_red cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead 6
        (psMul ratRing (cm9Pow k).val cm9Zeta.val)
        (simpleExt_mul_bounded ratRing (cm9Pow k).property cm9Zeta.property)
    have hmr : gnfCong cpdPhi9
        (psMul ratRing (cm9Pow k).val cm9Zeta.val)
        (psMul ratRing (psSingle ratRing ratRing.one k) cm9Zeta.val) :=
      gnfCong_mul_right cpdPhi9 cm9Zeta.val ⟨6, cm9Zeta.property⟩ ih
    have hprodeq : psMul ratRing (psSingle ratRing ratRing.one k) cm9Zeta.val
        = psSingle ratRing ratRing.one (k + 1) := by
      funext j
      show psMul ratRing (psSingle ratRing ratRing.one k)
          (psSingle ratRing ratRing.one 1) j
        = psSingle ratRing ratRing.one (k + 1) j
      rw [gefSMS ratRing.one ratRing.one k 1 j, ratRing.one_mul ratRing.one]
    exact gnfCong_trans cpdPhi9 hred
      (gnfCong_trans cpdPhi9 hmr
        (gnfCong_of_eq cpdPhi9
          (psMul ratRing (psSingle ratRing ratRing.one k) cm9Zeta.val)
          (psSingle ratRing ratRing.one (k + 1)) hprodeq))

/-- **CM9-4b: NF 代表の一意性** — 6 有界の 2 元が Φ_9 を法として合同なら等しい
    （pfdRed_of_bounded ＝ 恒等 と pfdRed_char ＝ 一意特徴付けの合成）。 -/
theorem cm9_nf_unique (w v : PS ratRing) (hw : IsPolyBounded ratRing w 6)
    (hv : IsPolyBounded ratRing v 6) (hcong : gnfCong cpdPhi9 w v) : w = v := by
  obtain ⟨h, ⟨Nh, hhb⟩, hhe⟩ := hcong
  funext j
  have h1 : pfdRed cpdPhi9 6 6 w j = w j :=
    pfdRed_of_bounded cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead 6 w hw j
  have h2 : pfdRed cpdPhi9 6 6 w j = v j :=
    pfdRed_char cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead 6 w v
      (fun i hi => hw i (by omega)) hv ⟨h, Nh, hhb, fun k => congrFun hhe k⟩ j
  rw [← h1, h2]

/-! ## CM9-5: x̄₉⁹ = 1 と x̄₉³ ≠ 1 -/

/-- psOne は 6 有界。 -/
theorem cm9_one_bound : IsPolyBounded ratRing (psOne ratRing) 6 := by
  intro j hj
  show (if j = 0 then ratRing.one else ratRing.zero) = ratRing.zero
  exact if_neg (by omega)

/-- **CM9-5a: X⁹ ≡ 1 (mod Φ_9)** — cm9_factor の商（h = x³−1）。 -/
theorem cm9_x9_cong_one :
    gnfCong cpdPhi9 (psSingle ratRing ratRing.one 9) (psOne ratRing) := by
  refine ⟨cm9X3m1, ⟨4, cm9X3m1_bound⟩, ?_⟩
  show psAdd ratRing (psSingle ratRing ratRing.one 9) (psNeg ratRing (psOne ratRing))
    = psMul ratRing cm9X3m1 cpdPhi9
  have hneg : psNeg ratRing (psOne ratRing) = psC ratRing (ratRing.neg ratRing.one) := by
    funext n
    cases n with
    | zero => rfl
    | succ k =>
      show ratRing.neg ratRing.zero = ratRing.zero
      exact CRing.neg_zero ratRing
  rw [hneg]
  show cm9X9m1 = psMul ratRing cm9X3m1 cpdPhi9
  rw [cm9_factor]
  exact (psRing ratRing).mul_comm cpdPhi9 cm9X3m1

/-- **CM9-5b（本丸）: x̄₉⁹ = 1** — cm9_pow_cong 9（x̄₉⁹ ≡ X⁹）と cm9_x9_cong_one
    （X⁹ ≡ 1）の合成 + NF 一意性。 -/
theorem cm9_zeta_pow9 : cm9Pow 9 = cm9R.one := by
  apply Subtype.ext
  show (cm9Pow 9).val = psOne ratRing
  exact cm9_nf_unique (cm9Pow 9).val (psOne ratRing) (cm9Pow 9).property cm9_one_bound
    (gnfCong_trans cpdPhi9 (cm9_pow_cong 9) cm9_x9_cong_one)

/-- **CM9-5c: 小さい冪の値** — k < 6 で x̄₉^k = X^k（deg k < 6 で簡約不要）。 -/
theorem cm9_pow_small (k : Nat) (hk : k < 6) :
    (cm9Pow k).val = psSingle ratRing ratRing.one k :=
  cm9_nf_unique (cm9Pow k).val (psSingle ratRing ratRing.one k) (cm9Pow k).property
    (fun i hi => if_neg (by omega)) (cm9_pow_cong k)

/-- **CM9-5d: x̄₉³ ≠ 1** — x̄₉³ = X³（deg 3 < 6）で定数項でなく 3 次係数 1 ≠ 0。 -/
theorem cm9_zeta_pow3_ne_one : cm9Pow 3 ≠ cm9R.one := by
  intro h
  have hval : (cm9Pow 3).val = psOne ratRing :=
    congrArg (fun z : GefNF cpdPhi9 6 => z.val) h
  rw [cm9_pow_small 3 (by omega)] at hval
  have hc : psSingle ratRing ratRing.one 3 3 = psOne ratRing 3 := congrFun hval 3
  rw [show psSingle ratRing ratRing.one 3 3 = ratRing.one from if_pos rfl,
    show psOne ratRing 3 = ratRing.zero from if_neg (by omega)] at hc
  exact cbp_one_ne_zero hc

/-! ## CM9-6: 冪の準同型と位数ちょうど 9 -/

/-- **CM9-6a: 冪の準同型** — x̄₉^{a+b} = x̄₉^a · x̄₉^b（b 帰納・mul_assoc）。 -/
theorem cm9Pow_add (a b : Nat) :
    cm9Pow (a + b) = cm9R.mul (cm9Pow a) (cm9Pow b) := by
  induction b with
  | zero => exact (CRing.mul_one cm9R (cm9Pow a)).symm
  | succ b ih =>
    show cm9R.mul (cm9Pow (a + b)) cm9Zeta
      = cm9R.mul (cm9Pow a) (cm9R.mul (cm9Pow b) cm9Zeta)
    rw [ih]
    exact cm9R.mul_assoc (cm9Pow a) (cm9Pow b) cm9Zeta

/-- **CM9-6b: 冪の差** — x̄₉^a = 1 かつ x̄₉^c = 1（a ≤ c）⟹ x̄₉^{c−a} = 1
    （x̄₉^c = x̄₉^a · x̄₉^{c−a} = 1 · x̄₉^{c−a}）。 -/
theorem cm9_pow_sub (a c : Nat) (ha : cm9Pow a = cm9R.one)
    (hc : cm9Pow c = cm9R.one) (hac : a ≤ c) : cm9Pow (c - a) = cm9R.one := by
  have hca : a + (c - a) = c := by omega
  have hsplit : cm9Pow (a + (c - a)) = cm9R.mul (cm9Pow a) (cm9Pow (c - a)) :=
    cm9Pow_add a (c - a)
  rw [hca, ha, hc, cm9R.one_mul (cm9Pow (c - a))] at hsplit
  exact hsplit.symm

/-- **CM9-6c（本丸）: 位数ちょうど 9** — x̄₉⁹ = 1 かつ 0 < k < 9 で x̄₉^k ≠ 1。
    k < 6 は cm9_pow_small（X^k ≠ 1）、k = 6,7,8 は cm9_pow_sub で x̄₉^{9−k}
    （= x̄₉^{3,2,1} ≠ 1）へ落として矛盾（位数は 9 の約数で 3 でない ⟹ 9 の
    本質＝準同型による短絡・explicit 6,7,8 値の計算を回避）。 -/
theorem cm9_order :
    cm9Pow 9 = cm9R.one ∧ ∀ k, 0 < k → k < 9 → cm9Pow k ≠ cm9R.one := by
  refine ⟨cm9_zeta_pow9, ?_⟩
  intro k hk0 hk9 hpow
  cases Nat.lt_or_ge k 6 with
  | inl hlt =>
    have hone : (cm9Pow k).val = psOne ratRing :=
      congrArg (fun z : GefNF cpdPhi9 6 => z.val) hpow
    rw [cm9_pow_small k hlt] at hone
    have hc : psSingle ratRing ratRing.one k k = psOne ratRing k := congrFun hone k
    rw [show psSingle ratRing ratRing.one k k = ratRing.one from if_pos rfl,
      show psOne ratRing k = ratRing.zero from if_neg (by omega)] at hc
    exact cbp_one_ne_zero hc
  | inr hge =>
    have hsub : cm9Pow (9 - k) = cm9R.one :=
      cm9_pow_sub k 9 hpow cm9_zeta_pow9 (by omega)
    have hlt2 : 9 - k < 6 := by omega
    have hone : (cm9Pow (9 - k)).val = psOne ratRing :=
      congrArg (fun z : GefNF cpdPhi9 6 => z.val) hsub
    rw [cm9_pow_small (9 - k) hlt2] at hone
    have hc : psSingle ratRing ratRing.one (9 - k) (9 - k) = psOne ratRing (9 - k) :=
      congrFun hone (9 - k)
    rw [show psSingle ratRing ratRing.one (9 - k) (9 - k) = ratRing.one from if_pos rfl,
      show psOne ratRing (9 - k) = ratRing.zero from if_neg (by omega)] at hc
    exact cbp_one_ne_zero hc

/-- **CM9-6d: 冪 x̄₉^0,…,x̄₉^8 は相異** — x̄₉^p = x̄₉^q（p < q < 9）なら
    左から x̄₉^{9−p} を掛けて 1 = x̄₉^{q−p}（0 < q−p < 9）で位数 9 に矛盾。 -/
theorem cm9_powers_distinct (i j : Nat) (hi : i < 9) (hj : j < 9) (hne : i ≠ j) :
    cm9Pow i ≠ cm9Pow j := by
  have key : ∀ p q, p < q → q < 9 → cm9Pow p ≠ cm9Pow q := by
    intro p q hpq hq9 heq
    have hmul : cm9R.mul (cm9Pow (9 - p)) (cm9Pow p)
        = cm9R.mul (cm9Pow (9 - p)) (cm9Pow q) :=
      congrArg (cm9R.mul (cm9Pow (9 - p))) heq
    have hL : cm9R.mul (cm9Pow (9 - p)) (cm9Pow p) = cm9R.one := by
      have h1 : cm9R.mul (cm9Pow (9 - p)) (cm9Pow p) = cm9Pow ((9 - p) + p) :=
        (cm9Pow_add (9 - p) p).symm
      rw [h1, show (9 - p) + p = 9 from by omega]
      exact cm9_zeta_pow9
    have hR : cm9R.mul (cm9Pow (9 - p)) (cm9Pow q) = cm9Pow (q - p) := by
      have h2 : cm9R.mul (cm9Pow (9 - p)) (cm9Pow q) = cm9Pow ((9 - p) + q) :=
        (cm9Pow_add (9 - p) q).symm
      rw [h2, show (9 - p) + q = 9 + (q - p) from by omega, cm9Pow_add 9 (q - p),
        cm9_zeta_pow9, cm9R.one_mul (cm9Pow (q - p))]
    rw [hL, hR] at hmul
    exact (cm9_order.2 (q - p) (by omega) (by omega)) hmul.symm
  cases Nat.lt_or_ge i j with
  | inl h => exact key i j h hj
  | inr h => exact fun heq => key j i (by omega) hi heq.symm

end IUT
