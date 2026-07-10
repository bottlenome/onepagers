/-
  IUT/CyclotomicMuTower.lean — A3 一般 n 塔 M2（一般段の μ_{3ⁿ} = ⟨ζ_n⟩・
  位数 3ⁿ の巡回群）。設計 audit/A3-inverse-limit-roadmap-2026-07-09.md §3.2
  の CyclotomicMuTower。CM9/CM9Roots（数値 9 = 3² 固定）を 3ⁿ に一般化した
  n 一般段（写経比率高・choice 回避構成は CM9 で確立済み）。

  ── 分類 **[実／本物建設(b)]**（本物の先行建設。骨格・模型・代理・toy 主語
     なし・sorry 皆無・新規 Classical.choice 皆無）。実 NF 担体
     `GefNF (ctsPhi n) (2·3^{n-1})` ＝ ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ}) の第二表示の
     上で、生成元 ζ_n = x̄ が 1 の原始 3ⁿ 乗根であること——ζ_n^{3ⁿ} = 1・
     ζ_n^{3^{n-1}} ≠ 1・位数ちょうど 3ⁿ・冪 3ⁿ 個相異・9 乗根群の全射性・
     構成的指標抽出——を core Lean のみで本物に n 一般で証明する。

  **complete_pct 影響**: A3 一般 n 塔（M2）の μ 段。μ_{3ⁿ}(ℚ(ζ_{3ⁿ})) = ⟨ζ_n⟩
  （位数 3ⁿ の巡回群）を n 一般で確立し、一般 σ_a（csa）と res_n（ctr）の指標
  抽出（σ(ζ_n) = ζ_n^a）の土台を与える。本ファイル単体では complete_pct 未設定
  （M2 完成＝ctr 到達で反映・独立監査確定）。

  内容（設計 §3.2）:
   * `ctmZeta n hn`         — ζ_n = x̄ = 単項式 X̄ の NF 担体元（gefNFMon）。
   * `ctmPow n hn k`        — ζ_n の冪 ζ_n^k（NF 環の乗法の反復）。
   * `ctm_pow_cong`         — ζ_n^k ≡ X^k (mod Φ_{3ⁿ})（合同代数の k 帰納）。
   * `ctm_nf_unique`        — NF 代表の一意性（pfdRed_char 直結）。
   * `ctm_zeta_pow`         — **ζ_n^{3ⁿ} = 1**（cts_pow_sub_one を商に落とす）。
   * `ctm_zeta_pow_sub_ne`  — **ζ_n^{3^{n-1}} ≠ 1**（deg 3^{n-1} < 2·3^{n-1} で NF）。
   * `ctmPow_add`           — 冪の準同型 ζ_n^{a+b} = ζ_n^a·ζ_n^b。
   * `ctm_order`            — **位数ちょうど 3ⁿ**（ctmPow_add + pow_sub 短絡）。
   * `ctm_powers_distinct`  — 冪 ζ_n^0,…,ζ_n^{3ⁿ−1} は相異。
   * `ctm_root_in_powers`   — **全射性**: y^{3ⁿ} = 1 ⟹ ∃ a<3ⁿ, y = ζ_n^a
                              （prc_roots_le_degree の 3ⁿ+1 根矛盾）。
   * `ctmFind / ctmFind_spec` — 構成的指標抽出（fuel 3ⁿ の choice-free 走査）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   - **本物**: 全定理は実 NF 担体 `GefNF (ctsPhi n) (2·3^{n-1})` 上の本物の
     等式・不等式・存在。模型・代理なし。核恒等式は実 `cts_pow_sub_one`
     （X^{3ⁿ}−1 = Φ_{3ⁿ}·(X^{3^{n-1}}−1)）の商。
   - **部分ケースであること（消さない）**: p = 3・円分塔 ℚ(ζ_{3ⁿ}) のみ。
     本ファイルは μ 群（位数 3ⁿ の巡回性）と 3ⁿ 乗根群の全射性・指標抽出まで。
     代入自己同型 σ_a（σ(ζ_n) = ζ_n^a の a）の群論的性質・制限準同型 res_n の
     compat・全射性は csa/ctr（後段）の射程であり本ファイルに含めない。
   - 等号判定 `ctmEq` は「deg < 2·3^{n-1} の各係数の qIsZero 連言」＝ GefNF
     担体の choice-free 一致判定（fuel 2·3^{n-1} の走査に一般化・CM9 の固定
     6 連言を n 可変に）。2·3^{n-1} 以上の係数は担体有界性で自動一致。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク（simp/decide/by_cases/rcases/ring/
  nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。
  3ⁿ は omega 不可（Nat.pow_succ で atom 化・`ctm_pow3_split` を明示補助）。
-/
import IUT.CyclotomicEmbedTower
import IUT.PolyRootCount
import IUT.GenExtBasisAlpha
import IUT.GenExtFieldInv
import IUT.PolyLeadFindQ
import IUT.EvaluationHom
import IUT.Composition
import IUT.LubinTateZp

namespace IUT

/-! ## CTM-0: 3ⁿ の冪算術（omega 不可・手動補助） -/

/-- **CTM-0a: 段の分割** — 1 ≤ n で 3ⁿ = 3^{n−1}·3（omega に渡す atom 関係）。 -/
theorem ctm_pow3_split (n : Nat) (hn : 1 ≤ n) : (3 : Nat) ^ n = 3 ^ (n - 1) * 3 := by
  have h := cts_pow3_succ (n - 1)
  rw [show n - 1 + 1 = n from by omega] at h
  exact h

/-! ## CTM-1: NF 環・生成元 ζ_n・その冪 -/

/-- **CTM-1a: NF 環** ℚ[x]/(Φ_{3ⁿ})（= (cteField n).toCRing の担体環）。 -/
def ctmR (n : Nat) (hn : 1 ≤ n) : CRing :=
  gefNFRing (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn) (cte_nf_pos n hn)

/-- **CTM-1b: 生成元 ζ_n = x̄** — 単項式 X の NF 担体元（deg 1 < 2·3^{n-1}
    で簡約不要）。 -/
def ctmZeta (n : Nat) (hn : 1 ≤ n) : GefNF (ctsPhi n) (2 * 3 ^ (n - 1)) :=
  gefNFMon (ctsPhi n) (2 * 3 ^ (n - 1)) 1 (by have hp := cte_pow3_pos (n - 1); omega)

/-- **CTM-1c: ζ_n の冪** ζ_n^k（NF 環の乗法の反復）。 -/
def ctmPow (n : Nat) (hn : 1 ≤ n) (k : Nat) : GefNF (ctsPhi n) (2 * 3 ^ (n - 1)) :=
  gefNFPow (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
    (cte_nf_pos n hn) (ctmZeta n hn) k

/-! ## CTM-2: ζ_n^k ≡ X^k (mod Φ_{3ⁿ}) と NF 一意性 -/

/-- **CTM-2a: 冪の合同** — ζ_n^k ≡ X^k (mod Φ_{3ⁿ})。k 帰納:
    ζ_n^{k+1} = pfdRed(ζ_n^k·X̄) ≡ ζ_n^k·X ≡ X^k·X = X^{k+1}（gnfCong 伝播）。 -/
theorem ctm_pow_cong (n : Nat) (hn : 1 ≤ n) (k : Nat) :
    gnfCong (ctsPhi n) (ctmPow n hn k).val (psSingle ratRing ratRing.one k) := by
  induction k with
  | zero =>
    exact gnfCong_of_eq (ctsPhi n) (ctmPow n hn 0).val (psSingle ratRing ratRing.one 0) rfl
  | succ k ih =>
    show gnfCong (ctsPhi n)
      (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1))
        (psMul ratRing (ctmPow n hn k).val (ctmZeta n hn).val))
      (psSingle ratRing ratRing.one (k + 1))
    have hred : gnfCong (ctsPhi n)
        (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1))
          (psMul ratRing (ctmPow n hn k).val (ctmZeta n hn).val))
        (psMul ratRing (ctmPow n hn k).val (ctmZeta n hn).val) :=
      gnfCong_red (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
        (2 * 3 ^ (n - 1)) (psMul ratRing (ctmPow n hn k).val (ctmZeta n hn).val)
        (simpleExt_mul_bounded ratRing (ctmPow n hn k).property (ctmZeta n hn).property)
    have hmr : gnfCong (ctsPhi n)
        (psMul ratRing (ctmPow n hn k).val (ctmZeta n hn).val)
        (psMul ratRing (psSingle ratRing ratRing.one k) (ctmZeta n hn).val) :=
      gnfCong_mul_right (ctsPhi n) (ctmZeta n hn).val
        ⟨2 * 3 ^ (n - 1), (ctmZeta n hn).property⟩ ih
    have hprodeq : psMul ratRing (psSingle ratRing ratRing.one k) (ctmZeta n hn).val
        = psSingle ratRing ratRing.one (k + 1) := by
      funext j
      show psMul ratRing (psSingle ratRing ratRing.one k)
          (psSingle ratRing ratRing.one 1) j
        = psSingle ratRing ratRing.one (k + 1) j
      rw [gefSMS ratRing.one ratRing.one k 1 j, ratRing.one_mul ratRing.one]
    exact gnfCong_trans (ctsPhi n) hred
      (gnfCong_trans (ctsPhi n) hmr
        (gnfCong_of_eq (ctsPhi n)
          (psMul ratRing (psSingle ratRing ratRing.one k) (ctmZeta n hn).val)
          (psSingle ratRing ratRing.one (k + 1)) hprodeq))

/-- **CTM-2b: NF 代表の一意性** — 2·3^{n-1} 有界の 2 元が Φ_{3ⁿ} を法として
    合同なら等しい（pfdRed_of_bounded ＋ pfdRed_char の合成）。 -/
theorem ctm_nf_unique (n : Nat) (hn : 1 ≤ n) (w v : PS ratRing)
    (hw : IsPolyBounded ratRing w (2 * 3 ^ (n - 1)))
    (hv : IsPolyBounded ratRing v (2 * 3 ^ (n - 1)))
    (hcong : gnfCong (ctsPhi n) w v) : w = v := by
  obtain ⟨h, ⟨Nh, hhb⟩, hhe⟩ := hcong
  funext j
  have h1 : pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) w j = w j :=
    pfdRed_of_bounded (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
      (2 * 3 ^ (n - 1)) w hw j
  have h2 : pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) w j = v j :=
    pfdRed_char (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
      (2 * 3 ^ (n - 1)) w v (fun i hi => hw i (by omega)) hv
      ⟨h, Nh, hhb, fun k => congrFun hhe k⟩ j
  rw [← h1, h2]

/-! ## CTM-3: ζ_n^{3ⁿ} = 1 と ζ_n^{3^{n-1}} ≠ 1 -/

/-- **CTM-3a: psOne は 2·3^{n-1} 有界**。 -/
theorem ctm_one_bound (n : Nat) (hn : 1 ≤ n) :
    IsPolyBounded ratRing (psOne ratRing) (2 * 3 ^ (n - 1)) := by
  intro j hj
  show (if j = 0 then ratRing.one else ratRing.zero) = ratRing.zero
  exact if_neg (by have hp := cte_pow3_pos (n - 1); omega)

/-- **CTM-3b: X^{3ⁿ} ≡ 1 (mod Φ_{3ⁿ})** — 核恒等式 `cts_pow_sub_one` の商
    （witness h = X^{3^{n-1}}−1）。 -/
theorem ctm_xpow_cong_one (n : Nat) (hn : 1 ≤ n) :
    gnfCong (ctsPhi n) (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing) := by
  refine ⟨ctsXm1 (3 ^ (n - 1)), ⟨3 ^ (n - 1) + 1, ?_⟩, ?_⟩
  · intro j hj
    show ratRing.add (psSingle ratRing ratRing.one (3 ^ (n - 1)) j)
        (psC ratRing (ratRing.neg ratRing.one) j) = ratRing.zero
    rw [show psSingle ratRing ratRing.one (3 ^ (n - 1)) j = ratRing.zero from if_neg (by omega),
      show psC ratRing (ratRing.neg ratRing.one) j = ratRing.zero
        from if_neg (by have hp := cte_pow3_pos (n - 1); omega),
      ratRing.zero_add]
  · show psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psNeg ratRing (psOne ratRing))
      = psMul ratRing (ctsXm1 (3 ^ (n - 1))) (ctsPhi n)
    have hneg : psNeg ratRing (psOne ratRing) = psC ratRing (ratRing.neg ratRing.one) := by
      funext m
      cases m with
      | zero => rfl
      | succ k =>
        show ratRing.neg ratRing.zero = ratRing.zero
        exact CRing.neg_zero ratRing
    rw [hneg]
    show ctsXm1 (3 ^ n) = psMul ratRing (ctsXm1 (3 ^ (n - 1))) (ctsPhi n)
    rw [cts_pow_sub_one n hn]
    exact (psRing ratRing).mul_comm (ctsPhi n) (ctsXm1 (3 ^ (n - 1)))

/-- **CTM-3c（本丸）: ζ_n^{3ⁿ} = 1** — ctm_pow_cong (3ⁿ)（ζ_n^{3ⁿ} ≡ X^{3ⁿ}）と
    ctm_xpow_cong_one（X^{3ⁿ} ≡ 1）の合成 + NF 一意性。 -/
theorem ctm_zeta_pow (n : Nat) (hn : 1 ≤ n) : ctmPow n hn (3 ^ n) = (ctmR n hn).one := by
  apply Subtype.ext
  show (ctmPow n hn (3 ^ n)).val = psOne ratRing
  exact ctm_nf_unique n hn (ctmPow n hn (3 ^ n)).val (psOne ratRing)
    (ctmPow n hn (3 ^ n)).property (ctm_one_bound n hn)
    (gnfCong_trans (ctsPhi n) (ctm_pow_cong n hn (3 ^ n)) (ctm_xpow_cong_one n hn))

/-- **CTM-3d: 小さい冪の値** — k < 2·3^{n-1} で ζ_n^k = X^k（簡約不要）。 -/
theorem ctm_pow_small (n : Nat) (hn : 1 ≤ n) (k : Nat) (hk : k < 2 * 3 ^ (n - 1)) :
    (ctmPow n hn k).val = psSingle ratRing ratRing.one k :=
  ctm_nf_unique n hn (ctmPow n hn k).val (psSingle ratRing ratRing.one k)
    (ctmPow n hn k).property (fun i hi => if_neg (by omega)) (ctm_pow_cong n hn k)

/-- **CTM-3e: ζ_n^{3^{n-1}} ≠ 1** — ζ_n^{3^{n-1}} = X^{3^{n-1}}
    （deg 3^{n-1} < 2·3^{n-1}）で 3^{n-1} 次係数 1 ≠ 定数項 0。 -/
theorem ctm_zeta_pow_sub_ne (n : Nat) (hn : 1 ≤ n) :
    ctmPow n hn (3 ^ (n - 1)) ≠ (ctmR n hn).one := by
  intro h
  have hval : (ctmPow n hn (3 ^ (n - 1))).val = psOne ratRing :=
    congrArg (fun z : GefNF (ctsPhi n) (2 * 3 ^ (n - 1)) => z.val) h
  rw [ctm_pow_small n hn (3 ^ (n - 1)) (by have hp := cte_pow3_pos (n - 1); omega)] at hval
  have hc : psSingle ratRing ratRing.one (3 ^ (n - 1)) (3 ^ (n - 1))
      = psOne ratRing (3 ^ (n - 1)) := congrFun hval (3 ^ (n - 1))
  rw [show psSingle ratRing ratRing.one (3 ^ (n - 1)) (3 ^ (n - 1)) = ratRing.one from if_pos rfl,
    show psOne ratRing (3 ^ (n - 1)) = ratRing.zero
      from if_neg (by have hp := cte_pow3_pos (n - 1); omega)] at hc
  exact cbp_one_ne_zero hc

/-! ## CTM-4: 冪の準同型と位数ちょうど 3ⁿ -/

/-- **CTM-4a: 冪の準同型** — ζ_n^{a+b} = ζ_n^a·ζ_n^b（b 帰納・mul_assoc）。 -/
theorem ctmPow_add (n : Nat) (hn : 1 ≤ n) (a b : Nat) :
    ctmPow n hn (a + b) = (ctmR n hn).mul (ctmPow n hn a) (ctmPow n hn b) := by
  induction b with
  | zero => exact (CRing.mul_one (ctmR n hn) (ctmPow n hn a)).symm
  | succ b ih =>
    show (ctmR n hn).mul (ctmPow n hn (a + b)) (ctmZeta n hn)
      = (ctmR n hn).mul (ctmPow n hn a) ((ctmR n hn).mul (ctmPow n hn b) (ctmZeta n hn))
    rw [ih]
    exact (ctmR n hn).mul_assoc (ctmPow n hn a) (ctmPow n hn b) (ctmZeta n hn)

/-- **CTM-4b: 冪の差** — ζ_n^a = 1 かつ ζ_n^c = 1（a ≤ c）⟹ ζ_n^{c−a} = 1。 -/
theorem ctm_pow_sub (n : Nat) (hn : 1 ≤ n) (a c : Nat)
    (ha : ctmPow n hn a = (ctmR n hn).one) (hc : ctmPow n hn c = (ctmR n hn).one)
    (hac : a ≤ c) : ctmPow n hn (c - a) = (ctmR n hn).one := by
  have hca : a + (c - a) = c := by omega
  have hsplit : ctmPow n hn (a + (c - a))
      = (ctmR n hn).mul (ctmPow n hn a) (ctmPow n hn (c - a)) :=
    ctmPow_add n hn a (c - a)
  rw [hca, ha, hc, (ctmR n hn).one_mul (ctmPow n hn (c - a))] at hsplit
  exact hsplit.symm

/-- **CTM-4c（本丸）: 位数ちょうど 3ⁿ** — ζ_n^{3ⁿ} = 1 かつ 0 < k < 3ⁿ で
    ζ_n^k ≠ 1。k < 2·3^{n-1} は ctm_pow_small（X^k ≠ 1）、2·3^{n-1} ≤ k は
    ctm_pow_sub で ζ_n^{3ⁿ−k}（3ⁿ−k ≤ 3^{n-1} < 2·3^{n-1}）へ落として矛盾
    （高冪の explicit 計算を準同型短絡で回避）。 -/
theorem ctm_order (n : Nat) (hn : 1 ≤ n) :
    ctmPow n hn (3 ^ n) = (ctmR n hn).one ∧
      ∀ k, 0 < k → k < 3 ^ n → ctmPow n hn k ≠ (ctmR n hn).one := by
  refine ⟨ctm_zeta_pow n hn, ?_⟩
  intro k hk0 hk9 hpow
  have hp := cte_pow3_pos (n - 1)
  have hpow3 : (3 : Nat) ^ n = 3 ^ (n - 1) * 3 := ctm_pow3_split n hn
  cases Nat.lt_or_ge k (2 * 3 ^ (n - 1)) with
  | inl hlt =>
    have hone : (ctmPow n hn k).val = psOne ratRing :=
      congrArg (fun z : GefNF (ctsPhi n) (2 * 3 ^ (n - 1)) => z.val) hpow
    rw [ctm_pow_small n hn k hlt] at hone
    have hc : psSingle ratRing ratRing.one k k = psOne ratRing k := congrFun hone k
    rw [show psSingle ratRing ratRing.one k k = ratRing.one from if_pos rfl,
      show psOne ratRing k = ratRing.zero from if_neg (by omega)] at hc
    exact cbp_one_ne_zero hc
  | inr hge =>
    have hsub : ctmPow n hn (3 ^ n - k) = (ctmR n hn).one :=
      ctm_pow_sub n hn k (3 ^ n) hpow (ctm_zeta_pow n hn) (by omega)
    have hlt2 : 3 ^ n - k < 2 * 3 ^ (n - 1) := by omega
    have hone : (ctmPow n hn (3 ^ n - k)).val = psOne ratRing :=
      congrArg (fun z : GefNF (ctsPhi n) (2 * 3 ^ (n - 1)) => z.val) hsub
    rw [ctm_pow_small n hn (3 ^ n - k) hlt2] at hone
    have hc : psSingle ratRing ratRing.one (3 ^ n - k) (3 ^ n - k)
        = psOne ratRing (3 ^ n - k) := congrFun hone (3 ^ n - k)
    rw [show psSingle ratRing ratRing.one (3 ^ n - k) (3 ^ n - k) = ratRing.one from if_pos rfl,
      show psOne ratRing (3 ^ n - k) = ratRing.zero from if_neg (by omega)] at hc
    exact cbp_one_ne_zero hc

/-- **CTM-4d: 冪 ζ_n^0,…,ζ_n^{3ⁿ−1} は相異** — ζ_n^p = ζ_n^q（p < q < 3ⁿ）なら
    左から ζ_n^{3ⁿ−p} を掛けて 1 = ζ_n^{q−p}（0 < q−p < 3ⁿ）で位数 3ⁿ に矛盾。 -/
theorem ctm_powers_distinct (n : Nat) (hn : 1 ≤ n) (i j : Nat)
    (hi : i < 3 ^ n) (hj : j < 3 ^ n) (hne : i ≠ j) :
    ctmPow n hn i ≠ ctmPow n hn j := by
  have key : ∀ p q, p < q → q < 3 ^ n → ctmPow n hn p ≠ ctmPow n hn q := by
    intro p q hpq hq9 heq
    have hmul : (ctmR n hn).mul (ctmPow n hn (3 ^ n - p)) (ctmPow n hn p)
        = (ctmR n hn).mul (ctmPow n hn (3 ^ n - p)) (ctmPow n hn q) :=
      congrArg ((ctmR n hn).mul (ctmPow n hn (3 ^ n - p))) heq
    have hL : (ctmR n hn).mul (ctmPow n hn (3 ^ n - p)) (ctmPow n hn p) = (ctmR n hn).one := by
      have h1 : (ctmR n hn).mul (ctmPow n hn (3 ^ n - p)) (ctmPow n hn p)
          = ctmPow n hn ((3 ^ n - p) + p) :=
        (ctmPow_add n hn (3 ^ n - p) p).symm
      rw [h1, show (3 ^ n - p) + p = 3 ^ n from by omega]
      exact ctm_zeta_pow n hn
    have hR : (ctmR n hn).mul (ctmPow n hn (3 ^ n - p)) (ctmPow n hn q)
        = ctmPow n hn (q - p) := by
      have h2 : (ctmR n hn).mul (ctmPow n hn (3 ^ n - p)) (ctmPow n hn q)
          = ctmPow n hn ((3 ^ n - p) + q) :=
        (ctmPow_add n hn (3 ^ n - p) q).symm
      rw [h2, show (3 ^ n - p) + q = 3 ^ n + (q - p) from by omega,
        ctmPow_add n hn (3 ^ n) (q - p), ctm_zeta_pow n hn,
        (ctmR n hn).one_mul (ctmPow n hn (q - p))]
    rw [hL, hR] at hmul
    exact ((ctm_order n hn).2 (q - p) (by omega) (by omega)) hmul.symm
  cases Nat.lt_or_ge i j with
  | inl h => exact key i j h hj
  | inr h => exact fun heq => key j i (by omega) hi heq.symm

/-! ## CTM-5: 体 K = ℚ(ζ_{3ⁿ}) と多項式 X^{3ⁿ} − 1 -/

/-- **CTM-5a: 体 K = ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ})**（Field268・`gefNF268`）。
    担体環 (ctmK n hn).ring は ctmR n hn に定義等値。 -/
def ctmK (n : Nat) (hn : 1 ≤ n) : Field268 :=
  gefNF268 (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
    (cte_nf_pos n hn) (eitPhi_irreducible n hn)

/-- **CTM-5b: K 係数の X^{3ⁿ} − 1** — 3ⁿ 次係数 1・定数 −1。 -/
def ctmXm1K (n : Nat) (hn : 1 ≤ n) : PS (ctmK n hn).ring :=
  psAdd (ctmK n hn).ring (psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n))
    (psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one))

/-- **CTM-5c: X^{3ⁿ} − 1 は 3ⁿ+1 有界**。 -/
theorem ctmXm1K_bound (n : Nat) (hn : 1 ≤ n) :
    IsPolyBounded (ctmK n hn).ring (ctmXm1K n hn) (3 ^ n + 1) := by
  intro j hj
  show (ctmK n hn).ring.add (psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n) j)
      (psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one) j) = (ctmK n hn).ring.zero
  rw [show psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n) j = (ctmK n hn).ring.zero
      from if_neg (by omega),
    show psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one) j = (ctmK n hn).ring.zero
      from if_neg (by have hp := cte_pow3_pos n; omega),
    (ctmK n hn).ring.zero_add]

/-- **CTM-5d: X^{3ⁿ} − 1 の先頭係数（3ⁿ 次）= 1**。 -/
theorem ctmXm1K_lead (n : Nat) (hn : 1 ≤ n) : ctmXm1K n hn (3 ^ n) = (ctmK n hn).ring.one := by
  show (ctmK n hn).ring.add (psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n) (3 ^ n))
      (psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one) (3 ^ n)) = (ctmK n hn).ring.one
  rw [show psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n) (3 ^ n) = (ctmK n hn).ring.one
      from if_pos rfl,
    show psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one) (3 ^ n)
      = (ctmK n hn).ring.zero from if_neg (by have hp := cte_pow3_pos n; omega),
    CRing.add_zero (ctmK n hn).ring]

/-- **CTM-5e: K の非自明性** 1 ≠ 0（`gnf_zero_ne_one` の Φ_{3ⁿ} 実例）。 -/
theorem ctm_one_ne_zero (n : Nat) (hn : 1 ≤ n) : (ctmK n hn).ring.one ≠ (ctmK n hn).ring.zero :=
  gnf_zero_ne_one (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn) (cte_nf_pos n hn)

/-- **CTM-5f: 先頭係数 ≠ 0**（根数上界の入力）。 -/
theorem ctmXm1K_lead_ne (n : Nat) (hn : 1 ≤ n) :
    ctmXm1K n hn (3 ^ n) ≠ (ctmK n hn).ring.zero := by
  rw [ctmXm1K_lead n hn]
  exact ctm_one_ne_zero n hn

/-! ## CTM-6: 評価 ev_y(X^{3ⁿ} − 1) = y^{3ⁿ} − 1 -/

/-- **CTM-6: 評価値** — ev_y(X^{3ⁿ} − 1)|_{3ⁿ+1} = y^{3ⁿ} + (−1)（`evalHom_add`
    で分け、各を一点集中和 `rsum_single` で潰す）。 -/
theorem ctmr_eval (n : Nat) (hn : 1 ≤ n) (y : (ctmK n hn).ring.carrier) :
    evalSum (evalHomId (ctmK n hn).ring) y (ctmXm1K n hn) (3 ^ n + 1)
      = (ctmK n hn).ring.add (rpow (ctmK n hn).ring y (3 ^ n))
          ((ctmK n hn).ring.neg (ctmK n hn).ring.one) := by
  have hp1 : evalSum (evalHomId (ctmK n hn).ring) y
        (psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n)) (3 ^ n + 1)
      = rpow (ctmK n hn).ring y (3 ^ n) := by
    rw [evalSum_id,
      rsum_single (ctmK n hn).ring _ (3 ^ n) (3 ^ n + 1) (by omega) (fun j hj hjne => by
        show (ctmK n hn).ring.mul (psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n) j)
            (rpow (ctmK n hn).ring y j) = (ctmK n hn).ring.zero
        rw [show psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n) j = (ctmK n hn).ring.zero
            from if_neg hjne, CRing.zero_mul (ctmK n hn).ring])]
    show (ctmK n hn).ring.mul (psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n) (3 ^ n))
        (rpow (ctmK n hn).ring y (3 ^ n)) = rpow (ctmK n hn).ring y (3 ^ n)
    rw [show psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n) (3 ^ n) = (ctmK n hn).ring.one
        from if_pos rfl, (ctmK n hn).ring.one_mul (rpow (ctmK n hn).ring y (3 ^ n))]
  have hp2 : evalSum (evalHomId (ctmK n hn).ring) y
        (psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one)) (3 ^ n + 1)
      = (ctmK n hn).ring.neg (ctmK n hn).ring.one := by
    rw [evalSum_id,
      rsum_single (ctmK n hn).ring _ 0 (3 ^ n + 1) (Nat.succ_pos (3 ^ n)) (fun j hj hjne => by
        show (ctmK n hn).ring.mul (psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one) j)
            (rpow (ctmK n hn).ring y j) = (ctmK n hn).ring.zero
        rw [show psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one) j
            = (ctmK n hn).ring.zero from if_neg hjne, CRing.zero_mul (ctmK n hn).ring])]
    show (ctmK n hn).ring.mul (psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one) 0)
        (rpow (ctmK n hn).ring y 0) = (ctmK n hn).ring.neg (ctmK n hn).ring.one
    rw [show psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one) 0
          = (ctmK n hn).ring.neg (ctmK n hn).ring.one from if_pos rfl,
      show rpow (ctmK n hn).ring y 0 = (ctmK n hn).ring.one from rfl,
      CRing.mul_one (ctmK n hn).ring]
  rw [show ctmXm1K n hn = psAdd (ctmK n hn).ring
        (psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n))
        (psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one)) from rfl,
    evalHom_add (evalHomId (ctmK n hn).ring) y
      (psSingle (ctmK n hn).ring (ctmK n hn).ring.one (3 ^ n))
      (psC (ctmK n hn).ring ((ctmK n hn).ring.neg (ctmK n hn).ring.one)) (3 ^ n + 1), hp1, hp2]

/-! ## CTM-7: 3ⁿ 乗根は X^{3ⁿ} − 1 の根・ζ_n^a の根性 -/

/-- **CTM-7a: 一般の 3ⁿ 乗根は根** — y^{3ⁿ} = 1 ⟹ prcIsRoot。 -/
theorem ctmr_y_is_root (n : Nat) (hn : 1 ≤ n) (y : (ctmK n hn).ring.carrier)
    (hy : rpow (ctmK n hn).ring y (3 ^ n) = (ctmK n hn).ring.one) :
    prcIsRoot (ctmK n hn) (ctmXm1K n hn) y := by
  apply prc_root_of_eval (ctmK n hn) (ctmXm1K n hn) y (3 ^ n + 1) (ctmXm1K_bound n hn)
  rw [ctmr_eval n hn y, hy]
  exact CRing.add_neg (ctmK n hn).ring (ctmK n hn).ring.one

/-- **CTM-7b: rpow(ζ_n^a) = ζ_n^{a·m}** — 冪の反復を `ctmPow_add` で回収。 -/
theorem ctmr_rpow_ctmPow (n : Nat) (hn : 1 ≤ n) (a : Nat) : ∀ m,
    rpow (ctmK n hn).ring (ctmPow n hn a) m = ctmPow n hn (a * m) := by
  intro m
  induction m with
  | zero =>
    show (ctmK n hn).ring.one = ctmPow n hn (a * 0)
    rw [Nat.mul_zero]
    rfl
  | succ m ih =>
    show (ctmK n hn).ring.mul (rpow (ctmK n hn).ring (ctmPow n hn a) m) (ctmPow n hn a)
      = ctmPow n hn (a * (m + 1))
    have harith : a * (m + 1) = a * m + a := Nat.mul_succ a m
    rw [ih, harith, ctmPow_add n hn (a * m) a]
    rfl

/-- **CTM-7c: ζ_n^{a·3ⁿ} = 1**（ctm_zeta_pow を a 回反復）。 -/
theorem ctmr_pow_mul (n : Nat) (hn : 1 ≤ n) (a : Nat) :
    ctmPow n hn (a * 3 ^ n) = (ctmK n hn).ring.one := by
  induction a with
  | zero =>
    show ctmPow n hn (0 * 3 ^ n) = (ctmK n hn).ring.one
    rw [Nat.zero_mul]
    rfl
  | succ a ih =>
    show ctmPow n hn ((a + 1) * 3 ^ n) = (ctmK n hn).ring.one
    have harith : (a + 1) * 3 ^ n = a * 3 ^ n + 3 ^ n := Nat.succ_mul a (3 ^ n)
    rw [harith, ctmPow_add n hn (a * 3 ^ n) (3 ^ n), ih, ctm_zeta_pow n hn]
    exact (ctmK n hn).ring.one_mul (ctmK n hn).ring.one

/-- **CTM-7d: (ζ_n^a)^{3ⁿ} = 1**（7b + 7c）。 -/
theorem ctmr_rpow_pow (n : Nat) (hn : 1 ≤ n) (a : Nat) :
    rpow (ctmK n hn).ring (ctmPow n hn a) (3 ^ n) = (ctmK n hn).ring.one := by
  rw [ctmr_rpow_ctmPow n hn a (3 ^ n)]
  exact ctmr_pow_mul n hn a

/-- **CTM-7e: ζ_n^a は X^{3ⁿ} − 1 の根**。 -/
theorem ctmr_pow_is_root (n : Nat) (hn : 1 ≤ n) (a : Nat) :
    prcIsRoot (ctmK n hn) (ctmXm1K n hn) (ctmPow n hn a) :=
  ctmr_y_is_root n hn (ctmPow n hn a) (ctmr_rpow_pow n hn a)

/-! ## CTM-8: NF 担体の等号 Bool 判定（choice-free・fuel 2·3^{n-1} 走査） -/

/-- **CTM-8a: 座標等号の畳込み** — deg < m の各係数で qIsZero(u_j − v_j) を
    連言（CM9 の固定 6 連言を m 可変に一般化した本物の choice-free 判定）。 -/
def ctmCoordEq (n : Nat) (u v : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) : Nat → Bool
  | 0 => true
  | m + 1 => ctmCoordEq n u v m && qIsZero (ratRing.add (u.val m) (ratRing.neg (v.val m)))

/-- **CTM-8b: 担体等号 Bool 判定** — deg < 2·3^{n-1} の全係数の連言。 -/
def ctmEq (n : Nat) (u v : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) : Bool :=
  ctmCoordEq n u v (2 * 3 ^ (n - 1))

/-- **CTM-8c: 畳込みの特徴付け** — ctmCoordEq u v m = true ⟺ deg < m の全係数一致。 -/
theorem ctmCoordEq_iff (n : Nat) (u v : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) : ∀ m,
    ctmCoordEq n u v m = true ↔ ∀ j, j < m → u.val j = v.val j := by
  intro m
  induction m with
  | zero =>
    apply Iff.intro
    · intro _ j hj; exact absurd hj (by omega)
    · intro _; rfl
  | succ m ih =>
    show (ctmCoordEq n u v m && qIsZero (ratRing.add (u.val m) (ratRing.neg (v.val m)))) = true
      ↔ ∀ j, j < m + 1 → u.val j = v.val j
    rw [Bool.and_eq_true]
    apply Iff.intro
    · intro h
      obtain ⟨h1, h2⟩ := h
      have hcoord : u.val m = v.val m :=
        CRing.eq_of_sub_eq_zero ratRing
          ((qIsZero_iff (ratRing.add (u.val m) (ratRing.neg (v.val m)))).mp h2)
      intro j hj
      cases Nat.lt_or_ge j m with
      | inl hlt => exact (ih.mp h1) j hlt
      | inr hge => rw [show j = m from by omega]; exact hcoord
    · intro h
      refine ⟨ih.mpr (fun j hj => h j (by omega)), ?_⟩
      rw [h m (by omega), CRing.add_neg ratRing (v.val m)]
      exact (qIsZero_iff ratRing.zero).mpr rfl

/-- **CTM-8d: 判定の特徴付け** — ctmEq u v = true ⟺ u = v。前向きは全係数一致
    ＋担体有界性（deg ≥ 2·3^{n-1} は両者 0）で Subtype.ext。 -/
theorem ctmEq_iff (n : Nat) (hn : 1 ≤ n) (u v : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) :
    ctmEq n u v = true ↔ u = v := by
  apply Iff.intro
  · intro h
    have hcoords : ∀ j, j < 2 * 3 ^ (n - 1) → u.val j = v.val j :=
      (ctmCoordEq_iff n u v (2 * 3 ^ (n - 1))).mp h
    apply Subtype.ext
    funext j
    cases Nat.lt_or_ge j (2 * 3 ^ (n - 1)) with
    | inl hlt => exact hcoords j hlt
    | inr hge => rw [u.property j hge, v.property j hge]
  · intro h
    subst h
    show ctmCoordEq n u u (2 * 3 ^ (n - 1)) = true
    exact (ctmCoordEq_iff n u u (2 * 3 ^ (n - 1))).mpr (fun j _ => rfl)

/-! ## CTM-9: 有限走査による決定 Or -/

/-- **CTM-9: 決定 Or** — [0, m) の中に y = ζ_n^a となる a が在るか否かを
    choice-free に決定（`ctmEq` の Bool 分岐で m 帰納）。 -/
theorem ctmr_scan (n : Nat) (hn : 1 ≤ n) (y : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) : ∀ m,
    (∃ a, a < m ∧ y = ctmPow n hn a) ∨ (∀ a, a < m → y ≠ ctmPow n hn a) := by
  intro m
  induction m with
  | zero => exact Or.inr (fun a ha => absurd ha (by omega))
  | succ m ih =>
    cases ih with
    | inl h =>
      obtain ⟨a, ha, hae⟩ := h
      exact Or.inl ⟨a, by omega, hae⟩
    | inr hno =>
      cases hb : ctmEq n y (ctmPow n hn m) with
      | true =>
        exact Or.inl ⟨m, by omega, (ctmEq_iff n hn y (ctmPow n hn m)).mp hb⟩
      | false =>
        refine Or.inr (fun a ha => ?_)
        cases Nat.lt_or_ge a m with
        | inl hlt => exact hno a hlt
        | inr hge =>
          rw [show a = m from by omega]
          intro hyeq
          have hcon : ctmEq n y (ctmPow n hn m) = true :=
            (ctmEq_iff n hn y (ctmPow n hn m)).mpr hyeq
          rw [hb] at hcon
          exact Bool.noConfusion hcon

/-! ## CTM-10: 冪リストと相異・根 -/

/-- **CTM-10a: 冪のリスト** [ζ_n^{m−1}, …, ζ_n^0]（長さ m）。 -/
def ctmrPows (n : Nat) (hn : 1 ≤ n) : Nat → List (GefNF (ctsPhi n) (2 * 3 ^ (n - 1)))
  | 0 => []
  | k + 1 => ctmPow n hn k :: ctmrPows n hn k

/-- 長さは m。 -/
theorem ctmrPows_len (n : Nat) (hn : 1 ≤ n) (m : Nat) : (ctmrPows n hn m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (ctmPow n hn m :: ctmrPows n hn m).length = m + 1
    rw [List.length_cons, ih]

/-- 所属 ⟹ 冪指標の存在。 -/
theorem ctmrPows_mem (n : Nat) (hn : 1 ≤ n) (m : Nat) (x : GefNF (ctsPhi n) (2 * 3 ^ (n - 1)))
    (hx : x ∈ ctmrPows n hn m) : ∃ a, a < m ∧ x = ctmPow n hn a := by
  induction m with
  | zero =>
    have hnil : x ∈ ([] : List (GefNF (ctsPhi n) (2 * 3 ^ (n - 1)))) := hx
    exact absurd hnil List.not_mem_nil
  | succ m ih =>
    have hx' : x ∈ ctmPow n hn m :: ctmrPows n hn m := hx
    cases List.mem_cons.mp hx' with
    | inl he => exact ⟨m, by omega, he⟩
    | inr hm =>
      obtain ⟨a, ha, hae⟩ := ih hm
      exact ⟨a, by omega, hae⟩

/-- **CTM-10b: 冪リストは相異**（位数 3ⁿ から・m ≤ 3ⁿ）。 -/
theorem ctmrPows_distinct (n : Nat) (hn : 1 ≤ n) : ∀ m, m ≤ 3 ^ n → prcDistinct (ctmrPows n hn m) := by
  intro m
  induction m with
  | zero => intro _; exact True.intro
  | succ m ih =>
    intro hm
    show prcDistinct (ctmPow n hn m :: ctmrPows n hn m)
    refine ⟨fun x hx => ?_, ih (by omega)⟩
    obtain ⟨a, ha, hae⟩ := ctmrPows_mem n hn m x hx
    rw [hae]
    exact ctm_powers_distinct n hn a m (by omega) (by omega) (by omega)

/-- **CTM-10c: 冪リストの各元は X^{3ⁿ} − 1 の根**。 -/
theorem ctmrPows_roots (n : Nat) (hn : 1 ≤ n) (m : Nat) (x : GefNF (ctsPhi n) (2 * 3 ^ (n - 1)))
    (hx : x ∈ ctmrPows n hn m) : prcIsRoot (ctmK n hn) (ctmXm1K n hn) x := by
  obtain ⟨a, ha, hae⟩ := ctmrPows_mem n hn m x hx
  rw [hae]
  exact ctmr_pow_is_root n hn a

/-! ## CTM-11: 本丸 — 3ⁿ 乗根はすべて ζ_n の冪 -/

/-- **CTM-11（本丸）: μ_{3ⁿ} の全射性** — y^{3ⁿ} = 1 ⟹ ∃ a < 3ⁿ, y = ζ_n^a。
    走査で不一致なら S = [y, ζ_n^0, …, ζ_n^{3ⁿ−1}]（長さ 3ⁿ+1）は相異な根
    3ⁿ+1 個となり、次数 3ⁿ の X^{3ⁿ}−1 に `prc_roots_le_degree` の
    3ⁿ+1 ≤ 3ⁿ で矛盾。 -/
theorem ctm_root_in_powers (n : Nat) (hn : 1 ≤ n) (y : (ctmK n hn).ring.carrier)
    (hy : rpow (ctmK n hn).ring y (3 ^ n) = (ctmK n hn).ring.one) :
    ∃ a, a < 3 ^ n ∧ y = ctmPow n hn a := by
  cases ctmr_scan n hn y (3 ^ n) with
  | inl h => exact h
  | inr hno =>
    exfalso
    have hlen : (y :: ctmrPows n hn (3 ^ n)).length = 3 ^ n + 1 := by
      have h1 : (y :: ctmrPows n hn (3 ^ n)).length = (ctmrPows n hn (3 ^ n)).length + 1 :=
        List.length_cons
      have h2 : (ctmrPows n hn (3 ^ n)).length = 3 ^ n := ctmrPows_len n hn (3 ^ n)
      omega
    have hroots : ∀ r, r ∈ (y :: ctmrPows n hn (3 ^ n)) →
        prcIsRoot (ctmK n hn) (ctmXm1K n hn) r := by
      intro r hr
      cases List.mem_cons.mp hr with
      | inl he => rw [he]; exact ctmr_y_is_root n hn y hy
      | inr hm => exact ctmrPows_roots n hn (3 ^ n) r hm
    have hdist : prcDistinct (y :: ctmrPows n hn (3 ^ n)) := by
      refine ⟨fun x hx => ?_, ctmrPows_distinct n hn (3 ^ n) (by omega)⟩
      obtain ⟨a, ha, hae⟩ := ctmrPows_mem n hn (3 ^ n) x hx
      rw [hae]
      intro hcon
      exact hno a ha hcon.symm
    have hle : (y :: ctmrPows n hn (3 ^ n)).length ≤ 3 ^ n :=
      prc_roots_le_degree (ctmK n hn) (3 ^ n) (ctmXm1K n hn) (ctmXm1K_bound n hn)
        (ctmXm1K_lead_ne n hn) (y :: ctmrPows n hn (3 ^ n)) hroots hdist
    rw [hlen] at hle
    omega

/-! ## CTM-12: 構成的指標抽出 ctmFind -/

/-- **CTM-12a: 下からの走査** — 位置 i から fuel 段、最初に ctmEq が真になる
    位置を返す（無ければ i + fuel）。 -/
def ctmFindGo (n : Nat) (hn : 1 ≤ n) (y : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) : Nat → Nat → Nat
  | i, 0 => i
  | i, fuel + 1 => if ctmEq n y (ctmPow n hn i) then i else ctmFindGo n hn y (i + 1) fuel

/-- **CTM-12b: 指標抽出** — 0 から 3ⁿ 段走査（見つからねば 3ⁿ）。 -/
def ctmFind (n : Nat) (hn : 1 ≤ n) (y : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) : Nat :=
  ctmFindGo n hn y 0 (3 ^ n)

/-- 走査結果の上界 ctmFindGo y i fuel ≤ i + fuel。 -/
theorem ctmFindGo_le (n : Nat) (hn : 1 ≤ n) (y : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) : ∀ fuel i,
    ctmFindGo n hn y i fuel ≤ i + fuel := by
  intro fuel
  induction fuel with
  | zero => intro i; show i ≤ i + 0; omega
  | succ fuel ih =>
    intro i
    cases hb : ctmEq n y (ctmPow n hn i) with
    | true =>
      have he : ctmFindGo n hn y i (fuel + 1) = i := by
        show (if ctmEq n y (ctmPow n hn i) then i else ctmFindGo n hn y (i + 1) fuel) = i
        rw [if_pos hb]
      rw [he]; omega
    | false =>
      have he : ctmFindGo n hn y i (fuel + 1) = ctmFindGo n hn y (i + 1) fuel := by
        show (if ctmEq n y (ctmPow n hn i) then i else ctmFindGo n hn y (i + 1) fuel)
          = ctmFindGo n hn y (i + 1) fuel
        rw [if_neg (by rw [hb]; exact fun hh => Bool.noConfusion hh)]
      rw [he]
      have hih := ih (i + 1)
      omega

/-- **CTM-12c: 走査は範囲内の一致を捕まえる** — [i, i+fuel) に一致が在れば、
    返す位置は一致かつ範囲内。 -/
theorem ctmFindGo_hit (n : Nat) (hn : 1 ≤ n) (y : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) : ∀ fuel i,
    (∃ a, i ≤ a ∧ a < i + fuel ∧ ctmEq n y (ctmPow n hn a) = true) →
    ctmEq n y (ctmPow n hn (ctmFindGo n hn y i fuel)) = true ∧ ctmFindGo n hn y i fuel < i + fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro i h
    obtain ⟨a, ha1, ha2, _⟩ := h
    exfalso; omega
  | succ fuel ih =>
    intro i h
    cases hb : ctmEq n y (ctmPow n hn i) with
    | true =>
      have he : ctmFindGo n hn y i (fuel + 1) = i := by
        show (if ctmEq n y (ctmPow n hn i) then i else ctmFindGo n hn y (i + 1) fuel) = i
        rw [if_pos hb]
      rw [he]
      refine ⟨hb, ?_⟩
      clear h ih
      omega
    | false =>
      have he : ctmFindGo n hn y i (fuel + 1) = ctmFindGo n hn y (i + 1) fuel := by
        show (if ctmEq n y (ctmPow n hn i) then i else ctmFindGo n hn y (i + 1) fuel)
          = ctmFindGo n hn y (i + 1) fuel
        rw [if_neg (by rw [hb]; exact fun hh => Bool.noConfusion hh)]
      rw [he]
      obtain ⟨a, ha1, ha2, ha3⟩ := h
      have hane : a ≠ i := by
        intro hai
        rw [hai, hb] at ha3
        exact Bool.noConfusion ha3
      obtain ⟨hr1, hr2⟩ := ih (i + 1) ⟨a, by omega, by omega, ha3⟩
      exact ⟨hr1, by omega⟩

/-- **CTM-12d: ctmFind の範囲** — ctmFind y < 3ⁿ ∨ ctmFind y = 3ⁿ。 -/
theorem ctmFind_lt (n : Nat) (hn : 1 ≤ n) (y : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) :
    ctmFind n hn y < 3 ^ n ∨ ctmFind n hn y = 3 ^ n := by
  have h := ctmFindGo_le n hn y (3 ^ n) 0
  show ctmFindGo n hn y 0 (3 ^ n) < 3 ^ n ∨ ctmFindGo n hn y 0 (3 ^ n) = 3 ^ n
  omega

/-- **CTM-12e: 抽出の仕様** — y^{3ⁿ} = 1 ⟹ y = ζ_n^{ctmFind y} かつ ctmFind y < 3ⁿ。
    全射性（11）で一致 a を得、走査がそれを捕まえる（12c）。 -/
theorem ctmFind_spec (n : Nat) (hn : 1 ≤ n) (y : (ctmK n hn).ring.carrier)
    (hy : rpow (ctmK n hn).ring y (3 ^ n) = (ctmK n hn).ring.one) :
    y = ctmPow n hn (ctmFind n hn y) ∧ ctmFind n hn y < 3 ^ n := by
  obtain ⟨a, ha, hae⟩ := ctm_root_in_powers n hn y hy
  have hmatch : ctmEq n y (ctmPow n hn a) = true := (ctmEq_iff n hn y (ctmPow n hn a)).mpr hae
  have hhit := ctmFindGo_hit n hn y (3 ^ n) 0 ⟨a, by omega, by omega, hmatch⟩
  show y = ctmPow n hn (ctmFindGo n hn y 0 (3 ^ n)) ∧ ctmFindGo n hn y 0 (3 ^ n) < 3 ^ n
  refine ⟨(ctmEq_iff n hn y (ctmPow n hn (ctmFindGo n hn y 0 (3 ^ n)))).mp hhit.1, ?_⟩
  have hlt := hhit.2
  omega

end IUT
