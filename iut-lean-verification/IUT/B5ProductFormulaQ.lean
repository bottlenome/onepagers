/-
  IUT/B5ProductFormulaQ.lean — B5 積公式 ∏_v |x|_v = 1（ℚ、実）の最終組み立て

  ── 主要成果の分類: **[実]** / complete_pct 影響: **あり（判定は独立監査）**。
     本ファイルは complete_pct を設定しない（規則に従い独立監査に委ねる）。
     実 v_p（`pvqNatVal`/`pvqVal`）・実アルキメデス絶対値（`arpAbs`=`qAbs`）・
     実 p 進絶対値（`pavAbs` = p^{-v_p}、`PadicAbsValueQ`）・実素因数分解
     （`pfcFactors`/`pfc_prod_factors`/`pfc_vp_count`、`PrimeFactorization`）・
     実有限台積（`fspProd`、`FiniteSupportPrimeProduct`）の上で、非零有理数
     x（PreRat 代表・x.num ≠ 0）に対する本物の積公式
         |x|_∞ · ∏_{p ∈ Supp(x)} |x|_p = 1
     を模型・surrogate・toy を一切使わずに from-scratch 証明する。

  ## 核イディオム「両側 cleared form」（負冪と逆元積を回避）
  素朴な |x|_∞ = a/b・∏_p|x|_p = b/a を掛ける方式は (i) 負冪 p^{-v}(v:Int) の
  表現と (ii) 逆元の有限積との交換、という重い補題群を要する。本証明は分母を
  払った乗法等式だけで組む:
    * アルキメデス側 cleared: A · β = α  （A = |x|_∞, α = b5N|num|, β = b5N|den|）
    * p 進側 cleared:        P · α = β  （P = ∏_p|x|_p）
    * 合成: (A·P)·α = A·(P·α) = A·β = α、最後に `qMul_inv`（既存 witness 形）で
      α を 1 回だけキャンセルして A·P = 1。
  逆元は最終キャンセルの 1 箇所のみ。負冪 v:Int は `b5_pav_cleared` の内部
  （Int.toNat の符号恒等式 + Nat.pow_add）に完全に閉じ込め、DAG の残りは全て
  Nat 冪 p^(pvqNatVal …) だけで走る。

  ## 出現回数の管理（R2 の核・重複除去）
  `pfcFactors n` は重複込みリスト。num・den の素因子を連結し `b5Dedup`（Nat の
  `=` 決定を自前 if で扱う choice なし重複除去）で相異なる素数リスト `b5Support x`
  にする。重複なしは Nodup 型ではなく `pfcCount q S = 1`（PrimeFactorization の
  自前 `=` 版 count）で管理する。核補題 `b5_prod_pow_count`:
      ∏_{p∈S} p^{count_L(p)} = listProd L  （count q S = 1 for q∈L）
  を L の帰納で 1 因子ずつ剥がして証明する。

  ## 正直な限定（消去・弱化禁止）
  1. B5 台帳「大域類体論/積公式(実)」の**積公式側のみ**。大域相互写像・イデール
     類群・局所-大域整合（相互律）は未着手。積公式は相互律のノルム 1 条件の最下段。
  2. **K = ℚ のみ**（一般数体の ∏_v|x|_v^{[K_v:ℚ_v]}=1 ではない。実素点 1 個・
     複素素点なし・分岐なしの最易ケース）。
  3. 非零性は代表 witness 形（x : PreRat, x.num ≠ 0）。QRat 全域のゼロ判定選言は
     排中律を要するため対象外（pvqVal・qMul_inv の既存の正直申告を継承）。
  4. 有限台は明示リスト `b5Support x`（num·den の素因子）上の有限積。全素点の型
     （places の束）と無限積の収束は未構成。
  5. 値は ℚ≥0 内（ℝ 未構成）。等式なので ℚ 内で完結し損失はないが、log を取った
     次数式（deg = Σ log|·| = 0）へは進めない。

  達成レベル: **一般 x∈ℚ^×（x.num ≠ 0）で完全**（設計書の後退順の最上位・目標）。
  R2 の組み替え補題 `b5_prod_pow_count` を重複込みリスト上で本物証明した。

  全て Lean 4.30.0 core のみ（mathlib 不使用）・sorry なし・新規 Classical.choice
  なし。#print axioms b5_product_formula は [propext, Quot.sound] のみ。
-/
import IUT.PrimeFactorization
import IUT.PadicAbsValueQ
import IUT.FiniteSupportPrimeProduct
import IUT.ArchValueInteger

namespace IUT

/-! ## N 層: 自然数の ℚ 埋め込み n ↦ n/1 -/

/-- 自然数の ℚ への埋め込み n ↦ n/1。 -/
def b5N (n : Nat) : QRat := Quot.mk ratRel (intToPreRat (n : Int))

/-- **N1**: b5N は乗法的。b5N(mn) = b5N m · b5N n。 -/
theorem b5N_mul (m n : Nat) : b5N (m * n) = ratRing.mul (b5N m) (b5N n) := by
  show Quot.mk ratRel (intToPreRat ((m * n : Nat) : Int))
     = Quot.mk ratRel (prMul (intToPreRat (m : Int)) (intToPreRat (n : Int)))
  apply congrArg (Quot.mk ratRel)
  apply preRat_ext
  · show ((m * n : Nat) : Int) = (m : Int) * (n : Int)
    exact Int.natCast_mul m n
  · show (1 : Int) = 1 * 1
    rw [Int.one_mul]

/-- **N2**: b5N 1 = 1。 -/
theorem b5N_one : b5N 1 = ratRing.one := by
  show Quot.mk ratRel (intToPreRat ((1 : Nat) : Int)) = Quot.mk ratRel prOne
  apply congrArg (Quot.mk ratRel)
  apply preRat_ext
  · show ((1 : Nat) : Int) = 1
    omega
  · rfl

/-- **N3**: b5N(p^{if p=q then 1 else 0}) = if p=q then b5N p else 1。 -/
theorem b5_pow_ind (p q : Nat) :
    b5N (p ^ (if p = q then 1 else 0)) = if p = q then b5N p else ratRing.one := by
  cases Nat.decEq p q with
  | isTrue h =>
    rw [if_pos h, if_pos h]
    show b5N (p ^ 1) = b5N p
    rw [Nat.pow_one]
  | isFalse h =>
    rw [if_neg h, if_neg h]
    show b5N (p ^ 0) = ratRing.one
    rw [Nat.pow_zero]
    exact b5N_one

/-- **N4**: intAbs a = ↑a.natAbs。 -/
theorem b5_intAbs_natAbs (a : Int) : intAbs a = (a.natAbs : Int) := by
  cases Int.lt_or_le a 0 with
  | inl h => rw [intAbs_of_nonpos (Int.le_of_lt h)]; omega
  | inr h => rw [intAbs_of_nonneg h]; omega

/-! ## count（pfcCount）と membership の橋渡し -/

/-- **B1**: q ∉ L なら pfcCount q L = 0。 -/
theorem b5_count_zero_of_not_mem (q : Nat) :
    ∀ (L : List Nat), q ∉ L → pfcCount q L = 0 := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons b L ih =>
    intro h
    show (if q = b then 1 else 0) + pfcCount q L = 0
    have hqb : q ≠ b := fun he => h (List.mem_cons.mpr (Or.inl he))
    have hnm : q ∉ L := fun hm => h (List.mem_cons.mpr (Or.inr hm))
    rw [if_neg hqb, ih hnm]

/-- **B4**: q ∈ L なら pfcCount q L ≠ 0。 -/
theorem b5_count_pos_of_mem (q : Nat) :
    ∀ (L : List Nat), q ∈ L → pfcCount q L ≠ 0 := by
  intro L
  induction L with
  | nil => intro h; cases h
  | cons b L ih =>
    intro h
    show (if q = b then 1 else 0) + pfcCount q L ≠ 0
    cases Nat.decEq q b with
    | isTrue hqb => rw [if_pos hqb]; omega
    | isFalse hqb =>
      rw [if_neg hqb]
      have hmL : q ∈ L := by
        cases List.mem_cons.mp h with
        | inl he => exact absurd he hqb
        | inr hm => exact hm
      have hh := ih hmL
      omega

/-- **B2**: pfcCount q L ≠ 0 なら q ∈ L。 -/
theorem b5_mem_of_count_pos (q : Nat) :
    ∀ (L : List Nat), pfcCount q L ≠ 0 → q ∈ L := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons b L ih =>
    intro h
    have hc : (if q = b then 1 else 0) + pfcCount q L ≠ 0 := h
    cases Nat.decEq q b with
    | isTrue hqb => exact List.mem_cons.mpr (Or.inl hqb)
    | isFalse hqb =>
      rw [if_neg hqb] at hc
      have hL : pfcCount q L ≠ 0 := by omega
      exact List.mem_cons.mpr (Or.inr (ih hL))

/-- **B3**: pfcCount q L = 0 なら q ∉ L。 -/
theorem b5_not_mem_of_count_zero (q : Nat) (L : List Nat)
    (h : pfcCount q L = 0) : q ∉ L :=
  fun hm => b5_count_pos_of_mem q L hm h

/-! ## L 層: 重複除去 b5Dedup（choice なし・自前 `=` 決定） -/

/-- 重複除去（Nat の `=` 決定、choice なし）。pfcCount による非依存 if。 -/
def b5Dedup : List Nat → List Nat
  | [] => []
  | q :: L => if pfcCount q (b5Dedup L) = 0 then q :: b5Dedup L else b5Dedup L

/-- **L1**: q ∈ b5Dedup L ↔ q ∈ L。 -/
theorem b5_dedup_mem : ∀ (L : List Nat) (q : Nat), q ∈ b5Dedup L ↔ q ∈ L := by
  intro L
  induction L with
  | nil => intro q; exact Iff.rfl
  | cons b L ih =>
    intro q
    show q ∈ (if pfcCount b (b5Dedup L) = 0 then b :: b5Dedup L else b5Dedup L)
       ↔ q ∈ (b :: L)
    cases Nat.decEq (pfcCount b (b5Dedup L)) 0 with
    | isTrue hz =>
      rw [if_pos hz]
      apply Iff.intro
      · intro hm
        cases List.mem_cons.mp hm with
        | inl he => exact List.mem_cons.mpr (Or.inl he)
        | inr hd => exact List.mem_cons.mpr (Or.inr ((ih q).mp hd))
      · intro hm
        cases List.mem_cons.mp hm with
        | inl he => exact List.mem_cons.mpr (Or.inl he)
        | inr hL => exact List.mem_cons.mpr (Or.inr ((ih q).mpr hL))
    | isFalse hz =>
      rw [if_neg hz]
      have hbL : b ∈ L := (ih b).mp (b5_mem_of_count_pos b (b5Dedup L) hz)
      apply Iff.intro
      · intro hm
        exact List.mem_cons.mpr (Or.inr ((ih q).mp hm))
      · intro hm
        cases List.mem_cons.mp hm with
        | inl he =>
          have hqL : q ∈ L := by rw [he]; exact hbL
          exact (ih q).mpr hqL
        | inr hL => exact (ih q).mpr hL

/-- **L2**: q ∈ L なら pfcCount q (b5Dedup L) = 1（重複除去後は count 1）。 -/
theorem b5_dedup_count_one (q : Nat) :
    ∀ (L : List Nat), q ∈ L → pfcCount q (b5Dedup L) = 1 := by
  intro L
  induction L with
  | nil => intro hq; cases hq
  | cons b L ih =>
    intro hq
    show pfcCount q (if pfcCount b (b5Dedup L) = 0 then b :: b5Dedup L else b5Dedup L) = 1
    cases Nat.decEq (pfcCount b (b5Dedup L)) 0 with
    | isTrue hz =>
      rw [if_pos hz]
      show (if q = b then 1 else 0) + pfcCount q (b5Dedup L) = 1
      cases Nat.decEq q b with
      | isTrue hqb =>
        rw [if_pos hqb]
        have hcz : pfcCount q (b5Dedup L) = 0 := by rw [hqb]; exact hz
        rw [hcz]
      | isFalse hqb =>
        rw [if_neg hqb]
        have hmL : q ∈ L := by
          cases List.mem_cons.mp hq with
          | inl he => exact absurd he hqb
          | inr hm => exact hm
        rw [ih hmL]
    | isFalse hz =>
      rw [if_neg hz]
      have hbL : b ∈ L := (b5_dedup_mem L b).mp (b5_mem_of_count_pos b (b5Dedup L) hz)
      cases Nat.decEq q b with
      | isTrue hqb =>
        have hmL : q ∈ L := by rw [hqb]; exact hbL
        exact ih hmL
      | isFalse hqb =>
        have hmL : q ∈ L := by
          cases List.mem_cons.mp hq with
          | inl he => exact absurd he hqb
          | inr hm => exact hm
        exact ih hmL

/-! ## F 層: 有限台積の congruence と指示子 -/

/-- **F2**: fspProd の congruence（S 上で f=g なら積が一致）。 -/
theorem b5_fsp_congr (f g : Nat → QRat) :
    ∀ (S : List Nat), (∀ p, p ∈ S → f p = g p) → fspProd f S = fspProd g S := by
  intro S
  induction S with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    show ratRing.mul (f p) (fspProd f rest) = ratRing.mul (g p) (fspProd g rest)
    rw [h p (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq)))]

/-- **F4**: 指示子の積 — count q S = 1 なら ∏_{p∈S}(if p=q then b5N p else 1) = b5N q。 -/
theorem b5_prod_indicator (q : Nat) :
    ∀ (S : List Nat), pfcCount q S = 1 →
      fspProd (fun p => if p = q then b5N p else ratRing.one) S = b5N q := by
  intro S
  induction S with
  | nil =>
    intro h
    have h0 : (0 : Nat) = 1 := h
    exact absurd h0 (by omega)
  | cons b S ih =>
    intro h
    have hc : (if q = b then 1 else 0) + pfcCount q S = 1 := h
    show ratRing.mul (if b = q then b5N b else ratRing.one)
           (fspProd (fun p => if p = q then b5N p else ratRing.one) S) = b5N q
    cases Nat.decEq b q with
    | isTrue hbq =>
      rw [if_pos hbq]
      have hqb : q = b := hbq.symm
      have hcount : pfcCount q S = 0 := by rw [if_pos hqb] at hc; omega
      have htriv : fspProd (fun p => if p = q then b5N p else ratRing.one) S
                 = ratRing.one := by
        apply fsp_prod_trivial_on
        intro p hp
        have hpq : p ≠ q := by
          intro he
          exact b5_not_mem_of_count_zero q S hcount (he ▸ hp)
        rw [if_neg hpq]
      rw [htriv, fsp_rat_mul_one, hbq]
    | isFalse hbq =>
      rw [if_neg hbq]
      have hqb : q ≠ b := fun he => hbq he.symm
      have hcount : pfcCount q S = 1 := by rw [if_neg hqb] at hc; omega
      rw [ratRing.one_mul, ih hcount]

/-! ## R 層: ∏_{p∈S} p^{count_L(p)} = listProd L（核・組み替え） -/

/-- **R2（核・最重量）**: count q S = 1 (q∈L) の下で
    ∏_{p∈S} b5N(p^{count_L(p)}) = b5N(listProd L)。重複込みリスト L を 1 因子ずつ
    剥がす帰納。S 側には素数性も nodup も不要（L⊆S も不要、count 条件のみ）。 -/
theorem b5_prod_pow_count :
    ∀ (L S : List Nat), (∀ q, q ∈ L → pfcCount q S = 1) →
      fspProd (fun p => b5N (p ^ pfcCount p L)) S = b5N (listProd L) := by
  intro L
  induction L with
  | nil =>
    intro S _
    have hfun : ∀ p, p ∈ S →
        (fun p => b5N (p ^ pfcCount p ([] : List Nat))) p = ratRing.one := by
      intro p _
      show b5N (p ^ pfcCount p ([] : List Nat)) = ratRing.one
      show b5N (p ^ 0) = ratRing.one
      rw [Nat.pow_zero]
      exact b5N_one
    rw [fsp_prod_trivial_on _ S hfun]
    show ratRing.one = b5N (listProd ([] : List Nat))
    show ratRing.one = b5N 1
    exact b5N_one.symm
  | cons q L ih =>
    intro S hcnt
    have hstep : ∀ p, p ∈ S →
        (fun p => b5N (p ^ pfcCount p (q :: L))) p
          = (fun p => ratRing.mul (if p = q then b5N p else ratRing.one)
                        (b5N (p ^ pfcCount p L))) p := by
      intro p _
      show b5N (p ^ ((if p = q then 1 else 0) + pfcCount p L))
         = ratRing.mul (if p = q then b5N p else ratRing.one) (b5N (p ^ pfcCount p L))
      cases Nat.decEq p q with
      | isTrue h => rw [if_pos h, if_pos h, Nat.pow_add, Nat.pow_one, b5N_mul]
      | isFalse h => rw [if_neg h, if_neg h, Nat.pow_add, Nat.pow_zero, b5N_mul, b5N_one]
    have hsplit :
        fspProd (fun p => ratRing.mul (if p = q then b5N p else ratRing.one)
            (b5N (p ^ pfcCount p L))) S
          = ratRing.mul
              (fspProd (fun p => if p = q then b5N p else ratRing.one) S)
              (fspProd (fun p => b5N (p ^ pfcCount p L)) S) :=
      fsp_prod_mul_pointwise (fun p => if p = q then b5N p else ratRing.one)
        (fun p => b5N (p ^ pfcCount p L)) S
    rw [b5_fsp_congr (fun p => b5N (p ^ pfcCount p (q :: L)))
          (fun p => ratRing.mul (if p = q then b5N p else ratRing.one)
                      (b5N (p ^ pfcCount p L))) S hstep,
      hsplit,
      b5_prod_indicator q S (hcnt q (List.mem_cons.mpr (Or.inl rfl))),
      ih S (fun r hr => hcnt r (List.mem_cons.mpr (Or.inr hr))),
      ← b5N_mul]
    show b5N (q * listProd L) = b5N (q * listProd L)
    rfl

/-- **R3**: p 進 multiplicity 版。S の各元が素数で count 1 なら
    ∏_{p∈S} b5N(p^{v_p(n)}) = b5N n。 -/
theorem b5_prod_pow_val (n : Nat) (hn : 1 ≤ n) (S : List Nat)
    (hpr : ∀ p, p ∈ S → IsPrime p)
    (hcnt : ∀ q, q ∈ pfcFactors n → pfcCount q S = 1) :
    fspProd (fun p => b5N (p ^ pvqNatVal p n)) S = b5N n := by
  have hcongr : fspProd (fun p => b5N (p ^ pvqNatVal p n)) S
              = fspProd (fun p => b5N (p ^ pfcCount p (pfcFactors n))) S := by
    apply b5_fsp_congr
    intro p hp
    show b5N (p ^ pvqNatVal p n) = b5N (p ^ pfcCount p (pfcFactors n))
    rw [pfc_vp_count n p hn (hpr p hp)]
  rw [hcongr, b5_prod_pow_count (pfcFactors n) S hcnt, pfc_prod_factors n hn]

/-! ## Support 層: num·den の素因子（重複なし） -/

/-- 積公式の有限台: num・den を割る素数のリスト（重複除去済）。 -/
def b5Support (x : PreRat) : List Nat :=
  b5Dedup (pfcFactors x.num.natAbs ++ pfcFactors x.den.natAbs)

/-- **S1**: 台の membership = num 側 ∨ den 側。 -/
theorem b5_support_mem (x : PreRat) (q : Nat) :
    q ∈ b5Support x ↔
      (q ∈ pfcFactors x.num.natAbs ∨ q ∈ pfcFactors x.den.natAbs) :=
  Iff.trans
    (b5_dedup_mem (pfcFactors x.num.natAbs ++ pfcFactors x.den.natAbs) q)
    List.mem_append

/-- **S2**: 台の全要素は素数。 -/
theorem b5_support_prime (x : PreRat) (hx : x.num ≠ 0) :
    ∀ p, p ∈ b5Support x → IsPrime p := by
  intro p hp
  cases (b5_support_mem x p).mp hp with
  | inl h => exact pfc_factors_prime x.num.natAbs p (natAbs_pos_of_ne hx) h
  | inr h => exact pfc_factors_prime x.den.natAbs p (natAbs_den_pos x) h

/-- **S3**: 台内の count は 1。 -/
theorem b5_support_count (x : PreRat) (q : Nat)
    (h : q ∈ pfcFactors x.num.natAbs ∨ q ∈ pfcFactors x.den.natAbs) :
    pfcCount q (b5Support x) = 1 :=
  b5_dedup_count_one q _ (List.mem_append.mpr h)

/-! ## Q 層: num 側・den 側の積 -/

/-- **Q1**: ∏_{p∈S} b5N(p^{v_p(|num|)}) = b5N|num|。 -/
theorem b5_prod_num (x : PreRat) (hx : x.num ≠ 0) :
    fspProd (fun p => b5N (p ^ pvqNatVal p x.num.natAbs)) (b5Support x)
      = b5N x.num.natAbs := by
  apply b5_prod_pow_val x.num.natAbs (natAbs_pos_of_ne hx) (b5Support x)
    (b5_support_prime x hx)
  intro q hq
  exact b5_support_count x q (Or.inl hq)

/-- **Q2**: ∏_{p∈S} b5N(p^{v_p(den)}) = b5N den。 -/
theorem b5_prod_den (x : PreRat) (hx : x.num ≠ 0) :
    fspProd (fun p => b5N (p ^ pvqNatVal p x.den.natAbs)) (b5Support x)
      = b5N x.den.natAbs := by
  apply b5_prod_pow_val x.den.natAbs (natAbs_den_pos x) (b5Support x)
    (b5_support_prime x hx)
  intro q hq
  exact b5_support_count x q (Or.inr hq)

/-! ## P1: 各素数の p 進 cleared 恒等式 |x|_p · p^{v_p(|num|)} = p^{v_p(den)} -/

/-- **P1**: 素数 p で |x|_p · b5N(p^{v_p(|num|)}) = b5N(p^{v_p(den)})。
    |x|_p = p^{-(v_p(a)-v_p(b))} なので両辺は p^{v_p(b)}。負冪 v:Int は Int.toNat
    の符号恒等式 (-v).toNat + va = vb + v.toNat（omega）に閉じ込め、Nat.pow_add で
    交差積を束ねる。 -/
theorem b5_pav_cleared (p : Nat) (hp : IsPrime p) (x : PreRat) :
    ratRing.mul (pavAbs p x) (b5N (p ^ pvqNatVal p x.num.natAbs))
      = b5N (p ^ pvqNatVal p x.den.natAbs) := by
  have hp0 : ¬ p = 0 := by have := hp.1; omega
  have hpb : pavBase p = p := by
    show (if p = 0 then 1 else p) = p
    rw [if_neg hp0]
  -- 指数の Nat 恒等式
  have hv : pvqVal p x
          = ((pvqNatVal p x.num.natAbs : Int)) - ((pvqNatVal p x.den.natAbs : Int)) := rfl
  have he : (-(pvqVal p x)).toNat + pvqNatVal p x.num.natAbs
          = pvqNatVal p x.den.natAbs + (pvqVal p x).toNat := by
    rw [hv]; omega
  have key : p ^ (-(pvqVal p x)).toNat * p ^ pvqNatVal p x.num.natAbs
           = p ^ pvqNatVal p x.den.natAbs * p ^ (pvqVal p x).toNat := by
    rw [← Nat.pow_add, ← Nat.pow_add, he]
  apply Quot.sound
  show ((pavBase p ^ (-(pvqVal p x)).toNat : Nat) : Int)
         * ((p ^ pvqNatVal p x.num.natAbs : Nat) : Int) * 1
     = ((p ^ pvqNatVal p x.den.natAbs : Nat) : Int)
         * (((pavBase p ^ (pvqVal p x).toNat : Nat) : Int) * 1)
  rw [hpb, Int.mul_one, Int.mul_one, ← Int.natCast_mul, ← Int.natCast_mul, key]

/-! ## G1: p 進側 cleared form  P · α = β -/

/-- **G1**: ∏_p|x|_p · b5N|num| = b5N den。 -/
theorem b5_padic_cleared (x : PreRat) (hx : x.num ≠ 0) :
    ratRing.mul (fspProd (fun p => pavAbs p x) (b5Support x)) (b5N x.num.natAbs)
      = b5N x.den.natAbs := by
  have hmerge :
      ratRing.mul (fspProd (fun p => pavAbs p x) (b5Support x))
        (fspProd (fun p => b5N (p ^ pvqNatVal p x.num.natAbs)) (b5Support x))
      = fspProd (fun p => ratRing.mul (pavAbs p x)
          (b5N (p ^ pvqNatVal p x.num.natAbs))) (b5Support x) :=
    (fsp_prod_mul_pointwise (fun p => pavAbs p x)
      (fun p => b5N (p ^ pvqNatVal p x.num.natAbs)) (b5Support x)).symm
  rw [← b5_prod_num x hx, hmerge,
    b5_fsp_congr
      (fun p => ratRing.mul (pavAbs p x) (b5N (p ^ pvqNatVal p x.num.natAbs)))
      (fun p => b5N (p ^ pvqNatVal p x.den.natAbs)) (b5Support x)
      (fun p hp => b5_pav_cleared p (b5_support_prime x hx p hp) x)]
  exact b5_prod_den x hx

/-! ## A1: アルキメデス側 cleared form  A · β = α（avi 非依存） -/

/-- **A1**: |x|_∞ · b5N den = b5N|num|。arpAbs=qAbs の展開 + Quot.sound。 -/
theorem b5_arch_cleared (x : PreRat) :
    ratRing.mul (arpAbs (Quot.mk ratRel x)) (b5N x.den.natAbs) = b5N x.num.natAbs := by
  apply Quot.sound
  show intAbs x.num * ((x.den.natAbs : Nat) : Int) * 1
     = ((x.num.natAbs : Nat) : Int) * (x.den * 1)
  have hden : ((x.den.natAbs : Int)) = x.den := by
    have h := x.den_pos; omega
  rw [b5_intAbs_natAbs, Int.mul_one, Int.mul_one, hden]

/-! ## FINAL: 積公式 |x|_∞ · ∏_p|x|_p = 1 -/

/-- **B5 積公式（ℚ、実）** — 非零有理数 x（PreRat 代表・x.num ≠ 0）に対し
    |x|_∞ · ∏_{p ∈ Supp(x)} |x|_p = 1。
    台 Supp(x) = num·den を割る素数全体（それ以外の p では |x|_p = 1）。 -/
theorem b5_product_formula (x : PreRat) (hx : x.num ≠ 0) :
    ratRing.mul (arpAbs (Quot.mk ratRel x))
      (fspProd (fun p => pavAbs p x) (b5Support x))
    = ratRing.one := by
  have hA1 : ratRing.mul (arpAbs (Quot.mk ratRel x)) (b5N x.den.natAbs)
           = b5N x.num.natAbs := b5_arch_cleared x
  have hG1 : ratRing.mul (fspProd (fun p => pavAbs p x) (b5Support x))
               (b5N x.num.natAbs) = b5N x.den.natAbs := b5_padic_cleared x hx
  have hnz : (intToPreRat (x.num.natAbs : Int)).num ≠ 0 := by
    show (x.num.natAbs : Int) ≠ 0
    have h1 := natAbs_pos_of_ne hx
    omega
  have hinv : ratRing.mul (b5N x.num.natAbs) (qInv (b5N x.num.natAbs)) = ratRing.one :=
    qMul_inv (intToPreRat (x.num.natAbs : Int)) hnz
  have h1 : ratRing.mul
              (ratRing.mul (arpAbs (Quot.mk ratRel x))
                (fspProd (fun p => pavAbs p x) (b5Support x)))
              (b5N x.num.natAbs)
          = b5N x.num.natAbs := by
    rw [ratRing.mul_assoc, hG1, hA1]
  calc ratRing.mul (arpAbs (Quot.mk ratRel x))
          (fspProd (fun p => pavAbs p x) (b5Support x))
      = ratRing.mul (ratRing.mul (arpAbs (Quot.mk ratRel x))
            (fspProd (fun p => pavAbs p x) (b5Support x))) ratRing.one :=
        (fsp_rat_mul_one _).symm
    _ = ratRing.mul (ratRing.mul (arpAbs (Quot.mk ratRel x))
            (fspProd (fun p => pavAbs p x) (b5Support x)))
            (ratRing.mul (b5N x.num.natAbs) (qInv (b5N x.num.natAbs))) := by
        rw [hinv]
    _ = ratRing.mul (ratRing.mul (ratRing.mul (arpAbs (Quot.mk ratRel x))
            (fspProd (fun p => pavAbs p x) (b5Support x))) (b5N x.num.natAbs))
            (qInv (b5N x.num.natAbs)) :=
        (ratRing.mul_assoc _ _ _).symm
    _ = ratRing.mul (b5N x.num.natAbs) (qInv (b5N x.num.natAbs)) := by rw [h1]
    _ = ratRing.one := hinv

end IUT
