/-
  IUT/PrimeFactorization.lean — B5 積公式の基礎スライス:
  「算術の基本定理（存在・積形）」と p 進 multiplicity の一致

  分類: [実] / complete_pct 影響: 判定は独立監査に委ねる（本ファイルでは
  complete_pct を設定しない）。実 Nat（n ≥ 1 の本物の自然数）上で、模型・
  surrogate・toy を一切使わずに、素因数分解の存在（積が n に戻る）と、各素数の
  p 進付値 v_p(n) が分解リスト中の出現回数に一致することを from-scratch 証明する。

  * `listProd` — 自然数リストの積（自前定義）。
  * `pfcCount` — 命題等号 `=` に基づく自前の出現回数カウント。
    （core の `List.count` は `BEq` ベースで、本リポジトリの禁止タクティク
      simp/decide 無しでの取り扱いが非現実的なため、忠実な自前版を用いる。
      正直な限定: 目標の `.count` ではなく `pfcCount` を主語にしている。）
  * `pfcAux` / `pfcFactors` — 最小素因子 q = leastDivisorFrom を取り出して
    n/q に降下する fuel 有界再帰（fuel = n）。重複込みの素因数リストを返す。
  * `leastDivisor_prime` — leastDivisorFrom n (n-1) 2 は素数
    （prime_factor_exists と同じ最小性論法）。
  * `pfc_prod_factors` — **∏(重複込み素因数) = n**（基本定理の存在・積形）。
  * `pfc_factors_prime` — 分解リストの要素は全て素数。
  * `pvqNatVal_prime` — v_p(q) = (if p = q then 1 else 0)（p, q 素数）。
  * `pfc_vp_count` — **v_p(n) = pfcCount p (pfcFactors n)**（p 進 multiplicity =
    分解リスト中の p の出現回数）。pvq_natval_mul / pvqNatVal_spec を活用。
  * `pfc_prod_primepow` — 本丸「∏_p p^{v_p(n)} = n」の**忠実な重複込み版**:
    `listProd(pfcFactors n) = n` かつ「各素数 p で v_p(n) = pfcCount p (list)」を
    束ねたもの。これは multiset 形の素冪分解に等しい。

  正直な限定:
  - distinct 素数上の ∏_p p^{v_p(n)} の「相異なる素数への重複除去」版は未実装。
    重複込みリスト + 出現回数（multiplicity）で忠実に表現した（誤魔化しなし）。
  - 対象は n ≥ 1 の実 Nat のみ（n = 0 は素因数分解の対象外）。
  - 出現回数は core `List.count`（BEq 版）ではなく自前 `pfcCount`（= 版）。

  既存の本物資産を interface のまま再利用（再定義せず）:
    pvqNatVal / pvqNatVal_spec / pvq_natval_mul（PadicValuationQ）、
    IsPrime / euclid（Fermat）、leastDivisorFrom / leastDivisorFrom_dvd /
    leastDivisorFrom_ge / leastDivisorFrom_min / prime_factor_exists の論法
    （NatPrimeParts）。

  全て選択公理不使用・sorry なし。§2(b) 本物建設（B5 積公式の基礎スライス）。
-/
import IUT.PadicValuationQ

namespace IUT

/-! ## 補助定義: リスト積と出現回数 -/

/-- **自然数リストの積**（自前定義）。listProd [] = 1, listProd (a::l) = a·∏l。 -/
def listProd : List Nat → Nat
  | [] => 1
  | a :: l => a * listProd l

/-- **出現回数**（命題等号版・自前定義）。core の BEq 版 `List.count` を避け、
    `if a = b` で数える。simp/decide 不要で rw 可能。 -/
def pfcCount (a : Nat) : List Nat → Nat
  | [] => 0
  | b :: l => (if a = b then 1 else 0) + pfcCount a l

/-! ## 最小素因子が素数であること -/

/-- **leastDivisorFrom n (n-1) 2 は素数** — prime_factor_exists と同じ
    最小性論法（2 ≤ d, d ∣ n, d 未満に n の約数なし ⇒ 約数は 1 か d のみ）。 -/
theorem leastDivisor_prime (n : Nat) (hn : 2 ≤ n) :
    IsPrime (leastDivisorFrom n (n - 1) 2) := by
  have hdvd : leastDivisorFrom n (n - 1) 2 ∣ n :=
    leastDivisorFrom_dvd n hn (n - 1) 2 (by omega)
  have hge : 2 ≤ leastDivisorFrom n (n - 1) 2 :=
    leastDivisorFrom_ge n hn (n - 1) 2 (by omega)
  have hmin : ∀ e, 2 ≤ e → e < leastDivisorFrom n (n - 1) 2 → ¬ e ∣ n :=
    fun e he1 he2 => leastDivisorFrom_min n hn (n - 1) 2 (by omega) (by omega) e he1 he2
  refine ⟨hge, ?_⟩
  intro k hk
  have hkd : k ∣ n := Nat.dvd_trans hk hdvd
  have hk0 : k ≠ 0 := by
    intro h0
    subst h0
    have := Nat.eq_zero_of_zero_dvd hk
    omega
  cases Nat.lt_or_ge k 2 with
  | inl h => left; omega
  | inr h2 =>
    right
    cases Nat.lt_or_ge k (leastDivisorFrom n (n - 1) 2) with
    | inl hlt => exact absurd hkd (hmin k h2 hlt)
    | inr hge2 =>
      have hkd2 : k ≤ leastDivisorFrom n (n - 1) 2 := Nat.le_of_dvd (by omega) hk
      omega

/-! ## 素因数分解の再帰核 -/

/-- **素因数分解核** — 2 ≤ n の限り最小素因子 q を取り出し n/q に降下する
    fuel 有界再帰。重複込みの素因数リストを返す。 -/
def pfcAux : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n =>
    if 2 ≤ n then
      leastDivisorFrom n (n - 1) 2 :: pfcAux fuel (n / leastDivisorFrom n (n - 1) 2)
    else []

/-- 展開等式（fuel の後続段、rfl）。 -/
theorem pfcAux_succ (fuel n : Nat) :
    pfcAux (fuel + 1) n =
      if 2 ≤ n then
        leastDivisorFrom n (n - 1) 2 :: pfcAux fuel (n / leastDivisorFrom n (n - 1) 2)
      else [] := rfl

/-- **素因数分解** — fuel = n を与えた重複込み素因数リスト。 -/
def pfcFactors (n : Nat) : List Nat := pfcAux n n

/-! ## 積が n に戻る（基本定理の存在・積形） -/

/-- **fuel 版**: 1 ≤ n ≤ fuel なら分解リストの積は n。 -/
theorem pfcAux_prod : ∀ fuel n, 1 ≤ n → n ≤ fuel → listProd (pfcAux fuel n) = n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn hnf
    exfalso; omega
  | succ fuel ih =>
    intro n hn hnf
    rw [pfcAux_succ]
    cases Nat.lt_or_ge n 2 with
    | inl hlt =>
      rw [if_neg (by omega : ¬ 2 ≤ n)]
      show (1 : Nat) = n
      omega
    | inr hle =>
      rw [if_pos hle]
      have key : ∀ q, q = leastDivisorFrom n (n - 1) 2 →
          listProd (q :: pfcAux fuel (n / q)) = n := by
        intro q hq
        have hqdvd : q ∣ n := by
          rw [hq]; exact leastDivisorFrom_dvd n hle (n - 1) 2 (by omega)
        have hqge : 2 ≤ q := by
          rw [hq]; exact leastDivisorFrom_ge n hle (n - 1) 2 (by omega)
        have hm0 : n / q * q = n := Nat.div_mul_cancel hqdvd
        have hm : q * (n / q) = n := by
          rw [Nat.mul_comm q (n / q)]; exact hm0
        have hmpos : 1 ≤ n / q := by
          cases Nat.eq_zero_or_pos (n / q) with
          | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hm; omega
          | inr h => exact h
        have h2q : 2 * (n / q) ≤ q * (n / q) := Nat.mul_le_mul hqge (Nat.le_refl (n / q))
        rw [hm] at h2q
        have hbound : n / q ≤ fuel := by omega
        show q * listProd (pfcAux fuel (n / q)) = n
        rw [ih (n / q) hmpos hbound]
        exact hm
      exact key _ rfl

/-- **算術の基本定理（存在・積形）** — n ≥ 1 の素因数（重複込み）分解の積は n。 -/
theorem pfc_prod_factors (n : Nat) (hn : 1 ≤ n) : listProd (pfcFactors n) = n := by
  show listProd (pfcAux n n) = n
  exact pfcAux_prod n n hn (Nat.le_refl n)

/-! ## 分解の要素は全て素数 -/

/-- **fuel 版**: 分解リストの要素は素数。 -/
theorem pfcAux_prime : ∀ fuel n, 1 ≤ n → n ≤ fuel →
    ∀ p, p ∈ pfcAux fuel n → IsPrime p := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn hnf
    exfalso; omega
  | succ fuel ih =>
    intro n hn hnf p hp
    rw [pfcAux_succ] at hp
    cases Nat.lt_or_ge n 2 with
    | inl hlt =>
      rw [if_neg (by omega : ¬ 2 ≤ n)] at hp
      cases hp
    | inr hle =>
      rw [if_pos hle] at hp
      have key : ∀ q, q = leastDivisorFrom n (n - 1) 2 →
          p ∈ (q :: pfcAux fuel (n / q)) → IsPrime p := by
        intro q hq hpm
        have hqdvd : q ∣ n := by
          rw [hq]; exact leastDivisorFrom_dvd n hle (n - 1) 2 (by omega)
        have hqge : 2 ≤ q := by
          rw [hq]; exact leastDivisorFrom_ge n hle (n - 1) 2 (by omega)
        have hqprime : IsPrime q := by
          rw [hq]; exact leastDivisor_prime n hle
        cases hpm with
        | head _ => exact hqprime
        | tail _ htl =>
          have hm0 : n / q * q = n := Nat.div_mul_cancel hqdvd
          have hm : q * (n / q) = n := by
            rw [Nat.mul_comm q (n / q)]; exact hm0
          have hmpos : 1 ≤ n / q := by
            cases Nat.eq_zero_or_pos (n / q) with
            | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hm; omega
            | inr h => exact h
          have h2q : 2 * (n / q) ≤ q * (n / q) := Nat.mul_le_mul hqge (Nat.le_refl (n / q))
          rw [hm] at h2q
          have hbound : n / q ≤ fuel := by omega
          exact ih (n / q) hmpos hbound p htl
      exact key _ rfl hp

/-- **分解の要素は素数** — pfcFactors n の全要素は素数。 -/
theorem pfc_factors_prime (n p : Nat) (hn : 1 ≤ n) (hp : p ∈ pfcFactors n) :
    IsPrime p :=
  pfcAux_prime n n hn (Nat.le_refl n) p hp

/-! ## 素数の p 進付値: v_p(q) = if p = q then 1 else 0 -/

/-- **v_p(q)（p, q 素数）** — p = q なら 1、そうでなければ 0。
    pvqNatVal_spec を p = q（q = q^1·1）と p ≠ q（q = p^0·q, p∤q）に適用。 -/
theorem pvqNatVal_prime (p q : Nat) (hp : IsPrime p) (hq : IsPrime q) :
    pvqNatVal p q = if p = q then 1 else 0 := by
  have hp2 : 2 ≤ p := hp.1
  have hdec : p = q ∨ ¬ p = q :=
    match Nat.decEq p q with
    | isTrue h => Or.inl h
    | isFalse h => Or.inr h
  cases hdec with
  | inl h =>
    rw [if_pos h, h]
    have hq2 : 2 ≤ q := hq.1
    have hnd1 : ¬ q ∣ 1 := by
      intro hd; have := Nat.le_of_dvd (by omega) hd; omega
    have hs := pvqNatVal_spec q hq2 1 1 hnd1 (by omega)
    rw [Nat.pow_one, Nat.mul_one] at hs
    exact hs
  | inr h =>
    rw [if_neg h]
    have hnd : ¬ p ∣ q := by
      intro hd
      cases hq.2 p hd with
      | inl h1 => omega
      | inr h1 => exact h h1
    have hq1 : 1 ≤ q := by have := hq.1; omega
    have hs := pvqNatVal_spec p hp2 0 q hnd hq1
    rw [Nat.pow_zero, Nat.one_mul] at hs
    exact hs

/-! ## p 進 multiplicity = 分解リスト中の出現回数 -/

/-- **fuel 版**: v_p(n) は分解リスト中の p の出現回数に一致。 -/
theorem pfcAux_vp_count : ∀ fuel n, 1 ≤ n → n ≤ fuel →
    ∀ p, IsPrime p → pvqNatVal p n = pfcCount p (pfcAux fuel n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn hnf
    exfalso; omega
  | succ fuel ih =>
    intro n hn hnf p hp
    rw [pfcAux_succ]
    cases Nat.lt_or_ge n 2 with
    | inl hlt =>
      rw [if_neg (by omega : ¬ 2 ≤ n)]
      show pvqNatVal p n = 0
      have hn1 : n = 1 := by omega
      rw [hn1]
      have hp2 : 2 ≤ p := hp.1
      have hnd1 : ¬ p ∣ 1 := by
        intro hd; have := Nat.le_of_dvd (by omega) hd; omega
      have hs := pvqNatVal_spec p hp2 0 1 hnd1 (by omega)
      rw [Nat.pow_zero, Nat.one_mul] at hs
      exact hs
    | inr hle =>
      rw [if_pos hle]
      have key : ∀ q, q = leastDivisorFrom n (n - 1) 2 →
          pvqNatVal p n = pfcCount p (q :: pfcAux fuel (n / q)) := by
        intro q hq
        have hqdvd : q ∣ n := by
          rw [hq]; exact leastDivisorFrom_dvd n hle (n - 1) 2 (by omega)
        have hqge : 2 ≤ q := by
          rw [hq]; exact leastDivisorFrom_ge n hle (n - 1) 2 (by omega)
        have hqprime : IsPrime q := by
          rw [hq]; exact leastDivisor_prime n hle
        have hm0 : n / q * q = n := Nat.div_mul_cancel hqdvd
        have hm : q * (n / q) = n := by
          rw [Nat.mul_comm q (n / q)]; exact hm0
        have hmpos : 1 ≤ n / q := by
          cases Nat.eq_zero_or_pos (n / q) with
          | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hm; omega
          | inr h => exact h
        have h2q : 2 * (n / q) ≤ q * (n / q) := Nat.mul_le_mul hqge (Nat.le_refl (n / q))
        rw [hm] at h2q
        have hbound : n / q ≤ fuel := by omega
        show pvqNatVal p n = (if p = q then 1 else 0) + pfcCount p (pfcAux fuel (n / q))
        rw [← ih (n / q) hmpos hbound p hp]
        have hpq : pvqNatVal p q = (if p = q then 1 else 0) :=
          pvqNatVal_prime p q hp hqprime
        rw [← hpq]
        have hmul := pvq_natval_mul p hp q (n / q) (by omega) hmpos
        rw [hm] at hmul
        exact hmul
      exact key _ rfl

/-- **p 進 multiplicity の一致** — p 素数・n ≥ 1 で
    v_p(n) = pfcCount p (pfcFactors n)（付値 = 分解リスト中の出現回数）。 -/
theorem pfc_vp_count (n p : Nat) (hn : 1 ≤ n) (hp : IsPrime p) :
    pvqNatVal p n = pfcCount p (pfcFactors n) := by
  show pvqNatVal p n = pfcCount p (pfcAux n n)
  exact pfcAux_vp_count n n hn (Nat.le_refl n) p hp

/-! ## 本丸: ∏_p p^{v_p(n)} = n の忠実な重複込み版 -/

/-- **本丸（重複込み版）** — 「∏_p p^{v_p(n)} = n」の multiset 形忠実表現:
    (1) 重複込み素因数リストの積が n に戻り、
    (2) 各素数 p の p 進付値 v_p(n) がそのリスト中の p の出現回数に一致する。
    (1)(2) を合わせると「n = ∏(素因数, 重複込み) で各素数の重複度が v_p(n)」であり、
    ∏_p p^{v_p(n)} = n の multiset 版に等しい。distinct 素数への重複除去版は未実装
    （正直な限定・ヘッダ参照）。 -/
theorem pfc_prod_primepow (n : Nat) (hn : 1 ≤ n) :
    listProd (pfcFactors n) = n ∧
      ∀ p, IsPrime p → pvqNatVal p n = pfcCount p (pfcFactors n) :=
  ⟨pfc_prod_factors n hn, fun p hp => pfc_vp_count n p hn hp⟩

end IUT
