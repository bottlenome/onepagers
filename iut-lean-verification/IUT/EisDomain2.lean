/-
  IUT/EisDomain2.lean — M96F（柱B: O = ℤ_p[π] の witness 付き整域性・
  第二段 — λ 進付値分解と一般の積の非零性、M93F の正直申告分の回収）

  M93F は被約係数写像 cᵢ の well-definedness・λ シフト両方向・
  witness 付き λ 割り算・剰余体乗法性を供給した。本モジュールは
  その続編であり、M91F が ℤ_p で行った付値分解→積の非零性の道筋を
  O 上で完遂する。鍵は witness (i, n) の**測度** μ = i + (n−1)(p−1)
  である: λ 倍は μ をちょうど 1 上げる（域内シフトは i を +1、
  巻き戻りは (p−2, n) → (0, n+1)）ので、逆に λ 割り算は μ を 1 下げ、
  μ に関する強帰納法（燃料 m による構造的再帰）が回る。割り算の
  可否は 0 番被約係数のレベル 1 成分の Bool 値 0 判定（M91F の
  zmodIsZero）で**データ構成の中で**場合分けする。

  * M96F-0 `eisNeZeroAt_zero_elim` / `eisNeZeroAt_lambda_mul_rev` /
    `eisNeZeroAt_lambda_wrap_rev` / `eisDivLambda` / `eisDivLambda_spec`
    — 簿記: レベル 0 witness の不成立、λ シフト簿記の**逆向き**
    （λ·x′ の witness から x′ の witness を抽出: 域内は添字 −1、
    巻き戻りは (0, n+1) → (p−2, n)、p キャンセルは val_zero_p_mul）、
    剰余 0 のときの λ 割り算の関数化（zpDivP による商の明示構成）
  * M96F-1 `EisValDecomp` / `eisValDecompose` / `eis_valuation_exists`
    （本丸その一）— **witness 付き λ 進付値分解**: (i, n)-witness を
    持つ x について x = λ^k·u、u は単数剰余（(0,1)-witness）、
    k ≤ i + (n−1)(p−1)。Σ 型構造体としてデータで返す（測度の
    強帰納法 + Bool 判定、排中律不使用）。∃ 版は商の元上で供給
  * M96F-2 `cring_mul_mul_comm` / `eis_lambda_pow_mul_witness` /
    `eis_lambda_pow_mul_ne_zero` / `eis_mul_neZeroAt_exists` /
    `eis_mul_ne_zero`（本丸その二）— **一般の積の witness 付き
    非零性**: 分解 x = λ^{k₁}u, y = λ^{k₂}v から x·y = λ^{k₁+k₂}(uv)、
    単数剰余の乗法性（M93F-4）と λ シフトの K 回反復（witness の
    明示伝播）で x·y ≠ 0。積の witness の ∃ 版も明示構成で供給
  * M96F-3 `eis_ne_zero_mul` — 条件付き零因子なしの橋: ∃-witness を
    持つ二元の積は 0 でない（構成的対偶形）
  * M96F-4 `EisDomain2Data` / `eisDomain2Data` / `eisDomain2_nonempty`
    — 分解・積定理一式の束と witness、見出し定理

  **位置づけ（正直な申告）**: (1) 分解の k は測度による上界
  k ≤ i + (n−1)(p−1) 付きで構成されるが、**λ 進付値そのもの
  （最小の k）の計算・一意性**は本モジュールでは追求しない。
  (2) 積の witness の ∃ 版は明示構成だが、添字の閉じた式
  （(k₁+k₂) mod (p−1) など）への簡約は行わない。(3) 選言形の
  NoZeroDiv (eisRing p)（x·y = 0 → x = 0 ∨ y = 0）は、裸の x ≠ 0
  から witness を取り出すのに排中律（ないし Markov 原理）を要する
  ため（M91F の ℤ_p と同じ事情）、構成的には追求しない——本シリーズ
  が witness 付き非零性を採用する理由そのものである。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.EisDomain

namespace IUT

/-! ## §0 簿記: レベル 0 の不成立と λ シフトの逆向き -/

/-- **M96F-0a**: レベル 0（ℤ/p^0 = ℤ/1 は自明環）の witness は
    存在しない（M91F の neZeroAt_zero_elim の Eisenstein 版）。 -/
theorem eisNeZeroAt_zero_elim (p : Nat) (x : EisCarrier p) (i : Nat)
    (hi : i < p - 1) (hx : EisNeZeroAt p x i 0 hi) : False := by
  apply hx
  obtain ⟨c, hc⟩ := Quot.exists_rep (eisCoeff p i 0 hi x)
  rw [← hc]
  apply Quot.sound
  show ((p ^ 0 : Nat) : Int) ∣ c - 0
  exact ⟨c - 0, (Int.one_mul (c - 0)).symm⟩

/-- **M96F-0b（域内シフトの逆向き）**: λ·x が (j+1, n)-witness を
    持てば x は (j, n)-witness を持つ（M93F-2a の係数等式
    cⱼ₊₁(λx) = cⱼ(x) をそのまま逆に読む）。 -/
theorem eisNeZeroAt_lambda_mul_rev (p : Nat) (x : EisCarrier p)
    {j n : Nat} (hj1 : j + 1 < p - 1) (hj : j < p - 1)
    (hx : EisNeZeroAt p ((eisRing p).mul (eisLambda p) x) (j + 1) n hj1) :
    EisNeZeroAt p x j n hj := by
  intro hz
  apply hx
  rw [eisCoeff_lambda_mul p x j n hj1]
  exact hz

/-- **M96F-0c（巻き戻りの逆向き）**: λ·x が (0, n+1)-witness を
    持てば x は (p−2, n)-witness を持つ。対偶: c_{p−2}(x) の
    レベル n 成分が 0 なら c₀(λx) = −π·c_{p−2}(x) のレベル n+1
    成分も 0（p 倍の上向き簿記 val_zero_p_mul + 負号の保存）。 -/
theorem eisNeZeroAt_lambda_wrap_rev (p : Nat) (hp : 2 ≤ p)
    (x : EisCarrier p) {n : Nat} (h0 : 0 < p - 1) (hpw : p - 2 < p - 1)
    (hx : EisNeZeroAt p ((eisRing p).mul (eisLambda p) x) 0 (n + 1) h0) :
    EisNeZeroAt p x (p - 2) n hpw := by
  induction x using Quot.ind
  rename_i f
  intro hz
  apply hx
  have hz' : (eisCoeffZp p f (p - 2) n).val n
      = Quot.mk (modCong (p ^ n)).rel 0 := hz
  show (eisCoeffZp p (psMul (zpRing p) (psX (zpRing p)) f) 0 (n + 1)).val
      (n + 1)
    = Quot.mk (modCong (p ^ (n + 1))).rel 0
  rw [eisCoeffZp_X_wrap p hp f n]
  have hneg : (zpRing p).mul (zpNegPi p) (eisCoeffZp p f (p - 2) n)
      = (zpRing p).neg
          ((zpRing p).mul (zpPi p) (eisCoeffZp p f (p - 2) n)) :=
    CRing.neg_mul (zpRing p) (zpPi p) (eisCoeffZp p f (p - 2) n)
  rw [hneg]
  have hW : ((zpRing p).mul (zpPi p) (eisCoeffZp p f (p - 2) n)).val (n + 1)
      = Quot.mk (modCong (p ^ (n + 1))).rel 0 :=
    val_zero_p_mul p (eisCoeffZp p f (p - 2) n) n hz'
  have h5 : ((zpRing p).neg
        ((zpRing p).mul (zpPi p) (eisCoeffZp p f (p - 2) n))).val (n + 1)
      = (zmod (p ^ (n + 1))).inv
          (((zpRing p).mul (zpPi p) (eisCoeffZp p f (p - 2) n)).val (n + 1)) :=
    rfl
  rw [h5, hW]
  show Quot.mk (modCong (p ^ (n + 1))).rel (-0)
    = Quot.mk (modCong (p ^ (n + 1))).rel 0
  apply Quot.sound
  show ((p ^ (n + 1) : Nat) : Int) ∣ -0 - 0
  refine ⟨0, ?_⟩
  rw [Int.mul_zero]
  decide

/-! ## §0' λ 割り算の関数化 -/

/-- **M96F-0d**: λ 割り算の商の明示構成（M93F-3 の x′ を zpDivP で
    関数化。f 自身には条件を課さない全域関数）。 -/
def eisDivLambda (p : Nat) (hp : 2 ≤ p) (f : PS (zpRing p)) :
    PS (zpRing p) :=
  psAdd (zpRing p) (psShift (zpRing p) f)
    (psNeg (zpRing p)
      (psMul (zpRing p) (psMono (zpRing p) (p - 2))
        (psC (zpRing p) (zpDivP p hp (f 0)))))

/-- **M96F-0e**: 定数項のレベル 1 成分が 0 なら mk f = λ·mk (f/λ)
    （M93F-3 eis_lambda_division + M43 zpDivP_mul_cancel）。 -/
theorem eisDivLambda_spec (p : Nat) (hp : 2 ≤ p) (f : PS (zpRing p))
    (hval1 : (f 0).val 1 = Quot.mk (modCong (p ^ 1)).rel 0) :
    Quot.mk (eisRel p) f
      = (eisRing p).mul (eisLambda p)
          (Quot.mk (eisRel p) (eisDivLambda p hp f)) :=
  eis_lambda_division p hp f (zpDivP p hp (f 0))
    ((zpDivP_mul_cancel p hp (f 0) hval1).symm)

/-- 簿記: x = λ·x′ かつ x′ = λ^k·u なら x = λ^{k+1}·u
    （再帰の組み立てステップ）。 -/
theorem eis_lambda_pow_succ_eq (p : Nat) {x x' u : EisCarrier p} {k : Nat}
    (heq : x = (eisRing p).mul (eisLambda p) x')
    (hequ : x' = (eisRing p).mul (rpow (eisRing p) (eisLambda p) k) u) :
    x = (eisRing p).mul (rpow (eisRing p) (eisLambda p) (k + 1)) u := by
  rw [heq, hequ]
  show (eisRing p).mul (eisLambda p)
      ((eisRing p).mul (rpow (eisRing p) (eisLambda p) k) u)
    = (eisRing p).mul
        ((eisRing p).mul (rpow (eisRing p) (eisLambda p) k) (eisLambda p)) u
  rw [(eisRing p).mul_comm (rpow (eisRing p) (eisLambda p) k) (eisLambda p),
    (eisRing p).mul_assoc (eisLambda p) (rpow (eisRing p) (eisLambda p) k) u]

/-! ## §1 M96F-1 本丸その一: witness 付き λ 進付値分解 -/

/-- **M96F-1a: λ 進付値分解のデータ** — k ≤ m（m は witness 測度の
    上界）と単数剰余 u（(0,1)-witness）と等式 x = λ^k·u の束。
    M91F の ZpValDecomp の Eisenstein 版（∃ ではなく Σ 型）。 -/
structure EisValDecomp (p : Nat) (h0 : 0 < p - 1) (x : EisCarrier p)
    (m : Nat) where
  k : Nat
  u : EisCarrier p
  k_le : k ≤ m
  unit1 : EisNeZeroAt p u 0 1 h0
  eq : x = (eisRing p).mul (rpow (eisRing p) (eisLambda p) k) u

/-- 単数剰余ならその場で分解終了（k = 0、λ^0 = 1）。 -/
def eisValDecompUnit (p : Nat) (h0 : 0 < p - 1) (m : Nat)
    (x : EisCarrier p) (hu : EisNeZeroAt p x 0 1 h0) :
    EisValDecomp p h0 x m where
  k := 0
  u := x
  k_le := Nat.zero_le m
  unit1 := hu
  eq := by
    show x = (eisRing p).mul (eisRing p).one x
    exact ((eisRing p).one_mul x).symm

/-- **M96F-1b: 付値分解の構成（本丸その一）** — witness 測度
    μ = i + (n−1)(p−1) の上界 m（燃料）に関する構造的再帰。
    各ステップ: 0 番被約係数のレベル 1 成分を zmodIsZero で Bool
    判定し、非零なら単数剰余で終了、零なら λ 割り算（M96F-0d/e）で
    商に降りて witness を逆向きシフト（M96F-0b/c、測度はちょうど
    1 減る）。レベル 0 と (0,1)-witness × 剰余 0 は矛盾で潰れる。
    場合分けは全て Bool 値判定と Nat の構造場合分け——排中律不使用。 -/
def eisValDecompose (p : Nat) (hp : 2 ≤ p) (h0 : 0 < p - 1) :
    (m : Nat) → (f : PS (zpRing p)) → (i n : Nat) → (hi : i < p - 1) →
    i + (n - 1) * (p - 1) ≤ m →
    EisNeZeroAt p (Quot.mk (eisRel p) f) i n hi →
    EisValDecomp p h0 (Quot.mk (eisRel p) f) m
  | 0, f, i, n, hi, hμ, hx =>
    match h1 : zmodIsZero (p ^ 1)
        (eisCoeff p 0 1 h0 (Quot.mk (eisRel p) f)) with
    | false =>
      eisValDecompUnit p h0 0 (Quot.mk (eisRel p) f)
        (zmodIsZero_false (p ^ 1)
          (eisCoeff p 0 1 h0 (Quot.mk (eisRel p) f)) h1)
    | true =>
      match i, n, hi, hμ, hx with
      | i', 0, hi', _, hx2 =>
        (eisNeZeroAt_zero_elim p (Quot.mk (eisRel p) f) i' hi' hx2).elim
      | 0, 1, _, _, hx2 =>
        (hx2 (zmodIsZero_true (p ^ 1)
          (eisCoeff p 0 1 h0 (Quot.mk (eisRel p) f)) h1)).elim
      | _ + 1, _, _, hμ', _ => absurd hμ' (by omega)
      | 0, nn + 2, _, hμ', _ =>
        absurd hμ' (by
          intro hle
          have h2 : (nn + 2 - 1) * (p - 1) = nn * (p - 1) + (p - 1) := by
            show (nn + 1) * (p - 1) = nn * (p - 1) + (p - 1)
            exact Nat.succ_mul nn (p - 1)
          rw [h2] at hle
          omega)
  | m + 1, f, i, n, hi, hμ, hx =>
    match h1 : zmodIsZero (p ^ 1)
        (eisCoeff p 0 1 h0 (Quot.mk (eisRel p) f)) with
    | false =>
      eisValDecompUnit p h0 (m + 1) (Quot.mk (eisRel p) f)
        (zmodIsZero_false (p ^ 1)
          (eisCoeff p 0 1 h0 (Quot.mk (eisRel p) f)) h1)
    | true =>
      -- 剰余 0: 定数項のレベル 1 成分が 0 なので λ で割れる
      have hval1 : (f 0).val 1 = Quot.mk (modCong (p ^ 1)).rel 0 := by
        have hz' : (eisCoeffZp p f 0 1).val 1
            = Quot.mk (modCong (p ^ 1)).rel 0 :=
          zmodIsZero_true (p ^ 1)
            (eisCoeff p 0 1 h0 (Quot.mk (eisRel p) f)) h1
        rw [eisCoeffZp_one p f] at hz'
        exact hz'
      have heq : Quot.mk (eisRel p) f
          = (eisRing p).mul (eisLambda p)
              (Quot.mk (eisRel p) (eisDivLambda p hp f)) :=
        eisDivLambda_spec p hp f hval1
      have hx' : EisNeZeroAt p ((eisRing p).mul (eisLambda p)
          (Quot.mk (eisRel p) (eisDivLambda p hp f))) i n hi := by
        rw [← heq]
        exact hx
      match i, n, hi, hμ, hx, hx' with
      | i', 0, hi', _, hx2, _ =>
        (eisNeZeroAt_zero_elim p (Quot.mk (eisRel p) f) i' hi' hx2).elim
      | 0, 1, _, _, hx2, _ =>
        (hx2 (zmodIsZero_true (p ^ 1)
          (eisCoeff p 0 1 h0 (Quot.mk (eisRel p) f)) h1)).elim
      | j + 1, n', hi', hμ', _, hx2' =>
        -- 域内シフトの逆向き: witness (j+1, n') → (j, n')、測度 −1
        have hj : j < p - 1 := by omega
        have hw : EisNeZeroAt p
            (Quot.mk (eisRel p) (eisDivLambda p hp f)) j n' hj :=
          eisNeZeroAt_lambda_mul_rev p
            (Quot.mk (eisRel p) (eisDivLambda p hp f)) hi' hj hx2'
        have hμ2 : j + (n' - 1) * (p - 1) ≤ m := by omega
        match eisValDecompose p hp h0 m (eisDivLambda p hp f) j n' hj
            hμ2 hw with
        | ⟨k, u, hk, hu, hequ⟩ =>
          { k := k + 1
            u := u
            k_le := Nat.succ_le_succ hk
            unit1 := hu
            eq := eis_lambda_pow_succ_eq p heq hequ }
      | 0, nn + 2, hi', hμ', _, hx2' =>
        -- 巻き戻りの逆向き: witness (0, nn+2) → (p−2, nn+1)、測度 −1
        have hpw : p - 2 < p - 1 := by omega
        have hw : EisNeZeroAt p
            (Quot.mk (eisRel p) (eisDivLambda p hp f)) (p - 2) (nn + 1)
            hpw :=
          eisNeZeroAt_lambda_wrap_rev p hp
            (Quot.mk (eisRel p) (eisDivLambda p hp f)) hi' hpw hx2'
        have hμ2 : p - 2 + (nn + 1 - 1) * (p - 1) ≤ m := by
          have h2 : (nn + 2 - 1) * (p - 1) = nn * (p - 1) + (p - 1) := by
            show (nn + 1) * (p - 1) = nn * (p - 1) + (p - 1)
            exact Nat.succ_mul nn (p - 1)
          have h3 : (nn + 1 - 1) * (p - 1) = nn * (p - 1) := rfl
          rw [h3]
          rw [h2] at hμ'
          omega
        match eisValDecompose p hp h0 m (eisDivLambda p hp f) (p - 2)
            (nn + 1) hpw hμ2 hw with
        | ⟨k, u, hk, hu, hequ⟩ =>
          { k := k + 1
            u := u
            k_le := Nat.succ_le_succ hk
            unit1 := hu
            eq := eis_lambda_pow_succ_eq p heq hequ }

/-- **系 (M96F-1c): 付値分解の ∃ 版**（商の元上。明示的 intro なので
    choice-free）: (i, n)-witness を持つ x は x = λ^k·u
    （k ≤ i + (n−1)(p−1)、u 単数剰余）と分解される。 -/
theorem eis_valuation_exists (p : Nat) (hp : 2 ≤ p) (h0 : 0 < p - 1)
    (x : EisCarrier p) (i n : Nat) (hi : i < p - 1)
    (hx : EisNeZeroAt p x i n hi) :
    ∃ (k : Nat) (u : EisCarrier p),
      k ≤ i + (n - 1) * (p - 1) ∧ EisNeZeroAt p u 0 1 h0 ∧
        x = (eisRing p).mul (rpow (eisRing p) (eisLambda p) k) u := by
  induction x using Quot.ind
  rename_i f
  obtain ⟨k, u, hk, hu, he⟩ :=
    eisValDecompose p hp h0 (i + (n - 1) * (p - 1)) f i n hi
      (Nat.le_refl _) hx
  exact ⟨k, u, hk, hu, he⟩

/-! ## §2 M96F-2 本丸その二: 一般の積の witness 付き非零性 -/

/-- 積の交換結合 (ab)(cd) = (ac)(bd)（一般の可換環、M91F の
    zpMul_mul_mul_comm の一般化）。 -/
theorem cring_mul_mul_comm (R : CRing) (a b c d : R.carrier) :
    R.mul (R.mul a b) (R.mul c d) = R.mul (R.mul a c) (R.mul b d) := by
  rw [R.mul_assoc a b (R.mul c d), ← R.mul_assoc b c d,
    R.mul_comm b c, R.mul_assoc c b d, ← R.mul_assoc a c (R.mul b d)]

/-- **M96F-2a**: 単数剰余 w について λ^K·w は常に何らかの
    (i, n)-witness を持つ（K の帰納法。各ステップは M93F-2 の
    λ シフト: 域内なら添字 +1、最高添字ならレベル +1 の巻き戻り。
    どちらに進むかは Nat.decLt の構造場合分け——排中律不使用）。 -/
theorem eis_lambda_pow_mul_witness (p : Nat) (hp : 2 ≤ p)
    (w : EisCarrier p) (h0 : 0 < p - 1)
    (hw : EisNeZeroAt p w 0 1 h0) : ∀ K : Nat,
    ∃ (i n : Nat) (hi : i < p - 1),
      EisNeZeroAt p
        ((eisRing p).mul (rpow (eisRing p) (eisLambda p) K) w) i n hi := by
  intro K
  induction K with
  | zero =>
    refine ⟨0, 1, h0, ?_⟩
    have h1 : (eisRing p).mul (rpow (eisRing p) (eisLambda p) 0) w = w :=
      (eisRing p).one_mul w
    rw [h1]
    exact hw
  | succ K ih =>
    obtain ⟨i, n, hi, hwit⟩ := ih
    have heq : (eisRing p).mul (rpow (eisRing p) (eisLambda p) (K + 1)) w
        = (eisRing p).mul (eisLambda p)
            ((eisRing p).mul (rpow (eisRing p) (eisLambda p) K) w) := by
      show (eisRing p).mul
          ((eisRing p).mul (rpow (eisRing p) (eisLambda p) K)
            (eisLambda p)) w
        = (eisRing p).mul (eisLambda p)
            ((eisRing p).mul (rpow (eisRing p) (eisLambda p) K) w)
      rw [(eisRing p).mul_comm (rpow (eisRing p) (eisLambda p) K)
          (eisLambda p),
        (eisRing p).mul_assoc (eisLambda p)
          (rpow (eisRing p) (eisLambda p) K) w]
    cases Nat.decLt (i + 1) (p - 1) with
    | isTrue h =>
      refine ⟨i + 1, n, h, ?_⟩
      rw [heq]
      exact eisNeZeroAt_lambda_mul p
        ((eisRing p).mul (rpow (eisRing p) (eisLambda p) K) w) h hwit
    | isFalse h =>
      have hieq : i = p - 2 := by omega
      subst hieq
      refine ⟨0, n + 1, h0, ?_⟩
      rw [heq]
      exact eisNeZeroAt_lambda_wrap p hp
        ((eisRing p).mul (rpow (eisRing p) (eisLambda p) K) w) hi h0 hwit

/-- **系 (M96F-2b)**: 単数剰余 w について λ^K·w ≠ 0。 -/
theorem eis_lambda_pow_mul_ne_zero (p : Nat) (hp : 2 ≤ p)
    (w : EisCarrier p) (h0 : 0 < p - 1)
    (hw : EisNeZeroAt p w 0 1 h0) (K : Nat) :
    (eisRing p).mul (rpow (eisRing p) (eisLambda p) K) w
      ≠ (eisRing p).zero := by
  obtain ⟨i, n, hi, hwit⟩ := eis_lambda_pow_mul_witness p hp w h0 hw K
  exact eisNeZeroAt_ne_zero p
    ((eisRing p).mul (rpow (eisRing p) (eisLambda p) K) w) hi hwit

/-- **M96F-2c: 積の witness（∃ 版）** — witness を持つ二元の積は
    再び witness を持つ（付値分解 → 単数剰余の乗法性 M93F-4 →
    λ シフトの反復 M96F-2a。全段明示構成）。 -/
theorem eis_mul_neZeroAt_exists (p : Nat) (hp : IsPrime p)
    (h0 : 0 < p - 1) (x y : EisCarrier p) (i n j l : Nat)
    (hi : i < p - 1) (hj : j < p - 1)
    (hx : EisNeZeroAt p x i n hi) (hy : EisNeZeroAt p y j l hj) :
    ∃ (i' n' : Nat) (hi' : i' < p - 1),
      EisNeZeroAt p ((eisRing p).mul x y) i' n' hi' := by
  obtain ⟨k1, u, hk1, hu, hex⟩ :=
    eis_valuation_exists p hp.1 h0 x i n hi hx
  obtain ⟨k2, v, hk2, hv, hey⟩ :=
    eis_valuation_exists p hp.1 h0 y j l hj hy
  have hxy : (eisRing p).mul x y
      = (eisRing p).mul (rpow (eisRing p) (eisLambda p) (k1 + k2))
          ((eisRing p).mul u v) := by
    rw [hex, hey,
      cring_mul_mul_comm (eisRing p) (rpow (eisRing p) (eisLambda p) k1) u
        (rpow (eisRing p) (eisLambda p) k2) v,
      ← rpow_add (eisRing p) (eisLambda p) k1 k2]
  have huv : EisNeZeroAt p ((eisRing p).mul u v) 0 1 h0 :=
    eis_residue_mul p hp h0 u v hu hv
  rw [hxy]
  exact eis_lambda_pow_mul_witness p hp.1 ((eisRing p).mul u v) h0 huv
    (k1 + k2)

/-- **定理 (M96F-2d・本丸その二): 一般の積の非零性** — witness を
    持つ二元の積は 0 でない（M93F の正直申告「一般の積への拡張は
    λ 進付値分解を要し次層」の回収。M90F が仮定として要求していた
    O の零因子なしの witness 版・無条件証明）。 -/
theorem eis_mul_ne_zero (p : Nat) (hp : IsPrime p) (h0 : 0 < p - 1)
    (x y : EisCarrier p) (i n j l : Nat) (hi : i < p - 1)
    (hj : j < p - 1) (hx : EisNeZeroAt p x i n hi)
    (hy : EisNeZeroAt p y j l hj) :
    (eisRing p).mul x y ≠ (eisRing p).zero := by
  obtain ⟨i', n', hi', hwit⟩ :=
    eis_mul_neZeroAt_exists p hp h0 x y i n j l hi hj hx hy
  exact eisNeZeroAt_ne_zero p ((eisRing p).mul x y) hi' hwit

/-! ## §3 M96F-3 条件付き零因子なしの橋 -/

/-- **M96F-3: 構成的対偶形** — ∃-witness を持つ二元の積は 0 でない。
    選言形の NoZeroDiv (eisRing p) 自体は、裸の ≠ 0 から witness を
    取り出すのに排中律を要するため追求しない（ヘッダの正直申告参照）。 -/
theorem eis_ne_zero_mul (p : Nat) (hp : IsPrime p) (h0 : 0 < p - 1)
    (x y : EisCarrier p)
    (hx : ∃ (i n : Nat) (hi : i < p - 1), EisNeZeroAt p x i n hi)
    (hy : ∃ (j l : Nat) (hj : j < p - 1), EisNeZeroAt p y j l hj) :
    (eisRing p).mul x y ≠ (eisRing p).zero := by
  obtain ⟨i, n, hi, hx'⟩ := hx
  obtain ⟨j, l, hj, hy'⟩ := hy
  exact eis_mul_ne_zero p hp h0 x y i n j l hi hj hx' hy'

/-! ## §4 M96F-4 まとめの束 -/

/-- **M96F-4a: O の整域性データ（第二段）** — λ 進付値分解（データ
    と ∃ 版）・λ 冪倍の witness 伝播と非零性・一般の積の witness と
    非零性・∃-witness 対偶形の束。 -/
structure EisDomain2Data (p : Nat) (hp : IsPrime p) (h0 : 0 < p - 1) where
  decompose : ∀ (m : Nat) (f : PS (zpRing p)) (i n : Nat)
    (hi : i < p - 1), i + (n - 1) * (p - 1) ≤ m →
    EisNeZeroAt p (Quot.mk (eisRel p) f) i n hi →
    EisValDecomp p h0 (Quot.mk (eisRel p) f) m
  valuation : ∀ (x : EisCarrier p) (i n : Nat) (hi : i < p - 1),
    EisNeZeroAt p x i n hi →
    ∃ (k : Nat) (u : EisCarrier p),
      k ≤ i + (n - 1) * (p - 1) ∧ EisNeZeroAt p u 0 1 h0 ∧
        x = (eisRing p).mul (rpow (eisRing p) (eisLambda p) k) u
  lambda_pow_witness : ∀ (w : EisCarrier p), EisNeZeroAt p w 0 1 h0 →
    ∀ K : Nat, ∃ (i n : Nat) (hi : i < p - 1),
      EisNeZeroAt p
        ((eisRing p).mul (rpow (eisRing p) (eisLambda p) K) w) i n hi
  lambda_pow_ne_zero : ∀ (w : EisCarrier p), EisNeZeroAt p w 0 1 h0 →
    ∀ K : Nat,
      (eisRing p).mul (rpow (eisRing p) (eisLambda p) K) w
        ≠ (eisRing p).zero
  mul_witness : ∀ (x y : EisCarrier p) (i n j l : Nat)
    (hi : i < p - 1) (hj : j < p - 1),
    EisNeZeroAt p x i n hi → EisNeZeroAt p y j l hj →
    ∃ (i' n' : Nat) (hi' : i' < p - 1),
      EisNeZeroAt p ((eisRing p).mul x y) i' n' hi'
  mul_ne_zero : ∀ (x y : EisCarrier p) (i n j l : Nat)
    (hi : i < p - 1) (hj : j < p - 1),
    EisNeZeroAt p x i n hi → EisNeZeroAt p y j l hj →
    (eisRing p).mul x y ≠ (eisRing p).zero
  ne_zero_mul : ∀ (x y : EisCarrier p),
    (∃ (i n : Nat) (hi : i < p - 1), EisNeZeroAt p x i n hi) →
    (∃ (j l : Nat) (hj : j < p - 1), EisNeZeroAt p y j l hj) →
    (eisRing p).mul x y ≠ (eisRing p).zero

/-- **M96F-4b: witness**（全フィールドが本モジュールの完全証明）。 -/
def eisDomain2Data (p : Nat) (hp : IsPrime p) (h0 : 0 < p - 1) :
    EisDomain2Data p hp h0 where
  decompose := fun m f i n hi hμ hx =>
    eisValDecompose p hp.1 h0 m f i n hi hμ hx
  valuation := fun x i n hi hx =>
    eis_valuation_exists p hp.1 h0 x i n hi hx
  lambda_pow_witness := fun w hw K =>
    eis_lambda_pow_mul_witness p hp.1 w h0 hw K
  lambda_pow_ne_zero := fun w hw K =>
    eis_lambda_pow_mul_ne_zero p hp.1 w h0 hw K
  mul_witness := fun x y i n j l hi hj hx hy =>
    eis_mul_neZeroAt_exists p hp h0 x y i n j l hi hj hx hy
  mul_ne_zero := fun x y i n j l hi hj hx hy =>
    eis_mul_ne_zero p hp h0 x y i n j l hi hj hx hy
  ne_zero_mul := fun x y hx hy => eis_ne_zero_mul p hp h0 x y hx hy

/-- **見出し定理 (M96F-4c)**: O = ℤ_p[π] の witness 付き整域性
    データ（第二段: 付値分解と一般の積の非零性）は任意の素数 p で
    存在する。 -/
theorem eisDomain2_nonempty (p : Nat) (hp : IsPrime p) (h0 : 0 < p - 1) :
    Nonempty (EisDomain2Data p hp h0) := ⟨eisDomain2Data p hp h0⟩

end IUT
