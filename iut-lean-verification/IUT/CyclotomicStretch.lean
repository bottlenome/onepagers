/-
  IUT/CyclotomicStretch.lean — CTS（p = 3 円分塔の共通足場: stretch 代入
  X ↦ X³ の一般補題と円分多項式塔 Φ_{3ⁿ} の再帰構成）

  ── 分類 **[実／本物建設(b)]**（骨格でなく実 ℚ[X] = `PS ratRing` 上の本物の
  作用素 stretch と本物の多項式等式・sorry 皆無・新規 Classical.choice 皆無・
  模型ゼロ）。名前付き実ターゲット: 柱A3「一般 n 円分塔 ℚ ⊂ ℚ(ζ₃) ⊂ ℚ(ζ_{9})
  ⊂ … ⊂ ℚ(ζ_{3ⁿ})」の各段の**法多項式** Φ_{3ⁿ} と、段の埋め込み ι_n・既約性
  E5・一般 μ の三方が共通に要する **stretch（係数列版の X ↦ X³ 代入）** の
  一般補題を本物で建設する。

  **complete_pct 影響**: 本ファイル単体では **complete_pct 未設定（0 前進）**。
  A3 一般 n 塔の complete_pct は、一般段機構 M2（ι_n の体埋め込み・E5 の
  Φ_{3ⁿ} 既約性・一般 μ の同定）が本物で揃った段で反映する。本層はその共通
  足場（stretch の乗法性・円分塔の核恒等式・合同輸送）を提供する。

  内容（すべて実 ℚ[X] = `PS ratRing`）:
   * `ctsStretch f`          — X ↦ X³ 代入（係数列版）f ↦ (j ↦ if 3∣j then f_{j/3} else 0)。
   * `ctsStretch_bounded`    — 有界性 deg(stretch f) = 3·(N−1)（有界 N から）。
   * `ctsStretch_add/neg/psC/single` — 環演算・定数・単項式との両立。
   * `cts_xm1`               — stretch(Xᵐ − 1) = X^{3m} − 1（座標照合）。
   * **`cts_rsum_thin`**     — 山場①: 3 非倍数で消える列の間引き和。
   * **`ctsStretch_mul`**    — 山場②: stretch の乗法性（間引き補題 1 本に集約）。
   * `ctsPhi n`              — 円分多項式塔 Φ_{3ⁿ}（cq0PS = Φ₃ を基底に stretch 再帰）。
   * `ctsPhi_two_eq`         — Φ_9 = 既存 cpdPhi9（= x⁶+x³+1）と一致。
   * `ctsPhi_bound/lead`     — deg Φ_{3ⁿ} = 2·3^{n−1}・先頭係数 = 1。
   * `ctsPhi_three_coeffs`   — 係数は 0/3^{n−1}/2·3^{n−1} 以外で 0（E5 の燃料）。
   * **`cts_pow_sub_one`**   — 核恒等式: X^{3ⁿ} − 1 = Φ_{3ⁿ}·(X^{3^{n−1}} − 1)。
   * **`cts_cong`**          — 合同輸送: gnfCong Φ_{3ⁿ} u v ⟹ gnfCong Φ_{3^{n+1}} (stretch u)(stretch v)。

  正直な限定（§4 規約により消さない）:
   - **p = 3 に固定**。stretch は X ↦ X³ 専用（一般素数 p の X ↦ X^p 版は
     本層に含めない）。円分塔も ℚ(ζ_{3ⁿ}) のみ。
   - **stretch は係数列（実 ℚ[X]）上の本物の作用素**。乗法性 `ctsStretch_mul`・
     核恒等式 `cts_pow_sub_one`・合同輸送 `cts_cong` はすべて実多項式の
     全係数一致で完全証明（sorry 皆無・新規 choice 皆無）。代理でも模型でもない。
   - `cts_cong` は **1 ≤ n を仮定**する（ctsPhi(n+1) = stretch(ctsPhi n) は
     n = 0 では成立しないため。設計 §3.0 の暗黙前提を明示した正直申告）。
   - **含めない（後続）**: 各段の体化（ι_n の実体埋め込み）・Φ_{3ⁿ} の既約性
     （E5）・一般 μ の同定は本層に含めない。本層は stretch 一般補題と塔の
     法多項式データ・核恒等式・合同輸送に限定する（A1 に非依存な独立切片）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.CyclotomicPolyData
import IUT.GenExtFieldNF

namespace IUT

/-! ## CTS-1: stretch（X ↦ X³ 代入の係数列版）と有界性 -/

/-- **CTS-1a: stretch** — X ↦ X³ 代入。係数列 f を「3 の倍数次に f の
    その 1/3 番目の係数を置き、他を 0 にする」写像。(stretch f)_{3i} = f_i、
    (stretch f)_j = 0 (3∤j)。 -/
def ctsStretch (f : PS ratRing) : PS ratRing :=
  fun j => if j % 3 = 0 then f (j / 3) else ratRing.zero

/-- **CTS-1b: 3 の倍数次の値** — (stretch f)_{3i} = f_i。 -/
theorem ctsStretch_mul3 (f : PS ratRing) (i : Nat) :
    ctsStretch f (3 * i) = f i := by
  show (if (3 * i) % 3 = 0 then f ((3 * i) / 3) else ratRing.zero) = f i
  rw [if_pos (show (3 * i) % 3 = 0 by omega), show (3 * i) / 3 = i from by omega]

/-- **CTS-1c: 有界性** — f が N 以上で消えるなら stretch f は 3·(N−1)+1
    以上で消える（deg が 3 倍に伸びる）。 -/
theorem ctsStretch_bounded {f : PS ratRing} {N : Nat}
    (hf : IsPolyBounded ratRing f N) :
    IsPolyBounded ratRing (ctsStretch f) (3 * (N - 1) + 1) := by
  intro j hj
  show (if j % 3 = 0 then f (j / 3) else ratRing.zero) = ratRing.zero
  cases Nat.decEq (j % 3) 0 with
  | isTrue h => rw [if_pos h]; exact hf (j / 3) (by omega)
  | isFalse h => rw [if_neg h]

/-! ## CTS-2: 加法・符号・定数・単項式との両立 -/

/-- **CTS-2a: 加法両立** — stretch(f + g) = stretch f + stretch g。 -/
theorem ctsStretch_add (f g : PS ratRing) :
    ctsStretch (psAdd ratRing f g) = psAdd ratRing (ctsStretch f) (ctsStretch g) := by
  funext j
  cases Nat.decEq (j % 3) 0 with
  | isTrue h =>
    show (if j % 3 = 0 then ratRing.add (f (j / 3)) (g (j / 3)) else ratRing.zero)
       = ratRing.add (if j % 3 = 0 then f (j / 3) else ratRing.zero)
                     (if j % 3 = 0 then g (j / 3) else ratRing.zero)
    rw [if_pos h, if_pos h, if_pos h]
  | isFalse h =>
    show (if j % 3 = 0 then ratRing.add (f (j / 3)) (g (j / 3)) else ratRing.zero)
       = ratRing.add (if j % 3 = 0 then f (j / 3) else ratRing.zero)
                     (if j % 3 = 0 then g (j / 3) else ratRing.zero)
    rw [if_neg h, if_neg h, if_neg h, ratRing.zero_add]

/-- **CTS-2b: 符号両立** — stretch(−f) = −stretch f。 -/
theorem ctsStretch_neg (f : PS ratRing) :
    ctsStretch (psNeg ratRing f) = psNeg ratRing (ctsStretch f) := by
  funext j
  cases Nat.decEq (j % 3) 0 with
  | isTrue h =>
    show (if j % 3 = 0 then ratRing.neg (f (j / 3)) else ratRing.zero)
       = ratRing.neg (if j % 3 = 0 then f (j / 3) else ratRing.zero)
    rw [if_pos h, if_pos h]
  | isFalse h =>
    show (if j % 3 = 0 then ratRing.neg (f (j / 3)) else ratRing.zero)
       = ratRing.neg (if j % 3 = 0 then f (j / 3) else ratRing.zero)
    rw [if_neg h, if_neg h, CRing.neg_zero ratRing]

/-- **CTS-2c: 定数両立** — stretch(c) = c（定数級数は不変）。 -/
theorem ctsStretch_psC (a : QRat) :
    ctsStretch (psC ratRing a) = psC ratRing a := by
  funext j
  show (if j % 3 = 0 then (if j / 3 = 0 then a else ratRing.zero) else ratRing.zero)
     = (if j = 0 then a else ratRing.zero)
  cases Nat.decEq j 0 with
  | isTrue h =>
    rw [if_pos h, if_pos (show j / 3 = 0 by omega), if_pos (show j % 3 = 0 by omega)]
  | isFalse h =>
    rw [if_neg h]
    cases Nat.decEq (j % 3) 0 with
    | isTrue h3 => rw [if_pos h3, if_neg (show j / 3 ≠ 0 by omega)]
    | isFalse h3 => rw [if_neg h3]

/-- **CTS-2d: 単項式両立** — stretch(c·Xᵐ) = c·X^{3m}。 -/
theorem ctsStretch_single (c : QRat) (m : Nat) :
    ctsStretch (psSingle ratRing c m) = psSingle ratRing c (3 * m) := by
  funext j
  show (if j % 3 = 0 then (if j / 3 = m then c else ratRing.zero) else ratRing.zero)
     = (if j = 3 * m then c else ratRing.zero)
  cases Nat.decEq (j % 3) 0 with
  | isTrue h3 =>
    rw [if_pos h3]
    cases Nat.decEq (j / 3) m with
    | isTrue hm => rw [if_pos hm, if_pos (show j = 3 * m by omega)]
    | isFalse hm => rw [if_neg hm, if_neg (show j ≠ 3 * m by omega)]
  | isFalse h3 =>
    rw [if_neg h3, if_neg (show j ≠ 3 * m by omega)]

/-! ## CTS-3: Xᵐ − 1 の stretch -/

/-- **CTS-3a: Xᵐ − 1** — 既存 `cpdXpMinus1`（= psSingle 1 m + psC(−1)）を再利用。 -/
def ctsXm1 (m : Nat) : PS ratRing := cpdXpMinus1 m

/-- **CTS-3b: stretch(Xᵐ − 1) = X^{3m} − 1**。加法・単項式・定数の両立で座標照合。 -/
theorem cts_xm1 (m : Nat) : ctsStretch (ctsXm1 m) = ctsXm1 (3 * m) := by
  show ctsStretch (psAdd ratRing (psSingle ratRing ratRing.one m)
      (psC ratRing (ratRing.neg ratRing.one)))
    = psAdd ratRing (psSingle ratRing ratRing.one (3 * m))
        (psC ratRing (ratRing.neg ratRing.one))
  rw [ctsStretch_add, ctsStretch_single, ctsStretch_psC]

/-! ## CTS-4: 山場 — 間引き和と stretch の乗法性 -/

/-- **CTS-4a: 間引き和** — 3 非倍数で消える列 h に対し、
    Σ_{k≤3m} h_k = Σ_{i≤m} h_{3i}（3 の倍数の項だけが生き残る）。 -/
theorem cts_rsum_thin (h : Nat → QRat) (m : Nat)
    (hz : ∀ k, k % 3 ≠ 0 → h k = ratRing.zero) :
    rsum ratRing h (3 * m + 1) = rsum ratRing (fun i => h (3 * i)) (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : h (3 * m + 1) = ratRing.zero := hz (3 * m + 1) (by omega)
    have h2 : h (3 * m + 1 + 1) = ratRing.zero := hz (3 * m + 1 + 1) (by omega)
    have harg : 3 * (m + 1) + 1 = 3 * m + 1 + 1 + 1 + 1 := by omega
    rw [harg]
    show ratRing.add (ratRing.add (ratRing.add (rsum ratRing h (3 * m + 1)) (h (3 * m + 1)))
        (h (3 * m + 1 + 1))) (h (3 * m + 1 + 1 + 1))
      = ratRing.add (rsum ratRing (fun i => h (3 * i)) (m + 1)) (h (3 * (m + 1)))
    rw [h1, CRing.add_zero ratRing, h2, CRing.add_zero ratRing, ih,
      show 3 * m + 1 + 1 + 1 = 3 * (m + 1) from by omega]

/-- **CTS-4b: stretch の乗法性** — stretch(f·g) = stretch f · stretch g。
    j%3≠0 の項は Cauchy 各項で片側が 3 非倍数 ⟹ 0。j = 3m の項は非零項が
    k = 3i のみ ⟹ 間引き補題 `cts_rsum_thin` で Σ_{i≤m} f_i·g_{m−i} = (f·g)_m。 -/
theorem ctsStretch_mul (f g : PS ratRing) :
    ctsStretch (psMul ratRing f g)
      = psMul ratRing (ctsStretch f) (ctsStretch g) := by
  funext j
  cases Nat.decEq (j % 3) 0 with
  | isTrue hj =>
    show (if j % 3 = 0 then psMul ratRing f g (j / 3) else ratRing.zero)
       = rsum ratRing (fun k => ratRing.mul (ctsStretch f k) (ctsStretch g (j - k))) (j + 1)
    rw [if_pos hj]
    have hz : ∀ k, k % 3 ≠ 0 →
        (fun k => ratRing.mul (ctsStretch f k) (ctsStretch g (j - k))) k = ratRing.zero := by
      intro k hk
      show ratRing.mul (ctsStretch f k) (ctsStretch g (j - k)) = ratRing.zero
      rw [show ctsStretch f k = ratRing.zero from if_neg hk]
      exact CRing.zero_mul ratRing _
    rw [show j + 1 = 3 * (j / 3) + 1 from by omega,
      cts_rsum_thin (fun k => ratRing.mul (ctsStretch f k) (ctsStretch g (j - k))) (j / 3) hz]
    show rsum ratRing (fun i => ratRing.mul (f i) (g (j / 3 - i))) (j / 3 + 1)
       = rsum ratRing (fun i =>
           ratRing.mul (ctsStretch f (3 * i)) (ctsStretch g (j - 3 * i))) (j / 3 + 1)
    apply rsum_congr
    intro i hi
    show ratRing.mul (f i) (g (j / 3 - i))
       = ratRing.mul (ctsStretch f (3 * i)) (ctsStretch g (j - 3 * i))
    rw [ctsStretch_mul3, show j - 3 * i = 3 * (j / 3 - i) from by omega, ctsStretch_mul3]
  | isFalse hj =>
    show (if j % 3 = 0 then psMul ratRing f g (j / 3) else ratRing.zero)
       = rsum ratRing (fun k => ratRing.mul (ctsStretch f k) (ctsStretch g (j - k))) (j + 1)
    rw [if_neg hj]
    have hzero : rsum ratRing (fun k =>
          ratRing.mul (ctsStretch f k) (ctsStretch g (j - k))) (j + 1)
        = rsum ratRing (fun _ => ratRing.zero) (j + 1) := by
      apply rsum_congr
      intro k hk
      show ratRing.mul (ctsStretch f k) (ctsStretch g (j - k)) = ratRing.zero
      cases Nat.decEq (k % 3) 0 with
      | isFalse hk3 =>
        rw [show ctsStretch f k = ratRing.zero from if_neg hk3]
        exact CRing.zero_mul ratRing _
      | isTrue hk3 =>
        rw [show ctsStretch g (j - k) = ratRing.zero from
            if_neg (show (j - k) % 3 ≠ 0 by omega)]
        exact ratRing.mul_zero _
    rw [hzero, rsum_const_zero ratRing (j + 1)]

/-! ## CTS-5: 円分多項式塔 Φ_{3ⁿ} -/

/-- **CTS-5a: 円分多項式塔** — Φ_{3ⁿ}。基底 Φ₃ = cq0PS（既存）から
    stretch 再帰で構成。ctsPhi 0 は番兵（= Φ₃）、ctsPhi 1 = Φ₃、
    ctsPhi (n+2) = stretch(ctsPhi (n+1))。 -/
def ctsPhi : Nat → PS ratRing
  | 0 => cq0PS
  | 1 => cq0PS
  | n + 2 => ctsStretch (ctsPhi (n + 1))

/-- **CTS-5b: 段の橋** — 1 ≤ n で ctsPhi (n+1) = stretch(ctsPhi n)。 -/
theorem ctsPhi_succ (n : Nat) (hn : 1 ≤ n) :
    ctsPhi (n + 1) = ctsStretch (ctsPhi n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- **CTS-5c: Φ_9 = cpdPhi9** — 二段目が既存 Φ_9 = x⁶+x³+1 と一致。 -/
theorem ctsPhi_two_eq : ctsPhi 2 = cpdPhi9 := by
  show ctsStretch (psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one 2)
      (psSingle ratRing ratRing.one 1)) (psC ratRing ratRing.one))
    = psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one 6)
        (psSingle ratRing ratRing.one 3)) (psC ratRing ratRing.one)
  rw [ctsStretch_add, ctsStretch_add, ctsStretch_single, ctsStretch_single, ctsStretch_psC]

/-! ## CTS-6: 3ⁿ の冪算術（omega 不可・手動補題） -/

/-- **CTS-6a: 3^{n+1} = 3^n·3**（Nat.pow_succ の別名）。 -/
theorem cts_pow3_succ (n : Nat) : (3 : Nat) ^ (n + 1) = 3 ^ n * 3 := Nat.pow_succ 3 n

/-! ## CTS-7: Φ_{3ⁿ} の有界性・先頭係数・係数の局在 -/

/-- **CTS-7a: 有界性（シフト版）** — ctsPhi (n+1) は 2·3ⁿ+1 以上で消える。 -/
theorem ctsPhi_bound_succ : ∀ n, IsPolyBounded ratRing (ctsPhi (n + 1)) (2 * 3 ^ n + 1) := by
  intro n
  induction n with
  | zero => exact cq0_bound
  | succ n ih =>
    have harg : 3 * ((2 * 3 ^ n + 1) - 1) + 1 = 2 * 3 ^ (n + 1) + 1 := by
      rw [cts_pow3_succ n]; omega
    rw [← harg]
    exact ctsStretch_bounded ih

/-- **CTS-7b: 有界性** — deg Φ_{3ⁿ} = 2·3^{n−1}（1 ≤ n）。 -/
theorem ctsPhi_bound (n : Nat) (hn : 1 ≤ n) :
    IsPolyBounded ratRing (ctsPhi n) (2 * 3 ^ (n - 1) + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show IsPolyBounded ratRing (ctsPhi (m + 1)) (2 * 3 ^ m + 1)
  exact ctsPhi_bound_succ m

/-- **CTS-7c: 先頭係数（シフト版）** — ctsPhi (n+1) の 2·3ⁿ 次係数 = 1。 -/
theorem ctsPhi_lead_succ : ∀ n, ctsPhi (n + 1) (2 * 3 ^ n) = ratRing.one := by
  intro n
  induction n with
  | zero => exact cq0PS_coeff2
  | succ n ih =>
    show ctsStretch (ctsPhi (n + 1)) (2 * 3 ^ (n + 1)) = ratRing.one
    show (if (2 * 3 ^ (n + 1)) % 3 = 0 then ctsPhi (n + 1) ((2 * 3 ^ (n + 1)) / 3)
        else ratRing.zero) = ratRing.one
    rw [if_pos (show (2 * 3 ^ (n + 1)) % 3 = 0 by rw [cts_pow3_succ n]; omega),
      show (2 * 3 ^ (n + 1)) / 3 = 2 * 3 ^ n by rw [cts_pow3_succ n]; omega, ih]

/-- **CTS-7d: 先頭係数** — Φ_{3ⁿ} の 2·3^{n−1} 次係数 = 1（1 ≤ n）。 -/
theorem ctsPhi_lead (n : Nat) (hn : 1 ≤ n) :
    ctsPhi n (2 * 3 ^ (n - 1)) = ratRing.one := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show ctsPhi (m + 1) (2 * 3 ^ m) = ratRing.one
  exact ctsPhi_lead_succ m

/-- **CTS-7e: 係数の局在（シフト版）** — ctsPhi (n+1) は j ∉ {0, 3ⁿ, 2·3ⁿ}
    で消える。 -/
theorem ctsPhi_vanish_succ : ∀ n j, j ≠ 0 → j ≠ 3 ^ n → j ≠ 2 * 3 ^ n →
    ctsPhi (n + 1) j = ratRing.zero := by
  intro n
  induction n with
  | zero =>
    intro j hj0 hj1 hj2
    rw [show (3 : Nat) ^ 0 = 1 from rfl] at hj1 hj2
    exact cq0_bound j (by omega)
  | succ n ih =>
    intro j hj0 hj1 hj2
    show (if j % 3 = 0 then ctsPhi (n + 1) (j / 3) else ratRing.zero) = ratRing.zero
    cases Nat.decEq (j % 3) 0 with
    | isFalse h3 => rw [if_neg h3]
    | isTrue h3 =>
      rw [if_pos h3]
      exact ih (j / 3) (by omega)
        (fun hc => hj1 (by rw [cts_pow3_succ n]; omega))
        (fun hc => hj2 (by rw [cts_pow3_succ n]; omega))

/-- **CTS-7f: 係数の局在** — Φ_{3ⁿ} は j ∉ {0, 3^{n−1}, 2·3^{n−1}} で消える
    （1 ≤ n）。E5-3（Φ_{3ⁿ} 既約性）の燃料。 -/
theorem ctsPhi_three_coeffs (n : Nat) (hn : 1 ≤ n) (j : Nat)
    (hj0 : j ≠ 0) (hj1 : j ≠ 3 ^ (n - 1)) (hj2 : j ≠ 2 * 3 ^ (n - 1)) :
    ctsPhi n j = ratRing.zero := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ctsPhi_vanish_succ m j hj0 hj1 hj2

/-! ## CTS-8: 核恒等式 X^{3ⁿ} − 1 = Φ_{3ⁿ}·(X^{3^{n−1}} − 1) -/

/-- **CTS-8a: 核恒等式（シフト版）** — X^{3^{n+1}} − 1 = Φ_{3^{n+1}}·(X^{3ⁿ} − 1)。
    基底 n=0 は cpd_factor 3（x³−1 = Φ₃·(x−1)）、段は両辺 stretch。 -/
theorem cts_pow_sub_one_succ : ∀ n,
    ctsXm1 (3 ^ (n + 1)) = psMul ratRing (ctsPhi (n + 1)) (ctsXm1 (3 ^ n)) := by
  intro n
  induction n with
  | zero =>
    show cpdXpMinus1 3 = psMul ratRing cq0PS cpdXMinus1
    have hcomm : psMul ratRing cpdXMinus1 (cpdPhiP 3)
        = psMul ratRing (cpdPhiP 3) cpdXMinus1 :=
      (psRing ratRing).mul_comm cpdXMinus1 (cpdPhiP 3)
    rw [cpd_factor 3 (by omega), hcomm, cpdPhi3_eq]
  | succ n ih =>
    have key : ctsStretch (ctsXm1 (3 ^ (n + 1)))
        = ctsStretch (psMul ratRing (ctsPhi (n + 1)) (ctsXm1 (3 ^ n))) := by rw [ih]
    rw [cts_xm1, ctsStretch_mul, cts_xm1,
      show 3 * 3 ^ (n + 1) = 3 ^ (n + 2) from by rw [cts_pow3_succ (n + 1)]; omega,
      show 3 * 3 ^ n = 3 ^ (n + 1) from by rw [cts_pow3_succ n]; omega] at key
    exact key

/-- **CTS-8b: 核恒等式** — X^{3ⁿ} − 1 = Φ_{3ⁿ}·(X^{3^{n−1}} − 1)（1 ≤ n）。
    円分塔の telescoping 因数分解（発見 D）。 -/
theorem cts_pow_sub_one (n : Nat) (hn : 1 ≤ n) :
    ctsXm1 (3 ^ n) = psMul ratRing (ctsPhi n) (ctsXm1 (3 ^ (n - 1))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show ctsXm1 (3 ^ (m + 1)) = psMul ratRing (ctsPhi (m + 1)) (ctsXm1 (3 ^ m))
  exact cts_pow_sub_one_succ m

/-! ## CTS-9: 合同輸送（ι_n の map_mul の燃料） -/

/-- **CTS-9: 合同輸送** — Φ_{3ⁿ} を法とする合同 u ≡ v は stretch を通じて
    Φ_{3^{n+1}} を法とする合同 stretch u ≡ stretch v へ持ち上がる（1 ≤ n）。
    witness q ↦ stretch q（u − v = q·Φ_n ⟹ stretch 両辺・CTS-2/CTS-4）。 -/
theorem cts_cong {n : Nat} (hn : 1 ≤ n) {u v : PS ratRing}
    (h : gnfCong (ctsPhi n) u v) :
    gnfCong (ctsPhi (n + 1)) (ctsStretch u) (ctsStretch v) := by
  obtain ⟨q, ⟨N, hN⟩, he⟩ := h
  have he' : psAdd ratRing u (psNeg ratRing v) = psMul ratRing q (ctsPhi n) := he
  refine ⟨ctsStretch q, ⟨3 * (N - 1) + 1, ctsStretch_bounded hN⟩, ?_⟩
  show psAdd ratRing (ctsStretch u) (psNeg ratRing (ctsStretch v))
     = psMul ratRing (ctsStretch q) (ctsPhi (n + 1))
  rw [ctsPhi_succ n hn, ← ctsStretch_mul, ← ctsStretch_neg, ← ctsStretch_add, he']

end IUT
