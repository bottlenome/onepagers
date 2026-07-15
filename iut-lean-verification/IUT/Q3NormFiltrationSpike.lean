/-
  IUT/Q3NormFiltrationSpike.lean — B2 de-risk スパイク: 実高次単数フィルトレーション
    U^(i) = 1 + π₉^i·O_M と 3 次ノルムの graded 挙動 N(1+π₉^i·a) mod π₉^{i+1}

  ── 主要成果の分類: **[実／本物の先行建設(b)]（B2 de-risk スパイク）**。
  B2（実局所類体論・相互写像）を塞いでいた「未発明イディオム」
  （audit/pillar-B2-reciprocity-normgroup-scope-2026-07-11.md §3）——
  実高次単数フィルトレーション U^(i) = 1 + π₉^i·O_M（可除性形式・v_M 不使用）と
  ノルムの graded 挙動 N(1+π₉^i·a) ≡ 1 + T_i(a) mod π₉^{i+1} ——を、
  q3kNormBase（実 3 次ノルム多項式）＋ q9wr の π₉-可除性資産を消費して
  実 Lean で割る。complete_pct 0 前進（w20 B2 の de-risk 基盤・2–3 ラウンド案件の先行）。

  ★★ 重大な de-risk 判定（監査の crux の反証・正直申告）★★
  B2 スコープ（同監査 §1.1）が B2 の crux とした命題
      「∃ x, q3kUnitMem x ∧ q3kNormBase x = q3rqZeta は偽（ζ₃ ∉ N(M^×)）」
  は**数学的に誤り**である。x = ζ₉ = Y が反例:
      N(ζ₉) = ζ₉^(1+σ+σ²) = ζ₉·(ζ₃ζ₉)·(ζ₃²ζ₉) = ζ₃³·ζ₉³ = ζ₉³ = ζ₃、
  かつ ζ₉ は単数（既存 q9tl_normBase_zeta9・q9tl_zeta9_unit が既にこれを証明済み）。
  本ファイルの q9nf_zeta_is_norm はこの ∃ を**証明**する（= 監査 crux の反証）。
  古典側の照合: (ζ₃,ζ₃)₃ = (ζ₃,−1)₃⁻¹ = 1（−1 は 3 乗）なので ζ₃ は本当にノルム。
  監査 §2.2 の q9lr_hilbert_zeta 案 (ζ₃,ζ₃)₃≠1 も偽。B2 の真の crux は
  U^(6)-graded level（上付き break t=2 ⇔ π₉⁶）に住む非ノルム（候補: 4 = 1+3、
  Artin(4)|_M: ζ₉↦ζ₉⁴ ≠ 1）へ**再標的化**しなければならない。q9nf_retarget_witness /
  q9nf_retarget_sharp が 1+3 の正確な filtration 位置 U^(6)∖U^(7) を実証する。

  内容:
   * q9nfPiPow / q9nfUfilt — π₉ 冪と実高次単数フィルトレーション
     U^(i) 所属 = q9wrDvd π₉^i (x−1)（可除性形式・v_M 不使用）
   * q9nf_ufilt_one / q9nf_ufilt_succ / q9nf_ufilt_mul — 1∈U^(i)・U^(i+1)⊆U^(i)・積閉性
   * q9nf_norm_expand（★ 核）— embed(N(1+t)) = 1 + Tr(t) + E₂(t) + embed(N(t))
     の厳密恒等式（q3k_norm_eq = x·σx·σ²x を (1+t) で展開）
   * q9nf_tr_embed / q9nf_trace_kill — Tr(t) = embed(3·t₀)、よって π₉⁶ ∣ Tr(t)。
     「trace 型先頭項 T_i」は低次 graded piece 上**零写像**（graded 先頭項は
     実際にはノルム 3 次項 embed(N t)・π₉ レベル 3i）
   * q9nf_norm_graded（★ i=1 の具体 graded 挙動）— N(1+π₉a) の 4 項分解＋
     各項の π₉-可除性（Tr: π₉⁶ ∣・E₂: π₉² ∣・N 項: π₉³ ∣）
   * q9nf_norm_filt（★ 一般 i）— 1 ≤ i ≤ 5 で N(U^(i)) ⊆ U^(i+1)（embed 側）
   * q9nf_zeta_is_norm（★★ 反証）— ∃x 単数, N(x) = ζ₃（監査 crux の否定を証明）
   * q9nf_zeta_graded_norm_hit / q9nf_zeta_U3 / q9nf_zeta_not_U4 — ζ₃ の正確な
     filtration 位置: embed(ζ₃) ∈ U^(3)∖U^(4)、かつその U^(2) 類は U^(1) からの
     ノルムで**打たれる**（graded level で ζ₃ とノルム像は区別できない——整合的）
   * q9nf_retarget_witness / q9nf_retarget_sharp — 再標的候補 1+3 ∈ U^(6)∖U^(7)
     （真の cokernel が住む graded level の実証）

  正直な限定（§4 規約により消さない・弱めない・q3k/q9ps/q9wr 継承の上に追記のみ）:
  1. **graded level のみ**。完全な非ノルム定理（再標的後の crux、例: 4 ∉ N(M^×)）は
     本スパイクの範囲外——それは複数ラウンドの B2 本体（level 6 での余核の同定を要する）。
  2. **可除性形式のみ（v_M 不在）**。トレース項の π₉-可除性は座標評価による下界
     π₉⁶（= embed(3) の分割）のみ。真のトレース減衰 Tr(m^i) ⊆ m_{L₂}^{⌈(6+i)/3⌉} は
     v_M を要し未形式化——このため q9nf_norm_filt は i ≤ 5 に限定（i=1 の核心域は完全）。
  3. E₂ 項の可除性も粗い下界 π₉^{2i}（真値は Galois 不変性から 3⌈2i/3⌉）。
  4. **拡大 1 個（M/L₂）**・Artin 写像・Hilbert 記号・余核の同定はゼロ。
  5. 監査 crux の反証（q9nf_zeta_is_norm）は既存 q9tl 資産の束ねであり本ファイルの
     新規計算ではない——新規なのは U^(i)・graded 分解・filtration 位置計算。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3WildRamFiltrationReal
import IUT.Q3KummerCubeIdent

namespace IUT

/-! ## q9nf-0: ブリッジと一般可換環補題 -/

/-- q3kAdd = q3kRing.add（rfl ブリッジ）。 -/
theorem q9nf_kA_eq : q3kAdd = q3kRing.add := rfl

/-- q3kZero = q3kRing.zero（rfl ブリッジ）。 -/
theorem q9nf_kZ_eq : q3kZero = q3kRing.zero := rfl

/-- u + (v + w) = v + (u + w)（一般 CRing の swap）。 -/
theorem q9nf_add_swap (R : CRing) (u v w : R.carrier) :
    R.add u (R.add v w) = R.add v (R.add u w) := by
  rw [← R.add_assoc u v w, R.add_comm u v, R.add_assoc v u w]

/-- **(1+a)(1+b)(1+c) の完全展開**（一般 CRing）:
    = 1 + (a+(b+c)) + ((ab+(ac+bc)) + a(bc))。ノルム graded 分解の骨格。 -/
theorem q9nf_cube_expand (R : CRing) (a b c : R.carrier) :
    R.mul (R.add R.one a) (R.mul (R.add R.one b) (R.add R.one c))
    = R.add R.one (R.add (R.add a (R.add b c))
        (R.add (R.add (R.mul a b) (R.add (R.mul a c) (R.mul b c)))
          (R.mul a (R.mul b c)))) := by
  have h1 : R.mul (R.add R.one b) (R.add R.one c)
      = R.add R.one (R.add (R.add b c) (R.mul b c)) := by
    rw [R.right_distrib R.one b (R.add R.one c),
        R.one_mul (R.add R.one c),
        R.left_distrib b R.one c,
        R.mul_one b,
        R.add_assoc R.one c (R.add b (R.mul b c)),
        q9nf_add_swap R c b (R.mul b c),
        ← R.add_assoc b c (R.mul b c)]
  rw [h1,
      R.right_distrib R.one a (R.add R.one (R.add (R.add b c) (R.mul b c))),
      R.one_mul (R.add R.one (R.add (R.add b c) (R.mul b c))),
      R.left_distrib a R.one (R.add (R.add b c) (R.mul b c)),
      R.mul_one a,
      R.left_distrib a (R.add b c) (R.mul b c),
      R.left_distrib a b c,
      R.add_assoc R.one (R.add (R.add b c) (R.mul b c))
        (R.add a (R.add (R.add (R.mul a b) (R.mul a c)) (R.mul a (R.mul b c)))),
      q9nf_add_swap R (R.add (R.add b c) (R.mul b c)) a
        (R.add (R.add (R.mul a b) (R.mul a c)) (R.mul a (R.mul b c))),
      R.add_assoc (R.add b c) (R.mul b c)
        (R.add (R.add (R.mul a b) (R.mul a c)) (R.mul a (R.mul b c))),
      ← R.add_assoc (R.mul b c) (R.add (R.mul a b) (R.mul a c)) (R.mul a (R.mul b c)),
      q9nf_add_swap R (R.mul b c) (R.mul a b) (R.mul a c),
      R.add_comm (R.mul b c) (R.mul a c),
      ← R.add_assoc a (R.add b c)
        (R.add (R.add (R.mul a b) (R.add (R.mul a c) (R.mul b c))) (R.mul a (R.mul b c)))]

/-- (1 + S) + (−1) = S（単数フィルトレーションの標準相殺）。 -/
theorem q9nf_one_add_cancel (S : q3kCar) :
    q3kAdd (q3kAdd q3kOne S) (q3kNeg q3kOne) = S := by
  rw [q9nf_kA_eq, q9ps_kN_eq, q9ps_kO_eq,
      q3kRing.add_comm q3kRing.one S,
      q3kRing.add_assoc S q3kRing.one (q3kRing.neg q3kRing.one),
      q3kRing.add_neg q3kRing.one, q3kRing.add_zero S]

/-! ## q9nf-1: π₉ 冪と可除性計算 -/

/-- π₉ の冪（π₉⁰ = 1・π₉^{n+1} = π₉·π₉^n）。 -/
def q9nfPiPow : Nat → q3kCar
  | 0 => q3kOne
  | n + 1 => q3kMul q9psPi9 (q9nfPiPow n)

/-- π₉^{m+n} = π₉^m·π₉^n。 -/
theorem q9nf_pipow_add (m n : Nat) :
    q9nfPiPow (m + n) = q3kMul (q9nfPiPow m) (q9nfPiPow n) := by
  induction n with
  | zero =>
    show q9nfPiPow m = q3kMul (q9nfPiPow m) q3kOne
    rw [q3k_kM_eq, q9ps_kO_eq]
    exact (q3kRing.mul_one (q9nfPiPow m)).symm
  | succ n ih =>
    show q3kMul q9psPi9 (q9nfPiPow (m + n))
        = q3kMul (q9nfPiPow m) (q3kMul q9psPi9 (q9nfPiPow n))
    rw [ih, q3k_kM_eq]
    exact q3kRing.mul_left_comm q9psPi9 (q9nfPiPow m) (q9nfPiPow n)

/-- π₉¹ = π₉。 -/
theorem q9nf_pipow1_eq : q9nfPiPow 1 = q9psPi9 := by
  show q3kMul q9psPi9 q3kOne = q9psPi9
  rw [q3k_kM_eq, q9ps_kO_eq]
  exact q3kRing.mul_one q9psPi9

/-- π₉³ = q9psPi9Cubed（q9wr の (π₉π₉)π₉ 形へのブリッジ）。 -/
theorem q9nf_pipow3_eq : q9nfPiPow 3 = q9psPi9Cubed := by
  show q3kMul q9psPi9 (q3kMul q9psPi9 (q3kMul q9psPi9 q3kOne))
      = q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9
  rw [q3k_kM_eq, q9ps_kO_eq, q3kRing.mul_one q9psPi9]
  exact (q3kRing.mul_assoc q9psPi9 q9psPi9 q9psPi9).symm

/-- π₉⁶ = q9psPi6（q9ps の wild 分割 3 = π₉⁶·u₆ へのブリッジ）。 -/
theorem q9nf_pipow6_eq : q9nfPiPow 6 = q9psPi6 := by
  have h : q9nfPiPow (3 + 3) = q3kMul (q9nfPiPow 3) (q9nfPiPow 3) := q9nf_pipow_add 3 3
  rw [q9nf_pipow3_eq] at h
  exact h

/-- 可除性: d ∣ 0。 -/
theorem q9nf_dvd_zero (d : q3kCar) : q9wrDvd d q3kZero :=
  ⟨q3kZero, by
    rw [q3k_kM_eq, q9nf_kZ_eq]
    exact (q3kRing.mul_zero d).symm⟩

/-- 可除性は加法で閉じる。 -/
theorem q9nf_dvd_add {d x y : q3kCar}
    (hx : q9wrDvd d x) (hy : q9wrDvd d y) : q9wrDvd d (q3kAdd x y) := by
  obtain ⟨cx, hcx⟩ := hx
  obtain ⟨cy, hcy⟩ := hy
  exact ⟨q3kAdd cx cy, by
    rw [hcx, hcy, q3k_kM_eq, q9nf_kA_eq]
    exact (q3kRing.left_distrib d cx cy).symm⟩

/-- d ∣ x ⟹ d ∣ x·y。 -/
theorem q9nf_dvd_mul_right {d x : q3kCar} (h : q9wrDvd d x) (y : q3kCar) :
    q9wrDvd d (q3kMul x y) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨q3kMul c y, by
    rw [hc, q3k_kM_eq]
    exact q3kRing.mul_assoc d c y⟩

/-- π₉^m ∣ x かつ π₉^n ∣ y ⟹ π₉^{m+n} ∣ x·y。 -/
theorem q9nf_dvd_mul {m n : Nat} {x y : q3kCar}
    (hx : q9wrDvd (q9nfPiPow m) x) (hy : q9wrDvd (q9nfPiPow n) y) :
    q9wrDvd (q9nfPiPow (m + n)) (q3kMul x y) := by
  obtain ⟨cx, hcx⟩ := hx
  obtain ⟨cy, hcy⟩ := hy
  exact ⟨q3kMul cx cy, by
    rw [hcx, hcy, q9nf_pipow_add m n, q3k_kM_eq]
    exact q3kRing.mul_mul_mul_comm (q9nfPiPow m) cx (q9nfPiPow n) cy⟩

/-- π₉^{m+k} ∣ x ⟹ π₉^m ∣ x（指数の単調性・加法形）。 -/
theorem q9nf_dvd_mono {m k : Nat} {x : q3kCar}
    (h : q9wrDvd (q9nfPiPow (m + k)) x) : q9wrDvd (q9nfPiPow m) x := by
  obtain ⟨c, hc⟩ := h
  exact ⟨q3kMul (q9nfPiPow k) c, by
    rw [hc, q9nf_pipow_add m k, q3k_kM_eq]
    exact q3kRing.mul_assoc (q9nfPiPow m) (q9nfPiPow k) c⟩

/-- π₉^n ∣ x かつ m ≤ n ⟹ π₉^m ∣ x。 -/
theorem q9nf_dvd_of_le {m n : Nat} (hmn : m ≤ n) {x : q3kCar}
    (h : q9wrDvd (q9nfPiPow n) x) : q9wrDvd (q9nfPiPow m) x := by
  obtain ⟨k, hk⟩ := Nat.le.dest hmn
  rw [← hk] at h
  exact q9nf_dvd_mono h

/-! ## q9nf-2: 実高次単数フィルトレーション U^(i) = 1 + π₉^i·O_M -/

/-- **U^(i) 所属**（可除性形式・v_M 不使用）: x ∈ 1 + π₉^i·O_M ⟺ π₉^i ∣ (x − 1)。 -/
def q9nfUfilt (i : Nat) (x : q3kCar) : Prop :=
  q9wrDvd (q9nfPiPow i) (q3kAdd x (q3kNeg q3kOne))

/-- 1 ∈ U^(i)（全 i）。 -/
theorem q9nf_ufilt_one (i : Nat) : q9nfUfilt i q3kOne := by
  show q9wrDvd (q9nfPiPow i) (q3kAdd q3kOne (q3kNeg q3kOne))
  rw [q9nf_kA_eq, q9ps_kN_eq, q9ps_kO_eq, q3kRing.add_neg q3kRing.one]
  exact q9nf_dvd_zero (q9nfPiPow i)

/-- U^(i+k) ⊆ U^(i)（フィルトレーションの単調性）。 -/
theorem q9nf_ufilt_antitone {i k : Nat} {x : q3kCar}
    (h : q9nfUfilt (i + k) x) : q9nfUfilt i x :=
  q9nf_dvd_mono h

/-- U^(i+1) ⊆ U^(i)。 -/
theorem q9nf_ufilt_succ {i : Nat} {x : q3kCar}
    (h : q9nfUfilt (i + 1) x) : q9nfUfilt i x :=
  q9nf_ufilt_antitone (i := i) (k := 1) h

/-- **U^(i) の積閉性**: x, y ∈ U^(i) ⟹ xy ∈ U^(i)（xy−1 = (x−1)y + (y−1)）。 -/
theorem q9nf_ufilt_mul {i : Nat} {x y : q3kCar}
    (hx : q9nfUfilt i x) (hy : q9nfUfilt i y) : q9nfUfilt i (q3kMul x y) := by
  have hkey : q3kAdd (q3kMul x y) (q3kNeg q3kOne)
      = q3kAdd (q3kMul (q3kAdd x (q3kNeg q3kOne)) y) (q3kAdd y (q3kNeg q3kOne)) := by
    rw [q3k_kM_eq, q9nf_kA_eq, q9ps_kN_eq, q9ps_kO_eq,
        q3kRing.right_distrib x (q3kRing.neg q3kRing.one) y,
        q3kRing.neg_mul q3kRing.one y, q3kRing.one_mul y,
        q3kRing.add_assoc (q3kRing.mul x y) (q3kRing.neg y)
          (q3kRing.add y (q3kRing.neg q3kRing.one)),
        ← q3kRing.add_assoc (q3kRing.neg y) y (q3kRing.neg q3kRing.one),
        q3kRing.neg_add y, q3kRing.zero_add (q3kRing.neg q3kRing.one)]
  show q9wrDvd (q9nfPiPow i) (q3kAdd (q3kMul x y) (q3kNeg q3kOne))
  rw [hkey]
  exact q9nf_dvd_add (q9nf_dvd_mul_right hx y) hy

/-- U^(i) 所属の分解: x ∈ U^(i) ⟹ x = 1 + π₉^i·a。 -/
theorem q9nf_ufilt_decomp {i : Nat} {x : q3kCar} (h : q9nfUfilt i x) :
    ∃ a : q3kCar, x = q3kAdd q3kOne (q3kMul (q9nfPiPow i) a) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [← hc, q9nf_kA_eq, q9ps_kN_eq, q9ps_kO_eq,
      q3kRing.add_comm x (q3kRing.neg q3kRing.one),
      ← q3kRing.add_assoc q3kRing.one (q3kRing.neg q3kRing.one) x,
      q3kRing.add_neg q3kRing.one, q3kRing.zero_add x]

/-! ## q9nf-3: σ の加法性・σπ₉ の分解・σ の π₉-可除性保存 -/

/-- σ は加法的（座標: ζ 倍の分配）。 -/
theorem q9nf_sigma_add (x y : q3kCar) :
    q3kSigma (q3kAdd x y) = q3kAdd (q3kSigma x) (q3kSigma y) := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta (q3rqAdd x.2.1 y.2.1)
        = q3rqAdd (q3rqMul q3rqZeta x.2.1) (q3rqMul q3rqZeta y.2.1)
    rw [q3k_M_eq, q3k_A_eq]
    exact q3rqRing.left_distrib q3rqZeta x.2.1 y.2.1
  · show q3rqMul q3rqZetaSq (q3rqAdd x.2.2 y.2.2)
        = q3rqAdd (q3rqMul q3rqZetaSq x.2.2) (q3rqMul q3rqZetaSq y.2.2)
    rw [q3k_M_eq, q3k_A_eq]
    exact q3rqRing.left_distrib q3rqZetaSq x.2.2 y.2.2

/-- σ² は加法的。 -/
theorem q9nf_sigma2_add (x y : q3kCar) :
    q3kSigma2 (q3kAdd x y) = q3kAdd (q3kSigma2 x) (q3kSigma2 y) := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZetaSq (q3rqAdd x.2.1 y.2.1)
        = q3rqAdd (q3rqMul q3rqZetaSq x.2.1) (q3rqMul q3rqZetaSq y.2.1)
    rw [q3k_M_eq, q3k_A_eq]
    exact q3rqRing.left_distrib q3rqZetaSq x.2.1 y.2.1
  · show q3rqMul q3rqZeta (q3rqAdd x.2.2 y.2.2)
        = q3rqAdd (q3rqMul q3rqZeta x.2.2) (q3rqMul q3rqZeta y.2.2)
    rw [q3k_M_eq, q3k_A_eq]
    exact q3rqRing.left_distrib q3rqZeta x.2.2 y.2.2

/-- **σπ₉ = π₉·(1 + π₉²·u\*)**（q9wr_sigma_pi_eq の乗法分解形——σ が π₉-可除性を
    保存する理由の閉形式）。 -/
theorem q9nf_sigma_pi9 :
    q3kSigma q9psPi9
      = q3kMul q9psPi9 (q3kAdd q3kOne (q3kMul (q3kMul q9psPi9 q9psPi9) q9wrUStar)) := by
  have h2 : q3kSigma q9psPi9
      = q3kAdd q9psPi9 (q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9wrUStar) := by
    rw [← q9wr_sigma_pi_eq, q9nf_kA_eq, q9ps_kN_eq,
        q3kRing.add_comm (q3kSigma q9psPi9) (q3kRing.neg q9psPi9),
        ← q3kRing.add_assoc q9psPi9 (q3kRing.neg q9psPi9) (q3kSigma q9psPi9),
        q3kRing.add_neg q9psPi9, q3kRing.zero_add (q3kSigma q9psPi9)]
  rw [h2, q9nf_kA_eq, q3k_kM_eq, q9ps_kO_eq,
      q3kRing.left_distrib q9psPi9 q3kRing.one
        (q3kRing.mul (q3kRing.mul q9psPi9 q9psPi9) q9wrUStar),
      q3kRing.mul_one q9psPi9,
      ← q3kRing.mul_assoc q9psPi9 (q3kRing.mul q9psPi9 q9psPi9) q9wrUStar,
      ← q3kRing.mul_assoc q9psPi9 q9psPi9 q9psPi9]

/-- **σ は π₉-可除性を保存する**: π₉^m ∣ x ⟹ π₉^m ∣ σx（m 帰納・σπ₉ 分解を消費）。 -/
theorem q9nf_dvd_sigma (m : Nat) (x : q3kCar)
    (h : q9wrDvd (q9nfPiPow m) x) : q9wrDvd (q9nfPiPow m) (q3kSigma x) := by
  induction m generalizing x with
  | zero =>
    exact ⟨q3kSigma x, (q3k_one_mul (q3kSigma x)).symm⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := h
    have hx' : x = q3kMul q9psPi9 (q3kMul (q9nfPiPow m) c) := by
      have hc' : x = q3kMul (q3kMul q9psPi9 (q9nfPiPow m)) c := hc
      rw [hc', q3k_kM_eq]
      exact q3kRing.mul_assoc q9psPi9 (q9nfPiPow m) c
    obtain ⟨d, hd⟩ := ih (q3kMul (q9nfPiPow m) c) ⟨c, rfl⟩
    refine ⟨q3kMul (q3kAdd q3kOne (q3kMul (q3kMul q9psPi9 q9psPi9) q9wrUStar)) d, ?_⟩
    show q3kSigma x
        = q3kMul (q3kMul q9psPi9 (q9nfPiPow m))
            (q3kMul (q3kAdd q3kOne (q3kMul (q3kMul q9psPi9 q9psPi9) q9wrUStar)) d)
    rw [hx', q3k_sigma_mul q9psPi9 (q3kMul (q9nfPiPow m) c), hd, q9nf_sigma_pi9,
        q3k_kM_eq]
    exact q3kRing.mul_mul_mul_comm q9psPi9
      (q3kAdd q3kOne (q3kMul (q3kMul q9psPi9 q9psPi9) q9wrUStar)) (q9nfPiPow m) d

/-- σ² も π₉-可除性を保存する（σ∘σ）。 -/
theorem q9nf_dvd_sigma2 (m : Nat) (x : q3kCar)
    (h : q9wrDvd (q9nfPiPow m) x) : q9wrDvd (q9nfPiPow m) (q3kSigma2 x) := by
  rw [q3k_sigma2_comp x]
  exact q9nf_dvd_sigma m (q3kSigma x) (q9nf_dvd_sigma m x h)

/-! ## q9nf-4: トレースと E₂（対称多項式）・ノルム展開恒等式 -/

/-- 実トレース Tr(t) = t + σt + σ²t。 -/
def q9nfTr (t : q3kCar) : q3kCar :=
  q3kAdd t (q3kAdd (q3kSigma t) (q3kSigma2 t))

/-- 第 2 対称項 E₂(t) = t·σt + t·σ²t + σt·σ²t。 -/
def q9nfE2 (t : q3kCar) : q3kCar :=
  q3kAdd (q3kMul t (q3kSigma t))
    (q3kAdd (q3kMul t (q3kSigma2 t)) (q3kMul (q3kSigma t) (q3kSigma2 t)))

/-- **Tr(t) = embed(3·t₀)**（1+ζ₃+ζ₃²=0 が Y・Y² 成分を消す——トレースの閉形式）。 -/
theorem q9nf_tr_embed (t : q3kCar) :
    q9nfTr t = q3kEmbed (q3rqMul q3kThree t.1) := by
  apply q3k_ext
  · show q3rqAdd t.1 (q3rqAdd t.1 t.1)
        = q3rqMul (q3rqAdd q3rqOne (q3rqAdd q3rqOne q3rqOne)) t.1
    rw [q3k_M_eq, q3k_A_eq, q9ps_1_eq,
        q3rqRing.right_distrib q3rqRing.one (q3rqRing.add q3rqRing.one q3rqRing.one) t.1,
        q3rqRing.right_distrib q3rqRing.one q3rqRing.one t.1,
        q3rqRing.one_mul t.1]
  · show q3rqAdd t.2.1 (q3rqAdd (q3rqMul q3rqZeta t.2.1) (q3rqMul q3rqZetaSq t.2.1))
        = q3rqZero
    rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3k_bc3 t.2.1, q3rqRing.add_neg t.2.1]
  · show q3rqAdd t.2.2 (q3rqAdd (q3rqMul q3rqZetaSq t.2.2) (q3rqMul q3rqZeta t.2.2))
        = q3rqZero
    rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3k_bc2 t.2.2, q3rqRing.add_neg t.2.2]

/-- **★ トレース kill**: π₉⁶ ∣ Tr(t)（全 t）。Tr(t) = embed(3·t₀) と 3 = π₉⁶·u₆
    （q9ps_three_split）の消費。graded norm の「trace 型先頭項」T_i は
    レベル 6 未満の graded piece 上で**零写像**——監査が期待した
    「T₁ の非全射性による ζ₃ 排除」は存在しない（実際の先頭項はノルム 3 次項）。 -/
theorem q9nf_trace_kill (t : q3kCar) : q9wrDvd (q9nfPiPow 6) (q9nfTr t) := by
  rw [q9nf_tr_embed t, ← q3k_embed_mul q3kThree t.1, q9ps_three_eq, ← q9ps_three_split]
  refine ⟨q3kMul q9psU6 (q3kEmbed t.1), ?_⟩
  rw [q9nf_pipow6_eq, q3k_kM_eq]
  exact q3kRing.mul_assoc q9psPi6 q9psU6 (q3kEmbed t.1)

/-- **★★ ノルム展開恒等式（核）**: embed(N(1+t)) = 1 + Tr(t) + E₂(t) + embed(N(t))。
    q3k_norm_eq（N(x) = x·σx·σ²x）を x = 1+t で展開した厳密恒等式——
    B2 スコープ §3 が「未発明」とした graded 挙動の代数的本体。 -/
theorem q9nf_norm_expand (t : q3kCar) :
    q3kEmbed (q3kNormBase (q3kAdd q3kOne t))
    = q3kAdd q3kOne (q3kAdd (q9nfTr t)
        (q3kAdd (q9nfE2 t) (q3kEmbed (q3kNormBase t)))) := by
  rw [← q3k_norm_eq (q3kAdd q3kOne t), ← q3k_norm_eq t,
      q9nf_sigma_add q3kOne t, q3k_sigma_one,
      q9nf_sigma2_add q3kOne t, q3k_sigma2_one]
  show q3kMul (q3kAdd q3kOne t)
      (q3kMul (q3kAdd q3kOne (q3kSigma t)) (q3kAdd q3kOne (q3kSigma2 t)))
    = q3kAdd q3kOne (q3kAdd (q3kAdd t (q3kAdd (q3kSigma t) (q3kSigma2 t)))
        (q3kAdd (q3kAdd (q3kMul t (q3kSigma t))
            (q3kAdd (q3kMul t (q3kSigma2 t)) (q3kMul (q3kSigma t) (q3kSigma2 t))))
          (q3kMul t (q3kMul (q3kSigma t) (q3kSigma2 t)))))
  rw [q3k_kM_eq, q9nf_kA_eq, q9ps_kO_eq]
  exact q9nf_cube_expand q3kRing t (q3kSigma t) (q3kSigma2 t)

/-- E₂ の可除性: π₉^m ∣ t ⟹ π₉^{2m} ∣ E₂(t)（3 つの 2 次積すべて）。 -/
theorem q9nf_e2_dvd (m : Nat) (t : q3kCar) (h : q9wrDvd (q9nfPiPow m) t) :
    q9wrDvd (q9nfPiPow (m + m)) (q9nfE2 t) := by
  have hs := q9nf_dvd_sigma m t h
  have hs2 := q9nf_dvd_sigma2 m t h
  exact q9nf_dvd_add (q9nf_dvd_mul h hs)
    (q9nf_dvd_add (q9nf_dvd_mul h hs2) (q9nf_dvd_mul hs hs2))

/-- ノルム 3 次項の可除性: π₉^m ∣ t ⟹ π₉^{3m} ∣ embed(N(t))（N(t) = t·σt·σ²t）。 -/
theorem q9nf_normterm_dvd (m : Nat) (t : q3kCar) (h : q9wrDvd (q9nfPiPow m) t) :
    q9wrDvd (q9nfPiPow (m + (m + m))) (q3kEmbed (q3kNormBase t)) := by
  rw [← q3k_norm_eq t]
  exact q9nf_dvd_mul h (q9nf_dvd_mul (q9nf_dvd_sigma m t h) (q9nf_dvd_sigma2 m t h))

/-- π₉ ∣ π₉·a（レベル 1 の自明可除性）。 -/
theorem q9nf_dvd_pi_mul (a : q3kCar) : q9wrDvd (q9nfPiPow 1) (q3kMul q9psPi9 a) :=
  ⟨a, by rw [q9nf_pipow1_eq]⟩

/-! ## q9nf-5: ★ ノルムの graded 挙動（i=1 の具体形と一般 i） -/

/-- **★★★ q9nf_norm_graded（i=1 の graded 挙動・スパイクの核心）**:
    N(1+π₉·a) = 1 + Tr(π₉a) + E₂(π₉a) + embed(N(π₉a)) の厳密 4 項分解、かつ
    各項の π₉-可除性: π₉⁶ ∣ Tr・π₉² ∣ E₂・π₉³ ∣ embed(N(π₉a))。
    したがって N(1+π₉a) ≡ 1 + Tr(π₉a) ≡ 1 (mod π₉²)——先頭 graded 項は
    trace ではなくレベル 3 のノルム 3 次項 embed((ζ₃−1)·N(a))。 -/
theorem q9nf_norm_graded (a : q3kCar) :
    q3kEmbed (q3kNormBase (q3kAdd q3kOne (q3kMul q9psPi9 a)))
      = q3kAdd q3kOne (q3kAdd (q9nfTr (q3kMul q9psPi9 a))
          (q3kAdd (q9nfE2 (q3kMul q9psPi9 a))
            (q3kEmbed (q3kNormBase (q3kMul q9psPi9 a)))))
    ∧ q9wrDvd (q9nfPiPow 6) (q9nfTr (q3kMul q9psPi9 a))
    ∧ q9wrDvd (q9nfPiPow 2) (q9nfE2 (q3kMul q9psPi9 a))
    ∧ q9wrDvd (q9nfPiPow 3) (q3kEmbed (q3kNormBase (q3kMul q9psPi9 a))) :=
  ⟨q9nf_norm_expand (q3kMul q9psPi9 a),
   q9nf_trace_kill (q3kMul q9psPi9 a),
   q9nf_e2_dvd 1 (q3kMul q9psPi9 a) (q9nf_dvd_pi_mul a),
   q9nf_normterm_dvd 1 (q3kMul q9psPi9 a) (q9nf_dvd_pi_mul a)⟩

/-- **★ 一般 i の graded 移送**: 1 ≤ i = j+1 ≤ 5 で x ∈ U^(i) ⟹ embed(N(x)) ∈ U^(i+1)。
    上界 i ≤ 5 は trace 項の座標下界 π₉⁶（正直限定 2）に由来——i=1..5 の核心域
    （break t=2 と余核 level 6 を含む）は完全にカバー。 -/
theorem q9nf_norm_filt {j : Nat} (hj : j ≤ 4) {x : q3kCar}
    (hx : q9nfUfilt (j + 1) x) :
    q9nfUfilt (j + 2) (q3kEmbed (q3kNormBase x)) := by
  obtain ⟨a, ha⟩ := q9nf_ufilt_decomp hx
  show q9wrDvd (q9nfPiPow (j + 2)) (q3kAdd (q3kEmbed (q3kNormBase x)) (q3kNeg q3kOne))
  rw [ha, q9nf_norm_expand (q3kMul (q9nfPiPow (j + 1)) a), q9nf_one_add_cancel]
  refine q9nf_dvd_add ?_ (q9nf_dvd_add ?_ ?_)
  · exact q9nf_dvd_of_le (by omega) (q9nf_trace_kill (q3kMul (q9nfPiPow (j + 1)) a))
  · exact q9nf_dvd_of_le (by omega)
      (q9nf_e2_dvd (j + 1) (q3kMul (q9nfPiPow (j + 1)) a) ⟨a, rfl⟩)
  · exact q9nf_dvd_of_le (by omega)
      (q9nf_normterm_dvd (j + 1) (q3kMul (q9nfPiPow (j + 1)) a) ⟨a, rfl⟩)

/-- **N(U^(1)) ⊆ U^(2)**（i=1 の filtration 形）。 -/
theorem q9nf_norm_U1_U2 {x : q3kCar} (hx : q9nfUfilt 1 x) :
    q9nfUfilt 2 (q3kEmbed (q3kNormBase x)) :=
  q9nf_norm_filt (j := 0) (by omega) hx

/-! ## q9nf-6: ★★ payoff——監査 crux の反証と ζ₃ の正確な filtration 位置

  B2 スコープ §1.1 の crux「∃ x, q3kUnitMem x ∧ q3kNormBase x = q3rqZeta は偽」は
  **反証される**（x = ζ₉）。graded level での正しい描像:
  ζ₉ = 1 + π₉ ∈ U^(1)、N(ζ₉) = ζ₃、embed(ζ₃) ∈ U^(3)∖U^(4)——
  ノルム 3 次項の graded レベル 3 が ζ₃−1 のレベル 3 と正確に一致し、
  ζ₃ の U-類はノルム像に**含まれる**（q9nf_zeta_graded_norm_hit）。 -/

/-- ζ₉ = 1 + π₉（U^(1) 分解の見出し例）。 -/
theorem q9nf_zeta9_eq_one_add_pi9 : q3kZeta9 = q3kAdd q3kOne q9psPi9 := by
  show q3kZeta9 = q3kAdd q3kOne (q3kAdd q3kZeta9 (q3kNeg q3kOne))
  rw [q9nf_kA_eq, q9ps_kN_eq, q9ps_kO_eq,
      q3kRing.add_comm q3kZeta9 (q3kRing.neg q3kRing.one),
      ← q3kRing.add_assoc q3kRing.one (q3kRing.neg q3kRing.one) q3kZeta9,
      q3kRing.add_neg q3kRing.one, q3kRing.zero_add q3kZeta9]

/-- ζ₉ ∈ U^(1)（ζ₉ − 1 = π₉）。 -/
theorem q9nf_zeta9_U1 : q9nfUfilt 1 q3kZeta9 := by
  refine ⟨q3kOne, ?_⟩
  show q9psPi9 = q3kMul (q9nfPiPow 1) q3kOne
  rw [q9nf_pipow1_eq, q3k_kM_eq, q9ps_kO_eq]
  exact (q3kRing.mul_one q9psPi9).symm

/-- **★★ 監査 crux の反証**: ζ₃ は実 3 次ノルムの像に**ある**——
    ∃ x 単数, N(x) = ζ₃（x = ζ₉・q9tl 資産の消費）。
    B2 スコープが「偽であるべき」とした ∃ 命題そのものの証明。
    ζ₃∉N(M^×) ルートでの B2 は**数学的に不可能**であり再標的化が必須。 -/
theorem q9nf_zeta_is_norm : ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q3rqZeta :=
  ⟨q3kZeta9, q9tl_zeta9_unit, q9tl_normBase_zeta9⟩

/-- **ζ₃ の U^(2)-類はノルムで打たれる**: embed(N(ζ₉)) = embed(ζ₃) ∈ U^(2)
    （q9nf_norm_U1_U2 の見出し実行——graded 機構と反証の整合性検査）。 -/
theorem q9nf_zeta_graded_norm_hit : q9nfUfilt 2 (q3kEmbed q3rqZeta) := by
  rw [← q9tl_normBase_zeta9]
  exact q9nf_norm_U1_U2 q9nf_zeta9_U1

/-- embed(ζ₃) − 1 = embed(ζ₃ − 1)（座標）。 -/
theorem q9nf_embed_zeta_sub :
    q3kAdd (q3kEmbed q3rqZeta) (q3kNeg q3kOne)
      = q3kEmbed (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta) := by
  apply q3k_ext
  · show q3rqAdd q3rqZeta (q3rqNeg q3rqOne) = q3rqAdd (q3rqNeg q3rqOne) q3rqZeta
    rw [q3k_A_eq]
    exact q3rqRing.add_comm q3rqZeta (q3rqNeg q3rqOne)
  · show q3rqAdd q3rqZero (q3rqNeg q3rqZero) = q3rqZero
    rw [q3k_A_eq, q3k_N_eq, q3k_Z_eq, q3rqRing.neg_zero,
        q3rqRing.zero_add q3rqRing.zero]
  · show q3rqAdd q3rqZero (q3rqNeg q3rqZero) = q3rqZero
    rw [q3k_A_eq, q3k_N_eq, q3k_Z_eq, q3rqRing.neg_zero,
        q3rqRing.zero_add q3rqRing.zero]

/-- embed(λ) = π₉³·w⁻¹（q9ps_pi9_cube の逆単数化）。 -/
theorem q9nf_embed_lambda : q3kEmbed q3rqLambda = q3kMul (q9nfPiPow 3) q9psWinv := by
  have h : q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psWinv
      = q3kMul (q3kEmbed q3rqLambda) (q3kMul q9psW q9psWinv) := by
    rw [q9ps_pi9_cube, q3k_kM_eq]
    exact q3kRing.mul_assoc (q3kEmbed q3rqLambda) q9psW q9psWinv
  have h2 : q3kMul (q9nfPiPow 3) q9psWinv = q3kEmbed q3rqLambda := by
    rw [q9nf_pipow3_eq]
    show q3kMul (q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9) q9psWinv = q3kEmbed q3rqLambda
    rw [h, q9ps_w_inv_mul, q3k_kM_eq, q9ps_kO_eq]
    exact q3kRing.mul_one (q3kEmbed q3rqLambda)
  exact h2.symm

/-- embed(ζ₃−1) = π₉³·(w⁻¹·embed(ζ₃+1))——ζ₃−1 の π₉-レベル 3 分解。 -/
theorem q9nf_zeta_sub_one_split :
    q3kEmbed (q3rqAdd (q3rqNeg q3rqOne) q3rqZeta)
      = q3kMul (q9nfPiPow 3) (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne))) := by
  have hzz : q3rqAdd (q3rqNeg q3rqOne) q3rqZeta
      = q3rqMul q3rqLambda (q3rqAdd q3rqZeta q3rqOne) := by
    rw [q3k_M_eq, q3k_A_eq, q3k_N_eq, q9ps_1_eq]
    exact q9ps_coord0.symm
  rw [hzz, ← q3k_embed_mul q3rqLambda (q3rqAdd q3rqZeta q3rqOne), q9nf_embed_lambda,
      q3k_kM_eq]
  exact q3kRing.mul_assoc (q9nfPiPow 3) q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne))

/-- **ζ₃ ∈ U^(3)**（embed 側・ζ₃−1 = π₉³·単数——filtration 位置の下界）。 -/
theorem q9nf_zeta_U3 : q9nfUfilt 3 (q3kEmbed q3rqZeta) := by
  show q9wrDvd (q9nfPiPow 3) (q3kAdd (q3kEmbed q3rqZeta) (q3kNeg q3kOne))
  rw [q9nf_embed_zeta_sub, q9nf_zeta_sub_one_split]
  exact ⟨q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne)), rfl⟩

/-- **★ ζ₃ ∉ U^(4)**（filtration 位置の上界・ζ₃ の gr³ 類は非零）。
    U6 イディオム（π₉³ 相殺 → ノルム 2 段 → 3·s 非単数）の U^(i) への一般化——
    「一様化子でない実単数の正確な graded 位置」を割る初の実例。 -/
theorem q9nf_zeta_not_U4 : ¬ q9nfUfilt 4 (q3kEmbed q3rqZeta) := by
  intro h
  obtain ⟨c, hc⟩ := h
  have hL : q3kMul (q9nfPiPow 3) (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne)))
      = q3kMul (q9nfPiPow 3) (q3kMul (q9nfPiPow 1) c) := by
    have h43 : q9nfPiPow 4 = q3kMul (q9nfPiPow 3) (q9nfPiPow 1) := q9nf_pipow_add 3 1
    rw [← q9nf_zeta_sub_one_split, ← q9nf_embed_zeta_sub, hc, h43, q3k_kM_eq]
    exact q3kRing.mul_assoc (q9nfPiPow 3) (q9nfPiPow 1) c
  rw [q9nf_pipow3_eq] at hL
  have hcan : q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne))
      = q3kMul (q9nfPiPow 1) c := q9wr_pi3_cancel hL
  have hunit : q3kUnitMem (q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne))) :=
    q3k_unit_mul (q3k_unit_inv q9psW q9ps_w_unit)
      (q9wr_embed_unit (q3rqAdd q3rqZeta q3rqOne) q9wr_zeta_add_one_unit)
  have h3 : IsZpUnit 3 (q3rqNorm (q3kNormBase (q3kMul q9psPi9 c))) := by
    have hp : q3kMul q9psPi9 c
        = q3kMul q9psWinv (q3kEmbed (q3rqAdd q3rqZeta q3rqOne)) := by
      rw [hcan, q9nf_pipow1_eq]
    rw [hp]
    exact hunit
  rw [q3k_normBase_mul q9psPi9 c, q9wr_normBase_pi9, q3rq_norm_mul,
      q9wr_qnorm_zeta_sub] at h3
  exact q9wr_three_mul_not_unit (q3rqNorm (q3kNormBase c)) h3

/-! ## q9nf-7: 再標的の witness——1+3 ∈ U^(6)∖U^(7)

  再標的化後の B2 crux 候補は「4 = 1+3 ∉ N(M^×)」（古典側: Artin(4)|_M: ζ₉↦ζ₉⁴ ≠ 1、
  N_{L₂/ℚ₃}(4)=16 ≡ 7 mod 9）。その graded 前提——1+3 が余核の住む level 6
  （上付き break t=2 ⇔ π₉⁶）に正確に座ること——をここで実証する。
  非ノルム性そのもの（level 6 での graded 余核の同定）は後続 B2 本体。 -/

/-- **再標的 witness の下界**: 1 + 3 ∈ U^(6)（(1+3)−1 = 3 = π₉⁶·u₆）。 -/
theorem q9nf_retarget_witness : q9nfUfilt 6 (q3kAdd q3kOne (q3kEmbed q3rqThreeElt)) := by
  show q9wrDvd (q9nfPiPow 6)
    (q3kAdd (q3kAdd q3kOne (q3kEmbed q3rqThreeElt)) (q3kNeg q3kOne))
  rw [q9nf_one_add_cancel, ← q9ps_three_split]
  refine ⟨q9psU6, ?_⟩
  rw [q9nf_pipow6_eq]

/-- **★ 再標的 witness の上界**: 1 + 3 ∉ U^(7)（3 の正確な graded 位置は 6——
    π₉⁶ 相殺 2 段 → u₆ 単数 vs π₉·c → 3·s 非単数の矛盾）。 -/
theorem q9nf_retarget_sharp : ¬ q9nfUfilt 7 (q3kAdd q3kOne (q3kEmbed q3rqThreeElt)) := by
  intro h
  obtain ⟨c, hc⟩ := h
  rw [q9nf_one_add_cancel] at hc
  have hemb : q3kMul (q9nfPiPow 6) q9psU6 = q3kEmbed q3rqThreeElt := by
    rw [q9nf_pipow6_eq]
    exact q9ps_three_split
  have hL : q3kMul (q9nfPiPow 6) q9psU6
      = q3kMul (q9nfPiPow 6) (q3kMul (q9nfPiPow 1) c) := by
    have h76 : q9nfPiPow 7 = q3kMul (q9nfPiPow 6) (q9nfPiPow 1) := q9nf_pipow_add 6 1
    rw [hemb, hc, h76, q3k_kM_eq]
    exact q3kRing.mul_assoc (q9nfPiPow 6) (q9nfPiPow 1) c
  have h66 : q9nfPiPow 6 = q3kMul q9psPi9Cubed q9psPi9Cubed := q9nf_pipow6_eq
  rw [h66, q3k_kM_eq] at hL
  rw [q3kRing.mul_assoc q9psPi9Cubed q9psPi9Cubed q9psU6,
      q3kRing.mul_assoc q9psPi9Cubed q9psPi9Cubed
        (q3kRing.mul (q9nfPiPow 1) c)] at hL
  have hcan1 := q9wr_pi3_cancel hL
  have hcan2 := q9wr_pi3_cancel hcan1
  have hcan2' : q9psU6 = q3kMul q9psPi9 c := by
    rw [hcan2, q9nf_pipow1_eq, q3k_kM_eq]
  have h3 : IsZpUnit 3 (q3rqNorm (q3kNormBase (q3kMul q9psPi9 c))) := by
    rw [← hcan2']
    exact q9ps_u6_unit
  rw [q3k_normBase_mul q9psPi9 c, q9wr_normBase_pi9, q3rq_norm_mul,
      q9wr_qnorm_zeta_sub] at h3
  exact q9wr_three_mul_not_unit (q3rqNorm (q3kNormBase c)) h3

end IUT
