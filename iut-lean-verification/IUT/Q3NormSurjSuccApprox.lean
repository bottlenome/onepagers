/-
  IUT/Q3NormSurjSuccApprox.lean — 柱B・B2 T3-M2: **逐次近似の有限深度降下**
    （per-level peel を level を跨いで合成する塔をデータとして建て、π₉↔λ 降下ブリッジ・
    塔コヒーレンス・基底近似を本物で建設する。T3-M2 core の実 Lean 化・第 1 段）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（T3-core 上界機構の逐次近似塔の実現）。
  audit/pillar-B2-T3-M2-M3-completeness-detail-2026-07-11.md §3（M2a/M2b/M2c/M2d）の
  設計を実 q3k/q3rq/q9nf/q9ps/q9rf 資産の上に建てる。toy 主語なし——主語は実 O_M = q3kRing・
  実 O_{L₂} = q3rqRing・実 π₉/λ フィルトレーション・実残余体 𝔽₃・実 3 次ノルム q3kNormBase。

  complete_pct 影響: **B2 T3-M2（監査次第・予測 +0.02〜0.05）**。本ラウンドで建てるのは
  (i) **π₉↔λ 降下ブリッジ**（q9na_lam_descent: π₉^{3j}∣embed(m) ⟹ λ^j∣m・choice-free・
  §2.3/§4 M3a-3 の核心をここで先行建設）と上昇ブリッジ（q9na_lam_ascent）、
  (ii) **逐次近似塔 q9naSeq をデータ関数として**建設（§2.3 O2 の Prop→データ回避を
  全域 λ 除算 q3rqDivLam で実現）、(iii) **塔コヒーレンス M2d**（q9na_tower_dvd:
  m≥n で π₉^{3n+5}∣(x_m−x_n)・望遠鏡・witness 陽）、(iv) **基底近似**（n=0 で λ³∣(u−N(1))）。
  逐次近似の**帰納段（n→n+1 の深度前進 = 剰余相殺 q9na_approx 全体）は未完**——
  それには w 冪の剰余コヒーレンス（res_M(peel b) = (−1)^j·resL(λ 商)）= M3c 級の帳簿を
  要する（正直な限定 1）。単体の complete_pct 前進は監査次第（過大主張しない）。

  真水（本物へ昇格・新規建設）:
   * q3rqLamPow / q9na_embed_lampow_dvd / q9na_lam_ascent（★ λ^j ↑ π₉^{3j} 上昇）。
   * q9na_lam_descent（★★ π₉^{3j}∣embed(m) ⟹ λ^j∣m 降下ブリッジ）— res_M=0 ⟹ resL=0 ⟹
     λ∣ の 1 段（q9lr_resM_of_pi9_dvd + q9rf_resM_embed + q9gn_resL_lambda_dvd）を、
     embed(λ)=π₉³·w⁻¹（q9nf_embed_lambda）と π₉³ 正則消去（q9wr_pi3_cancel）と
     単数 w 消去（q9gn_unit_dvd_cancel）で k 帰納。**choice ゼロ**。§4 M3a の核心を先行建設。
   * z3DivThree / q3rqDivLam / q3rqDivLamPow（★ 全域 λ 除算・§3.1 M2a・zpDivP 写経で
     Prop→データを回避し塔を関数化）。
   * q9naSeq（★ 逐次近似塔をデータ関数として）x₀=1・x_{n+1}=x_n·(1+π₉^{3n+5}·a_n)。
   * q9na_step_diff / q9na_tower_step / q9na_tower_dvd（★ M2d コヒーレンス・望遠鏡）。
   * q9na_approx_base（★ 基底近似 n=0: λ³∣(u−N(x₀)) を U^{(9)} 仮定から降下で）。

  正直な限定（§4 規約により消さない・弱めない・q9npg/q9np/q9ns/q9nf/q9gn/q9ps/q9rf/q9lr/
  q9wr/q3k/q3rq 継承の上に追記のみ）:
  1. **逐次近似の帰納段（深度前進）は未完**。本ファイルは塔 q9naSeq を**データとして**建て、
     コヒーレンス（M2d）と基底近似（n=0）を本物で証明するが、
     「∀n, u·N(x_n)⁻¹ ∈ U^{(3(3+n))}」（q9na_approx 全体）の**帰納段 n→n+1 の剰余相殺**は
     閉じていない——peel の π₉ 側剰余 res_M(b) と残差の λ 商の剰余 resL(e) の間の
     **w 冪係数 (−1)^j の剰余コヒーレンス**（embed(λ^j)=π₉^{3j}·w⁻ʲ の剰余への降下）が
     未配線（= M3c 級の帳簿）。塔補正 a_n は q3rqDivLam 駆動で**全域に定義**されるが、
     その補正が深度を前進させる correctness は未証明。
  2. これは「任意精度でノルムに近い」の**有限深度近似の骨組み + 降下ブリッジ**であり、
     「u はノルム」（T3-core）は主張しない。U^{(3)}⊆N の全体・index≤3（M4）は未達。
  3. M3（完備性＝無限積・N の連続性・分離性・厳密等式 N(x)=u）は未着手。
  4. q9npg/q9np/q9ns/q9nf/q9gn/q9ps/q9rf/q9lr/q9wr/q3k/q3rq の正直限定を全継承
     （可除性形式・v_M 不使用・O_M と M^× のみ・体化なし・σ を超える Galois ゼロ・
     実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体・拡大 1 個 M/L₂/ℚ₃）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無・𝔽₃ 切断は q9nsCorr の
  Quot.lift ベース・λ 除算は zpDivP の ediv ベースで choice-free・omega は Int/Nat atom のみ）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3NormSurjPeelGeneral
import IUT.Q3LocalReciprocityReal

namespace IUT

/-! ## q9na-0: λ の冪 λ^j : O_{L₂}（塔の深度計量） -/

/-- **q9na-0a: λ 冪** λ⁰=1・λ^{k+1}=λ·λ^k。 -/
def q3rqLamPow : Nat → q3rqCar
  | 0 => q3rqOne
  | (k + 1) => q3rqMul q3rqLambda (q3rqLamPow k)

/-- λ^{k+1} = λ·λ^k（定義展開）。 -/
theorem q9na_lampow_succ (k : Nat) :
    q3rqLamPow (k + 1) = q3rqMul q3rqLambda (q3rqLamPow k) := rfl

/-! ## q9na-1: ★ 上昇ブリッジ λ^j ∣ m ⟹ π₉^{3j} ∣ embed(m) -/

/-- **q9na-1a: embed(λ^j) は π₉^{3j} 可除**（k 帰納・embed(λ)=π₉³·w⁻¹）。 -/
theorem q9na_embed_lampow_dvd (j : Nat) :
    q9wrDvd (q9nfPiPow (3 * j)) (q3kEmbed (q3rqLamPow j)) := by
  induction j with
  | zero =>
    refine ⟨q3kEmbed (q3rqLamPow 0), ?_⟩
    rw [q3k_kM_eq]
    exact (q3kRing.one_mul (q3kEmbed (q3rqLamPow 0))).symm
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨q3kMul q9psWinv c, ?_⟩
    have he3 : 3 * (j + 1) = 3 + 3 * j := by omega
    rw [q9na_lampow_succ, ← q3k_embed_mul q3rqLambda (q3rqLamPow j),
        q9nf_embed_lambda, hc, he3, q9nf_pipow_add 3 (3 * j), q3k_kM_eq]
    exact q3kRing.mul_mul_mul_comm (q9nfPiPow 3) q9psWinv (q9nfPiPow (3 * j)) c

/-- **q9na-1b（★ 上昇）: λ^j ∣ m ⟹ π₉^{3j} ∣ embed(m)**。 -/
theorem q9na_lam_ascent (j : Nat) (m : q3rqCar)
    (h : ∃ f : q3rqCar, m = q3rqMul (q3rqLamPow j) f) :
    q9wrDvd (q9nfPiPow (3 * j)) (q3kEmbed m) := by
  obtain ⟨f, hf⟩ := h
  rw [hf, ← q3k_embed_mul (q3rqLamPow j) f]
  exact q9nf_dvd_mul_right (q9na_embed_lampow_dvd j) (q3kEmbed f)

/-! ## q9na-2: ★★ 降下ブリッジ π₉^{3j} ∣ embed(m) ⟹ λ^j ∣ m -/

/-- **q9na-2a（★★ 降下・§4 M3a 核心の先行建設）: π₉^{3j} ∣ embed(m) ⟹ λ^j ∣ m**。
    1 段: π₉∣embed(m) ⟹ res_M(embed m)=0 ⟹ resL(m)=0 ⟹ λ∣m（既存 3 本の合成）。
    段: embed(λ·m₁)=π₉³·(w⁻¹·embed m₁) を π₉³ 正則消去 + 単数 w 消去で embed(m₁) の
    π₉^{3j} 可除に落とし ih を回す。**choice ゼロ**（新規公理・可算選択なし）。 -/
theorem q9na_lam_descent (j : Nat) : ∀ (m : q3rqCar),
    q9wrDvd (q9nfPiPow (3 * j)) (q3kEmbed m) →
    ∃ f : q3rqCar, m = q3rqMul (q3rqLamPow j) f := by
  induction j with
  | zero =>
    intro m _
    exact ⟨m, (q3rqRing.one_mul m).symm⟩
  | succ j ih =>
    intro m hm
    -- 1 段の λ 可除性: res_M=0 ⟹ resL=0 ⟹ λ∣m
    have hpi1 : q9wrDvd q9psPi9 (q3kEmbed m) := by
      rw [← q9nf_pipow1_eq]
      exact q9nf_dvd_of_le (show 1 ≤ 3 * (j + 1) by omega) hm
    have hresM : q9rfResM (q3kEmbed m) = q9rfF3.zero := q9lr_resM_of_pi9_dvd hpi1
    have hresL : q9rfResL m = q9rfF3.zero := by
      rw [← q9rf_resM_embed]; exact hresM
    obtain ⟨m1, hm1⟩ := q9gn_resL_lambda_dvd m hresL
    -- embed(m) = π₉³·(w⁻¹·embed m₁)
    have hem : q3kEmbed m
        = q3kMul (q9nfPiPow 3) (q3kMul q9psWinv (q3kEmbed m1)) := by
      rw [hm1, ← q3k_embed_mul q3rqLambda m1, q9nf_embed_lambda, q3k_kM_eq,
          q3kRing.mul_assoc (q9nfPiPow 3) q9psWinv (q3kEmbed m1)]
    -- embed(m) = π₉³·(π₉^{3j}·c)
    obtain ⟨c, hc⟩ := hm
    have he3 : 3 * (j + 1) = 3 + 3 * j := by omega
    have hc2 : q3kEmbed m
        = q3kMul (q9nfPiPow 3) (q3kMul (q9nfPiPow (3 * j)) c) := by
      rw [hc, he3, q9nf_pipow_add 3 (3 * j), q3k_kM_eq,
          q3kRing.mul_assoc (q9nfPiPow 3) (q9nfPiPow (3 * j)) c]
    -- π₉³ 正則消去
    have hpi3form : q9nfPiPow 3 = q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9 :=
      q9nf_pipow3_eq
    have heq : q3kMul (q9nfPiPow 3) (q3kMul q9psWinv (q3kEmbed m1))
        = q3kMul (q9nfPiPow 3) (q3kMul (q9nfPiPow (3 * j)) c) := hem.symm.trans hc2
    rw [hpi3form] at heq
    have hcancel : q3kMul q9psWinv (q3kEmbed m1) = q3kMul (q9nfPiPow (3 * j)) c :=
      q9wr_pi3_cancel heq
    -- 単数 w 消去
    have hwu : q3kMul q9psW q9psWinv = q3kOne := by
      rw [q3k_kM_eq, q3kRing.mul_comm q9psW q9psWinv, q9np_winv_w, q9ps_kO_eq]
    have hm1dvd : q9wrDvd (q9nfPiPow (3 * j)) (q3kEmbed m1) :=
      q9gn_unit_dvd_cancel hwu ⟨c, hcancel⟩
    obtain ⟨f, hf⟩ := ih m1 hm1dvd
    refine ⟨f, ?_⟩
    rw [hm1, hf, q9na_lampow_succ, q3k_M_eq,
        q3rqRing.mul_assoc q3rqLambda (q3rqLamPow j) f]

/-! ## q9na-3: 全域 λ 除算（§3.1 M2a・Prop→データ回避の担い手） -/

/-- **q9na-3a: ℤ₃ の全域 3 除算**（zpDivP の ediv・choice-free・全域）。 -/
def z3DivThree (x : z3.carrier) : z3.carrier := zpDivP 3 (by omega) x

/-- **q9na-3b: 全域 λ 除算** (a,b) ↦ (b, −a/3)。res_L=0 のとき真の除算
    （λ·(divLam m)=m）となるが、全域関数として塔の再帰に供給する。 -/
def q3rqDivLam (m : q3rqCar) : q3rqCar :=
  ((m.2, z3.neg (z3DivThree m.1)) : q3rqCar)

/-- **q9na-3c: λ^k 除算**（divLam の k 回反復・全域）。 -/
def q3rqDivLamPow : Nat → q3rqCar → q3rqCar
  | 0, m => m
  | (k + 1), m => q3rqDivLamPow k (q3rqDivLam m)

/-! ## q9na-4: ★ 逐次近似塔 q9naSeq をデータ関数として建設 -/

/-- **q9na-4a: 補正剰余**（残差 u−N(x) の λ^{3+n} 商の 𝔽₃ 剰余・全域）。 -/
def q9naResidueF3 (u : q3rqCar) (x : q3kCar) (n : Nat) : q9rfF3.carrier :=
  q9rfResL (q3rqDivLamPow (3 + n) (q3rqAdd u (q3rqNeg (q3kNormBase x))))

/-- **q9na-4b: 補正元**（choice-free 𝔽₃ 切断 q9nsCorr で剰余をデータ化）。 -/
def q9naCorr (u : q3rqCar) (x : q3kCar) (n : Nat) : q3kCar :=
  q9nsCorr (q9naResidueF3 u x n)

/-- **q9na-4c: peel 因子** v = 1 + π₉^{3n+5}·a（level 3(3+n)−4 = 3n+5 の単一 peel）。 -/
def q9naV (u : q3rqCar) (x : q3kCar) (n : Nat) : q3kCar :=
  q3kAdd q3kOne (q3kMul (q9nfPiPow (3 * n + 5)) (q9naCorr u x n))

/-- **q9na-4d（★ 塔をデータ関数として）: 逐次近似塔** x₀=1・x_{n+1}=x_n·v_n。
    §2.3 O2（Prop→データ）を全域 λ 除算 q3rqDivLam 駆動の補正で回避し、
    塔を n ↦ x_n の**関数（データ）**として建てる（choice-free）。 -/
def q9naSeq (u : q3rqCar) : Nat → q3kCar
  | 0 => q3kOne
  | (n + 1) => q3kMul (q9naSeq u n) (q9naV u (q9naSeq u n) n)

/-- 塔の 1 段展開（定義）。 -/
theorem q9na_seq_succ (u : q3rqCar) (n : Nat) :
    q9naSeq u (n + 1) = q3kMul (q9naSeq u n) (q9naV u (q9naSeq u n) n) := rfl

/-! ## q9na-5: ★ 塔コヒーレンス M2d（望遠鏡・witness 陽） -/

/-- **q9na-5a: 1 段差の閉形式** x·(1+p·a) − x = p·(x·a)（純環恒等式）。 -/
theorem q9na_step_diff (x p a : q3kCar) :
    q3kAdd (q3kMul x (q3kAdd q3kOne (q3kMul p a))) (q3kNeg x)
      = q3kMul p (q3kMul x a) := by
  rw [q3k_kM_eq, q9nf_kA_eq, q9ps_kN_eq, q9ps_kO_eq,
      q3kRing.left_distrib x q3kRing.one (q3kRing.mul p a),
      q3kRing.mul_one x,
      q3kRing.add_assoc x (q3kRing.mul x (q3kRing.mul p a)) (q3kRing.neg x),
      q3kRing.add_comm (q3kRing.mul x (q3kRing.mul p a)) (q3kRing.neg x),
      ← q3kRing.add_assoc x (q3kRing.neg x) (q3kRing.mul x (q3kRing.mul p a)),
      q3kRing.add_neg x, q3kRing.zero_add (q3kRing.mul x (q3kRing.mul p a)),
      q3kRing.mul_left_comm x p a]

/-- **q9na-5b: 3 項望遠鏡** (A−B)+(B−C) = A−C（純環）。 -/
theorem q9na_sub3 (A B C : q3kCar) :
    q3kAdd (q3kAdd A (q3kNeg B)) (q3kAdd B (q3kNeg C)) = q3kAdd A (q3kNeg C) := by
  rw [q9nf_kA_eq, q9ps_kN_eq,
      ← q3kRing.add_assoc (q3kRing.add A (q3kRing.neg B)) B (q3kRing.neg C),
      q3kRing.add_assoc A (q3kRing.neg B) B,
      q3kRing.neg_add B, q3kRing.add_zero A]

/-- **q9na-5c（★ 塔 1 段コヒーレンス）: π₉^{3n+5} ∣ (x_{n+1} − x_n)**。
    x_{n+1}−x_n = x_n·(v_n−1) = π₉^{3n+5}·(x_n·a_n)（q9na_step_diff・witness 陽）。 -/
theorem q9na_tower_step (u : q3rqCar) (n : Nat) :
    q9wrDvd (q9nfPiPow (3 * n + 5))
      (q3kAdd (q9naSeq u (n + 1)) (q3kNeg (q9naSeq u n))) := by
  refine ⟨q3kMul (q9naSeq u n) (q9naCorr u (q9naSeq u n) n), ?_⟩
  show q3kAdd (q3kMul (q9naSeq u n) (q9naV u (q9naSeq u n) n)) (q3kNeg (q9naSeq u n))
      = q3kMul (q9nfPiPow (3 * n + 5))
          (q3kMul (q9naSeq u n) (q9naCorr u (q9naSeq u n) n))
  exact q9na_step_diff (q9naSeq u n) (q9nfPiPow (3 * n + 5))
    (q9naCorr u (q9naSeq u n) n)

/-- **q9na-5d（★★ 塔コヒーレンス M2d）: ∀ n k, π₉^{3n+5} ∣ (x_{n+k} − x_n)**。
    望遠鏡 (x_{n+k+1}−x_n) = (x_{n+k+1}−x_{n+k})+(x_{n+k}−x_n)・各段 q9na_tower_step。
    M3 の modulus-Cauchy（M(t)=2t）への引き渡しデータ（3(n)+5 ≥ level で単調）。 -/
theorem q9na_tower_dvd (u : q3rqCar) (n k : Nat) :
    q9wrDvd (q9nfPiPow (3 * n + 5))
      (q3kAdd (q9naSeq u (n + k)) (q3kNeg (q9naSeq u n))) := by
  induction k with
  | zero =>
    show q9wrDvd (q9nfPiPow (3 * n + 5))
      (q3kAdd (q9naSeq u n) (q3kNeg (q9naSeq u n)))
    rw [q9nf_kA_eq, q9ps_kN_eq, q3kRing.add_neg (q9naSeq u n)]
    exact q9nf_dvd_zero (q9nfPiPow (3 * n + 5))
  | succ k ih =>
    have hstep : q9wrDvd (q9nfPiPow (3 * n + 5))
        (q3kAdd (q9naSeq u (n + k + 1)) (q3kNeg (q9naSeq u (n + k)))) :=
      q9nf_dvd_of_le (show 3 * n + 5 ≤ 3 * (n + k) + 5 by omega)
        (q9na_tower_step u (n + k))
    have hsum := q9nf_dvd_add hstep ih
    have hcollapse : q3kAdd (q3kAdd (q9naSeq u (n + k + 1)) (q3kNeg (q9naSeq u (n + k))))
          (q3kAdd (q9naSeq u (n + k)) (q3kNeg (q9naSeq u n)))
        = q3kAdd (q9naSeq u (n + k + 1)) (q3kNeg (q9naSeq u n)) :=
      q9na_sub3 (q9naSeq u (n + k + 1)) (q9naSeq u (n + k)) (q9naSeq u n)
    show q9wrDvd (q9nfPiPow (3 * n + 5))
      (q3kAdd (q9naSeq u (n + k + 1)) (q3kNeg (q9naSeq u n)))
    rw [← hcollapse]
    exact hsum

/-! ## q9na-6: ★ 基底近似 n=0（U^{(9)} 仮定 ⟹ λ³ ∣ (u−N(x₀))） -/

/-- **q9na-6a（★ 基底近似）: u ∈ U^{(9)} ⟹ λ³ ∣ (u − N(x₀))**（x₀=1・N(1)=1・
    残差 u−1 が π₉^{3·3}∣embed から降下ブリッジで λ³ 可除）。逐次近似の初期段。 -/
theorem q9na_approx_base (u : q3rqCar) (hu : q9nfUfilt 9 (q3kEmbed u)) :
    ∃ f : q3rqCar,
      q3rqAdd u (q3rqNeg (q3kNormBase (q9naSeq u 0))) = q3rqMul (q3rqLamPow 3) f := by
  rw [show q9naSeq u 0 = q3kOne from rfl, q3k_normBase_one]
  have hemb : q9wrDvd (q9nfPiPow 9) (q3kEmbed (q3rqAdd u (q3rqNeg q3rqOne))) := by
    rw [q9rf_embed_add, ← q9ps_n1_embed]
    exact hu
  exact q9na_lam_descent 3 (q3rqAdd u (q3rqNeg q3rqOne)) hemb

/-! ## q9na-7: capstone -/

/-- **q9na-7a: T3-M2 逐次近似データ**（塔 + 両ブリッジ + コヒーレンス + 基底近似）。 -/
structure Q3NormSurjSuccApproxData where
  /-- 上昇ブリッジ λ^j ∣ m ⟹ π₉^{3j} ∣ embed(m)。 -/
  lam_ascent : ∀ (j : Nat) (m : q3rqCar),
    (∃ f : q3rqCar, m = q3rqMul (q3rqLamPow j) f) →
    q9wrDvd (q9nfPiPow (3 * j)) (q3kEmbed m)
  /-- 降下ブリッジ π₉^{3j} ∣ embed(m) ⟹ λ^j ∣ m。 -/
  lam_descent : ∀ (j : Nat) (m : q3rqCar),
    q9wrDvd (q9nfPiPow (3 * j)) (q3kEmbed m) →
    ∃ f : q3rqCar, m = q3rqMul (q3rqLamPow j) f
  /-- 塔コヒーレンス M2d: m≥n で π₉^{3n+5} ∣ (x_m − x_n)。 -/
  tower_dvd : ∀ (u : q3rqCar) (n k : Nat),
    q9wrDvd (q9nfPiPow (3 * n + 5))
      (q3kAdd (q9naSeq u (n + k)) (q3kNeg (q9naSeq u n)))
  /-- 基底近似 n=0: u ∈ U^{(9)} ⟹ λ³ ∣ (u − N(x₀))。 -/
  approx_base : ∀ (u : q3rqCar), q9nfUfilt 9 (q3kEmbed u) →
    ∃ f : q3rqCar,
      q3rqAdd u (q3rqNeg (q3kNormBase (q9naSeq u 0))) = q3rqMul (q3rqLamPow 3) f

/-- **q9na-7b: 見出し実例** — 実 O_M/O_{L₂} 上の T3-M2 逐次近似塔。 -/
def q9na_data : Q3NormSurjSuccApproxData where
  lam_ascent := q9na_lam_ascent
  lam_descent := q9na_lam_descent
  tower_dvd := q9na_tower_dvd
  approx_base := q9na_approx_base

/-- **q9na-7c: T3-M2 逐次近似塔の存在**（塔データ + π₉↔λ 降下ブリッジの実 Lean 化）。 -/
theorem q9na_exists : Nonempty Q3NormSurjSuccApproxData := ⟨q9na_data⟩

end IUT
