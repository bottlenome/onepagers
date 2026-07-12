/-
  IUT/Q3KummerDescentSpike.lean — q9cs（level-9 μ₉ 完全性 Module B・交互パリティ同時降下の
  de-risk スパイク）

  ── 主要成果の分類: **[実／本物の先行建設(b)]（de-risk スパイク）**（骨格・模型・代理でなく、
     F-wild level-9 μ₉ 完全性（audit/mu9-completeness-level9-kill-detail-2026-07-11.md）の
     **唯一の tier-L 残リスク＝交互パリティ同時降下（§3.6）の単段（偶段・奇段）を、実 O_{L₂}
     = ℤ₃[√−3] の q3rq 座標の忠実 Int 影の上で完全証明**し、単数 peel が素冪 Euclid
     `q3cu_ppow_dvd` の消費で choice-free に閉じることを実証する。さらに両段の交互合成
     （全レベル降下 q9cs_descent_all）と、q3rqMul 座標→Int rep の一般レベル n 橋
     （val-n 補題・忠実性補題）も同時に de-risk する。）

  complete_pct 影響: **complete_pct 0 前進（de-risk foundation）**。本スパイクは Module B
  （Q3Mu9Completeness・B6 降下核）の残リスク (a)「降下の Lean encode 物量」の焼却であり、
  それ自体は実 IUT 完全証明率を動かさない。成果は「B6 の数学が Lean で 1 段（偶・奇とも）
  ＋交互合成まで閉じた」という事実そのもの。

  内容:
   * q9cs-0: Int divisibility toolbox（dvd_mull/mulr・3-shift・pow 単調・積の冪加法）
   * q9cs-1: **単数 peel**（q9cs_unit_sq / q9cs_unit_peel — ★q3cu_ppow_dvd 消費・
             降下の load-bearing step）
   * q9cs-2: 平方座標の 3-content（B₁,B₂,C₁,C₂ が不変量の下で 3^{m+1} を持つ・偶奇両版）
   * q9cs-3: E1′/E2′ の q3rq 座標多項式（q9csMulFst/Snd の入れ子＝q3rqMul の忠実 Int 影）
   * q9cs-4: **q9cs_descent_even（★）** — 偶段 k=2m→2m+1（m≥1）: 不変量＋E1′/E2′ 第 1
             座標の mod 3^{m+1} 合同から 3^{m+1}∣b₁ ∧ 3^{m+1}∣c₁
   * q9cs-5: **q9cs_descent_odd（★）** — 奇段 k=2m+1→2m+2: 3^{m+1}∣b₂ ∧ 3^{m+1}∣c₂
             （主要項は E1′/E2′ 第 2 座標の (a₁²−3a₂²)·b₂ / ·c₂）
   * q9cs-6: **q9cs_descent_all（★★）** — 交互合成: 全レベル合同＋基底 3∣b₁,c₁ から
             ∀m, 3^m が b₁,b₂,c₁,c₂ を割る（Module B6 の帰納 glue の実証）
   * q9cs-7: 一般レベル n の val 計算補題（add/neg/mul・q3mc val-1 補題の n 版）と
             q3rqMul 座標の忠実性（q9cs_rq_mul_fst_valn/_snd_valn・rep→q9csMulFst/Snd）・
             z3 零元の rep 可除性（q9cs_zero_rep_dvd — E′=0 を rep 合同に読む橋）

  正直な限定（§4 規約・消さない・弱めない）:
  1. **スパイク＝単段＋合成のみ・Module B 本体ではない**。E1′/E2′ の合同仮定
     （q9cs_descent_all の hE 群）は仮定として取る——本物では x³=1 の Y/Y² 成分方程式
     （O_M の等式）から出る。その導出（立方展開 E0/E1/E2・3 正則での 3 消去）は Module A
     （q9ci）の仕事であり本ファイルは含まない。
  2. **q3rq 座標→Int rep の橋は単一積まで**。q9cs_rq_mul_fst/snd_valn は q3rqMul 1 回分の
     忠実性のみ実証。E1′ 全体（3 積の和）の rep 読みは同補題の反復（機械的・Module B の
     物量部分）で、本スパイクでは実施しない。
  3. **偶段は m≥1 のみ**（hm : 1 ≤ m）。基底 k=1（3∣b₁,c₁）・k=2 は §3.4–3.5 の
     単数枝反証・生存枝初期化の出口であり、本スパイクの範囲外（q9cs_descent_all は
     基底を仮定に取り、k=1→2 は奇段 m=0 で内部処理する——奇段は m=0 から有効）。
  4. **主語は O_{L₂} の 4 座標 Int 簿記**（b₁,b₂,c₁,c₂ と単数 a・ζ₃ の rep d₁,d₂）。
     O_M（q3k）の元・乗法は登場しない（E′ 係数 d=ζ₃ は任意 Int 対として抽象化——
     非主要単項式の 3-content は d の値に依存しないため忠実）。
  5. 交互不変量の号数対応: 偶段補題の結論は「k=2m 不変量 ⟹ k=2m+1 不変量の新規部分」、
     奇段は「k=2m+1 ⟹ k=2m+2 の新規部分」。設計文書 §3.6 の Qₖ と同一。

  全て選択公理不使用（新規 Classical.choice なし・sorry 皆無・禁止タクティク不使用。
  omega は純 Int/Nat 線形ゴールのみ）。#print axioms は [propext, Quot.sound] のみ。
-/
import IUT.Q3RamifiedQuadratic
import IUT.Q3TateCuspidalization
import IUT.Q3Mu3Completeness

namespace IUT

/-! ## q9cs-0: Int divisibility toolbox（witness 明示・choice-free） -/

/-- n ∣ x ⟹ n ∣ y·x（左から掛ける）。 -/
theorem q9cs_dvd_mull (y : Int) {n x : Int} (hx : n ∣ x) : n ∣ y * x := by
  obtain ⟨u, hu⟩ := hx
  exact ⟨y * u, by rw [hu, Int.mul_left_comm]⟩

/-- n ∣ x ⟹ n ∣ x·y（右から掛ける）。 -/
theorem q9cs_dvd_mulr {n x : Int} (hx : n ∣ x) (y : Int) : n ∣ x * y := by
  obtain ⟨u, hu⟩ := hx
  exact ⟨u * y, by rw [hu, Int.mul_assoc]⟩

/-- 3^{t+1} = 3·3^t（Int キャスト・q3mc:178 の写経）。 -/
theorem q9cs_pow_succ (t : Nat) :
    ((3 ^ (t + 1) : Nat) : Int) = ((3 : Nat) : Int) * ((3 ^ t : Nat) : Int) := by
  rw [Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]

/-- **3-shift**: 3^t ∣ x ⟹ 3^{t+1} ∣ 3·x（明示因子 3 が 1 段深くする）。 -/
theorem q9cs_dvd_three_shift {t : Nat} {x : Int}
    (hx : ((3 ^ t : Nat) : Int) ∣ x) : ((3 ^ (t + 1) : Nat) : Int) ∣ 3 * x := by
  obtain ⟨u, hu⟩ := hx
  refine ⟨u, ?_⟩
  rw [hu, q9cs_pow_succ t, Int.mul_assoc]
  exact rfl

/-- 冪の単調性: s ≤ t ⟹ 3^s ∣ 3^t（Int キャスト）。 -/
theorem q9cs_pow_le_dvd {s t : Nat} (h : s ≤ t) :
    ((3 ^ s : Nat) : Int) ∣ ((3 ^ t : Nat) : Int) :=
  Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 3 h)

/-- 深い冪の可除性は浅い冪へ落ちる: s ≤ t, 3^t ∣ x ⟹ 3^s ∣ x。 -/
theorem q9cs_dvd_of_le {s t : Nat} (h : s ≤ t) {x : Int}
    (hx : ((3 ^ t : Nat) : Int) ∣ x) : ((3 ^ s : Nat) : Int) ∣ x :=
  Int.dvd_trans (q9cs_pow_le_dvd h) hx

/-- 積は冪を加算する: 3^s ∣ x, 3^t ∣ y ⟹ 3^{s+t} ∣ x·y。 -/
theorem q9cs_dvd_mul_pow {s t : Nat} {x y : Int}
    (hx : ((3 ^ s : Nat) : Int) ∣ x) (hy : ((3 ^ t : Nat) : Int) ∣ y) :
    ((3 ^ (s + t) : Nat) : Int) ∣ x * y := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  refine ⟨u * v, ?_⟩
  rw [hu, hv, Nat.pow_add, Int.natCast_mul]
  calc (((3 ^ s : Nat) : Int) * u) * (((3 ^ t : Nat) : Int) * v)
      = ((3 ^ s : Nat) : Int) * (u * (((3 ^ t : Nat) : Int) * v)) :=
        Int.mul_assoc _ _ _
    _ = ((3 ^ s : Nat) : Int) * (((3 ^ t : Nat) : Int) * (u * v)) := by
        rw [Int.mul_left_comm u _ v]
    _ = (((3 ^ s : Nat) : Int) * ((3 ^ t : Nat) : Int)) * (u * v) :=
        (Int.mul_assoc _ _ _).symm

/-- 3^0 = 1 は全てを割る（降下の基底 m=0 用）。 -/
theorem q9cs_pow_zero_dvd (x : Int) : ((3 ^ 0 : Nat) : Int) ∣ x :=
  ⟨x, by rw [Nat.pow_zero]; omega⟩

/-! ## q9cs-1: 単数 peel（★ 素冪 Euclid q3cu_ppow_dvd の消費・load-bearing step） -/

/-- **a 単数 ⟹ ノルム型主要係数 a₁²−3a₂² は 3 と素**（3∤a₁ から euclid_int で）。
    §3.6 の「3∤a₁ ⟹ 3∤(a₁²−3a₂²)」の実体。 -/
theorem q9cs_unit_sq {a1 a2 : Int} (ha : ¬ ((3 : Nat) : Int) ∣ a1) :
    ¬ ((3 : Nat) : Int) ∣ (a1 * a1 - 3 * (a2 * a2)) := by
  intro h
  obtain ⟨k, hk⟩ := h
  have h3aa : ((3 : Nat) : Int) ∣ a1 * a1 := ⟨k + a2 * a2, by omega⟩
  exact ha (euclid_int 3 isPrime_three h3aa ha)

/-- **単数 peel（★）**: 3^t ∣ (a₁²−3a₂²)·x, 3∤a₁ ⟹ 3^t ∣ x。
    素冪 Euclid `q3cu_ppow_dvd`（実在・q3mc が消費したもの）の直接消費——
    交互パリティ降下の各段で主要項から単数因子を剥がす唯一の非自明ステップ。 -/
theorem q9cs_unit_peel (t : Nat) {a1 a2 x : Int}
    (ha : ¬ ((3 : Nat) : Int) ∣ a1)
    (h : ((3 ^ t : Nat) : Int) ∣ (a1 * a1 - 3 * (a2 * a2)) * x) :
    ((3 ^ t : Nat) : Int) ∣ x := by
  rw [Int.mul_comm (a1 * a1 - 3 * (a2 * a2)) x] at h
  exact q3cu_ppow_dvd t h (q9cs_unit_sq ha)

/-! ## q9cs-2: 平方座標の 3-content（不変量の下で B₁,B₂,C₁,C₂ ∈ 3^{m+1}ℤ） -/

/-- 偶段用（k=2m 不変量・m≥1）: 3^m ∣ x₁,x₂ ⟹ 3^{m+1} ∣ x₁²−3x₂²
    （x₁² は 3^{2m}・3x₂² は 3^{2m+1}・2m ≥ m+1）。 -/
theorem q9cs_sq_fst_even (m : Nat) (hm : 1 ≤ m) {x1 x2 : Int}
    (h1 : ((3 ^ m : Nat) : Int) ∣ x1) (h2 : ((3 ^ m : Nat) : Int) ∣ x2) :
    ((3 ^ (m + 1) : Nat) : Int) ∣ (x1 * x1 - 3 * (x2 * x2)) :=
  Int.dvd_sub
    (q9cs_dvd_of_le (show m + 1 ≤ m + m by omega) (q9cs_dvd_mul_pow h1 h1))
    (q9cs_dvd_three_shift (q9cs_dvd_mulr h2 x2))

/-- 偶段用: 3^m ∣ x₁,x₂ ⟹ 3^{m+1} ∣ x₁x₂+x₂x₁（各項 3^{2m}・m≥1）。 -/
theorem q9cs_sq_snd_even (m : Nat) (hm : 1 ≤ m) {x1 x2 : Int}
    (h1 : ((3 ^ m : Nat) : Int) ∣ x1) (h2 : ((3 ^ m : Nat) : Int) ∣ x2) :
    ((3 ^ (m + 1) : Nat) : Int) ∣ (x1 * x2 + x2 * x1) :=
  Int.dvd_add
    (q9cs_dvd_of_le (show m + 1 ≤ m + m by omega) (q9cs_dvd_mul_pow h1 h2))
    (q9cs_dvd_of_le (show m + 1 ≤ m + m by omega) (q9cs_dvd_mul_pow h2 h1))

/-- 奇段用（k=2m+1 不変量）: 3^{m+1} ∣ x₁, 3^m ∣ x₂ ⟹ 3^{m+1} ∣ x₁²−3x₂²
    （x₁² は x₁ 因子 1 本で足りる・3x₂² は 3-shift）。全 m ≥ 0 で有効。 -/
theorem q9cs_sq_fst_odd (m : Nat) {x1 x2 : Int}
    (h1 : ((3 ^ (m + 1) : Nat) : Int) ∣ x1) (h2 : ((3 ^ m : Nat) : Int) ∣ x2) :
    ((3 ^ (m + 1) : Nat) : Int) ∣ (x1 * x1 - 3 * (x2 * x2)) :=
  Int.dvd_sub (q9cs_dvd_mulr h1 x1) (q9cs_dvd_three_shift (q9cs_dvd_mulr h2 x2))

/-- 奇段用: 3^{m+1} ∣ x₁ ⟹ 3^{m+1} ∣ x₁x₂+x₂x₁（x₁ 因子 1 本）。 -/
theorem q9cs_sq_snd_odd (m : Nat) {x1 : Int} (x2 : Int)
    (h1 : ((3 ^ (m + 1) : Nat) : Int) ∣ x1) :
    ((3 ^ (m + 1) : Nat) : Int) ∣ (x1 * x2 + x2 * x1) :=
  Int.dvd_add (q9cs_dvd_mulr h1 x2) (q9cs_dvd_mull x2 h1)

/-! ## q9cs-3: E1′/E2′ の q3rq 座標多項式（q3rqMul の忠実 Int 影）

E1′ = a²·b + d·(a·c²) + d·(b²·c)、E2′ = a²·c + a·b² + d·(b·c²)（d = ζ₃）。
q3rqMul (x,y) = (x₁y₁ + D·x₂y₂, x₁y₂ + x₂y₁)・D = −3 なので座標影は
MulFst = x₁y₁ − 3(x₂y₂)、MulSnd = x₁y₂ + x₂y₁（値として同一・q9cs-7 で忠実性を実証）。 -/

/-- q3rqMul の第 1 座標の Int 影（D=−3）: (x·y)₁ = x₁y₁ − 3·x₂y₂。 -/
def q9csMulFst (x1 x2 y1 y2 : Int) : Int := x1 * y1 - 3 * (x2 * y2)

/-- q3rqMul の第 2 座標の Int 影: (x·y)₂ = x₁y₂ + x₂y₁。 -/
def q9csMulSnd (x1 x2 y1 y2 : Int) : Int := x1 * y2 + x2 * y1

/-- E1′ = a²·b + d·(a·c²) + d·(b²·c) の第 1 座標（q3rqMul の入れ子そのまま）。 -/
def q9csE1fst (a1 a2 b1 b2 c1 c2 d1 d2 : Int) : Int :=
  q9csMulFst (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) b1 b2
    + q9csMulFst d1 d2
        (q9csMulFst a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
        (q9csMulSnd a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
    + q9csMulFst d1 d2
        (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)
        (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)

/-- E1′ の第 2 座標。 -/
def q9csE1snd (a1 a2 b1 b2 c1 c2 d1 d2 : Int) : Int :=
  q9csMulSnd (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) b1 b2
    + q9csMulSnd d1 d2
        (q9csMulFst a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
        (q9csMulSnd a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
    + q9csMulSnd d1 d2
        (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)
        (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)

/-- E2′ = a²·c + a·b² + d·(b·c²) の第 1 座標。 -/
def q9csE2fst (a1 a2 b1 b2 c1 c2 d1 d2 : Int) : Int :=
  q9csMulFst (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) c1 c2
    + q9csMulFst a1 a2 (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2)
    + q9csMulFst d1 d2
        (q9csMulFst b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
        (q9csMulSnd b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))

/-- E2′ の第 2 座標。 -/
def q9csE2snd (a1 a2 b1 b2 c1 c2 d1 d2 : Int) : Int :=
  q9csMulSnd (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) c1 c2
    + q9csMulSnd a1 a2 (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2)
    + q9csMulSnd d1 d2
        (q9csMulFst b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
        (q9csMulSnd b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))

/-! ## q9cs-4: 偶段（★ k=2m → 2m+1・m≥1）

不変量 3^m ∣ b₁,b₂,c₁,c₂ と 3∤a₁、E1′/E2′ 第 1 座標の mod 3^{m+1} 合同から
3^{m+1} ∣ b₁ ∧ 3^{m+1} ∣ c₁。主要項 (a₁²−3a₂²)·b₁ 以外の全単項式が 3^{m+1} を
持つこと（§3.6 検算）を Lean で実証し、単数 peel で締める。 -/

/-- **q9cs-4（★）: 偶段降下** — E1′ 第 1 座標で b₁ を、E2′ 第 1 座標で c₁ を 1 段深く。 -/
theorem q9cs_descent_even (m : Nat) (hm : 1 ≤ m)
    (a1 a2 b1 b2 c1 c2 d1 d2 : Int)
    (ha : ¬ ((3 : Nat) : Int) ∣ a1)
    (hb1 : ((3 ^ m : Nat) : Int) ∣ b1) (hb2 : ((3 ^ m : Nat) : Int) ∣ b2)
    (hc1 : ((3 ^ m : Nat) : Int) ∣ c1) (hc2 : ((3 ^ m : Nat) : Int) ∣ c2)
    (hE1 : ((3 ^ (m + 1) : Nat) : Int) ∣ q9csE1fst a1 a2 b1 b2 c1 c2 d1 d2)
    (hE2 : ((3 ^ (m + 1) : Nat) : Int) ∣ q9csE2fst a1 a2 b1 b2 c1 c2 d1 d2) :
    ((3 ^ (m + 1) : Nat) : Int) ∣ b1 ∧ ((3 ^ (m + 1) : Nat) : Int) ∣ c1 := by
  -- 平方座標の 3^{m+1}-content（IH から）
  have hB1 : ((3 ^ (m + 1) : Nat) : Int) ∣ (b1 * b1 - 3 * (b2 * b2)) :=
    q9cs_sq_fst_even m hm hb1 hb2
  have hB2 : ((3 ^ (m + 1) : Nat) : Int) ∣ (b1 * b2 + b2 * b1) :=
    q9cs_sq_snd_even m hm hb1 hb2
  have hC1 : ((3 ^ (m + 1) : Nat) : Int) ∣ (c1 * c1 - 3 * (c2 * c2)) :=
    q9cs_sq_fst_even m hm hc1 hc2
  have hC2 : ((3 ^ (m + 1) : Nat) : Int) ∣ (c1 * c2 + c2 * c1) :=
    q9cs_sq_snd_even m hm hc1 hc2
  constructor
  · -- E1′ 第 1 座標: 主要項 (a₁²−3a₂²)·b₁ の抽出
    have hE1' : ((3 ^ (m + 1) : Nat) : Int) ∣
        ((a1 * a1 - 3 * (a2 * a2)) * b1 - 3 * ((a1 * a2 + a2 * a1) * b2)
          + (d1 * (a1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (a2 * (c1 * c2 + c2 * c1)))
              - 3 * (d2 * (a1 * (c1 * c2 + c2 * c1) + a2 * (c1 * c1 - 3 * (c2 * c2)))))
          + (d1 * ((b1 * b1 - 3 * (b2 * b2)) * c1 - 3 * ((b1 * b2 + b2 * b1) * c2))
              - 3 * (d2 * ((b1 * b1 - 3 * (b2 * b2)) * c2 + (b1 * b2 + b2 * b1) * c1)))) :=
      hE1
    have hrest : ((3 ^ (m + 1) : Nat) : Int) ∣
        (-(3 * ((a1 * a2 + a2 * a1) * b2))
          + (d1 * (a1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (a2 * (c1 * c2 + c2 * c1)))
              - 3 * (d2 * (a1 * (c1 * c2 + c2 * c1) + a2 * (c1 * c1 - 3 * (c2 * c2)))))
          + (d1 * ((b1 * b1 - 3 * (b2 * b2)) * c1 - 3 * ((b1 * b2 + b2 * b1) * c2))
              - 3 * (d2 * ((b1 * b1 - 3 * (b2 * b2)) * c2 + (b1 * b2 + b2 * b1) * c1)))) :=
      Int.dvd_add
        (Int.dvd_add
          (Int.dvd_neg.mpr
            (q9cs_dvd_three_shift (q9cs_dvd_mull (a1 * a2 + a2 * a1) hb2)))
          (Int.dvd_sub
            (q9cs_dvd_mull d1
              (Int.dvd_sub (q9cs_dvd_mull a1 hC1)
                (q9cs_dvd_mull 3 (q9cs_dvd_mull a2 hC2))))
            (q9cs_dvd_mull 3 (q9cs_dvd_mull d2
              (Int.dvd_add (q9cs_dvd_mull a1 hC2) (q9cs_dvd_mull a2 hC1))))))
        (Int.dvd_sub
          (q9cs_dvd_mull d1
            (Int.dvd_sub (q9cs_dvd_mulr hB1 c1)
              (q9cs_dvd_mull 3 (q9cs_dvd_mulr hB2 c2))))
          (q9cs_dvd_mull 3 (q9cs_dvd_mull d2
            (Int.dvd_add (q9cs_dvd_mulr hB1 c2) (q9cs_dvd_mulr hB2 c1)))))
    have hsub := Int.dvd_sub hE1' hrest
    have heq :
        ((a1 * a1 - 3 * (a2 * a2)) * b1 - 3 * ((a1 * a2 + a2 * a1) * b2)
          + (d1 * (a1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (a2 * (c1 * c2 + c2 * c1)))
              - 3 * (d2 * (a1 * (c1 * c2 + c2 * c1) + a2 * (c1 * c1 - 3 * (c2 * c2)))))
          + (d1 * ((b1 * b1 - 3 * (b2 * b2)) * c1 - 3 * ((b1 * b2 + b2 * b1) * c2))
              - 3 * (d2 * ((b1 * b1 - 3 * (b2 * b2)) * c2 + (b1 * b2 + b2 * b1) * c1))))
        - (-(3 * ((a1 * a2 + a2 * a1) * b2))
          + (d1 * (a1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (a2 * (c1 * c2 + c2 * c1)))
              - 3 * (d2 * (a1 * (c1 * c2 + c2 * c1) + a2 * (c1 * c1 - 3 * (c2 * c2)))))
          + (d1 * ((b1 * b1 - 3 * (b2 * b2)) * c1 - 3 * ((b1 * b2 + b2 * b1) * c2))
              - 3 * (d2 * ((b1 * b1 - 3 * (b2 * b2)) * c2 + (b1 * b2 + b2 * b1) * c1))))
        = (a1 * a1 - 3 * (a2 * a2)) * b1 := by omega
    rw [heq] at hsub
    exact q9cs_unit_peel (m + 1) ha hsub
  · -- E2′ 第 1 座標: 主要項 (a₁²−3a₂²)·c₁ の抽出
    have hE2' : ((3 ^ (m + 1) : Nat) : Int) ∣
        ((a1 * a1 - 3 * (a2 * a2)) * c1 - 3 * ((a1 * a2 + a2 * a1) * c2)
          + (a1 * (b1 * b1 - 3 * (b2 * b2)) - 3 * (a2 * (b1 * b2 + b2 * b1)))
          + (d1 * (b1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (b2 * (c1 * c2 + c2 * c1)))
              - 3 * (d2 * (b1 * (c1 * c2 + c2 * c1) + b2 * (c1 * c1 - 3 * (c2 * c2)))))) :=
      hE2
    have hrest : ((3 ^ (m + 1) : Nat) : Int) ∣
        (-(3 * ((a1 * a2 + a2 * a1) * c2))
          + (a1 * (b1 * b1 - 3 * (b2 * b2)) - 3 * (a2 * (b1 * b2 + b2 * b1)))
          + (d1 * (b1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (b2 * (c1 * c2 + c2 * c1)))
              - 3 * (d2 * (b1 * (c1 * c2 + c2 * c1) + b2 * (c1 * c1 - 3 * (c2 * c2)))))) :=
      Int.dvd_add
        (Int.dvd_add
          (Int.dvd_neg.mpr
            (q9cs_dvd_three_shift (q9cs_dvd_mull (a1 * a2 + a2 * a1) hc2)))
          (Int.dvd_sub (q9cs_dvd_mull a1 hB1)
            (q9cs_dvd_mull 3 (q9cs_dvd_mull a2 hB2))))
        (Int.dvd_sub
          (q9cs_dvd_mull d1
            (Int.dvd_sub (q9cs_dvd_mull b1 hC1)
              (q9cs_dvd_mull 3 (q9cs_dvd_mull b2 hC2))))
          (q9cs_dvd_mull 3 (q9cs_dvd_mull d2
            (Int.dvd_add (q9cs_dvd_mull b1 hC2) (q9cs_dvd_mull b2 hC1)))))
    have hsub := Int.dvd_sub hE2' hrest
    have heq :
        ((a1 * a1 - 3 * (a2 * a2)) * c1 - 3 * ((a1 * a2 + a2 * a1) * c2)
          + (a1 * (b1 * b1 - 3 * (b2 * b2)) - 3 * (a2 * (b1 * b2 + b2 * b1)))
          + (d1 * (b1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (b2 * (c1 * c2 + c2 * c1)))
              - 3 * (d2 * (b1 * (c1 * c2 + c2 * c1) + b2 * (c1 * c1 - 3 * (c2 * c2))))))
        - (-(3 * ((a1 * a2 + a2 * a1) * c2))
          + (a1 * (b1 * b1 - 3 * (b2 * b2)) - 3 * (a2 * (b1 * b2 + b2 * b1)))
          + (d1 * (b1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (b2 * (c1 * c2 + c2 * c1)))
              - 3 * (d2 * (b1 * (c1 * c2 + c2 * c1) + b2 * (c1 * c1 - 3 * (c2 * c2))))))
        = (a1 * a1 - 3 * (a2 * a2)) * c1 := by omega
    rw [heq] at hsub
    exact q9cs_unit_peel (m + 1) ha hsub

/-! ## q9cs-5: 奇段（★ k=2m+1 → 2m+2・全 m≥0）

不変量 3^{m+1} ∣ b₁,c₁・3^m ∣ b₂,c₂ から E1′/E2′ 第 2 座標で 3^{m+1} ∣ b₂ ∧ c₂。
主要項は (a₁²−3a₂²)·b₂ / ·c₂（第 2 座標に移る——交互パリティの「交互」の実体）。 -/

/-- **q9cs-5（★）: 奇段降下** — E1′ 第 2 座標で b₂ を、E2′ 第 2 座標で c₂ を 1 段深く。 -/
theorem q9cs_descent_odd (m : Nat)
    (a1 a2 b1 b2 c1 c2 d1 d2 : Int)
    (ha : ¬ ((3 : Nat) : Int) ∣ a1)
    (hb1 : ((3 ^ (m + 1) : Nat) : Int) ∣ b1) (hb2 : ((3 ^ m : Nat) : Int) ∣ b2)
    (hc1 : ((3 ^ (m + 1) : Nat) : Int) ∣ c1) (hc2 : ((3 ^ m : Nat) : Int) ∣ c2)
    (hE1 : ((3 ^ (m + 1) : Nat) : Int) ∣ q9csE1snd a1 a2 b1 b2 c1 c2 d1 d2)
    (hE2 : ((3 ^ (m + 1) : Nat) : Int) ∣ q9csE2snd a1 a2 b1 b2 c1 c2 d1 d2) :
    ((3 ^ (m + 1) : Nat) : Int) ∣ b2 ∧ ((3 ^ (m + 1) : Nat) : Int) ∣ c2 := by
  have hB1 : ((3 ^ (m + 1) : Nat) : Int) ∣ (b1 * b1 - 3 * (b2 * b2)) :=
    q9cs_sq_fst_odd m hb1 hb2
  have hB2 : ((3 ^ (m + 1) : Nat) : Int) ∣ (b1 * b2 + b2 * b1) :=
    q9cs_sq_snd_odd m b2 hb1
  have hC1 : ((3 ^ (m + 1) : Nat) : Int) ∣ (c1 * c1 - 3 * (c2 * c2)) :=
    q9cs_sq_fst_odd m hc1 hc2
  have hC2 : ((3 ^ (m + 1) : Nat) : Int) ∣ (c1 * c2 + c2 * c1) :=
    q9cs_sq_snd_odd m c2 hc1
  constructor
  · -- E1′ 第 2 座標: 主要項 (a₁²−3a₂²)·b₂ の抽出
    have hE1' : ((3 ^ (m + 1) : Nat) : Int) ∣
        ((a1 * a1 - 3 * (a2 * a2)) * b2 + (a1 * a2 + a2 * a1) * b1
          + (d1 * (a1 * (c1 * c2 + c2 * c1) + a2 * (c1 * c1 - 3 * (c2 * c2)))
              + d2 * (a1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (a2 * (c1 * c2 + c2 * c1))))
          + (d1 * ((b1 * b1 - 3 * (b2 * b2)) * c2 + (b1 * b2 + b2 * b1) * c1)
              + d2 * ((b1 * b1 - 3 * (b2 * b2)) * c1 - 3 * ((b1 * b2 + b2 * b1) * c2)))) :=
      hE1
    have hrest : ((3 ^ (m + 1) : Nat) : Int) ∣
        ((a1 * a2 + a2 * a1) * b1
          + (d1 * (a1 * (c1 * c2 + c2 * c1) + a2 * (c1 * c1 - 3 * (c2 * c2)))
              + d2 * (a1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (a2 * (c1 * c2 + c2 * c1))))
          + (d1 * ((b1 * b1 - 3 * (b2 * b2)) * c2 + (b1 * b2 + b2 * b1) * c1)
              + d2 * ((b1 * b1 - 3 * (b2 * b2)) * c1 - 3 * ((b1 * b2 + b2 * b1) * c2)))) :=
      Int.dvd_add
        (Int.dvd_add
          (q9cs_dvd_mull (a1 * a2 + a2 * a1) hb1)
          (Int.dvd_add
            (q9cs_dvd_mull d1
              (Int.dvd_add (q9cs_dvd_mull a1 hC2) (q9cs_dvd_mull a2 hC1)))
            (q9cs_dvd_mull d2
              (Int.dvd_sub (q9cs_dvd_mull a1 hC1)
                (q9cs_dvd_mull 3 (q9cs_dvd_mull a2 hC2))))))
        (Int.dvd_add
          (q9cs_dvd_mull d1
            (Int.dvd_add (q9cs_dvd_mulr hB1 c2) (q9cs_dvd_mulr hB2 c1)))
          (q9cs_dvd_mull d2
            (Int.dvd_sub (q9cs_dvd_mulr hB1 c1)
              (q9cs_dvd_mull 3 (q9cs_dvd_mulr hB2 c2)))))
    have hsub := Int.dvd_sub hE1' hrest
    have heq :
        ((a1 * a1 - 3 * (a2 * a2)) * b2 + (a1 * a2 + a2 * a1) * b1
          + (d1 * (a1 * (c1 * c2 + c2 * c1) + a2 * (c1 * c1 - 3 * (c2 * c2)))
              + d2 * (a1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (a2 * (c1 * c2 + c2 * c1))))
          + (d1 * ((b1 * b1 - 3 * (b2 * b2)) * c2 + (b1 * b2 + b2 * b1) * c1)
              + d2 * ((b1 * b1 - 3 * (b2 * b2)) * c1 - 3 * ((b1 * b2 + b2 * b1) * c2))))
        - ((a1 * a2 + a2 * a1) * b1
          + (d1 * (a1 * (c1 * c2 + c2 * c1) + a2 * (c1 * c1 - 3 * (c2 * c2)))
              + d2 * (a1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (a2 * (c1 * c2 + c2 * c1))))
          + (d1 * ((b1 * b1 - 3 * (b2 * b2)) * c2 + (b1 * b2 + b2 * b1) * c1)
              + d2 * ((b1 * b1 - 3 * (b2 * b2)) * c1 - 3 * ((b1 * b2 + b2 * b1) * c2))))
        = (a1 * a1 - 3 * (a2 * a2)) * b2 := by omega
    rw [heq] at hsub
    exact q9cs_unit_peel (m + 1) ha hsub
  · -- E2′ 第 2 座標: 主要項 (a₁²−3a₂²)·c₂ の抽出
    have hE2' : ((3 ^ (m + 1) : Nat) : Int) ∣
        ((a1 * a1 - 3 * (a2 * a2)) * c2 + (a1 * a2 + a2 * a1) * c1
          + (a1 * (b1 * b2 + b2 * b1) + a2 * (b1 * b1 - 3 * (b2 * b2)))
          + (d1 * (b1 * (c1 * c2 + c2 * c1) + b2 * (c1 * c1 - 3 * (c2 * c2)))
              + d2 * (b1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (b2 * (c1 * c2 + c2 * c1))))) :=
      hE2
    have hrest : ((3 ^ (m + 1) : Nat) : Int) ∣
        ((a1 * a2 + a2 * a1) * c1
          + (a1 * (b1 * b2 + b2 * b1) + a2 * (b1 * b1 - 3 * (b2 * b2)))
          + (d1 * (b1 * (c1 * c2 + c2 * c1) + b2 * (c1 * c1 - 3 * (c2 * c2)))
              + d2 * (b1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (b2 * (c1 * c2 + c2 * c1))))) :=
      Int.dvd_add
        (Int.dvd_add
          (q9cs_dvd_mull (a1 * a2 + a2 * a1) hc1)
          (Int.dvd_add (q9cs_dvd_mull a1 hB2) (q9cs_dvd_mull a2 hB1)))
        (Int.dvd_add
          (q9cs_dvd_mull d1
            (Int.dvd_add (q9cs_dvd_mull b1 hC2) (q9cs_dvd_mull b2 hC1)))
          (q9cs_dvd_mull d2
            (Int.dvd_sub (q9cs_dvd_mull b1 hC1)
              (q9cs_dvd_mull 3 (q9cs_dvd_mull b2 hC2)))))
    have hsub := Int.dvd_sub hE2' hrest
    have heq :
        ((a1 * a1 - 3 * (a2 * a2)) * c2 + (a1 * a2 + a2 * a1) * c1
          + (a1 * (b1 * b2 + b2 * b1) + a2 * (b1 * b1 - 3 * (b2 * b2)))
          + (d1 * (b1 * (c1 * c2 + c2 * c1) + b2 * (c1 * c1 - 3 * (c2 * c2)))
              + d2 * (b1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (b2 * (c1 * c2 + c2 * c1)))))
        - ((a1 * a2 + a2 * a1) * c1
          + (a1 * (b1 * b2 + b2 * b1) + a2 * (b1 * b1 - 3 * (b2 * b2)))
          + (d1 * (b1 * (c1 * c2 + c2 * c1) + b2 * (c1 * c1 - 3 * (c2 * c2)))
              + d2 * (b1 * (c1 * c1 - 3 * (c2 * c2)) - 3 * (b2 * (c1 * c2 + c2 * c1)))))
        = (a1 * a1 - 3 * (a2 * a2)) * c2 := by omega
    rw [heq] at hsub
    exact q9cs_unit_peel (m + 1) ha hsub

/-! ## q9cs-6: 交互合成（★★ 全レベル降下 = Module B6 の帰納 glue） -/

/-- **q9cs-6（★★）: 交互パリティ同時降下・全レベル** — E1′/E2′ の両座標が全レベルで
    合同（本物では O_{L₂} の等式 E′=0 から出る）、a 単数（3∤a₁）、基底 3∣b₁, 3∣c₁
    （§3.4–3.5 の単数枝反証・生存枝初期化の出口）から、∀m で 3^m が b₁,b₂,c₁,c₂ を割る。
    帰納の各段: m=0→1 は奇段 m=0（k=1→2）、m≥1→m+1 は偶段＋奇段の合成。
    ここから b=c=0（∩ₘ3^mℤ₃=0）は z3 の射影整合＋Subtype.ext（q3mc_three_mul_zero の
    結論部イディオム）で、Module B 本体の仕事。 -/
theorem q9cs_descent_all
    (a1 a2 b1 b2 c1 c2 d1 d2 : Int)
    (ha : ¬ ((3 : Nat) : Int) ∣ a1)
    (hE1f : ∀ t : Nat, ((3 ^ t : Nat) : Int) ∣ q9csE1fst a1 a2 b1 b2 c1 c2 d1 d2)
    (hE1s : ∀ t : Nat, ((3 ^ t : Nat) : Int) ∣ q9csE1snd a1 a2 b1 b2 c1 c2 d1 d2)
    (hE2f : ∀ t : Nat, ((3 ^ t : Nat) : Int) ∣ q9csE2fst a1 a2 b1 b2 c1 c2 d1 d2)
    (hE2s : ∀ t : Nat, ((3 ^ t : Nat) : Int) ∣ q9csE2snd a1 a2 b1 b2 c1 c2 d1 d2)
    (hbase_b : ((3 : Nat) : Int) ∣ b1) (hbase_c : ((3 : Nat) : Int) ∣ c1) :
    ∀ m : Nat, ((3 ^ m : Nat) : Int) ∣ b1 ∧ ((3 ^ m : Nat) : Int) ∣ b2
      ∧ ((3 ^ m : Nat) : Int) ∣ c1 ∧ ((3 ^ m : Nat) : Int) ∣ c2 := by
  intro m
  induction m with
  | zero =>
    exact ⟨q9cs_pow_zero_dvd b1, q9cs_pow_zero_dvd b2,
      q9cs_pow_zero_dvd c1, q9cs_pow_zero_dvd c2⟩
  | succ p ih =>
    obtain ⟨ihb1, ihb2, ihc1, ihc2⟩ := ih
    cases p with
    | zero =>
      -- m: 0 → 1（k=1→2 の奇段 m=0）: b₁,c₁ は基底・b₂,c₂ は奇段
      have hb1' : ((3 ^ 1 : Nat) : Int) ∣ b1 := by rw [Nat.pow_one]; exact hbase_b
      have hc1' : ((3 ^ 1 : Nat) : Int) ∣ c1 := by rw [Nat.pow_one]; exact hbase_c
      have hodd := q9cs_descent_odd 0 a1 a2 b1 b2 c1 c2 d1 d2 ha
        hb1' ihb2 hc1' ihc2 (hE1s 1) (hE2s 1)
      exact ⟨hb1', hodd.1, hc1', hodd.2⟩
    | succ q =>
      -- m: q+1 → q+2（偶段 m=q+1 で b₁,c₁ を深め、奇段 m=q+1 で b₂,c₂ を追随）
      have heven := q9cs_descent_even (q + 1) (by omega) a1 a2 b1 b2 c1 c2 d1 d2 ha
        ihb1 ihb2 ihc1 ihc2 (hE1f (q + 1 + 1)) (hE2f (q + 1 + 1))
      have hodd := q9cs_descent_odd (q + 1) a1 a2 b1 b2 c1 c2 d1 d2 ha
        heven.1 ihb2 heven.2 ihc2 (hE1s (q + 1 + 1)) (hE2s (q + 1 + 1))
      exact ⟨heven.1, hodd.1, heven.2, hodd.2⟩

/-! ## q9cs-7: 一般レベル n の val 計算補題と q3rqMul 座標の忠実性（rep 橋）

Module B は E′=0（z3 の等式）を各レベル n の Int rep 合同（q9cs_descent_all の hE 群の形）
に読む。その橋の部品: q3mc の val-1 補題の一般 n 版（rfl 系）＋ q3rqMul 1 回分の座標が
本ファイルの q9csMulFst/Snd に一致することの実証＋ z3 零元の rep 可除性。 -/

/-- (x+y) のレベル n 値（q3mc_add_val1 の一般 n 版）。 -/
theorem q9cs_add_valn (n : Nat) (x y : z3.carrier) (x1 y1 : Int)
    (hx : x.val n = Quot.mk (modCong (3 ^ n)).rel x1)
    (hy : y.val n = Quot.mk (modCong (3 ^ n)).rel y1) :
    (z3.add x y).val n = Quot.mk (modCong (3 ^ n)).rel (x1 + y1) := by
  show (zmod (3 ^ n)).mul (x.val n) (y.val n) = _
  rw [hx, hy]
  rfl

/-- (−x) のレベル n 値。 -/
theorem q9cs_neg_valn (n : Nat) (x : z3.carrier) (x1 : Int)
    (hx : x.val n = Quot.mk (modCong (3 ^ n)).rel x1) :
    (z3.neg x).val n = Quot.mk (modCong (3 ^ n)).rel (-x1) := by
  show (zmod (3 ^ n)).inv (x.val n) = _
  rw [hx]
  rfl

/-- (x·y) のレベル n 値。 -/
theorem q9cs_mul_valn (n : Nat) (x y : z3.carrier) (x1 y1 : Int)
    (hx : x.val n = Quot.mk (modCong (3 ^ n)).rel x1)
    (hy : y.val n = Quot.mk (modCong (3 ^ n)).rel y1) :
    (z3.mul x y).val n = Quot.mk (modCong (3 ^ n)).rel (x1 * y1) := by
  show zmodMul (3 ^ n) (x.val n) (y.val n) = _
  rw [hx, hy]
  rfl

/-- D = −3 のレベル n 値（q3rq_D_val1 の一般 n 版・q3rq_three_val 消費）。 -/
theorem q9cs_D_valn (n : Nat) :
    q3rqD.val n = Quot.mk (modCong (3 ^ n)).rel (-3) := by
  show (zmod (3 ^ n)).inv (q3rqThree.val n) = Quot.mk (modCong (3 ^ n)).rel (-3)
  rw [q3rq_three_val n]
  rfl

/-- **忠実性（第 1 座標）**: q3rqMul の第 1 座標のレベル n rep は q9csMulFst
    （D=−3 代入・+(−3)· と −3· の差は Quot.sound で吸収）。 -/
theorem q9cs_rq_mul_fst_valn (n : Nat) (x y : q3rqCar) (x1 x2 y1 y2 : Int)
    (hx1 : x.1.val n = Quot.mk (modCong (3 ^ n)).rel x1)
    (hx2 : x.2.val n = Quot.mk (modCong (3 ^ n)).rel x2)
    (hy1 : y.1.val n = Quot.mk (modCong (3 ^ n)).rel y1)
    (hy2 : y.2.val n = Quot.mk (modCong (3 ^ n)).rel y2) :
    (q3rqMul x y).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst x1 x2 y1 y2) := by
  have h : (z3.add (z3.mul x.1 y.1) (z3.mul q3rqD (z3.mul x.2 y.2))).val n
      = Quot.mk (modCong (3 ^ n)).rel (x1 * y1 + (-3) * (x2 * y2)) :=
    q9cs_add_valn n (z3.mul x.1 y.1) (z3.mul q3rqD (z3.mul x.2 y.2))
      (x1 * y1) ((-3) * (x2 * y2))
      (q9cs_mul_valn n x.1 y.1 x1 y1 hx1 hy1)
      (q9cs_mul_valn n q3rqD (z3.mul x.2 y.2) (-3) (x2 * y2) (q9cs_D_valn n)
        (q9cs_mul_valn n x.2 y.2 x2 y2 hx2 hy2))
  show (z3.add (z3.mul x.1 y.1) (z3.mul q3rqD (z3.mul x.2 y.2))).val n
    = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst x1 x2 y1 y2)
  rw [h]
  apply Quot.sound
  show ((3 ^ n : Nat) : Int)
    ∣ (x1 * y1 + (-3) * (x2 * y2) - (x1 * y1 - 3 * (x2 * y2)))
  exact ⟨0, by rw [Int.mul_zero]; omega⟩

/-- **忠実性（第 2 座標）**: q3rqMul の第 2 座標のレベル n rep は q9csMulSnd（定義一致）。 -/
theorem q9cs_rq_mul_snd_valn (n : Nat) (x y : q3rqCar) (x1 x2 y1 y2 : Int)
    (hx1 : x.1.val n = Quot.mk (modCong (3 ^ n)).rel x1)
    (hx2 : x.2.val n = Quot.mk (modCong (3 ^ n)).rel x2)
    (hy1 : y.1.val n = Quot.mk (modCong (3 ^ n)).rel y1)
    (hy2 : y.2.val n = Quot.mk (modCong (3 ^ n)).rel y2) :
    (q3rqMul x y).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd x1 x2 y1 y2) := by
  show (z3.add (z3.mul x.1 y.2) (z3.mul x.2 y.1)).val n
    = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd x1 x2 y1 y2)
  exact q9cs_add_valn n (z3.mul x.1 y.2) (z3.mul x.2 y.1) (x1 * y2) (x2 * y1)
    (q9cs_mul_valn n x.1 y.2 x1 y2 hx1 hy2)
    (q9cs_mul_valn n x.2 y.1 x2 y1 hx2 hy1)

/-- **z3 零元の rep 可除性**: x = 0 なら任意レベル n の任意 rep j は 3^n で割れる
    （E′=0 を q9cs_descent_all の hE 仮定の形に読む橋）。 -/
theorem q9cs_zero_rep_dvd (x : z3.carrier) (hx : x = z3.zero) (n : Nat) (j : Int)
    (hj : x.val n = Quot.mk (modCong (3 ^ n)).rel j) :
    ((3 ^ n : Nat) : Int) ∣ j := by
  have h0 : x.val n = Quot.mk (modCong (3 ^ n)).rel 0 := by rw [hx]; rfl
  rw [h0] at hj
  have hd := quot_exact intGrp (modCong (3 ^ n)) hj
  obtain ⟨k, hk⟩ := hd
  refine ⟨-k, ?_⟩
  rw [Int.mul_neg]
  omega

end IUT
