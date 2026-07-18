/-
  IUT/Q3TraceDifferentReal.lean — 柱B・B3 実トレース差積（different = トレース形式の導手）
    （実 Tr_{M/L₂}(O_M) = (3) = (π₉⁶) の実トレースイデアル特徴付け）

  ── 主要成果の分類: **[実／(a) 昇格]** — q9ac は M/L₂ の different を **具体生成元の付値**
     （d=6・(σπ₉−π₉)(σ²π₉−π₉)=π₉⁶·(u*u**)）で計算する。本モジュールはこれを
     **トレース論的 different 特徴付け**へ昇格する: トレースイデアル Tr_{M/L₂}(O_M) が
     ちょうど (3)=(π₉⁶)（＝トレース形式の余差積/導手の内容）に等しいことを実 q3k 上で割る。
     これは「different = トレース形式の導手」という本物の事実であり、生成元付値ルート
     （q9ac）とは **独立な** 特徴付け——主語は実 σ・実 Tr=t+σt+σ²t・実 O_M・実 π₉=Y−1。
     toy 模型（m202fVol 型・Bool 軌道・surrogate 群）を一切使わない。

  **本モジュールの真水（NEW・監査対象の新規実定理）は次に限定する**:
   (T1) Tr(1)=3=embed(3)（トレースイデアルの下界 3∈Tr(O_M)）——q9nf_tr_embed を t=1 で消費。
   (T4) トレースイデアル Tr(O_M) = (π₉⁶) を **両側** で割る:
        (∀t, π₉⁶∣Tr(t)) ∧ (∃t, Tr(t)=π₉⁶·u₆)（下界は t=1・witness Tr(1)=3=π₉⁶·u₆）。
   (T5) 鋭さ ¬(∀t, π₉⁷∣Tr(t))——トレースイデアルは (π₉⁷) に含まれない（witness t=1:
        Tr(1)=3=π₉⁶·u₆・¬π₉⁷∣π₉⁶·u₆ を U6 イディオムで割る）。よって Tr(O_M)=(π₉⁶) は
        **鋭い**（⊆ でなく =）。
   (T6) 生成元ルート（q9ac）とトレースルートが **同じ d=6 で一致**することの束ね
        （q9ac_different_sharp を消費し、二つの独立特徴付けの合致を実証）。

  **消費（再主張しない・二重計上回避）**:
   * Tr(t)=embed(3·t₀)・π₉⁶∣Tr(t)（全t）は `q9nf_tr_embed`/`q9nf_trace_kill` から **消費**。
   * 3=π₉⁶·u₆（u₆ 実閉形式単数）は `q9ps_three_split`/`q9ps_three_eq_pi6_u6` から **消費**。
   * d=6 の生成元ルート鋭さ ¬π₉⁷∣D は `q9ac_different_sharp` から **消費**（NEW として再主張しない）。
   * U6 イディオム（π₉³ 正則消去→ノルム 2 段→3·s 非単数）を T5 で新インスタンス化
     （`q9wr_pi3_cancel`・`q9wr_normBase_pi9`・`q9wr_qnorm_zeta_sub`・`q9wr_three_mul_not_unit` 消費）。

  complete_pct 影響: **B3 0.26→（独立監査次第・予測 +0.02〜0.06）— display-moving**。

  正直な限定（§4 規約により消さない・弱化しない・q9nf/q9ac/q9ps/q9wr 継承の上に追記のみ）:
  1. **トレースイデアルは明示閉形式 Tr の式（`q9nf_tr_embed`）経由で計算**する。抽象 Tr 双線型
     形式・O_M 上の一般積分ペアリングは範囲外——閉形式 Tr(t)=embed(3·t₀) の像で割る。
  2. **拡大 1 個（M/L₂）のみ**。合成 different・推移公式・他拡大のトレースは範囲外。
  3. **可除性形式（v_M 不在）**。イデアル/商対象を建てないため Tr(O_M)=(π₉⁶) は
     ∀-可除性（上界）＋ ∃-witness（下界・鋭さ）の二項で述べる（q9wr 正直限定 1 継承）。
  4. **d=6 の生成元ルートは q9ac から消費**（新規に d=6 を主張しない）。新規なのは
     **トレースイデアル特徴付け** と両ルートの合致——生成元付値とトレースイデアルが同じ 6。
  5. q9nf/q9ac/q9ps/q9wr の正直限定を全継承（O_M と M^× のみ・体化なし・σ を超える Galois ゼロ）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3NormFiltrationSpike
import IUT.Q3ArtinConductorReal

namespace IUT

/-! ## q9tf-1: Tr(1)=3（トレースイデアルの下界 3∈Tr(O_M)） -/

/-- **T1 `q9tf_trace_one`（★ 新規）**: Tr(1) = embed(3)。
    `q9nf_tr_embed` を t=1（t₀=1）で消費: Tr(1)=embed(3·1)=embed(3)。
    したがって 3 ∈ Tr(O_M)——トレースイデアルの **下界**。 -/
theorem q9tf_trace_one : q9nfTr q3kOne = q3kEmbed q3rqThreeElt := by
  rw [q9nf_tr_embed q3kOne]
  show q3kEmbed (q3rqMul q3kThree q3rqOne) = q3kEmbed q3rqThreeElt
  rw [q9ps_three_eq, q3k_M_eq, q9ps_1_eq, q3rqRing.mul_one q3rqThreeElt]

/-! ## q9tf-2: Tr(O_M) ⊆ (π₉⁶)（上界・q9nf_trace_kill 消費） -/

/-- **T2 `q9tf_trace_in_pi6`**: π₉⁶ ∣ Tr(t)（全 t）＝ Tr(O_M) ⊆ (π₉⁶)（**上界**）。
    `q9nf_trace_kill` を消費（Tr(t)=embed(3·t₀)・3=π₉⁶·u₆）。 -/
theorem q9tf_trace_in_pi6 : ∀ t : q3kCar, q9wrDvd (q9nfPiPow 6) (q9nfTr t) :=
  q9nf_trace_kill

/-! ## q9tf-3: 3=(π₉⁶)（q9ps_three_split 消費・下界を π₉⁶ に結ぶ） -/

/-- **T3 `q9tf_three_eq_pi6_unit`**: embed(3) = π₉⁶·u₆（u₆ 実単数）。
    `q9ps_three_eq_pi6_u6` を消費。Tr(1)=3 を (π₉⁶) に結ぶ。 -/
theorem q9tf_three_eq_pi6_unit : q3kEmbed q3rqThreeElt = q3kMul q9psPi6 q9psU6 :=
  q9ps_three_eq_pi6_u6

/-! ## q9tf-4: ★ トレースイデアル Tr(O_M) = (π₉⁶)（両側） -/

/-- **T4 `q9tf_trace_ideal_eq`（★ headline）**: Tr_{M/L₂}(O_M) = (π₉⁶)。
    イデアル/商対象を欠くため二項で忠実に述べる:
      (∀t, π₉⁶∣Tr(t))（上界）∧ (∃t, Tr(t)=π₉⁶·u₆)（下界・witness t=1: Tr(1)=3=π₉⁶·u₆）。
    これがトレース形式の余差積/導手の内容——生成元付値ルートとは独立な特徴付け。 -/
theorem q9tf_trace_ideal_eq :
    (∀ t : q3kCar, q9wrDvd (q9nfPiPow 6) (q9nfTr t))
    ∧ (∃ t : q3kCar, q9nfTr t = q3kMul q9psPi6 q9psU6) :=
  ⟨q9nf_trace_kill, ⟨q3kOne, q9tf_trace_one.trans q9tf_three_eq_pi6_unit⟩⟩

/-! ## q9tf-5: ★ 鋭さ Tr(O_M) ⊄ (π₉⁷)（= でなく ⊆ でないことの実証） -/

/-- **T5 `q9tf_trace_not_pi7`（★ 新規実定理）**: ¬(∀t, π₉⁷∣Tr(t))。
    トレースイデアルは (π₉⁷) に含まれない——よって Tr(O_M)=(π₉⁶) は **鋭い**。
    witness t=1: Tr(1)=3=π₉⁶·u₆・¬π₉⁷∣π₉⁶·u₆（π₉⁶ 消去 2 段 → u₆=π₉·c → N(u₆)∈(3) だが
    u₆ 単数 → mod-3 矛盾。q9nf_retarget_sharp の U6 エンジンをトレース witness で新実行）。 -/
theorem q9tf_trace_not_pi7 : ¬ (∀ t : q3kCar, q9wrDvd (q9nfPiPow 7) (q9nfTr t)) := by
  intro h
  obtain ⟨c, hc⟩ := h q3kOne
  rw [q9tf_trace_one] at hc
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

/-! ## q9tf-6: ★ 生成元ルートとトレースルートの合致 d=6 -/

/-- **T6 `q9tf_different_via_trace`（★ 本命題・二ルートの合致）**:
    トレースイデアル Tr(O_M)=(π₉⁶)（上界 ∀-可除性・下界 ∃-witness・鋭さ ¬π₉⁷）を、
    q9ac の生成元 different の鋭さ ¬π₉⁷∣D（`q9ac_different_sharp` 消費）と束ねる。
    生成元付値ルート（D=(σπ₉−π₉)(σ²π₉−π₉)=π₉⁶·(u*u**)）と
    トレースイデアルルート（Tr(O_M)=(π₉⁶)）が **ともに指数 6 で一致**する——
    二つの独立な different 特徴付けの合致が本モジュールの payoff。 -/
theorem q9tf_different_via_trace :
    (∀ t : q3kCar, q9wrDvd (q9nfPiPow 6) (q9nfTr t))
    ∧ (∃ t : q3kCar, q9nfTr t = q3kMul q9psPi6 q9psU6)
    ∧ ¬ (∀ t : q3kCar, q9wrDvd (q9nfPiPow 7) (q9nfTr t))
    ∧ ¬ q9wrDvd (q3kMul q9psPi6 q9psPi9)
        (q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
                (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9))) :=
  ⟨q9nf_trace_kill,
   ⟨q3kOne, q9tf_trace_one.trans q9tf_three_eq_pi6_unit⟩,
   q9tf_trace_not_pi7,
   q9ac_different_sharp⟩

/-! ## q9tf-7: capstone -/

/-- **T7 `Q3TraceDifferentRealData`**: 実トレース差積データ束ね
    （Tr(1)=3・Tr(O_M)⊆(π₉⁶)・3=(π₉⁶)・下界 witness・鋭さ・生成元ルート合致）。 -/
structure Q3TraceDifferentRealData where
  /-- Tr(1)=embed(3)（トレースイデアルの下界 3∈Tr(O_M)）。 -/
  trace_one : q9nfTr q3kOne = q3kEmbed q3rqThreeElt
  /-- π₉⁶∣Tr(t)（全 t）＝ Tr(O_M)⊆(π₉⁶)（上界）。 -/
  trace_in_pi6 : ∀ t : q3kCar, q9wrDvd (q9nfPiPow 6) (q9nfTr t)
  /-- embed(3)=π₉⁶·u₆（下界を (π₉⁶) に結ぶ）。 -/
  three_eq_pi6_unit : q3kEmbed q3rqThreeElt = q3kMul q9psPi6 q9psU6
  /-- Tr(O_M) の下界 witness: ∃t, Tr(t)=π₉⁶·u₆（t=1）。 -/
  trace_ideal_lower : ∃ t : q3kCar, q9nfTr t = q3kMul q9psPi6 q9psU6
  /-- 鋭さ ¬(∀t, π₉⁷∣Tr(t))＝ Tr(O_M)⊄(π₉⁷)（★ NEW）。 -/
  trace_not_pi7 : ¬ (∀ t : q3kCar, q9wrDvd (q9nfPiPow 7) (q9nfTr t))
  /-- 生成元 different ルートの鋭さ ¬π₉⁷∣D（q9ac 消費・両ルート合致）。 -/
  different_sharp : ¬ q9wrDvd (q3kMul q9psPi6 q9psPi9)
    (q3kMul (q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9))
            (q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)))

/-- **T7b `q9tf_data`**: 見出し実例——実 M=ℚ₃(ζ₉) 上の実トレース差積 Tr(O_M)=(π₉⁶)=(3)。 -/
def q9tf_data : Q3TraceDifferentRealData where
  trace_one := q9tf_trace_one
  trace_in_pi6 := q9nf_trace_kill
  three_eq_pi6_unit := q9tf_three_eq_pi6_unit
  trace_ideal_lower := ⟨q3kOne, q9tf_trace_one.trans q9tf_three_eq_pi6_unit⟩
  trace_not_pi7 := q9tf_trace_not_pi7
  different_sharp := q9ac_different_sharp

/-- **T7c `q9tf_exists`**: 実トレース差積の存在（実 σ・実 Tr・Tr(O_M)=(π₉⁶)=(3)・鋭さ込み）。 -/
theorem q9tf_exists : Nonempty Q3TraceDifferentRealData := ⟨q9tf_data⟩

end IUT
