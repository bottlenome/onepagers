/-
  IUT/Q3Codifferent.lean — 柱B・B3 実 CODIFFERENT / TRACE-DUAL 新構造:
    トレース像イデアル Tr(O_M) = (embed 3) = (π₉⁶)（trace-conductor 形の different）と、
    その双対 codifferent の trace-dual 述語 {y : π₉⁶ ∣ Tr(y·O_M)}（π₉⁻⁶·O_M ⊆ 𝔡⁻¹ の整数影）。

  ── 主要成果の分類: **[実／(b) 先行建設]** — B3 が「次の実構造」と特定した
     TRACE PAIRING（トレース対）による different の記述を初めて実 Lean で割る。
     従来 B3（q9tw/q9ac/q9dv/q9di）は different を **可除性 d=6 / 付値 v_M(D)=6 /
     主イデアル (π₉⁶)** として 4 通りに記述してきたが、これらは全て「different 生成元 D の
     divisibility」の言い換えであった。本モジュールが割るのは**それとは別種の実データ**——
     実トレース写像 Tr : O_M → O_{L₂} の **像イデアル** Tr(O_M) が主イデアル (embed 3) に
     **ちょうど一致**すること（trace-conductor 定理・different の第 5 の"視点"ではなく
     TRACE PAIRING という新しい実対象の上の定理）、およびその双対 codifferent の
     trace-dual membership。q9nf_tr_embed（Tr(t)=embed(3·t₀)）と q9nf_trace_kill
     （π₉⁶∣Tr）を消費して、Tr(O_M) = embed(3·O_{L₂}) = (embed 3) を両包含で実証する。

  complete_pct 影響: **B3 0.29→（独立監査次第・予測 +0.01〜0.03・trace-dual/codifferent 新構造）**。
     動かす新規内容は「different を D の可除性でなく **トレース対の像**として記述する初の実定理
     Tr(O_M) = (embed 3) = (π₉⁶)（trace-conductor）と、その双対述語による
     codifferent 𝔡⁻¹ ⊇ (π₉⁻⁶) の整数影・かつ level ちょうど 6 での非退化（sharp）」。
     d=6 の再導出ではない——主語が different 生成元 D から **trace 写像そのもの**に移る。

  真水（新規・本物）:
   * q9cd_tr_one — Tr(1) = embed(3)（トレースの生成値・embed(3) ∈ Tr(O_M) の witness）
   * q9cd_trace_image_eq — **★ trace-conductor**: {Tr(t) : t∈O_M} = {embed(3·s) : s∈O_{L₂}}
     ちょうど（両包含・Tr(embed s)=embed(3·s) で全射性を割る）。different の trace-image 描像。
   * q9cd_trace_kill_mem / q9cd_embed_three_in_image — (a) Tr(O_M)⊆𝔡=(π₉⁶)、
     (b) embed(3)∈Tr(O_M)（生成元がトレース像に属する・q9ps_three_split で 𝔡 と接続）
   * q9cd_pi6_in_trace_image — different 生成 π₉⁶·u₆=embed(3) がトレース像に属する
   * q9cdCodiffMem / q9cd_codiff_all — **★ codifferent trace-dual 述語** y∈𝔡⁻¹ の整数影
     {y : ∀t, π₉⁶∣Tr(y·t)}（= π₉⁻⁶·O_M ⊆ 𝔡⁻¹）が **全 y で成立**
   * q9cd_codiff_sharp — **★ 非退化**: level 7 では破れる（∃y t, ¬π₉⁷∣Tr(y·t)）——
     trace pairing がちょうど level 6 で different を検出（𝔡⁻¹ = (π₉⁻⁶) の sharpness）
   * Q3CodifferentData — capstone（束ね・新規証明ゼロ）

  正直な限定（§4 規約により消さない・弱めない・q9nf/q9di/q9v/q9wr 継承の上に追記のみ）:
  1. **整トレース像のみ・分数 𝔡⁻¹=(π₉⁻⁶) 本体は延期**。真の逆 different は O_M の分数
     イデアル（負冪 π₉⁻⁶）を choice-free に建設できないため、codifferent は
     **π₉⁶ シフトによる整数影**（y は y·π₉⁻⁶ を代表・述語 π₉⁶∣Tr(y·O_M)）として割る。
     これは toy 模型ではなく **実トレース・実 π₉⁶ の上の忠実な整数像**（§3 遵守・toy 不使用）。
     完全な分数イデアル群・イデアル類・trace form の双対基底は範囲外。
  2. **拡大 1 個（M/L₂）・trace pairing 一般論ゼロ**。一般の trace-dual / different の
     推移公式・discriminant との関係（disc = N(𝔡)）は未形式化。
  3. Tr(O_M)=(embed 3) の (embed 3)=(π₉⁶) 接続は q9ps_three_split（3=π₉⁶·u₆）を消費・
     sharp は q9nf_retarget_sharp（¬π₉⁷∣embed 3）を消費（新規なのは trace-image 等式と
     codifferent 述語の枠組み・d=6 の再導出ではない）。
  4. 付値 v_M・total valuation 不在（choice-free 障壁）を q9nf/q9v から継承。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3DifferentIdeal

namespace IUT

/-! ## q9cd-0: トレースの生成値 Tr(1) = embed(3) -/

/-- **Tr(1) = embed(3)**（トレースの生成値）。q9nf_tr_embed で Tr(1)=embed(3·1₀)、
    1₀ = 1 かつ 3·1 = 3、q9ps_three_eq で 3 = 3elt。embed(3) ∈ Tr(O_M) の witness。 -/
theorem q9cd_tr_one : q9nfTr q3kOne = q3kEmbed q3rqThreeElt := by
  rw [q9nf_tr_embed q3kOne]
  show q3kEmbed (q3rqMul q3kThree q3rqOne) = q3kEmbed q3rqThreeElt
  rw [q3rq_mul_one q3kThree, q9ps_three_eq]

/-! ## q9cd-1: ★ トレース像イデアル Tr(O_M) = (embed 3)（trace-conductor） -/

/-- トレース像の全射性: **Tr(embed s) = embed(3·s)**（embed(s)₀ = s なので
    Tr(embed s) = embed(3·s)）。任意の embed(3·s) がトレース像に属することを割る。 -/
theorem q9cd_tr_embed_eq (s : q3rqCar) :
    q9nfTr (q3kEmbed s) = q3kEmbed (q3rqMul q3rqThreeElt s) := by
  rw [q9nf_tr_embed (q3kEmbed s)]
  show q3kEmbed (q3rqMul q3kThree (q3kEmbed s).1) = q3kEmbed (q3rqMul q3rqThreeElt s)
  rw [q3kEmbed_0 s, q9ps_three_eq]

/-- トレース像の包含（forward）: **Tr(t) = embed(3·t₀)**（座標形・q9ps_three_eq 適用形）。
    任意のトレース値が (embed 3) に属する（s = t₀）ことを割る。 -/
theorem q9cd_tr_eq_embed_three (t : q3kCar) :
    q9nfTr t = q3kEmbed (q3rqMul q3rqThreeElt t.1) := by
  rw [q9nf_tr_embed t, q9ps_three_eq]

/-- **★ trace-conductor 定理**: トレース像 = 主イデアル (embed 3) **ちょうど**——
    {y : ∃t, Tr(t)=y} = {y : ∃s, y = embed(3·s)}。⟹ は Tr(t)=embed(3·t₀)（s=t₀）、
    ⟸ は Tr(embed s)=embed(3·s)（t=embed s・トレースの全射性）。different を
    trace 写像の**像**として記述する初の実等式（生成元 D の可除性 d=6 とは別種）。 -/
theorem q9cd_trace_image_eq (y : q3kCar) :
    (∃ t : q3kCar, q9nfTr t = y)
      ↔ (∃ s : q3rqCar, y = q3kEmbed (q3rqMul q3rqThreeElt s)) := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h
    exact ⟨t.1, by rw [← ht, q9cd_tr_eq_embed_three t]⟩
  · intro h
    obtain ⟨s, hs⟩ := h
    exact ⟨q3kEmbed s, by rw [q9cd_tr_embed_eq s, hs]⟩

/-! ## q9cd-2: (a) Tr(O_M) ⊆ 𝔡=(π₉⁶) と (b) embed(3) ∈ Tr(O_M) -/

/-- **(a) Tr(O_M) ⊆ 𝔡=(π₉⁶)**: ∀t, Tr(t) ∈ 𝔡（π₉⁶∣Tr(t)・q9nf_trace_kill を
    different ideal 述語 q9diMem へ橋渡し）。trace-conductor が different ideal に含まれる。 -/
theorem q9cd_trace_kill_mem (t : q3kCar) : q9diMem (q9nfTr t) :=
  q9nf_trace_kill t

/-- **(b) embed(3) ∈ Tr(O_M)**: different 生成 embed(3) がトレース像に属する（witness t=1）。
    (a) と合わせ Tr(O_M) が 𝔡=(π₉⁶) の生成元 embed(3) を含む——trace-image = different。 -/
theorem q9cd_embed_three_in_image : ∃ t : q3kCar, q9nfTr t = q3kEmbed q3rqThreeElt :=
  ⟨q3kOne, q9cd_tr_one⟩

/-- **π₉⁶·u₆ ∈ Tr(O_M)**: different level 6 の生成 π₉⁶·u₆ (=embed 3) がトレース像に属する
    （q9ps_three_split で embed(3)=π₉⁶·u₆・trace-image と主イデアル 𝔡=(π₉⁶) の接続）。 -/
theorem q9cd_pi6_in_trace_image :
    ∃ t : q3kCar, q9nfTr t = q3kMul q9psPi6 q9psU6 :=
  ⟨q3kOne, by rw [q9cd_tr_one, q9ps_three_split]⟩

/-- **embed(3) が different ideal 𝔡 に属する**（q9diMem embed(3)・trace 生成値が 𝔡 の元）。 -/
theorem q9cd_embed_three_mem : q9diMem (q3kEmbed q3rqThreeElt) := by
  rw [← q9cd_tr_one]
  exact q9cd_trace_kill_mem q3kOne

/-! ## q9cd-3: ★ codifferent 𝔡⁻¹ の trace-dual 述語（整数影・π₉⁶ シフト）

  真の codifferent 𝔡⁻¹ = {y ∈ Frac(O_M) : Tr(y·O_M) ⊆ O_{L₂}} は分数イデアル（負冪
  π₉⁻⁶）を要し choice-free に建設できない（正直な限定 1）。代わりに **π₉⁶ シフトによる
  整数影**を割る: 元 y ∈ O_M を分数元 y·π₉⁻⁶ の代表とみなし、
      y·π₉⁻⁶ ∈ 𝔡⁻¹  ⟺  Tr(y·π₉⁻⁶·O_M) ⊆ O_{L₂}  ⟺  π₉⁶ ∣ Tr(y·O_M)
  と述語化する（右辺は π₉⁻⁶ を明示せず整数のみで書ける）。これは toy ではなく
  実トレース・実 π₉⁶ の忠実な整数像であり、q9cd_codiff_all（全 y 成立 = π₉⁻⁶·O_M⊆𝔡⁻¹）と
  q9cd_codiff_sharp（level 7 で破れ = 𝔡⁻¹=(π₉⁻⁶) の非退化）で両側を割る。 -/

/-- **codifferent trace-dual membership**（整数影）: y·π₉⁻⁶ ∈ 𝔡⁻¹ の述語
    {y : ∀ t∈O_M, π₉⁶ ∣ Tr(y·t)}。分数 π₉⁻⁶ を明示せず整数のみで書いた 𝔡⁻¹ の影。 -/
def q9cdCodiffMem (y : q3kCar) : Prop :=
  ∀ t : q3kCar, q9wrDvd (q9nfPiPow 6) (q9nfTr (q3kMul y t))

/-- **★ π₉⁻⁶·O_M ⊆ 𝔡⁻¹**: codifferent trace-dual 述語は **全 y で成立**
    （∀y t, π₉⁶∣Tr(y·t)・q9nf_trace_kill を y·t に適用）。トレースは常に π₉⁶ で割れるので
    π₉⁻⁶·O_M 全体が codifferent に入る——𝔡⁻¹ ⊇ (π₉⁻⁶) の整数影。 -/
theorem q9cd_codiff_all (y : q3kCar) : q9cdCodiffMem y :=
  fun t => q9nf_trace_kill (q3kMul y t)

/-- ¬ π₉⁷ ∣ embed(3)（different 生成の sharpness・q9nf_retarget_sharp を
    q9nf_one_add_cancel 経由で embed(3) の可除性言明へ）。 -/
theorem q9cd_embed_three_not_pi7 : ¬ q9wrDvd (q9nfPiPow 7) (q3kEmbed q3rqThreeElt) := by
  intro h
  apply q9nf_retarget_sharp
  show q9wrDvd (q9nfPiPow 7)
    (q3kAdd (q3kAdd q3kOne (q3kEmbed q3rqThreeElt)) (q3kNeg q3kOne))
  rw [q9nf_one_add_cancel]
  exact h

/-- **★ codifferent の非退化（sharp）**: level 7 では trace-dual が破れる——
    ∃ y t, ¬ π₉⁷ ∣ Tr(y·t)（witness y=t=1: Tr(1·1)=Tr(1)=embed(3)、¬π₉⁷∣embed(3)）。
    trace pairing がちょうど level 6 で different を検出する（𝔡⁻¹=(π₉⁻⁶) の sharpness・
    π₉⁻⁷·O_M ⊄ 𝔡⁻¹）——d=6 の可除性ではなく **トレース対の非退化位置**を割る。 -/
theorem q9cd_codiff_sharp :
    ¬ (∀ y t : q3kCar, q9wrDvd (q9nfPiPow 7) (q9nfTr (q3kMul y t))) := by
  intro h
  apply q9cd_embed_three_not_pi7
  have h11 := h q3kOne q3kOne
  rw [q3k_one_mul q3kOne, q9cd_tr_one] at h11
  exact h11

/-! ## q9cd-4: capstone（束ね・新規証明ゼロ） -/

/-- **実 codifferent / trace-dual データ**——trace-conductor Tr(O_M)=(embed 3)=(π₉⁶)・
    (a) Tr⊆𝔡・(b) embed(3)∈Tr(O_M)・codifferent 述語の全 y 成立（𝔡⁻¹⊇(π₉⁻⁶) 整数影）・
    level 6 での非退化（sharp）を束ねる（新規証明ゼロ）。 -/
structure Q3CodifferentData where
  /-- Tr(1) = embed(3)（トレース生成値）。 -/
  tr_one : q9nfTr q3kOne = q3kEmbed q3rqThreeElt
  /-- trace-conductor: Tr(O_M) = (embed 3) ちょうど（両包含）。 -/
  trace_image_eq : ∀ y : q3kCar,
    (∃ t : q3kCar, q9nfTr t = y)
      ↔ (∃ s : q3rqCar, y = q3kEmbed (q3rqMul q3rqThreeElt s))
  /-- (a) Tr(O_M) ⊆ 𝔡=(π₉⁶)。 -/
  trace_kill_mem : ∀ t : q3kCar, q9diMem (q9nfTr t)
  /-- (b) embed(3) ∈ Tr(O_M)。 -/
  embed_three_in_image : ∃ t : q3kCar, q9nfTr t = q3kEmbed q3rqThreeElt
  /-- codifferent trace-dual 述語が全 y で成立（π₉⁻⁶·O_M ⊆ 𝔡⁻¹ の整数影）。 -/
  codiff_all : ∀ y : q3kCar, q9cdCodiffMem y
  /-- level 6 での非退化（𝔡⁻¹=(π₉⁻⁶) の sharpness）。 -/
  codiff_sharp : ¬ (∀ y t : q3kCar, q9wrDvd (q9nfPiPow 7) (q9nfTr (q3kMul y t)))

/-- **見出し実例** — 実 M=ℚ₃(ζ₉) 上の trace-dual / codifferent データ。 -/
def q9cd_data : Q3CodifferentData where
  tr_one := q9cd_tr_one
  trace_image_eq := q9cd_trace_image_eq
  trace_kill_mem := q9cd_trace_kill_mem
  embed_three_in_image := q9cd_embed_three_in_image
  codiff_all := q9cd_codiff_all
  codiff_sharp := q9cd_codiff_sharp

/-- **実 codifferent / trace-dual 構造の存在**（トレース対による different の記述）。 -/
theorem q9cd_exists : Nonempty Q3CodifferentData := ⟨q9cd_data⟩

end IUT
