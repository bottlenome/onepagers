/-
  # M267F: 非負有理数 ℚ≥0 の乗法建設と比較射 nnqToQ の順序半環準同型への昇格
        （柱C・log-volume 橋の残件 nnqToQ 乗法保存＋順序線形性を 1 スライス）

  ## 二軸（§1）
  * 分類: **[実／(a)昇格＋(b)本物の先行建設]**。
  * complete_pct 影響: **C を前進**（真水）。M236F（`NNQtoQHom.lean`）は
    比較射 nnqToQ : ℚ≥0 → ℚ を**加法**モノイド準同型に、M262F
    （`NNQOrder.lean`）は**順序**モノイド準同型に留めたが、両者とも
    「ℚ≥0 に乗法未定義ゆえ環準同型 map_mul は扱わない」と正直申告して
    いた。本層はその残件を**本物化**する: (b) ℚ≥0 上に本物の乗法 nnqMul
    をゼロから建設（可換モノイド・零吸収・順序単調）し、(a) 比較射
    nnqToQ を**乗法・単位元を保つ順序半環準同型**へ昇格する。さらに
    M262F が本層送りにした**順序線形性**（nnqLe の全順序性）を閉じる。
    これにより log-volume 橋の ℚ≥0 → ℚ 比較射が Mochizuki の要求する
    「順序半環の忠実な埋め込み」に一段近づく（C4 log-volume 橋の本物度前進）。

  ## 内容
  * M267F-1 `preDen_comm` / `nnq_mul_cross` — 乗法の分母簿記の可換律と
    well-def の核となる Nat 交差積恒等式（正因子の付替）。
  * M267F-2 `preMul` / `preMul_comm` / `preMul_assoc` / `preOne_mul` —
    **代表レベルの乗法** (a/(b+1))·(c/(d+1)) = ac/((b+1)(d+1))。分子は
    ac、分母簿記は preDen b d（(preDen b d)+1 = (b+1)(d+1)）。可換・結合・
    左単位を対の等式として直接検証（結合の分母は M67F の preDen_assoc）。
  * M267F-3 `preMul_rel_left` / `preMul_rel_right` / `nnqMul` / `nnqOne`
    — 両引数での well-definedness（交差積付替）と ℚ≥0 上の乗法（二重
    Quot.lift、choice-free）・単位元 1 = 1/1。
  * M267F-4 `nnqMul_comm` / `nnqMul_assoc` / `nnqOne_mul` / `nnqMul_one`
    / `nnqMul_zero` / `nnqZero_mul` — **ℚ≥0 は乗法可換モノイド + 零吸収**。
  * M267F-5 `nnqToQ_mul`（本丸）— **比較射の乗法保存** nnqToQ(x·y)
    = nnqToQ(x)·nnqToQ(y)。M67F の代表乗法（分子 ac・分母簿記 preDen）を
    M115F の QRat 代表乗法 prMul（分子 ac・分母 (b+1)(d+1)）に読み替え、
    分子は `Int.natCast_mul`、分母は `preDen_succ` を Int にキャストして
    交差積を潰す。M236F の加法性・M262F の順序性に**乗法性**を加えて
    比較射を順序半環準同型に完成させる。
  * M267F-6 `nnqToQ_one` — **単位元の保存** nnqToQ(1) = 1。
  * M267F-7 `nnqMul_mono` — **乗法の順序単調性** x ≤ y → x·c ≤ y·c
    （非負錐上の順序半環の順序公理）。
  * M267F-8 `nnqLe_total` — **順序線形性（全順序性）** nnqLe x y ∨
    nnqLe y x。M262F の正直申告（線形性は本層送り）を回収し、Nat の
    全順序 `Nat.le_total` から交差積で導く。
  * M267F-9 `NNQMulHomData` — 総括データ束と存在。

  ## 意義
  M236F（加法準同型）・M262F（順序準同型）を統合し、比較射 nnqToQ を
  **零・単位・加法・乗法・順序をすべて保つ順序半環準同型**に昇格する。
  ℚ≥0 に本物の乗法半環構造が入り、M67F の実化 log-volume 次数が ℚ・ℝ の
  中で加法だけでなく乗法（スケール合成）でも忠実に読めるようになる。

  ## 正直な限定（§4：消さない・弱めない）
  * **左分配律（乗法の加法への分配 x·(y+z) = x·y + x·z）は本層では
    形式化しない**。代表レベルでは成立する（両辺の交差積は
    a·b·P²·Q·S² + a·c·P²·Q²·S に一致する多項式恒等式）が、ring 系
    タクティク禁止の下での逐次 rw 展開が長大になるため次層送りとする。
    これにより ℚ≥0 は本層では「乗法可換モノイド + 順序 + 零吸収」まで
    であり、**完全な順序半環（分配律込み）には未到達**。比較射の
    乗法保存 nnqToQ_mul 自体は分配律に依存せず完全証明済み。
  * 乗法逆元（体構造）・ℚ≥0 の一般スカラー作用は範囲外（ℚ≥0 は半環）。
  * 順序線形性 nnqLe_total は全順序を与えるが、順序体の完備性・アルキ
    メデス性は本層では扱わない（M262F の限定を継承）。
  * 因子（RDiv）の効果性順序 → degR の乗法的単調性簿記は本層では扱わ
    ない（M67F のサポート上界の表示の自由度が絡むため）。
  * 全て選択公理不使用（型継承除く）。Prop 値 Quot.lift の well-def に
    propext を使う。主要定理の公理は `[propext, Quot.sound]` のみ
    （`#print axioms` で実測、一時確認後に除去）。
  * サブエージェント並行部品。
-/
import IUT.NNQOrder
import IUT.NNQtoQHom

namespace IUT

/-! ## M267F-1: 乗法の分母簿記の可換律と well-def の核 -/

/-- **補題 (M267F-1a): 分母簿記の可換律** — preDen b d = preDen d b。 -/
theorem preDen_comm (b d : Nat) : preDen b d = preDen d b := by
  show b * d + b + d = d * b + d + b
  rw [Nat.mul_comm b d, Nat.add_right_comm]

/-- **補題 (M267F-1b): 乗法 well-def の核となる Nat 交差積恒等式** —
    a·B' = a'·B なら a·c·(B'·D) = a'·c·(B·D)。正因子 c·D を括り出して
    付替を h に帰着する（mul_assoc / mul_left_comm の rw 連鎖）。 -/
theorem nnq_mul_cross (a a' c B B' D : Nat) (h : a * B' = a' * B) :
    a * c * (B' * D) = a' * c * (B * D) := by
  have e1 : a * c * (B' * D) = a * B' * (c * D) := by
    rw [Nat.mul_assoc a c (B' * D), Nat.mul_left_comm c B' D,
      ← Nat.mul_assoc a B' (c * D)]
  have e2 : a' * c * (B * D) = a' * B * (c * D) := by
    rw [Nat.mul_assoc a' c (B * D), Nat.mul_left_comm c B D,
      ← Nat.mul_assoc a' B (c * D)]
  rw [e1, e2, h]

/-! ## M267F-2: 代表レベルの乗法 -/

/-- **M267F-2a: 代表レベルの乗法** — (a,b)·(c,d) = (ac, preDen b d)
    （= ac/((b+1)(d+1))）。分子は積 ac、分母簿記は preDen b d。 -/
def preMul (x y : QPre) : QPre :=
  (x.1 * y.1, preDen x.2 y.2)

/-- **定理 (M267F-2b): 代表乗法の可換律**（対の等式）。 -/
theorem preMul_comm (x y : QPre) : preMul x y = preMul y x := by
  apply qpre_ext
  · show x.1 * y.1 = y.1 * x.1
    exact Nat.mul_comm x.1 y.1
  · exact preDen_comm x.2 y.2

/-- **定理 (M267F-2c): 代表乗法の結合律**（分子は Nat.mul_assoc、分母簿記は
    M67F の preDen_assoc）。 -/
theorem preMul_assoc (p q r : QPre) :
    preMul (preMul p q) r = preMul p (preMul q r) := by
  apply qpre_ext
  · show (p.1 * q.1) * r.1 = p.1 * (q.1 * r.1)
    exact Nat.mul_assoc p.1 q.1 r.1
  · exact preDen_assoc p.2 q.2 r.2

/-- **定理 (M267F-2d): 代表左単位則** (1,0)·y = y（対の等式）。
    (1,0) = 1/1、分子 1·c = c、分母簿記 preDen 0 d = d。 -/
theorem preOne_mul (y : QPre) : preMul (1, 0) y = y := by
  apply qpre_ext
  · show 1 * y.1 = y.1
    exact Nat.one_mul y.1
  · show 0 * y.2 + 0 + y.2 = y.2
    rw [Nat.zero_mul, Nat.add_zero, Nat.zero_add]

/-! ## M267F-3: 両引数での well-definedness と ℚ≥0 上の乗法 -/

/-- **定理 (M267F-3a): 乗法の第一引数の well-definedness** —
    x ~ x' ⟹ x·y ~ x'·y（交差積を preDen_succ で展開し nnq_mul_cross に
    帰着）。 -/
theorem preMul_rel_left {x x' : QPre} (h : nnqRel x x') (y : QPre) :
    nnqRel (preMul x y) (preMul x' y) := by
  show (x.1 * y.1) * (preDen x'.2 y.2 + 1)
      = (x'.1 * y.1) * (preDen x.2 y.2 + 1)
  rw [preDen_succ, preDen_succ]
  exact nnq_mul_cross x.1 x'.1 y.1 (x.2 + 1) (x'.2 + 1) (y.2 + 1) h

/-- **定理 (M267F-3b): 乗法の第二引数の well-definedness**（可換律で
    第一引数に帰着）。 -/
theorem preMul_rel_right (x : QPre) {y y' : QPre} (h : nnqRel y y') :
    nnqRel (preMul x y) (preMul x y') := by
  rw [preMul_comm x y, preMul_comm x y']
  exact preMul_rel_left h x

/-- **M267F-3c: ℚ≥0 の乗法**（二重 Quot.lift、choice-free）。 -/
def nnqMul (x y : NNQ) : NNQ :=
  Quot.lift
    (fun p => Quot.lift (fun q => Quot.mk nnqRel (preMul p q))
      (fun _ _ hq => Quot.sound (preMul_rel_right p hq)) y)
    (fun p p' hp => by
      induction y using Quot.ind
      rename_i q
      exact Quot.sound (preMul_rel_left hp q)) x

/-- **M267F-3d: ℚ≥0 の単位元** 1 = 1/1。 -/
def nnqOne : NNQ := Quot.mk nnqRel (1, 0)

/-! ## M267F-4: ℚ≥0 は乗法可換モノイド + 零吸収 -/

/-- **定理 (M267F-4a): 乗法の可換律** x·y = y·x。 -/
theorem nnqMul_comm (x y : NNQ) : nnqMul x y = nnqMul y x := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  show Quot.mk nnqRel (preMul p q) = Quot.mk nnqRel (preMul q p)
  rw [preMul_comm]

/-- **定理 (M267F-4b): 乗法の結合律** (x·y)·z = x·(y·z)。 -/
theorem nnqMul_assoc (x y z : NNQ) :
    nnqMul (nnqMul x y) z = nnqMul x (nnqMul y z) := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  induction z using Quot.ind; rename_i r
  show Quot.mk nnqRel (preMul (preMul p q) r)
      = Quot.mk nnqRel (preMul p (preMul q r))
  rw [preMul_assoc]

/-- **定理 (M267F-4c): 左単位則** 1·x = x。 -/
theorem nnqOne_mul (x : NNQ) : nnqMul nnqOne x = x := by
  induction x using Quot.ind; rename_i p
  show Quot.mk nnqRel (preMul (1, 0) p) = Quot.mk nnqRel p
  rw [preOne_mul]

/-- **定理 (M267F-4d): 右単位則** x·1 = x（可換律で左単位に帰着）。 -/
theorem nnqMul_one (x : NNQ) : nnqMul x nnqOne = x := by
  rw [nnqMul_comm]
  exact nnqOne_mul x

/-- **定理 (M267F-4e): 右零吸収** x·0 = 0（分子 a·0 = 0）。 -/
theorem nnqMul_zero (x : NNQ) : nnqMul x nnqZero = nnqZero := by
  induction x using Quot.ind; rename_i p
  apply Quot.sound
  show (p.1 * 0) * (0 + 1) = 0 * (preDen p.2 0 + 1)
  rw [Nat.mul_zero p.1, Nat.zero_mul (0 + 1), Nat.zero_mul (preDen p.2 0 + 1)]

/-- **定理 (M267F-4f): 左零吸収** 0·x = 0（可換律で右零吸収に帰着）。 -/
theorem nnqZero_mul (x : NNQ) : nnqMul nnqZero x = nnqZero := by
  rw [nnqMul_comm]
  exact nnqMul_zero x

/-! ## M267F-5: 比較射の乗法保存（本丸） -/

/-- **定理 (M267F-5): 比較射の乗法保存** — nnqToQ(x·y)
    = nnqToQ(x)·nnqToQ(y)。M67F の代表乗法（分子 ac・分母簿記 preDen p.2 q.2）を
    M115F の QRat 代表乗法 prMul（分子 ac・分母 (p.2+1)(q.2+1)）に読み替える。
    分子は `Int.natCast_mul`、分母は `preDen_succ` を Int にキャストして
    一致させ、交差積を両辺同形に潰す。M236F の加法性・M262F の順序性に
    **乗法性**を加えて比較射を順序半環準同型に完成させる。 -/
theorem nnqToQ_mul (x y : NNQ) :
    nnqToQ (nnqMul x y) = qMul (nnqToQ x) (nnqToQ y) := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  -- 分子の一致
  have hnum : ((preMul p q).1 : Int) = (p.1 : Int) * (q.1 : Int) := by
    show ((p.1 * q.1 : Nat) : Int) = (p.1 : Int) * (q.1 : Int)
    rw [Int.natCast_mul]
  -- 分母の一致（preDen_succ を Int にキャスト）
  have hden : ((preMul p q).2 : Int) + 1
      = ((p.2 : Int) + 1) * ((q.2 : Int) + 1) := by
    have h : preDen p.2 q.2 + 1 = (p.2 + 1) * (q.2 + 1) := preDen_succ p.2 q.2
    have hc : ((preDen p.2 q.2 + 1 : Nat) : Int)
        = (((p.2 + 1) * (q.2 + 1) : Nat) : Int) := by rw [h]
    rw [Int.natCast_mul] at hc
    have e1 : ((q.2 + 1 : Nat) : Int) = (q.2 : Int) + 1 := by omega
    have e2 : ((p.2 + 1 : Nat) : Int) = (p.2 : Int) + 1 := by omega
    rw [e1, e2] at hc
    have el : ((preDen p.2 q.2 + 1 : Nat) : Int)
        = ((preDen p.2 q.2 : Nat) : Int) + 1 := by omega
    rw [el] at hc
    show ((preDen p.2 q.2 : Nat) : Int) + 1 = ((p.2 : Int) + 1) * ((q.2 : Int) + 1)
    exact hc
  apply Quot.sound
  show ((preMul p q).1 : Int) * (((p.2 : Int) + 1) * ((q.2 : Int) + 1))
      = ((p.1 : Int) * (q.1 : Int)) * (((preMul p q).2 : Int) + 1)
  rw [hnum, hden]

/-! ## M267F-6: 単位元の保存 -/

/-- **定理 (M267F-6): 比較射の単位元保存** — nnqToQ(1) = 1。
    代表 (1,0)（= 1/1）を PreRat ⟨1, 0+1⟩ に送った先が ℚ の単位 prOne
    ⟨1,1⟩ と交差積 1·1 = 1·(0+1) で一致する。 -/
theorem nnqToQ_one : nnqToQ nnqOne = ratRing.one := by
  apply Quot.sound
  show ((1 : Nat) : Int) * 1 = (1 : Int) * (((0 : Nat) : Int) + 1)
  omega

/-! ## M267F-7: 乗法の順序単調性 -/

/-- **定理 (M267F-7): 乗法の順序単調性** — x ≤ y ⟹ x·c ≤ y·c。
    交差積を preDen_succ で展開し、共通因子 c の分子と分母 (r.1·(r.2+1)) を
    括り出して M262F の順序 hN に帰着する（非負錐上の順序半環の順序公理）。 -/
theorem nnqMul_mono (c : NNQ) {x y : NNQ} (h : nnqLe x y) :
    nnqLe (nnqMul x c) (nnqMul y c) := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  induction c using Quot.ind; rename_i r
  have hN : p.1 * (q.2 + 1) ≤ q.1 * (p.2 + 1) := h
  show (p.1 * r.1) * (preDen q.2 r.2 + 1) ≤ (q.1 * r.1) * (preDen p.2 r.2 + 1)
  rw [preDen_succ, preDen_succ]
  show (p.1 * r.1) * ((q.2 + 1) * (r.2 + 1))
      ≤ (q.1 * r.1) * ((p.2 + 1) * (r.2 + 1))
  have eL : (p.1 * r.1) * ((q.2 + 1) * (r.2 + 1))
      = (p.1 * (q.2 + 1)) * (r.1 * (r.2 + 1)) := by
    rw [Nat.mul_assoc p.1 r.1 ((q.2 + 1) * (r.2 + 1)),
      Nat.mul_left_comm r.1 (q.2 + 1) (r.2 + 1),
      ← Nat.mul_assoc p.1 (q.2 + 1) (r.1 * (r.2 + 1))]
  have eR : (q.1 * r.1) * ((p.2 + 1) * (r.2 + 1))
      = (q.1 * (p.2 + 1)) * (r.1 * (r.2 + 1)) := by
    rw [Nat.mul_assoc q.1 r.1 ((p.2 + 1) * (r.2 + 1)),
      Nat.mul_left_comm r.1 (p.2 + 1) (r.2 + 1),
      ← Nat.mul_assoc q.1 (p.2 + 1) (r.1 * (r.2 + 1))]
  rw [eL, eR]
  exact Nat.mul_le_mul hN (Nat.le_refl _)

/-! ## M267F-8: 順序線形性（全順序性） -/

/-- **定理 (M267F-8): 順序線形性** — nnqLe x y ∨ nnqLe y x。
    M262F が本層送りにした残件を回収。代表の交差積 a(d+1) と c(b+1) に
    Nat の全順序 `Nat.le_total` を適用するだけ。ℚ≥0 は全順序集合。 -/
theorem nnqLe_total (x y : NNQ) : nnqLe x y ∨ nnqLe y x := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  have h := Nat.le_total (p.1 * (q.2 + 1)) (q.1 * (p.2 + 1))
  cases h with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr h

/-! ## M267F-9: 総括 -/

/-- **M267F-9a: 総括** — ℚ≥0 の乗法半環（分配律を除く）と比較射 nnqToQ の
    順序半環準同型データ束。M236F の加法準同型・M262F の順序準同型に
    乗法・単位・順序線形性を統合し、実定理のみを束ねる。 -/
structure NNQMulHomData where
  /-- 乗法の可換律。 -/
  mul_comm : ∀ x y : NNQ, nnqMul x y = nnqMul y x
  /-- 乗法の結合律。 -/
  mul_assoc : ∀ x y z : NNQ, nnqMul (nnqMul x y) z = nnqMul x (nnqMul y z)
  /-- 左単位則 1·x = x。 -/
  one_mul : ∀ x : NNQ, nnqMul nnqOne x = x
  /-- 右零吸収 x·0 = 0。 -/
  mul_zero : ∀ x : NNQ, nnqMul x nnqZero = nnqZero
  /-- 比較射の乗法保存 nnqToQ(x·y) = nnqToQ(x)·nnqToQ(y)。 -/
  toQ_mul : ∀ x y : NNQ, nnqToQ (nnqMul x y) = qMul (nnqToQ x) (nnqToQ y)
  /-- 比較射の単位元保存 nnqToQ(1) = 1。 -/
  toQ_one : nnqToQ nnqOne = ratRing.one
  /-- 乗法の順序単調性 x ≤ y ⟹ x·c ≤ y·c。 -/
  mul_mono : ∀ (c : NNQ) {x y : NNQ}, nnqLe x y →
    nnqLe (nnqMul x c) (nnqMul y c)
  /-- 順序線形性（全順序性）。 -/
  le_total : ∀ x y : NNQ, nnqLe x y ∨ nnqLe y x

/-- **M267F-9b: witness**。 -/
def nnqMulHomData : NNQMulHomData where
  mul_comm := nnqMul_comm
  mul_assoc := nnqMul_assoc
  one_mul := nnqOne_mul
  mul_zero := nnqMul_zero
  toQ_mul := nnqToQ_mul
  toQ_one := nnqToQ_one
  mul_mono := nnqMul_mono
  le_total := nnqLe_total

/-- **capstone (M267F-9c): 存在** — ℚ≥0 の乗法半環構造（分配律を除く）と
    比較射 nnqToQ が順序半環準同型（零・単位・加法・乗法・順序をすべて
    保つ、加法性は M236F・順序性は M262F と合わせて）として ℚ に忠実に
    持ち上がることの単一証明記録。柱C の M236F/M262F 正直申告（乗法未定義・
    順序線形性未形式化）を本物化で回収する。 -/
theorem nnqMulHom_exists : Nonempty NNQMulHomData :=
  ⟨nnqMulHomData⟩

end IUT
