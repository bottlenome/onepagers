/-
  # M236F: 比較射 nnqToQ の準同型性（柱C・log-volume 橋の残件を 1 スライス）

  柱C（issue #37）C-1。M131F（`LogVolBridge.lean`）は比較射
  nnqToQ : ℚ≥0 → ℚ（M67F の NNQ を M115F の QRat に読む well-defined な
  Quot.lift）を導入したが、その正直申告 (3) で

    「比較射 nnqToQ が加法まで保つこと（モノイド準同型性）は本橋の
     定理には不要なため次層に回した」

  と明記していた。本層はまさにその残件——nnqToQ が**零・加法・ℕ倍
  スカラー作用を保つ**こと（可換モノイド準同型 + ℕ-作用両立）——を
  機械検証し、さらに M67F の実化次数 degR（NNQ 値）が比較射を通して
  QRat の中で加法的・Frobenius 斉次に振る舞う可換図式に持ち上げる。

  * M236F-1 `nnqToQ_zero` — **零の保存** nnqToQ(0) = 0
    （代表 (0,0) と prZero の交差積 0·1 = 0·1）
  * M236F-2 `nnqToQ_add` — **加法の保存（本丸）**
    nnqToQ(x + y) = nnqToQ(x) + nnqToQ(y)。NNQ の代表加法 preAdd
    （分子 a(d+1)+c(b+1)・分母簿記 preDen）を QRat の代表加法 prAdd
    に読み替える。分子は `Int.natCast_add`/`Int.natCast_mul`、分母は
    M67F の `preDen_succ`（(b⊕d)+1 = (b+1)(d+1)）を Int にキャストして
    一致させる（交差積が両辺同形に潰れる）。
  * M236F-3 `nnqToQ_smul` — **ℕ 倍作用の保存**
    nnqToQ(n·x) = ι_ℚ(n) · nnqToQ(x)（nnqSmul は分子を n 倍・分母不変、
    qMul (ι n) は分子を n 倍・分母を 1 倍）
  * M236F-4 `nnqToQ_degR_add` / `nnqToQ_degR_frob` — **実化次数の
    可換図式（QRat 値）**: M67F の degR_add / degR_frob を比較射
    nnqToQ で QRat へ持ち上げ、実化 log-volume 次数の加法性・Frobenius
    斉次性を QRat の言葉で言い直す
  * M236F-5 `rlogVol_realify_add` — **実数値への持ち上げ**: 実化次数を
    QRat 経由で本物の ℝ（M117F の qToReal）に読んだ値の加法性（realEq）
  * M236F-6 `NNQtoQHomData` — 総括データ束と存在

  ## 意義

  M131F の残件（正直申告 (3)）を回収し、比較射 nnqToQ が形式的な値写像
  にとどまらず**可換モノイド準同型かつ ℕ-作用両立射**であることを固定
  する。これにより M67F の実化次数（NNQ 値）と M131F の橋 qdegQ が
  「値の一致」だけでなく「代数構造（加法・スカラー）の両立」で結ばれ、
  実化 log-volume 次数の加法性・Frobenius 斉次性が QRat・ℝ の両方で
  成立することが従う。

  ## 正直な申告

  * nnqToQ の**乗法の保存（環準同型 map_mul）は扱わない**——NNQ（ℚ≥0）
    には本リポジトリで乗法を定義しておらず（M67F はモノイド + ℕ 倍
    作用のみ）、乗法構造の橋渡しは範囲外。ℕ 倍作用の保存 `nnqToQ_smul`
    が「スカラー乗法の断片」を担う。
  * ℕ 倍作用の互換は qMul (ι_ℚ n) の形で言明し、**一般の QRat スカラー
    による作用**（NNQ ⊗ ℚ 型の構造）は形式化しない。
  * degR 系 corollary は既存の degR_add / degR_frob（M67F）と本層の
    nnqToQ 準同型の**合成のみ**であり、因子の効果性順序からの単調性
    簿記（M131F 正直申告 (2)）は本層でも扱わない。
  * 全て選択公理不使用（型継承除く）。`#print axioms` で実測。
  * サブエージェント並行部品。
-/
import IUT.LogVolBridge

namespace IUT

/-! ## M236F-1: 零の保存 -/

/-- **定理 (M236F-1): 比較射は零を保つ** — nnqToQ(0) = 0。
    代表 (0,0)（= 0/1）を PreRat ⟨0, 1⟩ に送った先が ℚ の零 prZero
    ⟨0, 1⟩ と交差積 0·1 = 0·1 で一致する。 -/
theorem nnqToQ_zero : nnqToQ nnqZero = ratRing.zero := by
  apply Quot.sound
  show ((0 : Nat) : Int) * 1 = (0 : Int) * (((0 : Nat) : Int) + 1)
  omega

/-! ## M236F-2: 加法の保存（本丸） -/

/-- **定理 (M236F-2): 比較射の加法性（可換モノイド準同型）** —
    nnqToQ(x + y) = nnqToQ(x) + nnqToQ(y)。NNQ の代表加法
    （分子 a(d+1)+c(b+1)、分母簿記 preDen b d）を QRat の代表加法
    prAdd（分子 a(d+1)+c(b+1)、分母 (b+1)(d+1)）に読み替える。分子は
    `Int.natCast_add`/`Int.natCast_mul`、分母は M67F の `preDen_succ`
    を Int にキャストして一致させ、交差積を両辺同形に潰す。 -/
theorem nnqToQ_add (x y : NNQ) :
    nnqToQ (nnqAdd x y) = qAdd (nnqToQ x) (nnqToQ y) := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  have e1 : ((q.2 + 1 : Nat) : Int) = (q.2 : Int) + 1 := by omega
  have e2 : ((p.2 + 1 : Nat) : Int) = (p.2 : Int) + 1 := by omega
  -- 分子の一致
  have hnum : ((preAdd p q).1 : Int)
      = (p.1 : Int) * ((q.2 : Int) + 1) + (q.1 : Int) * ((p.2 : Int) + 1) := by
    show ((p.1 * (q.2 + 1) + q.1 * (p.2 + 1) : Nat) : Int)
        = (p.1 : Int) * ((q.2 : Int) + 1) + (q.1 : Int) * ((p.2 : Int) + 1)
    rw [Int.natCast_add, Int.natCast_mul, Int.natCast_mul, e1, e2]
  -- 分母の一致（preDen_succ を Int にキャスト）
  have hden : ((preAdd p q).2 : Int) + 1
      = ((p.2 : Int) + 1) * ((q.2 : Int) + 1) := by
    have h : preDen p.2 q.2 + 1 = (p.2 + 1) * (q.2 + 1) := preDen_succ p.2 q.2
    have hc : ((preDen p.2 q.2 + 1 : Nat) : Int)
        = (((p.2 + 1) * (q.2 + 1) : Nat) : Int) := by rw [h]
    rw [Int.natCast_mul, e1, e2] at hc
    have el : ((preDen p.2 q.2 + 1 : Nat) : Int)
        = ((preDen p.2 q.2 : Nat) : Int) + 1 := by omega
    rw [el] at hc
    show ((preDen p.2 q.2 : Nat) : Int) + 1 = ((p.2 : Int) + 1) * ((q.2 : Int) + 1)
    exact hc
  apply Quot.sound
  show ((preAdd p q).1 : Int) * (((p.2 : Int) + 1) * ((q.2 : Int) + 1))
      = ((p.1 : Int) * ((q.2 : Int) + 1) + (q.1 : Int) * ((p.2 : Int) + 1))
        * (((preAdd p q).2 : Int) + 1)
  rw [hnum, hden]

/-! ## M236F-3: ℕ 倍スカラー作用の保存 -/

/-- **定理 (M236F-3): 比較射の ℕ-作用両立** —
    nnqToQ(n·x) = ι_ℚ(n) · nnqToQ(x)。nnqSmul n は代表の分子を n 倍・
    分母不変、qMul (ι_ℚ n) は代表の分子を n 倍・分母を 1 倍するので、
    交差積 (n·a)·(1·(b+1)) = (n·a)·(b+1) で一致する。 -/
theorem nnqToQ_smul (n : Nat) (x : NNQ) :
    nnqToQ (nnqSmul n x) = qMul (ratOfInt.map (n : Int)) (nnqToQ x) := by
  induction x using Quot.ind; rename_i p
  apply Quot.sound
  show ((n * p.1 : Nat) : Int) * (1 * ((p.2 : Int) + 1))
      = (n : Int) * (p.1 : Int) * ((p.2 : Int) + 1)
  rw [Int.natCast_mul, Int.one_mul]

/-! ## M236F-4: 実化次数の可換図式（QRat 値） -/

/-- **定理 (M236F-4a): 実化 log-volume 次数の加法性（QRat 値）** —
    nnqToQ(deg_R(x + y)) = nnqToQ(deg_R x) + nnqToQ(deg_R y)。M67F の
    degR_add を比較射 nnqToQ で QRat へ持ち上げる。 -/
theorem nnqToQ_degR_add (w : Nat → Nat) (x y : RDiv) :
    nnqToQ (degR w (radd x y))
      = qAdd (nnqToQ (degR w x)) (nnqToQ (degR w y)) := by
  rw [degR_add]
  exact nnqToQ_add (degR w x) (degR w y)

/-- **定理 (M236F-4b): 実化 log-volume 次数の Frobenius 斉次性（QRat 値）** —
    nnqToQ(deg_R(φ_e x)) = ι_ℚ(e) · nnqToQ(deg_R x)。M67F の degR_frob を
    比較射 nnqToQ で QRat へ持ち上げる。 -/
theorem nnqToQ_degR_frob (w : Nat → Nat) (e : Nat) (x : RDiv) :
    nnqToQ (degR w (rfrobN e x))
      = qMul (ratOfInt.map (e : Int)) (nnqToQ (degR w x)) := by
  rw [degR_frob]
  exact nnqToQ_smul e (degR w x)

/-! ## M236F-5: 実数値への持ち上げ -/

/-- **定理 (M236F-5): 実化 log-volume 次数の実数値加法性** —
    実化次数を比較射 nnqToQ で QRat に読み、さらに M117F の qToReal で
    本物の ℝ に読んだ値は加法的（realEq）: vol_ℝ(x + y) ≈ vol_ℝ(x)
    + vol_ℝ(y)。M236F-4a と qToReal_add の合成。 -/
theorem rlogVol_realify_add (w : Nat → Nat) (x y : RDiv) :
    realEq (qToReal (nnqToQ (degR w (radd x y))))
      (realAdd (qToReal (nnqToQ (degR w x)))
        (qToReal (nnqToQ (degR w y)))) := by
  rw [nnqToQ_degR_add]
  exact realEq_symm
    (qToReal_add (nnqToQ (degR w x)) (nnqToQ (degR w y)))

/-! ## M236F-6: 総括 -/

/-- **M236F-6a: 総括** — 比較射 nnqToQ の準同型性データ束。M131F の
    残件（正直申告 (3)）を回収し、nnqToQ が零・加法・ℕ 倍作用を保つ
    可換モノイド準同型（+ ℕ-作用両立）であること、および M67F の実化
    次数がそれを通して QRat の中で加法的・Frobenius 斉次に振る舞う
    ことの実定理のみを束ねる。 -/
structure NNQtoQHomData where
  /-- 零の保存: nnqToQ(0) = 0。 -/
  map_zero : nnqToQ nnqZero = ratRing.zero
  /-- 加法の保存: nnqToQ(x + y) = nnqToQ(x) + nnqToQ(y)。 -/
  map_add : ∀ x y : NNQ, nnqToQ (nnqAdd x y) = qAdd (nnqToQ x) (nnqToQ y)
  /-- ℕ-作用の保存: nnqToQ(n·x) = ι_ℚ(n) · nnqToQ(x)。 -/
  map_smul : ∀ (n : Nat) (x : NNQ),
    nnqToQ (nnqSmul n x) = qMul (ratOfInt.map (n : Int)) (nnqToQ x)
  /-- 実化次数の加法性（QRat 値）。 -/
  degR_add : ∀ (w : Nat → Nat) (x y : RDiv),
    nnqToQ (degR w (radd x y))
      = qAdd (nnqToQ (degR w x)) (nnqToQ (degR w y))
  /-- 実化次数の Frobenius 斉次性（QRat 値）。 -/
  degR_frob : ∀ (w : Nat → Nat) (e : Nat) (x : RDiv),
    nnqToQ (degR w (rfrobN e x))
      = qMul (ratOfInt.map (e : Int)) (nnqToQ (degR w x))

/-- **M236F-6b: witness**。 -/
def nnqToQHomData : NNQtoQHomData where
  map_zero := nnqToQ_zero
  map_add := nnqToQ_add
  map_smul := nnqToQ_smul
  degR_add := nnqToQ_degR_add
  degR_frob := nnqToQ_degR_frob

/-- **M236F-6c: 存在** — 比較射 nnqToQ の準同型性データが無矛盾に存在。 -/
theorem nnqToQHom_exists : Nonempty NNQtoQHomData :=
  ⟨nnqToQHomData⟩

end IUT
