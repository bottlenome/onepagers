/-
  IUT/Realification.lean — M67F（realification 実化と可除性）の形式化

  ## 動機

  [FrdI] の **realified Frobenioid** F^rlf は、因子モノイド Φ を実係数
  Φ^rlf = Φ ⊗ ℝ≥0 に拡張したものであり、M48F/M51F/M57F〜M65F の
  Frobenioid 系譜が一貫して「realification は未形式化」と申告してきた
  残り項目である。realification の数学的本質は係数が連続体になること
  そのものではなく、**可除性（divisibility）の獲得**にある: 整係数の
  有効因子は n 等分できない（重複度 1 の因子の半分は因子でない）が、
  実化因子は任意の n ≥ 1 で n 等分できる。IUT 本体で多用される
  「q-パイロット対象の 1/2ℓ 等分」「テータ・パイロットの分数冪」型の
  操作（[IUTchIII] の log-volume 計算における分数係数の因子算術）は
  全てこの可除性を土台にしている。

  本モジュールは mathlib なし（core のみ）の制約下で、ℝ の代わりに
  **非負有理数 ℚ≥0 を Quot で自前構成**し（可除性の獲得には可算な
  ℚ≥0 で十分——「実化」の名で ℚ≥0 を使う正規化は正直な申告に記載）、
  実化因子モノイド RDiv・実化次数 degR・実化 Frobenioid 圏
  realFrobenioid・実化関手 realifyFunctor を建設して、可除性定理を
  両側（実化側は可除・整係数側は不可除の具体的反例）で機械検証する。

  ## ℚ≥0 の構成と well-definedness の紙上検証

  生の対 QPre = ℕ × ℕ で (a, b) を a/(b+1) と読む（分母 b+1 で正値を
  型で保証し subtype を回避）。同値関係は交差積
  qrel (a,b) (c,d) ⟺ a(d+1) = c(b+1)、NNQ = Quot qrel。
  加法は (a,b) + (c,d) = (a(d+1) + c(b+1), bd + b + d)
  （分母簿記: (bd+b+d) + 1 = (b+1)(d+1)）。

  **加法の well-definedness の交差積恒等式**（実装前に紙上検証済み）:
  B = b+1, B' = b'+1, D = d+1 と置き、仮定 aB' = a'B の下で
    (aD + cB)(B'D) = aB'·D² + cBB'D = a'B·D² + cBB'D = (a'D + cB')(BD)。
  var×var の積が多発するため omega は使えず（規約3）、この恒等式を
  自由変数の補題 `nnq_cross` に切り出して mul_assoc / mul_left_comm /
  mul_right_comm の rw 連鎖で証明する。結合則は正規化せず**両辺の代表の
  閉形式を直接比較**する方針: 分子恒等式 (aD+cB)F + e(BD) =
  a(DF) + (cF+eD)B（`nnq_num_assoc`）と分母簿記の結合律
  （succ 持ち上げ (b⊕d)+1 = (b+1)(d+1) と mul_assoc、`preDen_assoc`）の
  二本の Nat 恒等式で、商を取る前の**対の等式**として成立する。
  可除性の核は (a,b)/n = (a, (b+1)n − 1)（分母 n 倍）で、
  n·((a,b)/n) = (a,b) の検証は交差積 na(b+1) = a((b+1)n) 一本。

  ## 検証する定理（全て sorry なし・選択公理なし）

  ### Part 0–1: ℚ≥0 の商構成と可除性
  * M67F-1 `NNQ` / `nnqAdd` / `nnqZero` / `nnqSmul` / `nnqOfNat` —
    商構成と well-defined な演算、可換モノイド法則
    （`nnqAdd_assoc` / `nnqAdd_comm` / `nnqZero_add`）、
    埋め込みの加法性 `nnqOfNat_add`: ι(m+n) = ι m + ι n
  * M67F-2 `nnqDiv` / `nnq_div_cancel` — **n 等分と可除性の核**
    n·(x/n) = x（Quot.lift の関数を直接定義: choice-free）

  ### Part 2–3: 実化因子モノイドと実化準同型
  * M67F-3 `RDiv` / `radd` / `rzero` / `rfrobN` — 実化因子
    （ℚ≥0 値重複度の有限サポート関数）とモノイド法則・
    Frobenius 法則（`rfrob_add` / `rfrob_frob`、QDiv の証明の踏襲）
  * M67F-4 `realify` — **実化準同型** QDiv → RDiv（成分ごとの ι）。
    加法性 `realify_add`・Frobenius 両立 `realify_frob`
  * M67F-4c–e `degR` — **実化次数**（ℚ≥0 値の重み付き次数）:
    加法性 `degR_add`・斉次性 `degR_frob`・**次数の可換図式**
    `degR_realify`: deg_R(realify x) = ι(deg_N x)

  ### Part 4: 可除性定理（本丸）
  * M67F-5a `rdiv_divisible` — **実化因子は任意の n ≥ 1 で可除**:
    ∀ x n ≥ 1, ∃ y, φ_n(y) = x（witness `rdivPart` は成分ごとの
    nnqDiv の明示構成: ∃ だが choice-free）
  * M67F-5b `qdiv_not_divisible` — **整係数側の不可除性**:
    単一素点重複度 1 の因子（M51F の singleDiv 0 1）は 2 等分
    できない（成分の方程式 2m = 1 の ℕ での矛盾）
  * M67F-5c `realification_gains_divisibility` — **「実化の本質 =
    可除性の獲得」の両側機械検証**（反例自身も実化すれば可除になる）
  * M67F-5d `real_pilot_division` — 圏レベルの等分: 任意の対象 x と
    n ≥ 1 に「x の 1/n」対象と次数 n の純 Frobenius 射 y → x が実在

  ### Part 5: 実化 Frobenioid 圏と実化関手
  * M67F-6a `realFrobenioid` — 対象 = RDiv、射 = (d ≥ 1, c) with
    y = φ_d(x) + c の圏公理完全証明（divisorFrobenioid の踏襲）
  * M67F-6b `realifyFunctor` — **実化関手** divisorFrobenioid →
    realFrobenioid（対象 = realify、射 = (d, realify c)）の関手性
    （[FrdI] の F → F^rlf の base 一点・因子モノイドレベルの実装）

  ### Part 6: 剛性
  * M67F-7 `real_iso_objects_eq` / `real_gaunt_isoUnique` —
    実化圏も gaunt + IsoUnique（M53F の剛性述語の充足）。
    **可除性（φ_n の対象レベル全射性）を獲得しても Frobenius-like
    剛性は壊れない**: 同型なら次数の積 = 1 が必要で、n 等分の
    witness は同型を与えない

  ## 正直な申告（モデルと本物の差）

  * **ℝ でなく ℚ≥0**: [FrdI] の realification は ℝ≥0 係数（順序完備）
    だが、本モジュールは ℚ≥0 で代用した。可除性（本モジュールが
    機械検証する本質）には ℚ≥0 で十分だが、ℝ≥0 が担う上限の存在
    （順序完備性）・連続性は形式化されていない。
  * **順序構造は未形式化**: ℚ≥0 上の ≤（および因子の効果性の順序）は
    定義しておらず、[FrdI] §2 の「上限・下限による realified 次数の
    特徴付け」は扱わない。次数は重み簿記（加法性・斉次性・実化との
    可換図式）のみで、log-volume の実数値理論は未形式化。
  * **アルキメデス素点なし**: 素点は M51F と同じ添字 k : ℕ の
    非アルキメデス型簿記のみ。
  * **サポート上界はデータ**: QDiv と同様、RDiv も choice 回避のため
    上界をデータとして持つ。このため mult が同じで bound が違う
    RDiv は別対象である（M51F 以来の表示の自由度の正直な申告）。
  * 選択公理・追加公理は不使用（全定理 propext / Quot.sound 以下、
    `#print axioms` で実測済み。Quot.lift の関数は全て直接定義し、
    ∃ の witness は全て明示構成）。
-/
import IUT.PolyIsomorphism

namespace IUT

/-! ## Part 0: 非負有理数 ℚ≥0 の自前構成（mathlib なし・Quot による商） -/

/-- 生の対: (a, b) は有理数 a/(b+1) を表す（分母を b+1 にして
    正値性を型で保証し、subtype を回避する）。 -/
def QPre : Type := Nat × Nat

/-- 同値関係（交差積）: a/(b+1) = c/(d+1) ⟺ a(d+1) = c(b+1)。 -/
def nnqRel (x y : QPre) : Prop :=
  x.1 * (y.2 + 1) = y.1 * (x.2 + 1)

/-- **非負有理数 ℚ≥0**（商型）。 -/
def NNQ : Type := Quot nnqRel

/-- 対の外延性（Prod の成分一致 ⟹ 等しい）。 -/
theorem qpre_ext {x y : QPre} (h1 : x.1 = y.1) (h2 : x.2 = y.2) :
    x = y := by
  cases x with | mk a b =>
  cases y with | mk c d =>
  have h1' : a = c := h1
  have h2' : b = d := h2
  subst h1'
  subst h2'
  rfl

/-- 和の分母簿記: b ⊕ d = bd + b + d（(b⊕d)+1 = (b+1)(d+1) となる値）。 -/
def preDen (b d : Nat) : Nat := b * d + b + d

/-- 分母簿記の核恒等式: preDen b d + 1 = (b+1)(d+1)。 -/
theorem preDen_succ (b d : Nat) : preDen b d + 1 = (b + 1) * (d + 1) := by
  show b * d + b + d + 1 = (b + 1) * (d + 1)
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]

/-- 和の分子: a/(b+1) + c/(d+1) の分子 a(d+1) + c(b+1)。 -/
def preNum (x y : QPre) : Nat :=
  x.1 * (y.2 + 1) + y.1 * (x.2 + 1)

/-- 代表レベルの加法: (a,b) + (c,d) = (a(d+1) + c(b+1), bd + b + d)。 -/
def preAdd (x y : QPre) : QPre :=
  (preNum x y, preDen x.2 y.2)

/-- **加法の well-definedness の交差積恒等式**（紙上検証済みの核）:
    a·B' = a'·B ならば (aD + cB)(B'D) = (a'D + cB')(BD)。
    var×var の積が多発するため omega 不可（規約3）——
    mul_assoc / mul_left_comm / mul_right_comm の rw 連鎖で処理する。 -/
theorem nnq_cross (a a' c B B' D : Nat) (h : a * B' = a' * B) :
    (a * D + c * B) * (B' * D) = (a' * D + c * B') * (B * D) := by
  have e1 : a * D * (B' * D) = a * B' * (D * D) := by
    rw [Nat.mul_assoc, Nat.mul_left_comm D B' D, ← Nat.mul_assoc]
  have e2 : c * B * (B' * D) = c * B' * (B * D) := by
    rw [Nat.mul_assoc, Nat.mul_left_comm B B' D, ← Nat.mul_assoc]
  have e3 : a' * D * (B * D) = a' * B * (D * D) := by
    rw [Nat.mul_assoc, Nat.mul_left_comm D B D, ← Nat.mul_assoc]
  rw [Nat.add_mul, Nat.add_mul, e1, e2, e3, h]

/-- **加法の第一引数の well-definedness**: x ~ x' ⟹ x + y ~ x' + y。 -/
theorem preAdd_rel_left {x x' : QPre} (h : nnqRel x x') (y : QPre) :
    nnqRel (preAdd x y) (preAdd x' y) := by
  show preNum x y * (preDen x'.2 y.2 + 1)
      = preNum x' y * (preDen x.2 y.2 + 1)
  rw [preDen_succ, preDen_succ]
  exact nnq_cross x.1 x'.1 y.1 (x.2 + 1) (x'.2 + 1) (y.2 + 1) h

/-- 代表レベルの加法の可換律（対の等式として成立）。 -/
theorem preAdd_comm (x y : QPre) : preAdd x y = preAdd y x := by
  apply qpre_ext
  · show x.1 * (y.2 + 1) + y.1 * (x.2 + 1)
        = y.1 * (x.2 + 1) + x.1 * (y.2 + 1)
    exact Nat.add_comm _ _
  · show x.2 * y.2 + x.2 + y.2 = y.2 * x.2 + y.2 + x.2
    rw [Nat.mul_comm x.2 y.2, Nat.add_right_comm]

/-- **加法の第二引数の well-definedness**（可換律で第一引数に帰着）。 -/
theorem preAdd_rel_right (x : QPre) {y y' : QPre} (h : nnqRel y y') :
    nnqRel (preAdd x y) (preAdd x y') := by
  rw [preAdd_comm x y, preAdd_comm x y']
  exact preAdd_rel_left h x

/-- ℚ≥0 の加法（二重 Quot.lift、IUT/Profinite.lean の quotMul の流儀）。 -/
def nnqAdd (x y : NNQ) : NNQ :=
  Quot.lift
    (fun p => Quot.lift (fun q => Quot.mk nnqRel (preAdd p q))
      (fun _ _ hq => Quot.sound (preAdd_rel_right p hq)) y)
    (fun p p' hp => by
      induction y using Quot.ind
      rename_i q
      exact Quot.sound (preAdd_rel_left hp q)) x

/-- ℚ≥0 の零元 0 = 0/1。 -/
def nnqZero : NNQ := Quot.mk nnqRel (0, 0)

/-- ℕ 倍スカラー（well-defined: 交差積の両辺を n 倍するだけ）。 -/
def nnqSmul (n : Nat) (x : NNQ) : NNQ :=
  Quot.lift (fun p => Quot.mk nnqRel (n * p.1, p.2))
    (fun p p' h => Quot.sound (by
      show n * p.1 * (p'.2 + 1) = n * p'.1 * (p.2 + 1)
      rw [Nat.mul_assoc, Nat.mul_assoc, h])) x

/-- ℕ → ℚ≥0 の埋め込み ι n = n/1。 -/
def nnqOfNat (n : Nat) : NNQ := Quot.mk nnqRel (n, 0)

/-! ### ℚ≥0 の可換モノイド法則 -/

/-- 結合則の分子恒等式（代表の閉形式を直接比較する Nat 恒等式）:
    (aD + cB)F + e(BD) = a(DF) + (cF + eD)B。 -/
theorem nnq_num_assoc (a c e B D F : Nat) :
    (a * D + c * B) * F + e * (B * D)
      = a * (D * F) + (c * F + e * D) * B := by
  rw [Nat.add_mul (a * D) (c * B) F, Nat.add_mul (c * F) (e * D) B,
    ← Nat.mul_assoc e B D, ← Nat.mul_assoc a D F,
    Nat.mul_right_comm c B F, Nat.mul_right_comm e B D, Nat.add_assoc]

/-- 分母簿記の結合律: (b ⊕ d) ⊕ f = b ⊕ (d ⊕ f)
    （+1 して (b+1)(d+1)(f+1) の結合律に持ち上げ、succ 単射で落とす）。 -/
theorem preDen_assoc (b d f : Nat) :
    preDen (preDen b d) f = preDen b (preDen d f) := by
  have h : preDen (preDen b d) f + 1 = preDen b (preDen d f) + 1 := by
    rw [preDen_succ, preDen_succ, preDen_succ, preDen_succ, Nat.mul_assoc]
  exact Nat.add_right_cancel h

/-- 代表レベルの加法の結合律（対の等式として成立）。 -/
theorem preAdd_assoc (p q r : QPre) :
    preAdd (preAdd p q) r = preAdd p (preAdd q r) := by
  apply qpre_ext
  · show preNum p q * (r.2 + 1) + r.1 * (preDen p.2 q.2 + 1)
        = p.1 * (preDen q.2 r.2 + 1) + preNum q r * (p.2 + 1)
    rw [preDen_succ, preDen_succ]
    exact nnq_num_assoc p.1 q.1 r.1 (p.2 + 1) (q.2 + 1) (r.2 + 1)
  · exact preDen_assoc p.2 q.2 r.2

/-- 代表レベルの左単位則: (0,0) + y = y（対の等式として成立）。 -/
theorem preZero_add (y : QPre) : preAdd (0, 0) y = y := by
  apply qpre_ext
  · show 0 * (y.2 + 1) + y.1 * (0 + 1) = y.1
    rw [Nat.zero_mul, Nat.zero_add, Nat.mul_one]
  · show 0 * y.2 + 0 + y.2 = y.2
    rw [Nat.zero_mul, Nat.add_zero, Nat.zero_add]

/-- **定理 (M67F-1a): ℚ≥0 の加法の結合律**。 -/
theorem nnqAdd_assoc (x y z : NNQ) :
    nnqAdd (nnqAdd x y) z = nnqAdd x (nnqAdd y z) := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  induction z using Quot.ind; rename_i r
  show Quot.mk nnqRel (preAdd (preAdd p q) r)
      = Quot.mk nnqRel (preAdd p (preAdd q r))
  rw [preAdd_assoc]

/-- **定理 (M67F-1b): ℚ≥0 の加法の可換律**。 -/
theorem nnqAdd_comm (x y : NNQ) : nnqAdd x y = nnqAdd y x := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  show Quot.mk nnqRel (preAdd p q) = Quot.mk nnqRel (preAdd q p)
  rw [preAdd_comm]

/-- **定理 (M67F-1c): 左単位則** 0 + x = x。 -/
theorem nnqZero_add (x : NNQ) : nnqAdd nnqZero x = x := by
  induction x using Quot.ind; rename_i q
  show Quot.mk nnqRel (preAdd (0, 0) q) = Quot.mk nnqRel q
  rw [preZero_add]

/-- **定理 (M67F-1c'): 右単位則** x + 0 = x。 -/
theorem nnqAdd_zero (x : NNQ) : nnqAdd x nnqZero = x := by
  rw [nnqAdd_comm]
  exact nnqZero_add x

/-- **定理 (M67F-1d): 埋め込みの加法性** ι(m+n) = ι m + ι n。 -/
theorem nnqOfNat_add (m n : Nat) :
    nnqOfNat (m + n) = nnqAdd (nnqOfNat m) (nnqOfNat n) := by
  show Quot.mk nnqRel (m + n, 0) = Quot.mk nnqRel (preAdd (m, 0) (n, 0))
  have h : preAdd ((m, 0) : QPre) ((n, 0) : QPre) = ((m + n, 0) : QPre) := by
    apply qpre_ext
    · show m * (0 + 1) + n * (0 + 1) = m + n
      rw [Nat.mul_one, Nat.mul_one]
    · rfl
  rw [h]

/-- ι 0 = 0（定義から直ちに）。 -/
theorem nnqOfNat_zero : nnqOfNat 0 = nnqZero := rfl

/-! ### ℕ 倍スカラーの法則 -/

/-- スカラーの加法分配: n·(x + y) = n·x + n·y。 -/
theorem nnqSmul_add (n : Nat) (x y : NNQ) :
    nnqSmul n (nnqAdd x y) = nnqAdd (nnqSmul n x) (nnqSmul n y) := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  show Quot.mk nnqRel (n * preNum p q, preDen p.2 q.2)
      = Quot.mk nnqRel (preAdd (n * p.1, p.2) (n * q.1, q.2))
  have h : ((n * preNum p q, preDen p.2 q.2) : QPre)
      = preAdd (n * p.1, p.2) (n * q.1, q.2) := by
    apply qpre_ext
    · show n * (p.1 * (q.2 + 1) + q.1 * (p.2 + 1))
          = n * p.1 * (q.2 + 1) + n * q.1 * (p.2 + 1)
      rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc]
    · rfl
  rw [h]

/-- スカラーの合成: e₂·(e₁·x) = (e₁e₂)·x。 -/
theorem nnqSmul_smul (e₁ e₂ : Nat) (x : NNQ) :
    nnqSmul e₂ (nnqSmul e₁ x) = nnqSmul (e₁ * e₂) x := by
  induction x using Quot.ind; rename_i p
  show Quot.mk nnqRel (e₂ * (e₁ * p.1), p.2)
      = Quot.mk nnqRel (e₁ * e₂ * p.1, p.2)
  have h : e₂ * (e₁ * p.1) = e₁ * e₂ * p.1 := by
    rw [← Nat.mul_assoc, Nat.mul_comm e₂ e₁]
  rw [h]

/-- 1 倍は恒等。 -/
theorem nnqSmul_one (x : NNQ) : nnqSmul 1 x = x := by
  induction x using Quot.ind; rename_i p
  show Quot.mk nnqRel (1 * p.1, p.2) = Quot.mk nnqRel (p.1, p.2)
  rw [Nat.one_mul]

/-- スカラーは 0 を固定する。 -/
theorem nnqSmul_zero (n : Nat) : nnqSmul n nnqZero = nnqZero := by
  show Quot.mk nnqRel (n * 0, 0) = Quot.mk nnqRel (0, 0)
  rw [Nat.mul_zero]

/-- スカラーと埋め込みの両立: n·(ι m) = ι(n·m)（定義から rfl）。 -/
theorem nnqSmul_ofNat (n m : Nat) :
    nnqSmul n (nnqOfNat m) = nnqOfNat (n * m) := rfl

/-! ## Part 1: 可除性（ℚ≥0 レベル、M67F-2） -/

/-- m ≥ 1 なら (m-1)+1 = m（変数 m に generalize してから omega:
    積 (b+1)·n は外で作る——規約3）。 -/
theorem sub_one_add_one {m : Nat} (h : 1 ≤ m) : m - 1 + 1 = m := by
  omega

/-- 分母 n 倍の +1 簿記: ((b+1)n − 1) + 1 = (b+1)n（n ≥ 1）。 -/
theorem div_den_succ (b n : Nat) (hn : 1 ≤ n) :
    (b + 1) * n - 1 + 1 = (b + 1) * n :=
  sub_one_add_one (Nat.mul_pos (Nat.succ_pos b) hn)

/-- **n 等分**（choice-free）: (a, b)/n = (a, (b+1)n − 1)（分母を n 倍）。
    well-definedness は交差積の両辺の結合律一本。 -/
def nnqDiv (x : NNQ) (n : Nat) (hn : 1 ≤ n) : NNQ :=
  Quot.lift (fun p => Quot.mk nnqRel (p.1, (p.2 + 1) * n - 1))
    (fun p p' h => Quot.sound (by
      show p.1 * ((p'.2 + 1) * n - 1 + 1) = p'.1 * ((p.2 + 1) * n - 1 + 1)
      rw [div_den_succ p'.2 n hn, div_den_succ p.2 n hn,
        ← Nat.mul_assoc, ← Nat.mul_assoc, h])) x

/-- **定理 (M67F-2): 可除性の核** — n·(x/n) = x。
    交差積 (n·a)(b+1) = a((b+1)n) の可換・結合律一本で検証される。 -/
theorem nnq_div_cancel (x : NNQ) (n : Nat) (hn : 1 ≤ n) :
    nnqSmul n (nnqDiv x n hn) = x := by
  induction x using Quot.ind; rename_i p
  apply Quot.sound
  show n * p.1 * (p.2 + 1) = p.1 * ((p.2 + 1) * n - 1 + 1)
  rw [div_den_succ p.2 n hn, Nat.mul_comm n p.1,
    Nat.mul_assoc p.1 n (p.2 + 1), Nat.mul_comm n (p.2 + 1)]

/-- 0 の n 等分は 0（0/1 = 0/n の交差積）。 -/
theorem nnqDiv_zero (n : Nat) (hn : 1 ≤ n) :
    nnqDiv nnqZero n hn = nnqZero := by
  apply Quot.sound
  show 0 * (0 + 1) = 0 * ((0 + 1) * n - 1 + 1)
  rw [Nat.zero_mul, Nat.zero_mul]

/-! ## Part 2: 実化因子モノイド RDiv（M67F-3） -/

/-- **実化因子**: 素点ごとの重複度を ℚ≥0 に拡張した有限サポート関数
    （QDiv の ℚ≥0 係数版。サポート上界はデータとして持つ——choice 回避）。 -/
structure RDiv where
  /-- k 番目の素点での ℚ≥0 値重複度。 -/
  mult : Nat → NNQ
  /-- サポートの上界。 -/
  bound : Nat
  /-- 有限サポート性。 -/
  vanish : ∀ k, bound ≤ k → mult k = nnqZero

/-- 実化因子の外延性（vanish は Prop）。 -/
theorem RDiv.ext {x y : RDiv} (hm : x.mult = y.mult)
    (hb : x.bound = y.bound) : x = y := by
  cases x with | mk xm xb xv =>
  cases y with | mk ym yb yv =>
  have hm' : xm = ym := hm
  have hb' : xb = yb := hb
  subst hm'
  subst hb'
  rfl

/-- 自明実化因子 0。 -/
def rzero : RDiv where
  mult := fun _ => nnqZero
  bound := 0
  vanish := fun _ _ => rfl

/-- 実化因子の和（点ごとの ℚ≥0 加法、上界は max）。 -/
def radd (x y : RDiv) : RDiv where
  mult := fun k => nnqAdd (x.mult k) (y.mult k)
  bound := max x.bound y.bound
  vanish := fun k hk => by
    rw [x.vanish k (Nat.le_trans (Nat.le_max_left _ _) hk),
      y.vanish k (Nat.le_trans (Nat.le_max_right _ _) hk)]
    exact nnqAdd_zero nnqZero

/-- ℕ 倍 Frobenius φ_e: ℚ≥0 値重複度の点ごと e 倍。 -/
def rfrobN (e : Nat) (x : RDiv) : RDiv where
  mult := fun k => nnqSmul e (x.mult k)
  bound := x.bound
  vanish := fun k hk => by
    rw [x.vanish k hk]
    exact nnqSmul_zero e

/-- **定理 (M67F-3a): 実化因子和の結合律**。 -/
theorem radd_assoc (x y z : RDiv) :
    radd (radd x y) z = radd x (radd y z) :=
  RDiv.ext (funext fun k => nnqAdd_assoc (x.mult k) (y.mult k) (z.mult k))
    (nat_max_assoc x.bound y.bound z.bound)

/-- **定理 (M67F-3b): 実化因子和の可換律**。 -/
theorem radd_comm (x y : RDiv) : radd x y = radd y x :=
  RDiv.ext (funext fun k => nnqAdd_comm (x.mult k) (y.mult k))
    (nat_max_comm x.bound y.bound)

/-- **定理 (M67F-3c): 左単位則** 0 + x = x。 -/
theorem rzero_add (x : RDiv) : radd rzero x = x :=
  RDiv.ext (funext fun k => nnqZero_add (x.mult k)) (nat_zero_max x.bound)

/-- **定理 (M67F-3c'): 右単位則** x + 0 = x。 -/
theorem radd_zero (x : RDiv) : radd x rzero = x :=
  RDiv.ext (funext fun k => nnqAdd_zero (x.mult k)) (nat_max_zero x.bound)

/-- φ_1 は恒等。 -/
theorem rfrob_one (x : RDiv) : rfrobN 1 x = x :=
  RDiv.ext (funext fun k => nnqSmul_one (x.mult k)) rfl

/-- φ_e は自明因子を固定する。 -/
theorem rfrob_zero (e : Nat) : rfrobN e rzero = rzero :=
  RDiv.ext (funext fun _ => nnqSmul_zero e) rfl

/-- **Frobenius の加法分配**: φ_e(x + y) = φ_e(x) + φ_e(y)。 -/
theorem rfrob_add (e : Nat) (x y : RDiv) :
    rfrobN e (radd x y) = radd (rfrobN e x) (rfrobN e y) :=
  RDiv.ext (funext fun k => nnqSmul_add e (x.mult k) (y.mult k)) rfl

/-- **Frobenius の合成**: φ_{e₂}(φ_{e₁}(x)) = φ_{e₁e₂}(x)。 -/
theorem rfrob_frob (e₁ e₂ : Nat) (x : RDiv) :
    rfrobN e₂ (rfrobN e₁ x) = rfrobN (e₁ * e₂) x :=
  RDiv.ext (funext fun k => nnqSmul_smul e₁ e₂ (x.mult k)) rfl

/-! ## Part 3: 実化準同型 realify（M67F-4） -/

/-- **実化準同型**: 整係数因子 QDiv → 実化因子 RDiv（成分ごとの ι）。
    [FrdI] の Φ → Φ^rlf の単射部分のモデル。 -/
def realify (x : QDiv) : RDiv where
  mult := fun k => nnqOfNat (x.mult k)
  bound := x.bound
  vanish := fun k hk => by
    rw [x.vanish k hk]
    exact nnqOfNat_zero

/-- **定理 (M67F-4a): realify の加法性** realify(x + y) = realify x + realify y。 -/
theorem realify_add (x y : QDiv) :
    realify (qadd x y) = radd (realify x) (realify y) :=
  RDiv.ext (funext fun k => nnqOfNat_add (x.mult k) (y.mult k)) rfl

/-- **定理 (M67F-4b): realify と Frobenius の両立**
    realify(φ_e x) = φ_e(realify x)（代表レベルで rfl）。 -/
theorem realify_frob (e : Nat) (x : QDiv) :
    realify (qfrob e x) = rfrobN e (realify x) :=
  RDiv.ext (funext fun _ => rfl) rfl

/-- realify は 0 を 0 に送る。 -/
theorem realify_zero : realify qzero = rzero :=
  RDiv.ext (funext fun _ => rfl) rfl

/-! ### 実化次数（NNQ 値の重み付き次数、M67F-4c） -/

/-- ℚ≥0 値の有限和 Σ_{k<n} g k。 -/
def nnqSum (g : Nat → NNQ) : Nat → NNQ
  | 0 => nnqZero
  | n + 1 => nnqAdd (nnqSum g n) (g n)

/-- ℚ≥0 の和の入れ替え (a+b)+(c+d) = (a+c)+(b+d)
    （結合・可換から導出——omega の代わりの手作業版）。 -/
theorem nnqAdd_shuffle (a b c d : NNQ) :
    nnqAdd (nnqAdd a b) (nnqAdd c d) = nnqAdd (nnqAdd a c) (nnqAdd b d) := by
  rw [nnqAdd_assoc a b (nnqAdd c d), ← nnqAdd_assoc b c d,
    nnqAdd_comm b c, nnqAdd_assoc c b d, ← nnqAdd_assoc a c (nnqAdd b d)]

/-- 尾部切り落とし: g が a 以降で消滅するなら Σ_{k<n} = Σ_{k<a}。 -/
theorem nnqSum_tail (g : Nat → NNQ) (a n : Nat) (ha : a ≤ n)
    (h : ∀ k, a ≤ k → g k = nnqZero) : nnqSum g n = nnqSum g a := by
  induction n with
  | zero =>
    have h0 : a = 0 := Nat.le_zero.mp ha
    rw [h0]
  | succ m ih =>
    cases Nat.eq_or_lt_of_le ha with
    | inl h1 => rw [h1]
    | inr h2 =>
      have ha' : a ≤ m := by omega
      show nnqAdd (nnqSum g m) (g m) = nnqSum g a
      rw [h m ha', ih ha', nnqAdd_zero]

/-- ℚ≥0 値和の加法性。 -/
theorem nnqSum_add (g h : Nat → NNQ) (n : Nat) :
    nnqSum (fun k => nnqAdd (g k) (h k)) n
      = nnqAdd (nnqSum g n) (nnqSum h n) := by
  induction n with
  | zero => exact (nnqZero_add nnqZero).symm
  | succ j ih =>
    show nnqAdd (nnqSum (fun k => nnqAdd (g k) (h k)) j) (nnqAdd (g j) (h j))
        = nnqAdd (nnqAdd (nnqSum g j) (g j)) (nnqAdd (nnqSum h j) (h j))
    rw [ih]
    exact nnqAdd_shuffle (nnqSum g j) (nnqSum h j) (g j) (h j)

/-- ℚ≥0 値和とスカラーの両立 Σ e·g = e·Σ g。 -/
theorem nnqSum_smul (e : Nat) (g : Nat → NNQ) (n : Nat) :
    nnqSum (fun k => nnqSmul e (g k)) n = nnqSmul e (nnqSum g n) := by
  induction n with
  | zero => exact (nnqSmul_zero e).symm
  | succ j ih =>
    show nnqAdd (nnqSum (fun k => nnqSmul e (g k)) j) (nnqSmul e (g j))
        = nnqSmul e (nnqAdd (nnqSum g j) (g j))
    rw [ih, nnqSmul_add]

/-- ℚ≥0 値和と埋め込みの両立 Σ ι(g k) = ι(Σ g k)。 -/
theorem nnqSum_ofNat (g : Nat → Nat) (n : Nat) :
    nnqSum (fun k => nnqOfNat (g k)) n = nnqOfNat (nsum g n) := by
  induction n with
  | zero => rfl
  | succ j ih =>
    show nnqAdd (nnqSum (fun k => nnqOfNat (g k)) j) (nnqOfNat (g j))
        = nnqOfNat (nsum g j + g j)
    rw [nnqOfNat_add (nsum g j) (g j), ih]

/-- **実化次数**（ℚ≥0 値）: deg_w(x) = Σ_{k<bound} w(k)·mult(k)。
    重み w(k) は k 番目の素点の log p_k の整数化（M51F と同じ正規化）。 -/
def degR (w : Nat → Nat) (x : RDiv) : NNQ :=
  nnqSum (fun k => nnqSmul (w k) (x.mult k)) x.bound

/-- 実化次数の安定性: サポート上界を超えて和を取っても変わらない。 -/
theorem degR_stable (w : Nat → Nat) (x : RDiv) (n : Nat)
    (hn : x.bound ≤ n) :
    nnqSum (fun k => nnqSmul (w k) (x.mult k)) n = degR w x :=
  nnqSum_tail (fun k => nnqSmul (w k) (x.mult k)) x.bound n hn
    (fun k hk => by
      show nnqSmul (w k) (x.mult k) = nnqZero
      rw [x.vanish k hk]
      exact nnqSmul_zero (w k))

/-- **定理 (M67F-4c): 実化次数の加法性** deg(x+y) = deg x + deg y。 -/
theorem degR_add (w : Nat → Nat) (x y : RDiv) :
    degR w (radd x y) = nnqAdd (degR w x) (degR w y) := by
  show nnqSum (fun k => nnqSmul (w k) (nnqAdd (x.mult k) (y.mult k)))
      (max x.bound y.bound) = nnqAdd (degR w x) (degR w y)
  have hpt : (fun k => nnqSmul (w k) (nnqAdd (x.mult k) (y.mult k)))
      = fun k => nnqAdd (nnqSmul (w k) (x.mult k))
          (nnqSmul (w k) (y.mult k)) :=
    funext fun k => nnqSmul_add (w k) (x.mult k) (y.mult k)
  rw [hpt, nnqSum_add,
    degR_stable w x (max x.bound y.bound) (Nat.le_max_left _ _),
    degR_stable w y (max x.bound y.bound) (Nat.le_max_right _ _)]

/-- **定理 (M67F-4d): 実化次数の斉次性** deg(φ_e x) = e·deg x。 -/
theorem degR_frob (w : Nat → Nat) (e : Nat) (x : RDiv) :
    degR w (rfrobN e x) = nnqSmul e (degR w x) := by
  show nnqSum (fun k => nnqSmul (w k) (nnqSmul e (x.mult k))) x.bound
      = nnqSmul e (degR w x)
  have hpt : (fun k => nnqSmul (w k) (nnqSmul e (x.mult k)))
      = fun k => nnqSmul e (nnqSmul (w k) (x.mult k)) :=
    funext fun k => by
      rw [nnqSmul_smul e (w k), nnqSmul_smul (w k) e, Nat.mul_comm]
  rw [hpt, nnqSum_smul]
  rfl

/-- **定理 (M67F-4e): 実化次数は整次数の実化** —
    deg_R(realify x) = ι(deg_N x)（次数の可換図式。実化が log-volume
    簿記を保つことの機械検証）。 -/
theorem degR_realify (w : Nat → Nat) (x : QDiv) :
    degR w (realify x) = nnqOfNat (degN w x) := by
  show nnqSum (fun k => nnqOfNat (w k * x.mult k)) x.bound
      = nnqOfNat (nsum (fun k => w k * x.mult k) x.bound)
  exact nnqSum_ofNat (fun k => w k * x.mult k) x.bound

/-! ## Part 4: 可除性定理（本丸、M67F-5） -/

/-- x の n 等分（成分ごとの nnqDiv、choice-free な明示 witness）。 -/
def rdivPart (x : RDiv) (n : Nat) (hn : 1 ≤ n) : RDiv where
  mult := fun k => nnqDiv (x.mult k) n hn
  bound := x.bound
  vanish := fun k hk => by
    rw [x.vanish k hk]
    exact nnqDiv_zero n hn

/-- n 等分の検証: φ_n(x/n) = x（成分ごとの nnq_div_cancel）。 -/
theorem rdivPart_spec (x : RDiv) (n : Nat) (hn : 1 ≤ n) :
    rfrobN n (rdivPart x n hn) = x :=
  RDiv.ext (funext fun k => nnq_div_cancel (x.mult k) n hn) rfl

/-- **定理 (M67F-5a): 実化因子モノイドの可除性** —
    任意の実化因子は任意の n ≥ 1 で n 等分できる
    （witness は rdivPart の明示構成: 選択公理不使用）。
    IUT の「パイロット対象の 1/2ℓ 等分」型の操作の土台。 -/
theorem rdiv_divisible (x : RDiv) (n : Nat) (hn : 1 ≤ n) :
    ∃ y : RDiv, rfrobN n y = x :=
  ⟨rdivPart x n hn, rdivPart_spec x n hn⟩

/-- **定理 (M67F-5b): 整係数側の不可除性**（具体的反例）—
    単一素点重複度 1 の因子 p_0 は 2 等分できない
    （成分の方程式 2m = 1 が ℕ で矛盾）。 -/
theorem qdiv_not_divisible :
    ¬ ∃ y : QDiv, qfrob 2 y = singleDiv 0 1 := by
  intro hex
  match hex with
  | ⟨y, h⟩ =>
    have h1 : 2 * y.mult 0 = (if (0 : Nat) = 0 then 1 else 0) :=
      congrArg (fun z => QDiv.mult z 0) h
    rw [if_pos rfl] at h1
    omega

/-- **定理 (M67F-5c): 「実化の本質 = 可除性の獲得」の両側機械検証** —
    実化側は全ての因子が全ての n ≥ 1 で可除、整係数側には 2 等分
    できない因子が実在する。しかも反例 p_0 自身も実化すれば 2 等分
    できる（realify (singleDiv 0 1) は可除）。 -/
theorem realification_gains_divisibility :
    (∀ (x : RDiv) (n : Nat), 1 ≤ n → ∃ y : RDiv, rfrobN n y = x)
      ∧ (¬ ∃ y : QDiv, qfrob 2 y = singleDiv 0 1)
      ∧ (∃ y : RDiv, rfrobN 2 y = realify (singleDiv 0 1)) :=
  ⟨rdiv_divisible, qdiv_not_divisible,
    rdiv_divisible (realify (singleDiv 0 1)) 2 (by omega)⟩

/-! ## Part 5: 実化 Frobenioid 圏と実化関手（M67F-6） -/

/-- **実化 Frobenioid の射**: x → y は Frobenius 次数 d ≥ 1 と
    実化因子 c の対で、線形条件 y = φ_d(x) + c を満たすもの
    （divisorFrobenioid の射の ℚ≥0 版）。 -/
structure RDivHom (x y : RDiv) where
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的実化因子部分 Div(φ)。 -/
  c : RDiv
  d_pos : 1 ≤ d
  /-- 線形条件: y = φ_d(x) + c。 -/
  linear : y = radd (rfrobN d x) c

/-- 射の外延性: RDivHom は (d, c) 成分で決まる（linear は Prop）。 -/
theorem RDivHom.ext {x y : RDiv} {f g : RDivHom x y}
    (hd : f.d = g.d) (hc : f.c = g.c) : f = g := by
  cases f with | mk fd fc f1 f2 =>
  cases g with | mk gd gc g1 g2 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  subst hd'
  subst hc'
  rfl

/-- 恒等射の線形条件: x = φ_1(x) + 0。 -/
theorem real_id_linear (x : RDiv) : x = radd (rfrobN 1 x) rzero := by
  rw [rfrob_one, radd_zero]

/-- 合成射の線形条件（捻れ半直積型: 因子代数の構造定理から従う）。 -/
theorem real_comp_linear {a b : Nat} {x y z c₁ c₂ : RDiv}
    (h₁ : y = radd (rfrobN a x) c₁) (h₂ : z = radd (rfrobN b y) c₂) :
    z = radd (rfrobN (a * b) x) (radd (rfrobN b c₁) c₂) := by
  rw [h₂, h₁, rfrob_add, rfrob_frob, radd_assoc]

/-- **定理 (M67F-6a): 実化 Frobenioid 圏** — 対象 = 実化因子、
    射 = (d ≥ 1, c) with y = φ_d(x) + c。恒等 (1, 0)、合成
    (d₁,c₁)·(d₂,c₂) = (d₁d₂, φ_{d₂}(c₁) + c₂)。圏公理は実化因子
    モノイドの構造定理（M67F-3, rfrob_*）から完全証明される。 -/
def realFrobenioid : Cat where
  Obj := RDiv
  Hom := RDivHom
  id := fun x => ⟨1, rzero, Nat.le_refl 1, real_id_linear x⟩
  comp := fun f g =>
    ⟨f.d * g.d, radd (rfrobN g.d f.c) g.c,
      Nat.mul_pos f.d_pos g.d_pos,
      real_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    RDivHom.ext (Nat.one_mul f.d)
      (by show radd (rfrobN f.d rzero) f.c = f.c
          rw [rfrob_zero, rzero_add])
  comp_id := fun f =>
    RDivHom.ext (Nat.mul_one f.d)
      (by show radd (rfrobN 1 f.c) rzero = f.c
          rw [rfrob_one, radd_zero])
  assoc := fun f g h =>
    RDivHom.ext (Nat.mul_assoc f.d g.d h.d)
      (by show radd (rfrobN h.d (radd (rfrobN g.d f.c) g.c)) h.c
            = radd (rfrobN (g.d * h.d) f.c) (radd (rfrobN h.d g.c) h.c)
          rw [rfrob_add, rfrob_frob, radd_assoc])

/-- 圏の中の純 Frobenius 射 x → φ_e(x)。 -/
def realFrobMor (e : Nat) (he : 1 ≤ e) (x : RDiv) :
    RDivHom x (rfrobN e x) :=
  ⟨e, rzero, he, (radd_zero (rfrobN e x)).symm⟩

/-- **定理 (M67F-5d): 圏レベルの可除性（パイロットの等分）** —
    実化 Frobenioid では任意の対象 x と任意の n ≥ 1 に対し、
    「x の 1/n」にあたる対象 y（φ_n(y) = x）と次数 n の純 Frobenius 射
    y → x が実在する。divisorFrobenioid では偽（M67F-5b の反例）。 -/
theorem real_pilot_division (x : RDiv) (n : Nat) (hn : 1 ≤ n) :
    ∃ y : RDiv, rfrobN n y = x ∧ Nonempty (RDivHom y x) := by
  refine ⟨rdivPart x n hn, rdivPart_spec x n hn, ⟨⟨n, rzero, hn, ?_⟩⟩⟩
  rw [rdivPart_spec x n hn, radd_zero]

/-- **定理 (M67F-6b): 実化関手** divisorFrobenioid → realFrobenioid —
    対象は realify、射 (d, c) は (d, realify c)。線形条件の保存は
    realify の加法性（M67F-4a）と Frobenius 両立（M67F-4b）そのもの。
    [FrdI] の実化関手 F → F^rlf の base 一点・因子モノイドレベルの実装。 -/
def realifyFunctor : Functor divisorFrobenioid realFrobenioid where
  onObj := realify
  onHom := fun {x y} f =>
    { d := f.d
      c := realify f.c
      d_pos := f.d_pos
      linear := by
        have h : realify y = realify (qadd (qfrob f.d x) f.c) :=
          congrArg realify f.linear
        rw [realify_add, realify_frob] at h
        exact h }
  map_id := fun x => RDivHom.ext rfl realify_zero
  map_comp := fun f g =>
    RDivHom.ext rfl
      (by show realify (qadd (qfrob g.d f.c) g.c)
            = radd (rfrobN g.d (realify f.c)) (realify g.c)
          rw [realify_add, realify_frob])

/-! ## Part 6: 剛性（M67F-7）—可除でも同型は増えない -/

/-- 同型の hom 成分の Frobenius 次数は 1（M48F の算術核の再利用）。 -/
theorem real_iso_d_one {x y : RDiv} (i : CatIso realFrobenioid x y) :
    i.hom.d = 1 :=
  frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos
    (congrArg RDivHom.d i.hom_inv)

/-- 同型の hom 成分の因子部分は 0（上界の簿記から: max bound = 0）。 -/
theorem real_iso_c_zero {x y : RDiv} (i : CatIso realFrobenioid x y) :
    i.hom.c = rzero := by
  have hc : radd (rfrobN i.inv.d i.hom.c) i.inv.c = rzero :=
    congrArg RDivHom.c i.hom_inv
  have hb : max i.hom.c.bound i.inv.c.bound = 0 :=
    congrArg RDiv.bound hc
  have hb0 : i.hom.c.bound = 0 := nat_max_eq_zero_left hb
  exact RDiv.ext
    (funext fun k => i.hom.c.vanish k (by rw [hb0]; exact Nat.zero_le k))
    hb0

/-- **定理 (M67F-7a): 実化圏の gaunt 性** — realFrobenioid の同型は
    対象を動かせない（x ≅ y ⟹ x = y）。**可除性（全対象が n 等分可能 =
    φ_n の全射性）を獲得しても Frobenius-like 剛性は壊れない**:
    φ_n の「逆」は対象レベルの witness であって圏の同型ではない
    （同型なら n·d = 1 が必要で n ≥ 2 では不可能）。 -/
theorem real_iso_objects_eq {x y : RDiv}
    (i : CatIso realFrobenioid x y) : x = y := by
  have hl := i.hom.linear
  rw [real_iso_d_one i, real_iso_c_zero i, rfrob_one, radd_zero] at hl
  exact hl.symm

/-- **定理 (M67F-7b): gaunt + 同型の一意性**（M53F の剛性述語の充足）—
    実化 Frobenioid は IsGaunt かつ IsoUnique
    （poly-isomorphism は単集合以下に潰れる）。 -/
theorem real_gaunt_isoUnique :
    IsGaunt realFrobenioid ∧ IsoUnique realFrobenioid :=
  ⟨fun _ _ i => real_iso_objects_eq i,
   fun _ _ i j =>
     RDivHom.ext ((real_iso_d_one i).trans (real_iso_d_one j).symm)
       ((real_iso_c_zero i).trans (real_iso_c_zero j).symm)⟩

end IUT
