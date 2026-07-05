/-
  # M262F: 非負有理数 ℚ≥0 上の順序 nnqLe と比較射の順序両立（柱C・log-volume 橋の残件を 1 スライス）

  柱C（issue #37）C-1。M67F（`Realification.lean`）は ℚ≥0 を Quot で
  自前構成し可除性・実化次数 degR を建設したが、その正直申告で

    「順序構造は未形式化: ℚ≥0 上の ≤（および因子の効果性の順序）は
     定義しておらず……」

  と明記していた。M236F（`NNQtoQHom.lean`）は比較射 nnqToQ : ℚ≥0 → ℚ が
  零・加法・ℕ 倍作用を保つ可換モノイド準同型であることを固定したが、
  **順序**の両立はそこでも扱っていなかった。本層はこの残件——ℚ≥0 上に
  交差積による半順序 `nnqLe` を定義し、それが半順序であること・加法/
  ℕ 倍/埋め込みと単調に両立すること・そして比較射 nnqToQ が**順序を
  保つ**（ℚ の順序 qLe へ、さらに本物の ℝ の順序 rLe へ持ち上がる）
  ことを機械検証する。これで M236F の「可換モノイド準同型」の描像が
  **順序モノイド準同型**（零・加法・ℕ 倍作用・順序をすべて保つ）に
  完成する。

  * M262F-1 `nnqLe_cross` / `nnqLe_cross_r` — 交差積順序の well-def の
    核となる Nat 不等式（正因子の相殺 `Nat.le_of_mul_le_mul_right`）
  * M262F-2 `nnqLePre` / `nnqLePre_left` / `nnqLePre_right` — 代表順序と
    両引数での well-definedness（propext による Prop 値 Quot.lift）
  * M262F-3 `nnqLe` — **ℚ≥0 上の順序**（二重 Quot.lift、choice-free）
  * M262F-4 `nnqLe_refl` / `nnqLe_trans` / `nnqLe_antisym` / `nnqZero_le`
    — **半順序**（反射・推移・反対称）と最小元 0（0 ≤ x）
  * M262F-5 `nnqSmul_mono` / `nnqOfNat_mono` / `nnqAdd_le_left` /
    `nnqAdd_mono` — 演算の単調性（ℕ 倍・埋め込み・加法）。順序付き
    可換モノイドの構造
  * M262F-6 `nnqToQ_mono`（本丸）— **比較射の順序両立** nnqLe x y ⟹
    qLe (nnqToQ x) (nnqToQ y)。M236F の準同型描像に順序を追加
  * M262F-7 `nnqToQ_realMono` — 本物の ℝ への持ち上げ: nnqLe x y ⟹
    rLe (qToReal (nnqToQ x)) (qToReal (nnqToQ y))（M131F の qToReal_mono
    と合成）
  * M262F-8 `NNQOrderData` — 総括データ束と存在

  ## 意義

  M67F の正直申告（順序未形式化）を回収し、M236F の比較射準同型の描像を
  順序込みに完成させる。ℚ≥0 の半順序が加法・ℕ 倍・埋め込みと単調に
  両立し、比較射 nnqToQ を通して ℚ・ℝ の順序に忠実に持ち上がることで、
  M67F の実化次数 degR（ℚ≥0 値）の大小関係が本物の ℝ の順序として
  読めるようになる。

  ## 正直な限定

  * 順序 nnqLe は交差積 a(d+1) ≤ c(b+1) による半順序。**線形性
    （nnqLe x y ∨ nnqLe y x）は本層では扱わない**（ℕ の全順序から
    従うが本スライスの範囲外）。
  * 因子（RDiv）の点ごと順序から degR の順序を導く単調性簿記は本層では
    扱わない（degR はサポート上界が異なると別対象になる M67F の表示の
    自由度が絡むため）。本層は ℚ≥0 スカラーの順序とその演算・比較射
    両立に限定する。整係数 QDiv の効果性順序 → 実数値 log-volume の
    単調性は M240F が別途閉じている。
  * 乗法（環準同型 map_mul）は M236F 同様扱わない（ℚ≥0 に乗法未定義）。
  * 全て選択公理不使用（型継承除く）。Prop 値 Quot.lift の well-def に
    propext を使う。`#print axioms` で実測（[propext, Quot.sound] のみ）。
  * サブエージェント並行部品。
-/
import IUT.LogVolBridge

namespace IUT

/-! ## M262F-1: 交差積順序 well-def の核となる Nat 不等式 -/

/-- **補題 (M262F-1a): 第一引数の付替の核** — a·B' = a'·B（B > 0）かつ
    a·D ≤ c·B なら a'·D ≤ c·B'。正因子 B の相殺で落とす。 -/
theorem nnqLe_cross (a a' c B B' D : Nat) (hpos : 0 < B)
    (heq : a * B' = a' * B) (hle : a * D ≤ c * B) : a' * D ≤ c * B' := by
  have hmul : a * D * B' ≤ c * B * B' := Nat.mul_le_mul hle (Nat.le_refl B')
  have key : a' * D * B ≤ c * B' * B := by
    have e1 : a' * D * B = a * D * B' := by
      rw [Nat.mul_right_comm a' D B, ← heq, Nat.mul_right_comm a B' D]
    have e2 : c * B' * B = c * B * B' := Nat.mul_right_comm c B' B
    rw [e1, e2]
    exact hmul
  exact Nat.le_of_mul_le_mul_right key hpos

/-- **補題 (M262F-1b): 第二引数の付替の核** — q1·E' = q1'·E（E > 0）かつ
    A·E ≤ q1·B なら A·E' ≤ q1'·B。正因子 E の相殺で落とす。 -/
theorem nnqLe_cross_r (A B E E' q1 q1' : Nat) (hpos : 0 < E)
    (heq : q1 * E' = q1' * E) (hle : A * E ≤ q1 * B) : A * E' ≤ q1' * B := by
  have hmul : A * E * E' ≤ q1 * B * E' := Nat.mul_le_mul hle (Nat.le_refl E')
  have key : A * E' * E ≤ q1' * B * E := by
    have e1 : A * E' * E = A * E * E' := Nat.mul_right_comm A E' E
    have e2 : q1 * B * E' = q1' * B * E := by
      rw [Nat.mul_right_comm q1 B E', heq, Nat.mul_right_comm q1' E B]
    rw [e2] at hmul
    rw [e1]
    exact hmul
  exact Nat.le_of_mul_le_mul_right key hpos

/-! ## M262F-2: 代表順序と両引数での well-definedness -/

/-- **M262F-2a: 代表順序** — (a, b) ≤ (c, d) ⟺ a(d+1) ≤ c(b+1)
    （a/(b+1) ≤ c/(d+1) の交差積）。 -/
def nnqLePre (p q : QPre) : Prop := p.1 * (q.2 + 1) ≤ q.1 * (p.2 + 1)

/-- **M262F-2b: 第一引数の well-definedness** — p ~ p' なら
    nnqLePre p q と nnqLePre p' q は同値（propext で命題等式へ）。 -/
theorem nnqLePre_left {p p' : QPre} (h : nnqRel p p') (q : QPre) :
    nnqLePre p q = nnqLePre p' q := by
  apply propext
  apply Iff.intro
  · intro hle
    exact nnqLe_cross p.1 p'.1 q.1 (p.2 + 1) (p'.2 + 1) (q.2 + 1)
      (by omega) h hle
  · intro hle
    exact nnqLe_cross p'.1 p.1 q.1 (p'.2 + 1) (p.2 + 1) (q.2 + 1)
      (by omega) h.symm hle

/-- **M262F-2c: 第二引数の well-definedness** — q ~ q' なら
    nnqLePre p q と nnqLePre p q' は同値。 -/
theorem nnqLePre_right (p : QPre) {q q' : QPre} (h : nnqRel q q') :
    nnqLePre p q = nnqLePre p q' := by
  apply propext
  apply Iff.intro
  · intro hle
    exact nnqLe_cross_r p.1 (p.2 + 1) (q.2 + 1) (q'.2 + 1) q.1 q'.1
      (by omega) h hle
  · intro hle
    exact nnqLe_cross_r p.1 (p.2 + 1) (q'.2 + 1) (q.2 + 1) q'.1 q.1
      (by omega) h.symm hle

/-! ## M262F-3: ℚ≥0 上の順序 -/

/-- **M262F-3: ℚ≥0 上の順序**（二重 Quot.lift、choice-free）。
    x ≤ y ⟺ 代表 (a,b) (c,d) で a(d+1) ≤ c(b+1)。well-definedness は
    両引数の交差積付替（M262F-2）。 -/
def nnqLe (x y : NNQ) : Prop :=
  Quot.lift
    (fun p => Quot.lift (fun q => nnqLePre p q)
      (fun _ _ hq => nnqLePre_right p hq) y)
    (fun _ _ hp => by
      induction y using Quot.ind
      rename_i q
      exact nnqLePre_left hp q) x

/-! ## M262F-4: 半順序と最小元 -/

/-- **定理 (M262F-4a): 反射律** x ≤ x。 -/
theorem nnqLe_refl (x : NNQ) : nnqLe x x := by
  induction x using Quot.ind; rename_i p
  show p.1 * (p.2 + 1) ≤ p.1 * (p.2 + 1)
  exact Nat.le_refl _

/-- **定理 (M262F-4b): 推移律** x ≤ y → y ≤ z → x ≤ z
    （中間の分母 (q.2+1) の相殺）。 -/
theorem nnqLe_trans {x y z : NNQ} (hxy : nnqLe x y) (hyz : nnqLe y z) :
    nnqLe x z := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  induction z using Quot.ind; rename_i r
  have h1 : p.1 * (q.2 + 1) ≤ q.1 * (p.2 + 1) := hxy
  have h2 : q.1 * (r.2 + 1) ≤ r.1 * (q.2 + 1) := hyz
  show p.1 * (r.2 + 1) ≤ r.1 * (p.2 + 1)
  have m1 : p.1 * (q.2 + 1) * (r.2 + 1) ≤ q.1 * (p.2 + 1) * (r.2 + 1) :=
    Nat.mul_le_mul h1 (Nat.le_refl _)
  have m2 : q.1 * (r.2 + 1) * (p.2 + 1) ≤ r.1 * (q.2 + 1) * (p.2 + 1) :=
    Nat.mul_le_mul h2 (Nat.le_refl _)
  have key : p.1 * (r.2 + 1) * (q.2 + 1) ≤ r.1 * (p.2 + 1) * (q.2 + 1) :=
    calc p.1 * (r.2 + 1) * (q.2 + 1)
        = p.1 * (q.2 + 1) * (r.2 + 1) := Nat.mul_right_comm _ _ _
      _ ≤ q.1 * (p.2 + 1) * (r.2 + 1) := m1
      _ = q.1 * (r.2 + 1) * (p.2 + 1) := Nat.mul_right_comm _ _ _
      _ ≤ r.1 * (q.2 + 1) * (p.2 + 1) := m2
      _ = r.1 * (p.2 + 1) * (q.2 + 1) := Nat.mul_right_comm _ _ _
  exact Nat.le_of_mul_le_mul_right key (by omega)

/-- **定理 (M262F-4c): 反対称律** x ≤ y → y ≤ x → x = y
    （両側 ≤ から交差積の等式 → nnqRel → Quot.sound）。 -/
theorem nnqLe_antisym {x y : NNQ} (h1 : nnqLe x y) (h2 : nnqLe y x) :
    x = y := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  have e1 : p.1 * (q.2 + 1) ≤ q.1 * (p.2 + 1) := h1
  have e2 : q.1 * (p.2 + 1) ≤ p.1 * (q.2 + 1) := h2
  exact Quot.sound (Nat.le_antisymm e1 e2)

/-- **定理 (M262F-4d): 最小元** 0 ≤ x（ℚ≥0 は非負錐）。 -/
theorem nnqZero_le (x : NNQ) : nnqLe nnqZero x := by
  induction x using Quot.ind; rename_i p
  show 0 * (p.2 + 1) ≤ p.1 * (0 + 1)
  rw [Nat.zero_mul]
  exact Nat.zero_le _

/-! ## M262F-5: 演算の単調性（順序付き可換モノイド） -/

/-- **定理 (M262F-5a): ℕ 倍の単調性** x ≤ y → n·x ≤ n·y。 -/
theorem nnqSmul_mono (n : Nat) {x y : NNQ} (h : nnqLe x y) :
    nnqLe (nnqSmul n x) (nnqSmul n y) := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  have hN : p.1 * (q.2 + 1) ≤ q.1 * (p.2 + 1) := h
  show n * p.1 * (q.2 + 1) ≤ n * q.1 * (p.2 + 1)
  have hm : n * (p.1 * (q.2 + 1)) ≤ n * (q.1 * (p.2 + 1)) :=
    Nat.mul_le_mul (Nat.le_refl n) hN
  rw [← Nat.mul_assoc, ← Nat.mul_assoc] at hm
  exact hm

/-- **定理 (M262F-5b): 埋め込みの単調性** m ≤ n → ι m ≤ ι n。 -/
theorem nnqOfNat_mono {m n : Nat} (h : m ≤ n) :
    nnqLe (nnqOfNat m) (nnqOfNat n) := by
  show m * (0 + 1) ≤ n * (0 + 1)
  have e : (0 + 1 : Nat) = 1 := rfl
  rw [e, Nat.mul_one, Nat.mul_one]
  exact h

/-- **定理 (M262F-5c): 加法の右平行移動単調性** x ≤ y → x + c ≤ y + c
    （交差積を展開し、共通因子 c 側の項は相等・可変側の項は c の分母の
    二乗を掛けた M262F-4 の不等式に落とす）。 -/
theorem nnqAdd_le_left {x y : NNQ} (c : NNQ) (h : nnqLe x y) :
    nnqLe (nnqAdd x c) (nnqAdd y c) := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  induction c using Quot.ind; rename_i r
  have hN : p.1 * (q.2 + 1) ≤ q.1 * (p.2 + 1) := h
  show preNum p r * (preDen q.2 r.2 + 1) ≤ preNum q r * (preDen p.2 r.2 + 1)
  rw [preDen_succ, preDen_succ]
  show (p.1 * (r.2 + 1) + r.1 * (p.2 + 1)) * ((q.2 + 1) * (r.2 + 1))
      ≤ (q.1 * (r.2 + 1) + r.1 * (q.2 + 1)) * ((p.2 + 1) * (r.2 + 1))
  have key1 : p.1 * (r.2 + 1) * ((q.2 + 1) * (r.2 + 1))
      = p.1 * (q.2 + 1) * ((r.2 + 1) * (r.2 + 1)) := by
    rw [Nat.mul_assoc (p.1) (r.2 + 1) ((q.2 + 1) * (r.2 + 1)),
      Nat.mul_left_comm (r.2 + 1) (q.2 + 1) (r.2 + 1),
      ← Nat.mul_assoc (p.1) (q.2 + 1) ((r.2 + 1) * (r.2 + 1))]
  have key2 : q.1 * (r.2 + 1) * ((p.2 + 1) * (r.2 + 1))
      = q.1 * (p.2 + 1) * ((r.2 + 1) * (r.2 + 1)) := by
    rw [Nat.mul_assoc (q.1) (r.2 + 1) ((p.2 + 1) * (r.2 + 1)),
      Nat.mul_left_comm (r.2 + 1) (p.2 + 1) (r.2 + 1),
      ← Nat.mul_assoc (q.1) (p.2 + 1) ((r.2 + 1) * (r.2 + 1))]
  have t1 : p.1 * (r.2 + 1) * ((q.2 + 1) * (r.2 + 1))
      ≤ q.1 * (r.2 + 1) * ((p.2 + 1) * (r.2 + 1)) := by
    rw [key1, key2]
    exact Nat.mul_le_mul hN (Nat.le_refl _)
  have t2 : r.1 * (p.2 + 1) * ((q.2 + 1) * (r.2 + 1))
      = r.1 * (q.2 + 1) * ((p.2 + 1) * (r.2 + 1)) := by
    rw [Nat.mul_assoc (r.1) (p.2 + 1) ((q.2 + 1) * (r.2 + 1)),
      Nat.mul_left_comm (p.2 + 1) (q.2 + 1) (r.2 + 1),
      ← Nat.mul_assoc (r.1) (q.2 + 1) ((p.2 + 1) * (r.2 + 1))]
  have hLexp : (p.1 * (r.2 + 1) + r.1 * (p.2 + 1)) * ((q.2 + 1) * (r.2 + 1))
      = p.1 * (r.2 + 1) * ((q.2 + 1) * (r.2 + 1))
        + r.1 * (p.2 + 1) * ((q.2 + 1) * (r.2 + 1)) :=
    Nat.add_mul _ _ _
  have hRexp : (q.1 * (r.2 + 1) + r.1 * (q.2 + 1)) * ((p.2 + 1) * (r.2 + 1))
      = q.1 * (r.2 + 1) * ((p.2 + 1) * (r.2 + 1))
        + r.1 * (q.2 + 1) * ((p.2 + 1) * (r.2 + 1)) :=
    Nat.add_mul _ _ _
  rw [hLexp, hRexp, t2]
  exact Nat.add_le_add t1 (Nat.le_refl _)

/-- **定理 (M262F-5d): 加法の単調性** x ≤ y → c ≤ d → x + c ≤ y + d
    （片側平行移動 + 可換 + 推移）。 -/
theorem nnqAdd_mono {a b c d : NNQ} (h1 : nnqLe a b) (h2 : nnqLe c d) :
    nnqLe (nnqAdd a c) (nnqAdd b d) := by
  apply nnqLe_trans (nnqAdd_le_left c h1)
  rw [nnqAdd_comm b c, nnqAdd_comm b d]
  exact nnqAdd_le_left b h2

/-! ## M262F-6: 比較射の順序両立（本丸） -/

/-- **定理 (M262F-6): 比較射の順序両立（本丸）** — nnqLe x y なら
    qLe (nnqToQ x) (nnqToQ y)。M67F の ℚ≥0 順序が M115F の ℚ 順序 qLe に
    忠実に持ち上がる。M236F の準同型描像（零・加法・ℕ 倍）に順序を
    加えて**順序モノイド準同型**を完成させる。 -/
theorem nnqToQ_mono {x y : NNQ} (h : nnqLe x y) :
    qLe (nnqToQ x) (nnqToQ y) := by
  induction x using Quot.ind; rename_i p
  induction y using Quot.ind; rename_i q
  have hN : p.1 * (q.2 + 1) ≤ q.1 * (p.2 + 1) := h
  show (p.1 : Int) * ((q.2 : Int) + 1) ≤ (q.1 : Int) * ((p.2 : Int) + 1)
  have hI : ((p.1 * (q.2 + 1) : Nat) : Int) ≤ ((q.1 * (p.2 + 1) : Nat) : Int) :=
    Int.ofNat_le.mpr hN
  rw [Int.natCast_mul, Int.natCast_mul] at hI
  have e1 : ((q.2 + 1 : Nat) : Int) = (q.2 : Int) + 1 := by omega
  have e2 : ((p.2 + 1 : Nat) : Int) = (p.2 : Int) + 1 := by omega
  rw [e1, e2] at hI
  exact hI

/-! ## M262F-7: 本物の ℝ への持ち上げ -/

/-- **定理 (M262F-7): 実数値順序への持ち上げ** — nnqLe x y なら
    rLe (qToReal (nnqToQ x)) (qToReal (nnqToQ y))。ℚ≥0 の順序が比較射と
    M131F の埋め込み単調性 qToReal_mono を通して本物の ℝ の順序 rLe に
    持ち上がる。M67F の実化次数 degR の大小が本物の ℝ で読める。 -/
theorem nnqToQ_realMono {x y : NNQ} (h : nnqLe x y) :
    rLe (qToReal (nnqToQ x)) (qToReal (nnqToQ y)) :=
  qToReal_mono (nnqToQ_mono h)

/-! ## M262F-8: 総括 -/

/-- **M262F-8a: 総括** — ℚ≥0 上の順序 nnqLe のデータ束。M67F の順序
    未形式化を回収し、半順序・最小元・演算単調性・比較射順序両立
    （ℚ・ℝ の両順序）の実定理のみを束ねる。 -/
structure NNQOrderData where
  /-- 反射律。 -/
  le_refl : ∀ x : NNQ, nnqLe x x
  /-- 推移律。 -/
  le_trans : ∀ {x y z : NNQ}, nnqLe x y → nnqLe y z → nnqLe x z
  /-- 反対称律（NNQ の等式が返る）。 -/
  le_antisym : ∀ {x y : NNQ}, nnqLe x y → nnqLe y x → x = y
  /-- 最小元 0 ≤ x。 -/
  zero_le : ∀ x : NNQ, nnqLe nnqZero x
  /-- ℕ 倍の単調性。 -/
  smul_mono : ∀ (n : Nat) {x y : NNQ}, nnqLe x y →
    nnqLe (nnqSmul n x) (nnqSmul n y)
  /-- 埋め込みの単調性。 -/
  ofNat_mono : ∀ {m n : Nat}, m ≤ n → nnqLe (nnqOfNat m) (nnqOfNat n)
  /-- 加法の単調性。 -/
  add_mono : ∀ {a b c d : NNQ}, nnqLe a b → nnqLe c d →
    nnqLe (nnqAdd a c) (nnqAdd b d)
  /-- 比較射の順序両立（ℚ 値）。 -/
  toQ_mono : ∀ {x y : NNQ}, nnqLe x y → qLe (nnqToQ x) (nnqToQ y)
  /-- 比較射の順序両立（ℝ 値）。 -/
  toReal_mono : ∀ {x y : NNQ}, nnqLe x y →
    rLe (qToReal (nnqToQ x)) (qToReal (nnqToQ y))

/-- **M262F-8b: witness**。 -/
def nnqOrderData : NNQOrderData where
  le_refl := nnqLe_refl
  le_trans := nnqLe_trans
  le_antisym := nnqLe_antisym
  zero_le := nnqZero_le
  smul_mono := nnqSmul_mono
  ofNat_mono := nnqOfNat_mono
  add_mono := nnqAdd_mono
  toQ_mono := nnqToQ_mono
  toReal_mono := nnqToQ_realMono

/-- **capstone (M262F-8c): 存在** — ℚ≥0 の順序構造が無矛盾に存在する。
    柱C の M67F 正直申告（順序未形式化）を回収し、比較射 nnqToQ が
    順序モノイド準同型（零・加法・ℕ 倍・順序を保つ）として ℚ・ℝ の
    順序に忠実に持ち上がることの単一証明記録としての締めくくり。 -/
theorem nnqOrder_exists : Nonempty NNQOrderData :=
  ⟨nnqOrderData⟩

end IUT
