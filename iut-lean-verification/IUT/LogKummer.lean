/-
  IUT/LogKummer.lean — M205F（log-Kummer 対応の骨格・柱D D-α-4・並行部品）

  # M205F: log-Kummer 対応の骨格（柱D D-α-4・並行部品）

  IUT III 定理3.11 (ii) の **log-Kummer 対応** の骨格を、M3 の
  log-theta 格子の**垂直経路**（log-link のみの経路 = Θ-link 0 本の
  `Path 0`）の上に建てる。垂直線（一つの数論的正則構造の内部）の
  各段 m に「対数殻（Region）」と「Frobenius 的データ」を載せた塔
  `VerticalKummerTower` に対し、log-Kummer 両立性
  `LogKummerCompat` を次の二層で定義する:

  * **(a) 対数殻**: 各 log-step で包含 ⊆ **のみ**（一方向）。
    M202F の (Ind3) 上半両立 `UpperCompat` に正確に対応する
    （各ステップが `UpperCompat` を与える: `logKummerStep`）。
  * **(b)(c) Frobenius 的データ（splitting monoid・数体 MOD 側）**:
    各 log-step で**厳密**（等号・両側両立）。

  モジュール索引:
  * M205F-1 `path_row` — 格子経路の行単調性: どのリンク経路でも
    終点の行 ≥ 始点の行（log-link は行 +1・Θ-link は行不変）。
    M3-1 `path_col`（列の簿記）の行方向の対。
  * M205F-2 `VerticalKummerTower` — 垂直線の Kummer 塔:
    列ラベル `col`・各段の対数殻 `shell : Int → V.Region`・
    各段の Frobenius 的データ `frob : Int → α`。
  * M205F-3 `LogKummerCompat` — **log-Kummer 両立性述語**:
    (a) `upper`（殻の一方向包含 ⊆・Ind3 ゲート）と
    (b)(c) `strict`（Frobenius 側の厳密等号）の対。
  * M205F-4 `logKummerStep` / `logKummer_ind3_gated` — 各 log-step
    が M202F の `UpperCompat`（Ind3 の選択肢）を与える。(a) 部の
    両立が Ind3 の一方向スラック**そのもの**であることの型レベルの
    連結（Dα-3 → Dα-4 の接合点）。
  * M205F-5 `logKummer_shell_mono_up` / `logKummer_shell_mono` —
    **単調包含簿記**: 殻の包含は垂直線に沿って合成され、
    m ≤ m' なら shell m ⊆ shell m'（⊆ の望遠鏡合成）。
  * M205F-6 `logKummer_frob_const_up` / `logKummer_frob_const` —
    (b)(c) 側は**両側**: Frobenius 的データは垂直線全体で一定
    （厳密両立の望遠鏡合成、上下両方向）。
  * M205F-7 `logKummer_along_logPath` / `logKummerPathCompat` —
    **格子への接続**: 塔の列上の任意の垂直経路 `Path 0 s t` に沿って
    (列保存 ∧ 殻 ⊆ ∧ Frobenius =) が成り立ち、経路全体が一つの
    `UpperCompat` を与える。M3-2 `pure_log_same_col` との合流。
  * M205F-8 `m205fTower` / `m205fTower_compat` / `logKummer_not_symm`
    — **(a) 部の真の一方向性**: 両立するが逆包含 ⊇ は成り立たない
    witness（Int モデル・M202F-4 `upper_compat_not_symm` の塔版）。
  * M205F-9 `Level1KummerKernel` / `level1_kummer_of_residue` /
    `level1_kummer_unit_unique` / `level1_kummer_one` —
    **レベル 1 Kummer 核**: 単数分解 O^× = μ_{p−1} × U^(1)（M35）を
    Kummer 理論の離散核の語彙で再輸出する。存在（分解 x = ω(a)·u）と
    一意性（主単数部の一意性）、および具体 witness（p = 2, x = 1）。
  * M205F-10 capstone: `LogKummerData` / `logKummerData` /
    `logKummer_exists`。

  ## 意義

  Dα-4: 定理3.11 (ii) の log-Kummer 対応の骨格 —— 垂直線（log-link
  の反復）に沿って (b)(c) は厳密両立・(a) 対数殻は Ind3 ゲートの
  ⊆ のみ —— を M3 の格子経路の上の述語として立てる。各 log-step が
  M202F の `UpperCompat`（Ind3）を正確に一つ与えること
  （`logKummer_ind3_gated`）が Dα-3 との接合であり、包含の望遠鏡
  合成（`logKummer_shell_mono`）が「m を動かしても像は単調に
  容器に収まり続ける」という (ii) の簿記である。離散核側は M35 の
  単数分解 μ × U^(1) をレベル 1 Kummer 核として供給する。本モジュール
  は Dα-5 の kummer フィールドへ渡す部品である。

  ## 正直な限定

  * 本モジュールは **weak-form**（レベル 1 核 + 格子垂直経路の単調
    包含簿記 + 両立性述語）である。全レベル（全 n での U^(n) 剰余・
    塔の完全座標）にわたる Kummer 同型の構成は II-B（塔の完全座標）
    を要し、次層で強化される。
  * `VerticalKummerTower` の殻 `shell` と レベル 1 核
    `Level1KummerKernel` は capstone データ内で**並置**されるに
    留まり、殻が実際に単数群の対数像（log(O^×) の格子点）である
    ことの同定は II-B + Dα-5 の課題である。
  * Kummer「同型」そのもの（円分物の同期・mono-theta 環境経由の
    エタール-Frobenius 橋）と `MultiradialRep` の解析的構成は D-β
    の課題であり、本層は両立性の型レベルの骨格に徹する。
  * 幾何級数逆元近似（M176）による殻半径の定量簿記は本層では
    使用せず、体積付き強化の際に導入する。

  sorry なし・新規 Classical.choice なし（core Lean のみ）。
  サブエージェント並行部品（tier-L・Dα-4）。
-/
import IUT.LogThetaLattice
import IUT.Indeterminacies
import IUT.UnitDecomposition

namespace IUT

/-! ## M205F-1: 格子経路の行単調性（M3-1 の行方向の対） -/

/-- **補題 (M205F-1): 行の単調性** — 任意のリンク経路で終点の行は
    始点の行以上（log-link は行 +1・Θ-link は行不変なので、行は
    決して減らない）。垂直方向の包含簿記が「経路に沿って一方向に
    進む」ことの組合せ的基盤。 -/
theorem path_row {k : Nat} {s t : LatticeSite} (p : Path k s t) :
    s.row ≤ t.row := by
  induction p with
  | nil s => exact Int.le_refl s.row
  | log n m _ ih => exact Int.le_trans (show (m : Int) ≤ m + 1 by omega) ih
  | theta n m _ ih => exact ih

/-! ## M205F-2: 垂直線の Kummer 塔 -/

/-- **垂直 Kummer 塔** — log-theta 格子の一つの列 `col`（一つの
    数論的正則構造）の垂直線に載るデータ:
    各行 m の対数殻 `shell m`（(a) 部・体積理論 V の領域）と
    Frobenius 的データ `frob m`（(b)(c) 部・splitting monoid /
    数体 MOD 側の型 α の値）。 -/
structure VerticalKummerTower (V : VolumeTheory) (α : Type) where
  /-- 塔の属する列（数論的正則構造のラベル）。 -/
  col : Int
  /-- 各行 m の対数殻（(a) 部の mono-analytic container）。 -/
  shell : Int → V.Region
  /-- 各行 m の Frobenius 的データ（(b)(c) 部）。 -/
  frob : Int → α

/-! ## M205F-3: log-Kummer 両立性述語 -/

/-- **log-Kummer 両立性**（定理3.11 (ii) の骨格）— 垂直線の各
    log-step (m → m+1) で:
    * (a) 対数殻は包含 ⊆ **のみ**（`upper`・一方向・Ind3 ゲート）、
    * (b)(c) Frobenius 的データは**厳密**（`strict`・等号・両側）。
    (a) が等号でなく ⊆ に留まる点が (Ind3) 上半両立の核心である。 -/
structure LogKummerCompat {V : VolumeTheory} {α : Type}
    (T : VerticalKummerTower V α) : Prop where
  /-- (a) 各 log-step の一方向包含: shell m ⊆ shell (m+1)。 -/
  upper : ∀ m : Int, V.le (T.shell m) (T.shell (m + 1))
  /-- (b)(c) 各 log-step の厳密両立: frob m = frob (m+1)。 -/
  strict : ∀ m : Int, T.frob m = T.frob (m + 1)

/-! ## M205F-4: 各 log-step は (Ind3) の UpperCompat を与える -/

/-- **各 log-step の Ind3 データ** — 両立する塔の各段 m から、
    M202F の (Ind3) 上半両立 `UpperCompat`（lo = shell m,
    hi = shell (m+1)）を構成する。 -/
def logKummerStep {V : VolumeTheory} {α : Type}
    {T : VerticalKummerTower V α} (h : LogKummerCompat T) (m : Int) :
    UpperCompat V :=
  ⟨T.shell m, T.shell (m + 1), h.upper m⟩

/-- **定理 (M205F-4): (a) 部は Ind3 ゲート** — log-Kummer 両立塔の
    各 log-step は (Ind3) の選択肢（`UpperCompat`）を正確に一つ
    与える。Dα-3（M202F）と Dα-4 の接合点。 -/
theorem logKummer_ind3_gated {V : VolumeTheory} {α : Type}
    {T : VerticalKummerTower V α} (h : LogKummerCompat T) (m : Int) :
    ∃ c : UpperCompat V, c.lo = T.shell m ∧ c.hi = T.shell (m + 1) :=
  ⟨logKummerStep h m, rfl, rfl⟩

/-! ## M205F-5: 単調包含簿記（(a) 部の望遠鏡合成） -/

/-- **補題 (M205F-5a): 上向き k 段の包含** — m' = m + k（k : ℕ）なら
    shell m ⊆ shell m'（各段の ⊆ の望遠鏡合成）。 -/
theorem logKummer_shell_mono_up {V : VolumeTheory} {α : Type}
    {T : VerticalKummerTower V α} (h : LogKummerCompat T) :
    ∀ (k : Nat) (m m' : Int), m' = m + (k : Int) →
      V.le (T.shell m) (T.shell m') := by
  intro k
  induction k with
  | zero =>
    intro m m' hm
    have hm' : m' = m + ((0 : Nat) : Int) := hm
    rw [show m' = m by omega]
    exact V.le_refl (T.shell m)
  | succ k ih =>
    intro m m' hm
    have hm' : m' = m + ((k + 1 : Nat) : Int) := hm
    rw [show m' = m + (k : Int) + 1 by omega]
    exact V.le_trans (ih m (m + (k : Int)) rfl) (h.upper (m + (k : Int)))

/-- **定理 (M205F-5b): 単調包含簿記** — m ≤ m' なら
    shell m ⊆ shell m'。垂直線に沿って対数殻は単調に容器に収まり
    続ける（(a) 部の (ii) 簿記）。逆向き（m' < m）の包含は
    **主張されない**（M205F-8 で反例）。 -/
theorem logKummer_shell_mono {V : VolumeTheory} {α : Type}
    {T : VerticalKummerTower V α} (h : LogKummerCompat T)
    {m m' : Int} (hmm : m ≤ m') : V.le (T.shell m) (T.shell m') :=
  logKummer_shell_mono_up h (m' - m).toNat m m' (by omega)

/-! ## M205F-6: (b)(c) 部の厳密両立（両側・望遠鏡合成） -/

/-- **補題 (M205F-6a): 上向き k 段の厳密両立** — m' = m + k なら
    frob m = frob m'。 -/
theorem logKummer_frob_const_up {V : VolumeTheory} {α : Type}
    {T : VerticalKummerTower V α} (h : LogKummerCompat T) :
    ∀ (k : Nat) (m m' : Int), m' = m + (k : Int) →
      T.frob m = T.frob m' := by
  intro k
  induction k with
  | zero =>
    intro m m' hm
    have hm' : m' = m + ((0 : Nat) : Int) := hm
    rw [show m' = m by omega]
  | succ k ih =>
    intro m m' hm
    have hm' : m' = m + ((k + 1 : Nat) : Int) := hm
    rw [show m' = m + (k : Int) + 1 by omega, ← h.strict (m + (k : Int))]
    exact ih m (m + (k : Int)) rfl

/-- **定理 (M205F-6b): (b)(c) 部は両側** — Frobenius 的データは
    垂直線**全体**で一定（等号は対称なので上下どちらの方向にも
    両立する）。(a) の ⊆-のみ（一方向）との対比が (Ind3) の内容。 -/
theorem logKummer_frob_const {V : VolumeTheory} {α : Type}
    {T : VerticalKummerTower V α} (h : LogKummerCompat T) (m m' : Int) :
    T.frob m = T.frob m' := by
  cases Int.le_total m m' with
  | inl hle => exact logKummer_frob_const_up h (m' - m).toNat m m' (by omega)
  | inr hle =>
    exact (logKummer_frob_const_up h (m - m').toNat m' m (by omega)).symm

/-! ## M205F-7: 格子垂直経路への接続（M3 との合流） -/

/-- **定理 (M205F-7a): 垂直経路に沿った log-Kummer 対応** —
    塔の列上の任意の純 log 経路（Θ-link 0 本の `Path 0 s t`）に
    沿って、(列は保存される) ∧ (対数殻は ⊆) ∧ (Frobenius 的データは
    厳密に等しい)。M3-2 `pure_log_same_col`・M205F-1 `path_row`・
    望遠鏡合成 M205F-5/6 の合流点。 -/
theorem logKummer_along_logPath {V : VolumeTheory} {α : Type}
    {T : VerticalKummerTower V α} (h : LogKummerCompat T)
    {s t : LatticeSite} (p : Path 0 s t) (hs : s.col = T.col) :
    t.col = T.col ∧ V.le (T.shell s.row) (T.shell t.row)
      ∧ T.frob s.row = T.frob t.row :=
  ⟨Eq.trans (pure_log_same_col p) hs,
   logKummer_shell_mono h (path_row p),
   logKummer_frob_const h s.row t.row⟩

/-- **経路全体の Ind3 データ (M205F-7b)** — 垂直経路 `Path 0 s t`
    全体が一つの上半両立 `UpperCompat`（lo = 始点の殻,
    hi = 終点の殻）を与える。ステップごとの Ind3（M205F-4）の
    経路への合成版。 -/
def logKummerPathCompat {V : VolumeTheory} {α : Type}
    {T : VerticalKummerTower V α} (h : LogKummerCompat T)
    {s t : LatticeSite} (p : Path 0 s t) : UpperCompat V :=
  ⟨T.shell s.row, T.shell t.row, logKummer_shell_mono h (path_row p)⟩

/-! ## M205F-8: (a) 部の真の一方向性（witness） -/

/-- Int モデル上の具体的な垂直 Kummer 塔: 列 0・殻 shell m = m
    （行が進むほど真に大きくなる領域）・Frobenius 側は自明。 -/
def m205fTower : VerticalKummerTower m202fVol Unit where
  col := 0
  shell := fun m => m
  frob := fun _ => ()

/-- witness 塔は log-Kummer 両立（(a): m ≤ m+1、(b)(c): 自明等号）。 -/
theorem m205fTower_compat : LogKummerCompat m205fTower :=
  { upper := fun m => by
      show (m : Int) ≤ m + 1
      omega
    strict := fun _ => rfl }

/-- **定理 (M205F-8): (a) 部は真に一方向** — log-Kummer 両立する塔で
    あって、逆包含 shell (m+1) ⊆ shell m が成り立たないものが
    存在する。(b)(c) の両側厳密両立と対照的に、(a) の ⊆ を等号へ
    強化することは不可能（M202F-4 `upper_compat_not_symm`・M5
    `strict_evaluation_obstruction` の塔版）。 -/
theorem logKummer_not_symm :
    ∃ (V : VolumeTheory) (T : VerticalKummerTower V Unit),
      LogKummerCompat T ∧ ∃ m : Int, ¬ V.le (T.shell (m + 1)) (T.shell m) :=
  ⟨m202fVol, m205fTower, m205fTower_compat, 0,
   fun hle => by
     have h01 : (0 : Int) + 1 ≤ 0 := hle
     omega⟩

/-! ## M205F-9: レベル 1 Kummer 核（単数分解 μ × U^(1) の再輸出） -/

/-- **レベル 1 Kummer 核** — x が Teichmüller 部 ω(a)（μ_{p−1} 側 =
    Kummer 理論の離散核）と主単数部 u（U^(1) 側）に分解すること。
    log-Kummer 対応の離散核データのレベル 1 具体化（M35 の語彙）。 -/
def Level1KummerKernel (p : Nat) (hp : IsPrime p) (x : (Zp p).carrier)
    (a : Int) : Prop :=
  ∃ u, IsPrincipalUnit p u ∧ x = zpMul p (teich p hp a) u

/-- **定理 (M205F-9a): 核の存在** — x ≡ a (mod p)・p ∤ a なら
    レベル 1 Kummer 核分解が存在する（M35-4 `unit_decomposition`
    の再輸出）。 -/
theorem level1_kummer_of_residue (p : Nat) (hp : IsPrime p)
    (x : (Zp p).carrier) {a : Int} (ha : ¬ ((p : Nat) : Int) ∣ a)
    (hx : x.val 1 = Quot.mk (modCong (p ^ 1)).rel a) :
    Level1KummerKernel p hp x a :=
  unit_decomposition p hp x ha hx

/-- **定理 (M205F-9b): 主単数部の一意性** — 同じ x の二つの核分解の
    主単数部は一致する（M35-5 `decomposition_unique` の再輸出）。
    Kummer 核の**離散性**（分解の剛性）の内容。 -/
theorem level1_kummer_unit_unique (p : Nat) (hp : IsPrime p) {a : Int}
    (ha : ¬ ((p : Nat) : Int) ∣ a) {x u u' : (Zp p).carrier}
    (hu : IsPrincipalUnit p u) (hu' : IsPrincipalUnit p u')
    (hxu : x = zpMul p (teich p hp a) u)
    (hxu' : x = zpMul p (teich p hp a) u') : u = u' := by
  have heq : zpMul p (teich p hp a) u = zpMul p (teich p hp a) u' := by
    rw [← hxu, ← hxu']
  exact (decomposition_unique p hp ha hu hu' heq).2

/-- 2 は 1 を割らない（witness 用の初等補題）。 -/
theorem two_not_dvd_one : ¬ ((2 : Nat) : Int) ∣ 1 := by
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hc' : (1 : Int) = ((2 : Nat) : Int) * c := hc
  omega

/-- **witness (M205F-9c)**: p = 2・x = 1・a = 1 のレベル 1 Kummer 核。 -/
theorem level1_kummer_one : Level1KummerKernel 2 isPrime_two (zpOne 2) 1 :=
  level1_kummer_of_residue 2 isPrime_two (zpOne 2) two_not_dvd_one rfl

/-! ## M205F-10: capstone — LogKummerData / def / exists -/

/-- **log-Kummer 対応の骨格データ**（Dα-4 の成果物）—
    log-Kummer 両立する垂直 Kummer 塔（(a) ⊆-のみ・(b)(c) 厳密）、
    (a) 部の真の一方向性 witness、およびレベル 1 Kummer 核
    （単数分解 μ × U^(1)）を束ねる。 -/
structure LogKummerData where
  /-- (a) 部の舞台: 体積理論。 -/
  V : VolumeTheory
  /-- (b)(c) 部のデータ型。 -/
  Frob : Type
  /-- 垂直 Kummer 塔。 -/
  T : VerticalKummerTower V Frob
  /-- log-Kummer 両立性（(a) ⊆-のみ・(b)(c) 厳密）。 -/
  compat : LogKummerCompat T
  /-- (a) 部の真の一方向性（逆包含の不成立 witness）。 -/
  one_sided : ∃ m : Int, ¬ V.le (T.shell (m + 1)) (T.shell m)
  /-- 離散核側の素数。 -/
  p : Nat
  /-- p の素数性。 -/
  hp : IsPrime p
  /-- 核分解される単数。 -/
  x : (Zp p).carrier
  /-- レベル 1 剰余。 -/
  a : Int
  /-- レベル 1 Kummer 核分解。 -/
  kernel : Level1KummerKernel p hp x a

/-- 標準 witness: Int モデルの塔 + p = 2 のレベル 1 核。 -/
def logKummerData : LogKummerData where
  V := m202fVol
  Frob := Unit
  T := m205fTower
  compat := m205fTower_compat
  one_sided := ⟨0, fun hle => by
    have h01 : (0 : Int) + 1 ≤ 0 := hle
    omega⟩
  p := 2
  hp := isPrime_two
  x := zpOne 2
  a := 1
  kernel := level1_kummer_one

/-- **定理 (M205F-10): log-Kummer 骨格データの存在** — Dα-4 の
    骨格（両立塔 + 一方向性 + レベル 1 核）は充足可能。 -/
theorem logKummer_exists : Nonempty LogKummerData :=
  ⟨logKummerData⟩

end IUT
