/-
  IUT/LogThetaLattice.lean — M3（log-theta 格子と Θ-link / log-link）の形式化

  IUT III §1 の log-theta-lattice の組合せ骨格を形式化する。

  格子の頂点は Θ±ellNF-Hodge theater のラベル (n, m) ∈ ℤ²:
  * 垂直方向の log-link (n,m) → (n,m+1) は **同一の数論的正則構造**
    （同一の環構造 = 同一の列 n）の内部で対数を取る操作
  * 水平方向の Θ-link (n,m) → (n+1,m) は **異なる数論的正則構造**
    （異なる列）への移行であり、環構造を保たない
    （乗法的モノイドの同型のみ。IUT III Remark 1.2.2 ほか）

  証明する構造定理（すべて sorry なし）:
  * M3-1 `path_col`: 任意のリンク経路で
        終点の列 = 始点の列 + （経路中の Θ-link の本数）
  * M3-2 `pure_log_same_col`: log-link だけの経路は列を保つ
  * M3-3 `cross_col_needs_theta`: **列が異なる 2 頂点を結ぶ経路は
    必ず Θ-link を通過する**。「異なる正則構造の比較は環構造を
    保たないリンクを経由せざるを得ない」——多輻的表現（定理3.11）
    が必要になる理由——の組合せ的内容
  * M3-4 `invariant_col_blind` / `col_not_invariant`:
    リンク不変量（Θ-link をまたいで通用するデータ = mono-analytic
    な構造）は列を区別できず、列ラベル（環構造）自体はリンク
    不変量に **なれない**

  未形式化: 各頂点に載る実データ（Frobenioid、prime-strip）と
  log-link の非線形性（log-Kummer 対応）。これらは M5 に属する。
-/

namespace IUT

/-- log-theta 格子の頂点: Hodge theater のラベル (col, row)。
    col = Θ 方向（数論的正則構造を区別する）、row = log 方向。 -/
structure LatticeSite where
  col : Int
  row : Int

/-- 格子のリンク（有向辺）。 -/
inductive Link : LatticeSite → LatticeSite → Prop
  /-- log-link: 同一列の内部で row を 1 進める（正則構造を保つ）。 -/
  | log (n m : Int) : Link ⟨n, m⟩ ⟨n, m + 1⟩
  /-- Θ-link: 列を 1 進める（正則構造を変える）。 -/
  | theta (n m : Int) : Link ⟨n, m⟩ ⟨n + 1, m⟩

/-- リンク経路。添字 k は経路中の **Θ-link の通過本数**。 -/
inductive Path : Nat → LatticeSite → LatticeSite → Prop
  /-- 空経路。Θ-link 0 本。 -/
  | nil (s : LatticeSite) : Path 0 s s
  /-- log-link を 1 本進めて続ける（Θ 本数は不変）。 -/
  | log {k : Nat} {u : LatticeSite} (n m : Int) :
      Path k ⟨n, m + 1⟩ u → Path k ⟨n, m⟩ u
  /-- Θ-link を 1 本進めて続ける（Θ 本数 +1）。 -/
  | theta {k : Nat} {u : LatticeSite} (n m : Int) :
      Path k ⟨n + 1, m⟩ u → Path (k + 1) ⟨n, m⟩ u

/-- **定理 (M3-1): 列の変化は Θ-link の通過本数を正確に数える**。
    終点の列 = 始点の列 + k。 -/
theorem path_col {k : Nat} {s t : LatticeSite} (p : Path k s t) :
    t.col = s.col + k := by
  induction p with
  | nil s => simp
  | log n m _ ih => simpa using ih
  | theta n m _ ih =>
    simp at ih ⊢
    omega

/-- **定理 (M3-2): log-link だけの経路（Θ 本数 0）は列を保つ**。
    すなわち log-リンクの反復（log-Kummer 対応の舞台）は
    一つの数論的正則構造の内部に留まる。 -/
theorem pure_log_same_col {s t : LatticeSite} (p : Path 0 s t) :
    t.col = s.col := by
  have := path_col p
  omega

/-- **定理 (M3-3): 列をまたぐ経路は必ず Θ-link を通過する**。
    異なる数論的正則構造に属する 2 つの Hodge theater を結ぶには、
    環構造を保たない Θ-link を最低 1 回通らねばならない。
    これが「Θ-link の両側の比較には環構造に依らない（多輻的な）
    入れ物が必要」という定理3.11 の出発点の組合せ的内容である。 -/
theorem cross_col_needs_theta {k : Nat} {s t : LatticeSite}
    (p : Path k s t) (h : s.col ≠ t.col) : 1 ≤ k := by
  have := path_col p
  omega

/-- リンク不変量: すべてのリンクで値が変わらないラベル付け。
    「Θ-link・log-link をまたいで通用するデータ」の抽象化
    （IUT の用語では mono-analytic な構造に対応）。 -/
def LinkInvariant {α : Type} (f : LatticeSite → α) : Prop :=
  ∀ s t : LatticeSite, Link s t → f s = f t

/-- **定理 (M3-4a): リンク不変量は列を区別できない**。
    Θ-link をまたいで通用するデータは、どの数論的正則構造に
    属していたかを覚えていられない（mono-analytic 化）。 -/
theorem invariant_col_blind {α : Type} {f : LatticeSite → α}
    (hinv : LinkInvariant f) (n m : Int) :
    f ⟨n, m⟩ = f ⟨n + 1, m⟩ :=
  hinv _ _ (Link.theta n m)

/-- **定理 (M3-4b): 列ラベル（環構造の所属）自体はリンク不変量に
    なれない**。環構造そのものを Θ-link 越しに持ち運ぶことは
    形式的に不可能で、可能なのは列に依らないデータのみ。 -/
theorem col_not_invariant : ¬LinkInvariant LatticeSite.col := by
  intro h
  have := h ⟨0, 0⟩ ⟨1, 0⟩ (Link.theta 0 0)
  simp at this

/-- 検算: (0,0) から log → Θ → log で (1,2) に到達する経路は
    Θ-link をちょうど 1 本含む。 -/
example : Path 1 ⟨0, 0⟩ (⟨1, 2⟩ : LatticeSite) :=
  Path.log 0 0 (Path.theta 0 1 (Path.log 1 1 (Path.nil _)))

/-! ## 経路の構成と格子の連結性（生成性） -/

/-- **定理 (M3-7): 同一列内の log 経路** — log-link だけで
    (n,a) から (n,a+k) へ到達できる（Θ-link 0 本）。 -/
theorem path_log_up (n : Int) :
    ∀ (k : Nat) (a : Int), Path 0 (⟨n, a⟩ : LatticeSite) ⟨n, a + (k : Int)⟩ := by
  intro k
  induction k with
  | zero =>
    intro a
    simpa using Path.nil (⟨n, a⟩ : LatticeSite)
  | succ k ih =>
    intro a
    have base : Path 0 (⟨n, a⟩ : LatticeSite) ⟨n, (a + 1) + (k : Int)⟩ :=
      Path.log n a (ih (a + 1))
    rwa [show (a + 1) + (k : Int) = a + ((k + 1 : Nat) : Int) by omega] at base

/-- **定理 (M3-8): Θ-link 1 本で隣の列へ**。 -/
theorem path_theta_step (n m : Int) :
    Path 1 (⟨n, m⟩ : LatticeSite) ⟨n + 1, m⟩ :=
  Path.theta n m (Path.nil _)

/-- **定理 (M3-9): 前方単位到達** — (n,m) から次の列の任意の行
    (n+1, m′) へ Θ-link ちょうど 1 本で到達できる（m ≤ m′）。
    まず Θ-link で列を渡り、次の列の内部を log-link で上る。
    格子が Θ・log の合成で前方連結であることの単位ステップ。 -/
theorem path_forward_step (n m m' : Int) (h : m ≤ m') :
    Path 1 (⟨n, m⟩ : LatticeSite) ⟨n + 1, m'⟩ := by
  -- (n,m) →θ→ (n+1,m) →log→ (n+1,m′)
  have inner : Path 0 (⟨n + 1, m⟩ : LatticeSite) ⟨n + 1, m'⟩ := by
    have := path_log_up (n + 1) (m' - m).toNat m
    rwa [show m + ((m' - m).toNat : Int) = m' by omega] at this
  exact Path.theta n m inner

/-! ## コア性（coricity）: IUT III 定理1.5 の骨格

「垂直コア性」= log-link で不変なデータは各列（一つの数論的
正則構造）の内部で一定であり、その列の **コア** をなす。
「双コア性」= log-link と Θ-link の両方で不変なデータ
（mono-analytic core）は格子全体で一意である。 -/

/-- log-link 不変量（垂直方向のみの不変性）。 -/
def LogInvariant {α : Type} (f : LatticeSite → α) : Prop :=
  ∀ n m : Int, f ⟨n, m⟩ = f ⟨n, m + 1⟩

/-- **定理 (M3-5): 垂直コア性**（定理1.5 (i) の骨格）—
    log-link 不変量は各列の内部で一定。すなわち一つの数論的
    正則構造に属する Hodge theater たちは共通の「コア」を持つ。 -/
theorem vertical_coricity {α : Type} {f : LatticeSite → α}
    (h : LogInvariant f) : ∀ n m : Int, f ⟨n, m⟩ = f ⟨n, 0⟩ := by
  have up : ∀ (n : Int) (k : Nat), f ⟨n, (k : Int)⟩ = f ⟨n, 0⟩ := by
    intro n k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show ((k + 1 : Nat) : Int) = (k : Int) + 1 by omega, ← h n (k : Int)]
      exact ih
  have down : ∀ (n : Int) (k : Nat), f ⟨n, -(k : Int)⟩ = f ⟨n, 0⟩ := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [h n (-((k + 1 : Nat) : Int)),
          show (-((k + 1 : Nat) : Int) + 1) = -(k : Int) by omega]
      exact ih
  intro n m
  rcases Int.le_total 0 m with hm | hm
  · rw [show m = ((m.toNat : Nat) : Int) by omega]
    exact up n m.toNat
  · rw [show m = -(((-m).toNat : Nat) : Int) by omega]
    exact down n (-m).toNat

/-- **定理 (M3-6): 双コア性**（定理1.5 (iii) の骨格）—
    log-link と Θ-link の両方で不変なデータ（mono-analytic core、
    例えば F⊢×μ-prime-strip の同型類）は格子全体で一意である。
    Θ-link をまたいで「共有」できる構造の一意性の形式化。 -/
theorem bicoric_constant {α : Type} {f : LatticeSite → α}
    (h : LinkInvariant f) : ∀ s t : LatticeSite, f s = f t := by
  have hlog : LogInvariant f := fun n m => h _ _ (Link.log n m)
  have hcol : ∀ n : Int, f ⟨n, 0⟩ = f ⟨n + 1, 0⟩ :=
    fun n => h _ _ (Link.theta n 0)
  have hup : ∀ k : Nat, f ⟨(k : Int), 0⟩ = f ⟨0, 0⟩ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show ((k + 1 : Nat) : Int) = (k : Int) + 1 by omega, ← hcol (k : Int)]
      exact ih
  have hdown : ∀ k : Nat, f ⟨-(k : Int), 0⟩ = f ⟨0, 0⟩ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hcol (-((k + 1 : Nat) : Int)),
          show (-((k + 1 : Nat) : Int) + 1) = -(k : Int) by omega]
      exact ih
  have horiz : ∀ n : Int, f ⟨n, 0⟩ = f ⟨0, 0⟩ := by
    intro n
    rcases Int.le_total 0 n with hn | hn
    · rw [show n = ((n.toNat : Nat) : Int) by omega]
      exact hup n.toNat
    · rw [show n = -(((-n).toNat : Nat) : Int) by omega]
      exact hdown (-n).toNat
  intro s t
  obtain ⟨n, m⟩ := s
  obtain ⟨n', m'⟩ := t
  rw [vertical_coricity hlog n m, vertical_coricity hlog n' m',
      horiz n, horiz n']

end IUT
