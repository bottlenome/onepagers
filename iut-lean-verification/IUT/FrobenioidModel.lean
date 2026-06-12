/-
  IUT/FrobenioidModel.lean — M51F（Frobenioid の圏論的実体と数体での充足）の形式化

  M12（IUT/Frobenioid.lean）は Frobenioid を「因子モノイド＋次数準同型 deg＋
  Frobenius 自己射 φ_n」というデータの束として公理化し、その無矛盾性を
  Div = ℤ という退化モデル（`frobenioid_consistent`）で示すに留まっていた。
  M48F（IUT/FrobenioidCat.lean）は次数 ℤ レベルの圏 `elementaryFrobenioid` を
  建設したが、対象は次数（一個の整数）であり**因子そのもの**ではなかった。
  dashboard の M12/M5 行が「未達」と申告している
  「Frobenioid の圏論的実体と実際の数体での充足」のうち、本モジュールは

  (A) **実際の数体（ℚ）型のデータでの充足**: 有効因子＝「素点での重複度の
      有限サポート関数」を実装し、重み付き次数（log-volume の整数化）の
      加法性・斉次性を完全証明して、M12 の `Frobenioid` 構造を
      `Nonempty`-witness ではなく**実データの実定理**として充足する。
  (B) **因子レベルの圏論的実体**: 有効因子そのものを対象とし、
      射 x → y = (Frobenius 次数 d ≥ 1, 有効因子 c) with y = d·x + c
      （点ごとの線形条件）とする圏 `divisorFrobenioid` を建設し、
      次数関手で M48F の `elementaryFrobenioid` に落とす。

  の二段で埋める。[FrdI] §1 の言葉では、(A) は因子モノイド Φ(Spec ℚ) =
  ⊕_p ℕ（素点ごとの有効因子）と次数 deg = Σ_p w(p)·ord_p の実装、(B) は
  base 圏が一点の場合の Frobenioid F_Φ（対象 = Φ の元、射 = Frobenius 次数と
  効果的因子の対）の実装である。

  ## 検証する定理（全て sorry なし・選択公理なし）

  ### Part 0: 有限和のインフラ
  * `nsum` — Σ_{k<n} g k の自前定義（core のみ、rsum 流）
  * `nsum_vanish` / `nsum_tail` — 消滅区間の切り落とし
  * `nsum_weight_add` / `nsum_weight_scale` — 重み付き和の加法性・斉次性

  ### Part 1: ℚ の有効因子と M12 の充足
  * `QDiv` — 有効因子型: 重複度関数 mult : ℕ → ℕ ＋ サポート上界 bound ＋
    消滅証明 vanish。k 番目の座標は「k 番目の素点 p_k での重複度」を表す
  * M51F-1 `qadd_assoc` / `qadd_comm` / `qzero_add` / `qadd_zero` —
    有効因子の可換モノイド法則（点ごと加法＋上界 max）の完全証明
  * M51F-2 `degN_add` / `degZ_add` — **重み付き次数の加法性**
    deg(x+y) = deg x + deg y。重み w : ℕ → ℕ は素点ごとの log-volume の
    整数化（log p_k に相当）をパラメータとして受ける
  * M51F-3 `degN_frob` / `degZ_frob` — **Frobenius の斉次性**
    deg(φ_e x) = e·deg x（φ_e = 重複度の点ごと e 倍）
  * M51F-4 `rationalFrobenioid` — **M12 の `Frobenioid` 構造の実データに
    よる充足**。全フィールド（add_assoc/add_comm/zero_add/deg_add/frob_deg）
    が上の定理で埋まる。`Nonempty` でなく def（公理ゼロのデータ）
  * M51F-5 `rational_frob_not_invertible` / `rational_gaussian_deg` —
    M12-3（Frobenius 非可逆性）・M12-5（Gaussian 次数公式）が
    実データ上で発動することの確認（一般定理の instantiation）
  * M51F-6 `intVolume` / `rationalDegVol` / `rational_qpilot_volume` —
    次数＝log-volume 両立データ `DegreeVolumeCompat` を rationalFrobenioid
    上で実構成し、M12-6 `frobenioid_realizes_qpilot` を**実データで発動**:
    任意の骨格 s に対し q-パイロット因子（単一素点・重み |log q|）の
    実現領域の体積が −|log q| になる（`vol_q` の供給経路の完全実体化）
  * M51F-7 `degZ_single_valuation` — 単一素点の因子の次数と局所類体論
    （M27、IUT/LocalCFT.lean）の付値 v : K^× → ℤ の整合:
    deg(単一素点因子 (k,m)) = w(k)·v(p_k^m·u)。大域次数 = Σ 局所付値×重み
    の単一素点版

  ### Part 2: 因子レベルの圏（圏論的実体）
  * M51F-8 `divisorFrobenioid` — **因子そのものを対象とする圏**:
    対象 = QDiv、射 x → y = (d ≥ 1, c : QDiv) with y = qadd (qfrob d x) c。
    恒等 (1, 0)・合成 (d₁,c₁)·(d₂,c₂) = (d₁d₂, d₂·c₁ + c₂)（M48F と同じ
    捻れ半直積型）の圏公理の完全証明。線形条件の保存は qfrob_add
    （Frobenius の加法分配）・qfrob_frob（Frobenius の合成）・qadd_assoc
    という**因子代数の構造定理**から従う
  * M51F-9 `divDegFunctor` — **次数関手** divisorFrobenioid →
    elementaryFrobenioid（M48F）: 対象は degZ w、射は (d, deg c)。
    線形条件の保存は M51F-2/3（deg の加法性・斉次性）そのもの。
    関手性（map_id・map_comp）の完全証明
  * M51F-10 `divisor_iso_objects_eq` — **因子レベルの非可逆性**:
    divisorFrobenioid の同型は因子を動かせない（x ≅ y ⟹ x = y）。
    M48F-4d `iso_objects_eq` の因子版で、しかも次数に落とさず
    因子そのもので成立する強い形。`divisor_hom_exists_but_no_iso` は
    具体的証人（0 → 単一素点因子に射はあるが同型はない）
  * M51F-11 `Functor.mapIso` / `divisor_iso_deg_eq` — 関手は同型を保つ
    （一般補題）＋ 次数関手による M48F への帰着（divisorFrobenioid の
    同型 ⟹ elementaryFrobenioid の同型 ⟹ 次数一致）

  ## 正直な申告（モデルと本物の差）

  * **「ℚ の有効因子」の実装**: 素点を添字 k : ℕ で番号付けし（k ↦ k 番目の
    素数 p_k）、重み w k を log p_k の整数化としてパラメータに取った。
    素数の枚挙そのもの・w k = ⌊log p_k⌋ という解析的内容は形式化していない
    （重みは任意の ℕ 値関数として抽象化。これは M12 以来の「realified 次数を
    ℤ で代用する」正規化規約の継続である）。アルキメデス素点・分数因子
    （realification）は未形式化。
  * **大域次数公式**: 本物の数体では deg = Σ_v log #(O/p_v)·ord_v で、
    積公式（主因子の次数 0）が効く。ここでは**有効**因子のみを扱うため
    主因子・積公式は現れない（[FrdI] の因子モノイド Φ も有効因子で良い）。
  * **圏論的実体の範囲**: divisorFrobenioid は base 圏が一点の場合の
    Frobenioid である。base 圏（素点の圏）上のファイバー構造・
    poly-isomorphism・分裂・realification は引き続き未形式化。ただし
    M12 の構造が要求する全データはここで実データから充足され、
    M48F の次数圏が本圏の「次数の影」であることが関手で機械検証された。
  * 選択公理・追加公理は不使用（全定理 propext/Quot.sound 以下。
    funext は Quot.sound から導出される core の定理であり追加公理ではない）。
-/
import IUT.Frobenioid
import IUT.FrobenioidCat
import IUT.LocalCFT

namespace IUT

universe u v u' v'

/-! ## Part 0: 有限和 nsum のインフラ

    omega は var×var の積を読めないため（規約3）、重み付き和の操作は
    全て束縛変数上の補題に切り出し、積項は rw（mul_add・mul_left_comm）で
    処理してから線形部分だけを omega / 加法補題に渡す。 -/

/-- 有限和 Σ_{k<n} g k（core のみの自前定義）。 -/
def nsum (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => nsum g n + g n

/-- 和の入れ替え (a+b)+(c+d) = (a+c)+(b+d)（自由変数のみ: omega 可）。 -/
theorem nat_add_shuffle (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by omega

/-- max の結合律（自由変数のみ: omega 可）。 -/
theorem nat_max_assoc (a b c : Nat) :
    max (max a b) c = max a (max b c) := by omega

/-- max の可換律。 -/
theorem nat_max_comm (a b : Nat) : max a b = max b a := by omega

/-- max 0 a = a。 -/
theorem nat_zero_max (a : Nat) : max 0 a = a := by omega

/-- max a 0 = a。 -/
theorem nat_max_zero (a : Nat) : max a 0 = a := by omega

/-- max a b = 0 なら a = 0。 -/
theorem nat_max_eq_zero_left {a b : Nat} (h : max a b = 0) : a = 0 := by
  omega

/-- 全項消滅なら和は 0。 -/
theorem nsum_vanish (g : Nat → Nat) (n : Nat)
    (h : ∀ k, k < n → g k = 0) : nsum g n = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show nsum g m + g m = 0
    rw [h m (Nat.lt_succ_self m),
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

/-- **尾部切り落とし**: g が a 以降で消滅するなら、a ≤ n の範囲で
    Σ_{k<n} g k = Σ_{k<a} g k（サポート上界を超える項は和に効かない）。 -/
theorem nsum_tail (g : Nat → Nat) (a n : Nat) (ha : a ≤ n)
    (h : ∀ k, a ≤ k → g k = 0) : nsum g n = nsum g a := by
  induction n with
  | zero =>
    have h0 : a = 0 := Nat.le_zero.mp ha
    rw [h0]
  | succ m ih =>
    cases Nat.eq_or_lt_of_le ha with
    | inl h1 => rw [h1]
    | inr h2 =>
      have ha' : a ≤ m := by omega
      show nsum g m + g m = nsum g a
      rw [h m ha', ih ha', Nat.add_zero]

/-- **重み付き和の加法性**: Σ w·(x+y) = Σ w·x + Σ w·y。
    積項 w k * (mx k + my k) は mul_add で分配してから加法を入れ替える。 -/
theorem nsum_weight_add (w mx my : Nat → Nat) (n : Nat) :
    nsum (fun k => w k * (mx k + my k)) n
      = nsum (fun k => w k * mx k) n + nsum (fun k => w k * my k) n := by
  induction n with
  | zero => rfl
  | succ j ih =>
    show nsum (fun k => w k * (mx k + my k)) j + w j * (mx j + my j)
        = (nsum (fun k => w k * mx k) j + w j * mx j)
          + (nsum (fun k => w k * my k) j + w j * my j)
    rw [ih, Nat.mul_add (w j) (mx j) (my j)]
    exact nat_add_shuffle _ _ _ _

/-- **重み付き和の斉次性**: Σ w·(e·x) = e · Σ w·x。
    積項 w j * (e * m j) = e * (w j * m j) は mul_left_comm。 -/
theorem nsum_weight_scale (w m : Nat → Nat) (e n : Nat) :
    nsum (fun k => w k * (e * m k)) n
      = e * nsum (fun k => w k * m k) n := by
  induction n with
  | zero => rfl
  | succ j ih =>
    show nsum (fun k => w k * (e * m k)) j + w j * (e * m j)
        = e * (nsum (fun k => w k * m k) j + w j * m j)
    rw [ih, Nat.mul_add e (nsum (fun k => w k * m k) j) (w j * m j),
      Nat.mul_left_comm (w j) e (m j)]

/-! ## Part 1: ℚ の有効因子と M12 の充足 -/

/-- **ℚ の有効因子**: 素点（k 番目の素数 p_k に対応する添字 k : ℕ）での
    重複度の有限サポート関数。サポート上界 `bound` を**データとして**持つ
    （存在命題でなくデータにすることで、deg の定義に選択公理が不要になる）。 -/
structure QDiv where
  /-- k 番目の素点での重複度 ord_{p_k}。 -/
  mult : Nat → Nat
  /-- サポートの上界（bound 以降の素点では重複度 0）。 -/
  bound : Nat
  /-- 有限サポート性の証明。 -/
  vanish : ∀ k, bound ≤ k → mult k = 0

/-- 有効因子の外延性: mult と bound が一致すれば等しい（vanish は Prop）。 -/
theorem QDiv.ext {x y : QDiv} (hm : x.mult = y.mult)
    (hb : x.bound = y.bound) : x = y := by
  cases x with | mk xm xb xv =>
  cases y with | mk ym yb yv =>
  have hm' : xm = ym := hm
  have hb' : xb = yb := hb
  subst hm'
  subst hb'
  rfl

/-- 自明因子 0。 -/
def qzero : QDiv where
  mult := fun _ => 0
  bound := 0
  vanish := fun _ _ => rfl

/-- 因子の和（点ごとの重複度の和、上界は max）。 -/
def qadd (x y : QDiv) : QDiv where
  mult := fun k => x.mult k + y.mult k
  bound := max x.bound y.bound
  vanish := fun k hk => by
    have h1 := x.vanish k (Nat.le_trans (Nat.le_max_left _ _) hk)
    have h2 := y.vanish k (Nat.le_trans (Nat.le_max_right _ _) hk)
    omega

/-- Frobenius 射 φ_e: 重複度の点ごと e 倍（因子の e 倍 = 直線束の e 乗）。 -/
def qfrob (e : Nat) (x : QDiv) : QDiv where
  mult := fun k => e * x.mult k
  bound := x.bound
  vanish := fun k hk => by rw [x.vanish k hk, Nat.mul_zero]

/-- **定理 (M51F-1a): 因子和の結合律**。 -/
theorem qadd_assoc (x y z : QDiv) :
    qadd (qadd x y) z = qadd x (qadd y z) :=
  QDiv.ext (funext fun k => Nat.add_assoc (x.mult k) (y.mult k) (z.mult k))
    (nat_max_assoc x.bound y.bound z.bound)

/-- **定理 (M51F-1b): 因子和の可換律**。 -/
theorem qadd_comm (x y : QDiv) : qadd x y = qadd y x :=
  QDiv.ext (funext fun k => Nat.add_comm (x.mult k) (y.mult k))
    (nat_max_comm x.bound y.bound)

/-- **定理 (M51F-1c): 左単位則** 0 + x = x。 -/
theorem qzero_add (x : QDiv) : qadd qzero x = x :=
  QDiv.ext (funext fun k => Nat.zero_add (x.mult k)) (nat_zero_max x.bound)

/-- **定理 (M51F-1d): 右単位則** x + 0 = x。 -/
theorem qadd_zero (x : QDiv) : qadd x qzero = x :=
  QDiv.ext (funext fun k => Nat.add_zero (x.mult k)) (nat_max_zero x.bound)

/-- φ_1 は恒等（Frobenius 構造のモノイド単位）。 -/
theorem qfrob_one (x : QDiv) : qfrob 1 x = x :=
  QDiv.ext (funext fun k => Nat.one_mul (x.mult k)) rfl

/-- φ_e は自明因子を固定する。 -/
theorem qfrob_zero (e : Nat) : qfrob e qzero = qzero :=
  QDiv.ext (funext fun _ => Nat.mul_zero e) rfl

/-- **Frobenius の加法分配**: φ_e(x + y) = φ_e(x) + φ_e(y)
    （因子モノイドの自己準同型性）。 -/
theorem qfrob_add (e : Nat) (x y : QDiv) :
    qfrob e (qadd x y) = qadd (qfrob e x) (qfrob e y) :=
  QDiv.ext (funext fun k => Nat.mul_add e (x.mult k) (y.mult k)) rfl

/-- **Frobenius の合成**: φ_{e₂}(φ_{e₁}(x)) = φ_{e₁e₂}(x)
    （Frobenius 構造が乗法モノイド ℕ の作用であること）。 -/
theorem qfrob_frob (e₁ e₂ : Nat) (x : QDiv) :
    qfrob e₂ (qfrob e₁ x) = qfrob (e₁ * e₂) x :=
  QDiv.ext
    (funext fun k =>
      (Nat.mul_left_comm e₂ e₁ (x.mult k)).trans
        (Nat.mul_assoc e₁ e₂ (x.mult k)).symm)
    rfl

/-- **重み付き次数**（ℕ 値）: deg_w(x) = Σ_{k < bound} w(k)·ord_{p_k}(x)。
    重み w(k) は k 番目の素点の log-volume の整数化（log p_k 相当）。 -/
def degN (w : Nat → Nat) (x : QDiv) : Nat :=
  nsum (fun k => w k * x.mult k) x.bound

/-- 次数の安定性: サポート上界を超えて和を取っても次数は変わらない
    （deg が表示（bound の選び方）に依存しないことの実質）。 -/
theorem degN_stable (w : Nat → Nat) (x : QDiv) (n : Nat)
    (hn : x.bound ≤ n) :
    nsum (fun k => w k * x.mult k) n = degN w x :=
  nsum_tail (fun k => w k * x.mult k) x.bound n hn
    (fun k hk => by
      show w k * x.mult k = 0
      rw [x.vanish k hk, Nat.mul_zero])

/-- **定理 (M51F-2a): 次数の加法性**（ℕ 値）—
    deg(x + y) = deg x + deg y。max 上界での和を分配し、
    両項を各自のサポート上界まで切り落とす。 -/
theorem degN_add (w : Nat → Nat) (x y : QDiv) :
    degN w (qadd x y) = degN w x + degN w y := by
  show nsum (fun k => w k * (x.mult k + y.mult k)) (max x.bound y.bound)
      = degN w x + degN w y
  rw [nsum_weight_add w x.mult y.mult (max x.bound y.bound),
    degN_stable w x (max x.bound y.bound) (Nat.le_max_left _ _),
    degN_stable w y (max x.bound y.bound) (Nat.le_max_right _ _)]

/-- **定理 (M51F-3a): 次数の斉次性**（ℕ 値）— deg(φ_e x) = e·deg x。 -/
theorem degN_frob (w : Nat → Nat) (e : Nat) (x : QDiv) :
    degN w (qfrob e x) = e * degN w x :=
  nsum_weight_scale w x.mult e x.bound

/-- 自明因子の次数は 0。 -/
theorem degN_zero (w : Nat → Nat) : degN w qzero = 0 := rfl

/-- 重み付き次数（ℤ 値。M12 の deg : Div → Int の正規化に合わせる）。 -/
def degZ (w : Nat → Nat) (x : QDiv) : Int :=
  (degN w x : Int)

/-- 次数の非負性（有効因子なので当然だが、次数関手の c_nonneg 供給源）。 -/
theorem degZ_nonneg (w : Nat → Nat) (x : QDiv) : 0 ≤ degZ w x :=
  Int.natCast_nonneg (degN w x)

/-- **定理 (M51F-2b): 次数の加法性**（ℤ 値）。 -/
theorem degZ_add (w : Nat → Nat) (x y : QDiv) :
    degZ w (qadd x y) = degZ w x + degZ w y := by
  show ((degN w (qadd x y) : Nat) : Int)
      = ((degN w x : Nat) : Int) + ((degN w y : Nat) : Int)
  rw [degN_add, Int.natCast_add]

/-- **定理 (M51F-3b): 次数の斉次性**（ℤ 値）— M12 の公理 frob_deg の形。 -/
theorem degZ_frob (w : Nat → Nat) (e : Nat) (x : QDiv) :
    degZ w (qfrob e x) = (e : Int) * degZ w x := by
  show ((degN w (qfrob e x) : Nat) : Int)
      = (e : Int) * ((degN w x : Nat) : Int)
  rw [degN_frob, Int.natCast_mul]

/-- 自明因子の次数は 0（ℤ 値）。 -/
theorem degZ_zero (w : Nat → Nat) : degZ w qzero = 0 :=
  Int.natCast_zero

/-- **定理 (M51F-4): M12 の `Frobenioid` 構造の実データによる充足** —
    ℚ の有効因子（QDiv）・点ごとの和・重み付き次数・点ごと e 倍の
    Frobenius が、M12 の全公理（add_assoc・add_comm・zero_add・
    deg_add・frob_deg）を**定理として**満たす。`frobenioid_consistent`
    （M12-7a）の退化モデル Div = ℤ と違い、因子は本当に素点ごとの
    重複度データであり、deg は本当に重み付き有限和である。 -/
def rationalFrobenioid (w : Nat → Nat) : Frobenioid where
  Div := QDiv
  add := qadd
  zero := qzero
  add_assoc := qadd_assoc
  add_comm := qadd_comm
  zero_add := qzero_add
  deg := degZ w
  deg_add := degZ_add w
  frob := qfrob
  frob_deg := degZ_frob w

/-- **定理 (M51F-5): 実データ上の Frobenius 非可逆性** —
    M12-3 `frob_not_invertible` が rationalFrobenioid で発動する:
    次数 ≠ 0 の有効因子は φ_n (n ≥ 2) の不動点にならない。 -/
theorem rational_frob_not_invertible (w : Nat → Nat) (n : Nat)
    (hn : 2 ≤ n) (x : QDiv) (hx : degZ w x ≠ 0) : qfrob n x ≠ x :=
  frob_not_invertible (rationalFrobenioid w) n hn x hx

/-- **定理 (M51F-5'): 実データ上の Gaussian 次数公式** —
    M12-5 `gaussianDiv_deg` の instantiation: テータ値束
    ⊕_{j=1}^{L} φ_{j²}(x) の次数 = (Σ j²)·deg x が実因子で成立。 -/
theorem rational_gaussian_deg (w : Nat → Nat) (x : QDiv) (L : Nat) :
    degZ w (gaussianDiv (rationalFrobenioid w) x L)
      = (sumSq L : Int) * degZ w x :=
  gaussianDiv_deg (rationalFrobenioid w) x L

/-! ### 次数＝log-volume 両立データの実構成（M12-6 の発動） -/

/-- 整数直線の体積理論（M12-7b の証明内で無名で使われたモデルの命名版）:
    Region = ℤ、包含 = ≤、hull = max、vol = id。 -/
def intVolume : VolumeTheory where
  Region := Int
  le := (· ≤ ·)
  le_refl := Int.le_refl
  le_trans := fun h1 h2 => Int.le_trans h1 h2
  hull := fun a b => max a b
  le_hull_left := fun a b => by omega
  le_hull_right := fun a b => by omega
  hull_least := fun h1 h2 => by omega
  vol := fun r => r
  vol_mono := fun h => h

/-- **定理 (M51F-6a): 次数＝log-volume 両立データの実構成** —
    rationalFrobenioid の因子を「体積 = −次数」の領域として実現する
    `DegreeVolumeCompat`（M12 の定理3.11 (i)(c) 骨格）の witness。 -/
def rationalDegVol (w : Nat → Nat) :
    DegreeVolumeCompat (rationalFrobenioid w) intVolume where
  realize := fun x => -(degZ w x)
  vol_realize := fun _ => rfl

/-- 単一素点の因子: k 番目の素点に重複度 m、他は 0（p_k^m に対応）。 -/
def singleDiv (k m : Nat) : QDiv where
  mult := fun j => if j = k then m else 0
  bound := k + 1
  vanish := fun j hj => if_neg (show ¬ j = k by omega)

/-- 単一素点因子の次数 = 重み × 重複度（deg(p_k^m) = w(k)·m）。
    if の条件 j = k は自由変数上の decEq なので if_pos rfl / if_neg で
    場合を固定してから和を評価する（規約3）。 -/
theorem degN_single (w : Nat → Nat) (k m : Nat) :
    degN w (singleDiv k m) = w k * m := by
  have hzero : nsum (fun j => w j * (if j = k then m else 0)) k = 0 :=
    nsum_vanish _ k (fun j hj => by
      show w j * (if j = k then m else 0) = 0
      rw [if_neg (show ¬ j = k by omega), Nat.mul_zero])
  show nsum (fun j => w j * (if j = k then m else 0)) k
      + w k * (if k = k then m else 0) = w k * m
  rw [hzero, if_pos rfl, Nat.zero_add]

/-- **定理 (M51F-6b): q-パイロットの体積実現の実データでの発動** —
    任意の骨格 s（|log q| > 0）に対し、重み w ≡ |log q| の
    rationalFrobenioid の単一素点因子 p_0^1 は次数 |log q| を持ち、
    M12-6 `frobenioid_realizes_qpilot` により体積 −|log q| の領域として
    実現される。M5 `MultiradialRep` の `vol_q` フィールドの供給経路が
    公理ゼロの実データで一気通貫したことの機械検証。 -/
theorem rational_qpilot_volume (s : Skeleton) :
    intVolume.vol
      ((rationalDegVol (fun _ => s.logq.toNat)).realize (singleDiv 0 1))
      = -s.logq := by
  have hdeg : (rationalFrobenioid (fun _ => s.logq.toNat)).deg (singleDiv 0 1)
      = s.logq := by
    show ((degN (fun _ => s.logq.toNat) (singleDiv 0 1) : Nat) : Int) = s.logq
    rw [degN_single, Nat.mul_one]
    exact Int.toNat_of_nonneg (Int.le_of_lt s.hq)
  exact frobenioid_realizes_qpilot (rationalFrobenioid (fun _ => s.logq.toNat))
    (rationalDegVol (fun _ => s.logq.toNat)) (singleDiv 0 1) hdeg

/-- **定理 (M51F-7): 局所付値との整合**（M27 接続・ボーナス）—
    単一素点因子 (k, m) の大域次数は、局所類体論モデル（IUT/LocalCFT.lean）
    の付値 v : K^× ≅ ℤ × O^× → ℤ が p_k^m·u（u は任意の単数部分）に
    与える値 m の w(k) 倍に一致する。「大域次数 = 重み × 局所付値」の
    単一素点版で、deg が本当に素点での ord の簿記であることの検証。 -/
theorem degZ_single_valuation (w : Nat → Nat) (U : Grp) (k m : Nat)
    (u : U.carrier) :
    degZ w (singleDiv k m)
      = (w k : Int) * (valuation U).map ((m : Int), u) := by
  show ((degN w (singleDiv k m) : Nat) : Int) = (w k : Int) * (m : Int)
  rw [degN_single, Int.natCast_mul]

/-! ## Part 2: 因子レベルの圏（圏論的実体） -/

/-- **因子レベルの Frobenioid の射**: x → y は Frobenius 次数 d ≥ 1 と
    有効因子 c の対で、線形条件 y = φ_d(x) + c を満たすもの
    （[FrdI] §1 の射 = (Frobenius 次数, 効果的因子 Div(φ)) の、
    base 圏一点の場合の忠実な実装。c は QDiv なので効果性
    （c ≥ 0）は型に内蔵されており、M48F の c_nonneg に相当する
    側条件が不要になる）。 -/
structure DivHom (x y : QDiv) where
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的因子部分 Div(φ)。 -/
  c : QDiv
  d_pos : 1 ≤ d
  /-- 線形条件: y = φ_d(x) + c（点ごとの ord の変換則）。 -/
  linear : y = qadd (qfrob d x) c

/-- 射の外延性: DivHom は (d, c) 成分で決まる（linear は Prop）。 -/
theorem DivHom.ext {x y : QDiv} {f g : DivHom x y}
    (hd : f.d = g.d) (hc : f.c = g.c) : f = g := by
  cases f with | mk fd fc f1 f2 =>
  cases g with | mk gd gc g1 g2 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  subst hd'
  subst hc'
  rfl

/-- 恒等射の線形条件: x = φ_1(x) + 0。 -/
theorem div_id_linear (x : QDiv) : x = qadd (qfrob 1 x) qzero := by
  rw [qfrob_one, qadd_zero]

/-- 合成射の線形条件: y = φ_a(x) + c₁, z = φ_b(y) + c₂ なら
    z = φ_{ab}(x) + (φ_b(c₁) + c₂)。M48F の捻れ半直積型合成則の
    因子版で、算術核は qfrob_add（分配）・qfrob_frob（作用）・
    qadd_assoc（結合）という因子代数の構造定理。 -/
theorem div_comp_linear {a b : Nat} {x y z c₁ c₂ : QDiv}
    (h₁ : y = qadd (qfrob a x) c₁) (h₂ : z = qadd (qfrob b y) c₂) :
    z = qadd (qfrob (a * b) x) (qadd (qfrob b c₁) c₂) := by
  rw [h₂, h₁, qfrob_add, qfrob_frob, qadd_assoc]

/-- **定理 (M51F-8): 因子レベルの Frobenioid 圏** — 対象 = ℚ の有効因子、
    射 = (Frobenius 次数, 効果的因子) with 線形条件。恒等 (1, 0)、
    合成 (d₁,c₁)·(d₂,c₂) = (d₁d₂, φ_{d₂}(c₁) + c₂)。M48F の
    elementaryFrobenioid（対象 = 次数 ℤ）の一段上の実体であり、
    圏公理は因子モノイドの構造定理（M51F-1, qfrob_*）から完全証明される。 -/
def divisorFrobenioid : Cat where
  Obj := QDiv
  Hom := DivHom
  id := fun x => ⟨1, qzero, Nat.le_refl 1, div_id_linear x⟩
  comp := fun f g =>
    ⟨f.d * g.d, qadd (qfrob g.d f.c) g.c,
      Nat.mul_pos f.d_pos g.d_pos,
      div_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    DivHom.ext (Nat.one_mul f.d)
      (by show qadd (qfrob f.d qzero) f.c = f.c
          rw [qfrob_zero, qzero_add])
  comp_id := fun f =>
    DivHom.ext (Nat.mul_one f.d)
      (by show qadd (qfrob 1 f.c) qzero = f.c
          rw [qfrob_one, qadd_zero])
  assoc := fun f g h =>
    DivHom.ext (Nat.mul_assoc f.d g.d h.d)
      (by show qadd (qfrob h.d (qadd (qfrob g.d f.c) g.c)) h.c
            = qadd (qfrob (g.d * h.d) f.c) (qadd (qfrob h.d g.c) h.c)
          rw [qfrob_add, qfrob_frob, qadd_assoc])

/-- 圏の中の純 Frobenius 射 x → φ_e(x)（次数 e、因子部分 0）。 -/
def divFrobMor (e : Nat) (he : 1 ≤ e) (x : QDiv) :
    DivHom x (qfrob e x) :=
  ⟨e, qzero, he, (qadd_zero (qfrob e x)).symm⟩

/-- **定理 (M51F-9): 次数関手** divisorFrobenioid → elementaryFrobenioid —
    対象（因子）を次数 degZ w に、射 (d, c) を (d, deg c) に送る対応は
    関手である。線形条件の保存は次数の加法性（M51F-2）と斉次性
    （M51F-3）そのもの。M48F の次数圏が本圏の「次数の影」であること、
    つまり M48F の elementary Frobenioid が一般の因子 Frobenioid から
    次数関手で誘導されることの機械検証。 -/
def divDegFunctor (w : Nat → Nat) :
    Functor divisorFrobenioid elementaryFrobenioid where
  onObj := fun x => degZ w x
  onHom := fun {x y} f =>
    { d := f.d
      c := degZ w f.c
      d_pos := f.d_pos
      c_nonneg := degZ_nonneg w f.c
      linear := by
        have h : degZ w y = degZ w (qadd (qfrob f.d x) f.c) :=
          congrArg (degZ w) f.linear
        rw [degZ_add, degZ_frob] at h
        exact h }
  map_id := fun x => FrobHom.ext rfl (degZ_zero w)
  map_comp := fun f g =>
    FrobHom.ext rfl
      (by show degZ w (qadd (qfrob g.d f.c) g.c)
            = (g.d : Int) * degZ w f.c + degZ w g.c
          rw [degZ_add, degZ_frob])

/-- **補題 (M51F-11a): 関手は同型を保つ**(一般の圏論補題)。 -/
def Functor.mapIso {C : Cat.{u, v}} {D : Cat.{u', v'}} (F : Functor C D)
    {X Y : C.Obj} (i : CatIso C X Y) :
    CatIso D (F.onObj X) (F.onObj Y) where
  hom := F.onHom i.hom
  inv := F.onHom i.inv
  hom_inv := by rw [← F.map_comp, i.hom_inv, F.map_id]
  inv_hom := by rw [← F.map_comp, i.inv_hom, F.map_id]

/-- **定理 (M51F-10): 因子レベルの非可逆性** — divisorFrobenioid の
    同型は因子を動かせない: x ≅ y ⟹ x = y。M48F-4d `iso_objects_eq`
    （次数レベル）の因子版で、次数に落とさず因子そのもので成立する
    強い形。証明: 合成 = 恒等から d 成分の積 = 1（よって両方 1）、
    c 成分の和 = 0（よって上界 0 = 自明因子）、線形条件に代入して
    y = φ_1(x) + 0 = x。Frobenioid が「進むだけで戻れない」圏である
    こと（Frobenius-like / étale-like 二分法）の因子レベルの実体。 -/
theorem divisor_iso_objects_eq {x y : QDiv}
    (i : CatIso divisorFrobenioid x y) : x = y := by
  -- d 成分: hom.d * inv.d = 1 から hom.d = 1
  have hd1 : i.hom.d = 1 :=
    frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos
      (congrArg DivHom.d i.hom_inv)
  -- c 成分: φ_{inv.d}(hom.c) + inv.c = 0 から hom.c の上界が 0
  have hc : qadd (qfrob i.inv.d i.hom.c) i.inv.c = qzero :=
    congrArg DivHom.c i.hom_inv
  have hb : max i.hom.c.bound i.inv.c.bound = 0 :=
    congrArg QDiv.bound hc
  have hb0 : i.hom.c.bound = 0 := nat_max_eq_zero_left hb
  -- 上界 0 の有効因子は自明因子
  have hczero : i.hom.c = qzero :=
    QDiv.ext
      (funext fun k => i.hom.c.vanish k (by rw [hb0]; exact Nat.zero_le k))
      hb0
  -- 線形条件 y = φ_1(x) + 0 = x
  have hl := i.hom.linear
  rw [hd1, hczero, qfrob_one, qadd_zero] at hl
  exact hl.symm

/-- **定理 (M51F-11b): 次数関手による M48F への帰着** —
    divisorFrobenioid の同型は次数関手で elementaryFrobenioid の同型に
    送られ、M48F-4d `iso_objects_eq` により次数の一致が従う
    （M51F-10 を経由しない独立の経路。一般 Frobenioid の非可逆性が
    次数関手を通して elementary な場合に帰着する型の主張の実演）。 -/
theorem divisor_iso_deg_eq (w : Nat → Nat) {x y : QDiv}
    (i : CatIso divisorFrobenioid x y) : degZ w x = degZ w y :=
  iso_objects_eq (Functor.mapIso (divDegFunctor w) i)

/-- **定理 (M51F-10'): 射はあるが同型はない**（具体的証人）—
    自明因子 0 から単一素点因子 p_0 へは射 (1, p_0) が存在するが、
    同型は存在しない。M48F-4e `hom_exists_but_no_iso` の因子版。 -/
theorem divisor_hom_exists_but_no_iso :
    Nonempty (DivHom qzero (singleDiv 0 1))
      ∧ ¬ Nonempty (CatIso divisorFrobenioid qzero (singleDiv 0 1)) := by
  constructor
  · exact ⟨⟨1, singleDiv 0 1, Nat.le_refl 1,
      by rw [qfrob_one, qzero_add]⟩⟩
  · intro ⟨i⟩
    have h : qzero = singleDiv 0 1 := divisor_iso_objects_eq i
    have h0 : (0 : Nat) = 1 := congrArg (fun z => QDiv.mult z 0) h
    omega

/-- **定理 (M51F-9'): 次数関手は純 Frobenius 射を M48F の frobMor の
    データに送る** — divFrobMor e の像の Frobenius 次数は e、
    因子部分は 0（次数関手が [FrdI] の deg_Fr 簿記と整合すること）。 -/
theorem divDeg_frobMor (w : Nat → Nat) (e : Nat) (he : 1 ≤ e) (x : QDiv) :
    ((divDegFunctor w).onHom (divFrobMor e he x)).d = e
      ∧ ((divDegFunctor w).onHom (divFrobMor e he x)).c = 0 :=
  ⟨rfl, degZ_zero w⟩

end IUT
