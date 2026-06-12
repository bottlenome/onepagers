/-
  IUT/DecompositionInertia.lean — M65F（複数素点への分解・惰性: efg 簿記）の形式化

  ## 動機

  [FrdI] §1 の Frobenioid の base 圏（数体の素点の圏）の射は、体拡大 L/K に
  沿って K の素点 v が L の**複数の**素点 w₁, …, w_g に枝分かれするデータを
  運ぶ: 各 w_k は分岐指数 e_k と剰余次数 f_k を持ち、基本恒等式

      Σ_{k<g} e_k · f_k = [L : K]

  が成り立つ。因子の**引き戻し**では v での重複度 m が各 w_k に e_k·m として
  配られ、**押し出し（ノルム）**では w_k での重複度が剰余次数 f_k の重みで
  集約される。よって「引き戻して押し出すと次数は [L:K] 倍」という次数簿記が
  efg 恒等式そのものとして従う。

  ところが既存の形式化は M61F（IUT/RamifiedBase.lean）が dashboard で
  正直に申告している通り「base は一本の塔（分岐指数 e のみ）であり、
  **複数素点への分解（分解数 g）・惰性（剰余次数 f）は未形式化**」だった
  （M57F の離散 base も素点間の枝分かれを持たない）。本モジュールは
  この「未達」を、一段の拡大 L/K・一つの下流素点 v の上のファイバーの
  範囲で埋める:

  * **拡大データ** `ExtData`（分解数 g ≥ 1、各 k < g の分岐指数 e k ≥ 1・
    剰余次数 f k ≥ 1）と efg 和 `efSum E = Σ_{k<g} e_k·f_k`。
    惰性的（g = 1, e = 1, f = n）・完全分解（g = n, e = f = 1）・
    完全分岐（g = 1, e = n, f = 1）の3つの具体例と Σef = n の検証
  * **半局所圏** `semiLocalFrobenioid`（v の上のファイバー: 対象 =
    w_k ごとの重複度ベクトル Nat → Nat、射 = (d ≥ 1, c : Nat → Nat) with
    成分ごとの線形条件 m' k = d·m k + c k。Frobenius 次数は全成分共通・
    効果的因子は成分ごと）の圏公理完全証明
  * **引き戻し関手** `decompPullback` : localFrobenioid →
    semiLocalFrobenioid（m ↦ (k ↦ e_k·m)、(d, c) ↦ (d, k ↦ e_k·c)。
    v での因子が各 w_k に分岐指数倍で配られる）
  * **ノルム次数** `normDeg E m' = Σ_{k<g} f_k·m'_k`（剰余次数を重みと
    する押し出しの次数簿記）の加法性・Frobenius 斉次性・線形性
  * **efg 恒等式** `efg_identity` : normDeg(引き戻し) = (Σ e_k·f_k)·m —
    [FrdI] の Σe_kf_k = [L:K] 簿記の機械検証。3つの具体例での発動
  * **押し出し関手** `normFunctor` : semiLocalFrobenioid →
    localFrobenioid（m' ↦ normDeg E m'、(d, c) ↦ (d, normDeg E c)）の
    関手性（線形条件の保存 = normDeg の線形性）
  * **合成定理** `norm_pullback_obj` / `norm_pullback_hom_d/c` :
    Σef = n のもとで「ノルム ∘ 引き戻し」は M61F の `pullbackFunctor n`
    （n 倍関手）と対象・射の両成分で一致 — **「引き戻して押し出すと
    次数は [L:K] 倍」の関手レベルの機械検証**
  * **剛性** — 半局所圏の同型は d = 1・c = 0（全成分）を強制し対象を
    動かせない（gaunt・IsoUnique・rigid）。ファイバーをベクトル化しても
    Frobenius-like 剛性（poly-isomorphism = 単集合）は保たれる

  ## efg 恒等式の紙上検証（実装前の算術核）

  normDeg E (k ↦ e_k·m) = Σ_{k<g} f_k·(e_k·m)
    = Σ_{k<g} (e_k·f_k)·m   （束縛変数上の並べ替え f·(e·m) = (e·f)·m、
                              `efg_mul_swap` — omega は var×var 不可なので
                              Nat.mul_assoc/mul_comm の rw で証明: 規約3）
    = (Σ_{k<g} e_k·f_k)·m   （右係数の括り出し `nsum_mul_right`、
                              Nat.add_mul の分配で帰納証明）
  既存の nsum_weight_scale は Σ w·(e·x) = e·Σ w·x（係数が k に依存しない
  左係数）の形であり、ここで必要なのは**係数 e_k·f_k が k に依存する**
  右括り出しなので新補題 `nsum_mul_right` を加えた（nsum_weight_scale は
  normDeg の Frobenius 斉次性 `normDeg_frob` でそのまま使う）。

  ## 検証する定理（全て sorry なし・選択公理なし）

  * M65F-0 `nsum_congr` / `nsum_mul_right` / `nsum_one` / `efg_mul_swap`
    — nsum インフラの追加（区間限定の項別書き換え・右係数の括り出し）
  * M65F-1 `ExtData` / `efSum` / `inertExt` / `splitExt` / `ramifiedExt`
    と各 `*_sum`（Σef = n の検証） — 拡大データと3つの具体例
  * M65F-2 `SemiLocalHom` / `SemiLocalHom.ext` / `semiLocalFrobenioid`
    — v 上のファイバーの圏の圏公理完全証明（成分ごとに M57F の
    local_* 補題を再利用、合成は捻れ半直積型 (d₁d₂, k ↦ d₂c₁ₖ+c₂ₖ)）
  * M65F-3 `decompPullback` — 引き戻し関手の線形条件の保存
    （M61F の pullback_linear の成分版）と関手性（pullback_comp_c）
  * M65F-4 `normDeg` / `normDeg_zero` / `normDeg_add` / `normDeg_frob` /
    `normDeg_linear` — ノルム次数の加法性（nsum_weight_add）・
    Frobenius 斉次性（nsum_weight_scale）・線形性（両者の合成）
  * M65F-5 `efg_identity` / `efg_deg` / `efg_pullback` /
    `inert_efg` / `split_efg` / `ramified_efg` — **efg 恒等式**:
    normDeg E (k ↦ e_k·m) = (Σ_{k<g} e_k·f_k)·m、Σef = n なら = n·m。
    3つの具体例での発動（惰性: n·m、完全分解: n 個の和、完全分岐: n 倍）
  * M65F-6 `normFunctor` — 押し出し関手（線形条件の保存 = normDeg_linear、
    合成の保存も同じ補題: normDeg(k ↦ d₂c₁ₖ+c₂ₖ) = d₂·normDeg c₁ +
    normDeg c₂）
  * M65F-7 `norm_pullback_obj` / `norm_pullback_hom_d` /
    `norm_pullback_hom_c` — **合成 = n 倍関手**: Σef = n のもとで
    (normFunctor E) ∘ (decompPullback E) は M61F の pullbackFunctor n と
    対象（n·m）・射の両成分（d ↦ d、c ↦ n·c）で一致
  * M65F-8 `semiLocal_iso_d_one` / `semiLocal_iso_c_zero` /
    `semiLocal_iso_objects_eq` / `semiLocalFrobenioid_gaunt` /
    `semiLocal_iso_unique` / `semiLocal_rigid` — 剛性: 同型は d = 1・
    c = 0（全成分、funext 越しの読み出しは congrFun で成分ごと）を
    強制し対象を動かせない。gaunt・IsoUnique・CatIso の一意性まで完備

  ## 正直な申告（モデルと本物の差）

  * **一段の拡大のみ**: 本モジュールは一つの拡大 L/K・一つの下流素点 v の
    上のファイバーを扱う。塔との合成（M61F の towerCat の各射に ExtData を
    乗せて枝分かれが段ごとに起こる「樹状の base 圏」、分解の推移性
    e(M/K) = e(M/L)·e(L/K) 型の efg データの合成則）は未形式化。
  * **e, f, g は抽象データ**: 分解数 g・分岐指数 e_k・剰余次数 f_k は
    `ExtData` として公理的に与えられ、実際の体拡大（剰余体の拡大次数・
    付値の延長の枚挙）から計算されない。Σef = [L:K] も**仮定**（hn）として
    受け、基本恒等式そのものの証明（[Neukirch I §8] 型）は未形式化——
    ここで機械検証したのはこの簿記が因子の引き戻し・押し出しと**整合する**
    ことである。
  * **剰余次数の「重み」としての実装**: 本物の次数理論では
    log #(O_L/w_k) = f_k · log #(O_K/v) であり、ノルム次数の重み f_k は
    この対数体積の比から来る。ここでは f_k は重み付き和の抽象的な重みで
    あり、剰余体の濃度・対数体積との接続（M51F の degN の重み w と同様の
    正規化規約）は簿記としてのみ形式化した。
  * **単数なし**: M63F の単数つき全空間圏との合成（分解・惰性 + 単数 =
    [FrdI] の完全な射データ）・イデール的な大域化（全素点で同時に
    分解データを張る）は未形式化。
  * **半局所対象のサポート**: 対象は裸の Nat → Nat であり「k ≥ g の成分は
    無意味（normDeg は k < g しか見ない）」という打ち切り規約で運用する。
    商型（k ≥ g を同一視）にしないため、対象の等号は g までの一致より
    細かい。`semiLocalFrobenioid` が ExtData を引数に取るのはファイバーの
    解釈（どの v の上か・成分の個数 g）を型に記録するためで、圏の
    データ自体は E に依存しない（依存するのは関手 decompPullback /
    normFunctor と normDeg）。
  * 選択公理・追加公理は不使用（全定理 propext/Quot.sound 以下。
    funext は Quot.sound から導出される core の定理であり追加公理ではない）。
-/
import IUT.RamifiedBase

namespace IUT

/-! ## M65F-0: nsum インフラの追加

    omega は var×var の積を読めない（規約3）ため、efg 恒等式の積の
    並べ替えは束縛変数上の補題 `efg_mul_swap` に切り出し、k に依存する
    係数の括り出しは `nsum_mul_right` を Nat.add_mul の分配で帰納証明する。 -/

/-- **区間限定の項別書き換え**: k < n の範囲で g₁ k = g₂ k なら
    Σ_{k<n} g₁ k = Σ_{k<n} g₂ k（funext を経由せず帰納で直接）。 -/
theorem nsum_congr {g₁ g₂ : Nat → Nat} (n : Nat)
    (h : ∀ k, k < n → g₁ k = g₂ k) : nsum g₁ n = nsum g₂ n := by
  induction n with
  | zero => rfl
  | succ j ih =>
    show nsum g₁ j + g₁ j = nsum g₂ j + g₂ j
    rw [h j (Nat.lt_succ_self j), ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

/-- **右係数の括り出し**: Σ_{k<n} (h k · m) = (Σ_{k<n} h k) · m。
    既存の nsum_weight_scale は係数が k に依存しない左係数の形なので、
    係数 h k が k に依存する右括り出しを Nat.add_mul の分配で帰納証明する
    （efg 恒等式の算術核）。 -/
theorem nsum_mul_right (h : Nat → Nat) (m n : Nat) :
    nsum (fun k => h k * m) n = nsum h n * m := by
  induction n with
  | zero => exact (Nat.zero_mul m).symm
  | succ j ih =>
    show nsum (fun k => h k * m) j + h j * m = (nsum h j + h j) * m
    rw [ih, Nat.add_mul]

/-- 定数 1 の和 = 項数（完全分解の Σef = n の算術核）。 -/
theorem nsum_one (n : Nat) : nsum (fun _ => 1) n = n := by
  induction n with
  | zero => rfl
  | succ j ih =>
    show nsum (fun _ => 1) j + 1 = j + 1
    rw [ih]

/-- **積の並べ替え** a·(b·m) = (b·a)·m（f_k·(e_k·m) = (e_k·f_k)·m 用。
    束縛変数上で使うため自由変数の補題に切り出し、omega でなく
    mul_assoc/mul_comm の rw で証明する——規約3）。 -/
theorem efg_mul_swap (a b m : Nat) : a * (b * m) = b * a * m := by
  rw [← Nat.mul_assoc, Nat.mul_comm a b]

/-! ## M65F-1: 拡大データ — 分解数 g・分岐指数 e・剰余次数 f -/

/-- **拡大データ**: 体拡大 L/K で K の素点 v が L の素点 w₀, …, w_{g-1} に
    分解する様子の簿記データ。分解数 g ≥ 1、各 k < g の分岐指数 e k ≥ 1・
    剰余次数 f k ≥ 1。e, f は添字 k < g でのみ意味を持つ（Fin を使わず
    全域関数 + 範囲条件にするのは omega 罠の回避と nsum との整合のため）。
    基本恒等式 Σ_{k<g} e_k·f_k = [L:K] は本モジュールでは**仮定**として
    受ける（正直な申告参照）。 -/
structure ExtData where
  /-- 分解数（v の上にある L の素点の個数）。 -/
  g : Nat
  /-- 分岐指数 e_k（添字 k < g でのみ意味を持つ）。 -/
  e : Nat → Nat
  /-- 剰余次数 f_k（添字 k < g でのみ意味を持つ）。 -/
  f : Nat → Nat
  g_pos : 1 ≤ g
  e_pos : ∀ k, k < g → 1 ≤ e k
  f_pos : ∀ k, k < g → 1 ≤ f k

/-- **efg 和** Σ_{k<g} e_k·f_k（= [L:K] になるべき量）。 -/
def efSum (E : ExtData) : Nat :=
  nsum (fun k => E.e k * E.f k) E.g

/-- **具体例（惰性的拡大）**: g = 1, e = 1, f = n（v の上に素点が一つ、
    分岐せず剰余次数 n）。 -/
def inertExt (n : Nat) (hn : 1 ≤ n) : ExtData where
  g := 1
  e := fun _ => 1
  f := fun _ => n
  g_pos := Nat.le_refl 1
  e_pos := fun _ _ => Nat.le_refl 1
  f_pos := fun _ _ => hn

/-- 惰性的拡大の Σef = 1·n = n。 -/
theorem inertExt_sum (n : Nat) (hn : 1 ≤ n) : efSum (inertExt n hn) = n := by
  show 0 + 1 * n = n
  omega

/-- **具体例（完全分解）**: g = n, e = f = 1（v の上に素点が n 個、
    どれも不分岐・剰余次数 1）。 -/
def splitExt (n : Nat) (hn : 1 ≤ n) : ExtData where
  g := n
  e := fun _ => 1
  f := fun _ => 1
  g_pos := hn
  e_pos := fun _ _ => Nat.le_refl 1
  f_pos := fun _ _ => Nat.le_refl 1

/-- 完全分解の Σef = Σ_{k<n} 1 = n。 -/
theorem splitExt_sum (n : Nat) (hn : 1 ≤ n) : efSum (splitExt n hn) = n := by
  show nsum (fun _ => 1 * 1) n = n
  exact (nsum_congr n (fun _ _ => Nat.one_mul 1)).trans (nsum_one n)

/-- **具体例（完全分岐）**: g = 1, e = n, f = 1（v の上に素点が一つ、
    分岐指数 n・剰余次数 1）。 -/
def ramifiedExt (n : Nat) (hn : 1 ≤ n) : ExtData where
  g := 1
  e := fun _ => n
  f := fun _ => 1
  g_pos := Nat.le_refl 1
  e_pos := fun _ _ => hn
  f_pos := fun _ _ => Nat.le_refl 1

/-- 完全分岐の Σef = n·1 = n。 -/
theorem ramifiedExt_sum (n : Nat) (hn : 1 ≤ n) :
    efSum (ramifiedExt n hn) = n := by
  show 0 + n * 1 = n
  omega

/-! ## M65F-2: 半局所圏 — v の上のファイバー（重複度ベクトルの圏） -/

/-- **半局所 Frobenioid の射**: v の上の素点 w₀, …, w_{g-1} での重複度
    ベクトル m から m' への射は、Frobenius 次数 d ≥ 1（**全成分共通**——
    Frobenius は因子全体の d 乗）と効果的因子ベクトル c : Nat → Nat
    （**成分ごと**）の対で、成分ごとの線形条件 m' k = d·m k + c k を
    満たすもの。M57F の `LocalHom`（一成分）のベクトル版。 -/
structure SemiLocalHom (m m' : Nat → Nat) where
  /-- Frobenius 次数（全成分共通）。 -/
  d : Nat
  /-- 効果的因子部分（成分ごとの重複度の増分）。 -/
  c : Nat → Nat
  d_pos : 1 ≤ d
  /-- 成分ごとの重複度の変換則: m' k = d·m k + c k。 -/
  linear : ∀ k, m' k = d * m k + c k

/-- 射の外延性: SemiLocalHom は (d, c) 成分で決まる（linear は Prop）。
    c : Nat → Nat の等号は成分ごとの一致から funext で作ってから
    subst する（規約: FibHom.ext の cases→subst 方式の関数値版）。 -/
theorem SemiLocalHom.ext {m m' : Nat → Nat} {φ ψ : SemiLocalHom m m'}
    (hd : φ.d = ψ.d) (hc : ∀ k, φ.c k = ψ.c k) : φ = ψ := by
  cases φ with | mk fd fc f1 f2 =>
  cases ψ with | mk gd gc g1 g2 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := funext hc
  subst hd'
  subst hc'
  rfl

/-- **定理 (M65F-2): 半局所 Frobenioid** — v の上のファイバーの圏:
    対象 = 重複度ベクトル Nat → Nat（添字 k < E.g が w_k での重複度。
    k ≥ g の成分は打ち切り規約で無意味——正直な申告参照）、射 =
    (d ≥ 1, c) with 成分ごとの線形条件。合成は捻れ半直積型
    (d₁d₂, k ↦ d₂·c₁ₖ + c₂ₖ)。圏公理は成分ごとに M57F の local_*
    補題をそのまま再利用。引数 E はファイバーの解釈（どの v の上か）を
    型に記録するためのもので、圏のデータ自体は E に依存しない。 -/
def semiLocalFrobenioid (_E : ExtData) : Cat where
  Obj := Nat → Nat
  Hom := SemiLocalHom
  id := fun m => ⟨1, fun _ => 0, Nat.le_refl 1, fun k => local_id_linear (m k)⟩
  comp := fun φ ψ =>
    ⟨φ.d * ψ.d, fun k => ψ.d * φ.c k + ψ.c k,
      Nat.mul_pos φ.d_pos ψ.d_pos,
      fun k => local_comp_linear (φ.linear k) (ψ.linear k)⟩
  id_comp := fun φ =>
    SemiLocalHom.ext (Nat.one_mul φ.d) (fun k => local_id_comp_c φ.d (φ.c k))
  comp_id := fun φ =>
    SemiLocalHom.ext (Nat.mul_one φ.d) (fun k => local_comp_id_c (φ.c k))
  assoc := fun φ ψ χ =>
    SemiLocalHom.ext (Nat.mul_assoc φ.d ψ.d χ.d)
      (fun k => local_assoc_c ψ.d χ.d (φ.c k) (ψ.c k) (χ.c k))

/-! ## M65F-3: 引き戻し関手 — v の因子を各 w_k に分岐指数倍で配る -/

/-- **定理 (M65F-3): 分解引き戻し関手** localFrobenioid →
    semiLocalFrobenioid E — v での重複度 m を各 w_k に e_k·m として配り
    （対象）、射 (d, c) を (d, k ↦ e_k·c) に送る。線形条件の保存は
    M61F の `pullback_linear`（一素点の e 倍引き戻し）の成分ごとの適用、
    関手性（合成の保存）は `pullback_comp_c`。[FrdI] の「体拡大に沿った
    因子の引き戻しで素点が枝分かれし重複度が分岐指数倍になる」簿記の
    機械検証。 -/
def decompPullback (E : ExtData) :
    Functor localFrobenioid (semiLocalFrobenioid E) where
  onObj := fun (m : Nat) => fun k => E.e k * m
  onHom := fun φ =>
    ⟨φ.d, fun k => E.e k * φ.c, φ.d_pos,
      fun k => pullback_linear (E.e k) φ.linear⟩
  map_id := fun _ => SemiLocalHom.ext rfl (fun k => Nat.mul_zero (E.e k))
  map_comp := fun φ ψ =>
    SemiLocalHom.ext rfl (fun k => pullback_comp_c (E.e k) ψ.d φ.c ψ.c)

/-! ## M65F-4: ノルム次数 — 剰余次数 f_k を重みとする押し出しの簿記 -/

/-- **ノルム次数**: 重複度ベクトル m' の f-重み付き和
    normDeg E m' = Σ_{k<g} f_k·m'_k。本物の次数理論の
    log #(O_L/w_k) = f_k·log #(O_K/v) の「f_k 重みで v 側の次数に
    集約する」簿記（正直な申告参照）。 -/
def normDeg (E : ExtData) (m : Nat → Nat) : Nat :=
  nsum (fun k => E.f k * m k) E.g

/-- 零ベクトルのノルム次数は 0。 -/
theorem normDeg_zero (E : ExtData) : normDeg E (fun _ => 0) = 0 := by
  show nsum (fun k => E.f k * 0) E.g = 0
  exact nsum_vanish _ E.g (fun k _ => Nat.mul_zero (E.f k))

/-- **定理 (M65F-4a): ノルム次数の加法性**（nsum_weight_add の発動）。 -/
theorem normDeg_add (E : ExtData) (mx my : Nat → Nat) :
    normDeg E (fun k => mx k + my k) = normDeg E mx + normDeg E my := by
  show nsum (fun k => E.f k * (mx k + my k)) E.g
      = nsum (fun k => E.f k * mx k) E.g + nsum (fun k => E.f k * my k) E.g
  exact nsum_weight_add E.f mx my E.g

/-- **定理 (M65F-4b): ノルム次数の Frobenius 斉次性**
    （nsum_weight_scale の発動）: normDeg(d·m) = d·normDeg(m)。 -/
theorem normDeg_frob (E : ExtData) (d : Nat) (m : Nat → Nat) :
    normDeg E (fun k => d * m k) = d * normDeg E m := by
  show nsum (fun k => E.f k * (d * m k)) E.g
      = d * nsum (fun k => E.f k * m k) E.g
  exact nsum_weight_scale E.f m d E.g

/-- **定理 (M65F-4c): ノルム次数の線形性** — 成分ごとの線形条件
    m' k = d·m k + c k はノルム次数の線形条件 normDeg m' = d·normDeg m +
    normDeg c に移る（加法性 + 斉次性）。押し出し関手の線形条件の保存と
    合成の保存の両方を供給する核。 -/
theorem normDeg_linear (E : ExtData) {d : Nat} {m c m' : Nat → Nat}
    (h : ∀ k, m' k = d * m k + c k) :
    normDeg E m' = d * normDeg E m + normDeg E c := by
  have hm' : m' = fun k => d * m k + c k := funext h
  rw [hm']
  have h1 : nsum (fun k => E.f k * (d * m k + c k)) E.g
      = nsum (fun k => E.f k * (d * m k)) E.g
        + nsum (fun k => E.f k * c k) E.g :=
    nsum_weight_add E.f (fun k => d * m k) c E.g
  have h2 : nsum (fun k => E.f k * (d * m k)) E.g
      = d * nsum (fun k => E.f k * m k) E.g :=
    nsum_weight_scale E.f m d E.g
  show nsum (fun k => E.f k * (d * m k + c k)) E.g
      = d * nsum (fun k => E.f k * m k) E.g + nsum (fun k => E.f k * c k) E.g
  rw [h1, h2]

/-! ## M65F-5: efg 恒等式 — 引き戻して押し出すと次数は Σef 倍 -/

/-- **定理 (M65F-5): efg 恒等式** — v の重複度 m を引き戻したベクトル
    (k ↦ e_k·m) のノルム次数は (Σ_{k<g} e_k·f_k)·m。
    Σ_{k<g} f_k·(e_k·m) = Σ_{k<g} (e_k·f_k)·m（efg_mul_swap の項別適用）
    = (Σ_{k<g} e_k·f_k)·m（nsum_mul_right）。[FrdI] の
    Σe_kf_k = [L:K] 簿記が因子の引き戻し・押し出しと整合することの
    機械検証（ヘッダの紙上検証参照）。 -/
theorem efg_identity (E : ExtData) (m : Nat) :
    normDeg E (fun k => E.e k * m) = efSum E * m := by
  have h1 : nsum (fun k => E.f k * (E.e k * m)) E.g
      = nsum (fun k => E.e k * E.f k * m) E.g :=
    nsum_congr E.g (fun k _ => efg_mul_swap (E.f k) (E.e k) m)
  have h2 : nsum (fun k => E.e k * E.f k * m) E.g
      = nsum (fun k => E.e k * E.f k) E.g * m :=
    nsum_mul_right (fun k => E.e k * E.f k) m E.g
  show nsum (fun k => E.f k * (E.e k * m)) E.g
      = nsum (fun k => E.e k * E.f k) E.g * m
  rw [h1, h2]

/-- **系 (M65F-5'): 次数は拡大次数倍** — Σef = n（= [L:K]、仮定として
    受ける——正直な申告参照）のもとで、引き戻しのノルム次数は n·m。
    **「引き戻して押し出すと次数は [L:K] 倍」**。 -/
theorem efg_deg (E : ExtData) {n : Nat} (hn : efSum E = n) (m : Nat) :
    normDeg E (fun k => E.e k * m) = n * m := by
  rw [efg_identity E m, hn]

/-- **系 (M65F-5''): 引き戻し関手の対象との接続** — efg 恒等式を
    decompPullback の像の対象で言い直した形（定義的に efg_identity）。 -/
theorem efg_pullback (E : ExtData) (m : Nat) :
    normDeg E ((decompPullback E).onObj m) = efSum E * m :=
  efg_identity E m

/-- **発動（惰性的拡大）**: g = 1, e = 1, f = n では次数は n 倍
    （一つの素点の剰余次数がまるごと効く）。 -/
theorem inert_efg (n : Nat) (hn : 1 ≤ n) (m : Nat) :
    normDeg (inertExt n hn) (fun k => (inertExt n hn).e k * m) = n * m :=
  efg_deg (inertExt n hn) (inertExt_sum n hn) m

/-- **発動（完全分解）**: g = n, e = f = 1 では次数は n 個の素点の
    重複度の和として n 倍（枝分かれの本数が効く）。 -/
theorem split_efg (n : Nat) (hn : 1 ≤ n) (m : Nat) :
    normDeg (splitExt n hn) (fun k => (splitExt n hn).e k * m) = n * m :=
  efg_deg (splitExt n hn) (splitExt_sum n hn) m

/-- **発動（完全分岐）**: g = 1, e = n, f = 1 では次数は分岐指数 n 倍
    （M61F の pullback_deg と同じ簿記が分解の枠組みで再現）。 -/
theorem ramified_efg (n : Nat) (hn : 1 ≤ n) (m : Nat) :
    normDeg (ramifiedExt n hn) (fun k => (ramifiedExt n hn).e k * m)
      = n * m :=
  efg_deg (ramifiedExt n hn) (ramifiedExt_sum n hn) m

/-! ## M65F-6: 押し出し（ノルム）関手 -/

/-- **定理 (M65F-6): ノルム関手** semiLocalFrobenioid E →
    localFrobenioid — 重複度ベクトル m' を v 側のノルム次数
    normDeg E m' に、射 (d, c) を (d, normDeg E c) に送る。線形条件の
    保存は normDeg_linear（加法性 + 斉次性）、合成の保存
    normDeg(k ↦ d₂·c₁ₖ + c₂ₖ) = d₂·normDeg c₁ + normDeg c₂ も
    **同じ補題**で従う。[FrdI] のノルム（押し出し）の次数簿記の
    関手レベルの実体。 -/
def normFunctor (E : ExtData) :
    Functor (semiLocalFrobenioid E) localFrobenioid where
  onObj := fun m => normDeg E m
  onHom := fun φ =>
    ⟨φ.d, normDeg E φ.c, φ.d_pos, normDeg_linear E φ.linear⟩
  map_id := fun _ => LocalHom.ext rfl (normDeg_zero E)
  map_comp := fun φ ψ =>
    LocalHom.ext rfl
      (by show normDeg E (fun k => ψ.d * φ.c k + ψ.c k)
            = ψ.d * normDeg E φ.c + normDeg E ψ.c
          exact normDeg_linear E (fun _ => rfl))

/-! ## M65F-7: 合成 = n 倍関手 — ノルム ∘ 引き戻し = [L:K] 倍 -/

/-- **定理 (M65F-7a): 合成の対象成分 = pullbackFunctor n** —
    Σef = n のもとで「引き戻してからノルム」は対象を n·m に送り、
    M61F の n 倍引き戻し関手 `pullbackFunctor n` の対象成分と一致する。 -/
theorem norm_pullback_obj (E : ExtData) {n : Nat} (hn : efSum E = n)
    (hn' : 1 ≤ n) (m : Nat) :
    (normFunctor E).onObj ((decompPullback E).onObj m)
      = (pullbackFunctor n hn').onObj m := by
  show normDeg E (fun k => E.e k * m) = n * m
  exact efg_deg E hn m

/-- **定理 (M65F-7b): 合成の射の d 成分 = pullbackFunctor n の d 成分**
    — どちらも Frobenius 次数を変えない（定義的 rfl）。 -/
theorem norm_pullback_hom_d (E : ExtData) (n : Nat) (hn' : 1 ≤ n)
    {m m' : Nat} (φ : LocalHom m m') :
    ((normFunctor E).onHom ((decompPullback E).onHom φ)).d
      = ((pullbackFunctor n hn').onHom φ).d :=
  rfl

/-- **定理 (M65F-7c): 合成の射の c 成分 = pullbackFunctor n の c 成分**
    — Σef = n のもとで、効果的因子 c は n·c に送られる（efg 恒等式の
    c への適用）。M65F-7a/b/c を合わせて **「ノルム ∘ 引き戻し =
    [L:K] 倍関手」**が対象・射の全成分で機械検証された（射の等号
    そのものは両辺の型（端点の対象）が hn を経由してのみ一致するため
    成分等式で述べる）。 -/
theorem norm_pullback_hom_c (E : ExtData) {n : Nat} (hn : efSum E = n)
    (hn' : 1 ≤ n) {m m' : Nat} (φ : LocalHom m m') :
    ((normFunctor E).onHom ((decompPullback E).onHom φ)).c
      = ((pullbackFunctor n hn').onHom φ).c := by
  show normDeg E (fun k => E.e k * φ.c) = n * φ.c
  exact efg_deg E hn φ.c

/-! ## M65F-8: 剛性 — 半局所圏も Frobenius-like に剛的

    M48F-4（次数）・M51F-10（因子）・M57F-8（離散 base）・M61F-6
    （塔 base）の系譜のベクトル版。c : Nat → Nat の全成分 0 の読み出しは
    funext 越しなので congrFun で成分ごとに d·c k + c' k = 0 を読む。 -/

/-- **定理 (M65F-8a): 同型の Frobenius 次数は 1** — hom·inv = id の
    d 成分読み出し d·d' = 1 と d, d' ≥ 1 から（M48F の
    `frob_mul_eq_one_left` の再利用）。 -/
theorem semiLocal_iso_d_one {E : ExtData} {m m' : Nat → Nat}
    (i : CatIso (semiLocalFrobenioid E) m m') : i.hom.d = 1 :=
  frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos
    (congrArg SemiLocalHom.d i.hom_inv)

/-- **定理 (M65F-8b): 同型の因子部分は全成分 0** — hom·inv = id の
    c 成分（関数の等号）を congrFun で成分 k ごとに読み出し
    d'·c k + c' k = 0 を得て、inv.d = 1 を先に確定させて 1 倍に潰せば
    線形になり omega が通る（var×var を作らない、規約3）。 -/
theorem semiLocal_iso_c_zero {E : ExtData} {m m' : Nat → Nat}
    (i : CatIso (semiLocalFrobenioid E) m m') (k : Nat) :
    i.hom.c k = 0 := by
  have hdinv : i.inv.d = 1 :=
    frob_mul_eq_one_left i.inv.d_pos i.hom.d_pos
      (congrArg SemiLocalHom.d i.inv_hom)
  have hc : i.inv.d * i.hom.c k + i.inv.c k = 0 :=
    congrFun (congrArg SemiLocalHom.c i.hom_inv) k
  rw [hdinv, Nat.one_mul] at hc
  omega

/-- **定理 (M65F-8c): 同型は対象を動かせない** — m ≅ m' ⟹ m = m'
    （重複度ベクトルが全成分で一致）。(d, c) = (1, 0) を成分ごとの
    線形条件に代入。**ファイバーをベクトル化しても Frobenius-like
    剛性は保たれる**。 -/
theorem semiLocal_iso_objects_eq {E : ExtData} {m m' : Nat → Nat}
    (i : CatIso (semiLocalFrobenioid E) m m') : m = m' := by
  have hd : i.hom.d = 1 := semiLocal_iso_d_one i
  funext k
  have hl : m' k = i.hom.d * m k + i.hom.c k := i.hom.linear k
  rw [hd, Nat.one_mul, semiLocal_iso_c_zero i k, Nat.add_zero] at hl
  exact hl.symm

/-- **系 (M65F-8c'): semiLocalFrobenioid は gaunt**（M53F-1 の述語）。 -/
theorem semiLocalFrobenioid_gaunt (E : ExtData) :
    IsGaunt (semiLocalFrobenioid E) :=
  fun _ _ i => semiLocal_iso_objects_eq i

/-- **定理 (M65F-8d): 同型の一意性（剛性）** — 任意の二対象間の同型は
    hom 成分が一意（(d, c) = (1, 0) に固定）。poly-isomorphism は
    単集合のまま: **分解・惰性のベクトル構造を足しても Frobenius-like
    剛性は保たれる**（M53F の語彙、M57F-8d/M61F-6e の系譜）。 -/
theorem semiLocal_iso_unique (E : ExtData) :
    IsoUnique (semiLocalFrobenioid E) :=
  fun _ _ i j =>
    SemiLocalHom.ext
      ((semiLocal_iso_d_one i).trans (semiLocal_iso_d_one j).symm)
      (fun k => (semiLocal_iso_c_zero i k).trans
        (semiLocal_iso_c_zero j k).symm)

/-- **系 (M65F-8d'): CatIso 全体としての一意性**（M22-1a CatIso.ext
    経由、M53F-1 isoUnique_subsingleton の発動）。 -/
theorem semiLocal_rigid {E : ExtData} {m m' : Nat → Nat}
    (i j : CatIso (semiLocalFrobenioid E) m m') : i = j :=
  isoUnique_subsingleton (semiLocal_iso_unique E) i j

end IUT
