/-
  IUT/RamifiedBase.lean — M61F（base 圏の非自明射:
  分岐指数つき base 塔とファイバー輸送）の形式化

  ## 動機

  [FrdI] §1 の Frobenioid の base 圏は本来**非自明な射**を持つ:
  体拡大 L/K（分岐指数 e）に沿って素イデアルの因子を引き戻すと
  重複度が e 倍になる（π_K = π_L^e·(単数)）。base 圏の射はこの
  輸送データを運び、全空間の射は「base の射・Frobenius 次数 deg_Fr・
  効果的因子 Div」に分解される。

  ところが既存の形式化の base はすべて**離散圏**だった——M57F の
  `fiberedFrobenioid`（IUT/FiberedFrobenioid.lean）と M59F の
  `splitFiberedFrobenioid`（IUT/SplitFibered.lean）は base の射を
  等号の証明（PLift (k = l)）に限定し、dashboard でも
  「base の非自明射（分解・惰性・分岐）・base の射に沿った因子の
  輸送は未形式化」と正直に申告してきた。

  本モジュールはこの申告を**局所体の塔・単一素点の範囲で**解消する:

  * **塔の base 圏** `towerCat`（対象 = 塔 K₀ ⊆ K₁ ⊆ … の段数 n : ℕ、
    射 n → n' = (le : n ≤ n', 分岐指数 e ≥ 1)、合成 = (le_trans, e₁e₂)）。
    離散圏と違い **n < n' の非自明射を持つ**（`towerRamify`）が、
    塔は降りられない（`tower_no_descent`）
  * **分岐つき全空間圏** `ramifiedFrobenioid`（対象 = (段 n, 重複度 m)、
    射 = (le, e ≥ 1, d ≥ 1, c) with m' = e·d·m + c。base の射に沿った
    引き戻しで重複度が e 倍、Frobenius で d 倍、効果的因子 c を加算）
  * **射影関手** `ramProj` : 全空間 → 塔 base と**垂直部分**:
    e = 1 の射が各段のファイバーを成す（M57F の localFrobenioid の
    忠実なコピー、`ramVerticalIncl` / `ramVerticalIncl_full`）
  * **引き戻し関手** `pullbackFunctor e` : localFrobenioid →
    localFrobenioid（m ↦ e·m、(d, c) ↦ (d, e·c)）。
    **deg は分岐指数倍**（`pullback_deg`、[FrdI] の簿記が定理に）
  * **純引き戻し射と分解定理** `ramPullbackMor` / `ram_hom_factor`:
    全空間の任意の射 = 純引き戻し射 ∘ 垂直射（[FrdI] の
    「射 = base 輸送と Frobenius-like 部分の合成」の機械検証）、
    ＋輸送の自然性 `pullback_incl_compat`（引き戻し square の可換性）
  * **剛性** — 同型は e = 1・d = 1・c = 0 を強制し、段も重複度も
    動かせない（gaunt・IsoUnique）。**base の非自明射を足しても
    Frobenius-like 剛性は保たれ、新規に「同型は塔を昇れない」が出る**
  * **非可逆性の新形** `ram_no_descent` / `pullback_not_invertible`:
    塔は昇るだけで降りられず、分岐 e ≥ 2 の純引き戻し射は同型でない

  ## 合成の線形条件の紙上検証（圏公理に入る前の算術核）

  射 (n₁,m₁) → (n₂,m₂) → (n₃,m₃) の合成で、
  m₂ = e₁d₁·m₁ + c₁ かつ m₃ = e₂d₂·m₂ + c₂ なら、a := e₁d₁・
  b := e₂d₂ と置けば M57F の `local_comp_linear` がそのまま適用でき
    m₃ = (e₁d₁)(e₂d₂)·m₁ + ((e₂d₂)·c₁ + c₂)。
  c 成分 (e₂d₂)·c₁ + c₂ は捻れ半直積型の式そのままで一致し、
  係数の並べ替え (e₁d₁)(e₂d₂) = (e₁e₂)(d₁d₂) だけが新規に必要
  （`ram_mul_swap`、omega は var×var を読めないので
  Nat.mul_comm/mul_assoc の rw 連鎖で証明する——規約3）。

  ## 検証する定理（全て sorry なし・選択公理なし）

  * M61F-1 `TowerHom` / `towerCat` / `towerRamify` / `tower_no_descent`
    — 塔の base 圏の圏公理完全証明（ext は e 成分のみ: le は Prop）。
    非自明射の実在（0 → 1, e = 2）と降下射の不在
  * M61F-2 `RamHom` / `RamHom.ext` / `ramifiedFrobenioid` —
    分岐つき全空間圏の圏公理完全証明（恒等 (le_refl, 1, 1, 0)、
    合成 (le_trans, e₁e₂, d₁d₂, (e₂d₂)c₁ + c₂)）
  * M61F-3 `ramProj` / `ramVerticalIncl` / `ramVerticalRestrict` /
    `ramVerticalIncl_faithful` / `ramVerticalIncl_full` /
    `ramProj_vertical_id` — 射影関手の関手性（e 成分の合成保存）と
    垂直部分: e = 1 かつ段固定の射が localFrobenioid の忠実なコピー
    （往復恒等、M57F-5 方式）
  * M61F-4 `pullbackFunctor` / `pullback_deg` — base の射（分岐 e）に
    沿った因子の引き戻し関手 m ↦ e·m、(d, c) ↦ (d, e·c) の関手性。
    **引き戻しで次数（= 局所重複度）が分岐指数倍になる** [FrdI] の
    簿記が `pullback_deg : onObj m = e * m`（定義的 rfl）として定理に
  * M61F-5 `ramPullbackMor` / `ram_hom_factor` / `pullback_incl_compat`
    — 純引き戻し射 (le, e, 1, 0) : (n, m) → (n', e·m) の実在、
    **分解定理**: 任意の射 = 純引き戻し射 ∘ 垂直射（成分計算で ext）、
    輸送の自然性: 引き戻し square（垂直射を先に行って引き戻すのと、
    引き戻してから像の垂直射を行うのが一致）
  * M61F-6 `ram_iso_e_one` / `ram_iso_d_one` / `ram_iso_c_zero` /
    `ram_iso_objects_eq` / `ramifiedFrobenioid_gaunt` /
    `ram_iso_unique` / `ram_rigid` — **剛性**: 同型は e = 1・d = 1・
    c = 0 を強制（合成が e・d 成分を別々に保つので
    `frob_mul_eq_one_left` を各成分に直接適用できる。e·d = 1 経由の
    二段適用も同じ結論を与えるが、成分ごとの方が短い）し、
    段も重複度も動かせない（段は le の反対称性でも e = 1 でも出る）。
    同型は一意 = poly-isomorphism は単集合のまま: **base の非自明射を
    足しても Frobenius-like 剛性は保たれる**
  * M61F-7 `ram_no_descent` / `pullback_not_invertible` —
    **非可逆性の新形**: n < n' なら (n', m') から (n, m) への射は
    存在しない（塔は昇るだけで降りられない）。分岐 e ≥ 2 の
    純引き戻し射を hom とする同型は存在しない（具体的証人）

  ## 正直な申告（モデルと本物の差）

  * **単一素点の塔のみ**: base は一本の局所体の塔 K₀ ⊆ K₁ ⊆ … を
    モデル化した全順序圏（対象 ℕ・射は段の比較 + 分岐指数）であり、
    数体の素点の圏が持つ**複数素点への分解（分解数 g）・惰性（剰余
    次数 f）**は未形式化（efg = [L:K] の簿記には射が「一つの素点の
    複数の延長」へ枝分かれするデータが要る）。M57F の離散 base
    （素点の添字 ℕ）と本モジュールの塔 base の「直積」
    （素点ごとに塔が立つ base 圏）も未形式化。
  * **e は抽象パラメータ**: 分岐指数 e は射のデータとして公理的に
    与えられ、実際の体拡大（剰余体・付値の延長）から計算されない。
    「e がどの拡大から来るか」は局所体論（M24–M37 の Lubin–Tate 系列）
    との接続を要し未形式化。
  * **単数なし**: M59F の split 構造（単数成分 u）との合成
    「塔 base 上の単数つき全空間圏」は未形式化（単数が引き戻しで
    どう変換されるか——ノルム・単数群の指数——のモデル選択が要る）。
  * **不分岐部分の分離なし**: 本モデルの e は射ごとに自由であり、
    「e = 1 の射だけからなる不分岐部分塔」のような部分圏の理論
    （惰性体・分岐体の塔）は展開していない。
  * 選択公理・追加公理は不使用（全定理 propext/Quot.sound 以下、
    数値具体例の決定手続きを含む定理でも Classical.choice は不要）。
-/
import IUT.FiberedFrobenioid

namespace IUT

/-! ## 算術ヘルパー補題

    omega は var×var の積を読めない（規約3）ため、係数の並べ替えは
    Nat.mul_comm / Nat.mul_assoc の rw 連鎖で束縛変数上の補題に
    切り出す。合成の線形条件本体は M57F の `local_comp_linear` を
    a := e₁d₁・b := e₂d₂ でそのまま再利用する（ヘッダの紙上検証参照）。 -/

/-- **係数の並べ替え**: (e₁d₁)(e₂d₂) = (e₁e₂)(d₁d₂)。
    合成射の線形条件を (e, d) 成分の積に読み替える算術核。 -/
theorem ram_mul_swap (e₁ d₁ e₂ d₂ : Nat) :
    e₁ * d₁ * (e₂ * d₂) = e₁ * e₂ * (d₁ * d₂) := by
  rw [Nat.mul_assoc e₁ d₁, ← Nat.mul_assoc d₁ e₂, Nat.mul_comm d₁ e₂,
      Nat.mul_assoc e₂ d₁, ← Nat.mul_assoc e₁ e₂]

/-- 恒等射の線形条件: m = (1·1)·m + 0。 -/
theorem ram_id_linear (m : Nat) : m = 1 * 1 * m + 0 := by omega

/-- 合成射の線形条件: m₂ = e₁d₁·m₁ + c₁ かつ m₃ = e₂d₂·m₂ + c₂ なら
    m₃ = (e₁e₂)(d₁d₂)·m₁ + ((e₂d₂)c₁ + c₂)。M57F の local_comp_linear
    （a := e₁d₁, b := e₂d₂）＋係数の並べ替え ram_mul_swap。 -/
theorem ram_comp_linear {e₁ d₁ e₂ d₂ m₁ m₂ m₃ c₁ c₂ : Nat}
    (h₁ : m₂ = e₁ * d₁ * m₁ + c₁) (h₂ : m₃ = e₂ * d₂ * m₂ + c₂) :
    m₃ = e₁ * e₂ * (d₁ * d₂) * m₁ + (e₂ * d₂ * c₁ + c₂) := by
  have h := local_comp_linear h₁ h₂
  rw [h, ram_mul_swap]

/-- 左単位則の因子部分: (ed)·0 + y = y（e·d は var×var なので
    omega でなく mul_zero / zero_add の rw で潰す——規約3）。 -/
theorem ram_id_comp_c (e d y : Nat) : e * d * 0 + y = y := by
  rw [Nat.mul_zero, Nat.zero_add]

/-- 右単位則の因子部分: (1·1)·x + 0 = x。 -/
theorem ram_comp_id_c (x : Nat) : 1 * 1 * x + 0 = x := by omega

/-- 結合則の因子部分: (e₃d₃)·((e₂d₂)·x + y) + z
    = (e₂e₃)(d₂d₃)·x + ((e₃d₃)·y + z)。M57F の local_assoc_c
    （b := e₂d₂, c := e₃d₃）＋係数の並べ替え。 -/
theorem ram_assoc_c (e₂ d₂ e₃ d₃ x y z : Nat) :
    e₃ * d₃ * (e₂ * d₂ * x + y) + z
      = e₂ * e₃ * (d₂ * d₃) * x + (e₃ * d₃ * y + z) := by
  rw [local_assoc_c (e₂ * d₂) (e₃ * d₃) x y z, ram_mul_swap]

/-! ## M61F-1: 塔の base 圏 — 分岐指数を運ぶ非自明射 -/

/-- **塔の base 圏の射**: 局所体の塔 K₀ ⊆ K₁ ⊆ … の段 n から n' への
    射は、段の比較 le : n ≤ n'（Prop）と**分岐指数** e ≥ 1 の組。
    [FrdI] §1 の base 圏の射が運ぶ輸送データ（体拡大の分岐指数
    e(L/K)）のモデル。M57F の離散 base（射 = 等号のみ）と違い、
    n < n' の非自明射を持つ。 -/
structure TowerHom (n n' : Nat) where
  /-- 段の比較（塔は昇る向きにしか射を持たない）。 -/
  le : n ≤ n'
  /-- 分岐指数。 -/
  e : Nat
  e_pos : 1 ≤ e

/-- 射の外延性: TowerHom は e 成分で決まる（le は Prop なので
    proof irrelevance により自動で一致）。 -/
theorem TowerHom.ext {n n' : Nat} {f g : TowerHom n n'}
    (he : f.e = g.e) : f = g := by
  cases f with | mk fle fe f1 =>
  cases g with | mk gle ge g1 =>
  have he' : fe = ge := he
  subst he'
  rfl

/-- **定理 (M61F-1): 塔の base 圏** — 対象 = 塔の段数 ℕ、射 =
    (段の比較, 分岐指数 e ≥ 1)。恒等 = (le_refl, 1)（不分岐）、
    合成 = (le_trans, e₁·e₂)（分岐指数の乗法性 e(M/K) =
    e(M/L)·e(L/K)）。圏公理は e 成分の単位・結合則。 -/
def towerCat : Cat where
  Obj := Nat
  Hom := TowerHom
  id := fun n => ⟨Nat.le_refl n, 1, Nat.le_refl 1⟩
  comp := fun f g =>
    ⟨Nat.le_trans f.le g.le, f.e * g.e, Nat.mul_pos f.e_pos g.e_pos⟩
  id_comp := fun f => TowerHom.ext (Nat.one_mul f.e)
  comp_id := fun f => TowerHom.ext (Nat.mul_one f.e)
  assoc := fun f g h => TowerHom.ext (Nat.mul_assoc f.e g.e h.e)

/-- **非自明射の実在**: 任意の n ≤ n'・任意の分岐指数 e ≥ 1 に対し
    射 n → n' が存在する（離散 base 圏には無かったデータ）。 -/
def towerRamify {n n' : Nat} (h : n ≤ n') (e : Nat) (he : 1 ≤ e) :
    TowerHom n n' :=
  ⟨h, e, he⟩

/-- 具体的証人: 段 0 → 1 の分岐指数 2 の射（離散圏なら Hom が空に
    なる対象対の間に射がある）。 -/
theorem tower_nontrivial : Nonempty (TowerHom 0 1) :=
  ⟨towerRamify (Nat.zero_le 1) 2 (by omega)⟩

/-- **塔は降りられない（base レベル）**: n < n' なら射 n' → n は
    存在しない（le の向き）。 -/
theorem tower_no_descent {n n' : Nat} (h : n < n') :
    ¬ Nonempty (TowerHom n' n) :=
  fun ⟨f⟩ => absurd f.le (Nat.not_le.mpr h)

/-! ## M61F-2: 分岐つき全空間圏 -/

/-- **分岐つき全空間圏の射**: 対象 (n, m)（塔の段 n, その段での因子の
    重複度 m）から (n', m') への射は、base 成分 (le : n ≤ n',
    分岐指数 e ≥ 1) と簿記成分 (Frobenius 次数 d ≥ 1, 効果的因子 c) の
    組で、線形条件 m' = e·d·m + c を満たすもの。base の射に沿った
    引き戻しで重複度が e 倍（π_K = π_L^e·(単数)）、Frobenius で d 倍、
    効果的因子 c を加算する [FrdI] の簿記。 -/
structure RamHom (P Q : Nat × Nat) where
  /-- base 成分: 段の比較。 -/
  le : P.1 ≤ Q.1
  /-- 分岐指数（base の射が運ぶ輸送データ）。 -/
  e : Nat
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的因子部分。 -/
  c : Nat
  e_pos : 1 ≤ e
  d_pos : 1 ≤ d
  /-- 重複度の変換則: m' = e·d·m + c。 -/
  linear : Q.2 = e * d * P.2 + c

/-- 射の外延性: RamHom は (e, d, c) 成分で決まる（le は Prop なので
    proof irrelevance により自動で一致、linear も Prop）。 -/
theorem RamHom.ext {P Q : Nat × Nat} {f g : RamHom P Q}
    (he : f.e = g.e) (hd : f.d = g.d) (hc : f.c = g.c) : f = g := by
  cases f with | mk fle fe fd fc f1 f2 f3 =>
  cases g with | mk gle ge gd gc g1 g2 g3 =>
  have he' : fe = ge := he
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  subst he'
  subst hd'
  subst hc'
  rfl

/-- **定理 (M61F-2): 分岐つき全空間圏** — 対象 = (塔の段, 重複度)、
    射 = (le, e, d, c)。恒等 = (le_refl, 1, 1, 0)、合成 =
    (le_trans, e₁e₂, d₁d₂, (e₂d₂)c₁ + c₂)。圏公理の線形条件は
    local_comp_linear の再利用＋係数の並べ替え ram_mul_swap
    （ヘッダの紙上検証参照）、le は ext が吸収。 -/
def ramifiedFrobenioid : Cat where
  Obj := Nat × Nat
  Hom := RamHom
  id := fun P =>
    ⟨Nat.le_refl P.1, 1, 1, 0, Nat.le_refl 1, Nat.le_refl 1,
      ram_id_linear P.2⟩
  comp := fun f g =>
    ⟨Nat.le_trans f.le g.le, f.e * g.e, f.d * g.d,
      g.e * g.d * f.c + g.c,
      Nat.mul_pos f.e_pos g.e_pos, Nat.mul_pos f.d_pos g.d_pos,
      ram_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    RamHom.ext (Nat.one_mul f.e) (Nat.one_mul f.d)
      (ram_id_comp_c f.e f.d f.c)
  comp_id := fun f =>
    RamHom.ext (Nat.mul_one f.e) (Nat.mul_one f.d) (ram_comp_id_c f.c)
  assoc := fun f g h =>
    RamHom.ext (Nat.mul_assoc f.e g.e h.e) (Nat.mul_assoc f.d g.d h.d)
      (ram_assoc_c g.e g.d h.e h.d f.c g.c h.c)

/-! ## M61F-3: 射影関手と垂直部分 -/

/-- **定理 (M61F-3a): 射影関手** π : ramifiedFrobenioid → towerCat —
    対象 (n, m) を段 n に、射をその base 成分 (le, e) に送る。
    関手性は e 成分の合成保存（どちらの圏でも e₁·e₂）から rfl。
    [FrdI] の「Frobenioid から base 圏への構造射」の塔版——M57F の
    fibProj と違い、**射影先の射が分岐指数という実データを運ぶ**。 -/
def ramProj : Functor ramifiedFrobenioid towerCat where
  onObj := fun P => P.1
  onHom := fun f => ⟨f.le, f.e, f.e_pos⟩
  map_id := fun _ => TowerHom.ext rfl
  map_comp := fun _ _ => TowerHom.ext rfl

/-- 垂直包含の線形条件: m' = d·m + c なら m' = (1·d)·m + c。 -/
theorem ram_vert_linear {d m m' c : Nat} (h : m' = d * m + c) :
    m' = 1 * d * m + c := by
  rw [Nat.one_mul]
  exact h

/-- 垂直包含の合成の因子部分: d·x + y = (1·d)·x + y。 -/
theorem ram_vert_comp_c (d x y : Nat) : d * x + y = 1 * d * x + y := by
  rw [Nat.one_mul]

/-- **定理 (M61F-3b): 垂直包含関手** — 段 n を固定し、M57F の局所
    Frobenioid を全空間の n 上のファイバー（e = 1・段固定の射）に
    埋め込む: m ↦ (n, m)、(d, c) ↦ (le_refl, 1, d, c)。e = 1 =
    不分岐（base 方向に動かない）。離散版 M57F の fiberIncl との
    整合: 垂直射は分岐指数を持たない。 -/
def ramVerticalIncl (n : Nat) :
    Functor localFrobenioid ramifiedFrobenioid where
  onObj := fun m => (n, m)
  onHom := fun f =>
    ⟨Nat.le_refl n, 1, f.d, f.c, Nat.le_refl 1, f.d_pos,
      ram_vert_linear f.linear⟩
  map_id := fun _ => RamHom.ext rfl rfl rfl
  map_comp := fun f g =>
    RamHom.ext (Nat.one_mul 1).symm rfl (ram_vert_comp_c g.d f.c g.c)

/-- 垂直包含は射影の上で定値（π ∘ incl_n = const n、対象レベル）。 -/
theorem ramProj_vertical_const (n m : Nat) :
    ramProj.onObj ((ramVerticalIncl n).onObj m) = n :=
  rfl

/-- **定理 (M61F-3c): 垂直射の射影は恒等** — 垂直包含の像の射は
    射影すると base の恒等射（e = 1）になる。 -/
theorem ramProj_vertical_id (n : Nat) {m m' : Nat} (f : LocalHom m m') :
    ramProj.onHom ((ramVerticalIncl n).onHom f) = towerCat.id n :=
  TowerHom.ext rfl

/-- ファイバーの射（e = 1・段固定）から局所射への読み出し
    （onHom の逆写像）。 -/
def ramVerticalRestrict (n : Nat) {m m' : Nat}
    (g : RamHom (n, m) (n, m')) (he : g.e = 1) : LocalHom m m' :=
  ⟨g.d, g.c, g.d_pos, by
    have h : m' = g.e * g.d * m + g.c := g.linear
    rw [he, Nat.one_mul] at h
    exact h⟩

/-- **定理 (M61F-3d): 垂直包含は忠実** — onHom は単射
    （(d, c) 成分の読み出しで即座）。 -/
theorem ramVerticalIncl_faithful (n : Nat) {m m' : Nat}
    {f g : LocalHom m m'}
    (h : (ramVerticalIncl n).onHom f = (ramVerticalIncl n).onHom g) :
    f = g :=
  LocalHom.ext (congrArg RamHom.d h) (congrArg RamHom.c h)

/-- 往復 (局所射 → 垂直射 → 局所射) は恒等（忠実性の片割れ）。 -/
theorem ramVerticalIncl_roundtrip (n : Nat) {m m' : Nat}
    (f : LocalHom m m') :
    ramVerticalRestrict n ((ramVerticalIncl n).onHom f) rfl = f :=
  LocalHom.ext rfl rfl

/-- **定理 (M61F-3e): 垂直包含は e = 1 の射の上に充満** —
    e = 1 の段固定射はすべて垂直包含の像（往復恒等）。すなわち
    「各段のファイバー = e = 1 の射のなす localFrobenioid のコピー」
    の機械検証（M57F-5 の fiber_local_iso の塔 base 版）。 -/
theorem ramVerticalIncl_full (n : Nat) {m m' : Nat}
    (g : RamHom (n, m) (n, m')) (he : g.e = 1) :
    (ramVerticalIncl n).onHom (ramVerticalRestrict n g he) = g :=
  RamHom.ext he.symm rfl rfl

/-! ## M61F-4: base の射に沿った因子の引き戻し関手 -/

/-- 引き戻しの線形条件: m' = d·m + c なら e·m' = d·(e·m) + e·c
    （e 倍は Frobenius 作用 d と可換——係数の並べ替え）。 -/
theorem pullback_linear {d m m' c : Nat} (e : Nat)
    (h : m' = d * m + c) : e * m' = d * (e * m) + e * c := by
  rw [h, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm e d, Nat.mul_assoc]

/-- 引き戻しの合成の因子部分: e·(d·x + y) = d·(e·x) + e·y。 -/
theorem pullback_comp_c (e d x y : Nat) :
    e * (d * x + y) = d * (e * x) + e * y := by
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm e d, Nat.mul_assoc]

/-- **定理 (M61F-4a): 引き戻し関手** — 分岐指数 e ≥ 1 の base の射に
    沿った因子の引き戻し localFrobenioid → localFrobenioid:
    対象 m ↦ e·m（重複度が分岐指数倍）、射 (d, c) ↦ (d, e·c)
    （効果的因子も e 倍）。関手性（恒等・合成の保存）完全証明。
    [FrdI] §1 の「体拡大に沿った因子の引き戻し π_K ↦ π_L^e」の
    簿記レベルの実体。仮定 he : 1 ≤ e は定義本体では使われない
    （簿記は e = 0 でも型としては閉じる）が、分岐指数 ≥ 1 という
    数学的前提を関手の型に固定するため明示の引数とする。 -/
def pullbackFunctor (e : Nat) (_he : 1 ≤ e) :
    Functor localFrobenioid localFrobenioid where
  onObj := fun (m : Nat) => e * m
  onHom := fun f => ⟨f.d, e * f.c, f.d_pos, pullback_linear e f.linear⟩
  map_id := fun _ => LocalHom.ext rfl (Nat.mul_zero e)
  map_comp := fun f g =>
    LocalHom.ext rfl (pullback_comp_c e g.d f.c g.c)

/-- **定理 (M61F-4b): 引き戻しで次数は分岐指数倍** — 局所 deg =
    重複度そのものなので、「引き戻しで次数が分岐指数倍になる」
    [FrdI] の簿記が定義的等式（rfl）として定理になる。 -/
theorem pullback_deg (e : Nat) (he : 1 ≤ e) (m : Nat) :
    (pullbackFunctor e he).onObj m = e * m :=
  rfl

/-! ## M61F-5: 輸送と全空間の整合 — 純引き戻し射と分解定理 -/

/-- 純引き戻し射の線形条件: e·m = (e·1)·m + 0。 -/
theorem ram_pullback_linear (e m : Nat) : e * m = e * 1 * m + 0 := by
  rw [Nat.mul_one, Nat.add_zero]

/-- **定理 (M61F-5a): 純引き戻し射** — 段 n から n' への base の射
    （分岐 e）に沿って、任意の重複度 m に対し全空間の射
    (n, m) → (n', e·m) で (le, e, 1, 0)（Frobenius なし・因子加算なし、
    純粋な base 輸送）なるものが存在する。行き先の重複度 e·m は
    引き戻し関手の対象成分 `pullback_deg` と一致する。 -/
def ramPullbackMor {n n' : Nat} (h : n ≤ n') (e : Nat) (he : 1 ≤ e)
    (m : Nat) : RamHom (n, m) (n', e * m) :=
  ⟨h, e, 1, 0, he, Nat.le_refl 1, ram_pullback_linear e m⟩

/-- 純引き戻し射の射影 = base の射そのもの（towerRamify）。 -/
theorem ramProj_pullbackMor {n n' : Nat} (h : n ≤ n') (e : Nat)
    (he : 1 ≤ e) (m : Nat) :
    ramProj.onHom (ramPullbackMor h e he m) = towerRamify h e he :=
  TowerHom.ext rfl

/-- 分解定理の垂直成分の線形条件: m' = (e·d)·m + c なら
    m' = d·(e·m) + c（係数の並べ替え）。 -/
theorem ram_factor_linear {e d m m' c : Nat}
    (h : m' = e * d * m + c) : m' = d * (e * m) + c := by
  rw [h, Nat.mul_comm e d, Nat.mul_assoc]

/-- 分解定理の因子成分: c = (1·d)·0 + c。 -/
theorem ram_factor_c (d c : Nat) : c = 1 * d * 0 + c := by
  rw [Nat.one_mul, Nat.mul_zero, Nat.zero_add]

/-- **定理 (M61F-5b): 分解定理** — 全空間の任意の射 (n, m) → (n', m')
    は、純引き戻し射 (n, m) → (n', e·m) と垂直射（Frobenius d・
    因子 c）の合成に等しい（成分計算で ext: e 成分 e = e·1、
    d 成分 d = 1·d、c 成分 c = (1·d)·0 + c）。[FrdI] の
    「射 = base 輸送と Frobenius-like 部分の合成」の機械検証。 -/
theorem ram_hom_factor {n n' m m' : Nat} (f : RamHom (n, m) (n', m')) :
    f = ramifiedFrobenioid.comp
          (ramPullbackMor f.le f.e f.e_pos m)
          ((ramVerticalIncl n').onHom
            ⟨f.d, f.c, f.d_pos, ram_factor_linear f.linear⟩) :=
  RamHom.ext (Nat.mul_one f.e).symm (Nat.one_mul f.d).symm
    (ram_factor_c f.d f.c)

/-- 引き戻し square の因子成分: (1·d)·0 + e·x = (e·1)·x + 0。 -/
theorem ram_square_c (d e x : Nat) :
    1 * d * 0 + e * x = e * 1 * x + 0 := by
  rw [Nat.one_mul, Nat.mul_zero, Nat.zero_add, Nat.mul_one,
      Nat.add_zero]

/-- **定理 (M61F-5c): 輸送と垂直射の整合（引き戻し square）** —
    段 n の垂直射 f : (d, c) を先に行ってから純引き戻し射で段 n' に
    輸送するのと、先に輸送してから引き戻し関手の像の垂直射
    (d, e·c) を行うのは等しい。引き戻し関手 `pullbackFunctor` が
    全空間圏の合成と整合する（= base の射に沿った輸送の自然性）
    ことの機械検証。 -/
theorem pullback_incl_compat {n n' : Nat} (h : n ≤ n') (e : Nat)
    (he : 1 ≤ e) {m m' : Nat} (f : LocalHom m m') :
    ramifiedFrobenioid.comp
        (ramPullbackMor h e he m)
        ((ramVerticalIncl n').onHom ((pullbackFunctor e he).onHom f))
      = ramifiedFrobenioid.comp
          ((ramVerticalIncl n).onHom f)
          (ramPullbackMor h e he m') :=
  RamHom.ext ((Nat.mul_one e).trans (Nat.one_mul e).symm)
    ((Nat.one_mul f.d).trans (Nat.mul_one f.d).symm)
    (ram_square_c f.d e f.c)

/-! ## M61F-6: 剛性 — base の非自明射を足しても同型は自明

    M48F-4（次数）・M51F-10（因子）・M53F（剛性述語）・M57F-8
    （離散 base ファイバー）の系譜の塔 base 版。合成が e・d 成分を
    別々に保つ（(e₁e₂, d₁d₂)）ので、`frob_mul_eq_one_left` を
    各成分に直接適用できる（e·d = 1 から frob_mul_eq_one_left を
    二段適用しても同じ結論だが、成分ごとの方が短い）。新規内容は
    **「同型は塔を昇れない」**: 同型の base 成分は e = 1 かつ段固定
    （le の反対称性でも e = 1 ⟹ 線形条件でも出る）。 -/

/-- **定理 (M61F-6a): 同型の分岐指数は 1** — hom·inv = id の e 成分
    読み出し e·e' = 1 と e, e' ≥ 1 から。**同型は分岐できない**。 -/
theorem ram_iso_e_one {P Q : Nat × Nat}
    (i : CatIso ramifiedFrobenioid P Q) : i.hom.e = 1 :=
  frob_mul_eq_one_left i.hom.e_pos i.inv.e_pos
    (congrArg RamHom.e i.hom_inv)

/-- **定理 (M61F-6b): 同型の Frobenius 次数は 1**。 -/
theorem ram_iso_d_one {P Q : Nat × Nat}
    (i : CatIso ramifiedFrobenioid P Q) : i.hom.d = 1 :=
  frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos
    (congrArg RamHom.d i.hom_inv)

/-- **定理 (M61F-6c): 同型の因子部分は 0** — hom·inv = id の c 成分
    読み出し (e'·d')·c + c' = 0 で、inv の e = d = 1 を先に確定させて
    1 倍に潰せば線形になり omega が通る（var×var を作らない、規約3）。 -/
theorem ram_iso_c_zero {P Q : Nat × Nat}
    (i : CatIso ramifiedFrobenioid P Q) : i.hom.c = 0 := by
  have he : i.inv.e = 1 :=
    frob_mul_eq_one_left i.inv.e_pos i.hom.e_pos
      (congrArg RamHom.e i.inv_hom)
  have hd : i.inv.d = 1 :=
    frob_mul_eq_one_left i.inv.d_pos i.hom.d_pos
      (congrArg RamHom.d i.inv_hom)
  have hc : i.inv.e * i.inv.d * i.hom.c + i.inv.c = 0 :=
    congrArg RamHom.c i.hom_inv
  -- 1·1·c は単一の Nat.one_mul で潰れる（unifier が 1·1 ≡ 1 を
  -- defeq で読むため、外側の積が一発でマッチする）
  rw [he, hd, Nat.one_mul] at hc
  omega

/-- **定理 (M61F-6d): 同型は対象を動かせない（塔を昇れない）** —
    P ≅ Q ⟹ P = Q。段成分は hom.le と inv.le の反対称性、重複度成分は
    (e, d, c) = (1, 1, 0) を線形条件に代入。**base の非自明射を
    足しても剛性は保たれる**（M57F-8c の遺伝 + 新規に「同型は塔を
    昇れない」）。 -/
theorem ram_iso_objects_eq {P Q : Nat × Nat}
    (i : CatIso ramifiedFrobenioid P Q) : P = Q := by
  have he : i.hom.e = 1 := ram_iso_e_one i
  have hd : i.hom.d = 1 := ram_iso_d_one i
  have hc : i.hom.c = 0 := ram_iso_c_zero i
  have hl : Q.2 = i.hom.e * i.hom.d * P.2 + i.hom.c := i.hom.linear
  rw [he, hd, hc, Nat.one_mul, Nat.add_zero] at hl
  have hb : P.1 = Q.1 := Nat.le_antisymm i.hom.le i.inv.le
  cases P with | mk n m =>
  cases Q with | mk n' m' =>
  have hb' : n = n' := hb
  have hm : m' = m := hl
  subst hb'
  subst hm
  rfl

/-- **系 (M61F-6d'): ramifiedFrobenioid は gaunt**（M53F-1 の述語）。 -/
theorem ramifiedFrobenioid_gaunt : IsGaunt ramifiedFrobenioid :=
  fun _ _ i => ram_iso_objects_eq i

/-- **定理 (M61F-6e): 同型の一意性（剛性）** — 任意の二対象間の同型は
    hom 成分が一意（(e, d, c) = (1, 1, 0) に固定。le は proof
    irrelevance で自動一致）。poly-isomorphism は単集合のまま:
    **Frobenius-like 剛性は base の非自明射に遺伝する**。 -/
theorem ram_iso_unique : IsoUnique ramifiedFrobenioid :=
  fun _ _ i j =>
    RamHom.ext ((ram_iso_e_one i).trans (ram_iso_e_one j).symm)
      ((ram_iso_d_one i).trans (ram_iso_d_one j).symm)
      ((ram_iso_c_zero i).trans (ram_iso_c_zero j).symm)

/-- **系 (M61F-6e'): CatIso 全体としての一意性**（M22-1a CatIso.ext
    経由、M53F-1 isoUnique_subsingleton の発動）。 -/
theorem ram_rigid {P Q : Nat × Nat}
    (i j : CatIso ramifiedFrobenioid P Q) : i = j :=
  isoUnique_subsingleton ram_iso_unique i j

/-! ## M61F-7: 非可逆性の新形 — 塔は降りられず、分岐は戻せない -/

/-- **定理 (M61F-7a): 降下射の不在** — n < n' なら (n', m') から
    (n, m) への射は（重複度がいくつであっても）**存在しない**
    （le の向き）。M57F の no_cross_prime_hom（素点が違えば射は空）の
    塔版: **塔は昇るだけで降りられない**。Frobenius-like 非可逆性
    （M48F の frob_no_right_inverse）が base 方向にも現れる。 -/
theorem ram_no_descent {n n' m m' : Nat} (h : n < n') :
    ¬ Nonempty (RamHom (n', m') (n, m)) :=
  fun ⟨f⟩ => absurd f.le (Nat.not_le.mpr h)

/-- **定理 (M61F-7b): 分岐 e ≥ 2 の純引き戻し射は同型でない** —
    分岐する base 輸送を hom とする同型は存在しない（同型なら
    e = 1 のはずだが純引き戻し射の e は 2 以上、矛盾）。
    「分岐は圏の中で戻せない」の具体的証人つき機械検証。 -/
theorem pullback_not_invertible {n n' : Nat} (hle : n ≤ n') {e : Nat}
    (he : 1 ≤ e) (h2 : 2 ≤ e) (m : Nat) :
    ¬ ∃ i : CatIso ramifiedFrobenioid (n, m) (n', e * m),
        i.hom = ramPullbackMor hle e he m :=
  fun ⟨i, hi⟩ => by
    have h1 : i.hom.e = 1 := ram_iso_e_one i
    rw [hi] at h1
    have h1' : e = 1 := h1
    omega

end IUT
