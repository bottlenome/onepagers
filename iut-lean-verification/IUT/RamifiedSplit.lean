/-
  IUT/RamifiedSplit.lean — M63F（分岐塔 base 上の単数つき全空間圏:
  M59F × M61F の合成）の形式化

  ## 動機

  [FrdI] の Frobenioid の射は本来「base の射・Frobenius 次数 deg_Fr・
  効果的因子 Div・単数 u」の四つ組データに分解される。既存の形式化は
  この四つ組を二方向から建設してきた:

  * M59F `splitFiberedFrobenioid`（IUT/SplitFibered.lean）— 離散 base
    （素点の添字）上の単数つきファイバー射 (base_eq, d, c, u)。ただし
    base は離散圏で、「base の射に沿った因子・単数の輸送」は未形式化と
    正直に申告。
  * M61F `ramifiedFrobenioid`（IUT/RamifiedBase.lean）— 塔 base
    （局所体の塔の段 + 分岐指数 e）上の分岐つき射 (le, e, d, c)。
    ただし**単数なし**で、「M59F の split 構造との合成『塔 base 上の
    単数つき全空間圏』は未形式化（単数が引き戻しでどう変換されるかの
    モデル選択が要る）」と正直に申告。

  本モジュールは両者を合成し、**分岐塔 base 上の単数つき全空間圏**
  `ramSplitFrobenioid U hU`（対象 = (塔の段 n, 重複度 m)、射 =
  (le, e, d, c, u)）を建設する。これにより M61F の「単数なし」申告と
  M59F の「base は離散圏」申告が同時に解消され、[FrdI] の射データ
  四つ組（base の射 = 分岐指数 e, deg_Fr = d, Div = c, 単数 u）の
  **塔 base での完全版**が得られる。

  単数の変換則のモデル選択: 合成の単数成分は**第二射の合成倍率
  e₂·d₂ で捻る** u(f·g) = u(f)^{e₂d₂}·u(g)。M59F では捻りの指数は
  Frobenius 次数 d₂ のみだったが、塔 base では base の射（分岐 e₂）に
  沿った引き戻しも単数を冪で変換する（簿記レベルの簡約モデル——
  本物の「ノルム・単数群の指数」は下記の正直な申告参照）ので、
  因子簿記の線形条件 m' = (e·d)·m + c と同じ合成倍率 e·d を採用する。

  ## 単数結合則の紙上検証（圏公理に入る前の代数核）

  射 f, g, h の合成で単数成分は
    LHS (f·g)·h: (u₁^{e₂d₂}·u₂)^{e₃d₃}·u₃
    RHS f·(g·h): u₁^{(e₂e₃)(d₂d₃)}·(u₂^{e₃d₃}·u₃)
  LHS を展開すると
    (u₁^{e₂d₂}·u₂)^{e₃d₃}·u₃
      = (u₁^{e₂d₂})^{e₃d₃}·u₂^{e₃d₃}·u₃   （gpow_mul_dist、**可換性が必要**）
      = u₁^{(e₂d₂)(e₃d₃)}·u₂^{e₃d₃}·u₃     （gpow_mul の逆向き）
      = u₁^{(e₂e₃)(d₂d₃)}·u₂^{e₃d₃}·u₃     （指数の並べ替え ram_mul_swap、
                                              congrArg (gpow U u₁) で冪に適用）
      = u₁^{(e₂e₃)(d₂d₃)}·(u₂^{e₃d₃}·u₃)   （mul_assoc）
  で RHS に一致する。gpow_mul_dist は非可換群では偽（M55F ヘッダの
  紙上検証）なので、U には可換性 hU を仮定する（M55F/M59F と同じ
  数学的必然。実際の O^× は可換なのでモデルとして正当）。

  ## 検証する定理（全て sorry なし・選択公理なし）

  * M63F-1 `RamSplitHom` / `RamSplitHom.ext` — 分岐塔 base 上の
    単数つき射 (le : n ≤ n', e ≥ 1, d ≥ 1, c : ℕ, u : U) with
    m' = e·d·m + c。u は線形条件に関与しない（split）。ext: 射の等号は
    (e, d, c, u) 成分で決まる（le・linear は Prop）
  * M63F-2 `ramSplitFrobenioid U hU : Cat` — 対象 = (塔の段, 重複度)、
    恒等 = (le_refl, 1, 1, 0, 1)、合成 = (le_trans, e₁e₂, d₁d₂,
    (e₂d₂)c₁+c₂, u₁^{e₂d₂}·u₂)。圏公理完全証明（因子は M61F の ram_*
    補題、単数は上の紙上検証どおり gpow_mul_dist + gpow_mul +
    ram_mul_swap + mul_assoc）
  * M63F-3 `rsForgetUnit` / `rsProj` / `rsProj_onObj_factor` /
    `rsProj_onHom_factor` — 忘却関手（u を捨てて ramifiedFrobenioid へ）
    と射影関手（塔 base へ）の関手性、＋三角形 rsProj = ramProj ∘
    rsForgetUnit（関手合成は未定義なので対象・射の成分等式 2 本、
    どちらも定義的に rfl）
  * M63F-4 `rsPullbackMor` / `rsVerticalMor` / `rs_hom_factor` —
    純引き戻し射 (le, e, 1, 0, 1) : (n, m) → (n', e·m)（Frobenius
    なし・因子なし・単数なし、純粋な base 輸送）と**分解定理**:
    任意の射 = 純引き戻し射 ∘ 垂直単数つき射 (le_refl, 1, d, c, u)
    （成分計算で ext。単数成分は 1^{1·d}·u = u）。M61F-5b の単数つき版
  * M63F-5 `rs_iso_e_one` / `rs_iso_d_one` / `rs_iso_c_zero` /
    `rs_iso_objects_eq` / `ramSplitFrobenioid_gaunt` / `rsUnitIso` /
    `rsIsoToUnit` / `rs_polyiso_torsor` — **剛性と単数トーソルの両立**:
    同型は (e, d, c) = (1, 1, 0) を強制し段も重複度も動かせない
    （gaunt。合成が e・d を別々に保つので frob_mul_eq_one_left を
    各成分に直接適用、c は inv の e = d = 1 を確定させて omega）が、
    単数は任意（任意の u で (le_refl, 1, 1, 0, u) が自己同型、逆は
    u⁻¹）で、自己同型全体は U.carrier と明示的全単射（U-トーソル、
    M59F-5e 方式）
  * M63F-6 `rs_forget_iso_unique` / `rs_forget_mapIso_eq` /
    `rs_not_iso_unique` / `rs_dichotomy` — **二分法の最終形**:
    (1) 忘却像（塔 base + 分岐 + 因子簿記）では任意の二同型が一致 =
    base・分岐・因子部分は剛的で不定性ゼロ、(2) U 非自明なら hom の
    異なる自己同型対が実在 = 不定性は実在し (1) と合わせて**単数成分に
    のみ**宿る。**塔 base・分岐・ファイバー・単数を全部入れても
    (Ind2) 型不定性は単数成分にのみ宿る**——M53F→M55F→M57F→M59F→
    M61F の系譜の完結
  * M63F-7 `rs_pullback_not_invertible` — 分岐 e ≥ 2 の純引き戻し射を
    hom とする同型は存在しない（M61F-7b の単数つき版: 単数を足しても
    分岐は圏の中で戻せない）

  ## 正直な申告（モデルと本物の差）

  * **単一素点の塔のみ**: M61F と同じく base は一本の局所体の塔
    K₀ ⊆ K₁ ⊆ … の全順序圏であり、数体の素点の圏が持つ複数素点への
    分解（分解数 g）・惰性（剰余次数 f）は未形式化。M59F の離散 base
    （素点の添字）と本モジュールの塔 base の「直積」（素点ごとに塔が
    立つ base 圏）も未形式化。
  * **U は抽象可換群であり O^× の実体ではない**: 単数の「簿記としての
    運ばれ方」だけを抽象群でモデル化した。**「単数の引き戻しはノルム
    （あるいは単数群の間の норм 写像・指数写像）で変換される」という
    局所体論の実体はなく**、捻りの指数 e·d は因子簿記の合成倍率を
    そのまま流用した簿記レベルのモデル選択である。段ごとに異なる
    単数群（U を塔の上の群の族にし、射に沿った押し出し・引き戻しを
    持たせる）も見ていない。全段で同一の U を使うのは簡約であり
    隠していない。
  * **e は抽象パラメータ**: M61F と同じく、分岐指数 e は射のデータと
    して公理的に与えられ、実際の体拡大から計算されない。
  * **不分岐部分の分離なし**: 「e = 1 の射だけからなる不分岐部分塔」の
    部分圏の理論は展開していない（M61F と同じ）。
  * 選択公理・追加公理は不使用（全定理 propext/Quot.sound 以下、
    Classical.choice は不要）。
-/
import IUT.RamifiedBase
import IUT.SplitFrobenioid

namespace IUT

/-! ## M63F-1: 分岐塔 base 上の単数つき射 RamSplitHom

    [FrdI] の射データ四つ組 (base の射, deg_Fr, Div, u) の塔 base 版。
    (le, e) は塔 base の射（M61F の TowerHom）、(d, c) は捻れ半直積型の
    因子簿記、u は線形条件に関与しない単数成分（M55F/M59F の split
    構造）。 -/

/-- **分岐塔 base 上の単数つき射**: (n, m) → (n', m') は base 成分
    (le : n ≤ n', 分岐指数 e ≥ 1)・Frobenius 次数 d ≥ 1・効果的因子
    c : ℕ・単数 u : U の組で、線形条件 m' = e·d·m + c を満たすもの。
    u は線形条件に現れない（split 構造）。M61F の RamHom に M59F の
    単数成分を足した [FrdI] の射データ完全版。 -/
structure RamSplitHom (U : Grp) (P Q : Nat × Nat) where
  /-- base 成分: 塔の段の比較。 -/
  le : P.1 ≤ Q.1
  /-- 分岐指数（base の射が運ぶ輸送データ）。 -/
  e : Nat
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的因子部分。 -/
  c : Nat
  /-- 単数成分 u(φ)。 -/
  u : U.carrier
  e_pos : 1 ≤ e
  d_pos : 1 ≤ d
  /-- 重複度の変換則: m' = e·d·m + c（u は関与しない）。 -/
  linear : Q.2 = e * d * P.2 + c

/-- 射の外延性: RamSplitHom は (e, d, c, u) 成分で決まる（le は Prop
    なので proof irrelevance により自動で一致、linear も Prop）。 -/
theorem RamSplitHom.ext {U : Grp} {P Q : Nat × Nat}
    {f g : RamSplitHom U P Q}
    (he : f.e = g.e) (hd : f.d = g.d) (hc : f.c = g.c)
    (hu : f.u = g.u) : f = g := by
  cases f with | mk fle fe fd fc fu f1 f2 f3 =>
  cases g with | mk gle ge gd gc gu g1 g2 g3 =>
  have he' : fe = ge := he
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  have hu' : fu = gu := hu
  subst he'
  subst hd'
  subst hc'
  subst hu'
  rfl

/-! ## M63F-2: 分岐塔 base 上の単数つき全空間圏 -/

/-- **定理 (M63F-2): ramified split Frobenioid** — 対象 = (塔の段,
    重複度)、射 = (le, e, d, c, u)。恒等 = (le_refl, 1, 1, 0, 1)、
    合成 = (le_trans, e₁e₂, d₁d₂, (e₂d₂)c₁+c₂, u₁^{e₂d₂}·u₂)
    （単数は第二射の**合成倍率 e₂d₂** で捻られて運ばれる——分岐に
    沿った引き戻しも Frobenius も単数を冪で変換する簿記）。圏公理の
    因子成分は M61F の ram_* 補題、単数成分の結合則はヘッダの紙上検証
    どおり gpow_mul_dist（**ここで可換性 hU が必要**）・gpow_mul・
    指数の並べ替え ram_mul_swap（congrArg で冪の中へ）・mul_assoc、
    base 成分は proof irrelevance（RamSplitHom.ext が吸収）。 -/
def ramSplitFrobenioid (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) : Cat where
  Obj := Nat × Nat
  Hom := RamSplitHom U
  id := fun P =>
    ⟨Nat.le_refl P.1, 1, 1, 0, U.one, Nat.le_refl 1, Nat.le_refl 1,
      ram_id_linear P.2⟩
  comp := fun f g =>
    ⟨Nat.le_trans f.le g.le, f.e * g.e, f.d * g.d,
      g.e * g.d * f.c + g.c,
      U.mul (gpow U f.u (g.e * g.d)) g.u,
      Nat.mul_pos f.e_pos g.e_pos, Nat.mul_pos f.d_pos g.d_pos,
      ram_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    RamSplitHom.ext (Nat.one_mul f.e) (Nat.one_mul f.d)
      (ram_id_comp_c f.e f.d f.c)
      (by show U.mul (gpow U U.one (f.e * f.d)) f.u = f.u
          rw [gpow_one_base, U.one_mul])
  comp_id := fun f =>
    RamSplitHom.ext (Nat.mul_one f.e) (Nat.mul_one f.d)
      (ram_comp_id_c f.c)
      (by show U.mul (gpow U f.u (1 * 1)) U.one = f.u
          rw [Nat.one_mul, gpow_one, U.mul_one])
  assoc := fun f g h =>
    RamSplitHom.ext (Nat.mul_assoc f.e g.e h.e)
      (Nat.mul_assoc f.d g.d h.d)
      (ram_assoc_c g.e g.d h.e h.d f.c g.c h.c)
      (by show U.mul
              (gpow U (U.mul (gpow U f.u (g.e * g.d)) g.u) (h.e * h.d))
              h.u
            = U.mul (gpow U f.u (g.e * h.e * (g.d * h.d)))
                (U.mul (gpow U g.u (h.e * h.d)) h.u)
          rw [gpow_mul_dist U hU, ← gpow_mul,
              ram_mul_swap g.e g.d h.e h.d, U.mul_assoc])

/-! ## M63F-3: 忘却関手の三角形

    ramSplitFrobenioid は ramifiedFrobenioid（単数を忘れる）と
    towerCat（塔 base へ射影）の両方に関手で落ち、射影は忘却を経由して
    分解する（三角形の可換性）。関手合成は本ライブラリに定義されて
    いないため、三角形は対象・射の成分ごとの等式 2 本で述べる
    （どちらも定義的に rfl — M59F-3 方式）。 -/

/-- **定理 (M63F-3a): 単数の忘却関手** ramSplitFrobenioid →
    ramifiedFrobenioid — 単数成分 u を捨てる対応は関手（恒等・合成の
    base・分岐・因子成分は両圏で同一の式なので外延性で即座）。
    M59F の sfForgetUnit の塔 base 版。 -/
def rsForgetUnit (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) :
    Functor (ramSplitFrobenioid U hU) ramifiedFrobenioid where
  onObj := fun P => P
  onHom := fun f => ⟨f.le, f.e, f.d, f.c, f.e_pos, f.d_pos, f.linear⟩
  map_id := fun _ => RamHom.ext rfl rfl rfl
  map_comp := fun _ _ => RamHom.ext rfl rfl rfl

/-- **定理 (M63F-3b): 射影関手** ramSplitFrobenioid → towerCat —
    対象 (n, m) を塔の段 n に、射をその base 成分 (le, e) に送る。
    関手性は e 成分の合成保存から（M61F の ramProj と同じ理由）。 -/
def rsProj (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) :
    Functor (ramSplitFrobenioid U hU) towerCat where
  onObj := fun P => P.1
  onHom := fun f => ⟨f.le, f.e, f.e_pos⟩
  map_id := fun _ => TowerHom.ext rfl
  map_comp := fun _ _ => TowerHom.ext rfl

/-- **定理 (M63F-3c): 三角形の可換性（対象レベル）** —
    rsProj = ramProj ∘ rsForgetUnit が対象上で成立（定義的に rfl）。 -/
theorem rsProj_onObj_factor (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) (P : Nat × Nat) :
    (rsProj U hU).onObj P = ramProj.onObj ((rsForgetUnit U hU).onObj P) :=
  rfl

/-- **定理 (M63F-3d): 三角形の可換性（射レベル）** —
    rsProj = ramProj ∘ rsForgetUnit が射上で成立（定義的に rfl —
    単数を忘れてから塔 base に射影しても、直接射影しても同じ）。 -/
theorem rsProj_onHom_factor (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat} (f : RamSplitHom U P Q) :
    (rsProj U hU).onHom f = ramProj.onHom ((rsForgetUnit U hU).onHom f) :=
  rfl

/-! ## M63F-4: 純引き戻し射と分解定理の単数つき版

    M61F-5 の ramPullbackMor / ram_hom_factor に単数成分を足す。
    純引き戻し射の単数は 1（純粋な base 輸送は単数を持たない）、
    垂直射が (d, c, u) の全データを担う。 -/

/-- **定理 (M63F-4a): 純引き戻し射** — 段 n から n' への base の射
    （分岐 e）に沿って、任意の重複度 m に対し (le, e, 1, 0, 1) :
    (n, m) → (n', e·m)（Frobenius なし・因子なし・単数なし、純粋な
    base 輸送）が存在する。線形条件は M61F の ram_pullback_linear。 -/
def rsPullbackMor (U : Grp) {n n' : Nat} (h : n ≤ n') (e : Nat)
    (he : 1 ≤ e) (m : Nat) : RamSplitHom U (n, m) (n', e * m) :=
  ⟨h, e, 1, 0, U.one, he, Nat.le_refl 1, ram_pullback_linear e m⟩

/-- 純引き戻し射の射影 = base の射そのもの（towerRamify、M61F-5a の
    単数つき版）。 -/
theorem rsProj_pullbackMor (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {n n' : Nat} (h : n ≤ n') (e : Nat) (he : 1 ≤ e) (m : Nat) :
    (rsProj U hU).onHom (rsPullbackMor U h e he m) = towerRamify h e he :=
  TowerHom.ext rfl

/-- **垂直単数つき射** — 段 n を固定した (le_refl, 1, d, c, u)。
    e = 1 = 不分岐（base 方向に動かない）で、Frobenius・因子・単数の
    全データを担う。線形条件は M61F の ram_vert_linear。 -/
def rsVerticalMor (U : Grp) (n : Nat) {m m' : Nat} (d c : Nat)
    (u : U.carrier) (hd : 1 ≤ d) (hl : m' = d * m + c) :
    RamSplitHom U (n, m) (n, m') :=
  ⟨Nat.le_refl n, 1, d, c, u, Nat.le_refl 1, hd, ram_vert_linear hl⟩

/-- **定理 (M63F-4b): 分解定理（単数つき版）** — 全空間の任意の射
    (n, m) → (n', m') は、純引き戻し射 (n, m) → (n', e·m) と垂直単数
    つき射 (le_refl, 1, d, c, u) の合成に等しい（成分計算で ext:
    e 成分 e = e·1、d 成分 d = 1·d、c 成分 c = (1·d)·0 + c、u 成分
    u = 1^{1·d}·u は gpow_one_base + one_mul で潰す）。M61F-5b の
    単数つき版 = [FrdI] の「射 = base 輸送と Frobenius-like 部分の
    合成」の単数込みの機械検証。**単数は垂直成分にのみ宿る**。 -/
theorem rs_hom_factor (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {n n' m m' : Nat} (f : RamSplitHom U (n, m) (n', m')) :
    f = (ramSplitFrobenioid U hU).comp
          (rsPullbackMor U f.le f.e f.e_pos m)
          (rsVerticalMor U n' f.d f.c f.u f.d_pos
            (ram_factor_linear f.linear)) :=
  RamSplitHom.ext (Nat.mul_one f.e).symm (Nat.one_mul f.d).symm
    (ram_factor_c f.d f.c)
    (by show f.u = U.mul (gpow U U.one (1 * f.d)) f.u
        rw [gpow_one_base, U.one_mul])

/-! ## M63F-5: 剛性と単数トーソルの両立

    M61F-6（単数なしの塔 base）と M59F-5（離散 base の単数つき）の
    合成: 全部入りの圏でも base・分岐・因子簿記は剛的（gaunt）なまま、
    単数成分だけが U-トーソルとして自由に残る。 -/

/-- **定理 (M63F-5a): 同型の分岐指数は 1** — hom·inv = id の e 成分
    読み出し e·e' = 1 と e, e' ≥ 1 から（合成が e 成分を別途保つので
    frob_mul_eq_one_left を直接適用）。**単数を足しても同型は分岐
    できない**。 -/
theorem rs_iso_e_one (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i : CatIso (ramSplitFrobenioid U hU) P Q) : i.hom.e = 1 :=
  frob_mul_eq_one_left i.hom.e_pos i.inv.e_pos
    (congrArg (RamSplitHom.e) i.hom_inv)

/-- **定理 (M63F-5b): 同型の Frobenius 次数は 1**。 -/
theorem rs_iso_d_one (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i : CatIso (ramSplitFrobenioid U hU) P Q) : i.hom.d = 1 :=
  frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos
    (congrArg (RamSplitHom.d) i.hom_inv)

/-- **定理 (M63F-5c): 同型の因子部分は 0** — hom·inv = id の c 成分
    読み出し (e'·d')·c + c' = 0 で、inv の e = d = 1 を先に確定させて
    1 倍に潰せば線形になり omega が通る（var×var を作らない、
    M61F-6c 方式）。 -/
theorem rs_iso_c_zero (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i : CatIso (ramSplitFrobenioid U hU) P Q) : i.hom.c = 0 := by
  have he : i.inv.e = 1 :=
    frob_mul_eq_one_left i.inv.e_pos i.hom.e_pos
      (congrArg (RamSplitHom.e) i.inv_hom)
  have hd : i.inv.d = 1 :=
    frob_mul_eq_one_left i.inv.d_pos i.hom.d_pos
      (congrArg (RamSplitHom.d) i.inv_hom)
  have hc : i.inv.e * i.inv.d * i.hom.c + i.inv.c = 0 :=
    congrArg (RamSplitHom.c) i.hom_inv
  rw [he, hd, Nat.one_mul] at hc
  omega

/-- **定理 (M63F-5d): 同型は対象を動かせない（塔を昇れない）** —
    P ≅ Q ⟹ P = Q。段成分は hom.le と inv.le の反対称性、重複度成分は
    (e, d, c) = (1, 1, 0) を線形条件に代入（M61F-6d と同じ）。単数を
    足しても base・分岐・因子部分の剛性はそのまま生き残る。 -/
theorem rs_iso_objects_eq (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i : CatIso (ramSplitFrobenioid U hU) P Q) : P = Q := by
  have he : i.hom.e = 1 := rs_iso_e_one U hU i
  have hd : i.hom.d = 1 := rs_iso_d_one U hU i
  have hc : i.hom.c = 0 := rs_iso_c_zero U hU i
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

/-- **系 (M63F-5d'): ramSplitFrobenioid は gaunt**（M53F-1 の述語）。
    塔 base・分岐・ファイバー・単数の全部入りでも対象は動かせない。 -/
theorem ramSplitFrobenioid_gaunt (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) :
    IsGaunt (ramSplitFrobenioid U hU) :=
  fun _ _ i => rs_iso_objects_eq U hU i

/-- 単数自己射 (le_refl, 1, 1, 0, u): base・分岐・因子簿記は恒等、
    単数だけ u。 -/
def rsUnitEndo (U : Grp) (P : Nat × Nat) (u : U.carrier) :
    RamSplitHom U P P :=
  ⟨Nat.le_refl P.1, 1, 1, 0, u, Nat.le_refl 1, Nat.le_refl 1,
    ram_id_linear P.2⟩

/-- **定理 (M63F-5e): 単数は任意 — (le_refl, 1, 1, 0, u) は同型**
    （逆 = (le_refl, 1, 1, 0, u⁻¹)）。合成の単数捻りの指数は 1·1 で、
    Nat.one_mul + gpow_one で u¹ = u に潰れる。base・分岐・因子部分は
    固定されるのに単数部分は U 全体を走れる: 不定性の在処が単数成分で
    あることの構成的半分（M59F-5d の塔 base 版）。 -/
def rsUnitIso (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (P : Nat × Nat) (u : U.carrier) :
    CatIso (ramSplitFrobenioid U hU) P P where
  hom := rsUnitEndo U P u
  inv := rsUnitEndo U P (U.inv u)
  hom_inv :=
    RamSplitHom.ext (Nat.one_mul 1) (Nat.one_mul 1)
      (ram_id_comp_c 1 1 0)
      (by show U.mul (gpow U u (1 * 1)) (U.inv u) = U.one
          rw [Nat.one_mul, gpow_one]
          exact U.mul_inv u)
  inv_hom :=
    RamSplitHom.ext (Nat.one_mul 1) (Nat.one_mul 1)
      (ram_id_comp_c 1 1 0)
      (by show U.mul (gpow U (U.inv u) (1 * 1)) u = U.one
          rw [Nat.one_mul, gpow_one]
          exact U.inv_mul u)

/-- 同型から単数の読み出し（hom の u 成分）。 -/
def rsIsoToUnit (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i : CatIso (ramSplitFrobenioid U hU) P Q) : U.carrier :=
  i.hom.u

/-- 往復 (unit → iso → unit) は恒等。 -/
theorem rs_unit_iso_unit (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (P : Nat × Nat) (u : U.carrier) :
    rsIsoToUnit U hU (rsUnitIso U hU P u) = u :=
  rfl

/-- 往復 (iso → unit → iso) は恒等: 同型の e・d・c 成分は (1, 1, 0) に
    固定（M63F-5a/5b/5c）、le は proof irrelevance なので、u 成分の
    一致だけで hom が一致し、逆成分は M22-1a `CatIso.ext` で従う。 -/
theorem rs_iso_unit_iso (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P : Nat × Nat}
    (i : CatIso (ramSplitFrobenioid U hU) P P) :
    rsUnitIso U hU P (rsIsoToUnit U hU i) = i :=
  CatIso.ext
    (RamSplitHom.ext (rs_iso_e_one U hU i).symm
      (rs_iso_d_one U hU i).symm (rs_iso_c_zero U hU i).symm rfl)

/-- **定理 (M63F-5f): ramSplitFrobenioid の poly-isomorphism は
    U-トーソル** — 各対象の自己同型全体は U.carrier と明示的全単射
    （往復写像が両向きとも恒等、M59F-5e 方式）。base が剛化され
    （gaunt なので同型は自己同型しかない）、分岐・因子部分が
    (1, 1, 0) に剛化された後に残る自由度がちょうど U 全体:
    **(Ind2) 型不定性の在処**が塔 base・分岐を足しても単数成分の
    ままであることの機械検証。 -/
theorem rs_polyiso_torsor (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (P : Nat × Nat) :
    (∀ i : CatIso (ramSplitFrobenioid U hU) P P,
        rsUnitIso U hU P (rsIsoToUnit U hU i) = i)
      ∧ (∀ u : U.carrier, rsIsoToUnit U hU (rsUnitIso U hU P u) = u) :=
  ⟨fun i => rs_iso_unit_iso U hU i, fun _ => rfl⟩

/-! ## M63F-6: 二分法の最終形 — 全部入りでも不定性は単数成分にのみ宿る -/

/-- **定理 (M63F-6a): 忘却関手の像では同型は一意** — 任意の同型
    i, j : P ≅ Q の hom の忘却像（ramifiedFrobenioid の射）は一致する
    （e・d・c 成分がどれも (1, 1, 0) に固定され、le は proof
    irrelevance だから）。塔 base + 分岐 + 因子簿記レベルでは
    「貼り方の選択肢」が存在しない（M59F-6a の塔 base 版）。 -/
theorem rs_forget_iso_unique (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i j : CatIso (ramSplitFrobenioid U hU) P Q) :
    (rsForgetUnit U hU).onHom i.hom = (rsForgetUnit U hU).onHom j.hom :=
  RamHom.ext
    ((rs_iso_e_one U hU i).trans (rs_iso_e_one U hU j).symm)
    ((rs_iso_d_one U hU i).trans (rs_iso_d_one U hU j).symm)
    ((rs_iso_c_zero U hU i).trans (rs_iso_c_zero U hU j).symm)

/-- **系 (M63F-6a'): CatIso ごと忘却しても一意** — 同型の mapIso 像は
    ramifiedFrobenioid の剛性（M61F-6e'）により完全に一致する。 -/
theorem rs_forget_mapIso_eq (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i j : CatIso (ramSplitFrobenioid U hU) P Q) :
    Functor.mapIso (rsForgetUnit U hU) i
      = Functor.mapIso (rsForgetUnit U hU) j :=
  ram_rigid _ _

/-- **定理 (M63F-6b): U 非自明なら ramSplitFrobenioid は剛的でない**
    — 単位元以外の単数 u があれば (le_refl,1,1,0,u) と (le_refl,1,1,0,1)
    が異なる自己同型になる（ramifiedFrobenioid は IsoUnique だった
    （M61F-6e）——単数を足した瞬間に剛性が壊れる。M59F-6b の塔 base
    版）。 -/
theorem rs_not_iso_unique (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (h : ∃ u : U.carrier, u ≠ U.one) :
    ¬ IsoUnique (ramSplitFrobenioid U hU) := by
  intro hiso
  obtain ⟨u, hu⟩ := h
  exact hu (congrArg RamSplitHom.u
    (hiso (0, 0) (0, 0) (rsUnitIso U hU (0, 0) u)
      (rsUnitIso U hU (0, 0) U.one)))

/-- **定理 (M63F-6c): 二分法の最終形** — 塔 base・分岐・ファイバー・
    単数を全部入れた一つの圏 ramSplitFrobenioid の中で:
    (1) 任意の二つの同型は忘却像（塔 base + 分岐 + 因子簿記）が
        一致する = base・分岐・因子部分は剛的で不定性ゼロ、
    (2) U 非自明なら hom が異なる自己同型の対が実在する = 不定性は
        実在し、(1) と合わせてそれは**単数成分にのみ**宿る。
    [FrdI] の射データ四つ組（base の射 = 分岐指数, deg_Fr, Div, 単数）
    を塔 base で全て備えたモデルでも (Ind2) 型不定性（[IUTchIII]
    定理3.11 (i) の Ism のコピーの作用）の在処は単数部分に分離された
    まま、という M53F→M55F→M57F→M59F→M61F の系譜の完結。 -/
theorem rs_dichotomy (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (h : ∃ u : U.carrier, u ≠ U.one) :
    (∀ (P Q : Nat × Nat)
        (i j : CatIso (ramSplitFrobenioid U hU) P Q),
        (rsForgetUnit U hU).onHom i.hom
          = (rsForgetUnit U hU).onHom j.hom)
      ∧ (∃ (P : Nat × Nat)
          (i j : CatIso (ramSplitFrobenioid U hU) P P),
          i.hom ≠ j.hom) := by
  constructor
  · exact fun P Q i j => rs_forget_iso_unique U hU i j
  · obtain ⟨u, hu⟩ := h
    exact ⟨(0, 0), rsUnitIso U hU (0, 0) u, rsUnitIso U hU (0, 0) U.one,
      fun heq => hu (congrArg RamSplitHom.u heq)⟩

/-! ## M63F-7: 非可逆性 — 単数を足しても分岐は戻せない -/

/-- **定理 (M63F-7): 分岐 e ≥ 2 の純引き戻し射は同型でない** —
    分岐する base 輸送を hom とする同型は存在しない（同型なら e = 1
    のはずだが純引き戻し射の e は 2 以上、矛盾）。M61F-7b の単数つき
    版: **単数の自由度を足しても分岐は圏の中で戻せない**（トーソルに
    なるのは e = d = 1・c = 0 の自己同型だけで、分岐射は決して同型に
    ならない）。 -/
theorem rs_pullback_not_invertible (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {n n' : Nat} (hle : n ≤ n') {e : Nat}
    (he : 1 ≤ e) (h2 : 2 ≤ e) (m : Nat) :
    ¬ ∃ i : CatIso (ramSplitFrobenioid U hU) (n, m) (n', e * m),
        i.hom = rsPullbackMor U hle e he m :=
  fun ⟨i, hi⟩ => by
    have h1 : i.hom.e = 1 := rs_iso_e_one U hU i
    rw [hi] at h1
    have h1' : e = 1 := h1
    omega

end IUT
