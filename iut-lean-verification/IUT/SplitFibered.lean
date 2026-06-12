/-
  IUT/SplitFibered.lean — M59F（split × fibered の合成: 離散 base 上の
  単数つきファイバー Frobenioid）の形式化

  ## 動機

  [FrdI] の Frobenioid の射は本来「base の射・Frobenius 次数 deg_Fr・
  効果的因子 Div・単数 u」のデータに分解される。既存の形式化は
  この分解を二方向に分けて建設してきた:

  * M55F `splitFrobenioid`（IUT/SplitFrobenioid.lean）— 射に単数成分
    (d, c, u) を持たせた split 構造。ただし **base 圏は一点**で、
    「base 圏（素点の圏）上のファイバー構造は未形式化」と正直に申告。
  * M57F `fiberedFrobenioid`（IUT/FiberedFrobenioid.lean）— 離散 base
    （素点の添字 ℕ）上のファイバー構造 (base_eq, d, c)。ただし
    **単数なし**で、「単数成分（M55F の split 構造）との合成は範囲外」
    と正直に申告。

  本モジュールは両者を合成し、**離散 base 上の単数つきファイバー
  Frobenioid** `splitFiberedFrobenioid U hU`（対象 = (素点, 重複度)、
  射 = (base_eq, d, c, u)）を建設する。これにより M55F・M57F 双方の
  上記の正直申告が同時に解消され、[FrdI] の射データ四つ組
  （base の射, deg_Fr, Div, 単数）の**最も完全な離散版**が得られる。

  検証の核心は M53F→M55F→M57F と続いてきた二分法の最終形である:

  * **base・因子簿記は剛的** — 同型は (d, c) = (1, 0) を強制し、
    素点も重複度も動かせない（gaunt）。
  * **単数成分だけがトーソル** — 各対象の自己同型全体は U.carrier と
    明示的全単射（U-トーソル）。

  すなわち、離散 base・ファイバー構造・単数を**全部入れても**
  「(Ind2) 型不定性（[IUTchIII] 定理3.11 (i) の Ism のコピーの作用）は
  単数成分にのみ宿る」が保たれる（`sf_dichotomy`）。

  ## 単数結合則の可換性（M55F からの継承）

  合成の単数成分は M55F と同じく u(f·g) = u(f)^{d(g)} · u(g)
  （第二射の Frobenius 次数で捻る — Frobenius が単数を d 乗する
  [FrdI] の簿記）。結合則には (ab)^n = a^n b^n（`gpow_mul_dist`）が
  必要で、これは非可換群では偽（M55F ヘッダの紙上検証参照）。
  よって U には可換性 `hU : ∀ a b, U.mul a b = U.mul b a` を仮定する
  （実際の O^× は可換なのでモデルとして正当）。

  ## 検証する定理（全て sorry なし・選択公理なし）

  * M59F-1 `SplitFibHom` / `SplitFibHom.ext` — 単数つきファイバー射
    (base_eq : k = l, d ≥ 1, c : ℕ, u : U) with m' = d·m + c。
    単数 u は線形条件に関与しない（split）、base_eq は等号の証明のみ
    （離散 base）。ext: 射の等号は (d, c, u) 成分で決まる
  * M59F-2 `splitFiberedFrobenioid U hU : Cat` — 対象 = (素点, 重複度)、
    恒等 = (rfl, 1, 0, 1)、合成 = (Eq.trans, d₁d₂, d₂c₁+c₂, u₁^{d₂}·u₂)。
    圏公理完全証明（因子簿記は M57F の local_* 補題、単数は M55F の
    gpow_mul_dist + gpow_mul + mul_assoc、base は ext が吸収）
  * M59F-3 `sfForgetUnit` / `sfProj` / `sfProj_onObj_factor` /
    `sfProj_onHom_factor` — 忘却関手（u を捨てて fiberedFrobenioid へ）と
    射影関手（base へ）の関手性、＋三角形 sfProj = fibProj ∘ sfForgetUnit
    （関手合成は未定義なので対象・射の成分ごとの等式 2 本で、どちらも
    定義的に rfl）
  * M59F-4 `LocalSplitHom` / `localSplitFrobenioid` / `sfFiberIncl` /
    `sfFiberRestrictHom` / `sf_fiber_local_iso` — 一素点上の**局所 split
    圏**（対象 = 重複度 ℕ、射 = (d, c, u)）の圏公理と、素点 k の
    ファイバーへの包含関手の忠実充満（onHom の全単射性を往復写像の
    両向き恒等で機械検証、M57F-5 方式）。M55F の splitFrobenioid は
    対象 = 大域因子 QDiv なのでファイバーとは型が合わない——ファイバーの
    正しい局所モデルは本モジュールの localSplitFrobenioid である
  * M59F-5 `sf_iso_d_one` / `sf_iso_c_zero` / `sf_iso_objects_eq` /
    `splitFiberedFrobenioid_gaunt` / `sfUnitIso` / `sfIsoToUnit` /
    `sf_polyiso_torsor` — **剛性と単数トーソルの両立**: 同型は
    (d, c) = (1, 0) を強制し素点も重複度も動かせない（gaunt。
    d·d' = 1 は frob_mul_eq_one_left、c は inv.d = 1 を先に確定させて
    omega — M57F-8b 方式）が、単数は任意（任意の u で (rfl, 1, 0, u) が
    自己同型）で、自己同型全体は U.carrier と明示的全単射
    （U-トーソル、M55F-6 方式）
  * M59F-6 `sf_forget_iso_unique` / `sf_forget_mapIso_eq` /
    `sf_not_iso_unique` / `sf_dichotomy` — **二分法の総括**:
    (1) 忘却関手 sfForgetUnit の像では任意の二同型が一致（因子簿記 +
    base は剛的 = 不定性ゼロ）、(2) U 非自明なら hom の異なる自己同型対が
    実在（不定性は実在し、(1) と合わせて単数成分にのみ宿る）。
    離散 base・ファイバー構造・単数を全部入れた圏でも「(Ind2) 型不定性は
    単数成分にのみ宿る」が保たれることの最終形

  ## 正直な申告（モデルと本物の差）

  * **base は離散圏**: M57F と同じく、本物の base 圏（素点の圏、
    connected anabelioid の圏）が持つ素点間の射（分解・惰性・分岐、
    体拡大に沿った押し出し）は持たない。「base の射に沿った因子・単数の
    輸送」は未形式化のまま。
  * **U は抽象可換群であり O^× の実体ではない**: M55F と同じく、単数の
    「簿記としての運ばれ方」（Frobenius で d 乗されて合成される）だけを
    抽象群でモデル化した。位相・filtration（M28–M30）・素点ごとに異なる
    単数群を取る（U を base 上の群の族にする）ことは見ていない。
    全素点で同一の U を使うのは簡約であり隠していない。
  * **アルキメデス素点・realification は範囲外**（M51F 以来の申告と同じ）。
  * **ファイバーの局所対象は重複度 ℕ**: M55F の大域因子 QDiv との
    「大域 split ⊗ ファイバー」型の合成（対象 = (素点, 大域因子)）では
    なく、M57F の流儀（各素点上の局所重複度）に単数を足した。M57F-6 の
    divRestrictFunctor に対応する「大域 split 圏からの制限」は、大域側の
    単数をどの素点に配るかのモデル選択（単数の局所化）が必要になるため
    未形式化。
  * 選択公理・追加公理は不使用（全定理 propext/Quot.sound 以下）。
-/
import IUT.SplitFrobenioid
import IUT.FiberedFrobenioid

namespace IUT

/-! ## M59F-1: 単数つきファイバー射 SplitFibHom

    [FrdI] の射データ四つ組 (base の射, deg_Fr, Div, u) の離散 base 版。
    base_eq は素点の一致の証明（離散 base 圏の射、M57F）、(d, c) は
    捻れ半直積型の因子簿記（M57F）、u は線形条件に関与しない単数成分
    （M55F の split 構造）。 -/

/-- **単数つきファイバー射**: (k, m) → (l, m') は base 成分 = 素点の
    一致の証明 base_eq : k = l、Frobenius 次数 d ≥ 1、効果的因子 c : ℕ、
    単数 u : U の組で、線形条件 m' = d·m + c を満たすもの。
    u は線形条件に現れない（split 構造）。 -/
structure SplitFibHom (U : Grp) (P Q : Nat × Nat) where
  /-- base 成分: 素点の一致（離散 base 圏の射）。 -/
  base_eq : P.1 = Q.1
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的因子部分（その素点での重複度の増分）。 -/
  c : Nat
  /-- 単数成分 u(φ)。 -/
  u : U.carrier
  d_pos : 1 ≤ d
  /-- 重複度の変換則: m' = d·m + c（u は関与しない）。 -/
  linear : Q.2 = d * P.2 + c

/-- 射の外延性: SplitFibHom は (d, c, u) 成分で決まる（base_eq は
    Prop の証明なので proof irrelevance により自動で一致、linear も
    Prop）。 -/
theorem SplitFibHom.ext {U : Grp} {P Q : Nat × Nat}
    {f g : SplitFibHom U P Q}
    (hd : f.d = g.d) (hc : f.c = g.c) (hu : f.u = g.u) : f = g := by
  cases f with | mk fb fd fc fu f1 f2 =>
  cases g with | mk gb gd gc gu g1 g2 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  have hu' : fu = gu := hu
  subst hd'
  subst hc'
  subst hu'
  rfl

/-! ## M59F-2: 離散 base 上の単数つきファイバー Frobenioid -/

/-- **定理 (M59F-2): split fibered Frobenioid** — 対象 = (素点の添字,
    重複度)、射 = (base の等号, Frobenius 次数, 効果的因子, 単数)。
    恒等 = (rfl, 1, 0, 1)、合成 = (Eq.trans, d₁d₂, d₂c₁+c₂, u₁^{d₂}·u₂)
    （単数は第二射の Frobenius 次数で捻られて運ばれる — M55F と同じ
    [FrdI] の簿記）。圏公理の因子成分は M57F の local_* 補題、単数成分の
    結合則は gpow_mul_dist（**ここで可換性 hU が必要**）・gpow_mul・
    mul_assoc、base 成分は proof irrelevance（SplitFibHom.ext が吸収）。 -/
def splitFiberedFrobenioid (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) : Cat where
  Obj := Nat × Nat
  Hom := SplitFibHom U
  id := fun P => ⟨rfl, 1, 0, U.one, Nat.le_refl 1, local_id_linear P.2⟩
  comp := fun f g =>
    ⟨f.base_eq.trans g.base_eq, f.d * g.d, g.d * f.c + g.c,
      U.mul (gpow U f.u g.d) g.u,
      Nat.mul_pos f.d_pos g.d_pos,
      local_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    SplitFibHom.ext (Nat.one_mul f.d) (local_id_comp_c f.d f.c)
      (by show U.mul (gpow U U.one f.d) f.u = f.u
          rw [gpow_one_base, U.one_mul])
  comp_id := fun f =>
    SplitFibHom.ext (Nat.mul_one f.d) (local_comp_id_c f.c)
      (by show U.mul (gpow U f.u 1) U.one = f.u
          rw [gpow_one, U.mul_one])
  assoc := fun f g h =>
    SplitFibHom.ext (Nat.mul_assoc f.d g.d h.d)
      (local_assoc_c g.d h.d f.c g.c h.c)
      (by show U.mul (gpow U (U.mul (gpow U f.u g.d) g.u) h.d) h.u
            = U.mul (gpow U f.u (g.d * h.d))
                (U.mul (gpow U g.u h.d) h.u)
          rw [gpow_mul_dist U hU, ← gpow_mul, U.mul_assoc])

/-! ## M59F-3: 忘却関手の三角形

    splitFiberedFrobenioid は fiberedFrobenioid（単数を忘れる）と
    discCat Nat（base へ射影）の両方に関手で落ち、射影は忘却を経由して
    分解する（三角形の可換性）。関手合成は本ライブラリに定義されて
    いないため、三角形は対象・射の成分ごとの等式 2 本で述べる
    （どちらも定義的に rfl — 三つの関手の定義が文字通り整合している）。 -/

/-- **定理 (M59F-3a): 単数の忘却関手** splitFiberedFrobenioid →
    fiberedFrobenioid — 単数成分 u を捨てる対応は関手（恒等・合成の
    base・因子成分は両圏で同一の式なので外延性で即座）。M55F の
    splitForget のファイバー版。 -/
def sfForgetUnit (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) :
    Functor (splitFiberedFrobenioid U hU) fiberedFrobenioid where
  onObj := fun P => P
  onHom := fun f => ⟨f.base_eq, f.d, f.c, f.d_pos, f.linear⟩
  map_id := fun _ => FibHom.ext rfl rfl
  map_comp := fun _ _ => FibHom.ext rfl rfl

/-- **定理 (M59F-3b): 射影関手** splitFiberedFrobenioid → discCat Nat —
    対象 (k, m) を素点 k に、射をその base 成分に送る。関手性は
    proof irrelevance により rfl（M57F の fibProj と同じ理由）。 -/
def sfProj (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) :
    Functor (splitFiberedFrobenioid U hU) (discCat Nat) where
  onObj := fun P => P.1
  onHom := fun f => ⟨f.base_eq⟩
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- **定理 (M59F-3c): 三角形の可換性（対象レベル）** —
    sfProj = fibProj ∘ sfForgetUnit が対象上で成立（定義的に rfl）。 -/
theorem sfProj_onObj_factor (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) (P : Nat × Nat) :
    (sfProj U hU).onObj P = fibProj.onObj ((sfForgetUnit U hU).onObj P) :=
  rfl

/-- **定理 (M59F-3d): 三角形の可換性（射レベル）** —
    sfProj = fibProj ∘ sfForgetUnit が射上で成立（定義的に rfl —
    単数を忘れてから base に射影しても、直接 base に射影しても同じ）。 -/
theorem sfProj_onHom_factor (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat} (f : SplitFibHom U P Q) :
    (sfProj U hU).onHom f = fibProj.onHom ((sfForgetUnit U hU).onHom f) :=
  rfl

/-- **系 (M59F-3e): 単数自己射の射影は恒等** — 射影関手は任意の自己射を
    base の恒等射に潰す（M57F-4c の split 版）。 -/
theorem sfProj_endo_id (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P : Nat × Nat} (f : SplitFibHom U P P) :
    (sfProj U hU).onHom f = (discCat Nat).id P.1 :=
  rfl

/-! ## M59F-4: 局所 split 圏とファイバーの同定（忠実充満）

    M55F の splitFrobenioid は対象 = 大域因子 QDiv なので、素点 k の
    ファイバー（対象 = 重複度 ℕ）とは型が合わない。ファイバーの正しい
    局所モデルは「一素点上の局所 Frobenioid（M57F の localFrobenioid）に
    単数を足した圏」であり、まずそれを建設してから包含の忠実充満を
    M57F-5 方式（往復写像の両向き恒等）で機械検証する。 -/

/-- **局所 split 射**: 一素点上で、重複度 m から m' への単数つき射
    (d ≥ 1, c : ℕ, u : U) with m' = d·m + c。M57F の LocalHom に
    M55F の単数成分を足したもの。 -/
structure LocalSplitHom (U : Grp) (m m' : Nat) where
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的因子部分。 -/
  c : Nat
  /-- 単数成分。 -/
  u : U.carrier
  d_pos : 1 ≤ d
  /-- 重複度の変換則: m' = d·m + c（u は関与しない）。 -/
  linear : m' = d * m + c

/-- 射の外延性: LocalSplitHom は (d, c, u) 成分で決まる（linear は
    Prop）。 -/
theorem LocalSplitHom.ext {U : Grp} {m m' : Nat}
    {f g : LocalSplitHom U m m'}
    (hd : f.d = g.d) (hc : f.c = g.c) (hu : f.u = g.u) : f = g := by
  cases f with | mk fd fc fu f1 f2 =>
  cases g with | mk gd gc gu g1 g2 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  have hu' : fu = gu := hu
  subst hd'
  subst hc'
  subst hu'
  rfl

/-- **定理 (M59F-4a): 局所 split Frobenioid** — 一素点上の重複度 ℕ を
    対象とし、射 = (d, c, u) とする圏。合成は全空間と同じ
    (d₁d₂, d₂c₁+c₂, u₁^{d₂}·u₂)。M57F の localFrobenioid の単数つき版
    = M55F の splitFrobenioid の局所版。 -/
def localSplitFrobenioid (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) : Cat where
  Obj := Nat
  Hom := LocalSplitHom U
  id := fun m => ⟨1, 0, U.one, Nat.le_refl 1, local_id_linear m⟩
  comp := fun f g =>
    ⟨f.d * g.d, g.d * f.c + g.c, U.mul (gpow U f.u g.d) g.u,
      Nat.mul_pos f.d_pos g.d_pos,
      local_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    LocalSplitHom.ext (Nat.one_mul f.d) (local_id_comp_c f.d f.c)
      (by show U.mul (gpow U U.one f.d) f.u = f.u
          rw [gpow_one_base, U.one_mul])
  comp_id := fun f =>
    LocalSplitHom.ext (Nat.mul_one f.d) (local_comp_id_c f.c)
      (by show U.mul (gpow U f.u 1) U.one = f.u
          rw [gpow_one, U.mul_one])
  assoc := fun f g h =>
    LocalSplitHom.ext (Nat.mul_assoc f.d g.d h.d)
      (local_assoc_c g.d h.d f.c g.c h.c)
      (by show U.mul (gpow U (U.mul (gpow U f.u g.d) g.u) h.d) h.u
            = U.mul (gpow U f.u (g.d * h.d))
                (U.mul (gpow U g.u h.d) h.u)
          rw [gpow_mul_dist U hU, ← gpow_mul, U.mul_assoc])

/-- **定理 (M59F-4b): ファイバーへの包含関手** — 素点 k を固定し、
    局所 split 圏を全空間の k 上のファイバー（対象 (k, m)）に埋め込む:
    m ↦ (k, m)、(d, c, u) ↦ (rfl, d, c, u)。関手性は両圏の合成則が
    同一の式であることから外延性で即座（M57F-5a の split 版）。 -/
def sfFiberIncl (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) (k : Nat) :
    Functor (localSplitFrobenioid U hU) (splitFiberedFrobenioid U hU) where
  onObj := fun m => (k, m)
  onHom := fun f => ⟨rfl, f.d, f.c, f.u, f.d_pos, f.linear⟩
  map_id := fun _ => SplitFibHom.ext rfl rfl rfl
  map_comp := fun _ _ => SplitFibHom.ext rfl rfl rfl

/-- ファイバーの射から局所 split 射への読み出し（onHom の逆写像）。
    (k, m) → (k, m') の射の base_eq は k = k なので捨ててよく、
    (d, c, u) がそのまま局所射になる。 -/
def sfFiberRestrictHom (U : Grp) (k : Nat) {m m' : Nat}
    (g : SplitFibHom U (k, m) (k, m')) : LocalSplitHom U m m' :=
  ⟨g.d, g.c, g.u, g.d_pos, g.linear⟩

/-- 往復 (局所射 → ファイバー射 → 局所射) は恒等（忠実性の片割れ）。 -/
theorem sf_fiber_incl_faithful (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (k : Nat) {m m' : Nat} (f : LocalSplitHom U m m') :
    sfFiberRestrictHom U k ((sfFiberIncl U hU k).onHom f) = f :=
  LocalSplitHom.ext rfl rfl rfl

/-- 往復 (ファイバー射 → 局所射 → ファイバー射) は恒等（充満性の片割れ。
    base_eq の不一致は proof irrelevance が吸収）。 -/
theorem sf_fiber_incl_full (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (k : Nat) {m m' : Nat} (g : SplitFibHom U (k, m) (k, m')) :
    (sfFiberIncl U hU k).onHom (sfFiberRestrictHom U k g) = g :=
  SplitFibHom.ext rfl rfl rfl

/-- **定理 (M59F-4c): ファイバー = 局所 split Frobenioid（忠実充満）** —
    包含関手の onHom は全単射（往復写像 sfFiberRestrictHom との両向き
    恒等を明示的に検証）。素点 k のファイバーが局所 split 圏の忠実な
    コピーであること: [FrdI] の「各 base 対象の上に分裂 Φ ⊕ O^× を持つ
    因子モノイドの圏が乗る」構造の離散 base での機械検証
    （M57F-5b の split 版）。 -/
theorem sf_fiber_local_iso (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (k m m' : Nat) :
    (∀ f : LocalSplitHom U m m',
        sfFiberRestrictHom U k ((sfFiberIncl U hU k).onHom f) = f)
      ∧ (∀ g : SplitFibHom U (k, m) (k, m'),
          (sfFiberIncl U hU k).onHom (sfFiberRestrictHom U k g) = g) :=
  ⟨fun f => sf_fiber_incl_faithful U hU k f,
    fun g => sf_fiber_incl_full U hU k g⟩

/-! ## M59F-5: 剛性と単数トーソルの両立

    M55F-5/6（base 一点）と M57F-8（単数なし）の合成: 全部入りの圏でも
    base・因子簿記は剛的（gaunt）なまま、単数成分だけが U-トーソルとして
    自由に残る。 -/

/-- **定理 (M59F-5a): 同型の Frobenius 次数は 1** — hom·inv = id の
    d 成分読み出し d·d' = 1 と d, d' ≥ 1 から（M48F の
    `frob_mul_eq_one_left` を再利用。M55F-5a / M57F-8a の合成版）。 -/
theorem sf_iso_d_one (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i : CatIso (splitFiberedFrobenioid U hU) P Q) : i.hom.d = 1 :=
  frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos
    (congrArg (SplitFibHom.d) i.hom_inv)

/-- **定理 (M59F-5b): 同型の因子部分は 0** — hom·inv = id の c 成分
    読み出し d'·c + c' = 0 で、inv.d = 1 を先に確定させて 1 倍に潰せば
    線形になり omega が通る（var×var を作らない — M57F-8b 方式）。 -/
theorem sf_iso_c_zero (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i : CatIso (splitFiberedFrobenioid U hU) P Q) : i.hom.c = 0 := by
  have hdinv : i.inv.d = 1 :=
    frob_mul_eq_one_left i.inv.d_pos i.hom.d_pos
      (congrArg (SplitFibHom.d) i.inv_hom)
  have hc : i.inv.d * i.hom.c + i.inv.c = 0 :=
    congrArg (SplitFibHom.c) i.hom_inv
  rw [hdinv, Nat.one_mul] at hc
  omega

/-- **定理 (M59F-5c): 同型は対象を動かせない** — P ≅ Q ⟹ P = Q。
    素点成分は base_eq、重複度成分は (d, c) = (1, 0) を線形条件に代入
    （M57F-8c と同じ）。単数を足しても base・因子部分の剛性は
    そのまま生き残る。 -/
theorem sf_iso_objects_eq (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i : CatIso (splitFiberedFrobenioid U hU) P Q) : P = Q := by
  have hd : i.hom.d = 1 := sf_iso_d_one U hU i
  have hc : i.hom.c = 0 := sf_iso_c_zero U hU i
  have hl : Q.2 = i.hom.d * P.2 + i.hom.c := i.hom.linear
  rw [hd, hc, Nat.one_mul, Nat.add_zero] at hl
  have hb : P.1 = Q.1 := i.hom.base_eq
  cases P with | mk k m =>
  cases Q with | mk l m' =>
  have hb' : k = l := hb
  have hm : m' = m := hl
  subst hb'
  subst hm
  rfl

/-- **系 (M59F-5c'): splitFiberedFrobenioid は gaunt**（M53F-1 の述語）。
    離散 base・ファイバー構造・単数の全部入りでも対象は動かせない。 -/
theorem splitFiberedFrobenioid_gaunt (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) :
    IsGaunt (splitFiberedFrobenioid U hU) :=
  fun _ _ i => sf_iso_objects_eq U hU i

/-- 単数自己射 (rfl, 1, 0, u): base・因子簿記は恒等、単数だけ u。 -/
def sfUnitEndo (U : Grp) (P : Nat × Nat) (u : U.carrier) :
    SplitFibHom U P P :=
  ⟨rfl, 1, 0, u, Nat.le_refl 1, local_id_linear P.2⟩

/-- **定理 (M59F-5d): 単数は任意 — (rfl, 1, 0, u) は同型**
    （逆 = (rfl, 1, 0, u⁻¹)）。base・因子部分は (rfl, 1, 0) に固定される
    のに単数部分は U 全体を走れる: 不定性の在処が単数成分であることの
    構成的半分（M55F-5d のファイバー版）。 -/
def sfUnitIso (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (P : Nat × Nat) (u : U.carrier) :
    CatIso (splitFiberedFrobenioid U hU) P P where
  hom := sfUnitEndo U P u
  inv := sfUnitEndo U P (U.inv u)
  hom_inv :=
    SplitFibHom.ext (Nat.one_mul 1) (local_id_comp_c 1 0)
      (by show U.mul (gpow U u 1) (U.inv u) = U.one
          rw [gpow_one]
          exact U.mul_inv u)
  inv_hom :=
    SplitFibHom.ext (Nat.one_mul 1) (local_id_comp_c 1 0)
      (by show U.mul (gpow U (U.inv u) 1) u = U.one
          rw [gpow_one]
          exact U.inv_mul u)

/-- 同型から単数の読み出し（hom の u 成分）。 -/
def sfIsoToUnit (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i : CatIso (splitFiberedFrobenioid U hU) P Q) : U.carrier :=
  i.hom.u

/-- 往復 (unit → iso → unit) は恒等。 -/
theorem sf_unit_iso_unit (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (P : Nat × Nat) (u : U.carrier) :
    sfIsoToUnit U hU (sfUnitIso U hU P u) = u :=
  rfl

/-- 往復 (iso → unit → iso) は恒等: 同型の d・c 成分は (1, 0) に固定
    （M59F-5a/5b）、base_eq は proof irrelevance なので、u 成分の一致
    だけで hom が一致し、逆成分は M22-1a `CatIso.ext` で従う。 -/
theorem sf_iso_unit_iso (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P : Nat × Nat}
    (i : CatIso (splitFiberedFrobenioid U hU) P P) :
    sfUnitIso U hU P (sfIsoToUnit U hU i) = i :=
  CatIso.ext
    (SplitFibHom.ext (sf_iso_d_one U hU i).symm
      (sf_iso_c_zero U hU i).symm rfl)

/-- **定理 (M59F-5e): splitFiberedFrobenioid の poly-isomorphism は
    U-トーソル** — 各対象の自己同型全体は U.carrier と明示的全単射
    （往復写像が両向きとも恒等、M55F-6 方式）。base が剛化され
    （gaunt なので同型は自己同型しかない）、因子部分が (1, 0) に
    剛化された後に残る自由度がちょうど U 全体: **(Ind2) 型不定性の在処**が
    ファイバー構造を足しても単数成分のままであることの機械検証。 -/
theorem sf_polyiso_torsor (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (P : Nat × Nat) :
    (∀ i : CatIso (splitFiberedFrobenioid U hU) P P,
        sfUnitIso U hU P (sfIsoToUnit U hU i) = i)
      ∧ (∀ u : U.carrier, sfIsoToUnit U hU (sfUnitIso U hU P u) = u) :=
  ⟨fun i => sf_iso_unit_iso U hU i, fun _ => rfl⟩

/-! ## M59F-6: 二分法の総括 — 全部入りでも不定性は単数成分にのみ宿る -/

/-- **定理 (M59F-6a): 忘却関手の像では同型は一意** — 任意の同型
    i, j : P ≅ Q の hom の忘却像（fiberedFrobenioid の射）は一致する
    （d・c 成分がどちらも (1, 0) に固定され、base_eq は proof
    irrelevance だから）。base + 因子簿記レベルでは「貼り方の選択肢」が
    存在しない（M55F-7b のファイバー版）。 -/
theorem sf_forget_iso_unique (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i j : CatIso (splitFiberedFrobenioid U hU) P Q) :
    (sfForgetUnit U hU).onHom i.hom = (sfForgetUnit U hU).onHom j.hom :=
  FibHom.ext
    ((sf_iso_d_one U hU i).trans (sf_iso_d_one U hU j).symm)
    ((sf_iso_c_zero U hU i).trans (sf_iso_c_zero U hU j).symm)

/-- **系 (M59F-6a'): CatIso ごと忘却しても一意** — 同型の mapIso 像は
    fiberedFrobenioid の剛性（M57F-8d'）により完全に一致する。 -/
theorem sf_forget_mapIso_eq (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {P Q : Nat × Nat}
    (i j : CatIso (splitFiberedFrobenioid U hU) P Q) :
    Functor.mapIso (sfForgetUnit U hU) i
      = Functor.mapIso (sfForgetUnit U hU) j :=
  fibered_rigid _ _

/-- **定理 (M59F-6b): U 非自明なら splitFiberedFrobenioid は剛的でない**
    — 単位元以外の単数 u があれば (rfl,1,0,u) と (rfl,1,0,1) が異なる
    自己同型になる（fiberedFrobenioid は IsoUnique だった——単数を足した
    瞬間に剛性が壊れる。M55F-7a のファイバー版）。 -/
theorem sf_not_iso_unique (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (h : ∃ u : U.carrier, u ≠ U.one) :
    ¬ IsoUnique (splitFiberedFrobenioid U hU) := by
  intro hiso
  obtain ⟨u, hu⟩ := h
  exact hu (congrArg SplitFibHom.u
    (hiso (0, 0) (0, 0) (sfUnitIso U hU (0, 0) u)
      (sfUnitIso U hU (0, 0) U.one)))

/-- **定理 (M59F-6c): 二分法の総括** — 離散 base・ファイバー構造・
    単数を全部入れた一つの圏 splitFiberedFrobenioid の中で:
    (1) 任意の二つの同型は忘却像（base + 因子簿記）が一致する =
        base・因子部分は剛的で不定性ゼロ、
    (2) U 非自明なら hom が異なる自己同型の対が実在する = 不定性は
        実在し、(1) と合わせてそれは**単数成分にのみ**宿る。
    M55F-7c（base 一点）の最終形: [FrdI] の射データ四つ組
    （base の射, deg_Fr, Div, 単数）を全て備えた離散モデルでも
    (Ind2) 型不定性の在処は単数部分に分離されたまま、という
    M53F→M55F→M57F の系譜の総括。 -/
theorem sf_dichotomy (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (h : ∃ u : U.carrier, u ≠ U.one) :
    (∀ (P Q : Nat × Nat)
        (i j : CatIso (splitFiberedFrobenioid U hU) P Q),
        (sfForgetUnit U hU).onHom i.hom
          = (sfForgetUnit U hU).onHom j.hom)
      ∧ (∃ (P : Nat × Nat)
          (i j : CatIso (splitFiberedFrobenioid U hU) P P),
          i.hom ≠ j.hom) := by
  constructor
  · exact fun P Q i j => sf_forget_iso_unique U hU i j
  · obtain ⟨u, hu⟩ := h
    exact ⟨(0, 0), sfUnitIso U hU (0, 0) u, sfUnitIso U hU (0, 0) U.one,
      fun heq => hu (congrArg SplitFibHom.u heq)⟩

end IUT
