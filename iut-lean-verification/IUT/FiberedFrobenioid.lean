/-
  IUT/FiberedFrobenioid.lean — M57F（base 圏上のファイバー構造:
  素点の離散 base 圏上の Frobenioid 全空間圏）の形式化

  ## 動機

  [FrdI] の Frobenioid は本来 **base 圏 D（数体なら素点の圏）上の
  ファイバー圏**である: 射は「base の射・Frobenius 次数・効果的因子」の
  データであり、各 base 対象（素点）の上に局所的な因子簿記の圏が乗る。
  ところが既存の形式化はすべて base 一点だった——M48F の
  `elementaryFrobenioid`（対象 = 次数 ℤ）、M51F の `divisorFrobenioid`
  （対象 = 大域有効因子 QDiv）、M55F の `splitFrobenioid`（単数つき）は
  いずれも dashboard で「base 圏（素点の圏）上のファイバー構造は未形式化」
  と正直に申告してきた。

  本モジュールはこの「未達」を **base が離散圏の範囲で**埋める:

  * 素点の base 圏 = 離散圏 `discCat Nat`（対象 = 素点の添字 k、
    射 = 等号の証明のみ。素点間の射（分解・惰性）は持たない）
  * 一つの素点上の**局所 Frobenioid** `localFrobenioid`
    （対象 = その素点での重複度 m : ℕ、射 = (d ≥ 1, c) with
    m' = d·m + c。M48F の elementaryFrobenioid の ℕ 版で、
    c ≥ 0 が型に内蔵される）
  * **全空間圏** `fiberedFrobenioid`（対象 = (素点 k, 重複度 m)、
    射 = (base_eq : k = l, d ≥ 1, c) with m' = d·m + c。base が
    離散なので射は垂直成分のみ）
  * **射影関手** `fibProj` : 全空間 → base、垂直性
    （射があれば素点一致、素点が違えば射は空）
  * **ファイバーと局所圏の同定** `fiberIncl` / `fiber_local_iso`
    （素点 k のファイバー ≅ localFrobenioid、忠実充満を往復写像の
    両向き恒等で機械検証）
  * **大域→局所の制限関手** `divRestrictFunctor` : M51F の
    divisorFrobenioid（大域因子）から各素点の局所圏への読み出し、
    および**局所決定性** `restrict_determines`（大域射は全素点での
    制限＋bound で決まる = 局所‐大域の束着）

  ## 検証する定理（全て sorry なし・選択公理なし）

  * M57F-1 `discCat` — 型 B 上の離散圏（Hom a b = PLift (a = b)、
    合成 = Eq.trans）。圏公理は proof irrelevance + 構造 eta で rfl
  * M57F-2 `LocalHom` / `localFrobenioid` / `localToElementary` —
    一素点上の局所 Frobenioid の圏公理（合成 (d₁d₂, d₂c₁+c₂)）と、
    ℤ への埋め込み関手（M48F の elementaryFrobenioid への接続。
    cast 補題 `local_cast_linear` で線形条件を輸送）
  * M57F-3 `FibHom` / `fiberedFrobenioid` — 全空間圏の圏公理完全証明
    （base_eq の合成 = Eq.trans、簿記成分は localFrobenioid と同じ
    捻れ半直積型。`FibHom.ext`: 射の等号は (d, c) 成分だけで決まる
    —— base_eq は Prop なので proof irrelevance で消える）
  * M57F-4 `fibProj` / `fib_hom_vertical` / `fibProj_endo_id` /
    `no_cross_prime_hom` — 射影関手の関手性と**垂直性**: 任意の射は
    素点を保ち（射が存在すれば k = l）、素点が異なれば射は存在しない。
    base 離散ゆえ全ての射が「ファイバー方向（垂直）」である
  * M57F-5 `fiberIncl` / `fiberRestrictHom` / `fiber_local_iso` —
    素点 k のファイバー（対象 (k, m)）への包含関手の関手性＋
    **忠実充満の機械検証**（onHom の全単射性を往復写像の両向き恒等で。
    [FrdI] の「各 base 対象上のファイバーが因子モノイドの圏」の離散版）
  * M57F-6 `divRestrictFunctor` — **大域→局所の制限関手**
    divisorFrobenioid → localFrobenioid（x ↦ x.mult k、
    (d, c) ↦ (d, c.mult k)。線形条件の保存は qadd/qfrob が点ごとの
    定義であることから congrArg 一発）。関手性の完全証明
  * M57F-7 `restrict_determines` / `restrict_determines_components` —
    **局所決定性（束着定理）**: 大域射 f g : x → y は、全ての素点での
    制限が一致し c の bound 表示が一致すれば等しい。大域簿記が局所簿記の
    束であることの射レベルの実体
  * M57F-8 `fibered_iso_d_one` / `fibered_iso_c_zero` /
    `fibered_iso_objects_eq` / `fiberedFrobenioid_gaunt` /
    `fibered_iso_unique` / `fibered_rigid` — **剛性の遺伝**: 全空間圏の
    同型は (d, c) = (1, 0) を強制し対象（素点・重複度とも）を動かせない
    （gaunt）。同型は一意（IsoUnique、M53F の語彙）—— ファイバー構造を
    足しても Frobenius-like 剛性（poly-isomorphism = 単集合）は保たれる

  ## 正直な申告（モデルと本物の差）

  * **base は離散圏**: 本物の base 圏（素点の圏、あるいは [FrdI] の
    connected anabelioid の圏）は素点間の射（素イデアルの分解・惰性・
    分岐、体の拡大に沿った押し出し）を持つが、ここでは対象 = 素点の
    添字 ℕ・射 = 恒等（等号証明）のみの離散圏である。よって全空間の
    射も垂直成分のみで、「base の射に沿った因子の輸送」は未形式化。
  * **アルキメデス素点・realification・分裂（単数成分）は本モジュールの
    範囲外**（単数は M55F の splitFrobenioid が base 一点で形式化済み。
    両者の合成 = 「離散 base 上の split ファイバー構造」は未形式化）。
  * **局所決定性の bound 仮定**: QDiv は有限サポートの上界 bound を
    **データとして**持つ（選択公理回避のための設計、M51F）ため、
    mult が全点一致でも bound 表示が違えば QDiv としては別の項である。
    `restrict_determines` が bound の一致を仮定に置くのはこの表示の
    自由度ゆえであり、隠していない（真の因子の同一性は mult のみで
    決まるべきだが、それには商型が必要になる）。
  * 既存 M19 の `restrictFunctor`（群作用の制限関手）と名前が衝突する
    ため、本モジュールの制限関手は `divRestrictFunctor` と命名した。
  * 選択公理・追加公理は不使用（全定理 propext/Quot.sound 以下）。
-/
import IUT.PolyIsomorphism

namespace IUT

/-! ## 自然数算術のヘルパー補題

    omega は var×var の積を読めない（規約3）ため、合成・結合の線形条件は
    束縛変数上の補題に切り出し、積項は rw（mul_add・mul_assoc・mul_comm）で
    処理する。M48F の frob_comp_linear / frob_assoc_c の ℕ 版。 -/

/-- 恒等射の線形条件: m = 1·m + 0。 -/
theorem local_id_linear (m : Nat) : m = 1 * m + 0 := by omega

/-- 合成射の線形条件: m₂ = a·m₁ + c₁ かつ m₃ = b·m₂ + c₂ なら
    m₃ = (ab)·m₁ + (b·c₁ + c₂)。捻れ半直積型の合成則の算術核（ℕ 版）。 -/
theorem local_comp_linear {a b m₁ m₂ m₃ c₁ c₂ : Nat}
    (h₁ : m₂ = a * m₁ + c₁) (h₂ : m₃ = b * m₂ + c₂) :
    m₃ = a * b * m₁ + (b * c₁ + c₂) := by
  rw [h₂, h₁, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm b a, Nat.add_assoc]

/-- 左単位則の因子部分: b·0 + y = y（係数が変数でも 0 倍は線形）。 -/
theorem local_id_comp_c (b y : Nat) : b * 0 + y = y := by omega

/-- 右単位則の因子部分: 1·x + 0 = x。 -/
theorem local_comp_id_c (x : Nat) : 1 * x + 0 = x := by omega

/-- 結合則の因子部分: c·(b·x + y) + z = (bc)·x + (c·y + z)。 -/
theorem local_assoc_c (b c x y z : Nat) :
    c * (b * x + y) + z = b * c * x + (c * y + z) := by
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm c b, Nat.add_assoc]

/-- 線形条件の ℤ への輸送: m' = d·m + c（ℕ）ならキャスト後も成立。
    localToElementary（M57F-2 補）の算術核。 -/
theorem local_cast_linear {d m m' c : Nat} (h : m' = d * m + c) :
    (m' : Int) = (d : Int) * (m : Int) + (c : Int) := by
  rw [h, Int.natCast_add, Int.natCast_mul]

/-! ## M57F-1: 素点の離散 base 圏 -/

/-- **定理 (M57F-1): 離散圏** — 型 B を対象とし、射を等号の証明
    （PLift で Type に持ち上げ）だけとする圏。合成 = Eq.trans。
    圏公理は proof irrelevance（Prop の証明の definitional な一意性）と
    構造 eta により rfl で閉じる。素点の base 圏は `discCat Nat`
    （k = k 番目の素数の添字。素点間の射は持たない = 離散）。 -/
def discCat (B : Type) : Cat where
  Obj := B
  Hom := fun a b => PLift (a = b)
  id := fun _ => ⟨rfl⟩
  comp := fun f g => ⟨f.down.trans g.down⟩
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-! ## M57F-2: 一つの素点上の局所 Frobenioid -/

/-- **局所 Frobenioid の射**: 一つの素点上で、重複度 m から m' への射は
    Frobenius 次数 d ≥ 1 と効果的因子部分 c : ℕ の対で、線形条件
    m' = d·m + c を満たすもの。M48F の `FrobHom`（対象 ℤ・c : ℤ ≥ 0）の
    ℕ 版で、効果性 c ≥ 0 が型に内蔵される。 -/
structure LocalHom (m m' : Nat) where
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的因子部分（その素点での重複度の増分）。 -/
  c : Nat
  d_pos : 1 ≤ d
  /-- 重複度の変換則: m' = d·m + c。 -/
  linear : m' = d * m + c

/-- 射の外延性: LocalHom は (d, c) 成分で決まる（linear は Prop）。 -/
theorem LocalHom.ext {m m' : Nat} {f g : LocalHom m m'}
    (hd : f.d = g.d) (hc : f.c = g.c) : f = g := by
  cases f with | mk fd fc f1 f2 =>
  cases g with | mk gd gc g1 g2 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  subst hd'
  subst hc'
  rfl

/-- **定理 (M57F-2): 局所 Frobenioid** — 一つの素点上の重複度 ℕ を
    対象とし、射 = (Frobenius 次数, 効果的因子) とする圏。
    合成は (d₁,c₁)·(d₂,c₂) = (d₁d₂, d₂c₁+c₂)（捻れ半直積型、
    M48F/M51F と同じ）。 -/
def localFrobenioid : Cat where
  Obj := Nat
  Hom := LocalHom
  id := fun m => ⟨1, 0, Nat.le_refl 1, local_id_linear m⟩
  comp := fun f g =>
    ⟨f.d * g.d, g.d * f.c + g.c,
      Nat.mul_pos f.d_pos g.d_pos,
      local_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    LocalHom.ext (Nat.one_mul f.d) (local_id_comp_c f.d f.c)
  comp_id := fun f =>
    LocalHom.ext (Nat.mul_one f.d) (local_comp_id_c f.c)
  assoc := fun f g h =>
    LocalHom.ext (Nat.mul_assoc f.d g.d h.d)
      (local_assoc_c g.d h.d f.c g.c h.c)

/-- **定理 (M57F-2 補): ℤ への埋め込み関手** — 局所 Frobenioid は
    M48F の elementaryFrobenioid（対象 ℤ）に忠実に埋まる
    （m ↦ (m : ℤ)、(d, c) ↦ (d, (c : ℤ))。c ≥ 0 はキャストの非負性）。
    「localFrobenioid = elementaryFrobenioid の ℕ 部分圏」の機械検証。 -/
def localToElementary : Functor localFrobenioid elementaryFrobenioid where
  onObj := fun (m : Nat) => (m : Int)
  onHom := fun f =>
    ⟨f.d, (f.c : Int), f.d_pos, Int.natCast_nonneg f.c,
      local_cast_linear f.linear⟩
  map_id := fun _ => FrobHom.ext rfl Int.natCast_zero
  map_comp := fun f g =>
    FrobHom.ext rfl
      (by show ((g.d * f.c + g.c : Nat) : Int)
            = (g.d : Int) * (f.c : Int) + (g.c : Int)
          rw [Int.natCast_add, Int.natCast_mul])

/-! ## M57F-3: 全空間圏 — 離散 base 上のファイバー構造 -/

/-- **全空間圏の射**: 対象 (k, m)（素点の添字 k, その素点での重複度 m）
    から (l, m') への射は、base 成分 = 素点の一致の証明 base_eq : k = l
    （base が離散圏なので base の射は等号のみ）と簿記成分 (d ≥ 1, c)
    with m' = d·m + c の組。[FrdI] の射データ（base の射, deg_Fr, Div）の
    離散 base 版。 -/
structure FibHom (P Q : Nat × Nat) where
  /-- base 成分: 素点の一致（離散 base 圏の射）。 -/
  base_eq : P.1 = Q.1
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的因子部分。 -/
  c : Nat
  d_pos : 1 ≤ d
  /-- 重複度の変換則: m' = d·m + c。 -/
  linear : Q.2 = d * P.2 + c

/-- 射の外延性: FibHom は (d, c) 成分で決まる（base_eq は Prop の証明
    なので proof irrelevance により自動で一致、linear も Prop）。 -/
theorem FibHom.ext {P Q : Nat × Nat} {f g : FibHom P Q}
    (hd : f.d = g.d) (hc : f.c = g.c) : f = g := by
  cases f with | mk fb fd fc f1 f2 =>
  cases g with | mk gb gd gc g1 g2 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  subst hd'
  subst hc'
  rfl

/-- **定理 (M57F-3): 全空間圏（離散 base 上の fibered Frobenioid）** —
    対象 = (素点の添字, 重複度)、射 = (base の等号, Frobenius 次数,
    効果的因子)。base 成分の合成は Eq.trans、簿記成分の合成は
    捻れ半直積型 (d₁d₂, d₂c₁+c₂)。圏公理の簿記成分は localFrobenioid と
    同じ補題、base 成分は proof irrelevance（FibHom.ext が吸収）。 -/
def fiberedFrobenioid : Cat where
  Obj := Nat × Nat
  Hom := FibHom
  id := fun P => ⟨rfl, 1, 0, Nat.le_refl 1, local_id_linear P.2⟩
  comp := fun f g =>
    ⟨f.base_eq.trans g.base_eq, f.d * g.d, g.d * f.c + g.c,
      Nat.mul_pos f.d_pos g.d_pos,
      local_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    FibHom.ext (Nat.one_mul f.d) (local_id_comp_c f.d f.c)
  comp_id := fun f =>
    FibHom.ext (Nat.mul_one f.d) (local_comp_id_c f.c)
  assoc := fun f g h =>
    FibHom.ext (Nat.mul_assoc f.d g.d h.d)
      (local_assoc_c g.d h.d f.c g.c h.c)

/-! ## M57F-4: 射影関手と垂直性 -/

/-- **定理 (M57F-4a): 射影関手** π : fiberedFrobenioid → discCat Nat —
    対象 (k, m) を素点 k に、射をその base 成分に送る。関手性は
    proof irrelevance により rfl（base の射は等号の証明だけだから）。
    [FrdI] の「Frobenioid から base 圏への構造射」の離散版。 -/
def fibProj : Functor fiberedFrobenioid (discCat Nat) where
  onObj := fun P => P.1
  onHom := fun f => ⟨f.base_eq⟩
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- **定理 (M57F-4b): 垂直性** — 全空間圏の任意の射は素点を保つ
    （射が存在すれば base 成分は一致。base が離散なので全ての射が
    「ファイバー方向（垂直）」である）。 -/
theorem fib_hom_vertical {P Q : Nat × Nat} (f : FibHom P Q) :
    P.1 = Q.1 :=
  f.base_eq

/-- **定理 (M57F-4c): 自己射の射影は恒等** — 射影関手は任意の自己射を
    base の恒等射に潰す（proof irrelevance により rfl）。 -/
theorem fibProj_endo_id {P : Nat × Nat} (f : FibHom P P) :
    fibProj.onHom f = (discCat Nat).id P.1 :=
  rfl

/-- **定理 (M57F-4d): 素点間に射はない** — 異なる素点の上の対象の間には
    （重複度がいくつであっても）射が存在しない。離散 base 上の
    ファイバー構造の「分離性」。 -/
theorem no_cross_prime_hom {k l m m' : Nat} (h : k ≠ l) :
    ¬ Nonempty (FibHom (k, m) (l, m')) :=
  fun ⟨f⟩ => h f.base_eq

/-! ## M57F-5: ファイバーと局所圏の同定（忠実充満） -/

/-- **定理 (M57F-5a): ファイバーへの包含関手** — 素点 k を固定し、
    局所 Frobenioid を全空間の k 上のファイバー（対象 (k, m)）に
    埋め込む: m ↦ (k, m)、(d, c) ↦ (rfl, d, c)。関手性は両圏の合成則が
    同一の式であることから外延性で即座。 -/
def fiberIncl (k : Nat) : Functor localFrobenioid fiberedFrobenioid where
  onObj := fun m => (k, m)
  onHom := fun f => ⟨rfl, f.d, f.c, f.d_pos, f.linear⟩
  map_id := fun _ => FibHom.ext rfl rfl
  map_comp := fun _ _ => FibHom.ext rfl rfl

/-- 包含関手は射影関手の上でファイバーに収まる（π ∘ incl_k = const k）。 -/
theorem fibProj_fiberIncl (k m : Nat) :
    fibProj.onObj ((fiberIncl k).onObj m) = k :=
  rfl

/-- ファイバーの射から局所射への読み出し（onHom の逆写像）。
    (k, m) → (k, m') の射の base_eq は k = k なので捨ててよく、
    簿記成分 (d, c) がそのまま局所射になる。 -/
def fiberRestrictHom (k : Nat) {m m' : Nat}
    (g : FibHom (k, m) (k, m')) : LocalHom m m' :=
  ⟨g.d, g.c, g.d_pos, g.linear⟩

/-- 往復 (局所射 → ファイバー射 → 局所射) は恒等（忠実性の片割れ）。 -/
theorem fiber_incl_faithful (k : Nat) {m m' : Nat} (f : LocalHom m m') :
    fiberRestrictHom k ((fiberIncl k).onHom f) = f :=
  LocalHom.ext rfl rfl

/-- 往復 (ファイバー射 → 局所射 → ファイバー射) は恒等（充満性の片割れ。
    base_eq の不一致は proof irrelevance が吸収）。 -/
theorem fiber_incl_full (k : Nat) {m m' : Nat}
    (g : FibHom (k, m) (k, m')) :
    (fiberIncl k).onHom (fiberRestrictHom k g) = g :=
  FibHom.ext rfl rfl

/-- **定理 (M57F-5b): ファイバー = 局所 Frobenioid（忠実充満）** —
    包含関手の onHom は全単射（往復写像 fiberRestrictHom との両向き恒等を
    明示的に検証）。素点 k のファイバーが局所 Frobenioid の忠実なコピーで
    あること、すなわち [FrdI] の「各 base 対象の上に因子モノイドの圏が
    乗る」構造の離散 base での機械検証。 -/
theorem fiber_local_iso (k m m' : Nat) :
    (∀ f : LocalHom m m',
        fiberRestrictHom k ((fiberIncl k).onHom f) = f)
      ∧ (∀ g : FibHom (k, m) (k, m'),
          (fiberIncl k).onHom (fiberRestrictHom k g) = g) :=
  ⟨fun f => fiber_incl_faithful k f, fun g => fiber_incl_full k g⟩

/-! ## M57F-6: 大域因子の局所制限 -/

/-- **定理 (M57F-6): 制限関手** divisorFrobenioid → localFrobenioid —
    素点 k を固定し、大域有効因子 x（M51F の QDiv）をその素点での重複度
    x.mult k に、大域射 (d, c) を (d, c.mult k) に送る。線形条件の保存は
    qadd・qfrob が**点ごとの定義**であることから congrArg（k 成分の
    読み出し）一発で従う。既存 M19 の restrictFunctor（群作用の制限）と
    名前が衝突するため divRestrictFunctor と命名（正直な申告参照）。 -/
def divRestrictFunctor (k : Nat) :
    Functor divisorFrobenioid localFrobenioid where
  onObj := fun x => x.mult k
  onHom := fun {x y} f =>
    { d := f.d
      c := f.c.mult k
      d_pos := f.d_pos
      linear := by
        -- y = qadd (qfrob f.d x) f.c の k 成分を読み出すと
        -- y.mult k = f.d * x.mult k + f.c.mult k（点ごとの定義から defeq）
        have h : y.mult k = (qadd (qfrob f.d x) f.c).mult k :=
          congrArg (fun z => QDiv.mult z k) f.linear
        exact h }
  map_id := fun _ => LocalHom.ext rfl rfl
  map_comp := fun _ _ => LocalHom.ext rfl rfl

/-! ## M57F-7: 局所決定性（束着定理） -/

/-- **定理 (M57F-7a): 局所決定性（成分版）** — 大域射 f g : x → y は、
    Frobenius 次数が一致し、全ての素点で因子部分の重複度が一致し、
    因子部分の bound 表示が一致すれば等しい。 -/
theorem restrict_determines_components {x y : QDiv} {f g : DivHom x y}
    (hd : f.d = g.d) (hc : ∀ k, f.c.mult k = g.c.mult k)
    (hb : f.c.bound = g.c.bound) : f = g :=
  DivHom.ext hd (QDiv.ext (funext hc) hb)

/-- **定理 (M57F-7b): 局所決定性（束着定理）** — 大域射 f g : x → y の
    全ての素点 k での制限（divRestrictFunctor k の像）が一致し、
    因子部分の bound 表示が一致すれば f = g。**大域簿記は局所簿記の束で
    決まる**ことの射レベルの実体（次数 d は任意の一点、例えば k = 0 の
    制限から回収できることに注意）。bound の一致を仮定に置くのは、
    QDiv がサポート上界を選択公理回避のため**データとして**持つ表示の
    自由度ゆえである（正直な申告参照）。 -/
theorem restrict_determines {x y : QDiv} {f g : DivHom x y}
    (h : ∀ k, (divRestrictFunctor k).onHom f
      = (divRestrictFunctor k).onHom g)
    (hb : f.c.bound = g.c.bound) : f = g :=
  restrict_determines_components
    (congrArg LocalHom.d (h 0))
    (fun k => congrArg LocalHom.c (h k))
    hb

/-! ## M57F-8: 剛性の遺伝 — 全空間圏も Frobenius-like に剛的

    M48F-4（次数レベル）・M51F-10（因子レベル）・M53F（剛性述語）の系譜:
    base 圏上のファイバー構造を足しても、同型は (d, c) = (1, 0) を強制され
    対象（素点も重複度も）を動かせない。poly-isomorphism は単集合のまま
    （Frobenius-like 剛性はファイバー構造に遺伝する）。 -/

/-- **定理 (M57F-8a): 同型の Frobenius 次数は 1** — hom·inv = id の
    d 成分読み出し d·d' = 1 と d, d' ≥ 1 から（M48F の
    `frob_mul_eq_one_left` は ℕ の補題なのでそのまま再利用できる）。 -/
theorem fibered_iso_d_one {P Q : Nat × Nat}
    (i : CatIso fiberedFrobenioid P Q) : i.hom.d = 1 :=
  frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos
    (congrArg FibHom.d i.hom_inv)

/-- **定理 (M57F-8b): 同型の因子部分は 0** — hom·inv = id の c 成分
    読み出し d'·c + c' = 0 で、inv.d = 1 を先に確定させて 1 倍に潰せば
    線形になり omega が通る（var×var を作らない、規約3）。 -/
theorem fibered_iso_c_zero {P Q : Nat × Nat}
    (i : CatIso fiberedFrobenioid P Q) : i.hom.c = 0 := by
  have hdinv : i.inv.d = 1 :=
    frob_mul_eq_one_left i.inv.d_pos i.hom.d_pos
      (congrArg FibHom.d i.inv_hom)
  have hc : i.inv.d * i.hom.c + i.inv.c = 0 :=
    congrArg FibHom.c i.hom_inv
  rw [hdinv, Nat.one_mul] at hc
  omega

/-- **定理 (M57F-8c): 同型は対象を動かせない** — P ≅ Q ⟹ P = Q。
    素点成分は base_eq、重複度成分は (d, c) = (1, 0) を線形条件に代入。
    base 圏上のファイバー構造を足しても剛性（M48F-4d・M51F-10）は
    遺伝する。 -/
theorem fibered_iso_objects_eq {P Q : Nat × Nat}
    (i : CatIso fiberedFrobenioid P Q) : P = Q := by
  have hd : i.hom.d = 1 := fibered_iso_d_one i
  have hc : i.hom.c = 0 := fibered_iso_c_zero i
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

/-- **系 (M57F-8c'): fiberedFrobenioid は gaunt**（M53F-1 の述語）。 -/
theorem fiberedFrobenioid_gaunt : IsGaunt fiberedFrobenioid :=
  fun _ _ i => fibered_iso_objects_eq i

/-- **定理 (M57F-8d): 同型の一意性（剛性）** — 任意の二対象間の同型は
    hom 成分が一意（(d, c) = (1, 0) に固定。base_eq は proof irrelevance
    で自動一致）。poly-isomorphism は単集合のまま: **Frobenius-like
    剛性はファイバー構造に遺伝する**（M53F-3d の全空間版）。 -/
theorem fibered_iso_unique : IsoUnique fiberedFrobenioid :=
  fun _ _ i j =>
    FibHom.ext ((fibered_iso_d_one i).trans (fibered_iso_d_one j).symm)
      ((fibered_iso_c_zero i).trans (fibered_iso_c_zero j).symm)

/-- **系 (M57F-8d'): CatIso 全体としての一意性**（M22-1a CatIso.ext
    経由、M53F-1 isoUnique_subsingleton の発動）。 -/
theorem fibered_rigid {P Q : Nat × Nat}
    (i j : CatIso fiberedFrobenioid P Q) : i = j :=
  isoUnique_subsingleton fibered_iso_unique i j

end IUT
