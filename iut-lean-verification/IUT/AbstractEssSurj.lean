/-
  # M161F: 抽象本質的全射性への一歩（柱A A-2・並行部品）

  M23 (SGA1Object) は商公理付き抽象 Galois 圏 `QuotientData` において
  「任意の剰余類作用 Aut(A)/H は比較関手 Hom(A,−) の像に実現される」
  （M23-4 `sga1_essentially_surjective`）を公理のみから導出した。
  しかし SGA1 の本質的全射性の本来の主張は「**任意の推移的
  Aut(A)-集合**が像に実現される」であり、M23 のドキュメントは
  「M16-5 と合成すれば」と述べるのみで、その合成自体は未形式化
  だった（A-2 の残余の入口）。本モジュールはこの合成を選択公理
  抜きで完結させる:

  * M161F-1 `ActHom.Bij` — 同変全単射性の述語（単射 + 全射）。
    リポジトリ各所で ∧ の生の形で流通していた語彙の一本化
  * M161F-2 `SpanIso` / `SpanIso.refl` / `SpanIso.symm` —
    **スパンによる同変同型**: 共通頂点 Z から両側へ同変全単射が
    伸びる形 X ← Z → Y。全単射から逆写像を取り出す操作
    （Classical.choice を要する）を避けて「X ≅ Y」を表す標準形
  * M161F-3 `spanPullback` / `spanPr₁` / `spanPr₂` /
    `SpanIso.trans` — スパンの合成: ファイバー積
    {(a,b) | g₁(a) = f₂(b)}（componentwise 作用）を頂点とする
    **明示構成**により SpanIso が推移的、よって（refl/symm と
    併せ）同値関係をなすことの証明。choice 不要
  * M161F-4 `QuotientData.abstract_ess_surj_transitive` —
    **主定理**: 抽象公理系 `QuotientData` の下、A ガロア・
    a₀ ∈ F(A) のとき、**任意の推移的 Aut(A)-集合 X**（基点付き）
    に対し対象 Xo（= Qt(A, Stab(x₀))）が存在して
    X ≅ Hom(A, Xo)（SpanIso、頂点 = Aut(A)/Stab(x₀)）。
    M16-4 `orbit_stabilizer`（軌道-安定化定理）と M23-4 の合成
  * M161F-5 `QuotientData.abstract_ess_surj_orbit` — 系: 任意の
    Aut(A)-集合の任意の点の軌道（= 連結成分）が比較関手の像に
    実現される（M16-3 `orbit_transitive` との合成）
  * M161F-6 `AbstractEssSurjData` / `abstractEssSurjWitness` /
    `abstractEssSurj_exists` — 総括データ・証人・存在定理

  **意義**: A-2（SGA1 抽象本質的全射性）のステートメントが
  「剰余類作用の実現」（M23-4）から「**推移的 Aut(A)-集合の実現**」
  （SGA1 V.4 の対象レベルの主張そのもの）に、抽象公理系の内部で
  格上げされた。G-Set モデル（M20-9/M23-5）には一切依存せず、
  `QuotientData`（G1–G6 + 降下 + 商）だけから従う。

  **正直な限定**: (1) 実現は `SpanIso`（スパン同型）の形で与える。
  直接の同変全単射 X → Hom(A, Xo) の**関数としての**構成は全単射の
  逆写像抽出を要し、抽象レベルでは Classical.choice なしに不可能な
  ため、choice-free の標準形であるスパンを採用した（両脚とも
  同変全単射なので数学的内容は X ≅ Hom(A, Xo) と同値）。
  (2) A-2 の残余のうち「ガロア対象の十分性」（任意の連結対象が
  ガロア対象に支配されることの抽象公理からの導出）と pro-表現対象
  そのものの構成、および非推移的（= 有限和）対象への拡張は本切片の
  範囲外のまま残る。(3) 本モジュールの全定理は D : QuotientData を
  仮定にとるパラメトリックな形であり、モデル固有の Classical.choice
  （M22-8 の gsetDescentData 等）は継承しない — 公理は
  propext / Quot.sound のみ（剰余類空間 Quot 由来）。本モジュールの
  証明自体の choice 使用はゼロ。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.SGA1Object

namespace IUT

universe u

/-! ## M161F-1: 同変全単射性の述語 -/

/-- **同変全単射性**（M161F-1）: 同変写像が台の上で単射かつ全射。 -/
def ActHom.Bij {G : Grp} {X Y : GAction G} (φ : ActHom X Y) : Prop :=
  (∀ p q, φ.map p = φ.map q → p = q) ∧ (∀ y, ∃ p, φ.map p = y)

/-! ## M161F-2: スパンによる同変同型 -/

/-- **スパン同型**（M161F-2a）: 共通頂点 Z から X, Y の両側へ
    同変全単射が伸びる。全単射の逆写像抽出（Classical.choice）を
    避けて同変同型 X ≅ Y を表す choice-free の標準形。 -/
def SpanIso {G : Grp} (X Y : GAction G) : Prop :=
  ∃ (Z : GAction G) (f : ActHom Z X) (g : ActHom Z Y), f.Bij ∧ g.Bij

/-- **反射律**（M161F-2b）: 恒等スパン X ← X → X。 -/
theorem SpanIso.refl {G : Grp} (X : GAction G) : SpanIso X X :=
  ⟨X, ActHom.idHom X, ActHom.idHom X,
   ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩,
   ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩⟩

/-- **対称律**（M161F-2c）: 脚の入れ替え。 -/
theorem SpanIso.symm {G : Grp} {X Y : GAction G}
    (h : SpanIso X Y) : SpanIso Y X := by
  obtain ⟨Z, f, g, hf, hg⟩ := h
  exact ⟨Z, g, f, hg, hf⟩

/-! ## M161F-3: スパンの合成（ファイバー積による明示構成） -/

/-- **スパンの合成頂点**（M161F-3a）: 同変写像 g₁ : W₁ → Y,
    f₂ : W₂ → Y の Y 上のファイバー積 {(a,b) | g₁(a) = f₂(b)}
    への componentwise 作用。choice 不要の明示構成。 -/
def spanPullback {G : Grp} {W₁ W₂ Y : GAction G}
    (g₁ : ActHom W₁ Y) (f₂ : ActHom W₂ Y) : GAction G where
  carrier := { p : W₁.carrier × W₂.carrier // g₁.map p.1 = f₂.map p.2 }
  act := fun σ p => ⟨(W₁.act σ p.val.1, W₂.act σ p.val.2), by
    show g₁.map (W₁.act σ p.val.1) = f₂.map (W₂.act σ p.val.2)
    rw [g₁.equivariant, f₂.equivariant, p.property]⟩
  act_one := fun p => Subtype.ext (by
    show (W₁.act G.one p.val.1, W₂.act G.one p.val.2) = p.val
    rw [W₁.act_one, W₂.act_one])
  act_mul := fun σ τ p => Subtype.ext (by
    show (W₁.act (G.mul σ τ) p.val.1, W₂.act (G.mul σ τ) p.val.2)
        = (W₁.act σ (W₁.act τ p.val.1), W₂.act σ (W₂.act τ p.val.2))
    rw [W₁.act_mul, W₂.act_mul])

/-- 第一射影（M161F-3b）: ファイバー積 → W₁ は同変。 -/
def spanPr₁ {G : Grp} {W₁ W₂ Y : GAction G}
    (g₁ : ActHom W₁ Y) (f₂ : ActHom W₂ Y) :
    ActHom (spanPullback g₁ f₂) W₁ :=
  ⟨fun p => p.val.1, fun _ _ => rfl⟩

/-- 第二射影（M161F-3c）: ファイバー積 → W₂ は同変。 -/
def spanPr₂ {G : Grp} {W₁ W₂ Y : GAction G}
    (g₁ : ActHom W₁ Y) (f₂ : ActHom W₂ Y) :
    ActHom (spanPullback g₁ f₂) W₂ :=
  ⟨fun p => p.val.2, fun _ _ => rfl⟩

/-- **定理（M161F-3d）: 推移律** — スパン X ← W₁ → Y と
    Y ← W₂ → Z はファイバー積 W₁ ×_Y W₂ を頂点とするスパン
    X ← W₁ ×_Y W₂ → Z に合成され、両脚の全単射性が保たれる。
    `SpanIso` は同値関係（refl/symm/trans）をなす。 -/
theorem SpanIso.trans {G : Grp} {X Y Z : GAction G}
    (h₁ : SpanIso X Y) (h₂ : SpanIso Y Z) : SpanIso X Z := by
  obtain ⟨W₁, f₁, g₁, hf₁, hg₁⟩ := h₁
  obtain ⟨W₂, f₂, g₂, hf₂, hg₂⟩ := h₂
  refine ⟨spanPullback g₁ f₂,
    ActHom.comp (spanPr₁ g₁ f₂) f₁,
    ActHom.comp (spanPr₂ g₁ f₂) g₂, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- 左脚の単射性: f₁ 単射で第一成分が一致、f₂ 単射で第二成分も一致
    intro p q h
    have h1 : p.val.1 = q.val.1 := hf₁.1 _ _ h
    have h2 : p.val.2 = q.val.2 := by
      apply hf₂.1
      rw [← p.property, ← q.property, h1]
    apply Subtype.ext
    show (p.val.1, p.val.2) = (q.val.1, q.val.2)
    rw [h1, h2]
  · -- 左脚の全射性: f₁ で a を取り、g₁(a) の f₂-原像 b と対にする
    intro x
    obtain ⟨a, ha⟩ := hf₁.2 x
    obtain ⟨b, hb⟩ := hf₂.2 (g₁.map a)
    exact ⟨⟨(a, b), hb.symm⟩, ha⟩
  · -- 右脚の単射性（対称の議論）
    intro p q h
    have h2 : p.val.2 = q.val.2 := hg₂.1 _ _ h
    have h1 : p.val.1 = q.val.1 := by
      apply hg₁.1
      rw [p.property, q.property, h2]
    apply Subtype.ext
    show (p.val.1, p.val.2) = (q.val.1, q.val.2)
    rw [h1, h2]
  · -- 右脚の全射性: g₂ で b を取り、f₂(b) の g₁-原像 a と対にする
    intro z
    obtain ⟨b, hb⟩ := hg₂.2 z
    obtain ⟨a, ha⟩ := hg₁.2 (f₂.map b)
    exact ⟨⟨(a, b), ha⟩, hb⟩

/-! ## M161F-4: 主定理 — 推移的 Aut(A)-集合の抽象的実現 -/

/-- **定理（M161F-4）: 抽象本質的全射性・推移的 Aut(A)-集合版** —
    商公理付き抽象 Galois 圏 `QuotientData` の下、A ガロア・
    a₀ ∈ F(A) のとき、**任意の**基点付き推移的 Aut(A)-集合 X に
    対し対象 Xo が存在して X は比較関手の値 Hom(A, Xo) と
    スパン同型（頂点 = 剰余類作用 Aut(A)/Stab(x₀)、左脚 =
    軌道-安定化定理 M16-4、右脚 = 剰余類実現 M23-4）。
    M23-4 の「剰余類作用の実現」が SGA1 の対象レベルの主張
    そのもの（推移的対象の実現）へ公理内部で格上げされる。 -/
theorem QuotientData.abstract_ess_surj_transitive (D : QuotientData.{u})
    {A : D.C.Obj} (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A)
    (X : GAction (D.toGaloisCatData.autGrp A))
    (hX : X.Transitive) (x₀ : X.carrier) :
    ∃ Xo : D.C.Obj, SpanIso X (D.toGaloisCatData.homGAction A Xo) := by
  obtain ⟨Xo, Φ, hΦinj, hΦsurj⟩ := D.sga1_essentially_surjective hA a₀
    (stabilizer (D.toGaloisCatData.autGrp A) X x₀)
  obtain ⟨φ, hφinj, hφsurj⟩ :=
    orbit_stabilizer (D.toGaloisCatData.autGrp A) X x₀ hX
  exact ⟨Xo,
    cosetAction (D.toGaloisCatData.autGrp A)
      (stabilizer (D.toGaloisCatData.autGrp A) X x₀),
    φ, Φ, ⟨hφinj, hφsurj⟩, ⟨hΦinj, hΦsurj⟩⟩

/-! ## M161F-5: 系 — 任意の Aut(A)-集合の軌道の実現 -/

/-- **系（M161F-5）: 軌道の実現** — 任意の Aut(A)-集合 X の任意の
    点 x₀ の軌道（= 連結成分、M16-3）は比較関手の像にスパン同型で
    実現される。「任意の有限 Aut(A)-集合は連結成分ごとに像に入る」
    の成分単位の形。 -/
theorem QuotientData.abstract_ess_surj_orbit (D : QuotientData.{u})
    {A : D.C.Obj} (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A)
    (X : GAction (D.toGaloisCatData.autGrp A)) (x₀ : X.carrier) :
    ∃ Xo : D.C.Obj,
      SpanIso (orbitOf X x₀) (D.toGaloisCatData.homGAction A Xo) :=
  D.abstract_ess_surj_transitive hA a₀ (orbitOf X x₀)
    (orbit_transitive X x₀) ⟨x₀, orbitRel_refl X x₀⟩

/-! ## M161F-6: 総括 -/

/-- **総括データ（M161F-6a）**: 抽象本質的全射性の証人 —
    ガロア対象 base・基点と、任意の基点付き推移的 Aut(base)-集合を
    比較関手の像にスパン同型で実現する対象の存在。 -/
structure AbstractEssSurjData (D : QuotientData.{u}) where
  /-- ガロア対象（被覆理論の「十分大きい被覆」）。 -/
  base : D.C.Obj
  /-- base は抽象 IsGalois を満たす。 -/
  galois : D.toGaloisCatData.IsGalois base
  /-- ファイバーの基点。 -/
  basept : D.F.onObj base
  /-- 実現: 任意の基点付き推移的 Aut(base)-集合はある対象の
      Hom(base, −) 値とスパン同型。 -/
  realize : ∀ X : GAction (D.toGaloisCatData.autGrp base),
    X.Transitive → X.carrier →
    ∃ Xo : D.C.Obj, SpanIso X (D.toGaloisCatData.homGAction base Xo)

/-- **証人（M161F-6b）**: ガロア対象と基点が与えられれば M161F-4 が
    総括データを与える。 -/
def abstractEssSurjWitness (D : QuotientData.{u}) {A : D.C.Obj}
    (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A) :
    AbstractEssSurjData D where
  base := A
  galois := hA
  basept := a₀
  realize := fun X hX x₀ => D.abstract_ess_surj_transitive hA a₀ X hX x₀

/-- **定理（M161F-6c）: 抽象本質的全射性データの存在**。 -/
theorem abstractEssSurj_exists (D : QuotientData.{u}) {A : D.C.Obj}
    (hA : D.toGaloisCatData.IsGalois A) (a₀ : D.F.onObj A) :
    Nonempty (AbstractEssSurjData D) :=
  ⟨abstractEssSurjWitness D hA a₀⟩

end IUT
