/-
  # M245F: G-Set コエコライザによる hquot のモデル discharge（柱A A-3α ③）

  M234F `IUT/GaloisFullnessConnected.lean` は、一般連結対象 X 上の充満性を
  **軌道生成（無条件）+ deck 不変性の自動導出**まで詰め、残る外部入力を
  **hquot（商の普遍性 = コエコライザ: p の deck 変換で不変な v : B → Y は
  F-epi p : B → X を経由して降りる）一点**に純化した。M234F の正直な限定 (2)
  は「hquot を discharge した無条件モデル例は自明群・一点対象・p = id に
  留まる」であった。本モジュールはこの限定を**具体 G-Set モデルで前進**
  させる。

  核心は「hquot = コエコライザ普遍性」が G-Set 圏では**deck 群の軌道による
  商写像**として明示構成できることである。ただし deck 不変な v が p を
  経由するには、v が p のファイバー上定値である必要があり、deck 不変性が
  それを保証するのは **deck 群が p の各ファイバーに推移的に作用する**とき
  （= p が正規/ガロア被覆）に限る。この「ファイバー推移性」を明示条件
  `hfib` として切り出し、それが成り立つ G-Set 対象クラスで hquot を
  discharge する。

  * M245F-1 `gsetHquot_of_fiberTransitive` — **本丸**: G-Set モデルで
    F-epi p : B → X（F-epi = 台写像の全射）と **ファイバー推移性 hfib**
    （p b = p b' なら b を b' へ運ぶ deck 変換 σ が存在: σ ; p = p ∧
    σ b = b'）を仮定すれば、hquot が成り立つ——deck 不変な v : B → Y は
    p を経由して降りる。降下射 u は F-epi の切断 ρ（choice で選ぶ）で
    u(x) := v(ρ x) と構成し、well-defined 性・同変性・p ; u = v の全てを
    hfib（ファイバー内の任意二点は deck で移り合う）+ deck 不変性で閉じる。
    これは M149F の G-Set コエコライザ普遍性（`gsetQuot_univ`）を、商対象を
    明示構成せずに X = B/Deck(p) の側から直接使った形である
  * M245F-2 `fiberTransitiveConnectedData_regTerminal` /
    `connectedFullnessData_regTerminal_exists` — **非自明モデル witness**:
    B = 正則作用 G_reg（= G/1、普遍被覆）・X = 一点対象（= G/G、終対象）・
    p = 終射という**極大の正規被覆 G/1 → G/G**（deck 群 = G 全体、
    ファイバー = B 全体という非自明ケース）で hfib を `regAction_galois`
    のガロア推移性から満たし、M234F の `ConnectedFullnessData` を
    **任意の群 G（非自明を含む）で構成**する。M234F の witness が自明群
    punitGrp・p = id に限られていたのに対し、**任意 G の非自明な deck 群を
    持つ被覆**で hquot が discharge されることの実証
  * M245F-3 `connectedFullness_regTerminal_full` — 系: 任意の群 G・任意の
    対象 Y に対し、正則塔の比較関手は**一点対象 X 上で無条件に充満**
    （M234F-3 の充満性がこのモデル対象クラスで hquot 仮定を外せる）

  **discharge できたスライス（正直な到達点）**:
  hquot は **G-Set モデルの「ファイバー推移的（正規/ガロア）被覆」対象
  クラスで無条件に成立する**（M245F-1）。とくに極大正規被覆
  G_reg → 一点（deck 群 = G 全体・ファイバー非自明）という**非自明ケース**
  で hquot が discharge され、M234F の一般連結 X 上充満性がこのクラスで
  hquot 仮定なしに従う（M245F-2/3）。M234F の witness（自明群・p = id）
  から実質前進した。

  **正直な限定**:
  (1) hquot が discharge できるのは **hfib（deck 群のファイバー推移性 =
      p が正規/ガロア被覆）を満たす G-Set 被覆**に限る。一般の F-epi
      p : B → X（H ⊴ K でない剰余 G/H → G/K の非正規被覆）では、deck 不変な
      v が p を経由する保証がなく hquot は一般には成り立たない（deck 軌道 ⊊
      p のファイバー）。すなわち本モジュールが discharge するのは「一般 X」
      ではなく「**正規被覆で支配される X**」のクラスである
  (2) 具体 witness M245F-2 は極大ケース（X = 一点）に留める。中間の正規
      被覆 G/H → G/K（H ⊴ K ⊊ G）での witness 構成は剰余類対象の deck 群
      計算を要し範囲外（骨格は M245F-1 が既に一般 hfib で覆う）
  (3) F-epi の切断 ρ の構成に **Classical.choice を能動使用**する
      （② 承認済み・ヘッダ明記）。M234F 本体が choice 新規使用ゼロで
      あったのに対し、本モジュールの降下射構成は choice を使う
      （G-Set の任意ファイバーからの代表元選択のため。M22-8 の降下射
      構成が choice を要したのと同根）

  想定公理フットプリント: [propext, Classical.choice, Quot.sound]
  （Classical.choice は切断 ρ の構成と型が言及する gsetGaloisData の
  G6 の両方から。Quot.sound は colim/商操作から継承）。
  サブエージェント並行部品（tier M / opus）。
-/
import IUT.GaloisFullnessConnected
import IUT.SGA1Completion

namespace IUT

/-! ## M245F-1: ファイバー推移性からの hquot の discharge -/

/-- **本丸（M245F-1）: G-Set モデルで hquot をファイバー推移性から
    discharge** — F-epi p : B → X（台写像が全射 hp）と、p の各ファイバーに
    deck 群が推移的に作用する条件 hfib（p b = p b' を満たす b, b' は
    deck 変換 σ で移り合う: σ ; p = p ∧ σ b = b'）を仮定すれば、
    deck 不変な同変写像 v : B → Y（∀ deck σ, σ ; v = v）は p を経由して
    降りる: ∃ u : X → Y, p ; u = v。

    降下射 u は F-epi の切断 ρ x := choose(hp x)（p(ρ x) = x）を選び
    u(x) := v(ρ x) と定める。
    * well-defined + p ; u = v: ρ(p b) と b は同じファイバー ⟹ hfib で
      deck σ が σ(ρ(p b)) = b、deck 不変性で v(ρ(p b)) = v(b)。
    * 同変性: ρ(g·x) と g·ρx は同じファイバー（p 同変） ⟹ hfib + deck
      不変性で v(ρ(g·x)) = v(g·ρx) = g·v(ρx)（v 同変）。
    Classical.choice を切断 ρ の構成に能動使用（正直な限定 (3)）。 -/
theorem gsetHquot_of_fiberTransitive {G : Grp}
    (B X Y : GAction G) (p : ActHom B X)
    (hp : ∀ y : X.carrier, ∃ w : B.carrier, p.map w = y)
    (hfib : ∀ b b' : B.carrier, p.map b = p.map b' →
      ∃ σ : CatIso (GSetCat G) B B,
        ActHom.comp σ.hom p = p ∧ σ.hom.map b = b')
    (v : ActHom B Y)
    (hinv : ∀ σ : CatIso (GSetCat G) B B,
      ActHom.comp σ.hom p = p → ActHom.comp σ.hom v = v) :
    ∃ u : ActHom X Y, ActHom.comp p u = v := by
  have hρ : ∀ z : X.carrier, p.map (Classical.choose (hp z)) = z :=
    fun z => Classical.choose_spec (hp z)
  refine ⟨⟨fun x => v.map (Classical.choose (hp x)), ?_⟩, ?_⟩
  · -- 同変性
    intro g x
    show v.map (Classical.choose (hp (X.act g x)))
        = Y.act g (v.map (Classical.choose (hp x)))
    have e1 : Y.act g (v.map (Classical.choose (hp x)))
        = v.map (B.act g (Classical.choose (hp x))) :=
      (v.equivariant g (Classical.choose (hp x))).symm
    have hcond : p.map (B.act g (Classical.choose (hp x)))
        = p.map (Classical.choose (hp (X.act g x))) := by
      rw [p.equivariant, hρ x, hρ (X.act g x)]
    obtain ⟨σ, hσp, hσb⟩ := hfib (B.act g (Classical.choose (hp x)))
      (Classical.choose (hp (X.act g x))) hcond
    have hpt := congrFun (congrArg ActHom.map (hinv σ hσp))
      (B.act g (Classical.choose (hp x)))
    rw [e1, ← hσb]
    exact hpt
  · -- p ; u = v
    apply ActHom.ext
    intro b
    show v.map (Classical.choose (hp (p.map b))) = v.map b
    obtain ⟨σ, hσp, hσb⟩ := hfib (Classical.choose (hp (p.map b))) b (hρ (p.map b))
    have hpt : v.map (σ.hom.map (Classical.choose (hp (p.map b))))
        = v.map (Classical.choose (hp (p.map b))) :=
      congrFun (congrArg ActHom.map (hinv σ hσp)) (Classical.choose (hp (p.map b)))
    rw [hσb] at hpt
    exact hpt.symm

/-! ## M245F-2: 非自明モデル witness（極大正規被覆 G_reg → 一点） -/

/-- **非自明 witness（M245F-2a）: 極大正規被覆 G/1 → G/G での
    `ConnectedFullnessData`** — B = 正則作用 G_reg（普遍被覆）・
    X = 一点対象（終対象）・p = 終射。deck 群は G 全体・ファイバーは B 全体
    という非自明ケースで、hfib を `regAction_galois` のガロア推移性
    （任意二点は右移動の同型で移り合う）から満たし、M245F-1 で hquot を
    discharge する。**任意の群 G（非自明を含む）で構成される**——M234F の
    witness が自明群 punitGrp・p = id に限られていたのに対する前進。 -/
def fiberTransitiveConnectedData_regTerminal (G : Grp) :
    ConnectedFullnessData (gsetGaloisData G) where
  B := regAction G
  b₀ := G.one
  hB := regAction_galois G
  X := unitAction G
  p := (gsetGaloisData G).toT (regAction G)
  fepi := fun _ => ⟨G.one, rfl⟩
  quotient := fun Y v hinv =>
    gsetHquot_of_fiberTransitive (regAction G) (unitAction G) Y
      ((gsetGaloisData G).toT (regAction G))
      (fun _ => ⟨G.one, rfl⟩)
      (fun b b' _ => by
        obtain ⟨σ, hσ⟩ :=
          (gsetGaloisData G).galois_trans_iso (regAction_galois G) b b'
        exact ⟨σ, ActHom.ext (fun _ => rfl), hσ⟩)
      v hinv

/-- **系（M245F-2b）: 非自明 `ConnectedFullnessData` の存在** — 任意の
    群 G に対し、正規被覆 G_reg → 一点で hquot を discharge した充満性
    データが存在する（M234F の無矛盾性 witness を任意群・非自明 deck 群へ
    拡張）。 -/
theorem connectedFullnessData_regTerminal_exists (G : Grp) :
    Nonempty (ConnectedFullnessData (gsetGaloisData G)) :=
  ⟨fiberTransitiveConnectedData_regTerminal G⟩

/-! ## M245F-3: 系 — 一点対象上の無条件充満性 -/

/-- **系（M245F-3, capstone）: 一点対象上の無条件充満性（モデル）** —
    任意の群 G・任意の対象 Y に対し、正則塔（B = G_reg）の比較関手は
    **一点対象 X 上で無条件に充満**である: 任意の π₁-同変写像 φ は C 射
    u : X → Y の後合成である。M234F-3 の一般連結 X 上充満性が、この
    正規被覆モデル対象クラスで hquot 仮定を外して成立することの実証。 -/
theorem connectedFullness_regTerminal_full (G : Grp) (Y : GAction G)
    (φ : ActHom
      (GaloisTower.colimHomAction
        (constGaloisTower (gsetGaloisData G) (regAction G) G.one
          (regAction_galois G)) (unitAction G))
      (GaloisTower.colimHomAction
        (constGaloisTower (gsetGaloisData G) (regAction G) G.one
          (regAction_galois G)) Y)) :
    ∃ u : ActHom (unitAction G) Y,
      (constGaloisTower (gsetGaloisData G) (regAction G) G.one
        (regAction_galois G)).towerComparison.onHom u = φ :=
  (fiberTransitiveConnectedData_regTerminal G).full Y φ

end IUT
