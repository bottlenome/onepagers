/-
  # M250F: 中間正規被覆 G/core(H) → G/H の非自明 witness（柱A A-3α ③）

  M245F `IUT/GSetCoequalizer.lean` は hquot（商の普遍性 = コエコライザ）を
  G-Set モデルで discharge する本丸 `gsetHquot_of_fiberTransitive`（一般
  ファイバー推移性 hfib で成立）と、その非自明 witness を**極大正規被覆**
  G_reg → 一点（deck 群 = G 全体・ファイバー = B 全体）で構成した。だが
  M245F の正直な限定 (2) には「**中間の正規被覆 G/H → G/K（H ⊴ K ⊊ G）
  での witness 構成は剰余類対象の deck 群計算を要し範囲外**」と明記されて
  いた。本モジュールはこの限定を **1 スライス前進**させる。

  すなわち、任意の部分群 H に対する**中間正規被覆**
  p : G/core(H) → G/H を具体 G-Set 対象として実現し、その hfib を
  剰余類 deck 群（= H/core(H) の右移動）で満たして
  `ConnectedFullnessData` を構成する。極大ケース（deck 群 = G 全体）で
  も自明ケース（deck 群 = 自明）でもない**真に中間の deck 群**をもつ
  被覆で hquot を discharge した点が M245F からの前進である。

  核心（剰余類 deck 群の計算）:
  * B = G/core(H)（core(H) ⊴ G ゆえ M154F でガロア）・X = G/H・
    p = coreDominates（M148F-4b の支配全射 [g]_core ↦ [g]_H）。
  * p のファイバー推移性 hfib: p b = p b'（= [a]_H = [a']_H = a⁻¹a' ∈ H）
    なら、**右移動 c := a⁻¹a' ∈ H による deck 変換** coreRightMul（M148F-7b、
    正規性ゆえ剰余類空間に降りる）が b = [a]_core を b' = [a']_core に
    運び、かつ p を保つ（[g·c]_H = [g]_H が c ∈ H から従う）。この
    「deck 群 = H/core(H) の右移動」の明示計算が M245F の未実装スライス。

  * M250F-1 `coreDeckIso` — 右移動 coreRightMul を `GSetCat G` の同型射
    （CatIso）に包む（逆 = c⁻¹ の右移動、M148F-7c/d）。
  * M250F-2 `intermediateNormalCover_hfib` — **本丸**: p = coreDominates の
    ファイバー推移性。p b = p b' から H.mem(a⁻¹a') を剰余類の分離性で
    取り出し、c := a⁻¹a' の右移動 deck が hfib の両条件（p 保存・b ↦ b'）を
    満たす。
  * M250F-3 `intermediateNormalConnectedData` /
    `intermediateNormalConnectedData_exists` — **非自明 witness**:
    M250F-2 の hfib を `gsetHquot_of_fiberTransitive`（M245F-1）に食わせ、
    中間正規被覆 G/core(H) → G/H で `ConnectedFullnessData`（M234F-4a）を
    構成。deck 群は H/core(H)（H ≠ core(H) なら非自明、H ≠ G なら G 未満の
    真に中間の群）。
  * M250F-4 `connectedFullness_coreCover_full` — 系（capstone）: 任意の
    群 G・部分群 H・対象 Y に対し、G/core(H) 上定値塔の比較関手は
    **中間被支配対象 G/H 上で無条件に充満**（M234F-3 の充満性がこの中間
    正規被覆モデルで hquot 仮定を外せる）。

  **前進したスライス（正直な到達点）**:
  M245F が hquot の非自明 witness を**極大**正規被覆（G_reg → 一点、
  deck 群 = 全 G）に限っていたのに対し、本モジュールは**中間**正規被覆
  G/core(H) → G/H（deck 群 = H/core(H)、真に中間）で hquot を discharge
  した。M245F の限定 (2) が明示していた「中間正規被覆 G/H → G/K での
  witness（剰余類 deck 群計算）」を coreRightMul で具体的に閉じた。

  **正直な限定**:
  (1) 中間被覆の下側は G/H（一般の H）だが、上側（普遍被覆側）は
      **正規化 G/core(H)**（H そのものが正規でない場合は core(H) を取る
      必要がある）。すなわち被覆 G/H₀ → G/H で H₀ = core(H) ⊴ G という
      「H の正規核による中間被覆」に限る。**任意の中間正規被覆
      G/H₀ → G/H（H₀ ⊴ G, H₀ ⊆ H が与えられた一般の H₀）**への一般化は、
      H₀ = core(H) 以外の正規部分群でも右移動 deck が降りることの追加
      計算を要し範囲外（ただし core(H) は最大の中間正規核なので、
      本 witness は中間正規被覆の**代表的**ケースである）。
  (2) deck 群のファイバー推移性 hfib しか使わないので、非正規（deck 軌道 ⊊
      p のファイバー）の中間被覆は依然 hquot が一般には成り立たない
      （M245F の限定 (1) と同根）。
  (3) 型が `gsetGaloisData`（M21-8 の G6 に Classical.choice）と
      `gsetHquot_of_fiberTransitive`（切断 ρ に choice 能動使用）に
      言及するため、公理リストに Classical.choice を継承する。本
      モジュールの**証明体での新規 choice 使用はゼロ**（deck の推移性は
      剰余類の代表元計算のみ、choice 不要）。想定:
      [propext, Classical.choice, Quot.sound]。

  choice は型経由の継承のみ（本証明体は choice 不使用）。
  サブエージェント並行部品（tier M / opus）。
-/
import IUT.GSetCoequalizer
import IUT.CosetGalois

namespace IUT

/-! ## M250F-1: 右移動 deck を CatIso に包む -/

/-- **同型 deck（M250F-1）**: 右移動 `coreRightMul G H c`（M148F-7b、
    core(H) の正規性ゆえ剰余類空間 G/core(H) に降りる）は
    `GSetCat G` の同型射。逆は c⁻¹ の右移動（M148F-7c/d の
    左逆・右逆をそのまま同型データに）。 -/
def coreDeckIso (G : Grp) (H : Subgroup G) (c : G.carrier) :
    CatIso (GSetCat G) (cosetGSet G (coreSubgroup G H))
      (cosetGSet G (coreSubgroup G H)) where
  hom := coreRightMul G H c
  inv := coreRightMul G H (G.inv c)
  hom_inv := ActHom.ext (fun x => coreRightMul_left_inv G H c x)
  inv_hom := ActHom.ext (fun x => coreRightMul_right_inv G H c x)

/-! ## M250F-2: 中間正規被覆 p = coreDominates のファイバー推移性 -/

/-- **本丸（M250F-2）: 中間正規被覆 G/core(H) → G/H のファイバー推移性** —
    p = coreDominates の同じファイバー上の二点 b = [a]_core, b' = [a']_core
    （p b = p b' すなわち [a]_H = [a']_H）は、右移動 deck
    coreRightMul c（c := a⁻¹a' ∈ H）で移り合う。
    * p 保存: [g·c]_H = [g]_H が c ∈ H（正確には c⁻¹ ∈ H）から従う。
    * b ↦ b': [a·c]_core = [a·a⁻¹·a']_core = [a']_core。
    H.mem(a⁻¹a') は p b = p b'（剰余類の等値）から分離性
    `quot_exact_of_equiv` で取り出す。deck 群 = H/core(H) の右移動という
    M245F 未実装の剰余類 deck 群計算。choice 新規使用ゼロ。 -/
theorem intermediateNormalCover_hfib (G : Grp) (H : Subgroup G) :
    ∀ b b' : (cosetGSet G (coreSubgroup G H)).carrier,
      (coreDominates G H).map b = (coreDominates G H).map b' →
      ∃ σ : CatIso (GSetCat G) (cosetGSet G (coreSubgroup G H))
              (cosetGSet G (coreSubgroup G H)),
        ActHom.comp σ.hom (coreDominates G H) = coreDominates G H ∧
        σ.hom.map b = b' := by
  intro b b'
  induction b using Quot.ind; rename_i a
  induction b' using Quot.ind; rename_i a'
  intro hbb'
  -- p b = p b' は [a]_H = [a']_H。分離性で a⁻¹a' ∈ H を取り出す
  have hmem : H.mem (G.mul (G.inv a) a') := by
    have h' : Quot.mk (cosetRel G H) a = Quot.mk (cosetRel G H) a' := hbb'
    exact quot_exact_of_equiv (cosetRel G H) (cosetRel_refl G H)
      (fun hab => cosetRel_symm G H hab)
      (fun hab hbc => cosetRel_trans G H hab hbc) h'
  refine ⟨coreDeckIso G H (G.mul (G.inv a) a'), ?_, ?_⟩
  · -- p 保存: comp (coreRightMul c) p = p
    apply ActHom.ext
    intro x
    induction x using Quot.ind; rename_i g
    show Quot.mk (cosetRel G H) (G.mul g (G.mul (G.inv a) a'))
      = Quot.mk (cosetRel G H) g
    apply Quot.sound
    show H.mem (G.mul (G.inv (G.mul g (G.mul (G.inv a) a'))) g)
    rw [G.inv_mul_rev, G.mul_assoc, G.inv_mul, G.mul_one]
    exact H.inv_mem hmem
  · -- b ↦ b': [a·(a⁻¹a')]_core = [a']_core
    show Quot.mk (cosetRel G (coreSubgroup G H))
        (G.mul a (G.mul (G.inv a) a'))
      = Quot.mk (cosetRel G (coreSubgroup G H)) a'
    rw [← G.mul_assoc, G.mul_inv, G.one_mul]

/-! ## M250F-3: 非自明 witness（中間正規被覆での ConnectedFullnessData） -/

/-- **非自明 witness（M250F-3a）: 中間正規被覆 G/core(H) → G/H での
    `ConnectedFullnessData`** — B = G/core(H)（M154F でガロア）・
    X = G/H・p = coreDominates。hfib（M250F-2）を
    `gsetHquot_of_fiberTransitive`（M245F-1）に食わせ hquot を discharge。
    deck 群は H/core(H) — 極大（= 全 G, M245F）でも自明でもない**真に
    中間**の deck 群。**任意の群 G・任意の部分群 H で構成される**。 -/
def intermediateNormalConnectedData (G : Grp) (H : Subgroup G) :
    ConnectedFullnessData (gsetGaloisData G) where
  B := cosetGSet G (coreSubgroup G H)
  b₀ := Quot.mk (cosetRel G (coreSubgroup G H)) G.one
  hB := cosetGSet_core_galois G H
  X := cosetGSet G H
  p := coreDominates G H
  fepi := coreToCoset_surjective G H
  quotient := fun Y v hinv =>
    gsetHquot_of_fiberTransitive (cosetGSet G (coreSubgroup G H))
      (cosetGSet G H) Y (coreDominates G H)
      (coreToCoset_surjective G H)
      (intermediateNormalCover_hfib G H)
      v hinv

/-- **系（M250F-3b）: 中間正規被覆での非自明 witness の存在** — 任意の
    群 G・部分群 H に対し、中間正規被覆 G/core(H) → G/H で hquot を
    discharge した充満性データが存在する（M245F の極大 witness を
    中間 deck 群 H/core(H) へ拡張）。 -/
theorem intermediateNormalConnectedData_exists (G : Grp) (H : Subgroup G) :
    Nonempty (ConnectedFullnessData (gsetGaloisData G)) :=
  ⟨intermediateNormalConnectedData G H⟩

/-! ## M250F-4: 系 — 中間被支配対象 G/H 上の無条件充満性 -/

/-- **系（M250F-4, capstone）: 中間被支配対象 G/H 上の無条件充満性
    （モデル）** — 任意の群 G・部分群 H・対象 Y に対し、G/core(H) 上
    定値塔の比較関手は**中間正規被覆の下側 G/H 上で無条件に充満**である:
    任意の π₁-同変写像 φ は C 射 u : G/H → Y の後合成である。M234F-3 の
    一般連結 X 上充満性が、この中間正規被覆モデル対象クラスで hquot 仮定を
    外して成立することの実証（M245F の極大ケース
    `connectedFullness_regTerminal_full` の中間版）。 -/
theorem connectedFullness_coreCover_full (G : Grp) (H : Subgroup G)
    (Y : GAction G)
    (φ : ActHom
      (GaloisTower.colimHomAction
        (constGaloisTower (gsetGaloisData G) (cosetGSet G (coreSubgroup G H))
          (Quot.mk (cosetRel G (coreSubgroup G H)) G.one)
          (cosetGSet_core_galois G H)) (cosetGSet G H))
      (GaloisTower.colimHomAction
        (constGaloisTower (gsetGaloisData G) (cosetGSet G (coreSubgroup G H))
          (Quot.mk (cosetRel G (coreSubgroup G H)) G.one)
          (cosetGSet_core_galois G H)) Y)) :
    ∃ u : ActHom (cosetGSet G H) Y,
      (constGaloisTower (gsetGaloisData G) (cosetGSet G (coreSubgroup G H))
        (Quot.mk (cosetRel G (coreSubgroup G H)) G.one)
        (cosetGSet_core_galois G H)).towerComparison.onHom u = φ :=
  (intermediateNormalConnectedData G H).full Y φ

end IUT
