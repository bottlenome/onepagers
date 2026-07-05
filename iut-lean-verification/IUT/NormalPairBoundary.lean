/-
  # M255F: hquot/hfib の境界 — 正規性 ⟺ ファイバー推移性の特徴付け（柱A A-3α ③）

  M245F `IUT/GSetCoequalizer.lean` は hquot（商の普遍性 = コエコライザ）を
  G-Set モデルで discharge する本丸 `gsetHquot_of_fiberTransitive`（一般
  ファイバー推移性 hfib で成立）を確立し、正直な限定 (1) で
  「**非正規な G/H→G/K では deck 軌道 ⊊ ファイバーで hquot は一般に不成立**」
  と申告した。M250F `IUT/IntermediateNormalCover.lean` は中間正規被覆
  G/core(H) → G/H（core(H) ⊴ G）で hfib を満たしたが、これは上側
  H₀ = core(H) が **G 全体で正規**という強い条件に依存していた。

  本モジュールは③の境界を**精密に特徴付ける**（negative/boundary 結果も
  価値がある、という誠実な到達点）。被覆 p : G/H₀ → G/H（H₀ ⊆ H）に
  対して、**ファイバー推移性 hfib が成立する ⟺ H が H₀ を正規化する
  （= H₀ ⊴ H）** を両向きに閉じる:

  * M255F-1 `normalizesElt` / `normalizesSub` — 正規化の述語:
    元 c が H₀ を正規化（c⁻¹ H₀ c ⊆ H₀）／部分群 H が H₀ を正規化。
  * M255F-2 `cosetRel_right_of_normalizesElt` / `genRightMul` —
    **十分側の芯**: c が H₀ を正規化するなら右移動 [a] ↦ [ac] は剰余類
    空間 G/H₀ に降りる（M148F `coreRightMul` の core 非依存な一般化）。
  * M255F-3 `cosetRel_right_respects_iff_normalizesElt` — **単元境界の
    iff（本丸その1）**: 右移動 R_c が G/H₀ に well-defined に降りる
    **⟺ c が H₀ を正規化する**。「なぜ正規性が必要か」の数学的核心を
    ちょうど正規化群 N_G(H₀) として切り出した特徴付け。
  * M255F-4 `genRightMul_left_inv` / `genRightMul_right_inv` /
    `genRightMulIso` — R_c を `GSetCat G` の同型射（deck 変換）に包む
    （逆 = c⁻¹ の右移動、c ∈ H かつ H が H₀ を正規化するとき）。
  * M255F-5 `genDominates` / `genDominates_surjective` — 支配射
    p : G/H₀ → G/H（H₀ ⊆ H の剰余細分、F-epi = 全射）。
  * M255F-6 `normalPair_hfib` — **十分側（本丸その2）**: H₀ ⊆ H かつ
    H が H₀ を正規化するなら p = genDominates はファイバー推移的 hfib。
    右移動 deck が同ファイバー内の任意二点を移し合う（M250F を
    H₀ = core(H) から任意の H₀ ⊴ H へ一般化）。
  * M255F-7 `equivariantEndo_forces_normalizesElt` — **必要側の芯**:
    G/H₀ の同変自己写像 σ が [1] を [c] に送るなら c は H₀ を正規化する。
    σ の同変性 σ([n]) = n·σ([1]) と [n]=[1]（n ∈ H₀）から
    [nc] = [c] を導き、剰余類の分離性で c⁻¹ n c ∈ H₀ を取り出す。
    **deck が右移動に強制される**という被覆理論の一意性が正規性を強いる。
  * M255F-8 `normalPair_hfib_forces_normalizesSub` /
    `normalPair_hfib_iff_normalizesSub` — **必要側 + 境界の iff（本丸
    その3・capstone）**: hfib（p のファイバー推移性）**⟺** H が H₀ を
    正規化する（H₀ ⊴ H）。十分は M255F-6、必要は M255F-7（fiber over
    [1]_H の点 [c]（c ∈ H）へ deck σ を要求すると c ∈ N_G(H₀) が従う）。
  * M255F-9 `normalPair_hquot` — 系（capstone）: H₀ ⊴ H の正規対で
    hquot を discharge（`gsetHquot_of_fiberTransitive` に M255F-6 を
    食わせる）。deck 不変な v : G/H₀ → Y は p を経由して降りる。

  **特徴付けたスライス（正直な到達点）**:
  ③の境界を **hfib ⟺ H₀ ⊴ H（H が H₀ を正規化）** として**両向きに
  確定**した（M255F-8 iff）。十分（H₀ ⊴ H ⟹ hfib、M250F の core
  依存を除いた一般化、M255F-6）と必要（hfib ⟹ H₀ ⊴ H、M255F-7 の
  deck 一意性から、M255F-8）の双方を閉じた。M245F の限定 (1)
  「非正規では deck 軌道 ⊊ ファイバー」を、**非正規 ⟺ hfib 不成立**
  として厳密化した形である（必要方向の対偶: H₀ が H で非正規なら、
  [1]_H の上のある点へ deck が存在せず hfib が破れる）。

  **正直な限定**:
  (1) 特徴付けは**上側 H₀ の H での正規性**（H₀ ⊴ H = H ⊆ N_G(H₀)）で
      あり、G 全体での正規性ではない。H₀ ⊴ H だが H₀ ⋬ G のとき、
      G/H₀ は抽象 IsGalois にはならない（自己同型のファイバー全体への
      推移性には H₀ ⊴ G が必要）ため、本モジュールは
      `ConnectedFullnessData`（B のガロア性 hB を要求）を**構成しない**
      — 閉じたのは hfib/hquot レベルの境界であり、M250F/M245F の
      capstone（ガロア対象上の充満性）とは層が異なる。G/H₀ が
      ガロアになる H₀ ⊴ G の場合の充満性 capstone は M250F が既に覆う。
  (2) 必要方向（M255F-7）は**同変自己写像 σ の存在**から正規性を導く。
      これは hfib が要求する deck（同型 CatIso）より弱い前提（同変射
      だけ）で足りるため、境界の必要側はより強い形で閉じている
      （σ が同変射でさえあれば c ∈ N_G(H₀)）。具体有限群 S_3・
      H = S_3・H₀ = 位数2 部分群での反例（N_{S_3}(H₀) = H₀ ゆえ deck 群
      自明・3点ファイバーに非推移で hfib 破れ）は、S_3 の群公理を
      許可タクティク（decide 禁止）で機械検証する手間が範囲外のため、
      抽象的な必要方向 M255F-7/8 の対偶として一般に閉じるに留める。
  (3) 型が `gsetGaloisData`（M21-8 の G6 に Classical.choice）と
      `gsetHquot_of_fiberTransitive`（切断 ρ に choice 能動使用）に
      言及するため（M255F-9 のみ）、その宣言は公理リストに
      Classical.choice を継承する。本モジュールの**証明体での新規
      choice 使用はゼロ**（右移動 deck・正規化の抽出は剰余類の代表元
      計算のみ、choice 不要）。M255F-1〜8 は choice に言及しない
      ([propext, Quot.sound] 圏内)。想定: M255F-9 のみ
      [propext, Classical.choice, Quot.sound]。

  choice は M255F-9 の型経由の継承のみ（全証明体は choice 不使用）。
  サブエージェント並行部品（tier M / opus）。
-/
import IUT.GSetCoequalizer
import IUT.CosetGalois

namespace IUT

/-! ## M255F-1: 正規化の述語 -/

/-- **元による正規化（M255F-1a）**: c が部分群 H₀ を正規化する
    （共役 c⁻¹ H₀ c ⊆ H₀）。剰余類空間 G/H₀ に右移動 R_c が降りる
    ちょうどの条件（M255F-3 で iff を証明）。 -/
def normalizesElt (G : Grp) (H₀ : Subgroup G) (c : G.carrier) : Prop :=
  ∀ n, H₀.mem n → H₀.mem (G.mul (G.mul (G.inv c) n) c)

/-- **部分群による正規化（M255F-1b）**: H の全ての元が H₀ を正規化する
    （= H ⊆ N_G(H₀)、= H₀ ⊴ H）。 -/
def normalizesSub (G : Grp) (H H₀ : Subgroup G) : Prop :=
  ∀ c, H.mem c → normalizesElt G H₀ c

/-! ## M255F-2: 右移動が剰余類空間に降りる（十分側の芯） -/

/-- **補題 (M255F-2a): 正規化する元の右移動は剰余類同値を保つ** —
    c が H₀ を正規化するなら a ~ b（a⁻¹b ∈ H₀）から ac ~ bc
    （(ac)⁻¹(bc) = c⁻¹(a⁻¹b)c ∈ H₀）。M148F `cosetRel_right_core`
    （core 専用）を任意の正規化元へ一般化。 -/
theorem cosetRel_right_of_normalizesElt (G : Grp) (H₀ : Subgroup G)
    (c : G.carrier) (hc : normalizesElt G H₀ c)
    {a b : G.carrier} (h : cosetRel G H₀ a b) :
    cosetRel G H₀ (G.mul a c) (G.mul b c) := by
  have h' : H₀.mem (G.mul (G.inv a) b) := h
  have h1 := hc (G.mul (G.inv a) b) h'
  show H₀.mem (G.mul (G.inv (G.mul a c)) (G.mul b c))
  rw [G.inv_mul_rev, ← G.mul_assoc (G.mul (G.inv c) (G.inv a)) b c,
    G.mul_assoc (G.inv c) (G.inv a) b]
  exact h1

/-- **右移動 deck（M255F-2b）**: c が H₀ を正規化するとき、[a] ↦ [ac] は
    G/H₀ の同変自己写像（左作用と右移動は可換）。 -/
def genRightMul (G : Grp) (H₀ : Subgroup G) (c : G.carrier)
    (hc : normalizesElt G H₀ c) :
    ActHom (cosetAction G H₀) (cosetAction G H₀) where
  map := Quot.lift
    (fun a => Quot.mk (cosetRel G H₀) (G.mul a c))
    (fun _ _ hab => Quot.sound (cosetRel_right_of_normalizesElt G H₀ c hc hab))
  equivariant := by
    intro g x
    induction x using Quot.ind; rename_i a
    show Quot.mk (cosetRel G H₀) (G.mul (G.mul g a) c)
      = Quot.mk (cosetRel G H₀) (G.mul g (G.mul a c))
    rw [G.mul_assoc]

/-! ## M255F-3: 単元境界の iff（右移動 well-defined ⟺ 正規化） -/

/-- **本丸その1 (M255F-3): 右移動 R_c が G/H₀ に降りる ⟺ c が H₀ を
    正規化する** — 右移動が剰余類同値を保つ（well-defined 性）ことと、
    c ∈ N_G(H₀) が同値。逆向き（⟹）は a = 1, b = n（n ∈ H₀）を代入して
    (1·c)⁻¹(n·c) = c⁻¹ n c ∈ H₀ を読む。正順（⟸）は M255F-2a。
    「なぜ正規性が hquot に必要か」を正規化群として正確に切り出した
    境界特徴付け。 -/
theorem cosetRel_right_respects_iff_normalizesElt (G : Grp) (H₀ : Subgroup G)
    (c : G.carrier) :
    (∀ a b : G.carrier, cosetRel G H₀ a b →
        cosetRel G H₀ (G.mul a c) (G.mul b c))
      ↔ normalizesElt G H₀ c := by
  constructor
  · intro hresp n hn
    have h1 : cosetRel G H₀ G.one n := by
      show H₀.mem (G.mul (G.inv G.one) n)
      rw [G.inv_one, G.one_mul]
      exact hn
    have h3 : H₀.mem (G.mul (G.inv (G.mul G.one c)) (G.mul n c)) :=
      hresp G.one n h1
    rw [G.one_mul, ← G.mul_assoc (G.inv c) n c] at h3
    exact h3
  · intro hnorm a b hab
    exact cosetRel_right_of_normalizesElt G H₀ c hnorm hab

/-! ## M255F-4: 右移動 deck を CatIso（同型 deck）に包む -/

/-- **補題 (M255F-4a): 右移動は可逆（左逆）** — c⁻¹ の右移動が c の右移動を
    打ち消す。 -/
theorem genRightMul_left_inv (G : Grp) (H₀ : Subgroup G) (c : G.carrier)
    (hc : normalizesElt G H₀ c) (hc' : normalizesElt G H₀ (G.inv c)) :
    ∀ x, (genRightMul G H₀ (G.inv c) hc').map ((genRightMul G H₀ c hc).map x)
      = x := by
  intro x
  induction x using Quot.ind; rename_i a
  show Quot.mk (cosetRel G H₀) (G.mul (G.mul a c) (G.inv c))
    = Quot.mk (cosetRel G H₀) a
  rw [G.mul_assoc, G.mul_inv, G.mul_one]

/-- **補題 (M255F-4b): 右移動は可逆（右逆）**。 -/
theorem genRightMul_right_inv (G : Grp) (H₀ : Subgroup G) (c : G.carrier)
    (hc : normalizesElt G H₀ c) (hc' : normalizesElt G H₀ (G.inv c)) :
    ∀ x, (genRightMul G H₀ c hc).map ((genRightMul G H₀ (G.inv c) hc').map x)
      = x := by
  intro x
  induction x using Quot.ind; rename_i a
  show Quot.mk (cosetRel G H₀) (G.mul (G.mul a (G.inv c)) c)
    = Quot.mk (cosetRel G H₀) a
  rw [G.mul_assoc, G.inv_mul, G.mul_one]

/-- **同型 deck（M255F-4c）**: c ∈ H かつ H が H₀ を正規化するとき、
    右移動 R_c は `GSetCat G` の同型射（deck 変換）。逆は c⁻¹ の右移動
    （c⁻¹ ∈ H も H₀ を正規化）。 -/
def genRightMulIso (G : Grp) (H H₀ : Subgroup G) (hn : normalizesSub G H H₀)
    (c : G.carrier) (hcH : H.mem c) :
    CatIso (GSetCat G) (cosetAction G H₀) (cosetAction G H₀) where
  hom := genRightMul G H₀ c (hn c hcH)
  inv := genRightMul G H₀ (G.inv c) (hn (G.inv c) (H.inv_mem hcH))
  hom_inv := ActHom.ext (fun x =>
    genRightMul_left_inv G H₀ c (hn c hcH) (hn (G.inv c) (H.inv_mem hcH)) x)
  inv_hom := ActHom.ext (fun x =>
    genRightMul_right_inv G H₀ c (hn c hcH) (hn (G.inv c) (H.inv_mem hcH)) x)

/-! ## M255F-5: 支配射 p : G/H₀ → G/H（H₀ ⊆ H） -/

/-- **支配射（M255F-5a）**: H₀ ⊆ H（hle）から剰余類同値が細分になるので
    Quot.lift で [a]_{H₀} ↦ [a]_H が降りる（同変）。M148F `coreDominates`
    の任意の部分群対版。 -/
def genDominates (G : Grp) (H₀ H : Subgroup G)
    (hle : ∀ g, H₀.mem g → H.mem g) :
    ActHom (cosetAction G H₀) (cosetAction G H) where
  map := Quot.lift (fun a => Quot.mk (cosetRel G H) a)
    (fun _ _ hab => Quot.sound (hle _ hab))
  equivariant := by
    intro g x
    induction x using Quot.ind
    rfl

/-- **補題 (M255F-5b): 支配射は全射（F-epi）** — 代表元をそのまま持ち上げる。 -/
theorem genDominates_surjective (G : Grp) (H₀ H : Subgroup G)
    (hle : ∀ g, H₀.mem g → H.mem g) :
    ∀ y, ∃ x, (genDominates G H₀ H hle).map x = y := by
  intro y
  induction y using Quot.ind; rename_i a
  exact ⟨Quot.mk (cosetRel G H₀) a, rfl⟩

/-! ## M255F-6: 十分側 — H₀ ⊴ H ⟹ ファイバー推移性 hfib -/

/-- **十分側（M255F-6）: 正規対 H₀ ⊴ H はファイバー推移性を与える** —
    H₀ ⊆ H かつ H が H₀ を正規化するなら、p = genDominates の同じ
    ファイバー上の二点 [a]_{H₀}, [a']_{H₀}（p b = p b' すなわち
    [a]_H = [a']_H）は右移動 deck R_c（c := a⁻¹a' ∈ H）で移り合う。
    * p 保存: [g·c]_H = [g]_H が c⁻¹ ∈ H から従う。
    * b ↦ b': [a·(a⁻¹a')]_{H₀} = [a']_{H₀}。
    M250F `intermediateNormalCover_hfib`（H₀ = core(H) 専用）を
    任意の H₀ ⊴ H へ一般化。choice 新規使用ゼロ。 -/
theorem normalPair_hfib (G : Grp) (H H₀ : Subgroup G)
    (hle : ∀ g, H₀.mem g → H.mem g) (hn : normalizesSub G H H₀) :
    ∀ b b' : (cosetAction G H₀).carrier,
      (genDominates G H₀ H hle).map b = (genDominates G H₀ H hle).map b' →
      ∃ σ : CatIso (GSetCat G) (cosetAction G H₀) (cosetAction G H₀),
        ActHom.comp σ.hom (genDominates G H₀ H hle) = genDominates G H₀ H hle ∧
        σ.hom.map b = b' := by
  intro b b'
  induction b using Quot.ind; rename_i a
  induction b' using Quot.ind; rename_i a'
  intro hbb'
  have hmem : H.mem (G.mul (G.inv a) a') := by
    have h' : Quot.mk (cosetRel G H) a = Quot.mk (cosetRel G H) a' := hbb'
    exact quot_exact_of_equiv (cosetRel G H) (cosetRel_refl G H)
      (fun hab => cosetRel_symm G H hab)
      (fun hab hbc => cosetRel_trans G H hab hbc) h'
  refine ⟨genRightMulIso G H H₀ hn (G.mul (G.inv a) a') hmem, ?_, ?_⟩
  · apply ActHom.ext
    intro x
    induction x using Quot.ind; rename_i g
    show Quot.mk (cosetRel G H) (G.mul g (G.mul (G.inv a) a'))
      = Quot.mk (cosetRel G H) g
    apply Quot.sound
    show H.mem (G.mul (G.inv (G.mul g (G.mul (G.inv a) a'))) g)
    rw [G.inv_mul_rev, G.mul_assoc, G.inv_mul, G.mul_one]
    exact H.inv_mem hmem
  · show Quot.mk (cosetRel G H₀) (G.mul a (G.mul (G.inv a) a'))
      = Quot.mk (cosetRel G H₀) a'
    rw [← G.mul_assoc, G.mul_inv, G.one_mul]

/-! ## M255F-7: 必要側の芯 — 同変自己写像は右移動に強制される -/

/-- **必要側の芯（M255F-7）: 同変自己写像が [1] を [c] に送るなら
    c は H₀ を正規化する** — G/H₀ の同変自己写像 σ に対し σ([1]) = [c]
    なら、任意の n ∈ H₀ について [n⁻¹] = [1] と σ の同変性
    σ([n⁻¹]) = n⁻¹·σ([1]) = [n⁻¹ c] から [n⁻¹ c] = [c]、剰余類の分離性で
    (n⁻¹c)⁻¹ c = c⁻¹ n c ∈ H₀。deck が右移動 R_c に一意に強制される
    （連結被覆の射の一点決定性）ことが正規性を強いる。**hfib より弱い
    「同変射の存在」だけで正規化が従う**（限定 (2)）。 -/
theorem equivariantEndo_forces_normalizesElt (G : Grp) (H₀ : Subgroup G)
    (c : G.carrier) (σ : ActHom (cosetAction G H₀) (cosetAction G H₀))
    (hσ : σ.map (Quot.mk (cosetRel G H₀) G.one) = Quot.mk (cosetRel G H₀) c) :
    normalizesElt G H₀ c := by
  intro n hn
  have heq1 : Quot.mk (cosetRel G H₀) (G.inv n)
      = Quot.mk (cosetRel G H₀) G.one := by
    apply Quot.sound
    show H₀.mem (G.mul (G.inv (G.inv n)) G.one)
    rw [G.inv_inv, G.mul_one]
    exact hn
  have e : σ.map ((cosetAction G H₀).act (G.inv n)
        (Quot.mk (cosetRel G H₀) G.one))
      = (cosetAction G H₀).act (G.inv n)
        (σ.map (Quot.mk (cosetRel G H₀) G.one)) :=
    σ.equivariant (G.inv n) (Quot.mk (cosetRel G H₀) G.one)
  have lhs_eq : σ.map ((cosetAction G H₀).act (G.inv n)
        (Quot.mk (cosetRel G H₀) G.one))
      = Quot.mk (cosetRel G H₀) c := by
    have harg : (cosetAction G H₀).act (G.inv n)
          (Quot.mk (cosetRel G H₀) G.one)
        = Quot.mk (cosetRel G H₀) G.one := by
      show Quot.mk (cosetRel G H₀) (G.mul (G.inv n) G.one)
        = Quot.mk (cosetRel G H₀) G.one
      rw [G.mul_one]
      exact heq1
    rw [harg, hσ]
  have rhs_eq : (cosetAction G H₀).act (G.inv n)
        (σ.map (Quot.mk (cosetRel G H₀) G.one))
      = Quot.mk (cosetRel G H₀) (G.mul (G.inv n) c) := by
    rw [hσ]
    rfl
  rw [lhs_eq, rhs_eq] at e
  have hstep : Quot.mk (cosetRel G H₀) (G.mul (G.inv n) c)
      = Quot.mk (cosetRel G H₀) c := e.symm
  have hrel : H₀.mem (G.mul (G.inv (G.mul (G.inv n) c)) c) :=
    quot_exact_of_equiv (cosetRel G H₀) (cosetRel_refl G H₀)
      (fun hab => cosetRel_symm G H₀ hab)
      (fun hab hbc => cosetRel_trans G H₀ hab hbc) hstep
  rw [G.inv_mul_rev, G.inv_inv] at hrel
  exact hrel

/-! ## M255F-8: 境界の iff（本丸・capstone） -/

/-- **必要側（M255F-8a）: hfib は H の H₀ 正規化を強いる** — p の
    ファイバー推移性 hfib を仮定すると、任意の c ∈ H について
    p([1]_{H₀}) = p([c]_{H₀})（c ∈ H ゆえ [1]_H = [c]_H）から deck σ が
    [1] を [c] に送り、M255F-7 で c ∈ N_G(H₀)。よって H が H₀ を正規化する。 -/
theorem normalPair_hfib_forces_normalizesSub (G : Grp) (H H₀ : Subgroup G)
    (hle : ∀ g, H₀.mem g → H.mem g)
    (hfib : ∀ b b' : (cosetAction G H₀).carrier,
      (genDominates G H₀ H hle).map b = (genDominates G H₀ H hle).map b' →
      ∃ σ : CatIso (GSetCat G) (cosetAction G H₀) (cosetAction G H₀),
        ActHom.comp σ.hom (genDominates G H₀ H hle) = genDominates G H₀ H hle ∧
        σ.hom.map b = b') :
    normalizesSub G H H₀ := by
  intro c hcH
  have hp : (genDominates G H₀ H hle).map (Quot.mk (cosetRel G H₀) G.one)
      = (genDominates G H₀ H hle).map (Quot.mk (cosetRel G H₀) c) := by
    show Quot.mk (cosetRel G H) G.one = Quot.mk (cosetRel G H) c
    apply Quot.sound
    show H.mem (G.mul (G.inv G.one) c)
    rw [G.inv_one, G.one_mul]
    exact hcH
  obtain ⟨σ, _, hσb⟩ :=
    hfib (Quot.mk (cosetRel G H₀) G.one) (Quot.mk (cosetRel G H₀) c) hp
  exact equivariantEndo_forces_normalizesElt G H₀ c σ.hom hσb

/-- **本丸・境界の iff（M255F-8b, capstone）: hfib ⟺ H₀ ⊴ H** —
    被覆 p : G/H₀ → G/H（H₀ ⊆ H）のファイバー推移性 hfib は、
    **H が H₀ を正規化する（H₀ が H で正規）ことと同値**である。
    十分（⟸）は M255F-6、必要（⟹）は M255F-8a。③の限界を
    「正規性 ⟺ ファイバー推移性」として両向きに確定した誠実な特徴付け。 -/
theorem normalPair_hfib_iff_normalizesSub (G : Grp) (H H₀ : Subgroup G)
    (hle : ∀ g, H₀.mem g → H.mem g) :
    (∀ b b' : (cosetAction G H₀).carrier,
      (genDominates G H₀ H hle).map b = (genDominates G H₀ H hle).map b' →
      ∃ σ : CatIso (GSetCat G) (cosetAction G H₀) (cosetAction G H₀),
        ActHom.comp σ.hom (genDominates G H₀ H hle) = genDominates G H₀ H hle ∧
        σ.hom.map b = b')
      ↔ normalizesSub G H H₀ :=
  ⟨normalPair_hfib_forces_normalizesSub G H H₀ hle,
   normalPair_hfib G H H₀ hle⟩

/-! ## M255F-9: 系 — 正規対での hquot の discharge -/

/-- **系（M255F-9, capstone）: 正規対 H₀ ⊴ H で hquot を discharge** —
    H₀ ⊆ H かつ H が H₀ を正規化するとき、p = genDominates の deck
    変換で不変な同変写像 v : G/H₀ → Y は p を経由して降りる
    （`gsetHquot_of_fiberTransitive` に M255F-6 の hfib を食わせる）。
    型が `gsetGaloisData`（G6 の choice）と切断 ρ の choice に言及する
    ため Classical.choice を継承（本証明体は choice 不使用、限定 (3)）。 -/
theorem normalPair_hquot (G : Grp) (H H₀ : Subgroup G)
    (hle : ∀ g, H₀.mem g → H.mem g) (hn : normalizesSub G H H₀)
    (Y : GAction G) (v : ActHom (cosetAction G H₀) Y)
    (hinv : ∀ σ : CatIso (GSetCat G) (cosetAction G H₀) (cosetAction G H₀),
      ActHom.comp σ.hom (genDominates G H₀ H hle) = genDominates G H₀ H hle →
      ActHom.comp σ.hom v = v) :
    ∃ u : ActHom (cosetAction G H) Y,
      ActHom.comp (genDominates G H₀ H hle) u = v :=
  gsetHquot_of_fiberTransitive (cosetAction G H₀) (cosetAction G H) Y
    (genDominates G H₀ H hle)
    (genDominates_surjective G H₀ H hle)
    (normalPair_hfib G H H₀ hle hn)
    v hinv

end IUT
