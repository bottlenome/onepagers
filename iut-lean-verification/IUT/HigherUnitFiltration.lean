/-
  IUT/HigherUnitFiltration.lean
  -- M415F HigherUnitFiltration [実・本物・柱B]
  -- complete_pct 影響: 柱B で 高次単数フィルトレーション U^(i)=1+m^i の降鎖 U^(i+1)⊆U^(i)・
  --   次数商 U^(i)/U^(i+1)≅k^+（剰余体加法群 ℤ/p、i≥1）を本物パッケージ化し、**不分岐ノルムが
  --   各レベルを保つ N(U^(i))=U^(i)** を M335F ノルム × M31 フィルトレーションの結合として本物証明
  --   （split model の単数部でノルムは恒等 ⇒ 全部分群を保存、特にフィルトレーション各段を保つ）。
  -- 正直な限定: 分岐ノルムによるフィルトレーション**番号シフト** N(U^(i))=U^(e(i))・
  --   U^(0)/U^(1)≅k^×（剰余体乗法群 μ 側）・完全な分岐理論（高次分岐群 upper/lower numbering）は後続。

  ────────────────────────────────────────────────────────────────────────
  二軸（CLAUDE.md §1）
  * 分類: **[実]**（(a) 昇格 + (b) 本物建設）。M31 の単数 filtration U^(d)=1+m^d と
    M335F のノルム写像 N_{L/K} を**結合**し、「不分岐ノルムはフィルトレーションの各段を
    保つ」という局所類体論の高次単数群の基本命題を本物で閉じる。
  * complete_pct 影響: **前進あり**（柱B 高次単数フィルトレーション×ノルムの本物結合）。
    既存 M31 は filtration と次数商を、M335F はノルム写像を**別々に**持っていた。本モジュールは
    両者を split model U := principalUnits で噛み合わせ、`huf_norm_map_level`
    （N(U^(i))=U^(i)、不分岐）を新規に本物証明する。

  既存モジュールの何を本物化したか
  * M31 `unitFiltration`/`unitTheta`（U^(d)・次数商 θ_d）を高次単数フィルトレーションの
    降鎖＋次数商同型のパッケージ `HigherUnitFiltrationData` として昇格。
  * M335F `normGMap`/`normG_units`（不分岐ノルムの単数への恒等作用）を、
    フィルトレーション付き単数群 split model 上へ適用し、**ノルムが各段を保存**する
    ことを `huf_norm_map_level` で本物証明（M335F 単数全射を段ごとに精密化）。

  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
  * `hufLevel` / `huf_nested` / `huf_antitone` / `huf_top` / `huf_separated`
      — 高次単数フィルトレーション U^(i) の降鎖・U^(1)=全体・分離性
  * `hufGradedMap` / `huf_graded_hom` / `huf_graded_kernel` / `huf_graded_surj`
      — 次数商 U^(i)/U^(i+1) ≅ k^+（剰余体加法群 ℤ/p、i≥1）の第一同型三点セット
  * `hufSplitLevel` — split model K^×=ℤ×O^× の単数部フィルトレーション部分群
  * `huf_norm_map_level` — **N(U^(i))=U^(i)**（不分岐ノルムは各段を保つ・本命題）
  * `huf_norm_preserves` / `huf_norm_surj_level` — 前方保存・段ごと全射
  * `huf_units_are_norms` — 単数はノルム（M335F normG_units への接続）
  * `HigherUnitFiltrationData` / `hufDataOf` / `huf_exists` — capstone
  * `huf_deg2_*` — p=2 の worked examples

  正直な限定（CLAUDE.md §4: 消去・弱化禁止）
  * ここで扱う剰余体加法群は次数商 U^(i)/U^(i+1)（i≥1）で ℤ/p に同型。**U^(0)/U^(1)≅k^×**
    （Teichmüller/μ 側の乗法群）は本モジュール対象外——後続。
  * ノルムの作用は**不分岐**（split model で単数部が恒等）に限る。**分岐拡大での
    フィルトレーション番号シフト** N(U^(i))=U^(ψ(i)) と高次分岐群（Hasse–Arf の upper
    numbering）は骨組みも置かず後続。
  * 単数群の実体は M30 principalUnits（K=ℚ_p の 1+pℤ_p）。一般局所体 O_K^× ではない。

  全て選択公理不使用（propext/Quot.sound のみ）。共有ファイル未変更（新規 1 本）。
-/
import IUT.NormGroup
import IUT.UnitFiltration
import IUT.NormCorrespondence

namespace IUT

/-! ## §1 高次単数フィルトレーション U^(i) の降鎖 -/

/-- **M415F-1: 高次単数フィルトレーション** U^(i) = 1 + m^i（M31 の
    `unitFiltration` を主単数群 principalUnits の降鎖として採る）。 -/
def hufLevel (p i : Nat) : Subgroup (principalUnits p) := unitFiltration p i

/-- **M415F-2a: 降鎖（隣接段）** U^(i+1) ⊆ U^(i)。 -/
theorem huf_nested (p i : Nat) (x : (principalUnits p).carrier)
    (hx : (hufLevel p (i + 1)).mem x) : (hufLevel p i).mem x :=
  unitFiltration_antitone p (Nat.le_succ i) x hx

/-- **M415F-2b: 降鎖（一般）** d ≤ e ⇒ U^(e) ⊆ U^(d)。 -/
theorem huf_antitone (p : Nat) {d e : Nat} (h : d ≤ e)
    (x : (principalUnits p).carrier) (hx : (hufLevel p e).mem x) :
    (hufLevel p d).mem x :=
  unitFiltration_antitone p h x hx

/-- **M415F-2c: 最上段** U^(1) = 主単数群全体。 -/
theorem huf_top (p : Nat) (x : (principalUnits p).carrier) :
    (hufLevel p 1).mem x :=
  unitFiltration_full p x

/-- **M415F-2d: 分離性** ∩_i U^(i) = {1}（1 の近傍基）。 -/
theorem huf_separated (p : Nat) (x : (principalUnits p).carrier)
    (hx : ∀ i, (hufLevel p i).mem x) : x = (principalUnits p).one :=
  unitFiltration_separated p x hx

/-! ## §2 次数商 U^(i)/U^(i+1) ≅ k^+（剰余体加法群 ℤ/p, i≥1） -/

/-- **M415F-3: 次数商写像** θ_i : U^(i) → k^+ = ℤ/p（M31 `unitTheta`）。
    1 + m^i·u ↦ u mod m。 -/
def hufGradedMap (p i : Nat) (hp : 1 ≤ p) (x : (principalUnits p).carrier) :
    (zmod p).carrier :=
  unitTheta p i hp x

/-- **M415F-4: θ_i は準同型**（i≥1）— θ(xy)=θ(x)+θ(y)。 -/
theorem huf_graded_hom (p i : Nat) (hp : 1 ≤ p) (hi : 1 ≤ i)
    (x y : (principalUnits p).carrier)
    (hx : (hufLevel p i).mem x) (hy : (hufLevel p i).mem y) :
    hufGradedMap p i hp ((principalUnits p).mul x y)
      = (zmod p).mul (hufGradedMap p i hp x) (hufGradedMap p i hp y) :=
  unitTheta_hom p i hp hi x y hx hy

/-- **M415F-5: θ_i の核 = U^(i+1)** — 次数商の分子・分母同定。 -/
theorem huf_graded_kernel (p i : Nat) (hp : 1 ≤ p)
    (x : (principalUnits p).carrier) (hx : (hufLevel p i).mem x) :
    hufGradedMap p i hp x = Quot.mk (modCong p).rel 0
      ↔ (hufLevel p (i + 1)).mem x :=
  unitTheta_kernel p i hp x hx

/-- **M415F-6: θ_i は全射**（i≥1）— 任意の剰余類 c は 1+m^i·c の像。
    M415F-4〜6 で **U^(i)/U^(i+1) ≅ k^+（ℤ/p）**。 -/
theorem huf_graded_surj (p i : Nat) (hp : 1 ≤ p) (hi : 1 ≤ i)
    (c : (zmod p).carrier) :
    ∃ x : (principalUnits p).carrier,
      (hufLevel p i).mem x ∧ hufGradedMap p i hp x = c :=
  unitTheta_surj p i hp hi c

/-! ## §3 split model の単数部フィルトレーション部分群 -/

/-- **M415F-7: split model の段部分群** — K^× = ℤ × O^× 上で
    「付値 0 かつ 単数部 ∈ U^(i)」なる部分群。ノルム作用を段ごとに
    論じるための単数群フィルトレーションの split 表示。 -/
def hufSplitLevel (p i : Nat) : Subgroup (unitsModel (principalUnits p)) where
  mem := fun g => g.1 = (0 : Int) ∧ (unitFiltration p i).mem g.2
  one_mem := ⟨rfl, (unitFiltration p i).one_mem⟩
  mul_mem := fun {a b} ha hb => by
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, (unitFiltration p i).mul_mem ha2 hb2⟩
    show a.1 + b.1 = (0 : Int)
    rw [ha1, hb1]
    exact Int.add_zero 0
  inv_mem := fun {a} ha => by
    obtain ⟨ha1, ha2⟩ := ha
    refine ⟨?_, (unitFiltration p i).inv_mem ha2⟩
    show -a.1 = (0 : Int)
    rw [ha1]
    exact Int.neg_zero

/-! ## §4 不分岐ノルムの段ごとの作用 N(U^(i)) = U^(i) -/

/-- **M415F-8: 不分岐ノルムは各段を保つ** N(U^(i)) = U^(i)。
    split model 上でノルム N(m,x) = (n·m, x) は単数部を恒等に写すため、
    付値 0 の段部分群 U^(i)（単数側フィルトレーション）を**押し出しても
    引き戻しても不変**。M335F ノルム × M31 フィルトレーションの本物結合。 -/
theorem huf_norm_map_level (p i : Nat) (n : Int)
    (y : (unitsModel (principalUnits p)).carrier) :
    (Subgroup.map (normGMap (principalUnits p) n) (hufSplitLevel p i)).mem y
      ↔ (hufSplitLevel p i).mem y := by
  constructor
  · intro h
    obtain ⟨z, hz, hzy⟩ := h
    obtain ⟨hz1, hz2⟩ := hz
    have hval : ((n * z.1 : Int), z.2) = y := by
      rw [← normGMap_apply (principalUnits p) n z.1 z.2]; exact hzy
    have hf : (n * z.1 : Int) = y.1 := congrArg (fun w => w.1) hval
    have hs : z.2 = y.2 := congrArg (fun w => w.2) hval
    refine ⟨?_, ?_⟩
    · rw [← hf, hz1, Int.mul_zero]
    · rw [← hs]; exact hz2
  · intro hy
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨((0 : Int), y.2), ⟨rfl, hy2⟩, ?_⟩
    show (normGMap (principalUnits p) n).map ((0 : Int), y.2) = y
    rw [normGMap_apply (principalUnits p) n 0 y.2, Int.mul_zero]
    exact congrArg (fun t => (t, y.2)) hy1.symm

/-- **M415F-9: 前方保存** — N は U^(i) を U^(i) の中へ写す。 -/
theorem huf_norm_preserves (p i : Nat) (n : Int)
    (y : (unitsModel (principalUnits p)).carrier)
    (hy : (Subgroup.map (normGMap (principalUnits p) n) (hufSplitLevel p i)).mem y) :
    (hufSplitLevel p i).mem y :=
  (huf_norm_map_level p i n y).mp hy

/-- **M415F-10: 段ごとの全射** — U^(i) の任意の単数 (0,x)（x ∈ U^(i)）は
    ある U^(i) 元のノルムに等しい（不分岐ノルムは各段で全射）。 -/
theorem huf_norm_surj_level (p i : Nat) (n : Int)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p i).mem x) :
    (Subgroup.map (normGMap (principalUnits p) n) (hufSplitLevel p i)).mem
      ((0 : Int), x) :=
  (huf_norm_map_level p i n ((0 : Int), x)).mpr ⟨rfl, hx⟩

/-- **M415F-11: 単数はノルム**（M335F `normG_units` への接続）—
    任意の単数 (0,u) は不分岐ノルム群に入る（フィルトレーション U^(1) 段の帰結）。 -/
theorem huf_units_are_norms (p : Nat) (n : Int) (u : (principalUnits p).carrier) :
    (normGSubgroup (principalUnits p) n).mem ((0 : Int), u) :=
  normG_units (principalUnits p) n u

/-! ## §5 capstone: 高次単数フィルトレーションデータ -/

/-- **M415F-12: 高次単数フィルトレーションデータ** — 素数 p、単位性 hp、
    ノルム次数 deg、フィルトレーション降鎖 level i = U^(i)、split 段
    splitLevel、次数商写像 graded を束ね、
      * 降鎖 U^(i+1)⊆U^(i)（`level_nested`）
      * 次数商が準同型（i≥1, `graded_hom`）
      * 次数商の核 = U^(i+1)（`graded_kernel`）
      * 次数商が全射（i≥1, `graded_surj`）— 以上で U^(i)/U^(i+1)≅k^+
      * 不分岐ノルムが各段を保つ N(U^(i))=U^(i)（`norm_preserves`）
    を要請する。局所類体論の高次単数群の代数的核。 -/
structure HigherUnitFiltrationData where
  p : Nat
  hp : 1 ≤ p
  deg : Int
  level : Nat → Subgroup (principalUnits p)
  splitLevel : Nat → Subgroup (unitsModel (principalUnits p))
  graded : Nat → (principalUnits p).carrier → (zmod p).carrier
  level_nested : ∀ i x, (level (i + 1)).mem x → (level i).mem x
  graded_hom : ∀ i, 1 ≤ i → ∀ x y, (level i).mem x → (level i).mem y →
    graded i ((principalUnits p).mul x y)
      = (zmod p).mul (graded i x) (graded i y)
  graded_kernel : ∀ i x, (level i).mem x →
    (graded i x = Quot.mk (modCong p).rel 0 ↔ (level (i + 1)).mem x)
  graded_surj : ∀ i, 1 ≤ i → ∀ c, ∃ x, (level i).mem x ∧ graded i x = c
  norm_preserves : ∀ i y,
    (Subgroup.map (normGMap (principalUnits p) deg) (splitLevel i)).mem y
      ↔ (splitLevel i).mem y

/-- **M415F-13: フィルトレーションデータの構成**（素数 p、単位性 hp、
    次数 n から本物の witness を組む）。 -/
def hufDataOf (p : Nat) (hp : 1 ≤ p) (n : Int) : HigherUnitFiltrationData where
  p := p
  hp := hp
  deg := n
  level := fun i => hufLevel p i
  splitLevel := fun i => hufSplitLevel p i
  graded := fun i => hufGradedMap p i hp
  level_nested := fun i x hx => huf_nested p i x hx
  graded_hom := fun i hi x y hx hy => huf_graded_hom p i hp hi x y hx hy
  graded_kernel := fun i x hx => huf_graded_kernel p i hp x hx
  graded_surj := fun i hi c => huf_graded_surj p i hp hi c
  norm_preserves := fun i y => huf_norm_map_level p i n y

/-- **M415F-14: フィルトレーションデータの存在**（無矛盾性 witness、p=2）。 -/
theorem huf_exists : Nonempty HigherUnitFiltrationData :=
  ⟨hufDataOf 2 (by omega) 3⟩

/-! ## §6 worked examples: p = 2 -/

/-- **M415F-15: 実例** U^(2) ⊆ U^(1)（p=2 の降鎖の一段）。 -/
theorem huf_deg2_nested (x : (principalUnits 2).carrier)
    (hx : (hufLevel 2 2).mem x) : (hufLevel 2 1).mem x :=
  huf_nested 2 1 x hx

/-- **M415F-16: 実例** 次数商 U^(1)/U^(2) は両剰余類 0,1 mod 2 を覆う
    （p=2 の次数商全射）。 -/
theorem huf_deg2_graded_surj (c : (zmod 2).carrier) :
    ∃ x : (principalUnits 2).carrier,
      (hufLevel 2 1).mem x ∧ hufGradedMap 2 1 (by omega) x = c :=
  huf_graded_surj 2 1 (by omega) (by omega) c

/-- **M415F-17: 実例** 不分岐次数 3 のノルムは p=2 の段 U^(1) を保つ。 -/
theorem huf_deg2_norm_level (y : (unitsModel (principalUnits 2)).carrier) :
    (Subgroup.map (normGMap (principalUnits 2) 3) (hufSplitLevel 2 1)).mem y
      ↔ (hufSplitLevel 2 1).mem y :=
  huf_norm_map_level 2 1 3 y

end IUT
