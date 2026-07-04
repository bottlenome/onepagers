/-
  # M191F: Tate 曲線の有限連続被覆圏の実体化 — 有限レベル GAction の圏・和/ファイバー積の有限性保存・ファイバー忠実性（柱A A-3β-2・並行部品）

  A-3（エタール的入力の代理化）β 系列の第二歩。A-3β-1（M188F
  `TateCoverGroup.lean`）で建設した「テンパードデッキ群 ℤ・数論的
  基本群 Π・有限商逆系 ℤ/n・副有限完備化 ẑ」の三層束ねを入力に、
  **Tate 曲線の有限連続被覆の圏**（= 具体提示された π₁ の有限連続
  作用の圏。スキーム論的エタール被覆の代理）を実体化する。

  被覆理論の翻訳: 有限エタール被覆 ↔ **有限集合 + デッキ群の連続作用**
  （連続 = 固定化群が開 = 作用がある有限商 ℤ/n を経由する）。
  ここではデッキ群 = `tateDeckGrp` = ℤ を採り、「連続」を
  「作用が `quotProj : ℤ → ℤ/n` を通じて有限商を経由する
  （= 添字 n の合同で不変）」と定式化して、位相を経由せず代数的に
  捉える（M13 の副有限「代数側」形式化と同じ方針）。

  * M191F-1 `FactorsThrough` / `ContinuousCover` / `IsFiniteCover` —
    連続性（有限商 ℤ/n を経由 = 開固定化群）と「有限連続被覆」述語。
    `factorsThrough_of_dvd`（連続性は割り切りに沿って粗い商へ上がる）
  * M191F-2 `deckQuot` / `descendAct` / `descend_factors` /
    `descendCover` — 有限商 ℤ/n の作用（有限レベル GAction）を
    デッキ群 ℤ の連続作用に**降下**する具体構成。M188F の
    `quotProj`（= tateFiniteSystem の各段）と M20 の `GAction` の接続
  * M191F-3 `finite_sum` / `finite_prod` / `finite_subtype` —
    有限性の閉性補題（core Lean のみ・選択公理不使用）。被覆の
    台集合の有限性が圏の各操作で保存されることの算術核
  * M191F-4 `TateCover`（被覆の束）・`unitCover`（終対象）・
    `emptyCover`（始対象）・`sumCover`（直和 = 余積）・
    `pullbackCover`（ファイバー積）・`prodCover`（積）— Galois 圏の
    操作（M20 の `sumAction`/`pullbackAction`/`unitAction`/
    `emptyAction` の再利用）で被覆圏が閉じること。各操作が
    **有限性と連続性を同時に保存**する（レベルは公倍数 m·n を採る）
  * M191F-5 `tateLevelCover` / `tateLevelCover_act` — レベル n の
    標準被覆（ℤ が ℤ/n に平行移動で作用）。A-3β-1 の有限商 ℤ/n の
    実例化。台は M17 の `zmod_finite` で真に有限
  * M191F-6 `cover_fiber_faithful` — **ファイバー関手（台有限集合）は
    この部分圏上で忠実**（同変写像はその台写像で決まる。M20 の
    ファイバー関手 F の被覆圏への制限）
  * M191F-7 `profiniteLevel` / `cover_deck_profinite_compat` —
    A-3β-1 との接続: レベル n 被覆の構造群 ℤ/n は副有限完備化
    `tateProfinite` = ẑ の有限商であり、被覆の作用は「テンパード
    デッキ座標経由」でも「副有限完備化経由」でも一致する
    （M188F の `tateCompletion_proj` の被覆圏版）。被覆圏全体が ẑ を
    見ていることの形式的内容
  * M191F-8 `TateCoverCatData` / `tateCoverCatData` /
    `tateCoverCat_exists` — 総括データ・証人・存在定理

  **意義**: 「具体提示された π₁ の有限連続作用の圏」= 有限エタール
  被覆圏の代理が、既存資産（M188F の群・M13 の ℤ/n 逆系・M20 の
  GAction とその和/ファイバー積・M17 の有限性）の再利用だけで一
  ファイルに実体化された。被覆は「有限台 + ℤ/n 経由の連続作用」
  として構成的に与えられ、終対象・始対象・直和・ファイバー積・積の
  各操作で有限性と連続性が同時に保存される（レベルを公倍数で束ねる
  ことで両立）。ファイバー関手はこの部分圏上で忠実であり、各被覆の
  構造群は A-3β-1 の副有限完備化 ẑ の有限商として整合する。

  **正直な限定**: (1) 本モジュールが与えるのは被覆**圏の操作構造**
  （対象 = 有限連続被覆・終始対象・和・ファイバー積・積・忠実な
  ファイバー関手）であって、`GaloisCatData` インスタンス（G1–G6 を
  満たす抽象 Galois 圏としての完全な充足）や主定理
  `Aut(F) = π₁` の被覆圏版は **A-3β-3/4** に譲る。ここでの被覆は
  デッキ群 ℤ（幾何的部分）の連続作用に限り、数論的 π₁ = Π 全体
  （G_K 方向）の作用や連結性・ガロア対象の分類は扱わない。
  (2) 「連続性」は位相を導入せず「有限商 ℤ/n を経由（= 合同不変）」
  で代理する（M13 と同じ代数側形式化）。開部分群・射有限位相は未導入。
  (3) π₁ の提示は幾何からの**入力**であり、実際の Tate 曲線から
  計算された不変量でもスキーム論的エタール性でもない。デッキ群も
  玩具モデル ℤ（M188F の `tateDeckGrp`）である。(4) ファイバー積は
  台集合の有限部分集合として構成し、忠実性は同変写像が台写像で
  決まるという G-Set 圏（M20）の事実の制限であって、被覆圏が Galois
  圏の全公理を満たすことの証明ではない（それは A-3β-3）。

  全て sorry なし・選択公理不使用（新規 Classical.choice なし）。
  サブエージェント並行部品。
-/
import IUT.TateCoverGroup
import IUT.AbstractGalois
import IUT.Finiteness

namespace IUT

/-! ## M191F-1: 連続性（有限商 ℤ/n を経由）と有限連続被覆 -/

/-- **連続性の代理（M191F-1）**: デッキ群 ℤ の作用が添字 n の合同で
    不変（= 有限商 ℤ/n を経由 = 固定化群が指数有限で開）。位相を
    導入せず「合同不変」で連続性を代理する（M13 の副有限代数側
    形式化と同じ方針）。 -/
def FactorsThrough (n : Nat) (X : GAction tateDeckGrp) : Prop :=
  ∀ (g g' : tateDeckGrp.carrier) (x : X.carrier),
    (modCong n).rel g g' → X.act g x = X.act g' x

/-- **連続被覆（M191F-1）**: ある正の有限レベル n を経由するデッキ
    作用。エタール被覆の連続モノドロミー作用の代理。 -/
def ContinuousCover (X : GAction tateDeckGrp) : Prop :=
  ∃ n : Nat, 0 < n ∧ FactorsThrough n X

/-- **有限連続被覆（M191F-1）**: 台集合が有限（M17 の `Finite`）で
    作用が連続（有限商経由）。有限エタール被覆の代理。 -/
def IsFiniteCover (X : GAction tateDeckGrp) : Prop :=
  Finite X.carrier ∧ ContinuousCover X

/-- **補題 (M191F-1): 連続性は割り切りに沿って粗い商へ上がる** —
    m ∣ n のとき、レベル m で連続なら（より細かい）レベル n でも
    連続。合同 n ∣ (g−g') は m ∣ (g−g') を含意する（ℤ/n → ℤ/m）。
    和・積のレベルを公倍数に束ねる際の核。 -/
theorem factorsThrough_of_dvd {m n : Nat} (h : m ∣ n)
    {X : GAction tateDeckGrp} (hm : FactorsThrough m X) : FactorsThrough n X := by
  intro g g' x hrel
  apply hm g g' x
  exact Int.dvd_trans (Int.ofNat_dvd.mpr h) hrel

/-! ## M191F-2: 有限商作用のデッキ群への降下 -/

/-- **降下準同型（M191F-2）**: デッキ群 ℤ からその有限商 ℤ/n への
    射影（M188F の各有限レベル `quotProj` = tateFiniteSystem の段）。 -/
def deckQuot (n : Nat) : Hom tateDeckGrp (zmod n) := quotProj intGrp (modCong n)

/-- **降下作用（M191F-2）**: 有限商 ℤ/n の作用（有限レベル GAction）を
    デッキ群 ℤ の作用に引き戻す（`deckQuot n` に沿った制限）。
    これがエタール被覆の「有限商経由の連続作用」の具体形。 -/
def descendAct {n : Nat} (X : GAction (zmod n)) : GAction tateDeckGrp where
  carrier := X.carrier
  act := fun g x => X.act ((deckQuot n).map g) x
  act_one := fun x => by
    show X.act ((deckQuot n).map tateDeckGrp.one) x = x
    rw [(deckQuot n).map_one, X.act_one]
  act_mul := fun g h x => by
    show X.act ((deckQuot n).map (tateDeckGrp.mul g h)) x
        = X.act ((deckQuot n).map g) (X.act ((deckQuot n).map h) x)
    rw [(deckQuot n).map_mul, X.act_mul]

/-- 降下作用はレベル n で連続（合同で作用が不変。`quotProj` の
    合同不変性 = 商の well-defined 性）。 -/
theorem descend_factors {n : Nat} (X : GAction (zmod n)) :
    FactorsThrough n (descendAct X) := by
  intro g g' x hrel
  show X.act ((deckQuot n).map g) x = X.act ((deckQuot n).map g') x
  have hq : (deckQuot n).map g = (deckQuot n).map g' := Quot.sound hrel
  rw [hq]

/-! ## M191F-3: 有限性の閉性補題（core Lean・選択公理不使用） -/

/-- **有限直和は有限（M191F-3a）**: [0,m) と [0,k) のコードから
    [0,m+k) のコードを組む（inr 側を m だけずらす）。 -/
theorem finite_sum {A B : Type} (hA : Finite A) (hB : Finite B) :
    Finite (Sum A B) := by
  obtain ⟨m, cA, hmA, hiA⟩ := hA
  obtain ⟨k, cB, hkB, hiB⟩ := hB
  refine ⟨m + k, fun s => match s with
      | .inl a => cA a
      | .inr b => m + cB b, ?_, ?_⟩
  · intro s
    cases s with
    | inl a =>
      show cA a < m + k
      have := hmA a
      omega
    | inr b =>
      show m + cB b < m + k
      have := hkB b
      omega
  · intro s t h
    cases s with
    | inl a =>
      cases t with
      | inl a' =>
        show Sum.inl a = Sum.inl a'
        have hc : cA a = cA a' := h
        rw [hiA a a' hc]
      | inr b' =>
        exfalso
        have hc : cA a = m + cB b' := h
        have := hmA a
        omega
    | inr b =>
      cases t with
      | inl a' =>
        exfalso
        have hc : m + cB b = cA a' := h
        have := hmA a'
        omega
      | inr b' =>
        show Sum.inr b = Sum.inr b'
        have hc : m + cB b = m + cB b' := h
        have hc2 : cB b = cB b' := by omega
        rw [hiB b b' hc2]

/-- **有限直積は有限（M191F-3b）**: コード (a,b) ↦ cA a·k + cB b
    （k = B のコード上界）。剰余 mod k で cB b を、商で cA a を復元
    して単射性を示す（乗法の非線形は名前付き補題で処理）。 -/
theorem finite_prod {A B : Type} (hA : Finite A) (hB : Finite B) :
    Finite (A × B) := by
  obtain ⟨m, cA, hmA, hiA⟩ := hA
  obtain ⟨k, cB, hkB, hiB⟩ := hB
  refine ⟨m * k, fun p => cA p.1 * k + cB p.2, ?_, ?_⟩
  · intro p
    have hb : cB p.2 < k := hkB p.2
    have hlt : cA p.1 * k + cB p.2 < cA p.1 * k + k :=
      Nat.add_lt_add_left hb (cA p.1 * k)
    have heq : Nat.succ (cA p.1) * k = cA p.1 * k + k := Nat.succ_mul (cA p.1) k
    have hle : Nat.succ (cA p.1) * k ≤ m * k :=
      Nat.mul_le_mul (hmA p.1) (Nat.le_refl k)
    rw [← heq] at hlt
    exact Nat.lt_of_lt_of_le hlt hle
  · intro p q h
    obtain ⟨a1, a2⟩ := p
    obtain ⟨b1, b2⟩ := q
    have hh : cA a1 * k + cB a2 = cA b1 * k + cB b2 := h
    have hbp : cB a2 < k := hkB a2
    have hbq : cB b2 < k := hkB b2
    have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) hbp
    have hmodp : (cA a1 * k + cB a2) % k = cB a2 := by
      rw [Nat.add_comm (cA a1 * k) (cB a2), Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hbp]
    have hmodq : (cA b1 * k + cB b2) % k = cB b2 := by
      rw [Nat.add_comm (cA b1 * k) (cB b2), Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hbq]
    have hcB : cB a2 = cB b2 := by rw [← hmodp, ← hmodq, hh]
    have ha2 : a2 = b2 := hiB a2 b2 hcB
    have hmul : cA a1 * k = cA b1 * k := by
      have h2 : cA a1 * k + cB a2 = cA b1 * k + cB a2 := by rw [hh, hcB]
      exact Nat.add_right_cancel h2
    have ha1 : a1 = b1 := hiA a1 b1 (Nat.eq_of_mul_eq_mul_right hk hmul)
    rw [ha1, ha2]

/-- **有限型の部分型は有限（M191F-3c）**: 台のコードを `.val` に制限
    （単射性は Subtype.ext）。ファイバー積の台（積の部分集合）の
    有限性に使う。 -/
theorem finite_subtype {A : Type} {P : A → Prop} (hA : Finite A) :
    Finite { a : A // P a } := by
  obtain ⟨m, c, hm, hi⟩ := hA
  refine ⟨m, fun s => c s.val, fun s => hm s.val, ?_⟩
  intro s t h
  apply Subtype.ext
  exact hi s.val t.val h

/-- 一点集合は有限（終対象の台）。 -/
theorem finite_punit : Finite PUnit := by
  refine ⟨1, fun _ => 0, fun _ => Nat.one_pos, ?_⟩
  intro a b _
  cases a
  cases b
  rfl

/-- 空集合は有限（始対象の台）。 -/
theorem finite_empty : Finite Empty :=
  ⟨0, fun e => (nomatch e), fun e => (nomatch e), fun e _ _ => (nomatch e)⟩

/-! ## M191F-4: Tate 有限連続被覆と圏の操作 -/

/-- **Tate 有限連続被覆（M191F-4）**: デッキ群 ℤ の GAction であって
    台が有限・ある正のレベル n を経由して連続。有限エタール被覆の
    ファイバー + 連続モノドロミー作用の代理（対象）。 -/
structure TateCover where
  /-- デッキ群 ℤ の作用（被覆のファイバー + モノドロミー）。 -/
  carrier : GAction tateDeckGrp
  /-- 台集合は有限（M17 の意味）。 -/
  finite : Finite carrier.carrier
  /-- 連続レベル（作用が経由する有限商 ℤ/level）。 -/
  level : Nat
  /-- レベルは正。 -/
  level_pos : 0 < level
  /-- 作用はレベルを経由して連続（合同不変）。 -/
  factors : FactorsThrough level carrier

/-- 被覆は連続被覆である（連続性の証人を取り出す）。 -/
theorem coverContinuous (X : TateCover) : ContinuousCover X.carrier :=
  ⟨X.level, X.level_pos, X.factors⟩

/-- 被覆は有限連続被覆である。 -/
theorem coverIsFinite (X : TateCover) : IsFiniteCover X.carrier :=
  ⟨X.finite, coverContinuous X⟩

/-- 有限レベル ℤ/n の有限 GAction から被覆を作る（降下）。 -/
def descendCover {n : Nat} (hn : 0 < n) (X : GAction (zmod n))
    (hfin : Finite X.carrier) : TateCover where
  carrier := descendAct X
  finite := hfin
  level := n
  level_pos := hn
  factors := descend_factors X

/-- **終対象（M191F-4）**: 一点の自明作用（M20 の `unitAction`）。
    台は有限、任意のレベルで連続。 -/
def unitCover : TateCover where
  carrier := unitAction tateDeckGrp
  finite := finite_punit
  level := 1
  level_pos := Nat.one_pos
  factors := fun _ _ _ _ => rfl

/-- **始対象（M191F-4）**: 空作用（M20 の `emptyAction`）。 -/
def emptyCover : TateCover where
  carrier := emptyAction tateDeckGrp
  finite := finite_empty
  level := 1
  level_pos := Nat.one_pos
  factors := fun _ _ _ _ => rfl

/-- **直和 = 余積（M191F-4）**: 被覆の非交和（M20 の `sumAction`）。
    台は有限直和で有限、レベルは公倍数 level_X·level_Y で両者が
    連続を保つ（`factorsThrough_of_dvd`）。 -/
def sumCover (X Y : TateCover) : TateCover where
  carrier := sumAction tateDeckGrp X.carrier Y.carrier
  finite := finite_sum X.finite Y.finite
  level := X.level * Y.level
  level_pos := Nat.mul_pos X.level_pos Y.level_pos
  factors := by
    intro g g' s hrel
    have hX := factorsThrough_of_dvd (Nat.dvd_mul_right X.level Y.level) X.factors
    have hY := factorsThrough_of_dvd (Nat.dvd_mul_left Y.level X.level) Y.factors
    cases s with
    | inl x =>
      show Sum.inl (X.carrier.act g x) = Sum.inl (X.carrier.act g' x)
      rw [hX g g' x hrel]
    | inr y =>
      show Sum.inr (Y.carrier.act g y) = Sum.inr (Y.carrier.act g' y)
      rw [hY g g' y hrel]

/-- **ファイバー積（M191F-4）**: 射の対 f : X → Z ← Y : g の
    ファイバー積（M20 の `pullbackAction`）。台は積の部分型で有限、
    レベルは公倍数で連続を保つ。 -/
def pullbackCover (X Y Z : TateCover) (f : ActHom X.carrier Z.carrier)
    (g : ActHom Y.carrier Z.carrier) : TateCover where
  carrier := pullbackAction tateDeckGrp f g
  finite := finite_subtype (finite_prod X.finite Y.finite)
  level := X.level * Y.level
  level_pos := Nat.mul_pos X.level_pos Y.level_pos
  factors := by
    intro g₀ g₁ p hrel
    have hX := factorsThrough_of_dvd (Nat.dvd_mul_right X.level Y.level) X.factors
    have hY := factorsThrough_of_dvd (Nat.dvd_mul_left Y.level X.level) Y.factors
    apply Subtype.ext
    show (X.carrier.act g₀ p.val.1, Y.carrier.act g₀ p.val.2)
        = (X.carrier.act g₁ p.val.1, Y.carrier.act g₁ p.val.2)
    rw [hX g₀ g₁ p.val.1 hrel, hY g₀ g₁ p.val.2 hrel]

/-- 一点作用への唯一の同変写像（終対象への射）。 -/
def toUnitHom (X : GAction tateDeckGrp) : ActHom X (unitAction tateDeckGrp) :=
  ⟨fun _ => PUnit.unit, fun _ _ => rfl⟩

/-- **積（M191F-4）**: 終対象上のファイバー積として導出した積
    X × Y = X ×_pt Y（M21-1 の圏論的導出の被覆圏版）。 -/
def prodCover (X Y : TateCover) : TateCover :=
  pullbackCover X Y unitCover (toUnitHom X.carrier) (toUnitHom Y.carrier)

/-! ## M191F-5: レベル n の標準被覆（A-3β-1 の有限商の実例化） -/

/-- **レベル n の標準被覆（M191F-5）**: デッキ群 ℤ が有限商 ℤ/n に
    平行移動（正則作用）で作用する被覆。A-3β-1 の有限商 ℤ/n
    （`tateFiniteSystem` の段）の被覆としての実例化。台は M17 の
    `zmod_finite` で真に有限。 -/
def tateLevelCover (n : Nat) (hn : 0 < n) : TateCover :=
  descendCover hn (regAction (zmod n)) (zmod_finite n hn)

/-- レベル n 標準被覆の作用は「ℤ/n への還元による平行移動」
    そのもの（定義的に rfl）。 -/
theorem tateLevelCover_act (n : Nat) (hn : 0 < n) (g : tateDeckGrp.carrier)
    (x : (zmod n).carrier) :
    (tateLevelCover n hn).carrier.act g x
      = (zmod n).mul ((deckQuot n).map g) x := rfl

/-! ## M191F-6: ファイバー関手の忠実性（被覆圏への制限） -/

/-- **定理 (M191F-6): ファイバー関手は被覆圏上で忠実** — 被覆の
    同変写像はその台写像で決まる（同じ台写像なら同じ射）。M20 の
    ファイバー関手 F（忘却）を有限連続被覆の部分圏に制限した忠実性。
    A-3β-3 の「Aut(F) = π₁ 復元」の土台。 -/
theorem cover_fiber_faithful (X Y : TateCover) (f g : ActHom X.carrier Y.carrier)
    (h : ∀ x, f.map x = g.map x) : f = g :=
  ActHom.ext h

/-! ## M191F-7: A-3β-1（副有限完備化 ẑ）との接続 -/

/-- **副有限レベル射影（M191F-7）**: 副有限完備化 `tateProfinite` = ẑ
    から有限商 ℤ/n への射影（M13 の `limitProj`）。被覆の構造群
    ℤ/n は ẑ の有限商である。 -/
def profiniteLevel (n : Nat) : Hom tateProfinite (zmod n) :=
  limitProj tateFiniteSystem n

/-- **定理 (M191F-7): 被覆の作用はデッキ座標経由でも副有限完備化
    経由でも一致** — 数論的基本群 Π の元 g に対し、レベル n 被覆の
    作用を「デッキ射影 → ℤ/n」で計算しても「副有限完備化 → ℤ/n」で
    計算しても同じ。M188F の `tateCompletion_proj`（錐条件）の被覆圏
    版であり、被覆圏全体が副有限完備化 ẑ を見ていることの形式的内容。 -/
theorem cover_deck_profinite_compat (n : Nat) (X : GAction (zmod n))
    (g : tateCoverGrp.carrier) (x : X.carrier) :
    X.act ((profiniteLevel n).map (tateCompletion.map g)) x
      = X.act ((deckQuot n).map (tateDeckProj.map g)) x :=
  congrArg (fun q => X.act q x) (tateCompletion_proj n g)

/-! ## M191F-8: 総括 -/

/-- **Tate 有限連続被覆圏データ（M191F-8）**: A-3β-2 の成果物の束。
    終対象・始対象・余積（直和）・積を持ち、各操作が有限性と連続性を
    保存し、ファイバー関手が忠実であることを一つに束ねる。
    A-3β-3（GaloisCatData 充足・Aut(F)=π₁ 復元）はこのデータを入力に
    とる。 -/
structure TateCoverCatData where
  /-- 終対象（一点被覆）。 -/
  terminal : TateCover
  /-- 始対象（空被覆）。 -/
  initial : TateCover
  /-- 余積（直和）。 -/
  coprod : TateCover → TateCover → TateCover
  /-- 積（終対象上のファイバー積）。 -/
  prod : TateCover → TateCover → TateCover
  /-- 余積は台有限を保存する。 -/
  coprod_finite : ∀ X Y : TateCover, Finite (coprod X Y).carrier.carrier
  /-- 積は台有限を保存する。 -/
  prod_finite : ∀ X Y : TateCover, Finite (prod X Y).carrier.carrier
  /-- 余積は連続性を保存する。 -/
  coprod_continuous : ∀ X Y : TateCover, ContinuousCover (coprod X Y).carrier
  /-- 積は連続性を保存する。 -/
  prod_continuous : ∀ X Y : TateCover, ContinuousCover (prod X Y).carrier
  /-- ファイバー関手は忠実（同変写像は台写像で決まる）。 -/
  fiber_faithful : ∀ (X Y : TateCover) (f g : ActHom X.carrier Y.carrier),
    (∀ x, f.map x = g.map x) → f = g

/-- **証人（M191F-8）**: 本モジュールの構成が被覆圏データを実際に
    充足する。 -/
def tateCoverCatData : TateCoverCatData where
  terminal := unitCover
  initial := emptyCover
  coprod := sumCover
  prod := prodCover
  coprod_finite := fun X Y => (sumCover X Y).finite
  prod_finite := fun X Y => (prodCover X Y).finite
  coprod_continuous := fun X Y => coverContinuous (sumCover X Y)
  prod_continuous := fun X Y => coverContinuous (prodCover X Y)
  fiber_faithful := cover_fiber_faithful

/-- **定理 (M191F-8): Tate 有限連続被覆圏データの存在** — Tate 曲線の
    有限連続被覆の圏（終始対象・和・ファイバー積・積・忠実な
    ファイバー関手を備える）は無矛盾に存在する。 -/
theorem tateCoverCat_exists : Nonempty TateCoverCatData :=
  ⟨tateCoverCatData⟩

end IUT
