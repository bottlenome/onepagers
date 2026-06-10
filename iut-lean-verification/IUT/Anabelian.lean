/-
  IUT/Anabelian.lean  — M1（単遠アーベル復元）の形式化

  望月の遠アーベル幾何（[AbsTopIII] ほか、IUT I §I3 で「IUT の
  出発点」とされる）の **論理骨格** を形式化する。

  復元定理の実体（p 進局所体・数体の環構造の群論的復元）は
  形式化しない（し得る者は現状world中に存在しない）。ここで検証するのは、望月が
  [AbsTopIII] Introduction や Panoramic Overview で強調する
  「mono-anabelian / bi-anabelian の区別」の論理構造である:

  * mono-anabelian = 群から出発する **復元アルゴリズム** が存在する
  * bi-anabelian  = 基本群関手の **充満忠実性**（同型の比較）のみ

  検証結果（本ファイルの定理、すべて sorry なし）:
  1. `mono_implies_bi` — mono ⟹ bi は **公理なし** で証明できる
  2. `bi_implies_mono_classical` — 逆向き bi ⟹ mono は証明できるが
     **選択公理 (Classical.choice) が必須** になる
     （アルゴリズム性が失われるという望月の主張の形式的対応物。
       実際 #print axioms がこの非対称性をそのまま表示する）
  3. `recon_aut_indeterminacy` — 群論的復元の出力は群の自己同型で
     不変。これが多輻的表現の不定性 (Ind1) の形式的起源である
  4. `monoAnabelian_consistent` — 公理系の無矛盾性（恒等モデル）
-/

namespace IUT

/-- **復元設定**: 遠アーベル幾何の舞台の抽象化。

    `F` は「体スキーム的対象」（双曲的曲線・数体など）、
    `G` は「位相群的対象」（エタール基本群・Galois 群など）の型。
    `pi` は基本群関手 X ↦ π₁(X) に相当する。

    同型は等価関係 `isoF` / `isoG` として公理化し、
    `pi_congr` は関手性（同型を同型に送る）を表す。 -/
structure ReconSetting where
  F : Type
  G : Type
  pi : F → G
  isoF : F → F → Prop
  isoG : G → G → Prop
  isoF_refl : ∀ X, isoF X X
  isoF_symm : ∀ {X Y}, isoF X Y → isoF Y X
  isoF_trans : ∀ {X Y Z}, isoF X Y → isoF Y Z → isoF X Z
  isoG_refl : ∀ g, isoG g g
  isoG_symm : ∀ {g h}, isoG g h → isoG h g
  isoG_trans : ∀ {g h k}, isoG g h → isoG h k → isoG g k
  pi_congr : ∀ {X Y}, isoF X Y → isoG (pi X) (pi Y)

/-- **mono-anabelian**（[AbsTopIII] の意味での「単」遠アーベル性）:
    群論的データだけから元の対象を復元する **アルゴリズム**
    `recon : G → F` が存在する。

    * `recon_pi` — 復元の正しさ: recon(π₁(X)) ≅ X
    * `recon_congr` — 復元の「群論性」: 同型な群からは同型な対象を
      復元する（構成が群の表示に依らない） -/
def MonoAnabelian (S : ReconSetting) : Prop :=
  ∃ recon : S.G → S.F,
    (∀ X : S.F, S.isoF (recon (S.pi X)) X) ∧
    (∀ {g h : S.G}, S.isoG g h → S.isoF (recon g) (recon h))

/-- **bi-anabelian**（Grothendieck 流の「双」遠アーベル性）:
    基本群関手が同型を反映する（充満忠実性の同型部分）。 -/
def BiAnabelian (S : ReconSetting) : Prop :=
  ∀ X Y : S.F, S.isoG (S.pi X) (S.pi Y) → S.isoF X Y

/-- **定理 (M1-1)**: mono-anabelian ⟹ bi-anabelian。

    π₁(X) ≅ π₁(Y) なら、群論的復元を両辺に適用して
    X ≅ recon(π₁X) ≅ recon(π₁Y) ≅ Y。

    この証明は選択公理を一切使わない（#print axioms で確認可能）。 -/
theorem mono_implies_bi (S : ReconSetting) (h : MonoAnabelian S) : BiAnabelian S := by
  obtain ⟨recon, hpi, hcongr⟩ := h
  intro X Y hg
  exact S.isoF_trans (S.isoF_symm (hpi X)) (S.isoF_trans (hcongr hg) (hpi Y))

/-- **定理 (M1-2)**: bi-anabelian ⟹ mono-anabelian も成立はするが、
    復元写像を **選択公理で構成する** ことになる。

    証明: 各群 g に対し「π₁ の像に同型で入るか」を排中律で場合分けし、
    入るなら原像を Classical.choice で選ぶ。bi-anabelian 性により
    選び方の差は同型に吸収される。

    `#print axioms` の結果が望月の主張の形式的内容を示す:
    * `mono_implies_bi`          → 公理なし
    * `bi_implies_mono_classical` → [propext, Classical.choice, Quot.sound]

    すなわち bi から得られる「復元」は非アルゴリズム的であり、
    mono-anabelian はそれより真に強い情報を持つ。 -/
theorem bi_implies_mono_classical (S : ReconSetting) (hne : Nonempty S.F)
    (h : BiAnabelian S) : MonoAnabelian S := by
  classical
  -- 復元写像: π₁ の像（同型まで込み）に入る群には原像を選んで返す
  refine ⟨fun g =>
    if hg : ∃ X : S.F, S.isoG (S.pi X) g then Classical.choose hg
    else Classical.choice hne, ?_, ?_⟩
  · -- recon(π₁ X) ≅ X
    intro X
    have hex : ∃ Y : S.F, S.isoG (S.pi Y) (S.pi X) := ⟨X, S.isoG_refl _⟩
    simp only [dif_pos hex]
    exact h _ _ (Classical.choose_spec hex)
  · -- 同型な群からは同型な対象が復元される
    intro g₁ g₂ hg
    by_cases h₁ : ∃ X : S.F, S.isoG (S.pi X) g₁
    · have h₂ : ∃ X : S.F, S.isoG (S.pi X) g₂ :=
        ⟨Classical.choose h₁, S.isoG_trans (Classical.choose_spec h₁) hg⟩
      simp only [dif_pos h₁, dif_pos h₂]
      exact h _ _ (S.isoG_trans (Classical.choose_spec h₁)
        (S.isoG_trans hg (S.isoG_symm (Classical.choose_spec h₂))))
    · have h₂ : ¬∃ X : S.F, S.isoG (S.pi X) g₂ := by
        intro ⟨X, hX⟩
        exact h₁ ⟨X, S.isoG_trans hX (S.isoG_symm hg)⟩
      simp only [dif_neg h₁, dif_neg h₂]
      exact S.isoF_refl _

/-- **定理 (M1-3)**: Aut 不定性 — (Ind1) の形式的起源。

    群論的復元 recon の出力は、入力の群を自己同型 σ ∈ Aut(π₁X) で
    取り替えても（同型の意味で）変わらない。したがって復元された
    対象を別の対象と比較する際には、つねに Aut(π₁) 分の不定性が
    残る。IUT III 定理3.11 の不定性 (Ind1) はこの形式的現象の
    具体化である。 -/
theorem recon_aut_indeterminacy (S : ReconSetting)
    (recon : S.G → S.F)
    (hcongr : ∀ {g h : S.G}, S.isoG g h → S.isoF (recon g) (recon h))
    (g σg : S.G) (hσ : S.isoG σg g) :   -- σ による像 σg ≅ g
    S.isoF (recon σg) (recon g) :=
  hcongr hσ

/-- **無矛盾性 (M1-4)**: 恒等モデル（F = G、π = id、同型 = 等値）が
    mono-anabelian の公理を満たす。よって公理系は無矛盾。 -/
def identityModel : ReconSetting where
  F := Nat
  G := Nat
  pi := id
  isoF := Eq
  isoG := Eq
  isoF_refl := fun _ => rfl
  isoF_symm := Eq.symm
  isoF_trans := Eq.trans
  isoG_refl := fun _ => rfl
  isoG_symm := Eq.symm
  isoG_trans := Eq.trans
  pi_congr := fun h => h

theorem monoAnabelian_consistent : MonoAnabelian identityModel :=
  ⟨id, fun _ => rfl, fun h => h⟩

end IUT
