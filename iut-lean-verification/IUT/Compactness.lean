/-
  IUT/Compactness.lean — M18（コンパクト性の一般論）の形式化

  M15 の位相の上にコンパクト性（開被覆の有限部分被覆）を定義し、
  一般論の核心を完全証明する。有限部分族は List で表す:

  * M18-1 `listable_discrete_compact` — 枚挙可能（M17 の Listable）な
    離散空間はコンパクト。「有限 ⟹ コンパクト」の機械検証であり、
    副有限群の各有限レベル（ℤ/n、M17-5b）がコンパクトであることが
    従う（`zmod_compact`）
  * M18-2 `compact_image` — **コンパクト空間の連続像はコンパクト**
  * M18-3 `prod_open_rect_basis` — 直積位相の開集合は各点で開長方形
    近傍を含む（直積版の近傍基定理）
  * M18-4 `compact_prod` — **二項チコノフの定理**: コンパクト空間の
    直積はコンパクト。証明はチューブ補題の管化:
    各 x ∈ α でファイバー {x}×β を長方形被覆し、β のコンパクト性で
    有限化、その「チューブ」たちが α の開被覆をなすので α の
    コンパクト性で有限化する。集合族を述語として非可述的に定義する
    ことで**選択公理を使わずに**管を構成できる（有限個の存在命題の
    分解はすべて Prop ゴールへの分解で済む）

  全て sorry なし・選択公理（Classical.choice）不使用。

  **位置づけ（正直な申告）**: 逆極限のコンパクト性（一般のチコノフ
  または König 補題を要し、本質的に選択原理が入る）は未形式化。
  ẑ については有限レベルへの全射（M15-7、構成的）がその使用面を
  すでに供給している。
-/
import IUT.Topology
import IUT.Finiteness

namespace IUT

/-- コンパクト性: 任意の開被覆が有限（List）部分被覆を持つ。 -/
def Compact {α : Type} (T : Topology α) : Prop :=
  ∀ S : (α → Prop) → Prop,
    (∀ U, S U → T.IsOpen U) →
    (∀ x, ∃ U, S U ∧ U x) →
    ∃ L : List (α → Prop), (∀ U, U ∈ L → S U) ∧ (∀ x, ∃ U, U ∈ L ∧ U x)

/-- **定理 (M18-1): 枚挙可能な離散空間はコンパクト** —
    リストの各要素を覆う開集合を一つずつ集めれば良い
    （Prop ゴールへの有限分解なので選択公理不要）。 -/
theorem listable_discrete_compact {α : Type} (h : Listable α) :
    Compact (discreteTopology α) := by
  intro S _ hcov
  obtain ⟨l, hl⟩ := h
  -- リスト l の要素を覆う有限部分族を帰納法で構成
  have key : ∀ m : List α, ∃ L : List (α → Prop),
      (∀ U, U ∈ L → S U) ∧ (∀ x, x ∈ m → ∃ U, U ∈ L ∧ U x) := by
    intro m
    induction m with
    | nil => exact ⟨[], fun U h => absurd h (List.not_mem_nil), fun x h => absurd h List.not_mem_nil⟩
    | cons a t ih =>
      obtain ⟨L, hLS, hLcov⟩ := ih
      obtain ⟨U, hUS, hUa⟩ := hcov a
      refine ⟨U :: L, ?_, ?_⟩
      · intro V hV
        cases List.mem_cons.mp hV with
        | inl h => exact h ▸ hUS
        | inr h => exact hLS V h
      · intro x hx
        cases List.mem_cons.mp hx with
        | inl h => exact ⟨U, List.mem_cons_self, h ▸ hUa⟩
        | inr h =>
          obtain ⟨V, hVL, hVx⟩ := hLcov x h
          exact ⟨V, List.mem_cons_of_mem U hVL, hVx⟩
  obtain ⟨L, hLS, hLcov⟩ := key l
  exact ⟨L, hLS, fun x => hLcov x (hl x)⟩

/-- ℤ/n はコンパクト（離散位相、M17-5b と M18-1 の合成）。
    M13 の zmodSystem が「コンパクト群の逆系」であることの検証。 -/
theorem zmod_compact (n : Nat) (hn : 0 < n) :
    Compact (discreteTopology (zmod n).carrier) :=
  listable_discrete_compact (zmod_listable n hn)

/-- **定理 (M18-2): コンパクト空間の連続像はコンパクト**。 -/
theorem compact_image {α β : Type} {Tα : Topology α} {Tβ : Topology β}
    (f : α → β) (hf : Continuous Tα Tβ f)
    (hsurj : ∀ y, ∃ x, f x = y) (hcomp : Compact Tα) : Compact Tβ := by
  intro S hSopen hScov
  -- 引き戻し被覆
  obtain ⟨L, hLS, hLcov⟩ := hcomp
    (fun U => ∃ V, S V ∧ U = fun x => V (f x))
    (fun U ⟨V, hV, hUV⟩ => hUV ▸ hf V (hSopen V hV))
    (fun x => by
      obtain ⟨V, hV, hVfx⟩ := hScov (f x)
      exact ⟨fun y => V (f y), ⟨V, hV, rfl⟩, hVfx⟩)
  -- 引き戻しのリストから元の V たちのリストを回収（Prop ゴールへの分解）
  have key : ∀ L' : List (α → Prop),
      (∀ U, U ∈ L' → ∃ V, S V ∧ U = fun x => V (f x)) →
      ∃ M : List (β → Prop), (∀ V, V ∈ M → S V) ∧
        ∀ x U, U ∈ L' → U x → ∃ V, V ∈ M ∧ V (f x) := by
    intro L'
    induction L' with
    | nil => exact fun _ => ⟨[], fun V h => absurd h List.not_mem_nil,
        fun x U h => absurd h List.not_mem_nil⟩
    | cons U t ih =>
      intro hmem
      obtain ⟨M, hMS, hMcov⟩ := ih (fun W hW => hmem W (List.mem_cons_of_mem U hW))
      obtain ⟨V, hVS, hUV⟩ := hmem U List.mem_cons_self
      refine ⟨V :: M, ?_, ?_⟩
      · intro W hW
        cases List.mem_cons.mp hW with
        | inl h => exact h ▸ hVS
        | inr h => exact hMS W h
      · intro x W hW hWx
        cases List.mem_cons.mp hW with
        | inl h =>
          refine ⟨V, List.mem_cons_self, ?_⟩
          rw [h, hUV] at hWx
          exact hWx
        | inr h =>
          obtain ⟨V', hV'M, hV'⟩ := hMcov x W h hWx
          exact ⟨V', List.mem_cons_of_mem V hV'M, hV'⟩
  obtain ⟨M, hMS, hMcov⟩ := key L hLS
  refine ⟨M, hMS, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨U, hUL, hUx⟩ := hLcov x
  exact hMcov x U hUL hUx

/-- **定理 (M18-3): 直積位相の開長方形近傍基** — 直積位相の開集合は
    各点で「開長方形 ⊆ 開集合」を満たす長方形を含む。 -/
theorem prod_open_rect_basis {α β : Type} (Tα : Topology α) (Tβ : Topology β)
    (W : α × β → Prop) (hW : (prodTopology Tα Tβ).IsOpen W) :
    ∀ p, W p → ∃ U V, Tα.IsOpen U ∧ Tβ.IsOpen V ∧ U p.1 ∧ V p.2 ∧
      ∀ q : α × β, U q.1 → V q.2 → W q := by
  induction hW with
  | basic R hR =>
    obtain ⟨U, V, hU, hV, rfl⟩ := hR
    intro p hp
    exact ⟨U, V, hU, hV, hp.1, hp.2, fun q hq1 hq2 => ⟨hq1, hq2⟩⟩
  | univ =>
    intro p _
    exact ⟨fun _ => True, fun _ => True, Tα.isOpen_univ, Tβ.isOpen_univ,
      trivial, trivial, fun _ _ _ => trivial⟩
  | inter W₁ W₂ _ _ ih₁ ih₂ =>
    intro p hp
    obtain ⟨U₁, V₁, hU₁, hV₁, hpU₁, hpV₁, hsub₁⟩ := ih₁ p hp.1
    obtain ⟨U₂, V₂, hU₂, hV₂, hpU₂, hpV₂, hsub₂⟩ := ih₂ p hp.2
    exact ⟨fun a => U₁ a ∧ U₂ a, fun b => V₁ b ∧ V₂ b,
      Tα.isOpen_inter hU₁ hU₂, Tβ.isOpen_inter hV₁ hV₂,
      ⟨hpU₁, hpU₂⟩, ⟨hpV₁, hpV₂⟩,
      fun q hq1 hq2 => ⟨hsub₁ q hq1.1 hq2.1, hsub₂ q hq1.2 hq2.2⟩⟩
  | sUnion T _ ih =>
    intro p hp
    obtain ⟨W₀, hW₀, hW₀p⟩ := hp
    obtain ⟨U, V, hU, hV, hpU, hpV, hsub⟩ := ih W₀ hW₀ p hW₀p
    exact ⟨U, V, hU, hV, hpU, hpV, fun q hq1 hq2 => ⟨W₀, hW₀, hsub q hq1 hq2⟩⟩

/-- チューブの抽出（補題）: ファイバー {x}×β の有限長方形被覆から、
    x の開近傍 U（チューブの底）と被覆メンバーの有限リストを取り出す。
    リストに沿った Prop ゴールへの分解なので選択公理不要。 -/
theorem tube_extract {α β : Type} (Tα : Topology α) (Tβ : Topology β)
    (S : (α × β → Prop) → Prop) (x : α) :
    ∀ LV : List (β → Prop),
      (∀ V, V ∈ LV → ∃ U, Tα.IsOpen U ∧ U x ∧
        ∃ W, S W ∧ ∀ a b, U a → V b → W (a, b)) →
      ∃ U : α → Prop, Tα.IsOpen U ∧ U x ∧
        ∃ LW : List (α × β → Prop), (∀ W, W ∈ LW → S W) ∧
          ∀ a b, U a → (∃ V, V ∈ LV ∧ V b) → ∃ W, W ∈ LW ∧ W (a, b) := by
  intro LV
  induction LV with
  | nil =>
    intro _
    exact ⟨fun _ => True, Tα.isOpen_univ, trivial, [],
      fun W h => absurd h List.not_mem_nil,
      fun a b _ ⟨V, hV, _⟩ => absurd hV List.not_mem_nil⟩
  | cons V t ih =>
    intro hmem
    obtain ⟨U₀, hU₀, hU₀x, W₀, hW₀S, hW₀⟩ := hmem V List.mem_cons_self
    obtain ⟨U₁, hU₁, hU₁x, LW, hLWS, hLW⟩ :=
      ih (fun V' hV' => hmem V' (List.mem_cons_of_mem V hV'))
    refine ⟨fun a => U₀ a ∧ U₁ a, Tα.isOpen_inter hU₀ hU₁, ⟨hU₀x, hU₁x⟩,
      W₀ :: LW, ?_, ?_⟩
    · intro W hW
      cases List.mem_cons.mp hW with
      | inl h => exact h ▸ hW₀S
      | inr h => exact hLWS W h
    · intro a b ha hVb
      obtain ⟨V', hV', hV'b⟩ := hVb
      cases List.mem_cons.mp hV' with
      | inl h =>
        exact ⟨W₀, List.mem_cons_self, hW₀ a b ha.1 (h ▸ hV'b)⟩
      | inr h =>
        obtain ⟨W, hWmem, hWab⟩ := hLW a b ha.2 ⟨V', h, hV'b⟩
        exact ⟨W, List.mem_cons_of_mem W₀ hWmem, hWab⟩

/-- チューブの集約（補題）: チューブ被覆の有限リストから全体の
    有限部分被覆を集める。 -/
theorem tube_collect {α β : Type}
    (S : (α × β → Prop) → Prop) :
    ∀ LU : List (α → Prop),
      (∀ U, U ∈ LU → ∃ LW : List (α × β → Prop),
        (∀ W, W ∈ LW → S W) ∧ ∀ a b, U a → ∃ W, W ∈ LW ∧ W (a, b)) →
      ∃ LW : List (α × β → Prop), (∀ W, W ∈ LW → S W) ∧
        ∀ a b, (∃ U, U ∈ LU ∧ U a) → ∃ W, W ∈ LW ∧ W (a, b) := by
  intro LU
  induction LU with
  | nil =>
    intro _
    exact ⟨[], fun W h => absurd h List.not_mem_nil,
      fun a b ⟨U, hU, _⟩ => absurd hU List.not_mem_nil⟩
  | cons U t ih =>
    intro hmem
    obtain ⟨LW₀, hLW₀S, hLW₀⟩ := hmem U List.mem_cons_self
    obtain ⟨LW₁, hLW₁S, hLW₁⟩ :=
      ih (fun U' hU' => hmem U' (List.mem_cons_of_mem U hU'))
    refine ⟨LW₀ ++ LW₁, ?_, ?_⟩
    · intro W hW
      cases List.mem_append.mp hW with
      | inl h => exact hLW₀S W h
      | inr h => exact hLW₁S W h
    · intro a b hUa
      obtain ⟨U', hU', hU'a⟩ := hUa
      cases List.mem_cons.mp hU' with
      | inl h =>
        obtain ⟨W, hWmem, hWab⟩ := hLW₀ a b (h ▸ hU'a)
        exact ⟨W, List.mem_append.mpr (Or.inl hWmem), hWab⟩
      | inr h =>
        obtain ⟨W, hWmem, hWab⟩ := hLW₁ a b ⟨U', h, hU'a⟩
        exact ⟨W, List.mem_append.mpr (Or.inr hWmem), hWab⟩

/-- **定理 (M18-4): 二項チコノフ** — コンパクト空間の直積は
    コンパクト。チューブ補題による古典的証明の機械化
    （集合族を述語として非可述的に定義することで選択公理を回避）。 -/
theorem compact_prod {α β : Type} {Tα : Topology α} {Tβ : Topology β}
    (hα : Compact Tα) (hβ : Compact Tβ) :
    Compact (prodTopology Tα Tβ) := by
  intro S hSopen hScov
  -- チューブの底の族: 「その上のチューブが S の有限員で覆える」開集合
  have htube : ∀ x : α, ∃ U : α → Prop, Tα.IsOpen U ∧ U x ∧
      ∃ LW : List (α × β → Prop), (∀ W, W ∈ LW → S W) ∧
        ∀ a b, U a → ∃ W, W ∈ LW ∧ W (a, b) := by
    intro x
    -- ファイバー {x}×β を β の開被覆に変換
    obtain ⟨LV, hLVS, hLVcov⟩ := hβ
      (fun V => Tβ.IsOpen V ∧ ∃ U, Tα.IsOpen U ∧ U x ∧
        ∃ W, S W ∧ ∀ a b, U a → V b → W (a, b))
      (fun V hV => hV.1)
      (fun y => by
        obtain ⟨W, hWS, hWxy⟩ := hScov (x, y)
        obtain ⟨U, V, hU, hV, hxU, hyV, hsub⟩ :=
          prod_open_rect_basis Tα Tβ W (hSopen W hWS) (x, y) hWxy
        exact ⟨V, ⟨hV, U, hU, hxU, W, hWS, fun a b ha hb => hsub (a, b) ha hb⟩, hyV⟩)
    obtain ⟨U, hUopen, hUx, LW, hLWS, hLW⟩ :=
      tube_extract Tα Tβ S x LV (fun V hV => (hLVS V hV).2)
    refine ⟨U, hUopen, hUx, LW, hLWS, fun a b ha => ?_⟩
    exact hLW a b ha (hLVcov b)
  -- チューブの底たちは α の開被覆: α のコンパクト性で有限化
  obtain ⟨LU, hLUS, hLUcov⟩ := hα
    (fun U => Tα.IsOpen U ∧ ∃ LW : List (α × β → Prop),
      (∀ W, W ∈ LW → S W) ∧ ∀ a b, U a → ∃ W, W ∈ LW ∧ W (a, b))
    (fun U hU => hU.1)
    (fun x => by
      obtain ⟨U, hUopen, hUx, hrest⟩ := htube x
      exact ⟨U, ⟨hUopen, hrest⟩, hUx⟩)
  obtain ⟨LW, hLWS, hLWcov⟩ := tube_collect S LU (fun U hU => (hLUS U hU).2)
  refine ⟨LW, hLWS, fun p => ?_⟩
  obtain ⟨W, hWmem, hWp⟩ := hLWcov p.1 p.2 (hLUcov p.1)
  exact ⟨W, hWmem, hWp⟩

end IUT
