/-
  IUT/Boolean.lean

  「Essential Logical Structure of IUT」(望月, 2024) の中心表示

      A ∧ B = A ∧ (B₁ ∨̇ B₂ ∨̇ …) ⟹ A ∧ (B₁ ∨̇ … ∨̇ B′₁ ∨̇ …)

  の命題論理としての検証。ここで
  * A は Θ-リンクのコドメイン側（q-パイロット側）の主張
  * B は ドメイン側（Θ-パイロット側）の主張
  * ∨̇ は排他的論理和 XOR（不定性 Ind1–Ind3 による選択肢の分岐）
  を表す（同 PDF, Abstract）。

  検証結果:
  1. 包含的 OR への弱化は無条件に妥当（`and_or_weakening`）
  2. XOR 連鎖への弱化は **一般には不成立**（`xor_weakening_fails`）
  3. 追加選択肢が偽であることが分かっている場合に限り妥当
     （`xor_weakening_of_not`）
  4. RC 同一視は A ∧ B を A ∧ A に退化させ、論理積の情報を失わせる
     （`and_self_collapse`）— 望月が「同一視は論理構造を無効化する」
     と主張する箇所の形式的対応物

  つまり望月の表示が文字通り XOR で意図されているなら、
  弱化のステップには「新たに付け加わる選択肢と既存の選択肢が
  両立しない」ことの証明が別途必要であり、それは命題論理の
  外側（定理3.11 の内容）に属する。
-/

namespace IUT

/-- 排他的論理和。 -/
def Xor' (a b : Prop) : Prop := (a ∧ ¬b) ∨ (¬a ∧ b)

/-- 3 つの命題のうち「ちょうど 1 つ」が成り立つ。
    不定性による選択肢の分岐（どれか 1 つが実現するが
    どれかは特定できない）の形式化。 -/
def ExactlyOne₃ (a b c : Prop) : Prop :=
  (a ∧ ¬b ∧ ¬c) ∨ (¬a ∧ b ∧ ¬c) ∨ (¬a ∧ ¬b ∧ c)

/-- (1) 包含的 OR への弱化は命題論理として無条件に妥当。 -/
theorem and_or_weakening (A B C : Prop) (h : A ∧ B) : A ∧ (B ∨ C) :=
  ⟨h.1, Or.inl h.2⟩

/-- (2) XOR 連鎖への弱化は一般には不成立。
    反例: B₁ = True, B₂ = False, B₃ = True のとき
    Xor' B₁ B₂ は真だが Xor' (Xor' B₁ B₂) B₃ は偽。 -/
theorem xor_weakening_fails :
    ¬(∀ B₁ B₂ B₃ : Prop, Xor' B₁ B₂ → Xor' (Xor' B₁ B₂) B₃) := by
  intro h
  have h12 : Xor' True False := Or.inl ⟨trivial, not_false⟩
  have := h True False True h12
  rcases this with ⟨_, hnt⟩ | ⟨hn12, _⟩
  · exact hnt trivial
  · exact hn12 h12

/-- (3) 追加選択肢が偽なら XOR 弱化は妥当。
    「ちょうど 1 つ」の意味でも同様（`exactlyOne_extend`）。 -/
theorem xor_weakening_of_not (B₁ B₂ B₃ : Prop)
    (h : Xor' B₁ B₂) (h3 : ¬B₃) : Xor' (Xor' B₁ B₂) B₃ :=
  Or.inl ⟨h, h3⟩

/-- (3') ちょうど 1 つが成り立つ 2 択に、偽と分かっている選択肢を
    付け加えても「ちょうど 1 つ」は保たれる。 -/
theorem exactlyOne_extend (B₁ B₂ B₃ : Prop)
    (h : Xor' B₁ B₂) (h3 : ¬B₃) : ExactlyOne₃ B₁ B₂ B₃ := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)

/-- (4) RC 同一視による退化: 両側の主張を同じ命題 A に
    同一視してしまうと、論理積 A ∧ A は単なる A に潰れ、
    「2 つの独立な構造を同時に保持する」という Θ-リンクの
    論理的内容（∧ の意義）が消失する。 -/
theorem and_self_collapse (A : Prop) : (A ∧ A) ↔ A :=
  ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

end IUT
