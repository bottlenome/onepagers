/-
  IUT/CyclotomicSurj39.lean — A3/CS39（res₁ の全射性 `cr39_surjective`:
  res: Gal(ℚ(ζ₉)/ℚ) → Gal(ℚ(ζ₃)/ℚ) が全射であることの本物の証明）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・
     実 2 段円分塔 ℚ(ζ₃) ⊂ ℚ(ζ₉) の上での制限準同型 res の**全射性の本物の証明**。
     CG9 で本物構成した σ₂ = cg9Aut 2 5（x̄₉ ↦ x̄₉²）を用い、cr39Char σ₂ = 2
     ⟹ 2 % 3 = 2 ≠ 1 ⟹ res σ₂ = cg3Conj を示し、CG3 の位数 2（`cg3_galois_order_two`）
     二分で τ = id（σ = id）・τ = cg3Conj（σ = σ₂）と全射性を完全証明する）。

  complete_pct 影響: A3——res₁ 全射性で「2 段塔の Gal 構造完全把握」
  （短完全列 1 → ker → Gal₉ → Gal₃ → 1 の実質）を閉じ、監査残欠 (ii) を解消。
  ただし設計 §1.2 の通り単段では丸めで柱%据え置きの可能性大（A3 0.6 → 0.6〜0.62・
  柱A% 38.2）——過大主張せず正直に。本ファイル単体では complete_pct 未設定
  （独立監査で判定）。

  内容（設計 audit/A3-inverse-limit-roadmap-2026-07-09.md §1.1）:
   * `cs39Sigma2`/`cs39Sigma2_mem` — σ₂ = cg9Aut 2 5（2·5 ≡ 1 mod 9）と Galois 所属。
   * `cs39_char_sigma2` — cr39Char σ₂ = 2（σ₂ x̄₉ = x̄₉² ⟹ cm9Find(x̄₉²) = 2・
     cr39_char_spec ＋ cm9_powers_distinct の対偶）。
   * `cs39_res_sigma2` — res σ₂ = cg3Conj（2 % 3 ≠ 1 の if_neg）。
   * `cs39_conj_is_g` — cg3_galois_order_two の非自明元 g は ⟨cg3Conj, cg3Conj_mem⟩。
   * `cr39_surjective`（本丸） — res₁ は全射。仮説 0 本。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・ℚ 上・2 段（ℚ(ζ₃) ⊂ ℚ(ζ₉)）のみの忠実な部分ケース。
   (ii)  **無限塔・逆極限 G_K は未達**（本ファイルは res₁ 単段の全射性まで）。
   (iii) **群同型 Gal(ℚ(ζ₉)/ℚ) ≅ (ℤ/9)^× は未証明**（CG9 と同様「位数 6」・
         「全射性」まで。res₁ の核が位数 3 の巡回群であること等の完全な短完全列
         同型は未形式化）。
   (iv)  分離性・正規性の一般論も未形式化。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/
  dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.CyclotomicGal9
import IUT.CyclotomicGal3

namespace IUT

/-! ## CS39-1: σ₂ = cg9Aut 2 5（x̄₉ ↦ x̄₉²）と Galois 所属 -/

/-- **σ₂** — 指標 a = 2 の冪代入自己同型 x̄₉ ↦ x̄₉²（逆元 witness 5・2·5 ≡ 1 mod 9）。 -/
def cs39Sigma2 : FieldAut p9iPhi9Field := cg9Aut 2 5 cg9nd2 cg9nd5 rfl

/-- **σ₂ ∈ Gal(ℚ(ζ₉)/ℚ)**（ℚ 各点固定）。 -/
theorem cs39Sigma2_mem : (galoisSubgroup p9iExt9).mem cs39Sigma2 :=
  cg9Aut_mem 2 5 cg9nd2 cg9nd5 rfl

/-! ## CS39-2: 指標 cr39Char σ₂ = 2 -/

/-- **cr39Char σ₂ = 2** — σ₂(x̄₉) = x̄₉²（`cg9_subst_zeta`）と cr39Char の特徴付け
    `cr39_char_spec`（σ₂ x̄₉ = x̄₉^{cr39Char σ₂}）から cm9Pow 2 = cm9Pow (cr39Char σ₂)。
    両指数 < 9・`cm9_powers_distinct` の対偶で一致。choice 不要。 -/
theorem cs39_char_sigma2 : cr39Char cs39Sigma2 = 2 := by
  have hz : cs39Sigma2.toFun cm9Zeta = cm9Pow 2 := by
    show cg9Subst 2 cm9Zeta = cm9Pow 2
    exact cg9_subst_zeta 2
  have hspec : cs39Sigma2.toFun cm9Zeta = cm9Pow (cr39Char cs39Sigma2) :=
    cr39_char_spec cs39Sigma2
  have heq : cm9Pow 2 = cm9Pow (cr39Char cs39Sigma2) := by rw [← hz, hspec]
  have hlt : cr39Char cs39Sigma2 < 9 := cr39_char_lt cs39Sigma2
  cases Nat.decEq (cr39Char cs39Sigma2) 2 with
  | isTrue h => exact h
  | isFalse h =>
    exact absurd heq
      (cm9_powers_distinct 2 (cr39Char cs39Sigma2) (by omega) hlt (fun he => h he.symm))

/-! ## CS39-3: res σ₂ = cg3Conj -/

/-- **指標 2 ⟹ res = cg3Conj**（σ 抽象）— cr39Char σ = 2 ⟹ 2 % 3 = 2 ≠ 1 ⟹
    res σ = cg3Conj。σ を抽象に保ち concrete 評価を避ける（cr39Res の delta 展開のみ）。 -/
theorem cs39_res_of_char2 (σ : FieldAut p9iPhi9Field) (h : cr39Char σ = 2) :
    cr39Res σ = cg3Conj := by
  show (if cr39Char σ % 3 = 1 then fieldAutId cnfPhi3Field else cg3Conj) = cg3Conj
  rw [h, if_neg (show ¬ (2 % 3 = 1) by omega)]

/-- **res の Hom projection**（x 抽象）— `(cr39ResHom.map x).val = cr39Res x.val`。
    x を抽象に保つことで rfl は射影 β のみで済み concrete NF 評価を誘発しない。 -/
theorem cs39_resHom_val (x : (galoisGroupGrp p9iExt9).carrier) :
    (cr39ResHom.map x).val = cr39Res x.val := rfl

/-- **res σ₂ = cg3Conj** — cr39Char σ₂ = 2 ⟹ 2 % 3 = 2 ≠ 1 ⟹ res σ₂ = cg3Conj。 -/
theorem cs39_res_sigma2 :
    (cr39ResHom.map ⟨cs39Sigma2, cs39Sigma2_mem⟩).val = cg3Conj := by
  rw [cs39_resHom_val ⟨cs39Sigma2, cs39Sigma2_mem⟩]
  exact cs39_res_of_char2 cs39Sigma2 cs39_char_sigma2

/-! ## CS39-4: 非自明元の同定 -/

/-- **cg3_galois_order_two の g は共役** — 位数 2 の二分 ∀h を h := ⟨cg3Conj, cg3Conj_mem⟩
    に適用し、h = one 枝を cg3Conj ≠ id（`cg3Conj_ne_id`）で潰す。 -/
theorem cs39_conj_is_g
    (g : (galoisGroupGrp cnfExt3).carrier)
    (hall : ∀ h : (galoisGroupGrp cnfExt3).carrier,
        h = (galoisGroupGrp cnfExt3).one ∨ h = g) :
    (⟨cg3Conj, cg3Conj_mem⟩ : (galoisGroupGrp cnfExt3).carrier) = g := by
  cases hall ⟨cg3Conj, cg3Conj_mem⟩ with
  | inl h =>
    exfalso
    have hc : cg3Conj = fieldAutId cnfPhi3Field := congrArg Subtype.val h
    exact cg3Conj_ne_id hc
  | inr h => exact h

/-! ## CS39-5: capstone — res₁ の全射性 -/

/-- **res₁ は全射（本丸）** — 任意の τ ∈ Gal(ℚ(ζ₃)/ℚ) に σ ∈ Gal(ℚ(ζ₉)/ℚ) で
    res σ = τ。`cg3_galois_order_two` の二分: τ = one → σ := one（`Hom.map_one`）・
    τ = g = ⟨cg3Conj,…⟩ → σ := ⟨σ₂,…⟩（`cs39_res_sigma2`・`cs39_conj_is_g`）。
    仮説 0 本。 -/
theorem cr39_surjective :
    ∀ τ : (galoisGroupGrp cnfExt3).carrier,
      ∃ σ : (galoisGroupGrp p9iExt9).carrier, cr39ResHom.map σ = τ := by
  intro τ
  obtain ⟨g, _hg_ne, hall⟩ := cg3_galois_order_two
  cases hall τ with
  | inl hone =>
    refine ⟨(galoisGroupGrp p9iExt9).one, ?_⟩
    rw [hone]
    exact Hom.map_one cr39ResHom
  | inr hgeq =>
    refine ⟨⟨cs39Sigma2, cs39Sigma2_mem⟩, ?_⟩
    rw [hgeq]
    apply Subtype.ext
    rw [cs39_res_sigma2]
    exact congrArg Subtype.val (cs39_conj_is_g g hall)

end IUT
