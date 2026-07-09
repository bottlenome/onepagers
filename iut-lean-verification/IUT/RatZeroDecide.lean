/-
  IUT/RatZeroDecide.lean — N2: ℚ の構成的零判定（choice-free）— 柱C ℝ 基盤

  二軸: [実] ／ complete_pct: 実 ℚ 上で「零判定選言 x = 0 ∨ x ≠ 0」を
  **排中律なし**（Int の DecidableEq = `Int.decEq`）で構成し、`Field.lean` の
  正直申告（抽象体は零判定に Classical.choice を要する）を **実 ℚ に限り解消**する
  小さな昇格の部品。抽象体の選言形は依然 choice を要するが、実 ℚ の代表 num の
  DecidableEq で場合分けできるため構成的に取れる。

  * N2-1 `rzd_zero_or_ne` — `∀ x : QRat, x = ratRing.zero ∨ x ≠ ratRing.zero`。
    `Quot.ind` で代表 r を取り、`Decidable.em (r.num = 0)`（Int の決定手続き
    `Int.decEq`、choice-free）で場合分け:
      - r.num = 0 → `Quot.sound`（交差積 r.num·1 = 0·r.den、omega）で x = 0。
      - r.num ≠ 0 → 仮に x = 0 なら `quot_exact_rat` で r.num·1 = 0·r.den ⟹
        r.num = 0（omega）で矛盾。
  * N2-2 `rzd_ne_zero_of_num_ne` — 代表の num ≠ 0 ⟹ x ≠ 0（後続 Wave 便利形）。
  * N2-3 `rzd_eq_zero_iff` — x = 0 ⟺ 代表 num = 0。

  設計: audit/A1-real-numberfield-plan.md §2.3。`Rationals.lean` の `prInv`
  （`if hz : x.num = 0`）・`ratRel_inv` の `Decidable.em` と同じイディオム。
  新規 axiom なし・新規 Classical.choice なし（`#print axioms` = [propext, Quot.sound]）。
-/
import IUT.Rationals

namespace IUT

/-- **N2-1: ℚ の構成的零判定** — 実 ℚ では代表 num の DecidableEq
    （`Int.decEq`、choice-free）で選言 x = 0 ∨ x ≠ 0 が取れる。
    抽象体では排中律を要する（`Field.lean` 正直申告）が、実 ℚ で解消。 -/
theorem rzd_zero_or_ne : ∀ x : QRat, x = ratRing.zero ∨ x ≠ ratRing.zero := by
  intro x
  induction x using Quot.ind
  rename_i r
  cases Decidable.em (r.num = 0) with
  | inl hz =>
    apply Or.inl
    apply Quot.sound
    show r.num * (1 : Int) = 0 * r.den
    omega
  | inr hz =>
    apply Or.inr
    intro h
    have hrel : ratRel r prZero := quot_exact_rat h
    have he : r.num * (1 : Int) = 0 * r.den := hrel
    exact hz (by omega)

/-- **N2-2: 便利形** — 代表の num ≠ 0 ならその ℚ 元は零でない
    （逆元・次数降下で非零性を代表から引き上げる後続 Wave 用）。 -/
theorem rzd_ne_zero_of_num_ne {r : PreRat} (h : r.num ≠ 0) :
    Quot.mk ratRel r ≠ ratRing.zero := by
  intro he
  have hrel : ratRel r prZero := quot_exact_rat he
  have h1 : r.num * (1 : Int) = 0 * r.den := hrel
  exact h (by omega)

/-- **N2-3: 判定の同値形** — ℚ 元が零 ⟺ 代表の num = 0。 -/
theorem rzd_eq_zero_iff (r : PreRat) :
    Quot.mk ratRel r = ratRing.zero ↔ r.num = 0 := by
  apply Iff.intro
  · intro he
    have hrel : ratRel r prZero := quot_exact_rat he
    have h1 : r.num * (1 : Int) = 0 * r.den := hrel
    omega
  · intro hz
    apply Quot.sound
    show r.num * (1 : Int) = 0 * r.den
    omega

end IUT
