/-
  IUT/PolyLeadOracleQ.lean — 実 ℚ 上の先頭係数探索オラクル充填
  （PolyBezoutQ の `hlead_oracle` を実 ℚ = `ratRing` で choice-free に討つ）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無・模型なし）。

  **complete_pct 影響**: 柱A「実 Galois 理論／実 π₁^ét」の本物の先行建設。
  `PolyBezoutQ.lean`（M270F）の拡張ユークリッド互除法 `pbzExtGcdAux` /
  `pbzBezout` は「剰余多項式の先頭係数の位置を見つける（または零判定する）
  オラクル」 `hlead_oracle` を honest 仮説として受け取っていた。抽象
  `Field268` 上では等号判定が無いため一般には成立しないが、**実体 ℚ
  （`ratRing`）では真**——本層はまさにその充足を、実 ℚ の構成的零判定
  `rzd_zero_or_ne`（`RatZeroDecide.lean` N2・choice-free）を用いて
  **排中律なし**に構成する。これにより一般 f の ℚ[x]/(f) 実体化で
  `pbzBezout` を（honest 仮説なしで）呼べる形の鍵の一つが埋まる。

  * PLO-1 `plo_lead_oracle_Q` — `∀ (p : PS ratRing) (n : Nat),
      IsPolyBounded ratRing p n →
      (∀ i, p i = ratRing.zero) ∨
      (∃ d, p d ≠ ratRing.zero ∧ IsPolyBounded ratRing p (d + 1))`。
    `pbzExtGcdAux` / `pbzBezout` の `hlead_oracle` 引数を R = `ratRing`
    で充填した形（総称オラクル型と一致するので `pbzBezout ratRing …
    plo_lead_oracle_Q …` に直接渡せる）。
    証明: 有界上界 n に関する帰納で下向き有限探索。
      - n = 0: `IsPolyBounded p 0` は `∀ i, 0 ≤ i → p i = 0`、0 ≤ i は常真
        なので `∀ i, p i = 0`（左枝）。
      - n = m+1: 係数 `p m` を `rzd_zero_or_ne`（実 ℚ 構成的零判定）で
        零判定。`p m ≠ 0` なら右枝（d := m、有界性 hb : bound (m+1) を
        そのまま渡す）。`p m = 0` なら `ppu_bound_drop`（頂点係数 0 での
        上界一段降下、`PolyPSUtil.lean` N3-2）で `IsPolyBounded p m` を得、
        帰納法 ih に渡してその選言をそのまま返す。

  正直な限定: 本層が充足するのは **実 ℚ（`ratRing`）に限った**先頭係数
  探索であり、抽象 `Field268` 上のオラクルは依然 honest 仮説として残る
  （`Field.lean` 正直申告どおり、抽象体の等号判定は排中律を要する）。
  探索は有界上界 n を fuel とする有限降下であり、`rzd_zero_or_ne` の
  分子零判定（`Int.decEq`、choice-free）を各段で使うため、探索全体も
  choice-free（新規 Classical.choice なし）。complete_pct は未設定
  （本層はグラフメタ不更新）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyPSUtil
import IUT.RatZeroDecide

namespace IUT

/-! ## PLO-1: 実 ℚ 上の先頭係数探索オラクル（choice-free） -/

/-- **定理 (PLO-1): 実 ℚ の先頭係数探索オラクル** — 有界な係数列 p
    （`IsPolyBounded ratRing p n`）は、全係数が零であるか、さもなくば
    非零な最上位係数 `p d ≠ 0` を（かつ p が d+1 で有界であることと共に）
    持つ。実 ℚ の構成的零判定 `rzd_zero_or_ne` を各段で使い、有界上界 n を
    fuel とする下向き有限探索で **排中律なし**に決定する。これが
    `PolyBezoutQ` の拡張ユークリッド `pbzExtGcdAux` / `pbzBezout` の
    honest 仮説 `hlead_oracle`（総称 R 版）を R = `ratRing` で充填する形。 -/
theorem plo_lead_oracle_Q : ∀ (p : PS ratRing) (n : Nat),
    IsPolyBounded ratRing p n →
    (∀ i, p i = ratRing.zero) ∨
    (∃ d, p d ≠ ratRing.zero ∧ IsPolyBounded ratRing p (d + 1)) := by
  intro p n
  induction n with
  | zero =>
    intro hb
    apply Or.inl
    intro i
    exact hb i (Nat.zero_le i)
  | succ m ih =>
    intro hb
    cases rzd_zero_or_ne (p m) with
    | inl hz =>
      have hbm : IsPolyBounded ratRing p m := ppu_bound_drop ratRing hb hz
      exact ih hbm
    | inr hne =>
      apply Or.inr
      exact ⟨m, hne, hb⟩

end IUT
