/-
  IUT/Cq3Alpha.lean — CQ3（A1 実数体 ℚ(ζ₃) = ℚ[x]/(x²+x+1) の
  **ζ₃ の実在**・CbrtTwoAlpha（CTA・次数3・∛2）の次数2版アナロジー）

  ── 分類 **[実／承認済み足場(c)]**（本物の先行建設への足場。骨格でなく
  実 ℚ・実 Φ₃ = x²+x+1・実単純拡大 L = ℚ[X]/(x²+x+1) の上の本物の等式・
  sorry 皆無・新規 Classical.choice 皆無・模型ゼロ）。名前付き実ターゲット:
  A1「実数体 K = ℚ[x]/(f) を実際の商環として構成」の第二の本物のインスタンス
  実二次数体 ℚ(ζ₃) の ζ₃ の実在言明（CTA `CbrtTwoAlpha` の次数2版）。
  M275F `RootAdjunction`（根 ρ = [X]・f(ρ) = 0・ρ∉K 像）を実 ℚ・実 Φ₃ で
  実例化し、**ζ := ζ₃ = [X] ∈ ℚ[X]/(x²+x+1)** に対し
   * `cqz_zeta_relation` — **ζ² + ζ + 1 = 0**（f(ζ) = 0 の rsum 3 項展開を
     ζ²+ζ+1 = 0 の形へ整理。Φ₃ の係数は全て +1 なので map_one/一次結合のみで
     閉じる本物の等式）。
   * `cqz_zeta_not_rational` — **ζ ∉ ℚ 像**（deg 2 ≥ 2 での
     `rootAdj_root_not_in_base` の実例化）。
   * `cqz_exists` — ζ₃ が L に実在し ℚ に無い（capstone）。

  **complete_pct 影響**: 本層単体では **complete_pct 未設定（0 前進）**。
  A1 の complete_pct はイデアル極大性（Bezout）と体化が本物で揃った時に動かす。
  本層はその「本コース」の ζ₃ の実在言明を実 ℚ・実 Φ₃・実商環の上で本当に閉じる
  （水増しの束ねではなく、M275F を実 ℚ で実例化して ζ²+ζ+1 = 0・ζ∉ℚ を
  本物の対象の上で確定する）。ζ∉ℚ だけでも A1 の実数体建設に実質的価値がある。

  正直な限定（本層に含めないもの・§4 規約により消さない）:
   - **単一 f = x²+x+1（Φ₃）のみ**。一般既約 f の根の実在は未達。
   - **拡大環 L の体性（逆元）は本層で使わない**（Bezout/体化は別スライスの
     主語）。本層は根 ζ とその代数的関係 ζ²+ζ+1 = 0・ζ∉ℚ 像のみを確定する。
   - 1, ζ の完全な一次独立（次数 2 の完全抽出）は行わず、ζ∉ℚ 像
     （`rootAdj_root_not_in_base`）に留める（M275F の許容された限定を継承）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.Cq3Base
import IUT.RootAdjunction
import IUT.SimpleExtension

namespace IUT

/-! ## CQ3-1: 根 ζ = ζ₃ := [X] -/

/-- **CQ3-1: 根 ζ = ζ₃**（= [X] ∈ L = ℚ[X]/(x²+x+1)）— M275F `rootAdj_root` の
    実 ℚ・実 Φ₃ 実例化。 -/
def cqzZeta : (simpleExtRing cq0Field cq0PS 2 cq0_bound).carrier :=
  rootAdj_root cq0Field cq0PS 2 cq0_bound

/-! ## CQ3-2: ζ² + ζ + 1 = 0 -/

/-- **定理 (CQ3-2): ζ² + ζ + 1 = 0** — 単純拡大 L = ℚ[X]/(x²+x+1) において
    ζ = [X] は ζ·ζ + ζ + emb(1) = 0 を満たす。出発点は M275F `rootAdj_is_root`
    （f(ζ) = 0）。f の評価 `rootAdjEval` = Σ_{k≤2} emb(Φ₃ k)·ζ^k を係数
    （0→1, 1→1, 2→1）で展開すると emb(1)·1 + emb(1)·ζ + emb(1)·ζ² = 0。
    環準同型 emb で emb(1) = 1（map_one）を使い ζ² + ζ + 1 = 0 へ整える。 -/
theorem cqz_zeta_relation :
    (simpleExtRing cq0Field cq0PS 2 cq0_bound).add
      ((simpleExtRing cq0Field cq0PS 2 cq0_bound).add
        ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul cqzZeta cqzZeta)
        cqzZeta)
      ((simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one)
      = (simpleExtRing cq0Field cq0PS 2 cq0_bound).zero := by
  -- emb(1) = 1（基礎体埋め込みの map_one）
  have hmap1 :
      (simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one
        = (simpleExtRing cq0Field cq0PS 2 cq0_bound).one :=
    (simpleExtC cq0Field cq0PS 2 cq0_bound).map_one
  -- 各項の縮約（係数 = 1・冪の展開）
  have hg0 :
      (simpleExtRing cq0Field cq0PS 2 cq0_bound).mul
        ((simpleExtC cq0Field cq0PS 2 cq0_bound).map (cq0PS 0))
        (rpow (simpleExtRing cq0Field cq0PS 2 cq0_bound) cqzZeta 0)
      = (simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one := by
    rw [cq0PS_coeff0]
    exact CRing.mul_one (simpleExtRing cq0Field cq0PS 2 cq0_bound)
      ((simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one)
  have hg1 :
      (simpleExtRing cq0Field cq0PS 2 cq0_bound).mul
        ((simpleExtC cq0Field cq0PS 2 cq0_bound).map (cq0PS 1))
        (rpow (simpleExtRing cq0Field cq0PS 2 cq0_bound) cqzZeta 1)
      = cqzZeta := by
    rw [cq0PS_coeff1, hmap1,
      (simpleExtRing cq0Field cq0PS 2 cq0_bound).one_mul
        (rpow (simpleExtRing cq0Field cq0PS 2 cq0_bound) cqzZeta 1)]
    show (simpleExtRing cq0Field cq0PS 2 cq0_bound).mul
        (simpleExtRing cq0Field cq0PS 2 cq0_bound).one cqzZeta = cqzZeta
    exact (simpleExtRing cq0Field cq0PS 2 cq0_bound).one_mul cqzZeta
  have hg2 :
      (simpleExtRing cq0Field cq0PS 2 cq0_bound).mul
        ((simpleExtC cq0Field cq0PS 2 cq0_bound).map (cq0PS 2))
        (rpow (simpleExtRing cq0Field cq0PS 2 cq0_bound) cqzZeta 2)
      = (simpleExtRing cq0Field cq0PS 2 cq0_bound).mul cqzZeta cqzZeta := by
    rw [cq0PS_coeff2, hmap1,
      (simpleExtRing cq0Field cq0PS 2 cq0_bound).one_mul
        (rpow (simpleExtRing cq0Field cq0PS 2 cq0_bound) cqzZeta 2)]
    show (simpleExtRing cq0Field cq0PS 2 cq0_bound).mul
        ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul
          (simpleExtRing cq0Field cq0PS 2 cq0_bound).one cqzZeta) cqzZeta
      = (simpleExtRing cq0Field cq0PS 2 cq0_bound).mul cqzZeta cqzZeta
    rw [(simpleExtRing cq0Field cq0PS 2 cq0_bound).one_mul cqzZeta]
  -- f(ζ) の rsum 3 項展開 → emb(1) + ζ + ζ²
  have hexp :
      rootAdjEval cq0Field cq0PS 2 cq0_bound
        = (simpleExtRing cq0Field cq0PS 2 cq0_bound).add
            ((simpleExtRing cq0Field cq0PS 2 cq0_bound).add
              ((simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one)
              cqzZeta)
            ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul cqzZeta cqzZeta) := by
    show (simpleExtRing cq0Field cq0PS 2 cq0_bound).add
        ((simpleExtRing cq0Field cq0PS 2 cq0_bound).add
          ((simpleExtRing cq0Field cq0PS 2 cq0_bound).add
            (simpleExtRing cq0Field cq0PS 2 cq0_bound).zero
            ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul
              ((simpleExtC cq0Field cq0PS 2 cq0_bound).map (cq0PS 0))
              (rpow (simpleExtRing cq0Field cq0PS 2 cq0_bound) cqzZeta 0)))
          ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul
            ((simpleExtC cq0Field cq0PS 2 cq0_bound).map (cq0PS 1))
            (rpow (simpleExtRing cq0Field cq0PS 2 cq0_bound) cqzZeta 1)))
        ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul
          ((simpleExtC cq0Field cq0PS 2 cq0_bound).map (cq0PS 2))
          (rpow (simpleExtRing cq0Field cq0PS 2 cq0_bound) cqzZeta 2))
      = (simpleExtRing cq0Field cq0PS 2 cq0_bound).add
          ((simpleExtRing cq0Field cq0PS 2 cq0_bound).add
            ((simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one)
            cqzZeta)
          ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul cqzZeta cqzZeta)
    rw [hg0, hg1, hg2,
      (simpleExtRing cq0Field cq0PS 2 cq0_bound).zero_add
        ((simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one)]
  -- f(ζ) = 0 と展開を合わせて emb(1) + ζ + ζ² = 0
  have hkey :
      (simpleExtRing cq0Field cq0PS 2 cq0_bound).add
        ((simpleExtRing cq0Field cq0PS 2 cq0_bound).add
          ((simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one)
          cqzZeta)
        ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul cqzZeta cqzZeta)
      = (simpleExtRing cq0Field cq0PS 2 cq0_bound).zero := by
    rw [← hexp]
    exact rootAdj_is_root cq0Field cq0PS 2 cq0_bound
  -- 交換律・結合律で ζ² + ζ + 1 = 0 の順に並べ替え
  rw [(simpleExtRing cq0Field cq0PS 2 cq0_bound).add_assoc
      ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul cqzZeta cqzZeta)
      cqzZeta ((simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one),
    (simpleExtRing cq0Field cq0PS 2 cq0_bound).add_comm cqzZeta
      ((simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one),
    (simpleExtRing cq0Field cq0PS 2 cq0_bound).add_comm
      ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul cqzZeta cqzZeta)
      ((simpleExtRing cq0Field cq0PS 2 cq0_bound).add
        ((simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one) cqzZeta)]
  exact hkey

/-! ## CQ3-3: ζ ∉ ℚ 像 -/

/-- **定理 (CQ3-3): ζ ∉ ℚ 像** — ζ = ζ₃ は基礎体 ℚ のどの元の埋め込み像にも
    一致しない（真の拡大の非自明性）。deg Φ₃ = 2 ≥ 2 での M275F
    `rootAdj_root_not_in_base` の実例化（先頭係数 `cq0_lead`・基礎体非自明
    `cq0_base_nontrivial`）。 -/
theorem cqz_zeta_not_rational :
    ∀ c : QRat, cqzZeta ≠ (simpleExtC cq0Field cq0PS 2 cq0_bound).map c :=
  rootAdj_root_not_in_base cq0Field cq0PS 2 cq0_bound cq0_lead
    (by omega) cq0_base_nontrivial

/-! ## CQ3-4: capstone — ζ₃ が実在し ℚ に無い -/

/-- **定理 (CQ3-4): ζ₃ の実在** — 実二次数体 L = ℚ[X]/(x²+x+1) に、
    ζ² + ζ + emb(1) = 0 を満たし かつ ℚ のどの元の像とも異なる元 ζ が存在する
    （原始 3 乗根 ζ₃ が本物に実在し ℚ には無い）。 -/
theorem cqz_exists :
    ∃ ζ : (simpleExtRing cq0Field cq0PS 2 cq0_bound).carrier,
      (simpleExtRing cq0Field cq0PS 2 cq0_bound).add
        ((simpleExtRing cq0Field cq0PS 2 cq0_bound).add
          ((simpleExtRing cq0Field cq0PS 2 cq0_bound).mul ζ ζ) ζ)
        ((simpleExtC cq0Field cq0PS 2 cq0_bound).map ratRing.one)
        = (simpleExtRing cq0Field cq0PS 2 cq0_bound).zero ∧
      (∀ c : QRat, ζ ≠ (simpleExtC cq0Field cq0PS 2 cq0_bound).map c) :=
  ⟨cqzZeta, cqz_zeta_relation, cqz_zeta_not_rational⟩

end IUT
