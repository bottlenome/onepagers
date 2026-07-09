/-
  IUT/CbrtTwoAlpha.lean — CTA（A1 実数体 ℚ(∛2) = ℚ[x]/(x³−2) の
  **∛2 の実在**・Wave 3 / N9）

  ── 分類 **[実／承認済み足場(c)]**（本物の先行建設への足場。骨格でなく
  実 ℚ・実 f = x³−2・実単純拡大 L = ℚ[X]/(x³−2) の上の本物の等式・
  sorry 皆無・新規 Classical.choice 皆無・模型ゼロ）。名前付き実ターゲット:
  A1「実数体 K = ℚ[x]/(f) を実際の商環として構成」の ∛2 の実在言明
  （設計書 `audit/A1-real-numberfield-plan.md` §1 の G4・§4 の N9）。
  M275F `RootAdjunction`（根 ρ = [X]・f(ρ) = 0・ρ∉K 像）を実 ℚ・実 f で
  実例化し、**α := ∛2 = [X] ∈ ℚ[X]/(x³−2)** に対し
   * `cta_alpha_cubed` — **α³ = emb(2)**（f(α) = 0 の rsum 4 項展開を
     α³ = emb(2) へ移項。本物の等式）。
   * `cta_alpha_not_rational` — **α ∉ ℚ 像**（deg 3 ≥ 2 での
     `rootAdj_root_not_in_base` の実例化）。
   * `cta_exists` — ∛2 が L に実在し ℚ に無い（capstone）。

  **complete_pct 影響**: 本層単体では **complete_pct 未設定（0 前進）**。
  A1 の complete_pct はイデアル極大性（Wave 2 = `cbrtTwo_bezout`）と
  体化（Wave 3 の build 充填）が本物で揃った時に動かす。本層はその
  「本コース」の ∛2 の実在言明を実 ℚ・実 f・実商環の上で本当に閉じる
  （水増しの束ねではなく、M275F を実 ℚ で実例化して α³ = 2・α∉ℚ を
  本物の対象の上で確定する）。α∉ℚ だけでも A1 の実数体建設に実質的価値がある。

  正直な限定（本層に含めないもの・§4 規約により消さない）:
   - **単一 f = x³−2 のみ**。一般既約 f の根の実在は未達（設計 §5 の
     名前付き後続）。
   - **拡大環 L の体性（逆元）は本層で使わない**（Wave 2/3 の主語）。本層は
     根 α とその代数的関係 α³ = 2・α∉ℚ 像のみを確定する。
   - 1, α, α² の完全な一次独立（次数 3 の完全抽出）は行わず、α∉ℚ 像
     （`rootAdj_root_not_in_base`）に留める（M275F の許容された限定を継承）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.CbrtTwoBase
import IUT.RootAdjunction
import IUT.SimpleExtension
import IUT.LTErrorDivisible
import IUT.LubinTateZp

namespace IUT

/-! ## CTA-1: 根 α = ∛2 := [X] -/

/-- **CTA-1: 根 α = ∛2**（= [X] ∈ L = ℚ[X]/(x³−2)）— M275F `rootAdj_root` の
    実 ℚ・実 f 実例化。 -/
def ctaAlpha : (simpleExtRing ct0Field ct0PS 3 ct0_bound).carrier :=
  rootAdj_root ct0Field ct0PS 3 ct0_bound

/-! ## CTA-2: α³ = emb(2) -/

/-- **定理 (CTA-2): α³ = emb(2)** — 単純拡大 L = ℚ[X]/(x³−2) において
    α = [X] は α·(α·α) = emb(2)（基礎体埋め込みで送った 2）を満たす。
    出発点は M275F `rootAdj_is_root`（f(α) = 0）。f の評価
    `rootAdjEval` = Σ_{k≤3} emb(ct0PS k)·α^k を係数（0→−2, 1→0, 2→0, 3→1）で
    展開すると emb(−2)·1 + 0 + 0 + emb(1)·α³ = 0。環準同型 emb で
    emb(−2) = −emb(2)・emb(1) = 1 を使い α³ = emb(2) へ移項する。 -/
theorem cta_alpha_cubed :
    (simpleExtRing ct0Field ct0PS 3 ct0_bound).mul ctaAlpha
      ((simpleExtRing ct0Field ct0PS 3 ct0_bound).mul ctaAlpha ctaAlpha)
      = (simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two := by
  -- 定数項 −2 = −(2)（実 ℚ 上、`ratOfInt` の環準同型性）
  have hneg : cbpNegTwo = ratRing.neg ct0Two := by
    show ratOfInt.map (-2 : Int) = ratRing.neg (ratOfInt.map (2 : Int))
    exact RingHom.map_neg ratOfInt (2 : Int)
  -- 各係数を emb で送った像
  have hcoef0 :
      (simpleExtC ct0Field ct0PS 3 ct0_bound).map (ct0PS 0)
        = (simpleExtRing ct0Field ct0PS 3 ct0_bound).neg
            ((simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two) := by
    rw [ct0PS_coeff0, hneg]
    exact RingHom.map_neg (simpleExtC ct0Field ct0PS 3 ct0_bound) ct0Two
  have hcoef1 :
      (simpleExtC ct0Field ct0PS 3 ct0_bound).map (ct0PS 1)
        = (simpleExtRing ct0Field ct0PS 3 ct0_bound).zero := by
    rw [ct0PS_coeff1]
    exact RingHom.map_zero (simpleExtC ct0Field ct0PS 3 ct0_bound)
  have hcoef2 :
      (simpleExtC ct0Field ct0PS 3 ct0_bound).map (ct0PS 2)
        = (simpleExtRing ct0Field ct0PS 3 ct0_bound).zero := by
    rw [ct0PS_coeff2]
    exact RingHom.map_zero (simpleExtC ct0Field ct0PS 3 ct0_bound)
  have hcoef3 :
      (simpleExtC ct0Field ct0PS 3 ct0_bound).map (ct0PS 3)
        = (simpleExtRing ct0Field ct0PS 3 ct0_bound).one := by
    rw [ct0PS_coeff3]
    exact (simpleExtC ct0Field ct0PS 3 ct0_bound).map_one
  -- f(α) の rsum 4 項展開 → −emb(2) + α³
  have hexp :
      rootAdjEval ct0Field ct0PS 3 ct0_bound
        = (simpleExtRing ct0Field ct0PS 3 ct0_bound).add
            ((simpleExtRing ct0Field ct0PS 3 ct0_bound).neg
              ((simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two))
            (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 3) := by
    show (simpleExtRing ct0Field ct0PS 3 ct0_bound).add
        ((simpleExtRing ct0Field ct0PS 3 ct0_bound).add
          ((simpleExtRing ct0Field ct0PS 3 ct0_bound).add
            ((simpleExtRing ct0Field ct0PS 3 ct0_bound).add
              (simpleExtRing ct0Field ct0PS 3 ct0_bound).zero
              ((simpleExtRing ct0Field ct0PS 3 ct0_bound).mul
                ((simpleExtC ct0Field ct0PS 3 ct0_bound).map (ct0PS 0))
                (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 0)))
            ((simpleExtRing ct0Field ct0PS 3 ct0_bound).mul
              ((simpleExtC ct0Field ct0PS 3 ct0_bound).map (ct0PS 1))
              (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 1)))
          ((simpleExtRing ct0Field ct0PS 3 ct0_bound).mul
            ((simpleExtC ct0Field ct0PS 3 ct0_bound).map (ct0PS 2))
            (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 2)))
        ((simpleExtRing ct0Field ct0PS 3 ct0_bound).mul
          ((simpleExtC ct0Field ct0PS 3 ct0_bound).map (ct0PS 3))
          (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 3))
      = (simpleExtRing ct0Field ct0PS 3 ct0_bound).add
          ((simpleExtRing ct0Field ct0PS 3 ct0_bound).neg
            ((simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two))
          (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 3)
    rw [hcoef0, hcoef1, hcoef2, hcoef3,
      show rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 0
          = (simpleExtRing ct0Field ct0PS 3 ct0_bound).one from rfl,
      CRing.mul_one (simpleExtRing ct0Field ct0PS 3 ct0_bound)
        ((simpleExtRing ct0Field ct0PS 3 ct0_bound).neg
          ((simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two)),
      CRing.zero_mul (simpleExtRing ct0Field ct0PS 3 ct0_bound)
        (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 1),
      CRing.zero_mul (simpleExtRing ct0Field ct0PS 3 ct0_bound)
        (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 2),
      (simpleExtRing ct0Field ct0PS 3 ct0_bound).one_mul
        (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 3),
      (simpleExtRing ct0Field ct0PS 3 ct0_bound).zero_add
        ((simpleExtRing ct0Field ct0PS 3 ct0_bound).neg
          ((simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two)),
      CRing.add_zero (simpleExtRing ct0Field ct0PS 3 ct0_bound)
        ((simpleExtRing ct0Field ct0PS 3 ct0_bound).neg
          ((simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two)),
      CRing.add_zero (simpleExtRing ct0Field ct0PS 3 ct0_bound)
        ((simpleExtRing ct0Field ct0PS 3 ct0_bound).neg
          ((simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two))]
  -- f(α) = 0 と展開を合わせて −emb(2) + α³ = 0
  have hkey :
      (simpleExtRing ct0Field ct0PS 3 ct0_bound).add
        ((simpleExtRing ct0Field ct0PS 3 ct0_bound).neg
          ((simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two))
        (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 3)
      = (simpleExtRing ct0Field ct0PS 3 ct0_bound).zero := by
    rw [← hexp]
    exact rootAdj_is_root ct0Field ct0PS 3 ct0_bound
  -- 移項: α³ = emb(2)
  have hrp3 :
      rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 3
        = (simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two := by
    apply CRing.eq_of_sub_eq_zero (simpleExtRing ct0Field ct0PS 3 ct0_bound)
    rw [(simpleExtRing ct0Field ct0PS 3 ct0_bound).add_comm
        (rpow (simpleExtRing ct0Field ct0PS 3 ct0_bound) ctaAlpha 3)
        ((simpleExtRing ct0Field ct0PS 3 ct0_bound).neg
          ((simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two))]
    exact hkey
  -- α³ = α·(α·α) へ整形
  rw [← hrp3]
  show (simpleExtRing ct0Field ct0PS 3 ct0_bound).mul ctaAlpha
      ((simpleExtRing ct0Field ct0PS 3 ct0_bound).mul ctaAlpha ctaAlpha)
    = (simpleExtRing ct0Field ct0PS 3 ct0_bound).mul
        ((simpleExtRing ct0Field ct0PS 3 ct0_bound).mul
          ((simpleExtRing ct0Field ct0PS 3 ct0_bound).mul
            (simpleExtRing ct0Field ct0PS 3 ct0_bound).one ctaAlpha) ctaAlpha)
        ctaAlpha
  rw [(simpleExtRing ct0Field ct0PS 3 ct0_bound).one_mul ctaAlpha]
  exact ((simpleExtRing ct0Field ct0PS 3 ct0_bound).mul_assoc
    ctaAlpha ctaAlpha ctaAlpha).symm

/-! ## CTA-3: α ∉ ℚ 像 -/

/-- **定理 (CTA-3): α ∉ ℚ 像** — α = ∛2 は基礎体 ℚ のどの元の埋め込み像にも
    一致しない（真の拡大の非自明性）。deg f = 3 ≥ 2 での M275F
    `rootAdj_root_not_in_base` の実例化（先頭係数 `ct0_lead`・基礎体非自明
    `ct0_base_nontrivial`）。 -/
theorem cta_alpha_not_rational :
    ∀ c : QRat, ctaAlpha ≠ (simpleExtC ct0Field ct0PS 3 ct0_bound).map c :=
  rootAdj_root_not_in_base ct0Field ct0PS 3 ct0_bound ct0_lead
    (by omega) ct0_base_nontrivial

/-! ## CTA-4: capstone — ∛2 が実在し ℚ に無い -/

/-- **定理 (CTA-4): ∛2 の実在** — 実三次数体 L = ℚ[X]/(x³−2) に、α³ = emb(2)
    を満たし かつ ℚ のどの元の像とも異なる元 α が存在する（∛2 が本物に
    実在し ℚ には無い）。 -/
theorem cta_exists :
    ∃ α : (simpleExtRing ct0Field ct0PS 3 ct0_bound).carrier,
      (simpleExtRing ct0Field ct0PS 3 ct0_bound).mul α
        ((simpleExtRing ct0Field ct0PS 3 ct0_bound).mul α α)
        = (simpleExtC ct0Field ct0PS 3 ct0_bound).map ct0Two ∧
      (∀ c : QRat, α ≠ (simpleExtC ct0Field ct0PS 3 ct0_bound).map c) :=
  ⟨ctaAlpha, cta_alpha_cubed, cta_alpha_not_rational⟩

end IUT
