/-
  IUT/CbrtBezB.lean — Wave 1 / N5（ℚ[x]/(x³−2) 実体建設の Bezout 述語と
  2 核補題: 柱A 実 Galois 理論／実数体建設）

  ── 分類 **[実／承認済み足場(c)]**（骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無・模型なし）。

  **complete_pct 影響**: 0 前進（足場整備のみ・complete_pct 未設定）。
  本層は `audit/A1-real-numberfield-plan.md` §2.2 / §4 N5 の**名前付き
  実ターゲット**「実三次数体 ℚ(∛2) = ℚ[x]/(x³−2) を本物の商環として構成
  （G3/G4）」への必要足場である。実 ℚ（`ratRing`）の PS（冪級数＝有限台
  多項式）上で、拡張ユークリッド鎖を回すための中間 Bezout 述語 `cbzBezB`
  と、その鎖を賄う 2 本の核補題 `cbz_const`（非零定数の互除）・
  `cbz_descend`（1 段除法での Bezout 降下）を、psRing の CRing 法則の
  純代数と bound 伝播（`simpleExt_*_bounded` 既存）で完全証明する。
  後続計画: 本補題群を土台に N7 `cbrtTwo_bezout` を field_division_exists
  の入れ子場合分けで組み立て、`cbrtTwoData : SimpleExtData ratField268`
  を実 ℚ・実 f=x³−2 で充填する。

  * cbzBezB          — PS レベルの Bezout 述語（∃ u v, u·x + v·y = 1）
  * cbz_add_cancel   — 加法簿記 (a+B)+(C+(−a)) = C+B（純代数の下ごしらえ）
  * cbz_descend_algebra — 降下の代数核 v·w + (u−v·q)·g = u·g + v·rr
  * cbz_const        — 非零定数 y は任意 x と互いに素（witness v = psC(y0⁻¹)）
  * cbz_descend      — w = q·g + rr ∧ BezB g rr ⟹ BezB w g（1 段降下）

  正直な限定: `cbzBezB` は実 ℚ 上の PS（有限台多項式）に対する本物の
  Bezout 述語であり、2 核補題は完全証明（sorry 皆無・新規 choice 皆無）。
  ただし本層単体は「単一 f=x³−2 の Bezout 極大性」そのものではなく、
  その鎖を回す再利用部品である。本丸 `cbrtTwo_bezout` は後続 Wave で
  本補題群を組み合わせて実証する（§4 N7）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyPSUtil
import IUT.Field

namespace IUT

/-! ## N5-0: PS レベルの Bezout 述語 -/

/-- **N5-0: PS 上の Bezout 述語** — x と y が実 ℚ 上の PS（有限台多項式）
    として互いに素: ある有界 u, v が存在して u·x + v·y = 1。等式は PS＝
    係数関数の等式（以後の代数は psRing の CRing 法則で行う）。 -/
def cbzBezB (x y : PS ratRing) : Prop :=
  ∃ (u v : PS ratRing) (Nu Nv : Nat),
    IsPolyBounded ratRing u Nu ∧ IsPolyBounded ratRing v Nv ∧
    psAdd ratRing (psMul ratRing u x) (psMul ratRing v y) = psOne ratRing

/-! ## N5-1: 加法簿記の下ごしらえ -/

/-- **N5-1: 相殺付き加法簿記** — (a+B)+(C+(−a)) = C+B。降下の代数核で
    v·q·g を打ち消す整理に使う（可換環の純代数）。 -/
theorem cbz_add_cancel (R : CRing) (a B C : R.carrier) :
    R.add (R.add a B) (R.add C (R.neg a)) = R.add C B := by
  rw [R.add_comm C (R.neg a),
    R.add_add_add_comm a B (R.neg a) C,
    R.add_neg a, R.zero_add, R.add_comm B C]

/-! ## N5-2: 降下の代数核 -/

/-- **N5-2: 降下の代数核** — w = q·g + rr のとき
    v·w + (u + (−(v·q)))·g = u·g + v·rr（可換環の純代数）。設計 §2.2 の
    `bez_descend` で u' = v, v' = u + (−(v·q)) の Bezout 恒等式を与える。 -/
theorem cbz_descend_algebra (R : CRing) (u v q g rr w : R.carrier)
    (hw : w = R.add (R.mul q g) rr) :
    R.add (R.mul v w) (R.mul (R.add u (R.neg (R.mul v q))) g)
      = R.add (R.mul u g) (R.mul v rr) := by
  subst hw
  rw [R.left_distrib v (R.mul q g) rr,
    CRing.right_distrib R u (R.neg (R.mul v q)) g,
    CRing.neg_mul R (R.mul v q) g,
    ← R.mul_assoc v q g,
    cbz_add_cancel R (R.mul (R.mul v q) g) (R.mul v rr) (R.mul u g)]

/-! ## N5-3: 非零定数の互除（葉補題） -/

/-- **N5-3: 非零定数との Bezout** — y が非零定数（1 有界・y 0 ≠ 0）なら
    任意の x と互いに素。witness u := 0, v := psC (y0⁻¹)。核: (psC y0⁻¹)·y
    の j 係数は y0⁻¹·(y j)、j=0 で y0⁻¹·y0 = 1（`ratIUTField.mul_inv_cancel`）、
    j≥1 で y j = 0。 -/
theorem cbz_const (x y : PS ratRing)
    (hb : IsPolyBounded ratRing y 1) (hy0 : y 0 ≠ ratRing.zero) :
    cbzBezB x y := by
  refine ⟨psZero ratRing, psC ratRing (qInv (y 0)), 0, 1, ?_, ?_, ?_⟩
  · intro i _; rfl
  · intro i hi; exact if_neg (by omega)
  · have hz : psMul ratRing (psZero ratRing) x = psZero ratRing :=
      CRing.zero_mul (psRing ratRing) x
    have hadd : psAdd ratRing (psZero ratRing)
        (psMul ratRing (psC ratRing (qInv (y 0))) y)
        = psMul ratRing (psC ratRing (qInv (y 0))) y :=
      (psRing ratRing).zero_add _
    rw [hz, hadd]
    funext j
    rw [ppu_psC_mul_left ratRing (qInv (y 0)) y j]
    cases Nat.eq_zero_or_pos j with
    | inl hj0 =>
      rw [hj0, ratRing.mul_comm (qInv (y 0)) (y 0)]
      exact ratIUTField.mul_inv_cancel (y 0) hy0
    | inr hjpos =>
      rw [hb j (by omega), CRing.mul_zero ratRing (qInv (y 0))]
      exact (if_neg (show ¬ j = 0 from by omega)).symm

/-! ## N5-4: 1 段除法での Bezout 降下 -/

/-- **N5-4: Bezout 降下** — w = q·g + rr（q 有界）かつ g と rr が互いに素
    （`cbzBezB g rr`）なら w と g も互いに素（`cbzBezB w g`）。
    設計 §2.2: u·g + v·rr = 1 に rr = w − q·g を代入し u' := v,
    v' := u + (−(v·q)) で u'·w + v'·g = 1（代数核 `cbz_descend_algebra`）。
    bound は `simpleExt_add/neg/mul_bounded`（既存）で伝播。 -/
theorem cbz_descend (w q g rr : PS ratRing) (Nq : Nat)
    (hq : IsPolyBounded ratRing q Nq)
    (hw : w = psAdd ratRing (psMul ratRing q g) rr)
    (hbez : cbzBezB g rr) : cbzBezB w g := by
  obtain ⟨u, v, Nu, Nv, hu, hv, huv⟩ := hbez
  refine ⟨v, psAdd ratRing u (psNeg ratRing (psMul ratRing v q)),
    Nv, Nu + (Nv + Nq), hv, ?_, ?_⟩
  · exact simpleExt_add_bounded ratRing hu
      (simpleExt_neg_bounded ratRing (simpleExt_mul_bounded ratRing hv hq))
  · exact (cbz_descend_algebra (psRing ratRing) u v q g rr w hw).trans huv

end IUT
