/-
  IUT/GenExtFieldNF.lean — Wave2/F5（A1 0.80→0.85 設計 §1 F5）:
  正規形担体 `GefNF` の可換環 `gefNFRing`（乗法 = 掛けて f で簡約）

  ── 主要成果の分類: **[実]**（本物の先行建設。全域 inv 付き実体 ℚ[x]/(f)
     の第二表示＝正規形（次数 < nf の剰余）担体の可換環構造を、実 ℚ 係数の
     多項式除法関数 `pfdRed`（F3）の上に choice-free に建てる）。

  **complete_pct 影響**: A1（実 ℚ[x]/(f)・全域 inv 付き実体）への承認済み足場。
  既存 `simpleExtRing`（M269F）は Quot 担体上の環で、全域 inv は ∃ 形に留まる
  （0.2 の choice-free 非存在）。本層は次数 < nf の剰余代表を担体
  `GefNF := {g // IsPolyBounded ratRing g nf}` にし、加法は各点・**乗法は
  「掛けて f で割った剰余」**（`pfdRed f nf nf (a·b)`）で可換環 `gefNFRing` を
  構成する。これが F6（全域 inv・IUTField/Field268）の直接の土台。
  complete_pct は本ファイル単体では未前進（A1 は F5/F6 完了後の独立再監査で
  確定）。complete_pct 未設定。

  本物性: 乗法は本物の多項式除法関数 `pfdDivMod`（F3、`field_division_exists`
  の witness をそのまま関数化したもの）の剰余で、模型・代理でない。
  結合律 `mul_assoc`・分配律 `left_distrib` は `pfdRed_char`（剰余の一意特徴
  付け・M268F-7 の剰余一意性に帰着）で本物に閉じる: 「合同（差が f の倍元）を
  保つ剰余簡約」を小さな合同代数 `gnfCong`（refl/symm/trans/加法/左右乗法/
  剰余）で組み、両辺を同じ剰余に落とす。仮定・sorry での誤魔化しなし。

  正直な限定:
   - 対象体は実 ℚ（ratRing・qInv・ratIUTField.mul_inv_cancel）に固定。
   - 環（環法則）までは f の既約性 hirr 不要（本ファイルは環まで）。全域 inv・
     体性は F6（既約性の Bezout 化を使う）。
   - 上界 nf は型パラメータ（データ）。ℚ 以外の一般 Field268 は写経の反復で可能。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyDivModFn
import IUT.SimpleExtension
import IUT.RatZeroDecide

namespace IUT

/-! ## F5-0: ℚ 係数形式冪級数環の別名（環法則の作業用） -/

/-- `psRing ratRing` の別名（合同代数の環法則をドット記法で回すため）。 -/
def gnfCR : CRing := psRing ratRing

/-! ## F5-1: 正規形担体 `GefNF`（次数 < nf の剰余代表） -/

/-- **F5-1: 正規形担体** — 実 ℚ[x]/(f) の各類のちょうど 1 つの正規形代表
    （次数 < nf の多項式）。上界 nf は型パラメータ（データ）であり ∃N の
    抽出問題が生じない。 -/
def GefNF (f : PS ratRing) (nf : Nat) : Type :=
  { g : PS ratRing // IsPolyBounded ratRing g nf }

/-! ## F5-2: 合同代数 `gnfCong`（差が f の倍元）— 環法則の共通エンジン -/

/-- **F5-2: 法 f 合同** — u − v が（多項式 h により）h·f に等しい。
    剰余簡約が保つ同値関係。環法則（mul_assoc / left_distrib）はこの合同を
    組み立てて両辺を同じ剰余へ落とすことで閉じる。 -/
def gnfCong (f u v : PS ratRing) : Prop :=
  ∃ (h : PS ratRing), IsPoly ratRing h ∧
    gnfCR.add u (gnfCR.neg v) = gnfCR.mul h f

/-- 差分の等式補題（自己参照回避のため w, q, r, fp を抽象化）:
    w = q·fp + r ⟹ r − w = (−q)·fp。 -/
theorem gnfSubHelper (R : CRing) (w q r fp : R.carrier)
    (h : w = R.add (R.mul q fp) r) :
    R.add r (R.neg w) = R.mul (R.neg q) fp := by
  rw [h, CRing.neg_add_dist R (R.mul q fp) r,
    R.add_comm (R.neg (R.mul q fp)) (R.neg r),
    ← R.add_assoc r (R.neg r) (R.neg (R.mul q fp)),
    CRing.add_neg R r, R.zero_add, CRing.neg_mul R q fp]

/-- 合同は等式から従う（h = 0）。 -/
theorem gnfCong_of_eq (f u v : PS ratRing) (h : u = v) : gnfCong f u v := by
  refine ⟨gnfCR.zero, ⟨0, fun _ _ => rfl⟩, ?_⟩
  rw [h, CRing.add_neg gnfCR v, CRing.zero_mul gnfCR f]

/-- 合同の対称性（h ↦ −h）。 -/
theorem gnfCong_symm (f : PS ratRing) {u v : PS ratRing}
    (h : gnfCong f u v) : gnfCong f v u := by
  obtain ⟨c, ⟨Nc, hcb⟩, he⟩ := h
  refine ⟨gnfCR.neg c, ⟨Nc, simpleExt_neg_bounded ratRing hcb⟩, ?_⟩
  rw [CRing.neg_mul gnfCR c f, ← he, CRing.neg_add_dist gnfCR u (gnfCR.neg v),
    CRing.neg_neg gnfCR v, gnfCR.add_comm (gnfCR.neg u) v]

/-- 合同の推移性（h ↦ h1 + h2）。 -/
theorem gnfCong_trans (f : PS ratRing) {u v w : PS ratRing}
    (h1 : gnfCong f u v) (h2 : gnfCong f v w) : gnfCong f u w := by
  obtain ⟨c1, ⟨N1, hc1b⟩, he1⟩ := h1
  obtain ⟨c2, ⟨N2, hc2b⟩, he2⟩ := h2
  refine ⟨gnfCR.add c1 c2, ⟨N1 + N2, simpleExt_add_bounded ratRing hc1b hc2b⟩, ?_⟩
  rw [CRing.right_distrib gnfCR c1 c2 f, ← he1, ← he2,
    gnfCR.add_assoc u (gnfCR.neg v) (gnfCR.add v (gnfCR.neg w)),
    ← gnfCR.add_assoc (gnfCR.neg v) v (gnfCR.neg w),
    gnfCR.neg_add v, gnfCR.zero_add]

/-- 合同は加法と両立（h ↦ h1 + h2）。 -/
theorem gnfCong_add (f : PS ratRing) {u1 v1 u2 v2 : PS ratRing}
    (h1 : gnfCong f u1 v1) (h2 : gnfCong f u2 v2) :
    gnfCong f (gnfCR.add u1 u2) (gnfCR.add v1 v2) := by
  obtain ⟨c1, ⟨N1, hc1b⟩, he1⟩ := h1
  obtain ⟨c2, ⟨N2, hc2b⟩, he2⟩ := h2
  refine ⟨gnfCR.add c1 c2, ⟨N1 + N2, simpleExt_add_bounded ratRing hc1b hc2b⟩, ?_⟩
  rw [CRing.right_distrib gnfCR c1 c2 f, ← he1, ← he2,
    CRing.neg_add_dist gnfCR v1 v2,
    CRing.add_add_add_comm gnfCR u1 u2 (gnfCR.neg v1) (gnfCR.neg v2)]

/-- 合同は右乗法と両立（h ↦ h·c）。 -/
theorem gnfCong_mul_right (f c : PS ratRing) (hc : IsPoly ratRing c)
    {u v : PS ratRing} (h : gnfCong f u v) :
    gnfCong f (gnfCR.mul u c) (gnfCR.mul v c) := by
  obtain ⟨hcoef, ⟨Nh, hhb⟩, he⟩ := h
  obtain ⟨Nc, hcb⟩ := hc
  refine ⟨gnfCR.mul hcoef c, ⟨Nh + Nc, simpleExt_mul_bounded ratRing hhb hcb⟩, ?_⟩
  rw [← CRing.neg_mul gnfCR v c, ← CRing.right_distrib gnfCR u (gnfCR.neg v) c, he,
    gnfCR.mul_assoc hcoef f c, gnfCR.mul_comm f c, ← gnfCR.mul_assoc hcoef c f]

/-- 合同は左乗法と両立（h ↦ c·h）。 -/
theorem gnfCong_mul_left (f c : PS ratRing) (hc : IsPoly ratRing c)
    {u v : PS ratRing} (h : gnfCong f u v) :
    gnfCong f (gnfCR.mul c u) (gnfCR.mul c v) := by
  obtain ⟨hcoef, ⟨Nh, hhb⟩, he⟩ := h
  obtain ⟨Nc, hcb⟩ := hc
  refine ⟨gnfCR.mul c hcoef, ⟨Nc + Nh, simpleExt_mul_bounded ratRing hcb hhb⟩, ?_⟩
  rw [← CRing.mul_neg gnfCR c v, ← gnfCR.left_distrib c u (gnfCR.neg v), he,
    ← gnfCR.mul_assoc c hcoef f]

/-- **剰余は元に合同** — pfdRed f nf N w ≡ w (mod f)（余因子 = −商）。
    合同代数の唯一の非純代数入力（`pfdDivMod_spec` を使う）。 -/
theorem gnfCong_red (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (N : Nat) (w : PS ratRing) (hw : IsPolyBounded ratRing w (N + nf)) :
    gnfCong f (pfdRed f nf N w) w := by
  obtain ⟨hqb, _, heq⟩ := pfdDivMod_spec f nf hb hl N w hw
  refine ⟨gnfCR.neg (pfdDivMod f nf N w).1,
    ⟨N + 1, simpleExt_neg_bounded ratRing hqb⟩, ?_⟩
  have hweq : w = gnfCR.add (gnfCR.mul (pfdDivMod f nf N w).1 f) (pfdRed f nf N w) :=
    funext heq
  exact gnfSubHelper gnfCR w (pfdDivMod f nf N w).1 (pfdRed f nf N w) f hweq

/-! ## F5-3: 正規形担体の可換環 `gefNFRing`（乗法 = 掛けて簡約） -/

/-- **F5-3: 正規形担体の可換環** — 加法は各点、**乗法は「掛けて f で割った
    剰余」** `pfdRed f nf nf (a·b)`。加法系・mul_comm・one_mul は psRing の
    法則へ降下、mul_assoc / left_distrib は合同代数（両辺を同じ剰余に落とす）
    で本物に閉じる。環までは f の既約性は不要。 -/
def gefNFRing (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) : CRing where
  carrier := GefNF f nf
  add := fun a b => ⟨psAdd ratRing a.val b.val, fun j hj => by
    show ratRing.add (a.val j) (b.val j) = ratRing.zero
    rw [a.property j hj, b.property j hj, ratRing.zero_add]⟩
  zero := ⟨psZero ratRing, fun _ _ => rfl⟩
  neg := fun a => ⟨psNeg ratRing a.val, fun j hj => by
    show ratRing.neg (a.val j) = ratRing.zero
    rw [a.property j hj, CRing.neg_zero ratRing]⟩
  mul := fun a b => ⟨pfdRed f nf nf (psMul ratRing a.val b.val),
    pfdRed_bound f nf hb hl nf (psMul ratRing a.val b.val)
      (simpleExt_mul_bounded ratRing a.property b.property)⟩
  one := ⟨psOne ratRing, fun j hj => by
    show (if j = 0 then ratRing.one else ratRing.zero) = ratRing.zero
    exact if_neg (by omega)⟩
  add_assoc := by
    intro a b c
    apply Subtype.ext
    exact (psRing ratRing).add_assoc a.val b.val c.val
  zero_add := by
    intro a
    apply Subtype.ext
    exact (psRing ratRing).zero_add a.val
  neg_add := by
    intro a
    apply Subtype.ext
    exact (psRing ratRing).neg_add a.val
  add_comm := by
    intro a b
    apply Subtype.ext
    exact (psRing ratRing).add_comm a.val b.val
  mul_comm := by
    intro a b
    apply Subtype.ext
    exact congrArg (pfdRed f nf nf) ((psRing ratRing).mul_comm a.val b.val)
  one_mul := by
    intro a
    apply Subtype.ext
    show pfdRed f nf nf (psMul ratRing (psOne ratRing) a.val) = a.val
    have h1 : psMul ratRing (psOne ratRing) a.val = a.val :=
      (psRing ratRing).one_mul a.val
    rw [h1]
    funext j
    exact pfdRed_of_bounded f nf hb hl nf a.val a.property j
  mul_assoc := by
    intro a b c
    apply Subtype.ext
    funext j
    have hcong : gnfCong f
        (psMul ratRing (pfdRed f nf nf (psMul ratRing a.val b.val)) c.val)
        (pfdRed f nf nf
          (psMul ratRing a.val (pfdRed f nf nf (psMul ratRing b.val c.val)))) := by
      apply gnfCong_trans f
        (v := psMul ratRing a.val (psMul ratRing b.val c.val))
      · apply gnfCong_trans f
          (v := psMul ratRing (psMul ratRing a.val b.val) c.val)
        · exact gnfCong_mul_right f c.val ⟨nf, c.property⟩
            (gnfCong_red f nf hb hl nf (psMul ratRing a.val b.val)
              (simpleExt_mul_bounded ratRing a.property b.property))
        · exact gnfCong_of_eq f _ _
            ((psRing ratRing).mul_assoc a.val b.val c.val)
      · apply gnfCong_trans f
          (v := psMul ratRing a.val (pfdRed f nf nf (psMul ratRing b.val c.val)))
        · exact gnfCong_mul_left f a.val ⟨nf, a.property⟩
            (gnfCong_symm f
              (gnfCong_red f nf hb hl nf (psMul ratRing b.val c.val)
                (simpleExt_mul_bounded ratRing b.property c.property)))
        · exact gnfCong_symm f
            (gnfCong_red f nf hb hl nf
              (psMul ratRing a.val (pfdRed f nf nf (psMul ratRing b.val c.val)))
              (simpleExt_mul_bounded ratRing a.property
                (pfdRed_bound f nf hb hl nf (psMul ratRing b.val c.val)
                  (simpleExt_mul_bounded ratRing b.property c.property))))
    obtain ⟨cf, ⟨Ncf, hcfb⟩, hcfe⟩ := hcong
    exact pfdRed_char f nf hb hl nf
      (psMul ratRing (pfdRed f nf nf (psMul ratRing a.val b.val)) c.val)
      (pfdRed f nf nf
        (psMul ratRing a.val (pfdRed f nf nf (psMul ratRing b.val c.val))))
      (simpleExt_mul_bounded ratRing
        (pfdRed_bound f nf hb hl nf (psMul ratRing a.val b.val)
          (simpleExt_mul_bounded ratRing a.property b.property)) c.property)
      (pfdRed_bound f nf hb hl nf
        (psMul ratRing a.val (pfdRed f nf nf (psMul ratRing b.val c.val)))
        (simpleExt_mul_bounded ratRing a.property
          (pfdRed_bound f nf hb hl nf (psMul ratRing b.val c.val)
            (simpleExt_mul_bounded ratRing b.property c.property))))
      ⟨cf, Ncf, hcfb, fun k => congrFun hcfe k⟩ j
  left_distrib := by
    intro a b c
    apply Subtype.ext
    funext j
    have hbc : IsPolyBounded ratRing (psAdd ratRing b.val c.val) nf := by
      intro k hk
      show ratRing.add (b.val k) (c.val k) = ratRing.zero
      rw [b.property k hk, c.property k hk, ratRing.zero_add]
    have hcong : gnfCong f
        (psMul ratRing a.val (psAdd ratRing b.val c.val))
        (psAdd ratRing (pfdRed f nf nf (psMul ratRing a.val b.val))
          (pfdRed f nf nf (psMul ratRing a.val c.val))) := by
      apply gnfCong_trans f
        (v := psAdd ratRing (psMul ratRing a.val b.val) (psMul ratRing a.val c.val))
      · exact gnfCong_of_eq f _ _
          ((psRing ratRing).left_distrib a.val b.val c.val)
      · exact gnfCong_add f
          (gnfCong_symm f (gnfCong_red f nf hb hl nf (psMul ratRing a.val b.val)
            (simpleExt_mul_bounded ratRing a.property b.property)))
          (gnfCong_symm f (gnfCong_red f nf hb hl nf (psMul ratRing a.val c.val)
            (simpleExt_mul_bounded ratRing a.property c.property)))
    have hvbound : IsPolyBounded ratRing
        (psAdd ratRing (pfdRed f nf nf (psMul ratRing a.val b.val))
          (pfdRed f nf nf (psMul ratRing a.val c.val))) nf := by
      intro k hk
      show ratRing.add
        (pfdRed f nf nf (psMul ratRing a.val b.val) k)
        (pfdRed f nf nf (psMul ratRing a.val c.val) k) = ratRing.zero
      rw [pfdRed_bound f nf hb hl nf (psMul ratRing a.val b.val)
            (simpleExt_mul_bounded ratRing a.property b.property) k hk,
          pfdRed_bound f nf hb hl nf (psMul ratRing a.val c.val)
            (simpleExt_mul_bounded ratRing a.property c.property) k hk,
          ratRing.zero_add]
    obtain ⟨cf, ⟨Ncf, hcfb⟩, hcfe⟩ := hcong
    exact pfdRed_char f nf hb hl nf
      (psMul ratRing a.val (psAdd ratRing b.val c.val))
      (psAdd ratRing (pfdRed f nf nf (psMul ratRing a.val b.val))
        (pfdRed f nf nf (psMul ratRing a.val c.val)))
      (simpleExt_mul_bounded ratRing a.property hbc)
      hvbound
      ⟨cf, Ncf, hcfb, fun k => congrFun hcfe k⟩ j

/-! ## F5-4: 非自明性（1 ≠ 0） -/

/-- **F5-4: 非自明** — 正規形担体の環で 1 ≠ 0。0 次係数で 1 ≠ 0
    （`rzd_ne_zero_of_num_ne`、prOne.num = 1）。 -/
theorem gnf_zero_ne_one (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) :
    (gefNFRing f nf hb hl hn).one ≠ (gefNFRing f nf hb hl hn).zero := by
  intro h
  have hval : psOne ratRing = psZero ratRing :=
    congrArg (fun t : GefNF f nf => t.val) h
  have h0 : ratRing.one = ratRing.zero := congrFun hval 0
  have hnum : prOne.num ≠ 0 := by
    show (1 : Int) ≠ 0
    omega
  exact rzd_ne_zero_of_num_ne hnum h0

end IUT
