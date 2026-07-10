/-
  IUT/CyclotomicMuGroupReal.lean — CMR（柱A7 実円分剛性の基盤: 実 μ_{3^ℓ} ⊂ ℚ(ζ_{3^ℓ})
  を M322F 抽象枠 `CycMuGroup` の**実インスタンス**として構成する）

  ── 主要成果の分類: **[実／昇格(a)]**（骨格・模型・代理でなく、実 ℚ・実円分体
     ℚ(ζ_{3^ℓ}) = ℚ[x]/(Φ_{3^ℓ}) の中の**実部分群 μ_{3^ℓ}**——3^ℓ 乗根
     `{ y // rpow y (3^ℓ) = 1 }`——を担体に取り、その群構造（積の閉性
     `rpow_one_mul_closed`・生成元 ζ_ℓ = x̄・逆元 y^{3^ℓ−1}・離散対数 ctmFind）を
     本物で組み、M322F の抽象 `CycMuGroup`（従来の ℤ/n 模型 `cycMuStd` が実例）を
     **実 μ_{3^ℓ} の実インスタンス `cmrMu` へ昇格**する。担体は ℤ/n 模型でも抽象群でも
     なく、実円分体の中の実 3^ℓ 乗根の集合そのもの（§3 toy 主語禁止の遵守）。

  **complete_pct 影響**: A7（実円分剛性）——M322F の抽象 `CycMuGroup`（ℤ/n 模型
  `cycMuStd`）を実 μ_{3^ℓ} ⊂ ℚ(ζ_{3^ℓ}) の実インスタンスへ昇格する基盤。本ファイル
  単体では complete_pct 未設定（cgar で実 Gal 作用＋非自明 χ を実 μ 上に載せた
  A7a 完成時に独立監査で反映）。既存 surrogate（`cycMuStd`）は消さない・弱めない。

  内容（設計 audit/A7-real-cyclotomic-rigidity-detail-2026-07-10.md §1）:
   * `cmrCarrier ℓ hℓ`   — 実担体 { y : ℚ(ζ_{3^ℓ}) // y^{3^ℓ} = 1 }（実 3^ℓ 乗根群）。
   * `cmr_inv_root`      — 逆元候補 y^{3^ℓ−1} も 3^ℓ 乗根（(y^{3^ℓ−1})^{3^ℓ}=1）。
   * `cmrGrp ℓ hℓ`       — 実群 μ_{3^ℓ}（積＝体の積・単位＝1・逆元＝y^{3^ℓ−1}・
     群公理は Subtype.ext ＋ CRing 公理・逆律は rpow の反復定義から）。
   * `cmr_comm`          — μ_{3^ℓ} は可換（体の乗法可換）。
   * `cmrZeta ℓ hℓ`      — 生成元 ζ_ℓ = x̄（root 性は ctr_pow_rpow ＋ ctm_zeta_pow）。
   * `cmr_pow_val`       — ★三者橋: Grp.pow（左乗算反復）= rpow（右乗算反復）を
     可換性で合流させ、subtype 冪の val が体の rpow に一致することを k 帰納で確立。
   * `cmr_pow_zeta`      — ζ_ℓ の subtype 冪の val = ctmPow ℓ k（NF 環の冪）。
   * `cmrMu ℓ hℓ`        — ★A7a 中核: 実 `CycMuGroup` インスタンス（μ=cmrGrp・
     ζ=cmrZeta・n=3^ℓ・log=ctmFind・log_lt/pow_log/ord/distinct を実補題で充填）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   **p = 3・素数冪 3^ℓ 専用**の実円分体 ℚ(ζ_{3^ℓ})。一般素数 p は含めない。
   (ii)  本ファイルは実 μ_{3^ℓ} の**群構造と離散対数**まで（`CycMuGroup` の全フィールド
         を実対象で充填）。**G_K の実 Galois 作用**（各 σ の μ_{3^ℓ} への制限）は
         cgar（A7a・後続）、**非自明な円分指標 χ**（σ(ζ)=ζ^a, a≠1）も cgar、
         **円分剛性定理 cra**（A7c）は本ファイルに含めない。
   (iii) 既存 M322F の抽象定理群（`cycRig_char_isHom`・`cycRig_rigidity` 等）は
         `cmrMu` を代入すれば実 μ_{3^ℓ} を主語に即座に回る（M322F 設計が明言）。
         本ファイルはその実主語 `cmrMu` を供給する。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・propext/Quot.sound
  のみ）。禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。許可タクティク（cases/obtain/induction/rw/show/
  refine/exact/apply/intro/generalize/funext/Subtype.ext/omega）のみ使用。3^ℓ は
  omega 不可（`zpu_pow_pos` 再利用）。新規ファイル 1 個のみ（共有ファイル
  IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.CyclotomicMuTower
import IUT.CyclotomicResTower
import IUT.CyclotomicRigidity
import IUT.Zmod3PowUnits
import IUT.TorsionResidue
import IUT.EisensteinGalois
import IUT.FrobeniusGen

namespace IUT

/-! ## CMR-1: 実 μ_{3^ℓ} の担体と逆元候補の root 性 -/

/-- **CMR-1a: 実担体** — μ_{3^ℓ} = 実円分体 ℚ(ζ_{3^ℓ}) の中の 3^ℓ 乗根の集合
    { y // y^{3^ℓ} = 1 }（ℤ/n 模型でも抽象群でもない・実部分群）。 -/
def cmrCarrier (ℓ : Nat) (hℓ : 1 ≤ ℓ) : Type :=
  { y : (cteField ℓ hℓ).carrier //
      rpow (cteField ℓ hℓ).toCRing y (3 ^ ℓ) = (cteField ℓ hℓ).toCRing.one }

/-- **CMR-1b: 逆元候補も 3^ℓ 乗根** — y^{3^ℓ}=1 なら (y^{3^ℓ−1})^{3^ℓ}=1。
    (y^{3^ℓ−1})^{3^ℓ} = y^{(3^ℓ−1)·3^ℓ} = y^{3^ℓ·(3^ℓ−1)} = (y^{3^ℓ})^{3^ℓ−1}
    = 1^{3^ℓ−1} = 1（`rpow_rpow` ＋ `rpow_one_base`）。逆元の well-defined 性。 -/
theorem cmr_inv_root (ℓ : Nat) (hℓ : 1 ≤ ℓ) (y : (cteField ℓ hℓ).carrier)
    (hy : rpow (cteField ℓ hℓ).toCRing y (3 ^ ℓ) = (cteField ℓ hℓ).toCRing.one) :
    rpow (cteField ℓ hℓ).toCRing (rpow (cteField ℓ hℓ).toCRing y (3 ^ ℓ - 1)) (3 ^ ℓ)
      = (cteField ℓ hℓ).toCRing.one := by
  rw [rpow_rpow (cteField ℓ hℓ).toCRing y (3 ^ ℓ - 1) (3 ^ ℓ),
      Nat.mul_comm (3 ^ ℓ - 1) (3 ^ ℓ),
      ← rpow_rpow (cteField ℓ hℓ).toCRing y (3 ^ ℓ) (3 ^ ℓ - 1), hy,
      rpow_one_base (cteField ℓ hℓ).toCRing (3 ^ ℓ - 1)]

/-! ## CMR-2: 実群 μ_{3^ℓ} -/

/-- **CMR-2: 実群 μ_{3^ℓ}** — 担体 `cmrCarrier`、積は体の積（閉性
    `rpow_one_mul_closed`）、単位 1（`rpow_one_base`）、逆元 y^{3^ℓ−1}（`cmr_inv_root`）。
    群公理は Subtype.ext ＋ CRing 公理、逆律 inv_mul は rpow の反復定義
    y^{3^ℓ−1}·y = y^{(3^ℓ−1)+1} = y^{3^ℓ} = 1 から（1 ≤ 3^ℓ は `zpu_pow_pos`）。 -/
def cmrGrp (ℓ : Nat) (hℓ : 1 ≤ ℓ) : Grp where
  carrier := cmrCarrier ℓ hℓ
  mul := fun a b => ⟨(cteField ℓ hℓ).toCRing.mul a.val b.val,
    rpow_one_mul_closed (cteField ℓ hℓ).toCRing (3 ^ ℓ) a.property b.property⟩
  one := ⟨(cteField ℓ hℓ).toCRing.one, rpow_one_base (cteField ℓ hℓ).toCRing (3 ^ ℓ)⟩
  inv := fun a => ⟨rpow (cteField ℓ hℓ).toCRing a.val (3 ^ ℓ - 1),
    cmr_inv_root ℓ hℓ a.val a.property⟩
  mul_assoc := fun a b c =>
    Subtype.ext ((cteField ℓ hℓ).toCRing.mul_assoc a.val b.val c.val)
  one_mul := fun a => Subtype.ext ((cteField ℓ hℓ).toCRing.one_mul a.val)
  inv_mul := fun a => by
    apply Subtype.ext
    show (cteField ℓ hℓ).toCRing.mul (rpow (cteField ℓ hℓ).toCRing a.val (3 ^ ℓ - 1)) a.val
       = (cteField ℓ hℓ).toCRing.one
    rw [show (cteField ℓ hℓ).toCRing.mul (rpow (cteField ℓ hℓ).toCRing a.val (3 ^ ℓ - 1)) a.val
          = rpow (cteField ℓ hℓ).toCRing a.val ((3 ^ ℓ - 1) + 1) from rfl,
        show (3 ^ ℓ - 1) + 1 = 3 ^ ℓ from by have := zpu_pow_pos ℓ; omega]
    exact a.property

/-- **CMR-2b: μ_{3^ℓ} は可換**（体の乗法可換）。 -/
theorem cmr_comm (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a b : (cmrGrp ℓ hℓ).carrier) :
    (cmrGrp ℓ hℓ).mul a b = (cmrGrp ℓ hℓ).mul b a :=
  Subtype.ext ((cteField ℓ hℓ).toCRing.mul_comm a.val b.val)

/-! ## CMR-3: 三者橋 Grp.pow ↔ rpow ↔ ctmPow -/

/-- **CMR-3a（★本ファイル最大の簿記）: Grp.pow = rpow の三者橋** —
    subtype の群冪 `(cmrGrp).pow y k` の val は、体の rpow（右乗算反復）に一致する。
    Grp.pow は左乗算反復（pow (k+1) = mul g (pow g k)）、rpow は右乗算反復
    （rpow (k+1) = mul (rpow k) a）だが、体の可換性 `mul_comm` で k 帰納の両向きを合流。 -/
theorem cmr_pow_val (ℓ : Nat) (hℓ : 1 ≤ ℓ) (y : cmrCarrier ℓ hℓ) (k : Nat) :
    ((cmrGrp ℓ hℓ).pow y k).val = rpow (cteField ℓ hℓ).toCRing y.val k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (cteField ℓ hℓ).toCRing.mul y.val ((cmrGrp ℓ hℓ).pow y k).val
       = (cteField ℓ hℓ).toCRing.mul (rpow (cteField ℓ hℓ).toCRing y.val k) y.val
    rw [ih, (cteField ℓ hℓ).toCRing.mul_comm y.val (rpow (cteField ℓ hℓ).toCRing y.val k)]

/-! ## CMR-4: 生成元 ζ_ℓ と ζ_ℓ の冪 -/

/-- **CMR-4a: 生成元 ζ_ℓ の root 性** — ζ_ℓ^{3^ℓ} = 1（rpow = ctmPow の橋
    `ctr_pow_rpow` を経て `ctm_zeta_pow`。(ctmR ℓ hℓ).one と (cteField ℓ hℓ).toCRing.one
    は同じ `gefNFRing` ゆえ defeq）。 -/
theorem cmr_zeta_root (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    rpow (cteField ℓ hℓ).toCRing (ctmZeta ℓ hℓ) (3 ^ ℓ) = (cteField ℓ hℓ).toCRing.one := by
  rw [← ctr_pow_rpow ℓ hℓ (3 ^ ℓ), ctm_zeta_pow ℓ hℓ]
  rfl

/-- **CMR-4b: 生成元 ζ_ℓ = x̄**（実 μ_{3^ℓ} の生成元・原始 3^ℓ 乗根）。 -/
def cmrZeta (ℓ : Nat) (hℓ : 1 ≤ ℓ) : cmrCarrier ℓ hℓ :=
  ⟨ctmZeta ℓ hℓ, cmr_zeta_root ℓ hℓ⟩

/-- **CMR-4c: ζ_ℓ の群冪の val = ctmPow** — subtype 冪 `(cmrGrp).pow ζ_ℓ k` の val は
    NF 環の冪 ctmPow ℓ k に一致（三者橋 `cmr_pow_val` ＋ `ctr_pow_rpow`）。 -/
theorem cmr_pow_zeta (ℓ : Nat) (hℓ : 1 ≤ ℓ) (k : Nat) :
    ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) k).val = ctmPow ℓ hℓ k := by
  rw [cmr_pow_val ℓ hℓ (cmrZeta ℓ hℓ) k]
  exact (ctr_pow_rpow ℓ hℓ k).symm

/-! ## CMR-5: 実 CycMuGroup インスタンス（★A7a 中核） -/

/-- **CMR-5a: 生成元の位数 3^ℓ** — ζ_ℓ^{3^ℓ} = 1（群レベル・Subtype.ext ＋
    `cmr_pow_zeta` ＋ `ctm_zeta_pow`）。 -/
theorem cmr_ord (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (3 ^ ℓ) = (cmrGrp ℓ hℓ).one := by
  apply Subtype.ext
  show ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (3 ^ ℓ)).val = (cteField ℓ hℓ).toCRing.one
  rw [cmr_pow_zeta ℓ hℓ (3 ^ ℓ), ctm_zeta_pow ℓ hℓ]
  rfl

/-- **CMR-5b（★A7a 中核）: 実 μ_{3^ℓ} の `CycMuGroup` インスタンス** — M322F の抽象枠
    `CycMuGroup` を実円分体 ℚ(ζ_{3^ℓ}) の中の実 3^ℓ 乗根群で充填する。μ=実群 `cmrGrp`、
    生成元 ζ=実生成元 `cmrZeta`、位数 n=3^ℓ、離散対数 log=`ctmFind`（choice-free 走査）、
    log_lt/pow_log は `ctmFind_spec`、位数 ord は `cmr_ord`、冪の相異性 distinct は
    `ctm_powers_distinct`。これで M322F の全定理（円分指標・準同型性・剛性）が
    実 μ_{3^ℓ} を主語に回る。（G_K 作用・非自明 χ は cgar/A7a 後続。） -/
def cmrMu (ℓ : Nat) (hℓ : 1 ≤ ℓ) : CycMuGroup where
  μ := cmrGrp ℓ hℓ
  comm := cmr_comm ℓ hℓ
  ζ := cmrZeta ℓ hℓ
  n := 3 ^ ℓ
  hn := zpu_pow_pos ℓ
  ord := cmr_ord ℓ hℓ
  log := fun y => ctmFind ℓ hℓ y.val
  log_lt := fun z => (ctmFind_spec ℓ hℓ z.val z.property).2
  pow_log := fun z => by
    apply Subtype.ext
    show ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (ctmFind ℓ hℓ z.val)).val = z.val
    rw [cmr_pow_zeta ℓ hℓ (ctmFind ℓ hℓ z.val)]
    exact ((ctmFind_spec ℓ hℓ z.val z.property).1).symm
  distinct := fun i j hij hj heq =>
    ctm_powers_distinct ℓ hℓ i j (Nat.lt_trans hij hj) hj (Nat.ne_of_lt hij)
      (by
        have hval : ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) i).val
            = ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) j).val := congrArg Subtype.val heq
        rw [cmr_pow_zeta ℓ hℓ i, cmr_pow_zeta ℓ hℓ j] at hval
        exact hval)

end IUT
