/-
  IUT/CyclotomicGKActionReal.lean — CGAR（柱A7 実円分剛性の本丸 A7a: 実
  Gal(ℚ(ζ_{3^ℓ})/ℚ) の実 μ_{3^ℓ} への実作用＋非自明な円分指標 χ）

  ── 主要成果の分類: **[実／昇格(a)]**（骨格・模型・代理でなく、実 ℚ・実円分体
     ℚ(ζ_{3^ℓ}) = ℚ[x]/(Φ_{3^ℓ}) の中の実 μ_{3^ℓ}（cmr `cmrMu`）へ、実 Galois 群
     Gal(ℚ(ζ_{3^ℓ})/ℚ)=`galoisGroupGrp (cteExt ℓ hℓ)` が**体自己同型の制限**として
     作用する実 `CycGKAction`（`cgarAct`）を構成し、M322F 抽象枠の**実充填**を行う。
     さらに代入自己同型 σ₂=`cciFromUnits ⟨2,…⟩` の円分指数がちょうど 2 であること
     （`cgar_sigma2_exp`）と、それが単位元の指数 1 と異なること（`cgar_nontrivial`）で
     **非自明な円分指標 χ（σ(ζ)=ζ^a, a≠1）**を実 μ 上に実現する）。

  **complete_pct 影響**: A7（実円分剛性）A7a 完成——**実 Gal(ℚ(ζ_{3^ℓ})/ℚ) の実
  μ_{3^ℓ} への実作用＋非自明円分指標 χ（σ₂→2≠1）**で、M322F の「抽象 GK＋ℤ/n 模型
  `cycMuStd`＋trivial 作用 `cycTrivialAction`（χ≡1）」＝実例 `cycRigGaloisExample`
  を実主語へ昇格する。これにより M322F 正直申告（`CyclotomicRigidity.lean:71-73`
  「非自明な χ（σ(ζ)=ζ^a, a≠1）を与える実 Galois 自己同型の μ_n への降下は後続」）を
  本ファイルで discharge する。graph-meta.json A complete_note の名指し surrogate
  「円分剛性は抽象 GK+ℤ/n 模型」を実 Gal×実 μ×非自明 χ で置換。本ファイルで A7 の
  complete_pct 前進（設計見込み A7 0→0.15-0.2・柱A 40→42）を独立監査に諮る。

  内容（設計 audit/A7-real-cyclotomic-rigidity-detail-2026-07-10.md §2・CGAR-1〜6）:
   * `cgarRestrict ℓ hℓ σ`  — σ の μ_{3^ℓ} への制限（G-同変な群準同型 Hom cmrGrp cmrGrp。
     根の保存は `ctr_rpow_hom_gen`＋σ.map_one、乗法保存は σ.map_mul）。CGAR-1。
   * `cgarAct ℓ hℓ`         — ★実 `CycGKAction`（M322F 抽象枠 `CycGKAction` の実充填。
     act=cgarRestrict・act_one/act_mul は fieldAutId/fieldAutComp の defeq）。CGAR-2。
   * `cgar_exp_eq`          — M322F 抽象 χ 抽出 `cycRigExp` = 実指標 `ctr_charG`（rfl 合流）。CGAR-3。
   * `cgar_charG_id`/`cgar_one_exp` — 単位元の円分指数は 1（id 作用・ctmFind(ζ)=1）。
   * `cgarSigma2 ℓ hℓ`      — 代入自己同型 σ₂=`cciFromUnits ⟨2,…⟩`。CGAR-4。
   * `cgar_sigma2_exp`      — χ(σ₂)=2（`cci_charG_csaAut`）。
   * `cgar_nontrivial`      — ★χ(σ₂)=2 ≠ 1=χ(1)（非自明 χ の実現・M322F :71-73 の discharge）。CGAR-4。
   * `cgar_rigidity`        — 実主語剛性 σ_g(z)=ζ^{χ(g)·log z}（`cycRig_rigidity` の実主語版）。CGAR-5。
   * `cgarRigidityData`     — ★M322F capstone `CyclotomicRigidityData` の実主語版
     （旧実例 `cycRigGaloisExample`＝ℤ/n 模型+trivial χ の置換）。CGAR-5。
   * `cgarRecChar`          — M334F `cycRecCharacter` の実 witness（復元機構の入力昇格）。CGAR-6。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   **p = 3・円分切片限定**: 実現する G は Gal(ℚ(ζ_{3^ℓ})/ℚ)（G_ℚ の可解商）で
         あって、実絶対 Galois 群 G_K そのもの・実局所体 G_{K_v} 上の円分指標ではない。
   (ii)  μ は円分体自身の中の μ_{3^ℓ}⊂ℚ(ζ_{3^ℓ})^× であり、分離閉包 K̄ の μ_n(K̄) でも
         π₁ の幾何的 cyclotome でもない。
   (iii) χ を π₁^ét 位相群の連続指標として抽出する本丸（mono-theta 環境の円分剛性）は
         M334F 同様に依然後続——弱めず継承。
   (iv)  剛性の (ℤ/3^ℓ)^× 不定性（可換群 μ に残る全冪写像の不定性）は cra（A7c）で
         正直定理として固定する。既存 surrogate（M322F `cycRigGaloisExample`・M334F
         入力）は消さない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・propext/Quot.sound
  のみ）。禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。許可タクティク（cases/obtain/induction/rw/show/
  refine/exact/apply/intro/generalize/funext/Subtype.ext/omega）のみ使用。3^ℓ は
  omega 不可（`zpu_one_lt`/`zpu_pow_pos` 再利用）。新規ファイル 1 個のみ（共有ファイル
  IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。prefix `cgar`。
-/
import IUT.CyclotomicMuGroupReal
import IUT.CyclotomicCharIso
import IUT.CyclotomicResTower
import IUT.CyclotomicRigidity
import IUT.CyclotomeRecovery

namespace IUT

/-! ## CGAR-1: σ の μ_{3^ℓ} への制限（実 Galois 作用の群準同型） -/

/-- **CGAR-1: σ の μ_{3^ℓ} への制限** — Gal(ℚ(ζ_{3^ℓ})/ℚ) の元 σ（体自己同型）は
    3^ℓ 乗根を 3^ℓ 乗根に送る（`ctr_rpow_hom_gen`＋σ.map_one）ので、μ_{3^ℓ} への
    制限が実 Galois 作用そのもの（模型でなく体自己同型の制限）。乗法保存は σ.map_mul。 -/
def cgarRestrict (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) :
    Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ) where
  map := fun y => ⟨σ.val.toFun y.val, by
    rw [ctr_rpow_hom_gen ℓ hℓ σ.val y.val (3 ^ ℓ), y.property]
    exact σ.val.map_one⟩
  map_mul := fun y z => Subtype.ext (σ.val.map_mul y.val z.val)

/-! ## CGAR-2: 実 CycGKAction（★M322F CycGKAction の実充填・A7a 本丸） -/

/-- **CGAR-2（★A7a 本丸）: 実 `CycGKAction`** — M322F の抽象枠 `CycGKAction`
    （G_K の μ_n への群作用）を、実 Gal(ℚ(ζ_{3^ℓ})/ℚ) の実 μ_{3^ℓ}=`cmrMu` への
    実 Galois 作用で充填する。act=`cgarRestrict`、単位則 act_one は
    `galoisGroupGrp` の one.val=fieldAutId（恒等 toFun）、合成則 act_mul は
    mul.val=fieldAutComp（σ∘τ の toFun）——いずれも Subtype.ext rfl（defeq）。 -/
def cgarAct (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    CycGKAction (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) where
  act := cgarRestrict ℓ hℓ
  act_one := fun z => Subtype.ext rfl
  act_mul := fun σ τ z => Subtype.ext rfl

/-! ## CGAR-3: 指標の合流（抽象 χ 抽出 = 実指標 ctr_charG） -/

/-- **CGAR-3: 指標の合流** — M322F の抽象円分指数 `cycRigExp`（M.log(σ ζ) の抽出）は、
    実指標 `ctr_charG`（ctmFind(σ ζ)）にちょうど一致する（cmrZeta.val=ctmZeta・
    cmrMu.log=ctmFind の defeq 経由で rfl 合流）。 -/
theorem cgar_exp_eq (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) :
    cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ
      = ctr_charG ℓ hℓ σ.val := rfl

/-! ## CGAR-3b: 単位元の円分指数は 1 -/

/-- **CGAR-3b-i: 恒等自己同型の実指標は 1** — id(ζ)=ζ=ζ^1（`ctm_pow_one`）ゆえ
    ctmPow 1 = ctmPow (char id)、両者 < 3^ℓ の相異性（`cci_indexG`）で char id = 1。 -/
theorem cgar_charG_id (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    ctr_charG ℓ hℓ (fieldAutId (cteField ℓ hℓ)) = 1 := by
  have hz : (fieldAutId (cteField ℓ hℓ)).toFun (ctmZeta ℓ hℓ) = ctmPow ℓ hℓ 1 := by
    show ctmZeta ℓ hℓ = ctmPow ℓ hℓ 1
    exact (ctm_pow_one ℓ hℓ).symm
  have hspec : (fieldAutId (cteField ℓ hℓ)).toFun (ctmZeta ℓ hℓ)
      = ctmPow ℓ hℓ (ctr_charG ℓ hℓ (fieldAutId (cteField ℓ hℓ))) :=
    ctr_charG_spec ℓ hℓ (fieldAutId (cteField ℓ hℓ))
  have h : ctmPow ℓ hℓ 1
      = ctmPow ℓ hℓ (ctr_charG ℓ hℓ (fieldAutId (cteField ℓ hℓ))) := by
    rw [← hz, hspec]
  have hidx := cci_indexG ℓ hℓ 1 (ctr_charG ℓ hℓ (fieldAutId (cteField ℓ hℓ)))
    (ctr_charG_lt ℓ hℓ (fieldAutId (cteField ℓ hℓ))) h
  rw [Nat.mod_eq_of_lt (zpu_one_lt ℓ hℓ)] at hidx
  exact hidx.symm

/-- **CGAR-3b-ii: 単位元の円分指数は 1** — `cgar_exp_eq`（one 側）＋`cgar_charG_id`。 -/
theorem cgar_one_exp (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ)
        (galoisGroupGrp (cteExt ℓ hℓ)).one = 1 := by
  rw [cgar_exp_eq ℓ hℓ (galoisGroupGrp (cteExt ℓ hℓ)).one]
  show ctr_charG ℓ hℓ (fieldAutId (cteField ℓ hℓ)) = 1
  exact cgar_charG_id ℓ hℓ

/-! ## CGAR-4: 非自明な χ（代入自己同型 σ₂・M322F 正直申告 :71-73 の discharge） -/

/-- **CGAR-4a: 2 < 3^ℓ**（ℓ ≥ 1・`zpu_one_lt` と同型の技法）。 -/
theorem cgar_two_lt (ℓ : Nat) (hℓ : 1 ≤ ℓ) : 2 < 3 ^ ℓ := by
  obtain ⟨k, hk⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  rw [hk, Nat.pow_succ]
  have hp : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by omega)
  omega

/-- **CGAR-4b: 2 ∈ (ℤ/3^ℓ)^×** の担体元（2 < 3^ℓ・¬3∣2）。 -/
def cgarTwo (ℓ : Nat) (hℓ : 1 ≤ ℓ) : (zpuGrp ℓ hℓ).carrier :=
  ⟨2, cgar_two_lt ℓ hℓ, by intro h; obtain ⟨k, hk⟩ := h; omega⟩

/-- **CGAR-4c: 代入自己同型 σ₂** — `cciFromUnits` で (ℤ/3^ℓ)^× の元 2 を実 Galois
    自己同型 σ₂ ∈ Gal(ℚ(ζ_{3^ℓ})/ℚ)（σ₂(ζ)=ζ²）へ送る。非自明 χ の実 Galois witness。 -/
def cgarSigma2 (ℓ : Nat) (hℓ : 1 ≤ ℓ) : (galoisGroupGrp (cteExt ℓ hℓ)).carrier :=
  (cciFromUnits ℓ hℓ).map (cgarTwo ℓ hℓ)

/-- **CGAR-4d: χ(σ₂)=2** — `cgar_exp_eq`＋`cci_charG_csaAut`（char(σ_a)=a）。 -/
theorem cgar_sigma2_exp (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ)
        (cgarSigma2 ℓ hℓ) = 2 := by
  rw [cgar_exp_eq ℓ hℓ (cgarSigma2 ℓ hℓ)]
  exact cci_charG_csaAut ℓ hℓ (cgarTwo ℓ hℓ)

/-- **CGAR-4e（★非自明 χ・A7a のヘッドライン）: χ(σ₂)=2 ≠ 1=χ(1)** — 実 Gal の
    実 μ_{3^ℓ} 上の円分指標が非自明値を取る（M322F の trivial χ≡1 実例を実 μ×非自明 χ で
    置換）。M322F 正直申告 `CyclotomicRigidity.lean:71-73` の本 discharge。Nat 指数レベルで
    分離を述べる。 -/
theorem cgar_nontrivial (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ)
        (cgarSigma2 ℓ hℓ)
      ≠ cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ)
        (galoisGroupGrp (cteExt ℓ hℓ)).one := by
  rw [cgar_sigma2_exp ℓ hℓ, cgar_one_exp ℓ hℓ]
  omega

/-! ## CGAR-5: 剛性の実主語インスタンス化（M322F 定理の主語昇格） -/

/-- **CGAR-5a: 実主語円分剛性** — σ_g(z)=ζ^{χ(g)·log z}。実 Gal(ℚ(ζ_{3^ℓ})/ℚ) の
    実 μ_{3^ℓ} への作用が実円分指標 χ で一意に決定される（`cycRig_rigidity` の実主語版）。 -/
theorem cgar_rigidity (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) (y : cmrCarrier ℓ hℓ) :
    ((cgarAct ℓ hℓ).act σ).map y
      = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ)
          (cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ
            * ctmFind ℓ hℓ y.val) :=
  cycRig_rigidity (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ y

/-- **CGAR-5b（★旧模型実例の置換）: 実主語円分剛性データ** — M322F capstone
    `CyclotomicRigidityData` を実 Gal(ℚ(ζ_{3^ℓ})/ℚ)・実 μ_{3^ℓ}=`cmrMu`・実作用
    `cgarAct` で組む。旧実例 `cycRigGaloisExample`（G_ℚ trivial 塔＋ℤ/n 模型＋χ≡1）の
    実主語版であり、M322F の全定理（χ 準同型・単元性・剛性）が実 μ_{3^ℓ} を主語に回る。 -/
def cgarRigidityData (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    CyclotomicRigidityData (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) :=
  cycRigData (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ)

/-! ## CGAR-6: M334F 抽象 χ データの実 witness（復元機構の入力昇格） -/

/-- **CGAR-6: 実円分指標データ** — M334F の抽象 χ 入力 `cycRecCharacter` を、実 Gal の
    実 μ_{3^ℓ} 作用から抽出した実円分指標 `cycRigChar`（準同型・χ(1)=1・単元値は M322F）で
    充填する。これにより M334F の復元機構（`cycRecAction` 等）が実 χ を入力に持つ。
    （M334F の「χ を π₁^ét 位相群の連続指標として抽出」は依然後続——弱めず継承。） -/
def cgarRecChar (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    cycRecCharacter (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) :=
  cycRecCharOfAction (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ)

end IUT
