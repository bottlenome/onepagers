/-
  IUT/CyclotomicEmbedTower.lean — CTE（一般 n 円分塔の各段の体
  ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ}) と段間の埋め込み ι_n : ℚ(ζ_{3ⁿ}) ↪ ℚ(ζ_{3^{n+1}})）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・
     実円分体 ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ}) の上での本物の体化と、段間の本物の体
     埋め込み ι_n を **最初から n 引数で** 構成する。x̄_{3ⁿ} ↦ x̄_{3^{n+1}}³
     の担体写像 `cteMap`（= stretch）が環準同型をなすこと、とりわけ乗法性
     `cteMap_mul` を、CE39 の「余因子定数」短絡（nf=2 専用）に頼らず、
     一般段の合同輸送 `cts_cong` + stretch の乗法性 `ctsStretch_mul` + 剰余の
     一意特徴付け `pfdRed_char` の新イディオムで完全証明する（★発見B の解決）。

  **complete_pct 影響**: A3 一般 n 円分塔（M2）の基盤。任意段 ℚ(ζ_{3ⁿ}) の体化
  `cteField` と段間埋め込み `cteIota` を n 一般で本物に構成する。本ファイル
  単体では complete_pct 未設定（0 前進）。A3 一般 n 塔の complete_pct は、
  一般段機構 M2（ι_n の体埋め込み＝本ファイル・一般 μ の同定 ctm・決定補題
  cae・代入自己同型 csa・制限 ctr）が本物で揃った段（M2 完成＝ctr 到達）で
  反映する。本層はその基盤（各段の体・段間 ι_n）を提供する。

  内容（設計 audit/A3-inverse-limit-roadmap-2026-07-09.md §3.1）:
   * `cteField n hn`  — 各段の体 ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ})（`gefNFIUTField`
     の Φ_{3ⁿ} 実例化・deg = 2·3^{n−1}）。
   * `cteExt n hn`    — 体拡大 ℚ ↪ ℚ(ζ_{3ⁿ})（`gefFieldExtension` の実例化）。
   * `cteMap n hn`    — 担体写像 x̄ ↦ x̄³（= stretch・deg < 2·3^{n−1} ⟹
     stretch deg < 2·3ⁿ ⟹ 次段の NF に簡約不要で収まる）。
   * `cteMap_add / cteMap_one / cteMap_inj / cte_incl_compat` — 加法・1・単射・
     定数埋め込み適合。
   * **`cteMap_mul`** — ★乗法性（発見B の解決コマ）: cts_cong + ctsStretch_mul
     + pfdRed_char で閉じる（一般段の余因子非定数を回避）。
   * `cteIota n hn`   — 段間埋め込み ι_n : RingHom（(cteField n).toCRing →
     (cteField (n+1)).toCRing）。
   * `cteField_two_eq` — cteField 2 と既存 `p9iPhi9Field`（ℚ(ζ_9)）の同定橋
     （ctsPhi_two_eq 越し・引数 Prop は proof-irrelevant）。

  正直な限定（§4 規約により消さない）:
   - **p = 3 に固定**。円分塔は ℚ(ζ_{3ⁿ}) のみ（一般素数 p は本層に含めない）。
   - 本層は **各段の体化 `cteField` と段間の埋め込み ι_n（`cteIota`）まで**。
     ガロア群 Gal・制限準同型 res_n・全射性/分離性/正規性は csa/ctr（後段）。
   - `cteField_two_eq` の同定は cteField 2 = p9iPhi9Field のみ（一般段の cm9
     資産橋は ctm/csa 側で行う）。
   - 埋め込み ι_n は担体写像（体埋め込み）であり、逆向き（制限 res）は cae/ctr。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク（simp/decide/by_cases/rcases/ring/
  nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.CyclotomicStretch
import IUT.EisensteinTowerInput
import IUT.GenExtTower
import IUT.Phi9Irreducible

namespace IUT

/-! ## CTE-0: 3ⁿ の冪算術（omega 不可・手動補題） -/

/-- **CTE-0a: 3^k ≥ 1**（正値・段の次数 2·3^{n−1} ≥ 1 に効く）。 -/
theorem cte_pow3_pos : ∀ k : Nat, 1 ≤ (3 : Nat) ^ k
  | 0 => Nat.le_refl 1
  | k + 1 => by
      have hk := cte_pow3_pos k
      rw [cts_pow3_succ k]
      omega

/-- **CTE-0b: 段の次数の正値** — 2·3^{n−1} ≥ 1（1 ≤ n）。`gefNFIUTField` の
    `1 ≤ nf` 入力。 -/
theorem cte_nf_pos (n : Nat) (hn : 1 ≤ n) : 1 ≤ 2 * 3 ^ (n - 1) := by
  have hp := cte_pow3_pos (n - 1)
  omega

/-- **CTE-0c: 先頭係数非零** — Φ_{3ⁿ} の 2·3^{n−1} 次係数 ≠ 0（= 1・
    `ctsPhi_lead` + `cbp_one_ne_zero`）。`gefNFIUTField` の `f nf ≠ 0` 入力。 -/
theorem cte_lead_ne (n : Nat) (hn : 1 ≤ n) :
    ctsPhi n (2 * 3 ^ (n - 1)) ≠ ratRing.zero :=
  fun h => cbp_one_ne_zero ((ctsPhi_lead n hn).symm.trans h)

/-- **CTE-0d: stretch の次数緩め** — deg < 2·3^{n−1} の w は stretch すると
    deg < 2·3ⁿ（`ctsStretch_bounded` = 3·(N−1)+1 を 2·3ⁿ へ `pbzBound_mono`）。
    段間写像の担体が次段 NF に簡約不要で収まる根拠。 -/
theorem cte_stretch_bound (n : Nat) (hn : 1 ≤ n) {w : PS ratRing}
    (hw : IsPolyBounded ratRing w (2 * 3 ^ (n - 1))) :
    IsPolyBounded ratRing (ctsStretch w) (2 * 3 ^ n) := by
  refine pbzBound_mono ratRing (ctsStretch_bounded hw) ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hp := cte_pow3_pos k
  rw [cts_pow3_succ k, show (k + 1) - 1 = k from by omega]
  omega

/-! ## CTE-1: 各段の体 ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ}) と体拡大 -/

/-- **CTE-1a: 各段の体** — ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ})（全域 inv 付き実体
    `IUTField`）。deg Φ_{3ⁿ} = 2·3^{n−1}・先頭係数 1・既約性 `eitPhi_irreducible`
    の 1 行実例化（設計 §3.1: 最初から n 引数）。 -/
def cteField (n : Nat) (hn : 1 ≤ n) : IUTField :=
  gefNFIUTField (ctsPhi n) (2 * 3 ^ (n - 1))
    (ctsPhi_bound n hn) (cte_lead_ne n hn) (cte_nf_pos n hn) (eitPhi_irreducible n hn)

/-- **CTE-1b: 各段の体拡大** — ℚ ↪ ℚ(ζ_{3ⁿ})（定数埋め込み・次数 2·3^{n−1}・
    `gefFieldExtension` の Φ_{3ⁿ} 実例化）。 -/
def cteExt (n : Nat) (hn : 1 ≤ n) : FieldExtension :=
  gefFieldExtension (ctsPhi n) (2 * 3 ^ (n - 1))
    (ctsPhi_bound n hn) (cte_lead_ne n hn) (cte_nf_pos n hn) (eitPhi_irreducible n hn)

/-! ## CTE-2: 段間の担体写像 x̄_{3ⁿ} ↦ x̄_{3^{n+1}}³（= stretch） -/

/-- **CTE-2: 担体写像** — 次数 < 2·3^{n−1} の NF 元 u を stretch（X ↦ X³）で
    次段 GefNF (Φ_{3^{n+1}}) (2·3ⁿ) へ送る。deg u < 2·3^{n−1} ⟹
    deg (stretch u) < 2·3ⁿ ゆえ次段 NF に簡約不要で収まる（`cte_stretch_bound`）。 -/
def cteMap (n : Nat) (hn : 1 ≤ n) (u : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) :
    GefNF (ctsPhi (n + 1)) (2 * 3 ^ n) :=
  ⟨ctsStretch u.val, cte_stretch_bound n hn u.property⟩

/-! ## CTE-3: 環準同型性（加法・1・単射・定数適合） -/

/-- **CTE-3a: 加法保存** — ι_n(u + v) = ι_n(u) + ι_n(v)（各点線形・
    `ctsStretch_add`・簡約不要）。 -/
theorem cteMap_add (n : Nat) (hn : 1 ≤ n)
    (u v : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) :
    cteMap n hn ((cteField n hn).toCRing.add u v)
      = (cteField (n + 1) (by omega)).toCRing.add (cteMap n hn u) (cteMap n hn v) := by
  apply Subtype.ext
  show ctsStretch (psAdd ratRing u.val v.val)
     = psAdd ratRing (ctsStretch u.val) (ctsStretch v.val)
  exact ctsStretch_add u.val v.val

/-- **CTE-3b: 1 保存** — ι_n(1) = 1（psOne = psC 1 は stretch 不動
    `ctsStretch_psC`）。 -/
theorem cteMap_one (n : Nat) (hn : 1 ≤ n) :
    cteMap n hn (cteField n hn).toCRing.one
      = (cteField (n + 1) (by omega)).toCRing.one := by
  apply Subtype.ext
  show ctsStretch (psOne ratRing) = psOne ratRing
  exact ctsStretch_psC ratRing.one

/-- **CTE-3c: 単射性** — ι_n(u) = ι_n(v) ⟹ u = v（stretch は 3 の倍数次に
    元係数を写す全単射的間引き・`ctsStretch_mul3` で係数を復元）。 -/
theorem cteMap_inj (n : Nat) (hn : 1 ≤ n)
    {u v : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))}
    (h : cteMap n hn u = cteMap n hn v) : u = v := by
  apply Subtype.ext
  funext i
  have hval : ctsStretch u.val = ctsStretch v.val := congrArg Subtype.val h
  have hi := congrFun hval (3 * i)
  rw [ctsStretch_mul3 u.val i, ctsStretch_mul3 v.val i] at hi
  exact hi

/-- **CTE-3d: 定数埋め込み適合** — ι_n ∘ incl_n = incl_{n+1}（基礎体 ℚ の定数
    は stretch 不動 `ctsStretch_psC`）。 -/
theorem cte_incl_compat (n : Nat) (hn : 1 ≤ n) (a : QRat) :
    cteMap n hn (gefIncl (ctsPhi n) (2 * 3 ^ (n - 1)) (cte_nf_pos n hn) a)
      = gefIncl (ctsPhi (n + 1)) (2 * 3 ^ n) (cte_nf_pos (n + 1) (by omega)) a := by
  apply Subtype.ext
  show ctsStretch (psC ratRing a) = psC ratRing a
  exact ctsStretch_psC a

/-! ## CTE-4: ★乗法性（発見B の解決コマ・cts_cong + pfdRed_char） -/

/-- **CTE-4: 乗法保存（★山場）** — ι_n(u·v) = ι_n(u)·ι_n(v)。
    次段 NF 積 pfdRed_{Φ_{3^{n+1}}}(stretch u · stretch v) が
    stretch(pfdRed_{Φ_{3ⁿ}}(u·v)) に一致することを、CE39 の「余因子定数」短絡
    （nf=2 専用・一般 n では余因子非定数）に頼らず、一般段の合同輸送で閉じる:
    (1) NF 積の剰余は元に合同 `gnfCong_red`（mod Φ_{3ⁿ}）、
    (2) それを stretch で持ち上げ `cts_cong`（mod Φ_{3^{n+1}}）、
    (3) `ctsStretch_mul` で stretch(u·v) = stretch u · stretch v、
    (4) 剰余の一意特徴付け `pfdRed_char` で確定。 -/
theorem cteMap_mul (n : Nat) (hn : 1 ≤ n)
    (u v : GefNF (ctsPhi n) (2 * 3 ^ (n - 1))) :
    cteMap n hn ((cteField n hn).toCRing.mul u v)
      = (cteField (n + 1) (by omega)).toCRing.mul (cteMap n hn u) (cteMap n hn v) := by
  apply Subtype.ext
  show ctsStretch (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1))
        (psMul ratRing u.val v.val))
     = pfdRed (ctsPhi (n + 1)) (2 * 3 ^ n) (2 * 3 ^ n)
        (psMul ratRing (ctsStretch u.val) (ctsStretch v.val))
  -- 積の有界性（Φ_{3ⁿ} 側）
  have hbmul : IsPolyBounded ratRing (psMul ratRing u.val v.val)
      (2 * 3 ^ (n - 1) + 2 * 3 ^ (n - 1)) :=
    simpleExt_mul_bounded ratRing u.property v.property
  -- (1) NF 積の剰余 ≡ 積 (mod Φ_{3ⁿ})
  have hred : gnfCong (ctsPhi n)
      (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) (psMul ratRing u.val v.val))
      (psMul ratRing u.val v.val) :=
    gnfCong_red (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
      (2 * 3 ^ (n - 1)) (psMul ratRing u.val v.val) hbmul
  -- (2) stretch で持ち上げ (mod Φ_{3^{n+1}})
  have hlift := cts_cong hn hred
  -- (3) stretch(u·v) = stretch u · stretch v
  have hmuleq : ctsStretch (psMul ratRing u.val v.val)
      = psMul ratRing (ctsStretch u.val) (ctsStretch v.val) := ctsStretch_mul u.val v.val
  rw [hmuleq] at hlift
  have hsym := gnfCong_symm (ctsPhi (n + 1)) hlift
  obtain ⟨hh, ⟨Nhh, hhb⟩, hhe⟩ := hsym
  -- pfdRed_char 用の合同（∃ 形）
  have hcong : ∃ (h : PS ratRing) (Nh : Nat), IsPolyBounded ratRing h Nh ∧
      ∀ j, psAdd ratRing (psMul ratRing (ctsStretch u.val) (ctsStretch v.val))
          (psNeg ratRing (ctsStretch (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1))
            (2 * 3 ^ (n - 1)) (psMul ratRing u.val v.val)))) j
        = psMul ratRing h (ctsPhi (n + 1)) j :=
    ⟨hh, Nhh, hhb, fun j => congrFun hhe j⟩
  -- 有界性: 剰余の担体 v と積 w
  have hv : IsPolyBounded ratRing
      (ctsStretch (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1))
        (psMul ratRing u.val v.val))) (2 * 3 ^ n) :=
    cte_stretch_bound n hn
      (pfdRed_bound (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
        (2 * 3 ^ (n - 1)) (psMul ratRing u.val v.val) hbmul)
  have hw : IsPolyBounded ratRing
      (psMul ratRing (ctsStretch u.val) (ctsStretch v.val)) (2 * 3 ^ n + 2 * 3 ^ n) :=
    simpleExt_mul_bounded ratRing
      (cte_stretch_bound n hn u.property) (cte_stretch_bound n hn v.property)
  funext j
  exact (pfdRed_char (ctsPhi (n + 1)) (2 * 3 ^ n) (ctsPhi_bound (n + 1) (by omega))
    (cte_lead_ne (n + 1) (by omega)) (2 * 3 ^ n)
    (psMul ratRing (ctsStretch u.val) (ctsStretch v.val))
    (ctsStretch (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1))
      (psMul ratRing u.val v.val)))
    hw hv hcong j).symm

/-! ## CTE-5: 段間埋め込み ι_n（RingHom） -/

/-- **CTE-5: 段間埋め込み** — ι_n : ℚ(ζ_{3ⁿ}) ↪ ℚ(ζ_{3^{n+1}})（RingHom・
    担体写像 x̄ ↦ x̄³）。加法・乗法・1 保存は CTE-3/CTE-4。M2 の塔
    ℚ ⊂ ℚ(ζ₃) ⊂ ℚ(ζ_9) ⊂ … の各段間写像を n 一般で本物に供給する。 -/
def cteIota (n : Nat) (hn : 1 ≤ n) :
    RingHom (cteField n hn).toCRing (cteField (n + 1) (by omega)).toCRing where
  map := cteMap n hn
  map_add := cteMap_add n hn
  map_mul := cteMap_mul n hn
  map_one := cteMap_one n hn

/-! ## CTE-6: 同定橋 cteField 2 = p9iPhi9Field（ℚ(ζ_9)） -/

/-- **CTE-6a: 体化の多項式付替** — 法多項式が等しければ体化は等しい（引数の
    Prop hb/hl/hirr は proof-irrelevant なので f の subst のみで確定）。 -/
theorem gefNFIUTField_eq_of_poly_eq {f f' : PS ratRing} {nf : Nat}
    (hff : f = f')
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f)
    (hb' : IsPolyBounded ratRing f' (nf + 1)) (hl' : f' nf ≠ ratRing.zero)
    (hirr' : pibIrreducible ratRing f') :
    gefNFIUTField f nf hb hl hn hirr = gefNFIUTField f' nf hb' hl' hn hirr' := by
  subst hff
  rfl

/-- **CTE-6b: 同定橋** — cteField 2 = p9iPhi9Field（ℚ(ζ_9) = ℚ[x]/(Φ_9)）。
    ctsPhi 2 = cpdPhi9（`ctsPhi_two_eq`）越しの付替（deg 2·3^{2−1}=6 は defeq）。
    後段 ctm/csa が既存 cm9 資産（ℚ(ζ_9)）を使う橋。 -/
theorem cteField_two_eq : cteField 2 (by omega) = p9iPhi9Field :=
  gefNFIUTField_eq_of_poly_eq ctsPhi_two_eq
    (ctsPhi_bound 2 (by omega)) (cte_lead_ne 2 (by omega)) (cte_nf_pos 2 (by omega))
    (eitPhi_irreducible 2 (by omega))
    cpdPhi9_bound p9e_phi9_lead p9i_irreducible

end IUT
