/-
  IUT/F3Field.lean — F3F: 𝔽₃ の体化（コードベース初の有限 IUTField）

  ── 主要成果の分類: **[実／本物建設(b)]**。

  complete_pct 影響: 柱 A2 の A2a（`Zp3ValuationRing`/z3v 系: ℤ₃ の極大イデアル
  3ℤ₃・剰余体 𝔽₃ の実構成）に併設する本物の代数対象。監査
  `audit/A2-real-padic-local-field-detail-2026-07-10.md` §2.5 の設計に基づき、
  既存の `zmodRing 3`（M38-4・可換環としての ℤ/3）を土台に **本物の逆元 `inv`・
  体公理 `mul_inv_cancel`／`inv_zero`／`zero_ne_one` を完全証明**し、𝔽₃ を
  `IUTField`（M264F-1）の実インスタンスとして昇格する。既存の `IUTField` 実例は
  `ratIUTField`（ℚ・無限体）のみであったため、本ファイルは **コードベース初の
  「有限体」IUTField 実例**を与える。A2a（ℤ₃/3ℤ₃ → 𝔽₃ の環同型 `z3vResToF3` 等）
  および柱 B（局所体の剰余体）が今後 𝔽₃ を体として扱う際の共用部品となる。
  本ファイル単体では complete_pct は未設定（A2a の z3v 側と合わせて後続ラウンドで
  監査・計上する）。

  * F3F-1 `f3Field`         — `IUTField`（台 = `zmodRing 3`・逆元 = 恒等写像）
  * F3F-2 `f3_diff_sq`      — 差の平方恒等式 (a−b)(a+b) = a·a − b·b（choice-free・
    Int core の分配律のみで完全証明。`mul_inv_cancel` の中核補題）
  * F3F-3 非退化検算        — `f3_zero_ne_one` / `f3_one_ne_two` / `f3_zero_ne_two`
    （[0] ≠ [1] ≠ [2] ≠ [0]、𝔽₃ が本当に 3 元体であることの直接検算）
  * F3F-4 具体検算          — `f3_check_two`（x = [2] での `mul_inv_cancel` の
    具体代入。2·2 = 4 ≡ 1 (mod 3) を実際に走らせる）

  ## 本物性の核心（設計 §2.5 の p=3 特有の事実）
  (ℤ/3)^× = {[1],[2]} は位数 2 の群で、[1]²=[1]・[2]²=[4]=[1] だから
  **任意の非零元 x に対して x⁻¹ = x**。よって総 inv（判定不要の関数
  `fun x => x`）がそのまま体の逆元公理を満たす。これは p = 3 に特有の現象
  （一般の 𝔽_p や 𝔽_q では (ℤ/p)^× の位数が 2 を超えるため成立しない）であり、
  コードベース初の「total inv を持つ有限 IUTField」を判定なしに与える。

  ## choice-free 性・正直な限定（§3.1/3.3 準拠・消去禁止）
  - 全て選択公理不使用（新規 `Classical.choice` 導入なし）。`mul_inv_cancel` の
    非零性の判定は `¬ 3∣a → a%3=1 ∨ a%3=2` という **有限（Nat/Int の具体 modulus
    3 の）omega 決定可能命題**であり、§3.1 で述べる「ℚ_p の total inv は
    Markov 原理を要し choice-free 不可能」という限定には抵触しない
    （p=3 の有限体は決定可能な有限分岐なので排中律も選択公理も不要）。
  - **正直な限定（消去しない）**: 本ファイルは p = 3 に固定した実例のみ。一般の
    素数 p・素数冪 q の 𝔽_p / 𝔽_q への一般化（(ℤ/p)^× の構造論・原始根・巡回群
    としての単数群の一般証明）は後続。𝔽₃ の体としての位相・ガロア理論・
    A2a の剰余体同型 `z3vResToF3` との接続も本ファイルの範囲外（A2a 併設ファイル
    として独立に構成し、統合は親ラウンドで行う）。
-/
import IUT.Field

namespace IUT

/-! ## F3F-2: 差の平方恒等式（choice-free・Int core のみ） -/

/-- **F3F-2: 差の平方恒等式** — (a−b)(a+b) = a·a − b·b。`Int.mul_add`/
    `Int.sub_mul`/`Int.mul_comm` の分配律のみで閉じる（`ring` 不使用）。
    `mul_inv_cancel` の中核（b = 1 で使用: (a−1)(a+1) = a·a − 1）。 -/
theorem f3_diff_sq (a b : Int) : (a - b) * (a + b) = a * a - b * b := by
  rw [Int.mul_add, Int.sub_mul, Int.sub_mul, Int.mul_comm b a]
  generalize a * a = P
  generalize a * b = Q
  generalize b * b = R
  omega

/-! ## F3F-1: 𝔽₃ の体化 -/

/-- **F3F-1: 𝔽₃ は本物の体** — 台は `zmodRing 3`（M38-4）。総 inv = 恒等写像
    （p=3 特有: (ℤ/3)^× = {[1],[2]} は位数 2 で x² = 1、よって x⁻¹ = x）。
    `mul_inv_cancel` は代表 a（x ≠ 0 ⟹ 3∤a）を `Quot.ind` で開き、
    a % 3 ∈ {1,2} の 2 枝で `f3_diff_sq` を用いて a·a − 1 = (a−1)(a+1) の
    一方の因子が 3 の倍数であることから閉じる。コードベース初の「有限体」
    `IUTField` 実例。 -/
def f3Field : IUTField where
  toCRing := zmodRing 3
  inv := fun x => x
  mul_inv_cancel := by
    intro x
    induction x using Quot.ind
    rename_i a
    change Int at a
    intro hx
    have ha : ¬ (3 : Int) ∣ a := by
      intro hdvd
      apply hx
      show Quot.mk (modCong 3).rel a = Quot.mk (modCong 3).rel 0
      apply Quot.sound
      show (3 : Int) ∣ (a - 0)
      rw [Int.sub_zero]
      exact hdvd
    show Quot.mk (modCong 3).rel (a * a) = Quot.mk (modCong 3).rel 1
    apply Quot.sound
    show (3 : Int) ∣ (a * a - 1)
    have hmod : a % 3 = 1 ∨ a % 3 = 2 := by omega
    have hd : (a - 1) * (a + 1) = a * a - 1 * 1 := f3_diff_sq a 1
    cases hmod with
    | inl h1 =>
        have hfac : (3 : Int) ∣ (a - 1) := by omega
        obtain ⟨k, hk⟩ := hfac
        refine ⟨k * (a + 1), ?_⟩
        have hexp : (a - 1) * (a + 1) = 3 * (k * (a + 1)) := by
          rw [hk, Int.mul_assoc]
        omega
    | inr h2 =>
        have hfac : (3 : Int) ∣ (a + 1) := by omega
        obtain ⟨k, hk⟩ := hfac
        refine ⟨(a - 1) * k, ?_⟩
        have hexp : (a - 1) * (a + 1) = 3 * ((a - 1) * k) := by
          rw [hk, ← Int.mul_assoc, Int.mul_comm (a - 1) 3, Int.mul_assoc]
        omega
  inv_zero := rfl
  zero_ne_one := by
    intro h
    have hc : (3 : Int) ∣ ((0 : Int) - 1) :=
      quot_exact intGrp (modCong 3) h
    obtain ⟨k, hk⟩ := hc
    omega

/-! ## F3F-3: 非退化検算（𝔽₃ が本当に 3 元体であること） -/

/-- **F3F-3a**: [0] ≠ [1]（体公理の再掲）。 -/
theorem f3_zero_ne_one : f3Field.zero ≠ f3Field.one := f3Field.zero_ne_one

/-- **F3F-3b**: [1] ≠ [2]（分離の根拠: [1]=[2] なら `quot_exact` で
    3 ∣ (1−2) = 3∣(−1) が従うが、これは偽）。 -/
theorem f3_one_ne_two :
    Quot.mk (modCong 3).rel 1 ≠ Quot.mk (modCong 3).rel 2 := by
  intro h
  have hc : (3 : Int) ∣ ((1 : Int) - 2) := quot_exact intGrp (modCong 3) h
  obtain ⟨k, hk⟩ := hc
  omega

/-- **F3F-3c**: [0] ≠ [2]（3 ∤ (0−2) = −2）。 -/
theorem f3_zero_ne_two :
    f3Field.zero ≠ Quot.mk (modCong 3).rel 2 := by
  intro h
  have hc : (3 : Int) ∣ ((0 : Int) - 2) := quot_exact intGrp (modCong 3) h
  obtain ⟨k, hk⟩ := hc
  omega

/-! ## F3F-4: 具体検算（x = [2] での mul_inv_cancel の実走行） -/

/-- [2] ≠ 0（`f3_zero_ne_two` の対称形）。 -/
theorem f3_two_ne_zero : Quot.mk (modCong 3).rel 2 ≠ f3Field.zero :=
  fun h => f3_zero_ne_two h.symm

/-- **F3F-4: 具体検算** — 2·2 = 4 ≡ 1 (mod 3) を `mul_inv_cancel` の実代入で
    確認する（`f3Field.inv` が恒等写像であることも込み）。 -/
theorem f3_check_two :
    f3Field.mul (Quot.mk (modCong 3).rel 2) (f3Field.inv (Quot.mk (modCong 3).rel 2))
      = f3Field.one :=
  f3Field.mul_inv_cancel (Quot.mk (modCong 3).rel 2) f3_two_ne_zero

end IUT
