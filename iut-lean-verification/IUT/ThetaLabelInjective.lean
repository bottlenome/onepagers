/-
  IUT/ThetaLabelInjective.lean — M212F: テータ値ラベルの単射性（柱E・並行部品）

  柱E 残課題 E-1（#39）の**単射性**切片。M209F（ThetaValueEval.lean）は
  テータ値の q-指数が `thetaValExp j = j²` であること・その差分方程式
  F(j+1) = F(j) + 2j + 1, F(0) = 0 からの強制・±1/orbitRep 軌道ラベルの
  上での mod l well-defined 性（**軌道が一致すれば値指数が合同**）まで
  を閉じ、逆向き——**相異なるラベルが相異なるテータ値を与える（mod l）**
  ——を l の素数性（Euclid 補題）を要する未形式化として残していた。

  本モジュールはその未閉部を **M32（Fermat.lean）の Euclid 補題**
  （`euclid`: p 素数・p ∣ ab ⟹ p ∣ a ∨ p ∣ b、Bézout 経由・構成的）で
  **無条件に**閉じる。核心は

    j² ≡ j'² (mod l)  ⟹  l ∣ (j'−j)(j'+j)
      ⟹（l 素数・Euclid）  l ∣ (j'−j) または l ∣ (j'+j)
      ⟹（1 ≤ j, j' ≤ l⋇ = (l−1)/2 なので |j'−j| < l かつ 0 < j'+j < l）
        j'−j = 0、すなわち j = j'

  という古典的な平方剰余の単射性論法を、mathlib 不使用・選択公理不使用で
  形式化したもの。

  * M212F-1 `sq_diff_factor` — 二乗差の因数分解 (a−b)(a+b) = a·a − b·b（Int）。
  * M212F-2 `theta_cong_dvd` — j² ≡ j'² (mod l) から l ∣ (j'−j)(j'+j)（Nat）。
  * M212F-3 `theta_label_inj_le` — j ≤ j' の場合の単射性（Euclid + 範囲）。
  * M212F-4 `theta_label_injective`（**本丸**）— 1 ≤ j, j' ≤ l⋇ かつ
    thetaValExp j ≡ thetaValExp j' (mod l) ⟹ j = j'（無条件）。
  * M212F-5 総括レコード `ThetaLabelInjectiveData` / `…` / `…_exists`。

  意義: M209F の**値↔ラベル対応を真の単射へ完成**させる。M209F は
  「軌道一致 ⟹ 値合同」（well-defined、写像の存在）までだったのに対し、
  本層は「値合同 ⟹ ラベル一致」（単射）を素数性から閉じ、テータ値
  q^{1²}, …, q^{l⋇²} が {±1}-軌道ラベル {1, …, l⋇} で**過不足なく
  一意に**添字付けられること（mod l での l⋇ 個の相異なる値）を確立する。

  正直な限定: 本モジュールは Euclid 補題（M32、既形式化・選択公理不使用）
  により**無条件**に単射性を閉じる（Euclid-条件付きではない）。ただし
  扱うのは値の**指数簿記 j² の mod l 合同**のみ——完全な評価同型
  （エタールテータ関数値そのものの構成）、ガロア同変な p 進テータ値、
  tempered π₁ の商としての実現は M209F 同様 E-1 残として未形式化。
  素数性は仮定 `IsPrime l`（= M32 の定義）として受け、l = 2l⋇+1 の
  奇数構造と併せて用いる。全て選択公理不使用（M209F/M32 から継承、
  新規 Classical なし）。サブエージェント並行部品。
-/
import IUT.ThetaValueEval
import IUT.Fermat

namespace IUT

/-! ## M212F-1: 二乗差の因数分解（Int） -/

/-- **定理 (M212F-1): 二乗差の因数分解** — (a − b)(a + b) = a·a − b·b（Int）。
    平方剰余の単射性論法の代数的核。 -/
theorem sq_diff_factor (a b : Int) :
    (a - b) * (a + b) = a * a - b * b := by
  rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
  generalize a * a = A
  generalize a * b = B
  generalize b * b = D
  omega

/-! ## M212F-2: 値合同から因数への可除性（Nat） -/

/-- **定理 (M212F-2): 値合同 ⟹ 因数の可除性** — j ≤ j' で
    thetaValExp j' ≡ thetaValExp j (mod l)、すなわち
    (j')² = j² + l·k なら、l ∣ (j' − j)(j' + j)（Nat の可除性）。
    二乗差 (j')² − j² = (j' − j)(j' + j) の因数分解と natCast の整合。 -/
theorem theta_cong_dvd (l j j' : Nat) (hle : j ≤ j')
    (hcong : ∃ k : Int, thetaValExp (j' : Int) = thetaValExp (j : Int) + (l : Int) * k) :
    l ∣ (j' - j) * (j' + j) := by
  obtain ⟨k, hk⟩ := hcong
  have hk' : (j' : Int) * (j' : Int) = (j : Int) * (j : Int) + (l : Int) * k := hk
  have hdvdInt : ((l : Nat) : Int) ∣ (((j' - j) * (j' + j) : Nat) : Int) := by
    refine ⟨k, ?_⟩
    have hc1 : (((j' - j) * (j' + j) : Nat) : Int)
        = ((j' : Int) - (j : Int)) * ((j' : Int) + (j : Int)) := by
      rw [Int.natCast_mul]
      have e1 : ((j' - j : Nat) : Int) = (j' : Int) - (j : Int) := by omega
      have e2 : ((j' + j : Nat) : Int) = (j' : Int) + (j : Int) := by omega
      rw [e1, e2]
    rw [hc1, sq_diff_factor (j' : Int) (j : Int)]
    -- 目標: (j')² − j² = l·k、hk' より
    omega
  exact Int.ofNat_dvd.mp hdvdInt

/-! ## M212F-3: 単射性（j ≤ j' の場合） -/

/-- **補題 (M212F-3): 単射性（順序付き）** — l = 2L+1 が素数、
    1 ≤ j ≤ L、1 ≤ j' ≤ L、j ≤ j' かつ値指数が mod l で合同なら j = j'。
    l ∣ (j'−j)(j'+j) を Euclid で分解: l ∣ (j'−j) は |j'−j| < l から
    j'−j = 0、l ∣ (j'+j) は 0 < j'+j < l から矛盾。 -/
theorem theta_label_inj_le (l L : Nat) (hodd : l = 2 * L + 1) (hp : IsPrime l)
    (j j' : Nat) (hj : 1 ≤ j) (hjL : j ≤ L) (hj' : 1 ≤ j') (hj'L : j' ≤ L)
    (hle : j ≤ j')
    (hcong : ∃ k : Int, thetaValExp (j' : Int) = thetaValExp (j : Int) + (l : Int) * k) :
    j = j' := by
  have hdvd : l ∣ (j' - j) * (j' + j) := theta_cong_dvd l j j' hle hcong
  cases euclid l hp hdvd with
  | inl hld =>
    -- l ∣ (j' − j)、0 ≤ j' − j ≤ L − 1 < l なので j' − j = 0
    have hd0 : (j' - j) = 0 := Nat.eq_zero_of_dvd_of_lt hld (by omega)
    omega
  | inr hls =>
    -- l ∣ (j' + j)、0 < j' + j ≤ 2L < l なので j' + j = 0、矛盾
    have hs0 : (j' + j) = 0 := Nat.eq_zero_of_dvd_of_lt hls (by omega)
    omega

/-! ## M212F-4: 単射性（本丸） -/

/-- **定理 (M212F-4): テータ値ラベルの単射性（本丸・無条件）** —
    l = 2L+1 が素数、1 ≤ j, j' ≤ L（= l⋇）で値指数が mod l で合同
    （thetaValExp j' ≡ thetaValExp j）なら j = j'。
    相異なるラベル {1, …, l⋇} は相異なるテータ値 q^{j²}（mod l）を与える。
    M209F の「軌道一致 ⟹ 値合同」の逆——値の単射性——を Euclid 補題
    （M32、素数性）で無条件に閉じる。 -/
theorem theta_label_injective (l L : Nat) (hodd : l = 2 * L + 1) (hp : IsPrime l)
    (j j' : Nat) (hj : 1 ≤ j) (hjL : j ≤ L) (hj' : 1 ≤ j') (hj'L : j' ≤ L)
    (hcong : ∃ k : Int, thetaValExp (j' : Int) = thetaValExp (j : Int) + (l : Int) * k) :
    j = j' := by
  cases Nat.le_total j j' with
  | inl hle => exact theta_label_inj_le l L hodd hp j j' hj hjL hj' hj'L hle hcong
  | inr hge =>
    -- 対称化: 合同を反転（k ↦ −k）して j' ≤ j 側の補題を適用
    obtain ⟨k, hk⟩ := hcong
    have hswap : ∃ m : Int,
        thetaValExp (j : Int) = thetaValExp (j' : Int) + (l : Int) * m := by
      refine ⟨-k, ?_⟩
      rw [Int.mul_neg]
      omega
    have hji : j' = j :=
      theta_label_inj_le l L hodd hp j' j hj' hj'L hj hjL hge hswap
    omega

/-! ## M212F-5: 総括レコード -/

/-- **M212F-5a: テータ値ラベル単射性データ** — 二乗差の因数分解・
    値合同からの可除性・そして無条件の単射性（1 ≤ j, j' ≤ l⋇ かつ値合同
    ⟹ j = j'）の一括束ね。M209F の値↔ラベル well-defined を単射へ完成。 -/
structure ThetaLabelInjectiveData (l L : Nat) (hodd : l = 2 * L + 1)
    (hp : IsPrime l) where
  /-- 二乗差の因数分解 (a−b)(a+b) = a·a − b·b。 -/
  sq_factor : ∀ a b : Int, (a - b) * (a + b) = a * a - b * b
  /-- 値合同 ⟹ 因数の可除性: j ≤ j'、値合同 ⟹ l ∣ (j'−j)(j'+j)。 -/
  cong_dvd : ∀ j j' : Nat, j ≤ j' →
    (∃ k : Int, thetaValExp (j' : Int) = thetaValExp (j : Int) + (l : Int) * k) →
    l ∣ (j' - j) * (j' + j)
  /-- 単射性（本丸）: 1 ≤ j, j' ≤ L かつ値合同 ⟹ j = j'。 -/
  injective : ∀ j j' : Nat, 1 ≤ j → j ≤ L → 1 ≤ j' → j' ≤ L →
    (∃ k : Int, thetaValExp (j' : Int) = thetaValExp (j : Int) + (l : Int) * k) →
    j = j'

/-- **M212F-5b: witness 本体** — 全フィールドを M212F-1〜4 で埋める。 -/
def thetaLabelInjectiveData (l L : Nat) (hodd : l = 2 * L + 1) (hp : IsPrime l) :
    ThetaLabelInjectiveData l L hodd hp where
  sq_factor := sq_diff_factor
  cong_dvd := fun j j' hle hcong => theta_cong_dvd l j j' hle hcong
  injective := fun j j' hj hjL hj' hj'L hcong =>
    theta_label_injective l L hodd hp j j' hj hjL hj' hj'L hcong

/-- **定理 (M212F-5c): テータ値ラベル単射性データの存在（M212F 見出し）** —
    l = 2l⋇+1 が素数なら、テータ値ラベルの単射性データが存在する。
    M209F の値↔ラベル well-defined 対応が真の単射（相異なる {1,…,l⋇}
    ラベル ⟹ 相異なるテータ値 mod l）へ完成する。 -/
theorem thetaLabelInjective_exists (l L : Nat) (hodd : l = 2 * L + 1)
    (hp : IsPrime l) :
    Nonempty (ThetaLabelInjectiveData l L hodd hp) :=
  ⟨thetaLabelInjectiveData l L hodd hp⟩

end IUT

#print axioms IUT.theta_label_injective
#print axioms IUT.thetaLabelInjective_exists
