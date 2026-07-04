/-
  IUT/ThetaEvalCapstone.lean — M219F: テータ値評価・l⋇ ラベリングの
  総括 capstone（柱E・並行部品）

  柱E 残課題 E-1（#39）のテータ値評価チェーンを一本化する capstone。
  ここまで独立に閉じてきた三層

    M209F（ThetaValueEval.lean）— テータ値の q-指数 `thetaValExp j = j²`
      の基点・差分方程式・強制（一意性）、± / {±1}-軌道ラベル
      （orbitRep）の上での mod l well-defined 性、Gaussian 座席 tri
      との換算、非単位ラベル範囲 {1,…,l⋇} の一括束ね
      （`ThetaValueEvalData` / `thetaValueEvalData` / `thetaValueEval_exists`）、

    M212F（ThetaLabelInjective.lean）— M209F の「軌道一致 ⟹ 値合同」の
      **逆向き**（値合同 ⟹ ラベル一致）を M32 Euclid 補題（l の素数性）
      で無条件に閉じる単射性
      （`ThetaLabelInjectiveData` / `thetaLabelInjectiveData` /
      `thetaLabelInjective_exists`）、

    M162F（MuLIdentification.lean）— μ_l(O) 側の ±-軌道の完全分類と
      非単位軌道の l⋇ = (l−1)/2 ラベリング、係数シクロトーム同期
      centerToMu の ±-同変性、テータ ± との両側接合
      （`MuLIdentificationData` / `muLIdentificationData` /
      `muLIdentification_exists`）

  を、**新規の数学的証明を一切追加せず**、単一のレコード
  `ThetaEvalData` に束ねる。M209F は l⋇ = (l−1)/2 側の「値↔ラベル」
  の存在（well-defined 写像）、M212F はその単射性、M162F は μ_l(O)
  側の同一視——の三者が同じパラメータ l = 2L+1（+ μ_l 側は素数 p、
  l ∣ p−1）の下で**同時に**成立することを一つの証拠として提示する。

  * M219F-1 `ThetaEvalData` — 三層 Data を束ねる総括レコード
    （フィールド `valueEval : ThetaValueEvalData l L hodd`、
    `labelInjective : ThetaLabelInjectiveData l L hodd hpl`、
    `muLabel : MuLIdentificationData p l L hp hL hodd hdvd`）。
  * M219F-2 `thetaEvalData` — μ_l 生成元 ζ とその証拠
    （root・distinct・teich_form）を明示的に受け取り、三層を
    `thetaValueEvalData` / `thetaLabelInjectiveData` /
    `muLIdentificationData` でそのまま埋める witness 本体。
  * M219F-3 `thetaEval_exists` — ζ の具体形を要求しない存在版。
    三つの `…_exists`（Nonempty）を `obtain` で取り出し
    （目標が `Nonempty (ThetaEvalData …)` という Prop なので
    Prop→Prop の構成的場合分けであり、新規の選択公理は不要）、
    一つの `ThetaEvalData` に組み直す。

  意義: M209F（値指数 j² の強制と well-defined 性）→ M212F（その
  逆向きの単射性）→ M162F（μ_l(O) 側の ± 同一視・l⋇ ラベリング）
  という E-1 のテータ値評価チェーンを、パラメータ整合の下で一つの
  証明レコードとして提示する capstone。新規証明ゼロ（全フィールドは
  既存の `…Data`/`…_exists`/`…theorem` の再輸出）。

  正直な限定: 本 capstone が束ねるのはあくまで
  「値指数 j² の簿記 → ± well-defined → 単射性 → μ_l(O) 側の
  ± 同一視・l⋇ ラベリング」という**離散核**であり、E-1 の残り
  （完全な評価同型＝エタールテータ関数値そのものの構成、ガロア
  同変な p 進テータ値、tempered π₁ の商としての実現）は M209F/
  M212F/M162F 同様、未形式化のまま残る。`thetaEvalData` は
  μ_l 生成元 ζ を明示的な引数として要求する（M162F 自身の
  `muLIdentificationData` と同じ形）。全て選択公理不使用（型継承
  除く: M212F/M209F は M32 Euclid 補題・M2 経由で Classical を
  新規には導入しない）。サブエージェント並行部品。
-/
import IUT.ThetaValueEval
import IUT.ThetaLabelInjective
import IUT.MuLIdentification

namespace IUT

/-! ## M219F-1: 総括レコード -/

/-- **M219F-1: テータ値評価・l⋇ ラベリングの総括データ** — M209F
    （値指数 j² の基点・差分方程式・強制・± well-defined 性・
    tri 換算・非単位ラベル範囲）、M212F（値合同 ⟹ ラベル一致の
    単射性、Euclid 補題により無条件）、M162F（μ_l(O) 側の ±-軌道
    完全分類・l⋇ ラベリング・centerToMu の ±-同変性・テータ ± との
    接合）を一つのレコードに束ねる。パラメータは M212F・M162F 双方
    の要求（l の素数性 `hpl`、p の素数性 `hp` と `l ∣ p − 1`）を
    そのまま引き継ぐ。 -/
structure ThetaEvalData (p l L : Nat) (hp : IsPrime p) (hpl : IsPrime l)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) where
  /-- M209F: 値指数 q^{j²} の基点・差分方程式・強制・± well-defined 性・
      tri 換算・非単位ラベル範囲の一括束ね。 -/
  valueEval : ThetaValueEvalData l L hodd
  /-- M212F: 値合同 ⟹ ラベル一致（1 ≤ j, j' ≤ l⋇）の単射性
      （Euclid 補題により無条件）。 -/
  labelInjective : ThetaLabelInjectiveData l L hodd hpl
  /-- M162F: μ_l(O) の ±-軌道完全分類・l⋇ ラベリング・centerToMu の
      ±-同変性・テータ ± との両側接合。 -/
  muLabel : MuLIdentificationData p l L hp hL hodd hdvd

/-- **M219F-2: witness 本体** — μ_l 生成元 ζ（と root・distinct・
    teich_form の証拠、M162F `muLIdentificationData` と同形）を
    明示的に受け取り、三層のフィールドをそのまま埋める。 -/
def thetaEvalData (p l L : Nat) (hp : IsPrime p) (hpl : IsPrime l)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1)
    (ζ : (Zp p).carrier) (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (ha : ∃ a : Int, ¬ ((p : Nat) : Int) ∣ a ∧ ζ = teich p hp a) :
    ThetaEvalData p l L hp hpl hL hodd hdvd where
  valueEval := thetaValueEvalData l L hodd
  labelInjective := thetaLabelInjectiveData l L hodd hpl
  muLabel := muLIdentificationData p l L hp hL hodd hdvd ζ hζl hdist ha

/-- **M219F-3: 総括データの存在（M219F 見出し・ζ の具体形不要）** —
    p, l 素数・l = 2L+1 ∣ p−1（かつ 1 ≤ L）なら、テータ値評価・
    l⋇ ラベリングの総括データが存在する。M209F/M212F/M162F 各々の
    `…_exists`（Nonempty）を組み合わせるのみ（目標 `Nonempty
    (ThetaEvalData …)` は Prop なので Prop→Prop の構成的場合分け、
    新規の選択公理は不要）。 -/
theorem thetaEval_exists (p l L : Nat) (hp : IsPrime p) (hpl : IsPrime l)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) :
    Nonempty (ThetaEvalData p l L hp hpl hL hodd hdvd) := by
  obtain ⟨d1⟩ := thetaValueEval_exists l L hodd
  obtain ⟨d2⟩ := thetaLabelInjective_exists l L hodd hpl
  obtain ⟨d3⟩ := muLIdentification_exists p l L hp hL hodd hdvd
  exact ⟨{ valueEval := d1, labelInjective := d2, muLabel := d3 }⟩

end IUT
