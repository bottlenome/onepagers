/-
  IUT/RealMultiradialInput.lean — M228F: RealMultiradialInput —
  実数 threading（M216F が「将来層」と宣言した実数値 base の完全 threading の回収・
  柱D Dβ-2・並行部品）

  M215F `MultiradialInput`（Int 値 `MultiradialRep` 上の入力レコード）の
  **実数鏡映**。IUT の正否の局在（`iut_localized`）を、実数値 log-volume
  上の表現 `RealMultiradialRep`（M139）の土俵に持ち上げる。M216F の正直な
  限定に明記された「真のガウスパイロット `gaussPilotRepW` は Int 値要求の
  `Theorem311Rep.base` に型が合わず差し込めない——実数値 base の完全
  threading は将来層」を、実数側の全部品（M139 の実数表現・M159F の実数障害・
  M158F の実ガウスパイロット）を写経＋接合して**回収**する。

  還元の鎖（実数版）は Int 版の中央を実数鏡映したもので、
  `RealMultiradialInput → Cor312` を `cor312_of_realMultiradial`（M139-5b）
  経由で直接降ろす（`RealTheorem311Rep` は不要——既存 `Theorem311Rep` の
  Int 型を一切変更しない）。

  * M228F-1 `RealMultiradialInput` — D-β が供給すべき単一入力レコードの
    実数版:
    - `base`       : 実数値多輻的表現（M139 `RealMultiradialRep`）
    - `padded`     : 膨張整合性の実数版（M159F-6 `padding_necessary_real`）:
      q を実現する可能な像の実数値体積は ≥ intToReal(−|log q|) まで膨張
    - `not_strict` : 障害整合性の実数版（M159F-5
      `strict_evaluation_obstruction_real`）: 不可能な「厳密テータ評価」の
      実数版ではない
  * M228F-2 `realInputOfRep` — 任意の `RealMultiradialRep` から入力を作る
    （二つの障害フィールドは M159F-5/M159F-6 で自動充足）。
  * M228F-3 `cor312_of_realInput` — **局在の下降（実数経由）**:
    実数入力 ⟹ 系3.12。`cor312_of_realMultiradial` の一行還元。
  * M228F-4 `iut_localized_real` — **局在の見出し（実数版）**:
    `Nonempty (RealMultiradialInput V s) → Cor312 s`。
  * M228F-5 `gaussRealInput` — **gaussPilotRepW を base に直接差し込んだ
    実数値入力 witness**。Int 模型でなく本物の実数値体積が入る初の入力
    レコード（Θ-正則包の体積 = `rlogVol w (gaussDiv l)`）。
  * M228F-6 capstone: `RealMultiradialInputData`（構造）/
    `gaussRealInputData`（def; ガウス witness）/ `realMultiradialInput_exists`
    （Nonempty）と、Θ-包体積の同定 `gaussRealInput_vol_theta`。

  ## 意義

  M216F が正直な限定で「実数値 base の完全 threading は将来層」と分離した
  部分の回収。実数側は M139（表現）・M159F（障害）・M158F（実ガウス
  パイロット）で全部品が揃っており、新規イディオムなしの写経＋接合で
  閉じる。これにより Int 版 `MultiradialInput` の局在（`iut_localized`）が
  実数の土俵でも成立し、しかも **Int 模型でなく本物の実数値体積
  `rlogVol w (gaussDiv l)` が入った具体入力 witness `gaussRealInput`** が
  レコードの非空虚性を実証する（Int 版 demo は `m202fVol`・vol = id の
  体積値そのものが領域のデモ模型だったのに対し、こちらは実数値の
  重み付きガウス因子体積が Θ-正則包に入る）。

  ## 正直な限定

  * 実数値ではあるが**依然パイロット模型**である。`gaussPilotRepW` は
    Region = ℝ・vol = id の M139-3b 充足デモ模型上にあり、`gaussSkeletonW`
    の logq = 1 は正規化で実際の q-パイロット値ではない。したがって本層は
    **遠アーベル構成 D-β 本丸**（[AbsTopIII] 環復元・エタールテータ剛性に
    よる `RealMultiradialRep` の構成そのもの）ではなく、M216F/M158F/M139 の
    正直申告を引き継ぐ。回収されたのは「実数値 base への完全 threading（型の
    接合）」であり、「実データでの居住」ではない。
  * 二つの障害フィールド `padded`/`not_strict` は M159F-6/M159F-5 により
    任意の `RealMultiradialRep` に自動充足される（`realInputOfRep` 参照）。
    ゆえに `RealMultiradialInput` の居住可能性は `RealMultiradialRep` の
    居住可能性と等価であり、両フィールドは制約でなく機械検証済みの
    整合性の刻印として付帯する。
  * 重み w は ℕ 値（log p の整数化）。実数値 log p の構成は将来層（M158F と
    同じ限定）。

  継承 Classical: 本モジュール自身は新規 Classical.choice を導入しない。
  下流の M139/M158F/M159F 経由で継承する公理があれば `#print axioms` に
  現れる（propext/Quot.sound の範囲）。sorry なし・禁止タクティク不使用
  （core Lean のみ）。サブエージェント並行部品（tier-M）。
-/
import IUT.RealObstruction
import IUT.GaussPilotWeighted

namespace IUT

/-! ## M228F-1: D-β が供給すべき単一入力レコードの実数版 -/

/-- **M228F-1: `RealMultiradialInput`** — M215F `MultiradialInput` の
    実数鏡映。実数値多輻的表現 `base` に、M159F-5/M159F-6 の機械検証済み
    障害整合性を刻印として付帯させる。

    フィールドと Int 版の対応:
    * `base`       — (i) 実数値多輻的表現（M139 `RealMultiradialRep`）
    * `padded`     — 膨張整合性の実数版（M159F-6）: q-パイロットを実現する
      可能な像の実数値体積は ≥ intToReal(−|log q|) まで膨張
    * `not_strict` — 障害整合性の実数版（M159F-5）: 不可能な「厳密テータ
      評価」の実数版ではない -/
structure RealMultiradialInput (V : RealVolumeTheory) (s : Skeleton) where
  /-- 実数値多輻的表現（M139・D-β のアルゴリズム出力の実数版）。 -/
  base : RealMultiradialRep V s
  /-- 膨張整合性（M159F-6）: 可能な像の実数値体積は ≥ intToReal(−|log q|)。 -/
  padded : ∃ i, rLe (intToReal (-s.logq)) (V.vol (base.image i))
  /-- 障害整合性（M159F-5）: 厳密テータ評価の実数版ではない。 -/
  not_strict : ¬ StrictEvaluationReal base

/-! ## M228F-2: 表現から入力へ（障害フィールドは自動充足） -/

/-- **M228F-2: `realInputOfRep`** — 任意の実数値多輻的表現 `M` から入力
    レコードを構成する。二つの障害フィールドは M159F-6
    `padding_necessary_real` と M159F-5 `strict_evaluation_obstruction_real`
    によって自動的に充足される——ゆえに `RealMultiradialInput` の
    居住可能性は `RealMultiradialRep` の居住可能性と等価（正直な限定）。 -/
def realInputOfRep {V : RealVolumeTheory} {s : Skeleton}
    (M : RealMultiradialRep V s) : RealMultiradialInput V s where
  base := M
  padded := padding_necessary_real M
  not_strict := fun h => strict_evaluation_obstruction_real M h

/-! ## M228F-3: 局在の下降（実数入力 ⟹ 系3.12） -/

/-- **定理 (M228F-3): 実数入力 ⟹ 系3.12** — 局在の下降（実数経由）。
    入力レコードの `base` に M139-5b `cor312_of_realMultiradial` を適用する
    一行の還元。実数値の体積比較 → intToReal 反映 → 整数 Cor312 で
    IUT の最終帰結（−|log q| ≤ −|log Θ|）が実数入力の居住から直ちに従う。 -/
theorem cor312_of_realInput {V : RealVolumeTheory} {s : Skeleton}
    (I : RealMultiradialInput V s) : Cor312 s :=
  cor312_of_realMultiradial I.base

/-! ## M228F-4: 局在の見出し（実数版） -/

/-- **定理 (M228F-4): 局在の見出し（実数版）** — 実数入力レコードが
    居住可能であれば、系3.12 が成り立つ。IUT の正否は
    `Nonempty (RealMultiradialInput V s)` にも局在する（実数の土俵経由）。 -/
theorem iut_localized_real {V : RealVolumeTheory} {s : Skeleton}
    (h : Nonempty (RealMultiradialInput V s)) : Cor312 s := by
  obtain ⟨I⟩ := h
  exact cor312_of_realInput I

/-! ## M228F-5: gaussPilotRepW を base に差し込んだ実数値入力 witness -/

/-- **M228F-5: ガウス実数値入力 witness** — M158F-3 `gaussPilotRepW`
    （Θ-正則包 = 重み付きガウス因子の log-volume `rlogVol w (gaussDiv l)`）を
    `base` に**直接差し込んだ**実数値入力レコード。Int 模型（`m202fVol`・
    vol = id のデモ）でなく、**本物の実数値体積が Θ-包に入る初の入力
    レコード**。障害フィールドは `realInputOfRep` により M159F-5/M159F-6 から
    自動充足される。 -/
def gaussRealInput (w : Nat → Nat) (l : Nat) :
    RealMultiradialInput realVolumeTheory (gaussSkeletonW w l) :=
  realInputOfRep (gaussPilotRepW w l)

/-! ## M228F-6: capstone — Data / def / exists（レコードの非空虚性） -/

/-- **M228F-6a: 実数入力データの capstone 構造** — 実数値体積理論・骨格・
    入力を一つに束ね、`RealMultiradialInput` 型が空虚でないことを示す器。 -/
structure RealMultiradialInputData where
  V : RealVolumeTheory
  s : Skeleton
  input : RealMultiradialInput V s

/-- **M228F-6b: ガウス witness** — 重み付きガウスパイロット表現
    `gaussPilotRepW w l` を `base` に取った実数値入力データ。Θ-包体積が
    本物の `rlogVol w (gaussDiv l)` である実数値入力。 -/
def gaussRealInputData (w : Nat → Nat) (l : Nat) : RealMultiradialInputData where
  V := realVolumeTheory
  s := gaussSkeletonW w l
  input := gaussRealInput w l

/-- **定理 (M228F-6c): 実数入力レコードの非空虚性（見出し）** — 型
    `RealMultiradialInput` は少なくとも一つの witness を持つ（重み付き
    ガウスパイロット、w ≡ 1・l = 1）。実数値ではあるが依然パイロット模型で
    あり、実データ上の居住 = D-β 本丸ではない（正直な限定）。 -/
theorem realMultiradialInput_exists : Nonempty RealMultiradialInputData :=
  ⟨gaussRealInputData (fun _ => 1) 1⟩

/-- **定理 (M228F-6d): ガウス witness の Θ-包体積の同定** — ガウス実数値
    入力の `base` の Θ-正則包の実数値体積は、まさに重み付きガウス因子の
    次数 `wssq w l` の実数化。M158F-5 `gaussPilotW_vol_theta` を入力レコード
    越しに再輸出（`(gaussRealInput w l).base` は `gaussPilotRepW w l` に
    定義的に等しい）。**入力レコードに本物の実数値体積が入っている**ことの
    明示。 -/
theorem gaussRealInput_vol_theta (w : Nat → Nat) (l : Nat) :
    realEq (realVolumeTheory.vol (gaussRealInput w l).base.hullTheta)
      (natToReal (wssq w l)) :=
  gaussPilotW_vol_theta w l

/-
Dβ-2 完了: M215F `MultiradialInput` の実数鏡映 `RealMultiradialInput` を
構成し、M216F が「将来層」と宣言した実数値 base の完全 threading を回収した。
還元 `cor312_of_realInput`（実数入力 ⟹ 系3.12）・局在 `iut_localized_real`
は `cor312_of_realMultiradial`（M139）経由で降り、二つの障害フィールドは
M159F-5/M159F-6 で自動充足（`realInputOfRep`）。**gaussPilotRepW を base に
直接差し込んだ具体 witness `gaussRealInput`** は、Int 模型でなく本物の
実数値体積 rlogVol w (gaussDiv l) が Θ-正則包に入る初の入力レコードであり、
その Θ-包体積 = wssq w l の同定まで機械検証した。**実数値ではあるが依然
パイロット模型であり、遠アーベル構成 D-β 本丸ではない**（正直な限定）。
-/

end IUT
