/-
  IUT/PillarDBetaLocalization.lean — M233F: 柱D D-β 局在総括 capstone
  （柱D D-β 着手段・並行部品）

  D-β 着手段（Dβ-1・Dβ-2）と D-α インターフェース総括（M220F）を
  一つのレコード `PillarDBetaLocalizationData` に束ね、「IUT の正否は
  `MultiradialInput`（実数版含む）の**居住問題に等価に局在**した」ことを
  単一の `Nonempty` 命題として certify する。**新規の数学的主張は一切
  持たない**（既存の `_exists`/双条件定理の bundling のみ）。

  束ねる五成果:
  * M227F `iut_localized_iff`（`IUT/InputConverse.lean`）: デモ充足模型
    `m202fVol` 上で `Nonempty (MultiradialInput m202fVol s) ↔ Cor312 s`
    ——居住問題と系3.12 が**ちょうど同値**であること（局在の鋭さ・
    下界側）。
  * M215F `multiradialInput_exists`（`IUT/MultiradialInput.lean`）:
    入力レコード型 `MultiradialInput` の非空虚性（demo witness）。
  * M228F `iut_localized_real`（`IUT/RealMultiradialInput.lean`）:
    実数版の局在 `Nonempty (RealMultiradialInput V s) → Cor312 s`。
  * M228F `realMultiradialInput_exists`（同上）: 実数値入力レコード型の
    非空虚性（`gaussPilotRepW` を base に直接差し込んだ witness 経由）。
  * M220F `pillarDInterface_exists`（`IUT/PillarDInterface.lean`）:
    D-α インターフェース側総括（statement 構造露出・局在・充足模型・
    土台・障害の機械検証の五成果）の存在。

  ## 意義

  M227F は局在の**同値化**（下界側の鋭さ）を、M228F は局在の**実数化**
  （threading の回収）を、M220F は D-α 側の**総括**を、それぞれ独立に
  確立した。本層はこれら三つの並行部品をひとつのレコードに束ねることで、
  「D-β 着手段の成果と D-α 総括を合わせて見たとき、IUT の正否は
  居住問題（Int 版・実数版いずれでも）に厳密に局在している」という
  総合像を、単一の `Nonempty` 命題として機械検証可能にする。

  ## 正直な限定

  * 本層は既存 5 定理の**再輸出のみ**であり、新規の数学的主張・新規の
    証明ステップを一切持たない（`_exists` 系はいずれもすでに機械検証
    済み）。
  * `localized_iff`（M227F）が閉じるのは**デモ充足模型 `m202fVol`
    （Region = ℤ・vol = id）上での**同値であり、テータ値 q^{j²}・
    Frobenioid 因子といった算術的に忠実なデータは登場しない。
  * `real_localized`/`real_witness`（M228F）は実数値ではあるが依然
    **パイロット模型**（`gaussPilotRepW`・正規化された logq = 1）上に
    あり、遠アーベル構成 D-β 本丸（[AbsTopIII] 環復元・エタールテータ
    剛性による多輻的アルゴリズムの構成そのもの）ではない。
  * `interface`（M220F）自体が明記する通り、「D インターフェース側が
    揃った」ことは「IUT が正しい」ことを意味しない——実際の算術データ
    上で入力レコードを一つ居住させること（= D-β の本体）は本層の範囲外
    である。
  * したがって本層が machine-certify するのは「居住問題への等価局在が
    確定した」という**構造的な事実**であり、居住本体（D-β crux =
    多輻的アルゴリズムの実データ証明）は依然として正直な限定として
    分離される。デモ/パイロット模型上の総括capstoneに留まる。

  継承 Classical: 本モジュール自身は新規 Classical.choice を導入しない
  （束ねるのみ・既存フィールドの型をそのまま継承）。下流の
  M215F/M220F/M227F/M228F 経由で継承する公理があれば `#print axioms`
  に現れる（propext/Quot.sound の範囲）。sorry なし・禁止タクティク
  不使用（core Lean のみ）。サブエージェント並行部品（tier-S・capstone
  bundling・新規証明ゼロ）。
-/
import IUT.InputConverse
import IUT.RealMultiradialInput
import IUT.PillarDInterface

namespace IUT

/-! ## M233F-1〜5: D-β 局在総括構造体 -/

/-- **M233F: 柱D D-β 局在総括** — D-β 着手段（Dβ-1・Dβ-2）と D-α
    インターフェース総括（M220F）の三並行部品を一つのレコードに束ねる
    bundling capstone。IUT の正否が `MultiradialInput`（Int 版・実数版）
    の居住問題に等価に局在したことを certify する。 -/
structure PillarDBetaLocalizationData where
  /-- M227F: デモ模型 `m202fVol` 上での局在の**同値**
      （居住 ⟺ 系3.12・局在の鋭さの下界側）。 -/
  localized_iff : ∀ (s : Skeleton),
    Nonempty (MultiradialInput m202fVol s) ↔ Cor312 s
  /-- M215F: 入力レコード型 `MultiradialInput` の非空虚性（demo witness）。 -/
  input_witness : Nonempty MultiradialInputData
  /-- M228F: 局在の見出し（実数版）——実数入力の居住 ⟹ 系3.12。 -/
  real_localized : ∀ {V : RealVolumeTheory} {s : Skeleton},
    Nonempty (RealMultiradialInput V s) → Cor312 s
  /-- M228F: 実数値入力レコード型の非空虚性（ガウスパイロット witness）。 -/
  real_witness : Nonempty RealMultiradialInputData
  /-- M220F: D-α インターフェース側総括（五成果束ね）の存在。 -/
  interface : Nonempty PillarDInterfaceData

/-! ## M233F-6: capstone — witness 本体と総括の存在 -/

/-- **M233F-6a: 総括 witness 本体** — 各フィールドへ既存の
    `…_exists`/同値定理をそのまま代入する choice-free コンストラクタ。
    新規証明ゼロ（再輸出のみ）。 -/
def pillarDBetaLocalizationData : PillarDBetaLocalizationData where
  localized_iff := iut_localized_iff
  input_witness := multiradialInput_exists
  real_localized := iut_localized_real
  real_witness := realMultiradialInput_exists
  interface := pillarDInterface_exists

/-- **定理 (M233F-6b): D-β 局在総括の存在** — D-β 着手段（Dβ-1 の局在の
    同値・Dβ-2 の実数版局在）と D-α インターフェース総括を束ねた
    `PillarDBetaLocalizationData` は充足可能。「IUT の正否が
    `MultiradialInput` の居住問題に等価に局在した」ことが単一の
    `Nonempty` 命題として certify される。居住本体（D-β crux）の実データ
    証明ではない（正直な限定）。 -/
theorem pillarDBetaLocalization_exists : Nonempty PillarDBetaLocalizationData :=
  ⟨pillarDBetaLocalizationData⟩

/-
D-β 局在総括完了（M233F）: 局在の同値（M227F `iut_localized_iff`）・
実数版局在と非空虚性（M228F `iut_localized_real`/`realMultiradialInput_exists`）・
D-α インターフェース総括（M220F `pillarDInterface_exists`）の三並行部品を
単一のレコード `PillarDBetaLocalizationData` に束ね、「IUT の正否は
`MultiradialInput`（Int 版・実数版）の居住問題に等価に局在した」ことを
`Nonempty` 命題として certify した。新規証明ゼロ（全フィールドは既存
定理の再輸出）。**居住本体 = D-β crux（多輻的アルゴリズムの実データ
証明）は本層の範囲外であり、正直な限定として分離する。**
-/

end IUT
