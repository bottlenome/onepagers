/-
  IUT/PillarDInterface.lean — M220F: 柱D インターフェース側 100%
  capstone — D-α プログラムの総括（柱D・並行部品）

  柱D の Dα プログラム（issue #38 詳細化ラウンド）の**最終 capstone**。
  これまでの並行部品が別々に確立した五つの成果——

      statement 構造露出（M210F）・局在（M215F）・充足模型（M216F）・
      土台（M214F）・障害の機械検証（M5-2/M5-3）

  ——を**一つのレコード** `PillarDInterfaceData` に束ね、「D インター
  フェース側」が形式的に揃っていることを単一の `Nonempty` 命題として
  certify する。**新規の数学的主張は一切持たない**（bundling のみ）。

  * M220F-1 `struct_exposed` — 定理3.11 の statement 構造露出
    （M210F `theorem311Rep_exists`）: フル仕様 `Theorem311Rep`
    （base + 四本柱 env/shell/ind/kummer）が存在する。
  * M220F-2 `localized` — IUT 正否の局在の見出し（M215F
    `iut_localized`）: `Nonempty (MultiradialInput V s) → Cor312 s`。
  * M220F-3 `rep_of_input` — 前提 + 入力 ⟹ フル仕様（M215F
    `rep_of_input`）: 局在の下降のもう半分（入力からフル仕様への上昇）。
  * M220F-4 `input_witness` — 入力レコード型の非空虚性（M215F
    `multiradialInput_exists`）。
  * M220F-5 `satisfaction` — 非自明な充足模型（M216F
    `gaussPilot311_exists`）: 実際のガウス因子の次数で inhabited な
    フル仕様。
  * M220F-6 `foundation` — D-α 四本柱の型土台総括（M214F
    `pillarDFoundation_exists`）。
  * M220F-7 `not_strict` — 障害の機械検証その一（M5-2
    `strict_evaluation_obstruction`）: 厳密テータ評価は不可能。
  * M220F-8 `padded` — 障害の機械検証その二（M5-3
    `padding_necessary`）: 充足には膨張が必然。
  * M220F-9 capstone: `pillarDInterfaceData`（def; 各フィールドへ
    既存の定理・def をそのまま代入）/ `pillarDInterface_exists`
    （Nonempty; 総括の存在）。

  ## 意義

  Dα-8（issue #38 詳細化ラウンド）は D-α プログラムの**総括**である。
  「定理3.11 の statement 構造が露出済みか（M210F）」「IUT の正否は
  `MultiradialInput` の居住へ厳密に局在するか（M215F）」「その居住は
  非自明に充足可能か（M216F のガウスパイロット）」「四本柱の型土台は
  揃っているか（M214F）」「Scholze–Stix の障害は機械検証済みで、
  むしろ膨張の必然性として二分法の形式的な最終形になっているか
  （M5-2/M5-3）」——これら五つの問いにいずれも Yes と答える単一の
  レコードが本層である。これにより「**D インターフェース側 100%**:
  定理3.11 の statement 構造露出・系3.12 への還元・非自明充足模型・
  障害の機械検証・IUT 正否の `MultiradialInput` への局在の全部が
  揃った」という進捗が、一つの `Nonempty` 命題として機械検証可能に
  なる。全フィールドは既存の `…_exists`/定理の再輸出であり、
  **新規証明ゼロ**。

  ## 正直な限定

  * 「D インターフェース側が揃った」ことは「**IUT が正しい**」ことを
    意味しない。実際の算術データ上で `MultiradialInput` を一つ居住
    させること（= 遠アーベル復元・エタールテータ剛性による多輻的
    アルゴリズムの構成 = D-β = 永続的な幾何入力）は本層の範囲外で
    あり、`input_witness`/`satisfaction` が実証するのはあくまで
    レコード型・フル仕様型が**型として非空虚**であることに留まる
    （demo witness・ガウスパイロット模型）。
  * `struct_exposed`（M210F）自体の骨格（skeleton）だけでは系3.12 の
    正否は決まらない——別途 `cor312_independent`（M5 系列）が証明
    済みであり、だからこそ入力レコードの居住という外部データ（D-β）
    が本質的に必要になる。
  * `foundation`（M214F）が束ねるのは四本柱の**型土台**の相互独立な
    witness の並置であり、四者間の相互整合性（例: `ind` と `kummer`
    の `V` の同一視）は主張しない（M214F の正直な限定を継承）。
  * `not_strict`/`padded`（M5-2/M5-3）は `MultiradialInput` の二つの
    障害フィールドとして既に `inputOfRep` 経由で任意の `MultiradialRep`
    に自動充足されている（M215F 参照）——本層はそれを一般形（∀ V s M,
    …）として独立にも再輸出し、「障害の機械検証」という項目を
    それ自体で確認可能にする。

  継承 Classical: 本モジュール自身は新規 Classical.choice を導入しない。
  下流の四本柱・M5 系列・M210F/M214F/M215F/M216F 経由で継承する公理が
  あれば `#print axioms` に現れる（propext/Quot.sound の範囲）。
  sorry なし・禁止タクティク不使用（core Lean のみ）。サブエージェント
  並行部品（tier-S・bundling のみ・新規証明ゼロ）。
-/
import IUT.MultiradialInput
import IUT.GaussPilot311
import IUT.PillarDFoundation

namespace IUT

/-! ## M220F-1〜8: D インターフェース側の五成果を束ねる総括構造体 -/

/-- **M220F: 柱D インターフェース側 100% 総括** — D-α プログラムの
    五つの並行部品（statement 構造露出・局在・充足模型・土台・障害の
    機械検証）を一つのレコードに束ねる bundling capstone。 -/
structure PillarDInterfaceData where
  /-- M210F: 定理3.11 の statement 構造露出（フル仕様の存在）。 -/
  struct_exposed : ∀ (R : CRing) (p l L : Nat) (hp : IsPrime p) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1),
    Nonempty (Theorem311Rep R p l L hp hL hodd hdvd m202fVol base311Skel)
  /-- M215F: IUT 正否の局在の見出し（入力の居住 ⟹ 系3.12）。 -/
  localized : ∀ {V : VolumeTheory} {s : Skeleton},
    Nonempty (MultiradialInput V s) → Cor312 s
  /-- M215F: 前提の束 + 入力 ⟹ フル仕様 `Theorem311Rep`（局在の上昇）。 -/
  rep_of_input : ∀ (R : CRing) (p l L : Nat) (hp : IsPrime p) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) (_P : Theorem311Premises)
    {s : Skeleton} (_I : MultiradialInput m202fVol s),
    Nonempty (Theorem311Rep R p l L hp hL hodd hdvd m202fVol s)
  /-- M215F: 入力レコード型の非空虚性（demo witness）。 -/
  input_witness : Nonempty MultiradialInputData
  /-- M216F: 非自明な充足模型（実ガウス次数のフル仕様）。 -/
  satisfaction : Nonempty GaussPilot311Data
  /-- M214F: D-α 四本柱の型土台総括。 -/
  foundation : ∀ (R : CRing) (p l L : Nat) (hp : IsPrime p) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1),
    Nonempty (PillarDFoundationData R p l L hp hL hodd hdvd)
  /-- M5-2: 厳密テータ評価の障害（機械検証済み）。 -/
  not_strict : ∀ {V : VolumeTheory} {s : Skeleton} (M : MultiradialRep V s),
    StrictEvaluation M → False
  /-- M5-3: 膨張の必然性（機械検証済み）。 -/
  padded : ∀ {V : VolumeTheory} {s : Skeleton} (M : MultiradialRep V s),
    ∃ i, -s.logq ≤ V.vol (M.image i)

/-! ## M220F-9: capstone — witness 本体と総括の存在 -/

/-- **M220F-9a: 総括 witness 本体** — 各フィールドへ既存の
    `…_exists`/定理をそのまま代入する choice-free コンストラクタ。
    新規証明ゼロ（再輸出のみ）。 -/
def pillarDInterfaceData : PillarDInterfaceData where
  struct_exposed := theorem311Rep_exists
  localized := iut_localized
  rep_of_input := rep_of_input
  input_witness := multiradialInput_exists
  satisfaction := gaussPilot311_exists
  foundation := pillarDFoundation_exists
  not_strict := strict_evaluation_obstruction
  padded := padding_necessary

/-- **定理 (M220F-9b): 柱D インターフェース側総括の存在** — 五つの
    D-α 成果（statement 構造露出・局在・充足模型・土台・障害の機械
    検証）を束ねた `PillarDInterfaceData` は充足可能。「D インター
    フェース側 100%」が単一の `Nonempty` 命題として certify される。 -/
theorem pillarDInterface_exists : Nonempty PillarDInterfaceData :=
  ⟨pillarDInterfaceData⟩

/-
D-α プログラム総括完了（Dα-8）: 定理3.11 の statement 構造露出
（M210F）・IUT 正否の `MultiradialInput` への局在（M215F）・非自明な
充足模型（M216F ガウスパイロット）・D-α 四本柱の型土台（M214F）・
Scholze–Stix の障害の機械検証（M5-2/M5-3）の五成果を単一のレコード
`PillarDInterfaceData` に束ね、「D インターフェース側 100%」を一つの
`Nonempty` 命題として certify した。新規証明ゼロ（全フィールドは既存
定理の再輸出）。**実際の算術データ上での `MultiradialInput` の居住
（= 遠アーベル復元・エタールテータ剛性による多輻的アルゴリズムの構成
= D-β = 永続的な幾何入力）は本層の範囲外であり、正直な限定として
分離する。**
-/

end IUT
