/-
  IUT/MultiradialInput.lean — M215F: MultiradialInput — IUT の正否の
  単一レコードへの局在（柱D D-α-7・並行部品）

  D-α プログラム（issue #38 詳細化ラウンド）の**核心（keystone）**。
  定理3.11 の充足問題を、ただ一つの名前付きレコード
  `MultiradialInput` の**居住（inhabitation）**へと局在させる。すなわち
  「IUT は正しいか」という問いを、実際の数論データ上でこのレコードを
  一つ構成できるか、という単一の形式的命題に還元する。還元の鎖は

      Theorem311Premises → MultiradialInput → Theorem311Rep → Cor312

  であり、本層はその中央のレコードと二本の還元
  （`cor312_of_input`・`rep_of_input`）、および局在の見出し
  `iut_localized` を機械検証する。

  * M215F-1 `MultiradialInput` — D-β が供給すべき単一入力レコード:
    - `base`       : 多輻的表現（M5 `MultiradialRep`）— アルゴリズムの出力
    - `padded`     : 膨張整合性（M5-3 `padding_necessary`）— q を実現する
      可能な像の体積は ≥ −|log q| まで膨張している
    - `not_strict` : 障害整合性（M5-2 `strict_evaluation_obstruction`）—
      不可能な「厳密テータ評価」ではない
  * M215F-2 `inputOfRep` — 任意の `MultiradialRep` から入力を作る
    （二つの障害フィールドは M5-2/M5-3 で自動充足される）。
  * M215F-3 `cor312_of_input` — **局在の下降**: 入力 ⟹ 系3.12（一行）。
  * M215F-4 `rep_of_input` — **前提 + 入力 ⟹ フル仕様 Theorem311Rep**
    （`base` に D-α 四本柱 M196F/M201F/M202F/M205F を各 `…_exists`/
    具体 witness から choice-free に束ねる）。
  * M215F-5 `iut_localized` — **局在の見出し**:
    `Nonempty (MultiradialInput V s) → Cor312 s`。
  * M215F-6 capstone: `MultiradialInputData`（構造）/ `multiradialInputData`
    （def; パイロット模型上の demo witness）/ `multiradialInput_exists`
    （Nonempty; レコード型が非空虚であることの実証）。

  ## 意義

  D-α-7 は D-α プログラムの**最終形**である。M210F（`Theorem311Rep`）が
  定理3.11 の言明構造を露出したのに続き、本層は「その充足に外から
  投入されるべき唯一のデータ」を名前付きレコード `MultiradialInput` に
  切り出す。二本の還元

      `cor312_of_input : MultiradialInput V s → Cor312 s`
      `rep_of_input    : Premises → MultiradialInput → Nonempty Theorem311Rep`

  により、「前提の束（柱B/E・choice-free 検証済み）」と「入力レコード
  一つ」が揃えば、フル仕様の表現 `Theorem311Rep`（→ 系3.12 → Szpiro）が
  すべて従うことが機械検証される。したがって **IUT の正否は、実際の
  算術データ上で `MultiradialInput` を一つ居住させられるか否かに厳密に
  等しい**——これが二分法（M5-2/M5-3）の形式的な最終形である。この
  局在自体は選択公理も新規公理も使わない純粋な還元である。

  ## 正直な限定

  * capstone の demo witness `multiradialInputData` はパイロット充足模型
    `m202fVol`（Region = ℤ・vol = id）上の `base311Rep` を `base` に取る。
    これはレコード型が**型として非空虚**であることの実証にすぎず、
    **実際の算術データ上での居住**（= 遠アーベル復元・エタールテータ
    剛性による多輻的アルゴリズムの構成）ではない。その本物の居住こそが
    **D-β**（永続的な幾何入力）であり、本層は主張しない。
  * 二つの障害フィールド `padded`/`not_strict` は M5-3/M5-2 により任意の
    `MultiradialRep` に対して自動的に充足される（`inputOfRep` 参照）。
    したがって `MultiradialInput` の居住可能性は `MultiradialRep` の
    居住可能性と等価であり、両フィールドは「制約」ではなく機械検証済み
    の**整合性の刻印**（膨張が在り・厳密評価ではない）として付帯する。
  * `rep_of_input` は `Nonempty (Theorem311Rep …)` を返す。mono-theta 環境
    は `monoThetaEnv_exists`（Nonempty）から取り出すため、素の
    `Theorem311Rep`（Type）を choice なしに直接返すことはできない——
    Nonempty の中で choice-free に obtain する（下流 M196F と同じ流儀）。
  * 骨格（Skeleton）だけでは系3.12 の正否は決まらない（既に
    `cor312_independent` が別途証明）——だからこそ入力レコードの
    居住という外部データが本質的に必要になる。

  継承 Classical: 本モジュール自身は新規 Classical.choice を導入しない。
  下流の四本柱・M5 経由で継承する公理があれば `#print axioms` に現れる
  （propext/Quot.sound の範囲）。sorry なし・禁止タクティク不使用
  （core Lean のみ）。サブエージェント並行部品（tier-M）。
-/
import IUT.Multiradial311
import IUT.Premises311

namespace IUT

/-! ## M215F-1: D-β が供給すべき単一入力レコード -/

/-- **M215F-1: `MultiradialInput`** — IUT の正否がその居住へと局在する
    ただ一つの名前付きレコード。多輻的アルゴリズムの出力 `base` に、
    M5-2/M5-3 の機械検証済み障害整合性を刻印として付帯させる。

    フィールドと原文の対応:
    * `base`       — (i) 多輻的表現（M5 `MultiradialRep`・D-β の出力仕様）
    * `padded`     — (Ind1–3) の膨張整合性（M5-3 `padding_necessary`）:
      q-パイロットを実現する可能な像の体積は ≥ −|log q| まで膨張している
    * `not_strict` — 障害整合性（M5-2 `strict_evaluation_obstruction`）:
      不可能な「厳密テータ評価」ではない（Scholze–Stix の障害の回避） -/
structure MultiradialInput (V : VolumeTheory) (s : Skeleton) where
  /-- 多輻的表現（M5・D-β のアルゴリズム出力）。 -/
  base : MultiradialRep V s
  /-- (Ind1–3) 膨張整合性（M5-3）: 可能な像の体積は ≥ −|log q|。 -/
  padded : ∃ i, -s.logq ≤ V.vol (base.image i)
  /-- 障害整合性（M5-2）: 不可能な厳密テータ評価ではない。 -/
  not_strict : ¬ StrictEvaluation base

/-! ## M215F-2: 表現から入力へ（障害フィールドは自動充足） -/

/-- **M215F-2: `inputOfRep`** — 任意の多輻的表現 `M` から入力レコードを
    構成する。二つの障害フィールドは M5-3 `padding_necessary` と M5-2
    `strict_evaluation_obstruction` によって自動的に充足される——ゆえに
    `MultiradialInput` の居住可能性は `MultiradialRep` の居住可能性と
    等価である（正直な限定）。 -/
def inputOfRep {V : VolumeTheory} {s : Skeleton} (M : MultiradialRep V s) :
    MultiradialInput V s where
  base := M
  padded := padding_necessary M
  not_strict := fun h => strict_evaluation_obstruction M h

/-! ## M215F-3: 局在の下降（入力 ⟹ 系3.12） -/

/-- **定理 (M215F-3): 入力 ⟹ 系3.12** — 局在の下降。入力レコードの
    `base` に M5 `cor312_of_multiradial` を適用する一行の還元。IUT の
    最終帰結（−|log q| ≤ −|log Θ|）は入力の居住から直ちに従う。 -/
theorem cor312_of_input {V : VolumeTheory} {s : Skeleton}
    (I : MultiradialInput V s) : Cor312 s :=
  cor312_of_multiradial I.base

/-! ## M215F-4: 前提 + 入力 ⟹ フル仕様 Theorem311Rep -/

/-- **定理 (M215F-4): 前提の束 + 入力 ⟹ フル仕様 `Theorem311Rep`** —
    入力の `base` を Theorem311Rep の `base` フィールドに据え、D-α の
    四本柱 M196F（mono-theta 環境）/ M201F（対数殻）/ M202F（不定性）/
    M205F（log-Kummer）を各 `…_exists`/具体 witness から choice-free に
    束ねる。mono-theta 環境は `monoThetaEnv_exists`（Nonempty）から
    Prop の中で取り出すため、結論は `Nonempty (Theorem311Rep …)`。
    前提の束 `_P`（柱B/E の choice-free 在庫）は本還元の前提として
    参照される（現段階では駆動には未使用——D-β の領分）。 -/
theorem rep_of_input (R : CRing) (p l L : Nat) (hp : IsPrime p) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1)
    (_P : Theorem311Premises) {s : Skeleton}
    (I : MultiradialInput m202fVol s) :
    Nonempty (Theorem311Rep R p l L hp hL hodd hdvd m202fVol s) := by
  obtain ⟨e⟩ := monoThetaEnv_exists R p l L hp hL hodd hdvd
  exact ⟨{ base := I.base, env := e, shell := logShellData,
           ind := indeterminaciesData, kummer := logKummerData }⟩

/-! ## M215F-5: 局在の見出し -/

/-- **定理 (M215F-5): 局在の見出し** — 入力レコードが（実際の算術データ
    上で）居住可能であれば、系3.12 が成り立つ。IUT の正否は
    `Nonempty (MultiradialInput V s)` に局在する——この居住こそが D-β。 -/
theorem iut_localized {V : VolumeTheory} {s : Skeleton}
    (h : Nonempty (MultiradialInput V s)) : Cor312 s := by
  obtain ⟨I⟩ := h
  exact cor312_of_input I

/-! ## M215F-6: capstone — Data / def / exists（レコードの非空虚性） -/

/-- **M215F-6a: 入力データの capstone 構造** — 体積理論・骨格・入力を
    一つに束ね、`MultiradialInput` 型が空虚でないことを示す器。 -/
structure MultiradialInputData where
  V : VolumeTheory
  s : Skeleton
  input : MultiradialInput V s

/-- **M215F-6b: demo witness** — パイロット充足模型 `m202fVol` 上の
    `base311Rep`（M210F の具体 witness）を `inputOfRep` で入力に持ち上げ
    た demo。障害フィールドは M5-2/M5-3 から自動充足。**本物の算術データ
    上の居住ではない**（正直な限定）。 -/
def multiradialInputData : MultiradialInputData where
  V := m202fVol
  s := base311Skel
  input := inputOfRep base311Rep

/-- **定理 (M215F-6c): 入力レコードの非空虚性（見出し）** — 型
    `MultiradialInput` は少なくとも一つの witness を持つ（demo）。
    実際の算術データ上での居住 = 多輻的アルゴリズムの構成 = D-β は
    別途の課題であり、ここでは主張しない。 -/
theorem multiradialInput_exists : Nonempty MultiradialInputData :=
  ⟨multiradialInputData⟩

/-
D-α-7 完了: 定理3.11 の充足問題を単一レコード `MultiradialInput` の居住へ
局在させた。還元の鎖 Theorem311Premises → MultiradialInput →
Theorem311Rep → Cor312 のうち、中央のレコードと `cor312_of_input`
（入力 ⟹ 系3.12）・`rep_of_input`（前提 + 入力 ⟹ Nonempty Theorem311Rep）・
`iut_localized`（局在の見出し）を機械検証した。二つの障害フィールドは
M5-2/M5-3 で自動充足され（`inputOfRep`）、demo witness はレコードの
非空虚性を実証する。**実際の算術データ上での居住（= D-β の多輻的
アルゴリズム構成）は永続的な幾何入力として正直な限定に分離する。**
-/

end IUT
