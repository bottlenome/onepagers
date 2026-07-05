/-
  IUT/ThetaValueAlgebra.lean — M248F: テータ値の代数構造チェーンの総括
  capstone（柱E・並行部品）

  柱E 残課題 E-1（#39）のテータ値の**代数構造**チェーンを一本化する
  capstone。ここまで独立に閉じてきた四層

    M223F（ThetaValueConstruct.lean）— テータ値 q^{j²} の Laurent 単項式
      実体化（基点・乗法的漸化式・反転・値レベル評価写像の単射性、
      `ThetaValueConstructData` / `thetaValueConstructData` /
      `thetaValueConstruct_exists`）、

    M232F（ThetaRingObject.lean）— テータ値が住む環写像対象（指数モノイド
      準同型 uMonHom の単位・加法性・単元性、テータ値の乗法的合成則・
      単元性、`ThetaRingObjectData` / `thetaRingObjectData` /
      `thetaRingObject_exists`）、

    M237F（ThetaValueSubgroup.lean）— テータ値のなす Laurent 環単元群の
      部分群（単位・積・逆元閉性）・反射のコセット・有限多ラベル積の
      閉性（`ThetaValueSubgroupData` / `thetaValueSubgroupData` /
      `thetaValueSubgroup_exists`）、

    M242F（ThetaValueProdLaws.lean）— 多ラベル積の追加代数則（連接則・
      逆順/転置不変・連続ラベル範囲の指数和 = ssq とその閉形式、
      `ThetaValueProdLawData` / `thetaValueProdLawData` /
      `thetaValueProdLaw_exists`）

  を、**新規の数学的主張を一切追加せず**、単一のレコード
  `ThetaValueAlgebraData` に束ねる。M223F はテータ値の単項式実体化、
  M232F はそれが住む環写像対象、M237F はその部分群構造、M242F は
  多ラベル積の代数則——の四者が同じ係数環 R（M223F/評価写像の単射性
  部分は l = 2L+1 素数・R 非自明も併せ）の下で**同時に**成立することを
  一つの証拠として提示する。

  * M248F-1 `ThetaValueAlgebraData` — 四層 Data を束ねる総括レコード
    （フィールド `value_construct : ThetaValueConstructData R hne l L
    hodd hp`、`ring_object : ThetaRingObjectData R`、
    `subgroup : ThetaValueSubgroupData R`、
    `prod_laws : ThetaValueProdLawData R`）。
  * M248F-2 `thetaValueAlgebraData` — 四つの witness
    （`thetaValueConstructData` / `thetaRingObjectData` /
    `thetaValueSubgroupData` / `thetaValueProdLawData`）をそのまま
    埋める witness 本体。
  * M248F-3 `thetaValueAlgebra_exists` — 四つの `…_exists`
    （Nonempty）を `obtain` で取り出し（目標が
    `Nonempty (ThetaValueAlgebraData …)` という Prop なので
    Prop→Prop の構成的場合分けであり、新規の選択公理は不要）、
    一つの `ThetaValueAlgebraData` に組み直す。

  意義: M223F（単項式実体化）→ M232F（環写像対象）→ M237F（部分群
  構造）→ M242F（多ラベル積の代数則）という E-1 のテータ値代数構造
  チェーンを、一つの証明レコードとして提示する capstone。新規証明
  ゼロ（全フィールドは既存の `…Data`/`…_exists`/定理の再輸出）。

  正直な限定: 本 capstone が束ねるのはあくまで「テータ値 q^{j²} の
  単項式実体化 → それが住む環写像対象 → 単元部分群としての代数構造 →
  多ラベル積の代数則（連接・並べ替え・範囲和閉形式）」という**値の
  代数構造の離散核**であり、E-1 の残り（ガロア同変な p 進テータ値、
  tempered π₁ の商としての実現、エタールテータ関数値そのものの構成）
  は M223F/M232F/M237F/M242F 同様、未形式化のまま残る。全て選択公理
  不使用（新規導入なし。型継承として M223F 系は M212F 経由で
  [propext, Classical.choice, Quot.sound] を含みうる——本 capstone は
  それを新規に導入せず、既存の四つの `…_exists` をそのまま組み直す
  のみ。#print axioms で確認）。サブエージェント並行部品。
-/
import IUT.ThetaValueConstruct
import IUT.ThetaRingObject
import IUT.ThetaValueSubgroup
import IUT.ThetaValueProdLaws

namespace IUT

/-! ## M248F-1: 総括レコード -/

/-- **M248F-1: テータ値の代数構造チェーンの総括データ** — M223F
    （テータ値 q^{j²} の Laurent 単項式実体化：基点・乗法的漸化式・
    反転・値レベル評価写像の単射性）、M232F（テータ値が住む環写像対象：
    指数モノイド準同型の単位・加法性・単元性、乗法的合成則・単元性）、
    M237F（テータ値のなす Laurent 環単元群の部分群：単位・積・逆元
    閉性、反射のコセット、有限多ラベル積の閉性）、M242F（多ラベル積の
    追加代数則：連接則・逆順/転置不変・連続ラベル範囲の指数和 = ssq と
    その閉形式）を一つのレコードに束ねる。パラメータは M223F の要求
    （係数環 R の非自明性 `hne`、l = 2L+1 の素数性 `hp`）をそのまま
    引き継ぎ、M232F/M237F/M242F は係数環 R のみで成立する。 -/
structure ThetaValueAlgebraData (R : CRing) (hne : R.one ≠ R.zero)
    (l L : Nat) (hodd : l = 2 * L + 1) (hp : IsPrime l) where
  /-- M223F: テータ値 q^{j²} の Laurent 単項式実体化（基点・乗法的
      漸化式・反転・値レベル評価写像の単射性）。 -/
  value_construct : ThetaValueConstructData R hne l L hodd hp
  /-- M232F: テータ値が住む環写像対象（指数モノイド準同型の単位・
      加法性・単元性、テータ値の乗法的合成則・単元性）。 -/
  ring_object : ThetaRingObjectData R
  /-- M237F: テータ値のなす Laurent 環単元群の部分群（単位・積・逆元
      閉性）、反射のコセット、有限多ラベル積の閉性。 -/
  subgroup : ThetaValueSubgroupData R
  /-- M242F: 多ラベル積の追加代数則（連接則・逆順/転置不変・連続
      ラベル範囲の指数和 = ssq とその閉形式）。 -/
  prod_laws : ThetaValueProdLawData R

/-- **M248F-2: witness 本体** — 四つの既存 witness
    （`thetaValueConstructData` / `thetaRingObjectData` /
    `thetaValueSubgroupData` / `thetaValueProdLawData`）をそのまま
    フィールドに埋める。 -/
def thetaValueAlgebraData (R : CRing) (hne : R.one ≠ R.zero)
    (l L : Nat) (hodd : l = 2 * L + 1) (hp : IsPrime l) :
    ThetaValueAlgebraData R hne l L hodd hp where
  value_construct := thetaValueConstructData R hne l L hodd hp
  ring_object := thetaRingObjectData R
  subgroup := thetaValueSubgroupData R
  prod_laws := thetaValueProdLawData R

/-- **定理 (M248F-3): テータ値代数構造総括データの存在（M248F 見出し）** —
    係数環 R が非自明で l = 2L+1 が素数なら、テータ値の代数構造チェーン
    （単項式実体化・環写像対象・単元部分群・多ラベル積代数則）を束ねた
    データが存在する。M223F/M232F/M237F/M242F 各々の `…_exists`
    （Nonempty）を組み合わせるのみ（目標 `Nonempty
    (ThetaValueAlgebraData …)` は Prop なので Prop→Prop の構成的場合
    分け、新規の選択公理は不要）。 -/
theorem thetaValueAlgebra_exists (R : CRing) (hne : R.one ≠ R.zero)
    (l L : Nat) (hodd : l = 2 * L + 1) (hp : IsPrime l) :
    Nonempty (ThetaValueAlgebraData R hne l L hodd hp) := by
  obtain ⟨d1⟩ := thetaValueConstruct_exists R hne l L hodd hp
  obtain ⟨d2⟩ := thetaRingObject_exists R
  obtain ⟨d3⟩ := thetaValueSubgroup_exists R
  obtain ⟨d4⟩ := thetaValueProdLaw_exists R
  exact ⟨{ value_construct := d1, ring_object := d2, subgroup := d3, prod_laws := d4 }⟩

end IUT
