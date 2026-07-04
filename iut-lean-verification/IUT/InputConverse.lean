/-
  IUT/InputConverse.lean — M227F: 逆局在（局在の鋭さ・下界側）
  （柱D D-β-1・並行部品）

  D-β 詳細化ラウンド（§6.0）の第一段。既存の局在
  `iut_localized : Nonempty (MultiradialInput V s) → Cor312 s`
  （`IUT/MultiradialInput.lean`）は「入力レコードの居住 ⟹ 系3.12」
  という**片側**しか機械検証していなかった。本層はデモ充足模型
  `m202fVol`（Region = ℤ・vol = id、`IUT/Indeterminacies.lean`）の上で
  **逆向き**の矢印

      Cor312 s ⟹ Nonempty (MultiradialInput m202fVol s)

  を構成し、両者を `iut_localized_iff` として一本の同値に閉じる。
  すなわち「`m202fVol` 上では、`MultiradialInput` の居住問題は
  系3.12 とちょうど同値である」ことを機械検証する——これが局在の
  **鋭さ（下界側）**であり、D-β 全体の枠組み（軸2・鏡像定理 Dβ-7）
  のイディオムをデモ模型上で先行確立する。

  * M227F-1 `multiradialRepOfCor312` — `Cor312 s` から `MultiradialRep
    m202fVol s` を直接構成する。`Ind := Unit`、`image := fun _ =>
    -s.logTheta`（定数関数）、`shell := hullTheta := -s.logTheta`、
    `qRegion := -s.logq` と置くだけの Int 模型 witness。`q_realized`
    は仮定 `h : Cor312 s` それ自身（`≥` の定義展開で `≤` に一致）。
  * M227F-2 `input_of_cor312` — 上の表現を `inputOfRep`（M215F-2）に
    通し、障害刻印 `padded`/`not_strict` を自動充足させて
    `Nonempty (MultiradialInput m202fVol s)` を得る。
  * M227F-3 `iut_localized_iff` — 両矢印を束ねた同値。→ は既存
    `iut_localized`（M215F-5）、← は `input_of_cor312`。
  * M227F-4 capstone: `InputConverseData`（構造）/ `inputConverseData`
    （def; `base311Skel` 上の具体 witness）/ `inputConverse_exists`
    （Nonempty; 同値が実際に非空虚な骨格上で成立することの実証）。

  ## 正直な限定

  * 本層が閉じるのは**デモ充足模型 `m202fVol`（Region = ℤ・vol = id）
    上での**同値である。`image` を `−s.logTheta` という定数（骨格の
    データそのもの）に据えるだけの構成であり、テータ値 q^{j²}・
    Frobenioid 因子・実数体積といった**算術的に忠実な**データは
    一切登場しない。「算術模型上の鏡像定理」（`ThetaLinkTransport ↔
    Cor312`、D-β 詳細化 §4 の Dβ-7）とは**別物**であり、本層はその
    イディオム（← 方向の構成手筋）をデモ模型上で先取りするに過ぎない。
  * `q_realized` を仮定 `h` それ自身から供給する構成は、`Ind = Unit`
    （不定性が実質的に作用しない）という最も縮退した場合に限られる。
    実データでは (Ind1)(Ind2)(Ind3) が `image` に非自明に作用する
    必要があり（D-β 詳細化 Dβ-5「作用付き不定性」）、本層はそれを
    構成しない。
  * したがって本層が機械検証するのは「IUT の正否（= 系3.12 の真偽）
    は、少なくともデモ模型上では、入力レコードの居住問題と過不足
    なく同値である」という**局在の鋭さの下界**であり、実データ上の
    D-β（多輻的アルゴリズムの構成そのもの）を主張するものではない。

  継承 Classical: 本モジュール自身は新規 Classical.choice を導入しない。
  下流の M5/M215F 経由で継承する公理があれば `#print axioms` に現れる
  （本層で確認済み・propext/Quot.sound の範囲）。sorry なし・禁止
  タクティク不使用（core Lean のみ）。サブエージェント並行部品（tier-S）。
-/
import IUT.MultiradialInput

namespace IUT

/-! ## M227F-1: `Cor312` から `MultiradialRep` への直接構成 -/

/-- **M227F-1: `multiradialRepOfCor312`** — `Cor312 s` を仮定して
    Int 充足模型 `m202fVol` の上に `MultiradialRep m202fVol s` を
    構成する。`Ind := Unit`・`image := fun _ => -s.logTheta`（骨格の
    データそのものを定数像に据える）・`shell`/`hullTheta` はいずれも
    `image` と同じ値（`Int.le_refl` で自明に充足）・`qRegion :=
    -s.logq`。核心の `q_realized` は仮定 `h`（`Cor312 s` = `-s.logTheta
    ≥ -s.logq` は定義上 `-s.logq ≤ -s.logTheta` に一致）を直接使う。 -/
def multiradialRepOfCor312 {s : Skeleton} (h : Cor312 s) :
    MultiradialRep m202fVol s where
  Ind := Unit
  ind0 := ()
  shell := -s.logTheta
  image := fun _ => -s.logTheta
  image_in_shell := fun _ => Int.le_refl (-s.logTheta)
  hullTheta := -s.logTheta
  image_in_hull := fun _ => Int.le_refl (-s.logTheta)
  qRegion := -s.logq
  q_realized := ⟨(), h⟩
  vol_hull := rfl
  vol_q := rfl

/-! ## M227F-2: 入力レコードへの持ち上げ（逆局在） -/

/-- **定理 (M227F-2): 逆局在** — `Cor312 s` から `MultiradialInput
    m202fVol s` の居住を構成する。`multiradialRepOfCor312` で作った
    `MultiradialRep` を `inputOfRep`（M215F-2）に通すだけで、障害
    刻印 `padded`/`not_strict` は M5-3/M5-2 により自動充足される。 -/
theorem input_of_cor312 {s : Skeleton} (h : Cor312 s) :
    Nonempty (MultiradialInput m202fVol s) :=
  ⟨inputOfRep (multiradialRepOfCor312 h)⟩

/-! ## M227F-3: 局在の鋭さ — 同値への閉合 -/

/-- **定理 (M227F-3): `iut_localized_iff`** — デモ模型 `m202fVol` 上で、
    入力レコードの居住問題は系3.12 と**ちょうど同値**である。→ は
    既存の局在 `iut_localized`（M215F-5）、← は本層の `input_of_cor312`
    （逆局在）。局在の鋭さ（下界側）が閉じる。 -/
theorem iut_localized_iff (s : Skeleton) :
    Nonempty (MultiradialInput m202fVol s) ↔ Cor312 s :=
  ⟨iut_localized, input_of_cor312⟩

/-! ## M227F-4: capstone — 具体骨格上での同値の実証 -/

/-- **M227F-4a: 逆局在データの capstone 構造** — 骨格・系3.12 の証拠・
    それから構成した入力レコードを一つに束ねる。 -/
structure InputConverseData where
  s : Skeleton
  h : Cor312 s
  input : MultiradialInput m202fVol s

/-- **M227F-4b: demo witness** — M210F の具体骨格 `base311Skel`
    （l⋇ = 2・logq = 1・logTheta = 1）上で `Cor312` が成り立つこと
    （−1 ≥ −1、等号で成立）を示し、逆局在で入力レコードへ持ち上げる。 -/
def inputConverseData : InputConverseData where
  s := base311Skel
  h := by unfold Cor312 base311Skel; omega
  input := inputOfRep (multiradialRepOfCor312 (by unfold Cor312 base311Skel; omega))

/-- **定理 (M227F-4c): 逆局在の非空虚性（見出し）** — `base311Skel`
    という具体骨格上で、`Cor312` の証拠から入力レコードへの逆局在が
    実際に非空虚なデータとして構成できることの実証。 -/
theorem inputConverse_exists : Nonempty InputConverseData :=
  ⟨inputConverseData⟩

/-
D-β-1 完了: デモ充足模型 `m202fVol` 上で、局在の逆矢印
`Cor312 s → Nonempty (MultiradialInput m202fVol s)` を構成し、既存の
順方向 `iut_localized` と束ねて `iut_localized_iff`（同値）を機械検証
した。IUT の正否（系3.12）は、少なくともデモ模型上では、入力レコード
の居住問題と過不足なく等価である——**局在の鋭さ（下界側）**。実データ
上での忠実な鏡像定理（`ThetaLinkTransport ↔ Cor312`）は D-β の後段
（Dβ-3〜7）の課題として残る。
-/

end IUT
