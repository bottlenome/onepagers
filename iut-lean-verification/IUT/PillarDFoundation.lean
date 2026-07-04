/-
  IUT/PillarDFoundation.lean — M214F: 柱D D-α 型土台の総括 capstone
  （柱D・並行部品）

  柱D の Dα プログラム（issue #38）が Dα-2〜7 の共通入力とする四つの
  「型土台」——mono-theta 環境（M196F, Dα-1）・対数殻テンソルパケット
  （M201F, Dα-2）・(Ind1)(Ind2)(Ind3) の構造化（M202F, Dα-3）・
  log-Kummer 対応の骨格（M205F, Dα-4）——を、**一つの構造体**に束ねる
  bundling capstone。本モジュールは新規の数学的主張を一切持たない
  （**新規証明ゼロ**）。四つの `structure` を四つのフィールドに、
  四つの `…_exists` を一つの `Nonempty` 証明に、それぞれそのまま
  代入するだけで埋まる。

  * M214F-1 `PillarDFoundationData` — 四つの D-α 型土台を束ねる構造体:
    Dα-1 `env : MonoThetaEnv …`・Dα-2 `shell : LogShellData`・
    Dα-3 `ind : IndeterminaciesData`・Dα-4 `kummer : LogKummerData`
  * M214F-2 `pillarDFoundationData` — witness 本体（mono-theta 環境を
    直接引数に取り、他の三本は `logShellData`/`indeterminaciesData`/
    `logKummerData` を代入する choice-free コンストラクタ）
  * M214F-3 `pillarDFoundation_exists` — 総括の存在
    （Nonempty; mono-theta 環境の存在のみ `monoThetaEnv_exists` から
    Prop 内で取り出す——choice 不要）

  ## 意義

  Dα-1〜4（M196F/M201F/M202F/M205F）がいずれも sorry なし・新規
  Classical.choice なしで確立済みであることを一つの記録として証明する。
  これにより「柱D D-α の四つの型土台が揃った」という進捗が機械検証
  可能な単一の `Nonempty` 命題として certify され、Dα-5 の
  `Theorem311Rep`（定理3.11 のフル仕様: 基点 + reduction を担う本丸）
  が参照すべき四本の入力が同時に利用可能であることを保証する。

  ## 正直な限定

  本層が束ねるのは Dα-1〜4 の**型土台**のみであり、定理3.11 の
  フル仕様（基点条件・reduction・多輻性の充足）を担う `Theorem311Rep`
  の構成（Dα-5）そのものはここには含まれない。同様に `MultiradialRep`
  の解析的構成（遠アーベル復元・エタールテータ剛性）は柱D 本体・D-β の
  領分であり本層の範囲外。本モジュールはあくまで「四つの部品が同時に
  存在する」ことの bundling capstone であって、四者の間の**相互整合性**
  （例: `ind : IndeterminaciesData` の `V` と `kummer : LogKummerData` の
  `V` が同一視されること等）を主張するものではない——各フィールドは
  独立な witness としてそれぞれの `…_exists` から取り出されるに留まる。

  全て選択公理不使用（四つの `…_exists` がいずれも choice-free である
  ことを継承するのみで、本層は新規公理を導入しない）。
-/
import IUT.MonoThetaEnv
import IUT.LogShell
import IUT.Indeterminacies
import IUT.LogKummer

namespace IUT

/-! ## M214F-1: 柱D D-α 型土台の総括構造体 -/

/-- **M214F-1: 柱D D-α 型土台の総括** — Dα-1〜4 の四つの型土台
    （mono-theta 環境・対数殻テンソルパケット・構造化不定性・
    log-Kummer 対応の骨格）を一つの構造体に束ねる。柱D の Dα プログラム
    が Dα-5（`Theorem311Rep`）で参照すべき四本の入力が揃っていることの
    型レベルの証跡。 -/
structure PillarDFoundationData (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) where
  /-- Dα-1（M196F）: mono-theta 環境。 -/
  env : MonoThetaEnv R p l L hp hL hodd hdvd
  /-- Dα-2（M201F）: 対数殻テンソルパケット。 -/
  shell : LogShellData
  /-- Dα-3（M202F）: (Ind1)(Ind2)(Ind3) の構造化。 -/
  ind : IndeterminaciesData
  /-- Dα-4（M205F）: log-Kummer 対応の骨格。 -/
  kummer : LogKummerData

/-! ## M214F-2/3: witness 本体と存在 -/

/-- **M214F-2: 総括の witness 本体** — mono-theta 環境を直接引数に
    取り（M196F の `monoThetaEnv` と同じく choice-free コンストラクタ
    である）、対数殻・構造化不定性・log-Kummer 骨格の三本は
    param-free な `logShellData`/`indeterminaciesData`/`logKummerData`
    をそのまま代入する。 -/
def pillarDFoundationData (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1)
    (env : MonoThetaEnv R p l L hp hL hodd hdvd) :
    PillarDFoundationData R p l L hp hL hodd hdvd where
  env := env
  shell := logShellData
  ind := indeterminaciesData
  kummer := logKummerData

/-- **定理 (M214F-3): 柱D D-α 型土台の総括データの存在** — Dα-1〜4
    （M196F/M201F/M202F/M205F）を束ねた `PillarDFoundationData` は
    充足可能。mono-theta 環境の存在のみ M196F `monoThetaEnv_exists`
    から Prop（Nonempty）の中で取り出す——choice 不要。柱D の
    Dα 型土台プログラムが空回りでないことの capstone。 -/
theorem pillarDFoundation_exists (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) :
    Nonempty (PillarDFoundationData R p l L hp hL hodd hdvd) := by
  obtain ⟨e⟩ := monoThetaEnv_exists R p l L hp hL hodd hdvd
  exact ⟨pillarDFoundationData R p l L hp hL hodd hdvd e⟩

/-
D-α 型土台総括完了: M196F（mono-theta 環境）・M201F（対数殻）・
M202F（構造化不定性）・M205F（log-Kummer 骨格）の四つの Dα 型土台が
同時に利用可能であることを一つの `Nonempty` 命題として certify した。
新規証明ゼロ（四つの `…_exists` の再輸出のみ）。Dα-5 の
`Theorem311Rep`（フル仕様・基点＋reduction）と MultiradialRep の
解析的構成（D-β）は本層の範囲外。
-/

end IUT
