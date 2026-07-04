/-
  IUT/Multiradial311.lean — M210F: フル仕様 Theorem311Rep — D-α の要
  （柱D D-α-5・並行部品）

  IUT III 定理3.11 の **statement-structure（言明構造）** を、体積の影
  （M5 `MultiradialRep`）を `base` とし、その上に D-α プログラム
  （issue #38 詳細化ラウンド）の四本柱を並行フィールドとして載せた
  **フル仕様の表現型** `Theorem311Rep` に束ねる。定理3.11 → 系3.12 の
  還元は `base` を通して降りる（`cor312_of_311`）——これが本層の要
  （keystone）である。

  * M210F-1 `base311Skel` / `base311Rep` — 体積の影の具体 witness
    （M5 `multiradial_consistent` と同じ Int 充足模型 `m202fVol` 上の
    concrete `MultiradialRep`）。`theorem311Rep_exists` の base 供給元。
  * M210F-2 `Theorem311Rep` — フル仕様の表現型:
    - `base`   : 体積の影（M5 `MultiradialRep`）— 還元の降下先
    - `env`    : (i)(b) mono-theta 環境（M196F `MonoThetaEnv`）
    - `shell`  : (i)(a) 対数殻テンソルパケット（M201F `LogShellData`）
    - `ind`    : (Ind1)(Ind2)(Ind3) 不定性（M202F `IndeterminaciesData`）
    - `kummer` : (ii) log-Kummer 対応（M205F `LogKummerData`）
  * M210F-3 `cor312_of_311` — 還元は `base` を通して降りる（keystone・一行）。
  * M210F-4 `szpiro_of_311` — base 経由で Szpiro 型不等式まで再輸出。
  * M210F-5 capstone: `theorem311RepData`（def）/ `theorem311Rep_exists`
    （Nonempty; 四本柱の各 `…_exists`/具体 witness から choice-free に合成）。

  ## 意義

  D-α-5（issue #38 詳細化ラウンド）は、定理3.11 の言明構造
  (i)(a)(b)(c)/(Ind1–3)/(ii) を、体積の影 `base` の上のフィールドとして
  **明示的に露出**することが目的である。本層は D-α の四本の基盤
  M196F（mono-theta 環境）/ M201F（対数殻）/ M202F（不定性）/
  M205F（log-Kummer）を単一の型 `Theorem311Rep` に束ね、還元
  `cor312_of_311` が `base`（= 体積の影）を通してのみ降りることを
  機械検証する（keystone）。四本柱はいずれも既に `Nonempty` 版
  witness（`monoThetaEnv_exists` / `logShell_exists` /
  `indeterminacies_exists` / `logKummer_exists`）を持つため、フル仕様の
  存在 `theorem311Rep_exists` は各 witness の Prop 内取り出し（choice
  不要）だけで従う。

  ## 正直な限定

  * 本層の各フィールド（env/shell/ind/kummer）は定理3.11 の言明構造の
    層を**並置**したものであり、「ある具体的な曲線のデータの実際の
    構成要素である」ことは**まだ証明していない**。その同定
    （env が本当に当該曲線の mono-theta 環境であること・shell が
    log(O^×) の格子像であること 等）と `MultiradialInput` の解析的
    realization は D-β の課題である。
  * 還元 `cor312_of_311`/`szpiro_of_311` は `base` のみを用いる。
    四本柱は「言明構造の露出」であって還元の駆動には（現段階では）
    参加しない——それらが還元に実質寄与する（膨張の定量制御・Kummer
    同型の構成）のは D-β の領分である。
  * `base311Rep` は M5 `multiradial_consistent` と同じ充足デモ模型
    （`m202fVol`: Region = ℤ・vol = id）の上にあり、遠アーベル復元・
    エタールテータ剛性による `MultiradialRep` の**構成そのもの**
    （= D-β）ではない。

  継承 Classical: 本モジュール自身は新規 Classical.choice を導入しない。
  下流の四本柱・M5 経由で継承する公理があれば `#print axioms` に現れる
  （本層で確認済み・propext/Quot.sound の範囲）。sorry なし・禁止
  タクティク不使用（core Lean のみ）。サブエージェント並行部品（tier-M）。
-/
import IUT.Multiradial
import IUT.MonoThetaEnv
import IUT.LogShell
import IUT.Indeterminacies
import IUT.LogKummer

namespace IUT

/-! ## M210F-1: 体積の影の具体 witness（base 供給元） -/

/-- **M210F-1a: base 用スケルトン** — M5 `multiradial_consistent` と
    同じパラメータ（l⋇ = 2・logq = 1・logθ = 1）の Skeleton。 -/
def base311Skel : Skeleton where
  lstar := 2
  hl := by omega
  logq := 1
  hq := by omega
  logTheta := 1

/-- **M210F-1b: 体積の影の具体 witness** — Int 充足模型 `m202fVol`
    （Region = ℤ・le = ≤・hull = max・vol = id）の上の concrete
    `MultiradialRep`。M5 `multiradial_consistent` の内部 witness と
    同型の構成で、`Theorem311Rep` の `base` フィールドへ供給する。 -/
def base311Rep : MultiradialRep m202fVol base311Skel where
  Ind := Unit
  ind0 := ()
  shell := 0
  image := fun _ => -1
  image_in_shell := fun _ => by show (-1 : Int) ≤ 0; omega
  hullTheta := -1
  image_in_hull := fun _ => by show (-1 : Int) ≤ -1; omega
  qRegion := -1
  q_realized := ⟨(), by show (-1 : Int) ≤ -1; omega⟩
  vol_hull := rfl
  vol_q := rfl

/-! ## M210F-2: フル仕様の表現型 -/

/-- **M210F-2: フル仕様 `Theorem311Rep`** — 体積の影 `base`
    （M5 `MultiradialRep`）の上に、D-α プログラムの四本柱を並行
    フィールドとして載せた定理3.11 の言明構造型。還元
    `cor312_of_311` は `base` を通して降りる（keystone）。

    フィールドと原文の対応:
    * `base`   — 体積の影（M5・(i)(a) の log-volume 単調性で還元を駆動）
    * `env`    — (i)(b) mono-theta 環境（M196F・テータ群の群論的骨格）
    * `shell`  — (i)(a) 対数殻テンソルパケット（M201F・mono-analytic
      container・殻の体積 = wssq）
    * `ind`    — (Ind1)(Ind2)(Ind3) 不定性（M202F・三由来の積不定性）
    * `kummer` — (ii) log-Kummer 対応（M205F・(a) ⊆-のみ・(b)(c) 厳密） -/
structure Theorem311Rep (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1)
    (V : VolumeTheory) (s : Skeleton) where
  /-- 体積の影（M5・既存）— 還元 `cor312_of_311` の降下先。 -/
  base : MultiradialRep V s
  /-- (i)(b) mono-theta 環境（M196F）。 -/
  env : MonoThetaEnv R p l L hp hL hodd hdvd
  /-- (i)(a) 対数殻テンソルパケット（M201F）。 -/
  shell : LogShellData
  /-- (Ind1)(Ind2)(Ind3) 不定性（M202F）。 -/
  ind : IndeterminaciesData
  /-- (ii) log-Kummer 対応（M205F）。 -/
  kummer : LogKummerData

/-! ## M210F-3: 還元は base を通して降りる（keystone） -/

/-- **定理 (M210F-3): 定理3.11（フル仕様）⟹ 系3.12** — 還元は
    フル仕様の言明構造のうち体積の影 `base` のみを通して降りる
    （D-α の keystone）。M5 `cor312_of_multiradial` を `T.base` に
    適用する一行の還元。 -/
theorem cor312_of_311 {R p l L hp hL hodd hdvd V s}
    (T : Theorem311Rep R p l L hp hL hodd hdvd V s) : Cor312 s :=
  cor312_of_multiradial T.base

/-! ## M210F-4: Szpiro まで base 経由で再輸出 -/

/-- **定理 (M210F-4): 定理3.11（フル仕様）+ 体積計算 ⟹ Szpiro 型
    不等式** — M5 `szpiro_of_multiradial` を `T.base` に適用。フル
    仕様の表現から `base` 経由で Szpiro（→ ABC 型帰結）の全論理経路が
    接続される。 -/
theorem szpiro_of_311 {R p l L hp hL hodd hdvd V s}
    (T : Theorem311Rep R p l L hp hL hodd hdvd V s)
    (comp : LogVolumeComputation s) :
    (comp.a - 1) * s.logq ≤ comp.err :=
  szpiro_of_multiradial T.base comp

/-! ## M210F-5: capstone — def / exists（四本柱からの合成） -/

/-- **M210F-5a: フル仕様 witness の構成子** — 体積の影は具体 witness
    `base311Rep`、対数殻・不定性・log-Kummer は各層の具体 witness
    （`logShellData` / `indeterminaciesData` / `logKummerData`）で埋め、
    mono-theta 環境 `e` のみ引数に取る choice-free コンストラクタ。 -/
def theorem311RepData (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1)
    (e : MonoThetaEnv R p l L hp hL hodd hdvd) :
    Theorem311Rep R p l L hp hL hodd hdvd m202fVol base311Skel where
  base := base311Rep
  env := e
  shell := logShellData
  ind := indeterminaciesData
  kummer := logKummerData

/-- **定理 (M210F-5b): フル仕様 `Theorem311Rep` の存在** — p 素数・
    l = 2L+1 ∣ p−1 なら、定理3.11 のフル仕様言明構造（体積の影 +
    mono-theta 環境 + 対数殻 + 不定性 + log-Kummer）が存在する。
    mono-theta 環境は M196F `monoThetaEnv_exists` から Prop（Nonempty）
    の中で取り出す——choice 不要。他の三本柱は具体 witness def。 -/
theorem theorem311Rep_exists (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) :
    Nonempty (Theorem311Rep R p l L hp hL hodd hdvd m202fVol base311Skel) := by
  obtain ⟨e⟩ := monoThetaEnv_exists R p l L hp hL hodd hdvd
  exact ⟨theorem311RepData R p l L hp hL hodd hdvd e⟩

/-
D-α-5 完了: 定理3.11 の言明構造 (i)(a)(b)(c)/(Ind1–3)/(ii) を、体積の影
`base` の上のフィールドとして露出するフル仕様型 `Theorem311Rep` に束ね、
還元 `cor312_of_311`（→ `szpiro_of_311`）が `base` を通して降りることを
機械検証した（keystone）。四本柱 M196F/M201F/M202F/M205F は各 `…_exists`
/具体 witness で choice-free に合成される（`theorem311Rep_exists`）。
各フィールドが具体曲線データの実構成要素であることの同定と
`MultiradialInput` の解析的 realization は正直な限定として D-β に分離する。
-/

end IUT
