/-
# M216F: ガウスパイロットのフル仕様充足模型（柱D D-α-6・並行部品）

柱D D-α プログラム（issue #38 詳細化ラウンド）の総合弾。D-α-5（M210F
`Theorem311Rep`）が立てたフル仕様の表現型を、**具体的なガウスパイロット
データ**で充足する。M210F の witness（`theorem311RepData`）は base の
Θ-正則包の体積が抽象プレースホルダ（−logTheta = 1）だったが、本層は
base の Θ-正則包の体積を**実際のガウス因子 gaussDiv l の次数
Σ_{k≤l} w(k)·k²（wssq、M135F/M158F）そのもの**に据え、かつ shell
フィールドを M201F の**具体的な対数殻 `gaussLogShell`**（殻の体積 =
wssq）に結びつける。すなわち定理3.11 のフル仕様言明構造が、抽象点では
なく実在のテータ値データで inhabited であることを示す。

  * M216F-1 `gaussBase311Rep` — ガウス骨格 `gaussSkeletonW w l` 上の
    Int 値多輻的表現。Θ-正則包の体積 = wssq w l = Σ w(k)·k²
    （base311Rep の placeholder 1 ではなく実際のガウス次数）。
  * M216F-2 `gaussPilot311` — **本丸**: base = `gaussBase311Rep`
    （実ガウス次数）・shell = `logShellData`（M201F の gauss 殻）・
    env/ind/kummer = 各柱の witness、で埋めたフル仕様 `Theorem311Rep`。
  * M216F-3 `cor312_of_gaussPilot311` — 還元は base を通して降りる
    （`cor312_of_311`、mono-theta 環境 e から choice-free に構成）。
  * M216F-4 `gaussPilot311_cor312` — base 単独の系3.12 降下（env 不要）。
  * M216F-5 `gaussPilot311_base_vol_wssq` — base の Θ-正則包の体積 =
    Σ w(k)·k²（Int 値・rfl）。この模型の (i)(a) が実 Θ-hull 体積。
  * M216F-6 `gaussPilot311_shell_vol_wssq` — shell 殻の体積 =
    Σ w(k)·k²（realEq・M201F `gaussLogShell_vol_wssq` の再輸出）。
  * M216F-7 capstone: `GaussPilot311Data` / `def` / `…_exists`。

## 意義

D-α-6（issue #38 詳細化ラウンド）は、D-α-5 のフル仕様型 `Theorem311Rep`
が「体積値 −1 の抽象点」ではなく**実在のガウスパイロットデータ**で充足
可能であることを機械検証する。base の Θ-正則包の体積は実際のガウス因子
gaussDiv l の総次数 Σ w(k)·k²（wssq）に一致し、shell フィールドは M201F
の具体的な対数殻 `gaussLogShell`（殻の体積 = wssq）に結びつく。四本柱
env/shell/ind/kummer は各 witness で埋まり、還元 `cor312_of_311` は base
を通して降りる。すなわちフル仕様の言明構造 (i)(a)(b)(c)/(Ind1–3)/(ii) が
**具体的な Θ-値データで inhabited**であることを示す、M210F の demo witness
より一段具体的な充足模型である。

## 正直な限定

* `Theorem311Rep.base` は **Int 値**の `MultiradialRep V s`（体積は
  `Int` 値）を要求するため、真のガウスパイロット `gaussPilotRepW`
  （**実数値** `RealMultiradialRep`）を base フィールドへ直接差し込む
  ことは型が合わず不可能である。本層は base を **Int 値**で再構成し、
  Θ-正則包の体積が実ガウス次数 wssq w l（の整数化）に一致するよう
  据える——これは M210F の placeholder 1 より具体的だが、shell が
  実数値 gauss 殻であるのに対し base は Int 値の再構成である
  （実数値 base の完全 threading は将来層）。
* 本模型は M141F/M158F/M201F と同じく**体積値そのものを領域とする
  充足デモ模型**（Region = ℤ/ℝ・vol = id）の上にあり、遠アーベル
  復元・エタールテータ剛性による `MultiradialRep` の**構成そのもの**
  （= D-β）ではない。各フィールドが具体曲線データの実構成要素で
  あることの同定と `MultiradialInput` の解析的 realization は D-β。
* 重み w は ℕ 値（log p_k の整数化）で、実数値 log p の構成は将来層。

継承 Classical: 本モジュール自身は新規 Classical.choice を導入しない
（env witness は `monoThetaEnv_exists` から Prop 内で choice-free に
取り出す）。下流の柱経由で継承する公理があれば `#print axioms` に
現れる（propext/Quot.sound の範囲）。sorry なし・禁止タクティク不使用
（core Lean のみ）。サブエージェント並行部品（tier-M）。
-/
import IUT.Multiradial311

namespace IUT

/-! ## M216F-1: ガウス骨格上の Int 値 base（実 Θ-hull 体積） -/

/-- **M216F-1: ガウス骨格上の base 多輻的表現** — ガウス骨格
    `gaussSkeletonW w l`（logTheta := −wssq w l）の上の Int 充足模型
    `m202fVol`（Region = ℤ・vol = id）上の concrete `MultiradialRep`。
    M210F の `base311Rep` は Θ-正則包の体積が placeholder 1 だったが、
    本 base は **Θ-正則包の体積 = wssq w l = Σ_{k≤l} w(k)·k²**、すなわち
    実際のガウス因子 gaussDiv l の総次数の整数化に据える。vol_hull は
    gaussSkeletonW.logTheta の二重否定を `Int.neg_neg` で外して閉じる。 -/
def gaussBase311Rep (w : Nat → Nat) (l : Nat) :
    MultiradialRep m202fVol (gaussSkeletonW w l) where
  Ind := Unit
  ind0 := ()
  shell := ((wssq w l : Nat) : Int)
  image := fun _ => -1
  image_in_shell := fun _ => by
    show (-1 : Int) ≤ ((wssq w l : Nat) : Int)
    have h := Int.natCast_nonneg (wssq w l)
    omega
  hullTheta := ((wssq w l : Nat) : Int)
  image_in_hull := fun _ => by
    show (-1 : Int) ≤ ((wssq w l : Nat) : Int)
    have h := Int.natCast_nonneg (wssq w l)
    omega
  qRegion := -1
  q_realized := ⟨(), by show (-1 : Int) ≤ (-1 : Int); omega⟩
  vol_hull := by
    show ((wssq w l : Nat) : Int) = -(-((wssq w l : Nat) : Int))
    rw [Int.neg_neg]
  vol_q := rfl

/-! ## M216F-2: フル仕様充足模型（本丸） -/

/-- **M216F-2: ガウスパイロットのフル仕様充足模型（本丸）** — D-α-5 の
    `Theorem311Rep` を、base = `gaussBase311Rep`（実ガウス次数 Θ-hull
    体積）・shell = `logShellData`（M201F の具体的対数殻 gaussLogShell、
    殻の体積 = wssq）・env/ind/kummer = 各柱 witness、で埋めた
    フル仕様言明構造。mono-theta 環境 `e` のみ引数に取る choice-free
    コンストラクタ。M210F の demo witness より一段具体的な充足模型。 -/
def gaussPilot311 (R : CRing) (p l L : Nat) (hp : IsPrime p) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) (w : Nat → Nat)
    (e : MonoThetaEnv R p l L hp hL hodd hdvd) :
    Theorem311Rep R p l L hp hL hodd hdvd m202fVol (gaussSkeletonW w l) where
  base := gaussBase311Rep w l
  env := e
  shell := logShellData
  ind := indeterminaciesData
  kummer := logKummerData

/-! ## M216F-3: 還元は base を通して降りる（cor312_of_311 経由） -/

/-- **定理 (M216F-3): ガウスフル仕様模型 ⟹ 系3.12（cor312_of_311 経由）**
    — フル仕様模型 `gaussPilot311` を D-α keystone `cor312_of_311` に
    通す。還元は base（実ガウス次数の Θ-hull 体積）のみを経由して降りる。 -/
theorem cor312_of_gaussPilot311 (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) (w : Nat → Nat)
    (e : MonoThetaEnv R p l L hp hL hodd hdvd) :
    Cor312 (gaussSkeletonW w l) :=
  cor312_of_311 (gaussPilot311 R p l L hp hL hodd hdvd w e)

/-! ## M216F-4: base 単独の系3.12 降下（env 不要） -/

/-- **定理 (M216F-4): base 単独の系3.12 降下** — env を経由せず
    `gaussBase311Rep` を直接 M5 `cor312_of_multiradial` に通す簡易版。
    ガウス骨格 `gaussSkeletonW w l` の系3.12 結論形が実ガウス次数の
    体積簿記で降りる。 -/
theorem gaussPilot311_cor312 (w : Nat → Nat) (l : Nat) :
    Cor312 (gaussSkeletonW w l) :=
  cor312_of_multiradial (gaussBase311Rep w l)

/-! ## M216F-5: base の Θ-正則包の体積 = Σ w(k)·k² -/

/-- **定理 (M216F-5): base の Θ-正則包の体積 = Σ w(k)·k²** — 本模型の
    base（(i)(a) の Θ-hull）の体積が、まさに実際のガウス因子 gaussDiv l
    の総次数 wssq w l の整数化。M210F の placeholder 1 との差がここに
    現れる（本模型は実 Θ-hull 体積を担う）。id 体積で rfl。 -/
theorem gaussPilot311_base_vol_wssq (w : Nat → Nat) (l : Nat) :
    m202fVol.vol (gaussBase311Rep w l).hullTheta = ((wssq w l : Nat) : Int) :=
  rfl

/-! ## M216F-6: shell 殻の体積 = Σ w(k)·k²（実数値・再輸出） -/

/-- **定理 (M216F-6): shell 殻の体積 = Σ w(k)·k²** — 本模型の shell
    フィールド `logShellData` の具体的対数殻 gaussLogShell の体積が、
    まさに重み付きガウス因子の次数 wssq w l の実数化。M201F
    `gaussLogShell_vol_wssq`（= M135F `rlogVol_gauss_w`）の再輸出。
    模型の (i)(a) が実 Θ-hull 体積 Σ w(k)·k² であることの実数側言明。 -/
theorem gaussPilot311_shell_vol_wssq (w : Nat → Nat) (l : Nat) :
    realEq (realVolumeTheory.vol (logShellData.container w l).shell)
      (natToReal (wssq w l)) :=
  logShellData.vol_wssq w l

/-! ## M216F-7: capstone — GaussPilot311Data / def / exists -/

/-- **M216F-7a: 総括** — ガウスパイロットのフル仕様充足模型のデータ。
    フル仕様 `Theorem311Rep` の存在（実ガウス base + gauss 殻 +
    四本柱）、系3.12 降下、base の実 Θ-hull 体積、shell 殻の体積を束ねる。 -/
structure GaussPilot311Data where
  /-- 実ガウスデータで充足されたフル仕様 `Theorem311Rep` の存在。 -/
  rep : ∀ (R : CRing) (p l L : Nat) (hp : IsPrime p) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) (w : Nat → Nat),
    Nonempty (Theorem311Rep R p l L hp hL hodd hdvd m202fVol
      (gaussSkeletonW w l))
  /-- 系3.12 の結論形（base 単独降下）。 -/
  cor312 : ∀ (w : Nat → Nat) (l : Nat), Cor312 (gaussSkeletonW w l)
  /-- base の Θ-正則包の体積 = Σ w(k)·k²（Int 値）。 -/
  base_vol : ∀ (w : Nat → Nat) (l : Nat),
    m202fVol.vol (gaussBase311Rep w l).hullTheta = ((wssq w l : Nat) : Int)
  /-- shell 殻の体積 = Σ w(k)·k²（実数値）。 -/
  shell_vol : ∀ (w : Nat → Nat) (l : Nat),
    realEq (realVolumeTheory.vol (logShellData.container w l).shell)
      (natToReal (wssq w l))

/-- **M216F-7b: witness** — フル仕様の存在は mono-theta 環境を
    `monoThetaEnv_exists` から Prop（Nonempty）内で choice-free に
    取り出して `gaussPilot311` に供給する。他フィールドは具体 witness。 -/
def gaussPilot311Data : GaussPilot311Data where
  rep := fun R p l L hp hL hodd hdvd w => by
    obtain ⟨e⟩ := monoThetaEnv_exists R p l L hp hL hodd hdvd
    exact ⟨gaussPilot311 R p l L hp hL hodd hdvd w e⟩
  cor312 := gaussPilot311_cor312
  base_vol := gaussPilot311_base_vol_wssq
  shell_vol := gaussPilot311_shell_vol_wssq

/-- **M216F-7c: 存在** — ガウスパイロットのフル仕様充足模型は充足可能。 -/
theorem gaussPilot311_exists : Nonempty GaussPilot311Data :=
  ⟨gaussPilot311Data⟩

/-
D-α-6 完了: D-α-5 のフル仕様型 `Theorem311Rep` を、base の Θ-正則包の
体積が実際のガウス因子 gaussDiv l の総次数 Σ w(k)·k²（wssq）に一致する
Int 値 base `gaussBase311Rep` と、M201F の具体的対数殻 `gaussLogShell`
（殻の体積 = wssq）を shell に据えた**具体的なガウスパイロットデータ**で
充足した。還元 `cor312_of_311` は base を通して降りる。実数値 base の
完全 threading（`RealMultiradialRep` の直接差し込み）と各フィールドの
曲線データ同定は正直な限定として D-β に分離する。
-/

end IUT
