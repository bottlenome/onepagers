/-
# M201F: 対数殻テンソルパケット（柱D D-α-2・並行部品）

柱D D-α プログラム（issue #38 詳細化ラウンド, round 101）の (i)(a) 部品。
定理3.11 (i)(a) の**対数殻テンソルパケット** I ⊆ I^Q ——
多輻的像が着地する mono-analytic container（単解析的入れ物）—— を
型として立て、ガウス因子（M133/M135F）の log-volume 言明を
**殻の語彙**で再輸出する。

構成の骨格（既存部品の再利用のみ・体積公式は再証明しない）:

  * M201F-1 `LogShell` — 対数殻テンソルパケットの型:
    実数値体積理論 V 上で、procession 段数 `procLevel` を担い、
    多輻的像 `content` が殻 `shell` に収まる（`content_in_shell`
    = (i)(a) の「mono-analytic containers」性）
  * M201F-2 `logShell_of_rep` — 任意の実数値多輻的表現
    `RealMultiradialRep`（M139）から対数殻データを抽出する
    （image_in_shell を殻の会員性として実現）
  * M201F-3 `gaussLogShell` — M158F の重み付きガウスパイロット
    表現から得た**具体的な対数殻**（殻 = 重み付きガウス因子の
    log-volume rlogVol w (gaussDiv l)）
  * M201F-4 `gaussLogShell_vol_wssq` — **殻の体積 = Σ w(k)·k²**
    （wssq、M135F-3 `rlogVol_gauss_w` の殻語彙への再輸出）
  * M201F-5 `gaussLogShell_content_in_shell` — 多輻的像が殻に
    収まる（会員性）
  * M201F-6 `gaussLogShell_vol_lower` — **procession 正規化下界**:
    w ≥ 1 なら l³ ≤ 3·vol(殻)（M135F-6b `rlogVol_gauss_w_bound`
    の殻語彙表示）
  * M201F-7 `LogShellData` — 総括（Data / def / exists の三点）

## 意義

D-α-2: 定理3.11 (i)(a) の対数殻 = mono-analytic container を型として
立て、ガウス因子（M133/M135F）の log-volume 閉形式・下界を**殻の
語彙**（殻の体積 = wssq、像 ⊆ 殻、procession 正規化下界）に再輸出する。
D-α-5 の shellData フィールドへ供給する部品であり、テータパイロットの
q-次数簿記が「単解析的入れ物の体積」として言明される。procession
重み（procTotal の閉形式 2·procTotal L = (L+1)(L+2)）を殻が担う。

## 正直な限定

* 本モジュールが立てる `LogShell` は**単一の像 content**を担う
  concrete slice であり、原文の (i)(b)(c)（splitting monoid Ψ⊥_LGP・
  数体 M_MOD_j の直和 ∏_{j∈Fl⋇} I^Q）を含む**一般のテンソルパケット**
  ではない。指数付き像族 (Ind1)×(Ind2) の完全な packet 抽象は
  MultiradialRep の image 族に留め、殻には代表像のみ輸出する。
* 不定性 (Ind1–3) の構造・log-Kummer 対応（(ii)）・Kummer 同型は
  D-α-3/4（別部品）の担当であり本層では扱わない。
* `gaussLogShell` は M158F と同じく**体積値そのものを領域とする
  充足デモ模型**（realVolumeTheory: Region = ℝ・vol = id）の上に
  あり、遠アーベル復元・エタールテータ剛性による `MultiradialRep`
  の**構成そのもの**（= D-β）ではない。重み w は ℕ 値（log p_k の
  整数化）で、実数値 log p の構成は将来層。

全て選択公理不使用（M139/M158F 経由の Classical は継承しない範囲で
本層は新規公理を導入しない）。サブエージェント並行部品（tier-M）。
-/
import IUT.Multiradial
import IUT.GaussPilotWeighted

namespace IUT

/-! ## M201F-1: 対数殻テンソルパケットの型 -/

/-- **M201F-1: 対数殻テンソルパケット**（定理3.11 (i)(a)）——
    実数値体積理論 `V` 上の mono-analytic container。procession の
    段数 `procLevel` を重みとして担い、多輻的像 `content` が殻 `shell`
    に収まる（`content_in_shell`）。原文の「対数殻 I ⊆ I^Q」の
    「像が入れ物に収まる」構造の型化。 -/
structure LogShell (V : RealVolumeTheory) where
  /-- procession の段数 L（procTotal L が正規化分母の源）。 -/
  procLevel : Nat
  /-- 対数殻 = mono-analytic container（入れ物）。 -/
  shell : V.Region
  /-- 殻に着地する多輻的像（代表）。 -/
  content : V.Region
  /-- (i)(a) の会員性: 像は殻に収まる。 -/
  content_in_shell : V.le content shell

/-! ## M201F-2: 多輻的表現からの抽出 -/

/-- **M201F-2: 対数殻の抽出** — 任意の実数値多輻的表現
    `RealMultiradialRep`（M139）から対数殻データを取り出す。
    殻 = `M.shell`、代表像 = `M.image M.ind0`、会員性 = `image_in_shell`。
    定理3.11 (i)(a) の「像が単解析的入れ物に収まる」を殻の会員性として
    実現する。procession 段数 `L` は引数で受ける。 -/
def logShell_of_rep {V : RealVolumeTheory} {s : Skeleton}
    (M : RealMultiradialRep V s) (L : Nat) : LogShell V where
  procLevel := L
  shell := M.shell
  content := M.image M.ind0
  content_in_shell := M.image_in_shell M.ind0

/-! ## M201F-3: 具体的な対数殻（重み付きガウスパイロット模型） -/

/-- **M201F-3: 具体的な対数殻** — M158F の重み付きガウスパイロット
    表現 `gaussPilotRepW`（Θ-正則包 = 重み付きガウス因子の log-volume）
    から抽出した対数殻。殻 = rlogVol w (gaussDiv l)、procession 段数
    = l。テータパイロットの q-次数簿記を担う実在の因子で殻が充たされる。 -/
def gaussLogShell (w : Nat → Nat) (l : Nat) : LogShell realVolumeTheory :=
  logShell_of_rep (gaussPilotRepW w l) l

/-! ## M201F-4: 殻の体積 = Σ w(k)·k²（再輸出の本丸） -/

/-- **定理 (M201F-4): 殻の体積 = Σ w(k)·k²** — 具体的な対数殻の
    体積が、まさに重み付きガウス因子の次数 wssq w l の実数化。
    M135F-3 `rlogVol_gauss_w` の殻語彙への再輸出。 -/
theorem gaussLogShell_vol_wssq (w : Nat → Nat) (l : Nat) :
    realEq (realVolumeTheory.vol (gaussLogShell w l).shell)
      (natToReal (wssq w l)) := by
  show realEq (rlogVol w (gaussDiv l)) (natToReal (wssq w l))
  rw [rlogVol_gauss_w]
  exact realEq_refl _

/-! ## M201F-5: 像が殻に収まる（会員性） -/

/-- **定理 (M201F-5): 多輻的像 ⊆ 殻** — 具体的な対数殻でも
    (i)(a) の会員性が成立（構成から直ちに）。 -/
theorem gaussLogShell_content_in_shell (w : Nat → Nat) (l : Nat) :
    realVolumeTheory.le (gaussLogShell w l).content (gaussLogShell w l).shell :=
  (gaussLogShell w l).content_in_shell

/-! ## M201F-6: procession 正規化下界（殻語彙表示） -/

/-- **定理 (M201F-6): 殻の体積下界（procession 正規化）** —
    w ≥ 1（各素点の log p ≥ 1 の正規化）なら l³ ≤ 3·vol(殻)（rLe）。
    M135F-6b `rlogVol_gauss_w_bound` が対数殻の体積の言明になる:
    テータパイロット総 q-次数の実数下界が、単解析的入れ物の体積の
    言明として成立。 -/
theorem gaussLogShell_vol_lower {w : Nat → Nat} (hw : ∀ k, 1 ≤ w k)
    (l : Nat) : rLe (natToReal (l * l * l))
      (rmul (natToReal 3) (realVolumeTheory.vol (gaussLogShell w l).shell)) := by
  show rLe (natToReal (l * l * l))
    (rmul (natToReal 3) (rlogVol w (gaussDiv l)))
  exact rlogVol_gauss_w_bound hw l

/-! ## M201F-7: procession 重みの閉形式（殻の正規化簿記） -/

/-- **定理 (M201F-7pre): 対数殻の procession 正規化分母** —
    2·procTotal L = (L+1)(L+2)（M5-6 `two_mul_procTotal` の再輸出）。
    対数殻が担う procession 段重みの閉形式。 -/
theorem logShell_proc_closed (L : Nat) :
    2 * procTotal L = (L + 1) * (L + 2) :=
  two_mul_procTotal L

/-! ## M201F-8: 総括 -/

/-- **M201F-8a: 総括** — 対数殻テンソルパケットの再輸出データ。
    D-α-5 の shellData フィールドへ供給する束。 -/
structure LogShellData where
  /-- 全ての w・l で具体的な対数殻が存在する。 -/
  container : (Nat → Nat) → Nat → LogShell realVolumeTheory
  /-- (i)(a) の会員性: 像 ⊆ 殻。 -/
  content_in_shell : ∀ (w : Nat → Nat) (l : Nat),
    realVolumeTheory.le (container w l).content (container w l).shell
  /-- 殻の体積 = Σ w(k)·k²（再輸出の本丸）。 -/
  vol_wssq : ∀ (w : Nat → Nat) (l : Nat),
    realEq (realVolumeTheory.vol (container w l).shell) (natToReal (wssq w l))
  /-- procession 正規化下界（w ≥ 1）。 -/
  vol_lower : ∀ {w : Nat → Nat}, (∀ k, 1 ≤ w k) → ∀ l,
    rLe (natToReal (l * l * l))
      (rmul (natToReal 3) (realVolumeTheory.vol (container w l).shell))
  /-- procession 段重みの閉形式（正規化分母）。 -/
  proc_closed : ∀ L, 2 * procTotal L = (L + 1) * (L + 2)

/-- **M201F-8b: witness**。 -/
def logShellData : LogShellData where
  container := gaussLogShell
  content_in_shell := gaussLogShell_content_in_shell
  vol_wssq := gaussLogShell_vol_wssq
  vol_lower := gaussLogShell_vol_lower
  proc_closed := logShell_proc_closed

/-- **M201F-8c: 存在** — 対数殻テンソルパケットの再輸出データは充足可能。 -/
theorem logShell_exists : Nonempty LogShellData :=
  ⟨logShellData⟩

/-
D-α-2 完了: 定理3.11 (i)(a) の対数殻 = mono-analytic container を型
`LogShell` として立て、ガウス因子（M133/M135F）の log-volume を殻の
語彙（殻の体積 = wssq、像 ⊆ 殻、procession 正規化下界 l³ ≤ 3·vol）へ
再輸出した。体積公式は M135F/M158F を再利用し再証明していない。
一般のテンソルパケット（(i)(b)(c)・不定性 (Ind1–3)）と D-β の構成
本体は正直な限定として分離される。次段は D-α-5 の shellData 統合。
-/

end IUT
