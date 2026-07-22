/-
# M141F: ガウスパイロット模型 — Θ-正則包 = 実際のガウス因子の log-volume

柱D の接合弾: M139 の実数値多輻的表現 `RealMultiradialRep` を、
**Θ-正則包の体積が「実際のガウス因子 gaussDiv l（M133）の
log-volume」そのもの**である模型で充足する。M5-4 / M139-6 の
デモ模型は体積値 −1 の抽象点だったが、本弾では [IUTchIII] の
テータパイロットの体積簿記が本物の因子データで実現される:
hullTheta = rlogVol 1 (gaussDiv l)、その体積 = Σj²（M133-3 の
実数の等式 `rlogVol_gauss_eq` が鍵）。

  * M141F-1 `gaussSkeleton` — logTheta := −Σj² と仕込んだ骨格
    （vol_hull の要求 vol(hullTheta) ≈ intToReal (−logTheta) が
    Θ 側 log-volume = +Σj² になるよう符号を設定）
  * M141F-2 `gauss_neg_one_le` — 部品: −1 ≤ vol(gaussDiv l)
    （rlogVol_gauss_eq + intToReal の単調性）
  * M141F-3 `gaussPilotRep` — **本丸**: ℝ モデル上の実数値
    多輻的表現で、Θ-正則包 = ガウス因子の log-volume
  * M141F-4 `gaussPilot_cor312` — 実際のガウス因子の体積簿記で
    系3.12 の結論形が実数経由で降りるデモ
  * M141F-5 `gaussPilot_vol_theta` — Θ-包の体積 = Σj²
  * M141F-6 `GaussPilotData` — 総括

意義: [IUTchIV] の log-volume 計算の対象（ガウス因子）と
[IUTchIII] 定理3.11 の出力仕様（多輻的表現）が、形式体系内で
初めて同一の模型の中で接合された。体積側の言明が抽象的な
プレースホルダではなく、QDiv として実在する因子の実数値
log-volume で充たされる。

正直な限定: これは**体積値そのものを領域とする充足デモ模型**
（Region = ℝ・vol = id の M139-3b モデル上）であり、遠アーベル
復元・エタールテータ剛性による `MultiradialRep` の構成そのもの
（柱D 本丸）ではない。`gaussSkeleton` の logq = 1 は正規化で
あり実際の q-パイロット値ではない。また重み w は単位重み
（全素点 log p = 1、M133 の正直申告を引き継ぐ）。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealVolumeTheory

namespace IUT

/-! ## M141F-1: ガウス骨格 -/

/-- **M141F-1: ガウス骨格** — logTheta := −Σj²。`vol_hull` の要求は
    realEq (vol hullTheta) (intToReal (−logTheta)) なので、
    −logTheta = Σj² となり Θ 側の log-volume が +Σj² になる。 -/
def gaussSkeleton (l : Nat) : Skeleton where
  lstar := 2
  hl := by omega
  logq := 1
  hq := by omega
  logTheta := -((ssq l : Nat) : Int)

/-! ## M141F-2: 部品 -/

/-- **M141F-2: 部品** — −1 ≤ vol(gaussDiv l)（rLe）。
    M133-3 の等式で natToReal (ssq l) に書き換え、defeq で
    intToReal に読み替えて単調性に帰着。 -/
theorem gauss_neg_one_le (l : Nat) :
    rLe (intToReal (-1)) (rlogVol (fun _ => 1) (gaussDiv l)) := by
  rw [rlogVol_gauss_eq]
  show rLe (intToReal (-1)) (intToReal ((ssq l : Nat) : Int))
  apply intToReal_mono
  have h := Int.natCast_nonneg (ssq l)
  omega

/-! ## M141F-3: ガウスパイロット表現（本丸） -/

/-- **M141F-3: ガウスパイロット表現（本丸）** — ℝ モデル上の
    実数値多輻的表現で、**Θ-正則包 = 実際のガウス因子の
    log-volume** rlogVol 1 (gaussDiv l)。像は q-領域 −1 と
    ガウス体積の正則包（rmax）、shell はガウス体積そのもの。
    vol_hull は M133-3 `rlogVol_gauss_eq`（実数の Eq）で閉じる。 -/
def gaussPilotRep (l : Nat) :
    RealMultiradialRep realVolumeTheory (gaussSkeleton l) where
  Ind := Unit
  ind0 := ()
  shell := rlogVol (fun _ => 1) (gaussDiv l)
  image := fun _ => rmax (intToReal (-1)) (rlogVol (fun _ => 1) (gaussDiv l))
  image_in_shell := fun _ => rmax_least (gauss_neg_one_le l) (rLe_refl _)
  hullTheta := rlogVol (fun _ => 1) (gaussDiv l)
  image_in_hull := fun _ => rmax_least (gauss_neg_one_le l) (rLe_refl _)
  qRegion := intToReal (-1)
  q_realized := ⟨(), rLe_max_left _ _⟩
  vol_hull := by
    show realEq (rlogVol (fun _ => 1) (gaussDiv l))
      (intToReal (-(-((ssq l : Nat) : Int))))
    rw [rlogVol_gauss_eq, Int.neg_neg]
    exact realEq_refl _
  vol_q := realEq_refl _

/-! ## M141F-4: 系3.12 の結論形のデモ -/

/-- **定理 (M141F-4): ガウス体積簿記による系3.12 デモ** —
    実際のガウス因子の log-volume を Θ-正則包の体積とする模型で、
    系3.12 の結論形が実数経由（M139-5b の反映降下）で降りる。 -/
theorem gaussPilot_cor312 (l : Nat) : Cor312 (gaussSkeleton l) :=
  cor312_of_realMultiradial (gaussPilotRep l)

/-! ## M141F-5: Θ-包の体積 = Σj² -/

/-- **定理 (M141F-5): Θ-包の体積 = Σj²** — ガウスパイロット表現の
    Θ-正則包の体積が、まさにガウス因子の次数 Σ_{j≤l} j² の実数化。 -/
theorem gaussPilot_vol_theta (l : Nat) :
    realEq (realVolumeTheory.vol (gaussPilotRep l).hullTheta)
      (natToReal (ssq l)) := by
  show realEq (rlogVol (fun _ => 1) (gaussDiv l)) (natToReal (ssq l))
  rw [rlogVol_gauss_eq]
  exact realEq_refl _

/-! ## M141F-6: 総括 -/

/-- **M141F-6a: 総括** — ガウスパイロット模型のデータ。 -/
structure GaussPilotData where
  /-- 全ての l で実数値多輻的表現が充足される（ガウス体積簿記で）。 -/
  rep : ∀ l, Nonempty (RealMultiradialRep realVolumeTheory (gaussSkeleton l))
  /-- 系3.12 の結論形。 -/
  cor312 : ∀ l, Cor312 (gaussSkeleton l)
  /-- Θ-包の体積 = Σj²。 -/
  vol_theta : ∀ l,
    realEq (realVolumeTheory.vol (gaussPilotRep l).hullTheta)
      (natToReal (ssq l))

/-- **M141F-6b: witness**。 -/
def gaussPilotData : GaussPilotData where
  rep := fun l => ⟨gaussPilotRep l⟩
  cor312 := gaussPilot_cor312
  vol_theta := gaussPilot_vol_theta

/-- **M141F-6c: 存在**。 -/
theorem gaussPilot_exists : Nonempty GaussPilotData :=
  ⟨gaussPilotData⟩

end IUT
