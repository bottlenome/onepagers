/-
# M158F: 重み付きガウスパイロット模型 — Θ-正則包 = 重み付き因子体積の充足模型（柱D）

M141F（IUT/GaussPilotRep.lean）のガウスパイロット模型は単位重み
（全素点 log p = 1）での充足だった。本弾は M135F
（IUT/WeightedGauss.lean）の重み付き log-volume 評価と合流させ、
**一般素点重み w : ℕ → ℕ を任意に受けた**模型で同じ充足を実現する:
hullTheta = rlogVol w (gaussDiv l)、その体積 = Σ w(k)·k²（wssq）。
鍵は M135F-3 の実数の等式 `rlogVol_gauss_w`。

  * M158F-1 `gaussSkeletonW` — logTheta := −wssq w l と仕込んだ骨格
    （vol_hull の要求 vol(hullTheta) ≈ intToReal (−logTheta) が
    Θ 側 log-volume = +Σ w(k)·k² になるよう符号を設定）
  * M158F-2 `gauss_neg_one_le_w` — 部品: −1 ≤ vol_w(gaussDiv l)
    （rlogVol_gauss_w + intToReal の単調性）
  * M158F-3 `gaussPilotRepW` — **本丸**: ℝ モデル上の実数値
    多輻的表現で、Θ-正則包 = 重み付きガウス因子の log-volume
  * M158F-4 `gaussPilotW_cor312` — 重み付きガウス体積簿記で
    系3.12 の結論形が実数経由で降りるデモ
  * M158F-5 `gaussPilotW_vol_theta` — Θ-包の体積 = Σ w(k)·k²
  * M158F-6 `gaussPilotW_volume_lower` — **重み下界との接続**:
    w ≥ 1 なら l³ ≤ 3·vol(Θ-包)（M135F-6b の模型内表示）
  * M158F-7 `GaussPilotWeightedData` — 総括

意義: M141F（単位重み模型）× M135F（重み付き体積）の合流。
実素点重みの整数化 w を任意に受けた模型で系3.12 の結論形が
実数経由で降り、w ≥ 1 では体積下界 l³ ≤ 3·vol も模型内の
言明になる。テータパイロット総 q-次数の実数下界が、重み付き
模型の Θ-包の体積の言明として成立する。

正直な限定: M141F と同じく、これは**体積値そのものを領域とする
充足デモ模型**（Region = ℝ・vol = id の M139-3b モデル上）であり、
遠アーベル復元・エタールテータ剛性による `MultiradialRep` の
構成そのもの（柱D 本丸）ではない。`gaussSkeletonW` の logq = 1 は
正規化であり実際の q-パイロット値ではない。重み w は ℕ 値
（log p_k の整数化）で、実数値 log p の構成は将来層。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.GaussPilotRep
import IUT.WeightedGauss

namespace IUT

/-! ## M158F-1: 重み付きガウス骨格 -/

/-- **M158F-1: 重み付きガウス骨格** — logTheta := −wssq w l。
    `vol_hull` の要求は realEq (vol hullTheta) (intToReal (−logTheta))
    なので、−logTheta = Σ w(k)·k² となり Θ 側の log-volume が
    +wssq w l になる。 -/
def gaussSkeletonW (w : Nat → Nat) (l : Nat) : Skeleton where
  lstar := 2
  hl := by omega
  logq := 1
  hq := by omega
  logTheta := -((wssq w l : Nat) : Int)

/-! ## M158F-2: 部品 -/

/-- **M158F-2: 部品** — −1 ≤ vol_w(gaussDiv l)（rLe）。
    M135F-3 の等式で natToReal (wssq w l) に書き換え、defeq で
    intToReal に読み替えて単調性に帰着。 -/
theorem gauss_neg_one_le_w (w : Nat → Nat) (l : Nat) :
    rLe (intToReal (-1)) (rlogVol w (gaussDiv l)) := by
  rw [rlogVol_gauss_w]
  show rLe (intToReal (-1)) (intToReal ((wssq w l : Nat) : Int))
  apply intToReal_mono
  have h := Int.natCast_nonneg (wssq w l)
  omega

/-! ## M158F-3: 重み付きガウスパイロット表現（本丸） -/

/-- **M158F-3: 重み付きガウスパイロット表現（本丸）** — ℝ モデル
    上の実数値多輻的表現で、**Θ-正則包 = 重み付きガウス因子の
    log-volume** rlogVol w (gaussDiv l)。像は q-領域 −1 と重み付き
    ガウス体積の正則包（rmax）、shell は重み付きガウス体積そのもの。
    vol_hull は M135F-3 `rlogVol_gauss_w`（実数の Eq）で閉じる。 -/
def gaussPilotRepW (w : Nat → Nat) (l : Nat) :
    RealMultiradialRep realVolumeTheory (gaussSkeletonW w l) where
  Ind := Unit
  ind0 := ()
  shell := rlogVol w (gaussDiv l)
  image := fun _ => rmax (intToReal (-1)) (rlogVol w (gaussDiv l))
  image_in_shell := fun _ => rmax_least (gauss_neg_one_le_w w l) (rLe_refl _)
  hullTheta := rlogVol w (gaussDiv l)
  image_in_hull := fun _ => rmax_least (gauss_neg_one_le_w w l) (rLe_refl _)
  qRegion := intToReal (-1)
  q_realized := ⟨(), rLe_max_left _ _⟩
  vol_hull := by
    show realEq (rlogVol w (gaussDiv l))
      (intToReal (-(-((wssq w l : Nat) : Int))))
    rw [rlogVol_gauss_w, Int.neg_neg]
    exact realEq_refl _
  vol_q := realEq_refl _

/-! ## M158F-4: 系3.12 の結論形のデモ -/

/-- **定理 (M158F-4): 重み付きガウス体積簿記による系3.12 デモ** —
    任意重み w のガウス因子の log-volume を Θ-正則包の体積とする
    模型で、系3.12 の結論形が実数経由（M139-5b の反映降下）で
    降りる。 -/
theorem gaussPilotW_cor312 (w : Nat → Nat) (l : Nat) :
    Cor312 (gaussSkeletonW w l) :=
  cor312_of_realMultiradial (gaussPilotRepW w l)

/-! ## M158F-5: Θ-包の体積 = Σ w(k)·k² -/

/-- **定理 (M158F-5): Θ-包の体積 = Σ w(k)·k²** — 重み付きガウス
    パイロット表現の Θ-正則包の体積が、まさに重み付きガウス因子の
    次数 wssq w l の実数化。 -/
theorem gaussPilotW_vol_theta (w : Nat → Nat) (l : Nat) :
    realEq (realVolumeTheory.vol (gaussPilotRepW w l).hullTheta)
      (natToReal (wssq w l)) := by
  show realEq (rlogVol w (gaussDiv l)) (natToReal (wssq w l))
  rw [rlogVol_gauss_w]
  exact realEq_refl _

/-! ## M158F-6: 重み下界との接続 -/

/-- **定理 (M158F-6): 体積下界の模型内表示（M135F の本丸の合流）** —
    w ≥ 1 なら l³ ≤ 3·vol(Θ-正則包)（rLe）。vol hullTheta は defeq で
    rlogVol w (gaussDiv l) なので、M135F-6b `rlogVol_gauss_w_bound`
    がそのまま模型の Θ-包の体積の言明になる: **テータパイロット
    総 q-次数の実数下界が、重み付き模型の Θ-包の体積の言明として
    成立**。 -/
theorem gaussPilotW_volume_lower {w : Nat → Nat} (hw : ∀ k, 1 ≤ w k)
    (l : Nat) : rLe (natToReal (l * l * l))
      (rmul (natToReal 3)
        (realVolumeTheory.vol (gaussPilotRepW w l).hullTheta)) := by
  show rLe (natToReal (l * l * l))
    (rmul (natToReal 3) (rlogVol w (gaussDiv l)))
  exact rlogVol_gauss_w_bound hw l

/-! ## M158F-7: 総括 -/

/-- **M158F-7a: 総括** — 重み付きガウスパイロット模型のデータ。 -/
structure GaussPilotWeightedData where
  /-- 全ての w・l で実数値多輻的表現が充足される（重み付き
      ガウス体積簿記で）。 -/
  rep : ∀ (w : Nat → Nat) (l : Nat),
    Nonempty (RealMultiradialRep realVolumeTheory (gaussSkeletonW w l))
  /-- 系3.12 の結論形。 -/
  cor312 : ∀ (w : Nat → Nat) (l : Nat), Cor312 (gaussSkeletonW w l)
  /-- Θ-包の体積 = Σ w(k)·k²。 -/
  vol_theta : ∀ (w : Nat → Nat) (l : Nat),
    realEq (realVolumeTheory.vol (gaussPilotRepW w l).hullTheta)
      (natToReal (wssq w l))
  /-- 体積下界の模型内表示（w ≥ 1）。 -/
  volume_lower : ∀ {w : Nat → Nat}, (∀ k, 1 ≤ w k) → ∀ l,
    rLe (natToReal (l * l * l))
      (rmul (natToReal 3)
        (realVolumeTheory.vol (gaussPilotRepW w l).hullTheta))

/-- **M158F-7b: witness**。 -/
def gaussPilotWeightedData : GaussPilotWeightedData where
  rep := fun w l => ⟨gaussPilotRepW w l⟩
  cor312 := gaussPilotW_cor312
  vol_theta := gaussPilotW_vol_theta
  volume_lower := gaussPilotW_volume_lower

/-- **M158F-7c: 存在**。 -/
theorem gaussPilotWeighted_exists : Nonempty GaussPilotWeightedData :=
  ⟨gaussPilotWeightedData⟩

end IUT
