/-
# M135F: 重み付きガウス因子 — 素点重み w での log-volume 評価

M133（IUT/GaussianDivisor.lean）はガウス因子 Σ_{j≤l} j²·[p_j] の
log-volume を**単位重み**（全素点 log p = 1 の正規化）で評価し、
「実際の素点重みでの評価は次層」と正直申告していた。本層はその
申告を解消する: 重み w : ℕ → ℕ（k 番目の素点の log p_k の整数化）を
**任意に**受け、ガウス因子の次数・log-volume を重み付き平方和

  wssq w l = Σ_{k≤l} w(k)·k²

に同定する。さらに重みの単調性・単位重みとの整合・w ≥ 1 での
体積下界 l³ ≤ 3·vol_w を実数の言葉（rLe）で機械検証する。

  * M135F-1 `wssq` — 重み付き平方和 Σ_{k≤l} w(k)·k²（nsum で直接定義）
  * M135F-2 `gaussDiv_deg_w` — **次数の同定（本丸）**:
    degN w (gaussDiv l) = wssq w l（M133-2 の w-一般化。if 剥がしの
    帰納 `gauss_nsum_w` で範囲内の if を落とす）
  * M135F-3 `rlogVol_gauss_w` — log-volume = wssq（実数の等式そのもの、
    M133-3 の w-一般化）
  * M135F-4 `nsum_mono` / `wssq_mono` / `rlogVol_gauss_w_mono` —
    **重みの単調性**: w ≤ w'（点ごと）なら vol_w ≤ vol_{w'}（rLe）
  * M135F-5 `wssq_one` / `rlogVol_gauss_w_one` — **単位重みとの整合**:
    w ≡ 1 で wssq = ssq に退化し、M133-3 が再導出される
  * M135F-6 `wssq_lower` / `rlogVol_gauss_w_bound` — **体積下界の
    重み付き版**: w ≥ 1（各素点の log p ≥ 1 の正規化）なら
    l³ ≤ 3·vol_w(gaussDiv l)（rLe）。M132-4 の下界が任意の
    正規化重みに持ち上がる
  * M135F-7 `WeightedGaussData` — 総括

## 意義

M133 の正直申告解消（柱C C-1 × 柱E E-2）。実素点重み log p_k の
整数化 w を任意に受け、vol_w(gaussDiv) = Σ w(j)·j² の同定・
重み単調性・w ≥ 1 での体積下界を機械検証。[IUTchIV] の log-volume
計算の素点ごとの重み付けが形式体系内で自由パラメータになった。

## 正直な申告

* 重み w は ℕ 値（log p_k の整数化）。実数値 log p の構成
  （対数関数）は ℝ の冪級数論として将来層。
* 下界 M135F-6 の仮定 w ≥ 1 は「各素点の log-volume 寄与が単位以上」
  という正規化であり、素数の枚挙・w k = ⌊log p_k⌋ という解析的内容は
  M51F 以来の申告どおり形式化していない。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.GaussianDivisor

namespace IUT

/-! ## M135F-1: 重み付き平方和 -/

/-- **M135F-1: 重み付き平方和** wssq w l = Σ_{k≤l} w(k)·k²
    （nsum で直接定義。w ≡ 1 で ssq に退化する）。 -/
def wssq (w : Nat → Nat) (l : Nat) : Nat :=
  nsum (fun k => w k * (k * k)) (l + 1)

/-! ## M135F-2: 次数の同定 -/

/-- if 剥がし（M133 `gauss_nsum` の w-一般化）: 範囲内では
    重み × ガウス重複度 = w(k)·k²。 -/
theorem gauss_nsum_w (w : Nat → Nat) (l : Nat) : ∀ n, n ≤ l + 1 →
    nsum (fun k => w k * (if k ≤ l then k * k else 0)) n
      = nsum (fun k => w k * (k * k)) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    show nsum (fun k => w k * (if k ≤ l then k * k else 0)) n
        + w n * (if n ≤ l then n * n else 0)
      = nsum (fun k => w k * (k * k)) n + w n * (n * n)
    rw [ih (by omega), if_pos (by omega : n ≤ l)]

/-- **定理 (M135F-2): 次数の同定（本丸）** — 任意重み w での
    ガウス因子の次数 = 重み付き平方和 Σ w(k)·k²。 -/
theorem gaussDiv_deg_w (w : Nat → Nat) (l : Nat) :
    degN w (gaussDiv l) = wssq w l := by
  show nsum (fun k => w k * (if k ≤ l then k * k else 0)) (l + 1)
      = wssq w l
  rw [gauss_nsum_w w l (l + 1) (Nat.le_refl _)]
  rfl

/-! ## M135F-3: log-volume の同定 -/

/-- **定理 (M135F-3): log-volume = wssq**（実数の等式そのもの、
    M133-3 の w-一般化）。 -/
theorem rlogVol_gauss_w (w : Nat → Nat) (l : Nat) :
    rlogVol w (gaussDiv l) = natToReal (wssq w l) := by
  show qToReal (ratOfInt.map
    ((degN w (gaussDiv l) : Nat) : Int)) = natToReal (wssq w l)
  rw [gaussDiv_deg_w w l]
  rfl

/-! ## M135F-4: 重みの単調性 -/

/-- 有限和の単調性: f ≤ g（点ごと）なら Σf ≤ Σg。 -/
theorem nsum_mono {f g : Nat → Nat} (h : ∀ k, f k ≤ g k) :
    ∀ n, nsum f n ≤ nsum g n := by
  intro n
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => exact Nat.add_le_add ih (h n)

/-- **定理 (M135F-4a): 重み付き平方和の単調性** —
    w ≤ w'（点ごと）なら wssq w l ≤ wssq w' l。 -/
theorem wssq_mono {w w' : Nat → Nat} (h : ∀ k, w k ≤ w' k) (l : Nat) :
    wssq w l ≤ wssq w' l :=
  nsum_mono (fun k => Nat.mul_le_mul (h k) (Nat.le_refl (k * k))) (l + 1)

/-- **定理 (M135F-4b): log-volume の重み単調性**（実数版）—
    w ≤ w' なら vol_w(gaussDiv l) ≤ vol_{w'}(gaussDiv l)（rLe）。 -/
theorem rlogVol_gauss_w_mono {w w' : Nat → Nat} (h : ∀ k, w k ≤ w' k)
    (l : Nat) : rLe (rlogVol w (gaussDiv l)) (rlogVol w' (gaussDiv l)) := by
  rw [rlogVol_gauss_w w l, rlogVol_gauss_w w' l]
  exact natToReal_mono (wssq_mono h l)

/-! ## M135F-5: 単位重みとの整合 -/

/-- **定理 (M135F-5a): 単位重みへの退化** — wssq 1 l = ssq l
    （M133 の nsum_sq への帰着）。 -/
theorem wssq_one (l : Nat) : wssq (fun _ => 1) l = ssq l := by
  have e : (fun k : Nat => 1 * (k * k)) = (fun k : Nat => k * k) :=
    funext fun k => Nat.one_mul (k * k)
  show nsum (fun k : Nat => 1 * (k * k)) (l + 1) = ssq l
  rw [e, nsum_sq l]

/-- **定理 (M135F-5b): M133-3 の再導出** — 単位重みで本層の同定は
    M133 の rlogVol_gauss_eq に一致する。 -/
theorem rlogVol_gauss_w_one (l : Nat) :
    rlogVol (fun _ => 1) (gaussDiv l) = natToReal (ssq l) := by
  rw [rlogVol_gauss_w (fun _ => 1) l, wssq_one l]

/-! ## M135F-6: 体積下界の重み付き版 -/

/-- **定理 (M135F-6a): 重み付き平方和の下界** — w ≥ 1 なら
    ssq l ≤ wssq w l（単調性 + 単位重みへの退化）。 -/
theorem wssq_lower {w : Nat → Nat} (hw : ∀ k, 1 ≤ w k) (l : Nat) :
    ssq l ≤ wssq w l := by
  have h := wssq_mono (w := fun _ => 1) (w' := w) hw l
  rw [wssq_one l] at h
  exact h

/-- **定理 (M135F-6b): 体積下界の重み付き版（本丸の合流）** —
    w ≥ 1 なら l³ ≤ 3·vol_w(gaussDiv l)（rLe）。M132-4 / M133-4b の
    下界が任意の正規化重みに持ち上がる: Nat 側で
    l³ ≤ 3·ssq l ≤ 3·wssq w l と押さえてから natToReal_mono で ℝ へ。 -/
theorem rlogVol_gauss_w_bound {w : Nat → Nat} (hw : ∀ k, 1 ≤ w k)
    (l : Nat) : rLe (natToReal (l * l * l))
      (rmul (natToReal 3) (rlogVol w (gaussDiv l))) := by
  rw [rlogVol_gauss_w w l]
  have hn : l * l * l ≤ 3 * wssq w l :=
    Nat.le_trans (cube_le_ssq l)
      (Nat.mul_le_mul (Nat.le_refl 3) (wssq_lower hw l))
  exact rLe_trans (natToReal_mono hn)
    (rLe_of_realEq (realEq_symm (natToReal_mul 3 (wssq w l))))

/-! ## M135F-7: 総括 -/

/-- **M135F-7a: 総括** — 重み付きガウス因子の log-volume 評価データ。 -/
structure WeightedGaussData where
  /-- 次数の同定: degN w (gaussDiv l) = Σ w(k)·k²。 -/
  deg_eq : ∀ (w : Nat → Nat) (l : Nat), degN w (gaussDiv l) = wssq w l
  /-- log-volume の同定（実数の等式）。 -/
  vol_eq : ∀ (w : Nat → Nat) (l : Nat),
    rlogVol w (gaussDiv l) = natToReal (wssq w l)
  /-- 重みの単調性。 -/
  mono : ∀ {w w' : Nat → Nat}, (∀ k, w k ≤ w' k) → ∀ l,
    rLe (rlogVol w (gaussDiv l)) (rlogVol w' (gaussDiv l))
  /-- 単位重みとの整合（M133-3 の再導出）。 -/
  one_compat : ∀ l, rlogVol (fun _ => 1) (gaussDiv l) = natToReal (ssq l)
  /-- 体積下界（w ≥ 1）。 -/
  bound : ∀ {w : Nat → Nat}, (∀ k, 1 ≤ w k) → ∀ l,
    rLe (natToReal (l * l * l))
      (rmul (natToReal 3) (rlogVol w (gaussDiv l)))

/-- **M135F-7b: witness**。 -/
def weightedGaussData : WeightedGaussData where
  deg_eq := gaussDiv_deg_w
  vol_eq := rlogVol_gauss_w
  mono := rlogVol_gauss_w_mono
  one_compat := rlogVol_gauss_w_one
  bound := rlogVol_gauss_w_bound

/-- **M135F-7c: 存在**。 -/
theorem weightedGauss_exists : Nonempty WeightedGaussData :=
  ⟨weightedGaussData⟩

end IUT
