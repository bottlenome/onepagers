/-
  IUT/TowerTorsion.lean — M112F（柱B: M89F の捻れ塔 Λₙ を M109 の塔の
  全レベルへ持ち上げる骨格）

  M89F は基底の環 O = ℤ_p[[X]]/(X^{p−1} + π) 上で捻れ層 Λₙ := ker([πⁿ])
  の一般論（単調性 Λₙ ⊆ Λₙ₊₁・外側剥がし・λ ∈ Λₙ）を確立した。
  M109 はその O を出発点として分岐拡大の塔 O = O₁ ⊆ O₂ ⊆ … を
  towerStep の再帰で全レベル構成し、各レベルの一意化元 λₙ が
  π^{n+1}-捻れ点であること（tower_torsion）を示した。本ファイルは
  両者を統合し、**捻れ述語 IsTowerTorsion を M109 の塔の全レベルへ
  一般化**した上で、基底レベル（towerLevel p 0）では M89F/M83F の
  IsEisTorsion / eisIter と完全に一致することを確認する。

  * M112F-1 `ringF_zero` — f_π(0) = 0（一般環版、eisF_zero の一般化）
  * M112F-2 `ringFIter_succ_comm` — **外側剥がし**（一般環版、
    eisIter_succ_comm の一般化）: [πⁿ⁺¹] = f_π ∘ [πⁿ]
  * M112F-3 `IsTowerTorsion` / `towerTorsion_zero` / `towerTorsion_mono` /
    `towerTorsion_step` / `towerTorsion_hom` — **一般環版の捻れ述語**と
    基本事実: 0 は常に捻れ・単調性 Λₖ ⊆ Λₖ₊₁・一段降下・環準同型との
    両立（φ が π を運べば捻れも運ぶ）
  * M112F-4 `ringF_eisF` / `ringFIter_eisIter` / `towerTorsion_base_iff` —
    **基底互換**: towerLevel p 0 上の ringF/ringFIter は eisRing p 上の
    eisF/eisIter に defeq で一致し、よって IsTowerTorsion は基底レベルで
    IsEisTorsion と同値
  * M112F-5 `tower_lam_torsion` / `tower_lam_torsion_ge` /
    `tower_iota_lam_torsion` — **塔の λ の捻れ**: M109 の tower_torsion の
    述語形での言い換え、単調性による k ≥ n+1 への拡張、ι(λₙ) が
    一段上でも π^{n+1}-捻れであること（**Λₙ ⊆ Λₙ₊₁ の塔版**）
  * M112F-6 `TowerTorsionData` / `towerTorsionData` /
    `towerTorsionData_exists` — 総括レコードと witness・存在定理

  未形式化（正直申告）: 各レベルの Λₖ の非自明性（λₙ ≠ 0 の塔版）・
  Galois/[c]-作用の塔への持ち上げ（M89F-5/6 の O_n 版）は次層。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.EisTowerRings

namespace IUT

/-! ## f_π(0) = 0 と外側剥がし（一般環版） -/

/-- **定理 (M112F-1): f_π(0) = 0**（一般環版、M83F-3a eisF_zero の
    一般化）— π·0 + 0^p = 0。 -/
theorem ringF_zero (p : Nat) (hp : 1 ≤ p) (R : CRing) (piR : R.carrier) :
    ringF p R piR R.zero = R.zero := by
  show R.add (R.mul piR R.zero) (rpow R R.zero p) = R.zero
  rw [CRing.mul_zero R piR, rpow_zero_pos R p hp]
  exact R.zero_add R.zero

/-- **定理 (M112F-2): 外側剥がし**（一般環版、M89F-1
    eisIter_succ_comm の一般化）— [πⁿ⁺¹] = f_π ∘ [πⁿ]。定義は内側剥がし
    ringFIter (n+1) t = ringFIter n (f t) なので、n の帰納で f を
    外側からも剥がせることを示す（基底は f^{∘1} = f の defeq、
    帰納段は IH を f(t) に適用）。 -/
theorem ringFIter_succ_comm (p : Nat) (R : CRing) (piR : R.carrier) :
    ∀ (k : Nat) (t : R.carrier),
    ringFIter p R piR (k + 1) t = ringF p R piR (ringFIter p R piR k t) := by
  intro k
  induction k with
  | zero => intro t; rfl
  | succ k ih =>
    intro t
    show ringFIter p R piR (k + 1) (ringF p R piR t)
      = ringF p R piR (ringFIter p R piR k (ringF p R piR t))
    exact ih (ringF p R piR t)

/-! ## 一般環版の捻れ述語 -/

/-- **M112F-3a: 一般環版の捻れ層の述語** — t ∈ Λₖ ⟺ [πₖ]t = 0
    （IsEisTorsion の一般環版）。 -/
def IsTowerTorsion (p : Nat) (R : CRing) (piR : R.carrier) (k : Nat)
    (t : R.carrier) : Prop :=
  ringFIter p R piR k t = R.zero

/-- **M112F-3b: 0 ∈ Λₖ（∀ k）** — k の帰納 + M112F-1。 -/
theorem towerTorsion_zero (p : Nat) (hp : 1 ≤ p) (R : CRing)
    (piR : R.carrier) : ∀ k, IsTowerTorsion p R piR k R.zero := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show ringFIter p R piR k (ringF p R piR R.zero) = R.zero
    rw [ringF_zero p hp R piR]
    exact ih

/-- **定理 (M112F-3c): 単調性 Λₖ ⊆ Λₖ₊₁**（一般環版、M89F-4b
    eisTorsion_mono の一般化）— 外側剥がし（M112F-2）で
    [πᵏ⁺¹]t = f([πᵏ]t) = f(0) = 0。 -/
theorem towerTorsion_mono (p : Nat) (hp : 1 ≤ p) (R : CRing)
    (piR : R.carrier) {k : Nat} {t : R.carrier}
    (ht : IsTowerTorsion p R piR k t) :
    IsTowerTorsion p R piR (k + 1) t := by
  show ringFIter p R piR (k + 1) t = R.zero
  rw [ringFIter_succ_comm p R piR k t, ht]
  exact ringF_zero p hp R piR

/-- **M112F-3d: 一段降下** — t ∈ Λₖ₊₁ なら f_π(t) ∈ Λₖ（ringFIter の
    内側剥がしの定義そのもの、defeq）。 -/
theorem towerTorsion_step (p : Nat) (R : CRing) (piR : R.carrier)
    {k : Nat} {t : R.carrier} (ht : IsTowerTorsion p R piR (k + 1) t) :
    IsTowerTorsion p R piR k (ringF p R piR t) :=
  ht

/-- **定理 (M112F-3e): 環準同型との両立** — φ が π を運べば捻れも運ぶ
    （ringFIter_hom + RingHom.map_zero）。 -/
theorem towerTorsion_hom (p : Nat) {R S : CRing} (φ : RingHom R S)
    (piR : R.carrier) {k : Nat} {t : R.carrier}
    (ht : IsTowerTorsion p R piR k t) :
    IsTowerTorsion p S (φ.map piR) k (φ.map t) := by
  show ringFIter p S (φ.map piR) k (φ.map t) = S.zero
  rw [← ringFIter_hom p φ piR k t, ht]
  exact RingHom.map_zero φ

/-! ## 基底互換: towerLevel p 0 は eisRing p そのもの -/

/-- **M112F-4a: 基底での f_π は eisF に一致**（定義展開で rfl）。 -/
theorem ringF_eisF (p : Nat) (t : (eisRing p).carrier) :
    ringF p (eisRing p) ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) t
      = eisF p t :=
  rfl

/-- **定理 (M112F-4b): 基底での反復は eisIter に一致**（k の帰納、
    両者とも内側剥がし定義なので各段 M112F-4a + ih）。 -/
theorem ringFIter_eisIter (p : Nat) : ∀ (k : Nat) (t : (eisRing p).carrier),
    ringFIter p (eisRing p) ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
      k t = eisIter p k t := by
  intro k
  induction k with
  | zero => intro t; rfl
  | succ k ih =>
    intro t
    show ringFIter p (eisRing p)
        ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) k
        (ringF p (eisRing p) ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))
          t)
      = eisIter p k (eisF p t)
    rw [ringF_eisF p t]
    exact ih (eisF p t)

/-- **定理 (M112F-4c): 基底互換** — towerLevel p 0 上の捻れ述語は
    M83F/M89F の IsEisTorsion と同値（towerLevel p 0 の ring/pi は
    定義から eisRing p / (eisOf p).map … に defeq）。 -/
theorem towerTorsion_base_iff (p : Nat) (k : Nat) (t : (eisRing p).carrier) :
    IsTowerTorsion p (towerLevel p 0).ring (towerLevel p 0).pi k t
      ↔ IsEisTorsion p k t := by
  show ringFIter p (eisRing p)
      ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) k t
      = (eisRing p).zero
    ↔ eisIter p k t = (eisRing p).zero
  rw [ringFIter_eisIter p k t]

/-! ## 塔の λ の捻れ -/

/-- **M112F-5a: 塔の λ の捻れ**（= M109 の tower_torsion そのもの、
    述語形での言い換え）。 -/
theorem tower_lam_torsion (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    IsTowerTorsion p (towerLevel p n).ring (towerLevel p n).pi (n + 1)
      (towerLevel p n).lam :=
  tower_torsion p hp n

/-- **定理 (M112F-5b): 塔の λ の捻れは k ≥ n+1 全体で成立**
    （towerTorsion_mono を k − (n+1) 回反復）。 -/
theorem tower_lam_torsion_ge (p : Nat) (hp : 2 ≤ p) (n k : Nat)
    (hk : n + 1 ≤ k) :
    IsTowerTorsion p (towerLevel p n).ring (towerLevel p n).pi k
      (towerLevel p n).lam := by
  obtain ⟨d, hd⟩ : ∃ d, k = (n + 1) + d := ⟨k - (n + 1), by omega⟩
  subst hd
  clear hk
  induction d with
  | zero => exact tower_lam_torsion p hp n
  | succ d ih =>
    exact towerTorsion_mono p (by omega) (towerLevel p n).ring
      (towerLevel p n).pi ih

/-- **定理 (M112F-5c): ι(λₙ) は一段上でも π^{n+1}-捻れ** —
    **Λₙ ⊆ Λₙ₊₁ の塔版**（towerTorsion_hom を towerHom に適用、
    (towerLevel p (n+1)).pi = (towerHom p n).map (towerLevel p n).pi が
    定義から defeq であることを利用）。 -/
theorem tower_iota_lam_torsion (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    IsTowerTorsion p (towerLevel p (n + 1)).ring (towerLevel p (n + 1)).pi
      (n + 1) ((towerHom p n).map (towerLevel p n).lam) :=
  towerTorsion_hom p (towerHom p n) (towerLevel p n).pi
    (tower_lam_torsion p hp n)

/-! ## 総括レコード -/

/-- **M112F-6a: 総括** — 一般環版の捻れ塔骨格を M109 の塔の全レベルへ
    持ち上げたデータ。 -/
structure TowerTorsionData (p : Nat) (hp : 2 ≤ p) where
  /-- 塔の λ の捻れ（M112F-5a）。 -/
  lam_torsion : ∀ n, IsTowerTorsion p (towerLevel p n).ring
    (towerLevel p n).pi (n + 1) (towerLevel p n).lam
  /-- 単調性 Λₖ ⊆ Λₖ₊₁（一般環・一般レベル、M112F-3c）。 -/
  mono : ∀ (R : CRing) (piR : R.carrier) (k : Nat) (t : R.carrier),
    IsTowerTorsion p R piR k t → IsTowerTorsion p R piR (k + 1) t
  /-- ι(λₙ) の一段上での捻れ（M112F-5c）。 -/
  iota_torsion : ∀ n, IsTowerTorsion p (towerLevel p (n + 1)).ring
    (towerLevel p (n + 1)).pi (n + 1) ((towerHom p n).map (towerLevel p n).lam)
  /-- 基底互換（M112F-4c）。 -/
  base_compat : ∀ (k : Nat) (t : (eisRing p).carrier),
    IsTowerTorsion p (towerLevel p 0).ring (towerLevel p 0).pi k t
      ↔ IsEisTorsion p k t

/-- **M112F-6b: witness**。 -/
def towerTorsionData (p : Nat) (hp : 2 ≤ p) : TowerTorsionData p hp where
  lam_torsion := tower_lam_torsion p hp
  mono := fun R piR _ _ ht => towerTorsion_mono p (by omega) R piR ht
  iota_torsion := tower_iota_lam_torsion p hp
  base_compat := towerTorsion_base_iff p

/-- **M112F-6c: 存在**。 -/
theorem towerTorsionData_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (TowerTorsionData p hp) :=
  ⟨towerTorsionData p hp⟩

end IUT
