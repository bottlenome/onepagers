/-
# M133: ガウス因子 — rlogVol と Σj² の同定（C-1 × E-2 × M12 の接合）

第92–93弾で開通した二つの橋（M131F: Frobenioid 次数 → ℝ、
M132: ガウス体積簿記の ℝ 化）の**最終接合**。テータパイロットの
q-次数簿記を担う**ガウス因子** Σ_{j≤l} j²·[p_j] を QDiv として実装し、
その実数値 log-volume が Σj² に一致することを同定する:

  rlogVol 1 (gaussDiv l) = natToReal (ssq l)

これにより M132 の閉形式・体積下界が**実際の因子の log-volume の
言明**になる — [IUTchIV] の log-volume 計算の対象が形式体系内の
データ（QDiv）として存在し、その体積が実数として評価される。

  * M133-1 `gaussDiv` — ガウス因子（重複度 j²、上界 l+1）
  * M133-2 `gaussDiv_deg` — **次数の同定（本丸）**: 単位重みの
    次数 = Σj²（nsum の if 剥がし + 平方和への帰着）
  * M133-3 `rlogVol_gauss_eq` — log-volume = Σj²（実数の等式）
  * M133-4 `rlogVol_gauss_closed` / `rlogVol_gauss_bound` —
    閉形式 6·vol = l(l+1)(2l+1) と **下界 l³ ≤ 3·vol**（rLe）が
    ガウス因子の log-volume の言明として成立
  * M133-5 `rlogVol_gauss_frob` — Frobenius 共変性の instance
  * M133-6 `GaussianDivisorData` — 総括

正直な限定: 重み w は単位重み（全素点 log p = 1 の正規化）。
実際の素点重み（log p_k の実数化）での評価は重み付き ssq の
簿記として次層。

全て選択公理不使用。
-/
import IUT.VolumeReal

namespace IUT

/-! ## M133-1: ガウス因子 -/

/-- **M133-1: ガウス因子** Σ_{j≤l} j²·[p_j]（重複度 j²、上界 l+1）。 -/
def gaussDiv (l : Nat) : QDiv where
  mult := fun j => if j ≤ l then j * j else 0
  bound := l + 1
  vanish := fun k hk => if_neg (by omega)

/-! ## M133-2: 次数の同定 -/

/-- if 剥がし: 範囲内では単位重み × ガウス重複度 = k²。 -/
theorem gauss_nsum (l : Nat) : ∀ n, n ≤ l + 1 →
    nsum (fun k => 1 * (if k ≤ l then k * k else 0)) n
      = nsum (fun k => k * k) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    show nsum (fun k => 1 * (if k ≤ l then k * k else 0)) n
        + 1 * (if n ≤ l then n * n else 0)
      = nsum (fun k => k * k) n + n * n
    rw [ih (by omega), if_pos (by omega : n ≤ l), Nat.one_mul]

/-- 平方和への帰着: nsum k² (l+1) = ssq l。 -/
theorem nsum_sq (l : Nat) :
    nsum (fun k => k * k) (l + 1) = ssq l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    show nsum (fun k => k * k) (l + 1) + (l + 1) * (l + 1)
      = ssq l + (l + 1) * (l + 1)
    rw [ih]

/-- **定理 (M133-2): 次数の同定（本丸）** — 単位重みでの
    ガウス因子の次数 = Σj²。 -/
theorem gaussDiv_deg (l : Nat) :
    degN (fun _ => 1) (gaussDiv l) = ssq l := by
  show nsum (fun k => 1 * (if k ≤ l then k * k else 0)) (l + 1) = ssq l
  rw [gauss_nsum l (l + 1) (Nat.le_refl _), nsum_sq l]

/-! ## M133-3: log-volume の同定 -/

/-- **定理 (M133-3): log-volume = Σj²**（実数の等式そのもの）。 -/
theorem rlogVol_gauss_eq (l : Nat) :
    rlogVol (fun _ => 1) (gaussDiv l) = natToReal (ssq l) := by
  show qToReal (ratOfInt.map
    ((degN (fun _ => 1) (gaussDiv l) : Nat) : Int)) = natToReal (ssq l)
  rw [gaussDiv_deg l]
  rfl

/-! ## M133-4: 閉形式と体積下界（ガウス因子の言明として） -/

/-- **定理 (M133-4a): ガウス因子の log-volume の閉形式** —
    6·vol(gaussDiv l) = l(l+1)(2l+1)。 -/
theorem rlogVol_gauss_closed (l : Nat) :
    realEq (rmul (natToReal 6) (rlogVol (fun _ => 1) (gaussDiv l)))
      (natToReal (l * (l + 1) * (2 * l + 1))) := by
  rw [rlogVol_gauss_eq l]
  exact ssq_closed_real l

/-- **定理 (M133-4b): ガウス因子の体積下界（本丸の合流）** —
    l³ ≤ 3·vol(gaussDiv l)（rLe）。テータパイロットの総 q-次数の
    実数下界が、実際の因子の log-volume の言明として成立。 -/
theorem rlogVol_gauss_bound (l : Nat) :
    rLe (natToReal (l * l * l))
      (rmul (natToReal 3) (rlogVol (fun _ => 1) (gaussDiv l))) := by
  rw [rlogVol_gauss_eq l]
  exact cube_le_ssq_real l

/-! ## M133-5: Frobenius 共変性 -/

/-- **M133-5: Frobenius 共変性の instance** —
    vol(φ_e (gaussDiv l)) = e·vol(gaussDiv l)。 -/
theorem rlogVol_gauss_frob (e l : Nat) :
    realEq (rlogVol (fun _ => 1) (qfrob e (gaussDiv l)))
      (rmul (natToReal e) (rlogVol (fun _ => 1) (gaussDiv l))) :=
  rlogVol_frob (fun _ => 1) e (gaussDiv l)

/-! ## M133-6: 総括 -/

/-- **M133-6a: 総括** — ガウス因子と log-volume の接合データ。 -/
structure GaussianDivisorData where
  /-- 次数の同定。 -/
  deg_eq : ∀ l, degN (fun _ => 1) (gaussDiv l) = ssq l
  /-- log-volume の同定（実数の等式）。 -/
  vol_eq : ∀ l, rlogVol (fun _ => 1) (gaussDiv l) = natToReal (ssq l)
  /-- 閉形式。 -/
  vol_closed : ∀ l,
    realEq (rmul (natToReal 6) (rlogVol (fun _ => 1) (gaussDiv l)))
      (natToReal (l * (l + 1) * (2 * l + 1)))
  /-- 体積下界。 -/
  vol_bound : ∀ l, rLe (natToReal (l * l * l))
    (rmul (natToReal 3) (rlogVol (fun _ => 1) (gaussDiv l)))
  /-- Frobenius 共変性。 -/
  vol_frob : ∀ e l,
    realEq (rlogVol (fun _ => 1) (qfrob e (gaussDiv l)))
      (rmul (natToReal e) (rlogVol (fun _ => 1) (gaussDiv l)))

/-- **M133-6b: witness**。 -/
def gaussianDivisorData : GaussianDivisorData where
  deg_eq := gaussDiv_deg
  vol_eq := rlogVol_gauss_eq
  vol_closed := rlogVol_gauss_closed
  vol_bound := rlogVol_gauss_bound
  vol_frob := rlogVol_gauss_frob

/-- **M133-6c: 存在**。 -/
theorem gaussianDivisor_exists : Nonempty GaussianDivisorData :=
  ⟨gaussianDivisorData⟩

end IUT
