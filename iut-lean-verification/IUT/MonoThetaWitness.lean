/-
  IUT/MonoThetaWitness.lean — M92（mono-theta witness: 柱E・E7）

  柱E の解析側（M86〜M90: 実テータ級数・関数等式・ガウス簿記）と
  幾何側（M91: Tate 商）を、M11 の mono-theta 骨格（テータ群 =
  離散 Heisenberg 群 thetaGrp と cyclotomic rigidity）に**接合**する。

  数学的本丸: **M90 のガウス指数 tri j = j(j+1)/2 は、テータ群の
  標準切断を成す**。すなわち Φ(j) := (j, j, tri j) は
  (ℕ, +) → thetaGrp の準同型（thetaSection_mul）——Heisenberg 積の
  中心成分 c + c′ + ab′ が押し付ける 2-コサイクル ij を、三角数の
  加法則 tri(i+j) = tri i + tri j + ij がちょうど吸収するからである
  （tri_cocycle はこの恒等式を切断の第 3 成分として「無償」で回収）。
  さらに Φ = (1,1,1) の冪（theta_pow_one）であり、(1,1,1) を通る
  対角切断は**一意**（theta_section_rigid — mono-theta 的剛性）。

  解析側の対応物: T^j(Θ) の u^j 対角係数が q^{tri j} に立ち、その値は
  1（theta_gauss_tri、仮定なしの閉形式）。総括 MonoThetaWitness は
  切断・反復関数等式（M90）・ガウス値・cyclotomic rigidity（M11-5）・
  Tate 降下（M91）を一つの witness に束ねる。

  * M92-1 `tri` / `tri_nat` / `tri_int` — 三角数 j(j+1)/2（分母なし
    の再帰定義と 2·tri = j(j+1) の Nat/Int 橋）
  * M92-2 `theta_gauss_tri` — **仮定なしのガウス値**: T^j(Θ) の
    q^{tri j} u^j 係数 = 1
  * M92-3 `thetaSection` / `section_succ` / `theta_pow_one` /
    `thetaSection_mul` / `tri_cocycle` — **ガウス指数 = Heisenberg
    標準切断（本丸）**
  * M92-4 `theta_section_rigid` — (1,1,1) を通る切断の一意性
  * M92-5 `MonoThetaWitness` / `monoThetaWitness` / `mono_theta_exists`
    — **E7 総括 witness**

  l-捻れ・±構造込みの完全な mono-theta 環境・ガウス積分 vol_q（E8）
  は次層。全て選択公理不使用。
-/
import IUT.ThetaGauss
import IUT.TateQuotient

namespace IUT

/-! ## 三角数（分母なし） -/

/-- **M92-1a: 三角数** tri j = 1 + 2 + … + j（j(j+1)/2 の分母なし
    再帰定義）。 -/
def tri : Nat → Nat
  | 0 => 0
  | j + 1 => tri j + (j + 1)

/-- **M92-1b: 2·tri j = j(j+1)**（Nat 版）。 -/
theorem tri_nat : ∀ j, 2 * tri j = j * (j + 1) := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have ht : tri (j + 1) = tri j + (j + 1) := rfl
    have e : (j + 1) * ((j + 1) + 1) = j * (j + 1) + 2 * (j + 1) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      omega
    omega

/-- **M92-1c: 2·tri j = j(j+1)**（Int 版 — theta_gauss の仮定形）。 -/
theorem tri_int (j : Nat) :
    2 * ((tri j : Nat) : Int) = (j : Int) * ((j : Int) + 1) := by
  have hn := tri_nat j
  have hc : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
  have hb : ((j * (j + 1) : Nat) : Int) = (j : Int) * ((j : Int) + 1) := by
    rw [Int.natCast_mul, hc]
  omega

/-- **定理 (M92-2): 仮定なしのガウス値** — T^j(Θ) の q^{tri j} u^j
    係数 = 1（M90 の theta_gauss の閉形式インスタンス）。 -/
theorem theta_gauss_tri (R : CRing) (j : Nat) :
    tCoeff R j (tri j) ((j : Int)) = R.one :=
  theta_gauss R j (tri j) (tri_int j)

/-! ## ガウス指数 = Heisenberg 標準切断（本丸） -/

/-- **M92-3a: テータ切断** Φ(j) = (j, j, tri j) ∈ thetaGrp。 -/
def thetaSection (j : Nat) : thetaGrp.carrier :=
  ((j : Int), (j : Int), ((tri j : Nat) : Int))

/-- 一段: (1,1,1)·Φ(j) = Φ(j+1)。 -/
theorem section_succ (j : Nat) :
    thetaGrp.mul ((1, 1, 1) : Int × Int × Int) (thetaSection j)
      = thetaSection (j + 1) := by
  show ((1 + (j : Int), 1 + (j : Int),
      1 + ((tri j : Nat) : Int) + 1 * (j : Int)) : Int × Int × Int)
    = (((j + 1 : Nat) : Int), ((j + 1 : Nat) : Int),
      ((tri (j + 1) : Nat) : Int))
  refine triple_ext (by omega) (by omega) ?_
  have ht : tri (j + 1) = tri j + (j + 1) := rfl
  omega

/-- **M92-3b: Φ は (1,1,1) の冪** — Φ(j) = (1,1,1)^j。 -/
theorem theta_pow_one (j : Nat) :
    thetaGrp.pow ((1, 1, 1) : Int × Int × Int) j = thetaSection j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show thetaGrp.mul ((1, 1, 1) : Int × Int × Int)
        (thetaGrp.pow ((1, 1, 1) : Int × Int × Int) j)
      = thetaSection (j + 1)
    rw [ih]
    exact section_succ j

/-- **定理 (M92-3c): テータ切断は準同型（本丸）** —
    Φ(i+j) = Φ(i)·Φ(j)。Heisenberg 積の 2-コサイクル ij を三角数の
    加法則がちょうど吸収する。 -/
theorem thetaSection_mul (i j : Nat) :
    thetaSection (i + j) = thetaGrp.mul (thetaSection i) (thetaSection j) := by
  rw [← theta_pow_one (i + j), ← theta_pow_one i, ← theta_pow_one j,
    Grp.pow_add]

/-- **M92-3d: 2-コサイクル恒等式（無償の系）** —
    tri(i+j) = tri i + tri j + ij（切断の第 3 成分の読み取り）。 -/
theorem tri_cocycle (i j : Nat) :
    ((tri (i + j) : Nat) : Int)
      = ((tri i : Nat) : Int) + ((tri j : Nat) : Int) + (i : Int) * (j : Int) :=
  congrArg (fun t : Int × Int × Int => t.2.2) (thetaSection_mul i j)

/-! ## 切断の一意性（mono-theta 的剛性） -/

/-- **定理 (M92-4): (1,1,1) を通る切断の一意性** — ψ が乗法的で
    ψ(1) = (1,1,1) なら ψ = Φ。ガウス指数 tri j は対角切断の
    **唯一の**中心成分（mono-theta 的剛性の切断版）。 -/
theorem theta_section_rigid (ψ : Nat → thetaGrp.carrier)
    (hmul : ∀ i j, ψ (i + j) = thetaGrp.mul (ψ i) (ψ j))
    (h1 : ψ 1 = ((1, 1, 1) : Int × Int × Int)) :
    ∀ j, ψ j = thetaSection j := by
  have h0 : ψ 0 = thetaGrp.one := by
    have h00 := hmul 0 0
    have hcan : thetaGrp.mul (ψ 0) thetaGrp.one
        = thetaGrp.mul (ψ 0) (ψ 0) := by
      rw [thetaGrp.mul_one]
      exact h00
    exact (thetaGrp.mul_left_cancel hcan).symm
  intro j
  induction j with
  | zero => rw [h0]; rfl
  | succ j ih =>
    have hs := hmul 1 j
    have hidx : 1 + j = j + 1 := by omega
    rw [hidx] at hs
    rw [hs, h1, ih]
    exact section_succ j

/-! ## E7 総括 witness -/

/-- **M92-5a: mono-theta witness** — 柱E の解析側と幾何側を M11 の
    mono-theta 骨格に束ねる総括データ:
    切断（ガウス指数 = Heisenberg 標準切断）・反復関数等式（M90）・
    仮定なしガウス値・cyclotomic rigidity（M11-5）・Tate 降下（M91）。 -/
structure MonoThetaWitness where
  /-- テータ切断 ℕ → thetaGrp。 -/
  sec : Nat → thetaGrp.carrier
  /-- 正規化: 切断は (1,1,1) を通る。 -/
  sec_one : sec 1 = ((1, 1, 1) : Int × Int × Int)
  /-- 切断は準同型（2-コサイクルの吸収）。 -/
  sec_mul : ∀ i j, sec (i + j) = thetaGrp.mul (sec i) (sec j)
  /-- 切断の中心成分はガウス指数 tri。 -/
  sec_gauss : ∀ j, sec j = (((j : Int), (j : Int),
    ((tri j : Nat) : Int)) : Int × Int × Int)
  /-- 解析側: 反復関数等式 T^j(Θ) = (−1)^j Θ（M90）。 -/
  funeq : ∀ (R : CRing) (j m : Nat) (n : Int),
    tCoeff R j m n = negPow R j ((thetaRep R m).coeff n)
  /-- 解析側: T^j(Θ) の q^{tri j} u^j 係数 = 1。 -/
  gauss : ∀ (R : CRing) (j : Nat), tCoeff R j (tri j) ((j : Int)) = R.one
  /-- 群側: cyclotomic rigidity（M11-5）。 -/
  rigid : ∀ (σ : Hom thetaGrp thetaGrp) (z₁ z₂ : Int),
    σ.map (1, 0, 0) = ((1, 0, z₁) : Int × Int × Int) →
    σ.map (0, 1, 0) = ((0, 1, z₂) : Int × Int × Int) →
    σ.map (0, 0, 1) = ((0, 0, 1) : Int × Int × Int)
  /-- 幾何側: q^j-シフトは Tate 商上で恒等（M91）。 -/
  descent : ∀ (G : Grp) (q : G.carrier) (hq : G.Central q)
    (j : Nat) (x : G.carrier),
    (tateOf G q hq).map (G.mul (G.pow q j) x) = (tateOf G q hq).map x

/-- **M92-5b: witness 本体**。 -/
def monoThetaWitness : MonoThetaWitness where
  sec := thetaSection
  sec_one := rfl
  sec_mul := thetaSection_mul
  sec_gauss := fun _ => rfl
  funeq := fun R j m n => tCoeff_eq R j m n
  gauss := theta_gauss_tri
  rigid := mono_theta_cyclotomic_rigidity
  descent := tate_shift_trivial

/-- **定理 (M92-5c): mono-theta witness の存在（E7 見出し）**。 -/
theorem mono_theta_exists : Nonempty MonoThetaWitness :=
  ⟨monoThetaWitness⟩

end IUT
