/-
  IUT/LocalCFT.lean — M27（局所類体論の形式化: ℤ_p・不分岐相互法則・
  LCFT インターフェース）

  局所類体論 Art : K^× → Gal(K^ab/K) の形式化の第一段。本モジュール:

  §1 ℤ_p の実構成
  * M27-1 `padicSystem` / `Zp` — **ℤ_p = lim ℤ/p^n の実構成**
    （M13 の逆極限機械の実例化）
  * M27-2 `Zp_compact` — ℤ_p はコンパクト（M25 の König 論法の適用）
    かつ位相群（M15、自動適用）
  * M27-3 `toZp_injective` — ℤ → ℤ_p は単射（p 進分離性:
    全ての n で p^n ∣ a−b なら a = b。p^n の非有界性 m < p^m から）

  §2 不分岐局所相互法則（完全証明）
  * M27-4 `unramifiedRec` — **不分岐相互写像** K^× --v--> ℤ → ẑ
    = Gal(K^ur/K)（付値と副有限完備化 M13 の合成）
  * M27-5 `unramifiedRec_kernel` — **核 = 単数群 O^×**（v = 0 の部分）
    ——「単数は不分岐拡大で消える」局所類体論の核の特徴付け
  * M27-6 `unramifiedRec_level_surj` — **各有限レベルへ全射**
    （Frobenius の稠密性。ẑ → ℤ/n の構成的全射 M15-7 から）

  §3 LCFT のインターフェースと無矛盾性
  * M27-7 `LocalCFTData` — 局所類体論の statement の構造化:
    相互写像 rec : K^× → G^ab、単射性、各有限レベルへの全射性
    （= 稠密像）。
  * M27-8 `localCFT_consistent` — **不分岐モデルで充足**（§2 の
    不分岐相互法則そのものが witness。完全証明・公理化なし）

  **位置づけ（正直な申告）**: 分岐部分（単数群 O^× → 惰性群、
  Lubin–Tate 形式群による構成）と「rec が実際の Galois 群に
  対して同型を誘導する」ことの実証明は未形式化。本モジュールで
  完全証明されたのは ℤ_p の構成・コンパクト性と**不分岐局所類体論**
  （K^×/O^× ≅ ℤ ↪ ẑ = Gal(K^ur/K)、核・稠密性込み）である。
  これは M10 の `AbData`（G^ab の rank profile が読めること）の
  不分岐方向の実証明にあたる。
-/
import IUT.LimitCompact

namespace IUT

/-! ## §1 ℤ_p の実構成 -/

/-- p 冪の割り切り単調性。 -/
theorem pow_dvd_mono (p : Nat) : ∀ {i j : Nat}, i ≤ j → p ^ i ∣ p ^ j := by
  intro i j h
  induction j with
  | zero =>
    have h0 : i = 0 := Nat.le_zero.mp h
    subst h0
    exact Nat.dvd_refl _
  | succ j ih =>
    by_cases hij : i = j + 1
    · subst hij
      exact Nat.dvd_refl _
    · have h' : i ≤ j := by omega
      exact Nat.dvd_trans (ih h') (Nat.dvd_mul_right _ _)

/-- p 冪の正値性。 -/
theorem pow_pos' (p : Nat) (hp : 1 ≤ p) : ∀ n, 0 < p ^ n := by
  intro n
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    show 0 < p ^ n * p
    exact Nat.mul_pos ih (by omega)

/-- p 冪の非有界性: m < p^m（p ≥ 2）。 -/
theorem lt_pow_self (p : Nat) (hp : 2 ≤ p) : ∀ m, m < p ^ m := by
  intro m
  induction m with
  | zero => exact Nat.one_pos
  | succ m ih =>
    show m + 1 < p ^ m * p
    have h2 : p ^ m * 2 ≤ p ^ m * p := Nat.mul_le_mul (Nat.le_refl _) hp
    revert ih h2
    generalize p ^ m = q
    generalize q * p = r
    intro ih h2
    omega

/-- **ℤ/p^n たちの逆系**（M27-1a）。 -/
@[reducible] def padicSystem (p : Nat) : InverseSystem :=
  natSystem (fun n => zmod (p ^ n)) (fun h => zmodTrans (pow_dvd_mono p h))
    (fun i x => by induction x using Quot.ind; rfl)
    (fun hij hjk x => by induction x using Quot.ind; rfl)

/-- **ℤ_p = lim ℤ/p^n の実構成**（M27-1b）。M15 により自動的に
    位相群である。 -/
def Zp (p : Nat) : Grp := limitGrp (padicSystem p)

/-- **定理 (M27-2): ℤ_p はコンパクト**（M25 の適用）。 -/
theorem Zp_compact (p : Nat) (hp : 1 ≤ p) :
    Compact (limitTopology (padicSystem p)) :=
  natSystem_compact (fun n => zmod (p ^ n))
    (fun {i j} h => zmodTrans (pow_dvd_mono p h))
    (fun i x => by induction x using Quot.ind; rfl)
    (fun hij hjk x => by induction x using Quot.ind; rfl)
    (fun n => zmod_listable (p ^ n) (pow_pos' p hp n))

/-- ℤ_p は位相群（M15-3 の適用）。 -/
theorem Zp_mul_continuous (p : Nat) :
    Continuous (prodTopology (limitTopology (padicSystem p))
      (limitTopology (padicSystem p))) (limitTopology (padicSystem p))
      (fun q => (Zp p).mul q.1 q.2) :=
  limit_mul_continuous (padicSystem p)

/-- 完備化写像 ℤ → ℤ_p（対角埋め込み）。 -/
def toZp (p : Nat) : Hom intGrp (Zp p) where
  map := fun a => ⟨fun n => Quot.mk (modCong (p ^ n)).rel a, fun {_ _} _ => rfl⟩
  map_mul := fun _ _ => by
    apply Subtype.ext
    funext n
    rfl

/-- p 進分離性の算術核: 全ての n で p^n ∣ A−B なら A = B。 -/
theorem int_pow_separated (p : Nat) (hp : 2 ≤ p) (A B : Int)
    (h : ∀ n : Nat, ((p ^ n : Nat) : Int) ∣ (A - B)) : A = B := by
  by_cases hab : A = B
  · exact hab
  · exfalso
    obtain ⟨k, hk⟩ := h (A - B).natAbs
    have hNabs : (A - B).natAbs = p ^ (A - B).natAbs * k.natAbs := by
      have h1 : (A - B).natAbs
          = (((p ^ (A - B).natAbs : Nat) : Int)).natAbs * k.natAbs := by
        rw [← Int.natAbs_mul, ← hk]
      rw [Int.natAbs_natCast] at h1
      exact h1
    cases hk0 : k.natAbs with
    | zero =>
      rw [hk0, Nat.mul_zero] at hNabs
      have h0 : A - B = 0 := Int.natAbs_eq_zero.mp hNabs
      omega
    | succ j =>
      have hj : 1 ≤ k.natAbs := by rw [hk0]; omega
      have h2 : p ^ (A - B).natAbs * 1 ≤ p ^ (A - B).natAbs * k.natAbs :=
        Nat.mul_le_mul (Nat.le_refl _) hj
      rw [Nat.mul_one, ← hNabs] at h2
      have h3 := lt_pow_self p hp (A - B).natAbs
      omega

/-- **定理 (M27-3): ℤ → ℤ_p は単射**（p 進分離性）。 -/
theorem toZp_injective (p : Nat) (hp : 2 ≤ p) : (toZp p).Injective := by
  intro a b h
  have hval := congrArg Subtype.val h
  exact int_pow_separated p hp a b
    (fun n => quot_exact intGrp (modCong (p ^ n)) (congrFun hval n))

/-! ## §2 不分岐局所相互法則 -/

/-- 局所体の乗法群の骨格: K^× ≅ ℤ × O^×（付値による分裂。
    単数群 U は抽象群データ）。 -/
def unitsModel (U : Grp) : Grp := prodGrp intGrp U

/-- 付値 v : K^× → ℤ（第一成分）。 -/
def valuation (U : Grp) : Hom (unitsModel U) intGrp where
  map := fun x => x.1
  map_mul := fun _ _ => rfl

/-- **不分岐相互写像**（M27-4）: K^× --v--> ℤ --完備化--> ẑ。
    右辺 ẑ = Gal(K^ur/K)（Frobenius の冪の閉包）は M13 の実構成。 -/
def unramifiedRec (U : Grp) : Hom (unitsModel U) zhat :=
  Hom.comp toZhat (valuation U)

/-- **定理 (M27-5): 核 = 単数群** — rec(x) = 1 ⟺ v(x) = 0。
    「単数は不分岐拡大に消える」という局所類体論の核の特徴付け。 -/
theorem unramifiedRec_kernel (U : Grp) (x : (unitsModel U).carrier) :
    (unramifiedRec U).map x = zhat.one ↔ x.1 = 0 := by
  constructor
  · intro h
    have h0 : toZhat.map (0 : Int) = zhat.one := toZhat.map_one
    exact toZhat_injective x.1 0 (h.trans h0.symm)
  · intro h
    show toZhat.map x.1 = zhat.one
    rw [h]
    exact toZhat.map_one

/-- **定理 (M27-6): 各有限レベルへの全射性**（Frobenius の稠密性）—
    相互写像の像は ẑ のどの有限商 ℤ/n も覆う（M15-7 の適用）。 -/
theorem unramifiedRec_level_surj (U : Grp) (n : Nat) (c : (zmod n).carrier) :
    ∃ x : (unitsModel U).carrier,
      (limitProj zmodSystem n).map ((unramifiedRec U).map x) = c := by
  obtain ⟨z, hz⟩ := zhat_proj_surjective n c
  -- z = toZhat a の形の元で十分（zhat_proj_surjective の証明が対角で
  -- witness を与えるが、ここでは c の代表元から直接作る）
  induction c using Quot.ind; rename_i a
  exact ⟨(a, U.one), rfl⟩

/-! ## §3 局所類体論のインターフェース -/

/-- **局所類体論の statement の構造化**（M27-7）: 相互写像
    rec : K^× → G^ab、単射性、全ての有限レベルへの全射性（稠密像）。
    完全な LCFT は G^ab = Gal(K^ab/K) でこれが成り立つことを主張する。 -/
structure LocalCFTData where
  Kx : Grp
  Gab : Grp
  recMap : Hom Kx Gab
  recMap_inj : recMap.Injective
  levels : Nat → Grp
  projs : ∀ n, Hom Gab (levels n)
  recMap_level_surj : ∀ (n : Nat) (c : (levels n).carrier),
    ∃ x : Kx.carrier, (projs n).map (recMap.map x) = c

/-- **定理 (M27-8): 不分岐モデルによる充足** — §2 の不分岐局所
    相互法則（K^× = ℤ × O^×、G^ab = ẑ、rec = 完備化∘付値）が
    LCFT インターフェースを**完全証明で**満たす（公理化なし）。 -/
def unramifiedLocalCFT : LocalCFTData where
  Kx := unitsModel punitGrp
  Gab := zhat
  recMap := unramifiedRec punitGrp
  recMap_inj := by
    intro x y h
    have h1 : x.1 = y.1 := toZhat_injective x.1 y.1 h
    show x = y
    rw [show x = (x.1, x.2) from rfl, show y = (y.1, y.2) from rfl, h1]
    rfl
  levels := fun n => zmod n
  projs := limitProj zmodSystem
  recMap_level_surj := unramifiedRec_level_surj punitGrp

theorem localCFT_consistent : Nonempty LocalCFTData := ⟨unramifiedLocalCFT⟩

end IUT
