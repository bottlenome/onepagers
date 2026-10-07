/-
  IUT/ThetaPM.lean — M116F: テータ群の ±-構造 — インバージョン自己同型 ι と中心捻れ

  [EtTh] の mono-theta 環境は ±-構造（u ↦ u⁻¹ 対称性）を持つ。その群論核を
  離散 Heisenberg 骨格（thetaGrp、M11）と l-捻れ骨格（thetaGrpMod、M98F）の
  上に実装する。ι(a,b,c) = (−a,−b,c) は Heisenberg 積の自己準同型であり
  （2-コサイクル ab' は符号反転で不変: (−a)(−b') = ab'）、以下を検証する。

  * M116F-1 `thetaNeg` — インバージョン自己同型 ι : thetaGrp → thetaGrp
    （準同型性は成分計算で完全証明）
  * M116F-2 `thetaNeg_involutive` / `thetaNeg_center` — ι² = id、かつ
    **ι は中心（シクロトーム）を固定する**。cyclotomic rigidity（M11-5）と
    両立する形: ±-作用はシクロトームに符号を落とさない
  * M116F-3 `thetaNeg_section_mul` / `thetaNeg_section_inv` —
    **±-切断相互作用（本丸1)**: ι(Φ(j))·Φ(j) = (0,0,j) = 中心の j 乗。
    ±-対がガウス指数簿記 tri j を線形化する（2·tri j − j² = j）
  * M116F-4 `thetaRelMod_neg` / `thetaNegMod` / `thetaNegMod_involutive` /
    `thetaNegMod_red` — ι の mod-l 降下（Quot.lift、射影と可換）
  * M116F-5 `thetaNegMod_section` / `thetaNeg_label_center` —
    mod-l ±-切断相互作用と **l⋇ ラベリングへの接続（本丸2)**:
    ι(Φ(j)) ≡ Φ(l−j)·(0,0,z) (mod l)、中心捻れ z = tri j − tri(l−j)。
    テータラベル j ↔ l−j の ±-同一視は**中心捻れ付きで**成立する
    （z なしでは 2·(tri j − tri(l−j)) = l(2j−l−1) + 2j より一般に不成立）
  * M116F-6 `ThetaPMData` / `thetaPMData` / `thetaPM_exists` — 総括 witness

  意義: 柱E E-1（issue #39）の第一切片。[EtTh] の ±-構造 = u ↦ u⁻¹ 対称性の
  群論核。ι は中心（シクロトーム）を固定し、±-対 ι(Φ(j))·Φ(j) = 中心^j が
  ガウス指数を線形化、ラベル j ↔ l−j は中心捻れ付きで同一視される。

  **形式化の範囲（正直な申告）**: μ_l ↔ O^× 同一視、tempered π₁ の商としての
  実現、エタールテータ関数の関数等式の Heisenberg リフトは次層。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.ThetaGroupMod

namespace IUT

/-! ## M116F-1: インバージョン自己同型 ι -/

/-- **M116F-1: インバージョン自己同型** ι(a,b,c) = (−a,−b,c)。
    [EtTh] の ±-構造（u ↦ u⁻¹）の Heisenberg 骨格上の実現。
    準同型性: 2-コサイクル ab' は符号反転で不変（(−a)(−b') = ab'）。 -/
def thetaNeg : Hom thetaGrp thetaGrp where
  map := fun x => (-x.1, -x.2.1, x.2.2)
  map_mul := by
    intro x y
    obtain ⟨a, b, c⟩ := x
    obtain ⟨a', b', c'⟩ := y
    show (-(a + a'), -(b + b'), c + c' + a * b')
      = (-a + -a', -b + -b', c + c' + -a * -b')
    refine triple_ext (by omega) (by omega) ?_
    rw [Int.neg_mul_neg]

/-! ## M116F-2: ι は対合であり中心を固定する -/

/-- **定理 (M116F-2a): ι は対合** — ι² = id。±-構造は位数 2。 -/
theorem thetaNeg_involutive (x : thetaGrp.carrier) :
    thetaNeg.map (thetaNeg.map x) = x := by
  obtain ⟨a, b, c⟩ := x
  show (-(-a), -(-b), c) = (a, b, c)
  refine triple_ext (by omega) (by omega) rfl

/-- **定理 (M116F-2b): ι は中心（シクロトーム）を固定する** —
    ι(0,0,z) = (0,0,z)。±-作用はシクロトームに符号を落とさず、
    cyclotomic rigidity（M11-5: 中心生成元の厳密固定）と両立する。 -/
theorem thetaNeg_center (z : Int) :
    thetaNeg.map (0, 0, z) = ((0, 0, z) : Int × Int × Int) := by
  show (-(0 : Int), -(0 : Int), z) = ((0 : Int), (0 : Int), z)
  refine triple_ext (by omega) (by omega) rfl

/-! ## M116F-3: ±-切断相互作用（本丸1） -/

/-- **定理 (M116F-3a): ±-対は中心の j 乗（本丸1）** —
    ι(Φ(j))·Φ(j) = (0,0,j)。ガウス指数簿記 tri j（2 次）が ±-対では
    中心成分 2·tri j − j² = j（1 次）に**線形化**される。
    [EtTh] の ±-同期がガウス指数簿記を制御する機構の離散核。 -/
theorem thetaNeg_section_mul (j : Nat) :
    thetaGrp.mul (thetaNeg.map (thetaSection j)) (thetaSection j)
      = ((0, 0, (j : Int)) : Int × Int × Int) := by
  show (-(j : Int) + (j : Int), -(j : Int) + (j : Int),
      ((tri j : Nat) : Int) + ((tri j : Nat) : Int) + -(j : Int) * (j : Int))
    = ((0 : Int), (0 : Int), (j : Int))
  refine triple_ext (by omega) (by omega) ?_
  have h := tri_int j
  rw [Int.mul_add, Int.mul_one] at h
  rw [Int.neg_mul]
  revert h
  generalize (j : Int) * (j : Int) = P
  intro h
  omega

/-- **定理 (M116F-3b): ι(Φ(j)) = Φ(j)⁻¹·(0,0,j)** — インバージョンした
    切断は逆元と中心の j 乗の積。±-構造が「逆元 + 中心補正」として
    切断に作用することの成分計算による直接証明。 -/
theorem thetaNeg_section_inv (j : Nat) :
    thetaNeg.map (thetaSection j)
      = thetaGrp.mul (thetaGrp.inv (thetaSection j))
          ((0, 0, (j : Int)) : Int × Int × Int) := by
  show (-(j : Int), -(j : Int), ((tri j : Nat) : Int))
    = (-(j : Int) + 0, -(j : Int) + 0,
      -((tri j : Nat) : Int) + (j : Int) * (j : Int) + (j : Int) + -(j : Int) * 0)
  refine triple_ext (by omega) (by omega) ?_
  have h := tri_int j
  rw [Int.mul_add, Int.mul_one] at h
  rw [Int.mul_zero]
  revert h
  generalize (j : Int) * (j : Int) = P
  intro h
  omega

/-! ## M116F-4: ι の mod-l 降下 -/

/-- **定理 (M116F-4a): l-合同関係は ι と両立する** —
    成分ごとの整除の witness を符号反転するだけでよい。 -/
theorem thetaRelMod_neg (l : Nat) {x y : thetaGrp.carrier}
    (h : thetaRelMod l x y) :
    thetaRelMod l (thetaNeg.map x) (thetaNeg.map y) := by
  obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩, ⟨k3, hk3⟩⟩ := h
  refine ⟨⟨-k1, ?_⟩, ⟨-k2, ?_⟩, ⟨k3, ?_⟩⟩
  · show -x.1 - -y.1 = (l : Int) * -k1
    rw [Int.mul_neg]
    omega
  · show -x.2.1 - -y.2.1 = (l : Int) * -k2
    rw [Int.mul_neg]
    omega
  · show x.2.2 - y.2.2 = (l : Int) * k3
    exact hk3

/-- **M116F-4b: mod-l インバージョン** ι_l : thetaGrpMod l → thetaGrpMod l
    （Quot.lift による降下、thetaGrpMod の構成流儀を踏襲）。 -/
def thetaNegMod (l : Nat) : Hom (thetaGrpMod l) (thetaGrpMod l) where
  map := Quot.lift
    (fun x => Quot.mk (thetaRelMod l) (thetaNeg.map x))
    (fun _ _ hxy => Quot.sound (thetaRelMod_neg l hxy))
  map_mul := by
    intro a b
    induction a using Quot.ind
    rename_i x
    induction b using Quot.ind
    rename_i y
    exact congrArg (Quot.mk (thetaRelMod l)) (thetaNeg.map_mul x y)

/-- **定理 (M116F-4c): ι_l は対合** — mod-l でも ±-構造は位数 2。 -/
theorem thetaNegMod_involutive (l : Nat) (a : (thetaGrpMod l).carrier) :
    (thetaNegMod l).map ((thetaNegMod l).map a) = a := by
  induction a using Quot.ind
  rename_i x
  exact congrArg (Quot.mk (thetaRelMod l)) (thetaNeg_involutive x)

/-- **定理 (M116F-4d): ι_l は射影と可換** — ι_l ∘ red = red ∘ ι
    （降下の整合性、定義から rfl）。 -/
theorem thetaNegMod_red (l : Nat) (x : thetaGrp.carrier) :
    (thetaNegMod l).map ((thetaRed l).map x) = (thetaRed l).map (thetaNeg.map x) :=
  rfl

/-! ## M116F-5: mod-l ±-切断相互作用と l⋇ ラベリングへの接続（本丸2） -/

/-- **定理 (M116F-5a): mod-l ±-対は商中心の j 乗** —
    ι_l(Φ_l(j))·Φ_l(j) = red(0,0,j)（M116F-3a の商への降下）。 -/
theorem thetaNegMod_section (l : Nat) (j : Nat) :
    (thetaGrpMod l).mul ((thetaNegMod l).map (thetaSectionMod l j))
        (thetaSectionMod l j)
      = (thetaRed l).map (0, 0, (j : Int)) :=
  congrArg (Quot.mk (thetaRelMod l)) (thetaNeg_section_mul j)

/-- **定理 (M116F-5b): ラベル j ↔ l−j の ±-同一視は中心捻れ付きで成立
    （本丸2）** — ι(Φ(j)) ≡ Φ(l−j)·(0,0,z) (mod l)、中心捻れの閉形式は
    z = tri j − tri(l−j)。第 1・2 成分は −j ≡ l−j (mod l)（witness −1）、
    第 3 成分は z がズレを**厳密に**吸収する（witness 0）。
    z なしでは 2·(tri j − tri(l−j)) = l·(2j−l−1) + 2j より第 3 成分の
    l-整除は一般に不成立: **中心のズレ込みこそが [EtTh] の ±-構造の要**。 -/
theorem thetaNeg_label_center (l j : Nat) (hj : j ≤ l) :
    ∃ z : Int, thetaRelMod l (thetaNeg.map (thetaSection j))
      (thetaGrp.mul (thetaSection (l - j)) (0, 0, z)) := by
  refine ⟨((tri j : Nat) : Int) - ((tri (l - j) : Nat) : Int),
    ⟨-1, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩⟩
  · show -(j : Int) - (((l - j : Nat) : Int) + 0) = (l : Int) * (-1)
    omega
  · show -(j : Int) - (((l - j : Nat) : Int) + 0) = (l : Int) * (-1)
    omega
  · show ((tri j : Nat) : Int)
        - (((tri (l - j) : Nat) : Int)
            + (((tri j : Nat) : Int) - ((tri (l - j) : Nat) : Int))
            + ((l - j : Nat) : Int) * 0)
      = (l : Int) * 0
    omega

/-! ## M116F-6: 総括 witness -/

/-- **M116F-6a: ±-構造データ** — インバージョン ι とその全性質の一括束ね:
    対合性・中心固定・±-切断相互作用・mod-l 降下・中心捻れ付きラベル同一視。 -/
structure ThetaPMData (l : Nat) where
  /-- インバージョン自己同型 ι。 -/
  neg : Hom thetaGrp thetaGrp
  /-- ι は対合。 -/
  neg_involutive : ∀ x : thetaGrp.carrier, neg.map (neg.map x) = x
  /-- ι は中心（シクロトーム）を固定する。 -/
  neg_center : ∀ z : Int, neg.map (0, 0, z) = ((0, 0, z) : Int × Int × Int)
  /-- ±-対は中心の j 乗: ι(Φ(j))·Φ(j) = (0,0,j)。 -/
  neg_section_mul : ∀ j : Nat,
    thetaGrp.mul (neg.map (thetaSection j)) (thetaSection j)
      = ((0, 0, (j : Int)) : Int × Int × Int)
  /-- mod-l インバージョン ι_l。 -/
  negMod : Hom (thetaGrpMod l) (thetaGrpMod l)
  /-- ι_l は対合。 -/
  negMod_involutive : ∀ a : (thetaGrpMod l).carrier,
    negMod.map (negMod.map a) = a
  /-- ι_l は射影と可換: ι_l ∘ red = red ∘ ι。 -/
  negMod_red : ∀ x : thetaGrp.carrier,
    negMod.map ((thetaRed l).map x) = (thetaRed l).map (neg.map x)
  /-- mod-l ±-対は商中心の j 乗。 -/
  negMod_section : ∀ j : Nat,
    (thetaGrpMod l).mul (negMod.map (thetaSectionMod l j)) (thetaSectionMod l j)
      = (thetaRed l).map (0, 0, (j : Int))
  /-- ラベル j ↔ l−j の ±-同一視（中心捻れ付き）。 -/
  label_center : ∀ j : Nat, j ≤ l →
    ∃ z : Int, thetaRelMod l (neg.map (thetaSection j))
      (thetaGrp.mul (thetaSection (l - j)) (0, 0, z))

/-- **M116F-6b: witness 本体**。 -/
def thetaPMData (l : Nat) : ThetaPMData l where
  neg := thetaNeg
  neg_involutive := thetaNeg_involutive
  neg_center := thetaNeg_center
  neg_section_mul := thetaNeg_section_mul
  negMod := thetaNegMod l
  negMod_involutive := thetaNegMod_involutive l
  negMod_red := thetaNegMod_red l
  negMod_section := thetaNegMod_section l
  label_center := fun j hj => thetaNeg_label_center l j hj

/-- **定理 (M116F-6c): ±-構造 witness の存在（M116F 見出し）**。 -/
theorem thetaPM_exists (l : Nat) : Nonempty (ThetaPMData l) :=
  ⟨thetaPMData l⟩

end IUT
