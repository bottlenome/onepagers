/-
  IUT/FuneqLift.lean — M137F: 関数等式の Heisenberg 辞書 — T^j ↔ Φ(j) の対応

  issue #39 E-1 の残件「エタールテータの関数等式が Heisenberg 積を
  リフトする事実」の辞書化。解析側 T^j（M89/M90 の反復関数等式
  T^j(Θ) = (−1)^j Θ と、その代入簿記が生むガウス指数 q^{tri j}）と
  群側 Φ(j) = (j, j, tri j)（M92 の標準切断）が**同じガウス指数簿記**
  を持つ: 両者は中心成分 = tri j で同期し（section_gauss_component /
  funeq_gauss_descent — u^j 対角での q-次数降下量 m − i = tri j が
  Φ(j) の第 3 成分と一致）、乗法性は Heisenberg 積の 2-コサイクル ij
  を三角数加法則 tri(i+j) = tri i + tri j + ij がちょうど吸収
  （Heisenberg 性の源泉、gauss_additive_with_cocycle）、±-対は
  中心^j（M116F、dict_pm）。[EtTh] の mono-theta 環境の解析/群対応の
  離散核である。

  * M137F-1 `section_gauss_component` — 切断の第 3 成分 = ガウス指数
    tri j（定義から rfl）
  * M137F-2 `funeq_gauss_descent` / `FuneqDict` / `funeqDict` —
    **辞書（本丸）**: T^j の q-次数降下 = Φ(j) の中心成分。
    解析側（theta_gauss_tri・tCoeff_eq・tCoeff_shift）と群側
    （thetaSection_mul・thetaNeg_section_mul）を j ごとに一束に
  * M137F-3 `dict_multiplicative` / `gauss_additive_with_cocycle` —
    乗法性の両立: Φ(i)Φ(j) = Φ(i+j) と、その中心成分読み
    tri(i+j) = tri i + tri j + ij（Nat 版）
  * M137F-4 `dict_pm` — ±-対 ι(Φ(j))·Φ(j) = (0,0,j)（M116F の再輸出）
  * M137F-5 `FuneqLiftData` / `funeqLiftData` / `funeqLift_exists` —
    総括 witness（辞書・乗法性・コサイクル・±・反転 J = T（M98））

  本モジュールは**接続辞書**であり、新規の重い計算は含まない — 既存
  定理（M90: tCoeff_eq / tCoeff_shift / theta_gauss、M92: thetaSection_mul /
  theta_gauss_tri / tri_cocycle、M116F: thetaNeg_section_mul、M98:
  theta_refl_eq_funeq）の型を揃えて再輸出・合成する。

  **形式化の範囲（正直な申告）**: リフトの圏論的定式化（作用素環の
  表現としての同型）は将来層。全て選択公理不使用。サブエージェント
  並行部品。
-/
import IUT.MonoThetaWitness
import IUT.ThetaPM
import IUT.ThetaReflection

namespace IUT

/-! ## M137F-1: 切断の第 3 成分 = ガウス指数 -/

/-- **定理 (M137F-1): 切断の中心成分はガウス指数** —
    Φ(j) = (j, j, tri j) の第 3 成分は三角数 tri j。thetaSection の
    定義（M92-3a）からの直読み。解析側の q-指数簿記と群側の中心成分を
    同一視する辞書の「左辺」。 -/
theorem section_gauss_component (j : Nat) :
    (thetaSection j).2.2 = ((tri j : Nat) : Int) := rfl

/-! ## M137F-2: 辞書（本丸） — T^j の q-次数降下 = Φ(j) の中心成分 -/

/-- **定理 (M137F-2a): ガウス降下の閉形式** — u^j 対角（n = j）で
    T^j(Θ) の q-次数 m = tri j の係数は Θ の q-次数 0 の係数へ降下する:
    降下量 m − i = tri j − 0 = tri j はちょうど Φ(j) の中心成分
    （section_gauss_component）。M90 の tCoeff_shift（代入の閉形式
    2m = 2i + 2jn − j(j−1)）の i = 0, n = j インスタンス。 -/
theorem funeq_gauss_descent (R : CRing) (j : Nat) :
    tCoeff R j (tri j) ((j : Int))
      = (thetaRep R 0).coeff ((j : Int) - (j : Int)) := by
  refine tCoeff_shift R j (tri j) 0 ((j : Int)) ?_
  have ht := tri_int j
  rw [Int.mul_add, Int.mul_one] at ht
  rw [Int.mul_sub, Int.mul_one]
  revert ht
  generalize (j : Int) * (j : Int) = P
  intro ht
  omega

/-- **M137F-2b: 関数等式の Heisenberg 辞書（本丸）** — ラベル j ごとに、
    解析側 T^j と群側 Φ(j) が同じガウス指数簿記を持つことの一束:

    * `center_is_gauss` — 群側: Φ(j) の中心成分 = tri j
    * `analytic_gauss` — 解析側: T^j(Θ) の q^{tri j} u^j 係数 = 1
      （M92 theta_gauss_tri、仮定なし）
    * `analytic_descent` — 解析側: u^j 対角での q-次数降下量 = tri j
      （M90 tCoeff_shift の閉形式インスタンス）
    * `group_mul` — 群側: 切断の乗法性 Φ(i+j) = Φ(i)·Φ(j)
      （M92 thetaSection_mul）
    * `analytic_iter` — 解析側: 反復関数等式 T^j(Θ) = (−1)^j Θ
      （M90 tCoeff_eq）
    * `pm_pair` — ±-対: ι(Φ(j))·Φ(j) = 中心^j（M116F thetaNeg_section_mul）

    関数等式の j 回反復（解析）と Heisenberg 積の j 乗（群）が
    中心成分 tri j で同期する — 「関数等式が Heisenberg 積をリフトする」
    ことの離散核。 -/
structure FuneqDict (j : Nat) where
  /-- 群側: Φ(j) の中心成分はガウス指数 tri j。 -/
  center_is_gauss : (thetaSection j).2.2 = ((tri j : Nat) : Int)
  /-- 解析側: T^j(Θ) の q^{tri j} u^j 係数 = 1（仮定なしのガウス値）。 -/
  analytic_gauss : ∀ R : CRing, tCoeff R j (tri j) ((j : Int)) = R.one
  /-- 解析側: u^j 対角での q-次数降下量 = tri j = Φ(j) の中心成分。 -/
  analytic_descent : ∀ R : CRing,
    tCoeff R j (tri j) ((j : Int))
      = (thetaRep R 0).coeff ((j : Int) - (j : Int))
  /-- 群側: 切断の乗法性 Φ(i+j) = Φ(i)·Φ(j)。 -/
  group_mul : ∀ i : Nat,
    thetaSection (i + j) = thetaGrp.mul (thetaSection i) (thetaSection j)
  /-- 解析側: 反復関数等式 T^j(Θ) = (−1)^j Θ（係数形）。 -/
  analytic_iter : ∀ (R : CRing) (m : Nat) (n : Int),
    tCoeff R j m n = negPow R j ((thetaRep R m).coeff n)
  /-- ±-対: ι(Φ(j))·Φ(j) = (0,0,j) = 中心の j 乗。 -/
  pm_pair : thetaGrp.mul (thetaNeg.map (thetaSection j)) (thetaSection j)
      = ((0, 0, (j : Int)) : Int × Int × Int)

/-- **M137F-2c: 辞書 witness** — 全フィールドが既存定理の代入。 -/
def funeqDict (j : Nat) : FuneqDict j where
  center_is_gauss := section_gauss_component j
  analytic_gauss := fun R => theta_gauss_tri R j
  analytic_descent := fun R => funeq_gauss_descent R j
  group_mul := fun i => thetaSection_mul i j
  analytic_iter := fun R m n => tCoeff_eq R j m n
  pm_pair := thetaNeg_section_mul j

/-! ## M137F-3: 乗法性の両立 -/

/-- **定理 (M137F-3a): 辞書の乗法性** — Φ(i)·Φ(j) = Φ(i+j)
    （M92 thetaSection_mul の向きを揃えた再輸出）。解析側の
    T^i ∘ T^j = T^{i+j}（反復の合成）に対応する群側の乗法性。 -/
theorem dict_multiplicative (i j : Nat) :
    thetaGrp.mul (thetaSection i) (thetaSection j) = thetaSection (i + j) :=
  (thetaSection_mul i j).symm

/-- **定理 (M137F-3b): コサイクル付きガウス加法則（Nat 版）** —
    tri(i+j) = tri i + tri j + ij。ガウス指数は加法的では**なく**、
    ずれはちょうど Heisenberg 積の 2-コサイクル ij — この非加法性こそ
    Heisenberg 性の析出であり、関数等式の反復が可換群でなく
    Heisenberg 群にリフトする理由。M92 tri_cocycle（Int 版）の
    Nat への降下。 -/
theorem gauss_additive_with_cocycle (i j : Nat) :
    tri (i + j) = tri i + tri j + i * j := by
  have h := tri_cocycle i j
  rw [← Int.natCast_mul] at h
  omega

/-! ## M137F-4: ± との整合 -/

/-- **定理 (M137F-4): 辞書の ±-整合** — ι(Φ(j))·Φ(j) = (0,0,j)
    （M116F thetaNeg_section_mul の再輸出）。±-対がガウス指数簿記
    tri j（2 次）を中心成分 j（1 次）に線形化する — 解析側の
    u ↦ u⁻¹ 対称性（反転 J）と辞書が両立することの群側の核。 -/
theorem dict_pm (j : Nat) :
    thetaGrp.mul (thetaNeg.map (thetaSection j)) (thetaSection j)
      = ((0, 0, (j : Int)) : Int × Int × Int) :=
  thetaNeg_section_mul j

/-! ## M137F-5: 総括 witness -/

/-- **M137F-5a: 関数等式リフトの総括データ** — 辞書（∀ j）・乗法性・
    2-コサイクル恒等式・±-整合・反転 J = 関数等式 T（M98）を一つに
    束ねる。「エタールテータの関数等式が Heisenberg 積をリフトする」
    の辞書化（issue #39 E-1 残件）。 -/
structure FuneqLiftData where
  /-- ラベル j ごとの解析/群辞書。 -/
  dict : ∀ j : Nat, FuneqDict j
  /-- 乗法性: Φ(i)·Φ(j) = Φ(i+j)。 -/
  multiplicative : ∀ i j : Nat,
    thetaGrp.mul (thetaSection i) (thetaSection j) = thetaSection (i + j)
  /-- 2-コサイクル: tri(i+j) = tri i + tri j + ij。 -/
  cocycle : ∀ i j : Nat, tri (i + j) = tri i + tri j + i * j
  /-- ±-整合: ι(Φ(j))·Φ(j) = 中心^j。 -/
  pm : ∀ j : Nat,
    thetaGrp.mul (thetaNeg.map (thetaSection j)) (thetaSection j)
      = ((0, 0, (j : Int)) : Int × Int × Int)
  /-- 反転 J = 関数等式 T（M98 theta_refl_eq_funeq）: 解析側の
      u ↦ u⁻¹ 反転が一段の関数等式と係数レベルで一致。 -/
  reflection : ∀ (R : CRing) (m : Nat),
    (reflRep R (thetaRep R m)).coeff = (tThetaRep R m).coeff

/-- **M137F-5b: witness 本体** — 全フィールド既存定理の代入。 -/
def funeqLiftData : FuneqLiftData where
  dict := funeqDict
  multiplicative := dict_multiplicative
  cocycle := gauss_additive_with_cocycle
  pm := dict_pm
  reflection := theta_refl_eq_funeq

/-- **定理 (M137F-5c): 関数等式リフト辞書の存在（E-1 残件の見出し）**。 -/
theorem funeqLift_exists : Nonempty FuneqLiftData :=
  ⟨funeqLiftData⟩

end IUT
