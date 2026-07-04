/-
  IUT/ThetaHeisenbergLift.lean — M187F: エタールテータ関数等式の Heisenberg リフト
  — 中心捻れの閉形式と μ_l ラベル同定（柱E E-1・並行部品）

  柱E 残課題 E-1（#39）の「エタールテータの関数等式が Heisenberg 積と
  両立する」切片。M116F の ±-切断関係 ι(Φ(j)) ≡ Φ(l−j)·(0,0,z) (mod l)
  は中心捻れ z を**存在形**（∃ z）でしか与えなかった。本モジュールは
  この捻れを**明示的に** funeqTwist l j := tri j − tri(l−j) と定義し、

    (1) 閉形式 funeqTwist l j = j + l·(j − l⋇ − 1)、すなわち
        **funeqTwist l j ≡ j (mod l)**（l = 2l⋇+1）
    (2) よって M162F の同期写像 centerToMu による μ_l 像は
        **ちょうどテータ値ラベル ζ^j**
    (3) 商群 thetaGrpMod l では ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist l j)
        が**等式**として成立し、Heisenberg 積と両立する:
        ι_l(Φ_l(i)·Φ_l(j)) = Φ_l(l−(i+j))·red(0,0,funeqTwist l (i+j))、
        捻れの μ_l 像は乗法的 ζ^i·ζ^j

    を機械検証する。[EtTh] の「エタールテータの関数等式（反転 j ↔ l−j）は
    mono-theta 環境の Heisenberg 積をリフトし、その中心のズレ込みは
    μ_l 係数シクロトームの中でテータ値ラベルとして実現される」の離散核。

  * M187F-1 `funeqTwist` / `thetaNeg_label_twist` — 関数等式の中心捻れの
    明示形と、存在量化なしの反転関係
    ι(Φ(j)) ≡ Φ(l−j)·(0,0,funeqTwist l j) (mod l)（M116F-5b の強化）
  * M187F-2 `funeqTwist_closed` — **捻れの閉形式**:
    funeqTwist l j = j + l·(j − l⋇ − 1)。三角数の差
    2(tri j − tri(l−j)) = (2j−l)(l+1) の l = 2l⋇+1 での厳密整数分解
  * M187F-3 `funeqTwist_mu`（**本丸1**）— **捻れの μ_l 像 = テータ値
    ラベル**: centerToMu p l ζ (funeqTwist l j) = ζ^j。関数等式の
    中心のズレ込みが μ_l 係数シクロトーム（M162F/M124F）の中で
    ラベル j の μ_l 冪として実現される
  * M187F-4 `thetaNegMod_section_twist` / `thetaNegMod_mul_twist`
    （**本丸2**）— **商群での等式リフト**: thetaGrpMod l で
    ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist l j)（Quot.sound）、
    および Heisenberg 積版
    ι_l(Φ_l(i)·Φ_l(j)) = Φ_l(l−(i+j))·red(0,0,funeqTwist l (i+j))
  * M187F-5 `funeq_heisenberg_mul` / `funeqTwist_mul_mu` /
    `funeq_lift_pm_compat` — Heisenberg 積との μ_l 両立:
    積の反転の捻れの μ_l 像は ζ^i·ζ^j（乗法的）、捻れ同士も
    μ_l で乗法的、M162F `theta_pm_mu_label` の ∃ z を明示捻れ
    + μ_l ラベル付きで強化した接合
  * M187F-6 `ThetaHeisenbergLiftData` / `thetaHeisenbergLiftData` /
    `thetaHeisenbergLift_exists` — 総括レコード（生成元 ζ の存在は
    M121F mu_l_zp_exists から）

  意義: E-1 のうち「関数等式の反転 j ↔ l−j が Heisenberg 積を
  リフトする際の中心捻れの正体」を閉じる。M116F は捻れの存在まで、
  M162F は μ_l ラベルの ±-分類までだったのに対し、本モジュールは
  捻れの閉形式 j + l(j−l⋇−1) を確定し、その μ_l 像がちょうど
  テータ値ラベル ζ^j であること・積で乗法的であることを初めて接合する。

  正直な限定: 扱うのは離散 Heisenberg 骨格 thetaGrp とその mod-l 商・
  固定素数 p の ℤ_p 内 μ_l(O) のみ。解析側（M89/M98 の級数レベル
  関数等式 T(Θ) = −Θ = J(Θ)）と本モジュールの群側捻れの直接接合は
  M137F の辞書レベルにとどまり、p 進テータ関数の値そのものの
  ガロア同変な評価・tempered π₁ の商としての実現は未形式化（E-1 残）。
  商群レベルの主張（M187F-4）は Quot.sound を使う（thetaGrpMod の
  構成に内在、選択公理ではない）。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.MuLIdentification

namespace IUT

/-! ## M187F-1: 関数等式の中心捻れの明示形 -/

/-- **M187F-1a: 関数等式の中心捻れ** — ι(Φ(j)) と Φ(l−j) の mod-l
    比較で第 3 成分に現れるズレ z = tri j − tri(l−j)（M116F-5b の
    存在証明の witness を定義に昇格）。 -/
def funeqTwist (l j : Nat) : Int :=
  ((tri j : Nat) : Int) - ((tri (l - j) : Nat) : Int)

/-- **定理 (M187F-1b): 存在量化なしの反転関係** —
    ι(Φ(j)) ≡ Φ(l−j)·(0,0,funeqTwist l j) (mod l)。M116F-5b
    `thetaNeg_label_center` の ∃ z を明示捻れで置き換えた強化形。
    第 1・2 成分は −j ≡ l−j (mod l)（witness −1）、第 3 成分は
    funeqTwist がズレを厳密に吸収する（witness 0）。 -/
theorem thetaNeg_label_twist (l j : Nat) (hj : j ≤ l) :
    thetaRelMod l (thetaNeg.map (thetaSection j))
      (thetaGrp.mul (thetaSection (l - j)) (0, 0, funeqTwist l j)) := by
  refine ⟨⟨-1, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩⟩
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

/-! ## M187F-2: 捻れの閉形式 -/

/-- **定理 (M187F-2): 捻れの閉形式** — l = 2l⋇+1 のとき
    funeqTwist l j = j + l·(j − l⋇ − 1)。特に **funeqTwist l j ≡ j
    (mod l)**。証明は三角数の橋 2·tri j = j(j+1)（M92）を両ラベル
    j, l−j に適用し、非線形単項式 j², l², lj, l·l⋇ を原子化して
    2(tri j − tri(l−j)) = l(2j−l−1) = 2l(j−l⋇−1) を線形化する。 -/
theorem funeqTwist_closed (l L j : Nat) (hodd : l = 2 * L + 1)
    (hj : j ≤ l) :
    funeqTwist l j = (j : Int) + (l : Int) * ((j : Int) - (L : Int) - 1) := by
  show ((tri j : Nat) : Int) - ((tri (l - j) : Nat) : Int)
    = (j : Int) + (l : Int) * ((j : Int) - (L : Int) - 1)
  have h1 := tri_int j
  have h2 := tri_int (l - j)
  have hcast : ((l - j : Nat) : Int) = (l : Int) - (j : Int) := by omega
  rw [hcast] at h2
  -- h1 : 2·tri j = j·j + j
  rw [Int.mul_add, Int.mul_one] at h1
  -- h2 : 2·tri(l−j) = (l·l − l·j) − (l·j − j·j) + (l − j)
  rw [Int.mul_add, Int.mul_one, Int.sub_mul, Int.mul_sub, Int.mul_sub,
      Int.mul_comm (j : Int) (l : Int)] at h2
  -- 目標右辺の展開: l·(j − L − 1) = l·j − l·L − l
  rw [Int.mul_sub, Int.mul_sub, Int.mul_one]
  -- l² = 2·(l·L) + l（l = 2L+1 の非線形帰結を先に供給）
  have hl2 : (l : Int) = 2 * (L : Int) + 1 := by omega
  have hB : (l : Int) * (l : Int) = 2 * ((l : Int) * (L : Int)) + (l : Int) := by
    have hstep : (l : Int) * (l : Int) = (l : Int) * (2 * (L : Int) + 1) := by
      rw [← hl2]
    rw [hstep, Int.mul_add, Int.mul_one, Int.mul_left_comm (l : Int) 2 (L : Int)]
  -- 非線形単項式を原子化して omega
  revert h1 h2 hB
  generalize (j : Int) * (j : Int) = A
  generalize (l : Int) * (l : Int) = B
  generalize (l : Int) * (j : Int) = C
  generalize (l : Int) * (L : Int) = D
  intro h1 h2 hB
  omega

/-! ## M187F-3: 捻れの μ_l 像 = テータ値ラベル（本丸1） -/

/-- **定理 (M187F-3): 捻れの μ_l 像はテータ値ラベル（本丸1）** —
    centerToMu p l ζ (funeqTwist l j) = ζ^j。関数等式の反転
    j ↔ l−j が Heisenberg 積にリフトされる際の中心のズレ込みは、
    μ_l 係数シクロトーム（M124F 同期写像・M162F 同一視）の中で
    **ちょうどラベル j の μ_l 冪**として実現される。閉形式
    funeqTwist ≡ j (mod l)（M187F-2）と well-definedness
    （centerToMu_congr、l ≥ 3 のため hL）、自然数ラベルの像
    （M162F-3a）による。 -/
theorem funeqTwist_mu (p l L : Nat) (hL : 1 ≤ L) (hodd : l = 2 * L + 1)
    (ζ : (Zp p).carrier) (j : Nat) (hj : j < l) :
    centerToMu p l ζ (funeqTwist l j) = zpPow p ζ j := by
  have hcongr : centerToMu p l ζ (funeqTwist l j)
      = centerToMu p l ζ ((j : Nat) : Int) := by
    refine centerToMu_congr p l (by omega) ζ
      ⟨(j : Int) - (L : Int) - 1, ?_⟩
    rw [funeqTwist_closed l L j hodd (by omega)]
    generalize (l : Int) * ((j : Int) - (L : Int) - 1) = P
    omega
  rw [hcongr]
  exact centerToMu_natCast p l ζ hj

/-! ## M187F-4: 商群での等式リフト（本丸2） -/

/-- **定理 (M187F-4a): 商群での反転等式（本丸2）** — thetaGrpMod l で
    ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist l j) が**等式**として
    成立する（thetaRelMod の witness を Quot.sound で商に落とす）。
    合同（M116F-5b）から等式への昇格 — 関数等式の反転が mod-l
    テータ群の中で厳密な恒等式になることの形式化。 -/
theorem thetaNegMod_section_twist (l j : Nat) (hj : j ≤ l) :
    (thetaNegMod l).map (thetaSectionMod l j)
      = (thetaGrpMod l).mul (thetaSectionMod l (l - j))
          ((thetaRed l).map (0, 0, funeqTwist l j)) := by
  show Quot.mk (thetaRelMod l) (thetaNeg.map (thetaSection j))
    = Quot.mk (thetaRelMod l)
        (thetaGrp.mul (thetaSection (l - j)) (0, 0, funeqTwist l j))
  exact Quot.sound (thetaNeg_label_twist l j hj)

/-- **定理 (M187F-4b): 反転は Heisenberg 積をリフトする（本丸2・積版）**
    — ι_l(Φ_l(i)·Φ_l(j)) = Φ_l(l−(i+j))·red(0,0,funeqTwist l (i+j))。
    切断の乗法性（M98F-5b）で積をラベル i+j の切断に畳み、M187F-4a を
    適用する。関数等式の反転がテータ群 mod l の**積構造と両立**する
    ことの等式形。 -/
theorem thetaNegMod_mul_twist (l i j : Nat) (hij : i + j ≤ l) :
    (thetaNegMod l).map
        ((thetaGrpMod l).mul (thetaSectionMod l i) (thetaSectionMod l j))
      = (thetaGrpMod l).mul (thetaSectionMod l (l - (i + j)))
          ((thetaRed l).map (0, 0, funeqTwist l (i + j))) := by
  rw [← thetaSectionMod_mul l i j]
  exact thetaNegMod_section_twist l (i + j) hij

/-! ## M187F-5: Heisenberg 積との μ_l 両立と M162F の強化 -/

/-- **定理 (M187F-5a): 積の反転捻れの μ_l 像は乗法的** —
    ι(Φ(i)·Φ(j)) ≡ Φ(l−(i+j))·(0,0,funeqTwist l (i+j)) (mod l) かつ
    その捻れの μ_l 像は **ζ^i·ζ^j**。関数等式の反転が Heisenberg 積を
    リフトし、中心捻れが μ_l 側でラベルの積として振る舞うことの一括形。 -/
theorem funeq_heisenberg_mul (p l L : Nat) (hL : 1 ≤ L) (hodd : l = 2 * L + 1)
    (ζ : (Zp p).carrier) (i j : Nat) (hij : i + j < l) :
    thetaRelMod l
        (thetaNeg.map (thetaGrp.mul (thetaSection i) (thetaSection j)))
        (thetaGrp.mul (thetaSection (l - (i + j)))
          (0, 0, funeqTwist l (i + j)))
      ∧ centerToMu p l ζ (funeqTwist l (i + j))
          = zpMul p (zpPow p ζ i) (zpPow p ζ j) := by
  refine ⟨?_, ?_⟩
  · rw [← thetaSection_mul i j]
    exact thetaNeg_label_twist l (i + j) (by omega)
  · rw [funeqTwist_mu p l L hL hodd ζ (i + j) hij]
    exact zpPow_add p ζ i j

/-- **定理 (M187F-5b): 捻れ同士も μ_l で乗法的** — ラベル i, j, i+j の
    捻れの μ_l 像は centerToMu(funeqTwist i)·centerToMu(funeqTwist j)
    = centerToMu(funeqTwist (i+j))（= ζ^{i+j}）を満たす。関数等式の
    中心捻れ簿記が μ_l の中で 2-コサイクル的な障害なしに合成する。 -/
theorem funeqTwist_mul_mu (p l L : Nat) (hL : 1 ≤ L) (hodd : l = 2 * L + 1)
    (ζ : (Zp p).carrier) (i j : Nat) (hi : i < l) (hj : j < l)
    (hij : i + j < l) :
    zpMul p (centerToMu p l ζ (funeqTwist l i))
        (centerToMu p l ζ (funeqTwist l j))
      = centerToMu p l ζ (funeqTwist l (i + j)) := by
  rw [funeqTwist_mu p l L hL hodd ζ i hi, funeqTwist_mu p l L hL hodd ζ j hj,
      funeqTwist_mu p l L hL hodd ζ (i + j) hij, zpPow_add]

/-- **定理 (M187F-5c): M162F 接合の強化** — M162F `theta_pm_mu_label` の
    存在量化 ∃ z を明示捻れ funeqTwist l j で実現し、さらにその z の
    μ_l 像がテータ値ラベル ζ^j であることを付す。μ_l 側の反転
    ζ^j·ζ^{l−j} = 1（M162F-4c）と併せ、**ι のラベル入替・中心捻れ・
    μ_l ラベル**の三者が同一の j で貼り合うことの witness。 -/
theorem funeq_lift_pm_compat (p l L : Nat) (hL : 1 ≤ L) (hodd : l = 2 * L + 1)
    (ζ : (Zp p).carrier) (hζl : zpPow p ζ l = zpOne p)
    (j : Nat) (hpos : 0 < j) (hj : j < l) :
    (thetaRelMod l (thetaNeg.map (thetaSection j))
        (thetaGrp.mul (thetaSection (l - j)) (0, 0, funeqTwist l j))
      ∧ centerToMu p l ζ (funeqTwist l j) = zpPow p ζ j)
    ∧ zpMul p (zpPow p ζ j) (zpPow p ζ (l - j)) = zpOne p :=
  ⟨⟨thetaNeg_label_twist l j (by omega),
      funeqTwist_mu p l L hL hodd ζ j hj⟩,
    (mu_theta_pm_compat p l ζ hζl hpos hj).1⟩

/-! ## M187F-6: 総括レコード -/

/-- **M187F-6a: 関数等式 Heisenberg リフトデータ** — μ_l 生成元 ζ・
    捻れの反転関係・閉形式・μ_l ラベル同定・商群での等式リフト
    （単項・積）・μ_l 乗法両立・M162F ±-接合の一括束ね。E-1 の
    「関数等式の Heisenberg 積リフト」切片の witness。 -/
structure ThetaHeisenbergLiftData (p l L : Nat) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) where
  /-- μ_l(O) の生成元（O = ℤ_p 内の l 乗根）。 -/
  ζ : (Zp p).carrier
  /-- ζ は l 乗根: ζ^l = 1。 -/
  root : zpPow p ζ l = zpOne p
  /-- 反転関係（存在量化なし）: ι(Φ(j)) ≡ Φ(l−j)·(0,0,funeqTwist l j)。 -/
  twist_rel : ∀ j : Nat, j ≤ l →
    thetaRelMod l (thetaNeg.map (thetaSection j))
      (thetaGrp.mul (thetaSection (l - j)) (0, 0, funeqTwist l j))
  /-- 捻れの閉形式: funeqTwist l j = j + l·(j − l⋇ − 1)。 -/
  twist_closed : ∀ j : Nat, j ≤ l →
    funeqTwist l j = (j : Int) + (l : Int) * ((j : Int) - (L : Int) - 1)
  /-- 捻れの μ_l 像 = テータ値ラベル ζ^j。 -/
  twist_mu : ∀ j : Nat, j < l →
    centerToMu p l ζ (funeqTwist l j) = zpPow p ζ j
  /-- 商群での反転等式: ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist l j)。 -/
  quot_lift : ∀ j : Nat, j ≤ l →
    (thetaNegMod l).map (thetaSectionMod l j)
      = (thetaGrpMod l).mul (thetaSectionMod l (l - j))
          ((thetaRed l).map (0, 0, funeqTwist l j))
  /-- 商群での積リフト: ι_l(Φ_l(i)·Φ_l(j)) = Φ_l(l−(i+j))·red(0,0,捻れ)。 -/
  quot_mul_lift : ∀ i j : Nat, i + j ≤ l →
    (thetaNegMod l).map
        ((thetaGrpMod l).mul (thetaSectionMod l i) (thetaSectionMod l j))
      = (thetaGrpMod l).mul (thetaSectionMod l (l - (i + j)))
          ((thetaRed l).map (0, 0, funeqTwist l (i + j)))
  /-- 積の反転捻れの μ_l 像は乗法的: = ζ^i·ζ^j。 -/
  mul_mu : ∀ i j : Nat, i + j < l →
    centerToMu p l ζ (funeqTwist l (i + j))
      = zpMul p (zpPow p ζ i) (zpPow p ζ j)
  /-- 捻れ同士の μ_l 乗法両立。 -/
  twist_cocycle : ∀ i j : Nat, i < l → j < l → i + j < l →
    zpMul p (centerToMu p l ζ (funeqTwist l i))
        (centerToMu p l ζ (funeqTwist l j))
      = centerToMu p l ζ (funeqTwist l (i + j))
  /-- M162F 接合: μ_l 側の反転 ζ^j·ζ^{l−j} = 1。 -/
  pm_inv : ∀ j : Nat, 0 < j → j < l →
    zpMul p (zpPow p ζ j) (zpPow p ζ (l - j)) = zpOne p

/-- **M187F-6b: witness 本体** — 位数 l の生成元 ζ から全フィールドを
    M187F-1〜5 で埋める。 -/
def thetaHeisenbergLiftData (p l L : Nat) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) :
    ThetaHeisenbergLiftData p l L hL hodd where
  ζ := ζ
  root := hζl
  twist_rel := fun j hj => thetaNeg_label_twist l j hj
  twist_closed := fun j hj => funeqTwist_closed l L j hodd hj
  twist_mu := fun j hj => funeqTwist_mu p l L hL hodd ζ j hj
  quot_lift := fun j hj => thetaNegMod_section_twist l j hj
  quot_mul_lift := fun i j hij => thetaNegMod_mul_twist l i j hij
  mul_mu := fun i j hij =>
    (funeq_heisenberg_mul p l L hL hodd ζ i j hij).2
  twist_cocycle := fun i j hi hj hij =>
    funeqTwist_mul_mu p l L hL hodd ζ i j hi hj hij
  pm_inv := fun _ hpos hj => (mu_theta_pm_compat p l ζ hζl hpos hj).1

/-- **定理 (M187F-6c): 関数等式 Heisenberg リフトデータの存在
    （M187F 見出し）** — p 素数・l = 2l⋇+1 ∣ p−1 なら関数等式の
    Heisenberg リフトデータが存在する（生成元は M121F
    mu_l_zp_exists から）。 -/
theorem thetaHeisenbergLift_exists (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) :
    Nonempty (ThetaHeisenbergLiftData p l L hL hodd) := by
  obtain ⟨ζ, hζl, hdist, ha⟩ := mu_l_zp_exists p l hp (by omega) hdvd
  exact ⟨thetaHeisenbergLiftData p l L hL hodd ζ hζl⟩

end IUT

