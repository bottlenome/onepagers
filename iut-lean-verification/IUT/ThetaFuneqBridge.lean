/-
  IUT/ThetaFuneqBridge.lean — M190F: 解析的テータ関数等式と群側捻れの接合
  — 反転 J の反復リフト J(T^j Θ) = T^{l−j}(Θ) と funeqTwist の同定（柱E E-1・並行部品）

  柱E 残課題 E-1（#39）の「解析側（級数レベル）の関数等式と群側の
  中心捻れの接合」切片。M137F は解析側 T^j と群側 Φ(j) の対応を
  **辞書**（同じガウス簿記を持つことの並記）として与えるにとどまり、
  M187F の群側中心捻れ funeqTwist と解析側の関数等式そのものを結ぶ
  **証明された恒等式**は欠けていた。本モジュールは:

    (1) M98 の反転対称性 J(Θ) = −Θ が **Heisenberg 反復列 T^j(Θ) 全体に
        伝播**すること: J(T^j Θ) = −T^j(Θ)（係数レベル、j = 0 の M98-3 の
        全反復への一般化）
    (2) **本丸**: 奇数 l = 2l⋇+1 と 0 ≤ j ≤ l に対し
        **J(T^j Θ) = T^{l−j}(Θ)**（係数・級数の両レベル）——解析側の
        反転作用素 J が反復ラベルの入替 j ↔ l−j を**実現**する。これは
        群側 ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist l j)（M187F-4）の
        級数レベルの対応物であり、両者のラベル入替が同一であることを
        初めて定理として結ぶ
    (3) 入替の両側 T^j / T^{l−j} のガウス点 q-次数は tri j / tri(l−j) で
        あり（M92 theta_gauss_tri、値 1）、その**差はちょうど群側の
        中心捻れ funeqTwist l j**（定義的равенство）——閉形式
        j + l(j−l⋇−1) ≡ j (mod l)、μ_l 像はテータ値ラベル ζ^j（M187F-3）
    (4) 反転 J はガウス点の対の値 (1, −1) を交換する:
        T^j(Θ) の q^{tri j} 係数の u^{−(j+1)} 成分 = −1（±-対の解析版）

    を機械検証する。[EtTh] の「テータ関数等式（解析）が mono-theta
    環境の Heisenberg 積をリフトし、その中心のズレ込みが μ_l 内の
    テータ値ラベルになる」の解析↔群接合の離散核。

  * M190F-1 `negPow_two_mul_add` / `negPow_parity` — j 重否定 (−1)^j の
    偶奇簿記（周期 2、パリティ不変性）
  * M190F-2 `theta_refl_iter` — **反転の反復伝播**: J(T^j Θ) = −T^j(Θ)
    （M98-3 theta_refl_coeff の j = 0 から全反復への持ち上げ、
    negPow_neg による）
  * M190F-3 `theta_refl_iter_label` / `theta_refl_iter_series`（**本丸**）
    — **解析側のラベル入替**: 奇数 l、j ≤ l で J(T^j Θ) = T^{l−j}(Θ)
    （係数レベル + 級数（Quot）レベル J(T^j Θ) = thetaIter (l−j)）。
    パリティ (j+1) ≡ l−j (mod 2) が l の奇性から従う
  * M190F-4 `theta_gauss_pm` — 反転側ガウス値 = −1: T^j(Θ) の
    q^{tri j} u^{−(j+1)} 係数 = −1（ガウス点の ±-対の解析版、
    M137F dict_pm の級数側対応物）
  * M190F-5 `funeq_gauss_degree_twist` — **ガウス次数差 = funeqTwist**:
    入替対 (T^j, T^{l−j}) のガウス点 q-次数の差 tri j − tri(l−j) は
    群側捻れ funeqTwist l j に定義的に一致し（rfl）、閉形式
    j + l(j−l⋇−1)（M187F-2）を持つ
  * M190F-6 `funeq_analytic_group_bridge` — **解析↔群の一括接合**:
    解析側入替 J(T^j Θ) = T^{l−j}(Θ)・群側入替 ι_l(Φ_l(j)) =
    Φ_l(l−j)·red(0,0,funeqTwist l j)・捻れ = ガウス次数差・μ_l 像 = ζ^j
    の四者が同一ラベル j で貼り合う
  * M190F-7 `ThetaFuneqBridgeData` / `thetaFuneqBridgeData` /
    `thetaFuneqBridge_exists` — 総括レコード（生成元 ζ の存在は
    M121F mu_l_zp_exists から）

  意義: M137F の辞書（解析側と群側が「同じ簿記を持つ」ことの並記）を、
  **反転作用素 J がラベル入替 j ↔ l−j を解析側で実現し、その入替対の
  ガウス次数差が群側中心捻れ funeqTwist と一致する**という証明された
  恒等式に昇格する。E-1 のうち「級数レベル関数等式 T(Θ) = −Θ = J(Θ)
  （M89/M98）と群側捻れ（M187F）の接合」を閉じる。

  正直な限定: 接合は (i) 解析側の反転 J による反復ラベル入替
  J(T^j Θ) = T^{l−j}(Θ)（係数・級数レベルの等式）、(ii) 群側の
  ι_l によるラベル入替（M187F-4 の等式）、(iii) 両者の捻れ簿記の同定
  funeqTwist l j = tri j − tri(l−j)（定義的）+ 閉形式 + μ_l 像 ζ^j、の
  三層を同一ラベル j で束ねる形で行う。級数環 R[u^{±1}][[q]] から
  thetaGrp への**単一の作用素レベル準同型**（T ↦ Φ(1)-乗法を送る関手）
  としての定式化は未形式化であり、捻れは解析側では q-次数差・群側では
  中心元として現れる（同定は共有される tri 簿記経由であって、級数への
  環準同型の適用ではない）。p 進テータ値のガロア同変な評価・tempered
  π₁ の商としての実現も未形式化（E-1 残）。商群レベルの主張は
  Quot.sound を使う（thetaGrpMod / laurentRel の構成に内在、選択公理
  ではない）。全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.ThetaHeisenbergLift
import IUT.FuneqLift

namespace IUT

/-! ## M190F-1: j 重否定の偶奇簿記 -/

/-- **M190F-1a: j 重否定は周期 2** — negPow (2t + k) = negPow k。
    (−1)² = 1 の反復形（neg_neg の t 回適用）。 -/
theorem negPow_two_mul_add (R : CRing) (k : Nat) (x : R.carrier) :
    ∀ t : Nat, negPow R (2 * t + k) x = negPow R k x := by
  intro t
  induction t with
  | zero =>
    have h : 2 * 0 + k = k := by omega
    rw [h]
  | succ t ih =>
    have h : 2 * (t + 1) + k = 2 * t + k + 1 + 1 := by omega
    rw [h]
    show R.neg (R.neg (negPow R (2 * t + k) x)) = negPow R k x
    rw [CRing.neg_neg R, ih]

/-- **M190F-1b: j 重否定のパリティ不変性** — a ≡ b (mod 2) なら
    negPow a = negPow b。(−1)^a = (−1)^b の骨格形。 -/
theorem negPow_parity (R : CRing) (a b : Nat) (hab : a % 2 = b % 2)
    (x : R.carrier) : negPow R a x = negPow R b x := by
  have ha : a = 2 * (a / 2) + a % 2 := by omega
  have hb : b = 2 * (b / 2) + b % 2 := by omega
  rw [ha, hb, hab]
  rw [negPow_two_mul_add R (b % 2) x (a / 2),
      negPow_two_mul_add R (b % 2) x (b / 2)]

/-! ## M190F-2: 反転対称性の反復伝播 -/

/-- **定理 (M190F-2): 反転は全反復に伝播する** — J(T^j Θ) = −T^j(Θ)
    （係数レベル）。M98-3 の J(Θ) = −Θ（j = 0）を negPow_neg ごしに
    全ての Heisenberg 反復 T^j(Θ) へ持ち上げる。群側の
    「ι は Heisenberg 積と両立する」（M187F-5a）の解析側対応物。 -/
theorem theta_refl_iter (R : CRing) (j m : Nat) :
    (reflRep R (tGaussRep R j m)).coeff = (lNeg R (tGaussRep R j m)).coeff := by
  funext n
  show tCoeff R j m (-(n + 1)) = R.neg (tCoeff R j m n)
  rw [tCoeff_eq R j m (-(n + 1)), tCoeff_eq R j m n]
  have hpt : (thetaRep R m).coeff (-(n + 1))
      = R.neg ((thetaRep R m).coeff n) :=
    congrFun (theta_refl_coeff R m) n
  rw [hpt, negPow_neg]

/-! ## M190F-3: 解析側のラベル入替（本丸） -/

/-- **定理 (M190F-3a): 反転 J は反復ラベルの入替 j ↔ l−j を実現する
    （本丸・係数形）** — 奇数 l = 2l⋇+1、j ≤ l で
    **J(T^j Θ) = T^{l−j}(Θ)**。J(T^j Θ) = (−1)^{j+1} Θ（M190F-2 +
    M90-3）と T^{l−j}(Θ) = (−1)^{l−j} Θ が、l の奇性によるパリティ
    一致 j+1 ≡ l−j (mod 2) で貼り合う。群側の反転
    ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist l j)（M187F-4a）と
    同一のラベル入替が級数レベルで成立することの機械検証。 -/
theorem theta_refl_iter_label (R : CRing) (l L j : Nat)
    (hodd : l = 2 * L + 1) (hj : j ≤ l) (m : Nat) :
    (reflRep R (tGaussRep R j m)).coeff = (tGaussRep R (l - j) m).coeff := by
  funext n
  show tCoeff R j m (-(n + 1)) = tCoeff R (l - j) m n
  rw [tCoeff_eq R j m (-(n + 1)), tCoeff_eq R (l - j) m n]
  have hpt : (thetaRep R m).coeff (-(n + 1))
      = R.neg ((thetaRep R m).coeff n) :=
    congrFun (theta_refl_coeff R m) n
  rw [hpt, negPow_neg]
  show negPow R (j + 1) ((thetaRep R m).coeff n)
    = negPow R (l - j) ((thetaRep R m).coeff n)
  exact negPow_parity R (j + 1) (l - j) (by omega) ((thetaRep R m).coeff n)

/-- **定理 (M190F-3b): ラベル入替の級数（Quot）レベル** —
    J(T^j Θ) = thetaIter (l−j) ∈ R[u^{±1}][[q]]。M190F-3a を
    laurentRel（係数一致）の Quot.sound で級数の等式に昇格。 -/
theorem theta_refl_iter_series (R : CRing) (l L j : Nat)
    (hodd : l = 2 * L + 1) (hj : j ≤ l) :
    (fun m => Quot.mk (laurentRel R) (reflRep R (tGaussRep R j m)))
      = thetaIter R (l - j) := by
  funext m
  exact Quot.sound (theta_refl_iter_label R l L j hodd hj m)

/-! ## M190F-4: 反転側ガウス値 = −1 -/

/-- **定理 (M190F-4): ガウス点の ±-対（解析版）** — T^j(Θ) の
    q^{tri j} 係数は u^j 成分に +1（M92 theta_gauss_tri）、その反転
    パートナー u^{−(j+1)} 成分に **−1** を持つ。反転 J がガウス点の
    対の値 (1, −1) を交換することの機械検証 — 群側の ±-対
    ι(Φ(j))·Φ(j) = (0,0,j)（M137F-4 dict_pm）の級数側対応物。 -/
theorem theta_gauss_pm (R : CRing) (j : Nat) :
    tCoeff R j (tri j) (-((j : Int) + 1)) = R.neg R.one := by
  have hg : negPow R j ((thetaRep R (tri j)).coeff ((j : Int))) = R.one := by
    have h := theta_gauss_tri R j
    rw [tCoeff_eq R j (tri j) ((j : Int))] at h
    exact h
  rw [tCoeff_eq R j (tri j) (-((j : Int) + 1))]
  have hpt : (thetaRep R (tri j)).coeff (-((j : Int) + 1))
      = R.neg ((thetaRep R (tri j)).coeff ((j : Int))) :=
    congrFun (theta_refl_coeff R (tri j)) ((j : Int))
  rw [hpt, negPow_neg, hg]

/-! ## M190F-5: ガウス次数差 = 群側中心捻れ -/

/-- **定理 (M190F-5): 入替対のガウス次数差 = funeqTwist** — 解析側の
    ラベル入替（M190F-3a）の両側 T^j(Θ) / T^{l−j}(Θ) はそれぞれ
    q-次数 tri j / tri(l−j) にガウス点（値 1）を持ち、その q-次数の
    差は群側の中心捻れ funeqTwist l j に**定義的に一致**し（rfl）、
    閉形式 j + l(j−l⋇−1) ≡ j (mod l)（M187F-2）を持つ。解析側の
    「関数等式による q-次数のズレ込み」と群側の「中心捻れ」が同一の
    整数簿記であることの同定。 -/
theorem funeq_gauss_degree_twist (R : CRing) (l L j : Nat)
    (hodd : l = 2 * L + 1) (hj : j ≤ l) :
    tCoeff R j (tri j) ((j : Int)) = R.one
    ∧ tCoeff R (l - j) (tri (l - j)) (((l - j : Nat) : Int)) = R.one
    ∧ funeqTwist l j
        = ((tri j : Nat) : Int) - ((tri (l - j) : Nat) : Int)
    ∧ funeqTwist l j
        = (j : Int) + (l : Int) * ((j : Int) - (L : Int) - 1) :=
  ⟨theta_gauss_tri R j, theta_gauss_tri R (l - j), rfl,
    funeqTwist_closed l L j hodd hj⟩

/-! ## M190F-6: 解析↔群の一括接合 -/

/-- **定理 (M190F-6): 解析↔群接合（一括形）** — ラベル j < l ごとに、
    (1) 解析側入替 J(T^j Θ) = T^{l−j}(Θ)（M190F-3a）、
    (2) 群側入替 ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist l j)
    （M187F-4a）、(3) 捻れ = ガウス次数差 tri j − tri(l−j)（定義的）、
    (4) 捻れの μ_l 像 = テータ値ラベル ζ^j（M187F-3）の四者が
    **同一の j で**貼り合う。M137F の辞書の恒等式への昇格。 -/
theorem funeq_analytic_group_bridge (R : CRing) (p l L : Nat) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (ζ : (Zp p).carrier) (j : Nat) (hj : j < l) :
    (∀ m : Nat, (reflRep R (tGaussRep R j m)).coeff
        = (tGaussRep R (l - j) m).coeff)
    ∧ (thetaNegMod l).map (thetaSectionMod l j)
        = (thetaGrpMod l).mul (thetaSectionMod l (l - j))
            ((thetaRed l).map (0, 0, funeqTwist l j))
    ∧ funeqTwist l j
        = ((tri j : Nat) : Int) - ((tri (l - j) : Nat) : Int)
    ∧ centerToMu p l ζ (funeqTwist l j) = zpPow p ζ j :=
  ⟨fun m => theta_refl_iter_label R l L j hodd (by omega) m,
    thetaNegMod_section_twist l j (by omega),
    rfl,
    funeqTwist_mu p l L hL hodd ζ j hj⟩

/-! ## M190F-7: 総括レコード -/

/-- **M190F-7a: 解析↔群 関数等式接合データ** — μ_l 生成元 ζ・反転の
    反復伝播・解析側ラベル入替（係数/級数）・ガウス ±-対・ガウス
    次数差 = 捻れ・閉形式・群側入替・μ_l ラベルの一括束ね。E-1 の
    「級数レベル関数等式と群側中心捻れの接合」切片の witness。 -/
structure ThetaFuneqBridgeData (R : CRing) (p l L : Nat) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) where
  /-- μ_l(O) の生成元（O = ℤ_p 内の l 乗根）。 -/
  ζ : (Zp p).carrier
  /-- ζ は l 乗根: ζ^l = 1。 -/
  root : zpPow p ζ l = zpOne p
  /-- 反転の反復伝播: J(T^j Θ) = −T^j(Θ)（係数レベル、∀ j）。 -/
  refl_iter : ∀ j m : Nat,
    (reflRep R (tGaussRep R j m)).coeff = (lNeg R (tGaussRep R j m)).coeff
  /-- 解析側ラベル入替（係数レベル）: J(T^j Θ) = T^{l−j}(Θ)。 -/
  analytic_inversion : ∀ j : Nat, j ≤ l → ∀ m : Nat,
    (reflRep R (tGaussRep R j m)).coeff = (tGaussRep R (l - j) m).coeff
  /-- 解析側ラベル入替（級数レベル）: J(T^j Θ) = thetaIter (l−j)。 -/
  analytic_inversion_series : ∀ j : Nat, j ≤ l →
    (fun m => Quot.mk (laurentRel R) (reflRep R (tGaussRep R j m)))
      = thetaIter R (l - j)
  /-- ガウス値: T^j(Θ) の q^{tri j} u^j 係数 = 1。 -/
  gauss_value : ∀ j : Nat, tCoeff R j (tri j) ((j : Int)) = R.one
  /-- ガウス ±-対: 反転パートナー u^{−(j+1)} 成分 = −1。 -/
  gauss_pm : ∀ j : Nat,
    tCoeff R j (tri j) (-((j : Int) + 1)) = R.neg R.one
  /-- 捻れ = ガウス次数差: funeqTwist l j = tri j − tri(l−j)。 -/
  degree_twist : ∀ j : Nat,
    funeqTwist l j = ((tri j : Nat) : Int) - ((tri (l - j) : Nat) : Int)
  /-- 捻れの閉形式: funeqTwist l j = j + l(j−l⋇−1) ≡ j (mod l)。 -/
  twist_closed : ∀ j : Nat, j ≤ l →
    funeqTwist l j = (j : Int) + (l : Int) * ((j : Int) - (L : Int) - 1)
  /-- 群側入替: ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist l j)。 -/
  group_inversion : ∀ j : Nat, j ≤ l →
    (thetaNegMod l).map (thetaSectionMod l j)
      = (thetaGrpMod l).mul (thetaSectionMod l (l - j))
          ((thetaRed l).map (0, 0, funeqTwist l j))
  /-- 捻れの μ_l 像 = テータ値ラベル ζ^j。 -/
  twist_mu : ∀ j : Nat, j < l →
    centerToMu p l ζ (funeqTwist l j) = zpPow p ζ j

/-- **M190F-7b: witness 本体** — 位数 l の生成元 ζ から全フィールドを
    M190F-2〜5 と M187F-2/3/4 で埋める。 -/
def thetaFuneqBridgeData (R : CRing) (p l L : Nat) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) :
    ThetaFuneqBridgeData R p l L hL hodd where
  ζ := ζ
  root := hζl
  refl_iter := fun j m => theta_refl_iter R j m
  analytic_inversion := fun j hj m =>
    theta_refl_iter_label R l L j hodd hj m
  analytic_inversion_series := fun j hj =>
    theta_refl_iter_series R l L j hodd hj
  gauss_value := fun j => theta_gauss_tri R j
  gauss_pm := fun j => theta_gauss_pm R j
  degree_twist := fun _ => rfl
  twist_closed := fun j hj => funeqTwist_closed l L j hodd hj
  group_inversion := fun j hj => thetaNegMod_section_twist l j hj
  twist_mu := fun j hj => funeqTwist_mu p l L hL hodd ζ j hj

/-- **定理 (M190F-7c): 解析↔群 関数等式接合データの存在（M190F 見出し）**
    — p 素数・l = 2l⋇+1 ∣ p−1 なら接合データが存在する（生成元は
    M121F mu_l_zp_exists から）。 -/
theorem thetaFuneqBridge_exists (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) :
    Nonempty (ThetaFuneqBridgeData R p l L hL hodd) := by
  obtain ⟨ζ, hζl, hdist, ha⟩ := mu_l_zp_exists p l hp (by omega) hdvd
  exact ⟨thetaFuneqBridgeData R p l L hL hodd ζ hζl⟩

end IUT

