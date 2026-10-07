/-
  IUT/ThetaCenterMod.lean — M126F: テータ中心の商持ち上げ — centerToMu の thetaGrpMod レベル化

  M124F（シクロトミック同期）の正直申告「商群 thetaGrpMod l レベルの
  言明ではなく thetaGrp レベル + mod-l 降下の組で表現した」の解消。
  centerToMu を商群 thetaGrpMod l（M98F）の carrier 全体からの関数に
  持ち上げ、中心類の上で M124F の全性質（値・準同型性・忠実性・周期性・
  ±-両立）を商レベルで再現する。

  * M126F-1 `centerFun` — 全域代表関数: 中心系の類（第1・2成分が l で
    割り切れる代表）でのみ centerToMu、他では 1。if 条件は Int の
    等式の And（Int.decEq + instDecidableAnd で決定可能、選択公理なし）
  * M126F-2 `centerFun_congr` — well-definedness: thetaRelMod l と両立。
    第1・2成分の合同は int_emod_congr（M124F）で if 条件の同値に、
    第3成分の合同は centerToMu_congr で then 分岐の一致に変換し、
    ite_congr（+ propext）で閉じる
  * M126F-3 `centerToMuMod` — Quot.lift による商関数
    (thetaGrpMod l).carrier → ℤ_p（M124F の目標だった持ち上げ本体）
  * M126F-4 `centerToMuMod_red_center` / `centerToMuMod_red_noncenter` —
    標準類での値: 中心類 red(0,0,z) では centerToMu z、非中心類では 1
  * M126F-5 `centerToMuMod_mul_center`（**本丸**）— **中心類上の
    準同型性**: 商の積（thetaRed の map_mul + theta_center_mul）を
    経由して centerToMuMod(red(0,0,z)·red(0,0,z')) =
    centerToMuMod(red(0,0,z))·centerToMuMod(red(0,0,z'))
  * M126F-6 `centerToMuMod_faithful_center` / `centerToMuMod_period_center`
    — 忠実性の商版: 値が 1 なら中心類そのものが自明類 red(0,0,0) に
    一致（Quot.sound で witness を上げる）、逆向きも成立 = 中心類上の
    核はちょうど自明類
  * M126F-7 `centerToMuMod_neg` / `centerToMuMod_neg_center` — ±-両立の
    商版: ι の mod-l 降下 thetaNegMod（M116F）と可換（thetaNegMod_red
    が rfl なので rfl）、中心類では値不変
  * M126F-8 `ThetaCenterModData` / `thetaCenterModData` /
    `thetaCenterMod_exists` — 総括レコードと witness・Nonempty

  意義: 柱E E-1（#39）。M124F の正直申告（商レベル持ち上げは次層）の
  解消。中心系の類で centerToMu・他で 1 とする全域代表関数が
  thetaRelMod と両立し Quot.lift で降りる。シクロトミック同期が
  商群 = 実際の mod-l テータ群の土俵で完結し、[EtTh] の「テータ環境の
  シクロトームと基礎体のシクロトームの同期」が mono-theta 環境の
  l-捻れ骨格そのものの上の言明になる。

  正直申告: centerToMuMod は thetaGrpMod l 全体からの**大域準同型では
  ない**（Heisenberg コサイクル a·b' が非中心成分で値に混入するため、
  準同型性は中心類上のみ）。centerFun_congr / centerToMuMod は指示の
  仮定 hζl（ζ^l = 1）を必要としなかったため除いた（if 条件・値の比較
  とも余りの合同 int_emod_congr / centerToMu_congr が先に働くため）。
  hζl は準同型性 centerToMuMod_mul_center のみで、hdist（冪の相異性）
  は忠実性 centerToMuMod_faithful_center のみで使用。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.CyclotomicSync

namespace IUT

/-! ## M126F-1: 全域代表関数 -/

/-- **M126F-1: 全域代表関数** — 代表 w = (a,b,c) が中心系
    （l ∣ a かつ l ∣ b、余りで判定）なら centerToMu c、
    他では 1。if 条件は Int の等式の And で決定可能
    （Int.decEq + instDecidableAnd）なので選択公理は不要。 -/
def centerFun (p l : Nat) (ζ : (Zp p).carrier) (w : thetaGrp.carrier) :
    (Zp p).carrier :=
  if w.1 % ((l : Nat) : Int) = 0 ∧ w.2.1 % ((l : Nat) : Int) = 0 then
    centerToMu p l ζ w.2.2
  else zpOne p

/-! ## M126F-2: well-definedness -/

/-- **定理 (M126F-2): 代表関数の well-definedness** — centerFun は
    thetaRelMod l と両立する。第1・2成分の合同は int_emod_congr で
    if 条件の Prop 同値に、第3成分の合同は centerToMu_congr で
    then 分岐の値一致に変換し、ite_congr（+ propext）で両分岐を閉じる
    （else 分岐は zpOne どうしで rfl）。 -/
theorem centerFun_congr (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    {w w' : thetaGrp.carrier} (h : thetaRelMod l w w') :
    centerFun p l ζ w = centerFun p l ζ w' := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb : (0 : Int) < ((l : Nat) : Int) := by omega
  have e1 : w.1 % ((l : Nat) : Int) = w'.1 % ((l : Nat) : Int) :=
    int_emod_congr hb h1
  have e2 : w.2.1 % ((l : Nat) : Int) = w'.2.1 % ((l : Nat) : Int) :=
    int_emod_congr hb h2
  have hcond : (w.1 % ((l : Nat) : Int) = 0 ∧ w.2.1 % ((l : Nat) : Int) = 0)
      ↔ (w'.1 % ((l : Nat) : Int) = 0 ∧ w'.2.1 % ((l : Nat) : Int) = 0) := by
    rw [e1, e2]
  show (if w.1 % ((l : Nat) : Int) = 0 ∧ w.2.1 % ((l : Nat) : Int) = 0 then
      centerToMu p l ζ w.2.2 else zpOne p)
    = (if w'.1 % ((l : Nat) : Int) = 0 ∧ w'.2.1 % ((l : Nat) : Int) = 0 then
      centerToMu p l ζ w'.2.2 else zpOne p)
  exact ite_congr (propext hcond) (fun _ => centerToMu_congr p l hl ζ h3)
    (fun _ => rfl)

/-! ## M126F-3: 商関数（Quot.lift） -/

/-- **M126F-3: 商関数** — centerFun を thetaGrpMod l の carrier
    （= Quot (thetaRelMod l)）に降ろした関数。M124F の正直申告
    「商の carrier からの Quot.lift は本層の範囲外」の持ち上げ本体。 -/
def centerToMuMod (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    (thetaGrpMod l).carrier → (Zp p).carrier :=
  Quot.lift (centerFun p l ζ) (fun _ _ h => centerFun_congr p l hl ζ h)

/-! ## M126F-4: 標準類での値 -/

/-- **定理 (M126F-4a): 中心類での値** — 中心類 red(0,0,z) では
    centerToMuMod は centerToMu z を返す（Quot.lift の計算 +
    if_pos、0 % l = 0 は Int.zero_emod）。 -/
theorem centerToMuMod_red_center (p l : Nat) (hl : 2 ≤ l)
    (ζ : (Zp p).carrier) (z : Int) :
    centerToMuMod p l hl ζ ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier))
      = centerToMu p l ζ z := by
  have h0 : (0 : Int) % ((l : Nat) : Int) = 0 := Int.zero_emod _
  show (if (0 : Int) % ((l : Nat) : Int) = 0 ∧ (0 : Int) % ((l : Nat) : Int) = 0
      then centerToMu p l ζ z else zpOne p) = centerToMu p l ζ z
  exact if_pos ⟨h0, h0⟩

/-- **定理 (M126F-4b): 非中心類での値** — 第1成分または第2成分の余りが
    非零な代表の類では centerToMuMod は 1（if_neg、Or から ¬And）。 -/
theorem centerToMuMod_red_noncenter (p l : Nat) (hl : 2 ≤ l)
    (ζ : (Zp p).carrier) (w : thetaGrp.carrier)
    (h : w.1 % ((l : Nat) : Int) ≠ 0 ∨ w.2.1 % ((l : Nat) : Int) ≠ 0) :
    centerToMuMod p l hl ζ ((thetaRed l).map w) = zpOne p := by
  show (if w.1 % ((l : Nat) : Int) = 0 ∧ w.2.1 % ((l : Nat) : Int) = 0 then
      centerToMu p l ζ w.2.2 else zpOne p) = zpOne p
  refine if_neg ?_
  intro hc
  cases h with
  | inl h1 => exact h1 hc.1
  | inr h2 => exact h2 hc.2

/-! ## M126F-5: 中心類上の準同型性（本丸） -/

/-- **定理 (M126F-5): 中心類上の準同型性（本丸）** — 商群の積で
    centerToMuMod は中心類上準同型: 商の積を thetaRed の map_mul で
    代表の Heisenberg 積の類に戻し（コサイクル項 0·0 消滅 =
    theta_center_mul で代表は (0,0,z+z')）、中心類での値（M126F-4a）
    3 回と centerToMu_add（M124F 本丸1）で閉じる。 -/
theorem centerToMuMod_mul_center (p l : Nat) (hl : 2 ≤ l)
    (ζ : (Zp p).carrier) (hζl : zpPow p ζ l = zpOne p) (z z' : Int) :
    centerToMuMod p l hl ζ ((thetaGrpMod l).mul
        ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier))
        ((thetaRed l).map ((0, 0, z') : thetaGrp.carrier)))
      = zpMul p
          (centerToMuMod p l hl ζ
            ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier)))
          (centerToMuMod p l hl ζ
            ((thetaRed l).map ((0, 0, z') : thetaGrp.carrier))) := by
  rw [← (thetaRed l).map_mul, theta_center_mul]
  rw [centerToMuMod_red_center p l hl ζ (z + z'),
      centerToMuMod_red_center p l hl ζ z,
      centerToMuMod_red_center p l hl ζ z']
  exact centerToMu_add p l hl ζ hζl z z'

/-! ## M126F-6: 忠実性の商版 -/

/-- **定理 (M126F-6a): 忠実性の商版** — 中心類の値が 1 なら類そのものが
    自明類 red(0,0,0)。centerToMu_faithful（M124F 本丸2）で l ∣ z を
    得て、witness を thetaRelMod に上げて Quot.sound。中心類上の核は
    ちょうど自明類であることの片翼。 -/
theorem centerToMuMod_faithful_center (p l : Nat) (hl : 2 ≤ l)
    (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) (z : Int)
    (h : centerToMuMod p l hl ζ
      ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier)) = zpOne p) :
    (thetaRed l).map ((0, 0, z) : thetaGrp.carrier)
      = (thetaRed l).map ((0, 0, 0) : thetaGrp.carrier) := by
  rw [centerToMuMod_red_center p l hl ζ z] at h
  obtain ⟨k, hk⟩ := centerToMu_faithful p l hl ζ hdist z h
  apply Quot.sound
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨k, ?_⟩⟩
  · show (0 : Int) - 0 = ((l : Nat) : Int) * 0
    rw [Int.mul_zero]
    exact Int.sub_self 0
  · show (0 : Int) - 0 = ((l : Nat) : Int) * 0
    rw [Int.mul_zero]
    exact Int.sub_self 0
  · show z - 0 = ((l : Nat) : Int) * k
    rw [Int.sub_zero]
    exact hk

/-- **定理 (M126F-6b): 周期性（忠実性の逆向き）の商版** — 中心類が
    自明類なら値は 1（h を centerToMuMod で送り、中心類での値
    （M126F-4a）2 回と centerToMu_zero で読む）。もう片翼。 -/
theorem centerToMuMod_period_center (p l : Nat) (hl : 2 ≤ l)
    (ζ : (Zp p).carrier) (z : Int)
    (h : (thetaRed l).map ((0, 0, z) : thetaGrp.carrier)
      = (thetaRed l).map ((0, 0, 0) : thetaGrp.carrier)) :
    centerToMuMod p l hl ζ
      ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier)) = zpOne p := by
  have h2 := congrArg (centerToMuMod p l hl ζ) h
  rw [centerToMuMod_red_center p l hl ζ z,
      centerToMuMod_red_center p l hl ζ 0] at h2
  rw [centerToMuMod_red_center p l hl ζ z, h2]
  exact centerToMu_zero p l ζ

/-! ## M126F-7: ±-両立の商版 -/

/-- **定理 (M126F-7a): ±-両立の商版** — centerToMuMod は ι の mod-l
    降下 thetaNegMod（M116F）と可換: 商での ι 作用は代表での ι 作用に
    一致する（thetaNegMod_red が rfl なので Quot.lift の計算で rfl）。 -/
theorem centerToMuMod_neg (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (w : thetaGrp.carrier) :
    centerToMuMod p l hl ζ ((thetaNegMod l).map ((thetaRed l).map w))
      = centerToMuMod p l hl ζ ((thetaRed l).map (thetaNeg.map w)) := rfl

/-- **定理 (M126F-7b): 中心類は ±-不変** — ι は中心を固定する
    （thetaNeg_center）ので、中心類での centerToMuMod の値は
    thetaNegMod で送っても不変。 -/
theorem centerToMuMod_neg_center (p l : Nat) (hl : 2 ≤ l)
    (ζ : (Zp p).carrier) (z : Int) :
    centerToMuMod p l hl ζ ((thetaNegMod l).map
        ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier)))
      = centerToMuMod p l hl ζ
          ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier)) := by
  rw [centerToMuMod_neg p l hl ζ ((0, 0, z) : thetaGrp.carrier),
      thetaNeg_center]

/-! ## M126F-8: 総括レコード -/

/-- **M126F-8a: テータ中心商持ち上げデータ** — 商関数 centerToMuMod の
    中心類での値・非中心類での消滅・中心類上の準同型性・忠実性・
    周期性・±-両立の一括束ね。M124F のシクロトミック同期が商群
    thetaGrpMod l の土俵で完結することの witness 形。 -/
structure ThetaCenterModData (p l : Nat) (hp : IsPrime p) (hl : 2 ≤ l)
    (hdvd : l ∣ p - 1) where
  /-- 中心類での値: centerToMuMod (red (0,0,z)) = centerToMu z。 -/
  lift_red_center : ∀ ζ : (Zp p).carrier, ∀ z : Int,
    centerToMuMod p l hl ζ ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier))
      = centerToMu p l ζ z
  /-- 非中心類での消滅: 第1・2成分の余りが非零なら値 1。 -/
  noncenter : ∀ ζ : (Zp p).carrier, ∀ w : thetaGrp.carrier,
    w.1 % ((l : Nat) : Int) ≠ 0 ∨ w.2.1 % ((l : Nat) : Int) ≠ 0 →
    centerToMuMod p l hl ζ ((thetaRed l).map w) = zpOne p
  /-- 中心類上の準同型性（商群の積で）。 -/
  mul_center : ∀ ζ : (Zp p).carrier, zpPow p ζ l = zpOne p →
    ∀ z z' : Int,
    centerToMuMod p l hl ζ ((thetaGrpMod l).mul
        ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier))
        ((thetaRed l).map ((0, 0, z') : thetaGrp.carrier)))
      = zpMul p
          (centerToMuMod p l hl ζ
            ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier)))
          (centerToMuMod p l hl ζ
            ((thetaRed l).map ((0, 0, z') : thetaGrp.carrier)))
  /-- 忠実性: 中心類の値が 1 なら類は自明類 red(0,0,0)。 -/
  faithful_center : ∀ ζ : (Zp p).carrier,
    (∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) →
    ∀ z : Int,
    centerToMuMod p l hl ζ
      ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier)) = zpOne p →
    (thetaRed l).map ((0, 0, z) : thetaGrp.carrier)
      = (thetaRed l).map ((0, 0, 0) : thetaGrp.carrier)
  /-- 周期性: 中心類が自明類なら値 1。 -/
  period_center : ∀ ζ : (Zp p).carrier, ∀ z : Int,
    (thetaRed l).map ((0, 0, z) : thetaGrp.carrier)
      = (thetaRed l).map ((0, 0, 0) : thetaGrp.carrier) →
    centerToMuMod p l hl ζ
      ((thetaRed l).map ((0, 0, z) : thetaGrp.carrier)) = zpOne p
  /-- ±-両立: thetaNegMod と可換（代表での ι 作用に一致）。 -/
  neg_invariant : ∀ ζ : (Zp p).carrier, ∀ w : thetaGrp.carrier,
    centerToMuMod p l hl ζ ((thetaNegMod l).map ((thetaRed l).map w))
      = centerToMuMod p l hl ζ ((thetaRed l).map (thetaNeg.map w))

/-- **M126F-8b: witness 本体** — 全フィールドが既証明の純レコード。 -/
def thetaCenterModData (p l : Nat) (hp : IsPrime p) (hl : 2 ≤ l)
    (hdvd : l ∣ p - 1) : ThetaCenterModData p l hp hl hdvd where
  lift_red_center := fun ζ z => centerToMuMod_red_center p l hl ζ z
  noncenter := fun ζ w h => centerToMuMod_red_noncenter p l hl ζ w h
  mul_center := fun ζ hζl z z' =>
    centerToMuMod_mul_center p l hl ζ hζl z z'
  faithful_center := fun ζ hdist z h =>
    centerToMuMod_faithful_center p l hl ζ hdist z h
  period_center := fun ζ z h => centerToMuMod_period_center p l hl ζ z h
  neg_invariant := fun ζ w => centerToMuMod_neg p l hl ζ w

/-- **定理 (M126F-8c): テータ中心商持ち上げデータの存在（M126F 見出し）**。 -/
theorem thetaCenterMod_exists (p l : Nat) (hp : IsPrime p) (hl : 2 ≤ l)
    (hdvd : l ∣ p - 1) : Nonempty (ThetaCenterModData p l hp hl hdvd) :=
  ⟨thetaCenterModData p l hp hl hdvd⟩

end IUT
