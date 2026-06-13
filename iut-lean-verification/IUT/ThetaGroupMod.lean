/-
  IUT/ThetaGroupMod.lean — M98F（テータ群 mod l: 柱E 拡張）

  mono-theta 環境の l-捻れ骨格（テータ群 mod l）の形式化。
  [EtTh] の mono-theta 環境は l-捻れ係数のテータ群（Heisenberg mod l）
  を使う。本モジュールはその商群・剛性・標準切断・周期性を形式化する。

  * M98F-1 `thetaRelMod l` — Heisenberg 群 thetaGrp 上の合同関係（mod l）
    と演算両立性（積・逆元）
  * M98F-2 `thetaGrpMod l : Grp` — 商群 thetaGrp / (l-合同) と
    射影準同型 `thetaRed l : Hom thetaGrp (thetaGrpMod l)`
  * M98F-3 `theta_comm_mod` — 商標準生成元の交換子 = 商中心生成元
    ([EtTh] の交換子構造が mod l でも生き残る)
  * M98F-4 `mono_theta_cyclotomic_rigidity_mod` — mod-l cyclotomic rigidity:
    σ が標準生成元を中心ズレを除いて保つなら σ は中心生成元を固定する
  * M98F-5 `thetaSectionMod` / `thetaSectionMod_mul` / `thetaSectionMod_period`
    — 商標準切断と周期 2l（テータ値の l-捻れラベリングの骨格）
  * M98F-6 `ThetaGroupModData` / `thetaGroupModData` / `thetaGroupMod_exists`
    — 総括 witness（l-捻れ骨格の一括束ね）

  **形式化の範囲（正直な申告）**: ここで扱うのは l-捻れ骨格の群論的
  構造のみ。±-構造（実 theta 環境の ±1 作用）、μ_l 係数シクロトームと
  p 進整数環 O の l 乗根 μ_l(O) の間の同型、l⋇ = (l−1)/2 ラベリング、
  ガロア作用付きの tempered 基本群の商としての実現、エタールテータ関数の
  関数等式が Heisenberg 積をリフトする事実は次層。
  全て選択公理不使用。
-/
import IUT.MonoThetaWitness

namespace IUT

/-! ## M98F-1: thetaGrp 上の l-合同関係とその演算両立性 -/

/-- **M98F-1a: l-合同関係** — (a,b,c) ~ (a',b',c') mod l :⟺
    l | a−a', l | b−b', l | c−c'。 -/
def thetaRelMod (l : Nat) (x y : thetaGrp.carrier) : Prop :=
  (l : Int) ∣ x.1 - y.1 ∧
  (l : Int) ∣ x.2.1 - y.2.1 ∧
  (l : Int) ∣ x.2.2 - y.2.2

theorem thetaRelMod_refl (l : Nat) (x : thetaGrp.carrier) :
    thetaRelMod l x x := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩
  all_goals (rw [Int.mul_zero]; exact Int.sub_self _)

theorem thetaRelMod_symm (l : Nat) {x y : thetaGrp.carrier}
    (h : thetaRelMod l x y) : thetaRelMod l y x := by
  obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩, ⟨k3, hk3⟩⟩ := h
  refine ⟨⟨-k1, ?_⟩, ⟨-k2, ?_⟩, ⟨-k3, ?_⟩⟩
  · rw [Int.mul_neg]; omega
  · rw [Int.mul_neg]; omega
  · rw [Int.mul_neg]; omega

theorem thetaRelMod_trans (l : Nat) {x y z : thetaGrp.carrier}
    (h1 : thetaRelMod l x y) (h2 : thetaRelMod l y z) :
    thetaRelMod l x z := by
  obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩, ⟨k3, hk3⟩⟩ := h1
  obtain ⟨⟨m1, hm1⟩, ⟨m2, hm2⟩, ⟨m3, hm3⟩⟩ := h2
  refine ⟨⟨k1 + m1, ?_⟩, ⟨k2 + m2, ?_⟩, ⟨k3 + m3, ?_⟩⟩
  · rw [Int.mul_add]; omega
  · rw [Int.mul_add]; omega
  · rw [Int.mul_add]; omega

/-- **補題: 積の c-成分の差の分解** —
    a·b' − a₂·b₂' = a·(b'−b₂') + (a−a₂)·b₂'。 -/
theorem heisenberg_c_diff (a b' a₂ b₂' : Int) :
    a * b' - a₂ * b₂' = a * (b' - b₂') + (a - a₂) * b₂' := by
  rw [Int.mul_sub, Int.sub_mul]
  generalize a * b' = P
  generalize a * b₂' = Q
  generalize a₂ * b₂' = R
  omega

/-- **M98F-1b: 積の両立性** — l-合同関係は Heisenberg 積を保つ。 -/
theorem thetaRelMod_mul (l : Nat) {x x' y y' : thetaGrp.carrier}
    (hx : thetaRelMod l x x') (hy : thetaRelMod l y y') :
    thetaRelMod l (thetaGrp.mul x y) (thetaGrp.mul x' y') := by
  -- 先にタプルを展開してから証人を取り出す（射影が簡約されるため）
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := x'
  obtain ⟨a2, b2, c2⟩ := y
  obtain ⟨a2', b2', c2'⟩ := y'
  obtain ⟨⟨ka, hka⟩, ⟨kb, hkb⟩, ⟨kc, hkc⟩⟩ := hx
  obtain ⟨⟨ma, hma⟩, ⟨mb, hmb⟩, ⟨mc, hmc⟩⟩ := hy
  -- タプル射影を簡約
  simp only [] at hka hkb hkc hma hmb hmc
  -- thetaGrp.mul の各成分: (a+a2, b+b2, c+c2+a*b2)
  -- a 成分: (a+a2) − (a'+a2') = l*(ka+ma)
  refine ⟨⟨ka + ma, ?_⟩, ⟨kb + mb, ?_⟩, ?_⟩
  · show a + a2 - (a' + a2') = (l : Int) * (ka + ma)
    rw [Int.mul_add]; omega
  · show b + b2 - (b' + b2') = (l : Int) * (kb + mb)
    rw [Int.mul_add]; omega
  -- c 成分: (c+c2+a*b2) − (c'+c2'+a'*b2')
  --       = (c−c') + (c2−c2') + (a*b2 − a'*b2')
  --       = l*kc + l*mc + (a*(b2−b2') + (a−a')*b2')
  --       = l*(kc + mc + a*mb + ka*b2')
  · show (l : Int) ∣ c + c2 + a * b2 - (c' + c2' + a' * b2')
    have h_term1 : a * (b2 - b2') = (l : Int) * (a * mb) := by
      rw [hmb, ← Int.mul_assoc a (l : Int) mb, Int.mul_comm a (l : Int), Int.mul_assoc]
    have h_term2 : (a - a') * b2' = (l : Int) * (ka * b2') := by
      rw [hka, Int.mul_assoc]
    exact ⟨kc + mc + a * mb + ka * b2', by
      have h1 : c + c2 + a * b2 - (c' + c2' + a' * b2')
          = (c - c') + (c2 - c2') + (a * b2 - a' * b2') := by omega
      rw [h1, hkc, hmc, heisenberg_c_diff a b2 a' b2', h_term1, h_term2,
          ← Int.mul_add, ← Int.mul_add, ← Int.mul_add]
      congr 1; omega⟩

/-- **M98F-1c: 逆元の両立性** — l-合同関係は Heisenberg 逆元を保つ。 -/
theorem thetaRelMod_inv (l : Nat) {x y : thetaGrp.carrier}
    (h : thetaRelMod l x y) : thetaRelMod l (thetaGrp.inv x) (thetaGrp.inv y) := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := y
  obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩, ⟨k3, hk3⟩⟩ := h
  simp only [] at hk1 hk2 hk3
  -- inv (a,b,c) = (−a, −b, −c+a*b)
  -- a 成分: (−a) − (−a') = a'−a = l*(−k1)
  refine ⟨⟨-k1, ?_⟩, ⟨-k2, ?_⟩, ?_⟩
  · show -a - -a' = (l : Int) * (-k1)
    rw [Int.mul_neg]; omega
  · show -b - -b' = (l : Int) * (-k2)
    rw [Int.mul_neg]; omega
  -- c 成分: (−c+a*b) − (−c'+a'*b')
  --       = −(c−c') + a*(b−b') + (a−a')*b'
  --       = l*(−k3 + a*k2 + k1*b')
  · show (l : Int) ∣ -c + a * b - (-c' + a' * b')
    have h_term1 : a * (b - b') = (l : Int) * (a * k2) := by
      rw [hk2, ← Int.mul_assoc a (l : Int) k2, Int.mul_comm a (l : Int), Int.mul_assoc]
    have h_term2 : (a - a') * b' = (l : Int) * (k1 * b') := by
      rw [hk1, Int.mul_assoc]
    exact ⟨-k3 + a * k2 + k1 * b', by
      have h1 : -c + a * b - (-c' + a' * b')
          = (c' - c) + (a * b - a' * b') := by omega
      have h2 : c' - c = -((l : Int) * k3) := by omega
      rw [h1, h2, heisenberg_c_diff a b a' b', h_term1, h_term2,
          ← Int.mul_neg, ← Int.mul_add, ← Int.mul_add]
      congr 1; omega⟩

/-! ## M98F-2: 商群 thetaGrpMod l と射影準同型 -/

/-- 商の積（二重 Quot.lift — tateGrp と同じパターン）。 -/
private def thetaModMul (l : Nat) :
    Quot (thetaRelMod l) → Quot (thetaRelMod l) → Quot (thetaRelMod l) :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk (thetaRelMod l) (thetaGrp.mul x y))
      (fun y y' hy =>
        Quot.sound (thetaRelMod_mul l (thetaRelMod_refl l x) hy)))
    (fun x x' hx => by
      funext q
      induction q using Quot.ind
      rename_i y
      exact Quot.sound (thetaRelMod_mul l hx (thetaRelMod_refl l y)))

/-- 商の逆元（単一 Quot.lift）。 -/
private def thetaModInv (l : Nat) :
    Quot (thetaRelMod l) → Quot (thetaRelMod l) :=
  Quot.lift (fun x => Quot.mk (thetaRelMod l) (thetaGrp.inv x))
    (fun x x' hx => Quot.sound (thetaRelMod_inv l hx))

/-- **M98F-2a: テータ群 mod l** — Heisenberg 群の l-合同商群。 -/
def thetaGrpMod (l : Nat) : Grp where
  carrier := Quot (thetaRelMod l)
  mul := thetaModMul l
  one := Quot.mk (thetaRelMod l) thetaGrp.one
  inv := thetaModInv l
  mul_assoc := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    exact congrArg (Quot.mk (thetaRelMod l)) (thetaGrp.mul_assoc x y z)
  one_mul := by
    intro a
    induction a using Quot.ind; rename_i x
    exact congrArg (Quot.mk (thetaRelMod l)) (thetaGrp.one_mul x)
  inv_mul := by
    intro a
    induction a using Quot.ind; rename_i x
    exact congrArg (Quot.mk (thetaRelMod l)) (thetaGrp.inv_mul x)

/-- **M98F-2b: 射影準同型** thetaGrp → thetaGrpMod l。 -/
def thetaRed (l : Nat) : Hom thetaGrp (thetaGrpMod l) where
  map := Quot.mk (thetaRelMod l)
  map_mul := fun _ _ => rfl

/-! ## M98F-3: 商標準生成元の交換子 -/

/-- **定理 (M98F-3): 商での交換子公式** —
    標準生成元の交換子は商中心生成元に一致する。
    交換子構造が mod l でも剛性を保つことの形式的根拠。 -/
theorem theta_comm_mod (l : Nat) :
    (thetaGrpMod l).comm
      ((thetaRed l).map (1, 0, 0))
      ((thetaRed l).map (0, 1, 0))
    = (thetaRed l).map (0, 0, 1) := by
  rw [← Hom.map_grp_comm (thetaRed l)]
  rw [comm_xy]

/-! ## M98F-4: mod-l cyclotomic rigidity -/

/-- **定理 (M98F-4): mod-l cyclotomic rigidity** —
    商テータ群の自己準同型 σ が標準生成元を中心ズレを除いて保つなら
    σ は商中心生成元を厳密に固定する（[EtTh] Cor 2.19 の mod-l 版）。 -/
theorem mono_theta_cyclotomic_rigidity_mod (l : Nat)
    (σ : Hom (thetaGrpMod l) (thetaGrpMod l)) (z₁ z₂ : Int)
    (hx : σ.map ((thetaRed l).map (1, 0, 0)) = (thetaRed l).map (1, 0, z₁))
    (hy : σ.map ((thetaRed l).map (0, 1, 0)) = (thetaRed l).map (0, 1, z₂)) :
    σ.map ((thetaRed l).map (0, 0, 1)) = (thetaRed l).map (0, 0, 1) := by
  -- σ は準同型なので交換子を保つ
  have hcomm : σ.map ((thetaGrpMod l).comm
        ((thetaRed l).map (1, 0, 0))
        ((thetaRed l).map (0, 1, 0)))
      = (thetaGrpMod l).comm
        (σ.map ((thetaRed l).map (1, 0, 0)))
        (σ.map ((thetaRed l).map (0, 1, 0))) :=
    Hom.map_grp_comm σ _ _
  -- 左辺: theta_comm_mod で交換子 = red(0,0,1)
  rw [theta_comm_mod] at hcomm
  -- 右辺: hx, hy で標準生成元の像を代入
  rw [hx, hy] at hcomm
  -- 右辺の交換子: [red(1,0,z₁), red(0,1,z₂)] = red([(1,0,z₁),(0,1,z₂)])
  -- = red((0, 0, 1*1−0*0)) = red(0,0,1)  by theta_comm
  have hcomm_val :
      (thetaGrpMod l).comm ((thetaRed l).map (1, 0, z₁)) ((thetaRed l).map (0, 1, z₂))
      = (thetaRed l).map (0, 0, 1) := by
    rw [← Hom.map_grp_comm (thetaRed l)]
    have hkey : thetaGrp.comm ((1 : Int), 0, z₁) (0, 1, z₂)
        = ((0, 0, 1) : Int × Int × Int) := by
      rw [theta_comm]; rfl
    rw [hkey]
  rw [hcomm_val] at hcomm
  exact hcomm

/-! ## M98F-5: 商標準切断と周期 2l -/

/-- **M98F-5a: 商標準切断** — thetaSection の射影。 -/
def thetaSectionMod (l : Nat) (j : Nat) : (thetaGrpMod l).carrier :=
  (thetaRed l).map (thetaSection j)

/-- **M98F-5b: 商切断は乗法的**（thetaSection_mul + map_mul の一行）。 -/
theorem thetaSectionMod_mul (l : Nat) (i j : Nat) :
    thetaSectionMod l (i + j) =
      (thetaGrpMod l).mul (thetaSectionMod l i) (thetaSectionMod l j) := by
  show (thetaRed l).map (thetaSection (i + j))
    = (thetaGrpMod l).mul ((thetaRed l).map (thetaSection i))
        ((thetaRed l).map (thetaSection j))
  rw [thetaSection_mul i j, (thetaRed l).map_mul]

/-- **補題: tri(2l) = l*(2l+1)**（Nat 版）。
    2 * tri(2l) = (2l)*(2l+1) = 2*(l*(2l+1)) より。 -/
theorem tri_two_l (l : Nat) : tri (2 * l) = l * (2 * l + 1) := by
  apply Nat.eq_of_mul_eq_mul_left (n := 2) (by omega)
  rw [tri_nat, Nat.mul_assoc]

/-- **補題: tri(2l) の Int キャスト** — ((tri(2l):Nat):Int) = l*(2l+1)。 -/
theorem tri_two_l_int (l : Nat) :
    ((tri (2 * l) : Nat) : Int) = (l : Int) * (2 * (l : Int) + 1) := by
  have hcast : ((tri (2 * l) : Nat) : Int) = ((l * (2 * l + 1) : Nat) : Int) :=
    congrArg (Nat.cast) (tri_two_l l)
  rw [hcast, Int.natCast_mul]
  have hcast2 : ((2 * l + 1 : Nat) : Int) = 2 * (l : Int) + 1 := by omega
  rw [hcast2]

/-- **補題: j*(2l) = l*(2j) in Int**（tri_period_dvd の乗法再配置補題）。 -/
theorem j_mul_2l_eq (l j : Nat) :
    (j : Int) * (2 * (l : Int)) = (l : Int) * (2 * (j : Int)) := by
  rw [Int.mul_comm (j : Int) (2 * (l : Int)),
      Int.mul_assoc 2 (l : Int) (j : Int),
      Int.mul_left_comm 2 (l : Int) (j : Int)]

/-- **補題: l | tri(j+2l) − tri j** — 切断の周期性の核心部分。
    差 = tri(2l) + j*(2l) = l*(2l+1) + l*(2j) = l*(2l+1+2j)。 -/
theorem tri_period_dvd (l : Nat) (j : Nat) :
    (l : Int) ∣ ((tri (j + 2 * l) : Nat) : Int) - ((tri j : Nat) : Int) := by
  -- tri(j+2l) = tri j + tri(2l) + j*(2l)  [tri_cocycle]
  have hcoc : ((tri (j + 2 * l) : Nat) : Int)
      = ((tri j : Nat) : Int) + ((tri (2 * l) : Nat) : Int) + (j : Int) * ((2 * l : Nat) : Int) :=
    tri_cocycle j (2 * l)
  have h2l : ((2 * l : Nat) : Int) = 2 * (l : Int) := by omega
  rw [h2l] at hcoc
  rw [tri_two_l_int] at hcoc
  rw [j_mul_2l_eq] at hcoc
  -- hcoc: tri(j+2l) = tri j + l*(2l+1) + l*(2j)
  -- difference = l*(2l+1) + l*(2j) = l*(2l+1+2j)
  have hdistrib : (l : Int) * (2 * (l : Int) + 1) + (l : Int) * (2 * (j : Int))
      = (l : Int) * (2 * (l : Int) + 1 + 2 * (j : Int)) := by
    rw [← Int.mul_add]
  have hdiff : ((tri (j + 2 * l) : Nat) : Int) - ((tri j : Nat) : Int)
      = (l : Int) * (2 * (l : Int) + 1 + 2 * (j : Int)) := by
    rw [hcoc, ← hdistrib]; omega
  exact ⟨2 * (l : Int) + 1 + 2 * (j : Int), hdiff⟩

/-- **定理 (M98F-5c): 商切断の周期 2l** — thetaSectionMod l (j + 2l) = thetaSectionMod l j。
    テータ値の l-捻れラベリングが mod 2l で周期的であることの骨格。 -/
theorem thetaSectionMod_period (l : Nat) (j : Nat) :
    thetaSectionMod l (j + 2 * l) = thetaSectionMod l j := by
  -- goal: Quot.mk (thetaRelMod l) (thetaSection (j+2l)) = Quot.mk _ (thetaSection j)
  apply Quot.sound
  -- goal: thetaRelMod l (thetaSection (j+2l)) (thetaSection j)
  -- thetaSection j = ((j:Nat:Int), (j:Nat:Int), (tri j:Nat:Int))
  -- 各成分の差の整除性
  show (l : Int) ∣ ((j + 2 * l : Nat) : Int) - ((j : Nat) : Int) ∧
       (l : Int) ∣ ((j + 2 * l : Nat) : Int) - ((j : Nat) : Int) ∧
       (l : Int) ∣ ((tri (j + 2 * l) : Nat) : Int) - ((tri j : Nat) : Int)
  -- a = b 成分: (j+2l) − j = 2l = l*2
  refine ⟨⟨2, ?_⟩, ⟨2, ?_⟩, tri_period_dvd l j⟩
  · omega
  · omega

/-! ## M98F-6: 総括 witness -/

/-- **M98F-6a: テータ群 mod l データ** — l-捻れ骨格の一括束ね。
    各フィールドは M98F-2〜M98F-5 の主定理に対応する。 -/
structure ThetaGroupModData (l : Nat) where
  /-- 射影準同型 thetaGrp → thetaGrpMod l。 -/
  red : Hom thetaGrp (thetaGrpMod l)
  /-- 交換子公式: 標準生成元の交換子 = 中心生成元（mod l）。 -/
  comm_id : (thetaGrpMod l).comm (red.map (1, 0, 0)) (red.map (0, 1, 0))
      = red.map (0, 0, 1)
  /-- mod-l cyclotomic rigidity。 -/
  rigidity : ∀ (σ : Hom (thetaGrpMod l) (thetaGrpMod l)) (z₁ z₂ : Int),
      σ.map (red.map (1, 0, 0)) = red.map (1, 0, z₁) →
      σ.map (red.map (0, 1, 0)) = red.map (0, 1, z₂) →
      σ.map (red.map (0, 0, 1)) = red.map (0, 0, 1)
  /-- 標準切断 ℕ → thetaGrpMod l。 -/
  sec : Nat → (thetaGrpMod l).carrier
  /-- 切断は乗法的。 -/
  sec_mul : ∀ i j, sec (i + j) = (thetaGrpMod l).mul (sec i) (sec j)
  /-- 切断は周期 2l。 -/
  sec_period : ∀ j, sec (j + 2 * l) = sec j

/-- **M98F-6b: witness 本体**。 -/
def thetaGroupModData (l : Nat) : ThetaGroupModData l where
  red := thetaRed l
  comm_id := theta_comm_mod l
  rigidity := mono_theta_cyclotomic_rigidity_mod l
  sec := thetaSectionMod l
  sec_mul := thetaSectionMod_mul l
  sec_period := thetaSectionMod_period l

/-- **定理 (M98F-6c): テータ群 mod l witness の存在（M98F 見出し）**。 -/
theorem thetaGroupMod_exists (l : Nat) : Nonempty (ThetaGroupModData l) :=
  ⟨thetaGroupModData l⟩

end IUT
