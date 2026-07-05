/-
  IUT/IndActionFull.lean — M259F（Dβ-5 完遂: (Ind1)×(Ind2)×(Ind3)
  の完全同時作用 FullIndAction）

  D-β 詳細化ラウンド（軸1 = 模型忠実化）の続き。M254F
  `IUT/IndActionLabel.lean` は (Ind1) ラベル置換（`swapDiv`・`degZ_swap`）・
  (Ind2) 単数（重み0座標のずらし）・(Ind3) 上方包含膨張
  （`upperExpandAction`）を QDiv に作用させたが、**同時作用は
  (Ind1)×(Ind2) まで**であり、M254F の正直申告に

    「(Ind3) 膨張を同じ器に合流させる完全な (Ind1)×(Ind2)×(Ind3)
     同時作用（等号制約と下界制約の統合）は次段」

  と明記されていた。本モジュールはその**次段**として、三つの不定性を
  **単一の作用構造 `FullIndAction`** に合流させ、**(Ind1)×(Ind2)×(Ind3)
  の完全同時作用**を機械検証する。

  ## 核心（何を honest に実装したか）

  ### 三方向を一つの器に統合した混合次数挙動

  M254F が難所として明示した「**等号制約**（Ind1/Ind2 は degZ 不変）と
  **下界制約**（Ind3 は degZ 単調増加のみ）の統合」を、軌道 index
  `Bool × Bool × Bool`（第一 = (Ind1) 置換・第二 = (Ind2) 単数・
  第三 = (Ind3) 膨張）の上で表現する。

  * `FullIndAction w l`（構造）: 三つの不定性が **同時に** 像 `image` に
    軌道を与える器。`usesExpand`（(Ind3) 成分が発動しているかの標識）と、
    次数の**混合**挙動を課す二本柱の証明フィールドを持つ:
      - `deg_image_flat` — (Ind3) を切った切片（`usesExpand i = false`）では
        degZ を**厳密に保つ**（(Ind1)×(Ind2) の等号制約）。
      - `deg_image_lower` — 全軌道で基点次数 `degZ (gaussDiv l)` を
        **下界として**保つ（(Ind3) の単調増加・下界制約）。
    さらに `hull`（全 8 像を点毎に包含する上界包）と `image_le_hull`。
  * `fullIndAction` — 具体 witness。(Ind1) は**正の等重み座標** a, b
    （`w a = w b`、M254F 強形 `degZ_swap` を再利用）、(Ind2) は重み0座標 k₀
    （`w k₀ = 0`）、(Ind3) は座標 k₁ を +m 膨張。像は 8 点軌道で三方向に
    動き、hull が `labelHull`（置換被覆）＋ 単数 ＋ 膨張ですべてを覆う。
  * `fullImg_deg` — **混合次数の厳密式**:
    `degZ (image (s,u,t)) = degZ (gaussDiv l) + expandDeg t`。
    (Ind1)(Ind2) 成分 s,u は degZ に効かず（等号）、(Ind3) 成分 t だけが
    `w k₁·m ≥ 0` を上乗せする（下界保持の膨張スラック）。
  * `fullOrbit_ind1` / `fullOrbit_ind2` / `fullOrbit_ind3` — 三方向
    **それぞれ**が基点像を真に動かす（非定数軌道）。座標 1（置換）・
    座標 k₀（単数）・座標 k₁（膨張）で重複度が食い違う。
  * `full_indeterminacies_act` / `fullIndActionFull_wellDefined` — capstone。
    三方向同時の非定数軌道 ＋ (Ind1)×(Ind2) 切片の degZ 等号 ＋ 全軌道の
    degZ 下界を一つに束ねる。M254F の (Ind1)×(Ind2) からの完遂。

  ## 正直な限定（どこまで統合したか・crux は範囲外）

  * **hull は等次数ではない**。(Ind3) 膨張が次数を真に増やすため、全 8 像を
    覆う共通 hull の degZ は基点より大きく（下界のみ保持）、M241F の
    **等次数 hull を要求する `IndAction`**（`deg_hull` フィールド）へは
    合流できない。等次数 hull への居住は degZ 不変な (Ind1)×(Ind2) 切片
    （M254F `labelIndAction` の重み0置換）に限られ、そこは M254F 既済。
    本モジュールの前進は「三方向を一つの器に載せ、混合次数（等号＋下界）を
    証明したこと」であり、膨張込みの等次数 hull は**原理的に存在しない**
    （M254F `padding_necessary` の因子レベルの影）。
  * **crux `q_realized` は依然として外部仮説**（M238F/M241F/M254F と同じ）。
    crux の単一 Prop 化・鏡像定理・実データ証明は本モジュールでは構成しない。
    ここで示したのは「三つの不定性が像を同時に動かす軌道を実際に持ち、
    その混合次数挙動（等号＋下界）が成り立つ」ことまでである。
  * ラベル置換は「素点添字の置換」・単数は「重み0方向のずらし」・膨張は
    「片側包含による座標膨張」であり、原論文の procession 自己同型・log-shell
    単数積分・上方両立の**解析的内容は写像しない**（M53F/M55F/M202F の
    正直申告の継続）。
  * 各不定性の軌道は**二値**（発動/非発動）に留め、無限トーソル全体は据えない
    （hull の有界性のための設計判断、M241F と同旨）。
-/
import IUT.IndActionLabel

namespace IUT

/-! ## Part 1: 三方向の像の部品（置換部・単数/膨張の条件付き単一因子） -/

/-- (Ind1) 置換部: 標識 s が真なら座標 a, b を置換、偽なら素の `gaussDiv l`。 -/
def permGauss (s : Bool) (a b l : Nat) : QDiv :=
  match s with
  | false => gaussDiv l
  | true  => swapDiv a b (gaussDiv l)

/-- (Ind2)/(Ind3) の条件付き単一因子: 標識 c が真なら `singleDiv k m`、
    偽なら零因子（作用を選ばない基点側）。 -/
def condSingle (c : Bool) (k m : Nat) : QDiv :=
  match c with
  | false => qzero
  | true  => singleDiv k m

/-- 置換部（偽）の重複度は素の `gaussDiv l`。 -/
theorem permGauss_false_mult (a b l k : Nat) :
    (permGauss false a b l).mult k = (gaussDiv l).mult k := rfl

/-- 置換部（真）の重複度は置換された重複度。 -/
theorem permGauss_true_mult (a b l k : Nat) :
    (permGauss true a b l).mult k = swapMult a b (gaussDiv l).mult k := rfl

/-- 条件付き因子（偽）の重複度は 0。 -/
theorem condSingle_false_mult (k m j : Nat) :
    (condSingle false k m).mult j = 0 := rfl

/-- 条件付き因子（真）の重複度は単一素点。 -/
theorem condSingle_true_mult (k m j : Nat) :
    (condSingle true k m).mult j = (if j = k then m else 0) := rfl

/-! ## Part 2: 三方向を合流させた像と上界包 -/

/-- **(Ind1)×(Ind2)×(Ind3) 同時作用の像**（`Bool × Bool × Bool`）:
    第一成分 s = (Ind1) 置換（a, b）の有無、第二成分 u = (Ind2) 単数
    （重み0座標 k₀ の +1）の有無、第三成分 t = (Ind3) 膨張
    （座標 k₁ の +m）の有無。三方向が同時に基点 `gaussDiv l` を動かす。 -/
def fullImg (a b l k₀ k₁ m : Nat) : Bool × Bool × Bool → QDiv
  | (s, u, t) =>
    qadd (qadd (permGauss s a b l) (condSingle u k₀ 1)) (condSingle t k₁ m)

/-- 像の重複度の展開（置換部 ＋ 単数部 ＋ 膨張部）。 -/
theorem fullImg_mult (a b l k₀ k₁ m : Nat) (s u t : Bool) (k : Nat) :
    (fullImg a b l k₀ k₁ m (s, u, t)).mult k
      = ((permGauss s a b l).mult k + (condSingle u k₀ 1).mult k)
        + (condSingle t k₁ m).mult k := rfl

/-- 全 8 像を点毎に覆う上界包: `labelHull`（置換被覆）＋ 単数 ＋ 膨張。
    (Ind3) 膨張を含むため等次数ではない（下界のみ保持・正直な限定を参照）。 -/
def fullHull (a b l k₀ k₁ m : Nat) : QDiv :=
  qadd (qadd (labelHull a b l) (singleDiv k₀ 1)) (singleDiv k₁ m)

/-! ## Part 3: 混合次数挙動（等号成分 ＋ 膨張成分） -/

/-- (Ind3) 成分の次数寄与: 発動時は `w k₁·m`、非発動時は 0。 -/
def expandDeg (t : Bool) (w : Nat → Nat) (k₁ m : Nat) : Int :=
  match t with
  | false => 0
  | true  => ((w k₁ * m : Nat) : Int)

/-- (Ind3) 寄与は非負（膨張は下界を保つ）。 -/
theorem expandDeg_nonneg (t : Bool) (w : Nat → Nat) (k₁ m : Nat) :
    0 ≤ expandDeg t w k₁ m := by
  cases t with
  | false => exact Int.le_refl 0
  | true => exact Int.natCast_nonneg _

/-- 置換部の次数は等重み `w a = w b` なら不変（(Ind1) の等号制約・
    M254F `degZ_swap` の再利用）。 -/
theorem fullPerm_deg (w : Nat → Nat) (s : Bool) (a b l : Nat)
    (hab : ¬ a = b) (hw : w a = w b) :
    degZ w (permGauss s a b l) = degZ w (gaussDiv l) := by
  cases s with
  | false => rfl
  | true => exact degZ_swap w a b (gaussDiv l) hab hw

/-- 単数部の次数は重み0 `w k₀ = 0` なら 0（(Ind2) の等号制約）。 -/
theorem fullCondUnit_deg (w : Nat → Nat) (u : Bool) (k₀ : Nat) (hw0 : w k₀ = 0) :
    degZ w (condSingle u k₀ 1) = 0 := by
  cases u with
  | false => exact degZ_zero w
  | true =>
    show degZ w (singleDiv k₀ 1) = 0
    rw [degZ_single, hw0]
    show ((0 * 1 : Nat) : Int) = 0
    omega

/-- 膨張部の次数は (Ind3) 寄与 `expandDeg t`（下界制約の供給源）。 -/
theorem fullExpand_deg (w : Nat → Nat) (t : Bool) (k₁ m : Nat) :
    degZ w (condSingle t k₁ m) = expandDeg t w k₁ m := by
  cases t with
  | false => exact degZ_zero w
  | true =>
    show degZ w (singleDiv k₁ m) = ((w k₁ * m : Nat) : Int)
    exact degZ_single w k₁ m

/-- **混合次数の厳密式 (M259F-核心)**: 三方向同時作用の像の degZ は
    基点次数 ＋ (Ind3) 寄与に一致する。(Ind1)(Ind2) 成分 s, u は degZ に
    効かず（等号）、(Ind3) 成分 t だけが `expandDeg t = w k₁·m ≥ 0` を
    上乗せする。等号制約と下界制約の統合そのもの。 -/
theorem fullImg_deg (w : Nat → Nat) (a b l k₀ k₁ m : Nat) (s u t : Bool)
    (hab : ¬ a = b) (hw : w a = w b) (hw0 : w k₀ = 0) :
    degZ w (fullImg a b l k₀ k₁ m (s, u, t))
      = degZ w (gaussDiv l) + expandDeg t w k₁ m := by
  show degZ w (qadd (qadd (permGauss s a b l) (condSingle u k₀ 1))
      (condSingle t k₁ m)) = degZ w (gaussDiv l) + expandDeg t w k₁ m
  rw [degZ_add, degZ_add, fullPerm_deg w s a b l hab hw,
      fullCondUnit_deg w u k₀ hw0, fullExpand_deg w t k₁ m]
  omega

/-! ## Part 4: 完全同時作用の構造と witness -/

/-- **(Ind1)×(Ind2)×(Ind3) 完全同時作用の作用データ（M259F 本構造）**:
    三つの不定性が **同時に** 像 `image` に軌道を与える器。混合次数を
    二本柱で課す:

    * `usesExpand` — (Ind3) 膨張成分が発動しているかの標識。
    * `deg_image_flat` — (Ind3) を切った切片（`usesExpand i = false`）では
      degZ を**厳密に保つ**（(Ind1)×(Ind2) の等号制約）。
    * `deg_image_lower` — 全軌道で基点次数を**下界として**保つ
      （(Ind3) の単調増加・下界制約）。
    * `hull` / `image_le_hull` — 全像を点毎に包含する上界包（等次数でない・
      正直な限定を参照）。 -/
structure FullIndAction (w : Nat → Nat) (l : Nat) where
  /-- 三方向同時の軌道 index。 -/
  Ix : Type
  /-- 基点（どの不定性も選ばない）。 -/
  base : Ix
  /-- 三方向同時の像（非定数）。 -/
  image : Ix → QDiv
  /-- (Ind3) 膨張成分の発動標識。 -/
  usesExpand : Ix → Bool
  /-- 全像を覆う上界包。 -/
  hull : QDiv
  /-- 各像は hull に点毎包含。 -/
  image_le_hull : ∀ i, ∀ k, (image i).mult k ≤ hull.mult k
  /-- (Ind3) を切った切片では degZ を厳密保存（等号制約）。 -/
  deg_image_flat : ∀ i, usesExpand i = false →
    degZ w (image i) = degZ w (gaussDiv l)
  /-- 全軌道で基点次数を下界に保つ（下界制約・単調増加）。 -/
  deg_image_lower : ∀ i, degZ w (gaussDiv l) ≤ degZ w (image i)

/-- **完全同時作用の witness (M259F)**: (Ind1) 正の等重み座標 a, b の置換・
    (Ind2) 重み0座標 k₀ の単数・(Ind3) 座標 k₁ の +m 膨張を、単一の
    `FullIndAction` に合流させる。像は `Bool × Bool × Bool` の 8 点軌道で
    三方向に動き、degZ は (Ind1)(Ind2) 方向で不変・(Ind3) 方向で下界保持。 -/
def fullIndAction (w : Nat → Nat) (a b l k₀ k₁ m : Nat)
    (hab : ¬ a = b) (hw : w a = w b) (hw0 : w k₀ = 0) : FullIndAction w l where
  Ix := Bool × Bool × Bool
  base := (false, false, false)
  image := fullImg a b l k₀ k₁ m
  usesExpand := fun i => i.2.2
  hull := fullHull a b l k₀ k₁ m
  image_le_hull := fun i k => by
    obtain ⟨s, u, t⟩ := i
    have hX : (permGauss s a b l).mult k ≤ (labelHull a b l).mult k := by
      cases s with
      | false =>
        show (gaussDiv l).mult k
            ≤ ((gaussDiv l).mult k + (singleDiv a (b * b)).mult k)
              + (singleDiv b (a * a)).mult k
        exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      | true => exact swap_gauss_le_labelHull a b l hab k
    have hY : (condSingle u k₀ 1).mult k ≤ (singleDiv k₀ 1).mult k := by
      cases u with
      | false => exact Nat.zero_le _
      | true => exact Nat.le_refl _
    have hZ : (condSingle t k₁ m).mult k ≤ (singleDiv k₁ m).mult k := by
      cases t with
      | false => exact Nat.zero_le _
      | true => exact Nat.le_refl _
    show ((permGauss s a b l).mult k + (condSingle u k₀ 1).mult k)
          + (condSingle t k₁ m).mult k
        ≤ ((labelHull a b l).mult k + (singleDiv k₀ 1).mult k)
          + (singleDiv k₁ m).mult k
    omega
  deg_image_flat := fun i hi => by
    obtain ⟨s, u, t⟩ := i
    have ht : t = false := hi
    rw [fullImg_deg w a b l k₀ k₁ m s u t hab hw hw0, ht]
    show degZ w (gaussDiv l) + (0 : Int) = degZ w (gaussDiv l)
    omega
  deg_image_lower := fun i => by
    obtain ⟨s, u, t⟩ := i
    rw [fullImg_deg w a b l k₀ k₁ m s u t hab hw hw0]
    have hnn : 0 ≤ expandDeg t w k₁ m := expandDeg_nonneg t w k₁ m
    omega

/-! ## Part 5: 三方向それぞれの非定数軌道 -/

/-- **(Ind1) 方向の非定数軌道**: l ≥ 2 で座標 1, 2 を置換すると座標 1 の
    重複度が 1²（基点）と 2²（置換）で真に食い違う。単数・膨張成分は
    切ってある（第二・第三 false）ので置換純度で非定数。 -/
theorem fullOrbit_ind1 (w : Nat → Nat) (l k₀ k₁ m : Nat) (hl : 2 ≤ l)
    (hw : w 1 = w 2) (hw0 : w k₀ = 0) :
    (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (true, false, false)
      ≠ (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, false, false) := by
  intro heq
  have hk : (fullImg 1 2 l k₀ k₁ m (true, false, false)).mult 1
          = (fullImg 1 2 l k₀ k₁ m (false, false, false)).mult 1 :=
    congrArg (fun d => d.mult 1) heq
  have hL : (fullImg 1 2 l k₀ k₁ m (true, false, false)).mult 1 = 2 * 2 := by
    show ((swapMult 1 2 (gaussDiv l).mult 1 + 0) + 0) = 2 * 2
    rw [swapMult_left]
    show (((if 2 ≤ l then 2 * 2 else 0) + 0) + 0) = 2 * 2
    rw [if_pos hl]
  have hR : (fullImg 1 2 l k₀ k₁ m (false, false, false)).mult 1 = 1 * 1 := by
    show (((if 1 ≤ l then 1 * 1 else 0) + 0) + 0) = 1 * 1
    rw [if_pos (show (1 : Nat) ≤ l by omega)]
  rw [hL, hR] at hk
  omega

/-- **(Ind2) 方向の非定数軌道**: 座標 k₀ の重複度が基点と単数側で 1 だけ
    食い違う（置換・膨張成分は切ってある）。 -/
theorem fullOrbit_ind2 (w : Nat → Nat) (l k₀ k₁ m : Nat)
    (hab : ¬ (1 : Nat) = 2) (hw : w 1 = w 2) (hw0 : w k₀ = 0) :
    (fullIndAction w 1 2 l k₀ k₁ m hab hw hw0).image (false, true, false)
      ≠ (fullIndAction w 1 2 l k₀ k₁ m hab hw hw0).image (false, false, false) := by
  intro heq
  have hk : (fullImg 1 2 l k₀ k₁ m (false, true, false)).mult k₀
          = (fullImg 1 2 l k₀ k₁ m (false, false, false)).mult k₀ :=
    congrArg (fun d => d.mult k₀) heq
  have hL : (fullImg 1 2 l k₀ k₁ m (false, true, false)).mult k₀
          = (gaussDiv l).mult k₀ + 1 := by
    show (((gaussDiv l).mult k₀ + (if k₀ = k₀ then 1 else 0)) + 0)
        = (gaussDiv l).mult k₀ + 1
    rw [if_pos rfl]
  have hR : (fullImg 1 2 l k₀ k₁ m (false, false, false)).mult k₀
          = (gaussDiv l).mult k₀ := rfl
  rw [hL, hR] at hk
  omega

/-- **(Ind3) 方向の非定数軌道**: m ≥ 1 なら座標 k₁ の重複度が基点と膨張側で
    m だけ食い違う（置換・単数成分は切ってある）。 -/
theorem fullOrbit_ind3 (w : Nat → Nat) (l k₀ k₁ m : Nat) (hm : 1 ≤ m)
    (hab : ¬ (1 : Nat) = 2) (hw : w 1 = w 2) (hw0 : w k₀ = 0) :
    (fullIndAction w 1 2 l k₀ k₁ m hab hw hw0).image (false, false, true)
      ≠ (fullIndAction w 1 2 l k₀ k₁ m hab hw hw0).image (false, false, false) := by
  intro heq
  have hk : (fullImg 1 2 l k₀ k₁ m (false, false, true)).mult k₁
          = (fullImg 1 2 l k₀ k₁ m (false, false, false)).mult k₁ :=
    congrArg (fun d => d.mult k₁) heq
  have hL : (fullImg 1 2 l k₀ k₁ m (false, false, true)).mult k₁
          = (gaussDiv l).mult k₁ + m := by
    show (((gaussDiv l).mult k₁ + 0) + (if k₁ = k₁ then m else 0))
        = (gaussDiv l).mult k₁ + m
    rw [if_pos rfl]
    omega
  have hR : (fullImg 1 2 l k₀ k₁ m (false, false, false)).mult k₁
          = (gaussDiv l).mult k₁ := rfl
  rw [hL, hR] at hk
  omega

/-! ## Part 6: capstone（三方向同時 ＋ 混合次数の総括） -/

/-- **capstone (M259F-a): (Ind1)×(Ind2)×(Ind3) が同時に像を動かす** —
    (1) 三方向 **それぞれ** が基点像を真に動かす（非定数軌道）、
    (2) (Ind3) を切った切片（第三成分 false）では degZ を**厳密保存**
        （(Ind1)×(Ind2) の等号制約）、
    (3) 全軌道で基点次数を**下界として**保つ（(Ind3) 単調増加の下界制約）。
    等号制約と下界制約が一つの器に統合された三方向同時軌道共変性。 -/
theorem full_indeterminacies_act (w : Nat → Nat) (l k₀ k₁ m : Nat)
    (hl : 2 ≤ l) (hw : w 1 = w 2) (hw0 : w k₀ = 0) (hm : 1 ≤ m) :
    ((fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (true, false, false)
        ≠ (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, false, false))
      ∧ ((fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, true, false)
          ≠ (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, false, false))
      ∧ ((fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, false, true)
          ≠ (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, false, false))
      ∧ (∀ s u : Bool,
          degZ w ((fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (s, u, false))
            = degZ w (gaussDiv l))
      ∧ (∀ i, degZ w (gaussDiv l)
          ≤ degZ w ((fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image i)) :=
  ⟨fullOrbit_ind1 w l k₀ k₁ m hl hw hw0,
   fullOrbit_ind2 w l k₀ k₁ m (by omega) hw hw0,
   fullOrbit_ind3 w l k₀ k₁ m hm (by omega) hw hw0,
   fun s u => (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).deg_image_flat (s, u, false) rfl,
   (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).deg_image_lower⟩

/-- **capstone (M259F): (Ind1)×(Ind2)×(Ind3) 完全同時作用の総括** —
    (a) 三つの不定性を単一の器 `FullIndAction` に合流させ、
    (b) 混合次数の**厳密式** `degZ (image (s,u,t)) = degZ (gaussDiv l) + expandDeg t`
        （(Ind1)(Ind2) は等号・(Ind3) は下界の膨張スラック）を証明し、
    (c) 三方向それぞれが基点像を真に動かす（同時非定数軌道）、
    (d) 全像は共通 hull に包含される。
    M254F の (Ind1)×(Ind2) 同時作用から、(Ind3) 膨張を合流させた完全な
    (Ind1)×(Ind2)×(Ind3) 同時作用への前進が機械検証された
    （等次数 hull への居住・crux 単一 Prop 化は原理的/次段の限定として残す）。 -/
theorem fullIndActionFull_wellDefined (w : Nat → Nat) (l k₀ k₁ m : Nat)
    (hl : 2 ≤ l) (hw : w 1 = w 2) (hw0 : w k₀ = 0) (hm : 1 ≤ m) :
    (∀ s u t : Bool,
        degZ w ((fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (s, u, t))
          = degZ w (gaussDiv l) + expandDeg t w k₁ m)
      ∧ ((fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (true, false, false)
          ≠ (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, false, false))
      ∧ ((fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, true, false)
          ≠ (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, false, false))
      ∧ ((fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, false, true)
          ≠ (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image (false, false, false))
      ∧ (∀ i k, ((fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image i).mult k
          ≤ (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).hull.mult k) :=
  ⟨fun s u t => fullImg_deg w 1 2 l k₀ k₁ m s u t (by omega) hw hw0,
   fullOrbit_ind1 w l k₀ k₁ m hl hw hw0,
   fullOrbit_ind2 w l k₀ k₁ m (by omega) hw hw0,
   fullOrbit_ind3 w l k₀ k₁ m hm (by omega) hw hw0,
   (fullIndAction w 1 2 l k₀ k₁ m (by omega) hw hw0).image_le_hull⟩

end IUT
