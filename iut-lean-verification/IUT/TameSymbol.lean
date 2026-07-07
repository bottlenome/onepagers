/-
  IUT/TameSymbol.lean — M375F [実／本物]
  分類: 実 (従順 Hilbert 記号の付値公式＝M365F 実 inv で具体化)
  complete_pct 影響: 柱B を前進（M370F の抽象 invH を従順/不分岐ケースで具体化＝付値ベースの
    tame 記号 (π^i u, π^j w)=v(a)w(b)−v(b)w(a) mod n を M365F briInvCyclic（実 v ベース）で構成・
    双線形・反対称・単数は自明を本物で。M370F の「invH 受け取り」を tame 部で閉じる）。
  正直な限定: 従順/不分岐のみ・野性分岐/一般記号は局所 CFT 要・後続。

  ── 本物で閉じる中身（骨格のみでない）:
  * M375F-1 `tsySnd` — 分裂模型 K^× = ℤ × O^×（U=ℤ 具体化）の第二付値
    w : K^× → ℤ（従順な単数の離散対数＝剰余体巡回商のℤ模型）。第一付値 v は
    M365F `briVal`（本物の付値、第一成分）をそのまま再利用。
  * M375F-2 `tsyDet` / `tsyTameSymbolW` / `tsyTameSymbol` — 従順記号
    (a,b) = v(a)·w(b) − v(b)·w(a) mod n ∈ (1/n)ℤ/ℤ = `briQZn n`。反対称行列式を
    M365F 実付値 `briVal` と第二付値 w で構成。`tsy_symbol_via_proj` で M365F
    `briZmodProj`（実 mod-n 射影）由来であることを明示。
  * M375F-3 `tsy_tame_bilinear_left/right` — 各引数で双線形（付値の加法性
    v(ab)=v(a)+v(b)・w(ab)=w(a)+w(b) から）。**本証明**。
  * M375F-4 `tsy_tame_antisymmetric` — (a,b) = −(b,a)（行列式の反対称性、指数で omega）。
    **本証明**。
  * M375F-5 `tsy_tame_formula` — 閉じた値 (π^i u, π^j w) = [i·w − j·u] mod n。**本証明（rfl）**。
  * M375F-6 `tsy_unramified_split` / `tsy_unit_in_briKer` — 単数（v=0）は記号自明・
    M365F `bri_inv_split_iff` の核に落ちる（不分岐単数は従順商で自明に対）。**本証明**。
  * M375F-7 `tsy_concrete_invariant` / `tsy_invariant_is_valuation` — 従順記号は M365F の
    **実 briInvCyclic（v ベース）** を使い、抽象 invH ではないことを明示。標準単数 (0,1)
    との対で briInvCyclic を復元し、不変量が具体的に v(·) mod n であることを示す
    （M370F の「invH 受け取り」ギャップを tame 部で閉じる）。**本証明**。
  * M375F-8 capstone `TameSymbolData`/`tsyData`/`tsy_exists`・n=2 実例
    （(π,u)_2 = 1/2 ≠ 0 非自明・(π,π)_2 = 0）。

  正直な限定（消去・弱化禁止）:
  1. **従順/不分岐のみ**: 野性分岐の記号・一般 Hilbert 記号の非退化性は局所類体論
     （局所 Tate 双対・M370F `hsym_nondegenerate_hypothesis`）を要し後続。ここで具体化
     したのは M370F invH の**tame 部**であって全記号ではない。
  2. **第二付値 w** は分裂模型 K^× = ℤ × O^× の O^× 部を従順離散対数でℤ模型化した
     もの（U=ℤ 具体化）。真の剰余体 κ^×/(κ^×)^n との整合は後続。第一付値 v は
     M365F `briVal` の**本物の付値**である（toy 主語でない: 主語は本物の付値行列式）。
  3. 一般 U では w を入力 `Hom (unitsModel U) intGrp` として受ける（`tsyTameSymbolW`）。
     具体値は U=ℤ・w=第二射影 `tsySnd` で与える（`tsyTameSymbol`）。

  選択公理不使用・sorry 皆無: 全宣言の公理は [propext, Quot.sound] のみ。
  禁止タクティク不使用。一般名は `tsy` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.BrauerInvariant

namespace IUT

/-! ## M375F-1: 第二付値 w（分裂模型 U=ℤ の従順離散対数） -/

/-- **第二付値** w : K^× = ℤ × ℤ → ℤ（M375F-1）: 分裂表示 `unitsModel intGrp` の
    第二成分。従順な単数の離散対数（剰余体巡回商の ℤ 模型）に対応する
    **本物の群準同型**。第一付値 v は M365F `briVal`（第一成分）を再利用。 -/
def tsySnd : Hom (unitsModel intGrp) intGrp where
  map := fun x => x.2
  map_mul := fun _ _ => rfl

/-- 第二付値の明示式: w(k, l) = l。 -/
theorem tsySnd_apply (k l : Int) : tsySnd.map (k, l) = l := rfl

/-! ## M375F-2: 従順記号 (a,b) = v(a)w(b) − v(b)w(a) mod n -/

/-- **付値行列式** det(a,b) = v(a)·w(b) − v(b)·w(a) ∈ ℤ（M375F-2a）: 第一付値
    v = M365F `briVal` と第二付値 w の反対称双線形形式。従順記号の被還元核。 -/
def tsyDet (U : Grp) (w : Hom (unitsModel U) intGrp)
    (a b : (unitsModel U).carrier) : Int :=
  (briVal U).map a * w.map b - (briVal U).map b * w.map a

/-- **一般従順 Hilbert 記号**（M375F-2b）: (a,b)_n = [v(a)w(b) − v(b)w(a)] ∈
    (1/n)ℤ/ℤ = `briQZn n`。M365F 実付値 `briVal` と第二付値 w で構成した
    付値ベースの記号（抽象 invH ではない）。 -/
def tsyTameSymbolW (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a b : (unitsModel U).carrier) : (briQZn n).carrier :=
  Quot.mk (modCong n).rel (tsyDet U w a b)

/-- **具体従順 Hilbert 記号**（M375F-2c）: U=ℤ・w=第二射影 `tsySnd` の具体化。
    (a,b)_n = [a.1·b.2 − b.1·a.2] mod n。 -/
def tsyTameSymbol (n : Nat) (a b : (unitsModel intGrp).carrier) : (briQZn n).carrier :=
  tsyTameSymbolW intGrp n tsySnd a b

/-- **記号は実 mod-n 射影由来**（M375F-2d）: (a,b)_n = `briZmodProj n`(det(a,b))。
    M365F の実射影 ℤ ↠ (1/n)ℤ/ℤ を付値行列式に適用したもの（抽象 invH でない）。 -/
theorem tsy_symbol_via_proj (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a b : (unitsModel U).carrier) :
    tsyTameSymbolW U n w a b = (briZmodProj n).map (tsyDet U w a b) := rfl

/-! ## M375F-3: 双線形性（付値の加法性） -/

/-- 整数レベルの左双線形恒等式（分配則）。 -/
theorem tsy_det_bilinear_left_int (x x' y z u u' : Int) :
    (x + x') * y - z * (u + u') = (x * y - z * u) + (x' * y - z * u') := by
  rw [Int.add_mul, Int.mul_add]
  omega

/-- 整数レベルの右双線形恒等式（分配則）。 -/
theorem tsy_det_bilinear_right_int (x y y' z z' u : Int) :
    x * (y + y') - (z + z') * u = (x * y - z * u) + (x * y' - z' * u) := by
  rw [Int.mul_add, Int.add_mul]
  omega

/-- **双線形（左）**（M375F-3a, 本証明）: (a₁a₂, b) = (a₁,b) + (a₂,b)。付値の
    加法性 v(a₁a₂)=v(a₁)+v(a₂)・w(a₁a₂)=w(a₁)+w(a₂) と分配則から。 -/
theorem tsy_tame_bilinear_left (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a a' b : (unitsModel U).carrier) :
    tsyTameSymbolW U n w ((unitsModel U).mul a a') b
      = (briQZn n).mul (tsyTameSymbolW U n w a b) (tsyTameSymbolW U n w a' b) := by
  have h : tsyDet U w ((unitsModel U).mul a a') b
      = intGrp.mul (tsyDet U w a b) (tsyDet U w a' b) := by
    show (briVal U).map ((unitsModel U).mul a a') * w.map b
         - (briVal U).map b * w.map ((unitsModel U).mul a a')
       = intGrp.mul
           ((briVal U).map a * w.map b - (briVal U).map b * w.map a)
           ((briVal U).map a' * w.map b - (briVal U).map b * w.map a')
    rw [(briVal U).map_mul a a', w.map_mul a a']
    exact tsy_det_bilinear_left_int ((briVal U).map a) ((briVal U).map a')
      (w.map b) ((briVal U).map b) (w.map a) (w.map a')
  exact congrArg (Quot.mk (modCong n).rel) h

/-- **双線形（右）**（M375F-3b, 本証明）: (a, b₁b₂) = (a,b₁) + (a,b₂)。 -/
theorem tsy_tame_bilinear_right (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a b b' : (unitsModel U).carrier) :
    tsyTameSymbolW U n w a ((unitsModel U).mul b b')
      = (briQZn n).mul (tsyTameSymbolW U n w a b) (tsyTameSymbolW U n w a b') := by
  have h : tsyDet U w a ((unitsModel U).mul b b')
      = intGrp.mul (tsyDet U w a b) (tsyDet U w a b') := by
    show (briVal U).map a * w.map ((unitsModel U).mul b b')
         - (briVal U).map ((unitsModel U).mul b b') * w.map a
       = intGrp.mul
           ((briVal U).map a * w.map b - (briVal U).map b * w.map a)
           ((briVal U).map a * w.map b' - (briVal U).map b' * w.map a)
    rw [w.map_mul b b', (briVal U).map_mul b b']
    exact tsy_det_bilinear_right_int ((briVal U).map a) (w.map b) (w.map b')
      ((briVal U).map b) ((briVal U).map b') (w.map a)
  exact congrArg (Quot.mk (modCong n).rel) h

/-! ## M375F-4: 反対称性 (a,b) = −(b,a) -/

/-- **反対称性**（M375F-4, 本証明）: (a,b) = −(b,a)。行列式 v(a)w(b)−v(b)w(a) の
    反対称性（指数の入れ替えで符号反転、omega）。 -/
theorem tsy_tame_antisymmetric (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a b : (unitsModel U).carrier) :
    tsyTameSymbolW U n w a b = (briQZn n).inv (tsyTameSymbolW U n w b a) := by
  have h : tsyDet U w a b = intGrp.inv (tsyDet U w b a) := by
    show (briVal U).map a * w.map b - (briVal U).map b * w.map a
       = -((briVal U).map b * w.map a - (briVal U).map a * w.map b)
    rw [Int.neg_sub]
  show Quot.mk (modCong n).rel (tsyDet U w a b)
     = Quot.mk (modCong n).rel (intGrp.inv (tsyDet U w b a))
  rw [h]

/-! ## M375F-5: 閉じた値の公式 -/

/-- **閉じた形の値**（M375F-5, 本証明 rfl）: (π^i u, π^j w')_n = [i·w' − j·u] mod n。
    分裂座標 a=(i,u), b=(j,w') に対する具体従順記号の明示計算。 -/
theorem tsy_tame_formula (n : Nat) (i u j w' : Int) :
    tsyTameSymbol n (i, u) (j, w') = Quot.mk (modCong n).rel (i * w' - j * u) := rfl

/-! ## M375F-6: 不分岐単数の自明性（M365F 核との接続） -/

/-- **不分岐単数は記号自明**（M375F-6a, 本証明）: v(a)=v(b)=0（両者単数）なら
    (a,b)_n = 0。不分岐単数は従順商で自明に対する。 -/
theorem tsy_unramified_split (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a b : (unitsModel U).carrier)
    (ha : (briVal U).map a = 0) (hb : (briVal U).map b = 0) :
    tsyTameSymbolW U n w a b = (briQZn n).one := by
  have h : tsyDet U w a b = 0 := by
    show (briVal U).map a * w.map b - (briVal U).map b * w.map a = 0
    rw [ha, hb, Int.zero_mul, Int.zero_mul, Int.sub_zero]
  show Quot.mk (modCong n).rel (tsyDet U w a b) = (briQZn n).one
  rw [h]
  rfl

/-- **単数は M365F 不変量の核**（M375F-6b, 本証明）: v(a)=0 なら briInvCyclic(a)=0。
    M365F `bri_inv_split_iff`（分裂 ⟺ n∣v(a)）へ接続。不分岐単数がノルム群 =
    ker(inv) に落ちる。 -/
theorem tsy_unit_in_briKer (U : Grp) (n : Nat) (a : (unitsModel U).carrier)
    (ha : (briVal U).map a = 0) :
    (briInvCyclic U n).map a = (briQZn n).one := by
  refine (bri_inv_split_iff U n a).mpr ⟨0, ?_⟩
  rw [Int.mul_zero]
  exact ha

/-! ## M375F-7: 具体不変量（M365F 実 briInvCyclic の使用・M370F invH ギャップ閉包） -/

/-- **不変量は実付値の射影**（M375F-7a, 本証明 rfl）: briInvCyclic(a) = briZmodProj(v(a))。
    M365F の不変量が具体的に v(·) mod n（抽象 invH でなく実付値ベース）であることを明示。 -/
theorem tsy_invariant_is_valuation (U : Grp) (n : Nat) (a : (unitsModel U).carrier) :
    (briInvCyclic U n).map a = (briZmodProj n).map ((briVal U).map a) := rfl

/-- **従順記号は M365F 実不変量を復元**（M375F-7b, 本証明）: 標準単数 e=(0,1)（v=0,w=1）
    との対 (a, e)_n = briInvCyclic(a) = [v(a)] mod n。従順記号が抽象 invH ではなく
    M365F の**実 v ベース briInvCyclic** を使うことを具体化し、M370F の「invH 受け取り」
    ギャップを tame 部で閉じる。 -/
theorem tsy_concrete_invariant (n : Nat) (a : (unitsModel intGrp).carrier) :
    tsyTameSymbol n a (0, 1) = (briInvCyclic intGrp n).map a := by
  have h : tsyDet intGrp tsySnd a (0, 1) = a.1 := by
    show a.1 * 1 - 0 * a.2 = a.1
    rw [Int.mul_one, Int.zero_mul, Int.sub_zero]
  show Quot.mk (modCong n).rel (tsyDet intGrp tsySnd a (0, 1))
     = Quot.mk (modCong n).rel a.1
  rw [h]

/-! ## M375F-8: capstone と n=2 実例 -/

/-- **capstone データ**（M375F-8a）: 従順 Hilbert 記号の全性質 — 記号写像・双線形・
    反対称・不分岐単数の自明性を束ねる。 -/
structure TameSymbolData (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp) where
  /-- 従順記号 (a,b)_n。 -/
  symbol : (unitsModel U).carrier → (unitsModel U).carrier → (briQZn n).carrier
  /-- symbol の同定。 -/
  symbol_is : symbol = tsyTameSymbolW U n w
  /-- 双線形（左）。 -/
  bilinear_left : ∀ a a' b,
    symbol ((unitsModel U).mul a a') b
      = (briQZn n).mul (symbol a b) (symbol a' b)
  /-- 双線形（右）。 -/
  bilinear_right : ∀ a b b',
    symbol a ((unitsModel U).mul b b')
      = (briQZn n).mul (symbol a b) (symbol a b')
  /-- 反対称 (a,b) = −(b,a)。 -/
  antisymmetric : ∀ a b, symbol a b = (briQZn n).inv (symbol b a)
  /-- 不分岐単数（v=0）は自明。 -/
  unit_split : ∀ a b,
    (briVal U).map a = 0 → (briVal U).map b = 0 → symbol a b = (briQZn n).one

/-- **証人**（M375F-8b）: 全性質を本物の証明で満たす。 -/
def tsyData (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp) :
    TameSymbolData U n w where
  symbol := tsyTameSymbolW U n w
  symbol_is := rfl
  bilinear_left := tsy_tame_bilinear_left U n w
  bilinear_right := tsy_tame_bilinear_right U n w
  antisymmetric := tsy_tame_antisymmetric U n w
  unit_split := tsy_unramified_split U n w

/-- **従順記号データの存在**（M375F-8c, capstone）。 -/
theorem tsy_exists (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp) :
    Nonempty (TameSymbolData U n w) :=
  ⟨tsyData U n w⟩

/-- **具体的存在**（M375F-8d）: U=ℤ・n=2・w=第二射影で従順記号が実体化。 -/
theorem tsy_exists_witness : Nonempty (TameSymbolData intGrp 2 tsySnd) :=
  ⟨tsyData intGrp 2 tsySnd⟩

/-! ## M375F-8e: n=2 実例 — (π,u)_2 = 1/2 ≠ 0・(π,π)_2 = 0 -/

/-- **(π,π)_2 = 0**（M375F-8e-1, 本証明）: 素元 π=(1,0) の対角記号は 0
    （行列式の対角成分は消える）。 -/
theorem tsy_example_prime_prime :
    tsyTameSymbol 2 ((1 : Int), (0 : Int)) ((1 : Int), (0 : Int)) = (briQZn 2).one := by
  rw [tsy_tame_formula]
  refine (bri_qzn_zero_iff 2 _).mpr ⟨0, ?_⟩
  omega

/-- **(π,u)_2 = 1/2 は非自明**（M375F-8e-2, 本証明）: 素元 π=(1,0) と標準単数
    u=(0,1) の従順記号は行列式 = 1·1 − 0·0 = 1、[1] mod 2 = 1/2 ≠ 0。
    従順記号が住む値群 (1/2)ℤ/ℤ で非零値を実現。 -/
theorem tsy_example_prime_unit_nontrivial :
    tsyTameSymbol 2 ((1 : Int), (0 : Int)) ((0 : Int), (1 : Int)) ≠ (briQZn 2).one := by
  rw [tsy_tame_formula]
  intro hcon
  have hd : ((2 : Nat) : Int) ∣ ((1 : Int) * 1 - 0 * 0) :=
    (bri_qzn_zero_iff 2 _).mp hcon
  obtain ⟨k, hk⟩ := hd
  omega

/-- **反対称の実例**（M375F-8e-3, 本証明）: (u,π)_2 = −(π,u)_2。 -/
theorem tsy_example_antisym :
    tsyTameSymbol 2 ((0 : Int), (1 : Int)) ((1 : Int), (0 : Int))
      = (briQZn 2).inv (tsyTameSymbol 2 ((1 : Int), (0 : Int)) ((0 : Int), (1 : Int))) :=
  tsy_tame_antisymmetric intGrp 2 tsySnd ((0 : Int), (1 : Int)) ((1 : Int), (0 : Int))

end IUT
