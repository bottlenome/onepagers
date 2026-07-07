/-
  IUT/ThetaValueOrbitBridge.lean — M403F [実／本物／柱E]
  complete_pct 影響: 柱E で、M368F テータ・ガロア軌道 `galThValCyc`/`tgoOrbitPoint`
    （μ_l 側・抽象円分影の指数 Nat j*j）と、M398F/M318F 具体テータ値
    `thLtorExp`/`thLtorValue`（Laurent 環側・具体単項式の Int 指数 j*j）が、
    **同一の自然数 j² を Int/Nat 往復キャストの下で共有する**ことを本物の等式
    `tvob_orbit_exponent` に closes、両モデルの Galois 置換（`tgo_galois_permutes_label`）
    も同じ j² 上で機械検証する。
  正直な限定: 本層は μ_l モデル（M368F、抽象巡回群 CycMuGroup）と Laurent 環モデル
    （M398F/M318F、具体単項式）という**独立に構成された二つの実対象**が同一の自然数
    j*j を index として共有することを Int/Nat キャストの往復で確認するに留まる。
    両モデルの間の本物の環準同型・完全な解析的エタールテータ関数値・tempered π₁^ét
    による軌道の実現は M368F/M373F/M398F と同様に外部仮説として継承し、本層は一切
    導出しない（正直な限定は消去・弱化しない）。

  ## 内容（tier-S・実ブリッジ、M368F（μ_l 側ガロア軌道）↔ M398F/M318F（Laurent 環側
  具体テータ値）の直接連結）

  M368F は l-捻れ点ラベル j∈{0,…,l−1} に対し、円分影 `galThValCyc M j = ζ^{j*j}`
  （μ_l 側、Nat 指数 j*j 直書き）を基点として軌道点 `tgoOrbitPoint M Θ j` を構成し、
  G_K が円分影を mod M.n 還元形で置換すること（`tgo_galois_permutes_label`）を確立
  した。一方 M398F/M318F は、同じラベル j に対する**具体テータ値**
  `thLtorValue R (j:Int) = uMonHom R (thLtorExp (j:Int))`（Laurent 環側、Int 指数
  `thLtorExp (j:Int) = j*j`）を確立し、M398F `tvtb_exp_cast` でこの Int 指数が Nat
  平方 `(j*j:Nat)` のキャストであることを示した。しかし **この二つの指数（μ_l 側の
  Nat j*j と Laurent 環側の Int 指数の toNat）が同一の自然数であること自体は、
  これまで一度も定理として結ばれていなかった**。本層はその隙間を埋める:

  * M403F-1 `tvob_exp_toNat` — M398F の Int 指数 `thLtorExp (j:Int)` の `.toNat` が、
    ちょうど M368F の円分影に直書きされている Nat 指数 `j*j` に一致する
    （`tvtb_exp_cast` と `Int.toNat_natCast` の合成）。
  * M403F-2 本丸 capstone `tvob_orbit_exponent` — M368F の円分影
    `galThValCyc M j` が、M398F/M318F の具体指数の toNat 版 `(thLtorExp (j:Int)).toNat`
    で書き直せること。μ_l 側の軌道の指数と Laurent 環側の具体テータ値の指数が
    **同一の自然数 j²** であることの machine-checked な同定。
  * M403F-3 `tvob_orbit_point_exponent` — 軌道点 `tgoOrbitPoint M Θ j`（M368F、
    μ_l-トーサー候補）自体が、この共有指数で書き直せること（M348F `tmtCandidate`
    の定義展開＋M403F-2）。
  * M403F-4 `tvob_value_link` — 具体テータ値 `thLtorValue R (j:Int)`（Laurent 環側）
    が、共有指数の toNat/Int 往復キャストで書き直せること（M398F `thLtor_value_exponent`
    ＋M403F-1）。μ_l 側の軌道点（M403F-3）と Laurent 環側の具体値（M403F-4）が
    **同じ共有指数**の下で書けることを対にする。
  * M403F-5 `tvob_galois_permutes_concrete_exponent` — G_K の作用が M368F の軌道
    円分影を mod M.n 還元形に送るという `tgo_galois_permutes_label` の主張を、
    M398F/M318F の具体指数 `(thLtorExp (j:Int)).toNat` で書き直した形。軌道の
    Galois 置換が、具体テータ値の指数と同じ量の上で起きていることの本物の接続。
  * M403F-6 `ThetaValueOrbitBridgeData` / `thetaValueOrbitBridgeData` / `tvob_exists` —
    上記を一つの witness レコードに束ね、任意の GK・M・ρ・R・Θ・j に対する存在を示す。
  * M403F-7 実例（l=5, j=2（j²=4）・本物の G_ℚ 上、M368F/M398F と同じ具体構成）。

  選択公理不使用（新規 Classical.choice なし；継承分の Quot.sound のみ）。sorry 皆無・
  禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。許可タクティク（cases/obtain/induction/rw/show/refine/exact/apply/
  intro/generalize/funext/omega）のみ使用。共有ファイル（IUT.lean・build.sh・
  dashboard.md・graph 系）は一切変更していない。一般名は `tvob` 接頭辞で衝突回避。
-/
import IUT.ThetaValueTripleBridge
import IUT.ThetaOrbitProduct

namespace IUT

/-! ## M403F-1: Int/Nat 往復キャストの指数一致（μ_l 側 Nat j*j = Laurent 環側 toNat） -/

/-- **定理 (M403F-1: 共有指数の Nat 抽出)** — M398F/M318F の Laurent 環側 Int 指数
    `thLtorExp (j:Int)` の `.toNat` が、M368F の μ_l 側の円分影に直書きされている
    Nat 指数 `j*j` に一致する（`tvtb_exp_cast` で Int 指数を Nat キャストに書き換え、
    `Int.toNat_natCast` で往復を閉じる）。二つの独立モデルが同一の自然数を index に
    持つことの第一歩。 -/
theorem tvob_exp_toNat (j : Nat) : (thLtorExp (j : Int)).toNat = j * j := by
  rw [tvtb_exp_cast, Int.toNat_natCast]

/-! ## M403F-2: 本丸 capstone——μ_l 側の軌道円分影は Laurent 環側の共有指数で書ける -/

/-- **定理 (M403F-2: capstone——軌道の指数とテータ値の指数は同一の自然数 j²)** —
    M368F の円分影 `galThValCyc M j = ζ^{j*j}`（μ_l 側、抽象巡回群 CycMuGroup 上）が、
    M398F/M318F の具体テータ値の Int 指数 `thLtorExp (j:Int)` の `.toNat`（Laurent 環側、
    本物の単項式 u^{j²} の指数）で書き直せる。μ_l 側の軌道の指数構造と Laurent 環側の
    具体テータ値の指数構造が、**独立に構成されたにもかかわらず同一の自然数 j²** で
    貫かれることを machine-checked にする。 -/
theorem tvob_orbit_exponent (M : CycMuGroup) (j : Nat) :
    galThValCyc M j = M.μ.pow M.ζ (thLtorExp (j : Int)).toNat := by
  show M.μ.pow M.ζ (j * j) = M.μ.pow M.ζ (thLtorExp (j : Int)).toNat
  rw [tvob_exp_toNat]

/-! ## M403F-3: 軌道点（μ_l-トーサー候補）も共有指数で書ける -/

/-- **定理 (M403F-3: 軌道点の共有指数への書き換え)** — M368F の軌道点
    `tgoOrbitPoint M Θ j`（μ_l-トーサー候補、M348F `tmtCandidate` の j 番目）が、
    共有指数 `(thLtorExp (j:Int)).toNat` による円分影と基点 Θ の積として書ける
    （`tmtCandidate`/`tgoOrbitPoint` の定義展開＋M403F-2）。 -/
theorem tvob_orbit_point_exponent (M : CycMuGroup) (Θ : M.μ.carrier) (j : Nat) :
    tgoOrbitPoint M Θ j = M.μ.mul (M.μ.pow M.ζ (thLtorExp (j : Int)).toNat) Θ := by
  show M.μ.mul (galThValCyc M j) Θ = M.μ.mul (M.μ.pow M.ζ (thLtorExp (j : Int)).toNat) Θ
  rw [tvob_orbit_exponent]

/-! ## M403F-4: 具体テータ値も共有指数の往復キャストで書ける -/

/-- **定理 (M403F-4: 具体テータ値の共有指数への書き換え)** — M398F/M318F の具体
    テータ値 `thLtorValue R (j:Int)`（Laurent 環側、本物の単項式）が、共有指数
    `(thLtorExp (j:Int)).toNat` を Nat→Int に戻した指数の単項式として書ける
    （`thLtor_value_exponent` で単項式指数を抽出し、`tvtb_exp_cast`・
    `Int.toNat_natCast` で共有指数の往復キャストに書き換える）。M403F-3（μ_l 側）と
    本定理（Laurent 環側）が**同じ共有指数**の下で対になることを示す。 -/
theorem tvob_value_link (R : CRing) (j : Nat) :
    thLtorValue R (j : Int) = uMonHom R (((thLtorExp (j : Int)).toNat : Nat) : Int) := by
  rw [thLtor_value_exponent, tvtb_exp_cast, Int.toNat_natCast]

/-! ## M403F-5: Galois 置換も共有指数の上で起きる -/

/-- **定理 (M403F-5: 軌道の Galois 置換は共有指数の上で起きる)** — M368F
    `tgo_galois_permutes_label`（G_K の作用 σ_g が円分影 ζ^{j*j} を mod M.n 還元形
    ζ^{(χ(g)·j*j) mod M.n} に送る）を、M398F/M318F の共有指数 `(thLtorExp (j:Int)).toNat`
    で書き直した形。μ_l 側の軌道の Galois 置換が、Laurent 環側の具体テータ値の指数と
    **同じ量**の上で起きていることの本物の接続。 -/
theorem tvob_galois_permutes_concrete_exponent (GK : Grp) (M : CycMuGroup)
    (ρ : CycGKAction GK M) (g : GK.carrier) (j : Nat) :
    galThMuAct GK M ρ g (galThValCyc M j)
      = M.μ.pow M.ζ ((cycRigExp GK M ρ g * (thLtorExp (j : Int)).toNat) % M.n) := by
  rw [tvob_exp_toNat]
  exact tgo_galois_permutes_label GK M ρ g j

/-! ## M403F-6: 総括レコード（witness）と存在 -/

/-- **M403F-6a: テータ値・軌道 同一指数ブリッジデータ** — M368F のμ_l 側軌道
    （円分影・軌道点・ノルム安定性・Galois 置換）と M398F/M318F の Laurent 環側具体
    テータ値（具体値・その指数抽出）を、**同一の共有指数 `(thLtorExp (j:Int)).toNat`**
    の下で一括束ねる。主語は本物の抽象巡回群 μ_l（CycMuGroup、toy 代理なし）と本物の
    Laurent 単項式（`thLtorValue`、toy 代理なし）。 -/
structure ThetaValueOrbitBridgeData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (R : CRing) (Θ : M.μ.carrier) (j : Nat) where
  /-- 軌道の円分影は共有指数で書ける。 -/
  orbit_exponent : galThValCyc M j = M.μ.pow M.ζ (thLtorExp (j : Int)).toNat
  /-- 軌道点（μ_l-トーサー候補）も共有指数で書ける。 -/
  orbit_point_exponent :
      tgoOrbitPoint M Θ j = M.μ.mul (M.μ.pow M.ζ (thLtorExp (j : Int)).toNat) Θ
  /-- 具体テータ値も共有指数の往復キャストで書ける。 -/
  value_link : thLtorValue R (j : Int)
      = uMonHom R (((thLtorExp (j : Int)).toNat : Nat) : Int)
  /-- 軌道点は基点 Θ と同じ M.n 乗ノルムを持つ（M368F ノルム安定性、共有指数の下でも
      保たれることの確認）。 -/
  norm_stable : M.μ.pow (tgoOrbitPoint M Θ j) M.n = M.μ.pow Θ M.n
  /-- G_K は軌道の円分影を、共有指数を用いた mod M.n 還元形に置換する。 -/
  galois_permutes_concrete : ∀ g : GK.carrier,
      galThMuAct GK M ρ g (galThValCyc M j)
        = M.μ.pow M.ζ ((cycRigExp GK M ρ g * (thLtorExp (j : Int)).toNat) % M.n)

/-- **M403F-6b: witness 本体** — 各フィールドを M403F-2〜5 の主定理で埋める。 -/
def thetaValueOrbitBridgeData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (R : CRing) (Θ : M.μ.carrier) (j : Nat) : ThetaValueOrbitBridgeData GK M ρ R Θ j where
  orbit_exponent := tvob_orbit_exponent M j
  orbit_point_exponent := tvob_orbit_point_exponent M Θ j
  value_link := tvob_value_link R j
  norm_stable := tgo_norm_stable M Θ j
  galois_permutes_concrete := fun g => tvob_galois_permutes_concrete_exponent GK M ρ g j

/-- **定理 (M403F-6c: テータ値・軌道 同一指数ブリッジデータの存在)** — 任意の G_K・
    μ_l・作用 ρ・係数環 R・基点 Θ・l-捻れ点ラベル j に対し、M368F のμ_l 側軌道構造と
    M398F/M318F の Laurent 環側具体テータ値が、同一の共有指数の下で一括束ねたデータが
    存在する。 -/
theorem tvob_exists (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (R : CRing)
    (Θ : M.μ.carrier) (j : Nat) : Nonempty (ThetaValueOrbitBridgeData GK M ρ R Θ j) :=
  ⟨thetaValueOrbitBridgeData GK M ρ R Θ j⟩

/-! ## M403F-7: 実例（l=5・j=2（j²=4）・本物の G_ℚ 上、M368F/M398F と同じ具体構成） -/

/-- 実例: l=5・j=2（j²=4）のテータ値・軌道 同一指数ブリッジデータが、本物の絶対
    ガロア群 G_ℚ（M315F `algCloAbsGalois algCloTrivialTower`）・μ_5（`cycMuStd 5`）・
    自明作用（M368F `cycTrivialAction`）の下で存在する。 -/
theorem tvob_example_l5 (R : CRing) :
    Nonempty (ThetaValueOrbitBridgeData (algCloAbsGalois algCloTrivialTower)
      (cycMuStd 5 (by omega))
      (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega)))
      R (cycMuStd 5 (by omega)).ζ 2) :=
  tvob_exists (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))) R
    (cycMuStd 5 (by omega)).ζ 2

/-- 実例: j=2 の共有指数は 4（=2*2）——M368F の円分影 `galThValCyc M 2` が
    `(thLtorExp (2:Int)).toNat = 4` を指数とする M.ζ の冪に一致する（M403F-2 の
    数値例、M398F/M318F の具体値側と同じ 4）。 -/
example (M : CycMuGroup) :
    galThValCyc M 2 = M.μ.pow M.ζ (thLtorExp (2 : Int)).toNat :=
  tvob_orbit_exponent M 2

/-- 実例: j=2 の具体テータ値 `thLtorValue R (2:Int)` の指数は、共有指数の toNat/Int
    往復キャストで 4 として書ける（M403F-4 の数値例）。 -/
example (R : CRing) :
    thLtorValue R (2 : Int) = uMonHom R (((thLtorExp (2 : Int)).toNat : Nat) : Int) :=
  tvob_value_link R 2

end IUT
