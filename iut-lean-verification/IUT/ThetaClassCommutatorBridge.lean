-- M433F ThetaClassCommutatorBridge [実・本物・柱E]
-- complete_pct 影響: 柱E で M384F/M428F のテータ交換子・中心座標の μ_l（Zp）像を支配する
--   指数 j²（M318F thLtorExp）と、M353F のテータ Kummer 類 [Θ]∈H¹(G_K,μ_{2l}) を定める
--   捻り指数 e が、同一の自然数 j² であることを本物の等式で確立し、A 側（テータ交換子の
--   円分座標）と E 側（テータ Kummer コホモロジー類）を単一の共有指数で橋渡しした。
-- 正直な限定: A 側（Zp 上の centerToMu）と E 側（CycMuGroup 上の μ_{2l}）は異なる二つの
--   本物の円分表現であり、本モジュールはそれらを一つの群に同一視するのではなく、両者を
--   支配する共有指数 j² の一致を証明する（同一視自体は後続・外部）。完全な解析的エタール
--   テータ関数・tempered π₁^ét の幾何的実現は引き続き外部（M384F/M353F が既に明示した
--   限定を継承）。

/-
  IUT/ThetaClassCommutatorBridge.lean — M433F [実／本物・柱E]
  分類: 実（既存本物どうしの橋渡し・(a) 昇格）

  M428F (IUT/ThetaCommutatorValueBridge.lean, prefix `tcvb`) は M318F のテータ値指数
  thLtorExp j = j² が、M384F (IUT/TemperedThetaCommutator.lean, prefix `ttc`) の離散
  Heisenberg 群 thetaGrp の対角生成元での交換子の中心座標（シンプレクティック形式の対角
  評価 ω(g_j,h_j)=j·j）に本物で一致すること、さらにその一致が M124F `centerToMu`
  （中心座標を Zp p 内の μ_l に送る同期写像）の像でも保たれること（`tcvb_exp_mu`）を
  証明した。

  M353F (IUT/ThetaKummerClass.lean, prefix `tkc`) は、テータ値 Θ(q,u_j) の Kummer
  コサイクル κ_Θ(σ)=σ(Θ)/Θ が μ_{2l}（M322F `CycMuGroup` の抽象巡回群）に着地し、
  テータ Kummer 指標 g↦κ(g)^e（e=j²、`tkcThetaChar`）から Kummer 類 [Θ]∈H¹(G_K,μ_{2l})
  （`tkcClass`）を本物で構成した。

  本モジュールはこの二つの本物の対象を **共有指数 j²（自然数）で接続する**:

  * A 側: M384F/M428F の交換子中心座標の Zp-円分像 centerToMu p l ζ (thLtorExp j)
    （j:Int、`tcvb_exp_mu` により交換子座標の像に一致）
  * E 側: M353F のテータ Kummer 指標・類を定める捻り指数 e（j:Nat、`tkcThetaChar`/`tkcClass`
    の e 引数）

  両者は**同一の自然数 j²** から生じる（thLtorExp (j:Int) = ((j*j:Nat):Int)、`Int.natCast_mul`
  による Nat/Int 冪二乗のキャスト整合）。本モジュールはこの共有指数を `tccbExp` として明示し、

    tccbExp j = j*j
    (tccbExp j : Int) = thLtorExp (j:Int)                          -- E 側 e = A 側 j²
    (tccbExp j : Int) = ω(g_j,h_j)（M384F/M428F の交換子中心座標）    -- E 側 e = A 側交換子座標

  を本物で証明し、A 側の μ_l（Zp）像（`tcvb_exp_mu` 経由）と E 側の Kummer 指標・類
  （`tkc_galois_theta_link`/`tkc_class_pow_trivial` 経由）が **同じ j² に支配される**
  ことを単一の橋渡し定理 `tccb_commutator_class` に束ねる。

  * M433F-1 `tccb_nat_sq_cast` / `tccb_thLtorExp_natSq` / `tccb_commutator_natSq` —
    Nat 二乗 j·j の Int キャスト整合（M318F thLtorExp・M384F/M428F 交換子座標との一致）
  * M433F-2 `tccbExp` / `tccb_exp_eq_thLtorExp` / `tccb_exp_eq_commutator` — 共有指数の定義
    と両側での特徴付け
  * M433F-3 `tccb_mu_image` — A 側: 共有指数（thLtorExp 経由）の centerToMu 像 = 交換子座標の像
    （`tcvb_exp_mu` の再輸出）
  * M433F-4 `tccb_kummer_char` / `tccb_kummer_class_pow` — E 側: 共有指数を e として
    instantiate したテータ Kummer 指標・類（`tkc_galois_theta_link`/`tkc_class_pow_trivial`
    の共有指数版再輸出）
  * M433F-5 `tccb_commutator_class` — 本橋渡し定理: A 側 μ_l 像の一致と E 側 Kummer
    指標・共有指数の一致を単一の連言に束ねる
  * M433F-6 `ThetaClassCommutatorBridgeData` / `thetaClassCommutatorBridgeData` /
    `tccb_exists` — 総括レコード
  * M433F-7 実例（j=1: 標準生成元交換子の非自明 μ_l 像 ζ と、E 側指数 e=1 の Kummer 指標
    が同じ j²=1 に支配される）

  **正直な限定（消去・弱化禁止）**:
  - A 側の centerToMu は Zp p（p 進整数の冪演算）を住処とし、E 側の tkcThetaChar/tkcClass
    は CycMuGroup（抽象巡回群 μ_{2l}）を住処とする。**この二つの円分表現を本モジュールは
    同一の群として同一視しない** — 主張しているのは「両者を支配する指数 j² が同一の
    自然数である」という共有指数の一致であり、Zp と CycMuGroup 自体の同型（円分指標の
    完全な比較）は本モジュールの範囲外・後続。
  - M384F/M428F 自身が明示する限定（完全な幾何的 tempered π₁^temp の slim 遠アーベル性・
    p 進テータ関数のガロア同変な評価は外部）と M353F 自身が明示する限定（完全なエタール
    テータ類・tempered π₁ 作用は外部仮説・決して導出しない）は、そのまま本モジュールにも
    継承される。本モジュールはこれらを一切解消しない。
  - `tkcClass` の e 引数と thLtorExp の関係は「e := j² を代入すれば一致する」という
    **instantiation による一致**であり、M353F 自体が e を thLtorExp から導出することを
    強制する定理ではない（M353F は e を独立パラメータとして扱う一般的構成）。

  全て選択公理を証明本体で新規導入せず（M428F/M384F/M353F から継承、新規 Classical・
  新規 Classical.choice なし）。サブエージェント新規1本（共有ファイル未変更）。
  一般名は `tccb` 接頭辞で衝突回避（グレップ確認済み・既存コードに `tccb` なし）。
-/
import IUT.ThetaCommutatorValueBridge
import IUT.ThetaKummerClass

namespace IUT

/-! ## M433F-1: Nat 二乗の Int キャスト整合

  自然数 j の二乗 j·j（Nat）を Int にキャストしたものが、M318F のテータ値指数
  thLtorExp (j:Int)（Int 二乗）および M384F/M428F の交換子中心座標 ω(g_j,h_j) に
  一致することを、`Int.natCast_mul` によるキャスト法則で確立する。 -/

/-- **M433F-1a: Nat 積の Int キャスト** — ((j*j:Nat):Int) = (j:Int)*(j:Int)
    （`Int.natCast_mul` の対称形）。E 側 Nat 指数と A 側 Int 座標を結ぶ基礎キャスト。 -/
theorem tccb_nat_sq_cast (j : Nat) :
    ((j * j : Nat) : Int) = (j : Int) * (j : Int) :=
  (Int.natCast_mul j j).symm

/-- **定理 (M433F-1b): thLtorExp の Nat 二乗表示** — M318F のテータ値指数
    thLtorExp (j:Int)（j:Nat をキャストした Int 引数）は ((j*j:Nat):Int) に一致する
    （`thLtorExp_sq` と M433F-1a のキャスト整合）。 -/
theorem tccb_thLtorExp_natSq (j : Nat) :
    thLtorExp (j : Int) = ((j * j : Nat) : Int) := by
  rw [thLtorExp_sq]
  exact tccb_nat_sq_cast j

/-- **定理 (M433F-1c): 交換子中心座標の Nat 二乗表示** — M384F/M428F の対角生成元
    交換子 ω(g_j,h_j)（j:Nat をキャストした Int 引数）は ((j*j:Nat):Int) に一致する
    （`tcvb_omega_diag` と M433F-1a のキャスト整合）。 -/
theorem tccb_commutator_natSq (j : Nat) :
    (thetaGrp.comm (tcvbGenA (j : Int)) (tcvbGenB (j : Int))).2.2 = ((j * j : Nat) : Int) := by
  rw [tcvb_omega_diag]
  exact tccb_nat_sq_cast j

/-! ## M433F-2: 共有指数 tccbExp — A 側・E 側を同じ自然数で支配する -/

/-- **M433F-2a: 共有指数** tccbExp j = j·j（Nat）。M318F のテータ値指数・M384F/M428F の
    交換子中心座標（A 側）と、M353F のテータ Kummer 指標・類の捻り指数 e（E 側）の
    **両方を同時に特徴づける単一の自然数**。 -/
def tccbExp (j : Nat) : Nat := j * j

/-- **定理 (M433F-2b): 共有指数 = thLtorExp（Int キャスト経由）** —
    (tccbExp j : Int) = thLtorExp (j:Int)。E 側の指数がテータ値指数そのものであること。 -/
theorem tccb_exp_eq_thLtorExp (j : Nat) :
    ((tccbExp j : Nat) : Int) = thLtorExp (j : Int) :=
  (tccb_thLtorExp_natSq j).symm

/-- **定理 (M433F-2c): 共有指数 = 交換子中心座標（Int キャスト経由）** —
    (tccbExp j : Int) = ω(g_j,h_j)。A 側の交換子座標がこの共有指数そのものであること。 -/
theorem tccb_exp_eq_commutator (j : Nat) :
    ((tccbExp j : Nat) : Int)
      = (thetaGrp.comm (tcvbGenA (j : Int)) (tcvbGenB (j : Int))).2.2 :=
  (tccb_commutator_natSq j).symm

/-! ## M433F-3: A 側 — 共有指数の centerToMu（Zp）像

  M428F `tcvb_exp_mu` を、テータ値指数 thLtorExp (j:Int) に対する centerToMu 像として
  そのまま特化する: 共有指数を経由した A 側の Zp-円分像が交換子中心座標の像に一致する。 -/

/-- **定理 (M433F-3): A 側の μ_l（Zp）像の一致** — centerToMu p l ζ (thLtorExp (j:Int))
    = centerToMu p l ζ (ω(g_j,h_j))。M428F `tcvb_exp_mu` の j:Nat 特化での再輸出。
    共有指数 tccbExp j が Zp 内の μ_l でどちらの経路（テータ値指数経由・交換子座標経由）
    でも同じ像を持つことを保証する。 -/
theorem tccb_mu_image (p l : Nat) (ζ : (Zp p).carrier) (j : Nat) :
    centerToMu p l ζ (thLtorExp (j : Int))
      = centerToMu p l ζ ((thetaGrp.comm (tcvbGenA (j : Int)) (tcvbGenB (j : Int))).2.2) :=
  tcvb_exp_mu p l ζ (j : Int)

/-! ## M433F-4: E 側 — 共有指数を e として instantiate したテータ Kummer 指標・類

  M353F `tkcThetaChar`/`tkcClass` を共有指数 tccbExp j = j·j で instantiate し、
  M353F の本物の定理（1-コサイクル性・μ_{2l} 着地・2l 乗自明性）をそのまま継承する。 -/

/-- **定理 (M433F-4a): E 側のテータ Kummer 指標 = 共有指数での galThTorTwist** —
    (tkcThetaChar M κ (tccbExp j)).map g = κ(g)^{tccbExp j}。M353F `tkc_galois_theta_link`
    の共有指数版再輸出。テータ Kummer 類 [Θ] を生む指標が、A 側と同じ j² で評価される
    ことを明示する。 -/
theorem tccb_kummer_char {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (j : Nat)
    (g : GK.carrier) :
    (tkcThetaChar M κ (tccbExp j)).map g = galThTorTwist GK M κ g (tccbExp j) :=
  tkc_galois_theta_link M κ (tccbExp j) g

/-- **定理 (M433F-4b): E 側の Kummer 類の 2l 乗は自明（共有指数版）** —
    [Θ]^{2l}=0∈H¹(μ_{2l})、e=tccbExp j での instantiate。M353F `tkc_class_pow_trivial`
    の共有指数版再輸出。共有指数 j² で作った Kummer 類が μ_{2l} コホモロジーの中で
    本物に 2l-捻れであることを保つ。 -/
theorem tccb_kummer_class_pow {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (j : Nat) :
    (galH1Group (galH1TrivialModule GK M.μ M.comm)).pow (tkcClass M κ (tccbExp j)) M.n
      = (galH1Group (galH1TrivialModule GK M.μ M.comm)).one :=
  tkc_class_pow_trivial M κ (tccbExp j)

/-! ## M433F-5: 本橋渡し定理 — 共有指数による A 側・E 側の接続 -/

/-- **定理 (M433F-5: 本橋渡し) tccb_commutator_class** — テータ交換子（M384F/M428F、
    A 側・Zp 円分）と テータ Kummer 類 [Θ]（M353F、E 側・CycMuGroup 円分 μ_{2l}）が、
    **同一の共有指数 tccbExp j = j²** に支配されることを単一の連言で束ねる:
    (1) A 側: centerToMu 経由のテータ値指数の像 = 交換子中心座標の像（`tcvb_exp_mu` 継承）、
    (2) E 側: テータ Kummer 指標が共有指数 tccbExp j での galThTorTwist に一致
    （`tkc_galois_theta_link` 継承）、
    (3)(4) 共有指数 tccbExp j が thLtorExp (j:Int) にも交換子中心座標 ω(g_j,h_j) にも
    Int キャストで一致する（M433F-1/2）。
    E 側の量（テータ Kummer コホモロジー類の捻り指数）と A 側の量（テータ群の非可換
    交換子構造の中心座標が Zp 円分に落ちる先）を、単一の自然数 j² で接続する、
    本物どうしの橋。 -/
theorem tccb_commutator_class (p l : Nat) (ζ : (Zp p).carrier)
    {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (j : Nat) (g : GK.carrier) :
    centerToMu p l ζ (thLtorExp (j : Int))
        = centerToMu p l ζ ((thetaGrp.comm (tcvbGenA (j : Int)) (tcvbGenB (j : Int))).2.2)
      ∧ (tkcThetaChar M κ (tccbExp j)).map g = galThTorTwist GK M κ g (tccbExp j)
      ∧ ((tccbExp j : Nat) : Int) = thLtorExp (j : Int)
      ∧ ((tccbExp j : Nat) : Int)
          = (thetaGrp.comm (tcvbGenA (j : Int)) (tcvbGenB (j : Int))).2.2 :=
  ⟨tccb_mu_image p l ζ j, tccb_kummer_char M κ j g,
    tccb_exp_eq_thLtorExp j, tccb_exp_eq_commutator j⟩

/-! ## M433F-6: 総括レコード -/

/-- **M433F-6a: テータ類・交換子橋渡しデータ** — A 側の μ_l（Zp）像の一致・E 側の
    Kummer 指標の共有指数特徴づけ・共有指数と thLtorExp/交換子座標との Int キャスト
    一致を一括束ねる。主語はすべて既存の本物（thetaGrp, thLtorExp, centerToMu,
    tkcThetaChar, tkcClass）——toy 主語・新規外部仮説なし。 -/
structure ThetaClassCommutatorBridgeData (p l : Nat) (ζ : (Zp p).carrier)
    {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) where
  /-- A 側: centerToMu 経由のテータ値指数の像 = 交換子中心座標の像。 -/
  mu_image : ∀ j : Nat,
    centerToMu p l ζ (thLtorExp (j : Int))
      = centerToMu p l ζ ((thetaGrp.comm (tcvbGenA (j : Int)) (tcvbGenB (j : Int))).2.2)
  /-- E 側: テータ Kummer 指標は共有指数での galThTorTwist。 -/
  kummer_char : ∀ (j : Nat) (g : GK.carrier),
    (tkcThetaChar M κ (tccbExp j)).map g = galThTorTwist GK M κ g (tccbExp j)
  /-- E 側: Kummer 類の 2l 乗は自明（共有指数版）。 -/
  kummer_class_pow : ∀ j : Nat,
    (galH1Group (galH1TrivialModule GK M.μ M.comm)).pow (tkcClass M κ (tccbExp j)) M.n
      = (galH1Group (galH1TrivialModule GK M.μ M.comm)).one
  /-- 共有指数 = thLtorExp（Int キャスト）。 -/
  exp_eq_thLtorExp : ∀ j : Nat, ((tccbExp j : Nat) : Int) = thLtorExp (j : Int)
  /-- 共有指数 = 交換子中心座標（Int キャスト）。 -/
  exp_eq_commutator : ∀ j : Nat,
    ((tccbExp j : Nat) : Int)
      = (thetaGrp.comm (tcvbGenA (j : Int)) (tcvbGenB (j : Int))).2.2

/-- **M433F-6b: witness 本体** — 全フィールドを M433F-1〜4 の本物の証明で埋める
    （外部仮説ゼロ・完全証明）。 -/
def thetaClassCommutatorBridgeData (p l : Nat) (ζ : (Zp p).carrier)
    {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) :
    ThetaClassCommutatorBridgeData p l ζ M κ where
  mu_image := tccb_mu_image p l ζ
  kummer_char := tccb_kummer_char M κ
  kummer_class_pow := tccb_kummer_class_pow M κ
  exp_eq_thLtorExp := tccb_exp_eq_thLtorExp
  exp_eq_commutator := tccb_exp_eq_commutator

/-- **定理 (M433F-6c): テータ類・交換子橋渡しデータの存在（M433F 見出し）** —
    任意の p, l・任意の μ_l 候補 ζ・任意の G_K・μ_{2l} 候補 M・Kummer 捻り指標 κ に対し、
    M384F/M428F のテータ交換子（A 側）と M353F のテータ Kummer 類（E 側）を共有指数 j² で
    接続する橋渡しデータが**外部仮説なしで**存在する（完全証明）。 -/
theorem tccb_exists (p l : Nat) (ζ : (Zp p).carrier)
    {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) :
    Nonempty (ThetaClassCommutatorBridgeData p l ζ M κ) :=
  ⟨thetaClassCommutatorBridgeData p l ζ M κ⟩

/-! ## M433F-7: 実例 -/

/-- 実例: 共有指数 tccbExp 3 = 9 = thLtorExp 3 = 交換子座標 ω(g_3,h_3)。 -/
example : ((tccbExp 3 : Nat) : Int) = thLtorExp (3 : Int) := tccb_exp_eq_thLtorExp 3

/-- 実例: j=1 の共有指数 tccbExp 1 = 1。標準生成元交換子 [(1,0,0),(0,1,0)] の
    centerToMu 像（M384F `ttc_commutator_mu`、非自明 = ζ）と、共有指数 1 での
    A 側像（`tccb_mu_image`）が同じテータ値指数 thLtorExp 1 = 1 に支配されることを示す。 -/
example (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    centerToMu p l ζ (thLtorExp (((1 : Nat) : Int))) = zpPow p ζ 1 := by
  rw [tccb_mu_image p l ζ 1]
  exact ttc_commutator_mu p l hl ζ

/-- 実例: l=5・e=tccbExp 2=4 での E 側テータ Kummer 類の 10 乗が H¹(μ_{10}) で自明
    （M353F-9 と同じ e=4=2² を、共有指数として再確認）。 -/
example (GK : Grp) (κ : Hom GK (cycMuStd 10 (by omega)).μ) :
    (galH1Group (galH1TrivialModule GK (cycMuStd 10 (by omega)).μ
        (cycMuStd 10 (by omega)).comm)).pow (tkcClass (cycMuStd 10 (by omega)) κ (tccbExp 2))
        (cycMuStd 10 (by omega)).n
      = (galH1Group (galH1TrivialModule GK (cycMuStd 10 (by omega)).μ
          (cycMuStd 10 (by omega)).comm)).one :=
  tccb_kummer_class_pow (cycMuStd 10 (by omega)) κ 2

/-- 実例: 共有指数 tccbExp j が交換子中心座標にちょうど一致する具体例 j=4:
    tccbExp 4 = 16 = ω(g_4,h_4)。 -/
example :
    ((tccbExp 4 : Nat) : Int)
      = (thetaGrp.comm (tcvbGenA (4 : Int)) (tcvbGenB (4 : Int))).2.2 :=
  tccb_exp_eq_commutator 4

end IUT
