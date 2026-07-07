-- M438F ThetaCommTemperedBridge [実・橋（(a)昇格に準ずる接続）・柱E/柱A]
-- complete_pct 影響: 0 前進（橋・骨格整備のみ）。M433F の theta-class 交換子（thetaGrp
--   直上の A 側計算・E 側 Kummer 類）が、M424F/M429F が実際に建設した tempered π₁^ét
--   の組み上げ群 tpeGroup・算術 tempered 基本群 atpGroup に埋め込まれてもなお
--   **同一の値**（thLtorExp j・shared exponent tccbExp j・μ_l 像 ζ）を与えることを
--   本物の等式で確認する接続作業であり、新たな本物の数学的対象・新たな complete_pct
--   を生まない（正直な申告）。
-- 正直な限定: 本モジュールは M433F・M424F・M429F の各正直な限定をすべてそのまま継承し、
--   一切解消しない（後述）。

/-
  IUT/ThetaCommTemperedBridge.lean — M438F [実／橋・柱E×柱A]
  分類: 実（橋・既存2本物モジュールの接続。新規の重い証明なし・型を通す組み合わせが主眼）

  既存の実部品:
    * M433F (ThetaClassCommutatorBridge, prefix `tccb`): thetaGrp 直上のテータ値指数
      thLtorExp j（M318F）と Heisenberg 交換子中心座標 ω(g_j,h_j)（M384F/M428F、
      `tcvbGenA`/`tcvbGenB` の対角生成元）を共有指数 tccbExp j = j² で接続し
      （A 側）、M353F のテータ Kummer 類（E 側、`tkcThetaChar`/`tkcClass`）も同じ
      j² で instantiate した。
    * M424F (TemperedPi1Etale, prefix `tpe`): thetaGrp を deck 商 ℤ が捻る半直積
      tpeGroup（本物の tempered π₁^ét の組み上げ群）を建設し、埋め込み ι = `tpeIncl`
      を通じて thetaGrp のテータ交換子構造がそのまま tpeGroup の中心シクロトームに
      着地すること（`tpe_commutator_cyclotome`）・deck×テータ交換子＝ペアリング
      （`tpe_deck_theta_commutator`）・標準生成元交換子の μ_l 像 = ζ
      （`tpe_commutator_mu`）を証明した。
    * M429F (ArithTemperedPi1, prefix `atp`): tpeGroup を円分指標像 ℤ が χ 捻りで
      作用する半直積 atpGroup（算術 tempered 基本群）へ数論化し、合成埋め込み
      `atpInclGeom = atpIncl.comp tpeIncl : thetaGrp ↪ atpGroup` を通じてテータ
      交換子が二段塔でも降下すること（`atp_theta_commutator`）を証明した。

  本モジュールは **M433F の thetaGrp 直上の理論（A 側の指数・E 側の Kummer 類）が、
  M424F/M429F が実際に組み上げた tempered π₁^ét・算術 tempered 基本群の中に
  そのまま埋め込まれても値が変わらないこと** を確認する橋である:

    1. `tpeIncl`/`atpInclGeom` は準同型ゆえ交換子を保つ（`Hom.map_grp_comm`、
       M11/EtaleTheta の一般補題）——thetaGrp のテータ交換子（M433F の主語）を
       tpeGroup・atpGroup へ埋め込んだものは、埋め込み後に**その場で**計算した
       交換子（M424F/M429F の主語）に一致する。
    2. その帰結として、M433F の共有指数 thLtorExp j（＝ tccbExp j の Int 版）が、
       tpeGroup・atpGroup 内部の交換子中心座標としても読める。
    3. M424F の deck×テータ交換子（`tpe_deck_theta_commutator`、対角 n=j の特殊化）
       も同じ thLtorExp j に一致する——theta-theta 型の交換子（M433F/M428F の主語）と
       deck-theta 型の交換子（M424F の主語）が、対角特殊化で**同じ共有指数**に
       支配される。
    4. M433F の μ_l 像 `tccb_mu_image`（A 側、centerToMu 経由）と M424F の
       `tpe_commutator_mu`（標準生成元 j=1 での実測）が、同一の値 zpPow p ζ 1 を
       与える——M433F が thetaGrp 直上で証明した「テータ交換子の μ_l 像 = ζ」が、
       実際に組み上げられた tempered π₁^ét 群 tpeGroup・算術群 atpGroup の中でも
       ζ のまま保たれることの確認。

  * M438F-1 `tctb_commutator_incl` / `tctb_commutator_center` /
    `tctb_thLtorExp_eq_tpe_commutator` — tpeGroup への埋め込み・中心座標の一致・
    thLtorExp との一致
  * M438F-2 `tctb_shared_exp_tpe` — M433F の共有指数 tccbExp（Nat）が tpeGroup の
    交換子中心座標に一致
  * M438F-3 `tctb_deck_theta_shared_exp` — M424F の deck×テータ交換子の対角特殊化
    (n=j) も同じ thLtorExp j に一致（theta-theta 型と deck-theta 型の交換子の
    共有指数での合流）
  * M438F-4 `tctb_bridge_mu_image` / `tctb_mu_agree` — M433F の μ_l 像（A 側）と
    M424F の標準生成元交換子の μ_l 像（`tpe_commutator_mu`）が同一値 zpPow p ζ 1
  * M438F-5 `tctb_commutator_incl_atp` / `tctb_thLtorExp_eq_atp_commutator` /
    `tctb_atp_commutator_mu` — atpGroup（M429F・算術 tempered 基本群）への同じ接続
  * M438F-6 `ThetaCommTemperedBridgeData` / `thetaCommTemperedBridgeData` /
    `tctb_exists` — 総括レコード
  * M438F-7 実例

  **正直な限定（消去・弱化禁止・橋なので新規解消なし）**:
  - 本モジュールは M433F・M428F・M384F の限定（centerToMu と CycMuGroup 上の μ_{2l}
    を同一群として同一視しない・完全な解析的エタールテータ関数は外部）をそのまま
    継承する。
  - 本モジュールは M424F の限定（本組み上げ群 tpeGroup は中心 μ が非自明ゆえ slim
    でない・完全な幾何的 tempered π₁^temp の slim 遠アーベル性は外部・Tate 曲線の
    実被覆空間としての幾何的実現は外部）をそのまま継承する。
  - 本モジュールは M429F の限定（算術商は実 G_K（非可換副有限）ではなくその円分
    指標像のモデル ℤ・full slim 遠アーベル復元は外部）をそのまま継承する。
  - 本モジュール自体は **complete_pct を一切前進させない**——新たな本物の数学的
    対象・新たな実 IUT 構成要素をゼロから建設せず、既存 2 系統（M433F と
    M424F/M429F）が同じ値を計算していることを型で確認するだけである（正直な申告、
    水増しではない）。
  全て選択公理を証明本体で新規導入せず（`tpeIncl.map_grp_comm`/`atpInclGeom.map_grp_comm`
  等、既存の一般補題の適用のみ・新規 Classical・新規 Classical.choice なし）。
  サブエージェント新規1本（共有ファイル未変更）。一般名は `tctb` 接頭辞で衝突回避
  （グレップ確認済み・既存コードに `tctb` なし）。
-/
import IUT.ThetaClassCommutatorBridge
import IUT.ArithTemperedPi1

namespace IUT

/-! ## M438F-1: thetaGrp 交換子の tpeGroup への埋め込みは on the nose で一致

  `tpeIncl : Hom thetaGrp tpeGroup` は準同型ゆえ交換子を保つ（`Hom.map_grp_comm`、
  M11/EtaleTheta の一般補題）。ゆえに M433F/M428F が thetaGrp 直上で計算した
  対角生成元 `tcvbGenA j`/`tcvbGenB j` の交換子は、tpeGroup へ埋め込んだ後に
  **その場で**計算した交換子とちょうど一致する。 -/

/-- **定理 (M438F-1a): 埋め込みと交換子は可換** — ι(thetaGrp.comm (g_j,h_j))
    = tpeGroup.comm (ι g_j, ι h_j)。`tpeIncl.map_grp_comm` の tcvbGenA/tcvbGenB
    特化（新規証明ではなく既存の一般補題の直接適用）。 -/
theorem tctb_commutator_incl (j : Int) :
    tpeIncl.map (thetaGrp.comm (tcvbGenA j) (tcvbGenB j))
      = tpeGroup.comm (tpeIncl.map (tcvbGenA j)) (tpeIncl.map (tcvbGenB j)) :=
  tpeIncl.map_grp_comm (tcvbGenA j) (tcvbGenB j)

/-- **定理 (M438F-1b): 中心座標の一致** — thetaGrp 上の交換子中心座標
    (M433F/M428F の主語) は、tpeGroup へ埋め込んだ後の交換子の中心座標
    （M424F の主語、`.1.2.2`——tpeIncl.map z = (z,0) ゆえ第 1 座標を素通り）に
    一致する。 -/
theorem tctb_commutator_center (j : Int) :
    (thetaGrp.comm (tcvbGenA j) (tcvbGenB j)).2.2
      = (tpeGroup.comm (tpeIncl.map (tcvbGenA j)) (tpeIncl.map (tcvbGenB j))).1.2.2 :=
  congrArg (fun p : tpeGroup.carrier => p.1.2.2) (tctb_commutator_incl j)

/-- **定理 (M438F-1c): thLtorExp = tpeGroup 内の交換子中心座標** — M433F/M428F の
    テータ値指数 thLtorExp j（`tcvb_exp_from_commutator` 経由）が、M424F が実際に
    組み上げた tempered π₁^ét 群 tpeGroup の中の交換子中心座標としても読める。 -/
theorem tctb_thLtorExp_eq_tpe_commutator (j : Int) :
    thLtorExp j
      = (tpeGroup.comm (tpeIncl.map (tcvbGenA j)) (tpeIncl.map (tcvbGenB j))).1.2.2 := by
  rw [tcvb_exp_from_commutator]
  exact tctb_commutator_center j

/-! ## M438F-2: M433F の共有指数 tccbExp が tpeGroup の交換子中心座標に一致 -/

/-- **定理 (M438F-2): 共有指数 tccbExp（Nat）＝ tpeGroup 内の交換子中心座標** —
    M433F の共有指数 tccbExp j = j²（A 側 thLtorExp・E 側 Kummer 捻り指数の両方を
    支配する自然数）が、tpeGroup 内部で埋め込み経由に計算した交換子中心座標にも
    Int キャストで一致する。 -/
theorem tctb_shared_exp_tpe (j : Nat) :
    ((tccbExp j : Nat) : Int)
      = (tpeGroup.comm (tpeIncl.map (tcvbGenA (j : Int)))
          (tpeIncl.map (tcvbGenB (j : Int)))).1.2.2 :=
  (tccb_exp_eq_thLtorExp j).trans (tctb_thLtorExp_eq_tpe_commutator (j : Int))

/-! ## M438F-3: deck×テータ交換子（M424F）の対角特殊化も同じ共有指数に合流

  M424F の `tpe_deck_theta_commutator` は theta-theta 型（M433F/M428F の主語）とは
  異なる deck-theta 型の交換子である。対角特殊化 n=j（deck 元 j とテータ部
  `tcvbGenB j = (0,j,0)` の交換子）を取ると、ちょうど同じ thLtorExp j = j² に
  合流することを示す。 -/

/-- **定理 (M438F-3): deck×テータ交換子の対角特殊化 = thLtorExp j** —
    [s(j), ι(tcvbGenB j)] = ι(0,0,thLtorExp j)。M424F の deck-theta 型交換子
    （本丸その 1）が、対角特殊化で M433F/M428F の theta-theta 型交換子と
    同じ共有指数 j² に合流することの確認。 -/
theorem tctb_deck_theta_shared_exp (j : Int) :
    tpeGroup.comm (tpeSection.map j) (tpeIncl.map (tcvbGenB j))
      = tpeIncl.map ((0, 0, thLtorExp j) : Int × Int × Int) := by
  rw [thLtorExp_sq]
  exact tpe_deck_theta_commutator j 0 j 0

/-! ## M438F-4: μ_l 像の一致 — M433F の A 側と M424F の実測が同一値 -/

/-- **定理 (M438F-4a): μ_l 像の一致（一般 j）** — M433F の `tccb_mu_image`（thetaGrp
    直上・centerToMu 経由の A 側 μ_l 像）と、tpeGroup へ埋め込んだ後に計算した
    交換子中心座標の centerToMu 像が、任意の j で一致する。 -/
theorem tctb_bridge_mu_image (p l : Nat) (ζ : (Zp p).carrier) (j : Nat) :
    centerToMu p l ζ (thLtorExp (j : Int))
      = centerToMu p l ζ
          ((tpeGroup.comm (tpeIncl.map (tcvbGenA (j : Int)))
            (tpeIncl.map (tcvbGenB (j : Int)))).1.2.2) :=
  (tccb_mu_image p l ζ j).trans
    (congrArg (centerToMu p l ζ) (tctb_commutator_center (j : Int)))

/-- **定理 (M438F-4b): 標準生成元での実測一致（本橋渡し）** — M433F/M428F/M384F が
    thetaGrp 直上で証明した「標準生成元交換子の μ_l 像 = ζ」が、M424F が実際に
    組み上げた tempered π₁^ét 群 tpeGroup（`tpe_commutator_mu`）の中でも
    ちょうど同じ値 zpPow p ζ 1 として実現されることの確認。 -/
theorem tctb_mu_agree (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    centerToMu p l ζ (thLtorExp 1) = zpPow p ζ 1 := by
  rw [tctb_thLtorExp_eq_tpe_commutator 1]
  exact tpe_commutator_mu p l hl ζ

/-! ## M438F-5: atpGroup（M429F・算術 tempered 基本群）への同じ接続

  合成埋め込み `atpInclGeom = atpIncl.comp tpeIncl : thetaGrp ↪ atpGroup` も
  準同型ゆえ、同じ議論が二段塔の上段（算術化された tempered 基本群）でも成り立つ。 -/

/-- **定理 (M438F-5a): 埋め込みと交換子は可換（atpGroup 版）** —
    atpInclGeom(thetaGrp.comm (g_j,h_j)) = atpGroup.comm (atpInclGeom g_j, atpInclGeom h_j)。 -/
theorem tctb_commutator_incl_atp (j : Int) :
    atpInclGeom.map (thetaGrp.comm (tcvbGenA j) (tcvbGenB j))
      = atpGroup.comm (atpInclGeom.map (tcvbGenA j)) (atpInclGeom.map (tcvbGenB j)) :=
  atpInclGeom.map_grp_comm (tcvbGenA j) (tcvbGenB j)

/-- **定理 (M438F-5b): thLtorExp = atpGroup 内の交換子中心座標** — atpGroup の台は
    (thetaGrp.carrier × ℤ) × ℤ ゆえ、埋め込み後の中心座標は `.1.1.2.2` で読む
    （atpInclGeom.map z = ((z,0),0) ゆえ第 1・第 2 の deck/算術座標を素通り）。 -/
theorem tctb_thLtorExp_eq_atp_commutator (j : Int) :
    thLtorExp j
      = (atpGroup.comm (atpInclGeom.map (tcvbGenA j))
          (atpInclGeom.map (tcvbGenB j))).1.1.2.2 := by
  rw [tcvb_exp_from_commutator]
  exact congrArg (fun p : atpGroup.carrier => p.1.1.2.2) (tctb_commutator_incl_atp j)

/-- **定理 (M438F-5c): 標準生成元の μ_l 像は atpGroup の中でも ζ のまま**（本橋渡し・
    算術版）— M433F/M428F/M384F の μ_l 像 ζ（`tctb_mu_agree`）が、M429F が数論化した
    算術 tempered 基本群 atpGroup の中でも同じ交換子中心座標として保たれる。 -/
theorem tctb_atp_commutator_mu (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    centerToMu p l ζ
        ((atpGroup.comm (atpInclGeom.map (tcvbGenA 1))
          (atpInclGeom.map (tcvbGenB 1))).1.1.2.2)
      = zpPow p ζ 1 := by
  rw [← tctb_thLtorExp_eq_atp_commutator 1]
  exact tctb_mu_agree p l hl ζ

/-! ## M438F-6: 総括レコード -/

/-- **M438F-6a: テータ交換子・tempered π₁ 橋渡しデータ** — M433F の thetaGrp 直上の
    理論（A 側指数・共有指数 tccbExp）が、M424F/M429F が実際に組み上げた
    tempered π₁^ét（tpeGroup）・算術 tempered 基本群（atpGroup）に埋め込まれても
    値（thLtorExp j・μ_l 像 ζ）が変わらないことを一括束ねる。主語はすべて既存の
    本物（thetaGrp, tpeGroup, atpGroup, thLtorExp, tccbExp, centerToMu）——
    toy 主語・新規外部仮説なし。 -/
structure ThetaCommTemperedBridgeData (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) where
  /-- 埋め込みと交換子は可換（tpeGroup 版）。 -/
  commutator_incl_tpe : ∀ j : Int,
    tpeIncl.map (thetaGrp.comm (tcvbGenA j) (tcvbGenB j))
      = tpeGroup.comm (tpeIncl.map (tcvbGenA j)) (tpeIncl.map (tcvbGenB j))
  /-- thLtorExp j ＝ tpeGroup 内の交換子中心座標。 -/
  thLtorExp_eq_tpe : ∀ j : Int,
    thLtorExp j
      = (tpeGroup.comm (tpeIncl.map (tcvbGenA j)) (tpeIncl.map (tcvbGenB j))).1.2.2
  /-- 共有指数 tccbExp（Nat）＝ tpeGroup 内の交換子中心座標。 -/
  shared_exp_tpe : ∀ j : Nat,
    ((tccbExp j : Nat) : Int)
      = (tpeGroup.comm (tpeIncl.map (tcvbGenA (j : Int)))
          (tpeIncl.map (tcvbGenB (j : Int)))).1.2.2
  /-- deck×テータ交換子の対角特殊化も thLtorExp j に合流。 -/
  deck_theta_shared_exp : ∀ j : Int,
    tpeGroup.comm (tpeSection.map j) (tpeIncl.map (tcvbGenB j))
      = tpeIncl.map ((0, 0, thLtorExp j) : Int × Int × Int)
  /-- μ_l 像の一致（一般 j、A 側 M433F と tpeGroup 埋め込み後）。 -/
  mu_image_agree : ∀ j : Nat,
    centerToMu p l ζ (thLtorExp (j : Int))
      = centerToMu p l ζ
          ((tpeGroup.comm (tpeIncl.map (tcvbGenA (j : Int)))
            (tpeIncl.map (tcvbGenB (j : Int)))).1.2.2)
  /-- 標準生成元の μ_l 像は tpeGroup の中でも ζ のまま。 -/
  standard_mu_value_tpe : centerToMu p l ζ (thLtorExp 1) = zpPow p ζ 1
  /-- 埋め込みと交換子は可換（atpGroup 版）。 -/
  commutator_incl_atp : ∀ j : Int,
    atpInclGeom.map (thetaGrp.comm (tcvbGenA j) (tcvbGenB j))
      = atpGroup.comm (atpInclGeom.map (tcvbGenA j)) (atpInclGeom.map (tcvbGenB j))
  /-- thLtorExp j ＝ atpGroup 内の交換子中心座標。 -/
  thLtorExp_eq_atp : ∀ j : Int,
    thLtorExp j
      = (atpGroup.comm (atpInclGeom.map (tcvbGenA j))
          (atpInclGeom.map (tcvbGenB j))).1.1.2.2
  /-- 標準生成元の μ_l 像は atpGroup の中でも ζ のまま。 -/
  standard_mu_value_atp : centerToMu p l ζ
      ((atpGroup.comm (atpInclGeom.map (tcvbGenA 1))
        (atpInclGeom.map (tcvbGenB 1))).1.1.2.2)
    = zpPow p ζ 1

/-- **M438F-6b: witness 本体** — 全フィールドを M438F-1〜5 の本物の証明で埋める
    （外部仮説ゼロ・完全証明）。 -/
def thetaCommTemperedBridgeData (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    ThetaCommTemperedBridgeData p l hl ζ where
  commutator_incl_tpe := tctb_commutator_incl
  thLtorExp_eq_tpe := tctb_thLtorExp_eq_tpe_commutator
  shared_exp_tpe := tctb_shared_exp_tpe
  deck_theta_shared_exp := tctb_deck_theta_shared_exp
  mu_image_agree := tctb_bridge_mu_image p l ζ
  standard_mu_value_tpe := tctb_mu_agree p l hl ζ
  commutator_incl_atp := tctb_commutator_incl_atp
  thLtorExp_eq_atp := tctb_thLtorExp_eq_atp_commutator
  standard_mu_value_atp := tctb_atp_commutator_mu p l hl ζ

/-- **定理 (M438F-6c): テータ交換子・tempered π₁ 橋渡しデータの存在（M438F 見出し）** —
    任意の p, l（2 ≤ l）・任意の μ_l 候補 ζ に対し、M433F の thetaGrp 直上の理論
    （A 側指数・共有指数・μ_l 像）が M424F/M429F の tempered π₁^ét・算術 tempered
    基本群に埋め込まれても値が変わらないことを保証する橋渡しデータが
    **外部仮説なしで**存在する（完全証明・橋ゆえ complete_pct 0 前進）。 -/
theorem tctb_exists (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    Nonempty (ThetaCommTemperedBridgeData p l hl ζ) :=
  ⟨thetaCommTemperedBridgeData p l hl ζ⟩

/-! ## M438F-7: 実例 -/

/-- 実例: j=3 での thLtorExp と tpeGroup 内交換子中心座標の一致（9 = 3²）。 -/
example :
    thLtorExp 3
      = (tpeGroup.comm (tpeIncl.map (tcvbGenA 3)) (tpeIncl.map (tcvbGenB 3))).1.2.2 :=
  tctb_thLtorExp_eq_tpe_commutator 3

/-- 実例: 共有指数 tccbExp 4 = 16 が tpeGroup 内交換子中心座標に一致。 -/
example :
    ((tccbExp 4 : Nat) : Int)
      = (tpeGroup.comm (tpeIncl.map (tcvbGenA (4 : Int)))
          (tpeIncl.map (tcvbGenB (4 : Int)))).1.2.2 :=
  tctb_shared_exp_tpe 4

/-- 実例: deck×テータ交換子の対角特殊化 j=2 は thLtorExp 2 = 4 に合流。 -/
example :
    tpeGroup.comm (tpeSection.map 2) (tpeIncl.map (tcvbGenB 2))
      = tpeIncl.map ((0, 0, thLtorExp 2) : Int × Int × Int) :=
  tctb_deck_theta_shared_exp 2

/-- 実例: 標準生成元の μ_l 像は tpeGroup・atpGroup の両方で ζ のまま。 -/
example (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    centerToMu p l ζ
        ((tpeGroup.comm (tpeIncl.map (tcvbGenA 1)) (tpeIncl.map (tcvbGenB 1))).1.2.2)
      = zpPow p ζ 1
    ∧ centerToMu p l ζ
        ((atpGroup.comm (atpInclGeom.map (tcvbGenA 1))
          (atpInclGeom.map (tcvbGenB 1))).1.1.2.2)
      = zpPow p ζ 1 :=
  ⟨by rw [← tctb_thLtorExp_eq_tpe_commutator 1]; exact tctb_mu_agree p l hl ζ,
    tctb_atp_commutator_mu p l hl ζ⟩

end IUT
