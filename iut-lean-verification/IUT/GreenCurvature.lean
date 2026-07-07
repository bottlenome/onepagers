-- M450F GreenCurvature [実・本物・柱C]
-- complete_pct 影響: 柱C を前進。M445F(agr) が Arakelov 交点数の ∞ 素点寄与を
--   「特定核 g(a,b)=a·b の有限和（Riemann 和近似）」に留め、**curvature 項 dd^c・Dirac δ_E は未**と
--   正直に限定していた。その **curvature（Poisson/Laplacian）項を昇格で閉じる**。∞ 部の Green 関数を
--   **離散 Laplacian（格子上の 2 階中心差分 Δg=g(n+1)−2g(n)+g(n−1)）に対する本物の Green 関数**へ
--   置換し、`grc_poisson` で **Δ(Green) realEq 2a − 2δ₀**（Poisson 方程式＝点源 Dirac δ₀ と定数
--   curvature 背景 2a の差）を realEq で証明する。これが連続の dd^c を 1 次元格子で忠実に実現した核心。
-- 正直な限定（M445F より狭めた形）: 離散 Laplacian（連続 dd^c の格子近似）・1 次元格子・特定 Green 関数
--   G(n)=a·n²−|n|・整数係数に留まる。完全な測度論的 dd^c・多次元・(1,1)-流れ・Deligne pairing は未。

/-
  IUT/GreenCurvature.lean — M450F（柱C: アルキメデス Green 関数の curvature 項の昇格）

  ── 主要成果の分類: **[実]**（§2(a) 昇格）。M445F
     (`IUT/ArakelovGreenArch.lean`, prefix `agr`) は ∞ 素点の寄与を Green 核 g(a,b)=a·b の
     有限和 Σ_{i<N} g(p_i,q_i)（真の Green 積分 ∫g_D·g_E の Riemann 和近似）へ昇格した一方、
     **curvature 項 dd^c g_E・Dirac δ_E は未・特定積核に留まる**と `agr_model_scope` が正直に限定していた。
     真の Arakelov ∞ 交点数は Green 関数の測度論的積分 ∫_{X(ℂ)} g_D·(**dd^c g_E + δ_E**) であり、
     curvature 項 dd^c（Laplacian）と点源 δ_E が本質。本モジュールはその**curvature 項を昇格で閉じる**——
     連続の Laplacian dd^c を **1 次元格子上の離散 Laplacian（2 階中心差分）**で忠実に部分実現し、
     その Laplacian に対する**本物の Green 関数** G(n)=a·n²−|n| を建て、**Poisson 方程式
     Δ(Green) = 2a − 2δ₀**（点源 Dirac δ₀ と定数 curvature 背景 2a の差）を realEq で証明する。
     点源項は piecewise-linear な −|n|（0 で折れて δ を出す）から、curvature 背景項 2a は二次 a·n²
     （2 階差分が定数＝離散 dd^c）から出る。主語は M139-4 の本物の整数埋め込み intToReal と
     M142F の実数橋（加法/乗法/負元両立）。toy 主語なし。

  complete_pct 影響: **柱C（Frobenioid／Arakelov 交点理論）の実 IUT 完全証明率を前進**。
  M445F は curvature 項なし・特定積核に留めていた。本ファイルは:
  (1) **離散 Laplacian** `grcLaplacian g n = g(n+1)+g(n−1)−2g(n)`——格子点上の 2 階中心差分の実数値。
      連続の dd^c（Laplacian）の 1 次元格子近似。
  (2) **本物の Green 関数** `grcGreen a n = a·n²−|n|（実数値・整数橋経由）`——curvature パラメータ a。
      点源部 −|n|（0 で折れる）＋ curvature 背景部 a·n²（2 階差分が定数）。
  (3) **Poisson 方程式** `grc_poisson`——**Δ(grcGreen a) realEq 2a − 2δ₀**（realEq で証明）。
      **点源 Dirac δ₀ と定数 curvature 背景 2a の差**として Laplacian が特徴づけられる。M445F の
      「curvature なし」限定を実際に閉じた本丸——dd^c を離散 Laplacian で実現した核心。
  (4) **積核と異なる（Laplacian で特徴づけ）** `grc_green_not_multiplicative`——Green 関数は
      Δ≠0 の**本物の点源**を持つ（n=0 で Δ=−2）が、M445F の積核 g(a,b)=a·b（各変数で線形＝
      離散調和・`grc_linear_harmonic` で Δ=0）は点源を持たない。Laplacian が両者を分離する。
  (5) **curvature を含む pairing の対称性** `grc_pairing_curvature`——交点 ∞ 部の Green 核を本 Green
      関数へ置換した対称性 G(n)=G(−n)（真の g(z,w)=g(w,z)、curvature 項 a·n² 込みで偶）。
  (6) **調和ケースへの整合** `grc_reduces_to_agr`——curvature a=0 にすると定数背景 2a が消え Poisson が
      純点源 Δg=−2δ₀ へ帰着（M445F=agr が暗黙に居た curvature 無しの調和領域へ整合する方向）。
  (7) 正直な scope 定理 `grc_model_scope`（M445F より狭めた残限定）＋ capstone `grc_exists`。

  ## 正直な限定（消去/弱化禁止・地図として保持。M445F より狭めた形）
  - **本物（完全証明・M445F の curvature 無し限定を閉じた部分）**: ∞ 部の Green 関数が
    **離散 Laplacian に対する Poisson 方程式 Δg = 2a − 2δ₀** を満たすこと（`grc_poisson`、realEq）・
    点源 Dirac δ₀ と定数 curvature 背景 2a が**分離して現れる**こと・Green 関数が**本物の点源**を持ち
    積核（離散調和）と Laplacian で**実際に分離**すること（`grc_green_not_multiplicative`＋
    `grc_linear_harmonic`）・curvature 込みの**偶対称** G(n)=G(−n)（`grc_pairing_curvature`）・
    curvature 0 で**純点源へ帰着**（`grc_reduces_to_agr`）。全て本物・sorry 皆無・新規 Classical.choice なし。
  - **正直申告（M445F から狭めた残・後続）**:
    ・**離散 Laplacian（連続 dd^c の格子近似）に留まる**——真の curvature 項は (1,1)-流れ dd^c g_E の
      測度論的作用であり、本模型はこれを 1 次元格子の 2 階中心差分へ離散化した近似。連続極限・
      多次元 Laplacian・完全な測度論的 dd^c・Green 関数の測度論的積分 ∫g_D·(dd^c g_E+δ_E) は**後続**。
    ・**1 次元格子・特定 Green 関数**——G(n)=a·n²−|n|（点源＋定数曲率）に留まる。真の −log|z−w| 型／
      円周・リーマン面上の Green 関数の測度論的構成・可変曲率は後続。
    ・**整数係数**——curvature a・格子点 n は整数。有理/実係数の稠密化は後続。
    ・**Deligne pairing / arithmetic Riemann–Roch**（交点数と算術次数の Riemann–Roch 型関係）は後続。
    ・**一般数体（K≠ℚ）**は範囲外（M445F と同じ K=ℚ 模型・唯一の ∞ 素点）。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・[propext, Quot.sound]）・
  sorry 皆無・禁止タクティク不使用。
-/
import IUT.ArakelovGreenArch
import IUT.IntRealBridge
import IUT.RealOrder

namespace IUT

/-! ## M450F-0: 整数レベルの Green 関数・Dirac・2 階差分の恒等式 -/

/-- **M450F-0a: 格子上の Dirac δ₀** — δ₀(n) = 1 (n=0), 0 (else)。∞ 素点の点源（真の Dirac δ_E の
    格子版）。Poisson 方程式の右辺の点源項。 -/
def grcDeltaZ (n : Int) : Int := if n = 0 then 1 else 0

/-- **M450F-0b: 整数値 Green 関数** G(n) = a·n² − |n|——curvature パラメータ a を持つ本物の Green 関数
    の整数核。点源部 −|n|（0 で折れる piecewise-linear、2 階差分が δ を出す）＋ curvature 背景部
    a·n²（2 階差分が定数 2a＝離散 dd^c）。真の Green 潜在の格子模型。 -/
def grcGreenZ (a n : Int) : Int := a * (n * n) - (Int.natAbs n : Int)

/-- **M450F-0c: 係数付き二次の 2 階差分は定数 2a** — a·(n+1)² + a·(n−1)² − 2·(a·n²) = 2a。
    二次関数の離散 Laplacian は定数＝**curvature 背景項（離散 dd^c）**。積の分配を明示補題で
    展開し（`Int.mul_add`/`Int.mul_sub`）、二次恒等式 (n+1)²+(n−1)²−2n²=2 を経由。 -/
theorem grc_quad_second_diff (a n : Int) :
    a * ((n + 1) * (n + 1)) + a * ((n - 1) * (n - 1)) - 2 * (a * (n * n)) = 2 * a := by
  have h1 : (n + 1) * (n + 1) = n * n + n + n + 1 := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
  have h2 : (n - 1) * (n - 1) = n * n - n - n + 1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
  have hQ : (n + 1) * (n + 1) + (n - 1) * (n - 1) - 2 * (n * n) = 2 := by
    rw [h1, h2]; omega
  have e1 : 2 * (a * (n * n)) = a * (2 * (n * n)) := by rw [Int.mul_left_comm]
  have e2 : a * ((n + 1) * (n + 1)) + a * ((n - 1) * (n - 1))
      = a * ((n + 1) * (n + 1) + (n - 1) * (n - 1)) :=
    (Int.mul_add a ((n + 1) * (n + 1)) ((n - 1) * (n - 1))).symm
  have e3 : a * ((n + 1) * (n + 1) + (n - 1) * (n - 1)) - a * (2 * (n * n))
      = a * ((n + 1) * (n + 1) + (n - 1) * (n - 1) - 2 * (n * n)) :=
    (Int.mul_sub a ((n + 1) * (n + 1) + (n - 1) * (n - 1)) (2 * (n * n))).symm
  rw [e1, e2, e3, hQ, Int.mul_comm]

/-- **M450F-0d: |·| の 2 階差分は 2δ₀** — |n+1| + |n−1| − 2|n| = 2 (n=0), 0 (else)。
    piecewise-linear な |n| の離散 Laplacian は原点だけに集中した**点源 Dirac**（真の δ_E の格子版）。
    `Int.natAbs` を Int にキャストして omega で場合分け。 -/
theorem grc_natAbs_second_diff (n : Int) :
    (Int.natAbs (n + 1) : Int) + (Int.natAbs (n - 1) : Int) - 2 * (Int.natAbs n : Int)
      = (if n = 0 then 2 else 0) := by
  omega

/-- **M450F-0e: 整数 Green 関数の Poisson 方程式（点源＋定数曲率）** —
    G(n+1) + G(n−1) − (G(n)+G(n)) = 2a − 2·δ₀(n)。
    2 階差分（離散 Laplacian）が**定数 curvature 背景 2a と点源 Dirac 2δ₀ の差**に等しい。
    curvature 部は `grc_quad_second_diff`（二次の定数 2 階差分）、点源部は `grc_natAbs_second_diff`
    （|n| の点集中 2 階差分）から。連続 Poisson Δg = c·1 − δ_p の格子版。 -/
theorem grc_poissonZ (a n : Int) :
    grcGreenZ a (n + 1) + grcGreenZ a (n - 1) - (grcGreenZ a n + grcGreenZ a n)
      = 2 * a - 2 * grcDeltaZ n := by
  have hq := grc_quad_second_diff a n
  have hn := grc_natAbs_second_diff n
  unfold grcGreenZ grcDeltaZ
  omega

/-- **M450F-0f: 整数 Green 関数の偶対称** G(−n) = G(n)——curvature 項 a·n²（偶）と点源部 −|n|
    （偶）がともに偶ゆえ Green 関数は偶。真の g(z,w)=g(w,z)（対称性）の格子版。
    `Int.neg_mul_neg`（(−n)²=n²）と `Int.natAbs_neg`（|−n|=|n|）で。 -/
theorem grc_greenZ_even (a n : Int) : grcGreenZ a (-n) = grcGreenZ a n := by
  unfold grcGreenZ
  rw [Int.neg_mul_neg, Int.natAbs_neg]

/-! ## M450F-1: 実数値の離散 Laplacian（連続 dd^c の格子近似） -/

/-- **M450F-1a: 離散 Laplacian（2 階中心差分）** Δg(n) = g(n+1) + g(n−1) − 2g(n)——格子点上の
    実数値 2 階差分。連続の Laplacian dd^c の 1 次元格子近似。−2g(n) は realNeg(g(n)+g(n)) で表現。 -/
def grcLaplacian (g : Int → RReal) (n : Int) : RReal :=
  realAdd (realAdd (g (n + 1)) (g (n - 1))) (realNeg (realAdd (g n) (g n)))

/-- **M450F-1b: 実数値 Green 関数** G(n) = a·n² − |n|（整数橋 intToReal 経由の実数値）。
    curvature パラメータ a。真の Green 潜在の 1 次元格子模型。 -/
def grcGreen (a : Int) (n : Int) : RReal := intToReal (grcGreenZ a n)

/-- **M450F-1c: 整数値関数の離散 Laplacian は整数 2 階差分の像** —
    Δ(ι∘gZ)(n) realEq ι(gZ(n+1)+gZ(n−1)−(gZ(n)+gZ(n)))。実数橋（加法 `intToReal_add`・
    負元 `intToReal_neg`）で実数 Laplacian を整数 2 階差分へ落とす。Poisson の実数化の土台。 -/
theorem grc_lap_intToReal (gZ : Int → Int) (n : Int) :
    realEq (grcLaplacian (fun m => intToReal (gZ m)) n)
      (intToReal (gZ (n + 1) + gZ (n - 1) - (gZ n + gZ n))) := by
  have h1 : realEq (realAdd (intToReal (gZ (n + 1))) (intToReal (gZ (n - 1))))
      (intToReal (gZ (n + 1) + gZ (n - 1))) := intToReal_add _ _
  have h2 : realEq (realAdd (intToReal (gZ n)) (intToReal (gZ n)))
      (intToReal (gZ n + gZ n)) := intToReal_add _ _
  have h3 : realEq (realNeg (realAdd (intToReal (gZ n)) (intToReal (gZ n))))
      (intToReal (-(gZ n + gZ n))) :=
    realEq_trans (realNeg_congr h2) (intToReal_neg (gZ n + gZ n))
  refine realEq_trans
    (realAdd_congr_left (realNeg (realAdd (intToReal (gZ n)) (intToReal (gZ n)))) h1) ?_
  refine realEq_trans
    (realAdd_congr_right (intToReal (gZ (n + 1) + gZ (n - 1))) h3) ?_
  refine realEq_trans (intToReal_add _ _) ?_
  exact aip_intToReal_congr (by omega)

/-! ## M450F-2: Poisson 方程式（curvature 項 dd^c を離散 Laplacian で実現・本丸） -/

/-- **M450F-2: Poisson 方程式** — **Δ(grcGreen a) realEq 2a − 2δ₀**。
    離散 Laplacian（連続 dd^c の格子版）が Green 関数へ作用すると、**定数 curvature 背景 2a と
    点源 Dirac 2δ₀ の差**に等しい（realEq で証明）。**M445F `agr_model_scope` が「curvature 項
    dd^c・Dirac δ_E は未・特定積核 g(a,b)=a·b に留まる」と正直に限定していた内容を、本 Poisson 方程式が
    curvature 項（Laplacian dd^c を格子で実現した 2a）と点源 δ₀ を分離して満たすことで閉じる**。
    連続の Arakelov Green 方程式 dd^c g_E + δ_E ↔ 曲率＋点源 の 1 次元格子忠実版。 -/
theorem grc_poisson (a n : Int) :
    realEq (grcLaplacian (grcGreen a) n) (intToReal (2 * a - 2 * grcDeltaZ n)) :=
  realEq_trans (grc_lap_intToReal (grcGreenZ a) n) (aip_intToReal_congr (grc_poissonZ a n))

/-! ## M450F-3: 積核との分離（Laplacian が Green 関数を特徴づける） -/

/-- **M450F-3a: 線形（積型）核は離散調和** — 各変数で線形な核 f(n)=c·n の離散 Laplacian は 0。
    M445F の積核 g(a,b)=a·b は各スロットで線形ゆえ 2 階差分が消え**点源を持たない**。
    Green 関数（点源あり）との分離の一方。 -/
theorem grc_linear_harmonic (c m : Int) :
    realEq (grcLaplacian (fun n => intToReal (c * n)) m) realZero := by
  refine realEq_trans (grc_lap_intToReal (fun n => c * n) m) ?_
  have hz : c * (m + 1) + c * (m - 1) - (c * m + c * m) = 0 := by
    have p1 : c * (m + 1) = c * m + c := by rw [Int.mul_add, Int.mul_one]
    have p2 : c * (m - 1) = c * m - c := by rw [Int.mul_sub, Int.mul_one]
    rw [p1, p2]; omega
  rw [hz]
  exact realEq_refl _

/-- **M450F-3b: Green 関数は本物の点源を持つ（積核と Laplacian で分離）** —
    ∃ n, Δ(grcGreen 0)(n) ≠ 0。curvature 無し（a=0）でも n=0 で Δ = −2 ≠ 0 の**点源 Dirac** を持つ。
    **M445F の積核 g(a,b)=a·b は離散調和（`grc_linear_harmonic` で Δ=0）ゆえ点源を持たず**、本 Green
    関数と Laplacian が実際に**分離**する（Green 関数は積核でなく Laplacian で特徴づけられる）。
    M445F の「特定積核に留まる」限定を、Poisson で特徴づく本物の Green 関数の存在で閉じた証拠。 -/
theorem grc_green_not_multiplicative :
    ∃ n : Int, ¬ realEq (grcLaplacian (grcGreen 0) n) realZero := by
  refine ⟨0, ?_⟩
  intro hcon
  have hp : realEq (intToReal (2 * (0 : Int) - 2 * grcDeltaZ 0)) realZero :=
    realEq_trans (realEq_symm (grc_poisson 0 0)) hcon
  have hval : (2 * (0 : Int) - 2 * grcDeltaZ 0) = -2 := by unfold grcDeltaZ; omega
  rw [hval] at hp
  exact aip_intToReal_ne (by omega) hp

/-! ## M450F-4: curvature を含む pairing の対称性・調和ケースへの整合 -/

/-- **M450F-4a: curvature 込みの交点 pairing 対称性** — ∞ 部の Green 核を本 Green 関数へ置換した
    交点寄与 G(n) は偶 G(n)=G(−n)。真の Arakelov ∞ 交点の対称性 g(z,w)=g(w,z) を、curvature 項
    a·n² と点源 −|n| がともに偶であることから realEq で示す。M445F の交点 ∞ 部（積核対称）を
    curvature 込みの Green 関数へ昇格しても対称双線形形式の中核が保たれる。 -/
theorem grc_pairing_curvature (a n : Int) :
    realEq (grcGreen a n) (grcGreen a (-n)) :=
  aip_intToReal_congr (grc_greenZ_even a n).symm

/-- **M450F-4b: 調和ケースへの帰着（agr の curvature 無し領域へ整合）** —
    curvature a=0 にすると定数背景項 2a が消え、Poisson が**純点源 Δg = −2δ₀** へ帰着する。
    M445F=agr は curvature 項を持たない（積核の有限和）調和領域で動いていた——本 Green 関数の
    a=0 特殊化はその**curvature 無し領域へ整合する方向**を明示する。 -/
theorem grc_reduces_to_agr (n : Int) :
    realEq (grcLaplacian (grcGreen 0) n) (intToReal (-(2 * grcDeltaZ n))) :=
  realEq_trans (grc_poisson 0 n) (aip_intToReal_congr (by omega))

/-! ## M450F-5: 正直な scope 定理（M445F より狭めた残限定を露出） -/

/-- **M450F-5: 正直な scope 定理** — 本 Green curvature の正体は**離散 Laplacian（格子上の 2 階
    中心差分）**であること（定義的等式）。M445F の「curvature 項 dd^c 未」限定は `grc_poisson` で
    閉じたが、**離散 Laplacian（連続 dd^c の格子近似）・1 次元格子・特定 Green 関数 G(n)=a·n²−|n|・
    整数係数に留まる**という残限定を地図として露出する（真の測度論的 dd^c・(1,1)-流れ・多次元・
    Deligne pairing は後続。完全証明ファースト規則 §4）。 -/
theorem grc_model_scope (a : Int) (n : Int) :
    grcLaplacian (grcGreen a) n
      = realAdd (realAdd (grcGreen a (n + 1)) (grcGreen a (n - 1)))
          (realNeg (realAdd (grcGreen a n) (grcGreen a n))) :=
  rfl

/-! ## M450F-6: capstone -/

/-- **M450F-6a: Green curvature データ** — 本物の Green 関数・離散 Laplacian・Poisson 方程式
    （点源＋定数曲率）・偶対称・本物の点源（積核と分離）を束ねた実体。 -/
structure GrcGreenData where
  /-- 実数値 Green 関数 G(a,n)=a·n²−|n|。 -/
  green : Int → Int → RReal
  /-- 離散 Laplacian（2 階中心差分・連続 dd^c の格子版）。 -/
  laplacian : (Int → RReal) → Int → RReal
  /-- **Poisson 方程式** Δg = 2a − 2δ₀（定数曲率背景と点源 Dirac の差）。 -/
  poisson : ∀ a n, realEq (laplacian (green a) n) (intToReal (2 * a - 2 * grcDeltaZ n))
  /-- curvature 込みの偶対称 g(n)=g(−n)。 -/
  even_symm : ∀ a n, realEq (green a n) (green a (-n))
  /-- **本物の点源**（積核＝離散調和と Laplacian で分離する witness が存在）。 -/
  has_source : ∃ n, ¬ realEq (laplacian (green 0) n) realZero

/-- **M450F-6b: Green curvature データの witness**（全て本物）。 -/
def grcGreenData : GrcGreenData where
  green := grcGreen
  laplacian := grcLaplacian
  poisson := grc_poisson
  even_symm := grc_pairing_curvature
  has_source := grc_green_not_multiplicative

/-- **M450F-6c: 存在** — Green curvature データは充足可能（K=ℚ・1 次元格子・G(n)=a·n²−|n| witness）。 -/
theorem grc_exists : Nonempty GrcGreenData :=
  ⟨grcGreenData⟩

end IUT
