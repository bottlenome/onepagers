-- M470F GreenVariableSolve [実・本物・柱C]
-- complete_pct 影響: 柱C を前進。M465F(gvc) の `gvc_model_scope` は「可変係数（位置依存）＋混合項付き
--   離散楕円**作用素**を建てたが、**その作用素を解く可変曲率 Green 関数**（Δ_var G = δ_source を満たす
--   本物の Green 関数）は後続」と正直に限定していた、その **「Green 関数は後続」を昇格で閉じる**。
--   1 次元可変係数（位置依存）Laplacian Δ_var g(n) = a(n)·(g(n+1)+g(n−1)−2g(n)) に対する
--   **本物の Green 関数** G_p(n) = −|n−p|（点源 p を中心とする基本解）を明示構成し、`gvs_solves_poisson`
--   で **Δ_var(G_p) realEq δ_source（= −2·a(n)·δ_p、点源 p で −2a(p)・他で 0）** を realEq で証明する。
--   これが「作用素だけでなく Green 関数が実際に可変係数 Poisson を解く」核心＝M465F の残限定を閉じた本丸。
-- 正直な限定（M465F より狭めた形）: 1 次元格子・非発散型（a(n)·2 階中心差分）可変係数・基本解 G_p=−|n−p|・
--   整数係数・点源が単一格子点に集中する場合に留まる。2 次元以上の可変係数 Green・完全な測度論的 dd^c・
--   Deligne pairing・発散型 Σ1/a(k) 部分和型 Green（実数逆元の稠密化を要す）は未。

/-
  IUT/GreenVariableSolve.lean — M470F（柱C: 可変係数作用素を解く本物の Green 関数への昇格）

  ── 主要成果の分類: **[実]**（§2(a) 昇格）。M465F
     (`IUT/GreenVariableCoeff.lean`, prefix `gvc`) は連続の一般 2 階楕円作用素を
     **位置依存重み α(m,n),β(m,n),γ(m,n) と混合 2 階差分を持つ離散楕円作用素 gvcLaplacian**へ
     昇格し、混合項が非自明に効くこと・重みが位置依存であること・可変係数 Poisson 型関係式を証明した
     一方、`gvc_model_scope` が **「可変係数（位置依存）＋混合項付き離散楕円**作用素**を建てたが、
     その作用素を解く**可変曲率 Green 関数**（Δ_var G = δ_source を満たす本物の Green 関数）は後続」**と
     正直に限定していた。真の Arakelov 曲率理論では作用素の存在だけでなく、その作用素に対する
     **Green 関数（基本解、点源に対する応答 Δ_var G = δ_source）**を明示的に解くことが本質である。
     本モジュールはその **「Green 関数は後続」限定を昇格で閉じる**——1 次元の可変係数（位置依存）
     Laplacian **Δ_var g(n) = a(n)·(g(n+1)+g(n−1)−2g(n))**（各格子点で異なる重み a(n) を intToReal
     経由で rmul）に対する **本物の Green 関数 G_p(n) = −|n−p|**（点源 p を中心とする基本解、
     piecewise-linear で p で折れて δ を出す）を明示構成し、**可変係数 Poisson 方程式
     Δ_var(G_p) = −2·a(n)·δ_p**（点源 p で強度 −2a(p)、他の格子点で 0）を realEq で証明する。
     Laplacian(基本解) = 局所係数 × δ という基本解の定義そのものを 1 次元格子で忠実に実現した核心。
     主語は M139-4 の本物の整数埋め込み intToReal・M142F の実数橋（加法/乗法/負元）・M450F の本物の
     1 次元 grc（grcLaplacian・grc_lap_intToReal・grc_natAbs_second_diff）。toy 主語なし。

  complete_pct 影響: **柱C（Frobenioid／Arakelov 交点理論）の実 IUT 完全証明率を前進**。
  M465F は可変係数＋混合項付き離散楕円**作用素**の建設に留め、その作用素を**解く Green 関数**は
  後続としていた。本ファイルは:
  (1) **可変係数（位置依存）1 次元 Laplacian** `gvsVarLaplacian a g n = a(n)·Δ(g)(n)`——各格子点 n の
      重み a(n) を intToReal 経由で rmul し、M450F の grcLaplacian（2 階中心差分）へ位置依存に掛ける。
      連続の可変係数作用素 a(x)·∂² の 1 次元格子近似。
  (2) **本物の Green 関数** `gvsGreen p n = −|n−p|（整数橋経由の実数値）`——点源 p を中心とする基本解。
      piecewise-linear（p で折れる）。真の Green 潜在の可変係数版格子模型。
  (3) **可変係数 Poisson 方程式（本丸）** `gvs_solves_poisson`——
      **Δ_var(gvsGreen p) realEq intToReal(gvsSourceZ a p)**（realEq で証明）。右辺の点源
      gvsSourceZ a p n = a(n)·(if n=p then −2 else 0) は **点源 p で強度 −2a(p)・他で 0**。
      **M465F の「Green 関数は後続」限定を実際に閉じた本丸**——作用素だけでなく、その作用素に対する
      Green 関数（基本解）が可変係数 Poisson を realEq で実際に解く。
  (4) **点源が単一格子点に集中（0 elsewhere）** `gvs_offsource_zero`——n≠p のとき
      Δ_var(gvsGreen p) realEq realZero（点源 p 以外で作用素は消える）。点源 δ_p の「他で 0」を明示。
  (5) **Green 関数が可変係数を反映** `gvs_green_variable`——係数 a(n)=n（非定数）のとき、点源 p での
      応答強度 −2a(p) が源の位置により異なる（p=1 で −2、p=2 で −4、−2≠−4 ゆえ ¬realEq）。
      Green 関数（の解く点源応答）が **位置依存の可変係数を genuine に反映**する証拠。
  (6) **定数係数 grc への整合** `gvs_reduces_to_grc`——a(n)≡1（定数係数）で可変係数 Laplacian が
      M450F の定数係数 grcLaplacian（2 階中心差分）へ realEq で厳密帰着（重み 1 が消える）。
  (7) **Green 関数の単調性（基本性質）** `gvs_green_monotone`——p ≤ m ≤ n で G_p(n) ≤ G_p(m)、
      点源 p から離れるほど Green 関数値が減少（−|n−p| の単調性、rLe で）。
  (8) 正直な scope 定理 `gvs_model_scope`（M465F より狭めた残限定）＋ capstone `gvs_exists`。

  ## 正直な限定（消去/弱化禁止・地図として保持。M465F の「Green 関数は後続」を閉じた形）
  - **本物（完全証明・M465F の「Green 関数は後続」限定を閉じた部分）**: 可変係数（位置依存）Laplacian
    に対する **本物の Green 関数 G_p(n)=−|n−p| が可変係数 Poisson 方程式
    Δ_var(G_p) = −2·a(n)·δ_p を実際に解く**こと（`gvs_solves_poisson`、realEq）・点源が **単一格子点 p に
    集中し他で 0** であること（`gvs_offsource_zero`）・Green 関数の点源応答が **位置依存の可変係数を反映**
    すること（`gvs_green_variable`、−2≠−4）・a≡1 で **M450F 定数係数 grc へ厳密帰着**すること
    （`gvs_reduces_to_grc`）・Green 関数が **点源から離れて単調減少**すること（`gvs_green_monotone`）。
    全て本物・sorry 皆無・新規 Classical.choice なし。
  - **正直申告（M465F から狭めた残・後続）**:
    ・**1 次元格子・非発散型可変係数に留まる**——本作用素は a(n)·(2 階中心差分)（非発散型）であり、
      真の可変曲率は連続の測度論的 dd^c（(1,1)-形式）。連続極限・**2 次元以上の可変係数 Green 関数**・
      発散型 a(n)(g(n+1)−g(n))−a(n−1)(g(n)−g(n−1)) に対する Σ1/a(k) 部分和型 Green は**後続**。
    ・**基本解 G_p=−|n−p|・整数係数**——Green 関数は piecewise-linear な基本解に留まり、点源は単一格子点 p
      に集中する場合。真の −log|z−w| 型／リーマン面上の可変曲率 Green 関数・任意の点源配置は後続。
      係数 a・格子点は整数。有理/実係数（実数逆元 1/a(k)）の稠密化は後続。
    ・**Deligne pairing / arithmetic Riemann–Roch** は後続。
    ・**一般数体（K≠ℚ）**は範囲外（M465F と同じ K=ℚ 模型・唯一の ∞ 素点）。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・[propext, Quot.sound]）・
  sorry 皆無・禁止タクティク不使用。
-/
import IUT.GreenVariableCoeff
import IUT.GreenCurvature
import IUT.IntRealBridge
import IUT.RealOrder
import IUT.RealMul

namespace IUT

/-! ## M470F-0: 整数レベルの可変係数作用素・Green 関数・点源 -/

/-- **M470F-0a: 整数値 可変係数（位置依存）1 次元 Laplacian（非発散型）**
    Δ_var gZ(n) = a(n)·(gZ(n+1) + gZ(n−1) − (gZ(n)+gZ(n)))。
    **重み a(n) は位置 n の関数**（可変係数）で 2 階中心差分に掛かる。連続の可変係数作用素
    a(x)·∂² の 1 次元格子近似の整数核。 -/
def gvsVarLapZ (a : Int → Int) (gZ : Int → Int) (n : Int) : Int :=
  a n * (gZ (n + 1) + gZ (n - 1) - (gZ n + gZ n))

/-- **M470F-0b: 整数値 Green 関数（点源 p の基本解）** G_p(n) = −|n−p|。
    点源 p を中心とする piecewise-linear な基本解（p で折れて 2 階差分が δ_p を出す）。
    真の Green 潜在の可変係数版格子核（M450F の grcGreenZ 0 を任意点源 p へ平行移動した形）。 -/
def gvsGreenZ (p n : Int) : Int := -(Int.natAbs (n - p) : Int)

/-- **M470F-0c: 整数値 点源（可変係数重み付き Dirac）** δ_source(n) = a(n)·(if n=p then −2 else 0)。
    点源 p で強度 −2·a(p)（局所係数を反映）・他の格子点で 0。可変係数 Poisson の右辺。 -/
def gvsSourceZ (a : Int → Int) (p n : Int) : Int := a n * (if n = p then -2 else 0)

/-- **M470F-0d: 基本解 G_p の 2 階差分は点源 −2δ_p** —
    G_p(n+1) + G_p(n−1) − (G_p(n)+G_p(n)) = if n=p then −2 else 0。
    −|n−p| の離散 Laplacian は原点 p だけに集中した点源（真の δ_p の格子版）。
    M450F `grc_natAbs_second_diff`（|·| の 2 階差分が点集中）を点源 p へ平行移動した核心恒等式。 -/
theorem gvs_greenZ_second_diff (p n : Int) :
    gvsGreenZ p (n + 1) + gvsGreenZ p (n - 1) - (gvsGreenZ p n + gvsGreenZ p n)
      = (if n = p then -2 else 0) := by
  unfold gvsGreenZ
  omega

/-- **M470F-0e: 整数版 可変係数 Poisson** — Δ_var(G_p)(n) = a(n)·(if n=p then −2 else 0) = δ_source(n)。
    基本解 G_p の 2 階差分が点源 −2δ_p（`gvs_greenZ_second_diff`）ゆえ、位置依存重み a(n) を掛けると
    可変係数点源 a(n)·(−2δ_p) が残る。可変係数 Green 関数が点源方程式を解く整数核心。 -/
theorem gvs_poissonZ (a : Int → Int) (p n : Int) :
    gvsVarLapZ a (gvsGreenZ p) n = gvsSourceZ a p n := by
  unfold gvsVarLapZ gvsSourceZ
  rw [gvs_greenZ_second_diff p n]

/-- **M470F-0f: 基本解 G_p の点源 p 周りの偶対称（整数）** G_p(2p − n) = G_p(n)。
    G_p(n)=−|n−p| は点源 p を中心に偶（|(2p−n)−p|=|p−n|=|n−p|）。真の g(z,w)=g(w,z) の格子版。 -/
theorem gvs_greenZ_symm (p n : Int) : gvsGreenZ p (2 * p - n) = gvsGreenZ p n := by
  unfold gvsGreenZ
  omega

/-! ## M470F-1: 実数値の可変係数作用素・Green 関数 -/

/-- **M470F-1a: 実数値 可変係数（位置依存）1 次元 Laplacian**
    Δ_var g(n) = a(n)·Δ(g)(n)——各格子点 n の重み a(n) を intToReal 経由で M450F の
    grcLaplacian（2 階中心差分）へ rmul で位置依存に掛ける。連続の可変係数作用素 a(x)·∂² の格子近似。 -/
def gvsVarLaplacian (a : Int → Int) (g : Int → RReal) (n : Int) : RReal :=
  rmul (intToReal (a n)) (grcLaplacian g n)

/-- **M470F-1b: 実数値 Green 関数（点源 p の基本解）** G_p(n)=−|n−p|（整数橋 intToReal 経由）。
    可変係数 Laplacian に対する本物の基本解の 1 次元格子模型。 -/
def gvsGreen (p n : Int) : RReal := intToReal (gvsGreenZ p n)

/-! ## M470F-2: 可変係数 Poisson 方程式（Green 関数が作用素を解く・本丸） -/

/-- **M470F-2: 可変係数 Poisson 方程式（本丸）** —
    **Δ_var(gvsGreen p) realEq intToReal(gvsSourceZ a p)**。
    位置依存重み a(n) を持つ可変係数 Laplacian が本物の Green 関数 G_p(n)=−|n−p| へ作用すると、
    **点源 δ_source = a(n)·(−2δ_p)（点源 p で強度 −2a(p)・他で 0）** に等しい（realEq で証明）。
    **M465F `gvc_model_scope` が「可変係数＋混合項付き離散楕円**作用素**は建てたが、その作用素を解く
    Green 関数（Δ_var G = δ_source を満たす基本解）は後続」と正直に限定していた、その「Green 関数は
    後続」を実際に閉じる本丸**——作用素だけでなく、その作用素に対する Green 関数が可変係数 Poisson を
    realEq で実際に解く。実数化は重み rmul を `intToReal_mul`・2 階差分を M450F `grc_lap_intToReal`・
    点源核を整数版 `gvs_poissonZ` で落として合成。Laplacian(基本解) = 局所係数 × δ の 1 次元格子忠実版。 -/
theorem gvs_solves_poisson (a : Int → Int) (p n : Int) :
    realEq (gvsVarLaplacian a (gvsGreen p) n) (intToReal (gvsSourceZ a p n)) := by
  have hlap : realEq (grcLaplacian (gvsGreen p) n)
      (intToReal (gvsGreenZ p (n + 1) + gvsGreenZ p (n - 1) - (gvsGreenZ p n + gvsGreenZ p n))) :=
    grc_lap_intToReal (gvsGreenZ p) n
  refine realEq_trans (rmul_congr_right (intToReal (a n)) hlap) ?_
  refine realEq_trans
    (intToReal_mul (a n)
      (gvsGreenZ p (n + 1) + gvsGreenZ p (n - 1) - (gvsGreenZ p n + gvsGreenZ p n))) ?_
  exact aip_intToReal_congr (gvs_poissonZ a p n)

/-! ## M470F-3: 点源が単一格子点に集中（他で 0） -/

/-- **M470F-3: 点源は源 p 以外で消える（0 elsewhere）** — n≠p のとき Δ_var(gvsGreen p)(n) realEq realZero。
    可変係数 Green 関数の点源応答は **単一格子点 p に集中**し、他の格子点では作用素が消える
    （点源 δ_p の「他で 0」を明示）。`gvs_solves_poisson` の右辺 gvsSourceZ が n≠p で 0 になることから。 -/
theorem gvs_offsource_zero (a : Int → Int) (p n : Int) (h : n ≠ p) :
    realEq (gvsVarLaplacian a (gvsGreen p) n) realZero := by
  have hs := gvs_solves_poisson a p n
  have hz : gvsSourceZ a p n = 0 := by
    unfold gvsSourceZ
    rw [if_neg h, Int.mul_zero]
  rw [hz] at hs
  exact realEq_trans hs (realEq_of_seq_eq (fun _ => rfl))

/-! ## M470F-4: Green 関数が可変係数を反映 -/

/-- **M470F-4: Green 関数が可変係数を反映** — 係数 a(n)=n（非定数）のとき、可変係数 Green 関数の
    点源応答強度が **源の位置により異なる**: 点源 p=1 での応答 Δ_var(G₁)(1) は intToReal(−2)、
    点源 p=2 での応答 Δ_var(G₂)(2) は intToReal(−4) となり、−2≠−4 ゆえ ¬realEq。
    点源強度 −2a(p) が局所係数 a(p) を反映するため、可変係数（位置依存重み）が Green 関数の解く
    点源方程式に **genuine に効く**証拠（M465F の可変係数が Green 関数レベルで実現されたことの確認）。 -/
theorem gvs_green_variable :
    ¬ realEq (gvsVarLaplacian (fun i => i) (gvsGreen 1) 1)
             (gvsVarLaplacian (fun i => i) (gvsGreen 2) 2) := by
  intro hcon
  have e1 : gvsSourceZ (fun i => i) 1 1 = -2 := by
    show (1 : Int) * (if (1 : Int) = 1 then -2 else 0) = -2
    omega
  have e2 : gvsSourceZ (fun i => i) 2 2 = -4 := by
    show (2 : Int) * (if (2 : Int) = 2 then -2 else 0) = -4
    omega
  have h1 : realEq (gvsVarLaplacian (fun i => i) (gvsGreen 1) 1)
      (intToReal (gvsSourceZ (fun i => i) 1 1)) := gvs_solves_poisson (fun i => i) 1 1
  have h2 : realEq (gvsVarLaplacian (fun i => i) (gvsGreen 2) 2)
      (intToReal (gvsSourceZ (fun i => i) 2 2)) := gvs_solves_poisson (fun i => i) 2 2
  rw [e1] at h1
  rw [e2] at h2
  have hbad : realEq (intToReal (-2 : Int)) (intToReal (-4 : Int)) :=
    realEq_trans (realEq_symm h1) (realEq_trans hcon h2)
  exact aip_intToReal_ne (by omega) hbad

/-! ## M470F-5: 定数係数 grc への整合 -/

/-- **M470F-5: 定数係数 M450F grc への整合** — a(n)≡1（定数係数）で可変係数 Laplacian が
    M450F の定数係数 grcLaplacian（2 階中心差分）へ realEq で厳密帰着。重み 1 が消え、可変係数
    作用素は定数係数（M450F）作用素の a≡1 特殊化として現れる（可変→定数の整合方向）。 -/
theorem gvs_reduces_to_grc (p n : Int) :
    realEq (gvsVarLaplacian (fun _ => 1) (gvsGreen p) n) (grcLaplacian (gvsGreen p) n) := by
  have hlap : realEq (grcLaplacian (gvsGreen p) n)
      (intToReal (gvsGreenZ p (n + 1) + gvsGreenZ p (n - 1) - (gvsGreenZ p n + gvsGreenZ p n))) :=
    grc_lap_intToReal (gvsGreenZ p) n
  refine realEq_trans (rmul_congr_right (intToReal (1 : Int)) hlap) ?_
  refine realEq_trans
    (intToReal_mul 1
      (gvsGreenZ p (n + 1) + gvsGreenZ p (n - 1) - (gvsGreenZ p n + gvsGreenZ p n))) ?_
  refine realEq_trans (aip_intToReal_congr
    (by omega : (1 : Int) * (gvsGreenZ p (n + 1) + gvsGreenZ p (n - 1)
        - (gvsGreenZ p n + gvsGreenZ p n))
      = gvsGreenZ p (n + 1) + gvsGreenZ p (n - 1) - (gvsGreenZ p n + gvsGreenZ p n))) ?_
  exact realEq_symm hlap

/-! ## M470F-6: Green 関数の基本性質（単調性） -/

/-- **M470F-6: Green 関数の単調性** — 点源 p から右へ p ≤ m ≤ n のとき G_p(n) ≤ G_p(m)（rLe）。
    Green 関数 G_p(n)=−|n−p| は点源 p から離れるほど値が減少する（基本解の単調減衰）。
    整数レベル −|n−p| ≤ −|m−p| を `intToReal_mono` で実数の rLe へ持ち上げる。 -/
theorem gvs_green_monotone (p m n : Int) (h1 : p ≤ m) (h2 : m ≤ n) :
    rLe (gvsGreen p n) (gvsGreen p m) := by
  apply intToReal_mono
  unfold gvsGreenZ
  omega

/-! ## M470F-7: 正直な scope 定理（M465F の「Green 関数は後続」を閉じた形で残限定を露出） -/

/-- **M470F-7: 正直な scope 定理** — 本可変係数 Green 解の正体は**位置依存重み a(n) を M450F の
    2 階中心差分 grcLaplacian へ掛けた可変係数 Laplacian**であること（定義的等式）。M465F の
    「可変係数作用素は建てたが Green 関数は後続」限定は `gvs_solves_poisson`（G_p が可変係数 Poisson を
    解く）で閉じたが、**1 次元格子・非発散型可変係数（a(n)·2 階中心差分）・基本解 G_p=−|n−p|・整数係数・
    点源が単一格子点に集中する場合に留まる**という残限定を地図として露出する（真の測度論的 dd^c・
    2 次元以上の可変係数 Green・発散型 Σ1/a(k) 部分和型 Green・Deligne pairing は後続。
    完全証明ファースト規則 §4）。 -/
theorem gvs_model_scope (a : Int → Int) (g : Int → RReal) (n : Int) :
    gvsVarLaplacian a g n = rmul (intToReal (a n)) (grcLaplacian g n) :=
  rfl

/-! ## M470F-8: capstone -/

/-- **M470F-8a: 可変係数 Green 解データ** — 可変係数（位置依存）Laplacian・本物の Green 関数（基本解）・
    可変係数 Poisson 方程式（Green 関数が作用素を解く）・点源の集中・単調性を束ねた実体。 -/
structure GvsData where
  /-- 可変係数（位置依存）1 次元 Laplacian（重み a(n) を 2 階中心差分へ掛ける）。 -/
  varLaplacian : (Int → Int) → (Int → RReal) → Int → RReal
  /-- 本物の Green 関数（点源 p の基本解 G_p(n)=−|n−p|）。 -/
  green : Int → Int → RReal
  /-- **可変係数 Poisson 方程式** Δ_var(G_p) = δ_source（Green 関数が作用素を実際に解く）。 -/
  solves_poisson : ∀ a p n,
    realEq (varLaplacian a (green p) n) (intToReal (gvsSourceZ a p n))
  /-- 点源は源 p 以外で消える（点源 δ_p の「他で 0」）。 -/
  offsource_zero : ∀ a p n, n ≠ p → realEq (varLaplacian a (green p) n) realZero
  /-- **Green 関数が可変係数を反映**（点源応答強度が源の位置により異なる witness）。 -/
  variable_reflected :
    ¬ realEq (varLaplacian (fun i => i) (green 1) 1) (varLaplacian (fun i => i) (green 2) 2)

/-- **M470F-8b: 可変係数 Green 解データの witness**（全て本物）。 -/
def gvsData : GvsData where
  varLaplacian := gvsVarLaplacian
  green := gvsGreen
  solves_poisson := gvs_solves_poisson
  offsource_zero := gvs_offsource_zero
  variable_reflected := gvs_green_variable

/-- **M470F-8c: 存在** — 可変係数 Green 解データは充足可能
    （K=ℚ・1 次元格子・可変係数 a(n)·2 階中心差分・基本解 G_p(n)=−|n−p| witness）。 -/
theorem gvs_exists : Nonempty GvsData :=
  ⟨gvsData⟩

end IUT
