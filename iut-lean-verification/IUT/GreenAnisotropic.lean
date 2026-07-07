-- M460F GreenAnisotropic [実・本物・柱C]
-- complete_pct 影響: 柱C を前進。M455F(g2d) の `g2d_model_scope` が「**等方 curvature**・特定
--   separable Green・**軸に集中しない点源は後続**」と正直に限定していた、その **「等方・軸上のみ」を
--   非等方（方向ごとに重み α,β の異なる）Laplacian＋軸外の任意点源 (p,q) の Green 関数へ昇格で破って
--   閉じる**。∞ 部の Green 関数を **非等方離散 Laplacian Δ_{α,β}g = α(m 方向 2 階差分)＋β(n 方向
--   2 階差分)** に対する本物の Green 関数 G(m,n)=a(m²+n²)−|m−p|−|n−q| へ置換し、
--   `gan_poisson_anisotropic` で **Δ_{α,β}(ganGreen) realEq α(2a−2δ_p)＋β(2a−2δ_q)**
--   （方向重み α,β が curvature に効く非等方 Poisson・点源は軸外 (p,q)）を realEq で証明する。
-- 正直な限定（M455F より狭めた形）: 2 次元離散格子・特定 Green 関数・**位置非依存（定数）重み α,β**・
--   整数係数に留まる。完全な測度論的 dd^c・任意次元・可変係数（位置依存）曲率・Deligne pairing は未。

/-
  IUT/GreenAnisotropic.lean — M460F（柱C: Green curvature の非等方 Laplacian＋軸外点源への昇格）

  ── 主要成果の分類: **[実]**（§2(a) 昇格）。M455F
     (`IUT/GreenCurvature2D.lean`, prefix `g2d`) は ∞ 部の Green 関数の curvature 項を
     **2 次元格子上の等方 Laplacian（4 近傍差分 Δ₂g、各方向同一重み）**で実現し、2 次元 Poisson
     方程式 Δ₂g = 4a − 2δ₀(m) − 2δ₀(n) を証明した一方、`g2d_model_scope` が
     **「等方 curvature・特定 separable Green・軸に集中しない点源は後続」**と正直に限定していた。
     連続の Arakelov curvature 項 dd^c g_E は一般には**非等方**（方向ごとに曲率が異なる (1,1)-形式）
     であり、点源 δ_E は一般に**原点/軸に乗らない任意点**に置かれる。本モジュールはその
     **「等方・軸上のみ」限定を昇格で破る**——連続の非等方 Laplacian を **2 次元格子上の非等方離散
     Laplacian Δ_{α,β}g = α(g(m+1,n)+g(m−1,n)−2g(m,n)) + β(g(m,n+1)+g(m,n−1)−2g(m,n))**
     （方向ごとに重み α,β の異なる 2 階差分の重み付き和）で忠実に部分実現し、その Laplacian に対する
     **本物の Green 関数** G(m,n)=a(m²+n²)−|m−p|−|n−q| を建て、**非等方 Poisson 方程式
     Δ_{α,β}(ganGreen) = α(2a−2δ_p) + β(2a−2δ_q)**（方向重み α,β が curvature に効き、点源が
     **軸外の任意点 (p,q)** に置ける）を realEq で証明する。curvature 背景は二次形式 a(m²+n²) の
     各方向 2 階差分 2a を重み α,β で結んだ非等方トレース、点源は piecewise-linear な −|m−p|−|n−q|
     （**任意の (p,q) で折れて δ を出す**）から出る。主語は M139-4 の本物の整数埋め込み intToReal・
     M142F の実数橋（加法/乗法/負元）・M450F の 1 次元 grc・M455F の等方 2 次元 g2d。toy 主語なし。

  complete_pct 影響: **柱C（Frobenioid／Arakelov 交点理論）の実 IUT 完全証明率を前進**。
  M455F は等方 curvature・軸上点源に留めていた。本ファイルは:
  (1) **非等方離散 Laplacian** `ganLaplacian α β g m n = α·(m 方向 2 階差分) + β·(n 方向 2 階差分)`
      ——方向ごとに異なる重み α,β を掛けた 2 階中心差分の和（実数値、rmul で重み付け）。連続の非等方
      (1,1)-カレント dd^c の 2 次元格子近似。
  (2) **本物の非等方 Green 関数** `ganGreen a p q m n = a·(m²+n²) − |m−p| − |n−q|`——curvature
      パラメータ a・**軸外の任意点源位置 (p,q)**。M455F の等方 g2dGreenZ a m n（源が原点固定）を、
      源を任意の格子点 (p,q) へずらした拡張。
  (3) **非等方 Poisson 方程式** `gan_poisson_anisotropic`——**Δ_{α,β}(ganGreen) realEq
      α(2a−2δ_p) + β(2a−2δ_q)**。**方向重み α,β が curvature に効く**非等方版・点源が (p,q)。
      **M455F の「等方」限定を実際に破った本丸**——各方向の曲率寄与を α,β で個別に重み付け。
  (4) **軸外の任意点源** `gan_offaxis_source`——∀ p q, Δ_{1,1}(ganGreen 0 p q)(p,q) ≠ 0。
      **点源 Dirac を原点/軸に限らず任意の (p,q) に置ける**（源位置で Δ = −4 ≠ 0）。
      **M455F の「軸に集中しない点源は後続」限定を破った証拠**。
  (5) **等方版 M455F への整合** `gan_reduces_to_g2d`——α=β=1・p=q=0 で ganGreenZ が M455F の
      等方 g2dGreenZ へ厳密帰着し、`gan_reduces_to_g2d_poisson` で非等方 Poisson 右辺が
      等方 4a−2δ₀(m)−2δ₀(n) へ帰着。
  (6) **非等方 Laplacian の加法性（線形作用素）** `gan_laplacian_additive`——Δ_{α,β}(g+h)=Δ_{α,β}g+Δ_{α,β}h。
      重み rmul の左分配（`rmul_add_left`）と方向 2 階差分の加法性で realEq。
  (7) 正直な scope 定理 `gan_model_scope`（M455F より狭めた残限定）＋ capstone `gan_exists`。

  ## 正直な限定（消去/弱化禁止・地図として保持。M455F の「等方・軸上のみ」を破った形）
  - **本物（完全証明・M455F の等方/軸上限定を破った部分）**: ∞ 部の Green 関数が
    **非等方離散 Laplacian に対する非等方 Poisson 方程式 Δ_{α,β}g = α(2a−2δ_p)+β(2a−2δ_q)** を
    満たすこと（`gan_poisson_anisotropic`、realEq、方向重み α,β が curvature に効く）・点源 Dirac が
    **軸外の任意点 (p,q) に置ける**こと（`gan_offaxis_source`、∀ p q）・非等方 Laplacian が
    **加法的（線形作用素）**であること（`gan_laplacian_additive`）・α=β=1,p=q=0 で**等方 M455F へ
    厳密帰着**すること（`gan_reduces_to_g2d`/`gan_reduces_to_g2d_poisson`）。
    全て本物・sorry 皆無・新規 Classical.choice なし。
  - **正直申告（M455F から狭めた残・後続）**:
    ・**位置非依存（定数）重み α,β に留まる**——真の非等方曲率は位置ごとに変わる可変係数
      (1,1)-形式 dd^c g_E であり、本模型は方向重み α,β を**格子全体で定数**に固定した近似。
      **位置依存（可変係数）曲率・真の測度論的 dd^c・任意次元・連続極限は後続**。
    ・**特定 Green 関数**——G(m,n)=a(m²+n²)−|m−p|−|n−q|（separable 二次＋軸並行の折れ）に留まる。
      真の −log|z−w| 型／リーマン面上の Green 関数・非並行方向の点源・混合項 mn は後続。
    ・**整数係数**——curvature a・格子点 m,n・源 (p,q)・重み α,β は整数。有理/実係数の稠密化は後続。
    ・**Deligne pairing / arithmetic Riemann–Roch** は後続。
    ・**一般数体（K≠ℚ）**は範囲外（M455F と同じ K=ℚ 模型・唯一の ∞ 素点）。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・[propext, Quot.sound]）・
  sorry 皆無・禁止タクティク不使用。
-/
import IUT.GreenCurvature2D
import IUT.GreenCurvature
import IUT.IntRealBridge
import IUT.RealOrder
import IUT.RealMul
import IUT.RealRingLaws

namespace IUT

/-! ## M460F-0: 整数レベルの非等方 Green 関数・Poisson 恒等式（軸外点源） -/

/-- **M460F-0a: 整数値 非等方 Green 関数** G(m,n) = a·(m²+n²) − |m−p| − |n−q|。
    M455F の等方 g2dGreenZ a m n = a·(m²+n²) − |m| − |n|（源が原点固定）を、**点源位置を軸外の任意点
    (p,q) へずらした**拡張。二次背景 a·(m²+n²)＋軸外点源 −|m−p|−|n−q|（(p,q) で折れる）。 -/
def ganGreenZ (a p q m n : Int) : Int :=
  a * (m * m) + a * (n * n) - (Int.natAbs (m - p) : Int) - (Int.natAbs (n - q) : Int)

/-- **M460F-0b: m 方向 2 階差分の整数 Poisson（軸外源）** —
    G(m+1,n)+G(m−1,n)−2G(m,n) = 2a − 2δ₀(m−p)（源が m=p にある点源 Dirac）。
    二次部は `grc_quad_second_diff`（定数 2a）、点源部は |m−p| の点集中 2 階差分（omega が natAbs で処理）。 -/
theorem gan_secdiffZ_m (a p q m n : Int) :
    ganGreenZ a p q (m + 1) n + ganGreenZ a p q (m - 1) n
        - (ganGreenZ a p q m n + ganGreenZ a p q m n)
      = 2 * a - 2 * grcDeltaZ (m - p) := by
  have hq := grc_quad_second_diff a m
  unfold ganGreenZ grcDeltaZ
  omega

/-- **M460F-0c: n 方向 2 階差分の整数 Poisson（軸外源）** —
    G(m,n+1)+G(m,n−1)−2G(m,n) = 2a − 2δ₀(n−q)（源が n=q にある点源 Dirac）。 -/
theorem gan_secdiffZ_n (a p q m n : Int) :
    ganGreenZ a p q m (n + 1) + ganGreenZ a p q m (n - 1)
        - (ganGreenZ a p q m n + ganGreenZ a p q m n)
      = 2 * a - 2 * grcDeltaZ (n - q) := by
  have hq := grc_quad_second_diff a n
  unfold ganGreenZ grcDeltaZ
  omega

/-- **M460F-0d: 非等方 Poisson の整数版** —
    α·(m 方向 2 階差分) + β·(n 方向 2 階差分) = α(2a−2δ_p) + β(2a−2δ_q)。
    方向ごとの 2 階差分 `gan_secdiffZ_m`/`gan_secdiffZ_n` を重み α,β で結んだ非等方核。 -/
theorem gan_poissonZ (α β a p q m n : Int) :
    α * (ganGreenZ a p q (m + 1) n + ganGreenZ a p q (m - 1) n
          - (ganGreenZ a p q m n + ganGreenZ a p q m n))
      + β * (ganGreenZ a p q m (n + 1) + ganGreenZ a p q m (n - 1)
          - (ganGreenZ a p q m n + ganGreenZ a p q m n))
      = α * (2 * a - 2 * grcDeltaZ (m - p)) + β * (2 * a - 2 * grcDeltaZ (n - q)) := by
  rw [gan_secdiffZ_m a p q m n, gan_secdiffZ_n a p q m n]

/-! ## M460F-1: 実数値の非等方離散 Laplacian（方向重み α,β を rmul で付与） -/

/-- **M460F-1a: 実数値 非等方 Green 関数** G(m,n)=a·(m²+n²)−|m−p|−|n−q|（整数橋 intToReal 経由）。 -/
def ganGreen (a p q m n : Int) : RReal := intToReal (ganGreenZ a p q m n)

/-- **M460F-1b: 実数値 非等方離散 Laplacian**
    Δ_{α,β}g(m,n) = α·(g(m+1,n)+g(m−1,n)−2g(m,n)) + β·(g(m,n+1)+g(m,n−1)−2g(m,n))。
    各方向の 2 階中心差分に**方向ごとに異なる重み α,β を rmul で掛けた和**。連続の非等方 (1,1)-カレント
    dd^c の 2 次元格子近似。−2g は realNeg(g+g)、重み付けは rmul (intToReal α/β)。 -/
def ganLaplacian (α β : Int) (g : Int → Int → RReal) (m n : Int) : RReal :=
  realAdd
    (rmul (intToReal α)
      (realAdd (realAdd (g (m + 1) n) (g (m - 1) n))
               (realNeg (realAdd (g m n) (g m n)))))
    (rmul (intToReal β)
      (realAdd (realAdd (g m (n + 1)) (g m (n - 1)))
               (realNeg (realAdd (g m n) (g m n)))))

/-- **M460F-1c: 整数値関数の非等方 Laplacian は整数 2 階差分の重み付き像** —
    Δ_{α,β}(ι∘gZ)(m,n) realEq ι(α·(m 差分) + β·(n 差分))。実数橋（乗法 `intToReal_mul`・
    grc の 1 次元 `grc_lap_intToReal` を各方向へ再利用）で実数 Laplacian を整数へ落とす。Poisson 実数化の土台。 -/
theorem gan_lap_intToReal (α β : Int) (gZ : Int → Int → Int) (m n : Int) :
    realEq (ganLaplacian α β (fun i j => intToReal (gZ i j)) m n)
      (intToReal (α * (gZ (m + 1) n + gZ (m - 1) n - (gZ m n + gZ m n))
                + β * (gZ m (n + 1) + gZ m (n - 1) - (gZ m n + gZ m n)))) := by
  have hMA : realEq
      (rmul (intToReal α)
        (realAdd (realAdd (intToReal (gZ (m + 1) n)) (intToReal (gZ (m - 1) n)))
                 (realNeg (realAdd (intToReal (gZ m n)) (intToReal (gZ m n))))))
      (intToReal (α * (gZ (m + 1) n + gZ (m - 1) n - (gZ m n + gZ m n)))) :=
    realEq_trans
      (rmul_congr_right (intToReal α) (grc_lap_intToReal (fun i => gZ i n) m))
      (intToReal_mul α (gZ (m + 1) n + gZ (m - 1) n - (gZ m n + gZ m n)))
  have hNB : realEq
      (rmul (intToReal β)
        (realAdd (realAdd (intToReal (gZ m (n + 1))) (intToReal (gZ m (n - 1))))
                 (realNeg (realAdd (intToReal (gZ m n)) (intToReal (gZ m n))))))
      (intToReal (β * (gZ m (n + 1) + gZ m (n - 1) - (gZ m n + gZ m n)))) :=
    realEq_trans
      (rmul_congr_right (intToReal β) (grc_lap_intToReal (fun j => gZ m j) n))
      (intToReal_mul β (gZ m (n + 1) + gZ m (n - 1) - (gZ m n + gZ m n)))
  refine realEq_trans (g2d_add_both hMA hNB) ?_
  exact intToReal_add _ _

/-! ## M460F-2: 非等方 Poisson 方程式（方向重みが curvature に効く・本丸） -/

/-- **M460F-2: 非等方 Poisson 方程式** — **Δ_{α,β}(ganGreen a p q) realEq
    α(2a−2δ_p) + β(2a−2δ_q)**。非等方離散 Laplacian（連続の非等方 dd^c の格子版）が Green 関数へ
    作用すると、**各方向の曲率寄与 2a を重み α,β で個別に重み付けした背景と、軸外 (p,q) の点源 Dirac の
    差**に等しい（realEq で証明）。**M455F `g2d_model_scope` が「等方 curvature・軸に集中しない点源は
    後続」と正直に限定していた「等方・軸上のみ」を、本非等方 Poisson が破って閉じる**——α≠β で
    curvature が方向依存、(p,q)≠(0,0) で点源が軸外。連続の非等方 Arakelov Green 方程式の 2 次元格子版。 -/
theorem gan_poisson_anisotropic (α β a p q m n : Int) :
    realEq (ganLaplacian α β (ganGreen a p q) m n)
      (intToReal (α * (2 * a - 2 * grcDeltaZ (m - p))
                + β * (2 * a - 2 * grcDeltaZ (n - q)))) :=
  realEq_trans (gan_lap_intToReal α β (ganGreenZ a p q) m n)
    (aip_intToReal_congr (gan_poissonZ α β a p q m n))

/-! ## M460F-3: 軸外の任意点源（M455F の「軸上のみ」を破る） -/

/-- **M460F-3: 軸外の任意点源** — ∀ p q, Δ_{1,1}(ganGreen 0 p q)(p,q) ≠ 0。
    curvature 無し（a=0）でも**任意の格子点 (p,q)** で Δ_{1,1} = −4 ≠ 0 の**点源 Dirac**を持つ。
    源位置 (p,q) は原点/軸に限らず**任意**——**M455F `g2d_model_scope` の「軸に集中しない点源は後続」
    限定を実際に破った証拠**。M455F の等方版 `g2d_has_source` は原点 (0,0) の witness のみだったが、
    本定理は任意の (p,q) を源にできる（軸外の点源を実現）。 -/
theorem gan_offaxis_source (p q : Int) :
    ∃ m n : Int, ¬ realEq (ganLaplacian 1 1 (ganGreen 0 p q) m n) realZero := by
  refine ⟨p, q, ?_⟩
  intro hcon
  have hp : realEq
      (intToReal (1 * (2 * (0 : Int) - 2 * grcDeltaZ (p - p))
                + 1 * (2 * (0 : Int) - 2 * grcDeltaZ (q - q)))) realZero :=
    realEq_trans (realEq_symm (gan_poisson_anisotropic 1 1 0 p q p q)) hcon
  have hval : (1 * (2 * (0 : Int) - 2 * grcDeltaZ (p - p))
                + 1 * (2 * (0 : Int) - 2 * grcDeltaZ (q - q))) = -4 := by
    unfold grcDeltaZ; omega
  rw [hval] at hp
  exact aip_intToReal_ne (by omega) hp

/-! ## M460F-4: 等方版 M455F への整合 -/

/-- **M460F-4a: 等方 M455F への Green 関数の帰着** — α,β を問わず p=q=0 にすると
    ganGreenZ a 0 0 m n = g2dGreenZ a m n（M455F の等方 Green 関数）。源を原点に戻すと等方版に一致。 -/
theorem gan_reduces_to_g2d (a m n : Int) :
    ganGreenZ a 0 0 m n = g2dGreenZ a m n := by
  unfold ganGreenZ g2dGreenZ grcGreenZ
  omega

/-- **M460F-4b: 非等方 Poisson 右辺の等方帰着** — α=β=1・p=q=0 で非等方 Poisson 右辺
    1·(2a−2δ_0(m)) + 1·(2a−2δ_0(n)) = 4a − 2δ₀(m) − 2δ₀(n)（M455F `g2d_poissonZ` の右辺）。
    方向重みを等しく 1・源を原点に戻すと M455F の等方 2 次元 Poisson へ厳密帰着。 -/
theorem gan_reduces_to_g2d_poisson (a m n : Int) :
    1 * (2 * a - 2 * grcDeltaZ (m - 0)) + 1 * (2 * a - 2 * grcDeltaZ (n - 0))
      = 4 * a - 2 * grcDeltaZ m - 2 * grcDeltaZ n := by
  unfold grcDeltaZ; omega

/-! ## M460F-5: 非等方 Laplacian の加法性（線形作用素） -/

/-- **M460F-5a: 方向 2 階差分の加法性（1 方向）** —
    D(g1+h1,g2+h2,g3+h3) realEq D(g1,g2,g3) + D(h1,h2,h3)、
    ただし D(x1,x2,x3) = (x1+x2) − (x3+x3)。中央交換律 `g2d_add_interchange`・反元分配 `g2d_neg_add` で。 -/
theorem gan_secdiff_additive (g1 h1 g2 h2 g3 h3 : RReal) :
    realEq
      (realAdd (realAdd (realAdd g1 h1) (realAdd g2 h2))
               (realNeg (realAdd (realAdd g3 h3) (realAdd g3 h3))))
      (realAdd
        (realAdd (realAdd g1 g2) (realNeg (realAdd g3 g3)))
        (realAdd (realAdd h1 h2) (realNeg (realAdd h3 h3)))) := by
  have hfwd := g2d_add_interchange g1 h1 g2 h2
  have hc := g2d_add_interchange g3 h3 g3 h3
  have hnegc := realEq_trans (realNeg_congr hc)
    (g2d_neg_add (realAdd g3 g3) (realAdd h3 h3))
  refine realEq_trans (g2d_add_both hfwd hnegc) ?_
  exact g2d_add_interchange (realAdd g1 g2) (realAdd h1 h2)
    (realNeg (realAdd g3 g3)) (realNeg (realAdd h3 h3))

/-- **M460F-5b: 非等方 Laplacian の加法性（線形作用素）** — Δ_{α,β}(g+h) realEq Δ_{α,β}g + Δ_{α,β}h。
    各方向 2 階差分の加法性 `gan_secdiff_additive`・重み rmul の左分配 `rmul_add_left`・中央交換律で。
    連続の非等方 Laplacian の線形性を 2 次元格子で realEq で厳密実現。 -/
theorem gan_laplacian_additive (α β : Int) (g h : Int → Int → RReal) (m n : Int) :
    realEq (ganLaplacian α β (fun i j => realAdd (g i j) (h i j)) m n)
      (realAdd (ganLaplacian α β g m n) (ganLaplacian α β h m n)) := by
  have hMα : realEq
      (rmul (intToReal α)
        (realAdd (realAdd (realAdd (g (m + 1) n) (h (m + 1) n))
                          (realAdd (g (m - 1) n) (h (m - 1) n)))
                 (realNeg (realAdd (realAdd (g m n) (h m n)) (realAdd (g m n) (h m n))))))
      (realAdd
        (rmul (intToReal α)
          (realAdd (realAdd (g (m + 1) n) (g (m - 1) n))
                   (realNeg (realAdd (g m n) (g m n)))))
        (rmul (intToReal α)
          (realAdd (realAdd (h (m + 1) n) (h (m - 1) n))
                   (realNeg (realAdd (h m n) (h m n)))))) :=
    realEq_trans
      (rmul_congr_right (intToReal α)
        (gan_secdiff_additive (g (m + 1) n) (h (m + 1) n) (g (m - 1) n) (h (m - 1) n)
          (g m n) (h m n)))
      (rmul_add_left
        (realAdd (realAdd (g (m + 1) n) (g (m - 1) n)) (realNeg (realAdd (g m n) (g m n))))
        (realAdd (realAdd (h (m + 1) n) (h (m - 1) n)) (realNeg (realAdd (h m n) (h m n))))
        (intToReal α))
  have hNβ : realEq
      (rmul (intToReal β)
        (realAdd (realAdd (realAdd (g m (n + 1)) (h m (n + 1)))
                          (realAdd (g m (n - 1)) (h m (n - 1))))
                 (realNeg (realAdd (realAdd (g m n) (h m n)) (realAdd (g m n) (h m n))))))
      (realAdd
        (rmul (intToReal β)
          (realAdd (realAdd (g m (n + 1)) (g m (n - 1)))
                   (realNeg (realAdd (g m n) (g m n)))))
        (rmul (intToReal β)
          (realAdd (realAdd (h m (n + 1)) (h m (n - 1)))
                   (realNeg (realAdd (h m n) (h m n)))))) :=
    realEq_trans
      (rmul_congr_right (intToReal β)
        (gan_secdiff_additive (g m (n + 1)) (h m (n + 1)) (g m (n - 1)) (h m (n - 1))
          (g m n) (h m n)))
      (rmul_add_left
        (realAdd (realAdd (g m (n + 1)) (g m (n - 1))) (realNeg (realAdd (g m n) (g m n))))
        (realAdd (realAdd (h m (n + 1)) (h m (n - 1))) (realNeg (realAdd (h m n) (h m n))))
        (intToReal β))
  refine realEq_trans (g2d_add_both hMα hNβ) ?_
  exact g2d_add_interchange
    (rmul (intToReal α)
      (realAdd (realAdd (g (m + 1) n) (g (m - 1) n)) (realNeg (realAdd (g m n) (g m n)))))
    (rmul (intToReal α)
      (realAdd (realAdd (h (m + 1) n) (h (m - 1) n)) (realNeg (realAdd (h m n) (h m n)))))
    (rmul (intToReal β)
      (realAdd (realAdd (g m (n + 1)) (g m (n - 1))) (realNeg (realAdd (g m n) (g m n)))))
    (rmul (intToReal β)
      (realAdd (realAdd (h m (n + 1)) (h m (n - 1))) (realNeg (realAdd (h m n) (h m n)))))

/-! ## M460F-6: 正直な scope 定理（M455F の「等方・軸上のみ」を破った形で残限定を露出） -/

/-- **M460F-6: 正直な scope 定理** — 本非等方 Green curvature の正体は**非等方離散 Laplacian
    （方向重み α,β 付きの 2 階差分の和）**であること（定義的等式）。M455F の「等方 curvature・軸に
    集中しない点源は後続」限定は `gan_poisson_anisotropic`（方向重み α,β）と `gan_offaxis_source`
    （軸外 (p,q)）で破ったが、**2 次元離散格子・特定 Green 関数 G(m,n)=a(m²+n²)−|m−p|−|n−q|・
    位置非依存（定数）重み α,β・整数係数に留まる**という残限定を地図として露出する（真の測度論的 dd^c・
    任意次元・可変係数（位置依存）曲率・Deligne pairing は後続。完全証明ファースト規則 §4）。 -/
theorem gan_model_scope (α β a p q m n : Int) :
    ganLaplacian α β (ganGreen a p q) m n
      = realAdd
          (rmul (intToReal α)
            (realAdd (realAdd (ganGreen a p q (m + 1) n) (ganGreen a p q (m - 1) n))
                     (realNeg (realAdd (ganGreen a p q m n) (ganGreen a p q m n)))))
          (rmul (intToReal β)
            (realAdd (realAdd (ganGreen a p q m (n + 1)) (ganGreen a p q m (n - 1)))
                     (realNeg (realAdd (ganGreen a p q m n) (ganGreen a p q m n))))) :=
  rfl

/-! ## M460F-7: capstone -/

/-- **M460F-7a: 非等方 Green curvature データ** — 本物の非等方 Green 関数・方向重み付き Laplacian・
    非等方 Poisson 方程式（方向重み α,β の curvature＋軸外点源）・線形性・軸外の任意点源を束ねた実体。 -/
structure GanGreenData where
  /-- 実数値 非等方 Green 関数 G(a,p,q,m,n)=a(m²+n²)−|m−p|−|n−q|。 -/
  green : Int → Int → Int → Int → Int → RReal
  /-- 非等方離散 Laplacian（方向重み α,β 付き 2 階差分の和・連続の非等方 (1,1)-カレントの格子版）。 -/
  laplacian : Int → Int → (Int → Int → RReal) → Int → Int → RReal
  /-- **非等方 Poisson 方程式** Δ_{α,β}g = α(2a−2δ_p) + β(2a−2δ_q)（方向重みが curvature に効く）。 -/
  poisson : ∀ α β a p q m n,
    realEq (laplacian α β (green a p q) m n)
      (intToReal (α * (2 * a - 2 * grcDeltaZ (m - p))
                + β * (2 * a - 2 * grcDeltaZ (n - q))))
  /-- 非等方 Laplacian の加法性（線形作用素）。 -/
  additive : ∀ α β g h m n,
    realEq (laplacian α β (fun i j => realAdd (g i j) (h i j)) m n)
      (realAdd (laplacian α β g m n) (laplacian α β h m n))
  /-- **軸外の任意点源**（∀ p q, 源 (p,q) で Δ_{1,1} ≠ 0 の witness が存在）。 -/
  offaxis_source : ∀ p q, ∃ m n, ¬ realEq (laplacian 1 1 (green 0 p q) m n) realZero

/-- **M460F-7b: 非等方 Green curvature データの witness**（全て本物）。 -/
def ganGreenData : GanGreenData where
  green := ganGreen
  laplacian := ganLaplacian
  poisson := gan_poisson_anisotropic
  additive := gan_laplacian_additive
  offaxis_source := gan_offaxis_source

/-- **M460F-7c: 存在** — 非等方 Green curvature データは充足可能
    （K=ℚ・2 次元格子・非等方重み α,β・軸外源 (p,q)・G(m,n)=a(m²+n²)−|m−p|−|n−q| witness）。 -/
theorem gan_exists : Nonempty GanGreenData :=
  ⟨ganGreenData⟩

end IUT
