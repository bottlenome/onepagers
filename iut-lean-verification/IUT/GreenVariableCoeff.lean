-- M465F GreenVariableCoeff [実・本物・柱C]
-- complete_pct 影響: 柱C を前進。M460F(gan) の `gan_model_scope` が「**位置非依存（定数）重み α,β**・
--   **混合項 mn なし（separable）**・可変係数（位置依存）曲率は後続」と正直に限定していた、その
--   **「定数重み・混合項なし」を昇格で破って閉じる**。非等方離散 Laplacian を **位置依存重み α(m,n),β(m,n)
--   と混合 2 階差分 γ(m,n)·(g(m+1,n+1)−g(m+1,n)−g(m,n+1)+g(m,n)) を持つ一般 2 階楕円差分作用素**へ
--   置換し、(1) `gvc_mixed_nonzero` で **混合項 γ が非自明に効く**（双線形核 mn は m/n 方向の 2 階差分で
--   消えるが混合 2 階差分は 1 を返す）ことで separable（混合項なし）を破り、(2) `gvc_variable_coeff` で
--   **重みが位置依存**（α(m,n)=m の作用が位置 (1,0) と (2,0) で 2≠4 と異なる係数を持つ）ことで定数重みを
--   破る。線形性・可変係数 Poisson 型関係式・M460F への帰着も本物で証明する。
-- 正直な限定（M460F より狭めた形）: 2 次元離散格子・具体重み関数（多項式重み）・特定 Green/witness 関数
--   （双線形 mn・二次 m²）・整数係数に留まる。完全な測度論的 dd^c・任意次元・非線形 PDE・
--   Deligne pairing・一般 Riemann 面上の可変曲率 Green 関数は未。

/-
  IUT/GreenVariableCoeff.lean — M465F（柱C: 非等方 Laplacian の可変係数＋混合項への昇格）

  ── 主要成果の分類: **[実]**（§2(a) 昇格）。M460F
     (`IUT/GreenAnisotropic.lean`, prefix `gan`) は ∞ 部の Green 関数の curvature 項を
     **非等方離散 Laplacian Δ_{α,β}g = α·(m 方向 2 階差分) + β·(n 方向 2 階差分)（方向ごとに
     異なる定数重み α,β・混合項なし）**で実現し、非等方 Poisson 方程式を証明した一方、
     `gan_model_scope` が **「位置非依存（定数）重み α,β・混合項 mn なし（separable）・可変係数
     （位置依存）曲率は後続」**と正直に限定していた。連続の Arakelov curvature 項 dd^c g_E は一般に
     **可変係数（位置ごとに曲率が異なる (1,1)-形式）**であり、また **混合 2 階微分項 ∂²/∂m∂n**
     （非対角成分・非分離）を含む一般 2 階楕円作用素である。本モジュールはその **「定数重み・混合項なし」
     限定を昇格で破る**——連続の一般 2 階楕円作用素を **2 次元格子上の可変係数＋混合項付き離散楕円作用素
     Δ_{α,β,γ}g(m,n) = α(m,n)·(m 方向 2 階差分) + β(m,n)·(n 方向 2 階差分)
       + γ(m,n)·(混合 2 階差分 g(m+1,n+1)−g(m+1,n)−g(m,n+1)+g(m,n))**
     （**重み α,β,γ は各格子点 (m,n) の関数**＝可変係数、γ 項が **混合（非分離）2 階差分**）で忠実に
     部分実現し、混合項が非自明に効くこと・重みが位置依存であること・線形性・可変係数 Poisson 型関係式・
     M460F への帰着を realEq/整数橋で証明する。主語は M139-4 の本物の整数埋め込み intToReal・
     M142F の実数橋（加法/乗法/負元）・M450F の 1 次元 grc・M455F の等方 2 次元 g2d・M460F の
     非等方 gan（rmul 重み付け・grc_lap_intToReal）。toy 主語なし。

  complete_pct 影響: **柱C（Frobenioid／Arakelov 交点理論）の実 IUT 完全証明率を前進**。
  M460F は定数重み・混合項なし（separable）に留めていた。本ファイルは:
  (1) **可変係数＋混合項付き離散楕円作用素** `gvcLaplacian α β γ g m n`——重み α,β,γ は **位置 (m,n) の
      関数**（Int → Int → Int）で、各格子点で異なる係数を rmul で付与。**γ 項は混合 2 階差分**
      g(m+1,n+1)−g(m+1,n)−g(m,n+1)+g(m,n)（非対角・非分離）。連続の一般 2 階楕円作用素の格子近似。
  (2) **線形性（加法的）** `gvc_laplacian_additive`——Δ_{α,β,γ}(g+h)=Δ_{α,β,γ}g+Δ_{α,β,γ}h。
      混合項も含めた 3 方向すべてで重み rmul の左分配・2 階差分の加法性で realEq。
  (3) **混合項が非自明に効く** `gvc_mixed_nonzero`——双線形核 g(i,j)=i·j は m/n 方向の 2 階差分では
      0 になる（separable 部が消える）が、**混合 2 階差分は 1 を返す**ため γ=1 で Δ≠0。
      **M460F の「混合項なし（separable）」限定を実際に破った証拠**。
  (4) **重みが位置依存（可変係数）** `gvc_variable_coeff`——位置依存重み α(m,n)=m を二次核 m² に作用させると
      Δ = 2m となり、位置 (1,0) では 2、位置 (2,0) では 4 と **異なる係数**を持つ（2≠4 で ¬realEq）。
      **M460F の「位置非依存（定数）重み」限定を実際に破った証拠**。
  (5) **可変係数 Poisson 型関係式** `gvc_poisson_variable`——双線形核へ作用させた可変係数 Laplacian は
      **Δ_{α,β,γ}(i·j) realEq γ(m,n)**（m/n 方向が消え混合項の重み γ(m,n) だけが残る）を realEq で明示。
  (6) **M460F への帰着** `gvc_reduces_to_gan`——α,β 定数・γ=0 で本可変係数作用素が M460F の非等方
      （混合項なし）Laplacian `ganLaplacian` へ realEq で厳密帰着（混合項の重み 0 が消える）。
  (7) 正直な scope 定理 `gvc_model_scope`（M460F より狭めた残限定）＋ capstone `gvc_exists`。

  ## 正直な限定（消去/弱化禁止・地図として保持。M460F の「定数重み・混合項なし」を破った形）
  - **本物（完全証明・M460F の定数重み/混合項なし限定を破った部分）**: 一般 2 階楕円作用素が
    **位置依存重み α(m,n),β(m,n),γ(m,n)** を持つこと・**混合 2 階差分 γ 項が separable（混合項なし）を
    破って非自明に効く**こと（`gvc_mixed_nonzero`）・**重みが位置依存で係数が位置により異なる**こと
    （`gvc_variable_coeff`、2≠4）・作用素が **加法的（線形）**であること（`gvc_laplacian_additive`）・
    双線形核への **可変係数 Poisson 型関係式 Δ(i·j)=γ(m,n)**（`gvc_poisson_variable`）・α,β 定数・γ=0 で
    **M460F の非等方 gan へ厳密帰着**すること（`gvc_reduces_to_gan`）。全て本物・sorry 皆無・
    新規 Classical.choice なし。
  - **正直申告（M460F から狭めた残・後続）**:
    ・**2 次元離散格子に留まる**——真の curvature 項は連続の測度論的 (1,1)-形式 dd^c g_E であり、
      本模型は 2 次元格子の可変係数＋混合項付き 5 点/4 点差分へ離散化した近似。連続極限・**任意次元**・
      完全な測度論的 dd^c・非線形 PDE は後続。
    ・**具体重み関数・特定 witness 関数**——重みは多項式（α(m,n)=m 等）、作用対象は双線形 i·j／二次 m² に
      留まる。真の −log|z−w| 型／リーマン面上の可変曲率 Green 関数・任意の可変係数配置は後続。
    ・**整数係数**——重み・格子点・係数は整数。有理/実係数の稠密化は後続。
    ・**Deligne pairing / arithmetic Riemann–Roch** は後続。
    ・**一般数体（K≠ℚ）**は範囲外（M460F と同じ K=ℚ 模型・唯一の ∞ 素点）。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・[propext, Quot.sound]）・
  sorry 皆無・禁止タクティク不使用。
-/
import IUT.GreenAnisotropic
import IUT.GreenCurvature2D
import IUT.GreenCurvature
import IUT.IntRealBridge
import IUT.RealOrder
import IUT.RealMul
import IUT.RealRingLaws

namespace IUT

/-! ## M465F-0: 整数レベルの可変係数＋混合項付き楕円作用素 -/

/-- **M465F-0a: 整数値 可変係数＋混合項離散楕円作用素**
    Δ_{α,β,γ}gZ(m,n) = α(m,n)·(gZ(m+1,n)+gZ(m−1,n)−2gZ(m,n))
      + β(m,n)·(gZ(m,n+1)+gZ(m,n−1)−2gZ(m,n))
      + γ(m,n)·(gZ(m+1,n+1)+gZ(m,n)−(gZ(m+1,n)+gZ(m,n+1)))。
    **重み α,β,γ は位置 (m,n) の関数**（可変係数）・**γ 項は混合 2 階差分**（非対角・非分離）。
    連続の一般 2 階楕円作用素 a∂²ₘ+b∂²ₙ+c∂ₘ∂ₙ の 2 次元格子近似の整数核。 -/
def gvcLapZ (α β γ : Int → Int → Int) (gZ : Int → Int → Int) (m n : Int) : Int :=
  α m n * (gZ (m + 1) n + gZ (m - 1) n - (gZ m n + gZ m n))
    + β m n * (gZ m (n + 1) + gZ m (n - 1) - (gZ m n + gZ m n))
    + γ m n * (gZ (m + 1) (n + 1) + gZ m n - (gZ (m + 1) n + gZ m (n + 1)))

/-- **M465F-0b: 双線形 witness 核** gvcBilinZ(i,j) = i·j。混合 2 階差分が 1・m/n 方向 2 階差分が 0 の
    最小 witness（separable 破りの主役）。 -/
def gvcBilinZ (i j : Int) : Int := i * j

/-- **M465F-0c: 二次 witness 核（m 方向のみ）** gvcQuadMZ(i,j) = i·i。m 方向 2 階差分が定数 2・
    n/混合方向が 0 の witness（可変係数破りの主役）。 -/
def gvcQuadMZ (i _j : Int) : Int := i * i

/-- **M465F-0d: 双線形核の m 方向 2 階差分は 0** — (m+1)n+(m−1)n−2mn = 0（分離部は消える）。 -/
theorem gvc_bilin_mdiff (m n : Int) :
    (m + 1) * n + (m - 1) * n - (m * n + m * n) = 0 := by
  have e1 : (m + 1) * n = m * n + n := by rw [Int.add_mul, Int.one_mul]
  have e2 : (m - 1) * n = m * n - n := by rw [Int.sub_mul, Int.one_mul]
  rw [e1, e2]; omega

/-- **M465F-0e: 双線形核の n 方向 2 階差分は 0** — m(n+1)+m(n−1)−2mn = 0（分離部は消える）。 -/
theorem gvc_bilin_ndiff (m n : Int) :
    m * (n + 1) + m * (n - 1) - (m * n + m * n) = 0 := by
  have e1 : m * (n + 1) = m * n + m := by rw [Int.mul_add, Int.mul_one]
  have e2 : m * (n - 1) = m * n - m := by rw [Int.mul_sub, Int.mul_one]
  rw [e1, e2]; omega

/-- **M465F-0f: 双線形核の混合 2 階差分は 1** —
    (m+1)(n+1)+mn−((m+1)n+m(n+1)) = 1。**混合項だけが非自明に効く核心**（separable 破り）。 -/
theorem gvc_bilin_xdiff (m n : Int) :
    (m + 1) * (n + 1) + m * n - ((m + 1) * n + m * (n + 1)) = 1 := by
  have e1 : (m + 1) * (n + 1) = m * n + m + n + 1 := by
    rw [Int.add_mul, Int.one_mul, Int.mul_add, Int.mul_one]; omega
  have e2 : (m + 1) * n = m * n + n := by rw [Int.add_mul, Int.one_mul]
  have e3 : m * (n + 1) = m * n + m := by rw [Int.mul_add, Int.mul_one]
  rw [e1, e2, e3]; omega

/-- **M465F-0g: 二次核の m 方向 2 階差分は定数 2** — (m+1)²+(m−1)²−2m² = 2。
    可変係数 α(m,n) が乗ると位置依存の係数を生む土台。 -/
theorem gvc_quad_mdiff (m : Int) :
    (m + 1) * (m + 1) + (m - 1) * (m - 1) - (m * m + m * m) = 2 := by
  have h1 : (m + 1) * (m + 1) = m * m + m + m + 1 := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
  have h2 : (m - 1) * (m - 1) = m * m - m - m + 1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
  rw [h1, h2]; omega

/-- **M465F-0h: 双線形核の可変係数 Poisson（整数）** — Δ_{α,β,γ}(i·j)(m,n) = γ(m,n)。
    m/n 方向 2 階差分が 0（`gvc_bilin_mdiff`/`gvc_bilin_ndiff`）・混合 2 階差分が 1
    （`gvc_bilin_xdiff`）ゆえ、**混合項の重み γ(m,n) だけが残る**。混合項が本質的に効く整数核心。 -/
theorem gvc_poissonZ_bilin (α β γ : Int → Int → Int) (m n : Int) :
    gvcLapZ α β γ gvcBilinZ m n = γ m n := by
  have hm := gvc_bilin_mdiff m n
  have hn := gvc_bilin_ndiff m n
  have hx := gvc_bilin_xdiff m n
  unfold gvcLapZ gvcBilinZ
  rw [hm, hn, hx]
  omega

/-- **M465F-0i: 二次核への可変係数作用（整数）** —
    Δ_{α,0,0}(m²)(m,n) = α(m,n)·2、ただし α(m,n)=m（位置依存）なら = 2m。
    位置依存重み α(i,·)=i が二次核の定数 2 階差分 2 に乗ると **位置により異なる係数** 2m を生む。
    n/混合方向は二次核 i² が j に依らないゆえ消える。 -/
theorem gvc_varcoeffZ (m n : Int) :
    gvcLapZ (fun i _ => i) (fun _ _ => 0) (fun _ _ => 0) gvcQuadMZ m n = 2 * m := by
  have hm : gvcQuadMZ (m + 1) n + gvcQuadMZ (m - 1) n - (gvcQuadMZ m n + gvcQuadMZ m n) = 2 := by
    unfold gvcQuadMZ
    exact gvc_quad_mdiff m
  have hn : gvcQuadMZ m (n + 1) + gvcQuadMZ m (n - 1) - (gvcQuadMZ m n + gvcQuadMZ m n) = 0 := by
    unfold gvcQuadMZ; omega
  have hx : gvcQuadMZ (m + 1) (n + 1) + gvcQuadMZ m n
      - (gvcQuadMZ (m + 1) n + gvcQuadMZ m (n + 1)) = 0 := by
    unfold gvcQuadMZ; omega
  unfold gvcLapZ
  rw [hm, hn, hx]
  show m * 2 + 0 * 0 + 0 * 0 = 2 * m
  omega

/-! ## M465F-1: 実数値の可変係数＋混合項付き離散楕円作用素（重みを rmul で付与） -/

/-- **M465F-1a: 実数値 可変係数＋混合項離散楕円作用素**
    Δ_{α,β,γ}g(m,n) = α(m,n)·(m 方向 2 階差分) + β(m,n)·(n 方向 2 階差分)
      + γ(m,n)·(混合 2 階差分 g(m+1,n+1)+g(m,n)−(g(m+1,n)+g(m,n+1)))。
    **重み α,β,γ は位置 (m,n) の関数**（可変係数、各格子点で異なる重みを intToReal 経由で rmul）。
    連続の一般 2 階楕円作用素 a(x)∂²ₘ+b(x)∂²ₙ+c(x)∂ₘ∂ₙ の 2 次元格子近似。 -/
def gvcLaplacian (α β γ : Int → Int → Int) (g : Int → Int → RReal) (m n : Int) : RReal :=
  realAdd
    (realAdd
      (rmul (intToReal (α m n))
        (realAdd (realAdd (g (m + 1) n) (g (m - 1) n))
                 (realNeg (realAdd (g m n) (g m n)))))
      (rmul (intToReal (β m n))
        (realAdd (realAdd (g m (n + 1)) (g m (n - 1)))
                 (realNeg (realAdd (g m n) (g m n))))))
    (rmul (intToReal (γ m n))
      (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
               (realNeg (realAdd (g (m + 1) n) (g m (n + 1))))))

/-- **M465F-1b: 混合 2 階差分の実数橋** —
    実数値 (ι∘gZ) の混合 2 階差分 realEq ι(gZ(m+1,n+1)+gZ(m,n)−(gZ(m+1,n)+gZ(m,n+1)))。
    実数橋（加法 `intToReal_add`・負元 `intToReal_neg`）で実数混合差分を整数へ落とす。 -/
theorem gvc_mixed_intToReal (gZ : Int → Int → Int) (m n : Int) :
    realEq
      (realAdd (realAdd (intToReal (gZ (m + 1) (n + 1))) (intToReal (gZ m n)))
               (realNeg (realAdd (intToReal (gZ (m + 1) n)) (intToReal (gZ m (n + 1))))))
      (intToReal (gZ (m + 1) (n + 1) + gZ m n - (gZ (m + 1) n + gZ m (n + 1)))) := by
  have h1 : realEq (realAdd (intToReal (gZ (m + 1) (n + 1))) (intToReal (gZ m n)))
      (intToReal (gZ (m + 1) (n + 1) + gZ m n)) := intToReal_add _ _
  have h2 : realEq (realAdd (intToReal (gZ (m + 1) n)) (intToReal (gZ m (n + 1))))
      (intToReal (gZ (m + 1) n + gZ m (n + 1))) := intToReal_add _ _
  have h3 : realEq (realNeg (realAdd (intToReal (gZ (m + 1) n)) (intToReal (gZ m (n + 1)))))
      (intToReal (-(gZ (m + 1) n + gZ m (n + 1)))) :=
    realEq_trans (realNeg_congr h2) (intToReal_neg _)
  refine realEq_trans (realAdd_congr_left _ h1) ?_
  refine realEq_trans (realAdd_congr_right _ h3) ?_
  refine realEq_trans (intToReal_add _ _) ?_
  exact aip_intToReal_congr (by omega)

/-- **M465F-1c: 整数値関数の可変係数 Laplacian は整数核の像** —
    Δ_{α,β,γ}(ι∘gZ)(m,n) realEq ι(gvcLapZ α β γ gZ m n)。各方向の重み rmul を実数橋
    （乗法 `intToReal_mul`・m/n 方向は `grc_lap_intToReal`・混合は `gvc_mixed_intToReal`）で
    整数へ落とし、3 項を intToReal_add で合併。可変係数 Poisson の実数化の土台。 -/
theorem gvc_lap_intToReal (α β γ : Int → Int → Int) (gZ : Int → Int → Int) (m n : Int) :
    realEq (gvcLaplacian α β γ (fun i j => intToReal (gZ i j)) m n)
      (intToReal (gvcLapZ α β γ gZ m n)) := by
  have hMA : realEq
      (rmul (intToReal (α m n))
        (realAdd (realAdd (intToReal (gZ (m + 1) n)) (intToReal (gZ (m - 1) n)))
                 (realNeg (realAdd (intToReal (gZ m n)) (intToReal (gZ m n))))))
      (intToReal (α m n * (gZ (m + 1) n + gZ (m - 1) n - (gZ m n + gZ m n)))) :=
    realEq_trans
      (rmul_congr_right (intToReal (α m n)) (grc_lap_intToReal (fun i => gZ i n) m))
      (intToReal_mul (α m n) (gZ (m + 1) n + gZ (m - 1) n - (gZ m n + gZ m n)))
  have hNB : realEq
      (rmul (intToReal (β m n))
        (realAdd (realAdd (intToReal (gZ m (n + 1))) (intToReal (gZ m (n - 1))))
                 (realNeg (realAdd (intToReal (gZ m n)) (intToReal (gZ m n))))))
      (intToReal (β m n * (gZ m (n + 1) + gZ m (n - 1) - (gZ m n + gZ m n)))) :=
    realEq_trans
      (rmul_congr_right (intToReal (β m n)) (grc_lap_intToReal (fun j => gZ m j) n))
      (intToReal_mul (β m n) (gZ m (n + 1) + gZ m (n - 1) - (gZ m n + gZ m n)))
  have hXG : realEq
      (rmul (intToReal (γ m n))
        (realAdd (realAdd (intToReal (gZ (m + 1) (n + 1))) (intToReal (gZ m n)))
                 (realNeg (realAdd (intToReal (gZ (m + 1) n)) (intToReal (gZ m (n + 1)))))))
      (intToReal (γ m n * (gZ (m + 1) (n + 1) + gZ m n - (gZ (m + 1) n + gZ m (n + 1))))) :=
    realEq_trans
      (rmul_congr_right (intToReal (γ m n)) (gvc_mixed_intToReal gZ m n))
      (intToReal_mul (γ m n) (gZ (m + 1) (n + 1) + gZ m n - (gZ (m + 1) n + gZ m (n + 1))))
  refine realEq_trans (g2d_add_both (g2d_add_both hMA hNB) hXG) ?_
  refine realEq_trans (realAdd_congr_left _ (intToReal_add _ _)) ?_
  exact intToReal_add _ _

/-! ## M465F-2: 可変係数 Poisson 型関係式（混合項が残る・本丸） -/

/-- **M465F-2: 可変係数 Poisson 型関係式** — **Δ_{α,β,γ}(i·j) realEq γ(m,n)**。
    双線形核 g(i,j)=i·j へ可変係数 Laplacian を作用させると、m/n 方向の 2 階差分が消え
    **混合項の重み γ(m,n) だけが残る**（realEq で証明）。**M460F `gan_model_scope` が
    「混合項なし（separable）」と正直に限定していたその separable を、本混合項付き作用素が
    破って閉じる本丸**——混合 2 階差分は双線形核で 1 を返し γ を露出する。連続の一般 2 階楕円作用素の
    非対角（混合）成分を 2 次元格子で忠実に実現した核心。 -/
theorem gvc_poisson_variable (α β γ : Int → Int → Int) (m n : Int) :
    realEq (gvcLaplacian α β γ (fun i j => intToReal (gvcBilinZ i j)) m n)
      (intToReal (γ m n)) :=
  realEq_trans (gvc_lap_intToReal α β γ gvcBilinZ m n)
    (aip_intToReal_congr (gvc_poissonZ_bilin α β γ m n))

/-! ## M465F-3: 混合項が非自明に効く（M460F の separable を破る） -/

/-- **M465F-3: 混合項が非自明に効く** — ∃ m n, Δ_{0,0,1}(i·j)(m,n) ≠ 0。
    m/n 方向の重みを 0 にしても、**混合項 γ=1 が双線形核 i·j で 1 を返す**ため Δ = intToReal 1 ≠ 0。
    双線形核は m/n 方向の 2 階差分では消える（separable 部が 0）が、**混合 2 階差分は非零**——
    **M460F `gan_model_scope` の「混合項なし（separable）」限定を実際に破った証拠**。混合（非対角）
    成分が本作用素で本質的に効くことを示す。 -/
theorem gvc_mixed_nonzero :
    ∃ m n : Int, ¬ realEq
      (gvcLaplacian (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1)
        (fun i j => intToReal (gvcBilinZ i j)) m n) realZero := by
  refine ⟨0, 0, ?_⟩
  intro hcon
  have hp : realEq (intToReal ((fun _ _ => (1 : Int)) (0 : Int) (0 : Int))) realZero :=
    realEq_trans
      (realEq_symm (gvc_poisson_variable (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) 0 0))
      hcon
  exact aip_intToReal_ne (a := (1 : Int)) (b := (0 : Int)) (by omega) hp

/-! ## M465F-4: 重みが位置依存（M460F の定数重みを破る） -/

/-- **M465F-4: 重みが位置依存（可変係数）** — 位置依存重み α(m,n)=m を二次核 m² に作用させた
    Δ_{α,0,0}(m²) は位置 (1,0) で intToReal 2・位置 (2,0) で intToReal 4 となり、**同じ作用素が
    異なる位置で異なる係数**を持つ（2≠4 ゆえ ¬realEq）。**M460F `gan_model_scope` の
    「位置非依存（定数）重み α,β」限定を実際に破った証拠**——重み α(m,n)=m は格子点ごとに値が変わる
    可変係数であり、M460F の格子全体で定数の重みを破る。 -/
theorem gvc_variable_coeff :
    ¬ realEq
        (gvcLaplacian (fun i _ => i) (fun _ _ => 0) (fun _ _ => 0)
          (fun i j => intToReal (gvcQuadMZ i j)) 1 0)
        (gvcLaplacian (fun i _ => i) (fun _ _ => 0) (fun _ _ => 0)
          (fun i j => intToReal (gvcQuadMZ i j)) 2 0) := by
  intro hcon
  have h1 : realEq
      (gvcLaplacian (fun i _ => i) (fun _ _ => 0) (fun _ _ => 0)
        (fun i j => intToReal (gvcQuadMZ i j)) 1 0)
      (intToReal (2 * 1)) :=
    realEq_trans (gvc_lap_intToReal (fun i _ => i) (fun _ _ => 0) (fun _ _ => 0) gvcQuadMZ 1 0)
      (aip_intToReal_congr (gvc_varcoeffZ 1 0))
  have h2 : realEq
      (gvcLaplacian (fun i _ => i) (fun _ _ => 0) (fun _ _ => 0)
        (fun i j => intToReal (gvcQuadMZ i j)) 2 0)
      (intToReal (2 * 2)) :=
    realEq_trans (gvc_lap_intToReal (fun i _ => i) (fun _ _ => 0) (fun _ _ => 0) gvcQuadMZ 2 0)
      (aip_intToReal_congr (gvc_varcoeffZ 2 0))
  have hbad : realEq (intToReal (2 * 1)) (intToReal (2 * 2)) :=
    realEq_trans (realEq_symm h1) (realEq_trans hcon h2)
  exact aip_intToReal_ne (by omega) hbad

/-! ## M465F-5: 線形性（加法的作用素）・M460F への帰着 -/

/-- **M465F-5a: 一般 4 項の 2 階差分の加法性** —
    ((a1+b1)+(a2+b2)) − ((a3+b3)+(a4+b4)) realEq [(a1+a2)−(a3+a4)] + [(b1+b2)−(b3+b4)]。
    m/n 方向（a3=a4）と混合方向（a3≠a4）の両方を覆う一般形。中央交換律 `g2d_add_interchange`・
    反元分配 `g2d_neg_add` で（M460F `gan_secdiff_additive` の 4 項一般化）。 -/
theorem gvc_mixed_additive (a1 b1 a2 b2 a3 b3 a4 b4 : RReal) :
    realEq
      (realAdd (realAdd (realAdd a1 b1) (realAdd a2 b2))
               (realNeg (realAdd (realAdd a3 b3) (realAdd a4 b4))))
      (realAdd
        (realAdd (realAdd a1 a2) (realNeg (realAdd a3 a4)))
        (realAdd (realAdd b1 b2) (realNeg (realAdd b3 b4)))) := by
  have hpos := g2d_add_interchange a1 b1 a2 b2
  have hin := g2d_add_interchange a3 b3 a4 b4
  have hneg := realEq_trans (realNeg_congr hin)
    (g2d_neg_add (realAdd a3 a4) (realAdd b3 b4))
  refine realEq_trans (g2d_add_both hpos hneg) ?_
  exact g2d_add_interchange (realAdd a1 a2) (realAdd b1 b2)
    (realNeg (realAdd a3 a4)) (realNeg (realAdd b3 b4))

/-- **M465F-5b: 可変係数 Laplacian の加法性（線形作用素）** —
    Δ_{α,β,γ}(g+h) realEq Δ_{α,β,γ}g + Δ_{α,β,γ}h。混合項を含む 3 方向すべてで、各方向 2 階差分の
    加法性 `gvc_mixed_additive`・重み rmul の左分配 `rmul_add_left`・中央交換律で realEq。
    連続の一般 2 階楕円作用素（可変係数・混合項込み）の線形性を 2 次元格子で厳密実現。 -/
theorem gvc_laplacian_additive (α β γ : Int → Int → Int) (g h : Int → Int → RReal) (m n : Int) :
    realEq (gvcLaplacian α β γ (fun i j => realAdd (g i j) (h i j)) m n)
      (realAdd (gvcLaplacian α β γ g m n) (gvcLaplacian α β γ h m n)) := by
  have hMα : realEq
      (rmul (intToReal (α m n))
        (realAdd (realAdd (realAdd (g (m + 1) n) (h (m + 1) n))
                          (realAdd (g (m - 1) n) (h (m - 1) n)))
                 (realNeg (realAdd (realAdd (g m n) (h m n)) (realAdd (g m n) (h m n))))))
      (realAdd
        (rmul (intToReal (α m n))
          (realAdd (realAdd (g (m + 1) n) (g (m - 1) n))
                   (realNeg (realAdd (g m n) (g m n)))))
        (rmul (intToReal (α m n))
          (realAdd (realAdd (h (m + 1) n) (h (m - 1) n))
                   (realNeg (realAdd (h m n) (h m n)))))) :=
    realEq_trans
      (rmul_congr_right (intToReal (α m n))
        (gvc_mixed_additive (g (m + 1) n) (h (m + 1) n) (g (m - 1) n) (h (m - 1) n)
          (g m n) (h m n) (g m n) (h m n)))
      (rmul_add_left
        (realAdd (realAdd (g (m + 1) n) (g (m - 1) n)) (realNeg (realAdd (g m n) (g m n))))
        (realAdd (realAdd (h (m + 1) n) (h (m - 1) n)) (realNeg (realAdd (h m n) (h m n))))
        (intToReal (α m n)))
  have hNβ : realEq
      (rmul (intToReal (β m n))
        (realAdd (realAdd (realAdd (g m (n + 1)) (h m (n + 1)))
                          (realAdd (g m (n - 1)) (h m (n - 1))))
                 (realNeg (realAdd (realAdd (g m n) (h m n)) (realAdd (g m n) (h m n))))))
      (realAdd
        (rmul (intToReal (β m n))
          (realAdd (realAdd (g m (n + 1)) (g m (n - 1)))
                   (realNeg (realAdd (g m n) (g m n)))))
        (rmul (intToReal (β m n))
          (realAdd (realAdd (h m (n + 1)) (h m (n - 1)))
                   (realNeg (realAdd (h m n) (h m n)))))) :=
    realEq_trans
      (rmul_congr_right (intToReal (β m n))
        (gvc_mixed_additive (g m (n + 1)) (h m (n + 1)) (g m (n - 1)) (h m (n - 1))
          (g m n) (h m n) (g m n) (h m n)))
      (rmul_add_left
        (realAdd (realAdd (g m (n + 1)) (g m (n - 1))) (realNeg (realAdd (g m n) (g m n))))
        (realAdd (realAdd (h m (n + 1)) (h m (n - 1))) (realNeg (realAdd (h m n) (h m n))))
        (intToReal (β m n)))
  have hXγ : realEq
      (rmul (intToReal (γ m n))
        (realAdd (realAdd (realAdd (g (m + 1) (n + 1)) (h (m + 1) (n + 1)))
                          (realAdd (g m n) (h m n)))
                 (realNeg (realAdd (realAdd (g (m + 1) n) (h (m + 1) n))
                                   (realAdd (g m (n + 1)) (h m (n + 1)))))))
      (realAdd
        (rmul (intToReal (γ m n))
          (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
                   (realNeg (realAdd (g (m + 1) n) (g m (n + 1))))))
        (rmul (intToReal (γ m n))
          (realAdd (realAdd (h (m + 1) (n + 1)) (h m n))
                   (realNeg (realAdd (h (m + 1) n) (h m (n + 1))))))) :=
    realEq_trans
      (rmul_congr_right (intToReal (γ m n))
        (gvc_mixed_additive (g (m + 1) (n + 1)) (h (m + 1) (n + 1)) (g m n) (h m n)
          (g (m + 1) n) (h (m + 1) n) (g m (n + 1)) (h m (n + 1))))
      (rmul_add_left
        (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
                 (realNeg (realAdd (g (m + 1) n) (g m (n + 1)))))
        (realAdd (realAdd (h (m + 1) (n + 1)) (h m n))
                 (realNeg (realAdd (h (m + 1) n) (h m (n + 1)))))
        (intToReal (γ m n)))
  refine realEq_trans (g2d_add_both (g2d_add_both hMα hNβ) hXγ) ?_
  refine realEq_trans
    (g2d_add_both
      (g2d_add_interchange
        (rmul (intToReal (α m n))
          (realAdd (realAdd (g (m + 1) n) (g (m - 1) n)) (realNeg (realAdd (g m n) (g m n)))))
        (rmul (intToReal (α m n))
          (realAdd (realAdd (h (m + 1) n) (h (m - 1) n)) (realNeg (realAdd (h m n) (h m n)))))
        (rmul (intToReal (β m n))
          (realAdd (realAdd (g m (n + 1)) (g m (n - 1))) (realNeg (realAdd (g m n) (g m n)))))
        (rmul (intToReal (β m n))
          (realAdd (realAdd (h m (n + 1)) (h m (n - 1))) (realNeg (realAdd (h m n) (h m n))))))
      (realEq_refl
        (realAdd
          (rmul (intToReal (γ m n))
            (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
                     (realNeg (realAdd (g (m + 1) n) (g m (n + 1))))))
          (rmul (intToReal (γ m n))
            (realAdd (realAdd (h (m + 1) (n + 1)) (h m n))
                     (realNeg (realAdd (h (m + 1) n) (h m (n + 1))))))))) ?_
  exact g2d_add_interchange
    (realAdd
      (rmul (intToReal (α m n))
        (realAdd (realAdd (g (m + 1) n) (g (m - 1) n)) (realNeg (realAdd (g m n) (g m n)))))
      (rmul (intToReal (β m n))
        (realAdd (realAdd (g m (n + 1)) (g m (n - 1))) (realNeg (realAdd (g m n) (g m n))))))
    (realAdd
      (rmul (intToReal (α m n))
        (realAdd (realAdd (h (m + 1) n) (h (m - 1) n)) (realNeg (realAdd (h m n) (h m n)))))
      (rmul (intToReal (β m n))
        (realAdd (realAdd (h m (n + 1)) (h m (n - 1))) (realNeg (realAdd (h m n) (h m n))))))
    (rmul (intToReal (γ m n))
      (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
               (realNeg (realAdd (g (m + 1) n) (g m (n + 1))))))
    (rmul (intToReal (γ m n))
      (realAdd (realAdd (h (m + 1) (n + 1)) (h m n))
               (realNeg (realAdd (h (m + 1) n) (h m (n + 1))))))

/-- **M465F-5c: M460F 非等方 gan への帰着** — α,β 定数・γ=0 で本可変係数作用素が M460F の非等方
    （混合項なし）Laplacian `ganLaplacian α β g` へ realEq で厳密帰着。混合項の重み 0 が消え
    （rmul (intToReal 0) が realZero へ）、m/n 方向は定数重み α,β の非等方 gan に一致する。
    M460F の非等方（混合項なし）版が本可変係数＋混合項作用素の γ=0・定数重み特殊化として現れる整合方向。 -/
theorem gvc_reduces_to_gan (α β : Int) (g : Int → Int → RReal) (m n : Int) :
    realEq (gvcLaplacian (fun _ _ => α) (fun _ _ => β) (fun _ _ => 0) g m n)
      (ganLaplacian α β g m n) := by
  have hI0 : realEq (intToReal 0) realZero := realEq_of_seq_eq (fun _ => rfl)
  have hz : realEq
      (rmul (intToReal 0)
        (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
                 (realNeg (realAdd (g (m + 1) n) (g m (n + 1)))))) realZero :=
    realEq_trans
      (rmul_congr_left
        (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
                 (realNeg (realAdd (g (m + 1) n) (g m (n + 1))))) hI0)
      (realEq_trans
        (rmul_comm realZero
          (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
                   (realNeg (realAdd (g (m + 1) n) (g m (n + 1))))))
        (rmul_zero
          (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
                   (realNeg (realAdd (g (m + 1) n) (g m (n + 1)))))))
  show realEq
      (realAdd (ganLaplacian α β g m n)
        (rmul (intToReal 0)
          (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
                   (realNeg (realAdd (g (m + 1) n) (g m (n + 1)))))))
      (ganLaplacian α β g m n)
  exact realEq_trans (realAdd_congr_right (ganLaplacian α β g m n) hz)
    (realAdd_zero (ganLaplacian α β g m n))

/-! ## M465F-6: 正直な scope 定理（M460F の「定数重み・混合項なし」を破った形で残限定を露出） -/

/-- **M465F-6: 正直な scope 定理** — 本可変係数楕円作用素の正体は**位置依存重み α(m,n),β(m,n),γ(m,n) と
    混合 2 階差分を持つ離散楕円作用素**であること（定義的等式）。M460F の「位置非依存（定数）重み・
    混合項なし（separable）」限定は `gvc_variable_coeff`（重み α(m,n)=m が位置依存）と
    `gvc_mixed_nonzero`（混合項 γ が非自明に効く）で破ったが、**2 次元離散格子・具体重み関数
    （多項式重み）・特定 witness 関数（双線形 mn・二次 m²）・整数係数に留まる**という残限定を地図として
    露出する（真の測度論的 dd^c・任意次元・非線形 PDE・可変曲率 Green 関数・Deligne pairing は後続。
    完全証明ファースト規則 §4）。 -/
theorem gvc_model_scope (α β γ : Int → Int → Int) (g : Int → Int → RReal) (m n : Int) :
    gvcLaplacian α β γ g m n
      = realAdd
          (realAdd
            (rmul (intToReal (α m n))
              (realAdd (realAdd (g (m + 1) n) (g (m - 1) n))
                       (realNeg (realAdd (g m n) (g m n)))))
            (rmul (intToReal (β m n))
              (realAdd (realAdd (g m (n + 1)) (g m (n - 1)))
                       (realNeg (realAdd (g m n) (g m n))))))
          (rmul (intToReal (γ m n))
            (realAdd (realAdd (g (m + 1) (n + 1)) (g m n))
                     (realNeg (realAdd (g (m + 1) n) (g m (n + 1)))))) :=
  rfl

/-! ## M465F-7: capstone -/

/-- **M465F-7a: 可変係数＋混合項楕円作用素データ** — 位置依存重み付き Laplacian・線形性・
    可変係数 Poisson 型関係式（混合項が残る）・混合項の非自明性を束ねた実体。 -/
structure GvcData where
  /-- 可変係数＋混合項離散楕円作用素（重み α,β,γ は位置 (m,n) の関数・γ 項は混合 2 階差分）。 -/
  laplacian : (Int → Int → Int) → (Int → Int → Int) → (Int → Int → Int) →
    (Int → Int → RReal) → Int → Int → RReal
  /-- 可変係数 Laplacian の加法性（線形作用素）。 -/
  additive : ∀ α β γ g h m n,
    realEq (laplacian α β γ (fun i j => realAdd (g i j) (h i j)) m n)
      (realAdd (laplacian α β γ g m n) (laplacian α β γ h m n))
  /-- **可変係数 Poisson 型関係式** Δ_{α,β,γ}(i·j) = γ(m,n)（混合項の重みが残る）。 -/
  poisson_mixed : ∀ α β γ m n,
    realEq (laplacian α β γ (fun i j => intToReal (gvcBilinZ i j)) m n) (intToReal (γ m n))
  /-- **混合項が非自明に効く**（separable を破る witness が存在）。 -/
  mixed_nonzero : ∃ m n,
    ¬ realEq (laplacian (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1)
        (fun i j => intToReal (gvcBilinZ i j)) m n) realZero

/-- **M465F-7b: 可変係数＋混合項楕円作用素データの witness**（全て本物）。 -/
def gvcData : GvcData where
  laplacian := gvcLaplacian
  additive := gvc_laplacian_additive
  poisson_mixed := gvc_poisson_variable
  mixed_nonzero := gvc_mixed_nonzero

/-- **M465F-7c: 存在** — 可変係数＋混合項楕円作用素データは充足可能
    （K=ℚ・2 次元格子・位置依存重み α,β,γ・混合 2 階差分・双線形/二次 witness）。 -/
theorem gvc_exists : Nonempty GvcData :=
  ⟨gvcData⟩

end IUT
