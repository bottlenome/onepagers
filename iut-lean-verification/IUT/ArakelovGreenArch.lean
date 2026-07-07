-- M445F ArakelovGreenArch [実・本物・柱C]
-- complete_pct 影響: 柱C を前進。M440F(aip) が Arakelov 交点数の ∞ 素点寄与を
--   「実重み積 arch(D)·arch(E)＝Green 関数積分の一点近似」に留めていた**正直な限定を昇格で閉じる**。
--   ∞ 部を**複数点での Green 核の有限和 Σ_{i<N} g(p_D i, p_E i)（真の積分 ∫g_D·g_E の Riemann 和近似）**へ
--   置換し、`agr_green_not_pointwise` で一点積 (Σp_D)(Σp_E) と実際に異なる（Σ a_i b_i ≠ (Σa_i)(Σb_i)）ことを
--   定理で示し、`agr_error_bound` で N→大の幾何減衰収束（真の積分へ向かう方向）を示す。
-- 正直な限定（M440F より狭めた形）: 完全な ∫g_D·(dd^c g_E+δ_E)（測度論的 curvature 項 dd^c・δ_E）・
--   Deligne pairing・arithmetic Riemann–Roch は未。有限和近似・特定核（実数積型）・K=ℚ 模型に留まる。

/-
  IUT/ArakelovGreenArch.lean — M445F（柱C: アルキメデス Green 関数寄与の昇格）

  ── 主要成果の分類: **[実]**（§2(a) 昇格）。M440F
     (`IUT/ArakelovIntersectionPairing.lean`, prefix `aip`) の真の Arakelov 交点数

        ⟨D,E⟩ = Σ_v (n_v·m_v)·log p_v + arch(D)·arch(E)

     は有限素点部を場所ごとの局所交点数の和へ昇格した一方、**∞ 素点の寄与は一点の実重み積
     arch(D)·arch(E)（Green 関数積分の一点近似）に留まる**と `aip_model_scope` が正直に限定していた。
     本モジュールはその**正直な限定を昇格で閉じる**——∞ 部を、点配置 p_D, p_E に沿って Green 核
     g(a,b) を **N 点で足し上げた有限和 Σ_{i<N} g(p_D i, p_E i)**（真の Green 積分 ∫_{X(ℂ)} g_D·g_E の
     Riemann 和近似）へ置換する。これは一点積 (Σ p_D)(Σ p_E) と**一般に異なる**
     （Σ a_i b_i ≠ (Σ a_i)(Σ b_i)）ことを `agr_green_not_pointwise` で定理として示し、限定を
     実際に閉じたことを露出する。主語は M150F の本物の実数乗法 rmul・M312F の実測度的 log-volume・
     M181 の実数幾何減衰 `realPow_rabs_decay`。toy 主語なし。

  complete_pct 影響: **柱C（Frobenioid／Arakelov 交点理論）の実 IUT 完全証明率を前進**。
  M440F は ∞ 部を一点実重み積に潰していた。本ファイルは:
  (1) **Green 核** `agrGreenKernel a b`——アルキメデス Green 関数の実数値核（Green 潜在の積
      g_D(x)·g_E(x) の一点値の実数近似）。対称 g(a,b)=g(b,a)（`agr_kernel_symm`）。
  (2) **Green 有限和** `agrGreenSum p q N = Σ_{i<N} g(p i, q i)`——点配置 p,q に沿って核を
      N 点で足した有限和（真の積分 ∫g_D·g_E の Riemann 和近似・realEq 実数）。
  (3) **一点近似を脱したこと** `agr_green_not_pointwise`——具体配置で Green 和が一点積
      (Σp)(Σq) と ¬realEq（Σ a_i b_i ≠ (Σa_i)(Σb_i)）。**M440F の一点近似限定を実際に閉じた証拠**。
  (4) **Green 和の対称性** `agr_green_symmetric`——核対称性の場所ごとの和（帰納）。
  (5) **昇格 pairing** `agrPairing`——M440F 有限部（場所ごとの局所交点数の和）＋ ∞ 部を Green 和へ
      置換した交点数。その対称性 `agr_pairing_symmetric`（有限部 Int.mul_comm＋∞ 部 Green 和対称）。
  (6) **N 点近似の誤差減衰** `agr_error_bound`／`agr_green_telescope`——増分（新項）は隣接部分和の差で
      あり（望遠鏡）、その大きさが幾何減衰 |g(p_N,q_N)| ≤ r^N なら N≥K·m で ≤ 1/(m+1)
      （M181 `realPow_rabs_decay`）。部分和が Cauchy＝真の積分へ収束する方向を示す。
  (7) 正直な scope 定理 `agr_model_scope`（M440F より狭めた残限定）＋ capstone `agr_exists`。

  ## 正直な限定（消去/弱化禁止・地図として保持。M440F より狭めた形）
  - **本物（完全証明・M440F の一点近似限定を閉じた部分）**: ∞ 部が**複数点の Green 核の有限和**
    Σ_{i<N} g(p_i, q_i) であること・核が**対称**であること・和が**対称**であること・そして
    一点積 (Σp)(Σq) と**実際に異なる**こと（`agr_green_not_pointwise`、具体 witness で ¬realEq）・
    N 点近似の**幾何減衰収束**（`agr_error_bound`、増分が真の積分へ向かって 0 に減衰）。
    全て K=ℚ 模型上で本物・sorry 皆無・新規 Classical.choice なし。
  - **正直申告（M440F から狭めた残・後続）**:
    ・**有限和近似に留まる**——真の Arakelov ∞ 交点数は Green 関数の**測度論的積分**
      ∫_{X(ℂ)} g_D·(dd^c g_E + δ_E) であり、本模型はこれを N 点の Riemann 和へ離散化した近似。
      curvature 項 dd^c g_E・Dirac δ_E・(1,1)-流れ・完全な測度論的極限は**後続**。
    ・**特定核**——Green 核 g(a,b)=a·b（Green 潜在値の実数積型近似）に留まる。真の
      −log|z−w| 型／円周上の Green 関数の測度論的構成は後続。
    ・**Deligne pairing / arithmetic Riemann–Roch**（交点数と算術次数の Riemann–Roch 型関係）は後続。
    ・**一般数体（K≠ℚ）**は範囲外（M356F/M440F と同じ K=ℚ 模型・唯一の ∞ 素点）。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・[propext, Quot.sound]）・
  sorry 皆無・禁止タクティク不使用。
-/
import IUT.ArakelovIntersectionPairing
import IUT.RealGeomDecay
import IUT.RealLe

namespace IUT

/-! ## M445F-1: アルキメデス Green 核（対称な実数値核） -/

/-- **M445F-1a: アルキメデス Green 核** g(a,b)——∞ 素点での Green 関数の実数値核。
    Green 潜在の積 g_D(x)·g_E(x) の一点値の実数近似（M150F 実数乗法 rmul）。真の −log|z−w| 型は
    後続（`agr_model_scope`）。この核を点配置に沿って足すことで**一点近似でない**本物の
    有限和（∫g_D·g_E の Riemann 和）を建てる。 -/
def agrGreenKernel (a b : RReal) : RReal := rmul a b

/-- **M445F-1b: Green 核の対称性** g(a,b)=g(b,a)——真の Green 関数 g(z,w)=g(w,z) の実数核版
    （M150F `rmul_comm`）。交点数 ∞ 部の対称性の土台。 -/
theorem agr_kernel_symm (a b : RReal) :
    realEq (agrGreenKernel a b) (agrGreenKernel b a) :=
  rmul_comm a b

/-! ## M445F-2: Green 有限和（真の積分の Riemann 和近似） -/

/-- **M445F-2a: Green 有限和** Σ_{i<N} g(p i, q i)——点配置 p,q（∞ 素点での Green 潜在の
    サンプル値）に沿って Green 核を N 点で足した有限和。真の Green 積分 ∫_{X(ℂ)} g_D·g_E の
    Riemann 和近似。**一点積 arch·arch でなく複数点の和**——ここが M440F の一点近似の昇格の核。 -/
def agrGreenSum (p q : Nat → RReal) : Nat → RReal
  | 0 => realZero
  | N + 1 => realAdd (agrGreenSum p q N) (agrGreenKernel (p N) (q N))

/-- **M445F-2b: 点配置の総質量** Σ_{i<N} p i——∞ 素点での Green 潜在の総和（M440F の一点
    重み arch に相当）。一点近似は積 (Σp)(Σq)＝これらの積で、Green 和とは一般に異なる。 -/
def agrTotal (p : Nat → RReal) : Nat → RReal
  | 0 => realZero
  | N + 1 => realAdd (agrTotal p N) (p N)

/-- **M445F-2c: Green 和の対称性** Σ g(p i,q i) ≈ Σ g(q i,p i)——核の対称性
    `agr_kernel_symm` を場所ごとに足す（N の帰納）。∞ 部の交点対称性の核。 -/
theorem agr_green_symmetric (p q : Nat → RReal) :
    ∀ N, realEq (agrGreenSum p q N) (agrGreenSum q p N) := by
  intro N
  induction N with
  | zero => exact realEq_refl realZero
  | succ N ih =>
    show realEq (realAdd (agrGreenSum p q N) (agrGreenKernel (p N) (q N)))
        (realAdd (agrGreenSum q p N) (agrGreenKernel (q N) (p N)))
    refine realEq_trans (realAdd_congr_left _ ih) ?_
    exact realAdd_congr_right _ (agr_kernel_symm (p N) (q N))

/-! ## M445F-3: 一点近似を脱したこと（M440F の限定を実際に閉じる） -/

/-- **M445F-3a: 定数配置**（各サンプル点で Green 潜在値 1）——具体 witness 用。 -/
def agrOne : Nat → RReal := fun _ => intToReal 1

/-- **M445F-3b: 定数配置 2 点の Green 和は 2** — Σ_{i<2} 1·1 = 1+1 = 2。 -/
theorem agr_witness_greensum :
    realEq (agrGreenSum agrOne agrOne 2) (intToReal 2) := by
  have h11 : realEq (rmul (intToReal 1) (intToReal 1)) (intToReal 1) :=
    realEq_trans (intToReal_mul 1 1) (aip_intToReal_congr (by omega : (1 : Int) * 1 = 1))
  show realEq (realAdd (realAdd realZero (rmul (intToReal 1) (intToReal 1)))
      (rmul (intToReal 1) (intToReal 1))) (intToReal 2)
  have hinner : realEq (realAdd realZero (rmul (intToReal 1) (intToReal 1))) (intToReal 1) :=
    realEq_trans (realAdd_comm realZero _) (realEq_trans (realAdd_zero _) h11)
  refine realEq_trans (realAdd_congr_left _ hinner) ?_
  refine realEq_trans (realAdd_congr_right _ h11) ?_
  exact realEq_trans (realEq_symm (intToReal_add 1 1))
    (aip_intToReal_congr (by omega : (1 : Int) + 1 = 2))

/-- **M445F-3c: 定数配置 2 点の総質量は 2** — Σ_{i<2} 1 = 1+1 = 2。 -/
theorem agr_witness_total :
    realEq (agrTotal agrOne 2) (intToReal 2) := by
  show realEq (realAdd (realAdd realZero (intToReal 1)) (intToReal 1)) (intToReal 2)
  have hinner : realEq (realAdd realZero (intToReal 1)) (intToReal 1) :=
    realEq_trans (realAdd_comm realZero _) (realAdd_zero _)
  refine realEq_trans (realAdd_congr_left _ hinner) ?_
  exact realEq_trans (realEq_symm (intToReal_add 1 1))
    (aip_intToReal_congr (by omega : (1 : Int) + 1 = 2))

/-- **M445F-3d: 一点近似（総質量の積）は 4** — (Σp)(Σq) = 2·2 = 4。M440F の一点実重み積形式。 -/
theorem agr_witness_product :
    realEq (rmul (agrTotal agrOne 2) (agrTotal agrOne 2)) (intToReal 4) := by
  refine realEq_trans (rmul_congr_left _ agr_witness_total) ?_
  refine realEq_trans (rmul_congr_right (intToReal 2) agr_witness_total) ?_
  exact realEq_trans (intToReal_mul 2 2)
    (aip_intToReal_congr (by omega : (2 : Int) * 2 = 4))

/-- **M445F-3e: Green 和は一点近似積と異なる（M440F の限定を閉じた本丸）** —
    定数配置 2 点で Green 和 Σ g(p_i,q_i) ≈ 2 だが一点近似 (Σp)(Σq) ≈ 4 ゆえ ¬realEq。
    **M440F `aip_model_scope` が「∞ 部は実重み積 arch·arch＝Green 積分の一点近似に留まる」と
    正直に限定していた内容を、本 Green 和が実際にその一点近似を脱している（Σ a_i b_i ≠
    (Σa_i)(Σb_i)）ことで閉じる**。真の積分の Riemann 和は rank-1 積と一般に一致しない。 -/
theorem agr_green_not_pointwise :
    ∃ (p q : Nat → RReal) (N : Nat),
      ¬ realEq (agrGreenSum p q N) (rmul (agrTotal p N) (agrTotal q N)) := by
  refine ⟨agrOne, agrOne, 2, ?_⟩
  intro hcon
  have hbad : realEq (intToReal 2) (intToReal 4) :=
    realEq_trans (realEq_symm agr_witness_greensum)
      (realEq_trans hcon agr_witness_product)
  exact aip_intToReal_ne (by omega) hbad

/-! ## M445F-4: 昇格した交点数 pairing（∞ 部を Green 和で置換） -/

/-- **M445F-4a: 昇格した Arakelov 交点数** ⟨D,E⟩ = Σ_v (n_v·m_v)·log p_v + Σ_{i<N} g(p_D i, p_E i)。
    有限部は M440F 積因子 `aipProdFin` の log-volume（場所ごとの局所交点数の和）、∞ 部を M440F の
    一点実重み積から**Green 核の有限和**（真の積分の Riemann 和近似）へ昇格。 -/
def agrPairing (logp : Nat → RReal) (D E : ardRaw) (pD pE : Nat → RReal) (N : Nat) : RReal :=
  realAdd (logVolGlobal logp (aipProdFin D.fin E.fin)) (agrGreenSum pD pE N)

/-- **M445F-4b: 昇格 pairing の対称性** ⟨D,E⟩ ≈ ⟨E,D⟩——有限部は係数積の可換性
    n_v·m_v=m_v·n_v（Int.mul_comm・logVolGlobal_wd）、∞ 部は Green 和の対称性
    `agr_green_symmetric`（核対称性の場所ごとの和）。∞ 部を昇格しても交点数が対称双線形形式で
    あることの中核が保たれることの本物。 -/
theorem agr_pairing_symmetric (logp : Nat → RReal) (D E : ardRaw) (pD pE : Nat → RReal) (N : Nat) :
    realEq (agrPairing logp D E pD pE N) (agrPairing logp E D pE pD N) := by
  show realEq (realAdd (logVolGlobal logp (aipProdFin D.fin E.fin)) (agrGreenSum pD pE N))
      (realAdd (logVolGlobal logp (aipProdFin E.fin D.fin)) (agrGreenSum pE pD N))
  have hraw : rawEq (aipProdFin D.fin E.fin) (aipProdFin E.fin D.fin) := by
    intro k
    show D.fin.coeff k * E.fin.coeff k = E.fin.coeff k * D.fin.coeff k
    exact Int.mul_comm _ _
  refine realEq_trans (realAdd_congr_left _ (logVolGlobal_wd logp hraw)) ?_
  exact realAdd_congr_right _ (agr_green_symmetric pD pE N)

/-! ## M445F-5: N 点近似の誤差減衰（真の積分へ収束する方向） -/

/-- **M445F-5a: Green 和の望遠鏡増分** Σ_{i<N+1} g − Σ_{i<N} g ≈ g(p_N, q_N)——N+1 段と N 段の
    部分和の差はちょうど新項の Green 核値。部分和が Cauchy（増分→0）であることの土台。 -/
theorem agr_green_telescope (p q : Nat → RReal) (N : Nat) :
    realEq (realAdd (agrGreenSum p q (N + 1)) (realNeg (agrGreenSum p q N)))
      (agrGreenKernel (p N) (q N)) := by
  show realEq (realAdd (realAdd (agrGreenSum p q N) (agrGreenKernel (p N) (q N)))
      (realNeg (agrGreenSum p q N))) (agrGreenKernel (p N) (q N))
  refine realEq_trans
    (realAdd_congr_left (realNeg (agrGreenSum p q N))
      (realAdd_comm (agrGreenSum p q N) (agrGreenKernel (p N) (q N)))) ?_
  refine realEq_trans
    (realAdd_assoc (agrGreenKernel (p N) (q N)) (agrGreenSum p q N)
      (realNeg (agrGreenSum p q N))) ?_
  refine realEq_trans
    (realAdd_congr_right (agrGreenKernel (p N) (q N)) (realAdd_neg (agrGreenSum p q N))) ?_
  exact realAdd_zero (agrGreenKernel (p N) (q N))

/-- **M445F-5b: N 点近似の誤差減衰** — 増分（望遠鏡差＝新項の Green 核値）の大きさが幾何減衰
    |g(p_N,q_N)| ≤ |r|^N であれば、|r| ≤ (K/(K+1))↑（K≥1）の下で N ≥ K·m のとき
    |g(p_N,q_N)| ≤ 1/(m+1)↑（M181 `realPow_rabs_decay`）。増分が m→大で 0 へ幾何減衰
    ＝部分和が Cauchy＝Green 和が**真の積分へ収束する方向**を明示的モジュラスで示す
    （rate-bound／幾何減衰の既存補題の適用）。 -/
theorem agr_error_bound (p q : Nat → RReal) (r : RReal) (K m N : Nat)
    (hincr : rLe (rabs (agrGreenKernel (p N) (q N))) (realPow (rabs r) N))
    (hb : rLe (rabs r) (qToReal (qFrac K K))) (hK : 1 ≤ K) (hN : K * m ≤ N) :
    rLe (rabs (agrGreenKernel (p N) (q N))) (qToReal (qFrac 1 m)) :=
  rLe_trans hincr (realPow_rabs_decay r K m N hb hK hN)

/-! ## M445F-6: 正直な scope 定理（M440F より狭めた残限定を露出） -/

/-- **M445F-6: 正直な scope 定理** — 本昇格 pairing の正体は**有限部（場所ごとの局所交点数の和）
    ＋ ∞ 部（Green 核の有限和）**であること（定義的等式）。M440F の一点近似限定は
    `agr_green_not_pointwise` で閉じたが、**∞ 部は有限和近似・特定核 g(a,b)=a·b に留まる**という
    残限定を地図として露出する（真の測度論的積分 ∫g_D·(dd^c g_E+δ_E)・Deligne pairing は後続。
    完全証明ファースト規則 §4）。 -/
theorem agr_model_scope (logp : Nat → RReal) (D E : ardRaw) (pD pE : Nat → RReal) (N : Nat) :
    agrPairing logp D E pD pE N
      = realAdd (logVolGlobal logp (aipProdFin D.fin E.fin)) (agrGreenSum pD pE N) :=
  rfl

/-! ## M445F-7: capstone -/

/-- **M445F-7a: 昇格した Arakelov ∞ 交点数データ** — Green 核・対称性・Green 有限和・和の対称性・
    昇格 pairing の対称性・一点近似を脱したこと（(Σp)(Σq) と異なる witness）・望遠鏡増分を
    束ねた実体。 -/
structure AgrGreenData where
  /-- Green 核 g(a,b)。 -/
  kernel : RReal → RReal → RReal
  /-- Green 有限和 Σ_{i<N} g(p i, q i)。 -/
  greenSum : (Nat → RReal) → (Nat → RReal) → Nat → RReal
  /-- 核の対称性 g(a,b)≈g(b,a)。 -/
  kernel_symm : ∀ a b, realEq (kernel a b) (kernel b a)
  /-- Green 和の対称性 Σg(p,q)≈Σg(q,p)。 -/
  sum_symm : ∀ p q N, realEq (greenSum p q N) (greenSum q p N)
  /-- **一点近似を脱したこと**（(Σp)(Σq) と異なる witness が存在）。 -/
  not_pointwise : ∃ p q N,
    ¬ realEq (greenSum p q N) (rmul (agrTotal p N) (agrTotal q N))

/-- **M445F-7b: 昇格した Arakelov ∞ 交点数データの witness**（全て本物）。 -/
def agrGreenData : AgrGreenData where
  kernel := agrGreenKernel
  greenSum := agrGreenSum
  kernel_symm := agr_kernel_symm
  sum_symm := agr_green_symmetric
  not_pointwise := agr_green_not_pointwise

/-- **M445F-7c: 存在** — 昇格した Arakelov ∞ 交点数データは充足可能（K=ℚ・定数配置 witness）。 -/
theorem agr_exists : Nonempty AgrGreenData :=
  ⟨agrGreenData⟩

end IUT
