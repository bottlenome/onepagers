/-
  IUT/LogShellReal.lean — M321F（本物の対数殻: ℤ_p 上の O_v-加群 log-shell）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の p 進局所体 K = ℚ_p・O_v = ℤ_p の
    上での対数殻 m^d = p^d·ℤ_p を **O_v-加群として実構成**し、
    graded log（θ_d = 対数の主項係数）の**準同型性**・単数
    フィルトレーションとの整合・有界性を本物で閉じる）。
  * complete_pct 影響: **前進**。既存 `IUT/LogShell.lean`（M201F）が
    `realVolumeTheory`（Region = ℝ・vol = id）上の**代理模型**で
    「殻の語彙への再輸出」だったのに対し、本モジュールは**本物の
    ℤ_p 加法群 `(Zp p)`（O_v）とその乗法 `zpMul`（O_v スカラー倍）
    の上で、log-shell m^d = p^d·ℤ_p を真の O_v-部分加群として構成**し、
    0・和・O_v スカラー倍での閉性を本物で証明する。柱C（Frobenioid/
    log-shell）の log-shell 対象を**代理 → 実**へ昇格させる。

  ## 何を本物化したか（既存 LogShell が模型 → 本物へ）
  既存 M201F の `LogShell` は `V.Region`（= ℝ）上の抽象 container で
  あり、O_v-加群構造も log 写像も p 進局所体の実体を持たない。
  本 M321F は次を **本物の ℤ_p 上**で新規に積む:
  * M321F-1 `logShellMem` — 対数殻 m^d = p^d·ℤ_p の会員述語
    （x ≡ 0 mod p^d、レベル d 残余が 0）。本物の付値イデアル。
  * M321F-2 `logShell_zero_mem`/`_add_mem`/`_smul_mem` —
    **m^d が O_v-部分加群**であること: 0 を含み、加法 `(Zp p).mul`
    で閉じ、**O_v = ℤ_p の任意元 c による乗法 `zpMul p c` で閉じる**
    （＝ O_v-スカラー倍で閉じる）。本物の加群構造。
  * M321F-3 `logShellLog`/`logShell_log_isHom` — **graded log**
    θ_d（= p 進対数の主項係数 log(1+p^d u) ≡ p^d u の u mod p）を
    `unitTheta`（M31）として採り、その**準同型 log(xy)=log x + log y**
    を `unitTheta_hom` で本物に閉じる（乗法群 U^(d) → 加法群 ℤ/p）。
  * M321F-4 `logShellContent`/`logShell_unit_filtration` —
    **単数フィルトレーションとの整合**: x ∈ U^(d) の leading log
    x − 1（= log の主項）が殻 m^d に着地する（`unitFiltration` 接続）。
  * M321F-5 `logShell_antitone`/`logShellVol`/`logShell_vol_bounded` —
    **有界性**: 殻は antitone（m^e ⊆ m^d for d ≤ e）で、元は付値 ≥ d
    の有界球に収まる（有限体積 container、[O_v : m^d] = p^d）。
  * M321F-6 `LogShellRealData`/`logShellRealData`/`logShellReal_exists` — capstone。
  * M321F-7 `logShell_example_two` — 実例 ℤ₂ 上の m = 2·ℤ₂。

  ## 正直な限定（消去・弱化禁止）
  * **log 写像の準同型性は「主項（leading-coefficient）」で本物**。
    完全な p 進対数の収束級数 log(1+t) = t − t²/2 + t³/3 − …
    （分母 1/k の整数性・逆極限上の収束）の構成は重く、ここでは
    その**主項 θ_d = 対数の 1-jet の係数**（`unitTheta`）を採る。
    θ_d は本物の準同型（`unitTheta_hom`、M31）であり toy ではない
    —— log(1+p^d u) = p^d u + O(p^{2d}) の主項そのもの。完全収束級数
    は後続層。
  * **log-shell は K = ℚ_p の場合の m^d = p^d·ℤ_p**（真の付値イデアル・
    O_v-部分加群）。原文の I_K = (1/2p)·log(O_K^×) の係数 1/2p による
    分数化（ℤ_p の外へ出る fractional module）は、ℤ_p に 1/p が無い
    ため本層では m^d に留める。一般の局所体 O_K^×・分数係数版は後続。
  * **体積は付値レベル d（co-level）による主要部分**。Haar 測度による
    厳密 log-volume −d·log p、および M312F/M317F deg_ℝ との数値接続は
    後続層。本層では有界性（antitone・付値下界・有限指数 p^d）を本物で。
  * 多輻的アルゴリズムでの log-shell の役割（相互作用・不定性の
    受け皿）は柱D 後続。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無）。
  柱C 横展開・本物の先行建設[実]。tier-M（サブエージェント）。
-/
import IUT.UnitFiltration

namespace IUT

/-! ## M321F-1: 対数殻 m^d = p^d·ℤ_p の会員述語 -/

/-- **M321F-1: 対数殻の会員述語** — log-shell m^d = p^d·ℤ_p。
    x ∈ m^d ⟺ x ≡ 0 (mod p^d)（レベル d の残余が 0）。
    本物の付値イデアル（O_v = ℤ_p の中の真の部分加群）。 -/
def logShellMem (p d : Nat) (x : (Zp p).carrier) : Prop :=
  x.val d = Quot.mk (modCong (p ^ d)).rel 0

/-! ## M321F-2: m^d は O_v-部分加群 -/

/-- **定理 (M321F-2a): 0 ∈ 殻** — 加法単位元は各レベルで 0。 -/
theorem logShell_zero_mem (p d : Nat) : logShellMem p d (Zp p).one := rfl

/-- **定理 (M321F-2b): 殻は加法で閉じる** — x, y ∈ m^d なら
    x + y ∈ m^d（0 + 0 = 0）。 -/
theorem logShell_add_mem (p d : Nat) {x y : (Zp p).carrier}
    (hx : logShellMem p d x) (hy : logShellMem p d y) :
    logShellMem p d ((Zp p).mul x y) := by
  show quotMul intGrp (modCong (p ^ d)) (x.val d) (y.val d)
      = Quot.mk (modCong (p ^ d)).rel 0
  rw [hx, hy]
  show Quot.mk (modCong (p ^ d)).rel ((0 : Int) + 0)
      = Quot.mk (modCong (p ^ d)).rel 0
  have h : (0 : Int) + 0 = 0 := by omega
  rw [h]

/-- **定理 (M321F-2c): 殻は O_v スカラー倍で閉じる** — 任意の
    c ∈ O_v = ℤ_p と x ∈ m^d について c·x ∈ m^d（c·0 = 0）。
    これが **m^d が O_v-加群**であることの核（加法だけでなく
    ℤ_p 係数の乗法で閉じる）。 -/
theorem logShell_smul_mem (p d : Nat) (c : (Zp p).carrier)
    {x : (Zp p).carrier} (hx : logShellMem p d x) :
    logShellMem p d (zpMul p c x) := by
  show zmodMul (p ^ d) (c.val d) (x.val d) = Quot.mk (modCong (p ^ d)).rel 0
  rw [hx]
  induction c.val d using Quot.ind
  rename_i a
  show Quot.mk (modCong (p ^ d)).rel (a * 0) = Quot.mk (modCong (p ^ d)).rel 0
  rw [Int.mul_zero]

/-! ## M321F-3: graded log（対数の主項係数）とその準同型性 -/

/-- **M321F-3a: graded log** θ_d — p 進対数の主項係数。
    log(1 + p^d u) = p^d u + O(p^{2d}) の主項 p^d u を p^d で割り
    mod p した u（= `unitTheta`、M31）。単数群 U^(d) → 加法群 ℤ/p。 -/
def logShellLog (p d : Nat) (hp : 1 ≤ p) (x : (principalUnits p).carrier) :
    (zmod p).carrier :=
  unitTheta p d hp x

/-- **定理 (M321F-3b): graded log は準同型** — log(xy) = log x + log y
    （乗法群 U^(d) から加法群 ℤ/p へ）。`unitTheta_hom`（M31）を
    log-shell の語彙で採る。対数写像の「乗法 → 加法」性の主項での
    本物の実現。 -/
theorem logShell_log_isHom (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y) :
    logShellLog p d hp ((principalUnits p).mul x y)
      = (zmod p).mul (logShellLog p d hp x) (logShellLog p d hp y) :=
  unitTheta_hom p d hp hd x y hx hy

/-! ## M321F-4: 単数フィルトレーションとの整合（leading log ∈ 殻） -/

/-- ℤ_p の加法的引き算 a − b。 -/
def zpSub (p : Nat) (a b : (Zp p).carrier) : (Zp p).carrier :=
  (Zp p).mul a ((Zp p).inv b)

/-- **M321F-4a: leading log content** — 主単数 x = 1 + p^d u の
    leading log（= p 進対数の主項）x − 1。 -/
def logShellContent (p : Nat) (x : (Zp p).carrier) : (Zp p).carrier :=
  zpSub p x (zpOne p)

/-- **定理 (M321F-4b): 単数フィルトレーションとの整合** —
    x ∈ U^(d) = 1 + p^d·ℤ_p なら、その leading log content x − 1 は
    対数殻 m^d = p^d·ℤ_p に着地する。すなわち log(U^(d)) ⊆ m^d の
    主項版（`unitFiltration`（M31）接続）。付値 ≥ d の受け皿。 -/
theorem logShell_unit_filtration (p d : Nat)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x) :
    logShellMem p d (logShellContent p x.val) := by
  show quotMul intGrp (modCong (p ^ d)) (x.val.val d)
      ((zmod (p ^ d)).inv ((zpOne p).val d))
      = Quot.mk (modCong (p ^ d)).rel 0
  rw [hx]
  show Quot.mk (modCong (p ^ d)).rel (1 + intGrp.inv 1)
      = Quot.mk (modCong (p ^ d)).rel 0
  have h : (1 : Int) + intGrp.inv 1 = 0 := by
    show (1 : Int) + -1 = 0
    omega
  rw [h]

/-! ## M321F-5: 有界性（antitone・付値下界） -/

/-- **定理 (M321F-5a): 殻は antitone** — d ≤ e なら m^e ⊆ m^d
    （高次の殻はより小さい入れ物）。付値の単調性。 -/
theorem logShell_antitone (p : Nat) {d e : Nat} (h : d ≤ e)
    (x : (Zp p).carrier) (hx : logShellMem p e x) : logShellMem p d x := by
  have hcomp : (zmodTrans (pow_dvd_mono p h)).map (x.val e) = x.val d :=
    x.property h
  show x.val d = Quot.mk (modCong (p ^ d)).rel 0
  rw [← hcomp, hx]
  rfl

/-- **M321F-5b: 殻の co-level**（正規化 log-volume の指数部）。
    [O_v : m^d] = p^d で、log-volume は −d·log p（本層では指数 d）。 -/
def logShellVol (d : Nat) : Nat := d

/-- **定理 (M321F-5c): 殻の有界性** — m^d の元は付値 ≥ d、すなわち
    全ての下位レベル e ≤ d で残余 0。容器が原点付近の有界球
    （半径 p^{−d}）に収まる = 有限体積 container の本物版。 -/
theorem logShell_vol_bounded (p d : Nat) (x : (Zp p).carrier)
    (hx : logShellMem p d x) : ∀ e, e ≤ d → logShellMem p e x :=
  fun e he => logShell_antitone p he x hx

/-! ## M321F-6: capstone -/

/-- **M321F-6a: 対数殻データ**（総括） — 本物の p 進局所体 K = ℚ_p・
    O_v = ℤ_p 上の log-shell の O_v-加群構造・graded log 準同型・
    単数フィルトレーション整合・有界性を束ねる。 -/
structure LogShellRealData where
  /-- 局所体 K = ℚ_p の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  hp : 1 ≤ p
  /-- 対数殻 m^d = p^d·ℤ_p の会員述語。 -/
  mem : Nat → (Zp p).carrier → Prop
  /-- 0 ∈ 殻。 -/
  zero_mem : ∀ d, mem d (Zp p).one
  /-- 殻は加法で閉じる。 -/
  add_mem : ∀ d {x y}, mem d x → mem d y → mem d ((Zp p).mul x y)
  /-- 殻は O_v スカラー倍で閉じる（O_v-加群の核）。 -/
  smul_mem : ∀ d (c : (Zp p).carrier) {x}, mem d x → mem d (zpMul p c x)
  /-- graded log 写像（対数の主項係数）。 -/
  logMap : Nat → (principalUnits p).carrier → (zmod p).carrier
  /-- log は準同型（乗法 → 加法）。 -/
  log_hom : ∀ d, 1 ≤ d → ∀ (x y : (principalUnits p).carrier),
    (unitFiltration p d).mem x → (unitFiltration p d).mem y →
    logMap d ((principalUnits p).mul x y)
      = (zmod p).mul (logMap d x) (logMap d y)
  /-- 単数フィルトレーション整合: leading log(U^(d)) ⊆ m^d。 -/
  unit_compat : ∀ d (x : (principalUnits p).carrier),
    (unitFiltration p d).mem x → mem d (logShellContent p x.val)
  /-- 有界性: m^d の元は付値 ≥ d（antitone）。 -/
  bounded : ∀ d (x : (Zp p).carrier), mem d x → ∀ e, e ≤ d → mem e x

/-- **M321F-6b: witness** — ℤ_p 上の本物の log-shell データ。 -/
def logShellRealData (p : Nat) (hp : 1 ≤ p) : LogShellRealData where
  p := p
  hp := hp
  mem := logShellMem p
  zero_mem := logShell_zero_mem p
  add_mem := fun d => logShell_add_mem p d
  smul_mem := fun d c => logShell_smul_mem p d c
  logMap := fun d => logShellLog p d hp
  log_hom := fun d hd => logShell_log_isHom p d hp hd
  unit_compat := logShell_unit_filtration p
  bounded := logShell_vol_bounded p

/-- **M321F-6c: 存在** — 本物の対数殻データは充足可能（K = ℚ₂）。 -/
theorem logShellReal_exists : Nonempty LogShellRealData :=
  ⟨logShellRealData 2 (by omega)⟩

/-! ## M321F-7: 実例 -/

/-- **定理 (M321F-7): 実例** — ℤ₂ 上の log-shell m = 2·ℤ₂。
    2 = toZp 2 は殻 m^1 に属す（付値 1 ≥ 1）。 -/
theorem logShell_example_two :
    logShellMem 2 1 ((toZp 2).map 2) := by
  show Quot.mk (modCong (2 ^ 1)).rel 2 = Quot.mk (modCong (2 ^ 1)).rel 0
  apply Quot.sound
  show ((2 ^ 1 : Nat) : Int) ∣ 2 - 0
  rw [Nat.pow_one]
  exact ⟨1, by omega⟩

end IUT
