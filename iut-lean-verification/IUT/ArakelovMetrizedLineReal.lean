/-
  IUT/ArakelovMetrizedLineReal.lean — M480F [実／(a) 昇格]

  分類: **[実]** — 実 ℚ（QRat = Quot ratRel）上の**実 ℝ-計量付き直線束**
    L̄ = (q·ℤ ⊂ ℚ, ‖·‖ = λ·|·|_∞, **λ ∈ ℝ>0**) と、**実 ℝ 値の算術次数**。
    計量スケール λ はスクラッチ構成的実数 `RReal`（Bishop 流正則 Cauchy 列、
    M117F〜M162）であり、正値性は**実順序の一様下界 witness**
    （∀m, 1/(N+1) ≤ λ_m ⟹ `IsPos λ`）で持つ。次数は
    `rinvPos`（M145 の choice なし正値実数逆元）で構成した **RReal 値の関数**
    deg×(L̄) := 1/‖q‖ で、テンソル積で**乗法的**（= log 形で加法的）、
    イソメトリ捻りで**不変**、実順序 `rLe` で**比較可能**。

  (a) 昇格: 直前の M474F `ArakelovMetrizedLineQ`（aml）は計量スケールが
    `met : PreRat`（λ ∈ ℚ>0）に固定され、次数の値域が (ℚ>0, ×) であった。
    独立監査はこれを C3 の主要な限界と名指しした:「実 Arakelov 計量は ℝ>0
    スケールを持つ／次数が ℚ 値では C4 の log-volume と比較・加減できない／
    Cor 3.12 が要求する **ℝ 値の不等式**を表現できない」。本モジュールは
    対象クラスそのものを **λ ∈ ℝ>0 へ昇格**し、次数を **RReal 値**にする。

  complete_pct 影響: **あり（C3「実 Arakelov（実計量付き直線束・実算術次数）」の
    前進を意図・判定は独立監査）**。昇格した内容:
    1. **スケールが実 ℝ**: `armBundle.met : RReal`（+ 一様正値 witness）。
       `arm_codeg_surjective` により**任意の**正値実数 a（一様下界 witness 付き）
       が或る束の余次数として実現される ⟹ 次数写像の像は ℚ>0 ではなく **ℝ>0**。
       ℚ スケール族（M474F の対象クラス）は `armOfRat` で真部分族として埋まる。
    2. **次数が RReal 値の関数**（∃ 形の関係ではない）: `armDeg : armBundle → RReal`。
       `arm_deg_tensor`（乗法的準同型 = log 形の加法性）・`arm_deg_twist`
       （主イソメトリ捻り不変 =「主因子の次数 0」）・`arm_deg_congr`
       （λ の realEq に関する井戸定義）。
    3. **実 ℝ 値の不等式が表現できる**: 実順序 `rLe` の上で
       `arm_codeg_le_norm`（格子の非零切断の計量は余次数以上）・
       `arm_small_section_iff`・**`arm_riemann_roch_criterion`**
       （0≠s∈L で ‖s‖≤1 なる切断が存在 ⟺ deg×(L̄) ≥ 1、log 形で
       「h⁰(L̄) ≠ 0 ⟺ deg(L̄) ≥ 0」）・`arm_codeg_mono`/`arm_deg_anti`
       （計量の支配 ⟹ 次数の不等式）。
    4. **格子が load-bearing**: 監査は aml の `amlMem` が「次数理論が一度も
       使わない Prop」であることを指摘した。本モジュールの主要不等式
       `arm_codeg_le_norm` は仮定が `armMemNZ L s`（s は**格子の非零元**）で
       あり、任意の有理数 s では**偽**（0<|x|<1 なる有理倍で反例）。
       すなわち格子所属が証明で本質的に効いている。
    5. **実 B5 積公式の消費を維持**: `arm_norm_prod_section` /
       `arm_deg_section_indep` / `arm_deg_integral_section` は
       `b5_product_formula`（実 ℚ・実 |·|_∞・実 |·|_p）を消費する。

  正直な限定（消去・弱化禁止）:
  1. **K = ℚ のみ**（Spec ℤ・実素点 1 個・複素素点なし）。一般数体の Arakelov は未達。
  2. 直線束は**生成元表示** q·ℤ（K=ℚ は類数 1 ゆえ忠実だが、「ℚ 内の任意の階数 1
     ℤ-部分加群が主である」ことは未証明）。階数 ≥ 2 の格子・一般の計量付き加群は未達。
  3. 次数は**乗法形**（古典的 deg の指数 exp(deg)）。値域は実 ℝ>0 であり
     **順序（rLe）による不等式は表現できる**が、加法群 (ℝ,+) への同型
     （= 実対数 log）は本層でも**未構成**。したがって C4 の log-volume と
     「足し算」で直接結合することはまだできない（比較・不等式の伝達は
     単調性を経由すれば可能）。repo 内の logp 系（`ProductFormula` の
     `logp : Nat → RReal` 自由パラメタ）は循環と判定済みであり**一切消費しない**。
  4. λ の正値性は**一様下界 witness**（N : Nat と ∀m, 1/(N+1) ≤ λ_m）を構造体に
     持たせる形。`IsPos λ`（∃ 形）だけからは choice なしに N を取り出せないため
     （M145 と同じ設計）、対象は「正値実数」ではなく「正値 witness 付き実数」。
     `arm_deg_congr` により次数は witness の取り方に依らない（realEq 一意）。
  5. **無理数スケールの具体例は未提示**。RReal は任意の正則 Cauchy 列を許すので
     対象クラスは定義上 ℚ スケール族を真に含み、`arm_codeg_surjective` が像の
     ℝ>0 全域性を与えるが、「或る具体的 λ が如何なる有理数とも realEq でない」
     という無理性証明（√2 等）は repo に存在せず本層でも作らない。
  6. 非零性は代表 witness 形（x : PreRat・x.num ≠ 0）。商上のゼロ判定選言は
     排中律を要するため対象外（qInv・qMul_inv・b5 の既存の正直申告を継承）。
  7. 有限部の寄与 ∏_p |s/q|_p は実 p 進絶対値の有限台積。「指数 [L:ℤs] = 商加群の
     濃度」という数え上げ命題は未証明（絶対値経由でのみ扱う）— M474F から継承。
  8. 曲面上の Arakelov 交点理論・アルキメデス Green 関数の実積分は対象外。
     M474F（ℚ スケール版）および M356F 系模型モジュールは §4 に従い残置する。
  9. **テンソル積は普遍対象として構成していない**（M474F の監査指摘を継承）。
     `armTensor` は rank 1 の正しい公式（生成元の積・スケールの積）だが、
     ⊗ の普遍性（双線型写像の分解）は証明していない。したがって
     `arm_deg_tensor` は「⊗ の次数準同型性」ではなく「この演算に関する
     乗法性」である（rank 1 では両者は一致するが、証明はしていない）。
 10. M480F-5（次数公式・切断非依存性）の数学的内容は**実 B5 積公式そのもの**で
     あり、本層が足しているのは (i) 実 ℝ への埋め込みを通した積の代数と
     (ii) 余次数 λ·|q| による定数倍である（M474F の監査指摘「§5 の見出しは
     B5 の定数倍」を継承）。本モジュールで新規に数学的内容があるのは
     M480F-4h/4i（値域の ℝ>0 全域性）・M480F-9（格子上の実 ℝ 不等式・
     Riemann–Roch 型判定・単調性）であり、M480F-6/7（乗法性・捻り不変性）は
     M474F の ℚ 証明の実 ℝ への移送である。

  import 閉包は **ProductFormula / ArakelovDivisor / QuadraticProductFormula /
  FrobArakelovBridge を含まない**（circular と判定された系列を一切消費しない）。
  なお `RealInv → ScalarDistrib → VolumeReal → LogVolBridge` の経路で
  `LogVolBridge`（`rlogVol`、重み `w : Nat → Nat` 自由パラメタ）が推移的に
  閉包へ入るが、その定義・定理は**一切参照していない**（本ファイルに
  `rlogVol`/`logp`/`ardDeg`/`aadArithDeg` の出現は本文（定義・証明）でゼロ・
  ヘッダ注記のみ）。

  全て Lean 4.30.0 core のみ（mathlib 不使用）・sorry なし・新規 Classical.choice
  なし。全公開定理の #print axioms は [propext, Quot.sound]。
-/
import IUT.B5ProductFormulaQ
import IUT.RealMulOrder
import IUT.RealDivision
import IUT.RealInv

namespace IUT

/-! ## M480F-0: 実 ℝ>0 のための一様下界ツールキット

    構成的 ℝ で「正の実数」を choice なしに扱う唯一の実用形は、
    近似列の**一様下界** ∀m, 1/(N+1) ≤ x_m である（M145 の `rinvPos` が要求する
    形）。本節はこの形の基本操作（積・埋め込み・IsPos への変換）を用意する。 -/

/-- **M480F-0a: 埋め込み ℚ → ℝ の単調性**（M131F `qToReal_mono` と**同一内容**。
    新規性はない — `LogVolBridge` の定義群（`rlogVol` 等）に依存しない形で
    証明を本ファイル内に閉じるための重複であり、正直に「移送」と申告する）。 -/
theorem arm_qToReal_mono {a b : QRat} (h : qLe a b) :
    rLe (qToReal a) (qToReal b) := by
  intro n
  show qLe a (qAdd b (qAdd (qUnitFrac n) (qUnitFrac n)))
  have h1 : qLe (qAdd b ratRing.zero)
      (qAdd b (qAdd (qUnitFrac n) (qUnitFrac n))) :=
    qLe_add_two (qLe_refl b) (qFrac_add_nonneg 1 n 1 n)
  rw [qAdd_zero] at h1
  exact qLe_trans _ _ _ h h1

/-- **M480F-0b: 列ごとの非負性から実順序の非負性**。 -/
theorem arm_rLe_zero_of_seq {x : RReal} (h : ∀ m, qLe ratRing.zero (x.seq m)) :
    rLe realZero x := by
  intro n
  show qLe ratRing.zero (qAdd (x.seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))
  refine qLe_trans _ _ _ (qLe_of_eq (qAdd_zero ratRing.zero).symm) ?_
  exact qLe_add_two (h n) (qFrac_add_nonneg 1 n 1 n)

/-- 正の有理数 x（分子 ≥ 1）の標準的な一様下界指数 den(x) − 1。 -/
def armLB (x : PreRat) : Nat := (x.den - 1).toNat

/-- **M480F-0c: 有理数の下界** — 分子 ≥ 1 なら 1/den ≤ x
    （1·den ≤ num·den に還元）。 -/
theorem arm_preRat_lb {x : PreRat} (hx : 1 ≤ x.num) :
    qLe (qFrac 1 (armLB x)) (Quot.mk ratRel x) := by
  have hd := x.den_pos
  have he : ((armLB x : Nat) : Int) + 1 = x.den := by
    show (((x.den - 1).toNat : Nat) : Int) + 1 = x.den
    omega
  show (1 : Int) * x.den ≤ x.num * (((armLB x : Nat) : Int) + 1)
  rw [he]
  have h2 : 1 * x.den ≤ x.num * x.den :=
    Int.mul_le_mul_of_nonneg_right hx (Int.le_of_lt hd)
  exact h2

/-- **M480F-0d: 一様下界 ⟹ IsPos**（witness 添字 2N+1 で 2/(2N+2) = 1/(N+1)）。 -/
theorem arm_isPos_of_lb {x : RReal} {N : Nat}
    (h : ∀ m, qLe (qFrac 1 N) (x.seq m)) : IsPos x :=
  ⟨2 * N + 1, qLe_trans _ _ _ (qFrac_le (by omega)) (h (2 * N + 1))⟩

/-- **M480F-0e: 一様下界の積**（実数の積は加速添字でも一様下界を保つ）。
    `rinvPos` に渡せる形のまま積を取れるのが本補題の役割で、
    テンソル積のスケールと余次数の逆元構成の両方に効く。 -/
theorem arm_rmul_lb {x y : RReal} {N M : Nat}
    (hx : ∀ m, qLe (qFrac 1 N) (x.seq m))
    (hy : ∀ m, qLe (qFrac 1 M) (y.seq m)) :
    ∀ m, qLe (qFrac 1 ((N + 1) * (M + 1) - 1)) ((rmul x y).seq m) := by
  intro m
  have h0 : qLe ratRing.zero (x.seq (mulIdx (rBound x + rBound y) m)) :=
    qLe_trans _ _ _ (qFrac_nonneg 1 N) (hx _)
  have h := qLe_mul_two (hx (mulIdx (rBound x + rBound y) m))
    (hy (mulIdx (rBound x + rBound y) m)) (qFrac_nonneg 1 M) h0
  rw [qFrac_mul 1 N 1 M] at h
  exact h

/-- **M480F-0f: 非負実数の積は非負**。 -/
theorem arm_rmul_nonneg {x y : RReal} (hx : rLe realZero x)
    (hy : rLe realZero y) : rLe realZero (rmul x y) :=
  rLe_congr (rmul_zero x) (realEq_refl (rmul x y))
    (rmul_le_mul_left x hy hx)

/-- **M480F-0g: 正値有理数の逆元は非負**（下界 witness から分子 ≥ 1 を得て
    `prInv` の分岐を確定させる）。 -/
theorem arm_qInv_nonneg {N : Nat} {a : QRat} (h : qLe (qFrac 1 N) a) :
    qLe ratRing.zero (qInv a) := by
  induction a using Quot.ind
  rename_i x
  have h1 : 1 ≤ x.num := qlb_num_pos h
  have hne : x.num ≠ 0 := by omega
  show qLe ratRing.zero (Quot.mk ratRel (prInv x))
  rw [prInv_of_ne hne]
  show (0 : Int) * prInvDen x ≤ prInvNum x * 1
  rw [show prInvNum x = x.den from if_pos (by omega)]
  have hd := x.den_pos
  omega

/-! ## M480F-1: 実 ℝ-計量付き直線束

    L̄ = (L, ‖·‖) — 有限部 L = q·ℤ ⊂ ℚ（q ∈ ℚˣ）、アルキメデス部は
    **実数スケール** λ ∈ ℝ>0 による ‖x‖ = λ·|x|_∞。λ の正値性は構成的に
    使える一様下界 witness（正直な限定 4）で持つ。 -/

/-- **M480F-1a: 実 ℝ-計量付き直線束** — 生成元 q（非零・有理）と
    **実数**計量スケール λ（一様下界 witness 付き）。 -/
structure armBundle where
  /-- 生成元 q の代表（有限部 L = q·ℤ ⊂ ℚ）。 -/
  gen : PreRat
  /-- 生成元は非零（witness 形）。 -/
  gen_ne : gen.num ≠ 0
  /-- **アルキメデス計量スケール λ ∈ ℝ**（構成的実数、ℚ ではない）。 -/
  met : RReal
  /-- 正値性の一様下界の指数 N。 -/
  metLB : Nat
  /-- **λ ≥ 1/(N+1) > 0**（実順序の一様 witness）。 -/
  met_lb : ∀ m, qLe (qFrac 1 metLB) (met.seq m)

/-- 生成元の実 ℚ 値。 -/
abbrev armGen (L : armBundle) : QRat := Quot.mk ratRel L.gen

/-- **M480F-1b: スケールは実 ℝ で正**（`IsPos`）。 -/
theorem arm_met_pos (L : armBundle) : IsPos L.met := arm_isPos_of_lb L.met_lb

/-- **M480F-1c: スケールは非負**（実順序 rLe）。 -/
theorem arm_met_nonneg (L : armBundle) : rLe realZero L.met :=
  arm_rLe_zero_of_seq
    (fun m => qLe_trans _ _ _ (qFrac_nonneg 1 L.metLB) (L.met_lb m))

/-- **M480F-1d: 実 ℝ 値のアルキメデス計量** ‖s‖ := λ·|s|_∞ ∈ ℝ≥0
    （λ ∈ ℝ>0 と実絶対値 arpAbs の埋め込みの実数積）。 -/
def armNorm (L : armBundle) (s : QRat) : RReal :=
  rmul L.met (qToReal (arpAbs s))

/-- 実アルキメデス絶対値の乗法性（qAbs_mul の arpAbs 表示）。 -/
theorem arm_abs_mul (a b : QRat) :
    arpAbs (qMul a b) = qMul (arpAbs a) (arpAbs b) := qAbs_mul a b

/-! ## M480F-2: 有限部は実 ℚ の真の ℤ-部分加群（格子） -/

/-- **M480F-2a: 格子（切断の全体）** s ∈ L ⟺ ∃ m ∈ ℤ, s = q·m。 -/
def armMem (L : armBundle) (s : QRat) : Prop :=
  ∃ m : Int, s = qMul (armGen L) (ratOfInt.map m)

/-- **M480F-2b: 格子の非零元**（次数不等式の主語。m ≠ 0 を witness で持つ）。 -/
def armMemNZ (L : armBundle) (s : QRat) : Prop :=
  ∃ m : Int, m ≠ 0 ∧ s = qMul (armGen L) (ratOfInt.map m)

/-- **M480F-2c: 非零切断は切断**。 -/
theorem arm_memNZ_mem (L : armBundle) {s : QRat} (h : armMemNZ L s) :
    armMem L s := by
  apply Exists.elim h
  intro m hm
  exact ⟨m, hm.2⟩

/-- **M480F-2d: 生成元は非零切断**（q = q·1）。 -/
theorem arm_gen_memNZ (L : armBundle) : armMemNZ L (armGen L) :=
  ⟨1, by omega, (qMul_one (armGen L)).symm⟩

/-- **M480F-2e: ℤ 作用で閉じる**。 -/
theorem arm_mem_smul (L : armBundle) (m : Int) :
    armMem L (qMul (armGen L) (ratOfInt.map m)) := ⟨m, rfl⟩

/-- **M480F-2f: 加法で閉じる**（ℤ-部分加群性の核。実環準同型 ratOfInt.map_add
    と ratRing の左分配律で本物証明）。 -/
theorem arm_mem_add (L : armBundle) {s t : QRat}
    (hs : armMem L s) (ht : armMem L t) : armMem L (qAdd s t) := by
  apply Exists.elim hs
  intro m hm
  apply Exists.elim ht
  intro n hn
  refine ⟨m + n, ?_⟩
  have hadd : ratOfInt.map (m + n)
      = qAdd (ratOfInt.map m) (ratOfInt.map n) := ratOfInt.map_add m n
  have hdist : qMul (armGen L) (qAdd (ratOfInt.map m) (ratOfInt.map n))
      = qAdd (qMul (armGen L) (ratOfInt.map m))
          (qMul (armGen L) (ratOfInt.map n)) :=
    ratRing.left_distrib (armGen L) (ratOfInt.map m) (ratOfInt.map n)
  rw [hm, hn, hadd, hdist]

/-! ## M480F-3: 実 ℝ 値計量の公理 -/

/-- **M480F-3a: 計量の |·|_∞-斉次性** ‖x·s‖ ≈ |x|_∞·‖s‖（実数の realEq）。 -/
theorem arm_norm_smul (L : armBundle) (x s : QRat) :
    realEq (armNorm L (qMul x s))
      (rmul (qToReal (arpAbs x)) (armNorm L s)) := by
  show realEq (rmul L.met (qToReal (arpAbs (qMul x s))))
    (rmul (qToReal (arpAbs x)) (rmul L.met (qToReal (arpAbs s))))
  rw [arm_abs_mul x s]
  refine realEq_trans (rmul_congr_right L.met
    (realEq_symm (qToReal_mul (arpAbs x) (arpAbs s)))) ?_
  refine realEq_trans (realEq_symm (rmul_assoc_real L.met
    (qToReal (arpAbs x)) (qToReal (arpAbs s)))) ?_
  refine realEq_trans (rmul_congr_left (qToReal (arpAbs s))
    (rmul_comm L.met (qToReal (arpAbs x)))) ?_
  exact rmul_assoc_real (qToReal (arpAbs x)) L.met (qToReal (arpAbs s))

/-- **M480F-3b: 計量の非負性** 0 ≤ ‖s‖（実順序 rLe）。 -/
theorem arm_norm_nonneg (L : armBundle) (s : QRat) :
    rLe realZero (armNorm L s) :=
  arm_rmul_nonneg (arm_met_nonneg L)
    (rLe_congr (realEq_refl realZero) (realEq_refl (qToReal (arpAbs s)))
      (arm_qToReal_mono (qAbs_nonneg s)))

/-- **M480F-3c: 計量の正定値性** — 非零切断（代表 witness 形）の計量は
    実 ℝ で狭義正（`IsPos`）。ℚ 版 M474F-3c の「¬(‖s‖ ≤ 0)」対表示から
    **実数の正値 witness** へ昇格している。 -/
theorem arm_norm_pos (L : armBundle) (x : PreRat) (hx : x.num ≠ 0) :
    IsPos (armNorm L (Quot.mk ratRel x)) := by
  refine isPos_mul (arm_met_pos L) ?_
  refine arm_isPos_of_lb (N := armLB (prAbs x)) ?_
  intro m
  show qLe (qFrac 1 (armLB (prAbs x))) (Quot.mk ratRel (prAbs x))
  refine arm_preRat_lb ?_
  show 1 ≤ intAbs x.num
  have h := avi_intAbs_pos hx
  omega

/-! ## M480F-4: 実 ℝ 値の余次数と算術次数

    codeg×(L̄) := ‖q‖ = λ·|q|_∞ ∈ ℝ>0、deg×(L̄) := 1/codeg×(L̄) ∈ ℝ>0。
    古典的には deg(L̄) = −log‖q‖ で、deg× はその指数形。**値は実数**なので
    実順序 rLe による不等式が表現でき（M480F-8/9）、C4 の実 log-volume と
    同じ数体系に住む（加法形への変換 = 実 log は未構成・正直な限定 3）。 -/

/-- **M480F-4a: 実 ℝ 値の余次数** codeg×(L̄) = ‖q‖。 -/
def armCodeg (L : armBundle) : RReal := armNorm L (armGen L)

/-- 余次数の一様下界の指数（λ の下界と |q| の下界の積）。 -/
def armCodegLB (L : armBundle) : Nat :=
  (L.metLB + 1) * (armLB (prAbs L.gen) + 1) - 1

/-- **M480F-4b: 余次数の一様下界**（`rinvPos` に渡せる形）。 -/
theorem arm_codeg_lb (L : armBundle) :
    ∀ m, qLe (qFrac 1 (armCodegLB L)) ((armCodeg L).seq m) := by
  refine arm_rmul_lb L.met_lb ?_
  intro m
  show qLe (qFrac 1 (armLB (prAbs L.gen))) (Quot.mk ratRel (prAbs L.gen))
  refine arm_preRat_lb ?_
  show 1 ≤ intAbs L.gen.num
  have h := avi_intAbs_pos L.gen_ne
  omega

/-- **M480F-4c: 余次数は実 ℝ で正**。 -/
theorem arm_codeg_pos (L : armBundle) : IsPos (armCodeg L) :=
  arm_isPos_of_lb (arm_codeg_lb L)

/-- **M480F-4d: 実 ℝ 値の算術次数（本丸の対象）** deg×(L̄) := 1/‖q‖。
    M145 の choice なし正値実数逆元 `rinvPos` による**関数**（∃ 形の関係
    ではない）。値は RReal — ここが M474F（ℚ 値）からの昇格点。 -/
def armDeg (L : armBundle) : RReal :=
  rinvPos (armCodeg L) (armCodegLB L) (arm_codeg_lb L)

/-- **M480F-4e: 次数×余次数 = 1**（実数の realEq）。 -/
theorem arm_codeg_mul_deg (L : armBundle) :
    realEq (rmul (armCodeg L) (armDeg L)) (qToReal ratRing.one) :=
  rinvPos_mul_self (armCodeg L) (armCodegLB L) (arm_codeg_lb L)

/-- **M480F-4f: 可換形**。 -/
theorem arm_deg_mul_codeg (L : armBundle) :
    realEq (rmul (armDeg L) (armCodeg L)) (qToReal ratRing.one) :=
  realEq_trans (rmul_comm (armDeg L) (armCodeg L)) (arm_codeg_mul_deg L)

/-- **M480F-4g: 次数は非負**（実順序）。 -/
theorem arm_deg_nonneg (L : armBundle) : rLe realZero (armDeg L) := by
  refine arm_rLe_zero_of_seq ?_
  intro m
  exact arm_qInv_nonneg (arm_codeg_lb L (rinvIdx (armCodegLB L) m))

/-- **M480F-4h: 次数の値域は ℝ>0 全体（本モジュールの昇格の核）** —
    一様正値 witness を持つ**任意の実数** a に対し、余次数が a に等しい
    実 ℝ-計量付き直線束が存在する。M474F では余次数は必ず ℚ>0 の元で
    あったから、対象クラスと次数の像がここで真に ℝ>0 へ拡大している。 -/
theorem arm_codeg_surjective (a : RReal) (N : Nat)
    (h : ∀ m, qLe (qFrac 1 N) (a.seq m)) :
    ∃ L : armBundle, realEq (armCodeg L) a := by
  refine ⟨⟨prOne, by show (1 : Int) ≠ 0; omega, a, N, h⟩, ?_⟩
  show realEq (rmul a (qToReal (arpAbs (Quot.mk ratRel prOne)))) a
  have he : arpAbs (Quot.mk ratRel prOne) = ratRing.one := by
    apply Quot.sound
    show intAbs 1 * 1 = 1 * 1
    rw [intAbs_of_nonneg (by omega)]
  rw [he]
  exact rmul_one a

/-- **M480F-4i: 像は `IsPos` な実数の全体**（witness 形の制限は本質的でない）
    — 一様下界を持たない `IsPos a` からも、`rshift`（M145-1）で realEq
    同値な一様下界付きの代表を取れるので、余次数として実現できる。
    したがって「余次数の値域 = ℝ>0（構成的正値実数の全体、realEq 上）」。 -/
theorem arm_codeg_surjective_isPos (a : RReal) (ha : IsPos a) :
    ∃ L : armBundle, realEq (armCodeg L) a := by
  apply Exists.elim ha
  intro n hn
  refine Exists.elim (arm_codeg_surjective (rshift (2 * n + 1) a)
    (2 * n + 1) (isPos_shift_lb hn)) ?_
  intro L hL
  exact ⟨L, realEq_trans hL (rshift_eq (2 * n + 1) a)⟩

/-! ## M480F-5: 実 B5 積公式の消費 — 次数公式と切断非依存性

    任意の非零有理倍率 x に対し
      ‖q·x‖ · ∏_{p∈Supp(x)} |x|_p ≈ codeg×(L̄)
    が成り立ち、左辺は x に依らない。証明は**実 B5 積公式**
    `b5_product_formula`（|x|_∞·∏_p|x|_p = 1、実 ℚ・実絶対値）を消費する。
    循環と判定された M351F `pf_product_formula` 系は一切使わない。 -/

/-- **M480F-5a（核・実 B5 消費）**: ‖q·x‖ · ∏_{p∈Supp(x)}|x|_p ≈ codeg×(L̄)
    （実数の realEq）。 -/
theorem arm_norm_prod_section (L : armBundle) (x : PreRat) (hx : x.num ≠ 0) :
    realEq (rmul (armNorm L (qMul (armGen L) (Quot.mk ratRel x)))
        (qToReal (fspProd (fun p => pavAbs p x) (b5Support x))))
      (armCodeg L) := by
  have hb5 : qMul (arpAbs (Quot.mk ratRel x))
      (fspProd (fun p => pavAbs p x) (b5Support x)) = ratRing.one :=
    b5_product_formula x hx
  show realEq (rmul (rmul L.met
      (qToReal (arpAbs (qMul (armGen L) (Quot.mk ratRel x)))))
      (qToReal (fspProd (fun p => pavAbs p x) (b5Support x))))
    (rmul L.met (qToReal (arpAbs (armGen L))))
  rw [arm_abs_mul (armGen L) (Quot.mk ratRel x)]
  -- (λ·(|q|·|x|))·P ≈ (λ·|q|)·(|x|·P) ≈ (λ·|q|)·1 ≈ λ·|q|
  refine realEq_trans (rmul_congr_left _ (rmul_congr_right L.met
    (realEq_symm (qToReal_mul (arpAbs (armGen L))
      (arpAbs (Quot.mk ratRel x)))))) ?_
  refine realEq_trans (rmul_congr_left _ (realEq_symm
    (rmul_assoc_real L.met (qToReal (arpAbs (armGen L)))
      (qToReal (arpAbs (Quot.mk ratRel x)))))) ?_
  refine realEq_trans (rmul_assoc_real
    (rmul L.met (qToReal (arpAbs (armGen L))))
    (qToReal (arpAbs (Quot.mk ratRel x)))
    (qToReal (fspProd (fun p => pavAbs p x) (b5Support x)))) ?_
  refine realEq_trans (rmul_congr_right _
    (qToReal_mul (arpAbs (Quot.mk ratRel x))
      (fspProd (fun p => pavAbs p x) (b5Support x)))) ?_
  rw [hb5]
  exact rmul_one (rmul L.met (qToReal (arpAbs (armGen L))))

/-- **M480F-5b: 切断非依存性** — 次数データ ‖s‖·∏_p|s/q|_p は切断の取り方に
    依らない（Arakelov 次数の well-definedness の実 ℝ 形）。 -/
theorem arm_deg_section_indep (L : armBundle) (x y : PreRat)
    (hx : x.num ≠ 0) (hy : y.num ≠ 0) :
    realEq (rmul (armNorm L (qMul (armGen L) (Quot.mk ratRel x)))
        (qToReal (fspProd (fun p => pavAbs p x) (b5Support x))))
      (rmul (armNorm L (qMul (armGen L) (Quot.mk ratRel y)))
        (qToReal (fspProd (fun p => pavAbs p y) (b5Support y)))) :=
  realEq_trans (arm_norm_prod_section L x hx)
    (realEq_symm (arm_norm_prod_section L y hy))

/-- **M480F-5c: 算術次数公式** deg×(L̄)·(‖q·x‖·∏_p|x|_p) ≈ 1。 -/
theorem arm_deg_section_formula (L : armBundle) (x : PreRat) (hx : x.num ≠ 0) :
    realEq (rmul (armDeg L)
        (rmul (armNorm L (qMul (armGen L) (Quot.mk ratRel x)))
          (qToReal (fspProd (fun p => pavAbs p x) (b5Support x)))))
      (qToReal ratRing.one) :=
  realEq_trans (rmul_congr_right (armDeg L) (arm_norm_prod_section L x hx))
    (arm_deg_mul_codeg L)

/-- **M480F-5d: 整切断版**（s = q·m ∈ L、m ≠ 0）。格子の非零元に対する
    次数公式であることを `armMemNZ` で明示する（M480F-9 と同じ主語）。 -/
theorem arm_deg_integral_section (L : armBundle) (m : Int) (hm : m ≠ 0) :
    armMemNZ L (qMul (armGen L) (ratOfInt.map m)) ∧
    realEq (rmul (armDeg L)
        (rmul (armNorm L (qMul (armGen L) (Quot.mk ratRel (intToPreRat m))))
          (qToReal (fspProd (fun p => pavAbs p (intToPreRat m))
            (b5Support (intToPreRat m))))))
      (qToReal ratRing.one) :=
  ⟨⟨m, hm, rfl⟩, arm_deg_section_formula L (intToPreRat m) hm⟩

/-! ## M480F-6: テンソル積と次数の乗法性（log 形の加法性） -/

/-- **M480F-6a: 実 ℝ-計量付き直線束のテンソル積** L̄⊗M̄ = (q_L·q_M, λ_L·λ_M)。
    スケールは**実数の積** rmul であり、一様下界 witness は M480F-0e で合成する。 -/
def armTensor (L M : armBundle) : armBundle where
  gen := prMul L.gen M.gen
  gen_ne := Int.mul_ne_zero L.gen_ne M.gen_ne
  met := rmul L.met M.met
  metLB := (L.metLB + 1) * (M.metLB + 1) - 1
  met_lb := arm_rmul_lb L.met_lb M.met_lb

/-- **M480F-6b: 余次数の乗法性** codeg×(L̄⊗M̄) ≈ codeg×(L̄)·codeg×(M̄)。 -/
theorem arm_codeg_tensor (L M : armBundle) :
    realEq (armCodeg (armTensor L M))
      (rmul (armCodeg L) (armCodeg M)) := by
  show realEq (rmul (rmul L.met M.met)
      (qToReal (arpAbs (qMul (armGen L) (armGen M)))))
    (rmul (rmul L.met (qToReal (arpAbs (armGen L))))
      (rmul M.met (qToReal (arpAbs (armGen M)))))
  rw [arm_abs_mul (armGen L) (armGen M)]
  refine realEq_trans (rmul_congr_right (rmul L.met M.met)
    (realEq_symm (qToReal_mul (arpAbs (armGen L)) (arpAbs (armGen M))))) ?_
  exact rmul_mul_mul_comm L.met M.met
    (qToReal (arpAbs (armGen L))) (qToReal (arpAbs (armGen M)))

/-- **M480F-6c: 次数の乗法性（本丸1）** deg×(L̄⊗M̄) ≈ deg×(L̄)·deg×(M̄)。
    log 形では deg(L̄⊗M̄) = deg(L̄) + deg(M̄)（Arakelov 次数の加法性）。
    **値が実 ℝ の準同型**である点が M474F（ℚ 値）からの昇格。 -/
theorem arm_deg_tensor (L M : armBundle) :
    realEq (armDeg (armTensor L M)) (rmul (armDeg L) (armDeg M)) := by
  refine rinv_unique (arm_codeg_mul_deg (armTensor L M)) ?_
  refine realEq_trans (rmul_congr_left _ (arm_codeg_tensor L M)) ?_
  exact rmul_inv_mul (arm_codeg_mul_deg L) (arm_codeg_mul_deg M)

/-! ## M480F-7: 主イソメトリ捻りと次数不変性（「主因子の次数 0」の計量版） -/

/-- 1/|u|_∞ の有理数代表 den(u)/|num(u)|（choice なし）。 -/
def armInvAbsRat (u : PreRat) (hu : u.num ≠ 0) : PreRat :=
  ⟨u.den, intAbs u.num, avi_intAbs_pos hu⟩

/-- **M480F-7a: 補償等式** (1/|u|)·|u|_∞ = 1（実 ℚ の Quot.sound）。 -/
theorem arm_invAbs_mul (u : PreRat) (hu : u.num ≠ 0) :
    qMul (Quot.mk ratRel (armInvAbsRat u hu)) (arpAbs (Quot.mk ratRel u))
      = ratRing.one := by
  apply Quot.sound
  show u.den * intAbs u.num * 1 = 1 * (intAbs u.num * u.den)
  rw [Int.mul_one, Int.one_mul, Int.mul_comm u.den (intAbs u.num)]

/-- 1/|u| の一様下界（分子 = u.den ≥ 1）。 -/
theorem arm_invAbs_lb (u : PreRat) (hu : u.num ≠ 0) :
    ∀ m, qLe (qFrac 1 (armLB (armInvAbsRat u hu)))
      ((qToReal (Quot.mk ratRel (armInvAbsRat u hu))).seq m) := by
  intro m
  show qLe (qFrac 1 (armLB (armInvAbsRat u hu)))
    (Quot.mk ratRel (armInvAbsRat u hu))
  refine arm_preRat_lb ?_
  show 1 ≤ u.den
  have h := u.den_pos
  omega

/-- **M480F-7b: 主イソメトリ捻り** u·L̄ = (u·q, λ/|u|_∞)。スケールは
    実数 λ に有理数 1/|u| を掛けた**実数**。 -/
def armTwist (L : armBundle) (u : PreRat) (hu : u.num ≠ 0) : armBundle where
  gen := prMul u L.gen
  gen_ne := Int.mul_ne_zero hu L.gen_ne
  met := rmul L.met (qToReal (Quot.mk ratRel (armInvAbsRat u hu)))
  metLB := (L.metLB + 1) * (armLB (armInvAbsRat u hu) + 1) - 1
  met_lb := arm_rmul_lb L.met_lb (arm_invAbs_lb u hu)

/-- **M480F-7c: 捻りはイソメトリ** ‖u·s‖_{u·L̄} ≈ ‖s‖_{L̄}（∀ s ∈ ℚ）。 -/
theorem arm_twist_isometry (L : armBundle) (u : PreRat) (hu : u.num ≠ 0)
    (s : QRat) :
    realEq (armNorm (armTwist L u hu) (qMul (Quot.mk ratRel u) s))
      (armNorm L s) := by
  show realEq (rmul (rmul L.met (qToReal (Quot.mk ratRel (armInvAbsRat u hu))))
      (qToReal (arpAbs (qMul (Quot.mk ratRel u) s))))
    (rmul L.met (qToReal (arpAbs s)))
  rw [arm_abs_mul (Quot.mk ratRel u) s]
  refine realEq_trans (rmul_congr_right _
    (realEq_symm (qToReal_mul (arpAbs (Quot.mk ratRel u)) (arpAbs s)))) ?_
  refine realEq_trans (rmul_congr_left _
    (rmul_comm L.met (qToReal (Quot.mk ratRel (armInvAbsRat u hu))))) ?_
  refine realEq_trans (rmul_mul_mul_comm
    (qToReal (Quot.mk ratRel (armInvAbsRat u hu))) L.met
    (qToReal (arpAbs (Quot.mk ratRel u))) (qToReal (arpAbs s))) ?_
  refine realEq_trans (rmul_congr_left _
    (qToReal_mul (Quot.mk ratRel (armInvAbsRat u hu))
      (arpAbs (Quot.mk ratRel u)))) ?_
  rw [arm_invAbs_mul u hu]
  refine realEq_trans (rmul_comm (qToReal ratRing.one)
    (rmul L.met (qToReal (arpAbs s)))) ?_
  exact rmul_one (rmul L.met (qToReal (arpAbs s)))

/-- **M480F-7d: 捻りは格子の対応も保つ** — s ∈ L ⟹ u·s ∈ u·L。 -/
theorem arm_twist_mem (L : armBundle) (u : PreRat) (hu : u.num ≠ 0) {s : QRat}
    (hs : armMem L s) :
    armMem (armTwist L u hu) (qMul (Quot.mk ratRel u) s) := by
  apply Exists.elim hs
  intro m hm
  refine ⟨m, ?_⟩
  rw [hm]
  show qMul (Quot.mk ratRel u) (qMul (armGen L) (ratOfInt.map m))
    = qMul (Quot.mk ratRel (prMul u L.gen)) (ratOfInt.map m)
  exact (ratRing.mul_assoc (Quot.mk ratRel u) (armGen L) (ratOfInt.map m)).symm

/-- **M480F-7e: 捻りの余次数不変性** codeg×(u·L̄) ≈ codeg×(L̄)。 -/
theorem arm_codeg_twist (L : armBundle) (u : PreRat) (hu : u.num ≠ 0) :
    realEq (armCodeg (armTwist L u hu)) (armCodeg L) :=
  arm_twist_isometry L u hu (armGen L)

/-- **M480F-7f: 捻りの次数不変性（本丸2）** deg×(u·L̄) ≈ deg×(L̄)
    ＝「主 Arakelov 因子の次数 0」の実 ℝ-計量付き直線束版。 -/
theorem arm_deg_twist (L : armBundle) (u : PreRat) (hu : u.num ≠ 0) :
    realEq (armDeg (armTwist L u hu)) (armDeg L) := by
  refine rinv_unique (arm_codeg_mul_deg (armTwist L u hu)) ?_
  exact rinv_congr (realEq_symm (arm_codeg_twist L u hu))
    (arm_codeg_mul_deg L)

/-! ## M480F-8: 井戸定義性（正値 witness・スケールの realEq に依らない） -/

/-- **M480F-8a: 余次数の congruence** — 生成元が同じで λ ≈ λ' なら
    余次数は realEq で一致（正直な限定 4 の witness 非依存性）。 -/
theorem arm_codeg_congr {L M : armBundle} (hg : L.gen = M.gen)
    (hm : realEq L.met M.met) : realEq (armCodeg L) (armCodeg M) := by
  show realEq (rmul L.met (qToReal (arpAbs (Quot.mk ratRel L.gen))))
    (rmul M.met (qToReal (arpAbs (Quot.mk ratRel M.gen))))
  rw [hg]
  exact rmul_congr_left _ hm

/-- **M480F-8b: 次数の congruence** — 次数は正値 witness の取り方にも
    スケールの代表の取り方にも依らない。 -/
theorem arm_deg_congr {L M : armBundle} (hg : L.gen = M.gen)
    (hm : realEq L.met M.met) : realEq (armDeg L) (armDeg M) := by
  refine rinv_unique (arm_codeg_mul_deg L) ?_
  exact rinv_congr (realEq_symm (arm_codeg_congr hg hm))
    (arm_codeg_mul_deg M)

/-! ## M480F-9: 実 ℝ 値の不等式（監査が名指しした欠落の解消・本丸3）

    ここが「値が実数である」ことの本質的な使い所である。
    * `arm_codeg_le_norm`: **格子の非零元**に対して codeg×(L̄) ≤ ‖s‖。
      仮定 `armMemNZ L s` は本質的で、任意の有理数 s では偽（0<|x|<1 の
      有理倍を取れば ‖q·x‖ < ‖q‖）。格子が load-bearing になっている。
    * `arm_riemann_roch_criterion`: 0≠s∈L で ‖s‖ ≤ 1 なるものが存在
      ⟺ deg×(L̄) ≥ 1。log 形の「h⁰(L̄) ≠ 0 ⟺ deg(L̄) ≥ 0」であり、
      **実 ℝ の不等式**として述べられている。 -/

/-- ℚ 補題: 0 ≤ a かつ 1 ≤ b なら a ≤ a·b。 -/
theorem arm_qLe_self_mul {a b : QRat} (ha : qLe ratRing.zero a)
    (hb : qLe ratRing.one b) : qLe a (qMul a b) := by
  have h := qLe_mul_two (qLe_refl a) hb
    (qLe_trans _ _ _ (qLe_of_eq (rfl : ratRing.zero = ratRing.zero))
      (show qLe ratRing.zero ratRing.one from by
        show (0 : Int) * 1 ≤ (1 : Int) * 1
        omega)) ha
  rw [qMul_one a] at h
  exact h

/-- ℚ 補題: 非零整数の絶対値は 1 以上（|m|_∞ ≥ 1）。 -/
theorem arm_intAbs_ge_one {m : Int} (hm : m ≠ 0) :
    qLe ratRing.one (arpAbs (ratOfInt.map m)) := by
  show (1 : Int) * 1 ≤ intAbs m * 1
  have h := avi_intAbs_pos hm
  omega

/-- **M480F-9a（本丸3・格子 load-bearing）: 格子の非零切断の計量は余次数以上**
    codeg×(L̄) ≤ ‖s‖（∀ 0 ≠ s ∈ L）。すなわち codeg×(L̄) は格子の
    非零元のノルムの最小値（rank 1 の第一逐次最小）。 -/
theorem arm_codeg_le_norm (L : armBundle) {s : QRat} (hs : armMemNZ L s) :
    rLe (armCodeg L) (armNorm L s) := by
  apply Exists.elim hs
  intro m hm
  have hm0 : m ≠ 0 := hm.1
  have hs' : s = qMul (armGen L) (ratOfInt.map m) := hm.2
  rw [hs']
  show rLe (rmul L.met (qToReal (arpAbs (armGen L))))
    (rmul L.met (qToReal (arpAbs (qMul (armGen L) (ratOfInt.map m)))))
  rw [arm_abs_mul (armGen L) (ratOfInt.map m)]
  refine rmul_le_mul_left L.met ?_ (arm_met_nonneg L)
  refine arm_qToReal_mono ?_
  exact arm_qLe_self_mul (qAbs_nonneg (armGen L)) (arm_intAbs_ge_one hm0)

/-- **M480F-9b: 小さい切断の存在判定（乗法形）** — 0≠s∈L で ‖s‖ ≤ 1 なる
    ものが存在 ⟺ codeg×(L̄) ≤ 1。 -/
theorem arm_small_section_iff (L : armBundle) :
    (∃ s : QRat, armMemNZ L s ∧ rLe (armNorm L s) (qToReal ratRing.one))
      ↔ rLe (armCodeg L) (qToReal ratRing.one) := by
  constructor
  · intro h
    apply Exists.elim h
    intro s hs
    exact rLe_trans (arm_codeg_le_norm L hs.1) hs.2
  · intro h
    exact ⟨armGen L, arm_gen_memNZ L, h⟩

/-- **M480F-9c: 余次数 ≤ 1 ⟹ 次数 ≥ 1**（正値実数の逆元は順序を反転）。 -/
theorem arm_deg_ge_one_of_codeg_le_one (L : armBundle)
    (h : rLe (armCodeg L) (qToReal ratRing.one)) :
    rLe (qToReal ratRing.one) (armDeg L) :=
  rLe_congr
    (realEq_trans (rmul_comm (armDeg L) (armCodeg L)) (arm_codeg_mul_deg L))
    (rmul_one (armDeg L))
    (rmul_le_mul_left (armDeg L) h (arm_deg_nonneg L))

/-- **M480F-9d: 次数 ≥ 1 ⟹ 余次数 ≤ 1**（逆向き）。 -/
theorem arm_codeg_le_one_of_deg_ge_one (L : armBundle)
    (h : rLe (qToReal ratRing.one) (armDeg L)) :
    rLe (armCodeg L) (qToReal ratRing.one) :=
  rLe_congr
    (rmul_one (armCodeg L))
    (arm_codeg_mul_deg L)
    (rmul_le_mul_left (armCodeg L) h (arm_norm_nonneg L (armGen L)))

/-- **M480F-9e（見出し）: 算術 Riemann–Roch 型判定（乗法形）** —
    L̄ が長さ ≤ 1 の非零切断を持つ ⟺ deg×(L̄) ≥ 1。
    log 形では「h⁰(L̄) ≠ 0 ⟺ deg(L̄) ≥ 0」。左辺は**格子の非零元**に
    ついての存在命題、右辺は**実 ℝ の不等式**であり、M474F では（次数が
    ℚ 値・格子が未使用だったため）どちらも表現できなかった。 -/
theorem arm_riemann_roch_criterion (L : armBundle) :
    (∃ s : QRat, armMemNZ L s ∧ rLe (armNorm L s) (qToReal ratRing.one))
      ↔ rLe (qToReal ratRing.one) (armDeg L) := by
  constructor
  · intro h
    exact arm_deg_ge_one_of_codeg_le_one L
      ((arm_small_section_iff L).mp h)
  · intro h
    exact (arm_small_section_iff L).mpr
      (arm_codeg_le_one_of_deg_ge_one L h)

/-- **M480F-9f: 計量の支配 ⟹ 余次数の不等式**（同じ生成元・λ_L ≤ λ_M）。 -/
theorem arm_codeg_mono {L M : armBundle} (hg : L.gen = M.gen)
    (hm : rLe L.met M.met) : rLe (armCodeg L) (armCodeg M) := by
  show rLe (rmul L.met (qToReal (arpAbs (Quot.mk ratRel L.gen))))
    (rmul M.met (qToReal (arpAbs (Quot.mk ratRel M.gen))))
  rw [hg]
  refine rmul_le_mul_right hm ?_
  exact arm_qToReal_mono (qAbs_nonneg (Quot.mk ratRel M.gen))

/-- **M480F-9g: 計量の支配 ⟹ 次数の逆向き不等式** deg×(M̄) ≤ deg×(L̄)
    （log 形: 計量が大きいほど次数は小さい）。実 ℝ の不等式が次数の間で
    伝播することの証明であり、C4 の実 log-volume と同じ順序体で比較できる
    ようになったことを示す。 -/
theorem arm_deg_anti {L M : armBundle} (hg : L.gen = M.gen)
    (hm : rLe L.met M.met) : rLe (armDeg M) (armDeg L) := by
  have hprod : rLe realZero (rmul (armDeg L) (armDeg M)) :=
    arm_rmul_nonneg (arm_deg_nonneg L) (arm_deg_nonneg M)
  have hstep : rLe (rmul (armCodeg L) (rmul (armDeg L) (armDeg M)))
      (rmul (armCodeg M) (rmul (armDeg L) (armDeg M))) :=
    rmul_le_mul_right (arm_codeg_mono hg hm) hprod
  -- 左辺 ≈ deg M、右辺 ≈ deg L
  have hL : realEq (rmul (armCodeg L) (rmul (armDeg L) (armDeg M)))
      (armDeg M) :=
    realEq_trans (realEq_symm (rmul_assoc_real (armCodeg L) (armDeg L)
        (armDeg M)))
      (realEq_trans (rmul_congr_left (armDeg M) (arm_codeg_mul_deg L))
        (realEq_trans (rmul_comm (qToReal ratRing.one) (armDeg M))
          (rmul_one (armDeg M))))
  have hM : realEq (rmul (armCodeg M) (rmul (armDeg L) (armDeg M)))
      (armDeg L) :=
    realEq_trans (rmul_congr_right (armCodeg M)
        (rmul_comm (armDeg L) (armDeg M)))
      (realEq_trans (realEq_symm (rmul_assoc_real (armCodeg M) (armDeg M)
          (armDeg L)))
        (realEq_trans (rmul_congr_left (armDeg L) (arm_codeg_mul_deg M))
          (realEq_trans (rmul_comm (qToReal ratRing.one) (armDeg L))
            (rmul_one (armDeg L)))))
  exact rLe_congr hL hM hstep

/-! ## M480F-10: ℚ スケール族の埋め込みと具体例

    M474F（aml）の対象クラス = 計量スケールが ℚ>0 の族は、`armOfRat` により
    本モジュールの対象クラスの**部分族**として埋まる。逆は成り立たない
    （M480F-4h により余次数は任意の正値実数を取る）。 -/

/-- **M480F-10a: ℚ スケール族の埋め込み** — M474F の (q, λ∈ℚ>0) を
    実 ℝ-スケール束として実現する。 -/
def armOfRat (g : PreRat) (hg : g.num ≠ 0) (lam : PreRat)
    (hl : 0 < lam.num) : armBundle where
  gen := g
  gen_ne := hg
  met := qToReal (Quot.mk ratRel lam)
  metLB := armLB lam
  met_lb := fun _ => arm_preRat_lb (by omega)

/-- **M480F-10b: 埋め込みは計量を保つ** — ℚ スケール束の実計量は
    λ·|s|_∞ の実数版（M474F の `amlNorm` の像）。 -/
theorem arm_ofRat_norm (g : PreRat) (hg : g.num ≠ 0) (lam : PreRat)
    (hl : 0 < lam.num) (s : QRat) :
    realEq (armNorm (armOfRat g hg lam hl) s)
      (qToReal (qMul (Quot.mk ratRel lam) (arpAbs s))) :=
  qToReal_mul (Quot.mk ratRel lam) (arpAbs s)

/-- **M480F-10c: 自明束** O̅ = (ℤ ⊂ ℚ, |·|_∞)。 -/
def armTrivial : armBundle :=
  armOfRat prOne (by show (1 : Int) ≠ 0; omega) prOne (by show (0 : Int) < 1; omega)

/-- **M480F-10d: 自明束の余次数 ≈ 1**（log 形では deg(O̅) = 0）。 -/
theorem arm_codeg_trivial : realEq (armCodeg armTrivial) (qToReal ratRing.one) := by
  show realEq (rmul (qToReal (Quot.mk ratRel prOne))
    (qToReal (arpAbs (Quot.mk ratRel prOne)))) (qToReal ratRing.one)
  have he : arpAbs (Quot.mk ratRel prOne) = ratRing.one := by
    apply Quot.sound
    show intAbs 1 * 1 = 1 * 1
    rw [intAbs_of_nonneg (by omega)]
  rw [he]
  exact rmul_one (qToReal (Quot.mk ratRel prOne))

/-- **M480F-10e: 自明束の次数 ≈ 1**。 -/
theorem arm_deg_trivial : realEq (armDeg armTrivial) (qToReal ratRing.one) := by
  refine rinv_unique (arm_codeg_mul_deg armTrivial) ?_
  refine realEq_trans (rmul_congr_left _ arm_codeg_trivial) ?_
  exact rmul_one (qToReal ratRing.one)

/-- **M480F-10f: 自明束は Riemann–Roch 判定を満たす**（deg×(O̅) ≥ 1 なので
    長さ ≤ 1 の非零切断 s = 1 ∈ ℤ を持つ）。 -/
theorem arm_trivial_has_small_section :
    ∃ s : QRat, armMemNZ armTrivial s
      ∧ rLe (armNorm armTrivial s) (qToReal ratRing.one) :=
  (arm_small_section_iff armTrivial).mpr
    (rLe_of_realEq arm_codeg_trivial)

/-- **M480F-10g: 非空虚性** — 生成元 2、スケール 3/2 の束（M474F-8d の
    実 ℝ-スケール版）。 -/
def armExample : armBundle :=
  armOfRat ⟨2, 1, by omega⟩ (by show (2 : Int) ≠ 0; omega)
    ⟨3, 2, by omega⟩ (by show (0 : Int) < 3; omega)

/-- **M480F-10h: 具体例の余次数 ≈ 3**（(3/2)·|2|_∞ = 3、自明束と異なる値
    ＝ 次数は定数関数ではない）。 -/
theorem arm_example_codeg :
    realEq (armCodeg armExample) (qToReal (ratOfInt.map (3 : Int))) := by
  show realEq (rmul (qToReal (Quot.mk ratRel ⟨3, 2, by omega⟩))
      (qToReal (arpAbs (Quot.mk ratRel ⟨2, 1, by omega⟩))))
    (qToReal (ratOfInt.map (3 : Int)))
  refine realEq_trans (qToReal_mul (Quot.mk ratRel ⟨3, 2, by omega⟩)
    (arpAbs (Quot.mk ratRel ⟨2, 1, by omega⟩))) ?_
  refine realEq_of_seq_eq ?_
  intro n
  show qMul (Quot.mk ratRel ⟨3, 2, by omega⟩)
      (Quot.mk ratRel (prAbs ⟨2, 1, by omega⟩)) = ratOfInt.map (3 : Int)
  apply Quot.sound
  show 3 * intAbs 2 * 1 = 3 * (2 * 1)
  rw [intAbs_of_nonneg (show (0 : Int) ≤ 2 by omega)]
  omega

end IUT

-- 公理検査（全て [propext, Quot.sound] であること）
#print axioms IUT.arm_met_pos
#print axioms IUT.arm_mem_add
#print axioms IUT.arm_norm_smul
#print axioms IUT.arm_norm_nonneg
#print axioms IUT.arm_norm_pos
#print axioms IUT.arm_codeg_pos
#print axioms IUT.arm_codeg_mul_deg
#print axioms IUT.arm_deg_nonneg
#print axioms IUT.arm_codeg_surjective
#print axioms IUT.arm_codeg_surjective_isPos
#print axioms IUT.arm_norm_prod_section
#print axioms IUT.arm_deg_section_indep
#print axioms IUT.arm_deg_section_formula
#print axioms IUT.arm_deg_integral_section
#print axioms IUT.arm_codeg_tensor
#print axioms IUT.arm_deg_tensor
#print axioms IUT.arm_twist_isometry
#print axioms IUT.arm_twist_mem
#print axioms IUT.arm_codeg_twist
#print axioms IUT.arm_deg_twist
#print axioms IUT.arm_codeg_congr
#print axioms IUT.arm_deg_congr
#print axioms IUT.arm_codeg_le_norm
#print axioms IUT.arm_small_section_iff
#print axioms IUT.arm_riemann_roch_criterion
#print axioms IUT.arm_codeg_mono
#print axioms IUT.arm_deg_anti
#print axioms IUT.arm_deg_trivial
#print axioms IUT.arm_trivial_has_small_section
#print axioms IUT.arm_example_codeg
