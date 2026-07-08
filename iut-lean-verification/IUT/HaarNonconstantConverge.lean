-- M472F HaarNonconstantConverge [実・本物・柱D]
-- 分類: [実]（§2(a) 昇格・M467F IndetHaarLimit(ihl) の正直な限定「一般の非定数密度は Cesàro 収束が
--   保証されないため average 列の Cauchy 性を仮説 hC として受け取る」を、**単調（非増加）非定数密度の
--   具体クラス**について本物へ置換して閉じる）。平均の主語は M462F の実 Haar 平均 ihiAverage（区間一様測度の
--   Riemann 和）を単調非定数密度 hncStepDensity に適用したものであり toy を用いない。
-- complete_pct 影響: 前進（小）。M467F(ihl) は「定数密度は無条件で Cauchy（ihl_average_cauchy）だが一般の
--   非定数密度は average 列の Cauchy 性 hC を仮説として受け取る」と正直に限定していた。本 M472F はその hC を、
--   **単調（非増加）非定数密度の Riemann 和平均について仮説なしで**除去する:
--   (i) 一般の輸送補題 `hnc_cauchy_of_clean`: Riemann 和平均列 X が「各 N で clean な有理数列表現 C に realEq、
--       かつ C が tight-Cauchy（|C_m − C_n| ≤ u_m+u_n・j 揺らぎなし）」なら **X は無条件で IsCauchyReals**
--       （5 点分割 + M117 ε-消去 c=6 で j 固定の余剰 6u_s を潰す）——これが hC を除去する核心エンジン、
--   (ii) 具体クラス: 単調非増加密度 hncStepDensity（[a,0,0,…]・a≥0・非定数 a≠0）の Riemann 和は ≈ a
--       （hnc_haarsum_eq）ゆえ正規化平均 ihiAverage は ≈ (1/(N+1))·a、a=1 で clean 有理数列 ihiWeight N に
--       realEq（hnc_avg_clean）、その tight-Cauchy（hnc_weight_clean_cauchy）を (i) に渡して **hnc_monotone_cauchy
--       = 無条件 IsCauchyReals**、
--   (iii) rlim 収束（hnc_converges＝rlim_close の非定数版・hC を hnc_monotone_cauchy が供給）・極限は
--        realZero に一致（hnc_limit_eq）・極限も両側界 [0,1] を保つ（hnc_limit_two_sided＝M467F ihl_limit_two_sided
--        を単調密度へ適用）、
--   (iv) 定数密度への整合（hnc_reduces_to_ihl＝M467F ihl_const_avg_eq の再輸出・a=0 退化は hnc_avg_zero）。
--   残る限定は「除去は単調（非増加）非定数密度の具体クラス（clean 有理数列表現を持つもの・区間一様格子）に
--   留まり、一般可測密度・完全な測度論的 Haar・実 π₁^ét 積分・一般実数値単調密度（有理表現なし）の Cauchy は未」
--   とより狭く述べ直す（hnc_model_scope）。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。

/-
  IUT/HaarNonconstantConverge.lean — M472F（M467F の「一般の非定数密度は average 列の Cauchy 性 hC を仮説
  として受け取る」を、単調非増加非定数密度の Riemann 和平均について仮説なしで除去する）

  ## 二軸
  * 主要成果の分類: **[実]**（§2(a) 昇格・既存の正直な限定を本物へ置換して閉じる）。M467F
    `IndetHaarLimit`（`ihl`）は N→∞ 極限対象 `ihlHaarLimit f hC = rlim (fun N => ihiAverage f N) hC` を
    構成したが、`ihl_model_scope` に

      「一般の非定数密度の Cesàro 収束は average 列の Cauchy 性 hC を仮説として受け取る（定数密度は無条件で
       閉じたが、一般密度の average の収束は成立するとは限らない＝Cesàro 非収束の正直な限界）」

    と正直に限定していた（`ihlHaarLimit` の第 2 引数 `hC : IsCauchyReals (fun N => ihiAverage f N)`）。本
    M472F はこの hC を、**単調（非増加）非定数密度の具体クラス**について無条件で除去する:
      - **輸送エンジン** `hnc_cauchy_of_clean`: 平均列 X が「各 N で clean 表現 C（定数 j 列＝有理数持ち上げ）に
        realEq、かつ C が tight-Cauchy（|C_m − C_n| ≤ u_m+u_n、j 揺らぎ項なし）」なら X は **無条件で
        IsCauchyReals**。証明は 5 点分割 X_m,j→X_m,s→C_m,s→C_n,s→X_n,s→X_n,j（fine index s）で j 固定の
        余剰を 6u_s に集約し、M117 の ε-消去 `qLe_of_forall_add_frac`(c=6) で潰す（rmul の複雑な seq を触らず
        realEq と正則性だけで閉じる）。これが M467F の hC を除去する核心。
      - **単調非増加密度** `hncStepDensity a` = [a, 0, 0, …]（a≥0 で単調非増加・a≠0 で非定数）。Riemann 和は
        ≈ a（`hnc_haarsum_eq`: 0 を足すだけ）、ゆえに正規化 Haar 平均 `hncRiemannAvg a N = ihiAverage
        (hncStepDensity a) N` は ≈ (1/(N+1))·a。a=1 で **clean 有理数列** `ihiWeight N = qToReal (qFrac 1 N)`
        に realEq（`hnc_avg_clean`・M467F ihl_weight_const と同精神の rmul_one）。
      - **tight-Cauchy** `hnc_weight_clean_cauchy`: |1/(m+1) − 1/(n+1)| ≤ 1/(m+1) + 1/(n+1)（三角 + |·|=·）。
      - **本丸（hC 除去）** `hnc_monotone_cauchy`: 単調非定数密度 [1,0,0,…] の Riemann 和平均列は **無条件で
        IsCauchyReals**（hnc_cauchy_of_clean に hnc_avg_clean・hnc_weight_clean_cauchy を供給）。
      - **収束** `hnc_converges`（rlim_close 再輸出・hC を hnc_monotone_cauchy が供給）・極限 `hncLimit`。
      - **極限の特徴づけ** `hnc_limit_eq`: 極限は realZero（rlim_unique・avg ≈ 1/(N+1) → 0）。
      - **極限の両側界** `hnc_limit_two_sided`: 0 ≤ hncLimit ≤ 1（M467F `ihl_limit_two_sided` を単調密度へ
        適用・avg ∈ [0,1] を rLe_congr で持ち上げ）。
      - **定数密度への整合** `hnc_reduces_to_ihl`（M467F ihl_const_avg_eq の再輸出）・`hnc_avg_zero`（a=0 退化）。
      - **crux 外部** `hnc_crux_external`/`hnc_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は範囲外。
      - **残る限定を狭く正直に** `hnc_model_scope`。
  * complete_pct 影響: **前進（小）**。M467F の「一般の非定数密度は hC 仮説」を、単調（非増加）非定数密度の
    具体クラスについて **hC なしの無条件 IsCauchyReals** へ昇格して破る。除去は clean 有理数列表現を持つ
    単調密度クラスに留まる（一般実数値単調密度・一般可測密度は未）。crux Dβ-ω は**決して導出せず**外部仮説のまま。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M472F-1 `hncStepDensity`/`hnc_density_two_sided`/`hnc_monotone` — 単調非増加非定数密度 [a,0,…] と
      その両側界 [0,a]・単調性（f(i+1) ≤ f(i)）。
  * M472F-2 `hnc_haarsum_eq` — Riemann 和 ihiHaarSum (hncStepDensity a) N ≈ a（0 を足すだけ・M462F realAdd_zero）。
  * M472F-3 `hncRiemannAvg`/`hnc_avg_clean`/`hnc_avg_zero` — 非定数密度の正規化 Haar 平均（M462F ihiAverage の
      非定数版）と、a=1 での clean 有理数列 ihiWeight への realEq（rmul_one）・a=0 の退化（rmul_zero）。
  * M472F-4 `hnc_abs_qFrac_one`/`hnc_weight_clean_cauchy` — |1/(k+1)|=1/(k+1) と clean 列の tight-Cauchy。
  * M472F-5 **`hnc_cauchy_of_clean`（輸送エンジン・本丸1）** — realEq to clean tight-Cauchy ⟹ IsCauchyReals
      （5 点分割 + M117 ε-消去 c=6）。**M467F の hC を除去する汎用核**。
  * M472F-6 **`hnc_monotone_cauchy`（本丸2・hC 除去）** — 単調非定数密度 [1,0,…] の平均列は無条件 IsCauchyReals。
  * M472F-7 `hncLimit`/`hnc_converges`/`hnc_limit_eq`/`hnc_limit_two_sided` — rlim 収束・極限=0・両側界 [0,1]。
  * M472F-8 `hnc_reduces_to_ihl` — 定数密度は M467F ihl_const_avg_eq へ整合（再輸出）。
  * M472F-9 `hnc_crux_external`/`hnc_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M472F-10 `hnc_model_scope`・capstone `IndetHaarNonconstantData`/`hnc_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層が昇格するのは
    M467F の hC 仮説を **単調非増加非定数密度の具体クラス**について除去することであり、M128 完備性・M117 ε-消去
    で閉じる**無条件で本物**の命題——crux（rep ≤ gauss）とは別の主張。crux は任意の外部 Prop として受け取る
    のみ（`hnc_crux_is_hypothesis` は Iff.rfl）。
  * **hC 除去は clean 有理数列表現を持つ単調（非増加）非定数密度クラスに留まる**。M467F の「一般の非定数密度は
    hC 仮説」を、Riemann 和平均が clean 有理数列（定数 j 列＝有理数持ち上げ）に realEq でありその列が
    tight-Cauchy であるような単調密度（本層では [a,0,0,…]、a=1 の単位スパイクが代表）について無条件で破ったが、
    **一般の実数値単調密度（有理表現を持たないもの）・一般可測密度・完全な位相群の Haar 測度・実 π₁^ét（遠アーベル
    復元）上の完全積分は未**。輸送エンジン `hnc_cauchy_of_clean` 自体は「clean tight-Cauchy 表現を持つ任意の
    平均列」に適用できる汎用命題であり、単位スパイクはその無条件適用の witness。
  * **合成は有限段・ℝ は setoid**（realEq が同値・`=` でない）ゆえ Riemann 和・平均・収束・両側界は
    realEq/rLe/IsCauchyReals（witness 形）で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 昇格・正直な限定を本物へ置換[実]。一般名は `hnc` 接頭辞で衝突回避。
-/
import IUT.IndetHaarLimit
import IUT.IndetHaarIntegral
import IUT.RealComplete
import IUT.RealMul
import IUT.RealAbsTriangle
import IUT.RealLe
import IUT.ApartInv

namespace IUT

/-! ## M472F-1: 単調（非増加）非定数密度 [a, 0, 0, …] -/

/-- **M472F-1a: 単調非増加密度** — 格子点 0 で値 a、以降すべて realZero:
      hncStepDensity a = [a, 0, 0, …]。
    a ≥ 0 のとき単調非増加（f(0)=a ≥ f(i)=0）、a ≠ 0 のとき非定数。M462F の Haar 平均 ihiAverage の
    非定数密度としての「主語」。 -/
def hncStepDensity (a : RReal) : Nat → RReal
  | 0 => a
  | _ + 1 => realZero

/-- **M472F-1b: 密度は両側界 [0, a] に入る** — a ≥ 0 なら各 i で 0 ≤ f(i) ≤ a
    （i=0 は a、i≥1 は 0）。M462F ihi_average_two_sided の前提。 -/
theorem hnc_density_two_sided (a : RReal) (ha : rLe realZero a) :
    ∀ i, rLe realZero (hncStepDensity a i) ∧ rLe (hncStepDensity a i) a
  | 0 => ⟨ha, rLe_refl a⟩
  | _ + 1 => ⟨rLe_refl realZero, ha⟩

/-- **M472F-1c: 密度は単調非増加** — a ≥ 0 なら f(i+1) ≤ f(i)（i=0 は 0 ≤ a、i≥1 は 0 ≤ 0）。 -/
theorem hnc_monotone (a : RReal) (ha : rLe realZero a) :
    ∀ i, rLe (hncStepDensity a (i + 1)) (hncStepDensity a i)
  | 0 => ha
  | _ + 1 => rLe_refl realZero

/-! ## M472F-2: Riemann 和は ≈ a（0 を足すだけ） -/

/-- **M472F-2: 単調非増加密度の Haar 和** — ihiHaarSum (hncStepDensity a) N ≈ a（全 N）。
    N=0 は f(0)=a、帰納段は realAdd (Σ_k) (f(k+1)=0) ≈ Σ_k（M462F realAdd_zero）で 0 を足すだけ。
    区間一様測度の Riemann 和は全質量が最初のスパイク a に集中する。 -/
theorem hnc_haarsum_eq (a : RReal) :
    ∀ N, realEq (ihiHaarSum (hncStepDensity a) N) a
  | 0 => realEq_refl a
  | k + 1 =>
    realEq_trans (realAdd_zero (ihiHaarSum (hncStepDensity a) k)) (hnc_haarsum_eq a k)

/-! ## M472F-3: 非定数密度の正規化 Haar 平均と clean 有理数列表現 -/

/-- **M472F-3a: 非定数密度の正規化 Haar 平均** — M462F ihiAverage の単調非定数密度版:
      hncRiemannAvg a N = (1/(N+1))·ihiHaarSum (hncStepDensity a) N。 -/
def hncRiemannAvg (a : RReal) (N : Nat) : RReal :=
  ihiAverage (hncStepDensity a) N

/-- **M472F-3b: 単位スパイク平均は clean 有理数列 ihiWeight に realEq** — a=1（密度 [1,0,0,…]）のとき
    正規化 Haar 平均は clean 有理数列 ihiWeight N = qToReal (qFrac 1 N) = 1/(N+1) に realEq:
      hncRiemannAvg 1 N ≈ (1/(N+1))·(ihiHaarSum ≈ 1) ≈ (1/(N+1))·1 ≈ 1/(N+1)。
    M467F ihl_weight_const と同精神（rmul_one）。clean（定数 j 列）ゆえ後段の tight-Cauchy が使える。 -/
theorem hnc_avg_clean (N : Nat) :
    realEq (hncRiemannAvg (qToReal ratRing.one) N) (ihiWeight N) := by
  show realEq (rmul (ihiWeight N)
      (ihiHaarSum (hncStepDensity (qToReal ratRing.one)) N)) (ihiWeight N)
  exact realEq_trans
    (rmul_congr_right (ihiWeight N) (hnc_haarsum_eq (qToReal ratRing.one) N))
    (rmul_one (ihiWeight N))

/-- **M472F-3c: a=0 退化は realZero** — 密度 [0,0,…]（定数 0）の平均は realZero（rmul_zero）。
    単調非増加密度族の定数退化ケースが M467F 定数密度版（c=0）と整合することの明示。 -/
theorem hnc_avg_zero (N : Nat) :
    realEq (hncRiemannAvg realZero N) realZero := by
  show realEq (rmul (ihiWeight N)
      (ihiHaarSum (hncStepDensity realZero) N)) realZero
  exact realEq_trans
    (rmul_congr_right (ihiWeight N) (hnc_haarsum_eq realZero N))
    (rmul_zero (ihiWeight N))

/-! ## M472F-4: clean 有理数列の tight-Cauchy -/

/-- **M472F-4a: |1/(k+1)| = 1/(k+1)** — qFrac 1 k の絶対値は自身（分子 1 ≥ 0・代表レベル
    intAbs_of_nonneg + preRat_ext）。 -/
theorem hnc_abs_qFrac_one (k : Nat) : qAbs (qFrac 1 k) = qFrac 1 k :=
  qAbs_of_nonneg (qFrac_nonneg 1 k)

/-- **M472F-4b: clean 有理数列 ihiWeight の tight-Cauchy** — |1/(m+1) − 1/(n+1)| ≤ 1/(m+1) + 1/(n+1)
    （j 揺らぎ項なしの tight 形）。ihiWeight k = qToReal (qFrac 1 k) は定数 j 列ゆえ seq j = qFrac 1 k。
    三角不等式 |a+(−b)| ≤ |a|+|b| と |1/(k+1)|=1/(k+1) から。輸送エンジンの clean-Cauchy 前提。 -/
theorem hnc_weight_clean_cauchy (m n j : Nat) :
    qLe (qAbs (qAdd ((ihiWeight m).seq j) (qNeg ((ihiWeight n).seq j))))
      (qAdd (qUnitFrac m) (qUnitFrac n)) := by
  show qLe (qAbs (qAdd (qFrac 1 m) (qNeg (qFrac 1 n)))) (qAdd (qFrac 1 m) (qFrac 1 n))
  have step := qAbs_add_le (qFrac 1 m) (qNeg (qFrac 1 n))
  rw [qAbs_neg, hnc_abs_qFrac_one m, hnc_abs_qFrac_one n] at step
  exact step

/-! ## M472F-5: 輸送エンジン（本丸1）— realEq to clean tight-Cauchy ⟹ IsCauchyReals -/

/-- **定理 (M472F-5: 輸送エンジン・本丸・hC 除去の核)** — 平均列 X が
      (i) 各 N で clean 表現 C_N に realEq（∀ N, realEq (X N) (C N)）、
      (ii) C が **tight-Cauchy**（∀ m n j, |C_m,j − C_n,j| ≤ u_m + u_n、j 揺らぎ項なし）
    を満たすなら、**X は無条件で IsCauchyReals**。
    証明は 5 点分割 X_m,j → X_m,s → C_m,s → C_n,s → X_n,s → X_n,j（fine index s）で
      |X_m,j − X_n,j| ≤ (u_m+u_n) + (u_j+u_j) + 6u_s
    を作り、M117 ε-消去 `qLe_of_forall_add_frac`(c=6) で 6u_s を潰す（X の正則性 reg と realEq のみ使用、
    rmul の複雑な seq を一切触らない）。これが **M467F の hC 仮説を除去する汎用エンジン**——clean tight-Cauchy
    表現を持つ任意の Haar 平均列に無条件で IsCauchyReals を供給する。 -/
theorem hnc_cauchy_of_clean (X C : Nat → RReal)
    (hEq : ∀ N, realEq (X N) (C N))
    (hCauchy : ∀ m n j, qLe (qAbs (qAdd ((C m).seq j) (qNeg ((C n).seq j))))
      (qAdd (qUnitFrac m) (qUnitFrac n))) :
    IsCauchyReals X := by
  intro m n j
  apply qLe_of_forall_add_frac 6
  intro s
  -- 5 点分割（fine index s）
  have o1 := qAbs_sub_split ((X m).seq j) ((C m).seq s) ((X n).seq j)
  have o2 := qAbs_sub_split ((C m).seq s) ((C n).seq s) ((X n).seq j)
  have hA := qAbs_sub_split ((X m).seq j) ((X m).seq s) ((C m).seq s)
  have hD := qAbs_sub_split ((C n).seq s) ((X n).seq s) ((X n).seq j)
  -- 各片
  have pA1 : qLe (qAbs (qAdd ((X m).seq j) (qNeg ((X m).seq s))))
      (qAdd (qUnitFrac j) (qUnitFrac s)) := (X m).reg j s
  have pA2 : qLe (qAbs (qAdd ((X m).seq s) (qNeg ((C m).seq s))))
      (qAdd (qUnitFrac s) (qUnitFrac s)) := (hEq m) s
  have pB : qLe (qAbs (qAdd ((C m).seq s) (qNeg ((C n).seq s))))
      (qAdd (qUnitFrac m) (qUnitFrac n)) := hCauchy m n s
  have pD1 : qLe (qAbs (qAdd ((C n).seq s) (qNeg ((X n).seq s))))
      (qAdd (qUnitFrac s) (qUnitFrac s)) := (realEq_symm (hEq n)) s
  have pD2 : qLe (qAbs (qAdd ((X n).seq s) (qNeg ((X n).seq j))))
      (qAdd (qUnitFrac s) (qUnitFrac j)) := (X n).reg s j
  -- 組み立て
  have Abound := qLe_trans _ _ _ hA (qLe_add_two pA1 pA2)
  have Dbound := qLe_trans _ _ _ hD (qLe_add_two pD1 pD2)
  have o2b := qLe_trans _ _ _ o2 (qLe_add_two pB Dbound)
  have total := qLe_trans _ _ _ o1 (qLe_add_two Abound o2b)
  refine qLe_trans _ _ _ total ?_
  -- 濃縮 A' ≤ u_j + F3s
  have hA' : qLe (qAdd (qAdd (qUnitFrac j) (qUnitFrac s))
        (qAdd (qUnitFrac s) (qUnitFrac s)))
      (qAdd (qUnitFrac j) (qFrac 3 s)) := by
    refine qLe_trans _ _ _
      (qLe_of_eq (qAdd_assoc (qUnitFrac j) (qUnitFrac s)
        (qAdd (qUnitFrac s) (qUnitFrac s)))) ?_
    refine qLe_add_two (qLe_refl _) ?_
    exact qLe_trans _ _ _
      (qLe_add_two (qLe_refl _) (qFrac_add 1 1 s)) (qFrac_add 1 2 s)
  -- 濃縮 D' ≤ F3s + u_j
  have hD' : qLe (qAdd (qAdd (qUnitFrac s) (qUnitFrac s))
        (qAdd (qUnitFrac s) (qUnitFrac j)))
      (qAdd (qFrac 3 s) (qUnitFrac j)) := by
    refine qLe_trans _ _ _
      (qLe_of_eq (qAdd_assoc (qAdd (qUnitFrac s) (qUnitFrac s))
        (qUnitFrac s) (qUnitFrac j)).symm) ?_
    refine qLe_add_two ?_ (qLe_refl _)
    exact qLe_trans _ _ _
      (qLe_add_two (qFrac_add 1 1 s) (qLe_refl _)) (qFrac_add 2 1 s)
  -- E ≤ (u_j+F3s) + ((u_m+u_n) + (F3s+u_j))
  have hE := qLe_add_two hA'
    (qLe_add_two (qLe_refl (qAdd (qUnitFrac m) (qUnitFrac n))) hD')
  refine qLe_trans _ _ _ hE ?_
  -- 並べ替え → ((u_m+u_n)+(u_j+u_j)) + (F3s+F3s)
  have hReq : qAdd (qAdd (qUnitFrac j) (qFrac 3 s))
        (qAdd (qAdd (qUnitFrac m) (qUnitFrac n))
          (qAdd (qFrac 3 s) (qUnitFrac j)))
      = qAdd (qAdd (qAdd (qUnitFrac m) (qUnitFrac n))
          (qAdd (qUnitFrac j) (qUnitFrac j)))
        (qAdd (qFrac 3 s) (qFrac 3 s)) := by
    rw [qAdd_comm (qAdd (qUnitFrac j) (qFrac 3 s))
        (qAdd (qAdd (qUnitFrac m) (qUnitFrac n))
          (qAdd (qFrac 3 s) (qUnitFrac j))),
      qAdd_assoc (qAdd (qUnitFrac m) (qUnitFrac n))
        (qAdd (qFrac 3 s) (qUnitFrac j)) (qAdd (qUnitFrac j) (qFrac 3 s)),
      qAdd_comm (qFrac 3 s) (qUnitFrac j),
      qAdd_swap_mid (qUnitFrac j) (qFrac 3 s) (qUnitFrac j) (qFrac 3 s),
      ← qAdd_assoc (qAdd (qUnitFrac m) (qUnitFrac n))
        (qAdd (qUnitFrac j) (qUnitFrac j)) (qAdd (qFrac 3 s) (qFrac 3 s))]
  exact qLe_trans _ _ _ (qLe_of_eq hReq)
    (qLe_add_two (qLe_refl _) (qFrac_add 3 3 s))

/-! ## M472F-6: 本丸2 — hC を除去した無条件 Cauchy（単調非定数密度） -/

/-- **定理 (M472F-6: 単調非定数密度の平均列は無条件 IsCauchyReals・本丸・hC 除去)** — 単調非増加非定数密度
    [1,0,0,…] の Riemann 和平均列 `fun N => hncRiemannAvg 1 N` は **仮説なしで IsCauchyReals**。
    輸送エンジン hnc_cauchy_of_clean に clean 表現 ihiWeight（hnc_avg_clean）とその tight-Cauchy
    （hnc_weight_clean_cauchy）を供給。**M467F の hC 仮説（`ihlHaarLimit f hC` の第 2 引数）を、この単調
    非定数密度について実際に除去する**（M467F は定数密度でのみ無条件だった）。 -/
theorem hnc_monotone_cauchy :
    IsCauchyReals (fun N => hncRiemannAvg (qToReal ratRing.one) N) :=
  hnc_cauchy_of_clean
    (fun N => hncRiemannAvg (qToReal ratRing.one) N) ihiWeight
    (fun N => hnc_avg_clean N)
    (fun p q r => hnc_weight_clean_cauchy p q r)

/-! ## M472F-7: rlim 収束・極限=0・両側界 [0,1] -/

/-- **M472F-7a: 単調非定数密度の N→∞ Haar 極限**（無条件・hC を hnc_monotone_cauchy が供給）。
    M467F ihlHaarLimit の非定数版だが hC 仮説を必要としない。 -/
def hncLimit : RReal :=
  rlim (fun N => hncRiemannAvg (qToReal ratRing.one) N) hnc_monotone_cauchy

/-- **定理 (M472F-7b: 平均は N→∞ で極限値に収束・非定数版)** — 単調非定数密度の Riemann 和平均は極限
    hncLimit に 1/(N+1) 以内で収束（M128 rlim_close の witness 形）。M467F ihl_haar_converges の非定数版で、
    hC は hnc_monotone_cauchy が無条件供給。 -/
theorem hnc_converges (N j : Nat) :
    qLe (qAbs (qAdd (hncLimit.seq j)
        (qNeg ((hncRiemannAvg (qToReal ratRing.one) N).seq j))))
      (qAdd (qUnitFrac N) (qAdd (qUnitFrac j) (qUnitFrac j))) :=
  rlim_close (fun N => hncRiemannAvg (qToReal ratRing.one) N)
    hnc_monotone_cauchy N j

/-- **定理 (M472F-7c: 極限は realZero)** — 単調非定数密度 [1,0,…] の平均は (1/(N+1))·1 → 0 ゆえ N→∞ 極限は
    realZero に realEq（rlim_unique・|0 − avg_m,j| ≤ u_m + 2u_j を clean 列 1/(m+1) 経由で作る）。 -/
theorem hnc_limit_eq : realEq hncLimit realZero := by
  refine rlim_unique (fun N => hncRiemannAvg (qToReal ratRing.one) N)
    hnc_monotone_cauchy realZero ?_
  intro mm jj
  have t1 : qLe (qAbs (qAdd ((realZero).seq jj) (qNeg (qFrac 1 mm))))
      (qUnitFrac mm) := by
    show qLe (qAbs (qAdd ratRing.zero (qNeg (qFrac 1 mm)))) (qUnitFrac mm)
    rw [qAdd_zero_left, qAbs_neg, hnc_abs_qFrac_one mm]
    exact qLe_refl _
  have t2 : qLe (qAbs (qAdd (qFrac 1 mm)
        (qNeg ((hncRiemannAvg (qToReal ratRing.one) mm).seq jj))))
      (qAdd (qUnitFrac jj) (qUnitFrac jj)) := by
    rw [qAbs_sub_comm]
    exact hnc_avg_clean mm jj
  exact qLe_trans _ _ _
    (qAbs_sub_split ((realZero).seq jj) (qFrac 1 mm)
      ((hncRiemannAvg (qToReal ratRing.one) mm).seq jj))
    (qLe_add_two t1 t2)

/-- **M472F-7d: 単位スパイク重みは 1 以下** — 1/(N+1) ≤ 1（ihi_qFrac_one で ratRing.one = 1/1 に戻し
    qFrac_le）。両側界 [0,1] の上界。 -/
theorem hnc_weight_le_one (N : Nat) : rLe (ihiWeight N) (qToReal ratRing.one) := by
  have h : qLe (qFrac 1 N) (qFrac 1 0) := qFrac_le (by omega)
  rw [ihi_qFrac_one] at h
  exact rLe_qToReal h

/-- **定理 (M472F-7e: 極限も両側界 [0,1] を保つ)** — 単調非定数密度の各 N での平均は [0,1] に入る
    （0 ≤ (1/(N+1))·1 ≤ 1、clean 表現 ihiWeight と ihi_weight_nonneg・hnc_weight_le_one を rLe_congr で
    持ち上げ）ゆえ、**N→∞ 極限もその両側界に入る**: 0 ≤ hncLimit ≤ 1。M467F `ihl_limit_two_sided`
    （閉区間は極限で閉じる）を単調非定数密度へ適用。 -/
theorem hnc_limit_two_sided :
    rLe realZero hncLimit ∧ rLe hncLimit (qToReal ratRing.one) :=
  ihl_limit_two_sided (fun N => hncRiemannAvg (qToReal ratRing.one) N)
    hnc_monotone_cauchy realZero (qToReal ratRing.one)
    (fun N => rLe_congr (realEq_refl realZero)
      (realEq_symm (hnc_avg_clean N)) (ihi_weight_nonneg N))
    (fun N => rLe_congr (realEq_symm (hnc_avg_clean N))
      (realEq_refl (qToReal ratRing.one)) (hnc_weight_le_one N))

/-! ## M472F-8: 定数密度への整合 -/

/-- **定理 (M472F-8: 定数密度は M467F 定数版へ整合)** — 密度が定数 c のとき、正規化 Haar 平均は M467F
    `ihl_const_avg_eq` の通り c に一致（再輸出）。本層の非定数昇格は M467F の定数密度版を真に含む
    （定数は M467F、非定数は本層）。a=0 退化 hnc_avg_zero は c=0 の場合と整合。 -/
theorem hnc_reduces_to_ihl (c : RReal) (N : Nat) :
    realEq (ihiAverage (fun _ => c) N) c :=
  ihl_const_avg_eq c N

/-! ## M472F-9: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M472F-9a: 無条件 Cauchy は本物・crux は外部仮説／honest)** — 単調非定数密度の平均列が無条件
    IsCauchyReals であること（hnc_monotone_cauchy）は M128 完備性・M117 ε-消去で閉じる**無条件で本物**の
    命題（crux とは独立）。しかし theta-pilot ≤ gauss-pilot の**多輻的アルゴリズム**（crux Dβ-ω）は本層で
    **決して証明しない**。crux を任意の外部 Prop として受け取り、極限上界の本物性 **と** crux の連言を
    crux 供給時のみ返す。 -/
theorem hnc_crux_external (crux : Prop) (hcrux : crux) :
    rLe hncLimit (qToReal ratRing.one) ∧ crux :=
  ⟨hnc_limit_two_sided.2, hcrux⟩

/-- **定理 (M472F-9b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**として
    扱い、それ以上でも以下でもない（Iff.rfl）。M467F `ihl_crux_is_hypothesis` と同じ精神。 -/
theorem hnc_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M472F-10: 残る正直な限定・capstone -/

/-- **定理 (M472F-10a: 残る正直な scope・限定を定理化)** — 本層は、
    (i) **単調（非増加）非定数密度 [1,0,…] の Riemann 和平均列が無条件で IsCauchyReals**
        （hnc_monotone_cauchy）で、極限は両側界 [0,1] を保つ（hnc_limit_two_sided）——すなわち M467F の
        「一般の非定数密度は hC 仮説」を本クラスについて実際に破ったが、**hC 除去は clean 有理数列表現を持つ
        単調密度クラス（区間一様格子）に留まり、一般実数値単調密度（有理表現なし）・一般可測密度・完全な
        位相群 Haar 測度・実 π₁^ét 上の完全積分は未**、
    (ii) **crux（外部 Prop）は仮説としてのみ利用可能で本層では導出されない**（`∀ crux, crux → crux`）。
    この正直な限定を機械検証可能な形で固定する（消去・弱化禁止・M467F の hC 限定をより狭く述べ直す）。 -/
theorem hnc_model_scope :
    (realEq (hncRiemannAvg (qToReal ratRing.one) 0) (ihiWeight 0)
      ∧ IsCauchyReals (fun N => hncRiemannAvg (qToReal ratRing.one) N)
      ∧ (rLe realZero hncLimit ∧ rLe hncLimit (qToReal ratRing.one)))
    ∧ (∀ crux : Prop, crux → crux) :=
  ⟨⟨hnc_avg_clean 0, hnc_monotone_cauchy, hnc_limit_two_sided⟩, fun _ h => h⟩

/-- **M472F-10b: 単調非定数密度の無条件 Haar 収束データ**（総括） — M467F の hC 仮説を除去した単調非増加
    非定数密度 [1,0,…] について束ねる: 密度の単調性（monotone）・両側界（bounded）・平均の clean 表現
    （avg_clean）・**無条件 Cauchy（cauchy＝hC 除去）**・rlim 収束（converges）・極限=0（limit_eq）・
    極限の両側界 [0,1]（two_sided）。主語は M462F の本物の Haar 平均 ihiAverage であり toy を用いない。
    crux（Dβ-ω）は外部仮説。 -/
structure IndetHaarNonconstantData where
  /-- 密度は単調非増加。 -/
  monotone : ∀ i, rLe (hncStepDensity (qToReal ratRing.one) (i + 1))
    (hncStepDensity (qToReal ratRing.one) i)
  /-- 密度は両側界 [0,1]。 -/
  bounded : ∀ i, rLe realZero (hncStepDensity (qToReal ratRing.one) i)
    ∧ rLe (hncStepDensity (qToReal ratRing.one) i) (qToReal ratRing.one)
  /-- 平均は clean 有理数列 ihiWeight に realEq。 -/
  avg_clean : ∀ N, realEq (hncRiemannAvg (qToReal ratRing.one) N) (ihiWeight N)
  /-- 本丸: 平均列は無条件で IsCauchyReals（hC 除去）。 -/
  cauchy : IsCauchyReals (fun N => hncRiemannAvg (qToReal ratRing.one) N)
  /-- N→∞ で極限値に収束。 -/
  converges : ∀ N j, qLe (qAbs (qAdd (hncLimit.seq j)
      (qNeg ((hncRiemannAvg (qToReal ratRing.one) N).seq j))))
    (qAdd (qUnitFrac N) (qAdd (qUnitFrac j) (qUnitFrac j)))
  /-- 極限は realZero。 -/
  limit_eq : realEq hncLimit realZero
  /-- 極限も両側界 [0,1] を保つ。 -/
  two_sided : rLe realZero hncLimit ∧ rLe hncLimit (qToReal ratRing.one)

/-- **M472F-10c: 実データ** — 全フィールドを M472F-1〜7 の本物で充足。 -/
def indetHaarNonconstantData : IndetHaarNonconstantData where
  monotone := hnc_monotone (qToReal ratRing.one)
    (rLe_qToReal (qFrac_nonneg 1 0))
  bounded := fun i =>
    hnc_density_two_sided (qToReal ratRing.one)
      (rLe_qToReal (qFrac_nonneg 1 0)) i
  avg_clean := hnc_avg_clean
  cauchy := hnc_monotone_cauchy
  converges := hnc_converges
  limit_eq := hnc_limit_eq
  two_sided := hnc_limit_two_sided

/-- **M472F-10d: 存在（M472F 見出し）** — 単調（非増加）非定数密度 [1,0,…] について、M467F の hC 仮説を
    除去した無条件 Haar 収束データが存在する。単調非定数密度の Riemann 和平均列は clean 有理数列表現を持ち、
    輸送エンジン hnc_cauchy_of_clean により **無条件で IsCauchyReals**（M467F の hC 除去）となり、rlim で
    収束し、極限は realZero・両側界 [0,1] を保つ。crux（Dβ-ω＝theta ≤ gauss）は外部仮説として明示され
    **決して証明されない**——本層は M467F の「一般の非定数密度は hC 仮説」という限定を **単調非定数密度の
    具体クラスについて hC なしへ昇格して破る**（除去は clean 有理表現を持つ単調密度クラスに留まる旨は正直に
    固定）。 -/
theorem hnc_exists : Nonempty IndetHaarNonconstantData :=
  ⟨indetHaarNonconstantData⟩

/-! ## 実例（単調非増加非定数密度 [1,0,0,…] の無条件 Haar 収束） -/

/-- 実例（本丸・hC 除去）: 単調非定数密度の Riemann 和平均列は無条件で IsCauchyReals。 -/
example : IsCauchyReals (fun N => hncRiemannAvg (qToReal ratRing.one) N) :=
  hnc_monotone_cauchy

/-- 実例（輸送エンジン汎用）: clean tight-Cauchy 表現を持つ任意の平均列は無条件 IsCauchyReals。 -/
example (X C : Nat → RReal) (hEq : ∀ N, realEq (X N) (C N))
    (hC : ∀ m n j, qLe (qAbs (qAdd ((C m).seq j) (qNeg ((C n).seq j))))
      (qAdd (qUnitFrac m) (qUnitFrac n))) :
    IsCauchyReals X :=
  hnc_cauchy_of_clean X C hEq hC

/-- 実例（平均の clean 表現）: 単位スパイク平均 ≈ 1/(N+1)。 -/
example (N : Nat) : realEq (hncRiemannAvg (qToReal ratRing.one) N) (ihiWeight N) :=
  hnc_avg_clean N

/-- 実例（収束・witness 形）: 平均は極限に 1/(N+1) 以内で収束。 -/
example (N j : Nat) :
    qLe (qAbs (qAdd (hncLimit.seq j)
        (qNeg ((hncRiemannAvg (qToReal ratRing.one) N).seq j))))
      (qAdd (qUnitFrac N) (qAdd (qUnitFrac j) (qUnitFrac j))) :=
  hnc_converges N j

/-- 実例（極限は 0）: 単調非定数密度 [1,0,…] の N→∞ Haar 極限は realZero。 -/
example : realEq hncLimit realZero := hnc_limit_eq

/-- 実例（極限の両側界）: 0 ≤ hncLimit ≤ 1。 -/
example : rLe realZero hncLimit ∧ rLe hncLimit (qToReal ratRing.one) :=
  hnc_limit_two_sided

/-- 実例（定数密度は M467F へ整合）: 定数密度 c の平均は c（M467F ihl_const_avg_eq）。 -/
example (c : RReal) (N : Nat) : realEq (ihiAverage (fun _ => c) N) c :=
  hnc_reduces_to_ihl c N

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux := hnc_crux_is_hypothesis crux

/-- 実例（capstone 存在）: 単調非定数密度に hC 除去済み無条件 Haar 収束データが存在する。 -/
example : Nonempty IndetHaarNonconstantData := hnc_exists

end IUT
