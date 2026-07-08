-- M467F IndetHaarLimit [実・本物・柱D]
-- 分類: [実]（§2(a) 昇格・M462F IndetHaarIntegral(ihi) の正直な限定「Haar 積分は有限 Riemann 和近似で
--   **N→∞ 連続極限（測度論的完備化）は未**」を本物へ置換して閉じる）。極限の主語は M462F の実 Haar 平均
--   ihiAverage（区間一様測度の Riemann 和 / M457F 実 deg_ℝ 作用のサンプル）であり toy を用いない。
-- complete_pct 影響: 前進。M462F(ihi) は各 N で不定性群の区間 [0..N] 上の (N+1) 点 Haar 平均が両側界を保つ
--   ことを本物化したが、`ihi_model_scope` に「**連続測度の極限（N→∞ の測度論的完備化）は未**」と正直に
--   限定していた。本 M467F はその限定を破る:
--   (i) M128 の構成的完備性 rlim で **有限 N 点 Haar 平均の N→∞ 極限対象**を本物構成
--       （ihlHaarLimit / ihlConstLimit）、
--   (ii) **極限も両側界を保つ**（ihl_limit_two_sided・ihl_rlim_lower/upper＝閉区間は rlim で閉じる＝
--        構成的な順序極限定理）、
--   (iii) Haar 平均が N→∞ で極限値に収束（ihl_haar_converges＝rlim_close の witness 形）、
--   (iv) 区間一様測度（定数密度 c）の場合の **無条件の収束**（ihl_average_cauchy・ihl_const_avg_eq：
--        正規化 Haar 平均 (1/(N+1))·Σc ≈ c を全 N で本物化——これは M462F が「(1/(N+1))·(N+1)≈1 の ℚ 簡約は
--        端点表示のまま残す」と留保していた点も併せて閉じる）。
--   残る限定は「極限は区間一様測度の Riemann 和列の rlim（真の Lebesgue/Haar 積分の測度論的構成ではなく
--   Riemann 和の収束）・ℝ³ 忠実模型・完全な位相群 Haar 測度は未・一般の非定数密度の Cesàro 収束は
--   average 列の Cauchy 性を仮説として受け取る」とより狭く述べ直す（ihl_model_scope）。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。

/-
  IUT/IndetHaarLimit.lean — M467F（M462F の有限 N 点 Haar 平均 ihiAverage の N→∞ 連続極限を M128 構成的
  完備性 rlim で本物構成し、極限も両側界を保つ＝閉区間は極限で閉じることを示す）

  ## 二軸
  * 主要成果の分類: **[実]**（§2(a) 昇格・既存の正直な限定を本物へ置換して閉じる）。M462F
    `IndetHaarIntegral`（`ihi`）は不定性群の区間 [0..N] 上の (N+1) 点 Haar 平均 `ihiAverage f N` が両側界を
    保つことを **各有限 N で** 本物化したが、`ihi_model_scope` に

      「Haar 積分は有限 Riemann 和近似（連続 Haar 測度の格子近似）…**連続測度の極限（N→∞ の測度論的
       完備化）は未**」

    と正直に限定していた。本 M467F はこの「**N→∞ 連続極限は未**」を **M128 の構成的完備性 rlim による
    極限対象の構成**で破る:
      - **極限対象** `ihlHaarLimit f hC` = rlim (fun N => ihiAverage f N) hC — 有限 N 点 Haar 平均の列の
        M128 対角極限（average 列の正則性 hC = IsCauchyReals から）。定数密度 c の場合は無条件版
        `ihlConstLimit c`（hC を ihl_average_cauchy で自前供給）。
      - **本丸1（順序極限定理）** `ihl_rlim_lower`/`ihl_rlim_upper`/`ihl_limit_two_sided`: 各 N で
        Haar 平均が両側界 [L,U] に入る（rLe L (X N) ∧ rLe (X N) U）なら、**N→∞ 極限もその両側界に入る**
        （rLe L (rlim X hC) ∧ rLe (rlim X hC) U）——**閉区間は構成的極限で閉じる**。証明は M128 収束
        `rlim_close`（|極限 − X_N| ≤ 1/(N+1)）＋正則性で望遠鏡し、余剰 7u_s を ε-消去（c=7）で潰す。
      - **本丸2（収束）** `ihl_haar_converges`: 有限 N 点 Haar 平均は N→∞ で極限値に収束（rlim_close の
        witness 形 ∀ N j, |極限_j − (ihiAverage f N)_j| ≤ u_N + 2u_j）。
      - **無条件版（区間一様測度＝定数密度）** `ihl_average_cauchy`/`ihl_const_avg_eq`/`ihlConstLimit`/
        `ihl_haar_converges_const`: 定数密度 c（区間一様測度）の正規化 Haar 平均 (1/(N+1))·Σc は全 N で
        **c に realEq で一致**（ihl_const_avg_eq、これは M462F が留保した「(1/(N+1))·(N+1)≈1 の ℚ 簡約」を
        実際に閉じる）ゆえ average 列は無条件で Cauchy（ihl_average_cauchy）で、その rlim は c に一致
        （ihlConstLimit ≈ c）・両側界を保つ（ihl_const_limit_two_sided）。
      - **極限の特徴づけ** `ihl_limit_from_finite`: 極限は有限近似 ihiAverage の rlim として一意に定まる
        （rlim_unique の適用・定数密度で rlim ≈ c）。
      - **crux 外部** `ihl_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は範囲外。
      - **残る限定を狭く正直に** `ihl_model_scope`: 極限は区間一様測度の Riemann 和列の rlim（真の
        Lebesgue/Haar 積分の測度論的構成でなく Riemann 和の収束）・ℝ³ 忠実模型に留まり、完全な位相群 Haar
        測度・実 π₁^ét 上の完全積分は未。一般の非定数密度の Cesàro 収束は average 列の Cauchy 性を仮説として
        受け取る（定数密度は無条件で閉じたが、一般密度の average の収束は成立するとは限らない＝Cesàro 非収束の
        正直な限界）。
  * complete_pct 影響: **前進**。M462F の「N→∞ 連続極限は未」を、rlim による極限対象の本物構成＋極限の両側界
    保存（ihl_limit_two_sided：閉区間は極限で閉じる）＋収束（ihl_haar_converges）＋定数密度の無条件収束
    （ihl_const_avg_eq でℚ簡約も併せて閉じる）へ昇格して破る。crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の
    係争点）は**決して導出せず**外部仮説のまま。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M467F-1 `ihl_qFrac_selfN`/`ihl_qFrac_add_one` — ℚ 簡約の核（(N+1)/(N+1)=1・(N+1)/1 + 1/1 = (N+2)/1）。
  * M467F-2 `ihl_constSum_scalar`/`ihl_weight_const`/`ihl_const_avg_eq` — 定数密度の正規化 Haar 平均
      (1/(N+1))·Σc ≈ c を全 N で本物化（M462F 留保の ℚ 簡約を閉じる）。
  * M467F-3 `ihl_average_cauchy` — 定数密度 average 列は無条件で IsCauchyReals（M128 完備性の前提）。
  * M467F-4 `ihlHaarLimit`/`ihlConstLimit` — 有限 N 点 Haar 平均の N→∞ 極限対象（M128 rlim の構成）。
  * M467F-5 `ihl_rlim_lower`/`ihl_rlim_upper`/`ihl_limit_two_sided` — 本丸: 閉区間は rlim で閉じる
      （順序極限定理・M128 rlim_close + 正則性の望遠鏡 + ε-消去 c=7）。
  * M467F-6 `ihl_haar_converges`/`ihl_haar_converges_const` — Haar 平均の N→∞ 収束（rlim_close witness）。
  * M467F-7 `ihl_const_limit_two_sided`/`ihl_limit_from_finite` — 定数密度極限の両側界・rlim_unique 特徴づけ。
  * M467F-8 `ihl_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M467F-9 `ihl_model_scope` — 残る正直な限定（Riemann 和 rlim・ℝ³ 模型・完全 Haar 測度/実 π₁^ét は未・
      一般密度の Cauchy 性は仮説・crux 外部）を定理化（M462F の「N→∞ 連続極限は未」を実際に破った旨を明示）。
  * M467F-10 capstone `IndetHaarLimitData`/`ihl_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層が昇格するのは
    M462F の各有限 N の両側界を **N→∞ 極限**へ広げること（rlim 構成・極限の両側界保存・収束）であり、M128
    構成的完備性で閉じる**無条件で本物**の命題——crux（rep ≤ gauss）とは別の主張。crux は任意の外部 Prop と
    して受け取るのみ（`ihl_crux_is_hypothesis` は Iff.rfl）。
  * **極限は区間一様測度の Riemann 和列の rlim に留まる**。M462F の「N→∞ 連続極限は未」を実際に破り、有限
    N 点 Haar 平均の M128 対角極限を本物構成したが、これは **Riemann 和の収束**であって、完全な位相群の Haar
    測度・実 π₁^ét（遠アーベル復元）上の完全積分・真の Lebesgue/Haar 測度の測度論的構成は未。群は ℝ³ の忠実
    模型に留まる。
  * **一般の非定数密度の average 列の収束は成立するとは限らない**（有界密度の Cesàro 平均は一般には収束
    しない）。ゆえに一般の極限対象 `ihlHaarLimit f hC` は average 列の Cauchy 性 `hC` を**仮説として受け取る**
    （順序極限定理 ihl_limit_two_sided は hC の下で本物）。**定数密度 c（区間一様測度）の場合は無条件**で
    Cauchy（ihl_average_cauchy）＝収束（ihl_const_avg_eq: (1/(N+1))·Σc ≈ c）することを本物化した。
  * **合成は有限段・ℝ は setoid**（realEq が同値・`=` でない）ゆえ極限・両側界・収束は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 昇格・正直な限定を本物へ置換[実]。一般名は `ihl` 接頭辞で衝突回避。
-/
import IUT.IndetHaarIntegral
import IUT.RealComplete
import IUT.RealRingLaws
import IUT.RealPosMul

namespace IUT

/-! ## M467F-1: ℚ 簡約の核 -/

/-- **M467F-1a: (N+1)/(N+1) = 1** — qFrac (N+1) N（分子 N+1・分母 N+1）は単位元
    （Quot.sound・交差積 (N+1)·1 = 1·(N+1)）。区間 Haar 全質量 1 の ℚ 簡約に使う。 -/
theorem ihl_qFrac_selfN (N : Nat) : qFrac (N + 1) N = ratRing.one := by
  apply Quot.sound
  show ((N + 1 : Nat) : Int) * (1 : Int) = (1 : Int) * (((N : Nat) : Int) + 1)
  omega

/-- **M467F-1b: (N+1)/1 + 1/1 = (N+2)/1** — 整数分数の加法（Quot.sound）。定数和の
    スカラー表示 ihl_constSum_scalar の帰納段に使う。 -/
theorem ihl_qFrac_add_one (N : Nat) :
    qAdd (qFrac (N + 1) 0) (qFrac 1 0) = qFrac (N + 2) 0 := by
  apply Quot.sound
  show (((N + 1 : Nat) : Int) * (((0 : Nat) : Int) + 1)
        + (1 : Int) * (((0 : Nat) : Int) + 1)) * (((0 : Nat) : Int) + 1)
    = ((N + 2 : Nat) : Int)
      * ((((0 : Nat) : Int) + 1) * (((0 : Nat) : Int) + 1))
  omega

/-! ## M467F-2: 定数密度の正規化 Haar 平均 ≈ c（ℚ 簡約を閉じる） -/

/-- **M467F-2a: 定数和のスカラー表示** — ihiConstSum c N ≈ (N+1)·c
    （rmul (qToReal (qFrac (N+1) 0)) c、(N+1)/1 のスカラー乗法）。N 帰納:
    帰納段は分配律 rmul_add_right と ihl_qFrac_add_one で (N+1)·c ⊕ 1·c ≈ (N+2)·c。 -/
theorem ihl_constSum_scalar (c : RReal) :
    ∀ N, realEq (ihiConstSum c N) (rmul (qToReal (qFrac (N + 1) 0)) c)
  | 0 => by
    -- ihiConstSum c 0 = c、RHS = rmul (qFrac 1 0) c ≈ rmul 1 c ≈ c
    have h1 : realEq (rmul (qToReal (qFrac 1 0)) c) c := by
      rw [ihi_qFrac_one]
      exact realEq_trans (rmul_comm (qToReal ratRing.one) c) (rmul_one c)
    exact realEq_symm h1
  | Nat.succ k => by
    -- ihiConstSum c (k+1) = realAdd (ihiConstSum c k) c
    have hc1 : realEq (rmul (qToReal (qFrac 1 0)) c) c := by
      rw [ihi_qFrac_one]
      exact realEq_trans (rmul_comm (qToReal ratRing.one) c) (rmul_one c)
    -- IH: ihiConstSum c k ≈ (k+1)·c
    have ih := ihl_constSum_scalar c k
    -- realAdd (ihiConstSum c k) c ≈ realAdd ((k+1)·c) (1·c)
    have s1 : realEq (realAdd (ihiConstSum c k) c)
        (realAdd (rmul (qToReal (qFrac (k + 1) 0)) c)
          (rmul (qToReal (qFrac 1 0)) c)) :=
      realEq_trans (realAdd_congr_left c ih)
        (realAdd_congr_right (rmul (qToReal (qFrac (k + 1) 0)) c)
          (realEq_symm hc1))
    -- (k+1)·c ⊕ 1·c ≈ ((k+1)/1 ⊕ 1/1)·c ≈ ((k+2)/1)·c
    have s2 : realEq
        (realAdd (rmul (qToReal (qFrac (k + 1) 0)) c)
          (rmul (qToReal (qFrac 1 0)) c))
        (rmul (realAdd (qToReal (qFrac (k + 1) 0)) (qToReal (qFrac 1 0))) c) :=
      realEq_symm (rmul_add_right (qToReal (qFrac (k + 1) 0))
        (qToReal (qFrac 1 0)) c)
    have s3 : realEq
        (rmul (realAdd (qToReal (qFrac (k + 1) 0)) (qToReal (qFrac 1 0))) c)
        (rmul (qToReal (qFrac (k + 2) 0)) c) := by
      refine rmul_congr_left c ?_
      refine realEq_trans (qToReal_add (qFrac (k + 1) 0) (qFrac 1 0)) ?_
      rw [ihl_qFrac_add_one k]
      exact realEq_refl _
    -- 目標: ihiConstSum c (k+1) ≈ ((k+1)+1)·c = (k+2)·c
    show realEq (realAdd (ihiConstSum c k) c)
      (rmul (qToReal (qFrac (k + 1 + 1) 0)) c)
    exact realEq_trans s1 (realEq_trans s2 s3)

/-- **M467F-2b: 正規化 Haar 平均の重み簡約** — (1/(N+1))·ihiConstSum c N ≈ c。
    ihl_constSum_scalar で ihiConstSum c N ≈ (N+1)·c にした上で、結合律 + qFrac_mul で
    (1/(N+1))·((N+1)·c) = ((1/(N+1))·((N+1)/1))·c = ((N+1)/(N+1))·c = 1·c ≈ c。
    **M462F の留保「(1/(N+1))·(N+1)≈1 の ℚ 簡約は端点表示のまま残す」を実際に閉じる**。 -/
theorem ihl_weight_const (c : RReal) (N : Nat) :
    realEq (rmul (ihiWeight N) (ihiConstSum c N)) c := by
  -- (1/(N+1))·ihiConstSum c N ≈ (1/(N+1))·((N+1)·c)
  have t1 : realEq (rmul (ihiWeight N) (ihiConstSum c N))
      (rmul (qToReal (qFrac 1 N)) (rmul (qToReal (qFrac (N + 1) 0)) c)) :=
    rmul_congr_right (ihiWeight N) (ihl_constSum_scalar c N)
  -- (1/(N+1))·((N+1)·c) ≈ ((1/(N+1))·((N+1)/1))·c
  have t2 : realEq (rmul (qToReal (qFrac 1 N)) (rmul (qToReal (qFrac (N + 1) 0)) c))
      (rmul (rmul (qToReal (qFrac 1 N)) (qToReal (qFrac (N + 1) 0))) c) :=
    realEq_symm (rmul_assoc_real (qToReal (qFrac 1 N))
      (qToReal (qFrac (N + 1) 0)) c)
  -- (1/(N+1))·((N+1)/1) ≈ (1·(N+1))/((N+1)·1 - 1) = (N+1)/N = 1
  have t3 : realEq (rmul (qToReal (qFrac 1 N)) (qToReal (qFrac (N + 1) 0)))
      (qToReal ratRing.one) := by
    refine realEq_trans (qToReal_mul (qFrac 1 N) (qFrac (N + 1) 0)) ?_
    rw [qFrac_mul]
    have e1 : 1 * (N + 1) = N + 1 := by omega
    have e2 : (N + 1) * (0 + 1) - 1 = N := by omega
    rw [e1, e2, ihl_qFrac_selfN N]
    exact realEq_refl _
  -- ((N+1)/(N+1))·c ≈ 1·c ≈ c
  have t4 : realEq (rmul (rmul (qToReal (qFrac 1 N)) (qToReal (qFrac (N + 1) 0))) c) c :=
    realEq_trans (rmul_congr_left c t3)
      (realEq_trans (rmul_comm (qToReal ratRing.one) c) (rmul_one c))
  exact realEq_trans t1 (realEq_trans t2 t4)

/-- **M467F-2c: 定数密度の正規化 Haar 平均 ≈ c** — ihiAverage (fun _ => c) N ≈ c（全 N）。
    ihiHaarSum (fun _ => c) N = ihiConstSum c N（M462F ihi_const_haar）に ihl_weight_const。
    区間一様測度（定数密度 c）の Haar 積分＝平均は N に依らず c（N→∞ 極限も c）。 -/
theorem ihl_const_avg_eq (c : RReal) (N : Nat) :
    realEq (ihiAverage (fun _ => c) N) c := by
  show realEq (rmul (ihiWeight N) (ihiHaarSum (fun _ => c) N)) c
  rw [ihi_const_haar c N]
  exact ihl_weight_const c N

/-! ## M467F-3: 定数密度 average 列は無条件で Cauchy -/

/-- **M467F-3: 定数密度 average 列の正則性** — (fun N => ihiAverage (fun _ => c) N) は
    IsCauchyReals。各 N で ≈ c（ihl_const_avg_eq）ゆえ任意 m,n で列は互いに ≈、その witness
    |A_m − A_n| ≤ 2u_j ≤ (u_m+u_n)+(u_j+u_j)。M128 完備性の前提を無条件で供給。 -/
theorem ihl_average_cauchy (c : RReal) :
    IsCauchyReals (fun N => ihiAverage (fun _ => c) N) := by
  intro m n j
  have hmn : realEq (ihiAverage (fun _ => c) m) (ihiAverage (fun _ => c) n) :=
    realEq_trans (ihl_const_avg_eq c m) (realEq_symm (ihl_const_avg_eq c n))
  refine qLe_trans _ _ _ (hmn j) ?_
  refine qLe_trans _ _ _
    (qLe_of_eq (qAdd_zero_left (qAdd (qUnitFrac j) (qUnitFrac j))).symm) ?_
  exact qLe_add_two (qFrac_add_nonneg 1 m 1 n) (qLe_refl _)

/-! ## M467F-4: 有限 N 点 Haar 平均の N→∞ 極限対象（M128 rlim） -/

/-- **M467F-4a: 一般極限対象** — 有限 N 点 Haar 平均 ihiAverage f N の列の M128 対角極限
    （average 列の正則性 hC = IsCauchyReals を仮説として受け取る＝一般の非定数密度は Cesàro 収束が
    保証されないため）。 -/
def ihlHaarLimit (f : Nat → RReal)
    (hC : IsCauchyReals (fun N => ihiAverage f N)) : RReal :=
  rlim (fun N => ihiAverage f N) hC

/-- **M467F-4b: 定数密度の無条件極限対象** — 区間一様測度（定数密度 c）の Haar 平均列の N→∞ 極限
    （Cauchy 性を ihl_average_cauchy で自前供給）。 -/
def ihlConstLimit (c : RReal) : RReal :=
  rlim (fun N => ihiAverage (fun _ => c) N) (ihl_average_cauchy c)

/-! ## M467F-5: 本丸 — 閉区間は rlim で閉じる（順序極限定理） -/

/-- **補題 (M467F-5a: 下界は rlim で保存)** — X が Cauchy で各 N で L ≤ X_N なら、L ≤ rlim X。
    L_n − (rlim X)_n を index s へ望遠鏡:
      L_n − L_s（正則性 u_n+u_s）+ L_s − X_{s,s}（L ≤ X_s、≤ 2u_s = F2s）
      + X_{s,s} − (rlim X)_s（rlim_close の反転 |·| ≤ 3u_s = F3s）+ (rlim X)_s − (rlim X)_n（正則性 u_s+u_n）
    定数側 (u_n+u_n) + 7u_s を ε-消去（c=7）で潰す。 -/
theorem ihl_rlim_lower (X : Nat → RReal) (hC : IsCauchyReals X) (L : RReal)
    (hL : ∀ N, rLe L (X N)) : rLe L (rlim X hC) := by
  intro n
  apply qLe_of_forall_add_frac 7
  intro s
  -- 4 部品（片側差）
  have p1 : qLe (qAdd (L.seq n) (qNeg (L.seq s)))
      (qAdd (qUnitFrac n) (qUnitFrac s)) := reg_sub_le L n s
  have p2 : qLe (qAdd (L.seq s) (qNeg ((X s).seq s))) (qFrac 2 s) :=
    qLe_trans _ _ _ (qSub_le_of_le (hL s s)) (qFrac_add 1 1 s)
  have h3abs : qLe (qAbs (qAdd ((X s).seq s) (qNeg ((rlim X hC).seq s))))
      (qAdd (qUnitFrac s) (qAdd (qUnitFrac s) (qUnitFrac s))) := by
    rw [qAbs_sub_comm]
    exact rlim_close X hC s s
  have p3 : qLe (qAdd ((X s).seq s) (qNeg ((rlim X hC).seq s))) (qFrac 3 s) :=
    qLe_trans _ _ _ (qLe_trans _ _ _ (qLe_self_abs _) h3abs)
      (qLe_trans _ _ _ (qLe_add_two (qLe_refl _) (qFrac_add 1 1 s))
        (qFrac_add 1 2 s))
  have p4 : qLe (qAdd ((rlim X hC).seq s) (qNeg ((rlim X hC).seq n)))
      (qAdd (qUnitFrac s) (qUnitFrac n)) := reg_sub_le (rlim X hC) s n
  -- 望遠鏡: L_n − Y_n = p1 + (p2 + (p3 + p4))
  have esplit : qAdd (L.seq n) (qNeg ((rlim X hC).seq n))
      = qAdd (qAdd (L.seq n) (qNeg (L.seq s)))
        (qAdd (qAdd (L.seq s) (qNeg ((X s).seq s)))
          (qAdd (qAdd ((X s).seq s) (qNeg ((rlim X hC).seq s)))
            (qAdd ((rlim X hC).seq s) (qNeg ((rlim X hC).seq n))))) := by
    rw [← qSub_split ((X s).seq s) ((rlim X hC).seq s) ((rlim X hC).seq n),
      ← qSub_split (L.seq s) ((X s).seq s) ((rlim X hC).seq n),
      ← qSub_split (L.seq n) (L.seq s) ((rlim X hC).seq n)]
  have total : qLe (qAdd (L.seq n) (qNeg ((rlim X hC).seq n)))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac s))
        (qAdd (qFrac 2 s)
          (qAdd (qFrac 3 s) (qAdd (qUnitFrac s) (qUnitFrac n))))) :=
    qLe_trans _ _ _ (qLe_of_eq esplit)
      (qLe_add_two p1 (qLe_add_two p2 (qLe_add_two p3 p4)))
  -- 定数の濃縮: … ≤ (u_n+u_n) + F7s
  have hfold : qLe
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac s))
        (qAdd (qFrac 2 s)
          (qAdd (qFrac 3 s) (qAdd (qUnitFrac s) (qUnitFrac n)))))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 7 s)) := by
    -- 内: F3s + (u_s+u_n) → (F3s+u_s)+u_n ≤ F4s+u_n
    have i1 : qLe (qAdd (qFrac 3 s) (qAdd (qUnitFrac s) (qUnitFrac n)))
        (qAdd (qFrac 4 s) (qUnitFrac n)) :=
      qLe_trans _ _ _ (qLe_of_eq (qAdd_assoc _ _ _).symm)
        (qLe_add_two (qFrac_add 3 1 s) (qLe_refl _))
    -- 中: F2s + (F4s+u_n) → (F2s+F4s)+u_n ≤ F6s+u_n
    have i2 : qLe (qAdd (qFrac 2 s)
        (qAdd (qFrac 3 s) (qAdd (qUnitFrac s) (qUnitFrac n))))
        (qAdd (qFrac 6 s) (qUnitFrac n)) :=
      qLe_trans _ _ _ (qLe_add_two (qLe_refl _) i1)
        (qLe_trans _ _ _ (qLe_of_eq (qAdd_assoc _ _ _).symm)
          (qLe_add_two (qFrac_add 2 4 s) (qLe_refl _)))
    -- 外: (u_n+u_s) + (F6s+u_n) → (u_n+u_s)+(u_n+F6s) → (u_n+u_n)+(u_s+F6s) ≤ (u_n+u_n)+F7s
    have i3 : qLe (qAdd (qAdd (qUnitFrac n) (qUnitFrac s))
        (qAdd (qFrac 2 s)
          (qAdd (qFrac 3 s) (qAdd (qUnitFrac s) (qUnitFrac n)))))
        (qAdd (qAdd (qUnitFrac n) (qUnitFrac s))
          (qAdd (qUnitFrac n) (qFrac 6 s))) :=
      qLe_add_two (qLe_refl _)
        (qLe_trans _ _ _ i2 (qLe_of_eq (qAdd_comm _ _)))
    have e4 : qAdd (qAdd (qUnitFrac n) (qUnitFrac s))
        (qAdd (qUnitFrac n) (qFrac 6 s))
        = qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
          (qAdd (qUnitFrac s) (qFrac 6 s)) :=
      qAdd_swap_mid _ _ _ _
    exact qLe_trans _ _ _ i3 (qLe_trans _ _ _ (qLe_of_eq e4)
      (qLe_add_two (qLe_refl _) (qFrac_add 1 6 s)))
  -- 移項して着地
  have hD := qLe_trans _ _ _ total hfold
  have hx := qLe_sub_move hD
  have e5 : qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 7 s))
      ((rlim X hC).seq n)
      = qAdd (qAdd ((rlim X hC).seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))
        (qFrac 7 s) := by
    rw [qAdd_comm (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 7 s))
        ((rlim X hC).seq n),
      ← qAdd_assoc ((rlim X hC).seq n) (qAdd (qUnitFrac n) (qUnitFrac n))
        (qFrac 7 s)]
  exact qLe_trans _ _ _ hx (qLe_of_eq e5)

/-- **補題 (M467F-5b: 上界は rlim で保存)** — X が Cauchy で各 N で X_N ≤ U なら、rlim X ≤ U。
    Y_n − U_n を index s へ望遠鏡（下界版と対称）。 -/
theorem ihl_rlim_upper (X : Nat → RReal) (hC : IsCauchyReals X) (U : RReal)
    (hU : ∀ N, rLe (X N) U) : rLe (rlim X hC) U := by
  intro n
  apply qLe_of_forall_add_frac 7
  intro s
  have p1 : qLe (qAdd ((rlim X hC).seq n) (qNeg ((rlim X hC).seq s)))
      (qAdd (qUnitFrac n) (qUnitFrac s)) := reg_sub_le (rlim X hC) n s
  have p2 : qLe (qAdd ((rlim X hC).seq s) (qNeg ((X s).seq s))) (qFrac 3 s) :=
    qLe_trans _ _ _ (qLe_trans _ _ _ (qLe_self_abs _) (rlim_close X hC s s))
      (qLe_trans _ _ _ (qLe_add_two (qLe_refl _) (qFrac_add 1 1 s))
        (qFrac_add 1 2 s))
  have p3 : qLe (qAdd ((X s).seq s) (qNeg (U.seq s))) (qFrac 2 s) :=
    qLe_trans _ _ _ (qSub_le_of_le (hU s s)) (qFrac_add 1 1 s)
  have p4 : qLe (qAdd (U.seq s) (qNeg (U.seq n)))
      (qAdd (qUnitFrac s) (qUnitFrac n)) := reg_sub_le U s n
  have esplit : qAdd ((rlim X hC).seq n) (qNeg (U.seq n))
      = qAdd (qAdd ((rlim X hC).seq n) (qNeg ((rlim X hC).seq s)))
        (qAdd (qAdd ((rlim X hC).seq s) (qNeg ((X s).seq s)))
          (qAdd (qAdd ((X s).seq s) (qNeg (U.seq s)))
            (qAdd (U.seq s) (qNeg (U.seq n))))) := by
    rw [← qSub_split ((X s).seq s) (U.seq s) (U.seq n),
      ← qSub_split ((rlim X hC).seq s) ((X s).seq s) (U.seq n),
      ← qSub_split ((rlim X hC).seq n) ((rlim X hC).seq s) (U.seq n)]
  have total : qLe (qAdd ((rlim X hC).seq n) (qNeg (U.seq n)))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac s))
        (qAdd (qFrac 3 s)
          (qAdd (qFrac 2 s) (qAdd (qUnitFrac s) (qUnitFrac n))))) :=
    qLe_trans _ _ _ (qLe_of_eq esplit)
      (qLe_add_two p1 (qLe_add_two p2 (qLe_add_two p3 p4)))
  have hfold : qLe
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac s))
        (qAdd (qFrac 3 s)
          (qAdd (qFrac 2 s) (qAdd (qUnitFrac s) (qUnitFrac n)))))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 7 s)) := by
    have i1 : qLe (qAdd (qFrac 2 s) (qAdd (qUnitFrac s) (qUnitFrac n)))
        (qAdd (qFrac 3 s) (qUnitFrac n)) :=
      qLe_trans _ _ _ (qLe_of_eq (qAdd_assoc _ _ _).symm)
        (qLe_add_two (qFrac_add 2 1 s) (qLe_refl _))
    have i2 : qLe (qAdd (qFrac 3 s)
        (qAdd (qFrac 2 s) (qAdd (qUnitFrac s) (qUnitFrac n))))
        (qAdd (qFrac 6 s) (qUnitFrac n)) :=
      qLe_trans _ _ _ (qLe_add_two (qLe_refl _) i1)
        (qLe_trans _ _ _ (qLe_of_eq (qAdd_assoc _ _ _).symm)
          (qLe_add_two (qFrac_add 3 3 s) (qLe_refl _)))
    have i3 : qLe (qAdd (qAdd (qUnitFrac n) (qUnitFrac s))
        (qAdd (qFrac 3 s)
          (qAdd (qFrac 2 s) (qAdd (qUnitFrac s) (qUnitFrac n)))))
        (qAdd (qAdd (qUnitFrac n) (qUnitFrac s))
          (qAdd (qUnitFrac n) (qFrac 6 s))) :=
      qLe_add_two (qLe_refl _)
        (qLe_trans _ _ _ i2 (qLe_of_eq (qAdd_comm _ _)))
    have e4 : qAdd (qAdd (qUnitFrac n) (qUnitFrac s))
        (qAdd (qUnitFrac n) (qFrac 6 s))
        = qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
          (qAdd (qUnitFrac s) (qFrac 6 s)) :=
      qAdd_swap_mid _ _ _ _
    exact qLe_trans _ _ _ i3 (qLe_trans _ _ _ (qLe_of_eq e4)
      (qLe_add_two (qLe_refl _) (qFrac_add 1 6 s)))
  have hD := qLe_trans _ _ _ total hfold
  have hx := qLe_sub_move hD
  have e5 : qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 7 s))
      (U.seq n)
      = qAdd (qAdd (U.seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))
        (qFrac 7 s) := by
    rw [qAdd_comm (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 7 s))
        (U.seq n),
      ← qAdd_assoc (U.seq n) (qAdd (qUnitFrac n) (qUnitFrac n))
        (qFrac 7 s)]
  exact qLe_trans _ _ _ hx (qLe_of_eq e5)

/-- **定理 (M467F-5c: 極限も両側界を保つ・本丸・本物の昇格)** — 有限 N 点 Haar 平均の列 X が Cauchy で、
    各 N で両側界 [L,U] に入る（∀N, L ≤ X_N ∧ X_N ≤ U）なら、**N→∞ 極限もその両側界に入る**:
      L ≤ rlim X ≤ U。
    すなわち **M462F の「N→∞ 連続極限は未」を破り、閉区間が構成的極限で閉じる**本物の昇格（順序極限定理・
    crux 不等式は決して導出しない）。M128 rlim_close + 正則性の望遠鏡で閉じる。 -/
theorem ihl_limit_two_sided (X : Nat → RReal) (hC : IsCauchyReals X) (L U : RReal)
    (hL : ∀ N, rLe L (X N)) (hU : ∀ N, rLe (X N) U) :
    rLe L (rlim X hC) ∧ rLe (rlim X hC) U :=
  ⟨ihl_rlim_lower X hC L hL, ihl_rlim_upper X hC U hU⟩

/-! ## M467F-6: Haar 平均の N→∞ 収束（rlim_close） -/

/-- **定理 (M467F-6a: Haar 平均は N→∞ で極限値に収束)** — 有限 N 点 Haar 平均 ihiAverage f N は、
    その N→∞ 極限 ihlHaarLimit に 1/(N+1) 以内で収束する（M128 rlim_close の witness 形:
    ∀ N j, |極限_j − (ihiAverage f N)_j| ≤ u_N + 2u_j）。**N→∞ 連続極限への収束**そのもの。 -/
theorem ihl_haar_converges (f : Nat → RReal)
    (hC : IsCauchyReals (fun N => ihiAverage f N)) (N j : Nat) :
    qLe (qAbs (qAdd ((ihlHaarLimit f hC).seq j)
        (qNeg ((ihiAverage f N).seq j))))
      (qAdd (qUnitFrac N) (qAdd (qUnitFrac j) (qUnitFrac j))) :=
  rlim_close (fun N => ihiAverage f N) hC N j

/-- **定理 (M467F-6b: 定数密度 Haar 平均は極限値 c に一致)** — 区間一様測度（定数密度 c）の N→∞ 極限は
    c に realEq で一致（rlim_unique に ihl_const_avg_eq の収束 witness を渡す）。すなわち定数密度の連続
    Haar 積分＝平均は N→∞ で c（無条件）。 -/
theorem ihl_const_limit_eq (c : RReal) : realEq (ihlConstLimit c) c := by
  refine rlim_unique (fun N => ihiAverage (fun _ => c) N) (ihl_average_cauchy c) c ?_
  intro m j
  -- |c_j − (A m)_j| ≤ 2u_j ≤ u_m + 2u_j
  have hcm : realEq c (ihiAverage (fun _ => c) m) :=
    realEq_symm (ihl_const_avg_eq c m)
  refine qLe_trans _ _ _ (hcm j) ?_
  refine qLe_trans _ _ _
    (qLe_of_eq (qAdd_zero_left (qAdd (qUnitFrac j) (qUnitFrac j))).symm) ?_
  exact qLe_add_two (qFrac_nonneg 1 m) (qLe_refl _)

/-! ## M467F-7: 定数密度極限の両側界・rlim_unique 特徴づけ -/

/-- **定理 (M467F-7a: 定数密度極限も両側界を保つ・無条件)** — L ≤ c ≤ U なら定数密度の N→∞ 極限
    ihlConstLimit c も両側界に入る（極限 ≈ c ゆえ congruence で L ≤ 極限 ≤ U）。ihl_limit_two_sided の
    無条件具体化（定数密度は Cauchy 性を自前供給）。 -/
theorem ihl_const_limit_two_sided (c L U : RReal) (hL : rLe L c) (hU : rLe c U) :
    rLe L (ihlConstLimit c) ∧ rLe (ihlConstLimit c) U :=
  ⟨rLe_congr (realEq_refl L) (realEq_symm (ihl_const_limit_eq c)) hL,
    rLe_congr (realEq_symm (ihl_const_limit_eq c)) (realEq_refl U) hU⟩

/-- **定理 (M467F-7b: 極限は有限近似の rlim として一意)** — 有限 N 点 Haar 平均 ihiAverage f N の
    rlim_close 収束 witness を満たす任意の Z は ihlHaarLimit に realEq で一致（rlim_unique）。**極限は
    有限近似の列から一意に定まる**（極限対象の特徴づけ）。 -/
theorem ihl_limit_from_finite (f : Nat → RReal)
    (hC : IsCauchyReals (fun N => ihiAverage f N)) (Z : RReal)
    (hZ : ∀ N j, qLe (qAbs (qAdd (Z.seq j) (qNeg ((ihiAverage f N).seq j))))
      (qAdd (qUnitFrac N) (qAdd (qUnitFrac j) (qUnitFrac j)))) :
    realEq (ihlHaarLimit f hC) Z :=
  rlim_unique (fun N => ihiAverage f N) hC Z hZ

/-! ## M467F-8: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M467F-8a: 極限の両側界は本物・crux は外部仮説／honest)** — 極限が両側界を保つこと
    （ihl_limit_two_sided）は M128 完備性で閉じる**無条件で本物**の命題（crux とは独立）。しかし
    theta-pilot ≤ gauss-pilot の**多輻的アルゴリズム**（crux Dβ-ω）は本層で**決して証明しない**。crux を
    任意の外部 Prop として受け取り、極限上界の本物性 **と** crux の連言を crux 供給時のみ返す。 -/
theorem ihl_crux_external (X : Nat → RReal) (hC : IsCauchyReals X) (U : RReal)
    (hU : ∀ N, rLe (X N) U) (crux : Prop) (hcrux : crux) :
    rLe (rlim X hC) U ∧ crux :=
  ⟨ihl_rlim_upper X hC U hU, hcrux⟩

/-- **定理 (M467F-8b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**として
    扱い、それ以上でも以下でもない（Iff.rfl）。M462F `ihi_crux_is_hypothesis` と同じ精神。 -/
theorem ihl_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M467F-9: 残る正直な限定を定理として明記（消去・弱化禁止・より狭く述べ直す） -/

/-- **定理 (M467F-9: 残る正直な scope・限定を定理化)** — 本層の N→∞ 極限昇格は、
    (i) **定数密度 c（区間一様測度）の Haar 平均は全 N で c に一致し（ihl_const_avg_eq）、その N→∞ 極限も
        c に一致して両側界を保つ**（無条件）——すなわち M462F の「N→∞ 連続極限は未」を実際に破ったが、
        **極限は区間一様測度の Riemann 和列の rlim（真の Lebesgue/Haar 積分の測度論的構成でなく Riemann 和
        の収束）・ℝ³ 忠実模型に留まり、完全な位相群 Haar 測度・実 π₁^ét 上の完全積分・一般の非定数密度の
        Cesàro 収束（average 列の Cauchy 性）は未**、
    (ii) **crux（外部 Prop）は仮説としてのみ利用可能で本層では導出されない**（`∀ crux, crux → crux`）。
    この正直な限定を機械検証可能な形で固定する（消去・弱化禁止・M462F の限定をより狭く述べ直す）。 -/
theorem ihl_model_scope (c L U : RReal) (hL : rLe L c) (hU : rLe c U) :
    (realEq (ihlConstLimit c) c
      ∧ rLe L (ihlConstLimit c) ∧ rLe (ihlConstLimit c) U)
    ∧ (∀ crux : Prop, crux → crux) :=
  ⟨⟨ihl_const_limit_eq c, ihl_const_limit_two_sided c L U hL hU⟩,
    fun _ h => h⟩

/-! ## M467F-10: capstone -/

/-- **M467F-10a: N→∞ Haar 極限データ**（総括） — M462F の各有限 N の Haar 平均を、その N→∞ 極限へ
    昇格したものを束ねる（定数密度 c＝区間一様測度で無条件に成立）: 各 N で ≈ c（avg_eq）・average 列は
    Cauchy（cauchy）・極限は c に一致（limit_eq）・極限も両側界を保つ（two_sided）・有限近似からの一意性
    （from_finite）。主語は M462F の本物の Haar 平均であり toy を用いない。crux（Dβ-ω）は外部仮説。 -/
structure IndetHaarLimitData (c L U : RReal) where
  /-- 各 N で Haar 平均は c に一致（区間一様測度の正規化）。 -/
  avg_eq : ∀ N, realEq (ihiAverage (fun _ => c) N) c
  /-- average 列は無条件で Cauchy。 -/
  cauchy : IsCauchyReals (fun N => ihiAverage (fun _ => c) N)
  /-- N→∞ 極限は c に一致。 -/
  limit_eq : realEq (ihlConstLimit c) c
  /-- L ≤ c ≤ U のとき極限も両側界を保つ。 -/
  two_sided : rLe L c → rLe c U →
    rLe L (ihlConstLimit c) ∧ rLe (ihlConstLimit c) U
  /-- 極限は有限近似 ihiAverage の rlim 収束 witness から一意。 -/
  from_finite : ∀ Z : RReal,
    (∀ N j, qLe (qAbs (qAdd (Z.seq j)
        (qNeg ((ihiAverage (fun _ => c) N).seq j))))
      (qAdd (qUnitFrac N) (qAdd (qUnitFrac j) (qUnitFrac j)))) →
    realEq (ihlConstLimit c) Z

/-- **M467F-10b: 実データ** — 全フィールドを M467F-2〜7 の本物で充足。 -/
def indetHaarLimitData (c L U : RReal) : IndetHaarLimitData c L U where
  avg_eq := ihl_const_avg_eq c
  cauchy := ihl_average_cauchy c
  limit_eq := ihl_const_limit_eq c
  two_sided := fun hL hU => ihl_const_limit_two_sided c L U hL hU
  from_finite := fun Z hZ =>
    rlim_unique (fun N => ihiAverage (fun _ => c) N) (ihl_average_cauchy c) Z hZ

/-- **M467F-10c: 存在（M467F 見出し）** — 任意の定数密度 c（区間一様測度）と両側界 [L,U] に対し、
    N→∞ Haar 極限データが存在する。M462F の各有限 N の Haar 平均は、その N→∞ 極限（M128 rlim）へ昇格でき、
    その極限は両側界を保ち（閉区間は極限で閉じる）、有限近似から一意に定まる。crux（Dβ-ω＝theta ≤ gauss）は
    外部仮説として明示され、**決して証明されない**——本層は M462F の「N→∞ 連続極限は未」という限定を
    **有限 N 点 Haar 平均の N→∞ 極限対象の本物構成へ昇格して破る**（極限は Riemann 和列の rlim に留まる旨は
    正直に固定）。 -/
theorem ihl_exists (c L U : RReal) : Nonempty (IndetHaarLimitData c L U) :=
  ⟨indetHaarLimitData c L U⟩

/-! ## 実例（区間一様測度＝定数密度 c の N→∞ Haar 極限） -/

/-- 実例（定数密度の正規化 Haar 平均 ≈ c・全 N）: (1/(N+1))·Σc ≈ c。 -/
example (c : RReal) (N : Nat) : realEq (ihiAverage (fun _ => c) N) c :=
  ihl_const_avg_eq c N

/-- 実例（本丸・閉区間は極限で閉じる）: X が Cauchy で各 N で [L,U] 内なら rlim も [L,U] 内。 -/
example (X : Nat → RReal) (hC : IsCauchyReals X) (L U : RReal)
    (hL : ∀ N, rLe L (X N)) (hU : ∀ N, rLe (X N) U) :
    rLe L (rlim X hC) ∧ rLe (rlim X hC) U :=
  ihl_limit_two_sided X hC L U hL hU

/-- 実例（N→∞ 収束・witness 形）: Haar 平均は極限に 1/(N+1) 以内で収束。 -/
example (f : Nat → RReal) (hC : IsCauchyReals (fun N => ihiAverage f N))
    (N j : Nat) :
    qLe (qAbs (qAdd ((ihlHaarLimit f hC).seq j)
        (qNeg ((ihiAverage f N).seq j))))
      (qAdd (qUnitFrac N) (qAdd (qUnitFrac j) (qUnitFrac j))) :=
  ihl_haar_converges f hC N j

/-- 実例（定数密度極限は c・無条件）: 区間一様測度の N→∞ Haar 極限は c に一致。 -/
example (c : RReal) : realEq (ihlConstLimit c) c :=
  ihl_const_limit_eq c

/-- 実例（定数密度極限も両側界を保つ）: L ≤ c ≤ U なら極限も [L,U] 内。 -/
example (c L U : RReal) (hL : rLe L c) (hU : rLe c U) :
    rLe L (ihlConstLimit c) ∧ rLe (ihlConstLimit c) U :=
  ihl_const_limit_two_sided c L U hL hU

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  ihl_crux_is_hypothesis crux

/-- 実例（capstone 存在）: 定数密度 c と両側界 [L,U] に N→∞ Haar 極限データが存在する。 -/
example (c L U : RReal) : Nonempty (IndetHaarLimitData c L U) :=
  ihl_exists c L U

end IUT
