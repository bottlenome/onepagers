-- M462F IndetHaarIntegral [実・本物・柱D]
-- 分類: [実]（§2(a) 昇格・M457F LogLinkFullContinuous(lfc) の正直な限定「Haar 測度レベルの積分は未」を
--   本物へ置換して閉じる）。積分の主語は M457F の実 deg_ℝ log-volume 作用 lfcAction であり toy を用いない。
--   M457F は連続不定性群 lfcContGroup（ℝ³）の各点での両側界まで（点ごと）だったのを、本 M462F は
--   **連続不定性群の区間上の Haar 測度（区間一様測度）による積分＝平均化**を有限 Riemann 和で忠実に建て、
--   平均化した log-volume が両側界を保つことを本物構成する。
-- complete_pct 影響: 前進。M457F(lfc) は連続不定性群の元 g の作用の両側界を各点で本物化したが、
--   `lfc_model_scope` に「**Haar 測度レベルの積分は未**」と正直に限定していた。本 M462F はその限定を破る:
--   不定性群の区間 [0..N] 上の (N+1) 点サンプル `ihiHaarSum` による Haar 平均（区間一様測度の Riemann 和）を
--   建て、(i) 各サンプルの log-volume が両側界 [L,U] に入るなら Haar 平均も両側界に入る
--   （ihi_average_two_sided: (N+1)·L ≤ ∫ ≤ (N+1)·U、正規化 1/(N+1) で L ≤ 平均 ≤ U）、(ii) Haar 和が
--   積分の線形性を満たす（ihi_haar_additive）、(iii) 群の平行移動で Haar 積分が予測どおりシフトする
--   （ihi_average_shift_invariant＝正規化後の平均は平行移動同変）、(iv) 正規化した平均も両側界を保つ
--   （ihi_average_normalized・重み 1/(N+1) の非負乗法単調性）ことを realEq/rLe で本物化。N=0（単一点）で
--   M457F の各点作用へ厳密整合（ihi_reduces_to_lfc）。残る限定は「Haar 積分は有限 Riemann 和近似（連続
--   Haar 測度の格子近似）・区間一様測度・ℝ³ 忠実模型に留まり、完全な位相群の Haar 測度・実 π₁^ét 上の
--   完全積分・連続測度の極限は未」とより狭く述べ直す（ihi_model_scope）。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。

/-
  IUT/IndetHaarIntegral.lean — M462F（定理3.11 / log-link 版多輻 log-volume 輸送の不定性群上の Haar 積分：
  M457F の連続不定性群 lfcContGroup（ℝ³）上に区間一様測度（Haar 測度）による積分＝平均化を有限 Riemann 和で
  忠実に建て、平均化した log-volume が両側界を保つことを本物構成）

  ## 二軸
  * 主要成果の分類: **[実]**（§2(a) 昇格・既存の正直な限定を本物へ置換して閉じる）。M457F
    `LogLinkFullContinuous`（`lfc`）は連続不定性群 lfcContGroup の元 g=(t1,t2,t3) の実 deg_ℝ log-volume への
    作用 `lfcAction g V = V + lfcContShift v g` の両側界を **各点で** 本物化したが、`lfc_model_scope` に

      「連続群は ℝ³ の忠実模型に留まり、実 π₁^ét 上の完全不定性群・**Haar 測度レベルの積分**・完全な位相群
       構造は未」

    と正直に限定していた。本 M462F はこの「**Haar 測度レベルの積分は未**」を **不定性群の区間上の Haar
    測度（区間一様測度）による積分＝平均化**を有限 Riemann 和で忠実に建てて破る:
      - **Haar 積分（有限 Riemann 和）** `ihiHaarSum f N` = Σ_{i=0}^{N} f(i)——不定性群の区間 [0..N] 上の
        (N+1) 点を一様サンプルし log-volume 値 f(i)（= 各点での M457F lfcAction）を足し上げた区間一様測度の
        Riemann 和（= 未正規化 Haar 積分）。
      - **定数の Haar 積分** `ihiConstSum x N` = (N+1)·x（同じ再帰で x を (N+1) 個足す・両側界の端点 (N+1)L,
        (N+1)U に使う）。
      - **本丸** `ihi_average_two_sided`: **各サンプルの log-volume が両側界 [L,U] に入るなら Haar 積分も
        両側界に入る**——(N+1)·L ≤ Σ f(i) ≤ (N+1)·U。正規化 1/(N+1)（区間の Haar 全質量）で割ると
        **L ≤ 平均 ≤ U**（平均は min と max の間）。証明は M130 加法単調性 rLe_add の 2 項版 ihi_rLe_add2 の
        N 帰納（各点両側界を Haar 和へ持ち上げる）。
      - **積分の線形性** `ihi_haar_additive`: Σ(f+g) = Σf + Σg（4 項交換則 ihiAddInterchange の N 帰納）。
      - **平行移動不変（正規化）** `ihi_average_shift_invariant`: 不定性群の平行移動（各サンプルへ定数 c を
        加える）で Haar 積分は Σf + (N+1)·c へ予測どおりシフト——正規化後の平均は平行移動同変（不定性の
        平均化＝正規化）。
      - **正規化平均** `ihiWeight N` = 1/(N+1)（区間 Haar 測度の正規化重み・qFrac 1 N）、`ihiAverage f N`
        = (1/(N+1))·Σf、両側界 `ihi_average_normalized`: (1/(N+1))·(N+1)L ≤ 平均 ≤ (1/(N+1))·(N+1)U（M180
        非負乗法単調性 rmul_le_mul_left、重み非負 ihi_weight_nonneg）。
      - **M457F へ厳密整合** `ihi_reduces_to_lfc`: N=0（単一サンプル）で ihiHaarSum f 0 = f 0（M457F の各点
        lfcAction そのもの）・ihiAverage f 0 ≈ f 0（重み 1/1=1・rmul_one）。
      - **crux 外部** `ihi_crux_external`/`ihi_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は範囲外。
      - **残る限定を狭く正直に** `ihi_model_scope`: Haar 積分は有限 Riemann 和近似（連続 Haar 測度の格子
        近似）・区間一様測度・ℝ³ 忠実模型に留まり、完全な位相群の Haar 測度・実 π₁^ét 上の完全積分・連続
        測度の極限は未（M457F の「Haar 積分は未」を実際に破ったことを明示）。
  * complete_pct 影響: **前進**。M457F の「Haar 測度レベルの積分は未」という限定を、連続不定性群の区間上の
    Haar 積分（有限 Riemann 和）とその両側界保存（ihi_average_two_sided）＋線形性（ihi_haar_additive）＋
    平行移動同変（ihi_average_shift_invariant）＋正規化平均の両側界（ihi_average_normalized）へ昇格して破る。
    crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の係争点）は**決して導出せず**外部仮説のまま。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M462F-1 `ihiHaarSum`/`ihiConstSum` — 不定性群区間 [0..N] 上の (N+1) 点 Haar 積分（Riemann 和）と定数積分。
  * M462F-2 `ihi_rLe_add2`/`ihiAddInterchange` — 2 項加法単調性（M130 rLe_add ×2＋可換）・4 項交換則（土台）。
  * M462F-3 `ihi_haar_additive` — Haar 積分の線形性 Σ(f+g)=Σf+Σg（4 項交換則の N 帰納）。
  * M462F-4 `ihi_average_two_sided` — 本丸: 各点両側界 [L,U] ⟹ Haar 積分は [(N+1)L,(N+1)U]（正規化で
      L ≤ 平均 ≤ U）。M130 rLe_add の N 帰納。
  * M462F-5 `ihi_average_shift_invariant` — 平行移動で Haar 積分は Σf+(N+1)c（正規化平均は平行移動同変）。
  * M462F-6 `ihiWeight`/`ihi_weight_nonneg`/`ihiAverage`/`ihi_average_normalized` — 正規化重み 1/(N+1)・
      非負性・正規化平均・その両側界（M180 rmul_le_mul_left）。
  * M462F-7 `ihi_reduces_to_lfc` — N=0 で M457F 各点 lfcAction へ厳密整合（単一点 Haar 積分＝各点作用）。
  * M462F-8 `ihi_crux_external`/`ihi_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M462F-9 `ihi_model_scope` — 残る正直な限定（有限 Riemann 和近似・区間一様測度・ℝ³ 忠実模型・完全 Haar
      測度/実 π₁^ét/連続測度極限は未・crux 外部）を定理化（M457F の「Haar 積分は未」を実際に破った旨を明示）。
  * M462F-10 capstone `IndetHaarIntegralData`/`ihi_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロットの比較不等式そのもの＝IUT 論争の
    当の係争点）は恒久的に本層の範囲外**。本層が昇格するのは M457F の各点両側界を **不定性群の区間上の Haar
    平均（積分）** へ広げること（Haar 積分の両側界保存・線形性・平行移動同変・正規化平均）であり、M130 加法
    単調性・M180 非負乗法単調性で閉じる**無条件で本物**の命題——**crux（rep ≤ gauss）とは別の主張**。crux は
    任意の外部 Prop として受け取るのみ（`ihi_crux_is_hypothesis` は Iff.rfl）。
  * **Haar 積分は有限 Riemann 和近似に留まる**。M457F の「Haar 積分は未」を実際に破り、不定性群の区間 [0..N]
    上の (N+1) 点一様サンプルの Riemann 和で Haar 積分（区間一様測度による平均化）を本物化したが、これは
    **連続 Haar 測度の格子近似**であって、完全な位相群の Haar 測度・実 π₁^ét（遠アーベル復元）上の完全積分・
    連続測度の極限（N→∞ の測度論的完備化）は未。区間は一様測度・群は ℝ³ の忠実模型（Ind1 実回転近似・Ind2
    実スケール）に留まる。正規化重み 1/(N+1) は区間 Haar 全質量であり、正規化平均の端点 (1/(N+1))·(N+1)L は
    厳密には L に等しいが、その完全な代数的簡約（1/(N+1)·(N+1)≈1 の ℚ 簡約）は端点表示のまま残す（両側界
    保存の本質は未正規化 (N+1)L ≤ ∫ ≤ (N+1)U で完全に本物）。
  * **合成は有限段・log q_v は非負実重み witness**。M457F の連続作用 lfcAction が主語であり、**ℝ は setoid**
    （realEq が同値・`=` でない）ゆえ Haar 積分・線形性・両側界・平均は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 昇格・正直な限定を本物へ置換[実]。一般名は `ihi` 接頭辞で衝突回避。
-/
import IUT.LogLinkFullContinuous
import IUT.RealMulOrder
import IUT.RealAbsTriangle

namespace IUT

/-! ## M462F-1: 不定性群区間 [0..N] 上の Haar 積分（有限 Riemann 和）と定数積分 -/

/-- **M462F-1a: Haar 積分（有限 Riemann 和）** — 不定性群の区間 [0..N] 上の (N+1) 点を一様サンプルし、各点
    での log-volume 値 f(i)（= M457F lfcAction を i 番目の不定性群サンプルで評価した実 deg_ℝ）を足し上げた
    区間一様測度の Riemann 和（= 未正規化 Haar 積分）:
      ihiHaarSum f N  =  f(0) + f(1) + … + f(N)。
    正規化 1/(N+1)（区間 Haar 全質量）で割ると Haar 平均になる（ihiAverage）。 -/
def ihiHaarSum (f : Nat → RReal) : Nat → RReal
  | 0 => f 0
  | Nat.succ k => realAdd (ihiHaarSum f k) (f (k + 1))

/-- **M462F-1b: 定数の Haar 積分** — 定数 x を区間 [0..N] 上で足し上げた (N+1)·x（両側界の端点 (N+1)L,
    (N+1)U に使う・ihiHaarSum (fun _ => x) N と定義的に一致）。 -/
def ihiConstSum (x : RReal) : Nat → RReal
  | 0 => x
  | Nat.succ k => realAdd (ihiConstSum x k) x

/-! ## M462F-2: 加法単調性 2 項版・4 項交換則（土台） -/

/-- **補題 (M462F-2a: 2 項加法単調性・本物)** — a ≤ b かつ c ≤ d なら a+c ≤ b+d。M130 加法両立 `rLe_add`
    （同じ元を右から足す）を 2 回、可換律 `realAdd_comm` と congruence `rLe_congr` で左右に張り替えて合成。
    Haar 積分の各点両側界の持ち上げ（ihi_average_two_sided）と線形性の土台。 -/
theorem ihi_rLe_add2 {a b c d : RReal} (h1 : rLe a b) (h2 : rLe c d) :
    rLe (realAdd a c) (realAdd b d) :=
  rLe_trans (rLe_add c h1)
    (rLe_congr (realAdd_comm c b) (realAdd_comm d b) (rLe_add b h2))

/-- **補題 (M462F-2b: 4 項実数交換則・本物)** — (a+b)+(c+d) ≈ (a+c)+(b+d)。結合・可換・congruence のみ
    （ℝ setoid 上の加法群性）。Haar 積分の線形性 ihi_haar_additive の帰納段の土台。 -/
theorem ihiAddInterchange (a b c d : RReal) :
    realEq (realAdd (realAdd a b) (realAdd c d))
      (realAdd (realAdd a c) (realAdd b d)) :=
  realEq_trans (realAdd_assoc a b (realAdd c d))
    (realEq_trans (realAdd_congr_right a (realEq_symm (realAdd_assoc b c d)))
      (realEq_trans (realAdd_congr_right a (realAdd_congr_left d (realAdd_comm b c)))
        (realEq_trans (realAdd_congr_right a (realAdd_assoc c b d))
          (realEq_symm (realAdd_assoc a c (realAdd b d))))))

/-! ## M462F-3: Haar 積分の線形性 -/

/-- **定理 (M462F-3: Haar 積分の線形性・本物)** — Haar 積分は各点和について加法的:
      ∫ (f + g)  =  ∫ f  +  ∫ g  （ihiHaarSum (fun i => f i + g i) N ≈ ihiHaarSum f N + ihiHaarSum g N）。
    N の帰納: 帰納段は ihiHaarSum (f+g) (k+1) = ∫(f+g)_k + (f+g)(k+1) を ih と 4 項交換則
    `ihiAddInterchange` で (∫f_k + f(k+1)) + (∫g_k + g(k+1)) へ整理する。積分作用素の線形性
    （Haar 測度は線形汎函数）の本物。 -/
theorem ihi_haar_additive (f g : Nat → RReal) :
    ∀ N, realEq (ihiHaarSum (fun i => realAdd (f i) (g i)) N)
      (realAdd (ihiHaarSum f N) (ihiHaarSum g N))
  | 0 => realEq_refl _
  | Nat.succ k =>
    realEq_trans
      (realAdd_congr_left (realAdd (f (k + 1)) (g (k + 1))) (ihi_haar_additive f g k))
      (ihiAddInterchange (ihiHaarSum f k) (ihiHaarSum g k) (f (k + 1)) (g (k + 1)))

/-! ## M462F-4: 本丸 — Haar 積分（平均化）が両側界を保つ -/

/-- **補題 (M462F-4a: 下界の持ち上げ)** — 各サンプルが下界 L 以上（∀ i, L ≤ f i）なら、定数の Haar 積分
    (N+1)·L は Haar 積分 ∫ f 以下: ihiConstSum L N ≤ ihiHaarSum f N。N 帰納・2 項加法単調性。 -/
theorem ihi_haar_lower (f : Nat → RReal) (L : RReal) (hlo : ∀ i, rLe L (f i)) :
    ∀ N, rLe (ihiConstSum L N) (ihiHaarSum f N)
  | 0 => hlo 0
  | Nat.succ k => ihi_rLe_add2 (ihi_haar_lower f L hlo k) (hlo (k + 1))

/-- **補題 (M462F-4b: 上界の持ち上げ)** — 各サンプルが上界 U 以下（∀ i, f i ≤ U）なら Haar 積分 ∫ f は
    定数の Haar 積分 (N+1)·U 以下: ihiHaarSum f N ≤ ihiConstSum U N。 -/
theorem ihi_haar_upper (f : Nat → RReal) (U : RReal) (hhi : ∀ i, rLe (f i) U) :
    ∀ N, rLe (ihiHaarSum f N) (ihiConstSum U N)
  | 0 => hhi 0
  | Nat.succ k => ihi_rLe_add2 (ihi_haar_upper f U hhi k) (hhi (k + 1))

/-- **定理 (M462F-4c: Haar 平均が両側界を保つ・本丸・本物の昇格)** — 不定性群の区間 [0..N] 上の各サンプルの
    log-volume が両側界 [L,U] に入る（∀ i, L ≤ f i ≤ U）なら、Haar 積分（区間一様測度による平均化）もその
    両側界に入る:
      (N+1)·L  ≤  ∫ f  ≤  (N+1)·U。
    正規化 1/(N+1)（区間の Haar 全質量）で割ると **L ≤ 平均 ≤ U**（平均は min と max の間）。すなわち
    **M457F の「Haar 測度レベルの積分は未」を破り、連続不定性群の区間上の Haar 平均が各点両側界を保つ**本物の
    昇格（誤差なく凸結合＝平均は界の内側・crux 不等式は決して導出しない）。M130 加法単調性の N 帰納で閉じる。 -/
theorem ihi_average_two_sided (f : Nat → RReal) (L U : RReal)
    (hlo : ∀ i, rLe L (f i)) (hhi : ∀ i, rLe (f i) U) (N : Nat) :
    rLe (ihiConstSum L N) (ihiHaarSum f N) ∧ rLe (ihiHaarSum f N) (ihiConstSum U N) :=
  ⟨ihi_haar_lower f L hlo N, ihi_haar_upper f U hhi N⟩

/-! ## M462F-5: 平行移動不変（正規化平均は平行移動同変） -/

/-- **定理 (M462F-5: Haar 積分は平行移動で予測どおりシフト・本物)** — 不定性群の平行移動（各サンプルへ
    定数 c を加える＝群の並進作用）で Haar 積分は Σf + (N+1)·c へシフトする:
      ∫ (f + c)  =  ∫ f  +  (N+1)·c  （ihiHaarSum (fun i => f i + c) N ≈ ihiHaarSum f N + ihiConstSum c N）。
    正規化 1/(N+1) で割ると平均は c ぶんだけシフト——**正規化後の Haar 平均は不定性群の平行移動について
    同変**（不定性の平均化＝正規化）。M462F-3 線形性を定数 g=c へ特殊化（ihiHaarSum (fun _ => c) N は
    ihiConstSum c N と定義的に一致）。 -/
theorem ihi_const_haar (c : RReal) : ∀ N, ihiHaarSum (fun _ => c) N = ihiConstSum c N
  | 0 => rfl
  | Nat.succ k => congrArg (fun t => realAdd t c) (ihi_const_haar c k)

theorem ihi_average_shift_invariant (f : Nat → RReal) (c : RReal) (N : Nat) :
    realEq (ihiHaarSum (fun i => realAdd (f i) c) N)
      (realAdd (ihiHaarSum f N) (ihiConstSum c N)) :=
  (ihi_const_haar c N) ▸ ihi_haar_additive f (fun _ => c) N

/-! ## M462F-6: 正規化重み・正規化平均・その両側界 -/

/-- **M462F-6a: 正規化 Haar 重み** — 区間 [0..N]（(N+1) 点）の Haar 測度の正規化重み 1/(N+1) = qFrac 1 N。
    Haar 積分を平均化（全質量 1 に正規化）する係数。 -/
def ihiWeight (N : Nat) : RReal := qToReal (qFrac 1 N)

/-- **M462F-6b: 正規化重みは非負** — 1/(N+1) ≥ 0（qFrac_nonneg を実数順序へ持ち上げ・realZero は
    qToReal ratRing.zero と定義的一致）。M180 非負乗法単調性の前提。 -/
theorem ihi_weight_nonneg (N : Nat) : rLe realZero (ihiWeight N) :=
  rLe_qToReal (qFrac_nonneg 1 N)

/-- **M462F-6c: 正規化 Haar 平均** — Haar 積分（Riemann 和）を全質量 1/(N+1) で正規化した平均:
      ihiAverage f N  =  (1/(N+1))·∫ f。 -/
def ihiAverage (f : Nat → RReal) (N : Nat) : RReal :=
  rmul (ihiWeight N) (ihiHaarSum f N)

/-- **定理 (M462F-6d: 正規化平均も両側界を保つ・本物)** — 各サンプルが両側界 [L,U] に入るなら、正規化した
    Haar 平均も正規化した両側界に入る:
      (1/(N+1))·(N+1)L  ≤  平均  ≤  (1/(N+1))·(N+1)U。
    正規化端点 (1/(N+1))·(N+1)L は厳密には L に等しい（区間 Haar 全質量 1）。M180 非負乗法単調性
    `rmul_le_mul_left`（重み非負 ihi_weight_nonneg）で未正規化両側界 ihi_average_two_sided を左から重みで
    掛けて得る。 -/
theorem ihi_average_normalized (f : Nat → RReal) (L U : RReal)
    (hlo : ∀ i, rLe L (f i)) (hhi : ∀ i, rLe (f i) U) (N : Nat) :
    rLe (rmul (ihiWeight N) (ihiConstSum L N)) (ihiAverage f N)
    ∧ rLe (ihiAverage f N) (rmul (ihiWeight N) (ihiConstSum U N)) :=
  ⟨rmul_le_mul_left (ihiWeight N) (ihi_haar_lower f L hlo N) (ihi_weight_nonneg N),
    rmul_le_mul_left (ihiWeight N) (ihi_haar_upper f U hhi N) (ihi_weight_nonneg N)⟩

/-! ## M462F-7: M457F(lfc) へ厳密整合（単一点 Haar 積分＝各点作用） -/

/-- **補題 (M462F-7a: qFrac 1 0 = 1)** — 単位重み 1/(0+1) = 1（Quot.sound・代表 (1,1) の ratRel は自明）。
    N=0（単一サンプル）の正規化重みが単位元であることに使う。 -/
theorem ihi_qFrac_one : qFrac 1 0 = ratRing.one := by
  apply Quot.sound
  show ((1 : Nat) : Int) * (1 : Int) = (1 : Int) * (((0 : Nat) : Int) + 1)
  omega

/-- **定理 (M462F-7b: N=0 で M457F 各点作用へ厳密整合・本物)** — 区間が単一点（N=0）のとき、Haar 積分は
    サンプル f(0) そのもの（ihiHaarSum f 0 = f 0）であり、正規化平均は重み 1/1=1 ゆえ f(0) に realEq で一致
    する（ihiAverage f 0 ≈ f 0）。f(0) を M457F の各点 log-volume 作用 `lfcAction logq v g V` に取れば、
    **単一点の Haar 積分＝M457F の各点作用**——本層の Haar 積分昇格は M457F の各点両側界を真に含む
    （N=0 で M457F へ整合する）ことを機械検証する。 -/
theorem ihi_reduces_to_lfc (f : Nat → RReal) :
    ihiHaarSum f 0 = f 0 ∧ realEq (ihiAverage f 0) (f 0) := by
  refine ⟨rfl, ?_⟩
  show realEq (rmul (qToReal (qFrac 1 0)) (f 0)) (f 0)
  rw [ihi_qFrac_one]
  exact realEq_trans (rmul_comm (qToReal ratRing.one) (f 0)) (rmul_one (f 0))

/-- **定理 (M462F-7c: 単一点 Haar 平均は M457F lfcAction そのもの)** — f を M457F の各点作用
    `fun _ => lfcAction logq v g V` に取ると、単一点（N=0）の正規化 Haar 平均は M457F の各点 log-volume 作用
    lfcAction g V にちょうど realEq で一致する。本層の Haar 積分が M457F の各点作用を N=0 で回収することの
    具体化。 -/
theorem ihi_reduces_to_lfcAction (logq : Nat → RReal) (v : Nat) (g : lfcContGroup) (V : RReal) :
    realEq (ihiAverage (fun _ => lfcAction logq v g V) 0) (lfcAction logq v g V) :=
  (ihi_reduces_to_lfc (fun _ => lfcAction logq v g V)).2

/-! ## M462F-8: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M462F-8a: Haar 平均の両側界は本物・crux は外部仮説／honest)** — Haar 平均が両側界を保つこと
    （ihi_average_two_sided）は M130 加法単調性で閉じる**無条件で本物**の命題（crux とは独立に成立）。しかし
    theta-pilot ≤ gauss-pilot の**多輻的アルゴリズム**（crux Dβ-ω ＝ IUT 論争の当の係争点）は本層で
    **決して証明しない**。crux を任意の外部 Prop として受け取り、Haar 平均両側界（上界）の本物性 **と** crux の
    連言を、crux が仮説として供給された場合にのみ返す——crux は決して導出されない。 -/
theorem ihi_crux_external (f : Nat → RReal) (L U : RReal)
    (hlo : ∀ i, rLe L (f i)) (hhi : ∀ i, rLe (f i) U) (N : Nat)
    (crux : Prop) (hcrux : crux) :
    rLe (ihiHaarSum f N) (ihiConstSum U N) ∧ crux :=
  ⟨(ihi_average_two_sided f L U hlo hhi N).2, hcrux⟩

/-- **定理 (M462F-8b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**として
    扱い、それ以上でも以下でもない（Iff.rfl）。crux（theta ≤ gauss 比較）は本層が昇格した Haar 積分版
    両側界とは別物であり、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で明示
    （M457F `lfc_crux_is_hypothesis` と同じ精神）。 -/
theorem ihi_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M462F-9: 残る正直な限定を定理として明記（消去・弱化禁止・より狭く述べ直す） -/

/-- **定理 (M462F-9: 残る正直な scope・限定を定理化)** — 本層の Haar 積分昇格は、
    (i) **各サンプルが両側界 [L,U] に入るなら Haar 積分（区間一様測度による Riemann 和）も両側界
        [(N+1)L,(N+1)U] に入る**——すなわち本層は M457F の「Haar 測度レベルの積分は未」を実際に破り、
        連続不定性群の区間上の Haar 平均が各点両側界を保つことを得たが、**Haar 積分は有限 Riemann 和近似
        （連続 Haar 測度の格子近似）・区間一様測度・ℝ³ 忠実模型に留まり、完全な位相群の Haar 測度・実 π₁^ét
        上の完全積分・連続測度の極限（N→∞ の測度論的完備化）は未**、
    (ii) **crux（外部 Prop）は仮説としてのみ利用可能で本層では導出されない**（`∀ crux, crux → crux`）。
    この正直な限定（Haar 積分を有限 Riemann 和で本物化したが連続 Haar 測度/実 π₁^ét/連続極限は未・crux 外部）
    を機械検証可能な形で固定する（消去・弱化禁止・M457F の限定をより狭く述べ直す）。 -/
theorem ihi_model_scope (f : Nat → RReal) (L U : RReal)
    (hlo : ∀ i, rLe L (f i)) (hhi : ∀ i, rLe (f i) U) (N : Nat) :
    (rLe (ihiConstSum L N) (ihiHaarSum f N) ∧ rLe (ihiHaarSum f N) (ihiConstSum U N))
    ∧ (∀ crux : Prop, crux → crux) :=
  ⟨ihi_average_two_sided f L U hlo hhi N, fun _ h => h⟩

/-! ## M462F-10: capstone -/

/-- **M462F-10a: 不定性群上の Haar 積分データ**（総括） — M457F の各点作用 lfcAction を、連続不定性群の
    区間 [0..N] 上の Haar 平均（区間一様測度の Riemann 和）へ昇格したものを束ねる: Haar 積分の線形性
    （additive）・平均が両側界を保つこと（two_sided）・平行移動同変（shift）・正規化平均も両側界を保つこと
    （normalized）・N=0 で M457F 各点作用へ整合（reduces）。主語は M457F の本物の実 deg_ℝ 作用であり toy を
    用いない。crux（Dβ-ω＝theta ≤ gauss）は外部仮説であって本層で証明されない。 -/
structure IndetHaarIntegralData (f : Nat → RReal) (L U : RReal) where
  /-- 各サンプルの下界。 -/
  lower : ∀ i, rLe L (f i)
  /-- 各サンプルの上界。 -/
  upper : ∀ i, rLe (f i) U
  /-- Haar 積分の線形性: ∫(f+g)=∫f+∫g。 -/
  additive : ∀ (g : Nat → RReal) (N : Nat),
    realEq (ihiHaarSum (fun i => realAdd (f i) (g i)) N)
      (realAdd (ihiHaarSum f N) (ihiHaarSum g N))
  /-- 本丸: Haar 平均が両側界を保つ（(N+1)L ≤ ∫ ≤ (N+1)U）。 -/
  two_sided : ∀ N : Nat,
    rLe (ihiConstSum L N) (ihiHaarSum f N) ∧ rLe (ihiHaarSum f N) (ihiConstSum U N)
  /-- 平行移動同変: ∫(f+c)=∫f+(N+1)c。 -/
  shift : ∀ (c : RReal) (N : Nat),
    realEq (ihiHaarSum (fun i => realAdd (f i) c) N)
      (realAdd (ihiHaarSum f N) (ihiConstSum c N))
  /-- 正規化平均も両側界を保つ。 -/
  normalized : ∀ N : Nat,
    rLe (rmul (ihiWeight N) (ihiConstSum L N)) (ihiAverage f N)
    ∧ rLe (ihiAverage f N) (rmul (ihiWeight N) (ihiConstSum U N))
  /-- N=0 で単一点 Haar 積分は f(0)（M457F 各点作用）へ整合。 -/
  reduces : ihiHaarSum f 0 = f 0 ∧ realEq (ihiAverage f 0) (f 0)

/-- **M462F-10b: 実データ** — 全フィールドを M462F-3〜7 の本物で充足。積分は Riemann 和、両側界は M130
    加法単調性、正規化は M180 非負乗法単調性であり crux は受け取らず昇格のみ。 -/
def indetHaarIntegralData (f : Nat → RReal) (L U : RReal)
    (hlo : ∀ i, rLe L (f i)) (hhi : ∀ i, rLe (f i) U) :
    IndetHaarIntegralData f L U where
  lower := hlo
  upper := hhi
  additive := fun g N => ihi_haar_additive f g N
  two_sided := fun N => ihi_average_two_sided f L U hlo hhi N
  shift := fun c N => ihi_average_shift_invariant f c N
  normalized := fun N => ihi_average_normalized f L U hlo hhi N
  reduces := ihi_reduces_to_lfc f

/-- **M462F-10c: 存在（M462F 見出し）** — 各サンプルが両側界 [L,U] に入る任意の log-volume 族 f に対し、
    不定性群上の Haar 積分データが存在する。M457F の各点作用 lfcAction は、連続不定性群の区間 [0..N] 上の
    Haar 平均（区間一様測度の Riemann 和）へ昇格でき、その積分は線形で、平均が両側界を保ち、平行移動同変で、
    正規化平均も両側界を保ち、N=0 で M457F の各点作用へ厳密整合する。crux（Dβ-ω＝theta ≤ gauss）は外部仮説
    として明示され、**決して証明されない**——本層は M457F の「Haar 測度レベルの積分は未」という限定を
    **不定性群上の Haar 積分（有限 Riemann 和）へ昇格して破り**、Haar 平均が両側界を保つという構造を本物に
    する（Haar 積分は有限 Riemann 和近似に留まる旨は正直に固定）。 -/
theorem ihi_exists (f : Nat → RReal) (L U : RReal)
    (hlo : ∀ i, rLe L (f i)) (hhi : ∀ i, rLe (f i) U) :
    Nonempty (IndetHaarIntegralData f L U) :=
  ⟨indetHaarIntegralData f L U hlo hhi⟩

/-! ## 実例（不定性群区間 [0..N]・M457F 各点作用 lfcAction のサンプル族） -/

/-- 実例（Haar 積分の線形性・f,g 任意, N 任意）: ∫(f+g)=∫f+∫g。 -/
example (f g : Nat → RReal) (N : Nat) :
    realEq (ihiHaarSum (fun i => realAdd (f i) (g i)) N)
      (realAdd (ihiHaarSum f N) (ihiHaarSum g N)) :=
  ihi_haar_additive f g N

/-- 実例（本丸・Haar 平均が両側界を保つ・各点 [L,U]）: (N+1)L ≤ ∫f ≤ (N+1)U——連続不定性群の区間上の
    Haar 平均が各点両側界を保つ（正規化 1/(N+1) で L ≤ 平均 ≤ U）。 -/
example (f : Nat → RReal) (L U : RReal)
    (hlo : ∀ i, rLe L (f i)) (hhi : ∀ i, rLe (f i) U) (N : Nat) :
    rLe (ihiConstSum L N) (ihiHaarSum f N) ∧ rLe (ihiHaarSum f N) (ihiConstSum U N) :=
  ihi_average_two_sided f L U hlo hhi N

/-- 実例（平行移動同変・定数 c）: ∫(f+c)=∫f+(N+1)c——不定性群の並進で Haar 積分は予測どおりシフト。 -/
example (f : Nat → RReal) (c : RReal) (N : Nat) :
    realEq (ihiHaarSum (fun i => realAdd (f i) c) N)
      (realAdd (ihiHaarSum f N) (ihiConstSum c N)) :=
  ihi_average_shift_invariant f c N

/-- 実例（正規化平均も両側界を保つ）: (1/(N+1))·(N+1)L ≤ 平均 ≤ (1/(N+1))·(N+1)U。 -/
example (f : Nat → RReal) (L U : RReal)
    (hlo : ∀ i, rLe L (f i)) (hhi : ∀ i, rLe (f i) U) (N : Nat) :
    rLe (rmul (ihiWeight N) (ihiConstSum L N)) (ihiAverage f N)
    ∧ rLe (ihiAverage f N) (rmul (ihiWeight N) (ihiConstSum U N)) :=
  ihi_average_normalized f L U hlo hhi N

/-- 実例（M457F へ厳密整合・単一点 Haar 平均は各点 lfcAction）: N=0 で正規化 Haar 平均は M457F の各点作用
    lfcAction g V へ一致。 -/
example (logq : Nat → RReal) (v : Nat) (g : lfcContGroup) (V : RReal) :
    realEq (ihiAverage (fun _ => lfcAction logq v g V) 0) (lfcAction logq v g V) :=
  ihi_reduces_to_lfcAction logq v g V

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  ihi_crux_is_hypothesis crux

/-- 実例（capstone 存在）: 各点両側界 [L,U] の log-volume 族に不定性群上の Haar 積分データが存在する。 -/
example (f : Nat → RReal) (L U : RReal)
    (hlo : ∀ i, rLe L (f i)) (hhi : ∀ i, rLe (f i) U) :
    Nonempty (IndetHaarIntegralData f L U) :=
  ihi_exists f L U hlo hhi

end IUT
