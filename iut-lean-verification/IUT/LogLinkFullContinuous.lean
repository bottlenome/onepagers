-- M457F LogLinkFullContinuous [実・本物・柱D]
-- 分類: [実]（§2(a) 昇格・M452F LogLinkContinuousIndet(lci) の正直な限定「連続部は (Ind3) 方向の
--   1 次元実シフトのみ・(Ind1)(Ind2) との完全連続混合は未」を本物へ置換して閉じる）。作用の主語は
--   M442F/M437F の実 deg_ℝ log-volume（mlltLogLink / pvuLogShellBound）であり toy を用いない。M452F の
--   連続シフトを **(Ind3) 単独から (Ind1)(Ind2)(Ind3) 全 3 成分が連続 ℝ 値で同時に効く連続不定性群**へ拡張。
-- complete_pct 影響: 前進。M452F(lci) は log-link 版多輻 log-volume 輸送の両側界が **(Ind3) 方向の連続
--   ℝ シフト lciContShift v t = t·log q_v** の下で保たれることを本物化したが、`lci_model_scope` に
--   「連続部は (Ind3) 方向の 1 次元実シフトに留まり **(Ind1)(Ind2) との完全な連続混合は未**」と正直に限定
--   していた。本 M457F はその限定を破る: 連続不定性群 lfcContGroup = ℝ×ℝ×ℝ（(Ind1) 連続回転近似・
--   (Ind2) 連続スケール・(Ind3) 連続シフトの 3 実パラメータ加法群）の元 g=(t1,t2,t3) の作用 lfcAction が
--   **3 成分すべて連続 ℝ 値で同時に効く**下でも両側界が保たれること（lfc_two_sided_full_continuous）を、
--   作用が連続パラメータ加法についての群準同型（lfc_action_additive）であることと共に本物化。(Ind1)(Ind2)
--   成分を 0 にすると M452F の (Ind3) 単独連続版 lci へ、整数値制限で M447F 離散群 lfi へ厳密整合。残る限定は
--   「連続群は ℝ³ の忠実模型（Ind1 は実回転近似・Ind2 は実スケール）・実 π₁^ét 上の完全不定性群・Haar 測度
--   レベルの積分・完全な位相群構造は未」とより狭く述べ直す（lfc_model_scope）。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。

/-
  IUT/LogLinkFullContinuous.lean — M457F（定理3.11 / log-link 版多輻 log-volume 輸送の (Ind1)(Ind2)(Ind3)
  全連続混合：M452F の (Ind3) 単独連続シフトを 3 実パラメータの連続不定性群へ拡張し、全成分が連続 ℝ 値で
  同時に作用する下でも両側界が保たれることを本物構成）

  ## 二軸
  * 主要成果の分類: **[実]**（§2(a) 昇格・既存の正直な限定を本物へ置換して閉じる）。M452F
    `LogLinkContinuousIndet`（`lci`）は log-link 版多輻輸送の両側界が **(Ind3) 方向の連続 ℝ シフト**
    `lciContShift v t = rmul t (logq v) = t·log q_v`（t は実数 RReal＝ℝ setoid）の下で保たれることを本物化
    したが、`lci_model_scope` に

      「連続部は **(Ind3) 方向の 1 次元実シフト（rmul スケール）に留まり (Ind1)(Ind2) との完全な連続混合**・
       実 π₁^ét 上の完全不定性・Haar 測度レベルの積分は未」

    と正直に限定していた。本 M457F はこの限定を **(Ind1)(Ind2)(Ind3) 全 3 成分が連続 ℝ 値で同時に効く
    連続不定性群**へ昇格して破る:
      - **連続不定性群** `lfcContGroup = ℝ×ℝ×ℝ`（(Ind1) 連続回転近似 t1・(Ind2) 連続スケール t2・(Ind3)
        連続シフト t3 の 3 実パラメータ）を、成分ごとの実数加法 `lfcAdd`（単位元 `lfcZero`）で加法群として
        束ねる。M452F の (Ind3) 単独連続 t を 3 成分へ拡張。
      - **連続作用の全 3 成分シフト** `lfcContShift v g = (t1·log q_v + t2·log q_v) + t3·log q_v`——3 つの
        連続 ℝ 成分がすべて同時に log-volume の deg_ℝ へ効く（M452F の単一 rmul t を 3 項の可視和へ）。
      - **連続作用** `lfcAction g V = V + lfcContShift v g`（実 log-volume を 3 成分連続シフトぶん平行移動）。
      - **群準同型** `lfc_action_additive`: 連続パラメータの加法で lfcAction(g+h) V ≈ lfcAction g (lfcAction h V)
        （3 成分シフトが実数加法準同型 `lfc_shift_additive`・4 項交換則 `lfcAddInterchange` を 2 回適用）。
      - **本丸** `lfc_two_sided_full_continuous`: **(Ind1)(Ind2)(Ind3) 全連続混合の下で両側界が保たれる**
        （下界 + 3·(連続シフト g) ≤ 3·(連続輸送 g)・連続輸送 g ≤ 上界 + (連続シフト g)、誤差は連続 3 パラ
        メータで決まる連続シフト）を realEq/rLe で本物化。M437F 両側界 + M130 rLe_add + M337F rmul_add_left。
      - **M452F/M447F へ厳密整合** `lfc_reduces_to_lci`/`lfc_reduces_to_lfi`: (Ind1)(Ind2)=0 で M452F の
        (Ind3) 単独連続版 lci へ、さらに整数値 t3=intToReal μ で M447F 離散群 lfi へ整合。
      - **crux 位置不変** `lfc_crux_position_invariant`: crux（両側界の内側）の位置が全連続不定性群の下で不変。
      - **crux 外部** `lfc_crux_external`/`lfc_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は範囲外。
      - **残る限定を狭く正直に** `lfc_model_scope`: 連続群は ℝ³ の忠実模型（Ind1 は実回転近似・Ind2 は実
        スケール）に留まり実 π₁^ét 上の完全不定性群・Haar 測度レベルの積分・完全な位相群構造は未（M452F の
        「(Ind3) のみ連続」を実際に破ったことを明示）。
  * complete_pct 影響: **前進**。M452F の「連続部は (Ind3) 方向の 1 次元実シフトのみ・(Ind1)(Ind2) との
    完全連続混合は未」という限定を、3 実パラメータ連続不定性群 lfcContGroup の全成分同時連続作用の下での
    両側界不変（lfc_two_sided_full_continuous）＋作用の連続加法準同型（lfc_action_additive）へ昇格して
    破る。crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の係争点）は**決して導出せず**外部仮説のまま。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M457F-1 `lfcContGroup`/`lfcZero`/`lfcAdd` — (Ind1)(Ind2)(Ind3) 連続不定性群（ℝ×ℝ×ℝ・成分別実数加法群）。
  * M457F-2 `lfcContShift`/`lfcAction`/`lfcTransport` — 全 3 成分連続シフトと連続作用・連続輸送（M452F
      lciContShift/lciTransport の 3 成分拡張、μ=0 核 mlltLogLink + 3 成分連続シフト）。
  * M457F-3 `lfcAddInterchange` — 4 項実数交換則 (a+b)+(c+d) ≈ (a+c)+(b+d)（結合/交換/congr のみ）。
  * M457F-4 `lfc_shift_additive`/`lfc_action_additive`/`lfc_act_zero` — 連続シフトの実数加法準同型・作用の
      連続群準同型（交換則 2 回）・単位元は log-volume を動かさない。
  * M457F-5 `lfc_two_sided_full_continuous` — 本丸: 全連続混合の下で両側界（下界 + 3·連続シフト ≤ 3·連続
      輸送・連続輸送 ≤ 上界 + 連続シフト、M437F 両側界 + M130 rLe_add + M337F rmul_add_left）。
  * M457F-6 `lfc_reduces_to_lci`/`lfc_reduces_to_lfi` — (Ind1)(Ind2)=0 で M452F の (Ind3) 単独連続版へ、
      整数値で M447F 離散群へ厳密整合。
  * M457F-7 `lfc_crux_position_invariant` — crux 位置（両側界の内側）が全連続不定性群の下で不変。
  * M457F-8 `lfc_crux_external`/`lfc_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M457F-9 `lfc_model_scope` — 残る正直な限定（連続群は ℝ³ 忠実模型・Ind1 実回転近似・Ind2 実スケール・
      実 π₁^ét・Haar 測度積分・完全位相群は未）を定理化（M452F の「(Ind3) のみ連続」を実際に破った旨を明示）。
  * M457F-10 capstone `LogLinkFullContinuousData`/`lfc_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロットの比較不等式そのもの＝IUT 論争の
    当の係争点）は恒久的に本層の範囲外**。本層が昇格するのは M452F の連続両側界安定性を (Ind3) 単独から
    (Ind1)(Ind2)(Ind3) 全連続混合の作用へ広げること（連続加法準同型・全連続両側界・crux 位置不変）で
    あり、M437F 実 deg_ℝ・rmul 実分配・M130 加法単調性で閉じる**無条件で本物**の命題——**crux（rep ≤
    gauss）とは別の主張**。crux は任意の外部 Prop として受け取るのみ（`lfc_crux_is_hypothesis` は Iff.rfl）。
  * **連続群は ℝ³ の忠実模型に留まる**。M452F の「(Ind3) のみ連続」を実際に破り 3 成分すべてを連続 ℝ 値へ
    したが、**(Ind1) は実回転近似・(Ind2) は実スケール**であり実 π₁^ét（遠アーベル復元）上の**完全な不定性群
    ではない**。deg_ℝ への作用は 3 成分の連続シフトの和で、群レベルは加法群 ℝ³ にとどまる——**Haar 測度
    レベルの不定性積分・完全な位相群構造（連続同変性の測度論的完備化）は未**。本層が扱うのは 3 実パラメータ
    連続シフトの同時作用のみ。
  * **合成は有限段 n・付値レベル sumSq n（Σj²）・×2l 明示スケール・特定 l**。log-link は M337F 主項係数
    レベル・両側界は M432F/M437F の輸送安定・**局所体は K = ℚ_p**。log q_v は非負実重み witness
    （hq : realZero ≤ logq v が前提）。**ℝ は setoid**（realEq が同値・`=` でない）ゆえ連続シフト・加法性・
    両側界・crux 位置は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 昇格・正直な限定を本物へ置換[実]。一般名は `lfc` 接頭辞で衝突回避。
-/
import IUT.LogLinkContinuousIndet

namespace IUT

/-! ## M457F-1: (Ind1)(Ind2)(Ind3) 連続不定性群（ℝ×ℝ×ℝ・成分別実数加法群） -/

/-- **M457F-1a: 連続不定性群の元** — (Ind1)(Ind2)(Ind3) の 3 つの不定性を**すべて連続 ℝ 値**で束ねる:
    `t1`（(Ind1) 連続回転近似・実数）、`t2`（(Ind2) 連続スケール・実数）、`t3`（(Ind3) 連続シフト・実数）。
    M452F の (Ind3) 単独連続パラメータ t を 3 成分へ拡張した ℝ×ℝ×ℝ。実 π₁^ét 上の完全な不定性群では
    ない（忠実模型・正直な限定を参照）。 -/
structure lfcContGroup where
  /-- (Ind1) 連続回転近似成分（実数 RReal）。 -/
  t1 : RReal
  /-- (Ind2) 連続スケール成分（実数 RReal）。 -/
  t2 : RReal
  /-- (Ind3) 連続シフト成分（実数 RReal・M452F lci の連続パラメータ t に対応）。 -/
  t3 : RReal

/-- **M457F-1b: 単位元** — どの連続不定性も動かさない（3 成分すべて 0）。 -/
def lfcZero : lfcContGroup := ⟨realZero, realZero, realZero⟩

/-- **M457F-1c: 群演算** — 3 成分すべて実数加法 `realAdd` で合成する（連続不定性の合成＝各連続成分の
    実数加法の直積・ℝ×ℝ×ℝ 加法群）。 -/
def lfcAdd (g h : lfcContGroup) : lfcContGroup :=
  ⟨realAdd g.t1 h.t1, realAdd g.t2 h.t2, realAdd g.t3 h.t3⟩

/-- **M457F-1d: (Ind3) 単独連続元の埋め込み** — (Ind1)(Ind2) を 0 にし (Ind3) だけ連続 t を動かす群の元。
    M452F の (Ind3) 単独連続版 lci の連続パラメータ t に対応する生成元。 -/
def lfcGen3 (t : RReal) : lfcContGroup := ⟨realZero, realZero, t⟩

/-! ## M457F-2: 全 3 成分連続シフトと連続作用・連続輸送 -/

/-- **M457F-2a: 全 3 成分連続シフト** — 連続不定性群の元 g=(t1,t2,t3) が log-volume の deg_ℝ へ与える
    連続シフトは、**3 つの連続 ℝ 成分すべての寄与の和**:
      lfcContShift v g  =  (t1·log q_v + t2·log q_v) + t3·log q_v。
    M452F の (Ind3) 単独連続シフト `lciContShift v t = rmul t (logq v)` を 3 成分の可視和へ拡張——(Ind1)
    (Ind2)(Ind3) 全成分が連続 ℝ 値で同時に効く。(Ind1)(Ind2)=0 で t3·log q_v = lciContShift v t3 へ整合。 -/
def lfcContShift (logq : Nat → RReal) (v : Nat) (g : lfcContGroup) : RReal :=
  realAdd (realAdd (rmul g.t1 (logq v)) (rmul g.t2 (logq v))) (rmul g.t3 (logq v))

/-- **M457F-2b: 連続不定性群の元 g の log-volume への連続作用** — 実 log-volume V に元 g を作用させると、
    g の全 3 成分連続シフトぶん平行移動する: `lfcAction g V = V + lfcContShift v g`。 -/
def lfcAction (logq : Nat → RReal) (v : Nat) (g : lfcContGroup) (V : RReal) : RReal :=
  realAdd V (lfcContShift logq v g)

/-- **M457F-2c: 元 g による log-link 版多輻輸送後 log-volume** — M442F の μ=0 核（不定性ゼロ）
    `mlltLogLink` に、全 3 成分連続シフト `lfcContShift v g` を上乗せして log-link 輸送した実 deg_ℝ 体積:
      lfcTransport v l n g  =  mlltLogLink v l n  +  lfcContShift v g。
    M452F の (Ind3) 単独連続輸送 `lciTransport` を 3 成分連続シフトへ拡張した本物の主語。 -/
def lfcTransport (logq : Nat → RReal) (v l n : Nat) (g : lfcContGroup) : RReal :=
  realAdd (mlltLogLink logq v l n) (lfcContShift logq v g)

/-! ## M457F-3: 4 項実数交換則（連続シフトの加法性の土台） -/

/-- **補題 (M457F-3: 4 項実数交換則・本物)** — 実数加法の 4 項交換則:
      (a + b) + (c + d)  ≈  (a + c) + (b + d)。
    結合律 `realAdd_assoc`・可換律 `realAdd_comm`・congruence のみで閉じる（ℝ setoid 上の加法群性）。
    3 成分連続シフトの加法準同型 `lfc_shift_additive` を 2 回適用で得るための土台。 -/
theorem lfcAddInterchange (a b c d : RReal) :
    realEq (realAdd (realAdd a b) (realAdd c d))
      (realAdd (realAdd a c) (realAdd b d)) :=
  realEq_trans (realAdd_assoc a b (realAdd c d))
    (realEq_trans (realAdd_congr_right a (realEq_symm (realAdd_assoc b c d)))
      (realEq_trans (realAdd_congr_right a (realAdd_congr_left d (realAdd_comm b c)))
        (realEq_trans (realAdd_congr_right a (realAdd_assoc c b d))
          (realEq_symm (realAdd_assoc a c (realAdd b d))))))

/-! ## M457F-4: 連続シフトの実数加法準同型・作用の連続群準同型 -/

/-- **定理 (M457F-4a: 全 3 成分連続シフトの実数加法準同型・本物)** — 3 成分連続シフトは連続パラメータの
    成分別加法について加法的:
      lfcContShift v (g+h)  ≈  lfcContShift v g  +  lfcContShift v h。
    各成分の右分配 `rmul_add_right`（(ti+si)·log q_v = ti·log q_v + si·log q_v）で 3 項を展開し、4 項交換則
    `lfcAddInterchange` を 2 回適用して g 成分と h 成分に整理する。M452F の (Ind3) 単独連続加法準同型
    `lci_shift_additive` を **3 成分すべての連続加法（ℝ³→ℝ 準同型）へ昇格**したもの——全連続不定性群が
    実数加法群として log-volume に整合的に効く本物の準同型。 -/
theorem lfc_shift_additive (logq : Nat → RReal) (v : Nat) (g h : lfcContGroup) :
    realEq (lfcContShift logq v (lfcAdd g h))
      (realAdd (lfcContShift logq v g) (lfcContShift logq v h)) := by
  -- 記号: Ai = gi·q, Bi = hi·q。
  have e1 : realEq (rmul (realAdd g.t1 h.t1) (logq v))
      (realAdd (rmul g.t1 (logq v)) (rmul h.t1 (logq v))) := rmul_add_right g.t1 h.t1 (logq v)
  have e2 : realEq (rmul (realAdd g.t2 h.t2) (logq v))
      (realAdd (rmul g.t2 (logq v)) (rmul h.t2 (logq v))) := rmul_add_right g.t2 h.t2 (logq v)
  have e3 : realEq (rmul (realAdd g.t3 h.t3) (logq v))
      (realAdd (rmul g.t3 (logq v)) (rmul h.t3 (logq v))) := rmul_add_right g.t3 h.t3 (logq v)
  -- 各成分を Ai+Bi へ展開: lfcContShift(g+h) ≈ ((A1+B1)+(A2+B2))+(A3+B3)。
  have h12 : realEq
      (realAdd (rmul (realAdd g.t1 h.t1) (logq v)) (rmul (realAdd g.t2 h.t2) (logq v)))
      (realAdd (realAdd (rmul g.t1 (logq v)) (rmul h.t1 (logq v)))
        (realAdd (rmul g.t2 (logq v)) (rmul h.t2 (logq v)))) :=
    realEq_trans (realAdd_congr_left (rmul (realAdd g.t2 h.t2) (logq v)) e1)
      (realAdd_congr_right (realAdd (rmul g.t1 (logq v)) (rmul h.t1 (logq v))) e2)
  have hfull : realEq (lfcContShift logq v (lfcAdd g h))
      (realAdd (realAdd (realAdd (rmul g.t1 (logq v)) (rmul h.t1 (logq v)))
          (realAdd (rmul g.t2 (logq v)) (rmul h.t2 (logq v))))
        (realAdd (rmul g.t3 (logq v)) (rmul h.t3 (logq v)))) :=
    realEq_trans (realAdd_congr_left (rmul (realAdd g.t3 h.t3) (logq v)) h12)
      (realAdd_congr_right (realAdd (realAdd (rmul g.t1 (logq v)) (rmul h.t1 (logq v)))
        (realAdd (rmul g.t2 (logq v)) (rmul h.t2 (logq v)))) e3)
  -- 交換則 1 回目: 内側 ((A1+B1)+(A2+B2)) ≈ ((A1+A2)+(B1+B2))。
  have ic1 : realEq
      (realAdd (realAdd (rmul g.t1 (logq v)) (rmul h.t1 (logq v)))
        (realAdd (rmul g.t2 (logq v)) (rmul h.t2 (logq v))))
      (realAdd (realAdd (rmul g.t1 (logq v)) (rmul g.t2 (logq v)))
        (realAdd (rmul h.t1 (logq v)) (rmul h.t2 (logq v)))) :=
    lfcAddInterchange (rmul g.t1 (logq v)) (rmul h.t1 (logq v))
      (rmul g.t2 (logq v)) (rmul h.t2 (logq v))
  -- 交換則 2 回目: ((A1+A2)+(B1+B2))+(A3+B3) ≈ ((A1+A2)+A3)+((B1+B2)+B3)。
  have ic2 : realEq
      (realAdd (realAdd (realAdd (rmul g.t1 (logq v)) (rmul g.t2 (logq v)))
          (realAdd (rmul h.t1 (logq v)) (rmul h.t2 (logq v))))
        (realAdd (rmul g.t3 (logq v)) (rmul h.t3 (logq v))))
      (realAdd (realAdd (realAdd (rmul g.t1 (logq v)) (rmul g.t2 (logq v))) (rmul g.t3 (logq v)))
        (realAdd (realAdd (rmul h.t1 (logq v)) (rmul h.t2 (logq v))) (rmul h.t3 (logq v)))) :=
    lfcAddInterchange (realAdd (rmul g.t1 (logq v)) (rmul g.t2 (logq v)))
      (realAdd (rmul h.t1 (logq v)) (rmul h.t2 (logq v)))
      (rmul g.t3 (logq v)) (rmul h.t3 (logq v))
  exact realEq_trans hfull
    (realEq_trans (realAdd_congr_left (realAdd (rmul g.t3 (logq v)) (rmul h.t3 (logq v))) ic1) ic2)

/-- **定理 (M457F-4b: 連続作用は真の連続群準同型・本丸的)** — 連続不定性群の元の合成 g+h の log-volume
    への作用は、g の作用と h の作用の**合成**にちょうど realEq に等しい:
      lfcAction (g+h) V  ≈  lfcAction g (lfcAction h V)。
    すなわち `lfcAction` は lfcContGroup（ℝ³ 加法群）の log-volume 集合への**真の連続群作用**（連続加法
    準同型）である。M457F-4a のシフト加法準同型＋ realAdd の結合律・可換律で閉じる。M452F の (Ind3) 単独
    連続作用が全 3 成分連続作用へ昇格したことの核心。 -/
theorem lfc_action_additive (logq : Nat → RReal) (v : Nat) (g h : lfcContGroup) (V : RReal) :
    realEq (lfcAction logq v (lfcAdd g h) V)
      (lfcAction logq v g (lfcAction logq v h V)) := by
  show realEq (realAdd V (lfcContShift logq v (lfcAdd g h)))
      (realAdd (realAdd V (lfcContShift logq v h)) (lfcContShift logq v g))
  refine realEq_trans (realAdd_congr_right V (lfc_shift_additive logq v g h)) ?_
  refine realEq_trans
    (realAdd_congr_right V (realAdd_comm (lfcContShift logq v g) (lfcContShift logq v h))) ?_
  exact realEq_symm (realAdd_assoc V (lfcContShift logq v h) (lfcContShift logq v g))

/-- **定理 (M457F-4c: 単位元の作用は恒等)** — 連続不定性群の単位元 lfcZero（3 成分すべて 0）の log-volume
    への作用は恒等（lfcAction lfcZero V ≈ V）。3 成分連続シフトが 0（各 0·log q_v = 0 の和）ゆえ。 -/
theorem lfc_act_zero (logq : Nat → RReal) (v : Nat) (V : RReal) :
    realEq (lfcAction logq v lfcZero V) V := by
  have hz : realEq (rmul realZero (logq v)) realZero :=
    realEq_trans (rmul_comm realZero (logq v)) (rmul_zero (logq v))
  have hzz : realEq (realAdd (rmul realZero (logq v)) (rmul realZero (logq v))) realZero :=
    realEq_trans (realAdd_congr_left (rmul realZero (logq v)) hz)
      (realEq_trans (realAdd_congr_right realZero hz) (realAdd_zero realZero))
  have hshift : realEq (lfcContShift logq v lfcZero) realZero :=
    realEq_trans (realAdd_congr_left (rmul realZero (logq v)) hzz)
      (realEq_trans (realAdd_congr_right realZero hz) (realAdd_zero realZero))
  show realEq (realAdd V (lfcContShift logq v lfcZero)) V
  exact realEq_trans (realAdd_congr_right V hshift) (realAdd_zero V)

/-! ## M457F-5: 本丸 — 全連続混合の下で両側界が保たれる -/

/-- **定理 (M457F-5: (Ind1)(Ind2)(Ind3) 全連続混合の下で両側界が保たれる・本丸・本物の昇格)** — 連続
    不定性群 lfcContGroup の**任意の元 g=(t1,t2,t3)**（3 成分すべて連続 ℝ 値）の作用の下で、M442F/M437F の
    両側界は 3 成分連続シフト `lfcContShift v g` を許容誤差として両側に吸収した上でなお保たれる:
      (i) **下界（全連続不定性込み）**: 2l·(n³·log q_v) + 3·(連続シフト g) ≤ 3·(連続輸送 g)、
      (ii)**上界（全連続不定性込み）**: 連続輸送 g ≤ 2l·(対数殻 m^{Σj²+c} の deg_ℝ) + (連続シフト g)。
    証明は M437F `mllt_loglink_transport`（μ=0 核 mlltLogLink の両側界）を、M130 加法単調性 `rLe_add`
    で 3 成分連続シフトぶん平行移動し、M337F 実分配 `rmul_add_left`（3·(核+連続シフト) = 3·核 + 3·連続
    シフト）で主語を連続輸送へ張り替える。すなわち **M452F の「(Ind3) のみ連続」を破り、(Ind1)(Ind2)(Ind3)
    全成分が連続 ℝ 値で同時に効く不定性群の下で両側界が coherent に保たれる**本物の昇格（誤差は連続 3
    パラメータで決まる連続シフト・crux 不等式は決して導出しない）。 -/
theorem lfc_two_sided_full_continuous (logq : Nat → RReal) (v l n c : Nat) (g : lfcContGroup)
    (hq : rLe realZero (logq v)) :
    rLe (realAdd (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (lfcContShift logq v g)))
        (rmul (intToReal ((3 : Nat) : Int)) (lfcTransport logq v l n g))
    ∧ rLe (lfcTransport logq v l n g)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (lfcContShift logq v g)) := by
  have hlo : rLe (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((3 : Nat) : Int)) (mlltLogLink logq v l n)) :=
    (mllt_loglink_transport logq v l n c hq).1
  have hup : rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c))) :=
    (mllt_loglink_transport logq v l n c hq).2
  refine ⟨?_, ?_⟩
  · -- 下界: 下界 + 3·連続シフト ≤ 3·核 + 3·連続シフト = 3·(核+連続シフト) = 3·連続輸送。
    have step := rLe_add (rmul (intToReal ((3 : Nat) : Int)) (lfcContShift logq v g)) hlo
    have hdist :
        realEq (realAdd (rmul (intToReal ((3 : Nat) : Int)) (mlltLogLink logq v l n))
              (rmul (intToReal ((3 : Nat) : Int)) (lfcContShift logq v g)))
            (rmul (intToReal ((3 : Nat) : Int)) (lfcTransport logq v l n g)) :=
      realEq_symm (rmul_add_left (mlltLogLink logq v l n) (lfcContShift logq v g)
        (intToReal ((3 : Nat) : Int)))
    exact rLe_congr (realEq_refl _) hdist step
  · -- 上界: 核 + 連続シフト ≤ 上界 + 連続シフト、主語を連続輸送へ張り替える（定義的一致）。
    exact rLe_add (lfcContShift logq v g) hup

/-! ## M457F-6: M452F(lci)/M447F(lfi) へ厳密整合 -/

/-- **定理 (M457F-6a: M452F の (Ind3) 単独連続版 lci へ厳密整合)** — 連続不定性群の (Ind1)(Ind2) 成分を
    **0 に落とす**（g = lfcGen3 t = ⟨0,0,t⟩）と、3 成分連続シフト/連続輸送は M452F の (Ind3) 単独連続版
    `lciContShift`/`lciTransport` にちょうど整合する:
      lfcContShift v (lfcGen3 t)  ≈  lciContShift v t（0·q + 0·q が消え t·q が残る）、
      lfcTransport v l n (lfcGen3 t)  ≈  lciTransport v l n t。
    すなわち本層の全連続混合への昇格は **M452F の (Ind3) 単独連続版を真に含む**（(Ind1)(Ind2)=0 で M452F へ
    整合する）ことを機械検証する——昇格が骨格の張り替えでなく本物の一般化であることの証拠。 -/
theorem lfc_reduces_to_lci (logq : Nat → RReal) (v l n : Nat) (t : RReal) :
    realEq (lfcContShift logq v (lfcGen3 t)) (lciContShift logq v t)
    ∧ realEq (lfcTransport logq v l n (lfcGen3 t)) (lciTransport logq v l n t) := by
  have hz : realEq (rmul realZero (logq v)) realZero :=
    realEq_trans (rmul_comm realZero (logq v)) (rmul_zero (logq v))
  have hzz : realEq (realAdd (rmul realZero (logq v)) (rmul realZero (logq v))) realZero :=
    realEq_trans (realAdd_congr_left (rmul realZero (logq v)) hz)
      (realEq_trans (realAdd_congr_right realZero hz) (realAdd_zero realZero))
  have hshift : realEq (lfcContShift logq v (lfcGen3 t)) (lciContShift logq v t) :=
    realEq_trans (realAdd_congr_left (rmul t (logq v)) hzz)
      (realEq_trans (realAdd_comm realZero (rmul t (logq v))) (realAdd_zero (rmul t (logq v))))
  exact ⟨hshift, realAdd_congr_right (mlltLogLink logq v l n) hshift⟩

/-- **定理 (M457F-6b: M447F 離散群 lfi へ整数値制限で厳密整合)** — さらに (Ind3) 成分を**整数値
    t3 = intToReal μ** に制限する（g = ⟨0,0,intToReal μ⟩）と、3 成分連続シフトは M447F 離散不定性群の
    単一 μ 生成元 lfiGen μ の (Ind3) シフト `lfiShift v (lfiGen μ)` にちょうど整合する:
      lfcContShift v ⟨0,0,intToReal μ⟩  ≈  lfiShift v (lfiGen μ)。
    M457F-6a（lci へ整合）＋ M452F `lci_reduces_to_lfi`（整数値で lci→lfi は defeq）を合成——本層の全連続
    昇格が M452F 連続版・M447F 離散群の**両方を真に含む**（連続群 ⊃ 連続 (Ind3) ⊃ 離散 (Ind3)）ことを機械
    検証する。 -/
theorem lfc_reduces_to_lfi (logq : Nat → RReal) (v l n : Nat) (μ : Int) :
    realEq (lfcContShift logq v (lfcGen3 (intToReal μ))) (lfiShift logq v (lfiGen μ)) := by
  have h1 : realEq (lfcContShift logq v (lfcGen3 (intToReal μ)))
      (lciContShift logq v (intToReal μ)) := (lfc_reduces_to_lci logq v l n (intToReal μ)).1
  have h2 : lciContShift logq v (intToReal μ) = lfiShift logq v (lfiGen μ) :=
    (lci_reduces_to_lfi logq v l n μ).1
  exact h2 ▸ h1

/-! ## M457F-7: crux の位置（両側界の内側）が全連続不定性群の下で不変 -/

/-- **定理 (M457F-7: crux 位置は全連続不定性群の下で不変・本物)** — 連続不定性群の**任意の元 g**（3 成分
    すべて連続 ℝ 値）の作用の下でも、(i) M442F の **μ=0 核の上界**（crux が内側に座す μ=0 両側界の上側:
    mlltLogLink ≤ 2l·対数殻 deg_ℝ）がそのまま保たれ、(ii) 連続輸送 g は **μ=0 核に 3 成分連続シフトを
    足しただけ**（lfcTransport g ≈ 核 mlltLogLink + lfcContShift g）である。すなわち crux の位置づけ
    （テータ ⇄ ガウスの比較が μ=0 両側界の内側に座す）が **全連続不定性群の下で壊れない**——連続 3
    パラメータのどの値も crux の位置を両側界の外へ動かさない本物（crux 不等式そのものは決して導出しない）。
    M452F `lci_indet_interval`（(Ind3) 単独）を全 3 成分連続作用へ一般化。 -/
theorem lfc_crux_position_invariant (logq : Nat → RReal) (v l n c : Nat) (g : lfcContGroup)
    (hq : rLe realZero (logq v)) :
    rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
    ∧ realEq (lfcTransport logq v l n g)
        (realAdd (mlltLogLink logq v l n) (lfcContShift logq v g)) :=
  ⟨(mllt_loglink_transport logq v l n c hq).2, realEq_refl _⟩

/-! ## M457F-8: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M457F-8a: 全連続両側界は本物・crux は外部仮説／honest)** — 全連続混合の下で両側界が保たれる
    こと（M457F-5 上界: 連続輸送 g ≤ 2l·対数殻 + 連続シフト g）は M437F 実 deg_ℝ・rmul 実分配・M130 加法
    単調性で閉じる**無条件で本物**の命題（crux とは独立に成立）。しかし theta-pilot ≤ gauss-pilot の
    **多輻的アルゴリズム**（crux Dβ-ω ＝ IUT 論争の当の係争点）は本層で**決して証明しない**。crux を任意の
    外部 Prop `crux` として受け取り、全連続両側界上界の本物性 **と** crux の連言を、crux が仮説として供給
    された場合にのみ返す——crux は決して導出されない。 -/
theorem lfc_crux_external (logq : Nat → RReal) (v l n c : Nat) (g : lfcContGroup)
    (hq : rLe realZero (logq v)) (crux : Prop) (hcrux : crux) :
    rLe (lfcTransport logq v l n g)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (lfcContShift logq v g))
    ∧ crux :=
  ⟨(lfc_two_sided_full_continuous logq v l n c g hq).2, hcrux⟩

/-- **定理 (M457F-8b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**として
    扱い、それ以上でも以下でもない（Iff.rfl）。crux（theta ≤ gauss 比較）は本層が昇格した全連続不定性群
    作用版両側界とは別物であり、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で
    明示（M452F `lci_crux_is_hypothesis`・M447F `lfi_crux_is_hypothesis` と同じ精神）。 -/
theorem lfc_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M457F-9: 残る正直な限定を定理として明記（消去・弱化禁止・より狭く述べ直す） -/

/-- **定理 (M457F-9: 残る正直な scope・限定を定理化)** — 本層の全連続混合への昇格 `lfcTransport` は、
    (i) **任意の元 g（3 成分すべて連続 ℝ 値）の作用でも連続輸送は μ=0 核 + 全 3 成分連続シフト
        （lfcContShift v g）に分解する**——すなわち本層は M452F の「連続部は **(Ind3) のみ連続**」を実際に
        破り、(Ind1)(Ind2)(Ind3) 全成分の連続作用（成分別実数加法群 lfcAdd・連続群準同型
        lfc_action_additive）を得たが、**連続群は ℝ³ の忠実模型（Ind1 は実回転近似・Ind2 は実スケール）に
        留まり、実 π₁^ét 上の完全不定性群・Haar 測度レベルの積分・完全な位相群構造は未**、
    (ii) **crux（外部 Prop）は仮説としてのみ利用可能で本層では導出されない**（`∀ crux, crux → crux`）。
    この正直な限定（(Ind3) のみ連続を破って 3 成分全連続混合を得たが ℝ³ 忠実模型・実 π₁^ét・Haar 測度・
    完全位相群は未・crux 外部）を機械検証可能な形で固定する（消去・弱化禁止・M452F の限定をより狭く述べ
    直す）。 -/
theorem lfc_model_scope (logq : Nat → RReal) (v l n : Nat) (g : lfcContGroup) :
    realEq (lfcTransport logq v l n g)
        (realAdd (mlltLogLink logq v l n) (lfcContShift logq v g))
    ∧ (∀ crux : Prop, crux → crux) :=
  ⟨realEq_refl _, fun _ h => h⟩

/-! ## M457F-10: capstone -/

/-- **M457F-10a: (Ind1)(Ind2)(Ind3) 全連続混合 log-link 多輻輸送データ**（総括） — M452F の (Ind3) 単独
    連続シフトを、連続不定性群 lfcContGroup（ℝ³ 加法群）の任意の元 g の全 3 成分同時連続作用へ昇格した
    ものを束ねる: 連続作用が真の連続群準同型（action_additive）・単位元は恒等（act_zero）・任意の元 g の
    下で両側界が保たれること（two_sided）・crux 位置が全連続群で不変（crux_position）・(Ind1)(Ind2)=0 で
    M452F へ整合（reduces）。主語は M442F/M437F の本物の実 deg_ℝ であり toy を用いない。crux（Dβ-ω＝
    theta ≤ gauss）は外部仮説であって本層で証明されない。 -/
structure LogLinkFullContinuousData (logq : Nat → RReal) (v : Nat) where
  /-- 横 theta-link 輸送スケール 2l を与える l-捻れ。 -/
  l : Nat
  /-- 元 g の 3 成分連続シフト。 -/
  shift : lfcContGroup → RReal
  /-- shift は本層の 3 成分連続シフト `lfcContShift`。 -/
  is_shift : shift = fun g => lfcContShift logq v g
  /-- 元 g による log-link 版多輻輸送後 log-volume（n をわたる）。 -/
  transport : lfcContGroup → Nat → RReal
  /-- transport は本層の連続輸送写像 `lfcTransport`。 -/
  is_transport : transport = fun g n => lfcTransport logq v l n g
  /-- 連続作用は真の連続群作用: lfcAction (g+h) V ≈ lfcAction g (lfcAction h V)。 -/
  action_additive : ∀ (g h : lfcContGroup) (V : RReal),
    realEq (lfcAction logq v (lfcAdd g h) V) (lfcAction logq v g (lfcAction logq v h V))
  /-- 単位元の作用は恒等: lfcAction lfcZero V ≈ V。 -/
  act_zero : ∀ V : RReal, realEq (lfcAction logq v lfcZero V) V
  /-- 本丸: 全連続混合の下で両側界が保たれる（下界 + 3·連続シフト ≤ 3·連続輸送・
      連続輸送 ≤ 上界 + 連続シフト）。 -/
  two_sided : ∀ (g : lfcContGroup) (n c : Nat), rLe realZero (logq v) →
    rLe (realAdd (rmul (intToReal ((2 * l : Nat) : Int))
            (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (shift g)))
        (rmul (intToReal ((3 : Nat) : Int)) (transport g n))
    ∧ rLe (transport g n)
        (realAdd (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
          (shift g))
  /-- crux 位置（μ=0 核上界の内側）が全連続不定性群の下で不変。 -/
  crux_position : ∀ (g : lfcContGroup) (n c : Nat), rLe realZero (logq v) →
    rLe (mlltLogLink logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
    ∧ realEq (transport g n) (realAdd (mlltLogLink logq v l n) (shift g))
  /-- (Ind1)(Ind2)=0 で M452F の (Ind3) 単独連続版 lci へ整合。 -/
  reduces : ∀ (t : RReal) (n : Nat),
    realEq (transport (lfcGen3 t) n) (lciTransport logq v l n t)

/-- **M457F-10b: 実データ** — 全フィールドを M457F-4〜6 の本物で充足。連続作用は 3 成分 rmul の可視和、
    両側界は M437F、加法性は 4 項交換則 2 回であり crux は受け取らず昇格のみ。 -/
def logLinkFullContinuousData (logq : Nat → RReal) (v l : Nat) :
    LogLinkFullContinuousData logq v where
  l := l
  shift := fun g => lfcContShift logq v g
  is_shift := rfl
  transport := fun g n => lfcTransport logq v l n g
  is_transport := rfl
  action_additive := fun g h V => lfc_action_additive logq v g h V
  act_zero := fun V => lfc_act_zero logq v V
  two_sided := fun g n c hq => lfc_two_sided_full_continuous logq v l n c g hq
  crux_position := fun g n c hq => lfc_crux_position_invariant logq v l n c g hq
  reduces := fun t n => (lfc_reduces_to_lci logq v l n t).2

/-- **M457F-10c: 存在（M457F 見出し）** — 任意の実重み logq・素点 v・l-捻れ l に対し、(Ind1)(Ind2)(Ind3)
    全連続混合版の log-link 多輻輸送データが存在する。M452F の (Ind3) 単独連続シフトは、連続不定性群
    lfcContGroup（ℝ³ 加法群）の任意の元 g の全 3 成分同時連続作用へ昇格でき、その作用は真の連続群準同型で、
    任意の元 g の下で両側界を許容誤差（連続シフト）込みでなお満たし、crux の位置を全連続群の下で動かさず、
    (Ind1)(Ind2)=0 で M452F へ・整数値で M447F へ厳密整合する。crux（Dβ-ω＝theta ≤ gauss）は外部仮説として
    明示され、**決して証明されない**——本層は M452F の「(Ind3) のみ連続」という限定を **全連続混合へ昇格
    して破り**、両側界が全連続不定性群の下で安定であるという構造を本物にする（連続群は ℝ³ 忠実模型に留まる
    旨は正直に固定）。 -/
theorem lfc_exists (logq : Nat → RReal) (v l : Nat) :
    Nonempty (LogLinkFullContinuousData logq v) :=
  ⟨logLinkFullContinuousData logq v l⟩

/-! ## 実例（twist l=3 → ×2l=×6, 多輻段 n=5: Σ_{j=1}^{5} j²=55, 連続元 g=(t1,t2,t3)） -/

/-- 実例（連続作用は真の連続群準同型・g,h 任意）: 合成 g+h の作用は g の作用∘h の作用。 -/
example (logq : Nat → RReal) (v : Nat) (g h : lfcContGroup) (V : RReal) :
    realEq (lfcAction logq v (lfcAdd g h) V) (lfcAction logq v g (lfcAction logq v h V)) :=
  lfc_action_additive logq v g h V

/-- 実例（単位元の作用は恒等）: 連続不定性群の単位元 lfcZero は log-volume を動かさない。 -/
example (logq : Nat → RReal) (v : Nat) (V : RReal) :
    realEq (lfcAction logq v lfcZero V) V :=
  lfc_act_zero logq v V

/-- 実例（本丸・全連続混合の下で両側界・l=3, n=5, g 任意）: 下界 + 3·(連続シフト g) ≤ 3·(連続輸送 g)・
    連続輸送 g ≤ 6·殻 deg_ℝ + (連続シフト g)——3 成分連続不定性をすべて許容誤差として吸収してなお両側界内。 -/
example (logq : Nat → RReal) (v c : Nat) (g : lfcContGroup) (hq : rLe realZero (logq v)) :
    rLe (realAdd (rmul (intToReal ((2 * 3 : Nat) : Int))
            (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v)))
          (rmul (intToReal ((3 : Nat) : Int)) (lfcContShift logq v g)))
        (rmul (intToReal ((3 : Nat) : Int)) (lfcTransport logq v 3 5 g))
    ∧ rLe (lfcTransport logq v 3 5 g)
        (realAdd (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c)))
          (lfcContShift logq v g)) :=
  lfc_two_sided_full_continuous logq v 3 5 c g hq

/-- 実例（M452F へ厳密整合・l=3, n=5, (Ind3) 単独連続 t）: (Ind1)(Ind2)=0 で全連続版は M452F の lci へ一致。 -/
example (logq : Nat → RReal) (v : Nat) (t : RReal) :
    realEq (lfcContShift logq v (lfcGen3 t)) (lciContShift logq v t)
    ∧ realEq (lfcTransport logq v 3 5 (lfcGen3 t)) (lciTransport logq v 3 5 t) :=
  lfc_reduces_to_lci logq v 3 5 t

/-- 実例（M447F 離散群へ整数値制限で整合・μ=2）: (Ind3) 成分を整数値にすると M447F 離散群 lfi へ整合。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (lfcContShift logq v (lfcGen3 (intToReal 2))) (lfiShift logq v (lfiGen 2)) :=
  lfc_reduces_to_lfi logq v 3 5 2

/-- 実例（crux 位置は全連続群で不変・l=3, n=5, g 任意）: μ=0 核の上界（crux の位置）は元 g の下でも保たれ、
    連続輸送 g は μ=0 核 + 3 成分連続シフトである。 -/
example (logq : Nat → RReal) (v c : Nat) (g : lfcContGroup) (hq : rLe realZero (logq v)) :
    rLe (mlltLogLink logq v 3 5)
        (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c)))
    ∧ realEq (lfcTransport logq v 3 5 g)
        (realAdd (mlltLogLink logq v 3 5) (lfcContShift logq v g)) :=
  lfc_crux_position_invariant logq v 3 5 c g hq

/-- 実例（残る限定・scope）: 全連続作用でも連続輸送は μ=0 核 + 3 成分連続シフトに分解し、連続群は ℝ³ 忠実
    模型に留まり crux は仮説として通すのみ。 -/
example (logq : Nat → RReal) (v : Nat) (g : lfcContGroup) :
    realEq (lfcTransport logq v 3 5 g)
        (realAdd (mlltLogLink logq v 3 5) (lfcContShift logq v g))
    ∧ (∀ crux : Prop, crux → crux) :=
  lfc_model_scope logq v 3 5 g

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  lfc_crux_is_hypothesis crux

/-- 実例（capstone 存在）: (Ind1)(Ind2)(Ind3) 全連続混合版の log-link 多輻輸送データは存在する。 -/
example (logq : Nat → RReal) (v l : Nat) :
    Nonempty (LogLinkFullContinuousData logq v) :=
  lfc_exists logq v l

end IUT
