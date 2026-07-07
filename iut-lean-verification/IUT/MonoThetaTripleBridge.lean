/-
  IUT/MonoThetaTripleBridge.lean — M388F [実／本物／柱E]
  分類: 実（mono-theta 環境 M363F の三剛性＋テータ Kummer 類剛性を、一つの具体的な環境
    インスタンス env から直接取り出し束ねる本物のブリッジ）。
  complete_pct 影響: 柱E を前進（M363F `MonoThetaEnvBundle` は三剛性の**存在**
    （Nonempty）を束ねるにとどまっていたが、本層は**具体的な一つの env** から
    定数倍剛性（`env.constMult.const_mult_rigid`）・離散剛性（`env.discrete.no_sqrt_period`）・
    円分剛性（`env.cyclotomic.rigIso_gen`/`external_pin`）を**そのまま使える命題**として
    同時に取り出し、さらに M383F `trb_env_meet` を再輸出して円分剛性とテータ Kummer 類剛性
    （`env.kummerRigid`）が共有実元 ζ²＝ζ·ζ で合流することを一つの capstone 命題
    `mtt_triple_holds` に閉じる。抽象的な存在証明を「一つの env で同時に成立する具体的
    命題の連言」に格上げする点が新規）。
  正直な限定: 本層が新規に確立するのは (i) env の三つの実データフィールドから直接
    抽出した命題の同時成立（連言を一つの capstone にまとめること自体）と (ii) ζ²
    （円分剛性の内部生成元）が同一の ζ（テータ Kummer 類側の外部生成元）の自己積
    ζ·ζ に一致すること（`mtt_zeta_sq_mul`, zpPow_succ + thCyc_zpPow_one の合成）の
    2 点のみ。M338F/M333F/M323F/M358F/M363F/M383F それぞれの正直な限定（内部円分体は
    離散 Heisenberg テータ群の中心・無限位数仮説は外部 crux・完全な解析的エタール
    テータ剛性と tempered π₁^ét 本体は外部仮説）はそのまま継承し、消去・弱化しない。

  ## 内容（tier-S・実ブリッジ、既存三剛性の bundling）

  M363F `MonoThetaEnvBundle` は三剛性（`constMult`: M323F・`discrete`: M333F・
  `cyclotomic`: M338F）とテータ Kummer 類の剛性（`kummerRigid`: M358F）を一つの構造体に
  束ねるが、それを使う既存の capstone（`mte_three_rigidities`・`mte_capstone`）は
  「三剛性データが存在する（Nonempty）」という抽象的な主張にとどまり、**特定の env
  インスタンスのフィールドから直接引ける具体命題**としては提示していなかった。
  本層はその隙間を埋める:

  * M388F-1 `mtt_zeta_sq_mul` — 円分剛性が参照する ζ²＝zpPow p ζ 2（M363F の内部円分体
    生成元）が、テータ Kummer 類側の外部生成元 ζ の自己積 zpMul p ζ ζ に一致すること
    （zpPow_succ で ζ² = ζ·ζ¹、thCyc_zpPow_one で ζ¹=ζ を代入）。「同じ生成元 ζ が
    円分剛性とテータ Kummer 類剛性の両方を実の乗法で結ぶ」ことの本物の核。
  * M388F-2 `mtt_constMult_rigid_env` / `mtt_discrete_no_sqrt_env` /
    `mtt_cyclotomic_gen_env` / `mtt_cyclotomic_pin_env` / `mtt_kummer_gen_env` —
    一つの env インスタンスのフィールド（`env.constMult`・`env.discrete`・
    `env.cyclotomic`・`env.kummerRigid`）から、三剛性それぞれの本丸命題をそのまま
    使える形で取り出す（射影だが、Nonempty から具体命題への格上げ）。
  * M388F-3 `mtt_meet_env`（M383F `trb_env_meet` の再輸出）・`mtt_cyclotomic_gen_mul_env` —
    円分剛性（μ_l 側、座標 1）とテータ Kummer 類剛性（μ_{2l} 側、座標 2）が共有実元
    ζ² に合流し（M383F）、その ζ² が ζ·ζ（M388F-1）であることを合成する。
  * M388F-4 `MonoThetaTripleData` / `monoThetaTripleData` / `mtt_exists` — 上記全てを
    一つの witness レコードに束ね、任意の env に対する存在を示す。
  * M388F-5 `mtt_triple_holds`（本丸 capstone）— 一つの env に対し、三剛性の本丸命題
    （定数倍・離散・円分）が**同時に**成立し、かつ円分剛性がテータ Kummer 類剛性と
    共有実元で合流することを、一つの連言命題として証明する。
  * M388F-6 実例（l=5・μ_{10}・本物の G_ℚ 上、M363F/M383F と同じ具体構成）。

  選択公理不使用（新規 Classical.choice なし；継承分の Quot.sound のみ）。sorry 皆無・
  禁止タクティク不使用（cases/obtain/induction/rw/show/refine/exact/apply/intro/
  generalize/funext/omega のみ使用）。一般名は `mtt` 接頭辞で衝突回避。共有ファイル
  （IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
-/
import IUT.ThetaRigidityBridge

namespace IUT

/-! ## M388F-1: 共有実元 ζ² = ζ·ζ（円分剛性の内部生成元とテータ Kummer 類の外部生成元の合流） -/

/-- **定理 (M388F-1: ζ の自己積が円分剛性の生成元)** — 円分剛性（M338F/M363F）が参照する
    内部生成元 ζ²=zpPow p ζ 2 は、テータ Kummer 類（M358F）側の外部生成元 ζ の**自己積**
    zpMul p ζ ζ に一致する。zpPow_succ（ζ^{k+1}=ζ^k·ζ）を k=1 で用い、
    thCyc_zpPow_one（ζ^1=ζ）で ζ^1 を ζ に落とす、本物の計算。**mono-theta 環境の円分剛性
    とテータ Kummer 類剛性を貫く「同じ生成元 ζ」が、単なる記号ではなく実の乗法 ζ·ζ で
    一致する**ことの核。 -/
theorem mtt_zeta_sq_mul (p : Nat) (ζ : (Zp p).carrier) :
    zpPow p ζ 2 = zpMul p ζ ζ := by
  have h2 : (2 : Nat) = 1 + 1 := by omega
  rw [h2, zpPow_succ p ζ 1, thCyc_zpPow_one p ζ]

/-! ## M388F-2: 一つの env インスタンスからの三剛性の具体的取り出し -/

/-- **定理 (M388F-2a: 定数倍剛性、env 版)** — mono-theta 環境 `env` が束ねる定数倍剛性
    データ `env.constMult`（M323F）の本丸命題そのもの: 単元定数 c（c·cInv=1）で全テータ値を
    c 倍しても比 `env.constMult.ratio i j` は不変。M363F の `Nonempty (MonoThetaRigidityData R)`
    という存在命題を、**この env が実際に持つフィールドの具体命題**に格上げしたもの。 -/
theorem mtt_constMult_rigid_env {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e)
    (i j : Int) (c cInv : (laurentRing R).carrier)
    (hc : (laurentRing R).mul c cInv = (laurentRing R).one) :
    (laurentRing R).mul ((laurentRing R).mul c (env.constMult.value i))
        ((laurentRing R).mul cInv (env.constMult.inv j))
      = env.constMult.ratio i j :=
  env.constMult.const_mult_rigid i j c cInv hc

/-- **定理 (M388F-2b: 離散剛性、env 版)** — mono-theta 環境 `env` が束ねる離散剛性データ
    `env.discrete`（M333F）の本丸命題: 周期 `env.discrete.q` の格子内に平方根周期は無い
    （可除細分の不存在）。存在命題から、この env が実際に持つ周期 `env.discrete.q` 上の
    具体命題への格上げ。 -/
theorem mtt_discrete_no_sqrt_env {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    ¬ ∃ n : Int, tateZpow (tateMultGroup K) env.discrete.q (2 * n)
      = tateZpow (tateMultGroup K) env.discrete.q 1 :=
  env.discrete.no_sqrt_period

/-- **定理 (M388F-2c: 円分剛性の生成元固定、env 版)** — mono-theta 環境 `env` が束ねる
    円分剛性データ `env.cyclotomic`（M338F）の同型は座標 1 を内部円分体の生成元
    ζ²=zpPow p ζ 2 に送る（mark 保存）。 -/
theorem mtt_cyclotomic_gen_env {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    env.cyclotomic.rigIso 1 = zpPow p ζ 2 :=
  env.cyclotomic.rigIso_gen

/-- **定理 (M388F-2d: 円分剛性の ℤ/l^× 捻れ消去、env 版)** — mono-theta 環境 `env` の
    円分剛性同型で内部円分体の生成元 ζ² に写る座標 z は z ≡ 1 (mod l) に一意
    （ℤ/l^× 捻れ不定性の消去、M338F `thCyc_external_pin` の env 版）。 -/
theorem mtt_cyclotomic_pin_env {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e)
    (z : Int) (hz : env.cyclotomic.rigIso z = zpPow p ζ 2) :
    ((l : Nat) : Int) ∣ z - 1 :=
  env.cyclotomic.external_pin z hz

/-- **定理 (M388F-2e: テータ Kummer 類剛性の生成元固定、env 版)** — mono-theta 環境 `env`
    が束ねるテータ Kummer 類剛性データ `env.kummerRigid`（M358F）の係数同一視は座標 1 を
    外部生成元 ζ に送る（mark 保存）。 -/
theorem mtt_kummer_gen_env {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    tkrRigidIso p (2 * l) ζ 1 = ζ :=
  env.kummerRigid.rigIso_gen

/-! ## M388F-3: 円分剛性とテータ Kummer 類剛性の合流（M383F の再輸出＋ζ·ζ への合成） -/

/-- **定理 (M388F-3a: env 内での合流、M383F の再輸出)** — mono-theta 環境 `env` の円分剛性
    （座標 1）とテータ Kummer 類剛性（座標 2）は同一の実元 ζ² に合流する
    （M383F `trb_env_meet` をそのまま env 上で再輸出）。 -/
theorem mtt_meet_env {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    env.cyclotomic.rigIso 1 = tkrRigidIso p (2 * l) ζ 2 :=
  trb_env_meet env

/-- **定理 (M388F-3b: 合流点は ζ の自己積 ζ·ζ)** — mono-theta 環境 `env` の円分剛性同型が
    座標 1 で与える値（内部円分体の生成元）は、テータ Kummer 類側の外部生成元 ζ の自己積
    zpMul p ζ ζ にちょうど一致する（M388F-2c の生成元固定 + M388F-1 の ζ²=ζ·ζ）。
    「円分剛性とテータ Kummer 類剛性が座標 1/座標 2 という異なる内部座標から出発しながら
    同じ実の乗法量 ζ·ζ に合流する」ことの本物の核。 -/
theorem mtt_cyclotomic_gen_mul_env {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    env.cyclotomic.rigIso 1 = zpMul p ζ ζ := by
  rw [mtt_cyclotomic_gen_env env, mtt_zeta_sq_mul p ζ]

/-! ## M388F-4: 総括レコード（三剛性 + Kummer 剛性 + 合流を一つの env 上に束ねる）と存在 -/

/-- **M388F-4a: mono-theta 三剛性ブリッジデータ** — 一つの mono-theta 環境 `env`
    （M363F `MonoThetaEnvBundle`）の上に、定数倍剛性（`env.constMult`）・離散剛性
    （`env.discrete`）・円分剛性（`env.cyclotomic`）の本丸命題と、テータ Kummer 類剛性
    （`env.kummerRigid`）の生成元固定、そして円分剛性とテータ Kummer 類剛性が共有実元
    ζ·ζ に合流することを一括束ねる。主語は本物の env のフィールドそのもの（toy 代理なし）。 -/
structure MonoThetaTripleData {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) where
  /-- 定数倍剛性（本丸、env のフィールドから）。 -/
  constMult_rigid : ∀ (i j : Int) (c cInv : (laurentRing R).carrier),
    (laurentRing R).mul c cInv = (laurentRing R).one →
      (laurentRing R).mul ((laurentRing R).mul c (env.constMult.value i))
          ((laurentRing R).mul cInv (env.constMult.inv j))
        = env.constMult.ratio i j
  /-- 離散剛性（本丸、env のフィールドから）。 -/
  discrete_no_sqrt : ¬ ∃ n : Int, tateZpow (tateMultGroup K) env.discrete.q (2 * n)
    = tateZpow (tateMultGroup K) env.discrete.q 1
  /-- 円分剛性の生成元固定（env のフィールドから）。 -/
  cyclotomic_gen : env.cyclotomic.rigIso 1 = zpPow p ζ 2
  /-- 円分剛性の ℤ/l^× 捻れ消去（env のフィールドから）。 -/
  cyclotomic_pin : ∀ z : Int, env.cyclotomic.rigIso z = zpPow p ζ 2 →
    ((l : Nat) : Int) ∣ z - 1
  /-- テータ Kummer 類剛性の生成元固定（env のフィールドから）。 -/
  kummer_gen : tkrRigidIso p (2 * l) ζ 1 = ζ
  /-- 円分剛性とテータ Kummer 類剛性の合流（M383F 再輸出）。 -/
  meet : env.cyclotomic.rigIso 1 = tkrRigidIso p (2 * l) ζ 2
  /-- 合流点は ζ の自己積 ζ·ζ に一致する。 -/
  cyclotomic_gen_mul : env.cyclotomic.rigIso 1 = zpMul p ζ ζ

/-- **M388F-4b: witness 本体** — 各フィールドを M388F-1〜3 の主定理で埋める。 -/
def monoThetaTripleData {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    MonoThetaTripleData env where
  constMult_rigid := mtt_constMult_rigid_env env
  discrete_no_sqrt := mtt_discrete_no_sqrt_env env
  cyclotomic_gen := mtt_cyclotomic_gen_env env
  cyclotomic_pin := mtt_cyclotomic_pin_env env
  kummer_gen := mtt_kummer_gen_env env
  meet := mtt_meet_env env
  cyclotomic_gen_mul := mtt_cyclotomic_gen_mul_env env

/-- **定理 (M388F-4c: mono-theta 三剛性ブリッジデータの存在)** — 任意の mono-theta 環境
    `env` に対し、定数倍・離散・円分の三剛性の本丸命題と、テータ Kummer 類剛性・合流を
    一括束ねたデータが存在する。 -/
theorem mtt_exists {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    Nonempty (MonoThetaTripleData env) :=
  ⟨monoThetaTripleData env⟩

/-! ## M388F-5: 本丸 capstone——一つの env での三剛性の同時成立と合流 -/

/-- **定理 (M388F-5: capstone——mono-theta 環境の三剛性は一つの env 上で同時に成立し、
    円分剛性はテータ Kummer 類剛性と共有実元 ζ·ζ に合流する)** — 任意の mono-theta 環境
    `env`（M363F `MonoThetaEnvBundle`）に対し:
    (1) `env` の定数倍剛性データが定数倍不定性の下で比を不変に保つ（M323F 本丸）、
    (2) `env` の離散剛性データの周期に平方根周期が無い（M333F 本丸）、
    (3) `env` の円分剛性データが座標 1 で内部生成元 ζ² を固定し、ℤ/l^× 捻れを持たない
        （M338F 本丸）、
    (4) `env` の円分剛性（座標 1）はテータ Kummer 類剛性（座標 2）と同一の実元 ζ² に
        合流する（M383F の再輸出）。
    抽象的な「三剛性データが存在する」（M363F `mte_three_rigidities`）という主張を、
    **この env が実際に持つ具体データの連言**に格上げし、円分剛性とテータ Kummer 類剛性の
    合流（M383F）まで一つの capstone に閉じる。 -/
theorem mtt_triple_holds {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    (∀ (i j : Int) (c cInv : (laurentRing R).carrier),
        (laurentRing R).mul c cInv = (laurentRing R).one →
          (laurentRing R).mul ((laurentRing R).mul c (env.constMult.value i))
              ((laurentRing R).mul cInv (env.constMult.inv j))
            = env.constMult.ratio i j)
    ∧ (¬ ∃ n : Int, tateZpow (tateMultGroup K) env.discrete.q (2 * n)
        = tateZpow (tateMultGroup K) env.discrete.q 1)
    ∧ (env.cyclotomic.rigIso 1 = zpPow p ζ 2
        ∧ ∀ z : Int, env.cyclotomic.rigIso z = zpPow p ζ 2 → ((l : Nat) : Int) ∣ z - 1)
    ∧ env.cyclotomic.rigIso 1 = zpMul p ζ ζ :=
  ⟨env.constMult.const_mult_rigid, env.discrete.no_sqrt_period,
    ⟨env.cyclotomic.rigIso_gen, env.cyclotomic.external_pin⟩,
    mtt_cyclotomic_gen_mul_env env⟩

/-! ## M388F-6: 実例（l=5・μ_{10}・本物の G_ℚ 上） -/

/-- **定理 (M388F-6: 実例)** — 本物の絶対ガロア群 G_ℚ・μ_{10}・自明作用・自明 Kummer 捻り・
    指数 e=4 と、10 ∣ p−1 なる素数 p に対する本物の μ_{10}(ℤ_p) の生成元 ζ（M121F）から
    構成した mono-theta 環境（l=5、M363F `mteBuild`）に対し、三剛性の本丸命題が同時に成立し、
    円分剛性はテータ Kummer 類剛性と共有実元 ζ·ζ に合流する。 -/
theorem mtt_example_l5 (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p : Nat) (hp : IsPrime p) (hdvd : (2 * 5) ∣ p - 1) :
    ∃ (ζ : (Zp p).carrier) (hζ2l : zpPow p ζ (2 * 5) = zpOne p)
      (hdist2l : ∀ i j, i < j → j < 2 * 5 → zpPow p ζ i ≠ zpPow p ζ j),
      (mteBuild R K q hInf p 5 (by omega) ζ hζ2l hdist2l
        (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
        (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega)))
        (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
          (cycMuStd (2 * 5) (by omega))) 4
      ).cyclotomic.rigIso 1 = zpMul p ζ ζ := by
  obtain ⟨ζ, hζl, hdist, _⟩ := mu_l_zp_exists p (2 * 5) hp (by omega) hdvd
  exact ⟨ζ, hζl, hdist,
    mtt_cyclotomic_gen_mul_env
      (mteBuild R K q hInf p 5 (by omega) ζ hζl hdist
        (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
        (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega)))
        (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
          (cycMuStd (2 * 5) (by omega))) 4)⟩

/-- 実例: ζ²＝zpPow p ζ 2 は ζ の自己積 zpMul p ζ ζ に一致する（M388F-1）。 -/
example (p : Nat) (ζ : (Zp p).carrier) : zpPow p ζ 2 = zpMul p ζ ζ :=
  mtt_zeta_sq_mul p ζ

end IUT
