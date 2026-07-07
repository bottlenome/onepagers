/-
  IUT/ThetaRigidityBridge.lean — M383F [実／本物／柱E]
  分類: 実 (mono-theta 環境の円分剛性 と テータ Kummer 類の剛性 が同一の実元 ζ² で出会う橋)
  complete_pct 影響: 柱E を前進（M363F `MonoThetaEnvBundle` が同時に束ねる二つの本物の剛性
    同型——(i) `cyclotomic` フィールド（M338F 円分剛性、内部円分体 μ_l=⟨ζ²⟩ の同型
    `thCycRigIso p l (ζ²)`）と (ii) `kummerRigid` フィールドが使う μ_{2l} 側の円分剛性同型
    `tkrRigidIso p (2l) ζ`（M358F、テータ Kummer 類 [Θ] の係数同一視）——が、独立な内部座標
    （前者は座標 1、後者は座標 2）から出発しながら**同一の実元 ζ²** に一致することを
    本物で証明する。M363F は ζ² の位数/相異性（`mte_sq_hζl`/`mte_sq_hdist`）のみを示したが、
    本層は二つの剛性同型そのものが実元として合流することを示す点で新規）。
  正直な限定: 橋渡しは「同じ生成元 ζ から作った二つの円分剛性同型が特定座標で同じ実元 ζ² を
    与える」という代数的一致のみ。完全なエタールテータ mono-theta 環境（tempered π₁^ét 込み・
    p 進解析テータ本体）は M338F/M358F/M363F 同様に本層の範囲外（外部仮説として継承）。

  ## 内容（tier-S・本物の橋渡し）

  mono-theta 環境 `MonoThetaEnvBundle`（M363F, `mte`）は、μ_{2l} の生成元 ζ から二つの
  独立な円分剛性同型を同時に住まわせる:
  - `env.cyclotomic : ThetaCyclotomicRigidityData p l hl (zpPow p ζ 2) …`
    （M338F、内部円分体 μ_l=⟨ζ²⟩ の同型 `rigIso`、`rigIso_gen : rigIso 1 = ζ²`）。
  - `env.kummerRigid : TkrData M κ e p (2*l) … ζ hdist2l`
    （M358F、テータ Kummer 類 [Θ]∈H¹(G_K,μ_{2l}) の係数同型 `tkrRigidIso p (2l) ζ`、
    `rigIso_gen : tkrRigidIso p (2l) ζ 1 = ζ`）。

  両者は異なる法（l と 2l）・異なる生成元パラメータ（ζ² と ζ）を持つ独立の宣言だが、
  **後者を内部座標 2 で評価すると前者が座標 1 で与える値と同じ実元 ζ² に一致する**
  （`trb_rigIso_two`: `thCycRigIso p (2l) ζ 2 = zpPow p ζ 2`、`int_emod_unique` による
  2 mod 2l = 2 の計算＋`thCycRigIso` の定義展開、本物の帰納/計算証明）。これを
  `env.cyclotomic.rigIso_gen` と合成し、mono-theta 環境の内部で**円分剛性（μ_l 側）と
  テータ Kummer 類の剛性（μ_{2l} 側）が同じ実元 ζ² で出会う**ことを本物で示す
  （`trb_env_meet`）——標準包含 μ_l=⟨ζ²⟩↪μ_{2l}=⟨ζ⟩（M363F-1 の位数/相異性）が、
  剛性同型そのもののレベルでも矛盾なく実現されることの本物の橋。

  正直な限定（消去・弱化禁止）: 本層が橋渡しするのは「二つの円分剛性同型（M338F 版・
  M358F 版）が特定座標で同一の実元 ζ² を与える」という代数的一致のみ。円分剛性・
  テータ Kummer 類それぞれの正直な限定（内部円分体は離散 Heisenberg テータ群の中心・
  外部生成元 ζ は仮説として受ける・tempered π₁^ét 本体は外部仮説）はそのまま継承される。

  選択公理不使用（新規 Classical.choice なし）。sorry 不使用。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用。許可タクティク（cases/obtain/induction/rw/show/refine/exact/apply/intro/
  generalize/funext/omega）のみ使用。共有ファイル（IUT.lean・build.sh・dashboard.md・
  graph 系）は一切変更していない。一般名は `trb` 接頭辞で衝突回避。
-/
import IUT.MonoThetaEnvironment

namespace IUT

/-! ## M383F-1: 核となる計算——μ_{2l} の円分剛性同型は座標 2 で ζ² を与える -/

/-- **定理 (M383F-1a: 座標 2 の円分剛性同型は ζ²)** — 円分剛性同型 `thCycRigIso`
    （M338F、モジュラス 2l・生成元 ζ）を内部座標 z=2 で評価すると、その平方 ζ²
    （`zpPow p ζ 2`）に一致する（`int_emod_unique` で 2 mod 2l = 2（l≥2 ゆえ 2<2l）を
    確立し、`thCycRigIso` の定義 centerToMu = ζ^{z mod (2l)} を展開する）。M358F の
    `thCyc_rigIso_gen`（座標 1 ↦ ζ）を座標 2 に一般化した本物の計算補題。 -/
theorem trb_rigIso_two (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    thCycRigIso p (2 * l) ζ 2 = zpPow p ζ 2 := by
  have hb : (0 : Int) < ((2 * l : Nat) : Int) := by omega
  have h1 : (2 : Int) % ((2 * l : Nat) : Int) = 2 :=
    int_emod_unique 2 ((2 * l : Nat) : Int) 2 hb (by omega) (by omega) ⟨0, by omega⟩
  show zpPow p ζ ((2 : Int) % ((2 * l : Nat) : Int)).toNat = zpPow p ζ 2
  rw [h1]
  rfl

/-- **定理 (M383F-1b: テータ Kummer 類側での座標 2 の値)** — テータ Kummer 類の円分剛性
    同型 `tkrRigidIso`（M358F、`thCycRigIso` の係数版・定義により defeq）を座標 2 で
    評価しても同じ ζ² を与える。M358F の命名（`tkr` 接頭辞）での再確認。 -/
theorem trb_kummer_two (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    tkrRigidIso p (2 * l) ζ 2 = zpPow p ζ 2 :=
  trb_rigIso_two p l hl ζ

/-! ## M383F-2: 本丸——円分剛性（μ_l 側）とテータ Kummer 類の剛性（μ_{2l} 側）の合流 -/

/-- **定理 (M383F-2: 本丸——二つの円分剛性同型は ζ² で合流)** — μ_l の円分剛性同型
    `thCycRigIso p l (ζ²)`（M338F、生成元は ζ の平方 ζ²）を座標 1 で評価した値
    （`thCyc_rigIso_gen` により ζ² そのもの）は、μ_{2l} の円分剛性同型
    `thCycRigIso p (2l) ζ`（M358F のテータ Kummer 類が使う同型、生成元は ζ）を座標 2 で
    評価した値（M383F-1a）に一致する。**独立に法・生成元パラメータの異なる二つの円分剛性
    同型が、異なる内部座標（1 と 2）から出発して同一の実元 ζ² に合流する**ことの本物の橋。 -/
theorem trb_cyc_kummer_meet (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    thCycRigIso p l (zpPow p ζ 2) 1 = thCycRigIso p (2 * l) ζ 2 := by
  rw [thCyc_rigIso_gen p l hl (zpPow p ζ 2), trb_rigIso_two p l hl ζ]

/-! ## M383F-3: mono-theta 環境の内部での合流（capstone） -/

/-- **定理 (M383F-3: capstone——mono-theta 環境の円分剛性とテータ Kummer 類剛性の合流)** —
    任意の mono-theta 環境 `env`（M363F `MonoThetaEnvBundle`）に対し、`env` が束ねる
    円分剛性フィールド `env.cyclotomic`（M338F、内部円分体 μ_l=⟨ζ²⟩ の同型を座標 1 で評価）
    は、`env` が束ねるテータ Kummer 類の剛性が使う同型 `tkrRigidIso p (2l) ζ`（M358F、
    μ_{2l}=⟨ζ⟩ の同型を座標 2 で評価）と、同一の実元 ζ² で一致する。IUT のテータ理論の
    中心対象 mono-theta 環境の内部で、円分剛性（μ_l 側）とテータ Kummer 類の剛性（μ_{2l} 側）
    が矛盾なく同じ実元に合流することの本物の証明。 -/
theorem trb_env_meet {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    env.cyclotomic.rigIso 1 = tkrRigidIso p (2 * l) ζ 2 := by
  rw [env.cyclotomic.rigIso_gen]
  exact (trb_rigIso_two p l hl ζ).symm

/-! ## M383F-4: 橋データ（witness）と存在 -/

/-- **M383F-4a: 橋データ** — mono-theta 環境 `env` に対し、円分剛性（μ_l 側、座標 1）と
    テータ Kummer 類の剛性（μ_{2l} 側、座標 2）が同じ実元 ζ² に合流するという事実を
    witness として束ねる。 -/
structure ThetaRigidityBridgeData {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) where
  /-- 円分剛性（座標 1）とテータ Kummer 類の剛性（座標 2）が同じ実元 ζ² に一致する。 -/
  meet : env.cyclotomic.rigIso 1 = tkrRigidIso p (2 * l) ζ 2
  /-- その共通の実元は ζ² そのもの。 -/
  meet_val : env.cyclotomic.rigIso 1 = zpPow p ζ 2

/-- **M383F-4b: witness 本体** — 各フィールドを M383F-2/3 の主定理で埋める。 -/
def thetaRigidityBridgeData {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    ThetaRigidityBridgeData env where
  meet := trb_env_meet env
  meet_val := env.cyclotomic.rigIso_gen

/-- **定理 (M383F-4c: capstone——橋データの存在)** — 任意の mono-theta 環境 `env` に対し、
    円分剛性とテータ Kummer 類剛性が同じ実元 ζ² に合流する橋データが本物で組み上がる。 -/
theorem trb_exists {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    Nonempty (ThetaRigidityBridgeData env) :=
  ⟨thetaRigidityBridgeData env⟩

/-! ## M383F-5: 実例（l=5・μ_{10}・本物の G_ℚ 上） -/

/-- 実例: p 素数・10 ∣ p−1 のとき、本物の μ_{10}(ℤ_p) の生成元 ζ（M121F 供給）から
    mono-theta 環境（l=5、M363F `mteBuild`）を構成すると、円分剛性（座標 1）とテータ
    Kummer 類の剛性（座標 2）が同じ実元 ζ² に合流する（`trb_env_meet`）。 -/
theorem trb_example_l5 (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p : Nat) (hp : IsPrime p) (hdvd : (2 * 5) ∣ p - 1) :
    ∃ (ζ : (Zp p).carrier) (hζ2l : zpPow p ζ (2 * 5) = zpOne p)
      (hdist2l : ∀ i j, i < j → j < 2 * 5 → zpPow p ζ i ≠ zpPow p ζ j),
      (mteBuild R K q hInf p 5 (by omega) ζ hζ2l hdist2l
        (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
        (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega)))
        (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
          (cycMuStd (2 * 5) (by omega))) 4
      ).cyclotomic.rigIso 1 = tkrRigidIso p (2 * 5) ζ 2 := by
  obtain ⟨ζ, hζl, hdist, _⟩ := mu_l_zp_exists p (2 * 5) hp (by omega) hdvd
  exact ⟨ζ, hζl, hdist,
    trb_env_meet
      (mteBuild R K q hInf p 5 (by omega) ζ hζl hdist
        (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
        (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega)))
        (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
          (cycMuStd (2 * 5) (by omega))) 4)⟩

/-- 実例: 円分剛性同型（μ_5 側、座標 1）とテータ Kummer 類の剛性（μ_10 側、座標 2）が
    合流する共通の実元は ζ² そのもの。 -/
example (p : Nat) (ζ : (Zp p).carrier) :
    thCycRigIso p 5 (zpPow p ζ 2) 1 = zpPow p ζ 2 :=
  thCyc_rigIso_gen p 5 (by omega) (zpPow p ζ 2)

/-- 実例: 二つの円分剛性同型（法 5・法 10）の合流（`trb_cyc_kummer_meet`）。 -/
example (p : Nat) (ζ : (Zp p).carrier) :
    thCycRigIso p 5 (zpPow p ζ 2) 1 = thCycRigIso p (2 * 5) ζ 2 :=
  trb_cyc_kummer_meet p 5 (by omega) ζ

end IUT
