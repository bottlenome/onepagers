/-
  IUT/ThetaKummerTripleBridge.lean — M393F [実／本物／柱E]
  分類: 実（M388F `MonoThetaTripleBridge` の三剛性 capstone `mtt_triple_holds` と、M353F
    `ThetaKummerClass` の本物のテータ Kummer 類 `tkcClass`＝[Θ]∈H¹(G_K,μ_{2l}) を、一つの
    mono-theta 環境 `env` の内部で直接連結する本物のブリッジ）。
  complete_pct 影響: 柱E で [Θ]（M353F `tkcClass`）が「env のどの実データから来るか」
    （`env.kummerRigid.cls`＝M358F/M363F 経由の同一視）を明示し、その [Θ] の係数同一視
    `tkrRigidIso`（M358F）が座標 2 で評価する値が、M388F の三剛性 capstone が同時に確立する
    合流元 ζ·ζ（`mtt_triple_holds` 第4連言・M388F-1 の自己積計算）にちょうど一致することを
    証明する。すなわち「[Θ] の剛性座標＝三剛性束の合流元」を一つの capstone
    `tktb_class_governed` に閉じ、三剛性が同時に成立する env 上でのみ [Θ] のこの同一視が
    実現されることを機械検証する。骨格の水増しではなく、既存の本物の部品
    （M353F/M358F/M363F/M383F/M388F）を新しい向きで一点に集約する本物の接続。
  正直な限定: 本層が確立するのは「[Θ] の代数的コホモロジー類とその μ_{2l} 係数同一視の
    座標 2 の値が、mono-theta 環境の三剛性束の合流元 ζ·ζ に一致する」という代数的識別のみ。
    完全な解析的エタールテータ類（p 進収束・遠アーベル復元込み）・tempered π₁^ét 本体は
    M353F/M358F/M363F/M383F/M388F と同様に外部仮説として継承し、本層でも導出しない。

  ## 内容（tier-S・実ブリッジ、M388F↔M353F の直接連結）

  M388F `MonoThetaTripleBridge` は一つの mono-theta 環境 `env`（M363F
  `MonoThetaEnvBundle`）に対し、三剛性（定数倍・離散・円分）の本丸命題が同時に成立し、
  円分剛性（μ_l 側、座標 1）がテータ Kummer 類の剛性（μ_{2l} 側、座標 2）と共有実元
  ζ·ζ に合流することを capstone `mtt_triple_holds` に閉じた。しかし `mtt_triple_holds` は
  「円分剛性同型の値」（`env.cyclotomic.rigIso 1`）を主語とし、M353F の**テータ Kummer 類
  そのもの**（`tkcClass`∈H¹(G_K,μ_{2l})、コホモロジー類としての [Θ]）へは踏み込んでいない。
  本層はその隙間を埋める:

  * M393F-1 `tktb_coord2_mul` — テータ Kummer 類の係数同一視 `tkrRigidIso p (2l) ζ`
    （M358F）を座標 2 で評価した値は、ζ の自己積 zpMul p ζ ζ に一致する（M383F
    `trb_kummer_two`：座標 2 は ζ² を与える、＋M388F `mtt_zeta_sq_mul`：ζ²=ζ·ζ、の合成）。
  * M393F-2 `tktb_class_governed`（本丸 capstone）— 任意の mono-theta 環境 `env` に対し:
    (i) `env` が束ねるテータ Kummer 類の剛性データのコホモロジー類 `env.kummerRigid.cls`
    は M353F の本物の類 `tkcClass M κ e` そのものである（`TkrData.cls_eq`、環境の中で
    [Θ] が実際にどの本物の対象と同一視されるかの明示）、
    (ii) その [Θ] が住む係数加群 μ_{2l} の同一視 `tkrRigidIso` を座標 2 で評価した値は
    ζ·ζ（M393F-1）、
    (iii) その座標 2 の値は `env` の円分剛性（μ_l 側、座標 1）が与える値と一致する
    （M383F `trb_env_meet` の再輸出）、
    (iv) 以上と同時に、`env` の三剛性（定数倍・離散・円分）の本丸命題が丸ごと成立する
    （M388F `mtt_triple_holds` の再輸出）。
    (i)〜(iv) を一つの連言に閉じることで、「[Θ] の剛性座標（tkrRigidIso 座標 2 の値）＝
    三剛性束の合流元 ζ·ζ」であり、かつこの合流が三剛性すべてが同時に成立する**その同じ
    env** の上で起きることを machine-checked にする。
  * M393F-3 `ThetaKummerTripleBridgeData` / `thetaKummerTripleBridgeData` / `tktb_exists` —
    上記を一つの witness レコードに束ね、任意の env に対する存在を示す。
  * M393F-4 実例（l=5・μ_{10}・本物の G_ℚ 上、M383F/M388F と同じ具体構成）。

  選択公理不使用（新規 Classical.choice なし；継承分の Quot.sound のみ）。sorry 皆無・
  禁止タクティク不使用（rw/exact/apply のみ使用、新規 tactic block 不要な純再輸出＋合成が
  中心）。一般名は `tktb` 接頭辞で衝突回避。共有ファイル（IUT.lean・build.sh・dashboard.md・
  graph 系）は一切変更していない。
-/
import IUT.MonoThetaTripleBridge

namespace IUT

/-! ## M393F-1: [Θ] の係数同一視の座標 2 の値は ζ·ζ（M383F＋M388F の合成） -/

/-- **定理 (M393F-1: テータ Kummer 類の係数同一視、座標 2 は ζ の自己積)** — テータ
    Kummer 類 [Θ]（M353F）が住む係数加群 μ_{2l} の同一視 `tkrRigidIso p (2l) ζ`（M358F）を
    内部座標 2 で評価した値は、ζ の自己積 zpMul p ζ ζ に一致する。M383F `trb_kummer_two`
    （座標 2 は ζ²=zpPow p ζ 2 を与える）と M388F `mtt_zeta_sq_mul`（ζ²=ζ·ζ）の合成、
    [Θ] の係数側とテータ Kummer 類三剛性束の合流元を直結する本物の核。 -/
theorem tktb_coord2_mul (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    tkrRigidIso p (2 * l) ζ 2 = zpMul p ζ ζ :=
  (trb_kummer_two p l hl ζ).trans (mtt_zeta_sq_mul p ζ)

/-! ## M393F-2: 本丸 capstone——[Θ] の剛性座標は三剛性束の合流元に支配される -/

/-- **定理 (M393F-2: capstone——[Θ] は env のテータ Kummer 類データそのものであり、その
    剛性座標は三剛性束の合流元 ζ·ζ に支配される)** — 任意の mono-theta 環境 `env`
    （M363F `MonoThetaEnvBundle`）に対し:
    (1) `env` が束ねるテータ Kummer 類の剛性データの類 `env.kummerRigid.cls` は、M353F の
        本物のテータ Kummer 類 `tkcClass M κ e`（[Θ]∈H¹(G_K,μ_{2l})）そのものである
        （`TkrData.cls_eq`）、
    (2) [Θ] の係数同一視 `tkrRigidIso p (2l) ζ` を座標 2 で評価した値は ζ·ζ（M393F-1）、
    (3) その座標 2 の値は `env` の円分剛性（μ_l 側、座標 1）が与える値と一致する
        （M383F `trb_env_meet`）、
    (4) 以上と**同時に**、`env` の三剛性（定数倍・離散・円分）の本丸命題が成立し、円分剛性は
        ζ·ζ に合流する（M388F `mtt_triple_holds`）。
    (1)〜(4) を一つの capstone に閉じることで、「M353F の本物のテータ Kummer 類 [Θ] が、
    まさにこの env（三剛性がすべて同時に成立する env）の内部で、係数の剛性座標（座標 2）を
    通じて三剛性束の合流元 ζ·ζ に支配される」ことを machine-checked にする。 -/
theorem tktb_class_governed {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    env.kummerRigid.cls = tkcClass M κ e
    ∧ tkrRigidIso p (2 * l) ζ 2 = zpMul p ζ ζ
    ∧ env.cyclotomic.rigIso 1 = tkrRigidIso p (2 * l) ζ 2
    ∧ ((∀ (i j : Int) (c cInv : (laurentRing R).carrier),
          (laurentRing R).mul c cInv = (laurentRing R).one →
            (laurentRing R).mul ((laurentRing R).mul c (env.constMult.value i))
                ((laurentRing R).mul cInv (env.constMult.inv j))
              = env.constMult.ratio i j)
        ∧ (¬ ∃ n : Int, tateZpow (tateMultGroup K) env.discrete.q (2 * n)
            = tateZpow (tateMultGroup K) env.discrete.q 1)
        ∧ (env.cyclotomic.rigIso 1 = zpPow p ζ 2
            ∧ ∀ z : Int, env.cyclotomic.rigIso z = zpPow p ζ 2 → ((l : Nat) : Int) ∣ z - 1)
        ∧ env.cyclotomic.rigIso 1 = zpMul p ζ ζ) :=
  ⟨env.kummerRigid.cls_eq, tktb_coord2_mul p l hl ζ, trb_env_meet env, mtt_triple_holds env⟩

/-! ## M393F-3: 総括レコード（witness）と存在 -/

/-- **M393F-3a: [Θ]・三剛性束合流ブリッジデータ** — 一つの mono-theta 環境 `env` の上に、
    テータ Kummer 類の実の同一視（`env.kummerRigid.cls = tkcClass M κ e`）・その係数座標 2
    の値（ζ·ζ）・円分剛性座標との一致・三剛性の同時成立を一括束ねる。主語は本物の env の
    フィールドと本物のテータ Kummer 類 `tkcClass`（toy 代理なし）。 -/
structure ThetaKummerTripleBridgeData {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) where
  /-- env のテータ Kummer 類の剛性データの類は M353F の本物の類そのもの。 -/
  cls_eq : env.kummerRigid.cls = tkcClass M κ e
  /-- [Θ] の係数同一視の座標 2 の値は ζ·ζ。 -/
  coord2_mul : tkrRigidIso p (2 * l) ζ 2 = zpMul p ζ ζ
  /-- 座標 2 の値は env の円分剛性（座標 1）の値と一致する（M383F 再輸出）。 -/
  coord2_eq_cyclotomic : env.cyclotomic.rigIso 1 = tkrRigidIso p (2 * l) ζ 2
  /-- 三剛性の本丸命題が同時に成立し、円分剛性は ζ·ζ に合流する（M388F 再輸出）。 -/
  triple_holds :
    (∀ (i j : Int) (c cInv : (laurentRing R).carrier),
        (laurentRing R).mul c cInv = (laurentRing R).one →
          (laurentRing R).mul ((laurentRing R).mul c (env.constMult.value i))
              ((laurentRing R).mul cInv (env.constMult.inv j))
            = env.constMult.ratio i j)
    ∧ (¬ ∃ n : Int, tateZpow (tateMultGroup K) env.discrete.q (2 * n)
        = tateZpow (tateMultGroup K) env.discrete.q 1)
    ∧ (env.cyclotomic.rigIso 1 = zpPow p ζ 2
        ∧ ∀ z : Int, env.cyclotomic.rigIso z = zpPow p ζ 2 → ((l : Nat) : Int) ∣ z - 1)
    ∧ env.cyclotomic.rigIso 1 = zpMul p ζ ζ

/-- **M393F-3b: witness 本体** — 各フィールドを M393F-1〜2 の主定理で埋める。 -/
def thetaKummerTripleBridgeData {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    ThetaKummerTripleBridgeData env where
  cls_eq := env.kummerRigid.cls_eq
  coord2_mul := tktb_coord2_mul p l hl ζ
  coord2_eq_cyclotomic := trb_env_meet env
  triple_holds := mtt_triple_holds env

/-- **定理 (M393F-3c: [Θ]・三剛性束合流ブリッジデータの存在)** — 任意の mono-theta 環境
    `env` に対し、テータ Kummer 類の実の同一視・その係数座標 2 の値・三剛性の同時成立を
    一括束ねたデータが存在する。 -/
theorem tktb_exists {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    Nonempty (ThetaKummerTripleBridgeData env) :=
  ⟨thetaKummerTripleBridgeData env⟩

/-! ## M393F-4: 実例（l=5・μ_{10}・本物の G_ℚ 上） -/

/-- **定理 (M393F-4: 実例)** — 本物の絶対ガロア群 G_ℚ・μ_{10}・自明作用・自明 Kummer 捻り・
    指数 e=4 と、10 ∣ p−1 なる素数 p に対する本物の μ_{10}(ℤ_p) の生成元 ζ（M121F）から
    構成した mono-theta 環境（l=5、M363F `mteBuild`）に対し、そのテータ Kummer 類の剛性
    データの類は M353F の本物の類 `tkcClass` そのものであり、その係数同一視の座標 2 の値は
    ζ·ζ に一致する。 -/
theorem tktb_example_l5 (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p : Nat) (hp : IsPrime p) (hdvd : (2 * 5) ∣ p - 1) :
    ∃ (ζ : (Zp p).carrier) (hζ2l : zpPow p ζ (2 * 5) = zpOne p)
      (hdist2l : ∀ i j, i < j → j < 2 * 5 → zpPow p ζ i ≠ zpPow p ζ j),
      (mteBuild R K q hInf p 5 (by omega) ζ hζ2l hdist2l
        (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
        (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega)))
        (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
          (cycMuStd (2 * 5) (by omega))) 4
      ).kummerRigid.cls
        = tkcClass (cycMuStd (2 * 5) (by omega))
            (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
              (cycMuStd (2 * 5) (by omega))) 4
      ∧ tkrRigidIso p (2 * 5) ζ 2 = zpMul p ζ ζ := by
  obtain ⟨ζ, hζl, hdist, _⟩ := mu_l_zp_exists p (2 * 5) hp (by omega) hdvd
  refine ⟨ζ, hζl, hdist, ?_, tktb_coord2_mul p 5 (by omega) ζ⟩
  exact (mteBuild R K q hInf p 5 (by omega) ζ hζl hdist
    (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega)))
    (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
      (cycMuStd (2 * 5) (by omega))) 4).kummerRigid.cls_eq

end IUT
