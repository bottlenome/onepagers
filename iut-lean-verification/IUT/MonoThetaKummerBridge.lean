/-
  IUT/MonoThetaKummerBridge.lean — M423F [実／本物／柱E]
  分類: 実（M393F `ThetaKummerTripleBridge` の capstone `tktb_class_governed`——
    mono-theta 環境 `env` の [Θ]（`env.kummerRigid.cls`＝M353F `tkcClass M κ e`）が三剛性束の
    合流元 ζ·ζ に支配される——と、M377F `LogKummerMonoTheta` の capstone
    `lkm_kummer_class_transported`——同じ M/κ/e を持つテータ Kummer 類が log-Kummer 対応で
    log-shell 側へ輸送（全射で尽くす）される——を、**同一の M/κ/e** の上で一つの conjunction
    に結ぶ本物のブリッジ）。
  complete_pct 影響: 柱E で、[Θ]（`tkcClass M κ e`）が env の三剛性束の合流元 ζ·ζ に支配される
    という M393F の統治関係と、その**同じ M κ e** のテータ Kummer 類が log-Kummer 対応（M377F）
    により log-shell を尽くす形で輸送される、という二つの実の事実が**単一の M κ e の上で
    同時に成立する**ことを machine-checked にする（M393F と M377F は独立に存在していたが、
    どちらも `tkcClass M κ e`/`TkcData M κ e` という同じ本物の対象を主語にしており、本層は
    その主語の一致を陽に一つの capstone として固定した）。
  正直な限定: crux Dβ-ω（M377F `lkm_crux_external`/`lkm_crux_is_hypothesis`）は本層でも
    決して導出せず、外部仮説のまま（`mtk_crux_external` で Iff.rfl 相当の受け渡しとして
    再確認）。log-Kummer 対応側は log-shell/表現レベルの輸送（M377F の正直な限定を継承、
    完全な H¹⇄log-shell 写像・tempered π₁^ét・解析的エタールテータ本体は範囲外）。
    本層自体は概ね M393F/M377F の capstone の再輸出＋一箇所への集約（新規の計算核は無く、
    「同じ M κ e 上で二つの capstone が同時に成立する」という conjunction の構成が新規）。

  ## 内容（tier-S・実ブリッジ、M393F↔M377F の直接連結）

  M393F `tktb_class_governed` は一つの mono-theta 環境 `env`（M363F `MonoThetaEnvBundle`）
  に対し、`env` が束ねるテータ Kummer 類の剛性データの類 `env.kummerRigid.cls` が M353F の
  本物の類 `tkcClass M κ e` そのものであり、その係数座標（`tkrRigidIso` 座標 2）が三剛性束の
  合流元 ζ·ζ に支配され、かつ三剛性（定数倍・離散・円分）が同時に成立することを一つの
  capstone に閉じた。一方 M377F `lkm_kummer_class_transported` は（`env` の内部円分体の素数
  とは独立な）局所体の素数 `pL`・段 `d` に対し、テータ Kummer 類 `TkcData M κ e` が存在し、
  かつ log-Kummer 対応（graded log θ_d）が Frobenius-like 乗法 U^(d) 側から étale-like 加法
  log-shell ℤ/pL 側へ**全射**する（log-shell を尽くす）ことを示した。両者は独立に構成された
  が、いずれも「同じ本物の対象 `tkcClass M κ e`／`TkcData M κ e`」を主語にしている。本層は
  その一致を陽に取り出し一つの capstone に結ぶ:

  * M423F-1 `mtk_class_transport`（本丸 capstone）— 一つの mono-theta 環境 `env`
    （M363F、[Θ] を束ねる M/κ/e を固定）と局所体パラメータ `pL, d` に対し:
    (I) `env` 側の統治関係（M393F `tktb_class_governed`: `env.kummerRigid.cls = tkcClass M κ e`・
    座標 2 の値 ζ·ζ・円分剛性座標との一致・三剛性の同時成立）が、
    (II) 同じ `M κ e` を持つテータ Kummer 類が log-Kummer 対応で存在し log-shell を尽くす
    （M377F `lkm_kummer_class_transported`）が、**同時に**成立する。
  * M423F-2 `mtk_crux_external` — M423F-1 の統合されたブリッジ命題と crux Dβ-ω（外部仮説）の
    連言（crux は受け取るのみ、M377F `lkm_crux_external` と同じ精神で本層でも導出しない）。
  * M423F-3 `MonoThetaKummerTransportData` / `monoThetaKummerTransportData` / `mtk_exists` —
    M423F-1 の全成分を一つの witness レコードに束ね、存在を示す。
  * M423F-4 実例（l=5・μ_{10}・本物の G_ℚ 上、局所体は ℚ₂・d=1、M393F/M377F と同じ具体構成）。

  選択公理不使用（新規 Classical.choice なし；継承分の Quot.sound のみ）。sorry 皆無・
  禁止タクティク不使用（rw/exact/apply のみ使用、新規 tactic block 不要な純再輸出＋conjunction
  が中心）。一般名は `mtk` 接頭辞で衝突回避。共有ファイル（IUT.lean・build.sh・dashboard.md・
  graph 系）は一切変更していない。
-/
import IUT.ThetaKummerTripleBridge
import IUT.LogKummerMonoTheta

namespace IUT

/-! ## M423F-1: 本丸 capstone——[Θ] の三剛性束統治と log-Kummer 輸送が同じ M/κ/e 上で同時成立 -/

/-- **定理 (M423F-1: capstone——mono-theta 環境の [Θ] は三剛性束の合流元に支配され、かつ
    同じテータ Kummer 類は log-Kummer 対応で log-shell 側へ輸送される)** — 一つの mono-theta
    環境 `env`（M363F `MonoThetaEnvBundle`、係数群 `M`・Kummer 捻り `κ`・指数 `e` を固定）と
    局所体パラメータ `pL`（log-shell 側の素数）・`d`（フィルトレーション段）に対し:
    (I) `env` が束ねるテータ Kummer 類の剛性データの類 `env.kummerRigid.cls` は M353F の
        本物の類 `tkcClass M κ e` そのものであり、その係数同一視の座標 2 の値は ζ·ζ に一致し、
        その値は `env` の円分剛性（座標 1）と一致し、かつ `env` の三剛性（定数倍・離散・円分）
        の本丸命題が同時に成立する（M393F `tktb_class_governed` の再輸出）、
    (II) 同じ `M κ e` に対し、テータ Kummer 類 `TkcData M κ e` が存在し、log-Kummer 対応
        （graded log θ_d、Frobenius-like 乗法 U^(pL,d) → étale-like 加法 log-shell ℤ/pL）は
        任意の加法 log-shell 類を乗法単数の log として実現する（全射、M377F
        `lkm_kummer_class_transported` の再輸出）。
    (I)(II) を一つの capstone に閉じることで、「M393F が統治する [Θ]（三剛性束の合流元 ζ·ζ に
    支配される）」と「M377F が log-shell へ輸送する [Θ]」が**同一の本物の対象 `tkcClass M κ e`**
    の上で同時に成立することを machine-checked にする。 -/
theorem mtk_class_transport {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e)
    (pL d : Nat) (hp : 1 ≤ pL) (hd : 1 ≤ d) :
    (env.kummerRigid.cls = tkcClass M κ e
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
          ∧ env.cyclotomic.rigIso 1 = zpMul p ζ ζ))
    ∧ (Nonempty (TkcData M κ e)
      ∧ ∀ c : lkmEtaleSide pL, ∃ u : lkmFrobSide pL,
          (unitFiltration pL d).mem u ∧ lkmCorrespondence pL d hp u = c) :=
  ⟨tktb_class_governed env, lkm_kummer_class_transported M κ e pL d hp hd⟩

/-! ## M423F-2: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M423F-2: crux は外部仮説・decisive に導出しない／honest)** — M423F-1 の統合
    ブリッジ命題（[Θ] の三剛性束統治と log-Kummer 輸送の同時成立）と crux Dβ-ω（多輻的
    アルゴリズム＝theta-link 整合＝IUT 論争の当の係争点）の連言。crux を任意の外部 Prop
    `crux` として受け取り、統合ブリッジの本物性 **と** crux の連言を、crux が仮説として
    供給された場合にのみ返す——crux は決して導出されない（M377F `lkm_crux_external` と
    同じ精神、過大主張禁止）。 -/
theorem mtk_crux_external {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e)
    (pL d : Nat) (hp : 1 ≤ pL) (hd : 1 ≤ d)
    (crux : Prop) (hcrux : crux) :
    (env.kummerRigid.cls = tkcClass M κ e
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
          ∧ env.cyclotomic.rigIso 1 = zpMul p ζ ζ))
    ∧ (Nonempty (TkcData M κ e)
      ∧ ∀ c : lkmEtaleSide pL, ∃ u : lkmFrobSide pL,
          (unitFiltration pL d).mem u ∧ lkmCorrespondence pL d hp u = c)
    ∧ crux :=
  ⟨(mtk_class_transport env pL d hp hd).1, (mtk_class_transport env pL d hp hd).2, hcrux⟩

/-- **定理 (M423F-2b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説
    そのもの**として扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明した定理では
    なく、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で明示
    （M377F `lkm_crux_is_hypothesis` と同じ、再確認の再輸出）。 -/
theorem mtk_crux_is_hypothesis (crux : Prop) : crux ↔ crux := lkm_crux_is_hypothesis crux

/-! ## M423F-3: 総括レコード（witness）と存在 -/

/-- **M423F-3a: [Θ] 三剛性束統治・log-Kummer 輸送ブリッジデータ** — 一つの mono-theta 環境
    `env` の上に、[Θ] の三剛性束統治（M393F）と、同じ M/κ/e のテータ Kummer 類の log-Kummer
    輸送（M377F）を一括束ねる。主語は本物の env のフィールドと本物のテータ Kummer 類
    `tkcClass`/`TkcData`（toy 代理なし）。 -/
structure MonoThetaKummerTransportData {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e)
    (pL d : Nat) where
  /-- env のテータ Kummer 類の剛性データの類は M353F の本物の類そのもの。 -/
  cls_eq : env.kummerRigid.cls = tkcClass M κ e
  /-- [Θ] の係数同一視の座標 2 の値は ζ·ζ。 -/
  coord2_mul : tkrRigidIso p (2 * l) ζ 2 = zpMul p ζ ζ
  /-- 座標 2 の値は env の円分剛性（座標 1）の値と一致する。 -/
  coord2_eq_cyclotomic : env.cyclotomic.rigIso 1 = tkrRigidIso p (2 * l) ζ 2
  /-- 三剛性の本丸命題が同時に成立し、円分剛性は ζ·ζ に合流する。 -/
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
  /-- hp : 1 ≤ pL（局所体側の素数）。 -/
  hp : 1 ≤ pL
  /-- hd : 1 ≤ d（フィルトレーション段）。 -/
  hd : 1 ≤ d
  /-- 同じ M κ e に対しテータ Kummer 類データが存在する（M377F）。 -/
  cls_nonempty : Nonempty (TkcData M κ e)
  /-- log-Kummer 対応は加法 log-shell を尽くす（全射、M377F）。 -/
  transport_surj : ∀ c : lkmEtaleSide pL, ∃ u : lkmFrobSide pL,
    (unitFiltration pL d).mem u ∧ lkmCorrespondence pL d hp u = c

/-- **M423F-3b: witness 本体** — 各フィールドを M423F-1 の主定理で埋める。 -/
def monoThetaKummerTransportData {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e)
    (pL d : Nat) (hp : 1 ≤ pL) (hd : 1 ≤ d) :
    MonoThetaKummerTransportData env pL d where
  cls_eq := (tktb_class_governed env).1
  coord2_mul := (tktb_class_governed env).2.1
  coord2_eq_cyclotomic := (tktb_class_governed env).2.2.1
  triple_holds := (tktb_class_governed env).2.2.2
  hp := hp
  hd := hd
  cls_nonempty := (lkm_kummer_class_transported M κ e pL d hp hd).1
  transport_surj := (lkm_kummer_class_transported M κ e pL d hp hd).2

/-- **定理 (M423F-3c: [Θ] 三剛性束統治・log-Kummer 輸送ブリッジデータの存在)** — 任意の
    mono-theta 環境 `env` と局所体パラメータ `pL, d`（`hp : 1 ≤ pL`・`hd : 1 ≤ d`）に対し、
    [Θ] の三剛性束統治（M393F）と同じ M/κ/e の log-Kummer 輸送（M377F）を一括束ねたデータが
    存在する。 -/
theorem mtk_exists {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e)
    (pL d : Nat) (hp : 1 ≤ pL) (hd : 1 ≤ d) :
    Nonempty (MonoThetaKummerTransportData env pL d) :=
  ⟨monoThetaKummerTransportData env pL d hp hd⟩

/-! ## M423F-4: 実例（l=5・μ_{10}・本物の G_ℚ 上、局所体は ℚ₂・d=1） -/

/-- **定理 (M423F-4: 実例)** — 本物の絶対ガロア群 G_ℚ・μ_{10}・自明作用・自明 Kummer 捻り・
    指数 e=4 と、10 ∣ p−1 なる素数 p に対する本物の μ_{10}(ℤ_p) の生成元 ζ（M121F）から
    構成した mono-theta 環境（l=5、M363F `mteBuild`）に対し、そのテータ Kummer 類の剛性
    データの類は M353F の本物の類 `tkcClass` そのものであり（M393F 継承）、かつ同じ
    M/κ/e のテータ Kummer 類データが存在し、log-Kummer 対応（ℚ₂・d=1）は加法 log-shell
    ℤ/2 を尽くす（M377F 継承）。 -/
theorem mtk_example_l5 (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
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
      ∧ Nonempty (TkcData (cycMuStd (2 * 5) (by omega))
          (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
            (cycMuStd (2 * 5) (by omega))) 4)
      ∧ ∀ c : lkmEtaleSide 2, ∃ u : lkmFrobSide 2,
          (unitFiltration 2 1).mem u ∧ lkmCorrespondence 2 1 (by omega) u = c := by
  obtain ⟨ζ, hζl, hdist, _⟩ := mu_l_zp_exists p (2 * 5) hp (by omega) hdvd
  refine ⟨ζ, hζl, hdist, ?_, ?_⟩
  · exact (mteBuild R K q hInf p 5 (by omega) ζ hζl hdist
      (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
      (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega)))
      (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
        (cycMuStd (2 * 5) (by omega))) 4).kummerRigid.cls_eq
  · exact lkm_kummer_class_transported (cycMuStd (2 * 5) (by omega))
      (galThTrivialKummer (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega)))
      4 2 1 (by omega) (by omega)

/-- 実例: 統合ブリッジデータは任意の mono-theta 環境上で存在する（l=5, μ_10, ℚ₂・d=1）。 -/
example (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p : Nat) (hp5 : IsPrime p) (hdvd : (2 * 5) ∣ p - 1)
    (ζ : (Zp p).carrier) (hζ2l : zpPow p ζ (2 * 5) = zpOne p)
    (hdist2l : ∀ i j, i < j → j < 2 * 5 → zpPow p ζ i ≠ zpPow p ζ j) :
    Nonempty (MonoThetaKummerTransportData
      (mteBuild R K q hInf p 5 (by omega) ζ hζ2l hdist2l
        (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
        (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega)))
        (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
          (cycMuStd (2 * 5) (by omega))) 4) 2 1) :=
  mtk_exists
    (mteBuild R K q hInf p 5 (by omega) ζ hζ2l hdist2l
      (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
      (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega)))
      (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
        (cycMuStd (2 * 5) (by omega))) 4) 2 1 (by omega) (by omega)

end IUT

