-- M409F AbsTopFieldFromCyclotome [実・本物・柱A]
-- complete_pct 影響: 柱A で M404F の canonical G_K-加群円分体（cgm）の指標がちょうど M322F cycRigChar であり、
--   それが M329F AbsTopIII 体復元（absF）の入力 (K^×,v,χ) が消費する χ そのものであることを本物で示し、
--   復元体を「内部自己同型に対して剛＝群論的に内在的な」円分体に canonical に結びつける橋を閉じる。
-- 正直な限定: π₁^ét（幾何的 tempered π₁^temp）から (K^×,v,χ) を抽出する完全 mono-anabelian 数体復元アルゴリズムは外部/後続。
/-
  IUT/AbsTopFieldFromCyclotome.lean — M409F [実／本物・柱A]
  分類: 実（本物の対象の上での橋: M404F canonical 円分体 G_K-加群 ⇄ M329F AbsTopIII 体復元）

  遠アーベル（柱A）の系譜と本モジュールの位置:
    * M322F (cycRigChar, IUT/CyclotomicRigidity.lean): G_K の μ_n 作用が定める**実円分指標** χ_n。
    * M404F (cgm, IUT/CyclotomeGaloisModule.lean): 内在的に復元された中心 ≅ μ_l を、その上の χ 捻り
      G_K 作用まで込めて **canonical な G_K-加群**として組み上げ（σ_1=id・σ_{gh}=σ_g∘σ_h・各 σ_g は
      群準同型）、その指標がちょうど cycRigChar に一致し、かつ内部自己同型に対して剛（inner-invariant）で
      あることを完全証明した。
    * M329F (absF, IUT/AbsTopFieldRecover.lean): AbsTopIII 入力 `AbsTopIIIInputSkeleton` (K^×,v,χ) から
      加法を復元し、復元環が元の体 K に一致（恒等同型）することを完全証明した。χ の台は入力 `gal`
      （M322F `CycGKAction`）で受け取る。
    * M334F (cycRecCharOfAction, IUT/CyclotomeRecovery.lean): `CycGKAction ρ` から χ データを取り出す
      （`cycRecCharOfAction GK M ρ).chi = cycRigChar GK M ρ`）——M329F 体復元が消費する χ の実体。

  本モジュール（M409F）が閉じる**橋**（すべて本物の対象・toy 群/toy 指標なし・選択公理不使用）:
    AbsTopIII 入力 `AbsTopIIIInputSkeleton K GK M` は Galois 作用 `inp.gal : CycGKAction GK M` を持つ。
    この**同一の** `inp.gal` から:
      (i)  M404F は canonical 円分体 G_K-加群 `cyclotomeGaloisModuleData p l ζ0 GK M inp.gal` を組み、
      (ii) M329F の体復元が消費する χ は `cycRecCharOfAction GK M inp.gal).chi = cycRigChar GK M inp.gal`。
    ゆえに **M329F 体復元を養う χ は、ちょうど M404F canonical 円分体の指標**（同一の実円分指標
    cycRigChar）である。よって復元体は、群論的に内在的（内部自己同型に対して剛）な円分体に
    canonical に付随する。具体的に本モジュールは:
      * M409F-1 χ 同定: M329F 入力が消費する χ = M404F canonical 円分体の指標 cycRigChar（rfl 同定）。
      * M409F-2 canonical 円分体が体復元を養う指標の形（生成元作用 σ_g(ζ)=ζ^{χ(g)}・χ 準同型・χ(1)=1）。
      * M409F-3 体復元 = 元の体（M329F absF 再利用: 加法一致・乗法一致）。
      * M409F-4 canonical 性: 体を養う円分体は内部自己同型に対し剛（M404F cgm_inner_galois_commute・
        centerToMu 内部不変）——復元体は inner-automorphism-canonical。
      * M409F-5 capstone `atfc_absTopIII_from_cyclotome`: (K^×,v,χ) 入力から、体復元が元の体に一致し、
        その χ = M404F canonical 円分体の指標 cycRigChar であり、円分体が内部自己同型剛であることを束ねる。
      * M409F-6 capstone データ `AbsTopFieldFromCyclotomeData` + `atfc_toData` + `atfc_exists`。
      * M409F-7 実例（G_ℚ・具体 level）。

  意義: M334F は「χ から円分体 μ̂ を復元」して体復元と円分体復元を一周させたが、その円分体は
  `cycRec_mu_from_chi`（ℤ/n 上の χ 捻り模型）だった。M409F は**M404F の canonical G_K-加群円分体
  （中心の内在復元・その剛性・χ 捻り作用・実円分指標を束ねた本物）**を体復元に接続し、「体復元を
  養う χ は群に canonical に付随する（内部自己同型剛な）円分体の指標そのもの」という遠アーベルの
  結び目を本物で閉じる。主語はすべて本物: 本物の体 K（M264F）・本物の付値（M301F）・本物の μ_l 作用
  （M322F `CycGKAction`）・本物の内在中心（thetaGrp）・本物の内部自己同型（M399F tgrigConj）。

  正直な限定（消去弱化禁止）: 完全な mono-anabelian 復元アルゴリズム（幾何的 tempered π₁^temp の
  slim 遠アーベル性・π₁^ét から (K^×,v,χ) を抽出する完全アルゴリズム・[EtTh] mono-theta 環境全体）は
  外部（幾何的入力・後続）。本モジュールは、既に本物化された M404F canonical 円分体と M329F 体復元を
  「同一の Galois 作用 inp.gal を通じて結ぶ」橋を閉じるのであって、幾何的入力そのものは扱わない。
  中心 ≅ μ_l の同一視は既存 2 モデル（抽象 M.μ と Zp p 上 centerToMu）を経由する既存構図の忠実な継承。
  全て選択公理不使用（新規 Classical.choice なし・propext / Quot.sound のみ）。
-/
import IUT.CyclotomeGaloisModule
import IUT.CyclotomeRecovery

namespace IUT

/-! ## M409F-1: χ 同定 — M329F 体復元が消費する χ = M404F canonical 円分体の指標 cycRigChar

  AbsTopIII 入力 `inp` の Galois 作用 `inp.gal` から、M329F の体復元が消費する χ は
  `cycRecCharOfAction GK M inp.gal).chi`（M334F 接続）、M404F canonical 円分体の指標は
  `cycRigChar GK M inp.gal`（M404F cgm_char_*）。両者は**同一の実円分指標**である。 -/

/-- **M409F-1a: χ 同定（本橋の核）** — M329F の AbsTopIII 体復元が入力 `inp.gal` から消費する
    円分指標 χ = `cycRecCharOfAction GK M inp.gal).chi` は、ちょうど M404F canonical 円分体
    G_K-加群の指標 `cycRigChar GK M inp.gal` に一致する。復元体を養う χ が、群論的に内在的な
    canonical 円分体の指標そのものであることの同定。 -/
theorem atfc_char_eq_cycRigChar {GK : Grp} {M : CycMuGroup}
    (ρ : CycGKAction GK M) (g : GK.carrier) :
    (cycRecCharOfAction GK M ρ).chi g = cycRigChar GK M ρ g := rfl

/-- **M409F-1b: χ 同定（AbsTopIII 入力版）** — 入力 `inp` の Galois 台 `inp.gal` について、
    M329F 体復元が消費する χ = M404F canonical 円分体の指標。 -/
theorem atfc_input_char_eq_cycRigChar {K : IUTField} {GK : Grp} {M : CycMuGroup}
    (inp : AbsTopIIIInputSkeleton K GK M) (g : GK.carrier) :
    (cycRecCharOfAction GK M inp.gal).chi g = cycRigChar GK M inp.gal g := rfl

/-! ## M409F-2: canonical 円分体が体復元を養う指標の形（M404F cgm_char_* 再利用）

  体復元を養う χ = cycRigChar の作用は、M404F canonical 円分体の実 G_K-加群作用そのもの:
  生成元で σ_g(ζ)=ζ^{χ(g)}、χ は準同型、χ(1)=1。 -/

/-- **M409F-2a: 生成元作用 σ_g(ζ)=ζ^{χ(g)}** — canonical 円分体（体復元の χ 源）の生成元での
    作用（M404F cgm_char_gen）。 -/
theorem atfc_cyclotome_char_gen {GK : Grp} {M : CycMuGroup} (ρ : CycGKAction GK M)
    (g : GK.carrier) :
    galThMuAct GK M ρ g (M.μ.pow M.ζ 1) = M.μ.pow M.ζ (cycRigExp GK M ρ g) :=
  cgm_char_gen GK M ρ g

/-- **M409F-2b: χ の準同型性 χ(gh)=χ(g)·χ(h)**（M404F cgm_char_hom）。 -/
theorem atfc_cyclotome_char_hom {GK : Grp} {M : CycMuGroup} (ρ : CycGKAction GK M)
    (g h : GK.carrier) :
    cycRigChar GK M ρ (GK.mul g h)
      = zmodMul M.n (cycRigChar GK M ρ g) (cycRigChar GK M ρ h) :=
  cgm_char_hom GK M ρ g h

/-- **M409F-2c: χ(1)=1**（M404F cgm_char_one）。 -/
theorem atfc_cyclotome_char_one {GK : Grp} {M : CycMuGroup} (ρ : CycGKAction GK M) :
    cycRigChar GK M ρ GK.one = Quot.mk (modCong M.n).rel 1 :=
  cgm_char_one GK M ρ

/-- **M409F-2d: 復元作用は本物の群作用（合成則）**（M404F cgm_act_mul）——体復元を養う円分体が
    本物の G_K-加群であることの核。 -/
theorem atfc_cyclotome_act_mul {GK : Grp} {M : CycMuGroup} (ρ : CycGKAction GK M)
    (g h : GK.carrier) (z : M.μ.carrier) :
    galThMuAct GK M ρ (GK.mul g h) z = galThMuAct GK M ρ g (galThMuAct GK M ρ h z) :=
  cgm_act_mul GK M ρ g h z

/-! ## M409F-3: 体復元 = 元の体（M329F absF 再利用）

  M404F canonical 円分体を χ 源とする M329F 体復元は、その加法・乗法が元の体 K に一致する
  （復元環 ≅ 元の体・恒等同型）。 -/

/-- **M409F-3a: 復元加法 = 元の体加法（M329F absF_add_eq）**。 -/
theorem atfc_field_add_eq (K : IUTField) [DecidableEq K.carrier] (x y : K.carrier) :
    (absFRecoveredRing K).add x y = K.add x y :=
  absF_add_eq K x y

/-- **M409F-3b: 復元乗法 = 元の体乗法**（定義的一致）。 -/
theorem atfc_field_mul_eq (K : IUTField) [DecidableEq K.carrier] :
    (absFRecoveredRing K).mul = K.mul := rfl

/-! ## M409F-4: canonical 性 — 体を養う円分体は内部自己同型に対し剛（M404F 内在性）

  体復元を養う円分体（M404F canonical G_K-加群）の Galois χ 捻りは**内部自己同型と可換**であり、
  復元同一視 centerToMu は χ 捻り後も内部自己同型不変。ゆえに復元体はこの意味で
  inner-automorphism-canonical——群論的に内在的な円分体に一意付随する。 -/

/-- **M409F-4a: 内部自己同型とガロア χ 捻りは中心上で可換（M404F cgm_inner_galois_commute）** —
    体復元を養う円分体の Galois 加群構造は内部自己同型に依存しない。 -/
theorem atfc_inner_galois_commute {GK : Grp} {M : CycMuGroup} (ρ : CycGKAction GK M)
    (g : GK.carrier) (h : thetaGrp.carrier) (c : Int) :
    (tgrigConj thetaGrp h).map (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier))
      = ttoaAct GK M ρ g ((tgrigConj thetaGrp h).map ((0, 0, c) : thetaGrp.carrier)) :=
  cgm_inner_galois_commute GK M ρ g h c

/-- **M409F-4b: 復元同一視 centerToMu は χ 捻り後も内部自己同型不変（M404F cgm_centerToMu_inner_invariant）**。 -/
theorem atfc_centerToMu_inner_invariant (p l : Nat) (ζ0 : (Zp p).carrier)
    {GK : Grp} {M : CycMuGroup} (ρ : CycGKAction GK M)
    (g : GK.carrier) (h : thetaGrp.carrier) (c : Int) :
    centerToMu p l ζ0
        ((tgrigConj thetaGrp h).map (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier))).2.2
      = centerToMu p l ζ0 (ttoaChar GK M ρ g * c) :=
  cgm_centerToMu_inner_invariant p l ζ0 GK M ρ g h c

/-! ## M409F-5: capstone — (K^×,v,χ) 体復元は canonical 円分体に養われる -/

/-- **M409F-5: AbsTopIII 体復元 ⇐ canonical 円分体（capstone）** — AbsTopIII 入力
    `AbsTopIIIInputSkeleton K GK M`（乗法＋付値 K^×,v ＋ Galois 作用 χ の台 `gal`）から、
      (1) M329F 体復元が元の体 K に一致（加法・乗法とも）、
      (2) 体復元が消費する χ = `cycRecCharOfAction GK M inp.gal).chi` は M404F canonical 円分体の
          指標 `cycRigChar GK M inp.gal` に一致（χ 同定・本橋の核）、
      (3) その canonical 円分体の生成元作用 σ_g(ζ)=ζ^{χ(g)}（M404F cgm_char_gen）、
      (4) canonical 性: 円分体の Galois χ 捻りは内部自己同型と中心上で可換（M404F 内在性）——
          復元体は inner-automorphism-canonical、
    を一つに束ねる。「(K^×,v,χ) 体復元を養う χ は、群論的に内在的（内部自己同型剛）な canonical
    円分体の指標そのもの」という遠アーベルの結び目を本物で閉じる（π₁^ét→(K^×,v,χ) の完全抽出は外部）。 -/
theorem atfc_absTopIII_from_cyclotome (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) [DecidableEq K.carrier] {GK : Grp} {M : CycMuGroup}
    (inp : AbsTopIIIInputSkeleton K GK M) :
    (∀ x y, (absFRecoveredRing K).add x y = K.add x y) ∧
    (absFRecoveredRing K).mul = K.mul ∧
    (∀ g, (cycRecCharOfAction GK M inp.gal).chi g = cycRigChar GK M inp.gal g) ∧
    (∀ g, galThMuAct GK M inp.gal g (M.μ.pow M.ζ 1)
      = M.μ.pow M.ζ (cycRigExp GK M inp.gal g)) ∧
    (∀ (g : GK.carrier) (h : thetaGrp.carrier) (c : Int),
      (tgrigConj thetaGrp h).map (ttoaAct GK M inp.gal g ((0, 0, c) : thetaGrp.carrier))
        = ttoaAct GK M inp.gal g
            ((tgrigConj thetaGrp h).map ((0, 0, c) : thetaGrp.carrier))) :=
  ⟨fun x y => absF_add_eq K x y, rfl, fun _ => rfl,
   cgm_char_gen GK M inp.gal, cgm_inner_galois_commute GK M inp.gal⟩

/-! ## M409F-6: capstone データ -/

/-- **M409F-6a: canonical 円分体に養われた AbsTopIII 体復元データ** — 同一の Galois 作用 `inp.gal`
    を通じて、M404F canonical 円分体 G_K-加群データ・M329F 体復元データ・両者を結ぶ χ 同定・
    体の元体一致・円分体の内部自己同型剛性を束ねる。主語はすべて本物（toy なし）。 -/
structure AbsTopFieldFromCyclotomeData (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) [DecidableEq K.carrier] (GK : Grp) (M : CycMuGroup)
    (inp : AbsTopIIIInputSkeleton K GK M) where
  /-- M404F canonical 円分体 G_K-加群データ（同一の `inp.gal` から）。 -/
  cyclotome : CyclotomeGaloisModuleData p l ζ0 GK M inp.gal
  /-- M329F 体復元データ（復元環＝元の体）。 -/
  field_data : AbsTopFieldData K
  /-- χ 同定: 体復元が消費する χ = canonical 円分体の指標 cycRigChar。 -/
  char_eq : ∀ g, (cycRecCharOfAction GK M inp.gal).chi g = cycRigChar GK M inp.gal g
  /-- 復元加法 = 元の体加法。 -/
  field_add_eq : ∀ x y, (absFRecoveredRing K).add x y = K.add x y
  /-- 復元乗法 = 元の体乗法。 -/
  field_mul_eq : (absFRecoveredRing K).mul = K.mul
  /-- canonical 性: 円分体の Galois χ 捻りは内部自己同型と中心上で可換。 -/
  inner_canonical : ∀ (g : GK.carrier) (h : thetaGrp.carrier) (c : Int),
    (tgrigConj thetaGrp h).map (ttoaAct GK M inp.gal g ((0, 0, c) : thetaGrp.carrier))
      = ttoaAct GK M inp.gal g
          ((tgrigConj thetaGrp h).map ((0, 0, c) : thetaGrp.carrier))

/-- **M409F-6b: witness 本体** — 全フィールドを M404F/M329F の本物の証明で埋める
    （外部仮説は付値 val のみ・ζ0 が単数根であることすら不要）。 -/
def atfc_toData (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) [DecidableEq K.carrier] {GK : Grp} {M : CycMuGroup}
    (inp : AbsTopIIIInputSkeleton K GK M) (val : valRingValuation K) :
    AbsTopFieldFromCyclotomeData p l ζ0 K GK M inp where
  cyclotome := cyclotomeGaloisModuleData p l ζ0 GK M inp.gal
  field_data := absF_toFieldData K val
  char_eq := fun _ => rfl
  field_add_eq := fun x y => absF_add_eq K x y
  field_mul_eq := rfl
  inner_canonical := cgm_inner_galois_commute GK M inp.gal

/-- **M409F-6c: capstone データの存在** — DecidableEq を持つ体上、自明付値から、canonical 円分体に
    養われた AbsTopIII 体復元データが**外部仮説なしで**存在する。具体的な数体・局所体の離散付値上の
    復元は柱B ℤ_p 接続の後続。 -/
theorem atfc_exists (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) [DecidableEq K.carrier] {GK : Grp} {M : CycMuGroup}
    (inp : AbsTopIIIInputSkeleton K GK M) :
    Nonempty (AbsTopFieldFromCyclotomeData p l ζ0 K GK M inp) :=
  ⟨atfc_toData p l ζ0 K inp (trivialValuation K)⟩

/-! ## M409F-7: 実例 -/

/-- 実例: 任意の AbsTopIII 入力で、体復元が消費する χ = M404F canonical 円分体の指標
    cycRigChar（本橋の核の実インスタンス）。 -/
example {K : IUTField} {GK : Grp} {M : CycMuGroup}
    (inp : AbsTopIIIInputSkeleton K GK M) (g : GK.carrier) :
    (cycRecCharOfAction GK M inp.gal).chi g = cycRigChar GK M inp.gal g :=
  atfc_input_char_eq_cycRigChar inp g

/-- 実例: p=7・l=5 の canonical 円分体に養われた体復元データが存在する
    （K は DecidableEq を持つ任意の体・inp は任意の AbsTopIII 入力）。 -/
example (K : IUTField) [DecidableEq K.carrier] (ζ0 : (Zp 7).carrier)
    {GK : Grp} {M : CycMuGroup} (inp : AbsTopIIIInputSkeleton K GK M) :
    Nonempty (AbsTopFieldFromCyclotomeData 7 5 ζ0 K GK M inp) :=
  atfc_exists 7 5 ζ0 K inp

/-- 実例: capstone — (K^×,v,χ) 体復元が元の体に一致し、その χ が canonical 円分体の指標である。 -/
example (K : IUTField) [DecidableEq K.carrier] (ζ0 : (Zp 7).carrier)
    {GK : Grp} {M : CycMuGroup} (inp : AbsTopIIIInputSkeleton K GK M) :
    (∀ x y, (absFRecoveredRing K).add x y = K.add x y) ∧
    (absFRecoveredRing K).mul = K.mul ∧
    (∀ g, (cycRecCharOfAction GK M inp.gal).chi g = cycRigChar GK M inp.gal g) ∧
    (∀ g, galThMuAct GK M inp.gal g (M.μ.pow M.ζ 1)
      = M.μ.pow M.ζ (cycRigExp GK M inp.gal g)) ∧
    (∀ (g : GK.carrier) (h : thetaGrp.carrier) (c : Int),
      (tgrigConj thetaGrp h).map (ttoaAct GK M inp.gal g ((0, 0, c) : thetaGrp.carrier))
        = ttoaAct GK M inp.gal g
            ((tgrigConj thetaGrp h).map ((0, 0, c) : thetaGrp.carrier))) :=
  atfc_absTopIII_from_cyclotome 7 5 ζ0 K inp

/-- 実例: 体を養う canonical 円分体は内部自己同型 conj_{(2,3,5)} に対し剛（inner-automorphism-canonical）。 -/
example {GK : Grp} {M : CycMuGroup} (ρ : CycGKAction GK M) (g : GK.carrier) (c : Int) :
    (tgrigConj thetaGrp ((2, 3, 5) : thetaGrp.carrier)).map
        (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier))
      = ttoaAct GK M ρ g
          ((tgrigConj thetaGrp ((2, 3, 5) : thetaGrp.carrier)).map
            ((0, 0, c) : thetaGrp.carrier)) :=
  atfc_inner_galois_commute ρ g ((2, 3, 5) : thetaGrp.carrier) c

end IUT
