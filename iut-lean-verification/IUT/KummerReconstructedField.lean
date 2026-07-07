-- M419F KummerReconstructedField [実・本物・柱A]
-- complete_pct 影響: 柱A で 復元体 K 上の実 Kummer 指標 κ_α(σ)=σ(α)/α（M349F）を、M404F の canonical 円分体 μ_n=M.μ（内在中心の復元・内部自己同型剛・実円分指標 cycRigChar）を係数加群として据え、Kummer 類が canonical（内在的・inner-invariant な）円分体に付随する準同型として値を取ることを本物で束ねる（M349F+M404F+M409F の実対象を「復元体上の canonical-係数 Kummer 理論」に結ぶ binding）。
-- 正直な限定: 完全な mono-anabelian π₁^ét→数体復元アルゴリズムは外部/後続。n 乗根の存在 hfix・μ_n⊆K の自明作用 htriv・係数同一視 φ:μ_n⊆K^× → M.μ は明示の外部仮説として受け、決して自前で導出しない。
/-
  IUT/KummerReconstructedField.lean — M419F [実／本物・柱A]
  分類: 実（本物の対象の上での binding: M349F 実 Kummer 指標 κ:G_K→μ_n を、M404F canonical
        円分体 μ_n=M.μ を係数加群として据え、M409F/M329F 復元体 K の上で「canonical-係数の
        Kummer 理論」として組み上げる。主語はすべて本物: 本物の体 K（M264F）・本物の乗法群
        K^×（M309F tateMultGroup）・本物の絶対ガロア群モデル fieldAutGroup K（M271F）・本物の
        canonical 円分体 M.μ とその実 G_K-加群作用（M322F CycGKAction／M404F cgm）。toy 群/toy 指標なし）

  遠アーベル（柱A）の系譜と本モジュールの位置:
    * M320F (KummerTheory, kum): n 乗写像・商 K^×/(K^×)ⁿ・Kummer 写像 σ↦σ(r)/r の 1-コサイクル則。
    * M349F (KummerCharReal, kcr): 実 Kummer 指標 κ_α(σ)=σ(α)/α∈μ_n を本物で構成——1-コサイクル則・
      μ_n⊆K での準同型 kcrHomMu:G_K→μ_n・根の取替コバウンダリ（[κ]∈H¹ well-defined）・単射方向。
      `kcrGalThKappa` は係数同一視 φ:μ_n⊆K^× → M.μ を通じて κ を **canonical 円分体 M.μ 値**へ移す。
    * M345F (KummerExact, kex): 抽象 δ:K^×→H¹(G_K,μ_n)=Z¹/B¹・第一同型 K^×/ker(δ)≅im(δ)・単射性。
    * M404F (CyclotomeGaloisModule, cgm): 内在的に復元された中心 ≅ μ_l を、その上の χ 捻り G_K 作用
      まで込めて **canonical な G_K-加群**として組み上げ、指標がちょうど実円分指標 cycRigChar、かつ
      内部自己同型に対し剛（inner-invariant）であることを完全証明した。
    * M409F (AbsTopFieldFromCyclotome, atfc): M329F 体復元（復元環＝元の体 K）を M404F canonical
      円分体に結ぶ橋——体復元を養う χ = cycRigChar が canonical 円分体の指標そのもの。

  本モジュール（M419F）が本物で閉じる **binding**（すべて本物の対象・選択公理不使用）:
    Kummer 写像 δ:K^×/(K^×)ⁿ → H¹(G_K,μ_n) は μ_n を**係数加群**とする。本モジュールは、その係数
    μ_n を **M404F の canonical 円分体 M.μ**（内在中心の復元・実円分指標 cycRigChar・内部自己同型剛）
    に据える。すなわち復元体 K 上の Kummer 類は、canonical（群論的に内在的・inner-invariant）な
    円分体を係数として **canonical に付随**する。具体的に:
      * M419F-1: canonical 円分体 M.μ を係数加群として（G_K=fieldAutGroup K 上の M404F cgm 再輸出:
                 実 G_K-加群公理・生成元作用 σ_g(ζ)=ζ^{χ(g)}・χ=cycRigChar・内部自己同型剛）。
      * M419F-2: 実 Kummer 指標を canonical 円分体 M.μ 値へ（M349F kcrGalThKappa）——μ_n⊆K の
                 自明作用下で κ:G_K→M.μ は**本物の群準同型**（Kummer 類が M.μ で加法的）。
      * M419F-3: Kummer 類の値 κ(σ)=φ(κ_α(σ))——係数 μ_n=M.μ に landing する Kummer コサイクル。
      * M419F-4: canonical 性——係数円分体は内部自己同型に対し剛（M404F cgm_inner_galois_commute・
                 centerToMu 内部不変）。Kummer 類が内在的な円分体に付随する。
      * M419F-5: 復元体 = 元の体（M409F/M329F absF: 加法一致・乗法一致）。
      * M419F-6: capstone `KummerReconstructedFieldData` + `krf_toData` + `krf_exists`。
      * M419F-7: 実例。

  意義: M345F kex は係数を抽象 μ_n 加群 A（自明模型）で受けていた。M419F は復元体 K 上の Kummer 類の
  係数を **M404F の本物の canonical 円分体（中心の内在復元・その剛性・χ 捻り作用・実円分指標を束ねた
  本物）**に据え、「Kummer 類は係数として canonical（内在的）な円分体に付随する」という遠アーベルの
  結び目を復元体の上で本物で述べる。既存の本物の断片（M349F 実 Kummer 指標・M404F canonical 円分体・
  M409F 復元体）を「復元体上の canonical-係数 Kummer 理論」に結ぶ binding であり、新規のコア数学を
  積むのではなく、主語をすべて本物に保った正直な束ね（promotion/binding）である。

  正直な限定（消去弱化禁止）: 完全な mono-anabelian 復元アルゴリズム（幾何的 tempered π₁^temp の
  slim 遠アーベル性・π₁^ét から数体を抽出する完全アルゴリズム・[EtTh] mono-theta 環境全体）は
  外部（幾何的入力・後続）。n 乗根 α（α^n=a）の存在 `hfix`・μ_n⊆K での自明作用 `htriv`・係数同一視
  φ:μ_n⊆K^× → M.μ は M349F 準拠の**明示の外部仮説**として受け、決して自前で導出しない。中心 ≅ μ_l の
  同一視は既存 2 モデル（抽象 M.μ と Zp p 上 centerToMu）を経由する既存構図の忠実な継承。全て選択公理
  不使用（新規 Classical.choice なし・propext / Quot.sound のみ）。
-/
import IUT.KummerCharReal
import IUT.AbsTopFieldFromCyclotome

namespace IUT

/-! ## M419F-1: canonical 円分体 M.μ を係数加群として（G_K = fieldAutGroup K 上の M404F cgm 再輸出）

  復元体 K の絶対ガロア群モデル `fieldAutGroup K` を G_K として、M404F の canonical 円分体
  G_K-加群 M.μ（実 G_K-加群公理・実円分指標 cycRigChar・内部自己同型剛）を Kummer 類の**係数加群**
  として据える。 -/

/-- **M419F-1a: 係数の実 G_K-加群作用（合成則）** — canonical 円分体 M.μ 上の G_K=fieldAutGroup K
    作用は本物の群作用 σ_{g·h}=σ_g∘σ_h（M404F cgm_act_mul）。Kummer 類の係数が本物の G_K-加群である核。 -/
theorem krf_coeff_act_mul (K : IUTField) (M : CycMuGroup)
    (ρ : CycGKAction (fieldAutGroup K) M) (g h : (fieldAutGroup K).carrier) (z : M.μ.carrier) :
    galThMuAct (fieldAutGroup K) M ρ ((fieldAutGroup K).mul g h) z
      = galThMuAct (fieldAutGroup K) M ρ g (galThMuAct (fieldAutGroup K) M ρ h z) :=
  cgm_act_mul (fieldAutGroup K) M ρ g h z

/-- **M419F-1b: 係数作用は各 σ_g が群準同型** — σ_g(z·w)=σ_g(z)·σ_g(w)（M404F cgm_act_hom）。 -/
theorem krf_coeff_act_hom (K : IUTField) (M : CycMuGroup)
    (ρ : CycGKAction (fieldAutGroup K) M) (g : (fieldAutGroup K).carrier) (z w : M.μ.carrier) :
    galThMuAct (fieldAutGroup K) M ρ g (M.μ.mul z w)
      = M.μ.mul (galThMuAct (fieldAutGroup K) M ρ g z) (galThMuAct (fieldAutGroup K) M ρ g w) :=
  cgm_act_hom (fieldAutGroup K) M ρ g z w

/-- **M419F-1c: 係数円分体の生成元作用 σ_g(ζ)=ζ^{χ(g)}**（M404F cgm_char_gen）——Kummer 類の
    係数 μ_n=M.μ の生成元が canonical 実円分指標 χ で捻れる。「Kummer 類は canonical な χ の
    円分体を係数に持つ」ことの核。 -/
theorem krf_coeff_char_gen (K : IUTField) (M : CycMuGroup)
    (ρ : CycGKAction (fieldAutGroup K) M) (g : (fieldAutGroup K).carrier) :
    galThMuAct (fieldAutGroup K) M ρ g (M.μ.pow M.ζ 1) = M.μ.pow M.ζ (cycRigExp (fieldAutGroup K) M ρ g) :=
  cgm_char_gen (fieldAutGroup K) M ρ g

/-- **M419F-1d: 係数の指標は canonical 実円分指標 cycRigChar（準同型性）**（M404F cgm_char_hom）。 -/
theorem krf_coeff_char_hom (K : IUTField) (M : CycMuGroup)
    (ρ : CycGKAction (fieldAutGroup K) M) (g h : (fieldAutGroup K).carrier) :
    cycRigChar (fieldAutGroup K) M ρ ((fieldAutGroup K).mul g h)
      = zmodMul M.n (cycRigChar (fieldAutGroup K) M ρ g) (cycRigChar (fieldAutGroup K) M ρ h) :=
  cgm_char_hom (fieldAutGroup K) M ρ g h

/-- **M419F-1e: χ(1)=1**（M404F cgm_char_one）。 -/
theorem krf_coeff_char_one (K : IUTField) (M : CycMuGroup)
    (ρ : CycGKAction (fieldAutGroup K) M) :
    cycRigChar (fieldAutGroup K) M ρ (fieldAutGroup K).one = Quot.mk (modCong M.n).rel 1 :=
  cgm_char_one (fieldAutGroup K) M ρ

/-! ## M419F-2: 実 Kummer 指標を canonical 円分体 M.μ 値へ（M349F kcrGalThKappa）

  M349F の実 Kummer 準同型 kcrHomMu:G_K→μ_n（μ_n⊆K の自明作用下で本物の群準同型）を、係数同一視
  φ:μ_n⊆K^× → M.μ を通じて **canonical 円分体 M.μ 値**の Kummer 指標 κ:G_K→M.μ へ移す。 -/

/-- **M419F-2a: canonical 円分体値の Kummer 指標** — 実 Kummer 準同型 kcrHomMu（M349F, n 乗根 α・
    a=α^n が G_K-固定 `hfix`・μ_n⊆K の自明作用 `htriv`）を係数同一視 φ:μ_n⊆K^× → M.μ と合成し、
    復元体 K の絶対ガロア群 fieldAutGroup K から **canonical 円分体 M.μ への本物の群準同型**を得る。
    Kummer 類が canonical な円分体を係数に持つことの本体（M349F kcrGalThKappa を主語に据える）。 -/
def krfKappa (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (M : CycMuGroup)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ) :
    Hom (fieldAutGroup K) M.μ :=
  kcrGalThKappa K n r hfix htriv M φ

/-- **M419F-2b: Kummer 類は canonical 係数で加法的（本物の準同型則）** — κ(στ)=κ(σ)·κ(τ) が
    canonical 円分体 M.μ の積で成立する（Hom.comp の map_mul）。μ_n⊆K の自明作用下で、復元体上の
    Kummer 類が canonical な円分体を係数に持つ**準同型**であることの本物の内容。 -/
theorem krf_kappa_map_mul (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (M : CycMuGroup)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ) (σ τ : FieldAut K) :
    (krfKappa K n r hfix htriv M φ).map ((fieldAutGroup K).mul σ τ)
      = M.μ.mul ((krfKappa K n r hfix htriv M φ).map σ) ((krfKappa K n r hfix htriv M φ).map τ) :=
  (krfKappa K n r hfix htriv M φ).map_mul σ τ

/-- **M419F-2c: 単位元の Kummer 類は自明** — κ(1)=1（Hom.map_one）。 -/
theorem krf_kappa_map_one (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (M : CycMuGroup)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ) :
    (krfKappa K n r hfix htriv M φ).map (fieldAutGroup K).one = M.μ.one :=
  (krfKappa K n r hfix htriv M φ).map_one

/-! ## M419F-3: Kummer 類の値 κ(σ) = φ(κ_α(σ))（係数 μ_n=M.μ に landing する Kummer コサイクル） -/

/-- **M419F-3a: Kummer 類の値** — κ(σ) = φ(κ_α(σ))。復元体上の Kummer コサイクル
    κ_α(σ)=σ(α)/α∈μ_n（M349F kcrChar）を係数同一視 φ で canonical 円分体 M.μ に写した値。
    Kummer 類が μ_n=M.μ に landing していることの明示。 -/
theorem krf_kappa_val (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (M : CycMuGroup)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ) (σ : FieldAut K) :
    (krfKappa K n r hfix htriv M φ).map σ
      = φ.map ⟨kcrChar K r σ, kcr_mem_mu K n r σ (hfix σ)⟩ :=
  rfl

/-- **M419F-3b: Kummer 類の 1-コサイクル則（M349F kcr_cocycle）** — 係数へ写す前の Kummer コサイクル
    κ_α(στ)=κ_α(σ)·σ(κ_α(τ)) は本物の crossed homomorphism（M349F 再輸出）。μ_n⊆K の自明作用下で
    これが M419F-2b の M.μ 値準同型に降りる。 -/
theorem krf_kummer_cocycle (K : IUTField) (r : (tateMultGroup K).carrier)
    (σ τ : FieldAut K) :
    kcrChar K r ((fieldAutGroup K).mul σ τ)
      = (tateMultGroup K).mul (kcrChar K r σ) (kummerUnitAct K σ (kcrChar K r τ)) :=
  kcr_cocycle K r σ τ

/-! ## M419F-4: canonical 性 — 係数円分体は内部自己同型に対し剛（M404F 内在性）

  Kummer 類の係数 M.μ（canonical 円分体）の Galois χ 捻りは内部自己同型と可換であり、復元同一視
  centerToMu は χ 捻り後も内部自己同型不変。ゆえに Kummer 類は inner-automorphism-canonical な
  （群論的に内在的な）円分体に付随する。 -/

/-- **M419F-4a: 内部自己同型とガロア χ 捻りは中心上で可換（M404F cgm_inner_galois_commute）** —
    Kummer 類の係数円分体の Galois 加群構造は内部自己同型に依存しない（canonical 性の本丸）。 -/
theorem krf_coeff_inner_galois_commute (K : IUTField) (M : CycMuGroup)
    (ρ : CycGKAction (fieldAutGroup K) M) (g : (fieldAutGroup K).carrier)
    (h : thetaGrp.carrier) (c : Int) :
    (tgrigConj thetaGrp h).map (ttoaAct (fieldAutGroup K) M ρ g ((0, 0, c) : thetaGrp.carrier))
      = ttoaAct (fieldAutGroup K) M ρ g ((tgrigConj thetaGrp h).map ((0, 0, c) : thetaGrp.carrier)) :=
  cgm_inner_galois_commute (fieldAutGroup K) M ρ g h c

/-- **M419F-4b: 復元同一視 centerToMu は χ 捻り後も内部自己同型不変（M404F cgm_centerToMu_inner_invariant）**
    ——Kummer 類の係数円分体の同一視が canonical（群に一意付随）かつ Galois 同変。 -/
theorem krf_coeff_centerToMu_inner_invariant (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) (M : CycMuGroup) (ρ : CycGKAction (fieldAutGroup K) M)
    (g : (fieldAutGroup K).carrier) (h : thetaGrp.carrier) (c : Int) :
    centerToMu p l ζ0
        ((tgrigConj thetaGrp h).map (ttoaAct (fieldAutGroup K) M ρ g ((0, 0, c) : thetaGrp.carrier))).2.2
      = centerToMu p l ζ0 (ttoaChar (fieldAutGroup K) M ρ g * c) :=
  cgm_centerToMu_inner_invariant p l ζ0 (fieldAutGroup K) M ρ g h c

/-! ## M419F-5: 復元体 = 元の体（M409F/M329F absF 再利用） -/

/-- **M419F-5a: 復元加法 = 元の体加法（M329F absF_add_eq）** — Kummer 類が住む復元体は元の体 K に一致。 -/
theorem krf_field_add_eq (K : IUTField) [DecidableEq K.carrier] (x y : K.carrier) :
    (absFRecoveredRing K).add x y = K.add x y :=
  absF_add_eq K x y

/-- **M419F-5b: 復元乗法 = 元の体乗法**（定義的一致）。 -/
theorem krf_field_mul_eq (K : IUTField) [DecidableEq K.carrier] :
    (absFRecoveredRing K).mul = K.mul := rfl

/-! ## M419F-6: capstone — 復元体上の canonical-係数 Kummer 理論 -/

/-- **M419F-6a: 復元体上の canonical-係数 Kummer 理論データ** — 復元体 K（M409F/M329F）の上で、
    M404F canonical 円分体 M.μ（実 G_K-加群・実円分指標 cycRigChar・内部自己同型剛）を係数加群とし、
    M349F 実 Kummer 指標を M.μ 値へ移した κ:G_K→M.μ を主役に、以下を束ねる:
      (i)   Kummer 指標 κ:fieldAutGroup K → M.μ（μ_n⊆K の自明作用下の本物の群準同型）、
      (ii)  κ の準同型則 κ(στ)=κ(σ)·κ(τ)・κ(1)=1（Kummer 類が canonical 係数で加法的）、
      (iii) 係数円分体の生成元作用 σ_g(ζ)=ζ^{χ(g)}・χ=cycRigChar（canonical 実円分指標）、
      (iv)  canonical 性: 係数円分体は内部自己同型に対し剛（M404F 内在性）、
      (v)   復元体 = 元の体（加法・乗法とも一致）。
    主語はすべて本物: 本物の体 K・本物の乗法群 K^×・本物の絶対ガロア群 fieldAutGroup K・本物の
    canonical 円分体 M.μ とその実 G_K-加群作用・本物の内部自己同型（M399F tgrigConj）。toy なし。 -/
structure KummerReconstructedFieldData (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) [DecidableEq K.carrier] (n : Nat) (r : (tateMultGroup K).carrier)
    (M : CycMuGroup) (ρ : CycGKAction (fieldAutGroup K) M)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ) where
  /-- (i) canonical 円分体 M.μ 値の Kummer 指標 κ:fieldAutGroup K → M.μ。 -/
  kappa : Hom (fieldAutGroup K) M.μ
  /-- κ = M349F kcrGalThKappa を通じた canonical 係数の Kummer 指標。 -/
  is_kappa : ∀ hfix htriv, kappa = krfKappa K n r hfix htriv M φ
  /-- (ii-1) Kummer 類の準同型則 κ(στ)=κ(σ)·κ(τ)。 -/
  kappa_mul : ∀ σ τ : FieldAut K,
    kappa.map ((fieldAutGroup K).mul σ τ) = M.μ.mul (kappa.map σ) (kappa.map τ)
  /-- (ii-2) κ(1)=1。 -/
  kappa_one : kappa.map (fieldAutGroup K).one = M.μ.one
  /-- (iii-1) 係数円分体の生成元作用 σ_g(ζ)=ζ^{χ(g)}。 -/
  coeff_char_gen : ∀ g : (fieldAutGroup K).carrier,
    galThMuAct (fieldAutGroup K) M ρ g (M.μ.pow M.ζ 1)
      = M.μ.pow M.ζ (cycRigExp (fieldAutGroup K) M ρ g)
  /-- (iii-2) 係数の指標 = canonical 実円分指標 cycRigChar（準同型性）。 -/
  coeff_char_hom : ∀ g h : (fieldAutGroup K).carrier,
    cycRigChar (fieldAutGroup K) M ρ ((fieldAutGroup K).mul g h)
      = zmodMul M.n (cycRigChar (fieldAutGroup K) M ρ g) (cycRigChar (fieldAutGroup K) M ρ h)
  /-- (iv) canonical 性: 係数円分体は内部自己同型と中心上で可換（inner-invariant）。 -/
  coeff_inner_canonical : ∀ (g : (fieldAutGroup K).carrier) (h : thetaGrp.carrier) (c : Int),
    (tgrigConj thetaGrp h).map (ttoaAct (fieldAutGroup K) M ρ g ((0, 0, c) : thetaGrp.carrier))
      = ttoaAct (fieldAutGroup K) M ρ g ((tgrigConj thetaGrp h).map ((0, 0, c) : thetaGrp.carrier))
  /-- (v-1) 復元加法 = 元の体加法。 -/
  field_add_eq : ∀ x y : K.carrier, (absFRecoveredRing K).add x y = K.add x y
  /-- (v-2) 復元乗法 = 元の体乗法。 -/
  field_mul_eq : (absFRecoveredRing K).mul = K.mul

/-- **M419F-6b: witness 本体** — 全フィールドを M349F/M404F/M329F の本物の証明で埋める
    （外部仮説は n 乗根固定 hfix・自明作用 htriv・係数同一視 φ のみ・それ以外はゼロ）。 -/
def krf_toData (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) [DecidableEq K.carrier] (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (M : CycMuGroup) (ρ : CycGKAction (fieldAutGroup K) M)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ) :
    KummerReconstructedFieldData p l ζ0 K n r M ρ φ where
  kappa := krfKappa K n r hfix htriv M φ
  is_kappa := fun _ _ => rfl
  kappa_mul := krf_kappa_map_mul K n r hfix htriv M φ
  kappa_one := krf_kappa_map_one K n r hfix htriv M φ
  coeff_char_gen := krf_coeff_char_gen K M ρ
  coeff_char_hom := krf_coeff_char_hom K M ρ
  coeff_inner_canonical := krf_coeff_inner_galois_commute K M ρ
  field_add_eq := krf_field_add_eq K
  field_mul_eq := krf_field_mul_eq K

/-- **M419F-6c: capstone — 復元体上の canonical-係数 Kummer 理論の存在** — DecidableEq を持つ体 K・
    次数 n・n 乗根 α（固定 hfix・自明作用 htriv）・canonical 円分体 M とその実 G_K-加群作用 ρ・係数同一視
    φ から、復元体 K 上で M404F canonical 円分体 M.μ を係数とする Kummer 理論データ（Kummer 指標の
    準同型・係数の実円分指標 cycRigChar・係数の内部自己同型剛・復元体＝元の体）が存在する。
    「復元体上の Kummer 類は canonical（内在的）な円分体を係数に持つ」ことの本物の束ね
    （π₁^ét→数体の完全 mono-anabelian 抽出は外部）。 -/
theorem krf_exists (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) [DecidableEq K.carrier] (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (M : CycMuGroup) (ρ : CycGKAction (fieldAutGroup K) M)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ) :
    Nonempty (KummerReconstructedFieldData p l ζ0 K n r M ρ φ) :=
  ⟨krf_toData p l ζ0 K n r hfix htriv M ρ φ⟩

/-! ## M419F-7: 実例 -/

/-- 実例: α=1・n=2 の復元体上 canonical-係数 Kummer 理論データが存在（DecidableEq を持つ任意の体 K・
    任意の canonical 円分体 M とその作用 ρ・係数同一視 φ）。κ_1≡1 の基点で M349F 自明作用が成立する
    本物のインスタンス（ℚ^×/(ℚ^×)² の平方類を測る Kummer 指標の基点）。 -/
example (p l : Nat) (ζ0 : (Zp p).carrier) (K : IUTField) [DecidableEq K.carrier] (M : CycMuGroup)
    (ρ : CycGKAction (fieldAutGroup K) M)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K 2)) M.μ) :
    Nonempty (KummerReconstructedFieldData p l ζ0 K 2 (tateMultGroup K).one M ρ φ) :=
  krf_exists p l ζ0 K 2 (tateMultGroup K).one
    (kcr_one_fix K 2) (kcr_one_trivialAction K) M ρ φ

/-- 実例: 復元体上の Kummer 類は canonical 係数で加法的 κ(στ)=κ(σ)·κ(τ)（μ_n⊆K の自明作用下）。 -/
example (K : IUTField) (n : Nat) (r : (tateMultGroup K).carrier)
    (hfix : ∀ σ : FieldAut K, kummerUnitAct K σ (tateNpow (tateMultGroup K) r n)
            = tateNpow (tateMultGroup K) r n)
    (htriv : kcrTrivialAction K r) (M : CycMuGroup)
    (φ : Hom (subgroupGrp (tateTorMuSubgroup K n)) M.μ) (σ τ : FieldAut K) :
    (krfKappa K n r hfix htriv M φ).map ((fieldAutGroup K).mul σ τ)
      = M.μ.mul ((krfKappa K n r hfix htriv M φ).map σ) ((krfKappa K n r hfix htriv M φ).map τ) :=
  krf_kappa_map_mul K n r hfix htriv M φ σ τ

/-- 実例: Kummer 類の係数円分体は内部自己同型 conj_{(2,3,5)} に対し剛（inner-automorphism-canonical）。 -/
example (K : IUTField) (M : CycMuGroup) (ρ : CycGKAction (fieldAutGroup K) M)
    (g : (fieldAutGroup K).carrier) (c : Int) :
    (tgrigConj thetaGrp ((2, 3, 5) : thetaGrp.carrier)).map
        (ttoaAct (fieldAutGroup K) M ρ g ((0, 0, c) : thetaGrp.carrier))
      = ttoaAct (fieldAutGroup K) M ρ g
          ((tgrigConj thetaGrp ((2, 3, 5) : thetaGrp.carrier)).map ((0, 0, c) : thetaGrp.carrier)) :=
  krf_coeff_inner_galois_commute K M ρ g ((2, 3, 5) : thetaGrp.carrier) c

/-- 実例: Kummer 類の係数円分体の生成元は canonical 実円分指標 χ で捻れる σ_g(ζ)=ζ^{χ(g)}。 -/
example (K : IUTField) (M : CycMuGroup) (ρ : CycGKAction (fieldAutGroup K) M)
    (g : (fieldAutGroup K).carrier) :
    galThMuAct (fieldAutGroup K) M ρ g (M.μ.pow M.ζ 1) = M.μ.pow M.ζ (cycRigExp (fieldAutGroup K) M ρ g) :=
  krf_coeff_char_gen K M ρ g

end IUT
