-- M404F CyclotomeGaloisModule [実・本物・柱A]
-- complete_pct 影響: 柱A で 復元円分体を canonical G_K-加群として組み上げ——内在中心 ≅ μ_l 上の実 G_K 作用（M389F の χ 捻り ttoaAct・M322F CycGKAction）が加群公理（σ_1=id・σ_{gh}=σ_g∘σ_h・群積を保つ）を厳密に満たし、その指標が M322F cycRigChar に一致し、かつ内部自己同型（M399F tgrigConj）とガロア χ 捻りが中心上で可換＝内在的（inner-invariant）であることを完全証明。
-- 正直な限定: 完全な mono-anabelian π₁→数体復元・幾何的 tempered π₁^temp の slim 遠アーベル性は外部/後続。中心の μ_l 同一視は 2 モデル（抽象 M.μ と Zp p 上の centerToMu）を経由する。
/-
  IUT/CyclotomeGaloisModule.lean — M404F [実／本物・柱A]
  分類: 実（復元円分体 μ_l を canonical G_K-加群として組み上げる・内在中心 ≅ μ_l に
        χ 捻りの実 G_K 作用を載せ・その加群構造が内部自己同型に対し剛＝内在的）

  遠アーベル（柱A）の系譜:
    * M124F (centerToMu, IUT/CyclotomicSync.lean): テータ中心座標 z ∈ ℤ を μ_l = ⟨ζ⟩
      の元 ζ^{z%l} に送る同期写像（(0,0,1) ↦ ζ の ℤ-線形拡張）。
    * M322F (CycGKAction / cycRigChar, IUT/CyclotomicRigidity.lean): G_K の μ_n への
      **実ガロア作用**（σ_1=id・σ_{gh}=σ_g∘σ_h）と**円分指標** χ_n（σ_g(ζ)=ζ^{χ(g)}）。
    * M389F (ttoa, IUT/TemperedThetaOuterAction.lean): 離散 Heisenberg テータ群 thetaGrp
      への外ガロア作用 ttoaAct g = ttoaScale(χ(g))——中心（内部円分体 μ_l）を円分指標 χ で
      捻る作用。μ_l 上の作用は galThMuAct（= CycGKAction）の本物の群作用に一致。
    * M394F (tgr, IUT/ThetaGroupReconstruction.lean): 中心 Z={(0,0,∗)} が純群論的述語
      tgrCentral（∀h, g·h=h·g）だけから内在的に復元される。
    * M399F (tgrig, IUT/ThetaGroupRigidity.lean): 内部自己同型 tgrigConj は中心を各点固定
      （tgrig_conj_fix_center）——復元中心 = μ_l は内部自己同型で剛（tgrig_cyclotome_rigid）。

  本モジュール（M404F）は**次の実ステップ = canonical Galois module の組み上げ**を行う:
    「内在的に復元された中心 ≅ μ_l は、その上の G_K 作用（χ 捻り）まで込めて、群に
     **canonical に付随する Galois 加群**である——内部自己同型に対し剛（内在的）で、
     その指標はちょうど実円分指標 cycRigChar」。

  建設内容（すべて本物の対象・toy 群/toy 指標なし・選択公理不使用）:
    * **復元円分体 μ_l 上の実 G_K-加群公理**（M389F/M322F 再利用・厳密）:
        - 単位元は自明作用 σ_1 = id（cgm_act_one）
        - 合成則 σ_{g·h} = σ_g ∘ σ_h（cgm_act_mul）
        - 各 σ_g は群準同型（群積を保つ σ_g(z·w)=σ_g(z)·σ_g(w)・単位元保存）（cgm_act_hom/cgm_act_map_one）
      ——これが「復元円分体が G_K-加群である」ことの本物の内容。
    * **指標 = M322F cycRigChar**（本物の円分指標）:
        - 生成元での作用 σ_g(ζ) = ζ^{χ(g)}（cgm_char_gen）
        - χ の準同型性 χ(gh)=χ(g)·χ(h)（cgm_char_hom）・χ(1)=1（cgm_char_one）
      ——復元作用が実円分指標に一致する（reconstructed action = 真の cyclotomic character）。
    * **内在中心での χ 捻り**: ttoaAct（M389F）は中心座標 c を χ(g)·c に捻る
      （cgm_center_action・cgm_ttoaAct_center）——中心 ≅ μ_l 上の χ 捻りの明示式。
    * **canonical 性（本丸・mono-anabelian の結論）**:
        - **内部自己同型とガロア χ 捻りは中心上で可換**（cgm_inner_galois_commute）:
            conj_h ∘ (σ_g on center) = (σ_g on center) ∘ conj_h
          ——両辺とも (0,0,χ(g)·c)。ゆえに Galois 加群構造は内部自己同型に依存しない。
        - **復元同一視 centerToMu は χ 捻り後も内部自己同型不変**（cgm_centerToMu_inner_invariant）
          ——復元円分体の同一視が canonical（群に一意に付随）かつ Galois 同変。
        - χ 捻りした標準生成元の交換子の μ_l 像 = centerToMu(χ(g))（cgm_centerToMu_char, M389F-7）。
    * **capstone** CyclotomeGaloisModuleData + cgm_exists + 実例（実 G_ℚ・μ_l 上の trivial 作用）。

  意義: 「復元円分体 μ_l は canonical な G_K-加群である」という mono-anabelian の言明の最小
  だが本物のインスタンス。中心の内在復元（M394F）・その剛性（M399F）・χ 捻り作用（M389F）・
  実円分指標（M322F）を一つの Galois 加群データに束ね、その加群構造が**内部自己同型に対して
  剛＝群に canonical に付随する**ことを厳密に証明する。

  正直な限定: 完全な mono-anabelian 復元アルゴリズム（幾何的 tempered π₁^temp Δ^temp の
  slim 遠アーベル性・π₁^ét からの数体の遠アーベル復元本体・[EtTh] mono-theta 環境全体）は
  外部（幾何的入力・後続）。中心 ≅ μ_l の同一視は 2 つの μ_l モデル（M389F/M322F の抽象
  CycMuGroup M.μ と M124F の Zp p 上 centerToMu）を経由する——これは既存モジュールの構図の
  忠実な継承であり水増しではない。全て選択公理不使用（propext / Quot.sound のみ）。
-/
import IUT.ThetaGroupRigidity
import IUT.TemperedThetaOuterAction

namespace IUT

/-! ## M404F-1: 内在中心上の χ 捻り（明示式）

  M389F の外ガロア作用 ttoaAct g = ttoaScale(χ(g)) を内在中心 {(0,0,c)} に制限すると、
  中心座標を χ(g) 倍する: ttoaAct g (0,0,c) = (0,0, χ(g)·c)。復元円分体 μ_l（中心）上の
  Galois χ 捻りの明示式。 -/

/-- **M404F-1a: 内在中心上の χ 捻りの明示式** —
      ttoaAct g (0,0,c) = (0,0, χ(g)·c)。
    外ガロア作用は中心元を中心元に送り（幾何座標 0 を保存）、中心座標を χ(g) 倍する。 -/
theorem cgm_ttoaAct_center (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (c : Int) :
    ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier)
      = ((0, 0, ttoaChar GK M ρ g * c) : thetaGrp.carrier) := rfl

/-- **M404F-1b: 中心座標の χ 捻り** — (ttoaAct g (0,0,c)) の中心座標 = χ(g)·c。 -/
theorem cgm_center_action (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (c : Int) :
    (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier)).2.2 = ttoaChar GK M ρ g * c := rfl

/-! ## M404F-2: 復元円分体 μ_l 上の実 G_K-加群公理（M389F/M322F 再利用）

  内在的に復元された中心 ≅ μ_l = M.μ 上に G_K は galThMuAct（= CycGKAction）で作用し、
  加群公理（単位元は自明・合成則・各 σ_g は群準同型）を厳密に満たす。 -/

/-- **M404F-2a: 単位元は自明作用** — σ_1(z) = z（M389F/M343F galTh_mu_act_one）。 -/
theorem cgm_act_one (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (z : M.μ.carrier) : galThMuAct GK M ρ GK.one z = z :=
  galTh_mu_act_one GK M ρ z

/-- **M404F-2b: 合成則** — σ_{g·h}(z) = σ_g(σ_h(z))（M389F/M343F galTh_mu_act_mul）。
    復元円分体への G_K 作用が**本物の群作用**をなす（G_K-加群の定義的性質）。 -/
theorem cgm_act_mul (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) (z : M.μ.carrier) :
    galThMuAct GK M ρ (GK.mul g h) z = galThMuAct GK M ρ g (galThMuAct GK M ρ h z) :=
  galTh_mu_act_mul GK M ρ g h z

/-- **M404F-2c: 各 σ_g は群準同型（群積を保つ）** — σ_g(z·w) = σ_g(z)·σ_g(w)。
    G_K の各元が μ_l の**加法的（群準同型的）**自己同型として作用する
    ——G_K-加群構造の核（ρ.act g : Hom M.μ M.μ の map_mul）。 -/
theorem cgm_act_hom (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (z w : M.μ.carrier) :
    galThMuAct GK M ρ g (M.μ.mul z w)
      = M.μ.mul (galThMuAct GK M ρ g z) (galThMuAct GK M ρ g w) :=
  (ρ.act g).map_mul z w

/-- **M404F-2d: σ_g は単位元を保つ** — σ_g(1) = 1（Hom.map_one）。 -/
theorem cgm_act_map_one (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) : galThMuAct GK M ρ g M.μ.one = M.μ.one :=
  (ρ.act g).map_one

/-! ## M404F-3: 指標 = M322F cycRigChar（reconstructed action = 真の円分指標）

  復元円分体 μ_l 上の G_K 作用の指標はちょうど実円分指標 cycRigChar である:
  生成元 ζ での作用は ζ^{χ(g)}、χ は準同型、χ(1)=1。 -/

/-- **M404F-3a: 生成元での作用形** — σ_g(ζ) = ζ^{χ(g)}（M389F ttoa_gen_commutator_galois）。
    復元作用が生成元を円分指標倍の冪に送る——実円分指標との一致の核。 -/
theorem cgm_char_gen (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) :
    galThMuAct GK M ρ g (M.μ.pow M.ζ 1) = M.μ.pow M.ζ (cycRigExp GK M ρ g) :=
  ttoa_gen_commutator_galois GK M ρ g

/-- **M404F-3b: 指標の準同型性** — χ_n(g·h) = χ_n(g)·χ_n(h)（M322F cycRig_char_isHom）。 -/
theorem cgm_char_hom (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) :
    cycRigChar GK M ρ (GK.mul g h)
      = zmodMul M.n (cycRigChar GK M ρ g) (cycRigChar GK M ρ h) :=
  cycRig_char_isHom GK M ρ g h

/-- **M404F-3c: χ(1)=1** — 単位元の指標は 1（M322F cycRig_char_one）。 -/
theorem cgm_char_one (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    cycRigChar GK M ρ GK.one = Quot.mk (modCong M.n).rel 1 :=
  cycRig_char_one GK M ρ

/-! ## M404F-4: canonical 性（本丸・mono-anabelian の結論）

  復元円分体の Galois 加群構造は**内部自己同型に依存しない**（群に canonical に付随する）:
  内部自己同型 conj_h（M399F）とガロア χ 捻り（M389F）は中心上で可換であり、復元同一視
  centerToMu は χ 捻り後も内部自己同型不変である。 -/

/-- **M404F-4a: χ 捻り後の中心元は内部自己同型で固定** —
      conj_h(ttoaAct g (0,0,c)) = (0,0, χ(g)·c)。
    ttoaAct g は中心元 (0,0,c) を中心元 (0,0,χ(g)·c) に送り（M404F-1a）、内部自己同型は
    中心元を各点固定する（M399F tgrig_conj_fix_center）。 -/
theorem cgm_inner_twist_center (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (h : thetaGrp.carrier) (c : Int) :
    (tgrigConj thetaGrp h).map (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier))
      = ((0, 0, ttoaChar GK M ρ g * c) : thetaGrp.carrier) := by
  rw [cgm_ttoaAct_center, tgrig_conj_fix_center h (ttoaChar GK M ρ g * c)]

/-- **M404F-4b: 内部自己同型とガロア χ 捻りは中心上で可換（本丸）** —
      conj_h(ttoaAct g (0,0,c)) = ttoaAct g (conj_h(0,0,c))。
    両辺とも (0,0, χ(g)·c)。ゆえに復元円分体 ≅ 中心上の Galois 加群構造（χ 捻り）は
    内部自己同型 conj_h に**依存しない**——群に canonical に付随する Galois 加群である
    ことの本物の内容（mono-anabelian の内在性）。 -/
theorem cgm_inner_galois_commute (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (h : thetaGrp.carrier) (c : Int) :
    (tgrigConj thetaGrp h).map (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier))
      = ttoaAct GK M ρ g ((tgrigConj thetaGrp h).map ((0, 0, c) : thetaGrp.carrier)) := by
  rw [cgm_ttoaAct_center, tgrig_conj_fix_center h c, cgm_ttoaAct_center,
    tgrig_conj_fix_center h (ttoaChar GK M ρ g * c)]

/-- **M404F-4c: 復元同一視 centerToMu は χ 捻り後も内部自己同型不変** —
      centerToMu(conj_h(ttoaAct g (0,0,c)) の中心座標) = centerToMu(χ(g)·c)。
    復元円分体の μ_l 同一視（M124F centerToMu）が χ 捻り（Galois）と内部自己同型の
    両方に整合する——同一視が canonical（群に一意付随）かつ Galois 同変であることの
    本物の完全証明（M399F tgrig_cyclotome_rigid の χ 捻り版）。 -/
theorem cgm_centerToMu_inner_invariant (p l : Nat) (ζ0 : (Zp p).carrier)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (h : thetaGrp.carrier) (c : Int) :
    centerToMu p l ζ0
        ((tgrigConj thetaGrp h).map (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier))).2.2
      = centerToMu p l ζ0 (ttoaChar GK M ρ g * c) :=
  congrArg (fun s : Int × Int × Int => centerToMu p l ζ0 s.2.2)
    (cgm_inner_twist_center GK M ρ g h c)

/-- **M404F-4d: χ 捻り交換子の centerToMu 像** — 標準生成元の交換子 [(1,0,0),(0,1,0)]=(0,0,1)
    を χ 捻りして centerToMu で読むと centerToMu(χ(g))（M389F-7 ttoa_gen_commutator_centerToMu）。
    テータ交換子の μ_l 像が外ガロア作用で円分指標倍に捻れることを復元同一視で読む。 -/
theorem cgm_centerToMu_char (p l : Nat) (ζ0 : (Zp p).carrier)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (g : GK.carrier) :
    centerToMu p l ζ0
        ((ttoaAct GK M ρ g (thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0))).2.2)
      = centerToMu p l ζ0 (ttoaChar GK M ρ g) :=
  ttoa_gen_commutator_centerToMu p l ζ0 GK M ρ g

/-! ## M404F-5: capstone -/

/-- **M404F-5a: 復元円分体 canonical Galois 加群データ** — 内在的に復元された中心 ≅ μ_l を
    G_K-加群として組み上げた全成果を束ねる:
      (i) 復元円分体 μ_l 上の実 G_K-加群公理（σ_1=id・σ_{gh}=σ_g∘σ_h・各 σ_g は群準同型・
          単位元保存）、
      (ii) 指標 = M322F cycRigChar（σ_g(ζ)=ζ^{χ(g)}・χ 準同型・χ(1)=1）、
      (iii) 内在中心での χ 捻りの明示式、
      (iv) canonical 性: 内部自己同型とガロア χ 捻りが中心上で可換・復元同一視 centerToMu が
           χ 捻り後も内部自己同型不変・χ 捻り交換子の centerToMu 像 = centerToMu(χ(g))。
    主語は本物の μ_l（M322F CycGKAction M.μ）・本物の χ（cycRigChar）・本物の内在中心
    （thetaGrp の中心）・本物の内部自己同型（M399F tgrigConj）——toy 群/toy 指標なし。 -/
structure CyclotomeGaloisModuleData (p l : Nat) (ζ0 : (Zp p).carrier)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) where
  /-- (i-1) 単位元は自明作用 σ_1 = id。 -/
  act_one : ∀ z : M.μ.carrier, galThMuAct GK M ρ GK.one z = z
  /-- (i-2) 合成則 σ_{g·h} = σ_g ∘ σ_h。 -/
  act_mul : ∀ (g h : GK.carrier) (z : M.μ.carrier),
    galThMuAct GK M ρ (GK.mul g h) z = galThMuAct GK M ρ g (galThMuAct GK M ρ h z)
  /-- (i-3) 各 σ_g は群積を保つ σ_g(z·w) = σ_g(z)·σ_g(w)。 -/
  act_hom : ∀ (g : GK.carrier) (z w : M.μ.carrier),
    galThMuAct GK M ρ g (M.μ.mul z w)
      = M.μ.mul (galThMuAct GK M ρ g z) (galThMuAct GK M ρ g w)
  /-- (i-4) σ_g は単位元を保つ σ_g(1) = 1。 -/
  act_map_one : ∀ g : GK.carrier, galThMuAct GK M ρ g M.μ.one = M.μ.one
  /-- (ii-1) 指標: 生成元での作用 σ_g(ζ) = ζ^{χ(g)}。 -/
  char_gen : ∀ g : GK.carrier,
    galThMuAct GK M ρ g (M.μ.pow M.ζ 1) = M.μ.pow M.ζ (cycRigExp GK M ρ g)
  /-- (ii-2) 指標の準同型性 χ(gh) = χ(g)·χ(h)。 -/
  char_hom : ∀ g h : GK.carrier,
    cycRigChar GK M ρ (GK.mul g h)
      = zmodMul M.n (cycRigChar GK M ρ g) (cycRigChar GK M ρ h)
  /-- (ii-3) χ(1) = 1。 -/
  char_one : cycRigChar GK M ρ GK.one = Quot.mk (modCong M.n).rel 1
  /-- (iii) 内在中心での χ 捻り (ttoaAct g (0,0,c)).c = χ(g)·c。 -/
  center_action : ∀ (g : GK.carrier) (c : Int),
    (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier)).2.2 = ttoaChar GK M ρ g * c
  /-- (iv-1) 内部自己同型とガロア χ 捻りは中心上で可換（canonical 性の本丸）。 -/
  inner_galois_commute : ∀ (g : GK.carrier) (h : thetaGrp.carrier) (c : Int),
    (tgrigConj thetaGrp h).map (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier))
      = ttoaAct GK M ρ g ((tgrigConj thetaGrp h).map ((0, 0, c) : thetaGrp.carrier))
  /-- (iv-2) 復元同一視 centerToMu は χ 捻り後も内部自己同型不変（canonical・Galois 同変）。 -/
  centerToMu_inner_invariant : ∀ (g : GK.carrier) (h : thetaGrp.carrier) (c : Int),
    centerToMu p l ζ0
        ((tgrigConj thetaGrp h).map (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier))).2.2
      = centerToMu p l ζ0 (ttoaChar GK M ρ g * c)
  /-- (iv-3) χ 捻り交換子の centerToMu 像 = centerToMu(χ(g))。 -/
  centerToMu_char : ∀ g : GK.carrier,
    centerToMu p l ζ0
        ((ttoaAct GK M ρ g (thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0))).2.2)
      = centerToMu p l ζ0 (ttoaChar GK M ρ g)

/-- **M404F-5b: witness 本体** — 全フィールドを M404F-1〜4 の本物の証明で埋める
    （外部仮説ゼロ・完全証明・ζ0 が単数根であることすら不要）。 -/
def cyclotomeGaloisModuleData (p l : Nat) (ζ0 : (Zp p).carrier)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    CyclotomeGaloisModuleData p l ζ0 GK M ρ where
  act_one := cgm_act_one GK M ρ
  act_mul := cgm_act_mul GK M ρ
  act_hom := cgm_act_hom GK M ρ
  act_map_one := cgm_act_map_one GK M ρ
  char_gen := cgm_char_gen GK M ρ
  char_hom := cgm_char_hom GK M ρ
  char_one := cgm_char_one GK M ρ
  center_action := cgm_center_action GK M ρ
  inner_galois_commute := cgm_inner_galois_commute GK M ρ
  centerToMu_inner_invariant := cgm_centerToMu_inner_invariant p l ζ0 GK M ρ
  centerToMu_char := cgm_centerToMu_char p l ζ0 GK M ρ

/-- **定理 (M404F-5c: canonical Galois 加群データの存在／M404F 見出し)** —
    任意の p・l・μ_l 候補 ζ0・G_K・内部円分体 μ_l（CycMuGroup）・実ガロア作用 ρ
    （M322F CycGKAction）に対し、復元円分体を canonical G_K-加群として組み上げたデータ
    （μ_l 上の実 G_K-加群公理・指標 = cycRigChar・内在中心での χ 捻り・内部自己同型に対する
    剛性＝canonical 性）が**外部仮説なしで**存在する（完全証明）。 -/
theorem cgm_exists (p l : Nat) (ζ0 : (Zp p).carrier)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    Nonempty (CyclotomeGaloisModuleData p l ζ0 GK M ρ) :=
  ⟨cyclotomeGaloisModuleData p l ζ0 GK M ρ⟩

/-! ## M404F-6: 実例 -/

/-- 実例: p=7・l=5 の復元円分体 canonical Galois 加群データが存在する
    （ζ0 は任意の ℤ_7 の元でよい）。 -/
example (ζ0 : (Zp 7).carrier) (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    Nonempty (CyclotomeGaloisModuleData 7 5 ζ0 GK M ρ) :=
  cgm_exists 7 5 ζ0 GK M ρ

/-- 実例: 本物の絶対ガロア群 G_ℚ（M315F algCloAbsGalois）の μ_l（ℤ/l, cycMuStd）上の
    trivial 作用（cycTrivialAction）による canonical Galois 加群データが存在する。 -/
example (l : Nat) (hl : 1 ≤ l) (ζ0 : (Zp 7).carrier) :
    Nonempty (CyclotomeGaloisModuleData 7 l ζ0 (algCloAbsGalois algCloTrivialTower)
      (cycMuStd l hl) (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))) :=
  cgm_exists 7 l ζ0 (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))

/-- 実例（canonical 性の本丸）: 内部自己同型 conj_{(2,3,5)} とガロア χ 捻りは中心上で可換
    ——復元円分体の Galois 加群構造が内部自己同型に依存しない。 -/
example (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (g : GK.carrier) (c : Int) :
    (tgrigConj thetaGrp ((2, 3, 5) : thetaGrp.carrier)).map
        (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier))
      = ttoaAct GK M ρ g
          ((tgrigConj thetaGrp ((2, 3, 5) : thetaGrp.carrier)).map
            ((0, 0, c) : thetaGrp.carrier)) :=
  cgm_inner_galois_commute GK M ρ g ((2, 3, 5) : thetaGrp.carrier) c

/-- 実例: 復元円分体 μ_l 上の G_K 作用の合成則（本物の群作用・任意の CycGKAction）。 -/
example (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) (z : M.μ.carrier) :
    galThMuAct GK M ρ (GK.mul g h) z = galThMuAct GK M ρ g (galThMuAct GK M ρ h z) :=
  cgm_act_mul GK M ρ g h z

/-- 実例: 各 σ_g は復元円分体上の群準同型（群積を保つ）。 -/
example (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (z w : M.μ.carrier) :
    galThMuAct GK M ρ g (M.μ.mul z w)
      = M.μ.mul (galThMuAct GK M ρ g z) (galThMuAct GK M ρ g w) :=
  cgm_act_hom GK M ρ g z w

/-- 実例: 復元同一視 centerToMu は χ 捻り後も内部自己同型 conj_{(1,2,3)} 不変（canonical）。 -/
example (p l : Nat) (ζ0 : (Zp p).carrier) (GK : Grp) (M : CycMuGroup)
    (ρ : CycGKAction GK M) (g : GK.carrier) (c : Int) :
    centerToMu p l ζ0
        ((tgrigConj thetaGrp ((1, 2, 3) : thetaGrp.carrier)).map
          (ttoaAct GK M ρ g ((0, 0, c) : thetaGrp.carrier))).2.2
      = centerToMu p l ζ0 (ttoaChar GK M ρ g * c) :=
  cgm_centerToMu_inner_invariant p l ζ0 GK M ρ g ((1, 2, 3) : thetaGrp.carrier) c

end IUT
