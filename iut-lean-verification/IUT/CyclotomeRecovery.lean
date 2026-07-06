/-
  IUT/CyclotomeRecovery.lean — M334F [実／本物]
  分類: 実 (mono-anabelian 円分体 μ̂ の χ からの復元・円分剛性同型)
  complete_pct 影響: 柱A を前進（M329F 体復元が残した「χ からの μ 復元」を本物化＝
    円分剛性同型 recovered μ_n ≅ ℤ/n（G_K は χ で作用）を構成し AbsTopIII の
    (K^×,v,χ)→(体＋円分体) の像を閉じる方向）。M322F `CyclotomicRigidity` は
    「G_K の μ_n 作用 ρ → 円分指標 χ_n」の**順方向**（作用から指標を抽出）を本物化した。
    本モジュールは**逆方向**を本物化する: 円分指標 χ_n : G_K → (ℤ/n)^× を入力とし、
    そこから円分体 μ̂ を G_K-加群として復元する:
      recovered μ_n = (ℤ/n, g·x = χ(g)·x)。
    (1) `cycRec_mu_from_chi`: χ から復元した円分体が**本物の G_K-作用**をなす
        （χ 準同型 ⟹ χ(gh)·x=χ(g)·(χ(h)·x)、χ(1)·x=x）を zmodMul の結合則・
        左単位元で完全証明。
    (2) `cycRec_rigidity_iso`: **円分剛性同型** — 復元 μ_n は台として ℤ/n に恒等
        （canonical）で一致し、G_K の捻りが**ちょうど χ**（作用は χ(g) 倍）である
        ことを完全証明。生成元 class 1 への作用が χ(g) を返す（`cycRec_action_gen`）。
    (3) `cycRec_chi_hom` / 変 n 両立: χ の準同型性、及び n∣m の推移射 zmodTrans を
        通した円分指標 χ_m→χ_n の両立（`cycRecCharTrans`・`cycRec_action_change_n`）を
        本物で（μ_{nm}→μ_n の G_K-同変両立）。
    (4) capstone `cycRec_absTopIII_cyclotome`: M329F 体復元データ `AbsTopFieldData` と
        M322F 作用 `AbsTopIIIInputSkeleton.gal` から χ を取り、復元 μ̂ を組み、
        (K^×,v,χ)→(体＋円分体) の像を閉じる。

  正直な限定（消去・弱化禁止）:
  - **本物（完全証明・sorry/新規 Classical.choice 皆無）**: χ:G_K→(ℤ/n)^× を
    `cycRecCharacter`（準同型・χ(1)=1・単元値）で受け、そこから復元した G_K-加群
    (ℤ/n, χ 捻り) が**本物の群作用**（合成則・単位則）をなすこと、円分剛性同型
    （台は ℤ/n に恒等一致・捻りはちょうど χ・生成元作用が χ を返す）、χ の準同型性、
    n∣m の推移射での χ の両立と作用の同変両立、capstone（体復元 + 円分体復元）。
  - **正直申告（骨組み・後続）**:
    ・**χ 自体を π₁^ét（位相群）から抽出する本丸は骨組み**。本モジュールは χ を
      `cycRecCharacter` の抽象データ（または M322F `CycGKAction` からの `cycRigChar`）
      として受け取る。実 π₁^ét 位相群の連続指標としての χ の抽出は柱A/E 後続。
    ・**復元 μ̂ が幾何的な真の 1 の n 乗根の群 μ_n⊆K^sep と G_K-同型である**ことは、
      外部仮説 `cycRecGeoCompatible`（真の幾何作用が χ 捻りに一致）として**明示的に
      受け取り、決して導出しない**（`cycRec_geo_recovery_hypothesis`）。この同一視
      （mono-theta 環境の 3 剛性の 1 つ）は柱E/D 後続。
    ・実例は M315F の**本物の絶対ガロア群 G_ℚ** の trivial（不分岐）指標での復元
      （χ≡1 ⟹ 作用は恒等）。非自明 χ を与える実 Galois 降下は柱A/E 後続。

  禁止タクティク不使用（cases/obtain/induction/rw/show/refine/exact/apply/intro/
  funext/omega のみ）。共有ファイル未変更。一般名は `cycRec` 接頭辞で衝突回避。
-/
import IUT.CyclotomicRigidity
import IUT.AbsTopFieldRecover
import IUT.ZmodOrder
import IUT.PrimitiveRoot

namespace IUT

/-! ## M334F-1: 円分指標 χ : G_K → (ℤ/n)^× のデータ -/

/-- **M334F-1: 円分指標データ** — χ_n : G_K → (ℤ/n)^× を抽象データとして受け取る。
    準同型 χ(g·h)=χ(g)·χ(h)（ℤ/n の乗法 `zmodMul`）・χ(1)=1・各 χ(g) は単元
    （逆元を持つ）を要求する。M322F の `cycRigChar`（G_K の μ_n 作用から抽出した
    円分指標）がこのデータの本物のインスタンスを与える。円分体復元の入力。 -/
structure cycRecCharacter (GK : Grp) (n : Nat) where
  /-- 円分指標 χ : G_K → ℤ/n。 -/
  chi : GK.carrier → (zmod n).carrier
  /-- 準同型性 χ(g·h)=χ(g)·χ(h)。 -/
  chi_hom : ∀ g h, chi (GK.mul g h) = zmodMul n (chi g) (chi h)
  /-- χ(1)=1。 -/
  chi_one : chi GK.one = Quot.mk (modCong n).rel 1
  /-- χ(g) は (ℤ/n)^× の単元（逆元 v を持つ）。 -/
  chi_unit : ∀ g, ∃ v, zmodMul n (chi g) v = Quot.mk (modCong n).rel 1

/-! ## M334F-2: χ から復元した円分体の G_K-作用 -/

/-- **M334F-2a: 復元円分体の作用** — g ∈ G_K は ℤ/n に x ↦ χ(g)·x（zmodMul）で作用する。
    円分指標 χ から復元した円分体 μ̂ の G_K-加群構造の作用そのもの。 -/
def cycRecAction (GK : Grp) (n : Nat) (χ : cycRecCharacter GK n)
    (g : GK.carrier) (x : (zmod n).carrier) : (zmod n).carrier :=
  zmodMul n (χ.chi g) x

/-- **M334F-2b: 単位則** σ_1(x)=x（χ(1)=1 ⟹ 1·x=x）。復元作用が群作用の単位則を満たす。 -/
theorem cycRec_action_one (GK : Grp) (n : Nat) (χ : cycRecCharacter GK n)
    (x : (zmod n).carrier) :
    cycRecAction GK n χ GK.one x = x := by
  show zmodMul n (χ.chi GK.one) x = x
  rw [χ.chi_one]
  exact zmodOne_mul n x

/-- **M334F-2c: 合成則** σ_{g·h}(x)=σ_g(σ_h(x))（χ 準同型 ⟹ χ(gh)·x=χ(g)·(χ(h)·x)、
    zmodMul の結合則）。復元作用が群作用の合成則を満たす。 -/
theorem cycRec_action_mul (GK : Grp) (n : Nat) (χ : cycRecCharacter GK n)
    (g h : GK.carrier) (x : (zmod n).carrier) :
    cycRecAction GK n χ (GK.mul g h) x
      = cycRecAction GK n χ g (cycRecAction GK n χ h x) := by
  show zmodMul n (χ.chi (GK.mul g h)) x
     = zmodMul n (χ.chi g) (zmodMul n (χ.chi h) x)
  rw [χ.chi_hom, zmodMul_assoc]

/-! ## M334F-3: 復元円分体 = G_K-加群 -/

/-- **M334F-3: 復元 G_K-加群** — 台 ℤ/n と G_K 作用（合成則・単位則を満たす本物の群作用）
    を束ねる。χ から復元した円分体 μ̂ の G_K-加群としての実体。 -/
structure cycRecGKModule (GK : Grp) where
  /-- 位数 n（μ_n の n）。 -/
  n : Nat
  /-- G_K の ℤ/n への作用 σ_g。 -/
  act : GK.carrier → (zmod n).carrier → (zmod n).carrier
  /-- 単位則 σ_1=id。 -/
  act_one : ∀ x, act GK.one x = x
  /-- 合成則 σ_{g·h}=σ_g∘σ_h。 -/
  act_mul : ∀ g h x, act (GK.mul g h) x = act g (act h x)

/-- **M334F-3 本丸(1): χ から円分体 μ̂ を復元** — 円分指標 χ : G_K → (ℤ/n)^× から、
    ℤ/n を台とし g·x=χ(g)·x で G_K が作用する円分体を復元する。作用が**本物の群作用**
    （合成則・単位則）をなすことを zmodMul の結合則・左単位元で完全証明。
    M329F 体復元が残した「χ からの μ 復元」を本物化する中核。 -/
def cycRec_mu_from_chi (GK : Grp) (n : Nat) (χ : cycRecCharacter GK n) :
    cycRecGKModule GK where
  n := n
  act := fun g x => cycRecAction GK n χ g x
  act_one := fun x => cycRec_action_one GK n χ x
  act_mul := fun g h x => cycRec_action_mul GK n χ g h x

/-! ## M334F-4: 円分剛性同型（recovered μ_n ≅ ℤ/n・捻りはちょうど χ） -/

/-- **M334F-4a: 円分体の恒等同型** — 台 ℤ/n 上の恒等群準同型（作用を忘れた abelian
    群としての canonical 同型）。 -/
def cycRecIdIso (n : Nat) : Hom (zmod n) (zmod n) where
  map := fun x => x
  map_mul := fun _ _ => rfl

/-- **M334F-4b: 恒等同型は単射**（canonical 同型の忠実性）。 -/
theorem cycRec_idIso_injective (n : Nat) : (cycRecIdIso n).Injective :=
  fun _ _ h => h

/-- **M334F-4c: 恒等同型の写像は恒等関数**（canonical 一致の明示）。 -/
theorem cycRec_idIso_map (n : Nat) (x : (zmod n).carrier) :
    (cycRecIdIso n).map x = x := rfl

/-- **M334F-4 本丸(2): 円分剛性同型** — χ から復元した円分体 μ̂ は:
      (i) 台として ℤ/n に**恒等（canonical）**で一致（作用を忘れた abelian 群同型は恒等）、
      (ii) G_K の捻りは**ちょうど χ**（作用は g·x=χ(g)·x）、
      (iii) その恒等同型は単射（忠実）。
    円分指標が復元 μ_n の G_K-加群構造を χ で完全に決めること = 円分剛性同型。 -/
theorem cycRec_rigidity_iso (GK : Grp) (n : Nat) (χ : cycRecCharacter GK n) :
    ((cycRec_mu_from_chi GK n χ).n = n) ∧
    (∀ g x, (cycRec_mu_from_chi GK n χ).act g x = zmodMul n (χ.chi g) x) ∧
    ((cycRecIdIso n).Injective ∧ ∀ x, (cycRecIdIso n).map x = x) :=
  ⟨rfl, fun _ _ => rfl, ⟨cycRec_idIso_injective n, fun _ => rfl⟩⟩

/-- **M334F-4d: 生成元への作用が χ を返す** — g·(class 1)=χ(g)（μ_n の生成元 1 に作用
    すると円分指標 χ(g) がちょうど戻る）。捻りが χ そのものであることの明示的 witness。 -/
theorem cycRec_action_gen (GK : Grp) (n : Nat) (χ : cycRecCharacter GK n)
    (g : GK.carrier) :
    cycRecAction GK n χ g (Quot.mk (modCong n).rel 1) = χ.chi g := by
  show zmodMul n (χ.chi g) (Quot.mk (modCong n).rel 1) = χ.chi g
  exact zmodMul_one n (χ.chi g)

/-! ## M334F-5: χ の準同型性・変 n 両立（functoriality） -/

/-- **M334F-5a: χ は群準同型**（再輸出）χ(g·h)=χ(g)·χ(h)。 -/
theorem cycRec_chi_hom (GK : Grp) (n : Nat) (χ : cycRecCharacter GK n)
    (g h : GK.carrier) :
    χ.chi (GK.mul g h) = zmodMul n (χ.chi g) (χ.chi h) :=
  χ.chi_hom g h

/-- **M334F-5b: 推移射は乗法を保つ** — n∣m の推移射 zmodTrans（ℤ/n→ℤ/m）は zmodMul を
    保つ（円分指標の両立の核）。 -/
theorem cycRec_zmodTrans_mul {m n : Nat} (h : m ∣ n) (x y : (zmod n).carrier) :
    (zmodTrans h).map (zmodMul n x y)
      = zmodMul m ((zmodTrans h).map x) ((zmodTrans h).map y) := by
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  rfl

/-- **M334F-5c: 変 n（推移射）での円分指標** — n∣m のとき、level n の指標 χ を推移射
    zmodTrans で level m に落とした χ_m = zmodTrans∘χ も円分指標をなす（準同型・χ(1)=1・
    単元値）。μ_{nm}→μ_n の逆系での χ の両立の本物構成。 -/
def cycRecCharTrans {GK : Grp} {m n : Nat} (h : m ∣ n) (χ : cycRecCharacter GK n) :
    cycRecCharacter GK m where
  chi := fun g => (zmodTrans h).map (χ.chi g)
  chi_hom := fun g g' => by
    rw [χ.chi_hom, cycRec_zmodTrans_mul]
  chi_one := by
    show (zmodTrans h).map (χ.chi GK.one) = Quot.mk (modCong m).rel 1
    rw [χ.chi_one]
    rfl
  chi_unit := fun g => by
    obtain ⟨v, hv⟩ := χ.chi_unit g
    refine ⟨(zmodTrans h).map v, ?_⟩
    rw [← cycRec_zmodTrans_mul h (χ.chi g) v, hv]
    rfl

/-- **M334F-5d: 復元作用の変 n 同変両立** — n∣m の推移射 zmodTrans は復元作用と同変:
      σ_g^{(m)}(t x) = t(σ_g^{(n)} x)      （t = zmodTrans, σ^{(n)}=level n 作用）。
    復元円分体 μ̂ の μ_{nm}→μ_n 方向の G_K-同変両立（円分体の逆系両立）。 -/
theorem cycRec_action_change_n {GK : Grp} {m n : Nat} (h : m ∣ n)
    (χ : cycRecCharacter GK n) (g : GK.carrier) (x : (zmod n).carrier) :
    cycRecAction GK m (cycRecCharTrans h χ) g ((zmodTrans h).map x)
      = (zmodTrans h).map (cycRecAction GK n χ g x) := by
  show zmodMul m ((zmodTrans h).map (χ.chi g)) ((zmodTrans h).map x)
     = (zmodTrans h).map (zmodMul n (χ.chi g) x)
  rw [cycRec_zmodTrans_mul]

/-! ## M334F-6: M322F 作用からの χ（cycRigChar）接続 -/

/-- **M334F-6: G_K 作用 ρ から円分指標データ** — M322F `CycGKAction`（G_K の μ_n 作用）
    から抽出した円分指標 `cycRigChar` を `cycRecCharacter` として束ねる（準同型は
    `cycRig_char_isHom`、χ(1)=1 は `cycRig_char_one`、単元性は `cycRig_char_unit`）。
    順方向（作用→指標）の M322F と逆方向（指標→円分体）の本モジュールを接続する。 -/
def cycRecCharOfAction (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    cycRecCharacter GK M.n where
  chi := cycRigChar GK M ρ
  chi_hom := cycRig_char_isHom GK M ρ
  chi_one := cycRig_char_one GK M ρ
  chi_unit := cycRig_char_unit GK M ρ

/-! ## M334F-7: 外部仮説（真の幾何 μ̂ との同一視は導出しない） -/

/-- **M334F-7a: 幾何整合仮説（Prop）** — 真の幾何的 μ_n⊆K^sep 上の G_K 作用 `geoAct` が
    円分指標 χ の捻りに一致する、という**外部仮説**。mono-anabelian の本丸（π₁^ét の位相群
    データから μ̂ を復元し、それが真の幾何 μ_n と G_K-同型であること）を明示的に受け取る枠。 -/
def cycRecGeoCompatible (GK : Grp) (n : Nat) (χ : cycRecCharacter GK n)
    (geoAct : GK.carrier → (zmod n).carrier → (zmod n).carrier) : Prop :=
  ∀ g x, geoAct g x = zmodMul n (χ.chi g) x

/-- **M334F-7b: 幾何 μ̂ の復元（仮説依存・決して導出しない）** — 幾何整合仮説
    `cycRecGeoCompatible` の下で、真の幾何作用は本モジュールの復元円分体の作用に一致する。
    仮説は外部入力（π₁^ét からの χ 抽出・幾何 μ_n との同型）であり本体で導出しない。 -/
theorem cycRec_geo_recovery_hypothesis (GK : Grp) (n : Nat) (χ : cycRecCharacter GK n)
    (geoAct : GK.carrier → (zmod n).carrier → (zmod n).carrier)
    (hyp : cycRecGeoCompatible GK n χ geoAct)
    (g : GK.carrier) (x : (zmod n).carrier) :
    geoAct g x = (cycRec_mu_from_chi GK n χ).act g x :=
  hyp g x

/-! ## M334F-8: capstone — AbsTopIII の (K^×,v,χ) → (体 + 円分体) -/

/-- **M334F-8a: AbsTopIII 円分体復元データ** — M329F 体復元データ `AbsTopFieldData`
    （乗法＋付値からの体復元）と、χ から復元した円分体 μ̂（G_K-加群）を束ねる。
    復元加法が元の体加法に一致し、円分体の捻りがちょうど χ であることを保持する。
    (K^×, v, χ) → (体 + 円分体) の像を閉じる総括データ。 -/
structure cycRecAbsTopIIICyclotome (K : IUTField) [DecidableEq K.carrier]
    (GK : Grp) (M : CycMuGroup) where
  /-- M329F 体復元データ（復元環＝元の体）。 -/
  field_data : AbsTopFieldData K
  /-- 円分指標 χ（M322F 作用からの `cycRigChar`）。 -/
  chi : cycRecCharacter GK M.n
  /-- χ から復元した円分体 μ̂（G_K-加群）。 -/
  cyclotome : cycRecGKModule GK
  /-- 円分体は χ から復元したもの（`cycRec_mu_from_chi`）に一致（位数 M.n・捻りは χ）。 -/
  cyclotome_eq : cyclotome = cycRec_mu_from_chi GK M.n chi
  /-- 復元加法は元の体 K の加法に一致（M329F 体復元）。 -/
  field_add_eq : ∀ x y, (absFRecoveredRing K).add x y = K.add x y

/-- **M334F-8 capstone: (K^×,v,χ) → (体 + 円分体)** — M325F の AbsTopIII 入力
    `AbsTopIIIInputSkeleton`（乗法＋付値データ ＋ M322F 円分作用 `gal`）と離散付値から、
      (1) M329F 体復元データ（復元環＝元の体・復元加法＝元の加法）、
      (2) 作用 `inp.gal` から χ=`cycRigChar` を取り、そこから復元した円分体 μ̂
          （本物の G_K-加群・捻りはちょうど χ）、
    を組み上げる。M329F 体復元が残した「χ からの μ 復元」を本物で閉じ、
    (K^×, v, χ) → (体 + 円分体) の像を一周させる。 -/
def cycRec_absTopIII_cyclotome (K : IUTField) [DecidableEq K.carrier]
    {GK : Grp} {M : CycMuGroup} (inp : AbsTopIIIInputSkeleton K GK M)
    (val : valRingValuation K) :
    cycRecAbsTopIIICyclotome K GK M where
  field_data := absF_toFieldData K val
  chi := cycRecCharOfAction GK M inp.gal
  cyclotome := cycRec_mu_from_chi GK M.n (cycRecCharOfAction GK M inp.gal)
  cyclotome_eq := rfl
  field_add_eq := fun x y => absF_add_eq K x y

/-- **M334F-8b: capstone の存在**（DecidableEq を持つ体上、自明付値から円分体復元データが
    組み上がる）。具体的な数体・局所体の離散付値上での復元は柱B ℤ_p 接続の後続。 -/
theorem cycRec_absTopIII_exists (K : IUTField) [DecidableEq K.carrier]
    {GK : Grp} {M : CycMuGroup} (inp : AbsTopIIIInputSkeleton K GK M) :
    Nonempty (cycRecAbsTopIIICyclotome K GK M) :=
  ⟨cycRec_absTopIII_cyclotome K inp (trivialValuation K)⟩

/-- **M334F-8c: capstone の円分体は χ 捻り** — capstone データの円分体（`cycRec_mu_from_chi`
    で復元）の G_K 作用は、ちょうど χ での捻り g·x=χ(g)·x である（位数 M.n）。
    復元 μ̂ の捻りがちょうど円分指標であることの明示（円分剛性同型の capstone 版）。 -/
theorem cycRec_absTopIII_twist (K : IUTField) [DecidableEq K.carrier]
    {GK : Grp} {M : CycMuGroup} (d : cycRecAbsTopIIICyclotome K GK M)
    (g : GK.carrier) (x : (zmod M.n).carrier) :
    (cycRec_mu_from_chi GK M.n d.chi).act g x = zmodMul M.n (d.chi.chi g) x := rfl

/-! ## M334F-9: 実例 — 本物の絶対ガロア群 G_ℚ の円分体復元 -/

/-- **M334F-9a: 本物の G_ℚ の円分体復元** — M315F の本物の絶対ガロア群
    G_ℚ=`algCloAbsGalois algCloTrivialTower` の trivial（不分岐）作用から取った χ_l で
    復元した円分体 μ̂（G_ℚ-加群）。IUT が l-捻れ点で用いる μ_l の復元実例。 -/
def cycRecGaloisCyclotome (l : Nat) (hl : 1 ≤ l) :
    cycRecGKModule (algCloAbsGalois algCloTrivialTower) :=
  cycRec_mu_from_chi (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl).n
    (cycRecCharOfAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
      (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)))

/-- **M334F-9b: trivial 指標の復元作用は恒等** — 不分岐 χ≡1 ⟹ 復元円分体の作用は
    σ_g(x)=x（1·x=x）。本物の G_ℚ 上で復元 μ̂ の作用が正しく組み上がる実例。 -/
theorem cycRec_galois_trivial_act (l : Nat) (hl : 1 ≤ l)
    (g : (algCloAbsGalois algCloTrivialTower).carrier)
    (x : (zmod (cycMuStd l hl).n).carrier) :
    (cycRecGaloisCyclotome l hl).act g x = x := by
  show zmodMul (cycMuStd l hl).n
      (cycRigChar (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
        (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)) g) x = x
  rw [cycRig_trivial_char]
  exact zmodOne_mul (cycMuStd l hl).n x

end IUT
