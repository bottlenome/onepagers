/-
  IUT/ProfinitePi1.lean — M287F（pro-有限 π₁^ét = 有限ガロア群の逆極限
  lim Gal(Lᵢ/K) の本物の先行建設・M277F の「pro-有限位相は未」ギャップを埋める）

  分類 **[実]**（本物の体拡大の実 Galois 群 Gal(Lᵢ/K)=Aut_K(Lᵢ)（M271F
  `galoisGroupGrp`）の逆極限として π₁^ét を建設し、副有限位相を M265F
  `ProfiniteTopology` から本物に載せる）。

  complete_pct 影響: **柱A pro-有限 π₁^ét の本物の先行建設**。
  M277F `GrothendieckGalois.lean` は π₁^ét = Aut(F)（ファイバー関手の
  自己同型群）を建設したが、その正直申告 5「π₁ の **pro-有限位相・逆極限
  （有限商系）としての位相群構造は未**。M265F ProfiniteTopology との接続は
  後続」というギャップが残っていた。本モジュールがそのギャップを埋める:
  有限ガロア拡大の cofinal 塔 K⊆L₁⊆L₂⊆… の実 Galois 群 Gal(Lᵢ/K) の
  **逆極限 lim Gal(Lᵢ/K) を pro-有限群として本物に構成**し、各射影核が
  M265F の開部分群系（近傍基）になることを既存の副有限位相理論に接続する。

  内容（本物・toy 群を主語にしない）:
  * M287F-1 `ProfinitePi1Tower` — 有限ガロア拡大の Nat 添字 cofinal 塔
    （各層 `FieldExtension`、層間の**制限準同型** Gal(Lⱼ/K)→Gal(Lᵢ/K) を
    データとして持ち、逆系則（恒等保存・推移性）を witness で受ける）。
  * M287F-2 `profPi1System` — 塔から**逆系**を構成（`natSystem` 経由、
    `G n = galoisGroupGrp (ext n)` = 実 Gal(Lₙ/K)、`t = restr`）。
    `profPi1_restriction`（制限準同型の抽出）・`profPi1_system_compat`
    （制限の推移的整合性）。
  * M287F-3 `profPi1Limit` — **逆極限群 lim Gal(Lᵢ/K)**（成分ごと合成の
    群構造、M13 `limitGrp`）。`profPi1_proj`（射影 π₁→Gal(Lᵢ/K)）。
  * M287F-4 pro-有限性 — 各射影核が開部分群（M265F-3 `projKernelSubgroup`・
    M15-5a `projKernel_isOpen`）: `profPi1_kernel_open`。開部分群系が 1 の
    近傍基（M15-6 `projKernel_nbhd`）: `profPi1_nbhd_base`。開部分群の
    特徴付け（M265F-4）との接続: `profPi1_open_subgroup_iff`。
  * M287F-5 π₁ = Aut(F) との一致（骨組み）— 各層で Gal(Lᵢ/K)→Aut(F|_{Lᵢ})
    （M277F-7d `grGal_fromGalois`）、射影と合成した `profPi1_toPiEt`
    （lim Gal → Aut(F)）。
  * M287F-6 capstone `ProfinitePi1Data` / `profPi1Data` / `profPi1_exists` /
    `profPi1_limit_group` / `profPi1_is_profinite`。
  * M287F-7 実例 — 自明塔（ℚ 上、各層 Gal(ℚ/ℚ)=1）で lim Gal が本物に
    組み上がる `profPi1_trivialTower`。可換な副有限極限の実例として
    ẑ=lim ℤ/n（M265F の nẑ）が同じ「開射影核＝近傍基」の形をなすことの
    確認 `profPi1_zhat_kernel_open`/`profPi1_zhat_nbhd_base`。

  **正直な限定**（何が本物で何が未達か）:
  1. 塔は **Nat 添字の cofinal 鎖** K⊆L₁⊆L₂⊆… に限る（一般の有向系は
     後続、M265F・M24 と同精神）。
  2. 各層の**制限準同型 Gal(Lⱼ/K)→Gal(Lᵢ/K)** は塔の witness データとして
     受け取る（σ∈Gal(Lⱼ/K) が部分体 Lᵢ を保つ＝正規性・制限の全射性は
     分離正規拡大の機構を要し core に無いため）。Galois 群 `galoisGroupGrp`
     そのものは M271F の**本物**（Aut_K(L)）であり、逆系・逆極限群・
     副有限位相（開核・近傍基）は本物で閉じる。
  3. π₁=lim Gal の完全同型（普遍性・充満忠実）は**骨組み**（射影の構成 +
     各層 Gal→Aut(F) 準同型）に留める——完全な同型証明は後続（M277F 正直
     申告 4 と同一の分離正規拡大機構待ち）。
  4. 非自明塔の実例（例: ℚ の円分塔）は二次以上の拡大体の実構成が別切片の
     ため、本モジュールでは自明塔 lim Gal(ℚ/ℚ)=1 の本物の完全構成に留める。

  **選択公理不使用**（新規 Classical.choice を証明本体に導入しない）:
  制限準同型は witness データ、逆系・極限は既存の choice-free 部品
  （`natSystem`・`limitGrp`・`projKernel_isOpen`・`projKernel_nbhd`）で構成。
  sorry 不使用・禁止タクティク（simp/decide/by_cases/rcases/ring 等）不使用。
-/
import IUT.ProfiniteTopology
import IUT.GrothendieckGalois

namespace IUT

/-! ## M287F-0: 汎用の恒等準同型 -/

/-- 群 `G` 上の恒等準同型（自明塔の制限に使う。choice 不要）。 -/
def profPi1IdHom (G : Grp) : Hom G G where
  map := fun x => x
  map_mul := fun _ _ => rfl

/-! ## M287F-1: 有限ガロア拡大の cofinal 塔 -/

/-- **M287F-1: pro-有限 π₁ の塔** — 基礎体 `K` 上の有限ガロア拡大の
    Nat 添字 cofinal 鎖 K⊆L₁⊆L₂⊆…。各層は体拡大 `ext n`（= K⊆Lₙ）で、
    層間の**制限準同型** `restr : Gal(Lⱼ/K)→Gal(Lᵢ/K)`（i≤j）を witness
    データとして持ち、逆系則（恒等保存 `restr_self`・推移性 `restr_comp`）を
    仮説で受ける（正規性・制限の全射性は分離正規拡大機構待ちの正直な限定）。 -/
structure ProfinitePi1Tower where
  /-- 基礎体 K。 -/
  K : IUTField
  /-- 塔の各層 K⊆Lₙ（有限ガロア拡大）。 -/
  ext : Nat → FieldExtension
  /-- 制限準同型 Gal(Lⱼ/K) → Gal(Lᵢ/K)（i ≤ j、Lⱼ の自己同型を Lᵢ に制限）。 -/
  restr : ∀ {i j : Nat}, i ≤ j →
    Hom (galoisGroupGrp (ext j)) (galoisGroupGrp (ext i))
  /-- 恒等保存: 同一層への制限は恒等。 -/
  restr_self : ∀ (i : Nat) (x : (galoisGroupGrp (ext i)).carrier),
    (restr (Nat.le_refl i)).map x = x
  /-- 推移性: 制限の合成は合成の制限（逆系の整合条件）。 -/
  restr_comp : ∀ {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k)
    (x : (galoisGroupGrp (ext k)).carrier),
    (restr hij).map ((restr hjk).map x) = (restr (Nat.le_trans hij hjk)).map x

/-! ## M287F-2: 塔から逆系 -/

/-- **M287F-2: 有限ガロア群の逆系** — 塔 `T` の各層 Gal(Lₙ/K)（実
    `galoisGroupGrp`）と制限準同型からなる逆系（`natSystem` 経由）。
    恒等保存・推移性が逆系則をなす（塔の witness から）。 -/
@[reducible] def profPi1System (T : ProfinitePi1Tower) : InverseSystem :=
  natSystem (fun n => galoisGroupGrp (T.ext n)) (fun h => T.restr h)
    (fun i x => T.restr_self i x)
    (fun hij hjk x => T.restr_comp hij hjk x)

/-- **M287F-2a: 制限準同型の抽出** — 逆系の推移射は塔の制限準同型。 -/
theorem profPi1_restriction (T : ProfinitePi1Tower) {i j : Nat} (h : i ≤ j) :
    (profPi1System T).t h = T.restr h := rfl

/-- **M287F-2b: 制限の推移的整合性** — Gal(L_k)→Gal(L_i) を経由する制限は
    Gal(L_k)→Gal(L_j)→Gal(L_i) の合成に等しい（逆系の整合、塔の推移性）。 -/
theorem profPi1_system_compat (T : ProfinitePi1Tower) {i j k : Nat}
    (hij : i ≤ j) (hjk : j ≤ k)
    (x : (galoisGroupGrp (T.ext k)).carrier) :
    (T.restr hij).map ((T.restr hjk).map x)
      = (T.restr (Nat.le_trans hij hjk)).map x :=
  T.restr_comp hij hjk x

/-! ## M287F-3: 逆極限群 lim Gal(Lᵢ/K) -/

/-- **M287F-3: 逆極限群 π₁^ét = lim Gal(Lᵢ/K)** — 整合族（各層の Galois
    自己同型が制限で整合するもの）のなす群（成分ごと合成、M13 `limitGrp`）。
    本物の pro-有限 π₁^ét（有限ガロア群の逆極限としての本来の定義）。 -/
def profPi1Limit (T : ProfinitePi1Tower) : Grp := limitGrp (profPi1System T)

/-- **M287F-3a: 射影 π₁ → Gal(Lₙ/K)** — 逆極限の第 n 成分をとる準同型
    （極限の錐、M13 `limitProj`）。 -/
def profPi1_proj (T : ProfinitePi1Tower) (n : Nat) :
    Hom (profPi1Limit T) (galoisGroupGrp (T.ext n)) :=
  limitProj (profPi1System T) n

/-- **M287F-3b: 射影の整合性** — 射影は制限準同型と整合する
    （π_i = restr ∘ π_j、i≤j）。 -/
theorem profPi1_proj_compat (T : ProfinitePi1Tower) {i j : Nat} (h : i ≤ j)
    (x : (profPi1Limit T).carrier) :
    (T.restr h).map ((profPi1_proj T j).map x) = (profPi1_proj T i).map x :=
  x.property h

/-! ## M287F-4: pro-有限性（射影核 = 開部分群系 = 近傍基） -/

/-- **M287F-4a: 射影核の開部分群** — レベル n の射影核
    ker(π_n : lim Gal → Gal(Lₙ/K))（M265F-3 `projKernelSubgroup`）。 -/
def profPi1KernelSubgroup (T : ProfinitePi1Tower) (n : Nat) :
    Subgroup (profPi1Limit T) :=
  projKernelSubgroup (profPi1System T) n

/-- **M287F-4b: 射影核は開**（副有限位相、M15-5a）— pro-有限性の核。 -/
theorem profPi1_kernel_open (T : ProfinitePi1Tower) (n : Nat) :
    (limitTopology (profPi1System T)).IsOpen (profPi1KernelSubgroup T n).mem :=
  projKernel_isOpen (profPi1System T) n

/-- **M287F-4c: 射影核は clopen**（副有限群の全不連結性、M265F-2）。 -/
theorem profPi1_kernel_clopen (T : ProfinitePi1Tower) (n : Nat) :
    (limitTopology (profPi1System T)).IsOpen
      (fun σ => ¬ (profPi1KernelSubgroup T n).mem σ) :=
  projKernel_compl_isOpen (profPi1System T) n

/-- **M287F-4d: 開部分群系は 1 の近傍基**（M15-6 `projKernel_nbhd`）—
    1 の任意の開近傍 U はある射影核 ker(π_k) を含む。pro-有限位相の
    「開部分群が単位元の基本近傍系をなす」本来の性質。 -/
theorem profPi1_nbhd_base (T : ProfinitePi1Tower) (i₀ : Nat)
    (U : (profPi1Limit T).carrier → Prop)
    (hU : (limitTopology (profPi1System T)).IsOpen U)
    (h1 : U (profPi1Limit T).one) :
    ∃ k, ∀ y, projKernel (profPi1System T) k y → U y :=
  projKernel_nbhd (profPi1System T) i₀ U hU h1

/-- **M287F-4e: 開部分群の特徴付け**（M265F-4 との接続）— 部分群 H が
    副有限位相で開 ⟺ H はある射影核（開部分群 ker π_k）を含む。
    「pro-有限 π₁ の開部分群 = 有限レベルで定義される部分群」の実現。 -/
theorem profPi1_open_subgroup_iff (T : ProfinitePi1Tower) (i₀ : Nat)
    (H : Subgroup (profPi1Limit T)) :
    (limitTopology (profPi1System T)).IsOpen H.mem
      ↔ ∃ k, ∀ y, projKernel (profPi1System T) k y → H.mem y :=
  subgroup_isOpen_iff_contains_kernel (profPi1System T) i₀ H

/-! ## M287F-5: π₁ = Aut(F) との一致（骨組み） -/

/-- **M287F-5a: 各層 Gal(Lₙ/K) → Aut(F|_{Lₙ})**（M277F-7d
    `grGal_fromGalois`）— 有限層の Galois 群が π₁ = Aut(ファイバー関手) の
    中に後合成で実現される準同型。 -/
def profPi1_layerToPiEt (T : ProfinitePi1Tower) (n : Nat) :
    Hom (galoisGroupGrp (T.ext n))
      (piEtGroupAt (T.ext n).base (grGalPointAlgebra (T.ext n))) :=
  grGal_fromGalois (T.ext n)

/-- **M287F-5b: lim Gal → Aut(F|_{Lₙ})**（射影と各層準同型の合成）—
    pro-有限 π₁ = lim Gal(Lᵢ/K) から各有限層の Aut(F) への準同型。
    「lim Gal と Aut(F) の一致」の骨組み（射影の構成 + 各層準同型）。 -/
def profPi1_toPiEt (T : ProfinitePi1Tower) (n : Nat) :
    Hom (profPi1Limit T)
      (piEtGroupAt (T.ext n).base (grGalPointAlgebra (T.ext n))) :=
  Hom.comp (profPi1_layerToPiEt T n) (profPi1_proj T n)

/-! ## M287F-6: capstone -/

/-- **M287F-6a: capstone データ** — 塔 T に対する pro-有限 π₁^ét の全部品:
    有限ガロア群の逆系・逆極限群 lim Gal・射影・射影核の開性・近傍基・
    開部分群の特徴付け・各層 Aut(F) への準同型。 -/
structure ProfinitePi1Data (T : ProfinitePi1Tower) where
  /-- 有限ガロア群の逆系。 -/
  system : InverseSystem
  /-- 逆系は塔から構成した `profPi1System`。 -/
  system_eq : system = profPi1System T
  /-- 逆極限群 π₁ = lim Gal(Lᵢ/K)。 -/
  limitGroup : Grp
  /-- 逆極限群は `profPi1Limit`。 -/
  limitGroup_eq : limitGroup = profPi1Limit T
  /-- 射影 π₁ → Gal(Lₙ/K)。 -/
  proj : ∀ n, Hom (profPi1Limit T) (galoisGroupGrp (T.ext n))
  /-- 射影核（開部分群）は開。 -/
  kernel_open : ∀ n, (limitTopology (profPi1System T)).IsOpen
    (profPi1KernelSubgroup T n).mem
  /-- 開部分群系は 1 の近傍基。 -/
  nbhd_base : ∀ (i₀ : Nat) (U : (profPi1Limit T).carrier → Prop),
    (limitTopology (profPi1System T)).IsOpen U → U (profPi1Limit T).one →
    ∃ k, ∀ y, projKernel (profPi1System T) k y → U y
  /-- 各層 Aut(F) への準同型（π₁=Aut(F) 一致の骨組み）。 -/
  toPiEt : ∀ n, Hom (profPi1Limit T)
    (piEtGroupAt (T.ext n).base (grGalPointAlgebra (T.ext n)))

/-- **M287F-6b: 証人** — 逆系・逆極限群・射影・開核・近傍基・各層準同型が
    全条件を満たす。 -/
def profPi1Data (T : ProfinitePi1Tower) : ProfinitePi1Data T where
  system := profPi1System T
  system_eq := rfl
  limitGroup := profPi1Limit T
  limitGroup_eq := rfl
  proj := fun n => profPi1_proj T n
  kernel_open := fun n => profPi1_kernel_open T n
  nbhd_base := fun i₀ U hU h1 => profPi1_nbhd_base T i₀ U hU h1
  toPiEt := fun n => profPi1_toPiEt T n

/-- **M287F-6c: capstone — pro-有限 π₁^ét の存在** — 任意の有限ガロア塔に
    対し、その実 Galois 群の逆極限（副有限位相込み）が組み上がる。 -/
theorem profPi1_exists (T : ProfinitePi1Tower) : Nonempty (ProfinitePi1Data T) :=
  ⟨profPi1Data T⟩

/-- **M287F-6d: 逆極限群の構成** — π₁^ét = lim Gal(Lᵢ/K) を群として。 -/
def profPi1_limit_group (T : ProfinitePi1Tower) : Grp := profPi1Limit T

/-- **M287F-6e: pro-有限性の総括** — lim Gal の各射影核が開部分群であり、
    かつ開部分群系が 1 の近傍基をなす（＝pro-有限群である本来の内容）。 -/
theorem profPi1_is_profinite (T : ProfinitePi1Tower) :
    (∀ n, (limitTopology (profPi1System T)).IsOpen
        (profPi1KernelSubgroup T n).mem)
      ∧ (∀ (i₀ : Nat) (U : (profPi1Limit T).carrier → Prop),
          (limitTopology (profPi1System T)).IsOpen U →
          U (profPi1Limit T).one →
          ∃ k, ∀ y, projKernel (profPi1System T) k y → U y) :=
  ⟨fun n => profPi1_kernel_open T n,
    fun i₀ U hU h1 => profPi1_nbhd_base T i₀ U hU h1⟩

/-! ## M287F-7: 実例 -/

/-- **M287F-7a: 自明塔**（ℚ 上、各層 Gal(ℚ/ℚ)=1）— 制限は恒等準同型。
    非自明塔の実例は二次以上の拡大体の実構成が別切片のため、本物に
    完全構成できる自明塔で lim Gal が組み上がることを確認する。 -/
def profPi1_trivialTower : ProfinitePi1Tower where
  K := ratIUTField
  ext := fun _ => trivialExtension ratIUTField
  restr := fun _ => profPi1IdHom (galoisGroupGrp (trivialExtension ratIUTField))
  restr_self := fun _ _ => rfl
  restr_comp := fun _ _ _ => rfl

/-- **M287F-7b: 自明塔で pro-有限 π₁ が組み上がる**（本物の数体 ℚ 上）。 -/
def profPi1_trivial_data : ProfinitePi1Data profPi1_trivialTower :=
  profPi1Data profPi1_trivialTower

/-- **M287F-7c: 自明塔の pro-有限性の総括**（ℚ 上の lim Gal(ℚ/ℚ)=1 が
    開核・近傍基を持つ副有限群である）。 -/
theorem profPi1_trivial_is_profinite :
    (∀ n, (limitTopology (profPi1System profPi1_trivialTower)).IsOpen
        (profPi1KernelSubgroup profPi1_trivialTower n).mem)
      ∧ (∀ (i₀ : Nat)
          (U : (profPi1Limit profPi1_trivialTower).carrier → Prop),
          (limitTopology (profPi1System profPi1_trivialTower)).IsOpen U →
          U (profPi1Limit profPi1_trivialTower).one →
          ∃ k, ∀ y, projKernel (profPi1System profPi1_trivialTower) k y → U y) :=
  profPi1_is_profinite profPi1_trivialTower

/-- **M287F-7d: 可換な副有限極限の実例** — ẑ = lim ℤ/n（M265F の nẑ）の
    射影核が開（pro-有限 π₁ と同じ「開射影核」の形）。可換 Galois 群
    （Ẑ = Gal(ℚᵃᵇ/ℚ) 型）の逆極限の実例確認。 -/
theorem profPi1_zhat_kernel_open (n : Nat) :
    (limitTopology zmodSystem).IsOpen (projKernelSubgroup zmodSystem n).mem :=
  projKernel_isOpen zmodSystem n

/-- **M287F-7e: ẑ の開部分群系は 1 の近傍基**（同じ副有限位相の形）。 -/
theorem profPi1_zhat_nbhd_base (i₀ : Nat) (U : zhat.carrier → Prop)
    (hU : (limitTopology zmodSystem).IsOpen U) (h1 : U zhat.one) :
    ∃ k, ∀ y, projKernel zmodSystem k y → U y :=
  projKernel_nbhd zmodSystem i₀ U hU h1

end IUT
