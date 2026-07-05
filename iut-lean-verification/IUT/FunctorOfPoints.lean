/-
  IUT/FunctorOfPoints.lean — M297F（関数の圏／K-点＝環準同型・核＝素イデアル）

  分類: **[実]**（本物の可換環 `CRing`・本物の体 `IUTField`・本物の環準同型
    `RingHom`・本物の素イデアル `primeSpecPrime`（M289F）の上での実 mono-anabelian
    最下層構成。toy 主語なし——主語は「R から体 K への実環準同型」そのもの）。

  complete_pct 影響: **+**（柱A スキーム論／mono-anabelian。mono-anabelian の核
    「空間の点＝環への関数」を本物化する。すなわち「R の K-値点＝環準同型 R→K」
    であること、そして「体への環準同型の核は素イデアル（＝Spec R の点）」であること、
    さらに「幾何的射 Spec K → Spec R が体の唯一の点 (0) を ker φ に送る」ことを、
    実 CRing・実 IUTField・実 RingHom・実 primeSpecPrime の上で本物に建設する。
    米田的「空間＝関手 Hom(−,X)」の点集合側・核＝点対応の代数的核を本物で閉じる。）

  柱A「スキーム論（実 mono-anabelian への前提）」の**本物の先行建設**。

  ロードマップ上の位置: 遠アーベル幾何の中核である「点＝環への関数（K-値点）」の
  実装。X(K) = Hom(Spec K, X) = Hom(R, K)（アフィン X=Spec R の場合）という
  関手 of points の代数側と、点↔素イデアル（核）の対応を実代数で確立する。

  * M297F-1 `fptsKPoint R K` — R の **K-値点** = 環準同型 R → K（体 K への関数）。
  * M297F-2 `fptsPullbackPrime` — 素イデアルの **witness 形引き戻し** φ⁻¹(P)
    （φ:R→S・P:primeSpecPrime S ↦ primeSpecPrime R）。**構成的**（選言不要）。
  * M297F-3 `fptsKerPrime` / `fptsKerPoint` — 体への準同型 φ:R→K の **核 ker φ**
    ＝体の零点 (0)（`primeSpecFieldZeroPrime`, M289F）の引き戻し。これが Spec R の
    素点。`fpts_ker_mem`（核の所属＝φ(r)=0）・`fpts_ker_prime_witness`（核の素性）。
  * M297F-4 `fptsPrecomp` / `fptsPostcomp` — 関手性。R'→R が X(K) の反変誘導
    （precompose）、K→K' が X(K)→X(K') の共変誘導（postcompose）。単位則・合成則。
  * M297F-5 `fptsKerPoint` の residue 骨組み `fpts_point_residue` — K-点 φ は
    点 P（＝核）を定め、r↦0 ⟺ r∈P で因子化する（R/ker φ ↪ K の骨組み）。
  * M297F-6 capstone `FunctorOfPointsData`・`fpts_exists`・`fpts_kpoint_is_hom`・
    `fpts_ker_prime`・`fpts_functor_laws`。
  * M297F-7 実例: 体 L の K-点＝体の埋め込み L→K（`fptsFieldPoint`）、
    恒等 K-点（`fptsIdentityPoint`）、ℚ の ℚ-点。

  正直な限定（消去・弱化禁止）:
  - **選言形 specFunPrime（M291F）は体に対して非構成的**。M291F の `specFunPrime`
    は素条件を選言形 `ab∈P → a∈P ∨ b∈P` で述べるが、体の零イデアルに対しこの選言を
    出すには K の等号判定の排中律を要し、本規約が証明本体での Classical.choice を
    禁ずる。よって本ファイルは **M289F の witness 形 `primeSpecPrime`**
    （`¬a∈P → ¬b∈P → ¬ab∈P`）で核の素性を本物・構成的に建設する。核＝体の零点
    (0)（`primeSpecFieldZeroPrime`）の引き戻しであり、「幾何的射が (0) を ker φ に
    送る」ことの構成的な実現。選言形での定式化は排中律（後続の古典層）でのみ従う。
  - **residue 体の一般構成 R/P は未達**。剰余環 R/ker φ の一般構成（商環）は
    本コードベースに未整備なため、`fpts_point_residue` は「K-点 φ が点 P を定め
    r↦0 ⟺ r∈P で因子化する」述語レベルの骨組みまで。商環 R/P と埋め込み
    κ(P)↪K の完全構成は後続。
  - **関手 of points の完全な圏論版（米田 Hom(−,X)）は後続**。ここは K-点＝環準同型・
    核＝点（素イデアル）・R/K 両変数の関手性（precompose/postcompose）の代数的核まで。
  - 「Spec K → Spec R の局所環空間の射としての完全対応」は M293F/M294F の構造層
    骨組みに乗る後続。ここは環準同型 R→K ↔ 核＝素イデアル の代数的核を本物で。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無。
-/
import IUT.SpecFunctorial
import IUT.PrimeSpectrum

namespace IUT

/-! ## M297F-1: K-値点 = 環準同型 R → K -/

/-- **M297F-1: R の K-値点** — 可換環 R から体 K への環準同型。
    mono-anabelian「点＝環への関数（K への評価）」の本物の定義。 -/
abbrev fptsKPoint (R : CRing) (K : IUTField) : Type := RingHom R K.toCRing

/-- R の K-値点全体 X(K) = Hom(R, K)（関手 of points の点集合側）。 -/
abbrev fptsPoints (R : CRing) (K : IUTField) : Type := RingHom R K.toCRing

/-! ## M297F-2: 素イデアルの witness 形引き戻し（構成的） -/

/-- **M297F-2: 素イデアルの引き戻し（witness 形・構成的）** φ⁻¹(P)={r | φ(r)∈P}。
    M289F の witness 形素イデアル `primeSpecPrime` を引き戻す。選言を使わないため
    体の場合も構成的に閉じる（M291F の選言形 `specFunPullback` の witness 版）。 -/
def fptsPullbackPrime {R S : CRing} (φ : RingHom R S) (P : primeSpecPrime S) :
    primeSpecPrime R where
  mem := fun r => P.mem (φ.map r)
  zero_mem := by
    show P.mem (φ.map R.zero)
    rw [specFun_map_zero φ]
    exact P.zero_mem
  add_mem := by
    intro x y hx hy
    show P.mem (φ.map (R.add x y))
    rw [φ.map_add]
    exact P.add_mem _ _ hx hy
  smul_mem := by
    intro r x hx
    show P.mem (φ.map (R.mul r x))
    rw [φ.map_mul]
    exact P.smul_mem _ _ hx
  proper := by
    show ¬ P.mem (φ.map R.one)
    rw [φ.map_one]
    exact P.proper
  prime_witness := by
    intro a b ha hb
    show ¬ P.mem (φ.map (R.mul a b))
    rw [φ.map_mul]
    exact P.prime_witness _ _ ha hb

/-- 引き戻しの所属述語が φ⁻¹ そのものであることの明示。 -/
theorem fpts_pullback_mem {R S : CRing} (φ : RingHom R S) (P : primeSpecPrime S)
    (r : R.carrier) :
    (fptsPullbackPrime φ P).mem r ↔ P.mem (φ.map r) := Iff.rfl

/-! ## M297F-3: 体への準同型の核＝(0) の引き戻し＝Spec R の点 -/

/-- **M297F-3a: K-値点 φ の核 ker φ**（素イデアル）— 体 K の零点 (0)
    （`primeSpecFieldZeroPrime`, M289F）の φ による引き戻し。すなわち幾何的射
    Spec K → Spec R が Spec K の唯一の点 (0) を送る先が ker φ である、の本物。 -/
def fptsKerPrime {R : CRing} {K : IUTField} (φ : fptsKPoint R K) :
    primeSpecPrime R :=
  fptsPullbackPrime φ (primeSpecFieldZeroPrime K)

/-- **M297F-3b: 核の点**（Spec R の素点）。 -/
def fptsKerPoint {R : CRing} {K : IUTField} (φ : fptsKPoint R K) :
    PrimeSpectrum R :=
  ⟨fptsKerPrime φ⟩

/-- **M297F-3c: 核の所属＝φ(r)=0**（ker φ = {r | φ(r)=0}）。 -/
theorem fpts_ker_mem {R : CRing} {K : IUTField} (φ : fptsKPoint R K)
    (r : R.carrier) :
    (fptsKerPrime φ).mem r ↔ (φ.map r = K.zero) := Iff.rfl

/-- **M297F-3d: 核の素性（本物・witness 形）** — φ(a)≠0 かつ φ(b)≠0 なら
    φ(ab)≠0。体の整域性 `mul_ne_zero`（M264F）を本質的に使用。これが
    「体への準同型の核は素イデアル」の構成的核。 -/
theorem fpts_ker_prime_witness {R : CRing} {K : IUTField} (φ : fptsKPoint R K)
    (a b : R.carrier) (ha : φ.map a ≠ K.zero) (hb : φ.map b ≠ K.zero) :
    φ.map (R.mul a b) ≠ K.zero :=
  (fptsKerPrime φ).prime_witness a b ha hb

/-- **M297F-3e: 核は真イデアル**（φ(1)=1≠0 なので 1∉ker φ）。 -/
theorem fpts_ker_proper {R : CRing} {K : IUTField} (φ : fptsKPoint R K) :
    ¬ (fptsKerPrime φ).mem R.one :=
  (fptsKerPrime φ).proper

/-- **M297F-3f: 幾何的射は体の零点 (0) を ker φ に送る**（本物の対応）。
    ker φ の所属＝(0)_K の引き戻しの所属、すなわち φ(r)∈(0) ⟺ φ(r)=0。 -/
theorem fpts_ker_is_pullback_of_zero {R : CRing} {K : IUTField}
    (φ : fptsKPoint R K) (r : R.carrier) :
    (fptsKerPrime φ).mem r ↔ (primeSpecFieldZeroPrime K).mem (φ.map r) := Iff.rfl

/-! ## M297F-4: 関手性（R で反変・K で共変） -/

/-- **M297F-4a: 反変誘導（R 側）** — 環準同型 ψ:R→R' は K-点写像
    X(R')(K) → X(R)(K) を反変に誘導する（precompose φ ↦ φ∘ψ）。 -/
def fptsPrecomp {R R' : CRing} {K : IUTField} (ψ : RingHom R R') :
    fptsKPoint R' K → fptsKPoint R K :=
  fun φ => RingHom.comp ψ φ

/-- **M297F-4b: precompose の単位則** — 恒等 R→R での誘導は恒等。 -/
theorem fpts_precomp_id {R : CRing} {K : IUTField} (φ : fptsKPoint R K) :
    fptsPrecomp (K := K) (specFunIdRingHom R) φ = φ := rfl

/-- **M297F-4c: precompose の合成則（反変）** — (ψ₁∘ψ₂ の誘導) =
    (ψ₂ の誘導)∘(ψ₁ の誘導)。RingHom.comp が図式順なので反変性が自然に立つ。 -/
theorem fpts_precomp_comp {R R' R'' : CRing} {K : IUTField}
    (ψ₁ : RingHom R R') (ψ₂ : RingHom R' R'') (φ : fptsKPoint R'' K) :
    fptsPrecomp (K := K) (RingHom.comp ψ₁ ψ₂) φ
      = fptsPrecomp ψ₁ (fptsPrecomp ψ₂ φ) := rfl

/-- **M297F-4d: 共変誘導（K 側）** — 体の埋め込み θ:K→K' は K-点写像
    X(R)(K) → X(R)(K') を共変に誘導する（postcompose φ ↦ θ∘φ）。 -/
def fptsPostcomp {R : CRing} {K K' : IUTField}
    (θ : RingHom K.toCRing K'.toCRing) :
    fptsKPoint R K → fptsKPoint R K' :=
  fun φ => RingHom.comp φ θ

/-- **M297F-4e: postcompose の単位則** — 恒等 K→K での誘導は恒等。 -/
theorem fpts_postcomp_id {R : CRing} {K : IUTField} (φ : fptsKPoint R K) :
    fptsPostcomp (R := R) (specFunIdRingHom K.toCRing) φ = φ := rfl

/-- **M297F-4f: postcompose の合成則（共変）** — (θ₂∘θ₁ の誘導) =
    (θ₂ の誘導)∘(θ₁ の誘導)。 -/
theorem fpts_postcomp_comp {R : CRing} {K K' K'' : IUTField}
    (θ₁ : RingHom K.toCRing K'.toCRing) (θ₂ : RingHom K'.toCRing K''.toCRing)
    (φ : fptsKPoint R K) :
    fptsPostcomp (R := R) (RingHom.comp θ₁ θ₂) φ
      = fptsPostcomp θ₂ (fptsPostcomp θ₁ φ) := rfl

/-! ## M297F-5: residue 体経由の点（骨組み） -/

/-- **M297F-5: 点↔核の因子化骨組み** — K-値点 φ は点 P（＝核 fptsKerPoint φ）を
    定め、r↦0 ⟺ r∈P で因子化する（R/ker φ ↪ K の骨組み）。剰余環 R/P の一般構成は
    後続なので、ここは因子化述語 r∈P ⟺ φ(r)=0 の存在まで。 -/
theorem fpts_point_residue {R : CRing} {K : IUTField} (φ : fptsKPoint R K) :
    ∃ P : PrimeSpectrum R, ∀ r, P.toPrime.mem r ↔ φ.map r = K.zero :=
  ⟨fptsKerPoint φ, fun _ => Iff.rfl⟩

/-! ## M297F-6: capstone -/

/-- **M297F-6a: 関手 of points データ** — R の K-値点（＝環準同型）とその核
    （＝Spec R の点）、および核＝{φ=0} の対応を束ねる。 -/
structure FunctorOfPointsData (R : CRing) (K : IUTField) where
  /-- K-値点（環準同型 R→K）。 -/
  point : fptsKPoint R K
  /-- 核の点（Spec R の素点）。 -/
  ker : PrimeSpectrum R
  /-- 核＝{r | φ(r)=0}。 -/
  ker_eq : ∀ r, ker.toPrime.mem r ↔ point.map r = K.zero

/-- **M297F-6b: K-値点から関手 of points データを構成**。 -/
def fptsData {R : CRing} {K : IUTField} (φ : fptsKPoint R K) :
    FunctorOfPointsData R K where
  point := φ
  ker := fptsKerPoint φ
  ker_eq := fun _ => Iff.rfl

/-- **M297F-6c: K-値点＝環準同型 R→K**（定義の明示）。 -/
theorem fpts_kpoint_is_hom (R : CRing) (K : IUTField) :
    fptsKPoint R K = RingHom R K.toCRing := rfl

/-- **M297F-6d: 核＝素イデアル（点）**（本物）— 各 K-値点 φ に対し、
    φ の核はある素イデアル P であって P={r | φ(r)=0}。 -/
theorem fpts_ker_prime {R : CRing} {K : IUTField} (φ : fptsKPoint R K) :
    ∃ P : primeSpecPrime R, ∀ r, P.mem r ↔ φ.map r = K.zero :=
  ⟨fptsKerPrime φ, fun _ => Iff.rfl⟩

/-- **M297F-6e: 関手性の束ね**（R 反変・K 共変の単位/合成則）。 -/
structure fptsFunctorLaws : Prop where
  /-- R 反変・単位則。 -/
  precomp_id : ∀ {R : CRing} {K : IUTField} (φ : fptsKPoint R K),
    fptsPrecomp (K := K) (specFunIdRingHom R) φ = φ
  /-- R 反変・合成則。 -/
  precomp_comp : ∀ {R R' R'' : CRing} {K : IUTField}
      (ψ₁ : RingHom R R') (ψ₂ : RingHom R' R'') (φ : fptsKPoint R'' K),
    fptsPrecomp (K := K) (RingHom.comp ψ₁ ψ₂) φ
      = fptsPrecomp ψ₁ (fptsPrecomp ψ₂ φ)
  /-- K 共変・単位則。 -/
  postcomp_id : ∀ {R : CRing} {K : IUTField} (φ : fptsKPoint R K),
    fptsPostcomp (R := R) (specFunIdRingHom K.toCRing) φ = φ
  /-- K 共変・合成則。 -/
  postcomp_comp : ∀ {R : CRing} {K K' K'' : IUTField}
      (θ₁ : RingHom K.toCRing K'.toCRing) (θ₂ : RingHom K'.toCRing K''.toCRing)
      (φ : fptsKPoint R K),
    fptsPostcomp (R := R) (RingHom.comp θ₁ θ₂) φ
      = fptsPostcomp θ₂ (fptsPostcomp θ₁ φ)

/-- **M297F-6f: 関手 of points の関手則は成立**。 -/
theorem fpts_functor_laws : fptsFunctorLaws :=
  { precomp_id := fun φ => fpts_precomp_id φ
    precomp_comp := fun ψ₁ ψ₂ φ => fpts_precomp_comp ψ₁ ψ₂ φ
    postcomp_id := fun φ => fpts_postcomp_id φ
    postcomp_comp := fun θ₁ θ₂ φ => fpts_postcomp_comp θ₁ θ₂ φ }

/-! ## M297F-7: 実例 -/

/-- **M297F-7a: 体 L の K-点＝体の埋め込み L→K**。環準同型 θ:L→K は L の K-値点。 -/
def fptsFieldPoint {L K : IUTField} (θ : RingHom L.toCRing K.toCRing) :
    fptsKPoint L.toCRing K := θ

/-- **M297F-7b: 恒等 K-点** — 体 K の恒等射は K の K-値点（対角点）。 -/
def fptsIdentityPoint (K : IUTField) : fptsKPoint K.toCRing K :=
  specFunIdRingHom K.toCRing

/-- 恒等 K-点の核は {x | x=0}（体の零点 (0)）。 -/
theorem fpts_identity_ker (K : IUTField) (x : K.carrier) :
    (fptsKerPrime (fptsIdentityPoint K)).mem x ↔ (x = K.zero) := Iff.rfl

/-- **M297F-7c: ℚ の ℚ-点**（恒等）— 有理数体 ℚ（M264F `ratIUTField`）の
    ℚ-値点の実例。核は (0)。 -/
def fptsRatPoint : fptsKPoint ratIUTField.toCRing ratIUTField :=
  fptsIdentityPoint ratIUTField

/-- ℚ の ℚ-点は本物に存在。 -/
theorem fpts_rat_point_exists :
    Nonempty (fptsKPoint ratIUTField.toCRing ratIUTField) :=
  ⟨fptsRatPoint⟩

/-- **M297F-7d: K-値点は空でない**（体 K の対角点が存在）。 -/
theorem fpts_exists (K : IUTField) :
    Nonempty (fptsKPoint K.toCRing K) :=
  ⟨fptsIdentityPoint K⟩

end IUT
