/-
  IUT/MonoThetaEnvironment.lean — M363F [実／本物]
  分類: 実 (mono-theta 環境＝三剛性＋テータ Kummer 類を束ねる本物の対象)
  complete_pct 影響: 柱E を前進（IUT テータ理論の中心対象 mono-theta 環境を、三剛性
    (M323F 定数倍・M333F 離散・M338F 円分)＋ガロア同変テータ(M343F)＋テータ Kummer 類と剛性
    (M353F/M358F)を束ねた本物の対象として構成し、同時整合性を証明）。
  正直な限定: 既存の本物の剛性/類の部品の組立＋同時整合。完全なエタールテータ mono-theta 環境
    (tempered π₁ 込み)は外部。※束ねが主で新規数学が薄い場合はその旨を正直に明記。

  ── 本物で閉じる中身:
  * M363F-1（μ_l ↪ μ_{2l} の標準包含・generator 関係 ζ_l = ζ_{2l}²）: `mte_sq_hζl` /
    `mte_sq_hdist` — μ_{2l} の生成元 ζ（位数 2l・冪の相異性）から、その平方 ζ²=zpPow p ζ 2 が
    μ_l の生成元（位数 l・冪の相異性）を与えることを本物で導出する（M101 `zpPow_zpPow`
    の指数法則のみ、新規数学なし）。mono-theta 環境の内部円分体 μ_l（M338F 円分剛性）と
    テータ Kummer 類の係数 μ_{2l}（M353F/M358F）を**同じ生成元 ζ の平方関係**で結ぶ、
    本モジュール唯一の新規（といっても指数法則のみの）補題。
  * M363F-2（`MonoThetaEnvBundle` 構造体）: 三剛性（M323F 定数倍・M333F 離散・M338F 円分、
    円分剛性は ζ²=ζ_l を主語）・ガロア同変テータ（M343F `GaloisThetaData`）・テータ
    Kummer 類とその円分剛性（M358F `TkrData`, μ_{2l}=ζ を主語）を一括束ねる。
    `galoisTheta_κ` フィールドでガロア同変テータの Kummer 捻り κ とテータ Kummer 類の
    κ が**同一**であることを明示する（同じ Kummer 捻り指標が両方を貫く）。
  * M363F-3（accessors）: `mteConstantMultiple` / `mteDiscrete` / `mteCyclotomic`。
  * M363F-4（`mte_three_rigidities`）: 環境の三剛性を M338F `thCyc_three_rigidities` を
    そのまま再輸出して確立（新規証明ゼロ・純再輸出）。
  * M363F-5（`mte_kummer_rigid`）: 環境がテータ Kummer 類を剛性に保つことを M358F
    `tkr_exists` をそのまま再輸出して確立（新規証明ゼロ・純再輸出）。
  * M363F-6（`mte_coherent` / `mte_kappa_coherent`）: 同時整合性——(i) μ_l と μ_{2l} が
    同じ生成元 ζ の平方関係で両立（M363F-1 の実体化）、(ii) ガロア同変テータとテータ
    Kummer 類が同じ κ を共有（`galoisTheta_κ` の射影）。
  * M363F-7（`mteBuild` / `mte_exists` / `mte_capstone`）: 既存 capstone
    （M323F/M333F/M338F/M343F/M358F の `*_exists`・`*Data` witness）から mono-theta 環境を
    組み立て、存在と三剛性＋Kummer 剛性の同時成立を一つの capstone にまとめる。
  * M363F-8: 実例（l=5, μ_{10}, 本物の G_ℚ 上）。

  **正直な自己評価（水増し防止）**: 本層の新規数学は M363F-1（μ_l↪μ_{2l} の平方関係、
  `zpPow_zpPow` のみを用いる指数法則の適用）に尽きる。それ以外（`MonoThetaEnvBundle` の
  フィールド・`mte_three_rigidities`・`mte_kummer_rigid`・`mteBuild`・`mte_exists`）は
  既存 capstone（M323F `mThRig_exists`・M333F `discRig_exists`・M338F `thCyc_exists`/
  `thCyc_three_rigidities`・M343F `galThData`・M353F `tkc_exists`・M358F `tkrData`/
  `tkr_exists`）の**同時束ね**であり、それ自体は complete_pct を新規に動かさない
  （progress_pct 側の骨格整備）。complete_pct への寄与は「mono-theta 環境という named
  real object が、既存の本物の部品から矛盾なく同時に組み上がる」ことを証明した点に限る
  ——IUT の理論的主張（三剛性＋Kummer 類が同一の mono-theta 環境に共存する）を Lean で
  機械検証した、という意味での前進であり、新しい遠アーベル/エタール数学の追加ではない。
  完全なエタールテータ mono-theta 環境（tempered π₁^ét 込みの本丸）は柱E/D 後続。

  選択公理不使用（新規 Classical.choice なし；継承分の Quot.sound のみ）。sorry 皆無・
  禁止タクティク不使用。一般名は `mte` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.ThetaKummerRigidity

namespace IUT

/-! ## M363F-1: μ_l ↪ μ_{2l} の標準包含（生成元の平方関係 ζ_l = ζ_{2l}²） -/

/-- **M363F-1a: 平方は μ_l の位数条件を満たす** — μ_{2l} の生成元 ζ（ζ^{2l}=1）の平方
    ζ²=zpPow p ζ 2 は μ_l の位数条件 (ζ²)^l=1 を満たす（`zpPow_zpPow`: (ζ²)^l=ζ^{2l}=1）。
    mono-theta 環境の内部円分体 μ_l（M338F）とテータ Kummer 類の係数 μ_{2l}（M358F）を
    同じ生成元 ζ で結ぶ標準包含 μ_l=⟨ζ²⟩ ↪ μ_{2l}=⟨ζ⟩ の生成元側。 -/
theorem mte_sq_hζl (p l : Nat) (ζ : (Zp p).carrier)
    (hζ2l : zpPow p ζ (2 * l) = zpOne p) :
    zpPow p (zpPow p ζ 2) l = zpOne p := by
  rw [zpPow_zpPow]
  exact hζ2l

/-- **M363F-1b: 平方の冪は μ_l の相異性を満たす** — μ_{2l} の生成元 ζ の冪が 0..2l−1 で
    相異なるなら、平方 ζ² の冪は 0..l−1 で相異なる（(ζ²)^i=ζ^{2i}・(ζ²)^j=ζ^{2j}、
    i<j<l ⟹ 2i<2j<2l で外側の相異性 hdist2l に落とす）。μ_l=⟨ζ²⟩ が本当に位数 l の
    群を与える（潰れない）ことの本物の根拠。 -/
theorem mte_sq_hdist (p l : Nat) (ζ : (Zp p).carrier)
    (hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j) :
    ∀ i j, i < j → j < l →
      zpPow p (zpPow p ζ 2) i ≠ zpPow p (zpPow p ζ 2) j := by
  intro i j hij hjl heq
  rw [zpPow_zpPow, zpPow_zpPow] at heq
  exact hdist2l (2 * i) (2 * j) (by omega) (by omega) heq

/-! ## M363F-2: mono-theta 環境（構造体） -/

/-- **M363F-2: mono-theta 環境** — IUT テータ理論の中心対象。三剛性
    （`constMult`: M323F 定数倍剛性・`discrete`: M333F 離散剛性・`cyclotomic`: M338F
    円分剛性、内部円分体の生成元は μ_{2l} 生成元 ζ の平方 ζ²）・ガロア同変テータ
    （`galoisTheta`: M343F、Kummer 捻り κ を共有）・テータ Kummer 類とその円分剛性
    （`kummerRigid`: M358F、係数 μ_{2l} の生成元は ζ そのもの）を一括で束ねる。
    `galoisTheta_κ` により、ガロア同変テータとテータ Kummer 類が**同一の** Kummer 捻り
    指標 κ を共有することを明示する。 -/
structure MonoThetaEnvBundle (R : CRing) (K : IUTField) (p l : Nat) (hl : 2 ≤ l)
    (ζ : (Zp p).carrier) (hζ2l : zpPow p ζ (2 * l) = zpOne p)
    (hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j)
    (GK : Grp) (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat) where
  /-- M323F: 定数倍剛性データ（Laurent 環 R 上のテータ値の比）。 -/
  constMult : MonoThetaRigidityData R
  /-- M333F: 離散剛性データ（K 上の周期格子 q^ℤ の離散性）。 -/
  discrete : DiscreteRigidityData K
  /-- M338F: 円分剛性データ（内部円分体の生成元は μ_{2l} 生成元 ζ の平方 ζ²）。 -/
  cyclotomic : ThetaCyclotomicRigidityData p l hl (zpPow p ζ 2)
      (mte_sq_hζl p l ζ hζ2l) (mte_sq_hdist p l ζ hdist2l)
  /-- M343F: ガロア同変テータ値データ（G_K の μ_l への作用・Kummer 捻り）。 -/
  galoisTheta : GaloisThetaData GK M
  /-- ガロア同変テータの Kummer 捻り κ は、テータ Kummer 類（`kummerRigid`）の κ と同一。 -/
  galoisTheta_κ : galoisTheta.κ = κ
  /-- M358F: テータ Kummer 類の円分剛性データ（係数 μ_{2l} の生成元は ζ そのもの）。 -/
  kummerRigid : TkrData M κ e p (2 * l) (by omega) ζ hdist2l

/-! ## M363F-3: accessors -/

/-- **M363F-3a**: mono-theta 環境から定数倍剛性を取り出す。 -/
def mteConstantMultiple {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) : MonoThetaRigidityData R :=
  env.constMult

/-- **M363F-3b**: mono-theta 環境から離散剛性を取り出す。 -/
def mteDiscrete {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) : DiscreteRigidityData K :=
  env.discrete

/-- **M363F-3c**: mono-theta 環境から円分剛性を取り出す。 -/
def mteCyclotomic {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    ThetaCyclotomicRigidityData p l hl (zpPow p ζ 2)
      (mte_sq_hζl p l ζ hζ2l) (mte_sq_hdist p l ζ hdist2l) :=
  env.cyclotomic

/-! ## M363F-4: 三剛性（M338F の再輸出） -/

/-- **定理 (M363F-4: mono-theta 環境の三剛性)** — 任意の R・K（無限位数の周期 q・その仮説
    hInf 付き）・p・l・μ_{2l} 生成元 ζ（位数 2l・冪の相異性 hdist2l）に対し、三剛性
    （定数倍・離散・円分、円分剛性の主語は ζ の平方 ζ²）が同時に成立する。M338F
    `thCyc_three_rigidities` をそのまま ζ²=zpPow p ζ 2 に特殊化した再輸出（新規証明ゼロ）。 -/
theorem mte_three_rigidities (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζ2l : zpPow p ζ (2 * l) = zpOne p)
    (hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j) :
    Nonempty (MonoThetaRigidityData R)
    ∧ Nonempty (DiscreteRigidityData K)
    ∧ Nonempty (ThetaCyclotomicRigidityData p l hl (zpPow p ζ 2)
        (mte_sq_hζl p l ζ hζ2l) (mte_sq_hdist p l ζ hdist2l)) :=
  thCyc_three_rigidities R K q hInf p l hl (zpPow p ζ 2)
    (mte_sq_hζl p l ζ hζ2l) (mte_sq_hdist p l ζ hdist2l)

/-! ## M363F-5: テータ Kummer 類の円分剛性（M358F の再輸出） -/

/-- **定理 (M363F-5: mono-theta 環境はテータ Kummer 類を剛性に保つ)** — 任意の
    G_K・μ_{2l}・Kummer 捻り κ・指数 e・μ_{2l} 生成元 ζ（冪の相異性 hdist2l）に対し、
    テータ Kummer 類 [Θ]∈H¹(G_K,μ_{2l}) の円分剛性データが存在する。M358F `tkr_exists`
    をそのまま再輸出（新規証明ゼロ）。 -/
theorem mte_kummer_rigid {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j) :
    Nonempty (TkrData M κ e p (2 * l) (by omega) ζ hdist2l) :=
  tkr_exists M κ e p (2 * l) (by omega) ζ hdist2l

/-! ## M363F-6: 同時整合性（coherence） -/

/-- **定理 (M363F-6a: μ_l と μ_{2l} の同時整合)** — μ_{2l} の生成元 ζ の平方 ζ² が μ_l の
    位数条件・相異性を満たす（M363F-1 の実体化）。mono-theta 環境の内部円分体 μ_l
    （M338F 円分剛性）とテータ Kummer 類の係数 μ_{2l}（M358F）が、**同じ生成元 ζ の
    標準包含 μ_l=⟨ζ²⟩↪μ_{2l}=⟨ζ⟩** で矛盾なく両立することの本物の主張。 -/
theorem mte_coherent (p l : Nat) (ζ : (Zp p).carrier)
    (hζ2l : zpPow p ζ (2 * l) = zpOne p)
    (hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j) :
    zpPow p (zpPow p ζ 2) l = zpOne p
    ∧ (∀ i j, i < j → j < l →
        zpPow p (zpPow p ζ 2) i ≠ zpPow p (zpPow p ζ 2) j) :=
  ⟨mte_sq_hζl p l ζ hζ2l, mte_sq_hdist p l ζ hdist2l⟩

/-- **定理 (M363F-6b: ガロア同変テータとテータ Kummer 類は同じ κ を共有)** — mono-theta
    環境 env において、ガロア同変テータデータ `env.galoisTheta` の Kummer 捻り κ は、
    テータ Kummer 類（`env.kummerRigid`）を定める κ と**同一**である
    （`galoisTheta_κ` フィールドの射影）。同じ Kummer 捻り指標が mono-theta 環境の
    ガロア同変性とテータ Kummer 類の両方を貫くことの本物の整合性。 -/
theorem mte_kappa_coherent {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :
    env.galoisTheta.κ = κ :=
  env.galoisTheta_κ

/-! ## M363F-7: 存在（既存 capstone からの組立） -/

/-- **M363F-7a: mono-theta 環境の組立** — 既存の capstone witness
    （M323F `monoThetaRigidityData`・M333F `discreteRigidityData`・M338F
    `thetaCyclotomicRigidityData`・M343F `galThData`・M358F `tkrData`）から
    mono-theta 環境を一括構成する。 -/
def mteBuild (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζ2l : zpPow p ζ (2 * l) = zpOne p)
    (hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (κ : Hom GK M.μ) (e : Nat) :
    MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e where
  constMult := monoThetaRigidityData R
  discrete := discreteRigidityData K q hInf
  cyclotomic := thetaCyclotomicRigidityData p l hl (zpPow p ζ 2)
    (mte_sq_hζl p l ζ hζ2l) (mte_sq_hdist p l ζ hdist2l)
  galoisTheta := galThData GK M ρ κ
  galoisTheta_κ := rfl
  kummerRigid := tkrData M κ e p (2 * l) (by omega) ζ hdist2l

/-- **定理 (M363F-7b: capstone — mono-theta 環境の存在)** — 任意の R・K（周期 q・
    無限位数仮説 hInf）・p・l・μ_{2l} 生成元 ζ（位数 2l・冪の相異性）・G_K・μ_l（=M）・
    G_K 作用 ρ・Kummer 捻り κ・指数 e に対し、三剛性・ガロア同変テータ・テータ Kummer 類
    とその円分剛性を同時に束ねた mono-theta 環境が存在する。IUT のテータ理論の中心対象が
    既存の本物の部品から矛盾なく組み上がることの本物の証明。 -/
theorem mte_exists (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζ2l : zpPow p ζ (2 * l) = zpOne p)
    (hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (κ : Hom GK M.μ) (e : Nat) :
    Nonempty (MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e) :=
  ⟨mteBuild R K q hInf p l hl ζ hζ2l hdist2l GK M ρ κ e⟩

/-- **定理 (M363F-7c: capstone — 環境の存在＋三剛性＋Kummer 剛性の同時成立)** — mono-theta
    環境が存在し（M363F-7b）、かつ同じデータの上で三剛性（M338F）とテータ Kummer 類の
    円分剛性（M358F）が同時に成立する。「mono-theta 環境という一つの構造体が、三剛性の
    同時充足とテータ Kummer 類の剛性保持を併せ持つ」ことを一つの定理として閉じる
    （本モジュールの genuine capstone）。 -/
theorem mte_capstone (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζ2l : zpPow p ζ (2 * l) = zpOne p)
    (hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (κ : Hom GK M.μ) (e : Nat) :
    Nonempty (MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ e)
    ∧ (Nonempty (MonoThetaRigidityData R)
        ∧ Nonempty (DiscreteRigidityData K)
        ∧ Nonempty (ThetaCyclotomicRigidityData p l hl (zpPow p ζ 2)
            (mte_sq_hζl p l ζ hζ2l) (mte_sq_hdist p l ζ hdist2l)))
    ∧ Nonempty (TkrData M κ e p (2 * l) (by omega) ζ hdist2l) :=
  ⟨mte_exists R K q hInf p l hl ζ hζ2l hdist2l GK M ρ κ e,
   thCyc_three_rigidities R K q hInf p l hl (zpPow p ζ 2)
     (mte_sq_hζl p l ζ hζ2l) (mte_sq_hdist p l ζ hdist2l),
   tkr_exists M κ e p (2 * l) (by omega) ζ hdist2l⟩

/-! ## M363F-8: 実例（l=5・μ_{10}・本物の G_ℚ 上） -/

/-- **定理 (M363F-8: 実例)** — 本物の絶対ガロア群 G_ℚ=`algCloAbsGalois
    algCloTrivialTower`（M315F）・μ_{10}（=`cycMuStd 10`）・自明作用 ρ・自明 Kummer 捻り
    κ（M343F `galThTrivialKummer`）・指数 e=4（j=2 の j²）・素数 p（10 ∣ p−1・M121F
    `mu_l_zp_exists` から μ_{10}(ℤ_p) の生成元 ζ が供給される）に対し、mono-theta 環境
    （l=5・μ_{2l}=μ_{10}）が存在する。IUT のテータ理論の中心対象の本物の実例。 -/
theorem mte_example_l5 (R : CRing) (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q)
    (p : Nat) (hp : IsPrime p) (hdvd : (2 * 5) ∣ p - 1) :
    ∃ (ζ : (Zp p).carrier) (hζ2l : zpPow p ζ (2 * 5) = zpOne p)
      (hdist2l : ∀ i j, i < j → j < 2 * 5 → zpPow p ζ i ≠ zpPow p ζ j),
      Nonempty (MonoThetaEnvBundle R K p 5 (by omega) ζ hζ2l hdist2l
        (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
        (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
          (cycMuStd (2 * 5) (by omega))) 4) := by
  obtain ⟨ζ, hζl, hdist, _⟩ := mu_l_zp_exists p (2 * 5) hp (by omega) hdvd
  exact ⟨ζ, hζl, hdist,
    mte_exists R K q hInf p 5 (by omega) ζ hζl hdist
      (algCloAbsGalois algCloTrivialTower) (cycMuStd (2 * 5) (by omega))
      (cycTrivialAction (algCloAbsGalois algCloTrivialTower)
        (cycMuStd (2 * 5) (by omega)))
      (galThTrivialKummer (algCloAbsGalois algCloTrivialTower)
        (cycMuStd (2 * 5) (by omega))) 4⟩

end IUT
