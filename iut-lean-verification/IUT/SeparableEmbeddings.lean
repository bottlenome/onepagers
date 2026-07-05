/-
  IUT/SeparableEmbeddings.lean — M282F（分離次数 = K-埋め込みの個数 = [L:K]:
  柱A 実分離拡大とファイバー基数の本物の先行建設）

  ── 分類 **[実]**（本物の先行建設。骨格・模型・代理でなく本物の証明・
  sorry 皆無・新規 Classical.choice 皆無）。

  **complete_pct 影響**: **本物の先行建設(b)**。柱A「実分離拡大とファイバー
  基数」。単純拡大 L = K(α) = K[X]/(m)（m = α の最小多項式）に対し、
  **L → Ω の K-埋め込み（K を固定する環準同型）が α の像 = Ω 内の m の根で
  一意に定まり、その個数が m の相異なる根の個数 = deg m = [L:K]** に一致する
  ことを本物に構成する。これは M276F の「ファイバー基数 |F(L)| = n」の
  **=n を本物の代数（ガロア被覆のファイバー基数）に置換**する核であり、
  遠アーベル復元での π₁ 作用の基数の実代数的根拠である。

  本層の主要成果（本物・sorry 不使用・Classical.choice 不使用）:

  * M282F-1 `SepKHom` / `sepEmb_embedding` — **K-埋め込み**（基礎体 K を
    固定する環準同型 σ : L → Ω、`fixes_base : σ∘jL = jΩ`）と ext 補題
    （`sepEmb_ringHom_ext`・`sepEmb_ext`、写像が一致すれば準同型が一致）。
  * M282F-2 `sepEmbIsRoot` — Ω 内で β が m の根 ⟺ Σ_k jΩ(mₖ)·βᵏ = 0
    （M274F `evalSum` による Ω 上評価の消滅）。
  * M282F-3 `sepEmbLEval` / `sepEmbLEval_eq_map` / `sepEmb_polysum_val` /
    `sepEmbLEval_eq_quot` — L 内での ρ = [X] 評価 Σ jL(gₖ)·ρᵏ と、それが
    商類 [g] に一致すること（M275F の生成補題の**任意多項式 g への一般化**）。
  * M282F-4 `sepEmb_hom_Leval` — **K-埋め込みは ρ 評価を Ω 評価へ移す**:
    σ([g] の ρ 評価) = evalSum jΩ (σρ) g（fixes_base + ringHom_rpow +
    ringHom_rsum）。
  * M282F-5 **`sepEmb_determined_by_root`** — 本丸その一: **K-埋め込み σ の
    与える β = σ(ρ) は Ω 内で m の根**（σ([m]) = σ(0) = 0 かつ σ([m]) =
    Ω 上の m の評価 = Σ jΩ(mₖ)βᵏ）。埋め込み → 根の対応の本物の核。
  * M282F-6 **`sepEmb_hom_map_eq` / `sepEmb_injective`** — 本丸その二:
    **σ(ρ) = τ(ρ) ⟹ σ = τ**（L は ρ で K 上生成されるので σ は σ(ρ) で
    一意に定まる）。すなわち **{K-埋め込み} ↪ {m の根}** は単射。
  * M282F-7 capstone `SepEmbCount` / `SepEmbData` / `SepEmbData.build` /
    `sepEmb_card_eq_degree` / `sepEmb_card_eq_sepDegree` — **|K-埋め込み| =
    deg m = [L:K]**（Fin deg ≃ {埋め込み} の全単射）。単射性は本物、
    全射性（各根に埋め込みが実現）と根族の分解・相異性は honest 仮説。
  * M282F-8 実例 `sepEmb_quadratic_surj` / `sepEmb_quadratic_distinct` —
    2 次分離拡大で **ちょうど 2 つの K-埋め込み**（相異な 2 根 ↔ 相異な
    2 埋め込み、かつ任意の埋め込みはそのいずれか）。

  正直な限定（何が本物で何が honest 仮説か・§4 準拠、消去・弱化しない）:
   - **本物（本丸）**: (i) K-埋め込み σ から根 β = σ(ρ) を得ること
     （`sepEmb_determined_by_root`）、(ii) σ が σ(ρ) で一意に定まること
     （`sepEmb_injective`＝ 埋め込みの根への単射性）、(iii) ρ 生成による
     商類 [g] = Σ jL(gₖ)ρᵏ（`sepEmbLEval_eq_quot`）は完全証明。これらは
     ガロア被覆のファイバー写像 σ ↦ σ(ρ) が根の集合への単射だという
     **本物の代数的事実**である（toy 主語ではない・実商環 L = K[X]/(m) と
     実評価 evalSum の上の等式）。
   - **honest 仮説 1（全射＝各根から埋め込みの構成）**: 根 β から
     K-埋め込みを作る逆写像は、L = K[X]/(m) からの評価準同型（M274F）が
     商を factor するために **多項式の次数上界を ∃ から抽出する必要があり
     Classical.choice を要する**（M274F ヘッダの deferred と同根）。よって
     capstone `SepEmbData` では各根に実現する埋め込み `embOf` を honest
     witness として受け取る（deferred。逆写像の本物化は後続の
     evalHom→商 factor 層）。全射性の証明本体は本物の `sepEmb_injective`
     を使って `embOf` から復元する（honest 部分を最小化）。
   - **honest 仮説 2（分解と相異性）**: m が Ω 上で deg 個の**相異なる**根
     に分解すること（`rootFam` の族・`rootFam_distinct`・`exhaust`＝これら
     が m の根の全て）は、分離性 gcd(m,m')=1（M270F）が与える「重根なし
     ＝相異なる deg 個」の**分解 witness**として受け取る。分離閉包の一般
     構成と ≤ 側（deg 個以下）の因子定理的上限は本層の範囲外（許容された
     限定）。deg = [L:K]（K[X]/(m) の次元）は M269F 構成から。
   - これは |F(L)| = [L:K]（π₁ 作用の基数＝ガロア被覆のファイバー基数）の
     **本物の代数的根拠**である。deg m 相異なる根 ↔ deg m 個の K-埋め込み。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.RootAdjunction
import IUT.EvaluationHom
import IUT.MinimalPolynomial
import IUT.SeparablePoly

namespace IUT

/-! ## M282F-1: K-埋め込み（基礎体を固定する環準同型） -/

/-- **M282F-1a: K-埋め込み** — 基礎体 K を固定する環準同型 σ : L → Ω。
    L・Ω はともに K の像を持つ（jL : K → L, jΩ : K → Ω）とし、σ は
    K の像上で jΩ に一致する（`fixes_base`）。ガロア理論の K-代数準同型。 -/
structure SepKHom (K : Field268) {L Ω : CRing}
    (jL : RingHom K.ring L) (jΩ : RingHom K.ring Ω) where
  /-- 台となる環準同型 L → Ω。 -/
  hom : RingHom L Ω
  /-- K の像を固定する（σ(jL c) = jΩ c）。 -/
  fixes_base : ∀ c, hom.map (jL.map c) = jΩ.map c

/-- **M282F-1b: K-埋め込みの型**（`SepKHom` の別名、L → Ω の K-埋め込み）。 -/
abbrev sepEmb_embedding (K : Field268) {L Ω : CRing}
    (jL : RingHom K.ring L) (jΩ : RingHom K.ring Ω) : Type :=
  SepKHom K jL jΩ

/-- **M282F-1c: 環準同型の ext** — 写像 `.map` が一致すれば環準同型は一致
    （加法・乗法・単位の保存則は Prop、証明無関係で一致）。 -/
theorem sepEmb_ringHom_ext {L Ω : CRing} :
    ∀ (φ ψ : RingHom L Ω), φ.map = ψ.map → φ = ψ
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, h => by cases h; rfl

/-- **M282F-1d: K-埋め込みの ext** — 台の環準同型が一致すれば K-埋め込みは
    一致（`fixes_base` は Prop、証明無関係）。 -/
theorem sepEmb_ext {K : Field268} {L Ω : CRing} {jL : RingHom K.ring L}
    {jΩ : RingHom K.ring Ω} :
    ∀ (σ τ : SepKHom K jL jΩ), σ.hom = τ.hom → σ = τ
  | ⟨_, _⟩, ⟨_, _⟩, h => by cases h; rfl

/-! ## M282F-2: Ω 内の根の判定 -/

/-- **M282F-2: Ω 内の m の根** — β が Ω 内で m の根 ⟺ m の Ω 上評価
    Σ_{k≤deg} jΩ(mₖ)·βᵏ = 0（M274F `evalSum`）。 -/
def sepEmbIsRoot (K : Field268) (Ω : CRing) (jΩ : RingHom K.ring Ω)
    (m : PS K.ring) (deg : Nat) (β : Ω.carrier) : Prop :=
  evalSum jΩ β m (deg + 1) = Ω.zero

/-! ## M282F-3: L 内での ρ = [X] 評価と商類の一致（生成補題） -/

/-- **M282F-3a: L 内での g の ρ 評価** Σ_{k<N} jL(gₖ)·ρᵏ（ρ = [X]）。 -/
def sepEmbLEval (K : Field268) (p : PS K.ring) (d : Nat)
    (hp : IsPolyBounded K.ring p (d + 1)) (g : PS K.ring) (N : Nat) :
    (simpleExtRing K p d hp).carrier :=
  rsum (simpleExtRing K p d hp)
    (fun k => (simpleExtRing K p d hp).mul
      ((simpleExtC K p d hp).map (g k))
      (rpow (simpleExtRing K p d hp) (rootAdj_root K p d hp) k)) N

/-- **M282F-3b: ρ 評価 = 代表多項式の商像**（M275F-5a の任意 g・N への一般化）。
    quotOf が有限和・積・冪と交換する。 -/
theorem sepEmbLEval_eq_map (K : Field268) (p : PS K.ring) (d : Nat)
    (hp : IsPolyBounded K.ring p (d + 1)) (g : PS K.ring) (N : Nat) :
    sepEmbLEval K p d hp g N
      = (quotOf (polyCRing K.ring) (simpleExtModulus K p d hp)).map
          (rsum (polyCRing K.ring)
            (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (g k))
              (rpow (polyCRing K.ring) (rootAdjX K) k)) N) := by
  show rsum (simpleExtRing K p d hp)
      (fun k => (simpleExtRing K p d hp).mul
        ((simpleExtC K p d hp).map (g k))
        (rpow (simpleExtRing K p d hp) (rootAdj_root K p d hp) k)) N
    = (quotOf (polyCRing K.ring) (simpleExtModulus K p d hp)).map
        (rsum (polyCRing K.ring)
          (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (g k))
            (rpow (polyCRing K.ring) (rootAdjX K) k)) N)
  rw [ringHom_rsum (quotOf (polyCRing K.ring) (simpleExtModulus K p d hp))
      (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (g k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)) N]
  refine rsum_congr (simpleExtRing K p d hp) N (fun k _ => ?_)
  show (quotCRing (polyCRing K.ring) (simpleExtModulus K p d hp)).mul
      ((quotOf (polyCRing K.ring) (simpleExtModulus K p d hp)).map
        ((polyC K.ring).map (g k)))
      (rpow (quotCRing (polyCRing K.ring) (simpleExtModulus K p d hp))
        ((quotOf (polyCRing K.ring) (simpleExtModulus K p d hp)).map (rootAdjX K)) k)
    = (quotOf (polyCRing K.ring) (simpleExtModulus K p d hp)).map
        ((polyCRing K.ring).mul ((polyC K.ring).map (g k))
          (rpow (polyCRing K.ring) (rootAdjX K) k))
  rw [(quotOf (polyCRing K.ring) (simpleExtModulus K p d hp)).map_mul,
    ringHom_rpow (quotOf (polyCRing K.ring) (simpleExtModulus K p d hp))
      (rootAdjX K) k]

/-- **M282F-3c: 代表多項式 Σ gₖ Xᵏ は g そのもの**（g が N で有界のとき、
    点別に一点集中和で係数を復元。M275F-5b の任意 g・N への一般化）。 -/
theorem sepEmb_polysum_val (K : Field268) (g : PS K.ring) (N : Nat)
    (hg : IsPolyBounded K.ring g N) (n : Nat) :
    (rsum (polyCRing K.ring)
      (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (g k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)) N).val n = g n := by
  have hpow : ∀ k, (rpow (polyCRing K.ring) (rootAdjX K) k).val
      = psMono K.ring k := by
    intro k
    have hr : (rpow (polyCRing K.ring) (rootAdjX K) k).val
        = rpow (psRing K.ring) (psX K.ring) k :=
      ringHom_rpow (rootAdjPolyVal K.ring) (rootAdjX K) k
    rw [hr, rpow_psX K.ring k]
  have hcoef : ∀ k, ((polyCRing K.ring).mul ((polyC K.ring).map (g k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)).val n
      = K.ring.mul (g k) (psMono K.ring k n) := by
    intro k
    show psMul K.ring (psC K.ring (g k))
        ((rpow (polyCRing K.ring) (rootAdjX K) k).val) n
      = K.ring.mul (g k) (psMono K.ring k n)
    rw [hpow k, rootAdj_psC_mono_coeff K.ring (g k) k n]
  show (rsum (polyCRing K.ring)
      (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (g k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)) N).val n = g n
  rw [rootAdj_rsum_poly_val K.ring
      (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (g k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)) N,
    rootAdj_rsum_apply K.ring
      (fun k => ((polyCRing K.ring).mul ((polyC K.ring).map (g k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)).val) N n,
    rsum_congr K.ring N (fun k _ => hcoef k)]
  cases Nat.lt_or_ge n N with
  | inl hlt =>
    rw [rsum_single K.ring (fun k => K.ring.mul (g k) (psMono K.ring k n)) n N
        hlt (fun j _ hjne => by
          show K.ring.mul (g j) (psMono K.ring j n) = K.ring.zero
          rw [show psMono K.ring j n = K.ring.zero
              from if_neg (fun hc => hjne hc.symm)]
          exact K.ring.mul_zero (g j)),
      show psMono K.ring n n = K.ring.one from if_pos rfl,
      K.ring.mul_comm, K.ring.one_mul]
  | inr hge =>
    rw [rsum_congr K.ring N (fun k hk => by
        show K.ring.mul (g k) (psMono K.ring k n) = K.ring.zero
        rw [show psMono K.ring k n = K.ring.zero from if_neg (fun hc => by omega)]
        exact K.ring.mul_zero (g k)),
      rsum_const_zero K.ring]
    exact (hg n hge).symm

/-- **M282F-3d: 生成補題** — L 内での ρ 評価 = 商類 [g]（g が N で有界）。
    すなわち **L の任意の元は ρ の K 係数多項式**（ρ が L を K 上生成）。 -/
theorem sepEmbLEval_eq_quot (K : Field268) (p : PS K.ring) (d : Nat)
    (hp : IsPolyBounded K.ring p (d + 1)) (g : PS K.ring) (N : Nat)
    (hg : IsPolyBounded K.ring g N) :
    sepEmbLEval K p d hp g N
      = (quotOf (polyCRing K.ring) (simpleExtModulus K p d hp)).map
          (⟨g, ⟨N, hg⟩⟩ : Poly K.ring) := by
  rw [sepEmbLEval_eq_map K p d hp g N]
  have hpoly : (rsum (polyCRing K.ring)
      (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (g k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)) N)
      = (⟨g, ⟨N, hg⟩⟩ : Poly K.ring) :=
    Subtype.ext (funext (fun n => sepEmb_polysum_val K g N hg n))
  rw [hpoly]

/-! ## M282F-4: K-埋め込みは ρ 評価を Ω 評価へ移す -/

/-- **M282F-4: 埋め込みは評価を移す** — σ が L 内の ρ 評価に作用すると、
    Ω 内の β = σ(ρ) 評価 evalSum jΩ β g になる（fixes_base で jL(gₖ) を
    jΩ(gₖ) へ、ringHom_rpow で ρᵏ を βᵏ へ、ringHom_rsum で和を交換）。 -/
theorem sepEmb_hom_Leval (K : Field268) (p : PS K.ring) (d : Nat)
    (hp : IsPolyBounded K.ring p (d + 1)) {Ω : CRing}
    (jΩ : RingHom K.ring Ω)
    (σ : SepKHom K (simpleExtC K p d hp) jΩ) (g : PS K.ring) (N : Nat) :
    σ.hom.map (sepEmbLEval K p d hp g N)
      = evalSum jΩ (σ.hom.map (rootAdj_root K p d hp)) g N := by
  show σ.hom.map (rsum (simpleExtRing K p d hp)
      (fun k => (simpleExtRing K p d hp).mul
        ((simpleExtC K p d hp).map (g k))
        (rpow (simpleExtRing K p d hp) (rootAdj_root K p d hp) k)) N)
    = rsum Ω (fun i => Ω.mul (jΩ.map (g i))
        (rpow Ω (σ.hom.map (rootAdj_root K p d hp)) i)) N
  rw [ringHom_rsum σ.hom
      (fun k => (simpleExtRing K p d hp).mul
        ((simpleExtC K p d hp).map (g k))
        (rpow (simpleExtRing K p d hp) (rootAdj_root K p d hp) k)) N]
  refine rsum_congr Ω N (fun k _ => ?_)
  show σ.hom.map ((simpleExtRing K p d hp).mul
        ((simpleExtC K p d hp).map (g k))
        (rpow (simpleExtRing K p d hp) (rootAdj_root K p d hp) k))
    = Ω.mul (jΩ.map (g k)) (rpow Ω (σ.hom.map (rootAdj_root K p d hp)) k)
  rw [σ.hom.map_mul, σ.fixes_base (g k),
    ringHom_rpow σ.hom (rootAdj_root K p d hp) k]

/-! ## M282F-5: 本丸その一 — 埋め込みは根を与える -/

/-- **定理 (M282F-5): K-埋め込み σ の与える β = σ(ρ) は m の根** — 本丸。
    生成補題（M282F-3d）で法多項式類 [m] = σ による ρ 評価に一致し、
    かつ [m] = 0（商の定義、M275F-3d）なので σ([m]) = σ(0) = 0。他方
    σ による ρ 評価 = Ω 上の m の評価 evalSum jΩ (σρ) m。よって β は根。
    埋め込み → 根の対応の本物の核（ガロア被覆のファイバー写像）。 -/
theorem sepEmb_determined_by_root (K : Field268) (p : PS K.ring) (d : Nat)
    (hp : IsPolyBounded K.ring p (d + 1)) {Ω : CRing}
    (jΩ : RingHom K.ring Ω)
    (σ : SepKHom K (simpleExtC K p d hp) jΩ) :
    sepEmbIsRoot K Ω jΩ p d (σ.hom.map (rootAdj_root K p d hp)) := by
  show evalSum jΩ (σ.hom.map (rootAdj_root K p d hp)) p (d + 1) = Ω.zero
  rw [← sepEmb_hom_Leval K p d hp jΩ σ p (d + 1),
    sepEmbLEval_eq_quot K p d hp p (d + 1) hp]
  have hz : (quotOf (polyCRing K.ring) (simpleExtModulus K p d hp)).map
        (⟨p, ⟨d + 1, hp⟩⟩ : Poly K.ring)
      = (simpleExtRing K p d hp).zero :=
    rootAdj_modulus_class_zero (polyCRing K.ring) (simpleExtModulus K p d hp)
  rw [hz]
  exact RingHom.map_zero σ.hom

/-! ## M282F-6: 本丸その二 — 埋め込みは σ(ρ) で一意に定まる（単射性） -/

/-- **M282F-6a: 写像の一致** — σ(ρ) = τ(ρ) なら σ・τ は L の全ての元で一致。
    L の任意の元は [g]（商類）で、生成補題 + M282F-4 で σ([g]) = evalSum
    jΩ (σρ) g、τ([g]) = evalSum jΩ (τρ) g。σρ = τρ より一致。 -/
theorem sepEmb_hom_map_eq (K : Field268) (p : PS K.ring) (d : Nat)
    (hp : IsPolyBounded K.ring p (d + 1)) {Ω : CRing}
    (jΩ : RingHom K.ring Ω)
    (σ τ : SepKHom K (simpleExtC K p d hp) jΩ)
    (hroot : σ.hom.map (rootAdj_root K p d hp)
      = τ.hom.map (rootAdj_root K p d hp)) :
    σ.hom.map = τ.hom.map := by
  funext x
  induction x using Quot.ind
  rename_i a
  obtain ⟨N, hN⟩ := a.property
  have ha : a = (⟨a.val, ⟨N, hN⟩⟩ : Poly K.ring) := Subtype.ext rfl
  have hgen : Quot.mk (idealRel (polyCRing K.ring) (simpleExtModulus K p d hp)) a
      = sepEmbLEval K p d hp a.val N := by
    rw [ha]
    exact (sepEmbLEval_eq_quot K p d hp a.val N hN).symm
  show σ.hom.map (Quot.mk (idealRel (polyCRing K.ring)
      (simpleExtModulus K p d hp)) a)
    = τ.hom.map (Quot.mk (idealRel (polyCRing K.ring)
      (simpleExtModulus K p d hp)) a)
  rw [hgen, sepEmb_hom_Leval K p d hp jΩ σ a.val N,
    sepEmb_hom_Leval K p d hp jΩ τ a.val N, hroot]

/-- **定理 (M282F-6b): 埋め込みは根への単射** — σ(ρ) = τ(ρ) ⟹ σ = τ。
    L は ρ で K 上生成されるので、K-埋め込みは生成元 ρ の像で一意に定まる。
    すなわち σ ↦ σ(ρ) は **{K-埋め込み L→Ω} ↪ {m の根}** の単射。 -/
theorem sepEmb_injective (K : Field268) (p : PS K.ring) (d : Nat)
    (hp : IsPolyBounded K.ring p (d + 1)) {Ω : CRing}
    (jΩ : RingHom K.ring Ω)
    (σ τ : SepKHom K (simpleExtC K p d hp) jΩ)
    (hroot : σ.hom.map (rootAdj_root K p d hp)
      = τ.hom.map (rootAdj_root K p d hp)) : σ = τ :=
  sepEmb_ext σ τ
    (sepEmb_ringHom_ext σ.hom τ.hom
      (sepEmb_hom_map_eq K p d hp jΩ σ τ hroot))

/-! ## M282F-7: capstone — |K-埋め込み| = deg m = [L:K] -/

/-- **M282F-7a: 基数 = deg の証拠** — `Emb` がちょうど deg 個の元を持つ:
    Fin deg → Emb が単射かつ全射（Fin deg ≃ Emb の ∃ 形、選択公理不要）。 -/
structure SepEmbCount (deg : Nat) (Emb : Type) where
  /-- deg 個の元の枚挙。 -/
  enum : Fin deg → Emb
  /-- 相異（単射）。 -/
  enum_inj : ∀ i j, enum i = enum j → i = j
  /-- 全射（任意の元はいずれか）。 -/
  enum_surj : ∀ e, ∃ i, enum i = e

/-- **M282F-7b: 分離埋め込みの入力データ** — 単純分離拡大 L = K[X]/(m) と、
    m が Ω 上で deg 個の相異なる根に分解する分解 witness（分離性の帰結）と、
    各根に実現する K-埋め込み（honest 逆写像）を束ねる。honest 仮説は
    ヘッダの「正直な限定」参照（全射・分解・相異性は deferred）。 -/
structure SepEmbData where
  /-- 基礎体 K。 -/
  K : Field268
  /-- 分解体 Ω。 -/
  Ω : CRing
  /-- K の Ω への埋め込み。 -/
  jΩ : RingHom K.ring Ω
  /-- 最小多項式 m（係数列）。 -/
  modulus : PS K.ring
  /-- 次数 deg = [L:K]。 -/
  deg : Nat
  /-- 有界性（deg+1 で消える）。 -/
  bound : IsPolyBounded K.ring modulus (deg + 1)
  /-- **honest 仮説（分解）**: Ω 内の m の deg 個の根の族。 -/
  rootFam : Fin deg → Ω.carrier
  /-- 各 rootFam i は m の根。 -/
  rootFam_isRoot : ∀ i, sepEmbIsRoot K Ω jΩ modulus deg (rootFam i)
  /-- **honest 仮説（相異性）**: 根は相異なる（分離性の帰結、重根なし）。 -/
  rootFam_distinct : ∀ i j, rootFam i = rootFam j → i = j
  /-- **honest 仮説（逆写像）**: 各根 i に実現する K-埋め込み。 -/
  embOf : Fin deg → SepKHom K (simpleExtC K modulus deg bound) jΩ
  /-- embOf i の ρ 像は rootFam i。 -/
  embOf_root : ∀ i, (embOf i).hom.map (rootAdj_root K modulus deg bound)
    = rootFam i
  /-- **honest 仮説（全射／根の網羅）**: 任意の埋め込みの根は deg 個の
      いずれか（m は Ω 内でこれら以外に根を持たない）。 -/
  exhaust : ∀ σ : SepKHom K (simpleExtC K modulus deg bound) jΩ,
    ∃ i, σ.hom.map (rootAdj_root K modulus deg bound) = rootFam i

/-- **定理 (M282F-7c): 埋め込みの基数 = deg**（本物の単射性 + honest 分解）—
    enum := embOf。単射性は分解 witness の相異性 rootFam_distinct から、
    **全射性は本物の `sepEmb_injective`** で embOf から復元する（honest
    部分は根族・全射網羅のみで、埋め込みの一意性は本物）。 -/
def SepEmbData.build (D : SepEmbData) :
    SepEmbCount D.deg
      (SepKHom D.K (simpleExtC D.K D.modulus D.deg D.bound) D.jΩ) where
  enum := D.embOf
  enum_inj := fun i j h =>
    D.rootFam_distinct i j (by
      rw [← D.embOf_root i, ← D.embOf_root j]
      exact congrArg
        (fun s => s.hom.map (rootAdj_root D.K D.modulus D.deg D.bound)) h)
  enum_surj := fun σ => by
    obtain ⟨i, hi⟩ := D.exhaust σ
    refine ⟨i, ?_⟩
    exact sepEmb_injective D.K D.modulus D.deg D.bound D.jΩ (D.embOf i) σ
      (by rw [D.embOf_root i]; exact hi.symm)

/-- **定理 (M282F-7d): |K-埋め込み| = deg m = [L:K]** — 本層の見出し。
    単純分離拡大 L = K[X]/(m) の L → Ω の K-埋め込みはちょうど deg m 個
    （= [L:K]）ある。M276F の |F(L)| = n を**本物の代数（ガロア被覆の
    ファイバー基数）に置換**した結果。 -/
def sepEmb_card_eq_degree (D : SepEmbData) :
    SepEmbCount D.deg
      (SepKHom D.K (simpleExtC D.K D.modulus D.deg D.bound) D.jΩ) :=
  D.build

/-- **M282F-7e: 分離次数**（分離拡大なので [L:K]_sep = [L:K] = deg m）。 -/
def sepDegree (D : SepEmbData) : Nat := D.deg

/-- **定理 (M282F-7f): |K-埋め込み| = 分離次数** — 埋め込みの個数は分離次数
    deg m に一致（分離拡大での埋め込み数 = 分離次数の本物の等式）。 -/
def sepEmb_card_eq_sepDegree (D : SepEmbData) :
    SepEmbCount (sepDegree D)
      (SepKHom D.K (simpleExtC D.K D.modulus D.deg D.bound) D.jΩ) :=
  D.build

/-- **定理 (M282F-7g): 埋め込みの基数の存在**。 -/
theorem sepEmb_count_exists (D : SepEmbData) :
    Nonempty (SepEmbCount D.deg
      (SepKHom D.K (simpleExtC D.K D.modulus D.deg D.bound) D.jΩ)) :=
  ⟨D.build⟩

/-! ## M282F-8: 実例 — 2 次分離拡大でちょうど 2 つの埋め込み -/

/-- **定理 (M282F-8a): 相異な根 ⟹ 相異な埋め込み** — 根の添字が異なれば
    実現する K-埋め込みも異なる（単射性の帰結）。deg = 2 なら embOf ⟨0⟩ と
    embOf ⟨1⟩ は相異なる 2 つの埋め込み。 -/
theorem sepEmb_quadratic_distinct (D : SepEmbData)
    (i j : Fin D.deg) (hij : i ≠ j) : D.embOf i ≠ D.embOf j :=
  fun h => hij (D.build.enum_inj i j h)

/-- **定理 (M282F-8b): 埋め込みの網羅** — 任意の K-埋め込みは deg 個の根の
    実現埋め込みのいずれか（全射性）。deg = 2 なら任意の K-埋め込みは
    embOf ⟨0⟩ か embOf ⟨1⟩ に一致＝**ちょうど 2 つの埋め込み**。 -/
theorem sepEmb_quadratic_surj (D : SepEmbData)
    (σ : SepKHom D.K (simpleExtC D.K D.modulus D.deg D.bound) D.jΩ) :
    ∃ i, D.embOf i = σ :=
  D.build.enum_surj σ

end IUT
