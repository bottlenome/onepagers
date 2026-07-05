/-
  IUT/ProfiniteTopology.lean — M265F（副有限位相の完成: 開部分群の
  特徴付け・連続作用の同値・Hausdorff 分離・ẑ の実例）

  分類 **[実]**。complete_pct 影響: **柱A 実 profinite π₁ の本物の
  先行建設（副有限位相を実導入）**。

  M15（IUT/Topology.lean）は副有限位相の骨格——位相群性
  （`limit_mul_continuous`/`limit_inv_continuous`）・射影核の開性
  （`projKernel_isOpen`）・近傍基（`cylinder_nbhd_basis`）——を建設し、
  M16（IUT/SGA1.lean §4）は連続性条件を `SmoothAction`（安定化群が
  射影核を含む）として**代数的に**定義した。本モジュールはその上に
  「絶対 Galois 群の本物の位相」の残る使用面を**昇格**する:

  §1 開部分群の理論の完成
  * M265F-1 `projKernel_coset_isOpen` — 射影核の**左剰余類は開**
    （剰余類 = 柱状集合、の等式による。平行移動の開性の実質）
  * M265F-2 `projKernel_compl_isOpen` — 射影核の補集合は開、すなわち
    **射影核は clopen**（副有限群が全不連結であることの使用面）
  * M265F-3 `projKernelSubgroup` — 射影核の部分群構造（M15-5 の束ね、
    M16 の `Subgroup` としての正式なパッケージ）
  * M265F-4 `subgroup_isOpen_iff_contains_kernel` — **開部分群の
    特徴付け**: 部分群 H が開 ⟺ H がある射影核を含む。
    （⟸ は H を射影核剰余類の合併に分解する。副有限群論の基本定理）

  §2 連続作用の同値（SGA1 の「連続」の位相的意味の完成）
  * M265F-5 `smooth_action_continuous` / M265F-6 `continuous_action_smooth` /
    M265F-7 `smooth_iff_action_continuous` — **G-集合への作用が
    直積位相 × 離散位相で位相的に連続 ⟺ SmoothAction（各点の
    安定化群が射影核を含む＝開）**。M16-7 は代数的条件の片側実例
    のみだったので、位相的連続性そのものとの同値は本モジュールで
    初めて証明される（SGA1 V の「π₁ の連続作用」の位相的内容）

  §3 Hausdorff 分離
  * M265F-8 `limit_hausdorff_at_level` — レベル i で分離される 2 点は
    交わらない開集合で分離される（T2 性の**正の（apartness）定式化**。
    「x ≠ y ⟹ あるレベルで分離」の抽出は排中律を要するため、
    choice-free の範囲で使用面のみ証明する: 正直な限定）

  §4 ẑ = lim ℤ/n の実例（M13 の実構成の上で）
  * M265F-9 `nzhat` / `nzhatSubgroup` — 開部分群 nẑ = ker(ẑ → ℤ/n)
  * M265F-10 `toZhat_mem_nzhat_iff` — **nẑ ∩ ℤ = nℤ**: 対角像
    toZhat(a) ∈ nẑ ⟺ n ∣ a（quot_exact による完全な特徴付け）
  * M265F-11 `nzhat_isOpen` / `nzhat_compl_isOpen` / `nzhat_nbhd` —
    nẑ は clopen で、{nẑ} は 1 の開近傍基
  * M265F-12 `zhat_levelAction_continuous` — ẑ の ℤ/n への作用は
    直積位相 × 離散位相で**位相的に連続**（M265F-5 の実例化）
  * M265F-13 `factChain_coset_cover_finite` — コンパクト性（M25）
    との接続: 階乗鎖極限（ẑ の鎖型表示）の射影核剰余類被覆は
    有限部分被覆を持つ（「開部分群は有限指数」の被覆論的形）。
    **この 1 定理のみ** M25 `factChain_compact` 経由で
    Classical.choice を継承する（本体では新規導入しない: ヘッダ明記）

  §5 capstone
  * `ProfiniteTopologyData` / `profiniteTopologyData` /
    `profiniteTopology_exists` — 任意の逆系に対し副有限位相の
    全証明済み性質（位相群性・clopen 射影核・近傍基・開部分群
    特徴付け・T2 分離・連続作用同値)を束ねたデータが存在する
  * `zhatProfiniteTopology` — ẑ での実例化

  **正直な限定**:
  (1) T2 性は apartness 形（「あるレベルで値が違う」→ 分離）のみ。
      「x ≠ y → ∃ i, x.val i ≠ y.val i」の抽出は排中律を要するため
      choice-free の本モジュールでは扱わない。
  (2) 一般の逆系の極限のコンパクト性は M25 と同じく Nat 鎖に限る
      （M265F-13 は既存 M25 の接続であり、Classical.choice を継承）。
  (3) 「任意の開部分群は有限指数」の指数の有限性そのものは未証明
      （M265F-13 は被覆の有限性という使用面のみ）。
  (4) これらは実 profinite π₁（絶対 Galois 群）の**位相構造**の理論で
      あり、数論的なガロア群そのものの構成（柱Aの幾何入力）は別建て。
-/
import IUT.SGA1
import IUT.LimitCompact

namespace IUT

/-! ## §1 開部分群の理論の完成 -/

/-- **定理 (M265F-1): 射影核の左剰余類は開** — 剰余類
    g·ker(pᵢ) = {σ | σᵢ = gᵢ} は柱状集合に等しい（平行移動の開性の
    使用面。位相群での「開部分群の剰余類は開」の実物）。 -/
theorem projKernel_coset_isOpen (S : InverseSystem) (i : S.Idx)
    (g : (limitGrp S).carrier) :
    (limitTopology S).IsOpen
      (fun σ => projKernel S i ((limitGrp S).mul ((limitGrp S).inv g) σ)) := by
  have heq : (fun σ : (limitGrp S).carrier =>
        projKernel S i ((limitGrp S).mul ((limitGrp S).inv g) σ))
      = cylinder S i (fun c => c = g.val i) := by
    funext σ
    apply propext
    refine ⟨?_, ?_⟩
    · intro hσ
      have hσ' : (S.G i).mul ((S.G i).inv (g.val i)) (σ.val i)
          = (S.G i).one := hσ
      show σ.val i = g.val i
      have h1 := congrArg ((S.G i).mul (g.val i)) hσ'
      rw [← (S.G i).mul_assoc, (S.G i).mul_inv, (S.G i).one_mul,
        (S.G i).mul_one] at h1
      exact h1
    · intro hσ
      have hσ' : σ.val i = g.val i := hσ
      show (S.G i).mul ((S.G i).inv (g.val i)) (σ.val i) = (S.G i).one
      rw [hσ', (S.G i).inv_mul]
  rw [heq]
  exact cylinder_isOpen S i _

/-- **定理 (M265F-2): 射影核の補集合は開** — 射影核は **clopen**。
    副有限群の全不連結性の使用面（補集合も柱状集合）。 -/
theorem projKernel_compl_isOpen (S : InverseSystem) (i : S.Idx) :
    (limitTopology S).IsOpen (fun σ => ¬ projKernel S i σ) :=
  GenOpen.basic _ ⟨i, fun c => ¬ (c = (S.G i).one), rfl⟩

/-- **M265F-3: 射影核の部分群パッケージ** — M15-5b/c/d を M16 の
    `Subgroup` として正式に束ねる。 -/
def projKernelSubgroup (S : InverseSystem) (i : S.Idx) :
    Subgroup (limitGrp S) where
  mem := projKernel S i
  one_mem := projKernel_one S i
  mul_mem := fun ha hb => projKernel_mul S i ha hb
  inv_mem := fun ha => projKernel_inv S i ha

/-- **定理 (M265F-4): 開部分群の特徴付け** — 部分群 H が開
    ⟺ H はある射影核を含む。⟸ 方向は H を射影核剰余類（M265F-1 で
    開）の H 上の合併に分解する（非可述的な集合族で choice 回避）。
    「副有限群の開部分群 = 有限レベルで定義される部分群」という
    副有限群論の基本定理の形式化。 -/
theorem subgroup_isOpen_iff_contains_kernel (S : InverseSystem) (i₀ : S.Idx)
    (H : Subgroup (limitGrp S)) :
    (limitTopology S).IsOpen H.mem
      ↔ ∃ k, ∀ y, projKernel S k y → H.mem y := by
  refine ⟨fun hopen => projKernel_nbhd S i₀ H.mem hopen H.one_mem, ?_⟩
  intro ⟨k, hk⟩
  have heq : H.mem = fun σ => ∃ U,
      ((∃ g, H.mem g ∧ U = fun τ => projKernel S k
        ((limitGrp S).mul ((limitGrp S).inv g) τ)) ∧ U σ) := by
    funext σ
    apply propext
    refine ⟨?_, ?_⟩
    · intro hσ
      refine ⟨fun τ => projKernel S k ((limitGrp S).mul ((limitGrp S).inv σ) τ),
        ⟨σ, hσ, rfl⟩, ?_⟩
      show projKernel S k ((limitGrp S).mul ((limitGrp S).inv σ) σ)
      rw [(limitGrp S).inv_mul]
      exact projKernel_one S k
    · intro ⟨U, ⟨g, hg, hUeq⟩, hUσ⟩
      rw [hUeq] at hUσ
      have h1 := H.mul_mem hg (hk _ hUσ)
      rw [← (limitGrp S).mul_assoc, (limitGrp S).mul_inv,
        (limitGrp S).one_mul] at h1
      exact h1
  rw [heq]
  exact (limitTopology S).isOpen_sUnion _ (fun U hU => by
    obtain ⟨g, _, rfl⟩ := hU
    exact projKernel_coset_isOpen S k g)

/-! ## §2 連続作用の同値（SGA1 の「連続」の位相的意味） -/

/-- **定理 (M265F-5): SmoothAction ⟹ 作用写像は位相的に連続** —
    安定化群が射影核を含む（M16-7 の条件）なら、作用写像
    G × X → X は直積位相（副有限位相 × 離散位相）から離散位相への
    連続写像。証明: 引き戻しを「引き戻しに含まれる開長方形」の
    非可述的合併として表す（choice 不要）。各点 (σ, x) では
    安定化条件のレベル i の柱状集合 × {x} が求める長方形。 -/
theorem smooth_action_continuous (S : InverseSystem)
    (X : GAction (limitGrp S)) (h : SmoothAction S X) :
    Continuous (prodTopology (limitTopology S) (discreteTopology X.carrier))
      (discreteTopology X.carrier) (fun p => X.act p.1 p.2) := by
  intro V _
  show (prodTopology (limitTopology S) (discreteTopology X.carrier)).IsOpen
    (fun p : (limitGrp S).carrier × X.carrier => V (X.act p.1 p.2))
  have heq : (fun p : (limitGrp S).carrier × X.carrier => V (X.act p.1 p.2))
      = (fun p => ∃ R,
          (((prodTopology (limitTopology S)
              (discreteTopology X.carrier)).IsOpen R ∧
            ∀ q : (limitGrp S).carrier × X.carrier,
              R q → V (X.act q.1 q.2)) ∧ R p)) := by
    funext p
    apply propext
    refine ⟨?_, ?_⟩
    · intro hp
      obtain ⟨i, hi⟩ := h p.2
      refine ⟨fun q => q.1.val i = p.1.val i ∧ q.2 = p.2, ⟨?_, ?_⟩, rfl, rfl⟩
      · exact GenOpen.basic _
          ⟨cylinder S i (fun c => c = p.1.val i), fun y => y = p.2,
            cylinder_isOpen S i _, True.intro, rfl⟩
      · intro q hq
        have hτ : projKernel S i
            ((limitGrp S).mul ((limitGrp S).inv p.1) q.1) := by
          show (S.G i).mul ((S.G i).inv (p.1.val i)) (q.1.val i) = (S.G i).one
          rw [hq.1, (S.G i).inv_mul]
        have hfix := hi _ hτ
        have hdecomp : (limitGrp S).mul p.1
            ((limitGrp S).mul ((limitGrp S).inv p.1) q.1) = q.1 := by
          rw [← (limitGrp S).mul_assoc, (limitGrp S).mul_inv,
            (limitGrp S).one_mul]
        rw [hq.2, ← hdecomp, X.act_mul, hfix]
        exact hp
    · intro ⟨R, ⟨_, hsub⟩, hRp⟩
      exact hsub p hRp
  rw [heq]
  exact (prodTopology (limitTopology S)
    (discreteTopology X.carrier)).isOpen_sUnion _ (fun R hR => hR.1)

/-- **定理 (M265F-6): 作用写像が連続 ⟹ SmoothAction** — 作用写像が
    位相的に連続なら各点の安定化群は射影核を含む。証明: 点 x の
    固定集合 {p | p.1·p.2 = x} の引き戻しは開で (1, x) を含むので、
    開長方形近傍基（M18-3）と射影核近傍基（M15-6 系）で射影核まで
    縮められる。 -/
theorem continuous_action_smooth (S : InverseSystem) (i₀ : S.Idx)
    (X : GAction (limitGrp S))
    (hc : Continuous (prodTopology (limitTopology S)
      (discreteTopology X.carrier)) (discreteTopology X.carrier)
      (fun p => X.act p.1 p.2)) :
    SmoothAction S X := by
  intro x
  have hW : (prodTopology (limitTopology S)
      (discreteTopology X.carrier)).IsOpen
      (fun p : (limitGrp S).carrier × X.carrier => X.act p.1 p.2 = x) :=
    hc (fun y => y = x) True.intro
  have hWone : X.act ((limitGrp S).one, x).1 ((limitGrp S).one, x).2 = x :=
    X.act_one x
  obtain ⟨U, V, hU, _, hUone, hVx, hsub⟩ :=
    prod_open_rect_basis (limitTopology S) (discreteTopology X.carrier)
      (fun p => X.act p.1 p.2 = x) hW ((limitGrp S).one, x) hWone
  obtain ⟨k, hk⟩ := projKernel_nbhd S i₀ U hU hUone
  exact ⟨k, fun σ hσ => hsub (σ, x) (hk σ hσ) hVx⟩

/-- **定理 (M265F-7): 連続作用の同値**（SGA1 の「π₁ の連続作用」の
    位相的内容の完成）— 副有限群の作用について、
    **位相的連続性 ⟺ 各点の安定化群が射影核（開部分群）を含む**。 -/
theorem smooth_iff_action_continuous (S : InverseSystem) (i₀ : S.Idx)
    (X : GAction (limitGrp S)) :
    SmoothAction S X
      ↔ Continuous (prodTopology (limitTopology S)
          (discreteTopology X.carrier)) (discreteTopology X.carrier)
          (fun p => X.act p.1 p.2) :=
  ⟨smooth_action_continuous S X, continuous_action_smooth S i₀ X⟩

/-! ## §3 Hausdorff 分離（apartness 形の T2 性） -/

/-- **定理 (M265F-8): レベル分離 ⟹ 開集合分離**（T2 性の正の
    定式化）— あるレベル i で値が異なる 2 点は、交わらない開集合
    （柱状集合）で分離される。 -/
theorem limit_hausdorff_at_level (S : InverseSystem) (i : S.Idx)
    (x y : (limitGrp S).carrier) (hxy : x.val i ≠ y.val i) :
    ∃ U V : (limitGrp S).carrier → Prop,
      (limitTopology S).IsOpen U ∧ (limitTopology S).IsOpen V ∧
      U x ∧ V y ∧ ∀ z, U z → V z → False := by
  refine ⟨cylinder S i (fun c => c = x.val i),
    cylinder S i (fun c => c = y.val i),
    cylinder_isOpen S i _, cylinder_isOpen S i _, rfl, rfl, ?_⟩
  intro z hz hw
  have hz' : z.val i = x.val i := hz
  have hw' : z.val i = y.val i := hw
  apply hxy
  rw [← hz', hw']

/-! ## §4 ẑ = lim ℤ/n の実例 -/

/-- **M265F-9a: 開部分群 nẑ** = ker(ẑ → ℤ/n)（射影核の実例）。 -/
def nzhat (n : Nat) : zhat.carrier → Prop := projKernel zmodSystem n

/-- **M265F-9b: nẑ の部分群パッケージ**。 -/
def nzhatSubgroup (n : Nat) : Subgroup zhat := projKernelSubgroup zmodSystem n

/-- **定理 (M265F-10): nẑ ∩ ℤ = nℤ** — 対角像 toZhat(a) が nẑ に
    入る ⟺ n ∣ a。開部分群 nẑ の「整数部分」の完全な特徴付け
    （M13-3 `quot_exact` による、choice 不要）。 -/
theorem toZhat_mem_nzhat_iff (n : Nat) (a : Int) :
    nzhat n (toZhat.map a) ↔ ((n : Nat) : Int) ∣ a := by
  refine ⟨?_, ?_⟩
  · intro h
    have h' : ((n : Nat) : Int) ∣ (a - 0) := quot_exact intGrp (modCong n) h
    rw [Int.sub_zero] at h'
    exact h'
  · intro h
    apply Quot.sound
    show ((n : Nat) : Int) ∣ (a - 0)
    rw [Int.sub_zero]
    exact h

/-- M265F-11a: nẑ は開（M15-5a の実例化）。 -/
theorem nzhat_isOpen (n : Nat) :
    (limitTopology zmodSystem).IsOpen (nzhat n) :=
  projKernel_isOpen zmodSystem n

/-- M265F-11b: nẑ の補集合は開、すなわち nẑ は clopen。 -/
theorem nzhat_compl_isOpen (n : Nat) :
    (limitTopology zmodSystem).IsOpen (fun σ => ¬ nzhat n σ) :=
  projKernel_compl_isOpen zmodSystem n

/-- M265F-11c: {nẑ} は 1 ∈ ẑ の開近傍基（M15-6 系の実例化）。 -/
theorem nzhat_nbhd (U : zhat.carrier → Prop)
    (hU : (limitTopology zmodSystem).IsOpen U) (h1 : U zhat.one) :
    ∃ k, ∀ y, nzhat k y → U y :=
  projKernel_nbhd zmodSystem (1 : Nat) U hU h1

/-- **定理 (M265F-12): ẑ の ℤ/n への作用は位相的に連続** —
    M16-7（有限レベル作用は滑らか）と M265F-5 の合成。
    「絶対 Galois 群型の副有限群は有限商に**連続に**作用する」の
    ẑ での実物検証。 -/
theorem zhat_levelAction_continuous (n : Nat) :
    Continuous (prodTopology (limitTopology zmodSystem)
      (discreteTopology (levelAction zmodSystem n).carrier))
      (discreteTopology (levelAction zmodSystem n).carrier)
      (fun p => (levelAction zmodSystem n).act p.1 p.2) :=
  smooth_action_continuous zmodSystem (levelAction zmodSystem n)
    (levelAction_smooth zmodSystem n)

/-- **定理 (M265F-13): 射影核剰余類被覆の有限部分被覆**（コンパクト
    性 M25 との接続）— 階乗鎖極限（ẑ の鎖型表示、M25-5）の
    「レベル k の射影核の剰余類」による開被覆は有限部分被覆を持つ
    （「開部分群は有限指数」の被覆論的形）。
    **公理依存の明記**: 本定理は既存の M25 `factChain_compact`
    （König 型の木論法）を経由して Classical.choice を**継承**する。
    本モジュールの証明本体で choice を新規導入してはいない。 -/
theorem factChain_coset_cover_finite (k : Nat) :
    ∃ L : List ((limitGrp factChainSystem).carrier → Prop),
      (∀ U, U ∈ L → ∃ g : (limitGrp factChainSystem).carrier,
        U = fun σ => projKernel factChainSystem k
          ((limitGrp factChainSystem).mul
            ((limitGrp factChainSystem).inv g) σ)) ∧
      ∀ x, ∃ U, U ∈ L ∧ U x := by
  obtain ⟨L, hL1, hL2⟩ := factChain_compact
    (fun U => ∃ g : (limitGrp factChainSystem).carrier,
      U = fun σ => projKernel factChainSystem k
        ((limitGrp factChainSystem).mul
          ((limitGrp factChainSystem).inv g) σ))
    (fun U hU => by
      obtain ⟨g, rfl⟩ := hU
      exact projKernel_coset_isOpen factChainSystem k g)
    (fun x => by
      refine ⟨fun σ => projKernel factChainSystem k
        ((limitGrp factChainSystem).mul
          ((limitGrp factChainSystem).inv x) σ), ⟨x, rfl⟩, ?_⟩
      show projKernel factChainSystem k
        ((limitGrp factChainSystem).mul
          ((limitGrp factChainSystem).inv x) x)
      rw [(limitGrp factChainSystem).inv_mul]
      exact projKernel_one factChainSystem k)
  exact ⟨L, hL1, hL2⟩

/-! ## §5 capstone -/

/-- **capstone データ (M265F)**: 逆系 S の極限（副有限群）の位相構造の
    証明済み性質の束——位相群性（M15-3/4）・射影核の clopen 性
    （M15-5a + M265F-2）・近傍基（M15-6 系）・**開部分群の特徴付け**
    （M265F-4）・T2 分離（M265F-8）・**連続作用の同値**（M265F-7）。 -/
structure ProfiniteTopologyData (S : InverseSystem) where
  /-- 積は連続（位相群性の半分、M15-3）。 -/
  mul_continuous : Continuous
    (prodTopology (limitTopology S) (limitTopology S)) (limitTopology S)
    (fun p => (limitGrp S).mul p.1 p.2)
  /-- 逆元は連続（位相群性の残り半分、M15-4）。 -/
  inv_continuous : Continuous (limitTopology S) (limitTopology S)
    (fun x => (limitGrp S).inv x)
  /-- 射影核（開部分群）は開。 -/
  kernel_open : ∀ i, (limitTopology S).IsOpen (projKernelSubgroup S i).mem
  /-- 射影核は clopen（補集合も開）。 -/
  kernel_clopen : ∀ i, (limitTopology S).IsOpen
    (fun σ => ¬ (projKernelSubgroup S i).mem σ)
  /-- 射影核は 1 の開近傍基をなす。 -/
  kernel_nbhd_basis : ∀ (_i₀ : S.Idx) (U : (limitGrp S).carrier → Prop),
    (limitTopology S).IsOpen U → U (limitGrp S).one →
    ∃ k, ∀ y, (projKernelSubgroup S k).mem y → U y
  /-- 開部分群の特徴付け: 開 ⟺ 射影核を含む。 -/
  open_subgroup_iff_kernel : ∀ (_i₀ : S.Idx) (H : Subgroup (limitGrp S)),
    (limitTopology S).IsOpen H.mem ↔ ∃ k, ∀ y, projKernel S k y → H.mem y
  /-- T2 分離（apartness 形）: レベルで違えば開集合で分離。 -/
  t2_at_level : ∀ (i : S.Idx) (x y : (limitGrp S).carrier),
    x.val i ≠ y.val i →
    ∃ U V : (limitGrp S).carrier → Prop,
      (limitTopology S).IsOpen U ∧ (limitTopology S).IsOpen V ∧
      U x ∧ V y ∧ ∀ z, U z → V z → False
  /-- 連続作用の同値: 位相的連続 ⟺ 安定化群が開（SmoothAction）。 -/
  smooth_iff_continuous : ∀ (_i₀ : S.Idx) (X : GAction (limitGrp S)),
    SmoothAction S X
      ↔ Continuous (prodTopology (limitTopology S)
          (discreteTopology X.carrier)) (discreteTopology X.carrier)
          (fun p => X.act p.1 p.2)

/-- capstone の実現: 任意の逆系に対し副有限位相データを構成する。 -/
def profiniteTopologyData (S : InverseSystem) : ProfiniteTopologyData S where
  mul_continuous := limit_mul_continuous S
  inv_continuous := limit_inv_continuous S
  kernel_open := fun i => projKernel_isOpen S i
  kernel_clopen := fun i => projKernel_compl_isOpen S i
  kernel_nbhd_basis := fun i₀ U hU h1 => projKernel_nbhd S i₀ U hU h1
  open_subgroup_iff_kernel := fun i₀ H =>
    subgroup_isOpen_iff_contains_kernel S i₀ H
  t2_at_level := fun i x y h => limit_hausdorff_at_level S i x y h
  smooth_iff_continuous := fun i₀ X => smooth_iff_action_continuous S i₀ X

/-- **capstone 定理 (M265F): 副有限位相の存在** — 任意の逆系の極限は
    上記の全性質を備えた副有限位相を持つ。 -/
theorem profiniteTopology_exists (S : InverseSystem) :
    Nonempty (ProfiniteTopologyData S) :=
  ⟨profiniteTopologyData S⟩

/-- ẑ = lim ℤ/n（M13-7 の実構成）での実例化。 -/
def zhatProfiniteTopology : ProfiniteTopologyData zmodSystem :=
  profiniteTopologyData zmodSystem

end IUT
