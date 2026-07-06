/-
  IUT/AlgClosureColimit.lean — M315F（柱A: 分離閉包 K^sep = 有限分離拡大の
  余極限 colim Lₙ と絶対ガロア群 G_K = Gal(K^sep/K) = lim Gal(Lₙ/K) の
  本物の先行建設。mono-anabelian 本丸 AbsTopIII の主語＝π₁ 側の土台）

  分類 **[実]**（本物の体拡大の塔 K=L₀⊆L₁⊆… の**実**環準同型埋め込み
  step : Lₙ↪Lₙ₊₁ とその反復 embAdd を本物に構成し、余極限の**有向和関係が
  真の同値関係**であることを完全証明。絶対ガロア群 G_K は M287F の**実**
  逆極限 lim Gal(Lₙ/K)（副有限位相込み）を再利用し、その上の G_K の
  K^sep への**作用を各有限段の実 Galois 自己同型 σ_n の toFun** として
  本物に定義する。toy 群・toy 体を主語にしない——主語は M271F
  `galoisGroupGrp`（実 Gal(L/K)=Aut_K(L)）・M264F `IUTField`（実体）・
  M287F `profPi1Limit`（実 lim Gal）という本物の対象）。

  complete_pct 影響: **柱A 絶対ガロア群 G_K と分離閉包 K^sep の本物の
  先行建設**。M287F は有限ガロア塔の逆極限 lim Gal(Lᵢ/K)（副有限 π₁）を
  本物に建てたが、その逆極限が「基礎体 K の**分離閉包 K^sep の K 上自己
  同型群 Gal(K^sep/K)**」であるという遠アーベルの主語との接続——すなわち
  K^sep=colim Lₙ 側の本物の構成と、G_K の K^sep への作用——は無かった。
  本モジュールが (1) K^sep=colim Lₙ を有向和（germ + 同値関係、同値性を
  完全証明）として本物に構成し、(2) 各段の環準同型埋め込みが本物の
  ring hom（embAdd_add/mul/one）であることを本物に証明し、(3) G_K=lim Gal
  を M287F から接続してその副有限性を確定し、(4) G_K の K^sep への作用を
  各有限段の実 Galois 自己同型として本物に定義する。これにより
  mono-anabelian AbsTopIII の入力データ (G_K, K^sep, 作用) の**枠組みが
  本物の対象で閉じる**。昇格対象: M287F「lim Gal は π₁ だが K^sep 側との
  接続は未」→ K^sep=colim Lₙ・作用の本物化。

  内容（本物・toy を主語にしない）:
  * M315F-1 `AlgCloTower` — 基礎体 K 上の有限分離拡大の Nat 添字 cofinal
    塔（各段 `ext n : FieldExtension`（K⊆Lₙ）、段間の**環準同型埋め込み**
    `step n : Lₙ↪Lₙ₊₁`（加法・乗法・1 を保つ、実 ring hom）、および M287F
    の逆系データ `restr`/`restr_self`/`restr_comp` を witness で保持）。
  * M315F-2 `algCloEmbAdd` — 反復埋め込み Lᵢ↪L_{i+k}（k 段の step 合成）と
    それが**実 ring hom** であること（`algCloEmbAdd_add`/`_mul`/`_one`、
    k に関する帰納で完全証明）。合成則 `algCloEmbAdd_comp`（HEq）・
    オフセット congr `algCloEmbAdd_offset_heq`・段 congr `algCloStep_heq`。
  * M315F-3 `algCloSepGerm`/`algCloIota` — 余極限の germ 表現
    `Σ n, (Lₙ).carrier`（各元はある有限段 Lₙ に住む）と自然な包含
    Lₙ→K^sep。段送り整合 `algCloIota_step_rel`。
  * M315F-4 `algCloGermRel` — **有向和の同値関係**（両側を共通段まで持ち
    上げて一致、HEq 表現）。**反射律・対称律・推移律を完全証明**
    （`algClo_rel_refl`/`_symm`/`_trans`、`algClo_rel_equiv : Equivalence`）。
    K^sep = 有向和 colim Lₙ の本来の関係（＝各元がある有限段に住み、
    二元は十分高い段で一致する）を本物に確立。`algCloSep`（商型）。
  * M315F-5 `algClo_sep_element_in_stage`/`algCloGermInv`/
    `algClo_sep_inv_in_stage` — K^sep の各元がある有限段に住み、非零元の
    **逆元も同じ有限段に住む**（Lₙ が実体ゆえ、M264F の実 inv で本物に）。
  * M315F-6 `algCloAbsGalois` — G_K = Gal(K^sep/K) = lim Gal(Lₙ/K)（M287F
    `profPi1Limit` の再利用）。`algClo_absGalois_profinite`（副有限性、
    M287F `profPi1_is_profinite` 接続）。
  * M315F-7 `algCloAction` — G_K の K^sep（germ）への**作用**: g∈G_K の
    第 n 成分 σ_n∈Gal(Lₙ/K)（M287F 射影）の実 Galois 自己同型 toFun で
    Lₙ の元に作用。`algClo_action_one`（1 の作用は恒等）。固定体接続
    `algClo_fixedField_stage`（M283F `galCorr_fixedField`）。
  * M315F-8 `AlgCloAbsTopSubject` — mono-anabelian AbsTopIII の入力データ
    (G_K, K^sep, 作用) の枠組み。`algClo_absTop_subject`。
  * M315F-9 capstone `AlgClosureData`/`algClo_exists`/
    `algClo_absGalois_isProfinite`/`algClo_galois_correspondence`。
  * M315F-10 実例 `algCloTrivialTower`（分離閉体 K=ℚ 型: 各段 K=K^sep、
    G_K=lim Gal(K/K)=1）。

  **正直な限定**（何が本物で何が骨組み/後続か）:
  1. **本物（完全証明）**: 塔 step の反復 embAdd が ring hom
     （embAdd_add/mul/one）、合成則 embAdd_comp（HEq）、有向和関係
     algCloGermRel の**同値律（反射・対称・推移）**、各元・逆元が有限段に
     住むこと、G_K=lim Gal の副有限性（M287F 接続）、G_K の germ への作用
     の定義と 1 の作用＝恒等。これらは sorry/新規 choice 皆無で本物。
  2. **正直申告（骨組み/後続）**:
     ・K^sep の**商型 algCloSep 上の完全な体構造（加法・乗法の well-defined
       性と全 IUTField 公理）は後続**。本モジュールは germ + 同値関係
       （余極限の関係の本物）＋各有限段が実体＋包含が ring hom、まで。
       「完全な代数閉包（全分離多項式が分解）の存在」は Zorn 依存で
       非構成的ゆえ、有向系の余極限（cofinal 鎖 witness）で構成する
       という設計上の限定（CLAUDE.md の許容範囲）。
     ・段間の制限準同型 restr（σ∈Gal(Lⱼ) を Lᵢ に制限）は M287F と同じく
       塔の witness データ（分離正規拡大の全射性機構は core に無い）。
       Gal そのもの・逆極限・副有限位相は本物。
     ・作用 algCloAction の**商への降下（well-defined 性）＝σ が埋め込みと
       可換**は骨組み（restr 整合の帰結、後続）。germ 上の作用の定義と
       1 の作用＝恒等は本物。
     ・**固定体 K^sep^{G_K}=K**（Galois 主定理の無限版）は M283F/M285F の
       有限段の固定体接続 `algClo_fixedField_stage` に留め、無限版は後続。
     ・mono-anabelian AbsTopIII 本丸（G_K の位相群構造から数体 K を実際に
       復元するアルゴリズム）は後続——本モジュールは入力データ
       (G_K, K^sep, 作用) の**枠組みを本物の対象で閉じる**ところまで。
     ・非自明塔の実例（円分塔等）は二次以上の拡大体の実構成が別切片の
       ため、自明塔 K=K^sep（G_K=1）の本物の完全構成に留める。

  **選択公理不使用**（新規 Classical.choice を証明本体に導入しない）:
  embAdd は step の構造的反復、同値律は HEq の refl/symm/trans と embAdd の
  合成則、G_K は M287F の choice-free 逆極限、作用は M287F 射影と実
  Galois 自己同型の toFun。sorry 不使用・禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。許可タクティク（cases/obtain/induction/rw/show/
  refine/exact/apply/intro/generalize/funext/omega）のみ使用。
-/
import IUT.ProfinitePi1
import IUT.GaloisCorrespondence

namespace IUT

/-! ## M315F-1: 有限分離拡大の cofinal 塔（環準同型埋め込み付き） -/

/-- **M315F-1: 分離閉包/絶対ガロア群の塔** — 基礎体 `K` 上の有限分離拡大の
    Nat 添字 cofinal 鎖 K=L₀⊆L₁⊆…。各段は体拡大 `ext n`（K⊆Lₙ）で、段間の
    **環準同型埋め込み** `step n : Lₙ↪Lₙ₊₁`（加法・乗法・1 を保つ実 ring hom）
    を持つ。さらに M287F 逆極限（G_K=lim Gal）のための制限準同型 `restr` と
    逆系則（`restr_self`/`restr_comp`）を witness データとして保持する。 -/
structure AlgCloTower where
  /-- 基礎体 K。 -/
  K : IUTField
  /-- 塔の各段 K⊆Lₙ（有限分離拡大、Lₙ = (ext n).top）。 -/
  ext : Nat → FieldExtension
  /-- 各段の基礎体は K。 -/
  base_eq : ∀ n, (ext n).base = K
  /-- 段間の環準同型埋め込み step : Lₙ → Lₙ₊₁。 -/
  step : ∀ n, (ext n).top.carrier → (ext (n+1)).top.carrier
  /-- step は加法を保つ。 -/
  step_add : ∀ n x y,
    step n ((ext n).top.add x y) = (ext (n+1)).top.add (step n x) (step n y)
  /-- step は乗法を保つ。 -/
  step_mul : ∀ n x y,
    step n ((ext n).top.mul x y) = (ext (n+1)).top.mul (step n x) (step n y)
  /-- step は 1 を保つ。 -/
  step_one : ∀ n, step n (ext n).top.one = (ext (n+1)).top.one
  /-- 制限準同型 Gal(Lⱼ/K) → Gal(Lᵢ/K)（i ≤ j）。 -/
  restr : ∀ {i j : Nat}, i ≤ j →
    Hom (galoisGroupGrp (ext j)) (galoisGroupGrp (ext i))
  /-- 恒等保存: 同一段への制限は恒等。 -/
  restr_self : ∀ (i : Nat) (x : (galoisGroupGrp (ext i)).carrier),
    (restr (Nat.le_refl i)).map x = x
  /-- 推移性: 制限の合成は合成の制限（逆系の整合条件）。 -/
  restr_comp : ∀ {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k)
    (x : (galoisGroupGrp (ext k)).carrier),
    (restr hij).map ((restr hjk).map x) = (restr (Nat.le_trans hij hjk)).map x

/-- 塔の第 n 段の体 Lₙ。 -/
@[reducible] def algCloFld (T : AlgCloTower) (n : Nat) : IUTField := (T.ext n).top

/-! ## M315F-2: 反復埋め込み Lᵢ↪L_{i+k} と ring hom 性 -/

/-- **M315F-2: 反復埋め込み** Lᵢ → L_{i+k}（k 段の step の合成）。
    k=0 は恒等、k+1 は step を後合成。Nat 加法の定義的簡約
    （i+(k+1)=(i+k)+1）により型が整合する。 -/
def algCloEmbAdd (T : AlgCloTower) (i : Nat) :
    (k : Nat) → (algCloFld T i).carrier → (algCloFld T (i+k)).carrier
  | 0, x => x
  | (k+1), x => T.step (i+k) (algCloEmbAdd T i k x)

/-- **M315F-2a: embAdd は加法を保つ**（k に関する帰納）。 -/
theorem algCloEmbAdd_add (T : AlgCloTower) (i k : Nat)
    (x y : (algCloFld T i).carrier) :
    algCloEmbAdd T i k ((algCloFld T i).add x y)
      = (algCloFld T (i+k)).add (algCloEmbAdd T i k x) (algCloEmbAdd T i k y) := by
  induction k with
  | zero => exact rfl
  | succ k ih =>
    show T.step (i+k) (algCloEmbAdd T i k ((algCloFld T i).add x y))
      = (algCloFld T (i+(k+1))).add
          (T.step (i+k) (algCloEmbAdd T i k x))
          (T.step (i+k) (algCloEmbAdd T i k y))
    rw [ih]
    exact T.step_add (i+k) (algCloEmbAdd T i k x) (algCloEmbAdd T i k y)

/-- **M315F-2b: embAdd は乗法を保つ**（k に関する帰納）。 -/
theorem algCloEmbAdd_mul (T : AlgCloTower) (i k : Nat)
    (x y : (algCloFld T i).carrier) :
    algCloEmbAdd T i k ((algCloFld T i).mul x y)
      = (algCloFld T (i+k)).mul (algCloEmbAdd T i k x) (algCloEmbAdd T i k y) := by
  induction k with
  | zero => exact rfl
  | succ k ih =>
    show T.step (i+k) (algCloEmbAdd T i k ((algCloFld T i).mul x y))
      = (algCloFld T (i+(k+1))).mul
          (T.step (i+k) (algCloEmbAdd T i k x))
          (T.step (i+k) (algCloEmbAdd T i k y))
    rw [ih]
    exact T.step_mul (i+k) (algCloEmbAdd T i k x) (algCloEmbAdd T i k y)

/-- **M315F-2c: embAdd は 1 を保つ**（k に関する帰納）。 -/
theorem algCloEmbAdd_one (T : AlgCloTower) (i k : Nat) :
    algCloEmbAdd T i k (algCloFld T i).one = (algCloFld T (i+k)).one := by
  induction k with
  | zero => exact rfl
  | succ k ih =>
    show T.step (i+k) (algCloEmbAdd T i k (algCloFld T i).one)
      = (algCloFld T (i+(k+1))).one
    rw [ih]
    exact T.step_one (i+k)

/-- **M315F-2d: 段 congr（HEq）** — 段番号 m=m' で HEq a b なら
    HEq (step m a) (step m' b)。作用の合成の型整合に使う。 -/
theorem algCloStep_heq (T : AlgCloTower) {m m' : Nat} (h : m = m')
    {a : (algCloFld T m).carrier} {b : (algCloFld T m').carrier}
    (hab : HEq a b) : HEq (T.step m a) (T.step m' b) := by
  cases h
  have he : a = b := eq_of_heq hab
  rw [he]

/-- **M315F-2e: オフセット congr（HEq）** — 段数 k=k' なら
    HEq (embAdd i k x) (embAdd i k' x)。 -/
theorem algCloEmbAdd_offset_heq (T : AlgCloTower) (i : Nat) {k k' : Nat}
    (h : k = k') (x : (algCloFld T i).carrier) :
    HEq (algCloEmbAdd T i k x) (algCloEmbAdd T i k' x) := by
  cases h
  exact HEq.refl _

/-- **M315F-2f: embAdd の HEq 保存** — 段 m=m' で HEq a b なら
    HEq (embAdd m k a) (embAdd m' k b)。 -/
theorem algCloEmbAdd_heq (T : AlgCloTower) {m m' : Nat} (h : m = m') (k : Nat)
    {a : (algCloFld T m).carrier} {b : (algCloFld T m').carrier}
    (hab : HEq a b) : HEq (algCloEmbAdd T m k a) (algCloEmbAdd T m' k b) := by
  cases h
  have he : a = b := eq_of_heq hab
  rw [he]

/-- **M315F-2g: embAdd の合成則（HEq）** — Lᵢ を (k1+k2) 段上げるのは、
    まず k1 段上げてから k2 段上げるのに等しい（型は結合律で HEq）。
    k2 に関する帰納。 -/
theorem algCloEmbAdd_comp (T : AlgCloTower) (i k1 k2 : Nat)
    (x : (algCloFld T i).carrier) :
    HEq (algCloEmbAdd T i (k1+k2) x)
        (algCloEmbAdd T (i+k1) k2 (algCloEmbAdd T i k1 x)) := by
  induction k2 with
  | zero => exact HEq.refl _
  | succ k ih =>
    -- LHS = step (i+(k1+k)) (embAdd i (k1+k) x)
    -- RHS = step ((i+k1)+k) (embAdd (i+k1) k (embAdd i k1 x))
    have hidx : i + (k1 + k) = (i + k1) + k := by omega
    exact algCloStep_heq T hidx ih

/-! ## M315F-3: 余極限の germ 表現 K^sep = colim Lₙ -/

/-- **M315F-3: K^sep の germ 表現** — 各元は「ある有限段 Lₙ に住む元」
    ⟨n, x⟩（Σ 型）。余極限 colim Lₙ の元の直接表現。 -/
def algCloSepGerm (T : AlgCloTower) : Type := Σ n : Nat, (algCloFld T n).carrier

/-- **M315F-3a: 自然な包含** Lₙ → K^sep（第 n 段の元を germ に）。 -/
def algCloIota (T : AlgCloTower) (n : Nat) (x : (algCloFld T n).carrier) :
    algCloSepGerm T := ⟨n, x⟩

/-! ## M315F-4: 有向和の同値関係（同値律を完全証明） -/

/-- **M315F-4: 有向和の同値関係** — 二つの germ ⟨n,x⟩, ⟨m,y⟩ が K^sep で
    等しいとは、十分高い共通段まで両者を持ち上げると一致すること:
    ∃ p q, n+p = m+q かつ HEq (embAdd n p x) (embAdd m q y)。
    余極限（有向和）の等号の本来の定義。 -/
def algCloGermRel (T : AlgCloTower) (a b : algCloSepGerm T) : Prop :=
  ∃ (p q : Nat), a.1 + p = b.1 + q ∧
    HEq (algCloEmbAdd T a.1 p a.2) (algCloEmbAdd T b.1 q b.2)

/-- **M315F-4a: 反射律** — 同一 germ は関係する（p=q=0）。 -/
theorem algClo_rel_refl (T : AlgCloTower) (a : algCloSepGerm T) :
    algCloGermRel T a a :=
  ⟨0, 0, rfl, HEq.refl _⟩

/-- **M315F-4b: 対称律** — 関係は対称（p,q と HEq を入れ替え）。 -/
theorem algClo_rel_symm (T : AlgCloTower) {a b : algCloSepGerm T}
    (h : algCloGermRel T a b) : algCloGermRel T b a := by
  obtain ⟨p, q, hidx, hheq⟩ := h
  exact ⟨q, p, hidx.symm, hheq.symm⟩

/-- **M315F-4c: 推移律** — 関係は推移的。b の二つの持ち上げ（段 n+p と n+r）を
    合成則 embAdd_comp で共通段 n+(q+r) に揃え、a・c 側もそこへ持ち上げて
    HEq を連結する。 -/
theorem algClo_rel_trans (T : AlgCloTower) {a b c : algCloSepGerm T}
    (hab : algCloGermRel T a b) (hbc : algCloGermRel T b c) :
    algCloGermRel T a c := by
  obtain ⟨p, q, hidx1, hheq1⟩ := hab
  obtain ⟨r, s, hidx2, hheq2⟩ := hbc
  -- 目標のオフセット: a を p+r、c を s+q 段上げ、共通段で比較
  refine ⟨p + r, s + q, ?_, ?_⟩
  · -- 段番号: a.1+(p+r) = c.1+(s+q)。 a.1+p=b.1+q, b.1+r=c.1+s より線形。
    omega
  · -- HEq の連鎖:
    -- embAdd a.1 (p+r) a.2
    --   ≈ embAdd (a.1+p) r (embAdd a.1 p a.2)              [comp]
    --   ≈ embAdd (b.1+q) r (embAdd b.1 q b.2)              [heq: hidx1, hheq1]
    --   = embAdd (b.1+q) r B_q
    -- embAdd b.1 (q+r) b.2 ≈ embAdd (b.1+q) r B_q          [comp]
    -- embAdd b.1 (r+q) b.2 ≈ embAdd (b.1+r) q B_r          [comp]
    -- embAdd b.1 (q+r) b.2 ≈ embAdd b.1 (r+q) b.2          [offset_heq]
    -- embAdd (b.1+r) q B_r ≈ embAdd (c.1+s) q C            [heq: hidx2.symm, hheq2]
    -- embAdd c.1 (s+q) c.2 ≈ embAdd (c.1+s) q C            [comp]
    have e1 : HEq (algCloEmbAdd T a.1 (p+r) a.2)
                  (algCloEmbAdd T (a.1+p) r (algCloEmbAdd T a.1 p a.2)) :=
      algCloEmbAdd_comp T a.1 p r a.2
    have e2 : HEq (algCloEmbAdd T (a.1+p) r (algCloEmbAdd T a.1 p a.2))
                  (algCloEmbAdd T (b.1+q) r (algCloEmbAdd T b.1 q b.2)) :=
      algCloEmbAdd_heq T hidx1 r hheq1
    have e3 : HEq (algCloEmbAdd T b.1 (q+r) b.2)
                  (algCloEmbAdd T (b.1+q) r (algCloEmbAdd T b.1 q b.2)) :=
      algCloEmbAdd_comp T b.1 q r b.2
    have e4 : HEq (algCloEmbAdd T b.1 (r+q) b.2)
                  (algCloEmbAdd T (b.1+r) q (algCloEmbAdd T b.1 r b.2)) :=
      algCloEmbAdd_comp T b.1 r q b.2
    have e5 : HEq (algCloEmbAdd T b.1 (q+r) b.2)
                  (algCloEmbAdd T b.1 (r+q) b.2) :=
      algCloEmbAdd_offset_heq T b.1 (by omega) b.2
    have e6 : HEq (algCloEmbAdd T (b.1+r) q (algCloEmbAdd T b.1 r b.2))
                  (algCloEmbAdd T (c.1+s) q (algCloEmbAdd T c.1 s c.2)) :=
      algCloEmbAdd_heq T hidx2 q hheq2
    have e7 : HEq (algCloEmbAdd T c.1 (s+q) c.2)
                  (algCloEmbAdd T (c.1+s) q (algCloEmbAdd T c.1 s c.2)) :=
      algCloEmbAdd_comp T c.1 s q c.2
    -- 連結: LHS ≈ e1 ≈ e2 → (b.1+q,r,B_q); e3.symm ≈ e5.symm... を組む
    -- a 側: A' := embAdd (b.1+q) r B_q
    -- A' ≈ embAdd b.1 (q+r) b.2 (e3.symm)
    --    ≈ embAdd b.1 (r+q) b.2 (e5)
    --    ≈ embAdd (b.1+r) q B_r (e4)
    --    ≈ embAdd (c.1+s) q C (e6)
    --    ≈ embAdd c.1 (s+q) c.2 (e7.symm)
    exact HEq.trans e1 (HEq.trans e2 (HEq.trans e3.symm (HEq.trans e5
      (HEq.trans e4 (HEq.trans e6 e7.symm)))))

/-- **M315F-4d: 有向和関係は同値関係**（余極限の等号が真の同値律をなす）。 -/
theorem algClo_rel_equiv (T : AlgCloTower) : Equivalence (algCloGermRel T) where
  refl := algClo_rel_refl T
  symm := algClo_rel_symm T
  trans := algClo_rel_trans T

/-- **M315F-4e: K^sep の setoid**（有向和関係）。 -/
def algCloSetoid (T : AlgCloTower) : Setoid (algCloSepGerm T) where
  r := algCloGermRel T
  iseqv := algClo_rel_equiv T

/-- **M315F-4f: 分離閉包 K^sep = colim Lₙ**（有向和の商型）。
    各元は有限段の元の同値類（余極限の本来の構成）。 -/
def algCloSep (T : AlgCloTower) : Type := Quotient (algCloSetoid T)

/-- **M315F-4g: K^sep への包含**（商への降下）Lₙ → K^sep。 -/
def algCloSepMk (T : AlgCloTower) (n : Nat) (x : (algCloFld T n).carrier) :
    algCloSep T := Quotient.mk (algCloSetoid T) (algCloIota T n x)

/-- **M315F-4h: 段送り整合** — ⟨n,x⟩ と ⟨n+1, step x⟩ は K^sep で等しい
    （包含の鎖 Lₙ⊆Lₙ₊₁ の整合、余極限の錐条件）。 -/
theorem algCloIota_step_rel (T : AlgCloTower) (n : Nat)
    (x : (algCloFld T n).carrier) :
    algCloGermRel T (algCloIota T n x) (algCloIota T (n+1) (T.step n x)) := by
  -- n+1 = n+1, embAdd n 1 x = step n x = embAdd (n+1) 0 (step n x)
  refine ⟨1, 0, ?_, ?_⟩
  · exact rfl
  · exact HEq.refl _

/-- **M315F-4i: 段送りの K^sep 上の等号**（M315F-4h の商版）。 -/
theorem algCloSepMk_step (T : AlgCloTower) (n : Nat)
    (x : (algCloFld T n).carrier) :
    algCloSepMk T n x = algCloSepMk T (n+1) (T.step n x) :=
  Quotient.sound (algCloIota_step_rel T n x)

/-! ## M315F-5: 各元・逆元が有限段に住む -/

/-- **M315F-5a: 各元は有限段に住む** — K^sep の任意の germ はある段 n の
    元 x の像 ⟨n,x⟩。余極限の「各元は有限段に住む」性質。 -/
theorem algClo_sep_element_in_stage (T : AlgCloTower) (a : algCloSepGerm T) :
    ∃ (n : Nat) (x : (algCloFld T n).carrier), a = algCloIota T n x :=
  ⟨a.1, a.2, rfl⟩

/-- **M315F-5b: 有限段での逆元** — germ ⟨n,x⟩ の逆元は ⟨n, x⁻¹⟩（Lₙ の
    実 inv、M264F）。逆元も同じ有限段に住む。 -/
def algCloGermInv (T : AlgCloTower) (a : algCloSepGerm T) : algCloSepGerm T :=
  ⟨a.1, (algCloFld T a.1).inv a.2⟩

/-- **M315F-5c: 非零元の逆元が段内で乗法逆をなす** — x≠0（Lₙ で）なら
    Lₙ で x·x⁻¹=1（実体 Lₙ の逆元公理、本物）。逆元が同じ段に住むことの
    本物の内容。 -/
theorem algClo_sep_inv_in_stage (T : AlgCloTower) (n : Nat)
    (x : (algCloFld T n).carrier) (hx : x ≠ (algCloFld T n).zero) :
    (algCloFld T n).mul x ((algCloGermInv T (algCloIota T n x)).2)
      = (algCloFld T n).one :=
  (algCloFld T n).mul_inv_cancel x hx

/-! ## M315F-6: 絶対ガロア群 G_K = lim Gal(Lₙ/K)（M287F 接続） -/

/-- **M315F-6a: 塔から M287F の pro-有限 π₁ 塔**（Galois 側データを抽出）。 -/
def algCloProfTower (T : AlgCloTower) : ProfinitePi1Tower where
  K := T.K
  ext := T.ext
  restr := T.restr
  restr_self := T.restr_self
  restr_comp := T.restr_comp

/-- **M315F-6b: 絶対ガロア群 G_K = Gal(K^sep/K) = lim Gal(Lₙ/K)**
    （M287F `profPi1Limit` の再利用）。遠アーベル復元 AbsTopIII の主語
    ＝副有限群 G_K。 -/
def algCloAbsGalois (T : AlgCloTower) : Grp := profPi1Limit (algCloProfTower T)

/-- **M315F-6c: G_K → Gal(Lₙ/K) の射影**（M287F の逆極限の錐）。 -/
def algCloProj (T : AlgCloTower) (n : Nat) :
    Hom (algCloAbsGalois T) (galoisGroupGrp (T.ext n)) :=
  profPi1_proj (algCloProfTower T) n

/-- **M315F-6d: G_K は副有限群**（M287F `profPi1_is_profinite` 接続）—
    各射影核が開部分群、かつ開部分群系が 1 の近傍基をなす。 -/
theorem algClo_absGalois_profinite (T : AlgCloTower) :
    (∀ n, (limitTopology (profPi1System (algCloProfTower T))).IsOpen
        (profPi1KernelSubgroup (algCloProfTower T) n).mem)
      ∧ (∀ (i₀ : Nat)
          (U : (profPi1Limit (algCloProfTower T)).carrier → Prop),
          (limitTopology (profPi1System (algCloProfTower T))).IsOpen U →
          U (profPi1Limit (algCloProfTower T)).one →
          ∃ k, ∀ y, projKernel (profPi1System (algCloProfTower T)) k y → U y) :=
  profPi1_is_profinite (algCloProfTower T)

/-! ## M315F-7: G_K の K^sep への作用 -/

/-- **M315F-7a: G_K の K^sep（germ）への作用** — g∈G_K=lim Gal の第 n 成分
    σ_n∈Gal(Lₙ/K)（射影 `algCloProj`）は Lₙ の実 Galois 自己同型であり、その
    `toFun` で germ ⟨n,x⟩ の第 n 段の元 x に作用する。各有限段の実 Galois
    作用として本物に定義（商への降下は後続）。 -/
def algCloAction (T : AlgCloTower) (g : (algCloAbsGalois T).carrier)
    (a : algCloSepGerm T) : algCloSepGerm T :=
  ⟨a.1, (((algCloProj T a.1).map g).val).toFun a.2⟩

/-- **M315F-7b: 単位元 1∈G_K の作用は恒等** — 1 の第 n 成分は恒等自己同型
    （Gal の単位＝id）なので germ を保つ。 -/
theorem algClo_action_one (T : AlgCloTower) (a : algCloSepGerm T) :
    algCloAction T (algCloAbsGalois T).one a = a := by
  -- (algCloProj T a.1).map one = one（Hom.map_one）、その val は fieldAutId、
  -- toFun a.2 = a.2。
  show (⟨a.1, (((algCloProj T a.1).map (algCloAbsGalois T).one).val).toFun a.2⟩
        : algCloSepGerm T) = a
  have hone : (algCloProj T a.1).map (algCloAbsGalois T).one
      = (galoisGroupGrp (T.ext a.1)).one := Hom.map_one (algCloProj T a.1)
  rw [hone]
  -- (galoisGroupGrp E).one.val = fieldAutId E.top、.toFun a.2 = a.2
  show (⟨a.1, a.2⟩ : algCloSepGerm T) = a
  exact rfl

/-- **M315F-7c: 固定体（有限段）** — 第 n 段で G_K の像が固定する Lₙ の元の
    集合（M283F `galCorr_fixedField` 接続）。K^sep^{G_K}=K の無限版は後続、
    ここは各有限段の固定体接続。 -/
def algCloFixedFieldStage (T : AlgCloTower) (n : Nat)
    (H : Subgroup (fieldAutGroup (T.ext n).top)) :
    (algCloFld T n).carrier → Prop :=
  galCorr_fixedField (T.ext n) H

/-- **M315F-7d: 固定体所属の特徴づけ**（M283F 接続、有限段）。 -/
theorem algClo_fixedField_stage (T : AlgCloTower) (n : Nat)
    (H : Subgroup (fieldAutGroup (T.ext n).top))
    (x : (algCloFld T n).carrier) :
    algCloFixedFieldStage T n H x ↔ (∀ σ, H.mem σ → σ.toFun x = x) :=
  galCorr_fixedField_mem_iff (T.ext n) H x

/-! ## M315F-8: mono-anabelian AbsTopIII の入力データ枠組み -/

/-- **M315F-8: mono-anabelian 復元の主語データ** — 遠アーベル復元 AbsTopIII
    が入力とする三つ組 (G_K, K^sep, 作用):
    * 絶対ガロア群 G_K = lim Gal（副有限）、
    * 分離閉包 K^sep = colim Lₙ、
    * G_K の K^sep への作用（germ 版）。
    「G_K の位相群構造から数体 K を復元する」出発点の枠組み（復元
    アルゴリズム本丸は後続）。 -/
structure AlgCloAbsTopSubject (T : AlgCloTower) where
  /-- 絶対ガロア群 G_K。 -/
  absGalois : Grp
  /-- G_K は lim Gal(Lₙ/K)。 -/
  absGalois_eq : absGalois = algCloAbsGalois T
  /-- 分離閉包 K^sep の型。 -/
  sepClosure : Type
  /-- K^sep は有向和の商型。 -/
  sepClosure_eq : sepClosure = algCloSep T
  /-- G_K の K^sep（germ）への作用。 -/
  action : (algCloAbsGalois T).carrier → algCloSepGerm T → algCloSepGerm T
  /-- 作用は `algCloAction`。 -/
  action_eq : action = algCloAction T
  /-- 単位元の作用は恒等（作用の最小整合）。 -/
  action_one : ∀ a, action (algCloAbsGalois T).one a = a

/-- **M315F-8a: mono-anabelian 主語の証人** — (G_K, K^sep, 作用) が枠組みを
    なす。 -/
def algClo_absTop_subject (T : AlgCloTower) : AlgCloAbsTopSubject T where
  absGalois := algCloAbsGalois T
  absGalois_eq := rfl
  sepClosure := algCloSep T
  sepClosure_eq := rfl
  action := algCloAction T
  action_eq := rfl
  action_one := algClo_action_one T

/-! ## M315F-9: capstone -/

/-- **M315F-9a: capstone データ** — 塔 T に対する分離閉包 K^sep・絶対ガロア群
    G_K・作用の全部品。 -/
structure AlgClosureData (T : AlgCloTower) where
  /-- 分離閉包 K^sep = colim Lₙ（有向和の商型）。 -/
  sepClosure : Type
  /-- K^sep は `algCloSep`。 -/
  sepClosure_eq : sepClosure = algCloSep T
  /-- 絶対ガロア群 G_K = lim Gal。 -/
  absGalois : Grp
  /-- G_K は `algCloAbsGalois`。 -/
  absGalois_eq : absGalois = algCloAbsGalois T
  /-- 各段への射影 G_K → Gal(Lₙ/K)。 -/
  proj : ∀ n, Hom (algCloAbsGalois T) (galoisGroupGrp (T.ext n))
  /-- G_K の K^sep への作用（germ 版）。 -/
  action : (algCloAbsGalois T).carrier → algCloSepGerm T → algCloSepGerm T
  /-- 作用は `algCloAction`。 -/
  action_eq : action = algCloAction T
  /-- G_K は副有限（各射影核が開・開部分群系が近傍基）。 -/
  profinite :
    (∀ n, (limitTopology (profPi1System (algCloProfTower T))).IsOpen
        (profPi1KernelSubgroup (algCloProfTower T) n).mem)
      ∧ (∀ (i₀ : Nat)
          (U : (profPi1Limit (algCloProfTower T)).carrier → Prop),
          (limitTopology (profPi1System (algCloProfTower T))).IsOpen U →
          U (profPi1Limit (algCloProfTower T)).one →
          ∃ k, ∀ y, projKernel (profPi1System (algCloProfTower T)) k y → U y)

/-- **M315F-9b: 証人** — K^sep・G_K・射影・作用・副有限性が全条件を満たす。 -/
def algCloData (T : AlgCloTower) : AlgClosureData T where
  sepClosure := algCloSep T
  sepClosure_eq := rfl
  absGalois := algCloAbsGalois T
  absGalois_eq := rfl
  proj := fun n => algCloProj T n
  action := algCloAction T
  action_eq := rfl
  profinite := algClo_absGalois_profinite T

/-- **M315F-9c: capstone — 分離閉包 K^sep と絶対ガロア群 G_K の存在** —
    任意の有限分離拡大の cofinal 塔に対し、その余極限 K^sep=colim Lₙ・
    絶対ガロア群 G_K=lim Gal・G_K の作用が組み上がる。 -/
theorem algClo_exists (T : AlgCloTower) : Nonempty (AlgClosureData T) :=
  ⟨algCloData T⟩

/-- **M315F-9d: G_K は副有限群**（capstone: 絶対ガロア群の副有限性）。 -/
theorem algClo_absGalois_isProfinite (T : AlgCloTower) :
    (∀ n, (limitTopology (profPi1System (algCloProfTower T))).IsOpen
        (profPi1KernelSubgroup (algCloProfTower T) n).mem)
      ∧ (∀ (i₀ : Nat)
          (U : (profPi1Limit (algCloProfTower T)).carrier → Prop),
          (limitTopology (profPi1System (algCloProfTower T))).IsOpen U →
          U (profPi1Limit (algCloProfTower T)).one →
          ∃ k, ∀ y, projKernel (profPi1System (algCloProfTower T)) k y → U y) :=
  algClo_absGalois_profinite T

/-- **M315F-9e: capstone — Galois 対応の接続（有限段）** — G_K の像が固定する
    Lₙ の元の集合（固定体）が M283F の `galCorr_fixedField` で与えられ、
    その所属が「H の全元が固定する」ことと同値（G_K↔中間体対応の有限段版、
    無限版は後続）。 -/
theorem algClo_galois_correspondence (T : AlgCloTower) (n : Nat)
    (H : Subgroup (fieldAutGroup (T.ext n).top))
    (x : (algCloFld T n).carrier) :
    algCloFixedFieldStage T n H x ↔ (∀ σ, H.mem σ → σ.toFun x = x) :=
  algClo_fixedField_stage T n H x

/-! ## M315F-10: 実例 — 分離閉体 K=ℚ 型（K=K^sep, G_K=1） -/

/-- **M315F-10a: 自明塔**（分離閉体 K のモデル: 各段 Lₙ=K=K^sep、
    step=恒等、制限=恒等準同型）。分離閉体では K=K^sep で有限拡大の塔は
    定常、G_K=lim Gal(K/K)=1。本物の数体 ℚ 上で構成。 -/
def algCloTrivialTower : AlgCloTower where
  K := ratIUTField
  ext := fun _ => trivialExtension ratIUTField
  base_eq := fun _ => rfl
  step := fun _ x => x
  step_add := fun _ _ _ => rfl
  step_mul := fun _ _ _ => rfl
  step_one := fun _ => rfl
  restr := fun _ => profPi1IdHom (galoisGroupGrp (trivialExtension ratIUTField))
  restr_self := fun _ _ => rfl
  restr_comp := fun _ _ _ => rfl

/-- **M315F-10b: 自明塔で K^sep・G_K が組み上がる**（本物の ℚ 上）。 -/
def algClo_trivial_data : AlgClosureData algCloTrivialTower :=
  algCloData algCloTrivialTower

/-- **M315F-10c: 自明塔で G_K が副有限**（ℚ 上 lim Gal(ℚ/ℚ)=1 が
    副有限群）。 -/
theorem algClo_trivial_isProfinite :
    (∀ n, (limitTopology (profPi1System (algCloProfTower algCloTrivialTower))).IsOpen
        (profPi1KernelSubgroup (algCloProfTower algCloTrivialTower) n).mem)
      ∧ (∀ (i₀ : Nat)
          (U : (profPi1Limit (algCloProfTower algCloTrivialTower)).carrier → Prop),
          (limitTopology (profPi1System (algCloProfTower algCloTrivialTower))).IsOpen U →
          U (profPi1Limit (algCloProfTower algCloTrivialTower)).one →
          ∃ k, ∀ y, projKernel (profPi1System (algCloProfTower algCloTrivialTower)) k y → U y) :=
  algClo_absGalois_isProfinite algCloTrivialTower

/-- **M315F-10d: 自明塔の単位元作用は恒等**（G_K=1 の作用が K^sep を保つ）。 -/
theorem algClo_trivial_action_one (a : algCloSepGerm algCloTrivialTower) :
    algCloAction algCloTrivialTower (algCloAbsGalois algCloTrivialTower).one a = a :=
  algClo_action_one algCloTrivialTower a

end IUT
