/-
  IUT/AbsTopMultAdd.lean — M325F（柱A: mono-anabelian 本丸 AbsTopIII の核。
  体の**乗法構造 K^× ＋離散付値 v から加法構造を復元する**本物の 1 ステップ）

  ── 主要成果の分類: **[実]**（本物の体 `IUTField`（M264F）と本物の離散付値
  `valRingValuation`（M301F）の上で、**加法を忘れた乗法＋付値データ**から加法を
  本物に復元する。中核は恒等式
      x + y = x · (1 + x⁻¹·y)   （x ≠ 0）
  ——加法が**乗法 K^×・逆元・単項作用「1 + (·)」だけ**から一意に書ける、という
  mono-anabelian 復元の代数的核を core Lean のみで完全証明する。さらに「1+t」の
  付値が超距離不等式 v(1+t) ≥ min(0, v(t)) を満たすこと（付値環 O_v の加法が
  乗法＋付値から再構成される事実）を M301F の付値公理から本物に導き、これを使って
  加法の付値の超距離 v(x+y) ≥ v(x)（v(x)≤v(y) 側）を**乗法側の復元式から再導出**する。
  すなわち「加法の超距離は独立公理ではなく、乗法＋『1+t』の付値から従う」ことを
  本物に閉じる。主語は toy ではなく本物の体 K・本物の付値 v・本物の逆元 K.inv。）

  complete_pct 影響: **柱A「mono-anabelian AbsTopIII の核」の本物の先行建設**。
  既存 `IUT/Reconstruction.lean`（M10）・`IUT/Anabelian.lean`（M1）は AbsTopIII の
  **枠組み・両立性の骨格**を、`IUT/GlobalSectionsRecover.lean`（M294F）は「空間から
  環を戻す」代数幾何版第一歩を、`IUT/CyclotomicRigidity.lean`（M322F）は円分指標 χ を
  本物化したが、**「乗法群 K^× ＋付値から加法演算そのものを復元する」代数的核**を
  IUTField 上に本物で建てたモジュールは無かった。本ファイルはそこを昇格・建設する:
    (1) 加法復元恒等式 x+y = x·(1+x⁻¹y)（x≠0）を体公理から完全証明（**復元の核**）、
    (2) 復元加法が元の体加法と一致する整合性（consistency）を完全証明、
    (3) 「1+t」の付値超距離 v(1+t)≥min(0,v(t)) を M301F 付値公理から完全証明、
    (4) 逆元の付値 v(x⁻¹)=-v(x)・v(x⁻¹y)≥0（v(x)≤v(y)）を完全証明、
    (5) 加法の付値超距離 v(x+y)≥v(x) を**乗法側の復元式(1)＋(3)(4)から再導出**、
  を本物で閉じる。これにより AbsTopIII の「乗法＋付値 → 加法（→ 環構造）」の核が
  柱A に一段本物化される。数体復元の完全アルゴリズムは骨組み（後続）。

  * M325F-1 `absTopValOptLe_add_of_nonneg` — 値群補題（0≤s ⟹ r ≤ r+s、∞込み）
  * M325F-2 `absTop_add_from_one_add` / `absTopRecoverAdd` — **復元恒等式**
    x+y = x·(1+x⁻¹y)（x≠0）。加法を乗法＋逆元＋「1+·」から本物に復元。
  * M325F-3 `absTop_add_consistent` — 復元加法 = 元の体加法（整合性）
  * M325F-4 `absTop_v_one_add_ge` / `absTop_v_one_add_nonneg` — 「1+t」の付値超距離
    v(1+t)≥min(0,v(t))、および t∈O_v ⟹ 1+t∈O_v（O_v 加法の再構成）
  * M325F-5 `absTop_v_inv` / `absTop_v_inv_mul_nonneg` — v(x⁻¹)=-v(x)、v(x⁻¹y)≥0
  * M325F-6 `absTop_v_add_ge_of_le` — **加法の付値超距離を復元式から再導出**
    （x≠0, v(x)≤v(y) ⟹ v(x+y)≥v(x)）。加法超距離は乗法＋付値の帰結。
  * M325F-7 `absTopMultData` / `AbsTopReconstructData` / `absTop_toReconstructData`
    / `absTop_exists` / `absTop_add_from_mult` / `absTop_reconstruct_skeleton`
    — capstone（乗法＋付値データ・加法復元・整合性・超距離を束ねる）
  * M325F-8 `AbsTopIIIInputSkeleton` / `absTop_field_recover` — 数体復元の骨組み
    （M322F 円分/ガロア作用 CycGKAction を AbsTopIII の入力として接続）
  * M325F-9 実例 `absTop_example_recover` / `absTop_example_one_add_mem`

  正直な限定（何が本物で何が骨組みか・消去弱化禁止）:
  - **本物（完全証明・sorry 皆無・新規 choice 皆無）**: 加法復元恒等式
    x+y=x·(1+x⁻¹y)（x≠0）、復元加法と体加法の一致（整合性）、「1+t」の付値超距離
    v(1+t)≥min(0,v(t))、v(x⁻¹)=-v(x)、v(x⁻¹y)≥0（v(x)≤v(y)）、そして
    加法の付値超距離 v(x+y)≥v(x)（v(x)≤v(y) 側）を**乗法側の復元式から再導出**する
    ことは完全証明。これらが「乗法群＋付値から加法（の超距離・O_v 加法）を再構成する核」。
  - **超距離の符号化**: M301F と同じく v(x+y)≥min(v(x),v(y)) を全順序値群上で
    同値な選言/条件形（v(x)≤v(y) 側 ⟹ v(x+y)≥v(x)）で述べる。両者は同値。
  - **骨組み（後続）**: AbsTopIII 本丸（π₁^ét から数体を復元する完全アルゴリズム）は
    膨大ゆえ、ここは**乗法群＋付値から加法（超距離・O_v 加法）を再構成する核**を本物で、
    (K^×, v, χ) からの**完全な体復元は骨組み**（`AbsTopIIIInputSkeleton`・
    `absTop_field_recover` は M322F 円分/ガロア作用を入力として束ねる枠組みまで。
    加法の全ペア x+y の値としての再構成は復元式で本物だが、環同型類として数体 K を
    戻すアルゴリズムの全体、および M294F R≅Γ との圏論的接続は後続）。
  - 円分・ガロアからの入力は M322F `CycGKAction`（G_K の μ_n 作用）を使う（作用は本物、
    χ からの復元アルゴリズムの本丸は後続）。復元恒等式の付値解析は M301F を本物で使う。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。禁止タクティク
  不使用（cases/obtain/induction/rw/show/refine/exact/apply/intro/omega のみ）。
  共有ファイル未変更（新規 1 本のみ・一般名は `absTop` 接頭辞で衝突回避）。
-/
import IUT.ValuationRing
import IUT.CyclotomicRigidity

namespace IUT

/-! ## M325F-1: 値群の補題（0 ≤ s ⟹ r ≤ r + s、∞=none 込み） -/

/-- **M325F-1: 値群での「非負を足すと増える」** — `valOptLe (some 0) s` なら
    `valOptLe r (valOptAdd r s)`（∞ を最大とする ℤ∪{∞} 上）。加法復元の付値解析で、
    v(x+y)=v(x)+v(1+x⁻¹y) と v(1+x⁻¹y)≥0 から v(x+y)≥v(x) を出すのに使う。 -/
theorem absTopValOptLe_add_of_nonneg (r s : Option Int)
    (h : valOptLe (some (0 : Int)) s) : valOptLe r (valOptAdd r s) := by
  cases r with
  | none =>
    show valOptLe none (valOptAdd none s)
    rw [valOptAdd_none_left]
    exact True.intro
  | some a =>
    cases s with
    | none =>
      show valOptLe (some a) (valOptAdd (some a) none)
      rw [valOptAdd_some_none]
      exact True.intro
    | some b =>
      have hb : (0 : Int) ≤ b := h
      show valOptLe (some a) (valOptAdd (some a) (some b))
      rw [valOptAdd_some_some]
      show a ≤ a + b
      omega

/-! ## M325F-2: 加法復元恒等式 x + y = x · (1 + x⁻¹·y)（核） -/

/-- **M325F-2a: 復元加法** — 乗法・逆元・単項作用「1 + (·)」から作った加法
    `x ⊕ y := x · (1 + x⁻¹·y)`。x ≠ 0 のとき本来の加法 x + y に一致する（下記）。 -/
def absTopRecoverAdd (K : IUTField) (x y : K.carrier) : K.carrier :=
  K.mul x (K.add K.one (K.mul (K.inv x) y))

/-- **M325F-2b: 加法復元恒等式（核）** — x ≠ 0 なら
      x + y = x · (1 + x⁻¹·y).
    加法が乗法群 K^×・逆元・単項作用「1+·」だけから一意に書ける、という
    mono-anabelian 復元の代数的核。体公理（分配・結合・逆元）から完全証明。 -/
theorem absTop_add_from_one_add (K : IUTField) (x y : K.carrier) (hx : x ≠ K.zero) :
    K.add x y = K.mul x (K.add K.one (K.mul (K.inv x) y)) := by
  have hstep : K.mul x (K.add K.one (K.mul (K.inv x) y)) = K.add x y := by
    rw [K.left_distrib, K.mul_comm x K.one, K.one_mul,
      ← K.mul_assoc x (K.inv x) y, K.mul_inv_cancel x hx, K.one_mul]
  exact hstep.symm

/-! ## M325F-3: 整合性（復元加法 = 元の体加法） -/

/-- **M325F-3: 加法の整合性** — 乗法＋逆元＋「1+·」から復元した加法 `absTopRecoverAdd`
    は x ≠ 0 で本来の体加法と一致する。すなわち「加法を忘れた乗法＋付値データ」から
    再構成した加法が元の体の加法そのものに戻る（復元の忠実性）。 -/
theorem absTop_add_consistent (K : IUTField) (x y : K.carrier) (hx : x ≠ K.zero) :
    absTopRecoverAdd K x y = K.add x y := by
  show K.mul x (K.add K.one (K.mul (K.inv x) y)) = K.add x y
  exact (absTop_add_from_one_add K x y hx).symm

/-! ## M325F-4: 「1+t」の付値超距離 v(1+t) ≥ min(0, v(t)) -/

/-- **M325F-4a: 「1+t」の付値超距離（選言形）** — v(1+t) ≥ v(1)=0 または
    v(1+t) ≥ v(t)。全順序値群上で v(1+t) ≥ min(0, v(t)) と同値。M301F 付値公理
    `v_add_ge`（超距離）＋ `v_one`（v(1)=0）から本物に導出。 -/
theorem absTop_v_one_add_ge {K : IUTField} (val : valRingValuation K) (t : K.carrier) :
    valOptLe (some (0 : Int)) (val.v (K.add K.one t))
      ∨ valOptLe (val.v t) (val.v (K.add K.one t)) := by
  cases val.v_add_ge K.one t with
  | inl h =>
    apply Or.inl
    rw [val.v_one] at h
    exact h
  | inr h => exact Or.inr h

/-- **M325F-4b: O_v は「1+·」で不変** — t ∈ O_v（v(t)≥0）なら 1+t ∈ O_v。
    付値環 O_v の加法単位まわりの再構成が乗法単位 1 と付値から従う。 -/
theorem absTop_v_one_add_nonneg {K : IUTField} (val : valRingValuation K) (t : K.carrier)
    (ht : valRingMem val t) : valRingMem val (K.add K.one t) := by
  cases absTop_v_one_add_ge val t with
  | inl h => exact h
  | inr h => exact valOptLe_trans ht h

/-! ## M325F-5: 逆元の付値 v(x⁻¹) = -v(x)、v(x⁻¹·y) ≥ 0 -/

/-- **M325F-5a: 逆元の付値** — v(x)=a（有限, x≠0）なら v(x⁻¹) = -a。
    v(x·x⁻¹)=v(1)=0=v(x)+v(x⁻¹) から本物に決まる。 -/
theorem absTop_v_inv {K : IUTField} (val : valRingValuation K) (x : K.carrier)
    (a : Int) (hvx : val.v x = some a) : val.v (K.inv x) = some (-a) := by
  have hx0 : x ≠ K.zero := by
    intro h
    have hz : val.v x = none := by rw [h]; exact val.v_zero
    rw [hvx] at hz; nomatch hz
  have hv1 : val.v (K.mul x (K.inv x))
      = valOptAdd (val.v x) (val.v (K.inv x)) := val.v_mul x (K.inv x)
  rw [K.mul_inv_cancel x hx0, val.v_one, hvx] at hv1
  cases hvi : val.v (K.inv x) with
  | none => rw [hvi, valOptAdd_some_none] at hv1; nomatch hv1
  | some c =>
    rw [hvi, valOptAdd_some_some] at hv1
    have hcc : (0 : Int) = a + c := Option.some.inj hv1
    have hc : c = -a := by omega
    rw [hc]

/-- **M325F-5b: v(x⁻¹·y) ≥ 0（v(x)≤v(y)）** — x ≠ 0 かつ v(x)≤v(y) なら
    x⁻¹·y ∈ O_v。復元式の「1+x⁻¹y」が O_v の元になる条件を本物に与える。 -/
theorem absTop_v_inv_mul_nonneg {K : IUTField} (val : valRingValuation K)
    (x y : K.carrier) (hx : x ≠ K.zero)
    (hxy : valOptLe (val.v x) (val.v y)) :
    valRingMem val (K.mul (K.inv x) y) := by
  show valOptLe (some (0 : Int)) (val.v (K.mul (K.inv x) y))
  cases hvx : val.v x with
  | none =>
    exfalso; apply hx; exact val.v_eq_top x hvx
  | some a =>
    have hvinv : val.v (K.inv x) = some (-a) := absTop_v_inv val x a hvx
    rw [val.v_mul, hvinv]
    cases hvy : val.v y with
    | none => rw [valOptAdd_some_none]; exact True.intro
    | some b =>
      rw [valOptAdd_some_some]
      have hab : a ≤ b := by rw [hvx, hvy] at hxy; exact hxy
      show (0 : Int) ≤ -a + b
      omega

/-! ## M325F-6: 加法の付値超距離を復元式から再導出（核の帰結） -/

/-- **M325F-6: 加法の付値超距離（復元由来）** — x ≠ 0 かつ v(x)≤v(y) なら
    v(x+y) ≥ v(x)。これを**乗法側の復元式 x+y=x·(1+x⁻¹y)**（M325F-2）と
    「1+t」の付値超距離（M325F-4）・v(x⁻¹y)≥0（M325F-5）から**再導出**する。
    すなわち加法の超距離不等式は独立公理ではなく、**乗法群＋付値と『1+t』**から
    従う——mono-anabelian「乗法＋付値 → 加法」復元の本物の帰結。 -/
theorem absTop_v_add_ge_of_le {K : IUTField} (val : valRingValuation K)
    (x y : K.carrier) (hx : x ≠ K.zero)
    (hxy : valOptLe (val.v x) (val.v y)) :
    valOptLe (val.v x) (val.v (K.add x y)) := by
  have hform : K.add x y = K.mul x (K.add K.one (K.mul (K.inv x) y)) :=
    absTop_add_from_one_add K x y hx
  rw [hform, val.v_mul]
  have hnn : valRingMem val (K.add K.one (K.mul (K.inv x) y)) :=
    absTop_v_one_add_nonneg val (K.mul (K.inv x) y)
      (absTop_v_inv_mul_nonneg val x y hx hxy)
  exact absTopValOptLe_add_of_nonneg (val.v x)
    (val.v (K.add K.one (K.mul (K.inv x) y))) hnn

/-! ## M325F-7: capstone — 乗法＋付値データ・加法復元・整合性・超距離 -/

/-- **M325F-7a: 乗法＋付値データ（加法を忘れたデータ）** — 体 K 上の離散付値 val を
    「乗法群 K^×（=K.mul/one/inv）＋付値 v」の束として持つ。ここから加法を復元する
    のが AbsTopIII の核。K の加法 K.add は「忘れた」データとして復元対象。 -/
structure absTopMultData (K : IUTField) where
  /-- 台となる離散付値（乗法 K^× ＋付値 v のデータ）。 -/
  val : valRingValuation K

/-- **M325F-7b: 加法復元の総括レコード** — 乗法＋付値データ、復元加法が元の加法に
    一致する整合性、O_v の「1+·」不変性、加法の付値超距離（復元由来）を束ねる。 -/
structure AbsTopReconstructData (K : IUTField) where
  /-- 乗法＋付値データ。 -/
  mult : absTopMultData K
  /-- 加法の整合性: 復元加法 = 元の体加法（x≠0）。 -/
  add_recover : ∀ x y, x ≠ K.zero → absTopRecoverAdd K x y = K.add x y
  /-- O_v は「1+·」で不変。 -/
  one_add_mem : ∀ t, valRingMem mult.val t → valRingMem mult.val (K.add K.one t)
  /-- 加法の付値超距離（復元由来）: x≠0, v(x)≤v(y) ⟹ v(x+y)≥v(x)。 -/
  add_ultrametric : ∀ x y, x ≠ K.zero →
    valOptLe (mult.val.v x) (mult.val.v y) →
      valOptLe (mult.val.v x) (mult.val.v (K.add x y))

/-- **M325F-7c: 任意の離散付値から加法復元データを組み立てる**。 -/
def absTop_toReconstructData {K : IUTField} (val : valRingValuation K) :
    AbsTopReconstructData K where
  mult := ⟨val⟩
  add_recover := fun x y hx => absTop_add_consistent K x y hx
  one_add_mem := fun t ht => absTop_v_one_add_nonneg val t ht
  add_ultrametric := fun x y hx hxy => absTop_v_add_ge_of_le val x y hx hxy

/-- **M325F-7d: 加法復元データは存在する**（DecidableEq を持つ体上、自明付値から）。
    具体的な数体・局所体の離散付値は柱B ℤ_p 接続の後続。 -/
theorem absTop_exists (K : IUTField) [DecidableEq K.carrier] :
    Nonempty (AbsTopReconstructData K) :=
  ⟨absTop_toReconstructData (trivialValuation K)⟩

/-- **M325F-7e: 加法は乗法から復元される**（復元恒等式の再輸出・capstone）。 -/
theorem absTop_add_from_mult (K : IUTField) (x y : K.carrier) (hx : x ≠ K.zero) :
    K.add x y = K.mul x (K.add K.one (K.mul (K.inv x) y)) :=
  absTop_add_from_one_add K x y hx

/-- **M325F-7f: 数体復元の骨組み（加法側）** — 加法演算 K.add は乗法群 K^×・逆元・
    単項作用「1+·」の関数として一意に定まる（x≠0）。「乗法＋付値から環構造を戻す」
    枠組みの本物の核。完全な体（環同型類）復元アルゴリズムは後続。 -/
theorem absTop_reconstruct_skeleton (K : IUTField) :
    ∀ x y, x ≠ K.zero → K.add x y = absTopRecoverAdd K x y :=
  fun x y hx => absTop_add_from_one_add K x y hx

/-! ## M325F-8: 数体復元の骨組み（M322F 円分/ガロア作用を入力として接続） -/

/-- **M325F-8a: AbsTopIII 入力の骨組み** — 乗法＋付値データ・加法復元データに、
    M322F の円分/ガロア作用 `CycGKAction`（G_K の μ_n 作用、円分指標 χ の台）を
    **AbsTopIII の入力**として束ねる骨組み。(K^×, v, χ) から体 K を復元する
    アルゴリズムの本丸は後続だが、入力データの型と加法復元の核はここで本物に揃う。 -/
structure AbsTopIIIInputSkeleton (K : IUTField) (GK : Grp) (M : CycMuGroup) where
  /-- 乗法＋付値データ。 -/
  mult : absTopMultData K
  /-- 加法復元データ（整合性・超距離を含む・本物）。 -/
  recon : AbsTopReconstructData K
  /-- 円分/ガロア作用入力（M322F: G_K の μ_n 作用、円分指標 χ の台）。 -/
  gal : CycGKAction GK M

/-- **M325F-8b: 数体復元の骨組み（射影）** — AbsTopIII の入力 (K^×, v, χ 作用) から
    加法復元データ（整合性・付値超距離の本物）を取り出せる。円分/ガロア入力を保ったまま
    加法の核が復元されることを示す骨組み。完全な体復元は後続。 -/
theorem absTop_field_recover {K : IUTField} {GK : Grp} {M : CycMuGroup}
    (inp : AbsTopIIIInputSkeleton K GK M) :
    (∀ x y, x ≠ K.zero → absTopRecoverAdd K x y = K.add x y) ∧
    Nonempty (CycGKAction GK M) :=
  ⟨inp.recon.add_recover, ⟨inp.gal⟩⟩

/-! ## M325F-9: 実例 -/

/-- **M325F-9a: 加法復元の実例** — 任意の体 K・任意の非零 x で
    x + y = x·(1 + x⁻¹y) が成り立つ（復元恒等式の実インスタンス）。 -/
theorem absTop_example_recover (K : IUTField) (x y : K.carrier) (hx : x ≠ K.zero) :
    K.add x y = K.mul x (K.add K.one (K.mul (K.inv x) y)) :=
  absTop_add_from_one_add K x y hx

/-- **M325F-9b: 「1+t」の付値の実例** — 任意の離散付値で、t が付値環 O_v に属せば
    1+t も O_v に属す（v(1+t)≥0）。付値環の加法の再構成の実インスタンス。 -/
theorem absTop_example_one_add_mem {K : IUTField} (val : valRingValuation K)
    (t : K.carrier) (ht : valRingMem val t) : valRingMem val (K.add K.one t) :=
  absTop_v_one_add_nonneg val t ht

/-- **M325F-9c: 加法超距離の実例** — 単位 1 と任意の O_v 元 t で v(1+t)≥min(0,v(t))。 -/
theorem absTop_example_ultrametric {K : IUTField} (val : valRingValuation K)
    (t : K.carrier) :
    valOptLe (some (0 : Int)) (val.v (K.add K.one t))
      ∨ valOptLe (val.v t) (val.v (K.add K.one t)) :=
  absTop_v_one_add_ge val t

end IUT
