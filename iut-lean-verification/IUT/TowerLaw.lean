/-
  IUT/TowerLaw.lean — M281F: 体拡大の次数の塔法則 [M:K] = [M:L]·[L:K]
  ── 柱A 実代数拡大の次数論の本物の先行建設

  ── 主要成果の分類: **[実]**（本物の K-加群・有限基底・体拡大の塔上での
     拡大次数の乗法性を core Lean のみで実構成）。

  complete_pct 影響: **柱A「実代数拡大の次数」の本物の先行建設**。遠アーベル
  復元・分離次数・ガロア対応は「体拡大 K⊆L の次数 [L:K]」と、拡大の塔
  K⊆L⊆M に対する**次数の乗法性 [M:K]=[M:L]·[L:K]** を基礎語彙とする。既存資産は
  * `Field.lean`（M264F）＝本物の体 `IUTField`、
  * `FieldAutGroup.lean`（M271F）＝体拡大 `FieldExtension`（環準同型埋め込み ι:K→L）、
  * `MinimalPolynomial.lean`（M273F）＝代数的元・最小多項式
  を持つが、**「体拡大を K-ベクトル空間として見た次数」と「次数の乗法性（塔法則）」
  は 0 ファイル**であった。本モジュールがそれを本物に構成する。

  塔法則の代数的核は「被覆の合成でファイバー数が積になる」ことであり、その代数的
  中身は次の一段：K⊆L の K-基底 {xᵢ}（m 個）と L⊆M の L-基底 {yⱼ}（n 個）から、
  積 {xᵢyⱼ}（m·n 個）が M の K-基底をなす、すなわち [M:K]=[M:L]·[L:K]=n·m。

  * M281F-1 `TowerLawModule`      — R-加群（R の作用付きアーベル群、加群公理）。
    補助 `addZeroM`/`addLeftCancelM`/`smulZeroM`/`smulNegM`/`negZeroM`/`negAddM`/`add4M`。
  * M281F-2 `towerLawRegModule`   — 体 L の正則表現（L を L-加群として）。
    `towerLawRestrict` — ι:K→L によるスカラー制限（L-加群 → K-加群）。
  * M281F-3 `towerLawSum`         — 有限和（Fin n 添字の加群元の和）とその
    合同 `towerLawSum_congr`・零 `towerLawSum_zero`・加法性 `towerLawSum_add`・
    符号 `towerLawSum_neg`・制限橋渡し `towerLawSum_restrict`・
    スカラー左分配 `towerLaw_smul_sum_left`。
  * M281F-4 `TowerLawBasis`       — 有限基底（張る family `vec` + 座標 `repr` +
    張る性 `spans` + 一次独立 `indep`）。`towerLaw_coord_unique`（座標の一意性）。
  * M281F-5 `towerLawDegree`      — 基底からの拡大次数 [L:K]（基底要素数）。
  * M281F-6 `TowerData`/`towerLawProd`/`towerLawColSum`/`towerLaw_linComb2_eq`
    ── **塔法則の本丸**：`towerLaw_prod_spans`（積 {xᵢyⱼ} が M を K-上張る）・
    `towerLaw_prod_indep`（積が K-上一次独立）。
  * M281F-7 capstone: `TowerLawProdBasis`/`towerLaw_basis_product`（積基底の構成）・
    `towerLawProdDegree`/`towerLaw_degree_mul`（[M:K]=[M:L]·[L:K]）・`towerLaw_exists`。

  意義: 拡大次数＝被覆のファイバー基数の乗法性の代数的核。分離次数・ガロア対応・
  π₁^ét のファイバー計算の最下層。

  **正直な限定（何が本物で何が honest 仮説か）**:
   - **本物**: `TowerLawModule`（加群公理）と有限基底 witness（張る + 一次独立）を
     入力とするとき、積 {xᵢyⱼ} が M の K-基底をなすこと（張る性・一次独立の**両方**）
     は完全証明（sorry 皆無・新規 Classical.choice 皆無・禁止タクティク不使用）。
     張る性は「M の L-展開 → 各 L-係数の K-展開 → xᵢyⱼ の K-結合」、一次独立は
     「yⱼ の L-独立で各 L-係数 = 0 → xᵢ の K-独立で全係数 = 0」で閉じる。
     よって次数の乗法性 [M:K]=[M:L]·[L:K] が本物に従う。
   - **honest 仮説 1（基底 = witness）**: 基底・有限次元は witness（族 `vec` +
     張る `spans` + 一次独立 `indep`）として受け取る（一般の次元 well-defined 性・
     基底の存在は抽象体上で選択原理を要するため、有限基底を入力とする。M273F と同精神）。
   - **honest 仮説 2（スカラー作用 = 加群構造）**: スカラー体の作用は R-加群構造
     `TowerLawModule` の公理として仮説で受け取る（L の K-加群構造は ι:K→L による
     スカラー制限 `towerLawRestrict` として本物に構成する）。
   - **honest 仮説 3（積基底の添字）**: 積基底 {xᵢyⱼ} は `Fin m × Fin n`
     （二重添字、基数 m·n）で扱い、`Fin (m·n)` への再添字（全単射 Fin m × Fin n ≃
     Fin(m·n)）は div/mod を要する簿記のみの一段のため省略する。次数は基数 m·n
     であり、乗法性 [M:K]=m·n=[M:L]·[L:K] は本物（基底性そのものが実質内容）。
   - 本モジュールは体拡大を FieldExtension（環準同型埋め込み ι:K→L）で扱い、
     単一の体の塔 K⊆L⊆M（L は M の作用体）上で塔法則を構成する。

  全て選択公理不使用（新規 choice を証明本体に導入しない）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。
-/
import IUT.FieldAutGroup

namespace IUT

/-! ## M281F-0: CRing 補助 -/

/-- 右 0 加法（可換性 + zero_add）。 -/
theorem towerLaw_cring_add_zero (R : CRing) (a : R.carrier) : R.add a R.zero = a := by
  rw [R.add_comm]
  exact R.zero_add a

/-- 左 0 乗法（可換性 + mul_zero）。 -/
theorem towerLaw_cring_zero_mul (R : CRing) (a : R.carrier) : R.mul R.zero a = R.zero := by
  rw [R.mul_comm]
  exact CRing.mul_zero R a

/-- **埋め込みは 0 を保つ**: ι(0)=0（加法性 + 加法消去）。 -/
theorem towerLaw_incl_zero (E : FieldExtension) : E.incl E.base.zero = E.top.zero := by
  have h : E.incl E.base.zero = E.top.add (E.incl E.base.zero) (E.incl E.base.zero) := by
    have h2 := E.incl_add E.base.zero E.base.zero
    rw [E.base.zero_add] at h2
    exact h2
  have h3 : E.top.add (E.incl E.base.zero) E.top.zero
      = E.top.add (E.incl E.base.zero) (E.incl E.base.zero) := by
    rw [towerLaw_cring_add_zero E.top.toCRing]
    exact h
  exact (CRing.add_left_cancel E.top.toCRing h3).symm

/-! ## M281F-1: R-加群 -/

/-- **M281F-1: R-加群** — 環（体）`R` の作用 `smul` を持つアーベル群。
    加群公理（分配・結合・単位・零）を本物に要求する。体拡大 L/K を「K-上の
    ベクトル空間」として扱う枠。 -/
structure TowerLawModule (R : IUTField) where
  /-- 台。 -/
  carrier : Type
  /-- 加法。 -/
  add : carrier → carrier → carrier
  /-- 零元。 -/
  zero : carrier
  /-- 反元。 -/
  neg : carrier → carrier
  /-- スカラー作用。 -/
  smul : R.carrier → carrier → carrier
  /-- 加法結合律。 -/
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  /-- 左零加法。 -/
  zero_add : ∀ a, add zero a = a
  /-- 左反元。 -/
  neg_add : ∀ a, add (neg a) a = zero
  /-- 加法可換律。 -/
  add_comm : ∀ a b, add a b = add b a
  /-- スカラーの加法分配（ベクトル側）。 -/
  smul_add : ∀ (a : R.carrier) (x y), smul a (add x y) = add (smul a x) (smul a y)
  /-- スカラーの加法分配（スカラー側）。 -/
  add_smul : ∀ (a b : R.carrier) (x), smul (R.add a b) x = add (smul a x) (smul b x)
  /-- スカラーの乗法結合。 -/
  mul_smul : ∀ (a b : R.carrier) (x), smul (R.mul a b) x = smul a (smul b x)
  /-- 単位スカラー。 -/
  one_smul : ∀ x, smul R.one x = x
  /-- 零スカラー。 -/
  zero_smul : ∀ x, smul R.zero x = zero

namespace TowerLawModule

/-- 右 0 加法。 -/
theorem addZeroM {R : IUTField} (V : TowerLawModule R) (a : V.carrier) :
    V.add a V.zero = a := by
  rw [V.add_comm]
  exact V.zero_add a

/-- 4 項入替: (a+b)+(c+d) = (a+c)+(b+d)。 -/
theorem add4M {R : IUTField} (V : TowerLawModule R) (a b c d : V.carrier) :
    V.add (V.add a b) (V.add c d) = V.add (V.add a c) (V.add b d) := by
  rw [V.add_assoc a b (V.add c d), ← V.add_assoc b c d, V.add_comm b c,
    V.add_assoc c b d, ← V.add_assoc a c (V.add b d)]

/-- 加法左消去。 -/
theorem addLeftCancelM {R : IUTField} (V : TowerLawModule R) (a b c : V.carrier)
    (h : V.add a b = V.add a c) : b = c := by
  have e : b = V.add (V.add (V.neg a) a) b := by
    rw [V.neg_add, V.zero_add]
  rw [V.add_assoc] at e
  rw [h] at e
  rw [← V.add_assoc, V.neg_add, V.zero_add] at e
  exact e

/-- 零のスカラー倍は零。 -/
theorem smulZeroM {R : IUTField} (V : TowerLawModule R) (a : R.carrier) :
    V.smul a V.zero = V.zero := by
  have h : V.smul a V.zero = V.add (V.smul a V.zero) (V.smul a V.zero) := by
    have h2 := V.smul_add a V.zero V.zero
    rw [V.zero_add] at h2
    exact h2
  have h3 : V.add (V.smul a V.zero) V.zero = V.add (V.smul a V.zero) (V.smul a V.zero) := by
    rw [V.addZeroM]
    exact h
  exact (V.addLeftCancelM _ _ _ h3).symm

/-- 反元のスカラー: (-a)•x = -(a•x)。 -/
theorem smulNegM {R : IUTField} (V : TowerLawModule R) (a : R.carrier) (x : V.carrier) :
    V.smul (R.neg a) x = V.neg (V.smul a x) := by
  have haz : R.add a (R.neg a) = R.zero := by
    rw [R.add_comm]
    exact R.neg_add a
  have key : V.add (V.smul a x) (V.smul (R.neg a) x) = V.zero := by
    rw [← V.add_smul a (R.neg a) x, haz, V.zero_smul]
  have key2 : V.add (V.smul a x) (V.neg (V.smul a x)) = V.zero := by
    rw [V.add_comm]
    exact V.neg_add (V.smul a x)
  have e : V.add (V.smul a x) (V.smul (R.neg a) x)
      = V.add (V.smul a x) (V.neg (V.smul a x)) := by
    rw [key, key2]
  exact V.addLeftCancelM _ _ _ e

/-- 零の反元は零。 -/
theorem negZeroM {R : IUTField} (V : TowerLawModule R) : V.neg V.zero = V.zero := by
  have h := V.neg_add V.zero
  rw [V.addZeroM] at h
  exact h

/-- 和の反元は反元の和。 -/
theorem negAddM {R : IUTField} (V : TowerLawModule R) (a b : V.carrier) :
    V.neg (V.add a b) = V.add (V.neg a) (V.neg b) := by
  have haa : V.add a (V.neg a) = V.zero := by
    rw [V.add_comm]
    exact V.neg_add a
  have hbb : V.add b (V.neg b) = V.zero := by
    rw [V.add_comm]
    exact V.neg_add b
  have key : V.add (V.add a b) (V.add (V.neg a) (V.neg b)) = V.zero := by
    rw [V.add4M a b (V.neg a) (V.neg b), haa, hbb, V.zero_add]
  have key2 : V.add (V.add a b) (V.neg (V.add a b)) = V.zero := by
    rw [V.add_comm]
    exact V.neg_add (V.add a b)
  have e : V.add (V.add a b) (V.neg (V.add a b))
      = V.add (V.add a b) (V.add (V.neg a) (V.neg b)) := by
    rw [key, key2]
  exact V.addLeftCancelM _ _ _ e

end TowerLawModule

/-! ## M281F-2: 正則表現とスカラー制限 -/

/-- **M281F-2a: 体 L の正則表現** — L を自分自身への L-加群（作用 = 乗法）として。 -/
def towerLawRegModule (L : IUTField) : TowerLawModule L where
  carrier := L.carrier
  add := L.add
  zero := L.zero
  neg := L.neg
  smul := L.mul
  add_assoc := L.add_assoc
  zero_add := L.zero_add
  neg_add := L.neg_add
  add_comm := L.add_comm
  smul_add := L.left_distrib
  add_smul := fun a b x => CRing.right_distrib L.toCRing a b x
  mul_smul := L.mul_assoc
  one_smul := L.one_mul
  zero_smul := fun x => towerLaw_cring_zero_mul L.toCRing x

/-- **M281F-2b: スカラー制限** — 埋め込み ι:K→L により L-加群 V を K-加群として見る
    （a •ₖ v := ι(a) •ₗ v）。これで L を K-加群（K-ベクトル空間）として本物に得る。 -/
def towerLawRestrict (E : FieldExtension) (V : TowerLawModule E.top) :
    TowerLawModule E.base where
  carrier := V.carrier
  add := V.add
  zero := V.zero
  neg := V.neg
  smul := fun a v => V.smul (E.incl a) v
  add_assoc := V.add_assoc
  zero_add := V.zero_add
  neg_add := V.neg_add
  add_comm := V.add_comm
  smul_add := fun a x y => V.smul_add (E.incl a) x y
  add_smul := fun a b x => by
    show V.smul (E.incl (E.base.add a b)) x
      = V.add (V.smul (E.incl a) x) (V.smul (E.incl b) x)
    rw [E.incl_add]
    exact V.add_smul (E.incl a) (E.incl b) x
  mul_smul := fun a b x => by
    show V.smul (E.incl (E.base.mul a b)) x = V.smul (E.incl a) (V.smul (E.incl b) x)
    rw [E.incl_mul]
    exact V.mul_smul (E.incl a) (E.incl b) x
  one_smul := fun x => by
    show V.smul (E.incl E.base.one) x = x
    rw [E.incl_one]
    exact V.one_smul x
  zero_smul := fun x => by
    show V.smul (E.incl E.base.zero) x = V.zero
    rw [towerLaw_incl_zero E]
    exact V.zero_smul x

/-! ## M281F-3: 有限和 -/

/-- **M281F-3a: 有限和**（Fin n 添字の加群元の和; 左から順に加える）。 -/
def towerLawSum {R : IUTField} (V : TowerLawModule R) :
    (n : Nat) → (Fin n → V.carrier) → V.carrier
  | 0, _ => V.zero
  | n + 1, f =>
    V.add (towerLawSum V n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      (f ⟨n, Nat.lt_succ_self n⟩)

/-- 一段展開（定義等式）。 -/
theorem towerLawSum_succ {R : IUTField} (V : TowerLawModule R) (n : Nat)
    (f : Fin (n + 1) → V.carrier) :
    towerLawSum V (n + 1) f
      = V.add (towerLawSum V n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
          (f ⟨n, Nat.lt_succ_self n⟩) := rfl

/-- 正則表現の和の一段展開（L.add で明示）。 -/
theorem towerLawRegSum_succ (L : IUTField) (n : Nat)
    (f : Fin (n + 1) → L.carrier) :
    towerLawSum (towerLawRegModule L) (n + 1) f
      = L.add (towerLawSum (towerLawRegModule L) n
          (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
          (f ⟨n, Nat.lt_succ_self n⟩) := rfl

/-- 各項が一致すれば和も一致。 -/
theorem towerLawSum_congr {R : IUTField} (V : TowerLawModule R) :
    ∀ (n : Nat) (f g : Fin n → V.carrier),
      (∀ i, f i = g i) → towerLawSum V n f = towerLawSum V n g := by
  intro n
  induction n with
  | zero =>
    intro f g _
    rfl
  | succ m ih =>
    intro f g h
    rw [towerLawSum_succ V m f, towerLawSum_succ V m g,
      ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩),
      h ⟨m, Nat.lt_succ_self m⟩]

/-- 各項が 0 なら和は 0。 -/
theorem towerLawSum_zero {R : IUTField} (V : TowerLawModule R) :
    ∀ (n : Nat) (f : Fin n → V.carrier),
      (∀ i, f i = V.zero) → towerLawSum V n f = V.zero := by
  intro n
  induction n with
  | zero =>
    intro f _
    rfl
  | succ m ih =>
    intro f h
    rw [towerLawSum_succ V m f,
      ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩),
      h ⟨m, Nat.lt_succ_self m⟩, V.zero_add]

/-- 和の加法性: Σ(fᵢ+gᵢ) = Σfᵢ + Σgᵢ。 -/
theorem towerLawSum_add {R : IUTField} (V : TowerLawModule R) :
    ∀ (n : Nat) (f g : Fin n → V.carrier),
      towerLawSum V n (fun i => V.add (f i) (g i))
        = V.add (towerLawSum V n f) (towerLawSum V n g) := by
  intro n
  induction n with
  | zero =>
    intro f g
    exact (V.addZeroM V.zero).symm
  | succ m ih =>
    intro f g
    rw [towerLawSum_succ V m (fun i => V.add (f i) (g i))]
    rw [ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
    rw [towerLawSum_succ V m f, towerLawSum_succ V m g]
    exact V.add4M _ _ _ _

/-- 和の符号: Σ(-fᵢ) = -(Σfᵢ)。 -/
theorem towerLawSum_neg {R : IUTField} (V : TowerLawModule R) :
    ∀ (n : Nat) (f : Fin n → V.carrier),
      towerLawSum V n (fun i => V.neg (f i)) = V.neg (towerLawSum V n f) := by
  intro n
  induction n with
  | zero =>
    intro f
    exact V.negZeroM.symm
  | succ m ih =>
    intro f
    rw [towerLawSum_succ V m (fun i => V.neg (f i))]
    rw [ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
    rw [towerLawSum_succ V m f]
    exact (V.negAddM _ _).symm

/-- スカラー制限の和は元の和に等しい（add/zero が定義的に一致）。 -/
theorem towerLawSum_restrict (E : FieldExtension) (V : TowerLawModule E.top) :
    ∀ (n : Nat) (f : Fin n → V.carrier),
      towerLawSum (towerLawRestrict E V) n f = towerLawSum V n f := by
  intro n
  induction n with
  | zero =>
    intro f
    rfl
  | succ m ih =>
    intro f
    show V.add (towerLawSum (towerLawRestrict E V) m
        (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) (f ⟨m, Nat.lt_succ_self m⟩)
      = V.add (towerLawSum V m (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
          (f ⟨m, Nat.lt_succ_self m⟩)
    rw [ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]

/-- **スカラー左分配（塔をまたぐ）**: (Σᵢ wᵢ) •ₘ y = Σᵢ (wᵢ •ₘ y)。
    L-加群 M への L の作用が第 1 引数について有限和と可換であること。 -/
theorem towerLaw_smul_sum_left (L : IUTField) (M : TowerLawModule L) :
    ∀ (k : Nat) (w : Fin k → L.carrier) (y : M.carrier),
      M.smul (towerLawSum (towerLawRegModule L) k w) y
        = towerLawSum M k (fun i => M.smul (w i) y) := by
  intro k
  induction k with
  | zero =>
    intro w y
    exact M.zero_smul y
  | succ m ih =>
    intro w y
    rw [towerLawRegSum_succ L m w]
    rw [M.add_smul]
    rw [ih (fun i => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) y]
    rw [towerLawSum_succ M m (fun i => M.smul (w i) y)]

/-! ## M281F-4: 有限基底 -/

/-- **M281F-4: 有限基底** — 加群 V の R-基底は、張る family `vec : Fin dim → V`、
    座標写像 `repr`、張る性 `spans`（任意元が座標での線形結合）、一次独立 `indep`
    （零になる係数は全て零）からなる。次元 = `dim`（基底の要素数）。 -/
structure TowerLawBasis (R : IUTField) (V : TowerLawModule R) where
  /-- 次元（基底の要素数）。 -/
  dim : Nat
  /-- 基底ベクトル族。 -/
  vec : Fin dim → V.carrier
  /-- 座標写像。 -/
  repr : V.carrier → Fin dim → R.carrier
  /-- 張る性: 任意 v は基底の線形結合。 -/
  spans : ∀ v, v = towerLawSum V dim (fun i => V.smul (repr v i) (vec i))
  /-- 一次独立: 零になる係数は全て零。 -/
  indep : ∀ (c : Fin dim → R.carrier),
    towerLawSum V dim (fun i => V.smul (c i) (vec i)) = V.zero → ∀ i, c i = R.zero

/-- **M281F-4b: 座標の一意性** — 同じ元を表す座標は一致する。 -/
theorem towerLaw_coord_unique {R : IUTField} {V : TowerLawModule R}
    (b : TowerLawBasis R V) (c c' : Fin b.dim → R.carrier)
    (h : towerLawSum V b.dim (fun i => V.smul (c i) (b.vec i))
       = towerLawSum V b.dim (fun i => V.smul (c' i) (b.vec i))) :
    ∀ i, c i = c' i := by
  intro i
  have hzero : towerLawSum V b.dim
      (fun k => V.smul (R.add (c k) (R.neg (c' k))) (b.vec k)) = V.zero := by
    have step : ∀ k, V.smul (R.add (c k) (R.neg (c' k))) (b.vec k)
        = V.add (V.smul (c k) (b.vec k)) (V.neg (V.smul (c' k) (b.vec k))) := by
      intro k
      rw [V.add_smul, V.smulNegM]
    rw [towerLawSum_congr V b.dim _ _ step]
    rw [towerLawSum_add V b.dim (fun k => V.smul (c k) (b.vec k))
        (fun k => V.neg (V.smul (c' k) (b.vec k)))]
    rw [towerLawSum_neg V b.dim (fun k => V.smul (c' k) (b.vec k))]
    rw [h]
    rw [V.add_comm]
    exact V.neg_add _
  have he := b.indep (fun k => R.add (c k) (R.neg (c' k))) hzero i
  have e1 : R.add (R.add (c i) (R.neg (c' i))) (c' i) = c' i := by
    rw [he, R.zero_add]
  rw [R.add_assoc] at e1
  rw [R.neg_add] at e1
  rw [towerLaw_cring_add_zero R.toCRing] at e1
  exact e1

/-! ## M281F-5: 拡大次数 -/

/-- **M281F-5: 拡大次数 [L:K]** — 基底の要素数。基底 witness を入力とするときの
    次数（一般の次元 well-defined 性は選択原理を要するため witness 依存）。 -/
def towerLawDegree {R : IUTField} {V : TowerLawModule R} (b : TowerLawBasis R V) : Nat :=
  b.dim

/-! ## M281F-6: 塔法則の本丸 -/

/-- **M281F-6a: 塔データ** — 体拡大の塔 K⊆L⊆M（ext=ι:K→L、M は L-加群）と、
    L の K-基底 {xᵢ}・M の L-基底 {yⱼ}。 -/
structure TowerData where
  /-- 体拡大 K⊆L（base=K, top=L, incl=ι）。 -/
  ext : FieldExtension
  /-- 上体 L 上の加群 M。 -/
  M : TowerLawModule ext.top
  /-- L の K-基底（L をスカラー制限で K-加群として）。 -/
  basisLK : TowerLawBasis ext.base (towerLawRestrict ext (towerLawRegModule ext.top))
  /-- M の L-基底。 -/
  basisML : TowerLawBasis ext.top M

/-- **M281F-6b: 積基底ベクトル** xᵢ·yⱼ = xᵢ •ₘ yⱼ。 -/
def towerLawProd (T : TowerData) (i : Fin T.basisLK.dim) (j : Fin T.basisML.dim) :
    T.M.carrier :=
  T.M.smul (T.basisLK.vec i) (T.basisML.vec j)

/-- **M281F-6c: 列和** cⱼ = Σᵢ (係数 i j) •ₖ xᵢ ∈ L（各 j での L-係数）。 -/
def towerLawColSum (T : TowerData)
    (c : Fin T.basisLK.dim → Fin T.basisML.dim → T.ext.base.carrier)
    (j : Fin T.basisML.dim) : T.ext.top.carrier :=
  towerLawSum (towerLawRestrict T.ext (towerLawRegModule T.ext.top)) T.basisLK.dim
    (fun i => (towerLawRestrict T.ext (towerLawRegModule T.ext.top)).smul (c i j)
      (T.basisLK.vec i))

/-- **M281F-6d: 二重和の再結合** — Σⱼ Σᵢ (係数)•ₘ(xᵢyⱼ) = Σⱼ cⱼ •ₘ yⱼ。
    塔法則の張る性・独立性の両方の核となる等式。 -/
theorem towerLaw_linComb2_eq (T : TowerData)
    (c : Fin T.basisLK.dim → Fin T.basisML.dim → T.ext.base.carrier) :
    towerLawSum T.M T.basisML.dim (fun j =>
       towerLawSum T.M T.basisLK.dim (fun i =>
         T.M.smul (T.ext.incl (c i j)) (towerLawProd T i j)))
    = towerLawSum T.M T.basisML.dim (fun j =>
         T.M.smul (towerLawColSum T c j) (T.basisML.vec j)) := by
  apply towerLawSum_congr
  intro j
  have step1 : towerLawSum T.M T.basisLK.dim (fun i =>
        T.M.smul (T.ext.incl (c i j)) (towerLawProd T i j))
      = towerLawSum T.M T.basisLK.dim (fun i =>
        T.M.smul (T.ext.top.mul (T.ext.incl (c i j)) (T.basisLK.vec i))
          (T.basisML.vec j)) := by
    apply towerLawSum_congr
    intro i
    show T.M.smul (T.ext.incl (c i j)) (T.M.smul (T.basisLK.vec i) (T.basisML.vec j))
       = T.M.smul (T.ext.top.mul (T.ext.incl (c i j)) (T.basisLK.vec i)) (T.basisML.vec j)
    rw [T.M.mul_smul]
  rw [step1]
  rw [← towerLaw_smul_sum_left T.ext.top T.M T.basisLK.dim
        (fun i => T.ext.top.mul (T.ext.incl (c i j)) (T.basisLK.vec i)) (T.basisML.vec j)]
  have hcol : towerLawSum (towerLawRegModule T.ext.top) T.basisLK.dim
        (fun i => T.ext.top.mul (T.ext.incl (c i j)) (T.basisLK.vec i))
      = towerLawColSum T c j := by
    show towerLawSum (towerLawRegModule T.ext.top) T.basisLK.dim
        (fun i => T.ext.top.mul (T.ext.incl (c i j)) (T.basisLK.vec i))
      = towerLawSum (towerLawRestrict T.ext (towerLawRegModule T.ext.top)) T.basisLK.dim
          (fun i => (towerLawRestrict T.ext (towerLawRegModule T.ext.top)).smul (c i j)
            (T.basisLK.vec i))
    exact (towerLawSum_restrict T.ext (towerLawRegModule T.ext.top) T.basisLK.dim
      (fun i => (towerLawRestrict T.ext (towerLawRegModule T.ext.top)).smul (c i j)
        (T.basisLK.vec i))).symm
  rw [hcol]

/-- **M281F-6e: 張る性** — 任意 z∈M は積 {xᵢyⱼ} の K-線形結合で表せる。
    （M を yⱼ で L-展開し、各 L-係数を xᵢ で K-展開する。） -/
theorem towerLaw_prod_spans (T : TowerData) (z : T.M.carrier) :
    z = towerLawSum T.M T.basisML.dim (fun j =>
          towerLawSum T.M T.basisLK.dim (fun i =>
            T.M.smul (T.ext.incl (T.basisLK.repr (T.basisML.repr z j) i))
              (towerLawProd T i j))) := by
  have A := T.basisML.spans z
  have B := towerLaw_linComb2_eq T (fun i j => T.basisLK.repr (T.basisML.repr z j) i)
  have D : towerLawSum T.M T.basisML.dim (fun j =>
        T.M.smul (towerLawColSum T (fun i j => T.basisLK.repr (T.basisML.repr z j) i) j)
          (T.basisML.vec j))
      = towerLawSum T.M T.basisML.dim (fun j =>
        T.M.smul (T.basisML.repr z j) (T.basisML.vec j)) := by
    apply towerLawSum_congr
    intro j
    have hcoleq : towerLawColSum T (fun i j => T.basisLK.repr (T.basisML.repr z j) i) j
        = T.basisML.repr z j := (T.basisLK.spans (T.basisML.repr z j)).symm
    rw [hcoleq]
  exact A.trans (D.symm.trans B.symm)

/-- **M281F-6f: 一次独立** — 積 {xᵢyⱼ} の K-線形結合が零なら全係数が零。
    （yⱼ の L-独立で各 L-係数 cⱼ=0、次に xᵢ の K-独立で全係数=0。） -/
theorem towerLaw_prod_indep (T : TowerData)
    (c : Fin T.basisLK.dim → Fin T.basisML.dim → T.ext.base.carrier)
    (h : towerLawSum T.M T.basisML.dim (fun j =>
          towerLawSum T.M T.basisLK.dim (fun i =>
            T.M.smul (T.ext.incl (c i j)) (towerLawProd T i j))) = T.M.zero) :
    ∀ i j, c i j = T.ext.base.zero := by
  intro i j
  have h1 : towerLawSum T.M T.basisML.dim (fun j =>
        T.M.smul (towerLawColSum T c j) (T.basisML.vec j)) = T.M.zero := by
    rw [← towerLaw_linComb2_eq T c]
    exact h
  have hcol := T.basisML.indep (fun j => towerLawColSum T c j) h1
  have hlk := T.basisLK.indep (fun i => c i j) (hcol j)
  exact hlk i

/-! ## M281F-7: capstone -/

/-- **M281F-7a: 積基底** — 体拡大 E と加群 M に対する二重添字（Fin m × Fin n）の
    有限基底（基数 m·n）。張る性・一次独立を束ねる。 -/
structure TowerLawProdBasis (E : FieldExtension) (Mmod : TowerLawModule E.top) where
  /-- L の K-次元 [L:K]。 -/
  m : Nat
  /-- M の L-次元 [M:L]。 -/
  n : Nat
  /-- 積基底ベクトル族 xᵢyⱼ。 -/
  vec : Fin m → Fin n → Mmod.carrier
  /-- 座標写像（二重添字）。 -/
  repr : Mmod.carrier → Fin m → Fin n → E.base.carrier
  /-- 張る性。 -/
  spans : ∀ z, z = towerLawSum Mmod n (fun j =>
    towerLawSum Mmod m (fun i => Mmod.smul (E.incl (repr z i j)) (vec i j)))
  /-- 一次独立。 -/
  indep : ∀ (c : Fin m → Fin n → E.base.carrier),
    towerLawSum Mmod n (fun j =>
      towerLawSum Mmod m (fun i => Mmod.smul (E.incl (c i j)) (vec i j))) = Mmod.zero →
      ∀ i j, c i j = E.base.zero

/-- **M281F-7b: 積基底の構成** — 塔データから積基底 {xᵢyⱼ} を本物に構成する。
    塔法則の本丸（張る性 + 一次独立の完全証明）。 -/
def towerLaw_basis_product (T : TowerData) : TowerLawProdBasis T.ext T.M where
  m := T.basisLK.dim
  n := T.basisML.dim
  vec := fun i j => towerLawProd T i j
  repr := fun z i j => T.basisLK.repr (T.basisML.repr z j) i
  spans := towerLaw_prod_spans T
  indep := towerLaw_prod_indep T

/-- **M281F-7c: 積基底の次数** [M:K] = m·n（[L:K]·[M:L]）。 -/
def towerLawProdDegree (T : TowerData) : Nat :=
  T.basisLK.dim * T.basisML.dim

/-- **M281F-7d: 次数の乗法性（塔法則）** [M:K] = [M:L]·[L:K]。
    実質内容（積が基底をなすこと）は `towerLaw_basis_product` で本物に証明済み。 -/
theorem towerLaw_degree_mul (T : TowerData) :
    towerLawProdDegree T = towerLawDegree T.basisML * towerLawDegree T.basisLK := by
  show T.basisLK.dim * T.basisML.dim = T.basisML.dim * T.basisLK.dim
  exact Nat.mul_comm T.basisLK.dim T.basisML.dim

/-- **M281F-7e: 塔法則の存在** — 任意の塔データに対し積基底が存在する。 -/
theorem towerLaw_exists (T : TowerData) : Nonempty (TowerLawProdBasis T.ext T.M) :=
  ⟨towerLaw_basis_product T⟩

end IUT
