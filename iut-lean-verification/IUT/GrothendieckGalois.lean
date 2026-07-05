/-
  IUT/GrothendieckGalois.lean — M277F: Grothendieck ガロア理論の骨組み π₁^ét := Aut(F)
  ── 柱A 実 π₁^ét(Spec K) 復元の本丸（ファイバー関手の自然変換自己同型群）の
     本物の先行建設

  分類 **[実]**（本物のファイバー関手 = 有限エタール被覆の切断集合・本物の
  自然変換自己同型群 Aut(F) = π₁^ét の骨組み・本物の Gal(L/K) → π₁ 後合成準同型。
  toy 群・surrogate を主語にしない）。

  **complete_pct 影響: 柱A 実 π₁^ét(Spec K) 復元の中心イディオム
  「π₁^ét := Aut(ファイバー関手)」を本物で初建設**。M272F（FÉt(K) の対象と射 =
  本物の K-代数）が建てた被覆側の圏の上に、
  * ファイバー関手 F_Ω(K^n) := Hom_{K-alg}(K^n, Ω)（幾何的点 Spec Ω → Spec K
    でのファイバー = 本物の Ω 値点集合）を本物の関手（`grGalFiberFunctor` :
    分裂骨格の逆圏 → SetCat）として、
  * **π₁^ét := Aut(F)**（各成分が全単射な自己自然変換の群 `piEtGroupAt`/
    `piEtGroup`; 全単射性は明示逆成分 witness で choice 回避）を本物の群として、
  * π₁ のファイバーへの**作用**（`grGal_action`: 群作用則 e·x=x, (gh)·x=g·(h·x)
    完全証明）と**自明被覆上のモノドロミー自明性**（`grGal_split_trivial`:
    標準切断は π₁ の全元で固定 = Spec K 連結・基点唯一の骨組み）を、
  * **Gal(L/K) → π₁ の準同型**（`grGal_fromGalois`: K を固定する体自己同型が
    切断に後合成で誘導する自然変換; Galois 固定条件が compat の証明に本質使用）を、
  それぞれ完全証明つきで確立する。これは実 π₁^ét = Gal(K^sep/K) 復元
  （遠アーベルの入口）の**本コースの一段**であり、後続（分離拡大による非分裂
  対象の追加）で同じ定義 Aut(F) がそのまま非自明な π₁^ét を与える。

  * M277F-0 `grGalRingHom_map_zero` — 環準同型の 0 保存（加法性から導出）
  * M277F-1 `grGalFiber` / `grGalPull` / `grGalPull_id` / `grGalPull_comp` —
    ファイバー = 切断集合 Hom_{K-alg}(K^n, Ω) と射に沿った引き戻し（関手性）
  * M277F-2 `grGalSplitOp` / `grGalFiberFunctor` — 分裂骨格の逆圏と
    **本物のファイバー関手 F : (分裂骨格)^op → SetCat**（M19 の Functor として）
  * M277F-3 `grGalAut` / `grGalAut.ext` / `grGalAut.inv_natural` /
    `grGalAutId` / `grGalAutComp` / `grGalAutInv` / `grGalAutNatTrans` —
    **Aut(F) の元**（自然変換 + 各成分の明示逆 witness）と恒等・合成・逆、
    逆成分の自然性の完全証明、M19 `NatTrans` への橋
  * M277F-4 `piEtGroupAt` / `piEtGroup` — **π₁^ét(Spec K) の骨組み = Aut(F)
    が群をなす**（Grp インスタンス、群公理完全証明）
  * M277F-5 `grGal_action` / `grGal_action_one` / `grGal_action_mul` /
    `grGalFinAction` — π₁ の各ファイバーへの**群作用**（GAction、作用則完全証明）
  * M277F-6 `grGalBasePoint` / `grGalFiberOne_unique` / `grGalSectionHom` /
    `grGalCanonPoint` / `grGal_split_trivial` / `grGalCanonPoint_inj` /
    `grGalFinAction_compat` — 基点（F(K¹) は一点）・K^n のファイバーの n 個の
    標準点（相異なる）・**自明被覆のモノドロミー自明性**
  * M277F-7 `grGalPointAlgebra` / `grGalPost` / `grGal_fromGaloisAut` /
    `grGal_fromGalois` — **Gal(L/K) から π₁ への群準同型**（後合成の自然変換）
  * M277F-8 `GrothendieckGaloisData` / `grothendieckGaloisData` /
    `piEt_exists` / `grothendieckGalois_exists` — capstone（F・π₁・作用・
    Gal→π₁ の束と存在定理）
  * M277F-9 `grGal_rat_fiber_eq` / `grGal_rat_action` /
    `grGal_rat_canonPoint_distinct` / `grGal_rat_data` — 実例: 本物の数体 ℚ
    （M272F `ratSplitCover`）上での π₁ の作用の確認

  **正直な限定**（何が本物で何が未達か・消去/弱化禁止）:
  1. **Aut(F) の定義域は分裂骨格（自明被覆 K^n, n ∈ ℕ）に限る**。自然性は
     分裂対象間の**すべての** K-代数準同型に対して要求しており、これは
     FÉt(K) の分裂充満部分圏上のファイバー関手の自己同型群そのものである。
     一般の有限エタール対象（非自明な分離拡大 L/K の直積）を含む FÉt(K)
     全体への拡張は分離性理論（多項式の微分判定・根の非重複）が要り後続
     （M272F 正直申告 2 と同一の境界）。なお宇宙の観点でも分裂骨格は
     Nat 添字で small であり `Grp.carrier : Type` に本物のまま載る。
  2. **分裂対象だけでは π₁ は（古典論理では）自明群に潰れる**:
     `grGal_split_trivial` は「自明被覆のモノドロミーは自明」という本物の
     定理だが、裏返せば非自明な π₁^ét = Gal(K^sep/K) は非分裂対象（実分離
     拡大）を圏に追加して初めて現れる。本モジュールの成果は**定義
     （イディオム）と群構造・作用・Gal→π₁ 構成の確立**であり、非自明性の
     獲得は後続。「別コースの toy 群」ではなく本コースの Aut(F) を主語に
     している。
  3. ファイバー = 切断集合 Hom_{K-alg}(K^n, Ω) は本物の Ω 値点集合。
     |F(K^n)| = n の「≥ n」側（n 個の相異なる標準点）は
     `grGalCanonPoint_inj` で完全証明したが、「≤ n」側（切断は標準点に
     尽きる）は体の冪等元の 0/1 二分に排中律を要し未形式化
     （M272F 正直申告 5 と同一）。
  4. `grGal_fromGalois` は本物の構成（後合成）による**準同型の構成まで**。
     同型性（充満忠実・全射 = Grothendieck ガロア対応の完全形）は分離正規
     拡大と非分裂対象の機構が要り後続。分裂対象上では像が（古典的には）
     自明になるのは 2 と同じ理由であり、忠実性の獲得も後続。
  5. π₁ の **pro-有限位相・逆極限（有限商系 Aut(F)|_{rank≤n}）としての
     位相群構造は未**。M265F ProfiniteTopology との接続は後続。
  6. `grGalFinAction`（Fin n 上の作用）が自明作用であることは恣意ではなく
     `grGal_split_trivial`（標準点固定）の帰結として `grGalFinAction_compat`
     で正当化した。
  7. M276F FiberFunctor.lean（並行切片）とは概念整合（ファイバー = 切断
     集合）だが、依存回避のため import しない（本ファイル内で自前定義）。
     統合時の接続は親が行う。

  選択公理不使用・sorry 不使用・新規 Classical.choice 不使用（全単射性は
  すべて明示逆写像 witness、場合分けは Decidable witness の構成的分解）。
  禁止タクティク不使用。
-/
import IUT.FiniteEtaleAlgebra
import IUT.FieldAutGroup

namespace IUT

/-! ## M277F-0: 構成的補助 — 環準同型の 0 保存 -/

/-- **M277F-0: 環準同型は 0 を保つ**（公理に置かず加法性から導出:
    f(0) = f(0+0) = f(0)+f(0) より加法簡約で f(0) = 0）。 -/
theorem grGalRingHom_map_zero {R S : CRing} (f : RingHom R S) :
    f.map R.zero = S.zero := by
  have h : f.map R.zero = S.add (f.map R.zero) (f.map R.zero) := by
    have step := f.map_add R.zero R.zero
    rw [R.zero_add] at step
    exact step
  have h2 : S.add (f.map R.zero) S.zero
      = S.add (f.map R.zero) (f.map R.zero) := by
    rw [← h, S.add_comm, S.zero_add]
  have h3 := S.add_left_cancel h2
  exact h3.symm

/-! ## M277F-1: ファイバー = 切断集合 Hom_{K-alg}(K^n, Ω) と引き戻し

幾何的点 Spec Ω → Spec K（Ω は K-代数）でとった分裂被覆 K^n のファイバーは
Ω 値点の集合 Hom_{K-alg}(K^n, Ω) である（Ω = K なら K 有理点 = M272F の
切断そのもの、Ω = L なら L 値点 = Galois 作用の受け皿）。 -/

/-- **M277F-1a: ファイバー** — 分裂被覆 K^n の幾何的点 Ω でのファイバー
    = K-代数準同型 K^n → Ω の集合（本物の Ω 値点集合）。 -/
abbrev grGalFiber (K : IUTField) (Ω : KAlgebra K) (n : Nat) : Type :=
  KAlgHom (splitEtaleAlgebra K n) Ω

/-- **M277F-1b: 引き戻し** — 被覆の射（K-代数準同型 f : K^m → K^n、
    被覆側では Spec K^n → Spec K^m）に沿ってファイバーの点を引き戻す
    （切断 s : K^n → Ω を s∘f : K^m → Ω へ）。ファイバー関手の射部分。 -/
def grGalPull {K : IUTField} {Ω : KAlgebra K} {n m : Nat}
    (f : KAlgHom (splitEtaleAlgebra K m) (splitEtaleAlgebra K n))
    (s : grGalFiber K Ω n) : grGalFiber K Ω m :=
  kAlgCompHom f s

/-- **M277F-1c: 恒等射の引き戻しは恒等**（関手性 1）。 -/
theorem grGalPull_id {K : IUTField} {Ω : KAlgebra K} {n : Nat}
    (s : grGalFiber K Ω n) :
    grGalPull (kAlgIdHom (splitEtaleAlgebra K n)) s = s :=
  kAlgHom_ext (fun _ => rfl)

/-- **M277F-1d: 合成射の引き戻しは引き戻しの合成**（関手性 2）。 -/
theorem grGalPull_comp {K : IUTField} {Ω : KAlgebra K} {n m k : Nat}
    (f : KAlgHom (splitEtaleAlgebra K m) (splitEtaleAlgebra K n))
    (g : KAlgHom (splitEtaleAlgebra K k) (splitEtaleAlgebra K m))
    (s : grGalFiber K Ω n) :
    grGalPull (kAlgCompHom g f) s = grGalPull g (grGalPull f s) :=
  kAlgHom_ext (fun _ => rfl)

/-! ## M277F-2: 本物のファイバー関手 F : (分裂骨格)^op → SetCat -/

/-- **M277F-2a: 分裂骨格の逆圏** — 対象 = 枚数 n ∈ ℕ（分裂被覆 K^n）、
    射 n → m = K-代数準同型 K^m → K^n（逆圏なので被覆側 Spec K^n → Spec K^m
    の向き）。FÉt(K) の分裂充満部分圏の骨格（M272F-9b の `fEtCat` の
    分裂対象を Nat で添字づけたもの）。 -/
def grGalSplitOp (K : IUTField) : Cat where
  Obj := Nat
  Hom := fun n m => KAlgHom (splitEtaleAlgebra K m) (splitEtaleAlgebra K n)
  id := fun n => kAlgIdHom (splitEtaleAlgebra K n)
  comp := fun f g => kAlgCompHom g f
  id_comp := fun _ => kAlgHom_ext (fun _ => rfl)
  comp_id := fun _ => kAlgHom_ext (fun _ => rfl)
  assoc := fun _ _ _ => kAlgHom_ext (fun _ => rfl)

/-- **M277F-2b: ファイバー関手 F_Ω**（本物の関手、M19 `Functor` として）—
    対象部分は切断集合、射部分は引き戻し。SGA1 のファイバー関手
    FÉt(K) → FinSet の分裂骨格上の実体。 -/
def grGalFiberFunctor (K : IUTField) (Ω : KAlgebra K) :
    Functor (grGalSplitOp K) SetCat where
  onObj := fun n => grGalFiber K Ω n
  onHom := fun f => fun s => grGalPull f s
  map_id := fun _ => funext (fun s => grGalPull_id s)
  map_comp := fun f g => funext (fun s => grGalPull_comp f g s)

/-! ## M277F-3: Aut(F) の元 — 各成分が全単射な自己自然変換 -/

/-- **M277F-3a: Aut(F) の元** — ファイバー関手 F_Ω の自己自然変換であって
    各成分が全単射なもの。自然性 `natural` は**分裂対象間のすべての
    K-代数準同型**に対する可換性、全単射性は**明示逆成分 `invApp` の
    両側逆 witness**（`left_inv`/`right_inv`）として保持し choice を回避する。 -/
structure grGalAut (K : IUTField) (Ω : KAlgebra K) where
  /-- 成分: 各ファイバー F(K^n) の自己写像。 -/
  app : (n : Nat) → grGalFiber K Ω n → grGalFiber K Ω n
  /-- 明示逆成分（全単射性の構成的 witness）。 -/
  invApp : (n : Nat) → grGalFiber K Ω n → grGalFiber K Ω n
  /-- 自然性: すべての被覆の射（K-代数準同型）と可換。 -/
  natural : ∀ {n m : Nat}
    (f : KAlgHom (splitEtaleAlgebra K m) (splitEtaleAlgebra K n))
    (s : grGalFiber K Ω n),
    app m (grGalPull f s) = grGalPull f (app n s)
  /-- 逆成分は左逆。 -/
  left_inv : ∀ (n : Nat) (s : grGalFiber K Ω n), invApp n (app n s) = s
  /-- 逆成分は右逆。 -/
  right_inv : ∀ (n : Nat) (s : grGalFiber K Ω n), app n (invApp n s) = s

namespace grGalAut

/-- **外延性** — 成分と逆成分が一致すれば Aut(F) の元は等しい
    （残る場は Prop で証明無関係）。 -/
theorem ext {K : IUTField} {Ω : KAlgebra K} {σ τ : grGalAut K Ω}
    (h1 : σ.app = τ.app) (h2 : σ.invApp = τ.invApp) : σ = τ := by
  cases σ with
  | mk sa si sn sl sr =>
    cases τ with
    | mk ta ti tn tl tr =>
      have ha : sa = ta := h1
      have hi : si = ti := h2
      cases ha
      cases hi
      rfl

/-- **M277F-3b: 逆成分の自然性**（本物の内容: 全単射な自然変換の逆は
    自然変換 — app の自然性と両側逆 witness から導出）。 -/
theorem inv_natural {K : IUTField} {Ω : KAlgebra K} (η : grGalAut K Ω)
    {n m : Nat} (f : KAlgHom (splitEtaleAlgebra K m) (splitEtaleAlgebra K n))
    (s : grGalFiber K Ω n) :
    η.invApp m (grGalPull f s) = grGalPull f (η.invApp n s) := by
  have key : η.app m (η.invApp m (grGalPull f s))
      = η.app m (grGalPull f (η.invApp n s)) := by
    rw [η.right_inv, η.natural f (η.invApp n s), η.right_inv]
  have h1 : η.invApp m (η.app m (η.invApp m (grGalPull f s)))
      = η.invApp m (η.app m (grGalPull f (η.invApp n s))) :=
    congrArg (η.invApp m) key
  rw [η.left_inv, η.left_inv] at h1
  exact h1

end grGalAut

/-- **恒等自然変換** id_F ∈ Aut(F)。 -/
def grGalAutId (K : IUTField) (Ω : KAlgebra K) : grGalAut K Ω where
  app := fun _ s => s
  invApp := fun _ s => s
  natural := fun _ _ => rfl
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

/-- **合成** σ∘τ（先に τ、次に σ; 成分ごとの合成）。逆成分は τ⁻¹∘σ⁻¹。 -/
def grGalAutComp {K : IUTField} {Ω : KAlgebra K}
    (σ τ : grGalAut K Ω) : grGalAut K Ω where
  app := fun n s => σ.app n (τ.app n s)
  invApp := fun n s => τ.invApp n (σ.invApp n s)
  natural := fun {n m} f s => by
    show σ.app m (τ.app m (grGalPull f s))
      = grGalPull f (σ.app n (τ.app n s))
    rw [τ.natural f s, σ.natural f (τ.app n s)]
  left_inv := fun n s => by
    show τ.invApp n (σ.invApp n (σ.app n (τ.app n s))) = s
    rw [σ.left_inv, τ.left_inv]
  right_inv := fun n s => by
    show σ.app n (τ.app n (τ.invApp n (σ.invApp n s))) = s
    rw [τ.right_inv, σ.right_inv]

/-- **逆** σ⁻¹（成分と逆成分の交換; 自然性は M277F-3b `inv_natural`）。 -/
def grGalAutInv {K : IUTField} {Ω : KAlgebra K}
    (σ : grGalAut K Ω) : grGalAut K Ω where
  app := σ.invApp
  invApp := σ.app
  natural := fun f s => σ.inv_natural f s
  left_inv := σ.right_inv
  right_inv := σ.left_inv

/-- **M277F-3c: M19 `NatTrans` への橋** — Aut(F) の元は本物のファイバー関手
    `grGalFiberFunctor` の自己自然変換である（逆成分も `grGalAutInv` 経由で
    同様; 全単射性 witness は `grGalAut` 自身が保持）。 -/
def grGalAutNatTrans {K : IUTField} {Ω : KAlgebra K} (η : grGalAut K Ω) :
    NatTrans (grGalFiberFunctor K Ω) (grGalFiberFunctor K Ω) where
  app := fun n => fun s => η.app n s
  natural := fun f => funext (fun s => η.natural f s)

/-! ## M277F-4: π₁^ét := Aut(F) が群をなす -/

/-- **M277F-4a: π₁^ét(Spec K) の骨組み（幾何的点 Ω つき）** — Aut(F_Ω) は
    合成を積、恒等を単位元、逆自然変換を逆元として **Grp のインスタンス**を
    なす。群公理は外延性で成分に落として完全証明。 -/
def piEtGroupAt (K : IUTField) (Ω : KAlgebra K) : Grp where
  carrier := grGalAut K Ω
  mul := grGalAutComp
  one := grGalAutId K Ω
  inv := grGalAutInv
  mul_assoc := fun _ _ _ => grGalAut.ext rfl rfl
  one_mul := fun _ => grGalAut.ext rfl rfl
  inv_mul := fun a => grGalAut.ext
    (funext fun n => funext fun s => a.left_inv n s)
    (funext fun n => funext fun s => a.left_inv n s)

/-- **M277F-4b: π₁^ét(Spec K) の骨組み** — 標準の幾何的点 Ω = K
    （自明被覆 = Spec K 自身の有理点）でとった Aut(F)。 -/
def piEtGroup (K : IUTField) : Grp :=
  piEtGroupAt K (trivialEtaleAlgebra K)

/-! ## M277F-5: π₁ のファイバーへの作用 -/

/-- **M277F-5a: π₁ の作用** — π₁^ét = Aut(F) は各分裂被覆 K^n のファイバー
    （切断集合）に成分適用で作用する（GAction、M14 の機構）。 -/
def grGal_action (K : IUTField) (Ω : KAlgebra K) (n : Nat) :
    GAction (piEtGroupAt K Ω) where
  carrier := grGalFiber K Ω n
  act := fun η s => η.app n s
  act_one := fun _ => rfl
  act_mul := fun _ _ _ => rfl

/-- **M277F-5b: 作用則 e·x = x**（明示形）。 -/
theorem grGal_action_one (K : IUTField) (Ω : KAlgebra K) (n : Nat)
    (s : grGalFiber K Ω n) :
    (grGal_action K Ω n).act (piEtGroupAt K Ω).one s = s := rfl

/-- **M277F-5c: 作用則 (gh)·x = g·(h·x)**（明示形）。 -/
theorem grGal_action_mul (K : IUTField) (Ω : KAlgebra K) (n : Nat)
    (g h : grGalAut K Ω) (s : grGalFiber K Ω n) :
    (grGal_action K Ω n).act ((piEtGroupAt K Ω).mul g h) s
      = (grGal_action K Ω n).act g ((grGal_action K Ω n).act h s) := rfl

/-- **M277F-5d: 添字集合 Fin n 上の誘導作用** — π₁ は K^n のファイバーの
    n 個の標準点の添字 Fin n にも作用する。この作用が**自明**（各点固定）で
    あることは恣意的な定義ではなく M277F-6e `grGal_split_trivial` の帰結
    （`grGalFinAction_compat` で正当化）。 -/
def grGalFinAction (K : IUTField) (Ω : KAlgebra K) (n : Nat) :
    GAction (piEtGroupAt K Ω) where
  carrier := Fin n
  act := fun _ i => i
  act_one := fun _ => rfl
  act_mul := fun _ _ _ => rfl

/-! ## M277F-6: 基点・標準点と自明被覆のモノドロミー自明性 -/

/-- **M277F-6a: 基点** — 1 枚被覆 K¹ のファイバーの点（構造射との合成
    x ↦ Ω(x₀)）。「Spec K の幾何的点はただ一つ」の実体（一意性は 6b）。 -/
def grGalBasePoint (K : IUTField) (Ω : KAlgebra K) :
    KAlgHom (splitEtaleAlgebra K 1) Ω where
  hom :=
    { map := fun x => Ω.structMap.map (x ⟨0, Nat.zero_lt_one⟩)
      map_add := fun x y =>
        Ω.structMap.map_add (x ⟨0, Nat.zero_lt_one⟩) (y ⟨0, Nat.zero_lt_one⟩)
      map_mul := fun x y =>
        Ω.structMap.map_mul (x ⟨0, Nat.zero_lt_one⟩) (y ⟨0, Nat.zero_lt_one⟩)
      map_one := Ω.structMap.map_one }
  compat := fun _ => rfl

/-- **M277F-6b: F(K¹) は一点** — 1 枚被覆のファイバーの点は基点のみ
    （K¹ の任意の元は構造射の像なので compat で決まる）。 -/
theorem grGalFiberOne_unique {K : IUTField} {Ω : KAlgebra K}
    (s t : grGalFiber K Ω 1) : s = t := by
  apply kAlgHom_ext
  intro x
  have hx : x = (splitEtaleAlgebra K 1).structMap.map
      (x ⟨0, Nat.zero_lt_one⟩) := by
    funext j
    have hj : j = (⟨0, Nat.zero_lt_one⟩ : Fin 1) :=
      kAlgFin_ext (by have h := j.isLt; omega)
    rw [hj]
    exact rfl
  rw [hx, s.compat, t.compat]

/-- Aut(F) の元は基点を固定する（F(K¹) が一点だから）。 -/
theorem grGalApp_base {K : IUTField} {Ω : KAlgebra K} (η : grGalAut K Ω) :
    η.app 1 (grGalBasePoint K Ω) = grGalBasePoint K Ω :=
  grGalFiberOne_unique _ _

/-- **M277F-6c: 第 i 成分への射影 K^n → K¹**（K-代数準同型; 被覆側では
    Spec K¹ → Spec K^n の第 i 点の包含）。 -/
def grGalSectionHom (K : IUTField) (n : Nat) (i : Fin n) :
    KAlgHom (splitEtaleAlgebra K n) (splitEtaleAlgebra K 1) where
  hom :=
    { map := fun x _ => x i
      map_add := fun _ _ => rfl
      map_mul := fun _ _ => rfl
      map_one := rfl }
  compat := fun _ => rfl

/-- **M277F-6d: 第 i 標準点** — K^n のファイバーの第 i 点（基点を第 i 包含で
    引き戻したもの; 具体的には x ↦ Ω(xᵢ)）。M272F の `splitSection` の
    Ω 値版であり、ファイバーの n 個の点の実体。 -/
def grGalCanonPoint (K : IUTField) (Ω : KAlgebra K) (n : Nat) (i : Fin n) :
    grGalFiber K Ω n :=
  grGalPull (grGalSectionHom K n i) (grGalBasePoint K Ω)

/-- **M277F-6e: 自明被覆のモノドロミー自明性**（Grothendieck ガロア対応の
    骨組み） — π₁^ét の任意の元は分裂被覆 K^n のファイバーの各標準点を
    固定する。証明は自然性を第 i 包含 K^n → K¹ に適用し F(K¹) の一点性
    （基点固定）に帰着させる本物の議論。「Spec K は連結で幾何的点は一つ、
    自明被覆に非自明モノドロミーは無い」の実体。 -/
theorem grGal_split_trivial {K : IUTField} {Ω : KAlgebra K}
    (η : grGalAut K Ω) (n : Nat) (i : Fin n) :
    η.app n (grGalCanonPoint K Ω n i) = grGalCanonPoint K Ω n i := by
  have h1 := η.natural (grGalSectionHom K n i) (grGalBasePoint K Ω)
  rw [grGalApp_base] at h1
  exact h1

/-- **M277F-6f: 標準点の分離** — Ω が非自明（1 ≠ 0）なら標準点は添字で
    分離される（冪等元 eᵢ での値 Ω(1) ≠ Ω(0) で分離; |F(K^n)| ≥ n の実体）。 -/
theorem grGalCanonPoint_inj {K : IUTField} {Ω : KAlgebra K}
    (hΩ : Ω.alg.one ≠ Ω.alg.zero) {n : Nat} {i j : Fin n}
    (h : grGalCanonPoint K Ω n i = grGalCanonPoint K Ω n j) : i = j := by
  cases kAlgDecEm (i = j) with
  | inl hij => exact hij
  | inr hij =>
    exfalso
    have he : (grGalCanonPoint K Ω n i).hom.map (splitIdem K n i)
        = (grGalCanonPoint K Ω n j).hom.map (splitIdem K n i) := by
      rw [h]
    have hL : (grGalCanonPoint K Ω n i).hom.map (splitIdem K n i)
        = Ω.alg.one := by
      show Ω.structMap.map (if i = i then K.one else K.zero) = Ω.alg.one
      rw [if_pos rfl]
      exact Ω.structMap.map_one
    have hR : (grGalCanonPoint K Ω n j).hom.map (splitIdem K n i)
        = Ω.alg.zero := by
      show Ω.structMap.map (if i = j then K.one else K.zero) = Ω.alg.zero
      rw [if_neg hij]
      exact grGalRingHom_map_zero Ω.structMap
    rw [hL, hR] at he
    exact hΩ he

/-- **標準点は相異なる**（M277F-6f の対偶形）。 -/
theorem grGalCanonPoint_distinct {K : IUTField} {Ω : KAlgebra K}
    (hΩ : Ω.alg.one ≠ Ω.alg.zero) {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    grGalCanonPoint K Ω n i ≠ grGalCanonPoint K Ω n j :=
  fun hc => hij (grGalCanonPoint_inj hΩ hc)

/-- **M277F-6g: Fin n 上の誘導作用の整合** — 標準点の埋め込み
    `grGalCanonPoint` は Fin n 上の作用（M277F-5d）とファイバー上の作用
    （M277F-5a）を交換する。自明作用の正当化（`grGal_split_trivial` の帰結）。 -/
theorem grGalFinAction_compat {K : IUTField} {Ω : KAlgebra K}
    (η : grGalAut K Ω) (n : Nat) (i : Fin n) :
    grGalCanonPoint K Ω n ((grGalFinAction K Ω n).act η i)
      = (grGal_action K Ω n).act η (grGalCanonPoint K Ω n i) :=
  (grGal_split_trivial η n i).symm

/-! ## M277F-7: Gal(L/K) から π₁ への準同型（後合成） -/

/-- **M277F-7a: 体拡大の幾何的点** — 拡大 K ⊆ L の上体 L を K-代数と見る
    （構造射 = 埋め込み ι）。Spec L → Spec K が幾何的点の役を果たす
    （本物の Grothendieck ガロア理論では L = K^sep がここに入る）。 -/
def grGalPointAlgebra (E : FieldExtension) : KAlgebra E.base where
  alg := E.top.toCRing
  structMap :=
    { map := E.incl
      map_add := E.incl_add
      map_mul := E.incl_mul
      map_one := E.incl_one }

/-- **M277F-7b: 後合成** — K を固定する L の自己同型 σ ∈ Gal(L/K) は
    L 値点 s : K^n → L に後合成 σ∘s で作用する。**compat（K-代数準同型で
    あること）の証明に Galois 固定条件 σ(ιc) = ιc を本質使用**（これが
    「Gal がファイバーに作用する」の数学的核心）。 -/
def grGalPost (E : FieldExtension) {n : Nat} (σ : FieldAut E.top)
    (hσ : (galoisSubgroup E).mem σ)
    (s : grGalFiber E.base (grGalPointAlgebra E) n) :
    KAlgHom (splitEtaleAlgebra E.base n) (grGalPointAlgebra E) where
  hom :=
    { map := fun x => σ.toFun (s.hom.map x)
      map_add := fun x y => by
        rw [s.hom.map_add]
        exact σ.map_add (s.hom.map x) (s.hom.map y)
      map_mul := fun x y => by
        rw [s.hom.map_mul]
        exact σ.map_mul (s.hom.map x) (s.hom.map y)
      map_one := by
        rw [s.hom.map_one]
        exact σ.map_one }
  compat := fun c => by
    show σ.toFun (s.hom.map ((splitEtaleAlgebra E.base n).structMap.map c))
      = (grGalPointAlgebra E).structMap.map c
    rw [s.compat c]
    exact hσ c

/-- **M277F-7c: Gal(L/K) の元から Aut(F) の元へ** — 後合成は自然変換
    （後合成と引き戻し = 前合成は可換）であり、逆成分は σ⁻¹ の後合成
    （Gal が部分群として逆で閉じること M271F-4 を使用）。 -/
def grGal_fromGaloisAut (E : FieldExtension)
    (σ : (galoisGroupGrp E).carrier) :
    grGalAut E.base (grGalPointAlgebra E) where
  app := fun _ s => grGalPost E σ.val σ.property s
  invApp := fun _ s =>
    grGalPost E (fieldAutInv σ.val) ((galoisSubgroup E).inv_mem σ.property) s
  natural := fun _ _ => kAlgHom_ext (fun _ => rfl)
  left_inv := fun _ s => kAlgHom_ext (fun x => σ.val.left_inv (s.hom.map x))
  right_inv := fun _ s => kAlgHom_ext (fun x => σ.val.right_inv (s.hom.map x))

/-- **M277F-7d: Gal(L/K) → π₁ は群準同型** — 後合成は合成を保つ
    （(στ)∘s = σ∘(τ∘s)）。Galois 群が π₁ = Aut(F) の中に実現される骨組み。 -/
def grGal_fromGalois (E : FieldExtension) :
    Hom (galoisGroupGrp E) (piEtGroupAt E.base (grGalPointAlgebra E)) where
  map := grGal_fromGaloisAut E
  map_mul := fun _ _ => grGalAut.ext
    (funext fun _ => funext fun _ => kAlgHom_ext (fun _ => rfl))
    (funext fun _ => funext fun _ => kAlgHom_ext (fun _ => rfl))

/-! ## M277F-8: capstone -/

/-- **M277F-8a: capstone データ** — 体拡大 E = (K ⊆ L) に対する
    Grothendieck ガロア理論の全部品: 幾何的点・π₁ = Aut(F)・π₁ の各
    ファイバーへの作用・Gal(L/K) → π₁ の準同型。 -/
structure GrothendieckGaloisData (E : FieldExtension) where
  /-- 幾何的点（基点となる K-代数）。 -/
  point : KAlgebra E.base
  /-- π₁^ét(Spec K) の骨組み。 -/
  piEt : Grp
  /-- π₁ は Aut(F)（ファイバー関手の自己同型群）である。 -/
  piEt_eq : piEt = piEtGroupAt E.base point
  /-- π₁ の各分裂被覆のファイバーへの作用。 -/
  fibAct : (n : Nat) → GAction (piEtGroupAt E.base point)
  /-- Gal(L/K) から π₁ への準同型。 -/
  fromGal : Hom (galoisGroupGrp E) (piEtGroupAt E.base point)

/-- **証人** — 幾何的点 Spec L・Aut(F)・成分適用の作用・後合成準同型が
    全条件を満たす。 -/
def grothendieckGaloisData (E : FieldExtension) : GrothendieckGaloisData E where
  point := grGalPointAlgebra E
  piEt := piEtGroupAt E.base (grGalPointAlgebra E)
  piEt_eq := rfl
  fibAct := fun n => grGal_action E.base (grGalPointAlgebra E) n
  fromGal := grGal_fromGalois E

/-- **M277F-8b: capstone — π₁^ét 群の存在**（任意の体 K 上で Aut(F) は
    群として空でない: 恒等自然変換が元）。 -/
theorem piEt_exists (K : IUTField) : Nonempty ((piEtGroup K).carrier) :=
  ⟨grGalAutId K (trivialEtaleAlgebra K)⟩

/-- **M277F-8c: capstone — Grothendieck ガロア対応の骨組みの存在**
    （任意の体拡大 L/K で Gal(L/K) が π₁ = Aut(F) に準同型で実現される）。 -/
theorem grothendieckGalois_exists (E : FieldExtension) :
    Nonempty (GrothendieckGaloisData E) :=
  ⟨grothendieckGaloisData E⟩

/-! ## M277F-9: 実例 — 本物の数体 ℚ 上の π₁ の作用 -/

/-- **M277F-9a: ファイバーの同定** — π₁^ét(Spec ℚ) の作用するファイバーは
    M272F の実例 `ratSplitCover n`（Spec ℚ の n 枚分裂被覆）の切断集合
    そのもの（定義的に一致）。 -/
theorem grGal_rat_fiber_eq (n : Nat) :
    grGalFiber ratIUTField (trivialEtaleAlgebra ratIUTField) n
      = KAlgHom (ratSplitCover n).obj (trivialEtaleAlgebra ratIUTField) := rfl

/-- **M277F-9b: 実例 — π₁^ét(Spec ℚ) の作用の確認** — π₁^ét(Spec ℚ) の
    任意の元は `ratSplitCover n` のファイバーの各標準点を固定する
    （自明被覆のモノドロミー自明性の ℚ 上の実現）。 -/
theorem grGal_rat_action
    (η : grGalAut ratIUTField (trivialEtaleAlgebra ratIUTField))
    (n : Nat) (i : Fin n) :
    η.app n (grGalCanonPoint ratIUTField (trivialEtaleAlgebra ratIUTField) n i)
      = grGalCanonPoint ratIUTField (trivialEtaleAlgebra ratIUTField) n i :=
  grGal_split_trivial η n i

/-- **M277F-9c: 実例 — ℚ 上の標準点は相異なる**（|F(ℚ^n)| ≥ n; ℚ の
    非自明性 1 ≠ 0 を使用）。 -/
theorem grGal_rat_canonPoint_distinct {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    grGalCanonPoint ratIUTField (trivialEtaleAlgebra ratIUTField) n i
      ≠ grGalCanonPoint ratIUTField (trivialEtaleAlgebra ratIUTField) n j :=
  grGalCanonPoint_distinct ratIUTField.one_ne_zero hij

/-- **M277F-9d: 実例 — ℚ の自明拡大での capstone データ**（本物の数体上で
    Grothendieck ガロア理論の全部品が組み上がる）。 -/
def grGal_rat_data : GrothendieckGaloisData (trivialExtension ratIUTField) :=
  grothendieckGaloisData (trivialExtension ratIUTField)

end IUT
