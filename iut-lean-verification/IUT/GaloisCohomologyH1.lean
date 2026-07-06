/-
  IUT/GaloisCohomologyH1.lean — M326F: 群コホモロジー H¹(G_K, M) の完全構造
  ── 柱B 局所類体論の横展開（Kummer 理論・相互律の土台）

  分類 **[実]**（本物の先行建設 (b)）。toy 模型を主語にしない。

  **complete_pct 影響: 柱B 局所類体論の本物の先行建設
  （群コホモロジー H¹(G_K, M) の完全な群構造）**。IUT の Kummer 理論・
  cyclotomic rigidity・相互律の代数的土台である **1-コホモロジー
  H¹(G_K, M) = Z¹/B¹** を core Lean のみで本物構成する。M320F Kummer /
  M322F cyclotomic rigidity の μ_n 作用（G_K-加群）を受けて、
  crossed homomorphism（1-コサイクル）のなす群 Z¹、主コサイクル
  （1-コバウンダリ）のなす部分群 B¹、その商 H¹ = Z¹/B¹（M267F の
  商群機構）が**アーベル群**であること、そして**自明作用のとき
  H¹(G_K, M) = Hom(G_K, M)**（連続準同型群）であることを完全証明する。

  ── 本物で閉じる中身（骨格のみでない）:
  * M326F-1 `galH1Module` — G_K-加群 M（アーベル群＋各 g が群自己準同型
    として作用、σ_1=id・σ_{gh}=σ_g∘σ_h）。M322F `CycGKAction` と同型の
    構造（μ_n が実例）。
  * M326F-2 `galH1Cocycle` — 1-コサイクル f: G_K→M、f(gh)=f(g)+g·f(h)。
    `galH1_cocycles_group` — Z¹ が**アーベル群**（和・0・反元で閉じ、
    群公理を完全証明）。
  * M326F-3 `galH1Coboundary` / `galH1CoboundaryHom` — 主コサイクル
    f_m(g)=g·m−m と、それが与える群準同型 M → Z¹。
    `galH1_coboundaries_subgroup` = im(この準同型) は Z¹ の**部分群**
    （M267F `imSubgroup`）、`galH1_coboundaries_normal`（アーベルゆえ正規）。
  * M326F-4 `galH1Group` = **H¹ = Z¹/B¹**（M267F `quotientGroupN`）、
    `galH1_isGroup`（H¹ が**アーベル群**）。
  * M326F-5 `galH1TrivialModule` と `galH1_trivial_action` — **自明作用で
    Z¹ = Hom(G_K,M)（全単射対応）・B¹ = 0・射影 Z¹→H¹ が単射** を本物で
    ⟹ H¹(G_K,M) = Hom(G_K,M)。
  * M326F-6 `galH1KummerHom` / `galH1_kummer_link` — 任意の Kummer
    コサイクル割当 κ: K^× → Z¹ に対し合成 K^× → H¹ が M267F 第一同型定理
    で K^×/ker ↪ H¹ を与える骨組み。
  * M326F-7 capstone `GaloisH1Data` / `galH1_exists` /
    `galH1_cocycles_isGroup` / `galH1_quotient_isGroup`。
  * M326F-8 実例 `galH1_zmod_trivial`（自明作用 M=ℤ/n で H¹=Hom(G_K,ℤ/n)）。

  **正直な限定**（消去・弱化禁止）:
  1. G_K の作用は G_K-加群構造 `galH1Module` として**受け取る**（M322F の
     μ_n 作用を使う）。体拡大からの実 G_K 作用の構成そのものは範囲外。
  2. H¹ = Z¹/B¹ は本物（コサイクル群・コバウンダリ部分群・商群すべて
     完全証明）。**高次 Hⁿ・長完全列・カップ積は後続**。
  3. 局所双対 H¹(G_K,μ_n) ≅ K^×/(K^×)ⁿ（Kummer 双対性の完全同型）は
     `galH1_kummer_link` の**骨組みまで**（κ からの単射 K^×/ker ↪ H¹）。
     ker = (K^×)ⁿ の同定は M320F Kummer 理論（μ_n 根の抽出）に依存し、
     本モジュールでは**自明作用での Hom 一致**を本物で閉じる。
  4. 連続性（位相）は core に位相機構が無いため代数的 Hom として扱う。

  **選択公理不使用・sorry 皆無**: 全宣言の公理は [propext, Quot.sound]
  （と Nonempty 用の型付け）のみを想定。禁止タクティク不使用。
  一般名は `galH1` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.QuotientGroup
import IUT.CyclotomicRigidity

namespace IUT

/-! ## M326F-0: アーベル群の補助等式（本物の群論） -/

/-- **中間入替則**（アーベル群）: (a·b)·(c·d) = (a·c)·(b·d)。
    コサイクルの和が再びコサイクルであることの核。 -/
theorem galH1_mul4_swap (M : Grp) (comm : ∀ a b, M.mul a b = M.mul b a)
    (a b c d : M.carrier) :
    M.mul (M.mul a b) (M.mul c d) = M.mul (M.mul a c) (M.mul b d) := by
  rw [M.mul_assoc a b (M.mul c d), ← M.mul_assoc b c d, comm b c,
    M.mul_assoc c b d, ← M.mul_assoc a c (M.mul b d)]

/-- **反元の分配則**（アーベル群）: (a·b)⁻¹ = a⁻¹·b⁻¹。
    コサイクルの反元が再びコサイクルであることの核。 -/
theorem galH1_inv_mul (M : Grp) (comm : ∀ a b, M.mul a b = M.mul b a)
    (a b : M.carrier) :
    M.inv (M.mul a b) = M.mul (M.inv a) (M.inv b) := by
  rw [comm (M.inv a) (M.inv b)]
  have hproof : M.mul (M.mul a b) (M.mul (M.inv b) (M.inv a)) = M.one := by
    rw [M.mul_assoc a b (M.mul (M.inv b) (M.inv a)), ← M.mul_assoc b (M.inv b) (M.inv a),
      M.mul_inv, M.one_mul, M.mul_inv]
  exact (M.inv_eq_of_mul_eq_one hproof).symm

/-- **主コサイクル整合則**（アーベル群）: (p·im)·(q·p⁻¹) = q·im。
    f_m(gh) = f_m(g)+g·f_m(h) の代数的核（p=g·m, q=g·(h·m), im=m⁻¹）。 -/
theorem galH1_cobound_id (M : Grp) (comm : ∀ a b, M.mul a b = M.mul b a)
    (p q im : M.carrier) :
    M.mul (M.mul p im) (M.mul q (M.inv p)) = M.mul q im := by
  rw [galH1_mul4_swap M comm p im q (M.inv p), comm p q,
    M.mul_assoc q p (M.mul im (M.inv p)), comm im (M.inv p),
    ← M.mul_assoc p (M.inv p) im, M.mul_inv, M.one_mul]

/-- **アーベル群の部分群は正規**（gng⁻¹ = n）。 -/
theorem galH1_abelian_subgroup_normal (G : Grp)
    (comm : ∀ a b, G.mul a b = G.mul b a) (N : Subgroup G) :
    IsNormalSubgroup G N := by
  intro g n hn
  have h : G.mul (G.mul g n) (G.inv g) = n := by
    rw [G.mul_assoc, comm n (G.inv g), ← G.mul_assoc, G.mul_inv, G.one_mul]
  rw [h]
  exact hn

/-! ## M326F-1: G_K-加群 -/

/-- **G_K-加群**（M326F-1）: アーベル群 M と、各 g ∈ G_K の群自己準同型
    としての作用 σ_g : Hom M M（σ_g(m+m')=σ_g m + σ_g m' を Hom が保証）。
    σ_1 = id・σ_{gh}=σ_g∘σ_h。μ_n（M322F `CycGKAction`）が実例。 -/
structure galH1Module (GK : Grp) where
  /-- 係数加群 M（アーベル群）。 -/
  M : Grp
  /-- M はアーベル。 -/
  comm : ∀ a b, M.mul a b = M.mul b a
  /-- 各 g への群自己準同型 σ_g。 -/
  act : GK.carrier → Hom M M
  /-- σ_1 = id。 -/
  act_one : ∀ m, (act GK.one).map m = m
  /-- σ_{gh} = σ_g∘σ_h。 -/
  act_mul : ∀ g h m, (act (GK.mul g h)).map m = (act g).map ((act h).map m)

/-! ## M326F-2: 1-コサイクル（crossed homomorphism）と Z¹ -/

/-- **1-コサイクル**（M326F-2a）: f: G_K→M で f(gh) = f(g) + g·f(h)
    （crossed homomorphism / 1-cocycle 条件）。 -/
structure galH1Cocycle {GK : Grp} (A : galH1Module GK) where
  /-- 台写像 f: G_K→M。 -/
  f : GK.carrier → A.M.carrier
  /-- 1-コサイクル条件 f(gh)=f(g)+g·f(h)。 -/
  cocycle : ∀ g h, f (GK.mul g h) = A.M.mul (f g) ((A.act g).map (f h))

/-- **外延性**（M326F-2b）: 台写像が一致すればコサイクルとして等しい
    （cocycle 条件は Prop、証明無関係）。 -/
theorem galH1Cocycle.ext {GK : Grp} {A : galH1Module GK}
    {f f' : galH1Cocycle A} (h : f.f = f'.f) : f = f' := by
  cases f with
  | mk f1 p1 =>
    cases f' with
    | mk f2 p2 =>
      cases h
      rfl

/-- **1-コサイクル全体 Z¹ の群構造**（M326F-2c）: 和 (f+f')(g)=f(g)+f'(g)、
    0-コサイクル、反元 (−f)(g)=−f(g) で閉じる**アーベル群**。各閉性の証明が
    1-コサイクル条件を本質的に使う（M326F-0 の補助等式）。 -/
def galH1_cocycles_group {GK : Grp} (A : galH1Module GK) : Grp where
  carrier := galH1Cocycle A
  mul := fun f f' =>
    { f := fun g => A.M.mul (f.f g) (f'.f g)
      cocycle := by
        intro g h
        rw [f.cocycle g h, f'.cocycle g h, (A.act g).map_mul]
        exact galH1_mul4_swap A.M A.comm (f.f g) ((A.act g).map (f.f h))
          (f'.f g) ((A.act g).map (f'.f h)) }
  one :=
    { f := fun _ => A.M.one
      cocycle := by
        intro g _
        rw [(A.act g).map_one, A.M.one_mul] }
  inv := fun f =>
    { f := fun g => A.M.inv (f.f g)
      cocycle := by
        intro g h
        rw [f.cocycle g h, (A.act g).map_inv]
        exact galH1_inv_mul A.M A.comm (f.f g) ((A.act g).map (f.f h)) }
  mul_assoc := by
    intro f f' f''
    apply galH1Cocycle.ext
    funext g
    exact A.M.mul_assoc (f.f g) (f'.f g) (f''.f g)
  one_mul := by
    intro f
    apply galH1Cocycle.ext
    funext g
    exact A.M.one_mul (f.f g)
  inv_mul := by
    intro f
    apply galH1Cocycle.ext
    funext g
    exact A.M.inv_mul (f.f g)

/-- **Z¹ はアーベル群**（M326F-2d）。 -/
theorem galH1_cocycles_comm {GK : Grp} (A : galH1Module GK) :
    ∀ p q, (galH1_cocycles_group A).mul p q = (galH1_cocycles_group A).mul q p := by
  intro p q
  apply galH1Cocycle.ext
  funext g
  exact A.comm (p.f g) (q.f g)

/-! ## M326F-3: 1-コバウンダリと B¹ -/

/-- **主コサイクル（1-コバウンダリ）**（M326F-3a）: m∈M から f_m(g)=g·m−m。
    1-コサイクル条件は M326F-0 `galH1_cobound_id` で本物に閉じる。 -/
def galH1Coboundary {GK : Grp} (A : galH1Module GK) (m : A.M.carrier) :
    galH1Cocycle A where
  f := fun g => A.M.mul ((A.act g).map m) (A.M.inv m)
  cocycle := by
    intro g h
    rw [A.act_mul g h m, (A.act g).map_mul, (A.act g).map_inv]
    exact (galH1_cobound_id A.M A.comm ((A.act g).map m)
      ((A.act g).map ((A.act h).map m)) (A.M.inv m)).symm

/-- **コバウンダリ準同型 M → Z¹**（M326F-3b）: m ↦ f_m は群準同型
    （f_{m+m'} = f_m + f_{m'}、M326F-0 の入替則）。B¹ = im(この準同型)。 -/
def galH1CoboundaryHom {GK : Grp} (A : galH1Module GK) :
    Hom A.M (galH1_cocycles_group A) where
  map := galH1Coboundary A
  map_mul := by
    intro m m'
    apply galH1Cocycle.ext
    funext g
    show A.M.mul ((A.act g).map (A.M.mul m m')) (A.M.inv (A.M.mul m m'))
       = A.M.mul (A.M.mul ((A.act g).map m) (A.M.inv m))
                 (A.M.mul ((A.act g).map m') (A.M.inv m'))
    rw [(A.act g).map_mul, galH1_inv_mul A.M A.comm m m']
    exact (galH1_mul4_swap A.M A.comm ((A.act g).map m) (A.M.inv m)
      ((A.act g).map m') (A.M.inv m')).symm

/-- **1-コバウンダリ全体 B¹**（M326F-3c）: コバウンダリ準同型の像
    （M267F `imSubgroup`）= Z¹ の部分群。 -/
def galH1_coboundaries_subgroup {GK : Grp} (A : galH1Module GK) :
    Subgroup (galH1_cocycles_group A) :=
  imSubgroup (galH1CoboundaryHom A)

/-- **B¹ は正規部分群**（M326F-3d）: Z¹ はアーベルゆえ。 -/
theorem galH1_coboundaries_normal {GK : Grp} (A : galH1Module GK) :
    IsNormalSubgroup (galH1_cocycles_group A) (galH1_coboundaries_subgroup A) :=
  galH1_abelian_subgroup_normal (galH1_cocycles_group A)
    (galH1_cocycles_comm A) (galH1_coboundaries_subgroup A)

/-! ## M326F-4: H¹ = Z¹/B¹ -/

/-- **1-コホモロジー H¹(G_K, M) = Z¹/B¹**（M326F-4a）: M267F 商群機構で
    正規部分群 B¹ による Z¹ の商。 -/
def galH1Group {GK : Grp} (A : galH1Module GK) : Grp :=
  quotientGroupN (galH1_cocycles_group A) (galH1_coboundaries_subgroup A)
    (galH1_coboundaries_normal A)

/-- **H¹ はアーベル群**（M326F-4b）。 -/
theorem galH1_isGroup {GK : Grp} (A : galH1Module GK) :
    ∀ x y, (galH1Group A).mul x y = (galH1Group A).mul y x := by
  intro x y
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  show Quot.mk _ ((galH1_cocycles_group A).mul a b)
     = Quot.mk _ ((galH1_cocycles_group A).mul b a)
  rw [galH1_cocycles_comm A a b]

/-! ## M326F-5: 自明作用 ⟹ H¹(G_K,M) = Hom(G_K,M) -/

/-- **準同型の外延性**（M326F-5a）: 台写像一致 ⟹ 準同型として等しい。 -/
theorem galH1_hom_ext {G H : Grp} {φ φ' : Hom G H} (h : φ.map = φ'.map) : φ = φ' := by
  cases φ with
  | mk m1 q1 =>
    cases φ' with
    | mk m2 q2 =>
      cases h
      rfl

/-- **自明 G_K-加群**（M326F-5b）: アーベル群 M に G_K が自明に作用
    （σ_g = id）。 -/
def galH1TrivialModule (GK : Grp) (M : Grp)
    (comm : ∀ a b, M.mul a b = M.mul b a) : galH1Module GK where
  M := M
  comm := comm
  act := fun _ => { map := fun z => z, map_mul := fun _ _ => rfl }
  act_one := fun _ => rfl
  act_mul := fun _ _ _ => rfl

/-- **準同型 → コサイクル**（M326F-5c）: 自明作用では群準同型 φ:G_K→M が
    そのまま 1-コサイクル（f(gh)=f(g)+f(h)）。 -/
def galH1_cocycle_of_hom {GK : Grp} (M : Grp)
    (comm : ∀ a b, M.mul a b = M.mul b a) (φ : Hom GK M) :
    galH1Cocycle (galH1TrivialModule GK M comm) where
  f := φ.map
  cocycle := fun g h => φ.map_mul g h

/-- **コサイクル → 準同型**（M326F-5d）: 自明作用では 1-コサイクルは群準同型。 -/
def galH1_hom_of_cocycle {GK : Grp} (M : Grp)
    (comm : ∀ a b, M.mul a b = M.mul b a)
    (f : galH1Cocycle (galH1TrivialModule GK M comm)) : Hom GK M where
  map := f.f
  map_mul := fun g h => f.cocycle g h

/-- **往復 1**（M326F-5e）: hom→cocycle→hom は恒等。 -/
theorem galH1_hom_cocycle_hom {GK : Grp} (M : Grp)
    (comm : ∀ a b, M.mul a b = M.mul b a) (φ : Hom GK M) :
    galH1_hom_of_cocycle M comm (galH1_cocycle_of_hom M comm φ) = φ :=
  galH1_hom_ext rfl

/-- **往復 2**（M326F-5f）: cocycle→hom→cocycle は恒等。Z¹ ≅ Hom(G_K,M)。 -/
theorem galH1_cocycle_hom_cocycle {GK : Grp} (M : Grp)
    (comm : ∀ a b, M.mul a b = M.mul b a)
    (f : galH1Cocycle (galH1TrivialModule GK M comm)) :
    galH1_cocycle_of_hom M comm (galH1_hom_of_cocycle M comm f) = f :=
  galH1Cocycle.ext rfl

/-- **自明作用のコバウンダリは 0**（M326F-5g）: f_m(g) = g·m−m = m−m = 0。 -/
theorem galH1_trivial_coboundary_eq_one {GK : Grp} (M : Grp)
    (comm : ∀ a b, M.mul a b = M.mul b a) (m : M.carrier) (g : GK.carrier) :
    (galH1Coboundary (galH1TrivialModule GK M comm) m).f g = M.one := by
  show M.mul m (M.inv m) = M.one
  exact M.mul_inv m

/-- **自明作用の B¹ は自明**（M326F-5h）: B¹ の任意元は Z¹ の単位元。 -/
theorem galH1_trivial_coboundaries_trivial {GK : Grp} (M : Grp)
    (comm : ∀ a b, M.mul a b = M.mul b a) :
    ∀ x, (galH1_coboundaries_subgroup (galH1TrivialModule GK M comm)).mem x
       → x = (galH1_cocycles_group (galH1TrivialModule GK M comm)).one := by
  intro x hx
  obtain ⟨m, hm⟩ := hx
  apply galH1Cocycle.ext
  funext g
  show x.f g = M.one
  rw [← hm]
  exact galH1_trivial_coboundary_eq_one M comm m g

/-- **自明部分群による商の射影は単射**（M326F-5i）: N が自明（全元が単位元）
    なら G→G/N は単射。B¹=0 ゆえ Z¹→H¹ が単射（H¹ ≅ Z¹）。 -/
theorem galH1_proj_injective_of_trivial (G : Grp) (N : Subgroup G)
    (hN : IsNormalSubgroup G N) (htriv : ∀ x, N.mem x → x = G.one) :
    Hom.Injective (quotientProjN G N hN) := by
  intro a b hab
  have hrel := quot_exact G (normalCong G N hN) hab
  have h0 := htriv _ hrel
  have key := congrArg (G.mul a) h0
  rw [← G.mul_assoc, G.mul_inv, G.one_mul, G.mul_one] at key
  exact key.symm

/-- **自明作用の capstone データ**（M326F-5j）: Z¹ ≅ Hom(G_K,M)（全単射
    対応）・B¹=0・射影 Z¹→H¹ が単射 ⟹ H¹(G_K,M) = Hom(G_K,M)。 -/
structure GaloisH1TrivialData (GK : Grp) (M : Grp)
    (comm : ∀ a b, M.mul a b = M.mul b a) where
  /-- Hom → コサイクル。 -/
  toCocycle : Hom GK M → galH1Cocycle (galH1TrivialModule GK M comm)
  /-- コサイクル → Hom。 -/
  toHom : galH1Cocycle (galH1TrivialModule GK M comm) → Hom GK M
  /-- 往復 hom→cocycle→hom = id。 -/
  left_inv : ∀ φ, toHom (toCocycle φ) = φ
  /-- 往復 cocycle→hom→cocycle = id（Z¹ ≅ Hom）。 -/
  right_inv : ∀ f, toCocycle (toHom f) = f
  /-- B¹ は自明。 -/
  coboundaries_trivial : ∀ x,
    (galH1_coboundaries_subgroup (galH1TrivialModule GK M comm)).mem x →
    x = (galH1_cocycles_group (galH1TrivialModule GK M comm)).one
  /-- 射影 Z¹→H¹ は単射（H¹ ≅ Z¹ ≅ Hom）。 -/
  proj_injective : Hom.Injective
    (quotientProjN (galH1_cocycles_group (galH1TrivialModule GK M comm))
      (galH1_coboundaries_subgroup (galH1TrivialModule GK M comm))
      (galH1_coboundaries_normal (galH1TrivialModule GK M comm)))
  /-- 射影 Z¹→H¹ は全射。 -/
  proj_surjective : ∀ x, ∃ a,
    (quotientProjN (galH1_cocycles_group (galH1TrivialModule GK M comm))
      (galH1_coboundaries_subgroup (galH1TrivialModule GK M comm))
      (galH1_coboundaries_normal (galH1TrivialModule GK M comm))).map a = x

/-- **証人**（M326F-5k）。 -/
def galH1TrivialData (GK : Grp) (M : Grp)
    (comm : ∀ a b, M.mul a b = M.mul b a) :
    GaloisH1TrivialData GK M comm where
  toCocycle := galH1_cocycle_of_hom M comm
  toHom := galH1_hom_of_cocycle M comm
  left_inv := galH1_hom_cocycle_hom M comm
  right_inv := galH1_cocycle_hom_cocycle M comm
  coboundaries_trivial := galH1_trivial_coboundaries_trivial M comm
  proj_injective := galH1_proj_injective_of_trivial
    (galH1_cocycles_group (galH1TrivialModule GK M comm))
    (galH1_coboundaries_subgroup (galH1TrivialModule GK M comm))
    (galH1_coboundaries_normal (galH1TrivialModule GK M comm))
    (galH1_trivial_coboundaries_trivial M comm)
  proj_surjective := quotientProjN_surjective
    (galH1_cocycles_group (galH1TrivialModule GK M comm))
    (galH1_coboundaries_subgroup (galH1TrivialModule GK M comm))
    (galH1_coboundaries_normal (galH1TrivialModule GK M comm))

/-- **自明作用で H¹(G_K,M) = Hom(G_K,M)**（M326F-5l, capstone）。 -/
theorem galH1_trivial_action (GK : Grp) (M : Grp)
    (comm : ∀ a b, M.mul a b = M.mul b a) :
    Nonempty (GaloisH1TrivialData GK M comm) :=
  ⟨galH1TrivialData GK M comm⟩

/-! ## M326F-6: Kummer 理論との接続（骨組み） -/

/-- **Kummer 準同型 K^× → H¹**（M326F-6a）: 任意の Kummer コサイクル割当
    κ: K^× → Z¹ に対し、射影 Z¹→H¹ との合成。 -/
def galH1KummerHom {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A)) : Hom K1 (galH1Group A) :=
  Hom.comp (quotientProjN (galH1_cocycles_group A)
    (galH1_coboundaries_subgroup A) (galH1_coboundaries_normal A)) κ

/-- **Kummer 接続（骨組み）**（M326F-6b）: M267F 第一同型定理により
    K^×/ker(Kummer 写像) ↪ H¹(G_K,M) を与える（K^×/(K^×)ⁿ ↪ H¹ の骨組み）。
    **限定**: ker = (K^×)ⁿ の同定は M320F Kummer 理論に依存。 -/
theorem galH1_kummer_link {GK : Grp} (A : galH1Module GK) {K1 : Grp}
    (κ : Hom K1 (galH1_cocycles_group A)) :
    Nonempty (QuotientGroupData (galH1KummerHom A κ)) :=
  firstIsomorphism_exists (galH1KummerHom A κ)

/-! ## M326F-7: capstone -/

/-- **capstone データ**（M326F-7a）: G_K-加群 A に対する H¹ の全部品
    — 係数加群・Z¹・B¹（正規部分群）・H¹=Z¹/B¹。 -/
structure GaloisH1Data (GK : Grp) where
  /-- 係数 G_K-加群。 -/
  A : galH1Module GK
  /-- 1-コサイクル群 Z¹。 -/
  Z1 : Grp
  /-- 1-コバウンダリ部分群 B¹。 -/
  B1 : Subgroup Z1
  /-- B¹ は正規。 -/
  B1_normal : IsNormalSubgroup Z1 B1
  /-- H¹ = Z¹/B¹。 -/
  H1 : Grp
  /-- Z¹ の同定。 -/
  Z1_isCocycles : Z1 = galH1_cocycles_group A
  /-- H¹ の同定。 -/
  H1_isQuotient : H1 = galH1Group A

/-- **証人**（M326F-7b）。 -/
def galH1Data (GK : Grp) (A : galH1Module GK) : GaloisH1Data GK where
  A := A
  Z1 := galH1_cocycles_group A
  B1 := galH1_coboundaries_subgroup A
  B1_normal := galH1_coboundaries_normal A
  H1 := galH1Group A
  Z1_isCocycles := rfl
  H1_isQuotient := rfl

/-- **H¹ 構造の存在**（M326F-7c）。 -/
theorem galH1_exists (GK : Grp) (A : galH1Module GK) :
    Nonempty (GaloisH1Data GK) :=
  ⟨galH1Data GK A⟩

/-- **Z¹ は（アーベル）群**（M326F-7d）。 -/
theorem galH1_cocycles_isGroup {GK : Grp} (A : galH1Module GK) :
    ∀ p q, (galH1_cocycles_group A).mul p q = (galH1_cocycles_group A).mul q p :=
  galH1_cocycles_comm A

/-- **H¹ = Z¹/B¹ は（アーベル）群**（M326F-7e）。 -/
theorem galH1_quotient_isGroup {GK : Grp} (A : galH1Module GK) :
    ∀ x y, (galH1Group A).mul x y = (galH1Group A).mul y x :=
  galH1_isGroup A

/-! ## M326F-8: 実例（自明作用 M = ℤ/n） -/

/-- **実例**（M326F-8a）: 自明作用 M=ℤ/n（M13 商群 `zmod n`、可換）に対し
    H¹(G_K, ℤ/n) = Hom(G_K, ℤ/n)。 -/
def galH1_zmod_trivial (GK : Grp) (n : Nat) :
    GaloisH1TrivialData GK (zmod n) (cycStd_add_comm n) :=
  galH1TrivialData GK (zmod n) (cycStd_add_comm n)

/-- **実例存在**（M326F-8b）: H¹(G_K, ℤ/n) = Hom(G_K, ℤ/n) の証人が存在。 -/
theorem galH1_zmod_H1_eq_Hom (GK : Grp) (n : Nat) :
    Nonempty (GaloisH1TrivialData GK (zmod n) (cycStd_add_comm n)) :=
  ⟨galH1_zmod_trivial GK n⟩

end IUT
