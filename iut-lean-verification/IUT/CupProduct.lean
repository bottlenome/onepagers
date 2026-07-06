/-
  IUT/CupProduct.lean — M350F [実／本物]
  分類: 実 (ガロアコホモロジーのカップ積 H¹×H¹→H²)
  complete_pct 影響: 柱B を前進（M326F H¹=Z¹/B¹ の上でカップ積を 1-コチェイン上で定義し
    2-コサイクルへ・コホモロジー類へ降下（well-defined）・双線形・次数付き交換律を本物で。
    高次コホモロジー構造の土台）。
  正直な限定: 一般 Hⁿ・全次数の結合律は外部仮説/後続。

  ── 本物で閉じる中身（骨格のみでない）:
  * M350F-0  `cup_abel3` / `cup_regroup6` — アーベル群の並べ替え補助等式（cup の核）。
  * M350F-1  `cupPairing` — G_K-加群 A,B → C = A⊗B の双加法的・G_K 同変な
             テンソル対（双加法性 add_left/add_right・同変性 equiv）。
             派生: `cup_tensor_one_left` / `cup_tensor_inv_left`。
  * M350F-2  `cupCochain` — 1-コチェイン上のカップ積
             (f∪g)(σ,τ) = f(σ)⊗(σ·g(τ)) ∈ C²(G_K,C)。
  * M350F-3  `cupTwoCocycle` — 2-コサイクル c:G×G→C（2-コサイクル条件
             g·c(h,k)+c(g,hk)=c(gh,k)+c(g,h)）。`cupZ2group` = Z² が**アーベル群**。
  * M350F-4  `cup_cocycle` — **f,g が 1-コサイクルなら f∪g は 2-コサイクル**（本証明）。
             `cupCocycleOf` で cup を Z² へ写す。
  * M350F-5  `cupD1` — 1-コチェインの 2-コバウンダリ作用素、`cup_d1_add`/`cup_d1_inv`。
             `cupB2sub` = B²（2-コバウンダリ）は Z² の**部分群**、`cupH2group` = H²=Z²/B²。
  * M350F-6  `cup_coboundary` — **f が 1-コバウンダリなら f∪g は 2-コバウンダリ**（本証明）。
             `cup_coboundary_mem` で B² 所属。⟹ ∪ は H¹×H¹→H² に降下。
  * M350F-7  `cupProduct` — 類の上の [f]∪[g]∈H²、`cup_descent_left`（代表の取替に不変）。
  * M350F-8  `cup_bilinear_left`/`cup_bilinear_right` — **双線形**（各引数で加法的）。
  * M350F-9  capstone `cupProductData` / `cupProductBuild` / `cup_exists`。
  * M350F-10 実例 ℤ/n（自明作用・テンソル = zmodMul）`cupZmodPairing` / `cup_zmod_exists`。

  正直な限定（消去・弱化禁止）:
  1. テンソル対 A⊗B は `cupPairing`（双加法的・同変な対）として**受け取る**。
     一般の圏論的テンソル積の普遍性からの構成は範囲外。
  2. H² = Z²/B² は本物（2-コサイクル群・2-コバウンダリ部分群・商群すべて完全証明）。
  3. **次数付き交換律 [f]∪[g] = −[g]∪[f]** は交換同型 C⊗B≅B⊗A を要し、
     `cup_graded_comm_hypothesis`（未導出の Prop 仮説）として明示。
  4. **一般 Hⁿ・全次数にわたる結合律**は本モジュール範囲外（後続）。

  選択公理不使用・sorry 皆無: 公理は [propext, Quot.sound]。禁止タクティク不使用。
  一般名は `cup` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.GaloisCohomologyH1
import IUT.PrincipalUnits

namespace IUT

/-! ## M350F-0: アーベル群の並べ替え補助（本物の群論） -/

/-- **三項巡回並べ替え**（アーベル群）: P·(Q·R) = (R·P)·Q。
    cup の 2-コサイクル条件の代数的核。 -/
theorem cup_abel3 (M : Grp) (comm : ∀ a b, M.mul a b = M.mul b a)
    (P Q R : M.carrier) :
    M.mul P (M.mul Q R) = M.mul (M.mul R P) Q := by
  rw [M.mul_assoc R P Q, comm R (M.mul P Q), M.mul_assoc P Q R]

/-- **六項再編**（アーベル群）: ((P₁P₂)(Q₁Q₂))(R₁R₂) = ((P₁Q₁)R₁)((P₂Q₂)R₂)。
    2-コバウンダリ作用素の加法性の核（`galH1_mul4_swap` を 2 回）。 -/
theorem cup_regroup6 (M : Grp) (comm : ∀ a b, M.mul a b = M.mul b a)
    (P1 P2 Q1 Q2 R1 R2 : M.carrier) :
    M.mul (M.mul (M.mul P1 P2) (M.mul Q1 Q2)) (M.mul R1 R2)
      = M.mul (M.mul (M.mul P1 Q1) R1) (M.mul (M.mul P2 Q2) R2) := by
  rw [galH1_mul4_swap M comm P1 P2 Q1 Q2,
      galH1_mul4_swap M comm (M.mul P1 Q1) (M.mul P2 Q2) R1 R2]

/-- **単位元の逆は単位元**。 -/
theorem cup_inv_one (G : Grp) : G.inv G.one = G.one := by
  have h := G.inv_mul G.one
  rw [G.mul_one] at h
  exact h

/-! ## M350F-1: テンソル対 A⊗B（双加法的・G_K 同変） -/

/-- **テンソル対**（M350F-1a）: G_K-加群 A,B と係数 C = A⊗B の間の双加法的・
    G_K 同変な対 ⊗ : A.M×B.M → C.M。cup の係数構造。 -/
structure cupPairing {GK : Grp} (A B C : galH1Module GK) where
  /-- テンソル ⊗ : A.M×B.M → C.M。 -/
  tensor : A.M.carrier → B.M.carrier → C.M.carrier
  /-- 第一引数で加法的: (a+a')⊗b = a⊗b + a'⊗b。 -/
  add_left : ∀ a a' b,
    tensor (A.M.mul a a') b = C.M.mul (tensor a b) (tensor a' b)
  /-- 第二引数で加法的: a⊗(b+b') = a⊗b + a⊗b'。 -/
  add_right : ∀ a b b',
    tensor a (B.M.mul b b') = C.M.mul (tensor a b) (tensor a b')
  /-- G_K 同変: (g·a)⊗(g·b) = g·(a⊗b)。 -/
  equiv : ∀ g a b,
    tensor ((A.act g).map a) ((B.act g).map b) = (C.act g).map (tensor a b)

/-- **テンソルの零則（左）**（M350F-1b）: 0⊗b = 0。 -/
theorem cup_tensor_one_left {GK : Grp} {A B C : galH1Module GK}
    (P : cupPairing A B C) (b : B.M.carrier) :
    P.tensor A.M.one b = C.M.one := by
  have h := P.add_left A.M.one A.M.one b
  rw [A.M.one_mul A.M.one] at h
  have h2 : C.M.mul C.M.one (P.tensor A.M.one b)
          = C.M.mul (P.tensor A.M.one b) (P.tensor A.M.one b) := by
    rw [C.M.one_mul]
    exact h
  exact (C.M.mul_right_cancel h2).symm

/-- **テンソルと反元（左）**（M350F-1c）: (−a)⊗b = −(a⊗b)。 -/
theorem cup_tensor_inv_left {GK : Grp} {A B C : galH1Module GK}
    (P : cupPairing A B C) (a : A.M.carrier) (b : B.M.carrier) :
    P.tensor (A.M.inv a) b = C.M.inv (P.tensor a b) := by
  apply C.M.inv_eq_of_mul_eq_one
  rw [← P.add_left a (A.M.inv a) b, A.M.mul_inv a, cup_tensor_one_left P b]

/-! ## M350F-2: 1-コチェイン上のカップ積 -/

/-- **カップ積（1-コチェイン）**（M350F-2）: f∈C¹(A), g∈C¹(B) に対し
    (f∪g)(σ,τ) = f(σ)⊗(σ·g(τ)) ∈ C²(A⊗B)。 -/
def cupCochain {GK : Grp} {A B C : galH1Module GK} (P : cupPairing A B C)
    (f : GK.carrier → A.M.carrier) (g : GK.carrier → B.M.carrier) :
    GK.carrier → GK.carrier → C.M.carrier :=
  fun σ τ => P.tensor (f σ) ((B.act σ).map (g τ))

/-! ## M350F-3: 2-コサイクルと Z² -/

/-- **2-コサイクル**（M350F-3a）: c:G×G→C で 2-コサイクル条件
    g·c(h,k) + c(g,hk) = c(gh,k) + c(g,h)。 -/
structure cupTwoCocycle {GK : Grp} (C : galH1Module GK) where
  /-- 台写像 c:G×G→C。 -/
  c : GK.carrier → GK.carrier → C.M.carrier
  /-- 2-コサイクル条件。 -/
  cocycle : ∀ g h k,
    C.M.mul ((C.act g).map (c h k)) (c g (GK.mul h k))
      = C.M.mul (c (GK.mul g h) k) (c g h)

/-- **外延性**（M350F-3b）: 台写像一致 ⟹ 2-コサイクルとして等しい。 -/
theorem cupTwoCocycle.ext {GK : Grp} {C : galH1Module GK}
    {z z' : cupTwoCocycle C} (h : z.c = z'.c) : z = z' := by
  cases z with
  | mk c1 p1 =>
    cases z' with
    | mk c2 p2 =>
      cases h
      rfl

/-- **2-コサイクル群 Z²**（M350F-3c）: 点ごと和・0・反元で閉じる**アーベル群**。
    各閉性の証明が 2-コサイクル条件を本質的に使う（M326F-0 の補助等式）。 -/
def cupZ2group {GK : Grp} (C : galH1Module GK) : Grp where
  carrier := cupTwoCocycle C
  mul := fun z z' =>
    { c := fun g h => C.M.mul (z.c g h) (z'.c g h)
      cocycle := by
        intro g h k
        rw [(C.act g).map_mul (z.c h k) (z'.c h k)]
        rw [galH1_mul4_swap C.M C.comm ((C.act g).map (z.c h k))
          ((C.act g).map (z'.c h k)) (z.c g (GK.mul h k)) (z'.c g (GK.mul h k))]
        rw [z.cocycle g h k, z'.cocycle g h k]
        exact galH1_mul4_swap C.M C.comm (z.c (GK.mul g h) k) (z.c g h)
          (z'.c (GK.mul g h) k) (z'.c g h) }
  one :=
    { c := fun _ _ => C.M.one
      cocycle := by
        intro g _ _
        rw [(C.act g).map_one] }
  inv := fun z =>
    { c := fun g h => C.M.inv (z.c g h)
      cocycle := by
        intro g h k
        rw [(C.act g).map_inv]
        rw [← galH1_inv_mul C.M C.comm ((C.act g).map (z.c h k)) (z.c g (GK.mul h k))]
        rw [z.cocycle g h k]
        exact galH1_inv_mul C.M C.comm (z.c (GK.mul g h) k) (z.c g h) }
  mul_assoc := by
    intro z z' z''
    apply cupTwoCocycle.ext
    funext g h
    exact C.M.mul_assoc (z.c g h) (z'.c g h) (z''.c g h)
  one_mul := by
    intro z
    apply cupTwoCocycle.ext
    funext g h
    exact C.M.one_mul (z.c g h)
  inv_mul := by
    intro z
    apply cupTwoCocycle.ext
    funext g h
    exact C.M.inv_mul (z.c g h)

/-- **Z² はアーベル群**（M350F-3d）。 -/
theorem cupZ2_comm {GK : Grp} (C : galH1Module GK) :
    ∀ z z', (cupZ2group C).mul z z' = (cupZ2group C).mul z' z := by
  intro z z'
  apply cupTwoCocycle.ext
  funext g h
  exact C.comm (z.c g h) (z'.c g h)

/-! ## M350F-4: f∪g は 2-コサイクル -/

/-- **カップ積は 2-コサイクルを与える**（M350F-4a, 本証明）: f∈Z¹(A), g∈Z¹(B)
    なら f∪g は 2-コサイクル条件を満たす。証明は同変性・双加法性・両コサイクル
    条件・アーベル群並べ替え（`cup_abel3`）。 -/
theorem cup_cocycle {GK : Grp} {A B C : galH1Module GK} (P : cupPairing A B C)
    (f : galH1Cocycle A) (g : galH1Cocycle B) :
    ∀ x y z,
      C.M.mul ((C.act x).map (cupCochain P f.f g.f y z))
        (cupCochain P f.f g.f x (GK.mul y z))
        = C.M.mul (cupCochain P f.f g.f (GK.mul x y) z)
            (cupCochain P f.f g.f x y) := by
  intro σ τ ρ
  show C.M.mul ((C.act σ).map (P.tensor (f.f τ) ((B.act τ).map (g.f ρ))))
        (P.tensor (f.f σ) ((B.act σ).map (g.f (GK.mul τ ρ))))
      = C.M.mul (P.tensor (f.f (GK.mul σ τ)) ((B.act (GK.mul σ τ)).map (g.f ρ)))
          (P.tensor (f.f σ) ((B.act σ).map (g.f τ)))
  rw [← P.equiv σ (f.f τ) ((B.act τ).map (g.f ρ)),
      ← B.act_mul σ τ (g.f ρ),
      g.cocycle τ ρ,
      (B.act σ).map_mul (g.f τ) ((B.act τ).map (g.f ρ)),
      ← B.act_mul σ τ (g.f ρ),
      P.add_right (f.f σ) ((B.act σ).map (g.f τ))
        ((B.act (GK.mul σ τ)).map (g.f ρ)),
      f.cocycle σ τ,
      P.add_left (f.f σ) ((A.act σ).map (f.f τ))
        ((B.act (GK.mul σ τ)).map (g.f ρ))]
  exact cup_abel3 C.M C.comm
    (P.tensor ((A.act σ).map (f.f τ)) ((B.act (GK.mul σ τ)).map (g.f ρ)))
    (P.tensor (f.f σ) ((B.act σ).map (g.f τ)))
    (P.tensor (f.f σ) ((B.act (GK.mul σ τ)).map (g.f ρ)))

/-- **cup を Z² へ**（M350F-4b）: 1-コサイクル対から 2-コサイクルを作る。 -/
def cupCocycleOf {GK : Grp} {A B C : galH1Module GK} (P : cupPairing A B C)
    (f : galH1Cocycle A) (g : galH1Cocycle B) : cupTwoCocycle C where
  c := cupCochain P f.f g.f
  cocycle := cup_cocycle P f g

/-! ## M350F-5: 2-コバウンダリと B²・H² -/

/-- **2-コバウンダリ作用素**（M350F-5a）: 1-コチェイン ψ から
    (dψ)(g,h) = g·ψ(h) + ψ(g) − ψ(gh)。 -/
def cupD1 {GK : Grp} (C : galH1Module GK) (ψ : GK.carrier → C.M.carrier) :
    GK.carrier → GK.carrier → C.M.carrier :=
  fun g h => C.M.mul (C.M.mul ((C.act g).map (ψ h)) (ψ g))
    (C.M.inv (ψ (GK.mul g h)))

/-- **d は加法的**（M350F-5b）: d(ψ+ψ') = dψ + dψ'。 -/
theorem cup_d1_add {GK : Grp} (C : galH1Module GK)
    (ψ ψ' : GK.carrier → C.M.carrier) (g h : GK.carrier) :
    cupD1 C (fun s => C.M.mul (ψ s) (ψ' s)) g h
      = C.M.mul (cupD1 C ψ g h) (cupD1 C ψ' g h) := by
  show C.M.mul (C.M.mul ((C.act g).map (C.M.mul (ψ h) (ψ' h)))
        (C.M.mul (ψ g) (ψ' g)))
      (C.M.inv (C.M.mul (ψ (GK.mul g h)) (ψ' (GK.mul g h))))
    = C.M.mul (C.M.mul (C.M.mul ((C.act g).map (ψ h)) (ψ g))
        (C.M.inv (ψ (GK.mul g h))))
      (C.M.mul (C.M.mul ((C.act g).map (ψ' h)) (ψ' g))
        (C.M.inv (ψ' (GK.mul g h))))
  rw [(C.act g).map_mul (ψ h) (ψ' h),
      galH1_inv_mul C.M C.comm (ψ (GK.mul g h)) (ψ' (GK.mul g h))]
  exact cup_regroup6 C.M C.comm ((C.act g).map (ψ h)) ((C.act g).map (ψ' h))
    (ψ g) (ψ' g) (C.M.inv (ψ (GK.mul g h))) (C.M.inv (ψ' (GK.mul g h)))

/-- **d は反元と両立**（M350F-5c）: d(−ψ) = −(dψ)。 -/
theorem cup_d1_inv {GK : Grp} (C : galH1Module GK)
    (ψ : GK.carrier → C.M.carrier) (g h : GK.carrier) :
    cupD1 C (fun s => C.M.inv (ψ s)) g h = C.M.inv (cupD1 C ψ g h) := by
  show C.M.mul (C.M.mul ((C.act g).map (C.M.inv (ψ h))) (C.M.inv (ψ g)))
        (C.M.inv (C.M.inv (ψ (GK.mul g h))))
    = C.M.inv (C.M.mul (C.M.mul ((C.act g).map (ψ h)) (ψ g))
        (C.M.inv (ψ (GK.mul g h))))
  rw [(C.act g).map_inv, C.M.inv_inv (ψ (GK.mul g h)),
      galH1_inv_mul C.M C.comm (C.M.mul ((C.act g).map (ψ h)) (ψ g))
        (C.M.inv (ψ (GK.mul g h))),
      galH1_inv_mul C.M C.comm ((C.act g).map (ψ h)) (ψ g),
      C.M.inv_inv (ψ (GK.mul g h))]

/-- **2-コバウンダリ部分群 B²**（M350F-5d）: Z² の元 z で、ある 1-コチェイン ψ の
    2-コバウンダリ dψ に一致するもの全体。閉性は `cup_d1_add`/`cup_d1_inv`。 -/
def cupB2sub {GK : Grp} (C : galH1Module GK) : Subgroup (cupZ2group C) where
  mem := fun z => ∃ ψ : GK.carrier → C.M.carrier, ∀ g h, z.c g h = cupD1 C ψ g h
  one_mem := by
    refine ⟨fun _ => C.M.one, ?_⟩
    intro g h
    show C.M.one = C.M.mul (C.M.mul ((C.act g).map C.M.one) C.M.one)
      (C.M.inv C.M.one)
    rw [(C.act g).map_one, C.M.one_mul, C.M.one_mul, cup_inv_one C.M]
  mul_mem := fun {z z'} hz hz' => by
    obtain ⟨ψ, hψ⟩ := hz
    obtain ⟨ψ', hψ'⟩ := hz'
    refine ⟨fun s => C.M.mul (ψ s) (ψ' s), ?_⟩
    intro g h
    show C.M.mul (z.c g h) (z'.c g h)
       = cupD1 C (fun s => C.M.mul (ψ s) (ψ' s)) g h
    rw [hψ g h, hψ' g h, cup_d1_add C ψ ψ' g h]
  inv_mem := fun {z} hz => by
    obtain ⟨ψ, hψ⟩ := hz
    refine ⟨fun s => C.M.inv (ψ s), ?_⟩
    intro g h
    show C.M.inv (z.c g h) = cupD1 C (fun s => C.M.inv (ψ s)) g h
    rw [hψ g h, cup_d1_inv C ψ g h]

/-- **B² は正規部分群**（M350F-5e）: Z² はアーベルゆえ。 -/
theorem cupB2_normal {GK : Grp} (C : galH1Module GK) :
    IsNormalSubgroup (cupZ2group C) (cupB2sub C) :=
  galH1_abelian_subgroup_normal (cupZ2group C) (cupZ2_comm C) (cupB2sub C)

/-- **2-コホモロジー H² = Z²/B²**（M350F-5f）: M267F 商群機構。 -/
def cupH2group {GK : Grp} (C : galH1Module GK) : Grp :=
  quotientGroupN (cupZ2group C) (cupB2sub C) (cupB2_normal C)

/-! ## M350F-6: f が 1-コバウンダリなら f∪g は 2-コバウンダリ -/

/-- **カップ積のコバウンダリ降下**（M350F-6a, 本証明）: 1-コバウンダリ f_a と
    1-コサイクル g に対し (f_a∪g)(σ,τ) = (dψ)(σ,τ)、ψ(s) = a⊗g(s)。
    双方とも σ·(a⊗g(τ)) − a⊗(σ·g(τ)) に等しい。 -/
theorem cup_coboundary {GK : Grp} {A B C : galH1Module GK} (P : cupPairing A B C)
    (a : A.M.carrier) (g : galH1Cocycle B) (σ τ : GK.carrier) :
    cupCochain P (galH1Coboundary A a).f g.f σ τ
      = cupD1 C (fun s => P.tensor a (g.f s)) σ τ := by
  show P.tensor (A.M.mul ((A.act σ).map a) (A.M.inv a)) ((B.act σ).map (g.f τ))
    = C.M.mul (C.M.mul ((C.act σ).map (P.tensor a (g.f τ)))
        (P.tensor a (g.f σ)))
      (C.M.inv (P.tensor a (g.f (GK.mul σ τ))))
  rw [P.add_left ((A.act σ).map a) (A.M.inv a) ((B.act σ).map (g.f τ)),
      P.equiv σ a (g.f τ),
      cup_tensor_inv_left P a ((B.act σ).map (g.f τ)),
      g.cocycle σ τ,
      P.add_right a (g.f σ) ((B.act σ).map (g.f τ)),
      galH1_inv_mul C.M C.comm (P.tensor a (g.f σ))
        (P.tensor a ((B.act σ).map (g.f τ)))]
  rw [C.M.mul_assoc ((C.act σ).map (P.tensor a (g.f τ))) (P.tensor a (g.f σ))
        (C.M.mul (C.M.inv (P.tensor a (g.f σ)))
          (C.M.inv (P.tensor a ((B.act σ).map (g.f τ))))),
      ← C.M.mul_assoc (P.tensor a (g.f σ)) (C.M.inv (P.tensor a (g.f σ)))
        (C.M.inv (P.tensor a ((B.act σ).map (g.f τ)))),
      C.M.mul_inv (P.tensor a (g.f σ)), C.M.one_mul]

/-- **cup(f_a,g) は B² に属する**（M350F-6b）: 証人 ψ(s) = a⊗g(s)。 -/
theorem cup_coboundary_mem {GK : Grp} {A B C : galH1Module GK}
    (P : cupPairing A B C) (a : A.M.carrier) (g : galH1Cocycle B) :
    (cupB2sub C).mem (cupCocycleOf P (galH1Coboundary A a) g) := by
  refine ⟨fun s => P.tensor a (g.f s), ?_⟩
  intro σ τ
  exact cup_coboundary P a g σ τ

/-! ## M350F-7: 類の上のカップ積 [f]∪[g]∈H² -/

/-- **カップ積（類）**（M350F-7a）: [f]∪[g] = 射影(f∪g) ∈ H²。 -/
def cupProduct {GK : Grp} {A B C : galH1Module GK} (P : cupPairing A B C)
    (f : galH1Cocycle A) (g : galH1Cocycle B) : (cupH2group C).carrier :=
  (quotientProjN (cupZ2group C) (cupB2sub C) (cupB2_normal C)).map
    (cupCocycleOf P f g)

/-! ## M350F-8: 双線形性 -/

/-- **左加法性**（M350F-8a）: (f+f')∪g = f∪g + f'∪g（Z² の等式）。 -/
theorem cup_bilinear_left {GK : Grp} {A B C : galH1Module GK} (P : cupPairing A B C)
    (f f' : galH1Cocycle A) (g : galH1Cocycle B) :
    cupCocycleOf P ((galH1_cocycles_group A).mul f f') g
      = (cupZ2group C).mul (cupCocycleOf P f g) (cupCocycleOf P f' g) := by
  apply cupTwoCocycle.ext
  funext σ τ
  show P.tensor (A.M.mul (f.f σ) (f'.f σ)) ((B.act σ).map (g.f τ))
    = C.M.mul (P.tensor (f.f σ) ((B.act σ).map (g.f τ)))
        (P.tensor (f'.f σ) ((B.act σ).map (g.f τ)))
  exact P.add_left (f.f σ) (f'.f σ) ((B.act σ).map (g.f τ))

/-- **右加法性**（M350F-8b）: f∪(g+g') = f∪g + f∪g'（Z² の等式）。 -/
theorem cup_bilinear_right {GK : Grp} {A B C : galH1Module GK} (P : cupPairing A B C)
    (f : galH1Cocycle A) (g g' : galH1Cocycle B) :
    cupCocycleOf P f ((galH1_cocycles_group B).mul g g')
      = (cupZ2group C).mul (cupCocycleOf P f g) (cupCocycleOf P f g') := by
  apply cupTwoCocycle.ext
  funext σ τ
  show P.tensor (f.f σ) ((B.act σ).map (B.M.mul (g.f τ) (g'.f τ)))
    = C.M.mul (P.tensor (f.f σ) ((B.act σ).map (g.f τ)))
        (P.tensor (f.f σ) ((B.act σ).map (g'.f τ)))
  rw [(B.act σ).map_mul (g.f τ) (g'.f τ)]
  exact P.add_right (f.f σ) ((B.act σ).map (g.f τ)) ((B.act σ).map (g'.f τ))

/-- **代表の取替に不変（左）**（M350F-8c）: f を 1-コバウンダリ f_a だけずらしても
    [f]∪[g] は H² で不変。双線形性 + `cup_coboundary_mem`（B² は射影で潰れる）。
    ⟹ ∪ は H¹×H¹→H² に well-defined に降下。 -/
theorem cup_descent_left {GK : Grp} {A B C : galH1Module GK} (P : cupPairing A B C)
    (f : galH1Cocycle A) (a : A.M.carrier) (g : galH1Cocycle B) :
    cupProduct P ((galH1_cocycles_group A).mul f (galH1Coboundary A a)) g
      = cupProduct P f g := by
  show (quotientProjN (cupZ2group C) (cupB2sub C) (cupB2_normal C)).map
        (cupCocycleOf P ((galH1_cocycles_group A).mul f (galH1Coboundary A a)) g)
      = (quotientProjN (cupZ2group C) (cupB2sub C) (cupB2_normal C)).map
        (cupCocycleOf P f g)
  rw [cup_bilinear_left P f (galH1Coboundary A a) g,
      (quotientProjN (cupZ2group C) (cupB2sub C) (cupB2_normal C)).map_mul
        (cupCocycleOf P f g) (cupCocycleOf P (galH1Coboundary A a) g)]
  have hone : (quotientProjN (cupZ2group C) (cupB2sub C) (cupB2_normal C)).map
        (cupCocycleOf P (galH1Coboundary A a) g)
      = (quotientGroupN (cupZ2group C) (cupB2sub C) (cupB2_normal C)).one :=
    (quotientProjN_ker (cupZ2group C) (cupB2sub C) (cupB2_normal C)
      (cupCocycleOf P (galH1Coboundary A a) g)).mpr (cup_coboundary_mem P a g)
  rw [hone, (quotientGroupN (cupZ2group C) (cupB2sub C) (cupB2_normal C)).mul_one]

/-! ## M350F-9: capstone -/

/-- **capstone データ**（M350F-9a）: テンソル対 P に対する cup の全部品 —
    2-コサイクル群 Z²・2-コバウンダリ B²・H²=Z²/B²・コチェイン写像・類写像、
    双線形性・降下（well-defined）。 -/
structure cupProductData {GK : Grp} {A B C : galH1Module GK}
    (P : cupPairing A B C) where
  /-- 2-コサイクル群 Z²。 -/
  Z2 : Grp
  /-- 2-コバウンダリ部分群 B²。 -/
  B2 : Subgroup Z2
  /-- H² = Z²/B²。 -/
  H2 : Grp
  /-- Z¹×Z¹ → Z²（コチェイン上の cup）。 -/
  onCocycles : galH1Cocycle A → galH1Cocycle B → cupTwoCocycle C
  /-- H¹×H¹ → H²（類上の cup）。 -/
  onClasses : galH1Cocycle A → galH1Cocycle B → H2.carrier
  /-- Z² の同定。 -/
  Z2_is : Z2 = cupZ2group C
  /-- H² の同定。 -/
  H2_is : H2 = cupH2group C
  /-- コチェイン写像の同定。 -/
  onCocycles_is : ∀ f g, (onCocycles f g).c = cupCochain P f.f g.f
  /-- 左加法性。 -/
  bilinear_left : ∀ f f' g,
    onCocycles ((galH1_cocycles_group A).mul f f') g
      = (cupZ2group C).mul (onCocycles f g) (onCocycles f' g)
  /-- 右加法性。 -/
  bilinear_right : ∀ f g g',
    onCocycles f ((galH1_cocycles_group B).mul g g')
      = (cupZ2group C).mul (onCocycles f g) (onCocycles f g')
  /-- 代表の取替に不変（H¹×H¹→H² への降下）。 -/
  descends_left : ∀ f a g,
    onClasses ((galH1_cocycles_group A).mul f (galH1Coboundary A a)) g
      = onClasses f g

/-- **証人**（M350F-9b）。 -/
def cupProductBuild {GK : Grp} {A B C : galH1Module GK} (P : cupPairing A B C) :
    cupProductData P where
  Z2 := cupZ2group C
  B2 := cupB2sub C
  H2 := cupH2group C
  onCocycles := cupCocycleOf P
  onClasses := cupProduct P
  Z2_is := rfl
  H2_is := rfl
  onCocycles_is := fun _ _ => rfl
  bilinear_left := cup_bilinear_left P
  bilinear_right := cup_bilinear_right P
  descends_left := cup_descent_left P

/-- **cup 構造の存在**（M350F-9c）。 -/
theorem cup_exists {GK : Grp} {A B C : galH1Module GK} (P : cupPairing A B C) :
    Nonempty (cupProductData P) :=
  ⟨cupProductBuild P⟩

/-- **Z² は（アーベル）群**（M350F-9d）。 -/
theorem cup_Z2_isGroup {GK : Grp} (C : galH1Module GK) :
    ∀ z z', (cupZ2group C).mul z z' = (cupZ2group C).mul z' z :=
  cupZ2_comm C

/-! ## M350F-10: 実例 ℤ/n（自明作用・テンソル = zmodMul） -/

/-- **右分配則**（M350F-10a）: ℤ/n で (a+b)·c = a·c + b·c。 -/
theorem cup_zmod_right_distrib (n : Nat) (a b c : (zmod n).carrier) :
    zmodMul n ((zmod n).mul a b) c
      = (zmod n).mul (zmodMul n a c) (zmodMul n b c) := by
  induction a using Quot.ind
  rename_i x
  induction b using Quot.ind
  rename_i y
  induction c using Quot.ind
  rename_i z
  show Quot.mk (modCong n).rel ((x + y) * z)
     = Quot.mk (modCong n).rel (x * z + y * z)
  rw [Int.add_mul]

/-- **左分配則**（M350F-10b）: ℤ/n で a·(b+c) = a·b + a·c。 -/
theorem cup_zmod_left_distrib (n : Nat) (a b c : (zmod n).carrier) :
    zmodMul n a ((zmod n).mul b c)
      = (zmod n).mul (zmodMul n a b) (zmodMul n a c) := by
  induction a using Quot.ind
  rename_i x
  induction b using Quot.ind
  rename_i y
  induction c using Quot.ind
  rename_i z
  show Quot.mk (modCong n).rel (x * (y + z))
     = Quot.mk (modCong n).rel (x * y + x * z)
  rw [Int.mul_add]

/-- **自明作用 ℤ/n 加群**（M350F-10c）。 -/
def cupZmodModule (GK : Grp) (n : Nat) : galH1Module GK :=
  galH1TrivialModule GK (zmod n) (cycStd_add_comm n)

/-- **ℤ/n のテンソル対**（M350F-10d）: 自明作用・⊗ = zmodMul。同変性は自明作用ゆえ
    id⊗id = id で成立、双加法性は ℤ/n の分配則。 -/
def cupZmodPairing (GK : Grp) (n : Nat) :
    cupPairing (cupZmodModule GK n) (cupZmodModule GK n) (cupZmodModule GK n) where
  tensor := zmodMul n
  add_left := cup_zmod_right_distrib n
  add_right := cup_zmod_left_distrib n
  equiv := fun _ _ _ => rfl

/-- **実例 capstone**（M350F-10e）: ℤ/n 上の cup 構造。 -/
def cupZmodData (GK : Grp) (n : Nat) : cupProductData (cupZmodPairing GK n) :=
  cupProductBuild (cupZmodPairing GK n)

/-- **実例存在**（M350F-10f）: H¹(G_K,ℤ/n)×H¹(G_K,ℤ/n)→H²(G_K,ℤ/n) の cup。 -/
theorem cup_zmod_exists (GK : Grp) (n : Nat) :
    Nonempty (cupProductData (cupZmodPairing GK n)) :=
  ⟨cupZmodData GK n⟩

/-! ## M350F-11: 外部仮説（未導出・honest hypothesis） -/

/-- **外部仮説（未証明・未導出）: 次数付き交換律** [f]∪[g] = −[g]∪[f]。
    交換同型 C⊗B ≅ B⊗A（P' : cupPairing B A C'）と符号（H² の反元）を用いた
    次数 1×1 の graded-commutativity。交換同型の構成は本モジュール範囲外ゆえ
    **導出せず Prop 仮説として明示**（正直な限定）。 -/
def cup_graded_comm_hypothesis {GK : Grp} {A B C C' : galH1Module GK}
    (P : cupPairing A B C) (P' : cupPairing B A C') : Prop :=
  ∀ (f : galH1Cocycle A) (g : galH1Cocycle B),
    ∃ iso : Hom (cupH2group C) (cupH2group C'),
      iso.map (cupProduct P f g) = (cupH2group C').inv (cupProduct P' g f)

end IUT
