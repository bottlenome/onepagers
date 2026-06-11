/-
  IUT/FundamentalGroup.lean — M9（テンパード基本群・数論的基本群の理論）の形式化

  IUT の全構成（遠アーベル復元 [AbsTopIII]、エタールテータ [EtTh]、
  Frobenioid [FrdI/II]、Hodge theater [IUTchI]）の**土台**である
  基本群理論の論理骨格を形式化する。一次資料:

  * 数論的基本群: 完全列 1 → Δ → Π → G_K → 1（Δ = 幾何的基本群、
    Π = 数論的基本群、G_K = 基礎体の絶対ガロア群）。[IUTchI] §2 では
    Π ↠ G_K と Δ = ker が基本データとして常用される
  * テンパード基本群（André; Mochizuki "Semi-graphs of Anabelioids"）:
    p 進局所体上の双曲的曲線の被覆で「有限エタール被覆で引き戻すと
    位相的（無限離散）被覆になる」ものを分類する群 π₁^temp。
    副有限完備化が通常のエタール基本群 π₁^ét を与える
  * IUT がテンパードを必要とする理由（[EtTh] §1, [IUTchI] §2）:
    Tate 曲線の被覆 Ÿ → X はガロア群 **ℤ**（有限でない！）を持つ
    テンパード被覆であり、エタールテータ関数はこの Ÿ 上にのみ住む。
    テータ値 q^{j²}（M4 の評価理論）のラベル j はこのデッキ群 ℤ の
    元であり、いかなる有限商 ℤ/n でも指数簿記 j ↦ j² は潰れる

  検証する定理（全て sorry なし）:
  【数論的基本群の完全列】
  * M9-1 `geometric_normal` — 幾何的部分 ι(Δ) は Π の正規部分群
    （完全性から、公理ゼロ）
  * M9-2 `outer_conjugation_unique` — Π の共役は Δ に一意に持ち上がる
    （Π が Δ に作用することの形式的内容）
  * M9-3 `outer_action_inner_on_kernel` — ι(Δ) の元による共役は Δ の
    内部自己同型。よって商 G = Π/Δ の Out(Δ) への**外ガロア作用**が
    well-defined（遠アーベル幾何の出発点となる作用の存在）
  * M9-4 `slim_faithful` — Δ が slim（中心自明）なら共役表現は忠実。
    [AbsTopIII] 等で基本群の slim 性が復元の前提になる形式的理由
  * M9-5 `section_decomposition` — pr の切断 s があれば Π の各元は
    ι(d)·s(pr x) に**一意分解**する（数論的基本群の分裂、
    global multiplicative subspace 問題の形式骨格）
  【テンパード理論の核心】
  * M9-6 `theta_deck_not_finite` — テータ被覆のデッキ群 ℤ は有界指数
    でない（= 有限エタール被覆では実現不能。テンパードが真に必要）
  * M9-7 `theta_exponent_unique` — 自動形式性の差分方程式
    F(j+1) = F(j) + 2j + 1, F(0) = 0 の解は F(j) = j² ただ一つ
    （テータ零点の位数簿記が q^{j²} を**強制**する）
  * M9-8 `theta_exponent_not_periodic` — その解は非周期的。よって
    テータ簿記はいかなる有限商被覆 ℤ/p にも降下しない
  * M9-9 `finite_quotient_collapses_theta` — デッキ群 ℤ から有界指数群
    へのどんな準同型もテータラベルを潰す（j ≠ k で像が衝突するのに
    j² ≠ k²）。**π₁^ét（副有限）では足りず π₁^temp が必要**という
    IUT の主張の形式的内容（M4 評価理論の土台）
  * M9-10 `arithmetic_quotient_collapses_theta` — 同じ崩壊が数論的
    テンパード基本群 Π のどんな有界指数商でも起こる
  【無矛盾性と接続】
  * M9-11 `temperedArithmetic_consistent` — 公理系の無矛盾性
    （Tate 曲線型の玩具モデル: Δ = ℤ, Π = ℤ × ℤ, G = ℤ）
  * M9-12 `tempered_invariant_transport` — テンパード遠アーベル定理
    （André・Mochizuki: p 進双曲的曲線は π₁^temp から復元される）を
    M1 の ReconSetting で読むと、M1-7 の転送原理がそのまま適用できる
    （M9 → M1 接続）

  **形式化の範囲（正直な申告）**: ここで建設するのは基本群理論の
  **群論的骨格**である。位相（副有限位相・テンパード位相）、
  semi-graph of anabelioids の頂点・辺の分解群、および
  「実際の双曲的曲線の π₁^temp が slim である」等の幾何的入力は
  未形式化であり、`Slim` は中心自明性（slim 性の核心部分）として
  公理化する。M9-6〜M9-10 は具体的なデッキ群 ℤ 上の完全な証明で
  あり、公理化を含まない。
-/
import IUT.Anabelian

namespace IUT

/-! ## 最小群論（mathlib 非依存）

基本群を扱うための抽象群・準同型・冪を core Lean だけで建設する。 -/

/-- 抽象群。公理は左単位元・左逆元のみ（右側は定理として導出）。 -/
structure Grp where
  carrier : Type
  mul : carrier → carrier → carrier
  one : carrier
  inv : carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  inv_mul : ∀ a, mul (inv a) a = one

/-- 左簡約律。 -/
theorem Grp.mul_left_cancel (G : Grp) {a x y : G.carrier}
    (h : G.mul a x = G.mul a y) : x = y := by
  have h1 : G.mul (G.inv a) (G.mul a x) = G.mul (G.inv a) (G.mul a y) :=
    congrArg (G.mul (G.inv a)) h
  rw [← G.mul_assoc, ← G.mul_assoc, G.inv_mul, G.one_mul, G.one_mul] at h1
  exact h1

/-- 右逆元（左公理からの導出）。 -/
theorem Grp.mul_inv (G : Grp) (a : G.carrier) : G.mul a (G.inv a) = G.one := by
  have h := G.inv_mul (G.inv a)
  calc G.mul a (G.inv a)
      = G.mul G.one (G.mul a (G.inv a)) := (G.one_mul _).symm
    _ = G.mul (G.mul (G.inv (G.inv a)) (G.inv a)) (G.mul a (G.inv a)) := by rw [h]
    _ = G.mul (G.inv (G.inv a)) (G.mul (G.inv a) (G.mul a (G.inv a))) := G.mul_assoc _ _ _
    _ = G.mul (G.inv (G.inv a)) (G.mul (G.mul (G.inv a) a) (G.inv a)) := by
        rw [← G.mul_assoc (G.inv a) a (G.inv a)]
    _ = G.mul (G.inv (G.inv a)) (G.mul G.one (G.inv a)) := by rw [G.inv_mul]
    _ = G.mul (G.inv (G.inv a)) (G.inv a) := by rw [G.one_mul]
    _ = G.one := G.inv_mul _

/-- 右単位元（左公理からの導出）。 -/
theorem Grp.mul_one (G : Grp) (a : G.carrier) : G.mul a G.one = a := by
  rw [← G.inv_mul a, ← G.mul_assoc, G.mul_inv, G.one_mul]

/-- 右簡約律。 -/
theorem Grp.mul_right_cancel (G : Grp) {a x y : G.carrier}
    (h : G.mul x a = G.mul y a) : x = y := by
  have h1 : G.mul (G.mul x a) (G.inv a) = G.mul (G.mul y a) (G.inv a) := by
    rw [h]
  rw [G.mul_assoc, G.mul_assoc, G.mul_inv, G.mul_one, G.mul_one] at h1
  exact h1

/-- 逆元の特徴付け: a·b = 1 なら b = a⁻¹。 -/
theorem Grp.inv_eq_of_mul_eq_one (G : Grp) {a b : G.carrier}
    (h : G.mul a b = G.one) : b = G.inv a := by
  have h1 : G.mul (G.inv a) (G.mul a b) = G.mul (G.inv a) G.one :=
    congrArg (G.mul (G.inv a)) h
  rw [← G.mul_assoc, G.inv_mul, G.one_mul, G.mul_one] at h1
  exact h1

/-- 群準同型。 -/
structure Hom (G H : Grp) where
  map : G.carrier → H.carrier
  map_mul : ∀ a b, map (G.mul a b) = H.mul (map a) (map b)

/-- 準同型は単位元を保つ。 -/
theorem Hom.map_one {G H : Grp} (f : Hom G H) : f.map G.one = H.one := by
  have h : H.mul (f.map G.one) (f.map G.one) = H.mul (f.map G.one) H.one := by
    rw [← f.map_mul, G.one_mul, H.mul_one]
  exact H.mul_left_cancel h

/-- 準同型は逆元を保つ。 -/
theorem Hom.map_inv {G H : Grp} (f : Hom G H) (a : G.carrier) :
    f.map (G.inv a) = H.inv (f.map a) := by
  apply H.inv_eq_of_mul_eq_one
  rw [← f.map_mul, G.mul_inv, f.map_one]

/-- 単射性。 -/
def Hom.Injective {G H : Grp} (f : Hom G H) : Prop :=
  ∀ a b, f.map a = f.map b → a = b

/-- 準同型の合成。 -/
def Hom.comp {G H K : Grp} (g : Hom H K) (f : Hom G H) : Hom G K where
  map := fun a => g.map (f.map a)
  map_mul := fun a b => by rw [f.map_mul, g.map_mul]

/-- 単射の合成は単射。 -/
theorem Hom.comp_injective {G H K : Grp} {g : Hom H K} {f : Hom G H}
    (hg : g.Injective) (hf : f.Injective) : (g.comp f).Injective :=
  fun a b h => hf a b (hg _ _ h)

/-- 冪 g^n（n : Nat）。 -/
def Grp.pow (G : Grp) (g : G.carrier) : Nat → G.carrier
  | 0 => G.one
  | n + 1 => G.mul g (G.pow g n)

/-- 準同型は冪を保つ。 -/
theorem Hom.map_pow {G H : Grp} (f : Hom G H) (g : G.carrier) (n : Nat) :
    f.map (G.pow g n) = H.pow (f.map g) n := by
  induction n with
  | zero => exact f.map_one
  | succ k ih =>
    show f.map (G.mul g (G.pow g k)) = H.mul (f.map g) (H.pow (f.map g) k)
    rw [f.map_mul, ih]

/-! ## 数論的基本群の完全列 1 → Δ → Π → G → 1

p 進局所体（または数体）K 上の双曲的曲線 X の数論的基本群 Π = π₁(X)
は、幾何的基本群 Δ = π₁(X_K̄) と絶対ガロア群 G = G_K の拡大である。
[IUTchI] §2 はこの完全列（テンパード版を含む）を全構成の入力とする。 -/

/-- **数論的基本群の完全列**: ι : Δ ↪ Π（幾何的部分の単射）、
    pr : Π ↠ G（ガロア群への全射）、および完全性
    ker(pr) = im(ι)。 -/
structure GaloisSequence where
  /-- 幾何的（テンパード）基本群 Δ = π₁(X_K̄)。 -/
  Δ : Grp
  /-- 数論的（テンパード）基本群 Π = π₁(X)。 -/
  Pi : Grp
  /-- 絶対ガロア群 G_K。 -/
  Gal : Grp
  ι : Hom Δ Pi
  pr : Hom Pi Gal
  ι_inj : ι.Injective
  pr_surj : ∀ g : Gal.carrier, ∃ x : Pi.carrier, pr.map x = g
  exact_seq : ∀ x : Pi.carrier, pr.map x = Gal.one ↔ ∃ d : Δ.carrier, ι.map d = x

/-- **定理 (M9-1): 幾何的基本群の正規性** — ι(Δ) = ker(pr) は Π の
    正規部分群。完全列の最初の帰結であり、Π が Δ に共役で作用する
    ことの前提。公理ゼロで証明される。 -/
theorem geometric_normal (S : GaloisSequence) (x : S.Pi.carrier) (d : S.Δ.carrier) :
    ∃ d' : S.Δ.carrier,
      S.ι.map d' = S.Pi.mul (S.Pi.mul x (S.ι.map d)) (S.Pi.inv x) := by
  apply (S.exact_seq _).mp
  have hd : S.pr.map (S.ι.map d) = S.Gal.one := (S.exact_seq _).mpr ⟨d, rfl⟩
  rw [S.pr.map_mul, S.pr.map_mul, S.pr.map_inv, hd, S.Gal.mul_one, S.Gal.mul_inv]

/-- **定理 (M9-2): 共役持ち上げの一意性** — Π の元 x による共役は
    Δ の元に**一意に**持ち上がる。すなわち Π は Δ に作用し、この
    作用が外ガロア作用 G → Out(Δ) の素材になる。 -/
theorem outer_conjugation_unique (S : GaloisSequence) (x : S.Pi.carrier) (d : S.Δ.carrier) :
    ∃ d' : S.Δ.carrier,
      S.ι.map d' = S.Pi.mul (S.Pi.mul x (S.ι.map d)) (S.Pi.inv x) ∧
      ∀ d'' : S.Δ.carrier,
        S.ι.map d'' = S.Pi.mul (S.Pi.mul x (S.ι.map d)) (S.Pi.inv x) → d'' = d' := by
  obtain ⟨d', hd'⟩ := geometric_normal S x d
  exact ⟨d', hd', fun d'' hd'' => S.ι_inj _ _ (hd''.trans hd'.symm)⟩

/-- **定理 (M9-3): 外ガロア作用の well-defined 性** — ker(pr) = ι(Δ)
    の元による共役は Δ の**内部**自己同型を誘導する。したがって
    商 G = Π/Δ は Out(Δ) = Aut(Δ)/Inn(Δ) に well-defined に作用する。
    この外ガロア作用が遠アーベル幾何（M1）の入力である。 -/
theorem outer_action_inner_on_kernel (S : GaloisSequence) (x : S.Pi.carrier)
    (hx : S.pr.map x = S.Gal.one) :
    ∃ e : S.Δ.carrier, ∀ d : S.Δ.carrier,
      S.Pi.mul (S.Pi.mul x (S.ι.map d)) (S.Pi.inv x)
        = S.ι.map (S.Δ.mul (S.Δ.mul e d) (S.Δ.inv e)) := by
  obtain ⟨e, he⟩ := (S.exact_seq x).mp hx
  refine ⟨e, fun d => ?_⟩
  rw [S.ι.map_mul, S.ι.map_mul, S.ι.map_inv, he]

/-- **slim 性**（の核心部分 = 中心自明性）: 中心化する元は単位元のみ。
    Mochizuki の slim（全ての開部分群の中心化群が自明）の、本骨格で
    使用する帰結。実際の双曲的曲線の Δ^temp が slim であることは
    [SemiAnbd] 等の幾何的定理であり未形式化。 -/
def Slim (G : Grp) : Prop :=
  ∀ z : G.carrier, (∀ a : G.carrier, G.mul z a = G.mul a z) → z = G.one

/-- **定理 (M9-4): slim ⟹ 共役表現の忠実性** — Δ が slim なら、
    ι(Δ) 全体と可換な Δ の元は単位元に限る。これが「数論的基本群は
    自分自身の共役で Δ を見分けられる」こと、ひいては復元理論で
    基本群の slim 性が常に仮定される形式的理由である。 -/
theorem slim_faithful (S : GaloisSequence) (hslim : Slim S.Δ)
    (d : S.Δ.carrier)
    (hcentral : ∀ e : S.Δ.carrier,
      S.Pi.mul (S.ι.map d) (S.ι.map e) = S.Pi.mul (S.ι.map e) (S.ι.map d)) :
    d = S.Δ.one := by
  apply hslim
  intro e
  apply S.ι_inj
  rw [S.ι.map_mul, S.ι.map_mul]
  exact hcentral e

/-- **定理 (M9-5): 切断による一意分解** — pr の群論的切断
    s : G → Π（pr ∘ s = id）が存在すれば、Π の各元は
    x = ι(d) · s(pr x) と**一意に**分解する。数論的基本群の分裂
    （半直積構造）の形式的内容であり、IUT で問題になる
    global multiplicative subspace / 切断の選択の骨格。 -/
theorem section_decomposition (S : GaloisSequence) (s : Hom S.Gal S.Pi)
    (hs : ∀ g, S.pr.map (s.map g) = g) (x : S.Pi.carrier) :
    ∃ d : S.Δ.carrier,
      x = S.Pi.mul (S.ι.map d) (s.map (S.pr.map x)) ∧
      ∀ d' : S.Δ.carrier,
        x = S.Pi.mul (S.ι.map d') (s.map (S.pr.map x)) → d' = d := by
  have hy : S.pr.map (S.Pi.mul x (S.Pi.inv (s.map (S.pr.map x)))) = S.Gal.one := by
    rw [S.pr.map_mul, S.pr.map_inv, hs, S.Gal.mul_inv]
  obtain ⟨d, hd⟩ := (S.exact_seq _).mp hy
  have hx : x = S.Pi.mul (S.ι.map d) (s.map (S.pr.map x)) := by
    rw [hd, S.Pi.mul_assoc, S.Pi.inv_mul, S.Pi.mul_one]
  refine ⟨d, hx, fun d' hd' => ?_⟩
  apply S.ι_inj
  apply S.Pi.mul_right_cancel (a := s.map (S.pr.map x))
  rw [← hx, ← hd']

/-! ## テンパード理論の核心: テータ被覆とデッキ群 ℤ

Tate 曲線（q-パラメータを持つ楕円曲線から少数の点を除いた双曲的
曲線）X に対し、[EtTh] §1 はテンパード被覆 Ÿ → Y → X を構成する。
Y → X のガロア群（デッキ群）は **ℤ** であり、エタールテータ関数は
この無限被覆 Ÿ の上にのみ存在する。テータ値 q^{j²}（M4）のラベル
j ∈ F_l⋇ は、このデッキ群 ℤ の元 j のことである。

以下では (1) デッキ群 ℤ は有限被覆では実現できない、(2) テータの
指数簿記 j ↦ j² は差分方程式から一意に強制される、(3) いかなる
有限商（→ 副有限完備化 π₁^ét の有限レベル）もこの簿記を潰す、を
完全証明する。これが「IUT は π₁^ét でなく π₁^temp を必要とする」
の形式的内容である。 -/

/-- テータ被覆 Y → X のデッキ群 ℤ（加法群）。 -/
@[reducible] def intGrp : Grp where
  carrier := Int
  mul := fun a b => a + b
  one := 0
  inv := fun a => -a
  mul_assoc := fun a b c => by show a + b + c = a + (b + c); omega
  one_mul := fun a => by show 0 + a = a; omega
  inv_mul := fun a => by show -a + a = 0; omega

/-- **有界指数性**: ある N > 0 で全元の N 乗が消える。有限群は
    位数 N でこれを満たす（Lagrange）ので、これは有限性の帰結を
    抽出した形式的代理である（有限性そのものより弱い分、
    非有限性の証明はより強い主張になる）。 -/
def BoundedExponent (G : Grp) : Prop :=
  ∃ N : Nat, 0 < N ∧ ∀ g : G.carrier, G.pow g N = G.one

/-- デッキ群 ℤ における冪: 1 の n 乗 = n。 -/
theorem intGrp_pow_one (n : Nat) : intGrp.pow 1 n = (n : Int) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (1 : Int) + intGrp.pow 1 k = ((k + 1 : Nat) : Int)
    rw [ih]
    omega

/-- **定理 (M9-6): テータ被覆は有限エタールでない** — デッキ群 ℤ は
    有界指数を持たない（元 1 の位数が無限）。よってガロア群 ℤ を
    持つテータ被覆 Y → X は有限エタール被覆の枠内に存在せず、
    位相的被覆を許すテンパード理論が**真に必要**である。 -/
theorem theta_deck_not_finite : ¬ BoundedExponent intGrp := by
  intro h
  obtain ⟨N, hN, hpow⟩ := h
  have h1 : ((N : Nat) : Int) = 0 := by
    have h2 := hpow 1
    rw [intGrp_pow_one] at h2
    exact h2
  omega

/-- 平方の差分展開 (m+1)² = m² + 2m + 1（補題）。 -/
theorem sq_succ (m : Int) : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add]
  generalize m * m = K
  omega

/-- **定理 (M9-7): テータ指数の一意性** — テータ関数の自動形式性
    （デッキ移動 j ↦ j+1 で零点位数が 2j+1 だけ増える、[EtTh] §1 の
    関数等式の指数部分）を満たす簿記 F : ℤ → ℤ は F(j) = j² ただ
    一つ。テータ値が q^{j²} という**二次**の指数を持つこと（M4 の
    `GaussianEvaluation` の値）は、この差分方程式から強制される。 -/
theorem theta_exponent_unique (F : Int → Int) (h0 : F 0 = 0)
    (hrec : ∀ j : Int, F (j + 1) = F j + 2 * j + 1) :
    ∀ j : Int, F j = j * j := by
  have pos : ∀ n : Nat, F (n : Int) = (n : Int) * (n : Int) := by
    intro n
    induction n with
    | zero =>
      show F 0 = 0 * 0
      rw [h0]
      rfl
    | succ k ih =>
      have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hc, hrec, ih, sq_succ]
  have neg : ∀ n : Nat, F (-(n : Int)) = (n : Int) * (n : Int) := by
    intro n
    induction n with
    | zero =>
      show F (-(0 : Int)) = 0 * 0
      have hz : (-(0 : Int)) = 0 := rfl
      rw [hz, h0]
      rfl
    | succ k ih =>
      have hc : (-(((k + 1 : Nat) : Int))) + 1 = -(k : Int) := by omega
      have hr := hrec (-(((k + 1 : Nat) : Int)))
      rw [hc, ih] at hr
      have hc2 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hc2] at hr ⊢
      rw [sq_succ]
      revert hr
      generalize F (-((k : Int) + 1)) = A
      generalize (k : Int) * (k : Int) = K
      intro hr
      omega
  intro j
  obtain h | h := Int.natAbs_eq j
  · rw [h]
    exact pos j.natAbs
  · rw [h, Int.neg_mul, Int.mul_neg, Int.neg_neg]
    exact neg j.natAbs

/-- **定理 (M9-8): テータ簿記の非周期性** — 指数簿記 F(j) = j² は
    いかなる周期 p > 0 も持たない。よってテータ関数（の零点簿記）は
    有限部分被覆 ℤ/p に降下しない: テンパード被覆 Ÿ の無限性は
    エタールテータの存在に**不可欠**である。 -/
theorem theta_exponent_not_periodic (F : Int → Int) (h0 : F 0 = 0)
    (hrec : ∀ j : Int, F (j + 1) = F j + 2 * j + 1) (p : Int) (hp : 0 < p) :
    F p ≠ F 0 := by
  rw [theta_exponent_unique F h0 hrec p, h0]
  intro hcontra
  have hpos : (0 : Int) < p * p := Int.mul_pos hp hp
  rw [hcontra] at hpos
  exact Int.lt_irrefl 0 hpos

/-- **定理 (M9-9): 有限商はテータ簿記を潰す** — デッキ群 ℤ から
    有界指数群 F（任意の有限群の形式的代理）へのどんな準同型 f も、
    テータ指数の異なる二つのラベル j, k（j² ≠ k²）を同じ元に送る。

    すなわち副有限完備化 π₁^ét の有限レベルではテータ値 q^{j²} の
    ラベル付けが必ず退化し、評価理論（M4）はテンパード基本群
    π₁^temp の上でのみ機能する。これが基本群理論が M4/M5 の土台で
    ある所以の機械検証である。 -/
theorem finite_quotient_collapses_theta (F : Grp) (hF : BoundedExponent F)
    (f : Hom intGrp F) :
    ∃ j k : Int, f.map j = f.map k ∧ j * j ≠ k * k := by
  obtain ⟨N, hN, hpow⟩ := hF
  refine ⟨(N : Int), 0, ?_, ?_⟩
  · have h1 : f.map ((N : Nat) : Int) = F.one := by
      rw [← intGrp_pow_one N, f.map_pow, hpow]
    have h2 : f.map 0 = F.one := f.map_one
    rw [h1, h2]
  · have hNpos : (0 : Int) < (N : Int) := by omega
    have hpos : (0 : Int) < (N : Int) * (N : Int) := Int.mul_pos hNpos hNpos
    intro heq
    have hzero : ((0 : Int) * 0) = 0 := rfl
    rw [hzero] at heq
    rw [heq] at hpos
    exact Int.lt_irrefl 0 hpos

/-! ## 数論的テンパード基本群: 完全列とテータ被覆の合流

[IUTchI] §2 の設定: bad place v では数論的**テンパード**基本群
Π_v = π₁^temp(X_v) を使い、その幾何的部分 Δ_v^temp がテータ被覆の
デッキ群 ℤ を含む。両理論を合成した骨格を形式化する。 -/

/-- **数論的テンパード基本群**: ガロア完全列 1 → Δ → Π → G → 1 に
    加え、幾何的部分 Δ がテータ被覆のデッキ群 ℤ を忠実に含む。 -/
structure TemperedArithmetic extends GaloisSequence where
  /-- テータ被覆 Y → X のデッキ群 ℤ の Δ^temp への埋め込み。 -/
  θ : Hom intGrp Δ
  θ_inj : θ.Injective

/-- テータ被覆のデッキ群は数論的基本群 Π にも忠実に入る
    （単射の合成、M9-10 の前提）。 -/
theorem theta_in_arithmetic (T : TemperedArithmetic) :
    (T.ι.comp T.θ).Injective :=
  Hom.comp_injective T.ι_inj T.θ_inj

/-- **定理 (M9-10): 数論的基本群の有限商でもテータ簿記は潰れる** —
    数論的テンパード基本群 Π から有界指数群へのどんな準同型も、
    テータ被覆由来のラベル j ≠ k（j² ≠ k²）を衝突させる。
    M9-9 の崩壊現象は幾何的部分に限らず、数論的基本群全体の
    どんな「有限近似」でも不可避である。 -/
theorem arithmetic_quotient_collapses_theta (T : TemperedArithmetic)
    (F : Grp) (hF : BoundedExponent F) (f : Hom T.Pi F) :
    ∃ j k : Int,
      (f.comp (T.ι.comp T.θ)).map j = (f.comp (T.ι.comp T.θ)).map k ∧
      j * j ≠ k * k :=
  finite_quotient_collapses_theta F hF (f.comp (T.ι.comp T.θ))

/-! ## 無矛盾性 -/

/-- 直積群（モデル構成用）。 -/
@[reducible] def prodGrp (G H : Grp) : Grp where
  carrier := G.carrier × H.carrier
  mul := fun p q => (G.mul p.1 q.1, H.mul p.2 q.2)
  one := (G.one, H.one)
  inv := fun p => (G.inv p.1, H.inv p.2)
  mul_assoc := fun p q r => by
    show (G.mul (G.mul p.1 q.1) r.1, H.mul (H.mul p.2 q.2) r.2) = _
    rw [G.mul_assoc, H.mul_assoc]
  one_mul := fun p => by
    show (G.mul G.one p.1, H.mul H.one p.2) = p
    rw [G.one_mul, H.one_mul]
  inv_mul := fun p => by
    show (G.mul (G.inv p.1) p.1, H.mul (H.inv p.2) p.2) = (G.one, H.one)
    rw [G.inv_mul, H.inv_mul]

/-- **Tate 曲線型の玩具モデル**: Δ = ℤ（テータ被覆のデッキ群そのもの）、
    Π = ℤ × ℤ、G = ℤ。完全列は 0 → ℤ → ℤ² → ℤ → 0（第2成分への射影）。
    実際の Tate 曲線では Δ^temp ⊋ ℤ・G_K は非可換だが、公理系の
    無矛盾性の確認にはこの可換モデルで十分である。 -/
def tateModel : TemperedArithmetic where
  Δ := intGrp
  Pi := prodGrp intGrp intGrp
  Gal := intGrp
  ι := { map := fun n => (n, 0),
         map_mul := fun a b => by
           show ((a + b : Int), (0 : Int)) = (a + b, (0 : Int) + 0)
           rw [Int.add_zero] }
  pr := { map := fun p => p.2, map_mul := fun _ _ => rfl }
  ι_inj := fun a b h => congrArg Prod.fst h
  pr_surj := fun g => ⟨(0, g), rfl⟩
  exact_seq := fun x =>
    ⟨fun h => ⟨x.1, by
        have h2 : x.2 = (0 : Int) := h
        show (x.1, (0 : Int)) = x
        rw [← h2]⟩,
     fun h => by
        obtain ⟨d, hd⟩ := h
        show x.2 = (0 : Int)
        rw [← hd]⟩
  θ := { map := fun n => n, map_mul := fun _ _ => rfl }
  θ_inj := fun _ _ h => h

/-- **定理 (M9-11): 公理系の無矛盾性** — 数論的テンパード基本群の
    公理系（完全列＋テータ被覆の埋め込み）は Tate 曲線型モデルで
    充足される。 -/
theorem temperedArithmetic_consistent : Nonempty TemperedArithmetic :=
  ⟨tateModel⟩

/-- **定理 (M9-12): テンパード遠アーベル転送（M9 → M1 接続）** —
    テンパード遠アーベル定理（André・Mochizuki [SemiAnbd]:
    p 進局所体上の双曲的曲線は π₁^temp から関手的に復元される）を
    M1 の復元設定（F = 双曲的曲線、G = π₁^temp）として読めば、
    M1-7 の転送原理がそのまま適用でき、同型不変量はすべて
    テンパード基本群から計算できる。テンパード理論が遠アーベル
    復元（[AbsTopIII]）・テータ評価（M4）の土台に立つ経路の形式化。 -/
theorem tempered_invariant_transport (S : ReconSetting) (h : MonoAnabelian S)
    {α : Type} (φ : S.F → α)
    (hφ : ∀ {X Y : S.F}, S.isoF X Y → φ X = φ Y) :
    ∃ ψ : S.G → α, ∀ X, ψ (S.pi X) = φ X :=
  invariant_transport S h φ hφ

end IUT
