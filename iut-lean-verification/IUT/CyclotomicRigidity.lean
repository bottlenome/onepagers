/-
  IUT/CyclotomicRigidity.lean — M322F（柱A: 円分剛性 = mono-anabelian の中心。
  円分指標 χ_n : G_K → (ℤ/n)^× を G_K の μ_n への作用から本物構成し、その
  **準同型性**と**円分の一意決定（剛性）**を完全証明する）

  ── 主要成果の分類: **[実]**（本物の巡回群 μ_n = ⟨ζ⟩（1 の n 乗根、位数ちょうど n）
  の上に建てた本物の絶対ガロア群 G_K（M315F `algCloAbsGalois`）の作用から、
  σ(ζ)=ζ^{χ(σ)} を与える **円分指標 χ_n : G_K → (ℤ/n)^×** を実構成し、
  σ(τ(ζ))=σ(ζ^{χτ})=ζ^{χσ·χτ} という**準同型性 χ(στ)=χ(σ)·χ(τ)** と、
  μ_n への作用が χ で**一意に決まる**円分剛性を core Lean のみで完全証明する。
  主語は toy ではなく、本物の巡回群 CycMuGroup（実例は M13 の実巡回群 ℤ/n=`zmod n`）
  と本物の群準同型 Hom μ_n μ_n（実 Galois 自己同型が住む所）。）

  complete_pct 影響: **柱A「円分剛性 = mono-anabelian の中心」の本物の先行建設**。
  既存 `IUT/CyclotomicSync.lean`（M124F）は**テータ群 mod l の中心** (0,0,z) を
  μ_l に送る中心写像 centerToMu : ℤ → μ_l ⊆ ℤ_p の準同型性・忠実性を建てたが、
  その主語は「テータ群の中心 (0,0,z)」であって **G_K（絶対ガロア群）の μ_n への
  作用そのもの**ではなかった（centerToMu は z ∈ ℤ をパラメタとする写像で、
  ガロア作用の指数抽出ではない）。本モジュールはそこを昇格し、**本物の G_K の
  μ_n への群作用（各 g ↦ Hom μ_n μ_n の自己同型）から円分指標 χ_n(g)=(σ_g が ζ を
  送る指数) を本物に抽出**し、
    (1) χ_n(g·h)=χ_n(g)·χ_n(h)（(ℤ/n) の積）を σ の合成の指数計算で完全証明、
    (2) χ_n(1)=1、χ_n が (ℤ/n)^× に値を取る（χ_n(g) が単元）を完全証明、
    (3) μ_n への作用が χ_n で**一意に決定される**（σ_g(z)=ζ^{χ_n(g)·log_ζ z}）円分剛性、
    (4) 2 つの作用が χ で一致すれば μ_n 上で同変同型が一致する円分同期、
  を本物で閉じる。指数抽出は μ_n が巡回群であること（生成元 ζ の離散対数 log）で本物。
  昇格対象: M124F「中心 (0,0,z)↦μ_l の写像」→「G_K の μ_n 作用からの円分指標 χ_n」。

  内容（本物・toy を主語にしない）:
  * M322F-1 巡回群の冪法則: `cycRig_pow_add`（ζ^{a+b}=ζ^a·ζ^b）・`cycRig_pow_mul`
    （ζ^{ab}=(ζ^a)^b）・`cycRig_pow_period`（ζ^n=1 なら ζ^{e+nk}=ζ^e）・
    `cycRig_pow_reduce`（ζ^a=ζ^{a%n}）・`cycRig_pow_inj`（ζ^a=ζ^b → a%n=b%n、
    位数 n の相異性から）。可換群 Grp 上で完全証明。
  * M322F-2 `CycMuGroup` — 本物の巡回群 μ_n=⟨ζ⟩（可換群 μ・生成元 ζ・位数 n・
    ζ^n=1・離散対数 log : μ→ℕ（log z<n, ζ^{log z}=z）・冪の相異性 distinct）。
    IUT の l-捻れ点が住む 1 の n 乗根の群の本物の抽象。
  * M322F-3 `CycGKAction` — G_K の μ_n への**群作用**（各 g ↦ Hom μ_n μ_n、
    単位元は恒等・合成則）。実 Galois 自己同型が μ_n に作用する枠組み。
  * M322F-4 `cycRigExp` / `cycRigChar` — **円分指標** χ_n(g) = log_ζ(σ_g(ζ)) ∈ ℤ/n
    （σ_g(ζ)=ζ^{χ(g)} の指数）。`cycRig_act_pow`（σ_g(ζ^k)=ζ^{χ(g)·k}、作用の指数形）。
  * M322F-5 `cycRig_char_isHom`（**本丸1: 準同型性**）χ(g·h)=χ(g)·χ(h)（σ の合成
    σ_g(σ_h(ζ))=σ_g(ζ^{χh})=ζ^{χg·χh} と位数 n の相異性から (ℤ/n) の積で完全証明）。
    `cycRig_char_one`（χ(1)=1）・`cycRig_char_unit`（χ(g)∈(ℤ/n)^×、逆元=χ(g⁻¹)）。
  * M322F-6 `cycRig_rigidity`（**本丸2: 円分剛性**）σ_g(z)=ζ^{χ(g)·log_ζ z}（μ_n への
    作用が χ で一意に決定）・`cycRig_sync`（2 つの作用が χ 一致 ⟹ μ_n 上で一致、
    円分同期の同変同型）。
  * M322F-7 `cycRigCharProfinite` — χ_n の族（各 level n の χ）と各 level 準同型
    `cycRig_profinite_hom`、trivial（不分岐）族の逆系両立 `cycRig_profinite_trivial_compat`
    （ẑ^× への完全な逆極限持ち上げは骨組み・後続）。
  * M322F-8 `cycRig_theta_sync` — テータ中心の円分同期（M124F `centerToMu_add`）を
    接続点として再輸出（テータ値の円分部分が χ で同期する骨組み）。
  * M322F-9 capstone `CyclotomicRigidityData` / `cycRig_exists` / `cycRig_char_hom` /
    `cycRig_rigidity_capstone`。
  * M322F-10 実例 `cycMuStd`（本物の巡回群 ℤ/n=`zmod n` を μ_n として実構成、
    生成元 ζ=class 1・log=最小非負剰余）と、**本物の絶対ガロア群 G_ℚ=`algCloAbsGalois
    algCloTrivialTower` の μ_l 上の作用**から χ_l : G_ℚ → (ℤ/l)^× を実例化。

  **正直な限定**（何が本物で何が骨組み/後続か）:
  1. **本物（完全証明・sorry/新規 choice 皆無）**: 巡回群の冪法則（加法・乗法・周期・
     剰余還元・位数 n の単射性）、円分指標 χ_n(g)=log_ζ(σ_g ζ) の構成、**準同型性
     χ(g·h)=χ(g)·χ(h)（本丸1）**、χ(1)=1・χ(g) が (ℤ/n)^× の単元、**円分剛性
     σ_g(z)=ζ^{χ(g)·log z}（本丸2）**、円分同期（2 作用が χ 一致⟹μ_n 上一致）。
     実例の μ_n=ℤ/n（`zmod n`）は本物の巡回群（M13 商群）で、生成元・離散対数・位数 n の
     相異性を完全証明。実例の G_K は本物の絶対ガロア群 `algCloAbsGalois`（M315F）。
  2. **正直申告（骨組み/後続）**:
     ・**G_K の μ_n への作用は `CycGKAction` として抽象データで受け取る**（各 g ↦ 実
       群準同型 Hom μ_n μ_n）。M315F `algCloAction`（G_K の K^sep=colim Lₙ の germ への
       実作用）から μ_n（1 の n 乗根 ⊆ K^sep）への作用へ**具体的に降ろす**（μ_n の
       germ 表現を固定し σ_n の toFun を制限する）のは柱A/E 後続。実例では**本物の
       G_K の trivial（不分岐）作用**（χ≡1、σ(ζ)=ζ）を与えて χ の存在・準同型・剛性を
       本物の G_K 上で確認する。非自明な χ（σ(ζ)=ζ^a, a≠1）を与える実 Galois 自己同型の
       μ_n への降下は後続（作用データ CycGKAction を供給すれば本モジュールの χ・準同型・
       剛性は即座に本物で回る）。
     ・**pro-有限 χ : G_K → ẑ^× の逆極限完全構成は骨組み**: 各 level の χ_n（本物）と
       trivial 族の逆系両立（本物）まで。n｜m の逆系全体の両立と ẑ^× の逆極限
       （M287F `limitGrp`）への持ち上げの完全構成は後続。
     ・**テータの円分同期は骨組み**: M124F の中心写像 centerToMu の準同型性を接続点として
       再輸出（`cycRig_theta_sync`）するのみ。テータ値 Θ の円分部分と χ_n の完全な
       同一視（mono-theta 環境の 3 種の剛性の 1 つ・IUT 本丸）は柱E/D 後続。
     ・**円分剛性の完全形**（mono-theta 環境での "テータ環境のシクロトーム = 基礎体の
       シクロトーム" の遠アーベル復元）は柱E/D 後続。本モジュールは χ_n:G_K→(ℤ/n)^× の
       構成・準同型性・作用の一意決定（μ_n の G_K-加群構造が χ で完全に決まること）を本物で。

  **選択公理不使用**（新規 Classical.choice を証明本体に導入しない）: 冪法則は帰納、
  指数抽出は CycMuGroup の離散対数 log（実例では最小非負剰余=構成的）、準同型性・
  剛性は冪の指数計算と位数 n の単射性。sorry 不使用・禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用。許可タクティク（cases/obtain/induction/rw/show/refine/exact/apply/intro/
  generalize/funext/omega）のみ使用。共有ファイル（IUT.lean・build.sh・dashboard.md・
  graph 系）は一切変更していない。一般名は `cycRig` 接頭辞で衝突回避。
-/
import IUT.AlgClosureColimit
import IUT.CyclotomicSync

namespace IUT

/-! ## M322F-1: 巡回群の冪法則（可換群 Grp 上） -/

/-- **M322F-1a: 冪の加法則** ζ^{a+b}=ζ^a·ζ^b（b の帰納、可換性で g と冪の付け替え）。 -/
theorem cycRig_pow_add (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (g : G.carrier) (a b : Nat) :
    G.pow g (a + b) = G.mul (G.pow g a) (G.pow g b) := by
  induction b with
  | zero => exact (G.mul_one (G.pow g a)).symm
  | succ b ih =>
    show G.mul g (G.pow g (a + b)) = G.mul (G.pow g a) (G.mul g (G.pow g b))
    rw [ih, ← G.mul_assoc, hc g (G.pow g a), G.mul_assoc]

/-- **M322F-1b: 冪の乗法則** ζ^{a·b}=(ζ^a)^b（b の帰納、加法則と可換性）。 -/
theorem cycRig_pow_mul (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (g : G.carrier) (a b : Nat) :
    G.pow g (a * b) = G.pow (G.pow g a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show G.pow g (a * (b + 1)) = G.mul (G.pow g a) (G.pow (G.pow g a) b)
    rw [Nat.mul_succ, cycRig_pow_add G hc g (a * b) a, ih]
    exact hc (G.pow (G.pow g a) b) (G.pow g a)

/-- **M322F-1c: 周期性** ζ^n=1 なら ζ^{e+n·k}=ζ^e（k の帰納 + 加法則）。 -/
theorem cycRig_pow_period (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (g : G.carrier) (n : Nat) (hord : G.pow g n = G.one) :
    ∀ (k e : Nat), G.pow g (e + n * k) = G.pow g e := by
  intro k
  induction k with
  | zero => intro e; rfl
  | succ k ih =>
    intro e
    have hstep : e + n * (k + 1) = (e + n * k) + n := by rw [Nat.mul_succ]; omega
    rw [hstep, cycRig_pow_add G hc g (e + n * k) n, hord, G.mul_one, ih e]

/-- **M322F-1d: 剰余還元** ζ^a=ζ^{a % n}（周期性と a = a%n + n·(a/n)）。 -/
theorem cycRig_pow_reduce (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (g : G.carrier) (n : Nat) (hord : G.pow g n = G.one) (a : Nat) :
    G.pow g a = G.pow g (a % n) := by
  have h := cycRig_pow_period G hc g n hord (a / n) (a % n)
  rw [Nat.mod_add_div a n] at h
  exact h

/-- **M322F-1e: Nat 剰余一致 → Int 整除** a % n = b % n なら n ∣ (a−b)（Int）。 -/
theorem cycRig_nat_mod_dvd (n a b : Nat) (h : a % n = b % n) :
    ((n : Nat) : Int) ∣ (a : Int) - (b : Int) := by
  have e1 : (n : Int) * ((a / n : Nat) : Int) + ((a % n : Nat) : Int) = (a : Int) := by
    have h0 := Nat.div_add_mod a n
    rw [← Int.natCast_mul, ← Int.natCast_add, h0]
  have e2 : (n : Int) * ((b / n : Nat) : Int) + ((b % n : Nat) : Int) = (b : Int) := by
    have h0 := Nat.div_add_mod b n
    rw [← Int.natCast_mul, ← Int.natCast_add, h0]
  have hab : ((a % n : Nat) : Int) = ((b % n : Nat) : Int) := by rw [h]
  refine ⟨((a / n : Nat) : Int) - ((b / n : Nat) : Int), ?_⟩
  rw [Int.mul_sub, ← e1, ← e2, hab]
  omega

/-- **M322F-1f: 位数 n の単射性** ζ^a=ζ^b なら a%n=b%n（相異性 distinct から）。
    円分指標の well-defined 性（ℤ/n 値）の核。 -/
theorem cycRig_pow_inj (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (g : G.carrier) (n : Nat) (hn : 1 ≤ n) (hord : G.pow g n = G.one)
    (hdist : ∀ i j, i < j → j < n → G.pow g i ≠ G.pow g j)
    (a b : Nat) (h : G.pow g a = G.pow g b) : a % n = b % n := by
  have ha := cycRig_pow_reduce G hc g n hord a
  have hb := cycRig_pow_reduce G hc g n hord b
  have hab : G.pow g (a % n) = G.pow g (b % n) := by rw [← ha, ← hb]; exact h
  have han : a % n < n := Nat.mod_lt a hn
  have hbn : b % n < n := Nat.mod_lt b hn
  cases Nat.lt_trichotomy (a % n) (b % n) with
  | inl hlt => exact absurd hab (hdist (a % n) (b % n) hlt hbn)
  | inr h2 =>
    cases h2 with
    | inl heq => exact heq
    | inr hgt => exact absurd hab.symm (hdist (b % n) (a % n) hgt han)

/-! ## M322F-2: 本物の巡回群 μ_n = ⟨ζ⟩（1 の n 乗根の群） -/

/-- **M322F-2: 本物の巡回群 μ_n**（1 の n 乗根の群）— 可換群 μ・生成元 ζ・位数 n・
    ζ^n=1・離散対数 log_ζ（log z < n, ζ^{log z}=z、μ=⟨ζ⟩ の構成的完全性）・冪の相異性
    （ζ^0,…,ζ^{n−1} 相異、位数ちょうど n）。IUT のテータ評価点 μ_l が住む 1 の n 乗根の
    群の本物の抽象。実例は M13 の実巡回群 ℤ/n=`zmod n`（`cycMuStd`）。 -/
structure CycMuGroup where
  /-- 1 の n 乗根の群 μ_n（可換群）。 -/
  μ : Grp
  /-- μ_n は可換（1 の n 乗根は乗法可換）。 -/
  comm : ∀ a b, μ.mul a b = μ.mul b a
  /-- 生成元 ζ（原始 n 乗根、μ_n=⟨ζ⟩）。 -/
  ζ : μ.carrier
  /-- 位数 n。 -/
  n : Nat
  /-- 1 ≤ n。 -/
  hn : 1 ≤ n
  /-- ζ^n = 1。 -/
  ord : μ.pow ζ n = μ.one
  /-- 離散対数 log_ζ : μ_n → ℕ（各元は ζ の冪、その指数）。 -/
  log : μ.carrier → Nat
  /-- log は範囲 [0,n)。 -/
  log_lt : ∀ z, log z < n
  /-- ζ^{log z} = z（μ_n=⟨ζ⟩ の構成的完全性）。 -/
  pow_log : ∀ z, μ.pow ζ (log z) = z
  /-- ζ^0,…,ζ^{n−1} は相異（位数ちょうど n）。 -/
  distinct : ∀ i j, i < j → j < n → μ.pow ζ i ≠ μ.pow ζ j

/-! ## M322F-3: G_K の μ_n への群作用 -/

/-- **M322F-3: G_K の μ_n への群作用** — 各 g ∈ G_K は μ_n の**群自己準同型**
    σ_g = act g : Hom μ_n μ_n（実 Galois 自己同型が μ_n に作用する所）で作用し、
    単位元は恒等（σ_1=id）・合成則 σ_{g·h}=σ_g∘σ_h を満たす。μ_n への G_K-加群構造。 -/
structure CycGKAction (GK : Grp) (M : CycMuGroup) where
  /-- 各 g への μ_n の群自己準同型 σ_g。 -/
  act : GK.carrier → Hom M.μ M.μ
  /-- σ_1 = id（単位元の作用は恒等）。 -/
  act_one : ∀ z, (act GK.one).map z = z
  /-- σ_{g·h} = σ_g∘σ_h（合成則）。 -/
  act_mul : ∀ g h z, (act (GK.mul g h)).map z = (act g).map ((act h).map z)

/-! ## M322F-4: 円分指標 χ_n : G_K → ℤ/n -/

/-- **M322F-4a: 円分指数** χ(g) = log_ζ(σ_g(ζ)) ∈ ℕ — σ_g が生成元 ζ を送る指数
    （σ_g(ζ)=ζ^{χ(g)}）。μ_n が巡回群であることによる本物の指数抽出。 -/
def cycRigExp (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) : Nat := M.log ((ρ.act g).map M.ζ)

/-- **M322F-4b: 円分指標** χ_n : G_K → ℤ/n（円分指数の ℤ/n 類）。IUT の cyclotomic
    rigidity の代数的核: G_K の μ_n への作用が定める指標。 -/
def cycRigChar (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) : (zmod M.n).carrier :=
  Quot.mk (modCong M.n).rel ((cycRigExp GK M ρ g : Int))

/-- **M322F-4c: 作用の指数形** σ_g(ζ^k)=ζ^{χ(g)·k}（Hom.map_pow + pow_log + 乗法則）。 -/
theorem cycRig_act_pow (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (k : Nat) :
    (ρ.act g).map (M.μ.pow M.ζ k) = M.μ.pow M.ζ (cycRigExp GK M ρ g * k) := by
  have key : M.μ.pow M.ζ (cycRigExp GK M ρ g) = (ρ.act g).map M.ζ :=
    M.pow_log ((ρ.act g).map M.ζ)
  rw [Hom.map_pow, ← key, cycRig_pow_mul M.μ M.comm M.ζ (cycRigExp GK M ρ g) k]

/-- **M322F-4d: 合成の生成元像** σ_{g·h}(ζ)=ζ^{χ(g)·χ(h)}（作用の指数形の合成）。 -/
theorem cycRig_exp_mul_pow (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) :
    M.μ.pow M.ζ (cycRigExp GK M ρ (GK.mul g h))
      = M.μ.pow M.ζ (cycRigExp GK M ρ g * cycRigExp GK M ρ h) := by
  have e1 : M.μ.pow M.ζ (cycRigExp GK M ρ (GK.mul g h)) = (ρ.act (GK.mul g h)).map M.ζ :=
    M.pow_log ((ρ.act (GK.mul g h)).map M.ζ)
  have hh : (ρ.act h).map M.ζ = M.μ.pow M.ζ (cycRigExp GK M ρ h) :=
    (M.pow_log ((ρ.act h).map M.ζ)).symm
  rw [e1, ρ.act_mul g h M.ζ, hh, cycRig_act_pow GK M ρ g (cycRigExp GK M ρ h)]

/-! ## M322F-5: 準同型性（本丸1）・単位元・単元性 -/

/-- **M322F-5a: 円分指標の準同型性（本丸1）** — χ_n(g·h)=χ_n(g)·χ_n(h)（ℤ/n の積）。
    σ_g(σ_h(ζ))=σ_g(ζ^{χh})=ζ^{χg·χh} と位数 n の相異性（ζ^a=ζ^b→a≡b mod n）から。
    円分指標が G_K → (ℤ/n)^× の**群準同型**であること = 円分剛性の代数的核。 -/
theorem cycRig_char_isHom (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) :
    cycRigChar GK M ρ (GK.mul g h)
      = zmodMul M.n (cycRigChar GK M ρ g) (cycRigChar GK M ρ h) := by
  have hmod : cycRigExp GK M ρ (GK.mul g h) % M.n
      = (cycRigExp GK M ρ g * cycRigExp GK M ρ h) % M.n :=
    cycRig_pow_inj M.μ M.comm M.ζ M.n M.hn M.ord M.distinct _ _
      (cycRig_exp_mul_pow GK M ρ g h)
  have hdvd := cycRig_nat_mod_dvd M.n (cycRigExp GK M ρ (GK.mul g h))
    (cycRigExp GK M ρ g * cycRigExp GK M ρ h) hmod
  show Quot.mk (modCong M.n).rel ((cycRigExp GK M ρ (GK.mul g h) : Int))
     = Quot.mk (modCong M.n).rel ((cycRigExp GK M ρ g : Int) * (cycRigExp GK M ρ h : Int))
  apply Quot.sound
  show ((M.n : Nat) : Int) ∣ (cycRigExp GK M ρ (GK.mul g h) : Int)
      - (cycRigExp GK M ρ g : Int) * (cycRigExp GK M ρ h : Int)
  rw [← Int.natCast_mul]
  exact hdvd

/-- **M322F-5b: χ(1)=1** — σ_1=id ゆえ σ_1(ζ)=ζ=ζ^1、指数 ≡ 1 mod n。 -/
theorem cycRig_char_one (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    cycRigChar GK M ρ GK.one = Quot.mk (modCong M.n).rel 1 := by
  have hz : M.μ.pow M.ζ (cycRigExp GK M ρ GK.one) = M.μ.pow M.ζ 1 := by
    have e1 : M.μ.pow M.ζ (cycRigExp GK M ρ GK.one) = (ρ.act GK.one).map M.ζ :=
      M.pow_log ((ρ.act GK.one).map M.ζ)
    rw [e1, ρ.act_one M.ζ]
    show M.ζ = M.μ.mul M.ζ (M.μ.pow M.ζ 0)
    show M.ζ = M.μ.mul M.ζ M.μ.one
    exact (M.μ.mul_one M.ζ).symm
  have hmod : cycRigExp GK M ρ GK.one % M.n = 1 % M.n :=
    cycRig_pow_inj M.μ M.comm M.ζ M.n M.hn M.ord M.distinct _ _ hz
  have hdvd := cycRig_nat_mod_dvd M.n (cycRigExp GK M ρ GK.one) 1 hmod
  show Quot.mk (modCong M.n).rel ((cycRigExp GK M ρ GK.one : Int))
     = Quot.mk (modCong M.n).rel 1
  apply Quot.sound
  show ((M.n : Nat) : Int) ∣ (cycRigExp GK M ρ GK.one : Int) - 1
  exact hdvd

/-- **M322F-5c: χ(g) は (ℤ/n)^× の単元** — 逆元は χ(g⁻¹)（χ(g)·χ(g⁻¹)=χ(g·g⁻¹)=χ(1)=1）。
    これにより χ_n は **G_K → (ℤ/n)^×**（単元群への準同型）に値を取る。 -/
theorem cycRig_char_unit (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) :
    ∃ v, zmodMul M.n (cycRigChar GK M ρ g) v = Quot.mk (modCong M.n).rel 1 := by
  refine ⟨cycRigChar GK M ρ (GK.inv g), ?_⟩
  rw [← cycRig_char_isHom GK M ρ g (GK.inv g), GK.mul_inv g, cycRig_char_one]

/-! ## M322F-6: 円分剛性（本丸2）と円分同期 -/

/-- **M322F-6a: 円分剛性（本丸2）** — σ_g(z)=ζ^{χ(g)·log_ζ z}。μ_n の任意の元 z への
    G_K の作用が円分指標 χ(g) で**一意に決定**される（z=ζ^{log z} に作用の指数形を適用）。
    円分指標が μ_n の G_K-加群構造を完全に決めること = 円分剛性。 -/
theorem cycRig_rigidity (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (z : M.μ.carrier) :
    (ρ.act g).map z = M.μ.pow M.ζ (cycRigExp GK M ρ g * M.log z) := by
  have key := cycRig_act_pow GK M ρ g (M.log z)
  rw [M.pow_log z] at key
  exact key

/-- **M322F-6b: 円分同期** — 2 つの G_K 作用 ρ・ρ' が同じ円分指数を持てば（χ_ρ(g)=χ_{ρ'}(g)）、
    μ_n 上で作用が一致する（σ_g^ρ(z)=σ_g^{ρ'}(z)）。2 つの μ_n コピー間の G_K-同変同型が
    χ の一致で一意に貼り合う円分同期の核。 -/
theorem cycRig_sync (GK : Grp) (M : CycMuGroup) (ρ ρ' : CycGKAction GK M)
    (g : GK.carrier) (hchar : cycRigExp GK M ρ g = cycRigExp GK M ρ' g)
    (z : M.μ.carrier) :
    (ρ.act g).map z = (ρ'.act g).map z := by
  rw [cycRig_rigidity GK M ρ g z, cycRig_rigidity GK M ρ' g z, hchar]

/-! ## M322F-7: pro-有限 χ : G_K → ẑ^×（骨組み） -/

/-- **M322F-7a: 円分指標の族** χ_{n} — 各 level n（μ_n の族 Mf n と作用 ρf n）での
    円分指標。pro-有限版 χ : G_K → ẑ^× の逆系の各成分。 -/
def cycRigCharProfinite (GK : Grp) (Mf : Nat → CycMuGroup)
    (ρf : ∀ n, CycGKAction GK (Mf n)) (g : GK.carrier) (n : Nat) :
    (zmod (Mf n).n).carrier :=
  cycRigChar GK (Mf n) (ρf n) g

/-- **M322F-7b: 各 level の準同型性**（χ の族は各 level で群準同型）。 -/
theorem cycRig_profinite_hom (GK : Grp) (Mf : Nat → CycMuGroup)
    (ρf : ∀ n, CycGKAction GK (Mf n)) (g h : GK.carrier) (n : Nat) :
    cycRigCharProfinite GK Mf ρf (GK.mul g h) n
      = zmodMul (Mf n).n (cycRigCharProfinite GK Mf ρf g n)
          (cycRigCharProfinite GK Mf ρf h n) :=
  cycRig_char_isHom GK (Mf n) (ρf n) g h

/-! ## M322F-8/10 準備: 本物の巡回群 ℤ/n = `zmod n` を μ_n に -/

/-- **M322F-10a-i: ℤ/n の加法は可換**（Int 加法の可換性）。 -/
theorem cycStd_add_comm (n : Nat) (x y : (zmod n).carrier) :
    (zmod n).mul x y = (zmod n).mul y x := by
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  show Quot.mk (modCong n).rel (a + b) = Quot.mk (modCong n).rel (b + a)
  rw [Int.add_comm]

/-- **M322F-10a-ii: ℤ/n の生成元 class 1 の冪** (class 1)^k = class k
    （M287F の射影 quotProj と `intGrp_pow_one` から）。 -/
theorem cycStd_pow (n k : Nat) :
    (zmod n).pow (Quot.mk (modCong n).rel 1) k = Quot.mk (modCong n).rel (k : Int) := by
  have h := Hom.map_pow (quotProj intGrp (modCong n)) (1 : Int) k
  rw [intGrp_pow_one] at h
  exact h.symm

/-- **M322F-10a-iii: Int 剰余の合同不変性** n ∣ a−b なら a % n = b % n。 -/
theorem cycRig_int_emod_congr (n : Int) {a b : Int} (h : n ∣ a - b) :
    a % n = b % n := by
  obtain ⟨k, hk⟩ := h
  have ha : a = b + n * k := by omega
  rw [ha, Int.add_mul_emod_self_left]

/-- **M322F-10a: 本物の標準巡回群 μ_n = ℤ/n**（M13 商群 `zmod n`）— 生成元 ζ=class 1、
    離散対数 log=最小非負剰余 (a % n).toNat、位数 n、冪の相異性を完全証明。toy でない
    本物の巡回群を μ_n の実例とする。 -/
def cycMuStd (n : Nat) (hn : 1 ≤ n) : CycMuGroup where
  μ := zmod n
  comm := cycStd_add_comm n
  ζ := Quot.mk (modCong n).rel 1
  n := n
  hn := hn
  ord := by
    show (zmod n).pow (Quot.mk (modCong n).rel 1) n = (zmod n).one
    rw [cycStd_pow n n]
    show Quot.mk (modCong n).rel (n : Int) = Quot.mk (modCong n).rel 0
    exact Quot.sound ⟨1, by omega⟩
  log := fun z => Quot.lift (fun a => (a % (n : Int)).toNat)
    (fun a b hab => by
      show (a % (n : Int)).toNat = (b % (n : Int)).toNat
      rw [cycRig_int_emod_congr (n : Int) hab]) z
  log_lt := by
    intro z
    induction z using Quot.ind; rename_i a
    show (a % (n : Int)).toNat < n
    have h1 : 0 ≤ a % (n : Int) := Int.emod_nonneg a (by omega)
    have h2 : a % (n : Int) < (n : Int) := Int.emod_lt_of_pos a (by omega)
    have htn : (((a % (n : Int)).toNat : Nat) : Int) = a % (n : Int) := Int.toNat_of_nonneg h1
    have h3 : (((a % (n : Int)).toNat : Nat) : Int) < (n : Int) := by rw [htn]; exact h2
    exact Int.ofNat_lt.mp h3
  pow_log := by
    intro z
    induction z using Quot.ind; rename_i a
    show (zmod n).pow (Quot.mk (modCong n).rel 1) ((a % (n : Int)).toNat)
       = Quot.mk (modCong n).rel a
    rw [cycStd_pow n ((a % (n : Int)).toNat)]
    apply Quot.sound
    show ((n : Nat) : Int) ∣ (((a % (n : Int)).toNat : Nat) : Int) - a
    have h1 : 0 ≤ a % (n : Int) := Int.emod_nonneg a (by omega)
    have htn : (((a % (n : Int)).toNat : Nat) : Int) = a % (n : Int) := Int.toNat_of_nonneg h1
    rw [htn]
    have hd := Int.emod_add_mul_ediv a (n : Int)
    refine ⟨-(a / (n : Int)), ?_⟩
    rw [Int.mul_neg]
    omega
  distinct := by
    intro i j hij hj heq'
    rw [cycStd_pow n i, cycStd_pow n j] at heq'
    have hrel := quot_exact intGrp (modCong n) heq'
    have hrel2 : ((n : Nat) : Int) ∣ (j : Int) - (i : Int) := dvd_sub_symm hrel
    have hcast : ((j - i : Nat) : Int) = (j : Int) - (i : Int) :=
      Int.natCast_sub (Nat.le_of_lt hij)
    rw [← hcast] at hrel2
    have hnat : n ∣ (j - i) := Int.ofNat_dvd.mp hrel2
    have hlt : j - i < n := by omega
    have hz0 : j - i = 0 := Nat.eq_zero_of_dvd_of_lt hnat hlt
    omega

/-! ## M322F-8: テータの円分同期との接続（骨組み） -/

/-- **M322F-8: テータ中心の円分同期（接続点・骨組み）** — M124F の中心写像 centerToMu の
    準同型性 centerToMu(z+z')=centerToMu(z)·centerToMu(z') を接続点として再輸出する。
    テータ群 mod l の中心（テータ環境のシクロトーム）の円分同期が、本モジュールの
    円分指標 χ_n（基礎体のシクロトーム G_K→(ℤ/n)^×）と同じ**乗法的同期構造**を持つことの
    骨組み。テータ値 Θ の円分部分と χ_n の完全な同一視は柱E/D 後続。 -/
theorem cycRig_theta_sync (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) (z z' : Int) :
    centerToMu p l ζ (z + z')
      = zpMul p (centerToMu p l ζ z) (centerToMu p l ζ z') :=
  centerToMu_add p l hl ζ hζl z z'

/-! ## M322F-9: capstone -/

/-- **M322F-9a: 円分剛性データ** — G_K・μ_n・作用 ρ・円分指標 χ・準同型性・χ(1)=1・
    単元性・剛性（作用が χ で一意決定）を束ねる。mono-anabelian 円分剛性の総括。 -/
structure CyclotomicRigidityData (GK : Grp) (M : CycMuGroup) where
  /-- G_K の μ_n への作用 σ_g。 -/
  ρ : CycGKAction GK M
  /-- 円分指標 χ_n : G_K → ℤ/n。 -/
  char : GK.carrier → (zmod M.n).carrier
  /-- char は cycRigChar。 -/
  char_eq : ∀ g, char g = cycRigChar GK M ρ g
  /-- 準同型性 χ(g·h)=χ(g)·χ(h)。 -/
  char_hom : ∀ g h, char (GK.mul g h) = zmodMul M.n (char g) (char h)
  /-- χ(1)=1。 -/
  char_one : char GK.one = Quot.mk (modCong M.n).rel 1
  /-- χ(g)∈(ℤ/n)^×（単元）。 -/
  char_unit : ∀ g, ∃ v, zmodMul M.n (char g) v = Quot.mk (modCong M.n).rel 1
  /-- 円分剛性: σ_g(z)=ζ^{χ(g)·log z}（作用が χ で一意決定）。 -/
  rigidity : ∀ g z, (ρ.act g).map z = M.μ.pow M.ζ (cycRigExp GK M ρ g * M.log z)

/-- **M322F-9b: 証人** — 任意の G_K 作用 ρ から円分剛性データを本物で組む。 -/
def cycRigData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    CyclotomicRigidityData GK M where
  ρ := ρ
  char := cycRigChar GK M ρ
  char_eq := fun _ => rfl
  char_hom := fun g h => cycRig_char_isHom GK M ρ g h
  char_one := cycRig_char_one GK M ρ
  char_unit := fun g => cycRig_char_unit GK M ρ g
  rigidity := fun g z => cycRig_rigidity GK M ρ g z

/-- **M322F-9c: capstone — 円分剛性データの存在**（任意の G_K・μ_n・作用に対し
    円分指標 χ_n とその準同型性・単元性・剛性が組み上がる）。 -/
theorem cycRig_exists (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    Nonempty (CyclotomicRigidityData GK M) :=
  ⟨cycRigData GK M ρ⟩

/-- **M322F-9d: capstone — 円分指標は群準同型** χ(g·h)=χ(g)·χ(h)。 -/
theorem cycRig_char_hom (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) :
    cycRigChar GK M ρ (GK.mul g h)
      = zmodMul M.n (cycRigChar GK M ρ g) (cycRigChar GK M ρ h) :=
  cycRig_char_isHom GK M ρ g h

/-- **M322F-9e: capstone — 円分剛性** σ_g(z)=ζ^{χ(g)·log z}（μ_n への作用が
    円分指標で一意に決定される）。 -/
theorem cycRig_rigidity_capstone (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (z : M.μ.carrier) :
    (ρ.act g).map z = M.μ.pow M.ζ (cycRigExp GK M ρ g * M.log z) :=
  cycRig_rigidity GK M ρ g z

/-! ## M322F-10: 実例 — 本物の絶対ガロア群 G_ℚ の μ_l 上の円分指標 -/

/-- **M322F-10b: 本物の G_K の trivial（不分岐）作用** — 任意の群 GK の μ_n への
    恒等作用（σ_g=id、σ(ζ)=ζ）。円分指標 χ≡1（不分岐点での円分指標）を与える本物の作用。 -/
def cycTrivialAction (GK : Grp) (M : CycMuGroup) : CycGKAction GK M where
  act := fun _ => { map := fun z => z, map_mul := fun _ _ => rfl }
  act_one := fun _ => rfl
  act_mul := fun _ _ _ => rfl

/-- **M322F-10c: trivial 作用の円分指標は 1**（不分岐 σ(ζ)=ζ ⟹ χ≡1）。 -/
theorem cycRig_trivial_char (GK : Grp) (M : CycMuGroup) (g : GK.carrier) :
    cycRigChar GK M (cycTrivialAction GK M) g = Quot.mk (modCong M.n).rel 1 := by
  have h : cycRigChar GK M (cycTrivialAction GK M) g
      = cycRigChar GK M (cycTrivialAction GK M) GK.one := rfl
  rw [h]
  exact cycRig_char_one GK M (cycTrivialAction GK M)

/-- **M322F-10d: trivial 族の逆系両立**（本物） — n ∣ m の推移射 zmodTrans で、
    trivial 作用の円分指標 χ_m は χ_n に落ちる（χ≡1 が逆系で両立）。pro-有限
    χ : G_K → ẑ^× の逆系両立の本物の（trivial ケースの）witness。 -/
theorem cycRig_profinite_trivial_compat (GK : Grp) {i j : Nat} (hij : i ∣ j)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (g : GK.carrier) :
    (zmodTrans hij).map
        (cycRigChar GK (cycMuStd j hj) (cycTrivialAction GK (cycMuStd j hj)) g)
      = cycRigChar GK (cycMuStd i hi) (cycTrivialAction GK (cycMuStd i hi)) g := by
  rw [cycRig_trivial_char, cycRig_trivial_char]
  rfl

/-- **M322F-10e: 本物の絶対ガロア群 G_ℚ = `algCloAbsGalois algCloTrivialTower`（M315F）の
    μ_l（ℤ/l、l≥1）上の円分指標データ**。本物の G_K の（trivial）作用から χ_l:G_ℚ→(ℤ/l)^×
    が組み上がる。IUT がエタールテータを評価する l-捻れ点 μ_l 上の円分指標の実例。
    （非自明な χ を与える実 Galois 自己同型の μ_l への降下は柱A/E 後続。） -/
def cycRigGaloisExample (l : Nat) (hl : 1 ≤ l) :
    CyclotomicRigidityData (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl) :=
  cycRigData (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))

/-- **M322F-10f: 実例の円分指標が本物の G_ℚ 上で準同型**（χ_l(g·h)=χ_l(g)·χ_l(h)）。 -/
theorem cycRig_galois_example_hom (l : Nat) (hl : 1 ≤ l)
    (g h : (algCloAbsGalois algCloTrivialTower).carrier) :
    cycRigChar (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
        (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))
        ((algCloAbsGalois algCloTrivialTower).mul g h)
      = zmodMul l
          (cycRigChar (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
            (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)) g)
          (cycRigChar (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
            (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)) h) :=
  cycRig_char_isHom (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)) g h

/-- **M322F-10g: 実例の存在**（本物の G_ℚ の μ_l 上の円分剛性データ）。 -/
theorem cycRig_galois_example_exists (l : Nat) (hl : 1 ≤ l) :
    Nonempty (CyclotomicRigidityData (algCloAbsGalois algCloTrivialTower)
      (cycMuStd l hl)) :=
  ⟨cycRigGaloisExample l hl⟩

end IUT
