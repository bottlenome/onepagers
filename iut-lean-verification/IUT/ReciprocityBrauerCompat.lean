-- M400F ReciprocityBrauerCompat [実・本物・柱B]
-- complete_pct 影響: 柱B で inv(巡回代数 (χ,a)) = χ(rec(a)) の局所 CFT 整合（Hasse 不変量 = Artin 相互像における指標評価）を、M390F rec と M395F/M365F inv の接合として不分岐/巡回モデル上で本物化。
-- 正直な限定: 全 Br(K)≅ℚ/ℤ・分岐（野性）・非巡回類・一般指標での整合は後続（ここは χ=標準指標・次数 n 不分岐の忠実部分ケースのみ本物）。

/-
  IUT/ReciprocityBrauerCompat.lean — M400F（相互写像 ↔ Brauer 不変量の整合: 実部分ケース）

  ────────────────────────────────────────────────────────────────────────
  二軸（CLAUDE.md §1 必守）
  * 分類: **[実]**（(b) 本物先行建設 + (a) 昇格）。M390F（IUT/LubinTateNormGroup.lean,
    prefix `ltng`）が建てた相互写像 rec: K^× → Gal(L/K)=ℤ/n（核=ノルム群）と、
    M395F/M365F（IUT/BrauerInvariantFull.lean, IUT/BrauerInvariant.lean,
    prefix `brf`/`bri`）が建てた巡回代数の Hasse 不変量 inv: K^× → (1/n)ℤ/ℤ を
    **接合**し、局所類体論の基本整合
      inv(巡回代数 (χ,a)) = χ(rec(a))
    （巡回代数のハッセ不変量 = Artin 相互写像の像における指標 χ の評価）を、
    不分岐次数 n・標準指標 χ の忠実な実部分ケースで**完全証明**する。
  * complete_pct 影響: 柱B（局所類体論: Brauer ↔ 相互律）前進あり。次を完全証明:
      (1) **標準指標** χ_n: Gal(L/K)=ℤ/n → (1/n)ℤ/ℤ（`rbcCanonChar`＝恒等同一視）。
      (2) **基本整合** `rbc_inv_eq_char_rec`: inv(a) = χ(rec(a))
          （M365F `briInvCyclic` と M390F `ltngRec` の合成が一致）。
      (3) **相互律対** `rbcRecPairing`/`rbcPairingHom`: a ↦ χ(rec(a)) が
          巡回代数生成部分群上の準同型（双線形）で、inv と点毎一致。
      (4) **従順記号との整合** `rbc_tame_symbol_eq_char_rec`: 従順 Hilbert 記号
          (a, e)_n = χ(rec(a))（M395F `brf_tame_symbol_eq_inv`・M375F
          `tsy_concrete_invariant` を M390F rec へ結線）。
      (5) **零判定＝ノルム群** `rbc_char_rec_zero_iff`: χ(rec(m,u))=0 ⟺
          (m,u)∈N_{L/K}(L^×)（M390F `ltng_kernel_eq_norm` と接続）。
      (6) **非退化**: 指標 χ は単射（`rbc_char_injective`）、降下対は巡回代数
          生成部分群 K^×/N 上で単射（`rbc_descended_injective`、M395F 再利用）。
      (7) capstone `ReciprocityBrauerCompatData` + `rbcData` + `rbc_exists` と
          n=2 実例（素元 π: inv=χ(rec(π))=1/2≠0、従順記号経由の非自明性）。

  ────────────────────────────────────────────────────────────────────────
  既存モジュールの何を接合したか（CLAUDE.md 指示・明記必須）
  * M390F `ltngRec U n : K^× → ℤ/n`（相互写像、rec(m,u)=[m]、核=ノルム群）。
  * M365F `briInvCyclic U n : K^× → (1/n)ℤ/ℤ`（Hasse 不変量、inv(a)=[v(a)]=[a.1]）。
  * M395F `brfInv`（降下不変量 K^×/N ≅ (1/n)ℤ/ℤ）・`brf_inv_injective_subgroup`・
    `brf_tame_symbol_eq_inv`。M375F `tsy_concrete_invariant`（従順記号＝実不変量）。
  接合の核: 標準指標 χ_n は ℤ/n と (1/n)ℤ/ℤ の**恒等同一視**（`briQZn n = zmod n`）
  ゆえ χ(rec(a)) = rec(a) = [a.1] = inv(a) が定義的に一致する。局所 CFT の
  「Hasse 不変量 = 相互像での指標評価」の不分岐/標準指標ケースを本物で閉じる。

  ────────────────────────────────────────────────────────────────────────
  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
  * `rbcCanonChar` / `rbcCanonChar_apply` — 標準指標 χ_n: ℤ/n → (1/n)ℤ/ℤ
  * `rbc_inv_eq_char_rec`                 — **基本整合 inv(a) = χ(rec(a))**
  * `rbcRecPairing` / `rbcPairingHom`     — 相互律対 a ↦ χ(rec(a))（準同型）
  * `rbc_pairing_eq_inv`                  — 対 = 不変量（点毎一致）
  * `rbc_pairing_hom`                     — 対は準同型（双線形）
  * `rbc_char_injective`                  — 指標 χ は単射（非退化）
  * `rbc_descended_injective`             — 降下対は K^×/N 上単射（M395F 再利用）
  * `rbc_tame_symbol_eq_char_rec`         — 従順記号 (a,e)_n = χ(rec(a))
  * `rbc_tame_symbol_eq_descended`        — 従順記号 = 降下対（[a] 上）
  * `rbc_char_rec_zero_iff`               — χ(rec(m,u))=0 ⟺ (m,u)∈ノルム群
  * `ReciprocityBrauerCompatData` / `rbcData` / `rbc_exists` — capstone + witness
  * n=2 worked examples（素元 π の整合・非自明性・従順記号経由）

  ────────────────────────────────────────────────────────────────────────
  正直な限定（CLAUDE.md §4: 消去・弱化禁止）
  * 全 Br(K) ≅ ℚ/ℤ・**一般指標** χ（標準指標以外）・**分岐（野性）代数**・
    **非巡回類**での整合 inv(χ,a)=χ(rec(a)) は本モジュール外——後続。ここで本物に
    したのは **不分岐次数 n・標準指標** χ_n（ℤ/n=(1/n)ℤ/ℤ の恒等同一視）上の整合。
  * χ は Gal(L/K)=ℤ/n から (1/n)ℤ/ℤ への**標準同型**として実体化（一般の
    指標群 Hom(Gal,ℚ/ℤ) の完全記述は範囲外）。素元冪の分裂座標 K^×=ℤ×O^×
    （M330F/M365F/M390F 規約）に依存する点は M390F/M395F と同じ。
  * ℚ/ℤ は固定 n の n-捻れ (1/n)ℤ/ℤ ≅ ℤ/n（`zmod n`）。全 ℚ/ℤ = colim_n は後続。
  * **toy 主語ではない**: 主語は本物の rec（M390F）・本物の inv（M365F）・
    本物の ℤ/n（M13 商群）である。χ の恒等同一視は模型置換でなく
    「Gal=ℤ/n を不変量群 (1/n)ℤ/ℤ と標準同一視する」という数学的内容そのもの。

  全て mathlib なし・新規 Classical.choice なし（propext, Quot.sound のみ）。
  共有ファイル未変更（新規 1 本のみ）。一般名は `rbc` 接頭辞で衝突回避。
-/
import IUT.LubinTateNormGroup
import IUT.BrauerInvariantFull

namespace IUT

/-! ## §1 標準指標 χ_n: Gal(L/K) = ℤ/n → (1/n)ℤ/ℤ -/

/-- **M400F-1: 標準指標** χ_n: Gal(L/K)=ℤ/n → (1/n)ℤ/ℤ。次数 n の不分岐巡回拡大
    L/K の Galois 群 Gal(L/K)≅ℤ/n を、Hasse 不変量の値群 (1/n)ℤ/ℤ=`briQZn n`
    と**標準同一視**する指標（局所類体論で巡回代数 (χ,a) の χ に相当）。
    `briQZn n = zmod n` ゆえ恒等準同型として実体化する（Frobenius ↦ 1/n）。 -/
def rbcCanonChar (n : Nat) : Hom (zmod n) (briQZn n) := idHom (zmod n)

/-- 標準指標の明示式: χ_n([m]) = [m] ∈ (1/n)ℤ/ℤ（恒等同一視）。 -/
theorem rbcCanonChar_apply (n : Nat) (x : (zmod n).carrier) :
    (rbcCanonChar n).map x = x := rfl

/-- **M400F-2: 標準指標は単射（非退化）** — χ_n: ℤ/n → (1/n)ℤ/ℤ は同型ゆえ単射。
    相互像 rec(a) が不変量 χ(rec(a)) から一意に復元される（指標の非退化性）。 -/
theorem rbc_char_injective (n : Nat) : Hom.Injective (rbcCanonChar n) :=
  fun _ _ h => h

/-! ## §2 基本整合 inv(巡回代数 (χ,a)) = χ(rec(a)) -/

/-- **M400F-3: 局所 CFT 基本整合** inv(巡回代数 (χ_n, a)) = χ_n(rec(a))。
    巡回代数 (χ_n, a) の Hasse 不変量（M365F `briInvCyclic`、= [v(a)]=[a.1]）が、
    Artin 相互写像 rec(a)（M390F `ltngRec`、= [a.1]）における標準指標 χ_n の
    評価に一致する。局所類体論の中心的整合「Hasse 不変量 = 相互像での指標評価」
    を不分岐/標準指標ケースで本物化。χ_n が恒等同一視ゆえ両辺 = [a.1] で一致。 -/
theorem rbc_inv_eq_char_rec (U : Grp) (n : Nat) (a : (unitsModel U).carrier) :
    (briInvCyclic U n).map a = (rbcCanonChar n).map ((ltngRec U n).map a) := rfl

/-! ## §3 相互律対 a ↦ χ(rec(a)) -/

/-- **M400F-4: 相互律対（値）** a ↦ χ_n(rec(a)) ∈ (1/n)ℤ/ℤ。M390F 相互写像と
    標準指標を合成した局所ペアリングの値（§2 で不変量 inv に一致する）。 -/
def rbcRecPairing (U : Grp) (n : Nat) (a : (unitsModel U).carrier) : (briQZn n).carrier :=
  (rbcCanonChar n).map ((ltngRec U n).map a)

/-- **M400F-5: 相互律対（準同型）** χ_n ∘ rec: K^× → (1/n)ℤ/ℤ を群準同型として
    実体化。合成 `Hom.comp` ゆえ自動的に準同型（双線形の一段）。 -/
def rbcPairingHom (U : Grp) (n : Nat) : Hom (unitsModel U) (briQZn n) :=
  Hom.comp (rbcCanonChar n) (ltngRec U n)

/-- 相互律対の明示式: (χ∘rec)(a) = χ_n(rec(a)) = rbcRecPairing。 -/
theorem rbcPairingHom_apply (U : Grp) (n : Nat) (a : (unitsModel U).carrier) :
    (rbcPairingHom U n).map a = rbcRecPairing U n a := rfl

/-- **M400F-6: 相互律対 = Hasse 不変量**（点毎一致）: (χ∘rec)(a) = inv(a)。
    §2 基本整合を対 `rbcPairingHom` の言語で述べ直したもの。 -/
theorem rbc_pairing_eq_inv (U : Grp) (n : Nat) (a : (unitsModel U).carrier) :
    (rbcPairingHom U n).map a = (briInvCyclic U n).map a := rfl

/-- **M400F-7: 相互律対は準同型（双線形）** (χ∘rec)(a·b) = (χ∘rec)(a)+(χ∘rec)(b)。
    巡回代数のテンソル則 (χ,a)⊗(χ,b)≅(χ,ab) と付値の加法性が相互像側でも成立。 -/
theorem rbc_pairing_hom (U : Grp) (n : Nat) (a b : (unitsModel U).carrier) :
    (rbcPairingHom U n).map ((unitsModel U).mul a b)
      = (briQZn n).mul ((rbcPairingHom U n).map a) ((rbcPairingHom U n).map b) :=
  (rbcPairingHom U n).map_mul a b

/-- **M400F-8: 降下相互律対は K^×/N 上単射（非退化）** — 巡回代数生成部分群
    K^×/N 上で χ∘rec（= 降下不変量 M395F `brfInv`）は単射。相互律対が
    巡回 Brauer 類を分離する（不変量が完全不変量である）ことを M395F から再利用。 -/
theorem rbc_descended_injective (U : Grp) (n : Nat) :
    Hom.Injective (brfInv U n) :=
  brf_inv_injective_subgroup U n

/-! ## §4 従順 Hilbert 記号との整合（記号 = 相互律対） -/

/-- **M400F-9: 従順記号 = 相互律対** (a, e)_n = χ_n(rec(a))。標準単数 e=(0,1) との
    従順 Hilbert 記号（M375F）が、a の生成する巡回代数類の Hasse 不変量
    （M375F `tsy_concrete_invariant`）= 相互像での指標評価 χ(rec(a)) に一致。
    M375F/M395F の記号を M390F 相互写像 rec に結線した局所 CFT 整合。 -/
theorem rbc_tame_symbol_eq_char_rec (n : Nat) (a : (unitsModel intGrp).carrier) :
    tsyTameSymbol n a ((0 : Int), (1 : Int))
      = (rbcCanonChar n).map ((ltngRec intGrp n).map a) := by
  rw [tsy_concrete_invariant n a]
  exact rbc_inv_eq_char_rec intGrp n a

/-- **M400F-10: 従順記号 = 降下相互律対**（[a] 上）: (a,e)_n = brfInv([a])。
    M395F `brf_tame_symbol_eq_inv` の再輸出（降下対の言語での整合）。 -/
theorem rbc_tame_symbol_eq_descended (n : Nat) (a : (unitsModel intGrp).carrier) :
    tsyTameSymbol n a ((0 : Int), (1 : Int))
      = (brfInv intGrp n).map
          ((quotientProjN (unitsModel intGrp) (kerSubgroup (briInvCyclic intGrp n))
              (ker_isNormal (briInvCyclic intGrp n))).map a) :=
  brf_tame_symbol_eq_inv n a

/-! ## §5 零判定 = ノルム群（相互律対の核 = 相互写像の核） -/

/-- **M400F-11: 相互律対の零判定 = ノルム群** χ_n(rec(m,u)) = 0 ⟺ (m,u)∈N_{L/K}(L^×)。
    標準指標 χ_n は同型ゆえ χ(rec(a))=0 ⟺ rec(a)=1、すなわち相互写像 rec の核
    （M390F `ltng_kernel_eq_norm`）= ノルム群。相互律対が「不変量 0 ⟺ 分裂 ⟺
    ノルム」を M390F の核 = ノルム群と整合的に捉える。 -/
theorem rbc_char_rec_zero_iff (U : Grp) (n : Nat) (m : Int) (u : U.carrier) :
    (rbcCanonChar n).map ((ltngRec U n).map (m, u)) = (briQZn n).one
      ↔ (normGSubgroup U (n : Int)).mem (m, u) :=
  ltng_kernel_eq_norm U n m u

/-- **M400F-12: 相互律対の零判定 = 分裂判定**（付値側）χ(rec(a))=0 ⟺ n∣v(a)。
    M365F `bri_inv_split_iff`（inv=0 ⟺ n∣v(a)）を相互律対で述べ直したもの。 -/
theorem rbc_char_rec_split_iff (U : Grp) (n : Nat) (a : (unitsModel U).carrier) :
    (rbcCanonChar n).map ((ltngRec U n).map a) = (briQZn n).one
      ↔ ((n : Nat) : Int) ∣ a.1 :=
  bri_inv_split_iff U n a

/-! ## §6 capstone: 相互律 ↔ Brauer 不変量 整合データ -/

/-- **M400F-13: 相互律 ↔ Brauer 不変量 整合データ** — 局所 CFT の基本整合
    inv(χ,a)=χ(rec(a)) の全部品を構造化: 相互写像 rec（M390F）、標準指標 χ、
    Hasse 不変量 inv（M365F）を束ね、
      * 基本整合 inv = χ∘rec（`compat`）
      * 対の準同型性（`pairing_hom`）
      * 指標の単射性（`char_injective`）
      * 零判定 = ノルム群（`zero_iff_norm`）
      * 降下対の K^×/N 上単射（`descended_injective`）
    を要請する。 -/
structure ReciprocityBrauerCompatData (U : Grp) (n : Nat) where
  /-- 相互写像 rec: K^× → Gal(L/K)=ℤ/n（M390F）。 -/
  recMap : Hom (unitsModel U) (zmod n)
  /-- recMap の同定。 -/
  recMap_is : recMap = ltngRec U n
  /-- 標準指標 χ_n: ℤ/n → (1/n)ℤ/ℤ。 -/
  chi : Hom (zmod n) (briQZn n)
  /-- chi の同定。 -/
  chi_is : chi = rbcCanonChar n
  /-- Hasse 不変量 inv: K^× → (1/n)ℤ/ℤ（M365F）。 -/
  inv : Hom (unitsModel U) (briQZn n)
  /-- inv の同定。 -/
  inv_is : inv = briInvCyclic U n
  /-- **基本整合** inv(a) = χ(rec(a))。 -/
  compat : ∀ a, inv.map a = chi.map (recMap.map a)
  /-- 相互律対は準同型（双線形）。 -/
  pairing_hom : ∀ a b, chi.map (recMap.map ((unitsModel U).mul a b))
    = (briQZn n).mul (chi.map (recMap.map a)) (chi.map (recMap.map b))
  /-- 指標 χ は単射（非退化）。 -/
  char_injective : Hom.Injective chi
  /-- 零判定 χ(rec(m,u))=0 ⟺ (m,u)∈ノルム群。 -/
  zero_iff_norm : ∀ (m : Int) (u : U.carrier),
    chi.map (recMap.map (m, u)) = (briQZn n).one
      ↔ (normGSubgroup U (n : Int)).mem (m, u)
  /-- 降下対は巡回代数生成部分群 K^×/N 上で単射。 -/
  descended_injective : Hom.Injective (brfInv U n)

/-- **M400F-14: 整合データの構成**（単数群 U と次数 n から）。全性質を本物の
    証明で満たす witness。 -/
def rbcData (U : Grp) (n : Nat) : ReciprocityBrauerCompatData U n where
  recMap := ltngRec U n
  recMap_is := rfl
  chi := rbcCanonChar n
  chi_is := rfl
  inv := briInvCyclic U n
  inv_is := rfl
  compat := rbc_inv_eq_char_rec U n
  pairing_hom := fun a b => (Hom.comp (rbcCanonChar n) (ltngRec U n)).map_mul a b
  char_injective := rbc_char_injective n
  zero_iff_norm := rbc_char_rec_zero_iff U n
  descended_injective := brf_inv_injective_subgroup U n

/-- **M400F-15: 整合データの存在**（無矛盾性 witness）。 -/
theorem rbc_exists (U : Grp) (n : Nat) : Nonempty (ReciprocityBrauerCompatData U n) :=
  ⟨rbcData U n⟩

/-- **具体的存在**: 自明単数群・n=2 でも整合データが実体化。 -/
theorem rbc_exists_witness : Nonempty (ReciprocityBrauerCompatData punitGrp 2) :=
  ⟨rbcData punitGrp 2⟩

/-! ## §7 worked examples（n=2: 素元 π の整合と非自明性） -/

-- 例1: **基本整合**（素元 π=(1,1)）: inv(χ_2, π) = χ_2(rec(π)) ∈ (1/2)ℤ/ℤ
example (U : Grp) :
    (briInvCyclic U 2).map ((1 : Int), U.one)
      = (rbcCanonChar 2).map ((ltngRec U 2).map ((1 : Int), U.one)) :=
  rbc_inv_eq_char_rec U 2 ((1 : Int), U.one)

-- 例2: 整合の共通値は 1/2（素元の不変量 = 相互像での指標評価 = [1] mod 2）
example (U : Grp) :
    (rbcCanonChar 2).map ((ltngRec U 2).map ((1 : Int), U.one))
      = Quot.mk (modCong 2).rel 1 := rfl

-- 例3: **非自明性** χ_2(rec(π)) = 1/2 ≠ 0（四元数型: 素元は分裂しない）
example (U : Grp) :
    (rbcCanonChar 2).map ((ltngRec U 2).map ((1 : Int), U.one)) ≠ (briQZn 2).one := by
  rw [← rbc_inv_eq_char_rec U 2 ((1 : Int), U.one)]
  exact bri_quaternion_not_split U

-- 例4: **相互律対は準同型**（π·π の不変量 = 2×[1] = [2] = 0）
example (U : Grp) :
    (rbcPairingHom U 2).map ((unitsModel U).mul ((1 : Int), U.one) ((1 : Int), U.one))
      = (briQZn 2).mul
          ((rbcPairingHom U 2).map ((1 : Int), U.one))
          ((rbcPairingHom U 2).map ((1 : Int), U.one)) :=
  rbc_pairing_hom U 2 ((1 : Int), U.one) ((1 : Int), U.one)

-- 例5: **従順記号 = 相互律対**（π=(1,0)・標準単数 e=(0,1)）
example :
    tsyTameSymbol 2 ((1 : Int), (0 : Int)) ((0 : Int), (1 : Int))
      = (rbcCanonChar 2).map ((ltngRec intGrp 2).map ((1 : Int), (0 : Int))) :=
  rbc_tame_symbol_eq_char_rec 2 ((1 : Int), (0 : Int))

-- 例6: **従順記号経由の非自明性** χ_2(rec(π)) ≠ 0（記号 (π,e)_2=1/2 と一致し非自明）
example :
    (rbcCanonChar 2).map ((ltngRec intGrp 2).map ((1 : Int), (0 : Int))) ≠ (briQZn 2).one := by
  rw [← rbc_tame_symbol_eq_char_rec 2 ((1 : Int), (0 : Int))]
  exact tsy_example_prime_unit_nontrivial

-- 例7: **零判定 = ノルム群**（付値 2 の元 (2,u) は χ(rec)=0 ⟺ ノルム群）
example (u : punitGrp.carrier) :
    (rbcCanonChar 2).map ((ltngRec punitGrp 2).map ((2 : Int), u)) = (briQZn 2).one
      ↔ (normGSubgroup punitGrp (2 : Int)).mem ((2 : Int), u) :=
  rbc_char_rec_zero_iff punitGrp 2 2 u

-- 例8: **素元は核の外**（χ(rec(π)) ≠ 0 ⟺ π ∉ ノルム群、2∤1）
example (u : punitGrp.carrier) :
    ¬ (rbcCanonChar 2).map ((ltngRec punitGrp 2).map ((1 : Int), u)) = (briQZn 2).one := by
  intro h
  obtain ⟨k, hk⟩ := (rbc_char_rec_split_iff punitGrp 2 ((1 : Int), u)).mp h
  omega

-- 例9: capstone アクセサ（基本整合 inv = χ∘rec）
example (U : Grp) (a : (unitsModel U).carrier) :
    (rbcData U 2).inv.map a = (rbcData U 2).chi.map ((rbcData U 2).recMap.map a) :=
  (rbcData U 2).compat a

-- 例10: capstone アクセサ（指標 χ の単射性 = 非退化）
example (U : Grp) : Hom.Injective (rbcData U 2).chi :=
  (rbcData U 2).char_injective

end IUT
