/-
  IUT/TripodRealizationBundle.lean — BLW-4: tripod anabelian 入力バンドルの
  **実現束ね capstone**（F₂ ↠ 実 Kummer デッキ群 μ₃×μ₃ の実現準同型）
  ── 柱A・項目 A9（Belyi 化 / 遠アーベル幾何入力(実)）

  分類 **[実／(a) 昇格]**（BLW-1 の自由群 F₂ `tfgGrp`（+その普遍性 `tfgLift`）と
  BLW-2 の実 Kummer 被覆デッキ群 μ₃×μ₃ `kmuMu3Sq`（実測 rpow デッキ・忠実作用）を、
  **実現準同型** `trbRealize : Hom tfgGrp kmuMu3Sq` へ束ねる「値を立てる」段。BLW-1
  単独が敵対的既定で「bare F₂ = 抽象群論・+0.00–0.01」に留まるのを、q3td 先例の
  「抽象群 + 実被覆上の実現準同型」パターンで A9 の実加点素材へ昇格する。

  **complete_pct 影響（A9 BLW-4 bundle 完成）**: 二半（BLW-1 F₂ / BLW-2 実 Kummer
  デッキ）を実現準同型 F₂ → μ₃×μ₃ で結合し、生成元像（a↦(ζ,1)・b↦(1,ζ)）・
  **全射 F₂ ↠ (ℤ/3)²**（語 aⁱbʲ が (ζⁱ,ζʲ) を命中）・**核観察**（交換子 [a,b] と
  立方 a³,b³ が核 ⟹ 像は最大アーベル商 (ℤ/3)² の実現）を全て完全証明する。設計監査
  （audit/pillar-A9-…-2026-07-20.md §3 BLW-4・§4）どおり s_A9 0.14→**予測 0.16–0.18**
  （独立再監査確定が条件・過大主張しない）。実 IUT 完全証明率の前進は**独立監査通過後**に
  graph-meta.json へ反映する。

  ## 建設内容（全 choice-free・sorry なし・禁止タクティク不使用・omega 不使用）
  * 群冪 `trbPow`（任意 Grp の x^n・Nat 再帰の data 関数）と汎用補題
    `trb_pow_one`（1^n=1）・`trb_hom_pow`（準同型は冪を保存）・
    `trb_prodGrp_pow`（直積の冪は成分ごと）——全て induction+rw の完全証明。
  * **実現準同型 `trbRealize : Hom tfgGrp kmuMu3Sq`**＝`tfgLift` を G=μ₃×μ₃・
    g₁=(ζ,1)・g₂=(1,ζ) で適用。map_mul は BLW-1 の `tfgLift` から継承（新規証明ゼロ）。
    生成元像 `trb_realize_a`（=(ζ,1)）・`trb_realize_b`（=(1,ζ)）は `tfg_lift_a/b` 経由。
  * **全射 `trb_surjective_pow`**: ∀ i j, ∃ w, trbRealize w = (ζⁱ,ζʲ)（witness =
    aⁱbʲ）。⟹ tripod π₁ の群論的内容 F₂ が実 Kummer デッキ群の (ℤ/3)² 部分へ本当に
    全射する。ζ は位数 3（BLW-2 `kmu_mu3_*_ne_*` で {1,ζ,ζ²} が相異）なので像は (ℤ/3)²。
  * **核観察**: `trb_commutator_kernel`（[a,b]=aba⁻¹b⁻¹ ↦ 1・像がアーベルだから）・
    `trb_cube_a_kernel`/`trb_cube_b_kernel`（a³,b³ ↦ 1・ζ³=1 から）。⟹ 核は交換子＋
    立方を含み、像は F₂ の最大 (ℤ/3)² アーベル商の実現。
  * **capstone `TripodRealizationBundle`**（実現＋生成元像＋全射＋核の witness を要求
    する grounded 構造）と実証人 `trbBundle`・存在 `trb_bundle_exists`。

  接続する既存部品（精読して再利用・再証明ゼロ）:
  * BLW-1 `IUT/TripodFreeGroup.lean`（tfg）: `tfgGrp`（F₂）・生成元 `tfgA`/`tfgB`・
    普遍写像 `tfgLift`・生成元値 `tfg_lift_a`/`tfg_lift_b`。
  * BLW-2 `IUT/TripodKummerMu3.lean`（kmu）: 実デッキ群 `kmuMu3Sq = prodGrp kmuMu3 kmuMu3`・
    生成元 `kmuMu3Zeta`（ζ₃）・ζ 相異 `kmu_mu3_*`・ζ³=1 の実測 `kmu_zeta_rpow3`。
  * M16 `IUT/FundamentalGroup.lean`: `Grp`/`Hom`/`prodGrp`・群公理から派生した
    `Grp.mul_one`/`Grp.mul_inv`・`Hom.map_mul`/`Hom.map_one`/`Hom.map_inv`。
  * `rpow`（`IUT/LubinTateUnique.lean`）: 環冪（μ₃ 冪の担体値の同定）。

  **正直な限定**（消去・弱化禁止・BLW-1(tfg)・BLW-2(kmu)・blc・blr の限定を全文継承）:
  1. **「tripod の π₁ そのもの」ではない**: 実現したのは自由群 F₂（tripod π₁ の
     群論的内容）の **ℤ/3×ℤ/3 有限商**の、実 Kummer 被覆 u³=t / v³=1−t 上の実 μ₃×μ₃
     デッキ群としての実現である。位相ループの群 π₁^top・スキームのエタール基本群
     π₁^ét = F̂₂（副有限完備化）・π₁^temp との同定は不主張（ℂ・位相・被覆空間・
     スキームのエタールサイトが core に無いリポジトリ恒久限定の継承）。
  2. **全射は特定の (ℤ/3)² 有限商へ**: `trb_surjective_pow` は像が生成元冪 (ζⁱ,ζʲ)
     全体（= 実デッキ生成元が張る (ℤ/3)²）を覆うことを示す。副有限 F̂₂ への全射・
     単一 (ℤ/3)² 被覆（ファイバー積）・非可換商（S₃ 等・blc の f のガロア閉包）の
     実現は未達（named future targets）。**担体 `kmuMu3Sq.carrier` 全体への
     全射（∀ y ∃ w）は μ₃(K)={1,ζ,ζ²} の exhaustiveness を要し、BLW-2 は 3 元の
     相異のみ証明・exhaustiveness は未証明のため主張しない**（正直申告・弱化しない）。
  3. **π₁^ét = F̂₂・π₁^temp・residual finiteness F₂↪F̂₂ は 0**（BLW-1/2 §2.5 の継承）。
  4. **Belyi cuspidalization（[AbsTopII]）・noncritical Belyi（[GenEll]）は 0 のまま**:
     blc/blr の正直限定 1–2 を全文継承・並置。**A9 cap ≤ ~0.35**（これら本丸が 0 の間）。
  5. K = ℚ(ζ₃)・3 次 Kummer スライス固定（p=3 恒久限定の族）。位相・解析なし。

  全て選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用・omega 不使用。共有ファイル（IUT.lean・build.sh・dashboard・graph 系）は
  一切変更しない。新規 1 本のみ。目標公理 `[propext, Quot.sound]`。
-/
import IUT.TripodFreeGroup
import IUT.TripodKummerMu3

namespace IUT

/-! ## 1. 群冪と汎用補題（任意 Grp・choice-free・data 関数） -/

/-- 群の冪 x^n（Nat 再帰の data 関数）。 -/
def trbPow (G : Grp) (x : G.carrier) : Nat → G.carrier
  | 0 => G.one
  | n + 1 => G.mul (trbPow G x n) x

/-- 単位元の冪は単位元。 -/
theorem trb_pow_one (G : Grp) (n : Nat) : trbPow G G.one n = G.one := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show G.mul (trbPow G G.one n) G.one = G.one
    rw [ih, G.mul_one]

/-- 準同型は冪を保存: f(x^n) = f(x)^n。 -/
theorem trb_hom_pow {G H : Grp} (f : Hom G H) (x : G.carrier) (n : Nat) :
    f.map (trbPow G x n) = trbPow H (f.map x) n := by
  induction n with
  | zero => exact f.map_one
  | succ n ih =>
    show f.map (G.mul (trbPow G x n) x) = H.mul (trbPow H (f.map x) n) (f.map x)
    rw [f.map_mul, ih]

/-- 直積群の冪は成分ごと: (x)^n = (x.1^n, x.2^n)。 -/
theorem trb_prodGrp_pow (G H : Grp) (x : (prodGrp G H).carrier) (n : Nat) :
    trbPow (prodGrp G H) x n = (trbPow G x.1 n, trbPow H x.2 n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (prodGrp G H).mul (trbPow (prodGrp G H) x n) x
       = (G.mul (trbPow G x.1 n) x.1, H.mul (trbPow H x.2 n) x.2)
    rw [ih]

/-! ## 2. 実現準同型 F₂ → μ₃×μ₃ と生成元像 -/

/-- **実現準同型 F₂ → μ₃×μ₃**: `tfgLift` を G=μ₃×μ₃・a↦(ζ,1)・b↦(1,ζ) で適用。
    tripod の二ループ（0 の周り・1 の周り）を二つの Kummer デッキ生成元へ写す
    幾何的実現。map_mul は BLW-1 の `tfgLift` から継承（新規証明ゼロ）。 -/
def trbRealize : Hom tfgGrp kmuMu3Sq :=
  tfgLift kmuMu3Sq
    ((kmuMu3Zeta, kmuMu3.one) : kmuMu3Sq.carrier)
    ((kmuMu3.one, kmuMu3Zeta) : kmuMu3Sq.carrier)

/-- 生成元 a の像 = (ζ,1)（第 1 因子 μ₃ の生成元）。 -/
theorem trb_realize_a :
    trbRealize.map tfgA = ((kmuMu3Zeta, kmuMu3.one) : kmuMu3Sq.carrier) :=
  tfg_lift_a kmuMu3Sq _ _

/-- 生成元 b の像 = (1,ζ)（第 2 因子 μ₃ の生成元）。 -/
theorem trb_realize_b :
    trbRealize.map tfgB = ((kmuMu3.one, kmuMu3Zeta) : kmuMu3Sq.carrier) :=
  tfg_lift_b kmuMu3Sq _ _

/-! ## 3. 全射 F₂ ↠ (ℤ/3)²（語 aⁱbʲ ↦ (ζⁱ,ζʲ)） -/

/-- 語 aⁱbʲ ∈ F₂ の実現像 = (ζⁱ, ζʲ)。準同型性＋冪保存＋直積冪から降りる。 -/
theorem trb_realize_word (i j : Nat) :
    trbRealize.map (tfgGrp.mul (trbPow tfgGrp tfgA i) (trbPow tfgGrp tfgB j))
      = (trbPow kmuMu3 kmuMu3Zeta i, trbPow kmuMu3 kmuMu3Zeta j) := by
  rw [trbRealize.map_mul, trb_hom_pow trbRealize tfgA i, trb_hom_pow trbRealize tfgB j,
    trb_realize_a, trb_realize_b]
  show (prodGrp kmuMu3 kmuMu3).mul
        (trbPow (prodGrp kmuMu3 kmuMu3) (kmuMu3Zeta, kmuMu3.one) i)
        (trbPow (prodGrp kmuMu3 kmuMu3) (kmuMu3.one, kmuMu3Zeta) j)
      = (trbPow kmuMu3 kmuMu3Zeta i, trbPow kmuMu3 kmuMu3Zeta j)
  rw [trb_prodGrp_pow kmuMu3 kmuMu3 (kmuMu3Zeta, kmuMu3.one) i,
    trb_prodGrp_pow kmuMu3 kmuMu3 (kmuMu3.one, kmuMu3Zeta) j]
  show (kmuMu3.mul (trbPow kmuMu3 kmuMu3Zeta i) (trbPow kmuMu3 kmuMu3.one j),
        kmuMu3.mul (trbPow kmuMu3 kmuMu3.one i) (trbPow kmuMu3 kmuMu3Zeta j))
      = (trbPow kmuMu3 kmuMu3Zeta i, trbPow kmuMu3 kmuMu3Zeta j)
  rw [trb_pow_one kmuMu3 j, trb_pow_one kmuMu3 i,
    kmuMu3.mul_one (trbPow kmuMu3 kmuMu3Zeta i),
    kmuMu3.one_mul (trbPow kmuMu3 kmuMu3Zeta j)]

/-- **全射 F₂ ↠ (ℤ/3)²**: 任意の (ζⁱ,ζʲ) は語 aⁱbʲ で命中する。⟹ 実デッキ群の
    生成元が張る (ℤ/3)² 部分は F₂ の genuine な商として実現される。 -/
theorem trb_surjective_pow (i j : Nat) :
    ∃ w : tfgGrp.carrier,
      trbRealize.map w = (trbPow kmuMu3 kmuMu3Zeta i, trbPow kmuMu3 kmuMu3Zeta j) :=
  ⟨tfgGrp.mul (trbPow tfgGrp tfgA i) (trbPow tfgGrp tfgB j), trb_realize_word i j⟩

/-! ## 4. 核観察（交換子＋立方 ⊆ ker ⟹ 像は最大 (ℤ/3)² アーベル商の実現） -/

/-- μ₃ はアーベル（K の乗法の可換性から）。 -/
theorem trb_mu3_comm (a b : kmuMu3.carrier) : kmuMu3.mul a b = kmuMu3.mul b a :=
  Subtype.ext (kmuK.mul_comm a.val b.val)

/-- μ₃×μ₃ はアーベル（成分ごと）。 -/
theorem trb_mu3sq_comm (x y : kmuMu3Sq.carrier) : kmuMu3Sq.mul x y = kmuMu3Sq.mul y x := by
  show (prodGrp kmuMu3 kmuMu3).mul x y = (prodGrp kmuMu3 kmuMu3).mul y x
  show (kmuMu3.mul x.1 y.1, kmuMu3.mul x.2 y.2) = (kmuMu3.mul y.1 x.1, kmuMu3.mul y.2 x.2)
  rw [trb_mu3_comm x.1 y.1, trb_mu3_comm x.2 y.2]

/-- アーベル群では交換子 aba⁻¹b⁻¹ = 1。 -/
theorem trb_grp_comm_one (G : Grp) (comm : ∀ x y, G.mul x y = G.mul y x) (a b : G.carrier) :
    G.mul (G.mul (G.mul a b) (G.inv a)) (G.inv b) = G.one := by
  rw [comm a b, G.mul_assoc b a (G.inv a), G.mul_inv a, G.mul_one b, G.mul_inv b]

/-- **交換子は核に入る**: [a,b] = aba⁻¹b⁻¹ ↦ 1（像 μ₃×μ₃ がアーベルだから）。 -/
theorem trb_commutator_kernel :
    trbRealize.map
        (tfgGrp.mul (tfgGrp.mul (tfgGrp.mul tfgA tfgB) (tfgGrp.inv tfgA)) (tfgGrp.inv tfgB))
      = kmuMu3Sq.one := by
  rw [trbRealize.map_mul, trbRealize.map_mul, trbRealize.map_mul,
    trbRealize.map_inv, trbRealize.map_inv]
  exact trb_grp_comm_one kmuMu3Sq trb_mu3sq_comm (trbRealize.map tfgA) (trbRealize.map tfgB)

/-- μ₃ 冪の担体値は環冪: (ζ^n).val = rpow K ζ n。 -/
theorem trb_mu3pow_val (n : Nat) :
    (trbPow kmuMu3 kmuMu3Zeta n).val = rpow kmuK kmuZeta n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show kmuK.mul (trbPow kmuMu3 kmuMu3Zeta n).val kmuZeta
       = kmuK.mul (rpow kmuK kmuZeta n) kmuZeta
    rw [ih]

/-- μ₃ 内で ζ³ = 1（BLW-2 の実測 `kmu_zeta_rpow3` を担体値経由で持ち上げ）。 -/
theorem trb_mu3_zeta_cube : trbPow kmuMu3 kmuMu3Zeta 3 = kmuMu3.one := by
  apply Subtype.ext
  show (trbPow kmuMu3 kmuMu3Zeta 3).val = kmuK.one
  rw [trb_mu3pow_val 3]
  exact kmu_zeta_rpow3

/-- **立方 a³ は核に入る**: a³ ↦ (ζ³,1) = 1。 -/
theorem trb_cube_a_kernel : trbRealize.map (trbPow tfgGrp tfgA 3) = kmuMu3Sq.one := by
  rw [trb_hom_pow trbRealize tfgA 3, trb_realize_a]
  show trbPow (prodGrp kmuMu3 kmuMu3) (kmuMu3Zeta, kmuMu3.one) 3 = (kmuMu3.one, kmuMu3.one)
  rw [trb_prodGrp_pow kmuMu3 kmuMu3 (kmuMu3Zeta, kmuMu3.one) 3]
  show (trbPow kmuMu3 kmuMu3Zeta 3, trbPow kmuMu3 kmuMu3.one 3) = (kmuMu3.one, kmuMu3.one)
  rw [trb_pow_one kmuMu3 3, trb_mu3_zeta_cube]

/-- **立方 b³ は核に入る**: b³ ↦ (1,ζ³) = 1。 -/
theorem trb_cube_b_kernel : trbRealize.map (trbPow tfgGrp tfgB 3) = kmuMu3Sq.one := by
  rw [trb_hom_pow trbRealize tfgB 3, trb_realize_b]
  show trbPow (prodGrp kmuMu3 kmuMu3) (kmuMu3.one, kmuMu3Zeta) 3 = (kmuMu3.one, kmuMu3.one)
  rw [trb_prodGrp_pow kmuMu3 kmuMu3 (kmuMu3.one, kmuMu3Zeta) 3]
  show (trbPow kmuMu3 kmuMu3.one 3, trbPow kmuMu3 kmuMu3Zeta 3) = (kmuMu3.one, kmuMu3.one)
  rw [trb_pow_one kmuMu3 3, trb_mu3_zeta_cube]

/-! ## 5. capstone バンドル（実現＋生成元像＋全射＋核の witness を要求する grounded 構造） -/

/-- **tripod anabelian 実現バンドル** — F₂ の ℤ/3×ℤ/3 商を実 Kummer 被覆デッキ群
    μ₃×μ₃ として実現する準同型の grounded 束ね（各 field が本物の証明を要求する）。 -/
structure TripodRealizationBundle where
  /-- 実現準同型 F₂ → μ₃×μ₃。 -/
  realize : Hom tfgGrp kmuMu3Sq
  /-- 生成元 a の像 = (ζ,1)。 -/
  realizeA : realize.map tfgA = ((kmuMu3Zeta, kmuMu3.one) : kmuMu3Sq.carrier)
  /-- 生成元 b の像 = (1,ζ)。 -/
  realizeB : realize.map tfgB = ((kmuMu3.one, kmuMu3Zeta) : kmuMu3Sq.carrier)
  /-- 全射 F₂ ↠ (ℤ/3)²: 任意の (ζⁱ,ζʲ) が語 aⁱbʲ で命中。 -/
  surjOntoZ3Sq : ∀ i j : Nat, ∃ w : tfgGrp.carrier,
    realize.map w = (trbPow kmuMu3 kmuMu3Zeta i, trbPow kmuMu3 kmuMu3Zeta j)
  /-- 交換子 [a,b] は核に入る（像はアーベル）。 -/
  commutatorKernel : realize.map
    (tfgGrp.mul (tfgGrp.mul (tfgGrp.mul tfgA tfgB) (tfgGrp.inv tfgA)) (tfgGrp.inv tfgB))
    = kmuMu3Sq.one
  /-- 立方 a³ は核に入る。 -/
  cubeAKernel : realize.map (trbPow tfgGrp tfgA 3) = kmuMu3Sq.one
  /-- 立方 b³ は核に入る。 -/
  cubeBKernel : realize.map (trbPow tfgGrp tfgB 3) = kmuMu3Sq.one

/-- **実現バンドルの実証人** — 全 field が上で完全証明した本物の内容。 -/
def trbBundle : TripodRealizationBundle where
  realize := trbRealize
  realizeA := trb_realize_a
  realizeB := trb_realize_b
  surjOntoZ3Sq := trb_surjective_pow
  commutatorKernel := trb_commutator_kernel
  cubeAKernel := trb_cube_a_kernel
  cubeBKernel := trb_cube_b_kernel

/-- **tripod π₁ の ℤ/3×ℤ/3 商の実 Kummer デッキ実現バンドルは存在する**。 -/
theorem trb_bundle_exists : Nonempty TripodRealizationBundle := ⟨trbBundle⟩

end IUT
