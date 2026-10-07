/-
  # M157F: 階乗塔の GaloisTower 実構成 — ẑ 型 pro-対象の圏論版（柱A A-1 最終段）

  M24 (ProObject) の正直申告「ガロア閉包＝塔の存在は未形式化の入力
  （塔は構造体データ）」を**非自明な実構成で解消**する。G := ℤ
  （テータ被覆のデッキ群 `intGrp`、M9）に対し、部分群の鎖
  H_n := (n!)ℤ と剰余類対象 A n := ℤ/(n!) が
  `GaloisTower (gsetGaloisData intGrp)` の全フィールドを満たすことを
  構成する — ẑ = lim ℤ/n の pro-対象実現の圏論版である。

  * M157F-1 `natFact` / `natFact_pos` / `natFact_le_divides` — 階乗と
    その単調な整除性 n! ∣ m! (n ≤ m)（Nat.le の導出への帰納）
  * M157F-2 `intMulSubgroup` — 部分群 dℤ ⊆ ℤ（倍数の閉性、witness 明示）
  * M157F-3 `intSub_le` — 包含 (m!)ℤ ⊆ (n!)ℤ (n ≤ m)（整除性のキャスト
    持ち上げ + 結合則）
  * M157F-4 `cosetMapOfLe` / `factTowerHom` — **塔の射**: 包含
    H ⊆ K からの剰余類間同変射 G/H → G/K（M148F `coreToCoset` の
    Quot.lift パターンの一般包含版）と、その階乗鎖への適用
    ℤ/(j!) → ℤ/(i!) (i ≤ j)
  * M157F-5 `subgroup_ext` / `abelian_core_eq` — **可換群では
    core(H) = H**: mem の funext + propext から Subgroup 自体の等式
    （Prop フィールドは proof irrelevance で自動）。M154F の
    `cosetGSet_core_galois` を core を経由せず直接使うための鍵
  * M157F-6 `intCoset_galois` — **ガロア性**: ℤ は可換なので
    core((d)ℤ) = (d)ℤ、よって M154F-6b の G/core(H) の抽象 IsGalois が
    そのまま ℤ/(d) の IsGalois になる（`rw` 一発）
  * M157F-7 `factorialTower` — **本丸**: 階乗塔が
    `GaloisTower (gsetGaloisData intGrp)` の全フィールド
    （対象・基点・ガロア性・射・恒等/合成/基点の整合）を満たす
  * M157F-8 `galoisTower_inhabited_nontrivial` /
    `factTower_fiber_nontrivial` — **見出し**: 非自明なガロア塔の存在。
    M24-5 の `unitAction` 自明塔（全対象が一点）と違い、本塔の対象
    ℤ/(n!) は成長する: A 2 = ℤ/2 のファイバーで [0] ≠ [1]
    （`quot_exact_of_equiv` による Quot 分離、2 ∤ 1）
  * M157F-9 `FactorialTowerData` / `factorialTowerWitness` /
    `factorialTower_exists` — 総括データ・証人・存在定理

  **意義**: M24 の「塔は構造体データ（未形式化の入力）」を非自明な
  実構成で解消。M148F（閉包）→ M154F（抽象 IsGalois）→ 本層（塔）で
  柱A A-1 が完結。π₁(塔) = lim Aut は M24 の機構
  （`towerSystem` / `pi1Tower`）がそのまま適用される。

  **正直な申告**: (1) `gsetGaloisData G`（M21-8）は G6 フィールドに
  Classical.choice を含むため、型がそれに言及する宣言
  （M157F-6〜9）は公理リストに Classical.choice を**型経由で継承**する
  （M149F `gset_satisfies_quotient`・M154F と同じ事情）。本モジュールの
  証明自体は choice を一切使用しない。(2) 塔から π₁ を取り出す
  `transAut` の ∃! → 関数化が Classical.choice を使うのは M24 既存の
  申告どおり（本層は塔データの構成のみで、そこには choice はない）。

  全て選択公理不使用（型継承を除く）。サブエージェント並行部品。
-/
import IUT.CosetGalois
import IUT.ProObject

namespace IUT

/-! ## M157F-1: 階乗とその整除性 -/

/-- **階乗**（M157F-1a）: core Lean に factorial が無いため自前定義。 -/
def natFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFact n

/-- **補題 (M157F-1b): 階乗は正**（帰納 + 積の正値性）。 -/
theorem natFact_pos (n : Nat) : 0 < natFact n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    show 0 < (k + 1) * natFact k
    exact Nat.mul_pos (Nat.succ_pos k) ih

/-- **補題 (M157F-1c): 階乗の整除性** — i ≤ j なら i! ∣ j!
    （witness 明示の ∃ 形。`Nat.le` の導出そのものへの帰納:
    refl は k = 1、step は k を (m+1) 倍する）。 -/
theorem natFact_le_divides {i j : Nat} (h : i ≤ j) :
    ∃ k : Nat, natFact j = natFact i * k := by
  induction h with
  | refl => exact ⟨1, (Nat.mul_one (natFact i)).symm⟩
  | @step m _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k * (m + 1), ?_⟩
    show (m + 1) * natFact m = natFact i * (k * (m + 1))
    rw [hk, Nat.mul_comm (m + 1) (natFact i * k), Nat.mul_assoc]

/-! ## M157F-2: 部分群 dℤ ⊆ ℤ -/

/-- **部分群 dℤ**（M157F-2）: デッキ群 ℤ（`intGrp`、加法群）の
    d の倍数のなす部分群。mem は witness 明示の ∃ 形
    （core の Dvd API への依存を避ける）。閉性は分配則・符号則の
    書き換えのみ。 -/
def intMulSubgroup (d : Nat) : Subgroup intGrp where
  mem := fun x => ∃ c : Int, x = (d : Int) * c
  one_mem := ⟨0, (Int.mul_zero (d : Int)).symm⟩
  mul_mem := fun {a b} ha hb => by
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    show a + b = (d : Int) * (m + n)
    rw [hm, hn, Int.mul_add]
  inv_mem := fun {a} ha => by
    obtain ⟨m, hm⟩ := ha
    refine ⟨-m, ?_⟩
    show -a = (d : Int) * (-m)
    rw [hm, Int.mul_neg]

/-! ## M157F-3: 包含 (j!)ℤ ⊆ (i!)ℤ (i ≤ j) -/

/-- **定理 (M157F-3): 階乗部分群の鎖は逆向きに包含** — i ≤ j なら
    (j!)ℤ ⊆ (i!)ℤ（i! ∣ j! の witness を Int にキャストして結合）。 -/
theorem intSub_le {i j : Nat} (h : i ≤ j) :
    ∀ g, (intMulSubgroup (natFact j)).mem g →
      (intMulSubgroup (natFact i)).mem g := by
  intro g hg
  obtain ⟨c, hc⟩ := hg
  obtain ⟨k, hk⟩ := natFact_le_divides h
  refine ⟨(k : Int) * c, ?_⟩
  rw [hc, hk, Int.natCast_mul, Int.mul_assoc]

/-! ## M157F-4: 塔の射（包含からの剰余類間射） -/

/-- **剰余類間の同変射 (M157F-4a)**: 部分群の包含 H ⊆ K から
    G/H → G/K（M148F `coreToCoset` の Quot.lift パターンの一般包含版。
    cosetRel の細分性で well-defined、同変性は代表元上 rfl）。 -/
def cosetMapOfLe (G : Grp) {H K : Subgroup G}
    (hHK : ∀ g, H.mem g → K.mem g) :
    ActHom (cosetAction G H) (cosetAction G K) where
  map := Quot.lift (fun a => Quot.mk (cosetRel G K) a)
    (fun _ _ hab => Quot.sound (hHK _ hab))
  equivariant := by
    intro g x
    induction x using Quot.ind
    rfl

/-- **塔の射 (M157F-4b)**: ℤ/(j!) → ℤ/(i!) (i ≤ j) を `GSetCat` の
    射として実現（M157F-3 の包含に M157F-4a を適用）。 -/
def factTowerHom {i j : Nat} (h : i ≤ j) :
    (GSetCat intGrp).Hom (cosetGSet intGrp (intMulSubgroup (natFact j)))
      (cosetGSet intGrp (intMulSubgroup (natFact i))) :=
  cosetMapOfLe intGrp (intSub_le h)

/-! ## M157F-5: 可換群では core(H) = H -/

/-- **Subgroup の外延性 (M157F-5a)**: mem が一致すれば部分群として
    等しい（mem の funext + propext。Prop 値の閉性フィールドは
    proof irrelevance で自動）。 -/
theorem subgroup_ext {G : Grp} {H K : Subgroup G}
    (h : ∀ g, H.mem g ↔ K.mem g) : H = K := by
  cases H with | mk hmem h1 h2 h3 =>
  cases K with | mk kmem k1 k2 k3 =>
  have hm : hmem = kmem := funext (fun g => propext (h g))
  subst hm
  rfl

/-- **定理 (M157F-5b): 可換群では core(H) = H** — core ⊆ H は
    M148F-2、逆は可換性で共役 a⁻¹ga = g に潰れる。Subgroup 自体の
    等式（M157F-5a）なので `rw` で剰余類対象を書き換えられる。 -/
theorem abelian_core_eq (G : Grp)
    (hab : ∀ a b, G.mul a b = G.mul b a) (H : Subgroup G) :
    coreSubgroup G H = H := by
  apply subgroup_ext
  intro g
  constructor
  · exact core_le G H g
  · intro hg a
    have e : G.mul (G.mul (G.inv a) g) a = g := by
      rw [hab (G.mul (G.inv a) g) a, ← G.mul_assoc, G.mul_inv, G.one_mul]
    rw [e]
    exact hg

/-- デッキ群 ℤ は可換（加法の可換性）。 -/
theorem intGrp_comm : ∀ a b : intGrp.carrier,
    intGrp.mul a b = intGrp.mul b a :=
  fun a b => Int.add_comm a b

/-! ## M157F-6: 各層のガロア性 -/

/-- **定理 (M157F-6): ℤ/(d) は抽象 IsGalois** — ℤ は可換なので
    core((d)ℤ) = (d)ℤ（M157F-5b）、よって M154F-6b の
    「G/core(H) は IsGalois」がそのまま ℤ/(d) に転写される。
    **注**: 型が `gsetGaloisData`（G6 に Classical.choice）に言及する
    ため公理リストに choice を継承するが、本証明は choice 不使用。 -/
theorem intCoset_galois (d : Nat) :
    (gsetGaloisData intGrp).IsGalois
      (cosetGSet intGrp (intMulSubgroup d)) := by
  have h := cosetGSet_core_galois intGrp (intMulSubgroup d)
  rw [abelian_core_eq intGrp intGrp_comm (intMulSubgroup d)] at h
  exact h

/-! ## M157F-7: 本丸 — 階乗塔は GaloisTower -/

/-- **本丸 (M157F-7): 階乗塔** — A n := ℤ/(n!)、基点 [0]、
    ガロア性 = M157F-6、射 = M157F-4b が
    `GaloisTower (gsetGaloisData intGrp)`（M24-4a）の全フィールドを
    満たす。恒等・合成・基点の整合は代表元上 rfl（Quot.ind +
    `ActHom.ext`）。ẑ = lim ℤ/n の pro-対象実現の圏論版。 -/
def factorialTower : GaloisTower (gsetGaloisData intGrp) where
  A := fun n => cosetGSet intGrp (intMulSubgroup (natFact n))
  pt := fun n =>
    Quot.mk (cosetRel intGrp (intMulSubgroup (natFact n))) intGrp.one
  hGal := fun n => intCoset_galois (natFact n)
  P := fun {i j} h => factTowerHom h
  P_self := fun i h => by
    apply ActHom.ext
    intro x
    induction x using Quot.ind
    rfl
  P_comp := fun {i j k} hij hjk => by
    apply ActHom.ext
    intro x
    induction x using Quot.ind
    rfl
  P_pt := fun {i j} h => rfl

/-! ## M157F-8: 見出し — 非自明なガロア塔の存在 -/

/-- **定理 (M157F-8a): 非自明なガロア塔の存在**（見出し）。
    M24-5 `galoisTower_consistent` の自明塔（自明群上・全対象一点）と
    違い、本塔は無限群 ℤ 上で対象 ℤ/(n!) が成長する非自明な塔である
    （非自明性の witness は M157F-8b）。π₁(塔) = lim Aut(ℤ/(n!)) は
    M24 の `towerSystem` / `pi1Tower` がそのまま適用される。 -/
theorem galoisTower_inhabited_nontrivial :
    Nonempty (GaloisTower (gsetGaloisData intGrp)) :=
  ⟨factorialTower⟩

/-- **定理 (M157F-8b): 塔の非自明性** — 第 2 層 A 2 = ℤ/2! = ℤ/2 の
    ファイバーは [0] ≠ [1] の 2 元を分離する（Quot の分離は
    `quot_exact_of_equiv`（M16）、2 ∤ 1 は omega）。自明塔では
    全ファイバーが一点なので、これが「実構成」の証拠。 -/
theorem factTower_fiber_nontrivial :
    Quot.mk (cosetRel intGrp (intMulSubgroup (natFact 2))) (0 : Int)
      ≠ Quot.mk (cosetRel intGrp (intMulSubgroup (natFact 2))) (1 : Int) := by
  intro hq
  have h2 := quot_exact_of_equiv
    (cosetRel intGrp (intMulSubgroup (natFact 2)))
    (cosetRel_refl intGrp (intMulSubgroup (natFact 2)))
    (fun hab => cosetRel_symm intGrp (intMulSubgroup (natFact 2)) hab)
    (fun hab hbc => cosetRel_trans intGrp (intMulSubgroup (natFact 2)) hab hbc)
    hq
  have h3 : ∃ c : Int,
      intGrp.mul (intGrp.inv 0) 1 = ((natFact 2 : Nat) : Int) * c := h2
  obtain ⟨c, hc⟩ := h3
  have h4 : (-(0 : Int) + 1) = (2 : Int) * c := hc
  omega

/-! ## M157F-9: 総括 -/

/-- **総括データ (M157F-9a)**: 非自明なガロア塔の全部品 —
    塔本体・各層の同定（A n = ℤ/(n!)）・ファイバーの非自明性。 -/
structure FactorialTowerData where
  /-- ガロア塔本体（M157F-7）。 -/
  tower : GaloisTower (gsetGaloisData intGrp)
  /-- 各層は剰余類対象 ℤ/(n!) そのもの。 -/
  layer_eq : ∀ n, tower.A n = cosetGSet intGrp (intMulSubgroup (natFact n))
  /-- 非自明性: 第 2 層のファイバーが 2 元を分離（M157F-8b）。 -/
  nontrivial :
    Quot.mk (cosetRel intGrp (intMulSubgroup (natFact 2))) (0 : Int)
      ≠ Quot.mk (cosetRel intGrp (intMulSubgroup (natFact 2))) (1 : Int)

/-- **証人 (M157F-9b)**: 階乗塔が全条件を満たす。 -/
def factorialTowerWitness : FactorialTowerData where
  tower := factorialTower
  layer_eq := fun _ => rfl
  nontrivial := factTower_fiber_nontrivial

/-- **定理 (M157F-9c): 階乗塔データの存在**（無矛盾性）。 -/
theorem factorialTower_exists : Nonempty FactorialTowerData :=
  ⟨factorialTowerWitness⟩

end IUT
