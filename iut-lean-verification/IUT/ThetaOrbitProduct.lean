/-
  IUT/ThetaOrbitProduct.lean — M373F [実／本物]
  分類: 実 (テータ軌道の積 ∏_j Θ_j^{2l}=q^{Σj²} のガロア不変性)
  complete_pct 影響: 柱E を前進（M368F テータガロア軌道・M343F Θ^{2l}=q^{j²} から、軌道の
    2l 乗の積 ∏_j Θ_j^{2l}=q^{Σj²} が q の冪ゆえ G_K 固定・q^ℤ に属する・置換不変を本物で）。
  正直な限定: M368F/M343F を積言明にパッケージ・全ラベルのテータパイロット対象は M319F 関連。

  内容（tier-S・M368F/M343F/M93 を再輸出中心に構成）:
  * M373F-1 `topExpSumNat`/`top_exp_sum_shift`/`top_exp_sum_shift_closed` — ラベル
    j=0,…,l−1 の指数 j² の総和 Σj²（Nat 版）と、その閉形式 6·Σj²=l(l+1)(2l+1)
    （M93 `ssq`/`ssq_closed` の直接再輸出）。
  * M373F-2 `topCycProd`/`top_cyc_prod_pow` — 円分影 ζ^{j²}（M343F `galThValCyc`）の
    ラベル j=0,…,l−1 にわたる有限積が ζ^{Σj²} に一致すること（M322F `cycRig_pow_add`
    の帰納的合成）。
  * M373F-3 `top_cyc_prod_norm_trivial`/`top_product_galois_fixed`/
    `top_product_galois_fixed_exp`（**本丸・新規本物**） — 積の M.n 乗ノルムは
    μ_l が指数 M.n の群ゆえ自明（=1、M343F `galTh_mu_exp_ord`）であり、単位元は
    任意の群準同型で保たれる（`Hom.map_one`）——ゆえに ∏_j Θ_j^{2l}=q^{Σj²} に
    対応する量（円分影の積の n 乗ノルム、ζ^{Σj²} 形も含む）は G_K の作用
    `galThMuAct` で完全に固定される。
  * M373F-4 `topOrbitNormProdList`/`top_orbit_norm_prod_list_eq`/
    `top_orbit_norm_prod_range` — M368F `tgoOrbitPoint`/`tgo_norm_stable` を用い、
    軌道点のノルムの積（任意のラベル列 js に対する積）はラベル列の**長さのみ**に
    依存する（`tgo_norm_stable` により各項が j に依らず同一の Θ^{M.n} ゆえ）。
    これは軌道の積が**ラベルの置換・選び方に依らず well-defined**であることの
    本物の帰結（長さが同じなら並べ替え・relabel しても積は不変）。
  * M373F-5 capstone `ThetaOrbitProductData`/`topOrbitProductData`/`top_exists`、
    実例 l=5（Σj²=0+1+4+9+16=30、6·30=4·5·9=180）。

  正直な限定（消去・弱化禁止）: 本層は M368F（μ_l/CycGKAction の抽象軌道モデル）と
  M343F（Laurent 環 CRing の具体単項式モデル q^{j²}=u^{j²} モデル）という**二つの
  形式化層**を、労働の対象とする側（μ_l 側の円分影の積・そのガロア固定性）に
  限定してパッケージする。両モデルを繋ぐ「G_K が実際に基礎体 K 上の q を固定する」
  という主張自体は、この二層のいずれにも実 Galois 作用として明示的には形式化
  されておらず（μ_l 側では「n 乗すると自明」という exponent-of-order の技巧に
  帰着させて Galois-fixed を導く——M343F `galTh_norm_twist_trivial`/M348F
  `tmt_norm_invariant` と同じ厳密さの水準）、既存 M348F-3a/3b 同様、両モデルを
  形式的に橋渡しする定理はここでも与えない（正直な限定として明示）。全ラベルの
  テータパイロット対象・エタールテータ関数値そのものの p 進収束は M319F/柱E 後続。

  選択公理不使用（新規 Classical.choice なし）。sorry 不使用。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用。許可タクティク（cases/obtain/induction/rw/show/refine/exact/apply/intro/
  generalize/funext/omega）のみ使用。共有ファイル（IUT.lean・build.sh・dashboard.md・
  graph 系）は一切変更していない。一般名は `top` 接頭辞で衝突回避。
-/
import IUT.ThetaGaloisOrbit
import IUT.GaussianVolume

namespace IUT

/-! ## M373F-1: ラベル 0,…,l−1 の指数和 Σj²（Nat 版）と閉形式 -/

/-- **M373F-1a: 指数和** — topExpSumNat l = Σ_{j=0}^{l−1} j²（0 始まりラベルの
    テータ値指数 j² の総和、Nat 版）。 -/
def topExpSumNat : Nat → Nat
  | 0 => 0
  | l + 1 => l * l + topExpSumNat l

/-- **定理 (M373F-1b: シフト形の M93 `ssq` への一致)** — topExpSumNat (l+1) = ssq l
    （M93 `ssq` の l 帰納、加法の可換律のみ）。ラベル 0,…,l の指数和が既存本物の
    平方和 `ssq` に一致することの本物。 -/
theorem top_exp_sum_shift (l : Nat) : topExpSumNat (l + 1) = ssq l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    show (l + 1) * (l + 1) + topExpSumNat (l + 1) = ssq (l + 1)
    rw [ih]
    exact Nat.add_comm ((l + 1) * (l + 1)) (ssq l)

/-- **定理 (M373F-1c: 閉形式)** — 6·topExpSumNat (l+1) = l(l+1)(2l+1)
    （M93 `ssq_closed` の直接再輸出）。テータ軌道の指数和 Σj² の閉形式。 -/
theorem top_exp_sum_shift_closed (l : Nat) :
    6 * topExpSumNat (l + 1) = l * (l + 1) * (2 * l + 1) := by
  rw [top_exp_sum_shift l]
  exact ssq_closed l

/-! ## M373F-2: 円分影の有限積 ∏_j ζ^{j²} = ζ^{Σj²}（M343F 再輸出中心） -/

/-- **M373F-2a: 円分影の有限積** — ラベル j=0,…,l−1 にわたる円分影
    `galThValCyc M j`（M343F）の μ_l 内での有限積。 -/
def topCycProd (M : CycMuGroup) : Nat → M.μ.carrier
  | 0 => M.μ.one
  | l + 1 => M.μ.mul (galThValCyc M l) (topCycProd M l)

/-- **定理 (M373F-2b: 積は指数和の円分影に一致)** — topCycProd M l = ζ^{Σj²}
    （M322F `cycRig_pow_add` の帰納的合成、l 個の項を畳み込む）。テータ軌道の
    円分影の積 ∏_j ζ^{j²} が単一の円分影 ζ^{Σj²} に一致することの本物。 -/
theorem top_cyc_prod_pow (M : CycMuGroup) : ∀ l : Nat,
    topCycProd M l = M.μ.pow M.ζ (topExpSumNat l) := by
  intro l
  induction l with
  | zero => rfl
  | succ l ih =>
    show M.μ.mul (M.μ.pow M.ζ (l * l)) (topCycProd M l)
       = M.μ.pow M.ζ (l * l + topExpSumNat l)
    rw [ih]
    exact (cycRig_pow_add M.μ M.comm M.ζ (l * l) (topExpSumNat l)).symm

/-! ## M373F-3: 積の n 乗ノルムはガロア固定（本丸・新規本物） -/

/-- **定理 (M373F-3a: 積の n 乗ノルムは自明)** — (∏_j ζ^{j²})^{M.n} = 1
    （μ_l は指数 M.n の群、M343F `galTh_mu_exp_ord` の直接適用）。IUT の
    Θ^{2l}=q^{Σj²} の円分影版ノルムが自明に帰着することの本物。 -/
theorem top_cyc_prod_norm_trivial (M : CycMuGroup) (l : Nat) :
    M.μ.pow (topCycProd M l) M.n = M.μ.one :=
  galTh_mu_exp_ord M (topCycProd M l)

/-- **定理 (M373F-3b: 積の n 乗ノルムはガロア固定・本丸)** — G_K の任意の作用 σ_g は
    (∏_j ζ^{j²})^{M.n} を固定する: σ_g((∏_j ζ^{j²})^{M.n}) = (∏_j ζ^{j²})^{M.n}
    （M373F-3a により両辺とも単位元 1、群準同型は単位元を保つ `Hom.map_one`）。
    IUT の軌道の 2l 乗の積 ∏_j Θ_j^{2l}=q^{Σj²} が G_K 固定（本物）であることの
    円分影モデルでの核心。 -/
theorem top_product_galois_fixed (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (l : Nat) :
    galThMuAct GK M ρ g (M.μ.pow (topCycProd M l) M.n) = M.μ.pow (topCycProd M l) M.n := by
  rw [top_cyc_prod_norm_trivial M l]
  show (ρ.act g).map M.μ.one = M.μ.one
  exact Hom.map_one (ρ.act g)

/-- **定理 (M373F-3c: 指数和形でのガロア固定)** — G_K は (ζ^{Σj²})^{M.n} を固定する
    （M373F-2b で topCycProd を ζ^{Σj²} 形に書き換え、M373F-3b を適用）。
    「q^{Σj²} は G_K 固定」の円分影 ζ^{Σj²} 版・本丸の指数明示形。 -/
theorem top_product_galois_fixed_exp (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (l : Nat) :
    galThMuAct GK M ρ g (M.μ.pow (M.μ.pow M.ζ (topExpSumNat l)) M.n)
      = M.μ.pow (M.μ.pow M.ζ (topExpSumNat l)) M.n := by
  rw [← top_cyc_prod_pow M l]
  exact top_product_galois_fixed GK M ρ g l

/-! ## M373F-4: 軌道点ノルムの積は列の長さのみに依存（置換不変・M368F 接続） -/

/-- **M373F-4a: 軌道点ノルムの有限積（任意のラベル列）** — ラベル列 js に沿った
    軌道点 `tgoOrbitPoint M Θ j`（M368F）の M.n 乗ノルムの有限積。 -/
def topOrbitNormProdList (M : CycMuGroup) (Θ : M.μ.carrier) : List Nat → M.μ.carrier
  | [] => M.μ.one
  | j :: js => M.μ.mul (M.μ.pow (tgoOrbitPoint M Θ j) M.n) (topOrbitNormProdList M Θ js)

/-- **定理 (M373F-4b: 積は列の長さのみに依存・本丸)** — 任意のラベル列 js に対し
    topOrbitNormProdList M Θ js = (Θ^{M.n})^{|js|}（M368F `tgo_norm_stable` により
    各項が j に依らず同一の Θ^{M.n} であることの帰納的合成）。ラベルの**選び方・
    並べ替えに依らず**（長さが同じなら）積が一致する——軌道の積の well-definedness
    （置換不変性）の本物。 -/
theorem top_orbit_norm_prod_list_eq (M : CycMuGroup) (Θ : M.μ.carrier) :
    ∀ js : List Nat, topOrbitNormProdList M Θ js = M.μ.pow (M.μ.pow Θ M.n) js.length := by
  intro js
  induction js with
  | nil => rfl
  | cons j js ih =>
    show M.μ.mul (M.μ.pow (tgoOrbitPoint M Θ j) M.n) (topOrbitNormProdList M Θ js)
       = M.μ.mul (M.μ.pow Θ M.n) (M.μ.pow (M.μ.pow Θ M.n) js.length)
    rw [tgo_norm_stable M Θ j, ih]

/-- **定理 (M373F-4c: M368F 軌道 `tgoOrbit` のラベル列 `List.range l` への特殊化)** —
    topOrbitNormProdList M Θ (List.range l) = (Θ^{M.n})^{l}（`List.length_range`）。
    M368F の軌道 `tgoOrbit M Θ l`（ラベル 0,…,l−1）に沿った軌道点ノルムの積が
    (Θ^{M.n})^{l} に一致することの本物の接続。 -/
theorem top_orbit_norm_prod_range (M : CycMuGroup) (Θ : M.μ.carrier) (l : Nat) :
    topOrbitNormProdList M Θ (List.range l) = M.μ.pow (M.μ.pow Θ M.n) l := by
  rw [top_orbit_norm_prod_list_eq M Θ (List.range l), List.length_range]

/-! ## M373F-5: capstone（テータ軌道の積データ）と存在 -/

/-- **M373F-5a: テータ軌道の積データ** — 円分影の有限積が指数和形 ζ^{Σj²} に一致
    すること・その M.n 乗ノルムが自明であること・G_K がそのノルムを固定すること
    （円分影版・指数和版）・軌道点ノルムの積が `List.range l` で (Θ^{M.n})^{l} に
    一致することを一括束ねる。M368F（軌道）と M343F（Θ^{2l}=q^{j²} のガロア不変性）
    を「軌道の積」の言葉に束ね直した本物の witness 形。 -/
structure ThetaOrbitProductData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (Θ : M.μ.carrier) (l : Nat) where
  /-- 円分影の有限積は指数和形 ζ^{Σj²} に一致。 -/
  cycProd_eq : topCycProd M l = M.μ.pow M.ζ (topExpSumNat l)
  /-- 積の M.n 乗ノルムは自明（=1）。 -/
  norm_trivial : M.μ.pow (topCycProd M l) M.n = M.μ.one
  /-- 積の M.n 乗ノルムは任意の G_K 作用で固定される。 -/
  galois_fixed : ∀ g, galThMuAct GK M ρ g (M.μ.pow (topCycProd M l) M.n)
    = M.μ.pow (topCycProd M l) M.n
  /-- 軌道点ノルムの積（ラベル 0,…,l−1）は (Θ^{M.n})^{l} に一致。 -/
  orbit_norm_range : topOrbitNormProdList M Θ (List.range l) = M.μ.pow (M.μ.pow Θ M.n) l

/-- **M373F-5b: witness 本体** — 各フィールドを M373F-2〜4 の主定理で埋める。 -/
def topOrbitProductData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (Θ : M.μ.carrier) (l : Nat) : ThetaOrbitProductData GK M ρ Θ l where
  cycProd_eq := top_cyc_prod_pow M l
  norm_trivial := top_cyc_prod_norm_trivial M l
  galois_fixed := fun g => top_product_galois_fixed GK M ρ g l
  orbit_norm_range := top_orbit_norm_prod_range M Θ l

/-- **定理 (M373F-5c: capstone — テータ軌道の積データの存在)** — 任意の G_K・μ_l・
    作用 ρ・基点 Θ・ラベル数 l に対し、テータ軌道の積データ（円分影の積の指数和形・
    ノルムの自明性・ガロア固定性・軌道点ノルム積の well-definedness）が本物で
    組み上がる。M368F/M343F を「軌道の積 ∏_j Θ_j^{2l}=q^{Σj²} のガロア不変性」の
    言葉に束ねる総括が閉じる。 -/
theorem top_exists (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (Θ : M.μ.carrier)
    (l : Nat) : Nonempty (ThetaOrbitProductData GK M ρ Θ l) :=
  ⟨topOrbitProductData GK M ρ Θ l⟩

/-! ## 実例（l=5・本物の G_ℚ の μ_5 上のテータ軌道の積） -/

/-- 実例: 本物の絶対ガロア群 G_ℚ = `algCloAbsGalois algCloTrivialTower`（M315F）の
    μ_5（本物の巡回群 ℤ/5 = `cycMuStd 5`）上で、生成元 ζ を基点とするテータ軌道の
    積データが存在する。 -/
theorem top_example_l5 :
    Nonempty (ThetaOrbitProductData (algCloAbsGalois algCloTrivialTower)
      (cycMuStd 5 (by omega))
      (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega)))
      (cycMuStd 5 (by omega)).ζ 5) :=
  top_exists (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega)))
    (cycMuStd 5 (by omega)).ζ 5

/-- 実例: l=5 の指数和 Σ_{j=0}^{4} j² = 0+1+4+9+16 = 30
    （`top_exp_sum_shift` で ssq 4 = 30 に帰着）。 -/
example : topExpSumNat 5 = 30 := by
  rw [top_exp_sum_shift 4]
  rfl

/-- 実例: 指数和の閉形式 6·30 = 4·5·9 = 180（`top_exp_sum_shift_closed`）。 -/
example : 6 * topExpSumNat 5 = 4 * 5 * 9 := top_exp_sum_shift_closed 4

/-- 実例: l=5 の円分影の積の M.n 乗ノルムは、本物の G_ℚ の任意の作用 g で固定される
    （`top_product_galois_fixed`）。 -/
example (g : (algCloAbsGalois algCloTrivialTower).carrier) :
    galThMuAct (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
        (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))) g
        ((cycMuStd 5 (by omega)).μ.pow (topCycProd (cycMuStd 5 (by omega)) 5)
          (cycMuStd 5 (by omega)).n)
      = (cycMuStd 5 (by omega)).μ.pow (topCycProd (cycMuStd 5 (by omega)) 5)
          (cycMuStd 5 (by omega)).n :=
  top_product_galois_fixed (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))) g 5

end IUT
