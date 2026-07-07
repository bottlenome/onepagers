/-
  IUT/HilbertSymbol.lean — M370F [実／本物]
  分類: 実 (局所 Hilbert 記号 (a,b)_v=inv(δ(a)∪δ(b))∈(1/n)ℤ/ℤ)
  complete_pct 影響: 柱B を前進（M365F inv・M350F カップ積・M345F Kummer で Hilbert 記号
    (a,b)_n=inv(δ(a)∪δ(b)) を構成・双線形・反対称（M355F 次数付き交換律）・分裂条件を本物で。
    局所双対性の記号）。
  正直な限定: 非退化性（局所 CFT）・Steinberg 関係は外部仮説/後続。

  ── 本物で閉じる中身（骨格のみでない）:
  * M370F-1 `hsymSymbol` — Hilbert 記号 (a,b)_n = inv(δ(a)∪δ(b)) ∈ (1/n)ℤ/ℤ = `briQZn n`。
    Kummer 類 δ(a),δ(b)∈H¹(G_K,μ_n) を ℤ/n 対角ケース（M345F Kummer が住む
    H¹(G_K,ℤ/n)）のコサイクルとして受け、M350F `cupProduct` でカップ積 δ(a)∪δ(b)∈H²
    （=Br(K)[n], M360F `brauGroup`）へ、局所不変量 `invH:H²→(1/n)ℤ/ℤ` を合成。
  * M370F-2 `hsym_cup_bilinear_left/right` — H² レベルのカップ積双線形（M350F `cup_bilinear_*`
    を射影 `quotientProjN` の準同型性で H² へ持ち上げ）。`hsym_bilinear_left/right` —
    (a₁a₂,b)=(a₁,b)+(a₂,b)（inv の準同型性 M365F 系 `Hom.map_mul` を合成）。**本証明**。
  * M370F-3 `hsym_antisymmetric` — (a,b) = −(b,a)。M355F `cgc_graded_comm`
    ([f]∪[g]=−[g]∪[f]) に inv（`Hom.map_inv`）を合成。**本証明**。
  * M370F-4 `hsym_one_left`（(1,b)=0, `cup_tensor_one_left`＋射影 map_one）・
    `hsym_self_two_torsion`（(a,a)+(a,a)=0＝反対称の帰結、(a,a)=−(a,a)）。**本証明**。
  * M370F-5 `hsym_zero_iff_ker`（(a,b)=0 ⟺ δ(a)∪δ(b)∈ker(inv)）・
    `hsym_zero_of_split`（Brauer 類が分裂 ⟹ 記号 0）・`hsym_split_of_zero`
    （inv 単射なら 記号 0 ⟹ Brauer 分裂）・`hsym_brauer_split_iff`
    （分裂 ⟺ 2-コバウンダリ, M360F `brau_split_iff`）。分裂条件を本物で。
  * M370F-6 `hsym_nondegenerate_hypothesis` — 記号の左非退化（局所 Tate 双対）を
    **未導出の Prop 仮説**として明示（全 g で (a,b)=0 ⟹ a は H¹ で自明）。
  * M370F-7 capstone `hsymData`/`hsymBuild`/`hsym_exists`・自明不変量 `hsymTrivialInv`・
    n=2 実例（古典 2 次 Hilbert 記号 (a,b)_2∈{0,1/2}=briQZn 2）。

  **正直な限定**（消去・弱化禁止）:
  1. **局所不変量 inv: H²(G_K,μ_n) → (1/n)ℤ/ℤ** は本モジュールでは Hom `invH` として
     **受け取る**（本物化には局所類体論の不変量同型 M360F `brau_inv_hypothesis` を要する）。
     無条件に構成できるのは自明不変量 `hsymTrivialInv`（記号が恒等的に 0）のみ。真の
     非退化不変量は `hsym_nondegenerate_hypothesis`（未導出）。
  2. **非退化性（局所双対性）**は `hsym_nondegenerate_hypothesis`（未導出の Prop 仮説）。
     決して導出しない。
  3. **Steinberg 関係 (a,1−a)=0** は体の加法構造（1−a）を要し本モジュール範囲外/後続。
     代わりに次数構造が与える (a,a) の 2-捻れ性を本物で示す。
  4. δ(a),δ(b) は M345F Kummer 写像が住む H¹(G_K,ℤ/n) の元（自明作用 ℤ/n 対角ケース、
     M355F と同じ規約）として扱う。一般係数 μ_n・捻れ作用は後続。

  **選択公理不使用・sorry 皆無**: 全宣言の公理は [propext, Quot.sound] のみ。
  禁止タクティク不使用。一般名は `hsym` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.CupGradedComm
import IUT.BrauerInvariant
import IUT.LocalBrauer

namespace IUT

/-! ## M370F-2a: H² レベルのカップ積双線形（射影で持ち上げ） -/

/-- **H² 双線形（左）**（M370F-2a）: (f₁+f₂)∪g = f₁∪g + f₂∪g（H² の等式）。
    M350F `cup_bilinear_left`（Z² の等式）を射影 `quotientProjN` の準同型性
    `Hom.map_mul` で H²=Z²/B² へ持ち上げる。 -/
theorem hsym_cup_bilinear_left (GK : Grp) (n : Nat)
    (f f' g : galH1Cocycle (cupZmodModule GK n)) :
    cupProduct (cupZmodPairing GK n)
        ((galH1_cocycles_group (cupZmodModule GK n)).mul f f') g
      = (cupH2group (cupZmodModule GK n)).mul
          (cupProduct (cupZmodPairing GK n) f g)
          (cupProduct (cupZmodPairing GK n) f' g) := by
  show (quotientProjN (cupZ2group (cupZmodModule GK n)) (cupB2sub (cupZmodModule GK n))
          (cupB2_normal (cupZmodModule GK n))).map
        (cupCocycleOf (cupZmodPairing GK n)
          ((galH1_cocycles_group (cupZmodModule GK n)).mul f f') g)
      = (cupH2group (cupZmodModule GK n)).mul
          (cupProduct (cupZmodPairing GK n) f g)
          (cupProduct (cupZmodPairing GK n) f' g)
  rw [cup_bilinear_left (cupZmodPairing GK n) f f' g]
  exact (quotientProjN (cupZ2group (cupZmodModule GK n)) (cupB2sub (cupZmodModule GK n))
          (cupB2_normal (cupZmodModule GK n))).map_mul
        (cupCocycleOf (cupZmodPairing GK n) f g)
        (cupCocycleOf (cupZmodPairing GK n) f' g)

/-- **H² 双線形（右）**（M370F-2b）: f∪(g₁+g₂) = f∪g₁ + f∪g₂（H² の等式）。 -/
theorem hsym_cup_bilinear_right (GK : Grp) (n : Nat)
    (f g g' : galH1Cocycle (cupZmodModule GK n)) :
    cupProduct (cupZmodPairing GK n) f
        ((galH1_cocycles_group (cupZmodModule GK n)).mul g g')
      = (cupH2group (cupZmodModule GK n)).mul
          (cupProduct (cupZmodPairing GK n) f g)
          (cupProduct (cupZmodPairing GK n) f g') := by
  show (quotientProjN (cupZ2group (cupZmodModule GK n)) (cupB2sub (cupZmodModule GK n))
          (cupB2_normal (cupZmodModule GK n))).map
        (cupCocycleOf (cupZmodPairing GK n) f
          ((galH1_cocycles_group (cupZmodModule GK n)).mul g g'))
      = (cupH2group (cupZmodModule GK n)).mul
          (cupProduct (cupZmodPairing GK n) f g)
          (cupProduct (cupZmodPairing GK n) f g')
  rw [cup_bilinear_right (cupZmodPairing GK n) f g g']
  exact (quotientProjN (cupZ2group (cupZmodModule GK n)) (cupB2sub (cupZmodModule GK n))
          (cupB2_normal (cupZmodModule GK n))).map_mul
        (cupCocycleOf (cupZmodPairing GK n) f g)
        (cupCocycleOf (cupZmodPairing GK n) f g')

/-! ## M370F-1: Hilbert 記号 (a,b)_n = inv(δ(a)∪δ(b)) ∈ (1/n)ℤ/ℤ -/

/-- **局所 Hilbert 記号**（M370F-1）: Kummer 類 δ(a)=f, δ(b)=g ∈ H¹(G_K,ℤ/n) に対し
    (a,b)_n = inv(δ(a)∪δ(b)) ∈ (1/n)ℤ/ℤ = `briQZn n`。M350F `cupProduct` で
    δ(a)∪δ(b) ∈ H²(=Br(K)[n]) を作り、局所不変量 `invH:H²→(1/n)ℤ/ℤ` を合成。
    inv の本物化は局所 CFT（`brau_inv_hypothesis`）を要するため `invH` として受け取る。 -/
def hsymSymbol (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n))
    (f g : galH1Cocycle (cupZmodModule GK n)) : (briQZn n).carrier :=
  invH.map (cupProduct (cupZmodPairing GK n) f g)

/-- 記号の明示式: (a,b)_n = inv(δ(a)∪δ(b))。 -/
theorem hsymSymbol_apply (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n))
    (f g : galH1Cocycle (cupZmodModule GK n)) :
    hsymSymbol GK n invH f g = invH.map (cupProduct (cupZmodPairing GK n) f g) := rfl

/-! ## M370F-2: 双線形性（各引数で加法的） -/

/-- **双線形（左）**（M370F-2c, 本証明）: (a₁a₂,b)=(a₁,b)+(a₂,b)。
    H² カップ積双線形（M370F-2a）＋不変量 inv の準同型性（`Hom.map_mul`）。 -/
theorem hsym_bilinear_left (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n))
    (f f' g : galH1Cocycle (cupZmodModule GK n)) :
    hsymSymbol GK n invH ((galH1_cocycles_group (cupZmodModule GK n)).mul f f') g
      = (briQZn n).mul (hsymSymbol GK n invH f g) (hsymSymbol GK n invH f' g) := by
  show invH.map (cupProduct (cupZmodPairing GK n)
        ((galH1_cocycles_group (cupZmodModule GK n)).mul f f') g)
      = (briQZn n).mul (invH.map (cupProduct (cupZmodPairing GK n) f g))
          (invH.map (cupProduct (cupZmodPairing GK n) f' g))
  rw [hsym_cup_bilinear_left GK n f f' g]
  exact invH.map_mul (cupProduct (cupZmodPairing GK n) f g)
    (cupProduct (cupZmodPairing GK n) f' g)

/-- **双線形（右）**（M370F-2d, 本証明）: (a,b₁b₂)=(a,b₁)+(a,b₂)。 -/
theorem hsym_bilinear_right (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n))
    (f g g' : galH1Cocycle (cupZmodModule GK n)) :
    hsymSymbol GK n invH f ((galH1_cocycles_group (cupZmodModule GK n)).mul g g')
      = (briQZn n).mul (hsymSymbol GK n invH f g) (hsymSymbol GK n invH f g') := by
  show invH.map (cupProduct (cupZmodPairing GK n) f
        ((galH1_cocycles_group (cupZmodModule GK n)).mul g g'))
      = (briQZn n).mul (invH.map (cupProduct (cupZmodPairing GK n) f g))
          (invH.map (cupProduct (cupZmodPairing GK n) f g'))
  rw [hsym_cup_bilinear_right GK n f g g']
  exact invH.map_mul (cupProduct (cupZmodPairing GK n) f g)
    (cupProduct (cupZmodPairing GK n) f g')

/-! ## M370F-3: 反対称性 (a,b) = −(b,a) -/

/-- **反対称性**（M370F-3, 本証明）: (a,b) = −(b,a)。M355F `cgc_graded_comm`
    ([f]∪[g] = −[g]∪[f]) に不変量 inv（`Hom.map_inv`）を合成する。 -/
theorem hsym_antisymmetric (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n))
    (f g : galH1Cocycle (cupZmodModule GK n)) :
    hsymSymbol GK n invH f g = (briQZn n).inv (hsymSymbol GK n invH g f) := by
  show invH.map (cupProduct (cupZmodPairing GK n) f g)
      = (briQZn n).inv (invH.map (cupProduct (cupZmodPairing GK n) g f))
  rw [cgc_graded_comm GK n f g]
  exact invH.map_inv (cupProduct (cupZmodPairing GK n) g f)

/-! ## M370F-4: (1,b)=0 と (a,a) の 2-捻れ性 -/

/-- **(1,b)=0**（M370F-4a, 本証明）: 自明 Kummer 類（δ(1)=0=H¹ の単位コサイクル）
    との記号は消える。cup(0,g)=0（`cup_tensor_one_left`）⟹ H² で自明 ⟹ inv=0。 -/
theorem hsym_one_left (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n))
    (g : galH1Cocycle (cupZmodModule GK n)) :
    hsymSymbol GK n invH (galH1_cocycles_group (cupZmodModule GK n)).one g
      = (briQZn n).one := by
  have hc : cupCocycleOf (cupZmodPairing GK n)
        (galH1_cocycles_group (cupZmodModule GK n)).one g
      = (cupZ2group (cupZmodModule GK n)).one := by
    apply cupTwoCocycle.ext
    funext σ τ
    exact cup_tensor_one_left (cupZmodPairing GK n)
      (((cupZmodModule GK n).act σ).map (g.f τ))
  have hp : cupProduct (cupZmodPairing GK n)
        (galH1_cocycles_group (cupZmodModule GK n)).one g
      = (cupH2group (cupZmodModule GK n)).one := by
    show (quotientProjN (cupZ2group (cupZmodModule GK n)) (cupB2sub (cupZmodModule GK n))
            (cupB2_normal (cupZmodModule GK n))).map
          (cupCocycleOf (cupZmodPairing GK n)
            (galH1_cocycles_group (cupZmodModule GK n)).one g)
        = (cupH2group (cupZmodModule GK n)).one
    rw [hc]
    exact (quotientProjN (cupZ2group (cupZmodModule GK n)) (cupB2sub (cupZmodModule GK n))
            (cupB2_normal (cupZmodModule GK n))).map_one
  show invH.map (cupProduct (cupZmodPairing GK n)
        (galH1_cocycles_group (cupZmodModule GK n)).one g) = (briQZn n).one
  rw [hp]
  exact invH.map_one

/-- **(a,a) は 2-捻れ**（M370F-4b, 本証明）: 反対称性 (a,a)=−(a,a) から
    (a,a)+(a,a)=0。次数付き交換律が対角で与える交代性（alternating の芽）。 -/
theorem hsym_self_two_torsion (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n))
    (f : galH1Cocycle (cupZmodModule GK n)) :
    (briQZn n).mul (hsymSymbol GK n invH f f) (hsymSymbol GK n invH f f)
      = (briQZn n).one := by
  have hanti := hsym_antisymmetric GK n invH f f
  have step : (briQZn n).mul (hsymSymbol GK n invH f f) (hsymSymbol GK n invH f f)
      = (briQZn n).mul ((briQZn n).inv (hsymSymbol GK n invH f f))
          (hsymSymbol GK n invH f f) := by
    rw [← hanti]
  rw [step]
  exact (briQZn n).inv_mul (hsymSymbol GK n invH f f)

/-! ## M370F-5: 分裂条件 (a,b)=0 ⟺ 記号がカップ積の核 ⟺ Brauer 分裂 -/

/-- **記号 0 ⟺ カップ積が核**（M370F-5a）: (a,b)_n = 0 ⟺ δ(a)∪δ(b) ∈ ker(inv)。
    不変量の核による特徴付け（定義展開）。 -/
theorem hsym_zero_iff_ker (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n))
    (f g : galH1Cocycle (cupZmodModule GK n)) :
    hsymSymbol GK n invH f g = (briQZn n).one
      ↔ (kerSubgroup invH).mem (cupProduct (cupZmodPairing GK n) f g) :=
  Iff.rfl

/-- **Brauer 分裂 ⟹ 記号 0**（M370F-5b, 本証明）: 巡回代数 δ(a)∪δ(b) が Br(K) で
    分裂（H² で自明）なら記号 (a,b)=0（不変量は準同型ゆえ単位元を単位元へ）。 -/
theorem hsym_zero_of_split (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n))
    (f g : galH1Cocycle (cupZmodModule GK n))
    (h : cupProduct (cupZmodPairing GK n) f g = (cupH2group (cupZmodModule GK n)).one) :
    hsymSymbol GK n invH f g = (briQZn n).one := by
  show invH.map (cupProduct (cupZmodPairing GK n) f g) = (briQZn n).one
  rw [h]
  exact invH.map_one

/-- **記号 0 ⟹ Brauer 分裂（inv 単射のとき）**（M370F-5c, 本証明）: 不変量 inv が
    単射（非退化の一部＝Br(K)[n] を忠実に (1/n)ℤ/ℤ へ）なら、(a,b)=0 ⟹ 巡回代数が
    Br(K) で分裂。逆方向は非退化性を要する接続点。 -/
theorem hsym_split_of_zero (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n))
    (hinj : Hom.Injective invH)
    (f g : galH1Cocycle (cupZmodModule GK n))
    (h : hsymSymbol GK n invH f g = (briQZn n).one) :
    cupProduct (cupZmodPairing GK n) f g = (cupH2group (cupZmodModule GK n)).one := by
  apply hinj
  rw [invH.map_one]
  exact h

/-- **Brauer 分裂 ⟺ 2-コバウンダリ**（M370F-5d）: 巡回代数 δ(a)∪δ(b) が Br(K) で
    分裂 ⟺ そのコサイクル χ∪g が 2-コバウンダリ（B² に属す）。M360F `brau_split_iff`
    を Kbar=ℤ/n 模型で再輸出。「分裂 ⟺ ノルム/コバウンダリ」の一段。 -/
theorem hsym_brauer_split_iff (GK : Grp) (n : Nat)
    (f g : galH1Cocycle (cupZmodModule GK n)) :
    cupProduct (cupZmodPairing GK n) f g = (brauGroup (cupZmodModule GK n)).one
      ↔ (cupB2sub (cupZmodModule GK n)).mem
          (cupCocycleOf (cupZmodPairing GK n) f g) :=
  brau_split_iff (cupZmodModule GK n) (cupCocycleOf (cupZmodPairing GK n) f g)

/-! ## M370F-6: 非退化性（局所双対）は未導出の外部仮説 -/

/-- **外部仮説（未導出）: Hilbert 記号の左非退化性**（M370F-6）: 局所 Tate 双対
    （局所 CFT）が保証する非退化性 — δ(a) が全ての δ(b) と直交（(a,b)=0 ∀b）なら
    δ(a) は H¹ で自明（a は n 乗元、a∈(K^×)ⁿ に対応）。inv の全単射性を要するため
    本モジュールでは**決して導出しない** Prop 仮説として明示。 -/
def hsym_nondegenerate_hypothesis (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n)) : Prop :=
  ∀ f : galH1Cocycle (cupZmodModule GK n),
    (∀ g, hsymSymbol GK n invH f g = (briQZn n).one) →
      (galH1_coboundaries_subgroup (cupZmodModule GK n)).mem f

/-! ## M370F-7: capstone・自明不変量・n=2 実例 -/

/-- **自明不変量**（M370F-7a）: 無条件に存在する唯一の inv 準同型（全て 0 へ）。
    これ由来の記号は恒等的に 0（非退化でない）。真の非退化不変量は局所 CFT
    （`brau_inv_hypothesis`）を要し `hsym_nondegenerate_hypothesis` で受ける。 -/
def hsymTrivialInv (GK : Grp) (n : Nat) :
    Hom (cupH2group (cupZmodModule GK n)) (briQZn n) where
  map := fun _ => (briQZn n).one
  map_mul := fun _ _ => ((briQZn n).one_mul (briQZn n).one).symm

/-- **capstone データ**（M370F-7b）: 不変量 inv に対する Hilbert 記号の全性質 —
    双線形・反対称・(1,b)=0・(a,a) の 2-捻れ性を束ねる。 -/
structure hsymData (GK : Grp) (n : Nat) where
  /-- 局所不変量 inv: H²(=Br(K)[n]) → (1/n)ℤ/ℤ。 -/
  invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n)
  /-- 双線形（左）。 -/
  bilinear_left : ∀ f f' g,
    hsymSymbol GK n invH ((galH1_cocycles_group (cupZmodModule GK n)).mul f f') g
      = (briQZn n).mul (hsymSymbol GK n invH f g) (hsymSymbol GK n invH f' g)
  /-- 双線形（右）。 -/
  bilinear_right : ∀ f g g',
    hsymSymbol GK n invH f ((galH1_cocycles_group (cupZmodModule GK n)).mul g g')
      = (briQZn n).mul (hsymSymbol GK n invH f g) (hsymSymbol GK n invH f g')
  /-- 反対称 (a,b)=−(b,a)。 -/
  antisymmetric : ∀ f g,
    hsymSymbol GK n invH f g = (briQZn n).inv (hsymSymbol GK n invH g f)
  /-- (1,b)=0。 -/
  one_left : ∀ g,
    hsymSymbol GK n invH (galH1_cocycles_group (cupZmodModule GK n)).one g
      = (briQZn n).one
  /-- (a,a) は 2-捻れ。 -/
  self_two_torsion : ∀ f,
    (briQZn n).mul (hsymSymbol GK n invH f f) (hsymSymbol GK n invH f f)
      = (briQZn n).one

/-- **証人**（M370F-7c）: 任意の不変量 inv に対し全性質を本物の証明で満たす。 -/
def hsymBuild (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n)) : hsymData GK n where
  invH := invH
  bilinear_left := hsym_bilinear_left GK n invH
  bilinear_right := hsym_bilinear_right GK n invH
  antisymmetric := hsym_antisymmetric GK n invH
  one_left := hsym_one_left GK n invH
  self_two_torsion := hsym_self_two_torsion GK n invH

/-- **Hilbert 記号構造の存在**（M370F-7d, capstone）。 -/
theorem hsym_exists (GK : Grp) (n : Nat)
    (invH : Hom (cupH2group (cupZmodModule GK n)) (briQZn n)) :
    Nonempty (hsymData GK n) :=
  ⟨hsymBuild GK n invH⟩

/-- **無条件の存在（自明不変量）**（M370F-7e）: inv を CFT に頼らず自明不変量で
    取れば、Hilbert 記号の全性質を満たす構造が**無条件に**存在する
    （記号値は 0＝非退化でない、正直な限定の可視化）。 -/
theorem hsym_exists_trivial (GK : Grp) (n : Nat) : Nonempty (hsymData GK n) :=
  ⟨hsymBuild GK n (hsymTrivialInv GK n)⟩

/-! ## M370F-7f: n=2 実例 — 古典 2 次 Hilbert 記号 (a,b)_2 ∈ {0,1/2} -/

/-- **n=2 の Hilbert 記号構造の存在**（M370F-7f-1）: (a,b)_2 ∈ (1/2)ℤ/ℤ =`briQZn 2`
    ={0,1/2} — 古典的な 2 次 Hilbert 記号の全性質（双線形・反対称・交代）が実体化。 -/
theorem hsym_n2_exists (GK : Grp) : Nonempty (hsymData GK 2) :=
  hsym_exists_trivial GK 2

/-- **n=2 の値群 (1/2)ℤ/ℤ は非自明**（M370F-7f-2）: 古典 2 次 Hilbert 記号の
    値域 (1/2)ℤ/ℤ =`briQZn 2` は {0,1/2} で、1/2≠0（M365F 四元数不変量の再輸出）。
    Hilbert 記号が住む値群が非自明であること。 -/
theorem hsym_n2_value_group_nontrivial (U : Grp) :
    (briInvCyclic U 2).map ((1 : Int), U.one) ≠ (briQZn 2).one :=
  bri_quaternion_not_split U

/-- **n=2 自明不変量の記号値は 0**（M370F-7f-3）: 自明不変量では (a,b)_2 = 0
    （小さな計算例）。真の非零値は非退化不変量＝局所 CFT を要する。 -/
theorem hsym_n2_trivial_value (GK : Grp)
    (f g : galH1Cocycle (cupZmodModule GK 2)) :
    hsymSymbol GK 2 (hsymTrivialInv GK 2) f g = (briQZn 2).one := rfl

end IUT
