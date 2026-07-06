/-
  IUT/CupGradedComm.lean — M355F [実／本物]
  分類: 実 (カップ積の次数付き交換律 [f]∪[g]=−[g]∪[f]・M350F の仮説を閉じる)
  complete_pct 影響: 柱B を前進（M350F CupProduct が仮説とした次数付き交換律を ℤ/n 対角
    ケースで本物証明＝(f∪g)±(g∪f) がコバウンダリであることを明示 1-コチェインの d¹ で示し
    H² で [f]∪[g]=−[g]∪[f]、cup_graded_comm_hypothesis を実供給）。
  正直な限定: 一般係数/捻れ作用・符号規約の完全一般化は後続。
-/
import IUT.CupProduct

namespace IUT

/-! ## M355F-0: 交換した（swapped）カップ積 -/

/-- **交換カップ積（1-コチェイン）**（M355F-0）: (g∪f)(σ,τ) = g(σ)⊗(σ·f(τ))。
    ℤ/n 自明作用では ⊗ = zmodMul・σ·f(τ)=f(τ) ゆえ (g∪f)(σ,τ)=g(σ)·f(τ)。 -/
def cgcSwap (GK : Grp) (n : Nat)
    (f g : galH1Cocycle (cupZmodModule GK n)) :
    GK.carrier → GK.carrier → (zmod n).carrier :=
  cupCochain (cupZmodPairing GK n) g.f f.f

/-- **交換カップ積の具体値**（M355F-0a）: (g∪f)(σ,τ) = g(σ)·f(τ)（ℤ/n）。 -/
theorem cgc_swap_eval (GK : Grp) (n : Nat)
    (f g : galH1Cocycle (cupZmodModule GK n)) (σ τ : GK.carrier) :
    cgcSwap GK n f g σ τ = zmodMul n (g.f σ) (f.f τ) := rfl

/-- **通常カップ積の具体値**（M355F-0b）: (f∪g)(σ,τ) = f(σ)·g(τ)（ℤ/n）。 -/
theorem cgc_cup_eval (GK : Grp) (n : Nat)
    (f g : galH1Cocycle (cupZmodModule GK n)) (σ τ : GK.carrier) :
    cupCochain (cupZmodPairing GK n) f.f g.f σ τ = zmodMul n (f.f σ) (g.f τ) := rfl

/-! ## M355F-1: コチェインレベルの差 (f∪g)−(g∪f) -/

/-- **コチェインの差**（M355F-1）: (f∪g)(σ,τ) − (g∪f)(σ,τ) を ℤ/n（自明作用）で
    具体計算＝ f(σ)·g(τ) − g(σ)·f(τ)。反対称性の芽。 -/
theorem cgc_cochain_diff (GK : Grp) (n : Nat)
    (f g : galH1Cocycle (cupZmodModule GK n)) (σ τ : GK.carrier) :
    (zmod n).mul (cupCochain (cupZmodPairing GK n) f.f g.f σ τ)
        ((zmod n).inv (cgcSwap GK n f g σ τ))
      = (zmod n).mul (zmodMul n (f.f σ) (g.f τ))
          ((zmod n).inv (zmodMul n (g.f σ) (f.f τ))) := rfl

/-! ## M355F-2: 対称部 (f∪g)+(g∪f) はコバウンダリ（本証明の核） -/

/-- **点ごとのコバウンダリ等式**（M355F-2a, 本証明）: ℤ/n 自明作用で
    (f∪g)(σ,τ) + (g∪f)(σ,τ) = (d¹ψ)(σ,τ)、ψ(s) = −(f(s)·g(s))。
    両コサイクル条件（f(στ)=f(σ)+f(τ) 等）を代入し、整数上の積の展開で
    f(σ)g(τ)+g(σ)f(τ) = ψ(τ)+ψ(σ)−ψ(στ) を証明する。 -/
theorem cgc_coboundary_pointwise (GK : Grp) (n : Nat)
    (f g : galH1Cocycle (cupZmodModule GK n)) (σ τ : GK.carrier) :
    (zmod n).mul (cupCochain (cupZmodPairing GK n) f.f g.f σ τ)
        (cupCochain (cupZmodPairing GK n) g.f f.f σ τ)
      = cupD1 (cupZmodModule GK n)
          (fun s => (zmod n).inv (zmodMul n (f.f s) (g.f s))) σ τ := by
  have hf : f.f (GK.mul σ τ) = (zmod n).mul (f.f σ) (f.f τ) := f.cocycle σ τ
  have hg : g.f (GK.mul σ τ) = (zmod n).mul (g.f σ) (g.f τ) := g.cocycle σ τ
  show (zmod n).mul (zmodMul n (f.f σ) (g.f τ)) (zmodMul n (g.f σ) (f.f τ))
     = (zmod n).mul
         ((zmod n).mul
            ((zmod n).inv (zmodMul n (f.f τ) (g.f τ)))
            ((zmod n).inv (zmodMul n (f.f σ) (g.f σ))))
         ((zmod n).inv
            ((zmod n).inv (zmodMul n (f.f (GK.mul σ τ)) (g.f (GK.mul σ τ)))))
  rw [hf, hg]
  generalize f.f σ = a
  generalize f.f τ = b
  generalize g.f σ = c
  generalize g.f τ = d
  induction a using Quot.ind
  rename_i ra
  induction b using Quot.ind
  rename_i rb
  induction c using Quot.ind
  rename_i rc
  induction d using Quot.ind
  rename_i rd
  show Quot.mk (modCong n).rel (ra * rd + rc * rb)
     = Quot.mk (modCong n).rel
         (-(rb * rd) + -(ra * rc) + -(-((ra + rb) * (rc + rd))))
  have key : ra * rd + rc * rb
      = -(rb * rd) + -(ra * rc) + -(-((ra + rb) * (rc + rd))) := by
    have e : ∀ x y z w : Int,
        x * w + z * y = -(y * w) + -(x * z) + -(-((x + y) * (z + w))) := by
      intro x y z w
      rw [Int.mul_comm z y, Int.add_mul, Int.mul_add, Int.mul_add]
      generalize x * w = P
      generalize y * z = Q
      generalize y * w = R
      generalize x * z = S
      omega
    exact e ra rb rc rd
  rw [key]

/-- **対称部はコバウンダリ**（M355F-2b）: Z² の元
    (f∪g)+(g∪f) = cupCocycleOf(f,g)·cupCocycleOf(g,f) が B²（2-コバウンダリ）に属する。
    証人 ψ(s) = −(f(s)·g(s))。 -/
theorem cgc_coboundary_relation (GK : Grp) (n : Nat)
    (f g : galH1Cocycle (cupZmodModule GK n)) :
    (cupB2sub (cupZmodModule GK n)).mem
      ((cupZ2group (cupZmodModule GK n)).mul
        (cupCocycleOf (cupZmodPairing GK n) f g)
        (cupCocycleOf (cupZmodPairing GK n) g f)) := by
  refine ⟨fun s => (zmod n).inv (zmodMul n (f.f s) (g.f s)), ?_⟩
  intro σ τ
  show (zmod n).mul (cupCochain (cupZmodPairing GK n) f.f g.f σ τ)
        (cupCochain (cupZmodPairing GK n) g.f f.f σ τ)
     = cupD1 (cupZmodModule GK n)
         (fun s => (zmod n).inv (zmodMul n (f.f s) (g.f s))) σ τ
  exact cgc_coboundary_pointwise GK n f g σ τ

/-! ## M355F-3: 類レベルの次数付き交換律 [f]∪[g] = −[g]∪[f] -/

/-- **次数付き交換律（H²）**（M355F-3, capstone 本証明）: ℤ/n 対角ケースで
    [f]∪[g] = −[g]∪[f] を cupH2group の中で証明する。
    B² 所属（M355F-2b）⟹ 射影で潰れる ⟹ [f∪g]·[g∪f]=1 ⟹ [f∪g]=−[g∪f]。 -/
theorem cgc_graded_comm (GK : Grp) (n : Nat)
    (f g : galH1Cocycle (cupZmodModule GK n)) :
    cupProduct (cupZmodPairing GK n) f g
      = (cupH2group (cupZmodModule GK n)).inv
          (cupProduct (cupZmodPairing GK n) g f) := by
  have hmem : (cupB2sub (cupZmodModule GK n)).mem
      ((cupZ2group (cupZmodModule GK n)).mul
        (cupCocycleOf (cupZmodPairing GK n) g f)
        (cupCocycleOf (cupZmodPairing GK n) f g)) := by
    rw [cupZ2_comm (cupZmodModule GK n)
        (cupCocycleOf (cupZmodPairing GK n) g f)
        (cupCocycleOf (cupZmodPairing GK n) f g)]
    exact cgc_coboundary_relation GK n f g
  have hker := (quotientProjN_ker (cupZ2group (cupZmodModule GK n))
      (cupB2sub (cupZmodModule GK n)) (cupB2_normal (cupZmodModule GK n))
      ((cupZ2group (cupZmodModule GK n)).mul
        (cupCocycleOf (cupZmodPairing GK n) g f)
        (cupCocycleOf (cupZmodPairing GK n) f g))).mpr hmem
  rw [(quotientProjN (cupZ2group (cupZmodModule GK n))
        (cupB2sub (cupZmodModule GK n)) (cupB2_normal (cupZmodModule GK n))).map_mul
        (cupCocycleOf (cupZmodPairing GK n) g f)
        (cupCocycleOf (cupZmodPairing GK n) f g)] at hker
  exact Grp.inv_eq_of_mul_eq_one (cupH2group (cupZmodModule GK n)) hker

/-! ## M355F-4: M350F の仮説 cup_graded_comm_hypothesis を実供給 -/

/-- **仮説を閉じる**（M355F-4, capstone）: M350F が未導出仮説として明示した
    `cup_graded_comm_hypothesis` を、ℤ/n 対角ケース（P=P'=cupZmodPairing・
    C=C'=cupZmodModule）で本物に供給する。交換同型 iso は恒等写像で取り、
    次数付き交換律 M355F-3 がまさに要求の等式を与える。 -/
theorem cgc_supplies_hypothesis (GK : Grp) (n : Nat) :
    cup_graded_comm_hypothesis (cupZmodPairing GK n) (cupZmodPairing GK n) := by
  intro f g
  refine ⟨{ map := fun x => x, map_mul := fun _ _ => rfl }, ?_⟩
  exact cgc_graded_comm GK n f g

/-! ## M355F-5: capstone -/

/-- **capstone データ**（M355F-5a）: ℤ/n 対角ケースの次数付き交換律と、
    それが供給する M350F 仮説。 -/
structure cgcData (GK : Grp) (n : Nat) where
  /-- 次数付き交換律 [f]∪[g] = −[g]∪[f]（H²）。 -/
  gradedComm : ∀ (f g : galH1Cocycle (cupZmodModule GK n)),
    cupProduct (cupZmodPairing GK n) f g
      = (cupH2group (cupZmodModule GK n)).inv
          (cupProduct (cupZmodPairing GK n) g f)
  /-- M350F の仮説 cup_graded_comm_hypothesis を供給。 -/
  suppliesHyp : cup_graded_comm_hypothesis (cupZmodPairing GK n) (cupZmodPairing GK n)

/-- **証人**（M355F-5b）。 -/
def cgcBuild (GK : Grp) (n : Nat) : cgcData GK n where
  gradedComm := cgc_graded_comm GK n
  suppliesHyp := cgc_supplies_hypothesis GK n

/-- **次数付き交換律構造の存在**（M355F-5c）。 -/
theorem cgc_exists (GK : Grp) (n : Nat) : Nonempty (cgcData GK n) :=
  ⟨cgcBuild GK n⟩

/-- **実例**（M355F-5d）: n=6 の小さな ℤ/6 対角ケースで次数付き交換律が成立。 -/
example (GK : Grp) : Nonempty (cgcData GK 6) := cgc_exists GK 6

end IUT
