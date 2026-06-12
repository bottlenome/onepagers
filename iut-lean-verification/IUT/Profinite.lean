/-
  IUT/Profinite.lean — M13（副有限群: 逆極限と ẑ の構成）の形式化

  遠アーベル幾何の主役 π₁^ét は**副有限群**（有限群の逆極限）である。
  本モジュールは mathlib 非依存の core Lean だけで、その理論の中核を
  「実体」として建設する（公理化ではなく全て構成と完全証明）:

  §1 商群: 群の合同関係 `GrpCong` と商群 `quotGrp`（Quot による構成）
  * M13-1 `GrpCong.inv_compat` — 合同は逆元と**自動的に**両立する
    （公理は積との両立だけで足りる: 公理系の最小性）
  * M13-2 `quotGrp` / `quotProj` — 商群の構成と射影準同型（全射）
  * M13-3 `quot_exact` — 商の分離性: mk a = mk b → a ~ b
    （Quot.lift を Prop に使う標準論法、Quotient.exact の自前版）
  * M13-4 `quot_universal` — 商群の普遍性（一意な分解）

  §2 逆系と逆極限: `InverseSystem`（有向添字・推移射・整合性）と
     逆極限群 `limitGrp`（整合族のなす群）
  * M13-5 `limitGrp` / `limitProj` — 逆極限の群構造と射影の錐
  * M13-6 `limit_universal` — **逆極限の普遍性**（錐の一意分解）。
    副有限群の圏論的特徴付けの核

  §3 ẑ = lim_n ℤ/n の具体構成（π₁^ét の最初の実例）
  * M13-7 `zmod` / `zmodSystem` / `zhat` — ℤ/n を商群として構成し、
    割り切り順序の逆系の極限として **ẑ を実際に構成**する
  * M13-8 `toZhat_injective` — 完備化 ℤ → ẑ は**単射**（ℤ の残余
    有限性）。テンパード側 π₁^temp = ℤ の情報は完備化で消えない
  * M13-9 `zmod_bounded_exponent` / `zmod_collapses_theta` — 一方、
    **各有限レベル ℤ/n は必ずテータ簿記 j ↦ j² を潰す**（M9-9 の
    具体的実例化）。「π₁^ét は塔全体としては ℤ を覚えているのに、
    どの有限段でもテータが見えない」——テンパード理論（M9）が
    必要になる現象が、ẑ の実構成の上で再現される

  **位置づけ（正直な申告）**: 副有限群の位相（コンパクト性・開部分群）
  は導入していない。逆極限は代数的に構成し、位相的内容のうち本計画で
  使う「有限レベルへの射影と整合性」「極限の普遍性」を完全証明した。
  位相を経由せずに済むのは、pro-有限群の圏 ≃ pro-(有限群) の代数側を
  直接形式化しているからである。
-/
import IUT.FundamentalGroup
import IUT.EtaleTheta

namespace IUT

/-! ## §1 商群 -/

/-- **群の合同関係**（正規部分群による剰余類別の関係版）:
    同値関係であって積と両立するもの。逆元との両立は公理に
    含めない（M13-1 で導出される）。 -/
structure GrpCong (G : Grp) where
  rel : G.carrier → G.carrier → Prop
  refl : ∀ a, rel a a
  symm : ∀ {a b}, rel a b → rel b a
  trans : ∀ {a b c}, rel a b → rel b c → rel a c
  mul_compat : ∀ {a b a' b'}, rel a a' → rel b b' → rel (G.mul a b) (G.mul a' b')

/-- **定理 (M13-1): 合同は逆元と自動的に両立する** — 群では
    積との両立だけから inv との両立が従う（公理系の最小性）。 -/
theorem GrpCong.inv_compat {G : Grp} (C : GrpCong G) {a a' : G.carrier}
    (h : C.rel a a') : C.rel (G.inv a) (G.inv a') := by
  have h1 : C.rel (G.mul (G.inv a) (G.mul a (G.inv a')))
      (G.mul (G.inv a) (G.mul a' (G.inv a'))) :=
    C.mul_compat (C.refl _) (C.mul_compat h (C.refl _))
  rw [← G.mul_assoc, G.inv_mul, G.one_mul] at h1
  rw [G.mul_inv, G.mul_one] at h1
  exact C.symm h1

/-- 商の積（Quot.lift の二重適用）。 -/
def quotMul (G : Grp) (C : GrpCong G) (x y : Quot C.rel) : Quot C.rel :=
  Quot.lift
    (fun a => Quot.lift (fun b => Quot.mk C.rel (G.mul a b))
      (fun _ _ hb => Quot.sound (C.mul_compat (C.refl a) hb)) y)
    (fun a a' ha => by
      induction y using Quot.ind
      rename_i b
      exact Quot.sound (C.mul_compat ha (C.refl b))) x

/-- **商群**（M13-2）: 合同関係による商の群構造。 -/
def quotGrp (G : Grp) (C : GrpCong G) : Grp where
  carrier := Quot C.rel
  mul := quotMul G C
  one := Quot.mk C.rel G.one
  inv := Quot.lift (fun a => Quot.mk C.rel (G.inv a))
    (fun _ _ ha => Quot.sound (C.inv_compat ha))
  mul_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    induction z using Quot.ind; rename_i c
    show Quot.mk C.rel (G.mul (G.mul a b) c) = Quot.mk C.rel (G.mul a (G.mul b c))
    rw [G.mul_assoc]
  one_mul := by
    intro x
    induction x using Quot.ind; rename_i a
    show Quot.mk C.rel (G.mul G.one a) = Quot.mk C.rel a
    rw [G.one_mul]
  inv_mul := by
    intro x
    induction x using Quot.ind; rename_i a
    show Quot.mk C.rel (G.mul (G.inv a) a) = Quot.mk C.rel G.one
    rw [G.inv_mul]

/-- 射影準同型 G → G/C。 -/
def quotProj (G : Grp) (C : GrpCong G) : Hom G (quotGrp G C) where
  map := fun a => Quot.mk C.rel a
  map_mul := fun _ _ => rfl

/-- 射影は全射。 -/
theorem quotProj_surjective (G : Grp) (C : GrpCong G) :
    ∀ x : (quotGrp G C).carrier, ∃ a, (quotProj G C).map a = x := by
  intro x
  induction x using Quot.ind; rename_i a
  exact ⟨a, rfl⟩

/-- **定理 (M13-3): 商の分離性** — mk a = mk b なら a ~ b。
    （Prop への Quot.lift による標準論法。同値関係であることが効く。） -/
theorem quot_exact (G : Grp) (C : GrpCong G) {a b : G.carrier}
    (h : Quot.mk C.rel a = Quot.mk C.rel b) : C.rel a b := by
  have hf : Quot.lift (C.rel a)
      (fun _ _ hxy => propext
        ⟨fun hax => C.trans hax hxy, fun hay => C.trans hay (C.symm hxy)⟩)
      (Quot.mk C.rel a) := C.refl a
  rw [h] at hf
  exact hf

/-- **定理 (M13-4): 商群の普遍性** — 合同を潰す準同型は商を
    一意に経由する。 -/
theorem quot_universal (G H : Grp) (C : GrpCong G) (f : Hom G H)
    (hf : ∀ {a b}, C.rel a b → f.map a = f.map b) :
    ∃ g : Hom (quotGrp G C) H,
      (∀ a, g.map ((quotProj G C).map a) = f.map a) ∧
      ∀ g' : Hom (quotGrp G C) H,
        (∀ a, g'.map ((quotProj G C).map a) = f.map a) →
        ∀ x, g'.map x = g.map x := by
  refine ⟨{ map := Quot.lift f.map (fun _ _ h => hf h), map_mul := ?_ },
    fun _ => rfl, ?_⟩
  · intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show f.map (G.mul a b) = H.mul (f.map a) (f.map b)
    exact f.map_mul a b
  · intro g' hg' x
    induction x using Quot.ind; rename_i a
    exact hg' a

/-! ## §2 逆系と逆極限 -/

/-- **逆系**: 有向前順序 (Idx, le) 上の群の族と推移射
    t : le i j → Hom (G j) (G i)（反変）、整合性条件付き。
    各 G i が有限群のとき、極限が副有限群である。 -/
structure InverseSystem where
  Idx : Type
  le : Idx → Idx → Prop
  le_refl : ∀ i, le i i
  le_trans : ∀ {i j k}, le i j → le j k → le i k
  directed : ∀ i j, ∃ k, le i k ∧ le j k
  G : Idx → Grp
  t : ∀ {i j}, le i j → Hom (G j) (G i)
  t_self : ∀ (i) (x : (G i).carrier), (t (le_refl i)).map x = x
  t_comp : ∀ {i j k} (hij : le i j) (hjk : le j k) (x : (G k).carrier),
    (t hij).map ((t hjk).map x) = (t (le_trans hij hjk)).map x

/-- 整合族: 全ての推移射と両立する切断。 -/
def Compatible (S : InverseSystem) (s : ∀ i, (S.G i).carrier) : Prop :=
  ∀ {i j : S.Idx} (h : S.le i j), (S.t h).map (s j) = s i

/-- **逆極限群**（M13-5）: 整合族のなす群（演算は成分ごと）。 -/
def limitGrp (S : InverseSystem) : Grp where
  carrier := { s : ∀ i, (S.G i).carrier // Compatible S s }
  mul := fun x y => ⟨fun i => (S.G i).mul (x.val i) (y.val i), by
    intro i j h
    rw [(S.t h).map_mul, x.property h, y.property h]⟩
  one := ⟨fun i => (S.G i).one, by
    intro i j h
    exact (S.t h).map_one⟩
  inv := fun x => ⟨fun i => (S.G i).inv (x.val i), by
    intro i j h
    rw [(S.t h).map_inv, x.property h]⟩
  mul_assoc := by
    intro x y z
    apply Subtype.ext
    funext i
    exact (S.G i).mul_assoc _ _ _
  one_mul := by
    intro x
    apply Subtype.ext
    funext i
    exact (S.G i).one_mul _
  inv_mul := by
    intro x
    apply Subtype.ext
    funext i
    exact (S.G i).inv_mul _

/-- 射影準同型（極限の錐）。 -/
def limitProj (S : InverseSystem) (i : S.Idx) : Hom (limitGrp S) (S.G i) where
  map := fun x => x.val i
  map_mul := fun _ _ => rfl

/-- 射影の錐は推移射と整合する。 -/
theorem limitProj_compat (S : InverseSystem) {i j : S.Idx} (h : S.le i j)
    (x : (limitGrp S).carrier) :
    (S.t h).map ((limitProj S j).map x) = (limitProj S i).map x :=
  x.property h

/-- **定理 (M13-6): 逆極限の普遍性** — 任意の整合錐は極限を
    一意に経由する。副有限群の圏論的特徴付けの核であり、
    「π₁^ét = Aut(ファイバー関手) が有限レベルの整合データで
    決まる」ことの形式的内容。 -/
theorem limit_universal (S : InverseSystem) (H : Grp)
    (c : ∀ i, Hom H (S.G i))
    (hc : ∀ {i j} (h : S.le i j) (x), (S.t h).map ((c j).map x) = (c i).map x) :
    ∃ u : Hom H (limitGrp S),
      (∀ i x, (limitProj S i).map (u.map x) = (c i).map x) ∧
      ∀ u' : Hom H (limitGrp S),
        (∀ i x, (limitProj S i).map (u'.map x) = (c i).map x) →
        ∀ x, u'.map x = u.map x := by
  refine ⟨{ map := fun x => ⟨fun i => (c i).map x, fun {i j} h => hc h x⟩,
            map_mul := ?_ }, fun _ _ => rfl, ?_⟩
  · intro a b
    apply Subtype.ext
    funext i
    exact (c i).map_mul a b
  · intro u' hu' x
    apply Subtype.ext
    funext i
    exact hu' i x

/-! ## §3 ẑ = lim ℤ/n の具体構成 -/

/-- 補題: N ∣ A − A。 -/
theorem dvd_sub_refl (N A : Int) : N ∣ A - A :=
  ⟨0, by rw [Int.mul_zero]; omega⟩

/-- 補題: N ∣ A − B → N ∣ B − A。 -/
theorem dvd_sub_symm {N A B : Int} (h : N ∣ A - B) : N ∣ B - A := by
  obtain ⟨k, hk⟩ := h
  exact ⟨-k, by rw [Int.mul_neg, ← hk]; omega⟩

/-- 補題: 推移性。 -/
theorem dvd_sub_trans {N A B C : Int} (h1 : N ∣ A - B) (h2 : N ∣ B - C) :
    N ∣ A - C := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  exact ⟨k + l, by rw [Int.mul_add, ← hk, ← hl]; omega⟩

/-- 補題: 和との両立。 -/
theorem dvd_sub_add {N A B C D : Int} (h1 : N ∣ A - B) (h2 : N ∣ C - D) :
    N ∣ (A + C) - (B + D) := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  exact ⟨k + l, by rw [Int.mul_add, ← hk, ← hl]; omega⟩

/-- mod n 合同（n ∣ a − b）。 -/
def modCong (n : Nat) : GrpCong intGrp where
  rel := fun (a b : Int) => ((n : Nat) : Int) ∣ (a - b)
  refl := fun a => dvd_sub_refl _ a
  symm := fun h => dvd_sub_symm h
  trans := fun h1 h2 => dvd_sub_trans h1 h2
  mul_compat := fun h1 h2 => dvd_sub_add h1 h2

/-- 有限巡回群 ℤ/n（商群としての構成）。 -/
def zmod (n : Nat) : Grp := quotGrp intGrp (modCong n)

/-- 推移射 ℤ/n → ℤ/m（m ∣ n のとき）。 -/
def zmodTrans {m n : Nat} (h : m ∣ n) : Hom (zmod n) (zmod m) where
  map := Quot.lift (fun a => Quot.mk (modCong m).rel a)
    (fun _ _ hab => Quot.sound (Int.dvd_trans (Int.ofNat_dvd.mpr h) hab))
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    rfl

/-- **ℤ/n たちの逆系**（添字 = 自然数、順序 = 割り切り）。 -/
def zmodSystem : InverseSystem where
  Idx := Nat
  le := fun m n => m ∣ n
  le_refl := Nat.dvd_refl
  le_trans := fun h1 h2 => Nat.dvd_trans h1 h2
  directed := fun m n => ⟨m * n, Nat.dvd_mul_right m n, Nat.dvd_mul_left n m⟩
  G := fun n => zmod n
  t := fun h => zmodTrans h
  t_self := by
    intro i x
    induction x using Quot.ind
    rfl
  t_comp := by
    intro i j k hij hjk x
    induction x using Quot.ind
    rfl

/-- **ẑ（ℤ の副有限完備化）の実構成**（M13-7）= π₁^ét(Tate 曲線の
    テータ被覆塔) の実例。M9 では `BoundedExponent` で抽象的に
    扱った「副有限側」が、ここで実際の逆極限として手に入る。 -/
def zhat : Grp := limitGrp zmodSystem

/-- 完備化写像 ℤ → ẑ（対角埋め込み）。 -/
def toZhat : Hom intGrp zhat where
  map := fun a => ⟨fun n => Quot.mk (modCong n).rel a, fun {_ _} _ => rfl⟩
  map_mul := fun _ _ => by
    apply Subtype.ext
    funext n
    rfl

/-- ℤ の残余有限性の算術核: 全ての n で n ∣ (A − B) なら A = B
    （n = |A−B|+1 を取る。Int 明示束縛で証明）。 -/
theorem int_residually_finite (A B : Int)
    (hn : ∀ n : Nat, ((n : Nat) : Int) ∣ (A - B)) : A = B := by
  by_cases hab : A = B
  · exact hab
  · exfalso
    obtain ⟨k, hk⟩ := hn ((A - B).natAbs + 1)
    have hNabs : (A - B).natAbs = ((A - B).natAbs + 1) * k.natAbs := by
      have h1 : (A - B).natAbs
          = ((((A - B).natAbs + 1 : Nat) : Int)).natAbs * k.natAbs := by
        rw [← Int.natAbs_mul, ← hk]
      rw [Int.natAbs_natCast] at h1
      exact h1
    cases hk0 : k.natAbs with
    | zero =>
      rw [hk0, Nat.mul_zero] at hNabs
      have h0 : A - B = 0 := Int.natAbs_eq_zero.mp hNabs
      omega
    | succ j =>
      have hj : 1 ≤ k.natAbs := by rw [hk0]; omega
      have h2 : ((A - B).natAbs + 1) * 1 ≤ ((A - B).natAbs + 1) * k.natAbs :=
        Nat.mul_le_mul (Nat.le_refl _) hj
      rw [Nat.mul_one, ← hNabs] at h2
      omega

/-- **定理 (M13-8): 完備化の単射性**（ℤ の残余有限性）—
    全ての n で n ∣ (a − b) なら a = b（n = |a−b|+1 を取る）。
    テンパード基本群 ℤ の情報は副有限完備化で失われない。 -/
theorem toZhat_injective : toZhat.Injective := by
  intro a b h
  have hval := congrArg Subtype.val h
  exact int_residually_finite a b
    (fun n => quot_exact intGrp (modCong n) (congrFun hval n))

/-- **定理 (M13-9a)**: ℤ/n は有界指数（指数 n）。M9 の有限性代理
    `BoundedExponent` が、商群として構成した実物の ℤ/n で
    実際に成立することの検証。 -/
theorem zmod_bounded_exponent (n : Nat) (hn : 0 < n) :
    BoundedExponent (zmod n) := by
  refine ⟨n, hn, ?_⟩
  intro g
  induction g using Quot.ind; rename_i a
  have hpow := (quotProj intGrp (modCong n)).map_pow a n
  show (quotGrp intGrp (modCong n)).pow ((quotProj intGrp (modCong n)).map a) n
      = (quotGrp intGrp (modCong n)).one
  rw [← hpow]
  apply Quot.sound
  show ((n : Nat) : Int) ∣ (intGrp.pow a n - 0)
  rw [intGrp_pow_eq]
  exact ⟨a, by generalize ((n : Nat) : Int) * a = T; omega⟩

/-- **定理 (M13-9b): 各有限レベルはテータ簿記を潰す** — ẑ の
    どの有限段 ℤ/n でも、テータラベル j ↦ j² は必ず退化する
    （M9-9 の具体的実例化）。M13-8 と併せて:
    **完備化は ℤ を忠実に覚えているのに、どの有限近似でも
    テータが見えない**——これが「エタールテータはテンパード
    基本群（M9）でしか扱えない」の実構成上の再現である。 -/
theorem zmod_collapses_theta (n : Nat) (hn : 0 < n) (f : Hom intGrp (zmod n)) :
    ∃ j k : Int, f.map j = f.map k ∧ j * j ≠ k * k :=
  finite_quotient_collapses_theta (zmod n) (zmod_bounded_exponent n hn) f

end IUT
