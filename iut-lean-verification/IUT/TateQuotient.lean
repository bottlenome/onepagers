/-
  IUT/TateQuotient.lean — M91（Tate 点群 G/q^ℤ: 柱E・E6）

  Tate 曲線の点群 ℚ_p^×/q^ℤ の骨格を、**中心元 q を持つ任意の群 G の
  q^ℤ 商**として構成する（ℚ_p^× は可換なので任意の q に適用可）。
  設計の鍵は **Tate 関係を 2 つの自然数冪で対称に定義**すること:
  x ~ y :⟺ ∃ a b : Nat, q^a x = q^b y。これで整数冪 q^n（符号の
  場合分け地獄）を一切持ち込まずに反射・対称・推移・演算両立が
  Nat 冪の加法則 pow_add だけで閉じ、選択公理も不要になる。

  商群 tateGrp は Quot で構成（群公理は全て congrArg 一発）。
  **本丸は tate_shift_trivial: 代入 u ↦ q^j u（M89/M90 の作用素 T の
  幾何側）は Tate 商上で恒等** — テータの関数等式が「Tate 点上の
  値の well-definedness」を意味する理由の形式化。核の特徴付け
  tate_ker（ker = q^ℤ）は Quot.exact を使わず propext lift の
  標準トリックで抽出（choice なし）。検算: デッキ群 ℤ（M9 の
  intGrp）を生成元で割ると一点に潰れる。

  * M91-1 `Grp.pow_add` / `pow_mul_comm` / `mul_inv_rev` /
    `Central` / `central_pow` / `central_pow_inv` — 群論の補給
  * M91-2 `tateRel` と同値関係性・演算両立（mul・inv）
  * M91-3 `tateGrp` / `tateOf` — **q^ℤ 商群と射影準同型**
  * M91-4 `tate_exact` / `tate_q_one` / `tate_ker` — q ↦ 1・核 = q^ℤ
  * M91-5 `tate_shift_trivial` — **u ↦ q^j u は Tate 商上で恒等（本丸）**
  * M91-6 `tate_deck_collapse` — 検算: ℤ/⟨1⟩ は一点

  ℚ_p^× の実装（p^ℤ × ℤ_p^× 分解 M37 との接続）・q の無限位数・
  捻れ点 q^{j/N} の具体化（mono-theta E7）は次層。
  全て選択公理不使用。
-/
import IUT.EtaleTheta

namespace IUT

/-! ## 群論の補給 -/

/-- **M91-1a: Nat 冪の加法則** g^{a+b} = g^a g^b。 -/
theorem Grp.pow_add (G : Grp) (g : G.carrier) :
    ∀ a b, G.pow g (a + b) = G.mul (G.pow g a) (G.pow g b) := by
  intro a
  induction a with
  | zero =>
    intro b
    have h : 0 + b = b := by omega
    rw [h]
    show G.pow g b = G.mul G.one (G.pow g b)
    rw [G.one_mul]
  | succ a ih =>
    intro b
    have h : a + 1 + b = (a + b) + 1 := by omega
    rw [h]
    show G.mul g (G.pow g (a + b)) = G.mul (G.mul g (G.pow g a)) (G.pow g b)
    rw [ih b]
    exact (G.mul_assoc g _ _).symm

/-- **M91-1b: 同一元の冪同士は可換**。 -/
theorem Grp.pow_mul_comm (G : Grp) (g : G.carrier) (a b : Nat) :
    G.mul (G.pow g a) (G.pow g b) = G.mul (G.pow g b) (G.pow g a) := by
  rw [← Grp.pow_add, ← Grp.pow_add, Nat.add_comm]

/-- **M91-1c: 積の逆元** (ab)⁻¹ = b⁻¹a⁻¹。 -/
theorem Grp.mul_inv_rev (G : Grp) (a b : G.carrier) :
    G.inv (G.mul a b) = G.mul (G.inv b) (G.inv a) := by
  refine (G.inv_eq_of_mul_eq_one ?_).symm
  rw [G.mul_assoc a b, ← G.mul_assoc b (G.inv b), G.mul_inv, G.one_mul,
    G.mul_inv]

/-- **M91-1d: 中心性** — q が全元と可換。 -/
def Grp.Central (G : Grp) (q : G.carrier) : Prop :=
  ∀ x, G.mul q x = G.mul x q

/-- **M91-1e: 中心元の冪も中心**。 -/
theorem Grp.central_pow (G : Grp) (q : G.carrier) (hq : G.Central q) :
    ∀ a x, G.mul (G.pow q a) x = G.mul x (G.pow q a) := by
  intro a
  induction a with
  | zero => intro x; show G.mul G.one x = G.mul x G.one; rw [G.one_mul, G.mul_one]
  | succ a ih =>
    intro x
    show G.mul (G.mul q (G.pow q a)) x = G.mul x (G.mul q (G.pow q a))
    rw [G.mul_assoc, ih x, ← G.mul_assoc, hq x, G.mul_assoc]

/-- **M91-1f: 中心元の冪の逆元も中心**。 -/
theorem Grp.central_pow_inv (G : Grp) (q : G.carrier) (hq : G.Central q)
    (a : Nat) (x : G.carrier) :
    G.mul (G.inv (G.pow q a)) x = G.mul x (G.inv (G.pow q a)) := by
  have h1 : G.mul (G.pow q a) (G.mul (G.inv (G.pow q a)) x) = x := by
    rw [← G.mul_assoc, G.mul_inv, G.one_mul]
  have h2 : G.mul (G.pow q a) (G.mul x (G.inv (G.pow q a))) = x := by
    rw [← G.mul_assoc, Grp.central_pow G q hq a x, G.mul_assoc, G.mul_inv,
      G.mul_one]
  exact G.mul_left_cancel (h1.trans h2.symm)

/-! ## Tate 関係（2 つの Nat 冪による対称定義） -/

/-- **M91-2a: Tate 関係** x ~ y :⟺ ∃ a b, q^a x = q^b y。
    整数冪を回避する対称な定式化。 -/
def tateRel (G : Grp) (q : G.carrier) (x y : G.carrier) : Prop :=
  ∃ a b : Nat, G.mul (G.pow q a) x = G.mul (G.pow q b) y

theorem tateRel_refl (G : Grp) (q x : G.carrier) : tateRel G q x x :=
  ⟨0, 0, rfl⟩

theorem tateRel_symm (G : Grp) (q : G.carrier) {x y : G.carrier}
    (h : tateRel G q x y) : tateRel G q y x := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨b, a, hab.symm⟩

theorem tateRel_trans (G : Grp) (q : G.carrier) {x y z : G.carrier}
    (h1 : tateRel G q x y) (h2 : tateRel G q y z) : tateRel G q x z := by
  obtain ⟨a, b, hab⟩ := h1
  obtain ⟨c, d, hcd⟩ := h2
  refine ⟨c + a, b + d, ?_⟩
  calc G.mul (G.pow q (c + a)) x
      = G.mul (G.mul (G.pow q c) (G.pow q a)) x := by rw [Grp.pow_add]
    _ = G.mul (G.pow q c) (G.mul (G.pow q a) x) := G.mul_assoc _ _ _
    _ = G.mul (G.pow q c) (G.mul (G.pow q b) y) := by rw [hab]
    _ = G.mul (G.mul (G.pow q c) (G.pow q b)) y := (G.mul_assoc _ _ _).symm
    _ = G.mul (G.mul (G.pow q b) (G.pow q c)) y := by
        rw [Grp.pow_mul_comm G q c b]
    _ = G.mul (G.pow q b) (G.mul (G.pow q c) y) := G.mul_assoc _ _ _
    _ = G.mul (G.pow q b) (G.mul (G.pow q d) z) := by rw [hcd]
    _ = G.mul (G.mul (G.pow q b) (G.pow q d)) z := (G.mul_assoc _ _ _).symm
    _ = G.mul (G.pow q (b + d)) z := by rw [← Grp.pow_add]

/-- **M91-2b: 積は Tate 関係を保つ**（q の中心性を使用）。 -/
theorem tateRel_mul (G : Grp) (q : G.carrier) (hq : G.Central q)
    {x x' y y' : G.carrier} (hx : tateRel G q x x') (hy : tateRel G q y y') :
    tateRel G q (G.mul x y) (G.mul x' y') := by
  obtain ⟨a, b, h1⟩ := hx
  obtain ⟨c, d, h2⟩ := hy
  refine ⟨a + c, b + d, ?_⟩
  calc G.mul (G.pow q (a + c)) (G.mul x y)
      = G.mul (G.mul (G.pow q a) (G.pow q c)) (G.mul x y) := by
        rw [Grp.pow_add]
    _ = G.mul (G.pow q a) (G.mul (G.pow q c) (G.mul x y)) := G.mul_assoc _ _ _
    _ = G.mul (G.pow q a) (G.mul (G.mul (G.pow q c) x) y) := by
        rw [← G.mul_assoc (G.pow q c) x y]
    _ = G.mul (G.pow q a) (G.mul (G.mul x (G.pow q c)) y) := by
        rw [Grp.central_pow G q hq c x]
    _ = G.mul (G.pow q a) (G.mul x (G.mul (G.pow q c) y)) := by
        rw [G.mul_assoc x (G.pow q c) y]
    _ = G.mul (G.pow q a) (G.mul x (G.mul (G.pow q d) y')) := by rw [h2]
    _ = G.mul (G.mul (G.pow q a) x) (G.mul (G.pow q d) y') :=
        (G.mul_assoc _ _ _).symm
    _ = G.mul (G.mul (G.pow q b) x') (G.mul (G.pow q d) y') := by rw [h1]
    _ = G.mul (G.pow q b) (G.mul x' (G.mul (G.pow q d) y')) := G.mul_assoc _ _ _
    _ = G.mul (G.pow q b) (G.mul (G.mul x' (G.pow q d)) y') := by
        rw [← G.mul_assoc x' (G.pow q d) y']
    _ = G.mul (G.pow q b) (G.mul (G.mul (G.pow q d) x') y') := by
        rw [← Grp.central_pow G q hq d x']
    _ = G.mul (G.pow q b) (G.mul (G.pow q d) (G.mul x' y')) := by
        rw [G.mul_assoc (G.pow q d) x' y']
    _ = G.mul (G.mul (G.pow q b) (G.pow q d)) (G.mul x' y') :=
        (G.mul_assoc _ _ _).symm
    _ = G.mul (G.pow q (b + d)) (G.mul x' y') := by rw [← Grp.pow_add]

/-- **M91-2c: 逆元は Tate 関係を保つ**。 -/
theorem tateRel_inv (G : Grp) (q : G.carrier) (hq : G.Central q)
    {x y : G.carrier} (h : tateRel G q x y) :
    tateRel G q (G.inv x) (G.inv y) := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨b, a, ?_⟩
  have h1 := congrArg G.inv hab
  rw [Grp.mul_inv_rev, Grp.mul_inv_rev,
    ← Grp.central_pow_inv G q hq a (G.inv x),
    ← Grp.central_pow_inv G q hq b (G.inv y)] at h1
  -- h1 : (q^a)⁻¹ x⁻¹ = (q^b)⁻¹ y⁻¹ — 左から q^b q^a を掛けて整理
  have h2 : G.mul (G.mul (G.pow q b) (G.pow q a))
        (G.mul (G.inv (G.pow q a)) (G.inv x))
      = G.mul (G.mul (G.pow q b) (G.pow q a))
        (G.mul (G.inv (G.pow q b)) (G.inv y)) :=
    congrArg (G.mul (G.mul (G.pow q b) (G.pow q a))) h1
  rw [G.mul_assoc (G.pow q b) (G.pow q a),
    ← G.mul_assoc (G.pow q a) (G.inv (G.pow q a)), G.mul_inv, G.one_mul,
    Grp.pow_mul_comm G q b a,
    G.mul_assoc (G.pow q a) (G.pow q b),
    ← G.mul_assoc (G.pow q b) (G.inv (G.pow q b)), G.mul_inv, G.one_mul]
    at h2
  exact h2

/-! ## Tate 商群 -/

/-- 商の積（二重 Quot.lift）。 -/
def tateMul (G : Grp) (q : G.carrier) (hq : G.Central q) :
    Quot (tateRel G q) → Quot (tateRel G q) → Quot (tateRel G q) :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk (tateRel G q) (G.mul x y))
      (fun y y' hy =>
        Quot.sound (tateRel_mul G q hq (tateRel_refl G q x) hy)))
    (fun x x' hx => by
      funext z
      induction z using Quot.ind
      rename_i y
      exact Quot.sound (tateRel_mul G q hq hx (tateRel_refl G q y)))

/-- 商の逆元。 -/
def tateInv (G : Grp) (q : G.carrier) (hq : G.Central q) :
    Quot (tateRel G q) → Quot (tateRel G q) :=
  Quot.lift (fun x => Quot.mk (tateRel G q) (G.inv x))
    (fun x x' hx => Quot.sound (tateRel_inv G q hq hx))

/-- **M91-3a: Tate 商群** G/q^ℤ（群公理は全て congrArg 一発）。 -/
def tateGrp (G : Grp) (q : G.carrier) (hq : G.Central q) : Grp where
  carrier := Quot (tateRel G q)
  mul := tateMul G q hq
  one := Quot.mk (tateRel G q) G.one
  inv := tateInv G q hq
  mul_assoc := by
    intro a b c
    induction a using Quot.ind
    rename_i x
    induction b using Quot.ind
    rename_i y
    induction c using Quot.ind
    rename_i z
    exact congrArg (Quot.mk (tateRel G q)) (G.mul_assoc x y z)
  one_mul := by
    intro a
    induction a using Quot.ind
    rename_i x
    exact congrArg (Quot.mk (tateRel G q)) (G.one_mul x)
  inv_mul := by
    intro a
    induction a using Quot.ind
    rename_i x
    exact congrArg (Quot.mk (tateRel G q)) (G.inv_mul x)

/-- **M91-3b: 射影準同型** G → G/q^ℤ。 -/
def tateOf (G : Grp) (q : G.carrier) (hq : G.Central q) :
    Hom G (tateGrp G q hq) where
  map := Quot.mk (tateRel G q)
  map_mul := fun _ _ => rfl

/-! ## 核の特徴付けと本丸 -/

/-- **M91-4a: Quot 等式からの関係抽出**（propext lift の標準トリック、
    choice なし）。 -/
theorem tate_exact (G : Grp) (q : G.carrier) {x y : G.carrier}
    (h : Quot.mk (tateRel G q) x = Quot.mk (tateRel G q) y) :
    tateRel G q x y := by
  have hresp : ∀ z w : G.carrier, tateRel G q z w →
      tateRel G q x z = tateRel G q x w := fun z w hzw =>
    propext ⟨fun hxz => tateRel_trans G q hxz hzw,
      fun hxw => tateRel_trans G q hxw (tateRel_symm G q hzw)⟩
  have h2 : tateRel G q x x = tateRel G q x y :=
    congrArg (Quot.lift (fun z => tateRel G q x z) hresp) h
  exact h2 ▸ tateRel_refl G q x

/-- **M91-4b: q は商で 1 に**。 -/
theorem tate_q_one (G : Grp) (q : G.carrier) (hq : G.Central q) :
    (tateOf G q hq).map q = (tateGrp G q hq).one :=
  Quot.sound ⟨0, 1, by
    show G.mul G.one q = G.mul (G.mul q G.one) G.one
    rw [G.one_mul, G.mul_one, G.mul_one]⟩

/-- **M91-4c: 核の特徴付け** — ker(tateOf) = q^ℤ
    （x ↦ 1 ⟺ ∃ a b, q^a x = q^b）。 -/
theorem tate_ker (G : Grp) (q : G.carrier) (hq : G.Central q)
    (x : G.carrier) :
    ((tateOf G q hq).map x = (tateGrp G q hq).one
      ↔ ∃ a b : Nat, G.mul (G.pow q a) x = G.pow q b) := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := tate_exact G q h
    rw [G.mul_one] at hab
    exact ⟨a, b, hab⟩
  · intro ⟨a, b, hab⟩
    refine Quot.sound ⟨a, b, ?_⟩
    rw [G.mul_one]
    exact hab

/-- **定理 (M91-5): 代入 u ↦ q^j u は Tate 商上で恒等（本丸）** —
    M89/M90 の作用素 T^j の幾何側（デッキ変換）が Tate 点群では
    見えない = テータの値が Tate 点上 well-defined になる理由。 -/
theorem tate_shift_trivial (G : Grp) (q : G.carrier) (hq : G.Central q)
    (j : Nat) (x : G.carrier) :
    (tateOf G q hq).map (G.mul (G.pow q j) x) = (tateOf G q hq).map x :=
  Quot.sound ⟨0, j, by
    show G.mul G.one (G.mul (G.pow q j) x) = G.mul (G.pow q j) x
    rw [G.one_mul]⟩

/-! ## 検算: デッキ群 ℤ -/

/-- intGrp の全元は中心（可換群）。 -/
theorem intGrp_central (g : Int) : intGrp.Central g :=
  fun x => Int.add_comm g x

/-- **M91-6: 検算** — デッキ群 ℤ（M9）を生成元 1 で割ると一点に
    潰れる（ℤ/⟨1⟩ = 0）。 -/
theorem tate_deck_collapse (x : Int) :
    (tateOf intGrp 1 (intGrp_central 1)).map x
      = (tateGrp intGrp 1 (intGrp_central 1)).one :=
  Quot.sound ⟨(-x).toNat, x.toNat, by
    rw [intGrp_pow_one, intGrp_pow_one]
    show ((-x).toNat : Int) + x = (x.toNat : Int) + 0
    omega⟩

end IUT
