/-
  IUT/UnitFiltration.lean — M31（単数 filtration U^(d) と次数商 U^(d)/U^(d+1) ≅ ℤ/p）

  局所類体論の分岐側の中心構造。主単数群 1+m = U^(1)（M30）は
  filtration U^(1) ⊃ U^(2) ⊃ …（U^(d) = 1 + p^d ℤ_p）を持ち、
  次数商 U^(d)/U^(d+1) は ℤ/p と同型になる。分岐相互法則の
  「上付き番号付け」（高次単数群と分岐群の対応）の土台。

  * M31-1 `unitFiltration` — **U^(d) は principalUnits の部分群**。
    メンバーシップは「レベル d への射影が 1」で定義（well-defined
    性が定義に組み込まれる）。逆元閉性は geomSum 0 (d+1) = 1 から
  * M31-2 `unitFiltration_full` / `unitFiltration_antitone` /
    `unitFiltration_separated` — U^(1) = 全体・単調減少・分離性
    （∩ U^(d) = {1}）
  * M31-3 `levelTheta` / `unitTheta` — **次数商写像** θ_d:
    1 + p^d u ↦ u mod p。整数除算 ediv で構成（選択公理不要）、
    商上の well-defined 性込み
  * M31-4 `unitTheta_hom` — **θ_d は準同型**: θ(xy) = θ(x) + θ(y)
    （(1+p^d u)(1+p^d v) = 1 + p^d (u+v) + p^{2d} uv と 2d ≥ d+1 から）
  * M31-5 `unitTheta_kernel` — **核 = U^(d+1)**: θ(x) = 0 ⟺ x ∈ U^(d+1)
  * M31-6 `unitTheta_surj` — **全射性**: 任意の u mod p は
    1 + p^d u の像。M31-4〜6 で U^(d)/U^(d+1) ≅ ℤ/p（第一同型定理の
    内容を hom + 核 + 全射の三点で表現、本リポジトリの標準形式）

  全て選択公理不使用。
-/
import IUT.PrincipalUnitGroup

namespace IUT

/-- 簿記補題（omega が carrier 型の演算子を読めないため Int 束縛で分離）。 -/
theorem int_add_sub_self (Q W : Int) : Q + W - Q = W := by omega

/-- 簿記補題（同上）。 -/
theorem int_add_add_sub_self (u v W : Int) : u + v + W - (u + v) = W := by omega

/-- 簿記補題（同上）: A − A' = B なら A − 1 = (A'−1) + B。 -/
theorem int_sub_one_decomp {A A' B : Int} (h : A - A' = B) :
    A - 1 = A' - 1 + B := by omega

/-- 簿記補題（同上）: AB − 1 = (A−1) + (B−1) + (A−1)(B−1)。 -/
theorem int_mul_sub_one_split (A B : Int) :
    A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_one, Int.one_mul]
  generalize A * B = Q
  omega

/-- 冪のキャスト分解: ↑(p^{d+1}) = ↑(p^d)·↑p。 -/
theorem cast_pow_succ (p d : Nat) :
    ((p ^ (d + 1) : Nat) : Int) = ((p ^ d : Nat) : Int) * ((p : Nat) : Int) := by
  rw [Nat.pow_succ, Int.natCast_mul]

/-- 幾何級数の 0 での値: Σ_{k<d+1} 0^k = 1（0^0 = 1 のみ生き残る）。 -/
theorem geomSum_zero_succ : ∀ m, geomSum (0 : Int) (m + 1) = 1 := by
  intro m
  induction m with
  | zero => show (0 : Int) + 1 = 1; omega
  | succ m ih =>
    show geomSum 0 (m + 1) + ipow 0 m * 0 = 1
    rw [Int.mul_zero, ih]
    omega

/-- **定理 (M31-1): 単数 filtration** — U^(d) = {x : 主単数 |
    x ≡ 1 mod p^d} は部分群。メンバーシップは「レベル d への射影が
    1」で定義する（代表の取り方に依存しない）。 -/
def unitFiltration (p d : Nat) : Subgroup (principalUnits p) where
  mem := fun x => x.val.val d = Quot.mk (modCong (p ^ d)).rel 1
  one_mem := rfl
  mul_mem := fun {x y} hx hy => by
    show zmodMul (p ^ d) (x.val.val d) (y.val.val d)
      = Quot.mk (modCong (p ^ d)).rel 1
    rw [hx, hy]
    show Quot.mk (modCong (p ^ d)).rel (1 * 1)
      = Quot.mk (modCong (p ^ d)).rel 1
    rw [Int.one_mul]
  inv_mem := fun {x} hx => by
    show zmodGeomInv p d (x.val.val d) = Quot.mk (modCong (p ^ d)).rel 1
    rw [hx]
    show Quot.mk (modCong (p ^ d)).rel (geomSum (1 - 1) d)
      = Quot.mk (modCong (p ^ d)).rel 1
    have h11 : (1 : Int) - 1 = 0 := by omega
    rw [h11]
    cases d with
    | zero =>
      apply Quot.sound
      show ((p ^ 0 : Nat) : Int) ∣ geomSum 0 0 - 1
      rw [Nat.pow_zero]
      exact Int.one_dvd _
    | succ m => rw [geomSum_zero_succ m]

/-- **定理 (M31-2a): U^(1) は主単数群全体** — IsPrincipalUnit の
    定義（≡ 1 mod p）そのもの。 -/
theorem unitFiltration_full (p : Nat) (x : (principalUnits p).carrier) :
    (unitFiltration p 1).mem x := by
  obtain ⟨a, ha, hpa⟩ := x.property 1
  show x.val.val 1 = Quot.mk (modCong (p ^ 1)).rel 1
  rw [ha]
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ a - 1
  rw [Nat.pow_one]
  exact dvd_sub_symm hpa

/-- **定理 (M31-2b): filtration は単調減少** — d ≤ e なら
    U^(e) ⊆ U^(d)（整合性: レベル e で 1 ならレベル d でも 1）。 -/
theorem unitFiltration_antitone (p : Nat) {d e : Nat} (h : d ≤ e)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p e).mem x) :
    (unitFiltration p d).mem x := by
  have hcomp : (zmodTrans (pow_dvd_mono p h)).map (x.val.val e) = x.val.val d :=
    x.val.property h
  show x.val.val d = Quot.mk (modCong (p ^ d)).rel 1
  rw [← hcomp, hx]
  rfl

/-- **定理 (M31-2c): filtration は分離的** — ∩_d U^(d) = {1}
    （全レベルで 1 なら元として 1。1 の近傍基をなすことの代数的内容）。 -/
theorem unitFiltration_separated (p : Nat) (x : (principalUnits p).carrier)
    (hx : ∀ d, (unitFiltration p d).mem x) : x = (principalUnits p).one := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  exact hx n

/-! ## 次数商写像 θ_d : U^(d)/U^(d+1) → ℤ/p -/

/-- **M31-3a: レベルごとの次数商写像** — a ↦ (a−1)/p^d mod p。
    整数除算 ediv による構成（選択公理不要）。well-defined 性:
    a ≡ a' mod p^{d+1} なら差は p^d·(p·k) で、ediv の加法公式から
    商の差は p·k。 -/
def levelTheta (p d : Nat) (hp : 1 ≤ p) :
    (zmod (p ^ (d + 1))).carrier → (zmod p).carrier :=
  Quot.lift
    (fun a => Quot.mk (modCong p).rel ((a - 1) / ((p ^ d : Nat) : Int)))
    (fun a a' h => Quot.sound (by
      obtain ⟨k, hk⟩ := h
      have hd0 : ((p ^ d : Nat) : Int) ≠ 0 := by
        have := pow_pos' p hp d
        omega
      have hprod : ((p : Nat) : Int) * k * ((p ^ d : Nat) : Int)
          = ((p ^ (d + 1) : Nat) : Int) * k := by
        rw [cast_pow_succ,
          Int.mul_comm (((p : Nat) : Int) * k) ((p ^ d : Nat) : Int),
          ← Int.mul_assoc]
      have he : a - 1 = (a' - 1) + ((p : Nat) : Int) * k * ((p ^ d : Nat) : Int) :=
        int_sub_one_decomp (hk.trans hprod.symm)
      refine ⟨k, ?_⟩
      rw [he, Int.add_mul_ediv_right _ _ hd0]
      exact int_add_sub_self _ _))

/-- **M31-3b: 次数商写像** θ_d : 主単数 → ℤ/p（レベル d+1 の代表で
    評価）。 -/
def unitTheta (p d : Nat) (hp : 1 ≤ p) (x : (principalUnits p).carrier) :
    (zmod p).carrier :=
  levelTheta p d hp (x.val.val (d + 1))

/-- 補題: x ∈ U^(d) なら、レベル d+1 の任意の代表 a は
    p^d ∣ a − 1 を満たす（整合性 + 商の exactness）。 -/
theorem mem_rep_dvd (p d : Nat) (x : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) (a : Int)
    (ha : x.val.val (d + 1) = Quot.mk (modCong (p ^ (d + 1))).rel a) :
    ((p ^ d : Nat) : Int) ∣ a - 1 := by
  have hcomp : (zmodTrans (pow_dvd_mono p (Nat.le_succ d))).map
      (x.val.val (d + 1)) = x.val.val d := x.val.property (Nat.le_succ d)
  rw [ha, hx] at hcomp
  have hQ : Quot.mk (modCong (p ^ d)).rel a
      = Quot.mk (modCong (p ^ d)).rel 1 := hcomp
  exact quot_exact intGrp (modCong (p ^ d)) hQ

/-- p ∣ p^d（d ≥ 1、Int キャスト版）。 -/
theorem cast_dvd_pow (p d : Nat) (hd : 1 ≤ d) :
    ((p : Nat) : Int) ∣ ((p ^ d : Nat) : Int) :=
  Int.ofNat_dvd.mpr (by
    have := pow_dvd_mono p hd
    rwa [Nat.pow_one] at this)

/-- **定理 (M31-4): θ_d は準同型** — θ(xy) = θ(x) + θ(y)。
    核心の計算: (1+p^d u)(1+p^d v) = 1 + p^d (u + v + p^d uv) で
    p^d uv ≡ 0 (mod p)（d ≥ 1）。 -/
theorem unitTheta_hom (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y) :
    unitTheta p d hp ((principalUnits p).mul x y)
      = (zmod p).mul (unitTheta p d hp x) (unitTheta p d hp y) := by
  obtain ⟨a, ha⟩ := Quot.exists_rep (x.val.val (d + 1))
  obtain ⟨b, hb⟩ := Quot.exists_rep (y.val.val (d + 1))
  obtain ⟨u, hu⟩ := mem_rep_dvd p d x hx a ha.symm
  obtain ⟨v, hv⟩ := mem_rep_dvd p d y hy b hb.symm
  have hd0 : ((p ^ d : Nat) : Int) ≠ 0 := by
    have := pow_pos' p hp d
    omega
  show levelTheta p d hp
      (zmodMul (p ^ (d + 1)) (x.val.val (d + 1)) (y.val.val (d + 1)))
    = (zmod p).mul (levelTheta p d hp (x.val.val (d + 1)))
      (levelTheta p d hp (y.val.val (d + 1)))
  rw [← ha, ← hb]
  show Quot.mk (modCong p).rel ((a * b - 1) / ((p ^ d : Nat) : Int))
    = Quot.mk (modCong p).rel
      ((a - 1) / ((p ^ d : Nat) : Int) + (b - 1) / ((p ^ d : Nat) : Int))
  have hea : (a - 1) / ((p ^ d : Nat) : Int) = u := by
    rw [hu, Int.mul_ediv_cancel_left u hd0]
  have heb : (b - 1) / ((p ^ d : Nat) : Int) = v := by
    rw [hv, Int.mul_ediv_cancel_left v hd0]
  have hsplit : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) :=
    int_mul_sub_one_split a b
  have hab : a * b - 1
      = ((p ^ d : Nat) : Int) * (u + v + u * (((p ^ d : Nat) : Int) * v)) := by
    rw [hsplit, hu, hv, Int.mul_add, Int.mul_add,
      ← Int.mul_assoc ((p ^ d : Nat) : Int) u (((p ^ d : Nat) : Int) * v)]
  have heab : (a * b - 1) / ((p ^ d : Nat) : Int)
      = u + v + u * (((p ^ d : Nat) : Int) * v) := by
    rw [hab, Int.mul_ediv_cancel_left _ hd0]
  rw [heab, hea, heb]
  apply Quot.sound
  show ((p : Nat) : Int)
    ∣ (u + v + u * (((p ^ d : Nat) : Int) * v)) - (u + v)
  obtain ⟨w, hw⟩ := cast_dvd_pow p d hd
  have hcore : u * (((p : Nat) : Int) * w * v)
      = ((p : Nat) : Int) * (u * (w * v)) := by
    rw [Int.mul_assoc ((p : Nat) : Int) w v,
      ← Int.mul_assoc u ((p : Nat) : Int) (w * v),
      Int.mul_comm u ((p : Nat) : Int), Int.mul_assoc]
  refine ⟨u * (w * v), ?_⟩
  rw [hw, hcore]
  exact int_add_add_sub_self _ _ _

/-- **定理 (M31-5): θ_d の核は U^(d+1)** — θ(x) = 0 ⟺ x ≡ 1
    mod p^{d+1}。第一同型定理の核の同定。 -/
theorem unitTheta_kernel (p d : Nat) (hp : 1 ≤ p)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x) :
    (unitTheta p d hp x = Quot.mk (modCong p).rel 0
      ↔ (unitFiltration p (d + 1)).mem x) := by
  obtain ⟨a, ha⟩ := Quot.exists_rep (x.val.val (d + 1))
  obtain ⟨u, hu⟩ := mem_rep_dvd p d x hx a ha.symm
  have hd0 : ((p ^ d : Nat) : Int) ≠ 0 := by
    have := pow_pos' p hp d
    omega
  have hea : (a - 1) / ((p ^ d : Nat) : Int) = u := by
    rw [hu, Int.mul_ediv_cancel_left u hd0]
  constructor
  · intro h
    have h' : levelTheta p d hp (x.val.val (d + 1))
        = Quot.mk (modCong p).rel 0 := h
    rw [← ha] at h'
    have hQ : Quot.mk (modCong p).rel ((a - 1) / ((p ^ d : Nat) : Int))
        = Quot.mk (modCong p).rel 0 := h'
    have hrel := quot_exact intGrp (modCong p) hQ
    rw [hea] at hrel
    have hpu : ((p : Nat) : Int) ∣ u := by
      obtain ⟨w, hw⟩ := hrel
      refine ⟨w, ?_⟩
      revert hw
      generalize ((p : Nat) : Int) * w = q
      intro hw
      omega
    obtain ⟨w, hw⟩ := hpu
    show x.val.val (d + 1) = Quot.mk (modCong (p ^ (d + 1))).rel 1
    rw [← ha]
    apply Quot.sound
    show ((p ^ (d + 1) : Nat) : Int) ∣ a - 1
    refine ⟨w, ?_⟩
    rw [hu, hw, cast_pow_succ, Int.mul_assoc]
  · intro h
    show levelTheta p d hp (x.val.val (d + 1)) = Quot.mk (modCong p).rel 0
    rw [h]
    show Quot.mk (modCong p).rel ((1 - 1) / ((p ^ d : Nat) : Int))
      = Quot.mk (modCong p).rel 0
    have h11 : (1 : Int) - 1 = 0 := by omega
    rw [h11, Int.zero_ediv]

/-- **定理 (M31-6): θ_d は全射** — 任意の u mod p は 1 + p^d u の像
    （切断の明示構成）。M31-4〜6 で **U^(d)/U^(d+1) ≅ ℤ/p**。 -/
theorem unitTheta_surj (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (c : (zmod p).carrier) :
    ∃ x : (principalUnits p).carrier,
      (unitFiltration p d).mem x ∧ unitTheta p d hp x = c := by
  obtain ⟨u, hu⟩ := Quot.exists_rep c
  have hd0 : ((p ^ d : Nat) : Int) ≠ 0 := by
    have := pow_pos' p hp d
    omega
  refine ⟨⟨(toZp p).map (1 + ((p ^ d : Nat) : Int) * u), ?_⟩, ?_, ?_⟩
  · intro n
    refine ⟨1 + ((p ^ d : Nat) : Int) * u, rfl, ?_⟩
    obtain ⟨w, hw⟩ := cast_dvd_pow p d hd
    refine ⟨-(w * u), ?_⟩
    rw [hw, Int.mul_neg, Int.mul_assoc]
    generalize ((p : Nat) : Int) * (w * u) = q
    omega
  · show Quot.mk (modCong (p ^ d)).rel (1 + ((p ^ d : Nat) : Int) * u)
      = Quot.mk (modCong (p ^ d)).rel 1
    apply Quot.sound
    refine ⟨u, ?_⟩
    generalize ((p ^ d : Nat) : Int) * u = q
    omega
  · show levelTheta p d hp
        (Quot.mk (modCong (p ^ (d + 1))).rel (1 + ((p ^ d : Nat) : Int) * u))
      = c
    rw [← hu]
    show Quot.mk (modCong p).rel
        ((1 + ((p ^ d : Nat) : Int) * u - 1) / ((p ^ d : Nat) : Int))
      = Quot.mk (modCong p).rel u
    have he : 1 + ((p ^ d : Nat) : Int) * u - 1 = ((p ^ d : Nat) : Int) * u := by
      generalize ((p ^ d : Nat) : Int) * u = q
      omega
    rw [he, Int.mul_ediv_cancel_left u hd0]

end IUT
