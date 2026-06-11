/-
  IUT/AbcConsequences.lean — M8（ABC 予想の帰結）の形式化

  IUT の最終出力である ABC 型不等式が「何を導くか」の古典的還元
  （M8）のうち、最も有名な帰結を機械証明する:

      **ABC（有効版・指数2）⟹ 漸近フェルマー**
      「十分大きな冪指数 n に対し x^n + y^n = z^n の原始解は存在しない」

  形式化の方針:
  * radical（互いに異なる素因数の積）は素因数分解論を避け、
    実際に使う性質のみを公理化した `RadicalAxioms` として与える:
      - rad n ≤ n
      - rad (a^k) ≤ rad a   （冪は radical を変えない。真は等号）
      - rad (a·b) ≤ rad a · rad b （真は gcd=1 で等号）
    いずれも標準的な radical が満たす事実であり、この公理化は
    主張を弱めない（公理が弱いほど定理は強い）。
  * 実数の ε を避けるため、ABC は「指数 2・定数 C」の有効版
    （Stewart–Yu 型より弱い形）で定式化する。
  * フェルマー方程式の解は原始解（gcd(x,y) = 1）に限定する
    （一般解からの還元は gcd による割り算で、ここでは扱わない）。

  証明の骨格（Granville–Tucker の標準的議論）:
    x^n + y^n = z^n, gcd = 1 に ABC を適用すると
      z^n ≤ C · rad(x^n y^n z^n)² ≤ C · (xyz)² ≤ C · (z³)² = C·z⁶
    よって z^{n−6} ≤ C。z ≥ 2 なら 2^{n−6} ≤ C となり、
    C < 2^{n−6} なる n では解が存在しない。
-/

namespace IUT

/-- radical 関数の公理的インターフェース。
    標準的な radical（distinct prime divisors の積）はこれを満たす。 -/
structure RadicalAxioms where
  rad : Nat → Nat
  /-- rad n ≤ n。 -/
  rad_le : ∀ {n : Nat}, 0 < n → rad n ≤ n
  /-- 冪を取っても radical は増えない（真は rad(a^k) = rad a）。 -/
  rad_pow_le : ∀ {a : Nat} (k : Nat), 0 < a → rad (a ^ k) ≤ rad a
  /-- 劣乗法性（真は gcd = 1 のとき等号）。 -/
  rad_mul_le : ∀ a b : Nat, rad (a * b) ≤ rad a * rad b

/-- **有効版 ABC 予想（指数 2・定数 C）**: 互いに素な a + b = c に
    対し c ≤ C · rad(abc)²。IUT IV が主張する Vojta/Szpiro 型
    不等式から従う形の、実数を避けた離散版。 -/
def ABC (R : RadicalAxioms) (C : Nat) : Prop :=
  ∀ a b c : Nat, 0 < a → 0 < b → Nat.gcd a b = 1 → a + b = c →
    c ≤ C * R.rad (a * b * c) ^ 2

/-- 補題: x^n + y^n = z^n の解では x ≤ z（y も同様）。 -/
private theorem le_of_fermat {x y z n : Nat} (hn : n ≠ 0)
    (hy : 0 < y) (heq : x ^ n + y ^ n = z ^ n) : x ≤ z := by
  rcases Nat.le_total x z with h | h
  · exact h
  · -- z ≤ x なら z^n ≤ x^n < x^n + y^n = z^n となり矛盾
    exfalso
    have h1 : z ^ n ≤ x ^ n := Nat.pow_le_pow_left h n
    have h2 : 0 < y ^ n := Nat.pow_pos hy
    omega

/-- **定理 (M8-1): ABC ⟹ 漸近フェルマー**。
    有効版 ABC（指数 2・定数 C）のもとで、C < 2^{n−6} を満たす
    すべての冪指数 n に対し、フェルマー方程式 x^n + y^n = z^n は
    原始解（gcd(x,y) = 1, z ≥ 2）を持たない。

    すなわち ABC からはフェルマーの最終定理が「有限個の n を除いて」
    従う。IUT が正しければこの種の帰結が一斉に得られる、という
    M8 の古典的内容の機械検証である。 -/
theorem abc_implies_asymptotic_fermat
    (R : RadicalAxioms) (C : Nat) (habc : ABC R C)
    {n : Nat} (hn6 : 6 ≤ n) (hC : C < 2 ^ (n - 6)) :
    ∀ x y z : Nat, 0 < x → 0 < y → 2 ≤ z → Nat.gcd x y = 1 →
      x ^ n + y ^ n ≠ z ^ n := by
  intro x y z hx hy hz hco heq
  have hn0 : n ≠ 0 := by omega
  have hzpos : 0 < z := by omega
  -- 冪も互いに素
  have hco' : Nat.gcd (x ^ n) (y ^ n) = 1 := Nat.Coprime.pow n n hco
  -- ABC を x^n + y^n = z^n に適用
  have hbound : z ^ n ≤ C * R.rad (x ^ n * y ^ n * z ^ n) ^ 2 :=
    habc _ _ _ (Nat.pow_pos hx) (Nat.pow_pos hy) hco' heq
  -- radical の評価: rad(x^n y^n z^n) ≤ xyz
  have hrx : R.rad (x ^ n) ≤ x := Nat.le_trans (R.rad_pow_le n hx) (R.rad_le hx)
  have hry : R.rad (y ^ n) ≤ y := Nat.le_trans (R.rad_pow_le n hy) (R.rad_le hy)
  have hrz : R.rad (z ^ n) ≤ z := Nat.le_trans (R.rad_pow_le n hzpos) (R.rad_le hzpos)
  have hrad : R.rad (x ^ n * y ^ n * z ^ n) ≤ x * y * z :=
    Nat.le_trans (R.rad_mul_le _ _)
      (Nat.mul_le_mul
        (Nat.le_trans (R.rad_mul_le _ _) (Nat.mul_le_mul hrx hry)) hrz)
  -- x, y ≤ z より xyz ≤ z³
  have hxz : x ≤ z := le_of_fermat hn0 hy heq
  have hyz : y ≤ z := by
    have heq' : y ^ n + x ^ n = z ^ n := by omega
    exact le_of_fermat hn0 hx heq'
  have hc3 : z ^ 3 = z * z * z := by
    simp [Nat.pow_succ]
  have hxyz : x * y * z ≤ z ^ 3 := by
    rw [hc3]
    exact Nat.mul_le_mul (Nat.mul_le_mul hxz hyz) (Nat.le_refl z)
  -- rad² ≤ (z³)² = z⁶
  have hrad6 : R.rad (x ^ n * y ^ n * z ^ n) ^ 2 ≤ z ^ 6 := by
    have h1 : R.rad (x ^ n * y ^ n * z ^ n) ^ 2 ≤ (z ^ 3) ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_trans hrad hxyz) 2
    have h2 : (z ^ 3) ^ 2 = z ^ 6 := by
      rw [← Nat.pow_mul]
    omega
  -- z^n ≤ C·z⁶
  have hmain : z ^ n ≤ C * z ^ 6 := by
    have := Nat.mul_le_mul_left C hrad6
    omega
  -- z^n = z^{n−6}·z⁶ で約して z^{n−6} ≤ C
  have hsplit : z ^ n = z ^ (n - 6) * z ^ 6 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hcancel : z ^ (n - 6) ≤ C := by
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.pow_pos hzpos (n := 6))
    omega
  -- z ≥ 2 より 2^{n−6} ≤ z^{n−6} ≤ C、仮定 C < 2^{n−6} と矛盾
  have hpow2 : 2 ^ (n - 6) ≤ z ^ (n - 6) := Nat.pow_le_pow_left hz (n - 6)
  omega

/-- **定理 (M8-2): ABC ⟹ Catalan 型方程式の有界性**。
    有効版 ABC のもとで、3^b + 1 = 2^a 型の冪の衝突
    （Catalan/Pillai 型方程式）の解は 2^a ≤ 36·C に抑えられる
    （radical(1 · 3^b · 2^a) ≤ 6 のため）。
    ABC が「冪同士は滅多に隣り合えない」ことを一律に支配する
    ことの最小の実例。 -/
theorem abc_bounds_catalan23 (R : RadicalAxioms) (C : Nat) (habc : ABC R C)
    {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (heq : 3 ^ b + 1 = 2 ^ a) : 2 ^ a ≤ C * 36 := by
  have h3 : (0 : Nat) < 3 ^ b := Nat.pow_pos (by omega)
  have h2 : (0 : Nat) < 2 ^ a := Nat.pow_pos (by omega)
  -- ABC を 1 + 3^b = 2^a に適用
  have hbound : 2 ^ a ≤ C * R.rad (1 * 3 ^ b * 2 ^ a) ^ 2 :=
    habc 1 (3 ^ b) (2 ^ a) (by omega) h3 (Nat.gcd_one_left _) (by omega)
  -- radical の評価: rad(1·3^b·2^a) ≤ 1·3·2 = 6
  have hr1 : R.rad 1 ≤ 1 := R.rad_le (by omega)
  have hr3 : R.rad (3 ^ b) ≤ 3 :=
    Nat.le_trans (R.rad_pow_le b (by omega)) (R.rad_le (by omega))
  have hr2 : R.rad (2 ^ a) ≤ 2 :=
    Nat.le_trans (R.rad_pow_le a (by omega)) (R.rad_le (by omega))
  have hrad : R.rad (1 * 3 ^ b * 2 ^ a) ≤ 6 :=
    Nat.le_trans (R.rad_mul_le _ _)
      (Nat.le_trans
        (Nat.mul_le_mul (Nat.le_trans (R.rad_mul_le _ _)
          (Nat.mul_le_mul hr1 hr3)) hr2) (by omega))
  -- rad² ≤ 36
  have hsq : R.rad (1 * 3 ^ b * 2 ^ a) ^ 2 ≤ 36 := by
    have h := Nat.pow_le_pow_left hrad 2
    have h36 : (6 : Nat) ^ 2 = 36 := rfl
    rw [h36] at h
    exact h
  exact Nat.le_trans hbound (Nat.mul_le_mul_left C hsq)

/-- 公理系の無矛盾性: 定数関数 rad ≡ 1 は `RadicalAxioms` を満たす
    （このモデルでは ABC の **仮定** が満たせなくなるだけで、
    公理系そのものは無矛盾であることが分かる）。 -/
def trivialRadical : RadicalAxioms where
  rad := fun _ => 1
  rad_le := fun h => h
  rad_pow_le := fun _ _ => Nat.le_refl 1
  rad_mul_le := fun _ _ => Nat.le_refl 1

end IUT
