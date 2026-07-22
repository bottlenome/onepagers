/-
  IUT/PadicSeries.lean — M107F（柱B B-1 第三段: ℤ_p の p 進級数和の実構成）

  O = ℤ_p[[X]]/(E) の完備性（B-1 第三段）の基盤として、**各項が π^n で
  割れる級数 Σₙ π^n·g(n) の和を choice なしで実構成**する
  （witness 付きスタイル: 割れることは入力 g が担う。π = toZp p (p)）。

  鍵となる観察: レベル m での有限部分和 zpSum (zpTerm g) j は、
  j ≥ m では **値が安定する**（第 m 項以降は π^m で割れるので
  ℤ/p^m 上で消える）。この安定値をレベル m の値として採用すれば、
  整合族（= ℤ_p の元）が構成的に得られる。

  * M107F-1 `zpSum` / `zpSum_succ` — 有限部分和
  * M107F-2 `zpTerm` — 第 n 項 π^n·g(n)
  * M107F-3 `rpow_pi_val` / `rpow_pi_val_zero` — π^n のレベル m ≤ n
    での値は 0（π^n = p^n の p 進表示、p^m ∣ p^n から）
  * M107F-4 `zpTerm_val_zero` — 第 n 項のレベル m ≤ n での値は 0
  * M107F-5 `zpSum_val_stable` — 部分和のレベル m での値は
    j ≥ m で安定（第 m 項以降が寄与しないため）
  * M107F-6 `zpSeriesSum` — **級数和の実構成**（整合族 = レベル m の
    安定値。整合性は M107F-5 と各部分和自身の整合性の合成）
  * M107F-7 `zpSeriesSum_partial` — 部分和との一致（レベル m では
    m 項までの部分和に等しい）
  * M107F-8 `zpTerm_add` / `zpSum_add` / `zpSeriesSum_add` — **加法性**:
    Σ(g+h) = Σg + Σh（zpMul の分配律と有限和の並べ替えから）
  * M107F-9 `zpTerm_shift` / `zpSum_head` / `zpSeriesSum_head` —
    **頭出し分解**: Σₙπ^n g(n) = g(0) + π·Σₙπ^n g(n+1)
    （有限レベルでの帰納的恒等式を全レベルに持ち上げる）
  * M107F-10 `PadicSeriesData` / `padicSeriesData` / `padicSeries_exists`
    — 総括レコード（sum・partial_eq・sum_add・sum_head を束ねた witness）

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.LambdaSemilinear

namespace IUT

/-! ## 有限部分和と第 n 項 -/

/-- **M107F-1a: 有限部分和** zpSum f m = Σ_{k<m} f(k)（zpRing の加法で）。 -/
def zpSum (p : Nat) (f : Nat → (Zp p).carrier) : Nat → (Zp p).carrier
  | 0 => (zpRing p).zero
  | m + 1 => (zpRing p).add (zpSum p f m) (f m)

/-- **M107F-1b**: 定義の展開（rfl）。 -/
theorem zpSum_succ (p : Nat) (f : Nat → (Zp p).carrier) (m : Nat) :
    zpSum p f (m + 1) = (zpRing p).add (zpSum p f m) (f m) := rfl

/-- **M107F-2: 第 n 項** π^n·g(n)（π = toZp p (p)）。 -/
def zpTerm (p : Nat) (g : Nat → (Zp p).carrier) : Nat → (Zp p).carrier :=
  fun n => zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n) (g n)

/-! ## π^n のレベルごとの値 -/

/-- π^n のレベル m での値は p^n（の像）— 補助恒等式（m の制約なし）。 -/
theorem rpow_pi_val (p : Nat) (n m : Nat) :
    (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n).val m
      = Quot.mk (modCong (p ^ m)).rel (ipow ((p : Nat) : Int) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show zmodMul (p ^ m)
        ((rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n).val m)
        (((toZp p).map ((p : Nat) : Int)).val m)
      = Quot.mk (modCong (p ^ m)).rel (ipow ((p : Nat) : Int) (n + 1))
    rw [ih]
    rfl

/-- **定理 (M107F-3): π^n はレベル m ≤ n で 0**（p^m ∣ p^n）。 -/
theorem rpow_pi_val_zero (p : Nat) (hp : 2 ≤ p) (n m : Nat) (hmn : m ≤ n) :
    (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n).val m
      = Quot.mk (modCong (p ^ m)).rel 0 := by
  have _ := hp
  rw [rpow_pi_val p n m]
  refine Quot.sound ?_
  show ((p ^ m : Nat) : Int) ∣ (ipow ((p : Nat) : Int) n - 0)
  rw [Int.sub_zero, ← cast_pow_ipow p n]
  exact Int.ofNat_dvd.mpr (pow_dvd_mono p hmn)

/-- **定理 (M107F-4): 第 n 項はレベル m ≤ n で 0**（π^n の割り切れ性を
    zmodMul で係数 g(n) 側に伝播させる）。 -/
theorem zpTerm_val_zero (p : Nat) (hp : 2 ≤ p) (g : Nat → (Zp p).carrier)
    (n m : Nat) (hmn : m ≤ n) :
    (zpTerm p g n).val m = Quot.mk (modCong (p ^ m)).rel 0 := by
  show zmodMul (p ^ m)
      ((rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n).val m) ((g n).val m)
    = Quot.mk (modCong (p ^ m)).rel 0
  rw [rpow_pi_val_zero p hp n m hmn]
  induction (g n).val m using Quot.ind
  rename_i b
  show Quot.mk (modCong (p ^ m)).rel (0 * b) = Quot.mk (modCong (p ^ m)).rel 0
  refine Quot.sound ?_
  refine ⟨0, ?_⟩
  show (0 : Int) * b - 0 = ((p ^ m : Nat) : Int) * 0
  rw [Int.zero_mul, Int.mul_zero]
  omega

/-! ## 部分和の安定性 -/

/-- **定理 (M107F-5): 部分和のレベル m での値は j ≥ m で安定** —
    第 m 項以降は zpTerm_val_zero でレベル m 上消えるので、
    レベル m での値は j = m 以降変化しない。 -/
theorem zpSum_val_stable (p : Nat) (hp : 2 ≤ p) (g : Nat → (Zp p).carrier)
    (m : Nat) : ∀ j, m ≤ j →
    (zpSum p (zpTerm p g) j).val m = (zpSum p (zpTerm p g) m).val m := by
  intro j
  induction j with
  | zero =>
    intro hmj
    have hm0 : m = 0 := Nat.le_zero.mp hmj
    subst hm0
    rfl
  | succ j ih =>
    intro hmj
    cases Nat.lt_or_ge m (j + 1) with
    | inl hlt =>
      have hmj' : m ≤ j := by omega
      have hstep : (zpSum p (zpTerm p g) (j + 1)).val m
          = (zmod (p ^ m)).mul ((zpSum p (zpTerm p g) j).val m)
            ((zpTerm p g j).val m) := rfl
      rw [hstep, zpTerm_val_zero p hp g j m hmj']
      have hone : Quot.mk (modCong (p ^ m)).rel 0 = (zmod (p ^ m)).one := rfl
      rw [hone, Grp.mul_one]
      exact ih hmj'
    | inr hge =>
      have hm : m = j + 1 := by omega
      subst hm
      rfl

/-! ## 級数和の実構成 -/

/-- **定理 (M107F-6): p 進級数和の実構成** — レベル m の値は
    zpSum (zpTerm g) m の val m（安定値）。整合性は
    各部分和自身の整合性（Compatible）と M107F-5 の安定性の合成。
    choice 不使用: 割れることは入力 g が担い、witness は
    有限部分和の安定値として直接構成される。 -/
def zpSeriesSum (p : Nat) (hp : 2 ≤ p) (g : Nat → (Zp p).carrier) :
    (Zp p).carrier :=
  ⟨fun m => (zpSum p (zpTerm p g) m).val m, by
    intro i j h
    show (zmodTrans (pow_dvd_mono p h)).map ((zpSum p (zpTerm p g) j).val j)
      = (zpSum p (zpTerm p g) i).val i
    rw [(zpSum p (zpTerm p g) j).property h]
    exact zpSum_val_stable p hp g i j h⟩

/-- **定理 (M107F-7): 部分和との一致** — レベル m では m 項までの
    部分和に等しい。 -/
theorem zpSeriesSum_partial (p : Nat) (hp : 2 ≤ p) (g : Nat → (Zp p).carrier)
    (m : Nat) :
    (zpSeriesSum p hp g).val m = (zpSum p (zpTerm p g) m).val m := rfl

/-! ## 加法性 -/

/-- **M107F-8a: 第 n 項の加法分配** — π^n·(g(n)+h(n)) = π^n·g(n) + π^n·h(n)
    （zpMul_distrib＝zpRing の left_distrib そのもの）。 -/
theorem zpTerm_add (p : Nat) (g h : Nat → (Zp p).carrier) (n : Nat) :
    zpTerm p (fun n => (zpRing p).add (g n) (h n)) n
      = (zpRing p).add (zpTerm p g n) (zpTerm p h n) :=
  zpMul_distrib p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n) (g n) (h n)

/-- **M107F-8b: 有限和の加法分配** — zpSum (f1+f2) m = zpSum f1 m + zpSum f2 m
    （並べ替え: (A+B)+(C+D) = (A+C)+(B+D)）。 -/
theorem CRing.add_swap_mid (R : CRing) (a b c d : R.carrier) :
    R.add (R.add a b) (R.add c d) = R.add (R.add a c) (R.add b d) := by
  rw [R.add_assoc a b (R.add c d), ← R.add_assoc b c d, R.add_comm b c,
    R.add_assoc c b d, ← R.add_assoc a c (R.add b d)]

theorem zpSum_add (p : Nat) (f1 f2 : Nat → (Zp p).carrier) : ∀ m,
    zpSum p (fun n => (zpRing p).add (f1 n) (f2 n)) m
      = (zpRing p).add (zpSum p f1 m) (zpSum p f2 m) := by
  intro m
  induction m with
  | zero =>
    show (zpRing p).zero = (zpRing p).add (zpRing p).zero (zpRing p).zero
    rw [(zpRing p).zero_add]
  | succ m ih =>
    show (zpRing p).add
        (zpSum p (fun n => (zpRing p).add (f1 n) (f2 n)) m)
        ((zpRing p).add (f1 m) (f2 m))
      = (zpRing p).add
        ((zpRing p).add (zpSum p f1 m) (f1 m))
        ((zpRing p).add (zpSum p f2 m) (f2 m))
    rw [ih]
    exact CRing.add_swap_mid (zpRing p) (zpSum p f1 m) (zpSum p f2 m) (f1 m) (f2 m)

/-- **定理 (M107F-8c): 級数和の加法性** — Σ(g+h) = Σg + Σh。 -/
theorem zpSeriesSum_add (p : Nat) (hp : 2 ≤ p) (g h : Nat → (Zp p).carrier) :
    zpSeriesSum p hp (fun n => (zpRing p).add (g n) (h n))
      = (zpRing p).add (zpSeriesSum p hp g) (zpSeriesSum p hp h) := by
  refine Subtype.ext ?_
  funext m
  show (zpSum p (zpTerm p (fun n => (zpRing p).add (g n) (h n))) m).val m
    = (zmod (p ^ m)).mul
      ((zpSum p (zpTerm p g) m).val m) ((zpSum p (zpTerm p h) m).val m)
  have hterm : zpTerm p (fun n => (zpRing p).add (g n) (h n))
      = fun n => (zpRing p).add (zpTerm p g n) (zpTerm p h n) := by
    funext n
    exact zpTerm_add p g h n
  rw [hterm, zpSum_add p (zpTerm p g) (zpTerm p h) m]
  rfl

/-! ## 頭出し分解 -/

/-- **M107F-9a: 項の頭出しシフト** — π^{n+1}·g(n+1) = π·(π^n·g'(n))
    （g' = fun n => g (n+1)）。結合則・可換則の簿記のみ（zpRing の
    表現に統一して mul_comm/mul_assoc を直接適用する）。 -/
theorem zpTerm_shift (p : Nat) (g : Nat → (Zp p).carrier) (m : Nat) :
    zpTerm p g (m + 1)
      = zpMul p ((toZp p).map ((p : Nat) : Int))
        (zpTerm p (fun n => g (n + 1)) m) := by
  show (zpRing p).mul ((zpRing p).mul
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
      ((toZp p).map ((p : Nat) : Int))) (g (m + 1))
    = (zpRing p).mul ((toZp p).map ((p : Nat) : Int))
      ((zpRing p).mul (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m) (g (m + 1)))
  rw [(zpRing p).mul_comm
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
      ((toZp p).map ((p : Nat) : Int)),
    (zpRing p).mul_assoc]

/-- **M107F-9b: 有限レベルでの頭出し恒等式** —
    zpSum (zpTerm g) (m+1) = g(0) + π·zpSum (zpTerm g') m。
    m についての帰納。succ 段は add_assoc + left_distrib（zpRing の
    表現に統一）。 -/
theorem zpSum_head (p : Nat) (g : Nat → (Zp p).carrier) : ∀ m,
    zpSum p (zpTerm p g) (m + 1)
      = (zpRing p).add (g 0)
        (zpMul p ((toZp p).map ((p : Nat) : Int))
          (zpSum p (zpTerm p (fun n => g (n + 1))) m)) := by
  intro m
  induction m with
  | zero =>
    show (zpRing p).add (zpRing p).zero
        ((zpRing p).mul (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) 0) (g 0))
      = (zpRing p).add (g 0)
        ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) (zpRing p).zero)
    rw [(zpRing p).zero_add,
      CRing.mul_zero (zpRing p) ((toZp p).map ((p : Nat) : Int)),
      CRing.add_zero (zpRing p) (g 0)]
    show (zpRing p).mul (zpRing p).one (g 0) = g 0
    exact (zpRing p).one_mul (g 0)
  | succ m ih =>
    show (zpRing p).add (zpSum p (zpTerm p g) (m + 1)) (zpTerm p g (m + 1))
      = (zpRing p).add (g 0)
        (zpMul p ((toZp p).map ((p : Nat) : Int))
          ((zpRing p).add
            (zpSum p (zpTerm p (fun n => g (n + 1))) m)
            (zpTerm p (fun n => g (n + 1)) m)))
    have hA : zpSum p (zpTerm p g) (m + 1)
        = (zpRing p).add (g 0)
          (zpMul p ((toZp p).map ((p : Nat) : Int))
            (zpSum p (zpTerm p (fun n => g (n + 1))) m)) := ih
    have hB : zpTerm p g (m + 1)
        = zpMul p ((toZp p).map ((p : Nat) : Int))
          (zpTerm p (fun n => g (n + 1)) m) := zpTerm_shift p g m
    rw [hA, hB]
    have hdist : zpMul p ((toZp p).map ((p : Nat) : Int))
        ((zpRing p).add
          (zpSum p (zpTerm p (fun n => g (n + 1))) m)
          (zpTerm p (fun n => g (n + 1)) m))
        = (zpRing p).add
          (zpMul p ((toZp p).map ((p : Nat) : Int))
            (zpSum p (zpTerm p (fun n => g (n + 1))) m))
          (zpMul p ((toZp p).map ((p : Nat) : Int))
            (zpTerm p (fun n => g (n + 1)) m)) :=
      zpMul_distrib p ((toZp p).map ((p : Nat) : Int))
        (zpSum p (zpTerm p (fun n => g (n + 1))) m)
        (zpTerm p (fun n => g (n + 1)) m)
    rw [hdist]
    exact (zpRing p).add_assoc (g 0)
      (zpMul p ((toZp p).map ((p : Nat) : Int))
        (zpSum p (zpTerm p (fun n => g (n + 1))) m))
      (zpMul p ((toZp p).map ((p : Nat) : Int))
        (zpTerm p (fun n => g (n + 1)) m))

/-- **定理 (M107F-9c): 頭出し分解** —
    Σₙπ^n g(n) = g(0) + π·Σₙπ^n g(n+1)。M107F-9b の有限恒等式を
    レベル m で M107F-5 の安定性（j = m+1 への伸長）を介して
    全レベルに持ち上げる。 -/
theorem zpSeriesSum_head (p : Nat) (hp : 2 ≤ p) (g : Nat → (Zp p).carrier) :
    zpSeriesSum p hp g
      = (zpRing p).add (g 0)
        (zpMul p ((toZp p).map ((p : Nat) : Int))
          (zpSeriesSum p hp (fun n => g (n + 1)))) := by
  refine Subtype.ext ?_
  funext m
  show (zpSum p (zpTerm p g) m).val m
    = (zmod (p ^ m)).mul ((g 0).val m)
      (zmodMul (p ^ m) (((toZp p).map ((p : Nat) : Int)).val m)
        ((zpSum p (zpTerm p (fun n => g (n + 1))) m).val m))
  have hstab := zpSum_val_stable p hp g m (m + 1) (Nat.le_succ m)
  rw [← hstab, zpSum_head p g m]
  rfl

/-! ## 総括レコード -/

/-- **定理 (M107F-10a): p 進級数和のインターフェース** — 級数和の写像
    sum とその特徴づけ（部分和との一致・加法性・頭出し分解）を
    束ねた構造。O の完備性証明で使う統一インターフェース。 -/
structure PadicSeriesData (p : Nat) (hp : 2 ≤ p) where
  sum : (Nat → (Zp p).carrier) → (Zp p).carrier
  partial_eq : ∀ (g : Nat → (Zp p).carrier) (m : Nat),
    (sum g).val m = (zpSum p (zpTerm p g) m).val m
  sum_add : ∀ g h : Nat → (Zp p).carrier,
    sum (fun n => (zpRing p).add (g n) (h n))
      = (zpRing p).add (sum g) (sum h)
  sum_head : ∀ g : Nat → (Zp p).carrier,
    sum g = (zpRing p).add (g 0)
      (zpMul p ((toZp p).map ((p : Nat) : Int)) (sum (fun n => g (n + 1))))

/-- **定理 (M107F-10b): witness** — zpSeriesSum が
    PadicSeriesData を完全証明で充足する（choice 不使用）。 -/
def padicSeriesData (p : Nat) (hp : 2 ≤ p) : PadicSeriesData p hp where
  sum := zpSeriesSum p hp
  partial_eq := zpSeriesSum_partial p hp
  sum_add := zpSeriesSum_add p hp
  sum_head := zpSeriesSum_head p hp

/-- **定理 (M107F-10c)**: PadicSeriesData は充足可能（witness 存在）。 -/
theorem padicSeries_exists (p : Nat) (hp : 2 ≤ p) : Nonempty (PadicSeriesData p hp) :=
  ⟨padicSeriesData p hp⟩

end IUT
