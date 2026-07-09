/-
  IUT/PadicValuationQ.lean — 実 p 進付値 v_p : ℚ^× → ℤ の本物構成

  分類: [実] / complete_pct 影響: あり見込み（実素点 place at p の入口:
  有理数体 ℚ 上の実 p 進付値を本物の ℤ 値として構成し、加法性
  v_p(xy) = v_p(x) + v_p(y) と well-defined（ratRel 不変）を本物証明）。
  監査が名指しした「実素点の不在」を、模型・身代わりを一切使わずに埋める。

  * `pvqAux` / `pvqNatVal` — 自然数 n を割る p の最大冪の指数
    v_p(n)（fuel 有界再帰、fuel = n）。本物の整除で定義。
  * `pvqAux_spec` / `pvqNatVal_spec` — 一意性: n = p^k·n'（p∤n', n'≥1）
    なら v_p(n) = k（k の帰納、prime_pow_extract の指数を回収）。
  * `pvq_natval_mul` — **加法性（自然数版）** v_p(mn) = v_p(m)+v_p(n)
    （m,n≥1・p 素数）: prime_pow_extract で m=p^a·m', n=p^b·n' に分解し
    Euclid の補題で p∤m'n' を得て mn = p^(a+b)·(m'n') に spec を適用。
  * `pvqVal` — 有理数（PreRat 代表）の p 進付値
    v_p(x) = v_p(|num|) − v_p(den) ∈ ℤ。本物の ℤ 値。
  * `pvq_val_wd` — **well-defined** ratRel 同値な代表で不変（非零代表）。
    交差積 num·den の natAbs 乗法性 + 加法性で閉じる。
  * `pvq_val_mul` — **本丸: 加法性** v_p(xy) = v_p(x)+v_p(y)（非零 x,y）。
  * `pvq_val_p` — 健全性 v_p(p) = 1（p 素数）。
  * `PadicValData` / `pvq_exists` — capstone（付値のデータ束と存在）。

  正直な限定: ℚ = Quot ratRel の商上ではゼロ判定選言が排中律を要するため、
  付値は QRat 全域への Quot.lift ではなく **PreRat 代表上で定義し、非零
  代表 (num ≠ 0) に対する ratRel 不変性（pvq_val_wd）として well-defined を
  与える**（これが ℚ^× 上の付値の choice なし忠実版）。v_p(0) = +∞ は Int に
  収まらないため対象外（非零元のみ）。加法性が成り立つのは p が素数のとき
  のみ（例: v_4(2·2) ≠ v_4(2)+v_4(2)）で、素数仮定 IsPrime p を明示。

  全て選択公理不使用・sorry なし。§2(b) 本物建設。
-/
import IUT.NatPrimeParts
import IUT.Rationals

namespace IUT

/-! ## 補助: 2 ≤ p のとき k < p^k -/

/-- **底の指数下界** — 2 ≤ p なら k < p^k（k の帰納、p^(k+1) ≥ 2·p^k）。
    fuel = n が再帰深度 k+1 を上回ることの保証に使う。 -/
theorem nat_lt_pow (p : Nat) (hp : 2 ≤ p) : ∀ k, k < p ^ k := by
  intro k
  induction k with
  | zero =>
    show 0 < p ^ 0
    rw [Nat.pow_zero]
    omega
  | succ k ih =>
    have hpk : 0 < p ^ k := Nat.pow_pos (by omega)
    have h1 : p ^ (k + 1) = p ^ k * p := Nat.pow_succ p k
    have h2 : p ^ k * 2 ≤ p ^ k * p := Nat.mul_le_mul (Nat.le_refl (p ^ k)) hp
    rw [← h1] at h2
    omega

/-! ## p 進指数 v_p(n)（自然数）: fuel 有界再帰 -/

/-- **v_p(n) の fuel 付き再帰核** — n が p で割れる限り n/p に降りて指数を
    数える。n = 0 は保護（p ∣ 0 が真でも数えない）。fuel で停止性を確保。 -/
def pvqAux (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if p ∣ n ∧ n ≠ 0 then pvqAux p fuel (n / p) + 1 else 0

/-- 展開等式（fuel の後続段、rfl）。 -/
theorem pvqAux_succ (p fuel n : Nat) :
    pvqAux p (fuel + 1) n =
      if p ∣ n ∧ n ≠ 0 then pvqAux p fuel (n / p) + 1 else 0 := rfl

/-- **v_p(n)** — fuel = n を与えた p 進指数（n が p で割れる回数）。 -/
def pvqNatVal (p n : Nat) : Nat := pvqAux p n n

/-! ## 一意性（spec）: n = p^k·n'（p∤n'）なら v_p(n) = k -/

/-- **spec の fuel 版** — p∤n'・n'≥1・fuel ≥ k+1 なら
    pvqAux p fuel (p^k·n') = k（k の帰納）。降段 (p^{k+1}n')/p = p^k·n'
    は `Nat.mul_div_cancel_left`、条件 p ∣ p^{k+1}n' は明示 witness。 -/
theorem pvqAux_spec (p : Nat) (hp : 2 ≤ p) (n' : Nat)
    (hn' : ¬ p ∣ n') (hn'pos : 1 ≤ n') :
    ∀ k fuel, k + 1 ≤ fuel → pvqAux p fuel (p ^ k * n') = k := by
  intro k
  induction k with
  | zero =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      rw [Nat.pow_zero, Nat.one_mul, pvqAux_succ, if_neg (fun h => hn' h.1)]
  | succ k ih =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      have hf : k + 1 ≤ f := by omega
      have hppos : 0 < p := by omega
      have hpk : 0 < p ^ k * n' := Nat.mul_pos (Nat.pow_pos hppos) (by omega)
      have hN : p ^ (k + 1) * n' = p * (p ^ k * n') := by
        rw [Nat.pow_succ, Nat.mul_comm (p ^ k) p, Nat.mul_assoc]
      have hdvd : p ∣ p ^ (k + 1) * n' := ⟨p ^ k * n', hN⟩
      have hpos : 0 < p ^ (k + 1) * n' := by rw [hN]; exact Nat.mul_pos hppos hpk
      rw [pvqAux_succ, if_pos ⟨hdvd, by omega⟩]
      have hdiv : (p ^ (k + 1) * n') / p = p ^ k * n' := by
        rw [hN]; exact Nat.mul_div_cancel_left (p ^ k * n') hppos
      rw [hdiv, ih f hf]

/-- **v_p(p^k·n') = k** — fuel = p^k·n' が k+1 を上回る（nat_lt_pow）ので
    spec が発火。付値の一意性（所属レベルが冪指数を切り出す）の井戸定義性。 -/
theorem pvqNatVal_spec (p : Nat) (hp : 2 ≤ p) (k n' : Nat)
    (hn' : ¬ p ∣ n') (hn'pos : 1 ≤ n') :
    pvqNatVal p (p ^ k * n') = k := by
  have hlt : k < p ^ k := nat_lt_pow p hp k
  have h1 : p ^ k ≤ p ^ k * n' := by
    have h := Nat.mul_le_mul (Nat.le_refl (p ^ k)) hn'pos
    rw [Nat.mul_one] at h
    exact h
  have hb : k + 1 ≤ p ^ k * n' := by omega
  show pvqAux p (p ^ k * n') (p ^ k * n') = k
  exact pvqAux_spec p hp n' hn' hn'pos k (p ^ k * n') hb

/-! ## 加法性（自然数版）: v_p(mn) = v_p(m)+v_p(n) -/

/-- **加法性（自然数版）** — p 素数・m,n ≥ 1 なら v_p(mn) = v_p(m)+v_p(n)。
    prime_pow_extract で m = p^a·m'（p∤m'）, n = p^b·n'（p∤n'）に分解し、
    Euclid の補題（euclid）で p∤m'n' を得て mn = p^(a+b)·(m'n') に
    pvqNatVal_spec を適用。指数の一意性から加法性が本物に落ちる。 -/
theorem pvq_natval_mul (p : Nat) (hp : IsPrime p) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    pvqNatVal p (m * n) = pvqNatVal p m + pvqNatVal p n := by
  have hp2 : 2 ≤ p := hp.1
  obtain ⟨a, m', hm', hqm'⟩ := prime_pow_extract p hp m hm
  obtain ⟨b, n', hn', hqn'⟩ := prime_pow_extract p hp n hn
  have hm'pos : 1 ≤ m' := by
    cases Nat.eq_zero_or_pos m' with
    | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hm'; omega
    | inr h => exact h
  have hn'pos : 1 ≤ n' := by
    cases Nat.eq_zero_or_pos n' with
    | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hn'; omega
    | inr h => exact h
  have hvm : pvqNatVal p m = a := by
    rw [hm']; exact pvqNatVal_spec p hp2 a m' hqm' hm'pos
  have hvn : pvqNatVal p n = b := by
    rw [hn']; exact pvqNatVal_spec p hp2 b n' hqn' hn'pos
  have hmn : m * n = p ^ (a + b) * (m' * n') := by
    rw [hm', hn', Nat.pow_add, Nat.mul_assoc (p ^ a) m' (p ^ b * n'),
      ← Nat.mul_assoc m' (p ^ b) n', Nat.mul_comm m' (p ^ b),
      Nat.mul_assoc (p ^ b) m' n', ← Nat.mul_assoc (p ^ a) (p ^ b) (m' * n')]
  have hcop : ¬ p ∣ (m' * n') := by
    intro hd
    cases euclid p hp hd with
    | inl h => exact hqm' h
    | inr h => exact hqn' h
  have hvmn : pvqNatVal p (m * n) = a + b := by
    rw [hmn]
    exact pvqNatVal_spec p hp2 (a + b) (m' * n') hcop (Nat.mul_pos hm'pos hn'pos)
  rw [hvmn, hvm, hvn]

/-! ## 有理数の p 進付値 v_p : ℚ^× → ℤ -/

/-- **v_p(x)** — 有理数（PreRat 代表 x = num/den）の p 進付値
    = v_p(|num|) − v_p(den) ∈ ℤ。本物の ℤ 値（正なら分子側、負なら分母側に
    符号）。非零元 (num ≠ 0) に対して意味を持つ。 -/
def pvqVal (p : Nat) (x : PreRat) : Int :=
  (pvqNatVal p x.num.natAbs : Int) - (pvqNatVal p x.den.natAbs : Int)

/-- 非零分子は natAbs ≥ 1。 -/
theorem natAbs_pos_of_ne {a : Int} (ha : a ≠ 0) : 1 ≤ a.natAbs := by
  cases Nat.eq_zero_or_pos a.natAbs with
  | inl h0 => exfalso; exact ha (Int.natAbs_eq_zero.mp h0)
  | inr h => exact h

/-- 正分母は natAbs ≥ 1。 -/
theorem natAbs_den_pos (x : PreRat) : 1 ≤ x.den.natAbs := by
  cases Nat.eq_zero_or_pos x.den.natAbs with
  | inl h0 =>
    exfalso
    have hz : x.den = 0 := Int.natAbs_eq_zero.mp h0
    have := x.den_pos
    omega
  | inr h => exact h

/-- **well-defined** — ratRel 同値な非零代表で v_p は不変。交差積
    num·den の natAbs 乗法性（Int.natAbs_mul）から v_p を割り当て、
    pvq_natval_mul で加法に開いて omega で整理（choice 不使用）。 -/
theorem pvq_val_wd (p : Nat) (hp : IsPrime p) (x y : PreRat)
    (hx : x.num ≠ 0) (hy : y.num ≠ 0) (h : ratRel x y) :
    pvqVal p x = pvqVal p y := by
  have hh : x.num * y.den = y.num * x.den := h
  have hab : (x.num * y.den).natAbs = (y.num * x.den).natAbs := by rw [hh]
  rw [Int.natAbs_mul, Int.natAbs_mul] at hab
  have hApos : 1 ≤ x.num.natAbs := natAbs_pos_of_ne hx
  have hCpos : 1 ≤ y.num.natAbs := natAbs_pos_of_ne hy
  have hBpos : 1 ≤ x.den.natAbs := natAbs_den_pos x
  have hDpos : 1 ≤ y.den.natAbs := natAbs_den_pos y
  have hval : pvqNatVal p (x.num.natAbs * y.den.natAbs)
            = pvqNatVal p (y.num.natAbs * x.den.natAbs) := by rw [hab]
  rw [pvq_natval_mul p hp _ _ hApos hDpos,
    pvq_natval_mul p hp _ _ hCpos hBpos] at hval
  show (pvqNatVal p x.num.natAbs : Int) - (pvqNatVal p x.den.natAbs : Int)
     = (pvqNatVal p y.num.natAbs : Int) - (pvqNatVal p y.den.natAbs : Int)
  omega

/-- **本丸: 加法性** — 非零 x,y で v_p(xy) = v_p(x)+v_p(y)。
    prMul の num/den は成分積なので natAbs 乗法性 + pvq_natval_mul で
    分子・分母を別々に開き、omega で ℤ の差の和に整理。 -/
theorem pvq_val_mul (p : Nat) (hp : IsPrime p) (x y : PreRat)
    (hx : x.num ≠ 0) (hy : y.num ≠ 0) :
    pvqVal p (prMul x y) = pvqVal p x + pvqVal p y := by
  have hApos : 1 ≤ x.num.natAbs := natAbs_pos_of_ne hx
  have hCpos : 1 ≤ y.num.natAbs := natAbs_pos_of_ne hy
  have hBpos : 1 ≤ x.den.natAbs := natAbs_den_pos x
  have hDpos : 1 ≤ y.den.natAbs := natAbs_den_pos y
  have hnum : (prMul x y).num.natAbs = x.num.natAbs * y.num.natAbs := by
    show (x.num * y.num).natAbs = x.num.natAbs * y.num.natAbs
    rw [Int.natAbs_mul]
  have hden : (prMul x y).den.natAbs = x.den.natAbs * y.den.natAbs := by
    show (x.den * y.den).natAbs = x.den.natAbs * y.den.natAbs
    rw [Int.natAbs_mul]
  show (pvqNatVal p (prMul x y).num.natAbs : Int)
       - (pvqNatVal p (prMul x y).den.natAbs : Int)
     = ((pvqNatVal p x.num.natAbs : Int) - (pvqNatVal p x.den.natAbs : Int))
     + ((pvqNatVal p y.num.natAbs : Int) - (pvqNatVal p y.den.natAbs : Int))
  rw [hnum, hden, pvq_natval_mul p hp _ _ hApos hCpos,
    pvq_natval_mul p hp _ _ hBpos hDpos]
  omega

/-! ## 健全性: v_p(p) = 1 -/

/-- **健全性** — p 素数なら v_p(p) = 1（p = p^1·1, p∤1, 1 = p^0·1）。 -/
theorem pvq_val_p (p : Nat) (hp : IsPrime p) :
    pvqVal p (intToPreRat (p : Int)) = 1 := by
  have hp2 : 2 ≤ p := hp.1
  have hnd1 : ¬ p ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hv1 : pvqNatVal p 1 = 0 := by
    have h := pvqNatVal_spec p hp2 0 1 hnd1 (by omega)
    rw [Nat.pow_zero, Nat.one_mul] at h
    exact h
  have hvp : pvqNatVal p p = 1 := by
    have h := pvqNatVal_spec p hp2 1 1 hnd1 (by omega)
    rw [Nat.pow_one, Nat.mul_one] at h
    exact h
  have hnum : (intToPreRat (p : Int)).num.natAbs = p := by
    show ((p : Int)).natAbs = p
    exact Int.natAbs_natCast p
  have hden : (intToPreRat (p : Int)).den.natAbs = 1 := by
    show ((1 : Int)).natAbs = 1
    rfl
  show (pvqNatVal p (intToPreRat (p : Int)).num.natAbs : Int)
     - (pvqNatVal p (intToPreRat (p : Int)).den.natAbs : Int) = 1
  rw [hnum, hden, hvp, hv1]
  omega

/-! ## capstone: 付値データと存在 -/

/-- **p 進付値データ** — 加法性・well-defined・健全性を束ねる。 -/
structure PadicValData (p : Nat) where
  /-- 付値関数（非零 PreRat 代表上）。 -/
  val : PreRat → Int
  /-- 加法性 v_p(xy) = v_p(x)+v_p(y)（非零）。 -/
  additive : ∀ x y : PreRat, x.num ≠ 0 → y.num ≠ 0 →
    val (prMul x y) = val x + val y
  /-- well-defined（ratRel 不変・非零）。 -/
  welldef : ∀ x y : PreRat, x.num ≠ 0 → y.num ≠ 0 → ratRel x y → val x = val y
  /-- 健全性 v_p(p) = 1。 -/
  val_p : val (intToPreRat (p : Int)) = 1

/-- **capstone** — 各素数 p に対し、加法的で well-defined な実 p 進付値
    v_p : ℚ^× → ℤ（PreRat 代表上）が存在する（Nonempty, choice 不使用）。 -/
theorem pvq_exists (p : Nat) (hp : IsPrime p) : Nonempty (PadicValData p) :=
  ⟨{ val := pvqVal p
     additive := fun x y hx hy => pvq_val_mul p hp x y hx hy
     welldef := fun x y hx hy h => pvq_val_wd p hp x y hx hy h
     val_p := pvq_val_p p hp }⟩

end IUT
