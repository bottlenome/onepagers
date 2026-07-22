/-
  IUT/MuUnits.lean — M101（B-3 前半: μ_{p−1} ≅ (ℤ/p)^× の群同型）

  M34 で Teichmüller 代表 ω(a) が 1 の (p−1) 乗根であること
  （μ_{p−1} への値域）を示した。本モジュールはその**逆向き**を完成
  させる: ℤ_p 内の 1 の (p−1) 乗根は **Teichmüller 代表に他ならない**
  （x^{p−1} = 1 ⟹ x = ω(x mod p)。鍵は x = x^{p^n} と持ち上げ補題）。
  これにより μ_{p−1} と (ℤ/p)^× が**実際の Grp として**構成され、
  レベル 1 射影と Teichmüller 持ち上げが互いに逆な群同型を与える。
  issue #36 の B-3「μ_{p−1} ≅ (ℤ/p)^× の同定」の同型部分の解消。

  * M101-1 `zpPow_zpPow` / `zpPow_mul_dist` / `zpPow_zpOne` /
    `zpPow_one_exp` — 冪の指数法則（(x^m)^k = x^{mk}・(xy)^k = x^k y^k・
    1^k = 1・x^1 = x、いずれも成分ごとの Int 恒等式）
  * M101-2 `IsMuRoot` / `isMuRoot_one` / `isMuRoot_mul` / `isMuRoot_pow`
    — μ_{p−1} = {x | x^{p−1} = 1} は積・冪（特に逆元候補 x^{p−2}）で閉
  * M101-3 `muGrp` / `muGrp_comm` — **μ_{p−1} : Grp**（逆元 = x^{p−2}、
    アーベル群）
  * M101-4 `muRoot_pow_p` / `muRoot_pow_p_pow` — **μ の元は Frobenius
    固定**: x^p = x、ゆえに x^{p^n} = x（全射性の心臓部）
  * M101-5 `teichBar` — **ω の ℤ/p 上への降下**（Quot.lift、
    well-defined 性 = M35-3 の teich_congr。代表元抽出なし = 選択公理
    回避）と乗法性 `teichBar_mul`・レベル 1 復元 `teichBar_level_one`
  * M101-6 `teichBar_of_muRoot` / `muRoot_iff_teich` — **全射性の核心**:
    x^{p−1} = 1 なら x = ω̄(x mod p)。レベル n で x = x^{p^n} と
    持ち上げ補題（teich_pow_congr）の合流。帰結: μ_{p−1} = ω の像
  * M101-7 `teich_inj` / `teichBar_inj` — 単射性（ω(a) ≡ a mod p から）
  * M101-8 `IsZmodUnit` / `zmodUnits` / `zmodUnits_comm` —
    **(ℤ/p)^× : Grp**（レベル 1 剰余群の単数、逆元 = c^{p−2} = Fermat、
    アーベル群）
  * M101-9 `muToUnits` / `unitsToMu` — 相互の群準同型（レベル 1 射影と
    Teichmüller 持ち上げ）
  * M101-10 `MuUnitsIsoData` / `muUnitsIsoData` / `muUnitsIso_exists` —
    **総括: 互いに逆な群準同型対 μ_{p−1} ≅ (ℤ/p)^×**（左右の逆元法則・
    両群のアーベル性を束ねた純レコードと witness）

  未形式化（B-3 後半）: (ℤ/p)^× の巡回性（原始根の存在）。M96 の
  roots_bound（根の個数 ≤ 次数）を ℤ/p 上の X^d − 1 に適用する位数
  論法が必要で、別モジュールに残す（正直申告）。
  全て選択公理不使用。
-/
import IUT.Ring

namespace IUT

/-! ## 冪の指数法則 -/

/-- **M101-1a: 冪の合成則** (x^m)^k = x^{mk}（成分ごとの ipow_mul）。 -/
theorem zpPow_zpPow (p : Nat) (x : (Zp p).carrier) (m k : Nat) :
    zpPow p (zpPow p x m) k = zpPow p x (m * k) := by
  apply Subtype.ext
  funext n
  show zmodPow (p ^ n) (zmodPow (p ^ n) (x.val n) m) k
    = zmodPow (p ^ n) (x.val n) (m * k)
  induction x.val n using Quot.ind; rename_i a
  show Quot.mk (modCong (p ^ n)).rel (ipow (ipow a m) k)
    = Quot.mk (modCong (p ^ n)).rel (ipow a (m * k))
  rw [ipow_mul]

/-- **M101-1b: 冪の乗法分配** (xy)^k = x^k·y^k（成分ごとの mul_ipow）。 -/
theorem zpPow_mul_dist (p : Nat) (x y : (Zp p).carrier) (k : Nat) :
    zpPow p (zpMul p x y) k = zpMul p (zpPow p x k) (zpPow p y k) := by
  apply Subtype.ext
  funext n
  show zmodPow (p ^ n) (zmodMul (p ^ n) (x.val n) (y.val n)) k
    = zmodMul (p ^ n) (zmodPow (p ^ n) (x.val n) k) (zmodPow (p ^ n) (y.val n) k)
  induction x.val n using Quot.ind; rename_i a
  induction y.val n using Quot.ind; rename_i b
  show Quot.mk (modCong (p ^ n)).rel (ipow (a * b) k)
    = Quot.mk (modCong (p ^ n)).rel (ipow a k * ipow b k)
  rw [mul_ipow]

/-- **M101-1c**: 1^k = 1。 -/
theorem zpPow_zpOne (p : Nat) (k : Nat) : zpPow p (zpOne p) k = zpOne p := by
  apply Subtype.ext
  funext n
  show Quot.mk (modCong (p ^ n)).rel (ipow 1 k)
    = Quot.mk (modCong (p ^ n)).rel 1
  rw [one_ipow]

/-- **M101-1d**: x^1 = x。 -/
theorem zpPow_one_exp (p : Nat) (x : (Zp p).carrier) : zpPow p x 1 = x := by
  apply Subtype.ext
  funext n
  show zmodPow (p ^ n) (x.val n) 1 = x.val n
  induction x.val n using Quot.ind; rename_i a
  show Quot.mk (modCong (p ^ n)).rel (ipow a 1)
    = Quot.mk (modCong (p ^ n)).rel a
  have h : ipow a 1 = a := by
    show (1 : Int) * a = a
    rw [Int.one_mul]
  rw [h]

/-! ## μ_{p−1} の membership と閉性 -/

/-- **M101-2a: μ_{p−1} の membership** — 1 の (p−1) 乗根。 -/
def IsMuRoot (p : Nat) (x : (Zp p).carrier) : Prop :=
  zpPow p x (p - 1) = zpOne p

/-- **M101-2b**: 1 ∈ μ_{p−1}。 -/
theorem isMuRoot_one (p : Nat) : IsMuRoot p (zpOne p) :=
  zpPow_zpOne p (p - 1)

/-- **M101-2c: 積閉性**。 -/
theorem isMuRoot_mul (p : Nat) {x y : (Zp p).carrier}
    (hx : IsMuRoot p x) (hy : IsMuRoot p y) : IsMuRoot p (zpMul p x y) := by
  have hx' : zpPow p x (p - 1) = zpOne p := hx
  have hy' : zpPow p y (p - 1) = zpOne p := hy
  show zpPow p (zpMul p x y) (p - 1) = zpOne p
  rw [zpPow_mul_dist, hx', hy', zpOne_mul]

/-- **M101-2d: 冪閉性**（特に逆元候補 x^{p−2} が μ に留まる）。 -/
theorem isMuRoot_pow (p : Nat) {x : (Zp p).carrier}
    (hx : IsMuRoot p x) (k : Nat) : IsMuRoot p (zpPow p x k) := by
  have hx' : zpPow p x (p - 1) = zpOne p := hx
  show zpPow p (zpPow p x k) (p - 1) = zpOne p
  rw [zpPow_zpPow, Nat.mul_comm, ← zpPow_zpPow, hx', zpPow_zpOne]

/-! ## μ_{p−1} の群構成 -/

/-- **定理 (M101-3): μ_{p−1} : Grp** — 逆元は x^{p−2}
    （x^{p−2}·x = x^{p−1} = 1）。 -/
def muGrp (p : Nat) (hp : IsPrime p) : Grp where
  carrier := { x : (Zp p).carrier // IsMuRoot p x }
  mul := fun x y => ⟨zpMul p x.val y.val, isMuRoot_mul p x.property y.property⟩
  one := ⟨zpOne p, isMuRoot_one p⟩
  inv := fun x => ⟨zpPow p x.val (p - 2), isMuRoot_pow p x.property (p - 2)⟩
  mul_assoc := by
    intro x y z
    apply Subtype.ext
    exact zpMul_assoc p x.val y.val z.val
  one_mul := by
    intro x
    apply Subtype.ext
    exact zpOne_mul p x.val
  inv_mul := by
    intro x
    apply Subtype.ext
    show zpMul p (zpPow p x.val (p - 2)) x.val = zpOne p
    rw [← zpPow_succ]
    have h2 : p - 2 + 1 = p - 1 := by have := hp.1; omega
    rw [h2]
    exact x.property

/-- μ_{p−1} はアーベル群。 -/
theorem muGrp_comm (p : Nat) (hp : IsPrime p) (x y : (muGrp p hp).carrier) :
    (muGrp p hp).mul x y = (muGrp p hp).mul y x := by
  apply Subtype.ext
  exact zpMul_comm p x.val y.val

/-! ## μ の元は Frobenius 固定 -/

/-- **M101-4a**: x ∈ μ_{p−1} なら x^p = x。 -/
theorem muRoot_pow_p (p : Nat) (hp : IsPrime p) {x : (Zp p).carrier}
    (hx : IsMuRoot p x) : zpPow p x p = x := by
  have hx' : zpPow p x (p - 1) = zpOne p := hx
  have h : zpPow p x p = zpPow p x (p - 1 + 1) :=
    congrArg (zpPow p x) (by have := hp.1; omega)
  rw [h, zpPow_succ, hx', zpOne_mul]

/-- **定理 (M101-4b): Frobenius 固定** — x ∈ μ_{p−1} なら x^{p^n} = x
    （全射性の心臓部。指数の付け替えは congrArg で ambient の p に
    触れない）。 -/
theorem muRoot_pow_p_pow (p : Nat) (hp : IsPrime p) {x : (Zp p).carrier}
    (hx : IsMuRoot p x) : ∀ n, zpPow p x (p ^ n) = x := by
  intro n
  induction n with
  | zero =>
    have h : zpPow p x (p ^ 0) = zpPow p x 1 :=
      congrArg (zpPow p x) (Nat.pow_zero p)
    rw [h, zpPow_one_exp]
  | succ m ih =>
    have h : zpPow p x (p ^ (m + 1)) = zpPow p x (p ^ m * p) :=
      congrArg (zpPow p x) (Nat.pow_succ p m)
    rw [h, ← zpPow_zpPow, ih, muRoot_pow_p p hp hx]

/-- **M101-4c: μ の元のレベル 1 剰余は p と素** — x^{p−1} = 1 の
    レベル 1 読みで p ∣ a なら p ∣ 1 となり矛盾。 -/
theorem muRoot_level_one_unit (p : Nat) (hp : IsPrime p) {x : (Zp p).carrier}
    (hx : IsMuRoot p x) {a : Int}
    (ha : x.val 1 = Quot.mk (modCong (p ^ 1)).rel a) :
    ¬ ((p : Nat) : Int) ∣ a := by
  intro hdvd
  have hx' : zpPow p x (p - 1) = zpOne p := hx
  have h1 : zmodPow (p ^ 1) (x.val 1) (p - 1)
      = Quot.mk (modCong (p ^ 1)).rel 1 :=
    congrArg (fun w => w.val 1) hx'
  rw [ha] at h1
  have h2 : Quot.mk (modCong (p ^ 1)).rel (ipow a (p - 1))
      = Quot.mk (modCong (p ^ 1)).rel 1 := h1
  have h3 := quot_exact intGrp (modCong (p ^ 1)) h2
  have h4 : ((p ^ 1 : Nat) : Int) ∣ ipow a (p - 1) - 1 := h3
  rw [Nat.pow_one] at h4
  have h5 : ((p : Nat) : Int) ∣ ipow a (p - 1) := by
    have h6 : ipow a (p - 2 + 1) = ipow a (p - 2) * a := rfl
    have h7 : p - 2 + 1 = p - 1 := by have := hp.1; omega
    rw [h7] at h6
    rw [h6]
    exact dvd_mul_of_dvd hdvd (ipow a (p - 2))
  apply not_dvd_one p hp.1
  obtain ⟨u, hu⟩ := h5
  obtain ⟨v, hv⟩ := h4
  refine ⟨u - v, ?_⟩
  rw [Int.mul_sub, ← hu, ← hv]
  omega

/-! ## ω の ℤ/p 上への降下 -/

/-- **定理 (M101-5a): teichBar** — Teichmüller 持ち上げ ω の ℤ/p 上への
    降下（Quot.lift。well-defined 性は M35-3 の teich_congr =「ω は剰余
    のみに依存」。代表元の抽出なし = 選択公理回避）。 -/
def teichBar (p : Nat) (hp : IsPrime p) :
    (zmod (p ^ 1)).carrier → (Zp p).carrier :=
  Quot.lift (fun a => teich p hp a) (fun a b hab => by
    apply teich_congr p hp
    have h : ((p ^ 1 : Nat) : Int) ∣ a - b := hab
    rw [Nat.pow_one] at h
    exact h)

/-- **M101-5b: teichBar の乗法性**（teich_mul の降下）。 -/
theorem teichBar_mul (p : Nat) (hp : IsPrime p)
    (c d : (zmod (p ^ 1)).carrier) :
    teichBar p hp (zmodMul (p ^ 1) c d)
      = zpMul p (teichBar p hp c) (teichBar p hp d) := by
  induction c using Quot.ind; rename_i a
  induction d using Quot.ind; rename_i b
  show teich p hp (a * b) = zpMul p (teich p hp a) (teich p hp b)
  exact teich_mul p hp a b

/-- **M101-5c: レベル 1 復元** — ω̄(c) ≡ c（teich_reduction の降下）。 -/
theorem teichBar_level_one (p : Nat) (hp : IsPrime p)
    (c : (zmod (p ^ 1)).carrier) : (teichBar p hp c).val 1 = c := by
  induction c using Quot.ind; rename_i a
  exact teich_reduction p hp a

/-! ## 全射性: 1 の (p−1) 乗根は Teichmüller 代表に他ならない -/

/-- **定理 (M101-6a): 全射性の核心** — x^{p−1} = 1 なら
    x = ω̄(x mod p)。レベル n では x = x^{p^n}（Frobenius 固定）の
    代表 c と、c ≡ a (mod p) の持ち上げ補題（teich_pow_congr:
    p^n ∣ a^{p^n} − c^{p^n}）が合流する。 -/
theorem teichBar_of_muRoot (p : Nat) (hp : IsPrime p) {x : (Zp p).carrier}
    (hx : IsMuRoot p x) : teichBar p hp (x.val 1) = x := by
  obtain ⟨a, ha⟩ := Quot.exists_rep (x.val 1)
  rw [← ha]
  show teich p hp a = x
  apply Subtype.ext
  funext n
  cases n with
  | zero =>
    show Quot.mk (modCong (p ^ 0)).rel (ipow a (p ^ 0)) = x.val 0
    induction x.val 0 using Quot.ind; rename_i c
    apply Quot.sound
    show ((p ^ 0 : Nat) : Int) ∣ ipow a (p ^ 0) - c
    rw [Nat.pow_zero]
    exact Int.one_dvd _
  | succ m =>
    obtain ⟨c, hc⟩ := Quot.exists_rep (x.val (m + 1))
    have hcomp : (zmodTrans (pow_dvd_mono p (show 1 ≤ m + 1 by omega))).map
        (x.val (m + 1)) = x.val 1 := x.property (show 1 ≤ m + 1 by omega)
    rw [← hc] at hcomp
    have hQ : Quot.mk (modCong (p ^ 1)).rel c
        = Quot.mk (modCong (p ^ 1)).rel a := by
      rw [← ha] at hcomp
      exact hcomp
    have hca := quot_exact intGrp (modCong (p ^ 1)) hQ
    have hca' : ((p ^ 1 : Nat) : Int) ∣ c - a := hca
    rw [Nat.pow_one] at hca'
    have hac : ((p : Nat) : Int) ∣ a - c := dvd_sub_symm hca'
    have hfix := muRoot_pow_p_pow p hp hx (m + 1)
    have hlev : zmodPow (p ^ (m + 1)) (x.val (m + 1)) (p ^ (m + 1))
        = x.val (m + 1) := congrArg (fun w => w.val (m + 1)) hfix
    show Quot.mk (modCong (p ^ (m + 1))).rel (ipow a (p ^ (m + 1)))
      = x.val (m + 1)
    have step1 : Quot.mk (modCong (p ^ (m + 1))).rel (ipow a (p ^ (m + 1)))
        = Quot.mk (modCong (p ^ (m + 1))).rel (ipow c (p ^ (m + 1))) :=
      Quot.sound (teich_pow_congr p hp hac (m + 1))
    have step2 : Quot.mk (modCong (p ^ (m + 1))).rel (ipow c (p ^ (m + 1)))
        = x.val (m + 1) := by
      have h : zmodPow (p ^ (m + 1))
            (Quot.mk (modCong (p ^ (m + 1))).rel c) (p ^ (m + 1))
          = zmodPow (p ^ (m + 1)) (x.val (m + 1)) (p ^ (m + 1)) :=
        congrArg (fun w => zmodPow (p ^ (m + 1)) w (p ^ (m + 1))) hc
      rw [hlev] at h
      exact h
    exact Eq.trans step1 step2

/-- **定理 (M101-6b): μ_{p−1} = ω の像** — x ∈ μ_{p−1} ⟺
    x = ω(a)（p ∤ a）。M34-5 との合流による完全特徴付け。 -/
theorem muRoot_iff_teich (p : Nat) (hp : IsPrime p) (x : (Zp p).carrier) :
    IsMuRoot p x ↔ ∃ a : Int, ¬ ((p : Nat) : Int) ∣ a ∧ x = teich p hp a := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := Quot.exists_rep (x.val 1)
    refine ⟨a, muRoot_level_one_unit p hp hx ha.symm, ?_⟩
    have h := teichBar_of_muRoot p hp hx
    rw [← ha] at h
    exact (show teich p hp a = x from h).symm
  · intro hex
    obtain ⟨a, hpa, hx⟩ := hex
    rw [hx]
    show zpPow p (teich p hp a) (p - 1) = zpOne p
    exact teich_root_of_unity p hp hpa

/-- μ の元は ℤ_p の単数（M36 との接続）。 -/
theorem isZpUnit_of_muRoot (p : Nat) (hp : IsPrime p) {x : (Zp p).carrier}
    (hx : IsMuRoot p x) : IsZpUnit p x := by
  obtain ⟨a, ha⟩ := Quot.exists_rep (x.val 1)
  exact ⟨a, ha.symm, muRoot_level_one_unit p hp hx ha.symm⟩

/-! ## 単射性 -/

/-- **M101-7a: ω の単射性（剰余レベル）** — ω(a) = ω(b) なら
    a ≡ b (mod p)（レベル 1 復元 ω(a) ≡ a から）。 -/
theorem teich_inj (p : Nat) (hp : IsPrime p) {a b : Int}
    (h : teich p hp a = teich p hp b) : ((p : Nat) : Int) ∣ a - b := by
  have h1 : (teich p hp a).val 1 = (teich p hp b).val 1 :=
    congrArg (fun w => w.val 1) h
  rw [teich_reduction p hp a, teich_reduction p hp b] at h1
  have h2 := quot_exact intGrp (modCong (p ^ 1)) h1
  have h3 : ((p ^ 1 : Nat) : Int) ∣ a - b := h2
  rw [Nat.pow_one] at h3
  exact h3

/-- **M101-7b: teichBar の単射性**。 -/
theorem teichBar_inj (p : Nat) (hp : IsPrime p) {c d : (zmod (p ^ 1)).carrier}
    (h : teichBar p hp c = teichBar p hp d) : c = d := by
  revert h
  induction c using Quot.ind; rename_i a
  induction d using Quot.ind; rename_i b
  intro h
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ a - b
  rw [Nat.pow_one]
  exact teich_inj p hp h

/-! ## (ℤ/p)^× の群構成 -/

/-- **M101-8a: レベル 1 単数性** — 代表が p と素（M36-1 のレベル 1 版）。 -/
def IsZmodUnit (p : Nat) (c : (zmod (p ^ 1)).carrier) : Prop :=
  ∃ a : Int, c = Quot.mk (modCong (p ^ 1)).rel a ∧ ¬ ((p : Nat) : Int) ∣ a

/-- 1 は単数。 -/
theorem isZmodUnit_one (p : Nat) (hp : IsPrime p) :
    IsZmodUnit p (Quot.mk (modCong (p ^ 1)).rel 1) :=
  ⟨1, rfl, not_dvd_one p hp.1⟩

/-- **M101-8b: 積閉性**（Euclid の補題）。 -/
theorem isZmodUnit_mul (p : Nat) (hp : IsPrime p)
    {c d : (zmod (p ^ 1)).carrier}
    (hc : IsZmodUnit p c) (hd : IsZmodUnit p d) :
    IsZmodUnit p (zmodMul (p ^ 1) c d) := by
  obtain ⟨a, ha, hpa⟩ := hc
  obtain ⟨b, hb, hpb⟩ := hd
  refine ⟨a * b, ?_, ?_⟩
  · rw [ha, hb]
    rfl
  · intro hab
    exact hpb (euclid_int p hp hab hpa)

/-- **M101-8c: 冪閉性**。 -/
theorem isZmodUnit_pow (p : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c) (k : Nat) :
    IsZmodUnit p (zmodPow (p ^ 1) c k) := by
  obtain ⟨a, ha, hpa⟩ := hc
  refine ⟨ipow a k, ?_, not_dvd_ipow p hp hpa k⟩
  rw [ha]
  rfl

/-- **M101-8d: Fermat 逆元** — c^{p−2}·c = 1（古典形 Fermat の
    レベル 1 読み）。 -/
theorem zmodUnit_inv_mul (p : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c) :
    zmodMul (p ^ 1) (zmodPow (p ^ 1) c (p - 2)) c
      = Quot.mk (modCong (p ^ 1)).rel 1 := by
  obtain ⟨a, ha, hpa⟩ := hc
  rw [ha]
  show Quot.mk (modCong (p ^ 1)).rel (ipow a (p - 2) * a)
    = Quot.mk (modCong (p ^ 1)).rel 1
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ ipow a (p - 2) * a - 1
  rw [Nat.pow_one]
  have h6 : ipow a (p - 2 + 1) = ipow a (p - 2) * a := rfl
  have h7 : p - 2 + 1 = p - 1 := by have := hp.1; omega
  rw [h7] at h6
  rw [← h6]
  exact flt_unit p hp hpa

/-- **定理 (M101-8e): (ℤ/p)^× : Grp** — 環 ℤ/p の乗法単数群。逆元は
    c^{p−2}（Fermat）。 -/
def zmodUnits (p : Nat) (hp : IsPrime p) : Grp where
  carrier := { c : (zmod (p ^ 1)).carrier // IsZmodUnit p c }
  mul := fun c d =>
    ⟨zmodMul (p ^ 1) c.val d.val, isZmodUnit_mul p hp c.property d.property⟩
  one := ⟨Quot.mk (modCong (p ^ 1)).rel 1, isZmodUnit_one p hp⟩
  inv := fun c =>
    ⟨zmodPow (p ^ 1) c.val (p - 2), isZmodUnit_pow p hp c.property (p - 2)⟩
  mul_assoc := by
    intro x y z
    apply Subtype.ext
    exact (zmodRing (p ^ 1)).mul_assoc x.val y.val z.val
  one_mul := by
    intro x
    apply Subtype.ext
    exact (zmodRing (p ^ 1)).one_mul x.val
  inv_mul := by
    intro x
    apply Subtype.ext
    exact zmodUnit_inv_mul p hp x.property

/-- (ℤ/p)^× はアーベル群。 -/
theorem zmodUnits_comm (p : Nat) (hp : IsPrime p)
    (c d : (zmodUnits p hp).carrier) :
    (zmodUnits p hp).mul c d = (zmodUnits p hp).mul d c := by
  apply Subtype.ext
  exact zmodMul_comm (p ^ 1) c.val d.val

/-! ## 相互の群準同型と同型のパッケージング -/

/-- μ の元のレベル 1 射影は (ℤ/p)^× に入る。 -/
theorem isZmodUnit_of_muRoot (p : Nat) (hp : IsPrime p) {x : (Zp p).carrier}
    (hx : IsMuRoot p x) : IsZmodUnit p (x.val 1) := by
  obtain ⟨a, ha⟩ := Quot.exists_rep (x.val 1)
  exact ⟨a, ha.symm, muRoot_level_one_unit p hp hx ha.symm⟩

/-- (ℤ/p)^× の元の Teichmüller 持ち上げは μ_{p−1} に入る
    （M34-5 の降下）。 -/
theorem isMuRoot_teichBar (p : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c) :
    IsMuRoot p (teichBar p hp c) := by
  obtain ⟨a, ha, hpa⟩ := hc
  rw [ha]
  show zpPow p (teich p hp a) (p - 1) = zpOne p
  exact teich_root_of_unity p hp hpa

/-- **M101-9a: レベル 1 射影 μ_{p−1} → (ℤ/p)^×**（群準同型）。 -/
def muToUnits (p : Nat) (hp : IsPrime p) : Hom (muGrp p hp) (zmodUnits p hp) where
  map := fun x => ⟨x.val.val 1, isZmodUnit_of_muRoot p hp x.property⟩
  map_mul := by
    intro x y
    apply Subtype.ext
    rfl

/-- **M101-9b: Teichmüller 持ち上げ (ℤ/p)^× → μ_{p−1}**（群準同型）。 -/
def unitsToMu (p : Nat) (hp : IsPrime p) : Hom (zmodUnits p hp) (muGrp p hp) where
  map := fun c => ⟨teichBar p hp c.val, isMuRoot_teichBar p hp c.property⟩
  map_mul := by
    intro c d
    apply Subtype.ext
    exact teichBar_mul p hp c.val d.val

/-- **定理 (M101-10a): 総括レコード** — 互いに逆な群準同型対
    μ_{p−1} ≅ (ℤ/p)^× と両群のアーベル性。 -/
structure MuUnitsIsoData (p : Nat) (hp : IsPrime p) where
  /-- レベル 1 射影 μ_{p−1} → (ℤ/p)^×。 -/
  toUnits : Hom (muGrp p hp) (zmodUnits p hp)
  /-- Teichmüller 持ち上げ (ℤ/p)^× → μ_{p−1}。 -/
  toMu : Hom (zmodUnits p hp) (muGrp p hp)
  /-- 左逆: ω̄ ∘ 射影 = id（全射性の核心 M101-6）。 -/
  left_inv : ∀ x, toMu.map (toUnits.map x) = x
  /-- 右逆: 射影 ∘ ω̄ = id（レベル 1 復元 M101-5c）。 -/
  right_inv : ∀ c, toUnits.map (toMu.map c) = c
  /-- μ_{p−1} のアーベル性。 -/
  mu_comm : ∀ x y, (muGrp p hp).mul x y = (muGrp p hp).mul y x
  /-- (ℤ/p)^× のアーベル性。 -/
  units_comm : ∀ c d, (zmodUnits p hp).mul c d = (zmodUnits p hp).mul d c

/-- **定理 (M101-10b): witness** — 全フィールドが既証明の純レコード。 -/
def muUnitsIsoData (p : Nat) (hp : IsPrime p) : MuUnitsIsoData p hp where
  toUnits := muToUnits p hp
  toMu := unitsToMu p hp
  left_inv := by
    intro x
    apply Subtype.ext
    exact teichBar_of_muRoot p hp x.property
  right_inv := by
    intro c
    apply Subtype.ext
    exact teichBar_level_one p hp c.val
  mu_comm := muGrp_comm p hp
  units_comm := zmodUnits_comm p hp

/-- **定理 (M101-10c): 同型の存在**。 -/
theorem muUnitsIso_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (MuUnitsIsoData p hp) := ⟨muUnitsIsoData p hp⟩

end IUT
