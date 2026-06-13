/-
  IUT/ZpDomain.lean — M91F（柱B: ℤ_p の witness 付き零因子なし —
  O 整域性への突破口・第一段）

  ℤ_p = lim ℤ/p^n（M27 の実構成）の上で、**構成的（witness 付き）
  零因子なし定理**を証明する。古典的な「x ≠ 0 かつ y ≠ 0 なら
  xy ≠ 0」は、x ≠ 0 という否定的仮定から情報を取り出すために
  排中律を要するが、本モジュールでは非零性を**レベル付きの
  witness**（NeZeroAt p x n = レベル n 成分が 0 でない）として
  持ち歩くことで、全てを選択公理・排中律なしで構成する。

  * M91F-0 `zmodIsZero` — ℤ/n の **0 判定の Bool 値関数**
    （代表の emod による Quot.lift。decide のみ・選択公理不使用）。
    これにより「レベル 1 成分が 0 か否か」の場合分けが**データ
    構成の中で**可能になる
  * M91F-1 `NeZeroAt` / `neZeroAt_mono` / `neZeroAt_ne_zero` —
    構成的非零性: レベル n 成分 ≠ 0。レベルについて単調
    （整合性から下のレベルの非零は上へ伝播）、かつ x ≠ 0 を含意
  * M91F-2 `ZpValDecomp` / `zpValDecompose` — **付値分解
    （witness 付き・レベルの強帰納法）**: NeZeroAt p x m なら
    明示的に構成された k < m と u（レベル 1 単数）で x = p^k·u。
    Σ 型構造体として**データで**返す（除算は M43 の zpDivP）。
    ∃ 版は `zp_valuation_exists`
  * M91F-3 `neZeroAt_one_mul` — **レベル 1 乗法性**: p 素数のとき
    レベル 1 非零 × レベル 1 非零 → 積もレベル 1 非零
    （ℤ/p の零因子なし。M32 Bézout 経由の Euclid の補題 Int 版）
  * M91F-4 `neZeroAt_p_pow_mul` — **p シフト**: w がレベル 1 非零
    なら p^k·w はレベル k+1 非零（p 倍は最初の非零レベルを
    ちょうど 1 つ持ち上げる。成分簿記 `p_mul_val_zero` /
    `val_zero_p_mul` による帰納）
  * M91F-5 `zp_mul_ne_zero`（本丸）— **witness 付き零因子なし**:
    NeZeroAt p x m → NeZeroAt p y n → NeZeroAt p (x·y) (m+n)
    （分解 x = p^k u, y = p^l v から x·y = p^{k+l}·(uv)、
    k+l+1 ≤ m+n は単調性で閉じる）。否定形の系は
    `zp_ne_zero_mul` : x·y ≠ 0
  * M91F-6 `ZpDomainData` / `zpDomainData` — 上記一式（述語・
    単調性・分解・レベル 1 乗法性・本定理）の束と witness、
    見出し定理 `zpDomain_nonempty`

  **位置づけ（正直な申告）**: witness なしの零因子なし
  NoZeroDiv (zpRing p)（a·b = 0 → a = 0 ∨ b = 0）は、どちらの
  選言肢かを決めるのに排中律（ないし Markov 原理）を要するため
  構成的には追求しない——それが本モジュールが witness 付き
  非零性を採用する理由である。また M90F の仮定が要求する
  eisRing p（O = ℤ_p[π]）への転送は、O 上の同種の理論
  （成分簿記と付値分解の Eisenstein 版）を要する将来課題である。
  全て選択公理不使用。
-/
import IUT.PadicDivision

namespace IUT

/-! ## §0 簿記補題と ℤ/n の 0 判定 -/

/-- 簿記: A − 0 = W なら A = W。 -/
theorem int_eq_of_sub_zero {A W : Int} (h : A - 0 = W) : A = W := by omega

/-- 簿記: A = W なら A − 0 = W。 -/
theorem int_sub_zero_of_eq {A W : Int} (h : A = W) : A - 0 = W := by omega

/-- 簿記: A − B = W なら A = B + W。 -/
theorem int_eq_add_of_sub {A B W : Int} (h : A - B = W) : A = B + W := by
  omega

/-- **M91F-0a: ℤ/n の 0 判定**（代表の emod による Bool 値
    Quot.lift。well-defined 性は emod の加法公式から）。 -/
def zmodIsZero (n : Nat) : (zmod n).carrier → Bool :=
  Quot.lift (fun c => decide (c % ((n : Nat) : Int) = 0))
    (fun a b hab => by
      have hmod : a % ((n : Nat) : Int) = b % ((n : Nat) : Int) := by
        obtain ⟨k, hk⟩ := hab
        have ha : a = b + ((n : Nat) : Int) * k := int_eq_add_of_sub hk
        rw [ha, Int.add_mul_emod_self_left]
      show decide (a % ((n : Nat) : Int) = 0)
        = decide (b % ((n : Nat) : Int) = 0)
      rw [hmod])

/-- **M91F-0b**: 判定が true なら成分は 0。 -/
theorem zmodIsZero_true (n : Nat) (x : (zmod n).carrier) :
    zmodIsZero n x = true → x = Quot.mk (modCong n).rel 0 := by
  induction x using Quot.ind
  rename_i c
  intro h
  have h' : decide (c % ((n : Nat) : Int) = 0) = true := h
  have hc : c % ((n : Nat) : Int) = 0 := of_decide_eq_true h'
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hc
  apply Quot.sound
  show ((n : Nat) : Int) ∣ c - 0
  exact ⟨k, int_sub_zero_of_eq hk⟩

/-- **M91F-0c**: 0 での判定は true。 -/
theorem zmodIsZero_zero (n : Nat) :
    zmodIsZero n (Quot.mk (modCong n).rel 0) = true := by
  show decide ((0 : Int) % ((n : Nat) : Int) = 0) = true
  rw [Int.zero_emod]
  exact decide_eq_true rfl

/-- **M91F-0d**: 判定が false なら成分は 0 でない。 -/
theorem zmodIsZero_false (n : Nat) (x : (zmod n).carrier)
    (h : zmodIsZero n x = false) : x ≠ Quot.mk (modCong n).rel 0 := by
  intro h0
  rw [h0, zmodIsZero_zero] at h
  exact Bool.noConfusion h

/-! ## §1 構成的非零性 NeZeroAt -/

/-- **M91F-1a: 構成的非零性** — x のレベル n 成分が 0 でない。
    否定的仮定 x ≠ 0 と違い、**どのレベルで**非零かという witness
    を持ち歩くため、排中律なしで積の非零性が構成できる。 -/
def NeZeroAt (p : Nat) (x : (Zp p).carrier) (n : Nat) : Prop :=
  x.val n ≠ Quot.mk (modCong (p ^ n)).rel 0

/-- **M91F-1b: レベル単調性** — レベル m で非零なら全ての上の
    レベルでも非零（整合性: 上のレベルの 0 は下に射影される）。 -/
theorem neZeroAt_mono (p : Nat) (x : (Zp p).carrier) {m n : Nat}
    (hmn : m ≤ n) (hm : NeZeroAt p x m) : NeZeroAt p x n := by
  intro h0
  apply hm
  have hcomp := x.property hmn
  rw [h0] at hcomp
  exact hcomp.symm

/-- **M91F-1c**: NeZeroAt なら x ≠ 0。 -/
theorem neZeroAt_ne_zero (p : Nat) (x : (Zp p).carrier) {n : Nat}
    (hx : NeZeroAt p x n) : x ≠ (zpRing p).zero := by
  intro h0
  apply hx
  rw [h0]
  rfl

/-- レベル 0（ℤ/p^0 = ℤ/1 は自明群）では非零性は成立しない。 -/
theorem neZeroAt_zero_elim (p : Nat) (x : (Zp p).carrier)
    (hx : NeZeroAt p x 0) : False := by
  apply hx
  obtain ⟨c, hc⟩ := Quot.exists_rep (x.val 0)
  rw [← hc]
  apply Quot.sound
  show ((p ^ 0 : Nat) : Int) ∣ c - 0
  exact ⟨c - 0, (Int.one_mul (c - 0)).symm⟩

/-! ## §2 p 倍の成分簿記 -/

/-- p 倍のレベル n 成分は代表の p 倍。 -/
theorem val_p_mul (p : Nat) (y : (Zp p).carrier) (n : Nat) (c : Int)
    (hc : Quot.mk (modCong (p ^ n)).rel c = y.val n) :
    (zpMul p ((toZp p).map ((p : Nat) : Int)) y).val n
      = Quot.mk (modCong (p ^ n)).rel (((p : Nat) : Int) * c) := by
  show zmodMul (p ^ n)
      (Quot.mk (modCong (p ^ n)).rel ((p : Nat) : Int)) (y.val n)
    = Quot.mk (modCong (p ^ n)).rel (((p : Nat) : Int) * c)
  rw [← hc]
  rfl

/-- **簿記（上向き）**: y のレベル n 成分が 0 なら p·y のレベル
    n+1 成分も 0。 -/
theorem val_zero_p_mul (p : Nat) (y : (Zp p).carrier) (n : Nat)
    (h0 : y.val n = Quot.mk (modCong (p ^ n)).rel 0) :
    (zpMul p ((toZp p).map ((p : Nat) : Int)) y).val (n + 1)
      = Quot.mk (modCong (p ^ (n + 1))).rel 0 := by
  obtain ⟨c, hc⟩ := Quot.exists_rep (y.val (n + 1))
  have htrans : (zmodTrans (pow_dvd_mono p (Nat.le_succ n))).map
      (y.val (n + 1)) = y.val n := y.property (Nat.le_succ n)
  rw [← hc] at htrans
  have hcn : Quot.mk (modCong (p ^ n)).rel c
      = Quot.mk (modCong (p ^ n)).rel 0 := htrans.trans h0
  obtain ⟨d, hd⟩ := quot_exact intGrp (modCong (p ^ n)) hcn
  rw [val_p_mul p y (n + 1) c hc]
  apply Quot.sound
  show ((p ^ (n + 1) : Nat) : Int) ∣ ((p : Nat) : Int) * c - 0
  refine ⟨d, ?_⟩
  rw [cast_pow_succ p n]
  have hc' : c = ((p ^ n : Nat) : Int) * d := int_eq_of_sub_zero hd
  rw [hc', ← Int.mul_assoc ((p : Nat) : Int) ((p ^ n : Nat) : Int) d,
    Int.mul_comm ((p : Nat) : Int) ((p ^ n : Nat) : Int)]
  exact int_sub_zero_of_eq rfl

/-- **簿記（下向き・キャンセル）**: p·y のレベル n+1 成分が 0 なら
    y のレベル n 成分は 0（Int の左キャンセルによる）。 -/
theorem p_mul_val_zero (p : Nat) (hp : 2 ≤ p) (y : (Zp p).carrier) (n : Nat)
    (h0 : (zpMul p ((toZp p).map ((p : Nat) : Int)) y).val (n + 1)
      = Quot.mk (modCong (p ^ (n + 1))).rel 0) :
    y.val n = Quot.mk (modCong (p ^ n)).rel 0 := by
  obtain ⟨c, hc⟩ := Quot.exists_rep (y.val (n + 1))
  rw [val_p_mul p y (n + 1) c hc] at h0
  obtain ⟨d, hd⟩ := quot_exact intGrp (modCong (p ^ (n + 1))) h0
  have hpc : ((p : Nat) : Int) * c
      = ((p : Nat) : Int) * (((p ^ n : Nat) : Int) * d) := by
    rw [cast_pow_succ p n] at hd
    rw [← Int.mul_assoc ((p : Nat) : Int) ((p ^ n : Nat) : Int) d,
      Int.mul_comm ((p : Nat) : Int) ((p ^ n : Nat) : Int)]
    exact int_eq_of_sub_zero hd
  have hcancel : c = ((p ^ n : Nat) : Int) * d :=
    Int.eq_of_mul_eq_mul_left (by omega : ((p : Nat) : Int) ≠ 0) hpc
  have htrans : (zmodTrans (pow_dvd_mono p (Nat.le_succ n))).map
      (y.val (n + 1)) = y.val n := y.property (Nat.le_succ n)
  rw [← hc] at htrans
  rw [← htrans]
  show Quot.mk (modCong (p ^ n)).rel c = Quot.mk (modCong (p ^ n)).rel 0
  apply Quot.sound
  show ((p ^ n : Nat) : Int) ∣ c - 0
  exact ⟨d, int_sub_zero_of_eq hcancel⟩

/-- p 倍は非零レベルをちょうど 1 つ持ち上げる（1 ステップ）。 -/
theorem neZeroAt_p_mul (p : Nat) (hp : 2 ≤ p) (y : (Zp p).carrier)
    (n : Nat) (hy : NeZeroAt p y n) :
    NeZeroAt p (zpMul p ((toZp p).map ((p : Nat) : Int)) y) (n + 1) :=
  fun h0 => hy (p_mul_val_zero p hp y n h0)

/-! ## §3 M91F-2 付値分解（witness 付き） -/

/-- **M91F-2a: 付値分解のデータ** — k < m と u（レベル 1 非零 =
    単数性のレベル 1 witness）と等式 x = p^k·u の束。∃ ではなく
    Σ 型構造体（再利用可能なデータ）。 -/
structure ZpValDecomp (p : Nat) (x : (Zp p).carrier) (m : Nat) where
  k : Nat
  u : (Zp p).carrier
  k_lt : k < m
  unit1 : NeZeroAt p u 1
  eq : x = zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k) u

/-- **M91F-2b: 付値分解の構成**（レベルの強帰納法 + M43 zpDivP）。
    レベル 1 成分の 0 判定は M91F-0 の Bool 値関数で行うため、
    データ構成の中での場合分けに排中律を要しない。 -/
def zpValDecompose (p : Nat) (hp : 2 ≤ p) :
    (m : Nat) → (x : (Zp p).carrier) → NeZeroAt p x m → ZpValDecomp p x m
  | 0, x, hx => (neZeroAt_zero_elim p x hx).elim
  | m + 1, x, hx =>
    match h1 : zmodIsZero (p ^ 1) (x.val 1) with
    | false =>
      { k := 0
        u := x
        k_lt := Nat.zero_lt_succ m
        unit1 := zmodIsZero_false (p ^ 1) (x.val 1) h1
        eq := by
          show x = zpMul p (zpOne p) x
          exact (zpOne_mul p x).symm }
    | true =>
      have hx1 : x.val 1 = Quot.mk (modCong (p ^ 1)).rel 0 :=
        zmodIsZero_true (p ^ 1) (x.val 1) h1
      have hxe : zpMul p ((toZp p).map ((p : Nat) : Int)) (zpDivP p hp x)
          = x := zpDivP_mul_cancel p hp x hx1
      have hx' : NeZeroAt p (zpDivP p hp x) m := fun h0 =>
        hx (by
          rw [← hxe]
          exact val_zero_p_mul p (zpDivP p hp x) m h0)
      match zpValDecompose p hp m (zpDivP p hp x) hx' with
      | ⟨k, u, hk, hu, he⟩ =>
        { k := k + 1
          u := u
          k_lt := Nat.succ_lt_succ hk
          unit1 := hu
          eq := by
            rw [← hxe, he]
            show zpMul p ((toZp p).map ((p : Nat) : Int))
                (zpMul p (rpow (zpRing p)
                  ((toZp p).map ((p : Nat) : Int)) k) u)
              = zpMul p (zpMul p (rpow (zpRing p)
                  ((toZp p).map ((p : Nat) : Int)) k)
                  ((toZp p).map ((p : Nat) : Int))) u
            rw [← zpMul_assoc p ((toZp p).map ((p : Nat) : Int))
                (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k) u,
              zpMul_comm p ((toZp p).map ((p : Nat) : Int))
                (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k)] }

/-- **M91F-2c: 付値分解の ∃ 版**（明示的 intro なので choice-free）。 -/
theorem zp_valuation_exists (p : Nat) (hp : 2 ≤ p) (x : (Zp p).carrier)
    (m : Nat) (hx : NeZeroAt p x m) :
    ∃ k u, k < m ∧ NeZeroAt p u 1 ∧
      x = zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k) u :=
  match zpValDecompose p hp m x hx with
  | ⟨k, u, hk, hu, he⟩ => ⟨k, u, hk, hu, he⟩

/-! ## §4 M91F-3 レベル 1 乗法性（ℤ/p の零因子なし） -/

/-- **M91F-3: レベル 1 乗法性** — p 素数のとき、レベル 1 非零の
    積はレベル 1 非零（ℤ/p は零因子を持たない。Euclid の補題
    Int 版 = M34-2、その実体は M32 の Bézout）。 -/
theorem neZeroAt_one_mul (p : Nat) (hp : IsPrime p) (u v : (Zp p).carrier)
    (hu : NeZeroAt p u 1) (hv : NeZeroAt p v 1) :
    NeZeroAt p (zpMul p u v) 1 := by
  intro h0
  obtain ⟨a, ha⟩ := Quot.exists_rep (u.val 1)
  obtain ⟨b, hb⟩ := Quot.exists_rep (v.val 1)
  have h0' : zmodMul (p ^ 1) (u.val 1) (v.val 1)
      = Quot.mk (modCong (p ^ 1)).rel 0 := h0
  rw [← ha, ← hb] at h0'
  have hab : Quot.mk (modCong (p ^ 1)).rel (a * b)
      = Quot.mk (modCong (p ^ 1)).rel 0 := h0'
  obtain ⟨t, ht⟩ := quot_exact intGrp (modCong (p ^ 1)) hab
  rw [Nat.pow_one] at ht
  have hdvd : ((p : Nat) : Int) ∣ a * b := ⟨t, int_eq_of_sub_zero ht⟩
  have hpa : ¬ ((p : Nat) : Int) ∣ a := by
    intro hda
    apply hu
    rw [← ha]
    obtain ⟨s, hs⟩ := hda
    apply Quot.sound
    show ((p ^ 1 : Nat) : Int) ∣ a - 0
    rw [Nat.pow_one]
    exact ⟨s, int_sub_zero_of_eq hs⟩
  have hpb : ((p : Nat) : Int) ∣ b := euclid_int p hp hdvd hpa
  apply hv
  rw [← hb]
  obtain ⟨s, hs⟩ := hpb
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ b - 0
  rw [Nat.pow_one]
  exact ⟨s, int_sub_zero_of_eq hs⟩

/-! ## §5 M91F-4 p シフト -/

/-- **M91F-4: p シフト** — w がレベル 1 非零なら p^k·w はレベル
    k+1 非零（k の帰納法。各ステップは §2 のキャンセル簿記）。 -/
theorem neZeroAt_p_pow_mul (p : Nat) (hp : 2 ≤ p) (w : (Zp p).carrier)
    (hw : NeZeroAt p w 1) (k : Nat) :
    NeZeroAt p
      (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k) w)
      (k + 1) := by
  induction k with
  | zero =>
    show NeZeroAt p (zpMul p (zpOne p) w) 1
    rw [zpOne_mul]
    exact hw
  | succ k ih =>
    have heq : zpMul p
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (k + 1)) w
        = zpMul p ((toZp p).map ((p : Nat) : Int))
          (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k) w) := by
      show zpMul p (zpMul p (rpow (zpRing p)
            ((toZp p).map ((p : Nat) : Int)) k)
            ((toZp p).map ((p : Nat) : Int))) w
        = zpMul p ((toZp p).map ((p : Nat) : Int))
          (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k) w)
      rw [zpMul_comm p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k)
          ((toZp p).map ((p : Nat) : Int)),
        zpMul_assoc p ((toZp p).map ((p : Nat) : Int))
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k) w]
    rw [heq]
    exact neZeroAt_p_mul p hp _ (k + 1) ih

/-! ## §6 M91F-5 本丸: witness 付き零因子なし -/

/-- 環冪の加法則（一般の可換環、選択公理不使用）。 -/
theorem rpow_add (R : CRing) (a : R.carrier) (k l : Nat) :
    rpow R a (k + l) = R.mul (rpow R a k) (rpow R a l) := by
  induction l with
  | zero =>
    show rpow R a k = R.mul (rpow R a k) R.one
    rw [R.mul_comm, R.one_mul]
  | succ l ih =>
    show R.mul (rpow R a (k + l)) a
      = R.mul (rpow R a k) (R.mul (rpow R a l) a)
    rw [ih, R.mul_assoc]

/-- 積の交換結合（(ab)(cd) = (ac)(bd)、ℤ_p 乗法）。 -/
theorem zpMul_mul_mul_comm (p : Nat) (a b c d : (Zp p).carrier) :
    zpMul p (zpMul p a b) (zpMul p c d)
      = zpMul p (zpMul p a c) (zpMul p b d) := by
  rw [zpMul_assoc p a b (zpMul p c d), ← zpMul_assoc p b c d,
    zpMul_comm p b c, zpMul_assoc p c b d,
    ← zpMul_assoc p a c (zpMul p b d)]

/-- **定理 (M91F-5・本丸): witness 付き零因子なし** —
    x がレベル m 非零、y がレベル n 非零なら x·y はレベル m+n
    非零。証明: 付値分解 x = p^k·u, y = p^l·v（k < m, l < n）から
    x·y = p^{k+l}·(uv)、レベル 1 乗法性と p シフトで
    レベル k+l+1 非零、k+l+1 ≤ m+n は単調性で閉じる。 -/
theorem zp_mul_ne_zero (p : Nat) (hp : IsPrime p) (x y : (Zp p).carrier)
    (m n : Nat) (hx : NeZeroAt p x m) (hy : NeZeroAt p y n) :
    NeZeroAt p (zpMul p x y) (m + n) := by
  obtain ⟨k1, u1, hk1, hu1, he1⟩ := zpValDecompose p hp.1 m x hx
  obtain ⟨k2, u2, hk2, hu2, he2⟩ := zpValDecompose p hp.1 n y hy
  have hxy : zpMul p x y
      = zpMul p
        (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k1)
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k2))
        (zpMul p u1 u2) := by
    rw [he1, he2]
    exact zpMul_mul_mul_comm p _ _ _ _
  have hrp : zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k1)
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k2)
      = rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (k1 + k2) :=
    (rpow_add (zpRing p) ((toZp p).map ((p : Nat) : Int)) k1 k2).symm
  have huv : NeZeroAt p (zpMul p u1 u2) 1 :=
    neZeroAt_one_mul p hp u1 u2 hu1 hu2
  have hmain : NeZeroAt p (zpMul p x y) (k1 + k2 + 1) := by
    rw [hxy, hrp]
    exact neZeroAt_p_pow_mul p hp.1 (zpMul p u1 u2) huv (k1 + k2)
  exact neZeroAt_mono p (zpMul p x y) (by omega) hmain

/-- **系（否定形）**: witness 付き非零元の積は 0 でない。 -/
theorem zp_ne_zero_mul (p : Nat) (hp : IsPrime p) (x y : (Zp p).carrier)
    (m n : Nat) (hx : NeZeroAt p x m) (hy : NeZeroAt p y n) :
    (zpRing p).mul x y ≠ (zpRing p).zero :=
  neZeroAt_ne_zero p (zpMul p x y) (zp_mul_ne_zero p hp x y m n hx hy)

/-! ## §7 M91F-6 まとめの束 -/

/-- **M91F-6a: ℤ_p の witness 付き整域性データ** — 構成的非零性の
    単調性・零性含意・付値分解（データ）・レベル 1 乗法性・
    本定理・否定形の系の束。 -/
structure ZpDomainData (p : Nat) (hp : IsPrime p) where
  mono : ∀ (x : (Zp p).carrier) {m n : Nat}, m ≤ n →
    NeZeroAt p x m → NeZeroAt p x n
  ne_zero : ∀ (x : (Zp p).carrier) {n : Nat},
    NeZeroAt p x n → x ≠ (zpRing p).zero
  decompose : ∀ (m : Nat) (x : (Zp p).carrier),
    NeZeroAt p x m → ZpValDecomp p x m
  level_one_mul : ∀ u v, NeZeroAt p u 1 → NeZeroAt p v 1 →
    NeZeroAt p (zpMul p u v) 1
  mul_neZeroAt : ∀ x y m n, NeZeroAt p x m → NeZeroAt p y n →
    NeZeroAt p ((zpRing p).mul x y) (m + n)
  mul_ne_zero : ∀ x y m n, NeZeroAt p x m → NeZeroAt p y n →
    (zpRing p).mul x y ≠ (zpRing p).zero

/-- **M91F-6b: witness**（全フィールドが本モジュールの完全証明）。 -/
def zpDomainData (p : Nat) (hp : IsPrime p) : ZpDomainData p hp where
  mono := fun x {_ _} h hm => neZeroAt_mono p x h hm
  ne_zero := fun x {_} h => neZeroAt_ne_zero p x h
  decompose := fun m x h => zpValDecompose p hp.1 m x h
  level_one_mul := neZeroAt_one_mul p hp
  mul_neZeroAt := fun x y m n hx hy => zp_mul_ne_zero p hp x y m n hx hy
  mul_ne_zero := fun x y m n hx hy => zp_ne_zero_mul p hp x y m n hx hy

/-- **見出し定理 (M91F-6c)**: ℤ_p の witness 付き整域性データは
    任意の素数 p で存在する。 -/
theorem zpDomain_nonempty (p : Nat) (hp : IsPrime p) :
    Nonempty (ZpDomainData p hp) := ⟨zpDomainData p hp⟩

end IUT
