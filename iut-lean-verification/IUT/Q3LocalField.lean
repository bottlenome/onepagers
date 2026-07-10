/-
  IUT/Q3LocalField.lean — A2c（柱A2: 実 p 進局所体 — 体 ℚ₃ = ℤ₃[1/3] の実構成）

  ── 主要成果の分類: **[実／本物建設(b)]**。既存の実 ℤ₃ = lim ℤ/3ⁿ（zpRing 3）と
     A2a の局所体パッケージ（z3vGe/z3vExact・因数分解 x=3^v·u・付値の加法性）と
     M290F の本物の局所化 R[1/f]（ringLocRf/ringLocMap/ringLoc_unit_of_S）の上に、
     **コードベース初の p 進体オブジェクト ℚ₃ = ℤ₃[1/3]** を本物構成する。toy 主語なし。
     主語は実 zpRing 3 の実局所化 ringLocRf z3 q3fThree。

  complete_pct 影響: **A2 A2c を前進**（設計見込み A2 0.60→0.65・柱A 45→46）。
  内容: (i) ℚ₃ = ℤ₃[1/3] の実例代入（q3Ring）、(ii) ℤ₃ ↪ ℚ₃ の単射（q3f_embed_inj・
  3^n 正則性）、(iii) uniformizer 3（q3f_uniformizer: z3vExact 1 かつ ¬単数）、
  (iv) 3 は ℚ₃ で可逆（q3f_three_unit）、(v) **∃ 形体性**（q3f_has_inverses: 非零 witness
  付き元 mk(a,3ⁿ)（¬z3vGe a (k+1)）の逆元を 3^v·u 分解＋明示逆元 zpUnitInv で構成）、
  (vi) ℤ 値付値の関係形（q3fValRel）と well-defined（q3f_val_wd）・加法性（q3f_val_mul）・
  整数環 O=ℤ₃（q3f_ring_of_val: 付値≥0 なら分母を払える）。

  正直な限定（§3 準拠・消去/弱化しない）:
  - **total inv（IUTField としての ℚ₃）は主張しない**。ℚ₃ の元 x の逆元計算は v(x) の
    特定を要し、仮定 x≠0 は否定形（¬∀n, x.val n=[0]）で witness 抽出に Markov 原理を
    要する。choice-free 断片では関数化不能（ℚ_p は構成的には離散体でない）。忠実版は
    「正の非零 witness（¬z3vGe a (k+1)）付き元の逆元を明示構成する ∃ 形」（q3f_has_inverses）。
  - **付値は関数でなく関係**（q3fValRel: ∃ a n v, x=mk(a,3ⁿ)∧z3vExact a v∧κ=v−n）。
  - **p = 3 固定**・基礎体 ℚ のみ。ℚ↪ℚ₃ の環準同型（A2c-3）・ℚ₃ の位相・G_{ℚ₃}・
    分岐理論は本ファイルの範囲外（後続）。実 ℤ₃・M290F 局所化は既存（新設せず消費）。
    既存 surrogate（unitsModel 等）は消さない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ（Classical.choice 無し）。
-/
import IUT.Zp3ValuationRing
import IUT.RingLocalization

namespace IUT

/-! ## A2c-0: 主語の固定 — ℚ₃ = ℤ₃[1/3] -/

/-- ℤ₃ の中の元 3（= 対角埋め込みの像・付値の一様化子）。
    `z3vP 3 = (toZp 3).map ((3:Nat):Int) = (toZpRing 3).map 3`。 -/
@[reducible] def q3fThree : z3.carrier := z3vP 3

/-- ℚ₃ の分母集合 S = {1, 3, 3², …}（3 冪乗法系）。 -/
@[reducible] def q3S : ringLocMulSet z3 := ringLocPowers z3 q3fThree

/-- **A2c-0（★）: 体 ℚ₃ = ℤ₃[1/3]** — 実 ℤ₃ の 3 冪局所化（M290F の実例代入）。
    コードベース初の p 進体オブジェクト。 -/
@[reducible] def q3Ring : CRing := ringLocRf z3 q3fThree

/-! ## A2c-1: 局所化商の分離性（ringLocRel の商から関係を取り出す） -/

/-- ℚ₃ の担体 Quot の分離性（ringLocRel は反射・対称・推移なので商の等号から
    関係が復元される。M13-3 quot_exact の局所化版・inline）。 -/
theorem q3f_exact {x y : ringLocPre z3 q3S}
    (h : Quot.mk (ringLocRel q3S) x = Quot.mk (ringLocRel q3S) y) :
    ringLocRel q3S x y := by
  have hf : Quot.lift (ringLocRel q3S x)
      (fun _ _ hab => propext
        ⟨fun hxa => ringLocRel_trans hxa hab,
         fun hxb => ringLocRel_trans hxb (ringLocRel_symm hab)⟩)
      (Quot.mk (ringLocRel q3S) x) := ringLocRel_refl x
  rw [h] at hf
  exact hf

/-! ## A2c-2: 3 冪の環冪・正則性・非退化 -/

/-- ringLocPow（左掛け）と rpow（右掛け）の一致（可換環）。 -/
theorem q3_ringLocPow_eq_rpow (R : CRing) (f : R.carrier) (n : Nat) :
    ringLocPow R f n = rpow R f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show R.mul f (ringLocPow R f n) = R.mul (rpow R f n) f
    rw [ih]
    exact R.mul_comm f (rpow R f n)

/-- ringLocPow と ℤ_p 冪 zpPow の一致（A2a の rpow_zpRing_eq_zpPow 経由）。 -/
theorem q3_ringLocPow_eq_zpPow (k : Nat) :
    ringLocPow z3 q3fThree k = zpPow 3 q3fThree k := by
  rw [q3_ringLocPow_eq_rpow z3 q3fThree k]
  exact rpow_zpRing_eq_zpPow 3 q3fThree k

/-- 3ⁿ·1 = ringLocPow z3 3 n（付値補題との接着）。 -/
theorem q3_mul_one_pow (s : Nat) :
    zpMul 3 (rpow z3 q3fThree s) z3.one = ringLocPow z3 q3fThree s := by
  rw [q3_ringLocPow_eq_rpow z3 q3fThree s]
  exact cring_mul_one z3 (rpow z3 q3fThree s)

/-- **A2c-2a: 3ⁿ はレベル n で 0**（v(3ⁿ) ≥ n）。 -/
theorem q3_pow_ge (s : Nat) : z3vGe 3 (ringLocPow z3 q3fThree s) s := by
  induction s with
  | zero => exact z3vGe_zero 3 _
  | succ s ih =>
    show z3vGe 3 (z3.mul q3fThree (ringLocPow z3 q3fThree s)) (s + 1)
    exact val_zero_p_mul 3 (ringLocPow z3 q3fThree s) s ih

/-- **A2c-2b: 3ⁿ はレベル n+1 で非零**（v(3ⁿ) < n+1・M91F の p シフト）。 -/
theorem q3_pow_neZero (s : Nat) : NeZeroAt 3 (ringLocPow z3 q3fThree s) (s + 1) := by
  have h1 : NeZeroAt 3 z3.one 1 := by
    intro hz
    have hz' : Quot.mk (modCong (3 ^ 1)).rel 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := hz
    obtain ⟨kk, hkk⟩ := quot_exact intGrp (modCong (3 ^ 1)) hz'
    rw [Nat.pow_one] at hkk
    omega
  have h2 := neZeroAt_p_pow_mul 3 (by omega) z3.one h1 s
  have h3 : zpMul 3 (rpow (zpRing 3) ((toZp 3).map ((3 : Nat) : Int)) s) z3.one
      = ringLocPow z3 q3fThree s := q3_mul_one_pow s
  rw [h3] at h2
  exact h2

/-- **A2c-2c: 3ⁿ の厳密付値は n**（DVR の一様化子冪の付値）。 -/
theorem q3_pow_exact (s : Nat) : z3vExact 3 (ringLocPow z3 q3fThree s) s :=
  ⟨q3_pow_ge s, q3_pow_neZero s⟩

/-- **A2c-2d: 3ⁿ の正則性** — 3ⁿ·d = 0 ⟹ d = 0（zp_p_regular の反復・整域性）。 -/
theorem q3_pow_regular : ∀ (n : Nat) {d : z3.carrier}
    (_ : z3.mul (rpow z3 q3fThree n) d = z3.zero), d = z3.zero := by
  intro n
  induction n with
  | zero =>
    intro d h
    have h0 : z3.mul z3.one d = z3.zero := h
    rw [z3.one_mul] at h0
    exact h0
  | succ n ih =>
    intro d h
    have hstep : z3.mul (rpow z3 q3fThree n) (z3.mul q3fThree d) = z3.zero := by
      rw [← z3.mul_assoc]; exact h
    exact zp_p_regular 3 (by omega) (ih hstep)

/-- 分母（3 冪）の正則性（局所化の非退化・単射性の核）。 -/
theorem q3S_regular {t : z3.carrier} (ht : q3S.set t) {d : z3.carrier}
    (h : z3.mul t d = z3.zero) : d = z3.zero := by
  obtain ⟨n, hn⟩ := ht
  rw [hn, q3_ringLocPow_eq_rpow z3 q3fThree n] at h
  exact q3_pow_regular n h

/-! ## A2c-3: 非退化・埋め込み・可逆性・一様化子 -/

/-- **A2c-3a: ℚ₃ は非退化**（0 ≠ 1・3 冪の正則性から）。 -/
theorem q3f_zero_ne_one : q3Ring.zero ≠ q3Ring.one := by
  intro h
  have h' : Quot.mk (ringLocRel q3S) ringLocZero
      = Quot.mk (ringLocRel q3S) ringLocOne := h
  obtain ⟨t, ht, e⟩ := q3f_exact h'
  obtain ⟨nn, hn⟩ := ht
  have e2 : z3.mul t (z3.mul z3.zero z3.one) = z3.mul t (z3.mul z3.one z3.one) := e
  rw [cring_zero_mul z3 z3.one, z3.mul_comm t z3.zero, cring_zero_mul z3 t,
      z3.one_mul z3.one, cring_mul_one z3 t] at e2
  have hne := neZeroAt_ne_zero 3 (ringLocPow z3 q3fThree nn) (q3_pow_neZero nn)
  apply hne
  rw [← hn]
  exact e2.symm

/-- **A2c-3b: ℤ₃ ↪ ℚ₃**（普遍写像 r↦r/1 の単射・3 冪の正則性から）。 -/
theorem q3f_embed_inj {a b : z3.carrier}
    (h : (ringLocMap z3 q3S).map a = (ringLocMap z3 q3S).map b) : a = b := by
  have h' : Quot.mk (ringLocRel q3S) (ringLocOfElem a)
      = Quot.mk (ringLocRel q3S) (ringLocOfElem b) := h
  obtain ⟨t, ht, e⟩ := q3f_exact h'
  have e2 : z3.mul t (z3.mul a z3.one) = z3.mul t (z3.mul b z3.one) := e
  rw [cring_mul_one z3 a, cring_mul_one z3 b] at e2
  apply cring_eq_of_sub_zero z3
  apply q3S_regular ht
  show z3.mul t (z3.add a (z3.neg b)) = z3.zero
  rw [z3.left_distrib t a (z3.neg b), ringLoc_mul_neg z3 t b, e2]
  exact cring_add_neg z3 (z3.mul t b)

/-- **A2c-3c: 3 は ℚ₃ で可逆**（局所化の S 可逆性・witness 形）。 -/
theorem q3f_three_unit :
    ∃ y : q3Ring.carrier,
      q3Ring.mul ((ringLocMap z3 q3S).map q3fThree) y = q3Ring.one :=
  ringLocRf_f_unit z3 q3fThree

/-- **A2c-3d: 3 は uniformizer**（ℤ₃ の素元 v(3)=1 かつ ℤ₃ の単数でない）。 -/
theorem q3f_uniformizer : z3vExact 3 q3fThree 1 ∧ ¬ IsZpUnit 3 q3fThree := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- z3vGe 3 3 1 : (3).val 1 = [0]（3 ∣ 3）
    show Quot.mk (modCong (3 ^ 1)).rel ((3 : Nat) : Int)
      = Quot.mk (modCong (3 ^ 1)).rel 0
    apply Quot.sound
    show ((3 ^ 1 : Nat) : Int) ∣ ((3 : Nat) : Int) - 0
    refine ⟨1, ?_⟩
    rw [Nat.pow_one]
    omega
  · -- ¬ z3vGe 3 3 2 : (3).val 2 ≠ [0]（9 ∤ 3）
    intro hh
    have hh' : Quot.mk (modCong (3 ^ 2)).rel ((3 : Nat) : Int)
        = Quot.mk (modCong (3 ^ 2)).rel 0 := hh
    obtain ⟨kk, hkk⟩ := quot_exact intGrp (modCong (3 ^ 2)) hh'
    have h9 : (3 : Nat) ^ 2 = 9 := rfl
    rw [h9] at hkk
    omega
  · -- ¬ IsZpUnit 3 3（3 はレベル 1 の代表 3 で 3 ∣ 3）
    rintro ⟨aa, haa, hna⟩
    have haa' : Quot.mk (modCong (3 ^ 1)).rel ((3 : Nat) : Int)
        = Quot.mk (modCong (3 ^ 1)).rel aa := haa
    obtain ⟨kk, hkk⟩ := quot_exact intGrp (modCong (3 ^ 1)) haa'
    rw [Nat.pow_one] at hkk
    apply hna
    exact ⟨1 - kk, by omega⟩

/-! ## A2c-4（★本丸）: ∃ 形体性 — 非零 witness 付き元の逆元を明示構成 -/

/-- **A2c-4（★）: ∃ 形体性** — 分子 a が正の非零 witness（¬ z3vGe a (k+1)）を持つ
    元 mk(a, 3ⁿ) は ℚ₃ で可逆。逆元 y = mk(3ⁿ·u⁻¹, 3ᵛ) を 3^v·u 分解（z3v_extract）と
    明示逆元 zpUnitInv で構成する。total inv は主張しない（§3.1 の忠実版）。 -/
theorem q3f_has_inverses (a : z3.carrier) (n k : Nat)
    (h : ¬ z3vGe 3 a (k + 1)) :
    ∃ y : q3Ring.carrier,
      q3Ring.mul
        (Quot.mk (ringLocRel q3S) ⟨a, ringLocPow z3 q3fThree n, ⟨n, rfl⟩⟩) y
        = q3Ring.one := by
  obtain ⟨v, u, _hvk, hu, he, _hex⟩ := z3v_extract k a h
  refine ⟨Quot.mk (ringLocRel q3S)
    ⟨z3.mul (ringLocPow z3 q3fThree n) (zpUnitInv 3 isPrime_three u hu),
     ringLocPow z3 q3fThree v, ⟨v, rfl⟩⟩, ?_⟩
  have huinv : z3.mul u (zpUnitInv 3 isPrime_three u hu) = z3.one := by
    rw [z3.mul_comm u (zpUnitInv 3 isPrime_three u hu)]
    exact zpUnitInv_mul 3 isPrime_three u hu
  have ha_eq : a = z3.mul (ringLocPow z3 q3fThree v) u := by
    rw [q3_ringLocPow_eq_zpPow v]; exact he
  have hcore : z3.mul a
        (z3.mul (ringLocPow z3 q3fThree n) (zpUnitInv 3 isPrime_three u hu))
      = z3.mul (ringLocPow z3 q3fThree n) (ringLocPow z3 q3fThree v) := by
    rw [ha_eq,
      cring_mul_mul_swap' z3 (ringLocPow z3 q3fThree v) u
        (ringLocPow z3 q3fThree n) (zpUnitInv 3 isPrime_three u hu),
      huinv,
      cring_mul_one z3 (z3.mul (ringLocPow z3 q3fThree v) (ringLocPow z3 q3fThree n)),
      z3.mul_comm (ringLocPow z3 q3fThree v) (ringLocPow z3 q3fThree n)]
  apply Quot.sound
  refine ⟨z3.one, q3S.one_mem, ?_⟩
  show z3.mul z3.one
      (z3.mul (z3.mul a (z3.mul (ringLocPow z3 q3fThree n)
        (zpUnitInv 3 isPrime_three u hu))) z3.one)
    = z3.mul z3.one (z3.mul z3.one
        (z3.mul (ringLocPow z3 q3fThree n) (ringLocPow z3 q3fThree v)))
  rw [z3.one_mul,
      cring_mul_one z3 (z3.mul a (z3.mul (ringLocPow z3 q3fThree n)
        (zpUnitInv 3 isPrime_three u hu))),
      z3.one_mul, z3.one_mul]
  exact hcore

/-! ## A2c-5: ℤ 値付値の関係形（付値の well-defined・加法性・整数環 O=ℤ₃） -/

/-- **A2c-5a: ℚ₃ の付値の関係形**（ℤ 値。x=mk(a,3ⁿ)・a の厳密付値 v ⟹ κ=v−n）。
    total 付値関数を避けた忠実版。 -/
def q3fValRel (x : q3Ring.carrier) (κ : Int) : Prop :=
  ∃ (a : z3.carrier) (nn v : Nat),
    x = Quot.mk (ringLocRel q3S) ⟨a, ringLocPow z3 q3fThree nn, ⟨nn, rfl⟩⟩ ∧
    z3vExact 3 a v ∧ κ = (v : Int) - (nn : Int)

/-- 厳密付値の一意性（z3vExact は高々 1 つ）。 -/
theorem z3v_exact_unique {x : z3.carrier} {α β : Nat}
    (hα : z3vExact 3 x α) (hβ : z3vExact 3 x β) : α = β := by
  obtain ⟨hαge, hαgt⟩ := hα
  obtain ⟨hβge, hβgt⟩ := hβ
  cases Nat.lt_trichotomy α β with
  | inl hlt => exact absurd (z3vGe_antitone 3 x (by omega : α + 1 ≤ β) hβge) hαgt
  | inr h => cases h with
    | inl heq => exact heq
    | inr hgt => exact absurd (z3vGe_antitone 3 x (by omega : β + 1 ≤ α) hαge) hβgt

/-- **A2c-5b: 付値の代表非依存**（well-defined）。 -/
theorem q3f_val_wd {x : q3Ring.carrier} {κ κ' : Int}
    (h1 : q3fValRel x κ) (h2 : q3fValRel x κ') : κ = κ' := by
  obtain ⟨a, m, v, hx1, hav, hκ⟩ := h1
  obtain ⟨b, l, w, hx2, hbw, hκ'⟩ := h2
  have heq : Quot.mk (ringLocRel q3S) ⟨a, ringLocPow z3 q3fThree m, ⟨m, rfl⟩⟩
      = Quot.mk (ringLocRel q3S) ⟨b, ringLocPow z3 q3fThree l, ⟨l, rfl⟩⟩ := by
    rw [← hx1, ← hx2]
  obtain ⟨t, ht, e⟩ := q3f_exact heq
  obtain ⟨s, hs⟩ := ht
  have e2 : z3.mul t (z3.mul a (ringLocPow z3 q3fThree l))
      = z3.mul t (z3.mul b (ringLocPow z3 q3fThree m)) := e
  have ht' : z3vExact 3 t s := by rw [hs]; exact q3_pow_exact s
  have hL : z3vExact 3 (z3.mul t (z3.mul a (ringLocPow z3 q3fThree l)))
      (s + (v + l)) :=
    z3v_exact_mul ht' (z3v_exact_mul hav (q3_pow_exact l))
  have hR : z3vExact 3 (z3.mul t (z3.mul b (ringLocPow z3 q3fThree m)))
      (s + (w + m)) :=
    z3v_exact_mul ht' (z3v_exact_mul hbw (q3_pow_exact m))
  rw [← e2] at hR
  have hval := z3v_exact_unique hL hR
  rw [hκ, hκ']
  omega

/-- **A2c-5c: 付値の加法性** v(x·y) = v(x)+v(y)。 -/
theorem q3f_val_mul {x y : q3Ring.carrier} {κ lam : Int}
    (hx : q3fValRel x κ) (hy : q3fValRel y lam) :
    q3fValRel (q3Ring.mul x y) (κ + lam) := by
  obtain ⟨a, m, v, hx1, hav, hκ⟩ := hx
  obtain ⟨b, l, w, hy1, hbw, hlam⟩ := hy
  have hmulrep : q3Ring.mul x y
      = Quot.mk (ringLocRel q3S)
          ⟨z3.mul a b, ringLocPow z3 q3fThree (m + l), ⟨m + l, rfl⟩⟩ := by
    rw [hx1, hy1]
    show Quot.mk (ringLocRel q3S)
        (ringLocMul ⟨a, ringLocPow z3 q3fThree m, ⟨m, rfl⟩⟩
          ⟨b, ringLocPow z3 q3fThree l, ⟨l, rfl⟩⟩)
      = Quot.mk (ringLocRel q3S)
          ⟨z3.mul a b, ringLocPow z3 q3fThree (m + l), ⟨m + l, rfl⟩⟩
    apply congrArg (Quot.mk (ringLocRel q3S))
    apply ringLocPre_ext
    · rfl
    · exact (ringLocPow_add z3 q3fThree m l).symm
  refine ⟨z3.mul a b, m + l, v + w, hmulrep, z3v_exact_mul hav hbw, ?_⟩
  rw [hκ, hlam]
  omega

/-- **A2c-5d: 整数環 O = ℤ₃** — 付値 ≥ 0 の元は分母 3⁰=1 で表せる（ℤ₃ の像）。 -/
theorem q3f_ring_of_val {x : q3Ring.carrier} {κ : Int}
    (h : q3fValRel x κ) (hκ : 0 ≤ κ) :
    ∃ c : z3.carrier,
      x = Quot.mk (ringLocRel q3S) ⟨c, ringLocPow z3 q3fThree 0, ⟨0, rfl⟩⟩ := by
  obtain ⟨a, m, v, hx, hav, hκeq⟩ := h
  have hvm : m ≤ v := by rw [hκeq] at hκ; omega
  obtain ⟨v', u', _hv'le, hu', hae, hex'⟩ := z3v_extract v a hav.2
  have hvv : v' = v := z3v_exact_unique hex' hav
  subst hvv
  have ha' : a = z3.mul (ringLocPow z3 q3fThree v') u' := by
    rw [q3_ringLocPow_eq_zpPow v']; exact hae
  have hc : a = z3.mul (ringLocPow z3 q3fThree m)
      (z3.mul (ringLocPow z3 q3fThree (v' - m)) u') := by
    rw [← z3.mul_assoc, ← ringLocPow_add z3 q3fThree m (v' - m),
      (by omega : m + (v' - m) = v')]
    exact ha'
  refine ⟨z3.mul (ringLocPow z3 q3fThree (v' - m)) u', ?_⟩
  rw [hx]
  apply Quot.sound
  refine ⟨z3.one, q3S.one_mem, ?_⟩
  show z3.mul z3.one (z3.mul a z3.one)
    = z3.mul z3.one (z3.mul (z3.mul (ringLocPow z3 q3fThree (v' - m)) u')
        (ringLocPow z3 q3fThree m))
  rw [z3.one_mul, z3.one_mul, cring_mul_one z3 a, hc,
    z3.mul_comm (ringLocPow z3 q3fThree m)
      (z3.mul (ringLocPow z3 q3fThree (v' - m)) u')]

end IUT
