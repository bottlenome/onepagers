/-
  IUT/Finiteness.lean — M17（有限性の本格的定義）の形式化

  これまで有限性は `BoundedExponent`（有界指数）という**帰結の代理**で
  扱ってきた。本モジュールは有限性そのものを定義し、その理論の核心を
  完全証明して、代理が正当だったことを定理にする:

  * M17-1 `pigeonhole` — **鳩の巣原理**（[0,n] から [0,n) への写像は
    必ず衝突する）。有限性理論の基本定理。決定可能な有界探索による
    場合分けで証明（選択公理不使用）
  * M17-2 `inj_range_le` / `card_unique` — 単射は基数を増やさない・
    **基数の一意性**（全単射 α ≅ [0,m) ≅ [0,n) なら m = n）
  * M17-3 `Finite` / `Listable` — 有限性の二定義（数え上げ版 =
    [0,n) への単射コード / 枚挙版 = 全要素リスト）
  * M17-4 `finite_bounded_exponent` — **有限群は有界指数を持つ**
    （指数 n! で消える）: 鳩の巣で冪の衝突 g^i = g^j を見つけ、
    簡約律で g^(j−i) = 1、j−i ∣ n! で一様化。M9 以来の代理
    `BoundedExponent` が `Finite` の帰結であることの機械検証
  * M17-5 `zmod_finite` / `zmod_listable` — **ℤ/n は本当に有限**
    （非負剰余によるコードと枚挙の構成）。よって M13 の
    `zmodSystem` は正真正銘「有限群の逆系」であり、ẑ は本格的な
    意味で副有限群である

  全て sorry なし・選択公理不使用。
-/
import IUT.Profinite

namespace IUT

/-- 単射性（一般の関数）。 -/
def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ a b, f a = f b → a = b

/-- 有界存在の決定可能性（自前インスタンス、選択公理回避）。 -/
def decidableBoundedExists (P : Nat → Prop) [DecidablePred P] :
    ∀ n, Decidable (∃ i, i ≤ n ∧ P i)
  | 0 =>
    if h : P 0 then isTrue ⟨0, Nat.le_refl 0, h⟩
    else isFalse (fun ⟨i, hi, hPi⟩ => by
      have h0 : i = 0 := Nat.le_zero.mp hi
      exact h (h0 ▸ hPi))
  | n + 1 =>
    match decidableBoundedExists P n with
    | isTrue h => isTrue (match h with
        | ⟨i, hi, hPi⟩ => ⟨i, Nat.le_trans hi (Nat.le_succ n), hPi⟩)
    | isFalse h =>
      if hP : P (n + 1) then isTrue ⟨n + 1, Nat.le_refl _, hP⟩
      else isFalse (fun ⟨i, hi, hPi⟩ => by
        -- 注意: この文脈には ¬∃ 仮定があるため omega を使うと
        -- 前処理が Classical.choice を引き込む。明示補題で回避
        cases Nat.lt_or_ge i (n + 1) with
        | inl h1 => exact h ⟨i, Nat.le_of_lt_succ h1, hPi⟩
        | inr h2 => exact hP ((Nat.le_antisymm hi h2) ▸ hPi))

instance (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    Decidable (∃ i, i ≤ n ∧ P i) :=
  decidableBoundedExists P n

/-- **定理 (M17-1): 鳩の巣原理** — f が [0,n] を [0,n) に送るなら
    衝突 f i = f j (i < j ≤ n) が存在する。 -/
theorem pigeonhole : ∀ (n : Nat) (f : Nat → Nat),
    (∀ i, i ≤ n → f i < n) → ∃ i j, i < j ∧ j ≤ n ∧ f i = f j := by
  intro n
  induction n with
  | zero =>
    intro f hf
    exact absurd (hf 0 (Nat.le_refl 0)) (by omega)
  | succ n ih =>
    intro f hf
    -- ∃ への場合分けは自前の決定手続きを明示適用（選択公理回避）
    cases decidableBoundedExists (fun i => f i = f (n + 1)) n with
    | isTrue hex =>
      obtain ⟨i, hi, hfi⟩ := hex
      exact ⟨i, n + 1, by omega, Nat.le_refl _, hfi⟩
    | isFalse hex =>
      by_cases hfn : f (n + 1) = n
      · -- f (n+1) = n なら f は [0,n] 上で n を取らない
        have hrestrict : ∀ i, i ≤ n → f i < n := by
          intro i hi
          have h1 := hf i (by omega)
          have h2 : f i ≠ n := fun h => hex ⟨i, hi, by rw [h, hfn]⟩
          omega
        obtain ⟨i, j, hij, hj, hfij⟩ := ih f hrestrict
        exact ⟨i, j, hij, by omega, hfij⟩
      · -- f i = n を f (n+1) に付け替えた g で帰納法
        have hg : ∀ i, i ≤ n → (if f i = n then f (n + 1) else f i) < n := by
          intro i hi
          by_cases h : f i = n
          · rw [if_pos h]
            have := hf (n + 1) (Nat.le_refl _)
            omega
          · rw [if_neg h]
            have := hf i (by omega)
            omega
        obtain ⟨i, j, hij, hj, hgij⟩ :=
          ih (fun i => if f i = n then f (n + 1) else f i) hg
        by_cases hfi : f i = n
        · by_cases hfj : f j = n
          · exact ⟨i, j, hij, by omega, by rw [hfi, hfj]⟩
          · rw [if_pos hfi, if_neg hfj] at hgij
            exact absurd ⟨j, hj, hgij.symm⟩ hex
        · by_cases hfj : f j = n
          · rw [if_neg hfi, if_pos hfj] at hgij
            exact absurd ⟨i, by omega, hgij⟩ hex
          · rw [if_neg hfi, if_neg hfj] at hgij
            exact ⟨i, j, hij, by omega, hgij⟩

/-- **定理 (M17-2a)**: [0,m) から [0,n) への単射があれば m ≤ n。 -/
theorem inj_range_le {m n : Nat} (f : Nat → Nat)
    (hbound : ∀ i, i < m → f i < n)
    (hinj : ∀ i j, i < m → j < m → f i = f j → i = j) : m ≤ n := by
  cases Nat.lt_or_ge n m with
  | inr h => exact h
  | inl h =>
    exfalso
    obtain ⟨i, j, hij, hj, hfij⟩ :=
      pigeonhole n f (fun i hi => hbound i (by omega))
    have := hinj i j (by omega) (by omega) hfij
    omega

/-- **定理 (M17-2b): 基数の一意性** — α が [0,m) とも [0,n) とも
    全単射（コード・デコード対）で結ばれるなら m = n。 -/
theorem card_unique {α : Type} {m n : Nat}
    (c₁ : α → Nat) (d₁ : Nat → α)
    (hb₁ : ∀ a, c₁ a < m) (hcd₁ : ∀ a, d₁ (c₁ a) = a)
    (hdc₁ : ∀ i, i < m → c₁ (d₁ i) = i)
    (c₂ : α → Nat) (d₂ : Nat → α)
    (hb₂ : ∀ a, c₂ a < n) (hcd₂ : ∀ a, d₂ (c₂ a) = a)
    (hdc₂ : ∀ i, i < n → c₂ (d₂ i) = i) : m = n := by
  have hmn : m ≤ n := by
    apply inj_range_le (fun i => c₂ (d₁ i)) (fun i _ => hb₂ _)
    intro i j hi hj h
    have h1 : d₁ i = d₁ j := by
      have := congrArg d₂ h
      rw [hcd₂, hcd₂] at this
      exact this
    have := congrArg c₁ h1
    rw [hdc₁ i hi, hdc₁ j hj] at this
    exact this
  have hnm : n ≤ m := by
    apply inj_range_le (fun i => c₁ (d₂ i)) (fun i _ => hb₁ _)
    intro i j hi hj h
    have h1 : d₂ i = d₂ j := by
      have := congrArg d₁ h
      rw [hcd₁, hcd₁] at this
      exact this
    have := congrArg c₂ h1
    rw [hdc₂ i hi, hdc₂ j hj] at this
    exact this
  omega

/-- **有限性（数え上げ版、M17-3a）**: [0,n) への単射コードを持つ。 -/
def Finite (α : Type) : Prop :=
  ∃ (n : Nat) (code : α → Nat), (∀ a, code a < n) ∧ Injective code

/-- **有限性（枚挙版、M17-3b）**: 全要素を尽くすリストを持つ。 -/
def Listable (α : Type) : Prop :=
  ∃ l : List α, ∀ a : α, a ∈ l

/-! ## 有限群は有界指数を持つ -/

/-- 冪の加法則。 -/
theorem Grp.pow_comm_self (G : Grp) (g : G.carrier) (a : Nat) :
    G.mul g (G.pow g a) = G.mul (G.pow g a) g := by
  induction a with
  | zero =>
    show G.mul g G.one = G.mul G.one g
    rw [G.mul_one, G.one_mul]
  | succ a ih =>
    show G.mul g (G.mul g (G.pow g a)) = G.mul (G.mul g (G.pow g a)) g
    rw [G.mul_assoc, ih]

theorem Grp.pow_add (G : Grp) (g : G.carrier) (a b : Nat) :
    G.pow g (a + b) = G.mul (G.pow g a) (G.pow g b) := by
  induction b with
  | zero =>
    show G.pow g a = G.mul (G.pow g a) G.one
    rw [G.mul_one]
  | succ b ih =>
    show G.mul g (G.pow g (a + b)) = G.mul (G.pow g a) (G.mul g (G.pow g b))
    rw [ih, ← G.mul_assoc, G.pow_comm_self, G.mul_assoc]

/-- 階乗。 -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n := by
  intro n
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    show 0 < (n + 1) * fact n
    exact Nat.mul_pos (by omega) ih

/-- 1 ≤ k ≤ n なら k ∣ n!。 -/
theorem dvd_fact : ∀ {k n : Nat}, 1 ≤ k → k ≤ n → k ∣ fact n := by
  intro k n hk hkn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : k = n + 1
    · exact ⟨fact n, by rw [h]; rfl⟩
    · have hkn' : k ≤ n := by omega
      obtain ⟨m, hm⟩ := ih hkn'
      refine ⟨(n + 1) * m, ?_⟩
      show (n + 1) * fact n = k * ((n + 1) * m)
      rw [hm, ← Nat.mul_assoc, Nat.mul_comm (n + 1) k, Nat.mul_assoc]

/-- 冪の消滅は倍数に伝播する。 -/
theorem Grp.pow_mul_eq_one (G : Grp) (g : G.carrier) (d m : Nat)
    (h : G.pow g d = G.one) : G.pow g (d * m) = G.one := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show G.pow g (d * m + d) = G.one
    rw [G.pow_add, ih, h, G.one_mul]

/-- **定理 (M17-4): 有限群は有界指数を持つ**（指数 n!）—
    鳩の巣原理で冪の衝突 g^i = g^j を見つけ、簡約律で
    g^(j−i) = 1、(j−i) ∣ n! で一様化する。M9 以来の有限性代理
    `BoundedExponent` が本格的有限性 `Finite` の帰結であることの
    機械検証。 -/
theorem finite_bounded_exponent (G : Grp) (h : Finite G.carrier) :
    BoundedExponent G := by
  obtain ⟨n, code, hbound, hinj⟩ := h
  cases n with
  | zero => exact absurd (hbound G.one) (by omega)
  | succ n =>
    refine ⟨fact (n + 1), fact_pos _, ?_⟩
    intro g
    obtain ⟨i, j, hij, hj, hcode⟩ := pigeonhole (n + 1)
      (fun k => code (G.pow g k)) (fun k _ => hbound _)
    have hpow : G.pow g i = G.pow g j := hinj _ _ hcode
    have hd : G.pow g (j - i) = G.one := by
      have h1 : G.pow g (i + (j - i)) = G.mul (G.pow g i) (G.pow g (j - i)) :=
        G.pow_add g i (j - i)
      have h2 : i + (j - i) = j := by omega
      rw [h2, ← hpow] at h1
      have h3 : G.mul (G.pow g i) G.one = G.mul (G.pow g i) (G.pow g (j - i)) := by
        rw [G.mul_one]
        exact h1
      exact (G.mul_left_cancel h3).symm
    obtain ⟨m, hm⟩ := dvd_fact (k := j - i) (n := n + 1) (by omega) (by omega)
    rw [hm]
    exact G.pow_mul_eq_one g (j - i) m hd

/-! ## ℤ/n の本格的有限性 -/

/-- 代表元は自分の非負剰余と合同。 -/
theorem modCong_emod (n : Nat) (a : Int) :
    (modCong n).rel a (a % ((n : Nat) : Int)) := by
  refine ⟨a / ((n : Nat) : Int), ?_⟩
  have h := Int.mul_ediv_add_emod a ((n : Nat) : Int)
  revert h
  generalize ((n : Nat) : Int) * (a / ((n : Nat) : Int)) = T
  generalize a % ((n : Nat) : Int) = R
  intro h
  omega

/-- 合同なら非負剰余が一致する。 -/
theorem emod_eq_of_dvd {n : Nat} {a b : Int}
    (h : ((n : Nat) : Int) ∣ (a - b)) :
    a % ((n : Nat) : Int) = b % ((n : Nat) : Int) := by
  obtain ⟨k, hk⟩ := h
  have ha : a = b + ((n : Nat) : Int) * k := by
    revert hk
    generalize ((n : Nat) : Int) * k = T
    intro hk
    omega
  rw [ha]
  exact Int.add_mul_emod_self_left b ((n : Nat) : Int) k

/-- 非負剰余の一致から合同が戻る。 -/
theorem dvd_of_emod_eq {n : Nat} {a b : Int}
    (h : a % ((n : Nat) : Int) = b % ((n : Nat) : Int)) :
    ((n : Nat) : Int) ∣ (a - b) := by
  refine ⟨a / ((n : Nat) : Int) - b / ((n : Nat) : Int), ?_⟩
  have h1 := Int.mul_ediv_add_emod a ((n : Nat) : Int)
  have h2 := Int.mul_ediv_add_emod b ((n : Nat) : Int)
  rw [Int.mul_sub]
  revert h1 h2 h
  generalize ((n : Nat) : Int) * (a / ((n : Nat) : Int)) = T1
  generalize ((n : Nat) : Int) * (b / ((n : Nat) : Int)) = T2
  generalize a % ((n : Nat) : Int) = R1
  generalize b % ((n : Nat) : Int) = R2
  intro h1 h2 h
  omega

/-- **定理 (M17-5a): ℤ/n は有限**（非負剰余による単射コード）。
    よって M13 の zmodSystem は正真正銘の有限群の逆系であり、
    ẑ は本格的な意味の副有限群である。 -/
theorem zmod_finite (n : Nat) (hn : 0 < n) : Finite (zmod n).carrier := by
  have hpos : (0 : Int) < ((n : Nat) : Int) := by omega
  have hne : ((n : Nat) : Int) ≠ 0 := by omega
  refine ⟨n, Quot.lift (fun a => (a % ((n : Nat) : Int)).toNat)
    (fun a b hab => by
      show (a % ((n : Nat) : Int)).toNat = (b % ((n : Nat) : Int)).toNat
      rw [emod_eq_of_dvd hab]), ?_, ?_⟩
  · intro x
    induction x using Quot.ind; rename_i a
    show (a % ((n : Nat) : Int)).toNat < n
    have h1 := Int.emod_lt_of_pos a hpos
    have h2 := Int.emod_nonneg a hne
    revert h1 h2
    generalize a % ((n : Nat) : Int) = R
    intro h1 h2
    omega
  · intro x y h
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    apply Quot.sound
    apply dvd_of_emod_eq
    have h1 := Int.emod_lt_of_pos a hpos
    have h2 := Int.emod_nonneg a hne
    have h3 := Int.emod_lt_of_pos b hpos
    have h4 := Int.emod_nonneg b hne
    have h5 : (a % ((n : Nat) : Int)).toNat = (b % ((n : Nat) : Int)).toNat := h
    revert h1 h2 h3 h4 h5
    generalize a % ((n : Nat) : Int) = R1
    generalize b % ((n : Nat) : Int) = R2
    intro h1 h2 h3 h4 h5
    omega

/-- **定理 (M17-5b): ℤ/n は枚挙可能**（[mk 0, …, mk (n−1)] が全て）。 -/
theorem zmod_listable (n : Nat) (hn : 0 < n) : Listable (zmod n).carrier := by
  refine ⟨(List.range n).map
    (fun k => Quot.mk (modCong n).rel ((k : Nat) : Int)), ?_⟩
  intro x
  induction x using Quot.ind; rename_i a
  have hmem : (a % ((n : Nat) : Int)).toNat ∈ List.range n := by
    rw [List.mem_range]
    have h1 := Int.emod_lt_of_pos a (show (0 : Int) < ((n : Nat) : Int) by omega)
    have h2 := Int.emod_nonneg a (show ((n : Nat) : Int) ≠ 0 by omega)
    revert h1 h2
    generalize a % ((n : Nat) : Int) = R
    intro h1 h2
    omega
  rw [List.mem_map]
  refine ⟨(a % ((n : Nat) : Int)).toNat, hmem, ?_⟩
  apply Quot.sound
  -- rel ↑(toNat (a % n)) a: ↑toNat = a % n（非負）、これは a と合同
  have htn : (((a % ((n : Nat) : Int)).toNat : Nat) : Int) = a % ((n : Nat) : Int) := by
    have h2 := Int.emod_nonneg a (show ((n : Nat) : Int) ≠ 0 by omega)
    revert h2
    generalize a % ((n : Nat) : Int) = R
    intro h2
    omega
  rw [htn]
  exact (modCong n).symm (modCong_emod n a)

end IUT
