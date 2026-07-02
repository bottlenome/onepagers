/-
  IUT/MuLSubgroup.lean — M121F: μ_l 部分群 — l ∣ p−1 の原始 l 乗根と完全性

  柱E E-1（#39）第二切片の ℤ/p・ℤ_p 側: μ_l 係数シクロトーム ↔ O^×
  同一視の材料。l ∣ p−1 のとき (ℤ/p)^× に**位数ちょうど l の元**
  （原始 l 乗根）が存在し（原始根 g の (p−1)/l 乗、M102-9 の冪位数
  公式）、その冪 c^0, …, c^{l−1} が相異なる l 個の l 乗根を与え、
  さらに **x^l = 1 の任意の解はこの冪のどれか**（完全性 = 因数定理
  M96 の roots_bound による個数上界）であることを機械検証する。
  Teichmüller 持ち上げ teichBar（M101/M104）で ℤ_p 側にも移送し、
  zpPow z l = 1 かつ冪が相異なる（= 位数ちょうど l の）1 の原始
  l 乗根 z = ω(a) を構成する。

  * M121F-1 `order_l_exists` — **位数 l の元の存在**: l ∣ p−1 なら
    ∃ c 単数, ord c = l（原始根 M103 + 冪の位数 M102-9）
  * M121F-2 `mu_l_root` / `mu_l_powers_distinct` / `mu_l_pow_root` —
    位数 l の witness c について c^l = 1・c^0, …, c^{l−1} の相異性
    （M102-8）・全ての冪 (c^k)^l = 1（指数法則）
  * M121F-3 `mu_l_complete` — **完全性（本丸）**: x^l = 1 なら
    ∃ k ≤ l−1, c^k = x（有界探索 M17 の決定可能性で witness を構成的
    に取り、見つからなければ c^0, …, c^{l−1}, x の l+1 個の相異なる
    元が全て X^l − 1 の根となり bin_roots_bound（M96）に矛盾。
    M104-3 generator_covers の l = p−1 特殊形の一般化）
  * M121F-4 `mu_l_zp_exists` — **ℤ_p への持ち上げ**: ∃ z ∈ ℤ_p,
    z^l = 1 ∧ 冪 z^0, …, z^{l−1} 相異 ∧ z = ω(a)（p ∤ a）
    （teichBar_pow M104-2 + 単射性 M101-7 による移送）
  * M121F-5 `MuLSubgroupData` / `muLSubgroupData` /
    `muLSubgroup_exists` — 総括レコードと witness・Nonempty

  意義: [EtTh] の μ_l 係数シクロトーム ↔ O^× 同一視の ℤ/p・ℤ_p 側
  半分。位数ちょうど l の元の存在（原始根の (p−1)/l 乗）・冪の相異性・
  **l 乗根の完全性（因数定理）**。テータ群 mod l の中心（M98F/M116F）
  との接合は次層。

  正直申告: 完全性 mu_l_complete は指示の ¬∀≠ 形より強い ∃ 形
  （∃ k ≤ l−1, c^k = x）で証明した（decidableBoundedExists による
  構成的 witness 抽出、M104-3 と同じ流儀）。また x^l = 1 から x の
  単数性は自動的に従うため x の単数性仮定は不要だった。ℤ_p 側は
  z^l = 1 に加えて冪の相異性（位数ちょうど l）まで持ち上げ済み。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.CyclicUnits

namespace IUT

/-! ## 位数ちょうど l の元の存在 -/

/-- **定理 (M121F-1): 位数 l の元の存在** — l ∣ p−1 なら (ℤ/p)^× に
    位数ちょうど l の元（1 の原始 l 乗根）が存在する。原始根 g
    （ord g = p−1、M103）の m = (p−1)/l 乗を取り、冪の位数公式
    ord(g^m) = (p−1)/m = l（M102-9）で位数を計算する。 -/
theorem order_l_exists (p l : Nat) (hp : IsPrime p) (hl : 1 ≤ l)
    (hdvd : l ∣ p - 1) :
    ∃ c, IsZmodUnit p c ∧ zmodOrd p c = l := by
  obtain ⟨g, hg, hord⟩ := primitive_root_exists p hp
  obtain ⟨m, hm⟩ := hdvd
  have hp2 := hp.1
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hm
    omega
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
  have hmdvd : m ∣ zmodOrd p g := by
    rw [hord, hm, Nat.mul_comm l m]
    exact ⟨l, rfl⟩
  refine ⟨zmodPow (p ^ 1) g m, isZmodUnit_pow p hp hg m, ?_⟩
  rw [zmodOrd_pow_div p hp hg hm1 hmdvd, hord, hm, Nat.mul_comm l m,
    Nat.mul_div_cancel_left l hm1]

/-! ## 原始 l 乗根の性質（witness 形） -/

/-- **M121F-2a: l 乗して 1** — ord c = l なら c^l = 1
    （位数の定義的性質 M102-5c）。 -/
theorem mu_l_root (p l : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c)
    (ha : zmodOrd p c = l) :
    zmodPow (p ^ 1) c l = Quot.mk (modCong (p ^ 1)).rel 1 := by
  rw [← ha]
  exact zmodOrd_pow_eq_one p hp hc

/-- **M121F-2b: 冪の相異性** — ord c = l なら c^0, …, c^{l−1} は
    相異なる（M102-8 の instance。μ_l の位数がちょうど l の実質）。 -/
theorem mu_l_powers_distinct (p l : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c)
    (ha : zmodOrd p c = l) :
    ∀ i j, i < j → j < l → zmodPow (p ^ 1) c i ≠ zmodPow (p ^ 1) c j := by
  intro i j hij hj
  exact zmodOrd_powers_distinct p hp hc i j hij (by rw [ha]; exact hj)

/-- **M121F-2c: 全ての冪は l 乗根** — (c^k)^l = c^{kl} = (c^l)^k = 1
    （指数法則 M102-2d の付け替え）。 -/
theorem mu_l_pow_root (p l : Nat) (hp : IsPrime p)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c)
    (ha : zmodOrd p c = l) (k : Nat) :
    zmodPow (p ^ 1) (zmodPow (p ^ 1) c k) l
      = Quot.mk (modCong (p ^ 1)).rel 1 := by
  rw [← zmodPow_mul, Nat.mul_comm k l, zmodPow_mul,
    mu_l_root p l hp hc ha, zmodPow_one_base]

/-! ## 完全性（本丸）: x^l = 1 の解は c の冪に限る -/

/-- **定理 (M121F-3): 完全性** — ord c = l のとき x^l = 1 なる任意の
    x は c の冪 c^k（k ≤ l−1）。有界探索（M17 decidableBoundedExists）
    で witness を構成的に取り、見つからなければ c^0, …, c^{l−1}, x の
    l+1 個の相異なる元が全て X^l − 1 の根となり bin_roots_bound
    （M96 因数定理）に矛盾。M104-3 generator_covers（l = p−1）の
    任意の l ∣ p−1 への一般化。x の単数性は仮定不要（x^l = 1 が
    x·x^{l−1} = 1 を与えるため）。 -/
theorem mu_l_complete (p l : Nat) (hp : IsPrime p) (hl : 1 ≤ l)
    {c : (zmod (p ^ 1)).carrier} (hc : IsZmodUnit p c)
    (ha : zmodOrd p c = l)
    {x : (zmod (p ^ 1)).carrier}
    (hx : zmodPow (p ^ 1) x l = Quot.mk (modCong (p ^ 1)).rel 1) :
    ∃ k, k ≤ l - 1 ∧ zmodPow (p ^ 1) c k = x := by
  cases decidableBoundedExists
      (fun k => zmodEqb (p ^ 1) (zmodPow (p ^ 1) c k) x = true) (l - 1) with
  | isTrue h =>
    obtain ⟨k, hk, hP⟩ := h
    exact ⟨k, hk, zmodEqb_true hP⟩
  | isFalse h =>
    exfalso
    have hne : ∀ k, k ≤ l - 1 → zmodPow (p ^ 1) c k ≠ x := by
      intro k hk
      cases htest : zmodEqb (p ^ 1) (zmodPow (p ^ 1) c k) x with
      | true => exact absurd ⟨k, hk, htest⟩ h
      | false => exact zmodEqb_false htest
    have hdist : ∀ i j, i < j → j ≤ l - 1 + 1 →
        (fun i => if i ≤ l - 1 then zmodPow (p ^ 1) c i else x) i
          ≠ (fun i => if i ≤ l - 1 then zmodPow (p ^ 1) c i else x) j := by
      intro i j hij hj heq
      have heq' : (if i ≤ l - 1 then zmodPow (p ^ 1) c i else x)
          = (if j ≤ l - 1 then zmodPow (p ^ 1) c j else x) := heq
      cases Nat.lt_or_ge (l - 1) j with
      | inr hjle =>
        -- j ≤ l−1: 両方 c の冪 → 相異性（M102-8）に矛盾
        have hi' : i ≤ l - 1 := by omega
        rw [if_pos hi', if_pos hjle] at heq'
        exact zmodOrd_powers_distinct p hp hc i j hij
          (by rw [ha]; omega) heq'
      | inl hjgt =>
        -- j = l: r j = x、r i = c^i → 探索失敗の hne に矛盾
        have hi' : i ≤ l - 1 := by omega
        rw [if_pos hi', if_neg (by omega : ¬ j ≤ l - 1)] at heq'
        exact hne i hi' heq'
    have hroots : ∀ i, i ≤ l - 1 + 1 →
        rpow (zmodRing (p ^ 1))
          ((fun i => if i ≤ l - 1 then zmodPow (p ^ 1) c i else x) i)
          (l - 1 + 1)
        = (zmodRing (p ^ 1)).one := by
      intro i hi
      show rpow (zmodRing (p ^ 1))
          (if i ≤ l - 1 then zmodPow (p ^ 1) c i else x) (l - 1 + 1)
        = (zmodRing (p ^ 1)).one
      rw [← zmodPow_eq_rpow]
      have hcong : zmodPow (p ^ 1)
          (if i ≤ l - 1 then zmodPow (p ^ 1) c i else x) (l - 1 + 1)
          = zmodPow (p ^ 1)
            (if i ≤ l - 1 then zmodPow (p ^ 1) c i else x) l :=
        congrArg (zmodPow (p ^ 1) _) (by omega)
      rw [hcong]
      cases Nat.lt_or_ge (l - 1) i with
      | inr hile =>
        rw [if_pos hile]
        exact mu_l_pow_root p l hp hc ha i
      | inl higt =>
        rw [if_neg (by omega : ¬ i ≤ l - 1)]
        exact hx
    exact bin_roots_bound (zmodRing (p ^ 1)) (zmod_no_zero_div p hp)
      (zmodRing_one_ne_zero p hp) (zmodRing (p ^ 1)).one (l - 1)
      (fun i => if i ≤ l - 1 then zmodPow (p ^ 1) c i else x)
      hdist hroots

/-! ## ℤ_p への持ち上げ（Teichmüller 経由） -/

/-- **定理 (M121F-4): ℤ_p の原始 l 乗根** — l ∣ p−1 なら ℤ_p に
    z^l = 1 かつ冪 z^0, …, z^{l−1} が相異なる（= 位数ちょうど l の）
    元 z が存在し、z は Teichmüller 代表 ω(a)（p ∤ a）である。
    位数 l の c（M121F-1）を teichBar で持ち上げ、冪の交換
    teichBar_pow（M104-2）と μ 側相異性 mu_powers_distinct
    （M104-5a）で移送する。 -/
theorem mu_l_zp_exists (p l : Nat) (hp : IsPrime p) (hl : 1 ≤ l)
    (hdvd : l ∣ p - 1) :
    ∃ z : (Zp p).carrier, zpPow p z l = zpOne p
      ∧ (∀ i j, i < j → j < l → zpPow p z i ≠ zpPow p z j)
      ∧ ∃ a : Int, ¬ ((p : Nat) : Int) ∣ a ∧ z = teich p hp a := by
  obtain ⟨c, hc, ha⟩ := order_l_exists p l hp hl hdvd
  refine ⟨teichBar p hp c, ?_, ?_, ?_⟩
  · rw [← teichBar_pow, mu_l_root p l hp hc ha]
    show teich p hp 1 = zpOne p
    exact teich_one p hp
  · intro i j hij hj
    exact mu_powers_distinct p hp hc hij (by rw [ha]; exact hj)
  · obtain ⟨a, hca, hpa⟩ := hc
    refine ⟨a, hpa, ?_⟩
    rw [hca]

/-! ## 総括レコード -/

/-- **M121F-5a: 総括レコード** — μ_l 部分群の構成データ: 位数 l の
    元の存在・（任意の witness c についての）l 乗根性・冪の相異性・
    全冪の l 乗根性・完全性・ℤ_p 持ち上げ。[EtTh] μ_l 係数
    シクロトーム同一視の ℤ/p・ℤ_p 側半分のパッケージ。 -/
structure MuLSubgroupData (p l : Nat) (hp : IsPrime p) (hl : 1 ≤ l)
    (hdvd : l ∣ p - 1) where
  /-- 位数ちょうど l の元（原始 l 乗根）の存在。 -/
  order_l : ∃ c, IsZmodUnit p c ∧ zmodOrd p c = l
  /-- witness は 1 の l 乗根。 -/
  root : ∀ c : (zmod (p ^ 1)).carrier, IsZmodUnit p c → zmodOrd p c = l →
    zmodPow (p ^ 1) c l = Quot.mk (modCong (p ^ 1)).rel 1
  /-- 冪 c^0, …, c^{l−1} は相異なる。 -/
  powers_distinct : ∀ c : (zmod (p ^ 1)).carrier, IsZmodUnit p c →
    zmodOrd p c = l → ∀ i j, i < j → j < l →
      zmodPow (p ^ 1) c i ≠ zmodPow (p ^ 1) c j
  /-- 全ての冪 c^k は 1 の l 乗根。 -/
  pow_root : ∀ c : (zmod (p ^ 1)).carrier, IsZmodUnit p c →
    zmodOrd p c = l → ∀ k,
      zmodPow (p ^ 1) (zmodPow (p ^ 1) c k) l
        = Quot.mk (modCong (p ^ 1)).rel 1
  /-- 完全性: x^l = 1 の任意の解は c の冪。 -/
  complete : ∀ c : (zmod (p ^ 1)).carrier, IsZmodUnit p c →
    zmodOrd p c = l → ∀ x : (zmod (p ^ 1)).carrier,
      zmodPow (p ^ 1) x l = Quot.mk (modCong (p ^ 1)).rel 1 →
      ∃ k, k ≤ l - 1 ∧ zmodPow (p ^ 1) c k = x
  /-- ℤ_p 側の原始 l 乗根（Teichmüller 代表）。 -/
  zp_lift : ∃ z : (Zp p).carrier, zpPow p z l = zpOne p
    ∧ (∀ i j, i < j → j < l → zpPow p z i ≠ zpPow p z j)
    ∧ ∃ a : Int, ¬ ((p : Nat) : Int) ∣ a ∧ z = teich p hp a

/-- **M121F-5b: witness** — 全フィールドが既証明の純レコード。 -/
def muLSubgroupData (p l : Nat) (hp : IsPrime p) (hl : 1 ≤ l)
    (hdvd : l ∣ p - 1) : MuLSubgroupData p l hp hl hdvd where
  order_l := order_l_exists p l hp hl hdvd
  root := fun c hc ha => mu_l_root p l hp hc ha
  powers_distinct := fun c hc ha => mu_l_powers_distinct p l hp hc ha
  pow_root := fun c hc ha k => mu_l_pow_root p l hp hc ha k
  complete := fun c hc ha x hx => mu_l_complete p l hp hl hc ha hx
  zp_lift := mu_l_zp_exists p l hp hl hdvd

/-- **定理 (M121F-5c): μ_l 部分群データの存在**。 -/
theorem muLSubgroup_exists (p l : Nat) (hp : IsPrime p) (hl : 1 ≤ l)
    (hdvd : l ∣ p - 1) : Nonempty (MuLSubgroupData p l hp hl hdvd) :=
  ⟨muLSubgroupData p l hp hl hdvd⟩

end IUT
