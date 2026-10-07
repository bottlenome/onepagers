/-
  IUT/FlStarCount.lean — M111F（F_l^* の台の完全同定 |F_l^*| = l⋇）

  IUT/FlStar.lean（M109F）は乗法的対称性 F_l^* = F_l^×/{±1} を商群
  `flStar l hl`（= `quotGrp (flUnits l hl) (pmCong l hl)`）として構成し、
  `flStar_rep` で「任意の類は 1 ≤ j かつ 2j ≤ l−1（つまり j ≤ l⋇）の
  標準代表を持つ」（存在）を示した。本モジュールは標準代表の
  **一意性**を加え、さらに標準代表を **Quot.lift による関数**
  `flStarRep` として実現する（選択公理なしの関数化）ことで、
  **flStar の台が {1, …, l⋇}（l⋇ = (l−1)/2）と完全に一対一対応する**
  ことを閉じる（issue #35 A-4 の磨き切り = HodgeTheater M2 の
  乗法的対称性の台の同定の完成）。

  **|F_l^*| = l⋇**: 台 {1..l⋇} との全単射が rep（`flStarRep`）/
  section（`flStarRep_section`）/ complete（`flStarRep_complete`）で
  完結する。

  * M111F-1 `prime_odd` — l 素数 ≥ 3 は奇数（l % 2 = 1。2 ∣ l なら
    素数性から 2 = 1 ∨ 2 = l でどちらも矛盾）
  * M111F-2 `flStar_rep_unique` — **標準代表の一意性**: 範囲
    1 ≤ j, 2j ≤ l−1 の代表 j, j' が同じ類を与えるなら j = j'
    （`quot_exact` → {±1} 同値の 2 分岐。折り返し分岐 j = l − j' は
    2j ≤ l−1 と 2j' ≤ l−1 から l ≤ 2j' − 1 ≤ l − 2 の矛盾）
  * M111F-3 `flStarRep` — **標準代表関数**:
    `Quot.lift (fun u => if 2·u ≤ l−1 then u else l−u)`。
    well-definedness は {±1} 同値の 2 分岐 × 折り返しの分岐を
    l の奇数性（M111F-1）で処理する
  * M111F-4 `flStarRep_range` / `flStarRep_lt` — 値域: 1 ≤ rep x かつ
    2·rep x ≤ l−1（すなわち rep x ∈ {1, …, l⋇}）、および rep x < l
  * M111F-5 `flStarRep_section` — **切断性**: 範囲内の j の類の rep は
    j 自身（lift の計算 + if_pos）
  * M111F-6 `flStarRep_complete` — **完全性（全射性）**: 任意の類は
    自分の rep を標準代表とする類に等しい（折り返し側は Quot.sound の
    {±1} 右分岐）
  * M111F-7 `flStarRep_inj` — **単射性**: rep x = rep y → x = y
    （M111F-6 から即座）
  * M111F-8 `FlStarCountData` / `flStarCountData` /
    `flStarCountData_nonempty` — 総括: 台 {1..l⋇} との全単射
    （rep / range / section_ / complete）のデータ構造と witness

  **結論**: M109F が存在レベルで示した標準代表が、一意性・関数性・
  切断性・完全性まで揃い、F_l^* の台は {1, …, l⋇} と過不足なく
  一対一対応する。HodgeTheater M2 の乗法的対称性の台の同定はこれで
  完成（|F_l^*| = l⋇）。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.FlStar

namespace IUT

/-! ## l の奇数性 -/

/-- **定理 (M111F-1): 奇素数の奇数性** — l 素数かつ 3 ≤ l なら
    `l % 2 = 1`。2 ∣ l とすると素数性 `hl.2` から 2 = 1 ∨ 2 = l と
    なり、前者は数値矛盾、後者は 3 ≤ l と矛盾する。 -/
theorem prime_odd (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l) : l % 2 = 1 := by
  cases Nat.mod_two_eq_zero_or_one l with
  | inl h =>
    cases hl.2 2 (Nat.dvd_of_mod_eq_zero h) with
    | inl h2 => omega
    | inr h2 => omega
  | inr h => exact h

/-! ## 標準代表の一意性 -/

/-- **定理 (M111F-2): 標準代表の一意性** — 1 ≤ j, 2j ≤ l−1 の範囲の
    2 つの代表 j, j' が F_l^* の同じ類を与えるなら j = j'。
    `quot_exact` で {±1} 同値 `j = j' ∨ j = negMod l j'` に落とし、
    折り返し分岐 j = l − j' は範囲条件と omega で矛盾する。 -/
theorem flStar_rep_unique (l : Nat) (hl : IsPrime l) {j j' : Nat}
    (hj1 : 1 ≤ j) (hj2 : 2 * j ≤ l - 1) (hj1' : 1 ≤ j') (hj2' : 2 * j' ≤ l - 1)
    (hjl : j < l) (hjl' : j' < l)
    (h : Quot.mk (pmCong l hl).rel ⟨j, hj1, hjl⟩
        = Quot.mk (pmCong l hl).rel ⟨j', hj1', hjl'⟩) :
    j = j' := by
  have hrel := quot_exact (flUnits l hl) (pmCong l hl) h
  cases hrel with
  | inl heq => exact heq
  | inr heq =>
    have heq' : j = negMod l j' := heq
    have hne : negMod l j' = l - j' := by
      show (if j' = 0 then 0 else l - j') = l - j'
      rw [if_neg (show ¬ j' = 0 by omega)]
    rw [hne] at heq'
    omega

/-! ## 標準代表関数（Quot.lift による関数化） -/

/-- **定理 (M111F-3): 標準代表関数** — F_l^* の各類にその標準代表
    j ∈ {1, …, l⋇} を返す関数。∃ 形の `flStar_rep` を選択公理で
    関数化するのではなく、`Quot.lift` により
    `fun u => if 2u ≤ l−1 then u else l−u` を直接持ち上げる。
    well-definedness は {±1} 同値（`u = u' ∨ u = negMod l u'`）と
    折り返し分岐の組合せを l の奇数性（M111F-1）と omega で処理する。 -/
def flStarRep (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l)
    (x : (flStar l hl).carrier) : Nat :=
  Quot.lift
    (fun (u : (flUnits l hl).carrier) =>
      if 2 * u.val ≤ l - 1 then u.val else l - u.val)
    (fun u u' huu' => by
      show (if 2 * u.val ≤ l - 1 then u.val else l - u.val)
          = (if 2 * u'.val ≤ l - 1 then u'.val else l - u'.val)
      have hl2 : l % 2 = 1 := prime_odd l hl hodd
      have hu2 : u.val < l := u.property.2
      have hu1' : 1 ≤ u'.val := u'.property.1
      have hu2' : u'.val < l := u'.property.2
      cases huu' with
      | inl h => rw [h]
      | inr h =>
        have h' : u.val = negMod l u'.val := h
        have hne : negMod l u'.val = l - u'.val := by
          show (if u'.val = 0 then 0 else l - u'.val) = l - u'.val
          rw [if_neg (show ¬ u'.val = 0 by omega)]
        rw [hne] at h'
        cases Nat.lt_or_ge (l - 1) (2 * u'.val) with
        | inl hbig =>
          rw [if_pos (show 2 * u.val ≤ l - 1 by omega),
              if_neg (show ¬ 2 * u'.val ≤ l - 1 by omega)]
          exact h'
        | inr hsmall =>
          rw [if_neg (show ¬ 2 * u.val ≤ l - 1 by omega),
              if_pos (show 2 * u'.val ≤ l - 1 by omega)]
          omega) x

/-- **定理 (M111F-4a): 値域** — 標準代表は 1 ≤ rep x かつ
    2·rep x ≤ l−1、すなわち rep x ∈ {1, …, l⋇}（l⋇ = (l−1)/2）。
    折り返し側では l の奇数性から 2u ≥ l+1 が効く。 -/
theorem flStarRep_range (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l)
    (x : (flStar l hl).carrier) :
    1 ≤ flStarRep l hl hodd x ∧ 2 * flStarRep l hl hodd x ≤ l - 1 := by
  induction x using Quot.ind with
  | mk u =>
    have hl2 : l % 2 = 1 := prime_odd l hl hodd
    have hu1 : 1 ≤ u.val := u.property.1
    have hu2 : u.val < l := u.property.2
    show 1 ≤ (if 2 * u.val ≤ l - 1 then u.val else l - u.val)
        ∧ 2 * (if 2 * u.val ≤ l - 1 then u.val else l - u.val) ≤ l - 1
    cases Nat.lt_or_ge (l - 1) (2 * u.val) with
    | inl hbig =>
      rw [if_neg (show ¬ 2 * u.val ≤ l - 1 by omega)]
      exact ⟨by omega, by omega⟩
    | inr hsmall =>
      rw [if_pos (show 2 * u.val ≤ l - 1 by omega)]
      exact ⟨hu1, hsmall⟩

/-- **定理 (M111F-4b): 台の範囲内性** — 標準代表は l 未満
    （F_l^× の台の subtype 条件への供給用 bookkeeping）。 -/
theorem flStarRep_lt (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l)
    (x : (flStar l hl).carrier) : flStarRep l hl hodd x < l := by
  have h := flStarRep_range l hl hodd x
  omega

/-- **定理 (M111F-5): 切断性** — 範囲内（1 ≤ j, 2j ≤ l−1）の j の
    類の標準代表は j 自身。`Quot.lift` の計算規則と `if_pos` で
    ほぼ定義的に従う。 -/
theorem flStarRep_section (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l)
    {j : Nat} (hj1 : 1 ≤ j) (hj2 : 2 * j ≤ l - 1) (hjl : j < l) :
    flStarRep l hl hodd (Quot.mk (pmCong l hl).rel ⟨j, hj1, hjl⟩) = j := by
  show (if 2 * j ≤ l - 1 then j else l - j) = j
  rw [if_pos hj2]

/-- **定理 (M111F-6): 完全性（全射性）** — F_l^* の任意の類は自分の
    標準代表 rep x を代表とする類に等しい。代表 u が範囲内なら
    そのまま（{±1} 左分岐）、範囲外なら l − u への折り返しが
    `negMod` による {±1} 右分岐（`Quot.sound`）になる。 -/
theorem flStarRep_complete (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l)
    (x : (flStar l hl).carrier) :
    x = Quot.mk (pmCong l hl).rel
      ⟨flStarRep l hl hodd x, (flStarRep_range l hl hodd x).1,
        flStarRep_lt l hl hodd x⟩ := by
  induction x using Quot.ind with
  | mk u =>
    have hu1 : 1 ≤ u.val := u.property.1
    have hu2 : u.val < l := u.property.2
    refine Quot.sound ?_
    show u.val = (if 2 * u.val ≤ l - 1 then u.val else l - u.val)
        ∨ u.val = negMod l (if 2 * u.val ≤ l - 1 then u.val else l - u.val)
    cases Nat.lt_or_ge (l - 1) (2 * u.val) with
    | inl hbig =>
      refine Or.inr ?_
      rw [if_neg (show ¬ 2 * u.val ≤ l - 1 by omega)]
      show u.val = (if l - u.val = 0 then 0 else l - (l - u.val))
      rw [if_neg (show ¬ l - u.val = 0 by omega)]
      omega
    | inr hsmall =>
      refine Or.inl ?_
      rw [if_pos (show 2 * u.val ≤ l - 1 by omega)]

/-- **定理 (M111F-7): 単射性** — 標準代表が一致する 2 つの類は等しい。
    完全性（M111F-6）で両者を標準代表の類に書き換え、`Quot.sound` の
    {±1} 左分岐で閉じる。 -/
theorem flStarRep_inj (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l)
    (x y : (flStar l hl).carrier)
    (h : flStarRep l hl hodd x = flStarRep l hl hodd y) : x = y := by
  rw [flStarRep_complete l hl hodd x, flStarRep_complete l hl hodd y]
  exact Quot.sound (Or.inl h)

/-! ## 総括データ -/

/-- **定理 (M111F-8a): F_l^* の台の完全同定データ** —
    **|F_l^*| = l⋇**: 台 {1..l⋇} との全単射が rep / section_ /
    complete で完結（M2 HodgeTheater の乗法的対称性の台の同定の完成）。
    `rep` は各類の標準代表、`range` はその値域が {1, …, l⋇} に
    収まること、`section_` は範囲内の j から作った類の rep が j に
    戻ること（単射側）、`complete` は任意の類が自分の rep の類である
    こと（全射側）。 -/
structure FlStarCountData (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l) where
  rep : (flStar l hl).carrier → Nat
  range : ∀ x, 1 ≤ rep x ∧ 2 * rep x ≤ l - 1
  section_ : ∀ {j : Nat} (hj1 : 1 ≤ j) (_ : 2 * j ≤ l - 1) (hjl : j < l),
    rep (Quot.mk (pmCong l hl).rel ⟨j, hj1, hjl⟩) = j
  complete : ∀ x, ∃ (h1 : 1 ≤ rep x) (h2 : rep x < l),
    x = Quot.mk (pmCong l hl).rel ⟨rep x, h1, h2⟩

/-- **定理 (M111F-8b): 総括データの具体的 witness** — `flStarRep` と
    M111F-4/5/6 による `FlStarCountData` の実例。 -/
def flStarCountData (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l) :
    FlStarCountData l hl hodd where
  rep := flStarRep l hl hodd
  range := flStarRep_range l hl hodd
  section_ := fun hj1 hj2 hjl => flStarRep_section l hl hodd hj1 hj2 hjl
  complete := fun x => ⟨(flStarRep_range l hl hodd x).1, flStarRep_lt l hl hodd x,
    flStarRep_complete l hl hodd x⟩

/-- **定理 (M111F-8c): `FlStarCountData` の非空性** — witness の直接
    構成による存在証明（選択公理不使用）。 -/
theorem flStarCountData_nonempty (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l) :
    Nonempty (FlStarCountData l hl hodd) :=
  ⟨flStarCountData l hl hodd⟩

end IUT
