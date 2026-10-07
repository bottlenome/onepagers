/-
  IUT/FlStar.lean — M109F（乗法的対称性 F_l^* = F_l^×/{±1} の商群構成）

  IUT/HodgeTheater.lean（M2）は乗法的対称性 F_l^* = F_l^×/{±1}
  （ΘNF-Hodge theater 側）の台集合が {1, …, l⋇} であることの整合性
  のみを確認し、群構造そのもの（{±1} 商群としての実体）は
  未形式化として正直申告していた（issue #35 A-4 の残り）。
  IUT/FlUnits.lean（M108F）は F_l^×（l 素数）の乗法群構造を
  mathlib なしの純 Nat 算術で完全構成した。本モジュールは、その上に
  {±1}（`negMod`）による合同関係 `GrpCong` を構成し、IUT/Profinite.lean
  （M13）の一般的な商群構成 `quotGrp` を適用して **F_l^* を実際の
  商群として構成する**。これにより issue #35 A-4 は商群レベルで
  完全に解消される。

  * M109F-1 `negMod_mulMod_left` / `negMod_mulMod_right` — **±1 倍と
    乗法の両立**（Nat 簿記）: `(−a)·b = −(a·b)`、`a·(−b) = −(a·b)`
    （mod l）。Bézout 同様の div/mod 分解（`Nat.div_add_mod`）と
    Nat の切り捨て減算の分配則（`Nat.sub_mul`/`Nat.mul_add`）だけで
    純代数的に証明する（乗法項は `generalize` せず、`have` による
    等式の連鎖として omega に渡し、omega は各乗法項を不透明な
    原子として線形算術で処理する）
  * M109F-2 `negMod_range` — 範囲内の元の ±1 倍も範囲内（bookkeeping）
  * M109F-3 `pmCong` — **合同関係 `GrpCong (flUnits l hl)`**:
    `rel x y := x.val = y.val ∨ x.val = negMod l y.val`。反射律・
    対称律（`negMod_invol`）・推移律（4 分岐）・積との両立
    `mul_compat`（4 分岐、M109F-1 に帰着）を全て証明する
  * M109F-4 `flStar` / `flStar_comm` — **商群 F_l^* = F_l^×/{±1}**
    （`quotGrp` の適用）とその可換性
  * M109F-5 `flStar_rep` — **標準代表元の存在**: F_l^* の任意の元は
    ある `1 ≤ j`、`2j ≤ l−1`（つまり `j ≤ l⋇`）を満たす
    `⟨j, …⟩ : F_l^×` の像として書ける（l 素数 ≥ 3 → l 奇数、
    範囲外なら `l − j` に折り返す）
  * M109F-6 `flStar_rep_bound` — HodgeTheater への接続サニティ:
    代表は非零かつ `j ≤ (l−1)/2` — これが HodgeTheater M2 の
    乗法的対称性の台 `{1, …, l⋇}` と一致する範囲であり、
    商群 `flStar` の標準代表として実現されたことを示す
  * M109F-7 `FlStarData` / `flStarData` / `flStarData_nonempty` —
    総括データ構造（商群・可換性・標準代表の存在をまとめたもの）と
    その witness による存在証明

  **結論**: HodgeTheater M2 が骨格（台集合 {1,…,l⋇} のみ）として
  扱っていた乗法的対称性 F_l^* が、ここで F_l^×/{±1} という
  **実際の商群**として構成され、その標準代表が HodgeTheater 側の
  ラベル範囲と一致することが証明された。issue #35 A-4
  「素数性を使う F_l^* の群構造」はこれで完全に解消。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.FlUnits

namespace IUT

/-! ## ±1 倍と乗法の両立 -/

/-- **定理 (M109F-1a): ±1 倍の左乗法両立** — l 素数、1 ≤ a, b < l
    なら `(−a)·b ≡ −(a·b) (mod l)`。`negMod l a = l − a` に開き、
    `a*b` を `l*(a*b/l) + a*b%l` に分解（`Nat.div_add_mod`）して
    `l*b` をその分解に合わせて書き換え（`Nat.mul_add`）、最後に
    `Nat.mul_add_mod_of_lt` で mod を計算する。全ての乗法項は
    `have` の等式として扱い、omega には線形結合の整合性のみを
    委ねる（omega は非線形項を不透明な原子として扱う）。 -/
theorem negMod_mulMod_left (l : Nat) (hl : IsPrime l) {a b : Nat}
    (ha1 : 1 ≤ a) (ha : a < l) (hb1 : 1 ≤ b) (hb : b < l) :
    mulMod l (negMod l a) b = negMod l (mulMod l a b) := by
  have hlpos : 0 < l := by have := hl.1; omega
  have hna : negMod l a = l - a := by
    unfold negMod
    rw [if_neg (show a ≠ 0 by omega)]
  have hk1 : 1 ≤ a * b % l := mulMod_ne_zero l hl ha1 ha hb1 hb
  have hnk : negMod l (a * b % l) = l - a * b % l := by
    unfold negMod
    rw [if_neg (show a * b % l ≠ 0 by omega)]
  show mulMod l (negMod l a) b = negMod l (a * b % l)
  rw [hna, hnk]
  show ((l - a) * b) % l = l - a * b % l
  rw [Nat.sub_mul]
  -- 目標: (l * b - a * b) % l = l - a * b % l
  have hdm : l * (a * b / l) + a * b % l = a * b := Nat.div_add_mod (a * b) l
  have hab_lt : a * b < l * b := Nat.mul_lt_mul_of_pos_right ha (show 0 < b by omega)
  have hq_lt : l * (a * b / l) < l * b := by omega
  have hqb : a * b / l < b := by
    cases Nat.lt_or_ge (a * b / l) b with
    | inl h => exact h
    | inr h =>
      exfalso
      have hcontra : l * b ≤ l * (a * b / l) := Nat.mul_le_mul_left l h
      omega
  have hd : (b - a * b / l - 1) + a * b / l + 1 = b := by omega
  have step0 : l * ((b - a * b / l - 1) + a * b / l + 1) = l * b := congrArg (l * ·) hd
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at step0
  -- step0 : l * (b - a*b/l - 1) + l * (a*b/l) + l = l * b
  have hmlt : a * b % l < l := Nat.mod_lt (a * b) hlpos
  have hsub : l * b - a * b = l * (b - a * b / l - 1) + (l - a * b % l) := by omega
  rw [hsub, Nat.mul_comm l (b - a * b / l - 1)]
  exact Nat.mul_add_mod_of_lt (show l - a * b % l < l by omega)

/-- **定理 (M109F-1b): ±1 倍の右乗法両立** — `a·(−b) ≡ −(a·b) (mod l)`。
    `mulMod_comm` で `negMod_mulMod_left` に帰着する。 -/
theorem negMod_mulMod_right (l : Nat) (hl : IsPrime l) {a b : Nat}
    (ha1 : 1 ≤ a) (ha : a < l) (hb1 : 1 ≤ b) (hb : b < l) :
    mulMod l a (negMod l b) = negMod l (mulMod l a b) := by
  rw [mulMod_comm l a (negMod l b)]
  rw [negMod_mulMod_left l hl hb1 hb ha1 ha]
  rw [mulMod_comm l b a]

/-- **定理 (M109F-2): 範囲の保存** — 1 ≤ x < l なら negMod l x も
    同じ範囲に収まる（{±1} 作用の閉性）。 -/
theorem negMod_range (l x : Nat) (hx1 : 1 ≤ x) (hx : x < l) :
    1 ≤ negMod l x ∧ negMod l x < l := by
  have hxne : x ≠ 0 := by omega
  have he : negMod l x = l - x := by
    unfold negMod
    rw [if_neg hxne]
  rw [he]
  exact ⟨by omega, by omega⟩

/-! ## 合同関係 {±1} -/

/-- **定理 (M109F-3): 合同関係 `{±1}`** — `F_l^×` 上の同値関係
    `x ~ y ↔ x = y ∨ x = −y`。積との両立（M109F-1）から
    `GrpCong (flUnits l hl)` を構成する。 -/
def pmCong (l : Nat) (hl : IsPrime l) : GrpCong (flUnits l hl) where
  rel := fun x y => x.val = y.val ∨ x.val = negMod l y.val
  refl := fun a => Or.inl rfl
  symm := by
    intro a b h
    cases h with
    | inl h => exact Or.inl h.symm
    | inr h =>
      have hb : b.val < l := b.property.2
      have heq : negMod l a.val = b.val := by
        rw [h]
        exact negMod_invol hb
      exact Or.inr heq.symm
  trans := by
    intro a b c h1 h2
    cases h1 with
    | inl h1 =>
      cases h2 with
      | inl h2 => exact Or.inl (h1.trans h2)
      | inr h2 => exact Or.inr (by rw [h1, h2])
    | inr h1 =>
      cases h2 with
      | inl h2 => exact Or.inr (by rw [h1, h2])
      | inr h2 =>
        have hc : c.val < l := c.property.2
        have heq : a.val = negMod l (negMod l c.val) := by rw [h1, h2]
        rw [negMod_invol hc] at heq
        exact Or.inl heq
  mul_compat := by
    intro a b a' b' h1 h2
    show mulMod l a.val b.val = mulMod l a'.val b'.val
      ∨ mulMod l a.val b.val = negMod l (mulMod l a'.val b'.val)
    cases h1 with
    | inl h1 =>
      cases h2 with
      | inl h2 => exact Or.inl (by rw [h1, h2])
      | inr h2 =>
        apply Or.inr
        rw [h1, h2]
        exact negMod_mulMod_right l hl a'.property.1 a'.property.2 b'.property.1 b'.property.2
    | inr h1 =>
      cases h2 with
      | inl h2 =>
        apply Or.inr
        rw [h1, h2]
        exact negMod_mulMod_left l hl a'.property.1 a'.property.2 b'.property.1 b'.property.2
      | inr h2 =>
        have hnb' := negMod_range l b'.val b'.property.1 b'.property.2
        apply Or.inl
        rw [h1, h2]
        rw [negMod_mulMod_left l hl a'.property.1 a'.property.2 hnb'.1 hnb'.2]
        rw [negMod_mulMod_right l hl a'.property.1 a'.property.2 b'.property.1 b'.property.2]
        exact negMod_invol (mulMod_lt (show 0 < l by have := hl.1; omega) a'.val b'.val)

/-! ## 商群 F_l^* -/

/-- **定理 (M109F-4a): 乗法的対称性 F_l^* = F_l^×/{±1}** — `quotGrp`
    による商群としての実構成。issue #35 A-4「素数性を使う F_l^* の
    群構造」の完全解消。 -/
def flStar (l : Nat) (hl : IsPrime l) : Grp := quotGrp (flUnits l hl) (pmCong l hl)

/-- **定理 (M109F-4b): F_l^* はアーベル群** — `flUnits_comm` から
    商群でも可換性が保たれる。 -/
theorem flStar_comm (l : Nat) (hl : IsPrime l) :
    ∀ x y : (flStar l hl).carrier, (flStar l hl).mul x y = (flStar l hl).mul y x := by
  intro x y
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  show Quot.mk (pmCong l hl).rel ((flUnits l hl).mul a b)
      = Quot.mk (pmCong l hl).rel ((flUnits l hl).mul b a)
  rw [flUnits_comm l hl a b]

/-! ## 標準代表元 -/

/-- **定理 (M109F-5): 標準代表元の存在** — l 素数 ≥ 3 のとき、
    F_l^* の任意の元は `1 ≤ j` かつ `2j ≤ l−1`（すなわち `j ≤ l⋇`）
    を満たす `F_l^×` の元 `⟨j, …⟩` の像として書ける。l が奇数
    （素数 ≥ 3 なので 2 ∤ l）であることを使い、範囲外なら
    `l − j` に折り返す（`negMod` による {±1} 同値）。 -/
theorem flStar_rep (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l) :
    ∀ x : (flStar l hl).carrier, ∃ j : Nat, 1 ≤ j ∧ 2 * j ≤ l - 1 ∧
      ∃ (h1 : 1 ≤ j) (h2 : j < l), x = Quot.mk (pmCong l hl).rel ⟨j, h1, h2⟩ := by
  intro x
  induction x using Quot.ind
  rename_i a
  obtain ⟨av, ha1, ha2⟩ := a
  have hl2 : l % 2 = 1 := by
    cases Nat.mod_two_eq_zero_or_one l with
    | inl h =>
      exfalso
      have hdvd : 2 ∣ l := Nat.dvd_of_mod_eq_zero h
      cases hl.2 2 hdvd with
      | inl h2 => omega
      | inr h2 => omega
    | inr h => exact h
  cases Nat.lt_or_ge (l - 1) (2 * av) with
  | inr hcaseA =>
    -- 2 * av ≤ l - 1: そのまま j := av
    exact ⟨av, ha1, hcaseA, ha1, ha2, rfl⟩
  | inl hcaseB =>
    -- l - 1 < 2 * av: j := l - av に折り返す
    refine ⟨l - av, by omega, by omega, by omega, by omega, ?_⟩
    have hcompute : negMod l (l - av) = av := by
      unfold negMod
      rw [if_neg (show l - av ≠ 0 by omega)]
      omega
    exact Quot.sound (Or.inr hcompute.symm)

/-- **定理 (M109F-6): HodgeTheater への接続サニティ** — M109F-5 の
    標準代表は非零かつ `j ≤ (l−1)/2`。これは HodgeTheater M2 の
    乗法的対称性 F_l^* の台集合 `{1, …, l⋇}`（`l⋇ = (l−1)/2`）と
    ちょうど一致する範囲であり、商群 `flStar` の標準代表として
    HodgeTheater 側のラベル構造が実現されたことを示す。 -/
theorem flStar_rep_bound (l : Nat) (hl : IsPrime l) (hodd : 3 ≤ l)
    (x : (flStar l hl).carrier) :
    ∃ j : Nat, 1 ≤ j ∧ j ≤ (l - 1) / 2 ∧
      ∃ (h1 : 1 ≤ j) (h2 : j < l), x = Quot.mk (pmCong l hl).rel ⟨j, h1, h2⟩ := by
  obtain ⟨j, hj1, hj2, h1, h2, hx⟩ := flStar_rep l hl hodd x
  exact ⟨j, hj1, by omega, h1, h2, hx⟩

/-! ## 総括データ -/

/-- **定理 (M109F-7a): F_l^* の総括データ** — 商群・可換性・標準代表
    の存在をまとめた構造体。`star` は任意の `Grp` として抽象化し
    （`rep` で標準代表の作り方を別途データとして持たせる）、
    `flStarData` で `flStar l hl` による具体的な witness を与える。 -/
structure FlStarData (l : Nat) (hl : IsPrime l) where
  star : Grp
  rep : (j : Nat) → 1 ≤ j → j < l → star.carrier
  comm : ∀ x y : star.carrier, star.mul x y = star.mul y x
  rep_exists : 3 ≤ l → ∀ x : star.carrier,
    ∃ j : Nat, 1 ≤ j ∧ 2 * j ≤ l - 1 ∧ ∃ (h1 : 1 ≤ j) (h2 : j < l), x = rep j h1 h2

/-- **定理 (M109F-7b): 総括データの具体的 witness** — `flStar l hl`
    を土台にした `FlStarData` の実例。 -/
def flStarData (l : Nat) (hl : IsPrime l) : FlStarData l hl where
  star := flStar l hl
  rep := fun j h1 h2 => Quot.mk (pmCong l hl).rel ⟨j, h1, h2⟩
  comm := flStar_comm l hl
  rep_exists := fun hodd x => flStar_rep l hl hodd x

/-- **定理 (M109F-7c): `FlStarData` の非空性** — witness の直接構成
    による存在証明（選択公理不使用）。 -/
theorem flStarData_nonempty (l : Nat) (hl : IsPrime l) : Nonempty (FlStarData l hl) :=
  ⟨flStarData l hl⟩

end IUT
