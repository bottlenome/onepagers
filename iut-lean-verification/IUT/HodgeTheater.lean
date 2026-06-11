/-
  IUT/HodgeTheater.lean — M2（Θ±ellNF-Hodge theater）の形式化

  IUT I §4–§6 で構成される Hodge theater のうち、**ラベル構造と
  二つの対称性の組合せ骨格** を形式化し、その性質を証明する。

  形式化する内容（IUT I の記法との対応）:
  * F_l = {0, 1, …, l−1}（l = 2l⋇+1 ≥ 5。素数性は環論を使わない
    本骨格では不要なので奇数性のみ仮定し、未形式化部分として明示）
  * 加法的対称性 F_l^±± = F_l ⋊ {±1}（IUT I, Θ±ell-Hodge theater 側）
    — 本ファイルの `AddSym`。**合成で閉じた（二面体的）対称性で、
    ラベル全体に推移的に作用する** ことを証明する
  * ±1 商 |F_l| = F_l/{±1} = {0, 1, …, l⋇}（IUT I, Prop 6.5 周辺）
    — 標準代表元 `orbitRep` を構成し、**商がちょうど l⋇+1 個**
    （非零部分がちょうど l⋇ 個 = テータ値 q^{j²} のラベル）に
    なることを証明する
  * 乗法的対称性 F_l^* = F_l^×/{±1}（ΘNF-Hodge theater 側）の
    台集合が同じ {1, …, l⋇} であること

  未形式化（明示的な残課題）:
  * 素数性を使う F_l^* の群構造、prime-strip の圏論的データ、
    基礎付け（étale-like / Frobenius-like 区別）

  橋渡し: `HodgeTheaterData.toSkeleton` により、ここで構成した
  ラベル数 l⋇ ≥ 2 が Skeleton.lstar（M4 のテータ値計算と
  系3.12 の議論の入力）をそのまま供給することを示す。
-/
import IUT.Skeleton

namespace IUT

/-! ## F_l 上の mod 算術（変数法を避けた omega 親和的定義） -/

/-- F_l の加法: `a + b mod l`（a, b < l を前提とする定義）。 -/
def addMod (l a b : Nat) : Nat := if a + b < l then a + b else a + b - l

/-- F_l の −1 倍: `j ↦ −j mod l`。 -/
def negMod (l j : Nat) : Nat := if j = 0 then 0 else l - j

theorem addMod_lt {l a b : Nat} (ha : a < l) (hb : b < l) : addMod l a b < l := by
  unfold addMod; split <;> omega

theorem negMod_lt {l j : Nat} (hl : 0 < l) (hj : j < l) : negMod l j < l := by
  unfold negMod; split <;> omega

/-- −(−j) = j（{±1} 作用の対合性）。 -/
theorem negMod_invol {l j : Nat} (hj : j < l) : negMod l (negMod l j) = j := by
  unfold negMod; split <;> split <;> omega

/-- −1 倍は加法の準同型: −(a+b) = (−a) + (−b) mod l。 -/
theorem negMod_addMod {l a b : Nat} (ha : a < l) (hb : b < l) :
    negMod l (addMod l a b) = addMod l (negMod l a) (negMod l b) := by
  unfold addMod negMod
  repeat' split
  all_goals omega

/-- 加法の結合則 mod l。 -/
theorem addMod_assoc {l a b c : Nat} (ha : a < l) (hb : b < l) (hc : c < l) :
    addMod l (addMod l a b) c = addMod l a (addMod l b c) := by
  unfold addMod
  repeat' split
  all_goals omega

/-! ## 加法的対称性 F_l^±± = F_l ⋊ {±1}（IUT I の ±-対称性） -/

/-- F_l^±± の元: x ↦ shift ± x。`flip = true` が −1 成分。 -/
structure AddSym (l : Nat) where
  flip : Bool
  shift : Nat
  hshift : shift < l

/-- 作用: x ↦ shift + (±x) mod l。 -/
def AddSym.act {l : Nat} (s : AddSym l) (j : Nat) : Nat :=
  addMod l s.shift (if s.flip then negMod l j else j)

theorem AddSym.act_lt {l : Nat} (s : AddSym l) {j : Nat} (hl : 0 < l) (hj : j < l) :
    s.act j < l := by
  unfold AddSym.act
  refine addMod_lt s.hshift ?_
  split
  · exact negMod_lt hl hj
  · exact hj

/-- 合成: (s ∘ t)(x) = s.shift ± (t.shift ± x)
    = (s.shift ± t.shift) + (±±x)。flip は XOR、shift は捻り付き加法。 -/
def AddSym.comp {l : Nat} (hl : 0 < l) (s t : AddSym l) : AddSym l where
  flip := Bool.xor s.flip t.flip
  shift := addMod l s.shift (if s.flip then negMod l t.shift else t.shift)
  hshift := addMod_lt s.hshift (by
    split
    · exact negMod_lt hl t.hshift
    · exact t.hshift)

/-- **定理 (M2-1): F_l^±± は合成で閉じている**（二面体群の演算則）。
    すなわち対称性 s, t の逐次適用は単一の対称性 `s.comp t` に等しい。
    これが「Hodge theater の加法的対称性は群をなす」の組合せ核。 -/
theorem AddSym.act_comp {l : Nat} (hl : 0 < l) (s t : AddSym l) {x : Nat} (hx : x < l) :
    s.act (t.act x) = (s.comp hl t).act x := by
  obtain ⟨sf, sa, hsa⟩ := s
  obtain ⟨tf, ta, hta⟩ := t
  have hnx := negMod_lt hl hx
  have hnta := negMod_lt hl hta
  cases sf <;> cases tf
  -- s.flip = false, t.flip = false: 純平行移動の合成 = 結合則
  · show addMod l sa (addMod l ta x) = addMod l (addMod l sa ta) x
    exact (addMod_assoc hsa hta hx).symm
  -- s.flip = false, t.flip = true
  · show addMod l sa (addMod l ta (negMod l x))
       = addMod l (addMod l sa ta) (negMod l x)
    exact (addMod_assoc hsa hta hnx).symm
  -- s.flip = true, t.flip = false: −(t.shift + x) = −t.shift + −x
  · show addMod l sa (negMod l (addMod l ta x))
       = addMod l (addMod l sa (negMod l ta)) (negMod l x)
    rw [negMod_addMod hta hx]
    exact (addMod_assoc hsa hnta hnx).symm
  -- s.flip = true, t.flip = true: −(t.shift + −x) = −t.shift + x
  · show addMod l sa (negMod l (addMod l ta (negMod l x)))
       = addMod l (addMod l sa (negMod l ta)) x
    rw [negMod_addMod hta hnx, negMod_invol hx]
    exact (addMod_assoc hsa hnta hx).symm

/-- **定理 (M2-2): 加法的対称性はラベル全体に推移的に作用する**。
    任意のラベル j を任意のラベル k に移す平行移動が存在する。
    IUT I でラベルの「同期」(synchronization) を担う性質の組合せ核。 -/
theorem addSym_transitive {l : Nat} (hl : 0 < l) {j k : Nat} (hj : j < l) (hk : k < l) :
    ∃ s : AddSym l, s.flip = false ∧ s.act j = k := by
  have hsh : (if k ≥ j then k - j else k + l - j) < l := by split <;> omega
  refine ⟨⟨false, _, hsh⟩, rfl, ?_⟩
  show addMod l (if k ≥ j then k - j else k + l - j) j = k
  unfold addMod
  repeat' split
  all_goals omega

/-- 恒等対称性。 -/
def AddSym.one (l : Nat) (hl : 0 < l) : AddSym l := ⟨false, 0, hl⟩

/-- **定理 (M2-9): 単位元** — 恒等対称性は何も動かさない。 -/
theorem AddSym.one_act {l : Nat} (hl : 0 < l) {x : Nat} (hx : x < l) :
    (AddSym.one l hl).act x = x := by
  show addMod l 0 x = x
  unfold addMod
  split <;> omega

/-- **定理 (M2-10): 逆元の存在** — 各対称性は可逆。M2-1（閉性）・
    M2-9（単位元）と合わせて **F_l^±± が群をなす** ことの組合せ的
    内容が完結する（平行移動の逆は逆向き平行移動、反転付き対称性は
    自己逆＝二面体群の標準的構造）。 -/
theorem addSym_inverse {l : Nat} (hl : 0 < l) (s : AddSym l) :
    ∃ t : AddSym l, ∀ x, x < l → t.act (s.act x) = x := by
  obtain ⟨sf, sa, hsa⟩ := s
  cases sf
  · -- 平行移動 x ↦ sa + x の逆は x ↦ (−sa) + x
    refine ⟨⟨false, negMod l sa, negMod_lt hl hsa⟩, ?_⟩
    intro x hx
    show addMod l (negMod l sa) (addMod l sa x) = x
    unfold addMod negMod
    repeat' split
    all_goals omega
  · -- 反転付き x ↦ sa − x は自己逆
    refine ⟨⟨true, sa, hsa⟩, ?_⟩
    intro x hx
    show addMod l sa (negMod l (addMod l sa (negMod l x))) = x
    unfold addMod negMod
    repeat' split
    all_goals omega

/-! ## ±1 商: |F_l| = {0, …, l⋇} とテータ値ラベル {1, …, l⋇} -/

/-- {±1} 軌道の標準代表元: min(j, l−j) ∈ {0, …, l⋇}。 -/
def orbitRep (l j : Nat) : Nat := min j (l - j)

/-- **定理 (M2-3): 代表元は {0, …, l⋇} に収まる**（l = 2l⋇+1）。 -/
theorem orbitRep_le {l L j : Nat} (hodd : l = 2 * L + 1) (hj : j < l) :
    orbitRep l j ≤ L := by
  unfold orbitRep; omega

/-- **定理 (M2-4): 代表元は ±1 作用で不変**（well-defined 性）。 -/
theorem orbitRep_negMod {l j : Nat} (hl : 0 < l) (hj : j < l) :
    orbitRep l (negMod l j) = orbitRep l j := by
  unfold orbitRep negMod; split <;> omega

/-- **定理 (M2-5): {0, …, l⋇} の元は自分自身が代表元**（切断の存在）。
    M2-3 と合わせて、商 |F_l| がちょうど l⋇+1 個のラベルを持つ。 -/
theorem orbitRep_fixes {l L k : Nat} (hodd : l = 2 * L + 1) (hk : k ≤ L) :
    orbitRep l k = k := by
  unfold orbitRep; omega

/-- **定理 (M2-6): 軌道の分離** — 代表元が一致するのは
    同一ラベルか ±1 で移り合うラベルに限る。
    これで商集合の同定（l⋇+1 個、重複なし）が完結する。 -/
theorem orbitRep_eq_iff {l L j j' : Nat} (hodd : l = 2 * L + 1)
    (hj : j < l) (hj' : j' < l) :
    orbitRep l j = orbitRep l j' ↔ (j' = j ∨ j' = negMod l j) := by
  unfold orbitRep negMod
  constructor
  · intro h; split <;> omega
  · intro h
    rcases h with h | h
    · subst h; rfl
    · subst h; split <;> omega

/-- **定理 (M2-7): 非零軌道 = テータ値ラベル**。
    j ≠ 0 の代表元はちょうど {1, …, l⋇} を動く。
    これが Θ-パイロット対象のテータ値 q^{1²}, …, q^{l⋇²} の
    ラベル集合（個数 l⋇ = Skeleton.lstar）である。
    （乗法的対称性 F_l^* = F_l^×/{±1} の台集合も同じ {1, …, l⋇}。） -/
theorem theta_labels {l L : Nat} (hodd : l = 2 * L + 1) :
    (∀ j, j < l → j ≠ 0 → 1 ≤ orbitRep l j ∧ orbitRep l j ≤ L) ∧
    (∀ k, 1 ≤ k → k ≤ L → ∃ j, j < l ∧ j ≠ 0 ∧ orbitRep l j = k) := by
  constructor
  · intro j hj hj0
    unfold orbitRep; omega
  · intro k hk1 hkL
    exact ⟨k, by omega, by omega, orbitRep_fixes hodd hkL⟩

/-- **定理 (M2-11): 商 |F_l| の完全な代表系** — l = 2l⋇+1 のとき、
    {0, …, l⋇} の各 k はそれ自身が軌道代表元（orbitRep l k = k）で
    あり、逆に任意のラベル j < l の代表元は {0, …, l⋇} に収まる。
    M2-6（軌道の分離）と合わせて、商 |F_l| = F_l/{±1} が
    ちょうど {0, …, l⋇}（l⋇+1 個）と全単射的に同定される。 -/
theorem quotient_rep_bij {l L : Nat} (hodd : l = 2 * L + 1) :
    (∀ k, k ≤ L → orbitRep l k = k) ∧ (∀ j, j < l → orbitRep l j ≤ L) :=
  ⟨fun k hk => orbitRep_fixes hodd hk, fun j hj => orbitRep_le hodd hj⟩

/-! ## Hodge theater 骨格と Skeleton への橋渡し -/

/-- **Hodge theater の組合せ骨格**: IUT の走行仮定
    「l は 5 以上の素数」のうちラベル構造に効く部分
    （l = 2l⋇+1 ≥ 5）。素数性そのものは未形式化として残す。 -/
structure HodgeTheaterData where
  /-- 素数 l（≥ 5）。 -/
  l : Nat
  /-- l⋇ = (l−1)/2。 -/
  L : Nat
  /-- l は奇数: l = 2l⋇ + 1。 -/
  hodd : l = 2 * L + 1
  /-- l ≥ 5。 -/
  hl5 : l ≥ 5

/-- l ≥ 5 から l⋇ ≥ 2 が従う（系3.12 の議論が要求する条件）。 -/
theorem HodgeTheaterData.L_ge_two (h : HodgeTheaterData) : h.L ≥ 2 := by
  have := h.hodd; have := h.hl5; omega

/-- **橋渡し定理 (M2-8)**: Hodge theater のラベル構造は
    系3.12 の形式骨格 `Skeleton` の入力（lstar = l⋇ ≥ 2）を
    そのまま供給する。M2 → M3/M4 → M6 という依存の形式化。 -/
def HodgeTheaterData.toSkeleton (h : HodgeTheaterData)
    (logq logTheta : Int) (hq : logq > 0) : Skeleton where
  lstar := h.L
  hl := h.L_ge_two
  logq := logq
  hq := hq
  logTheta := logTheta

/-- 検算: l = 5 のとき l⋇ = 2、テータ値ラベルは {1, 2}。 -/
example : orbitRep 5 3 = 2 := rfl
example : orbitRep 5 4 = 1 := rfl

/-- 検算: l = 7 のとき l⋇ = 3。 -/
example : (HodgeTheaterData.mk 7 3 rfl (by omega)).L = 3 := rfl

end IUT
