/-
  IUT/FlUnits.lean — M108F（素数性を使う F_l^× の群構造）

  IUT/HodgeTheater.lean（M2）は F_l = {0, …, l−1} を Nat の mod 算術
  （addMod/negMod）で骨格化し、「素数性を使う F_l^* の群構造」を
  未形式化として正直申告している（issue #35 A-4）。本モジュールは
  **F_l^× = {1, …, l−1} が乗法で群をなす**（l 素数）ことを、
  mathlib なし・Bézout（M32-3）・Euclid の補題（M32-4b）のみを使い
  純 Nat 算術で完全証明する。

  * M108F-1 `mulMod` — F_l 上の乗法（`(a*b) % l`）と結合則・可換則・
    左単位律（Nat.mul_mod の対称使い、omega 親和的）
  * M108F-2 `mulMod_ne_zero` — **非零性の閉性**: 1 ≤ a, b < l かつ
    l 素数なら 1 ≤ mulMod l a b（Euclid の補題の対偶）
  * M108F-3 `bezout_inv_bookkeeping` / `flInv_exists` — **逆元の存在**:
    Bézout 1 = a·x + l·y（M32-3、a, l を入れ替えて呼ぶことで係数 x が
    そのまま逆元候補になる）を x % l に正規化し、
    `Int.add_mul_emod_self_left` で mod 計算を Int → Nat に落とす
    （代表元の抽出なし、選択公理不使用）
  * M108F-4 `flInvSearch` / `flInvSearch_spec` — **逆元の実構成**
    （fuel 付き有界探索、IUT/ZmodOrder.lean の `ordSearch` の雛形）。
    仕様は「範囲 [k, j] に witness j があれば、返り値は範囲内かつ
    j 以下」という形（`ordSearch_spec` と異なり、境界固定ではなく
    汎用 witness 版）
  * M108F-5 `flInv` / `flInv_spec` — 1 から l−1 を走査する具体的逆元
    関数と、その仕様（M108F-3 の存在証明の witness が探索範囲に
    収まることから、範囲の上界も l 未満に強まる）
  * M108F-6 `flUnits` — **乗法群 F_l^× : Grp**（carrier =
    {j // 1 ≤ j ∧ j < l}、閉性 = M108F-2・M108F-5、群法則は
    mulMod の結合則・単位律・M108F-5 の逆元仕様に帰着）・
    `flUnits_comm`（可換性）
  * M108F-7 `flUnits_card_labels` — HodgeTheater への接続サニティ:
    F_l^× の台集合が同じ {1, …, l−1} 上にあることの自明な整合確認

  未形式化（正直申告、次層）: F_l^* = F_l^×/{±1}（乗法的対称性、
  ΘNF-Hodge theater 側）の商群構造・prime-strip の圏論的データ。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.HodgeTheater
import IUT.NatPrimeParts
import IUT.FundamentalGroup

namespace IUT

/-! ## F_l 上の乗法（mod 算術） -/

/-- F_l の乗法: `a * b mod l`。 -/
def mulMod (l a b : Nat) : Nat := (a * b) % l

/-- mulMod は常に l 未満（l > 0 なら）。 -/
theorem mulMod_lt {l : Nat} (hl : 0 < l) (a b : Nat) : mulMod l a b < l :=
  Nat.mod_lt (a * b) hl

/-- mulMod の可換性。 -/
theorem mulMod_comm (l a b : Nat) : mulMod l a b = mulMod l b a := by
  show (a * b) % l = (b * a) % l
  rw [Nat.mul_comm]

/-- mulMod の結合則（Nat.mul_mod を両方向に使う）。 -/
theorem mulMod_assoc (l a b c : Nat) :
    mulMod l (mulMod l a b) c = mulMod l a (mulMod l b c) := by
  show (a * b % l * c) % l = (a * (b * c % l)) % l
  have h1 : (a * b % l * c) % l = (a * b * c) % l := by
    rw [Nat.mul_mod, Nat.mul_mod (a * b) c l, Nat.mod_mod]
  have h2 : (a * (b * c % l)) % l = (a * b * c) % l := by
    rw [Nat.mul_assoc, Nat.mul_mod a (b * c) l, Nat.mul_mod a (b * c % l) l, Nat.mod_mod]
  rw [h1, h2]

/-- 1 は mulMod の左単位元（範囲内の元に対して）。 -/
theorem mulMod_one_left {l a : Nat} (ha : a < l) : mulMod l 1 a = a := by
  show (1 * a) % l = a
  rw [Nat.one_mul]
  exact Nat.mod_eq_of_lt ha

/-! ## 非零性の閉性（Euclid の補題） -/

/-- **定理 (M108F-2): F_l^× の積閉性** — l 素数、1 ≤ a, b < l なら
    1 ≤ mulMod l a b（`mulMod = 0` なら l ∣ a*b、Euclid の補題から
    l ∣ a か l ∣ b、Nat.le_of_dvd で l ≤ a < l か l ≤ b < l の矛盾）。 -/
theorem mulMod_ne_zero (l : Nat) (hl : IsPrime l) {a b : Nat}
    (ha1 : 1 ≤ a) (ha : a < l) (hb1 : 1 ≤ b) (hb : b < l) :
    1 ≤ mulMod l a b := by
  cases Nat.decEq (mulMod l a b) 0 with
  | isFalse hf => omega
  | isTrue ht =>
    exfalso
    have hdvd : l ∣ a * b := Nat.dvd_of_mod_eq_zero ht
    cases euclid l hl hdvd with
    | inl h =>
      have := Nat.le_of_dvd (by omega) h
      omega
    | inr h =>
      have := Nat.le_of_dvd (by omega) h
      omega

/-! ## 逆元の存在（Bézout 経由） -/

/-- Bézout の簿記補題（Int 束縛）: `L*Q + R = X`、`1 = A*X + L*Y` なら
    `1 = A*R + L*(A*Q + Y)`。`X` を `L` で割った余り `R` に正規化しても
    `A*(・)` の mod L 値は変わらないことの計算部分。 -/
theorem bezout_inv_bookkeeping (A L X Y Q R : Int) (h1 : L * Q + R = X)
    (h2 : (1 : Int) = A * X + L * Y) :
    (1 : Int) = A * R + L * (A * Q + Y) := by
  have e1 : A * X = A * (L * Q + R) := by rw [h1]
  rw [e1, Int.mul_add] at h2
  rw [show A * (L * Q) = L * (A * Q) by
    rw [← Int.mul_assoc, Int.mul_comm A L, Int.mul_assoc]] at h2
  rw [Int.mul_add]
  generalize L * (A * Q) = m1 at h2 ⊢
  generalize A * R = m2 at h2 ⊢
  generalize L * Y = m3 at h2 ⊢
  omega

/-- **定理 (M108F-3): F_l^× の逆元の存在** — l 素数、1 ≤ a < l なら
    ある b（1 ≤ b < l）で a*b ≡ 1 (mod l)。Bézout（a, l を入れ替えて
    呼ぶことで係数 x がそのまま a の逆元候補になる）→ x を x % l に
    正規化 → `bezout_inv_bookkeeping` で mod 計算を保ったまま Nat に
    落とす。代表元の抽出なし（選択公理不使用）。 -/
theorem flInv_exists (l : Nat) (hl : IsPrime l) {a : Nat}
    (ha1 : 1 ≤ a) (ha : a < l) :
    ∃ b, 1 ≤ b ∧ b < l ∧ mulMod l a b = 1 := by
  have hnd : ¬ l ∣ a := by
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hg : Nat.gcd a l = 1 := by
    rw [Nat.gcd_comm]
    exact prime_gcd_one l hl a hnd
  obtain ⟨x, y, hxy⟩ := bezout a l
  rw [hg] at hxy
  have h1 : (1 : Int) = ((a : Nat) : Int) * x + ((l : Nat) : Int) * y := hxy
  have hdm : ((l : Nat) : Int) * (x / (l : Nat)) + x % ((l : Nat) : Int) = x :=
    Int.mul_ediv_add_emod x (l : Nat)
  have hkey := bezout_inv_bookkeeping (a : Nat) (l : Nat) x y (x / (l : Nat))
    (x % (l : Nat)) hdm h1
  have hlpos : (0 : Int) < ((l : Nat) : Int) := by have := hl.1; omega
  have hlne : ((l : Nat) : Int) ≠ 0 := by omega
  have hb0 : 0 ≤ x % ((l : Nat) : Int) := Int.emod_nonneg x hlne
  have hbl : x % ((l : Nat) : Int) < ((l : Nat) : Int) := Int.emod_lt_of_pos x hlpos
  let b : Nat := (x % ((l : Nat) : Int)).toNat
  have hbcast : ((b : Nat) : Int) = x % ((l : Nat) : Int) := Int.toNat_of_nonneg hb0
  have hblt : b < l := by
    have hcast : ((b : Nat) : Int) < ((l : Nat) : Int) := by rw [hbcast]; exact hbl
    omega
  rw [← hbcast] at hkey
  have heq : ((a : Nat) : Int) * ((b : Nat) : Int)
      = 1 + ((l : Nat) : Int) * (-(((a : Nat) : Int) * (x / (l : Nat)) + y)) := by
    rw [Int.mul_neg]
    omega
  have hmod : (((a : Nat) : Int) * ((b : Nat) : Int)) % ((l : Nat) : Int)
      = 1 % ((l : Nat) : Int) := by
    rw [heq]
    exact Int.add_mul_emod_self_left 1 (l : Nat) _
  have h1mod : (1 : Int) % ((l : Nat) : Int) = 1 :=
    Int.emod_eq_of_lt (by omega) (by have := hl.1; omega)
  rw [h1mod] at hmod
  have hcast2 : (((a * b : Nat) : Int)) % ((l : Nat) : Int) = 1 := by
    rw [Int.natCast_mul]
    exact hmod
  have hcast3 : (((a * b) % l : Nat) : Int) = (1 : Int) := by
    rw [← Int.ofNat_mod_ofNat]
    exact hcast2
  have hfin : (a * b) % l = 1 := by omega
  refine ⟨b, ?_, hblt, hfin⟩
  cases Nat.eq_zero_or_pos b with
  | inl hb0' =>
    exfalso
    rw [hb0', Nat.mul_zero, Nat.zero_mod] at hfin
    omega
  | inr hp => exact hp

/-! ## 逆元の実構成（fuel 付き有界探索） -/

/-- **M108F-4a: fuel 付き探索** — k から fuel ステップの範囲で
    `a*j ≡ 1 (mod l)` となる最初の j を返す（見つからなければ
    走り切った位置）。IUT/ZmodOrder.lean の `ordSearch` の雛形。 -/
def flInvSearch (l a : Nat) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k =>
    if mulMod l a k = 1 then k else flInvSearch l a fuel (k + 1)

/-- **定理 (M108F-4b): 探索の仕様** — 範囲 `[k, k+fuel]` の中の
    ある位置 `j` に witness（`mulMod l a j = 1`）があれば、返り値は
    範囲内かつ `j` 以下（`ordSearch_spec` と異なり境界固定ではなく
    汎用 witness 版。fuel の帰納法）。 -/
theorem flInvSearch_spec (l a : Nat) : ∀ fuel k j, k ≤ j → j ≤ k + fuel →
    mulMod l a j = 1 →
    mulMod l a (flInvSearch l a fuel k) = 1 ∧ k ≤ flInvSearch l a fuel k
      ∧ flInvSearch l a fuel k ≤ j := by
  intro fuel
  induction fuel with
  | zero =>
    intro k j hkj hjk hj
    have hjk' : j = k := by omega
    rw [hjk'] at hj
    exact ⟨hj, Nat.le_refl k, hkj⟩
  | succ fuel ih =>
    intro k j hkj hjk hj
    cases htest : Nat.decEq (mulMod l a k) 1 with
    | isTrue ht =>
      have hred : flInvSearch l a (fuel + 1) k = k := by
        show (if mulMod l a k = 1 then k else flInvSearch l a fuel (k + 1)) = k
        rw [if_pos ht]
      rw [hred]
      exact ⟨ht, Nat.le_refl k, hkj⟩
    | isFalse hf =>
      have hred : flInvSearch l a (fuel + 1) k = flInvSearch l a fuel (k + 1) := by
        show (if mulMod l a k = 1 then k else flInvSearch l a fuel (k + 1))
          = flInvSearch l a fuel (k + 1)
        rw [if_neg hf]
      rw [hred]
      have hne : j ≠ k := by
        intro he
        rw [he] at hj
        exact hf hj
      obtain ⟨r1, r2, r3⟩ := ih (k + 1) j (by omega) (by omega) hj
      exact ⟨r1, by omega, r3⟩

/-- **M108F-5a: 逆元** — 1 から l−1 を走査して見つける a の逆元。 -/
def flInv (l a : Nat) : Nat := flInvSearch l a (l - 1) 1

/-- **定理 (M108F-5b): 逆元の仕様** — 1 ≤ flInv l a < l かつ
    `a * flInv l a ≡ 1 (mod l)`。M108F-3 の存在証明の witness b が
    探索範囲 `[1, l-1]` に収まるので、M108F-4b から範囲の上界も
    `b < l` に強まる（探索仕様の `j` 上界を witness の実際の値に
    取ることで、`ordSearch_spec` のような境界固定形より強い結論が
    直接得られる）。 -/
theorem flInv_spec (l : Nat) (hl : IsPrime l) {a : Nat}
    (ha1 : 1 ≤ a) (ha : a < l) :
    1 ≤ flInv l a ∧ flInv l a < l ∧ mulMod l a (flInv l a) = 1 := by
  obtain ⟨b, hb1, hb2, hb3⟩ := flInv_exists l hl ha1 ha
  have hb2' : b ≤ 1 + (l - 1) := by have := hl.1; omega
  show 1 ≤ flInvSearch l a (l - 1) 1 ∧ flInvSearch l a (l - 1) 1 < l
    ∧ mulMod l a (flInvSearch l a (l - 1) 1) = 1
  obtain ⟨r1, r2, r3⟩ := flInvSearch_spec l a (l - 1) 1 b hb1 hb2' hb3
  exact ⟨r2, by omega, r1⟩

/-! ## 乗法群 F_l^× -/

/-- **定理 (M108F-6): 乗法群 F_l^× : Grp** — 台集合
    `{j : Nat // 1 ≤ j ∧ j < l}`、積 = mulMod（閉性 = M108F-2）、
    単位元 = 1（l ≥ 2 で範囲内）、逆元 = flInv（閉性 = M108F-5）、
    群法則は mulMod の結合則・左単位律・M108F-5 の逆元仕様に帰着する。
    issue #35 A-4「素数性を使う F_l^× の群構造」の解消。 -/
def flUnits (l : Nat) (hl : IsPrime l) : Grp where
  carrier := { j : Nat // 1 ≤ j ∧ j < l }
  mul := fun x y => ⟨mulMod l x.val y.val,
    mulMod_ne_zero l hl x.property.1 x.property.2 y.property.1 y.property.2,
    mulMod_lt (by have := hl.1; omega) x.val y.val⟩
  one := ⟨1, Nat.le_refl 1, by have := hl.1; omega⟩
  inv := fun x => ⟨flInv l x.val,
    (flInv_spec l hl x.property.1 x.property.2).1,
    (flInv_spec l hl x.property.1 x.property.2).2.1⟩
  mul_assoc := by
    intro x y z
    apply Subtype.ext
    exact mulMod_assoc l x.val y.val z.val
  one_mul := by
    intro x
    apply Subtype.ext
    show mulMod l 1 x.val = x.val
    exact mulMod_one_left x.property.2
  inv_mul := by
    intro x
    apply Subtype.ext
    show mulMod l (flInv l x.val) x.val = 1
    rw [mulMod_comm]
    exact (flInv_spec l hl x.property.1 x.property.2).2.2

/-- F_l^× はアーベル群。 -/
theorem flUnits_comm (l : Nat) (hl : IsPrime l) :
    ∀ x y, (flUnits l hl).mul x y = (flUnits l hl).mul y x := by
  intro x y
  apply Subtype.ext
  exact mulMod_comm l x.val y.val

/-! ## HodgeTheater への接続 -/

/-- **定理 (M108F-7): HodgeTheater への接続サニティ** — F_l^× の台集合
    `{1, …, l−1}` の元は、HodgeTheater 側のラベル `j`（1 ≤ j < l）と
    同じ値で対応する（自明な整合確認）。HodgeTheater の未形式化申告
    「素数性を使う F_l^* の群構造」はここまでで解消。F_l^* =
    F_l^×/{±1} の商群構造（乗法的対称性、ΘNF-Hodge theater 側）は
    次層（正直申告）として残す。 -/
theorem flUnits_card_labels (l : Nat) (hl : IsPrime l) (j : Nat)
    (hj1 : 1 ≤ j) (hj2 : j < l) :
    ((⟨j, hj1, hj2⟩ : (flUnits l hl).carrier)).val = j := rfl

end IUT
