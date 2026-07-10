/-
  IUT/Zmod3PowUnits.lean — ZPU（A3 M4 の土台: 乗法群 (ℤ/3^ℓ)^× と
  choice-free Hensel 逆元関数）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 IUT の
     指標同型 Gal(ℚ(ζ_{3ⁿ})/ℚ) ≅ (ℤ/3ⁿ)^× に直結する本物の乗法群
     (ℤ/3^ℓ)^× をゼロから積む）。担体は Nat subtype `{ a : Nat // a < 3^ℓ ∧ ¬ 3 ∣ a }`、
     乗法は `a·b mod 3^ℓ`、逆元は `ctr_inv_exists`（Hensel 持ち上げ・choice-free・
     Bezout 不使用）を**存在形から関数 `zpuInv` へ脱存在化**したもの。

  **complete_pct 影響**: A3 M4（指標同型 Gal(ℚ(ζ_{3ⁿ})/ℚ) ≅ (ℤ/3ⁿ)^×・逆極限
  ℤ₃^×）の基盤——乗法群 (ℤ/3^ℓ)^× を choice-free 逆元付きで新設する。cci（レベル
  同型 M4a）・zps（逆系＋全射性）・cli（極限同型 M4b）・cps（射影全射性 M4c）が
  この上に乗る。**本ファイル単体では complete_pct 未設定**（M4b＝cli 到達で反映）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・素数冪 3^ℓ 専用の乗法単数群。一般の (ℤ/N)^× ではない。
   (ii)  逆元は Euler 定理（位数 φ(3^ℓ) の Fermat 冪）を**使わず**、mod 3 の逆元を
         3^ℓ へ持ち上げる Hensel 帰納（`zpuInv`）で choice-free に供給する。
         既存 `zmodUnits`（素数 p 限定・Quot 担体・Fermat 逆元）とは別物のため
         名前衝突を避け `zpuGrp` を新設。
   (iii) 逆系・逆極限 ℤ₃^× は本ファイルに含めない（cli・M4b の射程）。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]・Classical.choice 無し）。
  禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。3^ℓ は omega 不可のため冪補題を本ファイルに集約。
  新規ファイル 1 個のみ（共有ファイルは親が統合）。依存は FundamentalGroup（Grp）と
  Nat core 算術のみ。
-/
import IUT.FundamentalGroup

namespace IUT

/-! ## ZPU-0: 冪の正値・整除の小補題（omega は 3^ℓ を扱えない・本ファイルに集約） -/

/-- **ZPU-0a: 3^k ≥ 1**。 -/
theorem zpu_pow_pos (k : Nat) : 1 ≤ (3 : Nat) ^ k := Nat.one_le_pow k 3 (by omega)

/-- **ZPU-0b: 3^i ∣ 3^j（i ≤ j）** — 差分 d := j−i の `Nat.pow_add`。 -/
theorem zpu_pow_dvd {i j : Nat} (h : i ≤ j) : (3 : Nat) ^ i ∣ 3 ^ j := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  refine ⟨3 ^ d, ?_⟩
  rw [← hd, Nat.pow_add]

/-- **ZPU-0c: 3 ∣ 3^ℓ（ℓ ≥ 1）**。 -/
theorem zpu_three_dvd_pow (ℓ : Nat) (hℓ : 1 ≤ ℓ) : (3 : Nat) ∣ 3 ^ ℓ := by
  obtain ⟨k, hk⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  rw [hk]
  exact ⟨3 ^ k, by rw [Nat.pow_succ, Nat.mul_comm (3 ^ k) 3]⟩

/-- **ZPU-0d: 1 < 3^ℓ（ℓ ≥ 1）**。 -/
theorem zpu_one_lt (ℓ : Nat) (hℓ : 1 ≤ ℓ) : 1 < 3 ^ ℓ := by
  obtain ⟨k, hk⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  rw [hk, Nat.pow_succ]
  have hp : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by omega)
  omega

/-! ## ZPU-1: Hensel 逆元の関数化（`ctr_inv_exists` の脱存在化・★本ファイルの中核） -/

/-- **ZPU-1a: mod 3^ℓ 逆元関数 `zpuInv`** — 基底は mod 3 の逆元 `a % 3`、段は
    `b + t·3^{m+1}`（t は `ctr_tex` の witness 式）。項レベル ite（by_cases 不使用）。 -/
def zpuInv : Nat → Nat → Nat
  | 0,     a => a % 3
  | m + 1, a =>
      let b := zpuInv m a
      let q := a * b / 3 ^ (m + 1)
      let t := if a % 3 = 1 then (3 - q % 3) % 3 else q % 3
      b + t * 3 ^ (m + 1)

/-- **ZPU-1b: `zpuInv` の段展開**（let 展開・rfl）。 -/
theorem zpuInv_succ (m a : Nat) :
    zpuInv (m + 1) a =
      zpuInv m a
        + (if a % 3 = 1 then (3 - a * zpuInv m a / 3 ^ (m + 1) % 3) % 3
           else a * zpuInv m a / 3 ^ (m + 1) % 3) * 3 ^ (m + 1) := rfl

/-- **ZPU-1c: 段の逆元則（b・t 抽象版）** — `ctr_inv_exists` の succ ケースを
    b（下段逆元）・t（mod 3 補正）抽象の補題として写経。b·t は関数の値を後で代入。 -/
theorem zpuInv_step_aux (m a b t : Nat)
    (hb3 : ¬ 3 ∣ b) (hbm : a * b % 3 ^ (m + 1) = 1)
    (ht : (a * b / 3 ^ (m + 1) + a * t) % 3 = 0) :
    ¬ 3 ∣ (b + t * 3 ^ (m + 1))
      ∧ a * (b + t * 3 ^ (m + 1)) % 3 ^ (m + 1 + 1) = 1 := by
  have hdm := Nat.div_add_mod (a * b) (3 ^ (m + 1))
  rw [hbm] at hdm
  refine ⟨?_, ?_⟩
  · intro hd
    apply hb3
    have hQ3 : (3 : Nat) ∣ 3 ^ (m + 1) := ⟨3 ^ m, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    obtain ⟨s, hs⟩ := hQ3
    obtain ⟨w, hw⟩ := hd
    have hts : t * 3 ^ (m + 1) = 3 * (t * s) := by
      rw [hs, ← Nat.mul_assoc, Nat.mul_comm t 3, Nat.mul_assoc]
    exact ⟨w - t * s, by omega⟩
  · obtain ⟨w, hw⟩ :=
      (Nat.dvd_of_mod_eq_zero ht : (3 : Nat) ∣ (a * b / 3 ^ (m + 1) + a * t))
    have hQ : (3 : Nat) ^ (m + 1 + 1) = 3 ^ (m + 1) * 3 := Nat.pow_succ 3 (m + 1)
    have hval : a * (b + t * 3 ^ (m + 1)) = 1 + w * 3 ^ (m + 1 + 1) := by
      have e1 : a * (b + t * 3 ^ (m + 1)) = a * b + a * t * 3 ^ (m + 1) := by
        rw [Nat.mul_add, Nat.mul_assoc]
      have e2 : (a * b / 3 ^ (m + 1) + a * t) * 3 ^ (m + 1)
          = 3 ^ (m + 1) * (a * b / 3 ^ (m + 1)) + a * t * 3 ^ (m + 1) := by
        rw [Nat.add_mul, Nat.mul_comm (a * b / 3 ^ (m + 1)) (3 ^ (m + 1))]
      have e3 : (a * b / 3 ^ (m + 1) + a * t) * 3 ^ (m + 1) = 3 * w * 3 ^ (m + 1) := by rw [hw]
      have e4 : 3 ^ (m + 1) * (a * b / 3 ^ (m + 1)) + a * t * 3 ^ (m + 1)
          = 3 * w * 3 ^ (m + 1) := by rw [← e2]; exact e3
      have e5 : w * (3 ^ (m + 1) * 3) = 3 * w * 3 ^ (m + 1) := by
        rw [Nat.mul_comm (3 ^ (m + 1)) 3, ← Nat.mul_assoc, Nat.mul_comm w 3]
      rw [e1, ← hdm, hQ, e5]
      omega
    rw [hval]
    have hp : 1 < 3 ^ (m + 1 + 1) := by
      have h1 : 1 ≤ 3 ^ (m + 1) := Nat.one_le_pow (m + 1) 3 (by omega)
      rw [hQ]; omega
    have hmod : (1 + w * 3 ^ (m + 1 + 1)) % 3 ^ (m + 1 + 1) = 1 % 3 ^ (m + 1 + 1) :=
      Nat.add_mul_mod_self_right 1 w (3 ^ (m + 1 + 1))
    rw [hmod, Nat.mod_eq_of_lt hp]

/-- **ZPU-1d: 逆元仕様（本丸）** — 3∤a なら 3∤`zpuInv m a` かつ a·`zpuInv m a` ≡ 1
    (mod 3^{m+1})。`ctr_inv_exists` の帰納を関数版へ写経（∃ の witness を関数値に置換）。 -/
theorem zpuInv_spec : ∀ m a, ¬ 3 ∣ a →
    ¬ 3 ∣ zpuInv m a ∧ a * zpuInv m a % 3 ^ (m + 1) = 1 := by
  intro m
  induction m with
  | zero =>
    intro a ha
    refine ⟨?_, ?_⟩
    · show ¬ 3 ∣ (a % 3)
      intro hd; obtain ⟨k, hk⟩ := hd; omega
    · show a * (a % 3) % 3 = 1
      rw [Nat.mul_mod a (a % 3) 3, Nat.mod_mod_of_dvd a (Nat.dvd_refl 3)]
      have h : a % 3 = 1 ∨ a % 3 = 2 := by omega
      cases h with
      | inl h1 => rw [h1]
      | inr h2 => rw [h2]
  | succ m ih =>
    intro a ha
    obtain ⟨hb3, hbm⟩ := ih a ha
    have ht : (a * zpuInv m a / 3 ^ (m + 1)
        + a * (if a % 3 = 1 then (3 - a * zpuInv m a / 3 ^ (m + 1) % 3) % 3
               else a * zpuInv m a / 3 ^ (m + 1) % 3)) % 3 = 0 := by
      cases Nat.decEq (a % 3) 1 with
      | isTrue h1 => rw [if_pos h1, Nat.add_mod, Nat.mul_mod, h1]; omega
      | isFalse h1 =>
        have h2 : a % 3 = 2 := by omega
        rw [if_neg h1, Nat.add_mod, Nat.mul_mod, h2]; omega
    have hfin := zpuInv_step_aux m a (zpuInv m a)
      (if a % 3 = 1 then (3 - a * zpuInv m a / 3 ^ (m + 1) % 3) % 3
       else a * zpuInv m a / 3 ^ (m + 1) % 3) hb3 hbm ht
    rw [zpuInv_succ m a]
    exact hfin

/-- **ZPU-1e: `zpuInv m a` < 3^{m+1}** — 基底 a%3 < 3、段 b + t·3^{m+1} < 3·3^{m+1}。 -/
theorem zpuInv_lt : ∀ m a, zpuInv m a < 3 ^ (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro a
    show a % 3 < 3 ^ (0 + 1)
    have h3 : (3 : Nat) ^ (0 + 1) = 3 := by rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    rw [h3]
    exact Nat.mod_lt a (by omega)
  | succ m ih =>
    intro a
    rw [zpuInv_succ m a]
    have hb := ih a
    have hp : (3 : Nat) ^ (m + 1 + 1) = 3 ^ (m + 1) * 3 := Nat.pow_succ 3 (m + 1)
    have ht3 : (if a % 3 = 1 then (3 - a * zpuInv m a / 3 ^ (m + 1) % 3) % 3
               else a * zpuInv m a / 3 ^ (m + 1) % 3) < 3 := by
      cases Nat.decEq (a % 3) 1 with
      | isTrue h1 => rw [if_pos h1]; exact Nat.mod_lt _ (by omega)
      | isFalse h1 => rw [if_neg h1]; exact Nat.mod_lt _ (by omega)
    have hmul : (if a % 3 = 1 then (3 - a * zpuInv m a / 3 ^ (m + 1) % 3) % 3
                else a * zpuInv m a / 3 ^ (m + 1) % 3) * 3 ^ (m + 1)
              ≤ 2 * 3 ^ (m + 1) :=
      Nat.mul_le_mul (by omega) (Nat.le_refl (3 ^ (m + 1)))
    rw [hp]
    omega

/-! ## ZPU-2: レベル ℓ ラッパ（ℓ ≥ 1・添字合わせ m := ℓ−1 を一元化） -/

/-- **ZPU-2a: レベル逆元** `zpuInvL ℓ a := zpuInv (ℓ−1) a`。 -/
def zpuInvL (ℓ : Nat) (a : Nat) : Nat := zpuInv (ℓ - 1) a

/-- **ZPU-2b: 3∤`zpuInvL ℓ a`**。 -/
theorem zpuInvL_nd3 (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : Nat) (ha : ¬ 3 ∣ a) :
    ¬ 3 ∣ zpuInvL ℓ a :=
  (zpuInv_spec (ℓ - 1) a ha).1

/-- **ZPU-2c: a·`zpuInvL ℓ a` ≡ 1 (mod 3^ℓ)** — 添字 (ℓ−1)+1 = ℓ の書き換え 1 回。 -/
theorem zpuInvL_one (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : Nat) (ha : ¬ 3 ∣ a) :
    a * zpuInvL ℓ a % 3 ^ ℓ = 1 := by
  have h := (zpuInv_spec (ℓ - 1) a ha).2
  have he : ℓ - 1 + 1 = ℓ := by omega
  rw [he] at h
  exact h

/-! ## ZPU-3: mod / 積の 3-非整除（4 分岐 omega ＋ mod-mod 論法） -/

/-- **ZPU-3a: 3∤a・3∤b ⟹ 3∤(a·b)** — a%3,b%3 ∈ {1,2} の 4 分岐（euclid 不要の初等形）。 -/
theorem zpu_mul_nd3_raw (a b : Nat) (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b) : ¬ 3 ∣ (a * b) := by
  intro h
  have hmm : a * b % 3 = a % 3 * (b % 3) % 3 := Nat.mul_mod a b 3
  have ha2 : a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb2 : b % 3 = 1 ∨ b % 3 = 2 := by omega
  cases ha2 with
  | inl h1 =>
    cases hb2 with
    | inl h2 => rw [h1, h2] at hmm; omega
    | inr h2 => rw [h1, h2] at hmm; omega
  | inr h1 =>
    cases hb2 with
    | inl h2 => rw [h1, h2] at hmm; omega
    | inr h2 => rw [h1, h2] at hmm; omega

/-- **ZPU-3b: 3∤x ⟹ 3∤(x mod 3^ℓ)** — `ctr_mod_not_dvd3` と同型の mod-mod 論法。 -/
theorem zpu_mod_nd3 (ℓ : Nat) (hℓ : 1 ≤ ℓ) (x : Nat) (hx : ¬ 3 ∣ x) :
    ¬ 3 ∣ (x % 3 ^ ℓ) := by
  intro h
  apply hx
  have hd3 : (3 : Nat) ∣ 3 ^ ℓ := zpu_three_dvd_pow ℓ hℓ
  have hmm : x % 3 ^ ℓ % 3 = x % 3 := Nat.mod_mod_of_dvd x hd3
  obtain ⟨r, hr⟩ := h
  have hz : x % 3 ^ ℓ % 3 = 0 := by rw [hr]; omega
  rw [hmm] at hz
  exact Nat.dvd_of_mod_eq_zero hz

/-- **ZPU-3c: 3∤a・3∤b ⟹ 3∤(a·b mod 3^ℓ)** — 群乗法の担体条件。 -/
theorem zpu_mul_nd3 (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a b : Nat) (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b) :
    ¬ 3 ∣ (a * b % 3 ^ ℓ) :=
  zpu_mod_nd3 ℓ hℓ (a * b) (zpu_mul_nd3_raw a b ha hb)

/-! ## ZPU-4: mod 正規化補題（結合律・逆元則の主材料） -/

/-- **ZPU-4a: (x mod N)·y ≡ x·y (mod N)**。 -/
theorem zpu_mod_mul (x y N : Nat) : (x % N) * y % N = x * y % N := by
  rw [Nat.mul_mod (x % N) y N, Nat.mod_mod_of_dvd x (Nat.dvd_refl N), ← Nat.mul_mod x y N]

/-- **ZPU-4b: x·(y mod N) ≡ x·y (mod N)**。 -/
theorem zpu_mul_mod (x y N : Nat) : x * (y % N) % N = x * y % N := by
  rw [Nat.mul_mod x (y % N) N, Nat.mod_mod_of_dvd y (Nat.dvd_refl N), ← Nat.mul_mod x y N]

/-! ## ZPU-5: 群 (ℤ/3^ℓ)^×（担体 Nat subtype・素数冪版・既存 zmodUnits と別名） -/

/-- **ZPU-5: 乗法群 `zpuGrp ℓ`** — 担体 `{ a // a < 3^ℓ ∧ ¬ 3 ∣ a }`、
    乗法 `a·b mod 3^ℓ`、単位元 1、逆元 `zpuInvL a mod 3^ℓ`。左公理を Nat.mul_mod で充填。 -/
def zpuGrp (ℓ : Nat) (hℓ : 1 ≤ ℓ) : Grp where
  carrier := { a : Nat // a < 3 ^ ℓ ∧ ¬ 3 ∣ a }
  mul := fun a b =>
    ⟨a.val * b.val % 3 ^ ℓ,
      Nat.mod_lt _ (by have := zpu_pow_pos ℓ; omega),
      zpu_mul_nd3 ℓ hℓ a.val b.val a.property.2 b.property.2⟩
  one := ⟨1, zpu_one_lt ℓ hℓ, by intro h; obtain ⟨k, hk⟩ := h; omega⟩
  inv := fun a =>
    ⟨zpuInvL ℓ a.val % 3 ^ ℓ,
      Nat.mod_lt _ (by have := zpu_pow_pos ℓ; omega),
      zpu_mod_nd3 ℓ hℓ (zpuInvL ℓ a.val) (zpuInvL_nd3 ℓ hℓ a.val a.property.2)⟩
  mul_assoc := fun a b c => by
    apply Subtype.ext
    show a.val * b.val % 3 ^ ℓ * c.val % 3 ^ ℓ = a.val * (b.val * c.val % 3 ^ ℓ) % 3 ^ ℓ
    rw [zpu_mod_mul (a.val * b.val) c.val (3 ^ ℓ), zpu_mul_mod a.val (b.val * c.val) (3 ^ ℓ),
        Nat.mul_assoc a.val b.val c.val]
  one_mul := fun a => by
    apply Subtype.ext
    show 1 * a.val % 3 ^ ℓ = a.val
    rw [Nat.one_mul, Nat.mod_eq_of_lt a.property.1]
  inv_mul := fun a => by
    apply Subtype.ext
    show zpuInvL ℓ a.val % 3 ^ ℓ * a.val % 3 ^ ℓ = 1
    rw [zpu_mod_mul (zpuInvL ℓ a.val) a.val (3 ^ ℓ), Nat.mul_comm (zpuInvL ℓ a.val) a.val,
        zpuInvL_one ℓ hℓ a.val a.property.2]

/-- **ZPU-6: `zpuGrp` は可換**（Subtype.ext ＋ Nat.mul_comm）。 -/
theorem zpuGrp_comm (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a b : (zpuGrp ℓ hℓ).carrier) :
    (zpuGrp ℓ hℓ).mul a b = (zpuGrp ℓ hℓ).mul b a := by
  apply Subtype.ext
  show a.val * b.val % 3 ^ ℓ = b.val * a.val % 3 ^ ℓ
  rw [Nat.mul_comm a.val b.val]

end IUT
