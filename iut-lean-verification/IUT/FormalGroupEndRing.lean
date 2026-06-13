/-
  IUT/FormalGroupEndRing.lean — M100（End(F) を環として閉じる:
  柱B B-4 — issue #36）

  M76（`FormalGroupOModule`）/ M76F（`FormalGroupEnd`）は
  a ↦ [a] := ltSol p hp a が形式群 F = lt2Sol 上で加法・乗法・単位を
  保つO-加群インターフェースをパッケージしたが、いずれも
  「**End(F) を環として閉じる一般論**（自己準同型の和・合成の閉性と
  環公理）は未形式化」と正直申告していた
  （`FormalGroupOModule.lean:26`・`FormalGroupEnd.lean:26-30`）。
  本モジュールはその穴を埋める。

  **設計**: 自己準同型環 End(F) の二つの自然な演算 —
  形式群加法 g ⊕ h := F(g(X), h(X)) = `ps21Comp F g h` と
  合成 g ⊙ h := g ∘ h = `psComp g h` — が、Lubin–Tate 像
  {[a] : a ∈ ℤ_p}（= End(F)、Lubin–Tate の主定理）の上で
  **可換環の全公理（可換・結合・分配・単位・零・逆元）を満たす**ことを、
  M76 の閉性（[a]⊕[b] = [a+b]・[a]⊙[b] = [ab]）と ℤ_p の環公理から
  機械検証する。これにより a ↦ [a] が **ℤ_p から End(F) への環同型
  （像の上）** であることがパッケージされる。

  * M100-1 `ltEnd_gAdd_comm` / `ltEnd_gAdd_assoc` — ⊕（形式群加法）の
    可換性・結合性（像の上。M76 + ℤ_p 加法公理で直接）
  * M100-2 `ltEnd_gMul_comm` / `ltEnd_gMul_assoc` — ⊙（合成）の
    可換性・結合性（合成は一般に非可換だが LT 像では ab = ba で可換）
  * M100-3 `ltEnd_left_distrib` / `ltEnd_right_distrib` — 分配律
    [a]⊙([b]⊕[c]) = ([a]⊙[b])⊕([a]⊙[c])（合成と形式群加法を繋ぐ
    環の本質的公理。M76 の加法・乗法の合流）
  * M100-4 `ltEnd_gAdd_zero` / `ltEnd_gAdd_neg` / `ltEnd_gMul_one` —
    単位元（0 級数）・逆元（[−a]）・乗法単位（X）の環公理
  * M100-5 `LTEndRingData` / `ltEndRingData` / `ltEndRing_exists` —
    総括 witness: End(F) の像が ⊕/⊙ で**可換環をなし**、ι : a ↦ [a] が
    +/×/0/1 を ⊕/⊙/0級数/X として実現する**単射準同型**（環同型）で
    あることを束ねた純レコード

  これで「End(F) の像（= Lubin–Tate により ℤ_p ≅ End(F)）が
  形式群加法と合成のもとで可換環として閉じる」ことが公理ゼロで
  機械検証された。

  **位置づけ（正直な申告）**: 像 {[a]} が End(F) の**全体**を尽くすこと
  （ℤ_p → End(F) の全射性）と、[a] の F-準同型性
  [a](F(X,Y)) = F([a]X, [a]Y) は本モジュールの対象外（M76F の申告と
  同じく別項目）。本モジュールが閉じるのは像の上での環構造である。
  全て選択公理不使用。
-/
import IUT.FormalGroupEnd

namespace IUT

/-! ## 形式群加法 ⊕ の環公理（像の上） -/

/-- **M100-1a: ⊕ の可換性** — F([a], [b]) = F([b], [a])。
    両辺を M76 で [a+b]・[b+a] に潰し ℤ_p の加法可換で合流。 -/
theorem ltEnd_gAdd_comm (p : Nat) (hp : IsPrime p) (a b : (Zp p).carrier) :
    ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a) (ltSol p hp b)
      = ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp b) (ltSol p hp a) := by
  rw [lt_module_add p hp a b, lt_module_add p hp b a, (zpRing p).add_comm]

/-- **M100-1b: ⊕ の結合性** — F(F([a],[b]),[c]) = F([a],F([b],[c]))。 -/
theorem ltEnd_gAdd_assoc (p : Nat) (hp : IsPrime p)
    (a b c : (Zp p).carrier) :
    ps21Comp (zpRing p) (lt2Sol p hp)
        (ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a) (ltSol p hp b))
        (ltSol p hp c)
      = ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a)
          (ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp b)
            (ltSol p hp c)) := by
  rw [lt_module_add p hp a b, lt_module_add p hp b c,
    lt_module_add p hp ((zpRing p).add a b) c,
    lt_module_add p hp a ((zpRing p).add b c),
    (zpRing p).add_assoc]

/-! ## 合成 ⊙ の環公理（像の上） -/

/-- **M100-2a: ⊙ の可換性** — [a] ∘ [b] = [b] ∘ [a]。
    合成は一般には非可換だが LT 像では ab = ba で可換。 -/
theorem ltEnd_gMul_comm (p : Nat) (hp : IsPrime p) (a b : (Zp p).carrier) :
    psComp (zpRing p) (ltSol p hp a) (ltSol p hp b)
      = psComp (zpRing p) (ltSol p hp b) (ltSol p hp a) := by
  rw [lt_module_mul p hp a b, lt_module_mul p hp b a, (zpRing p).mul_comm]

/-- **M100-2b: ⊙ の結合性** — ([a]∘[b])∘[c] = [a]∘([b]∘[c])。 -/
theorem ltEnd_gMul_assoc (p : Nat) (hp : IsPrime p)
    (a b c : (Zp p).carrier) :
    psComp (zpRing p) (psComp (zpRing p) (ltSol p hp a) (ltSol p hp b))
        (ltSol p hp c)
      = psComp (zpRing p) (ltSol p hp a)
          (psComp (zpRing p) (ltSol p hp b) (ltSol p hp c)) := by
  rw [lt_module_mul p hp a b, lt_module_mul p hp b c,
    lt_module_mul p hp ((zpRing p).mul a b) c,
    lt_module_mul p hp a ((zpRing p).mul b c),
    (zpRing p).mul_assoc]

/-! ## 分配律（合成と形式群加法を繋ぐ環の本質的公理） -/

/-- **M100-3a: 左分配律** — [a] ∘ ([b] ⊕ [c]) = ([a]∘[b]) ⊕ ([a]∘[c])。
    LHS = [a]∘[b+c] = [a(b+c)] = [ab+ac] = RHS。M76 の加法・乗法の合流。 -/
theorem ltEnd_left_distrib (p : Nat) (hp : IsPrime p)
    (a b c : (Zp p).carrier) :
    psComp (zpRing p) (ltSol p hp a)
        (ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp b) (ltSol p hp c))
      = ps21Comp (zpRing p) (lt2Sol p hp)
          (psComp (zpRing p) (ltSol p hp a) (ltSol p hp b))
          (psComp (zpRing p) (ltSol p hp a) (ltSol p hp c)) := by
  rw [lt_module_add p hp b c,
    lt_module_mul p hp a ((zpRing p).add b c),
    lt_module_mul p hp a b, lt_module_mul p hp a c,
    lt_module_add p hp ((zpRing p).mul a b) ((zpRing p).mul a c),
    (zpRing p).left_distrib]

/-- **M100-3b: 右分配律** — ([a] ⊕ [b]) ∘ [c] = ([a]∘[c]) ⊕ ([b]∘[c])。
    LHS = [a+b]∘[c] = [(a+b)c] = [ac+bc] = RHS。 -/
theorem ltEnd_right_distrib (p : Nat) (hp : IsPrime p)
    (a b c : (Zp p).carrier) :
    psComp (zpRing p)
        (ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a) (ltSol p hp b))
        (ltSol p hp c)
      = ps21Comp (zpRing p) (lt2Sol p hp)
          (psComp (zpRing p) (ltSol p hp a) (ltSol p hp c))
          (psComp (zpRing p) (ltSol p hp b) (ltSol p hp c)) := by
  rw [lt_module_add p hp a b,
    lt_module_mul p hp ((zpRing p).add a b) c,
    lt_module_mul p hp a c, lt_module_mul p hp b c,
    lt_module_add p hp ((zpRing p).mul a c) ((zpRing p).mul b c),
    CRing.right_distrib]

/-! ## 単位元・逆元・乗法単位 -/

/-- **M100-4a: ⊕ の左単位元** — [0] ⊕ [a] = [a]（0 級数が加法単位）。 -/
theorem ltEnd_gAdd_zero (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) :
    ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp (zpRing p).zero)
        (ltSol p hp a)
      = ltSol p hp a := by
  rw [lt_module_add p hp (zpRing p).zero a, (zpRing p).zero_add]

/-- **M100-4b: ⊕ の逆元** — [−a] ⊕ [a] = [0] = 0 級数。 -/
theorem ltEnd_gAdd_neg (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) :
    ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp ((zpRing p).neg a))
        (ltSol p hp a)
      = psZero (zpRing p) := by
  rw [lt_module_add p hp ((zpRing p).neg a) a, (zpRing p).neg_add]
  exact ltSol_zero p hp

/-- **M100-4c: ⊙ の左単位元** — [1] ⊙ [a] = [a]（X が乗法単位）。 -/
theorem ltEnd_gMul_one (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) :
    psComp (zpRing p) (ltSol p hp (zpRing p).one) (ltSol p hp a)
      = ltSol p hp a := by
  rw [lt_module_mul p hp (zpRing p).one a, (zpRing p).one_mul]

/-! ## 総括 witness: End(F) の像は可換環をなす（ℤ_p ≅ End(F)） -/

/-- **M100-5a: End(F) 環パッケージ** — 自己準同型環 End(F) の像
    {[a] : a ∈ ℤ_p} が、形式群加法 ⊕ と合成 ⊙ のもとで**可換環**をなし、
    包含 ι : ℤ_p → End(F)、a ↦ [a] がその環構造を実現する**単射準同型**
    であることを束ねた純レコード（ℤ_p ≅ End(F) 像の環同型）。 -/
structure LTEndRingData (p : Nat) (hp : IsPrime p) where
  /-- 包含 ι : a ↦ [a]。 -/
  incl : (Zp p).carrier → PS (zpRing p)
  /-- 形式群加法 ⊕。 -/
  gAdd : PS (zpRing p) → PS (zpRing p) → PS (zpRing p)
  /-- 合成 ⊙。 -/
  gMul : PS (zpRing p) → PS (zpRing p) → PS (zpRing p)
  /-- ι の定義（[a] = ltSol p hp a）。 -/
  incl_eq : ∀ a, incl a = ltSol p hp a
  /-- ⊕ の定義（形式群加法）。 -/
  gAdd_eq : ∀ g h, gAdd g h = ps21Comp (zpRing p) (lt2Sol p hp) g h
  /-- ⊙ の定義（合成）。 -/
  gMul_eq : ∀ g h, gMul g h = psComp (zpRing p) g h
  -- ι は環準同型（演算の実現）
  add_hom : ∀ a b, incl ((zpRing p).add a b) = gAdd (incl a) (incl b)
  mul_hom : ∀ a b, incl ((zpRing p).mul a b) = gMul (incl a) (incl b)
  zero_hom : incl (zpRing p).zero = psZero (zpRing p)
  one_hom : incl (zpRing p).one = psX (zpRing p)
  inj : ∀ a b, incl a = incl b → a = b
  -- 像の上で ⊕/⊙ が可換環公理を満たす
  add_comm : ∀ a b, gAdd (incl a) (incl b) = gAdd (incl b) (incl a)
  add_assoc : ∀ a b c,
      gAdd (gAdd (incl a) (incl b)) (incl c)
        = gAdd (incl a) (gAdd (incl b) (incl c))
  mul_comm : ∀ a b, gMul (incl a) (incl b) = gMul (incl b) (incl a)
  mul_assoc : ∀ a b c,
      gMul (gMul (incl a) (incl b)) (incl c)
        = gMul (incl a) (gMul (incl b) (incl c))
  left_distrib : ∀ a b c,
      gMul (incl a) (gAdd (incl b) (incl c))
        = gAdd (gMul (incl a) (incl b)) (gMul (incl a) (incl c))

/-- **M100-5b: witness** — ι := ltSol p hp、⊕ := ps21Comp F、⊙ := psComp。
    各フィールドは M100-1〜4・M76・M76F-3 で充足。 -/
def ltEndRingData (p : Nat) (hp : IsPrime p) : LTEndRingData p hp where
  incl := ltSol p hp
  gAdd := fun g h => ps21Comp (zpRing p) (lt2Sol p hp) g h
  gMul := fun g h => psComp (zpRing p) g h
  incl_eq := fun _ => rfl
  gAdd_eq := fun _ _ => rfl
  gMul_eq := fun _ _ => rfl
  add_hom := fun a b => (lt_module_add p hp a b).symm
  mul_hom := fun a b => (lt_module_mul p hp a b).symm
  zero_hom := ltSol_zero p hp
  one_hom := ltSol_one p hp
  inj := fun a b h => ltSol_injective p hp a b h
  add_comm := fun a b => ltEnd_gAdd_comm p hp a b
  add_assoc := fun a b c => ltEnd_gAdd_assoc p hp a b c
  mul_comm := fun a b => ltEnd_gMul_comm p hp a b
  mul_assoc := fun a b c => ltEnd_gMul_assoc p hp a b c
  left_distrib := fun a b c => ltEnd_left_distrib p hp a b c

/-- **M100-5c: 非空性** — End(F) の環パッケージは実在する。 -/
theorem ltEndRing_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (LTEndRingData p hp) :=
  ⟨ltEndRingData p hp⟩

end IUT
