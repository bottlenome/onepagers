/-
  IUT/TorsionModule.lean — M101（一般 [a]-作用と πⁿ-捻れ塔の保存:
  柱B B-1 第一層 — 形式群加法経由の ℤ_p-加群作用）

  M89F（EisensteinTower）は O = ℤ_p[[X]]/(X^{p−1}+π) の捻れ塔 Λₙ 上で
  **1 の (p−1) 乗根倍 ζ·(−) が各層を保つ**ことしか示せていなかった
  （f(T) = πT + T^p が非線形なので一般の c では環の乗法では破綻する、
  という正直申告）。本ファイルは Lubin–Tate 形式群の**点の側**
  (pℤ_p) で、一般の a ∈ ℤ_p に対する **[a]-作用 [a](x) := (ltSol a)(x)**
  を構成し、それが πⁿ-捻れ点を πⁿ-捻れ点へ送ること — すなわち
  **一般 [c]-倍作用は形式群加法経由で捻れ塔を保つ** — を機械検証する。
  これは ζ-倍（環の乗法）の制限を取り払い、B-1 の核心「一般 [c]-倍
  作用（形式群加法経由）」を点レベルで実現するものである。

  * M101-1 `ltAct` — **[a]-作用** [a](x) := zpEval (ltSol a) x（一般 a）
  * M101-2 `ltAct_zero` / `ltAct_one` — 正規化 [0](x) = 0・[1](x) = x
    （ltSol_zero/ltSol_one（M76）+ zpEval_zero/zpEval_X（M77））
  * M101-3 `ltSol_comm_iter` — 級数の可換性 [a]∘[πⁿ] = [πⁿ]∘[a]
    （ltSol_comm（M76-1）と psComp_assoc（M72F）の n 帰納）
  * M101-4 `ltAct_preserves_torsion` — **本丸**: x ∈ Λₙ ⟹ [a](x) ∈ Λₙ
    （[πⁿ]([a]x) = [a]([πⁿ]x) = [a](0) = 0、可換性 + 合成両立 M79）
  * M101-5 `ltAct_mul` — 乗法性 [ab](x) = [a]([b](x))
    （lt_module_mul（M76-4）+ 合成両立）
  * M101-6 `ltAct_add` — **加群則（形式群加法経由）**:
    F([a]x, [b]x) = [a+b](x)（M81-5 lt_point_module_add の作用言い換え）
  * M101-7 `LTTorsionModuleData` / `ltTorsionModule` / `_exists` —
    総括: 一般 [a]-作用は捻れ塔を保つ ℤ_p-加群構造をなす

  これにより「一般 c ∈ ℤ_p の [c]-作用が捻れを保つ」が（点の側で）
  決着する — M89F の ζ-倍限定を超える。残件: 分岐側 O = eisRing の
  捻れ塔 Λₙ ⊆ O への移植（O 上の級数評価が要る）・Λₙ の位数・
  塔の生成元 λₙ は未形式化（正直申告、B-1 後続層）。
  全て選択公理不使用。
-/
import IUT.FormalGroupPointsLaw

namespace IUT

/-! ## [a]-作用 -/

/-- **M101-1: [a]-作用** — [a](x) := (ltSol a)(x) = zpEval (ltSol a) x。
    一般の a ∈ ℤ_p に対する Lubin–Tate 形式群の点への ℤ_p-作用。
    ζ-倍（環の乗法）と違い f の非線形性に阻まれない。 -/
def ltAct (p : Nat) (hp : IsPrime p) (a x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    (Zp p).carrier :=
  zpEval p (ltSol p hp a) x e hx

/-- [a](x) ∈ pℤ_p の標準 witness（zpEval_closed の言い換え）。 -/
abbrev ltActWit (p : Nat) (hp : IsPrime p) (a x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    (Zp p).carrier :=
  (zpRing p).mul e (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx)

/-! ## 正規化 -/

/-- **M101-2a: [0](x) = 0** — ltSol_zero（[0] = 0 級数, M76）+ zpEval_zero。 -/
theorem ltAct_zero (p : Nat) (hp : IsPrime p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    ltAct p hp ((zpRing p).zero) x e hx = (zpRing p).zero := by
  show zpEval p (ltSol p hp ((zpRing p).zero)) x e hx = (zpRing p).zero
  rw [ltSol_zero p hp]
  exact zpEval_zero p x e hx

/-- **M101-2b: [1](x) = x** — ltSol_one（[1] = X, M76）+ zpEval_X。 -/
theorem ltAct_one (p : Nat) (hp : IsPrime p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    ltAct p hp ((zpRing p).one) x e hx = x := by
  show zpEval p (ltSol p hp ((zpRing p).one)) x e hx = x
  rw [ltSol_one p hp]
  exact zpEval_X p hp.1 x e hx

/-! ## 級数の可換性 [a]∘[πⁿ] = [πⁿ]∘[a] -/

/-- **定理 (M101-3): [a] は [πⁿ] と可換** — psComp ([πⁿ], [a]) =
    psComp ([a], [πⁿ])。一段の可換性 ltSol_comm（M76-1: [a]∘f = f∘[a]）を
    結合則 psComp_assoc（M72F）で n の帰納に積み上げる。 -/
theorem ltSol_comm_iter (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) :
    ∀ n, psComp (zpRing p) (ltIter p n) (ltSol p hp a)
      = psComp (zpRing p) (ltSol p hp a) (ltIter p n) := by
  intro n
  have ha0 : ltSol p hp a 0 = (zpRing p).zero := rfl
  have hf0 : ltPoly p 0 = (zpRing p).zero := ltPoly_coeff_zero p hp.1
  induction n with
  | zero =>
    show psComp (zpRing p) (psX (zpRing p)) (ltSol p hp a)
      = psComp (zpRing p) (ltSol p hp a) (psX (zpRing p))
    rw [psComp_X (zpRing p) (ltSol p hp a) ha0,
      psComp_X_right (zpRing p) (ltSol p hp a)]
  | succ n ih =>
    have hn0 : ltIter p n 0 = (zpRing p).zero := ltIter_coeff_zero p hp.1 n
    show psComp (zpRing p)
        (psComp (zpRing p) (ltIter p n) (ltPoly p)) (ltSol p hp a)
      = psComp (zpRing p) (ltSol p hp a)
          (psComp (zpRing p) (ltIter p n) (ltPoly p))
    calc psComp (zpRing p)
          (psComp (zpRing p) (ltIter p n) (ltPoly p)) (ltSol p hp a)
        = psComp (zpRing p) (ltIter p n)
            (psComp (zpRing p) (ltPoly p) (ltSol p hp a)) :=
          psComp_assoc (zpRing p) (ltIter p n) (ltPoly p) (ltSol p hp a)
            hf0 ha0
      _ = psComp (zpRing p) (ltIter p n)
            (psComp (zpRing p) (ltSol p hp a) (ltPoly p)) := by
          rw [ltSol_comm p hp a]
      _ = psComp (zpRing p)
            (psComp (zpRing p) (ltIter p n) (ltSol p hp a)) (ltPoly p) :=
          (psComp_assoc (zpRing p) (ltIter p n) (ltSol p hp a) (ltPoly p)
            ha0 hf0).symm
      _ = psComp (zpRing p)
            (psComp (zpRing p) (ltSol p hp a) (ltIter p n)) (ltPoly p) := by
          rw [ih]
      _ = psComp (zpRing p) (ltSol p hp a)
            (psComp (zpRing p) (ltIter p n) (ltPoly p)) :=
          psComp_assoc (zpRing p) (ltSol p hp a) (ltIter p n) (ltPoly p)
            hn0 hf0

/-! ## 本丸: 一般 [a]-作用は捻れ塔を保つ -/

/-- **定理 (M101-4): [a]-作用は πⁿ-捻れ点を保つ（本丸）** —
    x ∈ Λₙ なら [a](x) ∈ Λₙ。[πⁿ]([a]x) = [a]([πⁿ]x)（可換性 M101-3 +
    合成両立 M79）= [a](0) = 0（ltSol a の定数項 0）。**一般の c ∈ ℤ_p の
    [c]-作用が捻れ塔を保つ** — M89F の ζ-倍限定（環の乗法）を超える、
    形式群加法経由の作用。 -/
theorem ltAct_preserves_torsion (p : Nat) (hp : IsPrime p)
    (a : (Zp p).carrier) (n : Nat) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    (ht : IsTorsionPoint p n x e hx) :
    IsTorsionPoint p n (ltAct p hp a x e hx) (ltActWit p hp a x e hx)
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx) := by
  show zpEval p (ltIter p n) (zpEval p (ltSol p hp a) x e hx)
      (ltActWit p hp a x e hx)
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx) = (zpRing p).zero
  rw [← zpEval_comp_closed p hp.1 (ltIter p n) (ltSol p hp a) rfl x e hx,
    ltSol_comm_iter p hp a n,
    zpEval_comp_closed p hp.1 (ltSol p hp a) (ltIter p n)
      (ltIter_coeff_zero p hp.1 n) x e hx]
  exact zpEval_eq_at_zero p (ltSol p hp a) rfl
    (zpEval p (ltIter p n) x e hx)
    ((zpRing p).mul e (zpEval p (psShift (zpRing p) (ltIter p n)) x e hx))
    (zpEval_closed p hp.1 (ltIter p n) (ltIter_coeff_zero p hp.1 n) x e hx)
    ht

/-! ## 乗法性と加群則 -/

/-- **定理 (M101-5): 乗法性** — [ab](x) = [a]([b](x))。
    lt_module_mul（M76-4: [a]∘[b] = [ab]）+ 合成両立（M79）。 -/
theorem ltAct_mul (p : Nat) (hp : IsPrime p) (a b x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    ltAct p hp ((zpRing p).mul a b) x e hx
      = ltAct p hp a (ltAct p hp b x e hx) (ltActWit p hp b x e hx)
          (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx) := by
  show zpEval p (ltSol p hp ((zpRing p).mul a b)) x e hx = _
  rw [← lt_module_mul p hp a b,
    zpEval_comp_closed p hp.1 (ltSol p hp a) (ltSol p hp b) rfl x e hx]
  rfl

/-- **定理 (M101-6): 加群則（形式群加法経由）** — 形式群和
    F([a](x), [b](x)) = [a+b](x)。M81-5 lt_point_module_add を [a]-作用の
    言葉に言い換えたもの。**[a]-作用の加法性は形式群加法で実現される** —
    まさに B-1 の「形式群加法経由」の核心。 -/
theorem ltAct_add (p : Nat) (hp : IsPrime p) (a b x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval2 p (lt2Sol p hp)
        (ltAct p hp a x e hx) (ltActWit p hp a x e hx)
        (ltAct p hp b x e hx) (ltActWit p hp b x e hx)
        (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
        (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
      = ltAct p hp ((zpRing p).add a b) x e hx :=
  lt_point_module_add p hp a b x e hx

/-! ## 総括: 捻れ塔を保つ ℤ_p-加群作用 -/

/-- **M101-7a: 一般 [a]-作用データ** — Lubin–Tate 形式群の点 pℤ_p 上の
    一般 ℤ_p-作用の全簿記: 正規化（[0] = 0・[1] = X）・**捻れ塔の保存**
    （一般 a で各 Λₙ を保つ）・乗法性（[ab] = [a]∘[b]）。M89F の ζ-倍
    限定を超える、形式群加法経由の作用。 -/
structure LTTorsionModuleData (p : Nat) (hp : IsPrime p) : Prop where
  /-- 正規化 [0](x) = 0。 -/
  act_zero : ∀ (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    ltAct p hp ((zpRing p).zero) x e hx = (zpRing p).zero
  /-- 正規化 [1](x) = x。 -/
  act_one : ∀ (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    ltAct p hp ((zpRing p).one) x e hx = x
  /-- **捻れ塔の保存**: 一般 a ∈ ℤ_p で x ∈ Λₙ ⟹ [a](x) ∈ Λₙ。 -/
  act_preserves : ∀ (a : (Zp p).carrier) (n : Nat) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    IsTorsionPoint p n x e hx →
    IsTorsionPoint p n (ltAct p hp a x e hx) (ltActWit p hp a x e hx)
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
  /-- 乗法性 [ab](x) = [a]([b](x))。 -/
  act_mul : ∀ (a b x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    ltAct p hp ((zpRing p).mul a b) x e hx
      = ltAct p hp a (ltAct p hp b x e hx) (ltActWit p hp b x e hx)
          (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)

/-- **M101-7b: witness** — ltAct が捻れ塔を保つ ℤ_p-加群作用を成す。 -/
def ltTorsionModule (p : Nat) (hp : IsPrime p) :
    LTTorsionModuleData p hp where
  act_zero := ltAct_zero p hp
  act_one := ltAct_one p hp
  act_preserves := fun a n x e hx ht => ltAct_preserves_torsion p hp a n x e hx ht
  act_mul := ltAct_mul p hp

/-- **M101-7c: 存在定理（ヘッドライン）** — Lubin–Tate 形式群の捻れ塔は
    一般 c ∈ ℤ_p の [c]-作用（形式群加法経由）で保たれる。B-1 の核心
    「一般 [c]-倍作用」を点の側で実現。 -/
theorem ltTorsionModule_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (LTTorsionModuleData p hp) :=
  ⟨ltTorsionModule p hp⟩

end IUT
