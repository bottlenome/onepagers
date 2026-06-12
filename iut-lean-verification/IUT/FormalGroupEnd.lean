/-
  IUT/FormalGroupEnd.lean — M76F（O-加群構造のインターフェース化と
  剛性: 形式 ℤ_p-加群キャンペーン・パッケージ層）

  M76 で完全証明した [a] := ltSol 級数族の O-加群構造
  （f との可換性・正規化・F-加法・合成乗法）を
  **インターフェース構造 + witness + 剛性定理**として
  パッケージする（M27 の `LocalCFTData` 方式）。

  * M76F-1 `FormalOModuleData` — O-加群構造のインターフェース:
    係数正規化（定数項 0・一次係数 a）、f との可換性、
    [0] = 0・[1] = X、F-加法 F([a],[b]) = [a+b]、
    合成乗法 [a]∘[b] = [ab] の 8 フィールド
  * M76F-2 `ltOModule` — **witness**: M76 の諸定理（ltSol_comm /
    ltSol_zero / ltSol_one / lt_module_add / lt_module_mul）と
    定義的等式（rfl）でフィールドを充足
  * M76F-3 `ltSol_injective` — a ↦ [a] は単射（一次係数 a の読み出し
    = congrFun。「環準同型 ℤ_p ↪ End(F)」の単射性）
  * M76F-4 `oModule_bracket_unique` — **剛性（本丸）**: インター
    フェースの任意の witness D は D.bracket = ltSol を満たす。
    f との可換性 + f∘G の崩落（M72F）→ LT 方程式 → 一意性（M49）
  * M76F-5 `oModule_unique` / `ltOModule_inverse` — witness 同士の
    bracket の一致（剛性 ×2）と一般の逆元 F([a], [−a]) = 0 の
    インターフェース語彙での言い換え（M76-5a から定義的に）

  **位置づけ（正直な申告）**: End(F) を環として閉じる一般論
  （任意の F-自己準同型の和・合成の閉性）や [a] の F-準同型性
  [a](F(X,Y)) = F([a]X, [a]Y) は未形式化。本モジュールが示すのは
  「[a] 族の O-加群インターフェースは ltSol で一意に充足される」
  という剛性である。全て選択公理不使用。
  （部品証明はサブエージェント並行開発の成果を統合。）
-/
import IUT.FormalGroupOModule

namespace IUT

/-! ## O-加群構造のインターフェース -/

/-- **M76F-1: O-加群構造のインターフェース** — 形式群 F = lt2Sol 上の
    級数族 a ↦ [a] が満たすべき仕様の構造化:
    係数正規化・f との可換性・加法/乗法/単位の保存。 -/
structure FormalOModuleData (p : Nat) (hp : IsPrime p) where
  /-- 級数族 a ↦ [a]。 -/
  bracket : (Zp p).carrier → PS (zpRing p)
  /-- 定数項の消滅 [a](0) = 0。 -/
  bracket_coeff_zero : ∀ a, bracket a 0 = (zpRing p).zero
  /-- 一次係数 = a（正規化）。 -/
  bracket_coeff_one : ∀ a, bracket a 1 = a
  /-- f との可換性 [a]∘f = f∘[a]。 -/
  bracket_comm : ∀ a, psComp (zpRing p) (bracket a) (ltPoly p)
      = psComp (zpRing p) (ltPoly p) (bracket a)
  /-- 零の保存 [0] = 0 級数。 -/
  map_zero : bracket ((zpRing p).zero) = psZero (zpRing p)
  /-- 単位の保存 [1] = X。 -/
  map_one : bracket ((zpRing p).one) = psX (zpRing p)
  /-- F-加法 F([a]X, [b]X) = [a+b]X。 -/
  map_add : ∀ a b,
      ps21Comp (zpRing p) (lt2Sol p hp) (bracket a) (bracket b)
        = bracket ((zpRing p).add a b)
  /-- 合成乗法 [a]∘[b] = [ab]。 -/
  map_mul : ∀ a b, psComp (zpRing p) (bracket a) (bracket b)
      = bracket ((zpRing p).mul a b)

/-- **M76F-2: witness** — ltSol 族が O-加群インターフェースを
    完全証明で充足（M76 の諸定理の組み立てのみ・公理化なし）。 -/
def ltOModule (p : Nat) (hp : IsPrime p) : FormalOModuleData p hp where
  bracket := ltSol p hp
  bracket_coeff_zero := fun _ => rfl
  bracket_coeff_one := fun _ => rfl
  bracket_comm := ltSol_comm p hp
  map_zero := ltSol_zero p hp
  map_one := ltSol_one p hp
  map_add := lt_module_add p hp
  map_mul := lt_module_mul p hp

/-! ## 単射性と剛性 -/

/-- **M76F-3: a ↦ [a] は単射** — 一次係数の読み出し
    （ltSol p hp a 1 = a は定義的等式）。 -/
theorem ltSol_injective (p : Nat) (hp : IsPrime p)
    (a b : (Zp p).carrier) (h : ltSol p hp a = ltSol p hp b) :
    a = b :=
  congrFun h 1

/-- **M76F-4: 剛性（本丸）** — インターフェースの任意の witness D は
    bracket = ltSol を満たす。f との可換性と f∘G の崩落（M72F）から
    各 D.bracket a が LT 方程式を満たし、一意性（M49）で同定。 -/
theorem oModule_bracket_unique (p : Nat) (hp : IsPrime p)
    (D : FormalOModuleData p hp) :
    ∀ a, D.bracket a = ltSol p hp a := by
  intro a
  have heq : psComp (zpRing p) (D.bracket a) (ltPoly p)
      = (psRing (zpRing p)).add
          (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int))
            (D.bracket a))
          (psPow (zpRing p) (D.bracket a) p) :=
    (D.bracket_comm a).trans
      (psComp_ltPoly_left p hp.1 (D.bracket a) (D.bracket_coeff_zero a))
  obtain ⟨W, _, huniq⟩ := lubin_tate p hp a
  exact huniq (D.bracket a) (D.bracket_coeff_zero a)
    (D.bracket_coeff_one a) heq

/-- **M76F-5a: witness の一意性** — 任意の二つの witness は
    同じ bracket を持つ（剛性 ×2）。 -/
theorem oModule_unique (p : Nat) (hp : IsPrime p)
    (D D' : FormalOModuleData p hp) : D.bracket = D'.bracket := by
  funext a
  rw [oModule_bracket_unique p hp D a, oModule_bracket_unique p hp D' a]

/-- **M76F-5b: 一般の逆元（インターフェース語彙）** —
    F([a]X, [−a]X) = 0（M76-5a の言い換え）。 -/
theorem ltOModule_inverse (p : Nat) (hp : IsPrime p)
    (a : (Zp p).carrier) :
    ps21Comp (zpRing p) (lt2Sol p hp) ((ltOModule p hp).bracket a)
      ((ltOModule p hp).bracket ((zpRing p).neg a))
      = psZero (zpRing p) :=
  lt_module_add_neg p hp a

end IUT
