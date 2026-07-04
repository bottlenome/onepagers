/-
# M174: 三角不等式と埋め込みの順序保存（柱C）

M173（順序ブリッジ rLe_of_seq_le と絶対値の片側支配）の直上。実数の
**三角不等式** |x + y| ≤ |x| + |y| を rLe（非厳密順序）として閉じ、
また有理数埋め込み qToReal が順序を保つこと（qLe ⟹ rLe）を示す。
どちらも M173 の rLe_of_seq_le で点ごとの ℚ 不等式から直に持ち上がる。

  * M174-1 **`rabs_triangle`** — 三角不等式 |x + y| ≤ |x| + |y|
    （M127F rabs_add_le を rLe_of_seq_le で持ち上げ）
  * M174-2 `rLe_qToReal` — 埋め込みの順序保存 qLe a b ⟹ rLe q↑ p↑
    （定数列なので各項が仮定そのもの）
  * M174-3 `RealAbsTriangleData` — 総括

意義: 三角不等式は絶対収束・級数評価・距離の劣加法性の要。M173 の
片側支配（x ≤ |x| 等）と併せ、絶対値の順序論の中核が揃う。埋め込みの
順序保存は「ℚ の順序が ℝ の順序に忠実に移る」ことで、具体的な数値
評価（有理数の不等式）を実数の rLe に翻訳する橋。

正直な限定: 逆三角不等式（||x| − |y|| ≤ |x − y|）・狭義 rLt 版・
級数への一般化（有限和の三角不等式）は次層。本層は二項の三角不等式と
埋め込み単調性のみ。

全て選択公理不使用。
-/
import IUT.RealAbsLe

namespace IUT

/-! ## M174-1: 三角不等式 -/

/-- **定理 (M174-1): 三角不等式** — |x + y| ≤ |x| + |y|。
    M127F rabs_add_le（点ごと |x+y|_n ≤ (|x|+|y|)_n）を M173
    rLe_of_seq_le で rLe に持ち上げる。 -/
theorem rabs_triangle (x y : RReal) :
    rLe (rabs (realAdd x y)) (realAdd (rabs x) (rabs y)) :=
  rLe_of_seq_le (rabs_add_le x y)

/-! ## M174-2: 埋め込みの順序保存 -/

/-- **定理 (M174-2): 埋め込みの順序保存** — qLe a b なら rLe a↑ b↑。
    qToReal は定数列なので各項が仮定 h そのもの。ℚ の不等式を ℝ の
    rLe に翻訳する橋。 -/
theorem rLe_qToReal {a b : QRat} (h : qLe a b) :
    rLe (qToReal a) (qToReal b) :=
  rLe_of_seq_le (fun _ => h)

/-! ## M174-3: 総括 -/

/-- **M174-3a: 総括** — 三角不等式・埋め込み順序保存データ。 -/
structure RealAbsTriangleData where
  /-- 三角不等式 |x + y| ≤ |x| + |y|。 -/
  triangle : ∀ x y : RReal,
    rLe (rabs (realAdd x y)) (realAdd (rabs x) (rabs y))
  /-- 埋め込みの順序保存。 -/
  embed_le : ∀ {a b : QRat}, qLe a b → rLe (qToReal a) (qToReal b)

/-- **M174-3b: witness**。 -/
def realAbsTriangleData : RealAbsTriangleData where
  triangle := rabs_triangle
  embed_le := fun h => rLe_qToReal h

/-- **M174-3c: 存在**。 -/
theorem realAbsTriangle_exists : Nonempty RealAbsTriangleData :=
  ⟨realAbsTriangleData⟩

end IUT
