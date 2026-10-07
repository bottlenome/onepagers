/-
# M143F: 平方・三角数の換算簿記 — 隣接ガウス座席の和 = 平方ラベル

柱E E-2 の局所形。[IUTchI] のテータ値ラベル q^{j²} と Heisenberg
中心成分（ガウス指数）q^{tri j} の換算簿記の**局所単位**を形式化する:
隣接する三角数の和 = 平方数、すなわち tri j + tri(j+1) = (j+1)²。
M132 の大域橋 Σj² + Σj = 2Σtri（ssq_stri）の局所版であり、M137F の
辞書（Φ(j) の中心成分 = tri j）と合わせて「平方ラベルは隣接ガウス
座席 2 つ分」という読みが機械検証される。

  * M143F-1 `tri_adjacent_sq` — **局所換算（本丸）**:
    tri j + tri(j+1) = (j+1)²。M137F のコサイクル
    tri(i+j) = tri i + tri j + ij（i = 1）と tri_nat の閉形式による
  * M143F-2 `tri_adjacent_sq_real` — 局所換算の実数形（realEq、
    M132 natToReal_add による持ち上げ）
  * M143F-3 `ssq_stri_split` — 大域形（六角数分割）:
    Σ_{j≤l+1} j² = stri(l+1) + stri l — 平方和が隣接四面体数
    2 つに割れる（局所換算の総和形）
  * M143F-4 `ssq_stri_split_real` — 大域形の実数化
  * M143F-5 `dict_adjacent_centers` — **M137F 辞書との接続**:
    Φ(j) と Φ(j+1) の中心成分の和 = 平方ラベル (j+1)²
    （section_gauss_component + 局所換算の合成）
  * M143F-6 `TriSquareData` / `triSquareData` / `triSquare_exists` —
    総括 witness

意義: [IUTchI] の q^{j²} 正規化と q^{tri j} 座席の換算
（M132 ssq_stri の大域橋）の**局所単位** tri j + tri(j+1) = (j+1)²
を形式化し、M137F の Heisenberg 辞書の中心成分と接続。テータ値
ラベルの組合せ論核。

**形式化の範囲（正直な申告）**: 本層は換算簿記の Nat/ℝ 恒等式と
辞書接続のみ。q-冪そのもの（因子論・付値）での言い直しは M12 系の
因子構成と合流する将来層。全て選択公理不使用。サブエージェント
並行部品。
-/
import IUT.VolumeReal
import IUT.FuneqLift

namespace IUT

/-! ## M143F-1: 局所換算（本丸） — 隣接三角数の和 = 平方数 -/

/-- **定理 (M143F-1): 局所換算（本丸）** — tri j + tri(j+1) = (j+1)²。
    テータ値ラベル q^{(j+1)²} は隣接ガウス座席 q^{tri j}・q^{tri(j+1)}
    2 つ分。M137F のコサイクル tri(1+j) = tri 1 + tri j + j と
    tri_nat（2·tri j = j(j+1)）から。 -/
theorem tri_adjacent_sq (j : Nat) :
    tri j + tri (j + 1) = (j + 1) * (j + 1) := by
  have h1 : tri (j + 1) = tri j + (j + 1) := rfl
  -- 2·tri j = j(j+1) の閉形式
  have h2 := tri_nat j
  -- 積を原子 j*j の線形式へ
  have e1 : j * (j + 1) = j * j + j := Nat.mul_succ j j
  have e2 := sq_expand j
  omega

/-! ## M143F-2: 局所換算の実数形 -/

/-- **定理 (M143F-2): 局所換算の実数形** —
    tri j + tri(j+1) = (j+1)²（realEq、M132 natToReal_add による）。 -/
theorem tri_adjacent_sq_real (j : Nat) :
    realEq (realAdd (natToReal (tri j)) (natToReal (tri (j + 1))))
      (natToReal ((j + 1) * (j + 1))) := by
  have h := natToReal_add (tri j) (tri (j + 1))
  rw [tri_adjacent_sq j] at h
  exact h

/-! ## M143F-3: 大域形（六角数分割） -/

/-- **定理 (M143F-3): 大域形（六角数分割）** —
    Σ_{j≤l+1} j² = stri(l+1) + stri l。平方和が隣接四面体数 2 つに
    割れる: 局所換算 tri j + tri(j+1) = (j+1)² の j = 0, …, l に
    わたる総和形。M132 の総和橋 ssq + tri = 2·stri と整合する
    もう一つの大域読み。 -/
theorem ssq_stri_split : ∀ l, ssq (l + 1) = stri (l + 1) + stri l := by
  intro l
  induction l with
  | zero => rfl
  | succ l ih =>
    show ssq (l + 2) = stri (l + 2) + stri (l + 1)
    have h1 : ssq (l + 2) = ssq (l + 1) + (l + 2) * (l + 2) := rfl
    have h2 : stri (l + 2) = stri (l + 1) + tri (l + 2) := rfl
    have h3 : stri (l + 1) = stri l + tri (l + 1) := rfl
    -- 平方項を局所換算で隣接三角数 2 つに割る（l+1+1 = l+2 は defeq）
    have h4 : tri (l + 1) + tri (l + 2) = (l + 2) * (l + 2) :=
      tri_adjacent_sq (l + 1)
    rw [h1, ← h4]
    omega

/-! ## M143F-4: 大域形の実数化 -/

/-- **定理 (M143F-4): 大域形の実数化** —
    Σj² = stri(l+1) + stri l（realEq）。 -/
theorem ssq_stri_split_real (l : Nat) :
    realEq (natToReal (ssq (l + 1)))
      (realAdd (natToReal (stri (l + 1))) (natToReal (stri l))) := by
  have h := natToReal_add (stri (l + 1)) (stri l)
  rw [← ssq_stri_split l] at h
  exact realEq_symm h

/-! ## M143F-5: M137F 辞書との接続 -/

/-- **定理 (M143F-5): 辞書接続** — Φ(j) と Φ(j+1) の Heisenberg
    中心成分の和 = 平方ラベル (j+1)²。M137F の
    section_gauss_component（Φ(j).2.2 = tri j）と局所換算
    tri_adjacent_sq の合成: 「平方ラベルは隣接ガウス座席 2 つ分」の
    群側の読み。 -/
theorem dict_adjacent_centers (j : Nat) :
    (thetaSection j).2.2 + (thetaSection (j + 1)).2.2
      = (((j + 1) * (j + 1) : Nat) : Int) := by
  rw [section_gauss_component j, section_gauss_component (j + 1),
    ← tri_adjacent_sq j]
  omega

/-! ## M143F-6: 総括 witness -/

/-- **M143F-6a: 平方・三角数換算簿記の総括** — 局所換算（Nat/ℝ）・
    大域分割（Nat/ℝ）・辞書接続を一束に。 -/
structure TriSquareData where
  /-- 局所換算 tri j + tri(j+1) = (j+1)²。 -/
  local_conv : ∀ j, tri j + tri (j + 1) = (j + 1) * (j + 1)
  /-- 局所換算の実数形。 -/
  local_conv_real : ∀ j, realEq
    (realAdd (natToReal (tri j)) (natToReal (tri (j + 1))))
    (natToReal ((j + 1) * (j + 1)))
  /-- 大域分割 Σj² = stri(l+1) + stri l。 -/
  global_split : ∀ l, ssq (l + 1) = stri (l + 1) + stri l
  /-- 大域分割の実数形。 -/
  global_split_real : ∀ l, realEq (natToReal (ssq (l + 1)))
    (realAdd (natToReal (stri (l + 1))) (natToReal (stri l)))
  /-- 辞書接続: 隣接切断の中心成分の和 = 平方ラベル。 -/
  dict_centers : ∀ j,
    (thetaSection j).2.2 + (thetaSection (j + 1)).2.2
      = (((j + 1) * (j + 1) : Nat) : Int)

/-- **M143F-6b: witness 本体**。 -/
def triSquareData : TriSquareData where
  local_conv := tri_adjacent_sq
  local_conv_real := tri_adjacent_sq_real
  global_split := ssq_stri_split
  global_split_real := ssq_stri_split_real
  dict_centers := dict_adjacent_centers

/-- **定理 (M143F-6c): 換算簿記の存在（E-2 局所形の見出し）**。 -/
theorem triSquare_exists : Nonempty TriSquareData :=
  ⟨triSquareData⟩

end IUT
