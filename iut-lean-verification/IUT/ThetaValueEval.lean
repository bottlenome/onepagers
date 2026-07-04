/-
  IUT/ThetaValueEval.lean — M209F: テータ値評価の l⋇ ラベリング（柱E・並行部品）

  柱E 残課題 E-1（#39）の「M4 のテータ値 q^{j²} を ±/l⋇ ラベリング
  （M162F）へ接続する **値の簿記側**」切片。M4（Evaluation.lean）は
  Gaussian monoid の**次数**簿記（sumDeg = Σj²·d）を、M9-7
  （FundamentalGroup.lean `theta_exponent_unique`）はテータ値の指数が
  自動形式性の差分方程式 F(j+1) = F(j) + 2j + 1, F(0) = 0 から F(j) = j²
  と**強制**されることを与えていた。本モジュールはこの値指数簿記を
  一つの対象 `thetaValExp j = j²`（テータ値 q^{j²} の q-指数）として
  切り出し、

    (1) それが差分方程式の**唯一**の解であること（q^{j²} の強制、M9-7）、
    (2) 指数 j² が ±1 作用 j ↦ negMod l j = l−j の下で mod l で
        well-defined であること（(l−j)² ≡ j² mod l、M4-7
        `theta_value_pm_symmetry`）、
    (3) さらに **±1 商 |F_l| のラベル orbitRep（M2）の上で値指数が
        mod l で well-defined** であること（軌道が一致すれば値指数が
        合同、M2-6 `orbitRep_eq_iff` + M4-7）——テータ値 q^{1²},…,q^{l⋇²}
        がちょうど {±1}-軌道ラベル {1,…,l⋇} で添字付けられることの
        値論的内容、
    (4) 値指数 (j+1)² が隣接 Gaussian 座席 tri j + tri(j+1)（M92/M143F）
        に一致すること（テータ値 q^{j²} と Heisenberg 中心 q^{tri j} の
        換算の値側）

    を機械検証し、非単位 {±1}-軌道ラベルがちょうど l⋇ = (l−1)/2 個
    （M2-7 `theta_labels`）であることと束ねる。

  意義: M4 のテータ値 q^{j²}（GaussianEvaluation の値）と M162F の
  ±/l⋇ ラベリング（μ_l 側の反転軌道 = orbitRep 分類）を、**値の指数
  簿記が {±1}-軌道ラベル上で mod l well-defined**という定理で接続する。
  M162F/M190F が μ_l(O) 側・解析側（関数等式）でラベル入替 j ↔ l−j を
  実現していたのに対し、本モジュールは M4 の**値 q^{j²} そのもの**の
  指数簿記が同じ ± 同一視の下で（q^l の冪を除いて）不変であることを
  与える——E-1 チェーンの値簿記側の離散核。

  正直な限定（スライス A + 値↔ラベル well-defined）: 扱うのは値の
  **指数簿記 j²** と、その ±1/orbitRep 作用下の mod l well-defined 性、
  および Gaussian 座席 tri との換算のみ。ラベル {1,…,l⋇} への**単射性
  （相異なるラベルが相異なるテータ値を与える, mod l）**は l の素数性
  （Euclid 補題）を要し未形式化——本層は値指数が軌道ラベル上で
  well-defined（軌道が一致すれば合同）である向きのみを閉じる。完全な
  評価同型（エタールテータ関数値の構成）、ガロア同変な p 進テータ値、
  tempered π₁ の商としての実現も未形式化（E-1 残）。値指数簿記は
  q の指数（整数）としてのみ扱い、q-冪そのものの因子論・付値は未形式化。
  全て選択公理不使用（M9-7/M4-7/M2 から継承、新規 Classical なし）。
  サブエージェント並行部品。
-/
import IUT.Evaluation
import IUT.FundamentalGroup
import IUT.HodgeTheater
import IUT.TriSquare

namespace IUT

/-! ## M209F-1: テータ値の指数簿記 q^{j²} とその強制 -/

/-- **M209F-1a: テータ値の q-指数** — `thetaValExp j = j²`。
    l-等分点ラベル j で評価したテータ値 q^{j²}（IUT III p.161 の
    表示 {q^{j²}}）の q の指数部分。 -/
def thetaValExp (j : Int) : Int := j * j

/-- **定理 (M209F-1b): 基点** — F(0) = 0（q^{0²} = q^0 = 1）。 -/
theorem thetaValExp_zero : thetaValExp 0 = 0 := by
  show (0 : Int) * 0 = 0
  omega

/-- **定理 (M209F-1c): 自動形式性の差分方程式** —
    F(j+1) = F(j) + 2j + 1（デッキ移動 j ↦ j+1 で零点位数が 2j+1
    増える、M9-7 の差分方程式そのもの）。M9-8 `sq_succ` による。 -/
theorem thetaValExp_rec (j : Int) :
    thetaValExp (j + 1) = thetaValExp j + 2 * j + 1 := by
  show (j + 1) * (j + 1) = j * j + 2 * j + 1
  exact sq_succ j

/-- **定理 (M209F-1d): q^{j²} の強制（M9-7 の値側適用）** — 差分方程式
    F(j+1) = F(j) + 2j + 1, F(0) = 0 を満たす簿記 F は `thetaValExp`
    （= j²）ただ一つ。テータ値が**二次**の指数 q^{j²} を持つことが
    評価理論から強制される。M9-7 `theta_exponent_unique` の値簿記
    としての言い直し。 -/
theorem thetaValExp_unique (F : Int → Int) (h0 : F 0 = 0)
    (hrec : ∀ j : Int, F (j + 1) = F j + 2 * j + 1) :
    ∀ j : Int, F j = thetaValExp j :=
  theta_exponent_unique F h0 hrec

/-! ## M209F-2: 値指数の ± well-defined 性（mod l） -/

/-- **定理 (M209F-2a): 値指数の ±対称性（mod l）** — q^{(l−j)²} と
    q^{j²} は q^l の冪を除いて一致する: (l−j)² = j² + l·k。M4-7
    `theta_value_mod`（= `theta_value_pm_symmetry`）の値指数簿記形。
    テータ値が {±1} 反転 j ↦ l−j の下で q^l を法に well-defined。 -/
theorem thetaValExp_pm_mod (l j : Int) :
    ∃ k : Int, thetaValExp (l - j) = thetaValExp j + l * k :=
  theta_value_mod l j

/-- **定理 (M209F-2b): 値指数は {±1}-軌道ラベルの上で well-defined
    （本丸）** — j, j' < l で ±1 商ラベルが一致（orbitRep l j =
    orbitRep l j'、M2）なら値指数は mod l で合同:
    (j')² = j² + l·k。M2-6 `orbitRep_eq_iff` で j' ∈ {j, negMod l j}
    に分解し、negMod 側は M4-7 `theta_value_pm_symmetry`。テータ値
    q^{j²} が |F_l| = F_l/{±1} のラベル上で（q^l を除いて）well-defined
    ——テータ値 q^{1²},…,q^{l⋇²} がちょうど {±1}-軌道ラベル {1,…,l⋇}
    で添字付けられることの値論的内容。 -/
theorem thetaValExp_orbit_mod (l L j j' : Nat) (hodd : l = 2 * L + 1)
    (hj : j < l) (hj' : j' < l) (h : orbitRep l j = orbitRep l j') :
    ∃ k : Int, thetaValExp (j' : Int) = thetaValExp (j : Int) + (l : Int) * k := by
  cases (orbitRep_eq_iff hodd hj hj').mp h with
  | inl heq =>
    -- 同一ラベル: j' = j
    refine ⟨0, ?_⟩
    rw [heq, Int.mul_zero, Int.add_zero]
  | inr heq =>
    -- 反転ラベル: j' = negMod l j
    cases Nat.eq_zero_or_pos j with
    | inl h0 =>
      have hnj : negMod l j = 0 := by
        unfold negMod
        rw [if_pos h0]
      refine ⟨0, ?_⟩
      rw [heq, hnj, h0, Int.mul_zero, Int.add_zero]
    | inr hpos =>
      have hnj : negMod l j = l - j := by
        unfold negMod
        rw [if_neg (by omega)]
      refine ⟨(l : Int) - 2 * (j : Int), ?_⟩
      rw [heq, hnj]
      have hcast : ((l - j : Nat) : Int) = (l : Int) - (j : Int) := by omega
      show thetaValExp ((l - j : Nat) : Int)
        = thetaValExp (j : Int) + (l : Int) * ((l : Int) - 2 * (j : Int))
      rw [hcast]
      show ((l : Int) - (j : Int)) * ((l : Int) - (j : Int))
        = (j : Int) * (j : Int) + (l : Int) * ((l : Int) - 2 * (j : Int))
      exact theta_value_pm_symmetry (l : Int) (j : Int)

/-! ## M209F-3: 値指数 = 隣接 Gaussian 座席（tri との換算） -/

/-- **定理 (M209F-3): 値指数 (j+1)² = 隣接 Gaussian 座席の和** —
    テータ値の q-指数 (j+1)² は隣接する Heisenberg 中心成分（ガウス
    座席）tri j + tri(j+1) の和に一致する（M143F `tri_adjacent_sq` の
    値指数形）。テータ値 q^{j²} 正規化と q^{tri j} 座席の換算の値側。 -/
theorem thetaValExp_tri (j : Nat) :
    thetaValExp ((j : Int) + 1)
      = ((tri j : Nat) : Int) + ((tri (j + 1) : Nat) : Int) := by
  show ((j : Int) + 1) * ((j : Int) + 1)
    = ((tri j : Nat) : Int) + ((tri (j + 1) : Nat) : Int)
  have h := tri_adjacent_sq j
  have hc : (((tri j + tri (j + 1) : Nat)) : Int)
      = ((tri j : Nat) : Int) + ((tri (j + 1) : Nat) : Int) := by
    rw [Int.natCast_add]
  rw [← hc, h]
  have hc2 : ((((j + 1) * (j + 1) : Nat)) : Int)
      = ((j : Int) + 1) * ((j : Int) + 1) := by
    rw [Int.natCast_mul]
    have hj1 : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
    rw [hj1]
  rw [hc2]

/-! ## M209F-4: 総括レコード -/

/-- **M209F-4a: テータ値評価の l⋇ ラベリングデータ** — テータ値指数
    q^{j²} の基点・差分方程式・強制（一意性）、± / orbitRep 軌道
    ラベルの上での mod l well-defined 性、Gaussian 座席 tri との換算、
    非単位 {±1}-軌道ラベルがちょうど {1,…,l⋇}（l⋇ = (l−1)/2）である
    ことの一括束ね。E-1 の値簿記側 witness。 -/
structure ThetaValueEvalData (l L : Nat) (hodd : l = 2 * L + 1) where
  /-- 基点: F(0) = 0（q^{0²} = 1）。 -/
  val_zero : thetaValExp 0 = 0
  /-- 差分方程式 F(j+1) = F(j) + 2j + 1（自動形式性、M9-7）。 -/
  val_rec : ∀ j : Int, thetaValExp (j + 1) = thetaValExp j + 2 * j + 1
  /-- q^{j²} の強制: 差分方程式の解は thetaValExp（= j²）ただ一つ。 -/
  val_forced : ∀ (F : Int → Int), F 0 = 0 →
    (∀ j : Int, F (j + 1) = F j + 2 * j + 1) → ∀ j : Int, F j = thetaValExp j
  /-- ± well-defined（mod l）: (l−j)² ≡ j² (mod l)。 -/
  val_pm : ∀ j : Int,
    ∃ k : Int, thetaValExp ((l : Int) - j) = thetaValExp j + (l : Int) * k
  /-- {±1}-軌道ラベルの上で well-defined: 軌道一致 ⟹ 値指数合同（mod l）。 -/
  val_orbit : ∀ j j' : Nat, j < l → j' < l → orbitRep l j = orbitRep l j' →
    ∃ k : Int, thetaValExp (j' : Int) = thetaValExp (j : Int) + (l : Int) * k
  /-- Gaussian 座席との換算: (j+1)² = tri j + tri(j+1)。 -/
  val_tri : ∀ j : Nat, thetaValExp ((j : Int) + 1)
    = ((tri j : Nat) : Int) + ((tri (j + 1) : Nat) : Int)
  /-- 非単位ラベルの範囲: 1 ≤ orbitRep l j ≤ l⋇（テータ値の添字集合）。 -/
  label_range : ∀ j, j < l → j ≠ 0 → 1 ≤ orbitRep l j ∧ orbitRep l j ≤ L
  /-- 切断: 各 k ∈ {1,…,l⋇} は非零ラベル j で実現される。 -/
  label_section : ∀ k, 1 ≤ k → k ≤ L → ∃ j, j < l ∧ j ≠ 0 ∧ orbitRep l j = k

/-- **M209F-4b: witness 本体** — 全フィールドを M209F-1〜3 と M2-7
    `theta_labels` で埋める。 -/
def thetaValueEvalData (l L : Nat) (hodd : l = 2 * L + 1) :
    ThetaValueEvalData l L hodd where
  val_zero := thetaValExp_zero
  val_rec := thetaValExp_rec
  val_forced := thetaValExp_unique
  val_pm := fun j => thetaValExp_pm_mod (l : Int) j
  val_orbit := fun j j' hj hj' h => thetaValExp_orbit_mod l L j j' hodd hj hj' h
  val_tri := thetaValExp_tri
  label_range := (theta_labels hodd).1
  label_section := (theta_labels hodd).2

/-- **定理 (M209F-4c): テータ値評価データの存在（M209F 見出し）** —
    l = 2l⋇+1 なら値評価の l⋇ ラベリングデータが存在する。テータ値
    q^{j²}（M4）が ±/l⋇ ラベリング（M162F）と値簿記の水準で両立する。 -/
theorem thetaValueEval_exists (l L : Nat) (hodd : l = 2 * L + 1) :
    Nonempty (ThetaValueEvalData l L hodd) :=
  ⟨thetaValueEvalData l L hodd⟩

end IUT
