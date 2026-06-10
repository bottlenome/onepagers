/-
  IUT/Diophantine.lean — M7（IUT IV: log-volume 計算 → Szpiro 型不等式）の形式化

  IUT IV §1–2（定理1.10）の **条件付き論理ステップ** を形式化する:

      系3.12（M6）＋ log-volume 計算（IUT IV §1 のインターフェース）
        ⟹ Szpiro 型の高さ不等式

  IUT IV の実際の構造:
  * 系3.12 は −|log(q)| ≤ −|log(Θ)| を与える
  * IUT IV §1 の明示計算は、多輻的表現の不定性込みの領域の体積を
    上から評価して
        −|log(Θ)| ≤ −a·|log(q)| + err
    の形の不等式を与える。ここで係数 a は素数 l と共に増大し
    （テータ値 q^{j²} の平均次数の効果。本プロジェクトの
    `sumSq_gt` が示す a > 1 の起源）、err は判別式・導手などの
    「コンダクター項」で抑えられる誤差である。
  * 両者を合成すると (a−1)·|log(q)| ≤ err、すなわち高さ |log(q)|
    がコンダクター項で抑えられる —— Szpiro 型不等式の形になる。
    （実際の IUT IV では l ≈ height^{1/2} と選んで ε 付きの
    Diophantine 不等式に整形する。）

  ここで証明するのはこの **合成ステップの論理的妥当性** である。
  log-volume 計算そのもの（インターフェースの中身）は M5 の
  多輻的表現に依存するため未形式化であり、本定理は徹頭徹尾
  「条件付き」である。すなわち:

      M7 は M6 と計算インターフェースから形式的に従う。
      よって IUT 全体の成否は M5（とそれを使う M6）に集約される
      —— 二分法定理（Verdict.lean）の結論を下流側から補強する。

  注意（Scholze–Stix との関係）: RC 同一視のもとでは「計算」は
  逆向きの不等式 lstar·|log(Θ)| ≥ sumSq·|log(q)|（RCEval）になり、
  系3.12 と合成すると Szpiro 型どころか矛盾が出る（ScholzeStix.lean
  の `ss_incompatible`）。本ファイルの計算インターフェースは
  望月の読み（多輻的表現の出力を上から評価する）に対応する。
-/
import IUT.Skeleton

namespace IUT

/-- **IUT IV §1 の log-volume 計算インターフェース**（公理化）:
    多輻的表現における Θ-パイロットの体積評価
        −|log(Θ)| ≤ −a·|log(q)| + err
    を `logTheta ≥ a · logq − err` の形で表す。
    係数 a ≥ 2（l と共に増大する平均次数効果）、err ≥ 0
    （コンダクター項）。中身の証明は M5 に属し未形式化。 -/
structure LogVolumeComputation (s : Skeleton) where
  /-- 平均次数係数（実際の IUT IV では l に比例して増大）。 -/
  a : Int
  /-- コンダクター項（判別式・導手・素点数で抑えられる誤差）。 -/
  err : Int
  ha : a ≥ 2
  herr : err ≥ 0
  /-- 体積評価: |log(Θ)| ≥ a·|log(q)| − err。 -/
  bound : s.logTheta ≥ a * s.logq - err

/-- **定理 (M7-1): 系3.12 ＋ log-volume 計算 ⟹ Szpiro 型不等式（精密版）**。

    系3.12（logTheta ≤ logq）と体積評価（logTheta ≥ a·logq − err）
    を合成すると (a−1)·|log(q)| ≤ err。係数 a が l と共に増大する
    ことを使うと、固定された err に対し |log(q)| の上界は a に
    反比例して締まる（IUT IV の l 最適化の出発点）。 -/
theorem szpiro_of_cor312_precise (s : Skeleton) (hcor : Cor312 s)
    (comp : LogVolumeComputation s) :
    (comp.a - 1) * s.logq ≤ comp.err := by
  -- 系3.12: logTheta ≤ logq
  have h1 : s.logTheta ≤ s.logq := by
    have := hcor; unfold Cor312 at this; omega
  -- 体積評価と合成: a·logq − err ≤ logq
  have h2 : comp.a * s.logq - comp.err ≤ s.logq :=
    Int.le_trans comp.bound h1
  -- (a−1)·logq = a·logq − logq（分配則）
  have h3 : (comp.a - 1) * s.logq = comp.a * s.logq - s.logq := by
    rw [Int.sub_mul, Int.one_mul]
  omega

/-- **系 (M7-2): 簡約版** — 高さ |log(q)| がコンダクター項 err で
    抑えられる: |log(q)| ≤ err（a−1 ≥ 1 と |log(q)| > 0 より）。

    これは「系3.12 さえ認めれば Diophantine 帰結への道は
    形式的に通る」ことの機械検証であり、論争の全重量が
    M5/M6 に載っていることを下流側から確認する。 -/
theorem szpiro_of_cor312 (s : Skeleton) (hcor : Cor312 s)
    (comp : LogVolumeComputation s) : s.logq ≤ comp.err := by
  have hp := szpiro_of_cor312_precise s hcor comp
  -- logq = 1·logq ≤ (a−1)·logq（a−1 ≥ 1, logq ≥ 0）
  have h3 : 1 * s.logq ≤ (comp.a - 1) * s.logq :=
    Int.mul_le_mul_of_nonneg_right (by have := comp.ha; omega) (Int.le_of_lt s.hq)
  rw [Int.one_mul] at h3
  exact Int.le_trans h3 hp

/-- **整合性チェック (M7-3)**: 計算インターフェースは系3.12 と
    両立する（SS 読みの RCEval と違って矛盾を生まない）。
    モデル: logq = 1, logTheta = 1, a = 2, err = 1 で
    系3.12（−1 ≥ −1）と体積評価（1 ≥ 2·1 − 1）が同時に成り立つ。 -/
theorem computation_consistent :
    ∃ s : Skeleton, ∃ _ : LogVolumeComputation s, Cor312 s :=
  ⟨{ lstar := 2, hl := by omega, logq := 1, hq := by omega, logTheta := 1 },
   { a := 2, err := 1, ha := by omega, herr := by omega,
     bound := show (1 : Int) ≥ 2 * 1 - 1 by omega },
   show (-1 : Int) ≥ -1 by omega⟩

end IUT
