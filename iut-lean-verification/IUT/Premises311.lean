/-
  IUT/Premises311.lean — M97（定理3.11 の前提インターフェース: 柱D 入口）

  柱D（定理3.11 = 多輻的表現アルゴリズム）の**前提の束**を構成する。
  issue の全体計画 D ← {A, B, C, E} のうち、本キャンペーン
  （M72〜M96F）が choice-free で建設した柱B・柱E の総括 witness を
  一つの構造体 Theorem311Premises に束ね、M5 の定理3.11
  インターフェース（MultiradialRep）→ 系3.12 → Szpiro 型不等式の
  既存パイプラインに接続する。

  **実接続（本層の発見）**: M1 の sumSq（系3.12 骨格のテータ値
  Σj² 簿記、M5-2 の厳密評価障害定理で使用中）と M93 の ssq は
  **同一の再帰**である（ssq_eq_sumSq は帰納 + rfl 一発）。これに
  より E8 の閉形式 **6·Σj² = l(l+1)(2l+1)** と離散下界
  **l³ ≤ 3·Σj²** が、定理3.11 の体積側ステートメント
  （StrictEvaluation の Σj² 係数）にそのまま接続される——
  キャンペーン最初期（M1）と最新（M93）の輪が閉じた。

  * M97-1 `ssq_eq_sumSq` — **M1 ↔ M93 の同定**（輪の接続）
  * M97-2 `sumSq_closed` / `cube_le_sumSq` / `sumSq_tri_stri` —
    sumSq 側へ移送された閉形式・下界・三角数橋
  * M97-3 `Theorem311Premises` — **前提の束（柱B + 柱E の総括）**
  * M97-4 `theorem311Premises` / `premises_exist` — witness
  * M97-5 `premises_then_szpiro` — 既存パイプラインへの接続の再確認

  正直申告: **MultiradialRep の充足（= 定理3.11 の構成本体）が
  柱D の本丸であり未形式化**。柱A（SGA1）の総括 witness 群は
  プロジェクト初期に検証済みだが意図的 Classical 22 に属するため
  choice-free の本束には含めない（依存はここに明記）。柱C
  （Frobenioid）の pilot 分割定理群（mixed_pilot_division 等）は
  choice-free 検証済み（M5x〜M6x 帯）。全て選択公理不使用。
-/
import IUT.Multiradial
import IUT.GaussianVolume
import IUT.RecGluing
import IUT.EisDomain2
import IUT.EisEndoRigidity

namespace IUT

/-! ## M1 ↔ M93 の同定（輪の接続） -/

/-- **定理 (M97-1): ssq = sumSq** — M93 のガウス体積簿記と
    M1 の系3.12 骨格のテータ値簿記は同一の関数。 -/
theorem ssq_eq_sumSq : ∀ l, ssq l = sumSq l := by
  intro l
  induction l with
  | zero => rfl
  | succ l ih =>
    show ssq l + (l + 1) * (l + 1) = sumSq l + (l + 1) * (l + 1)
    rw [ih]

/-- **M97-2a: sumSq の閉形式**（M93 の移送）— 6·Σj² = l(l+1)(2l+1)。
    M5-2（厳密評価の障害）の Σj² 係数に対する閉形式。 -/
theorem sumSq_closed (l : Nat) :
    6 * sumSq l = l * (l + 1) * (2 * l + 1) := by
  rw [← ssq_eq_sumSq]
  exact ssq_closed l

/-- **M97-2b: sumSq の離散下界**（M93 の移送）— l³ ≤ 3·Σj²。 -/
theorem cube_le_sumSq (l : Nat) : l * l * l ≤ 3 * sumSq l := by
  rw [← ssq_eq_sumSq]
  exact cube_le_ssq l

/-- **M97-2c: 三角数橋の移送** — Σj² + tri l = 2·Σtri。 -/
theorem sumSq_tri_stri (l : Nat) : sumSq l + tri l = 2 * stri l := by
  rw [← ssq_eq_sumSq]
  exact ssq_stri l

/-! ## 前提の束 -/

/-- **M97-3: 定理3.11 の前提インターフェース** — 本キャンペーンが
    choice-free で建設した柱B（分岐 LCFT の剛性骨格）と柱E
    （テータの実体化）の総括 witness の束。定理3.11 の充足
    （MultiradialRep の構成）に投入される入力の在庫一覧。 -/
structure Theorem311Premises where
  /-- 柱B: K^× 貼り合わせレベル 1（M94）。 -/
  lcft_gluing : ∀ p (hp : IsPrime p) (hodd : 3 ≤ p),
    Nonempty (RecGluingData p hp hodd)
  /-- 柱B: 捻れ塔 Λₙ の Galois 加群構造（M89F）。 -/
  torsion_tower : ∀ p (hp : IsPrime p) (hodd : 3 ≤ p),
    Nonempty (EisTorsionTowerData p hp hodd)
  /-- 柱B: O の witness 付き整域性（M93F+M96F）。 -/
  integrality : ∀ p (hp : IsPrime p) (h0 : 0 < p - 1),
    Nonempty (EisDomain2Data p hp h0)
  /-- 柱B: 自己同型の上界骨格（M95）。 -/
  endo_rigidity : ∀ p (hp : IsPrime p) (hD : NoZeroDiv (eisRing p)),
    Nonempty (EisEndoRigidityData p hp hD)
  /-- 柱E: mono-theta witness（M92 — 関数等式・Heisenberg 切断・
      cyclotomic rigidity・Tate 降下の束）。 -/
  mono_theta : Nonempty MonoThetaWitness
  /-- 柱E: ガウス体積簿記（M93）。 -/
  gauss_volume : Nonempty GaussianVolumeData
  /-- 体積側の接続: 定理3.11 の Σj² 簿記の閉形式。 -/
  theta_bookkeeping : ∀ l, 6 * sumSq l = l * (l + 1) * (2 * l + 1)
  /-- 体積側の接続: テータパイロット総次数の離散下界。 -/
  volume_lower : ∀ l, l * l * l ≤ 3 * sumSq l

/-- **M97-4a: witness 本体** — 全フィールドが本キャンペーンの
    総括定理で充足される。 -/
def theorem311Premises : Theorem311Premises where
  lcft_gluing := recGluing_exists
  torsion_tower := eisTorsionTower_exists
  integrality := eisDomain2_nonempty
  endo_rigidity := eisEndoRigidity_exists
  mono_theta := mono_theta_exists
  gauss_volume := gaussian_volume_exists
  theta_bookkeeping := sumSq_closed
  volume_lower := cube_le_sumSq

/-- **定理 (M97-4b): 前提の束の存在（見出し）**。 -/
theorem premises_exist : Nonempty Theorem311Premises :=
  ⟨theorem311Premises⟩

/-! ## 既存パイプラインへの接続 -/

/-- **定理 (M97-5): 前提 + 定理3.11 の充足 ⟹ Szpiro 型不等式** —
    M5-5 のパイプラインの再確認: 前提の束は揃った。残る本丸は
    MultiradialRep の充足（定理3.11 の構成そのもの）である。 -/
theorem premises_then_szpiro (_P : Theorem311Premises)
    {V : VolumeTheory} {s : Skeleton}
    (M : MultiradialRep V s) (comp : LogVolumeComputation s) :
    (comp.a - 1) * s.logq ≤ comp.err :=
  szpiro_of_multiradial M comp

end IUT
