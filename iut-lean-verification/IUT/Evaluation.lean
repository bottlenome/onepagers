/-
  IUT/Evaluation.lean — M4（IUT II: Hodge–Arakelov 的評価）の形式化

  IUT II（特に Cor 3.5–3.6 の Gaussian monoids）の評価理論のうち、
  **値と次数の簿記層** を形式化する。

  評価理論の内容: エタールテータ関数を l-等分点（ラベル
  j ∈ F_l⋇ = {1, …, l⋇}）で評価すると、値はテータ値
      q^{1²}, q^{2²}, …, q^{l⋇²}
  になる（IUT III p.161 の表示 {q^{j²}}_{j=1,…,l⋇} を参照）。
  これらを束ねた Gaussian monoid の「次数」（q の指数の総和）と
  procession 正規化平均が、系3.12 の両辺の数値を決定する。

  形式化する定理:
  * M4-1 `sumDeg_eq` — Gaussian 分布の総次数 Σ_{j=1}^{l⋇} j²·d が
    閉形式 (Σj²)·d に一致する（評価の次数簿記）
  * M4-2 `gaussian_eval_strict` — Gaussian 値の素朴な（不定性に
    よる膨張なしの）読みは、M5 の「厳密テータ評価」仮定と一致する
  * M4-3 `gaussian_obstruction` — したがって素朴な Gaussian 評価は
    多輻的表現と両立しない（M4 → M5-2 の接続。Scholze–Stix の
    「Θ-link は q ↦ q^{j²} に過ぎない」という読みが、評価理論の
    値の簿記から直接障害を生むことの機械検証）
  * M4-4 `strict_gives_rceval` — 厳密評価の平均化恒等式は
    RC 評価（RCEval、S2 の前提）をそのまま導く（M4 → S2 の接続）
  * M4-5 `mkComputation` — 逆に不定性込みの（膨張を許す）評価
    上界からは M7 の体積計算インターフェースが構成される
    （M4 → M7 の接続）

  未形式化: エタールテータ関数そのものの構成と剛性（mono-theta
  環境の cyclotomic rigidity、[EtTh] の理論）、ガロア評価の
  遠アーベル的正当化。これらは評価の「値がなぜ q^{j²} になるか」
  の証明にあたり、M5 の構成問題と同根である。
-/
import IUT.Skeleton
import IUT.Arithmetic
import IUT.Multiradial

namespace IUT

/-- Gaussian 分布の総次数: `sumDeg L d = Σ_{j=1}^{L} j²·d`。
    テータ値 q^{j²}（j = 1, …, L）の次数 j²·deg(q) の総和。 -/
def sumDeg (L : Nat) (d : Int) : Int :=
  match L with
  | 0 => 0
  | n + 1 => sumDeg n d + ((n + 1) * (n + 1) : Nat) * d

/-- **定理 (M4-1): 評価の次数簿記** — Gaussian 分布の総次数は
    閉形式 (Σj²)·d に一致する。 -/
theorem sumDeg_eq (L : Nat) (d : Int) : sumDeg L d = (sumSq L : Int) * d := by
  induction L with
  | zero => simp [sumDeg, sumSq]
  | succ n ih =>
    show sumDeg n d + ((n + 1) * (n + 1) : Nat) * d = ((sumSq (n + 1) : Nat) : Int) * d
    rw [ih, sumSq_succ, Int.natCast_add, Int.add_mul]

/-- 検算: l = 5（l⋇ = 2）のとき総次数 = 5·d = (1² + 2²)·d。 -/
example (d : Int) : sumDeg 2 d = 5 * d := by
  rw [sumDeg_eq]; rfl

/-- **Gaussian 評価**（素朴な読み）: 多輻的表現の各可能な像の
    procession 正規化体積が、テータ値の次数簿記そのまま
    −Σ_{j} j²·|log q| / l⋇ に一致するという仮定。 -/
def GaussianEvaluation {V : VolumeTheory} {s : Skeleton}
    (M : MultiradialRep V s) : Prop :=
  ∀ i, (s.lstar : Int) * V.vol (M.image i) = -sumDeg s.lstar s.logq

/-- **定理 (M4-2)**: Gaussian 評価は M5 の厳密テータ評価に一致する
    （評価理論の値の簿記が `StrictEvaluation` の起源であることの
    形式化）。 -/
theorem gaussian_eval_strict {V : VolumeTheory} {s : Skeleton}
    {M : MultiradialRep V s} (h : GaussianEvaluation M) :
    StrictEvaluation M := by
  intro i
  rw [Int.neg_mul]
  have := h i
  rw [sumDeg_eq] at this
  omega

/-- **定理 (M4-3): Gaussian 障害** — 素朴な Gaussian 評価は
    多輻的表現の出力仕様と両立しない（M4 の値の簿記から
    Scholze–Stix 型の障害が直接従う）。 -/
theorem gaussian_obstruction {V : VolumeTheory} {s : Skeleton}
    (M : MultiradialRep V s) (h : GaussianEvaluation M) : False :=
  strict_evaluation_obstruction M (gaussian_eval_strict h)

/-- **定理 (M4-4)**: 厳密評価の平均化恒等式
    l⋇·|log Θ| = Σj²·|log q| は RC 評価（ScholzeStix.lean の
    `RCEval`、退化定理 S2 の前提）をそのまま導く。 -/
theorem strict_gives_rceval (s : Skeleton)
    (heval : (s.lstar : Int) * s.logTheta = (sumSq s.lstar : Int) * s.logq) :
    RCEval s :=
  Int.le_of_eq heval.symm

/-- **定理 (M4-5)**: 不定性込みの（膨張を許す）評価上界
    |log Θ| ≥ a·|log q| − err からは、M7 の体積計算
    インターフェースが構成される。
    （素朴評価は S2 の矛盾へ、膨張込み評価は M7 の Szpiro 型
    導出へ——どちらに転ぶかが「不定性の体積コスト」で決まる、
    という論争の構図そのものの形式化。） -/
def mkComputation (s : Skeleton) (a err : Int)
    (ha : a ≥ 2) (herr : err ≥ 0)
    (hbound : s.logTheta ≥ a * s.logq - err) : LogVolumeComputation s :=
  { a := a, err := err, ha := ha, herr := herr, bound := hbound }

/-- **整合性 (M4-6)**: 膨張込み評価は充足可能（モデル検証）。
    `computation_consistent`（M7-3）と合わせて、評価理論の
    両側の読みのうち矛盾を生むのは素朴側のみであることを確認。 -/
theorem padded_evaluation_consistent :
    ∃ (s : Skeleton) (comp : LogVolumeComputation s), True :=
  ⟨{ lstar := 2, hl := by omega, logq := 1, hq := by omega, logTheta := 1 },
   mkComputation _ 2 1 (by omega) (by omega) (show (1 : Int) ≥ 2 * 1 - 1 by omega),
   trivial⟩

end IUT
