/-
  IUT/ThetaJacobi.lean — M313F（テータの二次擬周期性:
  (qu)(q²u)·Θ(q,q²u) = Θ(q,u) / 柱E・テータ）

  分類: **[実]**（本物の先行建設 (b)）。
  complete_pct 影響: 柱E の実 IUT 完全証明率を **テータの高次
  擬周期性（second-order quasi-periodicity）**の側で前進させる。
  既存の柱E は実テータ級数 Θ(q,u)=Σ_n (−1)ⁿ q^{n(n+1)/2} uⁿ（M88,
  形式冪級数環 R[u^{±1}][[q]] 上の本物）・**一次**関数等式
  q·u·Θ(q,qu)=−Θ（M89, 作用素 T = (qu)·(u↦qu) で T(Θ)=−Θ）・
  反転対称性 J(Θ)=−Θ（M98）・テータ因子の原点通過 Θ(q,1)=0
  （M308F）まで本物で建設済みだが、**擬周期の反復（格子 q^ℤ に
  沿った二歩目）**は未着手だった。M308F は「因子全体が q^ℤ·(±1)
  軌道であること」を明示的に**後続**と正直申告している。本層は
  その二歩目へ本物で踏み込む:

    (1) **本物の対象**: 一次作用素 T = (qu)·(u↦qu) の**自乗** T² を
        単項式作用 uᵃqᵇ ↦ u^{a+2} q^{b+2a+3} として読み、Θ への
        作用の q^m 係数を **Θ 専用の有界台 Laurent 係数**
        （`thJacT2Rep`, choice なし）として直接定義する。累積擬周期
        因子は c₂(u) = (qu)·(q²u) = **q³·u²**（u-冪 +2・q-冪 +3）。
    (2) **本物の性質（本丸）**: **T²(Θ) = Θ**（`thJac_quasi_period2`）。
        すなわち (qu)(q²u)·Θ(q,q²u) = Θ(q,u)。各 q-次数 m・各 uᴺ
        係数で恒等式を閉じる。証明は再添字化 **n ↦ n−2** の一撃:
        二重三角橋 (N−2)(N−1) = N(N+1) − 4N + 2（`thJacBridge2`）が
        条件 2(m−(2N−1)) = (N−2)(N−1) ⟺ 2m = N(N+1) を与え、
        符号は isgn の周期2不変 isgn(N−2)=isgn(N)
        （`thJac_isgn_shift2`, isgn_succ 二回）、ガードは
        `thJacTri2_le`（2m=N(N+1) ⟹ 2N−1 ≤ m）で吸収。
        これは一次の T(Θ)=−Θ（M89）から作用素の線形性で機械的に
        従う式ではない——ここでは T は Θ 専用の係数公式でしか
        与えられておらず合成 T² が既製部品として無い——ので、
        **独立な二重畳み込みの係数計算として本物に閉じる**。

  * M313F-1 `thJacBridge2` / `thJacTri2_le` — 二重三角橋とガード
  * M313F-2 `thJac_isgn_shift2` — 符号の周期2不変 isgn(N−2)=isgn(N)
  * M313F-3 `thJacT2Rep` — T² = ((qu)·代入)² の Θ への作用の係数公式
    （bound は三角数の台 tri_bound で証明、choice なし）
  * M313F-4 `thJac_period_factor` — 擬周期因子の具体形（u-shift +2・
    q-degree drop 2N−1 = 因子 q³u² の読み）
  * M313F-5 `thJac_quasi_period2` / `thJac_quasi_period2_series` —
    **二次擬周期性（本丸, 係数レベル + 級数（Quot）レベル）**:
    T²(Θ) = Θ
  * M313F-6 `thJac_reflection_compat` — M98 反転対合との整合
    T²(Θ) = J²(Θ) = Θ
  * M313F-7 `ThetaJacobiData` / `thetaJacobiData` / `thJac_exists` —
    一次擬周期（M89）・二次擬周期（本層）・反転整合（M98）を束ねる
    総括レコードと存在

  **正直な限定（消去・弱化禁止）**:
  - 本層が本物にした M308F 後続は **擬周期の二歩目 T²(Θ)=Θ**
    （格子 q^ℤ に沿った二番目のシフト）まで。**任意 k 歩目
    Tᵏ(Θ)=(−1)ᵏΘ の一般形**・**因子全体が q^ℤ·(±1) 軌道である
    ことの完全形**は後続（k=1 は M89, k=2 が本層, 一般 k は帰納の
    次層）。
  - 擬周期性は**本物の Laurent 級数の係数比較**で（各 uᴺ 係数の
    等式）。無限和の収束は形式級数レベルで扱う（M88 と同精神）。
  - Jacobi 三重積 Θ=∏(1−qⁿ)(1+q^{n-1/2}u)(1+q^{n-1/2}u⁻¹) の積表示・
    three-rigidity・π₁^tp 上のエタールテータは後続。
  - toy 主語なし: 主語は本物の Θ（M88 の形式冪級数）と本物の
    二次作用素 T²（Θ 専用の有界台 Laurent 係数）であり、Bool 軌道・
    m202fVol・surrogate 群は一切用いない。

  全て選択公理不使用（純粋な有限台 Laurent 係数の計算）。
  サブエージェント新規1本（共有ファイル未変更）。一般名は
  `thJac` 接頭辞で衝突回避。
-/
import IUT.EtaleThetaReal

namespace IUT

/-! ## M313F-1: 二重三角橋とガード -/

/-- **M313F-1a: 二重三角橋** — (N−2)(N−1) = N(N+1) − 4N + 2。
    再添字化 n ↦ n−2 の橋（M89 の一次橋 tri_step の二次版）。 -/
theorem thJacBridge2 (N : Int) : (N - 2) * (N - 1) = N * (N + 1) - 4 * N + 2 := by
  have h1 : (N - 2) * (N - 1) = (N - 2) * N - (N - 2) := by
    rw [Int.mul_sub, Int.mul_one]
  have h2 : (N - 2) * N = N * N - 2 * N := Int.sub_mul N 2 N
  have h3 : N * (N + 1) = N * N + N := by rw [Int.mul_add, Int.mul_one]
  rw [h1, h2]
  omega

/-- **M313F-1b: 二次ガード** — 2m = N(N+1) なら 2N−1 ≤ m。
    (N−2)(N−1) ≥ 0（整数の連なりで常に非負）を橋で移す。 -/
theorem thJacTri2_le (m : Nat) (N : Int)
    (h : 2 * (m : Int) = N * (N + 1)) : 2 * N - 1 ≤ (m : Int) := by
  have hbr : (N - 2) * (N - 1) = N * (N + 1) - 4 * N + 2 := thJacBridge2 N
  have hnn : 0 ≤ (N - 2) * (N - 1) := by
    cases Int.lt_or_le N 2 with
    | inr hge => exact Int.mul_nonneg (by omega) (by omega)
    | inl hlt =>
      have heq : (2 - N) * (1 - N) = (N - 2) * (N - 1) := by
        rw [show (2 - N) = -(N - 2) by omega, show (1 - N) = -(N - 1) by omega,
          Int.neg_mul_neg]
      rw [← heq]
      exact Int.mul_nonneg (by omega) (by omega)
  omega

/-! ## M313F-2: 符号の周期2不変 -/

/-- **M313F-2: 符号は周期2で不変** — isgn(N−2) = isgn(N)
    （isgn_succ 二回 + neg_neg）。 -/
theorem thJac_isgn_shift2 (R : CRing) (N : Int) :
    isgn R (N - 2) = isgn R N := by
  have s1 := isgn_succ R (N - 2)
  have s2 := isgn_succ R (N - 1)
  rw [show (N - 2) + 1 = N - 1 by omega] at s1
  rw [show (N - 1) + 1 = N by omega] at s2
  rw [s2, s1, CRing.neg_neg R]

/-! ## M313F-3: T² = ((qu)·代入)² の Θ への作用 -/

/-- **M313F-3: T²(Θ) の q^m 係数**（uᴺ 係数 = Θ_{m−(2N−1)} の u^{N−2}
    係数、2N−1 ≤ m の範囲 — 単項式 uᵃqᵇ ↦ u^{a+2} q^{b+2a+3} の
    逆読み）。累積擬周期因子 c₂ = q³u²。bound 2m+2 は三角数の台
    tri_bound で証明。 -/
def thJacT2Rep (R : CRing) (m : Nat) : LRep R where
  coeff := fun N => if 2 * (N : Int) - 1 ≤ (m : Int)
    then (thetaRep R ((m : Int) - (2 * N - 1)).toNat).coeff (N - 2) else R.zero
  bnd := 2 * m + 2
  supp := fun N hN => by
    cases Int.decLe (2 * (N : Int) - 1) (m : Int) with
    | isFalse h => exact if_neg h
    | isTrue h =>
      rw [if_pos h]
      show (if 2 * ((((m : Int) - (2 * N - 1)).toNat : Nat) : Int)
          = (N - 2) * ((N - 2) + 1) then isgn R (N - 2) else R.zero)
        = R.zero
      refine if_neg (fun hc => ?_)
      have hcast : ((((m : Int) - (2 * N - 1)).toNat : Nat) : Int)
          = (m : Int) - (2 * N - 1) :=
        Int.toNat_of_nonneg (by omega)
      rw [hcast, show (N - 2) + 1 = N - 1 by omega] at hc
      have hbr : (N - 2) * (N - 1) = N * (N + 1) - 4 * N + 2 := thJacBridge2 N
      have h2 : 2 * (m : Int) = N * (N + 1) := by omega
      have hbnd := tri_bound m N h2
      omega

/-! ## M313F-4: 擬周期因子の具体形 -/

/-- **M313F-4: 擬周期因子の読み** — ガード域 2N−1 ≤ m では T²(Θ) の
    uᴺ 係数は Θ の u^{N−2} 係数（q-次数 2N−1 だけ低い）から来る。
    u-指数の +2 シフトと q-次数の 2N−1 降下が、累積因子 c₂ = q³u²
    （T の一次因子 qu を二回積んだ q³u²）の具体形を与える。 -/
theorem thJac_period_factor (R : CRing) (m : Nat) (N : Int)
    (hg : 2 * N - 1 ≤ (m : Int)) :
    (thJacT2Rep R m).coeff N
      = (thetaRep R ((m : Int) - (2 * N - 1)).toNat).coeff (N - 2) := by
  show (if 2 * (N : Int) - 1 ≤ (m : Int)
      then (thetaRep R ((m : Int) - (2 * N - 1)).toNat).coeff (N - 2)
      else R.zero)
    = (thetaRep R ((m : Int) - (2 * N - 1)).toNat).coeff (N - 2)
  rw [if_pos hg]

/-! ## M313F-5: 二次擬周期性（本丸） -/

/-- **定理 (M313F-5a): 二次擬周期性の係数形** — T²(Θ)_m = Θ_m。
    再添字化 n ↦ n−2・二重三角橋・符号の周期2不変・二次ガード。 -/
theorem thJac_quasi_period2 (R : CRing) (m : Nat) :
    (thJacT2Rep R m).coeff = (thetaRep R m).coeff := by
  funext N
  show (if 2 * (N : Int) - 1 ≤ (m : Int)
      then (thetaRep R ((m : Int) - (2 * N - 1)).toNat).coeff (N - 2)
      else R.zero)
    = (if 2 * (m : Int) = N * (N + 1) then isgn R N else R.zero)
  cases Int.decLe (2 * (N : Int) - 1) (m : Int) with
  | isFalse h =>
    rw [if_neg h, if_neg (fun hc => h (thJacTri2_le m N hc))]
  | isTrue h =>
    rw [if_pos h]
    show (if 2 * ((((m : Int) - (2 * N - 1)).toNat : Nat) : Int)
        = (N - 2) * ((N - 2) + 1) then isgn R (N - 2) else R.zero)
      = (if 2 * (m : Int) = N * (N + 1) then isgn R N else R.zero)
    have hcast : ((((m : Int) - (2 * N - 1)).toNat : Nat) : Int)
        = (m : Int) - (2 * N - 1) :=
      Int.toNat_of_nonneg (by omega)
    have hbr : (N - 2) * (N - 1) = N * (N + 1) - 4 * N + 2 := thJacBridge2 N
    cases Int.decEq (2 * (m : Int)) (N * (N + 1)) with
    | isTrue hc =>
      rw [if_pos (show 2 * ((((m : Int) - (2 * N - 1)).toNat : Nat) : Int)
          = (N - 2) * ((N - 2) + 1) from by
        rw [hcast, show (N - 2) + 1 = N - 1 by omega]
        omega),
        if_pos hc]
      exact thJac_isgn_shift2 R N
    | isFalse hc =>
      rw [if_neg (show ¬2 * ((((m : Int) - (2 * N - 1)).toNat : Nat) : Int)
          = (N - 2) * ((N - 2) + 1) from fun hcontra => by
        rw [hcast, show (N - 2) + 1 = N - 1 by omega] at hcontra
        exact hc (by omega)),
        if_neg hc]

/-- **定理 (M313F-5b): 二次擬周期性（級数レベル）** —
    (qu)(q²u)·Θ(q,q²u) = Θ(q,u)（T²(Θ) = Θ）。 -/
theorem thJac_quasi_period2_series (R : CRing) :
    (fun m => Quot.mk (laurentRel R) (thJacT2Rep R m)) = theta R := by
  funext m
  exact Quot.sound (thJac_quasi_period2 R m)

/-! ## M313F-6: 反転対合との整合 -/

/-- **定理 (M313F-6): 反転対合との整合** — T²(Θ) = J²(Θ) = Θ。
    二次擬周期（本層）と M98 反転対合 J（reflRep_involutive: J²=id）が
    Θ 上で一致する。テータの自己双対の高次版。 -/
theorem thJac_reflection_compat (R : CRing) (m : Nat) :
    (thJacT2Rep R m).coeff = (reflRep R (reflRep R (thetaRep R m))).coeff := by
  rw [thJac_quasi_period2 R m, reflRep_involutive R (thetaRep R m)]

/-! ## M313F-7: 総括レコードと存在 -/

/-- **M313F-7a: テータの Jacobi 擬周期性データ** — 一次擬周期
    T(Θ)=−Θ（M89）・二次擬周期 T²(Θ)=Θ（本層）・反転整合 T²=J²
    （M98）を一つに束ねる。主語は本物の形式テータ級数 Θ と本物の
    擬周期作用素（toy 主語なし）。 -/
structure ThetaJacobiData (R : CRing) where
  /-- 一次擬周期（M89 の関数等式）: (qu)·Θ(q,qu) = −Θ。 -/
  period1 : ∀ m : Nat, (tThetaRep R m).coeff = (lNeg R (thetaRep R m)).coeff
  /-- **本層の本丸**: 二次擬周期 (qu)(q²u)·Θ(q,q²u) = Θ。 -/
  period2 : ∀ m : Nat, (thJacT2Rep R m).coeff = (thetaRep R m).coeff
  /-- 反転対合との整合 T²(Θ) = J²(Θ) = Θ。 -/
  refl_compat : ∀ m : Nat,
    (thJacT2Rep R m).coeff = (reflRep R (reflRep R (thetaRep R m))).coeff

/-- **M313F-7b: witness 本体** — 全フィールドが既証明の純レコード。 -/
def thetaJacobiData (R : CRing) : ThetaJacobiData R where
  period1 := theta_funeq_coeff R
  period2 := thJac_quasi_period2 R
  refl_compat := thJac_reflection_compat R

/-- **定理 (M313F-7c): データの存在（見出し）**。 -/
theorem thJac_exists (R : CRing) : Nonempty (ThetaJacobiData R) :=
  ⟨thetaJacobiData R⟩

/-! ## 実例 -/

/-- 実例: 二次擬周期性 T²(Θ)=Θ を q¹ 係数で明示確認。 -/
example (R : CRing) : (thJacT2Rep R 1).coeff = (thetaRep R 1).coeff :=
  thJac_quasi_period2 R 1

/-- 実例: 二次擬周期性を q³ 係数で明示確認。 -/
example (R : CRing) : (thJacT2Rep R 3).coeff = (thetaRep R 3).coeff :=
  thJac_quasi_period2 R 3

/-- 実例: q⁰ 係数では T²(Θ) も Θ と同じ先頭 1 − u⁻¹（M88-5 経由）。 -/
example (R : CRing) :
    (thJacT2Rep R 0).coeff
      = (lAdd R (lOne R) (lNeg R (uMon R (-1)))).coeff :=
  (thJac_quasi_period2 R 0).trans (theta_zero_coeff R)

/-- 実例: 反転整合（q² 係数）。 -/
example (R : CRing) :
    (thJacT2Rep R 2).coeff
      = (reflRep R (reflRep R (thetaRep R 2))).coeff :=
  thJac_reflection_compat R 2

end IUT
