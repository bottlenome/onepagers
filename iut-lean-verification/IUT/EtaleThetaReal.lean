/-
  IUT/EtaleThetaReal.lean — M308F（エタールテータの本物の部分ケース:
  テータ因子の原点通過 / 柱E・テータ）

  分類: **[実]**（本物の先行建設 (b)）。
  complete_pct 影響: 柱E の実 IUT 完全証明率を **テータ因子（divisor）の
  本物の部分ケース**の側で前進させる。既存の柱E は実テータ級数
  Θ(q,u)=Σ_n (−1)ⁿ q^{n(n+1)/2} uⁿ（M88, 形式冪級数環 R[u^{±1}][[q]] 上
  の本物）・関数等式（M89）・反転対称性（M98）・ガウス簿記（M90）まで
  本物で建設済みだが、**テータの零点／因子**（候補2）は未着手だった。
  本層はそこへ本物で踏み込む:

    (1) **本物の対象**: Laurent 表現 F : LRep R 上の
        **u=1 での増大射（augmentation）ε: R[u^{±1}] → R**
        （`etThRealEv1`）を、有界台の**本物の有限和**（wsum, choice なし）
        として構成する。ε は Tate 点群 ℚ_p^×/q^ℤ の**単位元 u=1
        （＝ Tate 楕円曲線の原点）での値**であり、Laurent 環の標準
        augmentation Σ c_n u^n ↦ Σ c_n の忠実な実装。
    (2) **本物の性質（本丸）**: **Θ(q,1) = 0**（`etThReal_theta_vanish`）。
        すなわち各 q-次数 m で ε(Θ_m) = 0。これは古典的 Jacobi テータが
        原点に零点を持つことの解析的核であり、「テータ因子が Tate 曲線の
        原点を通る」ことの本物の機械検証。証明は既に本物で証明済みの
        反転対称性 J(Θ) = −Θ（M98 `theta_refl_coeff`, 係数 F_{−(n+1)} =
        −F_n）を、**不動点のない符号反転対合 n ↦ −(n+1)** の対ごとの
        相殺として、対称窓 [−(b+1), b] 上の有限和に持ち上げる
        （S = −S から 2S = 0 を導く弱い議論ではなく、相異なる対を一度ずつ
        足す本物の対消去なので、一般の可換環 R でそのまま S = 0 が立つ）。

  * M308F-1 `etThRealWinCoeff` / `etThRealEv1` — u=1 augmentation ε
    （対称窓上の本物の有限和）
  * M308F-2 `etThReal_rsum_split` — 有限和の分割（局所補題, 自前導出で
    外部依存を回避）
  * M308F-3 `etThRealEv1_window` — 窓非依存性（台を覆う任意窓で同値）
  * M308F-4 `etThRealEv1_add` / `etThRealEv1_one` — ε の加法性・単位
    （ε が本物の augmentation 準同型であることの証拠）
  * M308F-5 `etThRealEv1_of_antisym` — **反転対合による有限和の消去
    （本丸の核）**
  * M308F-6 `etThReal_theta_vanish` — **Θ(q,1) = 0（テータ因子の原点
    通過, 本丸）**
  * M308F-7 `EtaleThetaRealData` / `etaleThetaRealData` / `etThReal_exists`
    — 総括レコードと存在

  **正直な限定（消去・弱化禁止）**:
  - ここで扱うのは**テータ因子の一点（原点 u=1）通過**まで。零点の
    重複度が単純（simple zero）であること・因子全体が q^ℤ·(±1) 軌道で
    あること・Jacobi 三重積の積表示は**後続**。
  - ε の乗法性 ε(F·G)=ε(F)·ε(G)（増大射が完全な環準同型であること）は
    加法性・単位のみ本物化し、乗法性は**後続**（畳み込みの二重和の
    再添字が必要）。本層で本物にした augmentation の性質は
    加法性・単位・窓非依存性・そして本丸の Θ(q,1)=0。
  - 完全なエタールテータ関数（tempered 基本群 π₁^tp 上の被覆・
    cyclotomic 三剛性の全証明）は**後続**。本層は**本物の形式冪級数
    Θ 上の 1 性質（因子の原点通過）**まで。
  - toy 主語なし: 主語は本物の Θ（M88 の形式冪級数）と本物の
    augmentation（有界台の有限和）であり、Bool 軌道・m202fVol・surrogate
    群は一切用いない。

  全て選択公理不使用（Quot.sound すら使わない・純粋な有限和の計算）。
  サブエージェント新規1本（共有ファイル未変更）。
-/
import IUT.ThetaReflection
import IUT.PowerSeries

namespace IUT

/-! ## M308F-1: u=1 augmentation ε（本物の有限和） -/

/-- **M308F-1a: 対称窓の係数列** — 台 [−b, b]（b = F.bnd）を含む
    対称窓 [−(b+1), b]（長さ 2b+2, 反転対合 n ↦ −(n+1) で不変）上の
    Laurent 係数を Nat 添字 t で読む。 -/
def etThRealWinCoeff (R : CRing) (F : LRep R) (t : Nat) : R.carrier :=
  F.coeff (-((F.bnd : Int) + 1) + (t : Int))

/-- **M308F-1b: u=1 augmentation ε(F)** — Laurent 元 F を u ↦ 1 で
    特殊化した値 Σ_n F_n。台の有界性ゆえ本物の有限和（正準窓
    [−b, b], 長さ 2b+1）。Tate 点群の単位元 u=1（Tate 曲線の原点）での
    値。 -/
def etThRealEv1 (R : CRing) (F : LRep R) : R.carrier :=
  wsum R F.coeff (-(F.bnd : Int)) (2 * F.bnd + 1)

/-! ## M308F-2: 有限和の分割（自前導出） -/

/-- **M308F-2: 有限和の分割** — rsum g (i+d) = rsum g i + Σ_{k<d} g(i+k)。
    外部モジュール依存を避けるため d の帰納で自前導出。 -/
theorem etThReal_rsum_split (R : CRing) (g : Nat → R.carrier) (i : Nat) :
    ∀ d, rsum R g (i + d)
      = R.add (rsum R g i) (rsum R (fun k => g (i + k)) d) := by
  intro d
  induction d with
  | zero =>
    show rsum R g (i + 0)
      = R.add (rsum R g i) (rsum R (fun k => g (i + k)) 0)
    rw [Nat.add_zero]
    show rsum R g i = R.add (rsum R g i) R.zero
    exact (CRing.add_zero R (rsum R g i)).symm
  | succ d ih =>
    show rsum R g (i + (d + 1))
      = R.add (rsum R g i) (rsum R (fun k => g (i + k)) (d + 1))
    have e1 : i + (d + 1) = (i + d) + 1 := by omega
    rw [e1]
    show R.add (rsum R g (i + d)) (g (i + d))
      = R.add (rsum R g i)
          (R.add (rsum R (fun k => g (i + k)) d) (g (i + d)))
    rw [ih]
    exact R.add_assoc (rsum R g i) (rsum R (fun k => g (i + k)) d) (g (i + d))

/-! ## M308F-3: 窓非依存性 -/

/-- **M308F-3: ε の窓非依存性** — 台 [−b, b] を覆う任意の窓 [lo, lo+len)
    での有限和は ε(F) に一致（wsum_supported）。ε が padding に依らない
    本物の augmentation であることの根拠。 -/
theorem etThRealEv1_window (R : CRing) (F : LRep R) (lo : Int) (len : Nat)
    (hlo : lo ≤ -(F.bnd : Int)) (hhi : (F.bnd : Int) < lo + (len : Int)) :
    wsum R F.coeff lo len = etThRealEv1 R F :=
  wsum_supported R F.coeff F.bnd (fun k hk => F.supp k hk) lo len hlo hhi

/-! ## M308F-4: ε の加法性・単位（augmentation 準同型の証拠） -/

/-- **M308F-4a: ε は加法的** — ε(F + G) = ε(F) + ε(G)（共通窓 +
    wsum_add + 窓非依存性）。 -/
theorem etThRealEv1_add (R : CRing) (F G : LRep R) :
    etThRealEv1 R (lAdd R F G)
      = R.add (etThRealEv1 R F) (etThRealEv1 R G) := by
  have h1 := Nat.le_max_left F.bnd G.bnd
  have h2 := Nat.le_max_right F.bnd G.bnd
  show wsum R (fun k => R.add (F.coeff k) (G.coeff k))
      (-((max F.bnd G.bnd : Nat) : Int)) (2 * max F.bnd G.bnd + 1)
    = R.add (etThRealEv1 R F) (etThRealEv1 R G)
  rw [wsum_add R F.coeff G.coeff (-((max F.bnd G.bnd : Nat) : Int))
        (2 * max F.bnd G.bnd + 1),
      etThRealEv1_window R F (-((max F.bnd G.bnd : Nat) : Int))
        (2 * max F.bnd G.bnd + 1) (by omega) (by omega),
      etThRealEv1_window R G (-((max F.bnd G.bnd : Nat) : Int))
        (2 * max F.bnd G.bnd + 1) (by omega) (by omega)]

/-- **M308F-4b: ε の単位** — ε(1) = 1（定数 1 の u=1 での値）。 -/
theorem etThRealEv1_one (R : CRing) : etThRealEv1 R (lOne R) = R.one := by
  show R.add R.zero
      (if (-((0 : Nat) : Int) + ((0 : Nat) : Int)) = 0 then R.one else R.zero)
    = R.one
  rw [if_pos (show (-((0 : Nat) : Int) + ((0 : Nat) : Int)) = 0 from by omega),
    R.zero_add]

/-! ## M308F-5: 反転対合による有限和の消去（本丸の核） -/

/-- **定理 (M308F-5): 反転対合による ε の消去** — 係数が反転対合
    n ↦ −(n+1) で符号反転（F_{−(n+1)} = −F_n）するなら ε(F) = 0。

    対称窓 [−(b+1), b]（長さ 2b+2）を前半 [0, b]・後半 [b+1, 2b+1] に
    分け、後半を反転（t ↦ 2b+1−t）して前半と対にすると、位置 t の対
    (k, 2b+1−k) はちょうど格子点の対 (−(b+1)+k, b−k) を成し、
    b−k = −((−(b+1)+k)+1) より第 2 成分は第 1 成分の反転対合像。
    仮定より各対は F_k + F_{−(k+1)} 型で相殺 = 0。相異なる対を一度ずつ
    足すので S = −S 経由の 2S = 0 ではなく、一般の可換環で S = 0。 -/
theorem etThRealEv1_of_antisym (R : CRing) (F : LRep R)
    (hanti : ∀ n : Int, F.coeff (-(n + 1)) = R.neg (F.coeff n)) :
    etThRealEv1 R F = R.zero := by
  -- 対称窓 [−(b+1), b] へ移る
  have hwin : wsum R F.coeff (-((F.bnd : Int) + 1)) (2 * F.bnd + 2)
      = etThRealEv1 R F :=
    etThRealEv1_window R F (-((F.bnd : Int) + 1)) (2 * F.bnd + 2)
      (by omega) (by omega)
  rw [← hwin]
  show rsum R (etThRealWinCoeff R F) (2 * F.bnd + 2) = R.zero
  -- 長さ 2b+2 = (b+1)+(b+1) を分割し後半を反転
  have hlen : 2 * F.bnd + 2 = (F.bnd + 1) + (F.bnd + 1) := by omega
  have hsplit : rsum R (etThRealWinCoeff R F) ((F.bnd + 1) + (F.bnd + 1))
      = R.add (rsum R (etThRealWinCoeff R F) (F.bnd + 1))
          (rsum R (fun k => etThRealWinCoeff R F ((F.bnd + 1) + k))
            (F.bnd + 1)) :=
    etThReal_rsum_split R (etThRealWinCoeff R F) (F.bnd + 1) (F.bnd + 1)
  have hrefl : rsum R (fun k => etThRealWinCoeff R F ((F.bnd + 1) + k))
        (F.bnd + 1)
      = rsum R (fun k => etThRealWinCoeff R F ((F.bnd + 1) + (F.bnd - k)))
          (F.bnd + 1) :=
    rsum_reflect R F.bnd (fun k => etThRealWinCoeff R F ((F.bnd + 1) + k))
  rw [hlen, hsplit, hrefl,
    ← rsum_add R (etThRealWinCoeff R F)
      (fun k => etThRealWinCoeff R F ((F.bnd + 1) + (F.bnd - k))) (F.bnd + 1)]
  refine Eq.trans (rsum_congr R (F.bnd + 1) (fun k hk => ?_))
    (rsum_const_zero R (F.bnd + 1))
  -- 各対 (k, 反転) の和 = 0
  show R.add (etThRealWinCoeff R F k)
      (etThRealWinCoeff R F ((F.bnd + 1) + (F.bnd - k))) = R.zero
  have hidx : -((F.bnd : Int) + 1)
        + (((F.bnd + 1) + (F.bnd - k) : Nat) : Int)
      = -((-((F.bnd : Int) + 1) + (k : Int)) + 1) := by omega
  have hval : etThRealWinCoeff R F ((F.bnd + 1) + (F.bnd - k))
      = R.neg (etThRealWinCoeff R F k) := by
    show F.coeff (-((F.bnd : Int) + 1)
        + (((F.bnd + 1) + (F.bnd - k) : Nat) : Int))
      = R.neg (F.coeff (-((F.bnd : Int) + 1) + (k : Int)))
    rw [hidx]
    exact hanti (-((F.bnd : Int) + 1) + (k : Int))
  rw [hval, R.add_comm]
  exact R.neg_add (etThRealWinCoeff R F k)

/-! ## M308F-6: Θ(q,1) = 0（テータ因子の原点通過, 本丸） -/

/-- **定理 (M308F-6): テータ因子は原点 u=1 を通る** — 各 q-次数 m で
    ε(Θ_m) = Θ(q,1) の q^m 係数 = 0。すなわち本物の形式テータ級数
    Θ(q,u) は u=1（Tate 楕円曲線の原点）で消える。

    反転対称性 J(Θ) = −Θ（M98 `theta_refl_coeff`）が与える
    Θ_{−(n+1)} = −Θ_n をそのまま M308F-5 の反転対合仮定に渡す。 -/
theorem etThReal_theta_vanish (R : CRing) (m : Nat) :
    etThRealEv1 R (thetaRep R m) = R.zero := by
  refine etThRealEv1_of_antisym R (thetaRep R m) (fun n => ?_)
  show (thetaRep R m).coeff (-(n + 1)) = R.neg ((thetaRep R m).coeff n)
  exact congrFun (theta_refl_coeff R m) n

/-! ## M308F-7: 総括レコードと存在 -/

/-- **M308F-7a: エタールテータの本物の部分ケース データ** — u=1
    augmentation ε（本物の有限和）と、その加法性・単位、そして本丸
    「テータ因子の原点通過 ε(Θ_m)=0」を一つに束ねる。主語は本物の
    形式テータ級数 Θ と本物の augmentation（toy 主語なし）。 -/
structure EtaleThetaRealData (R : CRing) where
  /-- u=1 augmentation ε: R[u^{±1}] → R（本物の有限和）。 -/
  ev1 : LRep R → R.carrier
  /-- ε は加法的（augmentation 準同型の加法部分）。 -/
  ev1_add : ∀ F G : LRep R, ev1 (lAdd R F G) = R.add (ev1 F) (ev1 G)
  /-- ε(1) = 1（augmentation の単位）。 -/
  ev1_one : ev1 (lOne R) = R.one
  /-- **本丸**: テータ因子は原点 u=1 を通る — ε(Θ_m) = 0（∀ m）。 -/
  theta_divisor : ∀ m : Nat, ev1 (thetaRep R m) = R.zero

/-- **M308F-7b: witness 本体** — 全フィールドが既証明の純レコード。 -/
def etaleThetaRealData (R : CRing) : EtaleThetaRealData R where
  ev1 := etThRealEv1 R
  ev1_add := etThRealEv1_add R
  ev1_one := etThRealEv1_one R
  theta_divisor := etThReal_theta_vanish R

/-- **定理 (M308F-7c): データの存在（見出し）**。 -/
theorem etThReal_exists (R : CRing) : Nonempty (EtaleThetaRealData R) :=
  ⟨etaleThetaRealData R⟩

/-! ## 実例 -/

/-- 実例: 任意の係数環 R 上でテータ因子は原点を通る（q^3 係数まで）。 -/
example (R : CRing) : etThRealEv1 R (thetaRep R 3) = R.zero :=
  etThReal_theta_vanish R 3

/-- 実例: augmentation の単位。 -/
example (R : CRing) : (etaleThetaRealData R).ev1 (lOne R) = R.one :=
  etThRealEv1_one R

end IUT
