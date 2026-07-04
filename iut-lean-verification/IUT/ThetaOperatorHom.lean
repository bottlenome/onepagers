/-
  IUT/ThetaOperatorHom.lean — M198F: テータ級数の作用素準同型 T↦Φ(1)-乗算
  — 反復指数モノイド上の準同型と値レベル障害の定理化（柱E E-1・並行部品）

  柱E 残課題 E-1 のうち、M190F が「正直な限定」に明記した
  「級数環 R[u^{±1}][[q]] → thetaGrp の T ↦ Φ(1)-乗算という
  作用素レベルの準同型は未形式化」の切片を前進させる。本モジュールは
  **T-反復指数モノイド (ℕ, +) 上の作用素準同型**を構成し、あわせて
  この準同型が**級数の値には降りない**こと（値レベル障害）を
  定理として確定する:

    (1) **級数側の作用素半群則**: T^{j+k}(Θ) = T^k(T^j(Θ))。係数
        レベル tCoeff (j+k) = (−1)^k ∘ tCoeff j（negPow の加法則
        経由）と、級数（Quot）レベル thetaIter (j+k) =
        tOrbitIter k (thetaIter j)（T の Θ-軌道上の作用は M89 の
        関数等式により psNeg — その k 重反復）の両形
    (2) **群側の Φ(1)-乗算作用素**: phiMulOp l := Φ_l(1)·(−) とその
        k 重反復 phiMulIter。Φ_l(j+k) = phiMulIter k (Φ_l(j))、かつ
        **phiMulIter k = Φ_l(k)·(−)**（作用素の反復 = 群元 Φ_l(k) の
        乗算 — 作用素と群元の同定）
    (3) **本丸**: ラベル対応 T^j(Θ) ↦ Φ_l(j) のもとで、級数側の
        T^k-適用と群側の Φ(1)^k-乗算が同一の指数簿記で対応する
        作用素準同型 theta_operator_hom
    (4) **値レベル障害（本丸の裏面）**: T²(Θ) = Θ（thetaIter は
        周期 2）だが Φ_l(2) ≠ Φ_l(0)（l ≥ 3、商群の第 1 座標
        mod-l 不変量 firstCoordMod による分離）。ゆえに割当
        T^j(Θ) ↦ Φ_l(j) は級数の**値**を経由しては定義できず、
        作用素（反復指数）レベルでのみ準同型になる —— [EtTh] の
        「テータ関数そのものではなく mono-theta 環境（ラベル付き
        軌道）を使う」必然性の離散核
    (5) 準同型の J/ι_l-同変性: 級数側 J(T^j Θ) = T^{l−j}(Θ)
        （M190F-3b）と群側 ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist)
        （M187F-4a）の再束ね — 準同型は関数等式の反転とも両立する

  * M198F-1 `negPow_add` — j 重否定の加法則 (−1)^{j+k} = (−1)^k(−1)^j
  * M198F-2 `tCoeff_add` — 係数レベルの作用素半群則
    T^{j+k}(Θ) = T^k(T^j(Θ))（negPow_add + M90-3 tCoeff_eq）
  * M198F-3 `tOrbitIter` / `thetaIter_add` — Θ-軌道上の T^k
    （M89 関数等式より psNeg の k 重反復）と級数レベル半群則
  * M198F-4 `phiMulOp` / `phiMulIter` / `thetaSectionMod_zero` /
    `thetaSectionMod_succ_op` / `thetaSectionMod_add_op` — 群側の
    Φ(1)-乗算作用素・その反復・切断との整合
  * M198F-5 `phiMulIter_eq_mul` — **作用素 = 群元**: Φ(1)^k-乗算は
    Φ_l(k)-乗算（作用素レベルの反復が群の乗法に落ちる）
  * M198F-6 `theta_operator_hom`（**本丸**）— T ↦ Φ(1)-乗算の
    作用素準同型: 級数側 T^k-適用・群側 Φ(1)^k-乗算・群元 Φ_l(k) の
    乗算の三者が同一指数簿記で対応
  * M198F-7 `firstCoordMod` / `theta_op_value_obstruction`
    （**本丸の裏面**）— 値レベル障害: T²Θ = Θ だが Φ_l(2) ≠ Φ_l(0)
    （l ≥ 3）。準同型はラベル付き軌道（反復指数モノイド）上でしか
    定義できないことの**定理化**
  * M198F-8 `theta_op_hom_equivariant` — J/ι_l-同変性（M190F-3b +
    M187F-4a の準同型パッケージへの再束ね）
  * M198F-9 `ThetaOperatorHomData` / `thetaOperatorHomData` /
    `thetaOperatorHom_exists` — 総括レコード

  意義: M190F の辞書（解析側 T^j と群側 Φ_l(j) の恒等式レベルの接合）
  を、**作用素レベルの準同型**（単位・加法性・生成元・T^k ↔ Φ(1)^k の
  絡み合い・2l-周期性・J/ι_l-同変性を持つ (ℕ,+) → thetaGrpMod l）に
  昇格し、さらに「なぜ級数の値からの写像では準同型が取れないか」を
  値レベル障害の定理（M198F-7）として初めて機械検証する。

  正直な限定: 準同型の定義域は **T-反復指数モノイド (ℕ, +)**（=
  ラベル付き Θ-軌道 {T^j Θ}_j）であり、級数環 R[u^{±1}][[q]] 全体を
  定義域とする環準同型・環作用素の像としての定式化ではない。実際
  (i) T は有界台 Laurent 表現（LRep）の枠組では全級数環上の作用素と
  して定義できず（u の大負冪が高次 q 係数を呼び込む — M89 冒頭の
  申告）、(ii) 仮に値レベルで定義しようとしても M198F-7 が示す通り
  T²Θ = Θ かつ Φ_l(2) ≠ Φ_l(0) なので割当は well-defined にならない。
  ゆえに「作用素レベル」とはここでは反復指数の簿記を保つ準同型の
  意味であり、これが本枠組で到達可能な最強形である。p 進テータ値の
  ガロア同変な評価・tempered π₁ の商としての実現も未形式化（E-1 残）。
  商（thetaGrpMod / laurentRel / Quot）レベルの主張は Quot.sound を
  使う（商構成に内在、選択公理ではない）。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.ThetaFuneqBridge

namespace IUT

/-! ## M198F-1: j 重否定の加法則 -/

/-- **M198F-1: j 重否定の加法則** — negPow (j+k) = negPow k ∘ negPow j。
    (−1)^{j+k} = (−1)^k·(−1)^j の骨格形（k で帰納）。 -/
theorem negPow_add (R : CRing) (j k : Nat) (x : R.carrier) :
    negPow R (j + k) x = negPow R k (negPow R j x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show R.neg (negPow R (j + k) x) = R.neg (negPow R k (negPow R j x))
    rw [ih]

/-! ## M198F-2: 係数レベルの作用素半群則 -/

/-- **定理 (M198F-2): 係数レベルの作用素半群則** —
    T^{j+k}(Θ) の係数 = T^j(Θ) の係数の k 重否定、すなわち
    **T^{j+k} = T^k ∘ T^j** が Θ-軌道の係数簿記で成立する
    （M90-3 tCoeff_eq を negPow_add で貼り合わせ）。作用素の合成が
    反復指数の加法に一致することの係数形。 -/
theorem tCoeff_add (R : CRing) (j k m : Nat) (n : Int) :
    tCoeff R (j + k) m n = negPow R k (tCoeff R j m n) := by
  rw [tCoeff_eq R (j + k) m n, tCoeff_eq R j m n]
  exact negPow_add R j k ((thetaRep R m).coeff n)

/-! ## M198F-3: Θ-軌道上の T^k と級数レベル半群則 -/

/-- **M198F-3a: Θ-軌道上の T の k 重反復** — M89 の関数等式
    T(Θ) = −Θ により、T は Θ-軌道 {T^j Θ}_j 上で psNeg として
    作用する。その k 重反復（級数レベルの作用素 T^k の Θ-軌道への
    制限）。 -/
def tOrbitIter (R : CRing) : Nat → PS (laurentRing R) → PS (laurentRing R)
  | 0, f => f
  | k + 1, f => psNeg (laurentRing R) (tOrbitIter R k f)

/-- **定理 (M198F-3b): 級数レベルの作用素半群則** —
    thetaIter (j+k) = tOrbitIter k (thetaIter j)、すなわち
    **T^{j+k}(Θ) = T^k(T^j(Θ))** が R[u^{±1}][[q]] の級数の等式として
    成立する（M90-5c thetaIter_succ の k 重貼り合わせ）。 -/
theorem thetaIter_add (R : CRing) (j k : Nat) :
    thetaIter R (j + k) = tOrbitIter R k (thetaIter R j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show thetaIter R ((j + k) + 1)
      = psNeg (laurentRing R) (tOrbitIter R k (thetaIter R j))
    rw [thetaIter_succ R (j + k), ih]

/-! ## M198F-4: 群側の Φ(1)-乗算作用素 -/

/-- **M198F-4a: Φ(1)-乗算作用素** — thetaGrpMod l 上の左乗算
    x ↦ Φ_l(1)·x。級数側の作用素 T の群側対応物（M190F の辞書を
    作用素に昇格する主役）。 -/
def phiMulOp (l : Nat) (x : (thetaGrpMod l).carrier) :
    (thetaGrpMod l).carrier :=
  (thetaGrpMod l).mul (thetaSectionMod l 1) x

/-- **M198F-4b: Φ(1)-乗算の k 重反復** — 群側の作用素 T^k 対応物。 -/
def phiMulIter (l : Nat) : Nat → (thetaGrpMod l).carrier →
    (thetaGrpMod l).carrier
  | 0, x => x
  | k + 1, x => phiMulOp l (phiMulIter l k x)

/-- **M198F-4c: 切断の単位整合** — Φ_l(0) = 1（tri 0 = 0 より定義的）。
    作用素準同型の単位律。 -/
theorem thetaSectionMod_zero (l : Nat) :
    thetaSectionMod l 0 = (thetaGrpMod l).one := rfl

/-- **M198F-4d: 一段の絡み合い** — Φ_l(j+1) = Φ(1)-乗算 (Φ_l(j))。
    級数側の一段 thetaIter (j+1) = psNeg (thetaIter j)（M90-5c）の
    群側対応物。 -/
theorem thetaSectionMod_succ_op (l j : Nat) :
    thetaSectionMod l (j + 1) = phiMulOp l (thetaSectionMod l j) := by
  show thetaSectionMod l (j + 1)
    = (thetaGrpMod l).mul (thetaSectionMod l 1) (thetaSectionMod l j)
  have h : j + 1 = 1 + j := Nat.add_comm j 1
  rw [h]
  exact thetaSectionMod_mul l 1 j

/-- **定理 (M198F-4e): 群側の作用素半群則** —
    Φ_l(j+k) = phiMulIter k (Φ_l(j))。級数側 M198F-3b と同一の
    指数簿記（k で帰納、一段は M198F-4d）。 -/
theorem thetaSectionMod_add_op (l j k : Nat) :
    thetaSectionMod l (j + k) = phiMulIter l k (thetaSectionMod l j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show thetaSectionMod l ((j + k) + 1)
      = phiMulOp l (phiMulIter l k (thetaSectionMod l j))
    rw [thetaSectionMod_succ_op l (j + k), ih]

/-! ## M198F-5: 作用素の反復 = 群元の乗算 -/

/-- **定理 (M198F-5): Φ(1)^k-乗算 = Φ_l(k)-乗算** —
    phiMulIter l k x = Φ_l(k)·x。作用素レベルの k 重反復が群元
    Φ_l(k) の左乗算に**一致**する（作用素と群元の同定 — T^k ↦ Φ_l(k)
    が「作用素を群元で実現する」写像であることの根拠）。k = 0 は
    単位律（M198F-4c）、一段は結合律と切断の乗法性（M98F-5b）。 -/
theorem phiMulIter_eq_mul (l k : Nat) (x : (thetaGrpMod l).carrier) :
    phiMulIter l k x = (thetaGrpMod l).mul (thetaSectionMod l k) x := by
  induction k with
  | zero =>
    show x = (thetaGrpMod l).mul (thetaSectionMod l 0) x
    rw [thetaSectionMod_zero l]
    exact ((thetaGrpMod l).one_mul x).symm
  | succ k ih =>
    show phiMulOp l (phiMulIter l k x)
      = (thetaGrpMod l).mul (thetaSectionMod l (k + 1)) x
    rw [ih]
    show (thetaGrpMod l).mul (thetaSectionMod l 1)
        ((thetaGrpMod l).mul (thetaSectionMod l k) x)
      = (thetaGrpMod l).mul (thetaSectionMod l (k + 1)) x
    rw [← (thetaGrpMod l).mul_assoc]
    have h1 : thetaSectionMod l (k + 1)
        = (thetaGrpMod l).mul (thetaSectionMod l 1) (thetaSectionMod l k) := by
      have h : k + 1 = 1 + k := Nat.add_comm k 1
      rw [h]
      exact thetaSectionMod_mul l 1 k
    rw [h1]

/-! ## M198F-6: 作用素準同型（本丸） -/

/-- **定理 (M198F-6): T ↦ Φ(1)-乗算の作用素準同型（本丸）** —
    ラベル対応 T^j(Θ) ↦ Φ_l(j) のもとで、
    (1) 級数側: T^{j+k}(Θ) = T^k(T^j(Θ))（作用素の合成 = 指数の加法）、
    (2) 群側: Φ_l(j+k) = Φ(1)^k-乗算 (Φ_l(j))（同一の指数簿記）、
    (3) 作用素 = 群元: Φ(1)^k-乗算 (Φ_l(j)) = Φ_l(k)·Φ_l(j)
    （よって Φ_l(j+k) = Φ_l(k)·Φ_l(j) — 準同型性）
    の三者が**同一の (j, k) で**貼り合う。M190F の辞書（恒等式の並記）
    の作用素準同型への昇格。 -/
theorem theta_operator_hom (R : CRing) (l j k : Nat) :
    thetaIter R (j + k) = tOrbitIter R k (thetaIter R j)
    ∧ thetaSectionMod l (j + k) = phiMulIter l k (thetaSectionMod l j)
    ∧ phiMulIter l k (thetaSectionMod l j)
        = (thetaGrpMod l).mul (thetaSectionMod l k) (thetaSectionMod l j) :=
  ⟨thetaIter_add R j k, thetaSectionMod_add_op l j k,
    phiMulIter_eq_mul l k (thetaSectionMod l j)⟩

/-! ## M198F-7: 値レベル障害（本丸の裏面） -/

/-- **M198F-7a: 第 1 座標の mod-l 不変量** — thetaGrpMod l の元の
    第 1 座標 mod l（thetaRelMod は第 1 座標の差の l-整除を含むので
    Quot.lift で well-defined）。商群の元を分離する具体的不変量。 -/
def firstCoordMod (l : Nat) : (thetaGrpMod l).carrier → Int :=
  Quot.lift (fun x => x.1 % (l : Int))
    (fun x y hxy => by
      obtain ⟨⟨k, hk⟩, _, _⟩ := hxy
      show x.1 % (l : Int) = y.1 % (l : Int)
      have hx : x.1 = y.1 + (l : Int) * k := by
        rw [← hk]
        omega
      rw [hx]
      exact Int.add_mul_emod_self_left y.1 (l : Int) k)

/-- **M198F-7b: 不変量の切断値**（Quot.lift の計算則で定義的）。 -/
theorem firstCoordMod_section (l j : Nat) :
    firstCoordMod l (thetaSectionMod l j) = (j : Int) % (l : Int) := rfl

/-- **定理 (M198F-7c): 値レベル障害（本丸の裏面）** — T²(Θ) = Θ
    （thetaIter は周期 2 — M90-5d）だが **Φ_l(2) ≠ Φ_l(0)**（l ≥ 3、
    第 1 座標 mod-l 不変量が 2 ≠ 0 で分離）。ゆえに割当
    T^j(Θ) ↦ Φ_l(j) は級数の**値**の関数としては well-defined に
    ならず、作用素準同型（M198F-6）は**反復指数モノイド（ラベル付き
    Θ-軌道）上でのみ**定義できる。[EtTh] がテータ関数の値ではなく
    mono-theta 環境（ラベル構造）を保持する必然性の離散核。 -/
theorem theta_op_value_obstruction (R : CRing) (l : Nat) (hl : 3 ≤ l) :
    thetaIter R 2 = thetaIter R 0
    ∧ thetaSectionMod l 2 ≠ thetaSectionMod l 0 := by
  refine ⟨?_, ?_⟩
  · have h := thetaIter_even R 1
    have e : 2 * 1 = 2 := rfl
    rw [e] at h
    rw [thetaIter_zero R]
    exact h
  · intro hcontra
    have h2 : firstCoordMod l (thetaSectionMod l 2)
        = firstCoordMod l (thetaSectionMod l 0) :=
      congrArg (firstCoordMod l) hcontra
    rw [firstCoordMod_section l 2, firstCoordMod_section l 0] at h2
    have h2v : ((2 : Nat) : Int) % (l : Int) = 2 := by
      have hc : ((2 : Nat) : Int) = 2 := rfl
      rw [hc]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    have h0v : ((0 : Nat) : Int) % (l : Int) = 0 := by
      have hc : ((0 : Nat) : Int) = 0 := rfl
      rw [hc]
      exact Int.zero_emod (l : Int)
    rw [h2v, h0v] at h2
    omega

/-! ## M198F-8: 準同型の J/ι_l-同変性 -/

/-- **定理 (M198F-8): 作用素準同型の J/ι_l-同変性** — ラベル対応
    T^j(Θ) ↦ Φ_l(j) は関数等式の反転とも両立する: 級数側
    J(T^j Θ) = T^{l−j}(Θ)（M190F-3b）と群側
    ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist l j)（M187F-4a）が
    同一ラベル j で対応する（M190F の接合の準同型パッケージへの
    再束ね）。 -/
theorem theta_op_hom_equivariant (R : CRing) (l L : Nat)
    (hodd : l = 2 * L + 1) (j : Nat) (hj : j ≤ l) :
    (fun m => Quot.mk (laurentRel R) (reflRep R (tGaussRep R j m)))
        = thetaIter R (l - j)
    ∧ (thetaNegMod l).map (thetaSectionMod l j)
        = (thetaGrpMod l).mul (thetaSectionMod l (l - j))
            ((thetaRed l).map (0, 0, funeqTwist l j)) :=
  ⟨theta_refl_iter_series R l L j hodd hj,
    thetaNegMod_section_twist l j hj⟩

/-! ## M198F-9: 総括レコード -/

/-- **M198F-9a: テータ作用素準同型データ** — 反復指数モノイド
    (ℕ, +) からテータ群 mod l への作用素準同型（T^j ↦ Φ_l(j)）の
    一括束ね: 単位・生成元・加法性（準同型性）・2l-周期性・級数側
    半群則（係数/級数）・T^k ↔ Φ(1)^k の絡み合い・作用素 = 群元・
    J/ι_l-同変性・値レベル障害。E-1 の「作用素レベル準同型」切片の
    witness。 -/
structure ThetaOperatorHomData (R : CRing) (l L : Nat) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) where
  /-- 作用素準同型の本体: T^j ↦ Φ_l(j)（反復指数モノイド上）。 -/
  opHom : Nat → (thetaGrpMod l).carrier
  /-- 単位律: T^0 = id ↦ 1。 -/
  map_unit : opHom 0 = (thetaGrpMod l).one
  /-- 生成元: T ↦ Φ_l(1)。 -/
  map_gen : opHom 1 = thetaSectionMod l 1
  /-- 準同型性: T^{j+k} = T^j ∘ T^k ↦ Φ_l(j)·Φ_l(k)。 -/
  map_add : ∀ j k : Nat,
    opHom (j + k) = (thetaGrpMod l).mul (opHom j) (opHom k)
  /-- 2l-周期性: 準同型は ℤ/2l を経由する（M98F-5c）。 -/
  map_period : ∀ j : Nat, opHom (j + 2 * l) = opHom j
  /-- 級数側半群則（係数レベル）: T^{j+k}(Θ) の係数 = k 重否定。 -/
  series_coeff : ∀ (j k m : Nat) (n : Int),
    tCoeff R (j + k) m n = negPow R k (tCoeff R j m n)
  /-- 級数側半群則（級数レベル）: T^{j+k}(Θ) = T^k(T^j(Θ))。 -/
  series_iter : ∀ j k : Nat,
    thetaIter R (j + k) = tOrbitIter R k (thetaIter R j)
  /-- 絡み合い: 群側でも同一の指数簿記 Φ_l(j+k) = Φ(1)^k(Φ_l(j))。 -/
  intertwine : ∀ j k : Nat, opHom (j + k) = phiMulIter l k (opHom j)
  /-- 作用素 = 群元: Φ(1)^k-乗算 = Φ_l(k)-乗算。 -/
  op_eq_elem : ∀ (k : Nat) (x : (thetaGrpMod l).carrier),
    phiMulIter l k x = (thetaGrpMod l).mul (opHom k) x
  /-- J/ι_l-同変性（級数側）: J(T^j Θ) = T^{l−j}(Θ)。 -/
  equivariant_series : ∀ j : Nat, j ≤ l →
    (fun m => Quot.mk (laurentRel R) (reflRep R (tGaussRep R j m)))
      = thetaIter R (l - j)
  /-- J/ι_l-同変性（群側）: ι_l(opHom j) = opHom(l−j)·red(0,0,捻れ)。 -/
  equivariant_group : ∀ j : Nat, j ≤ l →
    (thetaNegMod l).map (opHom j)
      = (thetaGrpMod l).mul (opHom (l - j))
          ((thetaRed l).map (0, 0, funeqTwist l j))
  /-- 値レベル障害: T²Θ = Θ だが opHom 2 ≠ opHom 0 —— 準同型は
      級数の値を経由しては定義できない。 -/
  value_obstruction : thetaIter R 2 = thetaIter R 0 ∧ opHom 2 ≠ opHom 0

/-- **M198F-9b: witness 本体** — opHom := thetaSectionMod l として
    全フィールドを M198F-2〜8 と M98F-5b/5c で埋める。 -/
def thetaOperatorHomData (R : CRing) (l L : Nat) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) : ThetaOperatorHomData R l L hL hodd where
  opHom := thetaSectionMod l
  map_unit := thetaSectionMod_zero l
  map_gen := rfl
  map_add := fun j k => thetaSectionMod_mul l j k
  map_period := fun j => thetaSectionMod_period l j
  series_coeff := fun j k m n => tCoeff_add R j k m n
  series_iter := fun j k => thetaIter_add R j k
  intertwine := fun j k => thetaSectionMod_add_op l j k
  op_eq_elem := fun k x => phiMulIter_eq_mul l k x
  equivariant_series := fun j hj => theta_refl_iter_series R l L j hodd hj
  equivariant_group := fun j hj => thetaNegMod_section_twist l j hj
  value_obstruction := theta_op_value_obstruction R l (by omega)

/-- **定理 (M198F-9c): テータ作用素準同型データの存在（M198F 見出し）**
    — 任意の係数環 R と奇数 l = 2l⋇+1 ≥ 3 に対し、T ↦ Φ(1)-乗算の
    作用素準同型データが存在する。 -/
theorem thetaOperatorHom_exists (R : CRing) (l L : Nat) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) :
    Nonempty (ThetaOperatorHomData R l L hL hodd) :=
  ⟨thetaOperatorHomData R l L hL hodd⟩

end IUT

