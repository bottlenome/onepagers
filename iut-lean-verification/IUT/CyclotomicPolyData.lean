/-
  IUT/CyclotomicPolyData.lean — CPD（円分多項式 Φ_p = 1+x+…+x^{p-1} の実データ
  と telescoping 因数分解 (x−1)·Φ_p = x^p−1 の実証明: 柱A 円分塔 A3 の各段の
  法多項式の土台）

  ── 分類 **[実]**（本物の先行建設。骨格でなく実 ℚ[X] 上の本物の多項式と
  本物の多項式等式・sorry 皆無・新規 Classical.choice 皆無・模型ゼロ）。

  **complete_pct 影響**: complete_pct **未設定（0 前進）**。本層は A3「円分塔
  ℚ ⊂ ℚ(ζ_p) ⊂ ℚ(ζ_{p²}) ⊂ …」の各段の**法多項式**の本物の土台であり、
  A1 実 Galois エンジンに非依存に建てられる独立な数論の切片である。円分
  多項式 Φ_p を実 ℚ[X]（冪級数環 `psRing ratRing` の有限台元）の**本物の
  元**として構成し、その定義的特徴づけ

      (x − 1) · (1 + x + … + x^{p-1}) = x^p − 1

  を実多項式等式として telescoping で**完全証明**する（模型・代理なし）。
  これは Φ_p が x^p−1 を (x−1) で割った商であること、すなわち 1 の原始 p
  乗根の最小多項式候補であることの代数的核心である。

  内容（すべて実 ℚ[X] = `PS ratRing`）:
   * `cpdPhiP p`          — Φ_p = Σ_{i<p} X^i（`pmbLinComb` の係数≡1 版）。
   * `cpdPhiP_coeff`      — 係数確定: Φ_p の j 次係数は j<p で 1・他で 0。
   * `cpdPhiP_bound`      — 有界性 IsPolyBounded Φ_p p（deg = p−1）。
   * `cpdPhiP_lead`       — 先頭係数 Φ_p (p−1) ≠ 0（p ≥ 1）。
   * `cpdXpMinus1 p`      — x^p − 1（psSingle 1 p + psC(−1)）。
   * `cpdXMinus1`         — x − 1（psSingle 1 1 + psC(−1)）。
   * `cpd_shift_zero`     — (X·Φ_p)_0 = 0（単項式 X による係数シフトの 0 次）。
   * `cpd_shift_coeff`    — (X·Φ_p)_{j+1} = Φ_p の j 次（係数シフト）。
   * **`cpd_factor`**     — **本丸**: (x−1)·Φ_p = x^p−1（telescoping・実等式）。
   * `cpdPhi3_eq`         — Φ_3 = 既存 `cq0PS`（= x²+x+1）と一致（整合確認）。
   * `cpdPhi9` / `cpdPhi9_bound` — Φ_9 = x^6+x^3+1（= Φ_3(x^3)）の実データ。

  正直な限定（§4 規約により消さない）:
   - **本物**: Φ_p・x^p−1・x−1 は実 ℚ[X] の本物の元（有限台の係数列）。
     等式 (x−1)Φ_p = x^p−1 は実多項式の全係数一致で完全証明（sorry 皆無・
     新規 choice 皆無）。代理でも模型でもない。
   - **含めない（後続）**: Φ_p の既約性（p 素数のとき）・円分塔の各段の
     体化（ℚ(ζ_{p^k}) の構成）・原始根の最小多項式性の同定は本層に含めない。
     本層は法多項式データと因数分解等式に限定する（A1 に非依存な独立切片）。
   - complete_pct は円分塔の体化・遠アーベル復元が本物で揃った段で動かす。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.PolyMonomialBasis
import IUT.Cq3Base
import IUT.Composition
import IUT.Freshman
import IUT.LubinTateZp
import IUT.FormalGroupExists

namespace IUT

/-! ## CPD-1: 円分多項式 Φ_p = Σ_{i<p} X^i -/

/-- **CPD-1a: 円分多項式** Φ_p = 1 + x + … + x^{p-1} = Σ_{i<p} X^i。
    `pmbLinComb`（有限線形結合）の係数を恒等的に 1 に取った版。実 ℚ[X]
    （冪級数環の有限台元）の本物の元。 -/
def cpdPhiP (p : Nat) : PS ratRing :=
  pmbLinComb ratRing (fun _ => ratRing.one) p

/-- **CPD-1b: Φ_p の係数** — j 次係数は j < p のとき 1・それ以外 0。
    j < p は `pmbLinComb_coeff`（座標読み出し）、j ≥ p は `pmbLinComb_bound`
    （有界性）で確定。 -/
theorem cpdPhiP_coeff (p j : Nat) :
    cpdPhiP p j = if j < p then ratRing.one else ratRing.zero := by
  cases Nat.lt_or_ge j p with
  | inl h =>
    rw [if_pos h]
    exact pmbLinComb_coeff ratRing (fun _ => ratRing.one) p j h
  | inr h =>
    rw [if_neg (by omega)]
    exact pmbLinComb_bound ratRing (fun _ => ratRing.one) p j h

/-- **CPD-1c: Φ_p の有界性** — deg Φ_p = p−1（p 次以上の係数は 0）。 -/
theorem cpdPhiP_bound (p : Nat) : IsPolyBounded ratRing (cpdPhiP p) p :=
  pmbLinComb_bound ratRing (fun _ => ratRing.one) p

/-- **CPD-1d: Φ_p の先頭係数 ≠ 0** — Φ_p (p−1) = 1 ≠ 0（p ≥ 1）。 -/
theorem cpdPhiP_lead (p : Nat) (hp : 1 ≤ p) :
    cpdPhiP p (p - 1) ≠ ratRing.zero := by
  rw [cpdPhiP_coeff p (p - 1), if_pos (show p - 1 < p by omega)]
  exact cbp_one_ne_zero

/-! ## CPD-2: x^p − 1 と x − 1 -/

/-- **CPD-2a: x^p − 1** — 単項式 X^p（psSingle 1 p）と定数 −1（psC(−1)）の和。
    円分塔の各段で分裂させる多項式（1 の p 乗根の消去多項式）。 -/
def cpdXpMinus1 (p : Nat) : PS ratRing :=
  psAdd ratRing (psSingle ratRing ratRing.one p)
    (psC ratRing (ratRing.neg ratRing.one))

/-- **CPD-2b: x − 1** — 単項式 X（psSingle 1 1）と定数 −1（psC(−1)）の和。
    Φ_p を掛けて x^p−1 を復元する一次因子。 -/
def cpdXMinus1 : PS ratRing :=
  psAdd ratRing (psSingle ratRing ratRing.one 1)
    (psC ratRing (ratRing.neg ratRing.one))

/-! ## CPD-3: 単項式 X による係数シフト -/

/-- **CPD-3a: シフトの 0 次** — (X·Φ_p)_0 = 0。単項式 X = psSingle 1 1 は
    0 次係数が 0 なので Cauchy 積の 0 次は消える。 -/
theorem cpd_shift_zero (p : Nat) :
    psMul ratRing (psSingle ratRing ratRing.one 1) (cpdPhiP p) 0 = ratRing.zero := by
  show ratRing.add ratRing.zero
      (ratRing.mul (psSingle ratRing ratRing.one 1 0) (cpdPhiP p (0 - 0))) = ratRing.zero
  rw [show psSingle ratRing ratRing.one 1 0 = ratRing.zero from if_neg (by omega),
    CRing.zero_mul ratRing (cpdPhiP p (0 - 0)), ratRing.zero_add]

/-- **CPD-3b: シフトの一段** — (X·Φ_p)_{j+1} = (Φ_p)_j。Cauchy 積
    Σ_{k≤j+1} (X)_k · (Φ_p)_{j+1−k} は k=1 の一点だけ生き（X の 1 次係数 = 1）、
    値は 1·(Φ_p)_j = (Φ_p)_j（一点集中和 `rsum_single`）。 -/
theorem cpd_shift_coeff (p j : Nat) :
    psMul ratRing (psSingle ratRing ratRing.one 1) (cpdPhiP p) (j + 1) = cpdPhiP p j := by
  show rsum ratRing (fun k => ratRing.mul (psSingle ratRing ratRing.one 1 k)
      (cpdPhiP p (j + 1 - k))) (j + 1 + 1) = cpdPhiP p j
  rw [rsum_single ratRing (fun k => ratRing.mul (psSingle ratRing ratRing.one 1 k)
        (cpdPhiP p (j + 1 - k))) 1 (j + 1 + 1) (by omega)
      (fun q _ hne => by
        show ratRing.mul (psSingle ratRing ratRing.one 1 q) (cpdPhiP p (j + 1 - q)) = ratRing.zero
        rw [show psSingle ratRing ratRing.one 1 q = ratRing.zero from if_neg hne]
        exact ratRing.zero_mul _)]
  show ratRing.mul (psSingle ratRing ratRing.one 1 1) (cpdPhiP p (j + 1 - 1)) = cpdPhiP p j
  rw [show psSingle ratRing ratRing.one 1 1 = ratRing.one from if_pos rfl,
    show j + 1 - 1 = j from by omega, ratRing.one_mul]

/-! ## CPD-4: 本丸 — (x−1)·Φ_p = x^p−1（telescoping） -/

/-- **定理 (CPD-4): 円分因数分解** — (x − 1)·(1 + x + … + x^{p-1}) = x^p − 1
    （実 ℚ[X] の多項式等式、p ≥ 1）。証明は全係数一致（funext）:
    右辺 (x−1)·Φ を右分配で (X·Φ) + (−1)·Φ に分け、X·Φ は係数シフト
    （CPD-3）、(−1)·Φ は係数の符号反転（`psC_mul_coeff`）。各 j 次で
     - j = 0: 0 + (−Φ_0) = −1（= x^p−1 の定数項）
     - 1 ≤ j < p: Φ_{j−1} − Φ_j = 1 − 1 = 0（telescoping で相殺）
     - j = p: Φ_{p−1} − Φ_p = 1 − 0 = 1（= x^p の係数）
     - j > p: 0 − 0 = 0
    となり x^p−1 の係数（p 次=1・0 次=−1・他 0）に一致する。 -/
theorem cpd_factor (p : Nat) (hp : 1 ≤ p) :
    cpdXpMinus1 p = psMul ratRing cpdXMinus1 (cpdPhiP p) := by
  funext j
  have hdist : psMul ratRing cpdXMinus1 (cpdPhiP p) j
      = ratRing.add
          (psMul ratRing (psSingle ratRing ratRing.one 1) (cpdPhiP p) j)
          (psMul ratRing (psC ratRing (ratRing.neg ratRing.one)) (cpdPhiP p) j) :=
    congrFun (CRing.right_distrib (psRing ratRing)
      (psSingle ratRing ratRing.one 1)
      (psC ratRing (ratRing.neg ratRing.one)) (cpdPhiP p)) j
  have hT : psMul ratRing (psC ratRing (ratRing.neg ratRing.one)) (cpdPhiP p) j
      = ratRing.neg (cpdPhiP p j) := by
    rw [psC_mul_coeff ratRing (ratRing.neg ratRing.one) (cpdPhiP p) j,
      CRing.neg_mul ratRing ratRing.one (cpdPhiP p j), ratRing.one_mul]
  rw [hdist, hT]
  cases j with
  | zero =>
    show cpdXpMinus1 p 0
       = ratRing.add (psMul ratRing (psSingle ratRing ratRing.one 1) (cpdPhiP p) 0)
           (ratRing.neg (cpdPhiP p 0))
    rw [cpd_shift_zero p]
    show ratRing.add (psSingle ratRing ratRing.one p 0)
        (psC ratRing (ratRing.neg ratRing.one) 0)
       = ratRing.add ratRing.zero (ratRing.neg (cpdPhiP p 0))
    rw [cpdPhiP_coeff p 0, if_pos (show 0 < p by omega),
      show psSingle ratRing ratRing.one p 0 = ratRing.zero from if_neg (by omega),
      show psC ratRing (ratRing.neg ratRing.one) 0 = ratRing.neg ratRing.one from if_pos rfl]
  | succ n =>
    show cpdXpMinus1 p (n + 1)
       = ratRing.add (psMul ratRing (psSingle ratRing ratRing.one 1) (cpdPhiP p) (n + 1))
           (ratRing.neg (cpdPhiP p (n + 1)))
    rw [cpd_shift_coeff p n]
    show ratRing.add (psSingle ratRing ratRing.one p (n + 1))
        (psC ratRing (ratRing.neg ratRing.one) (n + 1))
       = ratRing.add (cpdPhiP p n) (ratRing.neg (cpdPhiP p (n + 1)))
    rw [show psC ratRing (ratRing.neg ratRing.one) (n + 1) = ratRing.zero from if_neg (by omega),
      CRing.add_zero ratRing (psSingle ratRing ratRing.one p (n + 1)),
      cpdPhiP_coeff p n, cpdPhiP_coeff p (n + 1)]
    cases Nat.lt_or_ge (n + 1) p with
    | inl hlt =>
      rw [show psSingle ratRing ratRing.one p (n + 1) = ratRing.zero from if_neg (by omega),
        if_pos (show n < p by omega), if_pos hlt, CRing.add_neg ratRing ratRing.one]
    | inr hge =>
      cases Nat.decEq (n + 1) p with
      | isTrue heq =>
        rw [show psSingle ratRing ratRing.one p (n + 1) = ratRing.one from if_pos heq,
          if_pos (show n < p by omega), if_neg (show ¬ (n + 1 < p) by omega),
          CRing.neg_zero ratRing, CRing.add_zero ratRing ratRing.one]
      | isFalse hne =>
        rw [show psSingle ratRing ratRing.one p (n + 1) = ratRing.zero from if_neg hne,
          if_neg (show ¬ (n < p) by omega), if_neg (show ¬ (n + 1 < p) by omega),
          CRing.neg_zero ratRing, ratRing.zero_add]

/-! ## CPD-5: 具体化 Φ_3 = x²+x+1・Φ_9 = x^6+x^3+1 -/

/-- **CPD-5a: Φ_3 = x²+x+1** — 本層の Φ_3 = Σ_{i<3} X^i が既存の `cq0PS`
    （Cq3Base の x²+x+1 = 円分多項式 Φ_3）と一致することの整合確認。
    係数を j = 0,1,2 と j ≥ 3 で照合。 -/
theorem cpdPhi3_eq : cpdPhiP 3 = cq0PS := by
  funext j
  rw [cpdPhiP_coeff 3 j]
  cases Nat.lt_or_ge j 3 with
  | inr hge =>
    rw [if_neg (by omega)]
    exact (cq0_bound j hge).symm
  | inl hlt =>
    rw [if_pos hlt]
    cases j with
    | zero => exact cq0PS_coeff0.symm
    | succ j1 =>
      cases j1 with
      | zero => exact cq0PS_coeff1.symm
      | succ j2 =>
        cases j2 with
        | zero => exact cq0PS_coeff2.symm
        | succ j3 => exact absurd hlt (by omega)

/-- **CPD-5b: Φ_9 = x^6 + x^3 + 1** — Φ_9 = Φ_3(x^3)（p = 3 の二段目）。
    円分塔 ℚ(ζ_9)/ℚ の法多項式の実データ。 -/
def cpdPhi9 : PS ratRing :=
  psAdd ratRing
    (psAdd ratRing (psSingle ratRing ratRing.one 6) (psSingle ratRing ratRing.one 3))
    (psC ratRing ratRing.one)

/-- **CPD-5c: Φ_9 の有界性** — deg Φ_9 = 6（7 次以上の係数は 0）。 -/
theorem cpdPhi9_bound : IsPolyBounded ratRing cpdPhi9 7 := by
  intro j hj
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 j)
      (psSingle ratRing ratRing.one 3 j)) (psC ratRing ratRing.one j) = ratRing.zero
  rw [show psSingle ratRing ratRing.one 6 j = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 3 j = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one j = ratRing.zero from if_neg (by omega),
    ratRing.zero_add, ratRing.zero_add]

end IUT
