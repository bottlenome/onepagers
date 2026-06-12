/-
  IUT/FormalGroupSub.lean — M51（二変数→二変数代入と恒等代入: 形式群第二層）

  形式群法則の方程式 f∘F = F∘(f(X), f(Y)) の右辺を書くための
  **二変数→二変数代入**

    F(P, Q)_{i,j} := Σ_{b≤i+j} Σ_{a≤i+j} F_{a,b} · (P^a · Q^b)_{i,j}

  を構成する（P₀₀ = Q₀₀ = 0 のとき総次数 truncation により真の代入と
  一致する有限和）。サニティアンカーとして**恒等代入 F(X, Y) = F** を
  完全証明する — 代入の定義が正しい座標規約を持つことの機械的保証。

  * M51-1 `psPow_psC` — 定数項埋め込みの冪 (psC z)^k = psC (z^k)
    （M47 の hC パターンの一般补題化）
  * M51-2 `ps2Mono` / `ps2X_pow` / `ps2Y_pow` / `ps2MonoXY` —
    二変数単項式 X^a Y^b の代数: X^a = psC(X^a)・Y^b = (Y-mono)^b・
    **X^a·Y^b = δ_{(a,b)}**（係数は (i,j) = (a,b) でだけ 1）
  * M51-3 `ps2Comp2` — 二変数→二変数代入（総次数の矩形で打ち切り）
  * M51-4 `ps2Comp2_coords` — **恒等代入** F(X, Y) = F
    （二重の一点集中和: 外側 b = j、内側 a = i にスパイク）

  ロードマップ: 次層で f∘F = F∘(f(X), f(Y)) の方程式定式化
  （f(X) = ps2Comp1 f X-座標 等）→ 形式群法則の存在の係数帰納
  （総次数版）。全て選択公理不使用。
-/
import IUT.PowerSeries2

namespace IUT

/-! ## 定数項埋め込みの冪と座標の冪 -/

/-- **M51-1**: (psC z)^k = psC (z^k)（psC は環準同型なので冪を保つ）。 -/
theorem psPow_psC (S : CRing) (z : S.carrier) (k : Nat) :
    psPow S (psC S z) k = psC S (rpow S z k) := by
  rw [psPow_eq_rpow S (psC S z) k]
  exact (ringHom_rpow (psConstHom S) z k).symm

/-- psX は単項式 X^1。 -/
theorem psX_eq_psMono (R : CRing) : psX R = psMono R 1 := rfl

/-- **M51-2a: X 座標の冪** X^a = psC(psMono a)。 -/
theorem ps2X_pow (R : CRing) (a : Nat) :
    psPow (psRing R) (ps2X R) a = psC (psRing R) (psMono R a) := by
  show psPow (psRing R) (psC (psRing R) (psX R)) a = psC (psRing R) (psMono R a)
  rw [psPow_psC (psRing R) (psX R) a, ← psPow_eq_rpow R (psX R) a,
    psX_eq_psMono R, psMono_pow R 1 a, show 1 * a = a from Nat.one_mul a]

/-- **M51-2b: Y 座標の冪** Y^b = psMono(psRing R) b。 -/
theorem ps2Y_pow (R : CRing) (b : Nat) :
    psPow (psRing R) (ps2Y R) b = psMono (psRing R) b := by
  show psPow (psRing R) (psMono (psRing R) 1) b = psMono (psRing R) b
  rw [psMono_pow (psRing R) 1 b, show 1 * b = b from Nat.one_mul b]

/-! ## 二変数単項式 -/

/-- 二変数単項式 X^a Y^b（係数は (i,j) = (a,b) でだけ 1）。 -/
def ps2Mono (R : CRing) (a b : Nat) : PS2 R :=
  fun j => fun i =>
    if j = b then (if i = a then R.one else R.zero) else R.zero

/-- **定理 (M51-2c): 単項式の積公式** X^a · Y^b = ps2Mono a b。 -/
theorem ps2MonoXY (R : CRing) (a b : Nat) :
    psMul (psRing R) (psPow (psRing R) (ps2X R) a)
      (psPow (psRing R) (ps2Y R) b) = ps2Mono R a b := by
  rw [ps2X_pow R a, ps2Y_pow R b]
  funext j i
  have hc : psMul (psRing R) (psC (psRing R) (psMono R a))
      (psMono (psRing R) b) j
      = (psRing R).mul (psMono R a) (psMono (psRing R) b j) :=
    psC_mul_coeff (psRing R) (psMono R a) (psMono (psRing R) b) j
  show psMul (psRing R) (psC (psRing R) (psMono R a))
      (psMono (psRing R) b) j i = ps2Mono R a b j i
  rw [hc]
  cases Nat.decEq j b with
  | isTrue hjb =>
    rw [show psMono (psRing R) b j = (psRing R).one from if_pos hjb,
      CRing.mul_one (psRing R) (psMono R a)]
    show psMono R a i = ps2Mono R a b j i
    rw [show ps2Mono R a b j i
        = (if i = a then R.one else R.zero) from by
      show (if j = b then (if i = a then R.one else R.zero) else R.zero)
        = (if i = a then R.one else R.zero)
      rw [if_pos hjb]]
    rfl
  | isFalse hjb =>
    rw [show psMono (psRing R) b j = (psRing R).zero from if_neg hjb,
      CRing.mul_zero (psRing R) (psMono R a)]
    show psZero R i = ps2Mono R a b j i
    rw [show ps2Mono R a b j i = R.zero from by
      show (if j = b then (if i = a then R.one else R.zero) else R.zero)
        = R.zero
      rw [if_neg hjb]]
    rfl

/-! ## 二変数→二変数代入 -/

/-- **M51-3: 二変数→二変数代入** F(P,Q)_{i,j} =
    Σ_{b,a ≤ i+j} F_{a,b}·(P^a Q^b)_{i,j}（総次数の矩形で打ち切り。
    P₀₀ = Q₀₀ = 0 のとき総次数 truncation により真の代入と一致）。 -/
def ps2Comp2 (R : CRing) (F P Q : PS2 R) : PS2 R :=
  fun j => fun i =>
    rsum R (fun b => rsum R (fun a => R.mul (F b a)
      ((psMul (psRing R) (psPow (psRing R) P a) (psPow (psRing R) Q b)) j i))
      (i + j + 1)) (i + j + 1)

/-- **定理 (M51-4): 恒等代入** F(X, Y) = F — 代入の座標規約の
    サニティアンカー（外側 b = j・内側 a = i の二重一点集中和）。 -/
theorem ps2Comp2_coords (R : CRing) (F : PS2 R) :
    ps2Comp2 R F (ps2X R) (ps2Y R) = F := by
  funext j i
  show rsum R (fun b => rsum R (fun a => R.mul (F b a)
      ((psMul (psRing R) (psPow (psRing R) (ps2X R) a)
        (psPow (psRing R) (ps2Y R) b)) j i)) (i + j + 1)) (i + j + 1)
    = F j i
  -- 各項の単項式を ps2Mono に書き換え
  have hterm : ∀ b a, (psMul (psRing R) (psPow (psRing R) (ps2X R) a)
      (psPow (psRing R) (ps2Y R) b)) j i = ps2Mono R a b j i :=
    fun b a => congrFun (congrFun (ps2MonoXY R a b) j) i
  have hc1 : rsum R (fun b => rsum R (fun a => R.mul (F b a)
        ((psMul (psRing R) (psPow (psRing R) (ps2X R) a)
          (psPow (psRing R) (ps2Y R) b)) j i)) (i + j + 1)) (i + j + 1)
      = rsum R (fun b => rsum R (fun a => R.mul (F b a)
          (ps2Mono R a b j i)) (i + j + 1)) (i + j + 1) :=
    rsum_congr R (i + j + 1) (fun b _ =>
      rsum_congr R (i + j + 1) (fun a _ => by rw [hterm b a]))
  rw [hc1]
  -- 外側: b = j にスパイク
  have houter : rsum R (fun b => rsum R (fun a => R.mul (F b a)
        (ps2Mono R a b j i)) (i + j + 1)) (i + j + 1)
      = rsum R (fun a => R.mul (F j a) (ps2Mono R a j j i)) (i + j + 1) :=
    rsum_single R _ j (i + j + 1) (by omega) (fun b _ hb => by
      have hz : rsum R (fun a => R.mul (F b a) (ps2Mono R a b j i)) (i + j + 1)
          = rsum R (fun _ => R.zero) (i + j + 1) :=
        rsum_congr R (i + j + 1) (fun a _ => by
          rw [show ps2Mono R a b j i = R.zero from by
            show (if j = b then (if i = a then R.one else R.zero) else R.zero)
              = R.zero
            rw [if_neg (fun h => hb h.symm)]]
          exact R.mul_zero _)
      rw [hz]
      exact rsum_const_zero R (i + j + 1))
  rw [houter]
  -- 内側: a = i にスパイク
  have hinner : rsum R (fun a => R.mul (F j a) (ps2Mono R a j j i)) (i + j + 1)
      = R.mul (F j i) (ps2Mono R i j j i) :=
    rsum_single R _ i (i + j + 1) (by omega) (fun a _ ha => by
      rw [show ps2Mono R a j j i = R.zero from by
        show (if j = j then (if i = a then R.one else R.zero) else R.zero)
          = R.zero
        rw [if_pos rfl, if_neg (fun h => ha h.symm)]]
      exact R.mul_zero _)
  rw [hinner,
    show ps2Mono R i j j i = R.one from by
      show (if j = j then (if i = i then R.one else R.zero) else R.zero) = R.one
      rw [if_pos rfl, if_pos rfl],
    CRing.mul_one R (F j i)]

end IUT
