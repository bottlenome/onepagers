/-
  # M252F: 点集合上の O-作用の可換環的派生則（柱C・O-加群構造の残件を 1 スライス）

  柱C（issue #37）。M231F（`FormalGroupPointLaws.lean`）は点集合
  F(pℤ_p) の群法則と ℤ_p-作用の加法性 F([a]x, [b]x) = [a+b]x を、
  M247F（`FormalGroupPointOAction.lean`）は O-作用の乗法側——単位
  [1]x = x・零 [0]x = 0・**乗法的合成 [a]([b]x) = [ab]x**——を束ねた。
  本層はこれらを入力に、M100F（`FormalGroupEndRing.lean`）が**級数
  レベル**で固定した自己準同型環 End(F) の可換環構造——⊕ = ps21Comp F
  の可換性・⊙ = psComp の可換性・一般の逆元——の**点レベル版**を、
  新しい点等式として証明する（M100F は級数レベルのみ、点版は未輸送）。

  * M252F-1 `lt_point_scalar_comm` — **スカラー合成の可換性（点版）**
    [a]([b]x) = [b]([a]x)。両辺を M247F `lt_point_scalar_mul` で
    [ab]x・[ba]x に潰し、ℤ_p の乗法可換 `mul_comm` で合流。M100F の
    `ltEnd_gMul_comm`（[a]∘[b] = [b]∘[a]）の点版。
  * M252F-2 `lt_point_gAdd_scalar_comm` — **形式群加法 ⊕ のスカラー
    点上での可換性（点版）** F([a]x, [b]x) = F([b]x, [a]x)。両辺を
    M231F/M81 `lt_point_module_add` で [a+b]x・[b+a]x に潰し、ℤ_p の
    加法可換 `add_comm` で合流。M100F の `ltEnd_gAdd_comm`
    （F([a],[b]) = F([b],[a])）の点版。
  * M252F-3 `lt_point_gAdd_scalar_neg` — **スカラー負元による点逆元
    （点版）** F([a]x, [−a]x) = 0。`lt_point_module_add` で
    [a+(−a)]x に潰し、ℤ_p の `add_comm`+`neg_add` で a+(−a) = 0 と
    し、M247F `lt_point_scalar_zero`（[0]x = 0）で零へ。すなわち
    [−a]x は点群 F(pℤ_p) における [a]x の F-逆元。M76 の級数レベル
    `lt_module_add_neg`（F([a],[−a]) = 0）の点版。
  * M252F-4 `FormalGroupPointODerivedData` /
    `formalGroupPointODerived_exists` — 派生則 3 本の総括データ束と存在。

  ## 意義

  M100F が級数レベルで閉じた End(F) の可換環構造（⊕/⊙ の可換性・
  一般逆元）を、M247F の乗法的合成 [a]([b]x)=[ab]x と M231F の加法性
  F([a]x,[b]x)=[a+b]x を橋として**点レベルへ輸送**し、点集合 F(pℤ_p)
  上の O-作用が「スカラー合成の可換・形式群加法のスカラー点上での
  可換・スカラー負元による点逆元」という可換環的派生則を備えることを
  固定する。これらは M247F/M231F の生の法則からは**新しい点等式**で
  あり（両モジュールにこれらの合成結果は無い）、O-加群構造の点版の
  代数的一貫性を一段前進させる。

  ## 正直な限定

  * (1) 本層は O-作用の**環準同型としての F-準同型性（分配律）**
    [a](x +_F y) = [a]x +_F [a]y（＝級数レベル [a](F(X,Y)) =
    F([a]X, [a]Y)）は**扱わない**——これは M100F の正直申告
    （line 40-43）でも End(F) 全射性と並んで対象外とされた別項目で
    あり、2 変数一意性を要する。本層が閉じるのはスカラーの可換性・
    負元という**スカラー側**の派生則のみ。
  * (2) M231F の限定 (1) と同様、各法則は個別の点等式として証明済み
    だが、点集合を担う単一の台型（subtype）を定義して O-加群の**型
    クラスインスタンス**を Mathlib に橋渡しする作業は範囲外。
  * (3) 各点の可除性 witness は M247F/M231F と同一の
    `zpEval_closed` 明示 witness を保持し、点集合上の一意表現への
    正規化（M231F 限定 (2)）は行わない。
  * (4) 各定理は M247F `lt_point_scalar_mul` / `lt_point_scalar_zero`・
    M231F/M81 `lt_point_module_add` と ℤ_p の環公理
    （`mul_comm`/`add_comm`/`neg_add`）の合成であり、新規の級数レベル
    証明は導入しない（新しいのは**点等式の組み立て**）。
  * 全て選択公理不使用（型継承除く）。`#print axioms` で実測。
    可能なら [propext, Quot.sound] のみ。
  * サブエージェント並行部品。
-/
import IUT.FormalGroupPointOAction

namespace IUT

/-! ## M252F-1: スカラー合成の可換性（点版） -/

/-- **定理 (M252F-1): スカラー合成の可換性（点版）** —
    [a]([b]x) = [b]([a]x)。両辺を M247F `lt_point_scalar_mul` で
    [ab]x・[ba]x に潰し、ℤ_p の乗法可換で合流。M100F `ltEnd_gMul_comm`
    の点版。 -/
theorem lt_point_scalar_comm (p : Nat) (hp : IsPrime p)
    (a b : (Zp p).carrier) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltSol p hp a)
      (zpEval p (ltSol p hp b) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp b)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
    = zpEval p (ltSol p hp b)
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx) :=
  (lt_point_scalar_mul p hp a b x e hx).trans
    ((congrArg (fun c => zpEval p (ltSol p hp c) x e hx)
        ((zpRing p).mul_comm a b)).trans
      (lt_point_scalar_mul p hp b a x e hx).symm)

/-! ## M252F-2: 形式群加法 ⊕ のスカラー点上での可換性（点版） -/

/-- **定理 (M252F-2): 形式群加法 ⊕ のスカラー点上での可換性（点版）** —
    F([a]x, [b]x) = F([b]x, [a]x)。両辺を M231F/M81 `lt_point_module_add`
    で [a+b]x・[b+a]x に潰し、ℤ_p の加法可換で合流。M100F `ltEnd_gAdd_comm`
    の点版。 -/
theorem lt_point_gAdd_scalar_comm (p : Nat) (hp : IsPrime p)
    (a b : (Zp p).carrier) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval2 p (lt2Sol p hp)
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval p (ltSol p hp b) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp b)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
      (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
    = zpEval2 p (lt2Sol p hp)
      (zpEval p (ltSol p hp b) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp b)) x e hx))
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx) :=
  (lt_point_module_add p hp a b x e hx).trans
    ((congrArg (fun c => zpEval p (ltSol p hp c) x e hx)
        ((zpRing p).add_comm a b)).trans
      (lt_point_module_add p hp b a x e hx).symm)

/-! ## M252F-3: スカラー負元による点逆元（点版） -/

/-- **定理 (M252F-3): スカラー負元による点逆元（点版）** —
    F([a]x, [−a]x) = 0。`lt_point_module_add` で [a+(−a)]x に潰し、
    ℤ_p の `add_comm`+`neg_add` で a+(−a) = 0 として M247F
    `lt_point_scalar_zero` で零へ。[−a]x は点群 F(pℤ_p) における
    [a]x の F-逆元。M76 級数レベル `lt_module_add_neg` の点版。 -/
theorem lt_point_gAdd_scalar_neg (p : Nat) (hp : IsPrime p)
    (a : (Zp p).carrier) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval2 p (lt2Sol p hp)
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval p (ltSol p hp ((zpRing p).neg a)) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp ((zpRing p).neg a)))
          x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
      (zpEval_closed p hp.1 (ltSol p hp ((zpRing p).neg a)) rfl x e hx)
    = (zpRing p).zero :=
  (lt_point_module_add p hp a ((zpRing p).neg a) x e hx).trans
    ((congrArg (fun c => zpEval p (ltSol p hp c) x e hx)
        (((zpRing p).add_comm a ((zpRing p).neg a)).trans
          ((zpRing p).neg_add a))).trans
      (lt_point_scalar_zero p hp x e hx))

/-! ## M252F-4: 総括 -/

/-- **点集合上の O-作用の可換環的派生則データ（M252F-4）**: 素数 p・
    `hp : IsPrime p` に対し、Lubin–Tate 形式群 F = lt2Sol p hp の
    点集合 F(pℤ_p) 上の O-作用が備える可換環的派生則——スカラー合成の
    可換 [a]([b]x) = [b]([a]x)・形式群加法のスカラー点上での可換
    F([a]x,[b]x) = F([b]x,[a]x)・スカラー負元による点逆元
    F([a]x,[−a]x) = 0——を一つの証明記録に束ねる。M100F の級数レベル
    End(F) 可換環構造の点版。 -/
structure FormalGroupPointODerivedData (p : Nat) (hp : IsPrime p) where
  /-- M252F-1: スカラー合成の可換 [a]([b]x) = [b]([a]x)。 -/
  scalarComm : ∀ (a b x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval p (ltSol p hp a)
      (zpEval p (ltSol p hp b) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp b)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
    = zpEval p (ltSol p hp b)
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
  /-- M252F-2: 形式群加法 ⊕ のスカラー点上での可換
      F([a]x,[b]x) = F([b]x,[a]x)。 -/
  gAddScalarComm : ∀ (a b x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval2 p (lt2Sol p hp)
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval p (ltSol p hp b) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp b)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
      (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
    = zpEval2 p (lt2Sol p hp)
      (zpEval p (ltSol p hp b) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp b)) x e hx))
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
  /-- M252F-3: スカラー負元による点逆元 F([a]x,[−a]x) = 0。 -/
  gAddScalarNeg : ∀ (a x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval2 p (lt2Sol p hp)
      (zpEval p (ltSol p hp a) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp a)) x e hx))
      (zpEval p (ltSol p hp ((zpRing p).neg a)) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp ((zpRing p).neg a)))
          x e hx))
      (zpEval_closed p hp.1 (ltSol p hp a) rfl x e hx)
      (zpEval_closed p hp.1 (ltSol p hp ((zpRing p).neg a)) rfl x e hx)
    = (zpRing p).zero

/-- **証人（M252F-4）**: 点集合 F(pℤ_p) 上の O-作用が可換環的派生則
    （スカラー合成の可換・形式群加法のスカラー点上での可換・スカラー
    負元による点逆元）を実際に備える。 -/
def formalGroupPointODerivedData (p : Nat) (hp : IsPrime p) :
    FormalGroupPointODerivedData p hp where
  scalarComm := lt_point_scalar_comm p hp
  gAddScalarComm := lt_point_gAdd_scalar_comm p hp
  gAddScalarNeg := lt_point_gAdd_scalar_neg p hp

/-- **capstone (M252F-4): 存在** — 柱C 形式群 F = lt2Sol p hp の点集合
    F(pℤ_p) 上の O-作用の可換環的派生則（M100F 級数レベル End(F) 可換環
    構造の点版）が無矛盾に存在する。 -/
theorem formalGroupPointODerived_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (FormalGroupPointODerivedData p hp) :=
  ⟨formalGroupPointODerivedData p hp⟩

end IUT
