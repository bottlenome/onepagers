/-
  # M247F: 形式群の点集合への O-作用の乗法側（柱C・O-加群構造の残件を 1 スライス）

  柱C（issue #37）。M231F（`FormalGroupPointLaws.lean`）は Lubin–Tate
  形式群 F = lt2Sol p hp の点集合 F(pℤ_p) の群法則——単位・可換・逆元・
  **[a]-作用の加法性 pointModuleAdd（F([a]x, [b]x) = [a+b]x）**・結合——を
  束ねたが、その正直申告 (1) で

    「これらから『点集合が Group / CommGroup の型クラスインスタンスを
     なす』束縛は与えない……群公理を型クラスとして充足させる作業は
     範囲外」

  と明記し、[a]-作用については**加法性のみ**（[a+b]）を束ねていた。本層は
  その O-作用の**乗法側**——級数レベルで完結済みの環準同型 O → End(F)
  （M76 `lt_module_mul`：[a]∘[b] = [ab]、`ltSol_one`：[1] = X、
  `ltSol_zero`：[0] = 0 級数）を、M79 の合成両立 `zpEval_comp_closed`
  （(F∘G)(x) = F(G(x))）と M77 の `zpEval_X` / `zpEval_zero` で
  **点レベルへ輸送**し、点集合 F(pℤ_p) 上のスカラー作用が

    * [1](x) = x（単位作用）
    * [0](x) = 0（零作用）
    * [a]([b](x)) = [ab](x)（乗法的合成＝本丸）

  を満たすことを機械検証する。これで M231F の加法側 pointModuleAdd と
  合わせ、点集合上の O-作用が**環作用（加法・乗法・単位を保つ）**として
  閉じる（O-加群構造の「作用が環準同型」部分の点版）。

  * M247F-1 `lt_point_scalar_one` — **単位作用の点版** [1](x) = x
    （`ltSol_one` を `zpEval_X` で輸送）
  * M247F-2 `lt_point_scalar_zero` — **零作用の点版** [0](x) = 0
    （`ltSol_zero` を `zpEval_zero` で輸送）
  * M247F-3 `lt_point_scalar_mul` — **乗法的合成の点版（本丸）**
    [a]([b](x)) = [ab](x)（M76 `lt_module_mul` を M79
    `zpEval_comp_closed` で輸送。外側の点 [b](x) ∈ pℤ_p の可除性
    witness は `zpEval_closed`（ltSol b 0 = 0）で明示構成）
  * M247F-4 `FormalGroupPointOActionData` / `formalGroupPointOAction_exists`
    — O-作用（乗法側 3 則 + M231F 加法側の再輸出）の総括データ束と存在

  ## 意義

  M231F 正直申告 (1) の O-作用側——点集合 F(pℤ_p) 上のスカラー作用が
  加法だけでなく**乗法・単位まで保つ環作用**であること——を、級数レベルの
  環準同型 O → End(F)（M76）の点への忠実な輸送として固定する。加法側
  （M231F pointModuleAdd）と本層の乗法側を合わせて、点集合が O-加群の
  「作用が環準同型」構造を（個別等式として）備えることが従う。

  ## 正直な限定

  * (1) 本層は級数レベルの環準同型 O → End(F)（M76 `lt_module_mul` /
    `ltSol_one` / `ltSol_zero`）を点レベルへ**輸送**するのみで、点集合を
    担う単一の台型（subtype）を定義して O-加群（あるいは O 上の加群）の
    **型クラスインスタンス**を充足させる作業は M231F の限定 (1) と同様に
    範囲外。各法則は個別の点等式として証明済みだが Mathlib 型クラスへの
    橋渡しは与えない。
  * (2) `lt_point_scalar_mul` の外側の点 [b](x) の可除性 witness は
    M79 `zpEval_closed`（psShift 因数分解による明示 witness）を保持し、
    点集合上の一意表現への正規化（M231F 限定 (2)）は行わない。
  * (3) 加法側フィールド `scalar_add` は M231F/M81 の既存定理
    `lt_point_module_add` の再輸出であり本層に新規証明はない。乗法側
    3 則（単位・零・合成）が本層の新規内容（M76 × M79 の輸送）。
  * 全て選択公理不使用（型継承除く）。`#print axioms` で実測。
  * サブエージェント並行部品。
-/
import IUT.FormalGroupOModule
import IUT.FormalGroupPointsLaw
import IUT.FormalGroupPointsComp

namespace IUT

/-! ## M247F-1: 単位作用の点版 -/

/-- **定理 (M247F-1): 単位作用の点版** — [1](x) = x。級数レベルの
    正規化 `ltSol_one`（[1] = X）を M77 の `zpEval_X`（X(x) = x）で
    点へ輸送する。 -/
theorem lt_point_scalar_one (p : Nat) (hp : IsPrime p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltSol p hp ((zpRing p).one)) x e hx = x :=
  (congrArg (fun H => zpEval p H x e hx) (ltSol_one p hp)).trans
    (zpEval_X p hp.1 x e hx)

/-! ## M247F-2: 零作用の点版 -/

/-- **定理 (M247F-2): 零作用の点版** — [0](x) = 0。級数レベルの
    正規化 `ltSol_zero`（[0] = 0 級数）を M77 の `zpEval_zero`
    （0(x) = 0）で点へ輸送する。 -/
theorem lt_point_scalar_zero (p : Nat) (hp : IsPrime p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltSol p hp ((zpRing p).zero)) x e hx = (zpRing p).zero :=
  (congrArg (fun H => zpEval p H x e hx) (ltSol_zero p hp)).trans
    (zpEval_zero p x e hx)

/-! ## M247F-3: 乗法的合成の点版（本丸） -/

/-- **定理 (M247F-3): 乗法的合成の点版（本丸）** —
    [a]([b](x)) = [ab](x)。級数レベルの環準同型の乗法保存 M76
    `lt_module_mul`（[a]∘[b] = [ab]）を M79 の合成両立
    `zpEval_comp_closed`（(F∘G)(x) = F(G(x))、G(0) = 0）で点へ輸送。
    外側の点 [b](x) ∈ pℤ_p の可除性 witness は `zpEval_closed`
    （ltSol b 0 = 0）で明示構成する。 -/
theorem lt_point_scalar_mul (p : Nat) (hp : IsPrime p)
    (a b : (Zp p).carrier) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (ltSol p hp a)
      (zpEval p (ltSol p hp b) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp b)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
    = zpEval p (ltSol p hp ((zpRing p).mul a b)) x e hx :=
  (zpEval_comp_closed p hp.1 (ltSol p hp a) (ltSol p hp b) rfl x e hx).symm.trans
    (congrArg (fun H => zpEval p H x e hx) (lt_module_mul p hp a b))

/-! ## M247F-4: 総括 -/

/-- **形式群の点集合への O-作用データ（M247F-4）**: 素数 p・
    `hp : IsPrime p` に対し、Lubin–Tate 形式群 F = lt2Sol p hp の点集合
    F(pℤ_p) 上のスカラー作用 [a](·) が備える環作用則——単位作用
    [1](x) = x・零作用 [0](x) = 0・乗法的合成 [a]([b](x)) = [ab](x)
    （本層の新規輸送）と、加法性 F([a]x, [b]x) = [a+b]x（M231F/M81 の
    `lt_point_module_add` の再輸出）——を一つの証明記録に束ねる。 -/
structure FormalGroupPointOActionData (p : Nat) (hp : IsPrime p) where
  /-- M247F-1: 単位作用 [1](x) = x。 -/
  scalar_one : ∀ (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval p (ltSol p hp ((zpRing p).one)) x e hx = x
  /-- M247F-2: 零作用 [0](x) = 0。 -/
  scalar_zero : ∀ (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval p (ltSol p hp ((zpRing p).zero)) x e hx = (zpRing p).zero
  /-- M247F-3: 乗法的合成 [a]([b](x)) = [ab](x)。 -/
  scalar_mul : ∀ (a b x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e),
    zpEval p (ltSol p hp a)
      (zpEval p (ltSol p hp b) x e hx)
      ((zpRing p).mul e
        (zpEval p (psShift (zpRing p) (ltSol p hp b)) x e hx))
      (zpEval_closed p hp.1 (ltSol p hp b) rfl x e hx)
    = zpEval p (ltSol p hp ((zpRing p).mul a b)) x e hx
  /-- M231F/M81 再輸出: 加法性 F([a]x, [b]x) = [a+b]x。 -/
  scalar_add : ∀ (a b x e : (Zp p).carrier)
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
    = zpEval p (ltSol p hp ((zpRing p).add a b)) x e hx

/-- **証人（M247F-4）**: 点集合 F(pℤ_p) 上の O-作用が環作用則（単位・
    零・乗法的合成・加法性）を実際に備える。乗法側 3 則は本層の新規輸送、
    加法側は M231F/M81 の再輸出。 -/
def formalGroupPointOActionData (p : Nat) (hp : IsPrime p) :
    FormalGroupPointOActionData p hp where
  scalar_one := lt_point_scalar_one p hp
  scalar_zero := lt_point_scalar_zero p hp
  scalar_mul := lt_point_scalar_mul p hp
  scalar_add := lt_point_module_add p hp

/-- **capstone (M247F-4): 存在** — 柱C 形式群 F = lt2Sol p hp の点集合
    F(pℤ_p) 上の O-作用（乗法的合成・単位・零・加法性を備えた環作用）
    が無矛盾に存在する。M231F 正直申告 (1) の O-作用乗法側の回収の
    締めくくり。 -/
theorem formalGroupPointOAction_exists (p : Nat) (hp : IsPrime p) :
    Nonempty (FormalGroupPointOActionData p hp) :=
  ⟨formalGroupPointOActionData p hp⟩

end IUT
